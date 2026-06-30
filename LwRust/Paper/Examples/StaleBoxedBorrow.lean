import LwRust.Paper.Soundness.Helpers.BorrowWellFormed
import LwRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Stale borrow annotations from joins

This file records the source-shaped cases behind the initialized-only
well-formedness relaxation.

The important point is that the stale target is introduced by a control-flow
join.  We do not model it as a concrete live borrow that is later violated.

Example 1, fully accepted by the current typing rule:

```rust
let mut x = 0;
let mut p = Box::new(&mut x);

if c {
    move p;     // drops the owner/loan annotation
    move x;
} else {
    ()
}
```

The join result is:

```text
x : undef int
p : undef (box (&mut [x] int))
```

The old `EnvJoinSameShape` premise would reject the join against the else
branch, because `x : int` joins with `x : undef int`.

Example 2, the result-type version of the same phenomenon:

```rust
let mut x = 0;
let mut y = 0;

if c {
    move x;
    Box::new(&mut y)
} else {
    Box::new(&mut x)
}
```

The result type join is `box (&mut [y, x] int)` in an environment where `x` is
maybe moved out.  That type is well formed under the initialized-only predicate,
but not under full `WellFormedTy`.

Example 3, a live boxed owner after the join:

```rust
let mut x = 0;
let mut y = 1;
let mut p = Box::new(&mut y);

if c {
    move x;
} else {
    p = Box::new(&mut x);
}
```

The join keeps `p` live:

```text
x : undef int
y : int
p : box (&mut [y, x] int)
```

The current mechanisation still has the paper/main mismatch that declared
`Box<T>` variables do not project through `T-LvBox`; this section therefore
records the live joined environment and the direct write prohibition on `x`, and
also records that `*p` is not currently typable until box projection is fixed.
-/

namespace LwRust
namespace Paper

open Core

private theorem envExt {left right : Env}
    (h : ∀ x, left.slotAt x = right.slotAt x) : left = right := by
  cases left with
  | mk leftSlotAt =>
      cases right with
      | mk rightSlotAt =>
          have hfun : leftSlotAt = rightSlotAt := funext h
          subst hfun
          rfl

private theorem partialTyStrengthensBorrowAppend {mutable : Bool}
    {leftTargets rightTargets : List LVal}
    {joined : PartialTy}
    (hleft : PartialTyStrengthens (.ty (.borrow mutable leftTargets)) joined)
    (hright : PartialTyStrengthens (.ty (.borrow mutable rightTargets)) joined) :
    PartialTyStrengthens (.ty (.borrow mutable (leftTargets ++ rightTargets)))
      joined := by
  cases hleft with
  | reflex =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hmem
        · exact hsubRight hmem)
  | borrow hsubLeft =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem)
  | intoUndef hinner =>
      rcases PartialTyStrengthens.from_borrow_inv hinner with
        ⟨targetTargets, htargetEq, hsubLeft⟩
      cases htargetEq
      have hsubRight : rightTargets ⊆ targetTargets := by
        cases hright with
        | intoUndef hinner' => exact PartialTyStrengthens.borrow_subset hinner'
      exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem))

def staleJoinChildLifetime : Lifetime := [0]

def staleJoinXSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def staleJoinYSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def staleJoinXMovedSlot : EnvSlot :=
  { ty := .undef .int, lifetime := Lifetime.root }

def staleJoinPSlot : EnvSlot :=
  { ty := .ty (.box (.borrow true [.var "x"])), lifetime := Lifetime.root }

def staleJoinPMovedSlot : EnvSlot :=
  { ty := .undef (.box (.borrow true [.var "x"])), lifetime := Lifetime.root }

def dropMoveXEnv : Env :=
  Env.empty.update "x" staleJoinXSlot

def dropMoveStartEnv : Env :=
  dropMoveXEnv.update "p" staleJoinPSlot

def dropMovePMovedEnv : Env :=
  dropMoveStartEnv.update "p" staleJoinPMovedSlot

def dropMoveJoinEnv : Env :=
  dropMovePMovedEnv.update "x" staleJoinXMovedSlot

def dropMovePrefix : List Term :=
  [.letMut "x" (.val (.int 0)),
    .letMut "p" (.box (.borrow true (.var "x")))]

def dropMoveTrueBranch : Term :=
  .block staleJoinChildLifetime
    [.move (.var "p"), .move (.var "x"), .val .unit]

def dropMoveFalseBranch : Term :=
  .val .unit

def dropMoveIf : Term :=
  .ite (.val (.bool true)) dropMoveTrueBranch dropMoveFalseBranch

def xOnlyTypingShape
    (lv : LVal) (partialTy : PartialTy) (lifetime : Lifetime) : Prop :=
  lv = .var "x" ∧ partialTy = .ty .int ∧ lifetime = Lifetime.root

theorem dropMoveXEnv_lvalTyping_shape {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTyping dropMoveXEnv lv partialTy lifetime →
    xOnlyTypingShape lv partialTy lifetime := by
  exact LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      xOnlyTypingShape lv partialTy lifetime)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    (by
      intro name slot hslot
      by_cases hx : name = "x"
      · subst hx
        have hslotEq : slot = staleJoinXSlot := by
          exact (Option.some.inj
            (by simpa [dropMoveXEnv, staleJoinXSlot] using hslot)).symm
        subst hslotEq
        exact ⟨rfl, rfl, rfl⟩
      · have hnone : dropMoveXEnv.slotAt name = none := by
          simp [dropMoveXEnv, Env.update, Env.empty, hx]
        rw [hnone] at hslot
        cases hslot)
    (by
      intro _source _inner _lifetime _hsource ihSource
      rcases ihSource with ⟨_hlv, hty, _hlifetime⟩
      cases hty)
    (by
      intro _source _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets ihBorrow _ihTargets
      rcases ihBorrow with ⟨_hlv, hty, _hlifetime⟩
      cases hty)
    (by intro _target _ty _lifetime _htarget _ihTarget; trivial)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy
        _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
      trivial)

theorem dropMoveXEnv_no_lval_borrow {lv : LVal} {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTyping dropMoveXEnv lv (.ty (.borrow mutable targets)) lifetime := by
  intro htyping
  rcases dropMoveXEnv_lvalTyping_shape htyping with ⟨_hlv, hty, _hlifetime⟩
  cases hty

def dropMoveStartTypingShape
    (lv : LVal) (partialTy : PartialTy) (lifetime : Lifetime) : Prop :=
  (lv = .var "x" ∧ partialTy = .ty .int ∧ lifetime = Lifetime.root) ∨
    (lv = .var "p" ∧
      partialTy = .ty (.box (.borrow true [.var "x"])) ∧
      lifetime = Lifetime.root)

theorem dropMoveStartEnv_lvalTyping_shape {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTyping dropMoveStartEnv lv partialTy lifetime →
    dropMoveStartTypingShape lv partialTy lifetime := by
  exact LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      dropMoveStartTypingShape lv partialTy lifetime)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    (by
      intro name slot hslot
      by_cases hx : name = "x"
      · subst hx
        have hslotEq : slot = staleJoinXSlot := by
          exact (Option.some.inj
            (by simpa [dropMoveStartEnv, dropMoveXEnv, staleJoinXSlot,
              staleJoinPSlot, Env.update] using hslot)).symm
        subst hslotEq
        exact Or.inl ⟨rfl, rfl, rfl⟩
      · by_cases hp : name = "p"
        · subst hp
          have hslotEq : slot = staleJoinPSlot := by
            exact (Option.some.inj
              (by simpa [dropMoveStartEnv, staleJoinPSlot, Env.update]
                using hslot)).symm
          subst hslotEq
          exact Or.inr ⟨rfl, rfl, rfl⟩
        · have hnone : dropMoveStartEnv.slotAt name = none := by
            simp [dropMoveStartEnv, dropMoveXEnv, Env.update, Env.empty, hx, hp]
          rw [hnone] at hslot
          cases hslot)
    (by
      intro _source _inner _lifetime _hsource ihSource
      rcases ihSource with hsourceShape | hsourceShape
      · rcases hsourceShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hsourceShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty)
    (by
      intro _source _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets ihBorrow _ihTargets
      rcases ihBorrow with hborrowShape | hborrowShape
      · rcases hborrowShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hborrowShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty)
    (by intro _target _ty _lifetime _htarget _ihTarget; trivial)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy
        _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
      trivial)

theorem dropMoveStartEnv_no_lval_borrow {lv : LVal} {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTyping dropMoveStartEnv lv (.ty (.borrow mutable targets))
      lifetime := by
  intro htyping
  rcases dropMoveStartEnv_lvalTyping_shape htyping with hshape | hshape
  · rcases hshape with ⟨_hlv, hty, _hlifetime⟩
    cases hty
  · rcases hshape with ⟨_hlv, hty, _hlifetime⟩
    cases hty

theorem dropMoveX_freshUpdate_int :
    FreshUpdateCoherenceObligations Env.empty "x" .int Lifetime.root := by
  constructor
  · intro lv mutable targets borrowLifetime _hbase htyping
    have hborrow :
        LValTyping dropMoveXEnv lv (.ty (.borrow mutable targets))
          borrowLifetime := by
      simpa [dropMoveXEnv, staleJoinXSlot] using htyping
    exact False.elim (dropMoveXEnv_no_lval_borrow hborrow)
  · intro lv mutable targets borrowLifetime _hbase htyping
    have hborrow :
        LValTyping dropMoveXEnv lv (.ty (.borrow mutable targets))
          borrowLifetime := by
      simpa [dropMoveXEnv, staleJoinXSlot] using htyping
    exact False.elim (dropMoveXEnv_no_lval_borrow hborrow)

theorem dropMoveP_freshUpdate :
    FreshUpdateCoherenceObligations dropMoveXEnv "p"
      (.box (.borrow true [.var "x"])) Lifetime.root := by
  constructor
  · intro lv mutable targets borrowLifetime _hbase htyping
    have hborrow :
        LValTyping dropMoveStartEnv lv (.ty (.borrow mutable targets))
          borrowLifetime := by
      simpa [dropMoveStartEnv, staleJoinPSlot] using htyping
    exact False.elim (dropMoveStartEnv_no_lval_borrow hborrow)
  · intro lv mutable targets borrowLifetime _hbase htyping
    have hborrow :
        LValTyping dropMoveStartEnv lv (.ty (.borrow mutable targets))
          borrowLifetime := by
      simpa [dropMoveStartEnv, staleJoinPSlot] using htyping
    exact False.elim (dropMoveStartEnv_no_lval_borrow hborrow)

theorem dropMoveDeclareX_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root
      (.letMut "x" (.val (.int 0))) .unit dropMoveXEnv := by
  refine TermTyping.declare ?freshBefore
    (TermTyping.const ValueTyping.int)
    ?freshAfter
    dropMoveX_freshUpdate_int
    ?envEq
  · simp [Env.fresh, Env.empty]
  · simp [Env.fresh, Env.empty]
  · rfl

theorem dropMoveX_typing :
    LValTyping dropMoveXEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var dropMoveXEnv "x" staleJoinXSlot
    (by simp [dropMoveXEnv, staleJoinXSlot])

theorem dropMoveX_mutable :
    Mutable dropMoveXEnv (.var "x") := by
  exact @Mutable.var dropMoveXEnv "x" staleJoinXSlot
    (by simp [dropMoveXEnv, staleJoinXSlot])

theorem dropMoveXEnv_no_contains_borrow {root : Name}
    {mutable : Bool} {targets : List LVal} :
    ¬ dropMoveXEnv ⊢ root ↝ (.borrow mutable targets) := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hx : root = "x"
  · subst hx
    have hslotEq : slot = staleJoinXSlot := by
      exact (Option.some.inj
        (by simpa [dropMoveXEnv, staleJoinXSlot] using hslot)).symm
    subst hslotEq
    cases hcontains
  · have hnone : dropMoveXEnv.slotAt root = none := by
      simp [dropMoveXEnv, Env.update, Env.empty, hx]
    rw [hnone] at hslot
    cases hslot

theorem dropMoveX_not_writeProhibited :
    ¬ WriteProhibited dropMoveXEnv (.var "x") := by
  intro hwrite
  cases hwrite with
  | inl hread =>
      rcases hread with ⟨root, targets, _target, hcontains, _htarget,
        _hconflict⟩
      exact dropMoveXEnv_no_contains_borrow hcontains
  | inr himm =>
      rcases himm with ⟨root, targets, _target, hcontains, _htarget,
        _hconflict⟩
      exact dropMoveXEnv_no_contains_borrow hcontains

theorem dropMoveDeclareP_typing :
    TermTyping dropMoveXEnv StoreTyping.empty Lifetime.root
      (.letMut "p" (.box (.borrow true (.var "x")))) .unit
      dropMoveStartEnv := by
  refine TermTyping.declare ?freshBefore ?initialiser ?freshAfter
    dropMoveP_freshUpdate ?envEq
  · simp [Env.fresh, dropMoveXEnv, Env.update, Env.empty]
  · exact TermTyping.box
      (TermTyping.mutBorrow dropMoveX_typing dropMoveX_mutable
        dropMoveX_not_writeProhibited)
  · simp [Env.fresh, dropMoveXEnv, Env.update, Env.empty]
  · rfl

theorem dropMovePrefix_typing :
    TermListTyping Env.empty StoreTyping.empty Lifetime.root
      dropMovePrefix .unit dropMoveStartEnv := by
  unfold dropMovePrefix
  exact TermListTyping.cons dropMoveDeclareX_typing
    (TermListTyping.singleton dropMoveDeclareP_typing)

theorem dropMoveStart_p_typing :
    LValTyping dropMoveStartEnv (.var "p")
      (.ty (.box (.borrow true [.var "x"]))) Lifetime.root := by
  exact @LValTyping.var dropMoveStartEnv "p" staleJoinPSlot
    (by simp [dropMoveStartEnv, staleJoinPSlot, Env.update])

theorem dropMovePMoved_x_typing :
    LValTyping dropMovePMovedEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var dropMovePMovedEnv "x" staleJoinXSlot
    (by
      simp [dropMovePMovedEnv, dropMoveStartEnv, dropMoveXEnv,
        staleJoinXSlot, staleJoinPSlot, staleJoinPMovedSlot, Env.update])

theorem dropMoveStart_contains_borrow_inv {root : Name} {mutable : Bool}
    {targets : List LVal} :
    dropMoveStartEnv ⊢ root ↝ (.borrow mutable targets) →
    root = "p" ∧ mutable = true ∧ targets = [.var "x"] := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hp : root = "p"
  · subst hp
    have hslotEq : slot = staleJoinPSlot := by
      exact (Option.some.inj
        (by simpa [dropMoveStartEnv, staleJoinPSlot, Env.update]
          using hslot)).symm
    subst hslotEq
    cases hcontains with
    | tyBox hinner =>
        cases hinner
        exact ⟨rfl, rfl, rfl⟩
  · by_cases hx : root = "x"
    · subst hx
      have hslotEq : slot = staleJoinXSlot := by
        exact (Option.some.inj
          (by
            simpa [dropMoveStartEnv, dropMoveXEnv, staleJoinXSlot,
              staleJoinPSlot, Env.update] using hslot)).symm
      subst hslotEq
      cases hcontains
    · have hnone : dropMoveStartEnv.slotAt root = none := by
        simp [dropMoveStartEnv, dropMoveXEnv, Env.update, Env.empty, hp, hx]
      rw [hnone] at hslot
      cases hslot

theorem dropMoveStart_not_writeProhibited_p :
    ¬ WriteProhibited dropMoveStartEnv (.var "p") := by
  intro hwrite
  cases hwrite with
  | inl hread =>
      rcases hread with ⟨root, targets, target, hcontains, htarget,
        hconflict⟩
      rcases dropMoveStart_contains_borrow_inv hcontains with
        ⟨rfl, _hmutable, rfl⟩
      simp at htarget
      subst htarget
      simp [PathConflicts, LVal.base] at hconflict
  | inr himm =>
      rcases himm with ⟨root, targets, target, hcontains, _htarget,
        _hconflict⟩
      rcases dropMoveStart_contains_borrow_inv hcontains with
        ⟨_hroot, hmutable, _htargets⟩
      cases hmutable

theorem dropMovePMoved_no_contains_borrow {root : Name}
    {mutable : Bool} {targets : List LVal} :
    ¬ dropMovePMovedEnv ⊢ root ↝ (.borrow mutable targets) := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hp : root = "p"
  · subst hp
    have hslotEq : slot = staleJoinPMovedSlot := by
      simpa [dropMovePMovedEnv, staleJoinPMovedSlot, Env.update] using
        hslot.symm
    subst hslotEq
    cases hcontains
  · by_cases hx : root = "x"
    · subst hx
      have hslotEq : slot = staleJoinXSlot := by
        exact (Option.some.inj
          (by
            simpa [dropMovePMovedEnv, dropMoveStartEnv, dropMoveXEnv,
              staleJoinXSlot, staleJoinPSlot, staleJoinPMovedSlot, Env.update]
              using hslot)).symm
      subst hslotEq
      cases hcontains
    · have hnone : dropMovePMovedEnv.slotAt root = none := by
        simp [dropMovePMovedEnv, dropMoveStartEnv, dropMoveXEnv, Env.update,
          Env.empty, hp, hx]
      rw [hnone] at hslot
      cases hslot

theorem dropMovePMoved_not_writeProhibited_x :
    ¬ WriteProhibited dropMovePMovedEnv (.var "x") := by
  intro hwrite
  cases hwrite with
  | inl hread =>
      rcases hread with ⟨root, targets, _target, hcontains, _htarget,
        _hconflict⟩
      exact dropMovePMoved_no_contains_borrow hcontains
  | inr himm =>
      rcases himm with ⟨root, targets, _target, hcontains, _htarget,
        _hconflict⟩
      exact dropMovePMoved_no_contains_borrow hcontains

theorem dropMove_move_p :
    EnvMove dropMoveStartEnv (.var "p") dropMovePMovedEnv := by
  refine ⟨staleJoinPSlot, .undef (.box (.borrow true [.var "x"])), ?_, ?_, rfl⟩
  · show dropMoveStartEnv.slotAt "p" = some staleJoinPSlot
    simp [dropMoveStartEnv, staleJoinPSlot, Env.update]
  · rfl

theorem dropMove_move_x_after_p :
    EnvMove dropMovePMovedEnv (.var "x") dropMoveJoinEnv := by
  refine ⟨staleJoinXSlot, .undef .int, ?_, ?_, rfl⟩
  · show dropMovePMovedEnv.slotAt "x" = some staleJoinXSlot
    simp [dropMovePMovedEnv, dropMoveStartEnv, dropMoveXEnv, staleJoinXSlot,
      staleJoinPSlot, staleJoinPMovedSlot, Env.update]
  · rfl

theorem dropMoveJoinEnv_drop_child :
    dropMoveJoinEnv.dropLifetime staleJoinChildLifetime = dropMoveJoinEnv := by
  apply envExt
  intro name
  by_cases hx : name = "x"
  · subst hx
    simp [dropMoveJoinEnv, dropMovePMovedEnv, dropMoveStartEnv, dropMoveXEnv,
      staleJoinXMovedSlot, staleJoinXSlot, staleJoinPSlot,
      staleJoinPMovedSlot, staleJoinChildLifetime, Env.dropLifetime, Env.update,
      Lifetime.root]
  · by_cases hp : name = "p"
    · subst hp
      simp [dropMoveJoinEnv, dropMovePMovedEnv, dropMoveStartEnv, dropMoveXEnv,
        staleJoinXMovedSlot, staleJoinXSlot, staleJoinPSlot,
        staleJoinPMovedSlot, staleJoinChildLifetime, Env.dropLifetime,
        Env.update, Lifetime.root]
    · simp [dropMoveJoinEnv, dropMovePMovedEnv, dropMoveStartEnv, dropMoveXEnv,
        staleJoinXMovedSlot, staleJoinXSlot, staleJoinPSlot,
        staleJoinPMovedSlot, staleJoinChildLifetime, Env.dropLifetime,
        Env.update, Env.empty, hx, hp]

theorem dropMoveTrueBranch_typing :
    TermTyping dropMoveStartEnv StoreTyping.empty Lifetime.root
      dropMoveTrueBranch .unit dropMoveJoinEnv := by
  unfold dropMoveTrueBranch
  refine @TermTyping.block dropMoveStartEnv dropMoveJoinEnv dropMoveJoinEnv
    StoreTyping.empty Lifetime.root staleJoinChildLifetime
    [.move (.var "p"), .move (.var "x"), .val .unit] .unit
    ⟨0, rfl⟩ ?body WellFormedTy.unit ?drop
  · exact TermListTyping.cons
      (TermTyping.move dropMoveStart_p_typing
        dropMoveStart_not_writeProhibited_p dropMove_move_p)
      (TermListTyping.cons
        (TermTyping.move dropMovePMoved_x_typing
          dropMovePMoved_not_writeProhibited_x dropMove_move_x_after_p)
        (TermListTyping.singleton (TermTyping.const ValueTyping.unit)))
  · exact dropMoveJoinEnv_drop_child.symm

theorem dropMoveFalseBranch_typing :
    TermTyping dropMoveStartEnv StoreTyping.empty Lifetime.root
      dropMoveFalseBranch .unit dropMoveStartEnv := by
  unfold dropMoveFalseBranch
  exact TermTyping.const ValueTyping.unit

theorem dropMoveStart_le_join :
    EnvStrengthens dropMoveStartEnv dropMoveJoinEnv := by
  intro name
  by_cases hx : name = "x"
  · subst hx
    rw [show dropMoveStartEnv.slotAt "x" = some staleJoinXSlot by
        simp [dropMoveStartEnv, dropMoveXEnv, staleJoinXSlot, staleJoinPSlot,
          Env.update],
      show dropMoveJoinEnv.slotAt "x" = some staleJoinXMovedSlot by
        simp [dropMoveJoinEnv, staleJoinXMovedSlot, Env.update]]
    exact ⟨rfl, PartialTyStrengthens.intoUndef PartialTyStrengthens.reflex⟩
  · by_cases hp : name = "p"
    · subst hp
      rw [show dropMoveStartEnv.slotAt "p" = some staleJoinPSlot by
          simp [dropMoveStartEnv, staleJoinPSlot, Env.update],
        show dropMoveJoinEnv.slotAt "p" = some staleJoinPMovedSlot by
          simp [dropMoveJoinEnv, dropMovePMovedEnv, staleJoinPMovedSlot,
            Env.update]]
      exact ⟨rfl, PartialTyStrengthens.intoUndef PartialTyStrengthens.reflex⟩
    · rw [show dropMoveStartEnv.slotAt name = none by
          simp [dropMoveStartEnv, dropMoveXEnv, Env.update, Env.empty, hx, hp],
        show dropMoveJoinEnv.slotAt name = none by
          simp [dropMoveJoinEnv, dropMovePMovedEnv, dropMoveStartEnv,
            dropMoveXEnv, Env.update, Env.empty, hx, hp]]
      trivial

theorem dropMove_envJoin :
    EnvJoin dropMoveJoinEnv dropMoveStartEnv dropMoveJoinEnv := by
  constructor
  · intro candidate hcandidate
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact EnvStrengthens.refl dropMoveJoinEnv
    · exact dropMoveStart_le_join
  · intro upper hupper
    exact hupper dropMoveJoinEnv (by simp)

def dropMoveJoinTypingShape
    (lv : LVal) (partialTy : PartialTy) (lifetime : Lifetime) : Prop :=
  (lv = .var "x" ∧ partialTy = .undef .int ∧ lifetime = Lifetime.root) ∨
    (lv = .var "p" ∧
      partialTy = .undef (.box (.borrow true [.var "x"])) ∧
      lifetime = Lifetime.root)

theorem dropMoveJoinEnv_lvalTyping_shape {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTyping dropMoveJoinEnv lv partialTy lifetime →
    dropMoveJoinTypingShape lv partialTy lifetime := by
  exact LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      dropMoveJoinTypingShape lv partialTy lifetime)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    (by
      intro name slot hslot
      by_cases hx : name = "x"
      · subst hx
        have hslotEq : slot = staleJoinXMovedSlot := by
          exact (Option.some.inj
            (by simpa [dropMoveJoinEnv, staleJoinXMovedSlot, Env.update]
              using hslot)).symm
        subst hslotEq
        exact Or.inl ⟨rfl, rfl, rfl⟩
      · by_cases hp : name = "p"
        · subst hp
          have hslotEq : slot = staleJoinPMovedSlot := by
            exact (Option.some.inj
              (by
                simpa [dropMoveJoinEnv, dropMovePMovedEnv,
                  staleJoinPMovedSlot, Env.update] using hslot)).symm
          subst hslotEq
          exact Or.inr ⟨rfl, rfl, rfl⟩
        · have hnone : dropMoveJoinEnv.slotAt name = none := by
            simp [dropMoveJoinEnv, dropMovePMovedEnv, dropMoveStartEnv,
              dropMoveXEnv, Env.update, Env.empty, hx, hp]
          rw [hnone] at hslot
          cases hslot)
    (by
      intro _source _inner _lifetime _hsource ihSource
      rcases ihSource with hsourceShape | hsourceShape
      · rcases hsourceShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hsourceShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty)
    (by
      intro _source _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets ihBorrow _ihTargets
      rcases ihBorrow with hborrowShape | hborrowShape
      · rcases hborrowShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hborrowShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty)
    (by intro _target _ty _lifetime _htarget _ihTarget; trivial)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy
        _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
      trivial)

theorem dropMoveJoinEnv_no_lval_borrow {lv : LVal} {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTyping dropMoveJoinEnv lv (.ty (.borrow mutable targets))
      lifetime := by
  intro htyping
  rcases dropMoveJoinEnv_lvalTyping_shape htyping with hshape | hshape
  · rcases hshape with ⟨_hlv, hty, _hlifetime⟩
    cases hty
  · rcases hshape with ⟨_hlv, hty, _hlifetime⟩
    cases hty

theorem dropMoveJoin_coherent :
    Coherent dropMoveJoinEnv := by
  intro lv mutable targets borrowLifetime htyping
  exact False.elim (dropMoveJoinEnv_no_lval_borrow htyping)

theorem dropMoveJoin_linearizable :
    Linearizable dropMoveJoinEnv := by
  refine ⟨fun _ => 0, ?_⟩
  intro name slot hslot v hv
  by_cases hx : name = "x"
  · subst hx
    have hslotEq : slot = staleJoinXMovedSlot := by
      exact (Option.some.inj
        (by simpa [dropMoveJoinEnv, staleJoinXMovedSlot, Env.update]
          using hslot)).symm
    subst hslotEq
    simp [staleJoinXMovedSlot, PartialTy.vars] at hv
  · by_cases hp : name = "p"
    · subst hp
      have hslotEq : slot = staleJoinPMovedSlot := by
        exact (Option.some.inj
          (by
            simpa [dropMoveJoinEnv, dropMovePMovedEnv, staleJoinPMovedSlot,
              Env.update] using hslot)).symm
      subst hslotEq
      simp [staleJoinPMovedSlot, PartialTy.vars] at hv
    · have hnone : dropMoveJoinEnv.slotAt name = none := by
        simp [dropMoveJoinEnv, dropMovePMovedEnv, dropMoveStartEnv,
          dropMoveXEnv, Env.update, Env.empty, hx, hp]
      rw [hnone] at hslot
      cases hslot

theorem dropMoveJoin_no_contains_borrow {root : Name}
    {mutable : Bool} {targets : List LVal} :
    ¬ dropMoveJoinEnv ⊢ root ↝ (.borrow mutable targets) := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hx : root = "x"
  · subst hx
    have hslotEq : slot = staleJoinXMovedSlot := by
      exact (Option.some.inj
        (by simpa [dropMoveJoinEnv, staleJoinXMovedSlot, Env.update]
          using hslot)).symm
    subst hslotEq
    cases hcontains
  · by_cases hp : root = "p"
    · subst hp
      have hslotEq : slot = staleJoinPMovedSlot := by
        exact (Option.some.inj
          (by
            simpa [dropMoveJoinEnv, dropMovePMovedEnv, staleJoinPMovedSlot,
              Env.update] using hslot)).symm
      subst hslotEq
      cases hcontains
    · have hnone : dropMoveJoinEnv.slotAt root = none := by
        simp [dropMoveJoinEnv, dropMovePMovedEnv, dropMoveStartEnv,
          dropMoveXEnv, Env.update, Env.empty, hx, hp]
      rw [hnone] at hslot
      cases hslot

theorem dropMoveJoin_borrowSafe :
    BorrowSafeEnv dropMoveJoinEnv := by
  intro x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable _hcontainsOther _htargetMutable _htargetOther _hconflict
  exact False.elim (dropMoveJoin_no_contains_borrow hcontainsMutable)

theorem dropMoveIf_typing :
    TermTyping dropMoveStartEnv StoreTyping.empty Lifetime.root
      dropMoveIf .unit dropMoveJoinEnv := by
  unfold dropMoveIf
  exact TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    dropMoveTrueBranch_typing
    dropMoveFalseBranch_typing
    (PartialTyJoin.self (.ty .unit))
    dropMove_envJoin
    WellFormedTy.unit
    dropMoveJoin_coherent
    dropMoveJoin_linearizable
    dropMoveJoin_borrowSafe
    (tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit)

theorem dropMove_old_sameShape_premise_fails :
    ¬ EnvJoinSameShape dropMoveStartEnv dropMoveJoinEnv := by
  intro hsame
  have h := hsame "x" staleJoinXSlot staleJoinXMovedSlot
    (by
      simp [dropMoveStartEnv, dropMoveXEnv, staleJoinXSlot, staleJoinPSlot,
        Env.update])
    (by simp [dropMoveJoinEnv, staleJoinXMovedSlot, Env.update])
  simp [staleJoinXSlot, staleJoinXMovedSlot, PartialTy.sameShape] at h

/-! ## Live boxed owner join -/

def boxedLivePYSlot : EnvSlot :=
  { ty := .ty (.box (.borrow true [.var "y"])), lifetime := Lifetime.root }

def boxedLivePXSlot : EnvSlot :=
  { ty := .ty (.box (.borrow true [.var "x"])), lifetime := Lifetime.root }

def boxedLivePJoinSlot : EnvSlot :=
  { ty := .ty (.box (.borrow true [.var "y", .var "x"])),
    lifetime := Lifetime.root }

def boxedLiveXYEnv : Env :=
  dropMoveXEnv.update "y" staleJoinYSlot

def boxedLiveStartEnv : Env :=
  boxedLiveXYEnv.update "p" boxedLivePYSlot

def boxedLiveXMovedEnv : Env :=
  boxedLiveStartEnv.update "x" staleJoinXMovedSlot

def boxedLivePAssignedEnv : Env :=
  boxedLiveStartEnv.update "p" boxedLivePXSlot

def boxedLiveJoinEnv : Env :=
  ((Env.empty.update "x" staleJoinXMovedSlot).update "y" staleJoinYSlot).update
    "p" boxedLivePJoinSlot

def boxedLiveTrueBranch : Term :=
  .block staleJoinChildLifetime [.move (.var "x"), .val .unit]

def boxedLiveFalseBranch : Term :=
  .block staleJoinChildLifetime
    [.assign (.var "p") (.box (.borrow true (.var "x")))]

def boxedLiveIf : Term :=
  .ite (.val (.bool true)) boxedLiveTrueBranch boxedLiveFalseBranch

theorem boxedLiveStart_x_typing :
    LValTyping boxedLiveStartEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var boxedLiveStartEnv "x" staleJoinXSlot (by
    simp [boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv, staleJoinXSlot,
      staleJoinYSlot, boxedLivePYSlot, Env.update])

theorem boxedLiveStart_y_typing :
    LValTyping boxedLiveStartEnv (.var "y") (.ty .int) Lifetime.root := by
  exact @LValTyping.var boxedLiveStartEnv "y" staleJoinYSlot (by
    simp [boxedLiveStartEnv, boxedLiveXYEnv, staleJoinYSlot, boxedLivePYSlot,
      Env.update])

theorem boxedLiveStart_p_typing :
    LValTyping boxedLiveStartEnv (.var "p")
      (.ty (.box (.borrow true [.var "y"]))) Lifetime.root := by
  exact @LValTyping.var boxedLiveStartEnv "p" boxedLivePYSlot (by
    simp [boxedLiveStartEnv, boxedLivePYSlot, Env.update])

theorem boxedLiveStart_x_mutable :
    Mutable boxedLiveStartEnv (.var "x") := by
  exact @Mutable.var boxedLiveStartEnv "x" staleJoinXSlot (by
    simp [boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv, staleJoinXSlot,
      staleJoinYSlot, boxedLivePYSlot, Env.update])

theorem boxedLiveStart_p_contains_borrow_inv {root : Name} {mutable : Bool}
    {targets : List LVal} :
    boxedLiveStartEnv ⊢ root ↝ (.borrow mutable targets) →
    root = "p" ∧ mutable = true ∧ targets = [.var "y"] := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hp : root = "p"
  · subst hp
    have hslotEq : slot = boxedLivePYSlot := by
      exact (Option.some.inj
        (by simpa [boxedLiveStartEnv, boxedLivePYSlot, Env.update]
          using hslot)).symm
    subst hslotEq
    cases hcontains with
    | tyBox hinner =>
        cases hinner
        exact ⟨rfl, rfl, rfl⟩
  · by_cases hy : root = "y"
    · subst hy
      have hslotEq : slot = staleJoinYSlot := by
        exact (Option.some.inj
          (by simpa [boxedLiveStartEnv, boxedLiveXYEnv, staleJoinYSlot,
            boxedLivePYSlot, Env.update] using hslot)).symm
      subst hslotEq
      cases hcontains
    · by_cases hx : root = "x"
      · subst hx
        have hslotEq : slot = staleJoinXSlot := by
          exact (Option.some.inj
            (by
              simpa [boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv,
                staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot, Env.update]
                using hslot)).symm
        subst hslotEq
        cases hcontains
      · have hnone : boxedLiveStartEnv.slotAt root = none := by
          simp [boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv, Env.update,
            Env.empty, hp, hy, hx]
        rw [hnone] at hslot
        cases hslot

theorem boxedLiveStart_not_writeProhibited_x :
    ¬ WriteProhibited boxedLiveStartEnv (.var "x") := by
  intro hwrite
  cases hwrite with
  | inl hread =>
      rcases hread with ⟨root, targets, target, hcontains, htarget,
        hconflict⟩
      rcases boxedLiveStart_p_contains_borrow_inv hcontains with
        ⟨_hroot, _hmutable, rfl⟩
      simp at htarget
      subst htarget
      simp [PathConflicts, LVal.base] at hconflict
  | inr himm =>
      rcases himm with ⟨root, targets, target, hcontains, htarget,
        hconflict⟩
      rcases boxedLiveStart_p_contains_borrow_inv hcontains with
        ⟨_hroot, hmutable, _htargets⟩
      cases hmutable

theorem boxedLive_move_x :
    EnvMove boxedLiveStartEnv (.var "x") boxedLiveXMovedEnv := by
  refine ⟨staleJoinXSlot, .undef .int, ?_, ?_, rfl⟩
  · show boxedLiveStartEnv.slotAt "x" = some staleJoinXSlot
    simp [boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv, staleJoinXSlot,
      staleJoinYSlot, boxedLivePYSlot, Env.update]
  · rfl

theorem boxedLiveXMovedEnv_drop_child :
    boxedLiveXMovedEnv.dropLifetime staleJoinChildLifetime = boxedLiveXMovedEnv := by
  apply envExt
  intro name
  by_cases hx : name = "x"
  · subst hx
    simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv,
      staleJoinXMovedSlot, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
      staleJoinChildLifetime, Env.dropLifetime, Env.update, Lifetime.root]
  · by_cases hy : name = "y"
    · subst hy
      simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv,
        staleJoinXMovedSlot, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
        staleJoinChildLifetime, Env.dropLifetime, Env.update, Lifetime.root]
    · by_cases hp : name = "p"
      · subst hp
        simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv,
          staleJoinXMovedSlot, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
          staleJoinChildLifetime, Env.dropLifetime, Env.update, Lifetime.root]
      · simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
          dropMoveXEnv, staleJoinXMovedSlot, staleJoinXSlot, staleJoinYSlot,
          boxedLivePYSlot, staleJoinChildLifetime, Env.dropLifetime,
          Env.update, Env.empty, hx, hy, hp]

theorem boxedLiveTrueBranch_typing :
    TermTyping boxedLiveStartEnv StoreTyping.empty Lifetime.root
      boxedLiveTrueBranch .unit boxedLiveXMovedEnv := by
  unfold boxedLiveTrueBranch
  refine @TermTyping.block boxedLiveStartEnv boxedLiveXMovedEnv
    boxedLiveXMovedEnv StoreTyping.empty Lifetime.root staleJoinChildLifetime
    [.move (.var "x"), .val .unit] .unit ⟨0, rfl⟩ ?body
    WellFormedTy.unit ?drop
  · exact TermListTyping.cons
      (TermTyping.move boxedLiveStart_x_typing
        boxedLiveStart_not_writeProhibited_x boxedLive_move_x)
      (TermListTyping.singleton (TermTyping.const ValueTyping.unit))
  · exact boxedLiveXMovedEnv_drop_child.symm

theorem boxedLive_borrowUnion_y_x :
    PartialTyUnion (.ty (.borrow true [.var "y"]))
      (.ty (.borrow true [.var "x"]))
      (.ty (.borrow true [.var "y", .var "x"])) := by
  constructor
  · intro candidate hcandidate
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inl htarget)
    · exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inr htarget)
  · intro upper hupper
    exact partialTyStrengthensBorrowAppend
      (hupper (.ty (.borrow true [.var "y"])) (by simp))
      (hupper (.ty (.borrow true [.var "x"])) (by simp))

theorem boxedLive_boxBorrowUnion_y_x :
    PartialTyUnion (.ty (.box (.borrow true [.var "y"])))
      (.ty (.box (.borrow true [.var "x"])))
      (.ty (.box (.borrow true [.var "y", .var "x"]))) := by
  exact PartialTyUnion.tyBox boxedLive_borrowUnion_y_x

theorem boxedLive_shape_py_px :
    ShapeCompatible boxedLiveStartEnv
      (.ty (.box (.borrow true [.var "y"])))
      (.ty (.box (.borrow true [.var "x"]))) := by
  exact ShapeCompatible.tyBox (ShapeCompatible.borrow
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, boxedLiveStart_y_typing⟩)
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, boxedLiveStart_x_typing⟩)
    ShapeCompatible.int)

theorem boxedLive_borrow_x_wellFormed :
    WellFormedTy boxedLiveStartEnv (.borrow true [.var "x"]) Lifetime.root := by
  exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
    intro target htarget
    simp at htarget
    subst htarget
    exact ⟨.int, Lifetime.root, boxedLiveStart_x_typing,
      LifetimeOutlives.refl Lifetime.root,
      ⟨staleJoinXSlot, by
        simp [boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv, staleJoinXSlot,
          staleJoinYSlot, boxedLivePYSlot, Env.update, LVal.base],
        LifetimeOutlives.refl Lifetime.root⟩⟩))

theorem boxedLive_box_borrow_x_wellFormed :
    WellFormedTy boxedLiveStartEnv
      (.box (.borrow true [.var "x"])) Lifetime.root :=
  WellFormedTy.box boxedLive_borrow_x_wellFormed

theorem boxedLive_rhs_typing :
    TermTyping boxedLiveStartEnv StoreTyping.empty staleJoinChildLifetime
      (.box (.borrow true (.var "x")))
      (.box (.borrow true [.var "x"])) boxedLiveStartEnv := by
  exact TermTyping.box
    (TermTyping.mutBorrow boxedLiveStart_x_typing boxedLiveStart_x_mutable
      boxedLiveStart_not_writeProhibited_x)

theorem boxedLive_assign_write :
    EnvWrite 0 boxedLiveStartEnv (.var "p")
      (.box (.borrow true [.var "x"])) boxedLivePAssignedEnv := by
  simpa [boxedLivePAssignedEnv, boxedLivePXSlot, boxedLivePYSlot, LVal.base] using
    (@EnvWrite.intro 0 boxedLiveStartEnv boxedLiveStartEnv (.var "p")
      boxedLivePYSlot (.box (.borrow true [.var "x"]))
      (.ty (.box (.borrow true [.var "x"])))
      (by
        show boxedLiveStartEnv.slotAt "p" = some boxedLivePYSlot
        simp [boxedLiveStartEnv, boxedLivePYSlot, Env.update])
      UpdateAtPath.strong)

def boxedLiveAssignedTypingShape
    (lv : LVal) (partialTy : PartialTy) (lifetime : Lifetime) : Prop :=
  (lv = .var "x" ∧ partialTy = .ty .int ∧ lifetime = Lifetime.root) ∨
    (lv = .var "y" ∧ partialTy = .ty .int ∧ lifetime = Lifetime.root) ∨
    (lv = .var "p" ∧
      partialTy = .ty (.box (.borrow true [.var "x"])) ∧
      lifetime = Lifetime.root)

theorem boxedLiveAssignedEnv_lvalTyping_shape {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTyping boxedLivePAssignedEnv lv partialTy lifetime →
    boxedLiveAssignedTypingShape lv partialTy lifetime := by
  exact LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      boxedLiveAssignedTypingShape lv partialTy lifetime)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    (by
      intro name slot hslot
      by_cases hx : name = "x"
      · subst hx
        have hslotEq : slot = staleJoinXSlot := by
          exact (Option.some.inj
            (by
              simpa [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
                dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
                boxedLivePXSlot, Env.update] using hslot)).symm
        subst hslotEq
        exact Or.inl ⟨rfl, rfl, rfl⟩
      · by_cases hy : name = "y"
        · subst hy
          have hslotEq : slot = staleJoinYSlot := by
            exact (Option.some.inj
              (by
                simpa [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
                  staleJoinYSlot, boxedLivePYSlot, boxedLivePXSlot, Env.update]
                  using hslot)).symm
          subst hslotEq
          exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
        · by_cases hp : name = "p"
          · subst hp
            have hslotEq : slot = boxedLivePXSlot := by
              exact (Option.some.inj
                (by simpa [boxedLivePAssignedEnv, boxedLivePXSlot, Env.update]
                  using hslot)).symm
            subst hslotEq
            exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
          · have hnone : boxedLivePAssignedEnv.slotAt name = none := by
              simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
                dropMoveXEnv, Env.update, Env.empty, hx, hy, hp]
            rw [hnone] at hslot
            cases hslot)
    (by
      intro _source _inner _lifetime _hsource ihSource
      rcases ihSource with hx | hy | hp
      · rcases hx with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hy with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hp with ⟨_hlv, hty, _hlifetime⟩
        cases hty)
    (by
      intro _source _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets ihBorrow _ihTargets
      rcases ihBorrow with hx | hy | hp
      · rcases hx with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hy with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hp with ⟨_hlv, hty, _hlifetime⟩
        cases hty)
    (by intro _target _ty _lifetime _htarget _ihTarget; trivial)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy
        _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
      trivial)

theorem boxedLiveAssignedEnv_no_lval_borrow {lv : LVal} {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTyping boxedLivePAssignedEnv lv (.ty (.borrow mutable targets))
      lifetime := by
  intro htyping
  rcases boxedLiveAssignedEnv_lvalTyping_shape htyping with hx | hy | hp
  · rcases hx with ⟨_hlv, hty, _hlifetime⟩
    cases hty
  · rcases hy with ⟨_hlv, hty, _hlifetime⟩
    cases hty
  · rcases hp with ⟨_hlv, hty, _hlifetime⟩
    cases hty

theorem boxedLiveAssigned_coherent :
    Coherent boxedLivePAssignedEnv := by
  intro lv mutable targets borrowLifetime htyping
  exact False.elim (boxedLiveAssignedEnv_no_lval_borrow htyping)

theorem boxedLiveAssigned_x_typing :
    LValTyping boxedLivePAssignedEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var boxedLivePAssignedEnv "x" staleJoinXSlot (by
    simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
      dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
      boxedLivePXSlot, Env.update])

theorem boxedLiveAssigned_p_contains_borrow_inv {root : Name} {mutable : Bool}
    {targets : List LVal} :
    boxedLivePAssignedEnv ⊢ root ↝ (.borrow mutable targets) →
    root = "p" ∧ mutable = true ∧ targets = [.var "x"] := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hp : root = "p"
  · subst hp
    have hslotEq : slot = boxedLivePXSlot := by
      exact (Option.some.inj
        (by simpa [boxedLivePAssignedEnv, boxedLivePXSlot, Env.update]
          using hslot)).symm
    subst hslotEq
    cases hcontains with
    | tyBox hinner =>
        cases hinner
        exact ⟨rfl, rfl, rfl⟩
  · by_cases hy : root = "y"
    · subst hy
      have hslotEq : slot = staleJoinYSlot := by
        exact (Option.some.inj
          (by
            simpa [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
              staleJoinYSlot, boxedLivePYSlot, boxedLivePXSlot, Env.update]
              using hslot)).symm
      subst hslotEq
      cases hcontains
    · by_cases hx : root = "x"
      · subst hx
        have hslotEq : slot = staleJoinXSlot := by
          exact (Option.some.inj
            (by
              simpa [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
                dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
                boxedLivePXSlot, Env.update] using hslot)).symm
        subst hslotEq
        cases hcontains
      · have hnone : boxedLivePAssignedEnv.slotAt root = none := by
          simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
            dropMoveXEnv, Env.update, Env.empty, hp, hy, hx]
        rw [hnone] at hslot
        cases hslot

theorem boxedLiveAssigned_rhs_targets_wellFormed :
    EnvWriteRhsTargetsWellFormed boxedLivePAssignedEnv
      (.box (.borrow true [.var "x"])) := by
  intro root slot mutable targets target hslot hcontains htarget _hrhs
  rcases boxedLiveAssigned_p_contains_borrow_inv
      ⟨slot, hslot, hcontains⟩ with ⟨rfl, _hmutable, rfl⟩
  simp at htarget
  subst htarget
  exact ⟨.int, Lifetime.root, boxedLiveAssigned_x_typing,
    LifetimeOutlives.refl Lifetime.root,
    ⟨staleJoinXSlot, by
      simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
        dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
        boxedLivePXSlot, Env.update, LVal.base],
      LifetimeOutlives.refl Lifetime.root⟩⟩

theorem boxedLiveAssigned_not_writeProhibited_p :
    ¬ WriteProhibited boxedLivePAssignedEnv (.var "p") := by
  intro hwrite
  cases hwrite with
  | inl hread =>
      rcases hread with ⟨root, targets, target, hcontains, htarget,
        hconflict⟩
      rcases boxedLiveAssigned_p_contains_borrow_inv hcontains with
        ⟨_hroot, _hmutable, rfl⟩
      simp at htarget
      subst htarget
      simp [PathConflicts, LVal.base] at hconflict
  | inr himm =>
      rcases himm with ⟨root, targets, target, hcontains, htarget,
        hconflict⟩
      rcases boxedLiveAssigned_p_contains_borrow_inv hcontains with
        ⟨_hroot, hmutable, _htargets⟩
      cases hmutable

theorem boxedLive_assign_ranked :
    ∃ φ, LinearizedBy φ boxedLiveStartEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ boxedLivePAssignedEnv
        (.box (.borrow true [.var "x"])) := by
  let φ : Name → Nat := fun name => if name = "p" then 1 else 0
  refine ⟨φ, ?linearized, ?below⟩
  · intro root slot hslot v hv
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.box (.borrow true [.var "y"])) := by
        simpa [boxedLiveStartEnv, boxedLivePYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
      subst hv
      simp [φ, LVal.base]
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [boxedLiveStartEnv, boxedLiveXYEnv, staleJoinYSlot,
            boxedLivePYSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars] at hv
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv,
              staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hv
          simp [PartialTy.vars, Ty.vars] at hv
        · have hnone : boxedLiveStartEnv.slotAt root = none := by
            simp [boxedLiveStartEnv, boxedLiveXYEnv, dropMoveXEnv, Env.update,
              Env.empty, hp, hy, hx]
          rw [hnone] at hslot
          cases hslot
  · constructor
    · intro root slot mutable targets target hslot hcontains htarget _hrhs
      rcases boxedLiveAssigned_p_contains_borrow_inv
          ⟨slot, hslot, hcontains⟩ with ⟨rfl, _hmutable, rfl⟩
      simp at htarget
      subst htarget
      simp [φ, LVal.base]
    · intro root other mutable targetsMutable targetsOther targetMutable
        targetOther hcontainsMutable hcontainsOther _htargetMutable
        _htargetOther _hconflict _hrhsMutable _hrhsOther
      rcases boxedLiveAssigned_p_contains_borrow_inv hcontainsMutable with
        ⟨rfl, _hmutable, _htargets⟩
      rcases boxedLiveAssigned_p_contains_borrow_inv hcontainsOther with
        ⟨rfl, _hmutableOther, _htargetsOther⟩
      rfl

theorem boxedLivePAssignedEnv_drop_child :
    boxedLivePAssignedEnv.dropLifetime staleJoinChildLifetime =
      boxedLivePAssignedEnv := by
  apply envExt
  intro name
  by_cases hx : name = "x"
  · subst hx
    simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
      dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
      boxedLivePXSlot, staleJoinChildLifetime, Env.dropLifetime, Env.update,
      Lifetime.root]
  · by_cases hy : name = "y"
    · subst hy
      simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
        dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
        boxedLivePXSlot, staleJoinChildLifetime, Env.dropLifetime, Env.update,
        Lifetime.root]
    · by_cases hp : name = "p"
      · subst hp
        simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
          dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
          boxedLivePXSlot, staleJoinChildLifetime, Env.dropLifetime, Env.update,
          Lifetime.root]
      · simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
          dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
          boxedLivePXSlot, staleJoinChildLifetime, Env.dropLifetime,
          Env.update, Env.empty, hx, hy, hp]

theorem boxedLiveFalseBranch_typing :
    TermTyping boxedLiveStartEnv StoreTyping.empty Lifetime.root
      boxedLiveFalseBranch .unit boxedLivePAssignedEnv := by
  unfold boxedLiveFalseBranch
  refine @TermTyping.block boxedLiveStartEnv boxedLivePAssignedEnv
    boxedLivePAssignedEnv StoreTyping.empty Lifetime.root staleJoinChildLifetime
    [.assign (.var "p") (.box (.borrow true (.var "x")))] .unit
    ⟨0, rfl⟩ ?body WellFormedTy.unit ?drop
  · exact TermListTyping.singleton (TermTyping.assign
      boxedLive_rhs_typing
      boxedLiveStart_p_typing
      boxedLive_shape_py_px
      boxedLive_box_borrow_x_wellFormed
      boxedLive_assign_write
      boxedLive_assign_ranked
      boxedLiveAssigned_coherent
      boxedLiveAssigned_rhs_targets_wellFormed
      boxedLiveAssigned_not_writeProhibited_p)
  · exact boxedLivePAssignedEnv_drop_child.symm

theorem boxedLiveXMoved_le_join :
    EnvStrengthens boxedLiveXMovedEnv boxedLiveJoinEnv := by
  intro name
  by_cases hx : name = "x"
  · subst hx
    rw [show boxedLiveXMovedEnv.slotAt "x" = some staleJoinXMovedSlot by
        simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
          dropMoveXEnv, staleJoinXMovedSlot, staleJoinXSlot, staleJoinYSlot,
          boxedLivePYSlot, Env.update],
      show boxedLiveJoinEnv.slotAt "x" = some staleJoinXMovedSlot by
        simp [boxedLiveJoinEnv, staleJoinXMovedSlot, Env.update]]
    exact ⟨rfl, PartialTyStrengthens.reflex⟩
  · by_cases hy : name = "y"
    · subst hy
      rw [show boxedLiveXMovedEnv.slotAt "y" = some staleJoinYSlot by
          simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
            dropMoveXEnv, staleJoinXMovedSlot, staleJoinXSlot, staleJoinYSlot,
            boxedLivePYSlot, Env.update],
        show boxedLiveJoinEnv.slotAt "y" = some staleJoinYSlot by
          simp [boxedLiveJoinEnv, staleJoinYSlot, Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hp : name = "p"
      · subst hp
        rw [show boxedLiveXMovedEnv.slotAt "p" = some boxedLivePYSlot by
            simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLivePYSlot,
              staleJoinXMovedSlot, Env.update],
          show boxedLiveJoinEnv.slotAt "p" = some boxedLivePJoinSlot by
            simp [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update]]
        exact ⟨rfl, PartialTyUnion.left_strengthens
          boxedLive_boxBorrowUnion_y_x⟩
      · rw [show boxedLiveXMovedEnv.slotAt name = none by
            simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
              dropMoveXEnv, Env.update, Env.empty, hx, hy, hp],
          show boxedLiveJoinEnv.slotAt name = none by
            simp [boxedLiveJoinEnv, Env.update, Env.empty, hx, hy, hp]]
        trivial

theorem boxedLivePAssigned_le_join :
    EnvStrengthens boxedLivePAssignedEnv boxedLiveJoinEnv := by
  intro name
  by_cases hx : name = "x"
  · subst hx
    rw [show boxedLivePAssignedEnv.slotAt "x" = some staleJoinXSlot by
        simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
          dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
          boxedLivePXSlot, Env.update],
      show boxedLiveJoinEnv.slotAt "x" = some staleJoinXMovedSlot by
        simp [boxedLiveJoinEnv, staleJoinXMovedSlot, Env.update]]
    exact ⟨rfl, PartialTyStrengthens.intoUndef PartialTyStrengthens.reflex⟩
  · by_cases hy : name = "y"
    · subst hy
      rw [show boxedLivePAssignedEnv.slotAt "y" = some staleJoinYSlot by
          simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
            dropMoveXEnv, staleJoinXSlot, staleJoinYSlot, boxedLivePYSlot,
            boxedLivePXSlot, Env.update],
        show boxedLiveJoinEnv.slotAt "y" = some staleJoinYSlot by
          simp [boxedLiveJoinEnv, staleJoinYSlot, Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hp : name = "p"
      · subst hp
        rw [show boxedLivePAssignedEnv.slotAt "p" = some boxedLivePXSlot by
            simp [boxedLivePAssignedEnv, boxedLivePXSlot, Env.update],
          show boxedLiveJoinEnv.slotAt "p" = some boxedLivePJoinSlot by
            simp [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update]]
        exact ⟨rfl, PartialTyUnion.right_strengthens
          boxedLive_boxBorrowUnion_y_x⟩
      · rw [show boxedLivePAssignedEnv.slotAt name = none by
            simp [boxedLivePAssignedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
              dropMoveXEnv, Env.update, Env.empty, hx, hy, hp],
          show boxedLiveJoinEnv.slotAt name = none by
            simp [boxedLiveJoinEnv, Env.update, Env.empty, hx, hy, hp]]
        trivial

theorem boxedLiveJoin_least {env' : Env}
    (hmoved : EnvStrengthens boxedLiveXMovedEnv env')
    (hassigned : EnvStrengthens boxedLivePAssignedEnv env') :
    EnvStrengthens boxedLiveJoinEnv env' := by
  intro name
  by_cases hp : name = "p"
  · subst hp
    rcases EnvStrengthens.slot_forward hmoved (show
        boxedLiveXMovedEnv.slotAt "p" = some boxedLivePYSlot by
          simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLivePYSlot,
            staleJoinXMovedSlot, Env.update]) with
      ⟨slotY, hslotY, hlife, hstrY⟩
    rcases EnvStrengthens.slot_forward hassigned (show
        boxedLivePAssignedEnv.slotAt "p" = some boxedLivePXSlot by
          simp [boxedLivePAssignedEnv, boxedLivePXSlot, Env.update]) with
      ⟨slotX, hslotX, _hlifeX, hstrX⟩
    have hslotEq : slotX = slotY := Option.some.inj (hslotX.symm.trans hslotY)
    subst hslotEq
    rw [show boxedLiveJoinEnv.slotAt "p" = some boxedLivePJoinSlot by
        simp [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update], hslotX]
    have hP : PartialTyStrengthens boxedLivePJoinSlot.ty slotX.ty :=
      boxedLive_boxBorrowUnion_y_x.2 (by
        intro candidate hcandidate
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
        rcases hcandidate with rfl | rfl
        · exact hstrY
        · exact hstrX)
    exact ⟨hlife, hP⟩
  · by_cases hy : name = "y"
    · subst hy
      rcases EnvStrengthens.slot_forward hmoved (show
          boxedLiveXMovedEnv.slotAt "y" = some staleJoinYSlot by
            simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
              dropMoveXEnv, staleJoinXMovedSlot, staleJoinXSlot,
              staleJoinYSlot, boxedLivePYSlot, Env.update]) with
        ⟨slot', hslot', hlife, hstr⟩
      rw [show boxedLiveJoinEnv.slotAt "y" = some staleJoinYSlot by
          simp [boxedLiveJoinEnv, staleJoinYSlot, Env.update], hslot']
      exact ⟨hlife, hstr⟩
    · by_cases hx : name = "x"
      · subst hx
        rcases EnvStrengthens.slot_forward hmoved (show
            boxedLiveXMovedEnv.slotAt "x" = some staleJoinXMovedSlot by
              simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
                dropMoveXEnv, staleJoinXMovedSlot, staleJoinXSlot,
                staleJoinYSlot, boxedLivePYSlot, Env.update]) with
          ⟨slot', hslot', hlife, hstr⟩
        rw [show boxedLiveJoinEnv.slotAt "x" = some staleJoinXMovedSlot by
            simp [boxedLiveJoinEnv, staleJoinXMovedSlot, Env.update], hslot']
        exact ⟨hlife, hstr⟩
      · have hmovedNone : boxedLiveXMovedEnv.slotAt name = none := by
          simp [boxedLiveXMovedEnv, boxedLiveStartEnv, boxedLiveXYEnv,
            dropMoveXEnv, Env.update, Env.empty, hp, hy, hx]
        have hjoinNone : boxedLiveJoinEnv.slotAt name = none := by
          simp [boxedLiveJoinEnv, Env.update, Env.empty, hp, hy, hx]
        have h := hmoved name
        rw [hmovedNone] at h
        rw [hjoinNone]
        cases henvSlot : env'.slotAt name with
        | none =>
            trivial
        | some envSlot =>
            rw [henvSlot] at h
            cases h

theorem boxedLive_envJoin :
    EnvJoin boxedLiveXMovedEnv boxedLivePAssignedEnv boxedLiveJoinEnv := by
  constructor
  · intro env henv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at henv
    rcases henv with rfl | rfl
    · exact boxedLiveXMoved_le_join
    · exact boxedLivePAssigned_le_join
  · intro env' henv'
    exact boxedLiveJoin_least
      (henv' boxedLiveXMovedEnv (by simp))
      (henv' boxedLivePAssignedEnv (by simp))

def boxedLiveJoinTypingShape
    (lv : LVal) (partialTy : PartialTy) (lifetime : Lifetime) : Prop :=
  (lv = .var "x" ∧ partialTy = .undef .int ∧ lifetime = Lifetime.root) ∨
    (lv = .var "y" ∧ partialTy = .ty .int ∧ lifetime = Lifetime.root) ∨
    (lv = .var "p" ∧
      partialTy = .ty (.box (.borrow true [.var "y", .var "x"])) ∧
      lifetime = Lifetime.root)

theorem boxedLiveJoinEnv_lvalTyping_shape {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTyping boxedLiveJoinEnv lv partialTy lifetime →
    boxedLiveJoinTypingShape lv partialTy lifetime := by
  exact LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      boxedLiveJoinTypingShape lv partialTy lifetime)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    (by
      intro name slot hslot
      by_cases hx : name = "x"
      · subst hx
        have hslotEq : slot = staleJoinXMovedSlot := by
          exact (Option.some.inj
            (by simpa [boxedLiveJoinEnv, staleJoinXMovedSlot, Env.update]
              using hslot)).symm
        subst hslotEq
        exact Or.inl ⟨rfl, rfl, rfl⟩
      · by_cases hy : name = "y"
        · subst hy
          have hslotEq : slot = staleJoinYSlot := by
            exact (Option.some.inj
              (by simpa [boxedLiveJoinEnv, staleJoinYSlot, Env.update]
                using hslot)).symm
          subst hslotEq
          exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
        · by_cases hp : name = "p"
          · subst hp
            have hslotEq : slot = boxedLivePJoinSlot := by
              exact (Option.some.inj
                (by simpa [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update]
                  using hslot)).symm
            subst hslotEq
            exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
          · have hnone : boxedLiveJoinEnv.slotAt name = none := by
              simp [boxedLiveJoinEnv, Env.update, Env.empty, hx, hy, hp]
            rw [hnone] at hslot
            cases hslot)
    (by
      intro _source _inner _lifetime _hsource ihSource
      rcases ihSource with hx | hy | hp
      · rcases hx with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hy with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hp with ⟨_hlv, hty, _hlifetime⟩
        cases hty)
    (by
      intro _source _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets ihBorrow _ihTargets
      rcases ihBorrow with hx | hy | hp
      · rcases hx with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hy with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hp with ⟨_hlv, hty, _hlifetime⟩
        cases hty)
    (by intro _target _ty _lifetime _htarget _ihTarget; trivial)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy
        _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
      trivial)

theorem boxedLiveJoinEnv_no_lval_borrow {lv : LVal} {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTyping boxedLiveJoinEnv lv (.ty (.borrow mutable targets))
      lifetime := by
  intro htyping
  rcases boxedLiveJoinEnv_lvalTyping_shape htyping with hx | hy | hp
  · rcases hx with ⟨_hlv, hty, _hlifetime⟩
    cases hty
  · rcases hy with ⟨_hlv, hty, _hlifetime⟩
    cases hty
  · rcases hp with ⟨_hlv, hty, _hlifetime⟩
    cases hty

theorem boxedLiveJoin_coherent :
    Coherent boxedLiveJoinEnv := by
  intro lv mutable targets borrowLifetime htyping
  exact False.elim (boxedLiveJoinEnv_no_lval_borrow htyping)

theorem boxedLiveJoin_linearizable :
    Linearizable boxedLiveJoinEnv := by
  refine ⟨fun name => if name = "p" then 1 else 0, ?_⟩
  intro name slot hslot v hv
  by_cases hp : name = "p"
  · subst hp
    have hslotTy :
        slot.ty = .ty (.box (.borrow true [.var "y", .var "x"])) := by
      simpa [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hv
    simp [PartialTy.vars, Ty.vars, LVal.base] at hv
    rcases hv with rfl | rfl <;> simp
  · by_cases hy : name = "y"
    · subst hy
      have hslotTy : slot.ty = .ty .int := by
        simpa [boxedLiveJoinEnv, staleJoinYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · by_cases hx : name = "x"
      · subst hx
        have hslotTy : slot.ty = .undef .int := by
          simpa [boxedLiveJoinEnv, staleJoinXMovedSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars] at hv
      · have hnone : boxedLiveJoinEnv.slotAt name = none := by
          simp [boxedLiveJoinEnv, Env.update, Env.empty, hp, hy, hx]
        rw [hnone] at hslot
        cases hslot

theorem boxedLiveJoin_p_contains_borrow_inv {root : Name} {mutable : Bool}
    {targets : List LVal} :
    boxedLiveJoinEnv ⊢ root ↝ (.borrow mutable targets) →
    root = "p" ∧ mutable = true ∧ targets = [.var "y", .var "x"] := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hp : root = "p"
  · subst hp
    have hslotEq : slot = boxedLivePJoinSlot := by
      exact (Option.some.inj
        (by simpa [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update]
          using hslot)).symm
    subst hslotEq
    cases hcontains with
    | tyBox hinner =>
        cases hinner
        exact ⟨rfl, rfl, rfl⟩
  · by_cases hy : root = "y"
    · subst hy
      have hslotEq : slot = staleJoinYSlot := by
        exact (Option.some.inj
          (by simpa [boxedLiveJoinEnv, staleJoinYSlot, Env.update]
            using hslot)).symm
      subst hslotEq
      cases hcontains
    · by_cases hx : root = "x"
      · subst hx
        have hslotEq : slot = staleJoinXMovedSlot := by
          exact (Option.some.inj
            (by simpa [boxedLiveJoinEnv, staleJoinXMovedSlot, Env.update]
              using hslot)).symm
        subst hslotEq
        cases hcontains
      · have hnone : boxedLiveJoinEnv.slotAt root = none := by
          simp [boxedLiveJoinEnv, Env.update, Env.empty, hp, hy, hx]
        rw [hnone] at hslot
        cases hslot

theorem boxedLiveJoin_borrowSafe :
    BorrowSafeEnv boxedLiveJoinEnv := by
  intro x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther _htargetMutable _htargetOther _hconflict
  rcases boxedLiveJoin_p_contains_borrow_inv hcontainsMutable with
    ⟨rfl, _hmutable, _htargetsMutable⟩
  rcases boxedLiveJoin_p_contains_borrow_inv hcontainsOther with
    ⟨rfl, _hmutableOther, _htargetsOther⟩
  rfl

theorem boxedLiveIf_typing :
    TermTyping boxedLiveStartEnv StoreTyping.empty Lifetime.root
      boxedLiveIf .unit boxedLiveJoinEnv := by
  unfold boxedLiveIf
  exact TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    boxedLiveTrueBranch_typing
    boxedLiveFalseBranch_typing
    (PartialTyJoin.self (.ty .unit))
    boxedLive_envJoin
    WellFormedTy.unit
    boxedLiveJoin_coherent
    boxedLiveJoin_linearizable
    boxedLiveJoin_borrowSafe
    (tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit)

theorem boxedLiveJoin_p_live :
    LValTyping boxedLiveJoinEnv (.var "p")
      (.ty (.box (.borrow true [.var "y", .var "x"]))) Lifetime.root := by
  exact @LValTyping.var boxedLiveJoinEnv "p" boxedLivePJoinSlot (by
    simp [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update])

theorem boxedLiveJoin_x_undef_typing :
    LValTyping boxedLiveJoinEnv (.var "x") (.undef .int) Lifetime.root := by
  exact @LValTyping.var boxedLiveJoinEnv "x" staleJoinXMovedSlot (by
    simp [boxedLiveJoinEnv, staleJoinXMovedSlot, Env.update])

theorem boxedLiveJoin_y_typing :
    LValTyping boxedLiveJoinEnv (.var "y") (.ty .int) Lifetime.root := by
  exact @LValTyping.var boxedLiveJoinEnv "y" staleJoinYSlot (by
    simp [boxedLiveJoinEnv, staleJoinYSlot, Env.update])

theorem boxedLiveJoin_int_undef_union :
    PartialTyUnion (.ty .int) (.undef .int) (.undef .int) := by
  constructor
  · intro candidate hcandidate
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact PartialTyStrengthens.intoUndef PartialTyStrengthens.reflex
    · exact PartialTyStrengthens.reflex
  · intro upper hupper
    exact hupper (.undef .int) (by simp)

theorem boxedLiveJoin_y_x_targets_maybe_typing :
    LValTargetsMaybeTyping boxedLiveJoinEnv [.var "y", .var "x"]
      (.undef .int) Lifetime.root := by
  exact LValTargetsMaybeTyping.cons
    boxedLiveJoin_y_typing
    (LValTargetsMaybeTyping.singleton boxedLiveJoin_x_undef_typing)
    boxedLiveJoin_int_undef_union
    (LifetimeIntersection.self Lifetime.root)

theorem boxedLiveJoin_writeProhibited_x :
    WriteProhibited boxedLiveJoinEnv (.var "x") := by
  exact Or.inl
    ⟨"p", [.var "y", .var "x"], .var "x",
      ⟨boxedLivePJoinSlot,
        by simp [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update],
        PartialTyContains.tyBox PartialTyContains.here⟩,
      by simp, by simp [PathConflicts, LVal.base]⟩

theorem boxedLiveJoin_no_deref_p_typing {partialTy : PartialTy}
    {lifetime : Lifetime} :
    ¬ LValTyping boxedLiveJoinEnv (.deref (.var "p")) partialTy lifetime := by
  intro htyping
  cases htyping with
  | box hsource =>
      rcases LValTyping.var_inv hsource with
        ⟨slot, hslot, htyEq, _hlifetimeEq⟩
      have hslotEq : slot = boxedLivePJoinSlot := by
        exact (Option.some.inj
          (by simpa [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update]
            using hslot)).symm
      subst hslotEq
      simp [boxedLivePJoinSlot] at htyEq
  | borrow hsource _htargets =>
      rcases LValTyping.var_inv hsource with
        ⟨slot, hslot, htyEq, _hlifetimeEq⟩
      have hslotEq : slot = boxedLivePJoinSlot := by
        exact (Option.some.inj
          (by simpa [boxedLiveJoinEnv, boxedLivePJoinSlot, Env.update]
            using hslot)).symm
      subst hslotEq
      simp [boxedLivePJoinSlot] at htyEq

/-! ## Box result join -/

def boxJoinStartEnv : Env :=
  (Env.empty.update "x" staleJoinXSlot).update "y" staleJoinYSlot

def boxJoinMovedEnv : Env :=
  boxJoinStartEnv.update "x" staleJoinXMovedSlot

def boxJoinResultTy : Ty :=
  .box (.borrow true [.var "y", .var "x"])

def boxJoinSketch : Term :=
  .ite (.val (.bool true))
    (.block staleJoinChildLifetime
      [.move (.var "x"), .box (.borrow true (.var "y"))])
    (.box (.borrow true (.var "x")))

theorem boxJoinMoved_x_not_initialized :
    ¬ ∃ ty lifetime,
      LValTyping boxJoinMovedEnv (.var "x") (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htyping⟩
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, htyEq, _hlifetimeEq⟩
  have hslotEq : slot = staleJoinXMovedSlot := by
    exact (Option.some.inj
      (by simpa [boxJoinMovedEnv, staleJoinXMovedSlot, Env.update]
        using hslot)).symm
  subst hslotEq
  simp [staleJoinXMovedSlot] at htyEq

theorem boxJoinMoved_y_typing :
    LValTyping boxJoinMovedEnv (.var "y") (.ty .int) Lifetime.root := by
  exact @LValTyping.var boxJoinMovedEnv "y" staleJoinYSlot
    (by
      simp [boxJoinMovedEnv, boxJoinStartEnv, staleJoinXMovedSlot,
        staleJoinXSlot, staleJoinYSlot, Env.update])

theorem boxJoinMoved_x_base_outlives :
    LValBaseOutlives boxJoinMovedEnv (.var "x") Lifetime.root := by
  exact ⟨staleJoinXMovedSlot,
    by
      show boxJoinMovedEnv.slotAt "x" = some staleJoinXMovedSlot
      simp [boxJoinMovedEnv, staleJoinXMovedSlot, Env.update],
    LifetimeOutlives.refl Lifetime.root⟩

theorem boxJoinMoved_y_base_outlives :
    LValBaseOutlives boxJoinMovedEnv (.var "y") Lifetime.root := by
  exact ⟨staleJoinYSlot,
    by
      show boxJoinMovedEnv.slotAt "y" = some staleJoinYSlot
      simp [boxJoinMovedEnv, boxJoinStartEnv, staleJoinXMovedSlot,
        staleJoinXSlot, staleJoinYSlot, Env.update],
    LifetimeOutlives.refl Lifetime.root⟩

theorem boxJoin_targets_wellFormed_whenInitialized :
    BorrowTargetsWellFormedWhenInitialized boxJoinMovedEnv
      [.var "y", .var "x"] Lifetime.root := by
  intro target htarget
  simp at htarget
  rcases htarget with htarget | htarget
  · subst htarget
    refine ⟨boxJoinMoved_y_base_outlives, ?_⟩
    intro _hinitialized
    exact ⟨.int, Lifetime.root, boxJoinMoved_y_typing,
      LifetimeOutlives.refl Lifetime.root, boxJoinMoved_y_base_outlives⟩
  · subst htarget
    refine ⟨boxJoinMoved_x_base_outlives, ?_⟩
    intro hinitialized
    exact False.elim (boxJoinMoved_x_not_initialized hinitialized)

theorem boxJoin_result_wellFormed_whenInitialized :
    WellFormedTyWhenInitialized boxJoinMovedEnv boxJoinResultTy Lifetime.root := by
  unfold boxJoinResultTy
  exact WellFormedTyWhenInitialized.box
    (WellFormedTyWhenInitialized.borrow
      boxJoin_targets_wellFormed_whenInitialized)

theorem boxJoin_result_not_wellFormed :
    ¬ WellFormedTy boxJoinMovedEnv boxJoinResultTy Lifetime.root := by
  intro hwell
  unfold boxJoinResultTy at hwell
  cases hwell with
  | box hborrow =>
      cases hborrow with
      | borrow htargets =>
          cases htargets with
          | intro htargetsFn =>
          rcases htargetsFn (.var "x") (by simp) with
            ⟨targetTy, targetLifetime, htyping, _houtlives, _hbase⟩
          exact boxJoinMoved_x_not_initialized
            ⟨targetTy, targetLifetime, htyping⟩

end Paper
end LwRust
