import LwRust.Paper.Typing

/-!
Examples for declared boxes as lvalues.

The paper treats `box T` as an owned pointer type: if `p : box int`, then `*p`
is an lvalue of type `int`.  These examples check that declared full-box types
(`.ty (.box inner)`) bridge into lvalue/path typing.
-/

namespace LwRust
namespace Paper

open Core

namespace BoxDerefPending

/--
Rust-style:

```rust
{
    let mut p = box 0;
    *p
}
```
-/
def declaredBoxReadProgram : Term :=
  .block [0]
    [ .letMut "p" (.box (.val (.int 0)))
    , .move (.deref (.var "p"))
    ]

/--
Rust-style:

```rust
{
    let mut p = box 0;
    *p = 1;
}
```
-/
def declaredBoxWriteProgram : Term :=
  .block [0]
    [ .letMut "p" (.box (.val (.int 0)))
    , .assign (.deref (.var "p")) (.val (.int 1))
    ]

/--
Rust-style:

```rust
{
    let mut p = box 0;
    let mut r = &mut *p;
}
```
-/
def declaredBoxBorrowProgram : Term :=
  .block [0]
    [ .letMut "p" (.box (.val (.int 0)))
    , .letMut "r" (.borrow true (.deref (.var "p")))
    ]

/--
Environment shape after `let mut p = box 0`.
-/
def declaredBoxIntSlot : EnvSlot :=
  { ty := .ty (.box .int), lifetime := Lifetime.root }

def declaredBoxIntEnv : Env :=
  Env.empty.update "p" declaredBoxIntSlot

theorem declaredBoxInt_var_typing :
    LValTyping declaredBoxIntEnv (.var "p") (.ty (.box .int))
      Lifetime.root := by
  exact @LValTyping.var declaredBoxIntEnv "p" declaredBoxIntSlot (by
    simp [declaredBoxIntEnv, declaredBoxIntSlot])

def blockLifetime : Lifetime := [0]

def blockBoxIntSlot : EnvSlot :=
  { ty := .ty (.box .int), lifetime := blockLifetime }

def blockBoxIntEnv : Env :=
  Env.empty.update "p" blockBoxIntSlot

theorem blockBoxInt_lval_cases {lv : LVal} {pt : PartialTy} {lf : Lifetime} :
    LValTyping blockBoxIntEnv lv pt lf →
      (lv = .var "p" ∧ pt = .ty (.box .int) ∧ lf = blockLifetime) ∨
      (lv = .deref (.var "p") ∧ pt = .ty .int ∧ lf = blockLifetime) := by
  intro h
  refine LValTyping.rec
    (motive_1 := fun lv pt lf _ =>
      (lv = .var "p" ∧ pt = .ty (.box .int) ∧ lf = blockLifetime) ∨
      (lv = .deref (.var "p") ∧ pt = .ty .int ∧ lf = blockLifetime))
    (motive_2 := fun _targets _pt _lf _ => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons h
  case var =>
    intro x slot hslot
    by_cases hx : x = "p"
    · subst hx
      have hslotEq : blockBoxIntSlot = slot := by
        simpa [blockBoxIntEnv] using hslot
      cases hslotEq
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · simp [blockBoxIntEnv, Env.update, Env.empty, hx] at hslot
  case box =>
    intro _lv _inner _lifetime _hsource ih
    rcases ih with hvar | hderef
    · rcases hvar with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hderef with ⟨_hlv, hty, _hlf⟩
      cases hty
  case boxFull =>
    intro _lv _inner _lifetime _hsource ih
    rcases ih with hvar | hderef
    · rcases hvar with ⟨hlv, hty, hlf⟩
      cases hty
      subst hlv
      subst hlf
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · rcases hderef with ⟨_hlv, hty, _hlf⟩
      cases hty
  case borrow =>
    intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hsource _htargets ihSource _ihTargets
    rcases ihSource with hvar | hderef
    · rcases hvar with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hderef with ⟨_hlv, hty, _hlf⟩
      cases hty
  case singleton =>
    intro _target _ty _lifetime _htarget _ihTarget
    trivial
  case cons =>
    intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy
      _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

theorem blockBoxInt_no_borrow_lval {lv : LVal} {mutable : Bool}
    {targets : List LVal} {lf : Lifetime} :
    ¬ LValTyping blockBoxIntEnv lv (.ty (.borrow mutable targets)) lf := by
  intro h
  rcases blockBoxInt_lval_cases h with hvar | hderef
  · rcases hvar with ⟨_hlv, hty, _hlf⟩
    cases hty
  · rcases hderef with ⟨_hlv, hty, _hlf⟩
    cases hty

theorem blockBoxInt_no_contains_borrow {x : Name} {mutable : Bool}
    {targets : List LVal} :
    ¬ EnvContains blockBoxIntEnv x (.borrow mutable targets) := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hty⟩
  by_cases hx : x = "p"
  · subst hx
    have hslotEq : blockBoxIntSlot = slot := by
      simpa [blockBoxIntEnv] using hslot
    cases hslotEq
    cases hty with
    | tyBox hinner =>
        cases hinner
  · simp [blockBoxIntEnv, Env.update, Env.empty, hx] at hslot

theorem blockBoxInt_not_writeProhibited (lv : LVal) :
    ¬ WriteProhibited blockBoxIntEnv lv := by
  intro hwp
  rcases hwp with hread | himm
  · rcases hread with ⟨_x, _targets, _target, hcontains, _htarget,
      _hconflict⟩
    exact blockBoxInt_no_contains_borrow hcontains
  · rcases himm with ⟨_x, _targets, _target, hcontains, _htarget,
      _hconflict⟩
    exact blockBoxInt_no_contains_borrow hcontains

theorem boxIntDeclareCoherence :
    FreshUpdateCoherenceObligations Env.empty "p" (.box .int)
      blockLifetime := by
  constructor
  · intro lv mutable targets borrowLifetime _hbase htyping
    have htyping' :
        LValTyping blockBoxIntEnv lv (.ty (.borrow mutable targets))
          borrowLifetime := by
      simpa [blockBoxIntEnv, blockBoxIntSlot] using htyping
    exact False.elim (blockBoxInt_no_borrow_lval htyping')
  · intro lv mutable targets borrowLifetime _hbase htyping
    have htyping' :
        LValTyping blockBoxIntEnv lv (.ty (.borrow mutable targets))
          borrowLifetime := by
      simpa [blockBoxIntEnv, blockBoxIntSlot] using htyping
    exact False.elim (blockBoxInt_no_borrow_lval htyping')

theorem declareBox_typing :
    TermTyping Env.empty StoreTyping.empty blockLifetime
      (.letMut "p" (.box (.val (.int 0)))) .unit blockBoxIntEnv := by
  refine TermTyping.declare ?fresh ?init ?freshOut boxIntDeclareCoherence ?env
  · simp [Env.fresh, Env.empty]
  · exact TermTyping.box (TermTyping.const ValueTyping.int)
  · simp [Env.fresh, Env.empty]
  · rfl

theorem blockBoxInt_var_typing :
    LValTyping blockBoxIntEnv (.var "p") (.ty (.box .int)) blockLifetime := by
  exact @LValTyping.var blockBoxIntEnv "p" blockBoxIntSlot (by
    simp [blockBoxIntEnv, blockBoxIntSlot])

theorem blockBoxInt_deref_typing :
    LValTyping blockBoxIntEnv (.deref (.var "p")) (.ty .int)
      blockLifetime := by
  exact LValTyping.boxFull blockBoxInt_var_typing

def blockBoxIntMovedSlot : EnvSlot :=
  { blockBoxIntSlot with ty := .box (.undef .int) }

def blockBoxIntMovedEnv : Env :=
  blockBoxIntEnv.update "p" blockBoxIntMovedSlot

theorem blockBoxInt_move_deref :
    EnvMove blockBoxIntEnv (.deref (.var "p")) blockBoxIntMovedEnv := by
  refine ⟨blockBoxIntSlot, .box (.undef .int), ?slot, ?strike, rfl⟩
  · simp [blockBoxIntEnv, blockBoxIntSlot, LVal.base]
  · change Strike [()] (.ty (.box .int)) (.box (.undef .int))
    rfl

theorem moveDeref_typing :
    TermTyping blockBoxIntEnv StoreTyping.empty blockLifetime
      (.move (.deref (.var "p"))) .int blockBoxIntMovedEnv := by
  exact TermTyping.move blockBoxInt_deref_typing
    (blockBoxInt_not_writeProhibited _) blockBoxInt_move_deref

theorem declaredBoxReadProgram_terms_typing :
    TermListTyping Env.empty StoreTyping.empty blockLifetime
      [ .letMut "p" (.box (.val (.int 0)))
      , .move (.deref (.var "p"))
      ] .int blockBoxIntMovedEnv := by
  exact TermListTyping.cons declareBox_typing
    (TermListTyping.singleton moveDeref_typing)

theorem declaredBoxReadProgram_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root declaredBoxReadProgram .int
      (blockBoxIntMovedEnv.dropLifetime blockLifetime) := by
  unfold declaredBoxReadProgram
  refine TermTyping.block ?child declaredBoxReadProgram_terms_typing
    WellFormedTy.int rfl
  exact ⟨0, rfl⟩

def blockBoxIntWriteEnv : Env :=
  blockBoxIntEnv.update "p" blockBoxIntSlot

theorem blockBoxInt_write_deref :
    EnvWrite 0 blockBoxIntEnv (.deref (.var "p")) .int
      blockBoxIntWriteEnv := by
  refine EnvWrite.intro
    (slot := blockBoxIntSlot)
    (updatedTy := .ty (.box .int))
    ?slot
    ?update
  · simp [blockBoxIntEnv, blockBoxIntSlot, LVal.base]
  · change UpdateAtPath 0 blockBoxIntEnv [()] (.ty (.box .int)) .int
      blockBoxIntEnv (.ty (.box .int))
    exact UpdateAtPath.boxFull (path := []) (inner := .int)
      UpdateAtPath.strong

theorem blockBoxIntWriteEnv_eq : blockBoxIntWriteEnv = blockBoxIntEnv := by
  unfold blockBoxIntWriteEnv blockBoxIntEnv Env.update
  simp
  funext y
  by_cases hy : y = "p"
  · simp [hy]
  · simp [hy]

theorem blockBoxInt_write_deref_same :
    EnvWrite 0 blockBoxIntEnv (.deref (.var "p")) .int blockBoxIntEnv := by
  simpa [blockBoxIntWriteEnv_eq] using blockBoxInt_write_deref

theorem int_no_contains_borrow {mutable : Bool} {targets : List LVal} :
    ¬ PartialTyContains (.ty .int) (.borrow mutable targets) := by
  intro h
  cases h

theorem blockBoxInt_linearized : LinearizedBy (fun _ => 0) blockBoxIntEnv := by
  intro x slot hslot v hv
  by_cases hx : x = "p"
  · subst hx
    have hslotEq : blockBoxIntSlot = slot := by
      simpa [blockBoxIntEnv] using hslot
    cases hslotEq
    simp [blockBoxIntSlot, PartialTy.vars, Ty.vars] at hv
  · simp [blockBoxIntEnv, Env.update, Env.empty, hx] at hslot

theorem blockBoxInt_rhsBorrowBelow_int :
    EnvWriteRhsBorrowTargetsBelow (fun _ => 0) blockBoxIntEnv .int := by
  constructor
  · intro _x _slot _mutable _targets _target _hslot _hcontains _htarget hrhs
    rcases hrhs with ⟨_rhsMutable, _rhsTargets, hcontainsRhs, _hmem⟩
    exact False.elim (int_no_contains_borrow hcontainsRhs)
  · intro _x _y _mutable _targetsMutable _targetsOther _targetMutable
      _targetOther _hx _hy _htargetMutable _htargetOther _hconflict
      hrhsMutable _hrhsOther
    rcases hrhsMutable with ⟨_rhsMutable, _rhsTargets, hcontainsRhs, _hmem⟩
    exact False.elim (int_no_contains_borrow hcontainsRhs)

theorem blockBoxInt_coherent : Coherent blockBoxIntEnv := by
  intro _lv _mutable _targets _borrowLifetime htyping
  exact False.elim (blockBoxInt_no_borrow_lval htyping)

theorem blockBoxInt_rhsTargetsWellFormed_int :
    EnvWriteRhsTargetsWellFormed blockBoxIntEnv .int := by
  intro _x _slot _mutable _targets _target _hslot _hcontains _htarget hrhs
  rcases hrhs with ⟨_rhsMutable, _rhsTargets, hcontainsRhs, _hmem⟩
  exact False.elim (int_no_contains_borrow hcontainsRhs)

theorem assignDeref_typing :
    TermTyping blockBoxIntEnv StoreTyping.empty blockLifetime
      (.assign (.deref (.var "p")) (.val (.int 1))) .unit blockBoxIntEnv := by
  refine TermTyping.assign
    (TermTyping.const ValueTyping.int)
    blockBoxInt_deref_typing
    ShapeCompatible.int
    WellFormedTy.int
    blockBoxInt_write_deref_same
    ?rank
    blockBoxInt_coherent
    blockBoxInt_rhsTargetsWellFormed_int
    (blockBoxInt_not_writeProhibited _)
  exact ⟨fun _ => 0, blockBoxInt_linearized, blockBoxInt_rhsBorrowBelow_int⟩

theorem declaredBoxWriteProgram_terms_typing :
    TermListTyping Env.empty StoreTyping.empty blockLifetime
      [ .letMut "p" (.box (.val (.int 0)))
      , .assign (.deref (.var "p")) (.val (.int 1))
      ] .unit blockBoxIntEnv := by
  exact TermListTyping.cons declareBox_typing
    (TermListTyping.singleton assignDeref_typing)

theorem declaredBoxWriteProgram_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root declaredBoxWriteProgram .unit
      (blockBoxIntEnv.dropLifetime blockLifetime) := by
  unfold declaredBoxWriteProgram
  refine TermTyping.block ?child declaredBoxWriteProgram_terms_typing
    WellFormedTy.unit rfl
  exact ⟨0, rfl⟩

def blockBorrowSlot : EnvSlot :=
  { ty := .ty (.borrow true [.deref (.var "p")]), lifetime := blockLifetime }

def blockBorrowEnv : Env :=
  blockBoxIntEnv.update "r" blockBorrowSlot

theorem blockBoxInt_mutable_deref :
    Mutable blockBoxIntEnv (.deref (.var "p")) := by
  have hpMutable : Mutable blockBoxIntEnv (.var "p") := by
    exact Mutable.var (slot := blockBoxIntSlot) (by
      simp [blockBoxIntEnv, blockBoxIntSlot])
  exact Mutable.boxFull blockBoxInt_var_typing hpMutable

theorem borrowDeref_typing :
    TermTyping blockBoxIntEnv StoreTyping.empty blockLifetime
      (.borrow true (.deref (.var "p")))
      (.borrow true [.deref (.var "p")]) blockBoxIntEnv := by
  exact TermTyping.mutBorrow blockBoxInt_deref_typing blockBoxInt_mutable_deref
    (blockBoxInt_not_writeProhibited _)

theorem blockBorrow_lval_cases {lv : LVal} {pt : PartialTy} {lf : Lifetime} :
    LValTyping blockBorrowEnv lv pt lf →
      (lv = .var "p" ∧ pt = .ty (.box .int) ∧ lf = blockLifetime) ∨
      (lv = .deref (.var "p") ∧ pt = .ty .int ∧ lf = blockLifetime) ∨
      (lv = .var "r" ∧ pt = .ty (.borrow true [.deref (.var "p")]) ∧
        lf = blockLifetime) ∨
      (lv = .deref (.var "r") ∧ pt = .ty .int ∧ lf = blockLifetime) := by
  intro h
  refine LValTyping.rec
    (motive_1 := fun lv pt lf _ =>
      (lv = .var "p" ∧ pt = .ty (.box .int) ∧ lf = blockLifetime) ∨
      (lv = .deref (.var "p") ∧ pt = .ty .int ∧ lf = blockLifetime) ∨
      (lv = .var "r" ∧ pt = .ty (.borrow true [.deref (.var "p")]) ∧
        lf = blockLifetime) ∨
      (lv = .deref (.var "r") ∧ pt = .ty .int ∧ lf = blockLifetime))
    (motive_2 := fun targets pt lf _ =>
      targets = [.deref (.var "p")] → pt = .ty .int ∧ lf = blockLifetime)
    ?var ?box ?boxFull ?borrow ?singleton ?cons h
  case var =>
    intro x slot hslot
    by_cases hr : x = "r"
    · subst hr
      have hslotEq : blockBorrowSlot = slot := by
        simpa [blockBorrowEnv] using hslot
      cases hslotEq
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    · by_cases hp : x = "p"
      · subst hp
        have hslotEq : blockBoxIntSlot = slot := by
          simpa [blockBorrowEnv, blockBoxIntEnv, Env.update, hr] using hslot
        cases hslotEq
        exact Or.inl ⟨rfl, rfl, rfl⟩
      · simp [blockBorrowEnv, blockBoxIntEnv, Env.update, Env.empty, hr, hp]
          at hslot
  case box =>
    intro _lv _inner _lifetime _hsource ih
    rcases ih with hp | hpDeref | hr | hrDeref
    · rcases hp with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hpDeref with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hr with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hrDeref with ⟨_hlv, hty, _hlf⟩
      cases hty
  case boxFull =>
    intro _lv _inner _lifetime _hsource ih
    rcases ih with hp | hpDeref | hr | hrDeref
    · rcases hp with ⟨hlv, hty, hlf⟩
      cases hty
      subst hlv
      subst hlf
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · rcases hpDeref with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hr with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hrDeref with ⟨_hlv, hty, _hlf⟩
      cases hty
  case borrow =>
    intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hsource _htargets ihSource ihTargets
    rcases ihSource with hp | hpDeref | hr | hrDeref
    · rcases hp with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hpDeref with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hr with ⟨hlv, hty, hlf⟩
      cases hty
      subst hlv
      subst hlf
      rcases ihTargets rfl with ⟨hty, htargetLf⟩
      subst hty
      subst htargetLf
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
    · rcases hrDeref with ⟨_hlv, hty, _hlf⟩
      cases hty
  case singleton =>
    intro _target _ty _lifetime _htarget ihTarget htargetsEq
    cases htargetsEq
    rcases ihTarget with hp | hpDeref | hr | hrDeref
    · rcases hp with ⟨hlv, _hty, _hlf⟩
      cases hlv
    · rcases hpDeref with ⟨_hlv, hty, hlf⟩
      cases hty
      exact ⟨rfl, hlf⟩
    · rcases hr with ⟨hlv, _hty, _hlf⟩
      cases hlv
    · rcases hrDeref with ⟨hlv, _hty, _hlf⟩
      injection hlv with hinner
      injection hinner with hname
      contradiction
  case cons =>
    intro _target rest _headTy _headLifetime _restLifetime _lifetime _restTy
      _unionTy _hhead hrest _hunion _hintersection _ihHead _ihRest
      htargetsEq
    cases rest with
    | nil => cases hrest
    | cons _restHead _restTail => simp at htargetsEq

theorem blockBorrow_r_targets_typing :
    LValTargetsTyping blockBorrowEnv [.deref (.var "p")] (.ty .int)
      blockLifetime := by
  have hp : LValTyping blockBorrowEnv (.var "p") (.ty (.box .int))
      blockLifetime := by
    exact @LValTyping.var blockBorrowEnv "p" blockBoxIntSlot (by
      simp [blockBorrowEnv, blockBoxIntEnv, blockBoxIntSlot, blockBorrowSlot,
        Env.update])
  have hderef : LValTyping blockBorrowEnv (.deref (.var "p")) (.ty .int)
      blockLifetime := LValTyping.boxFull hp
  exact LValTargetsTyping.singleton hderef

theorem borrowDeclareCoherence :
    FreshUpdateCoherenceObligations blockBoxIntEnv "r"
      (.borrow true [.deref (.var "p")]) blockLifetime := by
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    have htyping' :
        LValTyping blockBorrowEnv lv (.ty (.borrow mutable targets))
          borrowLifetime := by
      simpa [blockBorrowEnv, blockBorrowSlot] using htyping
    rcases blockBorrow_lval_cases htyping' with hp | hpDeref | hr | hrDeref
    · rcases hp with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hpDeref with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hr with ⟨hlv, hty, _hlf⟩
      cases hty
      subst hlv
      exact False.elim (hbase rfl)
    · rcases hrDeref with ⟨_hlv, hty, _hlf⟩
      cases hty
  · intro lv mutable targets borrowLifetime _hbase htyping
    have htyping' :
        LValTyping blockBorrowEnv lv (.ty (.borrow mutable targets))
          borrowLifetime := by
      simpa [blockBorrowEnv, blockBorrowSlot] using htyping
    rcases blockBorrow_lval_cases htyping' with hp | hpDeref | hr | hrDeref
    · rcases hp with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hpDeref with ⟨_hlv, hty, _hlf⟩
      cases hty
    · rcases hr with ⟨_hlv, hty, _hlf⟩
      cases hty
      exact ⟨.int, blockLifetime, blockBorrow_r_targets_typing⟩
    · rcases hrDeref with ⟨_hlv, hty, _hlf⟩
      cases hty

theorem declareBorrow_typing :
    TermTyping blockBoxIntEnv StoreTyping.empty blockLifetime
      (.letMut "r" (.borrow true (.deref (.var "p")))) .unit
      blockBorrowEnv := by
  refine TermTyping.declare ?fresh borrowDeref_typing ?freshOut
    borrowDeclareCoherence ?env
  · simp [Env.fresh, blockBoxIntEnv, Env.update, Env.empty]
  · simp [Env.fresh, blockBoxIntEnv, Env.update, Env.empty]
  · rfl

theorem declaredBoxBorrowProgram_terms_typing :
    TermListTyping Env.empty StoreTyping.empty blockLifetime
      [ .letMut "p" (.box (.val (.int 0)))
      , .letMut "r" (.borrow true (.deref (.var "p")))
      ] .unit blockBorrowEnv := by
  exact TermListTyping.cons declareBox_typing
    (TermListTyping.singleton declareBorrow_typing)

theorem declaredBoxBorrowProgram_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root declaredBoxBorrowProgram
      .unit (blockBorrowEnv.dropLifetime blockLifetime) := by
  unfold declaredBoxBorrowProgram
  refine TermTyping.block ?child declaredBoxBorrowProgram_terms_typing
    WellFormedTy.unit rfl
  exact ⟨0, rfl⟩

end BoxDerefPending

end Paper
end LwRust
