import LwRust.Paper.Examples.TypeSafetyPass

/-!
End-to-end accepted example for the NLL-style loop rule `T-WhileJoin`
(`TermTyping.whileLoopJoin`).

The program is the loop

```
while *q == 0 { q = & y }
```

started from `x : int`, `y : int`, `q : & [x]`.  The body re-points `q` from
`x` to `y`, so the back-edge environment `q : & [y]` differs from the entry
environment `q : & [x]` and the strict rule `T-While` rejects the loop
(`whileJoinBackEnv_ne_entry` below witnesses the failed strict invariant).
`T-WhileJoin` accepts it against the join invariant `q : & [x, y]`, the least
upper bound of the entry and back-edge environments, exactly rustc's NLL
fixpoint state for this loop.  The condition reads through `q`, which forces
the condition derivation to type the dereference against the *widened* target
list — the part of the example that genuinely needs the invariant.

Why the borrow is immutable: the analogous mutable loop
`while *p == 1 { p = &mut y }` (rustc accepts it) is *not* typeable here.
From the invariant `p : &mut [x, y]`, the body's `&mut y` is `WriteProhibited`
— `y` is already a target of the loan recorded in `p`'s own slot, and this
calculus has no NLL-style loan-kill on overwrite that would let the borrow
checker disregard a loan about to die with the assignment.  `ReadProhibited`
only counts mutable loans, so the immutable retarget `q = & y` is typeable
from `q : & [x, y]`, which makes the immutable loop the canonical
target-list-widening example for `T-WhileJoin`.

A pleasant economy: the post-body environment is `q : & [y]` from *both* the
invariant-side derivation (premise 10) and the entry-side derivation
(premise 14, the rule-carried monotonicity obligation), so one parametric
body lemma (`whileJoinBody_typing`) discharges both, and likewise for the
condition.
-/

namespace LwRust
namespace Paper

open Core

/-- Slot for the integer variables `x` and `y`. -/
def whileJoinIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

/-- Slot for the immutable borrow `q`, parametric in the target list. -/
def whileJoinQSlot (targets : List LVal) : EnvSlot :=
  { ty := .ty (.borrow false targets), lifetime := Lifetime.root }

/-- The example environments all share `x : int`, `y : int` and differ only in
`q`'s target list. -/
def whileJoinEnv (targets : List LVal) : Env :=
  ((Env.empty.update "x" whileJoinIntSlot).update "y" whileJoinIntSlot).update
    "q" (whileJoinQSlot targets)

/-- Loop-entry environment: `q : & [x]`. -/
abbrev whileJoinEntryEnv : Env := whileJoinEnv [.var "x"]

/-- Back-edge environment (after `q = & y`): `q : & [y]`. -/
abbrev whileJoinBackEnv : Env := whileJoinEnv [.var "y"]

/-- Join invariant `whileJoinEntryEnv ⊔ whileJoinBackEnv`: `q : & [x, y]`. -/
abbrev whileJoinInvEnv : Env := whileJoinEnv [.var "x", .var "y"]

def whileJoinBodyLifetime : Lifetime := { path := [0] }

def whileJoinCondition : Term :=
  .eq (.copy (.deref (.var "q"))) (.val (.int 0))

def whileJoinBody : Term :=
  .assign (.var "q") (.borrow false (.var "y"))

def whileRetargetLoop : Term :=
  .whileLoop whileJoinBodyLifetime whileJoinCondition whileJoinBody

/-- A target list is *good* when it only mentions the integer variables. -/
def WhileJoinGoodTargets (targets : List LVal) : Prop :=
  ∀ t ∈ targets, t = LVal.var "x" ∨ t = LVal.var "y"

theorem whileJoinEntry_goodTargets : WhileJoinGoodTargets [.var "x"] := by
  intro t ht
  simp at ht
  exact Or.inl ht

theorem whileJoinBack_goodTargets : WhileJoinGoodTargets [.var "y"] := by
  intro t ht
  simp at ht
  exact Or.inr ht

theorem whileJoinInv_goodTargets :
    WhileJoinGoodTargets [.var "x", .var "y"] := by
  intro t ht
  simpa using ht

/-! ### Slot lookups -/

theorem whileJoinEnv_slotAt_x (targets : List LVal) :
    (whileJoinEnv targets).slotAt "x" = some whileJoinIntSlot := by
  simp [whileJoinEnv, Env.update]

theorem whileJoinEnv_slotAt_y (targets : List LVal) :
    (whileJoinEnv targets).slotAt "y" = some whileJoinIntSlot := by
  simp [whileJoinEnv, Env.update]

theorem whileJoinEnv_slotAt_q (targets : List LVal) :
    (whileJoinEnv targets).slotAt "q" = some (whileJoinQSlot targets) := by
  simp [whileJoinEnv, Env.update]

theorem whileJoinEnv_slotAt_none (targets : List LVal) {name : Name}
    (hq : name ≠ "q") (hy : name ≠ "y") (hx : name ≠ "x") :
    (whileJoinEnv targets).slotAt name = none := by
  simp [whileJoinEnv, Env.update, Env.empty, hq, hy, hx]

/-- Updating `q`'s slot moves between the example environments. -/
theorem whileJoinEnv_update_q (targets targets' : List LVal) :
    (whileJoinEnv targets).update "q" (whileJoinQSlot targets') =
      whileJoinEnv targets' := by
  apply env_ext_local
  intro name
  by_cases hq : name = "q" <;>
    simp [whileJoinEnv, Env.update, hq]

/-- The strict rule `T-While` cannot type the loop: the back edge does not
restore the entry environment. -/
theorem whileJoinBackEnv_ne_entry : whileJoinBackEnv ≠ whileJoinEntryEnv := by
  intro h
  have hq := congrArg (fun env => Env.slotAt env "q") h
  simp [whileJoinEnv, whileJoinQSlot, Env.update] at hq

/-! ### Lvalue typings -/

theorem whileJoin_x_typing (targets : List LVal) :
    LValTyping (whileJoinEnv targets) (.var "x") (.ty .int) Lifetime.root :=
  @LValTyping.var (whileJoinEnv targets) "x" whileJoinIntSlot
    (whileJoinEnv_slotAt_x targets)

theorem whileJoin_y_typing (targets : List LVal) :
    LValTyping (whileJoinEnv targets) (.var "y") (.ty .int) Lifetime.root :=
  @LValTyping.var (whileJoinEnv targets) "y" whileJoinIntSlot
    (whileJoinEnv_slotAt_y targets)

theorem whileJoin_q_typing (targets : List LVal) :
    LValTyping (whileJoinEnv targets) (.var "q")
      (.ty (.borrow false targets)) Lifetime.root :=
  @LValTyping.var (whileJoinEnv targets) "q" (whileJoinQSlot targets)
    (whileJoinEnv_slotAt_q targets)

theorem whileJoin_target_typing (targets : List LVal) {t : LVal}
    (ht : t = LVal.var "x" ∨ t = LVal.var "y") :
    LValTyping (whileJoinEnv targets) t (.ty .int) Lifetime.root := by
  rcases ht with rfl | rfl
  · exact whileJoin_x_typing targets
  · exact whileJoin_y_typing targets

/-- Every lvalue not based at `q` types as a plain integer variable. -/
theorem whileJoin_old_root_int (targets : List LVal) : ∀ {lv partialTy lifetime},
    LVal.base lv ≠ "q" →
    LValTyping (whileJoinEnv targets) lv partialTy lifetime →
    (lv = .var "x" ∨ lv = .var "y") ∧
      partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  intro lv
  induction lv with
  | var x =>
      intro partialTy lifetime hbase htyping
      cases htyping with
      | var hslot =>
          rename_i slot
          by_cases hx : x = "x"
          · subst hx
            have hslotEq : slot = whileJoinIntSlot :=
              Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_x targets))
            subst slot
            simp [whileJoinIntSlot]
          · by_cases hy : x = "y"
            · subst hy
              have hslotEq : slot = whileJoinIntSlot :=
                Option.some.inj
                  (hslot.symm.trans (whileJoinEnv_slotAt_y targets))
              subst slot
              simp [whileJoinIntSlot]
            · by_cases hq : x = "q"
              · subst hq
                simp [LVal.base] at hbase
              · have hnone : (whileJoinEnv targets).slotAt x = none :=
                  whileJoinEnv_slotAt_none targets hq hy hx
                rw [hslot] at hnone
                cases hnone
  | deref lv ih =>
      intro partialTy lifetime hbase htyping
      cases htyping with
      | box hinner =>
          rcases ih (by simpa [LVal.base] using hbase) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy
      | borrow hinner _htargets =>
          rcases ih (by simpa [LVal.base] using hbase) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy

/-- Good target lists (all based at the integer variables) never type as a
borrow. -/
theorem whileJoin_no_good_targets_borrow (targets : List LVal) {ts : List LVal}
    (hts : WhileJoinGoodTargets ts) {mutable : Bool} {bts : List LVal}
    {lifetime : Lifetime} :
    ¬ LValTargetsTyping (whileJoinEnv targets) ts
      (.ty (.borrow mutable bts)) lifetime := by
  intro htyping
  generalize hpartialTy :
      (PartialTy.ty (Ty.borrow mutable bts)) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases hts _ List.mem_cons_self with rfl | rfl
      all_goals
        rcases whileJoin_old_root_int targets (by simp [LVal.base]) htarget
          with ⟨_, htargetTy, _⟩
        rw [← hpartialTy] at htargetTy
        cases htargetTy
  | cons hhead hrest hunion _hlifetime =>
      rcases hts _ List.mem_cons_self with rfl | rfl
      all_goals
        rcases whileJoin_old_root_int targets (by simp [LVal.base]) hhead
          with ⟨_, hheadTy, _⟩
        injection hheadTy with hheadTy
        subst hheadTy
        have hupper : PartialTyStrengthens (.ty .int) partialTy :=
          hunion.1 (by simp)
        rw [← hpartialTy] at hupper
        cases PartialTyStrengthens.from_int_inv hupper

/-- Good target lists never type as a box either. -/
theorem whileJoin_no_good_targets_box (targets : List LVal) {ts : List LVal}
    (hts : WhileJoinGoodTargets ts) {inner : PartialTy} {lifetime : Lifetime} :
    ¬ LValTargetsTyping (whileJoinEnv targets) ts (.box inner) lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases hts _ List.mem_cons_self with rfl | rfl
      all_goals
        rcases whileJoin_old_root_int targets (by simp [LVal.base]) htarget
          with ⟨_, htargetTy, _⟩
        rw [← hpartialTy] at htargetTy
        cases htargetTy
  | cons hhead hrest hunion _hlifetime =>
      rcases hts _ List.mem_cons_self with rfl | rfl
      all_goals
        rcases whileJoin_old_root_int targets (by simp [LVal.base]) hhead
          with ⟨_, hheadTy, _⟩
        injection hheadTy with hheadTy
        subst hheadTy
        have hupper : PartialTyStrengthens (.ty .int) partialTy :=
          hunion.1 (by simp)
        rw [← hpartialTy] at hupper
        cases hupper

/-- Lvalues based at `q` are never boxes, and a borrow typing for them is
exactly `q`'s slot. -/
theorem whileJoin_q_root_facts (targets : List LVal)
    (hts : WhileJoinGoodTargets targets) : ∀ {lv},
    LVal.base lv = "q" →
    (∀ {inner lifetime},
      ¬ LValTyping (whileJoinEnv targets) lv (.box inner) lifetime) ∧
    (∀ {mutable bts lifetime},
      LValTyping (whileJoinEnv targets) lv
        (.ty (.borrow mutable bts)) lifetime →
      lv = .var "q" ∧ mutable = false ∧ bts = targets ∧
        lifetime = Lifetime.root) := by
  intro lv
  induction lv with
  | var x =>
      intro hbase
      constructor
      · intro inner lifetime htyping
        generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : x = "q" := by simpa [LVal.base] using hbase
            subst hx
            have hslotEq : slot = whileJoinQSlot targets :=
              Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_q targets))
            subst slot
            simp [whileJoinQSlot] at hpartialTy
      · intro mutable bts lifetime htyping
        generalize hpartialTy :
            (PartialTy.ty (Ty.borrow mutable bts)) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : x = "q" := by simpa [LVal.base] using hbase
            subst hx
            have hslotEq : slot = whileJoinQSlot targets :=
              Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_q targets))
            subst slot
            simp [whileJoinQSlot] at hpartialTy
            rcases hpartialTy with ⟨rfl, rfl⟩
            simp [whileJoinQSlot]
  | deref lv ih =>
      intro hbase
      have ihp := ih (by simpa [LVal.base] using hbase)
      constructor
      · intro inner lifetime htyping
        cases htyping with
        | box hinner =>
            exact ihp.1 hinner
        | borrow hinner htargets =>
            rcases ihp.2 hinner with ⟨rfl, rfl, rfl, rfl⟩
            exact whileJoin_no_good_targets_box _ hts htargets
      · intro mutable bts lifetime htyping
        cases htyping with
        | box hinner =>
            exact False.elim (ihp.1 hinner)
        | borrow hinner htargets =>
            rcases ihp.2 hinner with ⟨rfl, rfl, rfl, rfl⟩
            exact False.elim
              (whileJoin_no_good_targets_borrow _ hts htargets)

/-! ### Borrow-prohibition facts

The example environments contain no mutable borrows at all, which makes every
read-prohibition (and hence borrow safety) vacuous. -/

theorem whileJoin_no_mut (targets : List LVal) {z : Name} {bts : List LVal} :
    ¬ ((whileJoinEnv targets) ⊢ z ↝ (Ty.borrow true bts)) := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hq : z = "q"
  · subst hq
    have hslotEq : slot = whileJoinQSlot targets :=
      Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_q targets))
    subst slot
    simp only [whileJoinQSlot] at hcontainsTy
    cases hcontainsTy
  · by_cases hy : z = "y"
    · subst hy
      have hslotEq : slot = whileJoinIntSlot :=
        Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_y targets))
      subst slot
      simp only [whileJoinIntSlot] at hcontainsTy
      cases hcontainsTy
    · by_cases hx : z = "x"
      · subst hx
        have hslotEq : slot = whileJoinIntSlot :=
          Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_x targets))
        subst slot
        simp only [whileJoinIntSlot] at hcontainsTy
        cases hcontainsTy
      · have hnone : (whileJoinEnv targets).slotAt z = none :=
          whileJoinEnv_slotAt_none targets hq hy hx
        rw [hslot] at hnone
        cases hnone

theorem whileJoin_not_readProhibited (targets : List LVal) (lv : LVal) :
    ¬ ReadProhibited (whileJoinEnv targets) lv := by
  intro hread
  rcases hread with ⟨z, bts, target, hcontains, _htarget, _hconflict⟩
  exact whileJoin_no_mut targets hcontains

theorem whileJoin_borrowSafe (targets : List LVal) :
    BorrowSafeEnv (whileJoinEnv targets) := by
  intro z w mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable _hcontainsOther _htargetMutable _htargetOther _hconflict
  exact absurd hcontainsMutable (whileJoin_no_mut targets)

/-- The only immutable borrow contained anywhere is `q`'s slot. -/
theorem whileJoin_imm_contains (targets : List LVal) {z : Name}
    {bts : List LVal} :
    ((whileJoinEnv targets) ⊢ z ↝ (Ty.borrow false bts)) →
      z = "q" ∧ bts = targets := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hq : z = "q"
  · subst hq
    have hslotEq : slot = whileJoinQSlot targets :=
      Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_q targets))
    subst slot
    simp only [whileJoinQSlot] at hcontainsTy
    cases hcontainsTy with
    | here => exact ⟨rfl, rfl⟩
  · exfalso
    by_cases hy : z = "y"
    · subst hy
      have hslotEq : slot = whileJoinIntSlot :=
        Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_y targets))
      subst slot
      simp only [whileJoinIntSlot] at hcontainsTy
      cases hcontainsTy
    · by_cases hx : z = "x"
      · subst hx
        have hslotEq : slot = whileJoinIntSlot :=
          Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_x targets))
        subst slot
        simp only [whileJoinIntSlot] at hcontainsTy
        cases hcontainsTy
      · have hnone : (whileJoinEnv targets).slotAt z = none :=
          whileJoinEnv_slotAt_none targets hq hy hx
        rw [hslot] at hnone
        cases hnone

theorem whileJoin_not_writeProhibited_q (targets : List LVal)
    (hts : WhileJoinGoodTargets targets) :
    ¬ WriteProhibited (whileJoinEnv targets) (.var "q") := by
  intro hwrite
  rcases hwrite with hread | himm
  · exact whileJoin_not_readProhibited targets _ hread
  · rcases himm with ⟨z, bts, target, hcontains, htarget, hconflict⟩
    rcases whileJoin_imm_contains targets hcontains with ⟨rfl, rfl⟩
    rcases hts target htarget with rfl | rfl <;>
      simp [PathConflicts, LVal.base] at hconflict

/-! ### Well-formedness kit -/

theorem whileJoin_contained (targets : List LVal)
    (hts : WhileJoinGoodTargets targets) :
    ContainedBorrowsWellFormed (whileJoinEnv targets) := by
  intro root slot mutable bts hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hq : root = "q"
  · subst hq
    have hslotEq : slot = whileJoinQSlot targets :=
      Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_q targets))
    subst slot
    have hcontainedEq : containedSlot = whileJoinQSlot targets :=
      Option.some.inj
        (hcontainedSlot.symm.trans (whileJoinEnv_slotAt_q targets))
    subst containedSlot
    simp only [whileJoinQSlot] at hcontainsTy
    cases hcontainsTy with
    | here =>
        intro target htarget
        rcases hts target htarget with rfl | rfl
        · exact ⟨.int, Lifetime.root, whileJoin_x_typing targets,
            LifetimeOutlives.refl Lifetime.root,
            ⟨whileJoinIntSlot, by
              simpa [LVal.base] using whileJoinEnv_slotAt_x targets,
              LifetimeOutlives.refl Lifetime.root⟩⟩
        · exact ⟨.int, Lifetime.root, whileJoin_y_typing targets,
            LifetimeOutlives.refl Lifetime.root,
            ⟨whileJoinIntSlot, by
              simpa [LVal.base] using whileJoinEnv_slotAt_y targets,
              LifetimeOutlives.refl Lifetime.root⟩⟩
  · exfalso
    by_cases hy : root = "y"
    · subst hy
      have hcontainedEq : containedSlot = whileJoinIntSlot :=
        Option.some.inj
          (hcontainedSlot.symm.trans (whileJoinEnv_slotAt_y targets))
      subst containedSlot
      simp only [whileJoinIntSlot] at hcontainsTy
      cases hcontainsTy
    · by_cases hx : root = "x"
      · subst hx
        have hcontainedEq : containedSlot = whileJoinIntSlot :=
          Option.some.inj
            (hcontainedSlot.symm.trans (whileJoinEnv_slotAt_x targets))
        subst containedSlot
        simp only [whileJoinIntSlot] at hcontainsTy
        cases hcontainsTy
      · have hnone : (whileJoinEnv targets).slotAt root = none :=
          whileJoinEnv_slotAt_none targets hq hy hx
        rw [hcontainedSlot] at hnone
        cases hnone

theorem whileJoin_linearizedBy (targets : List LVal)
    (hts : WhileJoinGoodTargets targets) :
    LinearizedBy (fun name => if name = "q" then 1 else 0)
      (whileJoinEnv targets) := by
  intro root slot hslot v hv
  by_cases hq : root = "q"
  · subst hq
    have hslotEq : slot = whileJoinQSlot targets :=
      Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_q targets))
    subst slot
    simp only [whileJoinQSlot, PartialTy.vars, Ty.vars] at hv
    rcases List.mem_map.mp hv with ⟨t, ht, rfl⟩
    rcases hts t ht with rfl | rfl <;> simp [LVal.base]
  · by_cases hy : root = "y"
    · subst hy
      have hslotEq : slot = whileJoinIntSlot :=
        Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_y targets))
      subst slot
      simp [whileJoinIntSlot, PartialTy.vars, Ty.vars] at hv
    · by_cases hx : root = "x"
      · subst hx
        have hslotEq : slot = whileJoinIntSlot :=
          Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_x targets))
        subst slot
        simp [whileJoinIntSlot, PartialTy.vars, Ty.vars] at hv
      · have hnone : (whileJoinEnv targets).slotAt root = none :=
          whileJoinEnv_slotAt_none targets hq hy hx
        rw [hslot] at hnone
        cases hnone

theorem whileJoin_coherent (targets : List LVal)
    (hts : WhileJoinGoodTargets targets)
    (hjoint : ∃ ty lifetime,
      LValTargetsTyping (whileJoinEnv targets) targets (.ty ty) lifetime) :
    Coherent (whileJoinEnv targets) := by
  intro lv mutable bts borrowLifetime htyping
  by_cases hbase : LVal.base lv = "q"
  · rcases (whileJoin_q_root_facts targets hts hbase).2 htyping with
      ⟨rfl, rfl, rfl, rfl⟩
    exact hjoint
  · rcases whileJoin_old_root_int targets hbase htyping with ⟨_, hpartialTy, _⟩
    cases hpartialTy

theorem whileJoinInv_targets_typing :
    LValTargetsTyping whileJoinInvEnv [.var "x", .var "y"] (.ty .int)
      Lifetime.root :=
  LValTargetsTyping.cons (whileJoin_x_typing _)
    (LValTargetsTyping.singleton (whileJoin_y_typing _))
    (PartialTyUnion.self (.ty .int))
    (LifetimeIntersection.self Lifetime.root)

theorem whileJoin_borrow_y_wellFormed (targets : List LVal) :
    WellFormedTy (whileJoinEnv targets) (.borrow false [.var "y"])
      Lifetime.root := by
  exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
    intro target htarget
    simp at htarget
    subst htarget
    exact ⟨.int, Lifetime.root, whileJoin_y_typing targets,
      LifetimeOutlives.refl Lifetime.root,
      ⟨whileJoinIntSlot, by
        simpa [LVal.base] using whileJoinEnv_slotAt_y targets,
        LifetimeOutlives.refl Lifetime.root⟩⟩))

theorem whileJoin_shape (targets : List LVal)
    (hts : WhileJoinGoodTargets targets) :
    ShapeCompatible (whileJoinEnv targets)
      (.ty (.borrow false targets)) (.ty (.borrow false [.var "y"])) := by
  refine ShapeCompatible.borrow ?left ?right ShapeCompatible.int
  · intro target htarget
    exact ⟨Lifetime.root, whileJoin_target_typing targets (hts target htarget)⟩
  · intro target htarget
    simp at htarget
    subst htarget
    exact ⟨Lifetime.root, whileJoin_y_typing targets⟩

/-! ### The body's environment write -/

theorem whileJoin_retarget_write (targets : List LVal) :
    EnvWrite 0 (whileJoinEnv targets) (.var "q") (.borrow false [.var "y"])
      whileJoinBackEnv := by
  have hwrite := @EnvWrite.intro 0 (whileJoinEnv targets) (whileJoinEnv targets)
    (.var "q") (whileJoinQSlot targets) (.borrow false [.var "y"])
    (.ty (.borrow false [.var "y"]))
    (whileJoinEnv_slotAt_q targets) UpdateAtPath.strong
  have hslotEq :
      ({ whileJoinQSlot targets with ty := .ty (.borrow false [.var "y"]) }
        : EnvSlot) = whileJoinQSlot [.var "y"] := by
    simp [whileJoinQSlot]
  simp only [LVal.base] at hwrite
  rw [hslotEq, whileJoinEnv_update_q] at hwrite
  exact hwrite

theorem whileJoin_retarget_below :
    EnvWriteRhsBorrowTargetsBelow (fun name => if name = "q" then 1 else 0)
      whileJoinBackEnv (.borrow false [.var "y"]) := by
  constructor
  · intro root slot mutable bts target hslot hcontains htarget _hrhs
    by_cases hq : root = "q"
    · subst hq
      have hslotEq : slot = whileJoinQSlot [.var "y"] :=
        Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_q [.var "y"]))
      subst slot
      simp only [whileJoinQSlot] at hcontains
      cases hcontains with
      | here =>
          simp at htarget
          subst htarget
          simp [LVal.base]
    · by_cases hy : root = "y"
      · subst hy
        have hslotEq : slot = whileJoinIntSlot :=
          Option.some.inj (hslot.symm.trans (whileJoinEnv_slotAt_y [.var "y"]))
        subst slot
        simp only [whileJoinIntSlot] at hcontains
        cases hcontains
      · by_cases hx : root = "x"
        · subst hx
          have hslotEq : slot = whileJoinIntSlot :=
            Option.some.inj
              (hslot.symm.trans (whileJoinEnv_slotAt_x [.var "y"]))
          subst slot
          simp only [whileJoinIntSlot] at hcontains
          cases hcontains
        · have hnone : whileJoinBackEnv.slotAt root = none :=
            whileJoinEnv_slotAt_none [.var "y"] hq hy hx
          rw [hslot] at hnone
          cases hnone
  · intro root other mutable targetsMutable targetsOther targetMutable
      targetOther hcontainsMutable _hcontainsOther _htargetMutable
      _htargetOther _hconflict _hrhsMutable _hrhsOther
    exact absurd hcontainsMutable (whileJoin_no_mut [.var "y"])

theorem whileJoin_writeCoherence (targets : List LVal) :
    EnvWriteCoherenceObligations (whileJoinEnv targets) whileJoinBackEnv
      "q" := by
  constructor
  · intro lv mutable bts borrowLifetime hbase htyping
    rcases whileJoin_old_root_int [.var "y"] hbase htyping with
      ⟨_, hpartialTy, _⟩
    cases hpartialTy
  · intro lv mutable bts borrowLifetime hbase htyping
    rcases (whileJoin_q_root_facts [.var "y"] whileJoinBack_goodTargets
        hbase).2 htyping with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨.int, Lifetime.root,
      LValTargetsTyping.singleton (whileJoin_y_typing [.var "y"])⟩

/-! ### Loop-rule side conditions -/

theorem whileJoin_lifetimeChild :
    LifetimeChild Lifetime.root whileJoinBodyLifetime :=
  ⟨0, rfl⟩

theorem whileJoinBack_dropLifetime :
    whileJoinBackEnv.dropLifetime whileJoinBodyLifetime = whileJoinBackEnv := by
  apply env_ext_local
  intro name
  by_cases hq : name = "q" <;> by_cases hy : name = "y" <;>
    by_cases hx : name = "x" <;>
    simp [whileJoinEnv, whileJoinQSlot, whileJoinIntSlot, Env.dropLifetime,
      Env.update, Env.empty, Lifetime.root, whileJoinBodyLifetime,
      hq, hy, hx]

/-! ### The environment join -/

theorem whileJoinEntry_le_inv :
    EnvStrengthens whileJoinEntryEnv whileJoinInvEnv := by
  intro name
  by_cases hq : name = "q"
  · subst hq
    rw [whileJoinEnv_slotAt_q, whileJoinEnv_slotAt_q]
    refine ⟨rfl, PartialTyStrengthens.borrow ?_⟩
    intro target htarget
    simp at htarget
    subst htarget
    simp
  · by_cases hy : name = "y"
    · subst hy
      rw [whileJoinEnv_slotAt_y, whileJoinEnv_slotAt_y]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hx : name = "x"
      · subst hx
        rw [whileJoinEnv_slotAt_x, whileJoinEnv_slotAt_x]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · rw [whileJoinEnv_slotAt_none [.var "x"] hq hy hx,
          whileJoinEnv_slotAt_none [.var "x", .var "y"] hq hy hx]
        trivial

theorem whileJoinBack_le_inv :
    EnvStrengthens whileJoinBackEnv whileJoinInvEnv := by
  intro name
  by_cases hq : name = "q"
  · subst hq
    rw [whileJoinEnv_slotAt_q, whileJoinEnv_slotAt_q]
    refine ⟨rfl, PartialTyStrengthens.borrow ?_⟩
    intro target htarget
    simp at htarget
    subst htarget
    simp
  · by_cases hy : name = "y"
    · subst hy
      rw [whileJoinEnv_slotAt_y, whileJoinEnv_slotAt_y]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hx : name = "x"
      · subst hx
        rw [whileJoinEnv_slotAt_x, whileJoinEnv_slotAt_x]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · rw [whileJoinEnv_slotAt_none [.var "y"] hq hy hx,
          whileJoinEnv_slotAt_none [.var "x", .var "y"] hq hy hx]
        trivial

theorem whileJoinInv_least {env' : Env}
    (hentry : EnvStrengthens whileJoinEntryEnv env')
    (hback : EnvStrengthens whileJoinBackEnv env') :
    EnvStrengthens whileJoinInvEnv env' := by
  intro name
  by_cases hq : name = "q"
  · subst hq
    rcases EnvStrengthens.slot_forward hentry
        (whileJoinEnv_slotAt_q [.var "x"]) with ⟨slotX, hslotX, hlife, hstrX⟩
    rcases EnvStrengthens.slot_forward hback
        (whileJoinEnv_slotAt_q [.var "y"]) with ⟨slotY, hslotY, _hlifeY, hstrY⟩
    have hslotEq : slotX = slotY :=
      Option.some.inj (hslotX.symm.trans hslotY)
    subst hslotEq
    rw [whileJoinEnv_slotAt_q, hslotX]
    have hX : PartialTyStrengthens (.ty (.borrow false [.var "x"]))
        slotX.ty := hstrX
    have hY : PartialTyStrengthens (.ty (.borrow false [.var "y"]))
        slotX.ty := hstrY
    have hXY := partialTyStrengthens_borrow_append hX hY
    exact ⟨hlife, by simpa [whileJoinQSlot] using hXY⟩
  · by_cases hy : name = "y"
    · subst hy
      rcases EnvStrengthens.slot_forward hentry
          (whileJoinEnv_slotAt_y [.var "x"]) with ⟨slot', hslot', hlife, hstr⟩
      rw [whileJoinEnv_slotAt_y, hslot']
      exact ⟨hlife, hstr⟩
    · by_cases hx : name = "x"
      · subst hx
        rcases EnvStrengthens.slot_forward hentry
            (whileJoinEnv_slotAt_x [.var "x"]) with ⟨slot', hslot', hlife, hstr⟩
        rw [whileJoinEnv_slotAt_x, hslot']
        exact ⟨hlife, hstr⟩
      · have hentryNone : whileJoinEntryEnv.slotAt name = none :=
          whileJoinEnv_slotAt_none [.var "x"] hq hy hx
        have hinvNone : whileJoinInvEnv.slotAt name = none :=
          whileJoinEnv_slotAt_none [.var "x", .var "y"] hq hy hx
        have h := hentry name
        rw [hentryNone] at h
        rw [hinvNone]
        cases henvSlot : env'.slotAt name with
        | none =>
            trivial
        | some envSlot =>
            rw [henvSlot] at h
            cases h

theorem whileJoin_envJoin :
    EnvJoin whileJoinEntryEnv whileJoinBackEnv whileJoinInvEnv := by
  constructor
  · intro env henv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at henv
    rcases henv with rfl | rfl
    · exact whileJoinEntry_le_inv
    · exact whileJoinBack_le_inv
  · intro env' henv'
    exact whileJoinInv_least (henv' (by simp)) (henv' (by simp))

theorem whileJoinEntry_join_sameShape :
    EnvJoinSameShape whileJoinEntryEnv whileJoinInvEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  by_cases hq : name = "q"
  · subst hq
    have hbranchEq : branchSlot = whileJoinQSlot [.var "x"] :=
      Option.some.inj (hbranch.symm.trans (whileJoinEnv_slotAt_q _))
    have hjoinEq : joinSlot = whileJoinQSlot [.var "x", .var "y"] :=
      Option.some.inj (hjoin.symm.trans (whileJoinEnv_slotAt_q _))
    subst branchSlot
    subst joinSlot
    simp [whileJoinQSlot, PartialTy.sameShape, Ty.sameShape]
  · by_cases hy : name = "y"
    · subst hy
      have hbranchEq : branchSlot = whileJoinIntSlot :=
        Option.some.inj (hbranch.symm.trans (whileJoinEnv_slotAt_y _))
      have hjoinEq : joinSlot = whileJoinIntSlot :=
        Option.some.inj (hjoin.symm.trans (whileJoinEnv_slotAt_y _))
      subst branchSlot
      subst joinSlot
      simp [whileJoinIntSlot, PartialTy.sameShape, Ty.sameShape]
    · by_cases hx : name = "x"
      · subst hx
        have hbranchEq : branchSlot = whileJoinIntSlot :=
          Option.some.inj (hbranch.symm.trans (whileJoinEnv_slotAt_x _))
        have hjoinEq : joinSlot = whileJoinIntSlot :=
          Option.some.inj (hjoin.symm.trans (whileJoinEnv_slotAt_x _))
        subst branchSlot
        subst joinSlot
        simp [whileJoinIntSlot, PartialTy.sameShape, Ty.sameShape]
      · have hnone : whileJoinEntryEnv.slotAt name = none :=
          whileJoinEnv_slotAt_none [.var "x"] hq hy hx
        rw [hbranch] at hnone
        cases hnone

theorem whileJoinBack_join_sameShape :
    EnvJoinSameShape whileJoinBackEnv whileJoinInvEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  by_cases hq : name = "q"
  · subst hq
    have hbranchEq : branchSlot = whileJoinQSlot [.var "y"] :=
      Option.some.inj (hbranch.symm.trans (whileJoinEnv_slotAt_q _))
    have hjoinEq : joinSlot = whileJoinQSlot [.var "x", .var "y"] :=
      Option.some.inj (hjoin.symm.trans (whileJoinEnv_slotAt_q _))
    subst branchSlot
    subst joinSlot
    simp [whileJoinQSlot, PartialTy.sameShape, Ty.sameShape]
  · by_cases hy : name = "y"
    · subst hy
      have hbranchEq : branchSlot = whileJoinIntSlot :=
        Option.some.inj (hbranch.symm.trans (whileJoinEnv_slotAt_y _))
      have hjoinEq : joinSlot = whileJoinIntSlot :=
        Option.some.inj (hjoin.symm.trans (whileJoinEnv_slotAt_y _))
      subst branchSlot
      subst joinSlot
      simp [whileJoinIntSlot, PartialTy.sameShape, Ty.sameShape]
    · by_cases hx : name = "x"
      · subst hx
        have hbranchEq : branchSlot = whileJoinIntSlot :=
          Option.some.inj (hbranch.symm.trans (whileJoinEnv_slotAt_x _))
        have hjoinEq : joinSlot = whileJoinIntSlot :=
          Option.some.inj (hjoin.symm.trans (whileJoinEnv_slotAt_x _))
        subst branchSlot
        subst joinSlot
        simp [whileJoinIntSlot, PartialTy.sameShape, Ty.sameShape]
      · have hnone : whileJoinBackEnv.slotAt name = none :=
          whileJoinEnv_slotAt_none [.var "y"] hq hy hx
        rw [hbranch] at hnone
        cases hnone

/-! ### Condition and body typings

Both are parametric in `q`'s target list, so each serves double duty: once
from the invariant environment (the loop's main premises) and once from the
entry environment (the rule-carried monotonicity premises). -/

theorem whileJoinCondition_typing (targets : List LVal)
    (hderef : LValTyping (whileJoinEnv targets) (.deref (.var "q"))
      (.ty .int) Lifetime.root) :
    TermTyping (whileJoinEnv targets) StoreTyping.empty Lifetime.root
      whileJoinCondition .bool (whileJoinEnv targets) := by
  unfold whileJoinCondition
  exact TermTyping.eq (ghost := "γ")
    (TermTyping.copy hderef CopyTy.int
      (whileJoin_not_readProhibited targets _))
    (by simp [Env.fresh, whileJoinEnv, Env.update, Env.empty])
    (TermTyping.const ValueTyping.int)
    (TermTyping.const ValueTyping.int)
    CopyTy.int
    CopyTy.int
    ShapeCompatible.int

theorem whileJoinInv_deref_q_typing :
    LValTyping whileJoinInvEnv (.deref (.var "q")) (.ty .int) Lifetime.root :=
  LValTyping.borrow (whileJoin_q_typing _) whileJoinInv_targets_typing

theorem whileJoinEntry_deref_q_typing :
    LValTyping whileJoinEntryEnv (.deref (.var "q")) (.ty .int)
      Lifetime.root :=
  LValTyping.borrow (whileJoin_q_typing _)
    (LValTargetsTyping.singleton (whileJoin_x_typing _))

theorem whileJoinBody_typing (targets : List LVal)
    (hts : WhileJoinGoodTargets targets) :
    TermTyping (whileJoinEnv targets) StoreTyping.empty whileJoinBodyLifetime
      whileJoinBody .unit whileJoinBackEnv := by
  unfold whileJoinBody
  exact TermTyping.assign
    (whileJoin_q_typing targets)
    (TermTyping.immBorrow (whileJoin_y_typing targets)
      (whileJoin_not_readProhibited targets _))
    (whileJoin_borrowSafe targets)
    (whileJoin_q_typing targets)
    (whileJoin_shape targets hts)
    (whileJoin_borrow_y_wellFormed targets)
    (whileJoin_retarget_write targets)
    ⟨fun name => if name = "q" then 1 else 0,
      whileJoin_linearizedBy targets hts, whileJoin_retarget_below⟩
    (whileJoin_writeCoherence targets)
    (whileJoin_contained [.var "y"] whileJoinBack_goodTargets)
    (whileJoin_not_writeProhibited_q [.var "y"] whileJoinBack_goodTargets)

/-! ### The loop typing -/

theorem whileRetargetLoop_typing :
    TermTyping whileJoinEntryEnv StoreTyping.empty Lifetime.root
      whileRetargetLoop .unit whileJoinInvEnv := by
  unfold whileRetargetLoop
  exact TermTyping.whileLoopJoin
    whileJoin_lifetimeChild
    whileJoin_envJoin
    whileJoinEntry_join_sameShape
    whileJoinBack_join_sameShape
    (whileJoin_contained [.var "x", .var "y"] whileJoinInv_goodTargets)
    (whileJoin_coherent [.var "x", .var "y"] whileJoinInv_goodTargets
      ⟨.int, Lifetime.root, whileJoinInv_targets_typing⟩)
    ⟨fun name => if name = "q" then 1 else 0,
      whileJoin_linearizedBy [.var "x", .var "y"] whileJoinInv_goodTargets⟩
    (whileJoin_borrowSafe [.var "x", .var "y"])
    (whileJoinCondition_typing [.var "x", .var "y"] whileJoinInv_deref_q_typing)
    (whileJoinBody_typing [.var "x", .var "y"] whileJoinInv_goodTargets)
    WellFormedTy.unit
    whileJoinBack_dropLifetime
    (whileJoinCondition_typing [.var "x"] whileJoinEntry_deref_q_typing)
    (whileJoinBody_typing [.var "x"] whileJoinEntry_goodTargets)

end Paper
end LwRust
