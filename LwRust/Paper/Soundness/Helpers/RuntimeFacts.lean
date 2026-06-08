import LwRust.Paper.Soundness.Helpers.Eqv

/-!
# Soundness helpers: RuntimeFacts

Runtime-invariant preservation facts (Linearizable / Coherent packaging).
-/

namespace LwRust
namespace Paper

open Core

/-! ### Runtime-invariant preservation facts

These package the two runtime invariants (`Linearizable`, `Coherent`) that
`lvalTyping_strengthen_transport` consumes, as preserved by the two state
operations that the Appendix 9.6 borrow-invariance argument performs: a single
`EnvWrite` and an `EnvJoin` (the write fan-out's branch merge).

`Linearizable` preservation is the `lw_rust_followup` contribution (Definition
11 plus its preservation proposition): a common rank function survives a write
under the rule-carried RHS-rank side condition, and survives branch joins when
both branches use the same rank function.

`Coherent` preservation is Section-4 content proved from explicit
root-transport/coherence side conditions carried by the strengthened write and
declaration rules. -/

/-- A tiny environment witnessing why bare rank-0 write linearization is false. -/
def writeLinearizationCycleEnv : Env :=
  (Env.empty.update "x" { ty := .ty .int, lifetime := Lifetime.root }).update "y"
    { ty := .ty (.borrow false [.var "x"]), lifetime := Lifetime.root }

/-- The result of writing `&y` into `x` in `writeLinearizationCycleEnv`. -/
def writeLinearizationCycleResult : Env :=
  writeLinearizationCycleEnv.update "x"
    { ty := .ty (.borrow false [.var "y"]), lifetime := Lifetime.root }

/-- Bare `EnvWrite` does not preserve linearizability.

The source has only the edge `y → x`, so it is linearizable.  The rank-0 strong
write `x := &y` adds the edge `x → y`, producing the cycle `x ↔ y`.  This is the
mechanized reason the valid preservation theorem below carries an explicit
RHS-rank/acyclicity side condition. -/
theorem EnvWrite.linearizable_bare_counterexample :
    ∃ env result lv rhsTy,
      EnvWrite 0 env lv rhsTy result ∧ Linearizable env ∧ ¬ Linearizable result := by
  refine ⟨writeLinearizationCycleEnv, writeLinearizationCycleResult, .var "x",
    .borrow false [.var "y"], ?_, ?_, ?_⟩
  · have hx :
        writeLinearizationCycleEnv.slotAt "x" =
          some { ty := .ty .int, lifetime := Lifetime.root } := by
      simp [writeLinearizationCycleEnv, Env.update]
    simpa [writeLinearizationCycleResult, LVal.base] using
      EnvWrite.intro (lv := .var "x")
        (slot := { ty := .ty .int, lifetime := Lifetime.root }) hx (UpdateAtPath.strong
        (env := writeLinearizationCycleEnv)
        (old := .ty .int)
        (ty := .borrow false [.var "y"]))
  · refine ⟨fun n => if n = "x" then 1 else if n = "y" then 2 else 0, ?_⟩
    intro z slot hslot v hv
    by_cases hy : z = "y"
    · subst hy
      have hslotEq :
          slot = { ty := .ty (.borrow false [.var "x"]), lifetime := Lifetime.root } := by
        have h :
            { ty := .ty (.borrow false [.var "x"]), lifetime := Lifetime.root } = slot := by
          simpa [writeLinearizationCycleEnv, Env.update] using hslot
        exact h.symm
      subst hslotEq
      simp [PartialTy.vars, Ty.vars, LVal.base] at hv
      subst hv
      simp
    · by_cases hx : z = "x"
      · subst hx
        have hslotEq :
            slot = { ty := .ty .int, lifetime := Lifetime.root } := by
          have h : { ty := .ty .int, lifetime := Lifetime.root } = slot := by
            simpa [writeLinearizationCycleEnv, Env.update] using hslot
          exact h.symm
        subst hslotEq
        simp [PartialTy.vars, Ty.vars] at hv
      · have hnone : writeLinearizationCycleEnv.slotAt z = none := by
          simp [writeLinearizationCycleEnv, Env.update, Env.empty, hx, hy]
        rw [hslot] at hnone
        cases hnone
  · intro hlin
    rcases hlin with ⟨φ, hφ⟩
    have hxSlot :
        writeLinearizationCycleResult.slotAt "x" =
          some { ty := .ty (.borrow false [.var "y"]), lifetime := Lifetime.root } := by
      simp [writeLinearizationCycleResult, Env.update]
    have hySlot :
        writeLinearizationCycleResult.slotAt "y" =
          some { ty := .ty (.borrow false [.var "x"]), lifetime := Lifetime.root } := by
      simp [writeLinearizationCycleResult, writeLinearizationCycleEnv, Env.update]
    have hy_lt_x : φ "y" < φ "x" :=
      hφ "x" { ty := .ty (.borrow false [.var "y"]), lifetime := Lifetime.root }
        hxSlot "y" (by simp [PartialTy.vars, Ty.vars, LVal.base])
    have hx_lt_y : φ "x" < φ "y" :=
      hφ "y" { ty := .ty (.borrow false [.var "x"]), lifetime := Lifetime.root }
        hySlot "x" (by simp [PartialTy.vars, Ty.vars, LVal.base])
    omega

/-- Source environment for the bare write-coherence counterexample. -/
def writeCoherenceEmptyBorrowEnv : Env :=
  Env.empty.update "x" { ty := .ty .int, lifetime := Lifetime.root }

/-- Result of writing `&[]` into `x`. -/
def writeCoherenceEmptyBorrowResult : Env :=
  writeCoherenceEmptyBorrowEnv.update "x"
    { ty := .ty (.borrow false []), lifetime := Lifetime.root }

theorem writeCoherenceEmptyBorrowEnv_lvalTyping_int
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTyping writeCoherenceEmptyBorrowEnv lv partialTy lifetime →
    partialTy = .ty .int := by
  induction lv generalizing partialTy lifetime with
  | var y =>
      intro htyping
      cases htyping with
      | var hslot =>
          by_cases hy : y = ("x" : Name)
          · subst hy
            simpa [writeCoherenceEmptyBorrowEnv, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          · have hnone : writeCoherenceEmptyBorrowEnv.slotAt y = none := by
              simp [writeCoherenceEmptyBorrowEnv, Env.update, Env.empty, hy]
            rw [hslot] at hnone
            cases hnone
  | deref source ih =>
      intro htyping
      cases htyping with
      | box hbox =>
          have hcontra := ih hbox
          cases hcontra
      | borrow hborrow _htargets =>
          have hcontra := ih hborrow
          cases hcontra

theorem writeCoherenceEmptyBorrowEnv_coherent :
    Coherent writeCoherenceEmptyBorrowEnv := by
  intro lv mutable targets borrowLifetime htyping
  have hty := writeCoherenceEmptyBorrowEnv_lvalTyping_int htyping
  cases hty

theorem writeCoherenceEmptyBorrowResult_not_coherent :
    ¬ Coherent writeCoherenceEmptyBorrowResult := by
  intro hcoh
  have hx :
      writeCoherenceEmptyBorrowResult.slotAt "x" =
        some { ty := .ty (.borrow false []), lifetime := Lifetime.root } := by
    simp [writeCoherenceEmptyBorrowResult, Env.update]
  have htyping :
      LValTyping writeCoherenceEmptyBorrowResult (.var "x")
        (.ty (.borrow false [])) Lifetime.root :=
    LValTyping.var hx
  rcases hcoh (.var "x") false [] Lifetime.root htyping with
    ⟨targetTy, targetLifetime, htargets⟩
  exact LValTargetsTyping.nil_false htargets

/-- Bare `EnvWrite.preserves_coherent` is false with only per-target RHS
well-formedness: writing the empty borrow `&[]` satisfies the per-target premise
vacuously, but the result is not coherent because target-list typing is
non-empty. -/
theorem EnvWrite.preserves_coherent_bare_counterexample :
    ∃ env result lv rhsTy slotLifetime,
      EnvWrite 0 env lv rhsTy result ∧
      Linearizable env ∧ Linearizable result ∧ Coherent env ∧
      PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) ∧
      ¬ Coherent result := by
  refine ⟨writeCoherenceEmptyBorrowEnv, writeCoherenceEmptyBorrowResult,
    .var "x", .borrow false [], Lifetime.root, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hx :
        writeCoherenceEmptyBorrowEnv.slotAt "x" =
          some { ty := .ty .int, lifetime := Lifetime.root } := by
      simp [writeCoherenceEmptyBorrowEnv, Env.update]
    simpa [writeCoherenceEmptyBorrowResult, LVal.base] using
      EnvWrite.intro (lv := .var "x")
        (slot := { ty := .ty .int, lifetime := Lifetime.root }) hx
        (UpdateAtPath.strong
          (env := writeCoherenceEmptyBorrowEnv)
          (old := .ty .int)
          (ty := .borrow false []))
  · refine ⟨fun _ => 0, ?_⟩
    intro y slot hslot v hv
    by_cases hy : y = ("x" : Name)
    · subst hy
      have hslotEq :
          slot = { ty := .ty .int, lifetime := Lifetime.root } := by
        simpa [writeCoherenceEmptyBorrowEnv, Env.update] using hslot.symm
      rw [hslotEq] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · have hnone : writeCoherenceEmptyBorrowEnv.slotAt y = none := by
        simp [writeCoherenceEmptyBorrowEnv, Env.update, Env.empty, hy]
      rw [hslot] at hnone
      cases hnone
  · refine ⟨fun _ => 0, ?_⟩
    intro y slot hslot v hv
    by_cases hy : y = ("x" : Name)
    · subst hy
      have hslotTy : slot.ty = .ty (.borrow false []) := by
        simpa [writeCoherenceEmptyBorrowResult, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · have hnone : writeCoherenceEmptyBorrowResult.slotAt y = none := by
        simp [writeCoherenceEmptyBorrowResult, writeCoherenceEmptyBorrowEnv,
          Env.update, Env.empty, hy]
      rw [hslot] at hnone
      cases hnone
  · exact writeCoherenceEmptyBorrowEnv_coherent
  · intro mutable targets hcontains target htarget
    cases hcontains
    simp at htarget
  · exact writeCoherenceEmptyBorrowResult_not_coherent

/-- No full union type exists for `int ⊔ unit`. -/
theorem PartialTyUnion.int_unit_full_false {ty : Ty} :
    ¬ PartialTyUnion (.ty .int) (.ty .unit) (.ty ty) := by
  intro hunion
  have htyUnit : ty = .unit :=
    PartialTyStrengthens.from_unit_inv (PartialTyUnion.right_strengthens hunion)
  subst htyUnit
  have hintUnit : PartialTyStrengthens (.ty .int) (.ty .unit) :=
    PartialTyUnion.left_strengthens hunion
  cases hintUnit

/-- Left branch for the bare join-coherence counterexample. -/
def joinCoherenceLeftEnv : Env :=
  ((Env.empty.update "a" { ty := .ty .int, lifetime := Lifetime.root }).update "b"
    { ty := .ty .unit, lifetime := Lifetime.root }).update "x"
      { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root }

/-- Right branch for the bare join-coherence counterexample. -/
def joinCoherenceRightEnv : Env :=
  ((Env.empty.update "a" { ty := .ty .int, lifetime := Lifetime.root }).update "b"
    { ty := .ty .unit, lifetime := Lifetime.root }).update "x"
      { ty := .ty (.borrow false [.var "b"]), lifetime := Lifetime.root }

/-- Join result: the branch borrows merge to `&[a,b]`. -/
def joinCoherenceJoinEnv : Env :=
  ((Env.empty.update "a" { ty := .ty .int, lifetime := Lifetime.root }).update "b"
    { ty := .ty .unit, lifetime := Lifetime.root }).update "x"
      { ty := .ty (.borrow false [.var "a", .var "b"]), lifetime := Lifetime.root }

theorem joinCoherenceLeftEnv_lvalTyping_shape {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    LValTyping joinCoherenceLeftEnv lv partialTy lifetime →
    partialTy = .ty .int ∨ partialTy = .ty .unit ∨
      partialTy = .ty (.borrow false [.var "a"]) := by
  induction lv generalizing partialTy lifetime with
  | var y =>
      intro htyping
      cases htyping with
      | var hslot =>
          by_cases hyx : y = "x"
          · subst hyx
            right; right
            simpa [joinCoherenceLeftEnv, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          · by_cases hyb : y = "b"
            · subst hyb
              right; left
              simpa [joinCoherenceLeftEnv, Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
            · by_cases hya : y = "a"
              · subst hya
                left
                simpa [joinCoherenceLeftEnv, Env.update] using
                  (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
              · have hnone : joinCoherenceLeftEnv.slotAt y = none := by
                  simp [joinCoherenceLeftEnv, Env.update, Env.empty, hyx, hyb, hya]
                rw [hslot] at hnone
                cases hnone
  | deref source ih =>
      intro htyping
      cases htyping with
      | box hsource =>
          rcases ih hsource with h | h | h <;> cases h
      | borrow hsource htargets =>
          rcases ih hsource with h | h | h
          · cases h
          · cases h
          · cases h
            cases htargets with
            | singleton htarget =>
                rcases LValTyping.var_inv htarget with ⟨slot, hslot, hty, _hlife⟩
                have hslotTy : slot.ty = .ty .int := by
                  simpa [joinCoherenceLeftEnv, Env.update] using
                    (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
                left
                exact hty.symm.trans hslotTy
            | cons _hhead hrest _hunion _hintersection =>
                exact False.elim (LValTargetsTyping.nil_false hrest)

theorem joinCoherenceRightEnv_lvalTyping_shape {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    LValTyping joinCoherenceRightEnv lv partialTy lifetime →
    partialTy = .ty .int ∨ partialTy = .ty .unit ∨
      partialTy = .ty (.borrow false [.var "b"]) := by
  induction lv generalizing partialTy lifetime with
  | var y =>
      intro htyping
      cases htyping with
      | var hslot =>
          by_cases hyx : y = "x"
          · subst hyx
            right; right
            simpa [joinCoherenceRightEnv, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          · by_cases hyb : y = "b"
            · subst hyb
              right; left
              simpa [joinCoherenceRightEnv, Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
            · by_cases hya : y = "a"
              · subst hya
                left
                simpa [joinCoherenceRightEnv, Env.update] using
                  (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
              · have hnone : joinCoherenceRightEnv.slotAt y = none := by
                  simp [joinCoherenceRightEnv, Env.update, Env.empty, hyx, hyb, hya]
                rw [hslot] at hnone
                cases hnone
  | deref source ih =>
      intro htyping
      cases htyping with
      | box hsource =>
          rcases ih hsource with h | h | h <;> cases h
      | borrow hsource htargets =>
          rcases ih hsource with h | h | h
          · cases h
          · cases h
          · cases h
            cases htargets with
            | singleton htarget =>
                rcases LValTyping.var_inv htarget with ⟨slot, hslot, hty, _hlife⟩
                have hslotTy : slot.ty = .ty .unit := by
                  simpa [joinCoherenceRightEnv, Env.update] using
                    (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
                right; left
                exact hty.symm.trans hslotTy
            | cons _hhead hrest _hunion _hintersection =>
                exact False.elim (LValTargetsTyping.nil_false hrest)

theorem joinCoherenceLeftEnv_coherent : Coherent joinCoherenceLeftEnv := by
  intro lv mutable targets borrowLifetime htyping
  have hshape := joinCoherenceLeftEnv_lvalTyping_shape htyping
  rcases hshape with h | h | h
  · cases h
  · cases h
  · cases h
    refine ⟨.int, Lifetime.root, LValTargetsTyping.singleton ?_⟩
    have ha : joinCoherenceLeftEnv.slotAt "a" =
        some { ty := .ty .int, lifetime := Lifetime.root } := by
      simp [joinCoherenceLeftEnv, Env.update]
    exact LValTyping.var ha

theorem joinCoherenceRightEnv_coherent : Coherent joinCoherenceRightEnv := by
  intro lv mutable targets borrowLifetime htyping
  have hshape := joinCoherenceRightEnv_lvalTyping_shape htyping
  rcases hshape with h | h | h
  · cases h
  · cases h
  · cases h
    refine ⟨.unit, Lifetime.root, LValTargetsTyping.singleton ?_⟩
    have hb : joinCoherenceRightEnv.slotAt "b" =
        some { ty := .ty .unit, lifetime := Lifetime.root } := by
      simp [joinCoherenceRightEnv, Env.update]
    exact LValTyping.var hb

theorem joinCoherenceJoinEnv_targets_not_typeable :
    ¬ ∃ ty lifetime,
      LValTargetsTyping joinCoherenceJoinEnv [.var "a", .var "b"] (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htargets⟩
  cases htargets with
  | cons hhead hrest hunion _hintersection =>
      rcases LValTyping.var_inv hhead with ⟨headSlot, hheadSlot, hheadTy, _⟩
      have hheadSlotTy : headSlot.ty = .ty .int := by
        simpa [joinCoherenceJoinEnv, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hheadSlot).symm
      cases hrest with
      | singleton htarget =>
          rcases LValTyping.var_inv htarget with ⟨restSlot, hrestSlot, hrestTy, _⟩
          have hrestSlotTy : restSlot.ty = .ty .unit := by
            simpa [joinCoherenceJoinEnv, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hrestSlot).symm
          have hheadTyPartialEq : PartialTy.ty _ = PartialTy.ty Ty.int :=
            hheadTy.symm.trans hheadSlotTy
          have hrestTyPartialEq : PartialTy.ty _ = PartialTy.ty Ty.unit :=
            hrestTy.symm.trans hrestSlotTy
          cases hheadTyPartialEq
          cases hrestTyPartialEq
          exact PartialTyUnion.int_unit_full_false hunion
      | cons _hhead2 hrest2 _hunion2 _hintersection2 =>
          exact False.elim (LValTargetsTyping.nil_false hrest2)

theorem joinCoherenceJoinEnv_not_coherent : ¬ Coherent joinCoherenceJoinEnv := by
  intro hcoh
  have hx : joinCoherenceJoinEnv.slotAt "x" =
      some { ty := .ty (.borrow false [.var "a", .var "b"]), lifetime := Lifetime.root } := by
    simp [joinCoherenceJoinEnv, Env.update]
  have htyping : LValTyping joinCoherenceJoinEnv (.var "x")
      (.ty (.borrow false [.var "a", .var "b"])) Lifetime.root :=
    LValTyping.var hx
  exact joinCoherenceJoinEnv_targets_not_typeable (hcoh (.var "x") false
    [.var "a", .var "b"] Lifetime.root htyping)

theorem joinCoherenceLeftEnv_linearizable : Linearizable joinCoherenceLeftEnv := by
  refine ⟨fun n => if n = "x" then 1 else 0, ?_⟩
  intro y slot hslot v hv
  by_cases hyx : y = "x"
  · subst hyx
    have hslotTy : slot.ty = .ty (.borrow false [.var "a"]) := by
      simpa [joinCoherenceLeftEnv, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hv
    simp [PartialTy.vars, Ty.vars, LVal.base] at hv ⊢
    subst hv
    simp
  · by_cases hyb : y = "b"
    · subst hyb
      have hslotTy : slot.ty = .ty .unit := by
        simpa [joinCoherenceLeftEnv, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · by_cases hya : y = "a"
      · subst hya
        have hslotTy : slot.ty = .ty .int := by
          simpa [joinCoherenceLeftEnv, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars] at hv
      · have hnone : joinCoherenceLeftEnv.slotAt y = none := by
          simp [joinCoherenceLeftEnv, Env.update, Env.empty, hyx, hyb, hya]
        rw [hslot] at hnone
        cases hnone

theorem joinCoherenceRightEnv_linearizable : Linearizable joinCoherenceRightEnv := by
  refine ⟨fun n => if n = "x" then 1 else 0, ?_⟩
  intro y slot hslot v hv
  by_cases hyx : y = "x"
  · subst hyx
    have hslotTy : slot.ty = .ty (.borrow false [.var "b"]) := by
      simpa [joinCoherenceRightEnv, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hv
    simp [PartialTy.vars, Ty.vars, LVal.base] at hv ⊢
    subst hv
    simp
  · by_cases hyb : y = "b"
    · subst hyb
      have hslotTy : slot.ty = .ty .unit := by
        simpa [joinCoherenceRightEnv, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · by_cases hya : y = "a"
      · subst hya
        have hslotTy : slot.ty = .ty .int := by
          simpa [joinCoherenceRightEnv, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars] at hv
      · have hnone : joinCoherenceRightEnv.slotAt y = none := by
          simp [joinCoherenceRightEnv, Env.update, Env.empty, hyx, hyb, hya]
        rw [hslot] at hnone
        cases hnone

theorem joinCoherenceJoinEnv_linearizable : Linearizable joinCoherenceJoinEnv := by
  refine ⟨fun n => if n = "x" then 1 else 0, ?_⟩
  intro y slot hslot v hv
  by_cases hyx : y = "x"
  · subst hyx
    have hslotTy : slot.ty = .ty (.borrow false [.var "a", .var "b"]) := by
      simpa [joinCoherenceJoinEnv, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hv
    simp [PartialTy.vars, Ty.vars, LVal.base] at hv ⊢
    rcases hv with hv | hv <;> subst hv <;> simp
  · by_cases hyb : y = "b"
    · subst hyb
      have hslotTy : slot.ty = .ty .unit := by
        simpa [joinCoherenceJoinEnv, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · by_cases hya : y = "a"
      · subst hya
        have hslotTy : slot.ty = .ty .int := by
          simpa [joinCoherenceJoinEnv, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars] at hv
      · have hnone : joinCoherenceJoinEnv.slotAt y = none := by
          simp [joinCoherenceJoinEnv, Env.update, Env.empty, hyx, hyb, hya]
        rw [hslot] at hnone
        cases hnone

theorem joinCoherenceEnvJoin :
    EnvJoin joinCoherenceLeftEnv joinCoherenceRightEnv joinCoherenceJoinEnv := by
  constructor
  · intro env hmem
    simp at hmem
    rcases hmem with h | h <;> subst h
    · intro y
      by_cases hyx : y = "x"
      · subst hyx
        simp [joinCoherenceLeftEnv, joinCoherenceJoinEnv, Env.update]
        exact PartialTyStrengthens.borrow (by
          intro target hmem
          simp at hmem
          simp [hmem])
      · by_cases hyb : y = "b"
        · subst hyb
          simp [joinCoherenceLeftEnv, joinCoherenceJoinEnv, Env.update]
        · by_cases hya : y = "a"
          · subst hya
            simp [joinCoherenceLeftEnv, joinCoherenceJoinEnv, Env.update]
          · simp [joinCoherenceLeftEnv, joinCoherenceJoinEnv, Env.update,
              Env.empty, hyx, hyb, hya]
    · intro y
      by_cases hyx : y = "x"
      · subst hyx
        simp [joinCoherenceRightEnv, joinCoherenceJoinEnv, Env.update]
        exact PartialTyStrengthens.borrow (by
          intro target hmem
          simp at hmem
          simp [hmem])
      · by_cases hyb : y = "b"
        · subst hyb
          simp [joinCoherenceRightEnv, joinCoherenceJoinEnv, Env.update]
        · by_cases hya : y = "a"
          · subst hya
            simp [joinCoherenceRightEnv, joinCoherenceJoinEnv, Env.update]
          · simp [joinCoherenceRightEnv, joinCoherenceJoinEnv, Env.update,
              Env.empty, hyx, hyb, hya]
  · intro upper hupper y
    by_cases hyx : y = "x"
    · subst hyx
      have hleft := hupper
        (by simp :
          joinCoherenceLeftEnv ∈ ({joinCoherenceLeftEnv, joinCoherenceRightEnv} : Set Env))
        "x"
      have hright := hupper
        (by simp :
          joinCoherenceRightEnv ∈ ({joinCoherenceLeftEnv, joinCoherenceRightEnv} : Set Env))
        "x"
      cases hslot : upper.slotAt "x" with
      | none =>
          simp [joinCoherenceLeftEnv, Env.update, hslot] at hleft
      | some upperSlot =>
          simp [joinCoherenceLeftEnv, joinCoherenceRightEnv, joinCoherenceJoinEnv,
            Env.update, hslot] at hleft hright ⊢
          constructor
          · exact hleft.1
          · have hjoinLe :
                PartialTyStrengthens
                  (.ty (.borrow false ([.var "a"] ++ [.var "b"]))) upperSlot.ty :=
              PartialTyUnion.borrow_append.2 (by
                intro candidate hcand
                simp at hcand
                rcases hcand with hcand | hcand
                · subst hcand
                  exact hleft.2
                · subst hcand
                  exact hright.2)
            simpa using hjoinLe
    · by_cases hyb : y = "b"
      · subst hyb
        have hleft := hupper
          (by simp :
            joinCoherenceLeftEnv ∈ ({joinCoherenceLeftEnv, joinCoherenceRightEnv} : Set Env))
          "b"
        simp [joinCoherenceLeftEnv, joinCoherenceJoinEnv, Env.update] at hleft ⊢
        exact hleft
      · by_cases hya : y = "a"
        · subst hya
          have hleft := hupper
            (by simp :
              joinCoherenceLeftEnv ∈ ({joinCoherenceLeftEnv, joinCoherenceRightEnv} : Set Env))
            "a"
          simp [joinCoherenceLeftEnv, joinCoherenceJoinEnv, Env.update] at hleft ⊢
          exact hleft
        · have hleft := hupper
            (by simp :
              joinCoherenceLeftEnv ∈ ({joinCoherenceLeftEnv, joinCoherenceRightEnv} : Set Env))
            y
          simp [joinCoherenceLeftEnv, joinCoherenceJoinEnv, Env.update, Env.empty,
            hyx, hyb, hya] at hleft ⊢
          exact hleft

/-- Bare `EnvJoin.preserves_coherent` is false: two coherent branches can merge
`&[a]` and `&[b]` into `&[a,b]`, while `a : int` and `b : unit` have no full
joint target type.  A valid join-coherence theorem needs the same cross-branch
target-shape/transport information carried by the fan-out invariants below. -/
theorem EnvJoin.preserves_coherent_bare_counterexample :
    ∃ left right join,
      EnvJoin left right join ∧
      Linearizable left ∧ Linearizable right ∧ Linearizable join ∧
      Coherent left ∧ Coherent right ∧ ¬ Coherent join := by
  exact ⟨joinCoherenceLeftEnv, joinCoherenceRightEnv, joinCoherenceJoinEnv,
    joinCoherenceEnvJoin, joinCoherenceLeftEnv_linearizable,
    joinCoherenceRightEnv_linearizable, joinCoherenceJoinEnv_linearizable,
    joinCoherenceLeftEnv_coherent, joinCoherenceRightEnv_coherent,
    joinCoherenceJoinEnv_not_coherent⟩

/-- Coherence obligations for joining two write fan-out branches.

The bare `EnvJoin.preserves_coherent` statement is false: joining can create a
borrow target list that neither branch had as a jointly typeable list.  The valid
replacement records how each borrow typing observed in the join is traced back to
one coherent branch, and how that branch's target-list typing transports forward
to the join. -/
structure EnvJoinCoherenceObligations (left right join : Env) : Prop where
  borrow_transport
    {lv : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime : Lifetime} :
    LValTyping join lv (.ty (.borrow mutable targets)) borrowLifetime →
      (∃ leftBorrowLifetime,
        LValTyping left lv (.ty (.borrow mutable targets)) leftBorrowLifetime ∧
          ∀ targetTy targetLifetime,
            LValTargetsTyping left targets (.ty targetTy) targetLifetime →
              ∃ joinTargetTy joinTargetLifetime,
                LValTargetsTyping join targets (.ty joinTargetTy) joinTargetLifetime)
      ∨
      (∃ rightBorrowLifetime,
        LValTyping right lv (.ty (.borrow mutable targets)) rightBorrowLifetime ∧
          ∀ targetTy targetLifetime,
            LValTargetsTyping right targets (.ty targetTy) targetLifetime →
              ∃ joinTargetTy joinTargetLifetime,
                LValTargetsTyping join targets (.ty joinTargetTy) joinTargetLifetime)

theorem EnvJoin.preserves_coherent_of_obligations {left right join : Env} :
    Coherent left →
    Coherent right →
    EnvJoinCoherenceObligations left right join →
    Coherent join := by
  intro hleftCoh hrightCoh hobligations lv mutable targets borrowLifetime htyping
  rcases hobligations.borrow_transport htyping with
    ⟨leftBorrowLifetime, hleftTyping, htargetsTransport⟩ |
    ⟨rightBorrowLifetime, hrightTyping, htargetsTransport⟩
  · rcases hleftCoh lv mutable targets leftBorrowLifetime hleftTyping with
      ⟨targetTy, targetLifetime, htargetsLeft⟩
    exact htargetsTransport targetTy targetLifetime htargetsLeft
  · rcases hrightCoh lv mutable targets rightBorrowLifetime hrightTyping with
      ⟨targetTy, targetLifetime, htargetsRight⟩
    exact htargetsTransport targetTy targetLifetime htargetsRight

theorem EnvWrite.preserves_coherent_of_obligations {env result : Env}
    {writeBase : Name} :
    Coherent env →
    EnvWriteCoherenceObligations env result writeBase →
    Coherent result := by
  intro hcoh hobligations lv mutable targets borrowLifetime htyping
  by_cases hbase : LVal.base lv = writeBase
  · exact hobligations.written_root_coherent hbase htyping
  · rcases hobligations.old_root_transport hbase htyping with
      ⟨⟨oldBorrowLifetime, htypingOld⟩, htargetsTransport⟩
    exact hcoh lv mutable targets oldBorrowLifetime htypingOld
      |>.elim (fun targetTy htarget =>
        htarget.elim (fun targetLifetime htargetsOld =>
          htargetsTransport targetTy targetLifetime htargetsOld))

/-- Under a *shape-preserving* strengthening the occurring variables only grow:
`a ⊑ b` and `a ≈shape b` give `vars a ⊆ vars b`.  (`sameShape` rules out the
`undef`-introducing strengthening cases, which would erase variables.) -/
theorem partialTy_vars_mono {a b : PartialTy} (hstr : PartialTyStrengthens a b) :
    PartialTy.sameShape a b → ∀ v, v ∈ PartialTy.vars a → v ∈ PartialTy.vars b := by
  induction hstr with
  | reflex => intro _ v hv; exact hv
  | @box aL bL _hsub ih =>
      intro hshape v hv
      simp only [PartialTy.vars] at hv ⊢
      exact ih (by simpa [PartialTy.sameShape] using hshape) v hv
  | @borrow m L R hsub =>
      intro _ v hv
      simp only [PartialTy.vars, Ty.vars, List.mem_map] at hv ⊢
      obtain ⟨t, ht, rfl⟩ := hv
      exact ⟨t, hsub ht, rfl⟩
  | @undefLeft aT bT _h _ih => intro _ v hv; simp [PartialTy.vars] at hv
  | @intoUndef aT bT _h _ih => intro hshape v _; simp [PartialTy.sameShape] at hshape
  | @boxIntoUndef aL bT _h _ih => intro hshape v _; simp [PartialTy.sameShape] at hshape

/-- A rank function for the larger environment `e'` linearizes the smaller `e`,
provided the strengthening `e → e'` is shape-preserving at every slot (so
variables only grow).  This lets a single `φ` (from `Linearizable e'`) serve both
environments in `lvalTyping_strengthen_transport`. -/
theorem linearizable_rankFn_of_le_shape {e e' : Env} {φ : Name → Nat}
    (hstr : ∀ x sE, e.slotAt x = some sE →
      ∃ sE', e'.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hφ' : ∀ x slot, e'.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x := by
  intro x sE hsE v hv
  rcases hstr x sE hsE with ⟨sE', hsE', hshape, hstrong⟩
  exact hφ' x sE' hsE' v (partialTy_vars_mono hstrong hshape v hv)

/-- **Deployment of the transport keystone to the deref-borrow join case**
(`borrow_borrow`).  Given the runtime invariants on the join environment (a rank
function for `left` and `join`, the shape-preserving slot map `left → join`,
`Coherent join`, and `WellFormedEnv join current`), a borrow typing of `source`
in `left` yields a typing of the reborrow `*source` in `join`.  Sorry-free: this
is the keystone applied to `*source`.  The explicit invariant parameters are
exactly what the write-fan-out driver supplies (via the preservation facts). -/
theorem borrowBorrowJoin_viaTransport
    {left join : Env} {source : LVal}
    {leftMutable : Bool} {leftTargets : List LVal} {leftTy : Ty}
    {leftBorrowLifetime leftLifetime current : Lifetime}
    (hstr : ∀ x sE, left.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hlinJoin : Linearizable join)
    (hcohJoin : Coherent join)
    (hwfJoin : WellFormedEnv join current)
    (hleft : LValTyping left source (.ty (.borrow leftMutable leftTargets))
      leftBorrowLifetime)
    (hleftTargets : LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime) :
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  obtain ⟨φ, hφJoin⟩ := hlinJoin
  have hφLeft := linearizable_rankFn_of_le_shape hstr hφJoin
  have hderefLeft : LValTyping left (.deref source) (.ty leftTy) leftLifetime :=
    LValTyping.borrow hleft hleftTargets
  rcases lvalTyping_strengthen_transport hstr hφLeft hφJoin hcohJoin
      (.deref source) hderefLeft with
    ⟨p', lf', hderefJoin, hshape, _hstrong⟩
  cases p' with
  | ty joinTy =>
      exact ⟨joinTy, lf', hderefJoin,
        LValTyping.lifetime_outlives_one hwfJoin hderefJoin⟩
  | box _ => simp [PartialTy.sameShape] at hshape
  | undef _ => simp [PartialTy.sameShape] at hshape

theorem EnvJoin.slot_union {left right join : Env} {x : Name}
    {leftSlot rightSlot joinSlot : EnvSlot} :
    EnvJoin left right join →
    left.slotAt x = some leftSlot →
    right.slotAt x = some rightSlot →
    join.slotAt x = some joinSlot →
    leftSlot.lifetime = joinSlot.lifetime ∧
      rightSlot.lifetime = joinSlot.lifetime ∧
      PartialTyUnion leftSlot.ty rightSlot.ty joinSlot.ty := by
  intro hjoin hleftSlot hrightSlot hjoinSlot
  have hleftMem : left ∈ ({left, right} : Set Env) := by simp
  have hrightMem : right ∈ ({left, right} : Set Env) := by simp
  have hleftStrength := hjoin.1 hleftMem x
  have hrightStrength := hjoin.1 hrightMem x
  simp [hleftSlot, hrightSlot, hjoinSlot] at hleftStrength hrightStrength
  refine ⟨hleftStrength.1, hrightStrength.1, ?_⟩
  constructor
  · intro ty hty
    simp at hty
    rcases hty with hty | hty
    · subst hty
      exact hleftStrength.2
    · subst hty
      exact hrightStrength.2
  · intro candidate hcandidate
    let candidateEnv : Env :=
      join.update x { joinSlot with ty := candidate }
    have hupper : candidateEnv ∈ upperBounds ({left, right} : Set Env) := by
      intro env henv
      simp at henv
      rcases henv with henv | henv
      · subst henv
        intro y
        by_cases hy : y = x
        · subst hy
          simp [candidateEnv, Env.update, hleftSlot]
          exact ⟨hleftStrength.1, hcandidate (by simp)⟩
        · have hleftAtY := hjoin.1 hleftMem y
          simpa [candidateEnv, Env.update, hy] using hleftAtY
      · subst henv
        intro y
        by_cases hy : y = x
        · subst hy
          simp [candidateEnv, Env.update, hrightSlot]
          exact ⟨hrightStrength.1, hcandidate (by simp)⟩
        · have hrightAtY := hjoin.1 hrightMem y
          simpa [candidateEnv, Env.update, hy] using hrightAtY
    have hjoinStrength := hjoin.2 hupper x
    simp [candidateEnv, Env.update, hjoinSlot] at hjoinStrength
    exact hjoinStrength

/-- A join preserves linearizability when both branches use the same rank
function.  This is the constructive replacement shape for the existential
`EnvJoin.preserves_linearizable` obligation from the followup paper. -/
theorem EnvJoin.preserves_linearizedBy {φ : Name → Nat} {left right join : Env} :
    EnvJoin left right join →
    LinearizedBy φ left →
    LinearizedBy φ right →
    LinearizedBy φ join := by
  intro hjoin hleft hright x joinSlot hjoinSlot v hv
  rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
    ⟨leftSlot, hleftSlot, _hleftLifetime⟩
  rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
    ⟨rightSlot, hrightSlot, _hrightLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨_hleftLife, _hrightLife, hunion⟩
  rcases partialTyUnion_vars_subset hunion hv with hvLeft | hvRight
  · exact hleft x leftSlot hleftSlot v hvLeft
  · exact hright x rightSlot hrightSlot v hvRight

theorem EnvJoin.preserves_linearizable_common {φ : Name → Nat}
    {left right join : Env} :
    EnvJoin left right join →
    LinearizedBy φ left →
    LinearizedBy φ right →
    Linearizable join := by
  intro hjoin hleft hright
  exact Linearizable.of_linearizedBy
    (EnvJoin.preserves_linearizedBy hjoin hleft hright)

/-- Appendix 9.6 shape stability: a `Definition 3.23` write of positive rank
preserves the *shape* of every slot, provided the write is leaf-shape-compatible
(`WriteShapeCompat`).  Positive rank forces every leaf update to be `W-Weak`
(a join that preserves shape via `partialTyJoin_sameShape`); the `W-Strong`
(rank 0) leaf — which could change `.undef`→`.ty` on re-initialisation — never
occurs in this regime, so it is discharged vacuously. -/
theorem EnvWrite.shapePreserved {rank : Nat} {env result : Env} {lv : LVal}
    {ty : Ty} :
    0 < rank →
    EnvWrite rank env lv ty result →
    (∀ slot, env.slotAt (LVal.base lv) = some slot →
      WriteShapeCompat env (LVal.path lv) slot.ty ty) →
    EnvShapePreserved env result := by
  intro hrank hwrite hsc
  refine EnvWrite.rec
    (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
      0 < rank → WriteShapeCompat env₁ path oldTy ty →
        EnvShapePreserved env₁ env₂ ∧ PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun rank env path targets ty result _ =>
      0 < rank →
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteShapeCompat env (LVal.path (prependPath path t)) tslot.ty ty) →
        EnvShapePreserved env result)
    (motive_3 := fun rank env lv ty result _ =>
      0 < rank →
      (∀ slot, env.slotAt (LVal.base lv) = some slot →
        WriteShapeCompat env (LVal.path lv) slot.ty ty) →
        EnvShapePreserved env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite hrank hsc
  case strong =>
    intro env old ty hrank0 _hcompat
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty hshape hjoinTy _hrank _hcompat
    exact ⟨EnvShapePreserved.refl env, partialTyJoin_sameShape hshape hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank hcompat
    cases hcompat with
    | box hInner =>
        rcases ih hrank hInner with ⟨hpres, hshape⟩
        exact ⟨hpres, hshape⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank hcompat
    cases hcompat with
    | borrow hTargets =>
        exact ⟨ih (Nat.succ_pos rank) hTargets, PartialTy.sameShape_refl _⟩
  case nil =>
    intro rank env path ty _hrank _hprem
    exact EnvShapePreserved.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank hprem
    exact ih hrank (fun slot hslot => hprem target (by simp) slot hslot)
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites hrank hprem
    have hupd : EnvShapePreserved env updated :=
      ihWrite hrank (fun slot hslot => hprem target (by simp) slot hslot)
    have hrest : EnvShapePreserved env restEnv :=
      ihWrites hrank
        (fun t ht slot hslot => hprem t (List.mem_cons_of_mem _ ht) slot hslot)
    intro x rslot hrslot
    rcases EnvJoin.lifetimesPreserved_left hjoin x rslot hrslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x rslot hrslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hrslot with ⟨_, _, hunionSlot⟩
    rcases hupd x us hus with ⟨es, hes, hShapeUS⟩
    rcases hrest x rs hrs with ⟨es', hes', hShapeRS⟩
    have hesEq : es = es' := Option.some.inj (hes.symm.trans hes')
    subst hesEq
    have hUSRS : PartialTy.sameShape us.ty rs.ty :=
      PartialTy.sameShape_trans (PartialTy.sameShape_symm hShapeUS) hShapeRS
    have hUSc : PartialTy.sameShape us.ty rslot.ty :=
      partialTyUnion_sameShape_of_sameShape hunionSlot hUSRS
    exact ⟨es, hes, PartialTy.sameShape_trans hShapeUS hUSc⟩
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank hprem
    have hsc' : WriteShapeCompat env₁ (LVal.path lv) slot.ty ty := hprem slot hslot
    rcases ih hrank hsc' with ⟨hpres, hshape⟩
    exact EnvShapePreserved.update_from_source_slot hpres hslot hshape

/-- Fan-out shape stability: a positive-rank `WriteBorrowTargets` of `ty`
preserves the shape of every slot, given per-target leaf shape-compatibility.
This is the `motive_2` already established inside `EnvWrite.shapePreserved`,
extracted as a standalone lemma so the write-fan-out driver can derive the
branch-sameShape it needs for the join merge. -/
theorem WriteBorrowTargets.shapePreserved {rank : Nat} {env result : Env}
    {path : List Unit} {targets : List LVal} {ty : Ty} :
    0 < rank →
    WriteBorrowTargets rank env path targets ty result →
    (∀ t, t ∈ targets → ∀ tslot,
      env.slotAt (LVal.base (prependPath path t)) = some tslot →
      WriteShapeCompat env (LVal.path (prependPath path t)) tslot.ty ty) →
    EnvShapePreserved env result := by
  intro hrank hwrites hsc
  refine WriteBorrowTargets.rec
    (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
      0 < rank → WriteShapeCompat env₁ path oldTy ty →
        EnvShapePreserved env₁ env₂ ∧ PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun rank env path targets ty result _ =>
      0 < rank →
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteShapeCompat env (LVal.path (prependPath path t)) tslot.ty ty) →
        EnvShapePreserved env result)
    (motive_3 := fun rank env lv ty result _ =>
      0 < rank →
      (∀ slot, env.slotAt (LVal.base lv) = some slot →
        WriteShapeCompat env (LVal.path lv) slot.ty ty) →
        EnvShapePreserved env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites hrank hsc
  case strong =>
    intro env old ty hrank0 _hcompat
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty hshape hjoinTy _hrank _hcompat
    exact ⟨EnvShapePreserved.refl env, partialTyJoin_sameShape hshape hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank hcompat
    cases hcompat with
    | box hInner =>
        rcases ih hrank hInner with ⟨hpres, hshape⟩
        exact ⟨hpres, hshape⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank hcompat
    cases hcompat with
    | borrow hTargets =>
        exact ⟨ih (Nat.succ_pos rank) hTargets, PartialTy.sameShape_refl _⟩
  case nil =>
    intro rank env path ty _hrank _hprem
    exact EnvShapePreserved.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank hprem
    exact ih hrank (fun slot hslot => hprem target (by simp) slot hslot)
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites hrank hprem
    have hupd : EnvShapePreserved env updated :=
      ihWrite hrank (fun slot hslot => hprem target (by simp) slot hslot)
    have hrest : EnvShapePreserved env restEnv :=
      ihWrites hrank
        (fun t ht slot hslot => hprem t (List.mem_cons_of_mem _ ht) slot hslot)
    intro x rslot hrslot
    rcases EnvJoin.lifetimesPreserved_left hjoin x rslot hrslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x rslot hrslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hrslot with ⟨_, _, hunionSlot⟩
    rcases hupd x us hus with ⟨es, hes, hShapeUS⟩
    rcases hrest x rs hrs with ⟨es', hes', hShapeRS⟩
    have hesEq : es = es' := Option.some.inj (hes.symm.trans hes')
    subst hesEq
    have hUSRS : PartialTy.sameShape us.ty rs.ty :=
      PartialTy.sameShape_trans (PartialTy.sameShape_symm hShapeUS) hShapeRS
    have hUSc : PartialTy.sameShape us.ty rslot.ty :=
      partialTyUnion_sameShape_of_sameShape hunionSlot hUSRS
    exact ⟨es, hes, PartialTy.sameShape_trans hShapeUS hUSc⟩
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank hprem
    have hsc' : WriteShapeCompat env₁ (LVal.path lv) slot.ty ty := hprem slot hslot
    rcases ih hrank hsc' with ⟨hpres, hshape⟩
    exact EnvShapePreserved.update_from_source_slot hpres hslot hshape

/-- Structural witness that a Definition 3.23 write descends to *initialised*
(`.ty`, never `.undef`) leaves.  Mirrors `WriteShapeCompat` but its leaf premise
is merely "the old leaf type is defined" — no `ShapeCompatible` (hence no
recursive target-typing construction).  This is exactly the discriminant of the
shape-breaking case: a positive-rank `W-Weak` preserves shape iff its leaf is not
`.undef` (re-initialisation `.undef ⊔ ty = ty` is the sole shape change). -/
inductive WriteLeafTy (env : Env) : List Unit → PartialTy → Ty → Prop where
  | leaf {oldTy ty : Ty} :
      WriteLeafTy env [] (.ty oldTy) ty
  | box {path : List Unit} {inner : PartialTy} {ty : Ty} :
      WriteLeafTy env path inner ty →
      WriteLeafTy env (() :: path) (.box inner) ty
  | borrow {mutable : Bool} {path : List Unit} {targets : List LVal} {ty : Ty} :
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty) →
      WriteLeafTy env (() :: path) (.ty (.borrow mutable targets)) ty

/-- Shape stability from initialised leaves: a positive-rank `EnvWrite` whose
leaves are defined (`WriteLeafTy`) preserves every slot's shape.

The strengthened `W-Weak` rule carries the local `ShapeCompatible` premise
needed to preserve shape at the leaf.
-/
theorem EnvWrite.shapePreserved_init {rank : Nat} {env result : Env} {lv : LVal}
    {ty : Ty} :
    0 < rank →
    EnvWrite rank env lv ty result →
    (∀ slot, env.slotAt (LVal.base lv) = some slot →
      WriteLeafTy env (LVal.path lv) slot.ty ty) →
    EnvShapePreserved env result := by
  intro hrank hwrite hsc
  refine EnvWrite.rec
    (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
      0 < rank → WriteLeafTy env₁ path oldTy ty →
        EnvShapePreserved env₁ env₂ ∧ PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun rank env path targets ty result _ =>
      0 < rank →
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty) →
        EnvShapePreserved env result)
    (motive_3 := fun rank env lv ty result _ =>
      0 < rank →
      (∀ slot, env.slotAt (LVal.base lv) = some slot →
        WriteLeafTy env (LVal.path lv) slot.ty ty) →
        EnvShapePreserved env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite hrank hsc
  case strong =>
    intro env old ty hrank0 _hcompat
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty hshape hjoinTy _hrank _hcompat
    exact ⟨EnvShapePreserved.refl env, partialTyJoin_sameShape hshape hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank hcompat
    cases hcompat with
    | box hInner =>
        rcases ih hrank hInner with ⟨hpres, hshape⟩
        exact ⟨hpres, hshape⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank hcompat
    cases hcompat with
    | borrow hTargets =>
        exact ⟨ih (Nat.succ_pos rank) hTargets, PartialTy.sameShape_refl _⟩
  case nil =>
    intro rank env path ty _hrank _hprem
    exact EnvShapePreserved.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank hprem
    exact ih hrank (fun slot hslot => hprem target (by simp) slot hslot)
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites hrank hprem
    have hupd : EnvShapePreserved env updated :=
      ihWrite hrank (fun slot hslot => hprem target (by simp) slot hslot)
    have hrest : EnvShapePreserved env restEnv :=
      ihWrites hrank
        (fun t ht slot hslot => hprem t (List.mem_cons_of_mem _ ht) slot hslot)
    intro x rslot hrslot
    rcases EnvJoin.lifetimesPreserved_left hjoin x rslot hrslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x rslot hrslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hrslot with ⟨_, _, hunionSlot⟩
    rcases hupd x us hus with ⟨es, hes, hShapeUS⟩
    rcases hrest x rs hrs with ⟨es', hes', hShapeRS⟩
    have hesEq : es = es' := Option.some.inj (hes.symm.trans hes')
    subst hesEq
    have hUSRS : PartialTy.sameShape us.ty rs.ty :=
      PartialTy.sameShape_trans (PartialTy.sameShape_symm hShapeUS) hShapeRS
    have hUSc : PartialTy.sameShape us.ty rslot.ty :=
      partialTyUnion_sameShape_of_sameShape hunionSlot hUSRS
    exact ⟨es, hes, PartialTy.sameShape_trans hShapeUS hUSc⟩
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank hprem
    have hsc' : WriteLeafTy env₁ (LVal.path lv) slot.ty ty := hprem slot hslot
    rcases ih hrank hsc' with ⟨hpres, hshape⟩
    exact EnvShapePreserved.update_from_source_slot hpres hslot hshape

/-- Fan-out version of `EnvWrite.shapePreserved_init`: a positive-rank
`WriteBorrowTargets` with initialised leaves preserves every slot's shape. -/
theorem WriteBorrowTargets.shapePreserved_init {rank : Nat} {env result : Env}
    {path : List Unit} {targets : List LVal} {ty : Ty} :
    0 < rank →
    WriteBorrowTargets rank env path targets ty result →
    (∀ t, t ∈ targets → ∀ tslot,
      env.slotAt (LVal.base (prependPath path t)) = some tslot →
      WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty) →
    EnvShapePreserved env result := by
  intro hrank hwrites hsc
  refine WriteBorrowTargets.rec
    (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
      0 < rank → WriteLeafTy env₁ path oldTy ty →
        EnvShapePreserved env₁ env₂ ∧ PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun rank env path targets ty result _ =>
      0 < rank →
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty) →
        EnvShapePreserved env result)
    (motive_3 := fun rank env lv ty result _ =>
      0 < rank →
      (∀ slot, env.slotAt (LVal.base lv) = some slot →
        WriteLeafTy env (LVal.path lv) slot.ty ty) →
        EnvShapePreserved env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites hrank hsc
  case strong =>
    intro env old ty hrank0 _hcompat
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty hshape hjoinTy _hrank _hcompat
    exact ⟨EnvShapePreserved.refl env, partialTyJoin_sameShape hshape hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank hcompat
    cases hcompat with
    | box hInner =>
        rcases ih hrank hInner with ⟨hpres, hshape⟩
        exact ⟨hpres, hshape⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank hcompat
    cases hcompat with
    | borrow hTargets =>
        exact ⟨ih (Nat.succ_pos rank) hTargets, PartialTy.sameShape_refl _⟩
  case nil =>
    intro rank env path ty _hrank _hprem
    exact EnvShapePreserved.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank hprem
    exact ih hrank (fun slot hslot => hprem target (by simp) slot hslot)
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites hrank hprem
    have hupd : EnvShapePreserved env updated :=
      ihWrite hrank (fun slot hslot => hprem target (by simp) slot hslot)
    have hrest : EnvShapePreserved env restEnv :=
      ihWrites hrank
        (fun t ht slot hslot => hprem t (List.mem_cons_of_mem _ ht) slot hslot)
    intro x rslot hrslot
    rcases EnvJoin.lifetimesPreserved_left hjoin x rslot hrslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x rslot hrslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hrslot with ⟨_, _, hunionSlot⟩
    rcases hupd x us hus with ⟨es, hes, hShapeUS⟩
    rcases hrest x rs hrs with ⟨es', hes', hShapeRS⟩
    have hesEq : es = es' := Option.some.inj (hes.symm.trans hes')
    subst hesEq
    have hUSRS : PartialTy.sameShape us.ty rs.ty :=
      PartialTy.sameShape_trans (PartialTy.sameShape_symm hShapeUS) hShapeRS
    have hUSc : PartialTy.sameShape us.ty rslot.ty :=
      partialTyUnion_sameShape_of_sameShape hunionSlot hUSRS
    exact ⟨es, hes, PartialTy.sameShape_trans hShapeUS hUSc⟩
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank hprem
    have hsc' : WriteLeafTy env₁ (LVal.path lv) slot.ty ty := hprem slot hslot
    rcases ih hrank hsc' with ⟨hpres, hshape⟩
    exact EnvShapePreserved.update_from_source_slot hpres hslot hshape

/-- Each target of a `WriteBorrowTargets` fan-out has its own single `EnvWrite`
at the dereferenced location `prependPath path t`.  (Extracted from the fan-out's
`singleton`/`cons` structure.)  This is what lets the per-target location/leaf
reasoning (`writeLeafTy_cont`, shape preservation) invert one target's write in
isolation. -/
theorem WriteBorrowTargets.member_write {rank : Nat} {env result : Env}
    {path : List Unit} {targets : List LVal} {rhsTy : Ty}
    (hwrites : WriteBorrowTargets rank env path targets rhsTy result) :
    ∀ t, t ∈ targets →
      ∃ result', EnvWrite rank env (prependPath path t) rhsTy result' := by
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun rank env path targets rhsTy _result _ =>
      ∀ t, t ∈ targets →
        ∃ result', EnvWrite rank env (prependPath path t) rhsTy result')
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
  case nil => intro rank env path ty t ht; simp at ht
  case singleton =>
      intro rank env updated path target ty hwrite _htyped _ih t ht
      rw [List.mem_singleton] at ht; subst ht; exact ⟨updated, hwrite⟩
  case cons =>
      intro rank env updated restEnv result path target rest ty
        hwrite _htyped _hrest _hjoin _ihWrite ihRest t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨updated, hwrite⟩
      · exact ihRest t ht
  case intro => intros; trivial

/-- `WriteLeafTy` is antitone under same-shape strengthening of its type
argument: if the write descends `a` to initialised leaves and `b ⊑ a` keeps the
same shape (so `b`'s borrow target lists are subsets of `a`'s), then it descends
`b` too — `b` simply imposes *fewer* per-target obligations.  This is what lets a
union-typed borrow's leaf witness specialise to each member borrow (member ⊑
union, same shape), resolving the merged-target-list mismatch. -/
theorem writeLeafTy_mono {env : Env} {q : List Unit} {a : PartialTy} {rhsTy : Ty}
    (h : WriteLeafTy env q a rhsTy) :
    ∀ {b : PartialTy}, PartialTyStrengthens b a → PartialTy.sameShape b a →
      WriteLeafTy env q b rhsTy := by
  induction h with
  | leaf =>
      intro b _hstr hshape
      cases b with
      | ty bt => exact WriteLeafTy.leaf
      | box _ => simp [PartialTy.sameShape] at hshape
      | undef _ => simp [PartialTy.sameShape] at hshape
  | box _hInner ih =>
      intro b hstr hshape
      cases b with
      | box innerB =>
          exact WriteLeafTy.box (ih (PartialTyStrengthens.box_inv hstr)
            (by simpa [PartialTy.sameShape] using hshape))
      | ty _ => simp [PartialTy.sameShape] at hshape
      | undef _ => simp [PartialTy.sameShape] at hshape
  | borrow hTargets _ih =>
      intro b hstr hshape
      cases b with
      | ty bt =>
          cases bt with
          | borrow mB targetsB =>
              rcases PartialTyStrengthens.from_borrow_inv hstr with ⟨_, heq, hsubset⟩
              cases heq
              exact WriteLeafTy.borrow (fun t ht tslot htslot =>
                hTargets t (hsubset ht) tslot htslot)
          | unit => simp [PartialTy.sameShape, Ty.sameShape] at hshape
          | int => simp [PartialTy.sameShape, Ty.sameShape] at hshape
          | box _ => simp [PartialTy.sameShape, Ty.sameShape] at hshape
      | box _ => simp [PartialTy.sameShape] at hshape
      | undef _ => simp [PartialTy.sameShape] at hshape

/-- For a `List Unit`, appending a `()` at the end equals prepending it (all
elements are `()`, so the list is determined by its length). -/
theorem list_unit_snoc : ∀ (p : List Unit), p ++ [()] = () :: p
  | [] => rfl
  | () :: p => by rw [List.cons_append, list_unit_snoc p]

@[simp] theorem base_prependPath (path : List Unit) (t : LVal) :
    LVal.base (prependPath path t) = LVal.base t := by
  induction path with
  | nil => rfl
  | cons _ p ih => simp [prependPath, LVal.base, ih]

@[simp] theorem path_prependPath (path : List Unit) (t : LVal) :
    LVal.path (prependPath path t) = LVal.path t ++ path := by
  induction path with
  | nil => simp [prependPath]
  | cons u p ih =>
      simp only [prependPath, LVal.path, ih, List.append_assoc, list_unit_snoc]

/-- **Matching lemma (the shape-bridge core).**  If `lv` types to `pt` and its
base slot is `slot`, then descending `slot.ty` along `path lv ++ q` reaches
initialised leaves whenever the continuation `pt`-write does (`WriteLeafTy env q
pt`).  Proven by mutual induction on the `LValTyping`/`LValTargetsTyping`
derivation: `var` is the continuation verbatim; `box`/`borrow` push one more
selector (the `borrow` case turns the per-target typings into `WriteLeafTy.borrow`
obligations); the multi-target `cons` specialises the union continuation to each
member via `writeLeafTy_mono`.  Top-level use takes `q = []` with the trivial
`WriteLeafTy.leaf`, giving `WriteLeafTy env (path lv) slot.ty rhsTy` for any
`lv : .ty _`. -/
theorem writeLeafTy_of_lvalTyping {env : Env} {lv : LVal} {pt : PartialTy}
    {lt : Lifetime} (htyping : LValTyping env lv pt lt) :
    ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
    ∀ (q : List Unit) (rhsTy : Ty),
      WriteLeafTy env q pt rhsTy →
      WriteLeafTy env (LVal.path lv ++ q) slot.ty rhsTy := by
  refine LValTyping.rec
    (motive_1 := fun lv pt _lt _ =>
      ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
      ∀ (q : List Unit) (rhsTy : Ty),
        WriteLeafTy env q pt rhsTy →
        WriteLeafTy env (LVal.path lv ++ q) slot.ty rhsTy)
    (motive_2 := fun targets pt _lt _ =>
      ∀ (q : List Unit) (rhsTy : Ty),
        WriteLeafTy env q pt rhsTy →
        ∀ t, t ∈ targets → ∀ tslot,
          env.slotAt (LVal.base t) = some tslot →
          WriteLeafTy env (LVal.path t ++ q) tslot.ty rhsTy)
    ?var ?box ?borrow ?singleton ?cons htyping
  case var =>
    intro x slot hslot slot' hslot' q rhsTy hleaf
    simp only [LVal.base] at hslot'
    have hEq : slot = slot' := by rw [hslot] at hslot'; exact Option.some.inj hslot'
    subst hEq
    simpa [LVal.base, LVal.path] using hleaf
  case box =>
    intro lv inner lifetime _hlv ih slot hslot q rhsTy hleaf
    rw [LVal.path, List.append_assoc]
    exact ih hslot (() :: q) rhsTy (WriteLeafTy.box hleaf)
  case borrow =>
    intro lv mutable targets borrowLifetime targetLifetime targetTy
      _hborrow _htargets ihBorrow ihTargets slot hslot q rhsTy hleaf
    rw [LVal.path, List.append_assoc]
    refine ihBorrow hslot (() :: q) rhsTy ?_
    refine WriteLeafTy.borrow (fun t ht tslot htslot => ?_)
    have hbase : env.slotAt (LVal.base t) = some tslot := by
      simpa using htslot
    have := ihTargets q rhsTy hleaf t ht tslot hbase
    simpa using this
  case singleton =>
    intro target ty lifetime _htarget ihTarget q rhsTy hleaf t ht tslot htslot
    rw [List.mem_singleton] at ht
    subst ht
    exact ihTarget htslot q rhsTy hleaf
  case cons =>
    intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest hunion _hintersection ihHead ihRest q rhsTy hleaf t ht tslot htslot
    obtain ⟨restFull, hrestFull⟩ := LValTargetsTyping.output_full _hrest
    subst hrestFull
    obtain ⟨unionFull, hunionFull⟩ := PartialTyUnion.ty_ty_full hunion
    subst hunionFull
    have hmemberLeaf : WriteLeafTy env q (.ty headTy) rhsTy := by
      apply writeLeafTy_mono hleaf (PartialTyUnion.left_strengthens hunion)
      show PartialTy.sameShape (.ty headTy) (.ty unionFull)
      simp only [PartialTy.sameShape]
      exact Ty.sameShape_symm (partialTyUnion_ty_left_sameShape hunion)
    have hrestLeaf : WriteLeafTy env q (.ty restFull) rhsTy := by
      apply writeLeafTy_mono hleaf (PartialTyUnion.right_strengthens hunion)
      show PartialTy.sameShape (.ty restFull) (.ty unionFull)
      simp only [PartialTy.sameShape]
      exact Ty.sameShape_symm
        (partialTyUnion_ty_left_sameShape (PartialTyUnion.symm hunion))
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ihHead htslot q rhsTy hmemberLeaf
    · exact ihRest q rhsTy hrestLeaf t ht tslot htslot

/-- A `Coherent` environment lets a borrow-typed lval be dereferenced: if `lv`
types to a borrow, its reborrow `*lv` types (to the joint target type).  This is
exactly `Coherent`'s payload packaged through `T-LvBor`; iterating it types each
nested deref of a write location `prependPath path t`. -/
theorem lvalTyping_deref_of_coherent {env : Env} (hcoh : Coherent env)
    {lv : LVal} {mutable : Bool} {targets : List LVal} {borrowLifetime : Lifetime}
    (h : LValTyping env lv (.ty (.borrow mutable targets)) borrowLifetime) :
    ∃ ty lifetime, LValTyping env (.deref lv) (.ty ty) lifetime := by
  obtain ⟨ty, lifetime, htargets⟩ := hcoh lv mutable targets borrowLifetime h
  exact ⟨ty, lifetime, LValTyping.borrow h htargets⟩

/-- A positive-rank write whose target lval is *initialised* (types to `.ty`)
preserves the shape of every slot.  The location typing `w : .ty` is exactly the
leaf-initialisation discriminant: the matching lemma turns it into the
`WriteLeafTy` premise of `EnvWrite.shapePreserved_init`. -/
theorem EnvWrite.shapePreserved_of_typed {env result : Env} {rank : Nat}
    {w : LVal} {rhsTy : Ty} {leafTy : Ty} {lf : Lifetime}
    (hrank : 0 < rank) (hwrite : EnvWrite rank env w rhsTy result)
    (hw : LValTyping env w (.ty leafTy) lf) :
    EnvShapePreserved env result := by
  apply EnvWrite.shapePreserved_init hrank hwrite
  intro slot hslot
  have := writeLeafTy_of_lvalTyping hw hslot [] rhsTy WriteLeafTy.leaf
  simpa using this

/-- Environment strengthening is transitive (an ingredient for the write-result
strengthening characterization `env ≤ result`). -/
theorem EnvStrengthens.trans {a b c : Env}
    (hab : EnvStrengthens a b) (hbc : EnvStrengthens b c) :
    EnvStrengthens a c := by
  intro x
  have h1 := hab x
  have h2 := hbc x
  cases hb : b.slotAt x with
  | none =>
      cases ha : a.slotAt x with
      | none =>
          cases hc : c.slotAt x with
          | none => trivial
          | some sc => rw [hb, hc] at h2; simp at h2
      | some sa => rw [ha, hb] at h1; simp at h1
  | some sb =>
      cases ha : a.slotAt x with
      | none => rw [ha, hb] at h1; simp at h1
      | some sa =>
          cases hc : c.slotAt x with
          | none => rw [hb, hc] at h2; simp at h2
          | some sc =>
              rw [ha, hb] at h1
              rw [hb, hc] at h2
              exact ⟨h1.1.trans h2.1, partialTyStrengthens_trans h1.2 h2.2⟩

theorem EnvStrengthens.update_from_source_slot {source middle : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvStrengthens source middle →
    source.slotAt x = some slot →
    PartialTyStrengthens slot.ty newTy →
    EnvStrengthens source (middle.update x { slot with ty := newTy }) := by
  intro hstr hslot hnew y
  by_cases hy : y = x
  · have hupd : (middle.update x { slot with ty := newTy }).slotAt y
        = some { slot with ty := newTy } := by rw [hy]; simp [Env.update]
    have hsy : source.slotAt y = some slot := by rw [hy]; exact hslot
    rw [hsy, hupd]
    exact ⟨rfl, hnew⟩
  · have hupd : (middle.update x { slot with ty := newTy }).slotAt y
        = middle.slotAt y := by simp [Env.update, hy]
    rw [hupd]
    exact hstr y

/-- A positive-rank `Definition 3.23` write only makes slots more defined:
`env ≤ result` (result strengthens env — borrow target lists only grow).  This is
the growth characterization complementing `EnvWrite.shapePreserved`. -/
theorem EnvWrite.envStrengthens {rank : Nat} {env result : Env} {lv : LVal}
    {ty : Ty} :
    0 < rank →
    EnvWrite rank env lv ty result →
    EnvStrengthens env result := by
  intro hrank hwrite
  refine EnvWrite.rec
    (motive_1 := fun rank env₁ _path oldTy _ty env₂ updatedTy _ =>
      0 < rank → EnvStrengthens env₁ env₂ ∧ PartialTyStrengthens oldTy updatedTy)
    (motive_2 := fun rank env _path _targets _ty result _ =>
      0 < rank → EnvStrengthens env result)
    (motive_3 := fun rank env _lv _ty result _ =>
      0 < rank → EnvStrengthens env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite hrank
  case strong =>
    intro env old ty hrank0
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty _hshape hjoinTy _hrank
    exact ⟨EnvStrengthens.refl env, PartialTyUnion.left_strengthens hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank
    rcases ih hrank with ⟨hpres, hinner⟩
    exact ⟨hpres, PartialTyStrengthens.box hinner⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank
    exact ⟨ih (Nat.succ_pos rank), PartialTyStrengthens.reflex⟩
  case nil =>
    intro rank env path ty _hrank
    exact EnvStrengthens.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank
    exact ih hrank
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite _ihWrites hrank
    have hupd : EnvStrengthens env updated := ihWrite hrank
    have hUpdResult : EnvStrengthens updated result := hjoin.1 (by simp)
    exact EnvStrengthens.trans hupd hUpdResult
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank
    rcases ih hrank with ⟨hpres, hstr⟩
    exact EnvStrengthens.update_from_source_slot hpres hslot hstr

/-- Every borrow target appearing in a result slot originates either from the
same variable's slot in the source env, or from the right-hand type written.
This is the per-slot growth bound (piece (A) of the coherence closure): writes
only grow borrow target lists by the rhs's contained-borrow targets. -/
def BorrowTargetOrigin
    (env : Env) (rhsTy : Ty) (x : Name) (mutable : Bool) (t : LVal) : Prop :=
  (∃ slot T, env.slotAt x = some slot ∧
    PartialTyContains slot.ty (.borrow mutable T) ∧ t ∈ T) ∨
  (∃ T, PartialTyContains (.ty rhsTy) (.borrow mutable T) ∧ t ∈ T)

/-- Type-level analogue of `BorrowTargetOrigin` used for the `UpdateAtPath`
motive: a borrow target in the updated type comes from the old type or the rhs. -/
def TypeBorrowOrigin
    (oldTy : PartialTy) (rhsTy : Ty) (mutable : Bool) (t : LVal) : Prop :=
  (∃ T, PartialTyContains oldTy (.borrow mutable T) ∧ t ∈ T) ∨
  (∃ T, PartialTyContains (.ty rhsTy) (.borrow mutable T) ∧ t ∈ T)

theorem EnvWrite.borrowTargetOrigin {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} :
    0 < rank →
    EnvWrite rank env lv rhsTy result →
    ∀ x slot m T, result.slotAt x = some slot →
      PartialTyContains slot.ty (.borrow m T) →
      ∀ t, t ∈ T → BorrowTargetOrigin env rhsTy x m t := by
  intro hrank hwrite
  refine EnvWrite.rec
    (motive_1 := fun rank env₁ _path oldTy ty env₂ updatedTy _ =>
      0 < rank →
      (∀ m T, PartialTyContains updatedTy (.borrow m T) →
        ∀ t, t ∈ T → TypeBorrowOrigin oldTy ty m t) ∧
      (∀ x slot m T, env₂.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env₁ ty x m t))
    (motive_2 := fun rank env _path _targets ty result _ =>
      0 < rank →
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x m t)
    (motive_3 := fun rank env _lv ty result _ =>
      0 < rank →
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x m t)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite hrank
  case strong =>
    intro env old ty h0
    exact absurd h0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty _hshape hjoin _hrank
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      rcases PartialTyUnion.contained_borrow_member hjoin hcontains ht with
        ⟨Tl, hl, htl⟩ | ⟨Tr, hr, htr⟩
      · exact Or.inl ⟨Tl, hl, htl⟩
      · exact Or.inr ⟨Tr, hr, htr⟩
    · intro x slot m T hslot hcontains t ht
      exact Or.inl ⟨slot, T, hslot, hcontains, ht⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupd ih hrank
    rcases ih hrank with ⟨ihType, ihEnv⟩
    refine ⟨?_, ihEnv⟩
    intro m T hcontains t ht
    cases hcontains with
    | box hinner =>
        rcases ihType m T hinner t ht with ⟨T₀, hc₀, ht₀⟩ | hrhs
        · exact Or.inl ⟨T₀, PartialTyContains.box hc₀, ht₀⟩
        · exact Or.inr hrhs
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      exact Or.inl ⟨T, hcontains, ht⟩
    · exact ih (Nat.succ_pos rank)
  case nil =>
    intro rank env path ty _hrank x slot m T hslot hcontains t ht
    exact Or.inl ⟨slot, T, hslot, hcontains, ht⟩
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank
    exact ih hrank
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites hrank x slot m T hslot hcontains t ht
    rcases EnvJoin.lifetimesPreserved_left hjoin x slot hslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x slot hslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hslot with ⟨_, _, hunion⟩
    rcases PartialTyUnion.contained_borrow_member hunion hcontains ht with
      ⟨Tl, hl, htl⟩ | ⟨Tr, hr, htr⟩
    · exact ihWrite hrank x us m Tl hus hl t htl
    · exact ihWrites hrank x rs m Tr hrs hr t htr
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank
      x rslot m T hrslot hcontains t ht
    rcases ih hrank with ⟨ihType, ihEnv⟩
    by_cases hx : x = LVal.base lv
    · have hreq : rslot = { slot with ty := updatedTy } := by
        have hlk : (env₂.update (LVal.base lv) { slot with ty := updatedTy }).slotAt x
            = some { slot with ty := updatedTy } := by rw [hx]; simp [Env.update]
        rw [hlk] at hrslot; exact (Option.some.inj hrslot).symm
      rw [hreq] at hcontains
      rcases ihType m T hcontains t ht with ⟨T₀, hc₀, ht₀⟩ | hrhs
      · exact Or.inl ⟨slot, T₀, by rw [hx]; exact hslot, hc₀, ht₀⟩
      · exact Or.inr hrhs
    · have hru : (env₂.update (LVal.base lv) { slot with ty := updatedTy }).slotAt x
          = env₂.slotAt x := by simp [Env.update, hx]
      rw [hru] at hrslot
      exact ihEnv x rslot m T hrslot hcontains t ht

/-- All-rank version of `EnvWrite.borrowTargetOrigin`.

The positive-rank theorem above discharged `W-Strong` vacuously.  At rank `0`,
`W-Strong` is the assignment case and any borrow exposed by the updated leaf comes
directly from the RHS type.  The same old-or-RHS origin classification therefore
holds for every `EnvWrite`; rank is only needed later if callers want to derive
the RHS-rank side condition from a positive-rank borrow fan-out rule. -/
theorem EnvWrite.borrowTargetOrigin_all {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} :
    EnvWrite rank env lv rhsTy result →
    ∀ x slot m T, result.slotAt x = some slot →
      PartialTyContains slot.ty (.borrow m T) →
      ∀ t, t ∈ T → BorrowTargetOrigin env rhsTy x m t := by
  intro hwrite
  refine EnvWrite.rec
    (motive_1 := fun _rank env₁ _path oldTy ty env₂ updatedTy _ =>
      (∀ m T, PartialTyContains updatedTy (.borrow m T) →
        ∀ t, t ∈ T → TypeBorrowOrigin oldTy ty m t) ∧
      (∀ x slot m T, env₂.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env₁ ty x m t))
    (motive_2 := fun _rank env _path _targets ty result _ =>
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x m t)
    (motive_3 := fun _rank env _lv ty result _ =>
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x m t)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite
  case strong =>
    intro env old ty
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      exact Or.inr ⟨T, hcontains, ht⟩
    · intro x slot m T hslot hcontains t ht
      exact Or.inl ⟨slot, T, hslot, hcontains, ht⟩
  case weak =>
    intro env rank old joined ty _hshape hjoin
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      rcases PartialTyUnion.contained_borrow_member hjoin hcontains ht with
        ⟨Tl, hl, htl⟩ | ⟨Tr, hr, htr⟩
      · exact Or.inl ⟨Tl, hl, htl⟩
      · exact Or.inr ⟨Tr, hr, htr⟩
    · intro x slot m T hslot hcontains t ht
      exact Or.inl ⟨slot, T, hslot, hcontains, ht⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupd ih
    rcases ih with ⟨ihType, ihEnv⟩
    refine ⟨?_, ihEnv⟩
    intro m T hcontains t ht
    cases hcontains with
    | box hinner =>
        rcases ihType m T hinner t ht with ⟨T₀, hc₀, ht₀⟩ | hrhs
        · exact Or.inl ⟨T₀, PartialTyContains.box hc₀, ht₀⟩
        · exact Or.inr hrhs
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      exact Or.inl ⟨T, hcontains, ht⟩
    · exact ih
  case nil =>
    intro rank env path ty x slot m T hslot hcontains t ht
    exact Or.inl ⟨slot, T, hslot, hcontains, ht⟩
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih
    exact ih
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites x slot m T hslot hcontains t ht
    rcases EnvJoin.lifetimesPreserved_left hjoin x slot hslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x slot hslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hslot with ⟨_, _, hunion⟩
    rcases PartialTyUnion.contained_borrow_member hunion hcontains ht with
      ⟨Tl, hl, htl⟩ | ⟨Tr, hr, htr⟩
    · exact ihWrite x us m Tl hus hl t htl
    · exact ihWrites x rs m Tr hrs hr t htr
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
      x rslot m T hrslot hcontains t ht
    rcases ih with ⟨ihType, ihEnv⟩
    by_cases hx : x = LVal.base lv
    · have hreq : rslot = { slot with ty := updatedTy } := by
        have hlk : (env₂.update (LVal.base lv) { slot with ty := updatedTy }).slotAt x
            = some { slot with ty := updatedTy } := by rw [hx]; simp [Env.update]
        rw [hlk] at hrslot; exact (Option.some.inj hrslot).symm
      rw [hreq] at hcontains
      rcases ihType m T hcontains t ht with ⟨T₀, hc₀, ht₀⟩ | hrhs
      · exact Or.inl ⟨slot, T₀, by rw [hx]; exact hslot, hc₀, ht₀⟩
      · exact Or.inr hrhs
    · have hru : (env₂.update (LVal.base lv) { slot with ty := updatedTy }).slotAt x
          = env₂.slotAt x := by simp [Env.update, hx]
      rw [hru] at hrslot
      exact ihEnv x rslot m T hrslot hcontains t ht

/-- Positive-rank write linearization under the explicit missing rank side
condition.

`EnvWrite.borrowTargetOrigin` says every variable in a positive-rank write result
comes either from the old slot at the same base, or from the RHS type.  The old
case is handled by the previous rank witness.  The RHS case is exactly the side
condition missing from the bare `EnvWrite.preserves_linearizedBy` statement. -/
theorem EnvWrite.preserves_linearizedBy_of_rhsVarsBelow {rank : Nat}
    {env result : Env} {lv : LVal} {rhsTy : Ty} {φ : Name → Nat} :
    0 < rank →
    EnvWrite rank env lv rhsTy result →
    LinearizedBy φ env →
    (∀ x slot, result.slotAt x = some slot →
      ∀ v, v ∈ Ty.vars rhsTy → φ v < φ x) →
    LinearizedBy φ result := by
  intro hrank hwrite hlin hrhs x slot hslot v hv
  rcases partialTy_vars_mem_contains v hv with
    ⟨mutable, targets, hcontains, target, htarget, hbase⟩
  rcases EnvWrite.borrowTargetOrigin hrank hwrite x slot mutable targets
      hslot hcontains target htarget with
    hfromOld | hfromRhs
  · rcases hfromOld with
      ⟨oldSlot, oldTargets, holdSlot, holdContains, holdTarget⟩
    have hvOld : v ∈ PartialTy.vars oldSlot.ty := by
      exact mem_partialTy_vars_iff.mpr
        ⟨mutable, oldTargets, target, holdContains, holdTarget, hbase⟩
    exact hlin x oldSlot holdSlot v hvOld
  · rcases hfromRhs with ⟨rhsTargets, hrhsContains, hrhsTarget⟩
    have hvRhsPartial : v ∈ PartialTy.vars (.ty rhsTy) := by
      exact mem_partialTy_vars_iff.mpr
        ⟨mutable, rhsTargets, target, hrhsContains, hrhsTarget, hbase⟩
    exact hrhs x slot hslot v (by simpa [PartialTy.vars] using hvRhsPartial)

/-- All-rank write linearization under an explicit RHS-rank side condition.

This is the non-vacuous replacement shape for the broad
`EnvWrite.preserves_linearizedBy` obligation: old borrow targets keep their
previous rank proof, and newly installed RHS borrow targets are covered by the
caller-provided acyclicity premise. -/
theorem EnvWrite.preserves_linearizedBy_of_rhsVarsBelow_all {rank : Nat}
    {env result : Env} {lv : LVal} {rhsTy : Ty} {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    LinearizedBy φ env →
    (∀ x slot, result.slotAt x = some slot →
      ∀ v, v ∈ Ty.vars rhsTy → φ v < φ x) →
    LinearizedBy φ result := by
  intro hwrite hlin hrhs x slot hslot v hv
  rcases partialTy_vars_mem_contains v hv with
    ⟨mutable, targets, hcontains, target, htarget, hbase⟩
  rcases EnvWrite.borrowTargetOrigin_all hwrite x slot mutable targets
      hslot hcontains target htarget with
    hfromOld | hfromRhs
  · rcases hfromOld with
      ⟨oldSlot, oldTargets, holdSlot, holdContains, holdTarget⟩
    have hvOld : v ∈ PartialTy.vars oldSlot.ty := by
      exact mem_partialTy_vars_iff.mpr
        ⟨mutable, oldTargets, target, holdContains, holdTarget, hbase⟩
    exact hlin x oldSlot holdSlot v hvOld
  · rcases hfromRhs with ⟨rhsTargets, hrhsContains, hrhsTarget⟩
    have hvRhsPartial : v ∈ PartialTy.vars (.ty rhsTy) := by
      exact mem_partialTy_vars_iff.mpr
        ⟨mutable, rhsTargets, target, hrhsContains, hrhsTarget, hbase⟩
    exact hrhs x slot hslot v (by simpa [PartialTy.vars] using hvRhsPartial)

theorem EnvWrite.preserves_linearizable_of_rhsVarsBelow_all {rank : Nat}
    {env result : Env} {lv : LVal} {rhsTy : Ty} {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    LinearizedBy φ env →
    (∀ x slot, result.slotAt x = some slot →
      ∀ v, v ∈ Ty.vars rhsTy → φ v < φ x) →
    Linearizable result := by
  intro hwrite hlin hbelow
  exact Linearizable.of_linearizedBy
    (EnvWrite.preserves_linearizedBy_of_rhsVarsBelow_all hwrite hlin hbelow)

/-- The rank side condition rejects the bare write-linearization counterexample.

In `writeLinearizationCycleEnv`, the old witness ranks `x < y` to justify the
old edge `y → x`.  Writing RHS `&y` into `x` would require the new edge `x → y`
to satisfy `φ y < φ x`, which is impossible for that same witness.
-/
theorem EnvWrite.linearizable_counterexample_violates_rhsBorrowTargetsBelow :
    ¬ EnvWriteRhsBorrowTargetsBelow
      (fun n => if n = "x" then 1 else if n = "y" then 2 else 0)
      writeLinearizationCycleResult (.borrow false [.var "y"]) := by
  intro hbelow
  have hx :
      writeLinearizationCycleResult.slotAt "x" =
        some { ty := .ty (.borrow false [.var "y"]), lifetime := Lifetime.root } := by
    simp [writeLinearizationCycleResult, Env.update]
  have hcontains :
      PartialTyContains (.ty (.borrow false [.var "y"]))
        (.borrow false [.var "y"]) :=
    PartialTyContains.here
  have hfromRhs :
      ∃ rhsMutable rhsTargets,
        PartialTyContains (.ty (.borrow false [.var "y"]))
          (.borrow rhsMutable rhsTargets) ∧
          (.var "y" : LVal) ∈ rhsTargets :=
    ⟨false, [.var "y"], PartialTyContains.here, by simp⟩
  have hlt :=
    hbelow.1 "x" { ty := .ty (.borrow false [.var "y"]), lifetime := Lifetime.root }
      false [.var "y"] (.var "y") hx hcontains (by simp) hfromRhs
  simp [LVal.base] at hlt

theorem EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all {rank : Nat}
    {env result : Env} {lv : LVal} {rhsTy : Ty} {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    LinearizedBy φ env →
    EnvWriteRhsBorrowTargetsBelow φ result rhsTy →
    LinearizedBy φ result := by
  intro hwrite hlin hbelow x slot hslot v hv
  rcases partialTy_vars_mem_contains v hv with
    ⟨mutable, targets, hcontains, target, htarget, hbase⟩
  rcases EnvWrite.borrowTargetOrigin_all hwrite x slot mutable targets
      hslot hcontains target htarget with
    hfromOld | hfromRhs
  · rcases hfromOld with
      ⟨oldSlot, oldTargets, holdSlot, holdContains, holdTarget⟩
    have hvOld : v ∈ PartialTy.vars oldSlot.ty := by
      exact mem_partialTy_vars_iff.mpr
        ⟨mutable, oldTargets, target, holdContains, holdTarget, hbase⟩
    exact hlin x oldSlot holdSlot v hvOld
  · have htargetBelow : φ (LVal.base target) < φ x :=
      hbelow.1 x slot mutable targets target hslot hcontains htarget
        (by
          rcases hfromRhs with ⟨rhsTargets, hrhsContains, hrhsTarget⟩
          exact ⟨mutable, rhsTargets, hrhsContains, hrhsTarget⟩)
    simpa [hbase] using htargetBelow

theorem EnvWrite.preserves_linearizable_of_rhsBorrowTargetsBelow_all {rank : Nat}
    {env result : Env} {lv : LVal} {rhsTy : Ty} {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    LinearizedBy φ env →
    EnvWriteRhsBorrowTargetsBelow φ result rhsTy →
    Linearizable result := by
  intro hwrite hlin hbelow
  exact Linearizable.of_linearizedBy
    (EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all hwrite hlin hbelow)

theorem LValTyping.box_partial_join_bounded {left right join : Env}
    {source : LVal} {leftInner rightInner : PartialTy}
    {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    LValTyping left source (.box leftInner) leftLifetime →
    LValTyping right source (.box rightInner) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinInner joinLifetime,
      PartialTyUnion leftInner rightInner joinInner ∧
        LValTyping join source (.box joinInner) joinLifetime ∧
          joinLifetime ≤ current := by
  intro hjoin hleft hright hleftOutlives hrightOutlives
  induction source generalizing leftInner rightInner leftLifetime rightLifetime with
  | var x =>
      rcases LValTyping.var_inv hleft with
        ⟨leftSlot, hleftSlot, hleftTy, hleftLifetime⟩
      rcases LValTyping.var_inv hright with
        ⟨rightSlot, hrightSlot, hrightTy, _hrightLifetime⟩
      rcases EnvJoin.lifetimesSurvive_left hjoin x leftSlot hleftSlot with
        ⟨joinSlot, hjoinSlot, hjoinLifetime⟩
      rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
        ⟨_hleftLife, _hrightLife, hunion⟩
      have hleftSlotTy : leftSlot.ty = .box leftInner := hleftTy
      have hrightSlotTy : rightSlot.ty = .box rightInner := hrightTy
      rw [hleftSlotTy, hrightSlotTy] at hunion
      rcases PartialTyUnion.box_box_shape hunion with ⟨joinInner, hjoinBox⟩
      have hinnerUnion :
          PartialTyUnion leftInner rightInner joinInner := by
        rw [hjoinBox] at hunion
        exact PartialTyUnion.box_inv hunion
      refine ⟨joinInner, joinSlot.lifetime, hinnerUnion, ?_, ?_⟩
      · simpa [hjoinBox] using LValTyping.var hjoinSlot
      · rw [← hjoinLifetime, hleftLifetime]
        exact hleftOutlives
  | deref source ih =>
      have hleftSource :
          LValTyping left source (.box (.box leftInner)) leftLifetime :=
        LValTyping.deref_box_inv hleft
      have hrightSource :
          LValTyping right source (.box (.box rightInner)) rightLifetime :=
        LValTyping.deref_box_inv hright
      rcases ih hleftSource hrightSource hleftOutlives hrightOutlives with
        ⟨joinOuter, joinLifetime, houterUnion, hjoinSource, hjoinOutlives⟩
      rcases PartialTyUnion.box_box_shape houterUnion with
        ⟨joinInner, hjoinOuter⟩
      have hinnerUnion :
          PartialTyUnion leftInner rightInner joinInner := by
        rw [hjoinOuter] at houterUnion
        exact PartialTyUnion.box_inv houterUnion
      refine ⟨joinInner, joinLifetime, hinnerUnion, ?_, hjoinOutlives⟩
      simpa [hjoinOuter] using LValTyping.box hjoinSource

theorem LValTyping.box_partial_join {left right join : Env}
    {source : LVal} {leftInner rightInner : PartialTy}
    {leftLifetime rightLifetime : Lifetime} :
    EnvJoin left right join →
    LValTyping left source (.box leftInner) leftLifetime →
    LValTyping right source (.box rightInner) rightLifetime →
    ∃ joinInner joinLifetime,
      PartialTyUnion leftInner rightInner joinInner ∧
        LValTyping join source (.box joinInner) joinLifetime := by
  intro hjoin hleft hright
  induction source generalizing leftInner rightInner leftLifetime rightLifetime with
  | var x =>
      rcases LValTyping.var_inv hleft with
        ⟨leftSlot, hleftSlot, hleftTy, _hleftLifetime⟩
      rcases LValTyping.var_inv hright with
        ⟨rightSlot, hrightSlot, hrightTy, _hrightLifetime⟩
      rcases EnvJoin.lifetimesSurvive_left hjoin x leftSlot hleftSlot with
        ⟨joinSlot, hjoinSlot, _hjoinLifetime⟩
      rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
        ⟨_hleftLife, _hrightLife, hunion⟩
      have hleftSlotTy : leftSlot.ty = .box leftInner := hleftTy
      have hrightSlotTy : rightSlot.ty = .box rightInner := hrightTy
      rw [hleftSlotTy, hrightSlotTy] at hunion
      rcases PartialTyUnion.box_box_shape hunion with ⟨joinInner, hjoinBox⟩
      have hinnerUnion :
          PartialTyUnion leftInner rightInner joinInner := by
        rw [hjoinBox] at hunion
        exact PartialTyUnion.box_inv hunion
      exact ⟨joinInner, joinSlot.lifetime, hinnerUnion,
        by simpa [hjoinBox] using LValTyping.var hjoinSlot⟩
  | deref source ih =>
      have hleftSource :
          LValTyping left source (.box (.box leftInner)) leftLifetime :=
        LValTyping.deref_box_inv hleft
      have hrightSource :
          LValTyping right source (.box (.box rightInner)) rightLifetime :=
        LValTyping.deref_box_inv hright
      rcases ih hleftSource hrightSource with
        ⟨joinOuter, joinLifetime, houterUnion, hjoinSource⟩
      rcases PartialTyUnion.box_box_shape houterUnion with
        ⟨joinInner, hjoinOuter⟩
      have hinnerUnion :
          PartialTyUnion leftInner rightInner joinInner := by
        rw [hjoinOuter] at houterUnion
        exact PartialTyUnion.box_inv houterUnion
      exact ⟨joinInner, joinLifetime, hinnerUnion,
        by simpa [hjoinOuter] using LValTyping.box hjoinSource⟩

theorem LValTyping.var_join_full {left right join : Env} {x : Name}
    {leftTy rightTy : Ty} {lifetime : Lifetime} :
    EnvJoin left right join →
    LValTyping left (.var x) (.ty leftTy) lifetime →
    LValTyping right (.var x) (.ty rightTy) lifetime →
    ∃ joinTy,
      LValTyping join (.var x) (.ty joinTy) lifetime := by
  intro hjoin hleftTyping hrightTyping
  rcases LValTyping.var_inv hleftTyping with
    ⟨leftSlot, hleftSlot, hleftTy, hleftLifetime⟩
  rcases LValTyping.var_inv hrightTyping with
    ⟨rightSlot, hrightSlot, hrightTy, hrightLifetime⟩
  rcases EnvJoin.lifetimesSurvive_left hjoin x leftSlot hleftSlot with
    ⟨joinSlot, hjoinSlot, hjoinLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨hleftLife, _hrightLife, hunion⟩
  have hleftSlotTy : leftSlot.ty = .ty leftTy := hleftTy
  have hrightSlotTy : rightSlot.ty = .ty rightTy := hrightTy
  rw [hleftSlotTy, hrightSlotTy] at hunion
  rcases PartialTyUnion.ty_ty_full hunion with ⟨joinTy, hjoinTy⟩
  exact ⟨joinTy, by
    rw [← hjoinTy]
    rw [← hleftLifetime, hjoinLifetime]
    exact LValTyping.var hjoinSlot⟩

theorem LValTyping.var_join_full_bounded {left right join : Env} {x : Name}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    LValTyping left (.var x) (.ty leftTy) leftLifetime →
    LValTyping right (.var x) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.var x) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftTyping hrightTyping hleftOutlives _hrightOutlives
  rcases LValTyping.var_inv hleftTyping with
    ⟨leftSlot, hleftSlot, hleftTy, hleftLifetime⟩
  rcases LValTyping.var_inv hrightTyping with
    ⟨rightSlot, hrightSlot, hrightTy, _hrightLifetime⟩
  rcases EnvJoin.lifetimesSurvive_left hjoin x leftSlot hleftSlot with
    ⟨joinSlot, hjoinSlot, hjoinLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨hleftLife, _hrightLife, hunion⟩
  have hleftSlotTy : leftSlot.ty = .ty leftTy := hleftTy
  have hrightSlotTy : rightSlot.ty = .ty rightTy := hrightTy
  rw [hleftSlotTy, hrightSlotTy] at hunion
  rcases PartialTyUnion.ty_ty_full hunion with ⟨joinTy, hjoinTy⟩
  refine ⟨joinTy, joinSlot.lifetime, ?_, ?_⟩
  · rw [← hjoinTy]
    exact LValTyping.var hjoinSlot
  · rw [← hjoinLifetime, hleftLifetime]
    exact hleftOutlives

theorem LValTyping.var_join_full_bounded_with_union
    {left right join : Env} {x : Name}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    LValTyping left (.var x) (.ty leftTy) leftLifetime →
    LValTyping right (.var x) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join (.var x) (.ty joinTy) joinLifetime ∧
          joinLifetime ≤ current := by
  intro hjoin hleftTyping hrightTyping hleftOutlives _hrightOutlives
  rcases LValTyping.var_inv hleftTyping with
    ⟨leftSlot, hleftSlot, hleftTy, hleftLifetime⟩
  rcases LValTyping.var_inv hrightTyping with
    ⟨rightSlot, hrightSlot, hrightTy, _hrightLifetime⟩
  rcases EnvJoin.lifetimesSurvive_left hjoin x leftSlot hleftSlot with
    ⟨joinSlot, hjoinSlot, hjoinLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨_hleftLife, _hrightLife, hunion⟩
  have hleftSlotTy : leftSlot.ty = .ty leftTy := hleftTy
  have hrightSlotTy : rightSlot.ty = .ty rightTy := hrightTy
  rw [hleftSlotTy, hrightSlotTy] at hunion
  rcases PartialTyUnion.ty_ty_full hunion with ⟨joinTy, hjoinTy⟩
  refine ⟨joinTy, joinSlot.lifetime, ?_, ?_, ?_⟩
  · simpa [hjoinTy] using hunion
  · rw [← hjoinTy]
    exact LValTyping.var hjoinSlot
  · rw [← hjoinLifetime, hleftLifetime]
    exact hleftOutlives

theorem LValTyping.var_join_box_full_bounded {left right join : Env} {x : Name}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    LValTyping left (.var x) (.box (.ty leftTy)) leftLifetime →
    LValTyping right (.var x) (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.var x) (.box (.ty joinTy)) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftTyping hrightTyping hleftOutlives _hrightOutlives
  rcases LValTyping.var_inv hleftTyping with
    ⟨leftSlot, hleftSlot, hleftTy, hleftLifetime⟩
  rcases LValTyping.var_inv hrightTyping with
    ⟨rightSlot, hrightSlot, hrightTy, _hrightLifetime⟩
  rcases EnvJoin.lifetimesSurvive_left hjoin x leftSlot hleftSlot with
    ⟨joinSlot, hjoinSlot, hjoinLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨hleftLife, _hrightLife, hunion⟩
  have hleftSlotTy : leftSlot.ty = .box (.ty leftTy) := hleftTy
  have hrightSlotTy : rightSlot.ty = .box (.ty rightTy) := hrightTy
  rw [hleftSlotTy, hrightSlotTy] at hunion
  rcases PartialTyUnion.box_box_shape hunion with ⟨joinInner, hjoinBox⟩
  have hinnerUnion :
      PartialTyUnion (.ty leftTy) (.ty rightTy) joinInner := by
    rw [hjoinBox] at hunion
    exact PartialTyUnion.box_inv hunion
  rcases PartialTyUnion.ty_ty_full hinnerUnion with ⟨joinTy, hjoinInner⟩
  refine ⟨joinTy, joinSlot.lifetime, ?_, ?_⟩
  · simpa [hjoinBox, hjoinInner] using LValTyping.var hjoinSlot
  · rw [← hjoinLifetime, hleftLifetime]
    exact hleftOutlives

theorem LValTyping.var_join_box_full_bounded_with_union
    {left right join : Env} {x : Name}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    LValTyping left (.var x) (.box (.ty leftTy)) leftLifetime →
    LValTyping right (.var x) (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join (.var x) (.box (.ty joinTy)) joinLifetime ∧
          joinLifetime ≤ current := by
  intro hjoin hleftTyping hrightTyping hleftOutlives _hrightOutlives
  rcases LValTyping.var_inv hleftTyping with
    ⟨leftSlot, hleftSlot, hleftTy, hleftLifetime⟩
  rcases LValTyping.var_inv hrightTyping with
    ⟨rightSlot, hrightSlot, hrightTy, _hrightLifetime⟩
  rcases EnvJoin.lifetimesSurvive_left hjoin x leftSlot hleftSlot with
    ⟨joinSlot, hjoinSlot, hjoinLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨_hleftLife, _hrightLife, hunion⟩
  have hleftSlotTy : leftSlot.ty = .box (.ty leftTy) := hleftTy
  have hrightSlotTy : rightSlot.ty = .box (.ty rightTy) := hrightTy
  rw [hleftSlotTy, hrightSlotTy] at hunion
  rcases PartialTyUnion.box_box_shape hunion with ⟨joinInner, hjoinBox⟩
  have hinnerUnion :
      PartialTyUnion (.ty leftTy) (.ty rightTy) joinInner := by
    rw [hjoinBox] at hunion
    exact PartialTyUnion.box_inv hunion
  rcases PartialTyUnion.ty_ty_full hinnerUnion with ⟨joinTy, hjoinInner⟩
  refine ⟨joinTy, joinSlot.lifetime, ?_, ?_, ?_⟩
  · simpa [hjoinInner] using hinnerUnion
  · simpa [hjoinBox, hjoinInner] using LValTyping.var hjoinSlot
  · rw [← hjoinLifetime, hleftLifetime]
    exact hleftOutlives

theorem LValTyping.deref_var_join_box_box_bounded {left right join : Env}
    {x : Name} {leftTy rightTy : Ty}
    {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    LValTyping left (.var x) (.box (.ty leftTy)) leftLifetime →
    LValTyping right (.var x) (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref (.var x)) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleft hright hleftOutlives hrightOutlives
  rcases LValTyping.var_join_box_full_bounded hjoin hleft hright
      hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, LValTyping.box hjoinTyping, hjoinOutlives⟩

theorem LValTyping.var_join_box_borrow_false {left right join : Env} {x : Name}
    {leftInner : PartialTy} {rightMutable : Bool} {rightTargets : List LVal}
    {leftLifetime rightLifetime : Lifetime} :
    EnvJoin left right join →
    LValTyping left (.var x) (.box leftInner) leftLifetime →
    LValTyping right (.var x) (.ty (.borrow rightMutable rightTargets))
      rightLifetime →
    False := by
  intro hjoin hleft hright
  rcases LValTyping.var_inv hleft with
    ⟨leftSlot, hleftSlot, hleftTy, _hleftLifetime⟩
  rcases LValTyping.var_inv hright with
    ⟨rightSlot, hrightSlot, hrightTy, _hrightLifetime⟩
  rcases EnvJoin.lifetimesSurvive_left hjoin x leftSlot hleftSlot with
    ⟨joinSlot, hjoinSlot, _hjoinLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨_hleftLife, _hrightLife, hunion⟩
  have hleftSlotTy : leftSlot.ty = .box leftInner := hleftTy
  have hrightSlotTy :
      rightSlot.ty = .ty (.borrow rightMutable rightTargets) := hrightTy
  rw [hleftSlotTy, hrightSlotTy] at hunion
  exact PartialTyUnion.not_box_borrow hunion

theorem LValTyping.var_join_borrow_box_false {left right join : Env} {x : Name}
    {leftMutable : Bool} {leftTargets : List LVal} {rightInner : PartialTy}
    {leftLifetime rightLifetime : Lifetime} :
    EnvJoin left right join →
    LValTyping left (.var x) (.ty (.borrow leftMutable leftTargets))
      leftLifetime →
    LValTyping right (.var x) (.box rightInner) rightLifetime →
    False := by
  intro hjoin hleft hright
  rcases LValTyping.var_inv hleft with
    ⟨leftSlot, hleftSlot, hleftTy, _hleftLifetime⟩
  rcases LValTyping.var_inv hright with
    ⟨rightSlot, hrightSlot, hrightTy, _hrightLifetime⟩
  rcases EnvJoin.lifetimesSurvive_left hjoin x leftSlot hleftSlot with
    ⟨joinSlot, hjoinSlot, _hjoinLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨_hleftLife, _hrightLife, hunion⟩
  have hleftSlotTy :
      leftSlot.ty = .ty (.borrow leftMutable leftTargets) := hleftTy
  have hrightSlotTy : rightSlot.ty = .box rightInner := hrightTy
  rw [hleftSlotTy, hrightSlotTy] at hunion
  exact PartialTyUnion.not_borrow_box hunion

theorem LValTyping.join_box_borrow_false {left right join : Env}
    {source : LVal} {boxInner : PartialTy}
    {mutable : Bool} {targets : List LVal}
    {leftLifetime rightLifetime : Lifetime} :
    EnvJoin left right join →
    LValTyping left source (.box boxInner) leftLifetime →
    LValTyping right source (.ty (.borrow mutable targets)) rightLifetime →
    False := by
  intro hjoin hleft hright
  induction source generalizing boxInner mutable targets leftLifetime rightLifetime with
  | var x =>
      exact LValTyping.var_join_box_borrow_false hjoin hleft hright
  | deref source ih =>
      have hleftSource :
          LValTyping left source (.box (.box boxInner)) leftLifetime :=
        LValTyping.deref_box_inv hleft
      cases hright with
      | box hrightSource =>
          rcases LValTyping.box_partial_join hjoin hleftSource hrightSource with
            ⟨_joinInner, _joinLifetime, hunion, _hjoinTyping⟩
          exact PartialTyUnion.not_box_borrow hunion
      | borrow hrightSource _hrightTargets =>
          exact ih hleftSource hrightSource

theorem LValTyping.join_borrow_box_false {left right join : Env}
    {source : LVal} {boxInner : PartialTy}
    {mutable : Bool} {targets : List LVal}
    {leftLifetime rightLifetime : Lifetime} :
    EnvJoin left right join →
    LValTyping left source (.ty (.borrow mutable targets)) leftLifetime →
    LValTyping right source (.box boxInner) rightLifetime →
    False := by
  intro hjoin hleft hright
  induction source generalizing boxInner mutable targets leftLifetime rightLifetime with
  | var x =>
      exact LValTyping.var_join_borrow_box_false hjoin hleft hright
  | deref source ih =>
      have hrightSource :
          LValTyping right source (.box (.box boxInner)) rightLifetime :=
        LValTyping.deref_box_inv hright
      cases hleft with
      | box hleftSource =>
          rcases LValTyping.box_partial_join hjoin hleftSource hrightSource with
            ⟨_joinInner, _joinLifetime, hunion, _hjoinTyping⟩
          exact PartialTyUnion.not_borrow_box hunion
      | borrow hleftSource _hleftTargets =>
          exact ih hleftSource hrightSource

theorem LValTyping.var_update_union_full_left {env : Env} {x : Name}
    {slot : EnvSlot} {oldTy rhsTy : Ty} {unionTy : PartialTy} :
    slot.ty = .ty oldTy →
    PartialTyUnion slot.ty (.ty rhsTy) unionTy →
    ∃ joinedTy,
      LValTyping (env.update x { slot with ty := unionTy }) (.var x)
        (.ty joinedTy) slot.lifetime := by
  intro hslotTy hunion
  rw [hslotTy] at hunion
  rcases PartialTyUnion.ty_ty_full hunion with ⟨joinedTy, hunionTy⟩
  exact ⟨joinedTy, by
    simpa [hunionTy] using
      LValTyping.var
        (env := env.update x { slot with ty := unionTy })
        (x := x)
        (slot := { slot with ty := unionTy })
        (by simp [Env.update])⟩

theorem LValBaseOutlives.join_left {left right join : Env}
    {target : LVal} {lifetime : Lifetime} :
    EnvJoin left right join →
    LValBaseOutlives left target lifetime →
    LValBaseOutlives join target lifetime := by
  intro hjoin hbase
  rcases hbase with ⟨baseSlot, hbaseSlot, houtlives⟩
  rcases EnvJoin.lifetimesSurvive_left hjoin (LVal.base target) baseSlot hbaseSlot with
    ⟨joinSlot, hjoinSlot, hlifetime⟩
  exact ⟨joinSlot, hjoinSlot, by rw [← hlifetime]; exact houtlives⟩

theorem LValBaseOutlives.join_right {left right join : Env}
    {target : LVal} {lifetime : Lifetime} :
    EnvJoin left right join →
    LValBaseOutlives right target lifetime →
    LValBaseOutlives join target lifetime := by
  intro hjoin hbase
  rcases hbase with ⟨baseSlot, hbaseSlot, houtlives⟩
  rcases EnvJoin.lifetimesSurvive_right hjoin (LVal.base target) baseSlot hbaseSlot with
    ⟨joinSlot, hjoinSlot, hlifetime⟩
  exact ⟨joinSlot, hjoinSlot, by rw [← hlifetime]; exact houtlives⟩

/-- Single-lval join transport with the lifetime bound now DISCHARGED via the
rank-stratified foundation stone.  The transported typing's lifetime is bounded
by its base slot (`lvalTyping_lifetime_le_base_bounded`, using the rank-`<N`
contained-borrow invariant `hcontN` of `join` — supplied by the strong-induction
hypothesis of the `ContainedBorrows join` bootstrap), and the base slot is bounded
by `current` (`LValBaseOutlives.join_left`). -/
theorem fullJoinTransport_viaInvariants {source join : Env} {target : LVal}
    {sourceTy : Ty} {sourceLifetime current : Lifetime} {φ : Name → Nat} {N : Nat}
    (hstr : ∀ x sE, source.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hφJoin : ∀ x slot, join.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcohJoin : Coherent join)
    (hcontN : ∀ x slot mutable T, φ x < N → join.slotAt x = some slot →
        join ⊢ x ↝ Ty.borrow mutable T → BorrowTargetsWellFormedInSlot join slot.lifetime T)
    (hrankN : φ (LVal.base target) < N)
    (hsourceTyping : LValTyping source target (.ty sourceTy) sourceLifetime)
    (hjoinBase : LValBaseOutlives join target current) :
    ∃ joinTy joinLifetime,
      LValTyping join target (.ty joinTy) joinLifetime ∧ joinLifetime ≤ current := by
  have hφSource := linearizable_rankFn_of_le_shape hstr hφJoin
  rcases lvalTyping_strengthen_transport hstr hφSource hφJoin hcohJoin target
      hsourceTyping with ⟨p', lf', hjoinTyping, hshape, _hstrong⟩
  cases p' with
  | ty joinTy =>
      refine ⟨joinTy, lf', hjoinTyping, ?_⟩
      obtain ⟨tbs, htbs, htbsle⟩ := hjoinBase
      exact LifetimeOutlives.trans
        (lvalTyping_lifetime_le_base_bounded N hφJoin hcontN target hrankN hjoinTyping htbs)
        htbsle
  | box _ => simp [PartialTy.sameShape] at hshape
  | undef _ => simp [PartialTy.sameShape] at hshape

/-- Per-target borrow-invariant preservation across a join, derived
one-directionally from the `left` branch via the keystone + runtime invariants.
This replaces the symmetric `FullLValTypingJoinTransport`-based
`BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport`. -/
theorem BorrowTargetsWellFormedInSlot.join_viaInvariants_left
    {left right join : Env} {targets : List LVal} {slotLifetime : Lifetime}
    {φ : Name → Nat} {N : Nat}
    (hjoin : EnvJoin left right join)
    (hstr : ∀ x sE, left.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hφJoin : ∀ x slot, join.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcohJoin : Coherent join)
    (hcontN : ∀ x slot mutable T, φ x < N → join.slotAt x = some slot →
        join ⊢ x ↝ Ty.borrow mutable T → BorrowTargetsWellFormedInSlot join slot.lifetime T)
    (hrankTargets : ∀ t, t ∈ targets → φ (LVal.base t) < N)
    (hleft : BorrowTargetsWellFormedInSlot left slotLifetime targets) :
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  intro target htarget
  rcases hleft target htarget with
    ⟨leftTy, leftLifetime, hleftTyping, _hleftOutlives, hleftBase, hleftVar⟩
  have hjoinBase := LValBaseOutlives.join_left hjoin hleftBase
  rcases fullJoinTransport_viaInvariants hstr hφJoin hcohJoin hcontN
      (hrankTargets target htarget) hleftTyping hjoinBase
    with ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives, hjoinBase, hleftVar⟩

/-- Right-branch mirror of `BorrowTargetsWellFormedInSlot.join_viaInvariants_left`. -/
theorem BorrowTargetsWellFormedInSlot.join_viaInvariants_right
    {left right join : Env} {targets : List LVal} {slotLifetime : Lifetime}
    {φ : Name → Nat} {N : Nat}
    (hjoin : EnvJoin left right join)
    (hstr : ∀ x sE, right.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hφJoin : ∀ x slot, join.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcohJoin : Coherent join)
    (hcontN : ∀ x slot mutable T, φ x < N → join.slotAt x = some slot →
        join ⊢ x ↝ Ty.borrow mutable T → BorrowTargetsWellFormedInSlot join slot.lifetime T)
    (hrankTargets : ∀ t, t ∈ targets → φ (LVal.base t) < N)
    (hright : BorrowTargetsWellFormedInSlot right slotLifetime targets) :
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  intro target htarget
  rcases hright target htarget with
    ⟨rightTy, rightLifetime, hrightTyping, _hrightOutlives, hrightBase, hrightVar⟩
  have hjoinBase := LValBaseOutlives.join_right hjoin hrightBase
  rcases fullJoinTransport_viaInvariants hstr hφJoin hcohJoin hcontN
      (hrankTargets target htarget) hrightTyping hjoinBase
    with ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives, hjoinBase, hrightVar⟩

/-- The slot shape-map `env → result` for a single `EnvWrite`, assembled from
`EnvWrite.envStrengthens` (existence + strengthening) and `EnvWrite.shapePreserved`
(no `undef` introduced).  Supplies `hstr` for the keystone in the write case. -/
theorem EnvWrite.shapeMap {rank : Nat} {env result : Env} {lv : LVal} {ty : Ty}
    (hrank : 0 < rank) (hwrite : EnvWrite rank env lv ty result)
    (hsc : ∀ slot, env.slotAt (LVal.base lv) = some slot →
      WriteShapeCompat env (LVal.path lv) slot.ty ty) :
    ∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty := by
  intro x sE hsE
  have hstrength := EnvWrite.envStrengthens hrank hwrite x
  have hshapePres := EnvWrite.shapePreserved hrank hwrite hsc
  rw [hsE] at hstrength
  cases hresult : result.slotAt x with
  | none => rw [hresult] at hstrength; exact absurd hstrength (by simp)
  | some sR =>
      rw [hresult] at hstrength
      rcases hshapePres x sR hresult with ⟨sE', hsE', hshape⟩
      have hEq : sE' = sE := Option.some.inj (hsE'.symm.trans hsE)
      subst hEq
      exact ⟨sR, rfl, hshape, hstrength.2⟩

/-- Slot shape-map `left → join` for a join whose branches are slot-sameShape
(`hbranch`): the joined slot is `sameShape` with the left branch slot (union of
two same-shape slots) and strengthens from it.  Branch sameShape holds for the
write fan-out (both branches are shape-preserving writes of a common env). -/
theorem EnvJoin.fanOutShapeMap_left {left right join : Env}
    (hjoin : EnvJoin left right join)
    (hbranch : ∀ x sL sR, left.slotAt x = some sL → right.slotAt x = some sR →
      PartialTy.sameShape sL.ty sR.ty) :
    ∀ x sE, left.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty := by
  intro x sL hsL
  have hleL := EnvJoin.le_left hjoin x
  rw [hsL] at hleL
  cases hsJ : join.slotAt x with
  | none => rw [hsJ] at hleL; exact absurd hleL (by simp)
  | some sJ =>
      have hleR := EnvJoin.le_right hjoin x
      rw [hsJ] at hleR
      cases hsR : right.slotAt x with
      | none => rw [hsR] at hleR; exact absurd hleR (by simp)
      | some sR =>
          rcases EnvJoin.slot_union hjoin hsL hsR hsJ with ⟨_, _, hunion⟩
          exact ⟨sJ, rfl,
            partialTyUnion_sameShape_of_sameShape hunion (hbranch x sL sR hsL hsR),
            PartialTyUnion.left_strengthens hunion⟩

/-- Right-branch mirror of `EnvJoin.fanOutShapeMap_left`. -/
theorem EnvJoin.fanOutShapeMap_right {left right join : Env}
    (hjoin : EnvJoin left right join)
    (hbranch : ∀ x sL sR, left.slotAt x = some sL → right.slotAt x = some sR →
      PartialTy.sameShape sL.ty sR.ty) :
    ∀ x sE, right.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty := by
  intro x sR hsR
  have hleR := EnvJoin.le_right hjoin x
  rw [hsR] at hleR
  cases hsJ : join.slotAt x with
  | none => rw [hsJ] at hleR; exact absurd hleR (by simp)
  | some sJ =>
      have hleL := EnvJoin.le_left hjoin x
      rw [hsJ] at hleL
      cases hsL : left.slotAt x with
      | none => rw [hsL] at hleL; exact absurd hleL (by simp)
      | some sL =>
          rcases EnvJoin.slot_union hjoin hsL hsR hsJ with ⟨_, _, hunion⟩
          have hsameLR : PartialTy.sameShape sL.ty sR.ty := hbranch x sL sR hsL hsR
          have hsameLJ : PartialTy.sameShape sL.ty sJ.ty :=
            partialTyUnion_sameShape_of_sameShape hunion hsameLR
          exact ⟨sJ, rfl,
            PartialTy.sameShape_trans (PartialTy.sameShape_symm hsameLR) hsameLJ,
            PartialTyUnion.right_strengthens hunion⟩

theorem EnvJoin.contained_borrow_member {left right join : Env} {x : Name}
    {joinSlot : EnvSlot} {mutable : Bool} {targets : List LVal}
    {target : LVal} :
    EnvJoin left right join →
    join.slotAt x = some joinSlot →
    PartialTyContains joinSlot.ty (.borrow mutable targets) →
    target ∈ targets →
    (∃ leftSlot leftTargets,
      left.slotAt x = some leftSlot ∧
      PartialTyContains leftSlot.ty (.borrow mutable leftTargets) ∧
      target ∈ leftTargets) ∨
    (∃ rightSlot rightTargets,
      right.slotAt x = some rightSlot ∧
      PartialTyContains rightSlot.ty (.borrow mutable rightTargets) ∧
      target ∈ rightTargets) := by
  intro hjoin hjoinSlot hcontains htarget
  rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
    ⟨leftSlot, hleftSlot, _hleftLifetime⟩
  rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
    ⟨rightSlot, hrightSlot, _hrightLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨_hleftLife, _hrightLife, hunion⟩
  rcases PartialTyUnion.contained_borrow_member hunion hcontains htarget with
    hleft | hright
  · rcases hleft with ⟨leftTargets, hcontainsLeft, htargetLeft⟩
    exact Or.inl ⟨leftSlot, leftTargets, hleftSlot, hcontainsLeft, htargetLeft⟩
  · rcases hright with ⟨rightTargets, hcontainsRight, htargetRight⟩
    exact Or.inr ⟨rightSlot, rightTargets, hrightSlot, hcontainsRight, htargetRight⟩

theorem BorrowTargetsWellFormedInSlot.of_partialTyUnion {env : Env}
    {left right union : PartialTy} {lifetime : Lifetime} :
    PartialTyUnion left right union →
    (∀ {mutable targets},
      PartialTyContains left (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot env lifetime targets) →
    (∀ {mutable targets},
      PartialTyContains right (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot env lifetime targets) →
    ∀ {mutable targets},
      PartialTyContains union (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot env lifetime targets := by
  -- With the borrow invariant stated per target (Definition 4.8(i)), the union
  -- case is immediate: rule W-Bor merges the target lists of `left` and `right`,
  -- so every target of the union's borrow is a target of `left`'s or `right`'s
  -- borrow, and that side's per-target well-formedness supplies its typing,
  -- lifetime bound and base-slot survival directly.  No joint target-list typing
  -- of the merged list is needed (it need not exist; see the note on
  -- `BorrowTargetsWellFormedInSlot`).
  intro hunion hleft hright mutable targets hcontains target htarget
  rcases PartialTyUnion.contained_borrow_member hunion hcontains htarget with
    hfromLeft | hfromRight
  · rcases hfromLeft with ⟨leftTargets, hcontainsLeft, htargetLeft⟩
    exact hleft hcontainsLeft target htargetLeft
  · rcases hfromRight with ⟨rightTargets, hcontainsRight, htargetRight⟩
    exact hright hcontainsRight target htargetRight

theorem PartialTyBorrowsWellFormedInSlot.of_partialTyUnion {env : Env}
    {left right union : PartialTy} {lifetime : Lifetime} :
    PartialTyUnion left right union →
    PartialTyBorrowsWellFormedInSlot env lifetime left →
    PartialTyBorrowsWellFormedInSlot env lifetime right →
    PartialTyBorrowsWellFormedInSlot env lifetime union := by
  intro hunion hleft hright mutable targets hcontains
  exact BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion hleft hright hcontains

theorem ContainedBorrowsWellFormed.join_of_inSlot {left right join : Env} :
    EnvJoin left right join →
    (∀ {x slot mutable targets},
      left.slotAt x = some slot →
      left ⊢ x ↝ Ty.borrow mutable targets →
      BorrowTargetsWellFormedInSlot join slot.lifetime targets) →
    (∀ {x slot mutable targets},
      right.slotAt x = some slot →
      right ⊢ x ↝ Ty.borrow mutable targets →
      BorrowTargetsWellFormedInSlot join slot.lifetime targets) →
    ContainedBorrowsWellFormed join := by
  intro hjoin hleft hright x joinSlot mutable targets hjoinSlot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq : containedSlot = joinSlot := by
    have hsomeEq : some containedSlot = some joinSlot := by
      rw [← hcontainedSlot, hjoinSlot]
    exact Option.some.inj hsomeEq
  have hcontainsJoin : PartialTyContains joinSlot.ty (.borrow mutable targets) := by
    simpa [hcontainedSlotEq] using hcontainsTy
  rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
    ⟨leftSlot, hleftSlot, _hleftLifetime⟩
  rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
    ⟨rightSlot, hrightSlot, _hrightLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨hleftLife, hrightLife, hunion⟩
  exact BorrowTargetsWellFormedInSlot.of_partialTyUnion
    (env := join) (lifetime := joinSlot.lifetime) hunion
    (by
      intro leftMutable leftTargets hcontainsLeft
      have htargets :
          BorrowTargetsWellFormedInSlot join leftSlot.lifetime leftTargets :=
        hleft hleftSlot ⟨leftSlot, hleftSlot, hcontainsLeft⟩
      simpa [hleftLife] using htargets)
    (by
      intro rightMutable rightTargets hcontainsRight
      have htargets :
          BorrowTargetsWellFormedInSlot join rightSlot.lifetime rightTargets :=
        hright hrightSlot ⟨rightSlot, hrightSlot, hcontainsRight⟩
      simpa [hrightLife] using htargets)
    hcontainsJoin

/-- Contained-borrow join preservation, now via the **rank-stratified bootstrap**.
`ContainedBorrows join` is established by strong induction on the slot rank `φ x`:
the borrow at `x` (rank `n`) has targets all of rank `< n` (Linearizable), so the
per-target join transport (`join_viaInvariants_left/right`) bounds their lifetimes
using the rank-`<n` invariant supplied by the induction hypothesis (`hcontN`).
This breaks the circularity the old `fullJoinTransport` lifetime gap hit. -/
theorem ContainedBorrowsWellFormed.join_viaInvariants {left right join : Env}
    (hjoin : EnvJoin left right join)
    (hstrL : ∀ x sE, left.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hstrR : ∀ x sE, right.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hlinJoin : Linearizable join) (hcohJoin : Coherent join)
    (hleftContained : ContainedBorrowsWellFormed left)
    (hrightContained : ContainedBorrowsWellFormed right) :
    ContainedBorrowsWellFormed join := by
  obtain ⟨φ, hφJoin⟩ := hlinJoin
  have hφLeft := linearizable_rankFn_of_le_shape hstrL hφJoin
  have hφRight := linearizable_rankFn_of_le_shape hstrR hφJoin
  suffices h : ∀ n, ∀ x joinSlot mutable targets, φ x = n →
      join.slotAt x = some joinSlot → join ⊢ x ↝ Ty.borrow mutable targets →
      BorrowTargetsWellFormedInSlot join joinSlot.lifetime targets by
    intro x joinSlot mutable targets hjoinSlot hcontains
    exact h (φ x) x joinSlot mutable targets rfl hjoinSlot hcontains
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro x joinSlot mutable targets hxn hjoinSlot hcontains
    have hcontN : ∀ x' slot' m' T', φ x' < n → join.slotAt x' = some slot' →
        join ⊢ x' ↝ Ty.borrow m' T' → BorrowTargetsWellFormedInSlot join slot'.lifetime T' :=
      fun x' slot' m' T' hx'n hslot' hcont' =>
        ihRank (φ x') hx'n x' slot' m' T' rfl hslot' hcont'
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hcontainedSlotEq : containedSlot = joinSlot :=
      Option.some.inj (by rw [← hcontainedSlot, hjoinSlot])
    have hcontainsJoin : PartialTyContains joinSlot.ty (.borrow mutable targets) := by
      simpa [hcontainedSlotEq] using hcontainsTy
    rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
      ⟨leftSlot, hleftSlot, _hleftLifetime⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
      ⟨rightSlot, hrightSlot, _hrightLifetime⟩
    rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
      ⟨hleftLife, hrightLife, hunion⟩
    refine BorrowTargetsWellFormedInSlot.of_partialTyUnion
      (env := join) (lifetime := joinSlot.lifetime) hunion ?_ ?_ hcontainsJoin
    · intro leftMutable leftTargets hcontainsLeft
      have hrankTargets : ∀ t, t ∈ leftTargets → φ (LVal.base t) < n := by
        intro t ht
        have hmem : LVal.base t ∈ PartialTy.vars leftSlot.ty :=
          mem_partialTy_vars_iff.mpr ⟨leftMutable, leftTargets, t, hcontainsLeft, ht, rfl⟩
        have hlt := hφLeft x leftSlot hleftSlot (LVal.base t) hmem
        omega
      have htargets :
          BorrowTargetsWellFormedInSlot join leftSlot.lifetime leftTargets :=
        BorrowTargetsWellFormedInSlot.join_viaInvariants_left hjoin hstrL hφJoin
          hcohJoin hcontN hrankTargets
          (hleftContained x leftSlot leftMutable leftTargets hleftSlot
            ⟨leftSlot, hleftSlot, hcontainsLeft⟩)
      simpa [hleftLife] using htargets
    · intro rightMutable rightTargets hcontainsRight
      have hrankTargets : ∀ t, t ∈ rightTargets → φ (LVal.base t) < n := by
        intro t ht
        have hmem : LVal.base t ∈ PartialTy.vars rightSlot.ty :=
          mem_partialTy_vars_iff.mpr ⟨rightMutable, rightTargets, t, hcontainsRight, ht, rfl⟩
        have hlt := hφRight x rightSlot hrightSlot (LVal.base t) hmem
        omega
      have htargets :
          BorrowTargetsWellFormedInSlot join rightSlot.lifetime rightTargets :=
        BorrowTargetsWellFormedInSlot.join_viaInvariants_right hjoin hstrR hφJoin
          hcohJoin hcontN hrankTargets
          (hrightContained x rightSlot rightMutable rightTargets hrightSlot
            ⟨rightSlot, hrightSlot, hcontainsRight⟩)
      simpa [hrightLife] using htargets

/--
Faithful target-list typing construction.

If every member of a non-empty target list has a full type bounded by a common
`boundTy` and a lifetime bounded by `current`, then the whole list has a
target-list typing whose union type is still bounded by `boundTy` and whose
intersection lifetime is still bounded by `current`.

This is the constructive core of borrow-target join preservation: at a
write-through-borrow join, shape compatibility supplies exactly the common
`boundTy`, so the merged target list is typeable even though the abstract union
of two target lists need not be (cf. the discussion of why the unconstrained
`partialTyUnion_preserves_borrows` is unsound).
-/
theorem LValTargetsTyping.of_members_bounded {env : Env} {boundTy : Ty}
    {current : Lifetime} :
    ∀ (targets : List LVal), targets ≠ [] →
    (∀ target, target ∈ targets →
      ∃ ty lifetime,
        LValTyping env target (.ty ty) lifetime ∧
        PartialTyStrengthens (.ty ty) (.ty boundTy) ∧
        lifetime ≤ current) →
    ∃ unionTy unionLifetime,
      LValTargetsTyping env targets (.ty unionTy) unionLifetime ∧
        PartialTyStrengthens (.ty unionTy) (.ty boundTy) ∧
        unionLifetime ≤ current := by
  intro targets
  induction targets with
  | nil => intro hne _; exact absurd rfl hne
  | cons head tail ih =>
      intro _hne hmembers
      cases tail with
      | nil =>
          rcases hmembers head (by simp) with ⟨ty, life, htyping, hle, hlife⟩
          exact ⟨ty, life, LValTargetsTyping.singleton htyping, hle, hlife⟩
      | cons t2 rest =>
          rcases hmembers head (by simp) with
            ⟨tyH, lifeH, htypingH, hleH, hlifeH⟩
          rcases ih (by simp)
              (fun target hmem => hmembers target (List.mem_cons_of_mem _ hmem)) with
            ⟨tyR, lifeR, htypingR, hleR, hlifeR⟩
          rcases partialTyUnion_exists_of_le_bound hleH hleR with ⟨tyU, hunion, hleU⟩
          rcases LifetimeIntersection.exists_of_common_inner hlifeH hlifeR with
            ⟨lifeU, hinter⟩
          exact ⟨tyU, lifeU,
            LValTargetsTyping.cons htypingH htypingR hunion hinter,
            hleU,
            LifetimeIntersection.le_of_le hinter hlifeH hlifeR⟩

/--
Combined member extraction for a target-list typing: every member has a single
typing whose type strengthens the list's union type *and* whose lifetime is
bounded by `current`.  This packages `lvalTargetsTyping_member_strengthens` and
`LValTargetsTyping.member_lifetime_outlives` into one consistent witness, which
matters because `LValTyping` is not deterministic (target lists join via
non-antisymmetric subset order).
-/
theorem lvalTargetsTyping_member_bounded {env : Env}
    {targets : List LVal} {unionTy : Ty} {lifetime current : Lifetime} :
    LValTargetsTyping env targets (.ty unionTy) lifetime →
    lifetime ≤ current →
    ∀ target, target ∈ targets →
      ∃ ty targetLifetime,
        LValTyping env target (.ty ty) targetLifetime ∧
        PartialTyStrengthens (.ty ty) (.ty unionTy) ∧
        targetLifetime ≤ current := by
  intro htargets
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun targets unionPt _lifetime _ =>
      _lifetime ≤ current →
      ∀ target, target ∈ targets →
        ∃ ty targetLifetime,
          LValTyping env target (.ty ty) targetLifetime ∧
          PartialTyStrengthens (.ty ty) unionPt ∧
          targetLifetime ≤ current)
    ?var ?box ?borrow ?singleton ?cons htargets
  · intro _x _slot _hslot; trivial
  · intro _lv _inner _lifetime _htyping _ih; trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _htyping _htargets _ihTyping _ihTargets; trivial
  · intro target ty targetLifetime htyping _ihTarget hle selected hmem
    simp at hmem
    subst hmem
    exact ⟨ty, targetLifetime, htyping, PartialTyStrengthens.reflex, hle⟩
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy'
      hhead _hrest hunion hintersection _ihHead ihRest hle selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ⟨headTy, headLifetime, hhead,
        PartialTyUnion.left_strengthens hunion,
        LifetimeOutlives.trans (LifetimeIntersection.left_le hintersection) hle⟩
    · rcases ihRest
          (LifetimeOutlives.trans (LifetimeIntersection.right_le hintersection) hle)
          selected hselected with
        ⟨ty, selectedLifetime, htyping, hstrength, hlifeBound⟩
      exact ⟨ty, selectedLifetime, htyping,
        partialTyStrengthens_trans hstrength
          (PartialTyUnion.right_strengthens hunion),
        hlifeBound⟩

/--
Lemma 9.1, Safe Strengthening.

The paper states this for full types `T₁ ⊑ T₂` and values `v`.  The
well-formedness and safe-abstraction premises are part of the paper statement;
the proof itself only needs the strengthening derivation and the existing
value/type abstraction.
-/
theorem safeStrengthening {store : ProgramStore} {env : Env}
    {lifetime : Lifetime} {left right : Ty} {value : Value} :
    WellFormedEnv env lifetime →
    store ∼ₛ env →
    PartialTyStrengthens (.ty left) (.ty right) →
    ValidValue store value left →
    ValidValue store value right := by
  intro _hwellFormed _hsafe hstrength hvalid
  cases hstrength with
  | reflex =>
      exact hvalid
  | borrow hsubset =>
      cases hvalid with
      | borrow hmem hloc =>
          exact ValidPartialValue.borrow (hsubset hmem) hloc

/--
Lemma 9.7, Value Typing.

Typing a runtime value is exactly `T-Const`, so it leaves the environment
unchanged.
-/
theorem valueTyping_environment_eq {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    TermTyping env₁ typing lifetime (.val value) ty env₂ →
    env₁ = env₂ := by
  intro htyping
  cases htyping
  rfl

/-- Value typing is functional for a fixed store typing and runtime value. -/
theorem valueTyping_deterministic {typing : StoreTyping} {value : Value}
    {left right : Ty} :
    ValueTyping typing value left →
    ValueTyping typing value right →
    left = right := by
  intro hleft hright
  cases hleft <;> cases hright
  · rfl
  · rfl
  · rename_i _ref hleftLookup hrightLookup
    rw [hleftLookup] at hrightLookup
    injection hrightLookup

/-- Lemma 9.7 lifted to singleton term lists. -/
theorem termListTyping_singleton_value_environment_eq {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    TermListTyping env₁ typing lifetime [.val value] ty env₂ →
    env₁ = env₂ := by
  intro htyping
  cases htyping with
  | singleton hterm =>
      exact valueTyping_environment_eq hterm
  | cons _hterm _hnonOwner hrest =>
      cases hrest

/-- `T-Const` inversion for singleton value term lists. -/
theorem termListTyping_singleton_value_valueTyping {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    TermListTyping env₁ typing lifetime [.val value] ty env₂ →
    ValueTyping typing value ty := by
  intro htyping
  cases htyping with
  | singleton hterm =>
      cases hterm with
      | const hvalueTyping =>
          exact hvalueTyping
  | cons _hterm _hnonOwner hrest =>
      cases hrest

/--
Block value typing consequence used by the `R-BlockB` preservation cases:
a singleton value block outputs exactly `drop(Γ, m)`.
-/
theorem blockValueTyping_output_eq {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value : Value} {ty : Ty} :
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    env' = env.dropLifetime blockLifetime := by
  intro htyping
  cases htyping with
  | block _hblockChild hterms _hwellFormed _hdropSafe hdrop =>
      have henv₂ := termListTyping_singleton_value_environment_eq hterms
      rw [henv₂]
      exact hdrop

/-- `T-Const` inversion for singleton value blocks. -/
theorem blockValueTyping_valueTyping {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value : Value} {ty : Ty} :
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    ValueTyping typing value ty := by
  intro htyping
  cases htyping with
  | block _hblockChild hterms _hwellFormed _hdropSafe _hdrop =>
      exact termListTyping_singleton_value_valueTyping hterms

/--
Lemma 9.9 support: if the store typing is valid for a terminal value and the
same value has type `T` under `σ`, then the runtime value safely abstracts `T`.
-/
theorem validStoreTyping_value {store : ProgramStore} {typing : StoreTyping}
    {value : Value} {ty : Ty} :
    ValidStoreTyping store (.val value) typing →
    ValueTyping typing value ty →
    ValidValue store value ty := by
  intro hvalidStoreTyping hvalueTyping
  rcases hvalidStoreTyping value (by simp [termValues]) with
    ⟨storedTy, hstoredTyping, hvalidValue⟩
  have hty : storedTy = ty :=
    valueTyping_deterministic hstoredTyping hvalueTyping
  subst hty
  exact hvalidValue

/-- Lemma 9.9, value case. -/
theorem valuePreservation_value {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidStoreTyping store (.val value) typing →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidValue store value ty ∧ env₂ = env := by
  intro hvalidStoreTyping htyping
  cases htyping with
  | const hvalueTyping =>
      exact ⟨validStoreTyping_value hvalidStoreTyping hvalueTyping, rfl⟩

/--
Lemma 4.11, zero-step terminal preservation.

This is the base case of Preservation for an already terminal value.
-/
theorem preservation_refl_value {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidState store (.val value) ∧ store ∼ₛ env₂ ∧ ValidValue store value ty := by
  intro hvalidState hvalidStoreTyping hsafe htyping
  rcases valuePreservation_value hvalidStoreTyping htyping with
    ⟨hvalidValue, henv⟩
  subst henv
  exact ⟨hvalidState, hsafe, hvalidValue⟩

/--
Lemma 4.11, zero-step terminal preservation for the mechanised runtime package.
-/
theorem preservation_refl_runtime_value {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidRuntimeState store (.val value) ∧ store ∼ₛ env₂ ∧
      ValidValue store value ty := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping
  rcases preservation_refl_value hvalidRuntime.1 hvalidStoreTyping hsafe htyping with
    ⟨hvalidState, hsafe₂, hvalidValue⟩
  exact ⟨⟨hvalidState,
      ValidRuntimeState.storeOwnersAllocated hvalidRuntime,
      ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime,
      ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime,
      ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime⟩,
    hsafe₂, hvalidValue⟩

/--
Lemma 4.11, multistep terminal preservation when the initial term is already a
value.  A value cannot step, so every such multistep derivation is reflexive.
-/
theorem preservation_multistep_runtime_value {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
  rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact preservation_refl_runtime_value hvalidRuntime hvalidStoreTyping hsafe htyping

/--
General value-tail composition for Lemma 4.11 proofs.

Once a proof has established preservation for a step whose result is already a
runtime value, any remaining multistep tail is necessarily reflexive.
-/
theorem preservation_value_tail_runtime {store finalStore : ProgramStore}
    {env : Env} {lifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) ∧ store ∼ₛ env ∧ ValidValue store value ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env ∧
      ValidValue finalStore finalValue ty := by
  intro hpreserved hmulti
  rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact hpreserved

/--
General one-redex-to-value multistep preservation pattern.

This factors the common proof shape for redexes such as `box v`, `let mut x = v`,
and `{v}ᵐ`: the initial term is not terminal, every first step from that redex
produces a value, and preservation for that first step composes with the
reflexive value tail.
-/
theorem preservation_multistep_of_step_to_value
    {store finalStore : ProgramStore} {lifetime : Lifetime}
    {term : Term} {finalValue : Value}
    {Result : ProgramStore → Value → Prop} :
    ¬ Terminal term →
    (∀ store' term',
      Step store lifetime term store' term' →
      ∃ value, term' = .val value) →
    (∀ store' value,
      Step store lifetime term store' (.val value) →
      Result store' value) →
    (∀ store' value finalStore finalValue,
      Result store' value →
      MultiStep store' lifetime (.val value) finalStore (.val finalValue) →
      Result finalStore finalValue) →
    MultiStep store lifetime term finalStore (.val finalValue) →
    Result finalStore finalValue := by
  intro hnotTerminal hstepValue hstepPreserve htail hmulti
  cases hmulti with
  | refl =>
      exact False.elim (hnotTerminal (value_terminal finalValue))
  | trans hstep hrest =>
      rcases hstepValue _ _ hstep with ⟨value, hterm⟩
      subst hterm
      exact htail _ _ _ _ (hstepPreserve _ _ hstep) hrest

/--
Specialized preservation combinator for redexes whose first step is already a
runtime value.

This is the common Lemma 4.11 shape after the rule-specific one-step
preservation argument has been factored out.
-/
theorem preservation_runtime_multistep_of_step_to_value
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {term : Term} {finalValue : Value} {ty : Ty} :
    ¬ Terminal term →
    (∀ store' term',
      Step store lifetime term store' term' →
      ∃ value, term' = .val value) →
    (∀ store' value,
      Step store lifetime term store' (.val value) →
      ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env ∧
        ValidValue store' value ty) →
    MultiStep store lifetime term finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env ∧
      ValidValue finalStore finalValue ty := by
  intro hnotTerminal hstepValue hstepPreserve hmulti
  exact preservation_multistep_of_step_to_value
    (Result := fun store' value =>
      ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env ∧
        ValidValue store' value ty)
    hnotTerminal hstepValue hstepPreserve
    (by
      intro _store' _value _finalStore _finalValue hpreserved htail
      exact preservation_value_tail_runtime hpreserved htail)
    hmulti

/--
Lemma 9.3, Location, factored through the part used by progress and read
preservation: a well-typed lval denotes an allocated store slot whose runtime
contents are safely abstracted by the lval's partial type.

The paper additionally writes the reached slot with the same lifetime as the
typing judgment.  Our store keeps allocation lifetimes on runtime slots, while
box contents are represented only through the `Box` type in `Γ`; the progress
and preservation arguments need the allocated slot and value abstraction below.
-/
def LValLocationAbstraction
    (store : ProgramStore) (lv : LVal) (ty : PartialTy) : Prop :=
  ∃ location slot,
    store.loc lv = some location ∧
    store.slotAt location = some slot ∧
    ValidPartialValue store slot.value ty

/--
The readable part of Lemma 9.3.  Undefined shadow types record declared but
moved-out storage; the operational `read`/`copy` premises only need a concrete
location for full and boxed partial types.
-/
def LValDefinedLocationAbstraction
    (store : ProgramStore) (lv : LVal) : PartialTy → Prop
  | .undef _ => True
  | ty => LValLocationAbstraction store lv ty

/-- Lemma 9.3, variable case. -/
theorem location_var {store : ProgramStore} {env : Env}
    {x : Name} {slot : EnvSlot} :
    store ∼ₛ env →
    env.slotAt x = some slot →
    LValLocationAbstraction store (.var x) slot.ty := by
  intro hsafe henv
  rcases hsafe.2 x slot henv with ⟨value, hstore, hvalid⟩
  exact ⟨.var x, StoreSlot.mk value slot.lifetime, by
      simp [ProgramStore.loc],
    by
      simpa [VariableProjection] using hstore,
    hvalid⟩

/-- Lemma 9.3, owned-box dereference case. -/
theorem location_box {store : ProgramStore} {lv : LVal} {inner : PartialTy} :
    LValLocationAbstraction store lv (.box inner) →
    LValLocationAbstraction store (.deref lv) inner := by
  intro hlocation
  rcases hlocation with ⟨source, sourceSlot, hloc, hslot, hvalid⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hvalid with
  | box htarget hinner =>
      exact ⟨_, _, by
          simp [ProgramStore.loc, hloc, hslot],
        htarget,
        hinner⟩

/--
Lemma 9.3, borrowed-reference dereference case.

The runtime borrowed reference identifies one member of the static target list.
That selected target has a concrete full type which strengthens the finite
union type from `T-LvBor`.
-/
theorem location_borrow_selected {store : ProgramStore} {env : Env}
    {lv : LVal} {mutable : Bool} {targets : List LVal}
    {targetTy : PartialTy} {targetLifetime : Lifetime} :
    LValLocationAbstraction store lv (.ty (.borrow mutable targets)) →
    LValTargetsTyping env targets targetTy targetLifetime →
    (∀ target ty lifetime,
      LValTyping env target (.ty ty) lifetime →
      LValLocationAbstraction store target (.ty ty)) →
    ∃ ty,
      LValLocationAbstraction store (.deref lv) (.ty ty) ∧
      PartialTyStrengthens (.ty ty) targetTy := by
  intro hborrowLocation htargets hresolve
  rcases hborrowLocation with
    ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hvalidBorrow with
  | borrow hmem htargetLocFromBorrow =>
      rcases lvalTargetsTyping_member_strengthens htargets _ hmem with
        ⟨selectedTy, selectedLifetime, hselectedTyping, hselectedStrengthens⟩
      rcases hresolve _ selectedTy selectedLifetime hselectedTyping with
        ⟨selectedLocation, selectedSlot, hselectedLoc, hselectedSlot, hselectedValid⟩
      exact ⟨selectedTy,
        ⟨selectedLocation, selectedSlot, by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            simpa [hselectedLoc] using htargetLocFromBorrow.symm,
          hselectedSlot,
          hselectedValid⟩,
        hselectedStrengthens⟩

theorem validPartialValue_full_value {store : ProgramStore}
    {partialValue : PartialValue} {ty : Ty} :
    ValidPartialValue store partialValue (.ty ty) →
    ∃ value, partialValue = .value value ∧ ValidValue store value ty := by
  intro hvalid
  cases hvalid with
  | unit =>
      exact ⟨.unit, rfl, ValidPartialValue.unit⟩
  | int =>
      exact ⟨.int _, rfl, ValidPartialValue.int⟩
  | borrow hmem hloc =>
      exact ⟨.ref { location := _, owner := false }, rfl,
        ValidPartialValue.borrow hmem hloc⟩
  | boxFull hslot hinner =>
      exact ⟨.ref { location := _, owner := true }, rfl,
        ValidPartialValue.boxFull hslot hinner⟩

/--
Lemma 9.3, Location.

This packages the variable, owned-box, and borrowed-reference cases into one
recursive theorem over `LValTyping`.  Undefined shadow types are intentionally
excluded from the concrete-location conclusion, since they are not readable
runtime values.
-/
theorem lvalTyping_defined_location {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv ty lifetime →
    LValDefinedLocationAbstraction store lv ty := by
  intro hwellFormed hsafe htyping
  refine LValTyping.rec
    (motive_1 := fun lv ty _ _ => LValDefinedLocationAbstraction store lv ty)
    (motive_2 := fun targets unionTy _ _ =>
      ∀ target,
        target ∈ targets →
        ∃ ty,
          LValLocationAbstraction store target (.ty ty) ∧
          PartialTyStrengthens (.ty ty) unionTy)
    ?var ?box ?borrow ?singleton ?cons htyping
  · intro x slot hslot
    rcases slot with ⟨slotTy, slotLifetime⟩
    cases slotTy <;> simp [LValDefinedLocationAbstraction]
    · exact location_var (store := store) (env := env) hsafe hslot
    · exact location_var (store := store) (env := env) hsafe hslot
  · intro _lv inner _lifetime _htyping ih
    cases inner <;> simp [LValDefinedLocationAbstraction]
    · exact location_box ih
    · exact location_box ih
  · intro lv mutable targets _borrowLifetime _targetLifetime targetTy
      _hborrow _htargets ihBorrow ihTargets
    cases targetTy with
    | ty finalTy =>
        simp [LValDefinedLocationAbstraction]
        rcases ihBorrow with
          ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hvalidBorrow with
        | borrow hmem htargetLocFromBorrow =>
            rcases ihTargets _ hmem with
              ⟨selectedTy, hselectedLocation, hstrength⟩
            rcases hselectedLocation with
              ⟨selectedLocation, selectedSlot, hselectedLoc,
                hselectedSlot, hselectedValid⟩
            rcases validPartialValue_full_value hselectedValid with
              ⟨selectedValue, hselectedValue, hvalidSelectedValue⟩
            exact ⟨selectedLocation, selectedSlot, by
                simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                simpa [hselectedLoc] using htargetLocFromBorrow.symm,
              hselectedSlot,
              by
                simpa [hselectedValue, ValidValue] using
                  safeStrengthening hwellFormed hsafe hstrength hvalidSelectedValue⟩
    | box _inner =>
        rcases ihBorrow with
          ⟨source, sourceSlot, _hsourceLoc, _hsourceSlot, hvalidBorrow⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hvalidBorrow with
        | borrow hmem _htargetLocFromBorrow =>
            rcases ihTargets _ hmem with
              ⟨selectedTy, _hselectedLocation, hstrength⟩
            cases hstrength
    | undef _shape =>
        simp [LValDefinedLocationAbstraction]
  · intro target ty _lifetime _htarget ihTarget selected hmem
    simp at hmem
    subst hmem
    exact ⟨ty, ihTarget, PartialTyStrengthens.reflex⟩
  · intro target rest headTy _headLifetime _restLifetime _lifetime _restTy unionTy
      _hhead _hrest hunion _hintersection ihHead ihRest selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ⟨headTy, ihHead, PartialTyUnion.left_strengthens hunion⟩
    · rcases ihRest selected hselected with
        ⟨selectedTy, hlocation, hstrength⟩
      exact ⟨selectedTy, hlocation,
        partialTyStrengthens_trans hstrength
          (PartialTyUnion.right_strengthens hunion)⟩

/-- A well-typed lval denotes allocated storage, even when its type is undefined. -/
def LValAllocatedLocation (store : ProgramStore) (lv : LVal) : Prop :=
  ∃ location slot, store.loc lv = some location ∧ store.slotAt location = some slot

theorem lvalTyping_allocated_location {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv ty lifetime →
    LValAllocatedLocation store lv := by
  intro hwellFormed hsafe htyping
  refine LValTyping.rec
    (motive_1 := fun lv _ _ _ => LValAllocatedLocation store lv)
    (motive_2 := fun targets _ _ _ =>
      ∀ target, target ∈ targets → LValAllocatedLocation store target)
    ?var ?box ?borrow ?singleton ?cons htyping
  · intro x slot hslot
    rcases location_var (store := store) (env := env) hsafe hslot with
      ⟨location, runtimeSlot, hloc, hslotRuntime, _hvalid⟩
    exact ⟨location, runtimeSlot, hloc, hslotRuntime⟩
  · intro _lv _inner _lifetime hbox _ih
    rcases location_box (lvalTyping_defined_location hwellFormed hsafe hbox) with
      ⟨location, slot, hloc, hslot, _hvalid⟩
    exact ⟨location, slot, hloc, hslot⟩
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      hborrow _htargets _ihBorrow ihTargets
    rcases lvalTyping_defined_location hwellFormed hsafe hborrow with
      ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
    rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
    cases hvalidBorrow with
    | borrow hmem htargetLocFromBorrow =>
        rcases ihTargets _ hmem with
          ⟨targetLocation, targetSlot, htargetLoc, htargetSlot⟩
        exact ⟨targetLocation, targetSlot, by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            simpa [htargetLoc] using htargetLocFromBorrow.symm,
          htargetSlot⟩
  · intro _target _ty _lifetime _htarget ihTarget selected hmem
    simp at hmem
    subst hmem
    exact ihTarget
  · intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
      _hhead _hrest _hunion _hintersection ihHead ihRest selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ihHead
    · exact ihRest selected hselected

theorem lvalTyping_read_nonOwner_of_shapeCompatible {store : ProgramStore} {env : Env}
    {current valueLifetime : Lifetime} {lv : LVal} {oldTy : PartialTy}
    {rhsTy : Ty} {oldSlot : StoreSlot} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv oldTy valueLifetime →
    NonOwnerTy rhsTy →
    ShapeCompatible env oldTy (.ty rhsTy) →
    store.read lv = some oldSlot →
    PartialValueNonOwner oldSlot.value := by
  intro hwellFormed hsafe htyping hnonOwner hshape hread
  have hshapeOld := partialTy_nonOwnerShape_of_shapeCompatible_right_ty hnonOwner hshape
  cases htyping with
  | var henvSlot =>
      exact safeAbstraction_var_read_nonOwner_of_envShape hsafe henvSlot hread hshapeOld
  | box hinner =>
      rename_i sourceLv
      have hboxLocation :
          LValLocationAbstraction store sourceLv (.box oldTy) :=
        lvalTyping_defined_location hwellFormed hsafe hinner
      rcases location_box hboxLocation with
        ⟨location, slot, hloc, hslot, hvalid⟩
      have hreadSlot :
          store.read (.deref sourceLv) = some slot := by
        simp [ProgramStore.read, hloc, hslot]
      rw [hread] at hreadSlot
      injection hreadSlot with hslotEq
      cases hslotEq
      exact validPartialValue_nonOwner_of_envShape hvalid hshapeOld
  | borrow hborrow htargets =>
      rename_i sourceLv mutable targets _borrowLifetime
      have hborrowLocation :=
        lvalTyping_defined_location hwellFormed hsafe hborrow
      have htargetsLocation :
          ∀ target ty lifetime,
            LValTyping env target (.ty ty) lifetime →
            LValLocationAbstraction store target (.ty ty) := by
        intro target ty lifetime htarget
        exact lvalTyping_defined_location hwellFormed hsafe htarget
      rcases location_borrow_selected hborrowLocation htargets htargetsLocation with
        ⟨selectedTy, hselectedLocation, hstrength⟩
      rcases hselectedLocation with
        ⟨location, slot, hloc, hslot, hvalid⟩
      have hreadSlot :
          store.read (.deref sourceLv) = some slot := by
        simp [ProgramStore.read, hloc, hslot]
      rw [hread] at hreadSlot
      injection hreadSlot with hslotEq
      cases hslotEq
      have hselectedShape :
          selectedTy = .unit ∨ selectedTy = .int ∨
            ∃ mutable targets, selectedTy = .borrow mutable targets :=
        ty_nonOwnerShape_of_strengthens_shapeCompatible_right_ty hnonOwner hstrength hshape
      rcases hselectedShape with hunit | hint | hborrowShape
      · subst hunit
        exact validPartialValue_nonOwner_of_envShape hvalid (Or.inl rfl)
      · subst hint
        exact validPartialValue_nonOwner_of_envShape hvalid (Or.inr (Or.inl rfl))
      · rcases hborrowShape with ⟨mutable, targets, hborrowTy⟩
        subst hborrowTy
        exact validPartialValue_nonOwner_of_envShape hvalid
          (Or.inr (Or.inr (Or.inr ⟨mutable, targets, rfl⟩)))

/-- Lemma 9.3 operational corollary: locating an lval makes `read` defined. -/
theorem read_defined_of_location {store : ProgramStore} {lv : LVal} {ty : PartialTy} :
    LValLocationAbstraction store lv ty →
    ∃ slot, store.read lv = some slot := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot, _hvalid⟩
  exact ⟨slot, by
    simp [ProgramStore.read, hloc, hslot]⟩

/-- Lemma 9.3 operational corollary: locating an lval makes `write` defined. -/
theorem write_defined_of_location {store : ProgramStore} {lv : LVal}
    {ty : PartialTy} {value : PartialValue} :
    LValLocationAbstraction store lv ty →
    ∃ store', store.write lv value = some store' := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot, _hvalid⟩
  exact ⟨store.update location { slot with value := value }, by
    simp [ProgramStore.write, hloc, hslot]⟩

/-- A successful runtime write updates exactly the location selected by `loc`. -/
theorem write_eq_update_of_read {store store' : ProgramStore}
    {lv : LVal} {oldSlot : StoreSlot} {value : PartialValue} :
    store.read lv = some oldSlot →
    store.write lv value = some store' →
    ∃ location,
      store.loc lv = some location ∧
        store.slotAt location = some oldSlot ∧
        store' = store.update location { oldSlot with value := value } := by
  intro hread hwrite
  unfold ProgramStore.read at hread
  unfold ProgramStore.write at hwrite
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hread
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hread
      | some runtimeSlot =>
          have holdSlot : oldSlot = runtimeSlot := by
            simpa [hloc, hslot] using hread.symm
          have hstore' :
              store' =
                store.update location { runtimeSlot with value := value } := by
            simpa [hloc, hslot] using hwrite.symm
          subst holdSlot
          subst hstore'
          refine ⟨location, ?_, ?_, rfl⟩
          · rfl
          · exact hslot

theorem read_defined_of_allocated {store : ProgramStore} {lv : LVal} :
    LValAllocatedLocation store lv →
    ∃ slot, store.read lv = some slot := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot⟩
  exact ⟨slot, by simp [ProgramStore.read, hloc, hslot]⟩

theorem allocated_of_read {store : ProgramStore} {lv : LVal} {slot : StoreSlot} :
    store.read lv = some slot →
    LValAllocatedLocation store lv := by
  intro hread
  unfold ProgramStore.read at hread
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hread
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hread
      | some runtimeSlot =>
          simp [hloc, hslot] at hread
          subst hread
          exact ⟨location, runtimeSlot, hloc, hslot⟩

theorem write_defined_of_allocated {store : ProgramStore} {lv : LVal}
    {value : PartialValue} :
    LValAllocatedLocation store lv →
    ∃ store', store.write lv value = some store' := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot⟩
  exact ⟨store.update location { slot with value := value }, by
    simp [ProgramStore.write, hloc, hslot]⟩

/-- Corollary 9.4, Read Preservation, from an established location witness. -/
theorem readPreservation_of_location {store : ProgramStore} {lv : LVal} {ty : Ty} :
    LValLocationAbstraction store lv (.ty ty) →
    ∃ value slot,
      store.read lv = some slot ∧
      slot.value = .value value ∧
      ValidValue store value ty := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot, hvalid⟩
  rcases validPartialValue_full_value hvalid with ⟨value, hvalue, hvalidValue⟩
  exact ⟨value, slot, by
      simp [ProgramStore.read, hloc, hslot],
    hvalue,
    hvalidValue⟩

/-- Corollary 9.4, Read Preservation. -/
theorem readPreservation {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) lifetime →
    ∃ value slot,
      store.read lv = some slot ∧
      slot.value = .value value ∧
      ValidValue store value ty := by
  intro hwellFormed hsafe htyping
  exact readPreservation_of_location
    (lvalTyping_defined_location hwellFormed hsafe htyping)

/-- Corollary 9.4, variable case. -/
theorem readPreservation_var {store : ProgramStore} {env : Env}
    {x : Name} {slot : EnvSlot} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    ∃ value runtimeSlot,
      store.read (.var x) = some runtimeSlot ∧
      runtimeSlot.value = .value value ∧
      ValidValue store value ty := by
  intro hsafe henv hty
  exact readPreservation_of_location (by
    simpa [hty] using location_var (store := store) (env := env) hsafe henv)

/-- Corollary 9.4, owned-box dereference case. -/
theorem readPreservation_box {store : ProgramStore} {lv : LVal} {ty : Ty} :
    LValLocationAbstraction store lv (.box (.ty ty)) →
    ∃ value runtimeSlot,
      store.read (.deref lv) = some runtimeSlot ∧
      runtimeSlot.value = .value value ∧
      ValidValue store value ty := by
  intro hlocation
  exact readPreservation_of_location (location_box hlocation)

/-- Corollary 9.4, borrowed-reference dereference case. -/
theorem readPreservation_borrow {store : ProgramStore} {env : Env}
    {lifetime : Lifetime} {lv : LVal} {mutable : Bool} {targets : List LVal}
    {targetTy : Ty} {targetLifetime : Lifetime} :
    WellFormedEnv env lifetime →
    store ∼ₛ env →
    LValLocationAbstraction store lv (.ty (.borrow mutable targets)) →
    LValTargetsTyping env targets (.ty targetTy) targetLifetime →
    (∀ target ty targetLifetime,
      LValTyping env target (.ty ty) targetLifetime →
      LValLocationAbstraction store target (.ty ty)) →
    ∃ value slot,
      store.read (.deref lv) = some slot ∧
      slot.value = .value value ∧
      ValidValue store value targetTy := by
  intro hwellFormed hsafe hborrowLocation htargets hresolve
  rcases location_borrow_selected hborrowLocation htargets hresolve with
    ⟨selectedTy, hselectedLocation, hstrength⟩
  rcases readPreservation_of_location hselectedLocation with
    ⟨value, slot, hread, hslotValue, hvalidSelected⟩
  exact ⟨value, slot, hread, hslotValue,
    safeStrengthening hwellFormed hsafe hstrength hvalidSelected⟩


end Paper
end LwRust
