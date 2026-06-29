import LwRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Preservation facts for relaxed control-flow joins

This file isolates the preservation-side part of the relaxed `T-If` question.
The terminal branch-to-join transport does not require `BorrowSafeEnv` for the
joined environment.  Runtime safety can instead be stated with an exact
branch-local environment that strengthens to the joined approximation.
-/

namespace LwRust
namespace Paper

open Core

/--
Runtime safety against an approximate typing environment.  The current store is
safe against some exact environment, and that exact environment has the same
shape while strengthening to the approximation.
-/
def RuntimeExactEnvWitness (store : ProgramStore) (lifetime : Lifetime)
    (approxEnv : Env) : Prop :=
  ∃ exactEnv,
    WellFormedEnv exactEnv lifetime ∧
      BorrowSafeEnv exactEnv ∧
      store ∼ₛ exactEnv ∧
      EnvSameShapeStrengthening exactEnv approxEnv

/-- The exact witness always induces ordinary safe abstraction for the
approximate environment. -/
theorem RuntimeExactEnvWitness.safe {store : ProgramStore} {lifetime : Lifetime}
    {approxEnv : Env} :
    RuntimeExactEnvWitness store lifetime approxEnv →
    store ∼ₛ approxEnv := by
  intro hwitness
  rcases hwitness with
    ⟨exactEnv, _hwellExact, _hborrowExact, hsafeExact, hmap⟩
  exact hmap.safe hsafeExact

theorem RuntimeExactEnvWitness.of_store_eq {store finalStore : ProgramStore}
    {lifetime : Lifetime} {approxEnv : Env} :
    finalStore = store →
    RuntimeExactEnvWitness store lifetime approxEnv →
    RuntimeExactEnvWitness finalStore lifetime approxEnv := by
  intro hstore hwitness
  subst hstore
  exact hwitness

theorem RuntimeExactEnvWitness.weaken {store : ProgramStore}
    {outer inner : Lifetime} {approxEnv : Env} :
    RuntimeExactEnvWitness store outer approxEnv →
    outer ≤ inner →
    RuntimeExactEnvWitness store inner approxEnv := by
  intro hwitness houtlives
  rcases hwitness with
    ⟨exactEnv, hwellExact, hborrowExact, hsafeExact, hmapExactApprox⟩
  exact ⟨exactEnv, WellFormedEnv.weaken hwellExact houtlives,
    hborrowExact, hsafeExact, hmapExactApprox⟩

/--
Heap allocation for `box` preserves the exact runtime witness.  The environment
does not change; only a fresh heap location is added to the store.
-/
theorem RuntimeExactEnvWitness.box_redex {store store' : ProgramStore}
    {lifetime : Lifetime} {approxEnv : Env} {value finalValue : Value} :
    RuntimeExactEnvWitness store lifetime approxEnv →
    Step store lifetime (.box (.val value)) store' (.val finalValue) →
    RuntimeExactEnvWitness store' lifetime approxEnv := by
  intro hwitness hstep
  rcases hwitness with
    ⟨exactEnv, hwellExact, hborrowExact, hsafeExact, hmapExactApprox⟩
  cases hstep with
  | box hfresh hbox =>
      cases hbox
      exact ⟨exactEnv, hwellExact, hborrowExact,
        safeAbstraction_boxAt hfresh hsafeExact, hmapExactApprox⟩

/--
Terminal `copy` runs do not change the store.  This lets the exact runtime
witness thread through the redex unchanged.
-/
theorem multistep_copy_to_value_store_eq {store finalStore : ProgramStore}
    {lifetime : Lifetime} {lv : LVal} {finalValue : Value} :
    MultiStep store lifetime (.copy lv) finalStore (.val finalValue) →
    finalStore = store := by
  intro hmulti
  cases hmulti with
  | trans hstep hrest =>
      cases hstep with
      | copy _hread =>
          rcases multistep_value_inv hrest with ⟨hstore, _hterm⟩
          exact hstore

/--
Terminal `borrow` runs do not change the store.  This is the borrow-redex
counterpart of `multistep_copy_to_value_store_eq`.
-/
theorem multistep_borrow_to_value_store_eq {store finalStore : ProgramStore}
    {lifetime : Lifetime} {mutable : Bool} {lv : LVal} {finalValue : Value} :
    MultiStep store lifetime (.borrow mutable lv) finalStore (.val finalValue) →
    finalStore = store := by
  intro hmulti
  cases hmulti with
  | trans hstep hrest =>
      cases hstep with
      | borrow _hloc =>
          rcases multistep_value_inv hrest with ⟨hstore, _hterm⟩
          exact hstore

/--
Strengthening has the same slot domain on both sides.  The order only weakens
partial types; it cannot introduce or remove environment roots.
-/
theorem EnvStrengthens.slot_backward {left right : Env} {x : Name}
    {rightSlot : EnvSlot} :
    EnvStrengthens left right →
    right.slotAt x = some rightSlot →
    ∃ leftSlot,
      left.slotAt x = some leftSlot ∧
        leftSlot.lifetime = rightSlot.lifetime ∧
        PartialTyStrengthens leftSlot.ty rightSlot.ty := by
  intro hstrength hright
  have h := hstrength x
  rw [hright] at h
  cases hleft : left.slotAt x with
  | none =>
      rw [hleft] at h
      exact False.elim h
  | some leftSlot =>
      rw [hleft] at h
      exact ⟨leftSlot, rfl, h.1, h.2⟩

theorem EnvStrengthens.slot_domain_iff {left right : Env} {x : Name} :
    EnvStrengthens left right →
    ((∃ leftSlot, left.slotAt x = some leftSlot) ↔
      ∃ rightSlot, right.slotAt x = some rightSlot) := by
  intro hstrength
  constructor
  · rintro ⟨leftSlot, hleftSlot⟩
    rcases EnvStrengthens.slot_forward hstrength hleftSlot with
      ⟨rightSlot, hrightSlot, _hlife, _hstrengthTy⟩
    exact ⟨rightSlot, hrightSlot⟩
  · rintro ⟨rightSlot, hrightSlot⟩
    rcases EnvStrengthens.slot_backward hstrength hrightSlot with
      ⟨leftSlot, hleftSlot, _hlife, _hstrengthTy⟩
    exact ⟨leftSlot, hleftSlot⟩

/--
An environment join has exactly the same root domain as each branch.

Together with `EnvJoinSameShape`, this is the static shape half of the relaxed
`if` story: joins may weaken slot types, but they do not leak branch-local roots
or drop roots that remain live on either branch.
-/
theorem EnvJoin.left_slot_domain_iff {left right join : Env} {x : Name} :
    EnvJoin left right join →
    ((∃ leftSlot, left.slotAt x = some leftSlot) ↔
      ∃ joinSlot, join.slotAt x = some joinSlot) := by
  intro hjoin
  exact EnvStrengthens.slot_domain_iff (EnvJoin.left_le hjoin)

theorem EnvJoin.right_slot_domain_iff {left right join : Env} {x : Name} :
    EnvJoin left right join →
    ((∃ rightSlot, right.slotAt x = some rightSlot) ↔
      ∃ joinSlot, join.slotAt x = some joinSlot) := by
  intro hjoin
  exact EnvStrengthens.slot_domain_iff (EnvJoin.right_le hjoin)

theorem EnvJoin.branch_slot_domain_iff {left right join : Env} {x : Name} :
    EnvJoin left right join →
    ((∃ leftSlot, left.slotAt x = some leftSlot) ↔
      ∃ rightSlot, right.slotAt x = some rightSlot) := by
  intro hjoin
  exact (EnvJoin.left_slot_domain_iff hjoin).trans
    (EnvJoin.right_slot_domain_iff hjoin).symm

theorem Env.dropLifetime_slot_lifetime_ne {env : Env} {x : Name}
    {slot : EnvSlot} {lifetime : Lifetime} :
    (env.dropLifetime lifetime).slotAt x = some slot →
    slot.lifetime ≠ lifetime := by
  intro hslot heq
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with
    ⟨_horig, hnotDropped⟩
  exact hnotDropped heq

theorem EnvSameShapeStrengthening.dropLifetime {source result : Env}
    {lifetime : Lifetime} :
    EnvSameShapeStrengthening source result →
    EnvSameShapeStrengthening (source.dropLifetime lifetime)
      (result.dropLifetime lifetime) := by
  intro hmap
  constructor
  · intro x resultSlot hresultSlot
    rcases Env.dropLifetime_slotAt_eq_some.mp hresultSlot with
      ⟨hresultSlotOrig, hresultLifetime⟩
    rcases hmap.1 x resultSlot hresultSlotOrig with
      ⟨sourceSlot, hsourceSlot, hlifetime, hstrength, hshape⟩
    exact ⟨sourceSlot,
      Env.dropLifetime_slotAt_eq_some.mpr
        ⟨hsourceSlot, by simpa [hlifetime] using hresultLifetime⟩,
      hlifetime, hstrength, hshape⟩
  · intro x sourceSlot hsourceSlot
    rcases Env.dropLifetime_slotAt_eq_some.mp hsourceSlot with
      ⟨hsourceSlotOrig, hsourceLifetime⟩
    rcases hmap.2 x sourceSlot hsourceSlotOrig with
      ⟨resultSlot, hresultSlot, hlifetime⟩
    exact ⟨resultSlot,
      Env.dropLifetime_slotAt_eq_some.mpr
        ⟨hresultSlot, by simpa [← hlifetime] using hsourceLifetime⟩,
      hlifetime⟩

theorem RuntimeExactEnvWitness.refl {store : ProgramStore} {lifetime : Lifetime}
    {env : Env} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    RuntimeExactEnvWitness store lifetime env := by
  intro hwell hborrow hsafe
  exact ⟨env, hwell, hborrow, hsafe, EnvSameShapeStrengthening.refl env⟩

theorem RuntimeExactEnvWitness.strengthen {store : ProgramStore}
    {lifetime : Lifetime} {source result : Env} :
    RuntimeExactEnvWitness store lifetime source →
    EnvSameShapeStrengthening source result →
    RuntimeExactEnvWitness store lifetime result := by
  intro hwitness hmapSourceResult
  rcases hwitness with
    ⟨exactEnv, hwellExact, hborrowExact, hsafeExact, hmapExactSource⟩
  exact ⟨exactEnv, hwellExact, hborrowExact, hsafeExact,
    EnvSameShapeStrengthening.trans hmapExactSource hmapSourceResult⟩

/--
Updating the same live slot on both sides with the same full type preserves the
exact-to-approximate same-shape strengthening map.

This is the small bridge needed after a branch-selected runtime target has been
identified: the exact branch environment and the joined approximation may differ
elsewhere, but replacing the selected slot's type by the assigned RHS type keeps
the selected exact update stronger than the selected approximate update.
-/
theorem EnvSameShapeStrengthening.update_both_same_ty {source result : Env}
    {x : Name} {sourceSlot resultSlot : EnvSlot} {rhsTy : Ty} :
    EnvSameShapeStrengthening source result →
    source.slotAt x = some sourceSlot →
    result.slotAt x = some resultSlot →
    EnvSameShapeStrengthening
      (source.update x { sourceSlot with ty := .ty rhsTy })
      (result.update x { resultSlot with ty := .ty rhsTy }) := by
  intro hmap hsourceSlot hresultSlot
  rcases hmap.1 x resultSlot hresultSlot with
    ⟨sourceSlotMapped, hsourceSlotMapped, hlifetime, _hstrength, _hshape⟩
  have hsourceSlotEq : sourceSlotMapped = sourceSlot :=
    Option.some.inj (hsourceSlotMapped.symm.trans hsourceSlot)
  subst hsourceSlotEq
  constructor
  · intro y updatedResultSlot hupdatedResultSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedResultSlot = { resultSlot with ty := .ty rhsTy } := by
        simpa [Env.update] using hupdatedResultSlot.symm
      subst hslotEq
      exact ⟨{ sourceSlotMapped with ty := .ty rhsTy },
        by simp [Env.update],
        by simpa using hlifetime,
        PartialTyStrengthens.reflex,
        PartialTy.sameShape_refl _⟩
    · have hresultOld : result.slotAt y = some updatedResultSlot := by
        simpa [Env.update, hy] using hupdatedResultSlot
      rcases hmap.1 y updatedResultSlot hresultOld with
        ⟨sourceOldSlot, hsourceOldSlot, hlifeOld, hstrengthOld, hshapeOld⟩
      exact ⟨sourceOldSlot,
        by simpa [Env.update, hy] using hsourceOldSlot,
        hlifeOld, hstrengthOld, hshapeOld⟩
  · intro y updatedSourceSlot hupdatedSourceSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedSourceSlot = { sourceSlotMapped with ty := .ty rhsTy } := by
        simpa [Env.update] using hupdatedSourceSlot.symm
      subst hslotEq
      exact ⟨{ resultSlot with ty := .ty rhsTy },
        by simp [Env.update],
        by simpa using hlifetime⟩
    · have hsourceOld : source.slotAt y = some updatedSourceSlot := by
        simpa [Env.update, hy] using hupdatedSourceSlot
      rcases hmap.2 y updatedSourceSlot hsourceOld with
        ⟨resultOldSlot, hresultOldSlot, hlifeOld⟩
      exact ⟨resultOldSlot,
        by simpa [Env.update, hy] using hresultOldSlot,
        hlifeOld⟩

/--
Updating the same live slot on both sides with strengthening full types
preserves exact-to-approximate same-shape strengthening.
-/
theorem EnvSameShapeStrengthening.update_both_ty_strengthening
    {source result : Env} {x : Name} {sourceSlot resultSlot : EnvSlot}
    {sourceTy resultTy : Ty} :
    EnvSameShapeStrengthening source result →
    source.slotAt x = some sourceSlot →
    result.slotAt x = some resultSlot →
    PartialTyStrengthens (.ty sourceTy) (.ty resultTy) →
    EnvSameShapeStrengthening
      (source.update x { sourceSlot with ty := .ty sourceTy })
      (result.update x { resultSlot with ty := .ty resultTy }) := by
  intro hmap hsourceSlot hresultSlot hstrengthTy
  rcases hmap.1 x resultSlot hresultSlot with
    ⟨sourceSlotMapped, hsourceSlotMapped, hlifetime, _hstrength, _hshape⟩
  have hsourceSlotEq : sourceSlotMapped = sourceSlot :=
    Option.some.inj (hsourceSlotMapped.symm.trans hsourceSlot)
  subst hsourceSlotEq
  constructor
  · intro y updatedResultSlot hupdatedResultSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedResultSlot = { resultSlot with ty := .ty resultTy } := by
        simpa [Env.update] using hupdatedResultSlot.symm
      subst hslotEq
      exact ⟨{ sourceSlotMapped with ty := .ty sourceTy },
        by simp [Env.update],
        by simpa using hlifetime,
        hstrengthTy,
        by
          simpa [PartialTy.sameShape] using
            ty_sameShape_of_strengthens hstrengthTy⟩
    · have hresultOld : result.slotAt y = some updatedResultSlot := by
        simpa [Env.update, hy] using hupdatedResultSlot
      rcases hmap.1 y updatedResultSlot hresultOld with
        ⟨sourceOldSlot, hsourceOldSlot, hlifeOld, hstrengthOld, hshapeOld⟩
      exact ⟨sourceOldSlot,
        by simpa [Env.update, hy] using hsourceOldSlot,
        hlifeOld, hstrengthOld, hshapeOld⟩
  · intro y updatedSourceSlot hupdatedSourceSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedSourceSlot = { sourceSlotMapped with ty := .ty sourceTy } := by
        simpa [Env.update] using hupdatedSourceSlot.symm
      subst hslotEq
      exact ⟨{ resultSlot with ty := .ty resultTy },
        by simp [Env.update],
        by simpa using hlifetime⟩
    · have hsourceOld : source.slotAt y = some updatedSourceSlot := by
        simpa [Env.update, hy] using hupdatedSourceSlot
      rcases hmap.2 y updatedSourceSlot hsourceOld with
        ⟨resultOldSlot, hresultOldSlot, hlifeOld⟩
      exact ⟨resultOldSlot,
        by simpa [Env.update, hy] using hresultOldSlot,
        hlifeOld⟩

/--
Updating the same live slot on both sides to related `undef` full types
preserves exact-to-approximate same-shape strengthening.

This is the variable-move analogue of `update_both_same_ty`: after both
environments strike the same variable slot, the exact struck type remains
stronger than the approximate struck type.
-/
theorem EnvSameShapeStrengthening.update_both_undef_ty {source result : Env}
    {x : Name} {sourceSlot resultSlot : EnvSlot}
    {sourceTy resultTy : Ty} :
    EnvSameShapeStrengthening source result →
    source.slotAt x = some sourceSlot →
    result.slotAt x = some resultSlot →
    PartialTyStrengthens (.ty sourceTy) (.ty resultTy) →
    EnvSameShapeStrengthening
      (source.update x { sourceSlot with ty := .undef sourceTy })
      (result.update x { resultSlot with ty := .undef resultTy }) := by
  intro hmap hsourceSlot hresultSlot hstrengthTy
  rcases hmap.1 x resultSlot hresultSlot with
    ⟨sourceSlotMapped, hsourceSlotMapped, hlifetime, _hstrength, _hshape⟩
  have hsourceSlotEq : sourceSlotMapped = sourceSlot :=
    Option.some.inj (hsourceSlotMapped.symm.trans hsourceSlot)
  subst hsourceSlotEq
  constructor
  · intro y updatedResultSlot hupdatedResultSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedResultSlot = { resultSlot with ty := .undef resultTy } := by
        simpa [Env.update] using hupdatedResultSlot.symm
      subst hslotEq
      exact ⟨{ sourceSlotMapped with ty := .undef sourceTy },
        by simp [Env.update],
        by simpa using hlifetime,
        PartialTyStrengthens.undefLeft hstrengthTy,
        by
          simpa [PartialTy.sameShape] using
            ty_sameShape_of_strengthens hstrengthTy⟩
    · have hresultOld : result.slotAt y = some updatedResultSlot := by
        simpa [Env.update, hy] using hupdatedResultSlot
      rcases hmap.1 y updatedResultSlot hresultOld with
        ⟨sourceOldSlot, hsourceOldSlot, hlifeOld, hstrengthOld, hshapeOld⟩
      exact ⟨sourceOldSlot,
        by simpa [Env.update, hy] using hsourceOldSlot,
        hlifeOld, hstrengthOld, hshapeOld⟩
  · intro y updatedSourceSlot hupdatedSourceSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedSourceSlot = { sourceSlotMapped with ty := .undef sourceTy } := by
        simpa [Env.update] using hupdatedSourceSlot.symm
      subst hslotEq
      exact ⟨{ resultSlot with ty := .undef resultTy },
        by simp [Env.update],
        by simpa using hlifetime⟩
    · have hsourceOld : source.slotAt y = some updatedSourceSlot := by
        simpa [Env.update, hy] using hupdatedSourceSlot
      rcases hmap.2 y updatedSourceSlot hsourceOld with
        ⟨resultOldSlot, hresultSlotOld, hlifeOld⟩
      exact ⟨resultOldSlot,
        by simpa [Env.update, hy] using hresultSlotOld,
        hlifeOld⟩

/--
Adding the same fresh full-typed slot to both sides preserves the
exact-to-approximate same-shape strengthening map.

This is the declaration analogue of `update_both_same_ty`: after a relaxed
control-flow join, a continuation may add a fresh local to the joined
approximation, while the runtime path adds it to the selected exact
environment.
-/
theorem EnvSameShapeStrengthening.update_both_fresh_same_ty
    {source result : Env} {x : Name} {newSlot : EnvSlot} :
    EnvSameShapeStrengthening source result →
    source.fresh x →
    result.fresh x →
    EnvSameShapeStrengthening (source.update x newSlot)
      (result.update x newSlot) := by
  intro hmap hsourceFresh hresultFresh
  constructor
  · intro y mappedResultSlot hmappedResultSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq : newSlot = mappedResultSlot := by
        simpa [Env.update] using hmappedResultSlot
      subst mappedResultSlot
      exact ⟨newSlot, by simp [Env.update],
        rfl, PartialTyStrengthens.reflex, PartialTy.sameShape_refl _⟩
    · have hresultOld : result.slotAt y = some mappedResultSlot := by
        simpa [Env.update, hy] using hmappedResultSlot
      rcases hmap.1 y mappedResultSlot hresultOld with
        ⟨sourceSlot, hsourceSlot, hlife, hstrength, hshape⟩
      exact ⟨sourceSlot, by simpa [Env.update, hy] using hsourceSlot,
        hlife, hstrength, hshape⟩
  · intro y mappedSourceSlot hmappedSourceSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq : newSlot = mappedSourceSlot := by
        simpa [Env.update] using hmappedSourceSlot
      subst mappedSourceSlot
      exact ⟨newSlot, by simp [Env.update], rfl⟩
    · have hsourceOld : source.slotAt y = some mappedSourceSlot := by
        simpa [Env.update, hy] using hmappedSourceSlot
      rcases hmap.2 y mappedSourceSlot hsourceOld with
        ⟨resultSlot, hresultSlot, hlife⟩
      exact ⟨resultSlot, by simpa [Env.update, hy] using hresultSlot,
        hlife⟩

/--
Adding fresh slots with related full types preserves exact-to-approximate
same-shape strengthening.

This is the declaration analogue needed after a relaxed branch returns a
stricter exact value type that only strengthens to the joined approximation.
-/
theorem EnvSameShapeStrengthening.update_both_fresh_ty_strengthening
    {source result : Env} {x : Name} {lifetime : Lifetime}
    {sourceTy resultTy : Ty} :
    EnvSameShapeStrengthening source result →
    source.fresh x →
    result.fresh x →
    PartialTyStrengthens (.ty sourceTy) (.ty resultTy) →
    EnvSameShapeStrengthening
      (source.update x { ty := .ty sourceTy, lifetime := lifetime })
      (result.update x { ty := .ty resultTy, lifetime := lifetime }) := by
  intro hmap hsourceFresh hresultFresh hstrengthTy
  constructor
  · intro y mappedResultSlot hmappedResultSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          mappedResultSlot = { ty := .ty resultTy, lifetime := lifetime } := by
        simpa [Env.update] using hmappedResultSlot.symm
      subst hslotEq
      exact ⟨{ ty := .ty sourceTy, lifetime := lifetime },
        by simp [Env.update],
        rfl,
        hstrengthTy,
        by
          simpa [PartialTy.sameShape] using
            ty_sameShape_of_strengthens hstrengthTy⟩
    · have hresultOld : result.slotAt y = some mappedResultSlot := by
        simpa [Env.update, hy] using hmappedResultSlot
      rcases hmap.1 y mappedResultSlot hresultOld with
        ⟨sourceSlot, hsourceSlot, hlife, hstrength, hshape⟩
      exact ⟨sourceSlot, by simpa [Env.update, hy] using hsourceSlot,
        hlife, hstrength, hshape⟩
  · intro y mappedSourceSlot hmappedSourceSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          mappedSourceSlot = { ty := .ty sourceTy, lifetime := lifetime } := by
        simpa [Env.update] using hmappedSourceSlot.symm
      subst hslotEq
      exact ⟨{ ty := .ty resultTy, lifetime := lifetime },
        by simp [Env.update], rfl⟩
    · have hsourceOld : source.slotAt y = some mappedSourceSlot := by
        simpa [Env.update, hy] using hmappedSourceSlot
      rcases hmap.2 y mappedSourceSlot hsourceOld with
        ⟨resultSlot, hresultSlot, hlife⟩
      exact ⟨resultSlot, by simpa [Env.update, hy] using hresultSlot,
        hlife⟩

/--
If a name is fresh in the approximate/result environment, it is fresh in any
exact/source environment that same-shape strengthens to it.
-/
theorem EnvSameShapeStrengthening.source_fresh_of_result_fresh
    {source result : Env} {x : Name} :
    EnvSameShapeStrengthening source result →
    result.fresh x →
    source.fresh x := by
  intro hmap hresultFresh
  unfold Env.fresh at hresultFresh ⊢
  cases hsource : source.slotAt x with
  | none => rfl
  | some sourceSlot =>
      rcases hmap.2 x sourceSlot hsource with
        ⟨resultSlot, hresultSlot, _hlife⟩
      rw [hresultFresh] at hresultSlot
      cases hresultSlot

/--
Replacing the same strong owner leaf in two same-shaped partial types preserves
the strengthening and same-shape relation between them.
-/
theorem PartialTy.strongLeafUpdate_transport_sameShapeStrengthening
    {source result : PartialTy} {path : List Unit} {rhsTy : Ty} :
    PartialTyStrengthens source result →
    PartialTy.sameShape source result →
    PartialTyStrengthens
        (PartialTy.strongLeafUpdate source path rhsTy)
        (PartialTy.strongLeafUpdate result path rhsTy) ∧
      PartialTy.sameShape
        (PartialTy.strongLeafUpdate source path rhsTy)
        (PartialTy.strongLeafUpdate result path rhsTy) := by
  intro hstrength hshape
  induction path generalizing source result with
  | nil =>
      exact ⟨by simp [PartialTy.strongLeafUpdate],
        by
          simpa [PartialTy.strongLeafUpdate] using
            PartialTy.sameShape_refl (PartialTy.ty rhsTy)⟩
  | cons _ path ih =>
      cases source with
      | ty sourceTy =>
          cases result <;>
            simp [PartialTy.strongLeafUpdate, PartialTy.sameShape] at hshape ⊢
          exact ⟨hstrength, hshape⟩
      | box sourceInner =>
          cases result with
          | ty resultTy =>
              simp [PartialTy.sameShape] at hshape
          | box resultInner =>
              simp [PartialTy.strongLeafUpdate, PartialTy.sameShape] at hshape ⊢
              rcases ih (PartialTyStrengthens.box_inv hstrength) hshape with
                ⟨hstrengthInner, hshapeInner⟩
              exact ⟨PartialTyStrengthens.box hstrengthInner, hshapeInner⟩
          | undef resultTy =>
              simp [PartialTy.sameShape] at hshape
      | undef sourceTy =>
          cases result <;>
            simp [PartialTy.strongLeafUpdate, PartialTy.sameShape] at hshape ⊢
          exact ⟨hstrength, hshape⟩

/--
Strong leaf replacement is monotone in both the owner type and the replacement
RHS type.
-/
theorem PartialTy.strongLeafUpdate_transport_ty_strengthening
    {source result : PartialTy} {path : List Unit}
    {exactRhsTy approxRhsTy : Ty} :
    PartialTyStrengthens source result →
    PartialTy.sameShape source result →
    PartialTyStrengthens (.ty exactRhsTy) (.ty approxRhsTy) →
    PartialTyStrengthens
        (PartialTy.strongLeafUpdate source path exactRhsTy)
        (PartialTy.strongLeafUpdate result path approxRhsTy) ∧
      PartialTy.sameShape
        (PartialTy.strongLeafUpdate source path exactRhsTy)
        (PartialTy.strongLeafUpdate result path approxRhsTy) := by
  intro hstrength hshape hRhsStrength
  induction path generalizing source result with
  | nil =>
      exact ⟨by simpa [PartialTy.strongLeafUpdate] using hRhsStrength,
        by
          simpa [PartialTy.strongLeafUpdate, PartialTy.sameShape] using
            ty_sameShape_of_strengthens hRhsStrength⟩
  | cons _ path ih =>
      cases source with
      | ty sourceTy =>
          cases result <;>
            simp [PartialTy.strongLeafUpdate, PartialTy.sameShape] at hshape ⊢
          exact ⟨hstrength, hshape⟩
      | box sourceInner =>
          cases result with
          | ty resultTy =>
              simp [PartialTy.sameShape] at hshape
          | box resultInner =>
              simp [PartialTy.strongLeafUpdate, PartialTy.sameShape] at hshape ⊢
              rcases ih (PartialTyStrengthens.box_inv hstrength) hshape with
                ⟨hstrengthInner, hshapeInner⟩
              exact ⟨PartialTyStrengthens.box hstrengthInner, hshapeInner⟩
          | undef resultTy =>
              simp [PartialTy.sameShape] at hshape
      | undef sourceTy =>
          cases result <;>
            simp [PartialTy.strongLeafUpdate, PartialTy.sameShape] at hshape ⊢
          exact ⟨hstrength, hshape⟩

/--
Updating the same owner root on both sides with the same strong leaf
replacement preserves exact-to-approximate same-shape strengthening.
-/
theorem EnvSameShapeStrengthening.update_both_strongLeafUpdate
    {source result : Env} {x : Name} {sourceSlot resultSlot : EnvSlot}
    {path : List Unit} {rhsTy : Ty} :
    EnvSameShapeStrengthening source result →
    source.slotAt x = some sourceSlot →
    result.slotAt x = some resultSlot →
    EnvSameShapeStrengthening
      (source.update x
        { sourceSlot with
            ty := PartialTy.strongLeafUpdate sourceSlot.ty path rhsTy })
      (result.update x
        { resultSlot with
            ty := PartialTy.strongLeafUpdate resultSlot.ty path rhsTy }) := by
  intro hmap hsourceSlot hresultSlot
  rcases hmap.1 x resultSlot hresultSlot with
    ⟨sourceSlotMapped, hsourceSlotMapped, hlifetime, hstrength, hshape⟩
  have hsourceSlotEq : sourceSlotMapped = sourceSlot :=
    Option.some.inj (hsourceSlotMapped.symm.trans hsourceSlot)
  subst hsourceSlotEq
  rcases PartialTy.strongLeafUpdate_transport_sameShapeStrengthening
      hstrength hshape with
    ⟨hupdatedStrength, hupdatedShape⟩
  constructor
  · intro y updatedResultSlot hupdatedResultSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedResultSlot =
            { resultSlot with
              ty := PartialTy.strongLeafUpdate resultSlot.ty path rhsTy } := by
        simpa [Env.update] using hupdatedResultSlot.symm
      subst hslotEq
      exact ⟨
        { sourceSlotMapped with
            ty := PartialTy.strongLeafUpdate sourceSlotMapped.ty path rhsTy },
        by simp [Env.update],
        by simpa using hlifetime,
        hupdatedStrength,
        hupdatedShape⟩
    · have hresultOld : result.slotAt y = some updatedResultSlot := by
        simpa [Env.update, hy] using hupdatedResultSlot
      rcases hmap.1 y updatedResultSlot hresultOld with
        ⟨sourceOldSlot, hsourceOldSlot, hlifeOld, hstrengthOld, hshapeOld⟩
      exact ⟨sourceOldSlot,
        by simpa [Env.update, hy] using hsourceOldSlot,
        hlifeOld, hstrengthOld, hshapeOld⟩
  · intro y updatedSourceSlot hupdatedSourceSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedSourceSlot =
            { sourceSlotMapped with
              ty := PartialTy.strongLeafUpdate sourceSlotMapped.ty path rhsTy } := by
        simpa [Env.update] using hupdatedSourceSlot.symm
      subst hslotEq
      exact ⟨
        { resultSlot with
            ty := PartialTy.strongLeafUpdate resultSlot.ty path rhsTy },
        by simp [Env.update],
        by simpa using hlifetime⟩
    · have hsourceOld : source.slotAt y = some updatedSourceSlot := by
        simpa [Env.update, hy] using hupdatedSourceSlot
      rcases hmap.2 y updatedSourceSlot hsourceOld with
        ⟨resultOldSlot, hresultOldSlot, hlifeOld⟩
      exact ⟨resultOldSlot,
        by simpa [Env.update, hy] using hresultOldSlot,
        hlifeOld⟩

/--
Typed variant of `EnvSameShapeStrengthening.update_both_strongLeafUpdate`.
The exact selected owner root may be updated with a stronger RHS type than the
approximate owner root.
-/
theorem EnvSameShapeStrengthening.update_both_strongLeafUpdate_ty_strengthening
    {source result : Env} {x : Name} {sourceSlot resultSlot : EnvSlot}
    {path : List Unit} {exactRhsTy approxRhsTy : Ty} :
    EnvSameShapeStrengthening source result →
    source.slotAt x = some sourceSlot →
    result.slotAt x = some resultSlot →
    PartialTyStrengthens (.ty exactRhsTy) (.ty approxRhsTy) →
    EnvSameShapeStrengthening
      (source.update x
        { sourceSlot with
            ty := PartialTy.strongLeafUpdate sourceSlot.ty path exactRhsTy })
      (result.update x
        { resultSlot with
            ty := PartialTy.strongLeafUpdate resultSlot.ty path
              approxRhsTy }) := by
  intro hmap hsourceSlot hresultSlot hRhsStrength
  rcases hmap.1 x resultSlot hresultSlot with
    ⟨sourceSlotMapped, hsourceSlotMapped, hlifetime, hstrength, hshape⟩
  have hsourceSlotEq : sourceSlotMapped = sourceSlot :=
    Option.some.inj (hsourceSlotMapped.symm.trans hsourceSlot)
  subst hsourceSlotEq
  rcases PartialTy.strongLeafUpdate_transport_ty_strengthening
      hstrength hshape hRhsStrength with
    ⟨hupdatedStrength, hupdatedShape⟩
  constructor
  · intro y updatedResultSlot hupdatedResultSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedResultSlot =
            { resultSlot with
              ty := PartialTy.strongLeafUpdate resultSlot.ty path
                approxRhsTy } := by
        simpa [Env.update] using hupdatedResultSlot.symm
      subst hslotEq
      exact ⟨
        { sourceSlotMapped with
            ty := PartialTy.strongLeafUpdate sourceSlotMapped.ty path
              exactRhsTy },
        by simp [Env.update],
        by simpa using hlifetime,
        hupdatedStrength,
        hupdatedShape⟩
    · have hresultOld : result.slotAt y = some updatedResultSlot := by
        simpa [Env.update, hy] using hupdatedResultSlot
      rcases hmap.1 y updatedResultSlot hresultOld with
        ⟨sourceOldSlot, hsourceOldSlot, hlifeOld, hstrengthOld, hshapeOld⟩
      exact ⟨sourceOldSlot,
        by simpa [Env.update, hy] using hsourceOldSlot,
        hlifeOld, hstrengthOld, hshapeOld⟩
  · intro y updatedSourceSlot hupdatedSourceSlot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          updatedSourceSlot =
            { sourceSlotMapped with
              ty := PartialTy.strongLeafUpdate sourceSlotMapped.ty path
                exactRhsTy } := by
        simpa [Env.update] using hupdatedSourceSlot.symm
      subst hslotEq
      exact ⟨
        { resultSlot with
            ty := PartialTy.strongLeafUpdate resultSlot.ty path
              approxRhsTy },
        by simp [Env.update],
        by simpa using hlifetime⟩
    · have hsourceOld : source.slotAt y = some updatedSourceSlot := by
        simpa [Env.update, hy] using hupdatedSourceSlot
      rcases hmap.2 y updatedSourceSlot hsourceOld with
        ⟨resultOldSlot, hresultOldSlot, hlifeOld⟩
      exact ⟨resultOldSlot,
        by simpa [Env.update, hy] using hresultOldSlot,
        hlifeOld⟩

/--
A contained borrow in the exact/source environment is present in the
approximate/result environment with at least the same target list.
-/
theorem EnvSameShapeStrengthening.contains_forward {source result : Env}
    {x : Name} {mutable : Bool} {targets : List LVal} :
    EnvSameShapeStrengthening source result →
    source ⊢ x ↝ Ty.borrow mutable targets →
    ∃ targets',
      result ⊢ x ↝ Ty.borrow mutable targets' ∧ targets ⊆ targets' := by
  intro hmap hcontains
  rcases hcontains with ⟨sourceSlot, hsourceSlot, hcontainsSource⟩
  rcases hmap.2 x sourceSlot hsourceSlot with
    ⟨resultSlot, hresultSlot, _hlifetime⟩
  rcases hmap.1 x resultSlot hresultSlot with
    ⟨sourceSlotMapped, hsourceSlotMapped, _hlife, hstrength, hshape⟩
  have hsourceSlotEq : sourceSlotMapped = sourceSlot :=
    Option.some.inj (hsourceSlotMapped.symm.trans hsourceSlot)
  subst hsourceSlotEq
  rcases PartialTyContains.mono_strengthens_sameShape hcontainsSource
      hstrength hshape with
    ⟨targets', hcontainsResult, hsubset⟩
  exact ⟨targets', ⟨resultSlot, hresultSlot, hcontainsResult⟩, hsubset⟩

theorem LinearizedBy.of_sameShapeStrengthening {source result : Env}
    {φ : Name → Nat} :
    EnvSameShapeStrengthening source result →
    LinearizedBy φ result →
    LinearizedBy φ source := by
  intro hmap hlinear x sourceSlot hsourceSlot v hv
  rcases hmap.2 x sourceSlot hsourceSlot with
    ⟨resultSlot, hresultSlot, _hlife⟩
  rcases hmap.1 x resultSlot hresultSlot with
    ⟨sourceSlotMapped, hsourceSlotMapped, _hlife', hstrength, hshape⟩
  have hsourceSlotEq : sourceSlotMapped = sourceSlot :=
    Option.some.inj (hsourceSlotMapped.symm.trans hsourceSlot)
  subst hsourceSlotEq
  exact hlinear x resultSlot hresultSlot v
    (partialTy_vars_mono hstrength hshape v hv)

/--
The RHS rank side condition transports from an approximate output back to an
exact output that strengthens to it.
-/
theorem EnvWriteRhsBorrowTargetsBelow.of_sameShapeStrengthening
    {source result : Env} {φ : Name → Nat} {rhsTy : Ty} :
    EnvSameShapeStrengthening source result →
    EnvWriteRhsBorrowTargetsBelow φ result rhsTy →
    EnvWriteRhsBorrowTargetsBelow φ source rhsTy := by
  intro hmap hbelow
  constructor
  · intro x slot mutable targets target hslot hcontains htarget hrhs
    rcases EnvSameShapeStrengthening.contains_forward hmap
        ⟨slot, hslot, hcontains⟩ with
      ⟨targets', hcontainsResult, hsubset⟩
    rcases hcontainsResult with
      ⟨resultSlot, hresultSlot, hcontainsResultTy⟩
    exact hbelow.1 x resultSlot mutable targets' target hresultSlot
      hcontainsResultTy (hsubset htarget) hrhs
  · intro x y mutable targetsMutable targetsOther targetMutable targetOther
      hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
      hrhsMutable hrhsOther
    rcases EnvSameShapeStrengthening.contains_forward hmap
        hcontainsMutable with
      ⟨targetsMutable', hcontainsMutableResult, hsubsetMutable⟩
    rcases EnvSameShapeStrengthening.contains_forward hmap
        hcontainsOther with
      ⟨targetsOther', hcontainsOtherResult, hsubsetOther⟩
    exact hbelow.2 x y mutable targetsMutable' targetsOther'
      targetMutable targetOther hcontainsMutableResult hcontainsOtherResult
      (hsubsetMutable htargetMutable) (hsubsetOther htargetOther)
      hconflict hrhsMutable hrhsOther

/--
The RHS rank side condition is monotone in the RHS type: if the exact RHS type
strengthens to the approximate RHS type, every exact RHS borrow target is also
an approximate RHS borrow target.
-/
theorem EnvWriteRhsBorrowTargetsBelow.of_rhs_strengthening
    {φ : Name → Nat} {env : Env} {exactTy approxTy : Ty} :
    PartialTyStrengthens (.ty exactTy) (.ty approxTy) →
    EnvWriteRhsBorrowTargetsBelow φ env approxTy →
    EnvWriteRhsBorrowTargetsBelow φ env exactTy := by
  intro hstrength hbelow
  have hshape : PartialTy.sameShape (.ty exactTy) (.ty approxTy) := by
    simpa [PartialTy.sameShape] using ty_sameShape_of_strengthens hstrength
  constructor
  · intro x slot mutable targets target hslot hcontains htarget hrhs
    rcases hrhs with ⟨rhsMutable, rhsTargets, hcontainsRhs, htargetRhs⟩
    rcases PartialTyContains.mono_strengthens_sameShape
        hcontainsRhs hstrength hshape with
      ⟨rhsTargetsApprox, hcontainsApprox, hsubsetApprox⟩
    exact hbelow.1 x slot mutable targets target hslot hcontains htarget
      ⟨rhsMutable, rhsTargetsApprox, hcontainsApprox,
        hsubsetApprox htargetRhs⟩
  · intro x y mutable targetsMutable targetsOther targetMutable targetOther
      hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
      hrhsMutable hrhsOther
    rcases hrhsMutable with
      ⟨rhsMutableA, rhsTargetsA, hcontainsRhsA, htargetRhsA⟩
    rcases hrhsOther with
      ⟨rhsMutableB, rhsTargetsB, hcontainsRhsB, htargetRhsB⟩
    rcases PartialTyContains.mono_strengthens_sameShape
        hcontainsRhsA hstrength hshape with
      ⟨rhsTargetsApproxA, hcontainsApproxA, hsubsetApproxA⟩
    rcases PartialTyContains.mono_strengthens_sameShape
        hcontainsRhsB hstrength hshape with
      ⟨rhsTargetsApproxB, hcontainsApproxB, hsubsetApproxB⟩
    exact hbelow.2 x y mutable targetsMutable targetsOther targetMutable
      targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther
      hconflict
      ⟨rhsMutableA, rhsTargetsApproxA, hcontainsApproxA,
        hsubsetApproxA htargetRhsA⟩
      ⟨rhsMutableB, rhsTargetsApproxB, hcontainsApproxB,
        hsubsetApproxB htargetRhsB⟩

/--
The RHS target well-formedness side condition is also monotone in the RHS type.
-/
theorem EnvWriteRhsTargetsWellFormed.of_rhs_strengthening
    {env : Env} {exactTy approxTy : Ty} :
    PartialTyStrengthens (.ty exactTy) (.ty approxTy) →
    EnvWriteRhsTargetsWellFormed env approxTy →
    EnvWriteRhsTargetsWellFormed env exactTy := by
  intro hstrength htargets
  have hshape : PartialTy.sameShape (.ty exactTy) (.ty approxTy) := by
    simpa [PartialTy.sameShape] using ty_sameShape_of_strengthens hstrength
  intro x slot mutable targets target hslot hcontains htarget hrhs
  rcases hrhs with ⟨rhsMutable, rhsTargets, hcontainsRhs, htargetRhs⟩
  rcases PartialTyContains.mono_strengthens_sameShape
      hcontainsRhs hstrength hshape with
    ⟨rhsTargetsApprox, hcontainsApprox, hsubsetApprox⟩
  exact htargets x slot mutable targets target hslot hcontains htarget
    ⟨rhsMutable, rhsTargetsApprox, hcontainsApprox,
      hsubsetApprox htargetRhs⟩

theorem ReadProhibited.of_sameShapeStrengthening {source result : Env}
    {lv : LVal} :
    EnvSameShapeStrengthening source result →
    ReadProhibited source lv →
    ReadProhibited result lv := by
  intro hmap hread
  rcases hread with
    ⟨x, targets, target, hcontains, htarget, hconflict⟩
  rcases EnvSameShapeStrengthening.contains_forward hmap hcontains with
    ⟨targets', hcontainsResult, hsubset⟩
  exact ⟨x, targets', target, hcontainsResult, hsubset htarget, hconflict⟩

theorem WriteProhibited.of_sameShapeStrengthening {source result : Env}
    {lv : LVal} :
    EnvSameShapeStrengthening source result →
    WriteProhibited source lv →
    WriteProhibited result lv := by
  intro hmap hwrite
  cases hwrite with
  | inl hread =>
      exact Or.inl (ReadProhibited.of_sameShapeStrengthening hmap hread)
  | inr himm =>
      rcases himm with
        ⟨x, targets, target, hcontains, htarget, hconflict⟩
      rcases EnvSameShapeStrengthening.contains_forward hmap hcontains with
        ⟨targets', hcontainsResult, hsubset⟩
      exact Or.inr
        ⟨x, targets', target, hcontainsResult, hsubset htarget, hconflict⟩

/--
RHS type borrow-safety transports from the joined approximation back to the
exact selected environment.

This is the direction needed for continuation code after a relaxed `if`: if the
tail typing proves the RHS type is safe against the joined approximation, it is
also safe against the exact branch environment that strengthens to it.
-/
theorem TyBorrowSafeAgainstEnv.of_sameShapeStrengthening
    {source result : Env} {ty : Ty} :
    EnvSameShapeStrengthening source result →
    TyBorrowSafeAgainstEnv result ty →
    TyBorrowSafeAgainstEnv source ty := by
  intro hmap hsafe
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther
      hcontainsTy hcontainsSource htargetMutable htargetOther hconflict
    rcases EnvSameShapeStrengthening.contains_forward hmap hcontainsSource with
      ⟨targetsOther', hcontainsResult, hsubsetOther⟩
    exact hsafe.1 targetsMutable mutable targetsOther' x targetMutable
      targetOther hcontainsTy hcontainsResult htargetMutable
      (hsubsetOther htargetOther) hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsSource hcontainsTy htargetMutable htargetOther hconflict
    rcases EnvSameShapeStrengthening.contains_forward hmap hcontainsSource with
      ⟨targetsMutable', hcontainsResult, hsubsetMutable⟩
    exact hsafe.2 x targetsMutable' mutable targetsOther targetMutable
      targetOther hcontainsResult hcontainsTy
      (hsubsetMutable htargetMutable) htargetOther hconflict

/--
An exact selected environment can be updated with an RHS type using RHS-safety
proved against the joined approximation.  The result is borrow-safe without
requiring `BorrowSafeEnv` for the approximation itself.
-/
theorem BorrowSafeEnv.update_of_approx_tyBorrowSafe {source result : Env}
    {x : Name} {slot : EnvSlot} {ty : Ty} :
    EnvSameShapeStrengthening source result →
    BorrowSafeEnv source →
    TyBorrowSafeAgainstEnv result ty →
    source.slotAt x = some slot →
    BorrowSafeEnv (source.update x { slot with ty := .ty ty }) := by
  intro hmap hborrow hsafeTyApprox _hslot
  have hsafeTySource :
      TyBorrowSafeAgainstEnv source ty :=
    TyBorrowSafeAgainstEnv.of_sameShapeStrengthening hmap hsafeTyApprox
  simpa using
    (borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv
      (x := x) (lifetime := slot.lifetime) hborrow hsafeTySource)

/--
Every borrow target appearing after a strong owner-leaf replacement comes either
from the old owner-root type or from the RHS type installed at the leaf.
-/
theorem PartialTy.strongLeafUpdate_borrowTargetOrigin
    {oldTy : PartialTy} {path : List Unit} {rhsTy : Ty}
    {mutable : Bool} {targets : List LVal} {target : LVal} :
    PartialTyContains (PartialTy.strongLeafUpdate oldTy path rhsTy)
      (.borrow mutable targets) →
    target ∈ targets →
    TypeBorrowOrigin oldTy rhsTy mutable target := by
  induction path generalizing oldTy targets target with
  | nil =>
      intro hcontains htarget
      exact Or.inr ⟨targets, by simpa [PartialTy.strongLeafUpdate] using hcontains,
        htarget⟩
  | cons _ path ih =>
      intro hcontains htarget
      cases oldTy with
      | ty ty =>
          exact Or.inl ⟨targets,
            by simpa [PartialTy.strongLeafUpdate] using hcontains,
            htarget⟩
      | undef ty =>
          exact Or.inl ⟨targets,
            by simpa [PartialTy.strongLeafUpdate] using hcontains,
            htarget⟩
      | box inner =>
          have hinner :
              PartialTyContains
                (PartialTy.strongLeafUpdate inner path rhsTy)
                (.borrow mutable targets) := by
            cases hcontains with
            | box hinner => exact hinner
          rcases ih hinner htarget with hfromOld | hfromRhs
          · rcases hfromOld with ⟨oldTargets, hcontainsOld, hmemOld⟩
            exact Or.inl
              ⟨oldTargets, PartialTyContains.box hcontainsOld, hmemOld⟩
          · exact Or.inr hfromRhs

/--
Nested strong owner-root updates preserve borrow safety when the RHS type is
borrow-safe against an approximation of the exact input.

This is the strong-leaf analogue of
`BorrowSafeEnv.update_of_approx_tyBorrowSafe`.  It is the local invariant needed
for selected heap-location writes after a relaxed control-flow join.
-/
theorem BorrowSafeEnv.update_strongLeafUpdate_of_approx_tyBorrowSafe
    {source result : Env} {x : Name} {slot : EnvSlot}
    {path : List Unit} {ty : Ty} :
    EnvSameShapeStrengthening source result →
    BorrowSafeEnv source →
    TyBorrowSafeAgainstEnv result ty →
    source.slotAt x = some slot →
    BorrowSafeEnv
      (source.update x
        { slot with ty := PartialTy.strongLeafUpdate slot.ty path ty }) := by
  intro hmap hborrow hsafeTyApprox hslot
  have hsafeTySource :
      TyBorrowSafeAgainstEnv source ty :=
    TyBorrowSafeAgainstEnv.of_sameShapeStrengthening hmap hsafeTyApprox
  intro y z mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hy : y = x
  · subst y
    by_cases hz : z = x
    · subst z
      rfl
    · have hcontainsMutableAtX :
          (source.update x
            { slot with ty := PartialTy.strongLeafUpdate slot.ty path ty }) ⊢
            x ↝ Ty.borrow true targetsMutable := by
        simpa using hcontainsMutable
      rcases hcontainsMutableAtX with
        ⟨updatedSlot, hupdatedSlot, hcontainsUpdated⟩
      have hupdatedSlotEq :
          updatedSlot =
            { slot with ty := PartialTy.strongLeafUpdate slot.ty path ty } := by
        simpa [Env.update] using hupdatedSlot.symm
      subst hupdatedSlotEq
      have hcontainsOtherSource : source ⊢ z ↝ Ty.borrow mutable targetsOther :=
        EnvContains.update_fresh_ne hz hcontainsOther
      rcases PartialTy.strongLeafUpdate_borrowTargetOrigin
          hcontainsUpdated htargetMutable with hfromOld | hfromRhs
      · rcases hfromOld with ⟨oldTargets, hcontainsOld, htargetOld⟩
        exact hborrow x z mutable oldTargets targetsOther targetMutable
          targetOther ⟨slot, hslot, hcontainsOld⟩ hcontainsOtherSource
          htargetOld htargetOther hconflict
      · rcases hfromRhs with ⟨rhsTargets, hcontainsRhs, htargetRhs⟩
        exact False.elim
          (hsafeTySource.1 rhsTargets mutable targetsOther z
            targetMutable targetOther hcontainsRhs hcontainsOtherSource
            htargetRhs htargetOther hconflict)
  · by_cases hz : z = x
    · subst z
      have hcontainsMutableSource :
          source ⊢ y ↝ Ty.borrow true targetsMutable :=
        EnvContains.update_fresh_ne hy hcontainsMutable
      have hcontainsOtherAtX :
          (source.update x
            { slot with ty := PartialTy.strongLeafUpdate slot.ty path ty }) ⊢
            x ↝ Ty.borrow mutable targetsOther := by
        simpa using hcontainsOther
      rcases hcontainsOtherAtX with
        ⟨updatedSlot, hupdatedSlot, hcontainsUpdated⟩
      have hupdatedSlotEq :
          updatedSlot =
            { slot with ty := PartialTy.strongLeafUpdate slot.ty path ty } := by
        simpa [Env.update] using hupdatedSlot.symm
      subst hupdatedSlotEq
      rcases PartialTy.strongLeafUpdate_borrowTargetOrigin
          hcontainsUpdated htargetOther with hfromOld | hfromRhs
      · rcases hfromOld with ⟨oldTargets, hcontainsOld, htargetOld⟩
        exact hborrow y x mutable targetsMutable oldTargets targetMutable
          targetOther hcontainsMutableSource ⟨slot, hslot, hcontainsOld⟩
          htargetMutable htargetOld hconflict
      · rcases hfromRhs with ⟨rhsTargets, hcontainsRhs, htargetRhs⟩
        exact False.elim
          (hsafeTySource.2 y targetsMutable mutable rhsTargets
            targetMutable targetOther hcontainsMutableSource hcontainsRhs
            htargetMutable htargetRhs hconflict)
    · exact hborrow y z mutable targetsMutable targetsOther targetMutable
        targetOther
        (EnvContains.update_fresh_ne hy hcontainsMutable)
        (EnvContains.update_fresh_ne hz hcontainsOther)
        htargetMutable htargetOther hconflict

/--
Reverse root-survival transport across an exact-to-approximate same-shape map.

This is the easy part of reversing well-formedness through a joined
approximation: root slots do not appear or disappear.  The hard part is not base
survival, but reconstructing full `LValTyping` through dereferences whose borrow
target lists may have grown at the join.
-/
theorem LValBaseOutlives.reverse_sameShapeStrengthening
    {source result : Env} {lv : LVal} {lifetime : Lifetime} :
    EnvSameShapeStrengthening source result →
    LValBaseOutlives result lv lifetime →
    LValBaseOutlives source lv lifetime := by
  intro hmap hbase
  rcases hbase with ⟨resultSlot, hresultSlot, houtlives⟩
  rcases hmap.1 (LVal.base lv) resultSlot hresultSlot with
    ⟨sourceSlot, hsourceSlot, hlifetime, _hstrength, _hshape⟩
  exact ⟨sourceSlot, hsourceSlot, by simpa [hlifetime] using houtlives⟩

/--
Variable lvalues also reverse cleanly across an exact-to-approximate same-shape
map.  This isolates the remaining reverse transport difficulty to dereference
typing, especially the `T-LvBor` case where join weakening can widen target
lists.
-/
theorem LValTyping.var_reverse_sameShapeStrengthening
    {source result : Env} {x : Name} {resultTy : PartialTy}
    {lifetime : Lifetime} :
    EnvSameShapeStrengthening source result →
    LValTyping result (.var x) resultTy lifetime →
    ∃ sourceTy,
      LValTyping source (.var x) sourceTy lifetime ∧
        PartialTyStrengthens sourceTy resultTy ∧
        PartialTy.sameShape sourceTy resultTy := by
  intro hmap htyping
  cases htyping with
  | var hresultSlot =>
      rcases hmap.1 x _ hresultSlot with
        ⟨sourceSlot, hsourceSlot, hlifetime, hstrength, hshape⟩
      refine ⟨sourceSlot.ty, ?_, hstrength, hshape⟩
      simpa [hlifetime] using (LValTyping.var hsourceSlot)

/--
Per-target borrow well-formedness transports forward across a same-shape
strengthening, provided the result environment is well formed.  This is the
direction used when an exact selected branch is strengthened to the joined
approximation.
-/
theorem BorrowTargetsWellFormed.transport_sameShapeStrengthening
    {source result : Env} {targets : List LVal}
    {lifetime current : Lifetime} :
    EnvSameShapeStrengthening source result →
    WellFormedEnv result current →
    BorrowTargetsWellFormed source targets lifetime →
    BorrowTargetsWellFormed result targets lifetime := by
  intro hmap hwellResult htargets
  have hdecomp :
      ∀ z zslot m W, result.slotAt z = some zslot →
        PartialTyContains zslot.ty (.borrow m W) →
        ∀ w, w ∈ W → ∃ wbs, result.slotAt (LVal.base w) = some wbs ∧
          wbs.lifetime ≤ zslot.lifetime := by
    intro z zslot m W hz hcontains w hw
    rcases hwellResult.1 z zslot m W hz
        ⟨zslot, hz, hcontains⟩ w hw with
      ⟨_targetTy, _targetLifetime, _htyping, _htargetOutlives, hbase⟩
    exact hbase
  have hslot :
      BorrowTargetsWellFormedInSlot result lifetime targets :=
    borrowTargetsWellFormedInSlot_transport hmap hwellResult.2.2.1
      hwellResult.2.2.2 hdecomp rfl (by
        intro target htarget
        exact BorrowTargetsWellFormed.member htargets target htarget)
  exact BorrowTargetsWellFormed.intro hslot

/--
Full type well-formedness transports forward across a same-shape strengthening.
This is useful for exact outputs that are later viewed through a joined
approximation.
-/
theorem WellFormedTy.transport_sameShapeStrengthening
    {source result : Env} {ty : Ty} {lifetime current : Lifetime} :
    EnvSameShapeStrengthening source result →
    WellFormedEnv result current →
    WellFormedTy source ty lifetime →
    WellFormedTy result ty lifetime := by
  intro hmap hwellResult hwellTy
  induction hwellTy with
  | unit => exact WellFormedTy.unit
  | int => exact WellFormedTy.int
  | bool => exact WellFormedTy.bool
  | borrow htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.transport_sameShapeStrengthening
          hmap hwellResult htargets)
  | box _hinner ih =>
      exact WellFormedTy.box ih


end Paper
end LwRust
