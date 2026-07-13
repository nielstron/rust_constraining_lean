import FWRust.Paper.Soundness.Lemma_4_11_Preservation

/-!
# Lemma 9.5 (Drop Preservation)

> Let `S` be a program store; let `Γ` be a well-formed typing environment with
> respect to a lifetime `l` where `S ∼ Γ`.  Then `drop(S, l) ∼ drop(Γ, l)`.

The unqualified printed statement is false for the unrestricted abstract-store
encoding: an owning reference stored in a child-lifetime variable may point to
an outer variable, so recursively dropping the child also erases the outer
variable that `Env.dropLifetime` retains.  The closed witness
`lemma_9_5_unqualified_counterexample` records this obstruction, but it is not
a valid runtime state because its owner targets a variable.  The store-only
`R-BlockB` form is `lemma_9_5_dropPreservation_of_store_invariants`; its
runtime-state corollary is `lemma_9_5_dropPreservation_of_validRuntimeState`.
The still more general store-effect wrapper is
`lemma_9_5_dropPreservation_of_store_effects`.

Recursive drops are otherwise framed by explicit reachability/disjointness
facts from the runtime validity package:

* `dropsLifetime_validStore`, `drops_validStore` — dropping preserves store
  validity;
* `dropsLifetime_storeOwnersAllocated`, `drops_storeOwnersAllocated_of_disjoint`
  — owner-allocation is preserved under the lifetime-disjointness side condition;
* `preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop` — the
  recursive lifetime-drop preservation used by Preservation for terminal value
  blocks;
* `safeAbstraction_seq_value_drop` — safe-abstraction preservation for
  recursive drops of non-final sequence temporaries;
* `lemma_9_5_value_drops_frame` — recursive value drops preserve a value
  abstraction when the drop avoids every reached location.
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

/--
Lemma 9.5 with the two concrete store effects that the abstract relational
`DropsLifetime` judgment does not by itself imply.  These premises say exactly
that the post-drop variable domain agrees with `Env.dropLifetime` and every
surviving variable keeps a valid abstraction.
-/
theorem lemma_9_5_dropPreservation_of_store_effects
    {store' : ProgramStore} {env : Env} {lifetime : Lifetime}
    (hdomain : ∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot)
    (hpreserve : ∀ x envSlot,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ lifetime →
      ∃ value,
        store'.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } ∧
        ValidPartialValue store' value envSlot.ty) :
    store' ≈ₛ env.dropLifetime lifetime :=
  safeAbstraction_dropLifetime_of_preserved hdomain hpreserve

/--
Lemma 9.5 from exactly the store-level representation invariants used by the
runtime proof and the lifetime dropped by `R-BlockB`.

Heap origin and root lifetime exclude an owning reference from a child-lifetime
slot to a surviving variable slot.  Thus the domain and survivor premises of
`lemma_9_5_dropPreservation_of_store_effects` are consequences rather than
assumptions.  `LifetimeChild parent child` is the static side condition of the
block rule and, in particular, says that the dropped lifetime is not root.
-/
theorem lemma_9_5_dropPreservation_of_store_invariants
    {store store' : ProgramStore} {env : Env}
    {parent child : Lifetime}
    (hwellFormed : WellFormedEnv env child)
    (hsafe : store ≈ₛ env)
    (hvalidStore : ValidStore store)
    (hownersAllocated : StoreOwnersAllocated store)
    (hownersHeap : StoreOwnerTargetsHeap store)
    (hheapRoot : HeapSlotsRootLifetime store)
    (hchild : LifetimeChild parent child)
    (hdrops : DropsLifetime store child store') :
    store' ≈ₛ env.dropLifetime child := by
  have hvalidUnit : ValidRuntimeState store (.val .unit) := by
    exact ⟨⟨hvalidStore,
        by simp [ValidTerm, termOwningLocations, termValues,
          valueOwningLocations, valueOwnedLocation?],
        by simp [termOwningLocations, termValues, valueOwningLocations,
          valueOwnedLocation?]⟩,
      hownersAllocated,
      hownersHeap,
      hheapRoot,
      termOwnerTargetsHeap_unit⟩
  have hvalidBlock :
      ValidRuntimeState store (.block child [.val .unit]) :=
    validRuntimeState_block_singleton_value_of_value hvalidUnit
  have hterminal :
      TerminalStateSafe store' .unit (env.dropLifetime child) .unit :=
    FWRust.Paper.preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop
      hvalidBlock hsafe.whenInitialized hchild hwellFormed.whenInitialized
      WellFormedTy.unit ValidPartialValueWhenInitialized.unit
      (MultiStep.trans (Step.blockB (lifetime := parent) hdrops)
        MultiStep.refl)
  exact SafeAbstraction.full_of_containedBorrowsWellFormed
    (ContainedBorrowsWellFormed.dropLifetime_child hchild
      hwellFormed.1 hwellFormed.2)
    hterminal.2.1

/--
Runtime-state corollary of
`lemma_9_5_dropPreservation_of_store_invariants`.  The original term is
irrelevant after projecting its four store-level invariants.
-/
theorem lemma_9_5_dropPreservation_of_validRuntimeState
    {store store' : ProgramStore} {env : Env} {term : Term}
    {parent child : Lifetime}
    (hwellFormed : WellFormedEnv env child)
    (hsafe : store ≈ₛ env)
    (hvalidRuntime : ValidRuntimeState store term)
    (hchild : LifetimeChild parent child)
    (hdrops : DropsLifetime store child store') :
    store' ≈ₛ env.dropLifetime child := by
  exact lemma_9_5_dropPreservation_of_store_invariants
    hwellFormed hsafe
    (ValidRuntimeState.validStore hvalidRuntime)
    (ValidRuntimeState.storeOwnersAllocated hvalidRuntime)
    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
    (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime)
    hchild hdrops

/--
Appendix 9.5 support: recursive drops preserve a value abstraction when every
location inspected by that abstraction is avoided by the drop derivation.
-/
theorem lemma_9_5_value_drops_frame {store store' : ProgramStore}
    {values : List PartialValue} {value : Value} {ty : Ty} :
    Drops store values store' →
    ValidValue store value ty →
    (∀ location, RuntimeFrame.Reaches store (.value value) (.ty ty) location →
      DropsAvoids store values location) →
    ValidValue store' value ty :=
  RuntimeFrame.validValue_drops_of_avoids_reaches

/--
Closed counterexample to the printed unqualified Lemma 9.5 under the current
abstract `ProgramStore`.  The child slot `x` owns the outer variable slot `y`.
The lifetime drop erases `x`, recursively follows that owner, and erases `y`,
while the environment drop correctly retains `y`.  This deliberately violates
`StoreOwnerTargetsHeap`, and hence cannot satisfy `ValidRuntimeState` for any
term.
-/
theorem lemma_9_5_unqualified_counterexample :
    ∃ (store store' : ProgramStore) (env : Env)
      (current lifetime : Lifetime),
      WellFormedEnv env current ∧
      store ≈ₛ env ∧
      DropsLifetime store lifetime store' ∧
      ¬ store' ≈ₛ env.dropLifetime lifetime := by
  let child : Lifetime := ([0] : Lifetime)
  let root : Lifetime := Lifetime.root
  let ownerY : Reference := { location := .var "y", owner := true }
  let storeY : ProgramStore :=
    ProgramStore.empty.declare "y" root (.int 5)
  let store : ProgramStore :=
    storeY.declare "x" child (.ref ownerY)
  let envY : Env := Env.empty.update "y"
    { ty := .ty .int, lifetime := root }
  let env : Env := envY.update "x"
    { ty := .ty (.box .int), lifetime := child }
  let xSlot : StoreSlot :=
    { value := .value (.ref ownerY), lifetime := child }
  let ySlot : StoreSlot :=
    { value := .value (.int 5), lifetime := root }
  let finalStore : ProgramStore :=
    (store.erase (.var "x")).erase (.var "y")
  have hsafeY : storeY ≈ₛ envY := by
    exact safeAbstraction_declare fullSafeAbstraction_empty
      (by simp [Env.fresh, Env.empty])
      (show ValidValue storeY (.int 5) .int from ValidPartialValue.int)
      (by
        intro y envSlot oldValue _hy henvSlot _hstoreSlot
        simp [Env.empty] at henvSlot)
  have hfreshX : storeY.fresh (.var "x") := by
    simp [storeY, root, ProgramStore.fresh, ProgramStore.declare,
      ProgramStore.update]
  have hownerValidY : ValidValue storeY (.ref ownerY) (.box .int) := by
    exact ValidPartialValue.boxFull
      (location := .var "y") (slot := ySlot)
      (by simp [storeY, ySlot, root, ProgramStore.declare,
        ProgramStore.update])
      ValidPartialValue.int
  have hownerValid : ValidValue store (.ref ownerY) (.box .int) := by
    exact validPartialValue_declare hfreshX hownerValidY
  have hsafe : store ≈ₛ env := by
    exact safeAbstraction_declare hsafeY
      (by simp [envY, Env.fresh, Env.empty, Env.update]) hownerValid
      (by
        intro y envSlot oldValue _hy henvSlot hstoreSlot
        rcases hsafeY.2 y envSlot henvSlot with
          ⟨safeValue, hsafeStore, hvalid⟩
        have hvalueEq : safeValue = oldValue := by
          rw [hstoreSlot] at hsafeStore
          injection hsafeStore with hslotEq
          exact (congrArg StoreSlot.value hslotEq).symm
        subst oldValue
        exact validPartialValue_declare hfreshX hvalid)
  have hwellYRoot : WellFormedEnv envY root := by
    exact WellFormedEnv.update_fresh_ty (wellFormedEnv_empty root)
      WellFormedTy.int (by simp [Env.fresh, Env.empty])
  have hrootChild : root ≤ child := by
    simp [root, child, Lifetime.root, LifetimeOutlives,
      Lifetime.contains]
  have hwellYChild : WellFormedEnv envY child :=
    WellFormedEnv.weaken hwellYRoot hrootChild
  have hwell : WellFormedEnv env child := by
    exact WellFormedEnv.update_fresh_ty hwellYChild
      (WellFormedTy.box WellFormedTy.int)
      (by simp [envY, Env.fresh, Env.empty, Env.update])
  have hdrops : Drops store
      [.value (.ref { location := .var "x", owner := true })]
      finalStore := by
    apply ProgramStore.Drops.ownerPresent
      (ref := { location := .var "x", owner := true })
      (slot := xSlot)
    · rfl
    · simp [store, storeY, xSlot, ownerY, root, child,
        ProgramStore.declare, ProgramStore.update]
    apply ProgramStore.Drops.ownerPresent
      (ref := ownerY) (slot := ySlot)
    · rfl
    · simp [store, storeY, ySlot, ownerY, root, child,
        ProgramStore.declare, ProgramStore.update, ProgramStore.erase]
    apply ProgramStore.Drops.nonOwner
    · intro ref
      left
      simp [ySlot]
    · exact ProgramStore.Drops.nil
  have hdropsLifetime : DropsLifetime store child finalStore := by
    refine ProgramStore.DropsLifetime.intro
      (dropSet :=
        [.value (.ref { location := .var "x", owner := true })])
      ?_ hdrops
    intro value
    constructor
    · intro hmem
      simp at hmem
      subst value
      exact ⟨.var "x", xSlot,
        by simp [store, storeY, xSlot, ownerY, root, child,
          ProgramStore.declare, ProgramStore.update],
        by rfl, rfl⟩
    · rintro ⟨location, slot, hslot, hlifetime, rfl⟩
      by_cases hx : location = (.var "x" : Location)
      · subst location
        simp
      · by_cases hy : location = (.var "y" : Location)
        · subst location
          simp [store, storeY, root, child, ProgramStore.declare,
            ProgramStore.update] at hslot
          subst slot
          simp [child, Lifetime.root] at hlifetime
        · simp [store, storeY, ProgramStore.declare,
            ProgramStore.update, hx, hy] at hslot
  have hnotSafe : ¬ finalStore ≈ₛ env.dropLifetime child := by
    intro hsafeFinal
    have henvY :
        (env.dropLifetime child).slotAt "y" =
          some { ty := .ty .int, lifetime := root } := by
      apply Env.dropLifetime_slotAt_eq_some.mpr
      constructor
      · simp [env, envY, Env.update]
      · simp [root, child, Lifetime.root]
    rcases (hsafeFinal.1 "y").mpr ⟨_, henvY⟩ with ⟨slot, hslot⟩
    simp [finalStore, store, storeY, ProgramStore.erase,
      ProgramStore.declare, ProgramStore.update, VariableProjection] at hslot
  exact ⟨store, finalStore, env, child, child, hwell, hsafe,
    hdropsLifetime, hnotSafe⟩

end FWRust.Paper.Soundness
