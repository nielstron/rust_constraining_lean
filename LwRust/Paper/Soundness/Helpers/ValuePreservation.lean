import LwRust.Paper.Soundness.Helpers.Frame

/-!
# Soundness helpers: ValuePreservation

Value-preservation fragments, composed runtime-validity preservation, multistep preservation.
-/

namespace LwRust
namespace Paper

open Core

/-! ## Appendix 9.4: Value Preservation Fragments -/

/-- Lemma 9.9, `R-Copy` one-step value preservation fragment, safe-only form. -/
theorem valuePreservation_copy_step_of_safe {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    ValidValue store value ty := by
  intro hsafe htyping hstep
  cases htyping with
  | copy hLv _hcopy _hreadProhibited =>
      cases hstep with
      | copy hread =>
          rcases readPreservation_of_safe hsafe hLv with
            ⟨readValue, runtimeSlot, hreadPreserved, hslotValue, hvalidValue⟩
          rw [hread] at hreadPreserved
          injection hreadPreserved with hslotEq
          cases hslotEq
          cases hslotValue
          exact hvalidValue

/-- Lemma 9.9, `R-Copy` one-step value preservation fragment. -/
theorem valuePreservation_copy_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    ValidValue store value ty := by
  intro _hwellFormed hsafe htyping hstep
  exact valuePreservation_copy_step_of_safe hsafe htyping hstep

/-- Lemma 9.9, `R-Move` one-step value preservation fragment, safe-only form. -/
theorem valuePreservation_move_step_of_safe {store store' : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store value ty := by
  intro hsafe htyping hstep
  cases htyping with
  | move hLv _hwriteProhibited _hmove =>
      cases hstep with
      | move hread _hwrite =>
          rcases readPreservation_of_safe hsafe hLv with
            ⟨readValue, runtimeSlot, hreadPreserved, hslotValue, hvalidValue⟩
          rw [hread] at hreadPreserved
          injection hreadPreserved with hslotEq
          cases hslotEq
          cases hslotValue
          exact hvalidValue

/-- Lemma 9.9, `R-Move` one-step value preservation fragment. -/
theorem valuePreservation_move_step {store store' : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store value ty := by
  intro _hwellFormed hsafe htyping hstep
  exact valuePreservation_move_step_of_safe hsafe htyping hstep

/--
`R-Move` value preservation in the post-write store, factored through an
explicit frame condition.

 The frame condition is no longer an opaque post-store validity premise:
the location overwritten by `move` must not be one of the locations inspected by
the moved value's validity derivation in the pre-write store.
-/
theorem valuePreservation_move_step_of_not_reaches_of_safe {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {value : Value} {ty : Ty} :
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    (∀ updated slot,
      store.loc lv = some updated →
      store.slotAt updated = some slot →
      ∀ ℓ, RuntimeFrame.Reaches store (.value value) (.ty ty) ℓ → ℓ ≠ updated) →
    ValidValue store' value ty := by
  intro hsafe htyping hstep hframe
  have hvalidStore : ValidValue store value ty :=
    valuePreservation_move_step_of_safe hsafe htyping hstep
  cases hstep with
  | move hread hwrite =>
      cases hloc : store.loc lv with
      | none =>
          simp [ProgramStore.read, hloc] at hread
      | some updated =>
          cases hslot : store.slotAt updated with
          | none =>
              simp [ProgramStore.read, hloc, hslot] at hread
          | some oldSlot =>
              have hstore' :
                  store' =
                    store.update updated { oldSlot with value := PartialValue.undef } := by
                simp [ProgramStore.write, hloc, hslot] at hwrite
                exact hwrite.symm
              subst hstore'
              exact RuntimeFrame.validValue_update_of_not_reaches hvalidStore
                (hframe updated oldSlot hloc hslot)

theorem valuePreservation_move_step_of_not_reaches {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    (∀ updated slot,
      store.loc lv = some updated →
      store.slotAt updated = some slot →
      ∀ ℓ, RuntimeFrame.Reaches store (.value value) (.ty ty) ℓ → ℓ ≠ updated) →
    ValidValue store' value ty := by
  intro _hwellFormed hsafe htyping hstep hframe
  exact valuePreservation_move_step_of_not_reaches_of_safe hsafe htyping hstep hframe

/-- `R-Move` post-write value preservation for unit values, safe-only form. -/
theorem valuePreservation_move_step_unit_post_of_safe {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) .unit env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .unit := by
  intro hsafe htyping hstep
  exact valuePreservation_move_step_of_not_reaches_of_safe
    hsafe htyping hstep
    (by
      intro _updated _slot _hloc _hslot ℓ hreach
      cases hreach)

/-- `R-Move` post-write value preservation for unit values. -/
theorem valuePreservation_move_step_unit_post {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) .unit env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .unit := by
  intro _hwellFormed hsafe htyping hstep
  exact valuePreservation_move_step_unit_post_of_safe hsafe htyping hstep

/-- `R-Move` post-write value preservation for integer values, safe-only form. -/
theorem valuePreservation_move_step_int_post_of_safe {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) .int env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .int := by
  intro hsafe htyping hstep
  exact valuePreservation_move_step_of_not_reaches_of_safe
    hsafe htyping hstep
    (by
      intro _updated _slot _hloc _hslot ℓ hreach
      cases hreach)

/-- `R-Move` post-write value preservation for integer values. -/
theorem valuePreservation_move_step_int_post {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) .int env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .int := by
  intro _hwellFormed hsafe htyping hstep
  exact valuePreservation_move_step_int_post_of_safe hsafe htyping hstep

/-- Lemma 9.9, `R-Borrow` one-step value preservation fragment. -/
theorem valuePreservation_borrow_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {mutable : Bool} {location : Location} :
    TermTyping env typing lifetime (.borrow mutable lv)
      (.borrow mutable [lv]) env₂ →
    Step store lifetime (.borrow mutable lv) store
      (.val (.ref { location := location, owner := false })) →
    ValidValue store (.ref { location := location, owner := false })
      (.borrow mutable [lv]) := by
  intro _htyping hstep
  cases hstep with
  | borrow hloc =>
      exact ValidPartialValue.borrow (by simp) hloc

/-- Copyable runtime values never contain owning references. -/
theorem copy_value_nonOwner {store : ProgramStore} {value : Value} {ty : Ty} :
    CopyTy ty →
    ValidValue store value ty →
    valueOwnedLocation? value = none := by
  intro hcopy hvalid
  cases hcopy with
  | unit =>
      cases hvalid
      rfl
  | int =>
      cases hvalid
      rfl
  | bool =>
      cases hvalid
      rfl
  | immBorrow =>
      cases hvalid with
      | borrow _hmem _hloc =>
          rfl

/-- Lemma 9.8, `R-Copy` valid-state preservation fragment, safe-only form. -/
theorem validState_copy_step_of_safe {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidState store (.copy lv) →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    ValidState store (.val value) := by
  intro hsafe hvalidState htyping hstep
  rcases hvalidState with ⟨hvalidStore, _hvalidTerm, _hdisjoint⟩
  cases htyping with
  | copy hLv hcopy _hreadProhibited =>
      cases hstep with
      | copy hread =>
          rcases readPreservation_of_safe hsafe hLv with
            ⟨readValue, runtimeSlot, hreadPreserved, hslotValue, hvalidValue⟩
          rw [hread] at hreadPreserved
          injection hreadPreserved with hslotEq
          cases hslotEq
          cases hslotValue
          have hnonOwner : valueOwnedLocation? value = none :=
            copy_value_nonOwner hcopy hvalidValue
          exact ⟨hvalidStore,
            validTerm_value_nonOwner hnonOwner,
            by
              intro owned hmem
              simp [termOwningLocations, termValues, valueOwningLocations,
                hnonOwner] at hmem⟩

/-- Lemma 9.8, `R-Copy` valid-state preservation fragment. -/
theorem validState_copy_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidState store (.copy lv) →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    ValidState store (.val value) := by
  intro _hwellFormed hsafe hvalidState htyping hstep
  exact validState_copy_step_of_safe hsafe hvalidState htyping hstep

/-- Lemma 9.8, `R-Borrow` valid-state preservation fragment. -/
theorem validState_borrow_step {store : ProgramStore} {lifetime : Lifetime}
    {mutable : Bool} {lv : LVal} {location : Location} :
    ValidState store (.borrow mutable lv) →
    Step store lifetime (.borrow mutable lv) store
      (.val (.ref { location := location, owner := false })) →
    ValidState store (.val (.ref { location := location, owner := false })) := by
  intro hvalidState _hstep
  rcases hvalidState with ⟨hvalidStore, _hvalidTerm, _hdisjoint⟩
  exact ⟨hvalidStore,
    validTerm_value_nonOwner
      (show valueOwnedLocation?
        (.ref { location := location, owner := false }) = none from rfl),
    by
      intro owned hmem
      simp [termOwningLocations, termValues, valueOwningLocations,
        valueOwnedLocation?] at hmem⟩

/-- Lemma 9.8, `R-Move` valid-state preservation fragment. -/
theorem validState_move_step {store store' : ProgramStore}
    {lifetime : Lifetime} {lv : LVal} {value : Value} :
    ValidState store (.move lv) →
    Step store lifetime (.move lv) store' (.val value) →
    ValidState store' (.val value) := by
  intro hvalidState hstep
  rcases hvalidState with ⟨hvalidStore, _hvalidTerm, _hdisjoint⟩
  cases hstep with
  | move hread hwrite =>
      exact ⟨validStore_write_undef hvalidStore hwrite,
        validTerm_value value,
        by
          intro owned hmem howns
          exact not_owns_after_move_of_owning_read hvalidStore hread hwrite
            (eq_owningRef_of_mem_valueOwningLocations
              (by simpa [termOwningLocations, termValues] using hmem))
            howns⟩

/-- Lemma 9.8, `R-Assign` valid-state preservation fragment. -/
theorem validState_assign_step {store store' : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {value : Value} :
    ValidState store (.assign lhs (.val value)) →
    Step store lifetime (.assign lhs (.val value)) store' (.val .unit) →
    ValidState store' (.val .unit) := by
  intro hvalidState hstep
  rcases hvalidState with ⟨hvalidStore, _hvalidTerm, hdisjoint⟩
  cases hstep with
  | assign hread hwrite hdrops =>
      have hvalidWritten :
          ValidStore _ :=
        validStore_write_disjoint hvalidStore (by
          intro owned hmem howns
          exact hdisjoint owned
            (by simpa [termOwningLocations, termValues, partialValueOwningLocations]
              using hmem)
            howns) hwrite
      exact ⟨drops_validStore hdrops hvalidWritten,
        validTerm_unit,
        by
          intro owned hmem
          simp [termOwningLocations, termValues, valueOwningLocations,
            valueOwnedLocation?] at hmem⟩

/-- Allocation invariant preservation for `R-Copy`. -/
theorem storeOwnersAllocated_copy_step {store : ProgramStore}
    {lifetime : Lifetime} {lv : LVal} {value : Value} :
    StoreOwnersAllocated store →
    Step store lifetime (.copy lv) store (.val value) →
    StoreOwnersAllocated store := by
  intro hallocated _hstep
  exact hallocated

/-- Allocation invariant preservation for `R-Borrow`. -/
theorem storeOwnersAllocated_borrow_step {store : ProgramStore}
    {lifetime : Lifetime} {mutable : Bool} {lv : LVal} {location : Location} :
    StoreOwnersAllocated store →
    Step store lifetime (.borrow mutable lv) store
      (.val (.ref { location := location, owner := false })) →
    StoreOwnersAllocated store := by
  intro hallocated _hstep
  exact hallocated

/-- Allocation invariant preservation for `R-Move`. -/
theorem storeOwnersAllocated_move_step {store store' : ProgramStore}
    {lifetime : Lifetime} {lv : LVal} {value : Value} :
    StoreOwnersAllocated store →
    Step store lifetime (.move lv) store' (.val value) →
    StoreOwnersAllocated store' := by
  intro hallocated hstep
  cases hstep with
  | move _hread hwrite =>
      exact storeOwnersAllocated_write_undef hallocated hwrite

/-- Allocation invariant preservation for `R-Declare`. -/
theorem storeOwnersAllocated_declare_step_of_validValue {store store' : ProgramStore}
    {lifetime : Lifetime} {x : Name} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    StoreOwnersAllocated store' := by
  intro hallocated hvalidValue hstep
  cases hstep with
  | declare hstore' =>
      subst hstore'
      exact storeOwnersAllocated_declare_of_validValue hallocated hvalidValue

/-- Allocation invariant preservation for `R-Seq`. -/
theorem storeOwnersAllocated_seq_step {store store' : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    ValidState store (.block blockLifetime (.val value :: next :: rest)) →
    StoreOwnersAllocated store →
    Step store lifetime (.block blockLifetime (.val value :: next :: rest))
      store' (.block blockLifetime (next :: rest)) →
    StoreOwnersAllocated store' := by
  intro hvalidState hallocated hstep
  rcases hvalidState with ⟨hvalidStore, _hvalidTerm, hdisjoint⟩
  cases hstep with
  | seq hdrops =>
      exact drops_storeOwnersAllocated_of_disjoint hdrops hvalidStore hallocated (by
        intro owned hmem
        exact hdisjoint owned (by
          simp [partialValuesOwningLocations, partialValueOwningLocations] at hmem
          simp [termOwningLocations, termValues]
          exact Or.inl hmem))

/-- Allocation invariant preservation for `R-BlockB`. -/
theorem storeOwnersAllocated_blockB_step {store store' : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} :
    ValidState store (.block blockLifetime [.val value]) →
    StoreOwnersAllocated store →
    LifetimeDropOwnersDisjoint store blockLifetime →
    Step store lifetime (.block blockLifetime [.val value]) store' (.val value) →
    StoreOwnersAllocated store' := by
  intro hvalidState hallocated hdropDisjoint hstep
  rcases hvalidState with ⟨hvalidStore, _hvalidTerm, _hdisjoint⟩
  cases hstep with
  | blockB hdrops =>
      exact dropsLifetime_storeOwnersAllocated hdrops hvalidStore hallocated hdropDisjoint

/-- Lemma 9.8, `R-Box` valid-state preservation fragment. -/
theorem validState_box_step {store store' : ProgramStore}
    {address : Nat} {value : Value} {ref : Reference} :
    ValidState store (.box (.val value)) →
    store.fresh (.heap address) →
    (.heap address) ∉ valueOwningLocations value →
    ¬ ProgramStore.Owns store (.heap address) →
    store.boxAt address value = (store', ref) →
    ValidState store' (.val (.ref ref)) := by
  intro hvalidState hfresh hnotInValue hnotOwned hbox
  rcases hvalidState with ⟨hvalidStore, hvalidTerm, hdisjoint⟩
  cases hbox
  exact ⟨validStore_update_fresh hvalidStore hfresh (by
      intro owned hmem howns
      exact hdisjoint owned
        (by simpa [termOwningLocations, termValues, partialValueOwningLocations]
          using hmem)
        howns),
    by
      simp [ValidTerm, termOwningLocations, termValues, valueOwningLocations,
        valueOwnedLocation?],
    by
      intro owned hmem howns
      simp [termOwningLocations, termValues, valueOwningLocations,
        valueOwnedLocation?] at hmem
      subst hmem
      rcases howns with ⟨storage, hownsAt⟩
      rcases hownsAt with ⟨slotLifetime, hslot⟩
      by_cases hstorage : storage = .heap address
      · subst hstorage
        simp [ProgramStore.update] at hslot
        exact hnotInValue (mem_valueOwningLocations_of_eq_owningRef hslot.1)
      · simp [ProgramStore.update, hstorage] at hslot
        exact hnotOwned ⟨storage, slotLifetime, hslot⟩⟩

/--
Lemma 9.8, typed `R-Box` valid-state preservation fragment.

The freshness side conditions required by `validState_box_step` are derived
from value validity and from the explicit allocation invariant for abstract
stores.
-/
theorem validState_box_step_of_validValue {store store' : ProgramStore}
    {lifetime : Lifetime} {value : Value} {ty : Ty} {ref : Reference} :
    ValidState store (.box (.val value)) →
    StoreOwnersAllocated store →
    ValidValue store value ty →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidState store' (.val (.ref ref)) := by
  intro hvalidState hallocated hvalidValue hstep
  cases hstep with
  | box hfresh hbox =>
      exact validState_box_step hvalidState hfresh
        (validValue_fresh_not_owningLocation hvalidValue hfresh)
        (not_owns_of_fresh_of_storeOwnersAllocated hallocated hfresh)
        hbox

/-- Allocation invariant preservation for `R-Box`, from operand validity. -/
theorem storeOwnersAllocated_box_step_of_validValue {store store' : ProgramStore}
    {lifetime : Lifetime} {value : Value} {ty : Ty} {ref : Reference} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    StoreOwnersAllocated store' := by
  intro hallocated hvalidValue hstep
  cases hstep with
  | box _hfresh hbox =>
      cases hbox
      exact storeOwnersAllocated_boxAt_of_validValue hallocated hvalidValue

/-! ### Composed Runtime Validity Preservation Fragments -/

/-- Runtime-validity preservation for `R-Copy`, safe-only form. -/
theorem validRuntimeState_copy_step_of_safe {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.copy lv) →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    ValidRuntimeState store (.val value) := by
  intro hsafe hvalidRuntime htyping hstep
  have htermHeap : TermOwnerTargetsHeap (.val value) := by
    cases htyping with
    | copy hLv hcopy hreadProhibited =>
        exact termOwnerTargetsHeap_value_nonOwner
          (copy_value_nonOwner hcopy
            (valuePreservation_copy_step_of_safe hsafe
              (TermTyping.copy (typing := typing) hLv hcopy hreadProhibited) hstep))
  exact ⟨validState_copy_step_of_safe hsafe hvalidRuntime.1 htyping hstep,
    storeOwnersAllocated_copy_step
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hstep,
    ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime,
    ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime,
    htermHeap⟩

/-- Runtime-validity preservation for `R-Copy`. -/
theorem validRuntimeState_copy_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidRuntimeState store (.copy lv) →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    ValidRuntimeState store (.val value) := by
  intro _hwellFormed hsafe hvalidRuntime htyping hstep
  exact validRuntimeState_copy_step_of_safe hsafe hvalidRuntime htyping hstep

/-- Runtime-validity preservation for `R-Borrow`. -/
theorem validRuntimeState_borrow_step {store : ProgramStore}
    {lifetime : Lifetime} {mutable : Bool} {lv : LVal} {location : Location} :
    ValidRuntimeState store (.borrow mutable lv) →
    Step store lifetime (.borrow mutable lv) store
      (.val (.ref { location := location, owner := false })) →
    ValidRuntimeState store (.val (.ref { location := location, owner := false })) := by
  intro hvalidRuntime hstep
  exact ⟨validState_borrow_step hvalidRuntime.1 hstep,
    storeOwnersAllocated_borrow_step
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hstep,
    ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime,
    ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime,
    termOwnerTargetsHeap_borrowed_ref⟩

/-- Runtime-validity preservation for `R-Move`. -/
theorem validRuntimeState_move_step {store store' : ProgramStore}
    {lifetime : Lifetime} {lv : LVal} {value : Value} :
    ValidRuntimeState store (.move lv) →
    Step store lifetime (.move lv) store' (.val value) →
    ValidRuntimeState store' (.val value) := by
  intro hvalidRuntime hstep
  cases hstep with
  | move hread hwrite =>
      exact ⟨validState_move_step hvalidRuntime.1
          (Step.move (lifetime := lifetime) hread hwrite),
        storeOwnersAllocated_move_step
          (ValidRuntimeState.storeOwnersAllocated hvalidRuntime)
          (Step.move (lifetime := lifetime) hread hwrite),
        storeOwnerTargetsHeap_write_undef
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hwrite,
        heapSlotsRootLifetime_write_undef
          (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwrite,
        termOwnerTargetsHeap_value_of_store_read
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hread⟩

/--
Runtime-validity preservation for `R-Assign`, assuming the assignment's
drop/write sequence preserves the explicit owner-allocation invariant.

The paper's store model leaves this allocation invariant implicit; the premise
is the explicit update-preservation frame condition for our abstract store
package.
-/
theorem validRuntimeState_assign_step {store store' : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {value : Value} :
    ValidRuntimeState store (.assign lhs (.val value)) →
    StoreOwnersAllocated store' →
    StoreOwnerTargetsHeap store' →
    HeapSlotsRootLifetime store' →
    Step store lifetime (.assign lhs (.val value)) store' (.val .unit) →
    ValidRuntimeState store' (.val .unit) := by
  intro hvalidRuntime hallocated hheap hroot hstep
  exact ⟨validState_assign_step hvalidRuntime.1 hstep, hallocated, hheap,
    hroot, termOwnerTargetsHeap_unit⟩

/--
Runtime-validity preservation for `R-Assign` from final post-write/post-drop
store invariants.
-/
theorem validRuntimeState_assign_step_of_postWriteDrop_invariants
    {store storeAfterWrite store' : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot}
    {value : Value} :
    ValidRuntimeState store (.assign lhs (.val value)) →
    StoreOwnersAllocated store' →
    StoreOwnerTargetsHeap store' →
    HeapSlotsRootLifetime store' →
    store.read lhs = some oldSlot →
    store.write lhs (.value value) = some storeAfterWrite →
    Drops storeAfterWrite [oldSlot.value] store' →
    ValidRuntimeState store' (.val .unit) := by
  intro hvalidRuntime hallocated hheap hroot hread hwrite hdrops
  exact validRuntimeState_assign_step (lifetime := lifetime) hvalidRuntime
    hallocated hheap hroot
    (Step.assign (lifetime := lifetime) hread hwrite hdrops)

/--
Runtime-validity preservation for `R-Assign` when the old lhs value is
non-owning.  In this common case the drop step is a no-op, so the original
allocation invariant and RHS value abstraction are enough.
-/
theorem validRuntimeState_assign_step_old_nonOwner
    {store storeAfterWrite store' : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot}
    {value : Value} {ty : Ty} :
    PartialValueNonOwner oldSlot.value →
    ValidRuntimeState store (.assign lhs (.val value)) →
    ValidValue store value ty →
    store.read lhs = some oldSlot →
    store.write lhs (.value value) = some storeAfterWrite →
    Drops storeAfterWrite [oldSlot.value] store' →
    ValidRuntimeState store' (.val .unit) := by
  intro hnonOwner hvalidRuntime hvalidValue hread hwrite hdrops
  have hdropEq : store' = storeAfterWrite :=
    drops_partialValue_nonOwner_eq hnonOwner hdrops
  subst store'
  have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
    ValueOwnerTargetsHeap.partial
      (TermOwnerTargetsHeap.value
        (termOwnerTargetsHeap_assign_inner
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
  exact validRuntimeState_assign_step_of_postWriteDrop_invariants
    (lifetime := lifetime) hvalidRuntime
    (storeOwnersAllocated_write_value_of_validValue
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue hwrite)
    (storeOwnerTargetsHeap_write
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hvalueHeap hwrite)
    (heapSlotsRootLifetime_write
      (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwrite)
    hread hwrite hdrops

/-- Runtime-validity preservation for `R-Declare`, from initializer validity. -/
theorem validRuntimeState_declare_step_of_validValue {store store' : ProgramStore}
    {lifetime : Lifetime} {x : Name} {value : Value} {ty : Ty} :
    ValidRuntimeState store (.letMut x (.val value)) →
    store.fresh (.var x) →
    ValidValue store value ty →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    ValidRuntimeState store' (.val .unit) := by
  intro hvalidRuntime hfresh hvalidValue hstep
  cases hstep with
  | declare hstore' =>
      subst hstore'
      have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
        ValueOwnerTargetsHeap.partial
          (TermOwnerTargetsHeap.value
            (termOwnerTargetsHeap_declare_inner
              (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
      exact ⟨validState_declare hvalidRuntime.1 hfresh,
        storeOwnersAllocated_declare_step_of_validValue
          (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
          (Step.declare rfl),
        by
          simpa [ProgramStore.declare] using
            storeOwnerTargetsHeap_update
              (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hvalueHeap,
        by
          simpa [ProgramStore.declare] using
            heapSlotsRootLifetime_update_var
              (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime),
        termOwnerTargetsHeap_unit⟩

/-- Runtime-validity preservation for `R-Seq`. -/
theorem validRuntimeState_seq_step {store store' : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    Step store lifetime (.block blockLifetime (.val value :: next :: rest))
      store' (.block blockLifetime (next :: rest)) →
    ValidRuntimeState store' (.block blockLifetime (next :: rest)) := by
  intro hvalidRuntime hstep
  cases hstep with
  | seq hdrops =>
      exact ⟨validState_seq_step hvalidRuntime.1 hdrops,
        storeOwnersAllocated_seq_step (lifetime := lifetime)
          hvalidRuntime.1 (ValidRuntimeState.storeOwnersAllocated hvalidRuntime)
          (Step.seq (lifetime := lifetime) hdrops),
        drops_storeOwnerTargetsHeap hdrops
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime),
        drops_heapSlotsRootLifetime hdrops
          (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime),
        termOwnerTargetsHeap_block_tail
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)⟩

/-- Runtime-validity preservation for `R-BlockB`. -/
theorem validRuntimeState_blockB_step {store store' : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    LifetimeDropOwnersDisjoint store blockLifetime →
    Step store lifetime (.block blockLifetime [.val value]) store' (.val value) →
    ValidRuntimeState store' (.val value) := by
  intro hvalidRuntime hdropDisjoint hstep
  cases hstep with
  | blockB hdrops =>
      exact ⟨validState_blockB hvalidRuntime.1 hdrops,
        storeOwnersAllocated_blockB_step (lifetime := lifetime)
          hvalidRuntime.1 (ValidRuntimeState.storeOwnersAllocated hvalidRuntime)
          hdropDisjoint (Step.blockB (lifetime := lifetime) hdrops),
        dropsLifetime_storeOwnerTargetsHeap hdrops
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime),
        dropsLifetime_heapSlotsRootLifetime hdrops
          (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime),
        termOwnerTargetsHeap_block_value
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)⟩

/--
Runtime-validity preservation for `R-BlockB` under the typed block-lifetime
shape.  Heap slots are always root-lifetime slots, and `T-Block` supplies a
child lifetime, so no store owner target can be allocated in the dropped block
lifetime.
-/
theorem validRuntimeState_blockB_step_of_child {store store' : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    LifetimeChild lifetime blockLifetime →
    Step store lifetime (.block blockLifetime [.val value]) store' (.val value) →
    ValidRuntimeState store' (.val value) := by
  intro hvalidRuntime hchild hstep
  exact validRuntimeState_blockB_step hvalidRuntime
    (lifetimeDropOwnersDisjoint_of_heapRootLifetime
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
      (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime)
      hchild)
    hstep

/-- Runtime-validity preservation for `R-Box`, from operand validity. -/
theorem validRuntimeState_box_step_of_validValue {store store' : ProgramStore}
    {lifetime : Lifetime} {value : Value} {ty : Ty} {ref : Reference} :
    ValidRuntimeState store (.box (.val value)) →
    ValidValue store value ty →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidRuntimeState store' (.val (.ref ref)) := by
  intro hvalidRuntime hvalidValue hstep
  cases hstep with
  | box hfresh hbox =>
      have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
        ValueOwnerTargetsHeap.partial
          (TermOwnerTargetsHeap.value
            (termOwnerTargetsHeap_box_inner
              (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
      exact ⟨validState_box_step_of_validValue hvalidRuntime.1
          (ValidRuntimeState.storeOwnersAllocated hvalidRuntime)
          hvalidValue (Step.box (lifetime := lifetime) hfresh hbox),
        storeOwnersAllocated_box_step_of_validValue
          (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
          (Step.box (lifetime := lifetime) hfresh hbox),
        by
          cases hbox
          simpa [ProgramStore.boxAt] using
            storeOwnerTargetsHeap_update
              (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hvalueHeap,
        by
          cases hbox
          simpa [ProgramStore.boxAt] using
            heapSlotsRootLifetime_update_heap_root
              (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime),
        by
          cases hbox
          intro owned hmem
          simp [termOwningLocations, termValues, valueOwningLocations,
            valueOwnedLocation?] at hmem
          subst hmem
          exact ⟨_, rfl⟩⟩

/-- Lemma 9.10, `R-Copy` store-preservation fragment, safe-only form. -/
theorem storePreservation_copy_step_of_safe {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    store ∼ₛ env₂ ∧ ValidValue store value ty := by
  intro hsafe htyping hstep
  cases htyping with
  | copy hLv hcopy hreadProhibited =>
      exact ⟨hsafe,
        valuePreservation_copy_step_of_safe (typing := typing) hsafe
          (TermTyping.copy (typing := typing) hLv hcopy hreadProhibited) hstep⟩

/-- Lemma 9.10, `R-Copy` store-preservation fragment. -/
theorem storePreservation_copy_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    store ∼ₛ env₂ ∧ ValidValue store value ty := by
  intro _hwellFormed hsafe htyping hstep
  exact storePreservation_copy_step_of_safe hsafe htyping hstep

/-- Lemma 9.10, `R-Borrow` store-preservation fragment. -/
theorem storePreservation_borrow_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {mutable : Bool} {location : Location} :
    store ∼ₛ env →
    TermTyping env typing lifetime (.borrow mutable lv)
      (.borrow mutable [lv]) env₂ →
    Step store lifetime (.borrow mutable lv) store
      (.val (.ref { location := location, owner := false })) →
    store ∼ₛ env₂ ∧
      ValidValue store (.ref { location := location, owner := false })
        (.borrow mutable [lv]) := by
  intro hsafe htyping hstep
  cases htyping with
  | mutBorrow hLv hmutable hnotWrite =>
      exact ⟨hsafe,
        valuePreservation_borrow_step (typing := typing)
          (TermTyping.mutBorrow (typing := typing) hLv hmutable hnotWrite) hstep⟩
  | immBorrow hLv hnotRead =>
      exact ⟨hsafe,
        valuePreservation_borrow_step (typing := typing)
          (TermTyping.immBorrow (typing := typing) hLv hnotRead) hstep⟩

/--
Lemma 4.11, `R-Copy` one-step preservation fragment, safe-only form.

This is the combination of the runtime-validity, store-preservation, and
value-preservation facts for a copy step.
-/
theorem preservation_copy_step_runtime_of_safe {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.copy lv) →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    ValidRuntimeState store (.val value) ∧ store ∼ₛ env₂ ∧
      ValidValue store value ty := by
  intro hsafe hvalidRuntime htyping hstep
  rcases storePreservation_copy_step_of_safe hsafe htyping hstep with
    ⟨hsafe₂, hvalidValue⟩
  exact ⟨validRuntimeState_copy_step_of_safe hsafe hvalidRuntime htyping hstep,
    hsafe₂, hvalidValue⟩

/--
Lemma 4.11, `R-Copy` one-step preservation fragment.

This is the paper-facing combination of the runtime-validity, store-preservation,
and value-preservation facts for a copy step.
-/
theorem preservation_copy_step_runtime {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidRuntimeState store (.copy lv) →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    ValidRuntimeState store (.val value) ∧ store ∼ₛ env₂ ∧
      ValidValue store value ty := by
  intro _hwellFormed hsafe hvalidRuntime htyping hstep
  exact preservation_copy_step_runtime_of_safe hsafe hvalidRuntime htyping hstep

/--
Lemma 4.11, `R-Borrow` one-step preservation fragment.

This is the paper-facing combination of the runtime-validity, store-preservation,
and value-preservation facts for a borrow step.
-/
theorem preservation_borrow_step_runtime {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {mutable : Bool} {location : Location} :
    store ∼ₛ env →
    ValidRuntimeState store (.borrow mutable lv) →
    TermTyping env typing lifetime (.borrow mutable lv)
      (.borrow mutable [lv]) env₂ →
    Step store lifetime (.borrow mutable lv) store
      (.val (.ref { location := location, owner := false })) →
    ValidRuntimeState store (.val (.ref { location := location, owner := false })) ∧
      store ∼ₛ env₂ ∧
      ValidValue store (.ref { location := location, owner := false })
        (.borrow mutable [lv]) := by
  intro hsafe hvalidRuntime htyping hstep
  rcases storePreservation_borrow_step hsafe htyping hstep with
    ⟨hsafe₂, hvalidValue⟩
  exact ⟨validRuntimeState_borrow_step hvalidRuntime hstep,
    hsafe₂, hvalidValue⟩

/--
Lemma 4.11, variable `R-Move` one-step preservation fragment.

The current store-preservation proof for `move x` exposes the separate
obligation that all variables other than `x` keep valid runtime abstractions
after the source slot is overwritten with `undef`.
-/
theorem preservation_move_var_step_runtime {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {current lifetime valueLifetime : Lifetime}
    {x : Name} {value : Value} {ty : Ty} :
    WellFormedEnv env₁ current →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.move (.var x)) →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    TermTyping env₁ typing lifetime (.move (.var x)) ty env₂ →
    Step store lifetime (.move (.var x)) store' (.val value) →
    ValidValue store' value ty →
    (∀ y envSlot oldValue,
      y ≠ x →
      env₁.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ValidSlotValue store' oldValue envSlot.ty) →
    ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env₂ ∧
      ValidValue store' value ty := by
  intro _hwellFormed hsafe hvalidRuntime henvSlot hmove _htyping hstep hvalidValue
    hpreserveOld
  exact ⟨validRuntimeState_move_step hvalidRuntime hstep,
    storePreservation_move_var_step hsafe henvSlot hmove hstep hpreserveOld,
    hvalidValue⟩

/--
Lemma 4.11, variable `R-Move` one-step preservation under concrete
store-update frame conditions.

This derives the post-write validity of the moved value and the surviving
environment slots from `RuntimeFrame.Reaches` non-interference facts.  It is the
direct-variable analogue of the framed assignment fragments.
-/
theorem preservation_move_var_step_runtime_of_frames {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {current lifetime valueLifetime : Lifetime}
    {x : Name} {value : Value} {ty : Ty} :
    WellFormedEnv env₁ current →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.move (.var x)) →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    TermTyping env₁ typing lifetime (.move (.var x)) ty env₂ →
    Step store lifetime (.move (.var x)) store' (.val value) →
    (∀ ℓ, RuntimeFrame.Reaches store (.value value) (.ty ty) ℓ →
      ℓ ≠ VariableProjection x) →
    (∀ y envSlot oldValue,
      y ≠ x →
      env₁.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ∀ ℓ, RuntimeFrame.Reaches store oldValue envSlot.ty ℓ →
        ℓ ≠ VariableProjection x) →
    ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env₂ ∧
      ValidValue store' value ty := by
  intro hwellFormed hsafe hvalidRuntime henvSlot hmove htyping hstep
    hvalueFrame hotherFrames
  have hvalidStore : ValidValue store value ty :=
    valuePreservation_move_step_of_safe hsafe htyping hstep
  rcases hsafe.2 x { ty := .ty ty, lifetime := valueLifetime } henvSlot with
    ⟨sourceValue, hsourceSlot, _hsourceValid⟩
  have hsourceSlotVar :
      store.slotAt (.var x) =
        some { value := sourceValue, lifetime := valueLifetime } := by
    simpa [VariableProjection] using hsourceSlot
  have hstore' :
      store' =
        store.update (VariableProjection x)
          { value := .undef, lifetime := valueLifetime } := by
    cases hstep with
    | move hread hwrite =>
        have hreadEq := hread
        rw [show store.read (.var x) =
            some { value := sourceValue, lifetime := valueLifetime } by
              simp [ProgramStore.read, ProgramStore.loc, hsourceSlotVar]] at hreadEq
        injection hreadEq with hslotEq
        cases hslotEq
        simp [ProgramStore.write, ProgramStore.loc, hsourceSlotVar] at hwrite
        exact hwrite.symm
  have hvalidValue : ValidValue store' value ty := by
    rw [hstore']
    exact RuntimeFrame.validValue_update_of_not_reaches hvalidStore hvalueFrame
  have hpreserveOld :
      ∀ y envSlot oldValue,
        y ≠ x →
        env₁.slotAt y = some envSlot →
        store.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := envSlot.lifetime } →
        ValidSlotValue store' oldValue envSlot.ty := by
    intro y envSlot oldValue hyx henvY hstoreY
    rw [hstore']
    exact RuntimeFrame.validSlotValue_update_of_not_reaches
      (by
        rcases hsafe.2 y envSlot henvY with ⟨safeValue, hsafeSlot, hvalidOld⟩
        rw [hstoreY] at hsafeSlot
        injection hsafeSlot with hslotEq
        cases hslotEq
        exact hvalidOld)
      (hotherFrames y envSlot oldValue hyx henvY hstoreY)
  exact preservation_move_var_step_runtime hwellFormed hsafe hvalidRuntime
    henvSlot hmove htyping hstep hvalidValue hpreserveOld

/--
Lemma 4.11, `R-Box` one-step preservation fragment, factored around the
operand-value abstraction established by inner preservation.
-/
theorem preservation_box_redex_runtime_of_validValue {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {ref : Reference} :
    store ∼ₛ env →
    ValidRuntimeState store (.box (.val value)) →
    ValidValue store value ty →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidRuntimeState store' (.val (.ref ref)) ∧ store' ∼ₛ env ∧
      ValidValue store' (.ref ref) (.box ty) := by
  intro hsafe hvalidRuntime hoperandValid hstep
  cases hstep with
  | box hfresh hbox =>
      cases hbox
      exact ⟨validRuntimeState_box_step_of_validValue hvalidRuntime hoperandValid
          (Step.box (lifetime := lifetime) hfresh rfl),
        safeAbstraction_boxAt hfresh hsafe,
        validValue_boxAt_ref hfresh hoperandValid⟩

/--
Lemma 4.11, `R-Box` one-step preservation fragment, factored around the
operand-value abstraction established by inner preservation.
-/
theorem preservation_box_step_runtime_of_validValue {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {ref : Reference} :
    store ∼ₛ env₁ →
    ValidRuntimeState store (.box (.val value)) →
    ValidValue store value ty →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidRuntimeState store' (.val (.ref ref)) ∧ store' ∼ₛ env₂ ∧
      ValidValue store' (.ref ref) (.box ty) := by
  intro hsafe hvalidRuntime hoperandValid htyping hstep
  cases htyping with
  | box hinner =>
      cases hinner with
      | const _hvalueTyping =>
          exact preservation_box_redex_runtime_of_validValue hsafe hvalidRuntime
            hoperandValid hstep

/--
Lemma 4.11, `R-Box` one-step preservation fragment.

This is the paper-facing combination of the runtime-validity, store-preservation,
and value-preservation facts for a box allocation step.
-/
theorem preservation_box_step_runtime {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {ref : Reference} :
    ValidStoreTyping store (.box (.val value)) typing →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.box (.val value)) →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidRuntimeState store' (.val (.ref ref)) ∧ store' ∼ₛ env₂ ∧
      ValidValue store' (.ref ref) (.box ty) := by
  intro hvalidStoreTyping hsafe hvalidRuntime htyping hstep
  cases htyping with
  | box hinner =>
      cases hinner with
      | const hvalueTyping =>
          rcases hvalidStoreTyping value (by simp [termValues]) with
            ⟨storedTy, hstoredTyping, hvalidValue⟩
          have hty : storedTy = ty :=
            valueTyping_deterministic hstoredTyping hvalueTyping
          subst hty
          exact preservation_box_step_runtime_of_validValue hsafe hvalidRuntime
            hvalidValue
            (TermTyping.box (typing := typing) (TermTyping.const hvalueTyping))
            hstep

/--
Lemma 4.11, `R-Declare` one-step preservation fragment.

This is the paper-facing combination of the runtime-validity, store-preservation,
and value-preservation facts for a variable declaration step.
-/
theorem preservation_declare_redex_runtime_of_validValue {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} {x : Name} {value : Value} {ty : Ty} :
    store ∼ₛ env →
    env.fresh x →
    ValidRuntimeState store (.letMut x (.val value)) →
    ValidValue store value ty →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    ValidRuntimeState store' (.val .unit) ∧
      store' ∼ₛ env.update x { ty := .ty ty, lifetime := lifetime } ∧
      ValidValue store' .unit .unit := by
  intro hsafe hfresh hvalidRuntime hvalidValue hstep
  have hfreshStore : store.fresh (VariableProjection x) :=
    safeAbstraction_store_fresh_var hsafe hfresh
  cases hstep with
  | declare hstore' =>
      subst hstore'
      have hsafe' :
          store.declare x lifetime value ∼ₛ
            env.update x { ty := .ty ty, lifetime := lifetime } := by
        exact safeAbstraction_declare hsafe hfresh
          (validPartialValue_declare hfreshStore hvalidValue)
          (by
            intro y envSlot oldValue _hyx henv hstoreSlot
            rcases hsafe.2 y envSlot henv with
              ⟨safeValue, hsafeSlot, hsafeValid⟩
            rw [hstoreSlot] at hsafeSlot
            injection hsafeSlot with hslotEq
            cases hslotEq
            exact validPartialValue_declare hfreshStore hsafeValid)
      exact ⟨validRuntimeState_declare_step_of_validValue
          hvalidRuntime hfreshStore hvalidValue (Step.declare (lifetime := lifetime) rfl),
        hsafe',
        ValidPartialValue.unit⟩

/--
Lemma 4.11, `R-Declare` one-step preservation fragment.

This is the paper-facing combination of the runtime-validity, store-preservation,
and value-preservation facts for a variable declaration step.
-/
theorem preservation_declare_step_runtime {store store' : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {value : Value} :
    ValidStoreTyping store (.letMut x (.val value)) typing →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.letMut x (.val value)) →
    TermTyping env₁ typing lifetime (.letMut x (.val value)) .unit env₃ →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    ValidRuntimeState store' (.val .unit) ∧ store' ∼ₛ env₃ ∧
      ValidValue store' .unit .unit := by
  intro hvalidStoreTyping hsafe hvalidRuntime htyping hstep
  cases htyping with
  | declare hfresh hinit _hfreshOut _hcoh henv₃ =>
      cases hinit with
      | const hvalueTyping =>
          rcases hvalidStoreTyping value (by simp [termValues]) with
            ⟨storedTy, hstoredTyping, hvalidValue⟩
          have hty : storedTy = _ :=
            valueTyping_deterministic hstoredTyping hvalueTyping
          subst hty
          have hpreserved :=
            preservation_declare_redex_runtime_of_validValue hsafe hfresh
              hvalidRuntime hvalidValue hstep
          rw [henv₃]
          exact hpreserved

theorem preservation_assign_var_old_nonOwner_step_runtime_of_preserved
    {store storeAfterWrite store' : ProgramStore} {env env' : Env}
    {lifetime : Lifetime} {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    PartialValueNonOwner oldSlot.value →
    ValidValue store value ty →
    store.read (.var x) = some oldSlot →
    store.write (.var x) (.value value) = some storeAfterWrite →
    Drops storeAfterWrite [oldSlot.value] store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidSlotValue store' oldValue otherEnvSlot.ty) →
    ValidRuntimeState store' (.val .unit) ∧ store' ∼ₛ env' ∧
      ValidValue store' .unit .unit := by
  intro hsafe hvalidRuntime henvX hwriteEnv hnonOwner hvalidValue
    hread hwrite hdrops hnewValid hpreserveOther
  exact ⟨validRuntimeState_assign_step_old_nonOwner (lifetime := lifetime)
      hnonOwner hvalidRuntime hvalidValue hread hwrite hdrops,
    storePreservation_assign_var_old_nonOwner_of_preserved hsafe henvX hwriteEnv
      hnonOwner hread hwrite hdrops hnewValid hpreserveOther,
    ValidPartialValue.unit⟩

/--
Lemma 4.11, direct-variable `R-Assign` preservation fragment under concrete
store-update frame conditions.

Compared with `preservation_assign_var_old_nonOwner_step_runtime_of_preserved`,
this derives the post-write validity of the RHS value and the surviving
environment slots from `RuntimeFrame.Reaches` non-interference facts.  The old
lhs value is non-owning, so the drop is a no-op and the only store change is the
write to `x`.
-/
theorem preservation_assign_var_old_nonOwner_step_runtime_of_frames
    {store storeAfterWrite store' : ProgramStore} {env env' : Env}
    {lifetime : Lifetime} {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    PartialValueNonOwner oldSlot.value →
    ValidValue store value ty →
    store.read (.var x) = some oldSlot →
    store.write (.var x) (.value value) = some storeAfterWrite →
    Drops storeAfterWrite [oldSlot.value] store' →
    (∀ ℓ, RuntimeFrame.Reaches store (.value value) (.ty ty) ℓ →
      ℓ ≠ VariableProjection x) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ ℓ, RuntimeFrame.Reaches store oldValue otherEnvSlot.ty ℓ →
        ℓ ≠ VariableProjection x) →
    ValidRuntimeState store' (.val .unit) ∧ store' ∼ₛ env' ∧
      ValidValue store' .unit .unit := by
  intro hsafe hvalidRuntime henvX hwriteEnv hnonOwner hvalidValue
    hread hwrite hdrops hvalueFrame hotherFrames
  have hdropEq : store' = storeAfterWrite :=
    drops_partialValue_nonOwner_eq hnonOwner hdrops
  subst store'
  have hstoreX : store.slotAt (VariableProjection x) = some oldSlot := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  have hstoreAfterWrite :
      storeAfterWrite = store.update (VariableProjection x)
        { oldSlot with value := .value value } :=
    write_var_eq hstoreX hwrite
  have hnewValid : ValidPartialValue storeAfterWrite (.value value) (.ty ty) := by
    rw [hstoreAfterWrite]
    exact RuntimeFrame.validValue_update_of_not_reaches hvalidValue hvalueFrame
  have hpreserveOther :
      ∀ y otherEnvSlot,
        y ≠ x →
        env.slotAt y = some otherEnvSlot →
        ∃ oldValue,
          storeAfterWrite.slotAt (VariableProjection y) =
            some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
          ValidSlotValue storeAfterWrite oldValue otherEnvSlot.ty := by
    intro y otherEnvSlot hyx henvY
    rcases hsafe.2 y otherEnvSlot henvY with ⟨oldValue, hstoreY, hvalidOld⟩
    refine ⟨oldValue, ?_, ?_⟩
    · rw [hstoreAfterWrite]
      simpa [ProgramStore.update, VariableProjection, hyx] using hstoreY
    · rw [hstoreAfterWrite]
      exact RuntimeFrame.validSlotValue_update_of_not_reaches hvalidOld
        (hotherFrames y otherEnvSlot oldValue hyx henvY hstoreY)
  exact preservation_assign_var_old_nonOwner_step_runtime_of_preserved
    (lifetime := lifetime) hsafe hvalidRuntime henvX hwriteEnv hnonOwner
    hvalidValue hread hwrite hdrops hnewValid hpreserveOther

theorem preservation_assign_var_envShape_step_runtime_of_frames
    {store storeAfterWrite store' : ProgramStore} {env env' : Env}
    {lifetime : Lifetime} {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    (envSlot.ty = .ty .unit ∨ envSlot.ty = .ty .int ∨ envSlot.ty = .ty .bool ∨
      (∃ inner, envSlot.ty = .undef inner) ∨
      ∃ mutable targets, envSlot.ty = .ty (.borrow mutable targets)) →
    ValidValue store value ty →
    store.read (.var x) = some oldSlot →
    store.write (.var x) (.value value) = some storeAfterWrite →
    Drops storeAfterWrite [oldSlot.value] store' →
    (∀ ℓ, RuntimeFrame.Reaches store (.value value) (.ty ty) ℓ →
      ℓ ≠ VariableProjection x) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ ℓ, RuntimeFrame.Reaches store oldValue otherEnvSlot.ty ℓ →
        ℓ ≠ VariableProjection x) →
    ValidRuntimeState store' (.val .unit) ∧ store' ∼ₛ env' ∧
      ValidValue store' .unit .unit := by
  intro hsafe hvalidRuntime henvX hwriteEnv hshape hvalidValue
    hread hwrite hdrops hvalueFrame hotherFrames
  have hnonOwner : PartialValueNonOwner oldSlot.value :=
    safeAbstraction_var_read_nonOwner_of_envShape hsafe henvX hread hshape
  exact preservation_assign_var_old_nonOwner_step_runtime_of_frames
    (lifetime := lifetime) hsafe hvalidRuntime henvX hwriteEnv hnonOwner
    hvalidValue hread hwrite hdrops hvalueFrame hotherFrames

theorem preservation_blockB_value_step_runtime_no_slots
    {store store' : ProgramStore} {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    store ∼ₛ env →
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ blockLifetime) →
    Step store lifetime (.block blockLifetime [.val value]) store' (.val value) →
    ValidValue store' value ty →
    ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env' ∧
      ValidValue store' value ty := by
  intro hvalidRuntime hsafe htyping hnoLifetime hstep hvalidValue
  have henv' : env' = env.dropLifetime blockLifetime := by
    exact blockValueTyping_output_eq htyping
  have hdropDisjoint : LifetimeDropOwnersDisjoint store blockLifetime :=
    lifetimeDropOwnersDisjoint_of_no_slots hnoLifetime
  have hsafe' : store' ∼ₛ env.dropLifetime blockLifetime := by
    cases hstep with
    | blockB hdrops =>
        exact safeAbstraction_dropsLifetime_no_slots hsafe hnoLifetime hdrops
  exact ⟨validRuntimeState_blockB_step hvalidRuntime hdropDisjoint hstep,
    by
      rw [henv']
      exact hsafe',
    hvalidValue⟩

/-! ### Multistep Preservation Fragments -/

/-- Lemma 4.11, multistep preservation for `R-Copy` redexes, safe-only form. -/
theorem preservation_copy_multistep_runtime_of_safe {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {finalValue : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.copy lv) →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    MultiStep store lifetime (.copy lv) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hsafe hvalidRuntime htyping hmulti
  exact preservation_runtime_multistep_of_step_to_value
    (by intro hterminal; simp [Terminal] at hterminal)
    (by
      intro _store' _term' hstep
      cases hstep with
      | copy _hread =>
          exact ⟨_, rfl⟩)
    (by
      intro _store' _value hstep
      cases hstep with
      | copy hread =>
          exact preservation_copy_step_runtime_of_safe hsafe hvalidRuntime htyping
            (Step.copy (lifetime := lifetime) hread))
    hmulti

/-- Lemma 4.11, multistep preservation for `R-Copy` redexes. -/
theorem preservation_copy_multistep_runtime {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {finalValue : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidRuntimeState store (.copy lv) →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    MultiStep store lifetime (.copy lv) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro _hwellFormed hsafe hvalidRuntime htyping hmulti
  exact preservation_copy_multistep_runtime_of_safe hsafe hvalidRuntime htyping hmulti

/-- Lemma 4.11, multistep preservation for `R-Borrow` redexes. -/
theorem preservation_borrow_multistep_runtime {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {mutable : Bool} {finalValue : Value} :
    store ∼ₛ env →
    ValidRuntimeState store (.borrow mutable lv) →
    TermTyping env typing lifetime (.borrow mutable lv)
      (.borrow mutable [lv]) env₂ →
    MultiStep store lifetime (.borrow mutable lv) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue (.borrow mutable [lv]) := by
  intro hsafe hvalidRuntime htyping hmulti
  exact preservation_runtime_multistep_of_step_to_value
    (by intro hterminal; simp [Terminal] at hterminal)
    (by
      intro _store' _term' hstep
      cases hstep with
      | borrow _hloc =>
          exact ⟨_, rfl⟩)
    (by
      intro _store' _value hstep
      cases hstep with
      | borrow hloc =>
          exact preservation_borrow_step_runtime hsafe hvalidRuntime htyping
            (Step.borrow (lifetime := lifetime) hloc))
    hmulti

/-- Lemma 4.11, multistep preservation for `R-Box` redexes. -/
theorem preservation_box_multistep_runtime {store finalStore : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    ValidStoreTyping store (.box (.val value)) typing →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.box (.val value)) →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    MultiStep store lifetime (.box (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue (.box ty) := by
  intro hvalidStoreTyping hsafe hvalidRuntime htyping hmulti
  exact preservation_runtime_multistep_of_step_to_value
    (term := .box (.val value))
    (ty := .box ty)
    (by simp [Terminal])
    (by
      intro _store' _term' hstep
      cases hstep with
      | box _hfresh _hbox =>
          exact ⟨_, rfl⟩
      | subBox hvalueStep =>
          exact False.elim (value_no_step hvalueStep))
    (by
      intro _store' _value hstep
      cases hstep with
      | box hfresh hbox =>
          exact preservation_box_step_runtime hvalidStoreTyping hsafe hvalidRuntime htyping
            (Step.box (lifetime := lifetime) hfresh hbox))
    hmulti

/--
Lemma 4.11, `T-Box` composition step.

This is the induction-over-constructor shape for `box t`: apply the preservation
induction hypothesis to the operand until it is a value, then apply `R-Box`.
-/
theorem preservation_box_context_multistep_runtime
    {store midStore finalStore : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {value finalValue : Value} {ty : Ty} :
    (ValidRuntimeState store term →
      ValidStoreTyping store term typing →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime term ty env₂ →
      MultiStep store lifetime term midStore (.val value) →
      ValidRuntimeState midStore (.val value) ∧ midStore ∼ₛ env₂ ∧
        ValidValue midStore value ty) →
    ValidRuntimeState store (.box term) →
    ValidStoreTyping store (.box term) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    MultiStep store lifetime term midStore (.val value) →
    Step midStore lifetime (.box (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue (.box ty) := by
  intro hinnerPreservation hvalidRuntime hvalidStoreTyping hsafe htyping hinnerMulti hboxStep
  cases htyping with
  | box hinnerTyping =>
      rcases hinnerPreservation
          (validRuntimeState_box_inner hvalidRuntime)
          (validStoreTyping_box_inner hvalidStoreTyping)
          hsafe hinnerTyping hinnerMulti with
        ⟨hvalidInner, hsafeInner, hvalidValue⟩
      cases hboxStep with
      | box hfresh hbox =>
          exact preservation_box_redex_runtime_of_validValue hsafeInner
            (validRuntimeState_box_value_of_value hvalidInner)
            hvalidValue
            (Step.box (lifetime := lifetime) hfresh hbox)

/--
Lemma 4.11, `T-Box` multistep preservation case.

This packages the operational decomposition of a terminal `box t` reduction with
the constructor-shaped preservation composition above.
-/
theorem preservation_box_context_terminal_multistep_runtime
    {store finalStore : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {finalValue : Value} {ty : Ty} :
    (∀ {midStore value},
      ValidRuntimeState store term →
      ValidStoreTyping store term typing →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime term ty env₂ →
      MultiStep store lifetime term midStore (.val value) →
      ValidRuntimeState midStore (.val value) ∧ midStore ∼ₛ env₂ ∧
        ValidValue midStore value ty) →
    ValidRuntimeState store (.box term) →
    ValidStoreTyping store (.box term) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    MultiStep store lifetime (.box term) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue (.box ty) := by
  intro hinnerPreservation hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
  rcases multistep_box_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hboxStep⟩
  exact preservation_box_context_multistep_runtime
    (midStore := midStore)
    (value := value)
    (by
      intro hvalidInner hvalidStoreTypingInner hsafeInner hinnerTyping hmultiInner
      exact hinnerPreservation hvalidInner hvalidStoreTypingInner hsafeInner
        hinnerTyping hmultiInner)
    hvalidRuntime hvalidStoreTyping hsafe htyping hinnerMulti hboxStep

/-- Lemma 4.11, multistep preservation for `R-Declare` redexes. -/
theorem preservation_declare_multistep_runtime {store finalStore : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {value finalValue : Value} :
    ValidStoreTyping store (.letMut x (.val value)) typing →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.letMut x (.val value)) →
    TermTyping env₁ typing lifetime (.letMut x (.val value)) .unit env₃ →
    MultiStep store lifetime (.letMut x (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hvalidStoreTyping hsafe hvalidRuntime htyping hmulti
  exact preservation_runtime_multistep_of_step_to_value
    (term := .letMut x (.val value))
    (ty := .unit)
    (by simp [Terminal])
    (by
      intro _store' _term' hstep
      cases hstep with
      | declare _hstore =>
          exact ⟨.unit, rfl⟩
      | subDeclare hvalueStep =>
          exact False.elim (value_no_step hvalueStep))
    (by
      intro _store' _value hstep
      cases hstep with
      | declare hstore =>
          exact preservation_declare_step_runtime hvalidStoreTyping hsafe hvalidRuntime htyping
              (Step.declare (lifetime := lifetime) hstore))
    hmulti

theorem preservation_blockB_value_multistep_runtime_no_slots
    {store finalStore : ProgramStore} {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    store ∼ₛ env →
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ blockLifetime) →
    ValidValue store value ty →
    MultiStep store lifetime (.block blockLifetime [.val value]) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env' ∧
      ValidValue finalStore finalValue ty := by
  intro hvalidRuntime hsafe htyping hnoLifetime hvalidValue hmulti
  exact preservation_runtime_multistep_of_step_to_value
    (term := .block blockLifetime [.val value])
    (ty := ty)
    (by simp [Terminal])
    (by
      intro _store' _term' hstep
      cases hstep with
      | blockA hvalueStep =>
          exact False.elim (value_no_step hvalueStep)
      | blockB _hdrops =>
          exact ⟨value, rfl⟩)
    (by
      intro _store' _value hstep
      cases hstep with
      | blockB hdrops =>
          have hstore : _store' = store :=
            dropsLifetime_no_slots_eq hnoLifetime hdrops
          have hvalidValue' : ValidValue _store' value ty := by
            rw [hstore]
            exact hvalidValue
          exact preservation_blockB_value_step_runtime_no_slots
            hvalidRuntime hsafe htyping hnoLifetime
            (Step.blockB (lifetime := lifetime) hdrops)
            hvalidValue')
    hmulti

theorem preservation_block_terminal_multistep_runtime_of_first_step
    {store finalStore : ProgramStore} {env' : Env}
    {lifetime blockLifetime : Lifetime} {terms : List Term}
    {finalValue : Value} {ty : Ty} :
    (∀ value next rest store',
      terms = .val value :: next :: rest →
      Drops store [.value value] store' →
      MultiStep store' lifetime (.block blockLifetime (next :: rest))
        finalStore (.val finalValue) →
      ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env' ∧
        ValidValue finalStore finalValue ty) →
    (∀ term rest store' term',
      terms = term :: rest →
      Step store blockLifetime term store' term' →
      MultiStep store' lifetime (.block blockLifetime (term' :: rest))
        finalStore (.val finalValue) →
      ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env' ∧
        ValidValue finalStore finalValue ty) →
    (∀ value store',
      terms = [.val value] →
      DropsLifetime store blockLifetime store' →
      MultiStep store' lifetime (.val value) finalStore (.val finalValue) →
      ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env' ∧
        ValidValue finalStore finalValue ty) →
    MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env' ∧
      ValidValue finalStore finalValue ty := by
  intro hseq hblockA hblockB hmulti
  rcases multistep_block_to_value_first_step_inv hmulti with
    hseqCase | hblockACase | hblockBCase
  · rcases hseqCase with ⟨value, next, rest, store', hterms, hdrops, htail⟩
    exact hseq value next rest store' hterms hdrops htail
  · rcases hblockACase with ⟨term, rest, store', term', hterms, hstep, htail⟩
    exact hblockA term rest store' term' hterms hstep htail
  · rcases hblockBCase with ⟨value, store', hterms, hdrops, htail⟩
    exact hblockB value store' hterms hdrops htail

end Paper
end LwRust
