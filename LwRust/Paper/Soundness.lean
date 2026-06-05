import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import LwRust.Paper.InductiveSemantics
import LwRust.Paper.Typing

/-!
Soundness infrastructure for the core FR calculus.

This file starts with Section 4.1's validity definitions.  Later sections build
on these with safe abstractions, progress, preservation, and the final
type-and-borrow safety theorem.
-/

namespace LwRust
namespace Paper

open Core

/--
The owned heap/variable location, if this runtime value is an owning reference.
Borrowed references and scalar values do not contribute ownership occurrences.
-/
def valueOwnedLocation? : Value → Option Location
  | .ref { location, owner := true } => some location
  | _ => none

def valueOwningLocations (value : Value) : List Location :=
  match valueOwnedLocation? value with
  | some location => [location]
  | none => []

def partialValueOwningLocations : PartialValue → List Location
  | .value value => valueOwningLocations value
  | .undef => []

def partialValuesOwningLocations (values : List PartialValue) : List Location :=
  List.flatMap partialValueOwningLocations values

def owningRef (location : Location) : Value :=
  .ref { location := location, owner := true }

def PartialValueNonOwner (value : PartialValue) : Prop :=
  ∀ ref, value ≠ .value (.ref ref) ∨ ref.owner = false

@[simp] theorem partialValueNonOwner_undef :
    PartialValueNonOwner .undef := by
  intro ref
  exact Or.inl (by simp)

@[simp] theorem partialValueNonOwner_unit :
    PartialValueNonOwner (.value .unit) := by
  intro ref
  exact Or.inl (by simp)

@[simp] theorem partialValueNonOwner_int (value : Int) :
    PartialValueNonOwner (.value (.int value)) := by
  intro ref
  exact Or.inl (by simp)

@[simp] theorem partialValueNonOwner_borrowed (location : Location) :
    PartialValueNonOwner (.value (.ref { location := location, owner := false })) := by
  intro ref
  by_cases href :
      PartialValue.value (Value.ref { location := location, owner := false }) =
        PartialValue.value (Value.ref ref)
  · exact Or.inr (by
      injection href with hrefValue
      cases ref
      cases hrefValue
      rfl)
  · exact Or.inl href

theorem not_partialValueNonOwner_owning_ref {ref : Reference} :
    ref.owner = true →
    ¬ PartialValueNonOwner (.value (.ref ref)) := by
  intro howner hnonOwner
  rcases hnonOwner ref with hne | hborrowed
  · exact hne rfl
  · rw [howner] at hborrowed
    contradiction

theorem mem_valueOwningLocations_of_eq_owningRef {value : Value} {owned : Location} :
    value = owningRef owned →
    owned ∈ valueOwningLocations value := by
  intro hvalue
  subst hvalue
  simp [valueOwningLocations, valueOwnedLocation?, owningRef]

theorem eq_owningRef_of_mem_valueOwningLocations {value : Value} {owned : Location} :
    owned ∈ valueOwningLocations value →
    value = owningRef owned := by
  intro hmem
  cases value with
  | unit =>
      simp [valueOwningLocations, valueOwnedLocation?] at hmem
  | int _ =>
      simp [valueOwningLocations, valueOwnedLocation?] at hmem
  | ref ref =>
      cases ref with
      | mk location owner =>
          cases owner <;> simp [valueOwningLocations, valueOwnedLocation?, owningRef] at hmem ⊢
          exact hmem.symm

theorem mem_partialValueOwningLocations_of_eq_owningRef
    {value : PartialValue} {owned : Location} :
    value = .value (owningRef owned) →
    owned ∈ partialValueOwningLocations value := by
  intro hvalue
  subst hvalue
  simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?,
    owningRef]

theorem mem_partialValueOwningLocations_ref_true {ref : Reference} :
    ref.owner = true →
    ref.location ∈ partialValueOwningLocations (.value (.ref ref)) := by
  intro howner
  cases ref with
  | mk location owner =>
      cases owner <;> simp [partialValueOwningLocations, valueOwningLocations,
        valueOwnedLocation?] at howner ⊢

theorem eq_location_of_mem_lifetime_drop_value {dropValue : PartialValue}
    {owned location : Location} :
    dropValue = .value (.ref { location := location, owner := true }) →
    owned ∈ partialValueOwningLocations dropValue →
    owned = location := by
  intro hvalue hmem
  subst hvalue
  simpa [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] using hmem

theorem eq_owningRef_of_mem_partialValueOwningLocations
    {value : PartialValue} {owned : Location} :
    owned ∈ partialValueOwningLocations value →
    value = .value (owningRef owned) := by
  intro hmem
  cases value with
  | undef =>
      simp [partialValueOwningLocations] at hmem
  | value value =>
      exact congrArg PartialValue.value
        (eq_owningRef_of_mem_valueOwningLocations
          (by simpa [partialValueOwningLocations] using hmem))

/--
Runtime values contained in a term.  This follows Definition 4.1's sequence
`v ∈ t`; in the core calculus, values occur directly as `Term.val` and inside
subterms.
-/
def termValues : Term → List Value
  | .block _ terms => List.flatMap termValues terms
  | .letMut _ initialiser => termValues initialiser
  | .assign _ rhs => termValues rhs
  | .box operand => termValues operand
  | .borrow _ _ => []
  | .move _ => []
  | .copy _ => []
  | .val value => [value]

def termOwningLocations (term : Term) : List Location :=
  List.flatMap valueOwningLocations (termValues term)

namespace ProgramStore

/--
`StoreOwns S ℓ storage` means the slot at `storage` contains an owning reference
to location `ℓ`.
-/
def OwnsAt (store : ProgramStore) (owned storage : Location) : Prop :=
  ∃ lifetime,
    store.slotAt storage =
      some (StoreSlot.mk (PartialValue.value (owningRef owned)) lifetime)

def Owns (store : ProgramStore) (owned : Location) : Prop :=
  ∃ storage, ProgramStore.OwnsAt store owned storage

end ProgramStore

/--
Definition 4.1, valid term.  A term is valid when it does not contain two
owning references to the same location.
-/
def ValidTerm (term : Term) : Prop :=
  (termOwningLocations term).Nodup

/--
Definition 4.2, valid store.  A store is valid when no two distinct store slots
contain owning references to the same location.

Because `ProgramStore` is an abstract partial map rather than an executable
finite map, we state this as a uniqueness property over possible slot lookups.
-/
def ValidStore (store : ProgramStore) : Prop :=
  ∀ owned storage₁ storage₂,
    ProgramStore.OwnsAt store owned storage₁ →
    ProgramStore.OwnsAt store owned storage₂ →
    storage₁ = storage₂

/--
Auxiliary well-formedness for the abstract partial-map store: every owning
reference contained in a store slot points at an allocated location.

The paper's store model treats references as locations into storage; this
predicate makes that implicit allocation invariant explicit for our abstract
`ProgramStore`.
-/
def StoreOwnersAllocated (store : ProgramStore) : Prop :=
  ∀ owned,
    ProgramStore.Owns store owned →
    ∃ slot, store.slotAt owned = some slot

/--
No store owner points at a location allocated in `lifetime`.  This is the
runtime side condition needed for preserving owner allocation through
`drop(S, lifetime)` with an abstract store.
-/
def LifetimeDropOwnersDisjoint (store : ProgramStore) (lifetime : Lifetime) : Prop :=
  ∀ location slot,
    store.slotAt location = some slot →
    slot.lifetime = lifetime →
    ¬ ProgramStore.Owns store location

/--
Definition 4.3, valid state.  A program state is valid when both components are
valid and no owning reference appears in both the store and the term.
-/
def ValidState (store : ProgramStore) (term : Term) : Prop :=
  ValidStore store ∧
  ValidTerm term ∧
  ∀ owned,
    owned ∈ termOwningLocations term →
    ¬ ProgramStore.Owns store owned

/--
Runtime validity package used by the mechanised preservation proof.

`ValidState` follows Definition 4.3.  `StoreOwnersAllocated` makes explicit the
allocation invariant that the paper's store model leaves implicit.
-/
def ValidRuntimeState (store : ProgramStore) (term : Term) : Prop :=
  ValidState store term ∧ StoreOwnersAllocated store

theorem ValidState.validStore {store : ProgramStore} {term : Term} :
    ValidState store term → ValidStore store := by
  intro hvalid
  exact hvalid.1

theorem ValidState.validTerm {store : ProgramStore} {term : Term} :
    ValidState store term → ValidTerm term := by
  intro hvalid
  exact hvalid.2.1

theorem ValidState.storeTermDisjoint {store : ProgramStore} {term : Term} :
    ValidState store term →
    ∀ owned,
      owned ∈ termOwningLocations term →
      ¬ ProgramStore.Owns store owned := by
  intro hvalid
  exact hvalid.2.2

theorem ValidRuntimeState.validState {store : ProgramStore} {term : Term} :
    ValidRuntimeState store term → ValidState store term := by
  intro hvalid
  exact hvalid.1

theorem ValidRuntimeState.storeOwnersAllocated {store : ProgramStore} {term : Term} :
    ValidRuntimeState store term → StoreOwnersAllocated store := by
  intro hvalid
  exact hvalid.2

theorem validState_box_inner {store : ProgramStore} {term : Term} :
    ValidState store (.box term) →
    ValidState store term := by
  intro hvalid
  simpa [ValidState, ValidTerm, termOwningLocations, termValues] using hvalid

theorem validRuntimeState_box_inner {store : ProgramStore} {term : Term} :
    ValidRuntimeState store (.box term) →
    ValidRuntimeState store term := by
  intro hvalid
  exact ⟨validState_box_inner hvalid.1, hvalid.2⟩

theorem validState_box_value_of_value {store : ProgramStore} {value : Value} :
    ValidState store (.val value) →
    ValidState store (.box (.val value)) := by
  intro hvalid
  simpa [ValidState, ValidTerm, termOwningLocations, termValues] using hvalid

theorem validRuntimeState_box_value_of_value {store : ProgramStore} {value : Value} :
    ValidRuntimeState store (.val value) →
    ValidRuntimeState store (.box (.val value)) := by
  intro hvalid
  exact ⟨validState_box_value_of_value hvalid.1, hvalid.2⟩

theorem validState_declare_value_of_value {store : ProgramStore} {x : Name}
    {value : Value} :
    ValidState store (.val value) →
    ValidState store (.letMut x (.val value)) := by
  intro hvalid
  simpa [ValidState, ValidTerm, termOwningLocations, termValues] using hvalid

theorem validRuntimeState_declare_value_of_value {store : ProgramStore} {x : Name}
    {value : Value} :
    ValidRuntimeState store (.val value) →
    ValidRuntimeState store (.letMut x (.val value)) := by
  intro hvalid
  exact ⟨validState_declare_value_of_value hvalid.1, hvalid.2⟩

theorem validState_declare_inner {store : ProgramStore} {x : Name} {term : Term} :
    ValidState store (.letMut x term) →
    ValidState store term := by
  intro hvalid
  simpa [ValidState, ValidTerm, termOwningLocations, termValues] using hvalid

theorem validRuntimeState_declare_inner {store : ProgramStore} {x : Name}
    {term : Term} :
    ValidRuntimeState store (.letMut x term) →
    ValidRuntimeState store term := by
  intro hvalid
  exact ⟨validState_declare_inner hvalid.1, hvalid.2⟩

theorem validState_assign_value_of_value {store : ProgramStore} {lhs : LVal}
    {value : Value} :
    ValidState store (.val value) →
    ValidState store (.assign lhs (.val value)) := by
  intro hvalid
  simpa [ValidState, ValidTerm, termOwningLocations, termValues] using hvalid

theorem validRuntimeState_assign_value_of_value {store : ProgramStore} {lhs : LVal}
    {value : Value} :
    ValidRuntimeState store (.val value) →
    ValidRuntimeState store (.assign lhs (.val value)) := by
  intro hvalid
  exact ⟨validState_assign_value_of_value hvalid.1, hvalid.2⟩

theorem validState_assign_inner {store : ProgramStore} {lhs : LVal} {rhs : Term} :
    ValidState store (.assign lhs rhs) →
    ValidState store rhs := by
  intro hvalid
  simpa [ValidState, ValidTerm, termOwningLocations, termValues] using hvalid

theorem validRuntimeState_assign_inner {store : ProgramStore} {lhs : LVal}
    {rhs : Term} :
    ValidRuntimeState store (.assign lhs rhs) →
    ValidRuntimeState store rhs := by
  intro hvalid
  exact ⟨validState_assign_inner hvalid.1, hvalid.2⟩

theorem ValidRuntimeState.validStore {store : ProgramStore} {term : Term} :
    ValidRuntimeState store term → ValidStore store := by
  intro hvalid
  exact hvalid.validState.validStore

theorem ValidRuntimeState.validTerm {store : ProgramStore} {term : Term} :
    ValidRuntimeState store term → ValidTerm term := by
  intro hvalid
  exact hvalid.validState.validTerm

theorem ValidRuntimeState.storeTermDisjoint {store : ProgramStore} {term : Term} :
    ValidRuntimeState store term →
    ∀ owned,
      owned ∈ termOwningLocations term →
      ¬ ProgramStore.Owns store owned := by
  intro hvalid
  exact hvalid.validState.storeTermDisjoint

theorem validTerm_value_nonOwner {value : Value} :
    valueOwnedLocation? value = none →
    ValidTerm (.val value) := by
  intro h
  simp [ValidTerm, termOwningLocations, termValues, valueOwningLocations, h]

theorem validTerm_value (value : Value) :
    ValidTerm (.val value) := by
  cases value with
  | unit =>
      simp [ValidTerm, termOwningLocations, termValues, valueOwningLocations,
        valueOwnedLocation?]
  | int _ =>
      simp [ValidTerm, termOwningLocations, termValues, valueOwningLocations,
        valueOwnedLocation?]
  | ref ref =>
      cases ref with
      | mk location owner =>
          cases owner <;>
            simp [ValidTerm, termOwningLocations, termValues, valueOwningLocations,
              valueOwnedLocation?]

@[simp] theorem validTerm_unit :
    ValidTerm (.val .unit) := by
  exact validTerm_value_nonOwner rfl

@[simp] theorem validTerm_int (value : Int) :
    ValidTerm (.val (.int value)) := by
  exact validTerm_value_nonOwner rfl

/-- Definition 4.1 excludes two owning references to the same location in one term. -/
theorem invalidTerm_duplicateOwner (location : Location) (lifetime : Lifetime) :
    ¬ ValidTerm
      (.block lifetime [.val (owningRef location), .val (owningRef location)]) := by
  simp [ValidTerm, termOwningLocations, termValues, valueOwningLocations,
    valueOwnedLocation?, owningRef]

/--
Definition 4.3 excludes the paper's motivating invalid-state shape: an owning
reference to the same location appears both in the store and in the term.
-/
theorem invalidState_storeTerm_duplicateOwner
    (owned storage : Location) (lifetime : Lifetime) :
    ¬ ValidState
      (ProgramStore.empty.update storage
        { value := .value (owningRef owned), lifetime := lifetime })
      (.val (owningRef owned)) := by
  intro hvalid
  exact hvalid.storeTermDisjoint owned
    (by simp [termOwningLocations, termValues, valueOwningLocations,
      valueOwnedLocation?, owningRef])
    (by
      exact ⟨storage, lifetime, by simp [ProgramStore.update, owningRef]⟩)

/-- Definition 4.2 excludes two distinct store slots owning the same location. -/
theorem invalidStore_duplicateOwner {owned storage₁ storage₂ : Location}
    {lifetime₁ lifetime₂ : Lifetime} :
    storage₁ ≠ storage₂ →
    ¬ ValidStore
      ((ProgramStore.empty.update storage₁
          { value := .value (owningRef owned), lifetime := lifetime₁ }).update storage₂
        { value := .value (owningRef owned), lifetime := lifetime₂ }) := by
  intro hne hvalid
  exact hne (hvalid owned storage₁ storage₂
    ⟨lifetime₁, by simp [ProgramStore.update, hne, owningRef]⟩
    ⟨lifetime₂, by simp [ProgramStore.update, owningRef]⟩)

@[simp] theorem validStore_empty :
    ValidStore ProgramStore.empty := by
  intro owned storage₁ storage₂ h₁
  rcases h₁ with ⟨lifetime, hslot⟩
  simp [ProgramStore.empty] at hslot

@[simp] theorem storeOwnersAllocated_empty :
    StoreOwnersAllocated ProgramStore.empty := by
  intro owned howns
  rcases howns with ⟨storage, lifetime, hslot⟩
  simp [ProgramStore.empty] at hslot

theorem not_owns_of_fresh_of_storeOwnersAllocated {store : ProgramStore}
    {owned : Location} :
    StoreOwnersAllocated store →
    store.fresh owned →
    ¬ ProgramStore.Owns store owned := by
  intro hallocated hfresh howns
  rcases hallocated owned howns with ⟨slot, hslot⟩
  rw [ProgramStore.fresh] at hfresh
  rw [hfresh] at hslot
  cases hslot

/-- Erasing a store location cannot create a new owning reference. -/
theorem ownsAt_erase {store : ProgramStore} {owned storage erased : Location} :
    ProgramStore.OwnsAt (store.erase erased) owned storage →
    storage ≠ erased ∧ ProgramStore.OwnsAt store owned storage := by
  intro howns
  rcases howns with ⟨lifetime, hslot⟩
  by_cases hsame : storage = erased
  · subst hsame
    simp [ProgramStore.erase] at hslot
  · exact ⟨hsame, ⟨lifetime, by
      simpa [ProgramStore.erase, hsame] using hslot⟩⟩

/-- Lemma 9.8 support: erasing a location preserves store validity. -/
theorem validStore_erase {store : ProgramStore} {erased : Location} :
    ValidStore store →
    ValidStore (store.erase erased) := by
  intro hvalid owned storage₁ storage₂ h₁ h₂
  rcases ownsAt_erase h₁ with ⟨_hne₁, hstore₁⟩
  rcases ownsAt_erase h₂ with ⟨_hne₂, hstore₂⟩
  exact hvalid owned storage₁ storage₂ hstore₁ hstore₂

/-- Erasing a store location cannot create ownership of any location. -/
theorem owns_erase {store : ProgramStore} {owned erased : Location} :
    ProgramStore.Owns (store.erase erased) owned →
    ProgramStore.Owns store owned := by
  intro howns
  rcases howns with ⟨storage, hownsAt⟩
  rcases ownsAt_erase hownsAt with ⟨_hne, hstoreOwnsAt⟩
  exact ⟨storage, hstoreOwnsAt⟩

/--
If a valid store has an owning reference to `owned` at `storage`, then erasing
`storage` removes all store ownership of `owned`.
-/
theorem not_owns_erase_of_ownsAt {store : ProgramStore}
    {owned storage : Location} :
    ValidStore store →
    ProgramStore.OwnsAt store owned storage →
    ¬ ProgramStore.Owns (store.erase storage) owned := by
  intro hvalid hsource howns
  rcases howns with ⟨otherStorage, hownsAt⟩
  rcases ownsAt_erase hownsAt with ⟨hotherNe, hstoreOwns⟩
  exact hotherNe (hvalid owned otherStorage storage hstoreOwns hsource)

/--
Erasing a location preserves owner-allocation when no remaining store slot owns
the erased location.
-/
theorem storeOwnersAllocated_erase_of_not_owns {store : ProgramStore}
    {erased : Location} :
    StoreOwnersAllocated store →
    ¬ ProgramStore.Owns store erased →
    StoreOwnersAllocated (store.erase erased) := by
  intro hallocated hnotOwnsErased owned howns
  have hownsStore : ProgramStore.Owns store owned := owns_erase howns
  rcases hallocated owned hownsStore with ⟨slot, hslot⟩
  by_cases howned : owned = erased
  · subst howned
    exact False.elim (hnotOwnsErased hownsStore)
  · exact ⟨slot, by
      simpa [ProgramStore.erase, howned] using hslot⟩

/--
Updating a location preserves owner-allocation when every owner introduced by
the new slot is allocated in the updated store.
-/
theorem storeOwnersAllocated_update {store : ProgramStore}
    {updatedLocation : Location} {slot : StoreSlot} :
    StoreOwnersAllocated store →
    (∀ owned,
      owned ∈ partialValueOwningLocations slot.value →
      ∃ allocatedSlot, (store.update updatedLocation slot).slotAt owned = some allocatedSlot) →
    StoreOwnersAllocated (store.update updatedLocation slot) := by
  intro hallocated hslotAllocated owned howns
  rcases howns with ⟨storage, slotLifetime, hslot⟩
  by_cases hstorage : storage = updatedLocation
  · have hnewSlot :
        slot = { value := .value (owningRef owned), lifetime := slotLifetime } := by
      simpa [ProgramStore.update, hstorage] using hslot
    exact hslotAllocated owned
      (mem_partialValueOwningLocations_of_eq_owningRef
        (by simpa using congrArg StoreSlot.value hnewSlot))
  · have holdOwns : ProgramStore.Owns store owned := by
      exact ⟨storage, slotLifetime, by
        simpa [ProgramStore.update, hstorage] using hslot⟩
    rcases hallocated owned holdOwns with ⟨allocatedSlot, hallocatedSlot⟩
    by_cases howned : owned = updatedLocation
    · subst howned
      exact ⟨slot, by simp [ProgramStore.update]⟩
    · exact ⟨allocatedSlot, by
        simpa [ProgramStore.update, howned] using hallocatedSlot⟩

/-- Updating a store slot to `undef` cannot create a new owning reference. -/
theorem ownsAt_update_undef {store : ProgramStore} {updated owned storage : Location}
    {updatedLifetime : Lifetime} :
    ProgramStore.OwnsAt
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      owned storage →
    storage ≠ updated ∧ ProgramStore.OwnsAt store owned storage := by
  intro howns
  rcases howns with ⟨slotLifetime, hslot⟩
  by_cases hstorage : storage = updated
  · subst hstorage
    simp [ProgramStore.update] at hslot
  · exact ⟨hstorage, ⟨slotLifetime, by
      simpa [ProgramStore.update, hstorage] using hslot⟩⟩

/-- Updating a store slot to `undef` preserves store validity. -/
theorem validStore_update_undef {store : ProgramStore} {updated : Location}
    {updatedLifetime : Lifetime} :
    ValidStore store →
    ValidStore (store.update updated { value := .undef, lifetime := updatedLifetime }) := by
  intro hvalid owned storage₁ storage₂ h₁ h₂
  rcases ownsAt_update_undef h₁ with ⟨_hne₁, hstore₁⟩
  rcases ownsAt_update_undef h₂ with ⟨_hne₂, hstore₂⟩
  exact hvalid owned storage₁ storage₂ hstore₁ hstore₂

/-- Updating a store slot to `undef` preserves owner-allocation. -/
theorem storeOwnersAllocated_update_undef {store : ProgramStore} {updated : Location}
    {updatedLifetime : Lifetime} :
    StoreOwnersAllocated store →
    StoreOwnersAllocated (store.update updated { value := .undef, lifetime := updatedLifetime }) := by
  intro hallocated
  exact storeOwnersAllocated_update hallocated (by
    intro owned hmem
    simp [partialValueOwningLocations] at hmem)

/-- Writing `undef` through an lval preserves store validity. -/
theorem validStore_write_undef {store store' : ProgramStore} {lv : LVal} :
    ValidStore store →
    store.write lv .undef = some store' →
    ValidStore store' := by
  intro hvalid hwrite
  unfold ProgramStore.write at hwrite
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hwrite
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hwrite
      | some slot =>
          simp [hloc, hslot] at hwrite
          subst hwrite
          exact validStore_update_undef hvalid

/-- Writing `undef` through an lval preserves owner-allocation. -/
theorem storeOwnersAllocated_write_undef {store store' : ProgramStore} {lv : LVal} :
    StoreOwnersAllocated store →
    store.write lv .undef = some store' →
    StoreOwnersAllocated store' := by
  intro hallocated hwrite
  unfold ProgramStore.write at hwrite
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hwrite
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hwrite
      | some slot =>
          simp [hloc, hslot] at hwrite
          subst hwrite
          exact storeOwnersAllocated_update_undef hallocated

/--
If an owning value is moved out of an lval and the lval is overwritten with
`undef`, the resulting store no longer owns that location.
-/
theorem not_owns_after_move_of_owning_read {store store' : ProgramStore}
    {lv : LVal} {value : Value} {owned : Location} {valueLifetime : Lifetime} :
    ValidStore store →
    store.read lv = some { value := .value value, lifetime := valueLifetime } →
    store.write lv .undef = some store' →
    value = owningRef owned →
    ¬ ProgramStore.Owns store' owned := by
  intro hvalid hread hwrite hvalue howns
  unfold ProgramStore.read at hread
  unfold ProgramStore.write at hwrite
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hread
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hread
      | some slot =>
          simp [hloc, hslot] at hread hwrite
          subst hwrite
          have hslotEq :
              slot = { value := .value value, lifetime := valueLifetime } := by
            simpa using hread
          have hsourceOwns :
              ProgramStore.OwnsAt store owned location := by
            have hsourceSlot :
                store.slotAt location =
                  some { value := .value (owningRef owned), lifetime := valueLifetime } := by
              subst hvalue
              simpa [hslotEq] using hslot
            exact ⟨valueLifetime, hsourceSlot⟩
          rcases howns with ⟨storage, hownsAt⟩
          rcases ownsAt_update_undef hownsAt with ⟨hstorageNe, hstoreOwns⟩
          exact hstorageNe (hvalid owned storage location hstoreOwns hsourceOwns)

/-- Lemma 9.8 support: dropping values preserves store validity. -/
theorem drops_validStore {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ValidStore store →
    ValidStore store' := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro hvalid
      exact hvalid
  | nonOwner _hnonOwner _hdrops ih =>
      intro hvalid
      exact ih hvalid
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hvalid
      exact ih hvalid
  | ownerPresent _howner _hslot _hdrops ih =>
      intro hvalid
      exact ih (validStore_erase hvalid)

/-- Dropping values never creates an allocated slot. -/
theorem drops_slotAt_of_slotAt {store store' : ProgramStore}
    {values : List PartialValue} {location : Location} {slot : StoreSlot} :
    Drops store values store' →
    store'.slotAt location = some slot →
    store.slotAt location = some slot := by
  intro hdrops
  induction hdrops generalizing slot with
  | nil =>
      intro hslot
      exact hslot
  | nonOwner _hnonOwner _hdrops ih =>
      intro hslot
      exact ih hslot
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hslot
      exact ih hslot
  | ownerPresent _howner _herasedSlot _hdrops ih =>
      intro hslot
      rename_i storeBefore _storeAfter ref erasedSlot rest
      have herased : (storeBefore.erase ref.location).slotAt location = some slot :=
        ih hslot
      by_cases hlocation : location = ref.location
      · subst hlocation
        simp [ProgramStore.erase] at herased
      · simpa [ProgramStore.erase, hlocation] using herased

/--
`DropsAvoids S ψ ℓ` records that the recursive drop of `ψ` never erases
location `ℓ`.

This is intentionally a structural companion to `Drops`: an owner-present drop
is allowed only when the erased owner location is different from `ℓ`, and the
recursive drop also avoids `ℓ`.
-/
inductive DropsAvoids : ProgramStore → List PartialValue → Location → Prop where
  | nil {store : ProgramStore} {location : Location} :
      DropsAvoids store [] location
  | nonOwner {store : ProgramStore} {value : PartialValue} {rest : List PartialValue}
      {location : Location} :
      (∀ ref, value ≠ .value (.ref ref) ∨ ref.owner = false) →
      DropsAvoids store rest location →
      DropsAvoids store (value :: rest) location
  | ownerMissing {store : ProgramStore} {ref : Reference} {rest : List PartialValue}
      {location : Location} :
      ref.owner = true →
      store.slotAt ref.location = none →
      DropsAvoids store rest location →
      DropsAvoids store (.value (.ref ref) :: rest) location
  | ownerPresent {store : ProgramStore} {ref : Reference} {slot : StoreSlot}
      {rest : List PartialValue} {location : Location} :
      ref.owner = true →
      store.slotAt ref.location = some slot →
      ref.location ≠ location →
      DropsAvoids (store.erase ref.location) (slot.value :: rest) location →
      DropsAvoids store (.value (.ref ref) :: rest) location

theorem dropsAvoids_slotAt_preserved {store store' : ProgramStore}
    {values : List PartialValue} {location : Location} {slot : StoreSlot} :
    Drops store values store' →
    DropsAvoids store values location →
    store.slotAt location = some slot →
    store'.slotAt location = some slot := by
  intro hdrops havoids hslot
  induction hdrops generalizing location slot with
  | nil =>
      exact hslot
  | nonOwner hnonOwner _hdrops ih =>
      cases havoids with
      | nonOwner _havoidsHead havoidsRest =>
          exact ih havoidsRest hslot
      | ownerMissing howner _hmissing _havoidsRest =>
          exact False.elim
            (not_partialValueNonOwner_owning_ref howner hnonOwner)
      | ownerPresent howner _hpresent _hne _havoidsRest =>
          exact False.elim
            (not_partialValueNonOwner_owning_ref howner hnonOwner)
  | ownerMissing howner hmissing _hdrops ih =>
      cases havoids with
      | nonOwner hnonOwner _havoidsRest =>
          exact False.elim
            (not_partialValueNonOwner_owning_ref howner hnonOwner)
      | ownerMissing _howner _hmissing havoidsRest =>
          exact ih havoidsRest hslot
      | ownerPresent _howner hpresent _hne _havoidsRest =>
          rw [hmissing] at hpresent
          cases hpresent
  | ownerPresent howner hpresent _hdrops ih =>
      rename_i storeBefore _storeAfter ref erasedSlot rest
      cases havoids with
      | nonOwner hnonOwner _havoidsRest =>
          exact False.elim
            (not_partialValueNonOwner_owning_ref howner hnonOwner)
      | ownerMissing _howner hmissing _havoidsRest =>
          rw [hpresent] at hmissing
          cases hmissing
      | ownerPresent _howner _hpresent hne havoidsRest =>
          rw [hpresent] at _hpresent
          cases _hpresent
          have herasedSlot :
              (storeBefore.erase ref.location).slotAt location = some slot := by
            simpa [ProgramStore.erase, hne.symm] using hslot
          exact ih havoidsRest herasedSlot

/-- Dropping a non-owning partial value leaves the store unchanged. -/
theorem drops_partialValue_nonOwner_eq {store store' : ProgramStore}
    {value : PartialValue} :
    PartialValueNonOwner value →
    Drops store [value] store' →
    store' = store := by
  intro hnonOwner hdrops
  cases hdrops with
  | nonOwner _hnonOwner hrest =>
      cases hrest
      rfl
  | ownerMissing howner _hmissing _hrest =>
      exact False.elim (not_partialValueNonOwner_owning_ref howner hnonOwner)
  | ownerPresent howner _hpresent _hrest =>
      exact False.elim (not_partialValueNonOwner_owning_ref howner hnonOwner)

/-- Dropping a runtime value with no owning reference leaves the store unchanged. -/
theorem drops_value_nonOwner_eq {store store' : ProgramStore} {value : Value} :
    valueOwnedLocation? value = none →
    Drops store [.value value] store' →
    store' = store := by
  intro hnonOwner hdrops
  exact drops_partialValue_nonOwner_eq (by
    intro ref
    cases value with
    | unit =>
        exact Or.inl (by simp)
    | int _ =>
        exact Or.inl (by simp)
    | ref valueRef =>
        cases valueRef with
        | mk location owner =>
            cases owner with
            | false =>
                by_cases href :
                    PartialValue.value
                      (Value.ref { location := location, owner := false }) =
                    PartialValue.value (Value.ref ref)
                · exact Or.inr (by
                    injection href with hvalue
                    cases ref
                    cases hvalue
                    rfl)
                · exact Or.inl href
            | true =>
                simp [valueOwnedLocation?] at hnonOwner) hdrops

/--
Dropping a list of non-owning partial values leaves the store unchanged.

This is the list-shaped version of Definition 3.4's non-owner case for
`drop(S, ψ)`.
-/
theorem drops_all_nonOwner_eq {store store' : ProgramStore} {values : List PartialValue} :
    (∀ value, value ∈ values → PartialValueNonOwner value) →
    Drops store values store' →
    store' = store := by
  intro hnonOwner hdrops
  induction hdrops with
  | nil =>
      rfl
  | nonOwner _hhead hrest ih =>
      exact ih (by
        intro value hmem
        exact hnonOwner value (by simp [hmem]))
  | ownerMissing howner _hmissing _hrest =>
      exact False.elim
        (not_partialValueNonOwner_owning_ref howner (hnonOwner _ (by simp)))
  | ownerPresent howner _hslot _hrest =>
      exact False.elim
        (not_partialValueNonOwner_owning_ref howner (hnonOwner _ (by simp)))

/-- Lemma 9.8 support: dropping a lifetime preserves store validity. -/
theorem dropsLifetime_validStore {store store' : ProgramStore} {lifetime : Lifetime} :
    DropsLifetime store lifetime store' →
    ValidStore store →
    ValidStore store' := by
  intro hdrops hvalid
  cases hdrops with
  | intro _hdropSet hdrops =>
      exact drops_validStore hdrops hvalid

/-- Dropping a lifetime never creates an allocated slot. -/
theorem dropsLifetime_slotAt_of_slotAt {store store' : ProgramStore}
    {lifetime : Lifetime} {location : Location} {slot : StoreSlot} :
    DropsLifetime store lifetime store' →
    store'.slotAt location = some slot →
    store.slotAt location = some slot := by
  intro hdrops hslot
  cases hdrops with
  | intro _hdropSet hdrops =>
      exact drops_slotAt_of_slotAt hdrops hslot

/--
If no allocated store slot has lifetime `m`, then the lifetime drop
`drop(S, m)` leaves the store unchanged.
-/
theorem dropsLifetime_no_slots_eq {store store' : ProgramStore} {lifetime : Lifetime} :
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ lifetime) →
    DropsLifetime store lifetime store' →
    store' = store := by
  intro hnoLifetime hdrops
  cases hdrops with
  | intro hdropSet hdrops =>
      exact drops_all_nonOwner_eq (store := store) (values := _) (by
        intro value hmem
        rcases (hdropSet value).mp hmem with
          ⟨location, slot, hslot, hlifetime, hvalue⟩
        exact False.elim (hnoLifetime location slot hslot hlifetime)) hdrops

/-- If no slot is allocated in lifetime `m`, then dropping `m` cannot erase an owner target. -/
theorem lifetimeDropOwnersDisjoint_of_no_slots {store : ProgramStore} {lifetime : Lifetime} :
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ lifetime) →
    LifetimeDropOwnersDisjoint store lifetime := by
  intro hnoLifetime location slot hslot hlifetime _howns
  exact hnoLifetime location slot hslot hlifetime

/-- Dropping values cannot create ownership in the resulting store. -/
theorem drops_owns_of_owns {store store' : ProgramStore} {values : List PartialValue}
    {owned : Location} :
    Drops store values store' →
    ProgramStore.Owns store' owned →
    ProgramStore.Owns store owned := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro howns
      exact howns
  | nonOwner _hnonOwner _hdrops ih =>
      intro howns
      exact ih howns
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro howns
      exact ih howns
  | ownerPresent _howner _hslot _hdrops ih =>
      intro howns
      exact owns_erase (ih howns)

/--
Dropping values preserves owner-allocation when the values being dropped are
not already owned by the store.  This is the side condition obtained from
`ValidState` for `R-Seq`.
-/
theorem drops_storeOwnersAllocated_of_disjoint
    {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ValidStore store →
    StoreOwnersAllocated store →
    (∀ owned, owned ∈ partialValuesOwningLocations values →
      ¬ ProgramStore.Owns store owned) →
    StoreOwnersAllocated store' := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro _hvalid hallocated _hdisjoint
      exact hallocated
  | nonOwner _hnonOwner _hdrops ih =>
      intro hvalid hallocated hdisjoint
      exact ih hvalid hallocated (by
        intro owned hmem
        exact hdisjoint owned (by
          simp [partialValuesOwningLocations]
          exact Or.inr (by simpa [partialValuesOwningLocations] using hmem)))
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hvalid hallocated hdisjoint
      exact ih hvalid hallocated (by
        intro owned hmem
        exact hdisjoint owned (by
          simp [partialValuesOwningLocations]
          exact Or.inr (by simpa [partialValuesOwningLocations] using hmem)))
  | ownerPresent howner hslot _hdrops ih =>
      intro hvalid hallocated hdisjoint
      rename_i storeBefore storeAfter ref slot rest
      have hnotOwnsErased : ¬ ProgramStore.Owns storeBefore ref.location := by
        exact hdisjoint ref.location (by
          simp [partialValuesOwningLocations]
          exact Or.inl (mem_partialValueOwningLocations_ref_true howner))
      have hvalidErased : ValidStore (storeBefore.erase ref.location) :=
        validStore_erase hvalid
      have hallocatedErased : StoreOwnersAllocated (storeBefore.erase ref.location) :=
        storeOwnersAllocated_erase_of_not_owns hallocated hnotOwnsErased
      exact ih hvalidErased hallocatedErased (by
        intro owned hmem hownsErased
        simp [partialValuesOwningLocations] at hmem
        rcases hmem with hmemSlot | hmemRest
        · have hslotValue :
              slot.value = .value (owningRef owned) :=
            eq_owningRef_of_mem_partialValueOwningLocations hmemSlot
          have hsourceOwns : ProgramStore.OwnsAt storeBefore owned ref.location := by
            have hslotStruct :
                slot = { value := .value (owningRef owned), lifetime := slot.lifetime } := by
              cases slot with
              | mk slotValue slotLifetime =>
                  cases hslotValue
                  rfl
            exact ⟨slot.lifetime, hslot.trans (congrArg some hslotStruct)⟩
          exact not_owns_erase_of_ownsAt hvalid hsourceOwns hownsErased
        · exact hdisjoint owned (by
            simp [partialValuesOwningLocations, hmemRest])
            (owns_erase hownsErased))

/-- Dropping a lifetime cannot create ownership in the resulting store. -/
theorem dropsLifetime_owns_of_owns {store store' : ProgramStore} {lifetime : Lifetime}
    {owned : Location} :
    DropsLifetime store lifetime store' →
    ProgramStore.Owns store' owned →
    ProgramStore.Owns store owned := by
  intro hdrops howns
  cases hdrops with
  | intro _hdropSet hdrops =>
      exact drops_owns_of_owns hdrops howns

/-- Lifetime dropping preserves owner-allocation under the lifetime-disjointness side condition. -/
theorem dropsLifetime_storeOwnersAllocated
    {store store' : ProgramStore} {lifetime : Lifetime} :
    DropsLifetime store lifetime store' →
    ValidStore store →
    StoreOwnersAllocated store →
    LifetimeDropOwnersDisjoint store lifetime →
    StoreOwnersAllocated store' := by
  intro hdrops hvalid hallocated hdropDisjoint
  cases hdrops with
  | intro hdropSet hdrops =>
      exact drops_storeOwnersAllocated_of_disjoint hdrops hvalid hallocated (by
        intro owned hmem howns
        simp [partialValuesOwningLocations] at hmem
        rcases hmem with ⟨dropValue, hdropValueMem, hownedMem⟩
        rcases (hdropSet dropValue).mp hdropValueMem with
          ⟨location, slot, hslot, hlifetime, hdropValue⟩
        have howned : owned = location :=
          eq_location_of_mem_lifetime_drop_value hdropValue hownedMem
        exact hdropDisjoint location slot hslot hlifetime (by
          simpa [howned] using howns))

/-- Lemma 9.8 support: declaring a fresh variable preserves store validity. -/
theorem validStore_declare {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {value : Value} :
    ValidStore store →
    store.fresh (.var x) →
    (∀ owned, owned ∈ valueOwningLocations value → ¬ ProgramStore.Owns store owned) →
    ValidStore (store.declare x lifetime value) := by
  intro hvalid hfresh hdisjoint owned storage₁ storage₂ h₁ h₂
  rcases h₁ with ⟨slotLifetime₁, hslot₁⟩
  rcases h₂ with ⟨slotLifetime₂, hslot₂⟩
  by_cases hstorage₁ : storage₁ = .var x
  · subst hstorage₁
    by_cases hstorage₂ : storage₂ = .var x
    · exact hstorage₂.symm
    · have hslot₂Old :
          store.slotAt storage₂ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₂ } := by
        simpa [ProgramStore.declare, hstorage₂] using hslot₂
      have hslot₁New :
          { value := .value value, lifetime := lifetime } =
            ({ value := .value (owningRef owned), lifetime := slotLifetime₁ } : StoreSlot) := by
        simpa [ProgramStore.declare] using hslot₁
      have hvalue : value = owningRef owned := by
        have hpartial :
            PartialValue.value value = PartialValue.value (owningRef owned) := by
          simpa using congrArg StoreSlot.value hslot₁New
        injection hpartial with hvalue
      exact False.elim
        (hdisjoint owned (mem_valueOwningLocations_of_eq_owningRef hvalue)
          ⟨storage₂, slotLifetime₂, hslot₂Old⟩)
  · by_cases hstorage₂ : storage₂ = .var x
    · subst hstorage₂
      have hslot₁Old :
          store.slotAt storage₁ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₁ } := by
        simpa [ProgramStore.declare, hstorage₁] using hslot₁
      have hslot₂New :
          { value := .value value, lifetime := lifetime } =
            ({ value := .value (owningRef owned), lifetime := slotLifetime₂ } : StoreSlot) := by
        simpa [ProgramStore.declare] using hslot₂
      have hvalue : value = owningRef owned := by
        have hpartial :
            PartialValue.value value = PartialValue.value (owningRef owned) := by
          simpa using congrArg StoreSlot.value hslot₂New
        injection hpartial with hvalue
      exact False.elim
        (hdisjoint owned (mem_valueOwningLocations_of_eq_owningRef hvalue)
          ⟨storage₁, slotLifetime₁, hslot₁Old⟩)
    · have hslot₁Old :
          store.slotAt storage₁ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₁ } := by
        simpa [ProgramStore.declare, hstorage₁] using hslot₁
      have hslot₂Old :
          store.slotAt storage₂ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₂ } := by
        simpa [ProgramStore.declare, hstorage₂] using hslot₂
      exact hvalid owned storage₁ storage₂ ⟨slotLifetime₁, hslot₁Old⟩
        ⟨slotLifetime₂, hslot₂Old⟩

/-- Lemma 9.8 support: updating a fresh location preserves store validity. -/
theorem validStore_update_fresh {store : ProgramStore} {updatedLocation : Location}
    {slot : StoreSlot} :
    ValidStore store →
    store.fresh updatedLocation →
    (∀ owned, owned ∈ partialValueOwningLocations slot.value →
      ¬ ProgramStore.Owns store owned) →
    ValidStore (store.update updatedLocation slot) := by
  intro hvalid hfresh hdisjoint owned storage₁ storage₂ h₁ h₂
  rcases h₁ with ⟨slotLifetime₁, hslot₁⟩
  rcases h₂ with ⟨slotLifetime₂, hslot₂⟩
  by_cases hstorage₁ : storage₁ = updatedLocation
  ·
    by_cases hstorage₂ : storage₂ = updatedLocation
    · exact hstorage₁.trans hstorage₂.symm
    · have hslot₁New :
          slot =
            ({ value := .value (owningRef owned), lifetime := slotLifetime₁ } : StoreSlot) := by
        simpa [ProgramStore.update, hstorage₁] using hslot₁
      have hslot₂Old :
          store.slotAt storage₂ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₂ } := by
        simpa [ProgramStore.update, hstorage₂] using hslot₂
      have hslotValue : slot.value = .value (owningRef owned) := by
        simpa using congrArg StoreSlot.value hslot₁New
      exact False.elim
        (hdisjoint owned
          (mem_partialValueOwningLocations_of_eq_owningRef hslotValue)
          ⟨storage₂, slotLifetime₂, hslot₂Old⟩)
  · by_cases hstorage₂ : storage₂ = updatedLocation
    · have hslot₁Old :
          store.slotAt storage₁ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₁ } := by
        simpa [ProgramStore.update, hstorage₁] using hslot₁
      have hslot₂New :
          slot =
            ({ value := .value (owningRef owned), lifetime := slotLifetime₂ } : StoreSlot) := by
        simpa [ProgramStore.update, hstorage₂] using hslot₂
      have hslotValue : slot.value = .value (owningRef owned) := by
        simpa using congrArg StoreSlot.value hslot₂New
      exact False.elim
        (hdisjoint owned
          (mem_partialValueOwningLocations_of_eq_owningRef hslotValue)
          ⟨storage₁, slotLifetime₁, hslot₁Old⟩)
    · have hslot₁Old :
          store.slotAt storage₁ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₁ } := by
        simpa [ProgramStore.update, hstorage₁] using hslot₁
      have hslot₂Old :
          store.slotAt storage₂ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₂ } := by
        simpa [ProgramStore.update, hstorage₂] using hslot₂
      exact hvalid owned storage₁ storage₂ ⟨slotLifetime₁, hslot₁Old⟩
        ⟨slotLifetime₂, hslot₂Old⟩

/-- Updating a location with a value whose owners are absent preserves store validity. -/
theorem validStore_update_disjoint {store : ProgramStore} {updatedLocation : Location}
    {slot : StoreSlot} :
    ValidStore store →
    (∀ owned, owned ∈ partialValueOwningLocations slot.value →
      ¬ ProgramStore.Owns store owned) →
    ValidStore (store.update updatedLocation slot) := by
  intro hvalid hdisjoint owned storage₁ storage₂ h₁ h₂
  rcases h₁ with ⟨slotLifetime₁, hslot₁⟩
  rcases h₂ with ⟨slotLifetime₂, hslot₂⟩
  by_cases hstorage₁ : storage₁ = updatedLocation
  ·
    by_cases hstorage₂ : storage₂ = updatedLocation
    · exact hstorage₁.trans hstorage₂.symm
    · have hslot₁New :
          slot =
            ({ value := .value (owningRef owned), lifetime := slotLifetime₁ } : StoreSlot) := by
        simpa [ProgramStore.update, hstorage₁] using hslot₁
      have hslot₂Old :
          store.slotAt storage₂ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₂ } := by
        simpa [ProgramStore.update, hstorage₂] using hslot₂
      have hslotValue : slot.value = .value (owningRef owned) := by
        simpa using congrArg StoreSlot.value hslot₁New
      exact False.elim
        (hdisjoint owned
          (mem_partialValueOwningLocations_of_eq_owningRef hslotValue)
          ⟨storage₂, slotLifetime₂, hslot₂Old⟩)
  · by_cases hstorage₂ : storage₂ = updatedLocation
    · have hslot₁Old :
          store.slotAt storage₁ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₁ } := by
        simpa [ProgramStore.update, hstorage₁] using hslot₁
      have hslot₂New :
          slot =
            ({ value := .value (owningRef owned), lifetime := slotLifetime₂ } : StoreSlot) := by
        simpa [ProgramStore.update, hstorage₂] using hslot₂
      have hslotValue : slot.value = .value (owningRef owned) := by
        simpa using congrArg StoreSlot.value hslot₂New
      exact False.elim
        (hdisjoint owned
          (mem_partialValueOwningLocations_of_eq_owningRef hslotValue)
          ⟨storage₁, slotLifetime₁, hslot₁Old⟩)
    · have hslot₁Old :
          store.slotAt storage₁ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₁ } := by
        simpa [ProgramStore.update, hstorage₁] using hslot₁
      have hslot₂Old :
          store.slotAt storage₂ =
            some { value := .value (owningRef owned), lifetime := slotLifetime₂ } := by
        simpa [ProgramStore.update, hstorage₂] using hslot₂
      exact hvalid owned storage₁ storage₂ ⟨slotLifetime₁, hslot₁Old⟩
        ⟨slotLifetime₂, hslot₂Old⟩

/-- Writing a disjoint partial value through an lval preserves store validity. -/
theorem validStore_write_disjoint {store store' : ProgramStore} {lv : LVal}
    {value : PartialValue} :
    ValidStore store →
    (∀ owned, owned ∈ partialValueOwningLocations value →
      ¬ ProgramStore.Owns store owned) →
    store.write lv value = some store' →
    ValidStore store' := by
  intro hvalid hdisjoint hwrite
  unfold ProgramStore.write at hwrite
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hwrite
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hwrite
      | some slot =>
          simp [hloc, hslot] at hwrite
          subst hwrite
          exact validStore_update_disjoint hvalid hdisjoint

/-- Writing a partial value preserves owner-allocation when its owners are allocated after the write. -/
theorem storeOwnersAllocated_write {store store' : ProgramStore} {lv : LVal}
    {value : PartialValue} :
    StoreOwnersAllocated store →
    (∀ owned,
      owned ∈ partialValueOwningLocations value →
      ∃ allocatedSlot, store'.slotAt owned = some allocatedSlot) →
    store.write lv value = some store' →
    StoreOwnersAllocated store' := by
  intro hallocated hvalueAllocated hwrite
  unfold ProgramStore.write at hwrite
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hwrite
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hwrite
      | some oldSlot =>
          simp [hloc, hslot] at hwrite
          subst hwrite
          exact storeOwnersAllocated_update hallocated hvalueAllocated

/-- Lemma 9.8, `R-BlockB` valid-state preservation fragment. -/
theorem validState_blockB {store store' : ProgramStore}
    {blockLifetime : Lifetime} {value : Value} :
    ValidState store (.block blockLifetime [.val value]) →
    DropsLifetime store blockLifetime store' →
    ValidState store' (.val value) := by
  intro hvalidState hdrops
  rcases hvalidState with ⟨hvalidStore, hvalidTerm, hdisjoint⟩
  exact ⟨dropsLifetime_validStore hdrops hvalidStore,
    by
      simpa [ValidTerm, termOwningLocations, termValues] using hvalidTerm,
    by
      intro owned hmem howns
      exact hdisjoint owned
        (by simpa [termOwningLocations, termValues] using hmem)
        (dropsLifetime_owns_of_owns hdrops howns)⟩

/-- Lemma 9.8, `R-Seq` valid-state preservation fragment. -/
theorem validState_seq_step {store store' : ProgramStore}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    ValidState store (.block blockLifetime (.val value :: next :: rest)) →
    Drops store [.value value] store' →
    ValidState store' (.block blockLifetime (next :: rest)) := by
  intro hvalidState hdrops
  rcases hvalidState with ⟨hvalidStore, hvalidTerm, hdisjoint⟩
  exact ⟨drops_validStore hdrops hvalidStore,
    by
      have hvalidAppend :
          (valueOwningLocations value ++
            termOwningLocations (.block blockLifetime (next :: rest))).Nodup := by
        simpa [ValidTerm, termOwningLocations, termValues] using hvalidTerm
      exact List.Nodup.of_append_right hvalidAppend,
    by
      intro owned hmem howns
      exact hdisjoint owned
        (by
          simp [termOwningLocations, termValues] at hmem ⊢
          exact Or.inr hmem)
        (drops_owns_of_owns hdrops howns)⟩

/-- Lemma 9.8, `R-Declare` valid-state preservation fragment. -/
theorem validState_declare {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {value : Value} :
    ValidState store (.letMut x (.val value)) →
    store.fresh (.var x) →
    ValidState (store.declare x lifetime value) (.val .unit) := by
  intro hvalidState hfresh
  rcases hvalidState with ⟨hvalidStore, _hvalidTerm, hdisjoint⟩
  exact ⟨validStore_declare hvalidStore hfresh (by
      intro owned hmem howns
      exact hdisjoint owned
        (by simpa [termOwningLocations, termValues] using hmem)
        howns),
    validTerm_unit,
    by
      intro owned hmem
      simp [termOwningLocations, termValues, valueOwningLocations,
        valueOwnedLocation?] at hmem⟩

@[simp] theorem empty_owns_false (owned : Location) :
    ¬ ProgramStore.Owns ProgramStore.empty owned := by
  intro h
  rcases h with ⟨storage, lifetime, hslot⟩
  simp [ProgramStore.empty] at hslot

@[simp] theorem empty_no_slots :
    ∀ location slot,
      ProgramStore.empty.slotAt location = some slot →
      False := by
  intro location slot hslot
  simp [ProgramStore.empty] at hslot

theorem empty_no_lifetime_slots (lifetime : Lifetime) :
    ∀ location slot,
      ProgramStore.empty.slotAt location = some slot →
      slot.lifetime ≠ lifetime := by
  intro location slot hslot
  exact False.elim (empty_no_slots location slot hslot)

@[simp] theorem validState_empty_unit :
    ValidState ProgramStore.empty (.val .unit) := by
  exact ⟨validStore_empty, validTerm_unit, by
    intro owned _hmem
    exact empty_owns_false owned⟩

/-! ## Section 4.2: Safe Abstractions -/

/--
Definition 4.4, valid type/value abstraction `S ⊢ v⊥ ∼ T̃`.
-/
inductive ValidPartialValue : ProgramStore → PartialValue → PartialTy → Prop where
  /-- V-Unit. -/
  | unit {store : ProgramStore} :
      ValidPartialValue store (.value .unit) (.ty .unit)
  /-- V-Int. -/
  | int {store : ProgramStore} {value : Int} :
      ValidPartialValue store (.value (.int value)) (.ty .int)
  /-- V-Undef. -/
  | undef {store : ProgramStore} {ty : Ty} :
      ValidPartialValue store .undef (.undef ty)
  /-- V-Borrow. -/
  | borrow {store : ProgramStore} {location : Location} {mutable : Bool}
      {targets : List LVal} {target : LVal} :
      target ∈ targets →
      store.loc target = some location →
      ValidPartialValue store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets))
  /-- V-Box. -/
  | box {store : ProgramStore} {location : Location} {slot : StoreSlot}
      {inner : PartialTy} :
      store.slotAt location = some slot →
      ValidPartialValue store slot.value inner →
      ValidPartialValue store
        (.value (.ref { location := location, owner := true }))
        (.box inner)
  /-- V-Box, full `Box<T>` type. -/
  | boxFull {store : ProgramStore} {location : Location} {slot : StoreSlot}
      {ty : Ty} :
      store.slotAt location = some slot →
      ValidPartialValue store slot.value (.ty ty) →
      ValidPartialValue store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty))

def ValidValue (store : ProgramStore) (value : Value) (ty : Ty) : Prop :=
  ValidPartialValue store (.value value) (.ty ty)

notation:50 store:51 " ⊢ " value:51 " ∼ " ty:51 =>
  ValidPartialValue store value ty

/--
Dropping a list of non-owning partial values preserves existing partial-value
abstractions, since the store is unchanged.
-/
theorem validPartialValue_after_drops_all_nonOwner {store store' : ProgramStore}
    {values : List PartialValue} {value : PartialValue} {ty : PartialTy} :
    (∀ dropped, dropped ∈ values → PartialValueNonOwner dropped) →
    Drops store values store' →
    ValidPartialValue store value ty →
    ValidPartialValue store' value ty := by
  intro hnonOwner hdrops hvalid
  have hstore : store' = store := drops_all_nonOwner_eq hnonOwner hdrops
  subst hstore
  exact hvalid

/--
Definition 4.5, valid store typing `S ▷ t ⊢ σ`.

Our `StoreTyping` is keyed by locations, so this uses the existing
`ValueTyping σ v T` relation to express `σ(v) = T`.
-/
def ValidStoreTyping (store : ProgramStore) (term : Term) (typing : StoreTyping) : Prop :=
  ∀ value,
    value ∈ termValues term →
    ∃ ty, ValueTyping typing value ty ∧ ValidValue store value ty

theorem validStoreTyping_box_inner {store : ProgramStore} {term : Term}
    {typing : StoreTyping} :
    ValidStoreTyping store (.box term) typing →
    ValidStoreTyping store term typing := by
  intro hvalid value hmem
  exact hvalid value (by simpa [termValues] using hmem)

theorem validStoreTyping_declare_inner {store : ProgramStore} {x : Name}
    {term : Term} {typing : StoreTyping} :
    ValidStoreTyping store (.letMut x term) typing →
    ValidStoreTyping store term typing := by
  intro hvalid value hmem
  exact hvalid value (by simpa [termValues] using hmem)

theorem validStoreTyping_assign_inner {store : ProgramStore} {lhs : LVal}
    {rhs : Term} {typing : StoreTyping} :
    ValidStoreTyping store (.assign lhs rhs) typing →
    ValidStoreTyping store rhs typing := by
  intro hvalid value hmem
  exact hvalid value (by simpa [termValues] using hmem)

/--
After `R-Seq` drops a completed head value, the remaining block mentions only
runtime values that were already present in the original block.
-/
theorem validStoreTyping_block_tail {store : ProgramStore} {typing : StoreTyping}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    ValidStoreTyping store (.block blockLifetime (.val value :: next :: rest)) typing →
    ValidStoreTyping store (.block blockLifetime (next :: rest)) typing := by
  intro htyping candidate hmem
  exact htyping candidate (by
    simp [termValues] at hmem ⊢
    exact Or.inr hmem)

theorem validPartialValue_owningLocation_allocated {store : ProgramStore}
    {partialValue : PartialValue} {partialTy : PartialTy} {owned : Location} :
    ValidPartialValue store partialValue partialTy →
    owned ∈ partialValueOwningLocations partialValue →
    ∃ slot, store.slotAt owned = some slot := by
  intro hvalid hmem
  cases hvalid with
  | unit =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | int =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | undef =>
      simp [partialValueOwningLocations] at hmem
  | borrow =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | box hslot _hinner =>
      rename_i location slot inner
      have howned : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] using hmem
      subst howned
      exact ⟨_, hslot⟩
  | boxFull hslot _hinner =>
      rename_i location slot ty
      have howned : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] using hmem
      subst howned
      exact ⟨_, hslot⟩

theorem validPartialValue_nonOwner_of_envShape {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValue store value ty →
    (ty = .ty .unit ∨ ty = .ty .int ∨ (∃ inner, ty = .undef inner) ∨
      ∃ mutable targets, ty = .ty (.borrow mutable targets)) →
    PartialValueNonOwner value := by
  intro hvalid hshape
  cases hvalid with
  | unit =>
      exact partialValueNonOwner_unit
  | int =>
      exact partialValueNonOwner_int _
  | undef =>
      exact partialValueNonOwner_undef
  | borrow =>
      exact partialValueNonOwner_borrowed _
  | box =>
      rcases hshape with hunit | hint | hundef | hborrow
      · cases hunit
      · cases hint
      · rcases hundef with ⟨_inner, hundef⟩
        cases hundef
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow
  | boxFull =>
      rcases hshape with hunit | hint | hundef | hborrow
      · cases hunit
      · cases hint
      · rcases hundef with ⟨_inner, hundef⟩
        cases hundef
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow

theorem partialTy_nonOwnerShape_of_shapeCompatible_right_ty {env : Env}
    {oldTy : PartialTy} {rhsTy : Ty} :
    ShapeCompatible env oldTy (.ty rhsTy) →
    oldTy = .ty .unit ∨ oldTy = .ty .int ∨
      (∃ inner, oldTy = .undef inner) ∨
      ∃ mutable targets, oldTy = .ty (.borrow mutable targets) := by
  intro hshape
  cases hshape with
  | unit =>
      exact Or.inl rfl
  | int =>
      exact Or.inr (Or.inl rfl)
  | borrow =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))
  | undefLeft _hinner =>
      exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))

theorem ty_nonOwnerShape_of_strengthens_shapeCompatible_right_ty {env : Env}
    {selectedTy : Ty} {oldTy : PartialTy} {rhsTy : Ty} :
    PartialTyStrengthens (.ty selectedTy) oldTy →
    ShapeCompatible env oldTy (.ty rhsTy) →
    selectedTy = .unit ∨ selectedTy = .int ∨
      ∃ mutable targets, selectedTy = .borrow mutable targets := by
  intro hstrength hshape
  cases hshape with
  | unit =>
      cases hstrength
      exact Or.inl rfl
  | int =>
      cases hstrength
      exact Or.inr (Or.inl rfl)
  | borrow =>
      cases hstrength with
      | reflex =>
          exact Or.inr (Or.inr ⟨_, _, rfl⟩)
      | borrow _hsubset =>
          exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  | undefLeft hinner =>
      cases hstrength with
      | intoUndef hinnerStrength =>
          cases hinner with
          | unit =>
              cases hinnerStrength
              exact Or.inl rfl
          | int =>
              cases hinnerStrength
              exact Or.inr (Or.inl rfl)
          | borrow =>
              cases hinnerStrength with
              | reflex =>
                  exact Or.inr (Or.inr ⟨_, _, rfl⟩)
              | borrow _hsubset =>
                  exact Or.inr (Or.inr ⟨_, _, rfl⟩)

theorem validValue_owningLocation_allocated {store : ProgramStore}
    {value : Value} {ty : Ty} {owned : Location} :
    ValidValue store value ty →
    owned ∈ valueOwningLocations value →
    ∃ slot, store.slotAt owned = some slot := by
  intro hvalid hmem
  exact validPartialValue_owningLocation_allocated hvalid
    (by simpa [partialValueOwningLocations] using hmem)

theorem validValue_fresh_not_owningLocation {store : ProgramStore}
    {value : Value} {ty : Ty} {owned : Location} :
    ValidValue store value ty →
    store.fresh owned →
    owned ∉ valueOwningLocations value := by
  intro hvalid hfresh hmem
  rcases validValue_owningLocation_allocated hvalid hmem with ⟨slot, hslot⟩
  rw [ProgramStore.fresh] at hfresh
  rw [hfresh] at hslot
  cases hslot

theorem storeOwnersAllocated_update_value_of_validValue {store : ProgramStore}
    {updatedLocation : Location} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    StoreOwnersAllocated
      (store.update updatedLocation { value := .value value, lifetime := lifetime }) := by
  intro hallocated hvalidValue
  exact storeOwnersAllocated_update hallocated (by
    intro owned hmem
    rcases validValue_owningLocation_allocated hvalidValue
        (by simpa [partialValueOwningLocations] using hmem) with
      ⟨allocatedSlot, hallocatedSlot⟩
    by_cases howned : owned = updatedLocation
    · subst howned
      exact ⟨{ value := .value value, lifetime := lifetime }, by
        simp [ProgramStore.update]⟩
    · exact ⟨allocatedSlot, by
        simpa [ProgramStore.update, howned] using hallocatedSlot⟩)

theorem storeOwnersAllocated_declare_of_validValue {store : ProgramStore}
    {x : Name} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    StoreOwnersAllocated (store.declare x lifetime value) := by
  intro hallocated hvalidValue
  exact storeOwnersAllocated_update_value_of_validValue
    (updatedLocation := .var x) hallocated hvalidValue

theorem storeOwnersAllocated_boxAt_of_validValue {store : ProgramStore}
    {address : Nat} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    StoreOwnersAllocated (store.boxAt address value).1 := by
  intro hallocated hvalidValue
  exact storeOwnersAllocated_update_value_of_validValue
    (updatedLocation := .heap address)
    (lifetime := Lifetime.root) hallocated hvalidValue

/-- Writing a valid value through an lval preserves owner allocation. -/
theorem storeOwnersAllocated_write_value_of_validValue {store store' : ProgramStore}
    {lv : LVal} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    store.write lv (.value value) = some store' →
    StoreOwnersAllocated store' := by
  intro hallocated hvalidValue hwrite
  unfold ProgramStore.write at hwrite
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hwrite
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hwrite
      | some slot =>
          simp [hloc, hslot] at hwrite
          subst hwrite
          exact storeOwnersAllocated_update_value_of_validValue hallocated hvalidValue

/-- Definition 4.6, variable projection `Θ`. -/
def VariableProjection (name : Name) : Location :=
  .var name

/--
Definition 4.7, safe abstraction `S ∼ Γ`.

Heap locations are intentionally ignored in the domain agreement, as in the
paper.  Because stores and environments are abstract partial maps, domain
agreement is stated pointwise for variable locations.
-/
def SafeAbstraction (store : ProgramStore) (env : Env) : Prop :=
  (∀ x, (∃ slot, store.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, env.slotAt x = some envSlot) ∧
  ∀ x envSlot,
    env.slotAt x = some envSlot →
    ∃ value,
      store.slotAt (VariableProjection x) =
        some (StoreSlot.mk value envSlot.lifetime) ∧
      ValidPartialValue store value envSlot.ty

infix:50 " ∼ₛ " => SafeAbstraction

/--
Drop Preservation, non-owning drop-set fragment: if every value in `ψ` is
non-owning, then `drop(S, ψ)` leaves the safe abstraction unchanged.
-/
theorem safeAbstraction_drops_all_nonOwner {store store' : ProgramStore}
    {env : Env} {values : List PartialValue} :
    store ∼ₛ env →
    (∀ value, value ∈ values → PartialValueNonOwner value) →
    Drops store values store' →
    store' ∼ₛ env := by
  intro hsafe hnonOwner hdrops
  have hstore : store' = store := drops_all_nonOwner_eq hnonOwner hdrops
  subst hstore
  exact hsafe

/--
If no store slot has lifetime `m`, then no environment slot has lifetime `m`
under a safe abstraction.
-/
theorem safeAbstraction_env_no_lifetime_of_store_no_lifetime {store : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ lifetime) →
    ∀ x envSlot,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ lifetime := by
  intro hsafe hnoStore x envSlot henv
  rcases hsafe.2 x envSlot henv with ⟨value, hslot, _hvalid⟩
  exact hnoStore (VariableProjection x) { value := value, lifetime := envSlot.lifetime } hslot

/-- Dropping an absent lifetime leaves the typing environment unchanged. -/
theorem Env.dropLifetime_eq_self_of_no_lifetime {env : Env} {lifetime : Lifetime} :
    (∀ x slot, env.slotAt x = some slot → slot.lifetime ≠ lifetime) →
    env.dropLifetime lifetime = env := by
  intro hnoLifetime
  cases env with
  | mk slotAt =>
      simp [Env.dropLifetime] at hnoLifetime ⊢
      funext x
      cases hslot : slotAt x with
      | none =>
          simp
      | some slot =>
          simp [hnoLifetime x slot hslot]

/--
Drop Preservation for an absent lifetime: if no store slot has lifetime `m`,
then `drop(S, m)` and `drop(Γ, m)` are both no-ops.
-/
theorem safeAbstraction_dropsLifetime_no_slots {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ lifetime) →
    DropsLifetime store lifetime store' →
    store' ∼ₛ env.dropLifetime lifetime := by
  intro hsafe hnoStore hdrops
  have hstore : store' = store := dropsLifetime_no_slots_eq hnoStore hdrops
  have henv : env.dropLifetime lifetime = env :=
    Env.dropLifetime_eq_self_of_no_lifetime
      (safeAbstraction_env_no_lifetime_of_store_no_lifetime hsafe hnoStore)
  rw [hstore, henv]
  exact hsafe

@[simp] theorem Env.dropLifetime_slotAt_eq_some {env : Env} {x : Name}
    {slot : EnvSlot} {lifetime : Lifetime} :
    (env.dropLifetime lifetime).slotAt x = some slot ↔
      env.slotAt x = some slot ∧ slot.lifetime ≠ lifetime := by
  unfold Env.dropLifetime
  cases hslot : env.slotAt x with
  | none =>
      simp [hslot]
  | some candidate =>
      by_cases hlifetime : candidate.lifetime = lifetime
      · constructor
        · intro hdropped
          simp [hslot, hlifetime] at hdropped
        · intro h
          rcases h with ⟨henv, hne⟩
          injection henv with hcandidate
          subst hcandidate
          exact False.elim (hne hlifetime)
      · constructor
        · intro hdropped
          have hcandidate : candidate = slot := by
            simpa [hslot, hlifetime] using hdropped
          exact ⟨by
            simp [hcandidate],
            by simpa [hcandidate] using hlifetime⟩
        · intro h
          rcases h with ⟨henv, hne⟩
          injection henv with hcandidate
          subst hcandidate
          simp [hslot, hlifetime]

/--
Lemma 9.5 shape, safe-abstraction preservation across environment lifetime
drop.

The two premises are the concrete store-side facts that the recursive runtime
drop must provide: variable-domain agreement after the drop, and preservation
of valid abstractions for variables whose allocation lifetime is not dropped.
-/
theorem safeAbstraction_dropLifetime_of_preserved
    {store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    (∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot) →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ lifetime →
      ∃ value,
        store'.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } ∧
        ValidPartialValue store' value envSlot.ty) →
    store' ∼ₛ env.dropLifetime lifetime := by
  intro hdomain hpreserve
  constructor
  · exact hdomain
  · intro x envSlot henvDropped
    rcases (Env.dropLifetime_slotAt_eq_some.mp henvDropped) with
      ⟨henv, hlifetime⟩
    exact hpreserve x envSlot henv hlifetime

/--
Lemma 9.5, Drop Preservation, lifetime-drop form.

The abstract `ProgramStore` keeps `drop(S, m)` relational.  The two explicit
premises are exactly the store-side effects needed to connect the runtime drop
with Definition 3.20's environment drop.
-/
theorem dropPreservation_lifetime {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    DropsLifetime store lifetime store' →
    (∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot) →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ lifetime →
      ∃ value,
        store'.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } ∧
        ValidPartialValue store' value envSlot.ty) →
    store' ∼ₛ env.dropLifetime lifetime := by
  intro _hsafe _hdrops hdomain hpreserve
  exact safeAbstraction_dropLifetime_of_preserved hdomain hpreserve

/--
Lemma 9.5, Drop Preservation, lifetime-drop form from a store-slot
characterisation.

`hslotAt` is the concrete store-side analogue of Definition 3.20: a variable
slot remains after `drop(S, m)` exactly when it existed before and its allocation
lifetime was not `m`.
-/
theorem dropPreservation_lifetime_of_slotAt {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    DropsLifetime store lifetime store' →
    (∀ x slot,
      store'.slotAt (VariableProjection x) = some slot ↔
        store.slotAt (VariableProjection x) = some slot ∧ slot.lifetime ≠ lifetime) →
    (∀ x envSlot value,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ lifetime →
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } →
      ValidPartialValue store' value envSlot.ty) →
    store' ∼ₛ env.dropLifetime lifetime := by
  intro hsafe hdrops hslotAt hpreserve
  refine dropPreservation_lifetime hsafe hdrops ?domain ?preserve
  · intro x
    constructor
    · intro hstore'
      rcases hstore' with ⟨slot, hslot'⟩
      rcases (hslotAt x slot).mp hslot' with ⟨hslot, hlifetime⟩
      rcases (hsafe.1 x).mp ⟨slot, hslot⟩ with ⟨envSlot, henv⟩
      have henvLifetime : envSlot.lifetime = slot.lifetime := by
        rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
        rw [hslot] at hsafeSlot
        injection hsafeSlot with hslotEq
        exact (congrArg StoreSlot.lifetime hslotEq).symm
      exact ⟨envSlot, by
        exact Env.dropLifetime_slotAt_eq_some.mpr
          ⟨henv, by simpa [henvLifetime] using hlifetime⟩⟩
    · intro henvDropped
      rcases henvDropped with ⟨envSlot, henvDropped⟩
      rcases Env.dropLifetime_slotAt_eq_some.mp henvDropped with
        ⟨henv, hlifetime⟩
      rcases (hsafe.1 x).mpr ⟨envSlot, henv⟩ with ⟨slot, hslot⟩
      have hslotEq :
          slot.lifetime = envSlot.lifetime := by
        rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
        rw [hslot] at hsafeSlot
        injection hsafeSlot with hslotEq
        exact congrArg StoreSlot.lifetime hslotEq
      exact ⟨slot, (hslotAt x slot).mpr
        ⟨hslot, by simpa [hslotEq] using hlifetime⟩⟩
  · intro x envSlot henv hlifetime
    rcases hsafe.2 x envSlot henv with ⟨value, hslot, _hvalid⟩
    exact ⟨value,
      (hslotAt x { value := value, lifetime := envSlot.lifetime }).mpr
        ⟨hslot, hlifetime⟩,
      hpreserve x envSlot value henv hlifetime hslot⟩

/--
Store-domain half of Lemma 9.5: if a variable slot survives a lifetime drop,
then the corresponding environment variable survives `Γ.dropLifetime`.

The explicit side condition is the store-side fact still needed from the runtime
drop relation: final variable slots are not allocated in the dropped lifetime.
-/
theorem dropLifetime_envDomain_of_storeSurvivor {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} {x : Name} :
    store ∼ₛ env →
    DropsLifetime store lifetime store' →
    (∀ slot,
      store'.slotAt (VariableProjection x) = some slot →
      slot.lifetime ≠ lifetime) →
    (∃ slot, store'.slotAt (VariableProjection x) = some slot) →
    ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot := by
  intro hsafe hdrops hnotDropped hstoreDomain
  rcases hstoreDomain with ⟨slot, hslot'⟩
  have hslot : store.slotAt (VariableProjection x) = some slot :=
    dropsLifetime_slotAt_of_slotAt hdrops hslot'
  rcases (hsafe.1 x).mp ⟨slot, hslot⟩ with ⟨envSlot, henv⟩
  have henvLifetime : envSlot.lifetime = slot.lifetime := by
    rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
    rw [hslot] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact (congrArg StoreSlot.lifetime hslotEq).symm
  exact ⟨envSlot, Env.dropLifetime_slotAt_eq_some.mpr
    ⟨henv, by
      intro hdrop
      exact hnotDropped slot hslot' (by simpa [henvLifetime] using hdrop)⟩⟩

/--
Store-domain converse for Lemma 9.5: if an environment variable survives
`Γ.dropLifetime`, then the store has the corresponding variable slot after the
runtime drop, assuming non-dropped variable slots are preserved by the drop.
-/
theorem dropLifetime_storeDomain_of_envSurvivor {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} {x : Name} :
    store ∼ₛ env →
    (∀ slot,
      store.slotAt (VariableProjection x) = some slot →
      slot.lifetime ≠ lifetime →
      store'.slotAt (VariableProjection x) = some slot) →
    (∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot) →
    ∃ slot, store'.slotAt (VariableProjection x) = some slot := by
  intro hsafe hpreserve henvDomain
  rcases henvDomain with ⟨envSlot, henvDropped⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp henvDropped with
    ⟨henv, hlifetime⟩
  rcases (hsafe.1 x).mpr ⟨envSlot, henv⟩ with ⟨slot, hslot⟩
  have hslotLifetime : slot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
    rw [hslot] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact congrArg StoreSlot.lifetime hslotEq
  exact ⟨slot, hpreserve slot hslot (by simpa [hslotLifetime] using hlifetime)⟩

/--
Domain component of Lemma 9.5.  This packages the two store-side facts needed
to align runtime lifetime drops with Definition 3.20's environment drop.
-/
theorem dropLifetime_domain_equiv_of_slot_preservation
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    DropsLifetime store lifetime store' →
    (∀ x slot,
      store'.slotAt (VariableProjection x) = some slot →
      slot.lifetime ≠ lifetime) →
    (∀ x slot,
      store.slotAt (VariableProjection x) = some slot →
      slot.lifetime ≠ lifetime →
      store'.slotAt (VariableProjection x) = some slot) →
    ∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot := by
  intro hsafe hdrops hnotDropped hpreserve x
  constructor
  · exact dropLifetime_envDomain_of_storeSurvivor hsafe hdrops (hnotDropped x)
  · exact dropLifetime_storeDomain_of_envSurvivor hsafe (hpreserve x)

@[simp] theorem validPartialValue_unit (store : ProgramStore) :
    store ⊢ PartialValue.value Value.unit ∼ PartialTy.ty Ty.unit :=
  ValidPartialValue.unit

@[simp] theorem validPartialValue_int (store : ProgramStore) (value : Int) :
    store ⊢ PartialValue.value (Value.int value) ∼ PartialTy.ty Ty.int :=
  ValidPartialValue.int

@[simp] theorem validStoreTyping_empty (store : ProgramStore) :
    ValidStoreTyping store (.val .unit) StoreTyping.empty := by
  intro value hmem
  simp [termValues] at hmem
  subst hmem
  exact ⟨.unit, ValueTyping.unit, ValidPartialValue.unit⟩

@[simp] theorem safeAbstraction_empty :
    ProgramStore.empty ∼ₛ Env.empty := by
  constructor
  · intro x
    constructor
    · intro h
      rcases h with ⟨slot, hslot⟩
      simp [VariableProjection, ProgramStore.empty] at hslot
    · intro h
      rcases h with ⟨slot, hslot⟩
      simp [Env.empty] at hslot
  · intro x envSlot henv
    simp [Env.empty] at henv

theorem safeAbstraction_store_fresh_var {store : ProgramStore} {env : Env}
    {x : Name} :
    store ∼ₛ env →
    env.fresh x →
    store.fresh (VariableProjection x) := by
  intro hsafe hfresh
  unfold ProgramStore.fresh
  cases hslot : store.slotAt (VariableProjection x) with
  | none =>
      rfl
  | some slot =>
      rcases (hsafe.1 x).mp ⟨slot, hslot⟩ with ⟨envSlot, henvSlot⟩
      unfold Env.fresh at hfresh
      rw [hfresh] at henvSlot
      cases henvSlot

theorem safeAbstraction_var_read_nonOwner_of_envShape {store : ProgramStore}
    {env : Env} {x : Name} {envSlot : EnvSlot} {oldSlot : StoreSlot} :
    store ∼ₛ env →
    env.slotAt x = some envSlot →
    store.read (.var x) = some oldSlot →
    (envSlot.ty = .ty .unit ∨ envSlot.ty = .ty .int ∨
      (∃ inner, envSlot.ty = .undef inner) ∨
      ∃ mutable targets, envSlot.ty = .ty (.borrow mutable targets)) →
    PartialValueNonOwner oldSlot.value := by
  intro hsafe henv hread hshape
  rcases hsafe.2 x envSlot henv with ⟨safeValue, hstoreSlot, hvalid⟩
  have hstoreRead :
      store.slotAt (VariableProjection x) =
        some { value := oldSlot.value, lifetime := oldSlot.lifetime } := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  rw [hstoreRead] at hstoreSlot
  injection hstoreSlot with hslotEq
  have hvalueEq : safeValue = oldSlot.value :=
    (congrArg StoreSlot.value hslotEq).symm
  subst hvalueEq
  exact validPartialValue_nonOwner_of_envShape hvalid hshape

/-- Definition 3.23, direct variable write: `write₀(Γ, x, T)` updates only `x`. -/
theorem envWrite_zero_var_eq {env env' : Env} {x : Name} {slot : EnvSlot}
    {ty : Ty} :
    env.slotAt x = some slot →
    EnvWrite 0 env (.var x) ty env' →
    env' = env.update x { slot with ty := .ty ty } := by
  intro hslot hwrite
  cases hwrite with
  | intro hbase hupdate =>
      simp [LVal.base, hslot] at hbase
      subst hbase
      cases hupdate with
      | strong =>
          rfl

/-- Definition 3.3, direct variable write: runtime `write(S, x, v⊥)` updates only `.var x`. -/
theorem write_var_eq {store store' : ProgramStore} {x : Name}
    {oldSlot : StoreSlot} {value : PartialValue} :
    store.slotAt (VariableProjection x) = some oldSlot →
    store.write (.var x) value = some store' →
    store' =
      store.update (VariableProjection x) { oldSlot with value := value } := by
  intro hslot hwrite
  have hslotVar : store.slotAt (.var x) = some oldSlot := by
    simpa [VariableProjection] using hslot
  simp [ProgramStore.write, ProgramStore.loc, hslotVar] at hwrite
  subst hwrite
  rfl

/--
Safe-abstraction preservation for a direct variable type/value update.

This is the base shape needed by the paper's Update Preservation lemma for
`write₀(Γ, x, T)`: the updated variable gets the new value/type, while every
other variable keeps its domain membership and value abstraction.
-/
theorem safeAbstraction_update_var_of_preserved {store' : ProgramStore}
    {env env' : Env} {x : Name} {envSlot : EnvSlot} {value : Value} {ty : Ty} :
    env.slotAt x = some envSlot →
    store'.slotAt (VariableProjection x) =
      some { value := .value value, lifetime := envSlot.lifetime } →
    ValidPartialValue store' (.value value) (.ty ty) →
    env' = env.update x { envSlot with ty := .ty ty } →
    (∀ y,
      y ≠ x →
      ((∃ slot, store'.slotAt (VariableProjection y) = some slot) ↔
        ∃ otherEnvSlot, env.slotAt y = some otherEnvSlot)) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    store' ∼ₛ env' := by
  intro henvX hstoreX hnewValid henv' hdomainOther hpreserveOther
  subst henv'
  constructor
  · intro y
    by_cases hyx : y = x
    · subst hyx
      constructor
      · intro _hstoreDomain
        exact ⟨{ envSlot with ty := .ty ty }, by simp [Env.update]⟩
      · intro _henvDomain
        exact ⟨{ value := .value value, lifetime := envSlot.lifetime }, hstoreX⟩
    · constructor
      · intro hstoreDomain
        rcases (hdomainOther y hyx).mp hstoreDomain with ⟨otherEnvSlot, henv⟩
        exact ⟨otherEnvSlot, by simpa [Env.update, hyx] using henv⟩
      · intro henvDomain
        rcases henvDomain with ⟨otherEnvSlot, henvUpdated⟩
        have henv : env.slotAt y = some otherEnvSlot := by
          simpa [Env.update, hyx] using henvUpdated
        exact (hdomainOther y hyx).mpr ⟨otherEnvSlot, henv⟩
  · intro y updatedSlot henvUpdated
    by_cases hyx : y = x
    · subst hyx
      have hupdatedSlot :
          updatedSlot = { envSlot with ty := .ty ty } := by
        simpa [Env.update] using henvUpdated.symm
      subst hupdatedSlot
      exact ⟨.value value, hstoreX, hnewValid⟩
    · have henv : env.slotAt y = some updatedSlot := by
        simpa [Env.update, hyx] using henvUpdated
      exact hpreserveOther y updatedSlot hyx henv

/--
Variable-base assignment store preservation, factored around the paper's
`write₀` update relation.  The remaining premises are the standard update
preservation obligations for variables other than the assignment target.
-/
theorem storePreservation_assign_var_of_preserved
    {storeAfterDrop store' : ProgramStore} {env env' : Env}
    {x : Name} {runtimeSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    storeAfterDrop.slotAt (VariableProjection x) = some runtimeSlot →
    runtimeSlot.lifetime = envSlot.lifetime →
    storeAfterDrop.write (.var x) (.value value) = some store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y,
      y ≠ x →
      ((∃ slot, store'.slotAt (VariableProjection y) = some slot) ↔
        ∃ otherEnvSlot, env.slotAt y = some otherEnvSlot)) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    store' ∼ₛ env' := by
  intro henvX hwriteEnv hruntimeX hlifetime hwriteStore hnewValid
    hdomainOther hpreserveOther
  have henv' :
      env' = env.update x { envSlot with ty := .ty ty } :=
    envWrite_zero_var_eq henvX hwriteEnv
  have hstore' :
      store' =
        storeAfterDrop.update (VariableProjection x)
          { runtimeSlot with value := .value value } :=
    write_var_eq hruntimeX hwriteStore
  have hstoreX :
      store'.slotAt (VariableProjection x) =
        some { value := .value value, lifetime := envSlot.lifetime } := by
    subst hstore'
    simp [ProgramStore.update, hlifetime]
  exact safeAbstraction_update_var_of_preserved henvX hstoreX hnewValid henv'
    hdomainOther hpreserveOther

/--
Variable-base assignment store preservation when the old lhs value is
non-owning.

The old-value drop is a no-op, so the domain part of safe abstraction follows
from the single runtime write.  The remaining premise is the genuine update
preservation obligation: values abstracting variables other than `x` must remain
valid after overwriting `x`.
-/
theorem storePreservation_assign_var_old_nonOwner_of_preserved
    {store storeAfterDrop store' : ProgramStore} {env env' : Env}
    {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    PartialValueNonOwner oldSlot.value →
    store.read (.var x) = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write (.var x) (.value value) = some store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    store' ∼ₛ env' := by
  intro hsafe henvX hwriteEnv hnonOwner hread hdrops hwrite hnewValid hpreserveOther
  have hdropEq : storeAfterDrop = store :=
    drops_partialValue_nonOwner_eq hnonOwner hdrops
  have hstoreX : store.slotAt (VariableProjection x) = some oldSlot := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  have hstoreXAfterDrop : storeAfterDrop.slotAt (VariableProjection x) = some oldSlot := by
    simpa [hdropEq] using hstoreX
  have hlifetime : oldSlot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henvX with ⟨safeValue, hsafeSlot, _hvalid⟩
    rw [hstoreX] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact congrArg StoreSlot.lifetime hslotEq
  have hstore' :
      store' = storeAfterDrop.update (VariableProjection x)
        { oldSlot with value := .value value } :=
    write_var_eq hstoreXAfterDrop hwrite
  refine storePreservation_assign_var_of_preserved henvX hwriteEnv hstoreXAfterDrop
    hlifetime hwrite hnewValid ?domain hpreserveOther
  intro y hyx
  constructor
  · intro hstoreDomain
    rcases hstoreDomain with ⟨slot, hslot⟩
    have hslotStore : store.slotAt (VariableProjection y) = some slot := by
      rw [hstore'] at hslot
      have hslotAfterDrop :
          storeAfterDrop.slotAt (VariableProjection y) = some slot := by
        simpa [ProgramStore.update, VariableProjection, hyx] using hslot
      simpa [hdropEq] using hslotAfterDrop
    exact (hsafe.1 y).mp ⟨slot, hslotStore⟩
  · intro henvDomain
    rcases (hsafe.1 y).mpr henvDomain with ⟨slot, hslot⟩
    exact ⟨slot, by
      rw [hstore']
      have hslotAfterDrop : storeAfterDrop.slotAt (VariableProjection y) = some slot := by
        simpa [hdropEq] using hslot
      simpa [ProgramStore.update, VariableProjection, hyx] using hslotAfterDrop⟩

/--
Variable-base assignment store preservation when the old lhs environment type is
non-owning-shaped (`unit`, `int`, `undef`, or borrow).

This packages the Section 4.1 argument at the abstraction level: from `S ∼ Γ`,
the environment slot shape, and the lhs read, the old runtime partial value is
known to be non-owning, so its drop leaves the store unchanged.
-/
theorem storePreservation_assign_var_envShape_of_preserved
    {store storeAfterDrop store' : ProgramStore} {env env' : Env}
    {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    (envSlot.ty = .ty .unit ∨ envSlot.ty = .ty .int ∨
      (∃ inner, envSlot.ty = .undef inner) ∨
      ∃ mutable targets, envSlot.ty = .ty (.borrow mutable targets)) →
    store.read (.var x) = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write (.var x) (.value value) = some store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    store' ∼ₛ env' := by
  intro hsafe henvX hwriteEnv hshape hread hdrops hwrite hnewValid hpreserveOther
  have hnonOwner : PartialValueNonOwner oldSlot.value :=
    safeAbstraction_var_read_nonOwner_of_envShape hsafe henvX hread hshape
  exact storePreservation_assign_var_old_nonOwner_of_preserved
    hsafe henvX hwriteEnv hnonOwner hread hdrops hwrite hnewValid hpreserveOther

/-- Updating a fresh location does not change an already-defined lval location. -/
theorem loc_update_of_loc {store : ProgramStore} {updatedLocation : Location}
    {newSlot : StoreSlot} {lv : LVal} {location : Location} :
    store.fresh updatedLocation →
    store.loc lv = some location →
    (store.update updatedLocation newSlot).loc lv = some location := by
  intro hfresh hloc
  induction lv generalizing location with
  | var y =>
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      cases hsource : store.loc lv with
      | none =>
          simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          cases hsourceSlot : store.slotAt source with
          | none =>
              simp [ProgramStore.loc, hsource, hsourceSlot] at hloc
          | some sourceSlot =>
              cases hsourceValue : sourceSlot.value with
              | undef =>
                  simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
              | value sourceValue =>
                  cases sourceValue with
                  | unit =>
                      simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                  | int n =>
                      simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                  | ref ref =>
                    simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                    have hupdatedSource :
                        (store.update updatedLocation newSlot).loc lv = some source :=
                      ih hsource
                    have hsourceNe : source ≠ updatedLocation := by
                      intro hsame
                      subst hsame
                      simp [ProgramStore.fresh] at hfresh
                      rw [hfresh] at hsourceSlot
                      contradiction
                    have hslot :
                        (store.update updatedLocation newSlot).slotAt source =
                          some sourceSlot := by
                      simpa [ProgramStore.update, hsourceNe] using hsourceSlot
                    simp [ProgramStore.loc, hupdatedSource, hslot, hsourceValue, hloc]

/-- Updating a fresh location preserves an existing slot lookup. -/
theorem slotAt_update_of_slotAt {store : ProgramStore} {updatedLocation location : Location}
    {newSlot slot : StoreSlot} :
    store.fresh updatedLocation →
    store.slotAt location = some slot →
    (store.update updatedLocation newSlot).slotAt location = some slot := by
  intro hfresh hslot
  have hlocationNe : location ≠ updatedLocation := by
    intro hsame
    subst hsame
    simp [ProgramStore.fresh] at hfresh
    rw [hfresh] at hslot
    contradiction
  simpa [ProgramStore.update, hlocationNe] using hslot

/-- Updating a fresh location preserves existing partial-value abstractions. -/
theorem validPartialValue_update_of_fresh {store : ProgramStore}
    {updatedLocation : Location} {newSlot : StoreSlot}
    {partialValue : PartialValue} {ty : PartialTy} :
    store.fresh updatedLocation →
    ValidPartialValue store partialValue ty →
    ValidPartialValue (store.update updatedLocation newSlot) partialValue ty := by
  intro hfresh hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValue.unit
  | int =>
      exact ValidPartialValue.int
  | undef =>
      exact ValidPartialValue.undef
  | borrow hmem hloc =>
      exact ValidPartialValue.borrow hmem (loc_update_of_loc hfresh hloc)
  | box hslot _hinner ih =>
      exact ValidPartialValue.box (slotAt_update_of_slotAt hfresh hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValue.boxFull (slotAt_update_of_slotAt hfresh hslot) ih

/-- Declaring a fresh variable does not change an already-defined lval location. -/
theorem loc_declare_of_loc {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {value : Value} {lv : LVal} {location : Location} :
    store.fresh (.var x) →
    store.loc lv = some location →
    (store.declare x lifetime value).loc lv = some location := by
  intro hfresh hloc
  induction lv generalizing location with
  | var y =>
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      cases hsource : store.loc lv with
      | none =>
          simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          cases hsourceSlot : store.slotAt source with
          | none =>
              simp [ProgramStore.loc, hsource, hsourceSlot] at hloc
          | some sourceSlot =>
              cases hsourceValue : sourceSlot.value with
              | undef =>
                  simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
              | value sourceValue =>
                  cases sourceValue with
                  | unit =>
                      simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                  | int n =>
                      simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                  | ref ref =>
                    simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                    have hdeclaredSource :
                        (store.declare x lifetime value).loc lv = some source :=
                      ih hsource
                    have hsourceNe : source ≠ .var x := by
                      intro hsame
                      subst hsame
                      simp [ProgramStore.fresh] at hfresh
                      rw [hfresh] at hsourceSlot
                      contradiction
                    have hslot :
                        (store.declare x lifetime value).slotAt source = some sourceSlot := by
                      simpa [ProgramStore.declare, ProgramStore.update, hsourceNe]
                        using hsourceSlot
                    simp [ProgramStore.loc, hdeclaredSource, hslot, hsourceValue, hloc]

/-- Declaring a fresh variable preserves an existing slot lookup away from it. -/
theorem slotAt_declare_of_slotAt {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {value : Value} {location : Location} {slot : StoreSlot} :
    store.fresh (.var x) →
    store.slotAt location = some slot →
    (store.declare x lifetime value).slotAt location = some slot := by
  intro hfresh hslot
  have hlocationNe : location ≠ .var x := by
    intro hsame
    subst hsame
    simp [ProgramStore.fresh] at hfresh
    rw [hfresh] at hslot
    contradiction
  simpa [ProgramStore.declare, ProgramStore.update, hlocationNe] using hslot

/-- Declaring a fresh variable preserves existing partial-value abstractions. -/
theorem validPartialValue_declare {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {newValue : Value} {partialValue : PartialValue}
    {ty : PartialTy} :
    store.fresh (.var x) →
    ValidPartialValue store partialValue ty →
    ValidPartialValue (store.declare x lifetime newValue) partialValue ty := by
  intro hfresh hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValue.unit
  | int =>
      exact ValidPartialValue.int
  | undef =>
      exact ValidPartialValue.undef
  | borrow hmem hloc =>
      exact ValidPartialValue.borrow hmem (loc_declare_of_loc hfresh hloc)
  | box hslot _hinner ih =>
      exact ValidPartialValue.box (slotAt_declare_of_slotAt hfresh hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValue.boxFull (slotAt_declare_of_slotAt hfresh hslot) ih

/--
Lemma 9.10 support, `R-Declare` safe-abstraction preservation.

The explicit `hpreserveOld` premise is the store-extension obligation for values
already represented by `Γ`; it is discharged by later store-monotonicity lemmas.
-/
theorem safeAbstraction_declare {store : ProgramStore} {env : Env}
    {x : Name} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    store ∼ₛ env →
    env.fresh x →
    ValidPartialValue (store.declare x lifetime value) (.value value) (.ty ty) →
    (∀ y envSlot oldValue,
      y ≠ x →
      env.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ValidPartialValue (store.declare x lifetime value) oldValue envSlot.ty) →
    store.declare x lifetime value ∼ₛ
      env.update x { ty := .ty ty, lifetime := lifetime } := by
  intro hsafe hfresh hnewValid hpreserveOld
  constructor
  · intro y
    constructor
    · intro hstoreDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ ty := .ty ty, lifetime := lifetime }, by simp [Env.update]⟩
      · rcases hstoreDomain with ⟨slot, hslot⟩
        have holdStore : ∃ slot, store.slotAt (VariableProjection y) = some slot := by
          rcases slot with ⟨slotValue, slotLifetime⟩
          exact ⟨{ value := slotValue, lifetime := slotLifetime }, by
            simpa [ProgramStore.declare, ProgramStore.update, VariableProjection, hyx]
              using hslot⟩
        rcases (hsafe.1 y).mp holdStore with ⟨envSlot, henvSlot⟩
        exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
    · intro henvDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ value := .value value, lifetime := lifetime }, by
          simp [ProgramStore.declare, ProgramStore.update, VariableProjection]⟩
      · rcases henvDomain with ⟨envSlot, henvSlot⟩
        have holdEnv : ∃ envSlot, env.slotAt y = some envSlot := by
          exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
        rcases (hsafe.1 y).mpr holdEnv with ⟨storeSlot, hstoreSlot⟩
        exact ⟨storeSlot, by
          simpa [ProgramStore.declare, ProgramStore.update, VariableProjection, hyx]
            using hstoreSlot⟩
  · intro y envSlot henv
    by_cases hyx : y = x
    · subst hyx
      have henvSlot :
          envSlot = { ty := .ty ty, lifetime := lifetime } := by
        simpa [Env.update] using henv.symm
      subst henvSlot
      exact ⟨.value value, by
          simp [ProgramStore.declare, ProgramStore.update, VariableProjection],
        hnewValid⟩
    · have holdEnv : env.slotAt y = some envSlot := by
        simpa [Env.update, hyx] using henv
      rcases hsafe.2 y envSlot holdEnv with ⟨oldValue, hstoreSlot, _holdValid⟩
      exact ⟨oldValue, by
          simpa [ProgramStore.declare, ProgramStore.update, VariableProjection, hyx]
            using hstoreSlot,
        hpreserveOld y envSlot oldValue hyx holdEnv hstoreSlot⟩

/--
Lemma 9.10 support, variable `R-Move` safe-abstraction preservation.

This is the `π = ε` base case of the paper's `move(Γ, w)` / write-`undef`
correspondence.  The `hpreserveOld` premise packages the separate no-borrow /
path-stability obligation for variables other than `x`.
-/
theorem safeAbstraction_move_var {store : ProgramStore} {env : Env}
    {x : Name} {slot : EnvSlot} {ty : Ty} {oldValue : PartialValue} :
    store ∼ₛ env →
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    store.slotAt (VariableProjection x) =
      some { value := oldValue, lifetime := slot.lifetime } →
    (∀ y envSlot value,
      y ≠ x →
      env.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := value, lifetime := envSlot.lifetime } →
      ValidPartialValue
        (store.update (VariableProjection x)
          { value := .undef, lifetime := slot.lifetime })
        value envSlot.ty) →
    store.update (VariableProjection x) { value := .undef, lifetime := slot.lifetime } ∼ₛ
      env.update x { slot with ty := .undef ty } := by
  intro hsafe henv hty hstoreSlot hpreserveOld
  constructor
  · intro y
    constructor
    · intro hstoreDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ slot with ty := .undef ty }, by simp [Env.update]⟩
      · rcases hstoreDomain with ⟨runtimeSlot, hruntimeSlot⟩
        have holdStore : ∃ oldSlot, store.slotAt (VariableProjection y) = some oldSlot := by
          rcases runtimeSlot with ⟨slotValue, slotLifetime⟩
          exact ⟨{ value := slotValue, lifetime := slotLifetime }, by
            simpa [ProgramStore.update, VariableProjection, hyx] using hruntimeSlot⟩
        rcases (hsafe.1 y).mp holdStore with ⟨envSlot, henvSlot⟩
        exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
    · intro henvDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ value := .undef, lifetime := slot.lifetime }, by
          simp [ProgramStore.update, VariableProjection]⟩
      · rcases henvDomain with ⟨envSlot, henvSlot⟩
        have holdEnv : ∃ envSlot, env.slotAt y = some envSlot := by
          exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
        rcases (hsafe.1 y).mpr holdEnv with ⟨runtimeSlot, hruntimeSlot⟩
        exact ⟨runtimeSlot, by
          simpa [ProgramStore.update, VariableProjection, hyx] using hruntimeSlot⟩
  · intro y envSlot henvUpdated
    by_cases hyx : y = x
    · subst hyx
      have henvSlot :
          envSlot = { slot with ty := .undef ty } := by
        simpa [Env.update] using henvUpdated.symm
      subst henvSlot
      exact ⟨.undef, by
          simp [ProgramStore.update, VariableProjection],
        by
          simpa [hty] using (ValidPartialValue.undef (ty := ty))⟩
    · have holdEnv : env.slotAt y = some envSlot := by
        simpa [Env.update, hyx] using henvUpdated
      rcases hsafe.2 y envSlot holdEnv with ⟨value, hstore, _hvalid⟩
      exact ⟨value, by
          simpa [ProgramStore.update, VariableProjection, hyx] using hstore,
        hpreserveOld y envSlot value hyx holdEnv hstore⟩

/-- Lemma 9.10, variable `R-Move` store-preservation fragment. -/
theorem storePreservation_move_var_step {store store' : ProgramStore}
    {env₁ env₂ : Env} {lifetime valueLifetime : Lifetime}
    {x : Name} {value : Value} {ty : Ty} :
    store ∼ₛ env₁ →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    Step store lifetime (.move (.var x)) store' (.val value) →
    (∀ y envSlot oldValue,
      y ≠ x →
      env₁.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ValidPartialValue store' oldValue envSlot.ty) →
    store' ∼ₛ env₂ := by
  intro hsafe henvSlot hmove hstep hpreserveOld
  cases hstep with
  | move _hread hwrite =>
      rcases hsafe.2 x _ henvSlot with
        ⟨oldValue, hstoreSlot, _hvalidOld⟩
      have hstore' :
          store' =
            store.update (VariableProjection x)
              { value := .undef, lifetime := valueLifetime } := by
        have hstoreSlotVar :
            store.slotAt (.var x) =
              some { value := oldValue, lifetime := valueLifetime } := by
          simpa [VariableProjection] using hstoreSlot
        simp [ProgramStore.write, ProgramStore.loc, hstoreSlotVar] at hwrite
        exact hwrite.symm
      rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv₂⟩
      have hmoveSlotEq :
          moveSlot = { ty := .ty ty, lifetime := valueLifetime } := by
        simp [LVal.base] at hmoveSlot
        rw [henvSlot] at hmoveSlot
        injection hmoveSlot with hmoveSlotEq
        exact hmoveSlotEq.symm
      subst hmoveSlotEq
      cases struck with
      | ty struckTy =>
          simp [Strike, LVal.path] at hstrike
      | box struckInner =>
          simp [Strike, LVal.path] at hstrike
      | undef struckTy =>
          simp [Strike, LVal.path] at hstrike
          subst hstrike
          subst henv₂
          subst hstore'
          exact safeAbstraction_move_var hsafe henvSlot rfl hstoreSlot
            (by
              intro y envSlot oldOtherValue hyx henv hslot
              exact hpreserveOld y envSlot oldOtherValue hyx henv hslot)

/-- Lemma 9.10, `R-Declare` store-preservation fragment. -/
theorem storePreservation_declare_step {store store' : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {value : Value} :
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.letMut x (.val value)) .unit env₃ →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    (∀ ty,
      ValueTyping typing value ty →
      ValidPartialValue (store.declare x lifetime value) (.value value) (.ty ty)) →
    (∀ y envSlot oldValue,
      y ≠ x →
      env₁.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ValidPartialValue (store.declare x lifetime value) oldValue envSlot.ty) →
    store' ∼ₛ env₃ := by
  intro hsafe htyping hstep hnewValid hpreserveOld
  cases htyping with
  | declare hfresh hinit henv₃ =>
      cases hstep with
      | declare hstore' =>
          cases hinit with
          | const hvalueTyping =>
              subst hstore'
              subst henv₃
              exact safeAbstraction_declare hsafe hfresh
                (hnewValid _ hvalueTyping)
                hpreserveOld

/--
Lemma 9.10, `R-Declare` store preservation, with the store-extension
obligations discharged from the existing validity hypotheses.
-/
theorem storePreservation_declare_step_valid {store store' : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {value : Value} :
    ValidStoreTyping store (.letMut x (.val value)) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.letMut x (.val value)) .unit env₃ →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    store' ∼ₛ env₃ := by
  intro hvalidStoreTyping hsafe htyping hstep
  cases htyping with
  | declare hfresh hinit henv₃ =>
      have hfreshStore : store.fresh (VariableProjection x) :=
        safeAbstraction_store_fresh_var hsafe hfresh
      refine storePreservation_declare_step hsafe
        (TermTyping.declare hfresh hinit henv₃) hstep ?newValid ?preserveOld
      · intro ty hvalueTyping
        rcases hvalidStoreTyping value (by simp [termValues]) with
          ⟨storedTy, hstoredTyping, hvalidValue⟩
        have hty : storedTy = ty := by
          cases hstoredTyping <;> cases hvalueTyping
          · rfl
          · rfl
          · rename_i hstoredLookup hvalueLookup
            rw [hstoredLookup] at hvalueLookup
            injection hvalueLookup
        subst hty
        exact validPartialValue_declare hfreshStore hvalidValue
      · intro y envSlot oldValue _hyx henv hstoreSlot
        rcases hsafe.2 y envSlot henv with
          ⟨safeValue, hsafeSlot, hsafeValid⟩
        rw [hstoreSlot] at hsafeSlot
        injection hsafeSlot with hslotEq
        cases hslotEq
        exact validPartialValue_declare hfreshStore hsafeValid

/-- Box allocation preserves existing partial-value abstractions. -/
theorem validPartialValue_boxAt {store : ProgramStore} {address : Nat}
    {newValue : Value} {partialValue : PartialValue} {ty : PartialTy} :
    store.fresh (.heap address) →
    ValidPartialValue store partialValue ty →
    ValidPartialValue (store.boxAt address newValue).1 partialValue ty := by
  intro hfresh hvalid
  exact validPartialValue_update_of_fresh
    (updatedLocation := .heap address)
    (newSlot := { value := .value newValue, lifetime := Lifetime.root })
    hfresh hvalid

/-- The owning reference returned by `boxAt` safely abstracts `Box<T>`. -/
theorem validValue_boxAt_ref {store : ProgramStore} {address : Nat}
    {value : Value} {ty : Ty} :
    store.fresh (.heap address) →
    ValidValue store value ty →
    ValidValue (store.boxAt address value).1 (Value.ref (store.boxAt address value).2)
      (.box ty) := by
  intro hfresh hvalidValue
  exact ValidPartialValue.boxFull
    (location := .heap address)
    (slot := { value := .value value, lifetime := Lifetime.root })
    (by simp [ProgramStore.boxAt])
    (validPartialValue_update_of_fresh
      (updatedLocation := .heap address)
      (newSlot := { value := .value value, lifetime := Lifetime.root })
      hfresh (show ValidPartialValue store (.value value) (.ty ty) from hvalidValue))

/-- Lemma 9.10 support: heap allocation preserves safe abstraction of variables. -/
theorem safeAbstraction_boxAt {store : ProgramStore} {env : Env}
    {address : Nat} {value : Value} :
    store.fresh (.heap address) →
    store ∼ₛ env →
    (store.boxAt address value).1 ∼ₛ env := by
  intro hfresh hsafe
  constructor
  · intro x
    constructor
    · intro hdomain
      rcases hdomain with ⟨slot, hslot⟩
      have holdDomain : ∃ oldSlot, store.slotAt (VariableProjection x) = some oldSlot := by
        rcases slot with ⟨slotValue, slotLifetime⟩
        exact ⟨{ value := slotValue, lifetime := slotLifetime }, by
          simpa [ProgramStore.boxAt, ProgramStore.update, VariableProjection]
            using hslot⟩
      exact (hsafe.1 x).mp holdDomain
    · intro hdomain
      rcases (hsafe.1 x).mpr hdomain with ⟨slot, hslot⟩
      exact ⟨slot, by
        simpa [ProgramStore.boxAt, ProgramStore.update, VariableProjection]
          using hslot⟩
  · intro x envSlot henv
    rcases hsafe.2 x envSlot henv with ⟨oldValue, hslot, hvalid⟩
    exact ⟨oldValue, by
        simpa [ProgramStore.boxAt, ProgramStore.update, VariableProjection]
          using hslot,
      validPartialValue_boxAt hfresh hvalid⟩

/--
Lemma 9.10, `R-Box` store-preservation fragment, factored around the
operand-value abstraction established by the inner preservation proof.
-/
theorem storePreservation_box_step_of_validValue {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {ref : Reference} :
    store ∼ₛ env₁ →
    ValidValue store value ty →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    store' ∼ₛ env₂ ∧ ValidValue store' (.ref ref) (.box ty) := by
  intro hsafe hvalidValue htyping hstep
  cases htyping with
  | box hinner =>
      cases hinner with
      | const _hvalueTyping =>
          cases hstep with
          | box hfresh hbox =>
              cases hbox
              exact ⟨safeAbstraction_boxAt hfresh hsafe,
                validValue_boxAt_ref hfresh hvalidValue⟩

/-- Lemma 9.10, `R-Box` store-preservation fragment. -/
theorem storePreservation_box_step {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {ref : Reference} :
    ValidStoreTyping store (.box (.val value)) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    store' ∼ₛ env₂ ∧ ValidValue store' (.ref ref) (.box ty) := by
  intro hvalidStoreTyping hsafe htyping hstep
  cases htyping with
  | box hinner =>
      cases hinner with
      | const hvalueTyping =>
          rcases hvalidStoreTyping value (by simp [termValues]) with
            ⟨storedTy, hstoredTyping, hvalidValue⟩
          have hty : storedTy = ty := by
            cases hstoredTyping <;> cases hvalueTyping
            · rfl
            · rfl
            · rename_i hstoredLookup hvalueLookup
              rw [hstoredLookup] at hvalueLookup
              injection hvalueLookup
          subst hty
          exact storePreservation_box_step_of_validValue hsafe hvalidValue
            (TermTyping.box (typing := typing) (TermTyping.const hvalueTyping))
            hstep

/-- Lemma 9.9, `R-Box` one-step value preservation fragment. -/
theorem valuePreservation_box_step {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {ref : Reference} :
    ValidStoreTyping store (.box (.val value)) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidValue store' (.ref ref) (.box ty) := by
  intro hvalidStoreTyping hsafe htyping hstep
  exact (storePreservation_box_step hvalidStoreTyping hsafe htyping hstep).2

/-! ## Section 4.3: Borrow Invariance -/

/--
Definition 4.8(i).  Every borrow contained in an environment slot points at a
well-typed lval whose allocation lifetime outlives the borrow's lifetime.
-/
def BorrowTargetsWellFormedInSlot
    (env : Env) (slotLifetime : Lifetime) (targets : List LVal) : Prop :=
  ∀ target,
    target ∈ targets →
    ∃ targetTy targetLifetime,
      LValTyping env target (.ty targetTy) targetLifetime ∧
      targetLifetime ≤ slotLifetime

def ContainedBorrowsWellFormed (env : Env) : Prop :=
  ∀ x slot mutable targets,
    env.slotAt x = some slot →
    env ⊢ x ↝ (Ty.borrow mutable targets) →
    BorrowTargetsWellFormedInSlot env slot.lifetime targets

/--
Definition 4.8(ii).  Every environment slot lives at least as long as the
current lifetime.
-/
def EnvSlotsOutlive (env : Env) (lifetime : Lifetime) : Prop :=
  ∀ x slot,
    env.slotAt x = some slot →
    slot.lifetime ≤ lifetime

/-- Definition 4.8, well-formed environment. -/
def WellFormedEnv (env : Env) (lifetime : Lifetime) : Prop :=
  ContainedBorrowsWellFormed env ∧ EnvSlotsOutlive env lifetime

@[simp] theorem containedBorrowsWellFormed_empty :
    ContainedBorrowsWellFormed Env.empty := by
  intro x slot mutable targets hslot _hcontains
  simp [Env.empty] at hslot

@[simp] theorem envSlotsOutlive_empty (lifetime : Lifetime) :
    EnvSlotsOutlive Env.empty lifetime := by
  intro x slot hslot
  simp [Env.empty] at hslot

@[simp] theorem wellFormedEnv_empty (lifetime : Lifetime) :
    WellFormedEnv Env.empty lifetime := by
  exact ⟨containedBorrowsWellFormed_empty, envSlotsOutlive_empty lifetime⟩

theorem wellFormedEnv_empty_all :
    ∀ lifetime, WellFormedEnv Env.empty lifetime := by
  intro lifetime
  exact wellFormedEnv_empty lifetime

theorem LValTyping.update_fresh {env : Env} {x : Name} {slot : EnvSlot} :
    env.fresh x →
    (∀ {lv ty lifetime},
      LValTyping env lv ty lifetime →
      LValTyping (env.update x slot) lv ty lifetime) ∧
    (∀ {targets ty lifetime},
    LValTargetsTyping env targets ty lifetime →
    LValTargetsTyping (env.update x slot) targets ty lifetime) := by
  intro hfresh
  constructor
  · intro lv ty lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv ty lifetime _ =>
        LValTyping (env.update x slot) lv ty lifetime)
      (motive_2 := fun targets ty lifetime _ =>
        LValTargetsTyping (env.update x slot) targets ty lifetime)
      (by
        intro y envSlot hslot
        by_cases h : y = x
        · subst h
          unfold Env.fresh at hfresh
          rw [hfresh] at hslot
          cases hslot
        · exact LValTyping.var (by simpa [Env.update, h]))
      (by
        intro lv inner lifetime _htyping ih
        exact LValTyping.box ih)
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          _hborrow _htargets ihBorrow ihTargets
        exact LValTyping.borrow ihBorrow ihTargets)
      (by
        intro target ty lifetime _htarget ihTarget
        exact LValTargetsTyping.singleton ihTarget)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest
        exact LValTargetsTyping.cons ihHead ihRest hunion hintersection)
      htyping
  · intro targets ty lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv ty lifetime _ =>
        LValTyping (env.update x slot) lv ty lifetime)
      (motive_2 := fun targets ty lifetime _ =>
        LValTargetsTyping (env.update x slot) targets ty lifetime)
      (by
        intro y envSlot hslot
        by_cases h : y = x
        · subst h
          unfold Env.fresh at hfresh
          rw [hfresh] at hslot
          cases hslot
        · exact LValTyping.var (by simpa [Env.update, h]))
      (by
        intro lv inner lifetime _htyping ih
        exact LValTyping.box ih)
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          _hborrow _htargets ihBorrow ihTargets
        exact LValTyping.borrow ihBorrow ihTargets)
      (by
        intro target ty lifetime _htarget ihTarget
        exact LValTargetsTyping.singleton ihTarget)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest
        exact LValTargetsTyping.cons ihHead ihRest hunion hintersection)
      htyping

theorem LValTyping.update_fresh_one {env : Env} {x : Name} {slot : EnvSlot}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    env.fresh x →
    LValTyping env lv ty lifetime →
    LValTyping (env.update x slot) lv ty lifetime := by
  intro hfresh htyping
  exact (LValTyping.update_fresh (slot := slot) hfresh).1 htyping

theorem LValTargetsTyping.update_fresh {env : Env} {x : Name} {slot : EnvSlot}
    {targets : List LVal} {ty : PartialTy} {lifetime : Lifetime} :
    env.fresh x →
    LValTargetsTyping env targets ty lifetime →
    LValTargetsTyping (env.update x slot) targets ty lifetime := by
  intro hfresh htyping
  exact (LValTyping.update_fresh (slot := slot) hfresh).2 htyping

theorem borrowTargetsWellFormedInSlot_update_fresh {env : Env} {x : Name}
    {slot : EnvSlot} {slotLifetime : Lifetime} {targets : List LVal} :
    env.fresh x →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    BorrowTargetsWellFormedInSlot (env.update x slot) slotLifetime targets := by
  intro hfresh htargets target hmem
  rcases htargets target hmem with
    ⟨targetTy, targetLifetime, htyping, houtlives⟩
  exact ⟨targetTy, targetLifetime,
    LValTyping.update_fresh_one (slot := slot) hfresh htyping,
    houtlives⟩

theorem BorrowTargetsWellFormed.inSlot {env : Env} {targets : List LVal}
    {lifetime : Lifetime} :
    BorrowTargetsWellFormed env targets lifetime →
    BorrowTargetsWellFormedInSlot env lifetime targets := by
  intro htargets
  induction htargets with
  | singleton htarget houtlives =>
      intro target hmem
      simp at hmem
      subst hmem
      exact ⟨_, _, htarget, houtlives⟩
  | cons htarget houtlives _hrest ih =>
      intro selected hmem
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ⟨_, _, htarget, houtlives⟩
      · exact ih selected hselected

theorem borrowTargetsWellFormedInSlot_of_wellFormedTy_contains {env : Env}
    {ty : Ty} {lifetime : Lifetime} {mutable : Bool} {targets : List LVal} :
    WellFormedTy env ty lifetime →
    PartialTyContains (.ty ty) (.borrow mutable targets) →
    BorrowTargetsWellFormedInSlot env lifetime targets := by
  intro hwellTy hcontains
  cases hcontains with
  | here =>
      cases hwellTy with
      | borrow htargets =>
          exact BorrowTargetsWellFormed.inSlot htargets

theorem WellFormedEnv.update_fresh_ty {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    env.fresh x →
    WellFormedEnv (env.update x { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro hwellEnv hwellTy hfresh
  constructor
  · intro y envSlot mutable targets hslot hcontains
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          envSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = envSlot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hcontainedEq :
          containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
          simpa [Env.update] using hcontainedSlot
        exact h.symm
      subst hcontainedEq
      exact borrowTargetsWellFormedInSlot_update_fresh
        (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
        (borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwellTy hcontainsTy)
    · have hslotOld : env.slotAt y = some envSlot := by
        simpa [Env.update, hy] using hslot
      have hcontainsOld : env ⊢ y ↝ Ty.borrow mutable targets := by
        rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
        have hcontainedOld : env.slotAt y = some containedSlot := by
          simpa [Env.update, hy] using hcontainedSlot
        exact ⟨containedSlot, hcontainedOld, hcontainsTy⟩
      exact borrowTargetsWellFormedInSlot_update_fresh
        (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
        (hwellEnv.1 y envSlot mutable targets hslotOld hcontainsOld)
  · intro y envSlot hslot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          envSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = envSlot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      exact LifetimeOutlives.refl lifetime
    · have hslotOld : env.slotAt y = some envSlot := by
        simpa [Env.update, hy] using hslot
      exact hwellEnv.2 y envSlot hslotOld

/--
The final environment-extension step used by Lemma 4.9, Borrow Invariance:
once the type computed by the typing derivation is well formed in the output
environment, adding a fresh result slot preserves well-formedness.
-/
theorem borrowInvariance_result_extension {env₂ : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh gamma →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime := by
  exact WellFormedEnv.update_fresh_ty

theorem LifetimeIntersection.le_of_le {left right intersection current : Lifetime} :
    LifetimeIntersection left right intersection →
    left ≤ current →
    right ≤ current →
    intersection ≤ current := by
  intro hintersection hleft hright
  exact hintersection.2 (by
    intro lifetime hmem
    simp at hmem
    rcases hmem with h | h
    · simpa [h] using hleft
    · simpa [h] using hright)

theorem LifetimeOutlives.trans {first second third : Lifetime} :
    first ≤ second →
    second ≤ third →
    first ≤ third := by
  intro hfirst hsecond
  simp [LifetimeOutlives, Core.Lifetime.contains] at hfirst hsecond ⊢
  exact hfirst.trans hsecond

theorem LValTyping.lifetime_outlives {env : Env} {current : Lifetime} :
    WellFormedEnv env current →
    (∀ {lv ty lifetime},
      LValTyping env lv ty lifetime →
      lifetime ≤ current) ∧
    (∀ {targets ty lifetime},
      LValTargetsTyping env targets ty lifetime →
      lifetime ≤ current) := by
  intro hwellEnv
  constructor
  · intro lv ty lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun _lv _ty lifetime _ => lifetime ≤ current)
      (motive_2 := fun _targets _ty lifetime _ => lifetime ≤ current)
      (by
        intro x slot hslot
        exact hwellEnv.2 x slot hslot)
      (by
        intro _lv _inner _lifetime _htyping ih
        exact ih)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets
        exact ihTargets)
      (by
        intro _target _ty _lifetime _htarget ihTarget
        exact ihTarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest
        exact LifetimeIntersection.le_of_le hintersection ihHead ihRest)
      htyping
  · intro targets ty lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv _ty lifetime _ => lifetime ≤ current)
      (motive_2 := fun _targets _ty lifetime _ => lifetime ≤ current)
      (by
        intro x slot hslot
        exact hwellEnv.2 x slot hslot)
      (by
        intro _lv _inner _lifetime _htyping ih
        exact ih)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets
        exact ihTargets)
      (by
        intro _target _ty _lifetime _htarget ihTarget
        exact ihTarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest
        exact LifetimeIntersection.le_of_le hintersection ihHead ihRest)
      htyping

theorem LValTyping.lifetime_outlives_one {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    LValTyping env lv ty lifetime →
    lifetime ≤ current := by
  intro hwellEnv htyping
  exact (LValTyping.lifetime_outlives hwellEnv).1 htyping

theorem LValTyping.var_inv {env : Env} {x : Name}
    {ty : PartialTy} {lifetime : Lifetime} :
    LValTyping env (.var x) ty lifetime →
    ∃ slot,
      env.slotAt x = some slot ∧
      slot.ty = ty ∧
      slot.lifetime = lifetime := by
  intro htyping
  cases htyping with
  | var hslot =>
      exact ⟨_, hslot, rfl, rfl⟩

/-! ## Appendix 9.1: Preliminary Lemmas -/

/-- A binary type union strengthens its left input. -/
theorem PartialTyUnion.left_strengthens {left right union : PartialTy} :
    PartialTyUnion left right union →
    PartialTyStrengthens left union := by
  intro h
  exact h.1 (by simp)

/-- A binary type union strengthens its right input. -/
theorem PartialTyUnion.right_strengthens {left right union : PartialTy} :
    PartialTyUnion left right union →
    PartialTyStrengthens right union := by
  intro h
  exact h.1 (by simp)

/-- Lemma 9.2, Transitive Strengthening. -/
theorem partialTyStrengthens_trans {left middle right : PartialTy} :
    PartialTyStrengthens left middle →
    PartialTyStrengthens middle right →
    PartialTyStrengthens left right := by
  intro hleft hright
  induction hright generalizing left with
  | reflex =>
      exact hleft
  | box hbox ih =>
      cases hleft with
      | reflex =>
          exact PartialTyStrengthens.box hbox
      | box hinner =>
          exact PartialTyStrengthens.box (ih hinner)
  | borrow hsubset₂ =>
      cases hleft with
      | reflex =>
          exact PartialTyStrengthens.borrow hsubset₂
      | borrow hsubset₁ =>
          exact PartialTyStrengthens.borrow
            (fun target hmem => hsubset₂ (hsubset₁ hmem))
  | undefLeft hundef ih =>
      cases hleft with
      | reflex =>
          exact PartialTyStrengthens.undefLeft hundef
      | undefLeft hinner =>
          exact PartialTyStrengthens.undefLeft (ih hinner)
      | intoUndef hinner =>
          exact PartialTyStrengthens.intoUndef (ih hinner)
      | boxIntoUndef hinner =>
          cases hundef with
          | reflex =>
              exact PartialTyStrengthens.boxIntoUndef hinner
  | intoUndef hundef ih =>
      cases hleft with
      | reflex =>
          exact PartialTyStrengthens.intoUndef hundef
      | borrow hsubset =>
          exact PartialTyStrengthens.intoUndef
            (ih (PartialTyStrengthens.borrow hsubset))
  | boxIntoUndef hundef ih =>
      cases hleft with
      | reflex =>
          exact PartialTyStrengthens.boxIntoUndef hundef
      | box hinner =>
          exact PartialTyStrengthens.boxIntoUndef (ih hinner)

/--
Target-list typing records a finite union of the target types.  Any selected
target therefore has a full type that strengthens the union type.
-/
theorem lvalTargetsTyping_member_strengthens {env : Env}
    {targets : List LVal} {unionTy : PartialTy} {lifetime : Lifetime} :
    LValTargetsTyping env targets unionTy lifetime →
    ∀ target,
      target ∈ targets →
      ∃ ty targetLifetime,
        LValTyping env target (.ty ty) targetLifetime ∧
        PartialTyStrengthens (.ty ty) unionTy := by
  intro htargets
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun targets unionTy _ _ =>
      ∀ target,
        target ∈ targets →
        ∃ ty targetLifetime,
          LValTyping env target (.ty ty) targetLifetime ∧
          PartialTyStrengthens (.ty ty) unionTy)
    ?var ?box ?borrow ?singleton ?cons htargets
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _htyping _htargets _ihTyping _ihTargets
    trivial
  · intro target ty targetLifetime htyping _ihTyping selected hmem
    simp at hmem
    subst hmem
    exact ⟨ty, targetLifetime, htyping, PartialTyStrengthens.reflex⟩
  · intro target rest headTy headLifetime _restLifetime _lifetime _restTy unionTy
      hhead _hrest hunion _hintersection _ihHead ihRest selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ⟨headTy, headLifetime, hhead, PartialTyUnion.left_strengthens hunion⟩
    · rcases ihRest selected hselected with
        ⟨ty, selectedLifetime, htyping, hstrength⟩
      exact ⟨ty, selectedLifetime, htyping,
        partialTyStrengthens_trans hstrength
          (PartialTyUnion.right_strengthens hunion)⟩

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
  | cons _hterm hrest =>
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
  | cons _hterm hrest =>
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
  | block hterms _hwellFormed hdrop =>
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
  | block hterms _hwellFormed _hdrop =>
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
  exact ⟨⟨hvalidState, hvalidRuntime.2⟩, hsafe₂, hvalidValue⟩

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
    ShapeCompatible env oldTy (.ty rhsTy) →
    store.read lv = some oldSlot →
    PartialValueNonOwner oldSlot.value := by
  intro hwellFormed hsafe htyping hshape hread
  have hshapeOld := partialTy_nonOwnerShape_of_shapeCompatible_right_ty hshape
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
        ty_nonOwnerShape_of_strengthens_shapeCompatible_right_ty hstrength hshape
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

/-! ## Appendix 9.4: Value Preservation Fragments -/

/-- Lemma 9.9, `R-Copy` one-step value preservation fragment. -/
theorem valuePreservation_copy_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    ValidValue store value ty := by
  intro hwellFormed hsafe htyping hstep
  cases htyping with
  | copy hLv _hcopy _hreadProhibited =>
      cases hstep with
      | copy hread =>
          rcases readPreservation hwellFormed hsafe hLv with
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
  intro hwellFormed hsafe htyping hstep
  cases htyping with
  | move hLv _hwriteProhibited _hmove =>
      cases hstep with
      | move hread _hwrite =>
          rcases readPreservation hwellFormed hsafe hLv with
            ⟨readValue, runtimeSlot, hreadPreserved, hslotValue, hvalidValue⟩
          rw [hread] at hreadPreserved
          injection hreadPreserved with hslotEq
          cases hslotEq
          cases hslotValue
          exact hvalidValue

/-- Lemma 9.9, `R-Borrow` one-step value preservation fragment. -/
theorem valuePreservation_borrow_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {mutable : Bool} {location : Location} :
    TermTyping env typing lifetime (.borrow mutable lv) (.borrow mutable [lv]) env₂ →
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
  | int =>
      cases hvalid
      rfl
  | immBorrow =>
      cases hvalid with
      | borrow _hmem _hloc =>
          rfl

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
  intro hwellFormed hsafe hvalidState htyping hstep
  rcases hvalidState with ⟨hvalidStore, _hvalidTerm, _hdisjoint⟩
  cases htyping with
  | copy hLv hcopy _hreadProhibited =>
      cases hstep with
      | copy hread =>
          rcases readPreservation hwellFormed hsafe hLv with
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
  | assign hread hdrops hwrite =>
      exact ⟨validStore_write_disjoint (drops_validStore hdrops hvalidStore) (by
          intro owned hmem hownsAfterDrop
          exact hdisjoint owned
            (by simpa [termOwningLocations, termValues, partialValueOwningLocations]
              using hmem)
            (drops_owns_of_owns hdrops hownsAfterDrop))
          hwrite,
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

/-- Allocation invariant preservation for `R-Declare`. -/
theorem storeOwnersAllocated_declare_step {store store' : ProgramStore}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name} {value : Value} :
    StoreOwnersAllocated store →
    ValidStoreTyping store (.letMut x (.val value)) typing →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    StoreOwnersAllocated store' := by
  intro hallocated hvalidStoreTyping hstep
  cases hstep with
  | declare hstore' =>
      rcases hvalidStoreTyping value (by simp [termValues]) with
        ⟨_ty, _hvalueTyping, hvalidValue⟩
      exact storeOwnersAllocated_declare_step_of_validValue hallocated hvalidValue
        (Step.declare (lifetime := lifetime) hstore')

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

/-- Lemma 9.8, typed `R-Box` valid-state preservation fragment. -/
theorem validState_box_step_typed {store store' : ProgramStore}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ref : Reference} :
    ValidState store (.box (.val value)) →
    StoreOwnersAllocated store →
    ValidStoreTyping store (.box (.val value)) typing →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidState store' (.val (.ref ref)) := by
  intro hvalidState hallocated hvalidStoreTyping hstep
  cases hstep with
  | box hfresh hbox =>
      rcases hvalidStoreTyping value (by simp [termValues]) with
        ⟨_ty, _hvalueTyping, hvalidValue⟩
      exact validState_box_step_of_validValue (lifetime := lifetime)
        hvalidState hallocated hvalidValue
        (Step.box (lifetime := lifetime) hfresh hbox)

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

/-- Allocation invariant preservation for `R-Box`. -/
theorem storeOwnersAllocated_box_step {store store' : ProgramStore}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ref : Reference} :
    StoreOwnersAllocated store →
    ValidStoreTyping store (.box (.val value)) typing →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    StoreOwnersAllocated store' := by
  intro hallocated hvalidStoreTyping hstep
  cases hstep with
  | box hfresh hbox =>
      rcases hvalidStoreTyping value (by simp [termValues]) with
        ⟨_ty, _hvalueTyping, hvalidValue⟩
      exact storeOwnersAllocated_box_step_of_validValue (lifetime := lifetime)
        hallocated hvalidValue
        (Step.box (lifetime := lifetime) hfresh hbox)

/-! ### Composed Runtime Validity Preservation Fragments -/

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
  intro hwellFormed hsafe hvalidRuntime htyping hstep
  exact ⟨validState_copy_step hwellFormed hsafe hvalidRuntime.1 htyping hstep,
    storeOwnersAllocated_copy_step hvalidRuntime.2 hstep⟩

/-- Runtime-validity preservation for `R-Borrow`. -/
theorem validRuntimeState_borrow_step {store : ProgramStore}
    {lifetime : Lifetime} {mutable : Bool} {lv : LVal} {location : Location} :
    ValidRuntimeState store (.borrow mutable lv) →
    Step store lifetime (.borrow mutable lv) store
      (.val (.ref { location := location, owner := false })) →
    ValidRuntimeState store (.val (.ref { location := location, owner := false })) := by
  intro hvalidRuntime hstep
  exact ⟨validState_borrow_step hvalidRuntime.1 hstep,
    storeOwnersAllocated_borrow_step hvalidRuntime.2 hstep⟩

/-- Runtime-validity preservation for `R-Move`. -/
theorem validRuntimeState_move_step {store store' : ProgramStore}
    {lifetime : Lifetime} {lv : LVal} {value : Value} :
    ValidRuntimeState store (.move lv) →
    Step store lifetime (.move lv) store' (.val value) →
    ValidRuntimeState store' (.val value) := by
  intro hvalidRuntime hstep
  exact ⟨validState_move_step hvalidRuntime.1 hstep,
    storeOwnersAllocated_move_step hvalidRuntime.2 hstep⟩

/--
Runtime-validity preservation for `R-Assign`, assuming the assignment's
drop/write sequence preserves the explicit owner-allocation invariant.

The paper's store model leaves this allocation invariant implicit; the premise
is the remaining update-preservation obligation for our abstract store package.
-/
theorem validRuntimeState_assign_step {store store' : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {value : Value} :
    ValidRuntimeState store (.assign lhs (.val value)) →
    StoreOwnersAllocated store' →
    Step store lifetime (.assign lhs (.val value)) store' (.val .unit) →
    ValidRuntimeState store' (.val .unit) := by
  intro hvalidRuntime hallocated hstep
  exact ⟨validState_assign_step hvalidRuntime.1 hstep, hallocated⟩

/--
Runtime-validity preservation for `R-Assign` from a post-drop allocation
invariant and a value abstraction in that post-drop store.

Unlike `R-Seq`, assignment may temporarily invalidate owner allocation after the
old value is dropped, because the old owner still occupies the lhs until the
write happens.  This lemma states the correct final-store bridge.
-/
theorem validRuntimeState_assign_step_of_postDrop_validValue
    {store storeAfterDrop store' : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot}
    {value : Value} {ty : Ty} :
    ValidRuntimeState store (.assign lhs (.val value)) →
    StoreOwnersAllocated storeAfterDrop →
    ValidValue storeAfterDrop value ty →
    store.read lhs = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write lhs (.value value) = some store' →
    ValidRuntimeState store' (.val .unit) := by
  intro hvalidRuntime hallocatedAfterDrop hvalidValue hread hdrops hwrite
  exact validRuntimeState_assign_step (lifetime := lifetime) hvalidRuntime
    (storeOwnersAllocated_write_value_of_validValue hallocatedAfterDrop hvalidValue hwrite)
    (Step.assign (lifetime := lifetime) hread hdrops hwrite)

/--
Runtime-validity preservation for `R-Assign` when the old lhs value is
non-owning.  In this common case the drop step is a no-op, so the original
allocation invariant and RHS value abstraction are enough.
-/
theorem validRuntimeState_assign_step_old_nonOwner
    {store storeAfterDrop store' : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot}
    {value : Value} {ty : Ty} :
    PartialValueNonOwner oldSlot.value →
    ValidRuntimeState store (.assign lhs (.val value)) →
    ValidValue store value ty →
    store.read lhs = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write lhs (.value value) = some store' →
    ValidRuntimeState store' (.val .unit) := by
  intro hnonOwner hvalidRuntime hvalidValue hread hdrops hwrite
  have hdropEq : storeAfterDrop = store :=
    drops_partialValue_nonOwner_eq hnonOwner hdrops
  subst hdropEq
  exact validRuntimeState_assign_step_of_postDrop_validValue
    (lifetime := lifetime) hvalidRuntime hvalidRuntime.2 hvalidValue hread hdrops hwrite

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
      exact ⟨validState_declare hvalidRuntime.1 hfresh,
        storeOwnersAllocated_declare_step_of_validValue hvalidRuntime.2 hvalidValue
          (Step.declare rfl)⟩

/-- Runtime-validity preservation for `R-Declare`. -/
theorem validRuntimeState_declare_step {store store' : ProgramStore}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name} {value : Value} :
    ValidRuntimeState store (.letMut x (.val value)) →
    store.fresh (.var x) →
    ValidStoreTyping store (.letMut x (.val value)) typing →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    ValidRuntimeState store' (.val .unit) := by
  intro hvalidRuntime hfresh hvalidStoreTyping hstep
  cases hstep with
  | declare hstore' =>
      rcases hvalidStoreTyping value (by simp [termValues]) with
        ⟨_ty, _hvalueTyping, hvalidValue⟩
      exact validRuntimeState_declare_step_of_validValue hvalidRuntime hfresh hvalidValue
        (Step.declare (lifetime := lifetime) hstore')

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
          hvalidRuntime.1 hvalidRuntime.2 (Step.seq (lifetime := lifetime) hdrops)⟩

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
          hvalidRuntime.1 hvalidRuntime.2 hdropDisjoint
          (Step.blockB (lifetime := lifetime) hdrops)⟩

/-- Runtime-validity preservation for `R-Box`, from operand validity. -/
theorem validRuntimeState_box_step_of_validValue {store store' : ProgramStore}
    {lifetime : Lifetime} {value : Value} {ty : Ty} {ref : Reference} :
    ValidRuntimeState store (.box (.val value)) →
    ValidValue store value ty →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidRuntimeState store' (.val (.ref ref)) := by
  intro hvalidRuntime hvalidValue hstep
  exact ⟨validState_box_step_of_validValue hvalidRuntime.1 hvalidRuntime.2
      hvalidValue hstep,
    storeOwnersAllocated_box_step_of_validValue hvalidRuntime.2 hvalidValue hstep⟩

/-- Runtime-validity preservation for `R-Box`. -/
theorem validRuntimeState_box_step {store store' : ProgramStore}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ref : Reference} :
    ValidRuntimeState store (.box (.val value)) →
    ValidStoreTyping store (.box (.val value)) typing →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidRuntimeState store' (.val (.ref ref)) := by
  intro hvalidRuntime hvalidStoreTyping hstep
  cases hstep with
  | box hfresh hbox =>
      rcases hvalidStoreTyping value (by simp [termValues]) with
        ⟨_ty, _hvalueTyping, hvalidValue⟩
      exact validRuntimeState_box_step_of_validValue (lifetime := lifetime)
        hvalidRuntime hvalidValue
        (Step.box (lifetime := lifetime) hfresh hbox)

/-- Lemma 9.10, `R-Copy` store-preservation fragment. -/
theorem storePreservation_copy_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    Step store lifetime (.copy lv) store (.val value) →
    store ∼ₛ env₂ ∧ ValidValue store value ty := by
  intro hwellFormed hsafe htyping hstep
  cases htyping with
  | copy hLv hcopy hreadProhibited =>
      exact ⟨hsafe,
        valuePreservation_copy_step (typing := typing) hwellFormed hsafe
          (TermTyping.copy (typing := typing) hLv hcopy hreadProhibited) hstep⟩

/-- Lemma 9.10, `R-Borrow` store-preservation fragment. -/
theorem storePreservation_borrow_step {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {mutable : Bool} {location : Location} :
    store ∼ₛ env →
    TermTyping env typing lifetime (.borrow mutable lv) (.borrow mutable [lv]) env₂ →
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
  intro hwellFormed hsafe hvalidRuntime htyping hstep
  rcases storePreservation_copy_step hwellFormed hsafe htyping hstep with
    ⟨hsafe₂, hvalidValue⟩
  exact ⟨validRuntimeState_copy_step hwellFormed hsafe hvalidRuntime htyping hstep,
    hsafe₂, hvalidValue⟩

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
    TermTyping env typing lifetime (.borrow mutable lv) (.borrow mutable [lv]) env₂ →
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
      ValidPartialValue store' oldValue envSlot.ty) →
    ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env₂ ∧
      ValidValue store' value ty := by
  intro _hwellFormed hsafe hvalidRuntime henvSlot hmove _htyping hstep hvalidValue
    hpreserveOld
  exact ⟨validRuntimeState_move_step hvalidRuntime hstep,
    storePreservation_move_var_step hsafe henvSlot hmove hstep hpreserveOld,
    hvalidValue⟩

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
  | declare hfresh hinit henv₃ =>
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

/--
Lemma 4.11, `R-Assign` runtime/value preservation fragment.

This stops short of store preservation (`S₂ ∼ Γ₂`), which requires the paper's
Update Preservation lemma for the flow-sensitive `EnvWrite` relation.
-/
theorem preservation_assign_step_runtime_validity {store store' : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {value : Value} :
    ValidRuntimeState store (.assign lhs (.val value)) →
    StoreOwnersAllocated store' →
    Step store lifetime (.assign lhs (.val value)) store' (.val .unit) →
    ValidRuntimeState store' (.val .unit) ∧ ValidValue store' .unit .unit := by
  intro hvalidRuntime hallocated hstep
  exact ⟨validRuntimeState_assign_step hvalidRuntime hallocated hstep,
    ValidPartialValue.unit⟩

/--
Lemma 4.11, direct-variable `R-Assign` preservation fragment when the old lhs
value is non-owning.

This composes the runtime-validity bridge with the variable-base update
preservation fragment.  The only remaining premise is the genuine
path-stability/update-preservation obligation for variables other than `x`.
-/
theorem preservation_assign_var_old_nonOwner_step_runtime_of_preserved
    {store storeAfterDrop store' : ProgramStore} {env env' : Env}
    {lifetime : Lifetime} {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    PartialValueNonOwner oldSlot.value →
    ValidValue store value ty →
    store.read (.var x) = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write (.var x) (.value value) = some store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    ValidRuntimeState store' (.val .unit) ∧ store' ∼ₛ env' ∧
      ValidValue store' .unit .unit := by
  intro hsafe hvalidRuntime henvX hwriteEnv hnonOwner hvalidValue
    hread hdrops hwrite hnewValid hpreserveOther
  exact ⟨validRuntimeState_assign_step_old_nonOwner (lifetime := lifetime)
      hnonOwner hvalidRuntime hvalidValue hread hdrops hwrite,
    storePreservation_assign_var_old_nonOwner_of_preserved hsafe henvX hwriteEnv
      hnonOwner hread hdrops hwrite hnewValid hpreserveOther,
    ValidPartialValue.unit⟩

/--
Lemma 4.11, direct-variable `R-Assign` preservation fragment when the old lhs
environment type is non-owning (`unit`, `int`, `undef`, or borrow).

This derives the runtime non-owner drop side condition from `S ∼ Γ`, the
variable read, and the environment slot shape.
-/
theorem preservation_assign_var_envShape_step_runtime_of_preserved
    {store storeAfterDrop store' : ProgramStore} {env env' : Env}
    {lifetime : Lifetime} {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    (envSlot.ty = .ty .unit ∨ envSlot.ty = .ty .int ∨
      (∃ inner, envSlot.ty = .undef inner) ∨
      ∃ mutable targets, envSlot.ty = .ty (.borrow mutable targets)) →
    ValidValue store value ty →
    store.read (.var x) = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write (.var x) (.value value) = some store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    ValidRuntimeState store' (.val .unit) ∧ store' ∼ₛ env' ∧
      ValidValue store' .unit .unit := by
  intro hsafe hvalidRuntime henvX hwriteEnv hshape hvalidValue
    hread hdrops hwrite hnewValid hpreserveOther
  have hnonOwner : PartialValueNonOwner oldSlot.value :=
    safeAbstraction_var_read_nonOwner_of_envShape hsafe henvX hread hshape
  exact preservation_assign_var_old_nonOwner_step_runtime_of_preserved
    (lifetime := lifetime) hsafe hvalidRuntime henvX hwriteEnv hnonOwner
    hvalidValue hread hdrops hwrite hnewValid hpreserveOther

/--
Lemma 4.11, `R-Seq` preservation fragment for non-owning values.

This covers unit, integers, and shared references.  Owning references need the
paper's full Drop Preservation lemma, because the step may recursively erase
reachable storage.
-/
theorem preservation_seq_nonOwner_step_runtime {store store' : ProgramStore}
    {env : Env} {lifetime blockLifetime : Lifetime} {value : Value}
    {next : Term} {rest : List Term} :
    valueOwnedLocation? value = none →
    store ∼ₛ env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    Step store lifetime (.block blockLifetime (.val value :: next :: rest))
      store' (.block blockLifetime (next :: rest)) →
    ValidRuntimeState store' (.block blockLifetime (next :: rest)) ∧ store' ∼ₛ env := by
  intro hnonOwner hsafe hvalidRuntime hstep
  cases hstep with
  | seq hdrops =>
      have hstore : store' = store := drops_value_nonOwner_eq hnonOwner hdrops
      subst hstore
      exact ⟨validRuntimeState_seq_step hvalidRuntime
        (Step.seq (lifetime := lifetime) hdrops), hsafe⟩

/--
Lemma 4.11 support, `R-Seq` preservation fragment for non-owning values, also
carrying forward the valid store typing needed to continue progress on the
remaining block.
-/
theorem preservation_seq_nonOwner_step_runtime_with_storeTyping
    {store store' : ProgramStore} {env : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value : Value} {next : Term}
    {rest : List Term} :
    valueOwnedLocation? value = none →
    store ∼ₛ env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    ValidStoreTyping store (.block blockLifetime (.val value :: next :: rest)) typing →
    Step store lifetime (.block blockLifetime (.val value :: next :: rest))
      store' (.block blockLifetime (next :: rest)) →
    ValidRuntimeState store' (.block blockLifetime (next :: rest)) ∧
      store' ∼ₛ env ∧
      ValidStoreTyping store' (.block blockLifetime (next :: rest)) typing := by
  intro hnonOwner hsafe hvalidRuntime hstoreTyping hstep
  rcases preservation_seq_nonOwner_step_runtime hnonOwner hsafe hvalidRuntime hstep with
    ⟨hvalidRuntime', hsafe'⟩
  cases hstep with
  | seq hdrops =>
      have hstore : store' = store := drops_value_nonOwner_eq hnonOwner hdrops
      subst hstore
      exact ⟨hvalidRuntime', hsafe', validStoreTyping_block_tail hstoreTyping⟩

/--
Lemma 4.11, `R-BlockB` one-step preservation fragment, factored through the
store-side premises needed by Lemma 9.5 (`drop(S, m) ∼ drop(Γ, m)`).
-/
theorem preservation_blockB_value_step_runtime_of_drop_preserved
    {store store' : ProgramStore} {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    store ∼ₛ env →
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    LifetimeDropOwnersDisjoint store blockLifetime →
    Step store lifetime (.block blockLifetime [.val value]) store' (.val value) →
    ValidValue store' value ty →
    (∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime blockLifetime).slotAt x = some envSlot) →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ blockLifetime →
      ∃ oldValue,
        store'.slotAt (VariableProjection x) =
          some { value := oldValue, lifetime := envSlot.lifetime } ∧
        ValidPartialValue store' oldValue envSlot.ty) →
    ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env' ∧
      ValidValue store' value ty := by
  intro hvalidRuntime hsafe htyping hdropDisjoint hstep hvalidValue hdomain hpreserve
  have henv' : env' = env.dropLifetime blockLifetime := by
    exact blockValueTyping_output_eq htyping
  have hsafeDrop : store' ∼ₛ env.dropLifetime blockLifetime := by
    cases hstep with
    | blockB hdrops =>
        exact dropPreservation_lifetime hsafe hdrops hdomain hpreserve
  have hsafe' : store' ∼ₛ env' := by
    rw [henv']
    exact hsafeDrop
  exact ⟨validRuntimeState_blockB_step hvalidRuntime hdropDisjoint hstep,
    hsafe', hvalidValue⟩

/--
Lemma 4.11, `R-BlockB` one-step preservation when the block lifetime is absent
from the store.  In this case the runtime lifetime drop and environment lifetime
drop are both no-ops.
-/
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
  intro hwellFormed hsafe hvalidRuntime htyping hmulti
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
          exact preservation_copy_step_runtime hwellFormed hsafe hvalidRuntime htyping
            (Step.copy (lifetime := lifetime) hread))
    hmulti

/-- Lemma 4.11, multistep preservation for `R-Borrow` redexes. -/
theorem preservation_borrow_multistep_runtime {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {mutable : Bool} {finalValue : Value} :
    store ∼ₛ env →
    ValidRuntimeState store (.borrow mutable lv) →
    TermTyping env typing lifetime (.borrow mutable lv) (.borrow mutable [lv]) env₂ →
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

/--
Lemma 4.11, multistep preservation for variable `R-Move` redexes, factored
through the move/update preservation obligations.

The paper's `R-Move` proof relies on Update Preservation for the overwritten
source slot.  For the abstract store, we expose the two facts needed by the
one-step fragment: the moved value remains valid in the post-store, and all
other environment slots keep valid abstractions.
-/
theorem preservation_move_var_multistep_runtime_of_preserved
    {store finalStore : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping}
    {current lifetime valueLifetime : Lifetime}
    {x : Name} {finalValue : Value} {ty : Ty} :
    WellFormedEnv env₁ current →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.move (.var x)) →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    TermTyping env₁ typing lifetime (.move (.var x)) ty env₂ →
    (∀ store' value,
      Step store lifetime (.move (.var x)) store' (.val value) →
      ValidValue store' value ty) →
    (∀ store' value,
      Step store lifetime (.move (.var x)) store' (.val value) →
      ∀ y envSlot oldValue,
        y ≠ x →
        env₁.slotAt y = some envSlot →
        store.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := envSlot.lifetime } →
        ValidPartialValue store' oldValue envSlot.ty) →
    MultiStep store lifetime (.move (.var x)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hwellFormed hsafe hvalidRuntime henvSlot hmove htyping hvaluePreserved
    hpreserveOld hmulti
  exact preservation_runtime_multistep_of_step_to_value
    (term := .move (.var x))
    (ty := ty)
    (by simp [Terminal])
    (by
      intro _store' _term' hstep
      cases hstep with
      | move _hread _hwrite =>
          exact ⟨_, rfl⟩)
    (by
      intro store' value hstep
      cases hstep with
      | move hread hwrite =>
          exact preservation_move_var_step_runtime hwellFormed hsafe hvalidRuntime
            henvSlot hmove htyping
            (Step.move (lifetime := lifetime) hread hwrite)
            (hvaluePreserved store' value
              (Step.move (lifetime := lifetime) hread hwrite))
            (hpreserveOld store' value
              (Step.move (lifetime := lifetime) hread hwrite)))
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

/--
Lemma 4.11, `T-Declare` composition step.

This is the induction-over-constructor shape for `let mut x = t`: apply the
preservation induction hypothesis to the initializer, then apply `R-Declare`.
The `env₂.fresh x` premise is the paper-side freshness fact needed after the
initializer has produced its output environment.
-/
theorem preservation_declare_context_multistep_runtime
    {store midStore finalStore : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {value finalValue : Value} :
    (∀ {innerTy innerEnv},
      ValidRuntimeState store term →
      ValidStoreTyping store term typing →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime term innerTy innerEnv →
      MultiStep store lifetime term midStore (.val value) →
      ValidRuntimeState midStore (.val value) ∧ midStore ∼ₛ innerEnv ∧
        ValidValue midStore value innerTy) →
    (∀ {innerTy innerEnv},
      TermTyping env₁ typing lifetime term innerTy innerEnv →
      innerEnv.fresh x) →
    ValidRuntimeState store (.letMut x term) →
    ValidStoreTyping store (.letMut x term) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.letMut x term) .unit env₃ →
    MultiStep store lifetime term midStore (.val value) →
    Step midStore lifetime (.letMut x (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hinnerPreservation hfreshAfter hvalidRuntime hvalidStoreTyping hsafe htyping
    hinnerMulti hdeclareStep
  cases htyping with
  | declare _hfresh₁ hinnerTyping henv₃ =>
      rcases hinnerPreservation
          (validRuntimeState_declare_inner hvalidRuntime)
          (validStoreTyping_declare_inner hvalidStoreTyping)
          hsafe hinnerTyping hinnerMulti with
        ⟨hvalidInner, hsafeInner, hvalidValue⟩
      cases hdeclareStep with
      | declare hstore =>
          have hpreserved :=
            preservation_declare_redex_runtime_of_validValue hsafeInner
              (hfreshAfter hinnerTyping)
              (validRuntimeState_declare_value_of_value hvalidInner)
              hvalidValue
              (Step.declare (lifetime := lifetime) hstore)
          rw [henv₃]
          exact hpreserved

/--
Lemma 4.11, `T-Declare` multistep preservation case.

This packages the operational decomposition of a terminal `let mut x = t`
reduction with the constructor-shaped preservation composition above.
-/
theorem preservation_declare_context_terminal_multistep_runtime
    {store finalStore : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {finalValue : Value} :
    (∀ {midStore value innerTy innerEnv},
      ValidRuntimeState store term →
      ValidStoreTyping store term typing →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime term innerTy innerEnv →
      MultiStep store lifetime term midStore (.val value) →
      ValidRuntimeState midStore (.val value) ∧ midStore ∼ₛ innerEnv ∧
        ValidValue midStore value innerTy) →
    (∀ {innerTy innerEnv},
      TermTyping env₁ typing lifetime term innerTy innerEnv →
      innerEnv.fresh x) →
    ValidRuntimeState store (.letMut x term) →
    ValidStoreTyping store (.letMut x term) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.letMut x term) .unit env₃ →
    MultiStep store lifetime (.letMut x term) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hinnerPreservation hfreshAfter hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
  rcases multistep_declare_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hdeclareStep⟩
  exact preservation_declare_context_multistep_runtime
    (midStore := midStore)
    (value := value)
    (by
      intro innerTy innerEnv hvalidInner hvalidStoreTypingInner hsafeInner hinnerTyping
        hmultiInner
      exact hinnerPreservation (midStore := midStore) (value := value)
        (innerTy := innerTy) (innerEnv := innerEnv)
        hvalidInner hvalidStoreTypingInner hsafeInner
        hinnerTyping hmultiInner)
    hfreshAfter
    hvalidRuntime hvalidStoreTyping hsafe htyping hinnerMulti hdeclareStep

/--
Lemma 4.11, `T-Assign` composition step.

This is the induction-over-constructor shape for `w = t`: apply the
preservation induction hypothesis to the RHS, then discharge the assignment
redex with the paper's Update Preservation obligation.
-/
theorem preservation_assign_context_multistep_runtime
    {store midStore finalStore : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {lhs : LVal} {rhs : Term} {value finalValue : Value} :
    (∀ {rhsTy env₂},
      ValidRuntimeState store rhs →
      ValidStoreTyping store rhs typing →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      MultiStep store lifetime rhs midStore (.val value) →
      ValidRuntimeState midStore (.val value) ∧ midStore ∼ₛ env₂ ∧
        ValidValue midStore value rhsTy) →
    (∀ {targetLifetime oldTy rhsTy env₂},
      LValTyping env₁ lhs oldTy targetLifetime →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      ShapeCompatible env₂ oldTy (.ty rhsTy) →
      WellFormedTy env₂ rhsTy targetLifetime →
      EnvWrite 0 env₂ lhs rhsTy env₃ →
      ¬ WriteProhibited env₃ lhs →
      ValidRuntimeState midStore (.assign lhs (.val value)) →
      midStore ∼ₛ env₂ →
      ValidValue midStore value rhsTy →
      Step midStore lifetime (.assign lhs (.val value)) finalStore (.val finalValue) →
      ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
        ValidValue finalStore finalValue .unit) →
    ValidRuntimeState store (.assign lhs rhs) →
    ValidStoreTyping store (.assign lhs rhs) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.assign lhs rhs) .unit env₃ →
    MultiStep store lifetime rhs midStore (.val value) →
    Step midStore lifetime (.assign lhs (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hinnerPreservation hassignRedex hvalidRuntime hvalidStoreTyping hsafe htyping
    hinnerMulti hassignStep
  cases htyping with
  | assign hLv hinnerTyping hshape hwellTy hwrite hnotWrite =>
      rcases hinnerPreservation
          (validRuntimeState_assign_inner hvalidRuntime)
          (validStoreTyping_assign_inner hvalidStoreTyping)
          hsafe hinnerTyping hinnerMulti with
        ⟨hvalidInner, hsafeInner, hvalidValue⟩
      exact hassignRedex hLv hinnerTyping hshape hwellTy hwrite hnotWrite
        (validRuntimeState_assign_value_of_value hvalidInner)
        hsafeInner hvalidValue hassignStep

/--
Lemma 4.11, `T-Assign` multistep preservation case.

This packages the operational decomposition of a terminal assignment reduction
with the constructor-shaped preservation composition above.
-/
theorem preservation_assign_context_terminal_multistep_runtime
    {store finalStore : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {lhs : LVal} {rhs : Term} {finalValue : Value} :
    (∀ {midStore value rhsTy env₂},
      ValidRuntimeState store rhs →
      ValidStoreTyping store rhs typing →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      MultiStep store lifetime rhs midStore (.val value) →
      ValidRuntimeState midStore (.val value) ∧ midStore ∼ₛ env₂ ∧
        ValidValue midStore value rhsTy) →
    (∀ {midStore value targetLifetime oldTy rhsTy env₂},
      LValTyping env₁ lhs oldTy targetLifetime →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      ShapeCompatible env₂ oldTy (.ty rhsTy) →
      WellFormedTy env₂ rhsTy targetLifetime →
      EnvWrite 0 env₂ lhs rhsTy env₃ →
      ¬ WriteProhibited env₃ lhs →
      ValidRuntimeState midStore (.assign lhs (.val value)) →
      midStore ∼ₛ env₂ →
      ValidValue midStore value rhsTy →
      Step midStore lifetime (.assign lhs (.val value)) finalStore (.val finalValue) →
      ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
        ValidValue finalStore finalValue .unit) →
    ValidRuntimeState store (.assign lhs rhs) →
    ValidStoreTyping store (.assign lhs rhs) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.assign lhs rhs) .unit env₃ →
    MultiStep store lifetime (.assign lhs rhs) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hinnerPreservation hassignRedex hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
  rcases multistep_assign_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hassignStep⟩
  exact preservation_assign_context_multistep_runtime
    (midStore := midStore)
    (value := value)
    (by
      intro rhsTy env₂ hvalidInner hvalidStoreTypingInner hsafeInner hinnerTyping
        hmultiInner
      exact hinnerPreservation (midStore := midStore) (value := value)
        (rhsTy := rhsTy) (env₂ := env₂)
        hvalidInner hvalidStoreTypingInner hsafeInner hinnerTyping hmultiInner)
    (by
      intro targetLifetime oldTy rhsTy env₂ hLv hinnerTyping hshape hwellTy hwrite
        hnotWrite hvalidAssign hsafeAssign hvalidValue hstep
      exact hassignRedex (midStore := midStore) (value := value)
        (targetLifetime := targetLifetime) (oldTy := oldTy)
        (rhsTy := rhsTy) (env₂ := env₂)
        hLv hinnerTyping hshape hwellTy hwrite hnotWrite
        hvalidAssign hsafeAssign hvalidValue hstep)
    hvalidRuntime hvalidStoreTyping hsafe htyping hinnerMulti hassignStep

/--
Lemma 4.11, multistep preservation for `R-BlockB` redexes when the block
lifetime is absent from the store.
-/
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

/--
Lemma 4.11, multistep preservation for `R-BlockB` redexes, factored through
the paper's Drop Preservation obligations.

This is the general version of the absent-lifetime special case below: the
runtime lifetime drop must provide domain agreement with `Γ.dropLifetime` and
preservation of valid abstractions for surviving variables.
-/
theorem preservation_blockB_value_multistep_runtime_of_drop_preserved
    {store finalStore : ProgramStore} {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    store ∼ₛ env →
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    LifetimeDropOwnersDisjoint store blockLifetime →
    ValidValue store value ty →
    (∀ store',
      DropsLifetime store blockLifetime store' →
      ValidValue store' value ty) →
    (∀ store',
      DropsLifetime store blockLifetime store' →
      ∀ x,
        (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
          ∃ envSlot, (env.dropLifetime blockLifetime).slotAt x = some envSlot) →
    (∀ store',
      DropsLifetime store blockLifetime store' →
      ∀ x envSlot,
        env.slotAt x = some envSlot →
        envSlot.lifetime ≠ blockLifetime →
        ∃ oldValue,
          store'.slotAt (VariableProjection x) =
            some { value := oldValue, lifetime := envSlot.lifetime } ∧
          ValidPartialValue store' oldValue envSlot.ty) →
    MultiStep store lifetime (.block blockLifetime [.val value]) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env' ∧
      ValidValue finalStore finalValue ty := by
  intro hvalidRuntime hsafe htyping hdropDisjoint _hvalidValue hresultValue hdomain hpreserve
    hmulti
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
          exact preservation_blockB_value_step_runtime_of_drop_preserved
            hvalidRuntime hsafe htyping hdropDisjoint
            (Step.blockB (lifetime := lifetime) hdrops)
            (hresultValue _store' hdrops)
            (hdomain _store' hdrops)
            (hpreserve _store' hdrops))
    hmulti

/--
Lemma 4.11, block terminal multistep dispatcher.

The operational decomposition of a terminal block reduction has exactly the
three paper rule shapes: `R-Seq`, `R-BlockA`, and `R-BlockB`.  This theorem is
the preservation-side induction skeleton; the branch premises are discharged by
the term-list preservation proof and the paper's Drop Preservation obligations.
-/
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

/-- Lemma 9.9, `R-Assign` one-step value preservation fragment. -/
theorem valuePreservation_assign_step {store₁ store₂ : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {value : Value} :
    Step store₁ lifetime (.assign lhs (.val value)) store₂ (.val .unit) →
    ValidValue store₂ .unit .unit := by
  intro _hstep
  exact ValidPartialValue.unit

/-- Lemma 9.9, `R-Declare` one-step value preservation fragment. -/
theorem valuePreservation_declare_step {store₁ store₂ : ProgramStore}
    {lifetime : Lifetime} {x : Name} {value : Value} :
    Step store₁ lifetime (.letMut x (.val value)) store₂ (.val .unit) →
    ValidValue store₂ .unit .unit := by
  intro _hstep
  exact ValidPartialValue.unit

/-! ## Section 4.4: Progress Support -/

/-- Lemma 4.10 result shape: a term is terminal or can take one step. -/
def ProgressResult (store : ProgramStore) (lifetime : Lifetime) (term : Term) : Prop :=
  Terminal term ∨ ∃ store' term', Step store lifetime term store' term'

/--
Operational totality facts the paper gets from finite program stores.

Our `ProgramStore` is an abstract partial map, so these are separated as an
explicit progress assumption instead of being postulated globally.
-/
structure OperationalStoreProgress (store : ProgramStore) : Prop where
  freshHeap : ∃ address, store.fresh (.heap address)
  dropValue : ∀ value : Value, ∃ store', Drops store [.value value] store'
  dropPartial : ∀ value : PartialValue, ∃ store', Drops store [value] store'
  dropLifetime : ∀ lifetime : Lifetime, ∃ store', DropsLifetime store lifetime store'

/-! ### Drop Existence Fragments -/

theorem drops_nonOwner {store : ProgramStore} {value : PartialValue} :
    PartialValueNonOwner value →
    Drops store [value] store := by
  intro hnonOwner
  exact ProgramStore.Drops.nonOwner hnonOwner ProgramStore.Drops.nil

/--
Finite-support drop existence.

The paper treats stores as finite maps, so recursive `drop` always terminates:
an owning-reference drop either finds no slot or erases one supported location
before continuing.  This lemma is the abstract support-based form used to derive
operational progress for concrete finite stores.
-/
theorem drops_exists_of_supported :
    ∀ (support : Finset Location) (store : ProgramStore) (values : List PartialValue),
      (∀ location slot, store.slotAt location = some slot → location ∈ support) →
      ∃ store', Drops store values store'
  | support, store, [], _hsupported => ⟨store, ProgramStore.Drops.nil⟩
  | support, store, value :: rest, hsupported => by
      cases value with
      | undef =>
          rcases drops_exists_of_supported support store rest hsupported with
            ⟨store', hdrops⟩
          exact ⟨store', ProgramStore.Drops.nonOwner partialValueNonOwner_undef hdrops⟩
      | value runtimeValue =>
          cases runtimeValue with
          | unit =>
              rcases drops_exists_of_supported support store rest hsupported with
                ⟨store', hdrops⟩
              exact ⟨store', ProgramStore.Drops.nonOwner partialValueNonOwner_unit hdrops⟩
          | int n =>
              rcases drops_exists_of_supported support store rest hsupported with
                ⟨store', hdrops⟩
              exact ⟨store', ProgramStore.Drops.nonOwner (partialValueNonOwner_int n) hdrops⟩
          | ref ref =>
              cases howner : ref.owner with
              | false =>
                  rcases drops_exists_of_supported support store rest hsupported with
                    ⟨store', hdrops⟩
                  exact ⟨store', ProgramStore.Drops.nonOwner (by
                    cases ref with
                    | mk location owner =>
                        simp at howner
                        subst howner
                        exact partialValueNonOwner_borrowed location) hdrops⟩
              | true =>
                  by_cases hpresent : ∃ slot, store.slotAt ref.location = some slot
                  · rcases hpresent with ⟨slot, hslot⟩
                    have hmem : ref.location ∈ support :=
                      hsupported ref.location slot hslot
                    have hsupportedErase :
                        ∀ location slot',
                          (store.erase ref.location).slotAt location = some slot' →
                          location ∈ support.erase ref.location := by
                      intro location slot' hslot'
                      by_cases hsame : location = ref.location
                      · subst hsame
                        simp [ProgramStore.erase] at hslot'
                      · have hslotOriginal : store.slotAt location = some slot' := by
                          simpa [ProgramStore.erase, hsame] using hslot'
                        exact Finset.mem_erase.mpr
                          ⟨hsame, hsupported location slot' hslotOriginal⟩
                    rcases drops_exists_of_supported (support.erase ref.location)
                        (store.erase ref.location) (slot.value :: rest) hsupportedErase with
                      ⟨store', hdrops⟩
                    exact ⟨store',
                      ProgramStore.Drops.ownerPresent howner hslot hdrops⟩
                  · have hmissing : store.slotAt ref.location = none := by
                      cases hslot : store.slotAt ref.location with
                      | none => rfl
                      | some slot =>
                          exact False.elim (hpresent ⟨slot, hslot⟩)
                    rcases drops_exists_of_supported support store rest hsupported with
                      ⟨store', hdrops⟩
                    exact ⟨store',
                      ProgramStore.Drops.ownerMissing howner hmissing hdrops⟩
termination_by support _store values => support.card + values.length
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have hcard : (support.erase ref.location).card < support.card :=
        Finset.card_erase_lt_of_mem hmem
      omega

theorem drops_empty_value (value : Value) :
    ∃ store', Drops ProgramStore.empty [.value value] store' := by
  cases value with
  | unit =>
      exact ⟨ProgramStore.empty,
        drops_nonOwner (by intro ref; exact Or.inl (by simp))⟩
  | int value =>
      exact ⟨ProgramStore.empty,
        drops_nonOwner (by intro ref; exact Or.inl (by simp))⟩
  | ref ref =>
      cases howner : ref.owner with
      | false =>
          exact ⟨ProgramStore.empty,
            drops_nonOwner (by
              intro candidate
              by_cases href : PartialValue.value (Value.ref ref) =
                  PartialValue.value (Value.ref candidate)
              · injection href with hrefValue
                injection hrefValue with hrefRef
                subst hrefRef
                exact Or.inr howner
              · exact Or.inl href)⟩
      | true =>
          exact ⟨ProgramStore.empty,
            ProgramStore.Drops.ownerMissing howner (by simp [ProgramStore.empty])
              ProgramStore.Drops.nil⟩

theorem drops_empty_partial (value : PartialValue) :
    ∃ store', Drops ProgramStore.empty [value] store' := by
  cases value with
  | undef =>
      exact ⟨ProgramStore.empty,
        drops_nonOwner (by intro ref; exact Or.inl (by simp))⟩
  | value value =>
      exact drops_empty_value value

theorem drops_empty_lifetime (lifetime : Lifetime) :
    ∃ store', DropsLifetime ProgramStore.empty lifetime store' := by
  exact ⟨ProgramStore.empty, ProgramStore.DropsLifetime.intro (dropSet := []) (by
      intro value
      constructor
      · intro hmem
        cases hmem
      · intro h
        rcases h with ⟨location, slot, hslot, _hlifetime, _hvalue⟩
        simp [ProgramStore.empty] at hslot)
    ProgramStore.Drops.nil⟩

@[simp] theorem operationalStoreProgress_empty :
    OperationalStoreProgress ProgramStore.empty := by
  constructor
  · exact ⟨0, by simp [ProgramStore.fresh, ProgramStore.empty]⟩
  · exact drops_empty_value
  · exact drops_empty_partial
  · exact drops_empty_lifetime

/--
A program store bundled with the operational witnesses needed by Progress.

This is intentionally a certified wrapper around `ProgramStore`, not a
replacement for the paper's mathematical store.  The bare `ProgramStore` is an
arbitrary partial-map function, so progress cannot prove freshness/drop/write
totality for every inhabitant without an additional finite/well-behaved-store
invariant.
-/
structure OperationalProgramStore where
  toProgramStore : ProgramStore
  progress : OperationalStoreProgress toProgramStore

namespace OperationalProgramStore

instance : Coe OperationalProgramStore ProgramStore where
  coe store := store.toProgramStore

@[simp] theorem operationalStoreProgress (store : OperationalProgramStore) :
    OperationalStoreProgress (store : ProgramStore) :=
  store.progress

@[simp] def empty : OperationalProgramStore :=
  { toProgramStore := ProgramStore.empty
    progress := operationalStoreProgress_empty }

end OperationalProgramStore

theorem ProgressResult.step_of_not_terminal {store : ProgramStore}
    {lifetime : Lifetime} {term : Term} :
    ProgressResult store lifetime term →
    ¬ Terminal term →
    ∃ store' term', Step store lifetime term store' term' := by
  intro hprogress hnotTerminal
  rcases hprogress with hterminal | hstep
  · exact False.elim (hnotTerminal hterminal)
  · exact hstep

/-- Lemma 4.10, `T-Const`/value case. -/
theorem progress_value (store : ProgramStore) (lifetime : Lifetime) (value : Value) :
    ProgressResult store lifetime (.val value) := by
  exact Or.inl (value_terminal value)

/-- Lemma 4.10, `R-Copy` lval base case. -/
theorem progress_copy_lval {store : ProgramStore} {env : Env}
    {current stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ value,
      Step store stepLifetime (.copy lv) store (.val value) := by
  intro hwellFormed hsafe htyping
  rcases readPreservation hwellFormed hsafe htyping with
    ⟨value, runtimeSlot, hread, hslotValue, _hvalid⟩
  rcases runtimeSlot with ⟨partialValue, runtimeLifetime⟩
  cases hslotValue
  exact ⟨value, Step.copy (valueLifetime := runtimeLifetime) hread⟩

/-- Lemma 4.10, `R-Move` lval base case. -/
theorem progress_move_lval {store : ProgramStore} {env : Env}
    {current stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ value store',
      Step store stepLifetime (.move lv) store' (.val value) := by
  intro hwellFormed hsafe htyping
  have hlocation : LValLocationAbstraction store lv (.ty ty) :=
    lvalTyping_defined_location hwellFormed hsafe htyping
  rcases readPreservation_of_location hlocation with
    ⟨value, runtimeSlot, hread, hslotValue, _hvalid⟩
  rcases write_defined_of_location (value := PartialValue.undef) hlocation with
    ⟨store', hwrite⟩
  rcases runtimeSlot with ⟨partialValue, runtimeLifetime⟩
  cases hslotValue
  exact ⟨value, store', Step.move (valueLifetime := runtimeLifetime) hread hwrite⟩

/-- Lemma 4.10, `R-Borrow` lval base case. -/
theorem progress_borrow_lval {store : ProgramStore} {env : Env}
    {current stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {mutable : Bool} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ location,
      Step store stepLifetime (.borrow mutable lv) store
        (.val (.ref { location := location, owner := false })) := by
  intro hwellFormed hsafe htyping
  rcases lvalTyping_defined_location hwellFormed hsafe htyping with
    ⟨location, slot, hloc, _hslot, _hvalid⟩
  exact ⟨location, Step.borrow hloc⟩

/-- Lemma 4.10, `box E` evaluation-context case. -/
theorem progress_subBox {store : ProgramStore} {lifetime : Lifetime}
    {term : Term} :
    (∃ store' term', Step store lifetime term store' term') →
    ProgressResult store lifetime (.box term) := by
  intro hstep
  rcases hstep with ⟨store', term', hstep⟩
  exact Or.inr ⟨store', .box term', Step.subBox hstep⟩

/-- Lemma 4.10, `let mut x = E` evaluation-context case. -/
theorem progress_subDeclare {store : ProgramStore} {lifetime : Lifetime}
    {x : Name} {term : Term} :
    (∃ store' term', Step store lifetime term store' term') →
    ProgressResult store lifetime (.letMut x term) := by
  intro hstep
  rcases hstep with ⟨store', term', hstep⟩
  exact Or.inr ⟨store', .letMut x term', Step.subDeclare hstep⟩

/-- Lemma 4.10, `w = E` evaluation-context case. -/
theorem progress_subAssign {store : ProgramStore} {lifetime : Lifetime}
    {lhs : LVal} {rhs : Term} :
    (∃ store' rhs', Step store lifetime rhs store' rhs') →
    ProgressResult store lifetime (.assign lhs rhs) := by
  intro hstep
  rcases hstep with ⟨store', rhs', hstep⟩
  exact Or.inr ⟨store', .assign lhs rhs', Step.subAssign hstep⟩

/-- Lemma 4.10, block-head evaluation-context case. -/
theorem progress_block_head {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {term : Term} {rest : List Term} :
    (∃ store' term', Step store blockLifetime term store' term') →
    ProgressResult store lifetime (.block blockLifetime (term :: rest)) := by
  intro hstep
  rcases hstep with ⟨store', term', hstep⟩
  exact Or.inr ⟨store', .block blockLifetime (term' :: rest), Step.blockA hstep⟩

/-- Lemma 4.10, typed `box E` context case. -/
theorem progress_box_context_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    ProgressResult store lifetime term →
    ¬ Terminal term →
    ProgressResult store lifetime (.box term) := by
  intro _htyping hprogress hnotTerminal
  exact progress_subBox (hprogress.step_of_not_terminal hnotTerminal)

/-- Lemma 4.10, typed `let mut x = E` context case. -/
theorem progress_declare_context_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name} {term : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime (.letMut x term) ty env₂ →
    ProgressResult store lifetime term →
    ¬ Terminal term →
    ProgressResult store lifetime (.letMut x term) := by
  intro _htyping hprogress hnotTerminal
  exact progress_subDeclare (hprogress.step_of_not_terminal hnotTerminal)

/-- Lemma 4.10, typed `w = E` context case. -/
theorem progress_assign_context_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lhs : LVal} {rhs : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime (.assign lhs rhs) ty env₂ →
    ProgressResult store lifetime rhs →
    ¬ Terminal rhs →
    ProgressResult store lifetime (.assign lhs rhs) := by
  intro _htyping hprogress hnotTerminal
  exact progress_subAssign (hprogress.step_of_not_terminal hnotTerminal)

/-- Lemma 4.10, `T-Copy` base case. -/
theorem progress_copy_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current stepLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing stepLifetime (.copy lv) ty env₂ →
    ProgressResult store stepLifetime (.copy lv) := by
  intro hwellFormed hsafe htyping
  cases htyping with
  | copy hLv _copyTy _hreadProhibited =>
      rcases progress_copy_lval hwellFormed hsafe hLv with ⟨value, hstep⟩
      exact Or.inr ⟨store, .val value, hstep⟩

/-- Lemma 4.10, `T-Move` base case. -/
theorem progress_move_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current stepLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing stepLifetime (.move lv) ty env₂ →
    ProgressResult store stepLifetime (.move lv) := by
  intro hwellFormed hsafe htyping
  cases htyping with
  | move hLv _hwriteProhibited _hmove =>
      rcases progress_move_lval hwellFormed hsafe hLv with ⟨value, store', hstep⟩
      exact Or.inr ⟨store', .val value, hstep⟩

/-- Lemma 4.10, `T-MutBorrow`/`T-ImmBorrow` base case. -/
theorem progress_borrow_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current stepLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {mutable : Bool} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing stepLifetime (.borrow mutable lv) ty env₂ →
    ProgressResult store stepLifetime (.borrow mutable lv) := by
  intro hwellFormed hsafe htyping
  cases htyping with
  | mutBorrow hLv _hmut _hwriteProhibited =>
      rcases progress_borrow_lval (mutable := true) hwellFormed hsafe hLv with
        ⟨location, hstep⟩
      exact Or.inr ⟨store, .val (.ref { location := location, owner := false }), hstep⟩
  | immBorrow hLv _hreadProhibited =>
      rcases progress_borrow_lval (mutable := false) hwellFormed hsafe hLv with
        ⟨location, hstep⟩
      exact Or.inr ⟨store, .val (.ref { location := location, owner := false }), hstep⟩

/--
Lemma 4.10, `R-Box` value case.

The paper obtains a fresh heap location from finiteness of stores.  Our
`ProgramStore` is an abstract partial map, so this case is stated with the
fresh address witness as an explicit premise.
-/
theorem progress_box_value_at {store : ProgramStore} {lifetime : Lifetime}
    {address : Nat} {value : Value} :
    store.fresh (.heap address) →
    ProgressResult store lifetime (.box (.val value)) := by
  intro hfresh
  exact Or.inr ⟨(store.boxAt address value).1,
    .val (.ref (store.boxAt address value).2),
    Step.box (address := address) (ref := (store.boxAt address value).2)
      hfresh rfl⟩

theorem progress_box_value {store : ProgramStore} {lifetime : Lifetime} {value : Value} :
    OperationalStoreProgress store →
    ProgressResult store lifetime (.box (.val value)) := by
  intro hstore
  rcases hstore.freshHeap with ⟨address, hfresh⟩
  exact progress_box_value_at (address := address) hfresh

/-- Lemma 4.10, `R-Assign` value case, with the required drop/write witnesses. -/
theorem progress_assign_value_at {store storeAfterDrop storeAfterWrite : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot} {value : Value} :
    store.read lhs = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write lhs (.value value) = some storeAfterWrite →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hread hdrops hwrite
  exact Or.inr ⟨storeAfterWrite, .val .unit, Step.assign hread hdrops hwrite⟩

theorem progress_assign_value {store : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot} {value : Value} :
    PartialValueNonOwner oldSlot.value →
    store.read lhs = some oldSlot →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hnonOwner hread
  let hdrops : Drops store [oldSlot.value] store := drops_nonOwner hnonOwner
  rcases write_defined_of_allocated (store := store) (lv := lhs)
      (value := PartialValue.value value) (allocated_of_read hread) with
    ⟨storeAfterWrite, hwrite⟩
  exact progress_assign_value_at hread hdrops hwrite

/-- Lemma 4.10, `T-Assign` value case. -/
theorem progress_assign_value_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lhs : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    OperationalStoreProgress store →
    TermTyping env typing lifetime (.assign lhs (.val value)) ty env₂ →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hwellFormed hsafe _hstore htyping
  cases htyping with
  | assign hLhs hRhs hshape _hwf _hwriteEnv _hnotWriteProhibited =>
      rcases read_defined_of_allocated
          (lvalTyping_allocated_location hwellFormed hsafe hLhs) with
        ⟨oldSlot, hread⟩
      cases hRhs with
      | const _hvalue =>
          have hnonOwner :
              PartialValueNonOwner oldSlot.value :=
            lvalTyping_read_nonOwner_of_shapeCompatible
              hwellFormed hsafe hLhs hshape hread
          exact progress_assign_value hnonOwner hread

/--
Lemma 4.10, `R-Seq` value case, with the required drop witness.

For abstract stores, existence of this witness is not automatic without a
finite/drop-normalisation invariant.
-/
theorem progress_seq_value_at {store storeAfterDrop : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    Drops store [.value value] storeAfterDrop →
    ProgressResult store lifetime (.block blockLifetime (.val value :: next :: rest)) := by
  intro hdrops
  exact Or.inr ⟨storeAfterDrop, .block blockLifetime (next :: rest), Step.seq hdrops⟩

theorem progress_seq_value {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    OperationalStoreProgress store →
    ProgressResult store lifetime (.block blockLifetime (.val value :: next :: rest)) := by
  intro hstore
  rcases hstore.dropValue value with ⟨store', hdrops⟩
  exact progress_seq_value_at (storeAfterDrop := store') hdrops

/--
Lemma 4.10, `R-BlockB` value case, with the required lifetime-drop witness.
-/
theorem progress_block_value_at {store storeAfterDrop : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} :
    DropsLifetime store blockLifetime storeAfterDrop →
    ProgressResult store lifetime (.block blockLifetime [.val value]) := by
  intro hdrops
  exact Or.inr ⟨storeAfterDrop, .val value, Step.blockB hdrops⟩

theorem progress_block_value {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} :
    OperationalStoreProgress store →
    ProgressResult store lifetime (.block blockLifetime [.val value]) := by
  intro hstore
  rcases hstore.dropLifetime blockLifetime with ⟨store', hdrops⟩
  exact progress_block_value_at (storeAfterDrop := store') hdrops

/-- Lemma 4.10, `T-Declare` value case. -/
theorem progress_declare_value_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name}
    {value : Value} {ty : Ty} :
    TermTyping env typing lifetime (.letMut x (.val value)) ty env₂ →
    ProgressResult store lifetime (.letMut x (.val value)) := by
  intro htyping
  cases htyping with
  | declare _hfresh _hinit _henv =>
      exact Or.inr ⟨store.declare x lifetime value, .val .unit, Step.declare rfl⟩

/-- Lemma 4.10, composed `T-Box` progress case. -/
theorem progress_box_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    ProgressResult store lifetime term →
    ProgressResult store lifetime (.box term) := by
  intro hstore _htyping hprogress
  rcases hprogress with hterminal | hstep
  · rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
    subst hterm
    exact progress_box_value hstore
  · exact progress_subBox hstep

/-- Lemma 4.10, composed `T-Declare` progress case. -/
theorem progress_declare_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name} {term : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime (.letMut x term) ty env₂ →
    ProgressResult store lifetime term →
    ProgressResult store lifetime (.letMut x term) := by
  intro htyping hprogress
  rcases hprogress with hterminal | hstep
  · rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
    subst hterm
    exact progress_declare_value_typing htyping
  · exact progress_subDeclare hstep

/-- Lemma 4.10, composed `T-Assign` progress case. -/
theorem progress_assign_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lhs : LVal}
    {rhs : Term} {ty : Ty} :
    WellFormedEnv env₁ current →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime (.assign lhs rhs) ty env₂ →
    ProgressResult store lifetime rhs →
    ProgressResult store lifetime (.assign lhs rhs) := by
  intro hwellFormed hsafe hstore htyping hprogress
  rcases hprogress with hterminal | hstep
  · rcases (terminal_iff_value rhs).mp hterminal with ⟨value, hrhs⟩
    subst hrhs
    exact progress_assign_value_typing hwellFormed hsafe hstore htyping
  · exact progress_subAssign hstep

/-- Lemma 4.10, composed block-head progress case. -/
theorem progress_block_of_head_progress {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {term : Term} {rest : List Term} :
    OperationalStoreProgress store →
    ProgressResult store blockLifetime term →
    ProgressResult store lifetime (.block blockLifetime (term :: rest)) := by
  intro hstore hprogress
  rcases hprogress with hterminal | hstep
  · rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
    subst hterm
    cases rest with
    | nil =>
        exact progress_block_value hstore
    | cons next rest =>
        exact progress_seq_value hstore
  · exact progress_block_head hstep

/--
Lemma 4.10, Progress.

The paper states well-formedness for the current lifetime.  Because blocks step
their body under the block lifetime while the block itself steps under the
enclosing lifetime, this mechanised statement takes the well-formedness premise
for every lifetime needed by nested blocks.
-/
theorem progress_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hwellFormed hsafe hstore htyping
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      (∀ lifetime, WellFormedEnv env lifetime) →
      store ∼ₛ env →
      OperationalStoreProgress store →
      ProgressResult store lifetime term)
    (motive_2 := fun env typing blockLifetime terms ty env₂ _ =>
      ∀ lifetime,
        (∀ lifetime, WellFormedEnv env lifetime) →
        store ∼ₛ env →
        OperationalStoreProgress store →
        ProgressResult store lifetime (.block blockLifetime terms))
    (fun {_env _typing lifetime value _ty} _hvalue hwellFormed hsafe hstore =>
      progress_value store lifetime value)
    (fun {_env _typing lifetime _valueLifetime _lv _ty} hLv hcopy hreadProhibited
        hwellFormed hsafe _hstore =>
      progress_copy_typing (typing := _typing) (hwellFormed lifetime) hsafe
        (TermTyping.copy (typing := _typing) hLv hcopy hreadProhibited))
    (fun {_env₁ _env₂ _typing lifetime _valueLifetime _lv _ty} hLv hwriteProhibited hmove
        hwellFormed hsafe _hstore =>
      progress_move_typing (typing := _typing) (hwellFormed lifetime) hsafe
        (TermTyping.move (typing := _typing) hLv hwriteProhibited hmove))
    (fun {_env _typing lifetime _valueLifetime _lv _ty} hLv hmutable hwriteProhibited
        hwellFormed hsafe _hstore =>
      progress_borrow_typing (typing := _typing) (hwellFormed lifetime) hsafe
        (TermTyping.mutBorrow (typing := _typing) hLv hmutable hwriteProhibited))
    (fun {_env _typing lifetime _valueLifetime _lv _ty} hLv hreadProhibited
        hwellFormed hsafe _hstore =>
      progress_borrow_typing (typing := _typing) (hwellFormed lifetime) hsafe
        (TermTyping.immBorrow (typing := _typing) hLv hreadProhibited))
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih
        hwellFormed hsafe hstore =>
      progress_box_typing hstore (TermTyping.box hterm)
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _env₃ _typing lifetime _blockLifetime _terms _ty}
        _hterms _hwellTy _hdrop ih hwellFormed hsafe hstore =>
      ih lifetime hwellFormed hsafe hstore)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty} hfresh hterm henv ih
        hwellFormed hsafe hstore =>
      progress_declare_typing (TermTyping.declare hfresh hterm henv)
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _env₃ _typing lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwf hwrite hnotWriteProhibited ih hwellFormed hsafe hstore =>
      progress_assign_typing (hwellFormed lifetime) hsafe hstore
        (TermTyping.assign hLhs hRhs hshape hwf hwrite hnotWriteProhibited)
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _typing _blockLifetime _term _ty} _hterm ih
        outerLifetime hwellFormed hsafe hstore =>
      progress_block_of_head_progress hstore
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _env₃ _typing _blockLifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead _ihRest outerLifetime hwellFormed hsafe hstore =>
      progress_block_of_head_progress hstore
        (ihHead hwellFormed hsafe hstore))
    htyping hwellFormed hsafe hstore

/-- Lemma 4.10, Progress for a non-empty typed sequence represented as a block body. -/
theorem progress_termList_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    ProgressResult store lifetime (.block blockLifetime terms) := by
  intro hwellFormed hsafe hstore htyping
  cases htyping with
  | singleton hterm =>
      exact progress_block_of_head_progress hstore
        (progress_typing hwellFormed hsafe hstore hterm)
  | cons hterm _hrest =>
      exact progress_block_of_head_progress hstore
        (progress_typing hwellFormed hsafe hstore hterm)

/--
Lemma 4.10, paper-facing Progress statement.

`ValidState` and `ValidStoreTyping` are retained as premises to match the paper.
The current proof uses the safe-abstraction, well-formed-environment, and
operational-store-progress hypotheses directly.
-/
theorem progress {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro _hvalidState _hvalidStoreTyping hwellFormed hsafe hstore htyping
  exact progress_typing hwellFormed hsafe hstore htyping

/-- Lemma 4.10, Progress for the mechanised runtime-validity package. -/
theorem progress_runtime {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstore htyping
  exact progress hvalidRuntime.1 hvalidStoreTyping hwellFormed hsafe hstore htyping

/-- Lemma 4.10, Progress for a certified operational store. -/
theorem OperationalProgramStore.progressResult {store : OperationalProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidState (store : ProgramStore) term →
    ValidStoreTyping (store : ProgramStore) term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    (store : ProgramStore) ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult (store : ProgramStore) lifetime term := by
  intro hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact Paper.progress hvalidState hvalidStoreTyping hwellFormed hsafe store.progress htyping

/--
Lemma 4.10, Progress for the mechanised runtime-validity package over a
certified operational store.
-/
theorem OperationalProgramStore.progress_runtime {store : OperationalProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState (store : ProgramStore) term →
    ValidStoreTyping (store : ProgramStore) term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    (store : ProgramStore) ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult (store : ProgramStore) lifetime term := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe htyping
  exact Paper.progress_runtime hvalidRuntime hvalidStoreTyping hwellFormed hsafe
    store.progress htyping

/--
Lemma 4.10, non-terminal form.

This is the phrasing used when applying Progress inside the final soundness
argument: if the term is not already a value, one reduction step exists.
-/
theorem progress_step {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step store lifetime term store' term' := by
  intro hvalidState hvalidStoreTyping hwellFormed hsafe hstore htyping hnotTerminal
  exact (progress hvalidState hvalidStoreTyping hwellFormed hsafe hstore htyping).step_of_not_terminal
    hnotTerminal

/-- Lemma 4.10, non-terminal form for the mechanised runtime-validity package. -/
theorem progress_runtime_step {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step store lifetime term store' term' := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstore htyping hnotTerminal
  exact (progress_runtime hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstore htyping).step_of_not_terminal
    hnotTerminal

/-- Lemma 4.10, `R-Copy` variable-lval base case. -/
theorem progress_copy_var {store : ProgramStore} {env : Env}
    {lifetime : Lifetime} {x : Name} {slot : EnvSlot} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    ∃ value,
      Step store lifetime (.copy (.var x)) store (.val value) := by
  intro hsafe henv hty
  rcases readPreservation_var (store := store) (env := env)
      (x := x) (slot := slot) (ty := ty) hsafe henv hty with
    ⟨value, runtimeSlot, hread, hvalue, _hvalid⟩
  rcases runtimeSlot with ⟨partialValue, valueLifetime⟩
  cases hvalue
  exact ⟨value, Step.copy (valueLifetime := valueLifetime) hread⟩

/-- Lemma 4.10, `R-Move` variable-lval base case. -/
theorem progress_move_var {store : ProgramStore} {env : Env}
    {lifetime : Lifetime} {x : Name} {slot : EnvSlot} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    ∃ value store',
      Step store lifetime (.move (.var x)) store' (.val value) := by
  intro hsafe henv hty
  have hlocation :
      LValLocationAbstraction store (.var x) (.ty ty) := by
    simpa [hty] using location_var (store := store) (env := env) hsafe henv
  rcases readPreservation_of_location hlocation with
    ⟨value, runtimeSlot, hread, hvalue, _hvalid⟩
  rcases write_defined_of_location (value := PartialValue.undef) hlocation with
    ⟨store', hwrite⟩
  rcases runtimeSlot with ⟨partialValue, valueLifetime⟩
  cases hvalue
  exact ⟨value, store', Step.move (valueLifetime := valueLifetime) hread hwrite⟩

/-- Lemma 4.10, `R-Borrow` variable-lval base case. -/
theorem progress_borrow_var (store : ProgramStore) (lifetime : Lifetime)
    (mutable : Bool) (x : Name) :
    Step store lifetime (.borrow mutable (.var x)) store
      (.val (.ref { location := .var x, owner := false })) := by
  exact Step.borrow (by simp [ProgramStore.loc])

/-! ## Section 4.5: Type and Borrow Safety -/

/-- A term terminates when it multisteps to a runtime value. -/
def TerminatesAsValue (store : ProgramStore) (lifetime : Lifetime) (term : Term) : Prop :=
  ∃ finalStore finalValue,
    MultiStep store lifetime term finalStore (.val finalValue)

/--
The terminal safety conclusion of Lemma 4.11 / Theorem 4.12: the terminal state
is valid, the final store safely abstracts the output environment, and the
terminal value abstracts the result type.
-/
def TerminalStateSafe (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) :
    Prop :=
  ValidRuntimeState store (.val value) ∧ store ∼ₛ env ∧ ValidValue store value ty

/--
Theorem 4.12 bridge, Type and Borrow Safety.

The paper's core calculus is terminating, while this mechanisation keeps the
operational semantics relational.  Therefore the theorem is stated with an
explicit termination witness and the Lemma 4.11 preservation conclusion as a
premise.  Progress rules out an initially stuck well-typed state; preservation
turns the terminal multistep into the safe terminal state promised by the paper.
-/
theorem typeAndBorrowSafety_of_preservation
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    (∀ finalStore finalValue,
      MultiStep store lifetime term finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₂ ty) →
    TerminatesAsValue store lifetime term →
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress htyping
    hpreservation hterminates
  rcases hterminates with ⟨finalStore, finalValue, hmulti⟩
  exact ⟨progress_runtime hvalidRuntime hvalidStoreTyping hwellFormed hsafe
      hstoreProgress htyping,
    ⟨finalStore, finalValue, hmulti, hpreservation finalStore finalValue hmulti⟩⟩

/-! ## Section 4.5.1: Borrow Safety -/

/--
Definition 4.13, borrow-safe environment.

The paper phrases this over variables in `dom(Γ)` and borrowed lvals inside
contained borrow types.  The containment premises already imply the relevant
variables are present in the environment.
-/
def BorrowSafeEnv (env : Env) : Prop :=
  ∀ x y mutable targetsMutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ (&mut targetsMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    x = y

def TyBorrowFree (ty : Ty) : Prop :=
  ∀ mutable targets, ¬ PartialTyContains (.ty ty) (.borrow mutable targets)

def PartialTyBorrowFree (ty : PartialTy) : Prop :=
  ∀ mutable targets, ¬ PartialTyContains ty (.borrow mutable targets)

theorem partialTyContains_ty_iff_eq {ty needle : Ty} :
    PartialTyContains (.ty ty) needle ↔ ty = needle := by
  constructor
  · intro hcontains
    cases hcontains
    rfl
  · intro hty
    subst hty
    exact PartialTyContains.here

theorem tyBorrowFree_iff_not_borrow {ty : Ty} :
    TyBorrowFree ty ↔ ∀ mutable targets, ty ≠ .borrow mutable targets := by
  constructor
  · intro hfree mutable targets hty
    exact hfree mutable targets
      (partialTyContains_ty_iff_eq.mpr hty)
  · intro hnotBorrow mutable targets hcontains
    exact hnotBorrow mutable targets
      (partialTyContains_ty_iff_eq.mp hcontains)

theorem partialTyBorrowFree_ty {ty : Ty} :
    TyBorrowFree ty →
    PartialTyBorrowFree (.ty ty) := by
  intro hfree mutable targets hcontains
  exact hfree mutable targets hcontains

@[simp] theorem partialTyBorrowFree_undef (ty : Ty) :
    PartialTyBorrowFree (.undef ty) := by
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem partialTyBorrowFree_box {ty : PartialTy} :
    PartialTyBorrowFree ty →
    PartialTyBorrowFree (.box ty) := by
  intro hfree mutable targets hcontains
  cases hcontains with
  | box hinner =>
      exact hfree mutable targets hinner

@[simp] theorem tyBorrowFree_unit :
    TyBorrowFree .unit := by
  rw [tyBorrowFree_iff_not_borrow]
  intro mutable targets h
  cases h

@[simp] theorem tyBorrowFree_int :
    TyBorrowFree .int := by
  rw [tyBorrowFree_iff_not_borrow]
  intro mutable targets h
  cases h

@[simp] theorem tyBorrowFree_box (ty : Ty) :
    TyBorrowFree (.box ty) := by
  rw [tyBorrowFree_iff_not_borrow]
  intro mutable targets h
  cases h

theorem not_tyBorrowFree_borrow (mutable : Bool) (targets : List LVal) :
    ¬ TyBorrowFree (.borrow mutable targets) := by
  intro hfree
  exact hfree mutable targets PartialTyContains.here

@[simp] theorem borrowSafeEnv_empty :
    BorrowSafeEnv Env.empty := by
  intro x y mutable targetsMutable targetsOther targetMutable targetOther hcontains _ _ _ _
  rcases hcontains with ⟨slot, hslot, _hcontainsTy⟩
  simp [Env.empty] at hslot

theorem EnvContains.update_fresh_ne {env : Env} {x y : Name} {slot : EnvSlot}
    {ty : Ty} :
    y ≠ x →
    (env.update x slot) ⊢ y ↝ ty →
    env ⊢ y ↝ ty := by
  intro hy hcontains
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  exact ⟨containedSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩

theorem EnvContains.update_same {env : Env} {x : Name} {slot : EnvSlot}
    {ty : Ty} :
    PartialTyContains slot.ty ty →
    (env.update x slot) ⊢ x ↝ ty := by
  intro hcontains
  exact ⟨slot, by simp [Env.update], hcontains⟩

theorem pathConflicts_symm {left right : LVal} :
    left ⋈ right →
    right ⋈ left := by
  intro h
  exact h.symm

theorem not_envContains_update_fresh_same_of_borrowFree {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} {borrowTy : Ty} :
    TyBorrowFree ty →
    borrowTy = .borrow mutable targets →
    ¬ (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢ x ↝ borrowTy := by
  intro hborrowFree hborrowTy hcontains
  subst hborrowTy
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  have hslotEq :
      containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
    have h :
        { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
      simpa [Env.update] using hslot
    exact h.symm
  subst hslotEq
  exact hborrowFree mutable targets hcontainsTy

theorem borrowSafeEnv_update_partialBorrowFree {env : Env} {x : Name}
    {slot : EnvSlot} :
    BorrowSafeEnv env →
    PartialTyBorrowFree slot.ty →
    BorrowSafeEnv (env.update x slot) := by
  intro hsafe hborrowFree y z mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hy : y = x
  · have hcontainsMutableAtX :
        (env.update x slot) ⊢ x ↝ Ty.borrow true targetsMutable := by
      simpa [hy] using hcontainsMutable
    exact False.elim
      (by
        rcases hcontainsMutableAtX with ⟨containedSlot, hslot, hcontainsTy⟩
        have hslotEq : containedSlot = slot := by
          have h : slot = containedSlot := by
            simpa [Env.update] using hslot
          exact h.symm
        subst hslotEq
        exact hborrowFree true targetsMutable hcontainsTy)
  · by_cases hz : z = x
    · have hcontainsOtherAtX :
          (env.update x slot) ⊢ x ↝ Ty.borrow mutable targetsOther := by
        simpa [hz] using hcontainsOther
      exact False.elim
        (by
          rcases hcontainsOtherAtX with ⟨containedSlot, hslot, hcontainsTy⟩
          have hslotEq : containedSlot = slot := by
            have h : slot = containedSlot := by
              simpa [Env.update] using hslot
            exact h.symm
          subst hslotEq
          exact hborrowFree mutable targetsOther hcontainsTy)
    · exact hsafe y z mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hy hcontainsMutable)
        (EnvContains.update_fresh_ne hz hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_fresh_borrowFree {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    TyBorrowFree ty →
    BorrowSafeEnv (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hborrowFree
  exact borrowSafeEnv_update_partialBorrowFree hsafe
    (partialTyBorrowFree_ty hborrowFree)

theorem borrowSafeEnv_move_var {env env' : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.slotAt x = some { ty := .ty ty, lifetime := lifetime } →
    EnvMove env (.var x) env' →
    BorrowSafeEnv env' := by
  intro hsafe hslot hmove
  rcases hmove with ⟨slot, struck, hbaseSlot, hstrike, henv'⟩
  simp [LVal.base, LVal.path] at hbaseSlot hstrike henv'
  rw [hslot] at hbaseSlot
  injection hbaseSlot with hslotEq
  subst hslotEq
  cases struck with
  | ty struckTy =>
      cases hstrike
  | box struckInner =>
      cases hstrike
  | undef shape =>
      have hshape : ty = shape := hstrike
      subst hshape
      rw [henv']
      exact borrowSafeEnv_update_partialBorrowFree hsafe
        (partialTyBorrowFree_undef ty)

theorem borrowSafety_move_var {env env' : Env} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {x : Name} {ty : Ty} :
    BorrowSafeEnv env →
    env.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    TermTyping env typing lifetime (.move (.var x)) ty env' →
    BorrowSafeEnv env' := by
  intro hsafe hslot htyping
  cases htyping with
  | move _hLv _hnotWrite hmove =>
      exact borrowSafeEnv_move_var hsafe hslot hmove

theorem EnvContains.dropLifetime_of_contains {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    (env.dropLifetime lifetime) ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _hlifetime⟩
  exact ⟨slot, henvSlot, hcontainsTy⟩

theorem borrowSafeEnv_dropLifetime {env : Env} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    BorrowSafeEnv (env.dropLifetime lifetime) := by
  intro hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.dropLifetime_of_contains hcontainsMutable)
    (EnvContains.dropLifetime_of_contains hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafety_block_drop {env env' : Env} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env' = env.dropLifetime lifetime →
    BorrowSafeEnv env' := by
  intro hsafe henv'
  rw [henv']
  exact borrowSafeEnv_dropLifetime hsafe

theorem borrowSafety_copy {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {lv : LVal} {ty : Ty} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    BorrowSafeEnv env₂ := by
  intro hsafe htyping
  cases htyping
  exact hsafe

theorem borrowSafety_borrow {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {lv : LVal} {mutable : Bool} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow mutable lv) (.borrow mutable [lv]) env₂ →
    BorrowSafeEnv env₂ := by
  intro hsafe htyping
  cases htyping with
  | mutBorrow =>
      exact hsafe
  | immBorrow =>
      exact hsafe

theorem borrowSafeEnv_update_fresh_immBorrow {env : Env} {gamma : Name}
    {lv : LVal} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    ¬ ReadProhibited env lv →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) := by
  intro hsafe hfresh hnotRead x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq :
        Ty.borrow false [lv] = Ty.borrow true targetsMutable :=
      partialTyContains_ty_iff_eq.mp hcontainsTy
    cases hborrowEq
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq :
          Ty.borrow false [lv] = Ty.borrow mutable targetsOther :=
        partialTyContains_ty_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargets
      have htargetOtherEq : targetOther = lv := by
        cases htargets
        simpa using htargetOther
      subst htargetOtherEq
      exact False.elim (hnotRead ⟨x, targetsMutable, targetMutable,
        EnvContains.update_fresh_ne hx hcontainsMutable,
        htargetMutable,
        hconflict⟩)
    · exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafety_immBorrow_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow false lv) (.borrow false [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) := by
  intro hsafe htyping hfresh
  cases htyping with
  | immBorrow _hLv hnotRead =>
      exact borrowSafeEnv_update_fresh_immBorrow hsafe hfresh hnotRead

theorem borrowSafety_box_context {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    (TermTyping env₁ typing lifetime term ty env₂ → BorrowSafeEnv env₂) →
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    BorrowSafeEnv env₂ := by
  intro hinner htyping
  cases htyping with
  | box hterm =>
      exact hinner hterm

theorem borrowSafety_block_context {env₁ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    (∀ env₂, TermListTyping env₁ typing blockLifetime terms ty env₂ → BorrowSafeEnv env₂) →
    TermTyping env₁ typing lifetime (.block blockLifetime terms) ty env₃ →
    BorrowSafeEnv env₃ := by
  intro htermsSafe htyping
  cases htyping with
  | block hterms _hwellTy hdrop =>
      exact borrowSafety_block_drop (htermsSafe _ hterms) hdrop

/--
Corollary 4.14 support: extending the output environment with a fresh,
borrow-free result slot preserves both well-formedness and borrow safety.

The remaining borrow-safety work is the paper's typing-rule induction showing
that the output environment of a well-typed term is itself borrow safe.  This
theorem packages the final result-extension step from the corollary.
-/
theorem borrowSafety_result_extension_borrowFree {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env.fresh gamma →
    WellFormedEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hwellFormed hwellTy hborrowSafe hborrowFree hfresh
  exact ⟨borrowInvariance_result_extension hwellFormed hwellTy hfresh,
    borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree⟩

theorem borrowSafety_result_extension_nonBorrow {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv env →
    (∀ mutable targets, ty ≠ .borrow mutable targets) →
    env.fresh gamma →
    WellFormedEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hwellFormed hwellTy hborrowSafe hnotBorrow hfresh
  exact borrowSafety_result_extension_borrowFree hwellFormed hwellTy hborrowSafe
    (tyBorrowFree_iff_not_borrow.mpr hnotBorrow) hfresh

/--
Corollary 4.14, `T-Const` case: typing a value does not change the environment,
so borrow safety of the result extension follows from the borrow-free shape of
the result type.
-/
theorem borrowSafety_value_result_extension_borrowFree {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty}
    {gamma : Name} :
    TermTyping env typing lifetime (.val value) ty env₂ →
    WellFormedEnv env lifetime →
    WellFormedTy env₂ ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env₂.fresh gamma →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro htyping hwellFormed hwellTy hborrowSafe hborrowFree hfresh
  have henv : env = env₂ := valueTyping_environment_eq htyping
  subst henv
  exact borrowSafety_result_extension_borrowFree hwellFormed hwellTy hborrowSafe
    hborrowFree hfresh

/-! ## Source-Level Initial States -/

def SourceValue : Value → Prop
  | .unit => True
  | .int _ => True
  | .ref _ => False

def SourceTerm (term : Term) : Prop :=
  ∀ value, value ∈ termValues term → SourceValue value

theorem sourceValue_no_owningLocations {value : Value} :
    SourceValue value →
    valueOwningLocations value = [] := by
  intro hsource
  cases value with
  | unit =>
      rfl
  | int _ =>
      rfl
  | ref ref =>
      cases hsource

theorem sourceValues_no_owningLocations {values : List Value} :
    (∀ value, value ∈ values → SourceValue value) →
    List.flatMap valueOwningLocations values = [] := by
  intro hsource
  induction values with
  | nil =>
      rfl
  | cons head tail ih =>
      have hhead : SourceValue head := hsource head (by simp)
      have htail : ∀ value, value ∈ tail → SourceValue value := by
        intro value hmem
        exact hsource value (by simp [hmem])
      calc
        List.flatMap valueOwningLocations (head :: tail)
            = valueOwningLocations head ++ List.flatMap valueOwningLocations tail := rfl
        _ = [] ++ [] := by
          rw [sourceValue_no_owningLocations hhead, ih htail]
        _ = [] := rfl

theorem sourceTerm_no_owningLocations {term : Term} :
    SourceTerm term →
    termOwningLocations term = [] := by
  intro hsource
  exact sourceValues_no_owningLocations hsource

theorem sourceTerm_validTerm {term : Term} :
    SourceTerm term →
    ValidTerm term := by
  intro hsource
  simp [ValidTerm, sourceTerm_no_owningLocations hsource]

theorem sourceValue_emptyStoreTyping {store : ProgramStore} {value : Value} :
    SourceValue value →
    ∃ ty, ValueTyping StoreTyping.empty value ty ∧ ValidValue store value ty := by
  intro hsource
  cases value with
  | unit =>
      exact ⟨.unit, ValueTyping.unit, ValidPartialValue.unit⟩
  | int value =>
      exact ⟨.int, ValueTyping.int, ValidPartialValue.int⟩
  | ref ref =>
      cases hsource

theorem sourceValue_validValue_of_empty_valueTyping {store : ProgramStore}
    {value : Value} {ty : Ty} :
    SourceValue value →
    ValueTyping StoreTyping.empty value ty →
    ValidValue store value ty := by
  intro hsource htyping
  rcases sourceValue_emptyStoreTyping (store := store) hsource with
    ⟨sourceTy, hsourceTyping, hvalidValue⟩
  have hty : sourceTy = ty :=
    valueTyping_deterministic hsourceTyping htyping
  subst hty
  exact hvalidValue

theorem sourceValue_empty_valueTyping_borrowFree {value : Value} {ty : Ty} :
    SourceValue value →
    ValueTyping StoreTyping.empty value ty →
    TyBorrowFree ty := by
  intro hsource htyping
  cases value with
  | unit =>
      cases htyping
      exact tyBorrowFree_unit
  | int _ =>
      cases htyping
      exact tyBorrowFree_int
  | ref _ =>
      cases hsource

theorem sourceTerm_empty_valueTyping_borrowFree {term : Term}
    {value : Value} {ty : Ty} :
    SourceTerm term →
    value ∈ termValues term →
    ValueTyping StoreTyping.empty value ty →
    TyBorrowFree ty := by
  intro hsource hmem htyping
  exact sourceValue_empty_valueTyping_borrowFree (hsource value hmem) htyping

theorem sourceInitial_value_borrowSafety_result_extension
    {value : Value} {ty : Ty} {env₂ : Env} {lifetime : Lifetime}
    {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh gamma →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource htyping hwellTy hfresh
  cases htyping with
  | const hvalueTyping =>
      exact borrowSafety_value_result_extension_borrowFree
        (TermTyping.const hvalueTyping)
        (wellFormedEnv_empty lifetime)
        hwellTy
        borrowSafeEnv_empty
        (sourceValue_empty_valueTyping_borrowFree hsource hvalueTyping)
        hfresh

theorem sourceTerm_validStoreTyping_empty {store : ProgramStore} {term : Term} :
    SourceTerm term →
    ValidStoreTyping store term StoreTyping.empty := by
  intro hsource value hmem
  exact sourceValue_emptyStoreTyping (hsource value hmem)

theorem sourceInitialState_valid {term : Term} :
    SourceTerm term →
    ValidState ProgramStore.empty term := by
  intro hsource
  exact ⟨validStore_empty, sourceTerm_validTerm hsource, by
    intro owned _hmem
    exact empty_owns_false owned⟩

theorem sourceInitialRuntimeState_valid {term : Term} :
    SourceTerm term →
    ValidRuntimeState ProgramStore.empty term := by
  intro hsource
  exact ⟨sourceInitialState_valid hsource, storeOwnersAllocated_empty⟩

/--
Source-level empty-store programs satisfy the initial hypotheses used by the
Section 4 soundness statements.
-/
theorem sourceInitialSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ∼ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    BorrowSafeEnv Env.empty ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    safeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    borrowSafeEnv_empty,
    operationalStoreProgress_empty⟩

/--
Source-level empty-store programs satisfy the mechanised runtime hypotheses,
including the explicit owner-allocation invariant.
-/
theorem sourceInitialRuntimeSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidRuntimeState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ∼ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    BorrowSafeEnv Env.empty ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialRuntimeState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    safeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    borrowSafeEnv_empty,
    operationalStoreProgress_empty⟩

/-- Well-typed source-level terms in the empty initial state satisfy Progress. -/
theorem sourceInitial_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  exact progress
    (sourceInitialState_valid hsource)
    (sourceTerm_validStoreTyping_empty hsource)
    wellFormedEnv_empty_all
    safeAbstraction_empty
    operationalStoreProgress_empty
    htyping

/-- Well-typed source-level terms satisfy Progress from the runtime hypothesis package. -/
theorem sourceInitial_runtime_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  rcases sourceInitialRuntimeSoundnessHypotheses
      (term := term) (lifetime := lifetime) hsource with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, _hwellFormed, _hborrowSafe, hstoreProgress⟩
  exact progress_runtime
    hvalidRuntime
    hvalidStoreTyping
    wellFormedEnv_empty_all
    hsafe
    hstoreProgress
    htyping

/-- Well-typed non-terminal source-level terms in the empty initial state can step. -/
theorem sourceInitial_progress_step {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step ProgramStore.empty lifetime term store' term' := by
  intro hsource htyping hnotTerminal
  exact (sourceInitial_progress hsource htyping).step_of_not_terminal hnotTerminal

/--
Well-typed non-terminal source-level terms can step from the runtime hypothesis
package used by the mechanised soundness statements.
-/
theorem sourceInitial_runtime_progress_step {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step ProgramStore.empty lifetime term store' term' := by
  intro hsource htyping hnotTerminal
  exact (sourceInitial_runtime_progress hsource htyping).step_of_not_terminal hnotTerminal

/--
Source-initial multistep preservation for a block containing a source-level
value.  This is the `R-BlockB` source-level instance of Lemma 4.11.
-/
theorem sourceInitial_blockB_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.block blockLifetime [.val value]) ty env₂ →
    MultiStep ProgramStore.empty lifetime
      (.block blockLifetime [.val value]) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.block blockLifetime [.val value]) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_blockB_value_multistep_runtime_no_slots
    (sourceInitialRuntimeState_valid hsourceTerm)
    safeAbstraction_empty
    htyping
    (empty_no_lifetime_slots blockLifetime)
    (sourceValue_validValue_of_empty_valueTyping hsource
      (blockValueTyping_valueTyping htyping))
    hmulti

/--
Source-initial multistep preservation for `box v` with a source-level value.
This is the `R-Box` source-level instance of Lemma 4.11.
-/
theorem sourceInitial_box_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue (.box ty) := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.box (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_box_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .box (.val value)) hsourceTerm)
    safeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti

/--
Source-initial multistep preservation for `let mut x = v` with a source-level
value.  This is the `R-Declare` source-level instance of Lemma 4.11.
-/
theorem sourceInitial_declare_value_multistep_preservation
    {x : Name} {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    MultiStep ProgramStore.empty lifetime
      (.letMut x (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.letMut x (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_declare_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .letMut x (.val value)) hsourceTerm)
    safeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti

/--
Source-level terminal preservation base case.

This is the source-initial instance of Lemma 4.11 when the program is already a
runtime value.  Since values cannot step, the multistep derivation is reflexive.
-/
theorem sourceInitial_multistep_value_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧
      finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.val value) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_multistep_runtime_value
    (sourceInitialRuntimeState_valid hsourceTerm)
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .val value) hsourceTerm)
    safeAbstraction_empty
    htyping
    hmulti

/-! ## Paper-Facing Section 4 Targets -/

/--
Main well-formedness induction behind Lemma 4.9.

This is the backwards target for Borrow Invariance: typing a term in a
well-formed environment produces a well-formed output environment and a
well-formed result type.
-/
theorem typingPreservesWellFormed {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  sorry

/--
Lemma 4.9, Borrow Invariance.

The paper phrases the conclusion as well-formedness of the output environment
extended with a fresh result binding `γ ↦ <T>^l`.
-/
theorem borrowInvariance {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
  rcases typingPreservesWellFormed hvalidState hvalidStoreTyping hwellFormed
      hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension hwellFormedOutput hwellFormedTy hfresh

/--
Lemma 4.11, Preservation.

This is stated over `ValidRuntimeState`, the mechanised package that contains
Definition 4.3's valid-state condition plus the explicit owner-allocation
invariant needed by our concrete store model.
-/
theorem preservation {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  sorry

/--
Theorem 4.12, Type and Borrow Safety.

The paper assumes termination; here that assumption is represented by an
explicit multistep witness to a final runtime value.
-/
theorem typeAndBorrowSafety {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    TerminatesAsValue store lifetime term →
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress
    htyping hterminates
  exact typeAndBorrowSafety_of_preservation hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hstoreProgress htyping
    (by
      intro finalStore finalValue hmulti
      exact preservation hvalidRuntime hvalidStoreTyping
        (hwellFormed lifetime) hsafe htyping hmulti)
    hterminates

/--
Main borrow-safety induction behind Corollary 4.14.

The result binding is included in the statement because the paper's corollary
checks borrow-safety after extending the output environment with `γ ↦ <T>^l`.
-/
theorem typingPreservesBorrowSafeResult {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  sorry

/--
Corollary 4.14, Borrow Safety.

Starting from a borrow-safe environment, the output environment extended with
the fresh result binding is both well-formed and borrow-safe.
-/
theorem borrowSafety {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hvalidState hvalidStoreTyping hwellFormed hborrowSafe hsafe htyping
    hfresh
  exact ⟨
    borrowInvariance hvalidState hvalidStoreTyping hwellFormed hsafe htyping
      hfresh,
    typingPreservesBorrowSafeResult hvalidState hvalidStoreTyping hwellFormed
      hborrowSafe hsafe htyping hfresh⟩

end Paper
end LwRust
