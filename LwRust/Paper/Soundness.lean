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
  | declare hfresh hinit _hfreshOut _hcoh henv₃ =>
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
  | declare hfresh hinit hfreshOut hcoh henv₃ =>
      have hfreshStore : store.fresh (VariableProjection x) :=
        safeAbstraction_store_fresh_var hsafe hfresh
      refine storePreservation_declare_step hsafe
        (TermTyping.declare hfresh hinit hfreshOut hcoh henv₃) hstep ?newValid ?preserveOld
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
Definition 4.8(i), the borrow invariant, stated faithfully **per target**.

The paper's Definition 4.8(i) reads: for all `x` and `w` with `Γ ⊢ x ↝ &[mut] w`
and `Γ(x) = ·ⁿ`, we have `Γ ⊢ w : T^m ∧ m ≼ n`.  The quantifier ranges over the
*individual* target lval `w`, and `Γ ⊢ w : T^m` types that single lval.  This is
strictly weaker than the joint target-list typing `Γ ⊢ ū : ⟨T⟩^m` used by the
well-formed-*type* judgement (Definition 3.21, `WellFormedTy`): the invariant
does **not** require all targets to share one joined pointee type.

This distinction matters at environment joins.  Joining `&[mut] L` with
`&[mut] R` produces `&[mut] (L ⊔ R)` whose target list merges `L` and `R`
(rule W-Bor merges only the target lists, never the pointee types).  The merged
list need not have a joint pointee typing — but each individual target keeps the
typing it had on whichever side it came from, so the per-target invariant is
preserved.  An earlier mechanisation used the joint typing here, which is exactly
why the join case could not be discharged. -/
def BorrowTargetsWellFormedInSlot
    (env : Env) (slotLifetime : Lifetime) (targets : List LVal) : Prop :=
  ∀ target, target ∈ targets →
    ∃ targetTy targetLifetime,
      LValTyping env target (.ty targetTy) targetLifetime ∧
        targetLifetime ≤ slotLifetime ∧
        LValBaseOutlives env target slotLifetime

/--
Slot-local borrow invariant for a partial type.  This is the proof obligation
that each Definition 3.23 update constructor has to re-establish for the slot
type it returns.
-/
def PartialTyBorrowsWellFormedInSlot
    (env : Env) (slotLifetime : Lifetime) (partialTy : PartialTy) : Prop :=
  ∀ {mutable targets},
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormedInSlot env slotLifetime targets

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

/--
Coherence of contained borrows: every borrow contained in a slot has a *joint*
target-list typing `Γ ⊢ ū : ⟨T⟩^m`, not merely per-target typings.

DELIBERATE DEVIATION FROM THE PAPER (documented):  Definition 4.8(i) of
`lw_rust.pdf`, taken literally, is the *per-target* statement (each target `w`
satisfies `Γ ⊢ w : T^m`), which `BorrowTargetsWellFormedInSlot` captures.  But
typing a *dereference* of a borrow — rule T-LvBor — requires the *joint* typing
of the whole target list (`LValTargetsTyping`, the Definition 3.21 well-formed
type premise).  So to type a reborrow target `*source` after a write/join, the
inner borrow's targets must be jointly typeable, i.e. coherent.  The paper's
borrow discipline maintains this (it is exactly Definition 3.21 carried as a
runtime invariant); the literal per-target Definition 4.8 omits it.  We therefore
carry `Coherent` as an explicit invariant.  It is non-vacuous (it is true of
every environment produced by the typing rules, since `T-LvBor` only forms a
borrow over a jointly-typeable target list) and is precisely what makes the
Appendix 9.6 borrow-invariance argument go through.

Stated over *lvals* (not merely slots): whenever an lval `lv` types to a borrow
`&ū`, the target list `ū` is jointly typeable.  This is strictly what typing a
reborrow `*lv` needs (rule T-LvBor), and it covers reborrow chains at depth — a
deref-of-borrow whose borrow type is *not* slot-contained (`PartialTyContains`
only descends through `box`, never through borrow target lists). -/
def Coherent (env : Env) : Prop :=
  ∀ lv mutable targets borrowLifetime,
    LValTyping env lv (.ty (.borrow mutable targets)) borrowLifetime →
    ∃ ty lifetime, LValTargetsTyping env targets (.ty ty) lifetime

theorem Linearizable.of_linearizedBy {φ : Name → Nat} {env : Env} :
    LinearizedBy φ env → Linearizable env := by
  intro hφ
  exact ⟨φ, hφ⟩

/-- Definition 4.8, well-formed environment.

DELIBERATE DEVIATION (documented, non-vacuous): augmented with the two runtime
invariants the borrow discipline maintains and that Appendix 9.6 needs —
`Coherent env` (every contained borrow's targets are jointly typeable, Def 3.21
carried at runtime, needed to type a reborrow) and `Linearizable env`
(`lw_rust_followup` Def 11, the well-foundedness rank making the borrow-target
recursion terminate).  These are exactly what `lvalTyping_strengthen_transport`
consumes; they hold of every environment the typing rules produce. -/
def WellFormedEnv (env : Env) (lifetime : Lifetime) : Prop :=
  ContainedBorrowsWellFormed env ∧ EnvSlotsOutlive env lifetime ∧
    Coherent env ∧ Linearizable env

@[simp] theorem containedBorrowsWellFormed_empty :
    ContainedBorrowsWellFormed Env.empty := by
  intro x slot mutable targets hslot _hcontains
  simp [Env.empty] at hslot

@[simp] theorem envSlotsOutlive_empty (lifetime : Lifetime) :
    EnvSlotsOutlive Env.empty lifetime := by
  intro x slot hslot
  simp [Env.empty] at hslot

theorem lvalTyping_empty_false {lv : LVal} {p : PartialTy} {lf : Lifetime}
    (h : LValTyping Env.empty lv p lf) : False := by
  induction lv generalizing p lf with
  | var x => cases h with | var hslot => simp [Env.empty] at hslot
  | deref lv' ih =>
      cases h with
      | box hb => exact ih hb
      | borrow hb _ => exact ih hb

theorem coherent_empty : Coherent Env.empty := by
  intro lv m T bLf hty
  exact (lvalTyping_empty_false hty).elim

theorem linearizable_empty : Linearizable Env.empty :=
  ⟨fun _ => 0, by intro x slot hslot; simp [Env.empty] at hslot⟩

@[simp] theorem wellFormedEnv_empty (lifetime : Lifetime) :
    WellFormedEnv Env.empty lifetime := by
  exact ⟨containedBorrowsWellFormed_empty, envSlotsOutlive_empty lifetime,
    coherent_empty, linearizable_empty⟩

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

/-- The target-list typing judgment is intentionally non-empty. -/
theorem LValTargetsTyping.nil_false {env : Env} {ty : PartialTy}
    {lifetime : Lifetime} :
    ¬ LValTargetsTyping env [] ty lifetime := by
  intro htyping
  cases htyping

theorem borrowTargetsWellFormedInSlot_update_fresh {env : Env} {x : Name}
    {slot : EnvSlot} {slotLifetime : Lifetime} {targets : List LVal} :
    env.fresh x →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    BorrowTargetsWellFormedInSlot (env.update x slot) slotLifetime targets := by
  intro hfresh htargets target hmem
  rcases htargets target hmem with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  refine ⟨targetTy, targetLifetime,
    LValTyping.update_fresh_one (slot := slot) hfresh htyping, houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  have hbaseSlot' :
      (env.update x slot).slotAt (LVal.base target) = some baseSlot := by
    have hbaseNe : LVal.base target ≠ x := by
      intro hbaseEq
      subst hbaseEq
      unfold Env.fresh at hfresh
      rw [hfresh] at hbaseSlot
      cases hbaseSlot
    simpa [Env.update, hbaseNe] using hbaseSlot
  exact ⟨baseSlot, hbaseSlot', hbaseOutlives⟩

theorem BorrowTargetsWellFormed.inSlot {env : Env} {targets : List LVal}
    {lifetime : Lifetime} :
    BorrowTargetsWellFormed env targets lifetime →
    BorrowTargetsWellFormedInSlot env lifetime targets := by
  intro htargets target hmem
  cases htargets with
  | intro hmembers => exact hmembers target hmem

theorem BorrowTargetsWellFormed.singleton {env : Env} {target : LVal}
    {targetTy : Ty} {targetLifetime lifetime : Lifetime} :
    LValTyping env target (.ty targetTy) targetLifetime →
    targetLifetime ≤ lifetime →
    LValBaseOutlives env target lifetime →
    BorrowTargetsWellFormed env [target] lifetime := by
  intro htarget houtlives hbase
  refine BorrowTargetsWellFormed.intro (by
    intro selected hselected
    simp at hselected
    subst hselected
    exact ⟨targetTy, targetLifetime, htarget, houtlives, hbase⟩)

theorem LifetimeOutlives.trans {first second third : Lifetime} :
    first ≤ second →
    second ≤ third →
    first ≤ third := by
  intro hfirst hsecond
  simp [LifetimeOutlives, Core.Lifetime.contains] at hfirst hsecond ⊢
  exact hfirst.trans hsecond

theorem LifetimeOutlives.antisymm {left right : Lifetime} :
    left ≤ right →
    right ≤ left →
    left = right := by
  intro hleftRight hrightLeft
  have hleftPrefix : left.path <+: right.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hleftRight
  have hrightPrefix : right.path <+: left.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hrightLeft
  have hpath : left.path = right.path :=
    hleftPrefix.eq_of_length (hleftPrefix.length_le.antisymm hrightPrefix.length_le)
  cases left
  cases right
  simp at hpath ⊢
  exact hpath

theorem LifetimeChild.outlives {parent child : Lifetime} :
    LifetimeChild parent child →
    parent ≤ child := by
  intro hchild
  rcases hchild with ⟨label, hpath⟩
  simp [LifetimeOutlives, Core.Lifetime.contains, hpath]

theorem LifetimeChild.ne {parent child : Lifetime} :
    LifetimeChild parent child →
    parent ≠ child := by
  intro hchild heq
  rcases hchild with ⟨label, hpath⟩
  have hlen := congrArg (fun lifetime : Lifetime => lifetime.path.length) heq
  simp [hpath] at hlen

theorem LifetimeChild.parent_of_outlives_child_ne {parent child slot : Lifetime} :
    LifetimeChild parent child →
    slot ≤ child →
    slot ≠ child →
    slot ≤ parent := by
  intro hchild hslot hne
  rcases hchild with ⟨label, hpath⟩
  have hslotPrefix : slot.path <+: child.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hslot
  have hparentPrefix : parent.path <+: child.path := by
    simp [hpath]
  have hslotLenLeChild : slot.path.length ≤ child.path.length :=
    hslotPrefix.length_le
  have hslotLenNeChild : slot.path.length ≠ child.path.length := by
    intro hlen
    have hpathEq : slot.path = child.path := hslotPrefix.eq_of_length hlen
    apply hne
    cases slot
    cases child
    simp at hpathEq ⊢
    exact hpathEq
  have hslotLenLtChild : slot.path.length < child.path.length :=
    Nat.lt_of_le_of_ne hslotLenLeChild hslotLenNeChild
  have hslotLenLeParent : slot.path.length ≤ parent.path.length := by
    rw [hpath, List.length_append] at hslotLenLtChild
    simp at hslotLenLtChild
    exact hslotLenLtChild
  have hslotParentPrefix : slot.path <+: parent.path :=
    List.prefix_of_prefix_length_le hslotPrefix hparentPrefix hslotLenLeParent
  simpa [LifetimeOutlives, Core.Lifetime.contains] using hslotParentPrefix

theorem LifetimeChild.not_child_outlives_parent {parent child : Lifetime} :
    LifetimeChild parent child →
    ¬ child ≤ parent := by
  intro hchild hle
  rcases hchild with ⟨label, hpath⟩
  have hprefix : child.path <+: parent.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hle
  have hlenLe : child.path.length ≤ parent.path.length :=
    hprefix.length_le
  rw [hpath, List.length_append] at hlenLe
  simp at hlenLe

theorem LValBaseOutlives.move_of_not_pathConflicts {env env' : Env}
    {moved target : LVal} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ target ⋈ moved →
    LValBaseOutlives env target lifetime →
    LValBaseOutlives env' target lifetime := by
  intro hmove hnotConflict hbase
  rcases hbase with ⟨baseSlot, hbaseSlot, houtlives⟩
  rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv'⟩
  have hbaseNe : LVal.base target ≠ LVal.base moved := by
    intro hbaseEq
    exact hnotConflict hbaseEq
  exact ⟨baseSlot, by
      simpa [henv', Env.update, hbaseNe] using hbaseSlot,
    houtlives⟩

theorem LValBaseOutlives.dropLifetime_child {env : Env}
    {parent child lifetime : Lifetime} {target : LVal} :
    LifetimeChild parent child →
    lifetime ≤ parent →
    LValBaseOutlives env target lifetime →
    LValBaseOutlives (env.dropLifetime child) target lifetime := by
  intro hchild hlifetimeParent hbase
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  exact ⟨baseSlot,
    Env.dropLifetime_slotAt_eq_some.mpr
      ⟨hbaseSlot, by
        intro hbaseLifetime
        subst hbaseLifetime
        exact LifetimeChild.not_child_outlives_parent hchild
          (LifetimeOutlives.trans hbaseOutlives hlifetimeParent)⟩,
    hbaseOutlives⟩

theorem EnvSlotsOutlive.weaken {env : Env} {outer inner : Lifetime} :
    EnvSlotsOutlive env outer →
    outer ≤ inner →
    EnvSlotsOutlive env inner := by
  intro houtlives houterInner x slot hslot
  exact LifetimeOutlives.trans (houtlives x slot hslot) houterInner

theorem WellFormedEnv.weaken {env : Env} {outer inner : Lifetime} :
    WellFormedEnv env outer →
    outer ≤ inner →
    WellFormedEnv env inner := by
  intro hwell houterInner
  exact ⟨hwell.1, EnvSlotsOutlive.weaken hwell.2.1 houterInner, hwell.2.2.1, hwell.2.2.2⟩

theorem BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed {env : Env}
    {targets : List LVal} {slotLifetime lifetime : Lifetime} :
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    slotLifetime ≤ lifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro htargets houtlives
  refine BorrowTargetsWellFormed.intro ?_
  intro target hmem
  rcases htargets target hmem with
    ⟨targetTy, targetLifetime, htargetTyping, htargetOutlivesSlot, hbase⟩
  refine ⟨targetTy, targetLifetime, htargetTyping,
    LifetimeOutlives.trans htargetOutlivesSlot houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  exact ⟨baseSlot, hbaseSlot, LifetimeOutlives.trans hbaseOutlives houtlives⟩

theorem EnvContains.borrowTargetsWellFormed {env : Env} {x : Name}
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    env ⊢ x ↝ Ty.borrow mutable targets →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
    (hwellFormed.1 x slot mutable targets hslot ⟨slot, hslot, hcontainsTy⟩)
    (hwellFormed.2.1 x slot hslot)

theorem BorrowTargetsWellFormed.member {env : Env} {targets : List LVal}
    {lifetime : Lifetime} :
    BorrowTargetsWellFormed env targets lifetime →
    ∀ target,
      target ∈ targets →
      ∃ targetTy targetLifetime,
        LValTyping env target (.ty targetTy) targetLifetime ∧
        targetLifetime ≤ lifetime ∧
        LValBaseOutlives env target lifetime := by
  intro htargets target hmem
  cases htargets with
  | intro hmembers => exact hmembers target hmem

theorem BorrowTargetsWellFormed.weaken {env : Env} {targets : List LVal}
    {outer inner : Lifetime} :
    BorrowTargetsWellFormed env targets outer →
      outer ≤ inner →
      BorrowTargetsWellFormed env targets inner := by
    intro htargets houterInner
    cases htargets with
    | intro hmembers =>
        refine BorrowTargetsWellFormed.intro ?_
        intro target htarget
        rcases hmembers target htarget with
          ⟨targetTy, targetLifetime, htyping, htOutlives, hbase⟩
        refine ⟨targetTy, targetLifetime, htyping,
          LifetimeOutlives.trans htOutlives houterInner, ?_⟩
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        exact ⟨baseSlot, hbaseSlot,
          LifetimeOutlives.trans hbaseOutlives houterInner⟩

theorem BorrowTargetsWellFormedInSlot.weaken {env : Env} {targets : List LVal}
    {outer inner : Lifetime} :
    BorrowTargetsWellFormedInSlot env outer targets →
    outer ≤ inner →
    BorrowTargetsWellFormedInSlot env inner targets := by
  intro htargets houtlives target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htargetTyping, htargetOutlives, hbase⟩
  refine ⟨targetTy, targetLifetime, htargetTyping,
    LifetimeOutlives.trans htargetOutlives houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  exact ⟨baseSlot, hbaseSlot, LifetimeOutlives.trans hbaseOutlives houtlives⟩

theorem PartialTyBorrowsWellFormedInSlot.weaken {env : Env}
    {partialTy : PartialTy} {outer inner : Lifetime} :
    PartialTyBorrowsWellFormedInSlot env outer partialTy →
    outer ≤ inner →
    PartialTyBorrowsWellFormedInSlot env inner partialTy := by
  intro hpartial houtlives mutable targets hcontains
  exact BorrowTargetsWellFormedInSlot.weaken (hpartial hcontains) houtlives

theorem WellFormedTy.weaken {env : Env} {ty : Ty} {outer inner : Lifetime} :
    WellFormedTy env ty outer →
    outer ≤ inner →
    WellFormedTy env ty inner := by
  intro hwell houtlives
  induction hwell with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | borrow htargets =>
      exact WellFormedTy.borrow (BorrowTargetsWellFormed.weaken htargets houtlives)
  | box _hinner ih =>
      exact WellFormedTy.box (ih houtlives)

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
  | tyBox hinner =>
      cases hwellTy with
      | box hwellInner =>
          exact borrowTargetsWellFormedInSlot_of_wellFormedTy_contains
            hwellInner hinner

theorem PartialTyBorrowsWellFormedInSlot.of_wellFormedTy {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedTy env ty lifetime →
    PartialTyBorrowsWellFormedInSlot env lifetime (.ty ty) := by
  intro hwellTy mutable targets hcontains
  exact borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwellTy hcontains

theorem PartialTyBorrowsWellFormedInSlot.box {env : Env}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    PartialTyBorrowsWellFormedInSlot env lifetime partialTy →
    PartialTyBorrowsWellFormedInSlot env lifetime (.box partialTy) := by
  intro hpartial mutable targets hcontains
  cases hcontains with
  | box hinner =>
      exact hpartial hinner

theorem PartialTyBorrowsWellFormedInSlot.box_inv {env : Env}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    PartialTyBorrowsWellFormedInSlot env lifetime (.box partialTy) →
    PartialTyBorrowsWellFormedInSlot env lifetime partialTy := by
  intro hpartial mutable targets hcontains
  exact hpartial (PartialTyContains.box hcontains)

/-- Every lval typing has a base variable slot. -/
theorem LValTyping.base_slot_exists {env : Env} :
    ∀ {lv : LVal} {p : PartialTy} {lf : Lifetime}, LValTyping env lv p lf →
      ∃ slot, env.slotAt (LVal.base lv) = some slot := by
  intro lv
  induction lv with
  | var x =>
      intro p lf h
      cases h with | var hslot => exact ⟨_, by simpa [LVal.base] using hslot⟩
  | deref lv' ih =>
      intro p lf h
      cases h with
      | box hb => simpa [LVal.base] using ih hb
      | borrow hb _ => simpa [LVal.base] using ih hb

/-- A variable in a (partial) type's `vars` comes from a contained borrow whose
target it is the base of.  (`Ty`/`PartialTy` are mutually inductive, so the proof
goes through the shared recursor.) -/
theorem partialTy_vars_mem_contains {pt : PartialTy} :
    ∀ v, v ∈ PartialTy.vars pt →
      ∃ mutable targets, PartialTyContains pt (.borrow mutable targets) ∧
        ∃ tgt, tgt ∈ targets ∧ LVal.base tgt = v :=
  PartialTy.rec
    (motive_1 := fun t => ∀ v, v ∈ Ty.vars t →
      ∃ mutable targets, PartialTyContains (.ty t) (.borrow mutable targets) ∧
        ∃ tgt, tgt ∈ targets ∧ LVal.base tgt = v)
    (motive_2 := fun pt => ∀ v, v ∈ PartialTy.vars pt →
      ∃ mutable targets, PartialTyContains pt (.borrow mutable targets) ∧
        ∃ tgt, tgt ∈ targets ∧ LVal.base tgt = v)
    (by intro v hv; simp [Ty.vars] at hv)
    (by intro v hv; simp [Ty.vars] at hv)
    (by
      intro m tgts v hv
      simp only [Ty.vars, List.mem_map] at hv
      obtain ⟨tgt, htgt, rfl⟩ := hv
      exact ⟨m, tgts, PartialTyContains.here, tgt, htgt, rfl⟩)
    (by
      intro inner ih v hv
      simp only [Ty.vars] at hv
      obtain ⟨m, tgts, hcontains, tgt, htgt, hbase⟩ := ih v hv
      exact ⟨m, tgts, PartialTyContains.tyBox hcontains, tgt, htgt, hbase⟩)
    (by intro t ih v hv; exact ih v (by simpa [PartialTy.vars] using hv))
    (by
      intro p ih v hv
      simp only [PartialTy.vars] at hv
      obtain ⟨m, tgts, hcontains, w⟩ := ih v hv
      exact ⟨m, tgts, PartialTyContains.box hcontains, w⟩)
    (by intro s _ih v hv;
        exact (List.not_mem_nil (show v ∈ ([] : List Name) from hv)).elim)
    pt

/-- Variables occurring in a well-formed type are bound in the environment (each
is the base of a borrow target, which types in `env`). -/
theorem wellFormedTy_vars_in_env {env : Env} {ty : Ty} {lifetime : Lifetime} :
    WellFormedTy env ty lifetime →
    ∀ v, v ∈ Ty.vars ty → ∃ slot, env.slotAt v = some slot := by
  intro hwf v hv
  obtain ⟨m, tgts, hcontains, tgt, htgt, hbase⟩ :=
    partialTy_vars_mem_contains (pt := .ty ty) v (by simpa [PartialTy.vars] using hv)
  obtain ⟨T, lt, hty, _, _⟩ :=
    borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwf hcontains tgt htgt
  rw [← hbase]
  exact LValTyping.base_slot_exists hty

/-- Variables in a slot's type of a contained-borrow-well-formed env are bound. -/
theorem containedBorrows_slot_vars_in_env {env : Env} {y : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    env.slotAt y = some slot →
    ∀ v, v ∈ PartialTy.vars slot.ty → ∃ s, env.slotAt v = some s := by
  intro hcontained hslot v hv
  obtain ⟨m, tgts, hcontains, tgt, htgt, hbase⟩ := partialTy_vars_mem_contains v hv
  have hwf := hcontained y slot m tgts hslot ⟨slot, hslot, hcontains⟩
  obtain ⟨T, lt, hty, _, _⟩ := hwf tgt htgt
  rw [← hbase]
  exact LValTyping.base_slot_exists hty

/-- Membership bound for the fresh-variable rank: every listed variable's
`φ + 1` is below the fold-max. -/
theorem mem_foldr_max_succ {l : List Name} {φ : Name → Nat} {v : Name}
    (hv : v ∈ l) :
    φ v + 1 ≤ l.foldr (fun w acc => max (φ w + 1) acc) 0 := by
  induction hv with
  | head as => exact le_max_left _ _
  | tail b _hmem ih => exact le_trans ih (le_max_right _ _)

/-- Explicit declaration-coherence obligation.

`WellFormedTy` carries the paper's per-target borrow invariant.  The mechanised
`Coherent` invariant is stronger: it asks for joint target-list typing for every
borrow that can be reached by lvalue typing.  A fresh declaration of a full type
therefore needs this extra closure fact; it is named here rather than hidden as a
local proof hole inside `WellFormedEnv.update_fresh_ty`.

This is not merely syntactic coherence of borrows contained in `ty`: after
declaring `x : &targets`, lvals such as `*x` can expose the joint target-list
union, and if that union is itself a borrow then `Coherent` needs coherence for
that exposed borrow as well.  The eventual proof should thread a lvalue-level
"declared type is coherent under the current environment" invariant through
term typing, not derive it from `WellFormedTy` alone.

As stated, this obligation is stronger than `WellFormedTy`: for example,
`WellFormedTy.borrow` accepts `&[]` vacuously, while
`LValTargetsTyping.nil_false` shows that no empty target list is jointly
typeable.  The valid replacement requires the lvalue-level
`FreshUpdateCoherenceObligations` side condition below. -/
theorem Coherent.update_fresh_ty {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    Coherent env →
    env.fresh x →
    FreshUpdateCoherenceObligations env x ty lifetime →
    Coherent (env.update x { ty := .ty ty, lifetime := lifetime })
    := by
  intro hcoh hfresh hobligations lv mutable targets borrowLifetime htyping
  by_cases hbase : LVal.base lv = x
  · exact hobligations.fresh_root_coherent hbase htyping
  · rcases hobligations.old_root_transport hbase htyping with
      ⟨oldBorrowLifetime, htypingOld⟩
    rcases hcoh lv mutable targets oldBorrowLifetime htypingOld with
      ⟨targetTy, targetLifetime, htargetsOld⟩
    exact ⟨targetTy, targetLifetime,
      LValTargetsTyping.update_fresh
        (slot := { ty := .ty ty, lifetime := lifetime }) hfresh htargetsOld⟩

/-- Bare `Coherent.update_fresh_ty` is false: `WellFormedTy` accepts `&[]`
vacuously, but coherence requires the target list to be jointly typeable, and
`LValTargetsTyping` is intentionally non-empty. -/
theorem Coherent.update_fresh_ty_bare_counterexample :
    ∃ env x ty lifetime,
      Coherent env ∧ WellFormedTy env ty lifetime ∧ env.fresh x ∧
        ¬ Coherent (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  refine ⟨Env.empty, "x", .borrow false [], Lifetime.root, ?_, ?_, ?_, ?_⟩
  · exact (wellFormedEnv_empty Lifetime.root).2.2.1
  · exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
      intro target htarget
      simp at htarget))
  · simp [Env.fresh, Env.empty]
  · intro hcoh
    have hx :
        (Env.empty.update "x"
          { ty := .ty (.borrow false []), lifetime := Lifetime.root }).slotAt "x" =
          some { ty := .ty (.borrow false []), lifetime := Lifetime.root } := by
      simp [Env.update]
    have htyping :
        LValTyping
          (Env.empty.update "x"
            { ty := .ty (.borrow false []), lifetime := Lifetime.root })
          (.var "x") (.ty (.borrow false [])) Lifetime.root :=
      LValTyping.var hx
    rcases hcoh (.var "x") false [] Lifetime.root htyping with
      ⟨targetTy, targetLifetime, htargets⟩
    exact LValTargetsTyping.nil_false htargets

theorem Coherent.update_fresh_ty_of_obligations {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    Coherent env →
    env.fresh x →
    FreshUpdateCoherenceObligations env x ty lifetime →
    Coherent (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  exact Coherent.update_fresh_ty

theorem WellFormedEnv.update_fresh_ty {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    env.fresh x →
    FreshUpdateCoherenceObligations env x ty lifetime →
    WellFormedEnv (env.update x { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro hwellEnv hwellTy hfresh hcohObligations
  refine ⟨?_, ?_, ?_, ?_⟩
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
      exact hwellEnv.2.1 y envSlot hslotOld
  · exact Coherent.update_fresh_ty hwellEnv.2.2.1 hfresh hcohObligations
  · -- Linearizable: rank the fresh variable strictly above the variables of its
    -- slot type (a finite list); existing ranks unchanged.
    obtain ⟨φ, hφ⟩ := hwellEnv.2.2.2
    have hfreshEq : env.slotAt x = none := hfresh
    have hxnotin : x ∉ Ty.vars ty := by
      intro hx
      obtain ⟨s, hs⟩ := wellFormedTy_vars_in_env hwellTy x hx
      rw [hfreshEq] at hs
      exact absurd hs (by simp)
    refine ⟨fun n => if n = x then
      (Ty.vars ty).foldr (fun w acc => max (φ w + 1) acc) 0 else φ n, ?_⟩
    intro y slot hslot v hv
    by_cases hy : y = x
    · have hslotEq : slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        rw [hy] at hslot
        simpa [Env.update] using hslot.symm
      have hvty : v ∈ Ty.vars ty := by
        rw [hslotEq] at hv; simpa [PartialTy.vars] using hv
      have hvx : v ≠ x := fun h => hxnotin (h ▸ hvty)
      simp only [if_neg hvx, if_pos hy]
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (mem_foldr_max_succ hvty)
    · have hslotOld : env.slotAt y = some slot := by
        simpa [Env.update, hy] using hslot
      obtain ⟨s, hs⟩ := containedBorrows_slot_vars_in_env hwellEnv.1 hslotOld v hv
      have hvx : v ≠ x := by
        intro h; rw [h, hfreshEq] at hs; exact absurd hs (by simp)
      simp only [if_neg hy, if_neg hvx]
      exact hφ y slot hslotOld v hv

/--
Fresh full-type update preserving well-formedness with the declaration
coherence gap made explicit.

This is the proved replacement for uses that should not depend on the false
bare `Coherent.update_fresh_ty` obligation.
-/
theorem WellFormedEnv.update_fresh_ty_of_coherenceObligations {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    env.fresh x →
    FreshUpdateCoherenceObligations env x ty lifetime →
    WellFormedEnv (env.update x { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro hwellEnv hwellTy hfresh hcohObligations
  refine ⟨?_, ?_, ?_, ?_⟩
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
      exact hwellEnv.2.1 y envSlot hslotOld
  · exact Coherent.update_fresh_ty_of_obligations
      hwellEnv.2.2.1 hfresh hcohObligations
  · obtain ⟨φ, hφ⟩ := hwellEnv.2.2.2
    have hfreshEq : env.slotAt x = none := hfresh
    have hxnotin : x ∉ Ty.vars ty := by
      intro hx
      obtain ⟨s, hs⟩ := wellFormedTy_vars_in_env hwellTy x hx
      rw [hfreshEq] at hs
      exact absurd hs (by simp)
    refine ⟨fun n => if n = x then
      (Ty.vars ty).foldr (fun w acc => max (φ w + 1) acc) 0 else φ n, ?_⟩
    intro y slot hslot v hv
    by_cases hy : y = x
    · have hslotEq : slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        rw [hy] at hslot
        simpa [Env.update] using hslot.symm
      have hvty : v ∈ Ty.vars ty := by
        rw [hslotEq] at hv; simpa [PartialTy.vars] using hv
      have hvx : v ≠ x := fun h => hxnotin (h ▸ hvty)
      simp only [if_neg hvx, if_pos hy]
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (mem_foldr_max_succ hvty)
    · have hslotOld : env.slotAt y = some slot := by
        simpa [Env.update, hy] using hslot
      obtain ⟨s, hs⟩ := containedBorrows_slot_vars_in_env hwellEnv.1 hslotOld v hv
      have hvx : v ≠ x := by
        intro h; rw [h, hfreshEq] at hs; exact absurd hs (by simp)
      simp only [if_neg hy, if_neg hvx]
      exact hφ y slot hslotOld v hv

/-- Updating a variable slot without changing its allocation lifetime preserves Definition 4.8(ii). -/
theorem EnvSlotsOutlive.update_same_lifetime {env : Env} {x : Name}
    {slot : EnvSlot} {newTy : PartialTy} {current : Lifetime} :
    EnvSlotsOutlive env current →
    env.slotAt x = some slot →
    EnvSlotsOutlive (env.update x { slot with ty := newTy }) current := by
  intro houtlives hslot y updatedSlot hupdated
  by_cases hy : y = x
  · subst hy
    have hupdatedSlot :
        updatedSlot = { slot with ty := newTy } := by
      have h :
          { slot with ty := newTy } = updatedSlot := by
        simpa [Env.update] using hupdated
      exact h.symm
    subst hupdatedSlot
    exact houtlives _ slot hslot
  · have hold : env.slotAt y = some updatedSlot := by
      simpa [Env.update, hy] using hupdated
    exact houtlives y updatedSlot hold

/--
An environment update relation preserves the allocation lifetime of every slot
that remains in the result.  This isolates the domain/lifetime part of
Appendix Lemma 9.6 from the borrow-target obligations.
-/
def EnvLifetimesPreserved (source result : Env) : Prop :=
  ∀ x resultSlot,
    result.slotAt x = some resultSlot →
    ∃ sourceSlot,
      source.slotAt x = some sourceSlot ∧
      sourceSlot.lifetime = resultSlot.lifetime

@[refl] theorem EnvLifetimesPreserved.refl (env : Env) :
    EnvLifetimesPreserved env env := by
  intro x slot hslot
  exact ⟨slot, hslot, rfl⟩

theorem EnvLifetimesPreserved.trans {first second third : Env} :
    EnvLifetimesPreserved first second →
    EnvLifetimesPreserved second third →
    EnvLifetimesPreserved first third := by
  intro hfirstSecond hsecondThird x slot hslot
  rcases hsecondThird x slot hslot with ⟨secondSlot, hsecondSlot, hlifetime₂⟩
  rcases hfirstSecond x secondSlot hsecondSlot with
    ⟨firstSlot, hfirstSlot, hlifetime₁⟩
  exact ⟨firstSlot, hfirstSlot, by rw [hlifetime₁, hlifetime₂]⟩

theorem EnvStrengthens.lifetimesPreserved {source result : Env} :
    EnvStrengthens source result →
    EnvLifetimesPreserved source result := by
  intro hstrength x resultSlot hresultSlot
  have hx := hstrength x
  cases hsource : source.slotAt x with
  | none =>
      simp [hsource, hresultSlot] at hx
  | some sourceSlot =>
      simp [hsource, hresultSlot] at hx
      exact ⟨sourceSlot, by simp, hx.1⟩

theorem EnvJoin.lifetimesPreserved_left {left right join : Env} :
    EnvJoin left right join →
    EnvLifetimesPreserved left join := by
  intro hjoin
  exact EnvStrengthens.lifetimesPreserved
    (hjoin.1 (by simp))

theorem EnvJoin.lifetimesPreserved_right {left right join : Env} :
    EnvJoin left right join →
    EnvLifetimesPreserved right join := by
  intro hjoin
  exact EnvStrengthens.lifetimesPreserved
    (hjoin.1 (by simp))

theorem EnvLifetimesPreserved.update_from_source_slot {source middle : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvLifetimesPreserved source middle →
    source.slotAt x = some slot →
    EnvLifetimesPreserved source
      (middle.update x { slot with ty := newTy }) := by
  intro hpreserved hslot y resultSlot hresultSlot
  by_cases hy : y = x
  · subst hy
    have hresultSlotEq : resultSlot = { slot with ty := newTy } := by
      have h :
          { slot with ty := newTy } = resultSlot := by
        simpa [Env.update] using hresultSlot
      exact h.symm
    subst hresultSlotEq
    exact ⟨slot, hslot, rfl⟩
  · have hmiddleSlot : middle.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresultSlot
    exact hpreserved y resultSlot hmiddleSlot

theorem EnvSlotsOutlive.of_lifetimesPreserved {source result : Env}
    {current : Lifetime} :
    EnvSlotsOutlive source current →
    EnvLifetimesPreserved source result →
    EnvSlotsOutlive result current := by
  intro houtlives hpreserved x slot hslot
  rcases hpreserved x slot hslot with
    ⟨sourceSlot, hsourceSlot, hlifetime⟩
  rw [← hlifetime]
  exact houtlives x sourceSlot hsourceSlot

theorem UpdateWrite.lifetimesPreserved :
    (∀ {rank env₁ path oldTy ty env₂ updatedTy},
      UpdateAtPath rank env₁ path oldTy ty env₂ updatedTy →
      EnvLifetimesPreserved env₁ env₂) ∧
    (∀ {rank env path targets ty result},
      WriteBorrowTargets rank env path targets ty result →
      EnvLifetimesPreserved env result) ∧
    (∀ {rank env lv ty result},
      EnvWrite rank env lv ty result →
      EnvLifetimesPreserved env result) := by
  constructor
  · intro rank env₁ path oldTy ty env₂ updatedTy hupdate
    exact UpdateAtPath.rec
      (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
        EnvLifetimesPreserved env₁ env₂)
      (motive_2 := fun _rank env _path _targets _ty result _ =>
        EnvLifetimesPreserved env result)
      (motive_3 := fun _rank env _lv _ty result _ =>
        EnvLifetimesPreserved env result)
      (by
        intro env old ty
        exact EnvLifetimesPreserved.refl env)
      (by
        intro env rank old joined ty _hshape _hjoinTy
        exact EnvLifetimesPreserved.refl env)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
        exact ih)
      (by
        intro env₁ env₂ rank path targets ty _hwrites ih
        exact ih)
      (by
        intro rank env path ty
        exact EnvLifetimesPreserved.refl env)
      (by
        intro rank env updated path target ty _hwrite _htyped ih
        exact ih)
      (by
        intro rank env updated restEnv result path target rest ty
          _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
        exact EnvLifetimesPreserved.trans ihWrite
          (EnvJoin.lifetimesPreserved_left hjoin))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
        exact EnvLifetimesPreserved.update_from_source_slot ih hslot)
      hupdate
  · constructor
    · intro rank env path targets ty result hwrites
      exact WriteBorrowTargets.rec
        (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
          EnvLifetimesPreserved env₁ env₂)
        (motive_2 := fun _rank env _path _targets _ty result _ =>
          EnvLifetimesPreserved env result)
        (motive_3 := fun _rank env _lv _ty result _ =>
          EnvLifetimesPreserved env result)
        (by
          intro env old ty
          exact EnvLifetimesPreserved.refl env)
        (by
          intro env rank old joined ty _hshape _hjoinTy
          exact EnvLifetimesPreserved.refl env)
        (by
          intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
          exact ih)
        (by
          intro env₁ env₂ rank path targets ty _hwrites ih
          exact ih)
        (by
          intro rank env path ty
          exact EnvLifetimesPreserved.refl env)
        (by
          intro rank env updated path target ty _hwrite _htyped ih
          exact ih)
        (by
          intro rank env updated restEnv result path target rest ty
            _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
          exact EnvLifetimesPreserved.trans ihWrite
            (EnvJoin.lifetimesPreserved_left hjoin))
        (by
          intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
          exact EnvLifetimesPreserved.update_from_source_slot ih hslot)
        hwrites
    · intro rank env lv ty result hwrite
      exact EnvWrite.rec
        (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
          EnvLifetimesPreserved env₁ env₂)
        (motive_2 := fun _rank env _path _targets _ty result _ =>
          EnvLifetimesPreserved env result)
        (motive_3 := fun _rank env _lv _ty result _ =>
          EnvLifetimesPreserved env result)
        (by
          intro env old ty
          exact EnvLifetimesPreserved.refl env)
        (by
          intro env rank old joined ty _hshape _hjoinTy
          exact EnvLifetimesPreserved.refl env)
        (by
          intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
          exact ih)
        (by
          intro env₁ env₂ rank path targets ty _hwrites ih
          exact ih)
        (by
          intro rank env path ty
          exact EnvLifetimesPreserved.refl env)
        (by
          intro rank env updated path target ty _hwrite _htyped ih
          exact ih)
        (by
          intro rank env updated restEnv result path target rest ty
            _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
          exact EnvLifetimesPreserved.trans ihWrite
            (EnvJoin.lifetimesPreserved_left hjoin))
        (by
          intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
          exact EnvLifetimesPreserved.update_from_source_slot ih hslot)
        hwrite

theorem EnvWrite.lifetimesPreserved {rank : Nat} {env : Env} {lv : LVal}
    {ty : Ty} {result : Env} :
    EnvWrite rank env lv ty result →
    EnvLifetimesPreserved env result :=
  UpdateWrite.lifetimesPreserved.2.2

theorem UpdateAtPath.cons_inv {rank : Nat} {env₁ env₂ : Env}
    {path : List Unit} {oldTy : PartialTy} {ty : Ty}
    {updatedTy : PartialTy} :
    UpdateAtPath rank env₁ (() :: path) oldTy ty env₂ updatedTy →
    (∃ inner updatedInner,
      oldTy = .box inner ∧
      updatedTy = .box updatedInner ∧
      UpdateAtPath rank env₁ path inner ty env₂ updatedInner) ∨
    (∃ targets,
      oldTy = .ty (.borrow true targets) ∧
      updatedTy = .ty (.borrow true targets) ∧
      WriteBorrowTargets (rank + 1) env₁ path targets ty env₂) := by
  intro hupdate
  cases hupdate with
  | box hinner =>
      exact Or.inl ⟨_, _, rfl, rfl, hinner⟩
  | mutBorrow hwrites =>
      exact Or.inr ⟨_, rfl, rfl, hwrites⟩

@[simp] theorem List.Unit_append_singleton (path : List Unit) :
    path ++ [()] = () :: path := by
  induction path with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head
      simp [ih]

@[simp] theorem LVal.path_deref_cons (lv : LVal) :
    LVal.path (.deref lv) = () :: LVal.path lv := by
  simp [LVal.path]

theorem EnvWrite.preserves_slotsOutlive {rank : Nat} {env result : Env}
    {lv : LVal} {ty : Ty} {current : Lifetime} :
    EnvSlotsOutlive env current →
    EnvWrite rank env lv ty result →
    EnvSlotsOutlive result current := by
  intro houtlives hwrite
  exact EnvSlotsOutlive.of_lifetimesPreserved houtlives
    (EnvWrite.lifetimesPreserved hwrite)

def EnvLifetimesSurvive (source result : Env) : Prop :=
  ∀ x sourceSlot,
    source.slotAt x = some sourceSlot →
    ∃ resultSlot,
      result.slotAt x = some resultSlot ∧
      sourceSlot.lifetime = resultSlot.lifetime

@[refl] theorem EnvLifetimesSurvive.refl (env : Env) :
    EnvLifetimesSurvive env env := by
  intro x slot hslot
  exact ⟨slot, hslot, rfl⟩

theorem EnvLifetimesSurvive.trans {first second third : Env} :
    EnvLifetimesSurvive first second →
    EnvLifetimesSurvive second third →
    EnvLifetimesSurvive first third := by
  intro hfirstSecond hsecondThird x slot hslot
  rcases hfirstSecond x slot hslot with ⟨secondSlot, hsecondSlot, hlifetime₁⟩
  rcases hsecondThird x secondSlot hsecondSlot with
    ⟨thirdSlot, hthirdSlot, hlifetime₂⟩
  exact ⟨thirdSlot, hthirdSlot, by rw [hlifetime₁, hlifetime₂]⟩

theorem EnvStrengthens.lifetimesSurvive {source result : Env} :
    EnvStrengthens source result →
    EnvLifetimesSurvive source result := by
  intro hstrength x sourceSlot hsourceSlot
  have hx := hstrength x
  cases hresult : result.slotAt x with
  | none =>
      simp [hsourceSlot, hresult] at hx
  | some resultSlot =>
      simp [hsourceSlot, hresult] at hx
      exact ⟨resultSlot, by simp, hx.1⟩

theorem EnvJoin.lifetimesSurvive_left {left right join : Env} :
    EnvJoin left right join →
    EnvLifetimesSurvive left join := by
  intro hjoin
  exact EnvStrengthens.lifetimesSurvive
    (hjoin.1 (by simp))

theorem EnvJoin.lifetimesSurvive_right {left right join : Env} :
    EnvJoin left right join →
    EnvLifetimesSurvive right join := by
  intro hjoin
  exact EnvStrengthens.lifetimesSurvive
    (hjoin.1 (by simp))

theorem EnvLifetimesSurvive.update_from_source_slot {source middle : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvLifetimesSurvive source middle →
    source.slotAt x = some slot →
    EnvLifetimesSurvive source
      (middle.update x { slot with ty := newTy }) := by
  intro hsurvive hslot y sourceSlot hsourceSlot
  by_cases hy : y = x
  · subst hy
    have hsourceSlotEq : sourceSlot = slot := by
      have hsomeEq : some sourceSlot = some slot := by
        rw [← hsourceSlot, hslot]
      exact Option.some.inj hsomeEq
    exact ⟨{ slot with ty := newTy }, by simp [Env.update], by
      rw [hsourceSlotEq]⟩
  · rcases hsurvive y sourceSlot hsourceSlot with
      ⟨middleSlot, hmiddleSlot, hlifetime⟩
    exact ⟨middleSlot, by simpa [Env.update, hy] using hmiddleSlot, hlifetime⟩

theorem UpdateWrite.lifetimesSurvive :
    (∀ {rank env₁ path oldTy ty env₂ updatedTy},
      UpdateAtPath rank env₁ path oldTy ty env₂ updatedTy →
      EnvLifetimesSurvive env₁ env₂) ∧
    (∀ {rank env path targets ty result},
      WriteBorrowTargets rank env path targets ty result →
      EnvLifetimesSurvive env result) ∧
    (∀ {rank env lv ty result},
      EnvWrite rank env lv ty result →
      EnvLifetimesSurvive env result) := by
  constructor
  · intro rank env₁ path oldTy ty env₂ updatedTy hupdate
    exact UpdateAtPath.rec
      (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
        EnvLifetimesSurvive env₁ env₂)
      (motive_2 := fun _rank env _path _targets _ty result _ =>
        EnvLifetimesSurvive env result)
      (motive_3 := fun _rank env _lv _ty result _ =>
        EnvLifetimesSurvive env result)
      (by
        intro env old ty
        exact EnvLifetimesSurvive.refl env)
      (by
        intro env rank old joined ty _hshape _hjoinTy
        exact EnvLifetimesSurvive.refl env)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
        exact ih)
      (by
        intro env₁ env₂ rank path targets ty _hwrites ih
        exact ih)
      (by
        intro rank env path ty
        exact EnvLifetimesSurvive.refl env)
      (by
        intro rank env updated path target ty _hwrite _htyped ih
        exact ih)
      (by
        intro rank env updated restEnv result path target rest ty
          _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
        exact EnvLifetimesSurvive.trans ihWrite
          (EnvJoin.lifetimesSurvive_left hjoin))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
        exact EnvLifetimesSurvive.update_from_source_slot ih hslot)
      hupdate
  · constructor
    · intro rank env path targets ty result hwrites
      exact WriteBorrowTargets.rec
        (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
          EnvLifetimesSurvive env₁ env₂)
        (motive_2 := fun _rank env _path _targets _ty result _ =>
          EnvLifetimesSurvive env result)
        (motive_3 := fun _rank env _lv _ty result _ =>
          EnvLifetimesSurvive env result)
        (by
          intro env old ty
          exact EnvLifetimesSurvive.refl env)
        (by
          intro env rank old joined ty _hshape _hjoinTy
          exact EnvLifetimesSurvive.refl env)
        (by
          intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
          exact ih)
        (by
          intro env₁ env₂ rank path targets ty _hwrites ih
          exact ih)
        (by
          intro rank env path ty
          exact EnvLifetimesSurvive.refl env)
        (by
          intro rank env updated path target ty _hwrite _htyped ih
          exact ih)
        (by
          intro rank env updated restEnv result path target rest ty
            _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
          exact EnvLifetimesSurvive.trans ihWrite
            (EnvJoin.lifetimesSurvive_left hjoin))
        (by
          intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
          exact EnvLifetimesSurvive.update_from_source_slot ih hslot)
        hwrites
    · intro rank env lv ty result hwrite
      exact EnvWrite.rec
        (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
          EnvLifetimesSurvive env₁ env₂)
        (motive_2 := fun _rank env _path _targets _ty result _ =>
          EnvLifetimesSurvive env result)
        (motive_3 := fun _rank env _lv _ty result _ =>
          EnvLifetimesSurvive env result)
        (by
          intro env old ty
          exact EnvLifetimesSurvive.refl env)
        (by
          intro env rank old joined ty _hshape _hjoinTy
          exact EnvLifetimesSurvive.refl env)
        (by
          intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
          exact ih)
        (by
          intro env₁ env₂ rank path targets ty _hwrites ih
          exact ih)
        (by
          intro rank env path ty
          exact EnvLifetimesSurvive.refl env)
        (by
          intro rank env updated path target ty _hwrite _htyped ih
          exact ih)
        (by
          intro rank env updated restEnv result path target rest ty
            _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
          exact EnvLifetimesSurvive.trans ihWrite
            (EnvJoin.lifetimesSurvive_left hjoin))
        (by
          intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
          exact EnvLifetimesSurvive.update_from_source_slot ih hslot)
        hwrite

theorem EnvWrite.lifetimesSurvive {rank : Nat} {env : Env} {lv : LVal}
    {ty : Ty} {result : Env} :
    EnvWrite rank env lv ty result →
    EnvLifetimesSurvive env result :=
  UpdateWrite.lifetimesSurvive.2.2

theorem EnvMove.lifetimesSurvive {env moved : Env} {lv : LVal} :
    EnvMove env lv moved →
    EnvLifetimesSurvive env moved := by
  intro hmove x sourceSlot hsourceSlot
  rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, hmoved⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hsourceSlotEq : sourceSlot = moveSlot := by
      have hsomeEq : some sourceSlot = some moveSlot := by
        rw [← hsourceSlot, hmoveSlot]
      exact Option.some.inj hsomeEq
    exact ⟨{ moveSlot with ty := struck }, by simp [hmoved, Env.update], by
      rw [hsourceSlotEq]⟩
  · exact ⟨sourceSlot, by simpa [hmoved, Env.update, hx] using hsourceSlot, rfl⟩

theorem LValBaseOutlives.write {rank : Nat} {env result : Env}
    {written lv : LVal} {ty : Ty} {current : Lifetime} :
    EnvWrite rank env written ty result →
    LValBaseOutlives env lv current →
    LValBaseOutlives result lv current := by
  intro hwrite hbase
  rcases hbase with ⟨slot, hslot, houtlives⟩
  rcases EnvWrite.lifetimesSurvive hwrite (LVal.base lv) slot hslot with
    ⟨resultSlot, hresultSlot, hlifetime⟩
  exact ⟨resultSlot, hresultSlot, by rw [← hlifetime]; exact houtlives⟩

theorem TermTyping.slot_lifetime_survives :
    (∀ {env₁ typing lifetime term ty env₂},
      TermTyping env₁ typing lifetime term ty env₂ →
      ∀ {x sourceSlot},
        sourceSlot.lifetime ≤ lifetime →
        env₁.slotAt x = some sourceSlot →
        ∃ resultSlot,
          env₂.slotAt x = some resultSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime) ∧
    (∀ {env₁ typing lifetime terms ty env₂},
      TermListTyping env₁ typing lifetime terms ty env₂ →
      ∀ {x sourceSlot},
        sourceSlot.lifetime ≤ lifetime →
        env₁.slotAt x = some sourceSlot →
        ∃ resultSlot,
          env₂.slotAt x = some resultSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime) := by
  constructor
  · intro env₁ typing lifetime term ty env₂ htyping
    exact TermTyping.rec
      (motive_1 := fun env₁ _typing lifetime _term _ty env₂ _ =>
        ∀ {x sourceSlot},
          sourceSlot.lifetime ≤ lifetime →
          env₁.slotAt x = some sourceSlot →
          ∃ resultSlot,
            env₂.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
      (motive_2 := fun env₁ _typing lifetime _terms _ty env₂ _ =>
        ∀ {x sourceSlot},
          sourceSlot.lifetime ≤ lifetime →
          env₁.slotAt x = some sourceSlot →
          ∃ resultSlot,
            env₂.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
      (by
        intro _env _typing _lifetime _value _ty _hvalue x sourceSlot
          _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hcopy _hnotRead
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty
          _hLv _hnotWrite hmove x sourceSlot _houtlives hslot
        exact EnvMove.lifetimesSurvive hmove x sourceSlot hslot)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hmutable _hnotWrite
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hnotRead
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih
          x sourceSlot houtlives hslot
        exact ih houtlives hslot)
      (by
        intro _env₁ _env₂ _env₃ _typing lifetime blockLifetime _terms _ty
          hchild _hterms _hwellTy hdrop ih x sourceSlot houtlives hslot
        rcases ih (LifetimeOutlives.trans houtlives (LifetimeChild.outlives hchild))
            hslot with
          ⟨bodySlot, hbodySlot, hbodyLifetime⟩
        subst hdrop
        have hbodyNotDropped : bodySlot.lifetime ≠ blockLifetime := by
          intro hdropped
          have hchildOutlivesParent : blockLifetime ≤ lifetime := by
            rw [← hdropped, ← hbodyLifetime]
            exact houtlives
          exact LifetimeChild.not_child_outlives_parent hchild hchildOutlivesParent
        exact ⟨bodySlot,
          Env.dropLifetime_slotAt_eq_some.mpr ⟨hbodySlot, hbodyNotDropped⟩,
          hbodyLifetime⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing lifetime y _term _ty
          hfresh _hterm _hfreshOut _hcoh henv₃ ih x sourceSlot houtlives hslot
        subst henv₃
        by_cases hxy : x = y
        · subst hxy
          rw [hfresh] at hslot
          cases hslot
        · rcases ih houtlives hslot with ⟨innerSlot, hinnerSlot, hlifetime⟩
          exact ⟨innerSlot, by simpa [Env.update, hxy] using hinnerSlot, hlifetime⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy
          _hLhs _hRhs _hshape _hwellRhs hwrite _hranked _hcoh _hnotWrite ih x sourceSlot
          houtlives hslot
        rcases ih houtlives hslot with ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
        rcases EnvWrite.lifetimesSurvive hwrite x rhsSlot hrhsSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hrhsLifetime, hresultLifetime]⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih
          x sourceSlot houtlives hslot
        exact ih houtlives hslot)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
          _hterm _hrest ihHead ihRest x sourceSlot houtlives hslot
        rcases ihHead houtlives hslot with ⟨midSlot, hmidSlot, hmidLifetime⟩
        have hmidOutlives : midSlot.lifetime ≤ _lifetime := by
          rw [← hmidLifetime]
          exact houtlives
        rcases ihRest hmidOutlives hmidSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hmidLifetime, hresultLifetime]⟩)
      htyping

  · intro env₁ typing lifetime terms ty env₂ htyping
    exact TermListTyping.rec
      (motive_1 := fun env₁ _typing lifetime _term _ty env₂ _ =>
        ∀ {x sourceSlot},
          sourceSlot.lifetime ≤ lifetime →
          env₁.slotAt x = some sourceSlot →
          ∃ resultSlot,
            env₂.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
      (motive_2 := fun env₁ _typing lifetime _terms _ty env₂ _ =>
        ∀ {x sourceSlot},
          sourceSlot.lifetime ≤ lifetime →
          env₁.slotAt x = some sourceSlot →
          ∃ resultSlot,
            env₂.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
      (by
        intro _env _typing _lifetime _value _ty _hvalue x sourceSlot
          _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hcopy _hnotRead
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty
          _hLv _hnotWrite hmove x sourceSlot _houtlives hslot
        exact EnvMove.lifetimesSurvive hmove x sourceSlot hslot)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hmutable _hnotWrite
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hnotRead
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih
          x sourceSlot houtlives hslot
        exact ih houtlives hslot)
      (by
        intro _env₁ _env₂ _env₃ _typing lifetime blockLifetime _terms _ty
          hchild _hterms _hwellTy hdrop ih x sourceSlot houtlives hslot
        rcases ih (LifetimeOutlives.trans houtlives (LifetimeChild.outlives hchild))
            hslot with
          ⟨bodySlot, hbodySlot, hbodyLifetime⟩
        subst hdrop
        have hbodyNotDropped : bodySlot.lifetime ≠ blockLifetime := by
          intro hdropped
          have hchildOutlivesParent : blockLifetime ≤ lifetime := by
            rw [← hdropped, ← hbodyLifetime]
            exact houtlives
          exact LifetimeChild.not_child_outlives_parent hchild hchildOutlivesParent
        exact ⟨bodySlot,
          Env.dropLifetime_slotAt_eq_some.mpr ⟨hbodySlot, hbodyNotDropped⟩,
          hbodyLifetime⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing lifetime y _term _ty
          hfresh _hterm _hfreshOut _hcoh henv₃ ih x sourceSlot houtlives hslot
        subst henv₃
        by_cases hxy : x = y
        · subst hxy
          rw [hfresh] at hslot
          cases hslot
        · rcases ih houtlives hslot with ⟨innerSlot, hinnerSlot, hlifetime⟩
          exact ⟨innerSlot, by simpa [Env.update, hxy] using hinnerSlot, hlifetime⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy
          _hLhs _hRhs _hshape _hwellRhs hwrite _hranked _hcoh _hnotWrite ih x sourceSlot
          houtlives hslot
        rcases ih houtlives hslot with ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
        rcases EnvWrite.lifetimesSurvive hwrite x rhsSlot hrhsSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hrhsLifetime, hresultLifetime]⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih
          x sourceSlot houtlives hslot
        exact ih houtlives hslot)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
          _hterm _hrest ihHead ihRest x sourceSlot houtlives hslot
        rcases ihHead houtlives hslot with ⟨midSlot, hmidSlot, hmidLifetime⟩
        have hmidOutlives : midSlot.lifetime ≤ _lifetime := by
          rw [← hmidLifetime]
          exact houtlives
        rcases ihRest hmidOutlives hmidSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hmidLifetime, hresultLifetime]⟩)
      htyping

theorem LValBaseOutlives.termTyping {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime current : Lifetime}
    {term : Term} {ty : Ty} {lv : LVal} :
    TermTyping env₁ typing lifetime term ty env₂ →
    LValBaseOutlives env₁ lv current →
    current ≤ lifetime →
    LValBaseOutlives env₂ lv current := by
  intro htyping hbase hcurrent
  rcases hbase with ⟨sourceSlot, hsourceSlot, hsourceOutlives⟩
  rcases (TermTyping.slot_lifetime_survives.1 htyping)
      (LifetimeOutlives.trans hsourceOutlives hcurrent)
      hsourceSlot with
    ⟨resultSlot, hresultSlot, hresultLifetime⟩
  exact ⟨resultSlot, hresultSlot, by rw [← hresultLifetime]; exact hsourceOutlives⟩

/-- Definition 3.18 `move(Γ,w)` preserves the lifetime of every surviving slot. -/
theorem EnvSlotsOutlive.move {env env' : Env} {lv : LVal}
    {current : Lifetime} :
    EnvSlotsOutlive env current →
    EnvMove env lv env' →
    EnvSlotsOutlive env' current := by
  intro houtlives hmove
  rcases hmove with ⟨slot, struck, hslot, _hstrike, henv'⟩
  rw [henv']
  exact EnvSlotsOutlive.update_same_lifetime houtlives hslot

/-- Definition 3.20 `drop(Γ,m)` preserves Definition 4.8(ii) for surviving slots. -/
theorem EnvSlotsOutlive.dropLifetime {env : Env} {dropped current : Lifetime} :
    EnvSlotsOutlive env current →
    EnvSlotsOutlive (env.dropLifetime dropped) current := by
  intro houtlives x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨hold, _hnotDropped⟩
  exact houtlives x slot hold

theorem EnvSlotsOutlive.dropLifetime_child {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    EnvSlotsOutlive env child →
    EnvSlotsOutlive (env.dropLifetime child) parent := by
  intro hchild houtlives x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨hold, hnotDropped⟩
  exact LifetimeChild.parent_of_outlives_child_ne hchild
    (houtlives x slot hold) hnotDropped

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
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime := by
  exact WellFormedEnv.update_fresh_ty

/--
Final environment-extension step with fresh-slot coherence made explicit.

This avoids the legacy `Coherent.update_fresh_ty` axiom by requiring the local
fresh-update coherence obligations for the result binding.
-/
theorem borrowInvariance_result_extension_of_coherenceObligations
    {env₂ : Env} {gamma : Name} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  exact WellFormedEnv.update_fresh_ty_of_coherenceObligations

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

theorem LifetimeIntersection.left_le {left right intersection : Lifetime} :
    LifetimeIntersection left right intersection →
    left ≤ intersection := by
  intro hintersection
  exact hintersection.1 (by simp)

theorem LifetimeIntersection.right_le {left right intersection : Lifetime} :
    LifetimeIntersection left right intersection →
    right ≤ intersection := by
  intro hintersection
  exact hintersection.1 (by simp)

theorem LifetimeIntersection.unique {left right first second : Lifetime} :
    LifetimeIntersection left right first →
    LifetimeIntersection left right second →
    first = second := by
  intro hfirst hsecond
  exact LifetimeOutlives.antisymm
    (hfirst.2 hsecond.1)
    (hsecond.2 hfirst.1)

theorem LifetimeOutlives.comparable_of_common_inner {left right current : Lifetime} :
    left ≤ current →
    right ≤ current →
    left ≤ right ∨ right ≤ left := by
  intro hleft hright
  have hleftPrefix : left.path <+: current.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hleft
  have hrightPrefix : right.path <+: current.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hright
  rcases Nat.le_total left.path.length right.path.length with hlen | hlen
  · have hprefix : left.path <+: right.path :=
      List.prefix_of_prefix_length_le hleftPrefix hrightPrefix hlen
    exact Or.inl (by
      simpa [LifetimeOutlives, Core.Lifetime.contains] using hprefix)
  · have hprefix : right.path <+: left.path :=
      List.prefix_of_prefix_length_le hrightPrefix hleftPrefix hlen
    exact Or.inr (by
      simpa [LifetimeOutlives, Core.Lifetime.contains] using hprefix)

theorem LifetimeIntersection.exists_of_common_inner {left right current : Lifetime} :
    left ≤ current →
    right ≤ current →
    ∃ intersection, LifetimeIntersection left right intersection := by
  intro hleft hright
  rcases LifetimeOutlives.comparable_of_common_inner hleft hright with
    hleftRight | hrightLeft
  · exact ⟨right, LifetimeIntersection.left hleftRight⟩
  · exact ⟨left, LifetimeIntersection.right hrightLeft⟩

theorem LValTargetsTyping.member_lifetime_outlives {env : Env}
    {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime current : Lifetime} :
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ current →
    ∀ target,
      target ∈ targets →
      ∃ targetTy selectedLifetime,
        LValTyping env target (.ty targetTy) selectedLifetime ∧
        selectedLifetime ≤ current := by
  intro htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets _partialTy targetLifetime _ =>
      targetLifetime ≤ current →
      ∀ target,
        target ∈ targets →
        ∃ targetTy selectedLifetime,
          LValTyping env target (.ty targetTy) selectedLifetime ∧
          selectedLifetime ≤ current)
    ?var ?box ?borrow ?singleton ?cons htyping houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget houtlives selected hmem
    simp at hmem
    subst hmem
    exact ⟨ty, lifetime, htarget, houtlives⟩
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest _hunion hintersection _ihHead ihRest houtlives selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ⟨headTy, headLifetime, hhead,
        LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives⟩
    · exact ihRest
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives)
        selected hselected

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
        exact hwellEnv.2.1 x slot hslot)
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
        exact hwellEnv.2.1 x slot hslot)
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

/-- The lifetime bound `lifetime ≤ current` for a typed lval needs only
`EnvSlotsOutlive env current` (every slot lives at least as long as `current`):
the lval's lifetime is the LUB of the base slots its borrow chain bottoms out at,
each bounded by `current`.  This is the `EnvSlotsOutlive`-only core of
`lifetime_outlives_one`, used to discharge the deref-borrow join lifetime bound
without circular appeal to `ContainedBorrows join`. -/
theorem LValTyping.lifetime_le_of_slotsOutlive {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime}
    (houtlive : EnvSlotsOutlive env current)
    (htyping : LValTyping env lv ty lifetime) :
    lifetime ≤ current := by
  exact LValTyping.rec
    (motive_1 := fun _lv _ty lifetime _ => lifetime ≤ current)
    (motive_2 := fun _targets _ty lifetime _ => lifetime ≤ current)
    (by intro x slot hslot; exact houtlive x slot hslot)
    (by intro _lv _inner _lifetime _htyping ih; exact ih)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets _ihBorrow ihTargets
      exact ihTargets)
    (by intro _target _ty _lifetime _htarget ihTarget; exact ihTarget)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
        _hhead _hrest _hunion hintersection ihHead ihRest
      exact LifetimeIntersection.le_of_le hintersection ihHead ihRest)
    htyping

/-- A target-list typing's union lifetime is bounded by `bound` whenever every
member lval's own typing lifetime is.  The union lifetime is the iterated LUB
(`LifetimeIntersection`) of the members, so it is `≤ bound` exactly when `bound`
is an upper bound of all members (`LifetimeIntersection.le_of_le`).  This is the
per-member fold used by the deref-borrow lifetime bound in the φ-stratified
join/contained-borrow bootstrap. -/
theorem lvalTargetsTyping_le_of_members {e : Env} {bound : Lifetime}
    {T : List LVal} {pt : PartialTy} {lf : Lifetime}
    (htgts : LValTargetsTyping e T pt lf)
    (hmem : ∀ t, t ∈ T → ∀ tt tlf, LValTyping e t (.ty tt) tlf → tlf ≤ bound) :
    lf ≤ bound := by
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _pt _lf _ => True)
    (motive_2 := fun T _pt lf _ =>
      (∀ t, t ∈ T → ∀ tt tlf, LValTyping e t (.ty tt) tlf → tlf ≤ bound) → lf ≤ bound)
    ?var ?box ?borrow ?singleton ?cons htgts hmem
  case var => intros; trivial
  case box => intros; trivial
  case borrow => intros; trivial
  case singleton =>
      intro target ty lifetime htarget _ih hmem
      exact hmem target (by simp) _ _ htarget
  case cons =>
      intro target rest headTy headLife restLife life restTy unionTy
        hhead _hrest hunion hintersection _ihHead ihRest hmem
      exact LifetimeIntersection.le_of_le hintersection
        (hmem target (by simp) _ _ hhead)
        (ihRest (fun t ht => hmem t (List.mem_cons_of_mem _ ht)))

/-- Structural classification of a typed lval: either a needle borrow occurring
in its partial type is `PartialTyContains`-reachable from the *base slot* (the
lval's spine is var/box only, so the borrow is slot-contained), or the spine
passes through a borrow dereference (a reborrow `*u`, with `u` a borrow lval of
the same base, hence same rank).  This is the case split the contained-borrow
bootstrap needs to know whether `ContainedBorrowsWellFormed` applies directly or
the φ-recursion must descend through `u`. -/
theorem lvalTyping_contained_or_reborrow {e : Env} :
    ∀ (lv : LVal) {pt : PartialTy} {lf : Lifetime} {needle : Ty},
      LValTyping e lv pt lf → PartialTyContains pt needle →
      (∃ bs, e.slotAt (LVal.base lv) = some bs ∧ PartialTyContains bs.ty needle) ∨
      (∃ u m0 T0 blf0, LVal.base u = LVal.base lv ∧
        LValTyping e u (.ty (.borrow m0 T0)) blf0) := by
  intro lv
  induction lv with
  | var x =>
      intro pt lf needle h hcontains
      cases h with
      | var hslot => exact Or.inl ⟨_, hslot, hcontains⟩
  | deref lv0 ih =>
      intro pt lf needle h hcontains
      cases h with
      | box hbox =>
          rcases ih hbox (PartialTyContains.box hcontains) with hc | hr
          · left; simpa [LVal.base] using hc
          · right
            rcases hr with ⟨u, m0, T0, blf0, hbase, htyp⟩
            exact ⟨u, m0, T0, blf0, by simpa [LVal.base] using hbase, htyp⟩
      | borrow hbor _htgts =>
          right
          exact ⟨lv0, _, _, _, by simp [LVal.base], hbor⟩

theorem LValTyping.base_outlives_one {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    LValTyping env lv ty lifetime →
    LValBaseOutlives env lv current := by
  intro hwellEnv htyping
  exact LValTyping.rec
    (motive_1 := fun lv _ty _lifetime _ => LValBaseOutlives env lv current)
    (motive_2 := fun _targets _ty _lifetime _ => True)
    (by
      intro x slot hslot
      exact ⟨slot, hslot, hwellEnv.2.1 x slot hslot⟩)
    (by
      intro _lv _inner _lifetime _htyping ih
      exact ih)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets ihBorrow _ihTargets
      exact ihBorrow)
    (by
      intro _target _ty _lifetime _htarget _ihTarget
      trivial)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
        _hhead _hrest _hunion _hintersection _ihHead _ihRest
      trivial)
    htyping

theorem EnvWrite.writeSlot_outlives_current_lifetime {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ∃ writeSlot,
      env₂.slotAt (LVal.base lhs) = some writeSlot ∧
      writeSlot.lifetime ≤ lifetime := by
  intro hwellInitial hLhs hRhs hwrite
  have hbase : LValBaseOutlives env₁ lhs lifetime :=
    LValTyping.base_outlives_one hwellInitial hLhs
  rcases hbase with ⟨sourceSlot, hsourceSlot, hsourceOutlives⟩
  rcases (TermTyping.slot_lifetime_survives.1 hRhs)
      hsourceOutlives hsourceSlot with
    ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
  cases hwrite with
  | intro hwriteSlot _hupdate =>
      rename_i writeEnv writeSlot updatedTy
      have hslotEq : writeSlot = rhsSlot := by
        have hsomeEq : some writeSlot = some rhsSlot := by
          rw [← hwriteSlot, hrhsSlot]
        exact Option.some.inj hsomeEq
      exact ⟨writeSlot, hwriteSlot, by rw [hslotEq, ← hrhsLifetime]; exact hsourceOutlives⟩

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

theorem PartialTyUnion.symm {left right union : PartialTy} :
    PartialTyUnion left right union →
    PartialTyUnion right left union := by
  intro hunion
  simpa [PartialTyUnion, PartialTyJoin, Set.pair_comm] using hunion

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

theorem PartialTyStrengthens.borrow_subset {mutable : Bool}
    {leftTargets rightTargets : List LVal} :
    PartialTyStrengthens (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets)) →
    leftTargets.Subset rightTargets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      intro target hmem
      exact hmem
  | borrow hsubset =>
      exact hsubset

theorem PartialTyStrengthens.to_borrow_inv {sourceTy : Ty}
    {mutable : Bool} {targets : List LVal} :
    PartialTyStrengthens (.ty sourceTy) (.ty (.borrow mutable targets)) →
    ∃ sourceTargets,
      sourceTy = .borrow mutable sourceTargets ∧
      sourceTargets.Subset targets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨targets, rfl, by intro target hmem; exact hmem⟩
  | borrow hsubset =>
      exact ⟨_, rfl, hsubset⟩

theorem PartialTyStrengthens.to_unit_inv {sourceTy : Ty} :
    PartialTyStrengthens (.ty sourceTy) (.ty .unit) →
    sourceTy = .unit := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.to_int_inv {sourceTy : Ty} :
    PartialTyStrengthens (.ty sourceTy) (.ty .int) →
    sourceTy = .int := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.to_box_ty_inv {sourceTy inner : Ty} :
    PartialTyStrengthens (.ty sourceTy) (.ty (.box inner)) →
    sourceTy = .box inner := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.from_unit_inv {targetTy : Ty} :
    PartialTyStrengthens (.ty .unit) (.ty targetTy) →
    targetTy = .unit := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.from_int_inv {targetTy : Ty} :
    PartialTyStrengthens (.ty .int) (.ty targetTy) →
    targetTy = .int := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.from_box_ty_inv {sourceInner targetTy : Ty} :
    PartialTyStrengthens (.ty (.box sourceInner)) (.ty targetTy) →
    targetTy = .box sourceInner := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.from_borrow_inv {mutable : Bool}
    {sourceTargets : List LVal} {targetTy : Ty} :
    PartialTyStrengthens (.ty (.borrow mutable sourceTargets)) (.ty targetTy) →
    ∃ targetTargets,
      targetTy = .borrow mutable targetTargets ∧
        sourceTargets.Subset targetTargets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨sourceTargets, rfl, by intro target hmem; exact hmem⟩
  | borrow hsubset =>
      exact ⟨_, rfl, hsubset⟩

theorem PartialTyStrengthens.to_borrow_right {source : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyStrengthens source (.ty (.borrow mutable targets)) →
    ∃ sourceTargets,
      source = .ty (.borrow mutable sourceTargets) ∧
      sourceTargets.Subset targets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨targets, rfl, by intro target hmem; exact hmem⟩
  | borrow hsubset =>
      exact ⟨_, rfl, hsubset⟩

theorem PartialTyStrengthens.box_inv {left right : PartialTy} :
    PartialTyStrengthens (.box left) (.box right) →
    PartialTyStrengthens left right := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact PartialTyStrengthens.reflex
  | box hinner =>
      exact hinner

theorem PartialTyStrengthens.not_undef_to_ty {left right : Ty} :
    ¬ PartialTyStrengthens (.undef left) (.ty right) := by
  intro hstrength
  cases hstrength

theorem PartialTyStrengthens.not_undef_to_box {left : Ty} {right : PartialTy} :
    ¬ PartialTyStrengthens (.undef left) (.box right) := by
  intro hstrength
  cases hstrength

theorem PartialTyStrengthens.not_box_to_ty {left : PartialTy} {right : Ty} :
    ¬ PartialTyStrengthens (.box left) (.ty right) := by
  intro hstrength
  cases hstrength

theorem PartialTyStrengthens.not_ty_to_box {left : Ty} {right : PartialTy} :
    ¬ PartialTyStrengthens (.ty left) (.box right) := by
  intro hstrength
  cases hstrength

theorem PartialTyStrengthens.ty_to_undef_inv {left right : Ty} :
    PartialTyStrengthens (.ty left) (.undef right) →
    PartialTyStrengthens (.ty left) (.ty right) := by
  intro hstrength
  cases hstrength with
  | intoUndef hinner =>
      exact hinner

theorem PartialTyStrengthens.box_to_undef_inv {left : PartialTy} {right : Ty} :
    PartialTyStrengthens (.box left) (.undef right) →
    ∃ inner,
      right = .box inner ∧
        PartialTyStrengthens left (.undef inner) := by
  intro hstrength
  cases hstrength with
  | boxIntoUndef hinner =>
      exact ⟨_, rfl, hinner⟩

theorem PartialTyStrengthens.ty_to_ty_inv {left right : Ty} :
    PartialTyStrengthens (.ty left) (.ty right) →
    left = right ∨
      ∃ mutable leftTargets rightTargets,
        left = .borrow mutable leftTargets ∧
        right = .borrow mutable rightTargets ∧
        leftTargets.Subset rightTargets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact Or.inl rfl
  | borrow hsubset =>
      exact Or.inr ⟨_, _, _, rfl, rfl, hsubset⟩

theorem PartialTyStrengthens.to_ty_right {source : PartialTy} {target : Ty} :
    PartialTyStrengthens source (.ty target) →
    ∃ sourceTy, source = .ty sourceTy := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨target, rfl⟩
  | borrow _hsubset =>
      exact ⟨.borrow _ _, rfl⟩

theorem PartialTyUnion.right_full_of_ty_union {headTy resultTy : Ty}
    {restTy : PartialTy} :
    PartialTyUnion (.ty headTy) restTy (.ty resultTy) →
    ∃ restFull, restTy = .ty restFull := by
  intro hunion
  exact PartialTyStrengthens.to_ty_right
    (PartialTyUnion.right_strengthens hunion)

theorem PartialTyUnion.left_full_of_ty_union {resultTy : Ty}
    {leftTy rightTy : PartialTy} :
    PartialTyUnion leftTy rightTy (.ty resultTy) →
    ∃ leftFull, leftTy = .ty leftFull := by
  intro hunion
  exact PartialTyStrengthens.to_ty_right
    (PartialTyUnion.left_strengthens hunion)

theorem LValTargetsTyping.cons_full_inv {env : Env}
    {target : LVal} {rest : List LVal} {ty : Ty}
    {lifetime : Lifetime} :
    rest ≠ [] →
    LValTargetsTyping env (target :: rest) (.ty ty) lifetime →
    ∃ headTy headLifetime restTy restLifetime,
      LValTyping env target (.ty headTy) headLifetime ∧
        LValTargetsTyping env rest (.ty restTy) restLifetime ∧
        PartialTyUnion (.ty headTy) (.ty restTy) (.ty ty) ∧
        LifetimeIntersection headLifetime restLifetime lifetime := by
  intro hrest htyping
  cases htyping with
  | singleton _htarget =>
      simp at hrest
  | cons hhead hrestTyping hunion hintersection =>
      rcases PartialTyUnion.right_full_of_ty_union hunion with
        ⟨restTy, hrestTy⟩
      subst hrestTy
      exact ⟨_, _, restTy, _, hhead, hrestTyping, hunion, hintersection⟩

theorem PartialTyUnion.ty_ty_full {left right : Ty} {union : PartialTy} :
    PartialTyUnion (.ty left) (.ty right) union →
    ∃ ty, union = .ty ty := by
  intro hunion
  have hleftStrength := PartialTyUnion.left_strengthens hunion
  cases hleftStrength with
  | reflex =>
      exact ⟨left, rfl⟩
  | borrow hsubset =>
      exact ⟨.borrow _ _, rfl⟩
  | intoUndef hleftRight =>
      rename_i upperTy
      have hrightStrength := PartialTyUnion.right_strengthens hunion
      cases hrightStrength with
      | intoUndef hrightUpper =>
      have hupper : (.ty upperTy) ∈ upperBounds ({.ty left, .ty right} : Set PartialTy) := by
        intro candidate hcandidate
        simp at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst hcandidate
          show PartialTyStrengthens (.ty left) (.ty upperTy)
          exact hleftRight
        · subst hcandidate
          show PartialTyStrengthens (.ty right) (.ty upperTy)
          exact hrightUpper
      have hundefLeTy :
          PartialTyStrengthens (.undef upperTy) (.ty upperTy) := by
        simpa [partialTy_le_iff] using hunion.2 hupper
      exact False.elim (PartialTyStrengthens.not_undef_to_ty hundefLeTy)

theorem LValTargetsTyping.output_full {env : Env}
    {targets : List LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTargetsTyping env targets partialTy lifetime →
    ∃ ty, partialTy = .ty ty := by
  intro htyping
  exact LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun _targets partialTy _lifetime _ =>
      ∃ ty, partialTy = .ty ty)
    (by
      intro _x _slot _hslot
      trivial)
    (by
      intro _lv _inner _lifetime _htyping _ih
      trivial)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets _ihBorrow _ihTargets
      trivial)
    (by
      intro _target ty _lifetime _htarget _ihTarget
      exact ⟨ty, rfl⟩)
    (by
      intro _target _rest headTy _headLifetime _restLifetime _lifetime restTy
        unionTy _hhead _hrest hunion _hintersection _ihHead ihRest
      rcases ihRest with ⟨restFull, hrestFull⟩
      subst hrestFull
      exact PartialTyUnion.ty_ty_full hunion)
    htyping

theorem LValTargetsTyping.not_box {env : Env}
    {targets : List LVal} {inner : PartialTy} {lifetime : Lifetime} :
    ¬ LValTargetsTyping env targets (.box inner) lifetime := by
  intro htyping
  rcases LValTargetsTyping.output_full htyping with ⟨ty, hfull⟩
  cases hfull

theorem LValTyping.deref_box_inv {env : Env} {source : LVal}
    {inner : PartialTy} {lifetime : Lifetime} :
    LValTyping env (.deref source) (.box inner) lifetime →
    LValTyping env source (.box (.box inner)) lifetime := by
  intro htyping
  cases htyping with
  | box hsource =>
      exact hsource
  | borrow _hborrow htargets =>
      exact False.elim (LValTargetsTyping.not_box htargets)

theorem LValTyping.deref_box_full_inv {env : Env} {source : LVal}
    {ty : Ty} {lifetime : Lifetime} :
    LValTyping env (.deref source) (.box (.ty ty)) lifetime →
    LValTyping env source (.box (.box (.ty ty))) lifetime := by
  exact LValTyping.deref_box_inv

theorem PartialTyUnion.box_box_shape {left right union : PartialTy} :
    PartialTyUnion (.box left) (.box right) union →
    ∃ inner, union = .box inner := by
  intro hunion
  have hleftStrength := PartialTyUnion.left_strengthens hunion
  cases hleftStrength with
  | reflex =>
      exact ⟨left, rfl⟩
  | box hleftInner =>
      exact ⟨_, rfl⟩
  | boxIntoUndef hleftUpper =>
      rename_i upperTy
      have hrightStrength := PartialTyUnion.right_strengthens hunion
      cases hrightStrength with
      | boxIntoUndef hrightUpper =>
          have hupper :
              (.box (.undef upperTy)) ∈ upperBounds ({.box left, .box right} : Set PartialTy) := by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact PartialTyStrengthens.box hleftUpper
            · subst hcandidate
              exact PartialTyStrengthens.box hrightUpper
          have hundefLeBox :
              PartialTyStrengthens (.undef (.box upperTy)) (.box (.undef upperTy)) := by
            simpa [partialTy_le_iff] using hunion.2 hupper
          exact False.elim (PartialTyStrengthens.not_undef_to_box hundefLeBox)

theorem PartialTyUnion.not_box_borrow {left union : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    ¬ PartialTyUnion (.box left) (.ty (.borrow mutable targets)) union := by
  intro hunion
  have hleftStrength := PartialTyUnion.left_strengthens hunion
  have hrightStrength := PartialTyUnion.right_strengthens hunion
  cases hleftStrength with
  | reflex =>
      exact PartialTyStrengthens.not_ty_to_box hrightStrength
  | box hbox =>
      exact PartialTyStrengthens.not_ty_to_box hrightStrength
  | boxIntoUndef hboxUndef =>
      rename_i upperTy
      have hrightTy :
          PartialTyStrengthens (.ty (.borrow mutable targets)) (.ty (.box upperTy)) :=
        PartialTyStrengthens.ty_to_undef_inv hrightStrength
      cases hrightTy

theorem PartialTyUnion.not_borrow_box {right union : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    ¬ PartialTyUnion (.ty (.borrow mutable targets)) (.box right) union := by
  intro hunion
  exact PartialTyUnion.not_box_borrow (PartialTyUnion.symm hunion)

theorem PartialTyUnion.borrow_borrow_shape {mutable : Bool}
    {leftTargets rightTargets : List LVal} {union : PartialTy} :
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets)) union →
    ∃ unionTargets,
      union = .ty (.borrow mutable unionTargets) ∧
        leftTargets.Subset unionTargets ∧
        rightTargets.Subset unionTargets := by
  intro hunion
  rcases PartialTyUnion.ty_ty_full hunion with ⟨unionTy, hunionTy⟩
  have hleftStrength :
      PartialTyStrengthens (.ty (.borrow mutable leftTargets))
        (.ty unionTy) := by
    rw [← hunionTy]
    exact PartialTyUnion.left_strengthens hunion
  have hrightStrength :
      PartialTyStrengthens (.ty (.borrow mutable rightTargets))
        (.ty unionTy) := by
    rw [← hunionTy]
    exact PartialTyUnion.right_strengthens hunion
  cases hleftStrength with
  | reflex =>
      have hrightSubset :
          rightTargets.Subset leftTargets :=
        PartialTyStrengthens.borrow_subset hrightStrength
      exact ⟨leftTargets, hunionTy, by intro target hmem; exact hmem, hrightSubset⟩
  | borrow hleftSubset =>
      rename_i unionTargets
      have hrightSubset :
          rightTargets.Subset unionTargets :=
        PartialTyStrengthens.borrow_subset hrightStrength
      exact ⟨unionTargets, hunionTy, hleftSubset, hrightSubset⟩

theorem PartialTyUnion.borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal} :
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable (leftTargets ++ rightTargets))) := by
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        exact List.mem_append_left rightTargets htarget)
    · subst hcandidate
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        exact List.mem_append_right leftTargets htarget)
  · intro upper hupper
    have hleftUpper :
        PartialTyStrengthens (.ty (.borrow mutable leftTargets)) upper :=
      hupper (by simp)
    have hrightUpper :
        PartialTyStrengthens (.ty (.borrow mutable rightTargets)) upper :=
      hupper (by simp)
    cases hleftUpper with
    | reflex =>
        have hrightSubset :
            rightTargets.Subset leftTargets :=
          PartialTyStrengthens.borrow_subset hrightUpper
        exact PartialTyStrengthens.borrow (by
          intro target htarget
          rcases List.mem_append.mp htarget with hleft | hright
          · exact hleft
          · exact hrightSubset hright)
    | borrow hleftSubset =>
        rename_i upperTargets
        have hrightSubset :
            rightTargets.Subset upperTargets :=
          PartialTyStrengthens.borrow_subset hrightUpper
        exact PartialTyStrengthens.borrow (by
          intro target htarget
          rcases List.mem_append.mp htarget with hleft | hright
          · exact hleftSubset hleft
          · exact hrightSubset hright)
    | intoUndef hleftInner =>
        rename_i upperTy
        have hrightInner :
            PartialTyStrengthens (.ty (.borrow mutable rightTargets)) (.ty upperTy) :=
          PartialTyStrengthens.ty_to_undef_inv hrightUpper
        have happendInner :
            PartialTyStrengthens
              (.ty (.borrow mutable (leftTargets ++ rightTargets))) (.ty upperTy) := by
          cases hleftInner with
          | reflex =>
              have hrightSubset :
                  rightTargets.Subset leftTargets :=
                PartialTyStrengthens.borrow_subset hrightInner
              exact PartialTyStrengthens.borrow (by
                intro target htarget
                rcases List.mem_append.mp htarget with hleft | hright
                · exact hleft
                · exact hrightSubset hright)
          | borrow hleftSubset =>
              rename_i upperTargets
              have hrightSubset :
                  rightTargets.Subset upperTargets :=
                PartialTyStrengthens.borrow_subset hrightInner
              exact PartialTyStrengthens.borrow (by
                intro target htarget
                rcases List.mem_append.mp htarget with hleft | hright
                · exact hleftSubset hleft
                · exact hrightSubset hright)
        exact PartialTyStrengthens.intoUndef happendInner

/--
Bounded join existence.  If two full types both strengthen a common full bound
`boundTy`, then their union exists and is itself bounded by `boundTy`.

This is the order-theoretic fact behind faithful borrow-target-list joins: the
union target list arising from a write-through-borrow is well typed precisely
because shape compatibility forces every joined component under one common bound
(see `LValTargetsTyping.of_members_bounded`).
-/
theorem partialTyUnion_exists_of_le_bound {leftTy rightTy boundTy : Ty} :
    PartialTyStrengthens (.ty leftTy) (.ty boundTy) →
    PartialTyStrengthens (.ty rightTy) (.ty boundTy) →
    ∃ unionTy,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty unionTy) ∧
        PartialTyStrengthens (.ty unionTy) (.ty boundTy) := by
  intro hleft hright
  cases boundTy with
  | unit =>
      have hl : leftTy = .unit := PartialTyStrengthens.to_unit_inv hleft
      have hr : rightTy = .unit := PartialTyStrengthens.to_unit_inv hright
      subst hl; subst hr
      exact ⟨.unit, PartialTyUnion.self _, PartialTyStrengthens.reflex⟩
  | int =>
      have hl : leftTy = .int := PartialTyStrengthens.to_int_inv hleft
      have hr : rightTy = .int := PartialTyStrengthens.to_int_inv hright
      subst hl; subst hr
      exact ⟨.int, PartialTyUnion.self _, PartialTyStrengthens.reflex⟩
  | box inner =>
      have hl : leftTy = .box inner := PartialTyStrengthens.to_box_ty_inv hleft
      have hr : rightTy = .box inner := PartialTyStrengthens.to_box_ty_inv hright
      subst hl; subst hr
      exact ⟨.box inner, PartialTyUnion.self _, PartialTyStrengthens.reflex⟩
  | borrow mutable boundTargets =>
      rcases PartialTyStrengthens.to_borrow_inv hleft with
        ⟨leftTargets, hleftEq, hleftSubset⟩
      rcases PartialTyStrengthens.to_borrow_inv hright with
        ⟨rightTargets, hrightEq, hrightSubset⟩
      subst hleftEq; subst hrightEq
      refine ⟨.borrow mutable (leftTargets ++ rightTargets),
        PartialTyUnion.borrow_append,
        PartialTyStrengthens.borrow ?_⟩
      intro target htarget
      rcases List.mem_append.mp htarget with hmem | hmem
      · exact hleftSubset hmem
      · exact hrightSubset hmem

theorem PartialTyUnion.not_borrow_mismatch {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal} {union : PartialTy} :
    leftMutable ≠ rightMutable →
    ¬ PartialTyUnion (.ty (.borrow leftMutable leftTargets))
      (.ty (.borrow rightMutable rightTargets)) union := by
  intro hmutableNe hunion
  rcases PartialTyUnion.ty_ty_full hunion with ⟨unionTy, hunionTy⟩
  have hleftStrength :
      PartialTyStrengthens (.ty (.borrow leftMutable leftTargets))
        (.ty unionTy) := by
    rw [← hunionTy]
    exact PartialTyUnion.left_strengthens hunion
  have hrightStrength :
      PartialTyStrengthens (.ty (.borrow rightMutable rightTargets))
        (.ty unionTy) := by
    rw [← hunionTy]
    exact PartialTyUnion.right_strengthens hunion
  cases hleftStrength with
  | reflex =>
      cases hrightStrength with
      | reflex =>
          exact hmutableNe rfl
      | borrow _hsubset =>
          exact hmutableNe rfl
  | borrow _hsubset =>
      cases hrightStrength with
      | reflex =>
          exact hmutableNe rfl
      | borrow _hsubsetRight =>
          exact hmutableNe rfl

theorem PartialTyUnion.full_connected_union_exists
    {leftHeadTy leftRestTy rightHeadTy rightRestTy leftTy joinHeadTy joinRestTy : Ty} :
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty leftHeadTy) (.ty rightHeadTy) (.ty joinHeadTy) →
    PartialTyUnion (.ty leftRestTy) (.ty rightRestTy) (.ty joinRestTy) →
    ∃ joinTy, PartialTyUnion (.ty joinHeadTy) (.ty joinRestTy) (.ty joinTy) := by
  intro hleftUnion hheadUnion hrestUnion
  cases joinHeadTy with
  | unit =>
      have hleftHeadUnit : leftHeadTy = .unit :=
        PartialTyStrengthens.to_unit_inv
          (PartialTyUnion.left_strengthens hheadUnion)
      have hrightHeadUnit : rightHeadTy = .unit :=
        PartialTyStrengthens.to_unit_inv
          (PartialTyUnion.right_strengthens hheadUnion)
      subst hleftHeadUnit
      have hleftTyUnit : leftTy = .unit :=
        PartialTyStrengthens.from_unit_inv
          (PartialTyUnion.left_strengthens hleftUnion)
      subst hleftTyUnit
      have hleftRestUnit : leftRestTy = .unit :=
        PartialTyStrengthens.to_unit_inv
          (PartialTyUnion.right_strengthens hleftUnion)
      subst hleftRestUnit
      have hjoinRestUnit : joinRestTy = .unit :=
        PartialTyStrengthens.from_unit_inv
          (PartialTyUnion.left_strengthens hrestUnion)
      subst hjoinRestUnit
      exact ⟨.unit, PartialTyUnion.self (.ty .unit)⟩
  | int =>
      have hleftHeadInt : leftHeadTy = .int :=
        PartialTyStrengthens.to_int_inv
          (PartialTyUnion.left_strengthens hheadUnion)
      have hrightHeadInt : rightHeadTy = .int :=
        PartialTyStrengthens.to_int_inv
          (PartialTyUnion.right_strengthens hheadUnion)
      subst hleftHeadInt
      have hleftTyInt : leftTy = .int :=
        PartialTyStrengthens.from_int_inv
          (PartialTyUnion.left_strengthens hleftUnion)
      subst hleftTyInt
      have hleftRestInt : leftRestTy = .int :=
        PartialTyStrengthens.to_int_inv
          (PartialTyUnion.right_strengthens hleftUnion)
      subst hleftRestInt
      have hjoinRestInt : joinRestTy = .int :=
        PartialTyStrengthens.from_int_inv
          (PartialTyUnion.left_strengthens hrestUnion)
      subst hjoinRestInt
      exact ⟨.int, PartialTyUnion.self (.ty .int)⟩
  | borrow mutable joinHeadTargets =>
      rcases PartialTyStrengthens.to_borrow_inv
          (PartialTyUnion.left_strengthens hheadUnion) with
        ⟨leftHeadTargets, hleftHeadEq, _hleftHeadSubset⟩
      rcases PartialTyStrengthens.to_borrow_inv
          (PartialTyUnion.right_strengthens hheadUnion) with
        ⟨rightHeadTargets, hrightHeadEq, _hrightHeadSubset⟩
      subst hleftHeadEq
      rcases PartialTyStrengthens.from_borrow_inv
          (PartialTyUnion.left_strengthens hleftUnion) with
        ⟨_leftHeadUpperTargets, hleftTyEq, _hleftTySubset⟩
      subst hleftTyEq
      rcases PartialTyStrengthens.to_borrow_inv
          (PartialTyUnion.right_strengthens hleftUnion) with
        ⟨leftRestTargets, hleftRestEq, _hleftRestSubset⟩
      subst hleftRestEq
      rcases PartialTyStrengthens.from_borrow_inv
          (PartialTyUnion.left_strengthens hrestUnion) with
        ⟨_leftRestUpperTargets, hjoinRestEq, _hjoinRestSubset⟩
      subst hjoinRestEq
      exact ⟨.borrow mutable (joinHeadTargets ++ _),
        PartialTyUnion.borrow_append⟩
  | box joinHeadInner =>
      have hleftHeadBox : leftHeadTy = .box joinHeadInner :=
        PartialTyStrengthens.to_box_ty_inv
          (PartialTyUnion.left_strengthens hheadUnion)
      have hrightHeadBox : rightHeadTy = .box joinHeadInner :=
        PartialTyStrengthens.to_box_ty_inv
          (PartialTyUnion.right_strengthens hheadUnion)
      subst hleftHeadBox
      have hleftTyBox : leftTy = .box joinHeadInner :=
        PartialTyStrengthens.from_box_ty_inv
          (PartialTyUnion.left_strengthens hleftUnion)
      subst hleftTyBox
      have hleftRestBox : leftRestTy = .box joinHeadInner :=
        PartialTyStrengthens.to_box_ty_inv
          (PartialTyUnion.right_strengthens hleftUnion)
      subst hleftRestBox
      have hjoinRestBox : joinRestTy = .box joinHeadInner :=
        PartialTyStrengthens.from_box_ty_inv
          (PartialTyUnion.left_strengthens hrestUnion)
      subst hjoinRestBox
      exact ⟨.box joinHeadInner, PartialTyUnion.self (.ty (.box joinHeadInner))⟩

theorem ShapeCompatible.full_partialTyUnion_exists {env : Env}
    {left right : Ty} :
    ShapeCompatible env (.ty left) (.ty right) →
    ∃ unionTy, PartialTyUnion (.ty left) (.ty right) (.ty unionTy) := by
  intro hshape
  cases hshape with
  | unit =>
      exact ⟨.unit, PartialTyUnion.self (.ty .unit)⟩
  | int =>
      exact ⟨.int, PartialTyUnion.self (.ty .int)⟩
  | borrow _hleft _hright _hcompatible =>
      exact ⟨.borrow _ (_ ++ _), PartialTyUnion.borrow_append⟩

/-- Definition 3.22 shape compatibility is symmetric. -/
theorem ShapeCompatible.symm {env : Env} {left right : PartialTy} :
    ShapeCompatible env left right →
    ShapeCompatible env right left := by
  intro h
  induction h with
  | unit => exact ShapeCompatible.unit
  | int => exact ShapeCompatible.int
  | box _hinner ih => exact ShapeCompatible.box ih
  | borrow hleft hright _hcompat ih => exact ShapeCompatible.borrow hright hleft ih
  | undefLeft _hinner ih => exact ShapeCompatible.undefRight ih
  | undefRight _hinner ih => exact ShapeCompatible.undefLeft ih

/-- `ShapeCompatible` transports along a target-subset on the left borrow: if a
borrow `&[m]T` is shape-compatible with `b` and `T' ⊆ T`, then `&[m]T'` is too.
(S-Bor only needs every left target to share the common pointee type; a subset
still does.)  This is the bridge that specialises a *joint* borrow's
`ShapeCompatible` to each *member* borrow (member targets ⊆ union targets) — the
piece the fan-out `hbranch` shape argument needs. -/
theorem ShapeCompatible.of_subset_targets_left {env : Env} {m : Bool}
    {T T' : List LVal} {b : PartialTy}
    (h : ShapeCompatible env (.ty (.borrow m T)) b)
    (hsub : ∀ t, t ∈ T' → t ∈ T) :
    ShapeCompatible env (.ty (.borrow m T')) b := by
  cases h with
  | borrow hleft hright hsc =>
      exact ShapeCompatible.borrow (fun t ht => hleft t (hsub t ht)) hright hsc
  | undefRight hinner =>
      cases hinner with
      | borrow hleft hright hsc =>
          exact ShapeCompatible.undefRight
            (ShapeCompatible.borrow (fun t ht => hleft t (hsub t ht)) hright hsc)

theorem PartialTyUnion.undef_left_ty {left right union : Ty} :
    PartialTyUnion (.ty left) (.ty right) (.ty union) →
    PartialTyUnion (.undef left) (.ty right) (.undef union) := by
  intro hunion
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.undefLeft
        (PartialTyUnion.left_strengthens hunion)
    · subst hcandidate
      exact PartialTyStrengthens.intoUndef
        (PartialTyUnion.right_strengthens hunion)
  · intro upper hupper
    have hleftUpper :
        PartialTyStrengthens (.undef left) upper :=
      hupper (by simp)
    have hrightUpper :
        PartialTyStrengthens (.ty right) upper :=
      hupper (by simp)
    cases hleftUpper with
    | reflex =>
        have hrightLeft :
            PartialTyStrengthens (.ty right) (.ty left) :=
          PartialTyStrengthens.ty_to_undef_inv hrightUpper
        have hunionLeft : PartialTyStrengthens (.ty union) (.ty left) :=
          hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact PartialTyStrengthens.reflex
            · subst hcandidate
              exact hrightLeft)
        exact PartialTyStrengthens.undefLeft hunionLeft
    | undefLeft hleftInner =>
        rename_i upperTy
        have hrightInner :
            PartialTyStrengthens (.ty right) (.ty upperTy) :=
          PartialTyStrengthens.ty_to_undef_inv hrightUpper
        have hunionUpper : PartialTyStrengthens (.ty union) (.ty upperTy) :=
          hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact hleftInner
            · subst hcandidate
              exact hrightInner)
        exact PartialTyStrengthens.undefLeft hunionUpper

theorem PartialTyUnion.ty_undef_right {left right union : Ty} :
    PartialTyUnion (.ty left) (.ty right) (.ty union) →
    PartialTyUnion (.ty left) (.undef right) (.undef union) := by
  intro hunion
  exact PartialTyUnion.symm
    (PartialTyUnion.undef_left_ty (PartialTyUnion.symm hunion))

theorem ShapeCompatible.right_full_partialTyUnion_exists {env : Env}
    {oldTy : PartialTy} {rhsTy : Ty} :
    ShapeCompatible env oldTy (.ty rhsTy) →
    ∃ unionTy, PartialTyUnion oldTy (.ty rhsTy) unionTy := by
  intro hshape
  cases hshape with
  | unit =>
      exact ⟨.ty .unit, PartialTyUnion.self (.ty .unit)⟩
  | int =>
      exact ⟨.ty .int, PartialTyUnion.self (.ty .int)⟩
  | borrow _hcompatible =>
      exact ⟨.ty (.borrow _ (_ ++ _)), PartialTyUnion.borrow_append⟩
  | undefLeft hinner =>
      rcases ShapeCompatible.full_partialTyUnion_exists hinner with
        ⟨unionTy, hunion⟩
      exact ⟨.undef unionTy, PartialTyUnion.undef_left_ty hunion⟩

theorem PartialTyUnion.box_inv {left right union : PartialTy} :
    PartialTyUnion (.box left) (.box right) (.box union) →
    PartialTyUnion left right union := by
  intro hunion
  constructor
  · intro ty hty
    simp at hty
    rcases hty with hty | hty
    · subst hty
      exact PartialTyStrengthens.box_inv (PartialTyUnion.left_strengthens hunion)
    · subst hty
      exact PartialTyStrengthens.box_inv (PartialTyUnion.right_strengthens hunion)
  · intro candidate hcandidate
    have hboxedUpper :
        (.box candidate) ∈ upperBounds ({.box left, .box right} : Set PartialTy) := by
      intro ty hty
      simp at hty
      rcases hty with hty | hty
      · subst hty
        exact PartialTyStrengthens.box (hcandidate (by simp))
      · subst hty
        exact PartialTyStrengthens.box (hcandidate (by simp))
    exact PartialTyStrengthens.box_inv (hunion.2 hboxedUpper)

theorem PartialTyUnion.box {left right union : PartialTy} :
    PartialTyUnion left right union →
    PartialTyUnion (.box left) (.box right) (.box union) := by
  intro hunion
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.box (PartialTyUnion.left_strengthens hunion)
    · subst hcandidate
      exact PartialTyStrengthens.box (PartialTyUnion.right_strengthens hunion)
  · intro upper hupper
    have hleftUpper :
        PartialTyStrengthens (.box left) upper :=
      hupper (by simp)
    have hrightUpper :
        PartialTyStrengthens (.box right) upper :=
      hupper (by simp)
    cases hleftUpper with
    | reflex =>
        have hrightLeft :
            PartialTyStrengthens right left :=
          PartialTyStrengthens.box_inv hrightUpper
        have hunionLeft : PartialTyStrengthens union left := by
          exact hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact PartialTyStrengthens.reflex
            · subst hcandidate
              exact hrightLeft)
        exact PartialTyStrengthens.box hunionLeft
    | box hleftInner =>
        rename_i upperInner
        have hrightInner :
            PartialTyStrengthens right upperInner :=
          PartialTyStrengthens.box_inv hrightUpper
        have hunionUpper : PartialTyStrengthens union upperInner := by
          exact hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact hleftInner
            · subst hcandidate
              exact hrightInner)
        exact PartialTyStrengthens.box hunionUpper
    | boxIntoUndef hleftInner =>
        rename_i upperTy
        rcases PartialTyStrengthens.box_to_undef_inv hrightUpper with
          ⟨rightUpper, hupperTy, hrightInner⟩
        have hrightUpperEq : rightUpper = upperTy := by
          injection hupperTy with hinner
          exact hinner.symm
        subst hrightUpperEq
        have hunionUpper : PartialTyStrengthens union (.undef rightUpper) := by
          exact hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact hleftInner
            · subst hcandidate
              exact hrightInner)
        exact PartialTyStrengthens.boxIntoUndef hunionUpper

theorem PartialTyUnion.borrow_member {mutable : Bool}
    {leftTargets rightTargets unionTargets : List LVal} {target : LVal} :
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable unionTargets)) →
    target ∈ unionTargets →
    target ∈ leftTargets ∨ target ∈ rightTargets := by
  intro hunion hmem
  by_contra hnot
  have hnotLeft : target ∉ leftTargets := by
    intro h
    exact hnot (Or.inl h)
  have hnotRight : target ∉ rightTargets := by
    intro h
    exact hnot (Or.inr h)
  have hleftSubsetUnion : leftTargets.Subset unionTargets := by
    exact PartialTyStrengthens.borrow_subset
      (PartialTyUnion.left_strengthens hunion)
  have hrightSubsetUnion : rightTargets.Subset unionTargets := by
    exact PartialTyStrengthens.borrow_subset
      (PartialTyUnion.right_strengthens hunion)
  have hleftLeFilter : PartialTyStrengthens (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable (unionTargets.filter (fun x => x ≠ target)))) := by
    apply PartialTyStrengthens.borrow
    intro x hx
    have hxUnion := hleftSubsetUnion hx
    have hne : x ≠ target := by
      intro heq
      subst heq
      exact hnotLeft hx
    simp [hxUnion, hne]
  have hrightLeFilter : PartialTyStrengthens (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable (unionTargets.filter (fun x => x ≠ target)))) := by
    apply PartialTyStrengthens.borrow
    intro x hx
    have hxUnion := hrightSubsetUnion hx
    have hne : x ≠ target := by
      intro heq
      subst heq
      exact hnotRight hx
    simp [hxUnion, hne]
  have hunionLeFilter : PartialTyStrengthens (.ty (.borrow mutable unionTargets))
      (.ty (.borrow mutable (unionTargets.filter (fun x => x ≠ target)))) := by
    exact hunion.2 (by
      intro ty hty
      simp at hty
      rcases hty with hty | hty
      · simpa [hty] using hleftLeFilter
      · simpa [hty] using hrightLeFilter)
  have hsubsetFilter :
      unionTargets.Subset (unionTargets.filter (fun x => x ≠ target)) := by
    exact PartialTyStrengthens.borrow_subset hunionLeFilter
  have hfiltered : target ∈ unionTargets.filter (fun x => x ≠ target) :=
    hsubsetFilter hmem
  simp at hfiltered

theorem PartialTyUnion.contained_borrow_member {left right union : PartialTy}
    {mutable : Bool} {targets : List LVal} {target : LVal} :
    PartialTyUnion left right union →
    PartialTyContains union (.borrow mutable targets) →
    target ∈ targets →
    (∃ leftTargets,
      PartialTyContains left (.borrow mutable leftTargets) ∧ target ∈ leftTargets) ∨
    (∃ rightTargets,
      PartialTyContains right (.borrow mutable rightTargets) ∧ target ∈ rightTargets) := by
  refine PartialTy.rec
    (motive_1 := fun unionTy =>
      ∀ left right mutable targets target,
        PartialTyUnion left right (.ty unionTy) →
        PartialTyContains (.ty unionTy) (.borrow mutable targets) →
        target ∈ targets →
        (∃ leftTargets,
          PartialTyContains left (.borrow mutable leftTargets) ∧
            target ∈ leftTargets) ∨
        (∃ rightTargets,
          PartialTyContains right (.borrow mutable rightTargets) ∧
            target ∈ rightTargets))
    (motive_2 := fun union =>
      ∀ left right mutable targets target,
        PartialTyUnion left right union →
        PartialTyContains union (.borrow mutable targets) →
        target ∈ targets →
        (∃ leftTargets,
          PartialTyContains left (.borrow mutable leftTargets) ∧
            target ∈ leftTargets) ∨
        (∃ rightTargets,
          PartialTyContains right (.borrow mutable rightTargets) ∧
            target ∈ rightTargets))
    ?unit ?int ?borrow ?boxTy ?ty ?boxPartial ?undef union
    left right mutable targets target
  · intro left right mutable targets target _hunion hcontains _htarget
    cases hcontains
  · intro left right mutable targets target _hunion hcontains _htarget
    cases hcontains
  · intro unionMutable unionTargets left right mutable targets target hunion
      hcontains htarget
    cases hcontains with
    | here =>
      rcases PartialTyStrengthens.to_borrow_right
          (PartialTyUnion.left_strengthens hunion) with
        ⟨leftTargets, rfl, _hleftSubset⟩
      rcases PartialTyStrengthens.to_borrow_right
          (PartialTyUnion.right_strengthens hunion) with
        ⟨rightTargets, rfl, _hrightSubset⟩
      rcases PartialTyUnion.borrow_member hunion htarget with hleft | hright
      · exact Or.inl ⟨leftTargets, PartialTyContains.here, hleft⟩
      · exact Or.inr ⟨rightTargets, PartialTyContains.here, hright⟩
  · intro inner _ih left right mutable targets target hunion hcontains htarget
    cases hcontains with
    | tyBox hinner =>
      have hleft := PartialTyUnion.left_strengthens hunion
      cases hleft with
      | reflex =>
          exact Or.inl ⟨targets, PartialTyContains.tyBox hinner, htarget⟩
  · intro ty ih left right mutable targets target hunion hcontains htarget
    exact ih left right mutable targets target hunion hcontains htarget
  · intro inner ih left right mutable targets target hunion hcontains htarget
    cases hcontains with
    | box hinner =>
      have hleft := PartialTyUnion.left_strengthens hunion
      cases hleft with
      | reflex =>
          exact Or.inl ⟨targets, PartialTyContains.box hinner, htarget⟩
      | box hleftInner =>
          have hright := PartialTyUnion.right_strengthens hunion
          cases hright with
          | reflex =>
              exact Or.inr ⟨targets, PartialTyContains.box hinner, htarget⟩
          | box hrightInner =>
              rcases ih _ _ mutable targets target
                  (PartialTyUnion.box_inv hunion) hinner htarget with
                hleftBorrow | hrightBorrow
              · rcases hleftBorrow with ⟨leftTargets, hcontainsLeft, hleftMem⟩
                exact Or.inl
                  ⟨leftTargets, PartialTyContains.box hcontainsLeft, hleftMem⟩
              · rcases hrightBorrow with ⟨rightTargets, hcontainsRight, hrightMem⟩
                exact Or.inr
                  ⟨rightTargets, PartialTyContains.box hcontainsRight, hrightMem⟩
  · intro shape _ih left right mutable targets target _hunion hcontains _htarget
    cases hcontains

/-- A variable occurs in a partial type iff it is the base of some target of a
borrow contained (through box nesting) in that type. -/
theorem mem_partialTy_vars_iff {pt : PartialTy} {v : Name} :
    v ∈ PartialTy.vars pt ↔
    ∃ mutable targets target,
      PartialTyContains pt (.borrow mutable targets) ∧
        target ∈ targets ∧ LVal.base target = v := by
  refine PartialTy.rec
    (motive_1 := fun t =>
      v ∈ Ty.vars t ↔
      ∃ mutable targets target,
        PartialTyContains (.ty t) (.borrow mutable targets) ∧
          target ∈ targets ∧ LVal.base target = v)
    (motive_2 := fun pt =>
      v ∈ PartialTy.vars pt ↔
      ∃ mutable targets target,
        PartialTyContains pt (.borrow mutable targets) ∧
          target ∈ targets ∧ LVal.base target = v)
    ?unit ?int ?borrow ?boxTy ?ty ?boxPartial ?undef pt
  · constructor
    · intro h; simp [Ty.vars] at h
    · rintro ⟨_, _, _, hc, _, _⟩; cases hc
  · constructor
    · intro h; simp [Ty.vars] at h
    · rintro ⟨_, _, _, hc, _, _⟩; cases hc
  · intro mutable tgts
    constructor
    · intro h
      simp only [Ty.vars, List.mem_map] at h
      rcases h with ⟨tgt, htgt, hbase⟩
      exact ⟨mutable, tgts, tgt, PartialTyContains.here, htgt, hbase⟩
    · rintro ⟨m, targets, tgt, hc, htgt, hbase⟩
      cases hc
      simp only [Ty.vars, List.mem_map]
      exact ⟨tgt, htgt, hbase⟩
  · intro inner ih
    constructor
    · intro h
      simp only [Ty.vars] at h
      rcases ih.mp h with ⟨m, tgts, tgt, hc, htgt, hbase⟩
      exact ⟨m, tgts, tgt, PartialTyContains.tyBox hc, htgt, hbase⟩
    · rintro ⟨m, targets, tgt, hc, htgt, hbase⟩
      cases hc with
      | tyBox hinner =>
          simp only [Ty.vars]
          exact ih.mpr ⟨m, targets, tgt, hinner, htgt, hbase⟩
  · intro t ih
    simpa [PartialTy.vars] using ih
  · intro inner ih
    constructor
    · intro h
      simp only [PartialTy.vars] at h
      rcases ih.mp h with ⟨m, tgts, tgt, hc, htgt, hbase⟩
      exact ⟨m, tgts, tgt, PartialTyContains.box hc, htgt, hbase⟩
    · rintro ⟨m, targets, tgt, hc, htgt, hbase⟩
      cases hc with
      | box hinner =>
          simp only [PartialTy.vars]
          exact ih.mpr ⟨m, targets, tgt, hinner, htgt, hbase⟩
  · intro shape _ih
    constructor
    · intro h; simp [PartialTy.vars] at h
    · rintro ⟨_, _, _, hc, _, _⟩; cases hc

/-- Every variable of a union type comes from one of the two joined types. -/
theorem partialTyUnion_vars_subset {a b u : PartialTy} {v : Name} :
    PartialTyUnion a b u →
    v ∈ PartialTy.vars u →
    v ∈ PartialTy.vars a ∨ v ∈ PartialTy.vars b := by
  intro hunion hv
  rcases mem_partialTy_vars_iff.mp hv with
    ⟨mutable, targets, target, hcontains, htarget, hbase⟩
  rcases PartialTyUnion.contained_borrow_member hunion hcontains htarget with
    ⟨leftTargets, hcl, htl⟩ | ⟨rightTargets, hcr, htr⟩
  · exact Or.inl
      (mem_partialTy_vars_iff.mpr ⟨mutable, leftTargets, target, hcl, htl, hbase⟩)
  · exact Or.inr
      (mem_partialTy_vars_iff.mpr ⟨mutable, rightTargets, target, hcr, htr, hbase⟩)

/--
`lw_rust_followup` Proposition 2 (rank decrease).

In a linearizable environment with rank `φ`, every variable occurring in the
type of an lval has strictly smaller rank than the lval's base variable.  This
is the well-founded measure that justifies recursion over `LValTyping` (and
hence shape-determinism of borrow-target unions).
-/
theorem lvalTyping_vars_rank_lt {env : Env} {φ : Name → Nat}
    (hφ : ∀ x slot, env.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    (∀ {lv : LVal} {pt : PartialTy} {life : Lifetime},
      LValTyping env lv pt life →
      ∀ v, v ∈ PartialTy.vars pt → φ v < φ (LVal.base lv)) ∧
    (∀ {tgts : List LVal} {pt : PartialTy} {life : Lifetime},
      LValTargetsTyping env tgts pt life →
      ∀ v, v ∈ PartialTy.vars pt → ∃ t, t ∈ tgts ∧ φ v < φ (LVal.base t)) := by
  refine ⟨fun {lv pt life} htyping => ?_, fun {tgts pt life} htyping => ?_⟩
  · exact LValTyping.rec
      (motive_1 := fun lv pt _life _ =>
        ∀ v, v ∈ PartialTy.vars pt → φ v < φ (LVal.base lv))
      (motive_2 := fun tgts pt _life _ =>
        ∀ v, v ∈ PartialTy.vars pt → ∃ t, t ∈ tgts ∧ φ v < φ (LVal.base t))
      (fun {x slot} h v hv => hφ x slot h v hv)
      (fun {lv' inner _life} _htyping ih v hv => ih v hv)
      (fun {lv' mutable targets borrowLife targetLife targetTy} _hborrow _htargets
          ihBorrow ihTargets v hv => by
        rcases ihTargets v hv with ⟨t, ht, hvt⟩
        exact lt_trans hvt
          (ihBorrow (LVal.base t)
            (mem_partialTy_vars_iff.mpr
              ⟨mutable, targets, t, PartialTyContains.here, ht, rfl⟩)))
      (fun {target ty _life} _htarget ihTarget v hv =>
        ⟨target, by simp, ihTarget v hv⟩)
      (fun {target rest headTy headLife restLife _life restTy unionTy}
          _hhead _hrest hunion _hintersection ihHead ihRest v hv => by
        rcases partialTyUnion_vars_subset hunion hv with hh | hr
        · exact ⟨target, by simp, ihHead v hh⟩
        · rcases ihRest v hr with ⟨t, ht, hvt⟩
          exact ⟨t, List.mem_cons_of_mem _ ht, hvt⟩)
      htyping
  · exact LValTargetsTyping.rec
      (motive_1 := fun lv pt _life _ =>
        ∀ v, v ∈ PartialTy.vars pt → φ v < φ (LVal.base lv))
      (motive_2 := fun tgts pt _life _ =>
        ∀ v, v ∈ PartialTy.vars pt → ∃ t, t ∈ tgts ∧ φ v < φ (LVal.base t))
      (fun {x slot} h v hv => hφ x slot h v hv)
      (fun {lv' inner _life} _htyping ih v hv => ih v hv)
      (fun {lv' mutable targets borrowLife targetLife targetTy} _hborrow _htargets
          ihBorrow ihTargets v hv => by
        rcases ihTargets v hv with ⟨t, ht, hvt⟩
        exact lt_trans hvt
          (ihBorrow (LVal.base t)
            (mem_partialTy_vars_iff.mpr
              ⟨mutable, targets, t, PartialTyContains.here, ht, rfl⟩)))
      (fun {target ty _life} _htarget ihTarget v hv =>
        ⟨target, by simp, ihTarget v hv⟩)
      (fun {target rest headTy headLife restLife _life restTy unionTy}
          _hhead _hrest hunion _hintersection ihHead ihRest v hv => by
        rcases partialTyUnion_vars_subset hunion hv with hh | hr
        · exact ⟨target, by simp, ihHead v hh⟩
        · rcases ihRest v hr with ⟨t, ht, hvt⟩
          exact ⟨t, List.mem_cons_of_mem _ ht, hvt⟩)
      htyping

/-- Every variable occurring in a typed lval's type has a base slot that outlives
the lval's own base slot.  (`vars pt` are exactly the bases of the borrow targets
syntactically inside `pt`; each such target outlives its containing borrow's slot,
and that chains up the spine.)  Proved by *plain* mutual structural recursion —
the type's variables are structurally smaller, so no rank induction is needed:
`var` uses the contained-borrow invariant's base-outlives directly; `box` lifts
through the inner type; `deref`-borrow chains the targets-motive (each `v` is
below some target `s`) with the borrow-motive (`s` is below `bs`); the
target-list cases recurse through the union's variable split. -/
theorem lvalTyping_vars_base_le {e : Env} (hcont : ContainedBorrowsWellFormed e) :
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping e lv pt lf →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs →
      ∀ v, v ∈ PartialTy.vars pt →
        ∀ {vbs : EnvSlot}, e.slotAt v = some vbs → vbs.lifetime ≤ bs.lifetime := by
  intro lv pt lf htyping
  refine LValTyping.rec
    (motive_1 := fun lv pt _lf _ =>
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs →
      ∀ v, v ∈ PartialTy.vars pt →
        ∀ {vbs : EnvSlot}, e.slotAt v = some vbs → vbs.lifetime ≤ bs.lifetime)
    (motive_2 := fun tgts pt _lf _ =>
      ∀ v, v ∈ PartialTy.vars pt → ∀ {vbs : EnvSlot}, e.slotAt v = some vbs →
        ∃ s, s ∈ tgts ∧ ∃ sbs, e.slotAt (LVal.base s) = some sbs ∧
          vbs.lifetime ≤ sbs.lifetime)
    ?var ?box ?borrow ?singleton ?cons htyping
  case var =>
      intro x slot hslot bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs
      have hsb : slot = bs := Option.some.inj (hslot.symm.trans hbs)
      subst hsb
      obtain ⟨m, tgts, hcontains, tgt, htgt, hbasetgt⟩ :=
        partialTy_vars_mem_contains v hv
      have hbtw := hcont x slot m tgts hslot ⟨slot, hslot, hcontains⟩
      obtain ⟨tt, tlf, _htyp, _hle, tgtbs, htgtbs, htgtbsle⟩ := hbtw tgt htgt
      rw [hbasetgt] at htgtbs
      have hvbseq : vbs = tgtbs := Option.some.inj (hvbs.symm.trans htgtbs)
      subst hvbseq
      exact htgtbsle
  case box =>
      intro lv0 inner lifetime _hlv0 ih bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs
      exact ih hbs v (by simpa [PartialTy.vars] using hv) hvbs
  case borrow =>
      intro lv0 mutable targets borrowLife targetLife targetTy _hbor _htgts
        ihBorrow ihTargets bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs
      obtain ⟨s, hs, sbs, hsbs, hvsbs⟩ := ihTargets v hv hvbs
      have hsbase : LVal.base s ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
        mem_partialTy_vars_iff.mpr ⟨mutable, targets, s, PartialTyContains.here, hs, rfl⟩
      exact LifetimeOutlives.trans hvsbs (ihBorrow hbs (LVal.base s) hsbase hsbs)
  case singleton =>
      intro target ty lifetime htarget _ih v hv vbs hvbs
      obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists htarget
      exact ⟨target, by simp, tbs, htbs, _ih htbs v hv hvbs⟩
  case cons =>
      intro target rest headTy headLife restLife life restTy unionTy
        hhead _hrest hunion _hintersection ihHead ihRest v hv vbs hvbs
      rcases partialTyUnion_vars_subset hunion hv with hh | hr
      · obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists hhead
        exact ⟨target, by simp, tbs, htbs, ihHead htbs v hh hvbs⟩
      · obtain ⟨s, hs, sbs, hsbs, hvsbs⟩ := ihRest v hr hvbs
        exact ⟨s, List.mem_cons_of_mem _ hs, sbs, hsbs, hvsbs⟩

/-- **Rank-bounded** form of `lvalTyping_vars_base_le`: only the contained-borrow
invariant at slots of rank `< N` is needed to bound the variables of an lval of
base-rank `< N`.  (The spine vars share the base rank; the target vars are
strictly smaller by `lvalTyping_vars_rank_lt` — so every `hcontN` query stays
below `N`.)  This is what lets the join's `ContainedBorrows` be *bootstrapped* by
strong rank induction: at rank `n` the targets (rank `< n`) are bounded using only
the rank-`<n` invariant supplied by the induction hypothesis. -/
theorem lvalTyping_vars_base_le_bounded {e : Env} {φ : Name → Nat} (N : Nat)
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcontN : ∀ x slot mutable T, φ x < N → e.slotAt x = some slot →
        e ⊢ x ↝ Ty.borrow mutable T → BorrowTargetsWellFormedInSlot e slot.lifetime T) :
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping e lv pt lf → φ (LVal.base lv) < N →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs →
      ∀ v, v ∈ PartialTy.vars pt →
        ∀ {vbs : EnvSlot}, e.slotAt v = some vbs → vbs.lifetime ≤ bs.lifetime := by
  intro lv pt lf htyping
  refine LValTyping.rec
    (motive_1 := fun lv pt _lf _ =>
      φ (LVal.base lv) < N →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs →
      ∀ v, v ∈ PartialTy.vars pt →
        ∀ {vbs : EnvSlot}, e.slotAt v = some vbs → vbs.lifetime ≤ bs.lifetime)
    (motive_2 := fun tgts pt _lf _ =>
      (∀ s, s ∈ tgts → φ (LVal.base s) < N) →
      ∀ v, v ∈ PartialTy.vars pt → ∀ {vbs : EnvSlot}, e.slotAt v = some vbs →
        ∃ s, s ∈ tgts ∧ ∃ sbs, e.slotAt (LVal.base s) = some sbs ∧
          vbs.lifetime ≤ sbs.lifetime)
    ?var ?box ?borrow ?singleton ?cons htyping
  case var =>
      intro x slot hslot hxN bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs hxN
      have hsb : slot = bs := Option.some.inj (hslot.symm.trans hbs)
      subst hsb
      obtain ⟨m, tgts, hcontains, tgt, htgt, hbasetgt⟩ :=
        partialTy_vars_mem_contains v hv
      have hbtw := hcontN x slot m tgts hxN hslot ⟨slot, hslot, hcontains⟩
      obtain ⟨tt, tlf, _htyp, _hle, tgtbs, htgtbs, htgtbsle⟩ := hbtw tgt htgt
      rw [hbasetgt] at htgtbs
      have hvbseq : vbs = tgtbs := Option.some.inj (hvbs.symm.trans htgtbs)
      subst hvbseq
      exact htgtbsle
  case box =>
      intro lv0 inner lifetime _hlv0 ih hxN bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs hxN
      exact ih hxN hbs v (by simpa [PartialTy.vars] using hv) hvbs
  case borrow =>
      intro lv0 mutable targets borrowLife targetLife targetTy hbor _htgts
        ihBorrow ihTargets hxN bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs hxN
      have htgtsN : ∀ s, s ∈ targets → φ (LVal.base s) < N := by
        intro s hs
        have hsbase : LVal.base s ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr ⟨mutable, targets, s, PartialTyContains.here, hs, rfl⟩
        exact lt_trans ((lvalTyping_vars_rank_lt hφ).1 hbor _ hsbase) hxN
      obtain ⟨s, hs, sbs, hsbs, hvsbs⟩ := ihTargets htgtsN v hv hvbs
      have hsbase : LVal.base s ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
        mem_partialTy_vars_iff.mpr ⟨mutable, targets, s, PartialTyContains.here, hs, rfl⟩
      exact LifetimeOutlives.trans hvsbs (ihBorrow hxN hbs (LVal.base s) hsbase hsbs)
  case singleton =>
      intro target ty lifetime htarget _ih hsN v hv vbs hvbs
      obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists htarget
      exact ⟨target, by simp, tbs, htbs, _ih (hsN target (by simp)) htbs v hv hvbs⟩
  case cons =>
      intro target rest headTy headLife restLife life restTy unionTy
        hhead _hrest hunion _hintersection ihHead ihRest hsN v hv vbs hvbs
      rcases partialTyUnion_vars_subset hunion hv with hh | hr
      · obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists hhead
        exact ⟨target, by simp, tbs, htbs,
          ihHead (hsN target (by simp)) htbs v hh hvbs⟩
      · obtain ⟨s, hs, sbs, hsbs, hvsbs⟩ :=
          ihRest (fun s' hs' => hsN s' (List.mem_cons_of_mem _ hs')) v hr hvbs
        exact ⟨s, List.mem_cons_of_mem _ hs, sbs, hsbs, hvsbs⟩

/-- **Foundation stone of the lifetime bound.**  In a linearizable
(`hφ`), contained-borrow-well-formed (`hcont`) environment, every typed lval's
lifetime is bounded by its base slot's lifetime.  Proved by strong induction on
the base rank `φ`, structural on the lval: `var` is reflexive; `box` recurses
structurally; the `deref`-of-borrow case folds the per-target bound
(`lvalTargetsTyping_le_of_members`) where each target `t` (strictly smaller rank
via `lvalTyping_vars_rank_lt`) is bounded by `t`'s base slot (rank IH) and that
slot outlives `bs` (the contained-borrow invariant's base-outlives).  The
remaining *reborrow* sub-case (the borrow lies behind a deref, not slot-contained)
is the deeper φ-recursion — isolated here. -/
theorem lvalTyping_lifetime_le_base {e : Env} {φ : Name → Nat}
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcont : ContainedBorrowsWellFormed e) :
    ∀ (lv : LVal) {pt : PartialTy} {lf : Lifetime},
      LValTyping e lv pt lf →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs → lf ≤ bs.lifetime := by
  suffices h : ∀ (n : Nat) (lv : LVal), φ (LVal.base lv) = n →
      ∀ {pt lf}, LValTyping e lv pt lf →
        ∀ {bs}, e.slotAt (LVal.base lv) = some bs → lf ≤ bs.lifetime by
    intro lv pt lf htyping bs hbs
    exact h (φ (LVal.base lv)) lv rfl htyping hbs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase pt lf hp bs hbs
        cases hp with
        | var hslot =>
            rename_i slot
            simp only [LVal.base] at hbs
            have heq : slot = bs := Option.some.inj (hslot.symm.trans hbs)
            rw [heq]
            exact LifetimeOutlives.refl _
    | deref lv' ihStruct =>
        intro hbase pt lf hp bs hbs
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        have hbs' : e.slotAt (LVal.base lv') = some bs := by simpa [LVal.base] using hbs
        cases hp with
        | box hbox => exact ihStruct hbase' hbox hbs'
        | borrow hbor htgts =>
            rename_i mutb T blf
            refine lvalTargetsTyping_le_of_members htgts (fun t ht tt tlf htyp => ?_)
            have hvar : LVal.base t ∈ PartialTy.vars (.ty (.borrow mutb T)) :=
              mem_partialTy_vars_iff.mpr ⟨mutb, T, t, PartialTyContains.here, ht, rfl⟩
            have hrankt : φ (LVal.base t) < n := by
              have hlt := (lvalTyping_vars_rank_lt hφ).1 hbor _ hvar
              simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
            obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists htyp
            -- tlf ≤ tbs.lifetime by the rank IH; tbs.lifetime ≤ bs.lifetime since
            -- `base t` occurs in `lv'`'s borrow type (uniform — no contained/reborrow split)
            exact LifetimeOutlives.trans
              (ihRank _ hrankt t rfl htyp htbs)
              (lvalTyping_vars_base_le hcont hbor hbs' (LVal.base t) hvar htbs)

/-- **Rank-bounded** form of `lvalTyping_lifetime_le_base`: only the rank-`<N`
contained-borrow invariant is needed to bound the lifetime of an lval of base
rank `<N`.  This is the tool the join `ContainedBorrows` bootstrap applies to each
fan-out target (rank `<n`) using the strong-induction hypothesis (rank-`<n`
invariant), breaking the circularity of the unbounded foundation stone (which
needs `ContainedBorrows` of the env being established). -/
theorem lvalTyping_lifetime_le_base_bounded {e : Env} {φ : Name → Nat} (N : Nat)
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcontN : ∀ x slot mutable T, φ x < N → e.slotAt x = some slot →
        e ⊢ x ↝ Ty.borrow mutable T → BorrowTargetsWellFormedInSlot e slot.lifetime T) :
    ∀ (lv : LVal), φ (LVal.base lv) < N → ∀ {pt : PartialTy} {lf : Lifetime},
      LValTyping e lv pt lf →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs → lf ≤ bs.lifetime := by
  suffices h : ∀ (n : Nat) (lv : LVal),
      φ (LVal.base lv) = n → φ (LVal.base lv) < N →
      ∀ {pt lf}, LValTyping e lv pt lf →
        ∀ {bs}, e.slotAt (LVal.base lv) = some bs → lf ≤ bs.lifetime by
    intro lv hlvN pt lf htyping bs hbs
    exact h (φ (LVal.base lv)) lv rfl hlvN htyping hbs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase _hlvN pt lf hp bs hbs
        cases hp with
        | var hslot =>
            rename_i slot
            simp only [LVal.base] at hbs
            have heq : slot = bs := Option.some.inj (hslot.symm.trans hbs)
            rw [heq]; exact LifetimeOutlives.refl _
    | deref lv' ihStruct =>
        intro hbase hlvN pt lf hp bs hbs
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        have hlvN' : φ (LVal.base lv') < N := by simpa [LVal.base] using hlvN
        have hbs' : e.slotAt (LVal.base lv') = some bs := by simpa [LVal.base] using hbs
        cases hp with
        | box hbox => exact ihStruct hbase' hlvN' hbox hbs'
        | borrow hbor htgts =>
            rename_i mutb T blf
            refine lvalTargetsTyping_le_of_members htgts (fun t ht tt tlf htyp => ?_)
            have hvar : LVal.base t ∈ PartialTy.vars (.ty (.borrow mutb T)) :=
              mem_partialTy_vars_iff.mpr ⟨mutb, T, t, PartialTyContains.here, ht, rfl⟩
            have hrankt : φ (LVal.base t) < n := by
              have hlt := (lvalTyping_vars_rank_lt hφ).1 hbor _ hvar
              simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
            have hrankt' : φ (LVal.base t) < N := lt_trans hrankt (hbase' ▸ hlvN')
            obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists htyp
            exact LifetimeOutlives.trans
              (ihRank _ hrankt t rfl hrankt' htyp htbs)
              (lvalTyping_vars_base_le_bounded N hφ hcontN hbor hlvN'
                hbs' (LVal.base t) hvar htbs)

@[refl] theorem Ty.sameShape_refl (t : Ty) : Ty.sameShape t t := by
  refine Ty.rec (motive_1 := fun t => Ty.sameShape t t)
    (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · trivial
  · trivial
  · intro _ _; rfl
  · intro _ ih; exact ih
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial

@[refl] theorem PartialTy.sameShape_refl (pt : PartialTy) :
    PartialTy.sameShape pt pt := by
  refine PartialTy.rec (motive_1 := fun t => Ty.sameShape t t)
    (motive_2 := fun pt => PartialTy.sameShape pt pt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ pt
  · trivial
  · trivial
  · intro _ _; rfl
  · intro _ ih; exact ih
  · intro _ ih; exact ih
  · intro _ ih; exact ih
  · intro _ ih; exact ih

theorem Ty.sameShape_symm {a b : Ty} (h : Ty.sameShape a b) :
    Ty.sameShape b a := by
  have key : ∀ a b, Ty.sameShape a b → Ty.sameShape b a := by
    intro a
    refine Ty.rec (motive_1 := fun a => ∀ b, Ty.sameShape a b → Ty.sameShape b a)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b h; cases b <;> simp_all [Ty.sameShape]
    · intro b h; cases b <;> simp_all [Ty.sameShape]
    · intro _ _ b h; cases b <;> simp_all [Ty.sameShape]
    · intro _ ih b h
      cases b with
      | box t' => exact ih t' h
      | unit => simp [Ty.sameShape] at h
      | int => simp [Ty.sameShape] at h
      | borrow _ _ => simp [Ty.sameShape] at h
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b h

theorem PartialTy.sameShape_symm {a b : PartialTy}
    (h : PartialTy.sameShape a b) : PartialTy.sameShape b a := by
  cases a <;> cases b <;>
    simp_all [PartialTy.sameShape] <;>
    first
      | exact Ty.sameShape_symm (by assumption)
      | exact (PartialTy.sameShape_symm (by assumption))

theorem Ty.sameShape_trans {a b c : Ty}
    (h₁ : Ty.sameShape a b) (h₂ : Ty.sameShape b c) : Ty.sameShape a c := by
  have key : ∀ a b c, Ty.sameShape a b → Ty.sameShape b c → Ty.sameShape a c := by
    intro a
    refine Ty.rec
      (motive_1 := fun a => ∀ b c, Ty.sameShape a b → Ty.sameShape b c →
        Ty.sameShape a c)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.sameShape]
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.sameShape]
    · intro _ _ b c h1 h2; cases b <;> cases c <;> simp_all [Ty.sameShape]
    · intro _ ih b c h1 h2
      cases b with
      | box tb =>
          cases c with
          | box tc => exact ih tb tc h1 h2
          | unit => simp [Ty.sameShape] at h2
          | int => simp [Ty.sameShape] at h2
          | borrow _ _ => simp [Ty.sameShape] at h2
      | unit => simp [Ty.sameShape] at h1
      | int => simp [Ty.sameShape] at h1
      | borrow _ _ => simp [Ty.sameShape] at h1
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b c h₁ h₂

theorem PartialTy.sameShape_trans {a b c : PartialTy}
    (h₁ : PartialTy.sameShape a b) (h₂ : PartialTy.sameShape b c) :
    PartialTy.sameShape a c := by
  cases a <;> cases b <;> cases c <;>
    simp_all [PartialTy.sameShape] <;>
    first
      | exact Ty.sameShape_trans (by assumption) (by assumption)
      | exact PartialTy.sameShape_trans (by assumption) (by assumption)

/-- Forward shape preservation across an environment transformation: every slot
present in `result` comes from a `sameShape` slot of `source`.  This is the
shape-stability invariant tracked through `EnvWrite`/`UpdateAtPath`/
`WriteBorrowTargets` (the Appendix 9.6 shape fragment). -/
def EnvShapePreserved (source result : Env) : Prop :=
  ∀ x resultSlot, result.slotAt x = some resultSlot →
    ∃ sourceSlot, source.slotAt x = some sourceSlot ∧
      PartialTy.sameShape sourceSlot.ty resultSlot.ty

@[refl] theorem EnvShapePreserved.refl (env : Env) :
    EnvShapePreserved env env := by
  intro x slot hslot
  exact ⟨slot, hslot, PartialTy.sameShape_refl _⟩

theorem EnvShapePreserved.trans {first second third : Env} :
    EnvShapePreserved first second →
    EnvShapePreserved second third →
    EnvShapePreserved first third := by
  intro h12 h23 x slot hslot
  rcases h23 x slot hslot with ⟨secondSlot, hsecondSlot, hshape23⟩
  rcases h12 x secondSlot hsecondSlot with ⟨firstSlot, hfirstSlot, hshape12⟩
  exact ⟨firstSlot, hfirstSlot, PartialTy.sameShape_trans hshape12 hshape23⟩

/-- If two branch environments both preserve slot shape from a common source,
then any slot present in both branches has the same shape in both branches. -/
theorem EnvShapePreserved.branch_sameShape {source left right : Env} :
    EnvShapePreserved source left →
    EnvShapePreserved source right →
    ∀ x leftSlot rightSlot,
      left.slotAt x = some leftSlot →
      right.slotAt x = some rightSlot →
      PartialTy.sameShape leftSlot.ty rightSlot.ty := by
  intro hleft hright x leftSlot rightSlot hleftSlot hrightSlot
  rcases hleft x leftSlot hleftSlot with
    ⟨sourceLeftSlot, hsourceLeftSlot, hshapeLeft⟩
  rcases hright x rightSlot hrightSlot with
    ⟨sourceRightSlot, hsourceRightSlot, hshapeRight⟩
  have hsourceEq : sourceLeftSlot = sourceRightSlot :=
    Option.some.inj (hsourceLeftSlot.symm.trans hsourceRightSlot)
  subst hsourceEq
  exact PartialTy.sameShape_trans (PartialTy.sameShape_symm hshapeLeft) hshapeRight

theorem EnvShapePreserved.update_from_source_slot {source middle : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvShapePreserved source middle →
    source.slotAt x = some slot →
    PartialTy.sameShape slot.ty newTy →
    EnvShapePreserved source (middle.update x { slot with ty := newTy }) := by
  intro hpres hslot hshape y resultSlot hresultSlot
  by_cases hy : y = x
  · subst hy
    have hresultSlotEq : resultSlot = { slot with ty := newTy } := by
      have h : { slot with ty := newTy } = resultSlot := by
        simpa [Env.update] using hresultSlot
      exact h.symm
    subst hresultSlotEq
    exact ⟨slot, hslot, hshape⟩
  · have hmiddleSlot : middle.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresultSlot
    exact hpres y resultSlot hmiddleSlot

/-- Leaf shape-compatibility premise for a `Definition 3.23` write of `ty`
through `path` into `oldTy`.  Stated as an inductive (so the borrow fan-out case
may reference the relation at a *longer* path — through `prependPath` — without a
structural-termination obstruction).  At the leaf the old type must be shape
compatible with the written type; `box` peels one layer; `borrow` requires each
target's onward write to be leaf-compatible. -/
inductive WriteShapeCompat (env : Env) : List Unit → PartialTy → Ty → Prop where
  | leaf {oldTy : PartialTy} {ty : Ty} :
      ShapeCompatible env oldTy (.ty ty) →
      WriteShapeCompat env [] oldTy ty
  | box {path : List Unit} {inner : PartialTy} {ty : Ty} :
      WriteShapeCompat env path inner ty →
      WriteShapeCompat env (() :: path) (.box inner) ty
  | borrow {path : List Unit} {targets : List LVal} {ty : Ty} :
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteShapeCompat env (LVal.path (prependPath path t)) tslot.ty ty) →
      WriteShapeCompat env (() :: path) (.ty (.borrow true targets)) ty

@[refl] theorem Ty.eqv_refl (t : Ty) : Ty.eqv t t := by
  refine Ty.rec (motive_1 := fun t => Ty.eqv t t)
    (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · trivial
  · trivial
  · intro _ _; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  · intro _ ih; exact ih
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial

theorem Ty.sameShape_of_eqv {a b : Ty} (h : Ty.eqv a b) : Ty.sameShape a b := by
  have key : ∀ a b, Ty.eqv a b → Ty.sameShape a b := by
    intro a
    refine Ty.rec (motive_1 := fun a => ∀ b, Ty.eqv a b → Ty.sameShape a b)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b h; cases b <;> simp_all [Ty.eqv, Ty.sameShape]
    · intro b h; cases b <;> simp_all [Ty.eqv, Ty.sameShape]
    · intro _ _ b h; cases b <;> simp_all [Ty.eqv, Ty.sameShape]
    · intro _ ih b h
      cases b with
      | box t' => exact ih t' h
      | unit => simp [Ty.eqv] at h
      | int => simp [Ty.eqv] at h
      | borrow _ _ => simp [Ty.eqv] at h
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b h

theorem Ty.eqv_symm {a b : Ty} (h : Ty.eqv a b) : Ty.eqv b a := by
  have key : ∀ a b, Ty.eqv a b → Ty.eqv b a := by
    intro a
    refine Ty.rec (motive_1 := fun a => ∀ b, Ty.eqv a b → Ty.eqv b a)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b h; cases b <;> simp_all [Ty.eqv]
    · intro b h; cases b <;> simp_all [Ty.eqv]
    · intro ma ta b h
      cases b with
      | borrow mb tb =>
          simp only [Ty.eqv] at h ⊢
          exact ⟨h.1.symm, h.2.2, h.2.1⟩
      | unit => simp [Ty.eqv] at h
      | int => simp [Ty.eqv] at h
      | box _ => simp [Ty.eqv] at h
    · intro _ ih b h
      cases b with
      | box t' => exact ih t' h
      | unit => simp [Ty.eqv] at h
      | int => simp [Ty.eqv] at h
      | borrow _ _ => simp [Ty.eqv] at h
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b h

theorem Ty.eqv_trans {a b c : Ty} (h₁ : Ty.eqv a b) (h₂ : Ty.eqv b c) :
    Ty.eqv a c := by
  have key : ∀ a b c, Ty.eqv a b → Ty.eqv b c → Ty.eqv a c := by
    intro a
    refine Ty.rec
      (motive_1 := fun a => ∀ b c, Ty.eqv a b → Ty.eqv b c → Ty.eqv a c)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.eqv]
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.eqv]
    · intro ma ta b c h1 h2
      cases b with
      | borrow mb tb =>
          cases c with
          | borrow mc tc =>
              simp only [Ty.eqv] at h1 h2 ⊢
              exact ⟨h1.1.trans h2.1, fun x hx => h2.2.1 (h1.2.1 hx),
                fun x hx => h1.2.2 (h2.2.2 hx)⟩
          | unit => simp [Ty.eqv] at h2
          | int => simp [Ty.eqv] at h2
          | box _ => simp [Ty.eqv] at h2
      | unit => simp [Ty.eqv] at h1
      | int => simp [Ty.eqv] at h1
      | box _ => simp [Ty.eqv] at h1
    · intro _ ih b c h1 h2
      cases b with
      | box tb =>
          cases c with
          | box tc => exact ih tb tc h1 h2
          | unit => simp [Ty.eqv] at h2
          | int => simp [Ty.eqv] at h2
          | borrow _ _ => simp [Ty.eqv] at h2
      | unit => simp [Ty.eqv] at h1
      | int => simp [Ty.eqv] at h1
      | borrow _ _ => simp [Ty.eqv] at h1
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b c h₁ h₂

@[refl] theorem PartialTy.eqv_refl (pt : PartialTy) : PartialTy.eqv pt pt := by
  refine PartialTy.rec (motive_1 := fun t => Ty.eqv t t)
    (motive_2 := fun pt => PartialTy.eqv pt pt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ pt
  · trivial
  · trivial
  · intro _ _; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  · intro _ ih; exact ih
  · intro _ ih; exact ih
  · intro _ ih; exact ih
  · intro _ ih; exact ih

theorem PartialTy.sameShape_of_eqv {a b : PartialTy} (h : PartialTy.eqv a b) :
    PartialTy.sameShape a b := by
  cases a <;> cases b <;>
    first
      | (simp only [PartialTy.eqv] at h; simp only [PartialTy.sameShape];
         exact Ty.sameShape_of_eqv h)
      | (simp only [PartialTy.eqv] at h; simp only [PartialTy.sameShape];
         exact PartialTy.sameShape_of_eqv h)
      | (simp [PartialTy.eqv] at h)

/-- Shape compatibility of full types implies structural same-shape. -/
theorem PartialTy.sameShape_of_shapeCompatible {env : Env} {a b : Ty} :
    ShapeCompatible env (.ty a) (.ty b) → PartialTy.sameShape (.ty a) (.ty b) := by
  intro h
  cases h with
  | unit => simp [PartialTy.sameShape, Ty.sameShape]
  | int => simp [PartialTy.sameShape, Ty.sameShape]
  | borrow _ _ _ => simp [PartialTy.sameShape, Ty.sameShape]

/-- The union target list of two same-`mutable` borrows is subset-equivalent to
the append of the operand target lists (`U` is the LUB, so `U ⊆ L ++ R`, while
`L, R ⊆ U` since `U` is an upper bound). -/
theorem partialTyUnion_borrow_targetsEquiv {m : Bool} {L R U : List LVal} :
    PartialTyUnion (.ty (.borrow m L)) (.ty (.borrow m R)) (.ty (.borrow m U)) →
    U ⊆ L ++ R ∧ (L ++ R) ⊆ U := by
  intro hunion
  refine ⟨?_, ?_⟩
  · have hmem : (PartialTy.ty (.borrow m (L ++ R))) ∈
        upperBounds ({PartialTy.ty (.borrow m L),
          PartialTy.ty (.borrow m R)} : Set PartialTy) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact PartialTyStrengthens.borrow (List.subset_append_left L R)
      · exact PartialTyStrengthens.borrow (List.subset_append_right L R)
    exact PartialTyStrengthens.borrow_subset (hunion.2 hmem)
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact PartialTyStrengthens.borrow_subset
        (PartialTyUnion.left_strengthens hunion) h
    · exact PartialTyStrengthens.borrow_subset
        (PartialTyUnion.right_strengthens hunion) h

/-- The union operation respects `eqv`: joining `eqv`-related heads and rests
yields `eqv`-related unions. -/
theorem partialTyUnion_eqv {headA restA tyA headB restB tyB : Ty}
    (hhead : Ty.eqv headA headB) (hrest : Ty.eqv restA restB)
    (hunionA : PartialTyUnion (.ty headA) (.ty restA) (.ty tyA))
    (hunionB : PartialTyUnion (.ty headB) (.ty restB) (.ty tyB)) :
    Ty.eqv tyA tyB := by
  cases headA with
  | unit =>
      have hb : headB = .unit := by cases headB <;> simp_all [Ty.eqv]
      subst hb
      have htyA : tyA = .unit :=
        PartialTyStrengthens.from_unit_inv (PartialTyUnion.left_strengthens hunionA)
      have htyB : tyB = .unit :=
        PartialTyStrengthens.from_unit_inv (PartialTyUnion.left_strengthens hunionB)
      subst htyA; subst htyB; trivial
  | int =>
      have hb : headB = .int := by cases headB <;> simp_all [Ty.eqv]
      subst hb
      have htyA : tyA = .int :=
        PartialTyStrengthens.from_int_inv (PartialTyUnion.left_strengthens hunionA)
      have htyB : tyB = .int :=
        PartialTyStrengthens.from_int_inv (PartialTyUnion.left_strengthens hunionB)
      subst htyA; subst htyB; trivial
  | box hA =>
      cases headB with
      | box hB =>
          have htyA : tyA = .box hA :=
            PartialTyStrengthens.from_box_ty_inv
              (PartialTyUnion.left_strengthens hunionA)
          have htyB : tyB = .box hB :=
            PartialTyStrengthens.from_box_ty_inv
              (PartialTyUnion.left_strengthens hunionB)
          subst htyA; subst htyB
          simpa [Ty.eqv] using hhead
      | unit => simp [Ty.eqv] at hhead
      | int => simp [Ty.eqv] at hhead
      | borrow _ _ => simp [Ty.eqv] at hhead
  | borrow mA tA =>
      cases headB with
      | borrow mB tB =>
          simp only [Ty.eqv] at hhead
          obtain ⟨rfl, htAB, htBA⟩ := hhead
          rcases PartialTyStrengthens.from_borrow_inv
            (PartialTyUnion.left_strengthens hunionA) with ⟨UA, htyAeq, _⟩
          subst htyAeq
          rcases PartialTyStrengthens.to_borrow_inv
            (PartialTyUnion.right_strengthens hunionA) with ⟨rA, hrestAeq, _⟩
          subst hrestAeq
          rcases partialTyUnion_borrow_targetsEquiv hunionA with ⟨hUA_app, _⟩
          rcases PartialTyStrengthens.from_borrow_inv
            (PartialTyUnion.left_strengthens hunionB) with ⟨UB, htyBeq, _⟩
          subst htyBeq
          rcases PartialTyStrengthens.to_borrow_inv
            (PartialTyUnion.right_strengthens hunionB) with ⟨rB, hrestBeq, _⟩
          subst hrestBeq
          rcases partialTyUnion_borrow_targetsEquiv hunionB with ⟨hUB_app, happ_UB⟩
          rcases partialTyUnion_borrow_targetsEquiv hunionA with ⟨_, happ_UA⟩
          simp only [Ty.eqv] at hrest
          obtain ⟨_, hrAB, hrBA⟩ := hrest
          refine ⟨rfl, ?_, ?_⟩
          · intro x hx
            rcases List.mem_append.mp (hUA_app hx) with h | h
            · exact happ_UB (List.mem_append_left _ (htAB h))
            · exact happ_UB (List.mem_append_right _ (hrAB h))
          · intro x hx
            rcases List.mem_append.mp (hUB_app hx) with h | h
            · exact happ_UA (List.mem_append_left _ (htBA h))
            · exact happ_UA (List.mem_append_right _ (hrBA h))
      | unit => simp [Ty.eqv] at hhead
      | int => simp [Ty.eqv] at hhead
      | box _ => simp [Ty.eqv] at hhead

/-- Strengthening within full types preserves shape: the strengthening rules
that keep a `.ty` a `.ty` (W-Reflex, W-Bor) never change the head constructor. -/
theorem ty_sameShape_of_strengthens {a b : Ty}
    (h : PartialTyStrengthens (.ty a) (.ty b)) : Ty.sameShape a b := by
  cases h with
  | reflex => exact Ty.sameShape_refl _
  | borrow _ => simp [Ty.sameShape]

/-- W-Weak preserves shape: if the old slot type is shape compatible with the
written full type, their join has the same shape as the old type.  The
`ShapeCompatible` premise is what excludes the degenerate `box`/`undef` cases (a
box can never be shape compatible with a full non-box `.ty`), and is exactly the
premise the assignment rules already carry. -/
theorem partialTyJoin_sameShape {env : Env} {old joined : PartialTy} {ty : Ty}
    (hshape : ShapeCompatible env old (.ty ty))
    (hjoin : PartialTyJoin old (.ty ty) joined) :
    PartialTy.sameShape old joined := by
  have hleft : PartialTyStrengthens old joined :=
    PartialTyUnion.left_strengthens hjoin
  cases hshape with
  | unit =>
      have hbound : joined ≤ (PartialTy.ty .unit) :=
        hjoin.2 (by intro p hp; simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff] at hp; rcases hp with rfl | rfl <;> rfl)
      cases joined with
      | ty u => have := PartialTyStrengthens.to_unit_inv hbound; subst this; trivial
      | box _ => cases hbound
      | undef _ => cases hbound
  | int =>
      have hbound : joined ≤ (PartialTy.ty .int) :=
        hjoin.2 (by intro p hp; simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff] at hp; rcases hp with rfl | rfl <;> rfl)
      cases joined with
      | ty u => have := PartialTyStrengthens.to_int_inv hbound; subst this; trivial
      | box _ => cases hbound
      | undef _ => cases hbound
  | borrow hL hR hpointee =>
      rename_i mutable leftTargets rightTargets leftTy rightTy
      have hbound : joined ≤
          (PartialTy.ty (.borrow mutable (leftTargets ++ rightTargets))) :=
        hjoin.2 (by
          intro p hp
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
          rcases hp with rfl | rfl
          · exact PartialTyStrengthens.borrow (by
              intro t ht; exact List.mem_append_left _ ht)
          · exact PartialTyStrengthens.borrow (by
              intro t ht; exact List.mem_append_right _ ht))
      cases joined with
      | ty u =>
          rcases PartialTyStrengthens.to_borrow_inv hbound with ⟨st, hu, _⟩
          subst hu; rfl
      | box _ => cases hbound
      | undef _ => cases hbound
  | undefLeft hinner =>
      cases hleft with
      | reflex => exact PartialTy.sameShape_refl _
      | undefLeft h => exact ty_sameShape_of_strengthens h

/-- The union of `.ty head` with a full `.ty rest` has the same shape as `head`
(the right operand must match `head`'s shape for the join to exist). -/
theorem partialTyUnion_ty_left_sameShape {head rest union : Ty} :
    PartialTyUnion (.ty head) (.ty rest) (.ty union) →
    Ty.sameShape union head := by
  intro hunion
  have hstr : PartialTyStrengthens (.ty head) (.ty union) :=
    PartialTyUnion.left_strengthens hunion
  cases head with
  | unit =>
      have : union = .unit := PartialTyStrengthens.from_unit_inv hstr
      subst this; simp [Ty.sameShape]
  | int =>
      have : union = .int := PartialTyStrengthens.from_int_inv hstr
      subst this; simp [Ty.sameShape]
  | borrow m tgts =>
      rcases PartialTyStrengthens.from_borrow_inv hstr with ⟨ut, hu, _⟩
      subst hu; simp [Ty.sameShape]
  | box t =>
      have : union = .box t := PartialTyStrengthens.from_box_ty_inv hstr
      subst this
      simpa [Ty.sameShape] using Ty.sameShape_refl t

/-- **Unconditional left-shape preservation for a `.ty`-left join.**  When the
left operand is a *defined* type `.ty a` (not `.undef`), the join with any
`.ty rhsTy` preserves its shape — no `ShapeCompatible` premise needed.  The
`.undef`-left case is genuinely excluded: re-initialisation `.undef int ⊔ .ty int
= .ty int` changes shape, which is why `partialTyJoin_sameShape` carries the
`ShapeCompatible` hypothesis.  For positive-rank writes through *initialised*
borrow targets the leaf is always `.ty`, so this is the form the fan-out needs. -/
theorem partialTyJoin_ty_left_sameShape {a rhsTy : Ty} {joined : PartialTy} :
    PartialTyJoin (.ty a) (.ty rhsTy) joined →
    PartialTy.sameShape (.ty a) joined := by
  intro hjoin
  have ha : PartialTyStrengthens (.ty a) joined :=
    PartialTyUnion.left_strengthens hjoin
  have hr : PartialTyStrengthens (.ty rhsTy) joined := by
    have := hjoin.1 (show (.ty rhsTy : PartialTy) ∈
      ({.ty a, .ty rhsTy} : Set PartialTy) by simp)
    simpa using this
  cases joined with
  | box j => exact absurd ha (PartialTyStrengthens.not_ty_to_box)
  | ty u =>
      exact Ty.sameShape_symm (partialTyUnion_ty_left_sameShape hjoin)
  | undef u =>
      exfalso
      have hau : PartialTyStrengthens (.ty a) (.ty u) :=
        PartialTyStrengthens.ty_to_undef_inv ha
      have hru : PartialTyStrengthens (.ty rhsTy) (.ty u) :=
        PartialTyStrengthens.ty_to_undef_inv hr
      have hub : (.ty u : PartialTy) ∈
          upperBounds ({.ty a, .ty rhsTy} : Set PartialTy) := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hau
        · exact hru
      exact PartialTyStrengthens.not_undef_to_ty (hjoin.2 hub)

/-- If two `sameShape` partial types have a union, the union has that same shape.
(The `sameShape a b` premise rules out the degenerate `.ty ⊔ .undef` join that
would otherwise change the shape.) -/
theorem partialTyUnion_sameShape_of_sameShape {a b c : PartialTy}
    (hunion : PartialTyUnion a b c) (hab : PartialTy.sameShape a b) :
    PartialTy.sameShape a c := by
  have key : ∀ (a : PartialTy),
      ∀ b c, PartialTyUnion a b c → PartialTy.sameShape a b →
        PartialTy.sameShape a c := by
    intro a
    refine PartialTy.rec
      (motive_1 := fun _ => True)
      (motive_2 := fun a => ∀ b c, PartialTyUnion a b c →
        PartialTy.sameShape a b → PartialTy.sameShape a c)
      (by trivial) (by trivial) (by intro _ _; trivial) (by intro _ _; trivial)
      ?tyCase ?boxCase ?undefCase a
    · intro au _ b c hunion hab
      cases b with
      | ty bu =>
          rcases PartialTyUnion.ty_ty_full hunion with ⟨cu, hc⟩
          subst hc
          exact Ty.sameShape_symm (partialTyUnion_ty_left_sameShape hunion)
      | box _ => simp [PartialTy.sameShape] at hab
      | undef _ => simp [PartialTy.sameShape] at hab
    · intro ap ihBox b c hunion hab
      cases b with
      | box bp =>
          rcases PartialTyUnion.box_box_shape hunion with ⟨cp, hc⟩
          subst hc
          exact ihBox bp cp (PartialTyUnion.box_inv hunion) hab
      | ty _ => simp [PartialTy.sameShape] at hab
      | undef _ => simp [PartialTy.sameShape] at hab
    · intro au _ b c hunion hab
      cases b with
      | undef bu =>
          have hleft := PartialTyUnion.left_strengthens hunion
          cases hleft with
          | reflex => exact PartialTy.sameShape_refl _
          | undefLeft h => exact ty_sameShape_of_strengthens h
      | ty _ => simp [PartialTy.sameShape] at hab
      | box _ => simp [PartialTy.sameShape] at hab
  exact key a b c hunion hab

/-- The union type of a (non-empty) target list has the shape of any one of its
members' types; combined with member determinism this fixes the union shape. -/
theorem lvalTargetsTyping_unionTy_sameShape_head {env : Env}
    {tgts : List LVal} {head : LVal} {rest : List LVal}
    {u headTy : Ty} {lu lhead : Lifetime} :
    tgts = head :: rest →
    LValTargetsTyping env tgts (.ty u) lu →
    LValTyping env head (.ty headTy) lhead →
    (∀ ma mb lma lmb,
      LValTyping env head (.ty ma) lma → LValTyping env head (.ty mb) lmb →
      Ty.sameShape ma mb) →
    Ty.sameShape u headTy := by
  intro htgts htyping hhead hdet
  cases htyping with
  | singleton hfirst =>
      -- tgts = [head], u = first's type
      simp only [List.cons.injEq] at htgts
      obtain ⟨rfl, _⟩ := htgts
      exact hdet _ _ _ _ hfirst hhead
  | cons hheadA hrestA hunionA hintA =>
      rename_i target rest' headTyA headLifeA restLifeA restTyA
      simp only [List.cons.injEq] at htgts
      obtain ⟨rfl, _⟩ := htgts
      -- u is the union of headTyA and restTyA; its shape = headTyA's = headTy's
      have huShapeHeadA : Ty.sameShape u headTyA := by
        rcases LValTargetsTyping.output_full hrestA with ⟨restTyVal, hrestFull⟩
        subst hrestFull
        exact partialTyUnion_ty_left_sameShape hunionA
      have hheadSame : Ty.sameShape headTyA headTy := hdet _ _ _ _ hheadA hhead
      exact Ty.sameShape_trans huShapeHeadA hheadSame

/-- Two target-list typings of the *same* list have same-shaped union types,
given per-member shape determinism. (The union shape is fixed by any member.) -/
theorem lvalTargetsTyping_sameList_sameShape {env : Env} {tgts : List LVal}
    {tyA tyB : Ty} {lA lB : Lifetime}
    (hdet : ∀ m, m ∈ tgts → ∀ ma mb lma lmb,
      LValTyping env m (.ty ma) lma → LValTyping env m (.ty mb) lmb →
      Ty.sameShape ma mb)
    (htA : LValTargetsTyping env tgts (.ty tyA) lA)
    (htB : LValTargetsTyping env tgts (.ty tyB) lB) :
    Ty.sameShape tyA tyB := by
  cases htA with
  | singleton hA =>
      cases htB with
      | singleton hB =>
          rename_i target
          exact hdet target (by simp) _ _ _ _ hA hB
      | cons _ hrB _ _ => cases hrB
  | cons hhA hrA huA hiA =>
      cases htB with
      | singleton _ => cases hrA
      | cons hhB hrB huB hiB =>
          rename_i target rest headTyA _ _ restTyA headTyB _ _ restTyB
          rcases LValTargetsTyping.output_full hrA with ⟨rA, hrAfull⟩
          rcases LValTargetsTyping.output_full hrB with ⟨rB, hrBfull⟩
          subst hrAfull; subst hrBfull
          have hA : Ty.sameShape tyA headTyA :=
            partialTyUnion_ty_left_sameShape huA
          have hB : Ty.sameShape tyB headTyB :=
            partialTyUnion_ty_left_sameShape huB
          have hheads : Ty.sameShape headTyA headTyB :=
            hdet target (by simp) _ _ _ _ hhA hhB
          exact Ty.sameShape_trans hA
            (Ty.sameShape_trans hheads (Ty.sameShape_symm hB))

/-- `eqv` version of `lvalTargetsTyping_sameList_sameShape`: two target-list
typings of the same list have `eqv` union types (so borrow target lists are
subset-equivalent), given per-member `eqv` determinism. -/
theorem lvalTargetsTyping_sameList_eqv {env : Env} :
    ∀ (tgts : List LVal) {tyA tyB : Ty} {lA lB : Lifetime},
    (∀ m, m ∈ tgts → ∀ ma mb lma lmb,
      LValTyping env m (.ty ma) lma → LValTyping env m (.ty mb) lmb →
      Ty.eqv ma mb) →
    LValTargetsTyping env tgts (.ty tyA) lA →
    LValTargetsTyping env tgts (.ty tyB) lB →
    Ty.eqv tyA tyB := by
  intro tgts
  induction tgts with
  | nil => intro tyA tyB lA lB _ htA _; cases htA
  | cons head tail ih =>
      intro tyA tyB lA lB hdet htA htB
      cases htA with
      | singleton hA =>
          cases htB with
          | singleton hB => exact hdet head (by simp) _ _ _ _ hA hB
          | cons _ hrB _ _ => cases hrB
      | cons hhA hrA huA hiA =>
          cases htB with
          | singleton _ => cases hrA
          | cons hhB hrB huB hiB =>
              rcases LValTargetsTyping.output_full hrA with ⟨rTyA, hrAfull⟩
              rcases LValTargetsTyping.output_full hrB with ⟨rTyB, hrBfull⟩
              subst hrAfull; subst hrBfull
              have hheadEqv := hdet head (by simp) _ _ _ _ hhA hhB
              have hrestEqv :=
                ih (fun m hm => hdet m (List.mem_cons_of_mem head hm)) hrA hrB
              exact partialTyUnion_eqv hheadEqv hrestEqv huA huB

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

/-- A target of the union borrow comes from some member's borrow targets. -/
theorem lvalTargetsTyping_borrowTargets_mem {env : Env} :
    ∀ {tgts : List LVal} {m : Bool} {U : List LVal} {lu : Lifetime},
    LValTargetsTyping env tgts (.ty (.borrow m U)) lu →
    ∀ x, x ∈ U →
      ∃ t, t ∈ tgts ∧ ∃ tt lt,
        LValTyping env t (.ty (.borrow m tt)) lt ∧ x ∈ tt := by
  intro tgts
  induction tgts with
  | nil => intro m U lu ht; cases ht
  | cons head tail ih =>
      intro m U lu ht x hx
      cases ht with
      | singleton hfirst =>
          exact ⟨head, by simp, U, _, hfirst, hx⟩
      | cons hhA hrA huA hiA =>
          rcases LValTargetsTyping.output_full hrA with ⟨rTy, hrFull⟩
          subst hrFull
          rcases PartialTyStrengthens.to_borrow_inv
            (PartialTyUnion.left_strengthens huA) with ⟨headTgts, hheadEq, _⟩
          subst hheadEq
          rcases PartialTyStrengthens.to_borrow_inv
            (PartialTyUnion.right_strengthens huA) with ⟨restTgts, hrestEq, _⟩
          subst hrestEq
          rcases partialTyUnion_borrow_targetsEquiv huA with ⟨hU_app, _⟩
          rcases List.mem_append.mp (hU_app hx) with h | h
          · exact ⟨head, by simp, headTgts, _, hhA, h⟩
          · rcases ih hrA x h with ⟨t, ht, tt, lt, htty, hxtt⟩
            exact ⟨t, List.mem_cons_of_mem head ht, tt, lt, htty, hxtt⟩

/-- Two target-list typings of subset-equivalent lists have `eqv` union types.
Generalises `lvalTargetsTyping_sameList_eqv` to lists with the same member set,
which is what relates reborrow chains (whose target lists are subset-equivalent
LUB witnesses). -/
theorem lvalTargetsTyping_subsetEquiv_eqv {env : Env}
    {tgtsA tgtsB : List LVal} {tyA tyB : Ty} {lA lB : Lifetime}
    (hAB : tgtsA ⊆ tgtsB) (hBA : tgtsB ⊆ tgtsA)
    (hdet : ∀ m, m ∈ tgtsA ++ tgtsB → ∀ ma mb lma lmb,
      LValTyping env m (.ty ma) lma → LValTyping env m (.ty mb) lmb → Ty.eqv ma mb)
    (htA : LValTargetsTyping env tgtsA (.ty tyA) lA)
    (htB : LValTargetsTyping env tgtsB (.ty tyB) lB) :
    Ty.eqv tyA tyB := by
  obtain ⟨h, hhmem⟩ : ∃ h, h ∈ tgtsA := by
    cases htA with
    | singleton _ => exact ⟨_, List.mem_cons_self⟩
    | cons _ _ _ _ => exact ⟨_, List.mem_cons_self⟩
  obtain ⟨hAty, hAlt, hAty_typing, hAty_le⟩ :=
    lvalTargetsTyping_member_strengthens htA h hhmem
  obtain ⟨hBty, hBlt, hBty_typing, hBty_le⟩ :=
    lvalTargetsTyping_member_strengthens htB h (hAB hhmem)
  have hh_eqv : Ty.eqv hAty hBty :=
    hdet h (List.mem_append_left _ hhmem) _ _ _ _ hAty_typing hBty_typing
  cases tyA with
  | unit =>
      have hAu : hAty = .unit := PartialTyStrengthens.to_unit_inv hAty_le
      subst hAu
      have hBu : hBty = .unit := by cases hBty <;> simp_all [Ty.eqv]
      subst hBu
      have : tyB = .unit := PartialTyStrengthens.from_unit_inv hBty_le
      subst this; trivial
  | int =>
      have hAu : hAty = .int := PartialTyStrengthens.to_int_inv hAty_le
      subst hAu
      have hBu : hBty = .int := by cases hBty <;> simp_all [Ty.eqv]
      subst hBu
      have : tyB = .int := PartialTyStrengthens.from_int_inv hBty_le
      subst this; trivial
  | box cA =>
      have hAbox : hAty = .box cA := by cases hAty_le; rfl
      subst hAbox
      have hBbox : ∃ cB, hBty = .box cB := by cases hBty <;> simp_all [Ty.eqv]
      obtain ⟨cB, hBeq⟩ := hBbox
      subst hBeq
      have : tyB = .box cB :=
        PartialTyStrengthens.from_box_ty_inv hBty_le
      subst this
      exact hh_eqv
  | borrow m UA =>
      rcases PartialTyStrengthens.to_borrow_inv hAty_le with ⟨hAtt, hAtyEq, _⟩
      subst hAtyEq
      cases hBty with
      | borrow mB hBtt =>
          simp only [Ty.eqv] at hh_eqv
          obtain ⟨rfl, _, _⟩ := hh_eqv
          rcases PartialTyStrengthens.from_borrow_inv hBty_le with ⟨UB, htyBeq, _⟩
          subst htyBeq
          refine ⟨rfl, ?_, ?_⟩
          · intro x hx
            obtain ⟨t, htmem, tt, lt, httty, hxtt⟩ :=
              lvalTargetsTyping_borrowTargets_mem htA x hx
            obtain ⟨tBty, tBlt, tBtyping, tBle⟩ :=
              lvalTargetsTyping_member_strengthens htB t (hAB htmem)
            rcases PartialTyStrengthens.to_borrow_inv tBle with ⟨tt'', tBtyEq, htt''_UB⟩
            subst tBtyEq
            have hcmp := hdet t (List.mem_append_left _ htmem) _ _ _ _ httty tBtyping
            simp only [Ty.eqv] at hcmp
            exact htt''_UB (hcmp.2.1 hxtt)
          · intro x hx
            obtain ⟨t, htmem, tt, lt, httty, hxtt⟩ :=
              lvalTargetsTyping_borrowTargets_mem htB x hx
            obtain ⟨tAty, tAlt, tAtyping, tAle⟩ :=
              lvalTargetsTyping_member_strengthens htA t (hBA htmem)
            rcases PartialTyStrengthens.to_borrow_inv tAle with ⟨tt'', tAtyEq, htt''_UA⟩
            subst tAtyEq
            have hcmp := hdet t (List.mem_append_right _ htmem) _ _ _ _ tAtyping httty
            simp only [Ty.eqv] at hcmp
            exact htt''_UA (hcmp.2.2 hxtt)
      | unit => simp [Ty.eqv] at hh_eqv
      | int => simp [Ty.eqv] at hh_eqv
      | box _ => simp [Ty.eqv] at hh_eqv

/-- Two environments whose common slots carry `eqv` types.  This is the relation
preserved by the write-fan-out join (both sides are one environment modified by
writing the same right-hand type), and it is what lets two branch typings of the
same lval be related across environments. -/
def EnvEqvCompat (e1 e2 : Env) : Prop :=
  ∀ x slotA slotB, e1.slotAt x = some slotA → e2.slotAt x = some slotB →
    PartialTy.eqv slotA.ty slotB.ty

/-- Cross-environment version of `lvalTargetsTyping_subsetEquiv_eqv`: the two
target-list typings live in possibly-different environments `e1`, `e2`, related
only through the cross-environment member determinism `hdet`.  The proof is
identical to the single-environment version (every member fact is taken in its
own environment; the two sides are linked only via `hdet`). -/
theorem lvalTargetsTyping_subsetEquiv_eqv_cross {e1 e2 : Env}
    {tgtsA tgtsB : List LVal} {tyA tyB : Ty} {lA lB : Lifetime}
    (hAB : tgtsA ⊆ tgtsB) (hBA : tgtsB ⊆ tgtsA)
    (hdet : ∀ m, m ∈ tgtsA ++ tgtsB → ∀ ma mb lma lmb,
      LValTyping e1 m (.ty ma) lma → LValTyping e2 m (.ty mb) lmb → Ty.eqv ma mb)
    (htA : LValTargetsTyping e1 tgtsA (.ty tyA) lA)
    (htB : LValTargetsTyping e2 tgtsB (.ty tyB) lB) :
    Ty.eqv tyA tyB := by
  obtain ⟨h, hhmem⟩ : ∃ h, h ∈ tgtsA := by
    cases htA with
    | singleton _ => exact ⟨_, List.mem_cons_self⟩
    | cons _ _ _ _ => exact ⟨_, List.mem_cons_self⟩
  obtain ⟨hAty, hAlt, hAty_typing, hAty_le⟩ :=
    lvalTargetsTyping_member_strengthens htA h hhmem
  obtain ⟨hBty, hBlt, hBty_typing, hBty_le⟩ :=
    lvalTargetsTyping_member_strengthens htB h (hAB hhmem)
  have hh_eqv : Ty.eqv hAty hBty :=
    hdet h (List.mem_append_left _ hhmem) _ _ _ _ hAty_typing hBty_typing
  cases tyA with
  | unit =>
      have hAu : hAty = .unit := PartialTyStrengthens.to_unit_inv hAty_le
      subst hAu
      have hBu : hBty = .unit := by cases hBty <;> simp_all [Ty.eqv]
      subst hBu
      have : tyB = .unit := PartialTyStrengthens.from_unit_inv hBty_le
      subst this; trivial
  | int =>
      have hAu : hAty = .int := PartialTyStrengthens.to_int_inv hAty_le
      subst hAu
      have hBu : hBty = .int := by cases hBty <;> simp_all [Ty.eqv]
      subst hBu
      have : tyB = .int := PartialTyStrengthens.from_int_inv hBty_le
      subst this; trivial
  | box cA =>
      have hAbox : hAty = .box cA := by cases hAty_le; rfl
      subst hAbox
      have hBbox : ∃ cB, hBty = .box cB := by cases hBty <;> simp_all [Ty.eqv]
      obtain ⟨cB, hBeq⟩ := hBbox
      subst hBeq
      have : tyB = .box cB :=
        PartialTyStrengthens.from_box_ty_inv hBty_le
      subst this
      exact hh_eqv
  | borrow m UA =>
      rcases PartialTyStrengthens.to_borrow_inv hAty_le with ⟨hAtt, hAtyEq, _⟩
      subst hAtyEq
      cases hBty with
      | borrow mB hBtt =>
          simp only [Ty.eqv] at hh_eqv
          obtain ⟨rfl, _, _⟩ := hh_eqv
          rcases PartialTyStrengthens.from_borrow_inv hBty_le with ⟨UB, htyBeq, _⟩
          subst htyBeq
          refine ⟨rfl, ?_, ?_⟩
          · intro x hx
            obtain ⟨t, htmem, tt, lt, httty, hxtt⟩ :=
              lvalTargetsTyping_borrowTargets_mem htA x hx
            obtain ⟨tBty, tBlt, tBtyping, tBle⟩ :=
              lvalTargetsTyping_member_strengthens htB t (hAB htmem)
            rcases PartialTyStrengthens.to_borrow_inv tBle with ⟨tt'', tBtyEq, htt''_UB⟩
            subst tBtyEq
            have hcmp := hdet t (List.mem_append_left _ htmem) _ _ _ _ httty tBtyping
            simp only [Ty.eqv] at hcmp
            exact htt''_UB (hcmp.2.1 hxtt)
          · intro x hx
            obtain ⟨t, htmem, tt, lt, httty, hxtt⟩ :=
              lvalTargetsTyping_borrowTargets_mem htB x hx
            obtain ⟨tAty, tAlt, tAtyping, tAle⟩ :=
              lvalTargetsTyping_member_strengthens htA t (hBA htmem)
            rcases PartialTyStrengthens.to_borrow_inv tAle with ⟨tt'', tAtyEq, htt''_UA⟩
            subst tAtyEq
            have hcmp := hdet t (List.mem_append_right _ htmem) _ _ _ _ tAtyping httty
            simp only [Ty.eqv] at hcmp
            exact htt''_UA (hcmp.2.2 hxtt)
      | unit => simp [Ty.eqv] at hh_eqv
      | int => simp [Ty.eqv] at hh_eqv
      | box _ => simp [Ty.eqv] at hh_eqv

/-- Single-lval type determinism (`eqv` form): in a linearizable environment,
any two typings of the same lval have `eqv` types (same shape, and borrow target
lists subset-equivalent).  Proved by strong induction on the rank of the lval's
base variable, with an inner structural induction on the lval (the dereference
recursion stays at the same rank, while borrow-target recursion strictly lowers
the rank via `lvalTyping_vars_rank_lt`). -/
theorem lvalTyping_eqv {env : Env} {φ : Name → Nat}
    (hφ : ∀ x slot, env.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    ∀ (lv : LVal) {a b : PartialTy} {la lb : Lifetime},
      LValTyping env lv a la → LValTyping env lv b lb → PartialTy.eqv a b := by
  suffices h : ∀ (n : Nat) (lv : LVal), φ (LVal.base lv) = n →
      ∀ {a b : PartialTy} {la lb : Lifetime},
        LValTyping env lv a la → LValTyping env lv b lb → PartialTy.eqv a b by
    intro lv a b la lb ha hb
    exact h (φ (LVal.base lv)) lv rfl ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase a b la lb ha hb
        cases ha with
        | var hslot =>
            cases hb with
            | var hslot' =>
                have heq := Option.some.inj (hslot.symm.trans hslot')
                rw [heq]
    | deref lv' ihStruct =>
        intro hbase a b la lb ha hb
        have hbase' : φ (LVal.base lv') = n := by
          simpa [LVal.base] using hbase
        cases ha with
        | box hboxA =>
            cases hb with
            | box hboxB =>
                have hbox := ihStruct hbase' hboxA hboxB
                exact hbox
            | borrow hborB htB =>
                have hbad := ihStruct hbase' hboxA hborB
                simp [PartialTy.eqv] at hbad
        | borrow hborA htA =>
            cases hb with
            | box hboxB =>
                have hbad := ihStruct hbase' hborA hboxB
                simp [PartialTy.eqv] at hbad
            | borrow hborB htB =>
                rename_i mutA tgtsA borrowLifeA mutB tgtsB borrowLifeB
                -- member determinism: borrow targets have strictly smaller rank.
                have hmemDet : ∀ (tgts : List LVal),
                    (∀ t : LVal, t ∈ tgts → φ (LVal.base t) < n) →
                    ∀ m : LVal, m ∈ tgts → ∀ ma mb lma lmb,
                      LValTyping env m (.ty ma) lma →
                      LValTyping env m (.ty mb) lmb → Ty.eqv ma mb := by
                  intro tgts hlow m hm ma mb lma lmb hma hmb
                  have := ihRank (φ (LVal.base m)) (hlow m hm) m rfl hma hmb
                  simpa [PartialTy.eqv] using this
                -- both borrow lvals have lower-rank targets (rank lemma)
                have hlowA : ∀ t : LVal, t ∈ tgtsA → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutA tgtsA)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hborA _ hvar
                  have hxn : φ (LVal.base lv') = n := hbase'
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hxn
                have hlowB : ∀ t : LVal, t ∈ tgtsB → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutB tgtsB)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hborB _ hvar
                  have hxn : φ (LVal.base lv') = n := hbase'
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hxn
                -- lv' is the same lval in both, so its borrow types are eqv:
                -- mutA = mutB and tgtsA, tgtsB are subset-equivalent.
                have hlvEqv : PartialTy.eqv (.ty (.borrow mutA tgtsA))
                    (.ty (.borrow mutB tgtsB)) :=
                  ihStruct hbase' hborA hborB
                simp only [PartialTy.eqv, Ty.eqv] at hlvEqv
                obtain ⟨rfl, htAB, htBA⟩ := hlvEqv
                rcases LValTargetsTyping.output_full htA with ⟨aTy, haFull⟩
                rcases LValTargetsTyping.output_full htB with ⟨bTy, hbFull⟩
                subst haFull; subst hbFull
                -- relate the two unions over subset-equivalent target lists
                have heqv : Ty.eqv aTy bTy :=
                  lvalTargetsTyping_subsetEquiv_eqv htAB htBA
                    (hmemDet (tgtsA ++ tgtsB) (by
                      intro t ht
                      rcases List.mem_append.mp ht with h | h
                      · exact hlowA t h
                      · exact hlowB t h))
                    htA htB
                simpa [PartialTy.eqv] using heqv
    -- end deref

/-- Cross-environment single-lval determinism: two typings of the same lval in
`eqv`-compatible environments have `eqv` types.  This is the keystone for joining
deref-of-borrow typings across the write-fan-out join — it is the cross-env
mirror of `lvalTyping_eqv`, with the same φ-rank/structural induction and the
cross-env `lvalTargetsTyping_subsetEquiv_eqv_cross` in the reborrow case. -/
theorem lvalTyping_eqv_cross {e1 e2 : Env} {φ : Name → Nat}
    (hcompat : EnvEqvCompat e1 e2)
    (hφ1 : ∀ x slot, e1.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hφ2 : ∀ x slot, e2.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    ∀ (lv : LVal) {a b : PartialTy} {la lb : Lifetime},
      LValTyping e1 lv a la → LValTyping e2 lv b lb → PartialTy.eqv a b := by
  suffices h : ∀ (n : Nat) (lv : LVal), φ (LVal.base lv) = n →
      ∀ {a b : PartialTy} {la lb : Lifetime},
        LValTyping e1 lv a la → LValTyping e2 lv b lb → PartialTy.eqv a b by
    intro lv a b la lb ha hb
    exact h (φ (LVal.base lv)) lv rfl ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase a b la lb ha hb
        cases ha with
        | var hslotA =>
            cases hb with
            | var hslotB => exact hcompat x _ _ hslotA hslotB
    | deref lv' ihStruct =>
        intro hbase a b la lb ha hb
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        cases ha with
        | box hboxA =>
            cases hb with
            | box hboxB =>
                have hbox := ihStruct hbase' hboxA hboxB
                exact hbox
            | borrow hborB htB =>
                have hbad := ihStruct hbase' hboxA hborB
                simp [PartialTy.eqv] at hbad
        | borrow hborA htA =>
            cases hb with
            | box hboxB =>
                have hbad := ihStruct hbase' hborA hboxB
                simp [PartialTy.eqv] at hbad
            | borrow hborB htB =>
                rename_i mutA tgtsA borrowLifeA mutB tgtsB borrowLifeB
                have hmemDet : ∀ (tgts : List LVal),
                    (∀ t : LVal, t ∈ tgts → φ (LVal.base t) < n) →
                    ∀ m : LVal, m ∈ tgts → ∀ ma mb lma lmb,
                      LValTyping e1 m (.ty ma) lma →
                      LValTyping e2 m (.ty mb) lmb → Ty.eqv ma mb := by
                  intro tgts hlow m hm ma mb lma lmb hma hmb
                  have := ihRank (φ (LVal.base m)) (hlow m hm) m rfl hma hmb
                  simpa [PartialTy.eqv] using this
                have hlowA : ∀ t : LVal, t ∈ tgtsA → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutA tgtsA)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ1).1 hborA _ hvar
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
                have hlowB : ∀ t : LVal, t ∈ tgtsB → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutB tgtsB)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ2).1 hborB _ hvar
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
                have hlvEqv : PartialTy.eqv (.ty (.borrow mutA tgtsA))
                    (.ty (.borrow mutB tgtsB)) :=
                  ihStruct hbase' hborA hborB
                simp only [PartialTy.eqv, Ty.eqv] at hlvEqv
                obtain ⟨rfl, htAB, htBA⟩ := hlvEqv
                rcases LValTargetsTyping.output_full htA with ⟨aTy, haFull⟩
                rcases LValTargetsTyping.output_full htB with ⟨bTy, hbFull⟩
                subst haFull; subst hbFull
                have heqv : Ty.eqv aTy bTy :=
                  lvalTargetsTyping_subsetEquiv_eqv_cross htAB htBA
                    (hmemDet (tgtsA ++ tgtsB) (by
                      intro t ht
                      rcases List.mem_append.mp ht with h | h
                      · exact hlowA t h
                      · exact hlowB t h))
                    htA htB
                simpa [PartialTy.eqv] using heqv
    -- end deref

/-- Single-lval shape determinism (the coarse `sameShape` form used downstream),
derived from `lvalTyping_eqv`. -/
theorem lvalTyping_sameShape {env : Env} {φ : Name → Nat}
    (hφ : ∀ x slot, env.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    ∀ (lv : LVal) {a b : PartialTy} {la lb : Lifetime},
      LValTyping env lv a la → LValTyping env lv b lb → PartialTy.sameShape a b := by
  intro lv a b la lb ha hb
  exact PartialTy.sameShape_of_eqv (lvalTyping_eqv hφ lv ha hb)

/-- A join is an upper bound of its left branch (`Γ₁ ⊑ Γ₁ ⊔ Γ₂`). -/
theorem EnvJoin.le_left {left right join : Env}
    (h : EnvJoin left right join) : left ≤ join :=
  h.1 (Set.mem_insert _ _)

/-- A join is an upper bound of its right branch (`Γ₂ ⊑ Γ₁ ⊔ Γ₂`). -/
theorem EnvJoin.le_right {left right join : Env}
    (h : EnvJoin left right join) : right ≤ join :=
  h.1 (Set.mem_insert_of_mem _ rfl)

/-- One-directional target-list transport at the type level.  Given a sub-list
inclusion `tgts ⊆ tgts'` of borrow targets jointly typed in two environments
`e` (type `pTy`) and `e'` (type `jTy`), together with per-member transport facts
(`hmem`: each shared member's `e`-type is `sameShape` and strengthens to its
`e'`-type), the joint types are `sameShape` and `pTy` strengthens to `jTy`.

The borrow case threads the subset through `lvalTargetsTyping_borrowTargets_mem`;
the box case closes by `Ty.box` rigidity (the only strengthening into `.ty (.box
_)` is reflexivity, so the contents must coincide). -/
theorem lvalTargetsTyping_subset_strengthen {e e' : Env}
    {tgts tgts' : List LVal} {pTy jTy : Ty} {lf jLf : Lifetime}
    (hsub : tgts ⊆ tgts')
    (hmem : ∀ m, m ∈ tgts → ∀ mE mE' lmE lmE',
      LValTyping e m (.ty mE) lmE → LValTyping e' m (.ty mE') lmE' →
      Ty.sameShape mE mE' ∧ PartialTyStrengthens (.ty mE) (.ty mE'))
    (htgts : LValTargetsTyping e tgts (.ty pTy) lf)
    (htgts' : LValTargetsTyping e' tgts' (.ty jTy) jLf) :
    Ty.sameShape pTy jTy ∧ PartialTyStrengthens (.ty pTy) (.ty jTy) := by
  obtain ⟨h, hhmem⟩ : ∃ h, h ∈ tgts := by
    cases htgts with
    | singleton _ => exact ⟨_, List.mem_cons_self⟩
    | cons _ _ _ _ => exact ⟨_, List.mem_cons_self⟩
  obtain ⟨hE, hElt, hEty, hEle⟩ := lvalTargetsTyping_member_strengthens htgts h hhmem
  obtain ⟨hE', hE'lt, hE'ty, hE'le⟩ :=
    lvalTargetsTyping_member_strengthens htgts' h (hsub hhmem)
  obtain ⟨hmemShape, hmemStr⟩ := hmem h hhmem _ _ _ _ hEty hE'ty
  have hsameShape : Ty.sameShape pTy jTy := by
    have h1 : Ty.sameShape hE pTy := ty_sameShape_of_strengthens hEle
    have h2 : Ty.sameShape hE' jTy := ty_sameShape_of_strengthens hE'le
    exact Ty.sameShape_trans (Ty.sameShape_trans (Ty.sameShape_symm h1) hmemShape) h2
  refine ⟨hsameShape, ?_⟩
  cases pTy with
  | unit =>
      have : jTy = .unit := by cases jTy <;> simp_all [Ty.sameShape]
      subst this; exact PartialTyStrengthens.reflex
  | int =>
      have : jTy = .int := by cases jTy <;> simp_all [Ty.sameShape]
      subst this; exact PartialTyStrengthens.reflex
  | box cA =>
      have hjeq : jTy = .box cA := by
        have hEbox : hE = .box cA := PartialTyStrengthens.to_box_ty_inv hEle
        subst hEbox
        have hE'box : hE' = .box cA := PartialTyStrengthens.from_box_ty_inv hmemStr
        subst hE'box
        exact PartialTyStrengthens.from_box_ty_inv hE'le
      subst hjeq; exact PartialTyStrengthens.reflex
  | borrow m UA =>
      obtain ⟨UB, hjeq⟩ : ∃ UB, jTy = .borrow m UB := by
        cases jTy <;> simp_all [Ty.sameShape]
      subst hjeq
      refine PartialTyStrengthens.borrow ?_
      intro x hx
      obtain ⟨t, htmem, tt, lt, httty, hxtt⟩ :=
        lvalTargetsTyping_borrowTargets_mem htgts x hx
      obtain ⟨tE', tlt', tE'ty, tE'le⟩ :=
        lvalTargetsTyping_member_strengthens htgts' t (hsub htmem)
      rcases PartialTyStrengthens.to_borrow_inv tE'le with ⟨tt2, htE'eq, htt2_UB⟩
      subst htE'eq
      obtain ⟨_, htstr⟩ := hmem t htmem _ _ _ _ httty tE'ty
      exact htt2_UB (PartialTyStrengthens.borrow_subset htstr hxtt)

/-! ### Exact type equivalence (`eqvX`)

`Ty.eqv` is too coarse for the strengthening transport: it relates `box(&[a])`
and `box(&[a,a])` (it recurses *into* `box` contents with `eqv`), yet `Ty.box`
is **rigid** under `PartialTyStrengthens` (only reflexivity strengthens into
`.ty (.box _)`).  So `c ⊑ a` plus `Ty.eqv a b` does **not** give `c ⊑ b`.

`eqvX` fixes this by making `box` contents **exactly equal** (they are
slot/structure-derived, never produced by a `PartialTyUnion`, so determinism in
fact yields equality there — see `lvalTyping_eqvX`).  With `eqvX`, strengthening
transfers along the right (`partialTyStrengthens_eqvX_right`), which is exactly
what the deref-borrow case of the join/strengthen transport needs. -/

/-- Exact type equivalence: like `Ty.eqv` but `box` contents must be *equal*. -/
def Ty.eqvX : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .borrow m₁ t₁, .borrow m₂ t₂ => m₁ = m₂ ∧ t₁ ⊆ t₂ ∧ t₂ ⊆ t₁
  | .box t₁, .box t₂ => t₁ = t₂
  | _, _ => False

/-- Partial-type version of `Ty.eqvX`. -/
def PartialTy.eqvX : PartialTy → PartialTy → Prop
  | .ty t₁, .ty t₂ => Ty.eqvX t₁ t₂
  | .box p₁, .box p₂ => PartialTy.eqvX p₁ p₂
  | .undef t₁, .undef t₂ => Ty.eqvX t₁ t₂
  | _, _ => False

@[refl] theorem Ty.eqvX_refl (a : Ty) : Ty.eqvX a a := by
  cases a <;> simp [Ty.eqvX]

@[refl] theorem PartialTy.eqvX_refl : (a : PartialTy) → PartialTy.eqvX a a
  | .ty t => Ty.eqvX_refl t
  | .box p => PartialTy.eqvX_refl p
  | .undef t => Ty.eqvX_refl t

theorem Ty.eqv_of_eqvX : {a b : Ty} → Ty.eqvX a b → Ty.eqv a b
  | .unit, .unit, _ => trivial
  | .int, .int, _ => trivial
  | .borrow _ _, .borrow _ _, h => h
  | .box _, .box _, h => by simp only [Ty.eqvX] at h; subst h; exact Ty.eqv_refl _
  | .unit, .int, h => by simp only [Ty.eqvX] at h
  | .unit, .borrow _ _, h => by simp only [Ty.eqvX] at h
  | .unit, .box _, h => by simp only [Ty.eqvX] at h
  | .int, .unit, h => by simp only [Ty.eqvX] at h
  | .int, .borrow _ _, h => by simp only [Ty.eqvX] at h
  | .int, .box _, h => by simp only [Ty.eqvX] at h
  | .borrow _ _, .unit, h => by simp only [Ty.eqvX] at h
  | .borrow _ _, .int, h => by simp only [Ty.eqvX] at h
  | .borrow _ _, .box _, h => by simp only [Ty.eqvX] at h
  | .box _, .unit, h => by simp only [Ty.eqvX] at h
  | .box _, .int, h => by simp only [Ty.eqvX] at h
  | .box _, .borrow _ _, h => by simp only [Ty.eqvX] at h

theorem PartialTy.eqv_of_eqvX : {a b : PartialTy} → PartialTy.eqvX a b → PartialTy.eqv a b
  | .ty _, .ty _, h => Ty.eqv_of_eqvX h
  | .box p1, .box p2, h => PartialTy.eqv_of_eqvX (a := p1) (b := p2) h
  | .undef _, .undef _, h => Ty.eqv_of_eqvX h
  | .ty _, .box _, h => by simp only [PartialTy.eqvX] at h
  | .ty _, .undef _, h => by simp only [PartialTy.eqvX] at h
  | .box _, .ty _, h => by simp only [PartialTy.eqvX] at h
  | .box _, .undef _, h => by simp only [PartialTy.eqvX] at h
  | .undef _, .ty _, h => by simp only [PartialTy.eqvX] at h
  | .undef _, .box _, h => by simp only [PartialTy.eqvX] at h

theorem PartialTy.sameShape_of_eqvX {a b : PartialTy} (h : PartialTy.eqvX a b) :
    PartialTy.sameShape a b :=
  PartialTy.sameShape_of_eqv (PartialTy.eqv_of_eqvX h)

/-- `Ty`-level core: an `eqvX` pair of full types strengthens (left to right). -/
theorem partialTyStrengthens_ty_of_eqvX {t1 t2 : Ty} (h : Ty.eqvX t1 t2) :
    PartialTyStrengthens (.ty t1) (.ty t2) := by
  cases t1 <;> cases t2 <;> simp only [Ty.eqvX] at h <;>
    first
      | exact PartialTyStrengthens.reflex
      | (obtain ⟨rfl, hsub, _⟩ := h; exact PartialTyStrengthens.borrow hsub)
      | (subst h; exact PartialTyStrengthens.reflex)

/-- `eqvX` types strengthen to one another (the reflex-case core of the transfer
below). -/
theorem partialTyStrengthens_of_eqvX :
    {a b : PartialTy} → PartialTy.eqvX a b → PartialTyStrengthens a b
  | .ty _, .ty _, h => partialTyStrengthens_ty_of_eqvX h
  | .box _, .box _, h => PartialTyStrengthens.box (partialTyStrengthens_of_eqvX h)
  | .undef _, .undef _, h => PartialTyStrengthens.undefLeft (partialTyStrengthens_ty_of_eqvX h)
  | .ty _, .box _, h => by simp only [PartialTy.eqvX] at h
  | .ty _, .undef _, h => by simp only [PartialTy.eqvX] at h
  | .box _, .ty _, h => by simp only [PartialTy.eqvX] at h
  | .box _, .undef _, h => by simp only [PartialTy.eqvX] at h
  | .undef _, .ty _, h => by simp only [PartialTy.eqvX] at h
  | .undef _, .box _, h => by simp only [PartialTy.eqvX] at h

/-- Strengthening transfers along `eqvX` on the right: `c ⊑ a` and `a ≈X b` give
`c ⊑ b`.  This is the wall-breaking lemma — it holds for `eqvX` (but **not** for
`eqv`) precisely because `eqvX` keeps `Ty.box` contents exact. -/
theorem partialTyStrengthens_eqvX_right {c a b : PartialTy}
    (hca : PartialTyStrengthens c a) (hab : PartialTy.eqvX a b) :
    PartialTyStrengthens c b := by
  induction hca generalizing b with
  | reflex => exact partialTyStrengthens_of_eqvX hab
  | @box cL aL _hcL ih =>
      cases b with
      | box bL => exact PartialTyStrengthens.box (ih (by simpa [PartialTy.eqvX] using hab))
      | ty _ => simp [PartialTy.eqvX] at hab
      | undef _ => simp [PartialTy.eqvX] at hab
  | @borrow m cL aL hsub =>
      cases b with
      | ty tb =>
          cases tb with
          | borrow m' bL =>
              simp only [PartialTy.eqvX, Ty.eqvX] at hab
              obtain ⟨rfl, haLbL, _⟩ := hab
              exact PartialTyStrengthens.borrow (fun x hx => haLbL (hsub hx))
          | unit => simp [PartialTy.eqvX, Ty.eqvX] at hab
          | int => simp [PartialTy.eqvX, Ty.eqvX] at hab
          | box _ => simp [PartialTy.eqvX, Ty.eqvX] at hab
      | box _ => simp [PartialTy.eqvX] at hab
      | undef _ => simp [PartialTy.eqvX] at hab
  | @undefLeft cT aT _h ih =>
      cases b with
      | undef bT =>
          exact PartialTyStrengthens.undefLeft (ih (by simpa [PartialTy.eqvX] using hab))
      | ty _ => simp [PartialTy.eqvX] at hab
      | box _ => simp [PartialTy.eqvX] at hab
  | @intoUndef cT aT _h ih =>
      cases b with
      | undef bT =>
          exact PartialTyStrengthens.intoUndef (ih (by simpa [PartialTy.eqvX] using hab))
      | ty _ => simp [PartialTy.eqvX] at hab
      | box _ => simp [PartialTy.eqvX] at hab
  | @boxIntoUndef cL aT h _ih =>
      cases b with
      | undef bT =>
          have hbox : Ty.eqvX (.box aT) bT := by simpa [PartialTy.eqvX] using hab
          have : bT = .box aT := by cases bT <;> simp_all [Ty.eqvX]
          subst this
          exact PartialTyStrengthens.boxIntoUndef h
      | ty _ => simp [PartialTy.eqvX] at hab
      | box _ => simp [PartialTy.eqvX] at hab

/-- `eqvX` form of `lvalTargetsTyping_subsetEquiv_eqv`: with member determinism
delivering `eqvX` (exact box contents), subset-equivalent target lists have
`eqvX` joint types.  The only change from the `eqv` proof is the `box` case,
which now reads off the exact content equality directly. -/
theorem lvalTargetsTyping_subsetEquiv_eqvX {env : Env}
    {tgtsA tgtsB : List LVal} {tyA tyB : Ty} {lA lB : Lifetime}
    (hAB : tgtsA ⊆ tgtsB) (hBA : tgtsB ⊆ tgtsA)
    (hdet : ∀ m, m ∈ tgtsA ++ tgtsB → ∀ ma mb lma lmb,
      LValTyping env m (.ty ma) lma → LValTyping env m (.ty mb) lmb → Ty.eqvX ma mb)
    (htA : LValTargetsTyping env tgtsA (.ty tyA) lA)
    (htB : LValTargetsTyping env tgtsB (.ty tyB) lB) :
    Ty.eqvX tyA tyB := by
  obtain ⟨h, hhmem⟩ : ∃ h, h ∈ tgtsA := by
    cases htA with
    | singleton _ => exact ⟨_, List.mem_cons_self⟩
    | cons _ _ _ _ => exact ⟨_, List.mem_cons_self⟩
  obtain ⟨hAty, hAlt, hAty_typing, hAty_le⟩ :=
    lvalTargetsTyping_member_strengthens htA h hhmem
  obtain ⟨hBty, hBlt, hBty_typing, hBty_le⟩ :=
    lvalTargetsTyping_member_strengthens htB h (hAB hhmem)
  have hh_eqv : Ty.eqvX hAty hBty :=
    hdet h (List.mem_append_left _ hhmem) _ _ _ _ hAty_typing hBty_typing
  cases tyA with
  | unit =>
      have hAu : hAty = .unit := PartialTyStrengthens.to_unit_inv hAty_le
      subst hAu
      have hBu : hBty = .unit := by cases hBty <;> simp_all [Ty.eqvX]
      subst hBu
      have : tyB = .unit := PartialTyStrengthens.from_unit_inv hBty_le
      subst this; trivial
  | int =>
      have hAu : hAty = .int := PartialTyStrengthens.to_int_inv hAty_le
      subst hAu
      have hBu : hBty = .int := by cases hBty <;> simp_all [Ty.eqvX]
      subst hBu
      have : tyB = .int := PartialTyStrengthens.from_int_inv hBty_le
      subst this; trivial
  | box cA =>
      have hAbox : hAty = .box cA := by cases hAty_le; rfl
      subst hAbox
      have hBbox : ∃ cB, hBty = .box cB := by cases hBty <;> simp_all [Ty.eqvX]
      obtain ⟨cB, hBeq⟩ := hBbox
      subst hBeq
      have : tyB = .box cB :=
        PartialTyStrengthens.from_box_ty_inv hBty_le
      subst this
      exact hh_eqv
  | borrow m UA =>
      rcases PartialTyStrengthens.to_borrow_inv hAty_le with ⟨hAtt, hAtyEq, _⟩
      subst hAtyEq
      cases hBty with
      | borrow mB hBtt =>
          simp only [Ty.eqvX] at hh_eqv
          obtain ⟨rfl, _, _⟩ := hh_eqv
          rcases PartialTyStrengthens.from_borrow_inv hBty_le with ⟨UB, htyBeq, _⟩
          subst htyBeq
          refine ⟨rfl, ?_, ?_⟩
          · intro x hx
            obtain ⟨t, htmem, tt, lt, httty, hxtt⟩ :=
              lvalTargetsTyping_borrowTargets_mem htA x hx
            obtain ⟨tBty, tBlt, tBtyping, tBle⟩ :=
              lvalTargetsTyping_member_strengthens htB t (hAB htmem)
            rcases PartialTyStrengthens.to_borrow_inv tBle with ⟨tt'', tBtyEq, htt''_UB⟩
            subst tBtyEq
            have hcmp := hdet t (List.mem_append_left _ htmem) _ _ _ _ httty tBtyping
            simp only [Ty.eqvX] at hcmp
            exact htt''_UB (hcmp.2.1 hxtt)
          · intro x hx
            obtain ⟨t, htmem, tt, lt, httty, hxtt⟩ :=
              lvalTargetsTyping_borrowTargets_mem htB x hx
            obtain ⟨tAty, tAlt, tAtyping, tAle⟩ :=
              lvalTargetsTyping_member_strengthens htA t (hBA htmem)
            rcases PartialTyStrengthens.to_borrow_inv tAle with ⟨tt'', tAtyEq, htt''_UA⟩
            subst tAtyEq
            have hcmp := hdet t (List.mem_append_right _ htmem) _ _ _ _ tAtyping httty
            simp only [Ty.eqvX] at hcmp
            exact htt''_UA (hcmp.2.2 hxtt)
      | unit => simp [Ty.eqvX] at hh_eqv
      | int => simp [Ty.eqvX] at hh_eqv
      | box _ => simp [Ty.eqvX] at hh_eqv

/-- `eqvX` form of `lvalTyping_eqv`: single-lval type determinism with *exact*
box contents.  Same φ-rank/structural induction; the borrow-deref case routes
through `lvalTargetsTyping_subsetEquiv_eqvX`. -/
theorem lvalTyping_eqvX {env : Env} {φ : Name → Nat}
    (hφ : ∀ x slot, env.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    ∀ (lv : LVal) {a b : PartialTy} {la lb : Lifetime},
      LValTyping env lv a la → LValTyping env lv b lb → PartialTy.eqvX a b := by
  suffices h : ∀ (n : Nat) (lv : LVal), φ (LVal.base lv) = n →
      ∀ {a b : PartialTy} {la lb : Lifetime},
        LValTyping env lv a la → LValTyping env lv b lb → PartialTy.eqvX a b by
    intro lv a b la lb ha hb
    exact h (φ (LVal.base lv)) lv rfl ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase a b la lb ha hb
        cases ha with
        | var hslot =>
            cases hb with
            | var hslot' =>
                have heq := Option.some.inj (hslot.symm.trans hslot')
                rw [heq]
    | deref lv' ihStruct =>
        intro hbase a b la lb ha hb
        have hbase' : φ (LVal.base lv') = n := by
          simpa [LVal.base] using hbase
        cases ha with
        | box hboxA =>
            cases hb with
            | box hboxB =>
                have hbox := ihStruct hbase' hboxA hboxB
                exact hbox
            | borrow hborB htB =>
                have hbad := ihStruct hbase' hboxA hborB
                simp [PartialTy.eqvX] at hbad
        | borrow hborA htA =>
            cases hb with
            | box hboxB =>
                have hbad := ihStruct hbase' hborA hboxB
                simp [PartialTy.eqvX] at hbad
            | borrow hborB htB =>
                rename_i mutA tgtsA borrowLifeA mutB tgtsB borrowLifeB
                have hmemDet : ∀ (tgts : List LVal),
                    (∀ t : LVal, t ∈ tgts → φ (LVal.base t) < n) →
                    ∀ m : LVal, m ∈ tgts → ∀ ma mb lma lmb,
                      LValTyping env m (.ty ma) lma →
                      LValTyping env m (.ty mb) lmb → Ty.eqvX ma mb := by
                  intro tgts hlow m hm ma mb lma lmb hma hmb
                  have := ihRank (φ (LVal.base m)) (hlow m hm) m rfl hma hmb
                  simpa [PartialTy.eqvX] using this
                have hlowA : ∀ t : LVal, t ∈ tgtsA → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutA tgtsA)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hborA _ hvar
                  have hxn : φ (LVal.base lv') = n := hbase'
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hxn
                have hlowB : ∀ t : LVal, t ∈ tgtsB → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutB tgtsB)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hborB _ hvar
                  have hxn : φ (LVal.base lv') = n := hbase'
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hxn
                have hlvEqv : PartialTy.eqvX (.ty (.borrow mutA tgtsA))
                    (.ty (.borrow mutB tgtsB)) :=
                  ihStruct hbase' hborA hborB
                simp only [PartialTy.eqvX, Ty.eqvX] at hlvEqv
                obtain ⟨rfl, htAB, htBA⟩ := hlvEqv
                rcases LValTargetsTyping.output_full htA with ⟨aTy, haFull⟩
                rcases LValTargetsTyping.output_full htB with ⟨bTy, hbFull⟩
                subst haFull; subst hbFull
                have heqv : Ty.eqvX aTy bTy :=
                  lvalTargetsTyping_subsetEquiv_eqvX htAB htBA
                    (hmemDet (tgtsA ++ tgtsB) (by
                      intro t ht
                      rcases List.mem_append.mp ht with h | h
                      · exact hlowA t h
                      · exact hlowB t h))
                    htA htB
                simpa [PartialTy.eqvX] using heqv

/-- **Strengthening transport** (the join/strengthen keystone).  If the source
environment `e` strengthens to `e'` at the slot level *shape-preservingly*
(`hstr`), both are linearizable, and `e'` is `Coherent`, then any `LValTyping` in
`e` transports to `e'` with a `sameShape`, strengthened type.

Proved by strong induction on the rank of the lval's base variable (φ from
`Linearizable e`), structural on the lval.  The deref-borrow case is the crux:
the inner borrow lval transports (structural IH) to a borrow `&tgts'` in `e'`;
`Coherent e'` supplies a joint typing of `tgts'`; and the two joint types are
related via `lvalTargetsTyping_subset_strengthen`, whose per-member facts come
from the rank IH (strictly smaller targets) reconciled in `e'` by
`lvalTyping_eqvX` + `partialTyStrengthens_eqvX_right` (this is where exact box
contents — `eqvX`, not `eqv` — are essential). -/
theorem lvalTyping_strengthen_transport {e e' : Env} {φ : Name → Nat}
    (hstr : ∀ x sE, e.slotAt x = some sE →
      ∃ sE', e'.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hφ' : ∀ x slot, e'.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcoh' : Coherent e') :
    ∀ (lv : LVal) {p : PartialTy} {lf : Lifetime},
      LValTyping e lv p lf →
      ∃ p' lf', LValTyping e' lv p' lf' ∧
        PartialTy.sameShape p p' ∧ PartialTyStrengthens p p' := by
  suffices h : ∀ (n : Nat) (lv : LVal), φ (LVal.base lv) = n →
      ∀ {p : PartialTy} {lf : Lifetime},
        LValTyping e lv p lf →
        ∃ p' lf', LValTyping e' lv p' lf' ∧
          PartialTy.sameShape p p' ∧ PartialTyStrengthens p p' by
    intro lv p lf hp
    exact h (φ (LVal.base lv)) lv rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase p lf hp
        cases hp with
        | var hslot =>
            rcases hstr x _ hslot with ⟨sE', hsE', hshape, hstrong⟩
            exact ⟨sE'.ty, sE'.lifetime, LValTyping.var hsE', hshape, hstrong⟩
    | deref lv' ihStruct =>
        intro hbase p lf hp
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        cases hp with
        | box hbox =>
            rcases ihStruct hbase' hbox with ⟨pw', lfw', hw', hshapeW, hstrongW⟩
            cases pw' with
            | box inner' =>
                refine ⟨inner', lfw', LValTyping.box hw', ?_, ?_⟩
                · simpa [PartialTy.sameShape] using hshapeW
                · cases hstrongW with
                  | reflex => exact PartialTyStrengthens.reflex
                  | box hh => exact hh
            | ty _ => simp [PartialTy.sameShape] at hshapeW
            | undef _ => simp [PartialTy.sameShape] at hshapeW
        | borrow hbor htgts =>
            rename_i mutb tgts bLf
            rcases ihStruct hbase' hbor with ⟨pw', lfw', hw', hshapeW, hstrongW⟩
            cases pw' with
            | ty tw' =>
                rcases PartialTyStrengthens.from_borrow_inv hstrongW with
                  ⟨tgts', htw'eq, hsub⟩
                subst htw'eq
                rcases hcoh' lv' mutb tgts' lfw' hw' with ⟨jTy, jLf, htgts'⟩
                rcases LValTargetsTyping.output_full htgts with ⟨pTy, hpFull⟩
                subst hpFull
                have hlow : ∀ t : LVal, t ∈ tgts → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutb tgts)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hbor _ hvar
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
                have hmem : ∀ m, m ∈ tgts → ∀ mE mE' lmE lmE',
                    LValTyping e m (.ty mE) lmE → LValTyping e' m (.ty mE') lmE' →
                    Ty.sameShape mE mE' ∧ PartialTyStrengthens (.ty mE) (.ty mE') := by
                  intro m hmtgts mE mE' lmE lmE' hmE hmE'
                  rcases ihRank (φ (LVal.base m)) (hlow m hmtgts) m rfl hmE with
                    ⟨pm', lfm', hm', hshapeM, hstrongM⟩
                  have heqvX : PartialTy.eqvX pm' (.ty mE') :=
                    lvalTyping_eqvX hφ' m hm' hmE'
                  have hsh : PartialTy.sameShape (.ty mE) (.ty mE') :=
                    PartialTy.sameShape_trans hshapeM (PartialTy.sameShape_of_eqvX heqvX)
                  refine ⟨by simpa [PartialTy.sameShape] using hsh, ?_⟩
                  exact partialTyStrengthens_eqvX_right hstrongM heqvX
                rcases lvalTargetsTyping_subset_strengthen hsub hmem htgts htgts' with
                  ⟨hshapeJoint, hstrongJoint⟩
                exact ⟨.ty jTy, jLf, LValTyping.borrow hw' htgts',
                  by simpa [PartialTy.sameShape] using hshapeJoint, hstrongJoint⟩
            | box _ => simp [PartialTy.sameShape] at hshapeW
            | undef _ => simp [PartialTy.sameShape] at hshapeW

/-- **Rank-bounded** transport keystone: `Coherent e'` restricted to lvals of
rank `≤ N` suffices to transport lvals of rank `≤ N` (the keystone only queries
`Coherent e'` at the transported lval's own rank).  This is what lets
`Coherent`/`ContainedBorrows` on a join/write be *bootstrapped* by strong rank
induction (the full keystone assumes `Coherent e'` outright and cannot). -/
theorem lvalTyping_strengthen_transport_bounded {e e' : Env} {φ : Name → Nat}
    (N : Nat)
    (hstr : ∀ x sE, e.slotAt x = some sE →
      ∃ sE', e'.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hφ' : ∀ x slot, e'.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcoh' : ∀ lv'' m'' T'' bLf'', φ (LVal.base lv'') ≤ N →
      LValTyping e' lv'' (.ty (.borrow m'' T'')) bLf'' →
      ∃ ty lt, LValTargetsTyping e' T'' (.ty ty) lt) :
    ∀ (lv : LVal), φ (LVal.base lv) ≤ N → ∀ {p : PartialTy} {lf : Lifetime},
      LValTyping e lv p lf →
      ∃ p' lf', LValTyping e' lv p' lf' ∧
        PartialTy.sameShape p p' ∧ PartialTyStrengthens p p' := by
  suffices h : ∀ (n : Nat), n ≤ N → ∀ (lv : LVal), φ (LVal.base lv) = n →
      ∀ {p : PartialTy} {lf : Lifetime},
        LValTyping e lv p lf →
        ∃ p' lf', LValTyping e' lv p' lf' ∧
          PartialTy.sameShape p p' ∧ PartialTyStrengthens p p' by
    intro lv hle p lf hp
    exact h (φ (LVal.base lv)) hle lv rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro hNle lv
    induction lv with
    | var x =>
        intro _hbase p lf hp
        cases hp with
        | var hslot =>
            rcases hstr x _ hslot with ⟨sE', hsE', hshape, hstrong⟩
            exact ⟨sE'.ty, sE'.lifetime, LValTyping.var hsE', hshape, hstrong⟩
    | deref lv' ihStruct =>
        intro hbase p lf hp
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        cases hp with
        | box hbox =>
            rcases ihStruct hbase' hbox with ⟨pw', lfw', hw', hshapeW, hstrongW⟩
            cases pw' with
            | box inner' =>
                refine ⟨inner', lfw', LValTyping.box hw', ?_, ?_⟩
                · simpa [PartialTy.sameShape] using hshapeW
                · cases hstrongW with
                  | reflex => exact PartialTyStrengthens.reflex
                  | box hh => exact hh
            | ty _ => simp [PartialTy.sameShape] at hshapeW
            | undef _ => simp [PartialTy.sameShape] at hshapeW
        | borrow hbor htgts =>
            rename_i mutb tgts bLf
            rcases ihStruct hbase' hbor with ⟨pw', lfw', hw', hshapeW, hstrongW⟩
            cases pw' with
            | ty tw' =>
                rcases PartialTyStrengthens.from_borrow_inv hstrongW with
                  ⟨tgts', htw'eq, hsub⟩
                subst htw'eq
                rcases hcoh' lv' mutb tgts' lfw' (by omega) hw' with
                  ⟨jTy, jLf, htgts'⟩
                rcases LValTargetsTyping.output_full htgts with ⟨pTy, hpFull⟩
                subst hpFull
                have hlow : ∀ t : LVal, t ∈ tgts → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutb tgts)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hbor _ hvar
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
                have hmem : ∀ m, m ∈ tgts → ∀ mE mE' lmE lmE',
                    LValTyping e m (.ty mE) lmE → LValTyping e' m (.ty mE') lmE' →
                    Ty.sameShape mE mE' ∧ PartialTyStrengthens (.ty mE) (.ty mE') := by
                  intro m hmtgts mE mE' lmE lmE' hmE hmE'
                  rcases ihRank (φ (LVal.base m)) (hlow m hmtgts)
                      (by have := hlow m hmtgts; omega) m rfl hmE with
                    ⟨pm', lfm', hm', hshapeM, hstrongM⟩
                  have heqvX : PartialTy.eqvX pm' (.ty mE') :=
                    lvalTyping_eqvX hφ' m hm' hmE'
                  have hsh : PartialTy.sameShape (.ty mE) (.ty mE') :=
                    PartialTy.sameShape_trans hshapeM (PartialTy.sameShape_of_eqvX heqvX)
                  refine ⟨by simpa [PartialTy.sameShape] using hsh, ?_⟩
                  exact partialTyStrengthens_eqvX_right hstrongM heqvX
                rcases lvalTargetsTyping_subset_strengthen hsub hmem htgts htgts' with
                  ⟨hshapeJoint, hstrongJoint⟩
                exact ⟨.ty jTy, jLf, LValTyping.borrow hw' htgts',
                  by simpa [PartialTy.sameShape] using hshapeJoint, hstrongJoint⟩
            | box _ => simp [PartialTy.sameShape] at hshapeW
            | undef _ => simp [PartialTy.sameShape] at hshapeW

/-! ### Runtime-invariant preservation facts

These package the two runtime invariants (`Linearizable`, `Coherent`) that
`lvalTyping_strengthen_transport` consumes, as preserved by the two state
operations that the Appendix 9.6 borrow-invariance argument performs: a single
`EnvWrite` and an `EnvJoin` (the write fan-out's branch merge).

`Linearizable` preservation is the `lw_rust_followup` contribution (Definition 11
+ its preservation proposition: a common rank function survives a write and a
branch join); it is stated here as an explicit, documented obligation
to be discharged from the followup development.

  `Coherent` preservation is Section-4 content provable from the transport keystone
  by a rank-stratified induction; it is likewise staged as an explicit obligation
  here so the borrow-invariance landmarks can be derived from it first. -/

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
def BorrowTargetOrigin (env : Env) (rhsTy : Ty) (x : Name) (t : LVal) : Prop :=
  (∃ slot m T, env.slotAt x = some slot ∧
    PartialTyContains slot.ty (.borrow m T) ∧ t ∈ T) ∨
  (∃ m T, PartialTyContains (.ty rhsTy) (.borrow m T) ∧ t ∈ T)

/-- Type-level analogue of `BorrowTargetOrigin` used for the `UpdateAtPath`
motive: a borrow target in the updated type comes from the old type or the rhs. -/
def TypeBorrowOrigin (oldTy : PartialTy) (rhsTy : Ty) (t : LVal) : Prop :=
  (∃ m T, PartialTyContains oldTy (.borrow m T) ∧ t ∈ T) ∨
  (∃ m T, PartialTyContains (.ty rhsTy) (.borrow m T) ∧ t ∈ T)

theorem EnvWrite.borrowTargetOrigin {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} :
    0 < rank →
    EnvWrite rank env lv rhsTy result →
    ∀ x slot m T, result.slotAt x = some slot →
      PartialTyContains slot.ty (.borrow m T) →
      ∀ t, t ∈ T → BorrowTargetOrigin env rhsTy x t := by
  intro hrank hwrite
  refine EnvWrite.rec
    (motive_1 := fun rank env₁ _path oldTy ty env₂ updatedTy _ =>
      0 < rank →
      (∀ m T, PartialTyContains updatedTy (.borrow m T) →
        ∀ t, t ∈ T → TypeBorrowOrigin oldTy ty t) ∧
      (∀ x slot m T, env₂.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env₁ ty x t))
    (motive_2 := fun rank env _path _targets ty result _ =>
      0 < rank →
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x t)
    (motive_3 := fun rank env _lv ty result _ =>
      0 < rank →
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x t)
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
      · exact Or.inl ⟨m, Tl, hl, htl⟩
      · exact Or.inr ⟨m, Tr, hr, htr⟩
    · intro x slot m T hslot hcontains t ht
      exact Or.inl ⟨slot, m, T, hslot, hcontains, ht⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupd ih hrank
    rcases ih hrank with ⟨ihType, ihEnv⟩
    refine ⟨?_, ihEnv⟩
    intro m T hcontains t ht
    cases hcontains with
    | box hinner =>
        rcases ihType m T hinner t ht with ⟨m₀, T₀, hc₀, ht₀⟩ | hrhs
        · exact Or.inl ⟨m₀, T₀, PartialTyContains.box hc₀, ht₀⟩
        · exact Or.inr hrhs
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      exact Or.inl ⟨m, T, hcontains, ht⟩
    · exact ih (Nat.succ_pos rank)
  case nil =>
    intro rank env path ty _hrank x slot m T hslot hcontains t ht
    exact Or.inl ⟨slot, m, T, hslot, hcontains, ht⟩
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
      rcases ihType m T hcontains t ht with ⟨m₀, T₀, hc₀, ht₀⟩ | hrhs
      · exact Or.inl ⟨slot, m₀, T₀, by rw [hx]; exact hslot, hc₀, ht₀⟩
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
      ∀ t, t ∈ T → BorrowTargetOrigin env rhsTy x t := by
  intro hwrite
  refine EnvWrite.rec
    (motive_1 := fun _rank env₁ _path oldTy ty env₂ updatedTy _ =>
      (∀ m T, PartialTyContains updatedTy (.borrow m T) →
        ∀ t, t ∈ T → TypeBorrowOrigin oldTy ty t) ∧
      (∀ x slot m T, env₂.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env₁ ty x t))
    (motive_2 := fun _rank env _path _targets ty result _ =>
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x t)
    (motive_3 := fun _rank env _lv ty result _ =>
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x t)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite
  case strong =>
    intro env old ty
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      exact Or.inr ⟨m, T, hcontains, ht⟩
    · intro x slot m T hslot hcontains t ht
      exact Or.inl ⟨slot, m, T, hslot, hcontains, ht⟩
  case weak =>
    intro env rank old joined ty _hshape hjoin
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      rcases PartialTyUnion.contained_borrow_member hjoin hcontains ht with
        ⟨Tl, hl, htl⟩ | ⟨Tr, hr, htr⟩
      · exact Or.inl ⟨m, Tl, hl, htl⟩
      · exact Or.inr ⟨m, Tr, hr, htr⟩
    · intro x slot m T hslot hcontains t ht
      exact Or.inl ⟨slot, m, T, hslot, hcontains, ht⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupd ih
    rcases ih with ⟨ihType, ihEnv⟩
    refine ⟨?_, ihEnv⟩
    intro m T hcontains t ht
    cases hcontains with
    | box hinner =>
        rcases ihType m T hinner t ht with ⟨m₀, T₀, hc₀, ht₀⟩ | hrhs
        · exact Or.inl ⟨m₀, T₀, PartialTyContains.box hc₀, ht₀⟩
        · exact Or.inr hrhs
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      exact Or.inl ⟨m, T, hcontains, ht⟩
    · exact ih
  case nil =>
    intro rank env path ty x slot m T hslot hcontains t ht
    exact Or.inl ⟨slot, m, T, hslot, hcontains, ht⟩
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
      rcases ihType m T hcontains t ht with ⟨m₀, T₀, hc₀, ht₀⟩ | hrhs
      · exact Or.inl ⟨slot, m₀, T₀, by rw [hx]; exact hslot, hc₀, ht₀⟩
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
condition that the bare `EnvWrite.preserves_linearizedBy` axiom is missing. -/
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
      ⟨oldSlot, oldMutable, oldTargets, holdSlot, holdContains, holdTarget⟩
    have hvOld : v ∈ PartialTy.vars oldSlot.ty := by
      exact mem_partialTy_vars_iff.mpr
        ⟨oldMutable, oldTargets, target, holdContains, holdTarget, hbase⟩
    exact hlin x oldSlot holdSlot v hvOld
  · rcases hfromRhs with ⟨rhsMutable, rhsTargets, hrhsContains, hrhsTarget⟩
    have hvRhsPartial : v ∈ PartialTy.vars (.ty rhsTy) := by
      exact mem_partialTy_vars_iff.mpr
        ⟨rhsMutable, rhsTargets, target, hrhsContains, hrhsTarget, hbase⟩
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
      ⟨oldSlot, oldMutable, oldTargets, holdSlot, holdContains, holdTarget⟩
    have hvOld : v ∈ PartialTy.vars oldSlot.ty := by
      exact mem_partialTy_vars_iff.mpr
        ⟨oldMutable, oldTargets, target, holdContains, holdTarget, hbase⟩
    exact hlin x oldSlot holdSlot v hvOld
  · rcases hfromRhs with ⟨rhsMutable, rhsTargets, hrhsContains, hrhsTarget⟩
    have hvRhsPartial : v ∈ PartialTy.vars (.ty rhsTy) := by
      exact mem_partialTy_vars_iff.mpr
        ⟨rhsMutable, rhsTargets, target, hrhsContains, hrhsTarget, hbase⟩
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
    hbelow "x" { ty := .ty (.borrow false [.var "y"]), lifetime := Lifetime.root }
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
      ⟨oldSlot, oldMutable, oldTargets, holdSlot, holdContains, holdTarget⟩
    have hvOld : v ∈ PartialTy.vars oldSlot.ty := by
      exact mem_partialTy_vars_iff.mpr
        ⟨oldMutable, oldTargets, target, holdContains, holdTarget, hbase⟩
    exact hlin x oldSlot holdSlot v hvOld
  · have htargetBelow : φ (LVal.base target) < φ x :=
      hbelow x slot mutable targets target hslot hcontains htarget hfromRhs
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
    ⟨leftTy, leftLifetime, hleftTyping, _hleftOutlives, hleftBase⟩
  have hjoinBase := LValBaseOutlives.join_left hjoin hleftBase
  rcases fullJoinTransport_viaInvariants hstr hφJoin hcohJoin hcontN
      (hrankTargets target htarget) hleftTyping hjoinBase
    with ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives, hjoinBase⟩

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
    ⟨rightTy, rightLifetime, hrightTyping, _hrightOutlives, hrightBase⟩
  have hjoinBase := LValBaseOutlives.join_right hjoin hrightBase
  rcases fullJoinTransport_viaInvariants hstr hφJoin hcohJoin hcontN
      (hrankTargets target htarget) hrightTyping hjoinBase
    with ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives, hjoinBase⟩

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
  | block _hblockChild hterms _hwellFormed hdrop =>
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
  | block _hblockChild hterms _hwellFormed _hdrop =>
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
    ValidRuntimeState store (.letMut x term) →
    ValidStoreTyping store (.letMut x term) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.letMut x term) .unit env₃ →
    MultiStep store lifetime term midStore (.val value) →
    Step midStore lifetime (.letMut x (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hinnerPreservation hvalidRuntime hvalidStoreTyping hsafe htyping
    hinnerMulti hdeclareStep
  cases htyping with
  | declare _hfresh₁ hinnerTyping hfreshOut _hcoh henv₃ =>
      rcases hinnerPreservation
          (validRuntimeState_declare_inner hvalidRuntime)
          (validStoreTyping_declare_inner hvalidStoreTyping)
          hsafe hinnerTyping hinnerMulti with
        ⟨hvalidInner, hsafeInner, hvalidValue⟩
      cases hdeclareStep with
      | declare hstore =>
          have hpreserved :=
            preservation_declare_redex_runtime_of_validValue hsafeInner
              hfreshOut
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
    ValidRuntimeState store (.letMut x term) →
    ValidStoreTyping store (.letMut x term) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.letMut x term) .unit env₃ →
    MultiStep store lifetime (.letMut x term) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hinnerPreservation hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
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
  | assign hLv hinnerTyping hshape hwellTy hwrite _hranked _hcoh hnotWrite =>
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
  | assign hLhs hRhs hshape _hwf _hwriteEnv _hranked _hcoh _hnotWriteProhibited =>
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
  | declare _hfresh _hinit _hfreshOut _hcoh _henv =>
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
        _hblockChild _hterms _hwellTy _hdrop ih hwellFormed hsafe hstore =>
      ih lifetime hwellFormed hsafe hstore)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfresh hterm hfreshOut hcoh henv ih
        hwellFormed hsafe hstore =>
      progress_declare_typing (TermTyping.declare hfresh hterm hfreshOut hcoh henv)
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _env₃ _typing lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwf hwrite hranked hcoh hnotWriteProhibited ih hwellFormed
        hsafe hstore =>
      progress_assign_typing (hwellFormed lifetime) hsafe hstore
        (TermTyping.assign hLhs hRhs hshape hwf hwrite hranked hcoh hnotWriteProhibited)
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

theorem terminalStateSafe_assign_unit_of_postconditions {store : ProgramStore}
    {env : Env} :
    ValidRuntimeState store (.val .unit) →
    store ∼ₛ env →
    TerminalStateSafe store .unit env .unit := by
  intro hvalidRuntime hsafe
  exact ⟨hvalidRuntime, hsafe, ValidPartialValue.unit⟩

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

theorem partialTyContains_borrow_iff_eq {mutable : Bool} {targets : List LVal}
    {needle : Ty} :
    PartialTyContains (.ty (.borrow mutable targets)) needle ↔
      Ty.borrow mutable targets = needle := by
  constructor
  · intro hcontains
    cases hcontains with
    | here => rfl
  · intro hty
    subst hty
    exact PartialTyContains.here

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
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_int :
    TyBorrowFree .int := by
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_box {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowFree (.box ty) := by
  intro hfree mutable targets hcontains
  cases hcontains with
  | tyBox hinner =>
      exact hfree mutable targets hinner

theorem partialTyBorrowFree_box_inv {ty : PartialTy} :
    PartialTyBorrowFree (.box ty) →
    PartialTyBorrowFree ty := by
  intro hfree mutable targets hcontains
  exact hfree mutable targets (PartialTyContains.box hcontains)

/-- A borrow-free fresh slot cannot be the root of a borrow-typed lval.

This discharges the fresh-root half of `FreshUpdateCoherenceObligations` for
borrow-free declarations/results.  The old-root transport half is separate:
borrow typings rooted in existing variables may dereference old borrow targets,
and transporting those target-list typings back to the old environment is the
real remaining obligation.
-/
theorem LValTyping.update_fresh_root_partialTyBorrowFree {env : Env} {x : Name}
    {ty : Ty} {slotLifetime : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {valueLifetime : Lifetime} :
    TyBorrowFree ty →
    LVal.base lv = x →
    LValTyping (env.update x { ty := .ty ty, lifetime := slotLifetime })
      lv partialTy valueLifetime →
    PartialTyBorrowFree partialTy := by
  intro hfree hbase htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _valueLifetime _ =>
      LVal.base lv = x → PartialTyBorrowFree partialTy)
    (motive_2 := fun _targets _partialTy _valueLifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping hbase
  · intro y envSlot hslot hbase
    have hy : y = x := by simpa [LVal.base] using hbase
    subst hy
    have hslotEq :
        envSlot = { ty := PartialTy.ty ty, lifetime := slotLifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := slotLifetime } = envSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    exact partialTyBorrowFree_ty hfree
  · intro lv inner lifetime _hsource ih hbase
    exact partialTyBorrowFree_box_inv (ih (by simpa [LVal.base] using hbase))
  · intro lv mutable targets borrowLifetime targetLifetime targetTy _hborrow _htargets
      ihBorrow _ihTargets hbase
    have hsourceFree :
        PartialTyBorrowFree (.ty (.borrow mutable targets)) :=
      ihBorrow (by simpa [LVal.base] using hbase)
    exact False.elim (hsourceFree mutable targets PartialTyContains.here)
  · intro target ty lifetime _htarget _ih
    trivial
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

theorem LValTyping.update_fresh_root_not_borrow_of_tyBorrowFree {env : Env}
    {x : Name} {ty : Ty} {slotLifetime : Lifetime} {lv : LVal}
    {mutable : Bool} {targets : List LVal} {borrowLifetime : Lifetime} :
    TyBorrowFree ty →
    LVal.base lv = x →
    ¬ LValTyping (env.update x { ty := .ty ty, lifetime := slotLifetime })
      lv (.ty (.borrow mutable targets)) borrowLifetime := by
  intro hfree hbase htyping
  have hpartialFree :=
    LValTyping.update_fresh_root_partialTyBorrowFree hfree hbase htyping
  exact hpartialFree mutable targets PartialTyContains.here

/-- Borrow-free fresh-update coherence, with only old-root transport left open.

For fresh-root lvals the declared type contains no borrows, so a borrow-typed
lval rooted at the fresh variable is impossible.  Callers still have to supply
the old-root transport fact, which is the nontrivial part for lvals rooted in the
pre-existing environment.
-/
theorem FreshUpdateCoherenceObligations.of_tyBorrowFree
    {env : Env} {x : Name} {ty : Ty} {lifetime : Lifetime} :
    TyBorrowFree ty →
    (∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LVal.base lv ≠ x →
      LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
        lv (.ty (.borrow mutable targets)) borrowLifetime →
      ∃ oldBorrowLifetime,
        LValTyping env lv (.ty (.borrow mutable targets)) oldBorrowLifetime) →
    FreshUpdateCoherenceObligations env x ty lifetime := by
  intro hfree holdTransport
  refine ⟨?_, ?_⟩
  · intro lv mutable targets borrowLifetime hbase htyping
    exact holdTransport hbase htyping
  · intro lv mutable targets borrowLifetime hbase htyping
    exact False.elim
      (LValTyping.update_fresh_root_not_borrow_of_tyBorrowFree hfree hbase htyping)

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

theorem EnvContains.update_fresh_of_old {env : Env} {x y : Name} {slot : EnvSlot}
    {ty : Ty} :
    env.fresh x →
    env ⊢ y ↝ ty →
    (env.update x slot) ⊢ y ↝ ty := by
  intro hfresh hcontains
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  by_cases hy : y = x
  · subst hy
    rw [hfresh] at hslot
    cases hslot
  · exact ⟨containedSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩

theorem EnvContains.update_box_borrow_to_inner {env : Env} {gamma x : Name}
    {ty : Ty} {lifetime : Lifetime} {mutable : Bool} {targets : List LVal} :
    (env.update gamma { ty := .ty (.box ty), lifetime := lifetime }) ⊢ x ↝
      (Ty.borrow mutable targets) →
    (env.update gamma { ty := .ty ty, lifetime := lifetime }) ⊢ x ↝
      (Ty.borrow mutable targets) := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hx : x = gamma
  · subst hx
    have hslotEq :
        slot = { ty := PartialTy.ty (.box ty), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (.box ty), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    cases hcontainsTy with
    | tyBox hinner =>
        exact ⟨{ ty := PartialTy.ty ty, lifetime := lifetime },
          by simp [Env.update], hinner⟩
  · exact ⟨slot, by simpa [Env.update, hx] using hslot, hcontainsTy⟩

theorem pathConflicts_symm {left right : LVal} :
    left ⋈ right →
    right ⋈ left := by
  intro h
  exact h.symm

theorem pathConflicts_of_base_eq {target left right : LVal} :
    LVal.base left = LVal.base right →
    target ⋈ left →
    target ⋈ right := by
  intro hbase hconflict
  exact hconflict.trans hbase

theorem readProhibited_congr_base {env : Env} {left right : LVal} :
    LVal.base left = LVal.base right →
    (ReadProhibited env left ↔ ReadProhibited env right) := fun hbase => by
  constructor
  · intro hread
    rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    exact ⟨x, targets, target, hcontains, htarget,
      pathConflicts_of_base_eq hbase hconflict⟩
  · intro hread
    rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    exact ⟨x, targets, target, hcontains, htarget,
      pathConflicts_of_base_eq hbase.symm hconflict⟩

theorem writeProhibited_congr_base {env : Env} {left right : LVal} :
    LVal.base left = LVal.base right →
    (WriteProhibited env left ↔ WriteProhibited env right) := fun hbase => by
  constructor
  · intro hwrite
    cases hwrite with
    | inl hread =>
        exact Or.inl ((readProhibited_congr_base hbase).mp hread)
    | inr himm =>
        rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
        exact Or.inr ⟨x, targets, target, hcontains, htarget,
          pathConflicts_of_base_eq hbase hconflict⟩
  · intro hwrite
    cases hwrite with
    | inl hread =>
        exact Or.inl ((readProhibited_congr_base hbase).mpr hread)
    | inr himm =>
        rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
        exact Or.inr ⟨x, targets, target, hcontains, htarget,
          pathConflicts_of_base_eq hbase.symm hconflict⟩

theorem not_writeProhibited_var_base {env : Env} {lv : LVal} :
    ¬ WriteProhibited env lv →
    ¬ WriteProhibited env (.var (LVal.base lv)) := by
  intro hnot hwrite
  exact hnot ((writeProhibited_congr_base
    (env := env) (left := lv) (right := .var (LVal.base lv))
    (by simp [LVal.base])).mpr hwrite)

theorem partialTyContains_borrow_injective {partialTy : PartialTy}
    {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal} :
    PartialTyContains partialTy (.borrow mutable₁ targets₁) →
    PartialTyContains partialTy (.borrow mutable₂ targets₂) →
    mutable₁ = mutable₂ ∧ targets₁ = targets₂ := by
  revert mutable₁ mutable₂ targets₁ targets₂
  refine PartialTy.rec
    (motive_1 := fun ty =>
      ∀ {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal},
        PartialTyContains (.ty ty) (.borrow mutable₁ targets₁) →
        PartialTyContains (.ty ty) (.borrow mutable₂ targets₂) →
        mutable₁ = mutable₂ ∧ targets₁ = targets₂)
    (motive_2 := fun partialTy =>
      ∀ {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal},
        PartialTyContains partialTy (.borrow mutable₁ targets₁) →
        PartialTyContains partialTy (.borrow mutable₂ targets₂) →
        mutable₁ = mutable₂ ∧ targets₁ = targets₂)
    ?unit ?int ?borrow ?boxTy ?ty ?boxPartial ?undef partialTy
  · intro mutable₁ mutable₂ targets₁ targets₂ hleft
    cases hleft
  · intro mutable₁ mutable₂ targets₁ targets₂ hleft
    cases hleft
  · intro mutable targets mutable₁ mutable₂ targets₁ targets₂ hleft hright
    cases hleft with
    | here =>
        cases hright with
        | here =>
            exact ⟨rfl, rfl⟩
  · intro inner ih mutable₁ mutable₂ targets₁ targets₂ hleft hright
    cases hleft with
    | tyBox hleftInner =>
        cases hright with
        | tyBox hrightInner =>
            exact ih hleftInner hrightInner
  · intro ty ih mutable₁ mutable₂ targets₁ targets₂ hleft hright
    exact ih hleft hright
  · intro inner ih mutable₁ mutable₂ targets₁ targets₂ hleft hright
    cases hleft with
    | box hleftInner =>
        cases hright with
        | box hrightInner =>
            exact ih hleftInner hrightInner
  · intro shape _ih mutable₁ mutable₂ targets₁ targets₂ hleft
    cases hleft

theorem partialTyContains_mut_imm_false {partialTy : PartialTy}
    {mutableTargets immTargets : List LVal} :
    PartialTyContains partialTy (.borrow true mutableTargets) →
    PartialTyContains partialTy (.borrow false immTargets) →
    False := by
  intro hmut himm
  rcases partialTyContains_borrow_injective hmut himm with ⟨hbool, _htargets⟩
  cases hbool

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

theorem EnvContains.dropLifetime_of_contains {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    (env.dropLifetime lifetime) ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _hlifetime⟩
  exact ⟨slot, henvSlot, hcontainsTy⟩

/-- A result type is borrow-safe against an environment when installing it as a
new root would introduce no borrow-target conflict with any existing root.

This is the root-independent part of result-extension.  It avoids relying on
the existence of a globally fresh name, which is especially important for block
results: a name can be fresh after `dropLifetime` precisely because a block-local
slot with that name was removed. -/
def TyBorrowSafeAgainstEnv (env : Env) (ty : Ty) : Prop :=
  (∀ targetsMutable mutable targetsOther x targetMutable targetOther,
    PartialTyContains (.ty ty) (.borrow true targetsMutable) →
    env ⊢ x ↝ Ty.borrow mutable targetsOther →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False) ∧
  (∀ x targetsMutable mutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ Ty.borrow true targetsMutable →
    PartialTyContains (.ty ty) (.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False)

theorem tyBorrowSafeAgainstEnv_borrowFree {env : Env} {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowSafeAgainstEnv env ty := by
  intro hfree
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      _hother _htargetMutable _htargetOther _hconflict
    exact hfree true targetsMutable hcontains
  · intro x targetsMutable mutable targetsOther targetMutable targetOther _hcontainsMutable
      hcontains _htargetMutable _htargetOther _hconflict
    exact hfree mutable targetsOther hcontains

theorem TyBorrowSafeAgainstEnv.dropLifetime {env : Env} {ty : Ty}
    {lifetime : Lifetime} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv (env.dropLifetime lifetime) ty := by
  intro hsafeTy
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      hother htargetMutable htargetOther hconflict
    exact hsafeTy.1 targetsMutable mutable targetsOther x targetMutable targetOther
      hcontains (EnvContains.dropLifetime_of_contains hother)
      htargetMutable htargetOther hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther hcontainsMutable
      hcontains htargetMutable htargetOther hconflict
    exact hsafeTy.2 x targetsMutable mutable targetsOther targetMutable targetOther
      (EnvContains.dropLifetime_of_contains hcontainsMutable) hcontains
      htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env ty →
    BorrowSafeEnv (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hsafeTy a b mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases ha : a = x
  · subst a
    have hcontainsMutableAtX :
        (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢
          x ↝ Ty.borrow true targetsMutable := by
      simpa using hcontainsMutable
    rcases hcontainsMutableAtX with ⟨containedSlot, hslot, hcontainsTy⟩
    have hslotEq :
        containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    by_cases hb : b = x
    · exact hb.symm
    · exact False.elim
        (hsafeTy.1 targetsMutable mutable targetsOther b targetMutable targetOther
          hcontainsTy
          (EnvContains.update_fresh_ne hb hcontainsOther)
          htargetMutable htargetOther hconflict)
  · by_cases hb : b = x
    · subst b
      have hcontainsOtherAtX :
          (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢
            x ↝ Ty.borrow mutable targetsOther := by
        simpa using hcontainsOther
      rcases hcontainsOtherAtX with ⟨containedSlot, hslot, hcontainsTy⟩
      have hslotEq :
          containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      exact False.elim
        (hsafeTy.2 a targetsMutable mutable targetsOther targetMutable targetOther
          (EnvContains.update_fresh_ne ha hcontainsMutable)
          hcontainsTy htargetMutable htargetOther hconflict)
    · exact hsafe a b mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne ha hcontainsMutable)
        (EnvContains.update_fresh_ne hb hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_of_update_fresh {env : Env} {x : Name} {slot : EnvSlot} :
    env.fresh x →
    BorrowSafeEnv (env.update x slot) →
    BorrowSafeEnv env := by
  intro hfresh hsafe y z mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe y z mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.update_fresh_of_old hfresh hcontainsMutable)
    (EnvContains.update_fresh_of_old hfresh hcontainsOther)
    htargetMutable htargetOther hconflict

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

theorem LValTyping.var_dropLifetime_child {env : Env} {parent child : Lifetime}
    {x : Name} {slot : EnvSlot} :
    LifetimeChild parent child →
    env.slotAt x = some slot →
    slot.lifetime ≤ parent →
    LValTyping (env.dropLifetime child) (.var x) slot.ty slot.lifetime := by
  intro hchild hslot houtlivesParent
  exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
    ⟨hslot, by
      intro hslotLifetime
      subst hslotLifetime
      exact LifetimeChild.not_child_outlives_parent hchild houtlivesParent⟩)

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

theorem Env.dropLifetime_update_ne {env : Env} {x : Name} {slot : EnvSlot}
    {dropped : Lifetime} :
    slot.lifetime ≠ dropped →
    (env.update x slot).dropLifetime dropped =
      (env.dropLifetime dropped).update x slot := by
  intro hslotLifetime
  cases env with
  | mk slotAt =>
      simp only [Env.dropLifetime, Env.update]
      congr
      funext y
      by_cases hy : y = x
      · subst hy
        simp [hslotLifetime]
      · simp [hy]

theorem borrowSafeEnv_dropLifetime_update_of_update {env : Env} {x : Name}
    {slot : EnvSlot} {dropped : Lifetime} :
    slot.lifetime ≠ dropped →
    BorrowSafeEnv (env.update x slot) →
    BorrowSafeEnv ((env.dropLifetime dropped).update x slot) := by
  intro hslotLifetime hsafe
  have hdropSafe :
      BorrowSafeEnv ((env.update x slot).dropLifetime dropped) :=
    borrowSafeEnv_dropLifetime hsafe
  rwa [Env.dropLifetime_update_ne hslotLifetime] at hdropSafe

theorem borrowSafeEnv_block_result_extension_of_body_extension {env₂ env₃ : Env}
    {lifetime blockLifetime : Lifetime} {ty : Ty} {gamma : Name} :
    LifetimeChild lifetime blockLifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) →
    BorrowSafeEnv (env₃.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hchild hdrop hbodySafe
  rw [hdrop]
  exact borrowSafeEnv_dropLifetime_update_of_update
    (x := gamma)
    (slot := { ty := .ty ty, lifetime := lifetime })
    (by
      intro hEq
      exact LifetimeChild.ne hchild hEq)
    hbodySafe

theorem borrowSafety_copy {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {lv : LVal} {ty : Ty} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    BorrowSafeEnv env₂ := by
  intro hsafe htyping
  cases htyping
  exact hsafe

theorem LValTyping.no_readProhibited_targets_of_immBorrow {env : Env} :
    BorrowSafeEnv env →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {borrowTargets},
        PartialTyContains partialTy (.borrow false borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ ReadProhibited env target) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {borrowTargets},
        PartialTyContains partialTy (.borrow false borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ ReadProhibited env target) := by
  intro hsafe
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (motive_2 := fun targets partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (by
        intro x slot hslot borrowTargets hcontains target htarget hread
        rcases hread with
          ⟨borrower, mutableTargets, mutableTarget, hmutableContains,
            hmutableTarget, hconflict⟩
        by_cases hsame : borrower = x
        · subst hsame
          rcases hmutableContains with ⟨mutableSlot, hmutableSlot, hmutableTy⟩
          rw [hslot] at hmutableSlot
          injection hmutableSlot with hslotEq
          subst hslotEq
          exact partialTyContains_mut_imm_false hmutableTy hcontains
        · have hsafeContradiction :
              borrower = x := by
            exact hsafe borrower x false mutableTargets borrowTargets
              mutableTarget target
              hmutableContains
              ⟨slot, hslot, hcontains⟩
              hmutableTarget
              htarget
              hconflict
          exact hsame hsafeContradiction)
      (by
        intro _lv _inner _lifetime _htyping ih borrowTargets hcontains target
          htarget hread
        exact ih (PartialTyContains.box hcontains) target htarget hread)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets borrowTargets hcontains target
          htarget hread
        exact ihTargets hcontains target htarget hread)
      (by
        intro target ty lifetime _htarget ihTarget borrowTargets hcontains selected
          hselected hread
        exact ihTarget hcontains selected hselected hread)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion _hintersection ihHead ihRest borrowTargets hcontains
          selected hselected hread
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead hread
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest hread)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (motive_2 := fun targets partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (by
        intro x slot hslot borrowTargets hcontains target htarget hread
        rcases hread with
          ⟨borrower, mutableTargets, mutableTarget, hmutableContains,
            hmutableTarget, hconflict⟩
        by_cases hsame : borrower = x
        · subst hsame
          rcases hmutableContains with ⟨mutableSlot, hmutableSlot, hmutableTy⟩
          rw [hslot] at hmutableSlot
          injection hmutableSlot with hslotEq
          subst hslotEq
          exact partialTyContains_mut_imm_false hmutableTy hcontains
        · have hsafeContradiction :
              borrower = x := by
            exact hsafe borrower x false mutableTargets borrowTargets
              mutableTarget target
              hmutableContains
              ⟨slot, hslot, hcontains⟩
              hmutableTarget
              htarget
              hconflict
          exact hsame hsafeContradiction)
      (by
        intro _lv _inner _lifetime _htyping ih borrowTargets hcontains target
          htarget hread
        exact ih (PartialTyContains.box hcontains) target htarget hread)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets borrowTargets hcontains target
          htarget hread
        exact ihTargets hcontains target htarget hread)
      (by
        intro target ty lifetime _htarget ihTarget borrowTargets hcontains selected
          hselected hread
        exact ihTarget hcontains selected hselected hread)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion _hintersection ihHead ihRest borrowTargets hcontains
          selected hselected hread
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead hread
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest hread)
      htyping

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

theorem borrowSafeEnv_update_fresh_mutBorrow {env : Env} {gamma : Name}
    {lv : LVal} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    ¬ WriteProhibited env lv →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) := by
  intro hsafe _hfresh hnotWrite x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq : Ty.borrow true [lv] = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    injection hborrowEq with _hmut htargetsMutable
    subst htargetsMutable
    have htargetMutableEq : targetMutable = lv := by
      simpa using htargetMutable
    have hconflictLv : lv ⋈ targetOther := by
      simpa [htargetMutableEq] using hconflict
    by_cases hy : y = gamma
    · exact hx.trans hy.symm
    · have hcontainsOtherOld : env ⊢ y ↝ Ty.borrow mutable targetsOther :=
        EnvContains.update_fresh_ne hy hcontainsOther
      have hwrite : WriteProhibited env lv := by
        cases mutable with
        | false =>
            exact Or.inr ⟨y, targetsOther, targetOther, hcontainsOtherOld,
              htargetOther, pathConflicts_symm hconflictLv⟩
        | true =>
            exact Or.inl ⟨y, targetsOther, targetOther, hcontainsOtherOld,
              htargetOther, pathConflicts_symm hconflictLv⟩
      exact False.elim (hnotWrite hwrite)
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq : Ty.borrow true [lv] = Ty.borrow mutable targetsOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargetsOther
      subst htargetsOther
      have htargetOtherEq : targetOther = lv := by
        simpa using htargetOther
      have hconflictLv : targetMutable ⋈ lv := by
        simpa [htargetOtherEq] using hconflict
      have hcontainsMutableOld : env ⊢ x ↝ Ty.borrow true targetsMutable :=
        EnvContains.update_fresh_ne hx hcontainsMutable
      have hwrite : WriteProhibited env lv :=
        Or.inl ⟨x, targetsMutable, targetMutable, hcontainsMutableOld,
          htargetMutable, hconflictLv⟩
      exact False.elim (hnotWrite hwrite)
    · exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

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
      partialTyContains_borrow_iff_eq.mp hcontainsTy
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
        partialTyContains_borrow_iff_eq.mp hcontainsTy
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

theorem borrowSafeEnv_update_fresh_immBorrowMany {env : Env} {gamma : Name}
    {targets : List LVal} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    (∀ target, target ∈ targets → ¬ ReadProhibited env target) →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow false targets), lifetime := lifetime }) := by
  intro hsafe hfresh hnotRead x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow false targets), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq :
        Ty.borrow false targets = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    cases hborrowEq
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow false targets), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq :
          Ty.borrow false targets = Ty.borrow mutable targetsOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargets
      subst htargets
      exact False.elim
        (hnotRead targetOther htargetOther
          ⟨x, targetsMutable, targetMutable,
            EnvContains.update_fresh_ne hx hcontainsMutable,
            htargetMutable,
            hconflict⟩)
    · exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem tyBorrowSafeAgainstEnv_mutBorrow {env : Env} {lv : LVal} :
    ¬ WriteProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow true [lv]) := by
  intro hnotWrite
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      hother htargetMutable htargetOther hconflict
    have hborrowEq : Ty.borrow true [lv] = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmut htargetsMutable
    subst htargetsMutable
    have htargetMutableEq : targetMutable = lv := by
      simpa using htargetMutable
    have hconflictLv : lv ⋈ targetOther := by
      simpa [htargetMutableEq] using hconflict
    have hwrite : WriteProhibited env lv := by
      cases mutable with
      | false =>
          exact Or.inr ⟨x, targetsOther, targetOther, hother,
            htargetOther, pathConflicts_symm hconflictLv⟩
      | true =>
          exact Or.inl ⟨x, targetsOther, targetOther, hother,
            htargetOther, pathConflicts_symm hconflictLv⟩
    exact hnotWrite hwrite
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable hcontains htargetMutable htargetOther hconflict
    have hborrowEq : Ty.borrow true [lv] = Ty.borrow mutable targetsOther :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmutable htargetsOther
    subst htargetsOther
    have htargetOtherEq : targetOther = lv := by
      simpa using htargetOther
    have hconflictLv : targetMutable ⋈ lv := by
      simpa [htargetOtherEq] using hconflict
    exact hnotWrite
      (Or.inl ⟨x, targetsMutable, targetMutable, hcontainsMutable,
        htargetMutable, hconflictLv⟩)

theorem tyBorrowSafeAgainstEnv_immBorrowMany {env : Env} {targets : List LVal} :
    (∀ target, target ∈ targets → ¬ ReadProhibited env target) →
    TyBorrowSafeAgainstEnv env (.borrow false targets) := by
  intro hnotRead
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      _hother _htargetMutable _htargetOther _hconflict
    have hborrowEq :
        Ty.borrow false targets = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontains
    cases hborrowEq
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable hcontains htargetMutable htargetOther hconflict
    have hborrowEq :
        Ty.borrow false targets = Ty.borrow mutable targetsOther :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmutable htargets
    subst htargets
    exact hnotRead targetOther htargetOther
      ⟨x, targetsMutable, targetMutable, hcontainsMutable,
        htargetMutable, hconflict⟩

theorem tyBorrowSafeAgainstEnv_immBorrow {env : Env} {lv : LVal} :
    ¬ ReadProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow false [lv]) := by
  intro hnotRead
  exact tyBorrowSafeAgainstEnv_immBorrowMany
    (by
      intro target htarget
      have htargetEq : target = lv := by
        simpa using htarget
      subst htargetEq
      exact hnotRead)

theorem PartialTyContains.tyBox_borrow_inv {inner : Ty} {mutable : Bool}
    {targets : List LVal} :
    PartialTyContains (.ty (.box inner)) (.borrow mutable targets) →
    PartialTyContains (.ty inner) (.borrow mutable targets) := by
  intro hcontains
  cases hcontains with
  | tyBox hinner => exact hinner

theorem TyBorrowSafeAgainstEnv.box {env : Env} {ty : Ty} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv env (.box ty) := by
  intro hsafeTy
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      hother htargetMutable htargetOther hconflict
    exact hsafeTy.1 targetsMutable mutable targetsOther x targetMutable targetOther
      (PartialTyContains.tyBox_borrow_inv hcontains) hother
      htargetMutable htargetOther hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther hcontainsMutable
      hcontains htargetMutable htargetOther hconflict
    exact hsafeTy.2 x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable (PartialTyContains.tyBox_borrow_inv hcontains)
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

theorem borrowSafety_mutBorrow_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow true lv) (.borrow true [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) := by
  intro hsafe htyping hfresh
  cases htyping with
  | mutBorrow _hLv _hmutable hnotWrite =>
      exact borrowSafeEnv_update_fresh_mutBorrow hsafe hfresh hnotWrite

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
  | block _hblockChild hterms _hwellTy hdrop =>
      exact borrowSafety_block_drop (htermsSafe _ hterms) hdrop

/--
Borrow-free result extension with the fresh-coherence gap exposed.

The fresh-root coherence case is discharged by `TyBorrowFree`; the only
remaining well-formedness premise is old-root transport for borrow typings in
the extended environment.  This is the axiom-clean replacement shape for the
legacy `borrowSafety_result_extension_borrowFree` below.
-/
theorem borrowSafety_result_extension_borrowFree_of_oldRootTransport {env : Env}
    {gamma : Name} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env.fresh gamma →
    (∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LVal.base lv ≠ gamma →
      LValTyping (env.update gamma { ty := .ty ty, lifetime := lifetime })
        lv (.ty (.borrow mutable targets)) borrowLifetime →
      ∃ oldBorrowLifetime,
        LValTyping env lv (.ty (.borrow mutable targets)) oldBorrowLifetime) →
    WellFormedEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hwellFormed hwellTy hborrowSafe hborrowFree hfresh holdTransport
  exact ⟨
    borrowInvariance_result_extension_of_coherenceObligations
      hwellFormed hwellTy hfresh
      (FreshUpdateCoherenceObligations.of_tyBorrowFree hborrowFree holdTransport),
    borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree⟩

/--
Corollary 4.14 support: extending the output environment with a fresh,
borrow-free result slot preserves both well-formedness and borrow safety.

The remaining borrow-safety work is the paper's typing-rule induction showing
that the output environment of a well-typed term is itself borrow safe.  This
theorem packages the final result-extension step from the corollary.

This is a legacy shortcut: its well-formedness half goes through
`borrowInvariance_result_extension`, which depends on `Coherent.update_fresh_ty`.
Use `borrowSafety_result_extension_borrowFree_of_oldRootTransport` when the
old-root transport obligation is available.
-/
theorem borrowSafety_result_extension_borrowFree {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env.fresh gamma →
    FreshUpdateCoherenceObligations env gamma ty lifetime →
    WellFormedEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hwellFormed hwellTy hborrowSafe hborrowFree hfresh hfreshCoherence
  exact ⟨borrowInvariance_result_extension hwellFormed hwellTy hfresh hfreshCoherence,
    borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree⟩

theorem borrowSafety_result_extension_unit {env : Env} {gamma : Name}
    {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    env.fresh gamma →
    FreshUpdateCoherenceObligations env gamma .unit lifetime →
    WellFormedEnv (env.update gamma { ty := .ty .unit, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty .unit, lifetime := lifetime }) := by
  intro hwellFormed hborrowSafe hfresh hfreshCoherence
  exact borrowSafety_result_extension_borrowFree hwellFormed WellFormedTy.unit
    hborrowSafe tyBorrowFree_unit hfresh hfreshCoherence

theorem borrowSafeEnv_update_box_of_update_inner {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) →
    BorrowSafeEnv (env.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.update_box_borrow_to_inner hcontainsMutable)
    (EnvContains.update_box_borrow_to_inner hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafety_result_extension_box_of_inner {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) →
    env.fresh gamma →
    FreshUpdateCoherenceObligations env gamma (.box ty) lifetime →
    WellFormedEnv (env.update gamma { ty := .ty (.box ty), lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro hwellFormed hwellTy hinnerSafe hfresh hfreshCoherence
  exact ⟨borrowInvariance_result_extension hwellFormed
      (WellFormedTy.box hwellTy) hfresh hfreshCoherence,
    borrowSafeEnv_update_box_of_update_inner hinnerSafe⟩

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
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro htyping hwellFormed hwellTy hborrowSafe hborrowFree hfresh hfreshCoherence
  have henv : env = env₂ := valueTyping_environment_eq htyping
  subst henv
  exact borrowSafety_result_extension_borrowFree hwellFormed hwellTy hborrowSafe
    hborrowFree hfresh hfreshCoherence

theorem borrowSafe_value_result_extension_borrowFree {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty}
    {gamma : Name} :
    TermTyping env typing lifetime (.val value) ty env₂ →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro htyping hborrowSafe hborrowFree hfresh
  have henv : env = env₂ := valueTyping_environment_eq htyping
  subst henv
  exact borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree

/-! ## Source-Level Initial States -/

def SourceValue : Value → Prop
  | .unit => True
  | .int _ => True
  | .ref _ => False

def SourceTerm (term : Term) : Prop :=
  ∀ value, value ∈ termValues term → SourceValue value

theorem SourceTerm.block_head {lifetime : Lifetime} {term : Term}
    {rest : List Term} :
    SourceTerm (.block lifetime (term :: rest)) →
    SourceTerm term := by
  intro hsource value hmem
  exact hsource value
    (by
      simp [termValues, hmem])

theorem SourceTerm.block_tail {lifetime : Lifetime} {term : Term}
    {rest : List Term} :
    SourceTerm (.block lifetime (term :: rest)) →
    SourceTerm (.block lifetime rest) := by
  intro hsource value hmem
  exact hsource value
    (by
      simp [termValues] at hmem ⊢
      exact Or.inr hmem)

theorem SourceTerm.box_inner {term : Term} :
    SourceTerm (.box term) →
    SourceTerm term := by
  intro hsource value hmem
  exact hsource value (by simpa [termValues] using hmem)

theorem SourceTerm.declare_inner {x : Name} {term : Term} :
    SourceTerm (.letMut x term) →
    SourceTerm term := by
  intro hsource value hmem
  exact hsource value (by simpa [termValues] using hmem)

theorem SourceTerm.assign_inner {lhs : LVal} {rhs : Term} :
    SourceTerm (.assign lhs rhs) →
    SourceTerm rhs := by
  intro hsource value hmem
  exact hsource value (by simpa [termValues] using hmem)

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

theorem sourceValue_valueTyping_borrowFree {typing : StoreTyping} {value : Value}
    {ty : Ty} :
    SourceValue value →
    ValueTyping typing value ty →
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
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource htyping hwellTy hfresh hfreshCoherence
  cases htyping with
  | const hvalueTyping =>
      exact borrowSafety_value_result_extension_borrowFree
        (TermTyping.const hvalueTyping)
        (wellFormedEnv_empty lifetime)
        hwellTy
        borrowSafeEnv_empty
        (sourceValue_empty_valueTyping_borrowFree hsource hvalueTyping)
        hfresh
        hfreshCoherence

theorem sourceInitial_box_value_borrowSafety_result_extension
    {value : Value} {ty : Ty} {env₂ : Env} {lifetime : Lifetime}
    {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma (.box ty) lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty (.box ty), lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro _hsource htyping hfresh hfreshCoherence
  cases htyping with
  | box hinner =>
      cases hinner with
      | const hvalueTyping =>
          have hinnerFree : TyBorrowFree ty :=
            sourceValue_empty_valueTyping_borrowFree _hsource hvalueTyping
          have hwellTy : WellFormedTy Env.empty ty lifetime := by
            cases hvalueTyping with
            | unit =>
                exact WellFormedTy.unit
            | int =>
                exact WellFormedTy.int
            | ref hlookup =>
                simp [StoreTyping.empty] at hlookup
          have hinnerSafe :
              BorrowSafeEnv
                (Env.empty.update gamma { ty := .ty ty, lifetime := lifetime }) :=
            borrowSafeEnv_update_fresh_borrowFree borrowSafeEnv_empty hinnerFree
          exact borrowSafety_result_extension_box_of_inner
            (wellFormedEnv_empty lifetime)
            hwellTy
            hinnerSafe
            hfresh
            hfreshCoherence

theorem sourceInitial_declare_value_borrowSafety_result_extension
    {x : Name} {value : Value} {env₃ : Env} {lifetime : Lifetime}
    {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    env₃.fresh gamma →
    FreshUpdateCoherenceObligations env₃ gamma .unit lifetime →
    WellFormedEnv (env₃.update gamma { ty := .ty .unit, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₃.update gamma { ty := .ty .unit, lifetime := lifetime }) := by
  intro hsource htyping hfreshGamma hfreshGammaCoherence
  cases htyping with
  | declare hfresh hinit _hfreshOut hcoh henv₃ =>
      cases hinit with
      | const hvalueTyping =>
          rename_i initTy
          have hwellTy : WellFormedTy Env.empty initTy lifetime := by
            cases hvalueTyping with
            | unit =>
                exact WellFormedTy.unit
            | int =>
                exact WellFormedTy.int
            | ref hlookup =>
                simp [StoreTyping.empty] at hlookup
          have hdeclared :
              WellFormedEnv
                  (Env.empty.update x { ty := .ty initTy, lifetime := lifetime })
                  lifetime ∧
            BorrowSafeEnv
                  (Env.empty.update x { ty := .ty initTy, lifetime := lifetime }) := by
            exact sourceInitial_value_borrowSafety_result_extension hsource
              (TermTyping.const hvalueTyping) hwellTy hfresh hcoh
          have hfreshGamma' :
              (Env.empty.update x { ty := .ty initTy, lifetime := lifetime }).fresh
                gamma := by
            simpa [henv₃] using hfreshGamma
          rw [henv₃]
          exact borrowSafety_result_extension_borrowFree
            hdeclared.1
            WellFormedTy.unit
            hdeclared.2
            tyBorrowFree_unit
            hfreshGamma'
            (by simpa [henv₃] using hfreshGammaCoherence)

theorem sourceInitial_blockB_value_borrowSafety_result_extension
    {value : Value} {ty : Ty} {env₂ : Env}
    {lifetime blockLifetime : Lifetime} {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime
      (.block blockLifetime [.val value]) ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource htyping hfresh hfreshCoherence
  cases htyping with
  | block _hblockChild hterms hwellTy hdrop =>
      have hvalueTyping := termListTyping_singleton_value_valueTyping hterms
      have henvList : Env.empty = _ :=
        termListTyping_singleton_value_environment_eq hterms
      subst henvList
      have hdropEmpty : env₂ = Env.empty := by
        simpa [Env.dropLifetime, Env.empty] using hdrop
      subst hdropEmpty
      exact borrowSafety_result_extension_borrowFree
        (wellFormedEnv_empty lifetime)
        hwellTy
        borrowSafeEnv_empty
        (sourceValue_empty_valueTyping_borrowFree hsource hvalueTyping)
        hfresh
        hfreshCoherence

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
The exact well-formedness invariant needed for runtime references in `T-Const`.

`ValueTyping` for references only consults `σ`; it does not itself say that the
type stored in `σ` is well formed in the current environment.  This predicate
names that missing bridge explicitly.
-/
def StoreTypingRefsWellFormed
    (env : Env) (typing : StoreTyping) (lifetime : Lifetime) : Prop :=
  ∀ (ref : Reference) (ty : Ty),
    typing.tyOf ref.location = some ty →
    WellFormedTy env ty lifetime

/-- `T-Const` value well-formedness from an explicit reference-store invariant. -/
theorem valueTyping_result_wellFormed_of_refs {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreTypingRefsWellFormed env typing lifetime →
    ValueTyping typing value ty →
    WellFormedTy env ty lifetime := by
  intro hrefs htyping
  cases htyping with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | ref hlookup =>
      exact hrefs _ _ hlookup

@[simp] theorem storeTypingRefsWellFormed_empty (env : Env) (lifetime : Lifetime) :
    StoreTypingRefsWellFormed env StoreTyping.empty lifetime := by
  intro ref ty hlookup
  simp [StoreTyping.empty] at hlookup

theorem valueTyping_empty_result_wellFormed {env : Env}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValueTyping StoreTyping.empty value ty →
    WellFormedTy env ty lifetime := by
  intro htyping
  exact valueTyping_result_wellFormed_of_refs
    (storeTypingRefsWellFormed_empty env lifetime) htyping

theorem LValTyping.containedBorrowTargetsWellFormed {env : Env} {lv : LVal}
    {partialTy : PartialTy} {mutable : Bool} {targets : List LVal}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed htyping hcontainsTop
  exact LValTyping.rec
    (motive_1 := fun _lv partialTy _ _ =>
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime)
    (motive_2 := fun _targetLvs unionTy _ _ =>
      ∀ {mutable targets},
        PartialTyContains unionTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime)
    (by
      intro x slot hslot mutable targets hcontains
      exact EnvContains.borrowTargetsWellFormed hwellFormed
        ⟨slot, hslot, hcontains⟩)
    (by
      intro _lv inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _mutableBorrow _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets _ihBorrow ihTargets _mutable _targets
        hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
        _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
        _mutable _targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion
          (by
            intro mutable targets hcontainsHead
            exact BorrowTargetsWellFormed.inSlot (ihHead hcontainsHead))
          (by
            intro mutable targets hcontainsRest
            exact BorrowTargetsWellFormed.inSlot (ihRest hcontainsRest))
          hcontains)
        (LifetimeOutlives.refl lifetime))
    htyping
    hcontainsTop

theorem LValTyping.containedBorrowTargetsWellFormed_at_lifetime {env : Env}
    {lv : LVal} {partialTy : PartialTy} {valueLifetime : Lifetime}
    {mutable : Bool} {targets : List LVal} :
    ContainedBorrowsWellFormed env →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormed env targets valueLifetime := by
  intro hcontained htyping hcontainsTop
  exact LValTyping.rec
    (motive_1 := fun _lv partialTy valueLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets valueLifetime)
    (motive_2 := fun _targetLvs unionTy targetLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains unionTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets targetLifetime)
    (by
      intro x slot hslot mutable targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (hcontained x slot mutable targets hslot ⟨slot, hslot, hcontains⟩)
        (LifetimeOutlives.refl slot.lifetime))
    (by
      intro _lv _inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _mutableBorrow _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets _ihBorrow ihTargets _mutable _targets
        hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
        _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
        _mutable _targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion
          (by
            intro mutable targets hcontainsHead
            exact BorrowTargetsWellFormedInSlot.weaken
              (BorrowTargetsWellFormed.inSlot (ihHead hcontainsHead))
              (LifetimeIntersection.left_le hintersection))
          (by
            intro mutable targets hcontainsRest
            exact BorrowTargetsWellFormedInSlot.weaken
              (BorrowTargetsWellFormed.inSlot (ihRest hcontainsRest))
              (LifetimeIntersection.right_le hintersection))
          hcontains)
        (LifetimeOutlives.refl _))
    htyping
    hcontainsTop

theorem LValTyping.lifetime_outlives_of_base_outlives {env : Env}
    {current : Lifetime} :
    ContainedBorrowsWellFormed env →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      LValBaseOutlives env lv current →
      lifetime ≤ current) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → LValBaseOutlives env target current) →
      lifetime ≤ current) := by
  intro hcontained
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormed env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormed_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormed env targets current :=
          BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget⟩
          exact hbaseTarget))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormed env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormed_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormed env targets current :=
          BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget⟩
          exact hbaseTarget))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping

theorem LValTyping.lifetime_outlives_of_base_outlives_one {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    LValTyping env lv partialTy lifetime →
    LValBaseOutlives env lv current →
    lifetime ≤ current := by
  intro hcontained htyping hbase
  exact (LValTyping.lifetime_outlives_of_base_outlives
    (current := current) hcontained).1 htyping hbase

theorem TermTyping.target_lifetime_outlives_surviving_base_slot {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lv : LVal} {oldTy : PartialTy} {term : Term} {ty : Ty}
    {resultSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    LValTyping env₁ lv oldTy targetLifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.slotAt (LVal.base lv) = some resultSlot →
    targetLifetime ≤ resultSlot.lifetime := by
  intro hwellInitial hLv hterm hresultSlot
  rcases LValTyping.base_outlives_one hwellInitial hLv with
    ⟨sourceSlot, hsourceSlot, hsourceOutlivesCurrent⟩
  have hbaseSelf : LValBaseOutlives env₁ lv sourceSlot.lifetime :=
    ⟨sourceSlot, hsourceSlot, LifetimeOutlives.refl sourceSlot.lifetime⟩
  have htargetOutlivesSource :
      targetLifetime ≤ sourceSlot.lifetime :=
    LValTyping.lifetime_outlives_of_base_outlives_one
      hwellInitial.1 hLv hbaseSelf
  rcases (TermTyping.slot_lifetime_survives.1 hterm)
      hsourceOutlivesCurrent hsourceSlot with
    ⟨survivedSlot, hsurvivedSlot, hsurvivedLifetime⟩
  have hslotEq : survivedSlot = resultSlot := by
    have hsomeEq : some survivedSlot = some resultSlot := by
      rw [← hsurvivedSlot, hresultSlot]
    exact Option.some.inj hsomeEq
  rw [← hslotEq, ← hsurvivedLifetime]
  exact htargetOutlivesSource

theorem LValTyping.borrowTargetsWellFormed {env : Env} {lv : LVal}
    {mutable : Bool} {targets : List LVal}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty (.borrow mutable targets)) valueLifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed htyping
  exact LValTyping.containedBorrowTargetsWellFormed hwellFormed htyping
    PartialTyContains.here

theorem wellFormedTy_of_containedBorrowTargets {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      BorrowTargetsWellFormed env targets lifetime) →
    WellFormedTy env ty lifetime := by
  intro htargets
  exact Ty.rec
    (motive_1 := fun ty =>
      (∀ mutable targets,
        PartialTyContains (.ty ty) (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime) →
      WellFormedTy env ty lifetime)
    (motive_2 := fun _partialTy => True)
    (by
      intro _htargets
      exact WellFormedTy.unit)
    (by
      intro _htargets
      exact WellFormedTy.int)
    (by
      intro mutable targets htargets
      exact WellFormedTy.borrow (htargets mutable targets PartialTyContains.here))
    (by
      intro inner ih htargets
      exact WellFormedTy.box (ih (by
        intro mutable targets hcontains
        exact htargets mutable targets (PartialTyContains.tyBox hcontains))))
    (by
      intro _ty _ih
      trivial)
    (by
      intro _partialTy _ih
      trivial)
    (by
      intro _shape _ih
      trivial)
    ty htargets

theorem LValTyping.fullTyWellFormed {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    WellFormedTy env ty lifetime := by
  intro hwellFormed htyping
  exact wellFormedTy_of_containedBorrowTargets (by
    intro mutable targets hcontains
    exact LValTyping.containedBorrowTargetsWellFormed hwellFormed htyping
      hcontains)

/--
The `T-Copy` result type is well formed.

This is intentionally specialized by `copy(T)`: copyable types are only `int`
and immutable borrows, so we do not need a false theorem saying every full type
read from an lval is recursively well formed.
-/
theorem copyBorrowTargetsWellFormed {env : Env} {lv : LVal}
    {targets : List LVal} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty (.borrow false targets)) valueLifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed hLv
  exact LValTyping.borrowTargetsWellFormed hwellFormed hLv

theorem copyTy_result_wellFormed {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    CopyTy ty →
    WellFormedTy env ty lifetime := by
  intro hwellFormed hLv hcopy
  cases hcopy with
  | int =>
      exact WellFormedTy.int
  | immBorrow =>
      exact WellFormedTy.borrow
        (copyBorrowTargetsWellFormed hwellFormed hLv)

theorem PartialTyContains.of_strike {path : Path} {source struck : PartialTy}
    {needle : Ty} :
    Strike path source struck →
    PartialTyContains struck needle →
    PartialTyContains source needle := by
  intro hstrike hcontains
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains
  | cons _ path ih =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains with
      | box hinner =>
          exact PartialTyContains.box (ih hstrike hinner)

/-- A struck partial type contains no live full type.

`Strike` replaces the moved leaf by `undef` and only rebuilds boxes on the way
back to the root, so no `PartialTyContains` derivation can start from the struck
result. -/
theorem PartialTyContains.not_strike_result {path : Path} {source struck : PartialTy}
    {needle : Ty} :
    Strike path source struck →
    ¬ PartialTyContains struck needle := by
  intro hstrike hcontains
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains
  | cons _ path ih =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains with
      | box hinner =>
          exact ih hstrike hinner

theorem LVal.path_deref_append (lv : LVal) (suffix : Path) :
    LVal.path (.deref lv) ++ suffix = LVal.path lv ++ (() :: suffix) := by
  rw [LVal.path, List.append_assoc]
  rfl

theorem List.Unit_cons_append_eq_append_cons (path suffix : List Unit) :
    () :: (path ++ suffix) = path ++ (() :: suffix) := by
  induction path with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head
      simp [ih]

/-- A `Strike` following an lvalue path can be decomposed at the partial type
selected by the lvalue typing derivation.

The borrow-dereference case is where this lemma pays for itself: `Strike` can
only step through `PartialTy.box`, so it cannot take one more selector after an
lvalue whose selected type is a full borrow. -/
theorem LValTyping.strike_suffix_at_type {env : Env} :
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {slot struck suffix},
        env.slotAt (LVal.base lv) = some slot →
        Strike (LVal.path lv ++ suffix) slot.ty struck →
        ∃ struckAt, Strike suffix partialTy struckAt) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime → True) := by
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy _lifetime _ =>
        ∀ {slot struck suffix},
          env.slotAt (LVal.base lv) = some slot →
          Strike (LVal.path lv ++ suffix) slot.ty struck →
          ∃ struckAt, Strike suffix partialTy struckAt)
      (motive_2 := fun _targets _partialTy _lifetime _ => True)
      (by
        intro x envSlot hslot slot struck suffix hbase hstrike
        have hbase' : env.slotAt x = some slot := by
          simpa [LVal.base] using hbase
        have hslotEq : envSlot = slot := by
          have hsomeEq : some envSlot = some slot := by
            rw [← hslot, hbase']
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact ⟨struck, by simpa [LVal.path] using hstrike⟩)
      (by
        intro lv inner lifetime _htyping ih slot struck suffix hbase hstrike
        have hstrikeAtParent :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        rcases ih hbase hstrikeAtParent with ⟨parentStruck, hparentStruck⟩
        cases parentStruck with
        | ty parentTy =>
            simp [Strike] at hparentStruck
        | box innerStruck =>
            exact ⟨innerStruck, by simpa [Strike] using hparentStruck⟩
        | undef parentTy =>
            simp [Strike] at hparentStruck)
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          _hborrow _htargets ihBorrow _ihTargets slot struck suffix hbase hstrike
        have hstrikeAtBorrow :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        rcases ihBorrow hbase hstrikeAtBorrow with ⟨borrowStruck, hborrowStruck⟩
        simp [Strike] at hborrowStruck)
      (by
        intro target ty lifetime _htarget _ihTarget
        trivial)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest _hunion _hintersection _ihHead _ihRest
        trivial)
      htyping
  · intro targets partialTy lifetime _htyping
    trivial

/-- If an lvalue is moved by `Strike`, every borrow contained in its selected
partial type was already contained in the moved base slot.

This is the static origin fact needed for non-variable move result-extension.
The proof follows the lvalue spine.  Box dereferences push the obligation one
selector back toward the base slot; borrow dereferences are impossible because
`Strike` cannot continue below a full borrow leaf. -/
theorem LValTyping.contains_base_of_strike_suffix {env : Env} :
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {slot struck suffix needle},
        env.slotAt (LVal.base lv) = some slot →
        Strike (LVal.path lv ++ suffix) slot.ty struck →
        PartialTyContains partialTy needle →
        env ⊢ LVal.base lv ↝ needle) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime → True) := by
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy _lifetime _ =>
        ∀ {slot struck suffix needle},
          env.slotAt (LVal.base lv) = some slot →
          Strike (LVal.path lv ++ suffix) slot.ty struck →
          PartialTyContains partialTy needle →
          env ⊢ LVal.base lv ↝ needle)
      (motive_2 := fun _targets _partialTy _lifetime _ => True)
      (by
        intro x envSlot hslot slot _struck _suffix needle hbase _hstrike hcontains
        have hbase' : env.slotAt x = some slot := by
          simpa [LVal.base] using hbase
        have hslotEq : envSlot = slot := by
          have hsomeEq : some envSlot = some slot := by
            rw [← hslot, hbase']
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact ⟨envSlot, hslot, hcontains⟩)
      (by
        intro lv inner lifetime _htyping ih slot struck suffix needle hbase hstrike
          hcontains
        have hstrikeAtParent :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        exact ih hbase hstrikeAtParent (PartialTyContains.box hcontains))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets _ihBorrow _ihTargets slot struck suffix needle hbase hstrike
          _hcontains
        have hstrikeAtBorrow :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        rcases (LValTyping.strike_suffix_at_type.1 hborrow hbase hstrikeAtBorrow) with
          ⟨borrowStruck, hborrowStruck⟩
        simp [Strike] at hborrowStruck)
      (by
        intro target ty lifetime _htarget _ihTarget
        trivial)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest _hunion _hintersection _ihHead _ihRest
        trivial)
      htyping
  · intro targets partialTy lifetime _htyping
    trivial

theorem LValTyping.contains_base_of_strike {env : Env} {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} {slot : EnvSlot}
    {struck : PartialTy}
    {needle : Ty} :
    LValTyping env lv partialTy lifetime →
    env.slotAt (LVal.base lv) = some slot →
    Strike (LVal.path lv) slot.ty struck →
    PartialTyContains partialTy needle →
    env ⊢ LVal.base lv ↝ needle := by
  intro htyping hslot hstrike hcontains
  simpa using
    (LValTyping.contains_base_of_strike_suffix.1 htyping
      (slot := slot) (struck := struck) (suffix := []) hslot
      (by simpa using hstrike) hcontains)

theorem EnvContains.of_move {env env' : Env} {lv : LVal} {x : Name}
    {ty : Ty} :
    EnvMove env lv env' →
    env' ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hmove hcontains
  rcases hmove with ⟨slot, struck, hslot, hstrike, henv'⟩
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hcontainedSlotEq :
        containedSlot = { slot with ty := struck } := by
      have h :
          { slot with ty := struck } = containedSlot := by
        simpa [henv', Env.update] using hcontainedSlot
      exact h.symm
    subst hcontainedSlotEq
    exact ⟨slot, hslot, PartialTyContains.of_strike hstrike hcontainsTy⟩
  · have hslotOld : env.slotAt x = some containedSlot := by
      simpa [henv', Env.update, hx] using hcontainedSlot
    exact ⟨containedSlot, hslotOld, hcontainsTy⟩

/-- The base slot struck by an `EnvMove` cannot still contain a live borrow in
the moved environment. -/
theorem EnvContains.move_base_same_false {env env' : Env} {lv : LVal}
    {mutable : Bool} {targets : List LVal} :
    EnvMove env lv env' →
    ¬ env' ⊢ LVal.base lv ↝ Ty.borrow mutable targets := by
  intro hmove hcontains
  rcases hmove with ⟨slot, struck, _hslot, hstrike, henv'⟩
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq :
      containedSlot = { slot with ty := struck } := by
    have h :
        { slot with ty := struck } = containedSlot := by
      simpa [henv', Env.update] using hcontainedSlot
    exact h.symm
  subst hcontainedSlotEq
  exact PartialTyContains.not_strike_result hstrike hcontainsTy

/-- Moving an lval preserves borrow safety of the environment before adding the
result binding.

`EnvMove` only strikes part of a slot to `undef`; every contained borrow still
visible in the moved environment was already contained in the source
environment.  Thus the original borrow-safety relation applies directly. -/
theorem borrowSafeEnv_move {env env' : Env} {lv : LVal} :
    BorrowSafeEnv env →
    EnvMove env lv env' →
    BorrowSafeEnv env' := by
  intro hsafe hmove x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.of_move hmove hcontainsMutable)
    (EnvContains.of_move hmove hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafety_move_borrowFree_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {ty : Ty}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    TyBorrowFree ty →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe htyping hborrowFree
  cases htyping with
  | move _hLv _hnotWrite hmove =>
      exact borrowSafeEnv_update_fresh_borrowFree
        (borrowSafeEnv_move hsafe hmove) hborrowFree

/-- Result-extension after a move, factored around the one remaining typing
origin fact.

If every borrow contained in the moved result type was contained in the moved
base slot before the move, then adding the moved value as a fresh result root is
borrow safe.  Any old root that conflicts with the fresh result must have been
the moved base by `BorrowSafeEnv env`; but the moved environment no longer
contains live borrows at that base.
-/
theorem borrowSafeEnv_move_result_extension_of_base_contains {env env₂ : Env}
    {lv : LVal} {ty : Ty} {gamma : Name} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    EnvMove env lv env₂ →
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      env ⊢ LVal.base lv ↝ Ty.borrow mutable targets) →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hmove hbaseContains _hfresh a b mutable targetsMutable targetsOther
    targetMutable targetOther hcontainsMutable hcontainsOther htargetMutable
    htargetOther hconflict
  by_cases ha : a = gamma
  · subst a
    have hcontainsMutableAtGamma :
        (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hslotEq :
        containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
        simpa [Env.update] using hcontainedSlot
      exact h.symm
    subst hslotEq
    by_cases hb : b = gamma
    · exact hb.symm
    · have hcontainsOtherMove :
          env₂ ⊢ b ↝ Ty.borrow mutable targetsOther :=
        EnvContains.update_fresh_ne hb hcontainsOther
      by_cases hbBase : b = LVal.base lv
      · subst hbBase
        exact False.elim (EnvContains.move_base_same_false hmove hcontainsOtherMove)
      · have hcontainsOtherOld :
            env ⊢ b ↝ Ty.borrow mutable targetsOther :=
          EnvContains.of_move hmove hcontainsOtherMove
        have hbaseEq :
            LVal.base lv = b :=
          hsafe (LVal.base lv) b mutable targetsMutable targetsOther targetMutable
            targetOther
            (hbaseContains true targetsMutable hcontainsTy)
            hcontainsOtherOld
            htargetMutable htargetOther hconflict
        exact False.elim (hbBase hbaseEq.symm)
  · by_cases hb : b = gamma
    · subst b
      have hcontainsOtherAtGamma :
          (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hslotEq :
          containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
          simpa [Env.update] using hcontainedSlot
        exact h.symm
      subst hslotEq
      have hcontainsMutableMove :
          env₂ ⊢ a ↝ Ty.borrow true targetsMutable :=
        EnvContains.update_fresh_ne ha hcontainsMutable
      by_cases haBase : a = LVal.base lv
      · subst haBase
        exact False.elim (EnvContains.move_base_same_false hmove hcontainsMutableMove)
      · have hcontainsMutableOld :
            env ⊢ a ↝ Ty.borrow true targetsMutable :=
          EnvContains.of_move hmove hcontainsMutableMove
        have hbaseEq :
            a = LVal.base lv :=
          hsafe a (LVal.base lv) mutable targetsMutable targetsOther targetMutable
            targetOther hcontainsMutableOld
            (hbaseContains mutable targetsOther hcontainsTy)
            htargetMutable htargetOther hconflict
        exact False.elim (haBase hbaseEq)
    · exact borrowSafeEnv_move hsafe hmove a b mutable targetsMutable targetsOther
        targetMutable targetOther
        (EnvContains.update_fresh_ne ha hcontainsMutable)
        (EnvContains.update_fresh_ne hb hcontainsOther)
        htargetMutable htargetOther hconflict

theorem tyBorrowSafeAgainstEnv_move_of_base_contains {env env₂ : Env}
    {lv : LVal} {ty : Ty} :
    BorrowSafeEnv env →
    EnvMove env lv env₂ →
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      env ⊢ LVal.base lv ↝ Ty.borrow mutable targets) →
    TyBorrowSafeAgainstEnv env₂ ty := by
  intro hsafe hmove hbaseContains
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontainsTy
      hcontainsOther htargetMutable htargetOther hconflict
    by_cases hxBase : x = LVal.base lv
    · subst hxBase
      exact False.elim (EnvContains.move_base_same_false hmove hcontainsOther)
    · have hcontainsOtherOld :
          env ⊢ x ↝ Ty.borrow mutable targetsOther :=
        EnvContains.of_move hmove hcontainsOther
      have hbaseEq :
          LVal.base lv = x :=
        hsafe (LVal.base lv) x mutable targetsMutable targetsOther targetMutable
          targetOther
          (hbaseContains true targetsMutable hcontainsTy)
          hcontainsOtherOld
          htargetMutable htargetOther hconflict
      exact False.elim (hxBase hbaseEq.symm)
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable hcontainsTy htargetMutable htargetOther hconflict
    by_cases hxBase : x = LVal.base lv
    · subst hxBase
      exact False.elim (EnvContains.move_base_same_false hmove hcontainsMutable)
    · have hcontainsMutableOld :
          env ⊢ x ↝ Ty.borrow true targetsMutable :=
        EnvContains.of_move hmove hcontainsMutable
      have hbaseEq :
          x = LVal.base lv :=
        hsafe x (LVal.base lv) mutable targetsMutable targetsOther targetMutable
          targetOther hcontainsMutableOld
          (hbaseContains mutable targetsOther hcontainsTy)
          htargetMutable htargetOther hconflict
      exact False.elim (hxBase hbaseEq)

theorem EnvContains.move_var_same_false {env env' : Env} {x : Name}
    {slot : EnvSlot} {ty : Ty} {mutable : Bool} {targets : List LVal} :
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    EnvMove env (.var x) env' →
    ¬ env' ⊢ x ↝ Ty.borrow mutable targets := by
  intro _hslot _hslotTy hmove hcontains
  exact EnvContains.move_base_same_false hmove hcontains

theorem borrowSafety_move_var_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {ty : Ty} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.move (.var x)) ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe htyping hfresh a b mutable targetsMutable targetsOther
    targetMutable targetOther hcontainsMutable hcontainsOther htargetMutable
    htargetOther hconflict
  cases htyping with
  | move hLv hnotWrite hmove =>
      rcases LValTyping.var_inv hLv with
        ⟨sourceSlot, hslotSource, hsourceTy, _hsourceLifetime⟩
      by_cases ha : a = gamma
      · subst a
        have hcontainsMovedMutable :
            env ⊢ x ↝ Ty.borrow true targetsMutable := by
          rcases hcontainsMutable with
            ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
          have hslotEq :
              containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
            have h :
                { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
              simpa [Env.update] using hcontainedSlot
            exact h.symm
          subst hslotEq
          exact ⟨sourceSlot, hslotSource, by
            rw [hsourceTy]
            exact hcontainsTy⟩
        by_cases hb : b = gamma
        · subst b
          exact rfl
        · have hcontainsOtherMove :
              env₂ ⊢ b ↝ Ty.borrow mutable targetsOther :=
            EnvContains.update_fresh_ne hb hcontainsOther
          by_cases hbx : b = x
          · subst b
            exact False.elim
              (EnvContains.move_var_same_false hslotSource hsourceTy hmove
                hcontainsOtherMove)
          · have hcontainsOtherOld :
                env ⊢ b ↝ Ty.borrow mutable targetsOther :=
              EnvContains.of_move hmove hcontainsOtherMove
            have hsafeEq :
                x = b :=
              hsafe x b mutable targetsMutable targetsOther targetMutable
                targetOther hcontainsMovedMutable hcontainsOtherOld
                htargetMutable htargetOther hconflict
            exact False.elim (hbx hsafeEq.symm)
      · by_cases hb : b = gamma
        · subst b
          have hcontainsMovedOther :
              env ⊢ x ↝ Ty.borrow mutable targetsOther := by
            rcases hcontainsOther with
              ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
            have hslotEq :
                containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
              have h :
                  { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
                simpa [Env.update] using hcontainedSlot
              exact h.symm
            subst hslotEq
            exact ⟨sourceSlot, hslotSource, by
              rw [hsourceTy]
              exact hcontainsTy⟩
          have hcontainsMutableMove :
              env₂ ⊢ a ↝ Ty.borrow true targetsMutable :=
            EnvContains.update_fresh_ne ha hcontainsMutable
          by_cases hax : a = x
          · subst a
            exact False.elim
              (EnvContains.move_var_same_false hslotSource hsourceTy hmove
                hcontainsMutableMove)
          · have hcontainsMutableOld :
                env ⊢ a ↝ Ty.borrow true targetsMutable :=
              EnvContains.of_move hmove hcontainsMutableMove
            have hcontainsOtherOld :
                env ⊢ x ↝ Ty.borrow mutable targetsOther :=
              hcontainsMovedOther
            have hsafeEq :
                a = x :=
              hsafe a x mutable targetsMutable targetsOther targetMutable
                targetOther hcontainsMutableOld hcontainsOtherOld
                htargetMutable htargetOther hconflict
            exact False.elim (hax hsafeEq)
        · exact borrowSafeEnv_move hsafe hmove a b mutable targetsMutable
            targetsOther targetMutable targetOther
            (EnvContains.update_fresh_ne ha hcontainsMutable)
            (EnvContains.update_fresh_ne hb hcontainsOther)
            htargetMutable htargetOther hconflict

theorem EnvMove.oldSlot_of_newSlot {env env' : Env} {lv : LVal}
    {x : Name} {newSlot : EnvSlot} :
    EnvMove env lv env' →
    env'.slotAt x = some newSlot →
    ∃ oldSlot,
      env.slotAt x = some oldSlot ∧
      oldSlot.lifetime = newSlot.lifetime := by
  intro hmove hnewSlot
  rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hnewSlotEq :
        newSlot = { moveSlot with ty := struck } := by
      have h :
          { moveSlot with ty := struck } = newSlot := by
        simpa [henv', Env.update] using hnewSlot
      exact h.symm
    subst hnewSlotEq
    exact ⟨moveSlot, hmoveSlot, rfl⟩
  · have holdSlot : env.slotAt x = some newSlot := by
      simpa [henv', Env.update, hx] using hnewSlot
    exact ⟨newSlot, holdSlot, rfl⟩

theorem not_pathConflicts_of_not_writeProhibited_contains {env : Env}
    {lv target : LVal} {x : Name} {mutable : Bool} {targets : List LVal} :
    ¬ WriteProhibited env lv →
    env ⊢ x ↝ Ty.borrow mutable targets →
    target ∈ targets →
    ¬ target ⋈ lv := by
  intro hnotWrite hcontains htarget hconflict
  cases mutable with
  | false =>
      exact hnotWrite (Or.inr ⟨x, targets, target, hcontains, htarget, hconflict⟩)
  | true =>
      exact hnotWrite (Or.inl ⟨x, targets, target, hcontains, htarget, hconflict⟩)

theorem LValTyping.no_writeProhibited_targets {env : Env} {moved : LVal} :
    ¬ WriteProhibited env moved →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        ∀ target,
          target ∈ targets →
          ¬ target ⋈ moved) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {mutable borrowTargets},
        PartialTyContains partialTy (.borrow mutable borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ target ⋈ moved) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains target
          htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains target
          htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping

theorem LValTyping.move_of_not_pathConflicts {env env' : Env} {moved : LVal} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ¬ lv ⋈ moved →
      LValTyping env' lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ moved) →
      LValTargetsTyping env' targets partialTy lifetime) := by
  intro hmove hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ moved →
        LValTyping env' lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ moved) →
        LValTargetsTyping env' targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
        have hx : x ≠ LVal.base moved := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by simpa [henv', Env.update, hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ moved := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ moved := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ moved →
        LValTyping env' lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ moved) →
        LValTargetsTyping env' targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
        have hx : x ≠ LVal.base moved := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by simpa [henv', Env.update, hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ moved := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ moved := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

theorem LValTyping.update_of_not_pathConflicts {env : Env} {x : Name}
    {slot : EnvSlot} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ¬ lv ⋈ (.var x) →
      LValTyping (env.update x slot) lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
      LValTargetsTyping (env.update x slot) targets partialTy lifetime) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) →
        LValTyping (env.update x slot) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping (env.update x slot) targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping (env.update x slot) lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow' PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) →
        LValTyping (env.update x slot) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping (env.update x slot) targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping (env.update x slot) lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow' PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

theorem BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {slotLifetime : Lifetime}
    {targets : List LVal} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    BorrowTargetsWellFormedInSlot (env.update x slot) slotLifetime targets := by
  intro hnotWrite htargets hnotTargets target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  refine ⟨targetTy, targetLifetime,
    (LValTyping.update_of_not_pathConflicts (slot := slot) hnotWrite).1
      htyping (hnotTargets target htarget),
    houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  have hbaseNe : LVal.base target ≠ x := by
    intro hbaseEq
    exact hnotTargets target htarget hbaseEq
  have hbaseSlot' :
      (env.update x slot).slotAt (LVal.base target) = some baseSlot := by
    simpa [Env.update, hbaseNe] using hbaseSlot
  exact ⟨baseSlot, hbaseSlot', hbaseOutlives⟩

theorem PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {slotLifetime : Lifetime}
    {partialTy : PartialTy} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ {mutable targets},
      PartialTyContains partialTy (.borrow mutable targets) →
      ∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    PartialTyBorrowsWellFormedInSlot
      (env.update x slot) slotLifetime partialTy := by
  intro hnotWrite hpartial hnotTargets mutable targets hcontains
  exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
    (slot := slot) hnotWrite (hpartial hcontains)
    (hnotTargets hcontains)

theorem ContainedBorrowsWellFormed.slot_partial {env : Env}
    {x : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    env.slotAt x = some slot →
    PartialTyBorrowsWellFormedInSlot env slot.lifetime slot.ty := by
  intro hcontained hslot mutable targets hcontains
  exact hcontained x slot mutable targets hslot ⟨slot, hslot, hcontains⟩

theorem ContainedBorrowsWellFormed.update_slot {env : Env} {x : Name}
    {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot (env.update x slot) slot.lifetime slot.ty →
    ¬ WriteProhibited (env.update x slot) (.var x) →
    ContainedBorrowsWellFormed (env.update x slot) := by
  intro hcontained hslotTargets hnotWrite y resultSlot mutable targets
    hresultSlot hcontains
  by_cases hy : y = x
  · subst hy
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hresultSlotEq : resultSlot = slot := by
      have h : slot = resultSlot := by
        simpa [Env.update] using hresultSlot
      exact h.symm
    have hcontainedSlotEq : containedSlot = slot := by
      have h : slot = containedSlot := by
        simpa [Env.update] using hcontainedSlot
      exact h.symm
    have hcontainsSlot : PartialTyContains slot.ty (.borrow mutable targets) := by
      simpa [hcontainedSlotEq] using hcontainsTy
    rw [hresultSlotEq]
    exact hslotTargets hcontainsSlot
  · rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hresultSlotOld : env.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresultSlot
    have hcontainedSlotOld : env.slotAt y = some containedSlot := by
      simpa [Env.update, hy] using hcontainedSlot
    have hcontainedSlotEq : containedSlot = resultSlot := by
      have hsomeEq : some containedSlot = some resultSlot := by
        rw [← hcontainedSlotOld, hresultSlotOld]
      exact Option.some.inj hsomeEq
    have htargetsOld :
        BorrowTargetsWellFormedInSlot env resultSlot.lifetime targets := by
      rw [← hcontainedSlotEq]
      exact hcontained y containedSlot mutable targets hcontainedSlotOld
        ⟨containedSlot, hcontainedSlotOld, hcontainsTy⟩
    exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
      (slot := slot) hnotWrite htargetsOld
      (by
        intro target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains
          hnotWrite
          ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
          htarget)

theorem declare_preserves_wellFormed_output_fresh {env₂ env₃ : Env}
    {lifetime : Lifetime} {x : Name} {ty : Ty} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh x →
    FreshUpdateCoherenceObligations env₂ x ty lifetime →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    WellFormedEnv env₃ lifetime := by
  intro hwellFormed hwellTy hfresh hcoh henv₃
  rw [henv₃]
  exact WellFormedEnv.update_fresh_ty hwellFormed hwellTy hfresh hcoh

theorem ContainedBorrowsWellFormed.move {env env' : Env} {lv : LVal}
    {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    ContainedBorrowsWellFormed env' := by
  intro hwellFormed hnotWrite hmove x slot mutable targets hslot hcontains
  rcases EnvMove.oldSlot_of_newSlot hmove hslot with
    ⟨oldSlot, holdSlot, hlifetime⟩
  rcases EnvContains.of_move hmove hcontains with
    ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  have hcontainedOldSlotEq : containedOldSlot = oldSlot := by
    have hsomeEq : some oldSlot = some containedOldSlot := by
      rw [← holdSlot, hcontainedOldSlot]
    injection hsomeEq with heq
    exact heq.symm
  have hlifetimeContained : containedOldSlot.lifetime = slot.lifetime := by
    rw [hcontainedOldSlotEq, hlifetime]
  have htargetsOld :
      BorrowTargetsWellFormedInSlot env containedOldSlot.lifetime targets :=
    hwellFormed.1 x containedOldSlot mutable targets hcontainedOldSlot
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  rw [← hlifetimeContained]
  have hnotTargets : ∀ target, target ∈ targets → ¬ target ⋈ lv := by
    intro target htarget
    exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩ htarget
  intro target htarget
  rcases htargetsOld target htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  exact ⟨targetTy, targetLifetime,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
      htyping (hnotTargets target htarget),
    houtlives,
    LValBaseOutlives.move_of_not_pathConflicts
      hmove (hnotTargets target htarget) hbase⟩

theorem BorrowTargetsWellFormed.move_of_no_pathConflicts {env env' : Env}
    {moved : LVal} {targets : List LVal} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    BorrowTargetsWellFormed env targets lifetime →
    (∀ target, target ∈ targets → ¬ target ⋈ moved) →
    BorrowTargetsWellFormed env' targets lifetime := by
  intro hmove hnotWrite htargets hnotTargets
  cases htargets with
  | intro hmembers =>
      refine BorrowTargetsWellFormed.intro ?_
      intro target htarget
      rcases hmembers target htarget with
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
      exact ⟨targetTy, targetLifetime,
        (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
          htyping (hnotTargets target htarget),
        houtlives,
        LValBaseOutlives.move_of_not_pathConflicts
          hmove (hnotTargets target htarget) hbase⟩

theorem WellFormedTy.move_of_no_pathConflicts {env env' : Env}
    {moved : LVal} {ty : Ty} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    WellFormedTy env ty lifetime →
    (∀ mutable targets target,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      target ∈ targets →
      ¬ target ⋈ moved) →
    WellFormedTy env' ty lifetime := by
  intro hmove hnotWrite hwellTy hnotConflicts
  induction hwellTy with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | borrow htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.move_of_no_pathConflicts
          hmove hnotWrite htargets
          (by
            intro target htarget
            exact hnotConflicts _ _ target PartialTyContains.here htarget))
  | box hinner ih =>
      exact WellFormedTy.box (ih (by
        intro mutable targets target hcontains htarget
        exact hnotConflicts mutable targets target
          (PartialTyContains.tyBox hcontains) htarget))

theorem WellFormedTy.move_result {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedTy env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  have hwellTy : WellFormedTy env ty lifetime :=
    LValTyping.fullTyWellFormed hwellFormed hLv
  exact WellFormedTy.move_of_no_pathConflicts hmove hnotWrite hwellTy
    (by
      intro mutable targets target hcontains htarget
      exact (LValTyping.no_writeProhibited_targets hnotWrite).1
        hLv hcontains target htarget)

/-- `Strike` only removes variables (it replaces a sub-value by `undef`). -/
theorem Strike.vars_subset :
    ∀ {path : Path} {ty struck : PartialTy}, Strike path ty struck →
      ∀ v, v ∈ PartialTy.vars struck → v ∈ PartialTy.vars ty := by
  intro path
  induction path with
  | nil =>
      intro ty struck h v hv
      cases ty with
      | ty t =>
          cases struck with
          | undef t' => simp [PartialTy.vars] at hv
          | ty _ => simp [Strike] at h
          | box _ => simp [Strike] at h
      | box _ => simp [Strike] at h
      | undef _ => simp [Strike] at h
  | cons _ rest ih =>
      intro ty struck h v hv
      cases ty with
      | box inner =>
          cases struck with
          | box struck' =>
              simp only [PartialTy.vars] at hv ⊢
              exact ih (show Strike rest inner struck' from h) v hv
          | ty _ => simp [Strike] at h
          | undef _ => simp [Strike] at h
      | ty _ => simp [Strike] at h
      | undef _ => simp [Strike] at h

/-- `Linearizable` is preserved by a move (the same rank function works; the
moved slot's type loses variables via `Strike`). -/
theorem Linearizable.move {env env' : Env} {lv : LVal}
    (hmove : EnvMove env lv env') (h : Linearizable env) :
    Linearizable env' := by
  rcases hmove with ⟨slot, struck, hslot, hstrike, henv'⟩
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x s hs
  subst henv'
  by_cases hx : x = LVal.base lv
  · subst hx
    have hseq : s = { slot with ty := struck } := by
      have h := hs
      simpa [Env.update] using h.symm
    subst hseq
    intro v hv
    exact hφ (LVal.base lv) slot hslot v
      (Strike.vars_subset hstrike v (by simpa using hv))
  · have hsenv : env.slotAt x = some s := by simpa [Env.update, hx] using hs
    exact hφ x s hsenv

/-- A partial type with no defined `.ty` leaf reachable: every `Strike` result
is of this form, and an lval typing rooted at a struck slot stays in it (so it
can never be a defined borrow). -/
def IsBoxUndef : PartialTy → Prop
  | .ty _ => False
  | .box inner => IsBoxUndef inner
  | .undef _ => True

theorem Strike.isBoxUndef :
    ∀ {path : Path} {ty struck : PartialTy}, Strike path ty struck → IsBoxUndef struck := by
  intro path
  induction path with
  | nil =>
      intro ty struck h
      cases ty with
      | ty t => cases struck with
        | undef _ => trivial
        | ty _ => simp [Strike] at h
        | box _ => simp [Strike] at h
      | box _ => simp [Strike] at h
      | undef _ => simp [Strike] at h
  | cons _ rest ih =>
      intro ty struck h
      cases ty with
      | box inner => cases struck with
        | box struck' =>
            have h' : Strike rest inner struck' := h
            show IsBoxUndef struck'
            exact ih h'
        | ty _ => simp [Strike] at h
        | undef _ => simp [Strike] at h
      | ty _ => simp [Strike] at h
      | undef _ => simp [Strike] at h

/-- An lval typed in the moved environment whose base is the moved variable has a
`Strike`-shaped (box/undef) type — never a defined `.ty` (in particular never a
borrow). -/
theorem LValTyping.isBoxUndef_of_base_moved {env : Env} {lv : LVal}
    {slot : EnvSlot} {struck : PartialTy}
    (_hslot : env.slotAt (LVal.base lv) = some slot)
    (hstrike : Strike (LVal.path lv) slot.ty struck) :
    ∀ {lv' p lf},
      LValTyping (env.update (LVal.base lv) { slot with ty := struck }) lv' p lf →
      LVal.base lv' = LVal.base lv → IsBoxUndef p := by
  intro lv' p lf h
  refine LValTyping.rec
    (motive_1 := fun lv' p _ _ => LVal.base lv' = LVal.base lv → IsBoxUndef p)
    (motive_2 := fun _ _ _ _ => True)
    ?var ?box ?borrow ?singleton ?cons h
  · intro y ySlot hySlot hbase
    have hy : y = LVal.base lv := by simpa [LVal.base] using hbase
    subst hy
    have : ySlot = { slot with ty := struck } := by
      simpa [Env.update] using hySlot.symm
    subst this
    exact Strike.isBoxUndef hstrike
  · intro lv'' inner lifetime _htyping ih hbase
    have := ih (by simpa [LVal.base] using hbase)
    simpa [IsBoxUndef] using this
  · intro lv'' mutable targets _bLf _tLf _tTy hborrow _htargets ihBorrow _ihTargets hbase
    have := ihBorrow (by simpa [LVal.base] using hbase)
    simp [IsBoxUndef] at this
  · intro _ _ _ _ _; trivial
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _; trivial

/-- `Coherent` is preserved by a move.  A defined borrow `lv':&T` in the moved
environment cannot be rooted at the (undef'd) moved variable
(`isBoxUndef_of_base_moved`), so it transports backward to the original
environment (restoring the moved slot is an update with no path conflict), where
`Coherent env` provides a joint typing of `T`; the joint typing then transports
forward across the move (the targets do not conflict with the moved value, by
`¬WriteProhibited`). -/
theorem Coherent.move {env env' : Env} {lv : LVal} {lifetime : Lifetime}
    (hwellFormed : WellFormedEnv env lifetime)
    (hnotWrite : ¬ WriteProhibited env lv)
    (hmove : EnvMove env lv env')
    (hcohEnv : Coherent env) : Coherent env' := by
  have hmoveCopy := hmove
  rcases hmoveCopy with ⟨slot, struck, hslot, hstrike, henv'⟩
  subst henv'
  intro lv' m T bLf hty'
  have hbaseNe : ¬ lv' ⋈ lv := by
    intro hbeq
    have hbu := LValTyping.isBoxUndef_of_base_moved hslot hstrike hty'
      (by simpa [PathConflicts, LVal.base] using hbeq)
    simp [IsBoxUndef] at hbu
  -- restoring the moved slot returns the original environment
  have hrestore :
      (env.update (LVal.base lv) { slot with ty := struck }).update (LVal.base lv) slot
        = env := by
    obtain ⟨g⟩ := env
    simp only [Env.update]
    congr 1
    funext y
    by_cases hy : y = LVal.base lv
    · subst hy; simpa using hslot.symm
    · simp [hy]
  have hnotWriteVarEnv : ¬ WriteProhibited env (.var (LVal.base lv)) :=
    not_writeProhibited_var_base hnotWrite
  have hnotWriteVar :
      ¬ WriteProhibited
        ((env.update (LVal.base lv) { slot with ty := struck }).update (LVal.base lv) slot)
        (.var (LVal.base lv)) := by rw [hrestore]; exact hnotWriteVarEnv
  -- backward typing: env' → env (restore update, no conflict)
  have htyEnvRestore :
      LValTyping ((env.update (LVal.base lv) { slot with ty := struck }).update
        (LVal.base lv) slot) lv' (.ty (.borrow m T)) bLf :=
    (LValTyping.update_of_not_pathConflicts hnotWriteVar).1 hty'
      (by simpa [PathConflicts, LVal.base] using hbaseNe)
  have htyEnv : LValTyping env lv' (.ty (.borrow m T)) bLf := by
    rwa [hrestore] at htyEnvRestore
  rcases hcohEnv lv' m T bLf htyEnv with ⟨ty, lt, htgtsEnv⟩
  -- targets do not conflict with the moved value
  have hnotTargets : ∀ target, target ∈ T → ¬ target ⋈ lv := by
    intro target htarget
    exact (LValTyping.no_writeProhibited_targets hnotWrite).1 htyEnv
      PartialTyContains.here target htarget
  -- forward transport of the joint typing across the move
  exact ⟨ty, lt,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).2 htgtsEnv hnotTargets⟩

/--
Move Preservation for well-formed environments, used in Lemma 4.9.

This is the proof obligation described in the `T-Move` case of the paper:
`move(Γ, w)` replaces the moved component by `undef`, and the
`¬writeProhibited(Γ, w)` premise prevents this from invalidating any surviving
borrow target.
-/
theorem move_preserves_wellFormed {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedEnv env' lifetime ∧ WellFormedTy env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  refine ⟨⟨ContainedBorrowsWellFormed.move hwellFormed hnotWrite hmove,
      EnvSlotsOutlive.move hwellFormed.2.1 hmove, ?_, ?_⟩,
    WellFormedTy.move_result hwellFormed hLv hnotWrite hmove⟩
  · exact Coherent.move hwellFormed hnotWrite hmove hwellFormed.2.2.1
  · exact Linearizable.move hmove hwellFormed.2.2.2

theorem EnvWrite.preserves_containedBorrowsWellFormed_var {env result : Env}
    {lifetime targetLifetime : Lifetime} {x : Name}
    {oldTy : PartialTy} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    LValTyping env (.var x) oldTy targetLifetime →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite 0 env (.var x) rhsTy result →
    ¬ WriteProhibited result (.var x) →
    ContainedBorrowsWellFormed result := by
  intro hwellFormed hLhs hwellRhs hwrite hnotWrite
  rcases LValTyping.var_inv hLhs with
    ⟨lhsSlot, hlhsSlot, _holdTy, hlhsLifetime⟩
  cases hwrite with
  | intro hwriteSlot hupdate =>
      rename_i writeEnv writeSlot updatedTy
      simp [LVal.base, LVal.path] at hwriteSlot hupdate
      have hslotEq : writeSlot = lhsSlot := by
        have hsomeEq : some writeSlot = some lhsSlot := by
          rw [← hwriteSlot, hlhsSlot]
        exact Option.some.inj hsomeEq
      cases hupdate with
      | strong =>
          have hnotWrite' :
              ¬ WriteProhibited
                (env.update x { writeSlot with ty := PartialTy.ty rhsTy })
                (.var x) := by
            simpa [LVal.base] using hnotWrite
          have hslotTargets :
              PartialTyBorrowsWellFormedInSlot
                (env.update x { writeSlot with ty := PartialTy.ty rhsTy })
                writeSlot.lifetime
                ({ writeSlot with ty := PartialTy.ty rhsTy }).ty := by
            intro mutable targets hcontainsTy
            have htargetsEnv :
                BorrowTargetsWellFormedInSlot env targetLifetime targets :=
              borrowTargetsWellFormedInSlot_of_wellFormedTy_contains
                hwellRhs hcontainsTy
            have htargetsEnvAtSlot :
                BorrowTargetsWellFormedInSlot env writeSlot.lifetime targets := by
              rw [hslotEq, hlhsLifetime]
              exact htargetsEnv
            exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
              (x := x)
              (slot := { writeSlot with ty := PartialTy.ty rhsTy }) hnotWrite'
              htargetsEnvAtSlot
              (by
                intro target htarget
                have hcontainsUpdated :
                    (env.update x { writeSlot with ty := PartialTy.ty rhsTy }) ⊢
                      x ↝ Ty.borrow mutable targets :=
                  ⟨{ writeSlot with ty := PartialTy.ty rhsTy },
                    by simp [Env.update],
                    hcontainsTy⟩
                exact not_pathConflicts_of_not_writeProhibited_contains
                  hnotWrite'
                  hcontainsUpdated
                  htarget)
          simpa [LVal.base] using
            ContainedBorrowsWellFormed.update_slot
              hwellFormed.1 hslotTargets hnotWrite'

/-- Remaining update invariant needed by Lemma 4.9.

The `W-Weak` union case is no longer a caller obligation:
`PartialTyBorrowsWellFormedInSlot.of_partialTyUnion` proves it directly for the
per-target invariant.  The package now only records the non-local mutable-borrow
fan-out fact, where branch writes and joins must preserve observer target
well-formedness.
-/
structure UpdateBorrowInvariantObligations : Prop where
  writeBorrowTargets_preserves_containedBorrowsWellFormed
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets

/-- Remaining explicit proof obligation for Appendix 9.6 fan-out writes.

This statement is intentionally kept at the `WriteBorrowTargets` boundary rather
than decomposed into bare join landmarks: unconditional join preservation of
contained borrows is false without the cross-branch target/coherence premises
carried by the fan-out proof.
-/
theorem updateBorrowInvariant_writeBorrowTargets_preserves_containedBorrowsWellFormed
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets := by
  sorry

/-- Concrete update-invariant package assembled from the explicit fan-out debt. -/
theorem updateBorrowInvariantObligations_from_sorries :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed :=
    updateBorrowInvariant_writeBorrowTargets_preserves_containedBorrowsWellFormed

/-- Initialized-leaf fact for Appendix 9.6 fan-out writes.

Documented rule strengthening: `WriteBorrowTargets.singleton/cons` now carry a
full typing for the concrete branch target `prependPath path target`.  Without
that premise, the bare fan-out syntax could write through arbitrary partial
paths, including reinitialising `undef` leaves, so branch shape would not be
derivable.  With it, the existing matching lemma
`writeLeafTy_of_lvalTyping` supplies exactly the initialized-leaf witness needed
by `EnvWrite.shapePreserved_init` and `WriteBorrowTargets.shapePreserved_init`. -/
theorem WriteBorrowTargets.initialized_leaves_appendix96
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    WriteBorrowTargets rank env path targets rhsTy result →
    ∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy := by
  intro _htargets hwrites
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _rank env path targets rhsTy _result _ =>
      ∀ target, target ∈ targets → ∀ targetSlot,
        env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
        WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
  case nil =>
    intro rank env path ty target htarget
    simp at htarget
  case singleton =>
    intro rank env updated path target ty _hwrite htyped _ih selected hselected slot hslot
    rw [List.mem_singleton] at hselected
    subst hselected
    rcases htyped with ⟨leafTy, leafLifetime, htyping⟩
    have hleaf :=
      writeLeafTy_of_lvalTyping htyping hslot [] ty WriteLeafTy.leaf
    simpa using hleaf
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite htyped _hwrites _hjoin _ihWrite ihRest selected hselected slot hslot
    rcases List.mem_cons.mp hselected with hhead | htail
    · subst hhead
      rcases htyped with ⟨leafTy, leafLifetime, htyping⟩
      have hleaf :=
        writeLeafTy_of_lvalTyping htyping hslot [] ty WriteLeafTy.leaf
      simpa using hleaf
    · exact ihRest selected htail slot hslot
  case intro => intros; trivial

/--
`ContainedBorrowsWellFormedIn source observer` says that every borrow contained
in `source` has targets that are also well formed in `observer`, at the
containing slot's lifetime.

This is the cross-branch invariant needed by `writeBorrowTargets`: when two
branch environments are joined, contained borrows from one branch can be
validated in the joined environment only if their targets are available on the
other branch as well.
-/
def ContainedBorrowsWellFormedIn (source observer : Env) : Prop :=
  ∀ {x slot mutable targets},
    source.slotAt x = some slot →
    source ⊢ x ↝ Ty.borrow mutable targets →
    BorrowTargetsWellFormedInSlot observer slot.lifetime targets

/--
Join transport needed for Definition 4.8(i).

This is the lval-shaped part of the Appendix 9.6 join argument: if the same
borrow target is fully typed on both branches, and both typings live long
enough for the observer slot, then the joined environment also gives that
target a full type at a lifetime that still lives long enough.
-/
structure FullLValTypingJoinTransport : Prop where
  full
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftTy) leftLifetime →
    LValTyping right target (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join target (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure LValTargetsTypingJoinTransport : Prop where
  targets
    {left right join : Env} {targets : List LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTargetsTyping left targets (.ty leftTy) leftLifetime →
    LValTargetsTyping right targets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join targets (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure DerefLValTypingJoinTransport : Prop where
  deref
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.ty leftTy) leftLifetime →
    LValTyping right (.deref source) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure DerefLValTypingJoinTransportWithUnion : Prop where
  deref
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.ty leftTy) leftLifetime →
    LValTyping right (.deref source) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
          joinLifetime ≤ current

structure FullLValTypingJoinTransportWithUnion : Prop where
  full
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftTy) leftLifetime →
    LValTyping right target (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join target (.ty joinTy) joinLifetime ∧
          joinLifetime ≤ current

structure BoxFullLValTypingJoinTransport : Prop where
  boxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join source (.box (.ty joinTy)) joinLifetime ∧
        joinLifetime ≤ current

structure DerefBoxFullLValTypingJoinTransport : Prop where
  derefBoxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.box (.ty leftTy)) leftLifetime →
    LValTyping right (.deref source) (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.box (.ty joinTy)) joinLifetime ∧
        joinLifetime ≤ current

structure BoxBoxFullLValTypingJoinTransport : Prop where
  boxBoxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.box (.ty leftTy))) leftLifetime →
    LValTyping right source (.box (.box (.ty rightTy))) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join source (.box (.box (.ty joinTy))) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefBoxFullLValTypingJoinTransport.of_boxBoxFull
    (htransport : BoxBoxFullLValTypingJoinTransport) :
    DerefBoxFullLValTypingJoinTransport where
  derefBoxFull := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleft hright hleftOutlives hrightOutlives
    have hleftSource :
        LValTyping left source (.box (.box (.ty leftTy))) leftLifetime :=
      LValTyping.deref_box_full_inv hleft
    have hrightSource :
        LValTyping right source (.box (.box (.ty rightTy))) rightLifetime :=
      LValTyping.deref_box_full_inv hright
    rcases htransport.boxBoxFull hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftSource hrightSource
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, hjoinSource, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, LValTyping.box hjoinSource, hjoinOutlives⟩

theorem BoxFullLValTypingJoinTransport.of_derefBoxFull
    (hderef : DerefBoxFullLValTypingJoinTransport) :
    BoxFullLValTypingJoinTransport where
  boxFull := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleft hright hleftOutlives hrightOutlives
    cases source with
    | var x =>
        exact LValTyping.var_join_box_full_bounded hjoin hleft hright
          hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.derefBoxFull hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleft hright hleftOutlives hrightOutlives

structure DerefLValTypingJoinConstructorLandmarks : Prop where
  box_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  box_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {rightMutable : Bool} {rightTargets : List LVal}
    {leftLifetime rightBorrowLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftMutable : Bool} {leftTargets : List LVal}
    {leftBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty}
    {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal}
    {leftBorrowLifetime rightBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefLValTypingJoinConstructorLandmarks.box_box_of_boxFull
    (hbox : BoxFullLValTypingJoinTransport)
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright hleftOutlives hrightOutlives
  rcases hbox.boxFull hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hright hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, LValTyping.box hjoinTyping, hjoinOutlives⟩

theorem LValTyping.deref_borrow_from_aligned_targets
    {env : Env} {source : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime targetLifetime current : Lifetime} {targetTy : Ty} :
    LValTyping env source (.ty (.borrow mutable targets)) borrowLifetime →
    LValTargetsTyping env targets (.ty targetTy) targetLifetime →
    targetLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping env (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hborrow htargets houtlives
  exact ⟨targetTy, targetLifetime,
    LValTyping.borrow hborrow htargets,
    houtlives⟩

structure DerefLValTypingJoinConstructorSplitLandmarks : Prop where
  boxFull :
    BoxFullLValTypingJoinTransport
  box_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {rightMutable : Bool} {rightTargets : List LVal}
    {leftLifetime rightBorrowLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftMutable : Bool} {leftTargets : List LVal}
    {leftBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty}
    {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal}
    {leftBorrowLifetime rightBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefLValTypingJoinConstructorLandmarks.of_split
    (hlandmarks : DerefLValTypingJoinConstructorSplitLandmarks) :
    DerefLValTypingJoinConstructorLandmarks where
  box_box := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft hleft hright
      hleftOutlives hrightOutlives
    exact DerefLValTypingJoinConstructorLandmarks.box_box_of_boxFull
      hlandmarks.boxFull hjoin hleftContained hrightContained hleftInRight
      hrightInLeft hleft hright hleftOutlives hrightOutlives
  box_borrow := by
    intro left right join source leftTy rightTy rightMutable rightTargets
      leftLifetime rightBorrowLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleft hright hrightTargets
      hleftOutlives hrightOutlives
    exact hlandmarks.box_borrow hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hright hrightTargets
      hleftOutlives hrightOutlives
  borrow_box := by
    intro left right join source leftTy rightTy leftMutable leftTargets
      leftBorrowLifetime leftLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleft hleftTargets hright
      hleftOutlives hrightOutlives
    exact hlandmarks.borrow_box hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hleftTargets hright
      hleftOutlives hrightOutlives
  borrow_borrow := by
    intro left right join source leftTy rightTy leftMutable rightMutable
      leftTargets rightTargets leftBorrowLifetime rightBorrowLifetime leftLifetime
      rightLifetime current hjoin hleftContained hrightContained hleftInRight
      hrightInLeft hleft hleftTargets hright hrightTargets hleftOutlives
      hrightOutlives
    exact hlandmarks.borrow_borrow hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hleftTargets hright hrightTargets
      hleftOutlives hrightOutlives

theorem DerefLValTypingJoinTransport.of_constructorLandmarks
    (hlandmarks : DerefLValTypingJoinConstructorLandmarks) :
    DerefLValTypingJoinTransport where
  deref := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases hleftTyping with
    | box hleftSource =>
        cases hrightTyping with
        | box hrightSource =>
            exact hlandmarks.box_box hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hrightSource
              hleftOutlives hrightOutlives
        | borrow hrightSource hrightTargets =>
            exact hlandmarks.box_borrow hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hrightSource hrightTargets
              hleftOutlives hrightOutlives
    | borrow hleftSource hleftTargets =>
        cases hrightTyping with
        | box hrightSource =>
            exact hlandmarks.borrow_box hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hleftTargets hrightSource
              hleftOutlives hrightOutlives
        | borrow hrightSource hrightTargets =>
            exact hlandmarks.borrow_borrow hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hleftTargets hrightSource hrightTargets
              hleftOutlives hrightOutlives

theorem FullLValTypingJoinTransport.of_deref
    (hderef : DerefLValTypingJoinTransport) :
    FullLValTypingJoinTransport where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases target with
    | var x =>
        exact LValTyping.var_join_full_bounded hjoin hleftTyping hrightTyping
          hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.deref hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleftTyping hrightTyping
          hleftOutlives hrightOutlives

theorem DerefLValTypingJoinTransportWithUnion.to_deref
    (htransport : DerefLValTypingJoinTransportWithUnion) :
    DerefLValTypingJoinTransport where
  deref := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    rcases htransport.deref hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftTyping hrightTyping
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, _hunion, hjoinTyping, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩

theorem FullLValTypingJoinTransportWithUnion.to_full
    (htransport : FullLValTypingJoinTransportWithUnion) :
    FullLValTypingJoinTransport where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    rcases htransport.full hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftTyping hrightTyping
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, _hunion, hjoinTyping, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩

theorem FullLValTypingJoinTransportWithUnion.of_deref
    (hderef : DerefLValTypingJoinTransportWithUnion) :
    FullLValTypingJoinTransportWithUnion where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases target with
    | var x =>
        exact LValTyping.var_join_full_bounded_with_union hjoin
          hleftTyping hrightTyping hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.deref hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleftTyping hrightTyping
          hleftOutlives hrightOutlives

def BorrowTargetsTransport (source target : Env) : Prop :=
  ∀ {slotLifetime targets},
    BorrowTargetsWellFormedInSlot source slotLifetime targets →
    BorrowTargetsWellFormedInSlot target slotLifetime targets

@[refl] theorem BorrowTargetsTransport.refl (env : Env) :
    BorrowTargetsTransport env env := by
  intro slotLifetime targets htargets
  exact htargets

theorem BorrowTargetsTransport.trans {first second third : Env} :
    BorrowTargetsTransport first second →
    BorrowTargetsTransport second third →
    BorrowTargetsTransport first third := by
  intro hfirstSecond hsecondThird slotLifetime targets htargets
  exact hsecondThird (hfirstSecond htargets)

/-- Observer-target transport across a join via the runtime invariants
(one-directional: `source → left → join`).  Here `ContainedBorrows join` is
already established (the bootstrap runs first), so each transported target's
lifetime is bounded by the *unbounded*-strength invariant — packaged through the
rank-bounded `fullJoinTransport` with the per-target bound `N := φ(base t)+1` and
`hcontN` derived from the full `hcontJoin`. -/
theorem BorrowTargetsTransport.join_viaInvariants_left
    {source left right join : Env}
    (hjoin : EnvJoin left right join)
    (hstrL : ∀ x sE, left.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hlinJoin : Linearizable join) (hcohJoin : Coherent join)
    (hcontJoin : ContainedBorrowsWellFormed join)
    (hsourceLeft : BorrowTargetsTransport source left) :
    BorrowTargetsTransport source join := by
  obtain ⟨φ, hφJoin⟩ := hlinJoin
  intro slotLifetime targets htargets
  have hleft := hsourceLeft htargets
  intro target htarget
  rcases hleft target htarget with ⟨leftTy, leftLf, hleftTyping, _hleftOutlives, hleftBase⟩
  have hjoinBase := LValBaseOutlives.join_left hjoin hleftBase
  rcases fullJoinTransport_viaInvariants (N := φ (LVal.base target) + 1)
      hstrL hφJoin hcohJoin
      (fun x' slot' m' T' _ hslot' hcont' => hcontJoin x' slot' m' T' hslot' hcont')
      (Nat.lt_succ_self _) hleftTyping hjoinBase
    with ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives, hjoinBase⟩

theorem ContainedBorrowsWellFormedIn.of_transport {source observer : Env} :
    ContainedBorrowsWellFormed source →
    BorrowTargetsTransport source observer →
    ContainedBorrowsWellFormedIn source observer := by
  intro hcontained htransport x slot mutable targets hslot hcontains
  exact htransport (hcontained x slot mutable targets hslot hcontains)

theorem ContainedBorrowsWellFormed.in_self {env : Env} :
    ContainedBorrowsWellFormed env →
    ContainedBorrowsWellFormedIn env env := by
  intro hcontained x slot mutable targets hslot hcontains
  exact hcontained x slot mutable targets hslot hcontains

theorem LValTargetsTyping.join_full_singleton_of_fullLValTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTargetsTyping left [target] (.ty leftTy) leftLifetime →
    LValTargetsTyping right [target] (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join [target] (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleftTargets hrightTargets hleftOutlives hrightOutlives
  cases hleftTargets with
  | singleton hleft =>
      cases hrightTargets with
      | singleton hright =>
          rcases htransport.full hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleft hright
              hleftOutlives hrightOutlives with
            ⟨joinTy, joinLifetime, hjoinTarget, hjoinOutlives⟩
          exact ⟨joinTy, joinLifetime,
            LValTargetsTyping.singleton hjoinTarget, hjoinOutlives⟩
      | cons _hhead hrest _hunion _hintersection =>
          cases hrest
  | cons _hhead hrest _hunion _hintersection =>
      cases hrest

theorem LValTargetsTyping.join_full_cons_of_parts
    {join : Env} {target : LVal} {rest : List LVal}
    {headTy restTy unionTy : Ty}
    {headLifetime restLifetime lifetime current : Lifetime} :
    LValTyping join target (.ty headTy) headLifetime →
    LValTargetsTyping join rest (.ty restTy) restLifetime →
    PartialTyUnion (.ty headTy) (.ty restTy) (.ty unionTy) →
    LifetimeIntersection headLifetime restLifetime lifetime →
    lifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join (target :: rest) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hhead hrest hunion hintersection houtlives
  exact ⟨unionTy, lifetime,
    LValTargetsTyping.cons hhead hrest hunion hintersection,
    houtlives⟩

structure LValTargetsTypingJoinConsTypeUnionLandmark : Prop where
  typeUnion
    {left right join : Env} {target : LVal} {rest : List LVal}
    {leftHeadTy rightHeadTy leftRestTy rightRestTy leftTy rightTy : Ty}
    {joinHeadTy joinRestTy : Ty}
    {leftHeadLifetime rightHeadLifetime leftRestLifetime rightRestLifetime
      leftLifetime rightLifetime joinHeadLifetime joinRestLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftHeadTy) leftHeadLifetime →
    LValTyping right target (.ty rightHeadTy) rightHeadLifetime →
    LValTargetsTyping left rest (.ty leftRestTy) leftRestLifetime →
    LValTargetsTyping right rest (.ty rightRestTy) rightRestLifetime →
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty rightHeadTy) (.ty rightRestTy) (.ty rightTy) →
    LifetimeIntersection leftHeadLifetime leftRestLifetime leftLifetime →
    LifetimeIntersection rightHeadLifetime rightRestLifetime rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    LValTyping join target (.ty joinHeadTy) joinHeadLifetime →
    LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime →
    joinHeadLifetime ≤ current →
    joinRestLifetime ≤ current →
    ∃ joinTy, PartialTyUnion (.ty joinHeadTy) (.ty joinRestTy) (.ty joinTy)

structure LValTargetsTypingJoinConsLandmark : Prop where
  cons
    {left right join : Env} {target : LVal} {rest : List LVal}
    {leftHeadTy rightHeadTy leftRestTy rightRestTy leftTy rightTy : Ty}
    {leftHeadLifetime rightHeadLifetime leftRestLifetime rightRestLifetime
      leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftHeadTy) leftHeadLifetime →
    LValTyping right target (.ty rightHeadTy) rightHeadLifetime →
    LValTargetsTyping left rest (.ty leftRestTy) leftRestLifetime →
    LValTargetsTyping right rest (.ty rightRestTy) rightRestLifetime →
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty rightHeadTy) (.ty rightRestTy) (.ty rightTy) →
    LifetimeIntersection leftHeadLifetime leftRestLifetime leftLifetime →
    LifetimeIntersection rightHeadLifetime rightRestLifetime rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    (∃ joinHeadTy joinHeadLifetime,
      LValTyping join target (.ty joinHeadTy) joinHeadLifetime ∧
        joinHeadLifetime ≤ current) →
    (∃ joinRestTy joinRestLifetime,
      LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime ∧
        joinRestLifetime ≤ current) →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join (target :: rest) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem LValTargetsTypingJoinConsLandmark.of_typeUnion
    (htypeUnion : LValTargetsTypingJoinConsTypeUnionLandmark) :
    LValTargetsTypingJoinConsLandmark where
  cons := by
    intro left right join target rest leftHeadTy rightHeadTy leftRestTy rightRestTy
      leftTy rightTy leftHeadLifetime rightHeadLifetime leftRestLifetime
      rightRestLifetime leftLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleftHead hrightHead hleftRest
      hrightRest hleftUnion hrightUnion hleftIntersection hrightIntersection
      hleftOutlives hrightOutlives hjoinHead hjoinRest
    rcases hjoinHead with
      ⟨joinHeadTy, joinHeadLifetime, hjoinHeadTyping, hjoinHeadOutlives⟩
    rcases hjoinRest with
      ⟨joinRestTy, joinRestLifetime, hjoinRestTyping, hjoinRestOutlives⟩
    rcases htypeUnion.typeUnion hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftHead hrightHead hleftRest hrightRest
        hleftUnion hrightUnion hleftIntersection hrightIntersection
        hleftOutlives hrightOutlives hjoinHeadTyping hjoinRestTyping
        hjoinHeadOutlives hjoinRestOutlives with
      ⟨joinTy, hjoinUnion⟩
    rcases LifetimeIntersection.exists_of_common_inner
        hjoinHeadOutlives hjoinRestOutlives with
      ⟨joinLifetime, hjoinIntersection⟩
    exact LValTargetsTyping.join_full_cons_of_parts
      hjoinHeadTyping hjoinRestTyping hjoinUnion hjoinIntersection
      (LifetimeIntersection.le_of_le hjoinIntersection
        hjoinHeadOutlives hjoinRestOutlives)

theorem LValTargetsTypingJoinTransport.of_full_and_cons
    (hfull : FullLValTypingJoinTransport)
    (hcons : LValTargetsTypingJoinConsLandmark) :
    LValTargetsTypingJoinTransport := by
  constructor
  intro left right join targets leftTy rightTy leftLifetime rightLifetime current
    hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleftTargets hrightTargets hleftOutlives hrightOutlives
  induction targets generalizing leftTy rightTy leftLifetime rightLifetime current with
  | nil =>
      cases hleftTargets
  | cons target rest ih =>
      by_cases hrestNil : rest = []
      · subst hrestNil
        cases hleftTargets with
        | singleton hleftTarget =>
            cases hrightTargets with
            | singleton hrightTarget =>
                rcases hfull.full hjoin hleftContained hrightContained
                    hleftInRight hrightInLeft hleftTarget hrightTarget
                    hleftOutlives hrightOutlives with
                  ⟨joinTy, joinLifetime, hjoinTarget, hjoinOutlives⟩
                exact ⟨joinTy, joinLifetime,
                  LValTargetsTyping.singleton hjoinTarget, hjoinOutlives⟩
            | cons _hrightHead hrightRest _hrightUnion _hrightIntersection =>
                cases hrightRest
        | cons _hleftHead hleftRest _hleftUnion _hleftIntersection =>
            cases hleftRest
      · rcases LValTargetsTyping.cons_full_inv hrestNil hleftTargets with
          ⟨leftHeadTy, leftHeadLifetime, leftRestTy, leftRestLifetime,
            hleftHead, hleftRest, hleftUnion, hleftIntersection⟩
        rcases LValTargetsTyping.cons_full_inv hrestNil hrightTargets with
          ⟨rightHeadTy, rightHeadLifetime, rightRestTy, rightRestLifetime,
            hrightHead, hrightRest, hrightUnion, hrightIntersection⟩
        have hleftHeadOutlives : leftHeadLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.left_le hleftIntersection) hleftOutlives
        have hrightHeadOutlives : rightHeadLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.left_le hrightIntersection) hrightOutlives
        have hleftRestOutlives : leftRestLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.right_le hleftIntersection) hleftOutlives
        have hrightRestOutlives : rightRestLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.right_le hrightIntersection) hrightOutlives
        have hjoinHead :
            ∃ joinHeadTy joinHeadLifetime,
              LValTyping join target (.ty joinHeadTy) joinHeadLifetime ∧
                joinHeadLifetime ≤ current :=
          hfull.full hjoin hleftContained hrightContained hleftInRight
            hrightInLeft hleftHead hrightHead hleftHeadOutlives
            hrightHeadOutlives
        have hjoinRest :
            ∃ joinRestTy joinRestLifetime,
              LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime ∧
                joinRestLifetime ≤ current :=
          ih hleftRest hrightRest hleftRestOutlives hrightRestOutlives
        exact hcons.cons hjoin hleftContained hrightContained hleftInRight
          hrightInLeft hleftHead hrightHead hleftRest hrightRest
          hleftUnion hrightUnion hleftIntersection hrightIntersection
          hleftOutlives hrightOutlives hjoinHead hjoinRest

theorem BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {targets : List LVal}
    {slotLifetime : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright target htarget
  -- Per-target invariant: each target is typed in both branches; transport the
  -- single typing across the join via the single-lval full join transport.  No
  -- joint target-list typing of the merged list is needed, so the list-level
  -- cons-union landmark is no longer required here.
  rcases hleft target htarget with
    ⟨leftTy, leftLifetime, hleftTyping, hleftOutlives, hleftBase⟩
  rcases hright target htarget with
    ⟨rightTy, rightLifetime, hrightTyping, hrightOutlives, _hrightBase⟩
  rcases htransport.full hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleftTyping hrightTyping
      hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives,
    LValBaseOutlives.join_left hjoin hleftBase⟩

theorem EnvJoin.preserves_observerTargets_of_lvalTargetsTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {targets : List LVal}
    {slotLifetime : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport

theorem BorrowTargetsTransport.join_observer
    (htransport : FullLValTypingJoinTransport)
    {source left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsTransport source left →
    BorrowTargetsTransport source right →
    BorrowTargetsTransport source join := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright slotLifetime targets htargets
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport hjoin hleftContained hrightContained hleftInRight hrightInLeft
    (hleft htargets) (hright htargets)

theorem ContainedBorrowsWellFormedIn.join_observer
    (htransport : FullLValTypingJoinTransport)
    {source left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    ContainedBorrowsWellFormedIn source left →
    ContainedBorrowsWellFormedIn source right →
    ContainedBorrowsWellFormedIn source join := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright x slot mutable targets hslot hcontains
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport hjoin hleftContained hrightContained hleftInRight hrightInLeft
    (hleft hslot hcontains)
    (hright hslot hcontains)

theorem ContainedBorrowsWellFormedIn.join_source
    {left right join observer : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormedIn left observer →
    ContainedBorrowsWellFormedIn right observer →
    ContainedBorrowsWellFormedIn join observer := by
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
    (env := observer) (lifetime := joinSlot.lifetime) hunion
    (by
      intro leftMutable leftTargets hcontainsLeft
      have htargets :
          BorrowTargetsWellFormedInSlot observer leftSlot.lifetime leftTargets :=
        hleft hleftSlot ⟨leftSlot, hleftSlot, hcontainsLeft⟩
      simpa [hleftLife] using htargets)
    (by
      intro rightMutable rightTargets hcontainsRight
      have htargets :
          BorrowTargetsWellFormedInSlot observer rightSlot.lifetime rightTargets :=
        hright hrightSlot ⟨rightSlot, hrightSlot, hcontainsRight⟩
      simpa [hrightLife] using htargets)
    hcontainsJoin

/--
Branch-specific contained-borrow join preservation.

The unconditional statement "contained borrows are preserved by every
environment join" is too strong for partial environments: a borrow introduced
on one branch may have targets that are not fully typable on the other branch.
The `writeBorrowTargets` cons case supplies precisely the missing cross-branch
premises via its observer-target induction hypotheses.
-/
theorem ContainedBorrowsWellFormed.join_of_crossBranchTargets
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    ContainedBorrowsWellFormed join := by
  intro hjoin hleftContained hrightContained hleftTargetsRight hrightTargetsLeft
  exact ContainedBorrowsWellFormed.join_of_inSlot hjoin
    (by
      intro x slot mutable targets hslot hcontains
      exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
        htransport hjoin hleftContained hrightContained
        hleftTargetsRight hrightTargetsLeft
        (hleftContained x slot mutable targets hslot hcontains)
        (hleftTargetsRight hslot hcontains))
    (by
      intro x slot mutable targets hslot hcontains
      exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
        htransport hjoin hleftContained hrightContained
        hleftTargetsRight hrightTargetsLeft
        (hrightTargetsLeft hslot hcontains)
        (hrightContained x slot mutable targets hslot hcontains))

structure UpdateBorrowInvariantCrossLandmarks : Prop where
  envWrite_preserves_core
    {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env

/-- Rank side condition needed for preserving one common linearization witness
through a mutable-borrow fan-out.

For every concrete branch write, each *new borrow edge* whose target came from
the RHS type must point to a strictly lower-ranked base.  This is the local
acyclicity premise behind the old bare `EnvWrite.preserves_linearizedBy`
obligation. -/
def WriteBorrowTargetsRhsVarsBelowBranches (φ : Name → Nat) (rank : Nat)
    (env : Env) (path : Path) (writeTargets : List LVal) (rhsTy : Ty) : Prop :=
  ∀ target, target ∈ writeTargets → ∀ updated,
    EnvWrite rank env (prependPath path target) rhsTy updated →
    EnvWriteRhsBorrowTargetsBelow φ updated rhsTy

/-- Coherence obligations for every branch and branch join in a mutable-borrow
fan-out write.

This is the fan-out analogue of the strengthened assignment coherence premise.
Each concrete branch write must expose the write-coherence transport needed by
`EnvWrite.preserves_coherent_of_obligations`; each cons join must expose the
join-coherence transport needed by `EnvJoin.preserves_coherent_of_obligations`.
-/
structure WriteBorrowTargetsCoherenceObligations
    (rank : Nat) (env : Env) (path : Path) (writeTargets : List LVal)
    (rhsTy : Ty) : Prop where
  write
    (target : LVal) :
    target ∈ writeTargets →
    ∀ updated,
      EnvWrite rank env (prependPath path target) rhsTy updated →
      EnvWriteCoherenceObligations env updated (LVal.base (prependPath path target))
  join
    (target : LVal) (rest : List LVal) :
    target ∈ writeTargets →
    (∀ t, t ∈ rest → t ∈ writeTargets) →
    ∀ updated restEnv result,
      EnvWrite rank env (prependPath path target) rhsTy updated →
      WriteBorrowTargets rank env path rest rhsTy restEnv →
      EnvJoin updated restEnv result →
      EnvJoinCoherenceObligations updated restEnv result

/-- Constructive variant of `WriteBorrowTargets.preserves_core_of_crossLandmarks`
that does not use the bare `EnvWrite.preserves_linearizedBy` axiom.

The extra `WriteBorrowTargetsRhsVarsBelowBranches` premise is the small
borrow-inference/rank side condition needed to keep the same linearization witness
across every fan-out branch. -/
theorem WriteBorrowTargets.preserves_core_of_crossLandmarks
    (hlandmarks : UpdateBorrowInvariantCrossLandmarks)
    {rank : Nat} {env result : Env} {path : Path}
    {writeTargets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime}
    {φ : Name → Nat} :
    0 < rank →
    Coherent env →
    LinearizedBy φ env →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    (∀ target, target ∈ writeTargets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    WriteBorrowTargetsRhsVarsBelowBranches φ rank env path writeTargets rhsTy →
    WriteBorrowTargetsCoherenceObligations rank env path writeTargets rhsTy →
    WriteBorrowTargets rank env path writeTargets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro hrank hcoh hφ hcontained hrhs hleaf hbelow hfanoutCoh hwrites
  exact (WriteBorrowTargets.rec
    (motive_1 := fun _rank _env _path _oldTy _rhsTy _result _updatedTy _ =>
      True)
    (motive_2 := fun _rank env _path _writeTargets constructorTy result _ =>
      0 < _rank → Coherent env → LinearizedBy φ env →
      ∀ {slotLifetime},
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        (∀ target, target ∈ _writeTargets → ∀ targetSlot,
          env.slotAt (LVal.base (prependPath _path target)) = some targetSlot →
          WriteLeafTy env (LVal.path (prependPath _path target))
            targetSlot.ty constructorTy) →
        WriteBorrowTargetsRhsVarsBelowBranches φ _rank env _path _writeTargets constructorTy →
        WriteBorrowTargetsCoherenceObligations _rank env _path _writeTargets constructorTy →
        (ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env) ∧
          Coherent result ∧ LinearizedBy φ result)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by intro env old ty; trivial)
    (by intro env rank old joined ty _hshape _hjoin; trivial)
    (by intro env₁ env₂ rank path inner updatedInner ty hupdate ih; trivial)
    (by intro env₁ env₂ rank path targets ty hwrites ih; trivial)
    (by
      intro rank env path ty _hrank hcoh hlinBy slotLifetime hcontained _hrhs _hleaf
        _hbelow _hfanoutCoh
      exact ⟨⟨hcontained, BorrowTargetsTransport.refl env,
        ContainedBorrowsWellFormed.in_self hcontained⟩, hcoh, hlinBy⟩)
    (by
      intro rank env updated path target ty hwrite _htyped _ih
        hrank hcoh hlinBy slotLifetime hcontained hrhs _hleaf hbelow hfanoutCoh
      have hlinEnv : Linearizable env := Linearizable.of_linearizedBy hlinBy
      have hlinUBy :=
        EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
          hwrite hlinBy (hbelow target (by simp) updated hwrite)
      have hlinU := Linearizable.of_linearizedBy hlinUBy
      have hcohU := EnvWrite.preserves_coherent_of_obligations hcoh
        (hfanoutCoh.write target (by simp) updated hwrite)
      exact ⟨hlandmarks.envWrite_preserves_core hrank hcontained hrhs hwrite,
        hcohU, hlinUBy⟩)
    (by
      intro rank env updated restEnv result path target rest ty
        hwrite _htyped hwrites hjoin _ihWrite ihWrites
        hrank hcoh hlinBy slotLifetime hcontained hrhs hleaf hbelow hfanoutCoh
      have hlinEnv : Linearizable env := Linearizable.of_linearizedBy hlinBy
      have hlinUBy :=
        EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
          hwrite hlinBy (hbelow target (by simp) updated hwrite)
      have hlinU := Linearizable.of_linearizedBy hlinUBy
      have hcohU := EnvWrite.preserves_coherent_of_obligations hcoh
        (hfanoutCoh.write target (by simp) updated hwrite)
      rcases hlandmarks.envWrite_preserves_core hrank hcontained hrhs hwrite with
        ⟨hupdatedContained, hupdatedTransport, hupdatedInEnv⟩
      have hleafRest :
          ∀ t, t ∈ rest → ∀ slot,
            env.slotAt (LVal.base (prependPath path t)) = some slot →
            WriteLeafTy env (LVal.path (prependPath path t)) slot.ty ty := by
        intro t ht slot hslot
        exact hleaf t (List.mem_cons_of_mem target ht) slot hslot
      have hbelowRest :
          WriteBorrowTargetsRhsVarsBelowBranches φ rank env path rest ty := by
        intro t ht branch hbranch
        exact hbelow t (List.mem_cons_of_mem target ht) branch hbranch
      have hfanoutCohRest :
          WriteBorrowTargetsCoherenceObligations rank env path rest ty := {
        write := by
          intro t ht branch hbranch
          exact hfanoutCoh.write t (List.mem_cons_of_mem target ht) branch hbranch
        join := by
          intro t later ht hlater branch laterEnv branchResult hbranch hlaterWrites hbranchJoin
          exact hfanoutCoh.join t later (List.mem_cons_of_mem target ht)
            (fun u hu => List.mem_cons_of_mem target (hlater u hu))
            branch laterEnv branchResult hbranch hlaterWrites hbranchJoin
      }
      rcases ihWrites hrank hcoh hlinBy hcontained hrhs hleafRest hbelowRest
          hfanoutCohRest with
        ⟨⟨hrestContained, _hrestTransport, hrestInEnv⟩, hcohRest, hlinRestBy⟩
      have hlinRest := Linearizable.of_linearizedBy hlinRestBy
      have hlinRBy := EnvJoin.preserves_linearizedBy hjoin hlinUBy hlinRestBy
      have hlinR := Linearizable.of_linearizedBy hlinRBy
      have hjoinCoh : EnvJoinCoherenceObligations updated restEnv result :=
        hfanoutCoh.join target rest (by simp)
          (fun t ht => List.mem_cons_of_mem target ht)
          updated restEnv result hwrite hwrites hjoin
      have hcohR := EnvJoin.preserves_coherent_of_obligations hcohU hcohRest hjoinCoh
      have hupdShape : EnvShapePreserved env updated :=
        EnvWrite.shapePreserved_init hrank hwrite
          (fun slot hslot => hleaf target (by simp) slot hslot)
      have hrestShape : EnvShapePreserved env restEnv :=
        WriteBorrowTargets.shapePreserved_init hrank hwrites
          (fun t ht slot hslot =>
            hleaf t (List.mem_cons_of_mem target ht) slot hslot)
      have hbranch : ∀ x sL sR, updated.slotAt x = some sL → restEnv.slotAt x = some sR →
          PartialTy.sameShape sL.ty sR.ty :=
        EnvShapePreserved.branch_sameShape hupdShape hrestShape
      have hstrL := EnvJoin.fanOutShapeMap_left hjoin hbranch
      have hstrR := EnvJoin.fanOutShapeMap_right hjoin hbranch
      have hcontJoin :=
        ContainedBorrowsWellFormed.join_viaInvariants hjoin hstrL hstrR hlinR hcohR
          hupdatedContained hrestContained
      refine ⟨⟨hcontJoin,
        BorrowTargetsTransport.join_viaInvariants_left hjoin hstrL hlinR hcohR
          hcontJoin hupdatedTransport,
        ContainedBorrowsWellFormedIn.join_source hjoin hupdatedInEnv hrestInEnv⟩,
        hcohR, hlinRBy⟩)
    (by intro rank env₁ env₂ lv slot ty updatedTy hslot hupdate ih; trivial)
    hwrites hrank hcoh hφ hcontained hrhs hleaf hbelow hfanoutCoh).1

theorem UpdateBorrowInvariantObligations.of_crossLandmarks
    (hlandmarks : UpdateBorrowInvariantCrossLandmarks)
    (hfanoutRanked :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty} {φ : Name → Nat},
        WriteBorrowTargetsRhsVarsBelowBranches φ rank env path targets rhsTy)
    (hfanoutCoherence :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty},
        WriteBorrowTargetsCoherenceObligations rank env path targets rhsTy) :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed := by
    intro rank env result path targets rhsTy slotLifetime
      hrank hcoh hlin hcontained htargets hleaf hrhs hwrites
    rcases hlin with ⟨φ, hφ⟩
    rcases WriteBorrowTargets.preserves_core_of_crossLandmarks
        hlandmarks hrank hcoh hφ hcontained hrhs hleaf
        (hfanoutRanked (rank := rank) (env := env) (path := path)
          (targets := targets) (rhsTy := rhsTy) (φ := φ))
        (hfanoutCoherence (rank := rank) (env := env) (path := path)
          (targets := targets) (rhsTy := rhsTy))
        hwrites with
      ⟨hresultContained, htransport, _hresultInEnv⟩
    exact ⟨hresultContained, htransport htargets⟩

-- The deref-of-borrow join transport landmark (`borrow_borrow`, formerly the
-- `FullLValTypingJoinTransport` chain) is no longer needed: the write fan-out
-- driver (`WriteBorrowTargets.preserves_core_of_crossLandmarks`) now establishes
-- borrow-target join preservation directly and one-directionally via the
-- transport keystone (`ContainedBorrowsWellFormed.join_viaInvariants` etc.),
-- supplied with the runtime invariants `Coherent`/`Linearizable`.  The old
-- symmetric `FullLValTypingJoinTransport` structure and its consumers remain in
-- the file as dead (proven) scaffolding.

/-- Old borrow-target transport for one write, derived from the transport keystone.

This is one of the constructive pieces behind the legacy single-write Appendix
9.6 claim below.  It deliberately exposes the runtime facts the keystone needs:
the write result must be shape-preserving/strengthening from the source, already
linearized, coherent, and contained-borrow well formed.
-/
theorem EnvWrite.borrowTargetsTransport_of_shapeMap
    {rank : Nat} {env result : Env} {lv : LVal} {rhsTy : Ty}
    {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    BorrowTargetsTransport env result := by
  intro hwrite hshapeMap hlinResult hcohResult hcontainedResult
    slotLifetime targets htargets target htarget
  rcases htargets target htarget with
    ⟨sourceTy, sourceLifetime, hsourceTyping, hsourceOutlives, hsourceBase⟩
  have hresultBase : LValBaseOutlives result target slotLifetime :=
    LValBaseOutlives.write hwrite hsourceBase
  rcases fullJoinTransport_viaInvariants
      (source := env) (join := result) (target := target)
      (sourceTy := sourceTy) (sourceLifetime := sourceLifetime)
      (current := slotLifetime) (φ := φ) (N := φ (LVal.base target) + 1)
      hshapeMap hlinResult hcohResult
      (fun x slot mutable targets _hrank hslot hcontains =>
        hcontainedResult x slot mutable targets hslot hcontains)
      (Nat.lt_succ_self _) hsourceTyping hresultBase with
    ⟨resultTy, resultLifetime, hresultTyping, hresultOutlives⟩
  exact ⟨resultTy, resultLifetime, hresultTyping, hresultOutlives, hresultBase⟩

/-- Constructive packaging of the parts of the legacy single-write core claim
once the result-side invariants have been established separately.

The nontrivial old-target transport component is proved by
`EnvWrite.borrowTargetsTransport_of_shapeMap`; the two contained-borrow facts are
kept explicit because those are structural update obligations, not consequences
of a bare `EnvWrite` plus RHS well-formedness alone.
-/
theorem EnvWrite.preserves_core_appendix96_of_result_invariants
    {rank : Nat} {env result : Env} {lv : LVal} {rhsTy : Ty}
    {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    ContainedBorrowsWellFormedIn result env →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro hwrite hshapeMap hlinResult hcohResult hcontainedResult hresultInEnv
  exact ⟨hcontainedResult,
    EnvWrite.borrowTargetsTransport_of_shapeMap
      hwrite hshapeMap hlinResult hcohResult hcontainedResult,
    hresultInEnv⟩

/-- Appendix 9.6 core preservation for one positive-rank write, with the
result-side invariants exposed.

This is the proved replacement for the old bare claim.  A single `EnvWrite` plus
RHS per-target well-formedness is not enough to derive old-target transport; the
caller must also provide the shape map and result-side linearization/coherence
and contained-borrow facts needed by the transport keystone. -/
theorem EnvWrite.preserves_core_appendix96
    {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} {slotLifetime : Lifetime} {φ : Name → Nat} :
    0 < rank →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    ContainedBorrowsWellFormedIn result env →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro _hrank _hcontained _hrhs hwrite hshape hlinResult hcohResult
    hcontainedResult hresultInEnv
  exact EnvWrite.preserves_core_appendix96_of_result_invariants
    hwrite hshape hlinResult hcohResult hcontainedResult hresultInEnv

/-- Source environment for the bare Appendix 9.6 single-write counterexample.

Here `x : &[a]` with `a : int`, and `y : &[*x]`.  Thus `*x` is an old borrow
target that is well formed before the write.
-/
def coreAppendix96Env : Env :=
  (((Env.empty.update "a" { ty := .ty .int, lifetime := Lifetime.root }).update "b"
    { ty := .ty .unit, lifetime := Lifetime.root }).update "x"
      { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root }).update "y"
        { ty := .ty (.borrow false [.deref (.var "x")]), lifetime := Lifetime.root }

/-- Result of weakly writing `&[b]` into `x`, yielding `x : &[a,b]`. -/
def coreAppendix96Result : Env :=
  coreAppendix96Env.update "x"
    { ty := .ty (.borrow false [.var "a", .var "b"]), lifetime := Lifetime.root }

theorem coreAppendix96Env_deref_x_typing :
    LValTyping coreAppendix96Env (.deref (.var "x")) (.ty .int) Lifetime.root := by
  have hx : coreAppendix96Env.slotAt "x" =
      some { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
    simp [coreAppendix96Env, Env.update]
  have ha : coreAppendix96Env.slotAt "a" =
      some { ty := .ty .int, lifetime := Lifetime.root } := by
    simp [coreAppendix96Env, Env.update]
  exact LValTyping.borrow (LValTyping.var hx)
    (LValTargetsTyping.singleton (LValTyping.var ha))

theorem coreAppendix96Result_targets_not_typeable :
    ¬ ∃ ty lifetime,
      LValTargetsTyping coreAppendix96Result [.var "a", .var "b"] (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htargets⟩
  cases htargets with
  | cons hhead hrest hunion _hintersection =>
      rcases LValTyping.var_inv hhead with ⟨headSlot, hheadSlot, hheadTy, _⟩
      have hheadSlotEq : headSlot = { ty := .ty .int, lifetime := Lifetime.root } := by
        have ha : coreAppendix96Result.slotAt "a" =
            some { ty := .ty .int, lifetime := Lifetime.root } := by
          simp [coreAppendix96Result, coreAppendix96Env, Env.update]
        exact Option.some.inj (by rw [← hheadSlot, ha])
      have hheadSlotTy : headSlot.ty = .ty .int := by
        rw [hheadSlotEq]
      cases hrest with
      | singleton htarget =>
          rcases LValTyping.var_inv htarget with ⟨restSlot, hrestSlot, hrestTy, _⟩
          have hrestSlotEq : restSlot = { ty := .ty .unit, lifetime := Lifetime.root } := by
            have hb : coreAppendix96Result.slotAt "b" =
                some { ty := .ty .unit, lifetime := Lifetime.root } := by
              simp [coreAppendix96Result, coreAppendix96Env, Env.update]
            exact Option.some.inj (by rw [← hrestSlot, hb])
          have hrestSlotTy : restSlot.ty = .ty .unit := by
            rw [hrestSlotEq]
          have hheadTyPartialEq : PartialTy.ty _ = PartialTy.ty Ty.int :=
            hheadTy.symm.trans hheadSlotTy
          have hrestTyPartialEq : PartialTy.ty _ = PartialTy.ty Ty.unit :=
            hrestTy.symm.trans hrestSlotTy
          cases hheadTyPartialEq
          cases hrestTyPartialEq
          exact PartialTyUnion.int_unit_full_false hunion
      | cons _hhead2 hrest2 _hunion2 _hintersection2 =>
          exact False.elim (LValTargetsTyping.nil_false hrest2)

theorem coreAppendix96Result_deref_x_not_typeable :
    ¬ ∃ ty lifetime,
      LValTyping coreAppendix96Result (.deref (.var "x")) (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htyping⟩
  cases htyping with
  | box hsource =>
      rcases LValTyping.var_inv hsource with ⟨slot, hslot, hty, _⟩
      have hslotTy : slot.ty = .ty (.borrow false [.var "a", .var "b"]) := by
        simpa [coreAppendix96Result, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      cases hty.symm.trans hslotTy
  | borrow hsource htargets =>
      rcases LValTyping.var_inv hsource with ⟨slot, hslot, hty, _⟩
      have hslotTy : slot.ty = .ty (.borrow false [.var "a", .var "b"]) := by
        simpa [coreAppendix96Result, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      have hsourceTy : PartialTy.ty (.borrow _ _) =
          PartialTy.ty (.borrow false [.var "a", .var "b"]) := hty.symm.trans hslotTy
      cases hsourceTy
      exact coreAppendix96Result_targets_not_typeable ⟨ty, lifetime, htargets⟩

theorem coreAppendix96Env_contained :
    ContainedBorrowsWellFormed coreAppendix96Env := by
  intro z slot mutable targets hslot hcontains
  by_cases hzy : z = "y"
  · subst hzy
    have hslotEq : slot =
        { ty := .ty (.borrow false [.deref (.var "x")]), lifetime := Lifetime.root } := by
      have hy : coreAppendix96Env.slotAt "y" =
          some { ty := .ty (.borrow false [.deref (.var "x")]), lifetime := Lifetime.root } := by
        simp [coreAppendix96Env, Env.update]
      exact Option.some.inj (by rw [← hslot, hy])
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hcontainedTy : containedSlot.ty = .ty (.borrow false [.deref (.var "x")]) := by
      simpa [coreAppendix96Env, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hcontainedSlot).symm
    rw [hcontainedTy] at hcontainsTy
    cases hcontainsTy
    subst hslotEq
    intro target htarget
    simp at htarget
    subst htarget
    refine ⟨.int, Lifetime.root, coreAppendix96Env_deref_x_typing,
      LifetimeOutlives.refl _, ?_⟩
    have hx : coreAppendix96Env.slotAt "x" =
        some { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
      simp [coreAppendix96Env, Env.update]
    exact ⟨_, hx, LifetimeOutlives.refl _⟩
  · by_cases hzx : z = "x"
    · subst hzx
      have hslotEq : slot =
          { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
        have hx : coreAppendix96Env.slotAt "x" =
            some { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
          simp [coreAppendix96Env, Env.update]
        exact Option.some.inj (by rw [← hslot, hx])
      rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hcontainedTy : containedSlot.ty = .ty (.borrow false [.var "a"]) := by
        simpa [coreAppendix96Env, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hcontainedSlot).symm
      rw [hcontainedTy] at hcontainsTy
      cases hcontainsTy
      subst hslotEq
      intro target htarget
      simp at htarget
      subst htarget
      have ha : coreAppendix96Env.slotAt "a" =
          some { ty := .ty .int, lifetime := Lifetime.root } := by
        simp [coreAppendix96Env, Env.update]
      exact ⟨.int, Lifetime.root, LValTyping.var ha,
        LifetimeOutlives.refl _, ⟨_, ha, LifetimeOutlives.refl _⟩⟩
    · by_cases hzb : z = "b"
      · subst hzb
        rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
        have hcontainedTy : containedSlot.ty = .ty .unit := by
          simpa [coreAppendix96Env, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hcontainedSlot).symm
        rw [hcontainedTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hza : z = "a"
        · subst hza
          rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
          have hcontainedTy : containedSlot.ty = .ty .int := by
            simpa [coreAppendix96Env, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hcontainedSlot).symm
          rw [hcontainedTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : coreAppendix96Env.slotAt z = none := by
            simp [coreAppendix96Env, Env.update, Env.empty, hzy, hzx, hzb, hza]
          rw [hslot] at hnone
          cases hnone

theorem coreAppendix96_rhs_wellFormed :
    PartialTyBorrowsWellFormedInSlot coreAppendix96Env Lifetime.root
      (.ty (.borrow false [.var "b"])) := by
  intro mutable targets hcontains
  cases hcontains
  intro target htarget
  simp at htarget
  subst htarget
  have hb : coreAppendix96Env.slotAt "b" =
      some { ty := .ty .unit, lifetime := Lifetime.root } := by
    simp [coreAppendix96Env, Env.update]
  exact ⟨.unit, Lifetime.root, LValTyping.var hb,
    LifetimeOutlives.refl _, ⟨_, hb, LifetimeOutlives.refl _⟩⟩

theorem coreAppendix96_bad_weak_shape_incompatible :
    ¬ ShapeCompatible coreAppendix96Env
      (.ty (.borrow false [.var "a"])) (.ty (.borrow false [.var "b"])) := by
  intro hshape
  cases hshape with
  | borrow hleft hright hpointee =>
      rcases hleft (.var "a") (by simp) with ⟨leftLifetime, hleftTyping⟩
      rcases hright (.var "b") (by simp) with ⟨rightLifetime, hrightTyping⟩
      rcases LValTyping.var_inv hleftTyping with ⟨leftSlot, hleftSlot, hleftTy, _⟩
      rcases LValTyping.var_inv hrightTyping with ⟨rightSlot, hrightSlot, hrightTy, _⟩
      have hleftSlotTy : leftSlot.ty = .ty .int := by
        simpa [coreAppendix96Env, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hleftSlot).symm
      have hrightSlotTy : rightSlot.ty = .ty .unit := by
        simpa [coreAppendix96Env, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hrightSlot).symm
      have hleftTyEq : PartialTy.ty _ = PartialTy.ty Ty.int :=
        hleftTy.symm.trans hleftSlotTy
      have hrightTyEq : PartialTy.ty _ = PartialTy.ty Ty.unit :=
        hrightTy.symm.trans hrightSlotTy
      cases hleftTyEq
      cases hrightTyEq
      cases hpointee

theorem coreAppendix96Env_deref_x_targets :
    BorrowTargetsWellFormedInSlot coreAppendix96Env Lifetime.root [.deref (.var "x")] := by
  intro target htarget
  simp at htarget
  subst htarget
  refine ⟨.int, Lifetime.root, coreAppendix96Env_deref_x_typing,
    LifetimeOutlives.refl _, ?_⟩
  have hx : coreAppendix96Env.slotAt "x" =
      some { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
    simp [coreAppendix96Env, Env.update]
  exact ⟨_, hx, LifetimeOutlives.refl _⟩

theorem coreAppendix96_transport_fails :
    ¬ BorrowTargetsTransport coreAppendix96Env coreAppendix96Result := by
  intro htransport
  have hresultTargets := htransport coreAppendix96Env_deref_x_targets
  rcases hresultTargets (.deref (.var "x")) (by simp) with
    ⟨targetTy, targetLifetime, htyping, _houtlives, _hbase⟩
  exact coreAppendix96Result_deref_x_not_typeable ⟨targetTy, targetLifetime, htyping⟩

/-- The pre-strengthening Appendix 9.6 counterexample is now rejected locally.

The old weak rule could merge `x : &[a]` with RHS `&[b]`, producing `x :
&[a,b]` and invalidating the old target `*x`.  The strengthened `W-Weak` rule
requires the local `ShapeCompatible` premise, and the theorem above proves that
premise is false in this example.
-/
theorem EnvWrite.preserves_core_appendix96_counterexample_rejected :
    ¬ ShapeCompatible coreAppendix96Env
      (.ty (.borrow false [.var "a"])) (.ty (.borrow false [.var "b"])) :=
  coreAppendix96_bad_weak_shape_incompatible

/-- Legacy packaging of Appendix 9.6 cross-landmarks.

The broad single-write field is no longer hidden behind an axiom.  Older callers
that still want this package must provide that compatibility premise explicitly;
the proved replacement is `EnvWrite.preserves_core_appendix96`, whose statement
exposes the result-side invariants needed for old-target transport.
-/
theorem updateBorrowInvariantCrossLandmarks_appendix96
    (hwriteCore :
      ∀ {rank : Nat} {env result : Env} {lv : LVal}
        {rhsTy : Ty} {slotLifetime : Lifetime},
        0 < rank →
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
        EnvWrite rank env lv rhsTy result →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env) :
    UpdateBorrowInvariantCrossLandmarks where
  envWrite_preserves_core := by
    intro rank env result lv rhsTy slotLifetime hrank hcontained hrhs hwrite
    exact hwriteCore hrank hcontained hrhs hwrite

structure UpdateBorrowInvariantLandmarks : Prop where
  envWrite_preserves_observerTargets
    {rank : Nat} {env result : Env} {lv : LVal}
    {observerTargets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime observerTargets
  envJoin_preserves_containedBorrowsWellFormed
    {left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormed join
  envJoin_preserves_observerTargets
    {left right join : Env} {targets : List LVal} {slotLifetime : Lifetime} :
    EnvJoin left right join →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets

theorem WriteBorrowTargets.preserves_observerTargets_of_landmarks
    (hlandmarks : UpdateBorrowInvariantLandmarks)
    {rank : Nat} {env result : Env} {path : Path}
    {writeTargets observerTargets : List LVal} {rhsTy : Ty}
    {slotLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path writeTargets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime observerTargets := by
  intro hcontained hobservers hrhs hwrites
  exact WriteBorrowTargets.rec
    (motive_1 := fun _rank _env _path _oldTy _rhsTy _result _updatedTy _ =>
      True)
    (motive_2 := fun _rank env _path _writeTargets constructorTy result _ =>
      ∀ {observerTargets slotLifetime},
        ContainedBorrowsWellFormed env →
        BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsWellFormedInSlot result slotLifetime observerTargets)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by
      intro env old ty
      trivial)
    (by
      intro env rank old joined ty _hshape _hjoin
      trivial)
    (by
      intro env₁ env₂ rank path inner updatedInner ty hupdate ih
      trivial)
    (by
      intro env₁ env₂ rank path targets ty hwrites ih
      trivial)
    (by
      intro rank env path ty observerTargets slotLifetime hcontained hobservers _hrhs
      exact ⟨hcontained, hobservers⟩)
    (by
      intro rank env updated path target ty hwrite _htyped _ih
        observerTargets slotLifetime hcontained hobservers hrhs
      exact hlandmarks.envWrite_preserves_observerTargets
        hcontained hobservers hrhs hwrite)
    (by
      intro rank env updated restEnv result path target rest ty
        hwrite _htyped _hwrites hjoin _ihWrite ihWrites
        observerTargets slotLifetime hcontained hobservers hrhs
      rcases hlandmarks.envWrite_preserves_observerTargets
          hcontained hobservers hrhs hwrite with
        ⟨hupdatedContained, hupdatedObservers⟩
      rcases ihWrites hcontained hobservers hrhs with
        ⟨hrestContained, hrestObservers⟩
      exact ⟨
        hlandmarks.envJoin_preserves_containedBorrowsWellFormed
          hjoin hupdatedContained hrestContained,
        hlandmarks.envJoin_preserves_observerTargets hjoin
          hupdatedObservers hrestObservers⟩)
    (by
      intro rank env₁ env₂ lv slot ty updatedTy hslot hupdate ih
      trivial)
    hwrites hcontained hobservers hrhs

theorem UpdateBorrowInvariantObligations.of_landmarks
    (hlandmarks : UpdateBorrowInvariantLandmarks) :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed := by
    intro rank env result path targets rhsTy slotLifetime
      _hrank _hcoh _hlin hcontained htargets _hleaf hrhs hwrites
    exact WriteBorrowTargets.preserves_observerTargets_of_landmarks
      hlandmarks hcontained htargets hrhs hwrites

/--
Definition 3.23 `writeBorrowTargets` borrow-invariant obligation.

This is the remaining paper-level update invariant needed by Lemma 4.9.  The
legacy theorem `updateBorrowInvariantObligations_appendix96` below records the
old Appendix 9.6 target as explicit result-side rank/coherence premises rather
than hiding them as axioms.
-/
theorem WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets := by
  exact hobligations.writeBorrowTargets_preserves_containedBorrowsWellFormed

/-- Appendix Lemma 9.6 package for the borrow-target fan-out.

This is an obligation-parametric compatibility route: the broad write-core and
fan-out rank/coherence facts are explicit premises until the remaining
result-side update obligations are proved constructively.
-/
theorem updateBorrowInvariantObligations_appendix96
    (hwriteCore :
      ∀ {rank : Nat} {env result : Env} {lv : LVal}
        {rhsTy : Ty} {slotLifetime : Lifetime},
        0 < rank →
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
        EnvWrite rank env lv rhsTy result →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env)
    (hfanoutRanked :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty} {φ : Name → Nat},
        WriteBorrowTargetsRhsVarsBelowBranches φ rank env path targets rhsTy)
    (hfanoutCoherence :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty},
        WriteBorrowTargetsCoherenceObligations rank env path targets rhsTy) :
    UpdateBorrowInvariantObligations := by
  exact UpdateBorrowInvariantObligations.of_crossLandmarks
    (updateBorrowInvariantCrossLandmarks_appendix96 hwriteCore)
    hfanoutRanked hfanoutCoherence

/--
Appendix Lemma 9.6 at the Definition 3.23 update-relation level.

The statement tracks both components needed by the enclosing `write` rule:
the intermediate environment remains contained-borrow well formed, and the
partial type returned by `update_k` has well-formed contained borrows at the
allocation lifetime of the slot being rebuilt.
-/
theorem UpdateAtPath.preserves_containedBorrowsWellFormed_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {rank : Nat} {env result : Env} {path : Path}
    {oldTy updatedTy : PartialTy} {rhsTy : Ty} {slotLifetime : Lifetime} :
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime oldTy →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    UpdateAtPath rank env path oldTy rhsTy result updatedTy →
    ContainedBorrowsWellFormed result ∧
      PartialTyBorrowsWellFormedInSlot result slotLifetime updatedTy := by
  intro hcoh hlin hcontained holdTy hrhsTy hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun _rank env _path oldTy constructorTy result updatedTy _ =>
      Coherent env → Linearizable env →
      ∀ {slotLifetime},
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime oldTy →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        ContainedBorrowsWellFormed result ∧
          PartialTyBorrowsWellFormedInSlot result slotLifetime updatedTy)
    (motive_2 := fun _rank _env _path _targets _rhsTy _result _ => True)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by
      intro env old ty hcoh hlin slotLifetime hcontained _holdTy hrhsTy
      exact ⟨hcontained, hrhsTy⟩)
    (by
      intro env rank old joined ty _hshape hjoin hcoh hlin slotLifetime hcontained holdTy hrhsTy
      exact ⟨hcontained,
        PartialTyBorrowsWellFormedInSlot.of_partialTyUnion
          (by simpa [PartialTyUnion] using hjoin) holdTy hrhsTy⟩)
    (by
      intro env₁ env₂ rank path inner updatedInner ty _hinner ih
        hcoh hlin slotLifetime hcontained holdTy hrhsTy
      rcases ih hcoh hlin hcontained
          (PartialTyBorrowsWellFormedInSlot.box_inv holdTy)
          hrhsTy with
        ⟨hcontainedResult, hupdatedInner⟩
      exact ⟨hcontainedResult, PartialTyBorrowsWellFormedInSlot.box hupdatedInner⟩)
    (by
      intro env₁ env₂ rank path targets ty hwrites _ih
        hcoh hlin slotLifetime hcontained holdTy hrhsTy
      have htargets :
          BorrowTargetsWellFormedInSlot env₁ slotLifetime targets :=
        holdTy PartialTyContains.here
      have htargetLeaves :
          ∀ target, target ∈ targets → ∀ targetSlot,
            env₁.slotAt (LVal.base (prependPath path target)) = some targetSlot →
            WriteLeafTy env₁ (LVal.path (prependPath path target)) targetSlot.ty ty :=
        WriteBorrowTargets.initialized_leaves_appendix96 htargets hwrites
      rcases WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
          hobligations (Nat.succ_pos rank) hcoh hlin hcontained htargets htargetLeaves
          hrhsTy hwrites with
        ⟨hcontainedResult, htargetsResult⟩
      exact ⟨hcontainedResult, by
        intro mutable selected hcontains
        cases hcontains
        exact htargetsResult⟩)
    (by
      intro rank env path ty
      trivial)
    (by
      intro rank env updated path target ty _hwrite _ih
      trivial)
    (by
      intro rank env updated restEnv result path target rest ty
        _hwrite _hwrites _hjoin _ihWrite _ihWrites
      trivial)
    (by
      intro rank env₁ env₂ lv slot ty updatedTy _hslot _hupdate _ih
      trivial)
    hupdate hcoh hlin hcontained holdTy hrhsTy

/--
Appendix Lemma 9.6, `W-Box` branch of Definition 3.23.

Updating through an owned box recursively updates the boxed partial type, then
replaces the original base slot with `.box updatedInner`.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_box_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ writeEnv env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {inner updatedInner oldTy : PartialTy}
    {rhs : Term} {rhsTy : Ty} {writeSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    env₂.slotAt (LVal.base lhs) = some writeSlot →
    writeSlot.ty = .box inner →
    UpdateAtPath 0 env₂ (LVal.path lhs) inner rhsTy writeEnv updatedInner →
    env₃ = writeEnv.update (LVal.base lhs)
      { writeSlot with ty := .box updatedInner } →
    ¬ WriteProhibited env₃ (.deref lhs) →
    ContainedBorrowsWellFormed env₃ := by
  intro hwellInitial hwellFormed hLhs _htargetLifetime hRhs _hshape hwellRhs
    hwriteSlot hwriteTy hinnerUpdate henv₃ hnotWrite
  subst henv₃
  have htargetOutlivesSlot :
      targetLifetime ≤ writeSlot.lifetime :=
    TermTyping.target_lifetime_outlives_surviving_base_slot
      hwellInitial hLhs hRhs (by simpa [LVal.base] using hwriteSlot)
  have hslotPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime writeSlot.ty :=
    ContainedBorrowsWellFormed.slot_partial hwellFormed.1 hwriteSlot
  have hinnerPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime inner := by
    rw [hwriteTy] at hslotPartial
    exact PartialTyBorrowsWellFormedInSlot.box_inv hslotPartial
  have hrhsPartialAtTarget :
      PartialTyBorrowsWellFormedInSlot env₂ targetLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellRhs
  have hrhsPartialAtSlot :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.weaken
      hrhsPartialAtTarget htargetOutlivesSlot
  rcases UpdateAtPath.preserves_containedBorrowsWellFormed_appendix96
      hobligations hwellFormed.2.2.1 hwellFormed.2.2.2 hwellFormed.1 hinnerPartial
      hrhsPartialAtSlot hinnerUpdate with
    ⟨hcontainedWriteEnv, hupdatedInnerPartial⟩
  have hnotWriteVar :
      ¬ WriteProhibited
        (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
        (.var (LVal.base lhs)) := by
    exact not_writeProhibited_var_base hnotWrite
  have hslotTargets :
      PartialTyBorrowsWellFormedInSlot
        (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
        writeSlot.lifetime
        ({ writeSlot with ty := .box updatedInner }).ty := by
    change PartialTyBorrowsWellFormedInSlot
      (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
      writeSlot.lifetime
      (.box updatedInner)
    have hboxedPartial :
        PartialTyBorrowsWellFormedInSlot writeEnv writeSlot.lifetime
          (.box updatedInner) :=
      PartialTyBorrowsWellFormedInSlot.box hupdatedInnerPartial
    intro mutable targets hcontains
    have htransported :
        PartialTyBorrowsWellFormedInSlot
          (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
          writeSlot.lifetime
          (.box updatedInner) :=
      PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts
        (x := LVal.base lhs)
        (slot := { writeSlot with ty := .box updatedInner })
        (partialTy := .box updatedInner)
        hnotWriteVar
        hboxedPartial
        (by
          intro mutable targets hcontains target htarget
          have hcontainsUpdated :
              (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner }) ⊢
                LVal.base lhs ↝ Ty.borrow mutable targets :=
            ⟨{ writeSlot with ty := .box updatedInner },
              by simp [Env.update],
              hcontains⟩
          exact not_pathConflicts_of_not_writeProhibited_contains
            hnotWriteVar hcontainsUpdated htarget)
    exact htransported hcontains
  exact ContainedBorrowsWellFormed.update_slot
    hcontainedWriteEnv hslotTargets hnotWriteVar

/--
Appendix Lemma 9.6, `W-MutB` branch of Definition 3.23.

Updating through a mutable borrow writes every possible borrowed target at
`rank + 1` and joins the resulting environments.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_mutBorrow_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {targets : List LVal} {oldTy : PartialTy}
    {rhs : Term} {rhsTy : Ty} {writeSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    env₂.slotAt (LVal.base lhs) = some writeSlot →
    writeSlot.ty = .ty (.borrow true targets) →
    WriteBorrowTargets 1 env₂ (LVal.path lhs) targets rhsTy env₃ →
    ¬ WriteProhibited
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
      (.deref lhs) →
    ContainedBorrowsWellFormed
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) }) := by
  intro hwellInitial hwellFormed hLhs _htargetLifetime hRhs _hshape hwellRhs
    hwriteSlot hwriteTy hwrites hnotWrite
  have htargetOutlivesSlot :
      targetLifetime ≤ writeSlot.lifetime :=
    TermTyping.target_lifetime_outlives_surviving_base_slot
      hwellInitial hLhs hRhs (by simpa [LVal.base] using hwriteSlot)
  have hslotPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime writeSlot.ty :=
    ContainedBorrowsWellFormed.slot_partial hwellFormed.1 hwriteSlot
  have htargetsOld :
      BorrowTargetsWellFormedInSlot env₂ writeSlot.lifetime targets := by
    rw [hwriteTy] at hslotPartial
    exact hslotPartial PartialTyContains.here
  have hrhsPartialAtTarget :
      PartialTyBorrowsWellFormedInSlot env₂ targetLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellRhs
  have hrhsPartialAtSlot :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.weaken
      hrhsPartialAtTarget htargetOutlivesSlot
  have htargetLeaves :
      ∀ target, target ∈ targets → ∀ targetSlot,
        env₂.slotAt (LVal.base (prependPath (LVal.path lhs) target)) = some targetSlot →
        WriteLeafTy env₂ (LVal.path (prependPath (LVal.path lhs) target))
          targetSlot.ty rhsTy :=
    WriteBorrowTargets.initialized_leaves_appendix96 htargetsOld hwrites
  rcases WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
      hobligations (by decide : 0 < 1) hwellFormed.2.2.1 hwellFormed.2.2.2
        hwellFormed.1 htargetsOld htargetLeaves hrhsPartialAtSlot hwrites with
    ⟨hcontainedWriteEnv, htargetsResult⟩
  have hnotWriteVar :
      ¬ WriteProhibited
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        (.var (LVal.base lhs)) := by
    exact not_writeProhibited_var_base hnotWrite
  have htargetsFinal :
      BorrowTargetsWellFormedInSlot
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        writeSlot.lifetime targets :=
    BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
      (x := LVal.base lhs)
      (slot := { writeSlot with ty := .ty (.borrow true targets) })
      hnotWriteVar
      htargetsResult
      (by
        intro target htarget
        have hcontainsUpdated :
            (env₃.update (LVal.base lhs)
              { writeSlot with ty := .ty (.borrow true targets) }) ⊢
              LVal.base lhs ↝ Ty.borrow true targets :=
          ⟨{ writeSlot with ty := .ty (.borrow true targets) },
            by simp [Env.update],
            PartialTyContains.here⟩
        exact not_pathConflicts_of_not_writeProhibited_contains
          hnotWriteVar hcontainsUpdated htarget)
  have hslotTargets :
      PartialTyBorrowsWellFormedInSlot
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        writeSlot.lifetime
        ({ writeSlot with ty := .ty (.borrow true targets) }).ty := by
    change PartialTyBorrowsWellFormedInSlot
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
      writeSlot.lifetime
      (.ty (.borrow true targets))
    intro mutable selected hcontains
    cases hcontains
    exact htargetsFinal
  exact ContainedBorrowsWellFormed.update_slot
    hcontainedWriteEnv hslotTargets hnotWriteVar

/--
Appendix Lemma 9.6, dereference/update component.

This is the part that needs the mutual induction over Definition 3.23:
`W-Box` recurses into the path, while `W-MutB` switches to
`writeBorrowTargets` and uses the environment-join borrow invariant.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ (.deref lhs) rhsTy env₃ →
    ¬ WriteProhibited env₃ (.deref lhs) →
    ContainedBorrowsWellFormed env₃ := by
  intro hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  cases hwrite with
  | intro hwriteSlot hupdate =>
      rename_i writeEnv writeSlot updatedTy
      simp [LVal.base] at hwriteSlot
      have hupdateCons :
          UpdateAtPath 0 env₂ (() :: LVal.path lhs) writeSlot.ty rhsTy
            writeEnv updatedTy := by
        simpa [LVal.path_deref_cons] using hupdate
      rcases UpdateAtPath.cons_inv hupdateCons with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, hwriteTy, hupdatedTy, hinnerUpdate⟩
        have hnotWriteBox :
            ¬ WriteProhibited
              (writeEnv.update (LVal.base lhs)
                { writeSlot with ty := .box updatedInner })
              (.deref lhs) := by
          simpa [LVal.base, hupdatedTy] using hnotWrite
        simpa [LVal.base, hupdatedTy] using
          EnvWrite.preserves_containedBorrowsWellFormed_deref_box_appendix96
            hobligations
            (lhs := lhs)
            hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
            hwriteSlot hwriteTy hinnerUpdate rfl hnotWriteBox
      · rcases hborrow with ⟨targets, hwriteTy, hupdatedTy, hwrites⟩
        have hwritesOne :
            WriteBorrowTargets 1 env₂ (LVal.path lhs) targets rhsTy writeEnv := by
          simpa using hwrites
        have hnotWriteBorrow :
            ¬ WriteProhibited
              (writeEnv.update (LVal.base lhs)
                { writeSlot with ty := .ty (.borrow true targets) })
              (.deref lhs) := by
          simpa [LVal.base, hupdatedTy] using hnotWrite
        simpa [LVal.base, hupdatedTy] using
          EnvWrite.preserves_containedBorrowsWellFormed_deref_mutBorrow_appendix96
            hobligations
            (lhs := lhs)
            hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
            hwriteSlot hwriteTy hwritesOne hnotWriteBorrow

/--
Appendix Lemma 9.6, borrow-target component.

The proof is the paper's induction over Definition 3.23:

* `W-Strong`/`W-Weak` reduce to replacing the base slot and checking the
  contained borrows of the updated partial type.
* `W-Box` is the recursive path case.
* `W-MutB` uses the corresponding induction over `writeBorrowTargets`, whose
  cons case is discharged by the environment-join borrow invariant.

The statement is deliberately at the assignment boundary rather than at a
syntactic variable case.  The right-hand side may change the environment from
`env₁` to `env₂`, and a write through `*w` may fan out through mutable-borrow
targets before joining the resulting environments.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_appendix96
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ContainedBorrowsWellFormed env₃ := by
  intro hobligations hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
    hwrite hnotWrite
  cases lhs with
  | var x =>
      rcases LValTyping.var_inv hLhs with
        ⟨sourceSlot, hsourceSlot, _hsourceTy, hsourceLifetime⟩
      cases hwrite with
      | intro hwriteSlot hupdate =>
          rename_i writeEnv writeSlot updatedTy
          simp [LVal.base] at hwriteSlot
          rcases (TermTyping.slot_lifetime_survives.1 hRhs)
              (by simpa [hsourceLifetime] using htargetLifetime)
              hsourceSlot with
            ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
          have hwriteSlotEq : writeSlot = rhsSlot := by
            have hsomeEq : some writeSlot = some rhsSlot := by
              rw [← hwriteSlot, hrhsSlot]
            exact Option.some.inj hsomeEq
          have hwriteLifetime : writeSlot.lifetime = targetLifetime := by
            rw [hwriteSlotEq, ← hrhsLifetime, hsourceLifetime]
          have hLhs₂ : LValTyping env₂ (.var x) writeSlot.ty targetLifetime := by
            rw [← hwriteLifetime]
            exact LValTyping.var hwriteSlot
          exact EnvWrite.preserves_containedBorrowsWellFormed_var
            hwellFormed hLhs₂ hwellRhs
            (EnvWrite.intro hwriteSlot hupdate)
            hnotWrite
    | deref lhs =>
        exact EnvWrite.preserves_containedBorrowsWellFormed_deref_appendix96
          hobligations hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
          hwrite hnotWrite

theorem EnvWrite.preserves_containedBorrowsWellFormed {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ContainedBorrowsWellFormed env₃ := by
  exact EnvWrite.preserves_containedBorrowsWellFormed_appendix96

/-- Assignment/update well-formedness using the precise RHS-edge rank premise.

The caller supplies the linearization witness for the pre-write environment,
proves that every newly installed RHS borrow edge points to a lower-ranked base,
and provides the lvalue-coherence transport facts for the write result. -/
theorem EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  have hlin3By :=
    EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all hwrite hlinBy hbelow
  have hlin3 := Linearizable.of_linearizedBy hlin3By
  have hcoh3 := EnvWrite.preserves_coherent_of_obligations
    hwellFormed.2.2.1 hwriteCoh
  exact ⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations hwellInitial hwellFormed hLhs
      htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite,
    EnvWrite.preserves_slotsOutlive hwellFormed.2.1 hwrite, hcoh3, hlin3⟩

/-- Assignment-level write-coherence side condition.

This is the remaining coherence proof boundary for `T-Assign`: after the RHS is
typed, the ranked write is performed, and the RHS borrow edges are known to point
downward, the resulting environment must be coherent.  The old
`EnvWrite.preserves_coherent` axiom tried to prove this from a per-target RHS
well-formedness premise, which is too weak.  This side condition is stated at the
assignment boundary where the needed typing/shape/rank facts are available.
-/
def AssignmentWritePreservesCoherent : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    Coherent env₃

/-- Structured assignment-level replacement for `AssignmentWritePreservesCoherent`.

This avoids asking directly for `Coherent env₃`.  Instead it asks for the two
lvalue-transport facts that are sufficient to prove coherence of the result:
old-root borrow typings transport back to `env₂`, while borrow typings rooted at
the written base provide their joint target-list typings in `env₃`.
-/
def AssignmentWriteCoherenceObligations : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs)

theorem AssignmentWritePreservesCoherent.of_coherenceObligations
    (hobligations : AssignmentWriteCoherenceObligations) :
    AssignmentWritePreservesCoherent := by
  intro env₁ env₂ env₃ typing lifetime targetLifetime lhs oldTy rhs rhsTy φ
    hwellInitial hwellFormed hlinBy hbelow hLhs htargetLifetime hRhs hshape
    hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_coherent_of_obligations hwellFormed.2.2.1
    (hobligations hwellInitial hwellFormed hlinBy hbelow hLhs htargetLifetime
      hRhs hshape hwellRhs hwrite hnotWrite)

/-- Assignment/update well-formedness using explicit rank and coherence premises. -/
theorem EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    AssignmentWritePreservesCoherent →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  have hlin3By :=
    EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all hwrite hlinBy hbelow
  have hlin3 := Linearizable.of_linearizedBy hlin3By
  have hcoh3 := hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact ⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations hwellInitial
      hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite,
    EnvWrite.preserves_slotsOutlive hwellFormed.2.1 hwrite, hcoh3, hlin3⟩

/-- Assignment preservation variant with the explicit RHS-edge rank premise. -/
theorem assign_preserves_wellFormed_of_rhsBorrowTargetsBelow
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow hobligations
    hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs htargetLifetime
    hRhs hshape hwellRhs hwrite hnotWrite

/-- Assignment preservation variant with explicit RHS-edge rank and coherence. -/
theorem assign_preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    AssignmentWritePreservesCoherent →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite

def DropFullLValTypingTransport (env : Env) (parent child : Lifetime) : Prop :=
  ∀ {lv targetTy targetLifetime},
    LValBaseOutlives env lv parent →
    LValTyping env lv (.ty targetTy) targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv (.ty targetTy) targetLifetime

/--
Appendix Lemma 9.5 target-stability fragment.

If an lval is typed in a well-formed block body, its base slot survives the
enclosing parent lifetime, and the reached location also lives at the parent
side, then dropping the immediate child lifetime preserves the lval typing.
-/
theorem LValTyping.dropLifetime_child_of_base_outlives {env : Env}
    {parent child : Lifetime} {lv : LVal} {targetTy : Ty}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    LValBaseOutlives env lv parent →
    LValTyping env lv (.ty targetTy) targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv (.ty targetTy) targetLifetime := by
  intro hchild hwellBody hbase htyping houtlives
  have htransport :
      (∀ {lv partialTy lifetime},
        LValTyping env lv partialTy lifetime →
        LValBaseOutlives env lv parent →
        lifetime ≤ parent →
        LValTyping (env.dropLifetime child) lv partialTy lifetime) ∧
      (∀ {targets partialTy lifetime},
        LValTargetsTyping env targets partialTy lifetime →
        (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
        lifetime ≤ parent →
        LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime) := by
    constructor
    · intro lv partialTy lifetime htyping
      exact LValTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
        (motive_2 := fun targets partialTy lifetime _ =>
          (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
          lifetime ≤ parent →
          LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
        (by
          intro x slot hslot _hbase houtlives
          exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
            ⟨hslot, by
              intro hslotLifetime
              subst hslotLifetime
              exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.box (ih hbase houtlives))
        (by
          intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
            hborrow _htargets ihBorrow ihTargets hbase houtlives
          have hborrowLifetime : _borrowLifetime ≤ parent :=
            LValTyping.lifetime_outlives_of_base_outlives_one
              hwellBody.1 hborrow hbase
          have hwellTargetsAtBorrow :
              BorrowTargetsWellFormed env targets _borrowLifetime :=
            LValTyping.containedBorrowTargetsWellFormed_at_lifetime
              hwellBody.1 hborrow PartialTyContains.here
          have hwellTargets :
              BorrowTargetsWellFormed env targets parent :=
            BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
          exact LValTyping.borrow
            (ihBorrow hbase hborrowLifetime)
            (ihTargets
              (by
                intro target htarget
                rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
                exact hbaseTarget)
              houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
            _hhead _hrest hunion hintersection ihHead ihRest hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
    · intro targets partialTy lifetime htyping
      exact LValTargetsTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
        (motive_2 := fun targets partialTy lifetime _ =>
          (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
          lifetime ≤ parent →
          LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
        (by
          intro x slot hslot _hbase houtlives
          exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
            ⟨hslot, by
              intro hslotLifetime
              subst hslotLifetime
              exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.box (ih hbase houtlives))
        (by
          intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
            hborrow _htargets ihBorrow ihTargets hbase houtlives
          have hborrowLifetime : _borrowLifetime ≤ parent :=
            LValTyping.lifetime_outlives_of_base_outlives_one
              hwellBody.1 hborrow hbase
          have hwellTargetsAtBorrow :
              BorrowTargetsWellFormed env targets _borrowLifetime :=
            LValTyping.containedBorrowTargetsWellFormed_at_lifetime
              hwellBody.1 hborrow PartialTyContains.here
          have hwellTargets :
              BorrowTargetsWellFormed env targets parent :=
            BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
          exact LValTyping.borrow
            (ihBorrow hbase hborrowLifetime)
            (ihTargets
              (by
                intro target htarget
                rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
                exact hbaseTarget)
              houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
            _hhead _hrest hunion hintersection ihHead ihRest hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
  exact htransport.1 htyping hbase houtlives

theorem LValTargetsTyping.dropLifetime_child_of_member_base_outlives {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hbaseTargets htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy targetLifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      targetLifetime ≤ parent →
      LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime)
    ?var ?box ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget hbaseTargets houtlives
    exact LValTargetsTyping.singleton
      (LValTyping.dropLifetime_child_of_base_outlives
        hchild hwellBody (hbaseTargets target (by simp)) htarget houtlives)
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest hbaseTargets houtlives
    exact LValTargetsTyping.cons
      (LValTyping.dropLifetime_child_of_base_outlives hchild hwellBody
        (hbaseTargets target (by simp)) hhead
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives))
      (ihRest
        (by
          intro selected hselected
          exact hbaseTargets selected (by simp [hselected]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives))
      hunion hintersection

theorem LValTargetsTyping.dropLifetime_child_of_wellFormedTargets {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    BorrowTargetsWellFormed env targets parent →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hwellTargets htyping houtlives
  exact LValTargetsTyping.dropLifetime_child_of_member_base_outlives
    hchild hwellBody
    (by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
        ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbase⟩
      exact hbase)
    htyping houtlives

/-- Backward typing across a lifetime drop: `dropLifetime` only *removes* slots
(leaving the rest unchanged), so any typing in the dropped environment also holds
in the original. -/
theorem LValTyping.of_dropLifetime {env : Env} {child : Lifetime}
    {lv : LVal} {p : PartialTy} {lf : Lifetime}
    (h : LValTyping (env.dropLifetime child) lv p lf) : LValTyping env lv p lf := by
  refine LValTyping.rec
    (motive_1 := fun lv p lf _ => LValTyping env lv p lf)
    (motive_2 := fun targets p lf _ => LValTargetsTyping env targets p lf)
    ?var ?box ?borrow ?singleton ?cons h
  · intro x slot hslot
    rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _⟩
    exact LValTyping.var henvSlot
  · intro _lv _inner _lifetime _htyping ih
    exact LValTyping.box ih
  · intro _lv _mutable _targets _bLf _tLf _tTy _hborrow _htargets ihBorrow ihTargets
    exact LValTyping.borrow ihBorrow ihTargets
  · intro _target _ty _lifetime _htarget ih
    exact LValTargetsTyping.singleton ih
  · intro _target _rest _headTy _headLf _restLf _lf _restTy _unionTy
      _hhead _hrest hunion hint ihHead ihRest
    exact LValTargetsTyping.cons ihHead ihRest hunion hint

theorem LValTargetsTyping.dropLifetime_child_of_transport {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    DropFullLValTypingTransport env parent child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro htransport hbaseTargets htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy targetLifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      targetLifetime ≤ parent →
      LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime)
    ?var ?box ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget hbaseTargets houtlives
    exact LValTargetsTyping.singleton
      (htransport (hbaseTargets target (by simp)) htarget houtlives)
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest hbaseTargets houtlives
    exact LValTargetsTyping.cons
      (htransport (hbaseTargets target (by simp)) hhead
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives))
      (ihRest
        (by
          intro selected hselected
          exact hbaseTargets selected (by simp [hselected]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives))
      hunion hintersection

theorem BorrowTargetsWellFormedInSlot.dropLifetime_child_of_transport
    {env : Env} {parent child slotLifetime : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    slotLifetime ≤ parent →
    BorrowTargetsWellFormedInSlot (env.dropLifetime child) slotLifetime targets := by
  intro hchild htransport htargets hslotParent target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htyping, htargetOutlivesSlot, hbase⟩
  have hbaseParent : LValBaseOutlives env target parent := by
    rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
    exact ⟨baseSlot, hbaseSlot,
      LifetimeOutlives.trans hbaseOutlives hslotParent⟩
  refine ⟨targetTy, targetLifetime,
    htransport hbaseParent htyping
      (LifetimeOutlives.trans htargetOutlivesSlot hslotParent),
    htargetOutlivesSlot, ?_⟩
  exact LValBaseOutlives.dropLifetime_child hchild hslotParent hbase

theorem BorrowTargetsWellFormed.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormed env targets parent →
    BorrowTargetsWellFormed (env.dropLifetime child) targets parent := by
  intro hchild htransport htargets
  cases htargets with
  | intro hmembers =>
      refine BorrowTargetsWellFormed.intro ?_
      intro target htarget
      rcases hmembers target htarget with
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
      have hbaseParent : LValBaseOutlives env target parent := by
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        exact ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
      refine ⟨targetTy, targetLifetime,
        htransport hbaseParent htyping houtlives, houtlives, ?_⟩
      exact LValBaseOutlives.dropLifetime_child hchild
        (LifetimeOutlives.refl parent) hbase

theorem WellFormedTy.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    WellFormedTy env ty parent →
    WellFormedTy (env.dropLifetime child) ty parent := by
  intro hchild htransport hwellTy
  induction hwellTy with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | borrow htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.dropLifetime_child_of_transport
          hchild htransport htargets)
  | box _hinner ih =>
      exact WellFormedTy.box (ih hchild htransport)

theorem ContainedBorrowsWellFormed.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    DropFullLValTypingTransport env parent child →
    ContainedBorrowsWellFormed (env.dropLifetime child) := by
  intro hchild hwellBody htransport x slot mutable targets hslot hcontains
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨holdSlot, hslotNeChild⟩
  have holdContains : env ⊢ x ↝ Ty.borrow mutable targets :=
    EnvContains.dropLifetime_of_contains hcontains
  have hslotParent : slot.lifetime ≤ parent :=
    LifetimeChild.parent_of_outlives_child_ne hchild
      (hwellBody.2.1 x slot holdSlot) hslotNeChild
  exact BorrowTargetsWellFormedInSlot.dropLifetime_child_of_transport
    hchild
    htransport
    (hwellBody.1 x slot mutable targets holdSlot holdContains)
    hslotParent

/-- `Linearizable` is preserved by a lifetime drop (the same rank function works;
`dropLifetime` only removes slots). -/
theorem Linearizable.dropLifetime_child {env : Env} {child : Lifetime}
    (h : Linearizable env) : Linearizable (env.dropLifetime child) := by
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _⟩
  exact hφ x slot henvSlot

/-- `Coherent` is preserved by a lifetime drop: a borrow typed in the dropped
environment also types in the original (`of_dropLifetime`), where `Coherent env`
gives its targets a joint typing, which then transports back across the drop
(`dropLifetime_child_of_wellFormedTargets`).  The targets are well formed at
`parent` because the surviving borrow's base outlives `parent`. -/
theorem Coherent.dropLifetime_child {env : Env} {parent child : Lifetime}
    (hchild : LifetimeChild parent child) (hwellBody : WellFormedEnv env child)
    (hcohEnv : Coherent env) : Coherent (env.dropLifetime child) := by
  intro lv m T bLf hty
  have htyEnv := LValTyping.of_dropLifetime hty
  rcases hcohEnv lv m T bLf htyEnv with ⟨ty, lt, htgtsEnv⟩
  rcases LValTyping.base_slot_exists hty with ⟨dslot, hdslot⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hdslot with ⟨henvBase, hneChild⟩
  have hbaseParent : LValBaseOutlives env lv parent := by
    rcases LValTyping.base_outlives_one hwellBody htyEnv with ⟨bslot, hbslot, hble⟩
    have hEq : dslot = bslot := Option.some.inj (henvBase.symm.trans hbslot)
    exact ⟨bslot, hbslot,
      LifetimeChild.parent_of_outlives_child_ne hchild hble (hEq ▸ hneChild)⟩
  have hbLfParent : bLf ≤ parent :=
    LValTyping.lifetime_outlives_of_base_outlives_one hwellBody.1 htyEnv hbaseParent
  have hwellT : BorrowTargetsWellFormed env T parent :=
    BorrowTargetsWellFormed.weaken
      (LValTyping.containedBorrowTargetsWellFormed_at_lifetime hwellBody.1 htyEnv
        PartialTyContains.here)
      hbLfParent
  have hltParent : lt ≤ parent :=
    (LValTyping.lifetime_outlives_of_base_outlives hwellBody.1).2 htgtsEnv (by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellT target htarget with
        ⟨_, _, _, _, hb⟩
      exact hb)
  exact ⟨ty, lt, LValTargetsTyping.dropLifetime_child_of_wellFormedTargets
    hchild hwellBody hwellT htgtsEnv hltParent⟩

/--
Block drop preservation for well-formed environments, used in the `T-Block`
case of Lemma 4.9.

This is the environment side of Appendix Lemma 9.5 together with the
`Γ₂ ⊢ T ≽ l` premise from `T-Block`: dropping the block lifetime removes locals
without invalidating the result type at the enclosing lifetime.
-/
theorem Env.dropLifetime_preserves_wellFormed_child {env env' : Env}
    {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    WellFormedTy env ty parent →
    env' = env.dropLifetime child →
    WellFormedEnv env' parent ∧ WellFormedTy env' ty parent := by
  intro hchild hwellBody hwellTy hdrop
  subst hdrop
  have htransport : DropFullLValTypingTransport env parent child := by
    intro lv targetTy targetLifetime hbase htyping houtlives
    exact LValTyping.dropLifetime_child_of_base_outlives
      hchild hwellBody hbase htyping houtlives
  refine ⟨
    ⟨ContainedBorrowsWellFormed.dropLifetime_child_of_transport
        hchild hwellBody htransport,
      EnvSlotsOutlive.dropLifetime_child hchild hwellBody.2.1,
      Coherent.dropLifetime_child hchild hwellBody hwellBody.2.2.1,
      Linearizable.dropLifetime_child hwellBody.2.2.2⟩,
    WellFormedTy.dropLifetime_child_of_transport hchild htransport hwellTy⟩

theorem block_preserves_wellFormed {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₂ blockLifetime →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnv env₃ lifetime ∧ WellFormedTy env₃ ty lifetime := by
  intro hchild hwellBody _hterms hwellTy hdrop
  exact Env.dropLifetime_preserves_wellFormed_child hchild hwellBody hwellTy hdrop

theorem declare_preserves_wellFormed_of_output_fresh {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name}
    {term : Term} {ty : Ty} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    FreshUpdateCoherenceObligations env₂ x ty lifetime →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    WellFormedEnv env₃ lifetime := by
  intro hwellFormed hwellTy hfresh _hterm hcoh henv₃
  exact declare_preserves_wellFormed_output_fresh hwellFormed hwellTy hfresh hcoh henv₃

/--
Constructor landmarks for Lemma 4.9.

The term-typing induction is small once the update-sensitive constructors are
named at their paper granularity.  The final Lemma 4.9 route below uses the
rule-carried obligation induction instead of manufacturing this legacy landmark
package from broad write-preservation claims.
-/
structure TypingPreservesWellFormedObligations : Prop where
  block_preserves_wellFormed
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₂ blockLifetime →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnv env₃ lifetime ∧ WellFormedTy env₃ ty lifetime
  copy_result_wellFormed
    {env : Env} {lv : LVal} {ty : Ty}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    CopyTy ty →
    WellFormedTy env ty lifetime
  move_preserves_wellFormed
    {env env' : Env} {lv : LVal} {ty : Ty}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedEnv env' lifetime ∧ WellFormedTy env' ty lifetime
  assign_preserves_wellFormed
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime

/--
Lemma 4.9 induction, parameterized by the appendix landmarks.

This is the proof we want to keep clean: each typing constructor is handled
once, while the reusable update/move/copy facts are proved separately.
-/
theorem typingPreservesWellFormed_of_landmarks
    (hlandmarks : TypingPreservesWellFormedObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        hlandmarks.copy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      hlandmarks.move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      hlandmarks.block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcoh henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcoh)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellRhs hwrite _hranked _hwriteCoh hnotWrite ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨hlandmarks.assign_preserves_wellFormed hwellFormed result.1 hLhs
          (LValTyping.lifetime_outlives_one hwellFormed hLhs)
          hRhs hshape hwellRhs hwrite hnotWrite,
        WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
      (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
          _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
        let headResult := ihHead htypingEq hwellFormed
        ihRest htypingEq headResult.1)
      htyping rfl hwellFormed

/-- Assignment-level rank side condition for the well-formedness induction.

This packages the rule obligation that `T-Assign` currently does not carry:
after typing the RHS and performing the write, there must be a pre-write
linearization witness such that every newly installed RHS borrow edge is ranked
downward in the result. -/
def AssignmentRhsEdgesRanked : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy

/-- Declaration-level fresh-slot coherence side condition for Lemma 4.9.

The legacy declaration case used `Coherent.update_fresh_ty`, which is false from
`WellFormedTy` alone.  This side condition states the missing local fact for each
`T-Declare`: adding the freshly declared full type must satisfy the explicit
fresh-update coherence obligations.
-/
def DeclarationFreshUpdateCoherent : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {ty : Ty},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₁.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh x →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    FreshUpdateCoherenceObligations env₂ x ty lifetime

/-- Declaration-level decomposition for borrow-free declared types.

For a borrow-free declared/result type, the fresh-root part of
`FreshUpdateCoherenceObligations` is automatic.  The only declaration-local
coherence work left is old-root transport for borrow typings in the extended
environment.
-/
def DeclarationFreshBorrowFreeOldRootTransport : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {ty : Ty},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₁.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh x →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    TyBorrowFree ty ∧
      (∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
        {borrowLifetime : Lifetime},
        LVal.base lv ≠ x →
        LValTyping (env₂.update x { ty := .ty ty, lifetime := lifetime })
          lv (.ty (.borrow mutable targets)) borrowLifetime →
        ∃ oldBorrowLifetime,
          LValTyping env₂ lv (.ty (.borrow mutable targets)) oldBorrowLifetime)

theorem DeclarationFreshUpdateCoherent.of_borrowFreeOldRootTransport
    (hdecl : DeclarationFreshBorrowFreeOldRootTransport) :
    DeclarationFreshUpdateCoherent := by
  intro env₁ env₂ env₃ typing lifetime x term ty hwellInitial hwellResult
    hwellTy hfreshIn hterm hfreshOut henv₃
  rcases hdecl hwellInitial hwellResult hwellTy hfreshIn hterm hfreshOut henv₃ with
    ⟨hborrowFree, holdTransport⟩
  exact FreshUpdateCoherenceObligations.of_tyBorrowFree hborrowFree holdTransport

/-- Lemma 4.9 well-formedness induction using the rule-carried ranked-assignment
side condition instead of the false bare `EnvWrite.preserves_linearizedBy`.

The `AssignmentRhsEdgesRanked` parameter is kept for compatibility with older
callers; after strengthening `T-Assign`, the proof consumes the rank witness
stored directly in the assignment typing derivation. -/
theorem typingPreservesWellFormed_of_assignmentRhsEdgesRanked
    (hobligations : UpdateBorrowInvariantObligations)
    (_hrankedAssign : AssignmentRhsEdgesRanked)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed, copyTy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcoh henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcoh)
      (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
          hLhs hRhs hshape hwellRhs hwrite hranked hwriteCoh hnotWrite ih htypingEq
          hwellFormed =>
        by
          let result := ih htypingEq hwellFormed
          have htargetLifetime : _targetLifetime ≤ _lifetime :=
            LValTyping.lifetime_outlives_one hwellFormed hLhs
          rcases hranked with
            ⟨φ, hlinBy, hbelow⟩
          exact ⟨assign_preserves_wellFormed_of_rhsBorrowTargetsBelow hobligations
              hwellFormed result.1 hlinBy hbelow hwriteCoh hLhs htargetLifetime
              hRhs hshape hwellRhs hwrite hnotWrite,
            WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
      let headResult := ihHead htypingEq hwellFormed
      ihRest htypingEq headResult.1)
    htyping rfl hwellFormed

/-- Lemma 4.9 well-formedness induction using rule-carried obligations.

The assignment rank/write-coherence facts and declaration fresh-slot coherence
fact come from the strengthened `T-Assign` and `T-Declare` constructors. -/
theorem typingPreservesWellFormed_of_ruleCarriedObligations
    (hobligations : UpdateBorrowInvariantObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed, copyTy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcohObligations henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcohObligations)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellRhs hwrite hranked hwriteCoh hnotWrite ih htypingEq
        hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        have htargetLifetime : _targetLifetime ≤ _lifetime :=
          LValTyping.lifetime_outlives_one hwellFormed hLhs
        rcases hranked with
          ⟨φ, hlinBy, hbelow⟩
        have hlin3By :=
          EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
            hwrite hlinBy hbelow
        have hcoh3 := EnvWrite.preserves_coherent_of_obligations
          result.1.2.2.1 hwriteCoh
        exact ⟨⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations
              hwellFormed result.1 hLhs htargetLifetime hRhs hshape hwellRhs
              hwrite hnotWrite,
            EnvWrite.preserves_slotsOutlive result.1.2.1 hwrite,
            hcoh3,
            Linearizable.of_linearizedBy hlin3By⟩,
          WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
      let headResult := ihHead htypingEq hwellFormed
      ihRest htypingEq headResult.1)
    htyping rfl hwellFormed

/-- Compatibility wrapper for the older explicit-premise API.

The premise names are now rule-carried by `TermTyping`; callers should prefer
`typingPreservesWellFormed_of_ruleCarriedObligations`. -/
theorem typingPreservesWellFormed_of_rankedAssign_and_declFreshCoherence
    (hobligations : UpdateBorrowInvariantObligations)
    (_hrankedAssign : AssignmentRhsEdgesRanked)
    (_hwriteCoherent : AssignmentWriteCoherenceObligations)
    (_hdeclFresh : DeclarationFreshUpdateCoherent)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  exact typingPreservesWellFormed_of_ruleCarriedObligations hobligations

/--
Lemma 4.9 wrapper used by the later borrow-invariance statements.

The term-typing induction itself lives in `typingPreservesWellFormed_of_landmarks`.
This wrapper uses the strengthened typing rules: assignment rank/write coherence
and declaration fresh-slot coherence are carried by `TermTyping`, while
`UpdateBorrowInvariantObligations` supplies the remaining contained-borrow update
facts.
-/
theorem typingPreservesWellFormed_of_storeTypingRefs
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact typingPreservesWellFormed_of_ruleCarriedObligations hobligations
    hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping

theorem typingPreservesWellFormed_emptyStoreTyping
    {store : ProgramStore} {env₁ env₂ : Env}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    UpdateBorrowInvariantObligations →
    ValidState store term →
    ValidStoreTyping store term StoreTyping.empty →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hobligations hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact typingPreservesWellFormed_of_storeTypingRefs
    hobligations
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    hvalidState hvalidStoreTyping hwellFormed hsafe htyping

theorem borrowInvariance_emptyStoreTyping {store : ProgramStore}
    {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    ValidState store term →
    ValidStoreTyping store term StoreTyping.empty →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
    hobligations
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

theorem borrowInvariance_of_storeTypingRefs {store : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
    hfresh hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
      hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/-- Source-initial borrow invariance through the rule-carried route. -/
theorem sourceInitial_borrowInvariance {term : Term} {env₂ : Env}
    {lifetime : Lifetime} {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hsource htyping hfresh hfreshCoherence
  exact borrowInvariance_emptyStoreTyping
    hobligations
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

theorem sourceInitial_typeAndBorrowSafety_of_preservation
    {term : Term} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    (∀ finalStore finalValue,
      MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₂ ty) →
    TerminatesAsValue ProgramStore.empty lifetime term →
    ProgressResult ProgramStore.empty lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping hpreservation hterminates
  exact typeAndBorrowSafety_of_preservation
    (sourceInitialRuntimeState_valid hsource)
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    wellFormedEnv_empty_all
    safeAbstraction_empty
    operationalStoreProgress_empty
    htyping
    hpreservation
    hterminates

theorem sourceInitial_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.val value) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.val value) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_multistep_value_preservation hsource htyping hmulti)
    ⟨ProgramStore.empty, value, MultiStep.refl⟩

theorem sourceInitial_blockB_value_typeAndBorrowSafety
    {value : Value} {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime
      (.block blockLifetime [.val value]) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.block blockLifetime [.val value]) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime
          (.block blockLifetime [.val value]) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.block blockLifetime [.val value]) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  rcases drops_empty_lifetime blockLifetime with ⟨storeAfterDrop, hdrops⟩
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_blockB_value_multistep_preservation hsource htyping hmulti)
    ⟨storeAfterDrop, value,
      MultiStep.trans (Step.blockB (lifetime := lifetime) hdrops) MultiStep.refl⟩

theorem sourceInitial_box_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    ProgressResult ProgramStore.empty lifetime (.box (.val value)) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ (.box ty) := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.box (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  let boxed := ProgramStore.empty.boxAt 0 value
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_box_value_multistep_preservation hsource htyping hmulti)
    ⟨boxed.1, .ref boxed.2,
      MultiStep.trans
        (Step.box (address := 0) (ref := boxed.2)
          (by simp [ProgramStore.fresh, ProgramStore.empty])
          (by simp [boxed]))
        MultiStep.refl⟩

theorem sourceInitial_declare_value_typeAndBorrowSafety
    {x : Name} {value : Value} {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    ProgressResult ProgramStore.empty lifetime (.letMut x (.val value)) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.letMut x (.val value)) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₃ .unit := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.letMut x (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_declare_value_multistep_preservation hsource htyping hmulti)
    ⟨ProgramStore.empty.declare x lifetime value, .unit,
      MultiStep.trans (Step.declare (lifetime := lifetime) rfl) MultiStep.refl⟩

theorem preservation_value_case {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
  exact preservation_multistep_runtime_value hvalidRuntime hvalidStoreTyping
    hsafe htyping hmulti

theorem preservation_box_value_case {store finalStore : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    ValidStoreTyping store (.box (.val value)) typing →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.box (.val value)) →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    MultiStep store lifetime (.box (.val value)) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ (.box ty) := by
  intro hvalidStoreTyping hsafe hvalidRuntime htyping hmulti
  exact preservation_box_multistep_runtime hvalidStoreTyping hsafe hvalidRuntime
    htyping hmulti

theorem preservation_declare_value_case {store finalStore : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {value finalValue : Value} :
    ValidStoreTyping store (.letMut x (.val value)) typing →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.letMut x (.val value)) →
    TermTyping env₁ typing lifetime (.letMut x (.val value)) .unit env₃ →
    MultiStep store lifetime (.letMut x (.val value)) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₃ .unit := by
  intro hvalidStoreTyping hsafe hvalidRuntime htyping hmulti
  exact preservation_declare_multistep_runtime hvalidStoreTyping hsafe hvalidRuntime
    htyping hmulti

theorem preservation_blockB_value_no_slots_case {store finalStore : ProgramStore}
    {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    store ∼ₛ env →
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ blockLifetime) →
    ValidValue store value ty →
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env' ty := by
  intro hvalidRuntime hsafe htyping hnoSlots hvalidValue hmulti
  exact preservation_blockB_value_multistep_runtime_no_slots hvalidRuntime hsafe
    htyping hnoSlots hvalidValue hmulti

theorem typingPreservesBorrowSafeResult_mutBorrow_case {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow true lv) (.borrow true [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) := by
  intro hborrowSafe htyping hfresh
  exact borrowSafety_mutBorrow_result_extension hborrowSafe htyping hfresh

theorem typingPreservesBorrowSafeResult_immBorrow_case {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow false lv) (.borrow false [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) := by
  intro hborrowSafe htyping hfresh
  exact borrowSafety_immBorrow_result_extension hborrowSafe htyping hfresh

theorem typingPreservesBorrowSafeResult_copy_case {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {ty : Ty}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hborrowSafe htyping hfresh
  cases htyping with
  | copy hLv hcopy _hnotRead =>
      cases hcopy with
      | int =>
          exact borrowSafeEnv_update_fresh_borrowFree hborrowSafe tyBorrowFree_int
      | immBorrow =>
          rename_i targets
          exact borrowSafeEnv_update_fresh_immBorrowMany hborrowSafe hfresh
            (by
              intro target htarget
              exact (LValTyping.no_readProhibited_targets_of_immBorrow hborrowSafe).1
                hLv PartialTyContains.here target htarget)

theorem typingPreservesBorrowSafeResult_box_case {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty}
    {gamma : Name} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) →
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro _hwellFormed _hwellTy hinnerSafe _htyping _hfresh
  exact borrowSafeEnv_update_box_of_update_inner hinnerSafe

theorem typingPreservesBorrowSafeResult_unit_case {env₂ : Env}
    {lifetime : Lifetime} {gamma : Name} :
    WellFormedEnv env₂ lifetime →
    BorrowSafeEnv env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty .unit, lifetime := lifetime }) := by
  intro _hwellFormed hborrowSafe _hfresh
  exact borrowSafeEnv_update_fresh_borrowFree hborrowSafe tyBorrowFree_unit

/--
Constructor-level borrow-safety landmarks used by the source-scoped Corollary
4.14 route.

Result-extension for `T-Const` is only proved for source values; arbitrary
runtime references need an evaluation/reachability invariant, not a local typing
fact.  The copy, move, mut/imm borrow, box, and declaration shells are proved
directly from the conflict definitions and induction hypotheses.  The assignment
field consumes the full RHS induction result: `BorrowSafeEnv env₂` plus the fact
that the RHS type can be safely exposed as a fresh root.  Block bodies are
handled by the mutual term/list induction below: the induction carries the
root-independent `TyBorrowSafeAgainstEnv` invariant through `dropLifetime`, so
there is no separate block-list obligation here.
-/
structure BorrowSafetyPreservationObligations : Prop where
  envWrite {env₁ env₂ env₃ : Env}
      {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
      {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
      BorrowSafeEnv env₂ →
      (∀ gamma,
        env₂.fresh gamma →
        BorrowSafeEnv (env₂.update gamma { ty := .ty rhsTy, lifetime := lifetime })) →
      LValTyping env₁ lhs oldTy targetLifetime →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      ShapeCompatible env₂ oldTy (.ty rhsTy) →
      WellFormedTy env₂ rhsTy targetLifetime →
      EnvWrite 0 env₂ lhs rhsTy env₃ →
      (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
      EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
      ¬ WriteProhibited env₃ lhs →
      BorrowSafeEnv env₃

/-- Move borrow-safety preservation, including result-extension.

The proof uses `LValTyping.contains_base_of_strike`: since `EnvMove` follows a
`Strike` path, every borrow contained in the moved result type originated in the
moved base slot.  Once that origin fact is known,
`borrowSafeEnv_move_result_extension_of_base_contains` discharges the fresh
result root.
-/
theorem borrowSafetyPreservation_move
    {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {ty : Ty} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    (∀ x, lv ≠ .var x) →
    ¬ TyBorrowFree ty →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hborrowSafe htyping _hnotVar _hnotBorrowFree hfresh
  cases htyping with
  | move hLv _hnotWrite hmove =>
      rcases hmove with ⟨slot, struck, hslot, hstrike, henv₂⟩
      subst henv₂
      exact borrowSafeEnv_move_result_extension_of_base_contains
        hborrowSafe
        ⟨slot, struck, hslot, hstrike, rfl⟩
        (by
          intro mutable targets hcontains
          exact LValTyping.contains_base_of_strike hLv hslot hstrike hcontains)
        hfresh

/-- Remaining explicit `EnvWrite` borrow-safety frame obligation.

The global term-typing induction supplies both `BorrowSafeEnv env₂` and the RHS
result-extension invariant.  The latter is part of the real assignment argument:
`BorrowSafeEnv env₂` alone does not say that borrow targets contained in `rhsTy`
are safe to expose as a root.
-/
theorem borrowSafetyPreservation_envWrite
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    BorrowSafeEnv env₂ →
    (∀ gamma,
      env₂.fresh gamma →
      BorrowSafeEnv (env₂.update gamma { ty := .ty rhsTy, lifetime := lifetime })) →
    LValTyping env₁ lhs oldTy targetLifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    ¬ WriteProhibited env₃ lhs →
    BorrowSafeEnv env₃ := by
  sorry

/-- Concrete borrow-safety package assembled from the explicit sorried lemmas. -/
theorem borrowSafetyPreservationObligations_from_sorries :
    BorrowSafetyPreservationObligations where
  envWrite := borrowSafetyPreservation_envWrite

theorem typingPreservesWellFormed_of_updateBorrowInvariant
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact typingPreservesWellFormed_of_storeTypingRefs hobligations hrefs hvalidState
    hvalidStoreTyping hwellFormed hsafe htyping

/-- Lemma 4.9 core statement: typing preserves environment well-formedness.

The remaining update-specific invariant work is explicit in
`UpdateBorrowInvariantObligations`; assignment rank/write-coherence and
declaration fresh-slot coherence are carried by the typing derivation itself. -/
theorem typingPreservesWellFormed {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact typingPreservesWellFormed_of_ruleCarriedObligations
    hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping

/--
Constructor-level runtime preservation landmarks used by Lemma 4.11.

The value, copy, borrow, box, and declaration cases are discharged by existing
multistep fragments.  The fields isolate the cases still requiring the paper's
general move/update/drop preservation arguments.
-/
structure RuntimePreservationObligations : Prop where
  move {store finalStore : ProgramStore} {env₁ env₂ : Env}
      {typing : StoreTyping} {lifetime : Lifetime}
      {lv : LVal} {ty : Ty} {finalValue : Value} :
      ValidRuntimeState store (.move lv) →
      ValidStoreTyping store (.move lv) typing →
      WellFormedEnv env₁ lifetime →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime (.move lv) ty env₂ →
      MultiStep store lifetime (.move lv) finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₂ ty
  assign {midStore finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
      {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
      {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
      {value finalValue : Value} :
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
      TerminalStateSafe finalStore finalValue env₃ .unit
  block {store finalStore : ProgramStore} {env₁ env₃ : Env}
      {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
      {terms : List Term} {ty : Ty} {finalValue : Value} :
      ValidRuntimeState store (.block blockLifetime terms) →
      ValidStoreTyping store (.block blockLifetime terms) typing →
      WellFormedEnv env₁ lifetime →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime (.block blockLifetime terms) ty env₃ →
      MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₃ ty

/-- Remaining explicit runtime preservation obligation for moves. -/
theorem runtimePreservation_move
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {ty : Ty} {finalValue : Value} :
    ValidRuntimeState store (.move lv) →
    ValidStoreTyping store (.move lv) typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.move lv) ty env₂ →
    MultiStep store lifetime (.move lv) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  sorry

/-- Remaining explicit runtime preservation obligation for assignment redexes.

The global Preservation induction handles RHS evaluation and passes the resulting
valid runtime state, safe abstraction, and value abstraction into this local
redex/update obligation.  This is not a pure typing obligation: the redex proof
must establish post-step runtime validity and `finalStore ∼ₛ env₃` after the
drop/write sequence, then package them with
`terminalStateSafe_assign_unit_of_postconditions`.
-/
theorem runtimePreservation_assign
    {midStore finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {value finalValue : Value} :
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
    TerminalStateSafe finalStore finalValue env₃ .unit := by
  sorry

/-- Remaining explicit runtime preservation obligation for blocks. -/
theorem runtimePreservation_block
    {store finalStore : ProgramStore} {env₁ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} {finalValue : Value} :
    ValidRuntimeState store (.block blockLifetime terms) →
    ValidStoreTyping store (.block blockLifetime terms) typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.block blockLifetime terms) ty env₃ →
    MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₃ ty := by
  sorry

/-- Concrete runtime-preservation package assembled from explicit sorried lemmas. -/
theorem runtimePreservationObligations_from_sorries :
    RuntimePreservationObligations where
  move := runtimePreservation_move
  assign := runtimePreservation_assign
  block := runtimePreservation_block

/--
Lemma 4.9, Borrow Invariance.

The paper phrases the conclusion as well-formedness of the output environment
extended with a fresh result binding `γ ↦ <T>^l`.

The final result binding must satisfy `FreshUpdateCoherenceObligations`; the
bare implication from `WellFormedTy` is false for borrow types such as `&[]`.
-/
theorem borrowInvariance {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
    hfresh hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
      hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/--
Borrow invariance through the ranked-assignment typing-preservation route.

This is the non-vacuous replacement for the old route through the bare
`EnvWrite.preserves_linearizedBy` axiom: assignment must supply the local
`AssignmentRhsEdgesRanked` obligation saying newly installed RHS borrow edges
are ranked downward in a pre-write linearization.
-/
theorem borrowInvariance_of_assignmentRhsEdgesRanked
    (hobligations : UpdateBorrowInvariantObligations)
    (hrankedAssign : AssignmentRhsEdgesRanked)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_assignmentRhsEdgesRanked
      hobligations hrankedAssign hrefs hvalidState hvalidStoreTyping hwellFormed
      hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension hwellFormedOutput hwellFormedTy hfresh
    hfreshCoherence

/--
Borrow invariance through the ranked-assignment route and the explicit
fresh-result coherence obligation.

Compared with `borrowInvariance_of_assignmentRhsEdgesRanked`, this removes the
dependency on the legacy `Coherent.update_fresh_ty` axiom.  The remaining
coherence work is split into:
* assignment/write coherence, carried by `hobligations`;
* fresh result-slot coherence, carried by `hfreshCoherence`.
-/
theorem borrowInvariance_of_assignmentRhsEdgesRanked_and_freshCoherence
    (hobligations : UpdateBorrowInvariantObligations)
    (hrankedAssign : AssignmentRhsEdgesRanked)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_assignmentRhsEdgesRanked
      hobligations hrankedAssign hrefs hvalidState hvalidStoreTyping hwellFormed
      hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/--
Borrow invariance through the rule-carried obligation route.

Assignment rank/write-coherence and declaration fresh-slot coherence are part of
the strengthened typing derivation.  The only remaining fresh-coherence premise
is for the final result binding `gamma`, which is added after the term has been
typed.
-/
theorem borrowInvariance_of_ruleCarriedObligations
    (hobligations : UpdateBorrowInvariantObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
      hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/--
Borrow invariance through the fully explicit ranked/fresh-coherence route.

This version avoids both legacy false/too-weak axioms already isolated in this
file: bare write linearization and fresh-type coherence from `WellFormedTy`
alone.  This is now a compatibility wrapper around
`borrowInvariance_of_ruleCarriedObligations`; the assignment/declaration
side-condition parameters are supplied by the typing derivation itself.
-/
theorem borrowInvariance_of_rankedAssign_and_declFreshCoherence
    (hobligations : UpdateBorrowInvariantObligations)
    (_hrankedAssign : AssignmentRhsEdgesRanked)
    (_hwriteCoherent : AssignmentWriteCoherenceObligations)
    (_hdeclFresh : DeclarationFreshUpdateCoherent)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  exact borrowInvariance_of_ruleCarriedObligations
    hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
    hfresh hfreshCoherence

/--
Source-initial borrow invariance through the explicit ranked/fresh-coherence
route.

This is the source-program version of
`borrowInvariance_of_rankedAssign_and_declFreshCoherence`: it avoids the legacy
bare write-linearization and fresh-type coherence axioms by making the missing
rank/coherence premises explicit.
-/
theorem sourceInitial_borrowInvariance_of_rankedAssign_and_declFreshCoherence
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    AssignmentRhsEdgesRanked →
    AssignmentWriteCoherenceObligations →
    DeclarationFreshUpdateCoherent →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hupdate hranked hwriteCoherent hdeclFresh hsource htyping hfresh
    hfreshCoherence
  exact borrowInvariance_of_rankedAssign_and_declFreshCoherence
    hupdate
    hranked
    hwriteCoherent
    hdeclFresh
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

/-- Source-initial borrow invariance through the rule-carried obligation route. -/
theorem sourceInitial_borrowInvariance_of_ruleCarriedObligations
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hupdate hsource htyping hfresh hfreshCoherence
  exact borrowInvariance_of_ruleCarriedObligations
    hupdate
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

/--
Lemma 4.11, Preservation.

This is stated over `ValidRuntimeState`, the mechanised package that contains
Definition 4.3's valid-state condition plus the explicit owner-allocation
invariant needed by our concrete store model.
-/
theorem preservation {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    RuntimePreservationObligations →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hobligations hvalidRuntime hvalidStoreTyping hwellFormed hsafe htyping hmulti
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      ∀ (store finalStore : ProgramStore) (finalValue : Value),
        ValidRuntimeState store term →
        ValidStoreTyping store term typing →
        WellFormedEnv env lifetime →
        store ∼ₛ env →
        MultiStep store lifetime term finalStore (.val finalValue) →
        TerminalStateSafe finalStore finalValue env₂ ty)
    (motive_2 := fun _env _typing _lifetime _terms _ty _env₂ _ => True)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping
        store finalStore finalValue hvalidRuntime hvalidStoreTyping _hwellFormed hsafe
        hmulti =>
      preservation_multistep_runtime_value hvalidRuntime hvalidStoreTyping hsafe
        (TermTyping.const hvalueTyping) hmulti)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy hnotRead
        store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        hmulti =>
      preservation_copy_multistep_runtime hwellFormed hsafe hvalidRuntime
        (TermTyping.copy (typing := _typing) hLv hcopy hnotRead) hmulti)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
        hLv hnotWrite hmove store finalStore finalValue hvalidRuntime hvalidStoreTyping
        hwellFormed hsafe hmulti =>
      hobligations.move hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        (TermTyping.move hLv hnotWrite hmove) hmulti)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hmutable hnotWrite
        store finalStore finalValue hvalidRuntime _hvalidStoreTyping _hwellFormed hsafe
        hmulti =>
      preservation_borrow_multistep_runtime hsafe hvalidRuntime
        (TermTyping.mutBorrow (typing := _typing) hLv hmutable hnotWrite) hmulti)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hnotRead
        store finalStore finalValue hvalidRuntime _hvalidStoreTyping _hwellFormed hsafe
        hmulti =>
      preservation_borrow_multistep_runtime hsafe hvalidRuntime
        (TermTyping.immBorrow (typing := _typing) hLv hnotRead) hmulti)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih
        store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed hsafe hmulti =>
      preservation_box_context_terminal_multistep_runtime
        (by
          intro midStore value hvalidInner hvalidStoreTypingInner hsafeInner
            _hinnerTyping hmultiInner
          exact ih store midStore value hvalidInner hvalidStoreTypingInner
            hwellFormed hsafeInner hmultiInner)
        hvalidRuntime hvalidStoreTyping hsafe (TermTyping.box hterm) hmulti)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop _ih store finalStore finalValue hvalidRuntime
        hvalidStoreTyping hwellFormed hsafe hmulti =>
      hobligations.block hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        (TermTyping.block hblockChild hterms hwellTy hdrop) hmulti)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfresh hterm hfreshOut _hcoh henv₃ ih
        store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        hmulti =>
      by
        rcases multistep_declare_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hdeclareStep⟩
        rcases ih store midStore value
            (validRuntimeState_declare_inner hvalidRuntime)
            (validStoreTyping_declare_inner hvalidStoreTyping)
            hwellFormed hsafe hinnerMulti with
          ⟨hvalidInner, hsafeInner, hvalidValue⟩
        cases hdeclareStep with
        | declare hstore =>
            have hpreserved :=
              preservation_declare_redex_runtime_of_validValue hsafeInner
                hfreshOut
                (validRuntimeState_declare_value_of_value hvalidInner)
                hvalidValue
                (Step.declare (lifetime := _lifetime) hstore)
            rw [henv₃]
            exact hpreserved)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellTy hwrite hranked hcoh hnotWrite _ih store finalStore finalValue
        hvalidRuntime hvalidStoreTyping hwellFormed hsafe hmulti =>
      by
        rcases multistep_assign_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hassignStep⟩
        rcases _ih store midStore value
            (validRuntimeState_assign_inner hvalidRuntime)
            (validStoreTyping_assign_inner hvalidStoreTyping)
            hwellFormed hsafe hinnerMulti with
          ⟨hvalidInner, hsafeInner, hvalidValue⟩
        exact hobligations.assign hLhs hRhs hshape hwellTy hwrite hnotWrite
          (validRuntimeState_assign_value_of_value hvalidInner)
          hsafeInner hvalidValue hassignStep)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm _ih => trivial)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest _ihHead _ihRest => trivial)
    htyping store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
    hsafe hmulti

/--
Theorem 4.12, Type and Borrow Safety.

The paper assumes termination; here that assumption is represented by an
explicit multistep witness to a final runtime value.
-/
theorem typeAndBorrowSafety {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    RuntimePreservationObligations →
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
  intro hobligations hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress
    htyping hterminates
  exact typeAndBorrowSafety_of_preservation hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hstoreProgress htyping
    (by
      intro finalStore finalValue hmulti
      exact preservation hobligations hvalidRuntime hvalidStoreTyping
        (hwellFormed lifetime) hsafe htyping hmulti)
    hterminates

/--
Main borrow-safety induction behind Corollary 4.14.

The result binding is included in the statement because the paper's corollary
checks borrow-safety after extending the output environment with `γ ↦ <T>^l`.
-/
theorem typingPreservesBorrowSafeResult_global {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    BorrowSafeEnv env₂ ∧
      TyBorrowSafeAgainstEnv env₂ ty ∧
      ∀ gamma,
        env₂.fresh gamma →
        BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hobligations hsource hborrowSafe htyping
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      SourceTerm term →
        BorrowSafeEnv env →
        BorrowSafeEnv env₂ ∧
          TyBorrowSafeAgainstEnv env₂ ty ∧
          ∀ gamma,
            env₂.fresh gamma →
            BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }))
    (motive_2 := fun env _typing lifetime terms _ty env₂ _ =>
      SourceTerm (.block lifetime terms) →
        BorrowSafeEnv env →
        BorrowSafeEnv env₂ ∧
          TyBorrowSafeAgainstEnv env₂ _ty)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping hsource hborrowSafe =>
      by
        have hborrowFree : TyBorrowFree _ty :=
          sourceValue_valueTyping_borrowFree
            (hsource _value (by simp [termValues])) hvalueTyping
        refine ⟨hborrowSafe, tyBorrowSafeAgainstEnv_borrowFree hborrowFree, ?_⟩
        intro gamma hfresh
        exact borrowSafe_value_result_extension_borrowFree
          (TermTyping.const hvalueTyping) hborrowSafe
          hborrowFree
          hfresh)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy hnotRead
        _hsource hborrowSafe =>
      ⟨hborrowSafe,
        (by
          cases hcopy with
          | int =>
              exact tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_int
          | immBorrow =>
              rename_i targets
              exact tyBorrowSafeAgainstEnv_immBorrowMany
                (by
                  intro target htarget
                  exact (LValTyping.no_readProhibited_targets_of_immBorrow hborrowSafe).1
                    hLv PartialTyContains.here target htarget)),
        fun gamma hfresh =>
        typingPreservesBorrowSafeResult_copy_case hborrowSafe
          (TermTyping.copy (typing := _typing) hLv hcopy hnotRead) hfresh⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
        hLv hnotWrite hmove _hsource hborrowSafe =>
      by
        have hcore : BorrowSafeEnv _env₂ :=
          borrowSafeEnv_move hborrowSafe hmove
        have hsafeTy : TyBorrowSafeAgainstEnv _env₂ _ty := by
          rcases hmove with ⟨slot, struck, hslot, hstrike, henv₂⟩
          subst henv₂
          exact tyBorrowSafeAgainstEnv_move_of_base_contains
            hborrowSafe
            ⟨slot, struck, hslot, hstrike, rfl⟩
            (by
              intro mutable targets hcontains
              exact LValTyping.contains_base_of_strike hLv hslot hstrike hcontains)
        refine ⟨hcore, hsafeTy, ?_⟩
        intro gamma hfresh
        cases _lv with
        | var x =>
            exact borrowSafety_move_var_result_extension hborrowSafe
              (TermTyping.move (typing := _typing) hLv hnotWrite hmove) hfresh
        | deref lv =>
            by_cases hborrowFree : TyBorrowFree _ty
            · exact borrowSafety_move_borrowFree_result_extension
                (typing := _typing) hborrowSafe
                (TermTyping.move (typing := _typing) hLv hnotWrite hmove)
                hborrowFree
            · exact borrowSafetyPreservation_move (typing := _typing) hborrowSafe
                (TermTyping.move (typing := _typing) hLv hnotWrite hmove)
                (by
                  intro x hvar
                  cases hvar)
                hborrowFree
                hfresh)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hmutable hnotWrite
        _hsource hborrowSafe =>
      ⟨hborrowSafe,
        tyBorrowSafeAgainstEnv_mutBorrow hnotWrite,
        fun gamma hfresh =>
        typingPreservesBorrowSafeResult_mutBorrow_case hborrowSafe
          (TermTyping.mutBorrow (typing := _typing) hLv hmutable hnotWrite) hfresh⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hnotRead
        _hsource hborrowSafe =>
      ⟨hborrowSafe,
        tyBorrowSafeAgainstEnv_immBorrow hnotRead,
        fun gamma hfresh =>
        typingPreservesBorrowSafeResult_immBorrow_case hborrowSafe
          (TermTyping.immBorrow (typing := _typing) hLv hnotRead) hfresh⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih hsource hborrowSafe =>
      by
        have hinner := ih (SourceTerm.box_inner hsource) hborrowSafe
        exact ⟨hinner.1, TyBorrowSafeAgainstEnv.box hinner.2.1, by
          intro gamma hfresh
          exact borrowSafeEnv_update_box_of_update_inner (hinner.2.2 gamma hfresh)⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop _ih hsource hborrowSafe =>
      by
        have hbody := _ih hsource hborrowSafe
        have hbodySafe : BorrowSafeEnv _env₂ :=
          hbody.1
        have hbodyTySafe : TyBorrowSafeAgainstEnv _env₂ _ty :=
          hbody.2
        have hblockTySafe : TyBorrowSafeAgainstEnv _env₃ _ty := by
          rw [hdrop]
          exact TyBorrowSafeAgainstEnv.dropLifetime hbodyTySafe
        have hblockCore :
            BorrowSafeEnv _env₃ :=
          borrowSafety_block_drop hbodySafe hdrop
        refine ⟨hblockCore, hblockTySafe, ?_⟩
        intro gamma _hfresh
        exact borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv hblockCore hblockTySafe)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfreshX hterm hfreshOut _hcoh henv₃ _ih
        hsource hborrowSafe =>
      by
        have hinner := _ih (SourceTerm.declare_inner hsource) hborrowSafe
        have hdeclaredSafe :
            BorrowSafeEnv
              (_env₂.update _x { ty := .ty _ty, lifetime := _lifetime }) := by
          exact hinner.2.2 _x hfreshOut
        rw [henv₃]
        exact ⟨hdeclaredSafe,
          tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit,
          fun gamma _hfreshGamma =>
            borrowSafeEnv_update_fresh_borrowFree hdeclaredSafe tyBorrowFree_unit⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellTy hwrite hranked hcoh hnotWrite _ih hsource hborrowSafe =>
      by
        have hRhsSafe := _ih (SourceTerm.assign_inner hsource) hborrowSafe
        have hwriteSafe :
            BorrowSafeEnv _env₃ :=
          hobligations.envWrite hRhsSafe.1 hRhsSafe.2.2 hLhs hRhs hshape hwellTy
            hwrite hranked hcoh hnotWrite
        exact ⟨hwriteSafe,
          tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit,
          fun _gamma _hfresh =>
          borrowSafeEnv_update_fresh_borrowFree hwriteSafe tyBorrowFree_unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm _ih hsource hborrowSafe =>
      let h := _ih (SourceTerm.block_head hsource) hborrowSafe
      ⟨h.1, h.2.1⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest _ihHead _ihRest hsource hborrowSafe =>
      by
        have hhead := _ihHead (SourceTerm.block_head hsource) hborrowSafe
        exact _ihRest (SourceTerm.block_tail hsource) hhead.1)
    htyping hsource hborrowSafe

theorem typingPreservesBorrowSafeResult {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hobligations hsource hborrowSafe htyping hfresh
  exact (typingPreservesBorrowSafeResult_global hobligations hsource
    hborrowSafe htyping).2 gamma hfresh

/--
Corollary 4.14, Borrow Safety.

Starting from a borrow-safe environment, the output environment extended with
the fresh result binding is both well-formed and borrow-safe.

The well-formedness half uses `borrowInvariance`, so the final result binding
coherence premise is explicit here as well.
-/
theorem borrowSafety {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hsource hrefs hvalidState hvalidStoreTyping
    hwellFormed hborrowSafe hsafe htyping hfresh hfreshCoherence
  exact ⟨
    borrowInvariance hupdateObligations hrefs hvalidState hvalidStoreTyping
      hwellFormed hsafe htyping hfresh hfreshCoherence,
      typingPreservesBorrowSafeResult hborrowObligations hsource
        hborrowSafe htyping hfresh⟩

/--
Borrow Safety through the explicit, non-axiomatic borrow-invariance route.

The borrow-safe preservation half is unchanged; the well-formedness half uses
`borrowInvariance_of_rankedAssign_and_declFreshCoherence`, so the remaining
coherence/rank obligations are explicit premises rather than hidden axioms.
-/
theorem borrowSafety_of_rankedAssign_and_declFreshCoherence
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    AssignmentRhsEdgesRanked →
    AssignmentWriteCoherenceObligations →
    DeclarationFreshUpdateCoherent →
    SourceTerm term →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hrankedAssign hwriteCoherent
    hdeclFresh hsource hrefs hvalidState hvalidStoreTyping hwellFormed hborrowSafe hsafe
    htyping hfresh hfreshCoherence
  exact ⟨
    borrowInvariance_of_rankedAssign_and_declFreshCoherence
      hupdateObligations hrankedAssign hwriteCoherent hdeclFresh hrefs hvalidState
      hvalidStoreTyping hwellFormed hsafe htyping hfresh hfreshCoherence,
    typingPreservesBorrowSafeResult hborrowObligations hsource
      hborrowSafe htyping hfresh⟩

/--
Borrow safety through the rule-carried borrow-invariance route.

The well-formedness half avoids the legacy write/fresh axioms and does not
require global assignment/declaration side predicates; those facts are attached
to the typing derivation.
-/
theorem borrowSafety_of_ruleCarriedObligations
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hsource hrefs hvalidState hvalidStoreTyping
    hwellFormed hborrowSafe hsafe htyping hfresh hfreshCoherence
  exact ⟨
    borrowInvariance_of_ruleCarriedObligations
      hupdateObligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe
      htyping hfresh hfreshCoherence,
    typingPreservesBorrowSafeResult hborrowObligations hsource
      hborrowSafe htyping hfresh⟩

/--
Source-initial Borrow Safety through the explicit, non-axiomatic
borrow-invariance route.

This is the source-program counterpart of
`borrowSafety_of_rankedAssign_and_declFreshCoherence`: the empty initial store,
environment, and store typing discharge the standard source-state premises, while
the rank/coherence obligations remain explicit instead of hidden behind legacy
axioms.
-/
theorem sourceInitial_borrowSafety_of_rankedAssign_and_declFreshCoherence
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    AssignmentRhsEdgesRanked →
    AssignmentWriteCoherenceObligations →
    DeclarationFreshUpdateCoherent →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hrankedAssign hwriteCoherent
    hdeclFresh hsource htyping hfresh hfreshCoherence
  exact borrowSafety_of_rankedAssign_and_declFreshCoherence
    hupdateObligations
    hborrowObligations
    hrankedAssign
    hwriteCoherent
    hdeclFresh
    hsource
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    borrowSafeEnv_empty
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

/-- Source-initial borrow safety through the rule-carried obligation route. -/
theorem sourceInitial_borrowSafety_of_ruleCarriedObligations
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hsource htyping hfresh hfreshCoherence
  exact borrowSafety_of_ruleCarriedObligations
    hupdateObligations
    hborrowObligations
    hsource
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    borrowSafeEnv_empty
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

end Paper
end LwRust
