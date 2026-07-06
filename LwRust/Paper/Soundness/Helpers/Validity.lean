import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import LwRust.Paper.InductiveSemantics
import LwRust.Paper.Typing

/-!
# Soundness helpers: Validity

Section 4.1: validity definitions (ownership, valid term/store/state, valid (partial) value, store typing).
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

/-! ## Source terms -/

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

theorem sourceTerm_unit_value : SourceTerm (.val .unit) := by
  intro value hmem
  simp [termValues] at hmem
  subst hmem
  trivial

theorem sourceTerm_unit_block {lifetime : Lifetime} :
    SourceTerm (.block lifetime [.val .unit]) := by
  intro value hmem
  simp [termValues] at hmem
  subst hmem
  trivial

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

/-- Transitive closure of store ownership edges. -/
inductive OwnsTransitively (store : ProgramStore) : Location → Location → Prop where
  | direct {storage owned : Location} :
      ProgramStore.OwnsAt store owned storage →
      OwnsTransitively store storage owned
  | trans {storage middle owned : Location} :
      ProgramStore.OwnsAt store middle storage →
      OwnsTransitively store middle owned →
      OwnsTransitively store storage owned

theorem OwnsTransitively.trans_right {store : ProgramStore}
    {storage middle owned : Location} :
    ProgramStore.OwnsTransitively store storage middle →
    ProgramStore.OwnsAt store owned middle →
    ProgramStore.OwnsTransitively store storage owned := by
  intro hpath howns
  induction hpath generalizing owned with
  | direct hfirst =>
      exact ProgramStore.OwnsTransitively.trans hfirst
        (ProgramStore.OwnsTransitively.direct howns)
  | trans hfirst _htail ih =>
      exact ProgramStore.OwnsTransitively.trans hfirst (ih howns)

theorem OwnsTransitively.to_owns {store : ProgramStore}
    {storage owned : Location} :
    ProgramStore.OwnsTransitively store storage owned →
    ProgramStore.Owns store owned := by
  intro hpath
  induction hpath with
  | @direct storage owned howns =>
      exact ⟨storage, howns⟩
  | trans _hfirst _htail ih =>
      exact ih

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
Store-side owner-target invariant for the abstract store.

Operationally, owning references are produced by `boxAt`, and `boxAt` always
allocates a heap location.  The abstract `ProgramStore` can otherwise contain
synthetic owning references to variable locations; those states are too broad for
the lifetime-drop preservation statement, because recursive owner dropping may
erase an outer variable that `Γ.dropLifetime` keeps.
-/
def StoreOwnerTargetsHeap (store : ProgramStore) : Prop :=
  ∀ owned,
    ProgramStore.Owns store owned →
    ∃ address, owned = .heap address

/--
Heap slots are created only by `boxAt`, which records them at `Lifetime.root`.
This excludes abstract stores with heap allocations in a block child lifetime;
such states would make `R-BlockB` erase heap ownership that the result value may
still carry.
-/
def HeapSlotsRootLifetime (store : ProgramStore) : Prop :=
  ∀ address slot,
    store.slotAt (.heap address) = some slot →
    slot.lifetime = Lifetime.root

def PartialValueOwnerTargetsHeap (value : PartialValue) : Prop :=
  ∀ owned, owned ∈ partialValueOwningLocations value →
    ∃ address, owned = .heap address

def ValueOwnerTargetsHeap (value : Value) : Prop :=
  ∀ owned, owned ∈ valueOwningLocations value →
    ∃ address, owned = .heap address

def TermOwnerTargetsHeap (term : Term) : Prop :=
  ∀ owned, owned ∈ termOwningLocations term →
    ∃ address, owned = .heap address

theorem sourceTerm_validTerm {term : Term} :
    SourceTerm term →
    ValidTerm term := by
  intro hsource
  simp [ValidTerm, sourceTerm_no_owningLocations hsource]

theorem sourceTerm_ownerTargetsHeap {term : Term} :
    SourceTerm term →
    TermOwnerTargetsHeap term := by
  intro hsource owned hmem
  simp [sourceTerm_no_owningLocations hsource] at hmem

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

`ValidState` follows Definition 4.3.  The store and term owner side conditions
make explicit the allocation/heap-origin invariants that the paper's store model
leaves implicit.
-/
def ValidRuntimeState (store : ProgramStore) (term : Term) : Prop :=
  ValidState store term ∧ StoreOwnersAllocated store ∧ StoreOwnerTargetsHeap store ∧
  HeapSlotsRootLifetime store ∧ TermOwnerTargetsHeap term

theorem ValidState.validStore {store : ProgramStore} {term : Term} :
    ValidState store term → ValidStore store := by
  intro hvalid
  exact hvalid.1

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
  exact hvalid.2.1

theorem ValidRuntimeState.storeOwnerTargetsHeap {store : ProgramStore} {term : Term} :
    ValidRuntimeState store term → StoreOwnerTargetsHeap store := by
  intro hvalid
  exact hvalid.2.2.1

theorem ValidRuntimeState.heapSlotsRootLifetime {store : ProgramStore} {term : Term} :
    ValidRuntimeState store term → HeapSlotsRootLifetime store := by
  intro hvalid
  exact hvalid.2.2.2.1

theorem ValidRuntimeState.termOwnerTargetsHeap {store : ProgramStore} {term : Term} :
    ValidRuntimeState store term → TermOwnerTargetsHeap term := by
  intro hvalid
  exact hvalid.2.2.2.2

theorem TermOwnerTargetsHeap.value {value : Value} :
    TermOwnerTargetsHeap (.val value) → ValueOwnerTargetsHeap value := by
  intro hterm owned hmem
  exact hterm owned (by simpa [termOwningLocations, termValues] using hmem)

theorem LifetimeChild.child_ne_root {parent child : Lifetime} :
    LifetimeChild parent child →
    child ≠ Lifetime.root := by
  intro hchild heq
  rcases hchild with ⟨label, hpath⟩
  have hlen := congrArg (fun lifetime : Lifetime => lifetime.path.length) heq
  simp [Lifetime.root, hpath] at hlen

theorem lifetimeDropOwnersDisjoint_of_heapRootLifetime {store : ProgramStore}
    {parent child : Lifetime} :
    StoreOwnerTargetsHeap store →
    HeapSlotsRootLifetime store →
    LifetimeChild parent child →
    LifetimeDropOwnersDisjoint store child := by
  intro hownersHeap hheapRoot hchild location slot hslot hlifetime howns
  rcases hownersHeap location howns with ⟨address, hlocation⟩
  subst hlocation
  have hroot : slot.lifetime = Lifetime.root := hheapRoot address slot hslot
  exact LifetimeChild.child_ne_root hchild (hlifetime ▸ hroot)

theorem ValueOwnerTargetsHeap.partial {value : Value} :
    ValueOwnerTargetsHeap value → PartialValueOwnerTargetsHeap (.value value) := by
  intro hvalue owned hmem
  exact hvalue owned (by simpa [partialValueOwningLocations] using hmem)

@[simp] theorem termOwnerTargetsHeap_unit :
    TermOwnerTargetsHeap (.val .unit) := by
  intro owned hmem
  simp [termOwningLocations, termValues, valueOwningLocations, valueOwnedLocation?] at hmem

@[simp] theorem termOwnerTargetsHeap_borrowed_ref {location : Location} :
    TermOwnerTargetsHeap (.val (.ref { location := location, owner := false })) := by
  intro owned hmem
  simp [termOwningLocations, termValues, valueOwningLocations, valueOwnedLocation?] at hmem

theorem termOwnerTargetsHeap_value_nonOwner {value : Value} :
    valueOwnedLocation? value = none →
    TermOwnerTargetsHeap (.val value) := by
  intro hnonOwner owned hmem
  simp [termOwningLocations, termValues, valueOwningLocations, hnonOwner] at hmem

theorem termOwnerTargetsHeap_value_of_store_read
    {store : ProgramStore} {lv : LVal} {value : Value} {lifetime : Lifetime} :
    StoreOwnerTargetsHeap store →
    store.read lv = some { value := .value value, lifetime := lifetime } →
    TermOwnerTargetsHeap (.val value) := by
  intro hheap hread owned hmem
  unfold ProgramStore.read at hread
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hread
  | some storage =>
      cases hslot : store.slotAt storage with
      | none =>
          simp [hloc, hslot] at hread
      | some slot =>
          simp [hloc, hslot] at hread
          have hslotEq :
              slot = { value := .value value, lifetime := lifetime } := by
            simpa using hread
          exact hheap owned
            ⟨storage, lifetime, by
              have hvalue := eq_owningRef_of_mem_valueOwningLocations
                (by simpa [termOwningLocations, termValues] using hmem)
              subst hvalue
              simpa [hslotEq] using hslot⟩

theorem termOwnerTargetsHeap_box_inner {term : Term} :
    TermOwnerTargetsHeap (.box term) →
    TermOwnerTargetsHeap term := by
  intro hterm owned hmem
  exact hterm owned (by simpa [termOwningLocations, termValues] using hmem)

theorem termOwnerTargetsHeap_box_value_of_value {value : Value} :
    TermOwnerTargetsHeap (.val value) →
    TermOwnerTargetsHeap (.box (.val value)) := by
  intro hterm owned hmem
  exact hterm owned (by simpa [termOwningLocations, termValues] using hmem)

theorem termOwnerTargetsHeap_declare_value_of_value {x : Name} {value : Value} :
    TermOwnerTargetsHeap (.val value) →
    TermOwnerTargetsHeap (.letMut x (.val value)) := by
  intro hterm owned hmem
  exact hterm owned (by simpa [termOwningLocations, termValues] using hmem)

theorem termOwnerTargetsHeap_declare_inner {x : Name} {term : Term} :
    TermOwnerTargetsHeap (.letMut x term) →
    TermOwnerTargetsHeap term := by
  intro hterm owned hmem
  exact hterm owned (by simpa [termOwningLocations, termValues] using hmem)

theorem termOwnerTargetsHeap_assign_value_of_value {lhs : LVal} {value : Value} :
    TermOwnerTargetsHeap (.val value) →
    TermOwnerTargetsHeap (.assign lhs (.val value)) := by
  intro hterm owned hmem
  exact hterm owned (by simpa [termOwningLocations, termValues] using hmem)

theorem termOwnerTargetsHeap_assign_inner {lhs : LVal} {rhs : Term} :
    TermOwnerTargetsHeap (.assign lhs rhs) →
    TermOwnerTargetsHeap rhs := by
  intro hterm owned hmem
  exact hterm owned (by simpa [termOwningLocations, termValues] using hmem)

theorem termOwnerTargetsHeap_block_head {blockLifetime : Lifetime}
    {term : Term} {rest : List Term} :
    TermOwnerTargetsHeap (.block blockLifetime (term :: rest)) →
    TermOwnerTargetsHeap term := by
  intro hterm owned hmem
  exact hterm owned (by
    simp [termOwningLocations, termValues] at hmem ⊢
    exact Or.inl hmem)

theorem termOwnerTargetsHeap_block_tail {blockLifetime : Lifetime}
    {value : Value} {next : Term} {rest : List Term} :
    TermOwnerTargetsHeap (.block blockLifetime (.val value :: next :: rest)) →
    TermOwnerTargetsHeap (.block blockLifetime (next :: rest)) := by
  intro hterm owned hmem
  exact hterm owned (by
    simp [termOwningLocations, termValues] at hmem ⊢
    exact Or.inr hmem)

theorem termOwnerTargetsHeap_block_value {blockLifetime : Lifetime} {value : Value} :
    TermOwnerTargetsHeap (.block blockLifetime [.val value]) →
    TermOwnerTargetsHeap (.val value) := by
  intro hterm owned hmem
  exact hterm owned (by simpa [termOwningLocations, termValues] using hmem)

theorem termOwnerTargetsHeap_block_singleton {blockLifetime : Lifetime} {term : Term} :
    TermOwnerTargetsHeap (.block blockLifetime [term]) →
    TermOwnerTargetsHeap term := by
  intro hterm owned hmem
  exact hterm owned (by simpa [termOwningLocations, termValues] using hmem)

theorem validState_block_singleton_inner {store : ProgramStore}
    {blockLifetime : Lifetime} {term : Term} :
    ValidState store (.block blockLifetime [term]) →
    ValidState store term := by
  intro hvalid
  exact ⟨hvalid.1,
    by
      simpa [ValidTerm, termOwningLocations, termValues] using hvalid.2.1,
    by
      intro owned hmem
      exact hvalid.2.2 owned
        (by simpa [termOwningLocations, termValues] using hmem)⟩

theorem validRuntimeState_block_singleton_inner {store : ProgramStore}
    {blockLifetime : Lifetime} {term : Term} :
    ValidRuntimeState store (.block blockLifetime [term]) →
    ValidRuntimeState store term := by
  intro hvalid
  exact ⟨validState_block_singleton_inner hvalid.1,
    ValidRuntimeState.storeOwnersAllocated hvalid,
    ValidRuntimeState.storeOwnerTargetsHeap hvalid,
    ValidRuntimeState.heapSlotsRootLifetime hvalid,
    termOwnerTargetsHeap_block_singleton
      (ValidRuntimeState.termOwnerTargetsHeap hvalid)⟩

theorem validState_block_head {store : ProgramStore}
    {blockLifetime : Lifetime} {term : Term} {rest : List Term} :
    ValidState store (.block blockLifetime (term :: rest)) →
    ValidState store term := by
  intro hvalid
  exact ⟨hvalid.1,
    by
      have hvalidAppend :
          (termOwningLocations term ++
            termOwningLocations (.block blockLifetime rest)).Nodup := by
        simpa [ValidTerm, termOwningLocations, termValues] using hvalid.2.1
      exact List.Nodup.of_append_left hvalidAppend,
    by
      intro owned hmem
      exact hvalid.2.2 owned
        (by
          simp [termOwningLocations, termValues] at hmem ⊢
          exact Or.inl hmem)⟩

theorem validRuntimeState_block_head {store : ProgramStore}
    {blockLifetime : Lifetime} {term : Term} {rest : List Term} :
    ValidRuntimeState store (.block blockLifetime (term :: rest)) →
    ValidRuntimeState store term := by
  intro hvalid
  exact ⟨validState_block_head hvalid.1,
    ValidRuntimeState.storeOwnersAllocated hvalid,
    ValidRuntimeState.storeOwnerTargetsHeap hvalid,
    ValidRuntimeState.heapSlotsRootLifetime hvalid,
    termOwnerTargetsHeap_block_head
      (ValidRuntimeState.termOwnerTargetsHeap hvalid)⟩

theorem validState_block_singleton_value_of_value {store : ProgramStore}
    {blockLifetime : Lifetime} {value : Value} :
    ValidState store (.val value) →
    ValidState store (.block blockLifetime [.val value]) := by
  intro hvalid
  simpa [ValidState, ValidTerm, termOwningLocations, termValues] using hvalid

theorem validRuntimeState_block_singleton_value_of_value {store : ProgramStore}
    {blockLifetime : Lifetime} {value : Value} :
    ValidRuntimeState store (.val value) →
    ValidRuntimeState store (.block blockLifetime [.val value]) := by
  intro hvalid
  exact ⟨validState_block_singleton_value_of_value hvalid.1,
    ValidRuntimeState.storeOwnersAllocated hvalid,
    ValidRuntimeState.storeOwnerTargetsHeap hvalid,
    ValidRuntimeState.heapSlotsRootLifetime hvalid,
    by
      intro owned hmem
      exact (ValidRuntimeState.termOwnerTargetsHeap hvalid) owned
        (by simpa [termOwningLocations, termValues] using hmem)⟩

theorem validRuntimeState_block_value_cons_of_value_source_tail
    {store : ProgramStore} {blockLifetime : Lifetime}
    {value : Value} {next : Term} {rest : List Term} :
    SourceTerm (.block blockLifetime (next :: rest)) →
    ValidRuntimeState store (.val value) →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) := by
  intro hsourceTail hvalidValue
  have htailOwners :
      termOwningLocations (.block blockLifetime (next :: rest)) = [] :=
    sourceTerm_no_owningLocations hsourceTail
  have htailOwnersExpanded :
      (List.flatMap valueOwningLocations (termValues next) ++
        List.flatMap valueOwningLocations (List.flatMap termValues rest)) = [] := by
    simpa [termOwningLocations, termValues] using htailOwners
  exact ⟨⟨hvalidValue.1.1,
      by
        have hvalueValidTerm : (valueOwningLocations value).Nodup := by
          simpa [ValidTerm, termOwningLocations, termValues] using hvalidValue.1.2.1
        simpa [ValidTerm, termOwningLocations, termValues, htailOwnersExpanded] using
          hvalueValidTerm,
      by
        intro owned hmem howns
        have hvalueMem : owned ∈ valueOwningLocations value := by
          simpa [termOwningLocations, termValues, htailOwnersExpanded] using hmem
        exact hvalidValue.1.2.2 owned
          (by simpa [termOwningLocations, termValues] using hvalueMem) howns⟩,
    ValidRuntimeState.storeOwnersAllocated hvalidValue,
    ValidRuntimeState.storeOwnerTargetsHeap hvalidValue,
    ValidRuntimeState.heapSlotsRootLifetime hvalidValue,
    by
      intro owned hmem
      have hvalueMem : owned ∈ valueOwningLocations value := by
        simpa [termOwningLocations, termValues, htailOwnersExpanded] using hmem
      exact (ValidRuntimeState.termOwnerTargetsHeap hvalidValue) owned
        (by simpa [termOwningLocations, termValues] using hvalueMem)⟩

theorem validState_box_inner {store : ProgramStore} {term : Term} :
    ValidState store (.box term) →
    ValidState store term := by
  intro hvalid
  simpa [ValidState, ValidTerm, termOwningLocations, termValues] using hvalid

theorem validRuntimeState_box_inner {store : ProgramStore} {term : Term} :
    ValidRuntimeState store (.box term) →
    ValidRuntimeState store term := by
  intro hvalid
  exact ⟨validState_box_inner hvalid.1,
    ValidRuntimeState.storeOwnersAllocated hvalid,
    ValidRuntimeState.storeOwnerTargetsHeap hvalid,
    ValidRuntimeState.heapSlotsRootLifetime hvalid,
    termOwnerTargetsHeap_box_inner (ValidRuntimeState.termOwnerTargetsHeap hvalid)⟩

theorem validState_box_value_of_value {store : ProgramStore} {value : Value} :
    ValidState store (.val value) →
    ValidState store (.box (.val value)) := by
  intro hvalid
  simpa [ValidState, ValidTerm, termOwningLocations, termValues] using hvalid

theorem validRuntimeState_box_value_of_value {store : ProgramStore} {value : Value} :
    ValidRuntimeState store (.val value) →
    ValidRuntimeState store (.box (.val value)) := by
  intro hvalid
  exact ⟨validState_box_value_of_value hvalid.1,
    ValidRuntimeState.storeOwnersAllocated hvalid,
    ValidRuntimeState.storeOwnerTargetsHeap hvalid,
    ValidRuntimeState.heapSlotsRootLifetime hvalid,
    termOwnerTargetsHeap_box_value_of_value
      (ValidRuntimeState.termOwnerTargetsHeap hvalid)⟩

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
  exact ⟨validState_declare_value_of_value hvalid.1,
    ValidRuntimeState.storeOwnersAllocated hvalid,
    ValidRuntimeState.storeOwnerTargetsHeap hvalid,
    ValidRuntimeState.heapSlotsRootLifetime hvalid,
    termOwnerTargetsHeap_declare_value_of_value
      (ValidRuntimeState.termOwnerTargetsHeap hvalid)⟩

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
  exact ⟨validState_declare_inner hvalid.1,
    ValidRuntimeState.storeOwnersAllocated hvalid,
    ValidRuntimeState.storeOwnerTargetsHeap hvalid,
    ValidRuntimeState.heapSlotsRootLifetime hvalid,
    termOwnerTargetsHeap_declare_inner (ValidRuntimeState.termOwnerTargetsHeap hvalid)⟩

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
  exact ⟨validState_assign_value_of_value hvalid.1,
    ValidRuntimeState.storeOwnersAllocated hvalid,
    ValidRuntimeState.storeOwnerTargetsHeap hvalid,
    ValidRuntimeState.heapSlotsRootLifetime hvalid,
    termOwnerTargetsHeap_assign_value_of_value
      (ValidRuntimeState.termOwnerTargetsHeap hvalid)⟩

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
  exact ⟨validState_assign_inner hvalid.1,
    ValidRuntimeState.storeOwnersAllocated hvalid,
    ValidRuntimeState.storeOwnerTargetsHeap hvalid,
    ValidRuntimeState.heapSlotsRootLifetime hvalid,
    termOwnerTargetsHeap_assign_inner (ValidRuntimeState.termOwnerTargetsHeap hvalid)⟩

theorem ValidRuntimeState.validStore {store : ProgramStore} {term : Term} :
    ValidRuntimeState store term → ValidStore store := by
  intro hvalid
  exact hvalid.validState.validStore

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

@[simp] theorem storeOwnerTargetsHeap_empty :
    StoreOwnerTargetsHeap ProgramStore.empty := by
  intro owned howns
  rcases howns with ⟨storage, lifetime, hslot⟩
  simp [ProgramStore.empty] at hslot

@[simp] theorem heapSlotsRootLifetime_empty :
    HeapSlotsRootLifetime ProgramStore.empty := by
  intro address slot hslot
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

theorem storeOwnerTargetsHeap_erase {store : ProgramStore} {erased : Location} :
    StoreOwnerTargetsHeap store →
    StoreOwnerTargetsHeap (store.erase erased) := by
  intro hheap owned howns
  exact hheap owned (owns_erase howns)

theorem heapSlotsRootLifetime_erase {store : ProgramStore} {erased : Location} :
    HeapSlotsRootLifetime store →
    HeapSlotsRootLifetime (store.erase erased) := by
  intro hroot address slot hslot
  by_cases herased : erased = .heap address
  · subst herased
    simp [ProgramStore.erase] at hslot
  · have hcandidate : (.heap address : Location) ≠ erased := by
      intro hcandidate
      exact herased hcandidate.symm
    exact hroot address slot (by
      simpa [ProgramStore.erase, hcandidate] using hslot)

theorem not_owns_var_of_storeOwnerTargetsHeap {store : ProgramStore} {x : Name} :
    StoreOwnerTargetsHeap store →
    ¬ ProgramStore.Owns store (.var x) := by
  intro hheap howns
  rcases hheap (.var x) howns with ⟨address, hlocation⟩
  cases hlocation

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

theorem storeOwnerTargetsHeap_update {store : ProgramStore}
    {updatedLocation : Location} {slot : StoreSlot} :
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap slot.value →
    StoreOwnerTargetsHeap (store.update updatedLocation slot) := by
  intro hheap hslotHeap owned howns
  rcases howns with ⟨storage, slotLifetime, hslot⟩
  by_cases hstorage : storage = updatedLocation
  · have hnewSlot :
        slot = { value := .value (owningRef owned), lifetime := slotLifetime } := by
      simpa [ProgramStore.update, hstorage] using hslot
    exact hslotHeap owned
      (mem_partialValueOwningLocations_of_eq_owningRef
        (by simpa using congrArg StoreSlot.value hnewSlot))
  · have holdOwns : ProgramStore.Owns store owned := by
      exact ⟨storage, slotLifetime, by
        simpa [ProgramStore.update, hstorage] using hslot⟩
    exact hheap owned holdOwns

theorem heapSlotsRootLifetime_update {store : ProgramStore}
    {updatedLocation : Location} {slot : StoreSlot} :
    HeapSlotsRootLifetime store →
    (∀ address, updatedLocation = .heap address → slot.lifetime = Lifetime.root) →
    HeapSlotsRootLifetime (store.update updatedLocation slot) := by
  intro hroot hslotRoot address heapSlot hheapSlot
  by_cases hupdated : updatedLocation = .heap address
  · subst hupdated
    have hslotEq : slot = heapSlot := by
      simpa [ProgramStore.update] using hheapSlot
    subst hslotEq
    exact hslotRoot address rfl
  · have hcandidate : (.heap address : Location) ≠ updatedLocation := by
      intro hcandidate
      exact hupdated hcandidate.symm
    exact hroot address heapSlot (by
      simpa [ProgramStore.update, hcandidate] using hheapSlot)

theorem heapSlotsRootLifetime_update_var {store : ProgramStore}
    {x : Name} {slot : StoreSlot} :
    HeapSlotsRootLifetime store →
    HeapSlotsRootLifetime (store.update (.var x) slot) := by
  intro hroot
  exact heapSlotsRootLifetime_update hroot (by
    intro address hvar
    cases hvar)

theorem heapSlotsRootLifetime_update_heap_root {store : ProgramStore}
    {address : Nat} {value : PartialValue} :
    HeapSlotsRootLifetime store →
    HeapSlotsRootLifetime
      (store.update (.heap address) { value := value, lifetime := Lifetime.root }) := by
  intro hroot
  exact heapSlotsRootLifetime_update hroot (by
    intro otherAddress _hheap
    rfl)

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

theorem storeOwnerTargetsHeap_update_undef {store : ProgramStore} {updated : Location}
    {updatedLifetime : Lifetime} :
    StoreOwnerTargetsHeap store →
    StoreOwnerTargetsHeap (store.update updated { value := .undef, lifetime := updatedLifetime }) := by
  intro hheap
  exact storeOwnerTargetsHeap_update hheap (by
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

theorem storeOwnerTargetsHeap_write_undef {store store' : ProgramStore} {lv : LVal} :
    StoreOwnerTargetsHeap store →
    store.write lv .undef = some store' →
    StoreOwnerTargetsHeap store' := by
  intro hheap hwrite
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
          exact storeOwnerTargetsHeap_update_undef hheap

theorem heapSlotsRootLifetime_write {store store' : ProgramStore} {lv : LVal}
    {value : PartialValue} :
    HeapSlotsRootLifetime store →
    store.write lv value = some store' →
    HeapSlotsRootLifetime store' := by
  intro hroot hwrite
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
          exact heapSlotsRootLifetime_update hroot (by
            intro address hlocation
            subst hlocation
            exact hroot address oldSlot hslot)

theorem heapSlotsRootLifetime_write_undef {store store' : ProgramStore} {lv : LVal} :
    HeapSlotsRootLifetime store →
    store.write lv .undef = some store' →
    HeapSlotsRootLifetime store' := by
  intro hroot hwrite
  exact heapSlotsRootLifetime_write hroot hwrite

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

theorem drops_storeOwnerTargetsHeap {store store' : ProgramStore}
    {values : List PartialValue} :
    Drops store values store' →
    StoreOwnerTargetsHeap store →
    StoreOwnerTargetsHeap store' := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro hheap
      exact hheap
  | nonOwner _hnonOwner _hdrops ih =>
      intro hheap
      exact ih hheap
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hheap
      exact ih hheap
  | ownerPresent _howner _hslot _hdrops ih =>
      intro hheap
      exact ih (storeOwnerTargetsHeap_erase hheap)

theorem drops_heapSlotsRootLifetime {store store' : ProgramStore}
    {values : List PartialValue} :
    Drops store values store' →
    HeapSlotsRootLifetime store →
    HeapSlotsRootLifetime store' := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro hroot
      exact hroot
  | nonOwner _hnonOwner _hdrops ih =>
      intro hroot
      exact ih hroot
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hroot
      exact ih hroot
  | ownerPresent _howner _hslot _hdrops ih =>
      intro hroot
      exact ih (heapSlotsRootLifetime_erase hroot)

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

theorem drops_no_slot_of_mem_owning_ref {store store' : ProgramStore}
    {values : List PartialValue} {location : Location} :
    Drops store values store' →
    (.value (.ref { location := location, owner := true })) ∈ values →
    (∃ slot, store.slotAt location = some slot) →
    ¬ ∃ slot, store'.slotAt location = some slot := by
  intro hdrops
  induction hdrops generalizing location with
  | nil =>
      intro hmem _hslot
      simp at hmem
  | nonOwner hnonOwner _hdrops ih =>
      intro hmem hslot hfinal
      simp at hmem
      rcases hmem with hhead | hrest
      · subst hhead
        exact not_partialValueNonOwner_owning_ref
          (ref := { location := location, owner := true }) rfl hnonOwner
      · exact ih hrest hslot hfinal
  | ownerMissing howner hmissing _hdrops ih =>
      intro hmem hslot hfinal
      rename_i storeBefore storeAfter ref rest
      simp at hmem
      rcases hmem with hhead | hrest
      · cases hhead
        rcases hslot with ⟨slot, hslot⟩
        rw [hslot] at hmissing
        cases hmissing
      · exact ih hrest hslot hfinal
  | ownerPresent howner hpresent _hdrops ih =>
      intro hmem hslot hfinal
      rename_i storeBefore storeAfter ref erasedSlot rest
      simp at hmem
      rcases hmem with hhead | hrest
      · cases hhead
        rcases hfinal with ⟨finalSlot, hfinalSlot⟩
        have herased :
            (storeBefore.erase location).slotAt location = some finalSlot :=
          drops_slotAt_of_slotAt _hdrops hfinalSlot
        simp [ProgramStore.erase] at herased
      · by_cases hrefLocation : ref.location = location
        · subst hrefLocation
          rcases hfinal with ⟨finalSlot, hfinalSlot⟩
          have herased :
              (storeBefore.erase ref.location).slotAt ref.location = some finalSlot :=
            drops_slotAt_of_slotAt _hdrops hfinalSlot
          simp [ProgramStore.erase] at herased
        · have herasedSlot : ∃ slot, (storeBefore.erase ref.location).slotAt location = some slot := by
            rcases hslot with ⟨slot, hslot⟩
            have hcandidate : location ≠ ref.location := by
              intro hcandidate
              exact hrefLocation hcandidate.symm
            exact ⟨slot, by simpa [ProgramStore.erase, hcandidate] using hslot⟩
          exact ih (by simp [hrest]) herasedSlot hfinal

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

theorem partialValueOwnerTargetsHeap_of_slot {store : ProgramStore}
    {location : Location} {slot : StoreSlot} :
    StoreOwnerTargetsHeap store →
    store.slotAt location = some slot →
    PartialValueOwnerTargetsHeap slot.value := by
  intro hheap hslot owned hmem
  have hslotValue : slot.value = .value (owningRef owned) :=
    eq_owningRef_of_mem_partialValueOwningLocations hmem
  exact hheap owned ⟨location, slot.lifetime, by
    cases slot with
    | mk slotValue slotLifetime =>
        cases hslotValue
        simpa using hslot⟩

theorem dropsAvoids_var_of_ownerTargetsHeap
    {store store' : ProgramStore} {values : List PartialValue} {x : Name} :
    Drops store values store' →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    DropsAvoids store values (.var x) := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro _hheap _hvalues
      exact DropsAvoids.nil
  | nonOwner hnonOwner _hdrops ih =>
      intro hheap hvalues
      exact DropsAvoids.nonOwner hnonOwner
        (ih hheap (by
          intro value hmem
          exact hvalues value (by simp [hmem])))
  | ownerMissing howner hmissing _hdrops ih =>
      intro hheap hvalues
      exact DropsAvoids.ownerMissing howner hmissing
        (ih hheap (by
          intro value hmem
          exact hvalues value (by simp [hmem])))
  | ownerPresent howner hslot _hdrops ih =>
      intro hheap hvalues
      rename_i storeBefore storeAfter ref slot rest
      have hheadHeap : ∃ address, ref.location = .heap address := by
        exact hvalues (.value (.ref ref)) (by simp) ref.location
          (mem_partialValueOwningLocations_ref_true howner)
      have hrefNeVar : ref.location ≠ .var x := by
        intro href
        rcases hheadHeap with ⟨address, hheapLocation⟩
        rw [href] at hheapLocation
        cases hheapLocation
      have hslotHeap : PartialValueOwnerTargetsHeap slot.value :=
        partialValueOwnerTargetsHeap_of_slot hheap hslot
      exact DropsAvoids.ownerPresent howner hslot hrefNeVar
        (ih (storeOwnerTargetsHeap_erase hheap) (by
          intro value hmem
          simp at hmem
          rcases hmem with hvalue | hrest
          · subst hvalue
            exact hslotHeap
          · exact hvalues value (by simp [hrest])))

theorem dropsAvoids_var_of_not_owning_var
    {store store' : ProgramStore} {values : List PartialValue} {x : Name} :
    Drops store values store' →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → (.var x) ∉ partialValueOwningLocations value) →
    DropsAvoids store values (.var x) := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro _hheap _hvalues
      exact DropsAvoids.nil
  | nonOwner hnonOwner _hdrops ih =>
      intro hheap hvalues
      exact DropsAvoids.nonOwner hnonOwner
        (ih hheap (by
          intro value hmem
          exact hvalues value (by simp [hmem])))
  | ownerMissing howner hmissing _hdrops ih =>
      intro hheap hvalues
      exact DropsAvoids.ownerMissing howner hmissing
        (ih hheap (by
          intro value hmem
          exact hvalues value (by simp [hmem])))
  | ownerPresent howner hslot _hdrops ih =>
      intro hheap hvalues
      rename_i storeBefore storeAfter ref slot rest
      have hrefNeVar : ref.location ≠ .var x := by
        intro href
        exact hvalues (.value (.ref ref)) (by simp)
          (by
            simpa [href] using mem_partialValueOwningLocations_ref_true howner)
      have hslotHeap : PartialValueOwnerTargetsHeap slot.value :=
        partialValueOwnerTargetsHeap_of_slot hheap hslot
      have hslotNotVar : (.var x) ∉ partialValueOwningLocations slot.value := by
        intro hmem
        rcases hslotHeap (.var x) hmem with ⟨address, hlocation⟩
        cases hlocation
      exact DropsAvoids.ownerPresent howner hslot hrefNeVar
        (ih (storeOwnerTargetsHeap_erase hheap) (by
          intro value hmem
          simp at hmem
          rcases hmem with hvalue | hrest
          · subst hvalue
            exact hslotNotVar
          · exact hvalues value (by simp [hrest])))

/--
If neither the explicit drop list nor the store owns `location`, then recursive
dropping avoids `location`.
-/
theorem dropsAvoids_of_not_owns_and_not_mem
    {store store' : ProgramStore} {values : List PartialValue}
    {location : Location} :
    Drops store values store' →
    (∀ value, value ∈ values → location ∉ partialValueOwningLocations value) →
    ¬ ProgramStore.Owns store location →
    DropsAvoids store values location := by
  intro hdrops
  induction hdrops generalizing location with
  | nil =>
      intro _hnotMem _hnotOwns
      exact DropsAvoids.nil
  | nonOwner hnonOwner _hdrops ih =>
      intro hnotMem hnotOwns
      exact DropsAvoids.nonOwner hnonOwner
        (ih (by
          intro value hmem
          exact hnotMem value (by simp [hmem])) hnotOwns)
  | ownerMissing howner hmissing _hdrops ih =>
      intro hnotMem hnotOwns
      exact DropsAvoids.ownerMissing howner hmissing
        (ih (by
          intro value hmem
          exact hnotMem value (by simp [hmem])) hnotOwns)
  | ownerPresent howner hpresent _hdrops ih =>
      intro hnotMem hnotOwns
      rename_i storeBefore _storeAfter ref slot rest
      have hrefNe : ref.location ≠ location := by
        intro href
        exact hnotMem (.value (.ref ref)) (by simp)
          (by
            simpa [href] using mem_partialValueOwningLocations_ref_true howner)
      have htailNotMem :
          ∀ value, value ∈ slot.value :: rest →
            location ∉ partialValueOwningLocations value := by
        intro value hmem
        simp at hmem
        rcases hmem with hslotValue | hrest
        · subst hslotValue
          intro howned
          have hslotOwns :
              ProgramStore.OwnsAt storeBefore location ref.location := by
            have hslotValueEq : slot.value = .value (owningRef location) :=
              eq_owningRef_of_mem_partialValueOwningLocations howned
            exact ⟨slot.lifetime, by
              cases slot with
              | mk slotValue slotLifetime =>
                  cases hslotValueEq
                  simpa [owningRef] using hpresent⟩
          exact hnotOwns ⟨ref.location, hslotOwns⟩
        · exact hnotMem value (by simp [hrest])
      have hnotOwnsAfterErase :
          ¬ ProgramStore.Owns (storeBefore.erase ref.location) location := by
        intro howns
        exact hnotOwns (owns_erase howns)
      exact DropsAvoids.ownerPresent howner hpresent hrefNe
        (ih htailNotMem hnotOwnsAfterErase)

/--
If `storage` continues to protect an ownership edge to `owned`, then a drop
list that avoids `storage` also avoids `owned`, provided the explicit drop-list
heads do not themselves contain an owning reference to `owned`.

The recursive owner-present case is the interesting one: if the opened slot
owned `owned`, the store would have two owners for `owned` (`storage` and the
opened location), contradicting `ValidStore`.
-/
theorem dropsAvoids_of_protected_owner {store store' : ProgramStore}
    {values : List PartialValue} {owned storage : Location} :
    Drops store values store' →
    ValidStore store →
    ProgramStore.OwnsAt store owned storage →
    DropsAvoids store values storage →
    (∀ value, value ∈ values → owned ∉ partialValueOwningLocations value) →
    DropsAvoids store values owned := by
  intro hdrops
  induction hdrops generalizing storage with
  | nil =>
      intro _hvalid _howns _havoidStorage _hdisjoint
      exact DropsAvoids.nil
  | nonOwner hnonOwner _hdrops ih =>
      intro hvalid howns havoidStorage hdisjoint
      cases havoidStorage with
      | nonOwner _ havoidRest =>
          exact DropsAvoids.nonOwner hnonOwner
            (ih hvalid howns havoidRest (by
              intro value hmem
              exact hdisjoint value (by simp [hmem])))
      | ownerMissing howner _ _ =>
          exact False.elim
            (not_partialValueNonOwner_owning_ref howner hnonOwner)
      | ownerPresent howner _ _ _ =>
          exact False.elim
            (not_partialValueNonOwner_owning_ref howner hnonOwner)
  | ownerMissing howner hmissing _hdrops ih =>
      intro hvalid howns havoidStorage hdisjoint
      cases havoidStorage with
      | nonOwner hnonOwner _ =>
          exact False.elim
            (not_partialValueNonOwner_owning_ref howner hnonOwner)
      | ownerMissing _ _ havoidRest =>
          exact DropsAvoids.ownerMissing howner hmissing
            (ih hvalid howns havoidRest (by
              intro value hmem
              exact hdisjoint value (by simp [hmem])))
      | ownerPresent _ hpresent _ _ =>
          rw [hmissing] at hpresent
          cases hpresent
  | ownerPresent howner hpresent _hdrops ih =>
      intro hvalid howns havoidStorage hdisjoint
      rename_i storeBefore storeAfter ref slot rest
      cases havoidStorage with
      | nonOwner hnonOwner _ =>
          exact False.elim
            (not_partialValueNonOwner_owning_ref howner hnonOwner)
      | ownerMissing _ hmissing _ =>
          rw [hpresent] at hmissing
          cases hmissing
      | ownerPresent _ hpresentStorage hstorageNe havoidRest =>
          rw [hpresent] at hpresentStorage
          cases hpresentStorage
          have hrefNeOwned : ref.location ≠ owned := by
            intro hrefOwned
            exact hdisjoint (.value (.ref ref)) (by simp)
              (by
                rw [← hrefOwned]
                exact mem_partialValueOwningLocations_ref_true howner)
          refine DropsAvoids.ownerPresent howner hpresent hrefNeOwned ?_
          have hvalidErased : ValidStore (storeBefore.erase ref.location) :=
            validStore_erase hvalid
          have hownsErased :
              ProgramStore.OwnsAt (storeBefore.erase ref.location) owned storage := by
            rcases howns with ⟨ownerLifetime, hownerSlot⟩
            exact ⟨ownerLifetime, by
              simpa [ProgramStore.erase, hstorageNe.symm] using hownerSlot⟩
          exact ih hvalidErased hownsErased havoidRest (by
            intro value hmem
            simp at hmem
            rcases hmem with hvalue | hrest
            · subst hvalue
              intro hownedInSlot
              have hslotValue :
                  slot.value = .value (owningRef owned) :=
                eq_owningRef_of_mem_partialValueOwningLocations hownedInSlot
              have hopenedOwns :
                  ProgramStore.OwnsAt storeBefore owned ref.location := by
                have hslotStruct :
                    slot =
                      { value := .value (owningRef owned),
                        lifetime := slot.lifetime } := by
                  cases slot with
                  | mk slotValue slotLifetime =>
                      cases hslotValue
                      rfl
                exact ⟨slot.lifetime,
                  hpresent.trans (congrArg some hslotStruct)⟩
              exact hstorageNe
                (hvalid owned ref.location storage hopenedOwns howns)
            · exact hdisjoint value (by simp [hrest]))

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

theorem dropsLifetime_storeOwnerTargetsHeap {store store' : ProgramStore}
    {lifetime : Lifetime} :
    DropsLifetime store lifetime store' →
    StoreOwnerTargetsHeap store →
    StoreOwnerTargetsHeap store' := by
  intro hdrops hheap
  cases hdrops with
  | intro _hdropSet hdrops =>
      exact drops_storeOwnerTargetsHeap hdrops hheap

theorem dropsLifetime_heapSlotsRootLifetime {store store' : ProgramStore}
    {lifetime : Lifetime} :
    DropsLifetime store lifetime store' →
    HeapSlotsRootLifetime store →
    HeapSlotsRootLifetime store' := by
  intro hdrops hroot
  cases hdrops with
  | intro _hdropSet hdrops =>
      exact drops_heapSlotsRootLifetime hdrops hroot

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

theorem dropsLifetime_slot_not_dropped {store store' : ProgramStore}
    {lifetime : Lifetime} {location : Location} {slot : StoreSlot} :
    DropsLifetime store lifetime store' →
    store'.slotAt location = some slot →
    slot.lifetime ≠ lifetime := by
  intro hdrops hslotFinal hlifetime
  cases hdrops with
  | intro hdropSet hdrops =>
      have hslotInitial : store.slotAt location = some slot :=
        drops_slotAt_of_slotAt hdrops hslotFinal
      have hmem :=
        (hdropSet (PartialValue.value (.ref { location := location, owner := true }))).mpr
          ⟨location, slot, hslotInitial, hlifetime, rfl⟩
      exact drops_no_slot_of_mem_owning_ref hdrops hmem ⟨slot, hslotInitial⟩
        ⟨slot, hslotFinal⟩

theorem dropsLifetime_preserves_var_slot_of_not_lifetime
    {store store' : ProgramStore} {lifetime : Lifetime} {x : Name} {slot : StoreSlot} :
    DropsLifetime store lifetime store' →
    StoreOwnerTargetsHeap store →
    store.slotAt (.var x) = some slot →
    slot.lifetime ≠ lifetime →
    store'.slotAt (.var x) = some slot := by
  intro hdrops hheap hslot hlifetime
  cases hdrops with
  | intro hdropSet hdrops =>
      exact dropsAvoids_slotAt_preserved hdrops
        (dropsAvoids_var_of_not_owning_var hdrops hheap (by
          intro dropValue hmem hownsVar
          rcases (hdropSet dropValue).mp hmem with
            ⟨location, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
          have howned : (.var x : Location) = location :=
            eq_location_of_mem_lifetime_drop_value hdropValue hownsVar
          subst howned
          have hdropSlotEq : dropSlot = slot := by
            rw [hslot] at hdropSlot
            injection hdropSlot with hdropSlotEq
            exact hdropSlotEq.symm
          subst hdropSlotEq
          exact hlifetime hdropLifetime))
        hslot

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

theorem storeOwnerTargetsHeap_write {store store' : ProgramStore} {lv : LVal}
    {value : PartialValue} :
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap value →
    store.write lv value = some store' →
    StoreOwnerTargetsHeap store' := by
  intro hheap hvalueHeap hwrite
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
          exact storeOwnerTargetsHeap_update hheap hvalueHeap

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

end Paper
end LwRust
