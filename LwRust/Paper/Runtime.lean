import Mathlib.Data.Finmap
import LwRust.Paper.Syntax

/-!
Runtime store primitives for the core FR semantics in Section 3.2.
-/

namespace LwRust
namespace Paper

open Core

/--
Paper Section 3 store slot `⟨v⊥⟩^m`, i.e. the current contents and allocation
lifetime of one abstract location.
-/
structure StoreSlot where
  value : PartialValue
  lifetime : Lifetime
  deriving BEq, Repr

/--
Paper Section 3 program store `S`, represented as a mathematical finite partial
map from abstract locations to store slots.

The finite-domain invariant is intentionally left abstract here.  The semantics
uses only lookup, functional update, freshness (`slotAt ℓ = none`), and erasure.
-/
structure ProgramStore where
  slotAt : Location → Option StoreSlot

namespace ProgramStore

def empty : ProgramStore :=
  { slotAt := fun _ => none }

def fresh (store : ProgramStore) (location : Location) : Prop :=
  store.slotAt location = none

def update (store : ProgramStore) (location : Location) (slot : StoreSlot) : ProgramStore :=
  { slotAt := fun candidate =>
      if candidate = location then some slot else store.slotAt candidate }

def erase (store : ProgramStore) (location : Location) : ProgramStore :=
  { slotAt := fun candidate =>
      if candidate = location then none else store.slotAt candidate }

@[simp] theorem empty_slotAt (location : Location) :
    empty.slotAt location = none := by
  rfl

@[simp] theorem update_slotAt_same
    (store : ProgramStore) (location : Location) (slot : StoreSlot) :
    (store.update location slot).slotAt location = some slot := by
  simp [update]

@[simp] theorem update_slotAt_ne
    (store : ProgramStore) {candidate location : Location} (slot : StoreSlot) :
    candidate ≠ location →
    (store.update location slot).slotAt candidate = store.slotAt candidate := by
  intro hne
  simp [update, hne]

@[simp] theorem erase_slotAt_same (store : ProgramStore) (location : Location) :
    (store.erase location).slotAt location = none := by
  simp [erase]

@[simp] theorem erase_slotAt_ne
    (store : ProgramStore) {candidate location : Location} :
    candidate ≠ location →
    (store.erase location).slotAt candidate = store.slotAt candidate := by
  intro hne
  simp [erase, hne]

/--
R-Declare store update: `S[ℓx ↦ ⟨v⟩^l]`.
-/
def declare (store : ProgramStore) (x : Name) (lifetime : Lifetime) (value : Value) :
    ProgramStore :=
  store.update (.var x) { value := .value value, lifetime := lifetime }

/--
R-Box store update at a chosen fresh heap location: `S[ℓn ↦ ⟨v⟩^*]`.
Freshness is a premise of the reduction rule, not executable state.
-/
def boxAt (store : ProgramStore) (address : Nat) (value : Value) : ProgramStore × Reference :=
  let location := Location.heap address
  (store.update location { value := .value value, lifetime := Lifetime.root },
    { location := location, owner := true })

/--
Definition 3.1. Locate the store location denoted by an lval.
-/
def loc (store : ProgramStore) : LVal → Option Location
  | .var x => some (.var x)
  | .deref lv => do
      let location ← loc store lv
      let slot ← store.slotAt location
      match slot.value with
      | .value (.ref ref) => some ref.location
      | .value _ => none
      | .undef => none

/--
Definition 3.2. Read the store slot for an lval.  This can return an undefined
partial value; rules that require a value pattern-match on the returned slot.
-/
def read (store : ProgramStore) (lv : LVal) : Option StoreSlot := do
  let location ← store.loc lv
  store.slotAt location

/--
Definition 3.3. Write a partial value to an existing lval, preserving the
location's allocation lifetime.
-/
def write (store : ProgramStore) (lv : LVal) (value : PartialValue) : Option ProgramStore := do
  let location ← store.loc lv
  let slot ← store.slotAt location
  return store.update location { slot with value := value }

def readValue (store : ProgramStore) (lv : LVal) : Option Value := do
  let slot ← store.read lv
  match slot.value with
  | .value value => some value
  | .undef => none

inductive Drops : ProgramStore → List PartialValue → ProgramStore → Prop where
  | nil {store : ProgramStore} :
      Drops store [] store
  | nonOwner {store store' : ProgramStore} {value : PartialValue} {rest : List PartialValue} :
      (∀ ref, value ≠ .value (.ref ref) ∨ ref.owner = false) →
      Drops store rest store' →
      Drops store (value :: rest) store'
  | ownerMissing {store store' : ProgramStore} {ref : Reference} {rest : List PartialValue} :
      ref.owner = true →
      store.slotAt ref.location = none →
      Drops store rest store' →
      Drops store (.value (.ref ref) :: rest) store'
  | ownerPresent {store store' : ProgramStore} {ref : Reference} {slot : StoreSlot}
      {rest : List PartialValue} :
      ref.owner = true →
      store.slotAt ref.location = some slot →
      Drops (store.erase ref.location) (slot.value :: rest) store' →
      Drops store (.value (.ref ref) :: rest) store'

/--
Definition 3.4, lifetime form.  `DropsLifetime S m S'` is the paper's
`drop(S, m) = S'`.  The drop set is exactly the owned references to locations
allocated in lifetime `m`.
-/
inductive DropsLifetime (store : ProgramStore) (lifetime : Lifetime) (store' : ProgramStore) :
    Prop where
  | intro {dropSet : List PartialValue} :
      (∀ value, value ∈ dropSet ↔
        ∃ location slot,
          store.slotAt location = some slot ∧
          slot.lifetime = lifetime ∧
          value = .value (.ref { location := location, owner := true })) →
      Drops store dropSet store' →
      DropsLifetime store lifetime store'

end ProgramStore

def loc (store : ProgramStore) (lv : LVal) : Option Location :=
  store.loc lv

def read (store : ProgramStore) (lv : LVal) : Option StoreSlot :=
  store.read lv

def write (store : ProgramStore) (lv : LVal) (value : PartialValue) : Option ProgramStore :=
  store.write lv value

abbrev Drops := ProgramStore.Drops
abbrev DropsLifetime := ProgramStore.DropsLifetime

/-! ## Concrete finite implementation -/

/--
A concrete finite implementation of program stores.

`ProgramStore` above is the paper-facing mathematical interface: a partial map
observed through `slotAt`.  `ConcreteProgramStore` is an actual finite map
implementation of the same interface.  Every primitive operation returns another
`ConcreteProgramStore`, so stores started from `empty` remain concrete stores by
construction.
-/
structure ConcreteProgramStore where
  slots : Finmap (fun _ : Location => StoreSlot)

namespace ConcreteProgramStore

def empty : ConcreteProgramStore :=
  { slots := ∅ }

def slotAt (store : ConcreteProgramStore) (location : Location) : Option StoreSlot :=
  store.slots.lookup location

def fresh (store : ConcreteProgramStore) (location : Location) : Prop :=
  store.slotAt location = none

def update (store : ConcreteProgramStore) (location : Location) (slot : StoreSlot) :
    ConcreteProgramStore :=
  { slots := store.slots.insert location slot }

def erase (store : ConcreteProgramStore) (location : Location) : ConcreteProgramStore :=
  { slots := store.slots.erase location }

def toProgramStore (store : ConcreteProgramStore) : ProgramStore :=
  { slotAt := store.slotAt }

instance : Coe ConcreteProgramStore ProgramStore where
  coe := toProgramStore

@[simp] theorem empty_slotAt (location : Location) :
    empty.slotAt location = none := by
  rfl

@[simp] theorem update_slotAt_same
    (store : ConcreteProgramStore) (location : Location) (slot : StoreSlot) :
    (store.update location slot).slotAt location = some slot := by
  simp [slotAt, update]

@[simp] theorem update_slotAt_ne
    (store : ConcreteProgramStore) {candidate location : Location} (slot : StoreSlot) :
    candidate ≠ location →
    (store.update location slot).slotAt candidate = store.slotAt candidate := by
  intro hne
  simp [slotAt, update, hne]

@[simp] theorem erase_slotAt_same (store : ConcreteProgramStore) (location : Location) :
    (store.erase location).slotAt location = none := by
  simp [slotAt, erase]

@[simp] theorem erase_slotAt_ne
    (store : ConcreteProgramStore) {candidate location : Location} :
    candidate ≠ location →
    (store.erase location).slotAt candidate = store.slotAt candidate := by
  intro hne
  simp [slotAt, erase, hne]

/-- Concrete version of R-Declare's store update. -/
def declare (store : ConcreteProgramStore) (x : Name) (lifetime : Lifetime) (value : Value) :
    ConcreteProgramStore :=
  store.update (.var x) { value := .value value, lifetime := lifetime }

/-- Concrete version of R-Box's heap allocation update. -/
def boxAt (store : ConcreteProgramStore) (address : Nat) (value : Value) :
    ConcreteProgramStore × Reference :=
  let location := Location.heap address
  (store.update location { value := .value value, lifetime := Lifetime.root },
    { location := location, owner := true })

/-- Concrete version of Definition 3.1. -/
def loc (store : ConcreteProgramStore) : LVal → Option Location
  | .var x => some (.var x)
  | .deref lv => do
      let location ← loc store lv
      let slot ← store.slotAt location
      match slot.value with
      | .value (.ref ref) => some ref.location
      | .value _ => none
      | .undef => none

/-- Concrete version of Definition 3.2. -/
def read (store : ConcreteProgramStore) (lv : LVal) : Option StoreSlot := do
  let location ← store.loc lv
  store.slotAt location

/-- Concrete version of Definition 3.3. -/
def write (store : ConcreteProgramStore) (lv : LVal) (value : PartialValue) :
    Option ConcreteProgramStore := do
  let location ← store.loc lv
  let slot ← store.slotAt location
  return store.update location { slot with value := value }

def readValue (store : ConcreteProgramStore) (lv : LVal) : Option Value := do
  let slot ← store.read lv
  match slot.value with
  | .value value => some value
  | .undef => none

@[simp] theorem toProgramStore_slotAt (store : ConcreteProgramStore) (location : Location) :
    (store : ProgramStore).slotAt location = store.slotAt location := by
  rfl

@[simp] theorem toProgramStore_empty :
    (empty : ProgramStore) = ProgramStore.empty := by
  rfl

@[simp] theorem toProgramStore_update
    (store : ConcreteProgramStore) (location : Location) (slot : StoreSlot) :
    ((store.update location slot : ConcreteProgramStore) : ProgramStore) =
      (store : ProgramStore).update location slot := by
  apply congrArg ProgramStore.mk
  funext candidate
  by_cases h : candidate = location
  · subst h
    simp
  · simp [h]

@[simp] theorem toProgramStore_erase
    (store : ConcreteProgramStore) (location : Location) :
    ((store.erase location : ConcreteProgramStore) : ProgramStore) =
      (store : ProgramStore).erase location := by
  apply congrArg ProgramStore.mk
  funext candidate
  by_cases h : candidate = location
  · subst h
    simp
  · simp [h]

end ConcreteProgramStore

end Paper
end LwRust
