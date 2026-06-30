import LwRust.Paper.Soundness.Helpers.RuntimeFacts

/-!
# Soundness helpers: store-update frame facts

Small frame lemmas for single-location store updates.  These are used to turn
runtime preservation obligations into concrete reachability side conditions.
-/

namespace LwRust
namespace Paper

open Core

namespace RuntimeFrame

/-- Updating a location leaves the lookup at any other location unchanged. -/
theorem ProgramStore.slotAt_update_ne {store : ProgramStore}
    {updated location : Location} {slot : StoreSlot} :
    location ≠ updated →
    (store.update updated slot).slotAt location = store.slotAt location := by
  intro hne
  simp [ProgramStore.update, hne]

/--
The locations whose slots are inspected while resolving `loc store lv`.
A variable reads no slot; a dereference reads the slot at the location its
source resolves to, plus whatever the source reads.
-/
inductive LocReads (store : ProgramStore) : LVal → Location → Prop where
  | here {lv : LVal} {location : Location} :
      store.loc lv = some location →
      LocReads store (.deref lv) location
  | there {lv : LVal} {location : Location} :
      LocReads store lv location →
      LocReads store (.deref lv) location

theorem LocReads.strictPrefix {store : ProgramStore}
    {lv : LVal} {location : Location} :
    LocReads store lv location →
    ∃ readPrefix, LVal.StrictPrefixOf readPrefix lv ∧
      store.loc readPrefix = some location := by
  intro hreads
  induction hreads with
  | here hloc =>
      exact ⟨_, LVal.StrictPrefixOf.self_deref _, hloc⟩
  | there _ ih =>
      rcases ih with ⟨readPrefix, hprefix, hloc⟩
      exact ⟨readPrefix, LVal.StrictPrefixOf.deref_right hprefix, hloc⟩

/-- If an update misses every location read while resolving `lv`, resolution is unchanged. -/
theorem loc_update_of_not_locReads {store : ProgramStore}
    {updated : Location} {slot : StoreSlot} :
    ∀ {lv : LVal} {location : Location},
      store.loc lv = some location →
      (∀ mid, LocReads store lv mid → mid ≠ updated) →
      (store.update updated slot).loc lv = some location := by
  intro lv
  induction lv with
  | var x =>
      intro location hloc _hreads
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      intro location hloc hreads
      cases hsource : store.loc lv with
      | none => simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          have hsourceNe : source ≠ updated :=
            hreads source (LocReads.here hsource)
          have hsource' : (store.update updated slot).loc lv = some source := by
            refine ih hsource ?_
            intro mid hmid
            exact hreads mid (LocReads.there hmid)
          have hslotEq :
              (store.update updated slot).slotAt source = store.slotAt source :=
            ProgramStore.slotAt_update_ne hsourceNe
          have hlocEq :
              (store.update updated slot).loc (.deref lv) = store.loc (.deref lv) := by
            simp [ProgramStore.loc, hsource, hsource', hslotEq]
          rw [hlocEq]
          exact hloc

/--
Reads observed after an update were already present before the update, provided
the original resolution of the lvalue avoided the updated location.
-/
theorem locReads_update_to_store_of_not_locReads {store : ProgramStore}
    {updated : Location} {slot : StoreSlot} :
    ∀ {lv : LVal} {location read : Location},
      store.loc lv = some location →
      (∀ mid, LocReads store lv mid → mid ≠ updated) →
      LocReads (store.update updated slot) lv read →
      LocReads store lv read := by
  intro lv
  induction lv with
  | var x =>
      intro location read _hloc _hreads hpost
      cases hpost
  | deref lv ih =>
      intro location read hloc hreads hpost
      cases hsource : store.loc lv with
      | none =>
          simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          have hsource' :
              (store.update updated slot).loc lv = some source :=
            loc_update_of_not_locReads hsource (by
              intro mid hmid
              exact hreads mid (LocReads.there hmid))
          cases hpost with
          | here hpostSource =>
              have hreadEq : read = source := by
                rw [hsource'] at hpostSource
                exact (Option.some.inj hpostSource).symm
              subst hreadEq
              exact LocReads.here hsource
          | there hpostRead =>
              exact LocReads.there
                (ih hsource
                  (by
                    intro mid hmid
                    exact hreads mid (LocReads.there hmid))
                  hpostRead)

/-- If an erase misses every location read while resolving `lv`, resolution is unchanged. -/
theorem loc_erase_of_not_locReads {store : ProgramStore}
    {erased : Location} :
    ∀ {lv : LVal} {location : Location},
      store.loc lv = some location →
      (∀ mid, LocReads store lv mid → mid ≠ erased) →
      (store.erase erased).loc lv = some location := by
  intro lv
  induction lv with
  | var x =>
      intro location hloc _hreads
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      intro location hloc hreads
      cases hsource : store.loc lv with
      | none => simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          have hsourceNe : source ≠ erased :=
            hreads source (LocReads.here hsource)
          have hsource' : (store.erase erased).loc lv = some source := by
            refine ih hsource ?_
            intro mid hmid
            exact hreads mid (LocReads.there hmid)
          have hslotEq :
              (store.erase erased).slotAt source = store.slotAt source := by
            rw [ProgramStore.erase_slotAt_ne]
            exact hsourceNe
          have hlocEq :
              (store.erase erased).loc (.deref lv) = store.loc (.deref lv) := by
            simp [ProgramStore.loc, hsource, hsource', hslotEq]
          rw [hlocEq]
          exact hloc

/-- A successful lookup after erasing a location also succeeds in the original store. -/
theorem slotAt_of_erase_slotAt {store : ProgramStore}
    {erased location : Location} {slot : StoreSlot} :
    (store.erase erased).slotAt location = some slot →
    store.slotAt location = some slot := by
  intro hslot
  by_cases hlocation : location = erased
  · subst hlocation
    simp [ProgramStore.erase] at hslot
  · simpa [ProgramStore.erase, hlocation] using hslot

/-- If `loc` resolves after an erase, the same lval resolved before the erase. -/
theorem loc_erase_some_to_store {store : ProgramStore}
    {erased : Location} :
    ∀ {lv : LVal} {location : Location},
      (store.erase erased).loc lv = some location →
      store.loc lv = some location := by
  intro lv
  induction lv with
  | var x =>
      intro location hloc
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      intro location hloc
      cases hsourceErased : (store.erase erased).loc lv with
      | none => simp [ProgramStore.loc, hsourceErased] at hloc
      | some source =>
          have hsource : store.loc lv = some source := ih hsourceErased
          cases hslotErased : (store.erase erased).slotAt source with
          | none => simp [ProgramStore.loc, hsourceErased, hslotErased] at hloc
          | some slot =>
              have hslot : store.slotAt source = some slot :=
                slotAt_of_erase_slotAt hslotErased
              simp [ProgramStore.loc, hsourceErased, hslotErased] at hloc
              simp [ProgramStore.loc, hsource, hslot, hloc]

/-- If a drop sequence avoids every location read while resolving `lv`, then
`lv` resolves to the same location after the drop. -/
theorem loc_drops_of_not_locReads {store store' : ProgramStore}
    {values : List PartialValue} :
    Drops store values store' →
    ∀ {lv : LVal} {location : Location},
      store.loc lv = some location →
      (∀ mid, LocReads store lv mid → DropsAvoids store values mid) →
      store'.loc lv = some location := by
  intro hdrops lv
  induction lv with
  | var x =>
      intro location hloc _hreads
      simpa [ProgramStore.loc] using hloc
  | deref source ih =>
      intro location hloc hreads
      cases hsource : store.loc source with
      | none =>
          simp [ProgramStore.loc, hsource] at hloc
      | some sourceLocation =>
          cases hsourceSlot : store.slotAt sourceLocation with
          | none =>
              simp [ProgramStore.loc, hsource, hsourceSlot] at hloc
          | some sourceSlot =>
              have hsource' :
                  store'.loc source = some sourceLocation :=
                ih hsource (by
                  intro mid hmid
                  exact hreads mid (LocReads.there hmid))
              have hsourceSlot' :
                  store'.slotAt sourceLocation = some sourceSlot :=
                dropsAvoids_slotAt_preserved hdrops
                  (hreads sourceLocation (LocReads.here hsource))
                  hsourceSlot
              have hlocEq :
                  store'.loc (.deref source) = store.loc (.deref source) := by
                simp [ProgramStore.loc, hsource, hsource', hsourceSlot,
                  hsourceSlot']
              rw [hlocEq]
              exact hloc

/-- Location reads observed after an erase are reads of the original store. -/
theorem locReads_erase_to_store {store : ProgramStore}
    {erased : Location} {lv : LVal} {location : Location} :
    LocReads (store.erase erased) lv location →
    LocReads store lv location := by
  intro hreads
  induction hreads with
  | here hloc =>
      exact LocReads.here (loc_erase_some_to_store hloc)
  | there _hreads ih =>
      exact LocReads.there ih

/-- If `loc` resolves after a recursive drop, it also resolved in the original store. -/
theorem loc_drops_to_store {store store' : ProgramStore}
    {values : List PartialValue} :
    Drops store values store' →
    ∀ {lv : LVal} {location : Location},
      store'.loc lv = some location →
      store.loc lv = some location := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro lv location hloc
      exact hloc
  | nonOwner _hnonOwner _hdrops ih =>
      intro lv location hloc
      exact ih hloc
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro lv location hloc
      exact ih hloc
  | ownerPresent _howner _hslot _hdrops ih =>
      intro lv location hloc
      exact loc_erase_some_to_store (ih hloc)

/-- Location reads observed after a recursive drop are reads of the original store. -/
theorem locReads_drops_to_store {store store' : ProgramStore}
    {values : List PartialValue} {lv : LVal} {location : Location} :
    Drops store values store' →
    LocReads store' lv location →
    LocReads store lv location := by
  intro hdrops hreads
  induction hdrops with
  | nil =>
      exact hreads
  | nonOwner _hnonOwner _hdrops ih =>
      exact ih hreads
  | ownerMissing _howner _hmissing _hdrops ih =>
      exact ih hreads
  | ownerPresent _howner _hslot _hdrops ih =>
      exact locReads_erase_to_store (ih hreads)

/--
The store locations whose slots are inspected while checking
`ValidPartialValue store v ty`.  Owned references read their pointee slot and
recurse; borrowed references read only the lval-resolution path of their
selected target.
-/
inductive Reaches (store : ProgramStore) : PartialValue → PartialTy → Location → Prop where
  | boxHere {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      Reaches store (.value (.ref { location := location, owner := true })) (.box inner)
        location
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy} {ℓ : Location} :
      store.slotAt location = some slot →
      Reaches store slot.value inner ℓ →
      Reaches store (.value (.ref { location := location, owner := true })) (.box inner) ℓ
  | boxFullHere {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      Reaches store (.value (.ref { location := location, owner := true })) (.ty (.box ty))
        location
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty} {ℓ : Location} :
      store.slotAt location = some slot →
      Reaches store slot.value (.ty ty) ℓ →
      Reaches store (.value (.ref { location := location, owner := true })) (.ty (.box ty)) ℓ
  | borrow {location ℓ : Location} {mutable : Bool} {targets : List LVal}
      {target : LVal} :
      target ∈ targets →
      store.loc target = some location →
      LocReads store target ℓ →
      Reaches store (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets)) ℓ

/--
Ownership reachability through a value.  Unlike `Reaches`, this relation does not
include the lval-resolution reads of borrowed references; those reads are
dependencies, but they are not ownership edges.
-/
inductive OwnerReaches (store : ProgramStore) : PartialValue → PartialTy → Location → Prop where
  | boxHere {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      OwnerReaches store (.value (.ref { location := location, owner := true })) (.box inner)
        location
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy} {ℓ : Location} :
      store.slotAt location = some slot →
      OwnerReaches store slot.value inner ℓ →
      OwnerReaches store (.value (.ref { location := location, owner := true })) (.box inner) ℓ
  | boxFullHere {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      OwnerReaches store (.value (.ref { location := location, owner := true })) (.ty (.box ty))
        location
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty} {ℓ : Location} :
      store.slotAt location = some slot →
      OwnerReaches store slot.value (.ty ty) ℓ →
      OwnerReaches store (.value (.ref { location := location, owner := true })) (.ty (.box ty)) ℓ

/-- Borrow-target lval-resolution dependencies inside a value. -/
inductive BorrowDependency (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | borrow {location readLocation : Location} {mutable : Bool}
      {targets : List LVal} {target : LVal} :
      target ∈ targets →
      store.loc target = some location →
      LocReads store target readLocation →
      BorrowDependency store (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets)) readLocation
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {dependency : Location} :
      store.slotAt location = some slot →
      BorrowDependency store slot.value inner dependency →
      BorrowDependency store
        (.value (.ref { location := location, owner := true })) (.box inner) dependency
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {dependency : Location} :
      store.slotAt location = some slot →
      BorrowDependency store slot.value (.ty ty) dependency →
      BorrowDependency store
        (.value (.ref { location := location, owner := true })) (.ty (.box ty)) dependency

theorem OwnerReaches.reaches {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    OwnerReaches store value ty location →
    Reaches store value ty location := by
  intro hreach
  induction hreach with
  | boxHere hslot => exact Reaches.boxHere hslot
  | boxInner hslot _ ih => exact Reaches.boxInner hslot ih
  | boxFullHere hslot => exact Reaches.boxFullHere hslot
  | boxFullInner hslot _ ih => exact Reaches.boxFullInner hslot ih

theorem BorrowDependency.reaches {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    BorrowDependency store value ty location →
    Reaches store value ty location := by
  intro hdependency
  induction hdependency with
  | borrow hmem hloc hreads => exact Reaches.borrow hmem hloc hreads
  | boxInner hslot _ ih => exact Reaches.boxInner hslot ih
  | boxFullInner hslot _ ih => exact Reaches.boxFullInner hslot ih

theorem Reaches.owner_or_borrow {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    Reaches store value ty location →
    OwnerReaches store value ty location ∨
      BorrowDependency store value ty location := by
  intro hreach
  induction hreach with
  | boxHere hslot =>
      exact Or.inl (OwnerReaches.boxHere hslot)
  | boxInner hslot _ ih =>
      rcases ih with howner | hborrow
      · exact Or.inl (OwnerReaches.boxInner hslot howner)
      · exact Or.inr (BorrowDependency.boxInner hslot hborrow)
  | boxFullHere hslot =>
      exact Or.inl (OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _ ih =>
      rcases ih with howner | hborrow
      · exact Or.inl (OwnerReaches.boxFullInner hslot howner)
      · exact Or.inr (BorrowDependency.boxFullInner hslot hborrow)
  | borrow hmem hloc hreads =>
      exact Or.inr (BorrowDependency.borrow hmem hloc hreads)

/--
Borrow-target lval-resolution dependencies selected by a particular validity
proof.  Unlike `BorrowDependency`, this does not range over every target in the
static target list; the `borrow` constructor follows the target used by
`ValidPartialValue.borrow`.
-/
inductive SelectedBorrowDependency (store : ProgramStore) :
    {value : PartialValue} → {ty : PartialTy} →
      ValidPartialValue store value ty → Location → Prop where
  | borrow {location : Location} {mutable : Bool} {targets : List LVal}
      {target : LVal} {hmem : target ∈ targets}
      {hloc : store.loc target = some location} {dependency : Location} :
      LocReads store target dependency →
      SelectedBorrowDependency store (ValidPartialValue.borrow hmem hloc)
        dependency
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {hslot : store.slotAt location = some slot}
      {hinner : ValidPartialValue store slot.value inner}
      {dependency : Location} :
      SelectedBorrowDependency store hinner dependency →
      SelectedBorrowDependency store (ValidPartialValue.box hslot hinner)
        dependency
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {hslot : store.slotAt location = some slot}
      {hinner : ValidPartialValue store slot.value (.ty ty)}
      {dependency : Location} :
      SelectedBorrowDependency store hinner dependency →
      SelectedBorrowDependency store (ValidPartialValue.boxFull hslot hinner)
        dependency

theorem SelectedBorrowDependency.borrowDependency {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {hvalid : ValidPartialValue store value ty} {dependency : Location} :
    SelectedBorrowDependency store hvalid dependency →
    BorrowDependency store value ty dependency := by
  intro hdependency
  induction hdependency with
  | @borrow _ location mutable targets target hmem hloc dependency hreads =>
      exact BorrowDependency.borrow hmem hloc hreads
  | @boxInner location slot inner hslot hinner dependency _hdependency ih =>
      exact BorrowDependency.boxInner hslot ih
  | @boxFullInner location slot innerTy hslot hinner dependency _hdependency ih =>
      exact BorrowDependency.boxFullInner hslot ih

/--
Proof-carrying runtime evidence for `ValidPartialValue`.

The paper-level validity judgement is a `Prop`, so it cannot reliably remember
which borrow target witnessed a reference after a target-list widening.  This
evidence object mirrors the validity constructors in `Type` and stores that
chosen target as data.
-/
inductive ValidPartialValueEvidence (store : ProgramStore) :
    PartialValue → PartialTy → Type where
  | unit :
      ValidPartialValueEvidence store (.value .unit) (.ty .unit)
  | int {value : Int} :
      ValidPartialValueEvidence store (.value (.int value)) (.ty .int)
  | bool {value : Bool} :
      ValidPartialValueEvidence store (.value (.bool value)) (.ty .bool)
  | undef {ty : Ty} :
      ValidPartialValueEvidence store .undef (.undef ty)
  | borrow {location : Location} {mutable : Bool}
      {targets : List LVal} (target : LVal) :
      target ∈ targets →
      store.loc target = some location →
      ValidPartialValueEvidence store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets))
  | box {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      ValidPartialValueEvidence store slot.value inner →
      ValidPartialValueEvidence store
        (.value (.ref { location := location, owner := true }))
        (.box inner)
  | boxFull {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      ValidPartialValueEvidence store slot.value (.ty ty) →
      ValidPartialValueEvidence store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty))

def ValidPartialValueEvidence.valid {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValueEvidence store value ty →
    ValidPartialValue store value ty
  | unit => ValidPartialValue.unit
  | int => ValidPartialValue.int
  | bool => ValidPartialValue.bool
  | undef => ValidPartialValue.undef
  | borrow _target hmem hloc => ValidPartialValue.borrow hmem hloc
  | box hslot hinner => ValidPartialValue.box hslot hinner.valid
  | boxFull hslot hinner => ValidPartialValue.boxFull hslot hinner.valid

theorem ValidPartialValueEvidence.exists_of_valid {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValue store value ty →
    ∃ _evidence : ValidPartialValueEvidence store value ty, True := by
  intro hvalid
  induction hvalid with
  | unit => exact ⟨ValidPartialValueEvidence.unit, trivial⟩
  | int => exact ⟨ValidPartialValueEvidence.int, trivial⟩
  | bool => exact ⟨ValidPartialValueEvidence.bool, trivial⟩
  | undef => exact ⟨ValidPartialValueEvidence.undef, trivial⟩
  | borrow hmem hloc =>
      exact ⟨ValidPartialValueEvidence.borrow _ hmem hloc, trivial⟩
  | box hslot _hinner ih =>
      rcases ih with ⟨innerEvidence, _⟩
      exact ⟨ValidPartialValueEvidence.box hslot innerEvidence, trivial⟩
  | boxFull hslot _hinner ih =>
      rcases ih with ⟨innerEvidence, _⟩
      exact ⟨ValidPartialValueEvidence.boxFull hslot innerEvidence, trivial⟩

inductive ValidPartialValueEvidence.StrengthensSameShape
    {store : ProgramStore} :
    {value : PartialValue} → {oldTy : PartialTy} →
      ValidPartialValueEvidence store value oldTy →
      {newTy : PartialTy} →
      ValidPartialValueEvidence store value newTy → Prop where
  | unit :
      StrengthensSameShape ValidPartialValueEvidence.unit
        ValidPartialValueEvidence.unit
  | int {value : Int} :
      StrengthensSameShape
        (ValidPartialValueEvidence.int (value := value))
        ValidPartialValueEvidence.int
  | bool {value : Bool} :
      StrengthensSameShape
        (ValidPartialValueEvidence.bool (value := value))
        ValidPartialValueEvidence.bool
  | undef {oldTy newTy : Ty} :
      StrengthensSameShape
        (ValidPartialValueEvidence.undef (ty := oldTy))
        (ValidPartialValueEvidence.undef (ty := newTy))
  | borrow {location : Location} {oldMutable newMutable : Bool}
      {leftTargets rightTargets : List LVal}
      {target : LVal} {hmem : target ∈ leftTargets}
      {hloc : store.loc target = some location}
      (hmutable : oldMutable = newMutable)
      (hsubset : leftTargets.Subset rightTargets) :
      StrengthensSameShape
        (ValidPartialValueEvidence.borrow (mutable := oldMutable)
          target hmem hloc)
        (ValidPartialValueEvidence.borrow (mutable := newMutable)
          target (hsubset hmem) hloc)
  | box {location : Location} {slot : StoreSlot}
      {oldInner newInner : PartialTy}
      {oldEvidence : ValidPartialValueEvidence store slot.value oldInner}
      {newEvidence : ValidPartialValueEvidence store slot.value newInner}
      {hslot : store.slotAt location = some slot} :
      StrengthensSameShape oldEvidence newEvidence →
      StrengthensSameShape
        (ValidPartialValueEvidence.box hslot oldEvidence)
        (ValidPartialValueEvidence.box hslot newEvidence)
  | boxFull {location : Location} {slot : StoreSlot}
      {oldInner newInner : Ty}
      {oldEvidence : ValidPartialValueEvidence store slot.value (.ty oldInner)}
      {newEvidence : ValidPartialValueEvidence store slot.value (.ty newInner)}
      {hslot : store.slotAt location = some slot} :
      StrengthensSameShape oldEvidence newEvidence →
      StrengthensSameShape
        (ValidPartialValueEvidence.boxFull hslot oldEvidence)
        (ValidPartialValueEvidence.boxFull hslot newEvidence)

theorem ValidPartialValueEvidence.StrengthensSameShape.refl
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy}
    (evidence : ValidPartialValueEvidence store value ty) :
    ValidPartialValueEvidence.StrengthensSameShape evidence evidence := by
  induction evidence with
  | unit => exact ValidPartialValueEvidence.StrengthensSameShape.unit
  | int => exact ValidPartialValueEvidence.StrengthensSameShape.int
  | bool => exact ValidPartialValueEvidence.StrengthensSameShape.bool
  | undef => exact ValidPartialValueEvidence.StrengthensSameShape.undef
  | @borrow location mutable targets target hmem hloc =>
      exact ValidPartialValueEvidence.StrengthensSameShape.borrow
        (oldMutable := mutable) (newMutable := mutable)
        (target := target) (hmem := hmem) (hloc := hloc)
        rfl (List.Subset.refl _)
  | box hslot hinner ih =>
      exact ValidPartialValueEvidence.StrengthensSameShape.box ih
  | boxFull hslot hinner ih =>
      exact ValidPartialValueEvidence.StrengthensSameShape.boxFull ih

theorem ValidPartialValueEvidence.strengthen_sameShape_exists
    {store : ProgramStore} {value : PartialValue}
    {oldTy newTy : PartialTy}
    (evidence : ValidPartialValueEvidence store value oldTy)
    (hstrength : PartialTyStrengthens oldTy newTy)
    (hshape : PartialTy.sameShape oldTy newTy) :
    ∃ newEvidence : ValidPartialValueEvidence store value newTy,
      ValidPartialValueEvidence.StrengthensSameShape evidence newEvidence := by
  induction evidence generalizing newTy with
  | unit =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.unit,
            ValidPartialValueEvidence.StrengthensSameShape.unit⟩
      | intoUndef _ => simp [PartialTy.sameShape] at hshape
  | int =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.int,
            ValidPartialValueEvidence.StrengthensSameShape.int⟩
      | intoUndef _ => simp [PartialTy.sameShape] at hshape
  | bool =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.bool,
            ValidPartialValueEvidence.StrengthensSameShape.bool⟩
      | intoUndef _ => simp [PartialTy.sameShape] at hshape
  | undef =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.undef,
            ValidPartialValueEvidence.StrengthensSameShape.undef⟩
      | undefLeft _ =>
          exact ⟨ValidPartialValueEvidence.undef,
            ValidPartialValueEvidence.StrengthensSameShape.undef⟩
  | @borrow location mutable targets target hmem hloc =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.borrow target hmem hloc,
            ValidPartialValueEvidence.StrengthensSameShape.borrow
              (oldMutable := mutable) (newMutable := mutable)
              (target := target) (hmem := hmem) (hloc := hloc)
              rfl (List.Subset.refl _)⟩
      | borrow hsubset =>
          exact ⟨ValidPartialValueEvidence.borrow target (hsubset hmem) hloc,
            ValidPartialValueEvidence.StrengthensSameShape.borrow
              (oldMutable := mutable) (newMutable := mutable)
              (target := target) (hmem := hmem) (hloc := hloc)
              rfl hsubset⟩
      | intoUndef _ => simp [PartialTy.sameShape] at hshape
  | box hslot hinner ih =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.box hslot hinner,
            ValidPartialValueEvidence.StrengthensSameShape.box
              (ValidPartialValueEvidence.StrengthensSameShape.refl hinner)⟩
      | box hinnerStrength =>
          rcases ih hinnerStrength
              (by simpa [PartialTy.sameShape] using hshape) with
            ⟨newEvidence, hrel⟩
          exact ⟨ValidPartialValueEvidence.box hslot newEvidence,
            ValidPartialValueEvidence.StrengthensSameShape.box hrel⟩
      | boxIntoUndef _ => simp [PartialTy.sameShape] at hshape
  | boxFull hslot hinner ih =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.boxFull hslot hinner,
            ValidPartialValueEvidence.StrengthensSameShape.boxFull
              (ValidPartialValueEvidence.StrengthensSameShape.refl hinner)⟩
      | tyBox hinnerStrength =>
          rcases ih hinnerStrength
              (by simpa [PartialTy.sameShape, Ty.sameShape] using hshape) with
            ⟨newEvidence, hrel⟩
          exact ⟨ValidPartialValueEvidence.boxFull hslot newEvidence,
            ValidPartialValueEvidence.StrengthensSameShape.boxFull hrel⟩
      | intoUndef _ => simp [PartialTy.sameShape] at hshape

inductive EvidenceBorrowDependency (store : ProgramStore) :
    {value : PartialValue} → {ty : PartialTy} →
      ValidPartialValueEvidence store value ty → Location → Prop where
  | borrow {location : Location} {mutable : Bool} {targets : List LVal}
      {target : LVal} {hmem : target ∈ targets}
      {hloc : store.loc target = some location} {dependency : Location} :
      LocReads store target dependency →
      EvidenceBorrowDependency store
        (ValidPartialValueEvidence.borrow target hmem hloc)
        dependency
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {hslot : store.slotAt location = some slot}
      {hinner : ValidPartialValueEvidence store slot.value inner}
      {dependency : Location} :
      EvidenceBorrowDependency store hinner dependency →
      EvidenceBorrowDependency store (ValidPartialValueEvidence.box hslot hinner)
        dependency
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {hslot : store.slotAt location = some slot}
      {hinner : ValidPartialValueEvidence store slot.value (.ty ty)}
      {dependency : Location} :
      EvidenceBorrowDependency store hinner dependency →
      EvidenceBorrowDependency store (ValidPartialValueEvidence.boxFull hslot hinner)
        dependency

theorem EvidenceBorrowDependency.selected {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : ValidPartialValueEvidence store value ty} {dependency : Location} :
    EvidenceBorrowDependency store evidence dependency →
    SelectedBorrowDependency store evidence.valid dependency := by
  intro hdependency
  induction hdependency with
  | @borrow _ location mutable targets target hmem hloc dependency hreads =>
      exact SelectedBorrowDependency.borrow (mutable := mutable)
        (target := target) (hmem := hmem) (hloc := hloc) hreads
  | @boxInner location slot inner hslot hinner dependency _hdependency ih =>
      exact SelectedBorrowDependency.boxInner (hslot := hslot) ih
  | @boxFullInner location slot innerTy hslot hinner dependency _hdependency ih =>
      exact SelectedBorrowDependency.boxFullInner (hslot := hslot) ih

theorem SelectedBorrowDependency.evidenceBorrowDependency {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {hvalid : ValidPartialValue store value ty} {dependency : Location} :
    SelectedBorrowDependency store hvalid dependency →
    ∃ evidence : ValidPartialValueEvidence store value ty,
      EvidenceBorrowDependency store evidence dependency := by
  intro hdependency
  induction hdependency with
  | @borrow selectedMutable location _mutable targets target hmem hloc
      dependency hreads =>
      exact ⟨ValidPartialValueEvidence.borrow (mutable := selectedMutable)
        target hmem hloc,
        EvidenceBorrowDependency.borrow (mutable := selectedMutable) hreads⟩
  | @boxInner location slot inner hslot hinner dependency _hdependency ih =>
      rcases ih with ⟨innerEvidence, hinnerDependency⟩
      exact ⟨ValidPartialValueEvidence.box hslot innerEvidence,
        EvidenceBorrowDependency.boxInner hinnerDependency⟩
  | @boxFullInner location slot innerTy hslot hinner dependency _hdependency ih =>
      rcases ih with ⟨innerEvidence, hinnerDependency⟩
      exact ⟨ValidPartialValueEvidence.boxFull hslot innerEvidence,
        EvidenceBorrowDependency.boxFullInner hinnerDependency⟩

theorem EvidenceBorrowDependency.of_strengthensSameShape
    {store : ProgramStore} {value : PartialValue}
    {oldTy newTy : PartialTy}
    {oldEvidence : ValidPartialValueEvidence store value oldTy}
    {newEvidence : ValidPartialValueEvidence store value newTy}
    {dependency : Location} :
    ValidPartialValueEvidence.StrengthensSameShape oldEvidence newEvidence →
    EvidenceBorrowDependency store newEvidence dependency →
    EvidenceBorrowDependency store oldEvidence dependency := by
  intro hrel hdependency
  induction hrel with
  | unit => exact hdependency
  | int => exact hdependency
  | bool => exact hdependency
  | undef => cases hdependency
  | @borrow location oldMutable _newMutable leftTargets _rightTargets target
      hmem hloc hmutable _hsubset =>
      cases hmutable
      cases hdependency with
      | borrow hreads =>
          exact EvidenceBorrowDependency.borrow (mutable := oldMutable)
            (target := target) (hmem := hmem) (hloc := hloc) hreads
  | box hinnerRel ih =>
      cases hdependency with
      | boxInner hinnerDependency =>
          exact EvidenceBorrowDependency.boxInner (ih hinnerDependency)
  | boxFull hinnerRel ih =>
      cases hdependency with
      | boxFullInner hinnerDependency =>
          exact EvidenceBorrowDependency.boxFullInner (ih hinnerDependency)

/--
A borrow node selected by proof-carrying runtime evidence.

This is the runtime analogue of `PartialTyContains ty (.borrow mutable targets)`
plus a target membership proof.  Because it is indexed by
`ValidPartialValueEvidence` rather than `ValidPartialValue`, the selected target
is data, not a proof-irrelevant artifact.
-/
def EvidenceSelectedBorrow (store : ProgramStore) :
    {value : PartialValue} → {ty : PartialTy} →
      ValidPartialValueEvidence store value ty → Bool → List LVal → LVal →
        Prop
  | _, _, ValidPartialValueEvidence.unit, _, _, _ => False
  | _, _, ValidPartialValueEvidence.int, _, _, _ => False
  | _, _, ValidPartialValueEvidence.bool, _, _, _ => False
  | _, _, ValidPartialValueEvidence.undef, _, _, _ => False
  | _, _, ValidPartialValueEvidence.borrow (mutable := evidenceMutable)
      (targets := evidenceTargets) evidenceTarget _hmem _hloc,
      selectedMutable, selectedTargets, selectedTarget =>
      evidenceMutable = selectedMutable ∧
        evidenceTargets = selectedTargets ∧
        evidenceTarget = selectedTarget
  | _, _, ValidPartialValueEvidence.box _hslot hinner,
      selectedMutable, selectedTargets, selectedTarget =>
      EvidenceSelectedBorrow store hinner selectedMutable selectedTargets
        selectedTarget
  | _, _, ValidPartialValueEvidence.boxFull _hslot hinner,
      selectedMutable, selectedTargets, selectedTarget =>
      EvidenceSelectedBorrow store hinner selectedMutable selectedTargets
        selectedTarget

namespace EvidenceSelectedBorrow

theorem borrow {store : ProgramStore} {location : Location}
    {evidenceMutable selectedMutable : Bool} {targets : List LVal}
    {target : LVal} {hmem : target ∈ targets}
    {hloc : store.loc target = some location} :
    evidenceMutable = selectedMutable →
    EvidenceSelectedBorrow store
      (ValidPartialValueEvidence.borrow (mutable := evidenceMutable)
        (targets := targets) target hmem hloc)
      selectedMutable targets target := by
  intro hmutable
  subst hmutable
  simp [EvidenceSelectedBorrow]

theorem boxInner {store : ProgramStore} {location : Location}
    {slot : StoreSlot} {inner : PartialTy}
    {hslot : store.slotAt location = some slot}
    {hinner : ValidPartialValueEvidence store slot.value inner}
    {mutable : Bool} {targets : List LVal} {target : LVal} :
    EvidenceSelectedBorrow store hinner mutable targets target →
    EvidenceSelectedBorrow store
      (ValidPartialValueEvidence.box hslot hinner) mutable targets target := by
  intro hselected
  simpa [EvidenceSelectedBorrow] using hselected

theorem boxFullInner {store : ProgramStore} {location : Location}
    {slot : StoreSlot} {ty : Ty}
    {hslot : store.slotAt location = some slot}
    {hinner : ValidPartialValueEvidence store slot.value (.ty ty)}
    {mutable : Bool} {targets : List LVal} {target : LVal} :
    EvidenceSelectedBorrow store hinner mutable targets target →
    EvidenceSelectedBorrow store
      (ValidPartialValueEvidence.boxFull hslot hinner) mutable targets
      target := by
  intro hselected
  simpa [EvidenceSelectedBorrow] using hselected

theorem contains {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : ValidPartialValueEvidence store value ty}
    {mutable : Bool} {targets : List LVal} {target : LVal} :
    EvidenceSelectedBorrow store evidence mutable targets target →
    PartialTyContains ty (.borrow mutable targets) ∧ target ∈ targets := by
  intro hselected
  induction evidence with
  | unit =>
      simp [EvidenceSelectedBorrow] at hselected
  | int =>
      simp [EvidenceSelectedBorrow] at hselected
  | bool =>
      simp [EvidenceSelectedBorrow] at hselected
  | undef =>
      simp [EvidenceSelectedBorrow] at hselected
  | borrow evidenceTarget hmem _hloc =>
      simp [EvidenceSelectedBorrow] at hselected
      rcases hselected with ⟨hmutable, htargets, htarget⟩
      cases hmutable
      cases htargets
      cases htarget
      exact ⟨PartialTyContains.here, by assumption⟩
  | box _hslot _hinner ih =>
      exact ⟨PartialTyContains.box (ih hselected).1, (ih hselected).2⟩
  | boxFull _hslot _hinner ih =>
      exact ⟨PartialTyContains.tyBox (ih hselected).1, (ih hselected).2⟩

theorem of_strengthensSameShape {store : ProgramStore}
    {value : PartialValue} {oldTy newTy : PartialTy}
    {oldEvidence : ValidPartialValueEvidence store value oldTy}
    {newEvidence : ValidPartialValueEvidence store value newTy}
    {mutable : Bool} {newTargets : List LVal} {target : LVal} :
    ValidPartialValueEvidence.StrengthensSameShape oldEvidence newEvidence →
    EvidenceSelectedBorrow store newEvidence mutable newTargets target →
    ∃ oldTargets,
      EvidenceSelectedBorrow store oldEvidence mutable oldTargets target := by
  intro hrel hselected
  induction hrel generalizing mutable newTargets target with
  | unit =>
      simp [EvidenceSelectedBorrow] at hselected
  | int =>
      simp [EvidenceSelectedBorrow] at hselected
  | bool =>
      simp [EvidenceSelectedBorrow] at hselected
  | undef =>
      simp [EvidenceSelectedBorrow] at hselected
  | @borrow location oldMutable _newMutable leftTargets _rightTargets
      evidenceTarget hmem hloc hmutableRel _hsubset =>
      simp [EvidenceSelectedBorrow] at hselected
      rcases hselected with ⟨hselectedMutable, htargets, htarget⟩
      cases htargets
      cases htarget
      exact ⟨leftTargets,
        EvidenceSelectedBorrow.borrow (store := store)
          (location := location)
          (targets := leftTargets) (target := evidenceTarget)
          (hmem := hmem) (hloc := hloc)
          (hmutableRel.trans hselectedMutable)⟩
  | box _hinnerRel ih =>
      rcases ih hselected with ⟨oldTargets, holdSelected⟩
      exact ⟨oldTargets, EvidenceSelectedBorrow.boxInner holdSelected⟩
  | boxFull _hinnerRel ih =>
      rcases ih hselected with ⟨oldTargets, holdSelected⟩
      exact ⟨oldTargets, EvidenceSelectedBorrow.boxFullInner holdSelected⟩

end EvidenceSelectedBorrow

theorem EvidenceBorrowDependency.selectedBorrow {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : ValidPartialValueEvidence store value ty}
    {dependency : Location} :
    EvidenceBorrowDependency store evidence dependency →
    ∃ mutable targets target,
      EvidenceSelectedBorrow store evidence mutable targets target ∧
        LocReads store target dependency := by
  intro hdependency
  induction hdependency with
  | borrow hreads =>
      exact ⟨_, _, _, EvidenceSelectedBorrow.borrow rfl, hreads⟩
  | boxInner _hdependency ih =>
      rcases ih with ⟨mutable, targets, target, hselected, hreads⟩
      exact ⟨mutable, targets, target,
        EvidenceSelectedBorrow.boxInner hselected, hreads⟩
  | boxFullInner _hdependency ih =>
      rcases ih with ⟨mutable, targets, target, hselected, hreads⟩
      exact ⟨mutable, targets, target,
        EvidenceSelectedBorrow.boxFullInner hselected, hreads⟩

theorem ValidPartialValueEvidence.borrow_selected {store : ProgramStore}
    {location : Location} {mutable : Bool} {targets : List LVal}
    (evidence : ValidPartialValueEvidence store
      (.value (.ref { location := location, owner := false }))
      (.ty (.borrow mutable targets))) :
    ∃ target,
      EvidenceSelectedBorrow store evidence mutable targets target ∧
        target ∈ targets ∧ store.loc target = some location := by
  cases evidence with
  | borrow target hmem hloc =>
      exact ⟨target, EvidenceSelectedBorrow.borrow rfl, hmem, hloc⟩

/--
Safe abstraction with concrete runtime evidence for each root slot.
-/
def SafeAbstractionEvidence (store : ProgramStore) (env : Env) : Prop :=
  (∀ x,
    (∃ slot, store.slotAt (VariableProjection x) = some slot) ↔
      ∃ slot, env.slotAt x = some slot) ∧
  ∀ x envSlot,
    env.slotAt x = some envSlot →
    ∃ value,
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } ∧
      ∃ _evidence : ValidPartialValueEvidence store value envSlot.ty, True

theorem SafeAbstractionEvidence.safe {store : ProgramStore} {env : Env} :
    SafeAbstractionEvidence store env →
    store ∼ₛ env := by
  intro hsafe
  constructor
  · exact hsafe.1
  · intro x envSlot hslot
    rcases hsafe.2 x envSlot hslot with
    ⟨value, hstore, hevidence, _⟩
    exact ⟨value, hstore, hevidence.valid⟩

theorem SafeAbstractionEvidence.of_safe {store : ProgramStore} {env : Env} :
    store ∼ₛ env →
    SafeAbstractionEvidence store env := by
  intro hsafe
  constructor
  · exact hsafe.1
  · intro x envSlot hslot
    rcases hsafe.2 x envSlot hslot with ⟨value, hstore, hvalid⟩
    rcases ValidPartialValueEvidence.exists_of_valid hvalid with
      ⟨evidence, _⟩
    exact ⟨value, hstore, evidence, trivial⟩

/--
Chosen runtime evidence for roots of an environment.

This provider is intentionally evidence-indexed by the concrete store lookup
proof.  It lets a relaxed preservation proof talk about the borrow target that
the abstraction actually follows, rather than every possible proof of
`ValidPartialValue` for a widened joined type.
-/
def RuntimeEvidenceProvider (store : ProgramStore) (env : Env) : Type :=
  ∀ x envSlot value,
    env.slotAt x = some envSlot →
    store.slotAt (VariableProjection x) =
      some { value := value, lifetime := envSlot.lifetime } →
    ValidPartialValueEvidence store value envSlot.ty

/--
Selected borrow safety for a fixed runtime evidence provider.

This is weaker than `RuntimeSelectedBorrowSafe`: it compares only the selected
borrow nodes exposed by the chosen provider.  That is the invariant expected to
transport through relaxed joins, where the joined static target list may contain
branches that are not followed by the concrete runtime value.
-/
def RuntimeSelectedBorrowSafeWith (store : ProgramStore) (env : Env)
    (evidenceOf : RuntimeEvidenceProvider store env) : Prop :=
  ∀ x y xSlot ySlot xValue yValue
    (hx : env.slotAt x = some xSlot)
    (hy : env.slotAt y = some ySlot)
    (hxStore : store.slotAt (VariableProjection x) =
      some { value := xValue, lifetime := xSlot.lifetime })
    (hyStore : store.slotAt (VariableProjection y) =
      some { value := yValue, lifetime := ySlot.lifetime })
    mutable targetsMutable targetsOther targetMutable targetOther,
      EvidenceSelectedBorrow store
        (evidenceOf x xSlot xValue hx hxStore)
        true targetsMutable targetMutable →
      EvidenceSelectedBorrow store
        (evidenceOf y ySlot yValue hy hyStore)
        mutable targetsOther targetOther →
      targetMutable ⋈ targetOther →
      x = y

/--
Selected-borrow safety for a terminal value against the current environment.

This is the value-level half that assignment needs after its RHS has evaluated:
`RuntimeSafeAbstraction store env` compares selected borrows between stored
environment roots, while this invariant compares the selected borrow carried by
the terminal RHS value with selected borrows in those roots.
-/
def RuntimeValueSelectedBorrowSafeWith (store : ProgramStore) (env : Env)
    (evidenceOf : RuntimeEvidenceProvider store env)
    {value : PartialValue} {ty : PartialTy}
    (valueEvidence : ValidPartialValueEvidence store value ty) : Prop :=
  (∀ y ySlot yValue
    (hy : env.slotAt y = some ySlot)
    (hyStore : store.slotAt (VariableProjection y) =
      some { value := yValue, lifetime := ySlot.lifetime })
    mutable targetsValue targetsOther targetValue targetOther,
      EvidenceSelectedBorrow store valueEvidence true targetsValue targetValue →
      EvidenceSelectedBorrow store
        (evidenceOf y ySlot yValue hy hyStore)
        mutable targetsOther targetOther →
      targetValue ⋈ targetOther →
      False) ∧
  (∀ x xSlot xValue
    (hx : env.slotAt x = some xSlot)
    (hxStore : store.slotAt (VariableProjection x) =
      some { value := xValue, lifetime := xSlot.lifetime })
    mutable targetsMutable targetsValue targetMutable targetValue,
      EvidenceSelectedBorrow store
        (evidenceOf x xSlot xValue hx hxStore)
        true targetsMutable targetMutable →
      EvidenceSelectedBorrow store valueEvidence mutable targetsValue targetValue →
      targetMutable ⋈ targetValue →
      False)

theorem RuntimeValueSelectedBorrowSafeWith.box {store : ProgramStore}
    {env : Env} {evidenceOf : RuntimeEvidenceProvider store env}
    {location : Location} {slot : StoreSlot} {inner : PartialTy}
    {hslot : store.slotAt location = some slot}
    {innerEvidence : ValidPartialValueEvidence store slot.value inner} :
    RuntimeValueSelectedBorrowSafeWith store env evidenceOf innerEvidence →
    RuntimeValueSelectedBorrowSafeWith store env evidenceOf
      (ValidPartialValueEvidence.box hslot innerEvidence) := by
  intro hsafe
  constructor
  · intro y ySlot yValue hy hyStore mutable targetsValue targetsOther
      targetValue targetOther hselectedValue hselectedOther hconflict
    exact hsafe.1 y ySlot yValue hy hyStore mutable targetsValue
      targetsOther targetValue targetOther
      (by simpa [EvidenceSelectedBorrow] using hselectedValue)
      hselectedOther hconflict
  · intro x xSlot xValue hx hxStore mutable targetsMutable targetsValue
      targetMutable targetValue hselectedMutable hselectedValue hconflict
    exact hsafe.2 x xSlot xValue hx hxStore mutable targetsMutable
      targetsValue targetMutable targetValue hselectedMutable
      (by simpa [EvidenceSelectedBorrow] using hselectedValue)
      hconflict

theorem RuntimeValueSelectedBorrowSafeWith.boxFull {store : ProgramStore}
    {env : Env} {evidenceOf : RuntimeEvidenceProvider store env}
    {location : Location} {slot : StoreSlot} {ty : Ty}
    {hslot : store.slotAt location = some slot}
    {innerEvidence : ValidPartialValueEvidence store slot.value (.ty ty)} :
    RuntimeValueSelectedBorrowSafeWith store env evidenceOf innerEvidence →
    RuntimeValueSelectedBorrowSafeWith store env evidenceOf
      (ValidPartialValueEvidence.boxFull hslot innerEvidence) := by
  intro hsafe
  constructor
  · intro y ySlot yValue hy hyStore mutable targetsValue targetsOther
      targetValue targetOther hselectedValue hselectedOther hconflict
    exact hsafe.1 y ySlot yValue hy hyStore mutable targetsValue
      targetsOther targetValue targetOther
      (by simpa [EvidenceSelectedBorrow] using hselectedValue)
      hselectedOther hconflict
  · intro x xSlot xValue hx hxStore mutable targetsMutable targetsValue
      targetMutable targetValue hselectedMutable hselectedValue hconflict
    exact hsafe.2 x xSlot xValue hx hxStore mutable targetsMutable
      targetsValue targetMutable targetValue hselectedMutable
      (by simpa [EvidenceSelectedBorrow] using hselectedValue)
      hconflict

theorem RuntimeValueSelectedBorrowSafeWith.singletonBorrow {store : ProgramStore}
    {env : Env} {evidenceOf : RuntimeEvidenceProvider store env}
    {location : Location} {mutable : Bool} {target : LVal}
    {hloc : store.loc target = some location} :
    (if mutable then ¬ WriteProhibited env target else ¬ ReadProhibited env target) →
    RuntimeValueSelectedBorrowSafeWith store env evidenceOf
      (ValidPartialValueEvidence.borrow (mutable := mutable)
        (targets := [target]) target (by simp) hloc) := by
  intro hnot
  constructor
  · intro y ySlot yValue hy hyStore otherMutable targetsValue targetsOther
      targetValue targetOther hselectedValue hselectedOther hconflict
    simp [EvidenceSelectedBorrow] at hselectedValue
    rcases hselectedValue with ⟨hmutable, htargets, htarget⟩
    cases htargets
    cases htarget
    cases mutable
    · cases hmutable
    · rcases EvidenceSelectedBorrow.contains hselectedOther with
        ⟨hcontainsOther, htargetOther⟩
      have hwrite : WriteProhibited env target := by
        cases otherMutable with
        | false =>
            exact Or.inr ⟨y, targetsOther, targetOther,
              ⟨ySlot, hy, hcontainsOther⟩, htargetOther,
              PathConflicts.symm hconflict⟩
        | true =>
            exact Or.inl ⟨y, targetsOther, targetOther,
              ⟨ySlot, hy, hcontainsOther⟩, htargetOther,
              PathConflicts.symm hconflict⟩
      exact hnot hwrite
  · intro x xSlot xValue hx hxStore valueMutable targetsMutable targetsValue
      targetMutable targetValue hselectedMutable hselectedValue hconflict
    simp [EvidenceSelectedBorrow] at hselectedValue
    rcases hselectedValue with ⟨hvalueMutable, htargets, htarget⟩
    cases htargets
    cases htarget
    rcases EvidenceSelectedBorrow.contains hselectedMutable with
      ⟨hcontainsMutable, htargetMutable⟩
    cases mutable
    · have hread : ReadProhibited env target :=
        ⟨x, targetsMutable, targetMutable,
          ⟨xSlot, hx, hcontainsMutable⟩, htargetMutable, hconflict⟩
      exact hnot hread
    · have hwrite : WriteProhibited env target :=
        Or.inl ⟨x, targetsMutable, targetMutable,
          ⟨xSlot, hx, hcontainsMutable⟩, htargetMutable, hconflict⟩
      exact hnot hwrite

/--
Safe abstraction plus a selected runtime alias invariant for the abstraction's
chosen evidence.
-/
def RuntimeSafeAbstraction (store : ProgramStore) (env : Env) : Prop :=
  SafeAbstractionEvidence store env ∧
    ∃ evidenceOf : RuntimeEvidenceProvider store env,
      RuntimeSelectedBorrowSafeWith store env evidenceOf

theorem runtimeSafeAbstraction_empty :
    RuntimeSafeAbstraction ProgramStore.empty Env.empty := by
  classical
  have hsafeEvidence : SafeAbstractionEvidence ProgramStore.empty Env.empty :=
    SafeAbstractionEvidence.of_safe safeAbstraction_empty
  let evidenceOf : RuntimeEvidenceProvider ProgramStore.empty Env.empty :=
    fun _x _envSlot _value henv _hstore => by
      simp [Env.empty] at henv
  refine ⟨hsafeEvidence, evidenceOf, ?_⟩
  intro _x _y _xSlot _ySlot _xValue _yValue hx _hy _hxStore _hyStore
    _mutable _targetsMutable _targetsOther _targetMutable _targetOther
    _hselectedMutable _hselectedOther _hconflict
  simp [Env.empty] at hx

theorem RuntimeSafeAbstraction.safe {store : ProgramStore} {env : Env} :
    RuntimeSafeAbstraction store env →
    store ∼ₛ env := by
  intro hsafe
  exact SafeAbstractionEvidence.safe hsafe.1

/--
Runtime-selected borrow safety.

This is intentionally weaker than `BorrowSafeEnv`: it compares only borrow
nodes selected by concrete runtime evidence for root slots.  Static target-list
alternatives introduced by relaxed joins do not participate unless they are the
target actually witnessing a runtime reference.
-/
def RuntimeSelectedBorrowSafe (store : ProgramStore) (env : Env) : Prop :=
  ∀ x y xSlot ySlot xValue yValue,
    env.slotAt x = some xSlot →
    env.slotAt y = some ySlot →
    store.slotAt (VariableProjection x) =
      some { value := xValue, lifetime := xSlot.lifetime } →
    store.slotAt (VariableProjection y) =
      some { value := yValue, lifetime := ySlot.lifetime } →
    ∀ (xEvidence : ValidPartialValueEvidence store xValue xSlot.ty)
      (yEvidence : ValidPartialValueEvidence store yValue ySlot.ty)
      mutable targetsMutable targetsOther targetMutable targetOther,
      EvidenceSelectedBorrow store xEvidence true targetsMutable targetMutable →
      EvidenceSelectedBorrow store yEvidence mutable targetsOther targetOther →
      targetMutable ⋈ targetOther →
      x = y

theorem RuntimeSelectedBorrowSafe.withProvider {store : ProgramStore} {env : Env}
    {evidenceOf : RuntimeEvidenceProvider store env} :
    RuntimeSelectedBorrowSafe store env →
    RuntimeSelectedBorrowSafeWith store env evidenceOf := by
  intro hsafe
  intro x y xSlot ySlot xValue yValue hx hy hxStore hyStore mutable
    targetsMutable targetsOther targetMutable targetOther hselectedMutable
    hselectedOther hconflict
  exact hsafe x y xSlot ySlot xValue yValue hx hy hxStore hyStore
    (evidenceOf x xSlot xValue hx hxStore)
    (evidenceOf y ySlot yValue hy hyStore)
    mutable targetsMutable targetsOther targetMutable targetOther
    hselectedMutable hselectedOther hconflict

theorem RuntimeSafeAbstraction.of_safeEvidence_and_selectedSafe
    {store : ProgramStore} {env : Env} :
    SafeAbstractionEvidence store env →
    RuntimeSelectedBorrowSafe store env →
    RuntimeSafeAbstraction store env := by
  classical
  intro hsafeEvidence hselectedSafe
  let evidenceOf : RuntimeEvidenceProvider store env :=
    fun x envSlot value henvSlot hstoreSlot =>
      let chosenValue := Classical.choose (hsafeEvidence.2 x envSlot henvSlot)
      have hchosenSpec :=
        Classical.choose_spec (hsafeEvidence.2 x envSlot henvSlot)
      let chosenEvidence := Classical.choose hchosenSpec.2
      have hchosenStore :
          store.slotAt (VariableProjection x) =
            some { value := chosenValue, lifetime := envSlot.lifetime } :=
        hchosenSpec.1
      have hvalueEq : chosenValue = value := by
        have hslotEq :
            { value := chosenValue, lifetime := envSlot.lifetime } =
              ({ value := value, lifetime := envSlot.lifetime } : StoreSlot) :=
          Option.some.inj (hchosenStore.symm.trans hstoreSlot)
        exact congrArg StoreSlot.value hslotEq
      by
        subst hvalueEq
        exact chosenEvidence
  exact ⟨hsafeEvidence, evidenceOf,
    RuntimeSelectedBorrowSafe.withProvider hselectedSafe⟩

theorem RuntimeSelectedBorrowSafe.of_borrowSafeEnv {store : ProgramStore}
    {env : Env} :
    BorrowSafeEnv env →
    RuntimeSelectedBorrowSafe store env := by
  intro hborrowSafe
  intro x y xSlot ySlot xValue yValue hx hy _hxStore _hyStore
    xEvidence yEvidence mutable targetsMutable targetsOther targetMutable
    targetOther hselectedMutable hselectedOther hconflict
  rcases EvidenceSelectedBorrow.contains hselectedMutable with
    ⟨hcontainsMutable, hmemMutable⟩
  rcases EvidenceSelectedBorrow.contains hselectedOther with
    ⟨hcontainsOther, hmemOther⟩
  exact hborrowSafe x y mutable targetsMutable targetsOther targetMutable
    targetOther ⟨xSlot, hx, hcontainsMutable⟩
    ⟨ySlot, hy, hcontainsOther⟩ hmemMutable hmemOther hconflict

/-- Frame lemma for `ValidPartialValue`: updating an uninspected location preserves validity. -/
theorem validPartialValue_update_of_not_reaches {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValue store v ty →
      (∀ ℓ, Reaches store v ty ℓ → ℓ ≠ updated) →
      ValidPartialValue (store.update updated newSlot) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit => intro _; exact ValidPartialValue.unit
  | int => intro _; exact ValidPartialValue.int
  | bool => intro _; exact ValidPartialValue.bool
  | undef => intro _; exact ValidPartialValue.undef
  | borrow hmem hloc =>
      intro hreach
      refine ValidPartialValue.borrow hmem ?_
      refine loc_update_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hmem hloc hmidReads)
  | @box location slot inner hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated := hreach location (Reaches.boxHere hslot)
      refine ValidPartialValue.box
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated := hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxFullInner hslot hℓ))

/--
Evidence-indexed frame lemma for store updates.

If the update avoids all owned locations and all borrow-resolution dependencies
recorded by the concrete evidence, validity survives the update with a
post-update evidence object.  The second component maps every dependency of the
new evidence back to the old evidence, so runtime environment abstractions can
transport their protected-dependency invariant through the write.
-/
theorem validPartialValueEvidence_update_of_owner_and_evidence_dependency_frame
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot} :
    ∀ {value : PartialValue} {ty : PartialTy}
      (evidence : ValidPartialValueEvidence store value ty),
      (∀ location,
        OwnerReaches store value ty location →
        location ≠ updated) →
      (∀ location,
        EvidenceBorrowDependency store evidence location →
        location ≠ updated) →
      ∃ evidence' :
        ValidPartialValueEvidence (store.update updated newSlot) value ty,
        (∀ location,
          EvidenceBorrowDependency (store.update updated newSlot) evidence' location →
          EvidenceBorrowDependency store evidence location) ∧
        (∀ mutable targets target,
          EvidenceSelectedBorrow (store.update updated newSlot) evidence'
            mutable targets target →
          EvidenceSelectedBorrow store evidence mutable targets target) := by
  intro value ty evidence
  induction evidence with
  | unit =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.unit, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | int =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.int, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | bool =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.bool, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | undef =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.undef, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | @borrow location mutable targets target hmem hloc =>
      intro _howners hdeps
      have hloc' : (store.update updated newSlot).loc target = some location :=
        loc_update_of_not_locReads hloc (by
          intro dependency hreads
          exact hdeps dependency
            (EvidenceBorrowDependency.borrow
              (store := store) (location := location) (mutable := mutable)
              (targets := targets) (target := target)
              (hmem := hmem) (hloc := hloc) hreads))
      refine ⟨ValidPartialValueEvidence.borrow target hmem hloc', ?_⟩
      constructor
      · intro dependency hdependency
        cases hdependency with
        | borrow hreads =>
            exact EvidenceBorrowDependency.borrow
              (store := store) (location := location) (mutable := mutable)
              (targets := targets) (target := target)
              (hmem := hmem) (hloc := hloc)
              (locReads_update_to_store_of_not_locReads hloc
                (by
                  intro mid hmid
                  exact hdeps mid
                    (EvidenceBorrowDependency.borrow
                      (store := store) (location := location) (mutable := mutable)
                      (targets := targets) (target := target)
                      (hmem := hmem) (hloc := hloc) hmid))
                hreads)
      · intro selectedMutable selectedTargets selectedTarget hselected
        simp [EvidenceSelectedBorrow] at hselected
        rcases hselected with ⟨hmutable, htargets, htarget⟩
        cases htargets
        cases htarget
        exact EvidenceSelectedBorrow.borrow (store := store)
          (location := location) (targets := targets) (target := target)
          (hmem := hmem) (hloc := hloc) hmutable
  | @box location slot inner hslot hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (OwnerReaches.boxHere hslot)
      have hslot' :
          (store.update updated newSlot).slotAt location = some slot := by
        rw [ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      rcases ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (EvidenceBorrowDependency.boxInner
                (store := store) (location := location) (slot := slot)
                (inner := inner) (hslot := hslot) (hinner := hinner)
                hdependency)) with
          ⟨innerEvidence', hinnerDeps, hinnerSelected⟩
      refine ⟨ValidPartialValueEvidence.box hslot' innerEvidence', ?_⟩
      constructor
      · intro dependency hdependency
        cases hdependency with
        | boxInner hdependency' =>
            exact EvidenceBorrowDependency.boxInner
              (store := store) (location := location) (slot := slot)
              (inner := inner) (hslot := hslot) (hinner := hinner)
              (hinnerDeps dependency hdependency')
      · intro mutable targets target hselected
        exact EvidenceSelectedBorrow.boxInner
          (hinnerSelected mutable targets target
            (by simpa [EvidenceSelectedBorrow] using hselected))
  | @boxFull location slot innerTy hslot hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (OwnerReaches.boxFullHere hslot)
      have hslot' :
          (store.update updated newSlot).slotAt location = some slot := by
        rw [ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      rcases ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxFullInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (EvidenceBorrowDependency.boxFullInner
                (store := store) (location := location) (slot := slot)
                (ty := innerTy) (hslot := hslot) (hinner := hinner)
                hdependency)) with
          ⟨innerEvidence', hinnerDeps, hinnerSelected⟩
      refine ⟨ValidPartialValueEvidence.boxFull hslot' innerEvidence', ?_⟩
      constructor
      · intro dependency hdependency
        cases hdependency with
        | boxFullInner hdependency' =>
            exact EvidenceBorrowDependency.boxFullInner
              (store := store) (location := location) (slot := slot)
              (ty := innerTy) (hslot := hslot) (hinner := hinner)
              (hinnerDeps dependency hdependency')
      · intro mutable targets target hselected
        exact EvidenceSelectedBorrow.boxFullInner
          (hinnerSelected mutable targets target
            (by simpa [EvidenceSelectedBorrow] using hselected))

/--
Provider-backed runtime abstraction transport through a framed store update.

This is the update analogue of
`runtimeSafeAbstraction_drops_of_evidence_frames`: the concrete preservation case
supplies the variable-domain/slot facts for the updated store and proves the
write avoids every owned cell and borrow-resolution dependency of each chosen
root evidence object.
-/
theorem runtimeSafeAbstraction_update_of_evidence_frames
    {store : ProgramStore} {env : Env} {updated : Location}
    {newSlot : StoreSlot}
    (_hsafeEvidence : SafeAbstractionEvidence store env)
    (evidenceOf : RuntimeEvidenceProvider store env)
    (hselectedSafe : RuntimeSelectedBorrowSafeWith store env evidenceOf)
    (hdomain :
      ∀ x,
        (∃ slot,
          (store.update updated newSlot).slotAt (VariableProjection x) =
            some slot) ↔
          ∃ slot, env.slotAt x = some slot)
    (hslotOfEnv :
      ∀ x envSlot,
        env.slotAt x = some envSlot →
        ∃ value,
          (store.update updated newSlot).slotAt (VariableProjection x) =
            some { value := value, lifetime := envSlot.lifetime })
    (hstoreBack :
      ∀ x envSlot value,
        env.slotAt x = some envSlot →
        (store.update updated newSlot).slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } →
        store.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime })
    (howners :
      ∀ x envSlot value
        (_henv : env.slotAt x = some envSlot)
        (_hstore :
          store.slotAt (VariableProjection x) =
            some { value := value, lifetime := envSlot.lifetime })
        location,
        OwnerReaches store value envSlot.ty location →
        location ≠ updated)
    (hdeps :
      ∀ x envSlot value
        (henv : env.slotAt x = some envSlot)
        (hstore :
          store.slotAt (VariableProjection x) =
            some { value := value, lifetime := envSlot.lifetime })
        location,
        EvidenceBorrowDependency store
          (evidenceOf x envSlot value henv hstore) location →
        location ≠ updated) :
    RuntimeSafeAbstraction (store.update updated newSlot) env := by
  classical
  have hframe :
      ∀ x envSlot value
        (henv : env.slotAt x = some envSlot)
        (hstore' :
          (store.update updated newSlot).slotAt (VariableProjection x) =
            some { value := value, lifetime := envSlot.lifetime }),
        ∃ evidence' :
          ValidPartialValueEvidence (store.update updated newSlot) value
            envSlot.ty,
          (∀ location,
            EvidenceBorrowDependency (store.update updated newSlot) evidence'
              location →
            EvidenceBorrowDependency store
              (evidenceOf x envSlot value henv
                (hstoreBack x envSlot value henv hstore')) location) ∧
          (∀ mutable targets target,
            EvidenceSelectedBorrow (store.update updated newSlot) evidence'
              mutable targets target →
            EvidenceSelectedBorrow store
              (evidenceOf x envSlot value henv
                (hstoreBack x envSlot value henv hstore'))
              mutable targets target) := by
    intro x envSlot value henv hstore'
    exact validPartialValueEvidence_update_of_owner_and_evidence_dependency_frame
      (evidenceOf x envSlot value henv
        (hstoreBack x envSlot value henv hstore'))
      (howners x envSlot value henv
        (hstoreBack x envSlot value henv hstore'))
      (hdeps x envSlot value henv
        (hstoreBack x envSlot value henv hstore'))
  let finalEvidenceOf :
      RuntimeEvidenceProvider (store.update updated newSlot) env :=
    fun x envSlot value henv hstore' =>
      Classical.choose (hframe x envSlot value henv hstore')
  have hsafeEvidence' :
      SafeAbstractionEvidence (store.update updated newSlot) env := by
    constructor
    · exact hdomain
    · intro x envSlot henv
      rcases hslotOfEnv x envSlot henv with ⟨value, hstore'⟩
      exact ⟨value, hstore', finalEvidenceOf x envSlot value henv hstore',
        trivial⟩
  refine ⟨hsafeEvidence', finalEvidenceOf, ?_⟩
  intro x y xSlot ySlot xValue yValue hx hy hxStore hyStore mutable
    targetsMutable targetsOther targetMutable targetOther hselectedMutable
    hselectedOther hconflict
  have hxStoreOld := hstoreBack x xSlot xValue hx hxStore
  have hyStoreOld := hstoreBack y ySlot yValue hy hyStore
  have hxSpec :=
    Classical.choose_spec (hframe x xSlot xValue hx hxStore)
  have hySpec :=
    Classical.choose_spec (hframe y ySlot yValue hy hyStore)
  have hxSelectedOld :
      EvidenceSelectedBorrow store
        (evidenceOf x xSlot xValue hx hxStoreOld)
        true targetsMutable targetMutable :=
    hxSpec.2 true targetsMutable targetMutable
      (by simpa [finalEvidenceOf] using hselectedMutable)
  have hySelectedOld :
      EvidenceSelectedBorrow store
        (evidenceOf y ySlot yValue hy hyStoreOld)
        mutable targetsOther targetOther :=
    hySpec.2 mutable targetsOther targetOther
      (by simpa [finalEvidenceOf] using hselectedOther)
  exact hselectedSafe x y xSlot ySlot xValue yValue hx hy hxStoreOld
    hyStoreOld mutable targetsMutable targetsOther targetMutable targetOther
    hxSelectedOld hySelectedOld hconflict

/-- Frame lemma for `ValidPartialValue`: erasing an uninspected location preserves validity. -/
theorem validPartialValue_erase_of_not_reaches {store : ProgramStore}
    {erased : Location} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValue store v ty →
      (∀ ℓ, Reaches store v ty ℓ → ℓ ≠ erased) →
      ValidPartialValue (store.erase erased) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit => intro _; exact ValidPartialValue.unit
  | int => intro _; exact ValidPartialValue.int
  | bool => intro _; exact ValidPartialValue.bool
  | undef => intro _; exact ValidPartialValue.undef
  | borrow hmem hloc =>
      intro hreach
      refine ValidPartialValue.borrow hmem ?_
      refine loc_erase_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hmem hloc hmidReads)
  | @box location slot inner hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ erased := hreach location (Reaches.boxHere hslot)
      refine ValidPartialValue.box
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ erased := hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxFullInner hslot hℓ))

/-- Value reachability observed after an erase was already present in the original store. -/
theorem reaches_erase_to_store {store : ProgramStore}
    {erased : Location} {v : PartialValue} {ty : PartialTy} {location : Location} :
    Reaches (store.erase erased) v ty location →
    Reaches store v ty location := by
  intro hreach
  induction hreach with
  | boxHere hslot =>
      exact Reaches.boxHere (slotAt_of_erase_slotAt hslot)
  | boxInner hslot _hinner ih =>
      exact Reaches.boxInner (slotAt_of_erase_slotAt hslot) ih
  | boxFullHere hslot =>
      exact Reaches.boxFullHere (slotAt_of_erase_slotAt hslot)
  | boxFullInner hslot _hinner ih =>
      exact Reaches.boxFullInner (slotAt_of_erase_slotAt hslot) ih
  | borrow hmem hloc hreads =>
      exact Reaches.borrow hmem (loc_erase_some_to_store hloc)
        (locReads_erase_to_store hreads)

/-- Recursive drops preserve validity when they avoid every reached location. -/
theorem validPartialValue_drops_of_avoids_reaches {store store' : ProgramStore}
    {values : List PartialValue} {v : PartialValue} {ty : PartialTy} :
    Drops store values store' →
    ValidPartialValue store v ty →
    (∀ location, Reaches store v ty location →
      DropsAvoids store values location) →
    ValidPartialValue store' v ty := by
  intro hdrops hvalid havoids
  induction hdrops generalizing v ty with
  | nil =>
      exact hvalid
  | nonOwner hnonOwner _hdrops ih =>
      exact ih hvalid (by
        intro location hreach
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner _ hrest => exact hrest
        | ownerMissing howner _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerPresent howner _ _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner))
  | ownerMissing howner hmissing _hdrops ih =>
      exact ih hvalid (by
        intro location hreach
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ _ hrest => exact hrest
        | ownerPresent _ hpresent _ _ =>
            rw [hmissing] at hpresent
            cases hpresent)
  | ownerPresent howner hpresent _hdrops ih =>
      rename_i storeBefore _storeAfter ref erasedSlot rest
      have hnotErased :
          ∀ location, Reaches storeBefore v ty location →
            location ≠ ref.location := by
        intro location hreach hlocation
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ hmissing _ =>
            rw [hpresent] at hmissing
            cases hmissing
        | ownerPresent _ _ hne _ =>
            exact hne hlocation.symm
      have hvalidErased :
          ValidPartialValue (storeBefore.erase ref.location) v ty :=
        validPartialValue_erase_of_not_reaches hvalid hnotErased
      exact ih hvalidErased (by
        intro location hreachErased
        have hreachStore : Reaches storeBefore v ty location :=
          reaches_erase_to_store hreachErased
        have havoid := havoids location hreachStore
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ hmissing _ =>
            rw [hpresent] at hmissing
            cases hmissing
        | ownerPresent _ hpresent' _ hrest =>
            rw [hpresent] at hpresent'
            cases hpresent'
            exact hrest)

/-- `ValidValue` specialization of the store-update frame. -/
theorem validValue_update_of_not_reaches {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} {value : Value} {ty : Ty} :
    ValidValue store value ty →
    (∀ ℓ, Reaches store (.value value) (.ty ty) ℓ → ℓ ≠ updated) →
    ValidValue (store.update updated newSlot) value ty :=
  validPartialValue_update_of_not_reaches

/-- `ValidValue` specialization of the recursive-drop frame. -/
theorem validValue_drops_of_avoids_reaches {store store' : ProgramStore}
    {values : List PartialValue} {value : Value} {ty : Ty} :
    Drops store values store' →
    ValidValue store value ty →
    (∀ location, Reaches store (.value value) (.ty ty) location →
      DropsAvoids store values location) →
    ValidValue store' value ty :=
  validPartialValue_drops_of_avoids_reaches

/--
Drop frame for the exact runtime dependencies recorded by a
`ValidPartialValue` derivation.

The older `validPartialValue_drops_of_avoids_reaches` ranges over every static
borrow target in the type.  This form only asks that the drop avoid owned
locations and the selected borrow-resolution dependencies that the validity
proof actually uses at runtime.
-/
theorem validPartialValue_drops_of_owner_and_selected_dependency_frame
    {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ∀ {value : PartialValue} {ty : PartialTy}
      (hvalid : ValidPartialValue store value ty),
      (∀ location,
        OwnerReaches store value ty location →
        DropsAvoids store values location) →
      (∀ location,
        SelectedBorrowDependency store hvalid location →
        DropsAvoids store values location) →
      ValidPartialValue store' value ty := by
  intro hdrops value ty hvalid
  induction hvalid with
  | unit =>
      intro _howners _hdeps
      exact ValidPartialValue.unit
  | int =>
      intro _howners _hdeps
      exact ValidPartialValue.int
  | bool =>
      intro _howners _hdeps
      exact ValidPartialValue.bool
  | undef =>
      intro _howners _hdeps
      exact ValidPartialValue.undef
  | @borrow location mutable targets target hmem hloc =>
      intro _howners hdeps
      refine ValidPartialValue.borrow hmem ?_
      exact loc_drops_of_not_locReads hdrops hloc (by
        intro mid hreads
        exact hdeps mid
          (SelectedBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (target := target)
            (hmem := hmem) (hloc := hloc) hreads))
  | @box location slot inner hslot hinner ih =>
      intro howners hdeps
      have hlocationAvoid : DropsAvoids store values location :=
        howners location (OwnerReaches.boxHere hslot)
      refine ValidPartialValue.box (location := location) (slot := slot) ?_ ?_
      · exact dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (SelectedBorrowDependency.boxInner
                (store := store) (location := location) (slot := slot)
                (inner := inner) (hslot := hslot) (hinner := hinner)
                hdependency))
  | @boxFull location slot innerTy hslot hinner ih =>
      intro howners hdeps
      have hlocationAvoid : DropsAvoids store values location :=
        howners location (OwnerReaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull (location := location) (slot := slot) ?_ ?_
      · exact dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxFullInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (SelectedBorrowDependency.boxFullInner
                (store := store) (location := location) (slot := slot)
                (ty := innerTy) (hslot := hslot) (hinner := hinner)
                hdependency))

/--
Evidence-indexed drop frame for runtime validity.

This is the same frame argument as
`validPartialValue_drops_of_owner_and_selected_dependency_frame`, but the
borrow target followed by validity is carried as data in
`ValidPartialValueEvidence`.  This is the form needed by runtime abstractions
that survive same-shape target-list widening.
-/
theorem validPartialValue_drops_of_owner_and_evidence_dependency_frame
    {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ∀ {value : PartialValue} {ty : PartialTy}
      (evidence : ValidPartialValueEvidence store value ty),
      (∀ location,
        OwnerReaches store value ty location →
        DropsAvoids store values location) →
      (∀ location,
        EvidenceBorrowDependency store evidence location →
        DropsAvoids store values location) →
      ValidPartialValue store' value ty := by
  intro hdrops value ty evidence
  induction evidence with
  | unit =>
      intro _howners _hdeps
      exact ValidPartialValue.unit
  | int =>
      intro _howners _hdeps
      exact ValidPartialValue.int
  | bool =>
      intro _howners _hdeps
      exact ValidPartialValue.bool
  | undef =>
      intro _howners _hdeps
      exact ValidPartialValue.undef
  | @borrow location mutable targets target hmem hloc =>
      intro _howners hdeps
      refine ValidPartialValue.borrow hmem ?_
      exact loc_drops_of_not_locReads hdrops hloc (by
        intro mid hreads
        exact hdeps mid
          (EvidenceBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (target := target)
            (hmem := hmem) (hloc := hloc) hreads))
  | @box location slot inner hslot hinner ih =>
      intro howners hdeps
      have hlocationAvoid : DropsAvoids store values location :=
        howners location (OwnerReaches.boxHere hslot)
      refine ValidPartialValue.box (location := location) (slot := slot) ?_ ?_
      · exact dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (EvidenceBorrowDependency.boxInner
                (store := store) (location := location) (slot := slot)
                (inner := inner) (hslot := hslot) (hinner := hinner)
                hdependency))
  | @boxFull location slot innerTy hslot hinner ih =>
      intro howners hdeps
      have hlocationAvoid : DropsAvoids store values location :=
        howners location (OwnerReaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull (location := location) (slot := slot) ?_ ?_
      · exact dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxFullInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (EvidenceBorrowDependency.boxFullInner
                (store := store) (location := location) (slot := slot)
                (ty := innerTy) (hslot := hslot) (hinner := hinner)
                hdependency))

/--
Evidence-indexed drop preservation.

Unlike `validPartialValue_drops_of_owner_and_evidence_dependency_frame`, this
returns a post-drop evidence object and a read-back map for its selected
dependencies.  This is the form needed by runtime environment abstractions:
the abstraction can keep following the same borrow target after the concrete
drop, instead of reconstructing an arbitrary validity proof.
-/
theorem validPartialValueEvidence_drops_of_owner_and_evidence_dependency_frame
    {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ∀ {value : PartialValue} {ty : PartialTy}
      (evidence : ValidPartialValueEvidence store value ty),
      (∀ location,
        OwnerReaches store value ty location →
        DropsAvoids store values location) →
      (∀ location,
        EvidenceBorrowDependency store evidence location →
        DropsAvoids store values location) →
      ∃ evidence' : ValidPartialValueEvidence store' value ty,
        (∀ location,
          EvidenceBorrowDependency store' evidence' location →
          EvidenceBorrowDependency store evidence location) ∧
        (∀ mutable targets target,
          EvidenceSelectedBorrow store' evidence' mutable targets target →
          EvidenceSelectedBorrow store evidence mutable targets target) := by
  intro hdrops value ty evidence
  induction evidence with
  | unit =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.unit, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | int =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.int, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | bool =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.bool, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | undef =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.undef, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | @borrow location mutable targets target hmem hloc =>
      intro _howners hdeps
      have hloc' : store'.loc target = some location :=
        loc_drops_of_not_locReads hdrops hloc (by
          intro dependency hreads
          exact hdeps dependency
            (EvidenceBorrowDependency.borrow
              (store := store) (location := location) (mutable := mutable)
              (targets := targets) (target := target)
              (hmem := hmem) (hloc := hloc) hreads))
      refine ⟨ValidPartialValueEvidence.borrow target hmem hloc', ?_⟩
      constructor
      · intro dependency hdependency
        cases hdependency with
        | borrow hreads =>
            exact EvidenceBorrowDependency.borrow
              (store := store) (location := location) (mutable := mutable)
              (targets := targets) (target := target)
              (hmem := hmem) (hloc := hloc)
              (locReads_drops_to_store hdrops hreads)
      · intro selectedMutable selectedTargets selectedTarget hselected
        simp [EvidenceSelectedBorrow] at hselected
        rcases hselected with ⟨hmutable, htargets, htarget⟩
        cases htargets
        cases htarget
        exact EvidenceSelectedBorrow.borrow (store := store)
          (location := location) (targets := targets) (target := target)
          (hmem := hmem) (hloc := hloc) hmutable
  | @box location slot inner hslot hinner ih =>
      intro howners hdeps
      have hlocationAvoid : DropsAvoids store values location :=
        howners location (OwnerReaches.boxHere hslot)
      have hslot' : store'.slotAt location = some slot :=
        dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      rcases ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (EvidenceBorrowDependency.boxInner
                (store := store) (location := location) (slot := slot)
                (inner := inner) (hslot := hslot) (hinner := hinner)
                hdependency)) with
          ⟨innerEvidence', hinnerDeps, hinnerSelected⟩
      refine ⟨ValidPartialValueEvidence.box hslot' innerEvidence', ?_⟩
      constructor
      · intro dependency hdependency
        cases hdependency with
        | boxInner hdependency' =>
            exact EvidenceBorrowDependency.boxInner
              (store := store) (location := location) (slot := slot)
              (inner := inner) (hslot := hslot) (hinner := hinner)
              (hinnerDeps dependency hdependency')
      · intro mutable targets target hselected
        exact EvidenceSelectedBorrow.boxInner
          (hinnerSelected mutable targets target
            (by simpa [EvidenceSelectedBorrow] using hselected))
  | @boxFull location slot innerTy hslot hinner ih =>
      intro howners hdeps
      have hlocationAvoid : DropsAvoids store values location :=
        howners location (OwnerReaches.boxFullHere hslot)
      have hslot' : store'.slotAt location = some slot :=
        dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      rcases ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxFullInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (EvidenceBorrowDependency.boxFullInner
                (store := store) (location := location) (slot := slot)
                (ty := innerTy) (hslot := hslot) (hinner := hinner)
                hdependency)) with
          ⟨innerEvidence', hinnerDeps, hinnerSelected⟩
      refine ⟨ValidPartialValueEvidence.boxFull hslot' innerEvidence', ?_⟩
      constructor
      · intro dependency hdependency
        cases hdependency with
        | boxFullInner hdependency' =>
            exact EvidenceBorrowDependency.boxFullInner
              (store := store) (location := location) (slot := slot)
              (ty := innerTy) (hslot := hslot) (hinner := hinner)
              (hinnerDeps dependency hdependency')
      · intro mutable targets target hselected
        exact EvidenceSelectedBorrow.boxFullInner
          (hinnerSelected mutable targets target
            (by simpa [EvidenceSelectedBorrow] using hselected))

/--
Provider-backed runtime abstraction transport through recursive drops.

The premises expose exactly the store-side facts a concrete preservation case
must prove: surviving variable slots still line up with the environment, every
root slot in the final store comes from the old store, and the drop avoids all
owned cells and borrow-resolution dependencies of the chosen root evidence.
The selected-borrow invariant is transported with the selected back-map returned
by `validPartialValueEvidence_drops_of_owner_and_evidence_dependency_frame`.
-/
theorem runtimeSafeAbstraction_drops_of_evidence_frames
    {store store' : ProgramStore} {env : Env} {values : List PartialValue}
    (_hsafeEvidence : SafeAbstractionEvidence store env)
    (evidenceOf : RuntimeEvidenceProvider store env)
    (hselectedSafe : RuntimeSelectedBorrowSafeWith store env evidenceOf)
    (hdrops : Drops store values store')
    (hdomain :
      ∀ x,
        (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
          ∃ slot, env.slotAt x = some slot)
    (hslotOfEnv :
      ∀ x envSlot,
        env.slotAt x = some envSlot →
        ∃ value,
          store'.slotAt (VariableProjection x) =
            some { value := value, lifetime := envSlot.lifetime })
    (hstoreBack :
      ∀ x envSlot value,
        env.slotAt x = some envSlot →
        store'.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } →
        store.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime })
    (howners :
      ∀ x envSlot value
        (_henv : env.slotAt x = some envSlot)
        (_hstore :
          store.slotAt (VariableProjection x) =
            some { value := value, lifetime := envSlot.lifetime })
        location,
        OwnerReaches store value envSlot.ty location →
        DropsAvoids store values location)
    (hdeps :
      ∀ x envSlot value
        (henv : env.slotAt x = some envSlot)
        (hstore :
          store.slotAt (VariableProjection x) =
            some { value := value, lifetime := envSlot.lifetime })
        location,
        EvidenceBorrowDependency store
          (evidenceOf x envSlot value henv hstore) location →
        DropsAvoids store values location) :
    RuntimeSafeAbstraction store' env := by
  classical
  have hframe :
      ∀ x envSlot value
        (henv : env.slotAt x = some envSlot)
        (hstore' :
          store'.slotAt (VariableProjection x) =
            some { value := value, lifetime := envSlot.lifetime }),
        ∃ evidence' : ValidPartialValueEvidence store' value envSlot.ty,
          (∀ location,
            EvidenceBorrowDependency store' evidence' location →
            EvidenceBorrowDependency store
              (evidenceOf x envSlot value henv
                (hstoreBack x envSlot value henv hstore')) location) ∧
          (∀ mutable targets target,
            EvidenceSelectedBorrow store' evidence' mutable targets target →
            EvidenceSelectedBorrow store
              (evidenceOf x envSlot value henv
                (hstoreBack x envSlot value henv hstore'))
              mutable targets target) := by
    intro x envSlot value henv hstore'
    exact validPartialValueEvidence_drops_of_owner_and_evidence_dependency_frame
      hdrops
      (evidenceOf x envSlot value henv
        (hstoreBack x envSlot value henv hstore'))
      (howners x envSlot value henv
        (hstoreBack x envSlot value henv hstore'))
      (hdeps x envSlot value henv
        (hstoreBack x envSlot value henv hstore'))
  let finalEvidenceOf : RuntimeEvidenceProvider store' env :=
    fun x envSlot value henv hstore' =>
      Classical.choose (hframe x envSlot value henv hstore')
  have hsafeEvidence' : SafeAbstractionEvidence store' env := by
    constructor
    · exact hdomain
    · intro x envSlot henv
      rcases hslotOfEnv x envSlot henv with ⟨value, hstore'⟩
      exact ⟨value, hstore', finalEvidenceOf x envSlot value henv hstore',
        trivial⟩
  refine ⟨hsafeEvidence', finalEvidenceOf, ?_⟩
  intro x y xSlot ySlot xValue yValue hx hy hxStore hyStore mutable
    targetsMutable targetsOther targetMutable targetOther hselectedMutable
    hselectedOther hconflict
  have hxStoreOld := hstoreBack x xSlot xValue hx hxStore
  have hyStoreOld := hstoreBack y ySlot yValue hy hyStore
  have hxSpec :=
    Classical.choose_spec (hframe x xSlot xValue hx hxStore)
  have hySpec :=
    Classical.choose_spec (hframe y ySlot yValue hy hyStore)
  have hxSelectedOld :
      EvidenceSelectedBorrow store
        (evidenceOf x xSlot xValue hx hxStoreOld)
        true targetsMutable targetMutable :=
    hxSpec.2 true targetsMutable targetMutable
      (by simpa [finalEvidenceOf] using hselectedMutable)
  have hySelectedOld :
      EvidenceSelectedBorrow store
        (evidenceOf y ySlot yValue hy hyStoreOld)
        mutable targetsOther targetOther :=
    hySpec.2 mutable targetsOther targetOther
      (by simpa [finalEvidenceOf] using hselectedOther)
  exact hselectedSafe x y xSlot ySlot xValue yValue hx hy hxStoreOld
    hyStoreOld mutable targetsMutable targetsOther targetMutable targetOther
    hxSelectedOld hySelectedOld hconflict

theorem reaches_owner_source_of_validPartialValue {env : Env}
    {store : ProgramStore} {slotLifetime : Lifetime}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    PartialTyBorrowsWellFormedInSlot env slotLifetime ty →
    ValidPartialValue store value ty →
    OwnerReaches store value ty location →
    location ∈ partialValueOwningLocations value ∨
      ∃ storage,
        OwnerReaches store value ty storage ∧
          ProgramStore.OwnsAt store location storage := by
  intro hborrows hvalid
  induction hvalid generalizing env slotLifetime location with
  | unit =>
      intro hreach
      cases hreach
  | int =>
      intro hreach
      cases hreach
  | bool =>
      intro hreach
      cases hreach
  | undef =>
      intro hreach
      cases hreach
  | borrow _hmem _hloc =>
      intro hreach
      cases hreach
  | @box ownerLocation slot inner hslot _hinner ih =>
      intro hreach
      cases hreach with
      | boxHere _hslot =>
          exact Or.inl (by
            simp [partialValueOwningLocations, valueOwningLocations,
              valueOwnedLocation?])
      | @boxInner _ reachedSlot _ _ hslot' hinnerReach =>
          have hslotEq : reachedSlot = slot := by
            rw [hslot] at hslot'
            injection hslot' with hslotEq
            exact hslotEq.symm
          subst reachedSlot
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.box hcontains)
          rcases ih hinnerBorrows hinnerReach with howned | hsource
          · exact Or.inr ⟨ownerLocation, OwnerReaches.boxHere hslot,
              slot.lifetime, by
                have hslotValue : slot.value = .value (owningRef location) :=
                  eq_owningRef_of_mem_partialValueOwningLocations howned
                cases slot with
                | mk slotValue slotLifetime =>
                    cases hslotValue
                    simpa using hslot⟩
          · rcases hsource with ⟨storage, hstorageReach, howns⟩
            exact Or.inr ⟨storage, OwnerReaches.boxInner hslot hstorageReach, howns⟩
  | @boxFull ownerLocation slot innerTy hslot _hinner ih =>
      intro hreach
      cases hreach with
      | boxFullHere _hslot =>
          exact Or.inl (by
            simp [partialValueOwningLocations, valueOwningLocations,
              valueOwnedLocation?])
      | @boxFullInner _ reachedSlot _ _ hslot' hinnerReach =>
          have hslotEq : reachedSlot = slot := by
            rw [hslot] at hslot'
            injection hslot' with hslotEq
            exact hslotEq.symm
          subst reachedSlot
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty innerTy) := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.tyBox hcontains)
          rcases ih hinnerBorrows hinnerReach with howned | hsource
          · exact Or.inr ⟨ownerLocation, OwnerReaches.boxFullHere hslot,
              slot.lifetime, by
                have hslotValue : slot.value = .value (owningRef location) :=
                  eq_owningRef_of_mem_partialValueOwningLocations howned
                cases slot with
                | mk slotValue slotLifetime =>
                    cases hslotValue
                    simpa using hslot⟩
          · rcases hsource with ⟨storage, hstorageReach, howns⟩
            exact Or.inr ⟨storage, OwnerReaches.boxFullInner hslot hstorageReach, howns⟩

/-- Owner reachability from a value stored at `storage` is a transitive ownership
path rooted at `storage`. -/
theorem ownsTransitively_of_ownerReaches_stored {store : ProgramStore}
    {storage location : Location} {storageLifetime : Lifetime}
    {storedValue : PartialValue} {partialTy : PartialTy} :
    store.slotAt storage =
      some { value := storedValue, lifetime := storageLifetime } →
    OwnerReaches store storedValue partialTy location →
    ProgramStore.OwnsTransitively store storage location := by
  intro hstored hreach
  induction hreach generalizing storage storageLifetime with
  | @boxHere ownerLocation _slot _inner _hslot =>
      exact ProgramStore.OwnsTransitively.direct
        ⟨storageLifetime, by simpa [owningRef] using hstored⟩
  | @boxInner ownerLocation slot inner reached hslot _hinner ih =>
      have hownsRoot : ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨storageLifetime, by simpa [owningRef] using hstored⟩
      exact ProgramStore.OwnsTransitively.trans hownsRoot
        (ih hslot)
  | @boxFullHere ownerLocation _slot _ty _hslot =>
      exact ProgramStore.OwnsTransitively.direct
        ⟨storageLifetime, by simpa [owningRef] using hstored⟩
  | @boxFullInner ownerLocation slot ty reached hslot _hinner ih =>
      have hownsRoot : ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨storageLifetime, by simpa [owningRef] using hstored⟩
      exact ProgramStore.OwnsTransitively.trans hownsRoot
        (ih hslot)

/-- Every location reached from a stored valid value is owned by the store. -/
theorem store_owns_of_reaches_stored_validPartialValue {env : Env}
    {store : ProgramStore} {slotLifetime storageLifetime : Lifetime}
    {storage : Location} {storedValue : PartialValue} {partialTy : PartialTy}
    {location : Location} :
    store.slotAt storage =
      some { value := storedValue, lifetime := storageLifetime } →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    ValidPartialValue store storedValue partialTy →
    OwnerReaches store storedValue partialTy location →
    ProgramStore.Owns store location := by
  intro hstored hborrows hvalid hreach
  rcases reaches_owner_source_of_validPartialValue hborrows hvalid hreach with
    hdirect | hsource
  · have hstoredValue : storedValue = .value (owningRef location) :=
      eq_owningRef_of_mem_partialValueOwningLocations hdirect
    exact ⟨storage, storageLifetime, by
      cases hstoredValue
      simpa [owningRef] using hstored⟩
  · rcases hsource with ⟨sourceStorage, _hsourceReach, howns⟩
    exact ⟨sourceStorage, howns⟩

theorem dropsAvoids_of_reaches_stored_validPartialValue
    {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ValidStore store →
    ∀ {env : Env} {slotLifetime storageLifetime : Lifetime} {storage : Location}
      {storedValue : PartialValue} {partialTy : PartialTy} {location : Location},
      store.slotAt storage =
        some { value := storedValue, lifetime := storageLifetime } →
      PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
        ValidPartialValue store storedValue partialTy →
        DropsAvoids store values storage →
        (∀ reached,
          OwnerReaches store storedValue partialTy reached →
          ∀ dropValue, dropValue ∈ values →
            reached ∉ partialValueOwningLocations dropValue) →
      (∀ dependency,
        BorrowDependency store storedValue partialTy dependency →
          DropsAvoids store values dependency) →
      Reaches store storedValue partialTy location →
      DropsAvoids store values location := by
  intro hdrops hvalidStore env slotLifetime storageLifetime storage storedValue
    partialTy location hstored hborrows hvalid havoidStorage hdisjoint hborrowAvoids hreach
  induction hvalid generalizing env slotLifetime storageLifetime storage location with
  | unit =>
      cases hreach
  | int =>
      cases hreach
  | bool =>
      cases hreach
  | undef =>
      cases hreach
  | @borrow borrowedLocation mutable targets target hmem hloc =>
      cases hreach with
      | @borrow _borrowedLocation readLocation _mutable _targets target' hmem' _hloc' hreads =>
          exact hborrowAvoids _
            (BorrowDependency.borrow hmem' _hloc' hreads)
  | @box ownerLocation slot inner hslot _hinnerValid ih =>
      cases hreach with
      | boxHere hreachSlot =>
          have howns : ProgramStore.OwnsAt store ownerLocation storage :=
            ⟨storageLifetime, hstored⟩
          exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
            havoidStorage (by
              intro dropValue hmem howned
              exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                dropValue hmem howned)
      | @boxInner _ reachSlot _ _ hreachSlot hinnerReach =>
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
              havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                  dropValue hmem howned)
          have hslotEq : reachSlot = slot := by
            rw [hslot] at hreachSlot
            injection hreachSlot with hslotEq
            exact hslotEq.symm
          subst reachSlot
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.box hcontains)
          exact ih
            (env := env) (slotLifetime := slotLifetime)
            (storageLifetime := slot.lifetime)
            (storage := ownerLocation)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hslot)
            hinnerBorrows hrootAvoid
              (by
                intro innerReached hinnerReached dropValue hmem howned
                exact hdisjoint innerReached
                  (OwnerReaches.boxInner hslot hinnerReached) dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependency.boxInner hslot hdependency))
            hinnerReach
  | @boxFull ownerLocation slot innerTy hslot _hinnerValid ih =>
      cases hreach with
      | boxFullHere hreachSlot =>
          have howns : ProgramStore.OwnsAt store ownerLocation storage :=
            ⟨storageLifetime, hstored⟩
          exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
            havoidStorage (by
              intro dropValue hmem howned
              exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                dropValue hmem howned)
      | @boxFullInner _ reachSlot _ _ hreachSlot hinnerReach =>
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
              havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                  dropValue hmem howned)
          have hslotEq : reachSlot = slot := by
            rw [hslot] at hreachSlot
            injection hreachSlot with hslotEq
            exact hslotEq.symm
          subst reachSlot
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty innerTy) := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.tyBox hcontains)
          exact ih
            (env := env) (slotLifetime := slotLifetime)
            (storageLifetime := slot.lifetime)
            (storage := ownerLocation)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hslot)
            hinnerBorrows hrootAvoid
              (by
                intro innerReached hinnerReached dropValue hmem howned
                exact hdisjoint innerReached
                  (OwnerReaches.boxFullInner hslot hinnerReached) dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependency.boxFullInner hslot hdependency))
            hinnerReach

/--
If the direct owners carried by a valid value are disjoint from the store, then
every location reached by the value is protected from a drop list whose explicit
owners are disjoint from that reachability footprint.
-/
theorem dropsAvoids_of_reaches_validPartialValue
    {store store' : ProgramStore} {values : List PartialValue}
    {env : Env} {slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {location : Location} :
    Drops store values store' →
    ValidStore store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
      ValidPartialValue store value partialTy →
      (∀ owned,
        owned ∈ partialValueOwningLocations value →
          ¬ ProgramStore.Owns store owned) →
        (∀ reached,
          OwnerReaches store value partialTy reached →
          ∀ dropValue, dropValue ∈ values →
            reached ∉ partialValueOwningLocations dropValue) →
    (∀ dependency,
      BorrowDependency store value partialTy dependency →
        DropsAvoids store values dependency) →
    Reaches store value partialTy location →
    DropsAvoids store values location := by
  intro hdrops hvalidStore hborrows hvalid hnotStoreOwned hdisjoint hborrowAvoids hreach
  induction hvalid generalizing env slotLifetime location with
  | unit =>
      cases hreach
  | int =>
      cases hreach
  | bool =>
      cases hreach
  | undef =>
      cases hreach
  | @borrow borrowedLocation mutable targets target hmem hloc =>
      cases hreach with
      | @borrow _borrowedLocation readLocation _mutable _targets target' hmem' _hloc' hreads =>
          exact hborrowAvoids _
            (BorrowDependency.borrow hmem' _hloc' hreads)
  | @box ownerLocation slot inner hslot hinnerValid _ih =>
      cases hreach with
      | boxHere hreachSlot =>
          exact dropsAvoids_of_not_owns_and_not_mem hdrops
            (by
              intro dropValue hmem
              exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                dropValue hmem)
            (hnotStoreOwned ownerLocation (by
              simp [partialValueOwningLocations, valueOwningLocations,
                valueOwnedLocation?]))
      | @boxInner _ reachSlot _ _ hreachSlot hinnerReach =>
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                  dropValue hmem)
              (hnotStoreOwned ownerLocation (by
                simp [partialValueOwningLocations, valueOwningLocations,
                  valueOwnedLocation?]))
          have hslotEq : reachSlot = slot := by
            rw [hslot] at hreachSlot
            injection hreachSlot with hslotEq
            exact hslotEq.symm
          subst reachSlot
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.box hcontains)
          exact dropsAvoids_of_reaches_stored_validPartialValue hdrops hvalidStore
            (env := env) (slotLifetime := slotLifetime)
            (storageLifetime := slot.lifetime) (storage := ownerLocation)
            (storedValue := slot.value) (partialTy := inner)
            (location := location)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hslot)
            hinnerBorrows hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxInner hslot hinnerReached) dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependency.boxInner hslot hdependency))
            hinnerReach
  | @boxFull ownerLocation slot innerTy hslot hinnerValid _ih =>
      cases hreach with
      | boxFullHere hreachSlot =>
          exact dropsAvoids_of_not_owns_and_not_mem hdrops
            (by
              intro dropValue hmem
              exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                dropValue hmem)
            (hnotStoreOwned ownerLocation (by
              simp [partialValueOwningLocations, valueOwningLocations,
                valueOwnedLocation?]))
      | @boxFullInner _ reachSlot _ _ hreachSlot hinnerReach =>
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                  dropValue hmem)
              (hnotStoreOwned ownerLocation (by
                simp [partialValueOwningLocations, valueOwningLocations,
                  valueOwnedLocation?]))
          have hslotEq : reachSlot = slot := by
            rw [hslot] at hreachSlot
            injection hreachSlot with hslotEq
            exact hslotEq.symm
          subst reachSlot
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty innerTy) := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.tyBox hcontains)
          exact dropsAvoids_of_reaches_stored_validPartialValue hdrops hvalidStore
            (env := env) (slotLifetime := slotLifetime)
            (storageLifetime := slot.lifetime) (storage := ownerLocation)
            (storedValue := slot.value) (partialTy := .ty innerTy)
            (location := location)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hslot)
            hinnerBorrows hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxFullInner hslot hinnerReached) dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependency.boxFullInner hslot hdependency))
            hinnerReach

end RuntimeFrame

end Paper
end LwRust
