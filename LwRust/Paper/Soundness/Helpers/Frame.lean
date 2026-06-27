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

/-- A resolved lvalue cannot have read a store slot that is fresh. -/
theorem LocReads.ne_fresh_of_loc {store : ProgramStore}
    {updated : Location} {lv : LVal} {location : Location} :
      store.fresh updated →
      store.loc lv = some location →
      LocReads store lv updated →
      False := by
  intro hfresh hloc hread
  induction lv generalizing updated location with
  | var x =>
      cases hread
  | deref lv ih =>
      cases hsource : store.loc lv with
      | none =>
          simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          cases hread with
          | here hsourceRead =>
              have hsourceEq : source = updated := by
                rw [hsource] at hsourceRead
                exact (Option.some.inj hsourceRead)
              have hfreshSource : store.fresh source := by
                simpa [hsourceEq] using hfresh
              cases hslot : store.slotAt source with
              | none =>
                  simp [ProgramStore.loc, hsource, hslot] at hloc
              | some slot =>
                  rw [hfreshSource] at hslot
                  contradiction
          | there hreadSource =>
              exact ih hfresh hsource hreadSource

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
      {pointee : Ty} {target : LVal} :
      target ∈ targets →
      store.loc target = some location →
      LocReads store target ℓ →
      Reaches store (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets pointee)) ℓ

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

/-- Owner reachability cannot end at a fresh store slot. -/
theorem OwnerReaches.ne_fresh {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    store.fresh location →
    OwnerReaches store value ty location →
    False := by
  intro hfresh hreach
  induction hreach with
  | boxHere hslot =>
      rw [hfresh] at hslot
      contradiction
  | boxInner _hslot _hinner ih =>
      exact ih hfresh
  | boxFullHere hslot =>
      rw [hfresh] at hslot
      contradiction
  | boxFullInner _hslot _hinner ih =>
      exact ih hfresh

/-- Borrow-target lval-resolution dependencies inside a value. -/
inductive BorrowDependency (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | borrow {location readLocation : Location} {mutable : Bool}
      {targets : List LVal} {pointee : Ty} {target : LVal} :
      target ∈ targets →
      store.loc target = some location →
      LocReads store target readLocation →
      BorrowDependency store (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets pointee)) readLocation
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
      {pointee : Ty} {target : LVal} {hmem : target ∈ targets}
      {hloc : store.loc target = some location} {dependency : Location} :
      LocReads store target dependency →
      SelectedBorrowDependency store (ValidPartialValue.borrow (pointee := pointee) hmem hloc)
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
  | @borrow _ location mutable targets pointee target hmem hloc dependency hreads =>
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
      {targets : List LVal} {pointee : Ty} (target : LVal) :
      target ∈ targets →
      store.loc target = some location →
      ValidPartialValueEvidence store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets pointee))
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
  | borrow {location : Location} {mutable : Bool} {leftTargets rightTargets : List LVal}
      {pointee : Ty} {target : LVal} {hmem : target ∈ leftTargets}
      {hloc : store.loc target = some location}
      (hsubset : leftTargets.Subset rightTargets) :
      StrengthensSameShape
        (ValidPartialValueEvidence.borrow (pointee := pointee) target hmem hloc)
        (ValidPartialValueEvidence.borrow (pointee := pointee) target
          (hsubset hmem) hloc)
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
  | @borrow location mutable targets pointee target hmem hloc =>
      exact ValidPartialValueEvidence.StrengthensSameShape.borrow
        (mutable := mutable) (pointee := pointee) (target := target)
        (hmem := hmem) (hloc := hloc) (List.Subset.refl _)
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
  | @borrow location mutable targets pointee target hmem hloc =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.borrow target hmem hloc,
            ValidPartialValueEvidence.StrengthensSameShape.borrow
              (mutable := mutable) (pointee := pointee) (target := target)
              (hmem := hmem) (hloc := hloc) (List.Subset.refl _)⟩
      | borrow hsubset =>
          exact ⟨ValidPartialValueEvidence.borrow target (hsubset hmem) hloc,
            ValidPartialValueEvidence.StrengthensSameShape.borrow
              (mutable := mutable) (pointee := pointee) (target := target)
              (hmem := hmem) (hloc := hloc) hsubset⟩
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

/--
Relaxed proof-carrying runtime evidence for abstract slots.

This is the storage-abstraction variant needed at control-flow joins after a
branch initializes storage that the joined environment marks as `undef`.  The
ordinary evidence relation validates `undef T` only against the concrete
`PartialValue.undef`; the relaxed relation additionally permits any value that is
valid at a stronger partial type to be hidden behind an `undef` upper bound.

The `undef` evidence is intentionally lossy: once a slot is abstracted as
`undef`, later frame proofs no longer need to preserve the concrete value's
owner reachability or borrow-resolution dependencies.
-/
inductive RelaxedValidPartialValueEvidence (store : ProgramStore) :
    PartialValue → PartialTy → Type where
  | unit :
      RelaxedValidPartialValueEvidence store (.value .unit) (.ty .unit)
  | int {value : Int} :
      RelaxedValidPartialValueEvidence store (.value (.int value)) (.ty .int)
  | bool {value : Bool} :
      RelaxedValidPartialValueEvidence store (.value (.bool value)) (.ty .bool)
  | undef {value : PartialValue} {ty : Ty} :
      RelaxedValidPartialValueEvidence store value (.undef ty)
  | borrow {location : Location} {mutable : Bool}
      {targets : List LVal} {pointee : Ty} (target : LVal) :
      target ∈ targets →
      store.loc target = some location →
      RelaxedValidPartialValueEvidence store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets pointee))
  | box {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      RelaxedValidPartialValueEvidence store slot.value inner →
      RelaxedValidPartialValueEvidence store
        (.value (.ref { location := location, owner := true }))
        (.box inner)
  | boxFull {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      RelaxedValidPartialValueEvidence store slot.value (.ty ty) →
      RelaxedValidPartialValueEvidence store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty))
  | intoUndef {value : PartialValue} {source : PartialTy} {target : Ty} :
      PartialTyStrengthens source (.undef target) →
      RelaxedValidPartialValueEvidence store value source →
      RelaxedValidPartialValueEvidence store value (.undef target)

inductive RelaxedValidPartialValueEvidence.Strengthens
    {store : ProgramStore} :
    {value : PartialValue} → {oldTy : PartialTy} →
      RelaxedValidPartialValueEvidence store value oldTy →
      {newTy : PartialTy} →
      RelaxedValidPartialValueEvidence store value newTy → Prop where
  | unit :
      Strengthens RelaxedValidPartialValueEvidence.unit
        RelaxedValidPartialValueEvidence.unit
  | int {value : Int} :
      Strengthens
        (RelaxedValidPartialValueEvidence.int (value := value))
        RelaxedValidPartialValueEvidence.int
  | bool {value : Bool} :
      Strengthens
        (RelaxedValidPartialValueEvidence.bool (value := value))
        RelaxedValidPartialValueEvidence.bool
  | undef {value : PartialValue} {ty : Ty} :
      Strengthens
        (RelaxedValidPartialValueEvidence.undef (value := value) (ty := ty))
        RelaxedValidPartialValueEvidence.undef
  | borrow {location : Location} {mutable : Bool}
      {leftTargets rightTargets : List LVal} {pointee : Ty}
      {target : LVal} {hmem : target ∈ leftTargets}
      {hloc : store.loc target = some location}
      (hsubset : leftTargets.Subset rightTargets) :
      Strengthens
        (RelaxedValidPartialValueEvidence.borrow (pointee := pointee)
          target hmem hloc)
        (RelaxedValidPartialValueEvidence.borrow (pointee := pointee)
          target (hsubset hmem) hloc)
  | box {location : Location} {slot : StoreSlot}
      {oldInner newInner : PartialTy}
      {oldEvidence : RelaxedValidPartialValueEvidence store slot.value oldInner}
      {newEvidence : RelaxedValidPartialValueEvidence store slot.value newInner}
      {hslot : store.slotAt location = some slot} :
      Strengthens oldEvidence newEvidence →
      Strengthens
        (RelaxedValidPartialValueEvidence.box hslot oldEvidence)
        (RelaxedValidPartialValueEvidence.box hslot newEvidence)
  | boxFull {location : Location} {slot : StoreSlot}
      {oldInner newInner : Ty}
      {oldEvidence : RelaxedValidPartialValueEvidence store slot.value (.ty oldInner)}
      {newEvidence : RelaxedValidPartialValueEvidence store slot.value (.ty newInner)}
      {hslot : store.slotAt location = some slot} :
      Strengthens oldEvidence newEvidence →
      Strengthens
        (RelaxedValidPartialValueEvidence.boxFull hslot oldEvidence)
        (RelaxedValidPartialValueEvidence.boxFull hslot newEvidence)
  | hide {value : PartialValue} {source : PartialTy} {target : Ty}
      {evidence : RelaxedValidPartialValueEvidence store value source}
      (hstrength : PartialTyStrengthens source (.undef target)) :
    Strengthens evidence
        (RelaxedValidPartialValueEvidence.undef (value := value) (ty := target))
  | discardUndef {value : PartialValue} {sourceTarget target : Ty}
      {evidence : RelaxedValidPartialValueEvidence store value (.undef sourceTarget)}
      (hstrength : PartialTyStrengthens (.undef sourceTarget) (.undef target)) :
      Strengthens evidence
        (RelaxedValidPartialValueEvidence.undef (value := value) (ty := target))
  | hiddenRefl {value : PartialValue} {source : PartialTy} {target : Ty}
      {evidence : RelaxedValidPartialValueEvidence store value source}
      {hstrength : PartialTyStrengthens source (.undef target)} :
      Strengthens
        (RelaxedValidPartialValueEvidence.intoUndef hstrength evidence)
        (RelaxedValidPartialValueEvidence.intoUndef hstrength evidence)
  | hiddenWiden {value : PartialValue} {source : PartialTy}
      {leftTarget rightTarget : Ty}
      {evidence : RelaxedValidPartialValueEvidence store value source}
      (hsource : PartialTyStrengthens source (.undef leftTarget))
      (hwiden : PartialTyStrengthens (.undef leftTarget) (.undef rightTarget)) :
      Strengthens
        (RelaxedValidPartialValueEvidence.intoUndef hsource evidence)
        (RelaxedValidPartialValueEvidence.intoUndef
          (partialTyStrengthens_trans hsource hwiden) evidence)

theorem RelaxedValidPartialValueEvidence.Strengthens.refl
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy}
    (evidence : RelaxedValidPartialValueEvidence store value ty) :
    RelaxedValidPartialValueEvidence.Strengthens evidence evidence := by
  induction evidence with
  | unit => exact RelaxedValidPartialValueEvidence.Strengthens.unit
  | int => exact RelaxedValidPartialValueEvidence.Strengthens.int
  | bool => exact RelaxedValidPartialValueEvidence.Strengthens.bool
  | undef => exact RelaxedValidPartialValueEvidence.Strengthens.undef
  | @borrow location mutable targets pointee target hmem hloc =>
      exact RelaxedValidPartialValueEvidence.Strengthens.borrow
        (mutable := mutable) (pointee := pointee) (target := target)
        (hmem := hmem) (hloc := hloc) (List.Subset.refl _)
  | box hslot _hinner ih =>
      exact RelaxedValidPartialValueEvidence.Strengthens.box ih
  | boxFull hslot _hinner ih =>
      exact RelaxedValidPartialValueEvidence.Strengthens.boxFull ih
  | intoUndef hstrength _hinner _ih =>
      exact RelaxedValidPartialValueEvidence.Strengthens.hiddenRefl
        (hstrength := hstrength)

def RelaxedValidPartialValueEvidence.of_strict {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValueEvidence store value ty →
    RelaxedValidPartialValueEvidence store value ty
  | ValidPartialValueEvidence.unit =>
      RelaxedValidPartialValueEvidence.unit
  | ValidPartialValueEvidence.int =>
      RelaxedValidPartialValueEvidence.int
  | ValidPartialValueEvidence.bool =>
      RelaxedValidPartialValueEvidence.bool
  | ValidPartialValueEvidence.undef =>
      RelaxedValidPartialValueEvidence.undef
  | ValidPartialValueEvidence.borrow target hmem hloc =>
      RelaxedValidPartialValueEvidence.borrow target hmem hloc
  | ValidPartialValueEvidence.box hslot hinner =>
      RelaxedValidPartialValueEvidence.box hslot
        (RelaxedValidPartialValueEvidence.of_strict hinner)
  | ValidPartialValueEvidence.boxFull hslot hinner =>
      RelaxedValidPartialValueEvidence.boxFull hslot
        (RelaxedValidPartialValueEvidence.of_strict hinner)

/--
Partial types whose runtime evidence cannot be hidden behind a top-level
`undef`.

This is the read-facing fragment of partial types: full values are concrete,
and boxed partial values are concrete exactly when their contents are concrete.
The `undef` case is deliberately excluded, since relaxed evidence may hide an
initialized value there.
-/
def PartialTy.Concrete : PartialTy → Prop
  | .ty _ => True
  | .box inner => PartialTy.Concrete inner
  | .undef _ => False

def RelaxedValidPartialValueEvidence.to_strict_full {store : ProgramStore}
    {value : PartialValue} {ty : Ty} :
    RelaxedValidPartialValueEvidence store value (.ty ty) →
    ValidPartialValueEvidence store value (.ty ty)
  | RelaxedValidPartialValueEvidence.unit =>
      ValidPartialValueEvidence.unit
  | RelaxedValidPartialValueEvidence.int =>
      ValidPartialValueEvidence.int
  | RelaxedValidPartialValueEvidence.bool =>
      ValidPartialValueEvidence.bool
  | RelaxedValidPartialValueEvidence.borrow target hmem hloc =>
      ValidPartialValueEvidence.borrow target hmem hloc
  | RelaxedValidPartialValueEvidence.boxFull hslot hinner =>
      ValidPartialValueEvidence.boxFull hslot
        (RelaxedValidPartialValueEvidence.to_strict_full hinner)

def RelaxedValidPartialValueEvidence.to_strict_concrete {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    PartialTy.Concrete ty →
    RelaxedValidPartialValueEvidence store value ty →
    ValidPartialValueEvidence store value ty
  | _hconcrete, RelaxedValidPartialValueEvidence.unit =>
      ValidPartialValueEvidence.unit
  | _hconcrete, RelaxedValidPartialValueEvidence.int =>
      ValidPartialValueEvidence.int
  | _hconcrete, RelaxedValidPartialValueEvidence.bool =>
      ValidPartialValueEvidence.bool
  | hconcrete, RelaxedValidPartialValueEvidence.undef =>
      False.elim hconcrete
  | _hconcrete, RelaxedValidPartialValueEvidence.borrow target hmem hloc =>
      ValidPartialValueEvidence.borrow target hmem hloc
  | hconcrete, RelaxedValidPartialValueEvidence.box hslot hinner =>
      ValidPartialValueEvidence.box hslot
        (RelaxedValidPartialValueEvidence.to_strict_concrete
          hconcrete hinner)
  | _hconcrete, RelaxedValidPartialValueEvidence.boxFull hslot hinner =>
      ValidPartialValueEvidence.boxFull hslot
        (RelaxedValidPartialValueEvidence.to_strict_full hinner)
  | hconcrete, RelaxedValidPartialValueEvidence.intoUndef _hstrength _hinner =>
      False.elim hconcrete

structure RelaxedValidPartialValueEvidence.BoxView
    (store : ProgramStore) (value : PartialValue) (inner : PartialTy) where
  location : Location
  slot : StoreSlot
  value_eq :
    value = .value (.ref { location := location, owner := true })
  slotAt : store.slotAt location = some slot
  innerEvidence : RelaxedValidPartialValueEvidence store slot.value inner

structure RelaxedValidPartialValueEvidence.BorrowView
    (store : ProgramStore) (value : PartialValue) (mutable : Bool)
    (targets : List LVal) (pointee : Ty) where
  location : Location
  target : LVal
  value_eq :
    value = .value (.ref { location := location, owner := false })
  target_mem : target ∈ targets
  target_loc : store.loc target = some location

def RelaxedValidPartialValueEvidence.box_inv {store : ProgramStore}
    {value : PartialValue} {inner : PartialTy} :
    RelaxedValidPartialValueEvidence store value (.box inner) →
    RelaxedValidPartialValueEvidence.BoxView store value inner
  | RelaxedValidPartialValueEvidence.box (location := location)
      (slot := slot) hslot hinner =>
      ⟨location, slot, rfl, hslot, hinner⟩

def RelaxedValidPartialValueEvidence.borrow_inv {store : ProgramStore}
    {value : PartialValue} {mutable : Bool}
    {targets : List LVal} {pointee : Ty} :
    RelaxedValidPartialValueEvidence store value
      (.ty (.borrow mutable targets pointee)) →
    RelaxedValidPartialValueEvidence.BorrowView store value mutable targets pointee
  | RelaxedValidPartialValueEvidence.borrow (location := location)
      target hmem hloc =>
      ⟨location, target, rfl, hmem, hloc⟩

theorem RelaxedValidPartialValueEvidence.strengthen_exists
    {store : ProgramStore} {value : PartialValue}
    {oldTy newTy : PartialTy} :
    (evidence : RelaxedValidPartialValueEvidence store value oldTy) →
    PartialTyStrengthens oldTy newTy →
    ∃ newEvidence : RelaxedValidPartialValueEvidence store value newTy,
      RelaxedValidPartialValueEvidence.Strengthens evidence newEvidence := by
  intro evidence hstrength
  induction evidence generalizing newTy with
  | unit =>
      cases hstrength with
      | reflex =>
          exact ⟨RelaxedValidPartialValueEvidence.unit,
            RelaxedValidPartialValueEvidence.Strengthens.unit⟩
      | intoUndef hinner =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.hide
              (PartialTyStrengthens.intoUndef hinner)⟩
  | int =>
      cases hstrength with
      | reflex =>
          exact ⟨RelaxedValidPartialValueEvidence.int,
            RelaxedValidPartialValueEvidence.Strengthens.int⟩
      | intoUndef hinner =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.hide
              (PartialTyStrengthens.intoUndef hinner)⟩
  | bool =>
      cases hstrength with
      | reflex =>
          exact ⟨RelaxedValidPartialValueEvidence.bool,
            RelaxedValidPartialValueEvidence.Strengthens.bool⟩
      | intoUndef hinner =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.hide
              (PartialTyStrengthens.intoUndef hinner)⟩
  | undef =>
      cases hstrength with
      | reflex =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.undef⟩
      | undefLeft hinner =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.discardUndef
              (PartialTyStrengthens.undefLeft hinner)⟩
  | @borrow location mutable targets pointee target hmem hloc =>
      cases hstrength with
      | reflex =>
          exact ⟨RelaxedValidPartialValueEvidence.borrow target hmem hloc,
            RelaxedValidPartialValueEvidence.Strengthens.borrow
              (mutable := mutable) (leftTargets := targets)
              (rightTargets := targets) (pointee := pointee)
              (target := target) (hmem := hmem) (hloc := hloc)
              (List.Subset.refl _)⟩
      | borrow hsubset =>
          exact ⟨RelaxedValidPartialValueEvidence.borrow target (hsubset hmem) hloc,
            RelaxedValidPartialValueEvidence.Strengthens.borrow
              (mutable := mutable) (leftTargets := targets)
              (pointee := pointee)
              (target := target) (hmem := hmem) (hloc := hloc) hsubset⟩
      | intoUndef hinner =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.hide
              (PartialTyStrengthens.intoUndef hinner)⟩
  | box hslot _hinner ih =>
      cases hstrength with
      | reflex =>
          exact ⟨RelaxedValidPartialValueEvidence.box hslot _hinner,
            RelaxedValidPartialValueEvidence.Strengthens.box
              (RelaxedValidPartialValueEvidence.Strengthens.refl _hinner)⟩
      | box hinnerStrength =>
          rcases ih hinnerStrength with ⟨innerEvidence, hrel⟩
          exact ⟨RelaxedValidPartialValueEvidence.box hslot innerEvidence,
            RelaxedValidPartialValueEvidence.Strengthens.box hrel⟩
      | boxIntoUndef hinnerStrength =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.hide
              (PartialTyStrengthens.boxIntoUndef hinnerStrength)⟩
  | boxFull hslot _hinner ih =>
      cases hstrength with
      | reflex =>
          exact ⟨RelaxedValidPartialValueEvidence.boxFull hslot _hinner,
            RelaxedValidPartialValueEvidence.Strengthens.boxFull
              (RelaxedValidPartialValueEvidence.Strengthens.refl _hinner)⟩
      | tyBox hinnerStrength =>
          rcases ih hinnerStrength with ⟨innerEvidence, hrel⟩
          exact ⟨RelaxedValidPartialValueEvidence.boxFull hslot innerEvidence,
            RelaxedValidPartialValueEvidence.Strengthens.boxFull hrel⟩
      | intoUndef hinnerStrength =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.hide
              (PartialTyStrengthens.intoUndef hinnerStrength)⟩
  | intoUndef hsource _hinner ih =>
      cases hstrength with
      | reflex =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.discardUndef
              PartialTyStrengthens.reflex⟩
      | undefLeft hinnerStrength =>
          exact ⟨RelaxedValidPartialValueEvidence.undef,
            RelaxedValidPartialValueEvidence.Strengthens.discardUndef
              (PartialTyStrengthens.undefLeft hinnerStrength)⟩

/--
Relaxed safe abstraction for store/environment pairs.

This keeps the ordinary variable-domain and lifetime agreement of `S ∼ Γ`, but
uses relaxed evidence for slot values.  Consequently a concrete initialized
value may represent an abstract `undef` slot, as long as the initialized value is
kept as hidden evidence behind the `undef` strengthening.
-/
def RelaxedSafeAbstraction (store : ProgramStore) (env : Env) : Prop :=
  (∀ x, (∃ slot, store.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, env.slotAt x = some envSlot) ∧
  ∀ x envSlot,
    env.slotAt x = some envSlot →
    ∃ value,
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } ∧
      ∃ _evidence : RelaxedValidPartialValueEvidence store value envSlot.ty, True

theorem SafeAbstraction.relaxed {store : ProgramStore} {env : Env} :
    store ∼ₛ env →
    RelaxedSafeAbstraction store env := by
  intro hsafe
  constructor
  · exact hsafe.1
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨value, hstoreSlot, hvalid⟩
    rcases ValidPartialValueEvidence.exists_of_valid hvalid with
      ⟨evidence, _⟩
    exact ⟨value, hstoreSlot,
      RelaxedValidPartialValueEvidence.of_strict evidence, trivial⟩

theorem RelaxedSafeAbstraction.strengthen {store : ProgramStore}
    {source result : Env} :
    RelaxedSafeAbstraction store source →
    EnvStrengthens source result →
    RelaxedSafeAbstraction store result := by
  intro hsafe hstrength
  constructor
  · intro x
    constructor
    · intro hstoreDomain
      rcases (hsafe.1 x).mp hstoreDomain with ⟨sourceSlot, hsourceSlot⟩
      rcases EnvStrengthens.slot_forward hstrength hsourceSlot with
        ⟨resultSlot, hresultSlot, _hlifetime, _hslotStrength⟩
      exact ⟨resultSlot, hresultSlot⟩
    · intro hresultDomain
      rcases hresultDomain with ⟨resultSlot, hresultSlot⟩
      have hx := hstrength x
      cases hsourceSlot : source.slotAt x with
      | none =>
          rw [hsourceSlot, hresultSlot] at hx
          cases hx
      | some sourceSlot =>
          exact (hsafe.1 x).mpr ⟨sourceSlot, hsourceSlot⟩
  · intro x resultSlot hresultSlot
    have hx := hstrength x
    cases hsourceSlot : source.slotAt x with
    | none =>
        rw [hsourceSlot, hresultSlot] at hx
        cases hx
    | some sourceSlot =>
        rw [hsourceSlot, hresultSlot] at hx
        rcases hsafe.2 x sourceSlot hsourceSlot with
          ⟨value, hstoreSlot, sourceEvidence, _⟩
        rcases RelaxedValidPartialValueEvidence.strengthen_exists
            sourceEvidence hx.2 with
          ⟨resultEvidence, _hrel⟩
        refine ⟨value, ?_, resultEvidence, trivial⟩
        simpa [hx.1] using hstoreSlot

theorem SafeAbstraction.relaxed_strengthen {store : ProgramStore}
    {source result : Env} :
    store ∼ₛ source →
    EnvStrengthens source result →
    RelaxedSafeAbstraction store result := by
  intro hsafe hstrength
  exact RelaxedSafeAbstraction.strengthen
    (SafeAbstraction.relaxed hsafe) hstrength

theorem RelaxedSafeAbstraction.strengthen_join_left {store : ProgramStore}
    {left right join : Env} :
    RelaxedSafeAbstraction store left →
    EnvJoin left right join →
    RelaxedSafeAbstraction store join := by
  intro hsafe hjoin
  exact RelaxedSafeAbstraction.strengthen hsafe (EnvJoin.left_le hjoin)

theorem RelaxedSafeAbstraction.strengthen_join_right {store : ProgramStore}
    {left right join : Env} :
    RelaxedSafeAbstraction store right →
    EnvJoin left right join →
    RelaxedSafeAbstraction store join := by
  intro hsafe hjoin
  exact RelaxedSafeAbstraction.strengthen hsafe (EnvJoin.right_le hjoin)

theorem SafeAbstraction.relaxed_strengthen_join_left {store : ProgramStore}
    {left right join : Env} :
    store ∼ₛ left →
    EnvJoin left right join →
    RelaxedSafeAbstraction store join := by
  intro hsafe hjoin
  exact RelaxedSafeAbstraction.strengthen_join_left
    (SafeAbstraction.relaxed hsafe) hjoin

theorem SafeAbstraction.relaxed_strengthen_join_right {store : ProgramStore}
    {left right join : Env} :
    store ∼ₛ right →
    EnvJoin left right join →
    RelaxedSafeAbstraction store join := by
  intro hsafe hjoin
  exact RelaxedSafeAbstraction.strengthen_join_right
    (SafeAbstraction.relaxed hsafe) hjoin

inductive EvidenceBorrowDependency (store : ProgramStore) :
    {value : PartialValue} → {ty : PartialTy} →
      ValidPartialValueEvidence store value ty → Location → Prop where
  | borrow {location : Location} {mutable : Bool} {targets : List LVal}
      {pointee : Ty} {target : LVal} {hmem : target ∈ targets}
      {hloc : store.loc target = some location} {dependency : Location} :
      LocReads store target dependency →
      EvidenceBorrowDependency store
        (ValidPartialValueEvidence.borrow (pointee := pointee) target hmem hloc)
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

theorem EvidenceBorrowDependency.ne_fresh {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : ValidPartialValueEvidence store value ty}
    {dependency : Location} :
    store.fresh dependency →
    EvidenceBorrowDependency store evidence dependency →
    False := by
  intro hfresh hdependency
  induction hdependency with
  | @borrow _ location mutable targets pointee target hmem hloc dependency hreads =>
      exact LocReads.ne_fresh_of_loc hfresh hloc hreads
  | boxInner _hdependency ih =>
      exact ih hfresh
  | boxFullInner _hdependency ih =>
      exact ih hfresh

theorem EvidenceBorrowDependency.selected {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : ValidPartialValueEvidence store value ty} {dependency : Location} :
    EvidenceBorrowDependency store evidence dependency →
    SelectedBorrowDependency store evidence.valid dependency := by
  intro hdependency
  induction hdependency with
  | @borrow _ location mutable targets pointee target hmem hloc dependency hreads =>
      exact SelectedBorrowDependency.borrow (mutable := mutable)
        (pointee := pointee) (target := target) (hmem := hmem)
        (hloc := hloc) hreads
  | @boxInner location slot inner hslot hinner dependency _hdependency ih =>
      exact SelectedBorrowDependency.boxInner (hslot := hslot) ih
  | @boxFullInner location slot innerTy hslot hinner dependency _hdependency ih =>
      exact SelectedBorrowDependency.boxFullInner (hslot := hslot) ih

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
  | borrow _hsubset =>
      rename_i oldMutable newMutable location mutable leftTargets rightTargets pointee
        target hmem hloc
      cases hdependency with
      | borrow hreads =>
          exact EvidenceBorrowDependency.borrow (mutable := oldMutable)
            (pointee := pointee) (target := target) (hmem := hmem)
            (hloc := hloc) hreads
  | box hinnerRel ih =>
      cases hdependency with
      | boxInner hinnerDependency =>
          exact EvidenceBorrowDependency.boxInner (ih hinnerDependency)
  | boxFull hinnerRel ih =>
      cases hdependency with
      | boxFullInner hinnerDependency =>
          exact EvidenceBorrowDependency.boxFullInner (ih hinnerDependency)

inductive RelaxedEvidenceBorrowDependency (store : ProgramStore) :
    {value : PartialValue} → {ty : PartialTy} →
      RelaxedValidPartialValueEvidence store value ty → Location → Prop where
  | borrow {location : Location} {mutable : Bool} {targets : List LVal}
      {pointee : Ty} {target : LVal} {hmem : target ∈ targets}
      {hloc : store.loc target = some location} {dependency : Location} :
      LocReads store target dependency →
      RelaxedEvidenceBorrowDependency store
        (RelaxedValidPartialValueEvidence.borrow (pointee := pointee)
          target hmem hloc)
        dependency
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {hslot : store.slotAt location = some slot}
      {hinner : RelaxedValidPartialValueEvidence store slot.value inner}
      {dependency : Location} :
      RelaxedEvidenceBorrowDependency store hinner dependency →
      RelaxedEvidenceBorrowDependency store
        (RelaxedValidPartialValueEvidence.box hslot hinner)
        dependency
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {hslot : store.slotAt location = some slot}
      {hinner : RelaxedValidPartialValueEvidence store slot.value (.ty ty)}
      {dependency : Location} :
      RelaxedEvidenceBorrowDependency store hinner dependency →
      RelaxedEvidenceBorrowDependency store
        (RelaxedValidPartialValueEvidence.boxFull hslot hinner)
        dependency

theorem RelaxedEvidenceBorrowDependency.ne_fresh {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : RelaxedValidPartialValueEvidence store value ty}
    {dependency : Location} :
    store.fresh dependency →
    RelaxedEvidenceBorrowDependency store evidence dependency →
    False := by
  intro hfresh hdependency
  induction hdependency with
  | @borrow _ location mutable targets pointee target hmem hloc dependency hreads =>
      exact LocReads.ne_fresh_of_loc hfresh hloc hreads
  | boxInner _hdependency ih =>
      exact ih hfresh
  | boxFullInner _hdependency ih =>
      exact ih hfresh

inductive RelaxedEvidenceOwnerReach (store : ProgramStore) :
    {value : PartialValue} → {ty : PartialTy} →
      RelaxedValidPartialValueEvidence store value ty → Location → Prop where
  | boxHere {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {hslot : store.slotAt location = some slot}
      {hinner : RelaxedValidPartialValueEvidence store slot.value inner} :
      RelaxedEvidenceOwnerReach store
        (RelaxedValidPartialValueEvidence.box hslot hinner)
        location
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {hslot : store.slotAt location = some slot}
      {hinner : RelaxedValidPartialValueEvidence store slot.value inner}
      {reached : Location} :
      RelaxedEvidenceOwnerReach store hinner reached →
      RelaxedEvidenceOwnerReach store
        (RelaxedValidPartialValueEvidence.box hslot hinner)
        reached
  | boxFullHere {location : Location} {slot : StoreSlot} {ty : Ty}
      {hslot : store.slotAt location = some slot}
      {hinner : RelaxedValidPartialValueEvidence store slot.value (.ty ty)} :
      RelaxedEvidenceOwnerReach store
        (RelaxedValidPartialValueEvidence.boxFull hslot hinner)
        location
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {hslot : store.slotAt location = some slot}
      {hinner : RelaxedValidPartialValueEvidence store slot.value (.ty ty)}
      {reached : Location} :
      RelaxedEvidenceOwnerReach store hinner reached →
      RelaxedEvidenceOwnerReach store
        (RelaxedValidPartialValueEvidence.boxFull hslot hinner)
        reached

theorem RelaxedEvidenceOwnerReach.ne_fresh {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : RelaxedValidPartialValueEvidence store value ty}
    {location : Location} :
    store.fresh location →
    RelaxedEvidenceOwnerReach store evidence location →
    False := by
  intro hfresh hreach
  induction hreach with
  | @boxHere location slot inner hslot =>
      rw [hfresh] at hslot
      contradiction
  | @boxInner location slot inner hslot hinner reached _hreach ih =>
      exact ih hfresh
  | @boxFullHere location slot ty hslot hinner =>
      rw [hfresh] at hslot
      contradiction
  | @boxFullInner location slot ty hslot hinner reached _hreach ih =>
      exact ih hfresh

theorem RelaxedEvidenceOwnerReach.reaches_concrete {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : RelaxedValidPartialValueEvidence store value ty}
    {location : Location} :
    PartialTy.Concrete ty →
    RelaxedEvidenceOwnerReach store evidence location →
    Reaches store value ty location := by
  intro hconcrete hreach
  induction hreach with
  | @boxHere location slot inner hslot =>
      exact Reaches.boxHere hslot
  | @boxInner location slot inner hslot hinner reached hinnerReach ih =>
      exact Reaches.boxInner hslot (ih hconcrete)
  | @boxFullHere location slot ty hslot =>
      exact Reaches.boxFullHere hslot
  | @boxFullInner location slot ty hslot hinner reached hinnerReach ih =>
      exact Reaches.boxFullInner hslot (ih trivial)

theorem RelaxedEvidenceOwnerReach.reaches_full {store : ProgramStore}
    {value : PartialValue} {ty : Ty}
    {evidence : RelaxedValidPartialValueEvidence store value (.ty ty)}
    {location : Location} :
    RelaxedEvidenceOwnerReach store evidence location →
    Reaches store value (.ty ty) location :=
  RelaxedEvidenceOwnerReach.reaches_concrete trivial

theorem RelaxedEvidenceOwnerReach.ownerReaches_concrete {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : RelaxedValidPartialValueEvidence store value ty}
    {location : Location} :
    PartialTy.Concrete ty →
    RelaxedEvidenceOwnerReach store evidence location →
    OwnerReaches store value ty location := by
  intro hconcrete hreach
  induction hreach with
  | boxHere =>
      rename_i location slot inner hslot _hinner
      exact OwnerReaches.boxHere hslot
  | boxInner _hinnerReach ih =>
      rename_i location slot inner hslot _hinner reached
      exact OwnerReaches.boxInner hslot (ih hconcrete)
  | boxFullHere =>
      rename_i location slot ty hslot _hinner
      exact OwnerReaches.boxFullHere hslot
  | boxFullInner _hinnerReach ih =>
      rename_i location slot ty hslot _hinner reached
      exact OwnerReaches.boxFullInner hslot (ih trivial)

theorem RelaxedEvidenceOwnerReach.ownerReaches_full {store : ProgramStore}
    {value : PartialValue} {ty : Ty}
    {evidence : RelaxedValidPartialValueEvidence store value (.ty ty)}
    {location : Location} :
    RelaxedEvidenceOwnerReach store evidence location →
    OwnerReaches store value (.ty ty) location := by
  exact RelaxedEvidenceOwnerReach.ownerReaches_concrete trivial

def RelaxedEvidenceBorrowDependency.borrowDependency_full {store : ProgramStore}
    {value : PartialValue} {ty : Ty}
    {evidence : RelaxedValidPartialValueEvidence store value (.ty ty)}
    {location : Location} :
    RelaxedEvidenceBorrowDependency store evidence location →
    BorrowDependency store value (.ty ty) location :=
  match evidence with
  | RelaxedValidPartialValueEvidence.unit =>
      fun hdependency => by cases hdependency
  | RelaxedValidPartialValueEvidence.int =>
      fun hdependency => by cases hdependency
  | RelaxedValidPartialValueEvidence.bool =>
      fun hdependency => by cases hdependency
  | @RelaxedValidPartialValueEvidence.borrow _ location mutable targets pointee
      target hmem hloc =>
      fun hdependency => by
        cases hdependency with
        | borrow hreads =>
            exact BorrowDependency.borrow (mutable := mutable)
              (targets := targets) (pointee := pointee) (target := target)
              hmem hloc hreads
  | RelaxedValidPartialValueEvidence.boxFull hslot hinner =>
      fun hdependency => by
        cases hdependency with
        | boxFullInner hinnerDependency =>
            exact BorrowDependency.boxFullInner hslot
              (RelaxedEvidenceBorrowDependency.borrowDependency_full
                hinnerDependency)

def RelaxedEvidenceBorrowDependency.borrowDependency {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {evidence : RelaxedValidPartialValueEvidence store value ty}
    {location : Location} :
    RelaxedEvidenceBorrowDependency store evidence location →
    BorrowDependency store value ty location :=
  match evidence with
  | RelaxedValidPartialValueEvidence.unit =>
      fun hdependency => by cases hdependency
  | RelaxedValidPartialValueEvidence.int =>
      fun hdependency => by cases hdependency
  | RelaxedValidPartialValueEvidence.bool =>
      fun hdependency => by cases hdependency
  | RelaxedValidPartialValueEvidence.undef =>
      fun hdependency => by cases hdependency
  | @RelaxedValidPartialValueEvidence.borrow _ location mutable targets pointee
      target hmem hloc =>
      fun hdependency => by
        cases hdependency with
        | borrow hreads =>
            exact BorrowDependency.borrow (mutable := mutable)
              (targets := targets) (pointee := pointee) (target := target)
              hmem hloc hreads
  | @RelaxedValidPartialValueEvidence.box _ location slot inner hslot hinner =>
      fun hdependency => by
        cases hdependency with
        | boxInner hinnerDependency =>
            exact BorrowDependency.boxInner hslot
              (RelaxedEvidenceBorrowDependency.borrowDependency
                hinnerDependency)
  | @RelaxedValidPartialValueEvidence.boxFull _ location slot innerTy hslot hinner =>
      fun hdependency => by
        cases hdependency with
        | boxFullInner hinnerDependency =>
            exact BorrowDependency.boxFullInner hslot
              (RelaxedEvidenceBorrowDependency.borrowDependency
                hinnerDependency)
  | @RelaxedValidPartialValueEvidence.intoUndef _ value source target hstrength hinner =>
      fun hdependency => by cases hdependency

theorem RelaxedEvidenceBorrowDependency.of_strengthens
    {store : ProgramStore} {value : PartialValue}
    {oldTy newTy : PartialTy}
    {oldEvidence : RelaxedValidPartialValueEvidence store value oldTy}
    {newEvidence : RelaxedValidPartialValueEvidence store value newTy}
    {dependency : Location} :
    RelaxedValidPartialValueEvidence.Strengthens oldEvidence newEvidence →
    RelaxedEvidenceBorrowDependency store newEvidence dependency →
    RelaxedEvidenceBorrowDependency store oldEvidence dependency := by
  intro hrel hdependency
  induction hrel with
  | unit => cases hdependency
  | int => cases hdependency
  | bool => cases hdependency
  | undef => cases hdependency
  | borrow _hsubset =>
      rename_i oldMutable newMutable location mutable leftTargets rightTargets pointee
        target hmem hloc
      cases hdependency with
      | borrow hreads =>
          exact RelaxedEvidenceBorrowDependency.borrow
            (mutable := oldMutable) (pointee := pointee) (target := target)
            (hmem := hmem) (hloc := hloc) hreads
  | box hinnerRel ih =>
      cases hdependency with
      | boxInner hinnerDependency =>
          exact RelaxedEvidenceBorrowDependency.boxInner
            (ih hinnerDependency)
  | boxFull hinnerRel ih =>
      cases hdependency with
      | boxFullInner hinnerDependency =>
          exact RelaxedEvidenceBorrowDependency.boxFullInner
            (ih hinnerDependency)
  | hide _hstrength =>
      cases hdependency
  | discardUndef _hstrength =>
      cases hdependency
  | hiddenRefl =>
      exact hdependency
  | hiddenWiden hsource _hwiden =>
      cases hdependency

theorem EvidenceBorrowDependency.of_relaxed_of_strict
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy}
    {evidence : ValidPartialValueEvidence store value ty}
    {dependency : Location} :
    RelaxedEvidenceBorrowDependency store
      (RelaxedValidPartialValueEvidence.of_strict evidence) dependency →
    EvidenceBorrowDependency store evidence dependency := by
  induction evidence with
  | unit =>
      intro hdependency
      cases hdependency
  | int =>
      intro hdependency
      cases hdependency
  | bool =>
      intro hdependency
      cases hdependency
  | undef =>
      intro hdependency
      cases hdependency
  | @borrow location mutable targets pointee target hmem hloc =>
      intro hdependency
      cases hdependency with
      | borrow hreads =>
          exact EvidenceBorrowDependency.borrow (mutable := mutable)
            (pointee := pointee) (target := target) (hmem := hmem)
            (hloc := hloc) hreads
  | box hslot hinner ih =>
      intro hdependency
      cases hdependency with
      | boxInner hinnerDependency =>
          exact EvidenceBorrowDependency.boxInner (ih hinnerDependency)
  | boxFull hslot hinner ih =>
      intro hdependency
      cases hdependency with
      | boxFullInner hinnerDependency =>
          exact EvidenceBorrowDependency.boxFullInner (ih hinnerDependency)

def RelaxedEvidenceBorrowDependency.of_to_strict_full
    {store : ProgramStore} {value : PartialValue} {ty : Ty}
    {evidence : RelaxedValidPartialValueEvidence store value (.ty ty)}
    {dependency : Location} :
    EvidenceBorrowDependency store
      (RelaxedValidPartialValueEvidence.to_strict_full evidence) dependency →
    RelaxedEvidenceBorrowDependency store evidence dependency :=
  match evidence with
  | RelaxedValidPartialValueEvidence.unit =>
      fun hdependency => by cases hdependency
  | RelaxedValidPartialValueEvidence.int =>
      fun hdependency => by cases hdependency
  | RelaxedValidPartialValueEvidence.bool =>
      fun hdependency => by cases hdependency
  | @RelaxedValidPartialValueEvidence.borrow _ location mutable targets pointee
      target hmem hloc =>
      fun hdependency => by
        cases hdependency with
        | borrow hreads =>
            exact RelaxedEvidenceBorrowDependency.borrow
              (mutable := mutable) (targets := targets) (pointee := pointee)
              (target := target) (hmem := hmem) (hloc := hloc) hreads
  | RelaxedValidPartialValueEvidence.boxFull hslot hinner =>
      fun hdependency => by
        cases hdependency with
        | boxFullInner hinnerDependency =>
            exact RelaxedEvidenceBorrowDependency.boxFullInner
              (RelaxedEvidenceBorrowDependency.of_to_strict_full
                hinnerDependency)

theorem RelaxedEvidenceOwnerReach.of_strengthens
    {store : ProgramStore} {value : PartialValue}
    {oldTy newTy : PartialTy}
    {oldEvidence : RelaxedValidPartialValueEvidence store value oldTy}
    {newEvidence : RelaxedValidPartialValueEvidence store value newTy}
    {reached : Location} :
    RelaxedValidPartialValueEvidence.Strengthens oldEvidence newEvidence →
    RelaxedEvidenceOwnerReach store newEvidence reached →
    RelaxedEvidenceOwnerReach store oldEvidence reached := by
  intro hrel hreach
  induction hrel with
  | unit => cases hreach
  | int => cases hreach
  | bool => cases hreach
  | undef => cases hreach
  | borrow _hsubset => cases hreach
  | box hinnerRel ih =>
      cases hreach with
      | boxHere => exact RelaxedEvidenceOwnerReach.boxHere
      | boxInner hinnerReach =>
          exact RelaxedEvidenceOwnerReach.boxInner (ih hinnerReach)
  | boxFull hinnerRel ih =>
      cases hreach with
      | boxFullHere => exact RelaxedEvidenceOwnerReach.boxFullHere
      | boxFullInner hinnerReach =>
          exact RelaxedEvidenceOwnerReach.boxFullInner (ih hinnerReach)
  | hide _hstrength =>
      cases hreach
  | discardUndef _hstrength =>
      cases hreach
  | hiddenRefl =>
      exact hreach
  | hiddenWiden hsource _hwiden =>
      cases hreach

/--
Evidence-indexed update frame for relaxed runtime evidence.

This is the relaxed analogue of
`validPartialValueEvidence_update_of_owner_and_evidence_dependency_frame`: it
transports the concrete evidence hidden behind `undef`, rather than
reconstructing arbitrary validity evidence after the write.
-/
theorem relaxedValidPartialValueEvidence_update_of_owner_and_evidence_dependency_frame
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot} :
    ∀ {value : PartialValue} {ty : PartialTy}
      (evidence : RelaxedValidPartialValueEvidence store value ty),
      (∀ location,
        RelaxedEvidenceOwnerReach store evidence location →
        location ≠ updated) →
      (∀ location,
        RelaxedEvidenceBorrowDependency store evidence location →
        location ≠ updated) →
      ∃ evidence' :
        RelaxedValidPartialValueEvidence
          (store.update updated newSlot) value ty,
        ∀ location,
          RelaxedEvidenceBorrowDependency
            (store.update updated newSlot) evidence' location →
          RelaxedEvidenceBorrowDependency store evidence location := by
  intro value ty evidence
  induction evidence with
  | unit =>
      intro _howners _hdeps
      exact ⟨RelaxedValidPartialValueEvidence.unit,
        by intro location hdep; cases hdep⟩
  | int =>
      intro _howners _hdeps
      exact ⟨RelaxedValidPartialValueEvidence.int,
        by intro location hdep; cases hdep⟩
  | bool =>
      intro _howners _hdeps
      exact ⟨RelaxedValidPartialValueEvidence.bool,
        by intro location hdep; cases hdep⟩
  | undef =>
      intro _howners _hdeps
      exact ⟨RelaxedValidPartialValueEvidence.undef,
        by intro location hdep; cases hdep⟩
  | @borrow location mutable targets pointee target hmem hloc =>
      intro _howners hdeps
      have hloc' : (store.update updated newSlot).loc target = some location :=
        loc_update_of_not_locReads hloc (by
          intro dependency hreads
          exact hdeps dependency
            (RelaxedEvidenceBorrowDependency.borrow
              (store := store) (location := location) (mutable := mutable)
              (targets := targets) (pointee := pointee) (target := target)
              (hmem := hmem) (hloc := hloc) hreads))
      refine ⟨RelaxedValidPartialValueEvidence.borrow (pointee := pointee)
        target hmem hloc', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | borrow hreads =>
          exact RelaxedEvidenceBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (pointee := pointee) (target := target)
            (hmem := hmem) (hloc := hloc)
            (locReads_update_to_store_of_not_locReads hloc
              (by
                intro mid hmid
                exact hdeps mid
                  (RelaxedEvidenceBorrowDependency.borrow
                    (store := store) (location := location) (mutable := mutable)
                    (targets := targets) (pointee := pointee) (target := target)
                    (hmem := hmem) (hloc := hloc) hmid))
              hreads)
  | @box location slot inner hslot hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (RelaxedEvidenceOwnerReach.boxHere (hslot := hslot))
      have hslot' :
          (store.update updated newSlot).slotAt location = some slot := by
        rw [ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      rcases ih
          (by
            intro reached hreach
            exact howners reached
              (RelaxedEvidenceOwnerReach.boxInner
                (hslot := hslot) hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (RelaxedEvidenceBorrowDependency.boxInner
                (store := store) (location := location) (slot := slot)
                (inner := inner) (hslot := hslot) (hinner := hinner)
                hdependency)) with
        ⟨innerEvidence', hinnerDeps⟩
      refine ⟨RelaxedValidPartialValueEvidence.box hslot' innerEvidence', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | boxInner hdependency' =>
          exact RelaxedEvidenceBorrowDependency.boxInner
            (store := store) (location := location) (slot := slot)
            (inner := inner) (hslot := hslot) (hinner := hinner)
            (hinnerDeps dependency hdependency')
  | @boxFull location slot innerTy hslot hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (RelaxedEvidenceOwnerReach.boxFullHere (hslot := hslot))
      have hslot' :
          (store.update updated newSlot).slotAt location = some slot := by
        rw [ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      rcases ih
          (by
            intro reached hreach
            exact howners reached
              (RelaxedEvidenceOwnerReach.boxFullInner
                (hslot := hslot) hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (RelaxedEvidenceBorrowDependency.boxFullInner
                (store := store) (location := location) (slot := slot)
                (ty := innerTy) (hslot := hslot) (hinner := hinner)
                hdependency)) with
        ⟨innerEvidence', hinnerDeps⟩
      refine ⟨RelaxedValidPartialValueEvidence.boxFull hslot' innerEvidence', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | boxFullInner hdependency' =>
          exact RelaxedEvidenceBorrowDependency.boxFullInner
            (store := store) (location := location) (slot := slot)
            (ty := innerTy) (hslot := hslot) (hinner := hinner)
            (hinnerDeps dependency hdependency')
  | @intoUndef value source target hstrength hinner ih =>
      intro _howners _hdeps
      refine ⟨RelaxedValidPartialValueEvidence.undef, ?_⟩
      intro dependency hdependency
      cases hdependency

theorem relaxedValidPartialValueEvidence_declare_of_fresh {store : ProgramStore}
    {x : Name} {lifetime : Lifetime} {newValue : Value}
    {value : PartialValue} {ty : PartialTy}
    (evidence : RelaxedValidPartialValueEvidence store value ty) :
    store.fresh (VariableProjection x) →
    ∃ evidence' :
      RelaxedValidPartialValueEvidence (store.declare x lifetime newValue)
        value ty,
      ∀ location,
        RelaxedEvidenceBorrowDependency
          (store.declare x lifetime newValue) evidence' location →
        RelaxedEvidenceBorrowDependency store evidence location := by
  intro hfresh
  rcases
      relaxedValidPartialValueEvidence_update_of_owner_and_evidence_dependency_frame
        (updated := VariableProjection x)
        (newSlot := { value := .value newValue, lifetime := lifetime })
        evidence
        (by
          intro location hreach hlocation
          subst hlocation
          exact RelaxedEvidenceOwnerReach.ne_fresh hfresh hreach)
        (by
          intro location hdependency hlocation
          subst hlocation
          exact RelaxedEvidenceBorrowDependency.ne_fresh hfresh hdependency) with
    ⟨evidence', hdependencyBack⟩
  refine ⟨by
      simpa [ProgramStore.declare, VariableProjection] using evidence',
    ?_⟩
  intro location hdependency
  exact hdependencyBack location (by
    simpa [ProgramStore.declare, VariableProjection] using hdependency)

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
        ∀ location,
          EvidenceBorrowDependency (store.update updated newSlot) evidence' location →
          EvidenceBorrowDependency store evidence location := by
  intro value ty evidence
  induction evidence with
  | unit =>
      intro _howners _hdeps
      exact ⟨ValidPartialValueEvidence.unit, by intro location hdep; cases hdep⟩
  | int =>
      intro _howners _hdeps
      exact ⟨ValidPartialValueEvidence.int, by intro location hdep; cases hdep⟩
  | bool =>
      intro _howners _hdeps
      exact ⟨ValidPartialValueEvidence.bool, by intro location hdep; cases hdep⟩
  | undef =>
      intro _howners _hdeps
      exact ⟨ValidPartialValueEvidence.undef, by intro location hdep; cases hdep⟩
  | @borrow location mutable targets pointee target hmem hloc =>
      intro _howners hdeps
      have hloc' : (store.update updated newSlot).loc target = some location :=
        loc_update_of_not_locReads hloc (by
          intro dependency hreads
          exact hdeps dependency
            (EvidenceBorrowDependency.borrow
              (store := store) (location := location) (mutable := mutable)
              (targets := targets) (pointee := pointee) (target := target)
              (hmem := hmem) (hloc := hloc) hreads))
      refine ⟨ValidPartialValueEvidence.borrow (pointee := pointee)
        target hmem hloc', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | borrow hreads =>
          exact EvidenceBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (pointee := pointee) (target := target)
            (hmem := hmem) (hloc := hloc)
            (locReads_update_to_store_of_not_locReads hloc
              (by
                intro mid hmid
                exact hdeps mid
                  (EvidenceBorrowDependency.borrow
                    (store := store) (location := location) (mutable := mutable)
                    (targets := targets) (pointee := pointee) (target := target)
                    (hmem := hmem) (hloc := hloc) hmid))
              hreads)
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
        ⟨innerEvidence', hinnerDeps⟩
      refine ⟨ValidPartialValueEvidence.box hslot' innerEvidence', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | boxInner hdependency' =>
          exact EvidenceBorrowDependency.boxInner
            (store := store) (location := location) (slot := slot)
            (inner := inner) (hslot := hslot) (hinner := hinner)
            (hinnerDeps dependency hdependency')
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
        ⟨innerEvidence', hinnerDeps⟩
      refine ⟨ValidPartialValueEvidence.boxFull hslot' innerEvidence', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | boxFullInner hdependency' =>
          exact EvidenceBorrowDependency.boxFullInner
            (store := store) (location := location) (slot := slot)
            (ty := innerTy) (hslot := hslot) (hinner := hinner)
            (hinnerDeps dependency hdependency')

theorem validPartialValueEvidence_declare_of_fresh {store : ProgramStore}
    {x : Name} {lifetime : Lifetime} {newValue : Value}
    {value : PartialValue} {ty : PartialTy}
    (evidence : ValidPartialValueEvidence store value ty) :
    store.fresh (VariableProjection x) →
    ∃ evidence' :
      ValidPartialValueEvidence (store.declare x lifetime newValue) value ty,
      ∀ location,
        EvidenceBorrowDependency
          (store.declare x lifetime newValue) evidence' location →
        EvidenceBorrowDependency store evidence location := by
  intro hfresh
  rcases
      validPartialValueEvidence_update_of_owner_and_evidence_dependency_frame
        (updated := VariableProjection x)
        (newSlot := { value := .value newValue, lifetime := lifetime })
        evidence
        (by
          intro location hreach hlocation
          subst hlocation
          exact OwnerReaches.ne_fresh hfresh hreach)
        (by
          intro location hdependency hlocation
          subst hlocation
          exact EvidenceBorrowDependency.ne_fresh hfresh hdependency) with
    ⟨evidence', hdependencyBack⟩
  refine ⟨by
      simpa [ProgramStore.declare, VariableProjection] using evidence',
    ?_⟩
  intro location hdependency
  exact hdependencyBack location (by
    simpa [ProgramStore.declare, VariableProjection] using hdependency)

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
  | @borrow location mutable targets pointee target hmem hloc =>
      intro _howners hdeps
      refine ValidPartialValue.borrow hmem ?_
      exact loc_drops_of_not_locReads hdrops hloc (by
        intro mid hreads
        exact hdeps mid
          (SelectedBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (pointee := pointee) (target := target)
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
  | @borrow location mutable targets pointee target hmem hloc =>
      intro _howners hdeps
      refine ValidPartialValue.borrow hmem ?_
      exact loc_drops_of_not_locReads hdrops hloc (by
        intro mid hreads
        exact hdeps mid
          (EvidenceBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (pointee := pointee) (target := target)
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
        ∀ location,
          EvidenceBorrowDependency store' evidence' location →
          EvidenceBorrowDependency store evidence location := by
  intro hdrops value ty evidence
  induction evidence with
  | unit =>
      intro _howners _hdeps
      exact ⟨ValidPartialValueEvidence.unit, by intro location hdep; cases hdep⟩
  | int =>
      intro _howners _hdeps
      exact ⟨ValidPartialValueEvidence.int, by intro location hdep; cases hdep⟩
  | bool =>
      intro _howners _hdeps
      exact ⟨ValidPartialValueEvidence.bool, by intro location hdep; cases hdep⟩
  | undef =>
      intro _howners _hdeps
      exact ⟨ValidPartialValueEvidence.undef, by intro location hdep; cases hdep⟩
  | @borrow location mutable targets pointee target hmem hloc =>
      intro _howners hdeps
      have hloc' : store'.loc target = some location :=
        loc_drops_of_not_locReads hdrops hloc (by
          intro dependency hreads
          exact hdeps dependency
            (EvidenceBorrowDependency.borrow
              (store := store) (location := location) (mutable := mutable)
              (targets := targets) (pointee := pointee) (target := target)
              (hmem := hmem) (hloc := hloc) hreads))
      refine ⟨ValidPartialValueEvidence.borrow (pointee := pointee)
        target hmem hloc', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | borrow hreads =>
          exact EvidenceBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (pointee := pointee) (target := target)
            (hmem := hmem) (hloc := hloc)
            (locReads_drops_to_store hdrops hreads)
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
        ⟨innerEvidence', hinnerDeps⟩
      refine ⟨ValidPartialValueEvidence.box hslot' innerEvidence', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | boxInner hdependency' =>
          exact EvidenceBorrowDependency.boxInner
            (store := store) (location := location) (slot := slot)
            (inner := inner) (hslot := hslot) (hinner := hinner)
            (hinnerDeps dependency hdependency')
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
        ⟨innerEvidence', hinnerDeps⟩
      refine ⟨ValidPartialValueEvidence.boxFull hslot' innerEvidence', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | boxFullInner hdependency' =>
          exact EvidenceBorrowDependency.boxFullInner
            (store := store) (location := location) (slot := slot)
            (ty := innerTy) (hslot := hslot) (hinner := hinner)
            (hinnerDeps dependency hdependency')

/--
Evidence-indexed drop frame for relaxed runtime evidence.

The hidden concrete witness below an abstract `undef` is transported through the
drop and wrapped again, so protected dependency paths are not lost by
reconstructing arbitrary post-drop validity evidence.
-/
theorem relaxedValidPartialValueEvidence_drops_of_owner_and_evidence_dependency_frame
    {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ∀ {value : PartialValue} {ty : PartialTy}
      (evidence : RelaxedValidPartialValueEvidence store value ty),
      (∀ location,
        RelaxedEvidenceOwnerReach store evidence location →
        DropsAvoids store values location) →
      (∀ location,
        RelaxedEvidenceBorrowDependency store evidence location →
        DropsAvoids store values location) →
      ∃ evidence' : RelaxedValidPartialValueEvidence store' value ty,
        ∀ location,
          RelaxedEvidenceBorrowDependency store' evidence' location →
          RelaxedEvidenceBorrowDependency store evidence location := by
  intro hdrops value ty evidence
  induction evidence with
  | unit =>
      intro _howners _hdeps
      exact ⟨RelaxedValidPartialValueEvidence.unit,
        by intro location hdep; cases hdep⟩
  | int =>
      intro _howners _hdeps
      exact ⟨RelaxedValidPartialValueEvidence.int,
        by intro location hdep; cases hdep⟩
  | bool =>
      intro _howners _hdeps
      exact ⟨RelaxedValidPartialValueEvidence.bool,
        by intro location hdep; cases hdep⟩
  | undef =>
      intro _howners _hdeps
      exact ⟨RelaxedValidPartialValueEvidence.undef,
        by intro location hdep; cases hdep⟩
  | @borrow location mutable targets pointee target hmem hloc =>
      intro _howners hdeps
      have hloc' : store'.loc target = some location :=
        loc_drops_of_not_locReads hdrops hloc (by
          intro dependency hreads
          exact hdeps dependency
            (RelaxedEvidenceBorrowDependency.borrow
              (store := store) (location := location) (mutable := mutable)
              (targets := targets) (pointee := pointee) (target := target)
              (hmem := hmem) (hloc := hloc) hreads))
      refine ⟨RelaxedValidPartialValueEvidence.borrow (pointee := pointee)
        target hmem hloc', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | borrow hreads =>
          exact RelaxedEvidenceBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (pointee := pointee) (target := target)
            (hmem := hmem) (hloc := hloc)
            (locReads_drops_to_store hdrops hreads)
  | @box location slot inner hslot hinner ih =>
      intro howners hdeps
      have hlocationAvoid : DropsAvoids store values location :=
        howners location (RelaxedEvidenceOwnerReach.boxHere (hslot := hslot))
      have hslot' : store'.slotAt location = some slot :=
        dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      rcases ih
          (by
            intro reached hreach
            exact howners reached
              (RelaxedEvidenceOwnerReach.boxInner
                (hslot := hslot) hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (RelaxedEvidenceBorrowDependency.boxInner
                (store := store) (location := location) (slot := slot)
                (inner := inner) (hslot := hslot) (hinner := hinner)
                hdependency)) with
        ⟨innerEvidence', hinnerDeps⟩
      refine ⟨RelaxedValidPartialValueEvidence.box hslot' innerEvidence', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | boxInner hdependency' =>
          exact RelaxedEvidenceBorrowDependency.boxInner
            (store := store) (location := location) (slot := slot)
            (inner := inner) (hslot := hslot) (hinner := hinner)
            (hinnerDeps dependency hdependency')
  | @boxFull location slot innerTy hslot hinner ih =>
      intro howners hdeps
      have hlocationAvoid : DropsAvoids store values location :=
        howners location
          (RelaxedEvidenceOwnerReach.boxFullHere (hslot := hslot))
      have hslot' : store'.slotAt location = some slot :=
        dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      rcases ih
          (by
            intro reached hreach
            exact howners reached
              (RelaxedEvidenceOwnerReach.boxFullInner
                (hslot := hslot) hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (RelaxedEvidenceBorrowDependency.boxFullInner
                (store := store) (location := location) (slot := slot)
                (ty := innerTy) (hslot := hslot) (hinner := hinner)
                hdependency)) with
        ⟨innerEvidence', hinnerDeps⟩
      refine ⟨RelaxedValidPartialValueEvidence.boxFull hslot' innerEvidence', ?_⟩
      intro dependency hdependency
      cases hdependency with
      | boxFullInner hdependency' =>
          exact RelaxedEvidenceBorrowDependency.boxFullInner
            (store := store) (location := location) (slot := slot)
            (ty := innerTy) (hslot := hslot) (hinner := hinner)
            (hinnerDeps dependency hdependency')
  | @intoUndef value source target hstrength hinner ih =>
      intro _howners _hdeps
      refine ⟨RelaxedValidPartialValueEvidence.undef, ?_⟩
      intro dependency hdependency
      cases hdependency

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
            intro mutable targets pointee hcontains
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
            intro mutable targets pointee hcontains
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

/--
Owner reachability selected by relaxed evidence is still a transitive ownership
path rooted at the slot that stores the represented value.
-/
theorem ownsTransitively_of_relaxedEvidenceOwnerReach_stored
    {store : ProgramStore} {storage location : Location}
    {storageLifetime : Lifetime} {storedValue : PartialValue}
    {partialTy : PartialTy}
    {evidence : RelaxedValidPartialValueEvidence store storedValue partialTy} :
    store.slotAt storage =
      some { value := storedValue, lifetime := storageLifetime } →
    RelaxedEvidenceOwnerReach store evidence location →
    ProgramStore.OwnsTransitively store storage location := by
  intro hstored hreach
  induction hreach generalizing storage storageLifetime with
  | @boxHere ownerLocation _slot _inner _hslot =>
      exact ProgramStore.OwnsTransitively.direct
        ⟨storageLifetime, by simpa [owningRef] using hstored⟩
  | @boxInner ownerLocation slot inner hslot _hinner reached _hreach ih =>
      have hownsRoot : ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨storageLifetime, by simpa [owningRef] using hstored⟩
      exact ProgramStore.OwnsTransitively.trans hownsRoot
        (ih hslot)
  | @boxFullHere ownerLocation _slot _ty _hslot =>
      exact ProgramStore.OwnsTransitively.direct
        ⟨storageLifetime, by simpa [owningRef] using hstored⟩
  | @boxFullInner ownerLocation slot ty hslot _hinner reached _hreach ih =>
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
  | @borrow borrowedLocation mutable targets pointee target hmem hloc =>
      cases hreach with
      | @borrow _borrowedLocation readLocation _mutable _targets _pointee target' hmem' _hloc' hreads =>
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
            intro mutable targets pointee hcontains
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
            intro mutable targets pointee hcontains
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
  | @borrow borrowedLocation mutable targets pointee target hmem hloc =>
      cases hreach with
      | @borrow _borrowedLocation readLocation _mutable _targets _pointee target' hmem' _hloc' hreads =>
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
            intro mutable targets pointee hcontains
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
            intro mutable targets pointee hcontains
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
