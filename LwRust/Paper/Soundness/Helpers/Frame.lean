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
  | borrow {location ℓ : Location} {mutable : Bool} {targets : List LVal} {target : LVal} :
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
**Store-realized borrow read.**

The purely store-level (type-free) realization of a borrow-resolution dependency:
descending through *owning* boxes from `value`, there is a borrow reference
`ref{loc, false}` whose **realized** target — a target `t` actually resolving to
the reference's stored pointee location `loc` (`store.loc t = some loc`) — reads
`dependency` during its lval resolution (`LocReads store t dependency`).

Unlike `BorrowDependency`, this carries **no static target list**: the only
target it ever speaks about is one that resolves to the value's *actual* runtime
pointee.  It is therefore keyed entirely on the store (`store.loc`,
`store.slotAt`, `LocReads`) and is invariant under any change to the env type's
target lists — in particular it is unchanged by a `T-If` join, which only
coarsens the type.  This is the realized-witness predicate the deref-write frame
truly needs (see `validPartialValue_update_of_owner_and_realized_reads_frame`).
-/
inductive RealizedBorrowReads (store : ProgramStore) :
    PartialValue → Location → Prop where
  | borrow {location dependency : Location} {target : LVal} :
      store.loc target = some location →
      LocReads store target dependency →
      RealizedBorrowReads store
        (.value (.ref { location := location, owner := false })) dependency
  | box {location : Location} {slot : StoreSlot} {dependency : Location} :
      store.slotAt location = some slot →
      RealizedBorrowReads store slot.value dependency →
      RealizedBorrowReads store
        (.value (.ref { location := location, owner := true })) dependency

/-- Erasing store slots cannot create a new realized borrow read: every realized
read observed after the erase was already a realized read in the original store.
-/
theorem RealizedBorrowReads.erase_to_store {store : ProgramStore}
    {erased : Location} {value : PartialValue} {dependency : Location} :
    RealizedBorrowReads (store.erase erased) value dependency →
    RealizedBorrowReads store value dependency := by
  intro hreads
  induction hreads with
  | borrow hloc hlocReads =>
      exact RealizedBorrowReads.borrow
        (loc_erase_some_to_store hloc)
        (locReads_erase_to_store hlocReads)
  | box hslot _hinnerReads ih =>
      exact RealizedBorrowReads.box (slotAt_of_erase_slotAt hslot) ih

/-- Updating a slot to `undef` cannot make a location resolution succeed in a
new way.  Any successful `loc` after the update was already successful before
the update. -/
theorem loc_update_undef_some_to_store {store : ProgramStore}
    {updated : Location} {updatedLifetime : Lifetime} :
    ∀ {lv : LVal} {location : Location},
      (store.update updated { value := .undef, lifetime := updatedLifetime }).loc lv =
        some location →
      store.loc lv = some location := by
  intro lv
  induction lv with
  | var x =>
      intro location hloc
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      intro location hloc
      cases hsource :
          (store.update updated { value := .undef, lifetime := updatedLifetime }).loc lv with
      | none =>
          simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          have hsourceStore : store.loc lv = some source := ih hsource
          by_cases hsourceEq : source = updated
          · subst hsourceEq
            simp [ProgramStore.loc, hsource] at hloc
          · have hslotEq :
                (store.update updated
                    { value := .undef, lifetime := updatedLifetime }).slotAt source =
                  store.slotAt source :=
                ProgramStore.slotAt_update_ne hsourceEq
            cases hslot : store.slotAt source with
            | none =>
                simp [ProgramStore.loc, hsource, hslotEq, hslot] at hloc
            | some slot =>
                rcases slot with ⟨slotValue, slotLifetime⟩
                cases slotValue with
                | undef =>
                    simp [ProgramStore.loc, hsource, hslotEq, hslot] at hloc
                | value value =>
                    cases value with
                    | ref ref =>
                        simp [ProgramStore.loc, hsource, hslotEq, hslot] at hloc
                        simp [ProgramStore.loc, hsourceStore, hslot, hloc]
                    | unit =>
                        simp [ProgramStore.loc, hsource, hslotEq, hslot] at hloc
                    | int value =>
                        simp [ProgramStore.loc, hsource, hslotEq, hslot] at hloc
                    | bool value =>
                        simp [ProgramStore.loc, hsource, hslotEq, hslot] at hloc

/-- Location reads observed after updating a slot to `undef` were already reads
of the original store. -/
theorem locReads_update_undef_to_store {store : ProgramStore}
    {updated : Location} {updatedLifetime : Lifetime} {lv : LVal}
    {location : Location} :
    LocReads
        (store.update updated { value := .undef, lifetime := updatedLifetime })
        lv location →
    LocReads store lv location := by
  intro hreads
  induction hreads with
  | here hloc =>
      exact LocReads.here (loc_update_undef_some_to_store hloc)
  | there _hreads ih =>
      exact LocReads.there ih

/-- Updating a slot to `undef` cannot create a store-realized borrow read. -/
theorem RealizedBorrowReads.update_undef_to_store {store : ProgramStore}
    {updated : Location} {updatedLifetime : Lifetime}
    {value : PartialValue} {dependency : Location} :
    RealizedBorrowReads
        (store.update updated { value := .undef, lifetime := updatedLifetime })
        value dependency →
    RealizedBorrowReads store value dependency := by
  intro hreads
  induction hreads with
  | borrow hloc hlocReads =>
      exact RealizedBorrowReads.borrow
        (loc_update_undef_some_to_store hloc)
        (locReads_update_undef_to_store hlocReads)
  | @box location slot dependency hslot _hinnerReads ih =>
      by_cases hlocation : location = updated
      · subst hlocation
        simp [ProgramStore.update] at hslot
        cases hslot
        cases _hinnerReads
      · exact RealizedBorrowReads.box
          (by
            rw [← ProgramStore.slotAt_update_ne hlocation]
            exact hslot)
          ih

/-- A borrow-resolution dependency is in particular a store-realized borrow read:
its `borrow` head already pins the target to the reference's own pointee location
(`store.loc target = some location`), and its box descent crosses owning boxes.
The static target list is discarded.  (Hence `SelectedBorrowDependency` — which
factors through `BorrowDependency` — also yields a `RealizedBorrowReads`.) -/
theorem BorrowDependency.realizedBorrowReads {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {dependency : Location} :
    BorrowDependency store value ty dependency →
    RealizedBorrowReads store value dependency := by
  intro hdependency
  induction hdependency with
  | borrow _hmem hloc hreads =>
      exact RealizedBorrowReads.borrow hloc hreads
  | boxInner hslot _hdependency ih =>
      exact RealizedBorrowReads.box hslot ih
  | boxFullInner hslot _hdependency ih =>
      exact RealizedBorrowReads.box hslot ih

/-- A validity proof's *selected* borrow dependency is in particular a
store-realized borrow read. -/
theorem SelectedBorrowDependency.realizedBorrowReads {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    {hvalid : ValidPartialValue store value ty} {dependency : Location} :
    SelectedBorrowDependency store hvalid dependency →
    RealizedBorrowReads store value dependency :=
  fun h => h.borrowDependency.realizedBorrowReads

/--
**The make-or-break realized-witness frame lemma.**

Updating a location `updated` preserves `ValidPartialValue` provided no
*owner-reachable* location and no *store-realized borrow read* of the value
resolves through `updated`.  This is strictly weaker than
`validPartialValue_update_of_owner_and_borrow_dependency_frame` and
`..._selected_dependency_frame`: it only constrains the borrow target that
actually witnesses the value's V-Borrow existential (the realized pointee), never
the full static target list.  V-Borrow survives the update via the *same*
realized target, because that target's resolution does not touch `updated`. -/
theorem validPartialValue_update_of_owner_and_realized_reads_frame
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot} :
    ∀ {value : PartialValue} {ty : PartialTy}
      (_hvalid : ValidPartialValue store value ty),
      (∀ location,
        OwnerReaches store value ty location →
        location ≠ updated) →
      (∀ location,
        RealizedBorrowReads store value location →
        location ≠ updated) →
      ValidPartialValue (store.update updated newSlot) value ty := by
  intro value ty hvalid
  induction hvalid with
  | unit | int | bool | undef =>
      intro _howners _hreads
      constructor
  | @borrow location mutable targets target hmem hloc =>
      intro _howners hreads
      refine ValidPartialValue.borrow hmem ?_
      exact loc_update_of_not_locReads hloc (by
        intro mid hmidReads
        exact hreads mid (RealizedBorrowReads.borrow hloc hmidReads))
  | @box location slot inner hslot _hinner ih =>
      intro howners hreads
      have hlocationNe : location ≠ updated :=
        howners location (OwnerReaches.boxHere hslot)
      refine ValidPartialValue.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxInner hslot hreach))
          (by
            intro dependency hdependency
            exact hreads dependency (RealizedBorrowReads.box hslot hdependency))
  | @boxFull location slot innerTy hslot _hinner ih =>
      intro howners hreads
      have hlocationNe : location ≠ updated :=
        howners location (OwnerReaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxFullInner hslot hreach))
          (by
            intro dependency hdependency
            exact hreads dependency (RealizedBorrowReads.box hslot hdependency))

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
