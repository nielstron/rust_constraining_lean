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
Ownership reachability through a value.  Unlike `Reaches`, this relation does not
include the lval-resolution reads of borrowed references; those reads are
dependencies, but they are not ownership edges.
-/
inductive OwnerReaches (store : ProgramStore) : PartialValue → PartialTy → Location → Prop where
  | undefOf {value : PartialValue} {oldTy : PartialTy} {ty : Ty} {ℓ : Location} :
      ValidPartialValueSkeleton store value oldTy →
      PartialTyStrengthens oldTy (.undef ty) →
      OwnerReaches store value oldTy ℓ →
      OwnerReaches store value (.undef ty) ℓ
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

/--
The store locations whose slots are inspected while checking the owner skeleton
of a value.  Fully visible borrows contribute their lval-resolution reads;
values hidden behind `undef` contribute only owner reachability.
-/
inductive Reaches (store : ProgramStore) : PartialValue → PartialTy → Location → Prop where
  | undefOf {value : PartialValue} {oldTy : PartialTy} {ty : Ty} {ℓ : Location} :
      ValidPartialValueSkeleton store value oldTy →
      PartialTyStrengthens oldTy (.undef ty) →
      OwnerReaches store value oldTy ℓ →
      Reaches store value (.undef ty) ℓ
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
Stale-aware reachability for weak runtime validity.  Initialized borrow target
lists contribute the same `loc`-resolution reads as full validity; stale borrow
annotations contribute no runtime read dependency.
-/
inductive ReachesWhenInitialized (env : Env) (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | undefOf {value : PartialValue} {oldTy : PartialTy} {ty : Ty} {ℓ : Location} :
      ValidPartialValueSkeleton store value oldTy →
      PartialTyStrengthens oldTy (.undef ty) →
      OwnerReaches store value oldTy ℓ →
      ReachesWhenInitialized env store value (.undef ty) ℓ
  | boxHere {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := true })) (.box inner)
        location
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {ℓ : Location} :
      store.slotAt location = some slot →
      ReachesWhenInitialized env store slot.value inner ℓ →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := true })) (.box inner) ℓ
  | boxFullHere {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := true })) (.ty (.box ty))
        location
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {ℓ : Location} :
      store.slotAt location = some slot →
      ReachesWhenInitialized env store slot.value (.ty ty) ℓ →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := true })) (.ty (.box ty)) ℓ
  | borrow {location ℓ : Location} {mutable : Bool} {targets : List LVal}
      {target : LVal} :
      BorrowTargetsInitialized env targets →
      target ∈ targets →
      store.loc target = some location →
      LocReads store target ℓ →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets)) ℓ

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

/--
Borrow-target lval-resolution dependencies for stale-aware validity.  A stale
borrow annotation has no dependency; initialized borrow target lists contribute
the same lvalue-resolution reads as ordinary validity.
-/
inductive BorrowDependencyWhenInitialized (env : Env) (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | borrow {location readLocation : Location} {mutable : Bool}
      {targets : List LVal} {target : LVal} :
      BorrowTargetsInitialized env targets →
      target ∈ targets →
      store.loc target = some location →
      LocReads store target readLocation →
      BorrowDependencyWhenInitialized env store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets)) readLocation
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {dependency : Location} :
      store.slotAt location = some slot →
      BorrowDependencyWhenInitialized env store slot.value inner dependency →
      BorrowDependencyWhenInitialized env store
        (.value (.ref { location := location, owner := true })) (.box inner)
        dependency
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {dependency : Location} :
      store.slotAt location = some slot →
      BorrowDependencyWhenInitialized env store slot.value (.ty ty) dependency →
      BorrowDependencyWhenInitialized env store
        (.value (.ref { location := location, owner := true })) (.ty (.box ty))
        dependency

theorem BorrowDependencyWhenInitialized.to_full {env : Env}
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy}
    {dependency : Location} :
    BorrowDependencyWhenInitialized env store value ty dependency →
    BorrowDependency store value ty dependency := by
  intro hdependency
  induction hdependency with
  | borrow _hinitialized hmem hloc hreads =>
      exact BorrowDependency.borrow hmem hloc hreads
  | boxInner hslot _hinner ih =>
      exact BorrowDependency.boxInner hslot ih
  | boxFullInner hslot _hinner ih =>
      exact BorrowDependency.boxFullInner hslot ih

theorem OwnerReaches.reaches {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    OwnerReaches store value ty location →
    Reaches store value ty location := by
  intro hreach
  induction hreach with
  | undefOf hvalid hstrength hinner _ih =>
      exact Reaches.undefOf hvalid hstrength hinner
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

theorem BorrowDependencyWhenInitialized.reaches {env : Env}
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy}
    {location : Location} :
    BorrowDependencyWhenInitialized env store value ty location →
    ReachesWhenInitialized env store value ty location := by
  intro hdependency
  induction hdependency with
  | borrow hinitialized hmem hloc hreads =>
      exact ReachesWhenInitialized.borrow hinitialized hmem hloc hreads
  | boxInner hslot _ ih =>
      exact ReachesWhenInitialized.boxInner hslot ih
  | boxFullInner hslot _ ih =>
      exact ReachesWhenInitialized.boxFullInner hslot ih

theorem OwnerReaches.undef_value_false {store : ProgramStore}
    {ty : PartialTy} {location : Location} :
    OwnerReaches store .undef ty location → False := by
  intro hreach
  generalize hvalueEq : (PartialValue.undef : PartialValue) = value at hreach
  induction hreach with
  | undefOf _ _ _ ih => exact ih hvalueEq
  | boxHere _ => cases hvalueEq
  | boxInner _ _ _ => cases hvalueEq
  | boxFullHere _ => cases hvalueEq
  | boxFullInner _ _ _ => cases hvalueEq

theorem Reaches.undef_value_false {store : ProgramStore}
    {ty : PartialTy} {location : Location} :
    Reaches store .undef ty location → False := by
  intro hreach
  generalize hvalueEq : (PartialValue.undef : PartialValue) = value at hreach
  induction hreach with
  | undefOf _ _ hinner =>
      cases hvalueEq
      exact OwnerReaches.undef_value_false hinner
  | boxHere _ => cases hvalueEq
  | boxInner _ _ _ => cases hvalueEq
  | boxFullHere _ => cases hvalueEq
  | boxFullInner _ _ _ => cases hvalueEq
  | borrow _ _ _ => cases hvalueEq

theorem BorrowDependency.undef_value_false {store : ProgramStore}
    {ty : PartialTy} {location : Location} :
    BorrowDependency store .undef ty location → False := by
  intro hdependency
  generalize hvalueEq : (PartialValue.undef : PartialValue) = value at hdependency
  induction hdependency with
  | borrow _ _ _ => cases hvalueEq
  | boxInner _ _ _ => cases hvalueEq
  | boxFullInner _ _ _ => cases hvalueEq

theorem Reaches.owner_or_borrow {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    Reaches store value ty location →
    OwnerReaches store value ty location ∨
      BorrowDependency store value ty location := by
  intro hreach
  induction hreach with
  | undefOf hvalid hstrength hinner =>
      exact Or.inl (OwnerReaches.undefOf hvalid hstrength hinner)
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

theorem ReachesWhenInitialized.owner_or_borrow {env : Env} {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    ReachesWhenInitialized env store value ty location →
    OwnerReaches store value ty location ∨
      BorrowDependencyWhenInitialized env store value ty location := by
  intro hreach
  induction hreach with
  | undefOf hvalid hstrength hinner =>
      exact Or.inl (OwnerReaches.undefOf hvalid hstrength hinner)
  | boxHere hslot =>
      exact Or.inl (OwnerReaches.boxHere hslot)
  | boxInner hslot _ ih =>
      rcases ih with howner | hborrow
      · exact Or.inl (OwnerReaches.boxInner hslot howner)
      · exact Or.inr (BorrowDependencyWhenInitialized.boxInner hslot hborrow)
  | boxFullHere hslot =>
      exact Or.inl (OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _ ih =>
      rcases ih with howner | hborrow
      · exact Or.inl (OwnerReaches.boxFullInner hslot howner)
      · exact Or.inr (BorrowDependencyWhenInitialized.boxFullInner hslot hborrow)
  | borrow hinitialized hmem hloc hreads =>
      exact Or.inr (BorrowDependencyWhenInitialized.borrow hinitialized hmem hloc hreads)

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
  | undef {ty : Ty} :
      ValidPartialValueEvidence store .undef (.undef ty)
  | undefOf {value : PartialValue} {oldTy : PartialTy} {ty : Ty} :
      ValidPartialValueSkeleton store value oldTy →
      PartialTyStrengthens oldTy (.undef ty) →
      ValidPartialValueEvidence store value (.undef ty)
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
  | undef => ValidPartialValue.undef
  | undefOf hinner hstrength => ValidPartialValue.undefOf hinner hstrength
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
  | undef => exact ⟨ValidPartialValueEvidence.undef, trivial⟩
  | undefOf hinner hstrength =>
      exact ⟨ValidPartialValueEvidence.undefOf hinner hstrength, trivial⟩
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
  | undef {oldTy newTy : Ty} :
      StrengthensSameShape
        (ValidPartialValueEvidence.undef (ty := oldTy))
        (ValidPartialValueEvidence.undef (ty := newTy))
  | undefOf {value : PartialValue} {oldInner newInner : PartialTy}
      {oldTy newTy : Ty}
      {oldEvidence : ValidPartialValueSkeleton store value oldInner}
      {newEvidence : ValidPartialValueSkeleton store value newInner}
      {oldStrength : PartialTyStrengthens oldInner (.undef oldTy)}
      {newStrength : PartialTyStrengthens newInner (.undef newTy)} :
      StrengthensSameShape
        (ValidPartialValueEvidence.undefOf oldEvidence oldStrength)
        (ValidPartialValueEvidence.undefOf newEvidence newStrength)
  | borrow {location : Location} {mutable : Bool} {leftTargets rightTargets : List LVal}
      {target : LVal} {hmem : target ∈ leftTargets}
      {hloc : store.loc target = some location}
      (hsubset : leftTargets.Subset rightTargets) :
      StrengthensSameShape
        (ValidPartialValueEvidence.borrow (mutable := mutable)
          (targets := leftTargets) target hmem hloc)
        (ValidPartialValueEvidence.borrow (mutable := mutable)
          (targets := rightTargets) target (hsubset hmem) hloc)
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
  | undef => exact ValidPartialValueEvidence.StrengthensSameShape.undef
  | undefOf hinner _hstrength =>
      exact ValidPartialValueEvidence.StrengthensSameShape.undefOf
  | @borrow location mutable targets target hmem hloc =>
      exact ValidPartialValueEvidence.StrengthensSameShape.borrow
        (mutable := mutable) (target := target) (hmem := hmem) (hloc := hloc)
        (List.Subset.refl _)
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
  | undef =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.undef,
            ValidPartialValueEvidence.StrengthensSameShape.undef⟩
      | undefLeft _ =>
          exact ⟨ValidPartialValueEvidence.undef,
            ValidPartialValueEvidence.StrengthensSameShape.undef⟩
  | undefOf hinner htoUndef =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.undefOf hinner htoUndef,
            ValidPartialValueEvidence.StrengthensSameShape.undefOf⟩
      | undefLeft hinnerStrength =>
          exact ⟨ValidPartialValueEvidence.undefOf hinner
              (partialTyStrengthens_trans_safe htoUndef
                (PartialTyStrengthens.undefLeft hinnerStrength)),
            ValidPartialValueEvidence.StrengthensSameShape.undefOf⟩
  | @borrow location mutable targets target hmem hloc =>
      cases hstrength with
      | reflex =>
          exact ⟨ValidPartialValueEvidence.borrow target hmem hloc,
            ValidPartialValueEvidence.StrengthensSameShape.borrow
              (mutable := mutable) (target := target) (hmem := hmem)
              (hloc := hloc) (List.Subset.refl _)⟩
      | borrow hsubset =>
          exact ⟨ValidPartialValueEvidence.borrow target (hsubset hmem) hloc,
            ValidPartialValueEvidence.StrengthensSameShape.borrow
              (mutable := mutable) (target := target) (hmem := hmem)
              (hloc := hloc) hsubset⟩
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
  | undef => cases hdependency
  | undefOf => cases hdependency
  | borrow _hsubset =>
      rename_i location mutable leftTargets rightTargets target hmem hloc
      cases hdependency with
      | borrow hreads =>
          exact EvidenceBorrowDependency.borrow (mutable := mutable)
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
  | _, _, ValidPartialValueEvidence.undef, _, _, _ => False
  | _, _, ValidPartialValueEvidence.undefOf _ _, _, _, _ => False
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
  | undef =>
      simp [EvidenceSelectedBorrow] at hselected
  | undefOf =>
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
  | undef =>
      simp [EvidenceSelectedBorrow] at hselected
  | undefOf =>
      simp [EvidenceSelectedBorrow] at hselected
  | borrow _hsubset =>
      rename_i location mutable leftTargets _rightTargets evidenceTarget hmem hloc
      simp [EvidenceSelectedBorrow] at hselected
      rcases hselected with ⟨hselectedMutable, htargets, htarget⟩
      cases htargets
      cases htarget
      exact ⟨leftTargets, by
        simpa [EvidenceSelectedBorrow] using hselectedMutable⟩
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

/-- Safe abstraction with concrete runtime evidence for each root slot. -/
def FullSafeAbstractionEvidence (store : ProgramStore) (env : Env) : Prop :=
  (∀ x,
    (∃ slot, store.slotAt (VariableProjection x) = some slot) ↔
      ∃ slot, env.slotAt x = some slot) ∧
  ∀ x envSlot,
    env.slotAt x = some envSlot →
    ∃ value,
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } ∧
      ∃ _evidence : ValidPartialValueEvidence store value envSlot.ty, True

theorem FullSafeAbstractionEvidence.safe {store : ProgramStore} {env : Env} :
    FullSafeAbstractionEvidence store env →
    FullSafeAbstraction store env := by
  intro hsafe
  constructor
  · exact hsafe.1
  · intro x envSlot hslot
    rcases hsafe.2 x envSlot hslot with
    ⟨value, hstore, hevidence, _⟩
    exact ⟨value, hstore, hevidence.valid⟩

theorem FullSafeAbstractionEvidence.of_safe {store : ProgramStore} {env : Env} :
    FullSafeAbstraction store env →
    FullSafeAbstractionEvidence store env := by
  intro hsafe
  constructor
  · exact hsafe.1
  · intro x envSlot hslot
    rcases hsafe.2 x envSlot hslot with ⟨value, hstore, hvalid⟩
    rcases ValidPartialValueEvidence.exists_of_valid hvalid with
      ⟨evidence, _⟩
    exact ⟨value, hstore, evidence, trivial⟩

/-- Chosen runtime evidence for roots of an environment. -/
def RuntimeEvidenceProvider (store : ProgramStore) (env : Env) : Type :=
  ∀ x envSlot value,
    env.slotAt x = some envSlot →
    store.slotAt (VariableProjection x) =
      some { value := value, lifetime := envSlot.lifetime } →
    ValidPartialValueEvidence store value envSlot.ty

/-- Selected borrow safety for a fixed runtime evidence provider. -/
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

/-- Safe abstraction plus a selected runtime alias invariant. -/
def RuntimeFullSafeAbstraction (store : ProgramStore) (env : Env) : Prop :=
  FullSafeAbstractionEvidence store env ∧
    ∃ evidenceOf : RuntimeEvidenceProvider store env,
      RuntimeSelectedBorrowSafeWith store env evidenceOf

theorem RuntimeFullSafeAbstraction.safe {store : ProgramStore} {env : Env} :
    RuntimeFullSafeAbstraction store env →
    FullSafeAbstraction store env := by
  intro hsafe
  exact FullSafeAbstractionEvidence.safe hsafe.1

theorem RuntimeFullSafeAbstraction.whenInitialized
    {store : ProgramStore} {env : Env} :
    RuntimeFullSafeAbstraction store env →
    store ∼ₛ env := by
  intro hsafe
  exact hsafe.safe.whenInitialized

/-- Runtime-selected borrow safety over all possible evidence choices. -/
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

/-- Owner-skeleton frame lemma for store updates. -/
theorem validPartialValueSkeleton_update_of_not_owner_reaches {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValueSkeleton store v ty →
      (∀ ℓ, OwnerReaches store v ty ℓ → ℓ ≠ updated) →
      ValidPartialValueSkeleton (store.update updated newSlot) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit => intro _; exact ValidPartialValueSkeleton.unit
  | int => intro _; exact ValidPartialValueSkeleton.int
  | undef => intro _; exact ValidPartialValueSkeleton.undef
  | borrow => intro _; exact ValidPartialValueSkeleton.borrow
  | undefOf hinner hstrength ih =>
      intro howners
      exact ValidPartialValueSkeleton.undefOf
        (ih (fun ℓ hℓ => howners ℓ (OwnerReaches.undefOf hinner hstrength hℓ)))
        hstrength
  | @box location slot inner hslot _hinner ih =>
      intro howners
      have hlocNe : location ≠ updated := howners location (OwnerReaches.boxHere hslot)
      refine ValidPartialValueSkeleton.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => howners ℓ (OwnerReaches.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro howners
      have hlocNe : location ≠ updated := howners location (OwnerReaches.boxFullHere hslot)
      refine ValidPartialValueSkeleton.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => howners ℓ (OwnerReaches.boxFullInner hslot hℓ))

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
  | undef => intro _; exact ValidPartialValue.undef
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValue.undefOf
        (validPartialValueSkeleton_update_of_not_owner_reaches hinner
          (fun ℓ hℓ => hreach ℓ (Reaches.undefOf hinner hstrength hℓ)))
        hstrength
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

/-- Stale-aware frame lemma for store updates.

This is the weak analogue of `validPartialValue_update_of_not_reaches`. Live
borrow annotations use the same `LocReads` frame as full validity; stale borrow
annotations do not require target resolution and are therefore store-frame
stable directly. -/
theorem validPartialValueWhenInitialized_update_of_not_reaches
    {env : Env} {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValueWhenInitialized env store v ty →
      (∀ ℓ, Reaches store v ty ℓ → ℓ ≠ updated) →
      ValidPartialValueWhenInitialized env (store.update updated newSlot) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValueWhenInitialized.undefOf
        (validPartialValueSkeleton_update_of_not_owner_reaches hinner
          (fun ℓ hℓ => hreach ℓ (Reaches.undefOf hinner hstrength hℓ)))
        hstrength
  | borrowLive hinitialized hmem hloc =>
      intro hreach
      refine ValidPartialValueWhenInitialized.borrowLive hinitialized hmem ?_
      refine loc_update_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hmem hloc hmidReads)
  | borrowStale hstale =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.borrowStale hstale
  | @box location slot inner hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated := hreach location (Reaches.boxHere hslot)
      refine ValidPartialValueWhenInitialized.box
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated := hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValueWhenInitialized.boxFull
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxFullInner hslot hℓ))

/-- Stale-aware frame lemma over `ReachesWhenInitialized`.

This is the premise shape used by preservation for weak runtime abstractions:
stale borrows are stable under store updates without requiring any target `loc`
frame proof. -/
theorem validPartialValueWhenInitialized_update_of_not_reachesWhenInitialized
    {env : Env} {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValueWhenInitialized env store v ty →
      (∀ ℓ, ReachesWhenInitialized env store v ty ℓ → ℓ ≠ updated) →
      ValidPartialValueWhenInitialized env (store.update updated newSlot) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValueWhenInitialized.undefOf
        (validPartialValueSkeleton_update_of_not_owner_reaches hinner
          (fun ℓ hℓ =>
            hreach ℓ (ReachesWhenInitialized.undefOf hinner hstrength hℓ)))
        hstrength
  | borrowLive hinitialized hmem hloc =>
      intro hreach
      refine ValidPartialValueWhenInitialized.borrowLive hinitialized hmem ?_
      refine loc_update_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid
        (ReachesWhenInitialized.borrow hinitialized hmem hloc hmidReads)
  | borrowStale hstale =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.borrowStale hstale
  | @box location slot inner hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated :=
        hreach location (ReachesWhenInitialized.boxHere hslot)
      refine ValidPartialValueWhenInitialized.box
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ =>
          hreach ℓ (ReachesWhenInitialized.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated :=
        hreach location (ReachesWhenInitialized.boxFullHere hslot)
      refine ValidPartialValueWhenInitialized.boxFull
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ =>
          hreach ℓ (ReachesWhenInitialized.boxFullInner hslot hℓ))

theorem validPartialValueWhenInitialized_update_of_owner_and_borrow_dependency_frame
    {env : Env} {store : ProgramStore} {updated : Location}
    {newSlot : StoreSlot} :
    ∀ {value : PartialValue} {ty : PartialTy}
      (_hvalid : ValidPartialValueWhenInitialized env store value ty),
      (∀ location,
        OwnerReaches store value ty location →
        location ≠ updated) →
      (∀ location,
        BorrowDependencyWhenInitialized env store value ty location →
        location ≠ updated) →
      ValidPartialValueWhenInitialized env (store.update updated newSlot) value ty := by
  intro value ty hvalid
  induction hvalid with
  | unit | int | undef =>
      intro _howners _hdeps
      constructor
  | undefOf hinner hstrength =>
      intro howners _hdeps
      exact ValidPartialValueWhenInitialized.undefOf
        (validPartialValueSkeleton_update_of_not_owner_reaches hinner
          (by
            intro reached hreach
            exact howners reached
              (OwnerReaches.undefOf hinner hstrength hreach)))
        hstrength
  | @borrowLive location mutable targets target hinitialized hmem hloc =>
      intro _howners hdeps
      refine ValidPartialValueWhenInitialized.borrowLive hinitialized hmem ?_
      exact loc_update_of_not_locReads hloc (by
        intro mid hreads
        exact hdeps mid
          (BorrowDependencyWhenInitialized.borrow hinitialized hmem hloc hreads))
  | @borrowStale location mutable targets hstale =>
      intro _howners _hdeps
      exact ValidPartialValueWhenInitialized.borrowStale
        (location := location) (mutable := mutable) (targets := targets) hstale
  | @box location slot inner hslot _hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (OwnerReaches.boxHere hslot)
      refine ValidPartialValueWhenInitialized.box
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (BorrowDependencyWhenInitialized.boxInner hslot hdependency))
  | @boxFull location slot innerTy hslot _hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (OwnerReaches.boxFullHere hslot)
      refine ValidPartialValueWhenInitialized.boxFull
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.boxFullInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (BorrowDependencyWhenInitialized.boxFullInner hslot hdependency))

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
  | undef =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.undef, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | undefOf hinner hstrength =>
      intro howners hdeps
      refine ⟨ValidPartialValueEvidence.undefOf
        (validPartialValueSkeleton_update_of_not_owner_reaches hinner
          (fun reached hreach =>
            howners reached (OwnerReaches.undefOf hinner hstrength hreach)))
        hstrength, ?_⟩
      constructor
      · intro dependency hdependency
        cases hdependency
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

The concrete preservation case supplies the variable-domain/slot facts for the
updated store and proves the write avoids every owned cell and borrow-resolution
dependency of each chosen root evidence object.
-/
theorem runtimeFullSafeAbstraction_update_of_evidence_frames
    {store : ProgramStore} {env : Env} {updated : Location}
    {newSlot : StoreSlot}
    (_hsafeEvidence : FullSafeAbstractionEvidence store env)
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
    RuntimeFullSafeAbstraction (store.update updated newSlot) env := by
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
      FullSafeAbstractionEvidence (store.update updated newSlot) env := by
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
theorem validPartialValueSkeleton_erase_of_not_owner_reaches {store : ProgramStore}
    {erased : Location} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValueSkeleton store v ty →
      (∀ ℓ, OwnerReaches store v ty ℓ → ℓ ≠ erased) →
      ValidPartialValueSkeleton (store.erase erased) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit => intro _; exact ValidPartialValueSkeleton.unit
  | int => intro _; exact ValidPartialValueSkeleton.int
  | undef => intro _; exact ValidPartialValueSkeleton.undef
  | borrow => intro _; exact ValidPartialValueSkeleton.borrow
  | undefOf hinner hstrength ih =>
      intro howners
      exact ValidPartialValueSkeleton.undefOf
        (ih (fun ℓ hℓ => howners ℓ (OwnerReaches.undefOf hinner hstrength hℓ)))
        hstrength
  | @box location slot inner hslot _hinner ih =>
      intro howners
      have hlocNe : location ≠ erased := howners location (OwnerReaches.boxHere hslot)
      refine ValidPartialValueSkeleton.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun ℓ hℓ => howners ℓ (OwnerReaches.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro howners
      have hlocNe : location ≠ erased := howners location (OwnerReaches.boxFullHere hslot)
      refine ValidPartialValueSkeleton.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun ℓ hℓ => howners ℓ (OwnerReaches.boxFullInner hslot hℓ))

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
  | undef => intro _; exact ValidPartialValue.undef
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValue.undefOf
        (validPartialValueSkeleton_erase_of_not_owner_reaches hinner
          (fun ℓ hℓ => hreach ℓ (Reaches.undefOf hinner hstrength hℓ)))
        hstrength
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

/-- A value that is valid after an erase was already valid before the erase. -/
theorem validPartialValueSkeleton_erase_to_store {store : ProgramStore}
    {erased : Location} {v : PartialValue} {ty : PartialTy} :
    ValidPartialValueSkeleton (store.erase erased) v ty →
    ValidPartialValueSkeleton store v ty := by
  intro hvalid
  induction hvalid with
  | unit => exact ValidPartialValueSkeleton.unit
  | int => exact ValidPartialValueSkeleton.int
  | undef => exact ValidPartialValueSkeleton.undef
  | borrow => exact ValidPartialValueSkeleton.borrow
  | undefOf _hinner hstrength ih =>
      exact ValidPartialValueSkeleton.undefOf ih hstrength
  | box hslot _hinner ih =>
      exact ValidPartialValueSkeleton.box (slotAt_of_erase_slotAt hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueSkeleton.boxFull (slotAt_of_erase_slotAt hslot) ih

theorem validPartialValue_erase_to_store {store : ProgramStore}
    {erased : Location} {v : PartialValue} {ty : PartialTy} :
    ValidPartialValue (store.erase erased) v ty →
    ValidPartialValue store v ty := by
  intro hvalid
  induction hvalid with
  | unit => exact ValidPartialValue.unit
  | int => exact ValidPartialValue.int
  | undef => exact ValidPartialValue.undef
  | undefOf hinner hstrength =>
      exact ValidPartialValue.undefOf
        (validPartialValueSkeleton_erase_to_store hinner) hstrength
  | borrow hmem hloc =>
      exact ValidPartialValue.borrow hmem (loc_erase_some_to_store hloc)
  | box hslot _hinner ih =>
      exact ValidPartialValue.box (slotAt_of_erase_slotAt hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValue.boxFull (slotAt_of_erase_slotAt hslot) ih

/-- Owner reachability observed after an erase was already present before it. -/
theorem ownerReaches_erase_to_store {store : ProgramStore}
    {erased : Location} {v : PartialValue} {ty : PartialTy} {location : Location} :
    OwnerReaches (store.erase erased) v ty location →
    OwnerReaches store v ty location := by
  intro hreach
  induction hreach with
  | undefOf hvalid hstrength _hinner ih =>
      exact OwnerReaches.undefOf
        (validPartialValueSkeleton_erase_to_store hvalid) hstrength ih
  | boxHere hslot =>
      exact OwnerReaches.boxHere (slotAt_of_erase_slotAt hslot)
  | boxInner hslot _hinner ih =>
      exact OwnerReaches.boxInner (slotAt_of_erase_slotAt hslot) ih
  | boxFullHere hslot =>
      exact OwnerReaches.boxFullHere (slotAt_of_erase_slotAt hslot)
  | boxFullInner hslot _hinner ih =>
      exact OwnerReaches.boxFullInner (slotAt_of_erase_slotAt hslot) ih

/-- Value reachability observed after an erase was already present in the original store. -/
theorem reaches_erase_to_store {store : ProgramStore}
    {erased : Location} {v : PartialValue} {ty : PartialTy} {location : Location} :
    Reaches (store.erase erased) v ty location →
    Reaches store v ty location := by
  intro hreach
  induction hreach with
  | undefOf hvalid hstrength hinner =>
      exact Reaches.undefOf (validPartialValueSkeleton_erase_to_store hvalid)
        hstrength (ownerReaches_erase_to_store hinner)
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

theorem reachesWhenInitialized_erase_to_store {env : Env} {store : ProgramStore}
    {erased : Location} {v : PartialValue} {ty : PartialTy}
    {location : Location} :
    ReachesWhenInitialized env (store.erase erased) v ty location →
    ReachesWhenInitialized env store v ty location := by
  intro hreach
  induction hreach with
  | undefOf hvalid hstrength hinner =>
      exact ReachesWhenInitialized.undefOf
        (validPartialValueSkeleton_erase_to_store hvalid) hstrength
        (ownerReaches_erase_to_store hinner)
  | boxHere hslot =>
      exact ReachesWhenInitialized.boxHere (slotAt_of_erase_slotAt hslot)
  | boxInner hslot _hinner ih =>
      exact ReachesWhenInitialized.boxInner (slotAt_of_erase_slotAt hslot) ih
  | boxFullHere hslot =>
      exact ReachesWhenInitialized.boxFullHere (slotAt_of_erase_slotAt hslot)
  | boxFullInner hslot _hinner ih =>
      exact ReachesWhenInitialized.boxFullInner (slotAt_of_erase_slotAt hslot) ih
  | borrow hinitialized hmem hloc hreads =>
      exact ReachesWhenInitialized.borrow hinitialized hmem
        (loc_erase_some_to_store hloc) (locReads_erase_to_store hreads)

theorem validPartialValueWhenInitialized_erase_of_not_reachesWhenInitialized
    {env : Env} {store : ProgramStore} {erased : Location} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValueWhenInitialized env store v ty →
      (∀ ℓ, ReachesWhenInitialized env store v ty ℓ → ℓ ≠ erased) →
      ValidPartialValueWhenInitialized env (store.erase erased) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValueWhenInitialized.undefOf
        (validPartialValueSkeleton_erase_of_not_owner_reaches hinner
          (fun ℓ hℓ =>
            hreach ℓ (ReachesWhenInitialized.undefOf hinner hstrength hℓ)))
        hstrength
  | borrowLive hinitialized hmem hloc =>
      intro hreach
      refine ValidPartialValueWhenInitialized.borrowLive hinitialized hmem ?_
      refine loc_erase_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid
        (ReachesWhenInitialized.borrow hinitialized hmem hloc hmidReads)
  | borrowStale hstale =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.borrowStale hstale
  | @box location slot inner hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ erased :=
        hreach location (ReachesWhenInitialized.boxHere hslot)
      refine ValidPartialValueWhenInitialized.box
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        exact hslot
        exact hlocNe
      · exact ih (fun ℓ hℓ =>
          hreach ℓ (ReachesWhenInitialized.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ erased :=
        hreach location (ReachesWhenInitialized.boxFullHere hslot)
      refine ValidPartialValueWhenInitialized.boxFull
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        exact hslot
        exact hlocNe
      · exact ih (fun ℓ hℓ =>
          hreach ℓ (ReachesWhenInitialized.boxFullInner hslot hℓ))

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

theorem validPartialValueWhenInitialized_drops_of_avoids_reachesWhenInitialized
    {env : Env} {store store' : ProgramStore} {values : List PartialValue}
    {v : PartialValue} {ty : PartialTy} :
    Drops store values store' →
    ValidPartialValueWhenInitialized env store v ty →
    (∀ location, ReachesWhenInitialized env store v ty location →
      DropsAvoids store values location) →
    ValidPartialValueWhenInitialized env store' v ty := by
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
          ∀ location, ReachesWhenInitialized env storeBefore v ty location →
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
          ValidPartialValueWhenInitialized env (storeBefore.erase ref.location) v ty :=
        validPartialValueWhenInitialized_erase_of_not_reachesWhenInitialized
          hvalid hnotErased
      exact ih hvalidErased (by
        intro location hreachErased
        have hreachStore :
            ReachesWhenInitialized env storeBefore v ty location :=
          reachesWhenInitialized_erase_to_store hreachErased
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
theorem validPartialValueSkeleton_drops_of_owner_frame
    {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ∀ {value : PartialValue} {ty : PartialTy},
      ValidPartialValueSkeleton store value ty →
      (∀ location,
        OwnerReaches store value ty location →
        DropsAvoids store values location) →
      ValidPartialValueSkeleton store' value ty := by
  intro hdrops value ty hvalid
  induction hvalid with
  | unit => intro _howners; exact ValidPartialValueSkeleton.unit
  | int => intro _howners; exact ValidPartialValueSkeleton.int
  | undef => intro _howners; exact ValidPartialValueSkeleton.undef
  | borrow => intro _howners; exact ValidPartialValueSkeleton.borrow
  | undefOf hinner hstrength ih =>
      intro howners
      exact ValidPartialValueSkeleton.undefOf
        (ih (by
          intro reached hreach
          exact howners reached (OwnerReaches.undefOf hinner hstrength hreach)))
        hstrength
  | @box location slot inner hslot hinner ih =>
      intro howners
      have hlocationAvoid : DropsAvoids store values location :=
        howners location (OwnerReaches.boxHere hslot)
      refine ValidPartialValueSkeleton.box (location := location) (slot := slot) ?_ ?_
      · exact dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      · exact ih (by
          intro reached hreach
          exact howners reached (OwnerReaches.boxInner hslot hreach))
  | @boxFull location slot innerTy hslot hinner ih =>
      intro howners
      have hlocationAvoid : DropsAvoids store values location :=
        howners location (OwnerReaches.boxFullHere hslot)
      refine ValidPartialValueSkeleton.boxFull (location := location) (slot := slot) ?_ ?_
      · exact dropsAvoids_slotAt_preserved hdrops hlocationAvoid hslot
      · exact ih (by
          intro reached hreach
          exact howners reached (OwnerReaches.boxFullInner hslot hreach))

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
  | undef =>
      intro _howners _hdeps
      exact ValidPartialValue.undef
  | undefOf hinner hstrength =>
      intro howners hdeps
      exact ValidPartialValue.undefOf
        (validPartialValueSkeleton_drops_of_owner_frame hdrops hinner
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.undefOf hinner hstrength hreach)))
        hstrength
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
  | undef =>
      intro _howners _hdeps
      exact ValidPartialValue.undef
  | undefOf hinner hstrength =>
      intro howners hdeps
      exact ValidPartialValue.undefOf
        (validPartialValueSkeleton_drops_of_owner_frame hdrops hinner
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.undefOf hinner hstrength hreach)))
        hstrength
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
  | undef =>
      intro _howners _hdeps
      refine ⟨ValidPartialValueEvidence.undef, ?_⟩
      constructor
      · intro location hdep
        cases hdep
      · intro mutable targets target hselected
        simp [EvidenceSelectedBorrow] at hselected
  | undefOf hinner hstrength =>
      intro howners hdeps
      refine ⟨ValidPartialValueEvidence.undefOf
        (validPartialValueSkeleton_drops_of_owner_frame hdrops hinner
          (by
            intro reached hreach
            exact howners reached (OwnerReaches.undefOf hinner hstrength hreach)))
        hstrength, ?_⟩
      constructor
      · intro dependency hdependency
        cases hdependency
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
-/
theorem runtimeFullSafeAbstraction_drops_of_evidence_frames
    {store store' : ProgramStore} {env : Env} {values : List PartialValue}
    (_hsafeEvidence : FullSafeAbstractionEvidence store env)
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
    RuntimeFullSafeAbstraction store' env := by
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
  have hsafeEvidence' : FullSafeAbstractionEvidence store' env := by
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

theorem reaches_owner_source_of_validPartialValue_core
    {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    ValidPartialValueSkeleton store value ty →
    OwnerReaches store value ty location →
    location ∈ partialValueOwningLocations value ∨
      ∃ storage,
        OwnerReaches store value ty storage ∧
          ProgramStore.OwnsAt store location storage := by
  intro hvalid
  intro hreach
  induction hreach with
  | undefOf hvalidOld hstrength _hinnerReach ih =>
      rcases ih hvalidOld with howned | hsource
      · exact Or.inl howned
      · rcases hsource with ⟨storage, hstorageReach, howns⟩
        exact Or.inr ⟨storage,
          OwnerReaches.undefOf hvalidOld hstrength hstorageReach, howns⟩
  | boxHere hslot =>
      exact Or.inl (by
        simp [partialValueOwningLocations, valueOwningLocations,
          valueOwnedLocation?])
  | @boxInner ownerLocation slot inner reached hslot _hinnerReach ih =>
      cases hvalid with
      | @box validLocation validSlot validInner hslotValid hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hslot] at hslotValid
            injection hslotValid
          cases hslotEq
          rcases ih hinnerValid with howned | hsource
          · exact Or.inr ⟨ownerLocation, OwnerReaches.boxHere hslot,
              slot.lifetime, by
                have hslotValue : slot.value = .value (owningRef reached) :=
                  eq_owningRef_of_mem_partialValueOwningLocations howned
                cases slot with
                | mk slotValue slotLifetime =>
                    cases hslotValue
                    simpa using hslot⟩
          · rcases hsource with ⟨storage, hstorageReach, howns⟩
            exact Or.inr ⟨storage, OwnerReaches.boxInner hslot hstorageReach, howns⟩
  | boxFullHere hslot =>
      exact Or.inl (by
        simp [partialValueOwningLocations, valueOwningLocations,
          valueOwnedLocation?])
  | @boxFullInner ownerLocation slot innerTy reached hslot _hinnerReach ih =>
      cases hvalid with
      | @boxFull validLocation validSlot validInnerTy hslotValid hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hslot] at hslotValid
            injection hslotValid
          cases hslotEq
          rcases ih hinnerValid with howned | hsource
          · exact Or.inr ⟨ownerLocation, OwnerReaches.boxFullHere hslot,
              slot.lifetime, by
                have hslotValue : slot.value = .value (owningRef reached) :=
                  eq_owningRef_of_mem_partialValueOwningLocations howned
                cases slot with
                | mk slotValue slotLifetime =>
                    cases hslotValue
                    simpa using hslot⟩
          · rcases hsource with ⟨storage, hstorageReach, howns⟩
            exact Or.inr ⟨storage, OwnerReaches.boxFullInner hslot hstorageReach, howns⟩

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
  intro _hborrows hvalid hreach
  exact reaches_owner_source_of_validPartialValue_core hvalid.skeleton hreach

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
  | undefOf _hvalid _hstrength _hinner ih =>
      exact ih hstored
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

theorem dropsAvoids_of_ownerReaches_stored_skeleton
    {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ValidStore store →
    ∀ {storageLifetime : Lifetime} {storage : Location}
      {storedValue : PartialValue} {partialTy : PartialTy} {location : Location},
      store.slotAt storage =
        some { value := storedValue, lifetime := storageLifetime } →
      ValidPartialValueSkeleton store storedValue partialTy →
      DropsAvoids store values storage →
      (∀ reached,
        OwnerReaches store storedValue partialTy reached →
        ∀ dropValue, dropValue ∈ values →
          reached ∉ partialValueOwningLocations dropValue) →
      OwnerReaches store storedValue partialTy location →
      DropsAvoids store values location := by
  intro hdrops hvalidStore storageLifetime storage storedValue partialTy location
    hstored hvalid havoidStorage hdisjoint hreach
  induction hreach generalizing storage storageLifetime havoidStorage with
  | undefOf hvalidOld hstrength hinnerReach ih =>
      exact ih
        (storage := storage) (storageLifetime := storageLifetime)
        hstored hvalidOld havoidStorage
        (by
          intro reached howner dropValue hmem howned
          exact hdisjoint reached
            (OwnerReaches.undefOf hvalidOld hstrength howner)
            dropValue hmem howned)
  | @boxHere ownerLocation slot inner hreachSlot =>
      have howns : ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨storageLifetime, hstored⟩
      exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
        havoidStorage (by
          intro dropValue hmem howned
          exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
            dropValue hmem howned)
  | @boxInner ownerLocation slot inner reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @box validLocation validSlot validInner hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
              havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                  dropValue hmem howned)
          exact ih
            (storage := ownerLocation) (storageLifetime := slot.lifetime)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxInner hreachSlot hinnerReached)
                dropValue hmem howned)
  | @boxFullHere ownerLocation slot innerTy hreachSlot =>
      have howns : ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨storageLifetime, hstored⟩
      exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
        havoidStorage (by
          intro dropValue hmem howned
          exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
            dropValue hmem howned)
  | @boxFullInner ownerLocation slot innerTy reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @boxFull validLocation validSlot validInnerTy hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
              havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                  dropValue hmem howned)
          exact ih
            (storage := ownerLocation) (storageLifetime := slot.lifetime)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxFullInner hreachSlot hinnerReached)
                dropValue hmem howned)

theorem dropsAvoids_of_reaches_stored_validPartialValue_core
    {store store' : ProgramStore} {values : List PartialValue} :
    Drops store values store' →
    ValidStore store →
    ∀ {storageLifetime : Lifetime} {storage : Location}
      {storedValue : PartialValue} {partialTy : PartialTy} {location : Location},
      store.slotAt storage =
        some { value := storedValue, lifetime := storageLifetime } →
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
  intro hdrops hvalidStore storageLifetime storage storedValue partialTy location
    hstored hvalid havoidStorage hdisjoint hborrowAvoids hreach
  induction hreach generalizing storage storageLifetime havoidStorage with
  | undefOf hvalidOld hstrength hinnerReach =>
      exact dropsAvoids_of_ownerReaches_stored_skeleton hdrops hvalidStore
        hstored hvalidOld havoidStorage
        (by
          intro reached howner dropValue hmem howned
          exact hdisjoint reached
            (OwnerReaches.undefOf hvalidOld hstrength howner)
            dropValue hmem howned)
        hinnerReach
  | borrow hmem hloc hreads =>
      exact hborrowAvoids _
        (BorrowDependency.borrow hmem hloc hreads)
  | @boxHere ownerLocation slot inner hreachSlot =>
      have howns : ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨storageLifetime, hstored⟩
      exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
        havoidStorage (by
          intro dropValue hmem howned
          exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
            dropValue hmem howned)
  | @boxInner ownerLocation slot inner reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @box validLocation validSlot validInner hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
              havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                  dropValue hmem howned)
          exact ih
            (storage := ownerLocation) (storageLifetime := slot.lifetime)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxInner hreachSlot hinnerReached)
                dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependency.boxInner hreachSlot hdependency))
  | @boxFullHere ownerLocation slot innerTy hreachSlot =>
      have howns : ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨storageLifetime, hstored⟩
      exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
        havoidStorage (by
          intro dropValue hmem howned
          exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
            dropValue hmem howned)
  | @boxFullInner ownerLocation slot innerTy reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @boxFull validLocation validSlot validInnerTy hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
              havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                  dropValue hmem howned)
          exact ih
            (storage := ownerLocation) (storageLifetime := slot.lifetime)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxFullInner hreachSlot hinnerReached)
                dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependency.boxFullInner hreachSlot hdependency))

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
  exact dropsAvoids_of_reaches_stored_validPartialValue_core hdrops hvalidStore
    hstored hvalid havoidStorage hdisjoint hborrowAvoids hreach

/--
If the direct owners carried by a valid value are disjoint from the store, then
every location reached by the value is protected from a drop list whose explicit
owners are disjoint from that reachability footprint.
-/
theorem dropsAvoids_of_ownerReaches_skeleton
    {store store' : ProgramStore} {values : List PartialValue}
    {value : PartialValue} {partialTy : PartialTy} {location : Location} :
    Drops store values store' →
    ValidStore store →
    ValidPartialValueSkeleton store value partialTy →
      (∀ owned,
        owned ∈ partialValueOwningLocations value →
          ¬ ProgramStore.Owns store owned) →
      (∀ reached,
        OwnerReaches store value partialTy reached →
        ∀ dropValue, dropValue ∈ values →
          reached ∉ partialValueOwningLocations dropValue) →
    OwnerReaches store value partialTy location →
    DropsAvoids store values location := by
  intro hdrops hvalidStore hvalid hnotStoreOwned hdisjoint hreach
  induction hreach with
  | undefOf hvalidOld hstrength hinnerReach ih =>
      exact ih hvalidOld hnotStoreOwned (by
        intro reached howner dropValue hmem howned
        exact hdisjoint reached
          (OwnerReaches.undefOf hvalidOld hstrength howner) dropValue hmem howned)
  | @boxHere ownerLocation slot inner hreachSlot =>
      exact dropsAvoids_of_not_owns_and_not_mem hdrops
        (by
          intro dropValue hmem
          exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
            dropValue hmem)
        (hnotStoreOwned ownerLocation (by
          simp [partialValueOwningLocations, valueOwningLocations,
            valueOwnedLocation?]))
  | @boxInner ownerLocation slot inner reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @box validLocation validSlot validInner hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                  dropValue hmem)
              (hnotStoreOwned ownerLocation (by
                simp [partialValueOwningLocations, valueOwningLocations,
                  valueOwnedLocation?]))
          exact dropsAvoids_of_ownerReaches_stored_skeleton hdrops hvalidStore
            (storageLifetime := slot.lifetime) (storage := ownerLocation)
            (storedValue := slot.value) (partialTy := inner)
            (location := reached)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxInner hreachSlot hinnerReached) dropValue hmem howned)
            hinnerReach
  | @boxFullHere ownerLocation slot innerTy hreachSlot =>
      exact dropsAvoids_of_not_owns_and_not_mem hdrops
        (by
          intro dropValue hmem
          exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
            dropValue hmem)
        (hnotStoreOwned ownerLocation (by
          simp [partialValueOwningLocations, valueOwningLocations,
            valueOwnedLocation?]))
  | @boxFullInner ownerLocation slot innerTy reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @boxFull validLocation validSlot validInnerTy hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                  dropValue hmem)
              (hnotStoreOwned ownerLocation (by
                simp [partialValueOwningLocations, valueOwningLocations,
                  valueOwnedLocation?]))
          exact dropsAvoids_of_ownerReaches_stored_skeleton hdrops hvalidStore
            (storageLifetime := slot.lifetime) (storage := ownerLocation)
            (storedValue := slot.value) (partialTy := .ty innerTy)
            (location := reached)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxFullInner hreachSlot hinnerReached) dropValue hmem howned)
            hinnerReach

theorem dropsAvoids_of_reaches_validPartialValue_core
    {store store' : ProgramStore} {values : List PartialValue}
    {value : PartialValue} {partialTy : PartialTy} {location : Location} :
    Drops store values store' →
    ValidStore store →
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
  intro hdrops hvalidStore hvalid hnotStoreOwned hdisjoint hborrowAvoids hreach
  induction hreach with
  | undefOf hvalidOld hstrength hinnerReach =>
      exact dropsAvoids_of_ownerReaches_skeleton hdrops hvalidStore
        hvalidOld hnotStoreOwned
        (by
          intro reached howner dropValue hmem howned
          exact hdisjoint reached
            (OwnerReaches.undefOf hvalidOld hstrength howner)
            dropValue hmem howned)
        hinnerReach
  | borrow hmem hloc hreads =>
      exact hborrowAvoids _
        (BorrowDependency.borrow hmem hloc hreads)
  | @boxHere ownerLocation slot inner hreachSlot =>
      exact dropsAvoids_of_not_owns_and_not_mem hdrops
        (by
          intro dropValue hmem
          exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
            dropValue hmem)
        (hnotStoreOwned ownerLocation (by
          simp [partialValueOwningLocations, valueOwningLocations,
            valueOwnedLocation?]))
  | @boxInner ownerLocation slot inner reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @box validLocation validSlot validInner hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                  dropValue hmem)
              (hnotStoreOwned ownerLocation (by
                simp [partialValueOwningLocations, valueOwningLocations,
                  valueOwnedLocation?]))
          exact dropsAvoids_of_reaches_stored_validPartialValue_core
            hdrops hvalidStore
            (storageLifetime := slot.lifetime) (storage := ownerLocation)
            (storedValue := slot.value) (partialTy := inner)
            (location := reached)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxInner hreachSlot hinnerReached) dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependency.boxInner hreachSlot hdependency))
            hinnerReach
  | @boxFullHere ownerLocation slot innerTy hreachSlot =>
      exact dropsAvoids_of_not_owns_and_not_mem hdrops
        (by
          intro dropValue hmem
          exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
            dropValue hmem)
        (hnotStoreOwned ownerLocation (by
          simp [partialValueOwningLocations, valueOwningLocations,
            valueOwnedLocation?]))
  | @boxFullInner ownerLocation slot innerTy reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @boxFull validLocation validSlot validInnerTy hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                  dropValue hmem)
              (hnotStoreOwned ownerLocation (by
                simp [partialValueOwningLocations, valueOwningLocations,
                  valueOwnedLocation?]))
          exact dropsAvoids_of_reaches_stored_validPartialValue_core
            hdrops hvalidStore
            (storageLifetime := slot.lifetime) (storage := ownerLocation)
            (storedValue := slot.value) (partialTy := .ty innerTy)
            (location := reached)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxFullInner hreachSlot hinnerReached)
                dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependency.boxFullInner hreachSlot hdependency))
            hinnerReach

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
  exact dropsAvoids_of_reaches_validPartialValue_core hdrops hvalidStore
    hvalid hnotStoreOwned hdisjoint hborrowAvoids hreach

theorem store_owns_of_reaches_stored_validPartialValueWhenInitialized
    {store : ProgramStore} {storageLifetime : Lifetime}
    {storage : Location} {storedValue : PartialValue} {partialTy : PartialTy}
    {env : Env} {location : Location} :
    store.slotAt storage =
      some { value := storedValue, lifetime := storageLifetime } →
    ValidPartialValueWhenInitialized env store storedValue partialTy →
    OwnerReaches store storedValue partialTy location →
    ProgramStore.Owns store location := by
  intro hstored hvalid hreach
  rcases reaches_owner_source_of_validPartialValue_core hvalid.skeleton hreach with
    hdirect | hsource
  · have hstoredValue : storedValue = .value (owningRef location) :=
      eq_owningRef_of_mem_partialValueOwningLocations hdirect
    exact ⟨storage, storageLifetime, by
      cases hstoredValue
      simpa [owningRef] using hstored⟩
  · rcases hsource with ⟨sourceStorage, _hsourceReach, howns⟩
    exact ⟨sourceStorage, howns⟩

theorem dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized_core
    {store store' : ProgramStore} {values : List PartialValue}
    {env : Env} :
    Drops store values store' →
    ValidStore store →
    ∀ {storageLifetime : Lifetime} {storage : Location}
      {storedValue : PartialValue} {partialTy : PartialTy} {location : Location},
      store.slotAt storage =
        some { value := storedValue, lifetime := storageLifetime } →
      ValidPartialValueWhenInitialized env store storedValue partialTy →
      DropsAvoids store values storage →
      (∀ reached,
        OwnerReaches store storedValue partialTy reached →
        ∀ dropValue, dropValue ∈ values →
          reached ∉ partialValueOwningLocations dropValue) →
      (∀ dependency,
        BorrowDependencyWhenInitialized env store storedValue partialTy dependency →
          DropsAvoids store values dependency) →
      ReachesWhenInitialized env store storedValue partialTy location →
      DropsAvoids store values location := by
  intro hdrops hvalidStore storageLifetime storage storedValue partialTy location
    hstored hvalid havoidStorage hdisjoint hborrowAvoids hreach
  induction hreach generalizing storage storageLifetime havoidStorage with
  | undefOf hvalidOld hstrength hinnerReach =>
      exact dropsAvoids_of_ownerReaches_stored_skeleton hdrops hvalidStore
        hstored hvalidOld havoidStorage
        (by
          intro reached howner dropValue hmem howned
          exact hdisjoint reached
            (OwnerReaches.undefOf hvalidOld hstrength howner)
            dropValue hmem howned)
        hinnerReach
  | borrow _hinitialized hmem hloc hreads =>
      exact hborrowAvoids _
        (BorrowDependencyWhenInitialized.borrow _hinitialized hmem hloc hreads)
  | @boxHere ownerLocation slot inner hreachSlot =>
      have howns : ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨storageLifetime, hstored⟩
      exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore
        howns havoidStorage (by
          intro dropValue hmem howned
          exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
            dropValue hmem howned)
  | @boxInner ownerLocation slot inner reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @box validLocation validSlot validInner hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore
              howns havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                  dropValue hmem howned)
          exact ih
            (storage := ownerLocation) (storageLifetime := slot.lifetime)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxInner hreachSlot hinnerReached)
                dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependencyWhenInitialized.boxInner hreachSlot hdependency))
  | @boxFullHere ownerLocation slot innerTy hreachSlot =>
      have howns : ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨storageLifetime, hstored⟩
      exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore
        howns havoidStorage (by
          intro dropValue hmem howned
          exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
            dropValue hmem howned)
  | @boxFullInner ownerLocation slot innerTy reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @boxFull validLocation validSlot validInnerTy hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore
              howns havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                  dropValue hmem howned)
          exact ih
            (storage := ownerLocation) (storageLifetime := slot.lifetime)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxFullInner hreachSlot hinnerReached)
                dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependencyWhenInitialized.boxFullInner hreachSlot hdependency))

theorem dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized
    {store store' : ProgramStore} {values : List PartialValue}
    {env : Env} {storageLifetime : Lifetime}
    {storage : Location} {storedValue : PartialValue} {partialTy : PartialTy}
    {location : Location} :
    Drops store values store' →
    ValidStore store →
    store.slotAt storage =
      some { value := storedValue, lifetime := storageLifetime } →
    ValidPartialValueWhenInitialized env store storedValue partialTy →
    DropsAvoids store values storage →
    (∀ reached,
      OwnerReaches store storedValue partialTy reached →
      ∀ dropValue, dropValue ∈ values →
        reached ∉ partialValueOwningLocations dropValue) →
    (∀ dependency,
      BorrowDependencyWhenInitialized env store storedValue partialTy dependency →
        DropsAvoids store values dependency) →
    ReachesWhenInitialized env store storedValue partialTy location →
    DropsAvoids store values location := by
  intro hdrops hvalidStore hstored hvalid havoidStorage hdisjoint
    hborrowAvoids hreach
  exact dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized_core
    hdrops hvalidStore hstored hvalid havoidStorage hdisjoint
    hborrowAvoids hreach

theorem dropsAvoids_of_reaches_validPartialValueWhenInitialized_core
    {store store' : ProgramStore} {values : List PartialValue}
    {env : Env} {value : PartialValue} {partialTy : PartialTy}
    {location : Location} :
    Drops store values store' →
    ValidStore store →
    ValidPartialValueWhenInitialized env store value partialTy →
      (∀ owned,
        owned ∈ partialValueOwningLocations value →
          ¬ ProgramStore.Owns store owned) →
      (∀ reached,
        OwnerReaches store value partialTy reached →
        ∀ dropValue, dropValue ∈ values →
          reached ∉ partialValueOwningLocations dropValue) →
    (∀ dependency,
      BorrowDependencyWhenInitialized env store value partialTy dependency →
        DropsAvoids store values dependency) →
    ReachesWhenInitialized env store value partialTy location →
    DropsAvoids store values location := by
  intro hdrops hvalidStore hvalid hnotStoreOwned hdisjoint hborrowAvoids hreach
  induction hreach with
  | undefOf hvalidOld hstrength hinnerReach =>
      exact dropsAvoids_of_ownerReaches_skeleton hdrops hvalidStore
        hvalidOld hnotStoreOwned
        (by
          intro reached howner dropValue hmem howned
          exact hdisjoint reached
            (OwnerReaches.undefOf hvalidOld hstrength howner)
            dropValue hmem howned)
        hinnerReach
  | borrow _hinitialized hmem hloc hreads =>
      exact hborrowAvoids _
        (BorrowDependencyWhenInitialized.borrow _hinitialized hmem hloc hreads)
  | @boxHere ownerLocation slot inner hreachSlot =>
      exact dropsAvoids_of_not_owns_and_not_mem hdrops
        (by
          intro dropValue hmem
          exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
            dropValue hmem)
        (hnotStoreOwned ownerLocation (by
          simp [partialValueOwningLocations, valueOwningLocations,
            valueOwnedLocation?]))
  | @boxInner ownerLocation slot inner reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @box validLocation validSlot validInner hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (OwnerReaches.boxHere hreachSlot)
                  dropValue hmem)
              (hnotStoreOwned ownerLocation (by
                simp [partialValueOwningLocations, valueOwningLocations,
                  valueOwnedLocation?]))
          exact dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized_core
            hdrops hvalidStore
            (storageLifetime := slot.lifetime) (storage := ownerLocation)
            (storedValue := slot.value) (partialTy := inner)
            (location := reached)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxInner hreachSlot hinnerReached) dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependencyWhenInitialized.boxInner hreachSlot hdependency))
            hinnerReach
  | @boxFullHere ownerLocation slot innerTy hreachSlot =>
      exact dropsAvoids_of_not_owns_and_not_mem hdrops
        (by
          intro dropValue hmem
          exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
            dropValue hmem)
        (hnotStoreOwned ownerLocation (by
          simp [partialValueOwningLocations, valueOwningLocations,
            valueOwnedLocation?]))
  | @boxFullInner ownerLocation slot innerTy reached hreachSlot hinnerReach ih =>
      cases hvalid with
      | @boxFull validLocation validSlot validInnerTy hvalidSlot hinnerValid =>
          have hslotEq : slot = validSlot := by
            rw [hreachSlot] at hvalidSlot
            injection hvalidSlot
          cases hslotEq
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hreachSlot)
                  dropValue hmem)
              (hnotStoreOwned ownerLocation (by
                simp [partialValueOwningLocations, valueOwningLocations,
                  valueOwnedLocation?]))
          exact dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized_core
            hdrops hvalidStore
            (storageLifetime := slot.lifetime) (storage := ownerLocation)
            (storedValue := slot.value) (partialTy := .ty innerTy)
            (location := reached)
            (by
              cases slot with
              | mk slotValue slotLifetime =>
                  simpa using hreachSlot)
            hinnerValid hrootAvoid
            (by
              intro innerReached hinnerReached dropValue hmem howned
              exact hdisjoint innerReached
                (OwnerReaches.boxFullInner hreachSlot hinnerReached)
                dropValue hmem howned)
            (by
              intro dependency hdependency
              exact hborrowAvoids dependency
                (BorrowDependencyWhenInitialized.boxFullInner hreachSlot hdependency))
            hinnerReach

theorem dropsAvoids_of_reaches_validPartialValueWhenInitialized
    {store store' : ProgramStore} {values : List PartialValue}
    {env : Env} {value : PartialValue} {partialTy : PartialTy}
    {location : Location} :
    Drops store values store' →
    ValidStore store →
    ValidPartialValueWhenInitialized env store value partialTy →
    (∀ owned,
      owned ∈ partialValueOwningLocations value →
        ¬ ProgramStore.Owns store owned) →
    (∀ reached,
      OwnerReaches store value partialTy reached →
      ∀ dropValue, dropValue ∈ values →
        reached ∉ partialValueOwningLocations dropValue) →
    (∀ dependency,
      BorrowDependencyWhenInitialized env store value partialTy dependency →
        DropsAvoids store values dependency) →
    ReachesWhenInitialized env store value partialTy location →
    DropsAvoids store values location := by
  intro hdrops hvalidStore hvalid hnotStoreOwned hdisjoint hborrowAvoids hreach
  exact dropsAvoids_of_reaches_validPartialValueWhenInitialized_core
    hdrops hvalidStore hvalid hnotStoreOwned hdisjoint hborrowAvoids hreach

end RuntimeFrame

end Paper
end LwRust
