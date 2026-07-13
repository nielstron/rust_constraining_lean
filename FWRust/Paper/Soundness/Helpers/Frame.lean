import FWRust.Paper.Soundness.Helpers.RuntimeFacts

/-!
# Soundness helpers: store-update frame facts

Compact frame lemmas for the single-target core.
-/

namespace FWRust
namespace Paper

open Core

namespace RuntimeFrame

theorem ProgramStore.slotAt_update_ne {store : ProgramStore}
    {updated location : Location} {slot : StoreSlot} :
    location ≠ updated →
    (store.update updated slot).slotAt location = store.slotAt location := by
  intro hne
  simp [ProgramStore.update, hne]

inductive LocReads (store : ProgramStore) : LVal → Location → Prop where
  | here {lv : LVal} {location : Location} :
      store.loc lv = some location →
      LocReads store (.deref lv) location
  | there {lv : LVal} {location : Location} :
      LocReads store lv location →
      LocReads store (.deref lv) location

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

theorem slotAt_of_erase_slotAt {store : ProgramStore}
    {erased location : Location} {slot : StoreSlot} :
    (store.erase erased).slotAt location = some slot →
    store.slotAt location = some slot := by
  intro hslot
  by_cases h : location = erased
  · subst h
    simp [ProgramStore.erase] at hslot
  · simpa [ProgramStore.erase, h] using hslot

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
      simp [ProgramStore.loc] at hloc ⊢
      cases hsource : (store.erase erased).loc lv with
      | none => simp [hsource] at hloc
      | some source =>
          have hsourceStore : store.loc lv = some source := ih hsource
          cases hslot : (store.erase erased).slotAt source with
          | none => simp [ProgramStore.loc, hsource, hslot] at hloc
          | some slot =>
              have hslotStore : store.slotAt source = some slot :=
                slotAt_of_erase_slotAt hslot
              simpa [ProgramStore.loc, hsource, hslot, hsourceStore, hslotStore] using hloc

theorem locReads_erase_to_store {store : ProgramStore}
    {erased : Location} {lv : LVal} {location : Location} :
    LocReads (store.erase erased) lv location →
    LocReads store lv location := by
  intro hreads
  induction hreads with
  | here hloc =>
      exact LocReads.here (loc_erase_some_to_store hloc)
  | there _ ih =>
      exact LocReads.there ih

inductive OwnerReaches (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | undefOf {value : PartialValue} {oldTy : PartialTy} {ty : Ty} {ℓ : Location} :
      ValidPartialValueSkeleton store value oldTy →
      PartialTyStrengthens oldTy (.undef ty) →
      OwnerReaches store value oldTy ℓ →
      OwnerReaches store value (.undef ty) ℓ
  | boxHere {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      OwnerReaches store (.value (.ref { location := location, owner := true }))
        (.box inner) location
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {ℓ : Location} :
      store.slotAt location = some slot →
      OwnerReaches store slot.value inner ℓ →
      OwnerReaches store (.value (.ref { location := location, owner := true }))
        (.box inner) ℓ
  | boxFullHere {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      OwnerReaches store (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) location
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {ℓ : Location} :
      store.slotAt location = some slot →
      OwnerReaches store slot.value (.ty ty) ℓ →
      OwnerReaches store (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) ℓ

inductive Reaches (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | undefOf {value : PartialValue} {oldTy : PartialTy} {ty : Ty} {ℓ : Location} :
      ValidPartialValueSkeleton store value oldTy →
      PartialTyStrengthens oldTy (.undef ty) →
      OwnerReaches store value oldTy ℓ →
      Reaches store value (.undef ty) ℓ
  | boxHere {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      Reaches store (.value (.ref { location := location, owner := true }))
        (.box inner) location
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {ℓ : Location} :
      store.slotAt location = some slot →
      Reaches store slot.value inner ℓ →
      Reaches store (.value (.ref { location := location, owner := true }))
        (.box inner) ℓ
  | boxFullHere {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      Reaches store (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) location
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {ℓ : Location} :
      store.slotAt location = some slot →
      Reaches store slot.value (.ty ty) ℓ →
      Reaches store (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) ℓ
  | borrow {location ℓ : Location} {mutable : Bool} {target : LVal} :
      store.loc target = some location →
      LocReads store target ℓ →
      Reaches store (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable target)) ℓ

theorem OwnerReaches.reaches {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    OwnerReaches store value ty location →
    Reaches store value ty location := by
  intro h
  induction h with
  | undefOf hvalid hstrength _ ih => exact Reaches.undefOf hvalid hstrength (by assumption)
  | boxHere hslot => exact Reaches.boxHere hslot
  | boxInner hslot _ ih => exact Reaches.boxInner hslot ih
  | boxFullHere hslot => exact Reaches.boxFullHere hslot
  | boxFullInner hslot _ ih => exact Reaches.boxFullInner hslot ih

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
  | box hslot _hinner ih =>
      intro howners
      rename_i location slot inner
      have hlocNe : location ≠ updated := howners location (OwnerReaches.boxHere hslot)
      refine ValidPartialValueSkeleton.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => howners ℓ (OwnerReaches.boxInner hslot hℓ))
  | boxFull hslot _hinner ih =>
      intro howners
      rename_i location slot ty
      have hlocNe : location ≠ updated := howners location (OwnerReaches.boxFullHere hslot)
      refine ValidPartialValueSkeleton.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => howners ℓ (OwnerReaches.boxFullInner hslot hℓ))

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
  | borrow hloc =>
      intro hreach
      refine ValidPartialValue.borrow ?_
      refine loc_update_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hloc hmidReads)
  | box hslot _hinner ih =>
      intro hreach
      rename_i location slot inner
      have hlocNe : location ≠ updated := hreach location (Reaches.boxHere hslot)
      refine ValidPartialValue.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxInner hslot hℓ))
  | boxFull hslot _hinner ih =>
      intro hreach
      rename_i location slot ty
      have hlocNe : location ≠ updated := hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxFullInner hslot hℓ))

theorem validPartialValueWhenInitialized_update_of_not_reaches {env : Env}
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot} :
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
  | borrowLive hinitialized hloc =>
      intro hreach
      refine ValidPartialValueWhenInitialized.borrowLive hinitialized ?_
      refine loc_update_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hloc hmidReads)
  | borrowStale hstale =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.borrowStale hstale
  | box hslot _hinner ih =>
      intro hreach
      rename_i location slot inner
      have hlocNe : location ≠ updated := hreach location (Reaches.boxHere hslot)
      refine ValidPartialValueWhenInitialized.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxInner hslot hℓ))
  | boxFull hslot _hinner ih =>
      intro hreach
      rename_i location slot ty
      have hlocNe : location ≠ updated := hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValueWhenInitialized.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxFullInner hslot hℓ))

theorem validValue_update_of_not_reaches {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} {value : Value} {ty : Ty} :
    ValidValue store value ty →
    (∀ ℓ, Reaches store (.value value) (.ty ty) ℓ → ℓ ≠ updated) →
    ValidValue (store.update updated newSlot) value ty :=
  validPartialValue_update_of_not_reaches

theorem validPartialValueSkeleton_erase_to_store {store : ProgramStore}
    {erased : Location} {value : PartialValue} {ty : PartialTy} :
    ValidPartialValueSkeleton (store.erase erased) value ty →
    ValidPartialValueSkeleton store value ty := by
  intro hvalid
  induction hvalid with
  | unit => exact ValidPartialValueSkeleton.unit
  | int => exact ValidPartialValueSkeleton.int
  | undef => exact ValidPartialValueSkeleton.undef
  | borrow => exact ValidPartialValueSkeleton.borrow
  | undefOf hinner hstrength ih => exact ValidPartialValueSkeleton.undefOf ih hstrength
  | box hslot _ ih =>
      exact ValidPartialValueSkeleton.box (slotAt_of_erase_slotAt hslot) ih
  | boxFull hslot _ ih =>
      exact ValidPartialValueSkeleton.boxFull (slotAt_of_erase_slotAt hslot) ih

theorem validPartialValue_erase_to_store {store : ProgramStore}
    {erased : Location} {value : PartialValue} {ty : PartialTy} :
    ValidPartialValue (store.erase erased) value ty →
    ValidPartialValue store value ty := by
  intro hvalid
  induction hvalid with
  | unit => exact ValidPartialValue.unit
  | int => exact ValidPartialValue.int
  | undef => exact ValidPartialValue.undef
  | borrow hloc =>
      exact ValidPartialValue.borrow (loc_erase_some_to_store hloc)
  | box hslot _ ih =>
      exact ValidPartialValue.box (slotAt_of_erase_slotAt hslot) ih
  | boxFull hslot _ ih =>
      exact ValidPartialValue.boxFull (slotAt_of_erase_slotAt hslot) ih

end RuntimeFrame

end Paper
end FWRust
