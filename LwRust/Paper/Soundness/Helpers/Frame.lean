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

theorem LocReads.false_of_lvalIsVar {store : ProgramStore} {lv : LVal}
    {location : Location} :
    LValIsVar lv →
    ¬ LocReads store lv location := by
  intro hvar hreads
  cases lv with
  | var _ =>
      cases hreads
  | deref _ =>
      cases hvar

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

/-- Ground unit values inspect no store location. -/
theorem reaches_unit_false {store : ProgramStore} {ℓ : Location} :
    ¬ Reaches store (.value .unit) (.ty .unit) ℓ := by
  intro h
  cases h

/-- Integer values inspect no store location. -/
theorem reaches_int_false {store : ProgramStore} {n : Int} {ℓ : Location} :
    ¬ Reaches store (.value (.int n)) (.ty .int) ℓ := by
  intro h
  cases h

/-- Undefined partial values inspect no store location. -/
theorem reaches_undef_false {store : ProgramStore} {ty : Ty} {ℓ : Location} :
    ¬ Reaches store .undef (.undef ty) ℓ := by
  intro h
  cases h

/-- `ValidValue` specialization of the store-update frame. -/
theorem validValue_update_of_not_reaches {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} {value : Value} {ty : Ty} :
    ValidValue store value ty →
    (∀ ℓ, Reaches store (.value value) (.ty ty) ℓ → ℓ ≠ updated) →
    ValidValue (store.update updated newSlot) value ty :=
  validPartialValue_update_of_not_reaches

/-- `ValidValue` specialization of the store-erase frame. -/
theorem validValue_erase_of_not_reaches {store : ProgramStore}
    {erased : Location} {value : Value} {ty : Ty} :
    ValidValue store value ty →
    (∀ ℓ, Reaches store (.value value) (.ty ty) ℓ → ℓ ≠ erased) →
    ValidValue (store.erase erased) value ty :=
  validPartialValue_erase_of_not_reaches

/-- `ValidValue` specialization of the recursive-drop frame. -/
theorem validValue_drops_of_avoids_reaches {store store' : ProgramStore}
    {values : List PartialValue} {value : Value} {ty : Ty} :
    Drops store values store' →
    ValidValue store value ty →
    (∀ location, Reaches store (.value value) (.ty ty) location →
      DropsAvoids store values location) →
    ValidValue store' value ty :=
  validPartialValue_drops_of_avoids_reaches

theorem reaches_owning_or_store_owns_of_validPartialValue {env : Env}
    {store : ProgramStore} {slotLifetime : Lifetime}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    PartialTyBorrowsWellFormedInSlot env slotLifetime ty →
    ValidPartialValue store value ty →
    Reaches store value ty location →
    location ∈ partialValueOwningLocations value ∨ ProgramStore.Owns store location := by
  intro hborrows hvalid
  induction hvalid generalizing env slotLifetime location with
  | unit =>
      intro hreach
      cases hreach
  | int =>
      intro hreach
      cases hreach
  | undef =>
      intro hreach
      cases hreach
  | borrow _hmem _hloc =>
      intro hreach
      cases hreach with
      | @borrow _location _readLocation _mutable _targets target htargetMem _hloc hreads =>
          rcases hborrows PartialTyContains.here target htargetMem with
            ⟨_targetTy, _targetLifetime, _htargetTyping, _hlifetime,
              _hbaseOutlives, hvar⟩
          exact False.elim (LocReads.false_of_lvalIsVar hvar hreads)
  | @box ownerLocation slot inner hslot _hinner ih =>
      intro hreach
      cases hreach with
      | boxHere _hslot =>
          exact Or.inl (by
            simp [partialValueOwningLocations, valueOwningLocations,
              valueOwnedLocation?])
      | @boxInner _ slot' _ _ hslot' hinnerReach =>
          have hslotEq : slot' = slot := by
            rw [hslot] at hslot'
            injection hslot' with hslotEq
            exact hslotEq.symm
          subst hslotEq
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.box hcontains)
          rcases ih hinnerBorrows hinnerReach with howned | howns
          · exact Or.inr ⟨ownerLocation, slot'.lifetime, by
              have hslotValue : slot'.value = .value (owningRef location) :=
                eq_owningRef_of_mem_partialValueOwningLocations howned
              cases slot' with
              | mk slotValue slotLifetime =>
                  cases hslotValue
                  simpa using hslot⟩
          · exact Or.inr howns
  | @boxFull ownerLocation slot innerTy hslot _hinner ih =>
      intro hreach
      cases hreach with
      | boxFullHere _hslot =>
          exact Or.inl (by
            simp [partialValueOwningLocations, valueOwningLocations,
              valueOwnedLocation?])
      | @boxFullInner _ slot' _ _ hslot' hinnerReach =>
          have hslotEq : slot' = slot := by
            rw [hslot] at hslot'
            injection hslot' with hslotEq
            exact hslotEq.symm
          subst hslotEq
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty innerTy) := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.tyBox hcontains)
          rcases ih hinnerBorrows hinnerReach with howned | howns
          · exact Or.inr ⟨ownerLocation, slot'.lifetime, by
              have hslotValue : slot'.value = .value (owningRef location) :=
                eq_owningRef_of_mem_partialValueOwningLocations howned
              cases slot' with
              | mk slotValue slotLifetime =>
                  cases hslotValue
                  simpa using hslot⟩
          · exact Or.inr howns

/--
Stronger source form of `reaches_owning_or_store_owns_of_validPartialValue`.
When a reached location is not the direct owner carried by the value itself, it
is owned by a storage location that is also reached by the same validity
derivation.
-/
theorem reaches_owner_source_of_validPartialValue {env : Env}
    {store : ProgramStore} {slotLifetime : Lifetime}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    PartialTyBorrowsWellFormedInSlot env slotLifetime ty →
    ValidPartialValue store value ty →
    Reaches store value ty location →
    location ∈ partialValueOwningLocations value ∨
      ∃ storage,
        Reaches store value ty storage ∧
          ProgramStore.OwnsAt store location storage := by
  intro hborrows hvalid
  induction hvalid generalizing env slotLifetime location with
  | unit =>
      intro hreach
      cases hreach
  | int =>
      intro hreach
      cases hreach
  | undef =>
      intro hreach
      cases hreach
  | borrow _hmem _hloc =>
      intro hreach
      cases hreach with
      | @borrow _location _readLocation _mutable _targets target htargetMem _hloc hreads =>
          rcases hborrows PartialTyContains.here target htargetMem with
            ⟨_targetTy, _targetLifetime, _htargetTyping, _hlifetime,
              _hbaseOutlives, hvar⟩
          exact False.elim (LocReads.false_of_lvalIsVar hvar hreads)
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
          · exact Or.inr ⟨ownerLocation, Reaches.boxHere hslot,
              slot.lifetime, by
                have hslotValue : slot.value = .value (owningRef location) :=
                  eq_owningRef_of_mem_partialValueOwningLocations howned
                cases slot with
                | mk slotValue slotLifetime =>
                    cases hslotValue
                    simpa using hslot⟩
          · rcases hsource with ⟨storage, hstorageReach, howns⟩
            exact Or.inr ⟨storage, Reaches.boxInner hslot hstorageReach, howns⟩
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
          · exact Or.inr ⟨ownerLocation, Reaches.boxFullHere hslot,
              slot.lifetime, by
                have hslotValue : slot.value = .value (owningRef location) :=
                  eq_owningRef_of_mem_partialValueOwningLocations howned
                cases slot with
                | mk slotValue slotLifetime =>
                    cases hslotValue
                    simpa using hslot⟩
          · rcases hsource with ⟨storage, hstorageReach, howns⟩
            exact Or.inr ⟨storage, Reaches.boxFullInner hslot hstorageReach, howns⟩

/-- Every location reached from a stored valid value is owned by the store. -/
theorem store_owns_of_reaches_stored_validPartialValue {env : Env}
    {store : ProgramStore} {slotLifetime storageLifetime : Lifetime}
    {storage : Location} {storedValue : PartialValue} {partialTy : PartialTy}
    {location : Location} :
    store.slotAt storage =
      some { value := storedValue, lifetime := storageLifetime } →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    ValidPartialValue store storedValue partialTy →
    Reaches store storedValue partialTy location →
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

/--
If a valid partial value is stored in a slot whose location is protected from a
drop, then every location inspected by that value's validity derivation is also
protected from the same drop, provided the explicit drop-list roots are disjoint
from those inspected locations.

For owner roots this follows from `dropsAvoids_of_protected_owner`.  For inner
owner graphs the owner storage is reached first, so the induction hypothesis
protects that storage before descending.
-/
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
        Reaches store storedValue partialTy reached →
        ∀ dropValue, dropValue ∈ values →
          reached ∉ partialValueOwningLocations dropValue) →
      Reaches store storedValue partialTy location →
      DropsAvoids store values location := by
  intro hdrops hvalidStore env slotLifetime storageLifetime storage storedValue
    partialTy location hstored hborrows hvalid havoidStorage hdisjoint hreach
  induction hvalid generalizing env slotLifetime storageLifetime storage location with
  | unit =>
      cases hreach
  | int =>
      cases hreach
  | undef =>
      cases hreach
  | @borrow borrowedLocation mutable targets target hmem hloc =>
      cases hreach with
      | @borrow _borrowedLocation readLocation _mutable _targets target' hmem' _hloc' hreads =>
          rcases hborrows PartialTyContains.here target' hmem' with
            ⟨_targetTy, _targetLifetime, _htyping, _houtlives, _hbase, hvar⟩
          exact False.elim (LocReads.false_of_lvalIsVar hvar hreads)
  | @box ownerLocation slot inner hslot _hinnerValid ih =>
      cases hreach with
      | boxHere hreachSlot =>
          have howns : ProgramStore.OwnsAt store ownerLocation storage :=
            ⟨storageLifetime, hstored⟩
          exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
            havoidStorage (by
              intro dropValue hmem howned
              exact hdisjoint ownerLocation (Reaches.boxHere hreachSlot)
                dropValue hmem howned)
      | @boxInner _ reachSlot _ _ hreachSlot hinnerReach =>
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
              havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (Reaches.boxHere hreachSlot)
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
                (Reaches.boxInner hslot hinnerReached) dropValue hmem howned)
            hinnerReach
  | @boxFull ownerLocation slot innerTy hslot _hinnerValid ih =>
      cases hreach with
      | boxFullHere hreachSlot =>
          have howns : ProgramStore.OwnsAt store ownerLocation storage :=
            ⟨storageLifetime, hstored⟩
          exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
            havoidStorage (by
              intro dropValue hmem howned
              exact hdisjoint ownerLocation (Reaches.boxFullHere hreachSlot)
                dropValue hmem howned)
      | @boxFullInner _ reachSlot _ _ hreachSlot hinnerReach =>
          have hrootAvoid : DropsAvoids store values ownerLocation := by
            have howns : ProgramStore.OwnsAt store ownerLocation storage :=
              ⟨storageLifetime, hstored⟩
            exact LwRust.Paper.dropsAvoids_of_protected_owner hdrops hvalidStore howns
              havoidStorage (by
                intro dropValue hmem howned
                exact hdisjoint ownerLocation (Reaches.boxFullHere hreachSlot)
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
                (Reaches.boxFullInner hslot hinnerReached) dropValue hmem howned)
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
      Reaches store value partialTy reached →
        ∀ dropValue, dropValue ∈ values →
          reached ∉ partialValueOwningLocations dropValue) →
    Reaches store value partialTy location →
    DropsAvoids store values location := by
  intro hdrops hvalidStore hborrows hvalid hnotStoreOwned hdisjoint hreach
  induction hvalid generalizing env slotLifetime location with
  | unit =>
      cases hreach
  | int =>
      cases hreach
  | undef =>
      cases hreach
  | @borrow borrowedLocation mutable targets target hmem hloc =>
      cases hreach with
      | @borrow _borrowedLocation readLocation _mutable _targets target' hmem' _hloc' hreads =>
          rcases hborrows PartialTyContains.here target' hmem' with
            ⟨_targetTy, _targetLifetime, _htyping, _houtlives, _hbase, hvar⟩
          exact False.elim (LocReads.false_of_lvalIsVar hvar hreads)
  | @box ownerLocation slot inner hslot hinnerValid _ih =>
      cases hreach with
      | boxHere hreachSlot =>
          exact dropsAvoids_of_not_owns_and_not_mem hdrops
            (by
              intro dropValue hmem
              exact hdisjoint ownerLocation (Reaches.boxHere hreachSlot)
                dropValue hmem)
            (hnotStoreOwned ownerLocation (by
              simp [partialValueOwningLocations, valueOwningLocations,
                valueOwnedLocation?]))
      | @boxInner _ reachSlot _ _ hreachSlot hinnerReach =>
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (Reaches.boxHere hreachSlot)
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
                (Reaches.boxInner hslot hinnerReached) dropValue hmem howned)
            hinnerReach
  | @boxFull ownerLocation slot innerTy hslot hinnerValid _ih =>
      cases hreach with
      | boxFullHere hreachSlot =>
          exact dropsAvoids_of_not_owns_and_not_mem hdrops
            (by
              intro dropValue hmem
              exact hdisjoint ownerLocation (Reaches.boxFullHere hreachSlot)
                dropValue hmem)
            (hnotStoreOwned ownerLocation (by
              simp [partialValueOwningLocations, valueOwningLocations,
                valueOwnedLocation?]))
      | @boxFullInner _ reachSlot _ _ hreachSlot hinnerReach =>
          have hrootAvoid : DropsAvoids store values ownerLocation :=
            dropsAvoids_of_not_owns_and_not_mem hdrops
              (by
                intro dropValue hmem
                exact hdisjoint ownerLocation (Reaches.boxFullHere hreachSlot)
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
                (Reaches.boxFullInner hslot hinnerReached) dropValue hmem howned)
            hinnerReach

end RuntimeFrame

end Paper
end LwRust
