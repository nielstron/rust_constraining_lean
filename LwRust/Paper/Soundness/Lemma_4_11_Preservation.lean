import LwRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Lemma 4.11 (Preservation)

Paper statement (Section 4.4):

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; let `σ` be a
> store typing where `S₁ ▷ t ⊢ σ`; let `Γ₁` be a well-formed typing environment
> with respect to a lifetime `l` where `S₁ ∼ Γ₁`; let `Γ₂` be a typing
> environment; and let `T` be a type.  If `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂` and
> `⟨S₁ ▷ t ⟶* S₂ ▷ v⟩^l`, then `S₂ ▷ v` remains valid where `S₂ ∼ Γ₂` and
> `S₂ ▷ v ∼ T`.

Status: proved for the strengthened rule-carried formulation over source
continuations.  This excludes arbitrary pre-existing runtime references in
unevaluated continuation terms, which are not produced by source-initial runs.
The block case handles general term lists, recursive sequence drops, and
recursive block-lifetime drops.
-/

namespace LwRust
namespace Paper

open Core

/-! ### Store-update frame primitives (Appendix 9.10 support)

A move/assign updates exactly one store location.  These lemmas isolate when
such an update leaves an unrelated slot lookup and `loc` resolution unchanged.
-/

/-- Updating a location leaves the lookup at any *other* location unchanged. -/
theorem ProgramStore.slotAt_update_ne {store : ProgramStore}
    {updated location : Location} {slot : StoreSlot} :
    location ≠ updated →
    (store.update updated slot).slotAt location = store.slotAt location := by
  intro hne
  simp [ProgramStore.update, hne]

/-- `loc` for a variable lval reads no slot, so it is store-independent. -/
@[simp] theorem ProgramStore.loc_var (store : ProgramStore) (x : Name) :
    store.loc (.var x) = some (.var x) := by
  simp [ProgramStore.loc]

/--
The locations whose slots are inspected while resolving `loc store lv`.  A
variable reads nothing; a deref reads the slot at the location its source
resolves to, plus whatever the source reads.
-/
inductive LocReads (store : ProgramStore) : LVal → Location → Prop where
  | here {lv : LVal} {location : Location} :
      store.loc lv = some location →
      LocReads store (.deref lv) location
  | there {lv : LVal} {location : Location} :
      LocReads store lv location →
      LocReads store (.deref lv) location

/-- If an update misses every location `loc` reads while resolving `lv`, the
resolution is unchanged. -/
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
      -- resolve the source location
      cases hsource : store.loc lv with
      | none => simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          have hsourceNe : source ≠ updated :=
            hreads source (LocReads.here hsource)
          have hsource' : (store.update updated slot).loc lv = some source := by
            refine ih hsource ?_
            intro mid hmid
            exact hreads mid (LocReads.there hmid)
          -- the deref reads the slot at `source`; it is unchanged since source ≠ updated
          have hslotEq :
              (store.update updated slot).slotAt source = store.slotAt source :=
            ProgramStore.slotAt_update_ne hsourceNe
          have hlocEq :
              (store.update updated slot).loc (.deref lv) = store.loc (.deref lv) := by
            simp [ProgramStore.loc, hsource, hsource', hslotEq]
          rw [hlocEq]; exact hloc

/-- If an erase misses every location `loc` reads while resolving `lv`, the
resolution is unchanged. -/
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
          rw [hlocEq]; exact hloc

/-- A successful lookup after erasing a location also succeeds in the original
store. -/
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
`ValidPartialValue store v ty`.  Owned (box) references read their pointee slot
and recurse; a borrow reads the slots `loc` traverses to resolve its target.
Ground values read nothing.
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

/-- Frame lemma for `ValidPartialValue`: updating a location the value's
validity derivation never inspects preserves the abstraction. -/
theorem validPartialValue_update_of_not_reaches {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValue store v ty →
      (∀ ℓ, Reaches store v ty ℓ → ℓ ≠ updated) →
      ValidPartialValue (store.update updated newSlot) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit | int | bool | undef => intro _; constructor
  | borrow hmem hloc =>
      intro hreach
      refine ValidPartialValue.borrow hmem ?_
      refine loc_update_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hmem hloc hmidReads)
  | @box location slot inner hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated := hreach location (Reaches.boxHere hslot)
      refine ValidPartialValue.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]; exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated := hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]; exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxFullInner hslot hℓ))

/-- Frame lemma for `ValidPartialValue`: erasing a location the validity
derivation never inspects preserves the abstraction. -/
theorem validPartialValue_erase_of_not_reaches {store : ProgramStore}
    {erased : Location} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValue store v ty →
      (∀ ℓ, Reaches store v ty ℓ → ℓ ≠ erased) →
      ValidPartialValue (store.erase erased) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit | int | bool | undef => intro _; constructor
  | borrow hmem hloc =>
      intro hreach
      refine ValidPartialValue.borrow hmem ?_
      refine loc_erase_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hmem hloc hmidReads)
  | @box location slot inner hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ erased := hreach location (Reaches.boxHere hslot)
      refine ValidPartialValue.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]; exact hslot; exact hlocNe
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ erased := hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]; exact hslot; exact hlocNe
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxFullInner hslot hℓ))

/-- Value reachability observed after an erase was already present in the
original store. -/
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

/-- Frame lemma for recursive drops: if the drop derivation avoids every
location inspected by a value-validity derivation, the value remains valid. -/
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

theorem validRuntimeState_of_sourceTerm {store : ProgramStore} {context term : Term} :
    SourceTerm term →
    ValidRuntimeState store context →
    ValidRuntimeState store term := by
  intro hsource hvalid
  exact ⟨⟨hvalid.1.1, sourceTerm_validTerm hsource, by
      intro owned hmem
      have hnone := sourceTerm_no_owningLocations hsource
      rw [hnone] at hmem
      cases hmem⟩,
    hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1,
    sourceTerm_ownerTargetsHeap hsource⟩

theorem sourceTerm_bool_value (value : Bool) :
    SourceTerm (.val (.bool value)) := by
  intro candidate hmem
  simp [termValues] at hmem
  subst hmem
  trivial

/--
Direct variable writes transport from the environment where the variable has
already been assigned the RHS type to the actual Definition 3.23 result.

At rank zero this is just `W-Strong`; at positive rank it is the weak join case.
The statement is intentionally rank-polymorphic so recursive borrowed-target
writes do not need separate base cases for `write₀` and `writeₖ₊₁`.
-/
theorem EnvWrite.var_rhs_to_result_map
    {rank : Nat} {env result : Env} {x : Name}
    {slot : EnvSlot} {oldTy rhsTy : Ty} :
    env.slotAt x = some slot →
    slot.ty = .ty oldTy →
    EnvWrite rank env (.var x) rhsTy result →
    EnvSameShapeStrengthening
      (env.update x { slot with ty := .ty rhsTy }) result := by
  intro hslot hslotTy hwrite
  cases hwrite with
  | @intro _rank _env₁ env₂ lv writeSlot _ty updatedTy hwriteSlot hupdate =>
      simp [LVal.base] at hwriteSlot
      have hslotEq : writeSlot = slot := by
        have hsome : some writeSlot = some slot := by
          rw [← hwriteSlot, hslot]
        exact Option.some.inj hsome
      subst writeSlot
      simp [LVal.path] at hupdate
      rw [hslotTy] at hupdate
      cases hupdate with
      | strong =>
          exact EnvSameShapeStrengthening.refl
            (env.update x { slot with ty := .ty rhsTy })
      | weak hshape hjoin =>
          constructor
          · intro y resultSlot hresultSlot
            by_cases hy : y = x
            · subst hy
              have hresultSlotEq :
                  resultSlot = { slot with ty := updatedTy } := by
                simpa [Env.update, LVal.base] using hresultSlot.symm
              subst hresultSlotEq
              refine ⟨{ slot with ty := .ty rhsTy }, ?_, ?_, ?_, ?_⟩
              · simp [Env.update]
              · rfl
              · exact PartialTyUnion.right_strengthens hjoin
              · exact partialTyJoin_ty_left_sameShape
                  (PartialTyUnion.symm hjoin)
            · have hresultOld :
                  env.slotAt y = some resultSlot := by
                simpa [Env.update, LVal.base, hy] using hresultSlot
              refine ⟨resultSlot, ?_, rfl, PartialTyStrengthens.reflex,
                PartialTy.sameShape_refl _⟩
              simpa [Env.update, hy] using hresultOld
          · intro y sourceSlot hsourceSlot
            by_cases hy : y = x
            · subst hy
              have hsourceSlotEq :
                  sourceSlot = { slot with ty := .ty rhsTy } := by
                simpa [Env.update, LVal.base] using hsourceSlot.symm
              subst hsourceSlotEq
              refine ⟨{ slot with ty := updatedTy }, ?_, rfl⟩
              simp [Env.update, LVal.base]
            · have hsourceOld :
                  env.slotAt y = some sourceSlot := by
                simpa [Env.update, hy] using hsourceSlot
              refine ⟨sourceSlot, ?_, rfl⟩
              simpa [Env.update, LVal.base, hy] using hsourceOld


theorem lval_loc_var_rank_le_base_of_safe {store : ProgramStore} {env : Env}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
    {x : Name} {φ : Name → Nat} :
    LinearizedBy φ env →
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    store.loc lv = some (VariableProjection x) →
    φ x ≤ φ (LVal.base lv) := by
  intro hφ hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      store.loc lv = some (VariableProjection x) →
      φ x ≤ φ (LVal.base lv))
    (motive_2 := fun targets partialTy lifetime _ =>
      (∀ target, target ∈ targets →
        store.loc target = some (VariableProjection x) →
        φ x ≤ φ (LVal.base target)))
    ?var ?box ?borrow ?empty ?singleton ?cons htyping
  · intro y slot _hslot hloc
    simp [ProgramStore.loc, VariableProjection] at hloc
    cases hloc
    exact Nat.le_refl _
  · intro source inner sourceLifetime hsource _ih hloc
    have hsourceAbs : LValLocationAbstraction store source (.box inner) :=
      lvalTyping_defined_location_of_safe hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @box ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          exact ⟨sourceLocation, sourceSlotLifetime, by
            simpa [owningRef] using hsourceSlot⟩
        exact False.elim ((not_owns_var_of_storeOwnerTargetsHeap hheap) howns)
  · intro source mutable targets pointee borrowLifetime targetLifetime
      hsource htargets _ihSource ihTargets hloc
    have hsourceAbs :
        LValLocationAbstraction store source (.ty (.borrow mutable targets pointee)) :=
      lvalTyping_defined_location_of_safe hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrow selectedLocation _mutable _targets _pointee selected hmem hselectedLoc =>
        have hderefLoc : store.loc source.deref = some selectedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hselectedLocationEq : selectedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        subst hselectedLocationEq
        have hxLeSelected : φ x ≤ φ (LVal.base selected) :=
          ihTargets selected hmem hselectedLoc
        have hselectedMemVars :
            LVal.base selected ∈ PartialTy.vars
              (.ty (.borrow mutable targets pointee)) := by
          exact mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, pointee, selected, PartialTyContains.here, hmem, rfl⟩
        have hselectedLtSource :
            φ (LVal.base selected) < φ (LVal.base source) :=
          (lvalTyping_vars_rank_lt hφ).1 hsource
            (LVal.base selected) hselectedMemVars
        exact le_trans hxLeSelected (Nat.le_of_lt hselectedLtSource)
  · intro ty _hvars target hmem _hloc
    cases hmem
  · intro target targetTy targetLifetime _htarget ihTarget selected hmem hloc
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ihTarget hloc
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest _hunion _hintersection ihHead ihRest selected hmem hloc
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst hhead
      exact ihHead hloc
    · exact ihRest selected htail hloc

theorem lval_loc_var_rank_le_base {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
    {x : Name} {φ : Name → Nat} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    store.loc lv = some (VariableProjection x) →
    φ x ≤ φ (LVal.base lv) := by
  intro hφ _hwellFormed hsafe hheap htyping hloc
  exact lval_loc_var_rank_le_base_of_safe hφ hsafe hheap htyping hloc

/--
If resolving a typed lvalue reads variable `x`, then `x` is no higher-ranked
than the lvalue's syntactic base.  This is the read-dependency analogue of
`lval_loc_var_rank_le_base`.
-/
theorem locReads_var_rank_le_base_of_safe {store : ProgramStore} {env : Env}
    {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {x : Name} {φ : Name → Nat} :
    LinearizedBy φ env →
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv pt lifetime →
    RuntimeFrame.LocReads store lv (VariableProjection x) →
    φ x ≤ φ (LVal.base lv) := by
  intro hφ hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _pt _lifetime _ =>
      RuntimeFrame.LocReads store lv (VariableProjection x) →
      φ x ≤ φ (LVal.base lv))
    (motive_2 := fun _targets _pt _lifetime _ => True)
    ?var ?box ?borrow ?empty ?singleton ?cons htyping
  · intro _y _slot _hslot hreads
    cases hreads
  · intro source inner sourceLifetime hsource ih hreads
    cases hreads with
    | here hsourceLoc =>
        simpa [LVal.base] using
          lval_loc_var_rank_le_base_of_safe hφ hsafe hheap
            hsource hsourceLoc
    | there hsourceReads =>
        simpa [LVal.base] using ih hsourceReads
  · intro source mutable targets pointee borrowLifetime targetLifetime
      hsource _htargets ihSource _ihTargets hreads
    cases hreads with
    | here hsourceLoc =>
        simpa [LVal.base] using
          lval_loc_var_rank_le_base_of_safe hφ hsafe hheap
            hsource hsourceLoc
    | there hsourceReads =>
        simpa [LVal.base] using ihSource hsourceReads
  · intros
    trivial
  · intros
    trivial
  · intros
    trivial

theorem locReads_var_rank_le_base {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {x : Name} {φ : Name → Nat} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv pt lifetime →
    RuntimeFrame.LocReads store lv (VariableProjection x) →
    φ x ≤ φ (LVal.base lv) := by
  intro hφ _hwellFormed hsafe hheap htyping hreads
  exact locReads_var_rank_le_base_of_safe hφ hsafe hheap htyping hreads

/--
Any borrow-resolution dependency on variable `x` is witnessed by some borrow
target base occurring in the dependency's static partial type whose rank is at
least `x`'s rank.
-/
theorem RuntimeFrame.borrowDependency_var_rank_le_var_of_safe
    {store : ProgramStore} {env : Env} {slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {x : Name}
    {φ : Name → Nat} :
    LinearizedBy φ env →
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    dependency = VariableProjection x →
    ∃ v, v ∈ PartialTy.vars partialTy ∧ φ x ≤ φ v := by
  intro hφ hsafe hheap hborrows hdependency hdependencyEq
  induction hdependency generalizing env slotLifetime with
  | @borrow location readLocation mutable targets pointee target hmem hloc hreads =>
      subst hdependencyEq
      have htargetWell := hborrows PartialTyContains.here target hmem
      rcases htargetWell with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      refine ⟨LVal.base target, ?_, ?_⟩
      · exact mem_partialTy_vars_iff.mpr
          ⟨mutable, targets, pointee, target, PartialTyContains.here, hmem, rfl⟩
      · exact locReads_var_rank_le_base_of_safe hφ hsafe hheap
          htargetTyping hreads
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets pointee hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hφ hsafe hinnerBorrows hdependencyEq with
        ⟨v, hv, hle⟩
      exact ⟨v, by simpa [PartialTy.vars] using hv, hle⟩
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets pointee hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hφ hsafe hinnerBorrows hdependencyEq with
        ⟨v, hv, hle⟩
      exact ⟨v, by simpa [PartialTy.vars, Ty.vars] using hv, hle⟩

theorem RuntimeFrame.borrowDependency_var_rank_le_var
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {x : Name}
    {φ : Name → Nat} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    dependency = VariableProjection x →
    ∃ v, v ∈ PartialTy.vars partialTy ∧ φ x ≤ φ v := by
  intro hφ _hwellFormed hsafe hheap hborrows hdependency hdependencyEq
  exact RuntimeFrame.borrowDependency_var_rank_le_var_of_safe
    hφ hsafe hheap hborrows hdependency hdependencyEq

/--
Safe-only root/rank abstraction for a resolved lvalue location.

This is the runtime slice of `RuntimeFrame.loc_intrinsicRootView` needed by the
heap-spine write map: following a typed lvalue either descends through owned
boxes inside the same root, or jumps through a borrow to a target whose base has
strictly lower rank.  No slot-level borrow well-formedness or coherence is used.
-/
theorem RuntimeFrame.loc_intrinsicRootRank_of_safe {store : ProgramStore}
    {env : Env} {φ : Name → Nat} {lv : LVal} {pt : PartialTy}
    {lifetime : Lifetime} {location : Location} :
    LinearizedBy φ env →
    store ∼ₛ env →
    LValTyping env lv pt lifetime →
    store.loc lv = some location →
    ∃ root,
      ProtectedByBase store root location ∧
      φ root ≤ φ (LVal.base lv) := by
  intro hφ hsafe htyping hloc
  exact go hφ hsafe htyping hloc
where
  go {store : ProgramStore} {env : Env} {φ : Name → Nat}
      {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
      {location : Location}
      (hφ : LinearizedBy φ env) (hsafe : store ∼ₛ env)
      (htyping : LValTyping env lv pt lifetime)
      (hloc : store.loc lv = some location) :
      ∃ root,
        ProtectedByBase store root location ∧
        φ root ≤ φ (LVal.base lv) := by
    cases lv with
    | var x =>
        have hlocEq : location = VariableProjection x := by
          simp [ProgramStore.loc] at hloc
          exact hloc.symm
        subst hlocEq
        exact ⟨x, Or.inl rfl, le_refl _⟩
    | deref source =>
        cases htyping with
        | box hsource =>
            have hsourceAbs : LValLocationAbstraction store source (.box _) :=
              lvalTyping_defined_location_of_safe hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases go hφ hsafe hsource hmiddleLoc with
              ⟨root, hprotMiddle, hrank⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            cases hmiddleValid with
            | @box ownedLocation ownedSlot _ hownedSlot _hinnerValid =>
                have hderefLoc : store.loc (.deref source) = some ownedLocation := by
                  simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot]
                have hlocEq : location = ownedLocation := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                have howns : ProgramStore.OwnsAt store ownedLocation middle := by
                  exact ⟨middleLifetime, by simpa [owningRef] using hmiddleSlot⟩
                refine ⟨root, ?_, by simpa [LVal.base] using hrank⟩
                rw [hlocEq]
                exact ProtectedByBase.trans_owned hprotMiddle howns
        | @borrow _ mutable targets pointee borrowLifetime targetLifetime
            hsource htargets =>
            have hsourceAbs :
                LValLocationAbstraction store source
                  (.ty (.borrow mutable targets pointee)) :=
              lvalTyping_defined_location_of_safe hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            cases hmiddleValid with
            | @borrow selectedLocation _mutable _targets _pointee selected
                hselectedMem hselectedLoc =>
                have hderefLoc : store.loc (.deref source) = some selectedLocation := by
                  simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot]
                have hlocEq : location = selectedLocation := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                rcases lvalTargetsTyping_member_strengthens htargets selected
                    hselectedMem with
                  ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrengthens⟩
                have hselectedMemVars :
                    LVal.base selected ∈ PartialTy.vars
                      (.ty (.borrow mutable targets pointee)) :=
                  mem_partialTy_vars_iff.mpr
                    ⟨mutable, targets, pointee, selected,
                      PartialTyContains.here, hselectedMem, rfl⟩
                have hselectedLtSource :
                    φ (LVal.base selected) < φ (LVal.base source) :=
                  (lvalTyping_vars_rank_lt hφ).1 hsource
                    (LVal.base selected) hselectedMemVars
                rcases go hφ hsafe hselectedTyping hselectedLoc with
                  ⟨root, hprotSelected, hrootLeSelected⟩
                exact ⟨root, hprotSelected,
                  by
                    simpa [LVal.base] using
                      le_of_lt (lt_of_le_of_lt hrootLeSelected
                        hselectedLtSource)⟩
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)

/--
Frame an update through the exact borrow-resolution dependencies used by a
`ValidPartialValue` derivation.

`RuntimeFrame.validPartialValue_update_of_not_reaches` is deliberately stronger:
it ranges over every static borrow target in the type.  Assignment through a
borrowed target only needs the selected target recorded in the validity proof, so
this lemma separates owner reachability from selected borrow dependencies.
-/
theorem RuntimeFrame.validPartialValue_update_of_owner_and_selected_dependency_frame
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot} :
    ∀ {value : PartialValue} {ty : PartialTy}
      (hvalid : ValidPartialValue store value ty),
      (∀ location,
        RuntimeFrame.OwnerReaches store value ty location →
        location ≠ updated) →
      (∀ location,
        RuntimeFrame.SelectedBorrowDependency store hvalid location →
        location ≠ updated) →
      ValidPartialValue (store.update updated newSlot) value ty := by
  intro value ty hvalid
  induction hvalid with
  | unit | int | bool | undef =>
      intro _howners _hdeps
      constructor
  | @borrow location mutable targets pointee target hmem hloc =>
      intro _howners hdeps
      refine ValidPartialValue.borrow hmem ?_
      exact RuntimeFrame.loc_update_of_not_locReads hloc (by
        intro mid hreads
        exact hdeps mid
          (RuntimeFrame.SelectedBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (pointee := pointee) (target := target) (hmem := hmem)
            (hloc := hloc) hreads))
  | @box location slot inner hslot _hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (RuntimeFrame.OwnerReaches.boxHere hslot)
      refine ValidPartialValue.box (location := location) (slot := slot) ?_ ?_
      · rw [RuntimeFrame.ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached
              (RuntimeFrame.OwnerReaches.boxInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (RuntimeFrame.SelectedBorrowDependency.boxInner
                (store := store) (location := location) (slot := slot)
                (inner := inner) (hslot := hslot) (hinner := _hinner)
                hdependency))
  | @boxFull location slot innerTy hslot _hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (RuntimeFrame.OwnerReaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [RuntimeFrame.ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached
              (RuntimeFrame.OwnerReaches.boxFullInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (RuntimeFrame.SelectedBorrowDependency.boxFullInner
                (store := store) (location := location) (slot := slot)
                (ty := innerTy) (hslot := hslot) (hinner := _hinner)
                hdependency))

mutual
  /--
  A path through a partial type whose runtime-selected borrow branch eventually
  resolves to variable `selectedName`.

  Unlike `PathSelected`, the borrow-head case carries an arbitrary selected target
  lvalue.  This is the induction principle needed for assignments through nested
  references such as `**p := v`.
  -/
  inductive RuntimePathSelected (store : ProgramStore) (env : Env) :
      PartialTy → List Unit → Name → EnvSlot → Ty → Prop where
    | borrowHere {mutable : Bool} {targets : List LVal} {pointee : Ty}
        {selectedTarget : LVal} {selectedTargetTy : Ty}
        {selectedTargetLifetime : Lifetime} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedSlotTy : Ty} :
        selectedTarget ∈ targets →
        LValTyping env selectedTarget (.ty selectedTargetTy)
          selectedTargetLifetime →
        store.loc selectedTarget = some (VariableProjection selectedName) →
        env.slotAt selectedName = some selectedSlot →
        selectedSlot.ty = .ty selectedSlotTy →
        RuntimePathSelected store env (.ty (.borrow mutable targets pointee)) [()]
          selectedName selectedSlot selectedSlotTy
    | box {inner : PartialTy} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedSlotTy : Ty} :
        RuntimePathSelected store env inner path selectedName selectedSlot
          selectedSlotTy →
        RuntimePathSelected store env (.box inner) (() :: path) selectedName
          selectedSlot selectedSlotTy
    | borrowStep {mutable : Bool} {targets : List LVal} {pointee : Ty}
        {path : List Unit} {selectedName : Name} {selectedSlot : EnvSlot}
        {selectedSlotTy : Ty} :
        RuntimeTargetsPathSelected store env targets path selectedName
          selectedSlot selectedSlotTy →
        RuntimePathSelected store env (.ty (.borrow mutable targets pointee))
          (() :: path) selectedName selectedSlot selectedSlotTy

  inductive RuntimeTargetsPathSelected (store : ProgramStore) (env : Env) :
      List LVal → List Unit → Name → EnvSlot → Ty → Prop where
    | target {targets : List LVal} {target : LVal} {pt : PartialTy}
        {lifetime : Lifetime} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedSlotTy : Ty} :
        target ∈ targets →
        LValTyping env target pt lifetime →
        RuntimePathSelected store env pt path selectedName selectedSlot
          selectedSlotTy →
        RuntimeTargetsPathSelected store env targets path selectedName
          selectedSlot selectedSlotTy
end

mutual
  theorem RuntimePathSelected.rank_lt_of_lvalTyping {store : ProgramStore}
      {env : Env} {φ : Name → Nat}
      (hφ : LinearizedBy φ env) (hsafe : store ∼ₛ env)
      (hheap : StoreOwnerTargetsHeap store) :
      ∀ {pt : PartialTy} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedSlotTy : Ty},
        RuntimePathSelected store env pt path selectedName selectedSlot
          selectedSlotTy →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv pt lifetime →
          φ selectedName < φ (LVal.base lv)
    | .ty (.borrow mutable targets pointee), [()], selectedName, selectedSlot,
      selectedSlotTy,
      RuntimePathSelected.borrowHere hmem htargetTyping htargetLoc _hslot _hty,
      lv, lifetime, htyping => by
        have hselectedLeTarget :
            φ selectedName ≤ φ (LVal.base _) :=
          lval_loc_var_rank_le_base_of_safe hφ hsafe hheap
            htargetTyping htargetLoc
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars
              (.ty (.borrow mutable targets pointee)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, pointee, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_of_le_of_lt hselectedLeTarget htargetLtLv
    | .box inner, () :: path, selectedName, selectedSlot, selectedSlotTy,
      RuntimePathSelected.box hinner, lv, lifetime, htyping => by
        have hderef : LValTyping env (.deref lv) inner lifetime :=
          LValTyping.box htyping
        simpa [LVal.base] using
          RuntimePathSelected.rank_lt_of_lvalTyping hφ hsafe
            hheap hinner hderef
    | .ty (.borrow mutable targets pointee), () :: path, selectedName, selectedSlot,
      selectedSlotTy, RuntimePathSelected.borrowStep htargets, lv, lifetime,
      htyping => by
        exact RuntimeTargetsPathSelected.rank_lt_of_lvalTyping hφ hsafe hheap
          htargets htyping

  theorem RuntimeTargetsPathSelected.rank_lt_of_lvalTyping
      {store : ProgramStore} {env : Env} {φ : Name → Nat}
      (hφ : LinearizedBy φ env) (hsafe : store ∼ₛ env)
      (hheap : StoreOwnerTargetsHeap store) :
      ∀ {mutable : Bool} {targets : List LVal} {pointee : Ty}
        {path : List Unit}
        {selectedName : Name} {selectedSlot : EnvSlot} {selectedSlotTy : Ty},
        RuntimeTargetsPathSelected store env targets path selectedName
          selectedSlot selectedSlotTy →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv (.ty (.borrow mutable targets pointee)) lifetime →
          φ selectedName < φ (LVal.base lv)
    | mutable, targets, pointee, path, selectedName, selectedSlot, selectedSlotTy,
      RuntimeTargetsPathSelected.target hmem htargetTyping hpath, lv, lifetime,
      htyping => by
        have hselectedLtTarget :
            φ selectedName < φ (LVal.base _) :=
          RuntimePathSelected.rank_lt_of_lvalTyping hφ hsafe
            hheap hpath htargetTyping
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars
              (.ty (.borrow mutable targets pointee)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, pointee, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_trans hselectedLtTarget htargetLtLv
end

theorem RuntimePathSelected.of_partialTyUnion {store : ProgramStore} {env : Env}
    {left right union : PartialTy} {path : List Unit} {selectedName : Name}
    {selectedSlot : EnvSlot} {selectedSlotTy : Ty} :
    PartialTyUnion left right union →
    RuntimePathSelected store env union path selectedName selectedSlot
      selectedSlotTy →
    RuntimePathSelected store env left path selectedName selectedSlot
        selectedSlotTy ∨
      RuntimePathSelected store env right path selectedName selectedSlot
        selectedSlotTy := by
  intro hunion hselected
  refine RuntimePathSelected.rec
    (motive_1 := fun union path selectedName selectedSlot selectedSlotTy _ =>
      ∀ left right,
        PartialTyUnion left right union →
        RuntimePathSelected store env left path selectedName selectedSlot
            selectedSlotTy ∨
          RuntimePathSelected store env right path selectedName selectedSlot
            selectedSlotTy)
    (motive_2 := fun _targets _path _selectedName _selectedSlot
      _selectedSlotTy _ => True)
    ?borrowHere ?box ?borrowStep ?target hselected left right hunion
  case borrowHere =>
    intro mutable targets pointee selectedTarget selectedTargetTy selectedTargetLifetime
      selectedName selectedSlot selectedSlotTy hmem htyping hloc hslot hty
      left right hunion
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.left_strengthens hunion) with
      ⟨leftTargets, _leftPointee, hleftEq, _hleftSubset, _hleftPointee⟩
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.right_strengthens hunion) with
      ⟨rightTargets, _rightPointee, hrightEq, _hrightSubset, _hrightPointee⟩
    cases hleftEq
    cases hrightEq
    rcases PartialTyUnion.borrow_member hunion hmem with hleft | hright
    · exact Or.inl (RuntimePathSelected.borrowHere hleft htyping hloc hslot hty)
    · exact Or.inr (RuntimePathSelected.borrowHere hright htyping hloc hslot hty)
  case box =>
    intro inner path selectedName selectedSlot selectedSlotTy hinner ih
      left right hunion
    have hleftStrength := PartialTyUnion.left_strengthens hunion
    cases hleftStrength with
    | reflex =>
        exact Or.inl (RuntimePathSelected.box hinner)
    | box hleftInner =>
        have hrightStrength := PartialTyUnion.right_strengthens hunion
        cases hrightStrength with
        | reflex =>
            exact Or.inr (RuntimePathSelected.box hinner)
        | box hrightInner =>
            rcases ih _ _ (PartialTyUnion.box_inv hunion) with hleft | hright
            · exact Or.inl (RuntimePathSelected.box hleft)
            · exact Or.inr (RuntimePathSelected.box hright)
  case borrowStep =>
    intro mutable targets pointee path selectedName selectedSlot selectedSlotTy
      htargets _ih left right hunion
    cases htargets with
    | target hmem htargetTyping hpath =>
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.left_strengthens hunion) with
          ⟨leftTargets, _leftPointee, hleftEq, _hleftSubset, _hleftPointee⟩
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.right_strengthens hunion) with
          ⟨rightTargets, _rightPointee, hrightEq, _hrightSubset, _hrightPointee⟩
        cases hleftEq
        cases hrightEq
        rcases PartialTyUnion.borrow_member hunion hmem with hleft | hright
        · exact Or.inl (RuntimePathSelected.borrowStep
            (RuntimeTargetsPathSelected.target hleft htargetTyping hpath))
        · exact Or.inr (RuntimePathSelected.borrowStep
            (RuntimeTargetsPathSelected.target hright htargetTyping hpath))
  case target =>
    intros
    trivial

theorem RuntimeTargetsPathSelected.of_lvalTargetsTyping {store : ProgramStore}
    {env : Env} {targets : List LVal} {pt : PartialTy}
    {lifetime : Lifetime} {path : List Unit} {selectedName : Name}
    {selectedSlot : EnvSlot} {selectedSlotTy : Ty} :
    LValTargetsTyping env targets pt lifetime →
    RuntimePathSelected store env pt path selectedName selectedSlot
      selectedSlotTy →
    RuntimeTargetsPathSelected store env targets path selectedName selectedSlot
      selectedSlotTy := by
  intro htargets hselected
  refine LValTargetsTyping.rec
    (motive_1 := fun _target _ty _lifetime _htyping => True)
    (motive_2 := fun targets pt lifetime _htyping =>
      ∀ {path : List Unit} {selectedName : Name} {selectedSlot : EnvSlot}
        {selectedSlotTy : Ty},
        RuntimePathSelected store env pt path selectedName selectedSlot
          selectedSlotTy →
        RuntimeTargetsPathSelected store env targets path selectedName
          selectedSlot selectedSlotTy)
    ?var ?box ?borrow ?empty ?singleton ?cons htargets hselected
  case var | box | borrow => intros; trivial
  case empty =>
      intros
      rename_i hselected
      cases hselected <;> simp_all [PartialTy.allVars, Ty.allVars, List.mem_map]
      rename_i htargets
      cases htargets with
      | target hmem _ _ => cases hmem
  case singleton =>
      intro target ty lifetime htarget _ih path selectedName selectedSlot
        selectedSlotTy hselected
      exact RuntimeTargetsPathSelected.target (by simp) htarget hselected
  case cons =>
      intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
        hhead _hrest hunion _hintersection _ihHead ihRest
        path selectedName selectedSlot selectedSlotTy hselected
      rcases RuntimePathSelected.of_partialTyUnion hunion hselected with
        hheadSelected | hrestSelected
      · exact RuntimeTargetsPathSelected.target (by simp) hhead hheadSelected
      · cases ihRest hrestSelected with
        | target hmem htargetTyping hpath =>
            exact RuntimeTargetsPathSelected.target (List.mem_cons_of_mem _ hmem)
              htargetTyping hpath

theorem RuntimePathSelected.prepend_of_lvalTyping {store : ProgramStore}
    {env : Env} {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {selectedName : Name} {selectedSlot : EnvSlot} {selectedSlotTy : Ty}
    (htyping : LValTyping env lv pt lifetime) :
    ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
    ∀ (path : List Unit),
      RuntimePathSelected store env pt path selectedName selectedSlot
        selectedSlotTy →
      RuntimePathSelected store env slot.ty (LVal.path lv ++ path)
        selectedName selectedSlot selectedSlotTy := by
  refine LValTyping.rec
    (motive_1 := fun lv pt _lifetime _ =>
      ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
      ∀ (path : List Unit),
        RuntimePathSelected store env pt path selectedName selectedSlot
          selectedSlotTy →
        RuntimePathSelected store env slot.ty (LVal.path lv ++ path)
          selectedName selectedSlot selectedSlotTy)
    (motive_2 := fun _targets _pt _lifetime _ => True)
    ?var ?box ?borrow ?empty ?singleton ?cons htyping
  case var =>
    intro x slot hslot slot' hslot' path hselected
    simp only [LVal.base] at hslot'
    have hslotEq : slot = slot' := by
      rw [hslot] at hslot'
      exact Option.some.inj hslot'
    subst hslotEq
    simpa [LVal.path] using hselected
  case box =>
    intro source inner sourceLifetime _hsource ih slot hslot path hselected
    rw [LVal.path, List.append_assoc]
    exact ih hslot (() :: path) (RuntimePathSelected.box hselected)
  case borrow =>
    intro source mutable targets pointee borrowLifetime targetLifetime
      _hsource htargets ih _ihTargets slot hslot path hselected
    rw [LVal.path, List.append_assoc]
    exact ih hslot (() :: path)
      (RuntimePathSelected.borrowStep
        (RuntimeTargetsPathSelected.of_lvalTargetsTyping htargets hselected))
  case empty =>
    intros
    trivial
  case singleton | cons =>
    intros
    trivial

theorem RuntimePathSelected.updateAtPath_map {store : ProgramStore}
    {env selectedSource writeEnv : Env}
    {oldTy updatedTy : PartialTy} {path : List Unit} {rank : Nat}
    {rhsTy selectedSlotTy : Ty} {selectedName : Name}
    {selectedSlot : EnvSlot} {φ : Name → Nat} {rootRank : Nat} :
    (∀ v, v ∈ PartialTy.vars oldTy → φ v < rootRank) →
    RuntimePathSelected store env oldTy path selectedName selectedSlot
      selectedSlotTy →
    UpdateAtPath rank env path oldTy rhsTy writeEnv updatedTy →
    (∀ {branchRank : Nat} {target : LVal} {targetTy : Ty}
      {lifetime : Lifetime} {branchResult : Env},
      0 < branchRank →
      φ (LVal.base target) < rootRank →
      LValTyping env target (.ty targetTy) lifetime →
      store.loc target = some (VariableProjection selectedName) →
      EnvWrite branchRank env target rhsTy branchResult →
      EnvSameShapeStrengthening selectedSource branchResult) →
    (∀ {branchRank : Nat} {target : LVal} {pt : PartialTy}
      {lifetime : Lifetime} {branchPath : List Unit} {branchResult : Env},
      0 < branchRank →
      φ (LVal.base target) < rootRank →
      LValTyping env target pt lifetime →
      RuntimePathSelected store env pt branchPath selectedName selectedSlot
        selectedSlotTy →
      EnvWrite branchRank env (prependPath branchPath target) rhsTy branchResult →
      EnvSameShapeStrengthening selectedSource branchResult) →
    EnvSameShapeStrengthening selectedSource writeEnv ∧
      PartialTyStrengthens oldTy updatedTy ∧
      PartialTy.sameShape oldTy updatedTy := by
  intro hbelow hselected hupdate hbranchHere hbranchStep
  refine (RuntimePathSelected.rec
    (motive_1 := fun oldTy path selectedName selectedSlot selectedSlotTy
      _hselected =>
      ∀ {rank : Nat} {updatedTy : PartialTy} {writeEnv : Env},
        (∀ v, v ∈ PartialTy.vars oldTy → φ v < rootRank) →
        UpdateAtPath rank env path oldTy rhsTy writeEnv updatedTy →
        (∀ {branchRank : Nat} {target : LVal} {targetTy : Ty}
          {lifetime : Lifetime} {branchResult : Env},
          0 < branchRank →
          φ (LVal.base target) < rootRank →
          LValTyping env target (.ty targetTy) lifetime →
          store.loc target = some (VariableProjection selectedName) →
          EnvWrite branchRank env target rhsTy branchResult →
          EnvSameShapeStrengthening selectedSource branchResult) →
        (∀ {branchRank : Nat} {target : LVal} {pt : PartialTy}
          {lifetime : Lifetime} {branchPath : List Unit} {branchResult : Env},
          0 < branchRank →
          φ (LVal.base target) < rootRank →
          LValTyping env target pt lifetime →
          RuntimePathSelected store env pt branchPath selectedName selectedSlot
            selectedSlotTy →
          EnvWrite branchRank env (prependPath branchPath target) rhsTy
            branchResult →
          EnvSameShapeStrengthening selectedSource branchResult) →
        EnvSameShapeStrengthening selectedSource writeEnv ∧
          PartialTyStrengthens oldTy updatedTy ∧
          PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun _targets _path _selectedName _selectedSlot
      _selectedSlotTy _ => True)
    ?borrowHere ?box ?borrowStep ?target hselected) hbelow hupdate
      hbranchHere hbranchStep
  case borrowHere =>
      intro mutable targets pointee selectedTarget selectedTargetTy selectedTargetLifetime
        selectedName selectedSlot selectedSlotTy hmem htargetTyping htargetLoc
        _hselectedSlot _hselectedTy rank updatedTy writeEnv hbelow hupdate
        hbranchHere _hbranchStep
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
        cases htyEq
      · rcases hborrow with
          ⟨writeTargets, oldPointee, updatedPointee, htyEq, hupdatedEq,
            hpointee, hwrites⟩
        cases htyEq
        cases hupdatedEq
        have htargetRank :
            φ (LVal.base selectedTarget) < rootRank :=
          hbelow (LVal.base selectedTarget)
            (mem_partialTy_vars_iff.mpr
              ⟨true, _, pointee, selectedTarget, PartialTyContains.here, hmem, rfl⟩)
        have hleaves :=
          WriteBorrowTargets.initialized_leaves_of_typed hwrites
        have hmap :
            EnvSameShapeStrengthening selectedSource writeEnv :=
          WriteBorrowTargets.selected_branch_to_result_map
            (Nat.succ_pos rank) hwrites hleaves hmem
            (fun branchResult hbranchWrite =>
              hbranchHere (Nat.succ_pos rank) htargetRank htargetTyping
                htargetLoc hbranchWrite)
        exact ⟨hmap,
          PartialTyStrengthens.borrow (List.Subset.refl _)
            (PointeeUpdateAtPath.strengthens_of_positive hpointee
              (Nat.succ_pos rank)),
          by
            simp [PartialTy.sameShape, Ty.sameShape]
            exact PointeeUpdateAtPath.sameShape_of_positive hpointee
              (Nat.succ_pos rank)⟩
  case box =>
      intro inner path selectedName selectedSlot selectedSlotTy hinner ih
        rank updatedTy writeEnv hbelow hupdate hbranchHere hbranchStep
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, hupdatedEq, hinnerUpdate⟩
        cases htyEq
        cases hupdatedEq
        have hbelowInner :
            ∀ v, v ∈ PartialTy.vars inner → φ v < rootRank := by
          intro v hv
          exact hbelow v (by simpa [PartialTy.vars] using hv)
        rcases ih hbelowInner hinnerUpdate hbranchHere hbranchStep with
          ⟨hmap, hstrength, hshape⟩
        exact ⟨hmap, PartialTyStrengthens.box hstrength,
          by simpa [PartialTy.sameShape] using hshape⟩
      · rcases hborrow with
          ⟨targets, oldPointee, updatedPointee, htyEq, _hupdatedEq,
            _hpointee, _hwrites⟩
        cases htyEq
  case borrowStep =>
      intro mutable targets pointee path selectedName selectedSlot selectedSlotTy
        htargetsSelected _ih rank updatedTy writeEnv hbelow hupdate
        _hbranchHere hbranchStep
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
        cases htyEq
      · rcases hborrow with
          ⟨writeTargets, oldPointee, updatedPointee, htyEq, hupdatedEq,
            hpointee, hwrites⟩
        cases htyEq
        cases hupdatedEq
        cases htargetsSelected with
        | target htargetMem htargetTyping htargetSelected =>
            rename_i branchTarget branchPt branchLifetime
            have htargetRank :
                φ (LVal.base branchTarget) < rootRank := by
              exact hbelow (LVal.base branchTarget)
                (mem_partialTy_vars_iff.mpr
                  ⟨true, _, pointee, branchTarget, PartialTyContains.here,
                    htargetMem, rfl⟩)
            have hleaves :=
              WriteBorrowTargets.initialized_leaves_of_typed hwrites
            have hmap :
                EnvSameShapeStrengthening selectedSource writeEnv :=
              WriteBorrowTargets.selected_branch_to_result_map
                (Nat.succ_pos rank) hwrites hleaves htargetMem
                (fun branchResult hbranchWrite =>
                  hbranchStep (Nat.succ_pos rank) htargetRank htargetTyping htargetSelected
                    hbranchWrite)
            exact ⟨hmap,
              PartialTyStrengthens.borrow (List.Subset.refl _)
                (PointeeUpdateAtPath.strengthens_of_positive hpointee
                  (Nat.succ_pos rank)),
              by
                simp [PartialTy.sameShape, Ty.sameShape]
                exact PointeeUpdateAtPath.sameShape_of_positive hpointee
                  (Nat.succ_pos rank)⟩
  case target =>
      intros
      trivial

theorem EnvWrite.runtime_selected_lval_map_of_safe {store : ProgramStore}
    {env result : Env} {lifetime : Lifetime} {lv : LVal}
    {lvTy rhsTy selectedSlotTy : Ty} {selectedName : Name}
    {selectedSlot : EnvSlot} {rank : Nat} {φ : Name → Nat} :
    LinearizedBy φ env →
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty lvTy) lifetime →
    store.loc lv = some (VariableProjection selectedName) →
    env.slotAt selectedName = some selectedSlot →
    selectedSlot.ty = .ty selectedSlotTy →
    EnvWrite rank env lv rhsTy result →
    EnvSameShapeStrengthening
      (env.update selectedName { selectedSlot with ty := .ty rhsTy }) result := by
  intro hφ hsafe hheap htyping hloc hslot hslotTy hwrite
  exact goLVal hφ hsafe hheap htyping hloc hslot hslotTy hwrite
where
  goLVal {store : ProgramStore} {env result : Env}
      {lifetime : Lifetime} {lv : LVal} {lvTy rhsTy selectedSlotTy : Ty}
      {selectedName : Name} {selectedSlot : EnvSlot} {rank : Nat}
      {φ : Name → Nat}
      (hφ : LinearizedBy φ env) (hsafe : store ∼ₛ env)
      (hheap : StoreOwnerTargetsHeap store)
      (htyping : LValTyping env lv (.ty lvTy) lifetime)
      (hloc : store.loc lv = some (VariableProjection selectedName))
      (hslot : env.slotAt selectedName = some selectedSlot)
      (hslotTy : selectedSlot.ty = .ty selectedSlotTy)
      (hwrite : EnvWrite rank env lv rhsTy result) :
      EnvSameShapeStrengthening
        (env.update selectedName { selectedSlot with ty := .ty rhsTy })
        result := by
    cases lv with
    | var x =>
        rcases LValTyping.var_inv htyping with
          ⟨slot, henvSlot, _hslotTyEq, _hlifetimeEq⟩
        simp [ProgramStore.loc, VariableProjection] at hloc
        cases hloc
        have hslotEq : selectedSlot = slot :=
          Option.some.inj (hslot.symm.trans henvSlot)
        subst hslotEq
        exact EnvWrite.var_rhs_to_result_map henvSlot hslotTy hwrite
    | deref source =>
      cases htyping with
      | @box source inner sourceLifetime hsource =>
        have hsourceAbs : LValLocationAbstraction store source (.box (.ty lvTy)) :=
          lvalTyping_defined_location_of_safe hsafe hsource
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @box ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
            have hderefLoc : store.loc source.deref = some ownerLocation := by
              simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            have hownerEq : ownerLocation = VariableProjection selectedName := by
              rw [hloc] at hderefLoc
              exact (Option.some.inj hderefLoc).symm
            subst hownerEq
            have howns : ProgramStore.Owns store (VariableProjection selectedName) :=
              ⟨sourceLocation, sourceLifetime, by
                simpa [owningRef] using hsourceSlot⟩
            exact False.elim ((not_owns_var_of_storeOwnerTargetsHeap hheap) howns)
      | @borrow source mutable targets pointee borrowLifetime targetLifetime
          hsource htargets =>
        have hsourceAbs :
            LValLocationAbstraction store source (.ty (.borrow mutable targets lvTy)) :=
          lvalTyping_defined_location_of_safe hsafe hsource
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @borrow selectedLocation _mutable _targets _pointee selectedTarget hselectedMem
            htargetLocFromBorrow =>
            rcases lvalTargetsTyping_member_strengthens htargets _ hselectedMem with
              ⟨selectedTargetTy, selectedTargetLifetime, hselectedTyping,
                _hselectedStrengthens⟩
            have hderefLoc :
                store.loc source.deref = some selectedLocation := by
              simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            have hselectedLocationEq :
                selectedLocation = VariableProjection selectedName := by
              rw [hloc] at hderefLoc
              exact (Option.some.inj hderefLoc).symm
            have hselectedLocVar :
                store.loc selectedTarget = some (VariableProjection selectedName) := by
              simpa [hselectedLocationEq] using htargetLocFromBorrow
            have hpathSelected :
                RuntimePathSelected store env (.ty (.borrow mutable targets lvTy)) [()]
                  selectedName selectedSlot selectedSlotTy :=
              RuntimePathSelected.borrowHere hselectedMem hselectedTyping
                hselectedLocVar hslot hslotTy
            exact goPath hφ hsafe hheap hsource hpathSelected
              hslot hslotTy (by simpa [prependPath] using hwrite)
  termination_by (φ (LVal.base lv), sizeOf lv, 1)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp))
      | exact Prod.Lex.left _ _ (by assumption)

  goPath {store : ProgramStore} {env result : Env}
      {lifetime : Lifetime} {lv : LVal} {pt : PartialTy}
      {path : List Unit} {rhsTy selectedSlotTy : Ty} {selectedName : Name}
      {selectedSlot : EnvSlot} {rank : Nat} {φ : Name → Nat}
      (hφ : LinearizedBy φ env) (hsafe : store ∼ₛ env)
      (hheap : StoreOwnerTargetsHeap store)
      (htyping : LValTyping env lv pt lifetime)
      (hselected : RuntimePathSelected store env pt path selectedName
        selectedSlot selectedSlotTy)
      (hslot : env.slotAt selectedName = some selectedSlot)
      (hslotTy : selectedSlot.ty = .ty selectedSlotTy)
      (hwrite : EnvWrite rank env (prependPath path lv) rhsTy result) :
      EnvSameShapeStrengthening
        (env.update selectedName { selectedSlot with ty := .ty rhsTy })
        result := by
    cases hwrite with
    | @intro _rank _env₁ writeEnv _writeLv writeSlot _ty updatedTy
        hwriteSlot hupdate =>
        have hwriteSlotBase :
            env.slotAt (LVal.base lv) = some writeSlot := by
          simpa [base_prependPath] using hwriteSlot
        have hupdatePath :
            UpdateAtPath rank env (LVal.path lv ++ path) writeSlot.ty rhsTy
              writeEnv updatedTy := by
          simpa [path_prependPath] using hupdate
        have hselectedBase :
            RuntimePathSelected store env writeSlot.ty (LVal.path lv ++ path)
              selectedName selectedSlot selectedSlotTy :=
          RuntimePathSelected.prepend_of_lvalTyping htyping hwriteSlotBase path
            hselected
        have hbelow :
            ∀ v, v ∈ PartialTy.vars writeSlot.ty → φ v < φ (LVal.base lv) :=
          hφ (LVal.base lv) writeSlot hwriteSlotBase
        rcases RuntimePathSelected.updateAtPath_map
            (store := store) (env := env)
            (selectedSource :=
              env.update selectedName { selectedSlot with ty := .ty rhsTy })
            (φ := φ) (rootRank := φ (LVal.base lv))
            hbelow hselectedBase hupdatePath
            (fun {branchRank target targetTy branchLifetime branchResult}
                _hbranchRank htargetRank htargetTyping htargetLoc
                hbranchWrite =>
              goLVal hφ hsafe hheap htargetTyping htargetLoc
                hslot hslotTy hbranchWrite)
            (fun {branchRank target branchPt branchLifetime branchPath branchResult}
                _hbranchRank htargetRank htargetTyping htargetSelected
                hbranchWrite =>
              goPath hφ hsafe hheap htargetTyping
                htargetSelected hslot hslotTy hbranchWrite)
          with ⟨hmap, hstrength, hshape⟩
        have hselectedRankLt :
            φ selectedName < φ (LVal.base lv) :=
          RuntimePathSelected.rank_lt_of_lvalTyping hφ hsafe hheap hselected htyping
        have hselectedNeRoot : selectedName ≠ LVal.base lv := by
          intro hEq
          subst hEq
          exact Nat.lt_irrefl _ hselectedRankLt
        have hrootNeSelected : LVal.base lv ≠ selectedName := by
          intro hEq
          exact hselectedNeRoot hEq.symm
        have hslotStrong :
            (env.update selectedName { selectedSlot with ty := .ty rhsTy }).slotAt
              (LVal.base (prependPath path lv)) = some writeSlot := by
          simpa [base_prependPath, Env.update, hrootNeSelected] using
            hwriteSlotBase
        have hfinal :
            EnvSameShapeStrengthening
              (env.update selectedName { selectedSlot with ty := .ty rhsTy })
              (writeEnv.update (LVal.base (prependPath path lv))
                { writeSlot with ty := updatedTy }) :=
          EnvSameShapeStrengthening.update_result_strengthening
            hmap hslotStrong rfl hstrength hshape
        simpa [base_prependPath] using hfinal
  termination_by (φ (LVal.base lv), sizeOf lv, 0)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      exact Prod.Lex.left _ _ (by assumption)

theorem EnvWrite.runtime_selected_lval_map {store : ProgramStore}
    {env result : Env} {current lifetime : Lifetime} {lv : LVal}
    {lvTy rhsTy selectedSlotTy : Ty} {selectedName : Name}
    {selectedSlot : EnvSlot} {rank : Nat} {φ : Name → Nat} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty lvTy) lifetime →
    store.loc lv = some (VariableProjection selectedName) →
    env.slotAt selectedName = some selectedSlot →
    selectedSlot.ty = .ty selectedSlotTy →
    EnvWrite rank env lv rhsTy result →
    EnvSameShapeStrengthening
      (env.update selectedName { selectedSlot with ty := .ty rhsTy }) result := by
  intro hφ _hwellFormed hsafe hheap htyping hloc hslot hslotTy hwrite
  exact EnvWrite.runtime_selected_lval_map_of_safe hφ hsafe hheap
    htyping hloc hslot hslotTy hwrite

theorem lval_loc_var_slot_full_of_lvalTyping {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : Ty} {lifetime : Lifetime}
    {x : Name} {slot : EnvSlot} :
    WellFormedEnv env current →
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty ty) lifetime →
    store.loc lv = some (VariableProjection x) →
    env.slotAt x = some slot →
    ∃ slotTy, slot.ty = .ty slotTy := by
  intro hwellFormed hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      ∀ ty, partialTy = .ty ty →
        store.loc lv = some (VariableProjection x) →
        env.slotAt x = some slot →
        ∃ slotTy, slot.ty = .ty slotTy)
    (motive_2 := fun targets partialTy lifetime _ =>
      ∀ target, target ∈ targets →
        store.loc target = some (VariableProjection x) →
        env.slotAt x = some slot →
        ∃ slotTy, slot.ty = .ty slotTy)
    ?var ?box ?borrow ?empty ?singleton ?cons htyping ty rfl
  · intro y envSlot henvSlot ty hty hloc hxSlot
    simp [ProgramStore.loc, VariableProjection] at hloc
    cases hloc
    have hslotEq : slot = envSlot :=
      Option.some.inj (hxSlot.symm.trans henvSlot)
    subst hslotEq
    exact ⟨ty, hty⟩
  · intro source inner sourceLifetime hsource _ih ty hty hloc _hxSlot
    cases hty
    have hsourceAbs : LValLocationAbstraction store source (.box (.ty ty)) :=
      lvalTyping_defined_location hwellFormed hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @box ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) :=
          ⟨sourceLocation, sourceSlotLifetime, by
            simpa [owningRef] using hsourceSlot⟩
        exact False.elim ((not_owns_var_of_storeOwnerTargetsHeap hheap) howns)
  · intro source mutable targets pointee borrowLifetime targetLifetime
      hsource htargets _ihSource ihTargets ty hty hloc hxSlot
    cases hty
    have hsourceAbs :
        LValLocationAbstraction store source (.ty (.borrow mutable targets pointee)) :=
      lvalTyping_defined_location hwellFormed hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrow selectedLocation _mutable _targets _pointee selected hmem hselectedLoc =>
        have hderefLoc : store.loc source.deref = some selectedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hselectedLocationEq : selectedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        have hselectedLocVar :
            store.loc selected = some (VariableProjection x) := by
          simpa [hselectedLocationEq] using hselectedLoc
        exact ihTargets selected hmem hselectedLocVar hxSlot
  · intro ty hvars selected hmem hloc hxSlot
    cases hmem
  · intro target targetTy targetLifetime _htarget ihTarget selected hmem hloc hxSlot
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ihTarget targetTy rfl hloc hxSlot
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest _hunion _hintersection ihHead ihRest selected hmem hloc
      hxSlot
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst hhead
      exact ihHead headTy rfl hloc hxSlot
    · exact ihRest selected htail hloc hxSlot

mutual
  /--
  A path through a partial type whose runtime-selected borrow branch eventually
  resolves to the heap location `.heap address`.  Heap mirror of
  `RuntimePathSelected`: the selected leaf is an owned heap cell rather than a
  variable, so no environment slot is carried; the owner-spine data is
  reconstructed at the consuming branch from the pure-box typing of the final
  selected target.
  -/
  inductive RuntimeSpinePathSelected (store : ProgramStore) (env : Env) :
      PartialTy → List Unit → Nat → Prop where
    | borrowHere {mutable : Bool} {targets : List LVal} {pointee : Ty}
        {selectedTarget : LVal} {selectedTargetTy : Ty}
        {selectedTargetLifetime : Lifetime} {address : Nat} :
        selectedTarget ∈ targets →
        LValTyping env selectedTarget (.ty selectedTargetTy)
          selectedTargetLifetime →
        store.loc selectedTarget = some (.heap address) →
        RuntimeSpinePathSelected store env (.ty (.borrow mutable targets pointee))
          [()] address
    | box {inner : PartialTy} {path : List Unit} {address : Nat} :
        RuntimeSpinePathSelected store env inner path address →
        RuntimeSpinePathSelected store env (.box inner) (() :: path) address
    | borrowStep {mutable : Bool} {targets : List LVal} {pointee : Ty}
        {path : List Unit} {address : Nat} :
        RuntimeSpineTargetsSelected store env targets path address →
        RuntimeSpinePathSelected store env (.ty (.borrow mutable targets pointee))
          (() :: path) address

  inductive RuntimeSpineTargetsSelected (store : ProgramStore) (env : Env) :
      List LVal → List Unit → Nat → Prop where
    | target {targets : List LVal} {target : LVal} {pt : PartialTy}
        {lifetime : Lifetime} {path : List Unit} {address : Nat} :
        target ∈ targets →
        LValTyping env target pt lifetime →
        RuntimeSpinePathSelected store env pt path address →
        RuntimeSpineTargetsSelected store env targets path address
end

theorem RuntimeSpinePathSelected.of_partialTyUnion {store : ProgramStore}
    {env : Env} {left right union : PartialTy} {path : List Unit}
    {address : Nat} :
    PartialTyUnion left right union →
    RuntimeSpinePathSelected store env union path address →
    RuntimeSpinePathSelected store env left path address ∨
      RuntimeSpinePathSelected store env right path address := by
  intro hunion hselected
  refine RuntimeSpinePathSelected.rec
    (motive_1 := fun union path address _ =>
      ∀ left right,
        PartialTyUnion left right union →
        RuntimeSpinePathSelected store env left path address ∨
          RuntimeSpinePathSelected store env right path address)
    (motive_2 := fun _targets _path _address _ => True)
    ?borrowHere ?box ?borrowStep ?target hselected left right hunion
  case borrowHere =>
    intro mutable targets pointee selectedTarget selectedTargetTy
      selectedTargetLifetime address hmem htyping hloc left right hunion
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.left_strengthens hunion) with
      ⟨leftTargets, _leftPointee, hleftEq, _hleftSubset, _hleftPointee⟩
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.right_strengthens hunion) with
      ⟨rightTargets, _rightPointee, hrightEq, _hrightSubset, _hrightPointee⟩
    cases hleftEq
    cases hrightEq
    rcases PartialTyUnion.borrow_member hunion hmem with hleft | hright
    · exact Or.inl
        (RuntimeSpinePathSelected.borrowHere hleft htyping hloc)
    · exact Or.inr
        (RuntimeSpinePathSelected.borrowHere hright htyping hloc)
  case box =>
    intro inner path address hinner ih left right hunion
    have hleftStrength := PartialTyUnion.left_strengthens hunion
    cases hleftStrength with
    | reflex =>
        exact Or.inl (RuntimeSpinePathSelected.box hinner)
    | box hleftInner =>
        have hrightStrength := PartialTyUnion.right_strengthens hunion
        cases hrightStrength with
        | reflex =>
            exact Or.inr (RuntimeSpinePathSelected.box hinner)
        | box hrightInner =>
            rcases ih _ _ (PartialTyUnion.box_inv hunion) with hleft | hright
            · exact Or.inl (RuntimeSpinePathSelected.box hleft)
            · exact Or.inr (RuntimeSpinePathSelected.box hright)
  case borrowStep =>
    intro mutable targets pointee path address htargets _ih left right hunion
    cases htargets with
    | target hmem htargetTyping hpath =>
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.left_strengthens hunion) with
          ⟨leftTargets, _leftPointee, hleftEq, _hleftSubset, _hleftPointee⟩
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.right_strengthens hunion) with
          ⟨rightTargets, _rightPointee, hrightEq, _hrightSubset, _hrightPointee⟩
        cases hleftEq
        cases hrightEq
        rcases PartialTyUnion.borrow_member hunion hmem with hleft | hright
        · exact Or.inl (RuntimeSpinePathSelected.borrowStep
            (RuntimeSpineTargetsSelected.target hleft htargetTyping hpath))
        · exact Or.inr (RuntimeSpinePathSelected.borrowStep
            (RuntimeSpineTargetsSelected.target hright htargetTyping hpath))
  case target =>
    intros
    trivial

theorem RuntimeSpineTargetsSelected.of_lvalTargetsTyping {store : ProgramStore}
    {env : Env} {targets : List LVal} {pt : PartialTy} {lifetime : Lifetime}
    {path : List Unit} {address : Nat} :
    LValTargetsTyping env targets pt lifetime →
    RuntimeSpinePathSelected store env pt path address →
    RuntimeSpineTargetsSelected store env targets path address := by
  intro htargets hselected
  refine LValTargetsTyping.rec
    (motive_1 := fun _target _ty _lifetime _htyping => True)
    (motive_2 := fun targets pt lifetime _htyping =>
      ∀ {path : List Unit} {address : Nat},
        RuntimeSpinePathSelected store env pt path address →
        RuntimeSpineTargetsSelected store env targets path address)
    ?var ?box ?borrow ?empty ?singleton ?cons htargets hselected
  case var | box | borrow => intros; trivial
  case empty =>
      intros
      rename_i hselected
      cases hselected <;> simp_all [PartialTy.allVars, Ty.allVars, List.mem_map]
      rename_i htargets
      cases htargets with
      | target hmem _ _ => cases hmem
  case singleton =>
      intro target ty lifetime htarget _ih path address hselected
      exact RuntimeSpineTargetsSelected.target (by simp) htarget hselected
  case cons =>
      intro target rest headTy headLifetime restLifetime lifetime restTy
        unionTy hhead _hrest hunion _hintersection _ihHead ihRest
        path address hselected
      rcases RuntimeSpinePathSelected.of_partialTyUnion hunion hselected with
        hheadSelected | hrestSelected
      · exact RuntimeSpineTargetsSelected.target (by simp) hhead hheadSelected
      · cases ihRest hrestSelected with
        | target hmem htargetTyping hpath =>
            exact RuntimeSpineTargetsSelected.target
              (List.mem_cons_of_mem _ hmem) htargetTyping hpath

theorem RuntimeSpinePathSelected.prepend_of_lvalTyping {store : ProgramStore}
    {env : Env} {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {address : Nat}
    (htyping : LValTyping env lv pt lifetime) :
    ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
    ∀ (path : List Unit),
      RuntimeSpinePathSelected store env pt path address →
      RuntimeSpinePathSelected store env slot.ty (LVal.path lv ++ path)
        address := by
  refine LValTyping.rec
    (motive_1 := fun lv pt _lifetime _ =>
      ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
      ∀ (path : List Unit),
        RuntimeSpinePathSelected store env pt path address →
        RuntimeSpinePathSelected store env slot.ty (LVal.path lv ++ path)
          address)
    (motive_2 := fun _targets _pt _lifetime _ => True)
    ?var ?box ?borrow ?empty ?singleton ?cons htyping
  case var =>
    intro x slot hslot slot' hslot' path hselected
    simp only [LVal.base] at hslot'
    have hslotEq : slot = slot' := by
      rw [hslot] at hslot'
      exact Option.some.inj hslot'
    subst hslotEq
    simpa [LVal.path] using hselected
  case box =>
    intro source inner sourceLifetime _hsource ih slot hslot path hselected
    rw [LVal.path, List.append_assoc]
    exact ih hslot (() :: path) (RuntimeSpinePathSelected.box hselected)
  case borrow =>
    intro source mutable targets pointee borrowLifetime targetLifetime
      _hsource htargets ih _ihTargets slot hslot path hselected
    rw [LVal.path, List.append_assoc]
    exact ih hslot (() :: path)
      (RuntimeSpinePathSelected.borrowStep
        (RuntimeSpineTargetsSelected.of_lvalTargetsTyping htargets hselected))
  case empty =>
    intros
    trivial
  case singleton | cons =>
    intros
    trivial

mutual
  theorem RuntimeSpinePathSelected.rank_lt_of_lvalTyping
      {store : ProgramStore} {env : Env} {φ : Name → Nat}
      {xRoot : Name}
      (hφ : LinearizedBy φ env)
      (hsafe : store ∼ₛ env) (hvalidStore : ValidStore store)
      (hheap : StoreOwnerTargetsHeap store) :
      ∀ {pt : PartialTy} {path : List Unit} {address : Nat},
        RuntimeSpinePathSelected store env pt path address →
        ProtectedByBase store xRoot (.heap address) →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv pt lifetime →
          φ xRoot < φ (LVal.base lv)
    | .ty (.borrow mutable targets pointee), [()], address,
      RuntimeSpinePathSelected.borrowHere hmem htargetTyping htargetLoc,
      hprot, lv, lifetime, htyping => by
        rcases RuntimeFrame.loc_intrinsicRootRank_of_safe hφ hsafe
            htargetTyping htargetLoc with
          ⟨root', hprot', hrank'⟩
        have hrootEq : root' = xRoot :=
          ProtectedByBase.root_unique hvalidStore hheap hprot' hprot
        subst hrootEq
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars
              (.ty (.borrow mutable targets pointee)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, pointee, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_of_le_of_lt hrank' htargetLtLv
    | .box inner, () :: path, address,
      RuntimeSpinePathSelected.box hinner, hprot, lv, lifetime, htyping => by
        have hderef : LValTyping env (.deref lv) inner lifetime :=
          LValTyping.box htyping
        simpa [LVal.base] using
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping hφ hsafe
            hvalidStore hheap hinner hprot hderef
    | .ty (.borrow mutable targets pointee), () :: path, address,
      RuntimeSpinePathSelected.borrowStep htargets, hprot, lv, lifetime,
      htyping => by
        exact RuntimeSpineTargetsSelected.rank_lt_of_lvalTyping hφ
          hsafe hvalidStore hheap htargets hprot htyping

  theorem RuntimeSpineTargetsSelected.rank_lt_of_lvalTyping
      {store : ProgramStore} {env : Env} {φ : Name → Nat}
      {xRoot : Name}
      (hφ : LinearizedBy φ env)
      (hsafe : store ∼ₛ env) (hvalidStore : ValidStore store)
      (hheap : StoreOwnerTargetsHeap store) :
      ∀ {targets : List LVal} {path : List Unit} {address : Nat},
        RuntimeSpineTargetsSelected store env targets path address →
        ProtectedByBase store xRoot (.heap address) →
        ∀ {mutable : Bool} {pointee : Ty} {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv (.ty (.borrow mutable targets pointee)) lifetime →
          φ xRoot < φ (LVal.base lv)
    | targets, path, address,
      RuntimeSpineTargetsSelected.target hmem htargetTyping hpath, hprot,
      mutable, pointee, lv, lifetime, htyping => by
        have hselectedLtTarget :
            φ xRoot < φ (LVal.base _) :=
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping hφ hsafe
            hvalidStore hheap hpath hprot htargetTyping
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars
              (.ty (.borrow mutable targets pointee)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, pointee, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_trans hselectedLtTarget htargetLtLv
end

theorem RuntimeSpinePathSelected.updateAtPath_map {store : ProgramStore}
    {env selectedSource writeEnv : Env}
    {oldTy updatedTy : PartialTy} {path : List Unit} {rank : Nat}
    {rhsTy : Ty} {address : Nat} {φ : Name → Nat} {rootRank : Nat} :
    (∀ v, v ∈ PartialTy.vars oldTy → φ v < rootRank) →
    RuntimeSpinePathSelected store env oldTy path address →
    UpdateAtPath rank env path oldTy rhsTy writeEnv updatedTy →
    (∀ {branchRank : Nat} {target : LVal} {targetTy : Ty}
      {lifetime : Lifetime} {branchResult : Env},
      0 < branchRank →
      φ (LVal.base target) < rootRank →
      LValTyping env target (.ty targetTy) lifetime →
      store.loc target = some (.heap address) →
      EnvWrite branchRank env target rhsTy branchResult →
      EnvSameShapeStrengthening selectedSource branchResult) →
    (∀ {branchRank : Nat} {target : LVal} {pt : PartialTy}
      {lifetime : Lifetime} {branchPath : List Unit} {branchResult : Env},
      0 < branchRank →
      φ (LVal.base target) < rootRank →
      LValTyping env target pt lifetime →
      RuntimeSpinePathSelected store env pt branchPath address →
      EnvWrite branchRank env (prependPath branchPath target) rhsTy
        branchResult →
      EnvSameShapeStrengthening selectedSource branchResult) →
    EnvSameShapeStrengthening selectedSource writeEnv ∧
      PartialTyStrengthens oldTy updatedTy ∧
      PartialTy.sameShape oldTy updatedTy := by
  intro hbelow hselected hupdate hbranchHere hbranchStep
  refine (RuntimeSpinePathSelected.rec
    (motive_1 := fun oldTy path address _hselected =>
      ∀ {rank : Nat} {updatedTy : PartialTy} {writeEnv : Env},
        (∀ v, v ∈ PartialTy.vars oldTy → φ v < rootRank) →
        UpdateAtPath rank env path oldTy rhsTy writeEnv updatedTy →
        (∀ {branchRank : Nat} {target : LVal} {targetTy : Ty}
          {lifetime : Lifetime} {branchResult : Env},
          0 < branchRank →
          φ (LVal.base target) < rootRank →
          LValTyping env target (.ty targetTy) lifetime →
          store.loc target = some (.heap address) →
          EnvWrite branchRank env target rhsTy branchResult →
          EnvSameShapeStrengthening selectedSource branchResult) →
        (∀ {branchRank : Nat} {target : LVal} {pt : PartialTy}
          {lifetime : Lifetime} {branchPath : List Unit} {branchResult : Env},
          0 < branchRank →
          φ (LVal.base target) < rootRank →
          LValTyping env target pt lifetime →
          RuntimeSpinePathSelected store env pt branchPath address →
          EnvWrite branchRank env (prependPath branchPath target) rhsTy
            branchResult →
          EnvSameShapeStrengthening selectedSource branchResult) →
        EnvSameShapeStrengthening selectedSource writeEnv ∧
          PartialTyStrengthens oldTy updatedTy ∧
          PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun _targets _path _address _ => True)
    ?borrowHere ?box ?borrowStep ?target hselected) hbelow hupdate
      hbranchHere hbranchStep
  case borrowHere =>
      intro mutable targets pointee selectedTarget selectedTargetTy
        selectedTargetLifetime address hmem htargetTyping htargetLoc rank
        updatedTy writeEnv hbelow hupdate hbranchHere _hbranchStep
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
        cases htyEq
      · rcases hborrow with
          ⟨writeTargets, oldPointee, updatedPointee, htyEq, hupdatedEq,
            hpointee, hwrites⟩
        cases htyEq
        cases hupdatedEq
        have htargetRank :
            φ (LVal.base selectedTarget) < rootRank :=
          hbelow (LVal.base selectedTarget)
            (mem_partialTy_vars_iff.mpr
              ⟨true, _, pointee, selectedTarget, PartialTyContains.here, hmem, rfl⟩)
        have hleaves :=
          WriteBorrowTargets.initialized_leaves_of_typed hwrites
        have hmap :
            EnvSameShapeStrengthening selectedSource writeEnv :=
          WriteBorrowTargets.selected_branch_to_result_map
            (Nat.succ_pos rank) hwrites hleaves hmem
            (fun branchResult hbranchWrite =>
              hbranchHere (Nat.succ_pos rank) htargetRank htargetTyping
                htargetLoc hbranchWrite)
        exact ⟨hmap,
          PartialTyStrengthens.borrow (List.Subset.refl _)
            (PointeeUpdateAtPath.strengthens_of_positive hpointee
              (Nat.succ_pos rank)),
          by
            simp [PartialTy.sameShape, Ty.sameShape]
            exact PointeeUpdateAtPath.sameShape_of_positive hpointee
              (Nat.succ_pos rank)⟩
  case box =>
      intro inner path address hinner ih
        rank updatedTy writeEnv hbelow hupdate hbranchHere hbranchStep
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, hupdatedEq, hinnerUpdate⟩
        cases htyEq
        cases hupdatedEq
        have hbelowInner :
            ∀ v, v ∈ PartialTy.vars inner → φ v < rootRank := by
          intro v hv
          exact hbelow v (by simpa [PartialTy.vars] using hv)
        rcases ih hbelowInner hinnerUpdate hbranchHere hbranchStep with
          ⟨hmap, hstrength, hshape⟩
        exact ⟨hmap, PartialTyStrengthens.box hstrength,
          by simpa [PartialTy.sameShape] using hshape⟩
      · rcases hborrow with
          ⟨targets, oldPointee, updatedPointee, htyEq, _hupdatedEq,
            _hpointee, _hwrites⟩
        cases htyEq
  case borrowStep =>
      intro mutable targets pointee path address htargetsSelected _ih rank updatedTy
        writeEnv hbelow hupdate _hbranchHere hbranchStep
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
        cases htyEq
      · rcases hborrow with
          ⟨writeTargets, oldPointee, updatedPointee, htyEq, hupdatedEq,
            hpointee, hwrites⟩
        cases htyEq
        cases hupdatedEq
        cases htargetsSelected with
        | target htargetMem htargetTyping htargetSelected =>
            rename_i branchTarget branchPt branchLifetime
            have htargetRank :
                φ (LVal.base branchTarget) < rootRank := by
              exact hbelow (LVal.base branchTarget)
                (mem_partialTy_vars_iff.mpr
                  ⟨true, _, pointee, branchTarget, PartialTyContains.here, htargetMem,
                    rfl⟩)
            have hleaves :=
              WriteBorrowTargets.initialized_leaves_of_typed hwrites
            have hmap :
                EnvSameShapeStrengthening selectedSource writeEnv :=
              WriteBorrowTargets.selected_branch_to_result_map
                (Nat.succ_pos rank) hwrites hleaves htargetMem
                (fun branchResult hbranchWrite =>
                  hbranchStep (Nat.succ_pos rank) htargetRank htargetTyping
                    htargetSelected hbranchWrite)
            exact ⟨hmap,
              PartialTyStrengthens.borrow (List.Subset.refl _)
                (PointeeUpdateAtPath.strengthens_of_positive hpointee
                  (Nat.succ_pos rank)),
              by
                simp [PartialTy.sameShape, Ty.sameShape]
                exact PointeeUpdateAtPath.sameShape_of_positive hpointee
                  (Nat.succ_pos rank)⟩
  case target =>
      intros
      trivial

/--
Heap mirror of `EnvWrite.runtime_selected_lval_map`: writing through an lvalue
that resolves to an owned heap cell transports the strongly-updated owner root
to the fan-out result by same-shape strengthening.
-/
theorem EnvWrite.runtime_selected_spine_map_of_safe {store : ProgramStore}
    {env result : Env} {lifetime : Lifetime} {lv : LVal}
    {lvTy rhsTy : Ty} {address : Nat} {xRoot : Name} {envSlot : EnvSlot}
    {rootSlot leafSlot : StoreSlot} {spinePath : List Unit} {leafTy : Ty}
    {rank : Nat} {φ : Name → Nat} :
    LinearizedBy φ env →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env.slotAt xRoot = some envSlot →
    StoreOwnerSpine store (VariableProjection xRoot) rootSlot envSlot.ty
      spinePath (.heap address) leafSlot (.ty leafTy) →
    spinePath ≠ [] →
    LValTyping env lv (.ty lvTy) lifetime →
    store.loc lv = some (.heap address) →
    EnvWrite rank env lv rhsTy result →
    EnvSameShapeStrengthening
      (env.update xRoot
        { envSlot with
            ty := PartialTy.strongLeafUpdate envSlot.ty spinePath rhsTy })
      result := by
  intro hφ hsafe hvalidStore hheap hrootSlot hspine hspineNonempty
    htyping hloc hwrite
  exact goLVal hφ hsafe hvalidStore hheap hrootSlot hspine
    hspineNonempty htyping hloc hwrite
where
  goLVal {store : ProgramStore} {env result : Env}
      {lifetime : Lifetime} {lv : LVal} {lvTy rhsTy : Ty}
      {address : Nat} {xRoot : Name} {envSlot : EnvSlot}
      {rootSlot leafSlot : StoreSlot} {spinePath : List Unit} {leafTy : Ty}
      {rank : Nat} {φ : Name → Nat}
      (hφ : LinearizedBy φ env) (hsafe : store ∼ₛ env)
      (hvalidStore : ValidStore store)
      (hheap : StoreOwnerTargetsHeap store)
      (hrootSlot : env.slotAt xRoot = some envSlot)
      (hspine : StoreOwnerSpine store (VariableProjection xRoot) rootSlot
        envSlot.ty spinePath (.heap address) leafSlot (.ty leafTy))
      (hspineNonempty : spinePath ≠ [])
      (htyping : LValTyping env lv (.ty lvTy) lifetime)
      (hloc : store.loc lv = some (.heap address))
      (hwrite : EnvWrite rank env lv rhsTy result) :
      EnvSameShapeStrengthening
        (env.update xRoot
          { envSlot with
              ty := PartialTy.strongLeafUpdate envSlot.ty spinePath rhsTy })
        result := by
    cases lv with
    | var x =>
        simp [ProgramStore.loc] at hloc
    | deref source =>
      cases htyping with
      | @box _ _ sourceLifetime hsource =>
        rcases StoreOwnerSpine.of_lvalTyping_box_of_safe hsafe hsource with
          ⟨envSlot', rootSlot', sourceLocation, sourceSlot, henvBase,
            hrootSlot', hrootLifetime', hsourceLoc, hsourceSlot, hsourceSpine⟩
        have hsourceValid := StoreOwnerSpine.leaf_valid hsourceSpine
        rcases sourceSlot with ⟨sourceValue, sourceLifetime'⟩
        cases hsourceValid with
        | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
            have hderefLoc :
                store.loc (.deref source) = some ownerLocation := by
              simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            have hlocEq : Location.heap address = ownerLocation := by
              rw [hloc] at hderefLoc
              exact Option.some.inj hderefLoc
            have hsnoc :=
              StoreOwnerSpine.snoc_box hsourceSpine rfl rfl hownedSlot
                hinnerValid
            rw [← hlocEq] at hsnoc
            have hlocalProt :
                ProtectedByBase store (LVal.base source) (.heap address) :=
              Or.inr (StoreOwnerSpine.ownsTransitively_of_nonempty hsnoc
                (by simp))
            have hrootProt :
                ProtectedByBase store xRoot (.heap address) :=
              Or.inr (StoreOwnerSpine.ownsTransitively_of_nonempty hspine
                hspineNonempty)
            have hbaseEq : LVal.base source = xRoot :=
              ProtectedByBase.root_unique hvalidStore hheap hlocalProt
                hrootProt
            have henvSlotEq : envSlot' = envSlot := by
              rw [hbaseEq] at henvBase
              exact Option.some.inj (henvBase.symm.trans hrootSlot)
            rw [henvSlotEq, hbaseEq] at hsnoc
            have hpathEq : spinePath = () :: LVal.path source :=
              StoreOwnerSpine.path_unique hspine hsnoc
            cases hwrite with
            | @intro _rank _env₁ writeEnv _writeLv writeSlot _ty updatedTy
                hwriteSlot hupdate =>
                have hwriteSlotBase :
                    env.slotAt (LVal.base source) = some writeSlot := by
                  simpa [LVal.base] using hwriteSlot
                have hwriteSlotEq : writeSlot = envSlot := by
                  rw [hbaseEq] at hwriteSlotBase
                  exact Option.some.inj (hwriteSlotBase.symm.trans hrootSlot)
                have hupdatePath :
                    UpdateAtPath rank env (() :: LVal.path source) envSlot.ty
                      rhsTy writeEnv updatedTy := by
                  rw [← hwriteSlotEq]
                  simpa [LVal.path_deref_cons] using hupdate
                have hwriteEnvEq : writeEnv = env :=
                  StoreOwnerSpine.updateAtPath_env_eq hsnoc hupdatePath
                rcases StoreOwnerSpine.strongLeafUpdate_strengthens_updateAtPath
                    hsnoc rfl hupdatePath with ⟨hstrength, hshape⟩
                rw [hwriteEnvEq, hpathEq]
                have hfinal :
                    EnvSameShapeStrengthening
                      (env.update xRoot
                        { envSlot with
                            ty := PartialTy.strongLeafUpdate envSlot.ty
                              (() :: LVal.path source) rhsTy })
                      (env.update xRoot { envSlot with ty := updatedTy }) :=
                  EnvSameShapeStrengthening.update_same rfl hstrength hshape
                have hgoalEq :
                    env.update (LVal.base (LVal.deref source))
                        { writeSlot with ty := updatedTy } =
                      env.update xRoot { envSlot with ty := updatedTy } := by
                  rw [hwriteSlotEq]
                  simp [LVal.base, hbaseEq]
                rw [hgoalEq]
                exact hfinal
      | @borrow _ mutable targets pointee borrowLifetime targetLifetime
          hsource htargets =>
        have hsourceAbs :
            LValLocationAbstraction store source
              (.ty (.borrow mutable targets lvTy)) :=
          lvalTyping_defined_location_of_safe hsafe hsource
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime'⟩
        cases hsourceValid with
        | @borrow selectedLocation _mutable _targets _pointee selectedTarget
            hselectedMem htargetLocFromBorrow =>
            rcases lvalTargetsTyping_member_strengthens htargets _
                hselectedMem with
              ⟨selectedTargetTy, selectedTargetLifetime, hselectedTyping,
                _hselectedStrengthens⟩
            have hderefLoc :
                store.loc source.deref = some selectedLocation := by
              simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            have hselectedLocationEq :
                selectedLocation = Location.heap address := by
              rw [hloc] at hderefLoc
              exact (Option.some.inj hderefLoc).symm
            have hselectedLocHeap :
                store.loc selectedTarget = some (.heap address) := by
              simpa [hselectedLocationEq] using htargetLocFromBorrow
            have hpathSelected :
                RuntimeSpinePathSelected store env
                  (.ty (.borrow mutable targets lvTy)) [()] address :=
              RuntimeSpinePathSelected.borrowHere hselectedMem
                hselectedTyping hselectedLocHeap
            exact goPath hφ hsafe hvalidStore hheap hrootSlot
              hspine hspineNonempty hsource hpathSelected
              (by simpa [prependPath] using hwrite)
  termination_by (φ (LVal.base lv), sizeOf lv, 1)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp))
      | exact Prod.Lex.left _ _ (by assumption)

  goPath {store : ProgramStore} {env result : Env}
      {lifetime : Lifetime} {lv : LVal} {pt : PartialTy}
      {path : List Unit} {rhsTy : Ty} {address : Nat} {xRoot : Name}
      {envSlot : EnvSlot} {rootSlot leafSlot : StoreSlot}
      {spinePath : List Unit} {leafTy : Ty} {rank : Nat} {φ : Name → Nat}
      (hφ : LinearizedBy φ env) (hsafe : store ∼ₛ env)
      (hvalidStore : ValidStore store)
      (hheap : StoreOwnerTargetsHeap store)
      (hrootSlot : env.slotAt xRoot = some envSlot)
      (hspine : StoreOwnerSpine store (VariableProjection xRoot) rootSlot
        envSlot.ty spinePath (.heap address) leafSlot (.ty leafTy))
      (hspineNonempty : spinePath ≠ [])
      (htyping : LValTyping env lv pt lifetime)
      (hselected : RuntimeSpinePathSelected store env pt path address)
      (hwrite : EnvWrite rank env (prependPath path lv) rhsTy result) :
      EnvSameShapeStrengthening
        (env.update xRoot
          { envSlot with
              ty := PartialTy.strongLeafUpdate envSlot.ty spinePath rhsTy })
        result := by
    cases hwrite with
    | @intro _rank _env₁ writeEnv _writeLv writeSlot _ty updatedTy
        hwriteSlot hupdate =>
        have hwriteSlotBase :
            env.slotAt (LVal.base lv) = some writeSlot := by
          simpa [base_prependPath] using hwriteSlot
        have hupdatePath :
            UpdateAtPath rank env (LVal.path lv ++ path) writeSlot.ty rhsTy
              writeEnv updatedTy := by
          simpa [path_prependPath] using hupdate
        have hselectedBase :
            RuntimeSpinePathSelected store env writeSlot.ty
              (LVal.path lv ++ path) address :=
          RuntimeSpinePathSelected.prepend_of_lvalTyping htyping
            hwriteSlotBase path hselected
        have hbelow :
            ∀ v, v ∈ PartialTy.vars writeSlot.ty → φ v < φ (LVal.base lv) :=
          hφ (LVal.base lv) writeSlot hwriteSlotBase
        have hrootProt :
            ProtectedByBase store xRoot (.heap address) :=
          Or.inr (StoreOwnerSpine.ownsTransitively_of_nonempty hspine
            hspineNonempty)
        rcases RuntimeSpinePathSelected.updateAtPath_map
            (store := store) (env := env)
            (selectedSource :=
              env.update xRoot
                { envSlot with
                    ty := PartialTy.strongLeafUpdate envSlot.ty spinePath
                      rhsTy })
            (φ := φ) (rootRank := φ (LVal.base lv))
            hbelow hselectedBase hupdatePath
            (fun {branchRank target targetTy branchLifetime branchResult}
                _hbranchRank htargetRank htargetTyping htargetLoc
                hbranchWrite =>
              goLVal hφ hsafe hvalidStore hheap hrootSlot hspine
                hspineNonempty htargetTyping htargetLoc hbranchWrite)
            (fun {branchRank target branchPt branchLifetime branchPath
                branchResult}
                _hbranchRank htargetRank htargetTyping htargetSelected
                hbranchWrite =>
              goPath hφ hsafe hvalidStore hheap hrootSlot hspine
                hspineNonempty htargetTyping htargetSelected hbranchWrite)
          with ⟨hmap, hstrength, hshape⟩
        have hselectedRankLt :
            φ xRoot < φ (LVal.base lv) :=
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping hφ hsafe
            hvalidStore hheap hselected hrootProt htyping
        have hrootNeBase : xRoot ≠ LVal.base lv := by
          intro hEq
          rw [hEq] at hselectedRankLt
          exact Nat.lt_irrefl _ hselectedRankLt
        have hbaseNeRoot : LVal.base lv ≠ xRoot := by
          intro hEq
          exact hrootNeBase hEq.symm
        have hslotStrong :
            (env.update xRoot
              { envSlot with
                  ty := PartialTy.strongLeafUpdate envSlot.ty spinePath
                    rhsTy }).slotAt
              (LVal.base (prependPath path lv)) = some writeSlot := by
          simpa [base_prependPath, Env.update, hbaseNeRoot] using
            hwriteSlotBase
        have hfinal :
            EnvSameShapeStrengthening
              (env.update xRoot
                { envSlot with
                    ty := PartialTy.strongLeafUpdate envSlot.ty spinePath
                      rhsTy })
              (writeEnv.update (LVal.base (prependPath path lv))
                { writeSlot with ty := updatedTy }) :=
          EnvSameShapeStrengthening.update_result_strengthening
            hmap hslotStrong rfl hstrength hshape
        simpa [base_prependPath] using hfinal
  termination_by (φ (LVal.base lv), sizeOf lv, 0)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      exact Prod.Lex.left _ _ (by assumption)

theorem EnvWrite.runtime_selected_spine_map {store : ProgramStore}
    {env result : Env} {current lifetime : Lifetime} {lv : LVal}
    {lvTy rhsTy : Ty} {address : Nat} {xRoot : Name} {envSlot : EnvSlot}
    {rootSlot leafSlot : StoreSlot} {spinePath : List Unit} {leafTy : Ty}
    {rank : Nat} {φ : Name → Nat} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env.slotAt xRoot = some envSlot →
    StoreOwnerSpine store (VariableProjection xRoot) rootSlot envSlot.ty
      spinePath (.heap address) leafSlot (.ty leafTy) →
    spinePath ≠ [] →
    LValTyping env lv (.ty lvTy) lifetime →
    store.loc lv = some (.heap address) →
    EnvWrite rank env lv rhsTy result →
    EnvSameShapeStrengthening
      (env.update xRoot
        { envSlot with
            ty := PartialTy.strongLeafUpdate envSlot.ty spinePath rhsTy })
      result := by
  intro hφ _hwellFormed hsafe hvalidStore hheap hrootSlot hspine
    hspineNonempty htyping hloc hwrite
  exact EnvWrite.runtime_selected_spine_map_of_safe hφ hsafe hvalidStore hheap
    hrootSlot hspine hspineNonempty htyping hloc hwrite

/--
GRAPH LEMMA A — safe abstraction survives a write through `*source`.

This is the genuine remaining content of Appendix 9.6 stated *as a property of
the abstraction graph* `∼ₛ` rather than as the preservation theorem: writing
`value` into the deref-resolved location and dropping the old contents preserves
safe abstraction against the retyped environment `env'`.

The store is a single-owner ownership forest (`ValidStore`: each location has at
most one owning slot) overlaid with *content-insensitive* borrow back-edges (a
borrow's validity reads its target's lval-resolution path, not the stored leaf
value).  So the write is frame-local around the concretely selected root: for an
owned-box path this is `source`'s base, while for a mutable-borrow path it is the
runtime-selected target branch.  The proof has to rebuild safe abstraction for
that selected root, transport it across the fan-out join, and then show the
post-write drop avoids every surviving root and borrow-resolution dependency.
-/
theorem safeAbstraction_assign_deref_drop_of_runtimeDropFrame
    {store writtenStore store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {lhsLocation : Location} {oldSlot : StoreSlot} {oldTy oldSlotTy : PartialTy}
    {value : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env (.deref source) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    ValidValue store value rhsTy →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    (writtenStore ∼ₛ env' →
      ValidStore writtenStore →
      StoreOwnerTargetsHeap writtenStore →
      (∀ dropValue, dropValue ∈ [oldSlot.value] →
        PartialValueOwnerTargetsHeap dropValue) →
      Drops writtenStore [oldSlot.value] store' →
      RuntimeDropFrame writtenStore env' [oldSlot.value]) →
    store.read (.deref source) = some oldSlot →
    store.loc (.deref source) = some lhsLocation →
    store.slotAt lhsLocation = some oldSlot →
    ValidPartialValue store oldSlot.value oldSlotTy →
    store.write (.deref source) (.value value) = some writtenStore →
    Drops writtenStore [oldSlot.value] store' →
    store' ∼ₛ env' := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite hderiveDropFrame hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops
  have hsafeWrite : writtenStore ∼ₛ env' := by
    have hwriteEq :
        writtenStore =
          store.update lhsLocation { oldSlot with value := .value value } := by
      unfold ProgramStore.write at hwriteStore
      simp [hlhsLoc, hlhsSlot] at hwriteStore
      exact hwriteStore.symm
    cases hLhs with
    | box hsourceBox =>
        rcases StoreOwnerSpine.of_lvalTyping_box hwellFormed hsafe hsourceBox with
          ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase, hrootSlot,
            hrootLifetime, hsourceLoc, hsourceSlot, hsourceSpine⟩
        have hsourceValid :
            ValidPartialValue store sourceSlot.value (.box oldTy) :=
          StoreOwnerSpine.leaf_valid hsourceSpine
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
            have hderefLoc :
                store.loc (.deref source) = some ownerLocation := by
              simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            have hownerLocationEq : ownerLocation = lhsLocation := by
              rw [hlhsLoc] at hderefLoc
              exact (Option.some.inj hderefLoc).symm
            subst ownerLocation
            have hownerSlotEq : ownerSlot = oldSlot := by
              rw [hlhsSlot] at hownedSlot
              exact (Option.some.inj hownedSlot).symm
            subst ownerSlot
            have hspine :
                StoreOwnerSpine store
                  (VariableProjection (LVal.base (.deref source))) rootSlot
                  envSlot.ty (LVal.path (.deref source)) lhsLocation oldSlot
                  oldTy := by
              have hsnoc :
                  StoreOwnerSpine store
                    (VariableProjection (LVal.base source)) rootSlot envSlot.ty
                    (() :: LVal.path source) lhsLocation oldSlot oldTy :=
                StoreOwnerSpine.snoc_box hsourceSpine rfl rfl hownedSlot
                  hinnerValid
              simpa [LVal.base, LVal.path_deref_cons] using hsnoc
            cases hwrite with
            | @intro _rank _env₁ writeEnv _writeLv writeSlot _writeTy updatedTy
                hwriteSlot hupdate =>
                have hwriteSlotEq : writeSlot = envSlot := by
                  simp [LVal.base] at hwriteSlot
                  have hsome : some writeSlot = some envSlot := by
                    rw [← hwriteSlot, henvBase]
                  exact Option.some.inj hsome
                subst writeSlot
                have hupdatePath :
                    UpdateAtPath 0 env (LVal.path (.deref source)) envSlot.ty
                      rhsTy writeEnv updatedTy := by
                  simpa [LVal.base] using hupdate
                have hwriteEnvEq : writeEnv = env :=
                  StoreOwnerSpine.updateAtPath_rank_zero_env_eq hspine hupdatePath
                subst writeEnv
                have hpathNonempty : LVal.path (.deref source) ≠ [] := by
                  simp [LVal.path_deref_cons]
                have hresultRoot :
                    (env.update (LVal.base source)
                      { envSlot with ty := updatedTy }).slotAt
                        (LVal.base source) =
                    some { envSlot with ty := updatedTy } := by
                  simp [Env.update]
                have hnotWriteObserver :
                    ¬ WriteProhibited
                      (env.update (LVal.base source)
                        { envSlot with ty := updatedTy })
                      (.var (LVal.base source)) := by
                  simpa [LVal.base] using
                    (not_writeProhibited_var_base hnotWrite)
                have hnotWriteSource :
                    ¬ WriteProhibited env (.var (LVal.base source)) :=
                  not_writeProhibited_var_of_update_self hwellFormed.2.2.2
                    hnotWriteObserver
                have hrhsVarsUpdated :
                    ∀ z, z ∈ PartialTy.vars (.ty rhsTy) →
                      z ∈ PartialTy.vars updatedTy :=
                  StoreOwnerSpine.updateAtPath_rank_zero_rhs_vars_subset_updated
                    hspine hupdatePath
                have hvarsObserver :
                    ∀ z, z ∈ PartialTy.vars (.ty rhsTy) →
                      WriteProhibited
                        (env.update (LVal.base source)
                          { envSlot with ty := updatedTy })
                        (.var z) := by
                  intro z hz
                  exact writeProhibited_of_envSlot_var_in_type hresultRoot rfl
                    (hrhsVarsUpdated z hz)
                have hvalidRuntimeValue :
                    ValidRuntimeState store (.val value) :=
                  validRuntimeState_assign_inner hvalidRuntime
                have hvalueNoReachLeaf :
                    ∀ location,
                      RuntimeFrame.Reaches store (.value value) (.ty rhsTy)
                        location →
                      location ≠ lhsLocation :=
                  term_value_reaches_ne_owner_spine_leaf_of_noWrite
                    hwellFormed hsafe hvalidRuntimeValue hwellTy hvalidValue
                    hspine hvarsObserver hnotWriteSource hnotWriteObserver
                have hnewValid :
                    ValidPartialValue writtenStore (.value value) (.ty rhsTy) := by
                  rw [hwriteEq]
                  exact RuntimeFrame.validPartialValue_update_of_not_reaches
                    hvalidValue hvalueNoReachLeaf
                have hotherNoReachLeaf :
                    ∀ y otherEnvSlot oldValue,
                      y ≠ LVal.base source →
                      env.slotAt y = some otherEnvSlot →
                      store.slotAt (VariableProjection y) =
                        some (StoreSlot.mk oldValue otherEnvSlot.lifetime) →
                      ∀ location,
                        RuntimeFrame.Reaches store oldValue otherEnvSlot.ty
                          location →
                        location ≠ lhsLocation := by
                  intro y otherEnvSlot oldValue hyx henvY hslotY
                  have henvYPost :
                      (env.update (LVal.base source)
                        { envSlot with ty := updatedTy }).slotAt y =
                      some otherEnvSlot := by
                    simpa [Env.update, hyx] using henvY
                  have hvarsOther :
                      ∀ z, z ∈ PartialTy.vars otherEnvSlot.ty →
                        WriteProhibited
                          (env.update (LVal.base source)
                            { envSlot with ty := updatedTy })
                          (.var z) := by
                    intro z hz
                    exact writeProhibited_of_envSlot_var_in_type henvYPost rfl hz
                  rcases hsafe.2 y otherEnvSlot henvY with
                    ⟨safeValue, hsafeSlot, hvalidOld⟩
                  have hsafeValueEq : safeValue = oldValue := by
                    have hslotEq :
                        StoreSlot.mk safeValue otherEnvSlot.lifetime =
                        StoreSlot.mk oldValue otherEnvSlot.lifetime :=
                      Option.some.inj (hsafeSlot.symm.trans hslotY)
                    exact congrArg StoreSlot.value hslotEq
                  subst safeValue
                  exact
                    stored_var_reaches_ne_owner_spine_leaf_of_noWrite
                      hwellFormed hsafe
                      (ValidRuntimeState.validStore hvalidRuntime)
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                      hspine hyx henvY hslotY hvalidOld hvarsOther
                      hnotWriteSource hnotWriteObserver
                simpa [LVal.base] using
                  safeAbstraction_update_owner_spine_of_frames
                    hwellFormed hsafe
                    (ValidRuntimeState.validStore hvalidRuntime)
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    henvBase hrootSlot hrootLifetime hspine hpathNonempty
                    hupdatePath hwriteEq hnewValid hotherNoReachLeaf
    | borrow hsourceBorrow htargets =>
        have hsourceAbs :=
          lvalTyping_defined_location hwellFormed hsafe hsourceBorrow
        have htargetsAbs :
            ∀ target ty lifetime,
              LValTyping env target (.ty ty) lifetime →
              LValLocationAbstraction store target (.ty ty) := by
          intro target ty lifetime htarget
          exact lvalTyping_defined_location hwellFormed hsafe htarget
        rcases location_borrow_selected_target hsourceAbs htargets htargetsAbs with
          ⟨selectedTarget, selectedTy, selectedLifetime, hselectedMem,
            hselectedTyping, hlhsAbs, hselectedStrengthens⟩
        rcases hlhsAbs with
          ⟨selectedLocation, selectedSlot, hselectedLoc, hselectedSlot,
            hselectedValid⟩
        have hselectedLocationEq : selectedLocation = lhsLocation := by
          rw [hlhsLoc] at hselectedLoc
          exact (Option.some.inj hselectedLoc).symm
        subst selectedLocation
        have hselectedSlotEq : selectedSlot = oldSlot := by
          rw [hlhsSlot] at hselectedSlot
          exact (Option.some.inj hselectedSlot).symm
        have holdSelectedValid :
            ValidPartialValue store oldSlot.value (.ty selectedTy) := by
          simpa [hselectedSlotEq] using hselectedValid
        -- Remaining content: prove the selected branch write safe, using the
        -- mutable-borrow authority as the frame exemption and borrow safety for
        -- every other root, then transport through the `WriteBorrowTargets`
        -- fan-out join.
        rw [hwriteEq]
        refine safeAbstraction_of_domain_and_slots ?domain ?slots
        · intro x
          have hstoreDomain :
              (∃ slot,
                  (store.update lhsLocation
                    { oldSlot with value := PartialValue.value value }).slotAt
                    (VariableProjection x) = some slot) ↔
                ∃ slot, store.slotAt (VariableProjection x) = some slot := by
            constructor
            · intro hdomain
              rcases hdomain with ⟨slot, hslot⟩
              by_cases hlocX : VariableProjection x = lhsLocation
              · subst hlocX
                exact ⟨oldSlot, hlhsSlot⟩
              · exact ⟨slot, by
                  simpa [ProgramStore.update, hlocX] using hslot⟩
            · intro hdomain
              rcases hdomain with ⟨slot, hslot⟩
              by_cases hlocX : VariableProjection x = lhsLocation
              · subst hlocX
                exact ⟨{ oldSlot with value := PartialValue.value value }, by
                  simp [ProgramStore.update]⟩
              · exact ⟨slot, by
                  simpa [ProgramStore.update, hlocX] using hslot⟩
          constructor
          · intro hdomain
            rcases (hstoreDomain.mp hdomain) with ⟨slot, hslot⟩
            rcases (hsafe.1 x).mp ⟨slot, hslot⟩ with ⟨envSlot, henvSlot⟩
            rcases EnvWrite.lifetimesSurvive hwrite x envSlot henvSlot with
              ⟨resultSlot, hresultSlot, _hlifetime⟩
            exact ⟨resultSlot, hresultSlot⟩
          · intro hdomain
            rcases hdomain with ⟨resultSlot, hresultSlot⟩
            rcases EnvWrite.lifetimesPreserved hwrite x resultSlot hresultSlot with
              ⟨sourceSlot, hsourceSlot, _hlifetime⟩
            rcases (hsafe.1 x).mpr ⟨sourceSlot, hsourceSlot⟩ with
              ⟨storeSlot, hstoreSlot⟩
            exact hstoreDomain.mpr ⟨storeSlot, hstoreSlot⟩
        · intro x resultSlot hresultSlot
          rcases EnvWrite.lifetimesPreserved hwrite x resultSlot hresultSlot with
            ⟨sourceSlot, hsourceSlot, hlifetime⟩
          rcases hsafe.2 x sourceSlot hsourceSlot with
            ⟨oldValue, hstoreSlot, hvalidOld⟩
          by_cases hxUpdated : VariableProjection x = lhsLocation
          · have hsourceSlotLifetime : sourceSlot.lifetime = oldSlot.lifetime := by
              have hstoreAtUpdated :
                  store.slotAt lhsLocation =
                    some { value := oldValue, lifetime := sourceSlot.lifetime } := by
                simpa [hxUpdated] using hstoreSlot
              rw [hlhsSlot] at hstoreAtUpdated
              exact (congrArg StoreSlot.lifetime
                (Option.some.inj hstoreAtUpdated)).symm
            have hslotFinal :
                (store.update lhsLocation
                  { value := PartialValue.value value, lifetime := oldSlot.lifetime }).slotAt
                    (VariableProjection x) =
                  some { value := PartialValue.value value, lifetime := resultSlot.lifetime } := by
              have hlifetime' : resultSlot.lifetime = oldSlot.lifetime := by
                rw [← hlifetime, hsourceSlotLifetime]
              simp [ProgramStore.update, hxUpdated, hlifetime']
            refine ⟨PartialValue.value value, hslotFinal, ?_⟩
            have hselectedMap :
                EnvSameShapeStrengthening
                  (env.update x { sourceSlot with ty := .ty rhsTy }) env' := by
              rcases hwellFormed.2.2.2 with ⟨φ, hφ⟩
              have hlhsLocVar :
                  store.loc source.deref = some (VariableProjection x) := by
                simpa [hxUpdated] using hlhsLoc
              have hLhsBorrow :
                  LValTyping env source.deref (.ty _) targetLifetime :=
                LValTyping.borrow hsourceBorrow htargets
              rcases lval_loc_var_slot_full_of_lvalTyping hwellFormed hsafe
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                  hLhsBorrow hlhsLocVar hsourceSlot with
                ⟨sourceSlotTy, hsourceSlotTy⟩
              exact EnvWrite.runtime_selected_lval_map_of_safe hφ hsafe
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hLhsBorrow hlhsLocVar hsourceSlot hsourceSlotTy hwrite
            have hnewValid :
                ValidPartialValue
                  (store.update lhsLocation
                    { value := PartialValue.value value, lifetime := oldSlot.lifetime })
                  (.value value) (.ty rhsTy) := by
              rcases hranked with ⟨φ, hφ, hbelowRhs⟩
              have hφOut : LinearizedBy φ env' :=
                EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
                  hwrite hφ hbelowRhs
              rcases hselectedMap.1 x resultSlot hresultSlot with
                ⟨newSourceSlot, hnewSourceSlot, _hnewLifetime,
                  hnewStrength, hnewShape⟩
              have hnewSourceSlotEq :
                  newSourceSlot = { sourceSlot with ty := .ty rhsTy } := by
                simpa [Env.update] using hnewSourceSlot.symm
              subst hnewSourceSlotEq
              have hvalueHeap : ValueOwnerTargetsHeap value :=
                TermOwnerTargetsHeap.value
                  (termOwnerTargetsHeap_assign_inner
                    (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
              refine
                RuntimeFrame.validPartialValue_update_of_owner_and_selected_dependency_frame
                  hvalidValue ?owners ?dependencies
              · intro location howner hlocationEq
                have hne :
                    location ≠ VariableProjection x :=
                  RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hvalueHeap hwellTy howner
                exact hne (by simpa [hxUpdated] using hlocationEq)
              · intro dependency hdependency hdependencyEq
                have hdependencyVar :
                    dependency = VariableProjection x := by
                  simpa [hxUpdated] using hdependencyEq
                have hborrows :
                    PartialTyBorrowsWellFormedInSlot env rhsWellLifetime
                      (.ty rhsTy) :=
                  PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy
                rcases RuntimeFrame.borrowDependency_var_rank_le_var_of_safe
                    hφ hsafe
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hborrows
                    (RuntimeFrame.SelectedBorrowDependency.borrowDependency
                      hdependency)
                    hdependencyVar with
                  ⟨v, hvRhs, hxLeV⟩
                have hvResult : v ∈ PartialTy.vars resultSlot.ty := by
                  exact partialTy_vars_mono hnewStrength hnewShape v
                    (by simpa using hvRhs)
                have hvLtX : φ v < φ x :=
                  hφOut x resultSlot hresultSlot v hvResult
                exact (Nat.not_lt_of_ge hxLeV) hvLtX
            rcases hselectedMap.1 x resultSlot hresultSlot with
              ⟨updatedSourceSlot, hupdatedSourceSlot, _hlifeMap,
                hstrength, hsameShape⟩
            have hupdatedSourceSlotEq :
                updatedSourceSlot = { sourceSlot with ty := .ty rhsTy } := by
              simpa [Env.update] using hupdatedSourceSlot.symm
            subst hupdatedSourceSlotEq
            exact validPartialValue_strengthen_sameShape hnewValid
              hstrength hsameShape
          · have hslotFinal :
                (store.update lhsLocation
                  { value := PartialValue.value value, lifetime := oldSlot.lifetime }).slotAt
                    (VariableProjection x) =
                  some { value := oldValue, lifetime := resultSlot.lifetime } := by
              have hlifetime' : resultSlot.lifetime = sourceSlot.lifetime := by
                rw [← hlifetime]
              simpa [ProgramStore.update, hxUpdated, hlifetime'] using hstoreSlot
            refine ⟨oldValue, hslotFinal, ?_⟩
            have hglobalMap : EnvSameShapeStrengthening env env' := by
              cases hwrite with
              | @intro _rank _env₁ writeEnv _writeLv writeSlot _ty updatedTy
                  hwriteSlot hupdate =>
                  have hwriteSlotBase :
                      env.slotAt (LVal.base source) = some writeSlot := by
                    simpa [LVal.base] using hwriteSlot
                  have hthrough :
                      PathThroughBorrow writeSlot.ty
                        (LVal.path (.deref source)) := by
                    simpa [LVal.path] using
                      LValTyping.pathThroughBorrow_append hsourceBorrow
                        hwriteSlotBase [()] PathThroughBorrow.borrowHere
                  rcases UpdateAtPath.sameShapeStrengthening_of_throughBorrow
                      hthrough hupdate with ⟨hmap, hstrength, hshape⟩
                  have hfinal :=
                    EnvSameShapeStrengthening.update_result_strengthening
                      (resultSlot := { writeSlot with ty := updatedTy })
                      hmap hwriteSlotBase rfl hstrength hshape
                  simpa [LVal.base] using hfinal
            rcases hglobalMap.1 x resultSlot hresultSlot with
              ⟨mappedSourceSlot, hmappedSourceSlot, _hlifeMap,
                hstrength, hsameShape⟩
            have hmappedSourceSlotEq : sourceSlot = mappedSourceSlot :=
              Option.some.inj (hsourceSlot.symm.trans hmappedSourceSlot)
            subst hmappedSourceSlotEq
            have hvalidStore := ValidRuntimeState.validStore hvalidRuntime
            have hheap :=
              ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
            rcases hranked with ⟨φ, hφ, hbelowRhs⟩
            by_cases howner :
                RuntimeFrame.OwnerReaches store oldValue sourceSlot.ty
                  lhsLocation
            · -- `x` owns the written cell: it is the unique owner-spine root,
              -- and validity is rebuilt along the strongly updated spine.
              have hownsTrans :
                  ProgramStore.OwnsTransitively store (VariableProjection x)
                    lhsLocation :=
                RuntimeFrame.ownsTransitively_of_ownerReaches_stored
                  hstoreSlot howner
              have hprotX : ProtectedByBase store x lhsLocation :=
                Or.inr hownsTrans
              rcases hheap lhsLocation
                  (ProgramStore.OwnsTransitively.to_owns hownsTrans) with
                ⟨address, haddrEq⟩
              have hLhsTyping :
                  LValTyping env (.deref source) (.ty _) targetLifetime :=
                LValTyping.borrow hsourceBorrow htargets
              have hlocHeap :
                  store.loc (.deref source) = some (.heap address) := by
                rw [← haddrEq]
                exact hlhsLoc
              rcases heapLeaf_spine_of_loc_of_safe hφ hsafe hLhsTyping
                  hlocHeap with
                ⟨xRoot, envSlotXr, rootSlotXr, spinePath, leafSlotXr, leafTyXr,
                  henvXr, hrootSlotXr, _hrootLtXr, hspine, hspineNonempty⟩
              have hprotXr : ProtectedByBase store xRoot lhsLocation := by
                rw [haddrEq]
                exact Or.inr
                  (StoreOwnerSpine.ownsTransitively_of_nonempty hspine
                    hspineNonempty)
              have hxEq : xRoot = x :=
                (ProtectedByBase.root_unique hvalidStore hheap hprotX
                  hprotXr).symm
              subst hxEq
              have henvSlotEq : sourceSlot = envSlotXr :=
                Option.some.inj (hsourceSlot.symm.trans henvXr)
              subst henvSlotEq
              have hrootSlotEq :
                  rootSlotXr =
                    StoreSlot.mk oldValue sourceSlot.lifetime :=
                Option.some.inj (hrootSlotXr.symm.trans hstoreSlot)
              subst hrootSlotEq
              have hmapSpine :=
                EnvWrite.runtime_selected_spine_map_of_safe hφ hsafe
                  hvalidStore hheap hsourceSlot hspine hspineNonempty
                  hLhsTyping hlocHeap hwrite
              -- validity of the written value in the updated store
              have hvalidRuntimeValue :
                  ValidRuntimeState store (.val value) :=
                validRuntimeState_assign_inner hvalidRuntime
              have hborrowsRhs :
                  PartialTyBorrowsWellFormedInSlot env rhsWellLifetime
                    (.ty rhsTy) :=
                PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy
              have hvalueHeapRhs :
                  PartialValueOwnerTargetsHeap (.value value) :=
                ValueOwnerTargetsHeap.partial
                  (TermOwnerTargetsHeap.value
                    (ValidRuntimeState.termOwnerTargetsHeap
                      hvalidRuntimeValue))
              have hrootNoOwnerReach :
                  ∀ reached,
                    RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy)
                      reached →
                    reached ≠ VariableProjection xRoot := by
                intro reached hownerReach
                exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows hheap
                  hvalueHeapRhs hborrowsRhs hownerReach
              have hvalueOwnerFrame :
                  ∀ reached,
                    RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy)
                      reached →
                    reached ≠ lhsLocation := by
                rw [haddrEq]
                exact StoreOwnerSpine.not_reaches_leaf_of_not_reaches_root
                  hvalidRuntimeValue hborrowsRhs hvalidValue hspine
                  hrootNoOwnerReach
              have hvalueDepFrame :
                  ∀ location,
                    RuntimeFrame.BorrowDependency store (.value value)
                      (.ty rhsTy) location →
                    location ≠ lhsLocation := by
                intro location hdep heq
                subst heq
                rcases RuntimeFrame.borrowDependency_witness hdep with
                  ⟨m, ts, pointee, t, hcontains, hmem, hreads⟩
                rcases hborrowsRhs hcontains t hmem with
                  ⟨tTy, tLt, htTyping, _houtlives, _hbase⟩
                rcases RuntimeFrame.locReads_resolved_prefix htTyping
                    hreads with
                  ⟨w, ptW, ltW, hwTyping, hbaseW, hwLoc⟩
                rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe
                    hwTyping hwLoc with
                  ⟨rootW, _, _, _, hprotW, hrankW, _, _, _, _, _, _⟩
                have hrootWEq : rootW = xRoot :=
                  ProtectedByBase.root_unique hvalidStore hheap hprotW hprotX
                rw [hrootWEq, hbaseW] at hrankW
                rcases hmapSpine.2 xRoot
                    { sourceSlot with
                        ty := PartialTy.strongLeafUpdate sourceSlot.ty
                          spinePath rhsTy }
                    (by simp [Env.update]) with
                  ⟨resultSlotXr, hresultXr, _hlifeXr⟩
                rcases hmapSpine.1 xRoot resultSlotXr hresultXr with
                  ⟨strongSlot', hstrongSlot', _hlifeStrong', hstrengthensXr,
                    hshapeXr⟩
                have hstrongEq :
                    strongSlot' =
                      { sourceSlot with
                          ty := PartialTy.strongLeafUpdate sourceSlot.ty
                            spinePath rhsTy } := by
                  simpa [Env.update] using hstrongSlot'.symm
                subst hstrongEq
                have hcontainsStrong :
                    PartialTyContains
                      (PartialTy.strongLeafUpdate sourceSlot.ty spinePath
                        rhsTy)
                      (.borrow m ts pointee) :=
                  StoreOwnerSpine.strongLeafUpdate_contains hspine hcontains
                rcases PartialTyContains.mono_strengthens_sameShape
                    hcontainsStrong hstrengthensXr hshapeXr with
                  ⟨ts', pointee', hcontains', hsubset, _hpointee⟩
                have hstrict : φ (LVal.base t) < φ xRoot :=
                  hbelowRhs.1 xRoot resultSlotXr m ts' pointee' t hresultXr hcontains'
                    (hsubset hmem) ⟨m, ts, pointee, hcontains, hmem⟩
                exact Nat.lt_irrefl _ (lt_of_le_of_lt hrankW hstrict)
              have hnewValid :
                  ValidPartialValue
                    (store.update lhsLocation
                      { value := PartialValue.value value,
                        lifetime := oldSlot.lifetime })
                    (.value value) (.ty rhsTy) :=
                RuntimeFrame.validPartialValue_update_of_owner_and_borrow_dependency_frame
                  hvalidValue hvalueOwnerFrame hvalueDepFrame
              have hrootValid :
                  ValidPartialValue
                    (store.update lhsLocation
                      { value := PartialValue.value value,
                        lifetime := oldSlot.lifetime })
                    oldValue
                    (PartialTy.strongLeafUpdate sourceSlot.ty spinePath
                      rhsTy) := by
                have hres :=
                  StoreOwnerSpine.valid_after_leaf_strong_update
                    (newSlot :=
                      { value := PartialValue.value value,
                        lifetime := oldSlot.lifetime })
                    hspine hspineNonempty rfl
                    (by
                      rw [← haddrEq]
                      exact hnewValid)
                rw [haddrEq]
                exact hres
              rcases hmapSpine.1 xRoot resultSlot hresultSlot with
                ⟨mappedStrong, hmappedStrong, _hlifeStrong, hstrengthStrong,
                  hshapeStrong⟩
              have hmappedStrongEq :
                  mappedStrong =
                    { sourceSlot with
                        ty := PartialTy.strongLeafUpdate sourceSlot.ty
                          spinePath rhsTy } := by
                simpa [Env.update] using hmappedStrong.symm
              subst hmappedStrongEq
              exact validPartialValue_strengthen_sameShape hrootValid
                hstrengthStrong hshapeStrong
            · -- `x` does not own the written cell: both frames hold and the
              -- old validity transports through the global map.
              have hdepFrame :
                  ∀ location,
                    RuntimeFrame.BorrowDependency store oldValue sourceSlot.ty
                      location →
                    location ≠ lhsLocation := by
                intro location hdep heq
                rw [heq] at hdep
                have hnotWPbase :
                    ¬ WriteProhibited env (.var (LVal.base source)) := by
                  intro hWP
                  exact hnotWrite
                    (writeProhibited_var_transport hglobalMap rfl hWP)
                have hkill₀ :
                    SlotDepKill store env lhsLocation (LVal.base source) :=
                  slotDepKill_of_firstNode hφ hwellFormed hsafe hvalidStore
                    hheap hsourceBorrow
                    (LValTyping.borrow hsourceBorrow htargets) hlhsLoc
                    hlhsSlot holdSelectedValid
                rcases LValTargetsTyping.output_full htargets with
                  ⟨lhsTy₂, hOldTyFull₂⟩
                have hLhsTyping :
                    LValTyping env (.deref source) (.ty lhsTy₂)
                      targetLifetime := by
                  rw [← hOldTyFull₂]
                  exact LValTyping.borrow hsourceBorrow htargets
                rcases writeGuarded_of_resolution hφ hwellFormed hsafe
                    hvalidStore hheap hlhsSlot holdSelectedValid hLhsTyping
                    hlhsLoc hwrite (WriteGuarded.base hkill₀) with
                  ⟨r, hprotR, hGr⟩
                rcases RuntimeFrame.borrowDependency_witness hdep with
                  ⟨m, ts, pointee, t, hcontains, hmem, hreads⟩
                have hborrowsX :
                    PartialTyBorrowsWellFormedInSlot env sourceSlot.lifetime
                      sourceSlot.ty := by
                  intro mutable' targets' pointee' hcontains'
                  exact hwellFormed.1 x sourceSlot mutable' targets' pointee'
                    hsourceSlot ⟨sourceSlot, hsourceSlot, hcontains'⟩
                rcases hborrowsX hcontains t hmem with
                  ⟨tTy, tLt, htTyping, _houtlives, _hbase⟩
                have hcollapse :
                    ∀ container mutable' ts' pointee' t',
                      env ⊢ container ↝ (.borrow mutable' ts' pointee') → t' ∈ ts' →
                      WriteGuarded store env lhsLocation (LVal.base source)
                        (LVal.base t') →
                      WriteGuarded store env lhsLocation (LVal.base source)
                        container :=
                  fun c m' ts' pointee' t' hn hm hG =>
                    (WriteGuarded.collapse_kill hborrowSafe hnotWPbase hn hm
                      hG).1
                have hGt :
                    WriteGuarded store env lhsLocation (LVal.base source)
                      (LVal.base t) :=
                  RuntimeFrame.locReads_protected_guarded_base hφ hwellFormed
                    hsafe hvalidStore hheap hcollapse htTyping hreads hprotR
                    hGr
                have hkillX :=
                  (WriteGuarded.collapse_kill hborrowSafe hnotWPbase
                    ⟨sourceSlot, hsourceSlot, hcontains⟩ hmem hGt).2
                exact hkillX sourceSlot oldValue hsourceSlot hstoreSlot hdep
              have holdValid :
                  ValidPartialValue
                    (store.update lhsLocation
                      { value := PartialValue.value value,
                        lifetime := oldSlot.lifetime })
                    oldValue sourceSlot.ty :=
                RuntimeFrame.validPartialValue_update_of_owner_and_borrow_dependency_frame
                  hvalidOld
                  (fun location h heq => howner (heq ▸ h)) hdepFrame
              exact validPartialValue_strengthen_sameShape holdValid
                hstrength hsameShape
  have hvalueHeap : ValueOwnerTargetsHeap value :=
    TermOwnerTargetsHeap.value
      (termOwnerTargetsHeap_assign_inner
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
  have hwrittenHeap : StoreOwnerTargetsHeap writtenStore :=
    storeOwnerTargetsHeap_write
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
      (ValueOwnerTargetsHeap.partial hvalueHeap) hwriteStore
  have hnewDisjoint :
      ∀ owned, owned ∈ partialValueOwningLocations (.value value) →
        ¬ ProgramStore.Owns store owned := by
    intro owned hmem
    exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned (by
      simpa [termOwningLocations, termValues, partialValueOwningLocations] using hmem)
  have hwrittenValidStore : ValidStore writtenStore :=
    validStore_write_disjoint (ValidRuntimeState.validStore hvalidRuntime)
      hnewDisjoint hwriteStore
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [oldSlot.value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact partialValueOwnerTargetsHeap_of_slot
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hlhsSlot
  have hdropOwnersOrphaned :
      ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
        ¬ ProgramStore.Owns writtenStore owned :=
    droppedValueOwnersOrphaned_assign_deref hwellFormed hsafe hvalidRuntime
      hlhsLoc hlhsSlot holdSlotValid hwriteStore
  have hdropFrame :
      RuntimeDropFrame writtenStore env' [oldSlot.value] :=
    hderiveDropFrame hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap hdrops
  exact safeAbstraction_drops_of_runtimeDropFrame
    hsafeWrite hwrittenHeap hdropValuesHeap hdropFrame hdrops

theorem safeAbstraction_assign_deref_drop_of_representedSlotsProtected
    {store writtenStore store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {lhsLocation : Location} {oldSlot : StoreSlot} {oldTy oldSlotTy : PartialTy}
    {value : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env (.deref source) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    ValidValue store value rhsTy →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    RuntimeRepresentedSlotsProtected writtenStore env' →
    store.read (.deref source) = some oldSlot →
    store.loc (.deref source) = some lhsLocation →
    store.slotAt lhsLocation = some oldSlot →
    ValidPartialValue store oldSlot.value oldSlotTy →
    store.write (.deref source) (.value value) = some writtenStore →
    Drops writtenStore [oldSlot.value] store' →
    store' ∼ₛ env' := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite hprotected hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops
  exact safeAbstraction_assign_deref_drop_of_runtimeDropFrame
    hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite
    (fun _hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap hdrops =>
      RuntimeDropFrame.of_orphaned_values hprotected
        hwrittenValidStore hwrittenHeap hdropValuesHeap
        (droppedValueOwnersOrphaned_assign_deref hwellFormed hsafe hvalidRuntime
          hlhsLoc hlhsSlot holdSlotValid hwriteStore)
        hdrops)
    hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops

theorem safeAbstraction_assign_deref_drop_of_wellFormed
    {store writtenStore store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {lhsLocation : Location} {oldSlot : StoreSlot} {oldTy oldSlotTy : PartialTy}
    {value : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env (.deref source) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    ValidValue store value rhsTy →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    WellFormedEnv env' lifetime →
    store.read (.deref source) = some oldSlot →
    store.loc (.deref source) = some lhsLocation →
    store.slotAt lhsLocation = some oldSlot →
    ValidPartialValue store oldSlot.value oldSlotTy →
    store.write (.deref source) (.value value) = some writtenStore →
    Drops writtenStore [oldSlot.value] store' →
    store' ∼ₛ env' := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite hwellOut hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops
  exact safeAbstraction_assign_deref_drop_of_runtimeDropFrame
    hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite
    (fun hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap hdrops =>
      RuntimeDropFrame.of_orphaned_values
        (RuntimeRepresentedSlotsProtected.of_containedBorrowsWellFormed
          hwellOut.1 hsafeWrite hwrittenValidStore hwrittenHeap)
        hwrittenValidStore hwrittenHeap hdropValuesHeap
        (droppedValueOwnersOrphaned_assign_deref hwellFormed hsafe hvalidRuntime
          hlhsLoc hlhsSlot holdSlotValid hwriteStore)
        hdrops)
    hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops

/--
Selected evidence dependencies of an existing represented slot cannot sit inside
the subtree overwritten by a write through a borrow.  The proof follows the
runtime borrow-resolution chain back to the write authority and uses the
subtree-aware dependency kill established from the first crossed borrow node.
-/
theorem evidenceDependency_not_below_assign_deref_borrow
    {store : ProgramStore} {env env' : Env}
    {current borrowLifetime targetLifetime derefLifetime : Lifetime}
    {φ : Name → Nat} {source : LVal} {mutable : Bool}
    {targets : List LVal} {pointee : Ty}
    {derefTy : Ty} {leafView : PartialTy} {rhsTy : Ty}
    {leaf : Location} {leafSlot : StoreSlot} {x : Name}
    {sourceSlot : EnvSlot} {oldValue : PartialValue}
    {evidence : RuntimeFrame.ValidPartialValueEvidence store oldValue
      sourceSlot.ty}
    {dependency : Location} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env source (.ty (.borrow mutable targets pointee))
      borrowLifetime →
    LValTargetsTyping env targets (.ty pointee) targetLifetime →
    LValTyping env (.deref source) (.ty derefTy) derefLifetime →
    store.loc (.deref source) = some leaf →
    store.slotAt leaf = some leafSlot →
    ValidPartialValue store leafSlot.value leafView →
    EnvWrite 0 env (.deref source) rhsTy env' →
    ¬ WriteProhibited env (.var (LVal.base source)) →
    env.slotAt x = some sourceSlot →
    store.slotAt (VariableProjection x) =
      some { value := oldValue, lifetime := sourceSlot.lifetime } →
    RuntimeFrame.EvidenceBorrowDependency store evidence dependency →
    ¬ (dependency = leaf ∨
      ProgramStore.OwnsTransitively store leaf dependency) := by
  intro hφ hwellFormed hborrowSafe hsafe hvalidStore hheap hsourceBorrow
    htargets hLhsTyping hloc hleafSlot hleafValid hwrite hnotWPbase hsourceSlot
    hstoreSlot hdependency hsubtree
  have hkill₀ :
      SlotDepTreeKill store env leaf (LVal.base source) :=
    slotDepTreeKill_of_firstNode hφ hwellFormed hsafe hvalidStore hheap
      hsourceBorrow (LValTyping.borrow hsourceBorrow htargets) hloc
      hleafSlot hleafValid
  rcases writeGuardedTree_of_resolution hφ hwellFormed hsafe hvalidStore
      hheap hleafSlot hleafValid hLhsTyping hloc hwrite
      (WriteGuardedTree.base hkill₀) with
    ⟨r, hprotR, hGr⟩
  have hborrowDep :
      RuntimeFrame.BorrowDependency store oldValue sourceSlot.ty dependency :=
    RuntimeFrame.SelectedBorrowDependency.borrowDependency
      (RuntimeFrame.EvidenceBorrowDependency.selected hdependency)
  rcases RuntimeFrame.borrowDependency_witness hborrowDep with
    ⟨m, ts, borrowPointee, t, hcontains, hmem, hreads⟩
  have hborrowsX :
      PartialTyBorrowsWellFormedInSlot env sourceSlot.lifetime
        sourceSlot.ty := by
    intro mutable' targets' pointee' hcontains'
    exact hwellFormed.1 x sourceSlot mutable' targets' pointee'
      hsourceSlot ⟨sourceSlot, hsourceSlot, hcontains'⟩
  rcases hborrowsX hcontains t hmem with
    ⟨tTy, tLt, htTyping, _houtlives, _hbase⟩
  have hcollapse :
      ∀ container mutable' ts' pointee' t',
        env ⊢ container ↝ (.borrow mutable' ts' pointee') →
        t' ∈ ts' →
        WriteGuardedTree store env leaf (LVal.base source)
          (LVal.base t') →
        WriteGuardedTree store env leaf (LVal.base source) container :=
    fun c m' ts' pointee' t' hn hm hG =>
      (WriteGuardedTree.collapse_kill hborrowSafe hnotWPbase hn hm hG).1
  have hGt :
      WriteGuardedTree store env leaf (LVal.base source) (LVal.base t) :=
    have hprotDependency : ProtectedByBase store r dependency :=
      Or.elim hsubtree
        (fun hdependencyEq => by
          subst hdependencyEq
          exact hprotR)
        (fun hbelow =>
          ProtectedByBase.trans_ownsTransitively hprotR hbelow)
    RuntimeFrame.locReads_protected_guarded_base hφ hwellFormed hsafe
      hvalidStore hheap hcollapse htTyping hreads hprotDependency hGr
  have hkillX :
      SlotDepTreeKill store env leaf x :=
    (WriteGuardedTree.collapse_kill hborrowSafe hnotWPbase
      ⟨sourceSlot, hsourceSlot, hcontains⟩ hmem hGt).2
  exact hkillX sourceSlot oldValue dependency hsourceSlot hstoreSlot
    hsubtree hborrowDep

/--
Borrow dependencies selected by the freshly written RHS cannot point to the
overwritten leaf or anywhere inside its old owner subtree.  The owner root of
the leaf is updated with a type containing the RHS type, and
`EnvWriteRhsBorrowTargetsBelow` forces every RHS borrow target root to rank
strictly below that owner root; resolving into the owner root's own subtree would
force the opposite inequality.
-/
theorem rhsBorrowDependency_not_in_assign_subtree
    {store : ProgramStore} {env env' : Env}
    {current rhsLifetime : Lifetime} {φ : Name → Nat}
    {root : Name} {rootEnvSlot : EnvSlot} {updatedTy : PartialTy}
    {leaf dependency : Location} {rhsTy : Ty} {value : Value} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    WellFormedTy env rhsTy rhsLifetime →
    EnvSameShapeStrengthening
      (env.update root { rootEnvSlot with ty := updatedTy }) env' →
    EnvWriteRhsBorrowTargetsBelow φ env' rhsTy →
    ProtectedByBase store root leaf →
    env.slotAt root = some rootEnvSlot →
    (∀ {mutable targets pointee},
      PartialTyContains (.ty rhsTy) (.borrow mutable targets pointee) →
      ∃ targets',
        PartialTyContains updatedTy (.borrow mutable targets' pointee) ∧
        ∀ target, target ∈ targets → target ∈ targets') →
    RuntimeFrame.BorrowDependency store (.value value) (.ty rhsTy)
      dependency →
    ¬ (dependency = leaf ∨ ProgramStore.OwnsTransitively store leaf dependency) := by
  intro hφ hwellFormed hsafe hvalidStore hheap hwellTy hmap hbelowRhs
    hrootProtected hrootEnv hcontainsUpdated hdependency hsubtree
  rcases RuntimeFrame.borrowDependency_witness hdependency with
    ⟨mutable, targets, pointee, target, hcontains, hmem, hreads⟩
  have hborrowsRhs :
      PartialTyBorrowsWellFormedInSlot env rhsLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy
  rcases hborrowsRhs hcontains target hmem with
    ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
  rcases RuntimeFrame.locReads_resolved_prefix htargetTyping hreads with
    ⟨readPrefix, prefixTy, prefixLifetime, hprefixTyping, hprefixBase,
      hprefixLoc⟩
  rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe
      hprefixTyping hprefixLoc with
    ⟨dependencyRoot, slotD, viewTyD, slotLifetimeD, hdependencyProtected,
      hrankDependency, _hslotD, _hvalidD, _hboundD, _hborrowsD,
      _hcontainsD, _hdescentD⟩
  have hrootProtectsDependency :
      ProtectedByBase store root dependency := by
    rcases hsubtree with hdependencyEq | hleafOwnsDependency
    · subst hdependencyEq
      exact hrootProtected
    · exact ProtectedByBase.trans_ownsTransitively hrootProtected
        hleafOwnsDependency
  have hdependencyRootEq : dependencyRoot = root :=
    ProtectedByBase.root_unique hvalidStore hheap hdependencyProtected
      hrootProtectsDependency
  rw [hdependencyRootEq, hprefixBase] at hrankDependency
  rcases hmap.2 root { rootEnvSlot with ty := updatedTy }
      (by simp [Env.update]) with
    ⟨resultSlot, hresultSlot, _hresultLifetime⟩
  rcases hmap.1 root resultSlot hresultSlot with
    ⟨mappedRootSlot, hmappedRootSlot, _hmappedLifetime, hstrength,
      hshape⟩
  have hmappedRootSlotEq :
      mappedRootSlot = { rootEnvSlot with ty := updatedTy } := by
    simpa [Env.update] using hmappedRootSlot.symm
  subst hmappedRootSlotEq
  rcases hcontainsUpdated hcontains with
    ⟨updatedTargets, hcontainsStrong, hsubsetUpdated⟩
  rcases PartialTyContains.mono_strengthens_sameShape
      hcontainsStrong hstrength hshape with
    ⟨resultTargets, resultPointee, hcontainsResult, hsubsetResult,
      _hpointeeResult⟩
  have hstrict : φ (LVal.base target) < φ root :=
    hbelowRhs.1 root resultSlot mutable resultTargets resultPointee target
      hresultSlot hcontainsResult (hsubsetResult (hsubsetUpdated target hmem))
      ⟨mutable, targets, pointee, hcontains, hmem⟩
  exact Nat.lt_irrefl _ (lt_of_le_of_lt hrankDependency hstrict)

/--
Evidence for the freshly written RHS survives the concrete update at the
overwritten leaf, and its selected borrow dependencies remain protected in the
updated store.
-/
theorem rhsEvidence_update_assign_deref_borrow
    {store : ProgramStore} {env env' : Env}
    {current rhsLifetime : Lifetime} {φ : Name → Nat}
    {root : Name} {rootEnvSlot : EnvSlot} {updatedTy : PartialTy}
    {leaf : Location} {newSlot : StoreSlot}
    {rhsTy : Ty} {value : Value} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    WellFormedTy env rhsTy rhsLifetime →
    ValidValue store value rhsTy →
    EnvSameShapeStrengthening
      (env.update root { rootEnvSlot with ty := updatedTy }) env' →
    EnvWriteRhsBorrowTargetsBelow φ env' rhsTy →
    ProtectedByBase store root leaf →
    env.slotAt root = some rootEnvSlot →
    (∀ {mutable targets pointee},
      PartialTyContains (.ty rhsTy) (.borrow mutable targets pointee) →
      ∃ targets',
        PartialTyContains updatedTy (.borrow mutable targets' pointee) ∧
        ∀ target, target ∈ targets → target ∈ targets') →
    (∀ location,
      RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) location →
      location ≠ leaf) →
    ∃ newEvidence :
      RuntimeFrame.ValidPartialValueEvidence (store.update leaf newSlot)
        (.value value) (.ty rhsTy),
      ∀ dependency,
        RuntimeFrame.EvidenceBorrowDependency (store.update leaf newSlot)
          newEvidence dependency →
        ∃ base,
          ProtectedByBase (store.update leaf newSlot) base dependency := by
  intro hφ hwellFormed hsafe hvalidStore hheap hwellTy hvalidValue hmap
    hbelowRhs hrootProtected hrootEnv hcontainsUpdated hownerFrame
  rcases RuntimeFrame.ValidPartialValueEvidence.exists_of_valid hvalidValue with
    ⟨oldEvidence, _⟩
  have hdependencyFrame :
      ∀ dependency,
        RuntimeFrame.EvidenceBorrowDependency store oldEvidence dependency →
        dependency ≠ leaf := by
    intro dependency hdependency hdependencyEq
    have hborrowDep :
        RuntimeFrame.BorrowDependency store (.value value) (.ty rhsTy)
          dependency :=
      RuntimeFrame.SelectedBorrowDependency.borrowDependency
        (RuntimeFrame.EvidenceBorrowDependency.selected hdependency)
    exact
      rhsBorrowDependency_not_in_assign_subtree hφ hwellFormed hsafe
        hvalidStore hheap hwellTy hmap hbelowRhs hrootProtected hrootEnv
        hcontainsUpdated hborrowDep (Or.inl hdependencyEq)
  rcases
      RuntimeFrame.validPartialValueEvidence_update_of_owner_and_evidence_dependency_frame
        (updated := leaf) (newSlot := newSlot) oldEvidence hownerFrame
        hdependencyFrame with
    ⟨newEvidence, hdependencyBack⟩
  refine ⟨newEvidence, ?_⟩
  intro dependency hdependency
  have hdependencyOld := hdependencyBack dependency hdependency
  have hborrowDep :
      RuntimeFrame.BorrowDependency store (.value value) (.ty rhsTy)
        dependency :=
    RuntimeFrame.SelectedBorrowDependency.borrowDependency
      (RuntimeFrame.EvidenceBorrowDependency.selected hdependencyOld)
  have hnotSubtree :
      ¬ (dependency = leaf ∨
        ProgramStore.OwnsTransitively store leaf dependency) :=
    rhsBorrowDependency_not_in_assign_subtree hφ hwellFormed hsafe hvalidStore
      hheap hwellTy hmap hbelowRhs hrootProtected hrootEnv
      hcontainsUpdated hborrowDep
  rcases borrowDependency_protectedBySomeBase_of_safe
      hsafe hvalidStore hheap
      (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)
      (RuntimeFrame.SelectedBorrowDependency.borrowDependency
        (RuntimeFrame.EvidenceBorrowDependency.selected hdependencyOld)) with
    ⟨base, hprotected⟩
  refine ⟨base, ProtectedByBase.update_of_not_ancestor hprotected ?_⟩
  intro howns
  exact hnotSubtree (Or.inr howns)

/-- Frame for an existing represented slot across a borrow-target leaf update. -/
theorem oldEvidenceFrame_assign_deref_borrow
    {store : ProgramStore} {env env' : Env}
    {current borrowLifetime targetLifetime derefLifetime : Lifetime}
    {φ : Name → Nat} {source : LVal} {mutable : Bool}
    {targets : List LVal} {pointee : Ty}
    {derefTy : Ty} {leafView : PartialTy} {rhsTy : Ty}
    {leaf : Location} {leafSlot : StoreSlot} {root y : Name}
    {envSlot : EnvSlot} {oldValue : PartialValue}
    {evidence : RuntimeFrame.ValidPartialValueEvidence store oldValue
      envSlot.ty} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env source (.ty (.borrow mutable targets pointee))
      borrowLifetime →
    LValTargetsTyping env targets (.ty pointee) targetLifetime →
    LValTyping env (.deref source) (.ty derefTy) derefLifetime →
    store.loc (.deref source) = some leaf →
    store.slotAt leaf = some leafSlot →
    ValidPartialValue store leafSlot.value leafView →
    EnvWrite 0 env (.deref source) rhsTy env' →
    ¬ WriteProhibited env (.var (LVal.base source)) →
    ProtectedByBase store root leaf →
    y ≠ root →
    env.slotAt y = some envSlot →
    store.slotAt (VariableProjection y) =
      some { value := oldValue, lifetime := envSlot.lifetime } →
    (∀ location,
      RuntimeFrame.OwnerReaches store oldValue envSlot.ty location →
      location ≠ leaf) ∧
    (∀ dependency,
      RuntimeFrame.EvidenceBorrowDependency store evidence dependency →
      dependency ≠ leaf) := by
  intro hφ hwellFormed hborrowSafe hsafe hvalidStore hheap hsourceBorrow
    htargets hLhsTyping hloc hleafSlot hleafValid hwrite hnotWPbase
    hrootProtected hyroot henvY hstoreY
  constructor
  · intro location howner hlocationEq
    have hownsTrans :
        ProgramStore.OwnsTransitively store (VariableProjection y) leaf :=
      by
        have hownsLocation :=
          RuntimeFrame.ownsTransitively_of_ownerReaches_stored hstoreY howner
        simpa [hlocationEq] using hownsLocation
    have hprotectedY : ProtectedByBase store y leaf :=
      Or.inr hownsTrans
    have hyEq : y = root :=
      ProtectedByBase.root_unique hvalidStore hheap hprotectedY hrootProtected
    exact hyroot hyEq
  · intro dependency hdependency hdependencyEq
    exact
      evidenceDependency_not_below_assign_deref_borrow hφ hwellFormed
        hborrowSafe hsafe hvalidStore hheap hsourceBorrow htargets hLhsTyping
        hloc hleafSlot hleafValid hwrite hnotWPbase henvY hstoreY
        hdependency (Or.inl hdependencyEq)

/-- Protected selected dependencies of an existing represented slot survive a
borrow-target leaf update. -/
theorem oldEvidenceProtected_update_assign_deref_borrow
    {store : ProgramStore} {env env' : Env}
    {current borrowLifetime targetLifetime derefLifetime : Lifetime}
    {φ : Name → Nat} {source : LVal} {mutable : Bool}
    {targets : List LVal} {pointee : Ty}
    {derefTy : Ty} {leafView : PartialTy} {rhsTy : Ty}
    {leaf : Location} {leafSlot newSlot : StoreSlot} {y : Name}
    {envSlot : EnvSlot} {oldValue : PartialValue}
    {evidence : RuntimeFrame.ValidPartialValueEvidence store oldValue
      envSlot.ty}
    {dependency : Location} {base : Name} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env source (.ty (.borrow mutable targets pointee))
      borrowLifetime →
    LValTargetsTyping env targets (.ty pointee) targetLifetime →
    LValTyping env (.deref source) (.ty derefTy) derefLifetime →
    store.loc (.deref source) = some leaf →
    store.slotAt leaf = some leafSlot →
    ValidPartialValue store leafSlot.value leafView →
    EnvWrite 0 env (.deref source) rhsTy env' →
    ¬ WriteProhibited env (.var (LVal.base source)) →
    env.slotAt y = some envSlot →
    store.slotAt (VariableProjection y) =
      some { value := oldValue, lifetime := envSlot.lifetime } →
    RuntimeFrame.EvidenceBorrowDependency store evidence dependency →
    ProtectedByBase store base dependency →
    ProtectedByBase (store.update leaf newSlot) base dependency := by
  intro hφ hwellFormed hborrowSafe hsafe hvalidStore hheap hsourceBorrow
    htargets hLhsTyping hloc hleafSlot hleafValid hwrite hnotWPbase
    henvY hstoreY hdependency hprotected
  refine ProtectedByBase.update_of_not_ancestor hprotected ?_
  intro howns
  exact
    evidenceDependency_not_below_assign_deref_borrow hφ hwellFormed
      hborrowSafe hsafe hvalidStore hheap hsourceBorrow htargets hLhsTyping
      hloc hleafSlot hleafValid hwrite hnotWPbase henvY hstoreY
      hdependency (Or.inr howns)
/--
Assignment-through-a-deref preservation engine.

Both the owned-box and borrowed-target cases of `*source := value` reduce here
once the `R-Assign` step is decomposed.  The runtime-validity component is
established directly from the write/drop preservation lemmas (using graph lemma
`droppedValueOwnersOrphaned_assign_deref` for the post-drop allocation
invariant), and the safe-abstraction component is exactly graph lemma
`safeAbstraction_assign_deref_drop_of_wellFormed`; the result value is `unit`.
-/
theorem preservation_assign_deref_envWrite_terminal_of_runtimeDropFrame
    {store writtenStore store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {lhsLocation : Location} {oldSlot : StoreSlot} {oldTy oldSlotTy : PartialTy}
    {value : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env (.deref source) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    ValidValue store value rhsTy →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    (writtenStore ∼ₛ env' →
      ValidStore writtenStore →
      StoreOwnerTargetsHeap writtenStore →
      (∀ dropValue, dropValue ∈ [oldSlot.value] →
        PartialValueOwnerTargetsHeap dropValue) →
      Drops writtenStore [oldSlot.value] store' →
      RuntimeDropFrame writtenStore env' [oldSlot.value]) →
    store.read (.deref source) = some oldSlot →
    store.loc (.deref source) = some lhsLocation →
    store.slotAt lhsLocation = some oldSlot →
    ValidPartialValue store oldSlot.value oldSlotTy →
    store.write (.deref source) (.value value) = some writtenStore →
    Drops writtenStore [oldSlot.value] store' →
    TerminalStateSafe store' .unit env' .unit := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite hderiveDropFrame hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops
  -- Owner/heap/root invariants of the post-write store.
  have hvalueHeap : ValueOwnerTargetsHeap value :=
    TermOwnerTargetsHeap.value
      (termOwnerTargetsHeap_assign_inner
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
  have hwrittenHeap : StoreOwnerTargetsHeap writtenStore :=
    storeOwnerTargetsHeap_write
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
      (ValueOwnerTargetsHeap.partial hvalueHeap) hwriteStore
  have hwrittenRoot : HeapSlotsRootLifetime writtenStore :=
    heapSlotsRootLifetime_write
      (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
  have hwrittenAllocated : StoreOwnersAllocated writtenStore :=
    storeOwnersAllocated_write_value_of_validValue
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue hwriteStore
  -- The written value's owners are not previously owned (valid-state disjointness),
  -- so the write keeps the store valid.
  have hnewDisjoint :
      ∀ owned, owned ∈ partialValueOwningLocations (.value value) →
        ¬ ProgramStore.Owns store owned := by
    intro owned hmem
    exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned (by
      simpa [termOwningLocations, termValues, partialValueOwningLocations] using hmem)
  have hwrittenValidStore : ValidStore writtenStore :=
    validStore_write_disjoint (ValidRuntimeState.validStore hvalidRuntime)
      hnewDisjoint hwriteStore
  -- Post-drop invariants.
  have hstoreHeap : StoreOwnerTargetsHeap store' :=
    drops_storeOwnerTargetsHeap hdrops hwrittenHeap
  have hstoreRoot : HeapSlotsRootLifetime store' :=
    drops_heapSlotsRootLifetime hdrops hwrittenRoot
  have hstoreAllocated : StoreOwnersAllocated store' :=
    drops_storeOwnersAllocated_of_disjoint hdrops hwrittenValidStore hwrittenAllocated
      (droppedValueOwnersOrphaned_assign_deref hwellFormed hsafe hvalidRuntime
        hlhsLoc hlhsSlot holdSlotValid hwriteStore)
  refine ⟨validRuntimeState_assign_step_of_postWriteDrop_invariants
      (lifetime := lifetime)
      hvalidRuntime hstoreAllocated hstoreHeap hstoreRoot hread hwriteStore hdrops,
    safeAbstraction_assign_deref_drop_of_runtimeDropFrame hwellFormed hborrowSafe hsafe hvalidRuntime
      hLhs hshape hwellTy hvalidValue hwrite hranked hnotWrite hderiveDropFrame hread
      hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops,
    ValidPartialValue.unit⟩

theorem preservation_assign_deref_envWrite_terminal_of_representedSlotsProtected
    {store writtenStore store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {lhsLocation : Location} {oldSlot : StoreSlot} {oldTy oldSlotTy : PartialTy}
    {value : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env (.deref source) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    ValidValue store value rhsTy →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    RuntimeRepresentedSlotsProtected writtenStore env' →
    store.read (.deref source) = some oldSlot →
    store.loc (.deref source) = some lhsLocation →
    store.slotAt lhsLocation = some oldSlot →
    ValidPartialValue store oldSlot.value oldSlotTy →
    store.write (.deref source) (.value value) = some writtenStore →
    Drops writtenStore [oldSlot.value] store' →
    TerminalStateSafe store' .unit env' .unit := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite hprotected hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops
  exact preservation_assign_deref_envWrite_terminal_of_runtimeDropFrame
    hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite
    (fun _hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap hdrops =>
      RuntimeDropFrame.of_orphaned_values hprotected
        hwrittenValidStore hwrittenHeap hdropValuesHeap
        (droppedValueOwnersOrphaned_assign_deref hwellFormed hsafe hvalidRuntime
          hlhsLoc hlhsSlot holdSlotValid hwriteStore)
        hdrops)
    hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops

theorem preservation_assign_deref_envWrite_terminal_of_wellFormed
    {store writtenStore store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {lhsLocation : Location} {oldSlot : StoreSlot} {oldTy oldSlotTy : PartialTy}
    {value : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env (.deref source) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    ValidValue store value rhsTy →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    WellFormedEnv env' lifetime →
    store.read (.deref source) = some oldSlot →
    store.loc (.deref source) = some lhsLocation →
    store.slotAt lhsLocation = some oldSlot →
    ValidPartialValue store oldSlot.value oldSlotTy →
    store.write (.deref source) (.value value) = some writtenStore →
    Drops writtenStore [oldSlot.value] store' →
    TerminalStateSafe store' .unit env' .unit := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite hwellOut hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops
  exact preservation_assign_deref_envWrite_terminal_of_runtimeDropFrame
    hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hvalidValue hwrite
    hranked hnotWrite
    (fun hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap hdrops =>
      RuntimeDropFrame.of_orphaned_values
        (RuntimeRepresentedSlotsProtected.of_containedBorrowsWellFormed
          hwellOut.1 hsafeWrite hwrittenValidStore hwrittenHeap)
        hwrittenValidStore hwrittenHeap hdropValuesHeap
        (droppedValueOwnersOrphaned_assign_deref hwellFormed hsafe hvalidRuntime
          hlhsLoc hlhsSlot holdSlotValid hwriteStore)
        hdrops)
    hread hlhsLoc hlhsSlot holdSlotValid hwriteStore hdrops

/--
Assignment through an owned box.  This isolates the `T-LvBox` subcase of
assignment preservation from the main term-induction proof.
-/
theorem preservation_assign_deref_box_step_runtime_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env source (.box oldTy) targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    WellFormedEnv env' lifetime →
    ValidValue store value rhsTy →
    Step store lifetime (.assign (.deref source) (.val value)) store' (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hsourceBox hshape hwellTy hwrite
    hranked hnotWrite hwellOut hvalidValue hstep
  rcases assign_step_components hstep with
    ⟨writtenStore, oldSlot, lhsLocation, hread, hwriteStore, hdrops,
      hlhsLoc, hlhsSlot, hwriteStoreEq, hresult⟩
  cases hresult
  rcases location_box (lvalTyping_defined_location hwellFormed hsafe hsourceBox) with
    ⟨typedLocation, typedSlot, htypedLoc, htypedSlot, htypedValid⟩
  have htypedLocationEq : typedLocation = lhsLocation := by
    rw [hlhsLoc] at htypedLoc
    exact (Option.some.inj htypedLoc).symm
  have htypedSlotEq : typedSlot = oldSlot := by
    rw [htypedLocationEq, hlhsSlot] at htypedSlot
    exact (Option.some.inj htypedSlot).symm
  have holdSlotValid : ValidPartialValue store oldSlot.value oldTy := by
    simpa [htypedSlotEq] using htypedValid
  exact preservation_assign_deref_envWrite_terminal_of_wellFormed
    hwellFormed hborrowSafe hsafe hvalidRuntime (LValTyping.box hsourceBox) hshape hwellTy
    hvalidValue hwrite hranked hnotWrite hwellOut hread hlhsLoc hlhsSlot holdSlotValid
    hwriteStore hdrops

/--
Assignment through an owned box, preserving the proof-carrying runtime
environment abstraction directly.

This is the semantic version of
`preservation_assign_deref_box_step_runtime_of_wellFormed`: it rebuilds the
updated owner-spine root evidence after the concrete leaf write, then transports
the runtime abstraction through the orphaned drop cleanup.
-/
theorem preservation_assign_deref_box_step_runtime_of_runtimeEnvAbstraction
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    RuntimeEnvAbstraction store env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env source (.box oldTy) targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    ValidValue store value rhsTy →
    Step store lifetime (.assign (.deref source) (.val value)) store' (.val finalValue) →
    TerminalStateRuntimeSafe store' finalValue env' .unit := by
  intro hwellFormed hborrowSafe habstraction hvalidRuntime hsourceBox hshape
    hwellTy hwrite hranked hnotWrite hvalidValue hstep
  have hsafe : store ∼ₛ env := habstraction.safe
  rcases assign_step_components hstep with
    ⟨writtenStore, oldSlot, lhsLocation, hread, hwriteStore, hdrops,
      hlhsLoc, hlhsSlot, hwriteEq, hresult⟩
  cases hresult
  rcases location_box (lvalTyping_defined_location hwellFormed hsafe hsourceBox) with
    ⟨typedLocation, typedSlot, htypedLoc, htypedSlot, htypedValid⟩
  have htypedLocationEq : typedLocation = lhsLocation := by
    rw [hlhsLoc] at htypedLoc
    exact (Option.some.inj htypedLoc).symm
  have htypedSlotEq : typedSlot = oldSlot := by
    rw [htypedLocationEq, hlhsSlot] at htypedSlot
    exact (Option.some.inj htypedSlot).symm
  have holdSlotValid : ValidPartialValue store oldSlot.value oldTy := by
    simpa [htypedSlotEq] using htypedValid
  have hvalueHeap : ValueOwnerTargetsHeap value :=
    TermOwnerTargetsHeap.value
      (termOwnerTargetsHeap_assign_inner
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
  have hwrittenHeap : StoreOwnerTargetsHeap writtenStore :=
    storeOwnerTargetsHeap_write
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
      (ValueOwnerTargetsHeap.partial hvalueHeap) hwriteStore
  have hwrittenRoot : HeapSlotsRootLifetime writtenStore :=
    heapSlotsRootLifetime_write
      (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
  have hwrittenAllocated : StoreOwnersAllocated writtenStore :=
    storeOwnersAllocated_write_value_of_validValue
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
      hwriteStore
  have hnewDisjoint :
      ∀ owned, owned ∈ partialValueOwningLocations (.value value) →
        ¬ ProgramStore.Owns store owned := by
    intro owned hmem
    exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned (by
      simpa [termOwningLocations, termValues, partialValueOwningLocations]
        using hmem)
  have hwrittenValidStore : ValidStore writtenStore :=
    validStore_write_disjoint (ValidRuntimeState.validStore hvalidRuntime)
      hnewDisjoint hwriteStore
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [oldSlot.value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact partialValueOwnerTargetsHeap_of_slot
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hlhsSlot
  have hdropOwnersOrphaned :
      ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
        ¬ ProgramStore.Owns writtenStore owned :=
    droppedValueOwnersOrphaned_assign_deref hwellFormed hsafe hvalidRuntime
      hlhsLoc hlhsSlot holdSlotValid hwriteStore
  rcases StoreOwnerSpine.of_lvalTyping_box hwellFormed hsafe hsourceBox with
    ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase, hrootSlot,
      hrootLifetime, hsourceLoc, hsourceSlot, hsourceSpine⟩
  have hsourceValid :
      ValidPartialValue store sourceSlot.value (.box oldTy) :=
    StoreOwnerSpine.leaf_valid hsourceSpine
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hsourceValid with
  | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
      have hderefLoc :
          store.loc (.deref source) = some ownerLocation := by
        simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
      have hownerLocationEq : ownerLocation = lhsLocation := by
        rw [hlhsLoc] at hderefLoc
        exact (Option.some.inj hderefLoc).symm
      have hownerSlotEq : ownerSlot = oldSlot := by
        rw [hownerLocationEq, hlhsSlot] at hownedSlot
        exact (Option.some.inj hownedSlot).symm
      have hspine :
          StoreOwnerSpine store
            (VariableProjection (LVal.base (.deref source))) rootSlot
            envSlot.ty (LVal.path (.deref source)) lhsLocation oldSlot
            oldTy := by
        have hsnoc :
            StoreOwnerSpine store
              (VariableProjection (LVal.base source)) rootSlot envSlot.ty
              (() :: LVal.path source) ownerLocation ownerSlot oldTy :=
          StoreOwnerSpine.snoc_box hsourceSpine rfl rfl hownedSlot
            hinnerValid
        simpa [LVal.base, LVal.path_deref_cons, hownerLocationEq,
          hownerSlotEq] using hsnoc
      cases hwrite with
      | @intro _rank _env₁ writeEnv _writeLv writeSlot _writeTy updatedTy
          hwriteSlot hupdate =>
          have hwriteSlotEq : writeSlot = envSlot := by
            simp [LVal.base] at hwriteSlot
            have hsome : some writeSlot = some envSlot := by
              rw [← hwriteSlot, henvBase]
            exact Option.some.inj hsome
          subst writeSlot
          have hupdatePath :
              UpdateAtPath 0 env (LVal.path (.deref source)) envSlot.ty
                rhsTy writeEnv updatedTy := by
            simpa [LVal.base] using hupdate
          have hwriteEnvEq : writeEnv = env :=
            StoreOwnerSpine.updateAtPath_rank_zero_env_eq hspine hupdatePath
          subst writeEnv
          have hpathNonempty : LVal.path (.deref source) ≠ [] := by
            simp [LVal.path_deref_cons]
          have hresultRoot :
              (env.update (LVal.base source)
                { envSlot with ty := updatedTy }).slotAt
                  (LVal.base source) =
              some { envSlot with ty := updatedTy } := by
            simp [Env.update]
          have hnotWriteObserver :
              ¬ WriteProhibited
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy })
                (.var (LVal.base source)) := by
            simpa [LVal.base] using
              (not_writeProhibited_var_base hnotWrite)
          have hnotWriteSource :
              ¬ WriteProhibited env (.var (LVal.base source)) :=
            not_writeProhibited_var_of_update_self hwellFormed.2.2.2
              hnotWriteObserver
          have hrhsVarsUpdated :
              ∀ z, z ∈ PartialTy.vars (.ty rhsTy) →
                z ∈ PartialTy.vars updatedTy :=
            StoreOwnerSpine.updateAtPath_rank_zero_rhs_vars_subset_updated
              hspine hupdatePath
          have hvarsObserver :
              ∀ z, z ∈ PartialTy.vars (.ty rhsTy) →
                WriteProhibited
                  (env.update (LVal.base source)
                    { envSlot with ty := updatedTy })
                  (.var z) := by
            intro z hz
            exact writeProhibited_of_envSlot_var_in_type hresultRoot rfl
              (hrhsVarsUpdated z hz)
          have hvalidRuntimeValue :
              ValidRuntimeState store (.val value) :=
            validRuntimeState_assign_inner hvalidRuntime
          have hvalueNoReachLeaf :
              ∀ location,
                RuntimeFrame.Reaches store (.value value) (.ty rhsTy)
                  location →
                location ≠ lhsLocation :=
            term_value_reaches_ne_owner_spine_leaf_of_noWrite
              hwellFormed hsafe hvalidRuntimeValue hwellTy hvalidValue
              hspine hvarsObserver hnotWriteSource hnotWriteObserver
          have hnewValidUpdate :
              ValidPartialValue
                (store.update lhsLocation
                  { oldSlot with value := .value value })
                (.value value) (.ty rhsTy) :=
            RuntimeFrame.validPartialValue_update_of_not_reaches
              hvalidValue hvalueNoReachLeaf
          have hotherNoReachLeaf :
              ∀ y otherEnvSlot oldValue,
                y ≠ LVal.base source →
                env.slotAt y = some otherEnvSlot →
                store.slotAt (VariableProjection y) =
                  some (StoreSlot.mk oldValue otherEnvSlot.lifetime) →
                ∀ location,
                  RuntimeFrame.Reaches store oldValue otherEnvSlot.ty
                    location →
                  location ≠ lhsLocation := by
            intro y otherEnvSlot oldValue hyx henvY hslotY
            have henvYPost :
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy }).slotAt y =
                some otherEnvSlot := by
              simpa [Env.update, hyx] using henvY
            have hvarsOther :
                ∀ z, z ∈ PartialTy.vars otherEnvSlot.ty →
                  WriteProhibited
                    (env.update (LVal.base source)
                      { envSlot with ty := updatedTy })
                    (.var z) := by
              intro z hz
              exact writeProhibited_of_envSlot_var_in_type henvYPost rfl hz
            rcases hsafe.2 y otherEnvSlot henvY with
              ⟨safeValue, hsafeSlot, hvalidOld⟩
            have hsafeValueEq : safeValue = oldValue := by
              have hslotEq :
                  StoreSlot.mk safeValue otherEnvSlot.lifetime =
                  StoreSlot.mk oldValue otherEnvSlot.lifetime :=
                Option.some.inj (hsafeSlot.symm.trans hslotY)
              exact congrArg StoreSlot.value hslotEq
            subst hsafeValueEq
            exact
              stored_var_reaches_ne_owner_spine_leaf_of_noWrite
                hwellFormed hsafe
                (ValidRuntimeState.validStore hvalidRuntime)
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hspine hyx henvY hslotY hvalidOld hvarsOther
                hnotWriteSource hnotWriteObserver
          have hsafeWriteUpdate :
              store.update lhsLocation { oldSlot with value := .value value } ∼ₛ
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy }) := by
            simpa [LVal.base] using
              safeAbstraction_update_owner_spine_of_frames
                hwellFormed hsafe
                (ValidRuntimeState.validStore hvalidRuntime)
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                henvBase hrootSlot hrootLifetime hspine hpathNonempty
                hupdatePath rfl hnewValidUpdate hotherNoReachLeaf
          have hwriteValidStoreUpdate :
              ValidStore
                (store.update lhsLocation
                  { oldSlot with value := .value value }) := by
            rw [← hwriteEq]
            exact hwrittenValidStore
          have hwriteHeapUpdate :
              StoreOwnerTargetsHeap
                (store.update lhsLocation
                  { oldSlot with value := .value value }) := by
            rw [← hwriteEq]
            exact hwrittenHeap
          have hnewBorrows :
              PartialTyBorrowsWellFormedInSlot env rhsWellLifetime
                (.ty rhsTy) :=
            PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy
          have hnewBorrowsPost :
              PartialTyBorrowsWellFormedInSlot
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy })
                rhsWellLifetime (.ty rhsTy) := by
            exact PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts
              (x := LVal.base source)
              (slot := { envSlot with ty := updatedTy })
              hnotWriteObserver
              hnewBorrows
              (by
                intro mutable targets pointee hcontains target htarget
                  hconflict
                have hxVars :
                    LVal.base source ∈ PartialTy.vars (.ty rhsTy) :=
                  mem_partialTy_vars_iff.mpr
                    ⟨mutable, targets, pointee, target, hcontains, htarget,
                      by simpa [PathConflicts, LVal.base] using hconflict⟩
                exact hnotWriteObserver
                  (writeProhibited_of_envSlot_var_in_type hresultRoot rfl
                    (hrhsVarsUpdated (LVal.base source) hxVars)))
          rcases RuntimeFrame.ValidPartialValueEvidence.exists_of_valid
              hnewValidUpdate with
            ⟨newEvidence, _⟩
          rcases StoreOwnerSpine.evidence_after_leaf_strong_update
              (newSlot := { oldSlot with value := .value value })
              hspine hpathNonempty newEvidence with
            ⟨strongRootEvidence, hstrongRootDeps⟩
          rcases
              StoreOwnerSpine.strongLeafUpdate_strengthens_updateAtPath_rank_zero
                hspine hupdatePath with
            ⟨hstrongStrength, hstrongShape⟩
          rcases
              RuntimeFrame.ValidPartialValueEvidence.strengthen_sameShape_exists
                strongRootEvidence hstrongStrength hstrongShape with
            ⟨rootEvidence, hrootEvidenceRel⟩
          have hnewProtected :
              ∀ dependency,
                RuntimeFrame.EvidenceBorrowDependency
                  (store.update lhsLocation
                    { oldSlot with value := .value value })
                  newEvidence dependency →
                ∃ base,
                  ProtectedByBase
                    (store.update lhsLocation
                      { oldSlot with value := .value value })
                    base dependency := by
            intro dependency hdependency
            exact borrowDependency_protectedBySomeBase_of_safe
              hsafeWriteUpdate hwriteValidStoreUpdate hwriteHeapUpdate
              hnewBorrowsPost
              (RuntimeFrame.SelectedBorrowDependency.borrowDependency
                (RuntimeFrame.EvidenceBorrowDependency.selected hdependency))
          have hrootProtected :
              ∀ dependency,
                RuntimeFrame.EvidenceBorrowDependency
                  (store.update lhsLocation
                    { oldSlot with value := .value value })
                  rootEvidence dependency →
                ∃ base,
                  ProtectedByBase
                    (store.update lhsLocation
                      { oldSlot with value := .value value })
                    base dependency := by
            intro dependency hdependency
            exact hnewProtected dependency
              (hstrongRootDeps dependency
                (RuntimeFrame.EvidenceBorrowDependency.of_strengthensSameShape
                  hrootEvidenceRel hdependency))
          have hotherFrame :
              ∀ y otherEnvSlot oldValue
                (evidence :
                  RuntimeFrame.ValidPartialValueEvidence store oldValue
                    otherEnvSlot.ty),
                y ≠ LVal.base source →
                env.slotAt y = some otherEnvSlot →
                store.slotAt (VariableProjection y) =
                  some (StoreSlot.mk oldValue otherEnvSlot.lifetime) →
                (∀ location,
                  RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty
                    location →
                  location ≠ lhsLocation) ∧
                (∀ location,
                  RuntimeFrame.EvidenceBorrowDependency store evidence
                    location →
                  location ≠ lhsLocation) := by
            intro y otherEnvSlot oldValue evidence hyx henvY hstoreY
            constructor
            · intro location howner
              exact hotherNoReachLeaf y otherEnvSlot oldValue hyx henvY
                hstoreY location howner.reaches
            · intro dependency hdependency
              exact hotherNoReachLeaf y otherEnvSlot oldValue hyx henvY
                hstoreY dependency
                (RuntimeFrame.BorrowDependency.reaches
                  (RuntimeFrame.SelectedBorrowDependency.borrowDependency
                    (RuntimeFrame.EvidenceBorrowDependency.selected
                      hdependency)))
          have hprotectedTransport :
              ∀ y otherEnvSlot oldValue
                (evidence :
                  RuntimeFrame.ValidPartialValueEvidence store oldValue
                    otherEnvSlot.ty),
                y ≠ LVal.base source →
                env.slotAt y = some otherEnvSlot →
                store.slotAt (VariableProjection y) =
                  some (StoreSlot.mk oldValue otherEnvSlot.lifetime) →
                ∀ dependency,
                  RuntimeFrame.EvidenceBorrowDependency store evidence
                    dependency →
                ∀ base,
                  ProtectedByBase store base dependency →
                  ProtectedByBase
                    (store.update lhsLocation
                      { oldSlot with value := .value value })
                    base dependency := by
            intro y otherEnvSlot oldValue evidence hyx henvY hstoreY
              dependency hdependency base hprotected
            refine ProtectedByBase.update_of_not_protected hprotected ?_
            intro hbaseLeaf
            have hrootProtectedLeaf :
                ProtectedByBase store (LVal.base source) lhsLocation :=
              Or.inr (StoreOwnerSpine.ownsTransitively_of_nonempty hspine
                hpathNonempty)
            have hbaseEq : base = LVal.base source :=
              ProtectedByBase.root_unique
                (ValidRuntimeState.validStore hvalidRuntime)
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hbaseLeaf hrootProtectedLeaf
            subst base
            have hborrowsOld :
                PartialTyBorrowsWellFormedInSlot env otherEnvSlot.lifetime
                  otherEnvSlot.ty := by
              intro mutable targets pointee hcontains
              exact hwellFormed.1 y otherEnvSlot mutable targets pointee
                henvY ⟨otherEnvSlot, henvY, hcontains⟩
            have henvYPost :
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy }).slotAt y =
                some otherEnvSlot := by
              simpa [Env.update, hyx] using henvY
            have hvarsPost :
                ∀ z, z ∈ PartialTy.vars otherEnvSlot.ty →
                  WriteProhibited
                    (env.update (LVal.base source)
                      { envSlot with ty := updatedTy })
                    (.var z) := by
              intro z hz
              exact writeProhibited_of_envSlot_var_in_type henvYPost rfl hz
            exact
              (borrowDependency_not_protectedByBase_of_varsProtectedIn
                hwellFormed hsafe
                (ValidRuntimeState.validStore hvalidRuntime)
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hborrowsOld hvarsPost hnotWriteSource hnotWriteObserver
                (RuntimeFrame.SelectedBorrowDependency.borrowDependency
                  (RuntimeFrame.EvidenceBorrowDependency.selected
                    hdependency)))
                hprotected
          have habstractionWriteUpdate :
              RuntimeEnvAbstraction
                (store.update lhsLocation
                  { oldSlot with value := .value value })
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy }) := by
            simpa [LVal.base] using
              RuntimeEnvAbstraction.update_owner_spine
                habstraction
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                henvBase hrootSlot hrootLifetime hspine hpathNonempty
                hupdatePath rfl rootEvidence hrootProtected
                hotherFrame hprotectedTransport
          have habstractionWrite :
              RuntimeEnvAbstraction writtenStore
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy }) := by
            rw [hwriteEq]
            simpa [LVal.base] using habstractionWriteUpdate
          have habstractionFinal :
              RuntimeEnvAbstraction store'
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy }) :=
            RuntimeEnvAbstraction.drops_of_orphaned_values
              habstractionWrite hwrittenValidStore hwrittenHeap hdropValuesHeap
              hdropOwnersOrphaned hdrops
          have hstoreHeap : StoreOwnerTargetsHeap store' :=
            drops_storeOwnerTargetsHeap hdrops hwrittenHeap
          have hstoreRoot : HeapSlotsRootLifetime store' :=
            drops_heapSlotsRootLifetime hdrops hwrittenRoot
          have hstoreAllocated : StoreOwnersAllocated store' :=
            drops_storeOwnersAllocated_of_disjoint hdrops hwrittenValidStore
              hwrittenAllocated hdropOwnersOrphaned
          exact ⟨
            validRuntimeState_assign_step_of_postWriteDrop_invariants
              (lifetime := lifetime)
              hvalidRuntime hstoreAllocated hstoreHeap hstoreRoot hread
              hwriteStore hdrops,
            habstractionFinal,
            ValidPartialValue.unit⟩

/--
Assignment through a borrow target.  This is the case where the proof has to use
the selected borrow target as write authority rather than reducing the target to
a direct variable write.
-/
theorem preservation_assign_deref_borrow_step_runtime_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime borrowLifetime targetLifetime rhsWellLifetime : Lifetime}
    {source : LVal} {mutable : Bool} {targets : List LVal}
    {pointee : Ty} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env source (.ty (.borrow mutable targets pointee)) borrowLifetime →
    LValTargetsTyping env targets (.ty pointee) targetLifetime →
    ShapeCompatible env (.ty pointee) (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    WellFormedEnv env' lifetime →
    ValidValue store value rhsTy →
    Step store lifetime (.assign (.deref source) (.val value)) store' (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hsourceBorrow htargets hshape hwellTy
    hwrite hranked hnotWrite hwellOut hvalidValue hstep
  rcases assign_step_components hstep with
    ⟨writtenStore, oldSlot, lhsLocation, hread, hwriteStore, hdrops,
      hlhsLoc, hlhsSlot, hwriteStoreEq, hresult⟩
  cases hresult
  rcases runtimeCoherent_selectedTarget_of_safe hsafe hsourceBorrow htargets with
    ⟨selectedTarget, selectedTy, selectedLifetime, borrowedLocation,
      _hselectedMem, hselectedTyping, _hselectedStrengthens, hselectedLoc,
      hpointsTo⟩
  rcases lvalTyping_defined_location_of_safe hsafe hselectedTyping with
    ⟨typedLocation, typedSlot, htypedLoc, htypedSlot, htypedValid⟩
  have htypedLocationBorrowed : typedLocation = borrowedLocation := by
    rw [hselectedLoc] at htypedLoc
    exact (Option.some.inj htypedLoc).symm
  have hderefLoc : store.loc (.deref source) = some borrowedLocation := by
    rcases hpointsTo with
      ⟨sourceLocation, slotLifetime, hsourceLoc, hsourceSlot⟩
    simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
  have hborrowedLocationEq : borrowedLocation = lhsLocation := by
    rw [hlhsLoc] at hderefLoc
    exact (Option.some.inj hderefLoc).symm
  have htypedLocationEq : typedLocation = lhsLocation :=
    htypedLocationBorrowed.trans hborrowedLocationEq
  have htypedSlotEq : typedSlot = oldSlot := by
    rw [htypedLocationEq] at htypedSlot
    rw [hlhsSlot] at htypedSlot
    exact (Option.some.inj htypedSlot).symm
  have holdSlotValid : ValidPartialValue store oldSlot.value (.ty selectedTy) := by
    simpa [htypedSlotEq] using htypedValid
  exact preservation_assign_deref_envWrite_terminal_of_wellFormed
    hwellFormed hborrowSafe hsafe hvalidRuntime (LValTyping.borrow hsourceBorrow htargets)
    hshape hwellTy hvalidValue hwrite hranked hnotWrite hwellOut hread hlhsLoc hlhsSlot
    holdSlotValid hwriteStore hdrops

/--
Assignment through a borrow target, preserving the proof-carrying runtime
environment abstraction directly.

The selected borrow target can be either a variable slot or a heap cell inside a
root owner's box spine.  In both cases the proof rebuilds the represented-slot
evidence from the concrete write and then transports it through the orphaned
drop cleanup.
-/
theorem preservation_assign_deref_borrow_step_runtime_of_runtimeEnvAbstraction
    {store store' : ProgramStore} {env env' : Env}
    {lifetime borrowLifetime targetLifetime rhsWellLifetime : Lifetime}
    {source : LVal} {mutable : Bool} {targets : List LVal}
    {pointee : Ty} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    RuntimeEnvAbstraction store env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env source (.ty (.borrow mutable targets pointee))
      borrowLifetime →
    LValTargetsTyping env targets (.ty pointee) targetLifetime →
    ShapeCompatible env (.ty pointee) (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    ValidValue store value rhsTy →
    Step store lifetime (.assign (.deref source) (.val value)) store'
      (.val finalValue) →
    TerminalStateRuntimeSafe store' finalValue env' .unit := by
  intro hwellFormed hborrowSafe habstraction hvalidRuntime hsourceBorrow
    htargets hshape hwellTy hwrite hranked hnotWrite hvalidValue hstep
  have hsafe : store ∼ₛ env := habstraction.safe
  rcases assign_step_components hstep with
    ⟨writtenStore, oldSlot, lhsLocation, hread, hwriteStore, hdrops,
      hlhsLoc, hlhsSlot, hwriteEq, hresult⟩
  cases hresult
  rcases runtimeCoherent_selectedTarget_of_safe hsafe hsourceBorrow htargets with
    ⟨selectedTarget, selectedTy, selectedLifetime, borrowedLocation,
      _hselectedMem, hselectedTyping, _hselectedStrengthens, hselectedLoc,
      hpointsTo⟩
  rcases lvalTyping_defined_location_of_safe hsafe hselectedTyping with
    ⟨typedLocation, typedSlot, htypedLoc, htypedSlot, htypedValid⟩
  have htypedLocationBorrowed : typedLocation = borrowedLocation := by
    rw [hselectedLoc] at htypedLoc
    exact (Option.some.inj htypedLoc).symm
  have hderefLoc : store.loc (.deref source) = some borrowedLocation := by
    rcases hpointsTo with
      ⟨sourceLocation, slotLifetime, hsourceLoc, hsourceSlot⟩
    simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
  have hborrowedLocationEq : borrowedLocation = lhsLocation := by
    rw [hlhsLoc] at hderefLoc
    exact (Option.some.inj hderefLoc).symm
  have htypedLocationEq : typedLocation = lhsLocation :=
    htypedLocationBorrowed.trans hborrowedLocationEq
  have htypedSlotEq : typedSlot = oldSlot := by
    rw [htypedLocationEq] at htypedSlot
    rw [hlhsSlot] at htypedSlot
    exact (Option.some.inj htypedSlot).symm
  have holdSlotValid : ValidPartialValue store oldSlot.value (.ty selectedTy) := by
    simpa [htypedSlotEq] using htypedValid
  rcases LValTargetsTyping.output_full htargets with ⟨lhsTy, hOldTyFull⟩
  have hLhsTyping : LValTyping env (.deref source) (.ty lhsTy) targetLifetime := by
    rw [← hOldTyFull]
    exact LValTyping.borrow hsourceBorrow htargets
  have hvalidStore : ValidStore store :=
    ValidRuntimeState.validStore hvalidRuntime
  have hheap : StoreOwnerTargetsHeap store :=
    ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
  have hvalueHeap : ValueOwnerTargetsHeap value :=
    TermOwnerTargetsHeap.value
      (termOwnerTargetsHeap_assign_inner
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
  have hwrittenHeap : StoreOwnerTargetsHeap writtenStore :=
    storeOwnerTargetsHeap_write hheap
      (ValueOwnerTargetsHeap.partial hvalueHeap) hwriteStore
  have hwrittenRoot : HeapSlotsRootLifetime writtenStore :=
    heapSlotsRootLifetime_write
      (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
  have hwrittenAllocated : StoreOwnersAllocated writtenStore :=
    storeOwnersAllocated_write_value_of_validValue
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
      hwriteStore
  have hnewDisjoint :
      ∀ owned, owned ∈ partialValueOwningLocations (.value value) →
        ¬ ProgramStore.Owns store owned := by
    intro owned hmem
    exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned (by
      simpa [termOwningLocations, termValues, partialValueOwningLocations]
        using hmem)
  have hwrittenValidStore : ValidStore writtenStore :=
    validStore_write_disjoint hvalidStore hnewDisjoint hwriteStore
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [oldSlot.value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact partialValueOwnerTargetsHeap_of_slot hheap hlhsSlot
  have hdropOwnersOrphaned :
      ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
        ¬ ProgramStore.Owns writtenStore owned :=
    droppedValueOwnersOrphaned_assign_deref hwellFormed hsafe hvalidRuntime
      hlhsLoc hlhsSlot holdSlotValid hwriteStore
  rcases hranked with ⟨φ, hφ, hbelowRhs⟩
  have hglobalMap : EnvSameShapeStrengthening env env' := by
    cases hwrite with
    | @intro _rank _env₁ writeEnv _writeLv writeSlot _ty updatedTy
        hwriteSlot hupdate =>
        have hwriteSlotBase :
            env.slotAt (LVal.base source) = some writeSlot := by
          simpa [LVal.base] using hwriteSlot
        have hthrough :
            PathThroughBorrow writeSlot.ty (LVal.path (.deref source)) := by
          simpa [LVal.path] using
            LValTyping.pathThroughBorrow_append hsourceBorrow hwriteSlotBase
              [()] PathThroughBorrow.borrowHere
        rcases UpdateAtPath.sameShapeStrengthening_of_throughBorrow hthrough
            hupdate with
          ⟨hmap, hstrength, hshape'⟩
        have hfinal :=
          EnvSameShapeStrengthening.update_result_strengthening
            (resultSlot := { writeSlot with ty := updatedTy })
            hmap hwriteSlotBase rfl hstrength hshape'
        simpa [LVal.base] using hfinal
  have hnotWPbase : ¬ WriteProhibited env (.var (LVal.base source)) := by
    intro hWP
    exact hnotWrite (writeProhibited_var_transport hglobalMap rfl hWP)
  have hwriteStoreUpdate :
      store.update lhsLocation { oldSlot with value := .value value } =
        writtenStore := by
    exact hwriteEq.symm
  cases lhsLocation with
  | var selectedName =>
      have hstoreSelected :
          store.slotAt (VariableProjection selectedName) = some oldSlot := by
        simpa [VariableProjection] using hlhsSlot
      rcases (hsafe.1 selectedName).mp ⟨oldSlot, hstoreSelected⟩ with
        ⟨selectedEnvSlot, henvSelected⟩
      have hslotLifetime :
          oldSlot.lifetime = selectedEnvSlot.lifetime := by
        rcases hsafe.2 selectedName selectedEnvSlot henvSelected with
          ⟨safeValue, hsafeSlot, _hvalidSafe⟩
        have hslotEq :
            StoreSlot.mk safeValue selectedEnvSlot.lifetime = oldSlot :=
          Option.some.inj (hsafeSlot.symm.trans hstoreSelected)
        exact (congrArg StoreSlot.lifetime hslotEq).symm
      have hlhsLocVar :
          store.loc (.deref source) = some (VariableProjection selectedName) := by
        simpa [VariableProjection] using hlhsLoc
      rcases lval_loc_var_slot_full_of_lvalTyping hwellFormed hsafe hheap
          hLhsTyping hlhsLocVar henvSelected with
        ⟨selectedSlotTy, hselectedSlotTy⟩
      have hselectedMap :
          EnvSameShapeStrengthening
            (env.update selectedName
              { selectedEnvSlot with ty := .ty rhsTy }) env' :=
        EnvWrite.runtime_selected_lval_map_of_safe hφ hsafe hheap
          hLhsTyping hlhsLocVar henvSelected hselectedSlotTy hwrite
      have hrootProtected :
          ProtectedByBase store selectedName (VariableProjection selectedName) :=
        Or.inl rfl
      have hvalueOwnerFrame :
          ∀ location,
            RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy)
              location →
            location ≠ VariableProjection selectedName := by
        intro location howner
        exact RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
          hheap hvalueHeap hwellTy howner
      rcases
          rhsEvidence_update_assign_deref_borrow
            (root := selectedName) (rootEnvSlot := selectedEnvSlot)
            (updatedTy := .ty rhsTy)
            (leaf := VariableProjection selectedName)
            (newSlot := { oldSlot with value := .value value })
            hφ hwellFormed hsafe hvalidStore hheap hwellTy hvalidValue
            hselectedMap hbelowRhs hrootProtected henvSelected
            (by
              intro mutable' targets' pointee' hcontains
              exact ⟨targets', hcontains, fun _ h => h⟩)
            hvalueOwnerFrame with
        ⟨newEvidence, hnewProtected⟩
      have hotherFrame :
          ∀ y otherEnvSlot oldValue
            (evidence :
              RuntimeFrame.ValidPartialValueEvidence store oldValue
                otherEnvSlot.ty),
            y ≠ selectedName →
            env.slotAt y = some otherEnvSlot →
            store.slotAt (VariableProjection y) =
              some (StoreSlot.mk oldValue otherEnvSlot.lifetime) →
            (∀ location,
              RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty
                location →
              location ≠ VariableProjection selectedName) ∧
            (∀ location,
              RuntimeFrame.EvidenceBorrowDependency store evidence location →
              location ≠ VariableProjection selectedName) := by
        intro y otherEnvSlot oldValue evidence hyx henvY hstoreY
        exact
          oldEvidenceFrame_assign_deref_borrow hφ hwellFormed hborrowSafe
            hsafe hvalidStore hheap hsourceBorrow htargets hLhsTyping
            hlhsLocVar hstoreSelected holdSlotValid hwrite hnotWPbase
            hrootProtected hyx henvY hstoreY
      have hprotectedTransport :
          ∀ y otherEnvSlot oldValue
            (evidence :
              RuntimeFrame.ValidPartialValueEvidence store oldValue
                otherEnvSlot.ty),
            y ≠ selectedName →
            env.slotAt y = some otherEnvSlot →
            store.slotAt (VariableProjection y) =
              some (StoreSlot.mk oldValue otherEnvSlot.lifetime) →
            ∀ location,
              RuntimeFrame.EvidenceBorrowDependency store evidence location →
            ∀ base,
              ProtectedByBase store base location →
              ProtectedByBase
                (store.update (VariableProjection selectedName)
                  { oldSlot with value := .value value })
                base location := by
        intro y otherEnvSlot oldValue evidence _hyx henvY hstoreY location
          hdependency base hprotected
        exact
          oldEvidenceProtected_update_assign_deref_borrow hφ hwellFormed
            hborrowSafe hsafe hvalidStore hheap hsourceBorrow htargets
            hLhsTyping hlhsLocVar hstoreSelected holdSlotValid hwrite
            hnotWPbase henvY hstoreY hdependency hprotected
      have habstractionWriteUpdate :
          RuntimeEnvAbstraction
            (store.update (VariableProjection selectedName)
              { oldSlot with value := .value value })
            (env.update selectedName
              { selectedEnvSlot with ty := .ty rhsTy }) :=
        RuntimeEnvAbstraction.update_var habstraction henvSelected
          (by simpa using hslotLifetime) newEvidence hnewProtected
          hotherFrame hprotectedTransport
      have habstractionWrite : RuntimeEnvAbstraction writtenStore env' := by
        rw [hwriteEq]
        exact RuntimeEnvAbstraction.strengthen_sameShape
          (by simpa [VariableProjection] using habstractionWriteUpdate)
          hselectedMap
      have habstractionFinal : RuntimeEnvAbstraction store' env' :=
        RuntimeEnvAbstraction.drops_of_orphaned_values habstractionWrite
          hwrittenValidStore hwrittenHeap hdropValuesHeap hdropOwnersOrphaned
          hdrops
      have hstoreHeap : StoreOwnerTargetsHeap store' :=
        drops_storeOwnerTargetsHeap hdrops hwrittenHeap
      have hstoreRoot : HeapSlotsRootLifetime store' :=
        drops_heapSlotsRootLifetime hdrops hwrittenRoot
      have hstoreAllocated : StoreOwnersAllocated store' :=
        drops_storeOwnersAllocated_of_disjoint hdrops hwrittenValidStore
          hwrittenAllocated hdropOwnersOrphaned
      exact ⟨
        validRuntimeState_assign_step_of_postWriteDrop_invariants
          (lifetime := lifetime)
          hvalidRuntime hstoreAllocated hstoreHeap hstoreRoot hread
          hwriteStore hdrops,
        habstractionFinal,
        ValidPartialValue.unit⟩
  | heap address =>
      have hlhsLocHeap : store.loc (.deref source) = some (.heap address) :=
        hlhsLoc
      rcases heapLeaf_spine_of_loc_of_safe hφ hsafe hLhsTyping
          hlhsLocHeap with
        ⟨xRoot, envSlotXr, rootSlotXr, spinePath, leafSlotXr, leafTyXr,
          henvXr, hrootSlotXr, hrootLifetimeXr, hspine,
          hspineNonempty⟩
      have hrootProtected :
          ProtectedByBase store xRoot (.heap address) :=
        Or.inr (StoreOwnerSpine.ownsTransitively_of_nonempty hspine
          hspineNonempty)
      have hmapSpine :
          EnvSameShapeStrengthening
            (env.update xRoot
              { envSlotXr with
                  ty := PartialTy.strongLeafUpdate envSlotXr.ty spinePath
                    rhsTy })
            env' :=
        EnvWrite.runtime_selected_spine_map_of_safe hφ hsafe hvalidStore
          hheap henvXr hspine hspineNonempty hLhsTyping hlhsLocHeap
          hwrite
      have hvalidRuntimeValue :
          ValidRuntimeState store (.val value) :=
        validRuntimeState_assign_inner hvalidRuntime
      have hborrowsRhs :
          PartialTyBorrowsWellFormedInSlot env rhsWellLifetime
            (.ty rhsTy) :=
        PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy
      have hvalueHeapRhs :
          PartialValueOwnerTargetsHeap (.value value) :=
        ValueOwnerTargetsHeap.partial
          (TermOwnerTargetsHeap.value
            (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntimeValue))
      have hrootNoOwnerReach :
          ∀ reached,
            RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy)
              reached →
            reached ≠ VariableProjection xRoot := by
        intro reached hownerReach
        exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows hheap
          hvalueHeapRhs hborrowsRhs hownerReach
      have hvalueOwnerFrame :
          ∀ reached,
            RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy)
              reached →
            reached ≠ .heap address :=
        StoreOwnerSpine.not_reaches_leaf_of_not_reaches_root
          hvalidRuntimeValue hborrowsRhs hvalidValue hspine
          hrootNoOwnerReach
      rcases
          rhsEvidence_update_assign_deref_borrow
            (root := xRoot) (rootEnvSlot := envSlotXr)
            (updatedTy :=
              PartialTy.strongLeafUpdate envSlotXr.ty spinePath rhsTy)
            (leaf := .heap address)
            (newSlot := { oldSlot with value := .value value })
            hφ hwellFormed hsafe hvalidStore hheap hwellTy hvalidValue
            hmapSpine hbelowRhs hrootProtected henvXr
            (by
              intro mutable' targets' pointee' hcontains
              exact
                ⟨targets',
                  StoreOwnerSpine.strongLeafUpdate_contains hspine hcontains,
                  fun _ h => h⟩)
            hvalueOwnerFrame with
        ⟨newEvidence, hnewProtected⟩
      rcases StoreOwnerSpine.evidence_after_leaf_strong_update
          (newSlot := { oldSlot with value := .value value })
          hspine hspineNonempty newEvidence with
        ⟨strongRootEvidence, hstrongRootDeps⟩
      have hstrongRootProtected :
          ∀ dependency,
            RuntimeFrame.EvidenceBorrowDependency
              (store.update (.heap address)
                { oldSlot with value := .value value })
              strongRootEvidence dependency →
            ∃ base,
              ProtectedByBase
                (store.update (.heap address)
                  { oldSlot with value := .value value })
                base dependency := by
        intro dependency hdependency
        exact hnewProtected dependency (hstrongRootDeps dependency hdependency)
      have hotherFrame :
          ∀ y otherEnvSlot oldValue
            (evidence :
              RuntimeFrame.ValidPartialValueEvidence store oldValue
                otherEnvSlot.ty),
            y ≠ xRoot →
            env.slotAt y = some otherEnvSlot →
            store.slotAt (VariableProjection y) =
              some (StoreSlot.mk oldValue otherEnvSlot.lifetime) →
            (∀ location,
              RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty
                location →
              location ≠ .heap address) ∧
            (∀ location,
              RuntimeFrame.EvidenceBorrowDependency store evidence location →
              location ≠ .heap address) := by
        intro y otherEnvSlot oldValue evidence hyx henvY hstoreY
        exact
          oldEvidenceFrame_assign_deref_borrow hφ hwellFormed hborrowSafe
            hsafe hvalidStore hheap hsourceBorrow htargets hLhsTyping
            hlhsLocHeap hlhsSlot holdSlotValid hwrite hnotWPbase
            hrootProtected hyx henvY hstoreY
      have hprotectedTransport :
          ∀ y otherEnvSlot oldValue
            (evidence :
              RuntimeFrame.ValidPartialValueEvidence store oldValue
                otherEnvSlot.ty),
            y ≠ xRoot →
            env.slotAt y = some otherEnvSlot →
            store.slotAt (VariableProjection y) =
              some (StoreSlot.mk oldValue otherEnvSlot.lifetime) →
            ∀ location,
              RuntimeFrame.EvidenceBorrowDependency store evidence location →
            ∀ base,
              ProtectedByBase store base location →
              ProtectedByBase
                (store.update (.heap address)
                  { oldSlot with value := .value value })
                base location := by
        intro y otherEnvSlot oldValue evidence _hyx henvY hstoreY location
          hdependency base hprotected
        exact
          oldEvidenceProtected_update_assign_deref_borrow hφ hwellFormed
            hborrowSafe hsafe hvalidStore hheap hsourceBorrow htargets
            hLhsTyping hlhsLocHeap hlhsSlot holdSlotValid hwrite hnotWPbase
            henvY hstoreY hdependency hprotected
      have habstractionWriteStrong :
          RuntimeEnvAbstraction
            (store.update (.heap address)
              { oldSlot with value := .value value })
            (env.update xRoot
              { envSlotXr with
                  ty := PartialTy.strongLeafUpdate envSlotXr.ty spinePath
                    rhsTy }) :=
        RuntimeEnvAbstraction.update_owner_spine_strong habstraction hheap
          henvXr hrootSlotXr hrootLifetimeXr hspine hspineNonempty rfl
          strongRootEvidence hstrongRootProtected hotherFrame
          hprotectedTransport
      have habstractionWrite : RuntimeEnvAbstraction writtenStore env' := by
        rw [hwriteEq]
        exact RuntimeEnvAbstraction.strengthen_sameShape
          habstractionWriteStrong hmapSpine
      have habstractionFinal : RuntimeEnvAbstraction store' env' :=
        RuntimeEnvAbstraction.drops_of_orphaned_values habstractionWrite
          hwrittenValidStore hwrittenHeap hdropValuesHeap hdropOwnersOrphaned
          hdrops
      have hstoreHeap : StoreOwnerTargetsHeap store' :=
        drops_storeOwnerTargetsHeap hdrops hwrittenHeap
      have hstoreRoot : HeapSlotsRootLifetime store' :=
        drops_heapSlotsRootLifetime hdrops hwrittenRoot
      have hstoreAllocated : StoreOwnersAllocated store' :=
        drops_storeOwnersAllocated_of_disjoint hdrops hwrittenValidStore
          hwrittenAllocated hdropOwnersOrphaned
      exact ⟨
        validRuntimeState_assign_step_of_postWriteDrop_invariants
          (lifetime := lifetime)
          hvalidRuntime hstoreAllocated hstoreHeap hstoreRoot hread
          hwriteStore hdrops,
        habstractionFinal,
        ValidPartialValue.unit⟩

/-- Assignment through a dereference, split by the lvalue-typing constructor. -/
theorem preservation_assign_deref_step_runtime_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env (.deref source) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    WellFormedEnv env' lifetime →
    ValidValue store value rhsTy →
    Step store lifetime (.assign (.deref source) (.val value)) store' (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hwrite hranked
    hnotWrite hwellOut hvalidValue hstep
  cases hLhs with
  | box hsourceBox =>
      exact preservation_assign_deref_box_step_runtime_of_wellFormed
        hwellFormed hborrowSafe hsafe hvalidRuntime hsourceBox hshape hwellTy hwrite
        hranked hnotWrite hwellOut hvalidValue hstep
  | borrow hsourceBorrow htargets =>
      exact preservation_assign_deref_borrow_step_runtime_of_wellFormed
        hwellFormed hborrowSafe hsafe hvalidRuntime hsourceBorrow htargets hshape hwellTy
        hwrite hranked hnotWrite hwellOut hvalidValue hstep

/-- Assignment redex preservation, dispatching on the lvalue shape. -/
theorem preservation_assign_step_terminal_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {lhs : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidRuntimeState store (.assign lhs (.val value)) →
    LValTyping env lhs oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    EnvWrite 0 env lhs rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' lhs →
    WellFormedEnv env' lifetime →
    ValidValue store value rhsTy →
    Step store lifetime (.assign lhs (.val value)) store' (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hwrite hranked
    hnotWrite hwellOut hvalidValue hstep
  cases lhs with
  | var x =>
      exact preservation_assign_var_step_runtime_of_wellFormed
        hwellFormed hsafe hvalidRuntime hLhs hshape hwellTy hwrite
        hnotWrite hwellOut hvalidValue hstep
  | deref source =>
      exact preservation_assign_deref_step_runtime_of_wellFormed
        hwellFormed hborrowSafe hsafe hvalidRuntime hLhs hshape hwellTy hwrite
        hranked hnotWrite hwellOut hvalidValue hstep

/-- Singleton value block preservation for `R-BlockB` using recursive drop preservation. -/
theorem preservation_blockB_value_multistep_runtime_of_runtimeDrop
    {store finalStore : ProgramStore} {env : Env}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    store ∼ₛ env →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env blockLifetime →
    WellFormedTy env ty lifetime →
    ValidValue store value ty →
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue (env.dropLifetime blockLifetime) ty := by
  intro hvalidRuntime hsafe hchild hwellBody hwellTy hvalidValue hmulti
  exact preservation_runtime_multistep_of_step_to_value
    (term := .block blockLifetime [.val value])
    (env := env.dropLifetime blockLifetime)
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
      intro store' steppedValue hstep
      cases hstep with
          | blockB hdrops =>
              have hdropDisjoint : LifetimeDropOwnersDisjoint store blockLifetime :=
                lifetimeDropOwnersDisjoint_of_heapRootLifetime
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                  (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime)
                  hchild
              cases hdrops with
              | intro hdropSet hdropsRaw =>
                  let hdropsLifetime : DropsLifetime store blockLifetime store' :=
                    ProgramStore.DropsLifetime.intro hdropSet hdropsRaw
                  have hresultValue : ValidValue store' value ty :=
                    RuntimeFrame.validPartialValue_drops_of_avoids_reaches
                      hdropsRaw hvalidValue
                      (by
                        intro location hreach
                        exact RuntimeFrame.dropsAvoids_of_reaches_validPartialValue
                          hdropsRaw
                          (ValidRuntimeState.validStore hvalidRuntime)
                          (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)
                          hvalidValue
                          (by
                            intro owned howned
                            exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
                              (by
                                simpa [termOwningLocations, termValues,
                                  partialValueOwningLocations] using howned))
                          (by
                            intro reached hreach dropValue hmem howned
                            rcases (hdropSet dropValue).mp hmem with
                              ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime,
                                hdropValue⟩
                            have hreachedEq : reached = dropLocation :=
                              eq_location_of_mem_lifetime_drop_value hdropValue howned
                            cases dropLocation with
                            | var y =>
                                have hreachVar :
                                    RuntimeFrame.OwnerReaches store (.value value) (.ty ty)
                                      (VariableProjection y) := by
                                  simpa [VariableProjection, hreachedEq] using hreach
                                exact RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
                                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                                  (TermOwnerTargetsHeap.value
                                    (termOwnerTargetsHeap_block_value
                                      (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
                                  (x := y) hwellTy hreachVar rfl
                            | heap address =>
                                have hroot : dropSlot.lifetime = Lifetime.root :=
                                  ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime
                                    address dropSlot hdropSlot
                                exact LifetimeChild.child_ne_root hchild
                                  (hdropLifetime ▸ hroot))
                            (by
                              intro dependency hdependency
                              exact borrowDependency_dropsAvoids_lifetime
                                hwellBody hsafe
                                (ValidRuntimeState.validStore hvalidRuntime)
                                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                                hdropSet hdropsRaw hdropDisjoint hchild
                                (LifetimeOutlives.refl lifetime)
                                (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)
                                hdependency)
                            hreach)
                  have hlifetimeFrame :
                      RuntimeLifetimeDropFrame store env _ blockLifetime :=
                    RuntimeLifetimeDropFrame.of_wellFormed
                      hwellBody hsafe
                      (ValidRuntimeState.validStore hvalidRuntime)
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                      hdropSet hdropsRaw hdropDisjoint hchild
                  have hsafeDrop : store' ∼ₛ env.dropLifetime blockLifetime :=
                    safeAbstraction_dropLifetime_of_runtimeFrame hsafe
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                      hdropsRaw hdropsLifetime hlifetimeFrame
                  exact ⟨validRuntimeState_blockB_step_of_child hvalidRuntime hchild
                      (Step.blockB (lifetime := lifetime) hdropsLifetime),
                    hsafeDrop, hresultValue⟩)
    hmulti

/-- `R-Seq` preserves the safe abstraction for the remaining sequence env. -/
theorem safeAbstraction_seq_value_drop_of_runtimeDropFrame
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    store ∼ₛ env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    RuntimeDropFrame store env [.value value] →
    Drops store [.value value] store' →
    store' ∼ₛ env := by
  intro hsafe hvalidRuntime hdropFrame hdrops
  have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
    ValueOwnerTargetsHeap.partial
      (TermOwnerTargetsHeap.value
        (termOwnerTargetsHeap_block_head
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [.value value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact hvalueHeap
  exact safeAbstraction_drops_of_runtimeDropFrame hsafe
    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
    hdropValuesHeap hdropFrame hdrops

/--
`R-Seq` runtime-abstraction preservation from the proof-carrying runtime
environment abstraction.

This is the semantic form intended to be threaded by preservation: it records
the concrete validity evidence for represented slots, so target-list widening
does not force us back to `ContainedBorrowsWellFormed`.
-/
theorem runtimeEnvAbstraction_seq_value_drop
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    RuntimeEnvAbstraction store env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    Drops store [.value value] store' →
    RuntimeEnvAbstraction store' env := by
  intro habstraction hvalidRuntime hdrops
  have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
    ValueOwnerTargetsHeap.partial
      (TermOwnerTargetsHeap.value
        (termOwnerTargetsHeap_block_head
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [.value value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact hvalueHeap
  have hdropOwnersOrphaned :
      ∀ owned, owned ∈ partialValuesOwningLocations [.value value] →
        ¬ ProgramStore.Owns store owned := by
    intro owned howned howns
    have hownedValue : owned ∈ valueOwningLocations value := by
      simpa [partialValuesOwningLocations, partialValueOwningLocations] using howned
    exact (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
      (by
        simp [termOwningLocations, termValues]
        exact Or.inl hownedValue)) howns
  exact RuntimeEnvAbstraction.drops_of_orphaned_values habstraction
    (ValidRuntimeState.validStore hvalidRuntime)
    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
    hdropValuesHeap hdropOwnersOrphaned hdrops

/-- `R-Seq` preserves the safe abstraction for the remaining sequence env. -/
theorem safeAbstraction_seq_value_drop_of_runtimeEnvAbstraction
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    RuntimeEnvAbstraction store env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    Drops store [.value value] store' →
    store' ∼ₛ env := by
  intro habstraction hvalidRuntime hdrops
  exact (runtimeEnvAbstraction_seq_value_drop habstraction hvalidRuntime hdrops).safe

/--
`R-Seq` safe-abstraction preservation from the semantic represented-slot
invariant.

This is the form that the preservation proof should ultimately consume once the
runtime invariant is threaded through executions.  The older well-formed wrapper
below is now only a producer of this invariant, via
`RuntimeRepresentedSlotsProtected.of_containedBorrowsWellFormed`.
-/
theorem safeAbstraction_seq_value_drop_of_representedSlotsProtected
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    store ∼ₛ env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    RuntimeRepresentedSlotsProtected store env →
    Drops store [.value value] store' →
    store' ∼ₛ env := by
  intro hsafe hvalidRuntime hprotected hdrops
  exact safeAbstraction_seq_value_drop_of_runtimeEnvAbstraction
    (RuntimeEnvAbstraction.of_representedSlotsProtected hsafe hprotected)
    hvalidRuntime hdrops

/-- `R-Seq` preserves the safe abstraction for the remaining sequence env. -/
theorem safeAbstraction_seq_value_drop
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    store ∼ₛ env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    WellFormedEnv env blockLifetime →
    Drops store [.value value] store' →
    store' ∼ₛ env := by
  intro hsafe hvalidRuntime hwellFormed hdrops
  exact safeAbstraction_seq_value_drop_of_runtimeEnvAbstraction
    (RuntimeEnvAbstraction.of_containedBorrowsWellFormed
      hwellFormed.1 hsafe
      (ValidRuntimeState.validStore hvalidRuntime)
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime))
    hvalidRuntime hdrops

/--
Shared run induction for the two while rules (`T-WhileDiv`, `T-While`): a
`WhileRunEnds` derivation that starts at the condition
phase, in a store abstracted by the loop's invariant environment `envInv`,
ends in a unit terminal state safe for the post-condition environment
`env₂`.

The rule-specific content enters through the two induction hypotheses,
which are the outer preservation IHs for the condition and body with their
environment bookkeeping already fixed.  `ihBody`'s last component
re-establishes the invariant once the body scope is dropped — via the back-edge
same-shape strengthening map for `T-While`, and vacuously for `T-WhileDiv`
(whose body never terminates, so `ihBody` is refuted by divergence).
-/
theorem preservation_whileRunEnds
    {lifetime bodyLifetime : Lifetime} {condition body : Term}
    {envInv env₂ env₃ : Env} {bodyTy : Ty}
    (hchild : LifetimeChild lifetime bodyLifetime)
    (hsourceCondition : SourceTerm condition)
    (hsourceBody : SourceTerm body)
    (ihCondition : ∀ store finalStore finalValue,
      ValidRuntimeState store condition →
      store ∼ₛ envInv →
      MultiStep store lifetime condition finalStore (.val finalValue) →
      WellFormedEnv env₂ lifetime ∧
        TerminalStateSafe finalStore finalValue env₂ .bool)
    (ihBody : ∀ store finalStore finalValue,
      ValidRuntimeState store body →
      WellFormedEnv env₂ bodyLifetime →
      store ∼ₛ env₂ →
      MultiStep store bodyLifetime body finalStore (.val finalValue) →
      WellFormedEnv env₃ bodyLifetime ∧
        TerminalStateSafe finalStore finalValue env₃ bodyTy ∧
        ∀ endStore : ProgramStore,
          endStore ∼ₛ env₃.dropLifetime bodyLifetime →
          endStore ∼ₛ envInv) :
    ∀ form startStore endStore,
      WhileRunEnds lifetime bodyLifetime condition body form
        startStore endStore →
      form = .whileCond bodyLifetime condition condition body →
      startStore ∼ₛ envInv →
      ValidRuntimeState startStore condition →
      WellFormedEnv env₂ lifetime ∧
        TerminalStateSafe endStore .unit env₂ .unit := by
  intro form startStore endStore hends
  induction hends with
  | exit =>
      rename_i hcond
      intro heq hsafe' hvalid'
      cases heq
      rcases ihCondition _ _ _ hvalid' hsafe' hcond with
        ⟨hwellCondition, hterminalCondition⟩
      exact ⟨hwellCondition,
        validRuntimeState_of_sourceTerm sourceTerm_unit_value
          hterminalCondition.1,
        hterminalCondition.2.1, ValidPartialValue.unit⟩
  | iterate =>
      rename_i hcond hblock _hrest ih
      intro heq hsafe' hvalid'
      cases heq
      rcases ihCondition _ _ _ hvalid' hsafe' hcond with
        ⟨hwellCondition, hterminalCondition⟩
      rcases multistep_block_head_to_value_inv hblock with
        ⟨midStore, bodyValue, hbodyRun, hblockCont⟩
      rcases ihBody _ _ _
          (validRuntimeState_of_sourceTerm hsourceBody
            hterminalCondition.1)
          (WellFormedEnv.of_outlives hwellCondition
            (LifetimeChild.outlives hchild))
          hterminalCondition.2.1 hbodyRun with
        ⟨hwellBody, hterminalBody, hinvariant⟩
      have hvalidConsBlock :
          ValidRuntimeState midStore
            (.block bodyLifetime [.val bodyValue, .val .unit]) :=
        validRuntimeState_block_value_cons_of_value_source_tail
          sourceTerm_unit_block hterminalBody.1
      have hterminalBodyRuntime :
          TerminalStateRuntimeSafe midStore bodyValue env₃ bodyTy :=
        TerminalStateRuntimeSafe.of_wellFormed hwellBody hterminalBody
      rcases preservation_block_terminal_multistep_runtime_of_first_step
          (env' := env₃.dropLifetime bodyLifetime) (ty := .unit)
          (by
            intro value next rest store₀ hterms hdrops htail
            cases hterms
            have hseqStep :
                Step midStore lifetime
                  (.block bodyLifetime [.val bodyValue, .val .unit])
                  store₀ (.block bodyLifetime [.val .unit]) :=
              Step.seq hdrops
            have hvalidAfterSeq :
                ValidRuntimeState store₀
                  (.block bodyLifetime [.val .unit]) :=
              validRuntimeState_seq_step hvalidConsBlock hseqStep
            have habstractionAfterSeq : RuntimeEnvAbstraction store₀ env₃ :=
              runtimeEnvAbstraction_seq_value_drop
                hterminalBodyRuntime.2.1 hvalidConsBlock hdrops
            have hsafeAfterSeq : store₀ ∼ₛ env₃ :=
              habstractionAfterSeq.safe
            exact preservation_blockB_value_multistep_runtime_of_runtimeDrop
              hvalidAfterSeq hsafeAfterSeq hchild hwellBody
              WellFormedTy.unit ValidPartialValue.unit htail)
          (by
            intro term rest store₀ term' hterms hstep htail
            cases hterms
            exact False.elim (value_no_step hstep))
          (by
            intro value store₀ hterms _hdropsL _htail
            simp at hterms)
          hblockCont with
        ⟨hvalidIterEnd, hsafeIterEnd, _hvalidValueIterEnd⟩
      exact ih rfl (hinvariant _ hsafeIterEnd)
        (validRuntimeState_of_sourceTerm hsourceCondition hvalidIterEnd)
  | bodyPhase =>
      intro heq hsafe' hvalid'
      cases heq

/-- Upgrade a terminal preservation conclusion to the runtime-abstraction form. -/
theorem terminalStateRuntimeSafe_of_terminal_typing
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    TerminalStateSafe finalStore finalValue env₂ ty →
    TerminalStateRuntimeSafe finalStore finalValue env₂ ty := by
  intro hsource hvalidRuntime hwellFormed hsafe htyping hterminal
  have hwellOut : WellFormedEnv env₂ lifetime :=
    (typingPreservesWellFormed_of_sourceTerm hsource
      (ValidRuntimeState.validState hvalidRuntime)
      hwellFormed hsafe htyping).1
  exact TerminalStateRuntimeSafe.of_wellFormed hwellOut hterminal

/-- Runtime-abstraction upgrade for the environment left by `R-BlockB`. -/
theorem terminalStateRuntimeSafe_dropLifetime_of_terminal
    {finalStore : ProgramStore} {env : Env}
    {lifetime blockLifetime : Lifetime} {finalValue : Value} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env blockLifetime →
    WellFormedTy env ty lifetime →
    TerminalStateSafe finalStore finalValue (env.dropLifetime blockLifetime) ty →
    TerminalStateRuntimeSafe finalStore finalValue
      (env.dropLifetime blockLifetime) ty := by
  intro hchild hwellBody hwellTy hterminal
  have hwellDropped : WellFormedEnv (env.dropLifetime blockLifetime) lifetime :=
    (Env.dropLifetime_preserves_wellFormed_child
      (env := env) (env' := env.dropLifetime blockLifetime)
      hchild hwellBody hwellTy rfl).1
  exact TerminalStateRuntimeSafe.of_wellFormed hwellDropped hterminal

/-- Runtime-abstraction variant of the block first-step dispatcher. -/
theorem preservation_block_terminal_runtimeSafe_of_first_step
    {store finalStore : ProgramStore} {env' : Env}
    {lifetime blockLifetime : Lifetime} {terms : List Term}
    {finalValue : Value} {ty : Ty} :
    (∀ value next rest store',
      terms = .val value :: next :: rest →
      Drops store [.value value] store' →
      MultiStep store' lifetime (.block blockLifetime (next :: rest))
        finalStore (.val finalValue) →
      TerminalStateRuntimeSafe finalStore finalValue env' ty) →
    (∀ term rest store' term',
      terms = term :: rest →
      Step store blockLifetime term store' term' →
      MultiStep store' lifetime (.block blockLifetime (term' :: rest))
        finalStore (.val finalValue) →
      TerminalStateRuntimeSafe finalStore finalValue env' ty) →
    (∀ value store',
      terms = [.val value] →
      DropsLifetime store blockLifetime store' →
      MultiStep store' lifetime (.val value) finalStore (.val finalValue) →
      TerminalStateRuntimeSafe finalStore finalValue env' ty) →
    MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
    TerminalStateRuntimeSafe finalStore finalValue env' ty := by
  intro hseq hblockA hblockB hmulti
  rcases multistep_block_to_value_first_step_inv hmulti with
    hseqCase | hblockACase | hblockBCase
  · rcases hseqCase with ⟨value, next, rest, store', hterms, hdrops, htail⟩
    exact hseq value next rest store' hterms hdrops htail
  · rcases hblockACase with ⟨term, rest, store', term', hterms, hstep, htail⟩
    exact hblockA term rest store' term' hterms hstep htail
  · rcases hblockBCase with ⟨value, store', hterms, hdrops, htail⟩
    exact hblockB value store' hterms hdrops htail

/--
Lemma 4.11, Preservation.

This is stated over `ValidRuntimeState`, the mechanised package that contains
Definition 4.3's valid-state condition plus the explicit owner-allocation
invariant needed by our concrete store model.
-/
theorem preservation_bounded (fuel : Nat) {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    term.size ≤ fuel →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateRuntimeSafe finalStore finalValue env₂ ty := by
  induction fuel generalizing store finalStore env₁ env₂ typing lifetime term ty
      finalValue with
  | zero =>
      intro hsize _hsource _hvalidRuntime _hvalidStoreTyping _hwellFormed
        _hborrowSafe _hsafe _htyping _hmulti
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
  intro hsize hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe
    htyping hmulti
  refine (TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      term.size ≤ fuel.succ →
      currentTyping = typing →
      SourceTerm term →
      ∀ (store finalStore : ProgramStore) (finalValue : Value),
        ValidRuntimeState store term →
        ValidStoreTyping store term currentTyping →
        WellFormedEnv env lifetime →
        BorrowSafeEnv env →
        store ∼ₛ env →
        MultiStep store lifetime term finalStore (.val finalValue) →
        TerminalStateRuntimeSafe finalStore finalValue env₂ ty)
    (motive_2 := fun env currentTyping blockLifetime terms ty env₂ _ =>
      Term.size (.block blockLifetime terms) ≤ fuel.succ →
      currentTyping = typing →
      SourceTerm (.block blockLifetime terms) →
      ∀ (outerLifetime : Lifetime) (store finalStore : ProgramStore)
        (finalValue : Value),
        LifetimeChild outerLifetime blockLifetime →
        ValidRuntimeState store (.block blockLifetime terms) →
        ValidStoreTyping store (.block blockLifetime terms) currentTyping →
        WellFormedEnv env blockLifetime →
        BorrowSafeEnv env →
        store ∼ₛ env →
        WellFormedTy env₂ ty outerLifetime →
        MultiStep store outerLifetime (.block blockLifetime terms)
          finalStore (.val finalValue) →
        TerminalStateRuntimeSafe finalStore finalValue
          (env₂.dropLifetime blockLifetime) ty)
    ?const ?missing ?copy ?move ?mutBorrow ?immBorrow ?box ?block
    ?declare ?assign ?eq ?ite ?iteDiverging
    ?whileLoopDiverging ?whileLoop ?singleton ?cons
    htyping hsize rfl hsource store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
    hborrowSafe hsafe hmulti)
  -- T-Val: a value is already terminal.
  case const =>
    intro _env _typing _lifetime _value _ty hvalueTyping _hsize htypingEq _hsource
      store finalStore finalValue hvalidRuntime hvalidStoreTyping _hwellFormed
      _hborrowSafe hsafe hmulti
    cases htypingEq
    have htermTyping : TermTyping _env typing _lifetime (.val _value) _ty _env :=
      TermTyping.const hvalueTyping
    have hterminal : TerminalStateSafe finalStore finalValue _env _ty :=
      preservation_multistep_runtime_value hvalidRuntime hvalidStoreTyping hsafe
        htermTyping hmulti
    exact TerminalStateRuntimeSafe.of_wellFormed _hwellFormed hterminal
  -- T-Missing: no run from `missing` reaches a value.
  case missing =>
    intro _env _typing _lifetime _ty _hwellTy _hloanFree _hsize _htypingEq hsource
      _store _finalStore _finalValue _hvalidRuntime _hvalidStoreTyping
      _hwellFormed _hborrowSafe _hsafe hmulti
    exact False.elim (multistep_missing_not_value hmulti)
  -- T-Copy
  case copy =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hcopy hnotRead
      _hsize htypingEq _hsource store finalStore finalValue hvalidRuntime
      hvalidStoreTyping _hwellFormed _hborrowSafe hsafe hmulti
    cases htypingEq
    have htermTyping : TermTyping _env typing _lifetime (.copy _lv) _ty _env :=
      TermTyping.copy hLv hcopy hnotRead
    have hterminal : TerminalStateSafe finalStore finalValue _env _ty :=
      preservation_copy_multistep_runtime_of_safe hsafe hvalidRuntime
        htermTyping hmulti
    exact TerminalStateRuntimeSafe.of_wellFormed _hwellFormed hterminal
  -- T-Move
  case move =>
    intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty hLv hnotWrite
      hmove _hsize htypingEq _hsource store finalStore finalValue hvalidRuntime
      hvalidStoreTyping hwellFormed _hborrowSafe hsafe hmulti
    cases htypingEq
    have htermTyping : TermTyping _env₁ typing _lifetime (.move _lv) _ty _env₂ :=
      TermTyping.move hLv hnotWrite hmove
    have hterminal : TerminalStateSafe finalStore finalValue _env₂ _ty :=
      by
        cases _lv with
        | var x =>
            rcases LValTyping.var_inv hLv with ⟨slot, hslot, htyEq, hlifetimeEq⟩
            cases slot with
            | mk slotTy slotLifetime =>
                cases htyEq
                cases hlifetimeEq
                exact preservation_move_var_multistep_runtime_of_wellFormed
                  hwellFormed hsafe hvalidRuntime hslot hmove htermTyping hmulti
          | deref lv =>
              cases hLv with
              | box hsourceBox =>
                  exact preservation_move_deref_box_multistep_runtime_of_wellFormed
                    hwellFormed hsafe hvalidRuntime hsourceBox hnotWrite hmove
                    htermTyping hmulti
              | borrow hsourceBorrow htargets =>
                  exact False.elim (by
                    rcases hmove with ⟨moveSlot, struck, hslot, hstrike, henv₂⟩
                    have hsourceSlot : _env₁.slotAt (LVal.base lv) = some moveSlot := by
                      simpa [LVal.base] using hslot
                    have hleaf :
                        WriteLeafTy _env₁ (LVal.path lv) moveSlot.ty Ty.unit :=
                      by
                        simpa using
                          (writeLeafTy_of_lvalTyping hsourceBorrow hsourceSlot []
                            Ty.unit WriteLeafTy.leaf)
                    exact WriteLeafTy.not_strike_deref hleaf
                      (by simpa [LVal.path_deref_cons] using hstrike))
    exact terminalStateRuntimeSafe_of_terminal_typing _hsource hvalidRuntime
      hwellFormed hsafe htermTyping hterminal
  -- T-MutBorrow
  case mutBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hmutable hnotWrite
      _hsize htypingEq _hsource store finalStore finalValue hvalidRuntime
      _hvalidStoreTyping _hwellFormed _hborrowSafe hsafe hmulti
    cases htypingEq
    have htermTyping :
        TermTyping _env typing _lifetime (.borrow true _lv) (.borrow true [_lv] _ty) _env :=
      TermTyping.mutBorrow hLv hmutable hnotWrite
    have hterminal : TerminalStateSafe finalStore finalValue _env (.borrow true [_lv] _ty) :=
      preservation_borrow_multistep_runtime hsafe hvalidRuntime htermTyping hmulti
    exact TerminalStateRuntimeSafe.of_wellFormed _hwellFormed hterminal
  -- T-ImmBorrow
  case immBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hnotRead _hsize htypingEq
      _hsource store finalStore finalValue hvalidRuntime _hvalidStoreTyping
      _hwellFormed _hborrowSafe hsafe hmulti
    cases htypingEq
    have htermTyping :
        TermTyping _env typing _lifetime (.borrow false _lv) (.borrow false [_lv] _ty) _env :=
      TermTyping.immBorrow hLv hnotRead
    have hterminal : TerminalStateSafe finalStore finalValue _env (.borrow false [_lv] _ty) :=
      preservation_borrow_multistep_runtime hsafe hvalidRuntime htermTyping hmulti
    exact TerminalStateRuntimeSafe.of_wellFormed _hwellFormed hterminal
  -- T-Box
  case box =>
    intro _env₁ _env₂ _typing _lifetime _term _ty hterm ih hsize htypingEq hsource
      store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
      hborrowSafe hsafe hmulti
    cases htypingEq
    have htermTyping : TermTyping _env₁ typing _lifetime (.box _term) (.box _ty) _env₂ :=
      TermTyping.box hterm
    have hterminal : TerminalStateSafe finalStore finalValue _env₂ (.box _ty) :=
      preservation_box_context_terminal_multistep_runtime
      (by
        intro midStore value hvalidInner hvalidStoreTypingInner hsafeInner
          _hinnerTyping hmultiInner
        exact (ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl (SourceTerm.box_inner hsource)
          store midStore value hvalidInner hvalidStoreTypingInner
          hwellFormed hborrowSafe hsafeInner hmultiInner).safe)
      hvalidRuntime hvalidStoreTyping hsafe htermTyping hmulti
    exact terminalStateRuntimeSafe_of_terminal_typing hsource hvalidRuntime
      hwellFormed hsafe htermTyping hterminal
  -- T-Block
  case block =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty
      hblockChild hterms hwellTy hdrop ih hsize htypingEq hsource store finalStore
      finalValue hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe
      hmulti
    cases htypingEq
    have htermTyping :
        TermTyping _env₁ typing _lifetime (.block _blockLifetime _terms) _ty _env₃ :=
      TermTyping.block hblockChild hterms hwellTy hdrop
    have hterminal : TerminalStateSafe finalStore finalValue _env₃ _ty :=
      by
        subst hdrop
        exact (ih hsize rfl hsource _lifetime store finalStore finalValue hblockChild
          hvalidRuntime hvalidStoreTyping
          (WellFormedEnv.weaken hwellFormed
            (LifetimeChild.outlives hblockChild))
          hborrowSafe hsafe hwellTy hmulti).safe
    exact terminalStateRuntimeSafe_of_terminal_typing hsource hvalidRuntime
      hwellFormed hsafe htermTyping hterminal
  -- T-LetMut
  case declare =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty hfresh hterm
      hfreshOut _hcoh henv₃ ih hsize htypingEq hsource store finalStore finalValue
      hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe hmulti
    cases htypingEq
    have htermTyping :
        TermTyping _env₁ typing _lifetime (.letMut _x _term) .unit _env₃ :=
      TermTyping.declare hfresh hterm hfreshOut _hcoh henv₃
    rcases multistep_declare_to_value_inv hmulti with
      ⟨midStore, value, hinnerMulti, hdeclareStep⟩
    rcases ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl (SourceTerm.declare_inner hsource) store midStore value
        (validRuntimeState_declare_inner hvalidRuntime)
        (validStoreTyping_declare_inner hvalidStoreTyping)
        hwellFormed hborrowSafe hsafe hinnerMulti with
      hterminalInner
    rcases hterminalInner with
      ⟨hvalidInner, hsafeInner, hvalidValue⟩
    cases hdeclareStep with
    | declare hstore =>
        have hpreserved :=
          preservation_declare_redex_runtime_of_validValue hsafeInner.safe
            hfreshOut
            (validRuntimeState_declare_value_of_value hvalidInner)
            hvalidValue
            (Step.declare (lifetime := _lifetime) hstore)
        have hterminal : TerminalStateSafe finalStore .unit _env₃ .unit := by
          rw [henv₃]
          exact hpreserved
        exact terminalStateRuntimeSafe_of_terminal_typing hsource hvalidRuntime
          hwellFormed hsafe htermTyping hterminal
  -- T-Assign
  case assign =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs
      _rhsTy hRhs hLhsPost hshape hwellTy hwrite hranked hcoh hcontained
      hnotWrite _ih hsize htypingEq hsource store finalStore finalValue
      hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe hmulti
    cases htypingEq
    rcases multistep_assign_to_value_inv hmulti with
      ⟨midStore, value, hinnerMulti, hassignStep⟩
    rcases _ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl (SourceTerm.assign_inner hsource) store midStore value
        (validRuntimeState_assign_inner hvalidRuntime)
        (validStoreTyping_assign_inner hvalidStoreTyping)
        hwellFormed hborrowSafe hsafe hinnerMulti with
      hterminalInner
    rcases hterminalInner with
      ⟨hvalidInner, hsafeInner, hvalidValue⟩
    have hwellInner : WellFormedEnv _env₂ _lifetime :=
      (typingPreservesWellFormed_of_sourceTerm
        (SourceTerm.assign_inner hsource)
        (ValidRuntimeState.validState
          (validRuntimeState_assign_inner hvalidRuntime))
        hwellFormed hsafe hRhs).1
    have hborrowSafeInner : BorrowSafeEnv _env₂ :=
      (typingPreservesBorrowSafeCore
        (SourceTerm.assign_inner hsource) hborrowSafe hRhs).1
    cases _lhs with
    | var x =>
        cases hshape with
        | unit =>
            exact preservation_assign_var_envShape_redex_runtime_of_runtimeEnvAbstraction
              hwellInner hsafeInner
              (validRuntimeState_assign_value_of_value hvalidInner)
              hLhsPost hwrite
              (by
                intro envSlot henvSlot
                rcases LValTyping.var_inv hLhsPost with
                  ⟨lhsSlot, hlhsSlot, hty, _hlifetime⟩
                have hslotEq : envSlot = lhsSlot := by
                  rw [hlhsSlot] at henvSlot
                  exact (Option.some.inj henvSlot).symm
                subst hslotEq
                exact Or.inl hty)
              hwellTy hnotWrite hvalidValue hassignStep
        | int =>
            exact preservation_assign_var_envShape_redex_runtime_of_runtimeEnvAbstraction
              hwellInner hsafeInner
              (validRuntimeState_assign_value_of_value hvalidInner)
              hLhsPost hwrite
              (by
                intro envSlot henvSlot
                rcases LValTyping.var_inv hLhsPost with
                  ⟨lhsSlot, hlhsSlot, hty, _hlifetime⟩
                have hslotEq : envSlot = lhsSlot := by
                  rw [hlhsSlot] at henvSlot
                  exact (Option.some.inj henvSlot).symm
                subst hslotEq
                exact Or.inr (Or.inl hty))
              hwellTy hnotWrite hvalidValue hassignStep
        | bool =>
            exact preservation_assign_var_envShape_redex_runtime_of_runtimeEnvAbstraction
              hwellInner hsafeInner
              (validRuntimeState_assign_value_of_value hvalidInner)
              hLhsPost hwrite
              (by
                intro envSlot henvSlot
                rcases LValTyping.var_inv hLhsPost with
                  ⟨lhsSlot, hlhsSlot, hty, _hlifetime⟩
                have hslotEq : envSlot = lhsSlot := by
                  rw [hlhsSlot] at henvSlot
                  exact (Option.some.inj henvSlot).symm
                subst hslotEq
                exact Or.inr (Or.inr (Or.inl hty)))
              hwellTy hnotWrite hvalidValue hassignStep
        | borrow hinner =>
            exact preservation_assign_var_envShape_redex_runtime_of_runtimeEnvAbstraction
              hwellInner hsafeInner
              (validRuntimeState_assign_value_of_value hvalidInner)
              hLhsPost hwrite
              (by
                intro envSlot henvSlot
                rcases LValTyping.var_inv hLhsPost with
                  ⟨lhsSlot, hlhsSlot, hty, _hlifetime⟩
                have hslotEq : envSlot = lhsSlot := by
                  rw [hlhsSlot] at henvSlot
                  exact (Option.some.inj henvSlot).symm
                subst hslotEq
                exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, hty⟩))))
              hwellTy hnotWrite hvalidValue hassignStep
        | undefLeft hinner =>
            exact preservation_assign_var_envShape_redex_runtime_of_runtimeEnvAbstraction
              hwellInner hsafeInner
              (validRuntimeState_assign_value_of_value hvalidInner)
              hLhsPost hwrite
              (by
                intro envSlot henvSlot
                rcases LValTyping.var_inv hLhsPost with
                  ⟨lhsSlot, hlhsSlot, hty, _hlifetime⟩
                have hslotEq : envSlot = lhsSlot := by
                  rw [hlhsSlot] at henvSlot
                  exact (Option.some.inj henvSlot).symm
                subst hslotEq
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hty⟩))))
              hwellTy hnotWrite hvalidValue hassignStep
        | tyBox hinnerShape =>
            exact preservation_assign_var_box_redex_runtime_of_runtimeEnvAbstraction
              hwellInner hsafeInner
              (validRuntimeState_assign_value_of_value hvalidInner)
              hLhsPost hinnerShape hwellTy hwrite hnotWrite hvalidValue
              hassignStep
    | deref source =>
        cases hLhsPost with
        | box hsourceBox =>
            exact preservation_assign_deref_box_step_runtime_of_runtimeEnvAbstraction
              hwellInner hborrowSafeInner hsafeInner
              (validRuntimeState_assign_value_of_value hvalidInner)
              hsourceBox hshape hwellTy hwrite hranked hnotWrite hvalidValue
              hassignStep
        | borrow hsourceBorrow htargets =>
            exact preservation_assign_deref_borrow_step_runtime_of_runtimeEnvAbstraction
              hwellInner hborrowSafeInner hsafeInner
              (validRuntimeState_assign_value_of_value hvalidInner)
              hsourceBorrow htargets hshape hwellTy hwrite hranked hnotWrite
              hvalidValue hassignStep
  -- T-Eq
  case eq =>
    intro _env₁ _env₂ _env₃ _envGhost _ghost _typing _lifetime _lhs _rhs
      _lhsTy _rhsTy _hLhs hfresh htypeFresh htyFresh hstoreFresh hghostRhs
      hnotMention henvEq _hcopyL _hcopyR _hshape ihL _ihGhost hsize htypingEq hsource store
      finalStore finalValue
      hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe hmulti
    cases htypingEq
    have hRhs : TermTyping _env₂ typing _lifetime _rhs _rhsTy
        (_envGhost.erase _ghost) :=
      TermTyping.erase_ghost
        (env := _env₂)
        (ghostSlot := { ty := .ty _lhsTy, lifetime := _lifetime })
        hfresh htypeFresh (by
          intro hmem
          exact htyFresh (Ty.vars_subset_allVars (ty := _lhsTy) hmem))
        hstoreFresh hnotMention hghostRhs
    rcases multistep_eq_to_value_inv hmulti with
      ⟨midStore, leftValue, rightStore, rightValue, hleftMulti, hrightMulti,
        hredex⟩
    have hsourceLeft : SourceTerm _lhs :=
      SourceTerm.eq_lhs hsource
    have hsourceRight : SourceTerm _rhs :=
      SourceTerm.eq_rhs hsource
    have hvalidLeft : ValidRuntimeState store _lhs :=
      validRuntimeState_of_sourceTerm hsourceLeft hvalidRuntime
    rcases ihL (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl hsourceLeft store midStore leftValue hvalidLeft
        hvalidStoreTyping.eq_lhs hwellFormed hborrowSafe hsafe hleftMulti with
      hterminalLeft
    have hwellLeft : WellFormedEnv _env₂ _lifetime :=
      (typingPreservesWellFormed_of_sourceTerm hsourceLeft
        (ValidRuntimeState.validState hvalidLeft)
        hwellFormed hsafe _hLhs).1
    have hborrowSafeLeft : BorrowSafeEnv _env₂ :=
      (typingPreservesBorrowSafeCore hsourceLeft hborrowSafe _hLhs).1
    have hvalidRight : ValidRuntimeState midStore _rhs :=
      validRuntimeState_of_sourceTerm hsourceRight hterminalLeft.1
    have hstoreTypingRight : ValidStoreTyping midStore _rhs typing :=
      validStoreTyping_sourceTerm_of_validStoreTyping hsourceRight
        hvalidStoreTyping.eq_rhs
    have hterminalRight :
        TerminalStateRuntimeSafe rightStore rightValue (_envGhost.erase _ghost) _rhsTy :=
      ihFuel
        (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        hsourceRight hvalidRight hstoreTypingRight hwellLeft
        hborrowSafeLeft hterminalLeft.2.1.safe hRhs hrightMulti
    cases hredex with
    | eqTrue =>
        exact ⟨validRuntimeState_of_sourceTerm (sourceTerm_bool_value true)
            hterminalRight.1,
          by simpa [henvEq] using hterminalRight.2.1,
          ValidPartialValue.bool⟩
    | eqFalse _hne =>
        exact ⟨validRuntimeState_of_sourceTerm (sourceTerm_bool_value false)
            hterminalRight.1,
          by simpa [henvEq] using hterminalRight.2.1,
          ValidPartialValue.bool⟩
  -- T-IfJoin: run the chosen branch's IH, then transport its
  -- terminal state into the join environment.
  case ite =>
    intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
      _trueBranch _falseBranch _trueTy _falseTy _joinTy _hcondition _htrue
      _hfalse hjoin henvJoin hsameLeft hsameRight _hwellJoin
      _hcoherent _hlinear _hborrowSafeJoin _hresultSafe ihCondition ihTrue
      ihFalse hsize htypingEq hsource store finalStore finalValue hvalidRuntime
      hvalidStoreTyping hwellFormed hborrowSafe hsafe hmulti
    cases htypingEq
    rcases multistep_ite_to_value_inv hmulti with
      ⟨midStore, hchosen⟩
    have hsourceCondition : SourceTerm _condition :=
      SourceTerm.ite_condition hsource
    have hvalidCondition : ValidRuntimeState store _condition :=
      validRuntimeState_of_sourceTerm hsourceCondition hvalidRuntime
    have hstoreTypingCondition : ValidStoreTyping store _condition typing :=
      hvalidStoreTyping.ite_condition
    have hborrowSafeCondition : BorrowSafeEnv _env₂ :=
      (typingPreservesBorrowSafeCore hsourceCondition hborrowSafe
        _hcondition).1
    rcases hchosen with htrueChosen | hfalseChosen
    · rcases htrueChosen with ⟨_hconditionMulti, htrueMulti⟩
      rcases ihCondition (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceCondition store midStore (.bool true)
          hvalidCondition hstoreTypingCondition hwellFormed hborrowSafe hsafe
          _hconditionMulti with
        hterminalCondition
      have hwellCondition : WellFormedEnv _env₂ _lifetime :=
        (typingPreservesWellFormed_of_sourceTerm hsourceCondition
          (ValidRuntimeState.validState hvalidCondition)
          hwellFormed hsafe _hcondition).1
      have hsourceTrue : SourceTerm _trueBranch :=
        SourceTerm.ite_trueBranch hsource
      have hvalidTrue : ValidRuntimeState midStore _trueBranch :=
        validRuntimeState_of_sourceTerm hsourceTrue hterminalCondition.1
      have hstoreTypingTrue : ValidStoreTyping midStore _trueBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
          hvalidStoreTyping.ite_trueBranch
      rcases ihTrue (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceTrue midStore finalStore finalValue hvalidTrue
          hstoreTypingTrue hwellCondition hborrowSafeCondition
          hterminalCondition.2.1.safe htrueMulti with
        hterminalTrue
      have hterminalJoin :
          TerminalStateRuntimeSafe finalStore finalValue _env₅ _joinTy :=
        TerminalStateRuntimeSafe.strengthen_join_runtime_left
          henvJoin hsameLeft hjoin hterminalTrue
      exact hterminalJoin
    · rcases hfalseChosen with ⟨_hconditionMulti, hfalseMulti⟩
      rcases ihCondition (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceCondition store midStore (.bool false)
          hvalidCondition hstoreTypingCondition hwellFormed hborrowSafe hsafe
          _hconditionMulti with
        hterminalCondition
      have hwellCondition : WellFormedEnv _env₂ _lifetime :=
        (typingPreservesWellFormed_of_sourceTerm hsourceCondition
          (ValidRuntimeState.validState hvalidCondition)
          hwellFormed hsafe _hcondition).1
      have hsourceFalse : SourceTerm _falseBranch :=
        SourceTerm.ite_falseBranch hsource
      have hvalidFalse : ValidRuntimeState midStore _falseBranch :=
        validRuntimeState_of_sourceTerm hsourceFalse hterminalCondition.1
      have hstoreTypingFalse : ValidStoreTyping midStore _falseBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceFalse
          hvalidStoreTyping.ite_falseBranch
      rcases ihFalse (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceFalse midStore finalStore finalValue hvalidFalse
          hstoreTypingFalse hwellCondition hborrowSafeCondition
          hterminalCondition.2.1.safe hfalseMulti with
        hterminalFalse
      have hterminalJoin :
          TerminalStateRuntimeSafe finalStore finalValue _env₅ _joinTy :=
        TerminalStateRuntimeSafe.strengthen_join_runtime_right
          henvJoin hsameRight hjoin hterminalFalse
      exact hterminalJoin
  -- T-IfDiv: only the true branch can terminate.
  case iteDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition _trueBranch
      _falseBranch _trueTy _falseTy _hcondition _htrue _hfalse hdiverges
      ihCondition ihTrue _ihFalse hsize htypingEq hsource store finalStore
      finalValue hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe
      hmulti
    cases htypingEq
    rcases multistep_ite_to_value_inv hmulti with
      ⟨midStore, hchosen⟩
    have hsourceCondition : SourceTerm _condition :=
      SourceTerm.ite_condition hsource
    have hvalidCondition : ValidRuntimeState store _condition :=
      validRuntimeState_of_sourceTerm hsourceCondition hvalidRuntime
    have hstoreTypingCondition : ValidStoreTyping store _condition typing :=
      hvalidStoreTyping.ite_condition
    have hborrowSafeCondition : BorrowSafeEnv _env₂ :=
      (typingPreservesBorrowSafeCore hsourceCondition hborrowSafe
        _hcondition).1
    rcases hchosen with htrueChosen | hfalseChosen
    · rcases htrueChosen with ⟨_hconditionMulti, htrueMulti⟩
      rcases ihCondition (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceCondition store midStore (.bool true)
          hvalidCondition hstoreTypingCondition hwellFormed hborrowSafe hsafe
          _hconditionMulti with
        hterminalCondition
      have hwellCondition : WellFormedEnv _env₂ _lifetime :=
        (typingPreservesWellFormed_of_sourceTerm hsourceCondition
          (ValidRuntimeState.validState hvalidCondition)
          hwellFormed hsafe _hcondition).1
      have hsourceTrue : SourceTerm _trueBranch :=
        SourceTerm.ite_trueBranch hsource
      have hvalidTrue : ValidRuntimeState midStore _trueBranch :=
        validRuntimeState_of_sourceTerm hsourceTrue hterminalCondition.1
      have hstoreTypingTrue : ValidStoreTyping midStore _trueBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
          hvalidStoreTyping.ite_trueBranch
      exact ihTrue (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl hsourceTrue midStore finalStore finalValue hvalidTrue
        hstoreTypingTrue hwellCondition hborrowSafeCondition
        hterminalCondition.2.1.safe htrueMulti
    · rcases hfalseChosen with ⟨_hconditionMulti, hfalseMulti⟩
      exact absurd hfalseMulti (diverges_multistep_not_value hdiverges)
  -- T-WhileDiv: the diverging body never completes an iteration, so the
  -- run can only exit through a false condition; the body IH of the shared
  -- run induction is refuted by divergence.
  case whileLoopDiverging =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition _body
      _bodyTy hchild _hcondition _hbody hdiverges ihCondition _ihBody
      hsize htypingEq hsource store finalStore finalValue hvalidRuntime
      hvalidStoreTyping hwellFormed hborrowSafe hsafe hmulti
    cases htypingEq
    have hsourceCondition : SourceTerm _condition :=
      SourceTerm.while_condition hsource
    rcases multistep_first_step_of_not_terminal (by simp [Terminal])
        hmulti with ⟨store', term', hstep, hrest⟩
    cases hstep
    obtain ⟨hvalue, hends⟩ :=
      multistep_while_form_to_value_inv hrest (WhileForm.cond _)
    subst hvalue
    have hwhile :=
      preservation_whileRunEnds (env₃ := _env₃) (bodyTy := _bodyTy)
        hchild hsourceCondition (SourceTerm.while_body hsource)
        (fun s fs fv hvalid hsafe' hm =>
          have hterminal :=
            ihCondition (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
              rfl hsourceCondition s fs fv hvalid
              (validStoreTyping_sourceTerm_of_validStoreTyping
                hsourceCondition hvalidStoreTyping.while_condition)
              hwellFormed hborrowSafe hsafe' hm
          ⟨(typingPreservesWellFormed_of_sourceTerm hsourceCondition
              (ValidRuntimeState.validState hvalid)
              hwellFormed hsafe' _hcondition).1, hterminal.safe⟩)
        (fun s fs fv _hvalid _hwf _hsafe' hm =>
          absurd hm (diverges_multistep_not_value hdiverges))
        _ _ _ hends rfl hsafe
        (validRuntimeState_of_sourceTerm hsourceCondition hvalidRuntime)
    exact TerminalStateRuntimeSafe.of_wellFormed hwhile.1 hwhile.2
  -- T-While: like the strict case, but the shared run induction
  -- carries `∼ₛ envInv`; the entry and back-edge states transport into the
  -- invariant via the same-shape strengthening maps (the T-If pattern).
  case whileLoop =>
    intro _env₁ _envBack _envInv _env₂ _envEntry₂ _env₃ _envEntry₃ _typing
      _lifetime _bodyLifetime _condition _body _bodyTy _bodyEntryTy hchild
      hjoin hss1 hss2 hcbwf hcoh hlin hbse _hnameFresh _hcondInv _hbodyInv _hwellTyBody
      hdropEq _hcondEntry _hbodyEntry ihCondInv ihBodyInv _ihCondEntry
      _ihBodyEntry
      hsize htypingEq hsource store finalStore finalValue hvalidRuntime
      hvalidStoreTyping hwellFormed hborrowSafe hsafe hmulti
    cases htypingEq
    have hsourceCondition : SourceTerm _condition :=
      SourceTerm.while_condition hsource
    have hsourceBody : SourceTerm _body :=
      SourceTerm.while_body hsource
    have hentryMap : EnvSameShapeStrengthening _env₁ _envInv :=
      EnvJoin.left_sameShapeStrengthening_of_sameShape hjoin hss1
    have hbackMap : EnvSameShapeStrengthening _envBack _envInv :=
      EnvJoin.right_sameShapeStrengthening_of_sameShape hjoin hss2
    have hwfInv : WellFormedEnv _envInv _lifetime :=
      ⟨hcbwf,
        EnvSlotsOutlive.of_lifetimesPreserved hwellFormed.2.1
          (EnvJoin.lifetimesPreserved_left hjoin),
        hcoh, hlin⟩
    have hbseCondition : BorrowSafeEnv _env₂ :=
      (typingPreservesBorrowSafeCore hsourceCondition hbse
        _hcondInv).1
    rcases multistep_first_step_of_not_terminal (by simp [Terminal])
        hmulti with ⟨store', term', hstep, hrest⟩
    cases hstep
    obtain ⟨hvalue, hends⟩ :=
      multistep_while_form_to_value_inv hrest (WhileForm.cond _)
    subst hvalue
    have hwhile :=
      preservation_whileRunEnds hchild hsourceCondition hsourceBody
        (fun s fs fv hvalid hsafe' hm =>
          have hterminal :=
            ihCondInv (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
              rfl hsourceCondition s fs fv hvalid
              (validStoreTyping_sourceTerm_of_validStoreTyping
                hsourceCondition hvalidStoreTyping.while_condition)
              hwfInv hbse hsafe' hm
          ⟨(typingPreservesWellFormed_of_sourceTerm hsourceCondition
              (ValidRuntimeState.validState hvalid)
              hwfInv hsafe' _hcondInv).1, hterminal.safe⟩)
        (fun s fs fv hvalid hwf hsafe' hm => by
          have hterm :=
            ihBodyInv (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
              rfl hsourceBody s fs fv hvalid
              (validStoreTyping_sourceTerm_of_validStoreTyping hsourceBody
                hvalidStoreTyping.while_body)
              hwf hbseCondition hsafe' hm
          have hwell : WellFormedEnv _env₃ _bodyLifetime :=
            (typingPreservesWellFormed_of_sourceTerm hsourceBody
              (ValidRuntimeState.validState hvalid)
              hwf hsafe' _hbodyInv).1
          exact ⟨hwell, hterm.safe,
            fun endStore h => hbackMap.safe (hdropEq ▸ h)⟩)
        _ _ _ hends rfl (hentryMap.safe hsafe)
        (validRuntimeState_of_sourceTerm hsourceCondition hvalidRuntime)
    exact TerminalStateRuntimeSafe.of_wellFormed hwhile.1 hwhile.2
  -- Block list, singleton case.
  case singleton =>
    intro _env₁ _env₂ _typing _lifetime _term _ty _hterm _ih hsize htypingEq hsource
      outerLifetime store finalStore finalValue hchild hvalidRuntime
      hvalidStoreTyping hwellFormed hborrowSafe hsafe hwellTy hmulti
    cases htypingEq
    rcases multistep_block_head_to_value_inv hmulti with
      ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
    rcases _ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl (SourceTerm.block_head hsource) store midStore value
        (validRuntimeState_block_singleton_inner hvalidRuntime)
        (validStoreTyping_block_singleton_inner hvalidStoreTyping)
        hwellFormed hborrowSafe hsafe hinnerMulti with
      hterminalInner
    have hwellInner : WellFormedEnv _env₂ _lifetime :=
      (typingPreservesWellFormed_of_sourceTerm
        (SourceTerm.block_head hsource)
        (ValidRuntimeState.validState
          (validRuntimeState_block_singleton_inner hvalidRuntime))
        hwellFormed hsafe _hterm).1
    have hterminal : TerminalStateSafe finalStore finalValue
        (_env₂.dropLifetime _lifetime) _ty :=
      preservation_blockB_value_multistep_runtime_of_runtimeDrop
        (validRuntimeState_block_singleton_value_of_value hterminalInner.1)
        hterminalInner.2.1.safe hchild hwellInner hwellTy
        hterminalInner.2.2 hblockValueMulti
    exact terminalStateRuntimeSafe_dropLifetime_of_terminal
      hchild hwellInner hwellTy hterminal
  -- Block list, cons case.
  case cons =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
      _hterm hrest _ihHead _ihRest hsize htypingEq hsource outerLifetime store
      finalStore finalValue hchild hvalidRuntime hvalidStoreTyping hwellFormed
      hborrowSafe hsafe hwellTy hmulti
    cases htypingEq
    cases _rest with
    | nil =>
        cases hrest
    | cons next restTail =>
        have hsourceHead : SourceTerm _term :=
          SourceTerm.block_head hsource
        have hsourceTail : SourceTerm (.block _lifetime (next :: restTail)) :=
          SourceTerm.block_tail hsource
        rcases multistep_block_head_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
        rcases _ihHead (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            rfl hsourceHead store midStore value
            (validRuntimeState_block_head hvalidRuntime)
            (validStoreTyping_block_head hvalidStoreTyping)
            hwellFormed hborrowSafe hsafe hinnerMulti with
          hterminalInner
        have hwellInner : WellFormedEnv _env₂ _lifetime :=
          (typingPreservesWellFormed_of_sourceTerm hsourceHead
            (ValidRuntimeState.validState
              (validRuntimeState_block_head hvalidRuntime))
            hwellFormed hsafe _hterm).1
        have hborrowSafeInner : BorrowSafeEnv _env₂ :=
          (typingPreservesBorrowSafeCore hsourceHead hborrowSafe
            _hterm).1
        have hvalueBlockValid :
            ValidRuntimeState midStore
              (.block _lifetime (.val value :: next :: restTail)) :=
          validRuntimeState_block_value_cons_of_value_source_tail
            hsourceTail hterminalInner.1
        have htailStoreTypingAtMid :
            ValidStoreTyping midStore (.block _lifetime (next :: restTail)) typing :=
          validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
            (validStoreTyping_block_tail_of_cons hvalidStoreTyping)
        exact preservation_block_terminal_runtimeSafe_of_first_step
          (env' := _env₃.dropLifetime _lifetime) (ty := _finalTy)
          (by
            intro seqValue seqNext seqRest storeAfter hterms hdrops htailMulti
            cases hterms
            have hseqStep :
                Step midStore outerLifetime
                  (.block _lifetime (.val value :: next :: restTail))
                  storeAfter (.block _lifetime (next :: restTail)) :=
              Step.seq hdrops
            have hvalidTailAfter :
                ValidRuntimeState storeAfter
                  (.block _lifetime (next :: restTail)) :=
              validRuntimeState_seq_step hvalueBlockValid hseqStep
            have hsafeTailAfter : storeAfter ∼ₛ _env₂ :=
              safeAbstraction_seq_value_drop_of_runtimeEnvAbstraction
                hterminalInner.2.1 hvalueBlockValid hdrops
            have htailStoreTyping :
                ValidStoreTyping storeAfter
                  (.block _lifetime (next :: restTail)) typing :=
              validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
                htailStoreTypingAtMid
            exact _ihRest
              (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
              rfl hsourceTail outerLifetime storeAfter finalStore
              finalValue hchild hvalidTailAfter htailStoreTyping hwellInner
              hborrowSafeInner hsafeTailAfter hwellTy htailMulti)
          (by
            intro blockTerm blockRest storeAfter termAfter hterms hstep _htailMulti
            cases hterms
            exact False.elim (value_no_step hstep))
          (by
            intro blockValue storeAfter hterms _hdrops _htailMulti
            cases hterms)
          hblockValueMulti

theorem preservation {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe
    htyping hmulti
  exact (preservation_bounded term.size (Nat.le_refl _) hsource hvalidRuntime
    hvalidStoreTyping hwellFormed hborrowSafe hsafe htyping hmulti).safe

/--
Preservation with the proof-carrying runtime abstraction in the terminal
conclusion.

This is the recursive preservation invariant: the terminal state carries the
runtime environment abstraction, not just its `SafeAbstraction` projection.
-/
theorem preservation_runtime {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateRuntimeSafe finalStore finalValue env₂ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe
    htyping hmulti
  exact preservation_bounded term.size (Nat.le_refl _) hsource hvalidRuntime
    hvalidStoreTyping hwellFormed hborrowSafe hsafe htyping hmulti

/--
Preservation packaged as the runtime-facing environment invariant.

The terminal runtime-safety proof supplies `RuntimeEnvAbstraction` for the final
store/environment pair; slot outliving is the independent part of typing
preservation that does not require the full static borrow/coherence package of
the output environment.
-/
theorem preservation_runtimeInvariant {store finalStore : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateRuntimeSafe finalStore finalValue env₂ ty ∧
      RuntimeEnvInvariant finalStore env₂ lifetime := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe
    htyping hmulti
  have hterminal :=
    preservation_runtime hsource hvalidRuntime hvalidStoreTyping hwellFormed
      hborrowSafe hsafe htyping hmulti
  have hslots : EnvSlotsOutlive env₂ lifetime :=
    typingPreservesSlotsOutlive hwellFormed.2.1 htyping
  exact ⟨hterminal, hterminal.2.1, hslots⟩

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Lemma 4.11, Preservation. -/
theorem lemma_4_11_preservation
    {store finalStore : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    TerminalStateSafe finalStore finalValue env₂ ty :=
  preservation hsource hvalid hstoreTyping hwellFormed hborrowSafe hsafe
    htyping hmulti

/-- Lemma 4.11 runtime-abstraction strengthening. -/
theorem lemma_4_11_preservation_runtime
    {store finalStore : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    TerminalStateRuntimeSafe finalStore finalValue env₂ ty :=
  preservation_runtime hsource hvalid hstoreTyping hwellFormed hborrowSafe hsafe
    htyping hmulti

/-- Lemma 4.11 runtime-invariant strengthening. -/
theorem lemma_4_11_preservation_runtimeInvariant
    {store finalStore : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    TerminalStateRuntimeSafe finalStore finalValue env₂ ty ∧
      RuntimeEnvInvariant finalStore env₂ lifetime :=
  preservation_runtimeInvariant hsource hvalid hstoreTyping hwellFormed hborrowSafe
    hsafe htyping hmulti

end LwRust.Paper.Soundness
