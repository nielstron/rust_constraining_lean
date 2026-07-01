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
  | undefOf {value : PartialValue} {oldTy : PartialTy} {ty : Ty}
      {ℓ : Location} :
      ValidPartialValueSkeleton store value oldTy →
      PartialTyStrengthens oldTy (.undef ty) →
      RuntimeFrame.OwnerReaches store value oldTy ℓ →
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
  | borrow {location ℓ : Location} {mutable : Bool} {targets : List LVal} {target : LVal} :
      target ∈ targets →
      store.loc target = some location →
      LocReads store target ℓ →
      Reaches store (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets)) ℓ

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
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValue.undefOf
        (RuntimeFrame.validPartialValueSkeleton_update_of_not_owner_reaches
          hinner
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
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValue.undefOf
        (RuntimeFrame.validPartialValueSkeleton_erase_of_not_owner_reaches
          hinner
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
  | undefOf hvalid hstrength hinner =>
      exact Reaches.undefOf
        (RuntimeFrame.validPartialValueSkeleton_erase_to_store hvalid)
        hstrength
        (RuntimeFrame.ownerReaches_erase_to_store hinner)
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
  intro hφ hwellFormed hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      store.loc lv = some (VariableProjection x) →
      φ x ≤ φ (LVal.base lv))
    (motive_2 := fun targets partialTy lifetime _ =>
      (∀ target, target ∈ targets →
        store.loc target = some (VariableProjection x) →
        φ x ≤ φ (LVal.base target)))
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro y slot _hslot hloc
    simp [ProgramStore.loc, VariableProjection] at hloc
    cases hloc
    exact Nat.le_refl _
  · intro source inner sourceLifetime hsource _ih hloc
    have hsourceAbs : LValLocationAbstraction store source (.box inner) :=
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
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          exact ⟨sourceLocation, sourceSlotLifetime, by
            simpa [owningRef] using hsourceSlot⟩
        exact False.elim ((not_owns_var_of_storeOwnerTargetsHeap hheap) howns)
  · intro source inner sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstraction store source (.ty (.box inner)) :=
      lvalTyping_defined_location hwellFormed hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
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
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets _ihSource ihTargets hloc
    have hsourceAbs :
        LValLocationAbstraction store source (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location hwellFormed hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrow selectedLocation _mutable _targets selected hmem hselectedLoc =>
        have hderefLoc : store.loc source.deref = some selectedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hselectedLocationEq : selectedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        subst hselectedLocationEq
        have hxLeSelected : φ x ≤ φ (LVal.base selected) :=
          ihTargets selected hmem hselectedLoc
        have hselectedMemVars :
            LVal.base selected ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
          exact mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, selected, PartialTyContains.here, hmem, rfl⟩
        have hselectedLtSource :
            φ (LVal.base selected) < φ (LVal.base source) :=
          (lvalTyping_vars_rank_lt hφ).1 hsource
            (LVal.base selected) hselectedMemVars
        exact le_trans hxLeSelected (Nat.le_of_lt hselectedLtSource)
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

/--
If resolving a typed lvalue reads variable `x`, then `x` is no higher-ranked
than the lvalue's syntactic base.  This is the read-dependency analogue of
`lval_loc_var_rank_le_base`.
-/
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
  intro hφ hwellFormed hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _pt _lifetime _ =>
      RuntimeFrame.LocReads store lv (VariableProjection x) →
      φ x ≤ φ (LVal.base lv))
    (motive_2 := fun _targets _pt _lifetime _ => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro _y _slot _hslot hreads
    cases hreads
  · intro source inner sourceLifetime hsource ih hreads
    cases hreads with
    | here hsourceLoc =>
        simpa [LVal.base] using
          lval_loc_var_rank_le_base hφ hwellFormed hsafe hheap
            hsource hsourceLoc
    | there hsourceReads =>
        simpa [LVal.base] using ih hsourceReads
  · intro source inner sourceLifetime hsource ih hreads
    cases hreads with
    | here hsourceLoc =>
        simpa [LVal.base] using
          lval_loc_var_rank_le_base hφ hwellFormed hsafe hheap
            hsource hsourceLoc
    | there hsourceReads =>
        simpa [LVal.base] using ih hsourceReads
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource _htargets ihSource _ihTargets hreads
    cases hreads with
    | here hsourceLoc =>
        simpa [LVal.base] using
          lval_loc_var_rank_le_base hφ hwellFormed hsafe hheap
            hsource hsourceLoc
    | there hsourceReads =>
        simpa [LVal.base] using ihSource hsourceReads
  · intros
    trivial
  · intros
    trivial

/--
Any borrow-resolution dependency on variable `x` is witnessed by some borrow
target base occurring in the dependency's static partial type whose rank is at
least `x`'s rank.
-/
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
  intro hφ hwellFormed hsafe hheap hborrows hdependency hdependencyEq
  induction hdependency generalizing env current slotLifetime with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      subst hdependencyEq
      have htargetWell := hborrows PartialTyContains.here target hmem
      rcases htargetWell with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      refine ⟨LVal.base target, ?_, ?_⟩
      · exact mem_partialTy_vars_iff.mpr
          ⟨mutable, targets, target, PartialTyContains.here, hmem, rfl⟩
      · exact locReads_var_rank_le_base hφ hwellFormed hsafe hheap
          htargetTyping hreads
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hφ hwellFormed hsafe hinnerBorrows hdependencyEq with
        ⟨v, hv, hle⟩
      exact ⟨v, by simpa [PartialTy.vars] using hv, hle⟩
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hφ hwellFormed hsafe hinnerBorrows hdependencyEq with
        ⟨v, hv, hle⟩
      exact ⟨v, by simpa [PartialTy.vars, Ty.vars] using hv, hle⟩

theorem lval_loc_var_rank_le_base_whenInitialized {store : ProgramStore}
    {env : Env} {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
    {x : Name} {φ : Name → Nat} :
    LinearizedBy φ env →
    SafeAbstractionWhenInitialized store env →
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
      ∀ target, target ∈ targets →
        store.loc target = some (VariableProjection x) →
        φ x ≤ φ (LVal.base target))
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro y slot _hslot hloc
    simp [ProgramStore.loc, VariableProjection] at hloc
    cases hloc
    exact Nat.le_refl _
  · intro source inner sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source (.box inner) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
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
  · intro source inner sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.box inner)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
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
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets _ihSource ihTargets hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrowLive selectedLocation _mutable _targets selected _hinit hmem
        hselectedLoc =>
        have hderefLoc : store.loc source.deref = some selectedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hselectedLocationEq : selectedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        subst hselectedLocationEq
        have hxLeSelected : φ x ≤ φ (LVal.base selected) :=
          ihTargets selected hmem hselectedLoc
        have hselectedMemVars :
            LVal.base selected ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
          exact mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, selected, PartialTyContains.here, hmem, rfl⟩
        have hselectedLtSource :
            φ (LVal.base selected) < φ (LVal.base source) :=
          (lvalTyping_vars_rank_lt hφ).1 hsource
            (LVal.base selected) hselectedMemVars
        exact le_trans hxLeSelected (Nat.le_of_lt hselectedLtSource)
    | @borrowStale _location _mutable _targets hstale =>
        have hinitialized : BorrowTargetsInitialized env targets := by
          intro target hmem
          rcases lvalTargetsTyping_member_strengthens htargets target hmem with
            ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
          exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
        exact False.elim (hstale hinitialized)
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

theorem locReads_var_rank_le_base_whenInitialized {store : ProgramStore}
    {env : Env} {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {x : Name} {φ : Name → Nat} :
    LinearizedBy φ env →
    SafeAbstractionWhenInitialized store env →
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
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro _y _slot _hslot hreads
    cases hreads
  · intro source inner sourceLifetime hsource ih hreads
    cases hreads with
    | here hsourceLoc =>
        simpa [LVal.base] using
          lval_loc_var_rank_le_base_whenInitialized hφ hsafe hheap
            hsource hsourceLoc
    | there hsourceReads =>
        simpa [LVal.base] using ih hsourceReads
  · intro source inner sourceLifetime hsource ih hreads
    cases hreads with
    | here hsourceLoc =>
        simpa [LVal.base] using
          lval_loc_var_rank_le_base_whenInitialized hφ hsafe hheap
            hsource hsourceLoc
    | there hsourceReads =>
        simpa [LVal.base] using ih hsourceReads
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource _htargets ihSource _ihTargets hreads
    cases hreads with
    | here hsourceLoc =>
        simpa [LVal.base] using
          lval_loc_var_rank_le_base_whenInitialized hφ hsafe hheap
            hsource hsourceLoc
    | there hsourceReads =>
        simpa [LVal.base] using ihSource hsourceReads
  · intros
    trivial
  · intros
    trivial

theorem RuntimeFrame.borrowDependencyWhenInitialized_var_rank_le_var
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {x : Name} {φ : Name → Nat} :
    LinearizedBy φ env →
    WellFormedEnvWhenInitialized env current →
    SafeAbstractionWhenInitialized store env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy dependency →
    dependency = VariableProjection x →
    ∃ v, v ∈ PartialTy.vars partialTy ∧ φ x ≤ φ v := by
  intro hφ hwellFormed hsafe hheap hborrows hdependency hdependencyEq
  induction hdependency generalizing current slotLifetime with
  | @borrow location readLocation mutable targets target hinitialized hmem hloc
      hreads =>
      subst hdependencyEq
      rcases hinitialized target hmem with
        ⟨targetTy, targetLifetime, htargetTyping⟩
      refine ⟨LVal.base target, ?_, ?_⟩
      · exact mem_partialTy_vars_iff.mpr
          ⟨mutable, targets, target, PartialTyContains.here, hmem, rfl⟩
      · exact locReads_var_rank_le_base_whenInitialized hφ hsafe hheap
          htargetTyping hreads
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime
            inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hwellFormed hinnerBorrows hdependencyEq with
        ⟨v, hv, hle⟩
      exact ⟨v, by simpa [PartialTy.vars] using hv, hle⟩
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime
            (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hwellFormed hinnerBorrows hdependencyEq with
        ⟨v, hv, hle⟩
      exact ⟨v, by simpa [PartialTy.vars, Ty.vars] using hv, hle⟩

theorem lval_loc_protected_rank_le_base_whenInitialized
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
    {location : Location} {xRoot : Name} {φ : Name → Nat} :
    LinearizedBy φ env →
    WellFormedEnvWhenInitialized env current →
    SafeAbstractionWhenInitialized store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    store.loc lv = some location →
    ProtectedByBase store xRoot location →
    φ xRoot ≤ φ (LVal.base lv) := by
  intro hφ hwellFormed hsafe hvalidStore hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      ∀ {location : Location} {xRoot : Name},
        store.loc lv = some location →
        ProtectedByBase store xRoot location →
        φ xRoot ≤ φ (LVal.base lv))
    (motive_2 := fun targets partialTy lifetime _ =>
      ∀ target, target ∈ targets →
        ∀ {location : Location} {xRoot : Name},
          store.loc target = some location →
          ProtectedByBase store xRoot location →
          φ xRoot ≤ φ (LVal.base target))
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro y slot _hslot location xRoot hloc hprot
    simp [ProgramStore.loc, VariableProjection] at hloc
    subst hloc
    have hrootEq : xRoot = y :=
      ProtectedByBase.root_unique hvalidStore hheap hprot (Or.inl rfl)
    subst hrootEq
    exact Nat.le_refl _
  · intro source inner sourceLifetime hsource _ih location xRoot hloc hprot
    rcases StoreOwnerSpineWhenInitialized.of_lvalTyping_box hwellFormed
        hsafe hsource with
      ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
        hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot, hsourceSpine⟩
    have hsourceValid :
        ValidPartialValueWhenInitialized env store sourceSlot.value
          (.box inner) :=
      StoreOwnerSpineWhenInitialized.leaf_valid hsourceSpine
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @box ownerLocation ownerSlot _ hownerSlot hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = location := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        have hsourceSpineSnoc :
            StoreOwnerSpineWhenInitialized env store
              (VariableProjection (LVal.base source)) rootSlot envSlot.ty
              (() :: LVal.path source) ownerLocation ownerSlot inner :=
          StoreOwnerSpineWhenInitialized.snoc_box hsourceSpine rfl rfl
            hownerSlot hinnerValid
        have hlocalProt :
            ProtectedByBase store (LVal.base source) ownerLocation :=
          Or.inr
            (StoreOwnerSpineWhenInitialized.ownsTransitively_of_nonempty
              hsourceSpineSnoc (by simp))
        have hprotOwner : ProtectedByBase store xRoot ownerLocation := by
          simpa [hownerEq] using hprot
        have hrootEq : xRoot = LVal.base source :=
          ProtectedByBase.root_unique hvalidStore hheap hprotOwner hlocalProt
        subst hrootEq
        exact Nat.le_refl _
  · intro source inner sourceLifetime hsource ih location xRoot hloc hprot
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.box inner)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = location := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        have hownsAt : ProgramStore.OwnsAt store ownerLocation sourceLocation :=
          ⟨sourceSlotLifetime, by simpa [owningRef] using hsourceSlot⟩
        have hprotSource : ProtectedByBase store xRoot sourceLocation :=
          ProtectedByBase.pred_of_ownsAt hvalidStore hheap
            (by simpa [hownerEq] using hprot) hownsAt
        exact ih hsourceLoc hprotSource
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets _ihSource ihTargets location xRoot hloc hprot
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrowLive selectedLocation _mutable _targets selected _hinit hmem
        hselectedLoc =>
        have hderefLoc : store.loc source.deref = some selectedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hselectedLocationEq : selectedLocation = location := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        have hselectedLoc' :
            store.loc selected = some location := by
          simpa [hselectedLocationEq] using hselectedLoc
        have hxLeSelected : φ xRoot ≤ φ (LVal.base selected) :=
          ihTargets selected hmem hselectedLoc' hprot
        have hselectedMemVars :
            LVal.base selected ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
          exact mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, selected, PartialTyContains.here, hmem, rfl⟩
        have hselectedLtSource :
            φ (LVal.base selected) < φ (LVal.base source) :=
          (lvalTyping_vars_rank_lt hφ).1 hsource
            (LVal.base selected) hselectedMemVars
        exact le_trans hxLeSelected (Nat.le_of_lt hselectedLtSource)
    | @borrowStale _location _mutable _targets hstale =>
        have hinitialized : BorrowTargetsInitialized env targets := by
          intro target hmem
          rcases lvalTargetsTyping_member_strengthens htargets target hmem with
            ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
          exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
        exact False.elim (hstale hinitialized)
  · intro target targetTy targetLifetime _htarget ihTarget selected hmem
      location xRoot hloc hprot
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ihTarget hloc hprot
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest _hunion _hintersection ihHead ihRest selected hmem
      location xRoot hloc hprot
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst hhead
      exact ihHead hloc hprot
    · exact ihRest selected htail hloc hprot

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
  | undefOf hinner hstrength =>
      intro howners _hdeps
      exact ValidPartialValue.undefOf
        (RuntimeFrame.validPartialValueSkeleton_update_of_not_owner_reaches
          hinner
          (fun reached hreach =>
            howners reached
              (RuntimeFrame.OwnerReaches.undefOf hinner hstrength hreach)))
        hstrength
  | @borrow location mutable targets target hmem hloc =>
      intro _howners hdeps
      refine ValidPartialValue.borrow hmem ?_
      exact RuntimeFrame.loc_update_of_not_locReads hloc (by
        intro mid hreads
        exact hdeps mid
          (RuntimeFrame.SelectedBorrowDependency.borrow
            (store := store) (location := location) (mutable := mutable)
            (targets := targets) (target := target) (hmem := hmem)
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
    | borrowHere {mutable : Bool} {targets : List LVal}
        {selectedTarget : LVal} {selectedTargetTy : Ty}
        {selectedTargetLifetime : Lifetime} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedSlotTy : Ty} :
        selectedTarget ∈ targets →
        LValTyping env selectedTarget (.ty selectedTargetTy)
          selectedTargetLifetime →
        store.loc selectedTarget = some (VariableProjection selectedName) →
        env.slotAt selectedName = some selectedSlot →
        selectedSlot.ty = .ty selectedSlotTy →
        RuntimePathSelected store env (.ty (.borrow mutable targets)) [()]
          selectedName selectedSlot selectedSlotTy
    | box {inner : PartialTy} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedSlotTy : Ty} :
        RuntimePathSelected store env inner path selectedName selectedSlot
          selectedSlotTy →
        RuntimePathSelected store env (.box inner) (() :: path) selectedName
          selectedSlot selectedSlotTy
    | boxFull {inner : Ty} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedSlotTy : Ty} :
        RuntimePathSelected store env (.ty inner) path selectedName selectedSlot
          selectedSlotTy →
        RuntimePathSelected store env (.ty (.box inner)) (() :: path)
          selectedName selectedSlot selectedSlotTy
    | borrowStep {mutable : Bool} {targets : List LVal} {path : List Unit}
        {selectedName : Name} {selectedSlot : EnvSlot} {selectedSlotTy : Ty} :
        RuntimeTargetsPathSelected store env targets path selectedName
          selectedSlot selectedSlotTy →
        RuntimePathSelected store env (.ty (.borrow mutable targets))
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
      {env : Env} {current : Lifetime} {φ : Name → Nat}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ∼ₛ env) (hheap : StoreOwnerTargetsHeap store) :
      ∀ {pt : PartialTy} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedSlotTy : Ty},
        RuntimePathSelected store env pt path selectedName selectedSlot
          selectedSlotTy →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv pt lifetime →
          φ selectedName < φ (LVal.base lv)
    | .ty (.borrow mutable targets), [()], selectedName, selectedSlot,
      selectedSlotTy,
      RuntimePathSelected.borrowHere hmem htargetTyping htargetLoc _hslot _hty,
      lv, lifetime, htyping => by
        have hselectedLeTarget :
            φ selectedName ≤ φ (LVal.base _) :=
          lval_loc_var_rank_le_base hφ hwellFormed hsafe hheap
            htargetTyping htargetLoc
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_of_le_of_lt hselectedLeTarget htargetLtLv
    | .box inner, () :: path, selectedName, selectedSlot, selectedSlotTy,
      RuntimePathSelected.box hinner, lv, lifetime, htyping => by
        have hderef : LValTyping env (.deref lv) inner lifetime :=
          LValTyping.box htyping
        simpa [LVal.base] using
          RuntimePathSelected.rank_lt_of_lvalTyping hφ hwellFormed hsafe
            hheap hinner hderef
    | .ty (.box inner), () :: path, selectedName, selectedSlot,
      selectedSlotTy, RuntimePathSelected.boxFull hinner, lv, lifetime,
      htyping => by
        have hderef : LValTyping env (.deref lv) (.ty inner) lifetime :=
          LValTyping.boxFull htyping
        simpa [LVal.base] using
          RuntimePathSelected.rank_lt_of_lvalTyping hφ hwellFormed hsafe
            hheap hinner hderef
    | .ty (.borrow mutable targets), () :: path, selectedName, selectedSlot,
      selectedSlotTy, RuntimePathSelected.borrowStep htargets, lv, lifetime,
      htyping => by
        exact RuntimeTargetsPathSelected.rank_lt_of_lvalTyping hφ hwellFormed
          hsafe hheap htargets htyping

  theorem RuntimeTargetsPathSelected.rank_lt_of_lvalTyping
      {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ∼ₛ env) (hheap : StoreOwnerTargetsHeap store) :
      ∀ {mutable : Bool} {targets : List LVal} {path : List Unit}
        {selectedName : Name} {selectedSlot : EnvSlot} {selectedSlotTy : Ty},
        RuntimeTargetsPathSelected store env targets path selectedName
          selectedSlot selectedSlotTy →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv (.ty (.borrow mutable targets)) lifetime →
          φ selectedName < φ (LVal.base lv)
    | mutable, targets, path, selectedName, selectedSlot, selectedSlotTy,
      RuntimeTargetsPathSelected.target hmem htargetTyping hpath, lv, lifetime,
      htyping => by
        have hselectedLtTarget :
            φ selectedName < φ (LVal.base _) :=
          RuntimePathSelected.rank_lt_of_lvalTyping hφ hwellFormed hsafe
            hheap hpath htargetTyping
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_trans hselectedLtTarget htargetLtLv
end

mutual
  theorem RuntimePathSelected.rank_lt_of_lvalTyping_whenInitialized
      {store : ProgramStore} {env : Env} {φ : Name → Nat}
      (hφ : LinearizedBy φ env)
      (hsafe : SafeAbstractionWhenInitialized store env)
      (hheap : StoreOwnerTargetsHeap store) :
      ∀ {pt : PartialTy} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedSlotTy : Ty},
        RuntimePathSelected store env pt path selectedName selectedSlot
          selectedSlotTy →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv pt lifetime →
          φ selectedName < φ (LVal.base lv)
    | .ty (.borrow mutable targets), [()], selectedName, selectedSlot,
      selectedSlotTy,
      RuntimePathSelected.borrowHere hmem htargetTyping htargetLoc _hslot _hty,
      lv, lifetime, htyping => by
        have hselectedLeTarget :
            φ selectedName ≤ φ (LVal.base _) :=
          lval_loc_var_rank_le_base_whenInitialized hφ hsafe hheap
            htargetTyping htargetLoc
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_of_le_of_lt hselectedLeTarget htargetLtLv
    | .box inner, () :: path, selectedName, selectedSlot, selectedSlotTy,
      RuntimePathSelected.box hinner, lv, lifetime, htyping => by
        have hderef : LValTyping env (.deref lv) inner lifetime :=
          LValTyping.box htyping
        simpa [LVal.base] using
          RuntimePathSelected.rank_lt_of_lvalTyping_whenInitialized hφ hsafe
            hheap hinner hderef
    | .ty (.box inner), () :: path, selectedName, selectedSlot,
      selectedSlotTy, RuntimePathSelected.boxFull hinner, lv, lifetime,
      htyping => by
        have hderef : LValTyping env (.deref lv) (.ty inner) lifetime :=
          LValTyping.boxFull htyping
        simpa [LVal.base] using
          RuntimePathSelected.rank_lt_of_lvalTyping_whenInitialized hφ hsafe
            hheap hinner hderef
    | .ty (.borrow mutable targets), () :: path, selectedName, selectedSlot,
      selectedSlotTy, RuntimePathSelected.borrowStep htargets, lv, lifetime,
      htyping => by
        exact RuntimeTargetsPathSelected.rank_lt_of_lvalTyping_whenInitialized
          hφ hsafe hheap htargets htyping

  theorem RuntimeTargetsPathSelected.rank_lt_of_lvalTyping_whenInitialized
      {store : ProgramStore} {env : Env} {φ : Name → Nat}
      (hφ : LinearizedBy φ env)
      (hsafe : SafeAbstractionWhenInitialized store env)
      (hheap : StoreOwnerTargetsHeap store) :
      ∀ {mutable : Bool} {targets : List LVal} {path : List Unit}
        {selectedName : Name} {selectedSlot : EnvSlot} {selectedSlotTy : Ty},
        RuntimeTargetsPathSelected store env targets path selectedName
          selectedSlot selectedSlotTy →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv (.ty (.borrow mutable targets)) lifetime →
          φ selectedName < φ (LVal.base lv)
    | mutable, targets, path, selectedName, selectedSlot, selectedSlotTy,
      RuntimeTargetsPathSelected.target hmem htargetTyping hpath, lv, lifetime,
      htyping => by
        have hselectedLtTarget :
            φ selectedName < φ (LVal.base _) :=
          RuntimePathSelected.rank_lt_of_lvalTyping_whenInitialized hφ hsafe
            hheap hpath htargetTyping
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, _, PartialTyContains.here, hmem, rfl⟩
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
    ?borrowHere ?box ?boxFull ?borrowStep ?target hselected left right hunion
  case borrowHere =>
    intro mutable targets selectedTarget selectedTargetTy selectedTargetLifetime
      selectedName selectedSlot selectedSlotTy hmem htyping hloc hslot hty
      left right hunion
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.left_strengthens hunion) with
      ⟨leftTargets, hleftEq, _hleftSubset⟩
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.right_strengthens hunion) with
      ⟨rightTargets, hrightEq, _hrightSubset⟩
    subst hleftEq
    subst hrightEq
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
  case boxFull =>
    intro inner path selectedName selectedSlot selectedSlotTy hinner ih
      left right hunion
    have hleftStrength := PartialTyUnion.left_strengthens hunion
    cases hleftStrength with
    | reflex =>
        exact Or.inl (RuntimePathSelected.boxFull hinner)
    | tyBox hleftInner =>
        have hrightStrength := PartialTyUnion.right_strengthens hunion
        cases hrightStrength with
        | reflex =>
            exact Or.inr (RuntimePathSelected.boxFull hinner)
        | tyBox hrightInner =>
            rcases ih _ _ (PartialTyUnion.tyBox_inv hunion) with hleft | hright
            · exact Or.inl (RuntimePathSelected.boxFull hleft)
            · exact Or.inr (RuntimePathSelected.boxFull hright)
  case borrowStep =>
    intro mutable targets path selectedName selectedSlot selectedSlotTy
      htargets _ih left right hunion
    cases htargets with
    | target hmem htargetTyping hpath =>
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.left_strengthens hunion) with
          ⟨leftTargets, hleftEq, _hleftSubset⟩
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.right_strengthens hunion) with
          ⟨rightTargets, hrightEq, _hrightSubset⟩
        subst hleftEq
        subst hrightEq
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
    ?var ?box ?boxFull ?borrow ?singleton ?cons htargets hselected
  case var | box | boxFull | borrow => intros; trivial
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
    (motive_1 := fun lv pt _lifetime _htyping =>
      ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
      ∀ (path : List Unit),
        RuntimePathSelected store env pt path selectedName selectedSlot
          selectedSlotTy →
        RuntimePathSelected store env slot.ty (LVal.path lv ++ path)
          selectedName selectedSlot selectedSlotTy)
    (motive_2 := fun _targets _pt _lifetime _htyping => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro x typedSlot htypedSlot slot hslot path hselected
    have hslotEq : slot = typedSlot :=
      Option.some.inj (hslot.symm.trans htypedSlot)
    subst hslotEq
    simpa [LVal.path] using hselected
  · intro source inner sourceLifetime _hsource ih slot hslot path hselected
    have hsourceSelected :
        RuntimePathSelected store env (.box inner) (() :: path) selectedName
          selectedSlot selectedSlotTy :=
      RuntimePathSelected.box hselected
    have hbase := ih hslot (() :: path) hsourceSelected
    simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
      using hbase
  · intro source inner sourceLifetime _hsource ih slot hslot path hselected
    have hsourceSelected :
        RuntimePathSelected store env (.ty (.box inner)) (() :: path)
          selectedName selectedSlot selectedSlotTy :=
      RuntimePathSelected.boxFull hselected
    have hbase := ih hslot (() :: path) hsourceSelected
    simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
      using hbase
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      _hsource htargets ihSource _ihTargets slot hslot path hselected
    have htargetsSelected :
        RuntimeTargetsPathSelected store env targets path selectedName
          selectedSlot selectedSlotTy :=
      RuntimeTargetsPathSelected.of_lvalTargetsTyping htargets hselected
    have hsourceSelected :
        RuntimePathSelected store env (.ty (.borrow mutable targets))
          (() :: path) selectedName selectedSlot selectedSlotTy :=
      RuntimePathSelected.borrowStep htargetsSelected
    have hbase := ihSource hslot (() :: path) hsourceSelected
    simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
      using hbase
  · intros
    trivial
  · intros
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
  intro hbelow hselected hupdate hdirect hindirect
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
          {lifetime : Lifetime} {branchPath : List Unit}
          {branchResult : Env},
          0 < branchRank →
          φ (LVal.base target) < rootRank →
          LValTyping env target pt lifetime →
          RuntimePathSelected store env pt branchPath selectedName
            selectedSlot selectedSlotTy →
          EnvWrite branchRank env (prependPath branchPath target) rhsTy
            branchResult →
          EnvSameShapeStrengthening selectedSource branchResult) →
        EnvSameShapeStrengthening selectedSource writeEnv ∧
          PartialTyStrengthens oldTy updatedTy ∧
          PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun _targets _path _selectedName _selectedSlot
      _selectedSlotTy _ => True)
    ?borrowHere ?box ?boxFull ?borrowStep ?target hselected)
    hbelow hupdate hdirect hindirect
  case borrowHere =>
      intro mutable targets selectedTarget selectedTargetTy
        selectedTargetLifetime selectedName selectedSlot selectedSlotTy hmem
        htargetTyping htargetLoc _hslot _hty rank updatedTy writeEnv hbelow
        hupdate hdirect _hindirect
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        cases hupdatedEq
        have htargetRank :
            φ (LVal.base selectedTarget) < rootRank :=
          hbelow (LVal.base selectedTarget)
            (mem_partialTy_vars_iff.mpr
              ⟨true, _, selectedTarget, PartialTyContains.here, hmem, rfl⟩)
        have hleaves :=
          WriteBorrowTargets.initialized_leaves_of_typed hwrites
        have hmap : EnvSameShapeStrengthening selectedSource writeEnv :=
          WriteBorrowTargets.selected_branch_to_result_map
            (Nat.succ_pos rank) hwrites hleaves hmem
            (fun branchResult hbranchWrite =>
              hdirect (Nat.succ_pos rank) htargetRank htargetTyping
                htargetLoc (by simpa [prependPath] using hbranchWrite))
        exact ⟨hmap, PartialTyStrengthens.reflex,
          PartialTy.sameShape_refl _⟩
  case box =>
      intro inner path selectedName selectedSlot selectedSlotTy hinner ih
        rank updatedTy writeEnv hbelow hupdate hdirect hindirect
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, hupdatedEq,
            hinnerUpdate⟩
          cases htyEq
          cases hupdatedEq
          have hbelowInner :
              ∀ v, v ∈ PartialTy.vars inner → φ v < rootRank := by
            intro v hv
            exact hbelow v (by simpa [PartialTy.vars] using hv)
          rcases ih hbelowInner hinnerUpdate hdirect hindirect with
            ⟨hmap, hstrength, hshape⟩
          exact ⟨hmap, PartialTyStrengthens.box hstrength,
            by simpa [PartialTy.sameShape] using hshape⟩
        · rcases hboxFull with
            ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinnerUpdate⟩
          cases htyEq
      · rcases hborrow with ⟨targets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  case boxFull =>
      intro inner path selectedName selectedSlot selectedSlotTy hinner ih
        rank updatedTy writeEnv hbelow hupdate hdirect hindirect
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinnerUpdate⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, hupdatedEq,
            hinnerUpdate⟩
          cases htyEq
          cases hupdatedEq
          have hbelowInner :
              ∀ v, v ∈ PartialTy.vars (.ty inner) → φ v < rootRank := by
            intro v hv
            exact hbelow v (by simpa [PartialTy.vars, Ty.vars] using hv)
          rcases ih hbelowInner hinnerUpdate hdirect hindirect with
            ⟨hmap, hstrength, hshape⟩
          exact ⟨hmap, PartialTyStrengthens.tyBox_rebox hstrength hshape,
            by
              cases updatedInner <;>
                simp [partialTyRebox, PartialTy.sameShape, Ty.sameShape] at hshape ⊢
              exact hshape⟩
      · rcases hborrow with ⟨targets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  case borrowStep =>
      intro mutable targets path selectedName selectedSlot selectedSlotTy
        htargetsSelected _ih rank updatedTy writeEnv hbelow hupdate _hdirect
        hindirect
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        cases hupdatedEq
        cases htargetsSelected with
        | target htargetMem htargetTyping htargetSelected =>
            rename_i branchTarget branchPt branchLifetime
            have htargetRank :
                φ (LVal.base branchTarget) < rootRank :=
              hbelow (LVal.base branchTarget)
                (mem_partialTy_vars_iff.mpr
                  ⟨true, _, branchTarget, PartialTyContains.here,
                    htargetMem, rfl⟩)
            have hleaves :=
              WriteBorrowTargets.initialized_leaves_of_typed hwrites
            have hmap : EnvSameShapeStrengthening selectedSource writeEnv :=
              WriteBorrowTargets.selected_branch_to_result_map
                (Nat.succ_pos rank) hwrites hleaves htargetMem
                (fun branchResult hbranchWrite =>
                  hindirect (Nat.succ_pos rank) htargetRank htargetTyping
                    htargetSelected hbranchWrite)
            exact ⟨hmap, PartialTyStrengthens.reflex,
              PartialTy.sameShape_refl _⟩
  case target =>
      intros
      trivial
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
  intro hφ hwellFormed hsafe hheap htyping hloc hselectedSlot
    hselectedSlotTy hwrite
  let selectedSource : Env :=
    env.update selectedName { selectedSlot with ty := .ty rhsTy }
  let PathMap : Nat → Prop := fun rootRank =>
    ∀ {target : LVal} {pt : PartialTy} {targetLifetime : Lifetime}
      {path : List Unit} {branchResult : Env} {branchRank : Nat},
      φ (LVal.base target) = rootRank →
      LValTyping env target pt targetLifetime →
      RuntimePathSelected store env pt path selectedName selectedSlot
        selectedSlotTy →
      env.slotAt selectedName = some selectedSlot →
      selectedSlot.ty = .ty selectedSlotTy →
      EnvWrite branchRank env (prependPath path target) rhsTy branchResult →
      EnvSameShapeStrengthening selectedSource branchResult
  let DirectMap : Nat → Prop := fun rootRank =>
    ∀ {target : LVal} {targetTy : Ty} {targetLifetime : Lifetime}
      {branchResult : Env} {branchRank : Nat},
      φ (LVal.base target) = rootRank →
      LValTyping env target (.ty targetTy) targetLifetime →
      store.loc target = some (VariableProjection selectedName) →
      env.slotAt selectedName = some selectedSlot →
      selectedSlot.ty = .ty selectedSlotTy →
      EnvWrite branchRank env target rhsTy branchResult →
      EnvSameShapeStrengthening selectedSource branchResult
  have hall : ∀ rootRank, PathMap rootRank ∧ DirectMap rootRank := by
    intro rootRank
    refine Nat.strong_induction_on rootRank ?_
    intro rootRank ih
    have hpath : PathMap rootRank := by
      intro target pt targetLifetime path branchResult branchRank hrootEq
        htargetTyping hselected hselectedSlotAt hselectedTy hbranchWrite
      cases hbranchWrite with
      | @intro _rank _env₁ writeEnv writeLv writeSlot _ty updatedTy
          hwriteSlot hupdate =>
          have hwriteSlotBase :
              env.slotAt (LVal.base target) = some writeSlot := by
            simpa [LVal.base_prependPath] using hwriteSlot
          have hupdatePath :
              UpdateAtPath branchRank env (LVal.path target ++ path)
                writeSlot.ty rhsTy writeEnv updatedTy := by
            simpa [LVal.path_prependPath] using hupdate
          have hselectedFull :
              RuntimePathSelected store env writeSlot.ty
                (LVal.path target ++ path) selectedName selectedSlot
                selectedSlotTy :=
            RuntimePathSelected.prepend_of_lvalTyping htargetTyping
              hwriteSlotBase path hselected
          have hbelow :
              ∀ v, v ∈ PartialTy.vars writeSlot.ty →
                φ v < φ (LVal.base target) :=
            hφ (LVal.base target) writeSlot hwriteSlotBase
          rcases RuntimePathSelected.updateAtPath_map
              (rootRank := φ (LVal.base target))
              (selectedSource := selectedSource)
              hbelow hselectedFull hupdatePath
                  (fun {branchRank : Nat} {recursiveTarget : LVal}
                    {recursiveTy : Ty} {recursiveLifetime : Lifetime}
                    {recursiveResult : Env}
                    hpositive htargetRank hrecursiveTyping hrecursiveLoc
                    hrecursiveWrite =>
                have hlt : φ (LVal.base recursiveTarget) < rootRank := by
                  simpa [hrootEq] using htargetRank
                (ih (φ (LVal.base recursiveTarget)) hlt).2 rfl
                  hrecursiveTyping hrecursiveLoc hselectedSlotAt
                  hselectedTy hrecursiveWrite)
                  (fun {branchRank : Nat} {recursiveTarget : LVal}
                    {recursivePt : PartialTy} {recursiveLifetime : Lifetime}
                    {recursivePath : List Unit} {recursiveResult : Env}
                    hpositive htargetRank hrecursiveTyping hrecursiveSelected
                    hrecursiveWrite =>
                have hlt : φ (LVal.base recursiveTarget) < rootRank := by
                  simpa [hrootEq] using htargetRank
                (ih (φ (LVal.base recursiveTarget)) hlt).1 rfl
                  hrecursiveTyping hrecursiveSelected hselectedSlotAt
                  hselectedTy hrecursiveWrite) with
            ⟨hinnerMap, hstrength, hshape⟩
          have hselectedLtBase :
              φ selectedName < φ (LVal.base target) :=
            RuntimePathSelected.rank_lt_of_lvalTyping hφ hwellFormed
              hsafe hheap hselected htargetTyping
          have hbaseNe : LVal.base target ≠ selectedName := by
            intro hbaseEq
            have hbad : φ selectedName < φ selectedName := by
              simpa [hbaseEq] using hselectedLtBase
            exact Nat.lt_irrefl _ hbad
          have hselectedSourceBase :
              selectedSource.slotAt (LVal.base target) = some writeSlot := by
            dsimp [selectedSource]
            rw [Env.update_slotAt_ne]
            · exact hwriteSlotBase
            · exact hbaseNe
          have hfinal :
              EnvSameShapeStrengthening selectedSource
                (writeEnv.update (LVal.base target)
                  { writeSlot with ty := updatedTy }) :=
            EnvSameShapeStrengthening.update_result_strengthening
              hinnerMap hselectedSourceBase rfl hstrength hshape
          simpa [LVal.base_prependPath] using hfinal
    have hdirect : DirectMap rootRank := by
      intro target targetTy targetLifetime branchResult branchRank hrootEq
        htargetTyping htargetLoc hselectedSlotAt hselectedTy hbranchWrite
      cases target with
      | var x =>
          rcases LValTyping.var_inv htargetTyping with
            ⟨targetSlot, htargetSlot, htargetSlotTy, _htargetLifetime⟩
          simp [ProgramStore.loc, VariableProjection] at htargetLoc
          cases htargetLoc
          have hslotEq : selectedSlot = targetSlot :=
            Option.some.inj (hselectedSlotAt.symm.trans htargetSlot)
          subst hslotEq
          exact EnvWrite.var_rhs_to_result_map htargetSlot hselectedTy
            hbranchWrite
      | deref source =>
          cases htargetTyping with
          | box hsource =>
              have hsourceAbs :
                  LValLocationAbstraction store source (.box (.ty targetTy)) :=
                lvalTyping_defined_location hwellFormed hsafe hsource
              rcases hsourceAbs with
                ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
                  hsourceValid⟩
              rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
              cases hsourceValid with
              | @box ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
                  have hderefLoc :
                      store.loc source.deref = some ownerLocation := by
                    simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                  have hownerEq :
                      ownerLocation = VariableProjection selectedName := by
                    rw [htargetLoc] at hderefLoc
                    exact (Option.some.inj hderefLoc).symm
                  subst hownerEq
                  have howns : ProgramStore.Owns store
                      (VariableProjection selectedName) :=
                    ⟨sourceLocation, sourceSlotLifetime, by
                      simpa [owningRef] using hsourceSlot⟩
                  exact False.elim
                    ((not_owns_var_of_storeOwnerTargetsHeap hheap) howns)
          | boxFull hsource =>
              have hsourceAbs :
                  LValLocationAbstraction store source
                    (.ty (.box targetTy)) :=
                lvalTyping_defined_location hwellFormed hsafe hsource
              rcases hsourceAbs with
                ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
                  hsourceValid⟩
              rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
              cases hsourceValid with
              | @boxFull ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
                  have hderefLoc :
                      store.loc source.deref = some ownerLocation := by
                    simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                  have hownerEq :
                      ownerLocation = VariableProjection selectedName := by
                    rw [htargetLoc] at hderefLoc
                    exact (Option.some.inj hderefLoc).symm
                  subst hownerEq
                  have howns : ProgramStore.Owns store
                      (VariableProjection selectedName) :=
                    ⟨sourceLocation, sourceSlotLifetime, by
                      simpa [owningRef] using hsourceSlot⟩
                  exact False.elim
                    ((not_owns_var_of_storeOwnerTargetsHeap hheap) howns)
          | borrow hsource htargets =>
              rename_i mutable targets borrowLifetime
              have hsourceAbs :
                  LValLocationAbstraction store source
                    (.ty (.borrow mutable targets)) :=
                lvalTyping_defined_location hwellFormed hsafe hsource
              rcases hsourceAbs with
                ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
                  hsourceValid⟩
              rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
              cases hsourceValid with
              | @borrow selectedLocation _mutable _targets selected hmem
                  hselectedLoc =>
                  have hderefLoc :
                      store.loc source.deref = some selectedLocation := by
                    simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                  have hselectedLocationEq :
                      selectedLocation = VariableProjection selectedName := by
                    rw [htargetLoc] at hderefLoc
                    exact (Option.some.inj hderefLoc).symm
                  have hselectedLocVar :
                      store.loc selected =
                        some (VariableProjection selectedName) := by
                    simpa [hselectedLocationEq] using hselectedLoc
                  rcases lvalTargetsTyping_member_strengthens htargets
                      selected hmem with
                    ⟨selectedTy, selectedLifetime, hselectedTyping,
                      _hselectedStrengthens⟩
                  have hselectedHead :
                      RuntimePathSelected store env
                        (.ty (.borrow mutable targets)) [()] selectedName
                        selectedSlot selectedSlotTy :=
                    RuntimePathSelected.borrowHere hmem hselectedTyping
                      hselectedLocVar hselectedSlotAt hselectedTy
                  have hsourceRoot :
                      φ (LVal.base source) = rootRank := by
                    simpa [LVal.base] using hrootEq
                  have hwritePath :
                      EnvWrite branchRank env (prependPath [()] source)
                        rhsTy branchResult := by
                    simpa [prependPath] using hbranchWrite
                  exact hpath hsourceRoot hsource hselectedHead
                    hselectedSlotAt hselectedTy hwritePath
    exact ⟨hpath, hdirect⟩
  exact (hall (φ (LVal.base lv))).2 rfl htyping hloc hselectedSlot
    hselectedSlotTy hwrite
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
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping ty rfl
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
  · intro source inner sourceLifetime hsource _ih ty hty hloc _hxSlot
    cases hty
    have hsourceAbs :
        LValLocationAbstraction store source (.ty (.box inner)) :=
      lvalTyping_defined_location hwellFormed hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
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
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets _ihSource ihTargets ty hty hloc hxSlot
    cases hty
    have hsourceAbs :
        LValLocationAbstraction store source (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location hwellFormed hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrow selectedLocation _mutable _targets selected hmem hselectedLoc =>
        have hderefLoc : store.loc source.deref = some selectedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hselectedLocationEq : selectedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        have hselectedLocVar :
            store.loc selected = some (VariableProjection x) := by
          simpa [hselectedLocationEq] using hselectedLoc
        exact ihTargets selected hmem hselectedLocVar hxSlot
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
    | borrowHere {mutable : Bool} {targets : List LVal}
        {selectedTarget : LVal} {selectedTargetTy : Ty}
        {selectedTargetLifetime : Lifetime} {address : Nat} :
        selectedTarget ∈ targets →
        LValTyping env selectedTarget (.ty selectedTargetTy)
          selectedTargetLifetime →
        store.loc selectedTarget = some (.heap address) →
        RuntimeSpinePathSelected store env (.ty (.borrow mutable targets))
          [()] address
    | box {inner : PartialTy} {path : List Unit} {address : Nat} :
        RuntimeSpinePathSelected store env inner path address →
        RuntimeSpinePathSelected store env (.box inner) (() :: path) address
    | boxFull {inner : Ty} {path : List Unit} {address : Nat} :
        RuntimeSpinePathSelected store env (.ty inner) path address →
        RuntimeSpinePathSelected store env (.ty (.box inner)) (() :: path)
          address
    | borrowStep {mutable : Bool} {targets : List LVal} {path : List Unit}
        {address : Nat} :
        RuntimeSpineTargetsSelected store env targets path address →
        RuntimeSpinePathSelected store env (.ty (.borrow mutable targets))
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
    ?borrowHere ?box ?boxFull ?borrowStep ?target hselected left right hunion
  case borrowHere =>
    intro mutable targets selectedTarget selectedTargetTy
      selectedTargetLifetime address hmem htyping hloc left right hunion
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.left_strengthens hunion) with
      ⟨leftTargets, hleftEq, _hleftSubset⟩
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.right_strengthens hunion) with
      ⟨rightTargets, hrightEq, _hrightSubset⟩
    subst hleftEq
    subst hrightEq
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
  case boxFull =>
    intro inner path address hinner ih left right hunion
    have hleftStrength := PartialTyUnion.left_strengthens hunion
    cases hleftStrength with
    | reflex =>
        exact Or.inl (RuntimeSpinePathSelected.boxFull hinner)
    | tyBox hleftInner =>
        have hrightStrength := PartialTyUnion.right_strengthens hunion
        cases hrightStrength with
        | reflex =>
            exact Or.inr (RuntimeSpinePathSelected.boxFull hinner)
        | tyBox hrightInner =>
            rcases ih _ _ (PartialTyUnion.tyBox_inv hunion) with hleft | hright
            · exact Or.inl (RuntimeSpinePathSelected.boxFull hleft)
            · exact Or.inr (RuntimeSpinePathSelected.boxFull hright)
  case borrowStep =>
    intro mutable targets path address htargets _ih left right hunion
    cases htargets with
    | target hmem htargetTyping hpath =>
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.left_strengthens hunion) with
          ⟨leftTargets, hleftEq, _hleftSubset⟩
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.right_strengthens hunion) with
          ⟨rightTargets, hrightEq, _hrightSubset⟩
        subst hleftEq
        subst hrightEq
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
    ?var ?box ?boxFull ?borrow ?singleton ?cons htargets hselected
  case var | box | boxFull | borrow => intros; trivial
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
    (motive_1 := fun lv pt _lifetime _htyping =>
      ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
      ∀ (path : List Unit),
        RuntimeSpinePathSelected store env pt path address →
        RuntimeSpinePathSelected store env slot.ty (LVal.path lv ++ path)
          address)
    (motive_2 := fun _targets _pt _lifetime _htyping => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro x typedSlot htypedSlot slot hslot path hselected
    have hslotEq : slot = typedSlot :=
      Option.some.inj (hslot.symm.trans htypedSlot)
    subst hslotEq
    simpa [LVal.path] using hselected
  · intro source inner sourceLifetime _hsource ih slot hslot path hselected
    have hsourceSelected :
        RuntimeSpinePathSelected store env (.box inner) (() :: path)
          address :=
      RuntimeSpinePathSelected.box hselected
    have hbase := ih hslot (() :: path) hsourceSelected
    simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
      using hbase
  · intro source inner sourceLifetime _hsource ih slot hslot path hselected
    have hsourceSelected :
        RuntimeSpinePathSelected store env (.ty (.box inner)) (() :: path)
          address :=
      RuntimeSpinePathSelected.boxFull hselected
    have hbase := ih hslot (() :: path) hsourceSelected
    simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
      using hbase
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      _hsource htargets ihSource _ihTargets slot hslot path hselected
    have htargetsSelected :
        RuntimeSpineTargetsSelected store env targets path address :=
      RuntimeSpineTargetsSelected.of_lvalTargetsTyping htargets hselected
    have hsourceSelected :
        RuntimeSpinePathSelected store env (.ty (.borrow mutable targets))
          (() :: path) address :=
      RuntimeSpinePathSelected.borrowStep htargetsSelected
    have hbase := ihSource hslot (() :: path) hsourceSelected
    simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
      using hbase
  · intros
    trivial
  · intros
    trivial
mutual
  theorem RuntimeSpinePathSelected.rank_lt_of_lvalTyping
      {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {xRoot : Name}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ∼ₛ env) (hvalidStore : ValidStore store)
      (hheap : StoreOwnerTargetsHeap store) :
      ∀ {pt : PartialTy} {path : List Unit} {address : Nat},
        RuntimeSpinePathSelected store env pt path address →
        ProtectedByBase store xRoot (.heap address) →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv pt lifetime →
          φ xRoot < φ (LVal.base lv)
    | .ty (.borrow mutable targets), [()], address,
      RuntimeSpinePathSelected.borrowHere hmem htargetTyping htargetLoc,
      hprot, lv, lifetime, htyping => by
        rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe
            htargetTyping htargetLoc with
          ⟨root', _, _, _, hprot', hrank', _, _, _, _, _, _⟩
        have hrootEq : root' = xRoot :=
          ProtectedByBase.root_unique hvalidStore hheap hprot' hprot
        subst hrootEq
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_of_le_of_lt hrank' htargetLtLv
    | .box inner, () :: path, address,
      RuntimeSpinePathSelected.box hinner, hprot, lv, lifetime, htyping => by
        have hderef : LValTyping env (.deref lv) inner lifetime :=
          LValTyping.box htyping
        simpa [LVal.base] using
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping hφ hwellFormed hsafe
            hvalidStore hheap hinner hprot hderef
    | .ty (.box inner), () :: path, address,
      RuntimeSpinePathSelected.boxFull hinner, hprot, lv, lifetime,
      htyping => by
        have hderef : LValTyping env (.deref lv) (.ty inner) lifetime :=
          LValTyping.boxFull htyping
        simpa [LVal.base] using
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping hφ hwellFormed hsafe
            hvalidStore hheap hinner hprot hderef
    | .ty (.borrow mutable targets), () :: path, address,
      RuntimeSpinePathSelected.borrowStep htargets, hprot, lv, lifetime,
      htyping => by
        exact RuntimeSpineTargetsSelected.rank_lt_of_lvalTyping hφ hwellFormed
          hsafe hvalidStore hheap htargets hprot htyping

  theorem RuntimeSpineTargetsSelected.rank_lt_of_lvalTyping
      {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {xRoot : Name}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ∼ₛ env) (hvalidStore : ValidStore store)
      (hheap : StoreOwnerTargetsHeap store) :
      ∀ {targets : List LVal} {path : List Unit} {address : Nat},
        RuntimeSpineTargetsSelected store env targets path address →
        ProtectedByBase store xRoot (.heap address) →
        ∀ {mutable : Bool} {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv (.ty (.borrow mutable targets)) lifetime →
          φ xRoot < φ (LVal.base lv)
    | targets, path, address,
      RuntimeSpineTargetsSelected.target hmem htargetTyping hpath, hprot,
      mutable, lv, lifetime, htyping => by
        have hselectedLtTarget :
            φ xRoot < φ (LVal.base _) :=
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping hφ hwellFormed hsafe
            hvalidStore hheap hpath hprot htargetTyping
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_trans hselectedLtTarget htargetLtLv
end

mutual
  theorem RuntimeSpinePathSelected.rank_lt_of_lvalTyping_whenInitialized
      {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {xRoot : Name}
      (hφ : LinearizedBy φ env)
      (hwellFormed : WellFormedEnvWhenInitialized env current)
      (hsafe : SafeAbstractionWhenInitialized store env)
      (hvalidStore : ValidStore store) (hheap : StoreOwnerTargetsHeap store) :
      ∀ {pt : PartialTy} {path : List Unit} {address : Nat},
        RuntimeSpinePathSelected store env pt path address →
        ProtectedByBase store xRoot (.heap address) →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv pt lifetime →
          φ xRoot < φ (LVal.base lv)
    | .ty (.borrow mutable targets), [()], address,
      RuntimeSpinePathSelected.borrowHere hmem htargetTyping htargetLoc,
      hprot, lv, lifetime, htyping => by
        have hselectedLeTarget :
            φ xRoot ≤ φ (LVal.base _) :=
          lval_loc_protected_rank_le_base_whenInitialized hφ hwellFormed hsafe
            hvalidStore hheap htargetTyping htargetLoc hprot
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_of_le_of_lt hselectedLeTarget htargetLtLv
    | .box inner, () :: path, address,
      RuntimeSpinePathSelected.box hinner, hprot, lv, lifetime, htyping => by
        have hderef : LValTyping env (.deref lv) inner lifetime :=
          LValTyping.box htyping
        simpa [LVal.base] using
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping_whenInitialized
            hφ hwellFormed hsafe hvalidStore hheap hinner hprot hderef
    | .ty (.box inner), () :: path, address,
      RuntimeSpinePathSelected.boxFull hinner, hprot, lv, lifetime,
      htyping => by
        have hderef : LValTyping env (.deref lv) (.ty inner) lifetime :=
          LValTyping.boxFull htyping
        simpa [LVal.base] using
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping_whenInitialized
            hφ hwellFormed hsafe hvalidStore hheap hinner hprot hderef
    | .ty (.borrow mutable targets), () :: path, address,
      RuntimeSpinePathSelected.borrowStep htargets, hprot, lv, lifetime,
      htyping => by
        exact
          RuntimeSpineTargetsSelected.rank_lt_of_lvalTyping_whenInitialized
            hφ hwellFormed hsafe hvalidStore hheap htargets hprot htyping

  theorem RuntimeSpineTargetsSelected.rank_lt_of_lvalTyping_whenInitialized
      {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {xRoot : Name}
      (hφ : LinearizedBy φ env)
      (hwellFormed : WellFormedEnvWhenInitialized env current)
      (hsafe : SafeAbstractionWhenInitialized store env)
      (hvalidStore : ValidStore store) (hheap : StoreOwnerTargetsHeap store) :
      ∀ {targets : List LVal} {path : List Unit} {address : Nat},
        RuntimeSpineTargetsSelected store env targets path address →
        ProtectedByBase store xRoot (.heap address) →
        ∀ {mutable : Bool} {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv (.ty (.borrow mutable targets)) lifetime →
          φ xRoot < φ (LVal.base lv)
    | targets, path, address,
      RuntimeSpineTargetsSelected.target hmem htargetTyping hpath, hprot,
      mutable, lv, lifetime, htyping => by
        have hselectedLtTarget :
            φ xRoot < φ (LVal.base _) :=
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping_whenInitialized
            hφ hwellFormed hsafe hvalidStore hheap hpath hprot htargetTyping
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, _, PartialTyContains.here, hmem, rfl⟩
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
  intro hbelow hselected hupdate hdirect hindirect
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
          {lifetime : Lifetime} {branchPath : List Unit}
          {branchResult : Env},
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
    ?borrowHere ?box ?boxFull ?borrowStep ?target hselected)
    hbelow hupdate hdirect hindirect
  case borrowHere =>
      intro mutable targets selectedTarget selectedTargetTy
        selectedTargetLifetime address hmem htargetTyping htargetLoc rank
        updatedTy writeEnv hbelow hupdate hdirect _hindirect
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        cases hupdatedEq
        have htargetRank :
            φ (LVal.base selectedTarget) < rootRank :=
          hbelow (LVal.base selectedTarget)
            (mem_partialTy_vars_iff.mpr
              ⟨true, _, selectedTarget, PartialTyContains.here, hmem, rfl⟩)
        have hleaves :=
          WriteBorrowTargets.initialized_leaves_of_typed hwrites
        have hmap : EnvSameShapeStrengthening selectedSource writeEnv :=
          WriteBorrowTargets.selected_branch_to_result_map
            (Nat.succ_pos rank) hwrites hleaves hmem
            (fun branchResult hbranchWrite =>
              hdirect (Nat.succ_pos rank) htargetRank htargetTyping
                htargetLoc (by simpa [prependPath] using hbranchWrite))
        exact ⟨hmap, PartialTyStrengthens.reflex,
          PartialTy.sameShape_refl _⟩
  case box =>
      intro inner path address hinner ih rank updatedTy writeEnv hbelow
        hupdate hdirect hindirect
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, hupdatedEq,
            hinnerUpdate⟩
          cases htyEq
          cases hupdatedEq
          have hbelowInner :
              ∀ v, v ∈ PartialTy.vars inner → φ v < rootRank := by
            intro v hv
            exact hbelow v (by simpa [PartialTy.vars] using hv)
          rcases ih hbelowInner hinnerUpdate hdirect hindirect with
            ⟨hmap, hstrength, hshape⟩
          exact ⟨hmap, PartialTyStrengthens.box hstrength,
            by simpa [PartialTy.sameShape] using hshape⟩
        · rcases hboxFull with
            ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinnerUpdate⟩
          cases htyEq
      · rcases hborrow with ⟨targets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  case boxFull =>
      intro inner path address hinner ih rank updatedTy writeEnv hbelow
        hupdate hdirect hindirect
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinnerUpdate⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, hupdatedEq,
            hinnerUpdate⟩
          cases htyEq
          cases hupdatedEq
          have hbelowInner :
              ∀ v, v ∈ PartialTy.vars (.ty inner) → φ v < rootRank := by
            intro v hv
            exact hbelow v (by simpa [PartialTy.vars, Ty.vars] using hv)
          rcases ih hbelowInner hinnerUpdate hdirect hindirect with
            ⟨hmap, hstrength, hshape⟩
          exact ⟨hmap, PartialTyStrengthens.tyBox_rebox hstrength hshape,
            by
              cases updatedInner <;>
                simp [partialTyRebox, PartialTy.sameShape, Ty.sameShape] at hshape ⊢
              exact hshape⟩
      · rcases hborrow with ⟨targets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  case borrowStep =>
      intro mutable targets path address htargetsSelected _ih rank updatedTy
        writeEnv hbelow hupdate _hdirect hindirect
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        cases hupdatedEq
        cases htargetsSelected with
        | target htargetMem htargetTyping htargetSelected =>
            rename_i branchTarget branchPt branchLifetime
            have htargetRank :
                φ (LVal.base branchTarget) < rootRank :=
              hbelow (LVal.base branchTarget)
                (mem_partialTy_vars_iff.mpr
                  ⟨true, _, branchTarget, PartialTyContains.here,
                    htargetMem, rfl⟩)
            have hleaves :=
              WriteBorrowTargets.initialized_leaves_of_typed hwrites
            have hmap : EnvSameShapeStrengthening selectedSource writeEnv :=
              WriteBorrowTargets.selected_branch_to_result_map
                (Nat.succ_pos rank) hwrites hleaves htargetMem
                (fun branchResult hbranchWrite =>
                  hindirect (Nat.succ_pos rank) htargetRank htargetTyping
                    htargetSelected hbranchWrite)
            exact ⟨hmap, PartialTyStrengthens.reflex,
              PartialTy.sameShape_refl _⟩
  case target =>
      intros
      trivial

theorem EnvSameShapeStrengthening.envStrengthens {source result : Env} :
    EnvSameShapeStrengthening source result →
    EnvStrengthens source result := by
  intro hmap x
  cases hsource : source.slotAt x with
  | none =>
      cases hresult : result.slotAt x with
      | none => trivial
      | some resultSlot =>
          rcases hmap.1 x resultSlot hresult with
            ⟨sourceSlot, hsourceSlot, _hlifetime, _hstrength, _hshape⟩
          rw [hsource] at hsourceSlot
          cases hsourceSlot
  | some sourceSlot =>
      cases hresult : result.slotAt x with
      | none =>
          rcases hmap.2 x sourceSlot hsource with
            ⟨resultSlot, hresultSlot, _hlifetime⟩
          rw [hresult] at hresultSlot
          cases hresultSlot
      | some resultSlot =>
          rcases hmap.1 x resultSlot hresult with
            ⟨mappedSourceSlot, hmappedSourceSlot, hlifetime, hstrength,
              _hshape⟩
          have hslotEq : mappedSourceSlot = sourceSlot :=
            Option.some.inj (hmappedSourceSlot.symm.trans hsource)
          subst hslotEq
          exact ⟨hlifetime, hstrength⟩

theorem RuntimeFrame.LocReads.typed_envMayReadThrough_prefix
    {store : ProgramStore} {env : Env} {target : LVal}
    {pt : PartialTy} {lifetime : Lifetime} {location : Location} :
    LValTyping env target pt lifetime →
    RuntimeFrame.LocReads store target location →
    ∃ readPrefix prefixTy prefixLifetime,
      LValTyping env readPrefix prefixTy prefixLifetime ∧
        store.loc readPrefix = some location ∧
        EnvMayReadThrough env readPrefix target := by
  intro htyping hreads
  induction hreads generalizing pt lifetime with
  | here hloc =>
      cases htyping with
      | box hsource =>
          exact ⟨_, _, _, hsource, hloc,
            EnvMayReadThrough.direct (LVal.StrictPrefixOf.self_deref _)⟩
      | boxFull hsource =>
          exact ⟨_, _, _, hsource, hloc,
            EnvMayReadThrough.direct (LVal.StrictPrefixOf.self_deref _)⟩
      | borrow hsource _htargets =>
          exact ⟨_, _, _, hsource, hloc,
            EnvMayReadThrough.direct (LVal.StrictPrefixOf.self_deref _)⟩
  | there _hreads ih =>
      cases htyping with
      | box hsource =>
          rcases ih hsource with
            ⟨readPrefix, prefixTy, prefixLifetime, hprefixTyping,
              hprefixLoc, hmayRead⟩
          exact ⟨readPrefix, prefixTy, prefixLifetime, hprefixTyping,
            hprefixLoc, EnvMayReadThrough.deref_right hmayRead⟩
      | boxFull hsource =>
          rcases ih hsource with
            ⟨readPrefix, prefixTy, prefixLifetime, hprefixTyping,
              hprefixLoc, hmayRead⟩
          exact ⟨readPrefix, prefixTy, prefixLifetime, hprefixTyping,
            hprefixLoc, EnvMayReadThrough.deref_right hmayRead⟩
      | borrow hsource _htargets =>
          rcases ih hsource with
            ⟨readPrefix, prefixTy, prefixLifetime, hprefixTyping,
              hprefixLoc, hmayRead⟩
          exact ⟨readPrefix, prefixTy, prefixLifetime, hprefixTyping,
            hprefixLoc, EnvMayReadThrough.deref_right hmayRead⟩

theorem LocationBelow.irrefl_whenInitialized {env : Env}
    {store : ProgramStore} {φ : Name → Nat}
    {location : Location} {slot : StoreSlot} {ty : PartialTy} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    store.slotAt location = some slot →
    ValidPartialValueWhenInitialized env store slot.value ty →
    ¬ LocationBelow store φ location location := by
  intro hvalid hheap hslot hvalidSlot hbelow
  rcases hbelow with ⟨r, r', hp, hp', hcase⟩
  have hrEq : r = r' := ProtectedByBase.root_unique hvalid hheap hp hp'
  subst hrEq
  rcases hcase with hlt | ⟨_heq, howns⟩
  · exact Nat.lt_irrefl _ hlt
  · exact ValidPartialValueWhenInitialized.no_storage_ownership_cycle
      hslot hvalidSlot howns

theorem StoreOwnerSpineWhenInitialized.leaf_slot {env : Env}
    {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf
      leafSlot leafTy →
    store.slotAt leaf = some leafSlot := by
  intro hspine
  induction hspine with
  | nil hslot _hvalid => exact hslot
  | box _hslot _howner _htail ih => exact ih
  | boxFull _hslot _howner _htail ih => exact ih

theorem lval_loc_var_slot_strengthens_whenInitialized
    {store : ProgramStore} {env : Env}
    {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {x : Name} {slot : EnvSlot} :
    SafeAbstractionWhenInitialized store env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv pt lifetime →
    store.loc lv = some (VariableProjection x) →
    env.slotAt x = some slot →
    PartialTyStrengthens slot.ty pt := by
  intro hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv pt _lifetime _ =>
      store.loc lv = some (VariableProjection x) →
      env.slotAt x = some slot →
      PartialTyStrengthens slot.ty pt)
    (motive_2 := fun targets pt _lifetime _ =>
      ∀ target, target ∈ targets →
        store.loc target = some (VariableProjection x) →
        env.slotAt x = some slot →
        PartialTyStrengthens slot.ty pt)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro y envSlot henvSlot hloc hxSlot
    simp [ProgramStore.loc, VariableProjection] at hloc
    cases hloc
    have hslotEq : slot = envSlot :=
      Option.some.inj (hxSlot.symm.trans henvSlot)
    subst hslotEq
    exact PartialTyStrengthens.reflex
  · intro source inner sourceLifetime hsource _ih hloc _hxSlot
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source (.box inner) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
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
  · intro source inner sourceLifetime hsource _ih hloc _hxSlot
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.box inner)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
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
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets _ihSource ihTargets hloc hxSlot
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrowLive selectedLocation _mutable _targets selected _hinit hmem
        hselectedLoc =>
        have hderefLoc : store.loc source.deref = some selectedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hselectedLocationEq :
            selectedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        have hselectedLocVar :
            store.loc selected = some (VariableProjection x) := by
          simpa [hselectedLocationEq] using hselectedLoc
        exact ihTargets selected hmem hselectedLocVar hxSlot
    | @borrowStale _location _mutable _targets hstale =>
        have hinitialized : BorrowTargetsInitialized env targets := by
          intro target hmem
          rcases lvalTargetsTyping_member_strengthens htargets target hmem with
            ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
          exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
        exact False.elim (hstale hinitialized)
  · intro target targetTy targetLifetime _htarget ihTarget selected hmem hloc
      hxSlot
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ihTarget hloc hxSlot
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest hunion _hintersection ihHead ihRest selected hmem hloc
      hxSlot
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst hhead
      exact partialTyStrengthens_trans_safe (ihHead hloc hxSlot)
        (PartialTyUnion.left_strengthens hunion)
    · exact partialTyStrengthens_trans_safe
        (ihRest selected htail hloc hxSlot)
        (PartialTyUnion.right_strengthens hunion)

theorem heapLeaf_spine_of_loc_whenInitialized {store : ProgramStore} {env : Env}
    {current : Lifetime} {φ : Name → Nat} {lv : LVal} {lvTy : Ty}
    {lifetime : Lifetime} {address : Nat} :
    LinearizedBy φ env →
    WellFormedEnvWhenInitialized env current →
    SafeAbstractionWhenInitialized store env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty lvTy) lifetime →
    store.loc lv = some (.heap address) →
    ∃ xRoot envSlot rootSlot spinePath leafSlot leafTy,
      env.slotAt xRoot = some envSlot ∧
      store.slotAt (VariableProjection xRoot) = some rootSlot ∧
      rootSlot.lifetime = envSlot.lifetime ∧
      StoreOwnerSpineWhenInitialized env store (VariableProjection xRoot)
        rootSlot envSlot.ty spinePath (.heap address) leafSlot (.ty leafTy) ∧
      spinePath ≠ [] := by
  intro hφ hwellFormed hsafe hheap htyping hloc
  rcases go hφ hwellFormed hsafe hheap htyping hloc with
    ⟨xRoot, envSlot, rootSlot, spinePath, leafSlot, leafPt, henvSlot,
      hrootSlot, hrootLifetime, hspine, hstrength, hnonempty⟩
  rcases PartialTyStrengthens.to_ty_right hstrength with ⟨leafTy, hleafPt⟩
  subst hleafPt
  exact ⟨xRoot, envSlot, rootSlot, spinePath, leafSlot, leafTy,
    henvSlot, hrootSlot, hrootLifetime, hspine, hnonempty⟩
where
  go {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {lv : LVal} {lvTy : Ty} {lifetime : Lifetime} {address : Nat}
      (hφ : LinearizedBy φ env)
      (hwellFormed : WellFormedEnvWhenInitialized env current)
      (hsafe : SafeAbstractionWhenInitialized store env)
      (hheap : StoreOwnerTargetsHeap store)
      (htyping : LValTyping env lv (.ty lvTy) lifetime)
      (hloc : store.loc lv = some (.heap address)) :
      ∃ xRoot envSlot rootSlot spinePath leafSlot leafPt,
        env.slotAt xRoot = some envSlot ∧
        store.slotAt (VariableProjection xRoot) = some rootSlot ∧
        rootSlot.lifetime = envSlot.lifetime ∧
        StoreOwnerSpineWhenInitialized env store (VariableProjection xRoot)
          rootSlot envSlot.ty spinePath (.heap address) leafSlot leafPt ∧
        PartialTyStrengthens leafPt (.ty lvTy) ∧
        spinePath ≠ [] := by
    cases lv with
    | var x =>
        simp [ProgramStore.loc] at hloc
    | deref u =>
        cases htyping with
        | @box _ _ sourceLifetime hsource =>
            rcases StoreOwnerSpineWhenInitialized.of_lvalTyping_box
                hwellFormed hsafe hsource with
              ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
                hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
                hsourceSpine⟩
            have hsourceValid :
                ValidPartialValueWhenInitialized env store sourceSlot.value
                  (.box (.ty lvTy)) :=
              StoreOwnerSpineWhenInitialized.leaf_valid hsourceSpine
            rcases sourceSlot with ⟨sourceValue, sourceLifetime'⟩
            cases hsourceValid with
            | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
                have hderefLoc :
                    store.loc (.deref u) = some ownerLocation := by
                  simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                have hlocEq : Location.heap address = ownerLocation := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                have hsnoc :
                    StoreOwnerSpineWhenInitialized env store
                      (VariableProjection (LVal.base u)) rootSlot
                      envSlot.ty (() :: LVal.path u) (.heap address)
                      ownerSlot (.ty lvTy) := by
                  have hsnoc' :=
                    StoreOwnerSpineWhenInitialized.snoc_box hsourceSpine rfl
                      rfl hownedSlot hinnerValid
                  simpa [hlocEq] using hsnoc'
                exact ⟨LVal.base u, envSlot, rootSlot, () :: LVal.path u,
                  ownerSlot, .ty lvTy, henvBase, hrootSlot, hrootLifetime,
                  hsnoc, PartialTyStrengthens.reflex, by simp⟩
        | @boxFull _ _ sourceLifetime hsource =>
            have hsourceAbs :
                LValLocationAbstractionWhenInitialized env store u
                  (.ty (.box lvTy)) :=
              lvalTyping_defined_location_whenInitialized hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, _hmiddleValid⟩
            cases middle with
            | var x =>
                have henvDomain :
                    ∃ envSlot, env.slotAt x = some envSlot :=
                  (hsafe.1 x).mp ⟨middleSlot, by
                    simpa [VariableProjection] using hmiddleSlot⟩
                rcases henvDomain with ⟨envSlot, henvSlot⟩
                rcases hsafe.2 x envSlot henvSlot with
                  ⟨rootValue, hrootStore, hrootValid⟩
                have hmiddleSlotEq :
                    middleSlot =
                      { value := rootValue,
                        lifetime := envSlot.lifetime } :=
                  Option.some.inj (hmiddleSlot.symm.trans
                    (by simpa [VariableProjection] using hrootStore))
                subst hmiddleSlotEq
                have hstrengthRoot :
                    PartialTyStrengthens envSlot.ty (.ty (.box lvTy)) :=
                  lval_loc_var_slot_strengthens_whenInitialized hsafe
                    hheap hsource
                    (by simpa [VariableProjection] using hmiddleLoc)
                    henvSlot
                rcases PartialTyStrengthens.to_ty_right hstrengthRoot with
                  ⟨rootTy, hrootTy⟩
                rw [hrootTy] at hstrengthRoot hrootValid
                rcases PartialTyStrengthens.to_box_ty_inv hstrengthRoot with
                  ⟨sourceInner, hrootTyEq, hinnerStrength⟩
                subst hrootTyEq
                have hrootValidBox :
                    ValidPartialValueWhenInitialized env store rootValue
                      (.ty (.box sourceInner)) := by
                  simpa using hrootValid
                cases hrootValidBox with
                | @boxFull ownerLocation ownerSlot _ hownedSlot hinnerValid =>
                    have hderefLoc :
                        store.loc (.deref u) = some ownerLocation := by
                      simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot,
                        owningRef]
                    have hlocEq : Location.heap address = ownerLocation := by
                      rw [hloc] at hderefLoc
                      exact Option.some.inj hderefLoc
                    have hbaseSpine :
                        StoreOwnerSpineWhenInitialized env store
                          (VariableProjection x)
                          { value := .value (owningRef ownerLocation),
                            lifetime := envSlot.lifetime }
                          (.ty (.box sourceInner)) [] (VariableProjection x)
                          { value := .value (owningRef ownerLocation),
                            lifetime := envSlot.lifetime }
                          (.ty (.box sourceInner)) := by
                      simpa [owningRef] using
                        (StoreOwnerSpineWhenInitialized.nil hrootStore
                          (ValidPartialValueWhenInitialized.boxFull
                            hownedSlot hinnerValid))
                    have hsnoc :
                        StoreOwnerSpineWhenInitialized env store
                          (VariableProjection x)
                          { value := .value (owningRef ownerLocation),
                            lifetime := envSlot.lifetime }
                          (.ty (.box sourceInner)) [()] (.heap address)
                          ownerSlot (.ty sourceInner) := by
                      simpa [hlocEq] using
                        StoreOwnerSpineWhenInitialized.snoc_boxFull
                          hbaseSpine rfl rfl hownedSlot hinnerValid
                    have hsnocEnv :
                        StoreOwnerSpineWhenInitialized env store
                          (VariableProjection x)
                          { value := .value (owningRef ownerLocation),
                            lifetime := envSlot.lifetime }
                          envSlot.ty [()] (.heap address)
                          ownerSlot (.ty sourceInner) := by
                      simpa [hrootTy] using hsnoc
                    exact ⟨x, envSlot,
                      { value := .value (owningRef ownerLocation),
                        lifetime := envSlot.lifetime },
                      [()], ownerSlot, .ty sourceInner, henvSlot,
                      by simpa [owningRef] using hrootStore, rfl, hsnocEnv,
                      hinnerStrength, by simp⟩
            | heap middleAddress =>
                rcases go hφ hwellFormed hsafe hheap hsource hmiddleLoc with
                  ⟨xRoot, envSlot, rootSlot, spinePath, middleLeafSlot,
                    middleLeafPt, henvSlot, hrootSlot, hrootLifetime,
                    hspineToMiddle, hmiddleStrength, hspineNonempty⟩
                rcases PartialTyStrengthens.to_ty_right hmiddleStrength with
                  ⟨middleLeafTy, hmiddleLeafPt⟩
                subst hmiddleLeafPt
                rcases PartialTyStrengthens.to_box_ty_inv hmiddleStrength with
                  ⟨sourceInner, hmiddleLeafTyEq, hinnerStrength⟩
                subst hmiddleLeafTyEq
                have hmiddleLeafValid :
                    ValidPartialValueWhenInitialized env store
                      middleLeafSlot.value (.ty (.box sourceInner)) :=
                  StoreOwnerSpineWhenInitialized.leaf_valid hspineToMiddle
                rcases middleLeafSlot with
                  ⟨middleLeafValue, middleLeafLifetime⟩
                cases hmiddleLeafValid with
                | @boxFull ownerLocation ownerSlot _ hownedSlot hinnerValid =>
                    have hderefLoc :
                        store.loc (.deref u) = some ownerLocation := by
                      have hmiddleLeafSlotAt :
                          store.slotAt (.heap middleAddress) =
                            some
                              { value := .value (owningRef ownerLocation),
                                lifetime := middleLeafLifetime } :=
                        StoreOwnerSpineWhenInitialized.leaf_slot hspineToMiddle
                      simp [ProgramStore.loc, hmiddleLoc, hmiddleLeafSlotAt,
                        owningRef]
                    have hlocEq : Location.heap address = ownerLocation := by
                      rw [hloc] at hderefLoc
                      exact Option.some.inj hderefLoc
                    have hsnoc :
                        StoreOwnerSpineWhenInitialized env store
                          (VariableProjection xRoot) rootSlot envSlot.ty
                          (() :: spinePath) (.heap address) ownerSlot
                          (.ty sourceInner) := by
                      have hsnoc' :=
                        StoreOwnerSpineWhenInitialized.snoc_boxFull
                          hspineToMiddle rfl rfl hownedSlot hinnerValid
                      simpa [hlocEq] using hsnoc'
                    exact ⟨xRoot, envSlot, rootSlot, () :: spinePath,
                      ownerSlot, .ty sourceInner, henvSlot, hrootSlot,
                      hrootLifetime, hsnoc, hinnerStrength, by simp⟩
        | @borrow _ mutable targets borrowLifetime targetLifetime targetTy
            hsource htargets =>
            have hsourceAbs :
                LValLocationAbstractionWhenInitialized env store u
                  (.ty (.borrow mutable targets)) :=
              lvalTyping_defined_location_whenInitialized hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            cases hmiddleValid with
            | @borrowLive targetLoc _mutable _targets witness _hinit hmem
                htargetLoc =>
                have hderefLoc : store.loc (.deref u) = some targetLoc := by
                  simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot]
                have hlocEq : Location.heap address = targetLoc := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                rcases lvalTargetsTyping_member_strengthens htargets witness
                    hmem with
                  ⟨witnessTy, witnessLifetime, hwitnessTyping,
                    hwitnessStrength⟩
                have hwitnessRank :
                    φ (LVal.base witness) < φ (LVal.base u) :=
                  (lvalTyping_vars_rank_lt hφ).1 hsource (LVal.base witness)
                    (by
                      simpa [PartialTy.vars, Ty.vars] using
                        List.mem_map_of_mem hmem)
                rcases go hφ hwellFormed hsafe hheap hwitnessTyping
                    (by rw [← hlocEq] at htargetLoc; exact htargetLoc) with
                  ⟨xRoot, envSlot, rootSlot, spinePath, leafSlot, leafPt,
                    henvSlot, hrootSlot, hrootLifetime, hspine, hstrength,
                    hnonempty⟩
                exact ⟨xRoot, envSlot, rootSlot, spinePath, leafSlot, leafPt,
                  henvSlot, hrootSlot, hrootLifetime, hspine,
                  partialTyStrengthens_trans_safe hstrength hwitnessStrength,
                  hnonempty⟩
            | @borrowStale _location _mutable _targets hstale =>
                have hinitialized : BorrowTargetsInitialized env targets := by
                  intro target hmem
                  rcases lvalTargetsTyping_member_strengthens htargets target
                      hmem with
                    ⟨selectedTy, selectedLifetime, hselectedTyping,
                      _hstrength⟩
                  exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
                exact False.elim (hstale hinitialized)
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)
theorem RuntimeFrame.loc_intrinsicRootView_whenInitialized
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {φ : Name → Nat} {lv : LVal} {pt : PartialTy}
    {lifetime : Lifetime} {location : Location} :
    LinearizedBy φ env →
    WellFormedEnvWhenInitialized env current →
    SafeAbstractionWhenInitialized store env →
    LValTyping env lv pt lifetime →
    store.loc lv = some location →
    ∃ root slotL viewTy slotLifetime,
      ProtectedByBase store root location ∧
      φ root ≤ φ (LVal.base lv) ∧
      store.slotAt location = some slotL ∧
      ValidPartialValueWhenInitialized env store slotL.value viewTy ∧
      PartialTyStrengthens viewTy pt ∧
      (∀ v, v ∈ PartialTy.vars viewTy → φ v < φ root) ∧
      PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime viewTy ∧
      (∀ {mutable : Bool} {targets : List LVal},
        PartialTyContains viewTy (.borrow mutable targets) →
        env ⊢ root ↝ (.borrow mutable targets)) := by
  intro hφ hwellFormed hsafe htyping hloc
  exact go hφ hwellFormed hsafe htyping hloc
where
  go {store : ProgramStore} {env : Env} {current : Lifetime}
      {φ : Name → Nat} {lv : LVal} {pt : PartialTy}
      {lifetime : Lifetime} {location : Location}
      (hφ : LinearizedBy φ env)
      (hwellFormed : WellFormedEnvWhenInitialized env current)
      (hsafe : SafeAbstractionWhenInitialized store env)
      (htyping : LValTyping env lv pt lifetime)
      (hloc : store.loc lv = some location) :
      ∃ root slotL viewTy slotLifetime,
        ProtectedByBase store root location ∧
        φ root ≤ φ (LVal.base lv) ∧
        store.slotAt location = some slotL ∧
        ValidPartialValueWhenInitialized env store slotL.value viewTy ∧
        PartialTyStrengthens viewTy pt ∧
        (∀ v, v ∈ PartialTy.vars viewTy → φ v < φ root) ∧
        PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime viewTy ∧
        (∀ {mutable : Bool} {targets : List LVal},
          PartialTyContains viewTy (.borrow mutable targets) →
          env ⊢ root ↝ (.borrow mutable targets)) := by
    cases lv with
    | var x =>
        cases htyping with
        | @var _ slot hslot =>
            have hlocEq : location = VariableProjection x := by
              simp [ProgramStore.loc] at hloc
              exact hloc.symm
            subst hlocEq
            rcases hsafe.2 x slot hslot with ⟨value, hstoreSlot, hvalid⟩
            refine ⟨x, _, slot.ty, slot.lifetime, Or.inl rfl, le_refl _,
              hstoreSlot, hvalid, PartialTyStrengthens.reflex,
              hφ x slot hslot, ?_, ?_⟩
            · intro mutable targets hcontains
              exact hwellFormed.1 x slot mutable targets hslot
                ⟨slot, hslot, hcontains⟩
            · intro mutable targets hcontains
              exact ⟨slot, hslot, hcontains⟩
    | deref u =>
        cases htyping with
        | box hsource =>
            have hsourceAbs :
                LValLocationAbstractionWhenInitialized env store u (.box _) :=
              lvalTyping_defined_location_whenInitialized hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            rcases go hφ hwellFormed hsafe hsource hmiddleLoc with
              ⟨root, slotM, viewTyM, slotLt, hprotM, hrank, hslotM,
                hvalidM, hstrengthM, hbound, hborrowsM, hcontainsM⟩
            have hslotMEq :
                slotM = ⟨middleValue, middleLifetime⟩ :=
              Option.some.inj (hslotM.symm.trans hmiddleSlot)
            subst hslotMEq
            cases hmiddleValid with
            | @box owned ownedSlot _ hownedSlot _hinnerValid =>
                have hderefLoc : store.loc (.deref u) = some owned := by
                  simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot]
                have hlocEq : location = owned := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                have hownsAt :
                    ProgramStore.OwnsAt store location middle :=
                  ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
                cases hvalidM with
                | @box owned₂ ownedSlot₂ innerView hownedSlot₂ hinnerView =>
                    refine ⟨root, ownedSlot₂, innerView, slotLt,
                      ProtectedByBase.trans_owned hprotM hownsAt,
                      hrank, hownedSlot₂, hinnerView, ?_, ?_, ?_, ?_⟩
                    · cases hstrengthM with
                      | reflex => exact PartialTyStrengthens.reflex
                      | box hinnerStrength => exact hinnerStrength
                    · intro v hv
                      exact hbound v (by simpa [PartialTy.vars] using hv)
                    · intro mutable targets hcontains
                      exact hborrowsM (PartialTyContains.box hcontains)
                    · intro mutable targets hcontains
                      exact hcontainsM (PartialTyContains.box hcontains)
                | @boxFull owned₂ ownedSlot₂ innerTy hownedSlot₂ hinnerView =>
                    cases hstrengthM
                | @undefOf _ _ hiddenOuter hskel hstrength =>
                    cases hstrengthM
        | boxFull hsource =>
            have hsourceAbs :
                LValLocationAbstractionWhenInitialized env store u (.ty (.box _)) :=
              lvalTyping_defined_location_whenInitialized hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            rcases go hφ hwellFormed hsafe hsource hmiddleLoc with
              ⟨root, slotM, viewTyM, slotLt, hprotM, hrank, hslotM,
                hvalidM, hstrengthM, hbound, hborrowsM, hcontainsM⟩
            have hslotMEq :
                slotM = ⟨middleValue, middleLifetime⟩ :=
              Option.some.inj (hslotM.symm.trans hmiddleSlot)
            subst hslotMEq
            cases hmiddleValid with
            | @boxFull owned ownedSlot _ hownedSlot _hinnerValid =>
                have hderefLoc : store.loc (.deref u) = some owned := by
                  simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot]
                have hlocEq : location = owned := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                have hownsAt :
                    ProgramStore.OwnsAt store location middle :=
                  ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
                cases hvalidM with
                | @box owned₂ ownedSlot₂ innerView hownedSlot₂ hinnerView =>
                    cases hstrengthM
                | @boxFull owned₂ ownedSlot₂ innerView hownedSlot₂ hinnerView =>
                    refine ⟨root, ownedSlot₂, .ty innerView, slotLt,
                      ProtectedByBase.trans_owned hprotM hownsAt,
                      hrank, hownedSlot₂, hinnerView, ?_, ?_, ?_, ?_⟩
                    · cases hstrengthM with
                      | reflex => exact PartialTyStrengthens.reflex
                      | tyBox hinnerStrength => exact hinnerStrength
                    · intro v hv
                      exact hbound v (by simpa [PartialTy.vars, Ty.vars] using hv)
                    · intro mutable targets hcontains
                      exact hborrowsM (PartialTyContains.tyBox hcontains)
                    · intro mutable targets hcontains
                      exact hcontainsM (PartialTyContains.tyBox hcontains)
                | @undefOf _ _ hiddenOuter hskel hstrength =>
                    cases hstrengthM
        | @borrow _ mutable targets borrowLifetime targetLifetime targetTy
            hsource htargets =>
            have hsourceAbs :
                LValLocationAbstractionWhenInitialized env store u
                  (.ty (.borrow mutable targets)) :=
              lvalTyping_defined_location_whenInitialized hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            rcases go hφ hwellFormed hsafe hsource hmiddleLoc with
              ⟨root, slotM, viewTyM, slotLt, hprotM, hrank, hslotM,
                hvalidM, hstrengthM, hbound, hborrowsM, hcontainsM⟩
            have hslotMEq :
                slotM = ⟨middleValue, middleLifetime⟩ :=
              Option.some.inj (hslotM.symm.trans hmiddleSlot)
            subst hslotMEq
            cases hvalidM with
            | @borrowLive target₀Loc mutable' targets' target₀ _hinitialized
                hmem₀ htarget₀Loc =>
                have htargetMem : target₀ ∈ targets := by
                  cases hstrengthM with
                  | reflex => exact hmem₀
                  | borrow hsubset => exact hsubset hmem₀
                have hderefLoc : store.loc (.deref u) = some target₀Loc := by
                  simp [ProgramStore.loc, hmiddleLoc, hslotM]
                have hlocEq : location = target₀Loc := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                rcases lvalTargetsTyping_member_strengthens htargets target₀
                    htargetMem with
                  ⟨selectedTy, selectedLifetime, htargetTyping,
                    hselectedStrengthens⟩
                have htargetRank :
                    φ (LVal.base target₀) < φ (LVal.base u) := by
                  exact (lvalTyping_vars_rank_lt hφ).1 hsource
                    (LVal.base target₀)
                    (by
                      simpa [PartialTy.vars, Ty.vars] using
                        List.mem_map_of_mem htargetMem)
                rcases go hφ hwellFormed hsafe htargetTyping htarget₀Loc with
                  ⟨root₂, slotL, viewTy, slotLt₂, hprot₂, hrank₂, hslotL,
                    hvalidL, hstrengthL, hbound₂, hborrows₂,
                    hcontains₂⟩
                exact ⟨root₂, slotL, viewTy, slotLt₂, hprot₂,
                  le_of_lt (lt_of_le_of_lt hrank₂ htargetRank),
                  hslotL, hvalidL,
                  partialTyStrengthens_trans_safe hstrengthL
                    hselectedStrengthens,
                  hbound₂, hborrows₂, hcontains₂⟩
            | @borrowStale target₀Loc mutable' targets' hnotInitialized =>
                have hinitialized : BorrowTargetsInitialized env targets' := by
                  intro target htarget
                  have htargetMem : target ∈ targets := by
                    cases hstrengthM with
                    | reflex => exact htarget
                    | borrow hsubset => exact hsubset htarget
                  rcases lvalTargetsTyping_member_strengthens htargets target
                      htargetMem with
                    ⟨targetTy, targetLifetime, htargetTyping, _hstrength⟩
                  exact ⟨targetTy, targetLifetime, htargetTyping⟩
                exact False.elim (hnotInitialized hinitialized)
            | unit | int | bool | undef =>
                cases hstrengthM
            | @box owned ownedSlot innerView hownedSlot hinnerView =>
                cases hstrengthM
            | @boxFull owned ownedSlot innerTy hownedSlot hinnerView =>
                cases hstrengthM
            | @undefOf _ _ hiddenOuter hskel hstrength =>
                cases hstrengthM
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)
theorem RuntimeFrame.borrowDependencyWhenInitialized_witness {env : Env}
    {store : ProgramStore} {value : PartialValue} {partialTy : PartialTy}
    {dependency : Location} :
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy
      dependency →
    ∃ mutable targets target,
      BorrowTargetsInitialized env targets ∧
      PartialTyContains partialTy (.borrow mutable targets) ∧
      target ∈ targets ∧
      RuntimeFrame.LocReads store target dependency := by
  intro hdep
  induction hdep with
  | @borrow location readLocation mutable targets target hinitialized hmem _hloc
      hreads =>
      exact ⟨mutable, targets, target, hinitialized, PartialTyContains.here,
        hmem, hreads⟩
  | boxInner _hslot _hinner ih =>
      rcases ih with ⟨m, ts, t, hinitialized, hcontains, hmem, hreads⟩
      exact ⟨m, ts, t, hinitialized, PartialTyContains.box hcontains, hmem,
        hreads⟩
  | boxFullInner _hslot _hinner ih =>
      rcases ih with ⟨m, ts, t, hinitialized, hcontains, hmem, hreads⟩
      exact ⟨m, ts, t, hinitialized, PartialTyContains.tyBox hcontains, hmem,
        hreads⟩

theorem StoreOwnerSpineWhenInitialized.path_unique {env₁ env₂ : Env}
    {store : ProgramStore}
    {storage leaf : Location} {slot₁ : StoreSlot} {ty₁ leafTy₁ : PartialTy}
    {leafSlot₁ : StoreSlot} {path₁ : Path} :
    StoreOwnerSpineWhenInitialized env₁ store storage slot₁ ty₁ path₁ leaf
      leafSlot₁ leafTy₁ →
    ∀ {slot₂ : StoreSlot} {ty₂ leafTy₂ : PartialTy} {leafSlot₂ : StoreSlot}
      {path₂ : Path},
      StoreOwnerSpineWhenInitialized env₂ store storage slot₂ ty₂ path₂ leaf
        leafSlot₂ leafTy₂ →
      path₁ = path₂ := by
  intro h₁
  induction h₁ with
  | nil hslot _hvalid =>
      intro slot₂ ty₂ leafTy₂ leafSlot₂ path₂ h₂
      cases h₂ with
      | nil _ _ => rfl
      | box hslot₂ howner₂ htail₂ =>
          exact absurd rfl
            (StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons
              (StoreOwnerSpineWhenInitialized.box hslot₂ howner₂ htail₂))
      | boxFull hslot₂ howner₂ htail₂ =>
          exact absurd rfl
            (StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons
              (StoreOwnerSpineWhenInitialized.boxFull hslot₂ howner₂ htail₂))
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro slot₂ ty₂ leafTy₂ leafSlot₂ path₂ h₂
      cases h₂ with
      | nil hslot₂ _ =>
          exact absurd rfl
            (StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons
              (StoreOwnerSpineWhenInitialized.box hslot howner htail))
      | @box _ owned₂ _ _ ownedSlot₂ _ inner₂ _ path₂' hslot₂ howner₂
          htail₂ =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          have hownedEq : owned = owned₂ := by
            have hvalueEq :
                PartialValue.value (owningRef owned) =
                  PartialValue.value (owningRef owned₂) := by
              rw [← howner, hslotEq, howner₂]
            simpa [owningRef] using hvalueEq
          subst hownedEq
          rw [ih htail₂]
      | @boxFull _ owned₂ _ _ ownedSlot₂ _ inner₂ _ path₂' hslot₂ howner₂
          htail₂ =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          have hownedEq : owned = owned₂ := by
            have hvalueEq :
                PartialValue.value (owningRef owned) =
                  PartialValue.value (owningRef owned₂) := by
              rw [← howner, hslotEq, howner₂]
            simpa [owningRef] using hvalueEq
          subst hownedEq
          rw [ih htail₂]
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro slot₂ ty₂ leafTy₂ leafSlot₂ path₂ h₂
      cases h₂ with
      | nil hslot₂ _ =>
          exact absurd rfl
            (StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons
              (StoreOwnerSpineWhenInitialized.boxFull hslot howner htail))
      | @box _ owned₂ _ _ ownedSlot₂ _ inner₂ _ path₂' hslot₂ howner₂
          htail₂ =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          have hownedEq : owned = owned₂ := by
            have hvalueEq :
                PartialValue.value (owningRef owned) =
                  PartialValue.value (owningRef owned₂) := by
              rw [← howner, hslotEq, howner₂]
            simpa [owningRef] using hvalueEq
          subst hownedEq
          rw [ih htail₂]
      | @boxFull _ owned₂ _ _ ownedSlot₂ _ inner₂ _ path₂' hslot₂ howner₂
          htail₂ =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          have hownedEq : owned = owned₂ := by
            have hvalueEq :
                PartialValue.value (owningRef owned) =
                  PartialValue.value (owningRef owned₂) := by
              rw [← howner, hslotEq, howner₂]
            simpa [owningRef] using hvalueEq
          subst hownedEq
          rw [ih htail₂]

theorem StoreOwnerSpineWhenInitialized.lval_eq_of_same_leaf
    {store : ProgramStore} {env₁ env₂ : Env} {left right : LVal}
    {leftRootSlot rightRootSlot leftLeafSlot rightLeafSlot : StoreSlot}
    {leftRootTy rightRootTy leftLeafTy rightLeafTy : PartialTy}
    {leaf : Location} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    StoreOwnerSpineWhenInitialized env₁ store
      (VariableProjection (LVal.base left)) leftRootSlot leftRootTy
      (LVal.path left) leaf leftLeafSlot leftLeafTy →
    StoreOwnerSpineWhenInitialized env₂ store
      (VariableProjection (LVal.base right)) rightRootSlot rightRootTy
      (LVal.path right) leaf rightLeafSlot rightLeafTy →
    left = right := by
  intro hvalidStore hheap hleft hright
  have hleftProtected :
      ProtectedByBase store (LVal.base left) leaf :=
    StoreOwnerSpineWhenInitialized.leaf_protected_by_base hleft rfl
  have hrightProtected :
      ProtectedByBase store (LVal.base right) leaf :=
    StoreOwnerSpineWhenInitialized.leaf_protected_by_base hright rfl
  have hbase :
      LVal.base left = LVal.base right :=
    ProtectedByBase.root_unique hvalidStore hheap hleftProtected
      hrightProtected
  have hpath :
      LVal.path left = LVal.path right := by
    have hleft' :
        StoreOwnerSpineWhenInitialized env₁ store
          (VariableProjection (LVal.base right)) leftRootSlot leftRootTy
          (LVal.path left) leaf leftLeafSlot leftLeafTy := by
      simpa [hbase] using hleft
    exact StoreOwnerSpineWhenInitialized.path_unique hleft' hright
  exact LVal.eq_of_base_path hbase hpath

namespace StoreOwnerSpineWhenInitialized

theorem valid_after_leaf_strong_update {env : Env} {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} {path : Path} {value : Value} {rhsTy : Ty}
    {newSlot : StoreSlot} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf leafSlot
      leafTy →
    path ≠ [] →
    newSlot.value = .value value →
    ValidPartialValueWhenInitialized env (store.update leaf newSlot)
      (.value value) (.ty rhsTy) →
    ValidPartialValueWhenInitialized env (store.update leaf newSlot) slot.value
      (PartialTy.strongLeafUpdate ty path rhsTy) := by
  intro hspine hpath hnewValue hnewValid
  induction hspine with
  | nil _hslot _hvalid =>
      exact absurd rfl hpath
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases htail with
      | nil hleafSlot _hleafValid =>
          rw [howner]
          have hnewSlotAt :
              (store.update owned newSlot).slotAt owned = some newSlot := by
            simp [ProgramStore.update]
          have hnewSlotValid :
              ValidPartialValueWhenInitialized env (store.update owned newSlot)
                newSlot.value (.ty rhsTy) := by
            rw [hnewValue]
            exact hnewValid
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            ValidPartialValueWhenInitialized.box hnewSlotAt hnewSlotValid
      | box hslot₂ howner₂ htail₂ =>
          rw [howner]
          have htailSpine :
              StoreOwnerSpineWhenInitialized env store owned ownedSlot _
                (() :: _) leaf leafSlot leafTy :=
            StoreOwnerSpineWhenInitialized.box hslot₂ howner₂ htail₂
          have htailValid :=
            ih (by simp) hnewValid
          have hleafNeOwned : leaf ≠ owned :=
            StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons htailSpine
          have hownedNeLeaf : owned ≠ leaf := fun h => hleafNeOwned h.symm
          have hownedSlotAt :
              (store.update leaf newSlot).slotAt owned = some ownedSlot := by
            rw [RuntimeFrame.ProgramStore.slotAt_update_ne hownedNeLeaf]
            exact StoreOwnerSpineWhenInitialized.storage_slot htailSpine
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            ValidPartialValueWhenInitialized.box hownedSlotAt htailValid
      | boxFull hslot₂ howner₂ htail₂ =>
          rw [howner]
          have htailSpine :
              StoreOwnerSpineWhenInitialized env store owned ownedSlot _
                (() :: _) leaf leafSlot leafTy :=
            StoreOwnerSpineWhenInitialized.boxFull hslot₂ howner₂ htail₂
          have htailValid :=
            ih (by simp) hnewValid
          have hleafNeOwned : leaf ≠ owned :=
            StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons htailSpine
          have hownedNeLeaf : owned ≠ leaf := fun h => hleafNeOwned h.symm
          have hownedSlotAt :
              (store.update leaf newSlot).slotAt owned = some ownedSlot := by
            rw [RuntimeFrame.ProgramStore.slotAt_update_ne hownedNeLeaf]
            exact StoreOwnerSpineWhenInitialized.storage_slot htailSpine
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            ValidPartialValueWhenInitialized.box hownedSlotAt htailValid
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases htail with
      | nil hleafSlot _hleafValid =>
          rw [howner]
          have hnewSlotAt :
              (store.update owned newSlot).slotAt owned = some newSlot := by
            simp [ProgramStore.update]
          have hnewSlotValid :
              ValidPartialValueWhenInitialized env (store.update owned newSlot)
                newSlot.value (.ty rhsTy) := by
            rw [hnewValue]
            exact hnewValid
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            StoreOwnerSpineWhenInitialized.valid_rebox hnewSlotAt hnewSlotValid
      | boxFull hslot₂ howner₂ htail₂ =>
          rw [howner]
          have htailSpine :
              StoreOwnerSpineWhenInitialized env store owned ownedSlot _
                (() :: _) leaf leafSlot leafTy :=
            StoreOwnerSpineWhenInitialized.boxFull hslot₂ howner₂ htail₂
          have htailValid :=
            ih (by simp) hnewValid
          have hleafNeOwned : leaf ≠ owned :=
            StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons htailSpine
          have hownedNeLeaf : owned ≠ leaf := fun h => hleafNeOwned h.symm
          have hownedSlotAt :
              (store.update leaf newSlot).slotAt owned = some ownedSlot := by
            rw [RuntimeFrame.ProgramStore.slotAt_update_ne hownedNeLeaf]
            exact StoreOwnerSpineWhenInitialized.storage_slot htailSpine
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            StoreOwnerSpineWhenInitialized.valid_rebox hownedSlotAt htailValid

theorem strongLeafUpdate_strengthens_updateAtPath {env writeEnv : Env}
    {store : ProgramStore} {rank : Nat}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy updatedTy : PartialTy} {oldLeafTy rhsTy : Ty} {path : Path} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf leafSlot
      leafTy →
    leafTy = .ty oldLeafTy →
    UpdateAtPath rank env path ty rhsTy writeEnv updatedTy →
    PartialTyStrengthens (PartialTy.strongLeafUpdate ty path rhsTy)
      updatedTy ∧
      PartialTy.sameShape (PartialTy.strongLeafUpdate ty path rhsTy)
        updatedTy := by
  intro hspine hleafTy hupdate
  induction hspine generalizing rank writeEnv updatedTy oldLeafTy with
  | nil _hslot _hvalid =>
      subst hleafTy
      cases hupdate with
      | strong =>
          exact ⟨by
              simpa [PartialTy.strongLeafUpdate] using
                (PartialTyStrengthens.reflex (ty := PartialTy.ty rhsTy)),
            by
              simpa [PartialTy.strongLeafUpdate] using
                PartialTy.sameShape_refl (PartialTy.ty rhsTy)⟩
      | weak hshape hjoin =>
          constructor
          · simpa [PartialTy.strongLeafUpdate] using
              PartialTyUnion.right_strengthens hjoin
          · have hshapeOldJoined :
                PartialTy.sameShape (.ty oldLeafTy) updatedTy :=
              partialTyJoin_ty_left_sameShape hjoin
            have hshapeRhsOld :
                PartialTy.sameShape (.ty rhsTy) (.ty oldLeafTy) :=
              PartialTy.sameShape_symm
                (PartialTy.sameShape_of_shapeCompatible hshape)
            simpa [PartialTy.strongLeafUpdate] using
              PartialTy.sameShape_trans hshapeRhsOld hshapeOldJoined
  | @box storage owned leaf slot ownedSlot leafSlot spineInner leafTy path
      hslot howner htail ih =>
      cases hupdate with
      | @box _env₁ _env₂ _rank _path _inner updatedInner _ty hinnerUpdate =>
          rcases ih hleafTy hinnerUpdate with ⟨hstr, hshape⟩
          constructor
          · change
              PartialTyStrengthens
                (.box (PartialTy.strongLeafUpdate spineInner path rhsTy))
                (.box updatedInner)
            exact PartialTyStrengthens.box hstr
          · change
              PartialTy.sameShape
                (.box (PartialTy.strongLeafUpdate spineInner path rhsTy))
                (.box updatedInner)
            simpa [PartialTy.sameShape] using hshape
  | @boxFull storage owned leaf slot ownedSlot leafSlot spineInner leafTy path
      hslot howner htail ih =>
      cases hupdate with
      | @boxFull _env₁ _env₂ _rank _path _inner updatedInner _ty hinnerUpdate =>
          rcases ih hleafTy hinnerUpdate with ⟨hstr, hshape⟩
          constructor
          · change
              PartialTyStrengthens
                (partialTyRebox
                  (PartialTy.strongLeafUpdate (.ty spineInner) path rhsTy))
                (partialTyRebox updatedInner)
            exact PartialTyStrengthens.rebox hstr hshape
          · change
              PartialTy.sameShape
                (partialTyRebox
                  (PartialTy.strongLeafUpdate (.ty spineInner) path rhsTy))
                (partialTyRebox updatedInner)
            exact PartialTy.sameShape_rebox hshape

theorem strongLeafUpdate_contains {env : Env} {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} {path : Path} {rhsTy needle : Ty} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf leafSlot
      leafTy →
    PartialTyContains (.ty rhsTy) needle →
    PartialTyContains (PartialTy.strongLeafUpdate ty path rhsTy) needle := by
  intro hspine hcontains
  induction hspine with
  | nil _ _ =>
      simpa [PartialTy.strongLeafUpdate] using hcontains
  | box _hslot _howner _htail ih =>
      simpa [PartialTy.strongLeafUpdate] using PartialTyContains.box ih
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      have hinner :
          PartialTyContains (PartialTy.strongLeafUpdate (.ty inner) path rhsTy)
            needle :=
        ih
      generalize hupdated :
        PartialTy.strongLeafUpdate (.ty inner) path rhsTy = updated at hinner ⊢
      cases updated with
      | ty updatedInner =>
          simpa [PartialTy.strongLeafUpdate, hupdated, partialTyRebox] using
            PartialTyContains.tyBox hinner
      | box updatedInner =>
          simpa [PartialTy.strongLeafUpdate, hupdated, partialTyRebox] using
            PartialTyContains.box hinner
      | undef updatedInner =>
          cases hinner

theorem updateAtPath_env_eq {env writeEnv : Env}
    {store : ProgramStore} {rank : Nat}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {path : Path}
    {rhsTy : Ty} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf
      leafSlot leafTy →
    UpdateAtPath rank env path rootTy rhsTy writeEnv updatedTy →
    writeEnv = env := by
  intro hspine hupdate
  induction hspine generalizing writeEnv updatedTy rhsTy rank with
  | nil _hslot _hvalid =>
      cases hupdate with
      | strong | weak _hshape _hjoin => rfl
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | box hinner =>
          exact ih hinner
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | boxFull hinner =>
          exact ih hinner

theorem contains_leafTy {env : Env} {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} {path : Path} {mutable : Bool}
    {targets : List LVal} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf leafSlot
      leafTy →
    leafTy = .ty (.borrow mutable targets) →
    PartialTyContains ty (.borrow mutable targets) := by
  intro hspine
  induction hspine with
  | nil _ _ =>
      intro h
      subst h
      exact PartialTyContains.here
  | box _hslot _howner _htail ih =>
      intro h
      exact PartialTyContains.box (ih h)
  | boxFull _hslot _howner _htail ih =>
      intro h
      exact PartialTyContains.tyBox (ih h)

theorem updateAtPath_node_fanout {env writeEnv : Env}
    {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy updatedTy : PartialTy} {mutable : Bool} {targets : List LVal}
    {spinePath suffix : List Unit} {rank : Nat} {rhsTy : Ty} :
    StoreOwnerSpineWhenInitialized env store storage slot ty spinePath leaf
      leafSlot leafTy →
    leafTy = .ty (.borrow mutable targets) →
    UpdateAtPath rank env (spinePath ++ (() :: suffix)) ty rhsTy writeEnv
      updatedTy →
    mutable = true ∧
      ∃ env₂, WriteBorrowTargets (rank + 1) env suffix targets rhsTy env₂ := by
  intro hspine
  induction hspine generalizing rank writeEnv updatedTy mutable targets with
  | nil _hslot _hvalid =>
      intro hleafTy hupdate
      subst hleafTy
      rcases UpdateAtPath.cons_inv (by simpa using hupdate) with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, hwrites⟩
        cases htyEq
        exact ⟨rfl, ⟨writeEnv, hwrites⟩⟩
  | box _hslot _howner _htail ih =>
      intro hleafTy hupdate
      rcases UpdateAtPath.cons_inv (by simpa [List.cons_append] using hupdate) with
        hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            hinner⟩
          cases htyEq
          exact ih hleafTy hinner
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  | boxFull _hslot _howner _htail ih =>
      intro hleafTy hupdate
      rcases UpdateAtPath.cons_inv (by simpa [List.cons_append] using hupdate) with
        hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            hinner⟩
          cases htyEq
          exact ih hleafTy hinner
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
theorem updateAtPathEffective_node_fanout_passthrough {env writeEnv : Env}
    {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} {targets : List LVal}
    {spinePath suffix : List Unit} {rank : Nat} {rhsTy : Ty}
    {updatedTy : PartialTy} {base : Name} {P : LVal → Prop} :
    StoreOwnerSpineWhenInitialized env store storage slot ty spinePath leaf
      leafSlot leafTy →
    leafTy = .ty (.borrow true targets) →
    UpdateAtPath rank env (spinePath ++ (() :: suffix)) ty rhsTy writeEnv
      updatedTy →
    (∀ branchEnv,
      WriteBorrowTargets (rank + 1) env suffix targets rhsTy branchEnv →
      ∃ written,
        WriteBorrowTargetsEffectiveWrite (rank + 1) env suffix targets rhsTy
          branchEnv written ∧
          P written) →
    ∃ written,
      UpdateAtPathEffectiveWrite rank env base
        (spinePath ++ (() :: suffix)) ty rhsTy writeEnv updatedTy written ∧
        P written := by
  intro hspine
  induction hspine generalizing rank writeEnv updatedTy targets with
  | nil _hslot _hvalid =>
      intro hleafTy hupdate hfanout
      subst hleafTy
      rcases UpdateAtPath.cons_inv (by simpa using hupdate) with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        cases hupdatedEq
        rcases hfanout writeEnv hwrites with ⟨written, heffective, hP⟩
        exact ⟨written, UpdateAtPathEffectiveWrite.mutBorrow heffective, hP⟩
  | box _hslot _howner _htail ih =>
      intro hleafTy hupdate hfanout
      rcases UpdateAtPath.cons_inv (by simpa [List.cons_append] using hupdate) with
        hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, hupdatedEq,
            hinner⟩
          cases htyEq
          cases hupdatedEq
          rcases ih hleafTy hinner hfanout with
            ⟨written, heffective, hP⟩
          exact ⟨written, UpdateAtPathEffectiveWrite.boxPassthrough heffective,
            hP⟩
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  | boxFull _hslot _howner _htail ih =>
      intro hleafTy hupdate hfanout
      rcases UpdateAtPath.cons_inv (by simpa [List.cons_append] using hupdate) with
        hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, hupdatedEq,
            hinner⟩
          cases htyEq
          cases hupdatedEq
          rcases ih hleafTy hinner hfanout with
            ⟨written, heffective, hP⟩
          exact ⟨written,
            UpdateAtPathEffectiveWrite.boxFullPassthrough heffective, hP⟩
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
theorem updateAtPathEffective_leaf_self {env writeEnv : Env}
    {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy updatedTy : PartialTy} {path : Path}
    {rank : Nat} {rhsTy : Ty} {base : Name} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf leafSlot
      leafTy →
    UpdateAtPath rank env path ty rhsTy writeEnv updatedTy →
    UpdateAtPathEffectiveWrite rank env base path ty rhsTy writeEnv updatedTy
      (prependPath path (.var base)) := by
  intro hspine
  induction hspine generalizing writeEnv updatedTy rhsTy rank base with
  | nil _hslot _hvalid =>
      intro hupdate
      cases hupdate with
      | strong =>
          simpa [prependPath] using
            (UpdateAtPathEffectiveWrite.strong
              (env := env) (base := base))
      | weak hshape hjoin =>
          simpa [prependPath] using
            (UpdateAtPathEffectiveWrite.weak
              (env := env) (base := base) hshape hjoin)
  | box _hslot _howner _htail ih =>
      intro hupdate
      cases hupdate with
      | box hinner =>
          simpa [prependPath] using
            (UpdateAtPathEffectiveWrite.box
              (ih (writeEnv := writeEnv) (rhsTy := rhsTy)
                (base := base) hinner))
  | boxFull _hslot _howner _htail ih =>
      intro hupdate
      cases hupdate with
      | boxFull hinner =>
          simpa [prependPath] using
            (UpdateAtPathEffectiveWrite.boxFull
              (ih (writeEnv := writeEnv) (rhsTy := rhsTy)
                (base := base) hinner))

end StoreOwnerSpineWhenInitialized

theorem EnvWrite.effectiveWrite_ownerSpine_whenInitialized_self
    {store : ProgramStore} {env result : Env}
    {writeLifetime : Lifetime} {lv : LVal}
    {lvTy rhsTy : Ty} {rank : Nat}
    {envSlot : EnvSlot} {rootSlot leafSlot : StoreSlot} {leaf : Location} :
    LValTyping env lv (.ty lvTy) writeLifetime →
    env.slotAt (LVal.base lv) = some envSlot →
    store.slotAt (VariableProjection (LVal.base lv)) = some rootSlot →
    StoreOwnerSpineWhenInitialized env store
      (VariableProjection (LVal.base lv)) rootSlot
      envSlot.ty (LVal.path lv) leaf leafSlot (.ty lvTy) →
    EnvWrite rank env lv rhsTy result →
    EnvWriteEffectiveWrite rank env lv rhsTy result lv := by
  intro _hLv henvSlot _hrootSlot hspine hwrite
  cases hwrite with
  | @intro _rank _env₁ writeEnv _writeLv writeSlot _ty updatedTy
      hwriteSlot hupdate =>
      have hslotEq : writeSlot = envSlot :=
        Option.some.inj (hwriteSlot.symm.trans henvSlot)
      subst writeSlot
      have heffective :
          UpdateAtPathEffectiveWrite rank env (LVal.base lv) (LVal.path lv)
            envSlot.ty rhsTy writeEnv updatedTy
            (prependPath (LVal.path lv) (.var (LVal.base lv))) :=
        StoreOwnerSpineWhenInitialized.updateAtPathEffective_leaf_self
          (base := LVal.base lv) hspine hupdate
      have hlvEq :
          prependPath (LVal.path lv) (.var (LVal.base lv)) = lv := by
        apply LVal.eq_of_base_path
        · simp [LVal.base]
        · simp [LVal.path]
      rw [hlvEq] at heffective
      exact EnvWriteEffectiveWrite.intro henvSlot heffective

theorem firstNodePack_whenInitialized {store : ProgramStore} {env : Env}
    {current : Lifetime}
    {source : LVal} {mutable : Bool} {targets : List LVal}
    {sourceLifetime targetLifetime : Lifetime} {targetTy : PartialTy}
    {res : Location} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstractionWhenInitialized store env →
    LValTyping env source (.ty (.borrow mutable targets)) sourceLifetime →
    LValTargetsTyping env targets targetTy targetLifetime →
    store.loc (.deref source) = some res →
    ∃ envSlot rootValue cell cellSlot L m ts spinePath suffix u₀,
      env.slotAt (LVal.base source) = some envSlot ∧
      store.slotAt (VariableProjection (LVal.base source)) =
        some { value := rootValue, lifetime := envSlot.lifetime } ∧
      store.slotAt cell = some cellSlot ∧
      cellSlot.value = .value (.ref { location := L, owner := false }) ∧
      ValidPartialValueWhenInitialized env store cellSlot.value
        (.ty (.borrow m ts)) ∧
      BorrowTargetsInitialized env ts ∧
      StoreOwnerSpineWhenInitialized env store
        (VariableProjection (LVal.base source))
        { value := rootValue, lifetime := envSlot.lifetime } envSlot.ty
        spinePath cell cellSlot (.ty (.borrow m ts)) ∧
      LVal.deref source = prependPath suffix (.deref u₀) ∧
      store.loc (.deref u₀) = some L ∧
      LVal.path u₀ = spinePath ∧
      (res = L ∨ RuntimeFrame.LocReads store (.deref source) L) := by
  sorry
theorem EnvMayReadThrough.ownerSpine_of_ownerSpine_same_leaf_whenInitialized
    {store : ProgramStore} {env : Env}
    {written readPrefix target : LVal}
    {writtenRootSlot readRootSlot writtenLeafSlot readLeafSlot : StoreSlot}
    {writtenRootTy readRootTy writtenLeafTy readLeafTy : PartialTy}
    {leaf : Location} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    StoreOwnerSpineWhenInitialized env store
      (VariableProjection (LVal.base written)) writtenRootSlot writtenRootTy
      (LVal.path written) leaf writtenLeafSlot writtenLeafTy →
    StoreOwnerSpineWhenInitialized env store
      (VariableProjection (LVal.base readPrefix)) readRootSlot readRootTy
      (LVal.path readPrefix) leaf readLeafSlot readLeafTy →
    EnvMayReadThrough env readPrefix target →
    EnvMayReadThrough env written target := by
  intro hvalidStore hheap hwrittenSpine hreadSpine hmayRead
  have heq :
      written = readPrefix :=
    StoreOwnerSpineWhenInitialized.lval_eq_of_same_leaf hvalidStore hheap
      hwrittenSpine hreadSpine
  simpa [heq] using hmayRead

theorem EnvMayReadThrough.ownerSpine_of_same_location_whenInitialized
    {store : ProgramStore} {env : Env}
    {lifetime writtenLifetime readPrefixLifetime : Lifetime}
    {written readPrefix target : LVal}
    {writtenTy : Ty} {readPrefixTy : PartialTy}
    {envSlot : EnvSlot} {rootSlot leafSlot : StoreSlot} {leaf : Location} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstractionWhenInitialized store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env written (.ty writtenTy) writtenLifetime →
    env.slotAt (LVal.base written) = some envSlot →
    store.slotAt (VariableProjection (LVal.base written)) = some rootSlot →
    StoreOwnerSpineWhenInitialized env store
      (VariableProjection (LVal.base written)) rootSlot
      envSlot.ty (LVal.path written) leaf leafSlot (.ty writtenTy) →
    LValTyping env readPrefix readPrefixTy readPrefixLifetime →
    store.loc written = some leaf →
    store.loc readPrefix = some leaf →
    EnvMayReadThrough env readPrefix target →
    EnvMayReadThrough env written target := by
  sorry
theorem envWriteEffectiveWrite_mayReadThrough_source_of_ownerSpine_same_location_whenInitialized
    {store : ProgramStore} {env result : Env}
    {lifetime writeLifetime readPrefixLifetime : Lifetime}
    {lv readPrefix dependencyTarget : LVal}
    {lvTy rhsTy : Ty} {readPrefixTy : PartialTy} {rank : Nat}
    {envSlot : EnvSlot} {rootSlot leafSlot : StoreSlot} {leaf : Location} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstractionWhenInitialized store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty lvTy) writeLifetime →
    env.slotAt (LVal.base lv) = some envSlot →
    store.slotAt (VariableProjection (LVal.base lv)) = some rootSlot →
    StoreOwnerSpineWhenInitialized env store
      (VariableProjection (LVal.base lv)) rootSlot
      envSlot.ty (LVal.path lv) leaf leafSlot (.ty lvTy) →
    EnvWrite rank env lv rhsTy result →
    LValTyping env readPrefix readPrefixTy readPrefixLifetime →
    store.loc lv = some leaf →
    store.loc readPrefix = some leaf →
    EnvMayReadThrough env readPrefix dependencyTarget →
    ∃ written,
      EnvWriteEffectiveWrite rank env lv rhsTy result written ∧
        EnvMayReadThrough env written dependencyTarget := by
  intro hwellFormed hsafe hvalidStore hheap hLv henvSlot hrootSlot hspine
    hwrite hreadPrefixTyping hlvLoc hreadPrefixLoc hmayRead
  have hmayReadOwner :
      EnvMayReadThrough env lv dependencyTarget :=
    EnvMayReadThrough.ownerSpine_of_same_location_whenInitialized
      hwellFormed hsafe hvalidStore hheap hLv henvSlot hrootSlot hspine
      hreadPrefixTyping hlvLoc hreadPrefixLoc hmayRead
  have heffective :
      EnvWriteEffectiveWrite rank env lv rhsTy result lv :=
    EnvWrite.effectiveWrite_ownerSpine_whenInitialized_self hLv henvSlot
      hrootSlot hspine hwrite
  exact ⟨lv, heffective, hmayReadOwner⟩

theorem envWriteEffectiveWrite_mayReadThrough_source_of_borrow_deref_same_location_whenInitialized
    {store : ProgramStore} {env result : Env}
    {lifetime borrowLifetime targetLifetime readPrefixLifetime : Lifetime}
    {source readPrefix dependencyTarget : LVal}
    {mutable : Bool} {targets : List LVal}
    {targetTy rhsTy : Ty} {readPrefixTy : PartialTy} {rank : Nat}
    {writtenLocation : Location} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstractionWhenInitialized store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env source (.ty (.borrow mutable targets)) borrowLifetime →
    LValTargetsTyping env targets (.ty targetTy) targetLifetime →
    EnvWrite rank env (.deref source) rhsTy result →
    LValTyping env readPrefix readPrefixTy readPrefixLifetime →
    store.loc (.deref source) = some writtenLocation →
    store.loc readPrefix = some writtenLocation →
    EnvMayReadThrough env readPrefix dependencyTarget →
    ∃ written,
      EnvWriteEffectiveWrite rank env (.deref source) rhsTy result written ∧
        EnvMayReadThrough env written dependencyTarget := by
  sorry
theorem envWriteEffectiveWrite_mayReadThrough_source_of_same_location_whenInitialized
    {store : ProgramStore} {env result : Env}
    {lifetime writeLifetime readPrefixLifetime : Lifetime}
    {lv readPrefix dependencyTarget : LVal}
    {lvTy rhsTy : Ty} {readPrefixTy : PartialTy} {rank : Nat}
    {writtenLocation : Location} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstractionWhenInitialized store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty lvTy) writeLifetime →
    EnvWrite rank env lv rhsTy result →
    LValTyping env readPrefix readPrefixTy readPrefixLifetime →
    store.loc lv = some writtenLocation →
    store.loc readPrefix = some writtenLocation →
    EnvMayReadThrough env readPrefix dependencyTarget →
    ∃ written,
      EnvWriteEffectiveWrite rank env lv rhsTy result written ∧
        EnvMayReadThrough env written dependencyTarget := by
  sorry
theorem envWriteEffectiveWrite_mayReadThrough_source_of_locReads_whenInitialized
    {store : ProgramStore} {env result : Env}
    {lifetime writeLifetime dependencyLifetime : Lifetime}
    {lv dependencyTarget : LVal}
    {lvTy dependencyTy rhsTy : Ty} {rank : Nat}
    {writtenLocation : Location} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstractionWhenInitialized store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty lvTy) writeLifetime →
    EnvWrite rank env lv rhsTy result →
    LValTyping env dependencyTarget (.ty dependencyTy) dependencyLifetime →
    store.loc lv = some writtenLocation →
    RuntimeFrame.LocReads store dependencyTarget writtenLocation →
    ∃ written,
      EnvWriteEffectiveWrite rank env lv rhsTy result written ∧
        EnvMayReadThrough env written dependencyTarget := by
  intro hwellFormed hsafe hvalidStore hheap hLv hwrite hdependencyTarget
    hlvLoc hreads
  rcases RuntimeFrame.LocReads.typed_envMayReadThrough_prefix
      hdependencyTarget hreads with
    ⟨readPrefix, readPrefixTy, readPrefixLifetime, hreadPrefixTyping,
      hreadPrefixLoc, hmayReadTarget⟩
  rcases
      envWriteEffectiveWrite_mayReadThrough_source_of_same_location_whenInitialized
        hwellFormed hsafe hvalidStore hheap hLv hwrite hreadPrefixTyping
        hlvLoc hreadPrefixLoc hmayReadTarget with
    ⟨written, heffective, hmayRead⟩
  exact ⟨written, heffective, hmayRead⟩

theorem lval_loc_var_slot_full_of_lvalTyping_whenInitialized
    {store : ProgramStore} {env : Env}
    {lv : LVal} {ty : Ty} {lifetime : Lifetime}
    {x : Name} {slot : EnvSlot} :
    SafeAbstractionWhenInitialized store env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty ty) lifetime →
    store.loc lv = some (VariableProjection x) →
    env.slotAt x = some slot →
    ∃ slotTy, slot.ty = .ty slotTy := by
  intro hsafe hheap htyping
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
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping ty rfl
  · intro y envSlot henvSlot ty hty hloc hxSlot
    simp [ProgramStore.loc, VariableProjection] at hloc
    cases hloc
    have hslotEq : slot = envSlot :=
      Option.some.inj (hxSlot.symm.trans henvSlot)
    subst hslotEq
    exact ⟨ty, hty⟩
  · intro source inner sourceLifetime hsource _ih ty hty hloc _hxSlot
    cases hty
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source (.box (.ty ty)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
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
  · intro source inner sourceLifetime hsource _ih ty hty hloc _hxSlot
    cases hty
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.box inner)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
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
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets _ihSource ihTargets ty hty hloc hxSlot
    cases hty
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrowLive selectedLocation _mutable _targets selected _hinit hmem
        hselectedLoc =>
        have hderefLoc : store.loc source.deref = some selectedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hselectedLocationEq : selectedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact (Option.some.inj hderefLoc).symm
        have hselectedLocVar :
            store.loc selected = some (VariableProjection x) := by
          simpa [hselectedLocationEq] using hselectedLoc
        exact ihTargets selected hmem hselectedLocVar hxSlot
    | @borrowStale _location _mutable _targets hstale =>
        have hinitialized : BorrowTargetsInitialized env targets := by
          intro target hmem
          rcases lvalTargetsTyping_member_strengthens htargets target hmem with
            ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
          exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
        exact False.elim (hstale hinitialized)
  · intro target targetTy targetLifetime _htarget ihTarget selected hmem hloc
      hxSlot
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
theorem EnvWrite.runtime_selected_lval_map_whenInitialized
    {store : ProgramStore}
    {env result : Env} {lifetime : Lifetime} {lv : LVal}
    {lvTy rhsTy selectedSlotTy : Ty} {selectedName : Name}
    {selectedSlot : EnvSlot} {rank : Nat} {φ : Name → Nat} :
    LinearizedBy φ env →
    SafeAbstractionWhenInitialized store env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty lvTy) lifetime →
    store.loc lv = some (VariableProjection selectedName) →
    env.slotAt selectedName = some selectedSlot →
    selectedSlot.ty = .ty selectedSlotTy →
    EnvWrite rank env lv rhsTy result →
    EnvSameShapeStrengthening
      (env.update selectedName { selectedSlot with ty := .ty rhsTy }) result := by
  intro hφ hsafe hheap htyping hloc hselectedSlot hselectedSlotTy hwrite
  let selectedSource : Env :=
    env.update selectedName { selectedSlot with ty := .ty rhsTy }
  let PathMap : Nat → Prop := fun rootRank =>
    ∀ {target : LVal} {pt : PartialTy} {targetLifetime : Lifetime}
      {path : List Unit} {branchResult : Env} {branchRank : Nat},
      φ (LVal.base target) = rootRank →
      LValTyping env target pt targetLifetime →
      RuntimePathSelected store env pt path selectedName selectedSlot
        selectedSlotTy →
      env.slotAt selectedName = some selectedSlot →
      selectedSlot.ty = .ty selectedSlotTy →
      EnvWrite branchRank env (prependPath path target) rhsTy branchResult →
      EnvSameShapeStrengthening selectedSource branchResult
  let DirectMap : Nat → Prop := fun rootRank =>
    ∀ {target : LVal} {targetTy : Ty} {targetLifetime : Lifetime}
      {branchResult : Env} {branchRank : Nat},
      φ (LVal.base target) = rootRank →
      LValTyping env target (.ty targetTy) targetLifetime →
      store.loc target = some (VariableProjection selectedName) →
      env.slotAt selectedName = some selectedSlot →
      selectedSlot.ty = .ty selectedSlotTy →
      EnvWrite branchRank env target rhsTy branchResult →
      EnvSameShapeStrengthening selectedSource branchResult
  have hall : ∀ rootRank, PathMap rootRank ∧ DirectMap rootRank := by
    intro rootRank
    refine Nat.strong_induction_on rootRank ?_
    intro rootRank ih
    have hpath : PathMap rootRank := by
      intro target pt targetLifetime path branchResult branchRank hrootEq
        htargetTyping hselected hselectedSlotAt hselectedTy hbranchWrite
      cases hbranchWrite with
      | @intro _rank _env₁ writeEnv writeLv writeSlot _ty updatedTy
          hwriteSlot hupdate =>
          have hwriteSlotBase :
              env.slotAt (LVal.base target) = some writeSlot := by
            simpa [LVal.base_prependPath] using hwriteSlot
          have hupdatePath :
              UpdateAtPath branchRank env (LVal.path target ++ path)
                writeSlot.ty rhsTy writeEnv updatedTy := by
            simpa [LVal.path_prependPath] using hupdate
          have hselectedFull :
              RuntimePathSelected store env writeSlot.ty
                (LVal.path target ++ path) selectedName selectedSlot
                selectedSlotTy :=
            RuntimePathSelected.prepend_of_lvalTyping htargetTyping
              hwriteSlotBase path hselected
          have hbelow :
              ∀ v, v ∈ PartialTy.vars writeSlot.ty →
                φ v < φ (LVal.base target) :=
            hφ (LVal.base target) writeSlot hwriteSlotBase
          rcases RuntimePathSelected.updateAtPath_map
              (rootRank := φ (LVal.base target))
              (selectedSource := selectedSource)
              hbelow hselectedFull hupdatePath
                  (fun {branchRank : Nat} {recursiveTarget : LVal}
                    {recursiveTy : Ty} {recursiveLifetime : Lifetime}
                    {recursiveResult : Env}
                    hpositive htargetRank hrecursiveTyping hrecursiveLoc
                    hrecursiveWrite =>
                have hlt : φ (LVal.base recursiveTarget) < rootRank := by
                  simpa [hrootEq] using htargetRank
                (ih (φ (LVal.base recursiveTarget)) hlt).2 rfl
                  hrecursiveTyping hrecursiveLoc hselectedSlotAt
                  hselectedTy hrecursiveWrite)
                  (fun {branchRank : Nat} {recursiveTarget : LVal}
                    {recursivePt : PartialTy} {recursiveLifetime : Lifetime}
                    {recursivePath : List Unit} {recursiveResult : Env}
                    hpositive htargetRank hrecursiveTyping hrecursiveSelected
                    hrecursiveWrite =>
                have hlt : φ (LVal.base recursiveTarget) < rootRank := by
                  simpa [hrootEq] using htargetRank
                (ih (φ (LVal.base recursiveTarget)) hlt).1 rfl
                  hrecursiveTyping hrecursiveSelected hselectedSlotAt
                  hselectedTy hrecursiveWrite) with
            ⟨hinnerMap, hstrength, hshape⟩
          have hselectedLtBase :
              φ selectedName < φ (LVal.base target) :=
            RuntimePathSelected.rank_lt_of_lvalTyping_whenInitialized
              hφ hsafe hheap hselected htargetTyping
          have hbaseNe : LVal.base target ≠ selectedName := by
            intro hbaseEq
            have hbad : φ selectedName < φ selectedName := by
              simpa [hbaseEq] using hselectedLtBase
            exact Nat.lt_irrefl _ hbad
          have hselectedSourceBase :
              selectedSource.slotAt (LVal.base target) = some writeSlot := by
            dsimp [selectedSource]
            rw [Env.update_slotAt_ne]
            · exact hwriteSlotBase
            · exact hbaseNe
          have hfinal :
              EnvSameShapeStrengthening selectedSource
                (writeEnv.update (LVal.base target)
                  { writeSlot with ty := updatedTy }) :=
            EnvSameShapeStrengthening.update_result_strengthening
              hinnerMap hselectedSourceBase rfl hstrength hshape
          simpa [LVal.base_prependPath] using hfinal
    have hdirect : DirectMap rootRank := by
      intro target targetTy targetLifetime branchResult branchRank hrootEq
        htargetTyping htargetLoc hselectedSlotAt hselectedTy hbranchWrite
      cases target with
      | var x =>
          rcases LValTyping.var_inv htargetTyping with
            ⟨targetSlot, htargetSlot, _htargetSlotTy, _htargetLifetime⟩
          simp [ProgramStore.loc, VariableProjection] at htargetLoc
          cases htargetLoc
          have hslotEq : selectedSlot = targetSlot :=
            Option.some.inj (hselectedSlotAt.symm.trans htargetSlot)
          subst hslotEq
          exact EnvWrite.var_rhs_to_result_map htargetSlot hselectedTy
            hbranchWrite
      | deref source =>
          cases htargetTyping with
          | box hsource =>
              have hsourceAbs :
                  LValLocationAbstractionWhenInitialized env store source
                    (.box (.ty targetTy)) :=
                lvalTyping_defined_location_whenInitialized hsafe hsource
              rcases hsourceAbs with
                ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
                  hsourceValid⟩
              rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
              cases hsourceValid with
              | @box ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
                  have hderefLoc :
                      store.loc source.deref = some ownerLocation := by
                    simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                  have hownerEq :
                      ownerLocation = VariableProjection selectedName := by
                    rw [htargetLoc] at hderefLoc
                    exact (Option.some.inj hderefLoc).symm
                  subst hownerEq
                  have howns : ProgramStore.Owns store
                      (VariableProjection selectedName) :=
                    ⟨sourceLocation, sourceSlotLifetime, by
                      simpa [owningRef] using hsourceSlot⟩
                  exact False.elim
                    ((not_owns_var_of_storeOwnerTargetsHeap hheap) howns)
          | boxFull hsource =>
              have hsourceAbs :
                  LValLocationAbstractionWhenInitialized env store source
                    (.ty (.box targetTy)) :=
                lvalTyping_defined_location_whenInitialized hsafe hsource
              rcases hsourceAbs with
                ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
                  hsourceValid⟩
              rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
              cases hsourceValid with
              | @boxFull ownerLocation ownerSlot _ hownerSlot _hinnerValid =>
                  have hderefLoc :
                      store.loc source.deref = some ownerLocation := by
                    simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                  have hownerEq :
                      ownerLocation = VariableProjection selectedName := by
                    rw [htargetLoc] at hderefLoc
                    exact (Option.some.inj hderefLoc).symm
                  subst hownerEq
                  have howns : ProgramStore.Owns store
                      (VariableProjection selectedName) :=
                    ⟨sourceLocation, sourceSlotLifetime, by
                      simpa [owningRef] using hsourceSlot⟩
                  exact False.elim
                    ((not_owns_var_of_storeOwnerTargetsHeap hheap) howns)
          | borrow hsource htargets =>
              rename_i mutable targets borrowLifetime
              have hsourceAbs :
                  LValLocationAbstractionWhenInitialized env store source
                    (.ty (.borrow mutable targets)) :=
                lvalTyping_defined_location_whenInitialized hsafe hsource
              rcases hsourceAbs with
                ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
                  hsourceValid⟩
              rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
              cases hsourceValid with
              | @borrowLive selectedLocation _mutable _targets selected
                  _hinit hmem hselectedLoc =>
                  have hderefLoc :
                      store.loc source.deref = some selectedLocation := by
                    simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                  have hselectedLocationEq :
                      selectedLocation = VariableProjection selectedName := by
                    rw [htargetLoc] at hderefLoc
                    exact (Option.some.inj hderefLoc).symm
                  have hselectedLocVar :
                      store.loc selected =
                        some (VariableProjection selectedName) := by
                    simpa [hselectedLocationEq] using hselectedLoc
                  rcases lvalTargetsTyping_member_strengthens htargets
                      selected hmem with
                    ⟨selectedTy, selectedLifetime, hselectedTyping,
                      _hselectedStrengthens⟩
                  have hselectedHead :
                      RuntimePathSelected store env
                        (.ty (.borrow mutable targets)) [()] selectedName
                        selectedSlot selectedSlotTy :=
                    RuntimePathSelected.borrowHere hmem hselectedTyping
                      hselectedLocVar hselectedSlotAt hselectedTy
                  have hsourceRoot :
                      φ (LVal.base source) = rootRank := by
                    simpa [LVal.base] using hrootEq
                  have hwritePath :
                      EnvWrite branchRank env (prependPath [()] source)
                        rhsTy branchResult := by
                    simpa [prependPath] using hbranchWrite
                  exact hpath hsourceRoot hsource hselectedHead
                    hselectedSlotAt hselectedTy hwritePath
              | @borrowStale _location _mutable _targets hstale =>
                  have hinitialized :
                      BorrowTargetsInitialized env targets := by
                    intro target hmem
                    rcases lvalTargetsTyping_member_strengthens htargets
                        target hmem with
                      ⟨selectedTy, selectedLifetime, hselectedTyping,
                        _hstrength⟩
                    exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
                  exact False.elim (hstale hinitialized)
    exact ⟨hpath, hdirect⟩
  exact (hall (φ (LVal.base lv))).2 rfl htyping hloc hselectedSlot
    hselectedSlotTy hwrite
theorem EnvWrite.runtime_selected_spine_map_whenInitialized
    {store : ProgramStore}
    {env result : Env} {current lifetime : Lifetime} {lv : LVal}
    {lvTy rhsTy : Ty} {address : Nat} {xRoot : Name} {envSlot : EnvSlot}
    {rootSlot leafSlot : StoreSlot} {spinePath : List Unit} {leafTy : Ty}
    {rank : Nat} {φ : Name → Nat} :
    LinearizedBy φ env →
    WellFormedEnvWhenInitialized env current →
    SafeAbstractionWhenInitialized store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env.slotAt xRoot = some envSlot →
    StoreOwnerSpineWhenInitialized env store (VariableProjection xRoot)
      rootSlot envSlot.ty spinePath (.heap address) leafSlot (.ty leafTy) →
    spinePath ≠ [] →
    LValTyping env lv (.ty lvTy) lifetime →
    store.loc lv = some (.heap address) →
    EnvWrite rank env lv rhsTy result →
    EnvSameShapeStrengthening
      (env.update xRoot
        { envSlot with
            ty := PartialTy.strongLeafUpdate envSlot.ty spinePath rhsTy })
      result := by
  intro hφ hwellFormed hsafe hvalidStore hheap hrootSlot hspine hspineNonempty
    htyping hloc hwrite
  exact goLVal hφ hwellFormed hsafe hvalidStore hheap hrootSlot hspine
    hspineNonempty htyping hloc hwrite
where
  goLVal {store : ProgramStore} {env result : Env}
      {current lifetime : Lifetime} {lv : LVal} {lvTy rhsTy : Ty}
      {address : Nat} {xRoot : Name} {envSlot : EnvSlot}
      {rootSlot leafSlot : StoreSlot} {spinePath : List Unit} {leafTy : Ty}
      {rank : Nat} {φ : Name → Nat}
      (hφ : LinearizedBy φ env)
      (hwellFormed : WellFormedEnvWhenInitialized env current)
      (hsafe : SafeAbstractionWhenInitialized store env)
      (hvalidStore : ValidStore store) (hheap : StoreOwnerTargetsHeap store)
      (hrootSlot : env.slotAt xRoot = some envSlot)
      (hspine : StoreOwnerSpineWhenInitialized env store
        (VariableProjection xRoot) rootSlot envSlot.ty spinePath
        (.heap address) leafSlot (.ty leafTy))
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
        rcases StoreOwnerSpineWhenInitialized.of_lvalTyping_box
            hwellFormed hsafe hsource with
          ⟨envSlot', rootSlot', sourceLocation, sourceSlot, henvBase,
            hrootSlot', hrootLifetime', hsourceLoc, hsourceSlot,
            hsourceSpine⟩
        have hsourceValid :=
          StoreOwnerSpineWhenInitialized.leaf_valid hsourceSpine
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
              StoreOwnerSpineWhenInitialized.snoc_box hsourceSpine rfl rfl
                hownedSlot hinnerValid
            rw [← hlocEq] at hsnoc
            have hlocalProt :
                ProtectedByBase store (LVal.base source) (.heap address) :=
              Or.inr
                (StoreOwnerSpineWhenInitialized.ownsTransitively_of_nonempty
                  hsnoc (by simp))
            have hrootProt :
                ProtectedByBase store xRoot (.heap address) :=
              Or.inr
                (StoreOwnerSpineWhenInitialized.ownsTransitively_of_nonempty
                  hspine hspineNonempty)
            have hbaseEq : LVal.base source = xRoot :=
              ProtectedByBase.root_unique hvalidStore hheap hlocalProt
                hrootProt
            have henvSlotEq : envSlot' = envSlot := by
              rw [hbaseEq] at henvBase
              exact Option.some.inj (henvBase.symm.trans hrootSlot)
            rw [henvSlotEq, hbaseEq] at hsnoc
            have hpathEq : spinePath = () :: LVal.path source :=
              StoreOwnerSpineWhenInitialized.path_unique hspine hsnoc
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
                  StoreOwnerSpineWhenInitialized.updateAtPath_env_eq hsnoc
                    hupdatePath
                rcases
                    StoreOwnerSpineWhenInitialized.strongLeafUpdate_strengthens_updateAtPath
                      hsnoc rfl hupdatePath with
                  ⟨hstrength, hshape⟩
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
      | @boxFull _ inner sourceLifetime hsource =>
        sorry
      | @borrow _ mutable targets borrowLifetime targetLifetime targetTy
          hsource htargets =>
        have hsourceAbs :
            LValLocationAbstractionWhenInitialized env store source
              (.ty (.borrow mutable targets)) :=
          lvalTyping_defined_location_whenInitialized hsafe hsource
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime'⟩
        cases hsourceValid with
        | @borrowLive selectedLocation _mutable _targets selectedTarget
            _hinit hselectedMem htargetLocFromBorrow =>
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
                  (.ty (.borrow mutable targets)) [()] address :=
              RuntimeSpinePathSelected.borrowHere hselectedMem
                hselectedTyping hselectedLocHeap
            exact goPath hφ hwellFormed hsafe hvalidStore hheap hrootSlot
              hspine hspineNonempty hsource hpathSelected
              (by simpa [prependPath] using hwrite)
        | @borrowStale _location _mutable _targets hstale =>
            have hinitialized : BorrowTargetsInitialized env targets := by
              intro target hmem
              rcases lvalTargetsTyping_member_strengthens htargets target hmem with
                ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
              exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
            exact False.elim (hstale hinitialized)
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
      {current lifetime : Lifetime} {lv : LVal} {pt : PartialTy}
      {path : List Unit} {rhsTy : Ty} {address : Nat} {xRoot : Name}
      {envSlot : EnvSlot} {rootSlot leafSlot : StoreSlot}
      {spinePath : List Unit} {leafTy : Ty} {rank : Nat} {φ : Name → Nat}
      (hφ : LinearizedBy φ env)
      (hwellFormed : WellFormedEnvWhenInitialized env current)
      (hsafe : SafeAbstractionWhenInitialized store env)
      (hvalidStore : ValidStore store) (hheap : StoreOwnerTargetsHeap store)
      (hrootSlot : env.slotAt xRoot = some envSlot)
      (hspine : StoreOwnerSpineWhenInitialized env store
        (VariableProjection xRoot) rootSlot envSlot.ty spinePath
        (.heap address) leafSlot (.ty leafTy))
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
          Or.inr
            (StoreOwnerSpineWhenInitialized.ownsTransitively_of_nonempty
              hspine hspineNonempty)
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
                _hbranchRank _htargetRank htargetTyping htargetLoc
                hbranchWrite =>
              goLVal hφ hwellFormed hsafe hvalidStore hheap hrootSlot hspine
                hspineNonempty htargetTyping htargetLoc hbranchWrite)
            (fun {branchRank target branchPt branchLifetime branchPath
                branchResult}
                _hbranchRank _htargetRank htargetTyping htargetSelected
                hbranchWrite =>
              goPath hφ hwellFormed hsafe hvalidStore hheap hrootSlot hspine
                hspineNonempty htargetTyping htargetSelected hbranchWrite)
          with ⟨hmap, hstrength, hshape⟩
        have hselectedRankLt :
            φ xRoot < φ (LVal.base lv) :=
          RuntimeSpinePathSelected.rank_lt_of_lvalTyping_whenInitialized
            hφ hwellFormed hsafe hvalidStore hheap hselected hrootProt htyping
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
theorem preservation_assign_deref_box_step_runtime_whenInitialized_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {source : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstractionWhenInitialized store env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env source (.box oldTy) targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTyWhenInitialized env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    WellFormedEnvWhenInitialized env' lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign (.deref source) (.val value)) store'
      (.val finalValue) →
    TerminalStateSafeWhenInitialized store' finalValue env' .unit := by
  intro hwellFormed hsafe hvalidRuntime hsourceBox _hshape hwellTy hwrite
    _hranked hnotWrite hwellOut hvalidValue hstep
  rcases assign_step_components hstep with
    ⟨writtenStore, oldSlot, lhsLocation, hread, hwriteStore, hdrops,
      hlhsLoc, hlhsSlot, _hwriteStoreEq, hresult⟩
  cases hresult
  have hwriteEq :
      writtenStore =
        store.update lhsLocation { oldSlot with value := .value value } := by
    unfold ProgramStore.write at hwriteStore
    simp [hlhsLoc, hlhsSlot] at hwriteStore
    exact hwriteStore.symm
  rcases StoreOwnerSpineWhenInitialized.of_lvalTyping_box hwellFormed hsafe
      hsourceBox with
    ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase, hrootSlot,
      hrootLifetime, hsourceLoc, hsourceSlot, hsourceSpine⟩
  have hsourceValid :
      ValidPartialValueWhenInitialized env store sourceSlot.value (.box oldTy) :=
    StoreOwnerSpineWhenInitialized.leaf_valid hsourceSpine
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
          StoreOwnerSpineWhenInitialized env store
            (VariableProjection (LVal.base (.deref source))) rootSlot
            envSlot.ty (LVal.path (.deref source)) lhsLocation oldSlot
            oldTy := by
        have hsnoc :
            StoreOwnerSpineWhenInitialized env store
              (VariableProjection (LVal.base source)) rootSlot envSlot.ty
              (() :: LVal.path source) lhsLocation oldSlot oldTy :=
          StoreOwnerSpineWhenInitialized.snoc_box hsourceSpine rfl rfl
            hownedSlot hinnerValid
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
            StoreOwnerSpineWhenInitialized.updateAtPath_rank_zero_env_eq
              hspine hupdatePath
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
                (env.update (LVal.base source) { envSlot with ty := updatedTy })
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
            StoreOwnerSpineWhenInitialized.updateAtPath_rank_zero_rhs_vars_subset_updated
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
                RuntimeFrame.ReachesWhenInitialized env store
                  (.value value) (.ty rhsTy) location →
                location ≠ lhsLocation :=
            term_value_reachesWhenInitialized_ne_owner_spine_leaf_of_noWrite
              hwellFormed hsafe hvalidRuntimeValue hwellTy hvalidValue hspine
              hvarsObserver hnotWriteSource hnotWriteObserver
          have hnewValid :
              ValidPartialValueWhenInitialized env writtenStore (.value value)
                (.ty rhsTy) := by
            rw [hwriteEq]
            exact RuntimeFrame.validPartialValueWhenInitialized_update_of_not_reachesWhenInitialized
              hvalidValue hvalueNoReachLeaf
          have hotherNoReachLeaf :
              ∀ y otherEnvSlot oldValue,
                y ≠ LVal.base source →
                env.slotAt y = some otherEnvSlot →
                store.slotAt (VariableProjection y) =
                  some (StoreSlot.mk oldValue otherEnvSlot.lifetime) →
                ∀ location,
                  RuntimeFrame.ReachesWhenInitialized env store oldValue
                    otherEnvSlot.ty location →
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
              stored_var_reachesWhenInitialized_ne_owner_spine_leaf_of_noWrite
                hwellFormed hsafe
                (ValidRuntimeState.validStore hvalidRuntime)
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hspine hyx henvY hslotY hvalidOld hvarsOther
                hnotWriteSource hnotWriteObserver
          have hsafeWrite :
              SafeAbstractionWhenInitialized writtenStore
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy }) := by
            rw [hwriteEq]
            simpa [LVal.base] using
                safeAbstractionWhenInitialized_update_owner_spine_of_frames
                  hwellFormed hsafe
                  (ValidRuntimeState.validStore hvalidRuntime)
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                  henvBase hrootSlot hrootLifetime hspine hpathNonempty
                  hupdatePath hnotWriteSource hnotWriteObserver rfl
                  (by simpa [hwriteEq] using hnewValid) hotherNoReachLeaf
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
              simpa [termOwningLocations, termValues,
                partialValueOwningLocations] using hmem)
          have hwrittenValidStore : ValidStore writtenStore :=
            validStore_write_disjoint
              (ValidRuntimeState.validStore hvalidRuntime)
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
                ¬ ProgramStore.Owns writtenStore owned := by
            intro owned howned hownsWritten
            have hownedOld :
                owned ∈ partialValueOwningLocations oldSlot.value := by
              simpa [partialValuesOwningLocations] using howned
            have hstoreOwnsOld : ProgramStore.OwnsAt store owned lhsLocation := by
              have holdValue :
                  oldSlot.value = .value (owningRef owned) :=
                eq_owningRef_of_mem_partialValueOwningLocations hownedOld
              exact ⟨oldSlot.lifetime, by
                cases oldSlot with
                | mk oldValue oldLifetime =>
                    cases holdValue
                    simpa [owningRef] using hlhsSlot⟩
            rcases hownsWritten with ⟨storage, ownerLifetime, hownerSlotWritten⟩
            by_cases hstorage : storage = lhsLocation
            · subst storage
              rw [hwriteEq] at hownerSlotWritten
              have hnewOwnsOld :
                  owned ∈ partialValueOwningLocations (.value value) := by
                have hnewValueEq :
                    PartialValue.value value = .value (owningRef owned) := by
                  have hslotEq :
                      { oldSlot with value := PartialValue.value value } =
                        StoreSlot.mk (PartialValue.value (owningRef owned))
                          ownerLifetime := by
                    simpa [ProgramStore.update] using hownerSlotWritten
                  exact congrArg StoreSlot.value hslotEq
                exact mem_partialValueOwningLocations_of_eq_owningRef
                  hnewValueEq
              exact
                (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
                  (by
                    simpa [termOwningLocations, termValues,
                      partialValueOwningLocations] using hnewOwnsOld))
                ⟨lhsLocation, hstoreOwnsOld⟩
            · have hownerSlotStore :
                  store.slotAt storage =
                    some (StoreSlot.mk (.value (owningRef owned))
                      ownerLifetime) := by
                rw [hwriteEq] at hownerSlotWritten
                simpa [ProgramStore.update, hstorage] using hownerSlotWritten
              have hstorageEq :
                  storage = lhsLocation :=
                (ValidRuntimeState.validStore hvalidRuntime)
                  owned storage lhsLocation
                  ⟨ownerLifetime, hownerSlotStore⟩ hstoreOwnsOld
              exact hstorage hstorageEq
          have hallocatedWrite : StoreOwnersAllocated writtenStore :=
            storeOwnersAllocated_write_value_of_validValueWhenInitialized
              (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
              hwriteStore
          have hrootWrite : HeapSlotsRootLifetime writtenStore :=
            heapSlotsRootLifetime_write
              (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
          have hallocatedFinal : StoreOwnersAllocated store' :=
            drops_storeOwnersAllocated_of_disjoint hdrops hwrittenValidStore
              hallocatedWrite hdropOwnersOrphaned
          have hheapFinal : StoreOwnerTargetsHeap store' :=
            drops_storeOwnerTargetsHeap hdrops hwrittenHeap
          have hrootFinal : HeapSlotsRootLifetime store' :=
            drops_heapSlotsRootLifetime hdrops hrootWrite
          have hsafeFinal :
              SafeAbstractionWhenInitialized store'
                (env.update (LVal.base source)
                  { envSlot with ty := updatedTy }) := by
              exact safeAbstractionWhenInitialized_drops_of_orphaned_values_early
                hwellOut hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap
                hdropOwnersOrphaned hdrops
          exact ⟨validRuntimeState_assign_step_of_postWriteDrop_invariants
              (lifetime := lifetime)
              hvalidRuntime hallocatedFinal hheapFinal hrootFinal hread
              hwriteStore hdrops,
            hsafeFinal, ValidPartialValueWhenInitialized.unit⟩

/-- Stale-aware assignment through a mutable borrow target. -/
theorem preservation_assign_deref_borrow_step_runtime_whenInitialized_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime borrowLifetime targetLifetime rhsWellLifetime : Lifetime}
    {source : LVal} {mutable : Bool} {targets : List LVal}
    {targetTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstractionWhenInitialized store env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    LValTyping env source (.ty (.borrow mutable targets)) borrowLifetime →
    LValTargetsTyping env targets targetTy targetLifetime →
    ShapeCompatible env targetTy (.ty rhsTy) →
    WellFormedTyWhenInitialized env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.deref source) rhsTy env' →
    EnvWriteNoStaleBorrowTargets 0 env (.deref source) rhsTy env' →
    (∃ φ, LinearizedBy φ env ∧ EnvWriteRhsBorrowTargetsBelow φ env' rhsTy) →
    ¬ WriteProhibited env' (.deref source) →
    WellFormedEnvWhenInitialized env' lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign (.deref source) (.val value)) store'
      (.val finalValue) →
    TerminalStateSafeWhenInitialized store' finalValue env' .unit := by
  intro hwellFormed hsafe hvalidRuntime hsourceBorrow htargets
    _hshape hwellTy hwrite hnoStale hranked hnotWrite hwellOut hvalidValue hstep
  rcases assign_step_components hstep with
    ⟨writtenStore, oldSlot, lhsLocation, hread, hwriteStore, hdrops,
      hlhsLoc, hlhsSlot, hwriteStoreEq, hresult⟩
  cases hresult
  have hwriteEq :
      writtenStore =
        store.update lhsLocation { oldSlot with value := .value value } := by
    unfold ProgramStore.write at hwriteStore
    simp [hlhsLoc, hlhsSlot] at hwriteStore
    exact hwriteStore.symm
  have hsourceAbs :
      LValLocationAbstractionWhenInitialized env store source
        (.ty (.borrow mutable targets)) :=
    lvalTyping_defined_location_whenInitialized hsafe hsourceBorrow
  have htargetsAbs :
      ∀ target ty lifetime,
        LValTyping env target (.ty ty) lifetime →
        LValLocationAbstractionWhenInitialized env store target (.ty ty) := by
    intro target ty lifetime htarget
    exact lvalTyping_defined_location_whenInitialized hsafe htarget
  rcases location_borrow_selected_target_whenInitialized hsourceAbs htargets
      htargetsAbs with
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
      ValidPartialValueWhenInitialized env store oldSlot.value (.ty selectedTy) := by
    simpa [hselectedSlotEq] using hselectedValid
  have hsafeWrite : SafeAbstractionWhenInitialized writtenStore env' := by
    rw [hwriteEq]
    refine safeAbstractionWhenInitialized_of_domain_and_slots ?domain ?slots
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
                LValTyping.pathThroughBorrow_append hsourceBorrow
                  hwriteSlotBase [()] PathThroughBorrow.borrowHere
            rcases UpdateAtPath.sameShapeStrengthening_of_throughBorrow
                hthrough hupdate with
              ⟨hmap, hstrength, hshape⟩
            have hfinal :=
              EnvSameShapeStrengthening.update_result_strengthening
                (resultSlot := { writeSlot with ty := updatedTy })
                hmap hwriteSlotBase rfl hstrength hshape
            simpa [LVal.base] using hfinal
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
              { oldSlot with value := PartialValue.value value }).slotAt
                (VariableProjection x) =
              some (StoreSlot.mk (PartialValue.value value)
                resultSlot.lifetime) := by
          have hlifetime' : resultSlot.lifetime = oldSlot.lifetime := by
            rw [← hlifetime, hsourceSlotLifetime]
          cases oldSlot
          simp [ProgramStore.update, hxUpdated, hlifetime']
        refine ⟨PartialValue.value value, hslotFinal, ?_⟩
        have hselectedMap :
            EnvSameShapeStrengthening
              (env.update x { sourceSlot with ty := .ty rhsTy }) env' := by
          rcases hwellFormed.2.2.2 with ⟨φ, hφ⟩
          have hlhsLocVar :
              store.loc source.deref = some (VariableProjection x) := by
            simpa [hxUpdated] using hlhsLoc
          rcases LValTargetsTyping.output_full htargets with
            ⟨lhsTy, hOldTyFull⟩
          subst hOldTyFull
          have hLhsBorrow :
              LValTyping env source.deref (.ty lhsTy) targetLifetime :=
            LValTyping.borrow hsourceBorrow htargets
          rcases lval_loc_var_slot_full_of_lvalTyping_whenInitialized hsafe
              (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
              hLhsBorrow hlhsLocVar hsourceSlot with
            ⟨sourceSlotTy, hsourceSlotTy⟩
          exact EnvWrite.runtime_selected_lval_map_whenInitialized hφ hsafe
            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
            hLhsBorrow hlhsLocVar hsourceSlot hsourceSlotTy hwrite
        have hnewValid :
            ValidPartialValueWhenInitialized env
              (store.update lhsLocation
                { oldSlot with value := PartialValue.value value })
              (.value value) (.ty rhsTy) := by
          rcases hranked with ⟨φ, hφ, hbelowRhs⟩
          have hφOut : LinearizedBy φ env' :=
            EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
              hwrite hφ hbelowRhs
          rcases hselectedMap.1 x resultSlot hresultSlot with
            ⟨newSourceSlot, hnewSourceSlot, _hnewLifetime, hnewStrength,
              hnewShape⟩
          have hnewSourceSlotEq :
              newSourceSlot = { sourceSlot with ty := .ty rhsTy } := by
            simpa [Env.update] using hnewSourceSlot.symm
          subst hnewSourceSlotEq
          have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
            ValueOwnerTargetsHeap.partial
              (TermOwnerTargetsHeap.value
                (termOwnerTargetsHeap_assign_inner
                  (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
          refine
            RuntimeFrame.validPartialValueWhenInitialized_update_of_owner_and_borrow_dependency_frame
              hvalidValue ?owners ?dependencies
          · intro location howner hlocationEq
            have hne : location ≠ VariableProjection x :=
              RuntimeFrame.ownerReaches_ne_var_of_heap
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hvalueHeap howner
            exact hne (by simpa [hxUpdated] using hlocationEq)
          · intro dependency hdependency hdependencyEq
            have hdependencyVar :
                dependency = VariableProjection x := by
              simpa [hxUpdated] using hdependencyEq
            have hborrows :
                PartialTyBorrowsWellFormedInSlotWhenInitialized env
                  rhsWellLifetime (.ty rhsTy) :=
              PartialTyBorrowsWellFormedInSlotWhenInitialized.of_wellFormedTy
                hwellTy
            rcases RuntimeFrame.borrowDependencyWhenInitialized_var_rank_le_var
                hφ hwellFormed hsafe
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hborrows hdependency hdependencyVar with
              ⟨v, hvRhs, hxLeV⟩
            have hvResult : v ∈ PartialTy.vars resultSlot.ty := by
              exact partialTy_vars_mono hnewStrength hnewShape v
                (by simpa using hvRhs)
            have hvLtX : φ v < φ x :=
              hφOut x resultSlot hresultSlot v hvResult
            exact (Nat.not_lt_of_ge hxLeV) hvLtX
        rcases hselectedMap.1 x resultSlot hresultSlot with
          ⟨updatedSourceSlot, hupdatedSourceSlot, _hlifeMap, hstrength,
            _hsameShape⟩
        have hupdatedSourceSlotEq :
            updatedSourceSlot = { sourceSlot with ty := .ty rhsTy } := by
          simpa [Env.update] using hupdatedSourceSlot.symm
        subst hupdatedSourceSlotEq
        have hnewValidResultEnv :
            ValidPartialValueWhenInitialized env'
              (store.update lhsLocation
                { oldSlot with value := PartialValue.value value })
              (.value value) (.ty rhsTy) :=
          validPartialValueWhenInitialized_transport_env
            (fun {targets} hinit =>
              borrowTargetsInitialized_back_of_envStrengthens
                (EnvSameShapeStrengthening.envStrengthens hglobalMap)
                hwellFormed.2.2.1 hwellFormed.2.2.2 hinit)
            hnewValid
        exact validPartialValueWhenInitialized_strengthen hnewValidResultEnv
          hstrength
      · have hslotFinal :
            (store.update lhsLocation
              { oldSlot with value := PartialValue.value value }).slotAt
                (VariableProjection x) =
            some { value := oldValue, lifetime := resultSlot.lifetime } := by
          have hlifetime' : resultSlot.lifetime = sourceSlot.lifetime := by
            rw [← hlifetime]
          simpa [ProgramStore.update, hxUpdated, hlifetime'] using hstoreSlot
        refine ⟨oldValue, hslotFinal, ?_⟩
        rcases hglobalMap.1 x resultSlot hresultSlot with
          ⟨mappedSourceSlot, hmappedSourceSlot, _hlifeMap, hstrength,
            hsameShape⟩
        have hmappedSourceSlotEq : sourceSlot = mappedSourceSlot :=
          Option.some.inj (hsourceSlot.symm.trans hmappedSourceSlot)
        subst hmappedSourceSlotEq
        have hvalidStore := ValidRuntimeState.validStore hvalidRuntime
        have hheap := ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
        rcases hranked with ⟨φ, hφ, hbelowRhs⟩
        by_cases howner :
            RuntimeFrame.OwnerReaches store oldValue sourceSlot.ty lhsLocation
        · have hownsTrans :
              ProgramStore.OwnsTransitively store (VariableProjection x)
                lhsLocation :=
            RuntimeFrame.ownsTransitively_of_ownerReaches_stored
              hstoreSlot howner
          have hprotX : ProtectedByBase store x lhsLocation :=
            Or.inr hownsTrans
          rcases hheap lhsLocation
              (ProgramStore.OwnsTransitively.to_owns hownsTrans) with
            ⟨address, haddrEq⟩
          rcases LValTargetsTyping.output_full htargets with
            ⟨lhsTy, hOldTyFull⟩
          subst hOldTyFull
          have hLhsTyping :
              LValTyping env (.deref source) (.ty lhsTy) targetLifetime :=
            LValTyping.borrow hsourceBorrow htargets
          have hlocHeap :
              store.loc (.deref source) = some (.heap address) := by
            rw [← haddrEq]
            exact hlhsLoc
          rcases heapLeaf_spine_of_loc_whenInitialized hφ hwellFormed hsafe
              hheap hLhsTyping hlocHeap with
            ⟨xRoot, envSlotXr, rootSlotXr, spinePath, leafSlotXr, leafTyXr,
              henvXr, hrootSlotXr, _hrootLtXr, hspine, hspineNonempty⟩
          have hprotXr : ProtectedByBase store xRoot lhsLocation := by
            rw [haddrEq]
            exact Or.inr
              (StoreOwnerSpineWhenInitialized.ownsTransitively_of_nonempty
                hspine hspineNonempty)
          have hxEq : xRoot = x :=
            (ProtectedByBase.root_unique hvalidStore hheap hprotX hprotXr).symm
          subst hxEq
          have henvSlotEq : sourceSlot = envSlotXr :=
            Option.some.inj (hsourceSlot.symm.trans henvXr)
          subst henvSlotEq
          have hrootSlotEq :
              rootSlotXr = StoreSlot.mk oldValue sourceSlot.lifetime :=
            Option.some.inj (hrootSlotXr.symm.trans hstoreSlot)
          subst hrootSlotEq
          have hmapSpine :=
            EnvWrite.runtime_selected_spine_map_whenInitialized hφ hwellFormed
              hsafe hvalidStore hheap hsourceSlot hspine hspineNonempty
              hLhsTyping hlocHeap hwrite
          have hvalidRuntimeValue :
              ValidRuntimeState store (.val value) :=
            validRuntimeState_assign_inner hvalidRuntime
          have hvalueHeapRhs : PartialValueOwnerTargetsHeap (.value value) :=
            ValueOwnerTargetsHeap.partial
              (TermOwnerTargetsHeap.value
                (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntimeValue))
          have hrootNoOwnerReach :
              ∀ reached,
                RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy)
                  reached →
                reached ≠ VariableProjection xRoot := by
            intro reached hownerReach
            exact RuntimeFrame.ownerReaches_ne_var_of_heap hheap hvalueHeapRhs
              hownerReach
          have hvalueOwnerFrame :
              ∀ reached,
                RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy)
                  reached →
                reached ≠ lhsLocation := by
            rw [haddrEq]
            exact StoreOwnerSpineWhenInitialized.not_reaches_leaf_of_not_reaches_root
              hvalidRuntimeValue hvalidValue hspine hrootNoOwnerReach
          have hvalueDepFrame :
              ∀ location,
                RuntimeFrame.BorrowDependencyWhenInitialized env store
                  (.value value) (.ty rhsTy) location →
                location ≠ lhsLocation := by
            intro location hdep heq
            subst heq
            rcases RuntimeFrame.borrowDependencyWhenInitialized_witness hdep with
              ⟨m, ts, t, hinitialized, hcontains, hmem, hreads⟩
            have hborrowsRhs :
                PartialTyBorrowsWellFormedInSlotWhenInitialized env
                  rhsWellLifetime (.ty rhsTy) :=
              PartialTyBorrowsWellFormedInSlotWhenInitialized.of_wellFormedTy
                hwellTy
            rcases hborrowsRhs hcontains t hmem with
              ⟨_hbaseTarget, hwhenInitialized⟩
            rcases hinitialized t hmem with
              ⟨tTy₀, tLt₀, htTyping₀⟩
            rcases hwhenInitialized ⟨tTy₀, tLt₀, htTyping₀⟩ with
              ⟨tTy, tLt, htTyping, _houtlives, _hbase⟩
            rcases RuntimeFrame.locReads_resolved_prefix htTyping hreads with
              ⟨w, ptW, ltW, hwTyping, hbaseW, hwLoc⟩
            rcases RuntimeFrame.loc_intrinsicRootView_whenInitialized hφ
                hwellFormed hsafe hwTyping hwLoc with
              ⟨rootW, _, _, _, hprotW, hrankW, _, _, _, _, _, _⟩
            have hrootWEq : rootW = xRoot :=
              ProtectedByBase.root_unique hvalidStore hheap hprotW hprotX
            rw [hrootWEq, hbaseW] at hrankW
            rcases hmapSpine.2 xRoot
                { sourceSlot with
                    ty := PartialTy.strongLeafUpdate sourceSlot.ty spinePath
                      rhsTy }
                (by simp [Env.update]) with
              ⟨resultSlotXr, hresultXr, _hlifeXr⟩
            rcases hmapSpine.1 xRoot resultSlotXr hresultXr with
              ⟨strongSlot', hstrongSlot', _hlifeStrong', hstrengthensXr,
                hshapeXr⟩
            have hstrongEq :
                strongSlot' =
                  { sourceSlot with
                    ty := PartialTy.strongLeafUpdate sourceSlot.ty spinePath
                      rhsTy } := by
              simpa [Env.update] using hstrongSlot'.symm
            subst hstrongEq
            have hcontainsStrong :
                PartialTyContains
                  (PartialTy.strongLeafUpdate sourceSlot.ty spinePath rhsTy)
                  (.borrow m ts) :=
              StoreOwnerSpineWhenInitialized.strongLeafUpdate_contains hspine
                hcontains
            rcases PartialTyContains.mono_strengthens_sameShape hcontainsStrong
                hstrengthensXr hshapeXr with
              ⟨ts', hcontains', hsubset⟩
            have hstrict : φ (LVal.base t) < φ xRoot :=
              hbelowRhs xRoot resultSlotXr m ts' t hresultXr hcontains'
                (hsubset hmem) ⟨m, ts, hcontains, hmem⟩
            exact Nat.lt_irrefl _ (lt_of_le_of_lt hrankW hstrict)
          have hnewValid :
              ValidPartialValueWhenInitialized env
                (store.update lhsLocation
                  { oldSlot with value := PartialValue.value value })
                (.value value) (.ty rhsTy) :=
            RuntimeFrame.validPartialValueWhenInitialized_update_of_owner_and_borrow_dependency_frame
              hvalidValue hvalueOwnerFrame hvalueDepFrame
          have hrootValid :
              ValidPartialValueWhenInitialized env
                (store.update lhsLocation
                  { oldSlot with value := PartialValue.value value })
                oldValue
                (PartialTy.strongLeafUpdate sourceSlot.ty spinePath rhsTy) := by
            have hres :=
              StoreOwnerSpineWhenInitialized.valid_after_leaf_strong_update
                (newSlot :=
                  { oldSlot with value := PartialValue.value value })
                hspine hspineNonempty rfl
                (by
                  rw [← haddrEq]
                  exact hnewValid)
            rw [haddrEq]
            exact hres
          rcases hmapSpine.1 xRoot resultSlot hresultSlot with
            ⟨mappedStrong, hmappedStrong, _hlifeStrong, hstrengthStrong,
              _hshapeStrong⟩
          have hmappedStrongEq :
              mappedStrong =
                { sourceSlot with
                    ty := PartialTy.strongLeafUpdate sourceSlot.ty spinePath
                      rhsTy } := by
            simpa [Env.update] using hmappedStrong.symm
          subst hmappedStrongEq
          have hrootValidResultEnv :
              ValidPartialValueWhenInitialized env'
                (store.update lhsLocation
                  { oldSlot with value := PartialValue.value value })
                oldValue
                (PartialTy.strongLeafUpdate sourceSlot.ty spinePath rhsTy) :=
            validPartialValueWhenInitialized_transport_env
              (fun {targets} hinit =>
                borrowTargetsInitialized_back_of_envStrengthens
                  (EnvSameShapeStrengthening.envStrengthens hglobalMap)
                  hwellFormed.2.2.1 hwellFormed.2.2.2 hinit)
              hrootValid
          exact validPartialValueWhenInitialized_strengthen hrootValidResultEnv
            hstrengthStrong
        · have hdepFrame :
              ∀ location,
                RuntimeFrame.BorrowDependencyWhenInitialized env store oldValue
                  sourceSlot.ty location →
                location ≠ lhsLocation := by
            intro location hdep heq
            rw [heq] at hdep
            rcases RuntimeFrame.borrowDependencyWhenInitialized_witness hdep with
              ⟨m, ts, t, hinitialized, hcontains, hmem, hreads⟩
            have hborrowsX :
                PartialTyBorrowsWellFormedInSlotWhenInitialized env
                  sourceSlot.lifetime sourceSlot.ty := by
              intro mutable' targets' hcontains'
              exact hwellFormed.1 x sourceSlot mutable' targets'
                hsourceSlot ⟨sourceSlot, hsourceSlot, hcontains'⟩
            rcases hborrowsX hcontains t hmem with
              ⟨_hbaseTarget, hwhenInitialized⟩
            rcases hinitialized t hmem with
              ⟨tTy₀, tLt₀, htTyping₀⟩
            rcases hwhenInitialized ⟨tTy₀, tLt₀, htTyping₀⟩ with
              ⟨tTy, tLt, htTyping, _houtlives, _hbase⟩
            rcases LValTargetsTyping.output_full htargets with
              ⟨lhsTy, hOldTyFull⟩
            have htargetsFull :
                LValTargetsTyping env targets (.ty lhsTy) targetLifetime := by
              simpa [hOldTyFull] using htargets
            have hLhsTyping :
                LValTyping env (.deref source) (.ty lhsTy) targetLifetime :=
              LValTyping.borrow hsourceBorrow htargetsFull
            rcases
                envWriteEffectiveWrite_mayReadThrough_source_of_locReads_whenInitialized
                  hwellFormed hsafe hvalidStore hheap hLhsTyping hwrite htTyping
                  hlhsLoc hreads with
              ⟨written, heffective, hmayRead⟩
            rcases PartialTyContains.mono_strengthens_sameShape hcontains
                hstrength hsameShape with
              ⟨resultTargets, hresultContains, hsubset⟩
            have hresultBorrow :
                env' ⊢ x ↝ (.borrow m resultTargets) :=
              ⟨resultSlot, hresultSlot, hresultContains⟩
            exact hnoStale written x resultSlot m resultTargets t
              heffective hresultSlot hresultBorrow (hsubset hmem) hmayRead
          have holdValid :
              ValidPartialValueWhenInitialized env
                (store.update lhsLocation
                  { oldSlot with value := PartialValue.value value })
                oldValue sourceSlot.ty :=
            RuntimeFrame.validPartialValueWhenInitialized_update_of_owner_and_borrow_dependency_frame
              hvalidOld (fun location h heq => howner (heq ▸ h)) hdepFrame
          have holdValidResultEnv :
              ValidPartialValueWhenInitialized env'
                (store.update lhsLocation
                  { oldSlot with value := PartialValue.value value })
                oldValue sourceSlot.ty :=
            validPartialValueWhenInitialized_transport_env
              (fun {targets} hinit =>
                borrowTargetsInitialized_back_of_envStrengthens
                  (EnvSameShapeStrengthening.envStrengthens hglobalMap)
                  hwellFormed.2.2.1 hwellFormed.2.2.2 hinit)
              holdValid
          exact validPartialValueWhenInitialized_strengthen holdValidResultEnv
            hstrength
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
        ¬ ProgramStore.Owns writtenStore owned := by
    intro owned howned hownsWritten
    have hownedOld :
        owned ∈ partialValueOwningLocations oldSlot.value := by
      simpa [partialValuesOwningLocations] using howned
    have hstoreOwnsOld : ProgramStore.OwnsAt store owned lhsLocation := by
      have holdValue :
          oldSlot.value = .value (owningRef owned) :=
        eq_owningRef_of_mem_partialValueOwningLocations hownedOld
      exact ⟨oldSlot.lifetime, by
        cases oldSlot with
        | mk oldValue oldLifetime =>
            cases holdValue
            simpa [owningRef] using hlhsSlot⟩
    rcases hownsWritten with ⟨storage, ownerLifetime, hownerSlotWritten⟩
    by_cases hstorage : storage = lhsLocation
    · subst storage
      rw [hwriteEq] at hownerSlotWritten
      have hnewOwnsOld :
          owned ∈ partialValueOwningLocations (.value value) := by
        have hnewValueEq :
            PartialValue.value value = .value (owningRef owned) := by
          have hslotEq :
              { oldSlot with value := PartialValue.value value } =
                StoreSlot.mk (PartialValue.value (owningRef owned))
                  ownerLifetime := by
            simpa [ProgramStore.update] using hownerSlotWritten
          exact congrArg StoreSlot.value hslotEq
        exact mem_partialValueOwningLocations_of_eq_owningRef hnewValueEq
      exact
        (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
          (by
            simpa [termOwningLocations, termValues, partialValueOwningLocations]
              using hnewOwnsOld))
        ⟨lhsLocation, hstoreOwnsOld⟩
    · have hownerSlotStore :
          store.slotAt storage =
            some (StoreSlot.mk (.value (owningRef owned)) ownerLifetime) := by
        rw [hwriteEq] at hownerSlotWritten
        simpa [ProgramStore.update, hstorage] using hownerSlotWritten
      have hstorageEq :
          storage = lhsLocation :=
        (ValidRuntimeState.validStore hvalidRuntime)
          owned storage lhsLocation
          ⟨ownerLifetime, hownerSlotStore⟩ hstoreOwnsOld
      exact hstorage hstorageEq
  have hallocatedWrite : StoreOwnersAllocated writtenStore :=
    storeOwnersAllocated_write_value_of_validValueWhenInitialized
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
      hwriteStore
  have hrootWrite : HeapSlotsRootLifetime writtenStore :=
    heapSlotsRootLifetime_write
      (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
  have hallocatedFinal : StoreOwnersAllocated store' :=
    drops_storeOwnersAllocated_of_disjoint hdrops hwrittenValidStore
      hallocatedWrite hdropOwnersOrphaned
  have hheapFinal : StoreOwnerTargetsHeap store' :=
    drops_storeOwnerTargetsHeap hdrops hwrittenHeap
  have hrootFinal : HeapSlotsRootLifetime store' :=
    drops_heapSlotsRootLifetime hdrops hrootWrite
  have hsafeFinal : SafeAbstractionWhenInitialized store' env' :=
    safeAbstractionWhenInitialized_drops_of_orphaned_values_early hwellOut
      hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap
      hdropOwnersOrphaned hdrops
  exact ⟨validRuntimeState_assign_step_of_postWriteDrop_invariants
      (lifetime := lifetime)
      hvalidRuntime hallocatedFinal hheapFinal hrootFinal hread hwriteStore
      hdrops,
    hsafeFinal, ValidPartialValueWhenInitialized.unit⟩

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
                  have hpreserve :
                      ∀ x envSlot,
                        env.slotAt x = some envSlot →
                        envSlot.lifetime ≠ blockLifetime →
                        ∃ oldValue,
                          store'.slotAt (VariableProjection x) =
                            some { value := oldValue, lifetime := envSlot.lifetime } ∧
                          ValidPartialValue store' oldValue envSlot.ty := by
                    intro x envSlot henvSlot hsurvives
                    rcases hsafe.2 x envSlot henvSlot with
                      ⟨oldValue, hstoreSlot, hvalidOld⟩
                    have hborrows :
                        PartialTyBorrowsWellFormedInSlot env envSlot.lifetime
                          envSlot.ty := by
                      intro mutable targets hcontains
                      exact hwellBody.1 x envSlot mutable targets henvSlot
                        ⟨envSlot, henvSlot, hcontains⟩
                    have havoidVar :
                        DropsAvoids store _ (VariableProjection x) :=
                      dropsAvoids_var_of_not_owning_var hdropsRaw
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                        (by
                          intro dropValue hmem hownsVar
                          rcases (hdropSet dropValue).mp hmem with
                            ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime,
                              hdropValue⟩
                          have howned :
                              (VariableProjection x : Location) = dropLocation :=
                            eq_location_of_mem_lifetime_drop_value hdropValue hownsVar
                          subst howned
                          have hdropSlotEq :
                              dropSlot =
                                { value := oldValue, lifetime := envSlot.lifetime } := by
                            rw [hstoreSlot] at hdropSlot
                            injection hdropSlot with hdropSlotEq
                            exact hdropSlotEq.symm
                          subst hdropSlotEq
                          exact hsurvives hdropLifetime)
                    have hvalidOld' : ValidPartialValue store' oldValue envSlot.ty := by
                      refine RuntimeFrame.validPartialValue_drops_of_avoids_reaches
                        hdropsRaw hvalidOld ?_
                      intro reached hreach
                      exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
                        hdropsRaw
                        (ValidRuntimeState.validStore hvalidRuntime)
                        hstoreSlot hborrows hvalidOld havoidVar
                        (by
                          intro reached' hreach' dropValue hmem howned
                          rcases (hdropSet dropValue).mp hmem with
                            ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime,
                              hdropValue⟩
                          have hreachedEq : reached' = dropLocation :=
                            eq_location_of_mem_lifetime_drop_value hdropValue howned
                          have hownsReached :
                              ProgramStore.Owns store reached' :=
                            RuntimeFrame.store_owns_of_reaches_stored_validPartialValue
                              hstoreSlot hborrows hvalidOld hreach'
                          have hownsDrop : ProgramStore.Owns store dropLocation := by
                            simpa [hreachedEq] using hownsReached
                          exact hdropDisjoint dropLocation dropSlot hdropSlot
                            hdropLifetime hownsDrop)
                        (by
                          intro dependency hdependency
                          have hslotParent : envSlot.lifetime ≤ lifetime :=
                            LifetimeChild.parent_of_outlives_child_ne hchild
                              (hwellBody.2.1 x envSlot henvSlot)
                              hsurvives
                          exact borrowDependency_dropsAvoids_lifetime
                            hwellBody hsafe
                            (ValidRuntimeState.validStore hvalidRuntime)
                            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                            hdropSet hdropsRaw hdropDisjoint hchild
                            hslotParent hborrows hdependency)
                        hreach
                    have hstoreSlot' :
                        store'.slotAt (VariableProjection x) =
                          some { value := oldValue, lifetime := envSlot.lifetime } :=
                      dropsLifetime_preserves_var_slot_of_not_lifetime hdropsLifetime
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                        (by simpa [VariableProjection] using hstoreSlot)
                        hsurvives
                    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩
                  have hsafeDrop : store' ∼ₛ env.dropLifetime blockLifetime :=
                    dropPreservation_lifetime hsafe hdropsLifetime
                      (dropLifetime_domain_equiv_of_ownerTargetsHeap hsafe
                        hdropsLifetime
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime))
                      hpreserve
                  exact ⟨validRuntimeState_blockB_step_of_child hvalidRuntime hchild
                      (Step.blockB (lifetime := lifetime) hdropsLifetime),
                    hsafeDrop, hresultValue⟩)
    hmulti

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
  constructor
  · intro x
    constructor
    · intro hstore'
      rcases hstore' with ⟨slot, hslot'⟩
      have hslot : store.slotAt (VariableProjection x) = some slot :=
        drops_slotAt_of_slotAt hdrops hslot'
      exact (hsafe.1 x).mp ⟨slot, hslot⟩
    · intro henv
      rcases (hsafe.1 x).mpr henv with ⟨slot, hslot⟩
      have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hdropValuesHeap
      exact ⟨slot, dropsAvoids_slotAt_preserved hdrops havoidVar hslot⟩
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops
        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
        hdropValuesHeap
    have hstoreSlot' :
        store'.slotAt (VariableProjection x) =
          some { value := oldValue, lifetime := envSlot.lifetime } :=
      dropsAvoids_slotAt_preserved hdrops havoidVar hstoreSlot
    have hborrows :
        PartialTyBorrowsWellFormedInSlot env envSlot.lifetime envSlot.ty := by
      intro mutable targets hcontains
      exact hwellFormed.1 x envSlot mutable targets henvSlot
        ⟨envSlot, henvSlot, hcontains⟩
    have hvalidOld' : ValidPartialValue store' oldValue envSlot.ty :=
      RuntimeFrame.validPartialValue_drops_of_avoids_reaches hdrops hvalidOld
        (by
          intro reached hreach
          exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
            hdrops
            (ValidRuntimeState.validStore hvalidRuntime)
            hstoreSlot hborrows hvalidOld havoidVar
            (by
              intro reached' hreach' dropValue hmem howned
              simp at hmem
              subst hmem
              have hownsReached :
                  ProgramStore.Owns store reached' :=
                RuntimeFrame.store_owns_of_reaches_stored_validPartialValue
                  hstoreSlot hborrows hvalidOld hreach'
              exact
                (ValidRuntimeState.storeTermDisjoint hvalidRuntime reached'
                  (by
                    have hhead :
                        reached' ∈ valueOwningLocations value := by
                      simpa [partialValueOwningLocations] using howned
                    simp [termOwningLocations, termValues, hhead]))
                hownsReached)
            (by
              intro dependency hdependency
              rcases borrowDependency_protectedBySomeBase
                  hwellFormed hsafe
                  (ValidRuntimeState.validStore hvalidRuntime)
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                  hborrows hdependency with
                ⟨base, hprotectedDependency⟩
              exact dropsAvoids_of_protectedByBase_unprotected_values
                hdrops
                (ValidRuntimeState.validStore hvalidRuntime)
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hdropValuesHeap
                (by
                  intro dropValue hmem owned howned hprotectedOwned
                  simp at hmem
                  subst hmem
                  have hownedValue :
                      owned ∈ valueOwningLocations value := by
                    simpa [partialValueOwningLocations] using howned
                  rcases hprotectedOwned with hroot | hpath
                  · subst hroot
                    rcases hvalueHeap (VariableProjection base)
                        (by simpa [partialValueOwningLocations] using howned) with
                      ⟨address, hheapLocation⟩
                    cases hheapLocation
                  · exact
                      (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
                        (by
                          simp [termOwningLocations, termValues]
                          exact Or.inl hownedValue))
                      (ProgramStore.OwnsTransitively.to_owns hpath))
                hprotectedDependency)
            hreach)
    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩

/-- `R-Seq` preserves the runtime-selected abstraction for the remaining sequence env. -/
theorem runtimeSafeAbstraction_seq_value_drop
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    RuntimeFrame.RuntimeSafeAbstraction store env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    WellFormedEnv env blockLifetime →
    Drops store [.value value] store' →
    RuntimeFrame.RuntimeSafeAbstraction store' env := by
  intro hruntimeSafe hvalidRuntime hwellFormed hdrops
  rcases hruntimeSafe with ⟨hsafeEvidence, evidenceOf, hselectedSafe⟩
  have hsafe : store ∼ₛ env :=
    RuntimeFrame.SafeAbstractionEvidence.safe hsafeEvidence
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
  refine RuntimeFrame.runtimeSafeAbstraction_drops_of_evidence_frames
    hsafeEvidence evidenceOf hselectedSafe hdrops ?domain ?slotOfEnv
    ?storeBack ?owners ?deps
  · intro x
    constructor
    · intro hstore'
      rcases hstore' with ⟨slot, hslot'⟩
      have hslot : store.slotAt (VariableProjection x) = some slot :=
        drops_slotAt_of_slotAt hdrops hslot'
      exact (hsafe.1 x).mp ⟨slot, hslot⟩
    · intro henv
      rcases (hsafe.1 x).mpr henv with ⟨slot, hslot⟩
      have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hdropValuesHeap
      exact ⟨slot, dropsAvoids_slotAt_preserved hdrops havoidVar hslot⟩
  · intro x envSlot henvSlot
    rcases hsafeEvidence.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, _oldEvidence, _⟩
    have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops
        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
        hdropValuesHeap
    exact ⟨oldValue, dropsAvoids_slotAt_preserved hdrops havoidVar hstoreSlot⟩
  · intro x envSlot oldValue _henvSlot hstoreSlot'
    exact drops_slotAt_of_slotAt hdrops hstoreSlot'
  · intro x envSlot oldValue henvSlot hstoreSlot reached hreach
    have oldEvidence := evidenceOf x envSlot oldValue henvSlot hstoreSlot
    have hborrows :
        PartialTyBorrowsWellFormedInSlot env envSlot.lifetime envSlot.ty := by
      intro mutable targets hcontains
      exact hwellFormed.1 x envSlot mutable targets henvSlot
        ⟨envSlot, henvSlot, hcontains⟩
    have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops
        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
        hdropValuesHeap
    exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
      hdrops
      (ValidRuntimeState.validStore hvalidRuntime)
      hstoreSlot hborrows oldEvidence.valid havoidVar
      (by
        intro reached' howner dropValue hmem howned
        simp at hmem
        subst hmem
        have hownsReached : ProgramStore.Owns store reached' :=
          RuntimeFrame.store_owns_of_reaches_stored_validPartialValue
            hstoreSlot hborrows oldEvidence.valid howner
        exact
          (ValidRuntimeState.storeTermDisjoint hvalidRuntime reached'
            (by
              have hhead : reached' ∈ valueOwningLocations value := by
                simpa [partialValueOwningLocations] using howned
              simp [termOwningLocations, termValues, hhead]))
          hownsReached)
      (by
        intro dependency hdependency
        rcases borrowDependency_protectedBySomeBase
            hwellFormed hsafe
            (ValidRuntimeState.validStore hvalidRuntime)
            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
            hborrows hdependency with
          ⟨base, hprotectedDependency⟩
        exact dropsAvoids_of_protectedByBase_unprotected_values
          hdrops
          (ValidRuntimeState.validStore hvalidRuntime)
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hdropValuesHeap
          (by
            intro dropValue hmem owned howned hprotectedOwned
            simp at hmem
            subst hmem
            have hownedValue :
                owned ∈ valueOwningLocations value := by
              simpa [partialValueOwningLocations] using howned
            rcases hprotectedOwned with hroot | hpath
            · subst hroot
              rcases hvalueHeap (VariableProjection base)
                  (by simpa [partialValueOwningLocations] using howned) with
                ⟨address, hheapLocation⟩
              cases hheapLocation
            · exact
                (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
                  (by
                    simp [termOwningLocations, termValues]
                    exact Or.inl hownedValue))
                (ProgramStore.OwnsTransitively.to_owns hpath))
          hprotectedDependency)
      (RuntimeFrame.OwnerReaches.reaches hreach)
  · intro x envSlot oldValue henvSlot hstoreSlot dependency hdependency
    have oldEvidence := evidenceOf x envSlot oldValue henvSlot hstoreSlot
    have hborrows :
        PartialTyBorrowsWellFormedInSlot env envSlot.lifetime envSlot.ty := by
      intro mutable targets hcontains
      exact hwellFormed.1 x envSlot mutable targets henvSlot
        ⟨envSlot, henvSlot, hcontains⟩
    have hborrowDependency :
        RuntimeFrame.BorrowDependency store oldValue envSlot.ty dependency :=
      RuntimeFrame.SelectedBorrowDependency.borrowDependency
        (RuntimeFrame.EvidenceBorrowDependency.selected hdependency)
    rcases borrowDependency_protectedBySomeBase
        hwellFormed hsafe
        (ValidRuntimeState.validStore hvalidRuntime)
        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
        hborrows hborrowDependency with
      ⟨base, hprotectedDependency⟩
    exact dropsAvoids_of_protectedByBase_unprotected_values
      hdrops
      (ValidRuntimeState.validStore hvalidRuntime)
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
      hdropValuesHeap
      (by
        intro dropValue hmem owned howned hprotectedOwned
        simp at hmem
        subst hmem
        have hownedValue :
            owned ∈ valueOwningLocations value := by
          simpa [partialValueOwningLocations] using howned
        rcases hprotectedOwned with hroot | hpath
        · subst hroot
          rcases hvalueHeap (VariableProjection base)
              (by simpa [partialValueOwningLocations] using howned) with
            ⟨address, hheapLocation⟩
          cases hheapLocation
        · exact
            (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
              (by
                simp [termOwningLocations, termValues]
                exact Or.inl hownedValue))
            (ProgramStore.OwnsTransitively.to_owns hpath))
      hprotectedDependency

theorem safeAbstractionWhenInitialized_dropLifetime_of_preserved
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
        ValidPartialValueWhenInitialized (env.dropLifetime lifetime) store'
          value envSlot.ty) →
    SafeAbstractionWhenInitialized store' (env.dropLifetime lifetime) := by
  intro hdomain hpreserve
  constructor
  · exact hdomain
  · intro x envSlot henvDropped
    rcases (Env.dropLifetime_slotAt_eq_some.mp henvDropped) with
      ⟨henv, hlifetime⟩
    exact hpreserve x envSlot henv hlifetime

theorem dropPreservation_lifetime_whenInitialized
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    SafeAbstractionWhenInitialized store env →
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
        ValidPartialValueWhenInitialized (env.dropLifetime lifetime) store'
          value envSlot.ty) →
    SafeAbstractionWhenInitialized store' (env.dropLifetime lifetime) := by
  intro _hsafe _hdrops hdomain hpreserve
  exact safeAbstractionWhenInitialized_dropLifetime_of_preserved
    hdomain hpreserve

theorem dropLifetime_envDomain_of_storeSurvivor_whenInitialized
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime}
    {x : Name} :
    SafeAbstractionWhenInitialized store env →
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

theorem dropLifetime_storeDomain_of_envSurvivor_of_ownerTargetsHeap_whenInitialized
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime}
    {x : Name} :
    SafeAbstractionWhenInitialized store env →
    DropsLifetime store lifetime store' →
    StoreOwnerTargetsHeap store →
    (∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot) →
    ∃ slot, store'.slotAt (VariableProjection x) = some slot := by
  intro hsafe hdrops hheap henvDomain
  rcases henvDomain with ⟨envSlot, henvDropped⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp henvDropped with
    ⟨henv, hlifetime⟩
  rcases (hsafe.1 x).mpr ⟨envSlot, henv⟩ with ⟨slot, hslot⟩
  have hslotLifetime : slot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
    rw [hslot] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact congrArg StoreSlot.lifetime hslotEq
  exact ⟨slot, dropsLifetime_preserves_var_slot_of_not_lifetime hdrops hheap
    hslot (by simpa [hslotLifetime] using hlifetime)⟩

theorem dropLifetime_domain_equiv_of_ownerTargetsHeap_whenInitialized
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    SafeAbstractionWhenInitialized store env →
    DropsLifetime store lifetime store' →
    StoreOwnerTargetsHeap store →
    ∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot := by
  intro hsafe hdrops hheap x
  constructor
  · exact dropLifetime_envDomain_of_storeSurvivor_whenInitialized
      hsafe hdrops (by
        intro slot hslot
        exact dropsLifetime_slot_not_dropped hdrops hslot)
  · exact dropLifetime_storeDomain_of_envSurvivor_of_ownerTargetsHeap_whenInitialized
      hsafe hdrops hheap

theorem preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop
    {store finalStore : ProgramStore} {env : Env}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    SafeAbstractionWhenInitialized store env →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnvWhenInitialized env blockLifetime →
    WellFormedTy env ty lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    TerminalStateSafeWhenInitialized finalStore finalValue
      (env.dropLifetime blockLifetime) ty := by
  intro hvalidRuntime hsafe hchild hwellBody hwellTy hvalidValue hmulti
  have hinitDropBack : ∀ {targets : List LVal},
      BorrowTargetsInitialized (env.dropLifetime blockLifetime) targets →
      BorrowTargetsInitialized env targets := by
    intro targets hinitialized target htarget
    rcases hinitialized target htarget with
      ⟨targetTy, targetLifetime, htargetTyping⟩
    exact ⟨targetTy, targetLifetime, LValTyping.of_dropLifetime htargetTyping⟩
  exact preservation_runtime_multistep_of_step_to_value_whenInitialized
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
              have hwellTyWhen :
                  WellFormedTyWhenInitialized env ty lifetime :=
                hwellTy.whenInitialized
              have hresultValueEnv :
                  ValidPartialValueWhenInitialized env store'
                    (.value value) (.ty ty) :=
                RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_reachesWhenInitialized
                  hdropsRaw hvalidValue
                  (by
                    intro location hreach
                    exact RuntimeFrame.dropsAvoids_of_reaches_validPartialValueWhenInitialized
                      hdropsRaw
                      (ValidRuntimeState.validStore hvalidRuntime)
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
                              hwellTy hreachVar rfl
                        | heap address =>
                            have hroot : dropSlot.lifetime = Lifetime.root :=
                              ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime
                                address dropSlot hdropSlot
                            exact LifetimeChild.child_ne_root hchild
                              (hdropLifetime ▸ hroot))
                      (by
                        intro dependency hdependency
                        exact borrowDependencyWhenInitialized_dropsAvoids_lifetime
                          hwellBody hsafe
                          (ValidRuntimeState.validStore hvalidRuntime)
                          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                          hdropSet hdropsRaw hdropDisjoint hchild
                          (LifetimeOutlives.refl lifetime)
                          (PartialTyBorrowsWellFormedInSlotWhenInitialized.of_wellFormedTy
                            hwellTyWhen)
                          hdependency)
                      hreach)
              have hresultValue :
                  ValidPartialValueWhenInitialized (env.dropLifetime blockLifetime) store'
                    (.value value) (.ty ty) :=
                validPartialValueWhenInitialized_transport_env hinitDropBack
                  hresultValueEnv
              have hpreserve :
                  ∀ x envSlot,
                    env.slotAt x = some envSlot →
                    envSlot.lifetime ≠ blockLifetime →
                    ∃ oldValue,
                      store'.slotAt (VariableProjection x) =
                        some { value := oldValue, lifetime := envSlot.lifetime } ∧
                      ValidPartialValueWhenInitialized (env.dropLifetime blockLifetime)
                        store' oldValue envSlot.ty := by
                intro x envSlot henvSlot hsurvives
                rcases hsafe.2 x envSlot henvSlot with
                  ⟨oldValue, hstoreSlot, hvalidOld⟩
                have hborrows :
                    PartialTyBorrowsWellFormedInSlotWhenInitialized env
                      envSlot.lifetime envSlot.ty := by
                  intro mutable targets hcontains
                  exact hwellBody.1 x envSlot mutable targets henvSlot
                    ⟨envSlot, henvSlot, hcontains⟩
                have havoidVar :
                    DropsAvoids store _ (VariableProjection x) :=
                  dropsAvoids_var_of_not_owning_var hdropsRaw
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    (by
                      intro dropValue hmem hownsVar
                      rcases (hdropSet dropValue).mp hmem with
                        ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime,
                          hdropValue⟩
                      have howned :
                          (VariableProjection x : Location) = dropLocation :=
                        eq_location_of_mem_lifetime_drop_value hdropValue hownsVar
                      subst howned
                      have hdropSlotEq :
                          dropSlot =
                            { value := oldValue, lifetime := envSlot.lifetime } := by
                        rw [hstoreSlot] at hdropSlot
                        injection hdropSlot with hdropSlotEq
                        exact hdropSlotEq.symm
                      subst hdropSlotEq
                      exact hsurvives hdropLifetime)
                have hvalidOldEnv' :
                    ValidPartialValueWhenInitialized env store' oldValue envSlot.ty := by
                  refine
                    RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_reachesWhenInitialized
                      hdropsRaw hvalidOld ?_
                  intro reached hreach
                  exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized
                    hdropsRaw
                    (ValidRuntimeState.validStore hvalidRuntime)
                    hstoreSlot hvalidOld havoidVar
                    (by
                      intro reached' hreach' dropValue hmem howned
                      rcases (hdropSet dropValue).mp hmem with
                        ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime,
                          hdropValue⟩
                      have hreachedEq : reached' = dropLocation :=
                        eq_location_of_mem_lifetime_drop_value hdropValue howned
                      have hownsReached :
                          ProgramStore.Owns store reached' :=
                        RuntimeFrame.store_owns_of_reaches_stored_validPartialValueWhenInitialized
                          hstoreSlot hvalidOld hreach'
                      have hownsDrop : ProgramStore.Owns store dropLocation := by
                        simpa [hreachedEq] using hownsReached
                      exact hdropDisjoint dropLocation dropSlot hdropSlot
                        hdropLifetime hownsDrop)
                    (by
                      intro dependency hdependency
                      have hslotParent : envSlot.lifetime ≤ lifetime :=
                        LifetimeChild.parent_of_outlives_child_ne hchild
                          (hwellBody.2.1 x envSlot henvSlot)
                          hsurvives
                      exact borrowDependencyWhenInitialized_dropsAvoids_lifetime
                        hwellBody hsafe
                        (ValidRuntimeState.validStore hvalidRuntime)
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                        hdropSet hdropsRaw hdropDisjoint hchild
                        hslotParent hborrows hdependency)
                    hreach
                have hvalidOldDrop :
                    ValidPartialValueWhenInitialized (env.dropLifetime blockLifetime)
                      store' oldValue envSlot.ty :=
                  validPartialValueWhenInitialized_transport_env hinitDropBack
                    hvalidOldEnv'
                have hstoreSlot' :
                    store'.slotAt (VariableProjection x) =
                      some { value := oldValue, lifetime := envSlot.lifetime } :=
                  dropsLifetime_preserves_var_slot_of_not_lifetime hdropsLifetime
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    (by simpa [VariableProjection] using hstoreSlot)
                    hsurvives
                exact ⟨oldValue, hstoreSlot', hvalidOldDrop⟩
              have hsafeDrop :
                  SafeAbstractionWhenInitialized store'
                    (env.dropLifetime blockLifetime) :=
                dropPreservation_lifetime_whenInitialized hsafe hdropsLifetime
                  (dropLifetime_domain_equiv_of_ownerTargetsHeap_whenInitialized
                    hsafe hdropsLifetime
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime))
                  hpreserve
              exact ⟨validRuntimeState_blockB_step_of_child hvalidRuntime hchild
                  (Step.blockB (lifetime := lifetime) hdropsLifetime),
                hsafeDrop, hresultValue⟩)
    hmulti

theorem safeAbstraction_seq_value_drop_whenInitialized
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    SafeAbstractionWhenInitialized store env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    WellFormedEnvWhenInitialized env blockLifetime →
    Drops store [.value value] store' →
    SafeAbstractionWhenInitialized store' env := by
  intro hsafe hvalidRuntime hwellFormed hdrops
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
  constructor
  · intro x
    constructor
    · intro hstore'
      rcases hstore' with ⟨slot, hslot'⟩
      have hslot : store.slotAt (VariableProjection x) = some slot :=
        drops_slotAt_of_slotAt hdrops hslot'
      exact (hsafe.1 x).mp ⟨slot, hslot⟩
    · intro henv
      rcases (hsafe.1 x).mpr henv with ⟨slot, hslot⟩
      have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hdropValuesHeap
      exact ⟨slot, dropsAvoids_slotAt_preserved hdrops havoidVar hslot⟩
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops
        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
        hdropValuesHeap
    have hstoreSlot' :
        store'.slotAt (VariableProjection x) =
          some { value := oldValue, lifetime := envSlot.lifetime } :=
      dropsAvoids_slotAt_preserved hdrops havoidVar hstoreSlot
    have hborrows :
        PartialTyBorrowsWellFormedInSlotWhenInitialized env
          envSlot.lifetime envSlot.ty := by
      intro mutable targets hcontains
      exact hwellFormed.1 x envSlot mutable targets henvSlot
        ⟨envSlot, henvSlot, hcontains⟩
    have hvalidOld' :
        ValidPartialValueWhenInitialized env store' oldValue envSlot.ty :=
      RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_reachesWhenInitialized
        hdrops hvalidOld
        (by
          intro reached hreach
          exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized
            hdrops
            (ValidRuntimeState.validStore hvalidRuntime)
            hstoreSlot hvalidOld havoidVar
            (by
              intro reached' hreach' dropValue hmem howned
              simp at hmem
              subst hmem
              have hownsReached :
                  ProgramStore.Owns store reached' :=
                RuntimeFrame.store_owns_of_reaches_stored_validPartialValueWhenInitialized
                  hstoreSlot hvalidOld hreach'
              exact
                (ValidRuntimeState.storeTermDisjoint hvalidRuntime reached'
                  (by
                    have hhead :
                        reached' ∈ valueOwningLocations value := by
                      simpa [partialValueOwningLocations] using howned
                    simp [termOwningLocations, termValues, hhead]))
                hownsReached)
            (by
              intro dependency hdependency
              exact dropsAvoids_of_borrowDependencyWhenInitialized_unprotected_values
                hdrops hwellFormed hsafe
                (ValidRuntimeState.validStore hvalidRuntime)
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hdropValuesHeap
                (by
                  intro dropValue hmem owned howned base hprotectedOwned
                  simp at hmem
                  subst hmem
                  have hownedValue :
                      owned ∈ valueOwningLocations value := by
                    simpa [partialValueOwningLocations] using howned
                  rcases hprotectedOwned with hroot | hpath
                  · subst hroot
                    rcases hvalueHeap (VariableProjection base)
                        (by simpa [partialValueOwningLocations] using howned) with
                      ⟨address, hheapLocation⟩
                    cases hheapLocation
                  · exact
                      (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
                        (by
                          simp [termOwningLocations, termValues]
                          exact Or.inl hownedValue))
                      (ProgramStore.OwnsTransitively.to_owns hpath))
                hborrows hdependency)
            hreach)
    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩

theorem preservation_block_terminal_multistep_runtime_whenInitialized_of_first_step
    {store finalStore : ProgramStore} {env' : Env}
    {lifetime blockLifetime : Lifetime} {terms : List Term}
    {finalValue : Value} {ty : Ty} :
    (∀ value next rest store',
      terms = .val value :: next :: rest →
      Drops store [.value value] store' →
      MultiStep store' lifetime (.block blockLifetime (next :: rest))
        finalStore (.val finalValue) →
      TerminalStateSafeWhenInitialized finalStore finalValue env' ty) →
    (∀ term rest store' term',
      terms = term :: rest →
      Step store blockLifetime term store' term' →
      MultiStep store' lifetime (.block blockLifetime (term' :: rest))
        finalStore (.val finalValue) →
      TerminalStateSafeWhenInitialized finalStore finalValue env' ty) →
    (∀ value store',
      terms = [.val value] →
      DropsLifetime store blockLifetime store' →
      MultiStep store' lifetime (.val value) finalStore (.val finalValue) →
      TerminalStateSafeWhenInitialized finalStore finalValue env' ty) →
    MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
    TerminalStateSafeWhenInitialized finalStore finalValue env' ty := by
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
Bounded preservation.

This is the recursive preservation skeleton used by the paper-facing theorem.
The induction follows the typing derivation and re-establishes terminal safety
for the environment produced by the typing rule.
-/
theorem preservation_bounded
    (fuel : Nat) {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    term.size ≤ fuel →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnvWhenInitialized env₁ lifetime →
    SafeAbstractionWhenInitialized store env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateSafeWhenInitialized finalStore finalValue env₂ ty := by
  sorry
theorem preservation
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateSafeWhenInitialized finalStore finalValue env₂ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hsafe
    htyping hmulti
  exact preservation_bounded term.size (Nat.le_refl _) hsource
    hvalidRuntime hvalidStoreTyping (WellFormedEnv.whenInitialized hwellFormed)
    hsafe.whenInitialized htyping
    hmulti

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/--
Lemma 4.11, Preservation.

This is the paper-facing preservation statement.
-/
theorem lemma_4_11_preservation
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    TerminalStateSafeWhenInitialized finalStore finalValue env₂ ty :=
  _root_.LwRust.Paper.preservation hsource hvalid hstoreTyping hwellFormed
    hsafe htyping hmulti

end LwRust.Paper.Soundness
