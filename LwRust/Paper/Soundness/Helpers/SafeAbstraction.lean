import LwRust.Paper.Soundness.Helpers.Validity

/-!
# Soundness helpers: SafeAbstraction

Section 4.2: safe abstractions and variable projection.
-/

namespace LwRust
namespace Paper

open Core

/-! ## Section 4.2: Safe Abstractions -/

/--
Definition 4.4, valid type/value abstraction `S ⊢ v⊥ ∼ T̃`.
-/
inductive ValidPartialValue : ProgramStore → PartialValue → PartialTy → Prop where
  /-- V-Unit. -/
  | unit {store : ProgramStore} :
      ValidPartialValue store (.value .unit) (.ty .unit)
  /-- V-Int. -/
  | int {store : ProgramStore} {value : Int} :
      ValidPartialValue store (.value (.int value)) (.ty .int)
  /-- V-Undef. -/
  | undef {store : ProgramStore} {ty : Ty} :
      ValidPartialValue store .undef (.undef ty)
  /-- V-Borrow. -/
  | borrow {store : ProgramStore} {location : Location} {mutable : Bool}
      {targets : List LVal} {target : LVal} :
      target ∈ targets →
      store.loc target = some location →
      ValidPartialValue store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets))
  /-- V-Box. -/
  | box {store : ProgramStore} {location : Location} {slot : StoreSlot}
      {inner : PartialTy} :
      store.slotAt location = some slot →
      ValidPartialValue store slot.value inner →
      ValidPartialValue store
        (.value (.ref { location := location, owner := true }))
        (.box inner)
  /-- V-Box, full `Box<T>` type. -/
  | boxFull {store : ProgramStore} {location : Location} {slot : StoreSlot}
      {ty : Ty} :
      store.slotAt location = some slot →
      ValidPartialValue store slot.value (.ty ty) →
      ValidPartialValue store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty))

def ValidValue (store : ProgramStore) (value : Value) (ty : Ty) : Prop :=
  ValidPartialValue store (.value value) (.ty ty)

notation:50 store:51 " ⊢ " value:51 " ∼ " ty:51 =>
  ValidPartialValue store value ty

/--
Dropping a list of non-owning partial values preserves existing partial-value
abstractions, since the store is unchanged.
-/
theorem validPartialValue_after_drops_all_nonOwner {store store' : ProgramStore}
    {values : List PartialValue} {value : PartialValue} {ty : PartialTy} :
    (∀ dropped, dropped ∈ values → PartialValueNonOwner dropped) →
    Drops store values store' →
    ValidPartialValue store value ty →
    ValidPartialValue store' value ty := by
  intro hnonOwner hdrops hvalid
  have hstore : store' = store := drops_all_nonOwner_eq hnonOwner hdrops
  subst hstore
  exact hvalid

/--
Definition 4.5, valid store typing `S ▷ t ⊢ σ`.

Our `StoreTyping` is keyed by locations, so this uses the existing
`ValueTyping σ v T` relation to express `σ(v) = T`.
-/
def ValidStoreTyping (store : ProgramStore) (term : Term) (typing : StoreTyping) : Prop :=
  ∀ value,
    value ∈ termValues term →
    ∃ ty, ValueTyping typing value ty ∧ ValidValue store value ty

theorem validStoreTyping_box_inner {store : ProgramStore} {term : Term}
    {typing : StoreTyping} :
    ValidStoreTyping store (.box term) typing →
    ValidStoreTyping store term typing := by
  intro hvalid value hmem
  exact hvalid value (by simpa [termValues] using hmem)

theorem validStoreTyping_declare_inner {store : ProgramStore} {x : Name}
    {term : Term} {typing : StoreTyping} :
    ValidStoreTyping store (.letMut x term) typing →
    ValidStoreTyping store term typing := by
  intro hvalid value hmem
  exact hvalid value (by simpa [termValues] using hmem)

theorem validStoreTyping_assign_inner {store : ProgramStore} {lhs : LVal}
    {rhs : Term} {typing : StoreTyping} :
    ValidStoreTyping store (.assign lhs rhs) typing →
    ValidStoreTyping store rhs typing := by
  intro hvalid value hmem
  exact hvalid value (by simpa [termValues] using hmem)

/--
After `R-Seq` drops a completed head value, the remaining block mentions only
runtime values that were already present in the original block.
-/
theorem validStoreTyping_block_tail {store : ProgramStore} {typing : StoreTyping}
    {blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    ValidStoreTyping store (.block blockLifetime (.val value :: next :: rest)) typing →
    ValidStoreTyping store (.block blockLifetime (next :: rest)) typing := by
  intro htyping candidate hmem
  exact htyping candidate (by
    simp [termValues] at hmem ⊢
    exact Or.inr hmem)

theorem validPartialValue_owningLocation_allocated {store : ProgramStore}
    {partialValue : PartialValue} {partialTy : PartialTy} {owned : Location} :
    ValidPartialValue store partialValue partialTy →
    owned ∈ partialValueOwningLocations partialValue →
    ∃ slot, store.slotAt owned = some slot := by
  intro hvalid hmem
  cases hvalid with
  | unit =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | int =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | undef =>
      simp [partialValueOwningLocations] at hmem
  | borrow =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | box hslot _hinner =>
      rename_i location slot inner
      have howned : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] using hmem
      subst howned
      exact ⟨_, hslot⟩
  | boxFull hslot _hinner =>
      rename_i location slot ty
      have howned : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] using hmem
      subst howned
      exact ⟨_, hslot⟩

theorem validPartialValue_nonOwner_of_envShape {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValue store value ty →
    (ty = .ty .unit ∨ ty = .ty .int ∨ (∃ inner, ty = .undef inner) ∨
      ∃ mutable targets, ty = .ty (.borrow mutable targets)) →
    PartialValueNonOwner value := by
  intro hvalid hshape
  cases hvalid with
  | unit =>
      exact partialValueNonOwner_unit
  | int =>
      exact partialValueNonOwner_int _
  | undef =>
      exact partialValueNonOwner_undef
  | borrow =>
      exact partialValueNonOwner_borrowed _
  | box =>
      rcases hshape with hunit | hint | hundef | hborrow
      · cases hunit
      · cases hint
      · rcases hundef with ⟨_inner, hundef⟩
        cases hundef
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow
  | boxFull =>
      rcases hshape with hunit | hint | hundef | hborrow
      · cases hunit
      · cases hint
      · rcases hundef with ⟨_inner, hundef⟩
        cases hundef
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow

theorem partialTy_nonOwnerShape_of_shapeCompatible_right_ty {env : Env}
    {oldTy : PartialTy} {rhsTy : Ty} :
    ShapeCompatible env oldTy (.ty rhsTy) →
    oldTy = .ty .unit ∨ oldTy = .ty .int ∨
      (∃ inner, oldTy = .undef inner) ∨
      ∃ mutable targets, oldTy = .ty (.borrow mutable targets) := by
  intro hshape
  cases hshape with
  | unit =>
      exact Or.inl rfl
  | int =>
      exact Or.inr (Or.inl rfl)
  | borrow =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))
  | undefLeft _hinner =>
      exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))

theorem ty_nonOwnerShape_of_strengthens_shapeCompatible_right_ty {env : Env}
    {selectedTy : Ty} {oldTy : PartialTy} {rhsTy : Ty} :
    PartialTyStrengthens (.ty selectedTy) oldTy →
    ShapeCompatible env oldTy (.ty rhsTy) →
    selectedTy = .unit ∨ selectedTy = .int ∨
      ∃ mutable targets, selectedTy = .borrow mutable targets := by
  intro hstrength hshape
  cases hshape with
  | unit =>
      cases hstrength
      exact Or.inl rfl
  | int =>
      cases hstrength
      exact Or.inr (Or.inl rfl)
  | borrow =>
      cases hstrength with
      | reflex =>
          exact Or.inr (Or.inr ⟨_, _, rfl⟩)
      | borrow _hsubset =>
          exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  | undefLeft hinner =>
      cases hstrength with
      | intoUndef hinnerStrength =>
          cases hinner with
          | unit =>
              cases hinnerStrength
              exact Or.inl rfl
          | int =>
              cases hinnerStrength
              exact Or.inr (Or.inl rfl)
          | borrow =>
              cases hinnerStrength with
              | reflex =>
                  exact Or.inr (Or.inr ⟨_, _, rfl⟩)
              | borrow _hsubset =>
                  exact Or.inr (Or.inr ⟨_, _, rfl⟩)

theorem validValue_owningLocation_allocated {store : ProgramStore}
    {value : Value} {ty : Ty} {owned : Location} :
    ValidValue store value ty →
    owned ∈ valueOwningLocations value →
    ∃ slot, store.slotAt owned = some slot := by
  intro hvalid hmem
  exact validPartialValue_owningLocation_allocated hvalid
    (by simpa [partialValueOwningLocations] using hmem)

theorem validValue_fresh_not_owningLocation {store : ProgramStore}
    {value : Value} {ty : Ty} {owned : Location} :
    ValidValue store value ty →
    store.fresh owned →
    owned ∉ valueOwningLocations value := by
  intro hvalid hfresh hmem
  rcases validValue_owningLocation_allocated hvalid hmem with ⟨slot, hslot⟩
  rw [ProgramStore.fresh] at hfresh
  rw [hfresh] at hslot
  cases hslot

theorem storeOwnersAllocated_update_value_of_validValue {store : ProgramStore}
    {updatedLocation : Location} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    StoreOwnersAllocated
      (store.update updatedLocation { value := .value value, lifetime := lifetime }) := by
  intro hallocated hvalidValue
  exact storeOwnersAllocated_update hallocated (by
    intro owned hmem
    rcases validValue_owningLocation_allocated hvalidValue
        (by simpa [partialValueOwningLocations] using hmem) with
      ⟨allocatedSlot, hallocatedSlot⟩
    by_cases howned : owned = updatedLocation
    · subst howned
      exact ⟨{ value := .value value, lifetime := lifetime }, by
        simp [ProgramStore.update]⟩
    · exact ⟨allocatedSlot, by
        simpa [ProgramStore.update, howned] using hallocatedSlot⟩)

theorem storeOwnersAllocated_declare_of_validValue {store : ProgramStore}
    {x : Name} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    StoreOwnersAllocated (store.declare x lifetime value) := by
  intro hallocated hvalidValue
  exact storeOwnersAllocated_update_value_of_validValue
    (updatedLocation := .var x) hallocated hvalidValue

theorem storeOwnersAllocated_boxAt_of_validValue {store : ProgramStore}
    {address : Nat} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    StoreOwnersAllocated (store.boxAt address value).1 := by
  intro hallocated hvalidValue
  exact storeOwnersAllocated_update_value_of_validValue
    (updatedLocation := .heap address)
    (lifetime := Lifetime.root) hallocated hvalidValue

/-- Writing a valid value through an lval preserves owner allocation. -/
theorem storeOwnersAllocated_write_value_of_validValue {store store' : ProgramStore}
    {lv : LVal} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidValue store value ty →
    store.write lv (.value value) = some store' →
    StoreOwnersAllocated store' := by
  intro hallocated hvalidValue hwrite
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
          exact storeOwnersAllocated_update_value_of_validValue hallocated hvalidValue

/-- Definition 4.6, variable projection `Θ`. -/
def VariableProjection (name : Name) : Location :=
  .var name

/--
Definition 4.7, safe abstraction `S ∼ Γ`.

Heap locations are intentionally ignored in the domain agreement, as in the
paper.  Because stores and environments are abstract partial maps, domain
agreement is stated pointwise for variable locations.
-/
def SafeAbstraction (store : ProgramStore) (env : Env) : Prop :=
  (∀ x, (∃ slot, store.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, env.slotAt x = some envSlot) ∧
  ∀ x envSlot,
    env.slotAt x = some envSlot →
    ∃ value,
      store.slotAt (VariableProjection x) =
        some (StoreSlot.mk value envSlot.lifetime) ∧
      ValidPartialValue store value envSlot.ty

infix:50 " ∼ₛ " => SafeAbstraction

/--
Drop Preservation, non-owning drop-set fragment: if every value in `ψ` is
non-owning, then `drop(S, ψ)` leaves the safe abstraction unchanged.
-/
theorem safeAbstraction_drops_all_nonOwner {store store' : ProgramStore}
    {env : Env} {values : List PartialValue} :
    store ∼ₛ env →
    (∀ value, value ∈ values → PartialValueNonOwner value) →
    Drops store values store' →
    store' ∼ₛ env := by
  intro hsafe hnonOwner hdrops
  have hstore : store' = store := drops_all_nonOwner_eq hnonOwner hdrops
  subst hstore
  exact hsafe

/--
If no store slot has lifetime `m`, then no environment slot has lifetime `m`
under a safe abstraction.
-/
theorem safeAbstraction_env_no_lifetime_of_store_no_lifetime {store : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ lifetime) →
    ∀ x envSlot,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ lifetime := by
  intro hsafe hnoStore x envSlot henv
  rcases hsafe.2 x envSlot henv with ⟨value, hslot, _hvalid⟩
  exact hnoStore (VariableProjection x) { value := value, lifetime := envSlot.lifetime } hslot

/-- Dropping an absent lifetime leaves the typing environment unchanged. -/
theorem Env.dropLifetime_eq_self_of_no_lifetime {env : Env} {lifetime : Lifetime} :
    (∀ x slot, env.slotAt x = some slot → slot.lifetime ≠ lifetime) →
    env.dropLifetime lifetime = env := by
  intro hnoLifetime
  cases env with
  | mk slotAt =>
      simp [Env.dropLifetime] at hnoLifetime ⊢
      funext x
      cases hslot : slotAt x with
      | none =>
          simp
      | some slot =>
          simp [hnoLifetime x slot hslot]

/--
Drop Preservation for an absent lifetime: if no store slot has lifetime `m`,
then `drop(S, m)` and `drop(Γ, m)` are both no-ops.
-/
theorem safeAbstraction_dropsLifetime_no_slots {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ lifetime) →
    DropsLifetime store lifetime store' →
    store' ∼ₛ env.dropLifetime lifetime := by
  intro hsafe hnoStore hdrops
  have hstore : store' = store := dropsLifetime_no_slots_eq hnoStore hdrops
  have henv : env.dropLifetime lifetime = env :=
    Env.dropLifetime_eq_self_of_no_lifetime
      (safeAbstraction_env_no_lifetime_of_store_no_lifetime hsafe hnoStore)
  rw [hstore, henv]
  exact hsafe

/-! ### A concrete lifetime-drop boundary

The abstract `ProgramStore` permits an owning reference to point at a variable
location.  That is more general than the operational states produced by `box`,
where owning references target heap locations.  The following tiny store shows
why the general Lemma 9.5 lifetime-drop proof cannot be recovered from the
current store validity interface alone: dropping the inner-lifetime variable `x`
recursively drops the outer-lifetime variable `y`, while `Γ.dropLifetime` keeps
`y`.
-/

def dropCounterInner : Lifetime := [0, 0]

def dropCounterOuter : Lifetime := [0]

def dropCounterXSlot : StoreSlot :=
  { value := .value (.ref { location := .var "y", owner := true }),
    lifetime := dropCounterInner }

def dropCounterYSlot : StoreSlot :=
  { value := .value .unit, lifetime := dropCounterOuter }

def dropCounterStore : ProgramStore :=
  (ProgramStore.empty.update (.var "x") dropCounterXSlot).update (.var "y")
    dropCounterYSlot

def dropCounterStoreAfter : ProgramStore :=
  (dropCounterStore.erase (.var "x")).erase (.var "y")

def dropCounterEnv : Env :=
  (Env.empty.update "x"
      { ty := .box (.ty .unit), lifetime := dropCounterInner }).update "y"
    { ty := .ty .unit, lifetime := dropCounterOuter }

theorem dropCounter_dropsLifetime :
    DropsLifetime dropCounterStore dropCounterInner dropCounterStoreAfter := by
  refine ProgramStore.DropsLifetime.intro (dropSet := [
      .value (.ref { location := .var "x", owner := true })]) ?dropSet ?drops
  · intro value
    constructor
    · intro hmem
      simp at hmem
      subst hmem
      exact ⟨.var "x", dropCounterXSlot, by
          simp [dropCounterStore, dropCounterXSlot, dropCounterYSlot],
        rfl, rfl⟩
    · intro h
      rcases h with ⟨location, slot, hslot, hlifetime, hvalue⟩
      have hlocation : location = .var "x" := by
        by_cases hx : location = .var "x"
        · exact hx
        · by_cases hy : location = .var "y"
          · subst hy
            simp [dropCounterStore, dropCounterXSlot, dropCounterYSlot] at hslot
            subst hslot
            simp [dropCounterInner, dropCounterOuter] at hlifetime
          · cases location with
            | var name =>
                simp [dropCounterStore, dropCounterXSlot, dropCounterYSlot, hx, hy] at hslot
            | heap address =>
                simp [dropCounterStore, dropCounterXSlot, dropCounterYSlot] at hslot
      subst hlocation
      simp [dropCounterStore, dropCounterXSlot, dropCounterYSlot] at hslot
      subst hslot
      simp [hvalue]
  · refine ProgramStore.Drops.ownerPresent (ref := { location := .var "x", owner := true })
      (slot := dropCounterXSlot) rfl ?xSlot ?tail
    · simp [dropCounterStore, dropCounterXSlot, dropCounterYSlot]
    · refine ProgramStore.Drops.ownerPresent (ref := { location := .var "y", owner := true })
        (slot := dropCounterYSlot) rfl ?ySlot ?unitTail
      · simp [dropCounterStore, dropCounterXSlot, dropCounterYSlot, ProgramStore.erase]
      · refine ProgramStore.Drops.nonOwner ?unitNonOwner ProgramStore.Drops.nil
        intro ref
        cases ref with
        | mk location owner =>
            cases location <;> cases owner <;> simp [dropCounterYSlot]

theorem dropCounter_safeAbstraction :
    dropCounterStore ∼ₛ dropCounterEnv := by
  constructor
  · intro name
    constructor
    · intro hstore
      by_cases hx : name = "x"
      · subst hx
        exact ⟨{ ty := .box (.ty .unit), lifetime := dropCounterInner }, by
          simp [dropCounterEnv]⟩
      · by_cases hy : name = "y"
        · subst hy
          exact ⟨{ ty := .ty .unit, lifetime := dropCounterOuter }, by
            simp [dropCounterEnv]⟩
        · rcases hstore with ⟨slot, hslot⟩
          simp [dropCounterStore, VariableProjection, dropCounterXSlot,
            dropCounterYSlot, hx, hy] at hslot
    · intro henv
      by_cases hx : name = "x"
      · subst hx
        exact ⟨dropCounterXSlot, by
          simp [dropCounterStore, VariableProjection, dropCounterXSlot,
            dropCounterYSlot]⟩
      · by_cases hy : name = "y"
        · subst hy
          exact ⟨dropCounterYSlot, by
            simp [dropCounterStore, VariableProjection, dropCounterXSlot,
              dropCounterYSlot]⟩
        · rcases henv with ⟨envSlot, henvSlot⟩
          simp [dropCounterEnv, Env.empty, hx, hy] at henvSlot
  · intro name envSlot henv
    by_cases hx : name = "x"
    · subst hx
      have henvSlot :
          envSlot = { ty := .box (.ty .unit), lifetime := dropCounterInner } := by
        simpa [dropCounterEnv, Env.update] using henv.symm
      subst henvSlot
      exact ⟨.value (.ref { location := .var "y", owner := true }), by
          simp [dropCounterStore, VariableProjection, dropCounterXSlot,
            dropCounterYSlot],
        ValidPartialValue.box (location := .var "y") (slot := dropCounterYSlot) (by
          simp [dropCounterStore, dropCounterXSlot, dropCounterYSlot])
          ValidPartialValue.unit⟩
    · by_cases hy : name = "y"
      · subst hy
        have henvSlot :
            envSlot = { ty := .ty .unit, lifetime := dropCounterOuter } := by
          simpa [dropCounterEnv, Env.update] using henv.symm
        subst henvSlot
        exact ⟨.value .unit, by
            simp [dropCounterStore, VariableProjection, dropCounterXSlot,
              dropCounterYSlot],
          ValidPartialValue.unit⟩
      · simp [dropCounterEnv, Env.empty, hx, hy] at henv

theorem dropCounter_not_safeAfterDrop :
    ¬ dropCounterStoreAfter ∼ₛ dropCounterEnv.dropLifetime dropCounterInner := by
  intro hsafe
  have henvY :
      (dropCounterEnv.dropLifetime dropCounterInner).slotAt "y" =
        some { ty := .ty .unit, lifetime := dropCounterOuter } := by
    simp [dropCounterEnv, Env.dropLifetime, Env.update, dropCounterInner,
      dropCounterOuter]
  rcases hsafe.2 "y" { ty := .ty .unit, lifetime := dropCounterOuter } henvY with
    ⟨value, hslot, _hvalid⟩
  simp [dropCounterStoreAfter, dropCounterStore, ProgramStore.erase, VariableProjection,
    dropCounterXSlot, dropCounterYSlot] at hslot

theorem dropCounter_not_storeOwnerTargetsHeap :
    ¬ StoreOwnerTargetsHeap dropCounterStore := by
  intro hheap
  have hownsY : ProgramStore.Owns dropCounterStore (.var "y") := by
    exact ⟨.var "x", dropCounterInner, by
      simp [dropCounterStore, dropCounterXSlot, dropCounterYSlot, owningRef]⟩
  rcases hheap (.var "y") hownsY with ⟨address, hheapLocation⟩
  cases hheapLocation

theorem dropCounter_safe_dropLifetime_fails :
    ∃ store store' env lifetime,
      store ∼ₛ env ∧ DropsLifetime store lifetime store' ∧
        ¬ store' ∼ₛ env.dropLifetime lifetime := by
  exact ⟨dropCounterStore, dropCounterStoreAfter, dropCounterEnv, dropCounterInner,
    dropCounter_safeAbstraction, dropCounter_dropsLifetime,
    dropCounter_not_safeAfterDrop⟩

@[simp] theorem Env.dropLifetime_slotAt_eq_some {env : Env} {x : Name}
    {slot : EnvSlot} {lifetime : Lifetime} :
    (env.dropLifetime lifetime).slotAt x = some slot ↔
      env.slotAt x = some slot ∧ slot.lifetime ≠ lifetime := by
  unfold Env.dropLifetime
  cases hslot : env.slotAt x with
  | none =>
      simp [hslot]
  | some candidate =>
      by_cases hlifetime : candidate.lifetime = lifetime
      · constructor
        · intro hdropped
          simp [hslot, hlifetime] at hdropped
        · intro h
          rcases h with ⟨henv, hne⟩
          injection henv with hcandidate
          subst hcandidate
          exact False.elim (hne hlifetime)
      · constructor
        · intro hdropped
          have hcandidate : candidate = slot := by
            simpa [hslot, hlifetime] using hdropped
          exact ⟨by
            simp [hcandidate],
            by simpa [hcandidate] using hlifetime⟩
        · intro h
          rcases h with ⟨henv, hne⟩
          injection henv with hcandidate
          subst hcandidate
          simp [hslot, hlifetime]

/--
Lemma 9.5 shape, safe-abstraction preservation across environment lifetime
drop.

The two premises are the concrete store-side facts that the recursive runtime
drop must provide: variable-domain agreement after the drop, and preservation
of valid abstractions for variables whose allocation lifetime is not dropped.
-/
theorem safeAbstraction_dropLifetime_of_preserved
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
        ValidPartialValue store' value envSlot.ty) →
    store' ∼ₛ env.dropLifetime lifetime := by
  intro hdomain hpreserve
  constructor
  · exact hdomain
  · intro x envSlot henvDropped
    rcases (Env.dropLifetime_slotAt_eq_some.mp henvDropped) with
      ⟨henv, hlifetime⟩
    exact hpreserve x envSlot henv hlifetime

/--
Lemma 9.5, Drop Preservation, lifetime-drop form.

The abstract `ProgramStore` keeps `drop(S, m)` relational.  The two explicit
premises are exactly the store-side effects needed to connect the runtime drop
with Definition 3.20's environment drop.
-/
theorem dropPreservation_lifetime {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
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
        ValidPartialValue store' value envSlot.ty) →
    store' ∼ₛ env.dropLifetime lifetime := by
  intro _hsafe _hdrops hdomain hpreserve
  exact safeAbstraction_dropLifetime_of_preserved hdomain hpreserve

/--
Lemma 9.5, Drop Preservation, lifetime-drop form from a store-slot
characterisation.

`hslotAt` is the concrete store-side analogue of Definition 3.20: a variable
slot remains after `drop(S, m)` exactly when it existed before and its allocation
lifetime was not `m`.
-/
theorem dropPreservation_lifetime_of_slotAt {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    DropsLifetime store lifetime store' →
    (∀ x slot,
      store'.slotAt (VariableProjection x) = some slot ↔
        store.slotAt (VariableProjection x) = some slot ∧ slot.lifetime ≠ lifetime) →
    (∀ x envSlot value,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ lifetime →
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } →
      ValidPartialValue store' value envSlot.ty) →
    store' ∼ₛ env.dropLifetime lifetime := by
  intro hsafe hdrops hslotAt hpreserve
  refine dropPreservation_lifetime hsafe hdrops ?domain ?preserve
  · intro x
    constructor
    · intro hstore'
      rcases hstore' with ⟨slot, hslot'⟩
      rcases (hslotAt x slot).mp hslot' with ⟨hslot, hlifetime⟩
      rcases (hsafe.1 x).mp ⟨slot, hslot⟩ with ⟨envSlot, henv⟩
      have henvLifetime : envSlot.lifetime = slot.lifetime := by
        rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
        rw [hslot] at hsafeSlot
        injection hsafeSlot with hslotEq
        exact (congrArg StoreSlot.lifetime hslotEq).symm
      exact ⟨envSlot, by
        exact Env.dropLifetime_slotAt_eq_some.mpr
          ⟨henv, by simpa [henvLifetime] using hlifetime⟩⟩
    · intro henvDropped
      rcases henvDropped with ⟨envSlot, henvDropped⟩
      rcases Env.dropLifetime_slotAt_eq_some.mp henvDropped with
        ⟨henv, hlifetime⟩
      rcases (hsafe.1 x).mpr ⟨envSlot, henv⟩ with ⟨slot, hslot⟩
      have hslotEq :
          slot.lifetime = envSlot.lifetime := by
        rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
        rw [hslot] at hsafeSlot
        injection hsafeSlot with hslotEq
        exact congrArg StoreSlot.lifetime hslotEq
      exact ⟨slot, (hslotAt x slot).mpr
        ⟨hslot, by simpa [hslotEq] using hlifetime⟩⟩
  · intro x envSlot henv hlifetime
    rcases hsafe.2 x envSlot henv with ⟨value, hslot, _hvalid⟩
    exact ⟨value,
      (hslotAt x { value := value, lifetime := envSlot.lifetime }).mpr
        ⟨hslot, hlifetime⟩,
      hpreserve x envSlot value henv hlifetime hslot⟩

/--
Store-domain half of Lemma 9.5: if a variable slot survives a lifetime drop,
then the corresponding environment variable survives `Γ.dropLifetime`.

The explicit side condition is the store-side fact still needed from the runtime
drop relation: final variable slots are not allocated in the dropped lifetime.
-/
theorem dropLifetime_envDomain_of_storeSurvivor {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} {x : Name} :
    store ∼ₛ env →
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

/--
Store-domain converse for Lemma 9.5: if an environment variable survives
`Γ.dropLifetime`, then the store has the corresponding variable slot after the
runtime drop, assuming non-dropped variable slots are preserved by the drop.
-/
theorem dropLifetime_storeDomain_of_envSurvivor {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} {x : Name} :
    store ∼ₛ env →
    (∀ slot,
      store.slotAt (VariableProjection x) = some slot →
      slot.lifetime ≠ lifetime →
      store'.slotAt (VariableProjection x) = some slot) →
    (∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot) →
    ∃ slot, store'.slotAt (VariableProjection x) = some slot := by
  intro hsafe hpreserve henvDomain
  rcases henvDomain with ⟨envSlot, henvDropped⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp henvDropped with
    ⟨henv, hlifetime⟩
  rcases (hsafe.1 x).mpr ⟨envSlot, henv⟩ with ⟨slot, hslot⟩
  have hslotLifetime : slot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
    rw [hslot] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact congrArg StoreSlot.lifetime hslotEq
  exact ⟨slot, hpreserve slot hslot (by simpa [hslotLifetime] using hlifetime)⟩

theorem dropLifetime_storeDomain_of_envSurvivor_of_ownerTargetsHeap
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime} {x : Name} :
    store ∼ₛ env →
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
  exact ⟨slot, dropsLifetime_preserves_var_slot_of_not_lifetime hdrops hheap hslot
    (by simpa [hslotLifetime] using hlifetime)⟩

/--
Domain component of Lemma 9.5.  This packages the two store-side facts needed
to align runtime lifetime drops with Definition 3.20's environment drop.
-/
theorem dropLifetime_domain_equiv_of_slot_preservation
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    DropsLifetime store lifetime store' →
    (∀ x slot,
      store'.slotAt (VariableProjection x) = some slot →
      slot.lifetime ≠ lifetime) →
    (∀ x slot,
      store.slotAt (VariableProjection x) = some slot →
      slot.lifetime ≠ lifetime →
      store'.slotAt (VariableProjection x) = some slot) →
    ∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot := by
  intro hsafe hdrops hnotDropped hpreserve x
  constructor
  · exact dropLifetime_envDomain_of_storeSurvivor hsafe hdrops (hnotDropped x)
  · exact dropLifetime_storeDomain_of_envSurvivor hsafe (hpreserve x)

theorem dropLifetime_domain_equiv_of_ownerTargetsHeap
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    store ∼ₛ env →
    DropsLifetime store lifetime store' →
    StoreOwnerTargetsHeap store →
    ∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot := by
  intro hsafe hdrops hheap x
  constructor
  · exact dropLifetime_envDomain_of_storeSurvivor hsafe hdrops (by
      intro slot hslot
      exact dropsLifetime_slot_not_dropped hdrops hslot)
  · exact dropLifetime_storeDomain_of_envSurvivor_of_ownerTargetsHeap
      hsafe hdrops hheap

@[simp] theorem validPartialValue_unit (store : ProgramStore) :
    store ⊢ PartialValue.value Value.unit ∼ PartialTy.ty Ty.unit :=
  ValidPartialValue.unit

@[simp] theorem validPartialValue_int (store : ProgramStore) (value : Int) :
    store ⊢ PartialValue.value (Value.int value) ∼ PartialTy.ty Ty.int :=
  ValidPartialValue.int

@[simp] theorem validStoreTyping_empty (store : ProgramStore) :
    ValidStoreTyping store (.val .unit) StoreTyping.empty := by
  intro value hmem
  simp [termValues] at hmem
  subst hmem
  exact ⟨.unit, ValueTyping.unit, ValidPartialValue.unit⟩

@[simp] theorem safeAbstraction_empty :
    ProgramStore.empty ∼ₛ Env.empty := by
  constructor
  · intro x
    constructor
    · intro h
      rcases h with ⟨slot, hslot⟩
      simp [VariableProjection, ProgramStore.empty] at hslot
    · intro h
      rcases h with ⟨slot, hslot⟩
      simp [Env.empty] at hslot
  · intro x envSlot henv
    simp [Env.empty] at henv

theorem safeAbstraction_store_fresh_var {store : ProgramStore} {env : Env}
    {x : Name} :
    store ∼ₛ env →
    env.fresh x →
    store.fresh (VariableProjection x) := by
  intro hsafe hfresh
  unfold ProgramStore.fresh
  cases hslot : store.slotAt (VariableProjection x) with
  | none =>
      rfl
  | some slot =>
      rcases (hsafe.1 x).mp ⟨slot, hslot⟩ with ⟨envSlot, henvSlot⟩
      unfold Env.fresh at hfresh
      rw [hfresh] at henvSlot
      cases henvSlot

theorem safeAbstraction_var_read_nonOwner_of_envShape {store : ProgramStore}
    {env : Env} {x : Name} {envSlot : EnvSlot} {oldSlot : StoreSlot} :
    store ∼ₛ env →
    env.slotAt x = some envSlot →
    store.read (.var x) = some oldSlot →
    (envSlot.ty = .ty .unit ∨ envSlot.ty = .ty .int ∨
      (∃ inner, envSlot.ty = .undef inner) ∨
      ∃ mutable targets, envSlot.ty = .ty (.borrow mutable targets)) →
    PartialValueNonOwner oldSlot.value := by
  intro hsafe henv hread hshape
  rcases hsafe.2 x envSlot henv with ⟨safeValue, hstoreSlot, hvalid⟩
  have hstoreRead :
      store.slotAt (VariableProjection x) =
        some { value := oldSlot.value, lifetime := oldSlot.lifetime } := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  rw [hstoreRead] at hstoreSlot
  injection hstoreSlot with hslotEq
  have hvalueEq : safeValue = oldSlot.value :=
    (congrArg StoreSlot.value hslotEq).symm
  subst hvalueEq
  exact validPartialValue_nonOwner_of_envShape hvalid hshape

/-- Definition 3.23, direct variable write: `write₀(Γ, x, T)` updates only `x`. -/
theorem envWrite_zero_var_eq {env env' : Env} {x : Name} {slot : EnvSlot}
    {ty : Ty} :
    env.slotAt x = some slot →
    EnvWrite 0 env (.var x) ty env' →
    env' = env.update x { slot with ty := .ty ty } := by
  intro hslot hwrite
  cases hwrite with
  | intro hbase hupdate =>
      simp [LVal.base, hslot] at hbase
      subst hbase
      cases hupdate with
      | strong =>
          rfl

/-- Definition 3.3, direct variable write: runtime `write(S, x, v⊥)` updates only `.var x`. -/
theorem write_var_eq {store store' : ProgramStore} {x : Name}
    {oldSlot : StoreSlot} {value : PartialValue} :
    store.slotAt (VariableProjection x) = some oldSlot →
    store.write (.var x) value = some store' →
    store' =
      store.update (VariableProjection x) { oldSlot with value := value } := by
  intro hslot hwrite
  have hslotVar : store.slotAt (.var x) = some oldSlot := by
    simpa [VariableProjection] using hslot
  simp [ProgramStore.write, ProgramStore.loc, hslotVar] at hwrite
  subst hwrite
  rfl

/--
Safe-abstraction preservation for a direct variable type/value update.

This is the base shape needed by the paper's Update Preservation lemma for
`write₀(Γ, x, T)`: the updated variable gets the new value/type, while every
other variable keeps its domain membership and value abstraction.
-/
theorem safeAbstraction_update_var_of_preserved {store' : ProgramStore}
    {env env' : Env} {x : Name} {envSlot : EnvSlot} {value : Value} {ty : Ty} :
    env.slotAt x = some envSlot →
    store'.slotAt (VariableProjection x) =
      some { value := .value value, lifetime := envSlot.lifetime } →
    ValidPartialValue store' (.value value) (.ty ty) →
    env' = env.update x { envSlot with ty := .ty ty } →
    (∀ y,
      y ≠ x →
      ((∃ slot, store'.slotAt (VariableProjection y) = some slot) ↔
        ∃ otherEnvSlot, env.slotAt y = some otherEnvSlot)) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    store' ∼ₛ env' := by
  intro henvX hstoreX hnewValid henv' hdomainOther hpreserveOther
  subst henv'
  constructor
  · intro y
    by_cases hyx : y = x
    · subst hyx
      constructor
      · intro _hstoreDomain
        exact ⟨{ envSlot with ty := .ty ty }, by simp [Env.update]⟩
      · intro _henvDomain
        exact ⟨{ value := .value value, lifetime := envSlot.lifetime }, hstoreX⟩
    · constructor
      · intro hstoreDomain
        rcases (hdomainOther y hyx).mp hstoreDomain with ⟨otherEnvSlot, henv⟩
        exact ⟨otherEnvSlot, by simpa [Env.update, hyx] using henv⟩
      · intro henvDomain
        rcases henvDomain with ⟨otherEnvSlot, henvUpdated⟩
        have henv : env.slotAt y = some otherEnvSlot := by
          simpa [Env.update, hyx] using henvUpdated
        exact (hdomainOther y hyx).mpr ⟨otherEnvSlot, henv⟩
  · intro y updatedSlot henvUpdated
    by_cases hyx : y = x
    · subst hyx
      have hupdatedSlot :
          updatedSlot = { envSlot with ty := .ty ty } := by
        simpa [Env.update] using henvUpdated.symm
      subst hupdatedSlot
      exact ⟨.value value, hstoreX, hnewValid⟩
    · have henv : env.slotAt y = some updatedSlot := by
        simpa [Env.update, hyx] using henvUpdated
      exact hpreserveOther y updatedSlot hyx henv

/--
Variable-base assignment store preservation, factored around the paper's
`write₀` update relation.  The remaining premises are the standard update
preservation obligations for variables other than the assignment target.
-/
theorem storePreservation_assign_var_of_preserved
    {storeAfterDrop store' : ProgramStore} {env env' : Env}
    {x : Name} {runtimeSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    storeAfterDrop.slotAt (VariableProjection x) = some runtimeSlot →
    runtimeSlot.lifetime = envSlot.lifetime →
    storeAfterDrop.write (.var x) (.value value) = some store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y,
      y ≠ x →
      ((∃ slot, store'.slotAt (VariableProjection y) = some slot) ↔
        ∃ otherEnvSlot, env.slotAt y = some otherEnvSlot)) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    store' ∼ₛ env' := by
  intro henvX hwriteEnv hruntimeX hlifetime hwriteStore hnewValid
    hdomainOther hpreserveOther
  have henv' :
      env' = env.update x { envSlot with ty := .ty ty } :=
    envWrite_zero_var_eq henvX hwriteEnv
  have hstore' :
      store' =
        storeAfterDrop.update (VariableProjection x)
          { runtimeSlot with value := .value value } :=
    write_var_eq hruntimeX hwriteStore
  have hstoreX :
      store'.slotAt (VariableProjection x) =
        some { value := .value value, lifetime := envSlot.lifetime } := by
    subst hstore'
    simp [ProgramStore.update, hlifetime]
  exact safeAbstraction_update_var_of_preserved henvX hstoreX hnewValid henv'
    hdomainOther hpreserveOther

/--
Variable-base assignment store preservation when the old lhs value is
non-owning.

The old-value drop is a no-op, so the domain part of safe abstraction follows
from the single runtime write.  The remaining premise is the genuine update
preservation obligation: values abstracting variables other than `x` must remain
valid after overwriting `x`.
-/
theorem storePreservation_assign_var_old_nonOwner_of_preserved
    {store storeAfterDrop store' : ProgramStore} {env env' : Env}
    {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    PartialValueNonOwner oldSlot.value →
    store.read (.var x) = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write (.var x) (.value value) = some store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    store' ∼ₛ env' := by
  intro hsafe henvX hwriteEnv hnonOwner hread hdrops hwrite hnewValid hpreserveOther
  have hdropEq : storeAfterDrop = store :=
    drops_partialValue_nonOwner_eq hnonOwner hdrops
  have hstoreX : store.slotAt (VariableProjection x) = some oldSlot := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  have hstoreXAfterDrop : storeAfterDrop.slotAt (VariableProjection x) = some oldSlot := by
    simpa [hdropEq] using hstoreX
  have hlifetime : oldSlot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henvX with ⟨safeValue, hsafeSlot, _hvalid⟩
    rw [hstoreX] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact congrArg StoreSlot.lifetime hslotEq
  have hstore' :
      store' = storeAfterDrop.update (VariableProjection x)
        { oldSlot with value := .value value } :=
    write_var_eq hstoreXAfterDrop hwrite
  refine storePreservation_assign_var_of_preserved henvX hwriteEnv hstoreXAfterDrop
    hlifetime hwrite hnewValid ?domain hpreserveOther
  intro y hyx
  constructor
  · intro hstoreDomain
    rcases hstoreDomain with ⟨slot, hslot⟩
    have hslotStore : store.slotAt (VariableProjection y) = some slot := by
      rw [hstore'] at hslot
      have hslotAfterDrop :
          storeAfterDrop.slotAt (VariableProjection y) = some slot := by
        simpa [ProgramStore.update, VariableProjection, hyx] using hslot
      simpa [hdropEq] using hslotAfterDrop
    exact (hsafe.1 y).mp ⟨slot, hslotStore⟩
  · intro henvDomain
    rcases (hsafe.1 y).mpr henvDomain with ⟨slot, hslot⟩
    exact ⟨slot, by
      rw [hstore']
      have hslotAfterDrop : storeAfterDrop.slotAt (VariableProjection y) = some slot := by
        simpa [hdropEq] using hslot
      simpa [ProgramStore.update, VariableProjection, hyx] using hslotAfterDrop⟩

/--
Variable-base assignment store preservation when the old lhs environment type is
non-owning-shaped (`unit`, `int`, `undef`, or borrow).

This packages the Section 4.1 argument at the abstraction level: from `S ∼ Γ`,
the environment slot shape, and the lhs read, the old runtime partial value is
known to be non-owning, so its drop leaves the store unchanged.
-/
theorem storePreservation_assign_var_envShape_of_preserved
    {store storeAfterDrop store' : ProgramStore} {env env' : Env}
    {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    (envSlot.ty = .ty .unit ∨ envSlot.ty = .ty .int ∨
      (∃ inner, envSlot.ty = .undef inner) ∨
      ∃ mutable targets, envSlot.ty = .ty (.borrow mutable targets)) →
    store.read (.var x) = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write (.var x) (.value value) = some store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    store' ∼ₛ env' := by
  intro hsafe henvX hwriteEnv hshape hread hdrops hwrite hnewValid hpreserveOther
  have hnonOwner : PartialValueNonOwner oldSlot.value :=
    safeAbstraction_var_read_nonOwner_of_envShape hsafe henvX hread hshape
  exact storePreservation_assign_var_old_nonOwner_of_preserved
    hsafe henvX hwriteEnv hnonOwner hread hdrops hwrite hnewValid hpreserveOther

/-- Updating a fresh location does not change an already-defined lval location. -/
theorem loc_update_of_loc {store : ProgramStore} {updatedLocation : Location}
    {newSlot : StoreSlot} {lv : LVal} {location : Location} :
    store.fresh updatedLocation →
    store.loc lv = some location →
    (store.update updatedLocation newSlot).loc lv = some location := by
  intro hfresh hloc
  induction lv generalizing location with
  | var y =>
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      cases hsource : store.loc lv with
      | none =>
          simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          cases hsourceSlot : store.slotAt source with
          | none =>
              simp [ProgramStore.loc, hsource, hsourceSlot] at hloc
          | some sourceSlot =>
              cases hsourceValue : sourceSlot.value with
              | undef =>
                  simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
              | value sourceValue =>
                  cases sourceValue with
                  | unit =>
                      simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                  | int n =>
                      simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                  | ref ref =>
                    simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                    have hupdatedSource :
                        (store.update updatedLocation newSlot).loc lv = some source :=
                      ih hsource
                    have hsourceNe : source ≠ updatedLocation := by
                      intro hsame
                      subst hsame
                      simp [ProgramStore.fresh] at hfresh
                      rw [hfresh] at hsourceSlot
                      contradiction
                    have hslot :
                        (store.update updatedLocation newSlot).slotAt source =
                          some sourceSlot := by
                      simpa [ProgramStore.update, hsourceNe] using hsourceSlot
                    simp [ProgramStore.loc, hupdatedSource, hslot, hsourceValue, hloc]

/-- Updating a fresh location preserves an existing slot lookup. -/
theorem slotAt_update_of_slotAt {store : ProgramStore} {updatedLocation location : Location}
    {newSlot slot : StoreSlot} :
    store.fresh updatedLocation →
    store.slotAt location = some slot →
    (store.update updatedLocation newSlot).slotAt location = some slot := by
  intro hfresh hslot
  have hlocationNe : location ≠ updatedLocation := by
    intro hsame
    subst hsame
    simp [ProgramStore.fresh] at hfresh
    rw [hfresh] at hslot
    contradiction
  simpa [ProgramStore.update, hlocationNe] using hslot

/-- Updating a fresh location preserves existing partial-value abstractions. -/
theorem validPartialValue_update_of_fresh {store : ProgramStore}
    {updatedLocation : Location} {newSlot : StoreSlot}
    {partialValue : PartialValue} {ty : PartialTy} :
    store.fresh updatedLocation →
    ValidPartialValue store partialValue ty →
    ValidPartialValue (store.update updatedLocation newSlot) partialValue ty := by
  intro hfresh hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValue.unit
  | int =>
      exact ValidPartialValue.int
  | undef =>
      exact ValidPartialValue.undef
  | borrow hmem hloc =>
      exact ValidPartialValue.borrow hmem (loc_update_of_loc hfresh hloc)
  | box hslot _hinner ih =>
      exact ValidPartialValue.box (slotAt_update_of_slotAt hfresh hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValue.boxFull (slotAt_update_of_slotAt hfresh hslot) ih

/-- Declaring a fresh variable does not change an already-defined lval location. -/
theorem loc_declare_of_loc {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {value : Value} {lv : LVal} {location : Location} :
    store.fresh (.var x) →
    store.loc lv = some location →
    (store.declare x lifetime value).loc lv = some location := by
  intro hfresh hloc
  induction lv generalizing location with
  | var y =>
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      cases hsource : store.loc lv with
      | none =>
          simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          cases hsourceSlot : store.slotAt source with
          | none =>
              simp [ProgramStore.loc, hsource, hsourceSlot] at hloc
          | some sourceSlot =>
              cases hsourceValue : sourceSlot.value with
              | undef =>
                  simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
              | value sourceValue =>
                  cases sourceValue with
                  | unit =>
                      simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                  | int n =>
                      simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                  | ref ref =>
                    simp [ProgramStore.loc, hsource, hsourceSlot, hsourceValue] at hloc
                    have hdeclaredSource :
                        (store.declare x lifetime value).loc lv = some source :=
                      ih hsource
                    have hsourceNe : source ≠ .var x := by
                      intro hsame
                      subst hsame
                      simp [ProgramStore.fresh] at hfresh
                      rw [hfresh] at hsourceSlot
                      contradiction
                    have hslot :
                        (store.declare x lifetime value).slotAt source = some sourceSlot := by
                      simpa [ProgramStore.declare, ProgramStore.update, hsourceNe]
                        using hsourceSlot
                    simp [ProgramStore.loc, hdeclaredSource, hslot, hsourceValue, hloc]

/-- Declaring a fresh variable preserves an existing slot lookup away from it. -/
theorem slotAt_declare_of_slotAt {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {value : Value} {location : Location} {slot : StoreSlot} :
    store.fresh (.var x) →
    store.slotAt location = some slot →
    (store.declare x lifetime value).slotAt location = some slot := by
  intro hfresh hslot
  have hlocationNe : location ≠ .var x := by
    intro hsame
    subst hsame
    simp [ProgramStore.fresh] at hfresh
    rw [hfresh] at hslot
    contradiction
  simpa [ProgramStore.declare, ProgramStore.update, hlocationNe] using hslot

/-- Declaring a fresh variable preserves existing partial-value abstractions. -/
theorem validPartialValue_declare {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {newValue : Value} {partialValue : PartialValue}
    {ty : PartialTy} :
    store.fresh (.var x) →
    ValidPartialValue store partialValue ty →
    ValidPartialValue (store.declare x lifetime newValue) partialValue ty := by
  intro hfresh hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValue.unit
  | int =>
      exact ValidPartialValue.int
  | undef =>
      exact ValidPartialValue.undef
  | borrow hmem hloc =>
      exact ValidPartialValue.borrow hmem (loc_declare_of_loc hfresh hloc)
  | box hslot _hinner ih =>
      exact ValidPartialValue.box (slotAt_declare_of_slotAt hfresh hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValue.boxFull (slotAt_declare_of_slotAt hfresh hslot) ih

/--
Lemma 9.10 support, `R-Declare` safe-abstraction preservation.

The explicit `hpreserveOld` premise is the store-extension obligation for values
already represented by `Γ`; it is discharged by later store-monotonicity lemmas.
-/
theorem safeAbstraction_declare {store : ProgramStore} {env : Env}
    {x : Name} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    store ∼ₛ env →
    env.fresh x →
    ValidPartialValue (store.declare x lifetime value) (.value value) (.ty ty) →
    (∀ y envSlot oldValue,
      y ≠ x →
      env.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ValidPartialValue (store.declare x lifetime value) oldValue envSlot.ty) →
    store.declare x lifetime value ∼ₛ
      env.update x { ty := .ty ty, lifetime := lifetime } := by
  intro hsafe hfresh hnewValid hpreserveOld
  constructor
  · intro y
    constructor
    · intro hstoreDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ ty := .ty ty, lifetime := lifetime }, by simp [Env.update]⟩
      · rcases hstoreDomain with ⟨slot, hslot⟩
        have holdStore : ∃ slot, store.slotAt (VariableProjection y) = some slot := by
          rcases slot with ⟨slotValue, slotLifetime⟩
          exact ⟨{ value := slotValue, lifetime := slotLifetime }, by
            simpa [ProgramStore.declare, ProgramStore.update, VariableProjection, hyx]
              using hslot⟩
        rcases (hsafe.1 y).mp holdStore with ⟨envSlot, henvSlot⟩
        exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
    · intro henvDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ value := .value value, lifetime := lifetime }, by
          simp [ProgramStore.declare, ProgramStore.update, VariableProjection]⟩
      · rcases henvDomain with ⟨envSlot, henvSlot⟩
        have holdEnv : ∃ envSlot, env.slotAt y = some envSlot := by
          exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
        rcases (hsafe.1 y).mpr holdEnv with ⟨storeSlot, hstoreSlot⟩
        exact ⟨storeSlot, by
          simpa [ProgramStore.declare, ProgramStore.update, VariableProjection, hyx]
            using hstoreSlot⟩
  · intro y envSlot henv
    by_cases hyx : y = x
    · subst hyx
      have henvSlot :
          envSlot = { ty := .ty ty, lifetime := lifetime } := by
        simpa [Env.update] using henv.symm
      subst henvSlot
      exact ⟨.value value, by
          simp [ProgramStore.declare, ProgramStore.update, VariableProjection],
        hnewValid⟩
    · have holdEnv : env.slotAt y = some envSlot := by
        simpa [Env.update, hyx] using henv
      rcases hsafe.2 y envSlot holdEnv with ⟨oldValue, hstoreSlot, _holdValid⟩
      exact ⟨oldValue, by
          simpa [ProgramStore.declare, ProgramStore.update, VariableProjection, hyx]
            using hstoreSlot,
        hpreserveOld y envSlot oldValue hyx holdEnv hstoreSlot⟩

/--
Lemma 9.10 support, variable `R-Move` safe-abstraction preservation.

This is the `π = ε` base case of the paper's `move(Γ, w)` / write-`undef`
correspondence.  The `hpreserveOld` premise packages the separate no-borrow /
path-stability obligation for variables other than `x`.
-/
theorem safeAbstraction_move_var {store : ProgramStore} {env : Env}
    {x : Name} {slot : EnvSlot} {ty : Ty} {oldValue : PartialValue} :
    store ∼ₛ env →
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    store.slotAt (VariableProjection x) =
      some { value := oldValue, lifetime := slot.lifetime } →
    (∀ y envSlot value,
      y ≠ x →
      env.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := value, lifetime := envSlot.lifetime } →
      ValidPartialValue
        (store.update (VariableProjection x)
          { value := .undef, lifetime := slot.lifetime })
        value envSlot.ty) →
    store.update (VariableProjection x) { value := .undef, lifetime := slot.lifetime } ∼ₛ
      env.update x { slot with ty := .undef ty } := by
  intro hsafe henv hty hstoreSlot hpreserveOld
  constructor
  · intro y
    constructor
    · intro hstoreDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ slot with ty := .undef ty }, by simp [Env.update]⟩
      · rcases hstoreDomain with ⟨runtimeSlot, hruntimeSlot⟩
        have holdStore : ∃ oldSlot, store.slotAt (VariableProjection y) = some oldSlot := by
          rcases runtimeSlot with ⟨slotValue, slotLifetime⟩
          exact ⟨{ value := slotValue, lifetime := slotLifetime }, by
            simpa [ProgramStore.update, VariableProjection, hyx] using hruntimeSlot⟩
        rcases (hsafe.1 y).mp holdStore with ⟨envSlot, henvSlot⟩
        exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
    · intro henvDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ value := .undef, lifetime := slot.lifetime }, by
          simp [ProgramStore.update, VariableProjection]⟩
      · rcases henvDomain with ⟨envSlot, henvSlot⟩
        have holdEnv : ∃ envSlot, env.slotAt y = some envSlot := by
          exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
        rcases (hsafe.1 y).mpr holdEnv with ⟨runtimeSlot, hruntimeSlot⟩
        exact ⟨runtimeSlot, by
          simpa [ProgramStore.update, VariableProjection, hyx] using hruntimeSlot⟩
  · intro y envSlot henvUpdated
    by_cases hyx : y = x
    · subst hyx
      have henvSlot :
          envSlot = { slot with ty := .undef ty } := by
        simpa [Env.update] using henvUpdated.symm
      subst henvSlot
      exact ⟨.undef, by
          simp [ProgramStore.update, VariableProjection],
        by
          simpa [hty] using (ValidPartialValue.undef (ty := ty))⟩
    · have holdEnv : env.slotAt y = some envSlot := by
        simpa [Env.update, hyx] using henvUpdated
      rcases hsafe.2 y envSlot holdEnv with ⟨value, hstore, _hvalid⟩
      exact ⟨value, by
          simpa [ProgramStore.update, VariableProjection, hyx] using hstore,
        hpreserveOld y envSlot value hyx holdEnv hstore⟩

/-- Lemma 9.10, variable `R-Move` store-preservation fragment. -/
theorem storePreservation_move_var_step {store store' : ProgramStore}
    {env₁ env₂ : Env} {lifetime valueLifetime : Lifetime}
    {x : Name} {value : Value} {ty : Ty} :
    store ∼ₛ env₁ →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    Step store lifetime (.move (.var x)) store' (.val value) →
    (∀ y envSlot oldValue,
      y ≠ x →
      env₁.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ValidPartialValue store' oldValue envSlot.ty) →
    store' ∼ₛ env₂ := by
  intro hsafe henvSlot hmove hstep hpreserveOld
  cases hstep with
  | move _hread hwrite =>
      rcases hsafe.2 x _ henvSlot with
        ⟨oldValue, hstoreSlot, _hvalidOld⟩
      have hstore' :
          store' =
            store.update (VariableProjection x)
              { value := .undef, lifetime := valueLifetime } := by
        have hstoreSlotVar :
            store.slotAt (.var x) =
              some { value := oldValue, lifetime := valueLifetime } := by
          simpa [VariableProjection] using hstoreSlot
        simp [ProgramStore.write, ProgramStore.loc, hstoreSlotVar] at hwrite
        exact hwrite.symm
      rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv₂⟩
      have hmoveSlotEq :
          moveSlot = { ty := .ty ty, lifetime := valueLifetime } := by
        simp [LVal.base] at hmoveSlot
        rw [henvSlot] at hmoveSlot
        injection hmoveSlot with hmoveSlotEq
        exact hmoveSlotEq.symm
      subst hmoveSlotEq
      cases struck with
      | ty struckTy =>
          simp [Strike, LVal.path] at hstrike
      | box struckInner =>
          simp [Strike, LVal.path] at hstrike
      | undef struckTy =>
          simp [Strike, LVal.path] at hstrike
          subst hstrike
          subst henv₂
          subst hstore'
          exact safeAbstraction_move_var hsafe henvSlot rfl hstoreSlot
            (by
              intro y envSlot oldOtherValue hyx henv hslot
              exact hpreserveOld y envSlot oldOtherValue hyx henv hslot)

/-- Lemma 9.10, `R-Declare` store-preservation fragment. -/
theorem storePreservation_declare_step {store store' : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {value : Value} :
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.letMut x (.val value)) .unit env₃ →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    (∀ ty,
      ValueTyping typing value ty →
      ValidPartialValue (store.declare x lifetime value) (.value value) (.ty ty)) →
    (∀ y envSlot oldValue,
      y ≠ x →
      env₁.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ValidPartialValue (store.declare x lifetime value) oldValue envSlot.ty) →
    store' ∼ₛ env₃ := by
  intro hsafe htyping hstep hnewValid hpreserveOld
  cases htyping with
  | declare hfresh hinit _hfreshOut _hcoh henv₃ =>
      cases hstep with
      | declare hstore' =>
          cases hinit with
          | const hvalueTyping =>
              subst hstore'
              subst henv₃
              exact safeAbstraction_declare hsafe hfresh
                (hnewValid _ hvalueTyping)
                hpreserveOld

/--
Lemma 9.10, `R-Declare` store preservation, with the store-extension
obligations discharged from the existing validity hypotheses.
-/
theorem storePreservation_declare_step_valid {store store' : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {value : Value} :
    ValidStoreTyping store (.letMut x (.val value)) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.letMut x (.val value)) .unit env₃ →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    store' ∼ₛ env₃ := by
  intro hvalidStoreTyping hsafe htyping hstep
  cases htyping with
  | declare hfresh hinit hfreshOut hcoh henv₃ =>
      have hfreshStore : store.fresh (VariableProjection x) :=
        safeAbstraction_store_fresh_var hsafe hfresh
      refine storePreservation_declare_step hsafe
        (TermTyping.declare hfresh hinit hfreshOut hcoh henv₃) hstep ?newValid ?preserveOld
      · intro ty hvalueTyping
        rcases hvalidStoreTyping value (by simp [termValues]) with
          ⟨storedTy, hstoredTyping, hvalidValue⟩
        have hty : storedTy = ty := by
          cases hstoredTyping <;> cases hvalueTyping
          · rfl
          · rfl
          · rename_i hstoredLookup hvalueLookup
            rw [hstoredLookup] at hvalueLookup
            injection hvalueLookup
        subst hty
        exact validPartialValue_declare hfreshStore hvalidValue
      · intro y envSlot oldValue _hyx henv hstoreSlot
        rcases hsafe.2 y envSlot henv with
          ⟨safeValue, hsafeSlot, hsafeValid⟩
        rw [hstoreSlot] at hsafeSlot
        injection hsafeSlot with hslotEq
        cases hslotEq
        exact validPartialValue_declare hfreshStore hsafeValid

/-- Box allocation preserves existing partial-value abstractions. -/
theorem validPartialValue_boxAt {store : ProgramStore} {address : Nat}
    {newValue : Value} {partialValue : PartialValue} {ty : PartialTy} :
    store.fresh (.heap address) →
    ValidPartialValue store partialValue ty →
    ValidPartialValue (store.boxAt address newValue).1 partialValue ty := by
  intro hfresh hvalid
  exact validPartialValue_update_of_fresh
    (updatedLocation := .heap address)
    (newSlot := { value := .value newValue, lifetime := Lifetime.root })
    hfresh hvalid

/-- The owning reference returned by `boxAt` safely abstracts `Box<T>`. -/
theorem validValue_boxAt_ref {store : ProgramStore} {address : Nat}
    {value : Value} {ty : Ty} :
    store.fresh (.heap address) →
    ValidValue store value ty →
    ValidValue (store.boxAt address value).1 (Value.ref (store.boxAt address value).2)
      (.box ty) := by
  intro hfresh hvalidValue
  exact ValidPartialValue.boxFull
    (location := .heap address)
    (slot := { value := .value value, lifetime := Lifetime.root })
    (by simp [ProgramStore.boxAt])
    (validPartialValue_update_of_fresh
      (updatedLocation := .heap address)
      (newSlot := { value := .value value, lifetime := Lifetime.root })
      hfresh (show ValidPartialValue store (.value value) (.ty ty) from hvalidValue))

/-- Lemma 9.10 support: heap allocation preserves safe abstraction of variables. -/
theorem safeAbstraction_boxAt {store : ProgramStore} {env : Env}
    {address : Nat} {value : Value} :
    store.fresh (.heap address) →
    store ∼ₛ env →
    (store.boxAt address value).1 ∼ₛ env := by
  intro hfresh hsafe
  constructor
  · intro x
    constructor
    · intro hdomain
      rcases hdomain with ⟨slot, hslot⟩
      have holdDomain : ∃ oldSlot, store.slotAt (VariableProjection x) = some oldSlot := by
        rcases slot with ⟨slotValue, slotLifetime⟩
        exact ⟨{ value := slotValue, lifetime := slotLifetime }, by
          simpa [ProgramStore.boxAt, ProgramStore.update, VariableProjection]
            using hslot⟩
      exact (hsafe.1 x).mp holdDomain
    · intro hdomain
      rcases (hsafe.1 x).mpr hdomain with ⟨slot, hslot⟩
      exact ⟨slot, by
        simpa [ProgramStore.boxAt, ProgramStore.update, VariableProjection]
          using hslot⟩
  · intro x envSlot henv
    rcases hsafe.2 x envSlot henv with ⟨oldValue, hslot, hvalid⟩
    exact ⟨oldValue, by
        simpa [ProgramStore.boxAt, ProgramStore.update, VariableProjection]
          using hslot,
      validPartialValue_boxAt hfresh hvalid⟩

/--
Lemma 9.10, `R-Box` store-preservation fragment, factored around the
operand-value abstraction established by the inner preservation proof.
-/
theorem storePreservation_box_step_of_validValue {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {ref : Reference} :
    store ∼ₛ env₁ →
    ValidValue store value ty →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    store' ∼ₛ env₂ ∧ ValidValue store' (.ref ref) (.box ty) := by
  intro hsafe hvalidValue htyping hstep
  cases htyping with
  | box hinner =>
      cases hinner with
      | const _hvalueTyping =>
          cases hstep with
          | box hfresh hbox =>
              cases hbox
              exact ⟨safeAbstraction_boxAt hfresh hsafe,
                validValue_boxAt_ref hfresh hvalidValue⟩

/-- Lemma 9.10, `R-Box` store-preservation fragment. -/
theorem storePreservation_box_step {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {ref : Reference} :
    ValidStoreTyping store (.box (.val value)) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    store' ∼ₛ env₂ ∧ ValidValue store' (.ref ref) (.box ty) := by
  intro hvalidStoreTyping hsafe htyping hstep
  cases htyping with
  | box hinner =>
      cases hinner with
      | const hvalueTyping =>
          rcases hvalidStoreTyping value (by simp [termValues]) with
            ⟨storedTy, hstoredTyping, hvalidValue⟩
          have hty : storedTy = ty := by
            cases hstoredTyping <;> cases hvalueTyping
            · rfl
            · rfl
            · rename_i hstoredLookup hvalueLookup
              rw [hstoredLookup] at hvalueLookup
              injection hvalueLookup
          subst hty
          exact storePreservation_box_step_of_validValue hsafe hvalidValue
            (TermTyping.box (typing := typing) (TermTyping.const hvalueTyping))
            hstep

/-- Lemma 9.9, `R-Box` one-step value preservation fragment. -/
theorem valuePreservation_box_step {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {ref : Reference} :
    ValidStoreTyping store (.box (.val value)) typing →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    Step store lifetime (.box (.val value)) store' (.val (.ref ref)) →
    ValidValue store' (.ref ref) (.box ty) := by
  intro hvalidStoreTyping hsafe htyping hstep
  exact (storePreservation_box_step hvalidStoreTyping hsafe htyping hstep).2


end Paper
end LwRust
