import FWRust.Paper.Soundness.Helpers.Validity

/-!
# Soundness helpers: FullSafeAbstraction

Section 4.2: safe abstractions and variable projection.
-/

namespace FWRust
namespace Paper

open Core

/-! ## Section 4.2: Safe Abstractions -/

/--
Internal owner-shape projection of value validity.  It forgets only whether a
borrowed reference resolves to its annotated target; unlike the paper-facing
relation below, it is used solely for ownership and allocation arguments.
-/
inductive ValidPartialValueSkeleton : ProgramStore → PartialValue → PartialTy → Prop where
  | unit {store : ProgramStore} :
      ValidPartialValueSkeleton store (.value .unit) (.ty .unit)
  | int {store : ProgramStore} {value : Int} :
      ValidPartialValueSkeleton store (.value (.int value)) (.ty .int)
  | undef {store : ProgramStore} {ty : Ty} :
      ValidPartialValueSkeleton store .undef (.undef ty)
  | borrow {store : ProgramStore} {location : Location} {mutable : Bool}
      {target : LVal} :
      ValidPartialValueSkeleton store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable target))
  | box {store : ProgramStore} {location : Location} {slot : StoreSlot}
      {inner : PartialTy} :
      store.slotAt location = some slot →
      ValidPartialValueSkeleton store slot.value inner →
      ValidPartialValueSkeleton store
        (.value (.ref { location := location, owner := true }))
        (.box inner)
  | boxFull {store : ProgramStore} {location : Location} {slot : StoreSlot}
      {ty : Ty} :
      store.slotAt location = some slot →
      ValidPartialValueSkeleton store slot.value (.ty ty) →
      ValidPartialValueSkeleton store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty))

/-- Definition 4.4, valid type/value abstraction `S ⊢ v⊥ ∼ T̃`. -/
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
      {target : LVal} :
      store.loc target = some location →
      ValidPartialValue store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable target))
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

/-! A moved-out type is represented by runtime `undef`, exactly as in V-Undef. -/

@[simp] theorem validPartialValue_undef_iff {store : ProgramStore}
    {value : PartialValue} {ty : Ty} :
    ValidPartialValue store value (.undef ty) ↔ value = .undef := by
  constructor
  · intro hvalid
    cases hvalid with
    | undef => rfl
  · rintro rfl
    exact ValidPartialValue.undef

def ValidValue (store : ProgramStore) (value : Value) (ty : Ty) : Prop :=
  ValidPartialValue store (.value value) (.ty ty)

notation:50 store:51 " ⊢ " value:51 " ∼ " ty:51 =>
  ValidPartialValue store value ty

/--
Runtime value validity for environments that may contain stale loan
annotations.

For initialized borrow targets this is the ordinary `ValidPartialValue`
obligation: the reference must resolve through the static target.  If the target
is not initialized, the borrow annotation is only a protection token; runtime
validity records the value shape but does not require target resolution that
typing cannot use.
-/
def TargetInitialized (env : Env) (target : LVal) : Prop :=
  ∃ targetTy targetLifetime,
    LValTyping env target (.ty targetTy) targetLifetime

inductive ValidPartialValueWhenInitialized (env : Env) (store : ProgramStore) :
    PartialValue → PartialTy → Prop where
  | unit :
      ValidPartialValueWhenInitialized env store (.value .unit) (.ty .unit)
  | int {value : Int} :
      ValidPartialValueWhenInitialized env store (.value (.int value)) (.ty .int)
  | undef {ty : Ty} :
      ValidPartialValueWhenInitialized env store .undef (.undef ty)
  | borrowLive {location : Location} {mutable : Bool} {target : LVal} :
      TargetInitialized env target →
      store.loc target = some location →
      ValidPartialValueWhenInitialized env store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable target))
  | borrowStale {location : Location} {mutable : Bool} {target : LVal} :
      ¬ TargetInitialized env target →
      ValidPartialValueWhenInitialized env store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable target))
  | box {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      ValidPartialValueWhenInitialized env store slot.value inner →
      ValidPartialValueWhenInitialized env store
        (.value (.ref { location := location, owner := true }))
        (.box inner)
  | boxFull {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      ValidPartialValueWhenInitialized env store slot.value (.ty ty) →
      ValidPartialValueWhenInitialized env store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty))

theorem ValidPartialValue.whenInitialized {env : Env} {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValue store value ty →
    ValidPartialValueWhenInitialized env store value ty := by
  intro hvalid
  induction hvalid with
  | unit => exact ValidPartialValueWhenInitialized.unit
  | int => exact ValidPartialValueWhenInitialized.int
  | undef => exact ValidPartialValueWhenInitialized.undef
  | @borrow location mutable target hloc =>
      by_cases hinitialized : TargetInitialized env target
      · exact ValidPartialValueWhenInitialized.borrowLive
          hinitialized hloc
      · exact ValidPartialValueWhenInitialized.borrowStale
          (location := location) (mutable := mutable) (target := target)
          hinitialized
  | box hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.box hslot ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.boxFull hslot ih

theorem ValidPartialValueWhenInitialized.toFull_of_borrowsWellFormed
    {env : Env} {store : ProgramStore} {value : PartialValue}
    {partialTy : PartialTy} :
    ValidPartialValueWhenInitialized env store value partialTy →
    ∀ {slotLifetime : Lifetime},
      PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
      ValidPartialValue store value partialTy := by
  intro hvalid
  induction hvalid with
  | unit =>
      intro _slotLifetime _hwell
      exact ValidPartialValue.unit
  | int =>
      intro _slotLifetime _hwell
      exact ValidPartialValue.int
  | undef =>
      intro _slotLifetime _hwell
      exact ValidPartialValue.undef
  | @borrowLive location mutable target hinitialized hloc =>
      intro _slotLifetime _hwell
      exact ValidPartialValue.borrow hloc
  | @borrowStale location mutable target hstale =>
      intro slotLifetime hwell
      have hinitialized : TargetInitialized env target := by
        rcases hwell (mutable := mutable) (target := target)
            PartialTyContains.here with
          ⟨targetTy, targetLifetime, htyping, _hle, _hbase⟩
        exact ⟨targetTy, targetLifetime, htyping⟩
      exact False.elim (hstale hinitialized)
  | @box location slot inner hslot _hinner ih =>
      intro slotLifetime hwell
      exact ValidPartialValue.box hslot
        (ih (slotLifetime := slotLifetime)
          (by
            intro mutable target hcontains
            exact hwell (PartialTyContains.box hcontains)))
  | @boxFull location slot ty hslot _hinner ih =>
      intro slotLifetime hwell
      exact ValidPartialValue.boxFull hslot
        (ih (slotLifetime := slotLifetime)
          (by
            intro mutable target hcontains
            exact hwell (PartialTyContains.tyBox hcontains)))

theorem ValidPartialValueWhenInitialized.skeleton {env : Env}
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy} :
    ValidPartialValueWhenInitialized env store value ty →
    ValidPartialValueSkeleton store value ty := by
  intro hvalid
  induction hvalid with
  | unit => exact ValidPartialValueSkeleton.unit
  | int => exact ValidPartialValueSkeleton.int
  | undef => exact ValidPartialValueSkeleton.undef
  | borrowLive _hinitialized _hloc =>
      exact ValidPartialValueSkeleton.borrow
  | borrowStale _hstale =>
      exact ValidPartialValueSkeleton.borrow
  | box hslot _hinner ih =>
      exact ValidPartialValueSkeleton.box hslot ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueSkeleton.boxFull hslot ih

theorem ValidPartialValue.skeleton {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValue store value ty →
    ValidPartialValueSkeleton store value ty := by
  intro hvalid
  induction hvalid with
  | unit => exact ValidPartialValueSkeleton.unit
  | int => exact ValidPartialValueSkeleton.int
  | undef => exact ValidPartialValueSkeleton.undef
  | borrow =>
      exact ValidPartialValueSkeleton.borrow
  | box hslot _hinner ih =>
      exact ValidPartialValueSkeleton.box hslot ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueSkeleton.boxFull hslot ih

/--
Local ownership acyclicity for a valid stored value.

If a slot contains a valid value and that value owns `owned`, then following
ownership edges from `owned` can never lead back to the slot's storage location.
This is the finite-derivation version of the paper's assignment-progress cycle
argument.
-/
theorem ValidPartialValueSkeleton.no_owned_path_to_storage {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValueSkeleton store value ty →
    ∀ {storage : Location} {slot : StoreSlot} {owned : Location},
      store.slotAt storage = some slot →
      slot.value = value →
      owned ∈ partialValueOwningLocations value →
      ¬ ProgramStore.OwnsTransitively store owned storage := by
  intro hvalid
  induction hvalid with
  | unit =>
      intro storage slot owned _hslot _hvalue hmem hpath
      simp [partialValueOwningLocations, valueOwningLocations,
        valueOwnedLocation?] at hmem
  | int =>
      intro storage slot owned _hslot _hvalue hmem hpath
      simp [partialValueOwningLocations, valueOwningLocations,
        valueOwnedLocation?] at hmem
  | undef =>
      intro storage slot owned _hslot _hvalue hmem hpath
      simp [partialValueOwningLocations] at hmem
  | borrow =>
      intro storage slot owned _hslot _hvalue hmem hpath
      simp [partialValueOwningLocations, valueOwningLocations,
        valueOwnedLocation?] at hmem
  | @box ownerLocation ownerSlot inner hownedSlot _hinner ih =>
      intro storage slot owned hslot hvalue hmem hpath
      have hownedEq : owned = ownerLocation := by
        simpa [partialValueOwningLocations, valueOwningLocations,
          valueOwnedLocation?] using hmem
      subst owned
      have hparentOwns :
          ProgramStore.OwnsAt store ownerLocation storage := by
        refine ⟨slot.lifetime, ?_⟩
        cases slot with
        | mk slotValue slotLifetime =>
            cases hvalue
            simpa [owningRef] using hslot
      cases hpath with
      | direct hback =>
          rcases hback with ⟨backLifetime, hbackSlot⟩
          have hownerSlotValue :
              ownerSlot.value = .value (owningRef storage) := by
            have hslotEq :
                ownerSlot =
                  { value := .value (owningRef storage),
                    lifetime := backLifetime } :=
              Option.some.inj (hownedSlot.symm.trans hbackSlot)
            exact congrArg StoreSlot.value hslotEq
          have hstorageMem :
              storage ∈ partialValueOwningLocations ownerSlot.value :=
            mem_partialValueOwningLocations_of_eq_owningRef hownerSlotValue
          exact ih hownedSlot rfl hstorageMem
            (ProgramStore.OwnsTransitively.direct hparentOwns)
      | trans hfirst htail =>
          rename_i middle
          rcases hfirst with ⟨firstLifetime, hfirstSlot⟩
          have hownerSlotValue :
              ownerSlot.value = .value (owningRef middle) := by
            have hslotEq :
                ownerSlot =
                  { value := .value (owningRef middle),
                    lifetime := firstLifetime } :=
              Option.some.inj (hownedSlot.symm.trans hfirstSlot)
            exact congrArg StoreSlot.value hslotEq
          have hmiddleMem :
              middle ∈ partialValueOwningLocations ownerSlot.value :=
            mem_partialValueOwningLocations_of_eq_owningRef hownerSlotValue
          exact ih hownedSlot rfl hmiddleMem
            (ProgramStore.OwnsTransitively.trans_right htail hparentOwns)
  | @boxFull ownerLocation ownerSlot innerTy hownedSlot _hinner ih =>
      intro storage slot owned hslot hvalue hmem hpath
      have hownedEq : owned = ownerLocation := by
        simpa [partialValueOwningLocations, valueOwningLocations,
          valueOwnedLocation?] using hmem
      subst owned
      have hparentOwns :
          ProgramStore.OwnsAt store ownerLocation storage := by
        refine ⟨slot.lifetime, ?_⟩
        cases slot with
        | mk slotValue slotLifetime =>
            cases hvalue
            simpa [owningRef] using hslot
      cases hpath with
      | direct hback =>
          rcases hback with ⟨backLifetime, hbackSlot⟩
          have hownerSlotValue :
              ownerSlot.value = .value (owningRef storage) := by
            have hslotEq :
                ownerSlot =
                  { value := .value (owningRef storage),
                    lifetime := backLifetime } :=
              Option.some.inj (hownedSlot.symm.trans hbackSlot)
            exact congrArg StoreSlot.value hslotEq
          have hstorageMem :
              storage ∈ partialValueOwningLocations ownerSlot.value :=
            mem_partialValueOwningLocations_of_eq_owningRef hownerSlotValue
          exact ih hownedSlot rfl hstorageMem
            (ProgramStore.OwnsTransitively.direct hparentOwns)
      | trans hfirst htail =>
          rename_i middle
          rcases hfirst with ⟨firstLifetime, hfirstSlot⟩
          have hownerSlotValue :
              ownerSlot.value = .value (owningRef middle) := by
            have hslotEq :
                ownerSlot =
                  { value := .value (owningRef middle),
                    lifetime := firstLifetime } :=
              Option.some.inj (hownedSlot.symm.trans hfirstSlot)
            exact congrArg StoreSlot.value hslotEq
          have hmiddleMem :
              middle ∈ partialValueOwningLocations ownerSlot.value :=
            mem_partialValueOwningLocations_of_eq_owningRef hownerSlotValue
          exact ih hownedSlot rfl hmiddleMem
            (ProgramStore.OwnsTransitively.trans_right htail hparentOwns)

/--
Local ownership acyclicity for a valid stored value.

If a slot contains a valid value and that value owns `owned`, then following
ownership edges from `owned` can never lead back to the slot's storage location.
This is the finite-derivation version of the paper's assignment-progress cycle
argument.
-/
theorem ValidPartialValue.no_owned_path_to_storage {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValue store value ty →
    ∀ {storage : Location} {slot : StoreSlot} {owned : Location},
      store.slotAt storage = some slot →
      slot.value = value →
      owned ∈ partialValueOwningLocations value →
      ¬ ProgramStore.OwnsTransitively store owned storage := by
  intro hvalid
  exact ValidPartialValueSkeleton.no_owned_path_to_storage hvalid.skeleton

/-- A valid stored value cannot make its own storage part of an ownership cycle. -/
theorem ValidPartialValue.no_storage_ownership_cycle {store : ProgramStore}
    {storage : Location} {slot : StoreSlot} {ty : PartialTy} :
    store.slotAt storage = some slot →
    ValidPartialValue store slot.value ty →
    ¬ ProgramStore.OwnsTransitively store storage storage := by
  intro hslot hvalid hpath
  cases hpath with
  | direct howns =>
      rcases howns with ⟨ownerLifetime, hownerSlot⟩
      have hslotValue :
          slot.value = .value (owningRef storage) := by
        have hslotEq :
            slot =
              { value := .value (owningRef storage),
                lifetime := ownerLifetime } :=
          Option.some.inj (hslot.symm.trans hownerSlot)
        exact congrArg StoreSlot.value hslotEq
      have hmem :
          storage ∈ partialValueOwningLocations slot.value :=
        mem_partialValueOwningLocations_of_eq_owningRef hslotValue
      exact ValidPartialValue.no_owned_path_to_storage hvalid hslot rfl hmem
        (ProgramStore.OwnsTransitively.direct ⟨ownerLifetime, hownerSlot⟩)
  | trans howns htail =>
      rename_i middle
      rcases howns with ⟨ownerLifetime, hownerSlot⟩
      have hslotValue :
          slot.value = .value (owningRef middle) := by
        have hslotEq :
            slot =
              { value := .value (owningRef middle),
                lifetime := ownerLifetime } :=
          Option.some.inj (hslot.symm.trans hownerSlot)
        exact congrArg StoreSlot.value hslotEq
      have hmem :
          middle ∈ partialValueOwningLocations slot.value :=
        mem_partialValueOwningLocations_of_eq_owningRef hslotValue
      exact ValidPartialValue.no_owned_path_to_storage hvalid hslot rfl hmem htail

theorem ValidPartialValueWhenInitialized.no_storage_ownership_cycle {env : Env}
    {store : ProgramStore} {storage : Location} {slot : StoreSlot}
    {ty : PartialTy} :
    store.slotAt storage = some slot →
    ValidPartialValueWhenInitialized env store slot.value ty →
    ¬ ProgramStore.OwnsTransitively store storage storage := by
  intro hslot hvalid hpath
  cases hpath with
  | direct howns =>
      rcases howns with ⟨ownerLifetime, hownerSlot⟩
      have hslotValue :
          slot.value = .value (owningRef storage) := by
        have hslotEq :
            slot =
              { value := .value (owningRef storage),
                lifetime := ownerLifetime } :=
          Option.some.inj (hslot.symm.trans hownerSlot)
        exact congrArg StoreSlot.value hslotEq
      have hmem :
          storage ∈ partialValueOwningLocations slot.value :=
        mem_partialValueOwningLocations_of_eq_owningRef hslotValue
      exact ValidPartialValueSkeleton.no_owned_path_to_storage
        hvalid.skeleton hslot rfl hmem
        (ProgramStore.OwnsTransitively.direct ⟨ownerLifetime, hownerSlot⟩)
  | trans howns htail =>
      rename_i middle
      rcases howns with ⟨ownerLifetime, hownerSlot⟩
      have hslotValue :
          slot.value = .value (owningRef middle) := by
        have hslotEq :
            slot =
              { value := .value (owningRef middle),
                lifetime := ownerLifetime } :=
          Option.some.inj (hslot.symm.trans hownerSlot)
        exact congrArg StoreSlot.value hslotEq
      have hmem :
          middle ∈ partialValueOwningLocations slot.value :=
        mem_partialValueOwningLocations_of_eq_owningRef hslotValue
      exact ValidPartialValueSkeleton.no_owned_path_to_storage
        hvalid.skeleton hslot rfl hmem htail

theorem partialTyStrengthens_trans_safe {left middle right : PartialTy} :
    PartialTyStrengthens left middle →
    PartialTyStrengthens middle right →
    PartialTyStrengthens left right := by
  intro hleft hright
  induction hleft generalizing right with
  | reflex =>
      exact hright
  | box hbox ih =>
      cases hright with
      | reflex => exact PartialTyStrengthens.box hbox
      | box hinner => exact PartialTyStrengthens.box (ih hinner)
      | boxIntoUndef hinner =>
          exact PartialTyStrengthens.boxIntoUndef (ih hinner)
  | tyBox hbox ih =>
      cases hright with
      | reflex => exact PartialTyStrengthens.tyBox hbox
      | tyBox hinner => exact PartialTyStrengthens.tyBox (ih hinner)
      | intoUndef hinner =>
          cases hinner with
          | reflex =>
              exact PartialTyStrengthens.intoUndef
                (PartialTyStrengthens.tyBox hbox)
          | tyBox hrightInner =>
              exact PartialTyStrengthens.intoUndef
                (PartialTyStrengthens.tyBox (ih hrightInner))
  | undefLeft hundef ih =>
      cases hright with
      | reflex => exact PartialTyStrengthens.undefLeft hundef
      | undefLeft hinner => exact PartialTyStrengthens.undefLeft (ih hinner)
  | intoUndef hundef ih =>
      cases hright with
      | reflex => exact PartialTyStrengthens.intoUndef hundef
      | undefLeft hinner => exact PartialTyStrengthens.intoUndef (ih hinner)
  | boxIntoUndef hundef ih =>
      cases hright with
      | reflex => exact PartialTyStrengthens.boxIntoUndef hundef
      | undefLeft hinner =>
          cases hinner with
          | reflex => exact PartialTyStrengthens.boxIntoUndef hundef
          | tyBox hbox =>
              exact PartialTyStrengthens.boxIntoUndef
                (ih (PartialTyStrengthens.undefLeft hbox))

theorem validPartialValue_strengthen_sameShape {store : ProgramStore}
    {value : PartialValue} {oldTy newTy : PartialTy} :
    ValidPartialValue store value oldTy →
    PartialTyStrengthens oldTy newTy →
    PartialTy.sameShape oldTy newTy →
    ValidPartialValue store value newTy := by
  intro hvalid
  induction hvalid generalizing newTy with
  | unit =>
      intro hstrength hshape
      cases hstrength with
      | reflex => exact ValidPartialValue.unit
      | intoUndef _ => simp [PartialTy.sameShape] at hshape
  | int =>
      intro hstrength hshape
      cases hstrength with
      | reflex => exact ValidPartialValue.int
      | intoUndef _ => simp [PartialTy.sameShape] at hshape
  | undef =>
      intro hstrength _hshape
      cases hstrength with
      | reflex => exact ValidPartialValue.undef
      | undefLeft _ => exact ValidPartialValue.undef
  | borrow hloc =>
      intro hstrength hshape
      cases hstrength with
      | reflex => exact ValidPartialValue.borrow hloc
      | intoUndef _ => simp [PartialTy.sameShape] at hshape
  | box hslot hinner ih =>
      intro hstrength hshape
      cases hstrength with
      | reflex => exact ValidPartialValue.box hslot hinner
      | box hinnerStrength =>
          exact ValidPartialValue.box hslot
            (ih hinnerStrength (by simpa [PartialTy.sameShape] using hshape))
      | boxIntoUndef _ => simp [PartialTy.sameShape] at hshape
  | boxFull hslot hinner ih =>
      intro hstrength hshape
      cases hstrength with
      | reflex => exact ValidPartialValue.boxFull hslot hinner
      | tyBox hinnerStrength =>
          exact ValidPartialValue.boxFull hslot
            (ih hinnerStrength (by
              simpa [PartialTy.sameShape, Ty.sameShape] using hshape))
      | intoUndef _ => simp [PartialTy.sameShape] at hshape

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

theorem validStoreTyping_block_head {store : ProgramStore} {typing : StoreTyping}
    {blockLifetime : Lifetime} {term : Term} {rest : List Term} :
    ValidStoreTyping store (.block blockLifetime (term :: rest)) typing →
    ValidStoreTyping store term typing := by
  intro htyping value hmem
  exact htyping value (by
    simp [termValues] at hmem ⊢
    exact Or.inl hmem)

theorem validStoreTyping_block_tail_of_cons {store : ProgramStore}
    {typing : StoreTyping} {blockLifetime : Lifetime} {term : Term}
    {rest : List Term} :
    ValidStoreTyping store (.block blockLifetime (term :: rest)) typing →
    ValidStoreTyping store (.block blockLifetime rest) typing := by
  intro htyping value hmem
  exact htyping value (by
    simp [termValues] at hmem ⊢
    exact Or.inr hmem)

/-- `ValidStoreTyping` is monotone along value containment; the
per-constructor corollaries below give dot-notation access at the
sub-term extraction sites of the soundness proofs. -/
theorem ValidStoreTyping.mono {store : ProgramStore} {big sub : Term}
    {typing : StoreTyping}
    (hvalid : ValidStoreTyping store big typing)
    (hsub : ∀ value, value ∈ termValues sub → value ∈ termValues big) :
    ValidStoreTyping store sub typing :=
  fun value hmem => hvalid value (hsub value hmem)

theorem validStoreTyping_sourceTerm_of_validStoreTyping
    {store store' : ProgramStore} {term : Term} {typing : StoreTyping} :
    SourceTerm term →
    ValidStoreTyping store term typing →
    ValidStoreTyping store' term typing := by
  intro hsource htyping value hmem
  rcases htyping value hmem with ⟨ty, hvalueTyping, _hvalidValue⟩
  refine ⟨ty, hvalueTyping, ?_⟩
  have hsourceValue : SourceValue value := hsource value hmem
  cases value with
  | unit =>
      cases hvalueTyping
      exact ValidPartialValue.unit
  | int _ =>
      cases hvalueTyping
      exact ValidPartialValue.int
  | ref _ =>
      cases hsourceValue

/-- A singleton block has the same runtime values as its body term. -/
theorem validStoreTyping_block_singleton_inner {store : ProgramStore}
    {typing : StoreTyping} {blockLifetime : Lifetime} {term : Term} :
    ValidStoreTyping store (.block blockLifetime [term]) typing →
    ValidStoreTyping store term typing := by
  intro htyping value hmem
  exact htyping value (by simpa [termValues] using hmem)

theorem validPartialValueSkeleton_owningLocation_allocated {store : ProgramStore}
    {partialValue : PartialValue} {partialTy : PartialTy} {owned : Location} :
    ValidPartialValueSkeleton store partialValue partialTy →
    owned ∈ partialValueOwningLocations partialValue →
    ∃ slot, store.slotAt owned = some slot := by
  intro hvalid hmem
  induction hvalid with
  | unit =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | int =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | undef =>
      simp [partialValueOwningLocations] at hmem
  | borrow =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | @box location slot _inner hslot _hinner _ih =>
      have howned : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] using hmem
      rw [howned]
      exact ⟨slot, hslot⟩
  | @boxFull location slot _ty hslot _hinner _ih =>
      have howned : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] using hmem
      rw [howned]
      exact ⟨slot, hslot⟩

theorem validPartialValue_owningLocation_allocated {store : ProgramStore}
    {partialValue : PartialValue} {partialTy : PartialTy} {owned : Location} :
    ValidPartialValue store partialValue partialTy →
    owned ∈ partialValueOwningLocations partialValue →
    ∃ slot, store.slotAt owned = some slot := by
  intro hvalid
  exact validPartialValueSkeleton_owningLocation_allocated hvalid.skeleton

theorem validPartialValue_nonOwner_of_envShape {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    ValidPartialValue store value ty →
    (ty = .ty .unit ∨ ty = .ty .int ∨
      ∃ mutable targets, ty = .ty (.borrow mutable targets)) →
    PartialValueNonOwner value := by
  intro hvalid hshape
  cases hvalid with
  | unit =>
      exact partialValueNonOwner_unit
  | int =>
      exact partialValueNonOwner_int _
  | undef =>
      rcases hshape with hunit | hint | hborrow
      · cases hunit
      · cases hint
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow
  | borrow =>
      exact partialValueNonOwner_borrowed _
  | box =>
      rcases hshape with hunit | hint | hborrow
      · cases hunit
      · cases hint
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow
  | boxFull =>
      rcases hshape with hunit | hint | hborrow
      · cases hunit
      · cases hint
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow

theorem validPartialValueWhenInitialized_nonOwner_of_envShape {env : Env}
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy} :
    ValidPartialValueWhenInitialized env store value ty →
    (ty = .ty .unit ∨ ty = .ty .int ∨
      ∃ mutable targets, ty = .ty (.borrow mutable targets)) →
    PartialValueNonOwner value := by
  intro hvalid hshape
  cases hvalid with
  | unit =>
      exact partialValueNonOwner_unit
  | int =>
      exact partialValueNonOwner_int _
  | undef =>
      rcases hshape with hunit | hint | hborrow
      · cases hunit
      · cases hint
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow
  | borrowLive =>
      exact partialValueNonOwner_borrowed _
  | borrowStale =>
      exact partialValueNonOwner_borrowed _
  | box =>
      rcases hshape with hunit | hint | hborrow
      · cases hunit
      · cases hint
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow
  | boxFull =>
      rcases hshape with hunit | hint | hborrow
      · cases hunit
      · cases hint
      · rcases hborrow with ⟨_mutable, _targets, hborrow⟩
        cases hborrow

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

theorem validPartialValueWhenInitialized_owningLocation_allocated
    {env : Env} {store : ProgramStore}
    {partialValue : PartialValue} {partialTy : PartialTy} {owned : Location} :
    ValidPartialValueWhenInitialized env store partialValue partialTy →
    owned ∈ partialValueOwningLocations partialValue →
    ∃ slot, store.slotAt owned = some slot := by
  intro hvalid hmem
  induction hvalid with
  | unit =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | int =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | undef =>
      simp [partialValueOwningLocations] at hmem
  | borrowLive =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | borrowStale =>
      simp [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?] at hmem
  | @box location slot inner hslot _hinner ih =>
      have howned : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?]
          using hmem
      rw [howned]
      exact ⟨slot, hslot⟩
  | @boxFull location slot ty hslot _hinner ih =>
      have howned : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations, valueOwnedLocation?]
          using hmem
      rw [howned]
      exact ⟨slot, hslot⟩

theorem validValueWhenInitialized_owningLocation_allocated {env : Env}
    {store : ProgramStore} {value : Value} {ty : Ty} {owned : Location} :
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    owned ∈ valueOwningLocations value →
    ∃ slot, store.slotAt owned = some slot := by
  intro hvalid hmem
  exact validPartialValueWhenInitialized_owningLocation_allocated hvalid
    (by simpa [partialValueOwningLocations] using hmem)

theorem validValueWhenInitialized_fresh_not_owningLocation {env : Env}
    {store : ProgramStore} {value : Value} {ty : Ty} {owned : Location} :
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    store.fresh owned →
    owned ∉ valueOwningLocations value := by
  intro hvalid hfresh hmem
  rcases validValueWhenInitialized_owningLocation_allocated hvalid hmem with
    ⟨slot, hslot⟩
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

theorem storeOwnersAllocated_update_value_of_validValueWhenInitialized
    {env : Env} {store : ProgramStore}
    {updatedLocation : Location} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    StoreOwnersAllocated
      (store.update updatedLocation { value := .value value, lifetime := lifetime }) := by
  intro hallocated hvalidValue
  exact storeOwnersAllocated_update hallocated (by
    intro owned hmem
    rcases validValueWhenInitialized_owningLocation_allocated hvalidValue hmem with
      ⟨allocatedSlot, hallocatedSlot⟩
    by_cases howned : owned = updatedLocation
    · subst howned
      exact ⟨{ value := .value value, lifetime := lifetime }, by
        simp [ProgramStore.update]⟩
    · exact ⟨allocatedSlot, by
        simpa [ProgramStore.update, howned] using hallocatedSlot⟩)

theorem storeOwnersAllocated_boxAt_of_validValueWhenInitialized {env : Env}
    {store : ProgramStore} {address : Nat} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    StoreOwnersAllocated (store.boxAt address value).1 := by
  intro hallocated hvalidValue
  exact storeOwnersAllocated_update_value_of_validValueWhenInitialized
    (updatedLocation := .heap address)
    (lifetime := Lifetime.root) hallocated hvalidValue

theorem storeOwnersAllocated_declare_of_validValueWhenInitialized {env : Env}
    {store : ProgramStore} {x : Name} {lifetime : Lifetime} {value : Value}
    {ty : Ty} :
    StoreOwnersAllocated store →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    StoreOwnersAllocated (store.declare x lifetime value) := by
  intro hallocated hvalidValue
  exact storeOwnersAllocated_update_value_of_validValueWhenInitialized
    (updatedLocation := .var x) hallocated hvalidValue

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

/-- Writing a weakly valid value through an lval preserves owner allocation. -/
theorem storeOwnersAllocated_write_value_of_validValueWhenInitialized
    {env : Env} {store store' : ProgramStore}
    {lv : LVal} {value : Value} {ty : Ty} :
    StoreOwnersAllocated store →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
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
          exact storeOwnersAllocated_update_value_of_validValueWhenInitialized
            hallocated hvalidValue

/-- Definition 4.6, variable projection `Θ`. -/
def VariableProjection (name : Name) : Location :=
  .var name

/--
Definition 4.7, safe abstraction `S ∼ₛ Γ`.

Heap locations are intentionally ignored in the domain agreement, as in the
paper.  Because stores and environments are abstract partial maps, domain
agreement is stated pointwise for variable locations.
-/
def FullSafeAbstraction (store : ProgramStore) (env : Env) : Prop :=
  (∀ x, (∃ slot, store.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, env.slotAt x = some envSlot) ∧
  ∀ x envSlot,
    env.slotAt x = some envSlot →
    ∃ value,
      store.slotAt (VariableProjection x) =
        some (StoreSlot.mk value envSlot.lifetime) ∧
      ValidPartialValue store value envSlot.ty

infix:50 " ∼ₛ " => FullSafeAbstraction

theorem FullSafeAbstraction.undef_slot {store : ProgramStore} {env : Env}
    {x : Name} {ty : Ty} {lifetime : Lifetime} :
    store ∼ₛ env →
    env.slotAt x = some { ty := .undef ty, lifetime := lifetime } →
    store.slotAt (VariableProjection x) =
      some { value := .undef, lifetime := lifetime } := by
  intro hsafe henv
  rcases hsafe.2 x { ty := .undef ty, lifetime := lifetime } henv with
    ⟨value, hstore, hvalid⟩
  have hvalue : value = .undef := validPartialValue_undef_iff.mp hvalid
  simpa [hvalue] using hstore

theorem FullSafeAbstraction.transport_pointwise
    {store : ProgramStore} {env result : Env}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    store ∼ₛ env →
    store ∼ₛ result := by
  intro hsafe
  constructor
  · intro x
    constructor
    · intro hstoreDomain
      rcases (hsafe.1 x).mp hstoreDomain with ⟨slot, hslot⟩
      exact ⟨slot, by simpa [heq x] using hslot⟩
    · intro hresultDomain
      rcases hresultDomain with ⟨slot, hslot⟩
      exact (hsafe.1 x).mpr ⟨slot, by simpa [heq x] using hslot⟩
  · intro x envSlot hslot
    have hsourceSlot : env.slotAt x = some envSlot := by
      simpa [heq x] using hslot
    exact hsafe.2 x envSlot hsourceSlot

theorem FullSafeAbstraction.borrow_value_target {store : ProgramStore} {env : Env}
    {x : Name} {lifetime : Lifetime} {mutable : Bool} {target : LVal}
    {location : Location} :
    store ∼ₛ env →
    env.slotAt x =
      some { ty := .ty (.borrow mutable target), lifetime := lifetime } →
    store.slotAt (VariableProjection x) =
      some (StoreSlot.mk
        (.value (.ref { location := location, owner := false })) lifetime) →
    store.loc target = some location := by
  intro hsafe henv hstore
  rcases hsafe.2 x { ty := .ty (.borrow mutable target), lifetime := lifetime }
      henv with
    ⟨value, hstoreAbstract, hvalid⟩
  have hslotEq :
      StoreSlot.mk value lifetime =
        StoreSlot.mk
          (.value (.ref { location := location, owner := false })) lifetime :=
    Option.some.inj (hstoreAbstract.symm.trans hstore)
  cases hslotEq
  cases hvalid with
  | borrow hloc =>
      exact hloc

theorem FullSafeAbstraction.borrow_read_target {store : ProgramStore} {env : Env}
    {x : Name} {lifetime : Lifetime} {mutable : Bool} {target : LVal}
    {location : Location} :
    store ∼ₛ env →
    env.slotAt x =
      some { ty := .ty (.borrow mutable target), lifetime := lifetime } →
    store.read (.var x) =
      some (StoreSlot.mk
        (.value (.ref { location := location, owner := false })) lifetime) →
    store.loc target = some location := by
  intro hsafe henv hread
  exact FullSafeAbstraction.borrow_value_target hsafe henv
    (by simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread)

theorem fullSafeAbstraction_of_domain_and_slots {store : ProgramStore} {env : Env} :
    (∀ x, (∃ slot, store.slotAt (VariableProjection x) = some slot) ↔
          ∃ envSlot, env.slotAt x = some envSlot) →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      ∃ value,
        store.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } ∧
        ValidPartialValue store value envSlot.ty) →
    store ∼ₛ env := by
  intro hdomain hslots
  exact ⟨hdomain, hslots⟩

/--
Transport safe abstraction across an environment shape/strengthening map when
the runtime store itself is unchanged.

This is the store-side counterpart to the shape maps produced by environment
writes: same-shape strengthening preserves runtime-value validity, while the
two slot maps provide exact domain agreement.
-/
theorem fullSafeAbstraction_transport_sameShape {store : ProgramStore}
    {env result : Env} :
    store ∼ₛ env →
    (∀ x resultSlot,
      result.slotAt x = some resultSlot →
      ∃ sourceSlot,
        env.slotAt x = some sourceSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime ∧
          PartialTyStrengthens sourceSlot.ty resultSlot.ty ∧
          PartialTy.sameShape sourceSlot.ty resultSlot.ty) →
    (∀ x sourceSlot,
      env.slotAt x = some sourceSlot →
      ∃ resultSlot,
        result.slotAt x = some resultSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime) →
    store ∼ₛ result := by
  intro hsafe hback hfwd
  refine fullSafeAbstraction_of_domain_and_slots ?domain ?slots
  · intro x
    constructor
    · intro hstoreDomain
      rcases (hsafe.1 x).mp hstoreDomain with ⟨sourceSlot, hsource⟩
      rcases hfwd x sourceSlot hsource with ⟨resultSlot, hresult, _⟩
      exact ⟨resultSlot, hresult⟩
    · intro hresultDomain
      rcases hresultDomain with ⟨resultSlot, hresult⟩
      rcases hback x resultSlot hresult with
        ⟨sourceSlot, hsource, _hlife, _hstrength, _hshape⟩
      exact (hsafe.1 x).mpr ⟨sourceSlot, hsource⟩
  · intro x resultSlot hresult
    rcases hback x resultSlot hresult with
      ⟨sourceSlot, hsource, hlife, hstrength, hshape⟩
    rcases hsafe.2 x sourceSlot hsource with
      ⟨value, hstore, hvalid⟩
    refine ⟨value, ?_, ?_⟩
    · simpa [hlife] using hstore
    · exact validPartialValue_strengthen_sameShape hvalid hstrength hshape

theorem validPartialValueWhenInitialized_transport_env
    {env result : Env} {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} :
    (∀ {target : LVal},
      TargetInitialized result target →
      TargetInitialized env target) →
    ValidPartialValueWhenInitialized env store value ty →
    ValidPartialValueWhenInitialized result store value ty := by
  intro hinitBack hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      exact ValidPartialValueWhenInitialized.undef
  | @borrowLive location mutable target _hinitialized hloc =>
      by_cases hresultInitialized : TargetInitialized result target
      · exact ValidPartialValueWhenInitialized.borrowLive
          hresultInitialized hloc
      · exact ValidPartialValueWhenInitialized.borrowStale
          (location := location) (mutable := mutable) (target := target)
          hresultInitialized
  | @borrowStale location mutable target hstale =>
      have hresultStale : ¬ TargetInitialized result target := by
        intro hresultInitialized
        exact hstale (hinitBack hresultInitialized)
      exact ValidPartialValueWhenInitialized.borrowStale
        (location := location) (mutable := mutable) (target := target)
        hresultStale
  | box hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.box hslot ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.boxFull hslot ih

theorem fullSafeAbstraction_env_no_lifetime_of_store_no_lifetime {store : ProgramStore}
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
theorem fullSafeAbstraction_dropsLifetime_no_slots {store store' : ProgramStore}
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
      (fullSafeAbstraction_env_no_lifetime_of_store_no_lifetime hsafe hnoStore)
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
theorem fullSafeAbstraction_dropLifetime_of_preserved
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
  exact fullSafeAbstraction_dropLifetime_of_preserved hdomain hpreserve

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

@[simp] theorem fullSafeAbstraction_empty :
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

theorem fullSafeAbstraction_store_fresh_var {store : ProgramStore} {env : Env}
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

theorem fullSafeAbstraction_var_read_nonOwner_of_envShape {store : ProgramStore}
    {env : Env} {x : Name} {envSlot : EnvSlot} {oldSlot : StoreSlot} :
    store ∼ₛ env →
    env.slotAt x = some envSlot →
    store.read (.var x) = some oldSlot →
    (envSlot.ty = .ty .unit ∨ envSlot.ty = .ty .int ∨
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
    EnvWrite env (.var x) ty env' →
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
theorem fullSafeAbstraction_update_var_of_preserved {store' : ProgramStore}
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
Safe-abstraction preservation for updating one variable's abstract slot to an
arbitrary partial type.

Direct assignment to a variable uses the full-type specialization above; writes
through owned boxes update the base variable's boxed partial type, so they need
this more general form.
-/
theorem fullSafeAbstraction_update_var_partial_of_preserved {store' : ProgramStore}
    {env env' : Env} {x : Name} {envSlot : EnvSlot}
    {value : PartialValue} {newTy : PartialTy} :
    env.slotAt x = some envSlot →
    store'.slotAt (VariableProjection x) =
      some { value := value, lifetime := envSlot.lifetime } →
    ValidPartialValue store' value newTy →
    env' = env.update x { envSlot with ty := newTy } →
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
        exact ⟨{ envSlot with ty := newTy }, by simp [Env.update]⟩
      · intro _henvDomain
        exact ⟨{ value := value, lifetime := envSlot.lifetime }, hstoreX⟩
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
          updatedSlot = { envSlot with ty := newTy } := by
        simpa [Env.update] using henvUpdated.symm
      subst hupdatedSlot
      exact ⟨value, hstoreX, hnewValid⟩
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
    EnvWrite env (.var x) ty env' →
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
  exact fullSafeAbstraction_update_var_of_preserved henvX hstoreX hnewValid henv'
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
    {store storeAfterWrite store' : ProgramStore} {env env' : Env}
    {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some envSlot →
    EnvWrite env (.var x) ty env' →
    PartialValueNonOwner oldSlot.value →
    store.read (.var x) = some oldSlot →
    store.write (.var x) (.value value) = some storeAfterWrite →
    Drops storeAfterWrite [oldSlot.value] store' →
    ValidPartialValue store' (.value value) (.ty ty) →
    (∀ y otherEnvSlot,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      ∃ oldValue,
        store'.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } ∧
        ValidPartialValue store' oldValue otherEnvSlot.ty) →
    store' ∼ₛ env' := by
  intro hsafe henvX hwriteEnv hnonOwner hread hwrite hdrops hnewValid hpreserveOther
  have hdropEq : store' = storeAfterWrite :=
    drops_partialValue_nonOwner_eq hnonOwner hdrops
  subst store'
  have hstoreX : store.slotAt (VariableProjection x) = some oldSlot := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  have hlifetime : oldSlot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henvX with ⟨safeValue, hsafeSlot, _hvalid⟩
    rw [hstoreX] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact congrArg StoreSlot.lifetime hslotEq
  have hstoreAfterWrite :
      storeAfterWrite = store.update (VariableProjection x)
        { oldSlot with value := .value value } :=
    write_var_eq hstoreX hwrite
  refine storePreservation_assign_var_of_preserved henvX hwriteEnv hstoreX
    hlifetime hwrite hnewValid ?domain hpreserveOther
  intro y hyx
  constructor
  · intro hstoreDomain
    rcases hstoreDomain with ⟨slot, hslot⟩
    have hslotStore : store.slotAt (VariableProjection y) = some slot := by
      rw [hstoreAfterWrite] at hslot
      simpa [ProgramStore.update, VariableProjection, hyx] using hslot
    exact (hsafe.1 y).mp ⟨slot, hslotStore⟩
  · intro henvDomain
    rcases (hsafe.1 y).mpr henvDomain with ⟨slot, hslot⟩
    exact ⟨slot, by
      rw [hstoreAfterWrite]
      simpa [ProgramStore.update, VariableProjection, hyx] using hslot⟩

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

/-- Updating a fresh location preserves existing owner-skeleton abstractions. -/
theorem validPartialValueSkeleton_update_of_fresh {store : ProgramStore}
    {updatedLocation : Location} {newSlot : StoreSlot}
    {partialValue : PartialValue} {ty : PartialTy} :
    store.fresh updatedLocation →
    ValidPartialValueSkeleton store partialValue ty →
    ValidPartialValueSkeleton (store.update updatedLocation newSlot) partialValue ty := by
  intro hfresh hvalid
  induction hvalid with
  | unit => exact ValidPartialValueSkeleton.unit
  | int => exact ValidPartialValueSkeleton.int
  | undef => exact ValidPartialValueSkeleton.undef
  | borrow => exact ValidPartialValueSkeleton.borrow
  | box hslot _hinner ih =>
      exact ValidPartialValueSkeleton.box (slotAt_update_of_slotAt hfresh hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueSkeleton.boxFull (slotAt_update_of_slotAt hfresh hslot) ih

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
  | borrow hloc =>
      exact ValidPartialValue.borrow (loc_update_of_loc hfresh hloc)
  | box hslot _hinner ih =>
      exact ValidPartialValue.box (slotAt_update_of_slotAt hfresh hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValue.boxFull (slotAt_update_of_slotAt hfresh hslot) ih

/-- Updating a fresh location preserves weak partial-value abstractions. -/
theorem validPartialValueWhenInitialized_update_of_fresh {env : Env}
    {store : ProgramStore} {updatedLocation : Location} {newSlot : StoreSlot}
    {partialValue : PartialValue} {ty : PartialTy} :
    store.fresh updatedLocation →
    ValidPartialValueWhenInitialized env store partialValue ty →
    ValidPartialValueWhenInitialized env (store.update updatedLocation newSlot)
      partialValue ty := by
  intro hfresh hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      exact ValidPartialValueWhenInitialized.undef
  | borrowLive hinitialized hloc =>
      exact ValidPartialValueWhenInitialized.borrowLive hinitialized
        (loc_update_of_loc hfresh hloc)
  | borrowStale hstale =>
      exact ValidPartialValueWhenInitialized.borrowStale hstale
  | box hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.box
        (slotAt_update_of_slotAt hfresh hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.boxFull
        (slotAt_update_of_slotAt hfresh hslot) ih

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

/-- Declaring a fresh variable preserves existing owner-skeleton abstractions. -/
theorem validPartialValueSkeleton_declare {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {newValue : Value} {partialValue : PartialValue}
    {ty : PartialTy} :
    store.fresh (.var x) →
    ValidPartialValueSkeleton store partialValue ty →
    ValidPartialValueSkeleton (store.declare x lifetime newValue) partialValue ty := by
  intro hfresh hvalid
  induction hvalid with
  | unit => exact ValidPartialValueSkeleton.unit
  | int => exact ValidPartialValueSkeleton.int
  | undef => exact ValidPartialValueSkeleton.undef
  | borrow => exact ValidPartialValueSkeleton.borrow
  | box hslot _hinner ih =>
      exact ValidPartialValueSkeleton.box (slotAt_declare_of_slotAt hfresh hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueSkeleton.boxFull (slotAt_declare_of_slotAt hfresh hslot) ih

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
  | borrow hloc =>
      exact ValidPartialValue.borrow (loc_declare_of_loc hfresh hloc)
  | box hslot _hinner ih =>
      exact ValidPartialValue.box (slotAt_declare_of_slotAt hfresh hslot) ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValue.boxFull (slotAt_declare_of_slotAt hfresh hslot) ih

/-- Declaring a fresh variable preserves existing initialized partial-value abstractions. -/
theorem validPartialValueWhenInitialized_declare {store : ProgramStore}
    {env : Env} {x : Name} {lifetime : Lifetime} {newValue : Value}
    {partialValue : PartialValue} {ty : PartialTy} :
    store.fresh (.var x) →
    ValidPartialValueWhenInitialized env store partialValue ty →
    ValidPartialValueWhenInitialized env (store.declare x lifetime newValue)
      partialValue ty := by
  intro hfresh hvalid
  simpa [ProgramStore.declare] using
    (validPartialValueWhenInitialized_update_of_fresh
      (updatedLocation := .var x)
      (newSlot := { value := .value newValue, lifetime := lifetime })
      hfresh hvalid)

/--
Lemma 9.10 support, `R-Declare` safe-abstraction preservation.

The explicit `hpreserveOld` premise is the store-extension obligation for values
already represented by `Γ`; it is discharged by later store-monotonicity lemmas.
-/
theorem fullSafeAbstraction_declare {store : ProgramStore} {env : Env}
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
      exact ⟨oldValue,
        by
          simpa [ProgramStore.declare, ProgramStore.update, VariableProjection, hyx]
            using hstoreSlot,
        hpreserveOld y envSlot oldValue hyx holdEnv hstoreSlot⟩

/--
Lemma 9.10 support, variable `R-Move` safe-abstraction preservation.

This is the `π = ε` base case of the paper's `move(Γ, w)` / write-`undef`
correspondence.  The `hpreserveOld` premise packages the separate no-borrow /
path-stability obligation for variables other than `x`.
-/
theorem fullSafeAbstraction_move_var {store : ProgramStore} {env : Env}
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
          exact fullSafeAbstraction_move_var hsafe henvSlot rfl hstoreSlot
            (by
              intro y envSlot oldOtherValue hyx henv hslot
              exact hpreserveOld y envSlot oldOtherValue hyx henv hslot)

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

/-- The owning reference returned by `boxAt` weakly abstracts `Box<T>`. -/
theorem validValueWhenInitialized_boxAt_ref {env : Env} {store : ProgramStore}
    {address : Nat} {value : Value} {ty : Ty} :
    store.fresh (.heap address) →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    ValidPartialValueWhenInitialized env (store.boxAt address value).1
      (.value (Value.ref (store.boxAt address value).2)) (.ty (.box ty)) := by
  intro hfresh hvalidValue
  exact ValidPartialValueWhenInitialized.boxFull
    (location := .heap address)
    (slot := { value := .value value, lifetime := Lifetime.root })
    (by simp [ProgramStore.boxAt])
    (validPartialValueWhenInitialized_update_of_fresh
      (updatedLocation := .heap address)
      (newSlot := { value := .value value, lifetime := Lifetime.root })
      hfresh hvalidValue)

/-- Lemma 9.10 support: heap allocation preserves safe abstraction of variables. -/
theorem fullSafeAbstraction_boxAt {store : ProgramStore} {env : Env}
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
    have hslot' :
        (store.boxAt address value).1.slotAt (VariableProjection x) =
          some { value := oldValue, lifetime := envSlot.lifetime } := by
      simpa [ProgramStore.boxAt, ProgramStore.update, VariableProjection]
        using hslot
    exact ⟨oldValue, hslot', validPartialValue_boxAt hfresh hvalid⟩

end Paper
end FWRust
