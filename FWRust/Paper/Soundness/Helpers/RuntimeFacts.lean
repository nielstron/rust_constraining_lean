import FWRust.Paper.Soundness.Helpers.Eqv

/-!
# Soundness helpers: Runtime facts

Runtime, value, and location facts for the single-target core.
-/

namespace FWRust
namespace Paper

open Core

/-- Under a shape-preserving strengthening, occurring variables only grow. -/
theorem partialTy_vars_mono {a b : PartialTy} (hstr : PartialTyStrengthens a b) :
    PartialTy.sameShape a b → ∀ v, v ∈ PartialTy.vars a → v ∈ PartialTy.vars b := by
  induction hstr with
  | reflex => intro _ v hv; exact hv
  | box _ ih =>
      intro hshape v hv
      simp only [PartialTy.vars] at hv ⊢
      exact ih (by simpa [PartialTy.sameShape] using hshape) v hv
  | tyBox _ ih =>
      intro hshape v hv
      simp only [PartialTy.vars, Ty.vars] at hv ⊢
      exact ih (by simpa [PartialTy.sameShape, Ty.sameShape] using hshape) v hv
  | undefLeft _ _ => intro _ v hv; simp [PartialTy.vars] at hv
  | intoUndef _ _ => intro hshape v _; simp [PartialTy.sameShape] at hshape
  | boxIntoUndef _ _ => intro hshape v _; simp [PartialTy.sameShape] at hshape

theorem EnvStrengthens.trans {a b c : Env} :
    EnvStrengthens a b → EnvStrengthens b c → EnvStrengthens a c := by
  intro hab hbc x
  specialize hab x
  specialize hbc x
  cases ha : a.slotAt x <;> cases hb : b.slotAt x <;> cases hc : c.slotAt x <;>
    simp [ha, hb, hc] at hab hbc ⊢
  rcases hab with ⟨hlab, htyab⟩
  rcases hbc with ⟨hlbc, htybc⟩
  exact ⟨hlab.trans hlbc, partialTyStrengthens_trans htyab htybc⟩

theorem EnvStrengthens.update_from_source_slot {source middle : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvStrengthens source middle →
    source.slotAt x = some slot →
    PartialTyStrengthens slot.ty newTy →
    EnvStrengthens source (middle.update x { slot with ty := newTy }) := by
  intro hstrength hslot hty y
  by_cases hy : y = x
  · subst hy
    simp [Env.update, hslot, hty]
  · have h := hstrength y
    simpa [Env.update, hy] using h

theorem PartialTyStrengthens.tyBox_rebox {sourceTy : Ty} {updatedTy : PartialTy} :
    PartialTyStrengthens (.ty sourceTy) updatedTy →
    PartialTy.sameShape (.ty sourceTy) updatedTy →
    PartialTyStrengthens (.ty (.box sourceTy)) (partialTyRebox updatedTy) := by
  intro hstrength hshape
  cases updatedTy with
  | ty targetTy =>
      exact PartialTyStrengthens.tyBox hstrength
  | box _ =>
      simp [PartialTy.sameShape] at hshape
  | undef _ =>
      simp [PartialTy.sameShape] at hshape

theorem safeStrengthening {store : ProgramStore} {env : Env}
    {lifetime : Lifetime} {left right : Ty} {value : Value} :
    WellFormedEnv env lifetime →
    store ∼ₛ env →
    PartialTyStrengthens (.ty left) (.ty right) →
    ValidValue store value left →
    ValidValue store value right := by
  intro _hwellFormed _hsafe hstrength hvalid
  exact validPartialValue_strengthen_sameShape hvalid hstrength
    (by simpa [PartialTy.sameShape] using ty_sameShape_of_strengthens hstrength)

theorem safeStrengthening_of_strengthens {store : ProgramStore}
    {left right : Ty} {value : Value} :
    PartialTyStrengthens (.ty left) (.ty right) →
    ValidValue store value left →
    ValidValue store value right := by
  intro hstrength hvalid
  exact validPartialValue_strengthen_sameShape hvalid hstrength
    (by simpa [PartialTy.sameShape] using ty_sameShape_of_strengthens hstrength)

theorem valueTyping_environment_eq {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    TermTyping env₁ typing lifetime (.val value) ty env₂ →
    env₁ = env₂ := by
  intro htyping
  cases htyping
  rfl

theorem valueTyping_deterministic {typing : StoreTyping} {value : Value}
    {left right : Ty} :
    ValueTyping typing value left →
    ValueTyping typing value right →
    left = right := by
  intro hleft hright
  exact ValueTyping.deterministic hleft hright

theorem termListTyping_singleton_value_environment_eq {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    TermListTyping env₁ typing lifetime [.val value] ty env₂ →
    env₁ = env₂ := by
  intro htyping
  cases htyping with
  | singleton hterm =>
      exact valueTyping_environment_eq hterm
  | cons _hterm hrest =>
      cases hrest

theorem termListTyping_singleton_value_valueTyping {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    TermListTyping env₁ typing lifetime [.val value] ty env₂ →
    ValueTyping typing value ty := by
  intro htyping
  cases htyping with
  | singleton hterm =>
      cases hterm with
      | const hvalueTyping => exact hvalueTyping
  | cons _hterm hrest =>
      cases hrest

theorem blockValueTyping_output_eq {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value : Value} {ty : Ty} :
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    env' = env.dropLifetime blockLifetime := by
  intro htyping
  cases htyping with
  | block _hblockChild hterms _hwellFormed hdrop =>
      have henv₂ := termListTyping_singleton_value_environment_eq hterms
      rw [henv₂]
      exact hdrop

theorem blockValueTyping_valueTyping {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value : Value} {ty : Ty} :
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    ValueTyping typing value ty := by
  intro htyping
  cases htyping with
  | block _hblockChild hterms _hwellFormed _hdrop =>
      exact termListTyping_singleton_value_valueTyping hterms

theorem validStoreTyping_value {store : ProgramStore} {typing : StoreTyping}
    {value : Value} {ty : Ty} :
    ValidStoreTyping store (.val value) typing →
    ValueTyping typing value ty →
    ValidValue store value ty := by
  intro hvalidStoreTyping hvalueTyping
  rcases hvalidStoreTyping value (by simp [termValues]) with
    ⟨storedTy, hstoredTyping, hvalidValue⟩
  have hty : storedTy = ty :=
    valueTyping_deterministic hstoredTyping hvalueTyping
  subst hty
  exact hvalidValue

theorem valuePreservation_value {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidStoreTyping store (.val value) typing →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidValue store value ty ∧ env₂ = env := by
  intro hvalidStoreTyping htyping
  cases htyping with
  | const hvalueTyping =>
      exact ⟨validStoreTyping_value hvalidStoreTyping hvalueTyping, rfl⟩

theorem preservation_refl_value {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidState store (.val value) ∧ store ∼ₛ env₂ ∧ ValidValue store value ty := by
  intro hvalidState hvalidStoreTyping hsafe htyping
  rcases valuePreservation_value hvalidStoreTyping htyping with
    ⟨hvalidValue, henv⟩
  subst henv
  exact ⟨hvalidState, hsafe, hvalidValue⟩

theorem preservation_refl_runtime_value {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidRuntimeState store (.val value) ∧ store ∼ₛ env₂ ∧
      ValidValue store value ty := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping
  rcases preservation_refl_value hvalidRuntime.1 hvalidStoreTyping hsafe htyping with
    ⟨hvalidState, hsafe₂, hvalidValue⟩
  exact ⟨⟨hvalidState,
      ValidRuntimeState.storeOwnersAllocated hvalidRuntime,
      ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime,
      ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime,
      ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime⟩,
    hsafe₂, hvalidValue⟩

theorem preservation_multistep_runtime_value {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
  rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact preservation_refl_runtime_value hvalidRuntime hvalidStoreTyping hsafe htyping

theorem preservation_refl_runtime_value_whenInitialized {store : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    SafeAbstraction store env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidRuntimeState store (.val value) ∧
      SafeAbstraction store env₂ ∧
      ValidPartialValueWhenInitialized env₂ store (.value value) (.ty ty) := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping
  rcases valuePreservation_value hvalidStoreTyping htyping with
    ⟨hvalidValue, henv⟩
  subst henv
  exact ⟨hvalidRuntime, hsafe, hvalidValue.whenInitialized⟩

theorem preservation_multistep_runtime_value_whenInitialized
    {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    SafeAbstraction store env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧
      SafeAbstraction finalStore env₂ ∧
      ValidPartialValueWhenInitialized env₂ finalStore (.value finalValue)
        (.ty ty) := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
  rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact preservation_refl_runtime_value_whenInitialized
    hvalidRuntime hvalidStoreTyping hsafe htyping

theorem preservation_value_tail_runtime {store finalStore : ProgramStore}
    {env : Env} {lifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) ∧ store ∼ₛ env ∧ ValidValue store value ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env ∧
      ValidValue finalStore finalValue ty := by
  intro hpreserved hmulti
  rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact hpreserved

theorem preservation_value_tail_runtime_full {store finalStore : ProgramStore}
    {env : Env} {lifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) ∧ store ≈ₛ env ∧ ValidValue store value ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ≈ₛ env ∧
      ValidValue finalStore finalValue ty := by
  intro hpreserved hmulti
  rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact hpreserved

theorem preservation_value_tail_runtime_whenInitialized
    {store finalStore : ProgramStore}
    {env : Env} {lifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    (ValidRuntimeState store (.val value) ∧
      SafeAbstraction store env ∧
      ValidPartialValueWhenInitialized env store (.value value) (.ty ty)) →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧
      SafeAbstraction finalStore env ∧
      ValidPartialValueWhenInitialized env finalStore (.value finalValue)
        (.ty ty) := by
  intro hpreserved hmulti
  rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact hpreserved

theorem preservation_multistep_of_step_to_value
    {store finalStore : ProgramStore} {lifetime : Lifetime}
    {term : Term} {finalValue : Value}
    {Result : ProgramStore → Value → Prop} :
    ¬ Terminal term →
    (∀ store' term',
      Step store lifetime term store' term' →
      ∃ value, term' = .val value) →
    (∀ store' value,
      Step store lifetime term store' (.val value) →
      Result store' value) →
    (∀ store' value finalStore finalValue,
      Result store' value →
      MultiStep store' lifetime (.val value) finalStore (.val finalValue) →
      Result finalStore finalValue) →
    MultiStep store lifetime term finalStore (.val finalValue) →
    Result finalStore finalValue := by
  intro hnotTerminal hstepValue hstepPreserve htail hmulti
  cases hmulti with
  | refl =>
      exact False.elim (hnotTerminal (value_terminal finalValue))
  | trans hstep hrest =>
      rcases hstepValue _ _ hstep with ⟨value, hterm⟩
      subst hterm
      exact htail _ _ _ _ (hstepPreserve _ _ hstep) hrest

theorem preservation_runtime_multistep_of_step_to_value
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {term : Term} {finalValue : Value} {ty : Ty} :
    ¬ Terminal term →
    (∀ store' term',
      Step store lifetime term store' term' →
      ∃ value, term' = .val value) →
    (∀ store' value,
      Step store lifetime term store' (.val value) →
      ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env ∧
        ValidValue store' value ty) →
    MultiStep store lifetime term finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env ∧
      ValidValue finalStore finalValue ty := by
  intro hnotTerminal hstepValue hstepPreserve hmulti
  exact preservation_multistep_of_step_to_value
    (Result := fun store' value =>
      ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env ∧
        ValidValue store' value ty)
    hnotTerminal hstepValue hstepPreserve
    (by
      intro _store' _value _finalStore _finalValue hpreserved htail
      exact preservation_value_tail_runtime hpreserved htail)
    hmulti

theorem preservation_runtime_multistep_of_step_to_value_full
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {term : Term} {finalValue : Value} {ty : Ty} :
    ¬ Terminal term →
    (∀ store' term',
      Step store lifetime term store' term' →
      ∃ value, term' = .val value) →
    (∀ store' value,
      Step store lifetime term store' (.val value) →
      ValidRuntimeState store' (.val value) ∧ store' ≈ₛ env ∧
        ValidValue store' value ty) →
    MultiStep store lifetime term finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ≈ₛ env ∧
      ValidValue finalStore finalValue ty := by
  intro hnotTerminal hstepValue hstepPreserve hmulti
  exact preservation_multistep_of_step_to_value
    (Result := fun store' value =>
      ValidRuntimeState store' (.val value) ∧ store' ≈ₛ env ∧
        ValidValue store' value ty)
    hnotTerminal hstepValue hstepPreserve
    (by
      intro _store' _value _finalStore _finalValue hpreserved htail
      exact preservation_value_tail_runtime_full hpreserved htail)
    hmulti

theorem preservation_runtime_multistep_of_step_to_value_whenInitialized
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {term : Term} {finalValue : Value} {ty : Ty} :
    ¬ Terminal term →
    (∀ store' term',
      Step store lifetime term store' term' →
      ∃ value, term' = .val value) →
    (∀ store' value,
      Step store lifetime term store' (.val value) →
      ValidRuntimeState store' (.val value) ∧
        SafeAbstraction store' env ∧
        ValidPartialValueWhenInitialized env store' (.value value) (.ty ty)) →
    MultiStep store lifetime term finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧
      SafeAbstraction finalStore env ∧
      ValidPartialValueWhenInitialized env finalStore (.value finalValue)
        (.ty ty) := by
  intro hnotTerminal hstepValue hstepPreserve hmulti
  exact preservation_multistep_of_step_to_value
    (Result := fun store' value =>
      ValidRuntimeState store' (.val value) ∧
        SafeAbstraction store' env ∧
        ValidPartialValueWhenInitialized env store' (.value value) (.ty ty))
    hnotTerminal hstepValue hstepPreserve
    (by
      intro _store' _value _finalStore _finalValue hpreserved htail
      exact preservation_value_tail_runtime_whenInitialized hpreserved htail)
    hmulti

def LValLocationAbstraction
    (store : ProgramStore) (lv : LVal) (ty : PartialTy) : Prop :=
  ∃ location slot,
    store.loc lv = some location ∧
    store.slotAt location = some slot ∧
    ValidPartialValue store slot.value ty

def RuntimeBorrowTarget
    (store : ProgramStore) (lv : LVal) (target : LVal) : Prop :=
  ∃ sourceLocation borrowedLocation slotLifetime,
    store.loc lv = some sourceLocation ∧
      store.slotAt sourceLocation =
        some (StoreSlot.mk
          (.value (.ref { location := borrowedLocation, owner := false }))
          slotLifetime) ∧
      store.loc target = some borrowedLocation

def RuntimeBorrowPointsTo
    (store : ProgramStore) (lv : LVal) (borrowedLocation : Location) : Prop :=
  ∃ sourceLocation slotLifetime,
    store.loc lv = some sourceLocation ∧
      store.slotAt sourceLocation =
        some (StoreSlot.mk
          (.value (.ref { location := borrowedLocation, owner := false }))
          slotLifetime)

theorem RuntimeBorrowTarget.pointsTo {store : ProgramStore} {lv target : LVal} :
    RuntimeBorrowTarget store lv target →
    ∃ borrowedLocation,
      store.loc target = some borrowedLocation ∧
        RuntimeBorrowPointsTo store lv borrowedLocation := by
  rintro ⟨sourceLocation, borrowedLocation, slotLifetime,
    hsourceLoc, hsourceSlot, htargetLoc⟩
  exact ⟨borrowedLocation, htargetLoc,
    sourceLocation, slotLifetime, hsourceLoc, hsourceSlot⟩

theorem RuntimeBorrowPointsTo.unique {store : ProgramStore} {lv : LVal}
    {left right : Location} :
    RuntimeBorrowPointsTo store lv left →
    RuntimeBorrowPointsTo store lv right →
    left = right := by
  rintro ⟨leftSource, leftLifetime, hleftLoc, hleftSlot⟩
    ⟨rightSource, rightLifetime, hrightLoc, hrightSlot⟩
  have hsourceEq : leftSource = rightSource :=
    Option.some.inj (hleftLoc.symm.trans hrightLoc)
  subst hsourceEq
  have hslotEq :
      StoreSlot.mk
        (.value (.ref { location := left, owner := false })) leftLifetime =
      StoreSlot.mk
        (.value (.ref { location := right, owner := false })) rightLifetime :=
    Option.some.inj (hleftSlot.symm.trans hrightSlot)
  injection hslotEq with hvalueEq _hlifetimeEq
  injection hvalueEq with hrefEq
  injection hrefEq with hrefRecordEq
  exact (Reference.mk.inj hrefRecordEq).1

theorem LValLocationAbstraction.borrow_target {store : ProgramStore}
    {lv : LVal} {mutable : Bool} {target : LVal} :
    LValLocationAbstraction store lv (.ty (.borrow mutable target)) →
    RuntimeBorrowTarget store lv target := by
  rintro ⟨sourceLocation, ⟨slotValue, slotLifetime⟩, hlv, hslot, hvalid⟩
  cases hvalid with
  | borrow htargetLoc =>
      exact ⟨sourceLocation, _, slotLifetime, hlv, hslot, htargetLoc⟩

def RuntimeBorrowTargetsConservative (store : ProgramStore) (env : Env) : Prop :=
  ∀ {lv mutable target lifetime},
    LValTyping env lv (.ty (.borrow mutable target)) lifetime →
    RuntimeBorrowTarget store lv target

def RuntimeCoherent (store : ProgramStore) (env : Env) : Prop :=
  ∀ {lv mutable target lifetime},
    LValTyping env lv (.ty (.borrow mutable target)) lifetime →
    ∃ targetTy targetLifetime borrowedLocation,
      LValTyping env target (.ty targetTy) targetLifetime ∧
        store.loc target = some borrowedLocation ∧
        RuntimeBorrowPointsTo store lv borrowedLocation

theorem RuntimeCoherent.borrowTargetsConservative {store : ProgramStore} {env : Env} :
    RuntimeCoherent store env →
    RuntimeBorrowTargetsConservative store env := by
  intro hcoherent _lv _mutable _target _lifetime htyping
  rcases hcoherent htyping with
    ⟨_targetTy, _targetLifetime, borrowedLocation,
      _htargetTyping, htargetLoc, hpointsTo⟩
  rcases hpointsTo with ⟨sourceLocation, slotLifetime, hsourceLoc, hsourceSlot⟩
  exact ⟨sourceLocation, borrowedLocation, slotLifetime,
    hsourceLoc, hsourceSlot, htargetLoc⟩

def LValDefinedLocationAbstraction
    (store : ProgramStore) (lv : LVal) : PartialTy → Prop
  | .undef _ => True
  | ty => LValLocationAbstraction store lv ty

def LValLocationAbstractionWhenInitialized
    (env : Env) (store : ProgramStore) (lv : LVal) (ty : PartialTy) : Prop :=
  ∃ location slot,
    store.loc lv = some location ∧
    store.slotAt location = some slot ∧
    ValidPartialValueWhenInitialized env store slot.value ty

def LValDefinedLocationAbstractionWhenInitialized
    (env : Env) (store : ProgramStore) (lv : LVal) : PartialTy → Prop
  | .undef _ => True
  | ty => LValLocationAbstractionWhenInitialized env store lv ty

theorem location_var_whenInitialized {store : ProgramStore} {env : Env}
    {x : Name} {slot : EnvSlot} :
    SafeAbstraction store env →
    env.slotAt x = some slot →
    LValLocationAbstractionWhenInitialized env store (.var x) slot.ty := by
  intro hsafe henv
  rcases hsafe.2 x slot henv with ⟨value, hstore, hvalid⟩
  exact ⟨.var x, StoreSlot.mk value slot.lifetime, by
      simp [ProgramStore.loc],
    by
      simpa [VariableProjection] using hstore,
    hvalid⟩

theorem location_box_whenInitialized {store : ProgramStore} {env : Env}
    {lv : LVal} {inner : PartialTy} :
    LValLocationAbstractionWhenInitialized env store lv (.box inner) →
    LValLocationAbstractionWhenInitialized env store (.deref lv) inner := by
  intro hlocation
  rcases hlocation with ⟨source, sourceSlot, hloc, hslot, hvalid⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hvalid with
  | box htarget hinner =>
      exact ⟨_, _, by
          simp [ProgramStore.loc, hloc, hslot],
        htarget,
        hinner⟩

theorem location_boxFull_whenInitialized {store : ProgramStore} {env : Env}
    {lv : LVal} {inner : Ty} :
    LValLocationAbstractionWhenInitialized env store lv (.ty (.box inner)) →
    LValLocationAbstractionWhenInitialized env store (.deref lv) (.ty inner) := by
  intro hlocation
  rcases hlocation with ⟨source, sourceSlot, hloc, hslot, hvalid⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hvalid with
  | boxFull htarget hinner =>
      exact ⟨_, _, by
          simp [ProgramStore.loc, hloc, hslot],
        htarget,
        hinner⟩

theorem validPartialValueWhenInitialized_full_value {env : Env}
    {store : ProgramStore} {partialValue : PartialValue} {ty : Ty} :
    ValidPartialValueWhenInitialized env store partialValue (.ty ty) →
    ∃ value, partialValue = .value value ∧
      ValidPartialValueWhenInitialized env store (.value value) (.ty ty) := by
  intro hvalid
  cases hvalid with
  | unit =>
      exact ⟨.unit, rfl, ValidPartialValueWhenInitialized.unit⟩
  | int =>
      exact ⟨.int _, rfl, ValidPartialValueWhenInitialized.int⟩
  | borrowLive hinitialized hloc =>
      exact ⟨.ref { location := _, owner := false }, rfl,
        ValidPartialValueWhenInitialized.borrowLive hinitialized hloc⟩
  | borrowStale hstale =>
      exact ⟨.ref { location := _, owner := false }, rfl,
        ValidPartialValueWhenInitialized.borrowStale hstale⟩
  | boxFull hslot hinner =>
      exact ⟨.ref { location := _, owner := true }, rfl,
        ValidPartialValueWhenInitialized.boxFull hslot hinner⟩

theorem location_var {store : ProgramStore} {env : Env}
    {x : Name} {slot : EnvSlot} :
    FullSafeAbstraction store env →
    env.slotAt x = some slot →
    LValLocationAbstraction store (.var x) slot.ty := by
  intro hsafe henv
  rcases hsafe.2 x slot henv with ⟨value, hstore, hvalid⟩
  exact ⟨.var x, StoreSlot.mk value slot.lifetime, by
      simp [ProgramStore.loc],
    by
      simpa [VariableProjection] using hstore,
    hvalid⟩

theorem location_box {store : ProgramStore} {lv : LVal} {inner : PartialTy} :
    LValLocationAbstraction store lv (.box inner) →
    LValLocationAbstraction store (.deref lv) inner := by
  intro hlocation
  rcases hlocation with ⟨source, sourceSlot, hloc, hslot, hvalid⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hvalid with
  | box htarget hinner =>
      exact ⟨_, _, by
          simp [ProgramStore.loc, hloc, hslot],
        htarget,
        hinner⟩

theorem location_boxFull {store : ProgramStore} {lv : LVal} {inner : Ty} :
    LValLocationAbstraction store lv (.ty (.box inner)) →
    LValLocationAbstraction store (.deref lv) (.ty inner) := by
  intro hlocation
  rcases hlocation with ⟨source, sourceSlot, hloc, hslot, hvalid⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hvalid with
  | boxFull htarget hinner =>
      exact ⟨_, _, by
          simp [ProgramStore.loc, hloc, hslot],
        htarget,
        hinner⟩

theorem validPartialValue_full_value {store : ProgramStore}
    {partialValue : PartialValue} {ty : Ty} :
    ValidPartialValue store partialValue (.ty ty) →
    ∃ value, partialValue = .value value ∧ ValidValue store value ty := by
  intro hvalid
  cases hvalid with
  | unit =>
      exact ⟨.unit, rfl, ValidPartialValue.unit⟩
  | int =>
      exact ⟨.int _, rfl, ValidPartialValue.int⟩
  | borrow hloc =>
      exact ⟨.ref { location := _, owner := false }, rfl,
        ValidPartialValue.borrow hloc⟩
  | boxFull hslot hinner =>
      exact ⟨.ref { location := _, owner := true }, rfl,
        ValidPartialValue.boxFull hslot hinner⟩

theorem lvalTyping_defined_location_of_safe {store : ProgramStore} {env : Env}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    FullSafeAbstraction store env →
    LValTyping env lv ty lifetime →
    LValDefinedLocationAbstraction store lv ty := by
  intro hsafe htyping
  induction htyping with
  | var hslot =>
      rename_i x slot
      rcases slot with ⟨slotTy, slotLifetime⟩
      cases slotTy with
      | ty _ =>
          simpa [LValDefinedLocationAbstraction] using
            location_var (store := store) (env := env) hsafe hslot
      | box _ =>
          simpa [LValDefinedLocationAbstraction] using
            location_var (store := store) (env := env) hsafe hslot
      | undef _ =>
          trivial
  | box hbox ih =>
      rename_i source inner lifetime
      cases inner with
      | ty _ =>
          simpa [LValDefinedLocationAbstraction] using location_box ih
      | box _ =>
          simpa [LValDefinedLocationAbstraction] using location_box ih
      | undef _ =>
          trivial
  | boxFull hbox ih =>
      simp [LValDefinedLocationAbstraction] at ih ⊢
      exact location_boxFull ih
  | borrow hborrow htarget ihBorrow ihTarget =>
      simp [LValDefinedLocationAbstraction] at ihBorrow ihTarget ⊢
      rcases ihBorrow with
        ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hvalidBorrow with
      | borrow htargetLocFromBorrow =>
          rcases ihTarget with
            ⟨targetLocation, targetSlot, htargetLoc, htargetSlot, htargetValid⟩
          have hlocationEq : targetLocation = _ :=
            Option.some.inj (htargetLoc.symm.trans htargetLocFromBorrow)
          subst hlocationEq
          exact ⟨targetLocation, targetSlot, by
              simp [ProgramStore.loc, hsourceLoc, hsourceSlot],
            htargetSlot,
            htargetValid⟩

theorem lvalTyping_defined_location_whenInitialized {store : ProgramStore}
    {env : Env} {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    SafeAbstraction store env →
    LValTyping env lv ty lifetime →
    LValDefinedLocationAbstractionWhenInitialized env store lv ty := by
  intro hsafe htyping
  induction htyping with
  | var hslot =>
      rename_i x slot
      rcases slot with ⟨slotTy, slotLifetime⟩
      cases slotTy with
      | ty _ =>
          simpa [LValDefinedLocationAbstractionWhenInitialized] using
            location_var_whenInitialized (store := store) (env := env) hsafe hslot
      | box _ =>
          simpa [LValDefinedLocationAbstractionWhenInitialized] using
            location_var_whenInitialized (store := store) (env := env) hsafe hslot
      | undef _ =>
          trivial
  | box hbox ih =>
      rename_i source inner lifetime
      cases inner with
      | ty _ =>
          simpa [LValDefinedLocationAbstractionWhenInitialized] using
            location_box_whenInitialized ih
      | box _ =>
          simpa [LValDefinedLocationAbstractionWhenInitialized] using
            location_box_whenInitialized ih
      | undef _ =>
          trivial
  | boxFull hbox ih =>
      simp [LValDefinedLocationAbstractionWhenInitialized] at ih ⊢
      exact location_boxFull_whenInitialized ih
  | borrow hborrow htarget ihBorrow ihTarget =>
      rename_i lvTarget target mutable borrowLifetime targetLifetime targetTy
      simp [LValDefinedLocationAbstractionWhenInitialized] at ihBorrow ihTarget ⊢
      rcases ihBorrow with
        ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hvalidBorrow with
      | borrowLive _hinitialized htargetLocFromBorrow =>
          rcases ihTarget with
            ⟨targetLocation, targetSlot, htargetLoc, htargetSlot, htargetValid⟩
          have hlocationEq : targetLocation = _ :=
            Option.some.inj (htargetLoc.symm.trans htargetLocFromBorrow)
          subst hlocationEq
          exact ⟨targetLocation, targetSlot, by
              simp [ProgramStore.loc, hsourceLoc, hsourceSlot],
            htargetSlot,
            htargetValid⟩
      | borrowStale hstale =>
          have hinitialized : TargetInitialized env target :=
            ⟨targetTy, targetLifetime, htarget⟩
          exact False.elim (hstale hinitialized)

def LValAllocatedLocation (store : ProgramStore) (lv : LVal) : Prop :=
  ∃ location slot, store.loc lv = some location ∧ store.slotAt location = some slot

theorem lvalTyping_allocated_location_of_safe_whenInitialized
    {store : ProgramStore} {env : Env}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    SafeAbstraction store env →
    LValTyping env lv ty lifetime →
    LValAllocatedLocation store lv := by
  intro hsafe htyping
  induction htyping with
  | var hslot =>
      rcases location_var_whenInitialized (store := store) (env := env)
          hsafe hslot with
        ⟨location, runtimeSlot, hloc, hslotRuntime, _hvalid⟩
      exact ⟨location, runtimeSlot, hloc, hslotRuntime⟩
  | box hbox _ih =>
      rcases location_box_whenInitialized
          (lvalTyping_defined_location_whenInitialized hsafe hbox) with
        ⟨location, slot, hloc, hslot, _hvalid⟩
      exact ⟨location, slot, hloc, hslot⟩
  | boxFull hbox _ih =>
      rcases location_boxFull_whenInitialized
          (lvalTyping_defined_location_whenInitialized hsafe hbox) with
        ⟨location, slot, hloc, hslot, _hvalid⟩
      exact ⟨location, slot, hloc, hslot⟩
  | borrow hborrow htarget _ihBorrow ihTarget =>
      rename_i lvTarget target mutable borrowLifetime targetLifetime targetTy
      rcases lvalTyping_defined_location_whenInitialized hsafe hborrow with
        ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hvalidBorrow with
      | borrowLive _hinitialized htargetLocFromBorrow =>
          rcases ihTarget with
            ⟨targetLocation, targetSlot, htargetLoc, htargetSlot⟩
          have hlocationEq : targetLocation = _ :=
            Option.some.inj (htargetLoc.symm.trans htargetLocFromBorrow)
          subst hlocationEq
          exact ⟨targetLocation, targetSlot, by
              simp [ProgramStore.loc, hsourceLoc, hsourceSlot],
            htargetSlot⟩
      | borrowStale hstale =>
          have hinitialized : TargetInitialized env target :=
            ⟨targetTy, targetLifetime, htarget⟩
          exact False.elim (hstale hinitialized)

theorem lvalTyping_defined_location {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    FullSafeAbstraction store env →
    LValTyping env lv ty lifetime →
    LValDefinedLocationAbstraction store lv ty := by
  intro _hwellFormed hsafe htyping
  exact lvalTyping_defined_location_of_safe hsafe htyping

theorem runtimeBorrowTarget_of_lvalTyping_safe {store : ProgramStore} {env : Env}
    {lv : LVal} {mutable : Bool} {target : LVal}
    {lifetime : Lifetime} :
    FullSafeAbstraction store env →
    LValTyping env lv (.ty (.borrow mutable target)) lifetime →
    RuntimeBorrowTarget store lv target := by
  intro hsafe htyping
  exact LValLocationAbstraction.borrow_target
    (lvalTyping_defined_location_of_safe hsafe htyping)

theorem runtimeBorrowTargetsConservative_of_safe {store : ProgramStore} {env : Env} :
    FullSafeAbstraction store env →
    RuntimeBorrowTargetsConservative store env := by
  intro hsafe _lv _mutable _target _lifetime htyping
  exact runtimeBorrowTarget_of_lvalTyping_safe hsafe htyping

theorem runtimeCoherent_selectedTarget_of_safe {store : ProgramStore} {env : Env}
    {lv : LVal} {mutable : Bool} {target : LVal} {targetTy : Ty}
    {borrowLifetime targetLifetime : Lifetime} :
    FullSafeAbstraction store env →
    LValTyping env lv (.ty (.borrow mutable target)) borrowLifetime →
    LValTyping env target (.ty targetTy) targetLifetime →
    ∃ selectedTy selectedLifetime borrowedLocation,
      LValTyping env target (.ty selectedTy) selectedLifetime ∧
        store.loc target = some borrowedLocation ∧
        RuntimeBorrowPointsTo store lv borrowedLocation := by
  intro hsafe htyping htarget
  rcases RuntimeBorrowTarget.pointsTo
      (runtimeBorrowTarget_of_lvalTyping_safe hsafe htyping) with
    ⟨borrowedLocation, htargetLoc, hpointsTo⟩
  exact ⟨targetTy, targetLifetime, borrowedLocation, htarget,
    htargetLoc, hpointsTo⟩

theorem runtimeCoherent_of_coherent_safe {store : ProgramStore} {env : Env} :
    (∀ {lv mutable target lifetime},
      LValTyping env lv (.ty (.borrow mutable target)) lifetime →
        ∃ targetTy targetLifetime,
          LValTyping env target (.ty targetTy) targetLifetime) →
    FullSafeAbstraction store env →
    RuntimeCoherent store env := by
  intro hcoherent hsafe _lv _mutable _target _lifetime htyping
  rcases hcoherent htyping with ⟨targetTy, targetLifetime, htarget⟩
  exact runtimeCoherent_selectedTarget_of_safe hsafe htyping htarget

theorem lvalTyping_allocated_location_of_safe {store : ProgramStore} {env : Env}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    FullSafeAbstraction store env →
    LValTyping env lv ty lifetime →
    LValAllocatedLocation store lv := by
  intro hsafe htyping
  have hwhen : SafeAbstraction store env := hsafe.whenInitialized
  exact lvalTyping_allocated_location_of_safe_whenInitialized hwhen htyping

theorem lvalTyping_allocated_location {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv ty lifetime →
    LValAllocatedLocation store lv := by
  intro _hwellFormed hsafe htyping
  exact lvalTyping_allocated_location_of_safe_whenInitialized hsafe htyping

theorem write_defined_of_location {store : ProgramStore} {lv : LVal}
    {ty : PartialTy} {value : PartialValue} :
    LValLocationAbstraction store lv ty →
    ∃ store', store.write lv value = some store' := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot, _hvalid⟩
  exact ⟨store.update location { slot with value := value }, by
    simp [ProgramStore.write, hloc, hslot]⟩

theorem write_defined_of_location_whenInitialized {store : ProgramStore}
    {env : Env} {lv : LVal} {ty : PartialTy} {value : PartialValue} :
    LValLocationAbstractionWhenInitialized env store lv ty →
    ∃ store', store.write lv value = some store' := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot, _hvalid⟩
  exact ⟨store.update location { slot with value := value }, by
    simp [ProgramStore.write, hloc, hslot]⟩

theorem write_eq_update_of_read {store store' : ProgramStore}
    {lv : LVal} {oldSlot : StoreSlot} {value : PartialValue} :
    store.read lv = some oldSlot →
    store.write lv value = some store' →
    ∃ location,
      store.loc lv = some location ∧
        store.slotAt location = some oldSlot ∧
        store' = store.update location { oldSlot with value := value } := by
  intro hread hwrite
  unfold ProgramStore.read at hread
  unfold ProgramStore.write at hwrite
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hread
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hread
      | some runtimeSlot =>
          have holdSlot : oldSlot = runtimeSlot := by
            simpa [hloc, hslot] using hread.symm
          have hstore' :
              store' =
                store.update location { runtimeSlot with value := value } := by
            simpa [hloc, hslot] using hwrite.symm
          subst holdSlot
          subst hstore'
          exact ⟨location, rfl, hslot, rfl⟩

theorem read_defined_of_allocated {store : ProgramStore} {lv : LVal} :
    LValAllocatedLocation store lv →
    ∃ slot, store.read lv = some slot := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot⟩
  exact ⟨slot, by simp [ProgramStore.read, hloc, hslot]⟩

theorem readPreservation_of_location {store : ProgramStore} {lv : LVal} {ty : Ty} :
    LValLocationAbstraction store lv (.ty ty) →
    ∃ value slot,
      store.read lv = some slot ∧
      slot.value = .value value ∧
      ValidValue store value ty := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot, hvalid⟩
  rcases validPartialValue_full_value hvalid with ⟨value, hvalue, hvalidValue⟩
  exact ⟨value, slot, by
      simp [ProgramStore.read, hloc, hslot],
    hvalue,
    hvalidValue⟩

theorem readPreservation_of_location_whenInitialized {store : ProgramStore}
    {env : Env} {lv : LVal} {ty : Ty} :
    LValLocationAbstractionWhenInitialized env store lv (.ty ty) →
    ∃ value slot,
      store.read lv = some slot ∧
      slot.value = .value value ∧
      ValidPartialValueWhenInitialized env store (.value value) (.ty ty) := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot, hvalid⟩
  rcases validPartialValueWhenInitialized_full_value hvalid with
    ⟨value, hvalue, hvalidValue⟩
  exact ⟨value, slot, by
      simp [ProgramStore.read, hloc, hslot],
    hvalue,
    hvalidValue⟩

theorem readPreservation_of_safe {store : ProgramStore} {env : Env}
    {lv : LVal} {ty : Ty} {lifetime : Lifetime} :
    FullSafeAbstraction store env →
    LValTyping env lv (.ty ty) lifetime →
    ∃ value slot,
      store.read lv = some slot ∧
      slot.value = .value value ∧
      ValidValue store value ty := by
  intro hsafe htyping
  exact readPreservation_of_location
    (lvalTyping_defined_location_of_safe hsafe htyping)

theorem readPreservation_of_safe_whenInitialized {store : ProgramStore}
    {env : Env} {lv : LVal} {ty : Ty} {lifetime : Lifetime} :
    SafeAbstraction store env →
    LValTyping env lv (.ty ty) lifetime →
    ∃ value slot,
      store.read lv = some slot ∧
      slot.value = .value value ∧
      ValidPartialValueWhenInitialized env store (.value value) (.ty ty) := by
  intro hsafe htyping
  exact readPreservation_of_location_whenInitialized
    (lvalTyping_defined_location_whenInitialized hsafe htyping)

theorem readPreservation {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env current →
    FullSafeAbstraction store env →
    LValTyping env lv (.ty ty) lifetime →
    ∃ value slot,
      store.read lv = some slot ∧
      slot.value = .value value ∧
      ValidValue store value ty := by
  intro _hwellFormed hsafe htyping
  exact readPreservation_of_safe hsafe htyping

end Paper
end FWRust
