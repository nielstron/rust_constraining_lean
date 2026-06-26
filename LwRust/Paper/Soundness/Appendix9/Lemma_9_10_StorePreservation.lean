import LwRust.Paper.Soundness.Lemma_4_11_Preservation

/-!
# Lemma 9.10 (Store Preservation)

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; … then `S₂ ∼ Γ₂`
> (the final store is safely abstracted by the result environment).

Status: mechanized through Preservation (Lemma 4.11).  This is the
`finalStore ∼ₛ env₂` conjunct of `TerminalStateSafe`.  Mechanized support:

* box/declare base cases — `preservation_box_context_terminal_multistep_runtime`,
  `preservation_declare_redex_runtime_of_validValue` (uses Lemma 9.7);
* assign — `storePreservation_assign_var_*_of_preserved` (uses Lemma 9.6) and
  `preservation_assign_var_envShape_step_runtime_of_frames`, which derives the
  post-write validity premises from concrete reachability frame conditions;
* direct-variable move — `preservation_move_var_step_runtime_of_frames`, which
  derives the moved value and surviving slots from the same concrete frame
  condition shape;
* block `R-BlockB` — via Lemma 9.5
  (`preservation_blockB_value_multistep_runtime_of_runtimeDrop`) for terminal
  value blocks.

The move, assignment, sequence-drop, and block-drop cases are discharged in
`preservation`; the theorem below records the full store-preservation projection.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/--
Appendix 9.10, Store Preservation, as the safe-abstraction projection of
Lemma 4.11.
-/
theorem lemma_9_10_storePreservation
    {store finalStore : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm term →
      ValidRuntimeState store term →
      ValidStoreTyping store term typing →
      WellFormedEnv env₁ lifetime →
      BorrowSafeEnv env₁ →
      store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    finalStore ∼ₛ env₂ := by
    intro hsource hvalid hstoreTyping hwellFormed hborrowSafe hsafe htyping hmulti
    exact (preservation hsource hvalid hstoreTyping
      hwellFormed hborrowSafe hsafe htyping hmulti).2.1

/--
Appendix 9.10, direct-variable assignment store preservation under the concrete
frame conditions used to keep the RHS and unaffected variables valid after the
runtime write to `x` and the subsequent cleanup drop of the overwritten value.
-/
theorem lemma_9_10_assign_var_envShape_frame
    {store storeAfterWrite store' : ProgramStore} {env env' : Env}
    {lifetime : Lifetime} {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    (envSlot.ty = .ty .unit ∨ envSlot.ty = .ty .int ∨ envSlot.ty = .ty .bool ∨
      (∃ inner, envSlot.ty = .undef inner) ∨
      ∃ mutable targets pointee, envSlot.ty = .ty (.borrow mutable targets pointee)) →
    ValidValue store value ty →
    store.read (.var x) = some oldSlot →
    store.write (.var x) (.value value) = some storeAfterWrite →
    Drops storeAfterWrite [oldSlot.value] store' →
    (∀ ℓ, RuntimeFrame.Reaches store (.value value) (.ty ty) ℓ →
      ℓ ≠ VariableProjection x) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ ℓ, RuntimeFrame.Reaches store oldValue otherEnvSlot.ty ℓ →
        ℓ ≠ VariableProjection x) →
    ValidRuntimeState store' (.val .unit) ∧ store' ∼ₛ env' ∧
      ValidValue store' .unit .unit :=
  preservation_assign_var_envShape_step_runtime_of_frames (lifetime := lifetime)

/--
Appendix 9.10, direct-variable move store preservation under concrete
store-update frame conditions for the moved value and unaffected variables.
-/
theorem lemma_9_10_move_var_frame {store store' : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {current lifetime valueLifetime : Lifetime}
    {x : Name} {value : Value} {ty : Ty} :
    WellFormedEnv env₁ current →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.move (.var x)) →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    TermTyping env₁ typing lifetime (.move (.var x)) ty env₂ →
    Step store lifetime (.move (.var x)) store' (.val value) →
    (∀ ℓ, RuntimeFrame.Reaches store (.value value) (.ty ty) ℓ →
      ℓ ≠ VariableProjection x) →
    (∀ y envSlot oldValue,
      y ≠ x →
      env₁.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ∀ ℓ, RuntimeFrame.Reaches store oldValue envSlot.ty ℓ →
        ℓ ≠ VariableProjection x) →
    ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env₂ ∧
      ValidValue store' value ty :=
  preservation_move_var_step_runtime_of_frames

end LwRust.Paper.Soundness
