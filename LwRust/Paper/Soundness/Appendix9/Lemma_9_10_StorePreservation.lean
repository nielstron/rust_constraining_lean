import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety

/-!
# Lemma 9.10 (Store Preservation)

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; … then `S₂ ∼ Γ₂`
> (the final store is safely abstracted by the result environment).

Status: **in progress** — the `finalStore ∼ₛ env₂` conjunct of
`TerminalStateSafe`, established by Preservation (Lemma 4.11).  Mechanized
support:

* box/declare base cases — `preservation_box_context_terminal_multistep_runtime`,
  `preservation_declare_redex_runtime_of_validValue` (uses Lemma 9.7);
* assign — `storePreservation_assign_var_*_of_preserved` (uses Lemma 9.6) and
  `preservation_assign_var_envShape_step_runtime_of_frames`, which derives the
  post-write validity premises from concrete reachability frame conditions;
* direct-variable move — `preservation_move_var_step_runtime_of_frames`, which
  derives the moved value and surviving slots from the same concrete frame
  condition shape;
* block `R-BlockB` — via Lemma 9.5 (`preservation_blockB_value_*`).

The move/assign/block cases are the `RuntimePreservationObligations` fields; the
copy/borrow cases are already discharged in `preservation`.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/--
Appendix 9.10, direct-variable assignment store preservation under the concrete
frame conditions used to keep the RHS and unaffected variables valid after the
runtime write to `x`.
-/
theorem lemma_9_10_assign_var_envShape_frame
    {store storeAfterDrop store' : ProgramStore} {env env' : Env}
    {lifetime : Lifetime} {x : Name} {oldSlot : StoreSlot} {envSlot : EnvSlot}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    (envSlot.ty = .ty .unit ∨ envSlot.ty = .ty .int ∨
      (∃ inner, envSlot.ty = .undef inner) ∨
      ∃ mutable targets, envSlot.ty = .ty (.borrow mutable targets)) →
    ValidValue store value ty →
    store.read (.var x) = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write (.var x) (.value value) = some store' →
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
