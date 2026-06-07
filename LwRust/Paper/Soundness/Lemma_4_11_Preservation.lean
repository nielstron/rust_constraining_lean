import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
# Lemma 4.11 (Preservation)

Paper statement (Section 4.4):

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; let `σ` be a
> store typing where `S₁ ▷ t ⊢ σ`; let `Γ₁` be a well-formed typing environment
> with respect to a lifetime `l` where `S₁ ∼ Γ₁`; let `Γ₂` be a typing
> environment; and let `T` be a type.  If `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂` and
> `⟨S₁ ▷ t ⟶* S₂ ▷ v⟩^l`, then `S₂ ▷ v` remains valid where `S₂ ∼ Γ₂` and
> `S₂ ▷ v ∼ T`.

Status: unconditional as a paper-facing statement, but it depends on explicit
sorried runtime lemmas through `runtimePreservationObligations_from_sorries`.
The assignment case is handled by the global Preservation induction and leaves
only the final assignment-redex/update obligation.  The structural cases
(value/copy/borrow/box/declare) are already proven inside `preservation`; block
still needs the term-list/block-step preservation argument.
-/

namespace LwRust
namespace Paper

open Core


theorem terminalStateSafe_assign_unit_of_postconditions {store : ProgramStore}
    {env : Env} :
    ValidRuntimeState store (.val .unit) →
    store ∼ₛ env →
    TerminalStateSafe store .unit env .unit := by
  intro hvalidRuntime hsafe
  exact ⟨hvalidRuntime, hsafe, ValidPartialValue.unit⟩

/-- Remaining explicit runtime preservation obligation for moves. -/
theorem runtimePreservation_move
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {ty : Ty} {finalValue : Value} :
    ValidRuntimeState store (.move lv) →
    ValidStoreTyping store (.move lv) typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.move lv) ty env₂ →
    MultiStep store lifetime (.move lv) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  sorry

/-- Remaining explicit runtime preservation obligation for assignment redexes.

The global Preservation induction handles RHS evaluation and passes the resulting
valid runtime state, safe abstraction, and value abstraction into this local
redex/update obligation.  This is not a pure typing obligation: the redex proof
must establish post-step runtime validity and `finalStore ∼ₛ env₃` after the
drop/write sequence, then package them with
`terminalStateSafe_assign_unit_of_postconditions`.
-/
theorem runtimePreservation_assign
    {midStore finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {value finalValue : Value} :
    LValTyping env₁ lhs oldTy targetLifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ValidRuntimeState midStore (.assign lhs (.val value)) →
    midStore ∼ₛ env₂ →
    ValidValue midStore value rhsTy →
    Step midStore lifetime (.assign lhs (.val value)) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₃ .unit := by
  sorry

/-- Remaining explicit runtime preservation obligation for blocks. -/
theorem runtimePreservation_block
    {store finalStore : ProgramStore} {env₁ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} {finalValue : Value} :
    ValidRuntimeState store (.block blockLifetime terms) →
    ValidStoreTyping store (.block blockLifetime terms) typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.block blockLifetime terms) ty env₃ →
    MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₃ ty := by
  sorry

/-- Concrete runtime-preservation package assembled from explicit sorried lemmas. -/
theorem runtimePreservationObligations_from_sorries :
    RuntimePreservationObligations where
  move := runtimePreservation_move
  assign := runtimePreservation_assign
  block := runtimePreservation_block

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Lemma 4.11, Preservation. -/
theorem lemma_4_11_preservation
    {store finalStore : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {finalValue : Value}
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    TerminalStateSafe finalStore finalValue env₂ ty :=
  preservation runtimePreservationObligations_from_sorries hvalid hstoreTyping
    hwellFormed hsafe htyping hmulti

end LwRust.Paper.Soundness
