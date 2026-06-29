import LwRust.Extractor.RelaxedPreservation

/-!
# Lemma 4.11, relaxed preservation wrapper

The relaxed `T-If` rule does not preserve `BorrowSafeEnv` for the joined
approximation.  Preservation therefore carries runtime safety through
`RuntimeExactEnvWitness`: the actual runtime path has an exact borrow-safe
environment that strengthens to the static approximation.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/--
Path-sensitive Lemma 4.11.

The result exposes the relaxed invariant directly.  The only additional
premise is `RelaxedPreservationHooks`, the explicit frontier for
non-control-flow exact-transport obligations.  There is no global
`BorrowSafeTypingPreservation` assumption and no borrow-safety premise for the
output approximation.
-/
theorem lemma_4_11_preservation_pathSensitive
    (hooks : RelaxedPreservationHooks)
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    WellFormedEnv env₂ lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue env₂ ty := by
  exact relaxed_preservation_with_hooks_of_termTyping hooks hsource hvalid
    hstoreTyping hwellFormed
    (RuntimeExactEnvWitness.refl hwellFormed hborrowSafe hsafe)
    htyping hmulti

/--
Lemma 4.11, ordinary terminal-safety projection of the path-sensitive theorem.

This is the paper-facing preservation conclusion.  Its proof uses the relaxed
invariant above rather than restoring `BorrowSafeEnv` for the joined
approximation.
-/
theorem lemma_4_11_preservation
    (hooks : RelaxedPreservationHooks)
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    TerminalStateSafe finalStore finalValue env₂ ty :=
  (lemma_4_11_preservation_pathSensitive hooks hsource hvalid hstoreTyping
    hwellFormed hborrowSafe hsafe htyping hmulti).2.1

end LwRust.Paper.Soundness
