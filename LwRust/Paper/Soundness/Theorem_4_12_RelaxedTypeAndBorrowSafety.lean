import LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
import LwRust.Paper.Soundness.Lemma_4_11_RelaxedPreservation

/-!
# Relaxed safety boundary

The previous relaxed Theorem 4.12 wrapper depended on a hook-based preservation
statement that still assumed `BorrowSafeEnv` at the input.  That is not a valid
soundness theorem for the relaxed `T-If` rule, because an input environment may
itself be a joined approximation.

This module is the explicit relaxed boundary: it derives the conditional
Theorem 4.12 wrapper from the checked borrow-safety-free preservation theorem in
`Lemma_4_11_RelaxedPreservation`.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

theorem theorem_4_12_relaxed_typeAndBorrowSafety
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    TerminatesAsValue store lifetime term →
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hsafe
    hstoreProgress htyping hterminates
  exact typeAndBorrowSafety_of_preservation hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hstoreProgress htyping
    (by
      intro finalStore finalValue hmulti
      exact lemma_4_11_preservation hsource hvalidRuntime hvalidStoreTyping
        hwellFormed hsafe htyping hmulti)
    hterminates

end LwRust.Paper.Soundness
