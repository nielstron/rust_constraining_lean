import LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
import LwRust.Paper.Soundness.Lemma_4_11_RelaxedPreservation

/-!
# Theorem 4.12, relaxed preservation-backed safety

This module keeps the relaxed preservation/safety wrappers separate from the
legacy public soundness import path.  Import it explicitly when using the
path-sensitive relaxed invariant.
-/

namespace LwRust
namespace Paper

open Core

/--
Theorem 4.12, conditional Type and Borrow Safety via relaxed preservation.

This is the soundness-facing wrapper for the relaxed `T-If` rule.  Runtime
safety after joins is carried by `RuntimeExactEnvWitness` inside Lemma 4.11,
not by a global proof that typed terms preserve `BorrowSafeEnv`.
-/
theorem typeAndBorrowSafety_relaxed {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    RelaxedPreservationHooks →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    TerminatesAsValue store lifetime term →
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hooks hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe
    hsafe hstoreProgress htyping hterminates
  exact typeAndBorrowSafety_of_preservation hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hstoreProgress htyping
    (by
      intro finalStore finalValue hmulti
      exact Soundness.lemma_4_11_preservation hooks hsource hvalidRuntime
        hvalidStoreTyping hwellFormed hborrowSafe hsafe htyping hmulti)
    hterminates

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/--
Theorem 4.12, relaxed conditional Type and Borrow Safety.

This version uses the path-sensitive relaxed preservation invariant and does
not assume `BorrowSafeTypingPreservation`.
-/
theorem theorem_4_12_typeAndBorrowSafety_relaxed
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hooks : RelaxedPreservationHooks)
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (hstore : OperationalStoreProgress store)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hterminates : TerminatesAsValue store lifetime term) :
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty :=
  typeAndBorrowSafety_relaxed hooks hsource hvalid hstoreTyping hwellFormed
    hborrowSafe hsafe hstore htyping hterminates

end LwRust.Paper.Soundness
