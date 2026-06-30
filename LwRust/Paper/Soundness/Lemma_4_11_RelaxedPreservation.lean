import LwRust.Paper.Soundness.Lemma_4_11_Preservation

/-!
# Borrow-safety-free preservation for relaxed `T-If`

The relaxed `T-If` rule does not preserve `BorrowSafeEnv` for the joined
approximation.  The branch-to-join part of preservation is nevertheless valid:
once the actually selected branch has produced a terminal safe state, that state
can be strengthened into the joined approximation by same-shape strengthening.

The public theorem below is the paper-facing Lemma 4.11 replacement: it assumes
only `WellFormedEnv env₁ lifetime` and `store ∼ₛ env₁`, not `BorrowSafeEnv env₁`.
It is intentionally left as the explicit borrow-safety-free preservation target
until the remaining selected-runtime invariant is proved from source execution.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/--
Transport the terminal state of the selected true branch into the relaxed
joined approximation.
-/
theorem terminalStateSafe_ite_join_left_relaxed
    {finalStore : ProgramStore} {env₃ env₄ env₅ : Env}
    {lifetime : Lifetime} {trueTy falseTy joinTy : Ty}
    {finalValue : Value}
    (hjoin : PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy))
    (henvJoin : EnvJoin env₃ env₄ env₅)
    (hsameLeft : EnvJoinSameShape env₃ env₅)
    (hsameRight : EnvJoinSameShape env₄ env₅)
    (hcoherent : Coherent env₅)
    (hlinear : Linearizable env₅)
    (hwellTrue : WellFormedEnv env₃ lifetime)
    (hwellFalse : WellFormedEnv env₄ lifetime)
    (hterminalTrue : TerminalStateSafe finalStore finalValue env₃ trueTy) :
    WellFormedEnv env₅ lifetime ∧
      TerminalStateSafe finalStore finalValue env₅ joinTy := by
  have hbranchShape :=
    EnvJoin.branches_sameShape henvJoin hsameLeft hsameRight
  have hcontained : ContainedBorrowsWellFormed env₅ :=
    containedBorrowsWellFormed_join henvJoin hsameLeft hsameRight
      hwellTrue.1 hwellFalse.1 hcoherent hlinear
  exact TerminalStateSafe.strengthen_join hcontained hcoherent hlinear
    (EnvJoin.lifetimesPreserved_left henvJoin)
    (EnvJoin.left_sameShapeStrengthening henvJoin hbranchShape)
    (PartialTyUnion.left_strengthens hjoin) hwellTrue hterminalTrue

/--
Transport the terminal state of the selected false branch into the relaxed
joined approximation.
-/
theorem terminalStateSafe_ite_join_right_relaxed
    {finalStore : ProgramStore} {env₃ env₄ env₅ : Env}
    {lifetime : Lifetime} {trueTy falseTy joinTy : Ty}
    {finalValue : Value}
    (hjoin : PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy))
    (henvJoin : EnvJoin env₃ env₄ env₅)
    (hsameLeft : EnvJoinSameShape env₃ env₅)
    (hsameRight : EnvJoinSameShape env₄ env₅)
    (hcoherent : Coherent env₅)
    (hlinear : Linearizable env₅)
    (hwellTrue : WellFormedEnv env₃ lifetime)
    (hwellFalse : WellFormedEnv env₄ lifetime)
    (hterminalFalse : TerminalStateSafe finalStore finalValue env₄ falseTy) :
    WellFormedEnv env₅ lifetime ∧
      TerminalStateSafe finalStore finalValue env₅ joinTy := by
  have hbranchShape :=
    EnvJoin.branches_sameShape henvJoin hsameLeft hsameRight
  have hcontained : ContainedBorrowsWellFormed env₅ :=
    containedBorrowsWellFormed_join henvJoin hsameLeft hsameRight
      hwellTrue.1 hwellFalse.1 hcoherent hlinear
  exact TerminalStateSafe.strengthen_join hcontained hcoherent hlinear
    (EnvJoin.lifetimesPreserved_right henvJoin)
    (EnvJoin.right_sameShapeStrengthening henvJoin hbranchShape)
    (PartialTyUnion.right_strengthens hjoin) hwellFalse hterminalFalse

/--
Borrow-safety-free preservation target for the relaxed typing rules.

This is the paper-facing statement: no
`RelaxedPreservationHooks`, no `BorrowSafeEnv env₁`, and no hidden replacement for
global borrow safety in the theorem assumptions.
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
    TerminalStateSafe finalStore finalValue env₂ ty := by
  exact preservation_bounded_borrowSafeFree term.size (Nat.le_refl _)
    hsource hvalid hstoreTyping hwellFormed hsafe htyping hmulti

end LwRust.Paper.Soundness
