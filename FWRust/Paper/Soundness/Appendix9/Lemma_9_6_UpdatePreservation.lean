import FWRust.Paper.Soundness.Lemma_4_11_Preservation

/-!
# Lemma 9.6 (Update Preservation)

> Let `S` be a program store; let `Γ` be a well-formed typing environment …
> writing a well-typed value through an lval preserves the safe abstraction:
> if `S ∼ Γ` and the assignment `w = v` is well typed with `write₀(Γ, w, T) = Γ₂`
> and `S ⊢ v ∼ T`, then `write(S, w, v) ∼ Γ₂`.

The operational theorem below exposes the corresponding conclusion for a
single assignment step whose evaluated RHS is a full value.  Static
preservation transports well-formedness, borrow safety, and linearizability
across the single-target `EnvWrite` relation.
Runtime preservation follows the selected write chain, proves the necessary
reachability frame conditions, and preserves the safe abstraction across the
store write and cleanup drop.  The reusable assignment lemmas live in
`Lemma_4_11_Preservation` and `Soundness.Helpers.ValuePreservation`.

The runtime statement must use the corrected assignment order implemented by
`Step.assign`: read the overwritten slot, write the new value, then drop the
overwritten old value from the post-write store.  The printed appendix proof's
drop/write order is not the theorem being mechanized here.
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

/--
An Appendix 9.6 update-preservation analogue in the operational one-step form
induced by the mechanised assignment rule.  It specializes the new assignment
value and RHS type to full `Value`/`Ty` (the overwritten type remains partial),
and packages the independent assignment-specific preservation theorem used by
the closed proof; it is not a
projection from the global Lemma 4.11 wrapper.  The additional premises make
explicit the static/runtime invariants used to justify the corrected
write-then-drop implementation.
-/
theorem lemma_9_6_updatePreservation_oneStep_of_runtime_invariants
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {lifetime targetLifetime : Lifetime} {lv : LVal}
    {oldTy : PartialTy} {value : Value} {rhsTy : Ty}
    (hvalid : ValidRuntimeState store (.assign lv (.val value)))
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (htySafe : TyBorrowSafeAgainstEnv env₁ rhsTy)
    (hsafe : store ≈ₛ env₁)
    (hlv : LValTyping env₁ lv oldTy targetLifetime)
    (hshape : ShapeCompatible env₁ oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env₁ rhsTy targetLifetime)
    (hwrite : EnvWrite env₁ lv rhsTy env₂)
    (hnotWrite : ¬ WriteProhibited env₂ lv)
    (hlinear : Linearizable env₁)
    (hvalidValue : ValidValue store value rhsTy)
    (hstep : Step store lifetime (.assign lv (.val value))
      finalStore (.val .unit)) :
    FullSafeAbstraction finalStore env₂ := by
  exact (preservation_assign_step_runtime_of_linearized
    hwellFormed hborrowSafe htySafe hsafe hvalid hlv hshape hwellTy
    hwrite hnotWrite hlinear hvalidValue hstep).2.1

end FWRust.Paper.Soundness
