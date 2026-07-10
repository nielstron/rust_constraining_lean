import FWRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Lemma 9.6 (Update Preservation)

> Let `S` be a program store; let `Γ` be a well-formed typing environment …
> writing a well-typed value through an lval preserves the safe abstraction:
> if `S ∼ Γ` and the assignment `w = v` is well typed with `write₀(Γ, w, T) = Γ₂`
> and `S ⊢ v ∼ T`, then `write(S, w, v) ∼ Γ₂`.

Status: the static and runtime parts are integrated into the assignment case of
the closed Preservation proof.  Static preservation transports well-formedness,
borrow safety, and linearizability across the single-target `EnvWrite` relation.
Runtime preservation follows the selected write chain, proves the necessary
reachability frame conditions, and preserves the safe abstraction across the
store write and cleanup drop.  The reusable assignment lemmas live in
`Lemma_4_11_Preservation` and `Soundness.Helpers.ValuePreservation`.

The runtime statement must use the corrected assignment order implemented by
`Step.assign`: read the overwritten slot, write the new value, then drop the
overwritten old value from the post-write store.  The printed appendix proof's
drop/write order is not the theorem being mechanized here.
-/
