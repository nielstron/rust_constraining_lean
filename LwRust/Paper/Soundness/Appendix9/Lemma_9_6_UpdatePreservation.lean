import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety

/-!
# Lemma 9.6 (Update Preservation)

> Let `S` be a program store; let `Γ` be a well-formed typing environment …
> writing a well-typed value through an lval preserves the safe abstraction:
> if `S ∼ Γ` and the assignment `w = v` is well typed with `write₀(Γ, w, T) = Γ₂`
> and `S ⊢ v ∼ T`, then `write(S, w, v) ∼ Γ₂`.

Status: split into a **static** half and a **runtime** half.

* Static (Definition 4.8 well-formedness preserved by `write₀`): mechanized by
  the explicit-obligation assignment lemmas in `LwRust.Paper.Soundness`, gated on
  `UpdateBorrowInvariantObligations` plus the rule-carried RHS-rank and
  write-coherence premises.  This is the `T-Assign` case of Lemma 4.9.
* Runtime (safe abstraction preserved by the store `write`): mechanized for
  direct variable assignment, the one-step owned-dereference case used by owner
  replacement, and the direct mutable-reference fan-out case `*p := v`.  The
  remaining Lemma 4.11 holes are the recursive Appendix 9.6 cases: owner-chain
  writes below more than one box, and nested mutable-borrow fan-out where the
  runtime reference selects one target while recursive `write_k` calls join all
  possible target environments.

The runtime statement must use the corrected assignment order implemented by
`Step.assign`: read the overwritten slot, write the new value, then drop the
overwritten old value from the post-write store.  The printed appendix proof's
drop/write order is not the theorem being mechanized here.
-/
