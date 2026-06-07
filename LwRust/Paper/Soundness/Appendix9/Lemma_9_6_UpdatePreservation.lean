import LwRust.Paper.Soundness

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
* Runtime (safe abstraction preserved by the store `write`): mechanized as
  `storePreservation_assign_var_*_of_preserved` and the redex lemmas
  `preservation_assign_var_envShape_step_runtime_of_preserved`, currently taking
  the per-variable update-preservation facts (`∀ y ≠ x, validity survives the
  write`) as hypotheses; this is the `RuntimePreservationObligations.assign`
  case.
-/
