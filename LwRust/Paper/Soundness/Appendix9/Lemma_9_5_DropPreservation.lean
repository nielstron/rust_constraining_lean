import LwRust.Paper.Soundness

/-!
# Lemma 9.5 (Drop Preservation)

> Let `S` be a program store; let `Γ` be a well-formed typing environment with
> respect to a lifetime `l` where `S ∼ Γ`.  Then `drop(S, l) ∼ drop(Γ, l)`.

Status: **in progress** — this is one of the runtime preservation facts behind
`RuntimePreservationObligations.block` (the `R-BlockB` lifetime drop).  The
store-side groundwork is mechanized:

* `dropsLifetime_validStore`, `drops_validStore` — dropping preserves store
  validity;
* `dropsLifetime_storeOwnersAllocated`, `drops_storeOwnersAllocated_of_disjoint`
  — owner-allocation is preserved under the lifetime-disjointness side condition;
* `preservation_blockB_value_multistep_runtime_of_drop_preserved`,
  `preservation_blockB_value_multistep_runtime_no_slots` — the safe-abstraction
  half, currently taking the per-variable drop-preservation facts as hypotheses.

The remaining work is to discharge those `∀ x, … survives the drop` hypotheses
into a single `drop(S, l) ∼ drop(Γ, l)` statement.
-/
