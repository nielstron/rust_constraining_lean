import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety

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
* `lemma_9_5_value_drops_frame` — recursive value drops preserve a value
  abstraction when the drop avoids every reached location.

The remaining work is to discharge those `∀ x, … survives the drop` hypotheses
into a single `drop(S, l) ∼ drop(Γ, l)` statement.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/--
Appendix 9.5 support: recursive drops preserve a value abstraction when every
location inspected by that abstraction is avoided by the drop derivation.
-/
theorem lemma_9_5_value_drops_frame {store store' : ProgramStore}
    {values : List PartialValue} {value : Value} {ty : Ty} :
    Drops store values store' →
    ValidValue store value ty →
    (∀ location, RuntimeFrame.Reaches store (.value value) (.ty ty) location →
      DropsAvoids store values location) →
    ValidValue store' value ty :=
  RuntimeFrame.validValue_drops_of_avoids_reaches

end LwRust.Paper.Soundness
