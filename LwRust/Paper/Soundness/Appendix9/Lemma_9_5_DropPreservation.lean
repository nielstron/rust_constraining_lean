import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety

/-!
# Lemma 9.5 (Drop Preservation)

> Let `S` be a program store; let `Γ` be a well-formed typing environment with
> respect to a lifetime `l` where `S ∼ Γ`.  Then `drop(S, l) ∼ drop(Γ, l)`.

Status: **partial appendix support** — the full paper statement for arbitrary
recursive drops is not used by the closed Section 4 proof.  Preservation uses
the strengthened drop-safe block-local rule, whose required `R-BlockB`
safe-abstraction half for terminal value blocks is mechanized here:

* `dropsLifetime_validStore`, `drops_validStore` — dropping preserves store
  validity;
* `dropsLifetime_storeOwnersAllocated`, `drops_storeOwnersAllocated_of_disjoint`
  — owner-allocation is preserved under the lifetime-disjointness side condition;
* `preservation_blockB_value_multistep_runtime_of_envDropSafe` — the
  safe-abstraction half used by Preservation for terminal value blocks;
* `lemma_9_5_value_drops_frame` — recursive value drops preserve a value
  abstraction when the drop avoids every reached location.

The unrestricted Appendix 9.5 theorem would require a full recursive
drop-preservation argument for arbitrary owner values, which this mechanization
avoids by strengthening `T-Block`.
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
