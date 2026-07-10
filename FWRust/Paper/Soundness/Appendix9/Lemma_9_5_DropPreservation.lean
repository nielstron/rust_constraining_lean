import FWRust.Paper.Soundness.Lemma_4_11_Preservation

/-!
# Lemma 9.5 (Drop Preservation)

> Let `S` be a program store; let `Γ` be a well-formed typing environment with
> respect to a lifetime `l` where `S ∼ Γ`.  Then `drop(S, l) ∼ drop(Γ, l)`.

Status: mechanized in the form needed by the closed Section 4 proof.  Recursive
drops are framed by explicit reachability/disjointness facts from the runtime
validity package:

* `dropsLifetime_validStore`, `drops_validStore` — dropping preserves store
  validity;
* `dropsLifetime_storeOwnersAllocated`, `drops_storeOwnersAllocated_of_disjoint`
  — owner-allocation is preserved under the lifetime-disjointness side condition;
* `preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop` — the
  recursive lifetime-drop preservation used by Preservation for terminal value
  blocks;
* `safeAbstraction_seq_value_drop` — safe-abstraction preservation for
  recursive drops of non-final sequence temporaries;
* `lemma_9_5_value_drops_frame` — recursive value drops preserve a value
  abstraction when the drop avoids every reached location.
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

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

end FWRust.Paper.Soundness
