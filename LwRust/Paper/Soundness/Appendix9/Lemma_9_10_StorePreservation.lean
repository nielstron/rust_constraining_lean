import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety

/-!
# Lemma 9.10 (Store Preservation)

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; … then `S₂ ∼ Γ₂`
> (the final store is safely abstracted by the result environment).

Status: **in progress** — the `finalStore ∼ₛ env₂` conjunct of
`TerminalStateSafe`, established by Preservation (Lemma 4.11).  Mechanized
support:

* box/declare base cases — `preservation_box_context_terminal_multistep_runtime`,
  `preservation_declare_redex_runtime_of_validValue` (uses Lemma 9.7);
* assign — `storePreservation_assign_var_*_of_preserved` (uses Lemma 9.6);
* block `R-BlockB` — via Lemma 9.5 (`preservation_blockB_value_*`).

The move/assign/block cases are the `RuntimePreservationObligations` fields; the
copy/borrow cases are already discharged in `preservation`.
-/
