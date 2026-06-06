import LwRust.Paper.Soundness

/-!
# Lemma 9.9 (Value Preservation)

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; … then the final
> value is abstracted by the result type: `S₂ ▷ v ∼ T`.

Status: **in progress** — this is the `ValidValue finalStore finalValue ty`
conjunct of `TerminalStateSafe`, established by Preservation (Lemma 4.11).  The
base cases (`R-Copy`/`R-Move` via Corollary 9.4, `&[mut] w` via Lemma 9.3,
`box`/`declare` via the multistep fragments
`preservation_box_context_terminal_multistep_runtime`,
`preservation_declare_multistep_runtime`) are mechanized; the move/assign/block
cases are the corresponding `RuntimePreservationObligations` fields.
-/
