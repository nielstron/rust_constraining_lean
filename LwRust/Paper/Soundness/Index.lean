import LwRust.Paper.Soundness.Definitions
import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance
import LwRust.Paper.Soundness.Lemma_4_10_Progress
import LwRust.Paper.Soundness.Lemma_4_11_Preservation
import LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety
import LwRust.Paper.Soundness.Appendix9.Lemma_9_1_SafeStrengthening
import LwRust.Paper.Soundness.Appendix9.Lemma_9_2_TransitiveStrengthening
import LwRust.Paper.Soundness.Appendix9.Lemma_9_3_Location
import LwRust.Paper.Soundness.Appendix9.Corollary_9_4_ReadPreservation
import LwRust.Paper.Soundness.Appendix9.Lemma_9_5_DropPreservation
import LwRust.Paper.Soundness.Appendix9.Lemma_9_6_UpdatePreservation
import LwRust.Paper.Soundness.Appendix9.Lemma_9_7_ValueTyping
import LwRust.Paper.Soundness.Appendix9.Lemma_9_8_AliasPreservation
import LwRust.Paper.Soundness.Appendix9.Lemma_9_9_ValuePreservation
import LwRust.Paper.Soundness.Appendix9.Lemma_9_10_StorePreservation

/-!
# Section 4 (Soundness) + Appendix 9, organized by result

One file per core lemma/theorem of `lw_rust.pdf` Section 4 and Appendix 9.  Each
file states the paper result, wires it to the mechanization in
`LwRust.Paper.Soundness`, and records its status.  The mechanization uses the
documented strengthened typing system: variable-only source redexes for
move/borrow, variable-only stored borrow targets, dereference-capable assignment
via `EnvWrite`, rule-carried assignment/declaration coherence facts, and
singleton/drop-safe block sequencing.  Theorem 4.12 is currently the conditional
terminal-safety form; Lemma 4.10 provides the local progress theorem used for
nontermination-friendly safety statements.

## Section 4

* `Definitions`                          — Def 4.1–4.8, 4.13
* `Lemma_4_9_BorrowInvariance`           — Lemma 4.9    (core wrapper proven)
* `Lemma_4_10_Progress`                  — Lemma 4.10   (proven)
* `Lemma_4_11_Preservation`              — Lemma 4.11   (owner-overwrite assignment proof debt remains)
* `Theorem_4_12_TypeAndBorrowSafety`     — Theorem 4.12 (conditional on termination)
* `Corollary_4_14_BorrowSafety`          — Cor 4.14     (core wrapper proven)

## Appendix 9

* `Appendix9.Lemma_9_1_SafeStrengthening`       — proven
* `Appendix9.Lemma_9_2_TransitiveStrengthening` — proven
* `Appendix9.Lemma_9_3_Location`                — proven (location availability)
* `Appendix9.Corollary_9_4_ReadPreservation`    — proven
* `Appendix9.Lemma_9_5_DropPreservation`        — partial; Section 4 uses strengthened block rule
* `Appendix9.Lemma_9_6_UpdatePreservation`      — split support; Section 4 uses rule-carried update facts
* `Appendix9.Lemma_9_7_ValueTyping`             — proven
* `Appendix9.Lemma_9_8_AliasPreservation`       — mechanized for structural fragments
* `Appendix9.Lemma_9_9_ValuePreservation`       — proven as Preservation value projection
* `Appendix9.Lemma_9_10_StorePreservation`      — Preservation store projection; inherits assignment proof debt
-/
