import FWRust.Paper.Soundness.Definitions
import FWRust.Paper.Soundness.Lemma_4_9_BorrowInvariance
import FWRust.Paper.Soundness.Lemma_4_10_Progress
import FWRust.Paper.Soundness.Lemma_4_11_Preservation
import FWRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
import FWRust.Paper.Soundness.Appendix9.Lemma_9_1_SafeStrengthening
import FWRust.Paper.Soundness.Appendix9.Lemma_9_2_TransitiveStrengthening
import FWRust.Paper.Soundness.Appendix9.Lemma_9_3_Location
import FWRust.Paper.Soundness.Appendix9.Corollary_9_4_ReadPreservation
import FWRust.Paper.Soundness.Appendix9.Lemma_9_5_DropPreservation
import FWRust.Paper.Soundness.Appendix9.Lemma_9_6_UpdatePreservation
import FWRust.Paper.Soundness.Appendix9.Lemma_9_7_ValueTyping
import FWRust.Paper.Soundness.Appendix9.Lemma_9_8_AliasPreservation
import FWRust.Paper.Soundness.Appendix9.Lemma_9_9_ValuePreservation
import FWRust.Paper.Soundness.Appendix9.Lemma_9_10_StorePreservation

/-!
# Section 4 (Soundness) + Appendix 9, organized by result

One file per core lemma/theorem of `fw_rust.pdf` Section 4 and Appendix 9.  Each
file states the paper result, wires it to the mechanization in
`FWRust.Paper.Soundness`, and records its status.  The README documents the
intentional repairs and strengthenings relative to the paper.  Move sources are
lvalue-general where the paper permits them; moves
through borrowed references are intentionally untypeable because `EnvMove`
follows the paper's `Strike` definition.  Theorem 4.12 proves terminal safety
and terminal existence for source terms in the core calculus.  Lemma 4.10
provides the local progress theorem used for nontermination-friendly safety
statements.

## Section 4

* `Definitions`                          — Def 4.1–4.8, 4.13
* `Lemma_4_9_BorrowInvariance`           — Lemma 4.9    (core wrapper proven)
* `Lemma_4_10_Progress`                  — Lemma 4.10   (proven)
* `Lemma_4_11_Preservation`              — Lemma 4.11   (general source-continuation wrapper)
* `Theorem_4_12_TypeAndBorrowSafety`     — Theorem 4.12 (total for source terms)
* `InitialStates`                        — source-initial wrappers, deriving `SourceTerm` from typability

## Appendix 9

* `Appendix9.Lemma_9_1_SafeStrengthening`       — proven
* `Appendix9.Lemma_9_2_TransitiveStrengthening` — proven
* `Appendix9.Lemma_9_3_Location`                — proven (location availability)
* `Appendix9.Corollary_9_4_ReadPreservation`    — proven
* `Appendix9.Lemma_9_5_DropPreservation`        — framed support used by the closed Section 4 proof
* `Appendix9.Lemma_9_6_UpdatePreservation`      — static/runtime support used by assignment preservation
* `Appendix9.Lemma_9_7_ValueTyping`             — proven
* `Appendix9.Lemma_9_8_AliasPreservation`       — mechanized for structural fragments
* `Appendix9.Lemma_9_9_ValuePreservation`       — proven as Preservation value projection
* `Appendix9.Lemma_9_10_StorePreservation`      — Preservation store projection
-/
