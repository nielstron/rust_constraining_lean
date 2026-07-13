import FWRust.Paper.Soundness.Lemma_4_10_Progress
import FWRust.Paper.Soundness.Lemma_4_9_BorrowInvariance
import FWRust.Paper.Soundness.Lemma_4_11_Preservation
import FWRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
import FWRust.Paper.Soundness.InitialStates
import FWRust.Paper.Soundness.Corollary_4_14_BorrowSafety
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
# Section 4 (Soundness) — aggregator

This module is a pure aggregator.  All soundness content now lives in the
per-result lemma files (each carries the material needed to prove its result and
ends with the paper-facing statement) and in the Appendix 9 files.  Generic,
reusable typing/runtime facts live under `Soundness.Helpers`.

Section 4 is mechanized for the strengthened calculus documented in the README.
In brief:

* move sources are lvalue-general where the paper permits them; `EnvMove` is
  intentionally `Strike`-based and therefore cannot move out through borrowed
  references, matching Definition 3.18;
* safe-abstraction interface: the paper's sole Definition 4.7 relation is
  `FullSafeAbstraction` (notation `∼`), and all paper-facing statements use it;
* theorem interface: the local safety statement is `progress_runtime_step`;
* repairs/strengthenings: the abstract `ProgramStore` exposes progress
  totality as `OperationalStoreProgress`, declaration and assignment carry the
  local coherence/rank facts needed by preservation, and source-initial wrappers
  derive `SourceTerm` from empty-store typability.

The lemma files form a linear chain following the paper order
(4.10 → 4.9 → 4.11 → 4.12 → 4.14), with the source-initial corollaries and the
Appendix 9 results layered on top.
-/
