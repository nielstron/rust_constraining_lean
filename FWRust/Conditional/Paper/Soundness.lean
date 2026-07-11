import FWRust.Conditional.Paper.Soundness.Lemma_4_10_Progress
import FWRust.Conditional.Paper.Soundness.Lemma_4_9_BorrowInvariance
import FWRust.Conditional.Paper.Soundness.Lemma_4_11_Preservation
import FWRust.Conditional.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
import FWRust.Conditional.Paper.Soundness.LoopReachableSafety
import FWRust.Conditional.Paper.Soundness.InitialStates
import FWRust.Conditional.Paper.Soundness.Appendix9.Lemma_9_1_SafeStrengthening
import FWRust.Conditional.Paper.Soundness.Appendix9.Lemma_9_2_TransitiveStrengthening
import FWRust.Conditional.Paper.Soundness.Appendix9.Lemma_9_3_Location
import FWRust.Conditional.Paper.Soundness.Appendix9.Corollary_9_4_ReadPreservation
import FWRust.Conditional.Paper.Soundness.Appendix9.Lemma_9_5_DropPreservation
import FWRust.Conditional.Paper.Soundness.Appendix9.Lemma_9_6_UpdatePreservation
import FWRust.Conditional.Paper.Soundness.Appendix9.Lemma_9_7_ValueTyping
import FWRust.Conditional.Paper.Soundness.Appendix9.Lemma_9_8_AliasPreservation
import FWRust.Conditional.Paper.Soundness.Appendix9.Lemma_9_9_ValuePreservation
import FWRust.Conditional.Paper.Soundness.Appendix9.Lemma_9_10_StorePreservation

/-!
# Section 4 (Soundness) — aggregator

This module is a pure aggregator.  All soundness content now lives in the
per-result lemma files (each carries the material needed to prove its result and
ends with the paper-facing statement) and in the Appendix 9 files.  Generic,
reusable typing/runtime facts live under `Soundness.Helpers`.

Section 4 is mechanized for the strengthened calculus documented in the README.
The README separates shortcuts to eliminate from intentional repairs and
strengthenings to keep.  In brief:

* move sources are lvalue-general where the paper permits them; `EnvMove` is
  intentionally `Strike`-based and therefore cannot move out through borrowed
  references, matching Definition 3.18;
* theorem interface: the lower-level safety bridge still accepts an explicit
  `TerminatesAsValue` witness for generated terms that may contain `.missing`
  or nonterminating loops, while the total Theorem 4.12 wrapper proves terminal
  existence for source terms satisfying both `Term.MissingFree` and
  `Term.LoopFree`.  The nontermination-friendly all-prefix statement is
  `reachableProgressWhenInitialized`; the local
  safety statement is `progress_runtime_step`; for states maintained by the
  stale-aware preservation invariant, use
  `theorem_4_12_typeAndBorrowStep_of_preservationInvariant`;
* repairs/strengthenings: the abstract `ProgramStore` exposes progress
  totality as `OperationalStoreProgress`, declaration and assignment carry the
  local coherence/rank facts needed by preservation, and source-initial wrappers
  derive `SourceTerm` from empty-store typability.

The lemma files form a linear chain following the paper order
(4.10 → 4.9 → 4.11 → 4.12), with the source-initial corollaries and the
Appendix 9 results layered on top.
-/
