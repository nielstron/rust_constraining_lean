import LwRust.Paper.Soundness.Lemma_4_10_Progress
import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance
import LwRust.Paper.Soundness.Lemma_4_11_Preservation
import LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety
import LwRust.Paper.Soundness.InitialStates
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
# Section 4 (Soundness) — aggregator

This module is a pure aggregator.  All soundness content now lives in the
per-result lemma files (each carries the material needed to prove its result and
ends with the paper-facing statement) and in the Appendix 9 files.  Generic,
reusable typing/runtime facts live under `Soundness.Helpers`.

Section 4 is mechanized for the strengthened calculus with the following
documented deviations from the paper rules:

* the abstract `ProgramStore` exposes progress totality as
  `OperationalStoreProgress`; concrete finite stores instantiate it;
* the current Theorem 4.12 wrapper is conditional terminal safety: it exposes
  `TerminatesAsValue` instead of proving the paper's terminal-existence
  conclusion.  The nontermination-friendly local safety statement is
  `progress_runtime_step`, which says a well-typed non-terminal state can step;
* move/borrow/assignment source redexes are restricted to variable lvalues;
* declaration and assignment typing carry the local coherence/rank facts needed
  by the `lw_rust_followup` linearizability argument;
* block/sequence typing is strengthened to singleton/drop-safe blocks and
  non-owning non-final sequence temporaries, avoiding an unproved general
  recursive drop-preservation theorem.

The lemma files form a linear chain following the paper order
(4.10 → 4.9 → 4.11 → 4.12 → 4.14), with the source-initial corollaries and the
Appendix 9 results layered on top.
-/
