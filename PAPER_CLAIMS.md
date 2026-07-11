# Paper-to-Lean claim map

This file maps claims from Pearce (2021) to declarations in the canonical FW
Rust formalization.  The native while-loop results are listed separately
because they extend the paper.

## Generative-compiler framework

| Claim | Lean declaration |
| --- | --- |
| Definition 3.1, sealor completeness | [`ConservativeSealor.Conservative`](FWRust/Sealor/Definitions.lean) |
| Definition 3.1, prefixes admitting a valid continuation | [`ConservativeSealor.Completable`](FWRust/Sealor/Definitions.lean) |
| Definition 3.1, selective soundness | [`ConservativeSealor.SealorSoundOn`](FWRust/Sealor/Definitions.lean) |
| Theorem 3.2, completeness lifts to the generative compiler | [`ConservativeSealor.conservative_sealors_give_complete_prefix_checkers`](FWRust/Sealor/Definitions.lean) |
| Theorem 3.2, soundness lifts to the generative compiler | [`ConservativeSealor.sealor_soundness_lifts_to_prefix_checkers`](FWRust/Sealor/Definitions.lean) |

## FW Rust sealor

The canonical extractor retains the core let/assignment/box/borrow/copy
frontiers and also handles Boolean, equality, and conditional syntax.

| Claim | Lean declaration |
| --- | --- |
| Theorem 5.1, SFR maintains well-typedness of realizations | [`ConservativeSealor.sealTerm_typed`](FWRust/Sealor/Sealors/NestedBlocks.lean) |
| Corollary 5.2, SFR is globally complete for partial syntax | [`ConservativeSealor.nestedBlocksPrefixChecker_complete`](FWRust/Sealor/Sealors/NestedBlocks.lean) |
| Theorem 5.3, SFR is globally complete for arbitrary strings | [`ConservativeSealor.nestedBlocksPrefixChecker_complete_on_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean) |
| Lemma 5.4, statement boundaries realize SFR's output | [`ConservativeSealor.sealProgram_completedStatementBoundary_completes`](FWRust/Sealor/Sealors/NestedBlocks.lean) |
| Theorem 5.5, SFR reflects well-typedness onto realizations at statement boundaries | [`ConservativeSealor.sealProgram_completedStatementBoundary_sound_general`](FWRust/Sealor/Sealors/NestedBlocks.lean) |
| Corollary 5.6, SFR is sound for partial syntax at statement boundaries | [`ConservativeSealor.nestedBlocksPrefixChecker_sound_on_completedStatementBoundaries`](FWRust/Sealor/Sealors/NestedBlocks.lean) |
| Theorem 5.7, SFR is sound at statement boundaries for arbitrary strings | [`ConservativeSealor.nestedBlocksPrefixChecker_sound_on_statementBoundary_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean) |

Theorems 5.3 and 5.7 are conditional on a premise encoding the required bridge
between strings and generated partial ASTs.  A complete parser and its proof
are not formalized here.

## FW Rust metatheory

| Claim by Pearce (2021) | Lean declaration |
| --- | --- |
| Lemma 4.9, Borrow Invariance | [`FWRust.Paper.typingPreservesWellFormed_of_sourceTerm`](FWRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean) |
| Lemma 4.10, Progress | [`FWRust.Paper.Soundness.lemma_4_10_progress`](FWRust/Paper/Soundness/Lemma_4_10_Progress.lean) |
| Lemma 4.11, Preservation | [`FWRust.Paper.Soundness.lemma_4_11_preservation`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean) |
| Theorem 4.12, Type and Borrow Safety for the terminating fragment | [`FWRust.Paper.Soundness.theorem_4_12_typeAndBorrowSafety_total`](FWRust/Paper/Soundness/Theorem_4_12_TypeAndBorrowSafety.lean) |

The arbitrary-state results expose concrete starting-state hypotheses such as
runtime validity, valid store typing, input well-formedness, safe abstraction,
and operational store progress.  Assignment and declaration obligations are
carried locally by their typing rules.  Empty-initial declarations such as
[`FWRust.Paper.emptyInitial_typeAndBorrowSafety_total`](FWRust/Paper/Soundness/InitialStates.lean)
derive the required source syntax, runtime/store invariants, finite support,
and safe abstraction from typing.

There is intentionally no declaration for the old strong reading of
Corollary 4.14.  With control-flow joins, an annotation may retain a stale
target as a conservative protection token even though that target is not a
live runtime pointer.  The preserved runtime statement is the stale-aware
`TerminalStateSafe` conclusion of Lemma 4.11 and Theorem 4.12.

## Section 6.1 control flow

The Section 6.1 constructs are part of `FWRust.Paper`.  `T-If` has only
guard/branch typing and type/environment joins.

| Control-flow claim | Lean declaration |
| --- | --- |
| Minimal five-premise T-If rule | [`FWRust.Paper.TermTyping.ite`](FWRust/Paper/Typing.lean) |
| Weak joined-result well-formedness is derived | [`FWRust.Paper.wellFormedTyWhenInitialized_join`](FWRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean) |
| Rank-free, path-local lvalue back-transport | [`FWRust.Paper.lvalTyping_back_of_envStrengthens`](FWRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean) |
| Initialized Borrow Invariance | [`FWRust.Paper.typingPreservesWellFormedWhenInitialized_of_sourceTerm`](FWRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean) |
| Progress | [`FWRust.Paper.Soundness.lemma_4_10_progress`](FWRust/Paper/Soundness/Lemma_4_10_Progress.lean) |
| Preservation | [`FWRust.Paper.Soundness.lemma_4_11_preservation`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean) |
| Total empty-initial type/runtime safety for missing- and loop-free terms | [`FWRust.Paper.emptyInitial_typeAndBorrowSafety_total`](FWRust/Paper/Soundness/InitialStates.lean) |
| Coherent non-linear join independence regression | [`FWRust.Paper.LinearJoinCounterexample`](FWRust/Paper/Examples/LinearJoinCounterexample.lean) |

The total empty-initial theorem requires syntactic `MissingFree` and `LoopFree`:
generated `missing` terms self-loop, and source loops need not terminate.  See
`CONDITIONALS.md` for the stale-aware safety argument and local rule repairs.

## Native while-loop extension

These declarations describe an extension beyond Pearce (2021).

| While component | Lean declaration | Boundary |
| --- | --- | --- |
| Source loop and two runtime phases | [`Term.whileLoop`, `Term.whileCond`, `Term.whileBody`](FWRust/Paper/Syntax.lean) | Integrated |
| Six loop reduction rules | [`Step.whileStart`](FWRust/Paper/InductiveSemantics.lean) through [`Step.whileBodyDone`](FWRust/Paper/InductiveSemantics.lean) | Integrated |
| Minimal normal loop rule | [`FWRust.Paper.TermTyping.whileLoop`](FWRust/Paper/Typing.lean) | Seven premises |
| Diverging-body loop rule | [`FWRust.Paper.TermTyping.whileLoopDiverging`](FWRust/Paper/Typing.lean) | Four premises |
| Finite terminal-run decomposition | [`FWRust.Paper.WhileRunEnds`](FWRust/Paper/InductiveSemantics.lean) | Used by preservation |
| Finite reachable-prefix decomposition | [`FWRust.Paper.WhileRunReaches`](FWRust/Paper/InductiveSemantics.lean) | Used by all-prefix progress |
| Loop-local terminal preservation | [`FWRust.Paper.preservation_whileRunEnds`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean) | Integrated into Lemma 4.11 |
| Every finite prefix is terminal or can step | [`FWRust.Paper.reachableProgressWhenInitialized`](FWRust/Paper/Soundness/LoopReachableSafety.lean) | No termination premise |
| Focused minimal-loop reachable safety | [`FWRust.Paper.whileLoop_reachableProgress`](FWRust/Paper/Soundness/LoopReachableSafety.lean) | Exposes T-While's seven premises |
| Syntactic loop exclusion for total wrappers | [`Term.LoopFree`](FWRust/Paper/Syntax.lean) | Used with `MissingFree` |

See [`WHILE.md`](WHILE.md) for the exact rules and the distinction between
finite-run terminal preservation, safety of arbitrary reachable prefixes, and
total termination.
