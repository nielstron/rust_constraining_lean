# Paper-to-Lean claim map

This file contains a mapping between claims in our work and claims of Pearce (2021) and their mechanized statements.

## Generative-compiler framework

| Claim | Lean declaration |
| --- | --- |
| Definition 3.1, sealor completeness | [`ConservativeSealor.Conservative`](FWRust/Sealor/Definitions.lean#L19) |
| Definition 3.1, prefixes admitting a valid continuation | [`ConservativeSealor.Completable`](FWRust/Sealor/Definitions.lean#L13) |
| Definition 3.1, selective soundness | [`ConservativeSealor.SealorSoundOn`](FWRust/Sealor/Definitions.lean#L55) |
| Theorem 3.2, completeness lifts to the generative compiler | [`ConservativeSealor.conservative_sealors_give_complete_prefix_checkers`](FWRust/Sealor/Definitions.lean#L75) |
| Theorem 3.2, soundness lifts to the generative compiler | [`ConservativeSealor.sealor_soundness_lifts_to_prefix_checkers`](FWRust/Sealor/Definitions.lean#L92) |

## FR sealor

| Claim | Lean declaration |
| --- | --- |
| Theorem 5.1, SFR maintains well-typedness of realizations | [`ConservativeSealor.sealTerm_typed`](FWRust/Sealor/Sealors/NestedBlocks.lean#L183) |
| Corollary 5.2, SFR is globally complete for partial syntax | [`ConservativeSealor.nestedBlocksPrefixChecker_complete`](FWRust/Sealor/Sealors/NestedBlocks.lean#L313) |
| Theorem 5.3, SFR is globally complete for arbitrary strings | [`ConservativeSealor.nestedBlocksPrefixChecker_complete_on_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean#L322) |
| Lemma 5.4, statement boundaries realize SFR's output | [`ConservativeSealor.sealProgram_completedStatementBoundary_completes`](FWRust/Sealor/Sealors/NestedBlocks.lean#L349) |
| Theorem 5.5, SFR reflects well-typedness onto realizations at statement boundaries | [`ConservativeSealor.sealProgram_completedStatementBoundary_sound_general`](FWRust/Sealor/Sealors/NestedBlocks.lean#L365) |
| Corollary 5.6, SFR is sound for partial syntax at statement boundaries | [`ConservativeSealor.nestedBlocksPrefixChecker_sound_on_completedStatementBoundaries`](FWRust/Sealor/Sealors/NestedBlocks.lean#L399) |
| Theorem 5.7, SFR is sound at statement boundaries for arbitrary strings | [`ConservativeSealor.nestedBlocksPrefixChecker_sound_on_statementBoundary_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean#L408) |

Theorems 5.3 and 5.7 are mechanized conditional on a premise that encodes the existence of a complete parser from strings to partial ASTs. Such a parser and proof are not formalized in this mechanization.

## FR metatheory

| Claim by Pearce (2021) | Lean declaration |
| --- | --- |
| Lemma 4.9, Borrow Invariance | [`FWRust.Paper.typingPreservesWellFormed_of_sourceTerm`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean#L7347) |
| Lemma 4.10, Progress | [`FWRust.Paper.Soundness.lemma_4_10_progress`](FWRust/Paper/Soundness/Lemma_4_10_Progress.lean#L1285) |
| Lemma 4.11, Preservation | [`FWRust.Paper.Soundness.lemma_4_11_preservation`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean#L17070) |
| Theorem 4.12, Type and Borrow Safety | [`FWRust.Paper.Soundness.theorem_4_12_typeAndBorrowSafety_total`](FWRust/Paper/Soundness/Theorem_4_12_TypeAndBorrowSafety.lean#L536) |
| Corollary 4.14, Borrow Safety | [`FWRust.Paper.Soundness.corollary_4_14_borrowSafety`](FWRust/Paper/Soundness/Corollary_4_14_BorrowSafety.lean#L39) |

The arbitrary-state Lean results expose the additional source-continuation,
borrow-safety, finite-support, and linearizability assumptions required by the
mechanization. These assumptions are discharged for programs typed from the
empty initial state by the corresponding declarations in
[`FWRust.Paper.Soundness.InitialStates`](FWRust/Paper/Soundness/InitialStates.lean).

## Section 6.1 control-flow extension

The extension is namespaced separately as `FWRust.Conditional.Paper`; its
`T-If` constructor has only guard/branch typing and type/environment joins.

| Conditional-extension claim | Lean declaration |
| --- | --- |
| Minimal T-If rule | [`FWRust.Conditional.Paper.TermTyping.ite`](FWRust/Conditional/Paper/Typing.lean) |
| Weak joined-result well-formedness is derived | [`FWRust.Conditional.Paper.wellFormedTyWhenInitialized_join`](FWRust/Conditional/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean) |
| Rank-free, path-local lvalue back-transport | [`FWRust.Conditional.Paper.lvalTyping_back_of_envStrengthens`](FWRust/Conditional/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean) |
| Lemma 4.9, Borrow Invariance | [`FWRust.Conditional.Paper.typingPreservesWellFormedWhenInitialized_of_sourceTerm`](FWRust/Conditional/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean) |
| Lemma 4.10, Progress | [`FWRust.Conditional.Paper.Soundness.lemma_4_10_progress`](FWRust/Conditional/Paper/Soundness/Lemma_4_10_Progress.lean) |
| Lemma 4.11, Preservation | [`FWRust.Conditional.Paper.Soundness.lemma_4_11_preservation`](FWRust/Conditional/Paper/Soundness/Lemma_4_11_Preservation.lean) |
| Total empty-initial type/runtime safety | [`FWRust.Conditional.Paper.emptyInitial_typeAndBorrowSafety_total`](FWRust/Conditional/Paper/Soundness/InitialStates.lean) |
| Coherent non-linear join independence regression | [`FWRust.Conditional.Paper.LinearJoinCounterexample`](FWRust/Conditional/Paper/Examples/LinearJoinCounterexample.lean) |

The total empty-initial theorem requires only typing and the syntactic
`MissingFree` premise (generated `missing` terms intentionally self-loop).  It
derives source syntax, runtime/store validity, finite support, initial
well-formedness, and safe abstraction internally.  See `CONDITIONALS.md` for
the extension's local assignment/declaration corrections and the stale-aware
interpretation of terminal safety.
