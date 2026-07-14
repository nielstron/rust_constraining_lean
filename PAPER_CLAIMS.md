# Paper-to-Lean claim map

This file maps the headline formal claims in the current generative-compilation
paper, together with the cited metatheory of Pearce (2021), to their Lean
counterparts. The framework declarations model the acceptance predicate (the
Boolean-verdict projection) of a generative compiler; textual diagnostics are
outside the mechanization.

## Generative-compiler framework

| Claim | Lean declaration |
| --- | --- |
| Section 3, prefixes admitting a valid continuation (auxiliary Lean predicate) | [`ConservativeSealor.Completable`](FWRust/Sealor/Definitions.lean#L13) |
| Section 3, exactness directions for the underlying checker | [`ConservativeSealor.CheckerComplete`](FWRust/Sealor/Definitions.lean#L67), [`ConservativeSealor.CheckerSound`](FWRust/Sealor/Definitions.lean#L75), [`ConservativeSealor.CheckerExact`](FWRust/Sealor/Definitions.lean#L81) |
| Section 3, generative-compiler completeness, soundness, and exactness on a class | [`ConservativeSealor.PrefixCheckerCompleteOn`](FWRust/Sealor/Definitions.lean#L88), [`ConservativeSealor.PrefixCheckerSoundOn`](FWRust/Sealor/Definitions.lean#L97), [`ConservativeSealor.PrefixCheckerExactOn`](FWRust/Sealor/Definitions.lean#L106) |
| Section 3, global generative-compiler completeness, soundness, and exactness | [`ConservativeSealor.PrefixCheckerComplete`](FWRust/Sealor/Definitions.lean#L116), [`ConservativeSealor.PrefixCheckerSound`](FWRust/Sealor/Definitions.lean#L123), [`ConservativeSealor.PrefixCheckerExact`](FWRust/Sealor/Definitions.lean#L130) |
| Section 3, induced generative-compiler verdict | [`ConservativeSealor.SealorPrefixChecker`](FWRust/Sealor/Definitions.lean#L143) |
| Definition 3.1, sealor completeness and soundness on a class | [`ConservativeSealor.SealorCompleteOn`](FWRust/Sealor/Definitions.lean#L21), [`ConservativeSealor.SealorSoundOn`](FWRust/Sealor/Definitions.lean#L37) |
| Definition 3.1, global sealor completeness and soundness | [`ConservativeSealor.SealorComplete`](FWRust/Sealor/Definitions.lean#L29), [`ConservativeSealor.SealorSound`](FWRust/Sealor/Definitions.lean#L45) |
| Section 3, combined sealor exactness on a class and globally | [`ConservativeSealor.SealorExactOn`](FWRust/Sealor/Definitions.lean#L52), [`ConservativeSealor.SealorExact`](FWRust/Sealor/Definitions.lean#L61) |
| Theorem 3.2, completeness-on-a-class lifting result | [`ConservativeSealor.sealor_completeness_lifts_to_prefix_checkers`](FWRust/Sealor/Definitions.lean#L149) |
| Theorem 3.2, soundness-on-a-class lifting result | [`ConservativeSealor.sealor_soundness_lifts_to_prefix_checkers`](FWRust/Sealor/Definitions.lean#L164) |
| Theorem 3.2, combined exactness consequence | [`ConservativeSealor.sealor_exactness_lifts_to_prefix_checkers`](FWRust/Sealor/Definitions.lean#L179) |

## FR sealor

| Claim | Lean declaration |
| --- | --- |
| Section 5, textual-prefix predicates used by name and decimal-integer realization | [`ConservativeSealor.NamePrefix`](FWRust/Sealor/PartialProgram.lean#L90), [`ConservativeSealor.DecimalIntPrefix`](FWRust/Sealor/PartialProgram.lean#L95) |
| Theorem 5.1, SFR maintains well-typedness of realizations | [`ConservativeSealor.sealTerm_typed`](FWRust/Sealor/Sealors/NestedBlocks.lean#L183) |
| Corollary 5.2, SFR is globally complete for partial syntax | [`ConservativeSealor.nestedBlocksSealor_complete`](FWRust/Sealor/Sealors/NestedBlocks.lean#L315) |
| Theorem 5.3, SFR is globally complete for arbitrary strings (conditional parser bridge) | [`ConservativeSealor.nestedBlocksSealor_complete_on_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean#L330) |
| Lemma 5.4, statement boundaries realize SFR's output | [`ConservativeSealor.sealProgram_completedStatementBoundary_completes`](FWRust/Sealor/Sealors/NestedBlocks.lean#L373) |
| Theorem 5.5, SFR reflects well-typedness onto realizations at statement boundaries | [`ConservativeSealor.sealProgram_completedStatementBoundary_sound_general`](FWRust/Sealor/Sealors/NestedBlocks.lean#L389) |
| Corollary 5.6, SFR is sound for partial syntax at statement boundaries | [`ConservativeSealor.nestedBlocksSealor_sound_on_completedStatementBoundaries`](FWRust/Sealor/Sealors/NestedBlocks.lean#L424) |
| Theorem 5.7, SFR is sound at statement boundaries for arbitrary strings (conditional parser bridges) | [`ConservativeSealor.nestedBlocksSealor_sound_on_statementBoundary_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean#L441) |
| Section 5 conclusion, SFR is exact at statement boundaries (conditional parser bridges) | [`ConservativeSealor.nestedBlocksSealor_exact_on_statementBoundary_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean#L501) |
| Section 5 conclusion, the induced generative compiler is exact there (conditional parser bridges) | [`ConservativeSealor.nestedBlocksPrefixChecker_exact_on_statementBoundary_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean#L526) |

The paper states Theorems 5.3 and 5.7 unconditionally and uses parser facts in
their prose proofs. Lean makes those facts explicit: Theorem 5.3 assumes a
parser, decoder, and an extendable-string-to-completable-AST bridge; Theorem
5.7 additionally assumes preservation of the statement-boundary class and a
realization-to-string-extension bridge. Parser/decoders and correspondign proofs are beyond this formalization.

At string level, Lean models the sealor semantically as
`fun s => sealProgram (decode s) : String → Program`, using the abstract
decoder. The paper's sealor instead has the textual interface
`String → String`. A serializer, parse-failure behavior (including returning an
unparsed input unchanged), and transformation of textual diagnostics are not
formalized.

The partial-syntax proofs use Lean's `Completes*` relations. Relative to the
current paper prose, Lean represents keyword-only prefixes with explicit
constructors rather than folding them into the hole case.

## FR metatheory

| Claim by Pearce (2021) | Lean declaration |
| --- | --- |
| Definition 4.7, Safe Abstraction (the full relation, notation `∼ₛ`) | [`FWRust.Paper.FullSafeAbstraction`](FWRust/Paper/Soundness/Helpers/SafeAbstraction.lean#L953) |
| Lemma 4.9, Borrow Invariance (strengthened static invariant walk) | [`FWRust.Paper.typingPreservesWellFormed_of_sourceTerm`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean#L6994) |
| Lemma 4.10, Progress | [`FWRust.Paper.Soundness.lemma_4_10_progress`](FWRust/Paper/Soundness/Lemma_4_10_Progress.lean#L1146) |
| Lemma 4.11, Preservation | [`FWRust.Paper.Soundness.lemma_4_11_preservation`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean#L16558) |
| Theorem 4.12, Type and Borrow Safety | [`FWRust.Paper.Soundness.theorem_4_12_typeAndBorrowSafety_total`](FWRust/Paper/Soundness/Theorem_4_12_TypeAndBorrowSafety.lean#L536) |
| Corollary 4.14, Borrow Safety (strengthened static calculus-core form from the Appendix) | [`FWRust.Paper.Soundness.corollary_4_14_borrowSafety`](FWRust/Paper/Soundness/Corollary_4_14_BorrowSafety.lean#L39) |

The Lemma 4.9 declaration proves a stronger bundle of output invariants, under
explicit `SourceTerm` and initial borrow-safety premises; the fresh-result-slot
form is derived by the Corollary 4.14 declaration. The latter is the
calculus-core strengthening stated in Pearce's Appendix, rather than the main
text's reduction-and-final-store formulation.

The arbitrary-state Lean results expose source-continuation, borrow-safety,
finite-support, and linearizability premises. They also package concrete-store
invariants in `ValidRuntimeState` and require `OperationalStoreProgress` where
needed. These assumptions are discharged for programs typed from the empty
initial state by the corresponding declarations in
[`FWRust.Paper.Soundness.InitialStates`](FWRust/Paper/Soundness/InitialStates.lean).
Further rule-level differences are tracked in [`DIFFERENCES.md`](DIFFERENCES.md).
