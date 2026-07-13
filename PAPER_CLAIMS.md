# Paper-to-Lean claim map

This map distinguishes literal theorem coverage from useful restricted or
representation-level results.

Status terminology:

- **Exact/generalized:** the Lean proposition has the paper's logical content,
  possibly generalized from strings to an arbitrary completion relation.
- **AST-level:** the theorem is proved for generated partial syntax and its
  realization relation, before parsing strings.
- **Conditional string:** the theorem assumes an unverified parser/decoder
  bridge.
- **Paper-shaped specialization:** the declaration states the paper's
  characteristic conclusion explicitly, while restricting the initial state,
  reduct, or instantiating variables that the printed statement leaves
  arbitrary.
- **Restricted/strengthened:** the conclusion may be stronger, but the theorem
  has additional hypotheses or a narrower domain than the printed claim.
- **Support only:** relevant ingredients are proved, but no declaration states
  the paper theorem itself.

## Generative-compiler framework

| Paper claim | Lean declaration | Status |
| --- | --- | --- |
| Sealor completeness | [`ConservativeSealor.Conservative`](FWRust/Sealor/Definitions.lean) | Global-class relational form, stated contrapositively; classically equivalent to every completable input having a valid sealing, but not separately parameterized by a class |
| Prefixes admitting a valid continuation | [`ConservativeSealor.Completable`](FWRust/Sealor/Definitions.lean) | Exact generalized relational form |
| Selective sealor soundness | [`ConservativeSealor.SealorSoundOn`](FWRust/Sealor/Definitions.lean) | Exact generalized relational form |
| Completeness lifts to the induced generative compiler | [`ConservativeSealor.conservative_sealors_give_complete_prefix_checkers`](FWRust/Sealor/Definitions.lean) | Global-class relational form; uses the compiler-completeness half of exactness |
| Soundness lifts to the induced generative compiler | [`ConservativeSealor.sealor_soundness_lifts_to_prefix_checkers`](FWRust/Sealor/Definitions.lean) | Exact/generalized; uses the compiler-soundness half of exactness |

## FR sealor

| Paper claim | Lean declaration | Status |
| --- | --- | --- |
| SFR maintains well-typedness of realizations | [`ConservativeSealor.sealTerm_typed`](FWRust/Sealor/Sealors/NestedBlocks.lean) | AST-level, exact for `PartialTerm`/`CompletesTerm` |
| SFR is globally complete for partial syntax | [`ConservativeSealor.nestedBlocksPrefixChecker_complete`](FWRust/Sealor/Sealors/NestedBlocks.lean) | AST-level |
| SFR is globally complete for arbitrary strings | [`ConservativeSealor.nestedBlocksPrefixChecker_complete_on_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean) | Conditional string: assumes the parser/decoder completeness bridge |
| Statement boundaries realize SFR's output | [`ConservativeSealor.sealProgram_completedStatementBoundary_completes`](FWRust/Sealor/Sealors/NestedBlocks.lean) | AST-level |
| SFR reflects well-typedness onto realizations at statement boundaries | [`ConservativeSealor.sealProgram_completedStatementBoundary_sound_general`](FWRust/Sealor/Sealors/NestedBlocks.lean) | AST-level |
| SFR is sound for partial syntax at statement boundaries | [`ConservativeSealor.nestedBlocksPrefixChecker_sound_on_completedStatementBoundaries`](FWRust/Sealor/Sealors/NestedBlocks.lean) | AST-level |
| SFR is sound at statement boundaries for arbitrary strings | [`ConservativeSealor.nestedBlocksPrefixChecker_sound_on_statementBoundary_strings`](FWRust/Sealor/Sealors/NestedBlocks.lean) | Conditional string: assumes boundary preservation and AST-realization-to-string-extension bridges |

The AST-level results do not require a parser.  The two string-level declarations
quantify over `parse` and `decode`; this repository does not supply and verify a
concrete pair satisfying their bridge premises.

## FR metatheory from Pearce (2021)

| Paper claim | Lean declaration | Status |
| --- | --- | --- |
| Lemma 4.9, Borrow Invariance | [`FWRust.Paper.lemma_4_9_borrowInvariance`](FWRust/Paper/Soundness/InitialStates.lean) | Corrected paper-shaped form: states the printed arbitrary-fresh-slot conclusion and assumes only source syntax plus initial well-formedness and borrow safety; finite support and linearizability are not required |
| Lemma 4.9, empty-initial specialization | [`FWRust.Paper.lemma_4_9_borrowInvariance_emptyInitial`](FWRust/Paper/Soundness/InitialStates.lean) | Paper-shaped source-initial conclusion from typing alone; source syntax, well-formedness, and borrow safety are derived |
| Lemma 4.9, missing-premise obstruction | [`FWRust.Paper.lemma_4_9_missingBorrowSafety_obstruction`](FWRust/Paper/Soundness/InitialStates.lean) | Checked counterexample to the full printed premises: concrete valid state, valid store typing, strict safe abstraction, well-formed source environment, source typing, and a fresh result name, but the updated result environment is not well formed. The missing invariant is `BorrowSafeEnv` |
| Lemma 4.10, Progress, source-initial | [`FWRust.Paper.emptyInitial_progress`](FWRust/Paper/Soundness/InitialStates.lean) | Paper-shaped value-or-step result from typing alone; the empty initial state derives runtime validity and operational totality |
| Lemma 4.10, general kernel | [`FWRust.Paper.Soundness.lemma_4_10_progress`](FWRust/Paper/Soundness/Lemma_4_10_Progress.lean) | Representation-strengthened by explicit operational-store totality |
| Lemma 4.11, Preservation, source-initial | [`FWRust.Paper.lemma_4_11_preservation_emptyInitial`](FWRust/Paper/Soundness/InitialStates.lean) | Paper-shaped terminal multistep result from typing and reduction alone; `FullTerminalStateSafe` contains final validity, strict safe abstraction, and value validity |
| Lemma 4.11, general kernel | [`FWRust.Paper.Soundness.lemma_4_11_preservation`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean) | Restricted/strengthened: source, runtime-validity, borrow-safety, finite-support, and linearizability premises, with the full printed conclusion |
| Theorem 4.12, Type and Borrow Safety, source-initial | [`FWRust.Paper.emptyInitial_typeAndBorrowSafety_total`](FWRust/Paper/Soundness/InitialStates.lean) | Total, non-circular paper-shaped specialization from typing alone; proves terminal existence and the stronger terminal-safety package |
| Theorem 4.12, general kernel | [`FWRust.Paper.Soundness.theorem_4_12_typeAndBorrowSafety_total`](FWRust/Paper/Soundness/Theorem_4_12_TypeAndBorrowSafety.lean) | Restricted/strengthened arbitrary-store result |
| Corollary 4.14, corrected dynamic conclusion | [`FWRust.Paper.Soundness.corollary_4_14_borrowSafety_terminal_of_runtime_invariants`](FWRust/Paper/Soundness/Corollary_4_14_BorrowSafety.lean) | Paper-shaped terminal multistep form: existential `Γ₃`, fresh-update well-formedness and borrow safety, strengthening, and final strict safe abstraction. It uses the paper's explicit branch-free choice `Γ₃ = Γ₂`; Lean separately repairs the printed unrelated result type with the terminal specialization `T₂ = T₁` and states the concrete runtime invariants explicitly |
| Corollary 4.14, source-initial forms | [`FWRust.Paper.Soundness.corollary_4_14_borrowSafety_emptyInitial_terminal`](FWRust/Paper/Soundness/Corollary_4_14_BorrowSafety.lean), [`...terminalStep`](FWRust/Paper/Soundness/Corollary_4_14_BorrowSafety.lean) | The same full dynamic conclusion for terminal multistep and one-step executions, deriving all initial invariants from empty typability |
| Corollary 4.14, static calculus-core/Appendix form | [`FWRust.Paper.Soundness.corollary_4_14_borrowSafety`](FWRust/Paper/Soundness/Corollary_4_14_BorrowSafety.lean) | Restricted/strengthened static core result with the fresh result slot; the Appendix labels this variant Corollary 4.13 |
| Corollary 4.14, literal arbitrary-`T₂` obstruction | [`FWRust.Paper.Soundness.corollary_4_14_printedStatement_counterexample`](FWRust/Paper/Soundness/Corollary_4_14_BorrowSafety.lean) | Checked counterexample satisfying every printed premise: the statement leaves `T₂` unrelated to the reduct, so an incompatible arbitrary `T₂` makes the existential strengthening conclusion false |

All of these results concern the corrected/strengthened typing and operational
relations described in `DIFFERENCES.md`, not a byte-for-byte transcription of
the 2021 calculus.

### Appendix 9

| Paper claim | Lean declaration | Status |
| --- | --- | --- |
| Lemma 9.1, Safe Strengthening | [`FWRust.Paper.Soundness.lemma_9_1_safeStrengthening`](FWRust/Paper/Soundness/Appendix9/Lemma_9_1_SafeStrengthening.lean) | Proved |
| Lemma 9.2, Transitive Strengthening | [`FWRust.Paper.Soundness.lemma_9_2_transitiveStrengthening`](FWRust/Paper/Soundness/Appendix9/Lemma_9_2_TransitiveStrengthening.lean) | Exact |
| Lemma 9.3, Location | [`FWRust.Paper.Soundness.lemma_9_3_location_value`](FWRust/Paper/Soundness/Appendix9/Lemma_9_3_Location.lean) | Proves the printed location, allocated-slot, arbitrary-partial-type, and value-abstraction content. The encoded heap-slot lifetime equality is false; [`lemma_9_3_lifetime_index_counterexample`](FWRust/Paper/Soundness/Appendix9/Lemma_9_3_Location.lean) is a checked witness |
| Corollary 9.4, Read Preservation | [`FWRust.Paper.Soundness.corollary_9_4_read_value`](FWRust/Paper/Soundness/Appendix9/Corollary_9_4_ReadPreservation.lean) | Proves a defined full-value read and `ValidValue`, exposing the actual slot lifetime instead of asserting the false equality from 9.3 |
| Lemma 9.5, Drop Preservation | [`FWRust.Paper.Soundness.lemma_9_5_dropPreservation_of_store_invariants`](FWRust/Paper/Soundness/Appendix9/Lemma_9_5_DropPreservation.lean) | Strict post-drop abstraction under exactly the four concrete store-representation invariants plus the block-lifetime invariants; [`...of_validRuntimeState`](FWRust/Paper/Soundness/Appendix9/Lemma_9_5_DropPreservation.lean) projects those premises from a runtime state. [`lemma_9_5_unqualified_counterexample`](FWRust/Paper/Soundness/Appendix9/Lemma_9_5_DropPreservation.lean) refutes the unqualified abstract-store form by violating heap origin |
| Lemma 9.6, Update Preservation | [`FWRust.Paper.Soundness.lemma_9_6_updatePreservation_oneStep_of_runtime_invariants`](FWRust/Paper/Soundness/Appendix9/Lemma_9_6_UpdatePreservation.lean) | Strengthened operational analogue for the corrected write-then-drop semantics: it uses an actual terminal assignment step, specializes the new assignment value/RHS type to an evaluated full `Value`/`Ty` while retaining a partial overwritten type, and states the necessary runtime/static representation invariants. It packages the independent assignment-specific proof rather than projecting global Lemma 4.11; no vacuous empty-store assignment wrapper is advertised |
| Lemma 9.7, Value Typing | [`FWRust.Paper.Soundness.lemma_9_7_valueTyping`](FWRust/Paper/Soundness/Appendix9/Lemma_9_7_ValueTyping.lean) | Strengthened by dropping an unused premise |
| Lemma 9.8, Alias Preservation | [`FWRust.Paper.Soundness.lemma_9_8_aliasPreservation_oneStep_of_runtime_invariants`](FWRust/Paper/Soundness/Appendix9/Lemma_9_8_AliasPreservation.lean) | Printed one-step conclusion projected from the independent shared strict theorem [`appendix_9_oneStep_fullPreservation_of_runtime_invariants`](FWRust/Paper/Soundness/Appendix9/Lemma_9_8_AliasPreservation.lean), plus an empty/source-initial form. The general theorem has no `SourceTerm` or finite-support premise and covers runtime-valued redexes. `RuntimeRedexBorrowSafe` is nontrivial only for assignment, where it supplies RHS loan compatibility absent from runtime/store validity |
| Lemma 9.9, Value Preservation | [`FWRust.Paper.Soundness.lemma_9_9_valuePreservation_oneStep_of_runtime_invariants`](FWRust/Paper/Soundness/Appendix9/Lemma_9_9_ValuePreservation.lean) | Printed one-step strict value-validity conclusion projected from the same independent shared terminal-redex theorem, plus an empty/source-initial form; not a projection of global Lemma 4.11 |
| Lemma 9.10, Store Preservation | [`FWRust.Paper.Soundness.lemma_9_10_storePreservation_oneStep_of_runtime_invariants`](FWRust/Paper/Soundness/Appendix9/Lemma_9_10_StorePreservation.lean) | Printed one-step strict safe-abstraction conclusion projected from the same independent shared terminal-redex theorem, plus an empty/source-initial form; not a projection of global Lemma 4.11 |

## Termination follow-up (Payet, Pearce, and Spoto, 2022)

| Paper claim | Lean declaration | Status |
| --- | --- | --- |
| Definition 11, Linearizable typing | [`FWRust.Paper.Linearizable`](FWRust/Paper/Typing.lean) | Weaker literal definition: edge inequalities only; injectivity and explicit finite context `κ` are absent |
| Proposition 1, well-founded lvalue order | — | Not formalized |
| Proposition 2, termination of recursive `type` | — | Not formalized; Lean uses an inductive typing relation |
| Lemma 1, move preserves linearizability | [`FWRust.Paper.LinearizedBy.move`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean) | Proved modulo Lean's weaker `Linearizable` definition |
| Lemma 2, drop preserves linearizability | [`FWRust.Paper.LinearizedBy.dropLifetime`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean) | Proved modulo Lean's weaker `Linearizable` definition |
| Lemma 3, fresh declaration preserves linearizability | [`FWRust.Paper.LinearizedBy.update_fresh_above`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean) | Helper form with explicit non-occurrence premises |
| Lemma 4, assignment preserves linearizability | [`FWRust.Paper.EnvWrite.preserves_linearizable`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean) | Restricted by additional well-formedness, borrow-safety, finite-support, typing, shape, and prohibition premises |
| Section 6 typing invariant | [`FWRust.Paper.typingPreservesLinearizable_of_sourceTerm`](FWRust/Paper/Soundness/Lemma_4_11_Preservation.lean) | Restricted to source, well-formed, borrow-safe, finite-support inputs |
