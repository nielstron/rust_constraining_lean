# Differences between the Lean formalization and the published papers

This document records semantic and theorem-statement differences.  A theorem
being listed as *restricted* does not mean that its Lean proof is incomplete:
it means that the proved proposition has more hypotheses, or a narrower input
domain, than the proposition printed in the paper.

## 1. Which FR calculus is formalized

The development combines the core calculus of Pearce (2021) with the
single-target corrections from Payet, Pearce, and Spoto (2022).  In particular,
borrows contain one lvalue rather than a set of possible targets, and `write` is
the follow-up paper's strong update.  Join-induced target sets, weak-update
unions, and fan-out are therefore absent.  This is the branch-free follow-up
specialization, not a literal transcription of every rule in the 2021 paper.

## 2. Static-rule differences

- `T-Block` has a `LifetimeChild` premise.  The block lifetime must be an
  immediate child of the ambient lifetime, whereas the papers rely on a more
  general ambient lexical-nesting assumption.
- Lean types the assignment lvalue, checks shape compatibility, and checks the
  RHS type's lifetime obligations in the post-RHS environment `env₂`.  The 2021
  `T-Assign` rule types the lvalue in the pre-RHS environment `Γ₁`.  The
  follow-up rule does perform `write(τ′, w, T)` after the RHS produces `τ′`, but
  its `survives` premise still obtains the lvalue lifetime from
  `type(w, τ)`, the **pre-RHS** typing.  Thus the earlier claim that the
  follow-up uniformly uses the post-RHS environment for the lvalue lifetime was
  incorrect.
- `T-Declare` checks freshness in the post-initializer environment `Γ₂`, rather
  than the printed `Γ₁`.  This rejects a shadow chain such as
  `let mut x = (let mut x = t)`.  On the well-formed source derivations used by
  the main proofs, post-environment freshness also implies pre-environment
  freshness.
- `CopyTy` includes `unit`.  The 2021 Definition 3.6 lists only `int` and
  immutable borrows; the follow-up's complement characterization agrees with
  the Lean choice.
- The borrow well-formedness predicates require the target's base-variable slot
  to outlive the borrow in addition to the two conditions printed in Definition
  4.8(i).  This is a genuine strengthening: lvalue typing alone does not bound
  every intervening base slot.

Theorems in this repository are consequently theorems about this corrected and
strengthened `TermTyping` relation.  Even a theorem with the same outer logical
shape as a paper theorem should be read with that qualification.

## 3. Safe abstraction and runtime validity

`FullSafeAbstraction` (notation `≈ₛ`) is the paper-facing counterpart of
Definition 4.7.  `SafeAbstraction` (notation `∼ₛ`) is an environment-indexed
internal staging invariant.  Its live-borrow branch retains Definition 4.4's
location equation, but its stale-borrow branch deliberately forgets that
equation and records only that the annotated target is not currently typable.
Thus `SafeAbstraction` is genuinely weaker for stale loans; it is not an
extensionally equivalent restatement of the paper relation.

The strict `ValidPartialValue` relation used by `FullSafeAbstraction` retains
both runtime requirements of Definition 4.4: an undefined type abstracts only
runtime `⊥`, and a borrowed reference points to the location obtained by
resolving its annotated target.  Strict validity converts to the staging
relation directly.  Conversion back uses
`ValidPartialValueWhenInitialized.toFull_of_borrowsWellFormed` and
`SafeAbstraction.full_of_containedBorrowsWellFormed`: full borrow
well-formedness makes every contained target initialized, so the relaxed stale
case is impossible at a paper-facing endpoint.  `ValidPartialValueSkeleton` is
an even weaker ownership/frame helper and is not itself either safe-abstraction
predicate.

`ValidRuntimeState` strengthens Definition 4.3's `ValidState` with invariants
needed by the abstract partial-map store: owners are allocated, owning
references target heap locations, heap slots have root lifetime, and runtime
term owners target the heap.  These properties hold for the intended concrete
execution states but are not premises of the printed definition.

## 4. Section 4 theorem strength

- **Lemma 4.9 (Borrow Invariance): paper-shaped facade and exact
  source-initial specialization.**
  `lemma_4_9_borrowInvariance` has the printed fresh-result-slot conclusion:
  `Γ₂[γ ↦ ⟨T⟩ˡ]` is well formed.  It assumes only `SourceTerm`, initial
  `WellFormedEnv`, and initial `BorrowSafeEnv`; finite support and
  linearizability are not needed.  The
  `lemma_4_9_borrowInvariance_emptyInitial` specialization derives all three
  premises from empty-initial typability.  The unrestricted printed premise is
  not valid for the mechanized T-Assign relation:
  `lemma_4_9_missingBorrowSafety_obstruction` packages a concrete valid state,
  valid store typing, strict safe abstraction, well-formed source environment,
  source typing, and fresh result name whose updated output is not well formed.
  The missing static invariant is `BorrowSafeEnv`.
- **Lemma 4.10 (Progress): paper-shaped source-initial theorem plus a
  representation-strengthened kernel.**  `emptyInitial_progress` has the
  paper's value-or-step conclusion from typing alone.  It derives the initial
  runtime facts and `OperationalStoreProgress`; the general kernel exposes
  operational totality because Lean's stores are arbitrary partial maps rather
  than finite concrete maps.
- **Lemma 4.11 (Preservation): paper-shaped source-initial theorem plus a
  restricted general kernel.**  `lemma_4_11_preservation_emptyInitial` assumes
  only typing and a terminal multistep and concludes `FullTerminalStateSafe`,
  which contains all three printed conclusions: final-state validity, strict
  safe abstraction, and result-value validity.  The arbitrary-store kernel
  states the same conclusion but exposes `SourceTerm`, `ValidRuntimeState`,
  `BorrowSafeEnv`, finite support, and the follow-up `Linearizable` invariant.
- **Theorem 4.12 (Type and Borrow Safety): total paper-shaped source-initial
  theorem plus a restricted general kernel.**
  `emptyInitial_typeAndBorrowSafety_total` needs only typing and constructs a
  terminal execution together with the stronger terminal-safety package; it
  has no termination premise.  The arbitrary-store theorem exposes the same
  source, borrow-safety, runtime-validity, finiteness, and linearizability
  invariants used by preservation.
- **Corollary 4.14 (Borrow Safety): corrected dynamic terminal forms plus the
  static core variant.**
  `corollary_4_14_borrowSafety_terminal_of_runtime_invariants` states the
  printed existential `Γ₃`, fresh-update well-formedness and borrow safety,
  environment strengthening, and final strict safe abstraction for arbitrary
  runtime-valid terminal executions.  The source-initial one-step and
  multistep forms derive every initial invariant from typing.  These theorems
  use the paper's explicit branch-free specialization `Γ₃ = Γ₂`.  Lean's
  terminal theorem separately repairs the printed unrelated result type by
  taking `T₂ = T₁`; arbitrary nonterminal reducts are not covered.  Lean also
  proves the branch-free static Appendix result.  The literal main-body statement
  quantifies an unrelated `T₂` without
  assuming that the reduct has that type.  The checked
  `corollary_4_14_printedStatement_counterexample` gives an empty-initial
  `box ()` step satisfying every printed premise for which the existential
  conclusion fails at an arbitrary incompatible `T₂`.  The 2021 paper calls the
  main-body result Corollary 4.14 but labels the static Appendix variant
  Corollary 4.13.

The extra hypotheses and specializations are not merely hidden proof
parameters.  The checked Lemma 4.9 obstruction satisfies all of its printed
runtime, store-typing, safe-abstraction, well-formedness, typing, and freshness
premises; strict output well-formedness still fails without borrow safety.  The
checked Corollary 4.14 counterexample likewise refutes its literal arbitrary-
`T₂` quantification while satisfying all printed operational premises.  The
distinction between the literal claims, paper-shaped facades, and empty-initial
specializations must therefore remain visible.

## 5. Appendix 9 coverage

- Lemmas 9.1 and 9.2 are direct proofs of safe strengthening and transitivity.
- `lemma_9_3_location_value` proves location resolution, allocation,
  arbitrary-partial-type validity, and value abstraction.  The paper's
  returned-slot lifetime equality is false for the current heap-slot encoding;
  `lemma_9_3_lifetime_index_counterexample` is a closed witness.  Corollary 9.4
  therefore exposes the actual slot lifetime while proving the full-value read
  and `ValidValue` conclusion.
- `lemma_9_5_dropPreservation_of_store_invariants` proves strict post-drop safe
  abstraction from only the four concrete store-representation invariants and
  the block-lifetime invariants, without restating domain or survivor effects;
  `lemma_9_5_dropPreservation_of_validRuntimeState` is its convenient runtime
  corollary.  The unqualified abstract-store statement is false: its checked
  counterexample uses an owner that targets a variable, precisely violating
  the heap-origin invariant.
- Lemma 9.6 is represented by an assignment-specific operational analogue with
  the paper's post-update safe-abstraction conclusion.  It specializes the
  paper's new partial value/type to an evaluated full RHS `Value`/`Ty` (while
  retaining a partial overwritten type), uses an actual terminal assignment
  step, states the runtime/static representation invariants needed by that
  step, and follows Lean's write-then-drop order.  There is no direct
  empty-store assignment corollary: such a step cannot read an overwritten slot
  and would therefore be vacuous.
- Lemma 9.7 is proved in a stronger form that drops an unused well-formedness
  premise.
- Lemmas 9.8–9.10 have named one-step wrappers with the printed conclusions and
  empty/source-initial forms.  Their general wrappers project the independent
  shared theorem `appendix_9_oneStep_fullPreservation_of_runtime_invariants`,
  which performs a direct case split over terminal steps; it does not invoke
  global Lemma 4.11 and needs neither `SourceTerm` nor finite support.  It thus
  covers already evaluated redexes such as `box (.val ownerRef)`.  The explicit
  `RuntimeRedexBorrowSafe` premise is definitionally `True` except for
  assignment: there it says the runtime RHS's `ValueTyping` type is borrow-safe
  against the input environment.  `ValidRuntimeState` and `ValidStoreTyping`
  do not imply that loan-conflict fact.  The per-rule facts in
  `Helpers/ValuePreservation` and `Lemma_4_11_Preservation` are the proof
  ingredients assembled by the shared theorem.

## 6. Follow-up linearization and termination

The follow-up paper's Definition 11 requires an injective rank map over a finite
context `κ`.  Lean's `Linearizable` currently asks only for a total
`Name → Nat` map satisfying strict inequalities along mentioned-variable edges;
it does not state injectivity or carry `κ` explicitly.  This is a weaker literal
definition, even though the edge inequalities are the part used by the proofs.

The move and lifetime-drop preservation lemmas have direct Lean counterparts.
Fresh declaration is handled by a rank-raising helper.  Assignment
linearizability is proved only with additional well-formedness, borrow-safety,
result-type-safety, finite-support, shape, and write-prohibition premises.  The
global typing invariant likewise assumes a source term, well-formed and
borrow-safe input, and finite support.

The follow-up's Proposition 1 (well-foundedness of its lvalue order) and
Proposition 2 (termination of the recursive `type` algorithm) are not
formalized.  Lean defines typing inductively and uses linearizability inside
preservation; it does not implement and verify that borrow-checking algorithm.

## 7. Operational-rule and representation differences

- Lean's `R-Assign` reads the old slot, writes the new value, and then drops the
  old value from the post-write store.  This follows the reference
  implementation rather than the printed 2021 drop-then-write rule and Appendix
  Lemma 9.6 proof.
- Raw `R-Declare` is an update and does not itself require a fresh variable.
  Freshness is recovered from `T-Declare` for typed states, so the untyped
  reduction relation is broader than the soundness theorem's domain.
- `ProgramStore` and `Env` are arbitrary partial maps.  Finite-support premises
  make explicit the finiteness implicit in the papers' concrete maps.
- Lifetimes are paths ordered by prefix, a concrete lexical tree rather than an
  arbitrary partial order.

## 8. Sealor mechanization boundary

The language-specific sealor proofs first operate over generated partial ASTs
and an inductive realization relation.  The maintenance, partial-syntax
completeness, and statement-boundary soundness results are AST-level theorems.
They do not by themselves prove claims about arbitrary character strings.

At this AST layer, identifier and integer frontiers are treated as lexical
prefixes, keyword-only term states have the paper's unrestricted-hole
realization behavior, and an unfinished term list must realize at least its
frontier term.  These choices prevent the realization relation from accepting
unrelated identifier spellings, treating a partial integer as already complete,
or witnessing a statement boundary with an empty continuation.

The arbitrary-string completeness and soundness declarations are conditional
lifting theorems.  They quantify over a parser and decoder and assume bridge
properties connecting string extension to AST realization (and, for
soundness, connecting the string boundary class to the AST boundary class).
No concrete parser/decoder satisfying those bridge assumptions is formalized.
Accordingly, the paper's unconditional string-level claims remain conditional
in Lean even though their AST-level cores are proved.
