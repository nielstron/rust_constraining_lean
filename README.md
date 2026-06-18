# lw_rust

Lean mechanisation of the core FR/lw-rust calculus from the paper.

## Deviations from the Paper

This section records **critical deviations**: places where the mechanisation
currently proves less than the printed paper claims.  The goal is to reduce
these to 0.  Each entry notes whether the deviation is mechanisation debt
(closable) or a likely paper bug (the printed claim appears unprovable as
stated; the deviation then documents the corrected claim).

- **The mechanised typing relation is strictly stronger than the paper's, and
  no admissibility theorem bridges the gap.**  `T-Assign` carries extra
  obligations (the lhs re-typeable after the rhs, a linearization/rank witness
  `∃ φ, LinearizedBy φ ∧ EnvWriteRhsBorrowTargetsBelow`,
  `EnvWriteCoherenceObligations`, `ContainedBorrowsWellFormed` for the result,
  plus per-branch typing witnesses and weak-update shape premises inside
  `EnvWrite` itself); `T-Declare` carries `FreshUpdateCoherenceObligations`
  and a second freshness check on the post-initialiser environment; `T-Block`
  requires `LifetimeChild` (immediate child, stricter than the paper's
  "inside").  These are deliberate corrections (see Improvements below), but
  every safety theorem quantifies over *mechanised* typings, so the end-to-end
  results cover a (potentially proper) subset of the programs the paper's
  rules accept.  *Mechanisation debt:* an admissibility lemma showing the
  extra obligations are derivable for paper-typable core programs would
  restore full coverage.

  Provenance assessment (which obligations are derivable from the paper rules
  vs. genuinely additional):

  - *Rank witness* (`∃ φ, LinearizedBy φ ∧ EnvWriteRhsBorrowTargetsBelow`) —
    **derivable in principle**: `Linearizable` is Definition 11 of
    `lw_rust_followup.pdf`, whose Section 6 ("Semantical Invariant",
    Lemmas 1–4) proves in prose that the typing rules preserve
    linearizability from any linearizable start; the mechanised premise is
    the rule-carried form of Lemma 4's (hand-wavy) assignment case.  The
    second conjunct (fan-out mutable-conflict locality) goes beyond the
    follow-up but is vacuous for the core, where multi-target borrows cannot
    arise (paper Section 3.4).
  - *Coherence obligations* (`EnvWriteCoherenceObligations`,
    `ContainedBorrowsWellFormed`, `FreshUpdateCoherenceObligations`) —
    **derivable for core programs**: coherence concerns joint target-list
    typing, and core target lists are singletons typed in the same
    environment; the incoherent-`&[]` pathology cannot be produced by core
    source programs from the empty environment.  For *arbitrary* well-formed
    starting environments these are likely genuinely necessary, since such
    environments admit pathologies the core never creates.
  - *`EnvWrite` internals* (fan-out initialized-typing witnesses, weak-update
    `ShapeCompatible`) — **formalised paper prose**: the paper asserts
    "borrowed locations cannot have partial types"; for pipeline
    environments this follows from `WellFormedEnv`, but the Lean relations
    range over arbitrary environments, so the assertion must be a premise.
  - *Lhs re-typing after the rhs* — **genuinely stricter, printed rule
    dubious where they diverge**: the paper types `w` only in `Γ₁`; if the
    rhs retypes the lhs path (e.g. `*p = { p = &mut w; … }`), the printed
    rule's shape check compares against a stale type — arguably a paper bug.
  - *`env₂.fresh x` on `T-Declare`* — **genuinely stricter**: rejects
    initializer shadowing (`let mut x = (let mut x = e)`), which the printed
    rule accepts; harmless modulo alpha-renaming, and the follow-up's
    Lemma 3 implicitly assumes post-initialiser freshness as well.
  - *`LifetimeChild`* — **not a restriction**: it formalises the paper's
    Section 3.1 ambient assumption that block lifetimes reflect nesting,
    with immediate-child paths as the canonical labelling.

  In summary, none of the obligations is a new semantic requirement for the
  soundness of core programs; the residue of this deviation is the missing
  formalised admissibility proof (essentially follow-up Section 6 plus
  coherence propagation) and the two benign tightenings above.

- **Global `BorrowSafeEnv` is removed and replaced by local authority
  checks.**  The printed paper treats borrow-safety as a whole-environment
  property, and the original Corollary 4.14 suggests that this global property
  should survive typing.  That is too strong for path-insensitive joins:
  `T-If` and `T-WhileJoin` can merge branch-exclusive mutable borrows into a
  well-formed environment whose target lists are not globally borrow-safe.  The
  mechanisation therefore deletes `BorrowSafeEnv` rather than carrying it as a
  premise on `T-If`, `T-WhileJoin`, progress, preservation, or extractor
  correctness.

  The replacement is deliberately tighter and more local.  `T-Assign` carries
  `AssignmentBorrowSafety env lhs`: direct root writes need no global borrow
  safety, while dereference writes require `BorrowSafeRoot` only for roots in
  the written lvalue's `BorrowAuthorityGuard` closure.  Unrelated conflicts
  elsewhere in a joined environment no longer block unrelated assignments or
  dereferences.  This accepts more realistic Rust-shaped code, such as
  conditionals that swap two distinct mutable borrows across branches, while
  still rejecting operations that actually need ambiguous dereference
  authority.  Corollary 4.14 is correspondingly weakened to the true global
  result: output environments remain well-formed, not globally borrow-safe.

## Improvements

This section notes down changes done to the paper that strengthen its results or otherwise were necessary for correctness.
These deviations from the paper should be kept.

- **Join-invariant loops (`T-WhileJoin`) with rule-carried monotonicity.**
  Beyond the strict rule below, `TermTyping.whileLoopJoin` checks a loop
  against an invariant environment solving `Γ_inv = Γ_entry ⊔ Γ_back`
  (NLL-style: loops may widen borrow target lists across iterations, e.g.
  re-point an outer `&mut` inside the body), with the `T-If` obligation kit
  for the join.  Its final two premises re-type the condition and body from
  the *entry-side* environments.  In rustc this is implied — per-code borrow
  checking is monotone under removing loans — but in this calculus it is
  unprovable (`Examples/ThinningFalse.lean`: borrow types carry pointee
  information in their target lists, so shrinking a target list can make a
  dereference typeless), so the monotonicity fact is carried as premises,
  following the rule-carried-obligation convention.  The conservative
  extractor's transport re-roots truncated loops at the loop position using
  exactly these entry-side derivations, which is what lets partial loop
  conditions keep their statement extraction with no precision loss.

- **`T-Eq` keeps the paper's ghost-slot check, rule-carried.**  The paper
  types the right operand in `Γ₂[γ ↦ ⟨T₁⟩^l]` for an anonymous fresh `γ` and
  erases `γ` afterwards, so borrows inside the left operand's result type keep
  prohibiting conflicting uses while the right operand is typed.  The
  mechanised rule carries exactly that ghost derivation as a premise (the
  paper's precision filter), *plus* the eliminated form — the right operand
  typed in plain `Γ₂` — which is what the metatheory threads.  In the paper
  the eliminated form is implied by the ghost form via fresh-slot thinning,
  but that implication is unprovable here: the ghost slot has no runtime
  counterpart, so its derivation cannot be threaded through preservation
  (safe abstraction `S ∼ Γ` demands two-way domain agreement), and a general
  thinning metatheorem is in the same family as the false environment
  weakening of `Examples/ThinningFalse.lean` (target-list borrow types make
  dereferences environment-sensitive).  Following the
  rule-carried-obligation convention (cf. `T-WhileJoin`), the monotonicity
  fact is carried as a premise rather than proven; no precision is lost
  relative to the paper, and right operands conflicting with lhs-result
  borrows are rejected as the paper intends.

- **While loops (`T-While`, `T-WhileDiv`), beyond the paper.**  The paper's
  calculus is loop-free (its original termination argument depended on it).
  `Term.whileLoop` adds `while cond { body }` with two in-flight runtime
  forms (`whileCond`, `whileBody`) instead of syntactic unfolding — unfolding
  is unsound here: the copied continuation would nest inside the iteration
  block, so body locals would leak across iterations and the copied loop
  would sit at lifetimes violating the lexical `LifetimeChild` discipline.
  `T-While` uses a *strict* loop invariant: the body must restore the
  loop-entry environment exactly (`Γ₃.dropLifetime = Γ₁`), so the back edge
  re-enters the same derivation verbatim and terminal-run preservation is an
  induction over the iteration structure (`WhileRunEnds`,
  `WhileRunReaches`).  This under-approximates rustc's NLL fixpoint (loops
  that widen borrow sets across iterations are rejected).  `T-WhileDiv`
  types a loop whose body is checked but diverges (`…; panic!()`) with no
  back-edge obligation — what `ast_copier` relies on when rebuilding a
  truncated loop body — and the extractor rebuilds partial loop bodies this
  way (`while c { …stmts…; missing }`).

- **Divergence-aware conditionals (`T-IfDiv`), modelling real Rust.**  The
  paper's `T-If` always joins both branch environments; rustc instead lets a
  `panic!()`-terminated branch type at `!` and contribute nothing to the
  borrow-state merge.  `TermTyping.iteDiverging` adds exactly this rule: if
  the else-branch is fully type-checked *and* syntactically diverges
  (`Term.Diverges`, the counterpart of `!`-propagation; `Term.missing` plays
  the role of `panic!()`), the conditional's result type and environment are
  the live branch's.  No new terms and no semantics changes are involved;
  in preservation the dead-branch path is discharged by
  `diverges_multistep_not_value` (a diverging branch never reaches a value),
  and all other metatheory cases defer to the premise IHs.  This is what lets
  the conservative extractor rebuild `if c { … } else { …; panic!() }` around
  a truncated branch the way `ast_copier` does
  (`LwRust/Extractor/Extractors/NestedBlocks.lean`).

- **The executable checker has an explicit three-way verdict.**
  `borrowCheckVerdict? fuel term = .accepted` and the boolean wrapper
  `borrowCheck? fuel term = true` both imply the inductive closed-program
  property `borrowCheck term` (`borrowCheck_of_borrowCheck?`,
  `borrowCheck?_sound`, and
  `borrowCheck_of_borrowCheckVerdict?_accepted`).  The `.failed` verdict,
  exposed as `borrowCheckFailed?`, records an executable rule-premise failure,
  not a completeness theorem for logical non-typability; the reflection lemma
  `borrowCheckFailed?_eq_true_iff` characterizes it exactly as a checker error
  not classified as unknown, while
  `borrowCheckFailed?_eq_true_iff_witness` packages the same executable result
  as a `CertifiedBorrowFailure` witness.  The executable certifier bit is
  characterized by `certifyBorrowFailure?_found_iff`, and
  `borrowCheckFailureWitness_of_certifyBorrowFailure?` projects that bit to
  the proof-facing witness.  A failure witness also rules out an accepted
  checker witness at the same fuel
  (`borrowCheckFailureWitness_no_borrowCheckWitness`), without claiming
  logical non-typability.  The `.unknown` verdict, exposed as
  `borrowUnknown?`, records fuel exhaustion, non-converged invariant iteration,
  or an inference limitation, including failures from fuel-bounded helper
  inference that should not be reported as finite rejection
  (`borrowUnknown?_eq_true_iff` and `borrowUnknown?_eq_true_iff_witness`);
  `certifyBorrowUnknown?_found_iff` and
  `borrowUnknownWitness_of_certifyBorrowUnknown?` provide the matching
  proof-carrying found-bit projection, and
  `borrowUnknownWitness_no_borrowCheckWitness` similarly rules out a same-fuel
  accepted checker witness.
  The theorem `borrowCheck?_eq_true_iff` characterizes successful executable
  runs, and `borrowCheck?_eq_true_iff_witness` states the proof-carrying
  reflection: `borrowCheck? fuel term = true` exactly when a
  `CertifiedBorrowCheck` witness exists.  In examples, `borrow_check` runs the
  default-fuel checker and proves the proof-facing statement; `borrow_check[n]`
  uses explicit fuel.  When an exact closed typing premise is needed,
  `borrow_check[n, result]` checks the expected `CheckResult` and proves the
  corresponding `TermTyping` derivation.  Term-level successful runs are
  exposed by `termTyping_of_checkTermMatches?` and
  `termListTyping_of_checkTermListMatches?`: given the maintained
  `WellFormedEnv` and store-reference invariant, a true executable
  `checkTermMatches?` or `checkTermListMatches?` result yields the inductive
  `TermTyping` or `TermListTyping` premise.  The matching proof-carrying
  bridges are `checkedTermTypingWitness_of_checkTermMatches?` and
  `certifiedTermCheck_of_checkTermMatches?`; the tactic form
  `borrow_check[n, inEnv, outEnv]` runs these term-level checks for goals whose
  environments are already written as finite `inEnv.toEnv`/`outEnv.toEnv`
  boundaries.  For accepted programs these tactics prove `borrowCheck term`
  via `borrowCheck?_sound`, not merely the boolean
  `borrowCheck? fuel term = true`.  `BorrowCheckerSoundness` then composes
  that bridge with the source-initial soundness wrappers:
  `borrowCheck?_emptyInitial_progress`,
  `borrowCheck?_emptyInitial_preservation`, and
  `borrowCheck?_emptyInitial_no_stuck_states` expose the progress,
  preservation, and no-stuckness consequences of an accepted executable run.
  `CertifiedBorrowOutcome` packages the
  proof-carrying surface used by clients: `certifyBorrowOutcome?` first runs
  the executable accepted checker and, optionally, consumes a
  `CertifiedBorrowReject`; the top-level `borrowOutcome?` boolean is the
  corresponding witness-found bit (`borrowOutcome?_eq_true_iff_witness`), and
  if it is true the witness proves either `borrowCheck term` or
  `borrowReject term` (`borrowOutcome?_sound`).  With no rejection certificate
  supplied, a true `borrowOutcome? fuel term` result projects directly to
  `borrowCheck term` (`borrowCheck_of_borrowOutcome?` and
  `borrowCheck_of_borrowOutcomeWitness`).  The term-level helper
  `checkTermFails?` uses the same unknown filter.  Logical rejection is the
  Prop `borrowReject term` and is exposed only through proof-carrying
  `CertifiedTermReject` certificates, with closed programs packaged as
  `CertifiedBorrowReject` so the same witness proves both `borrowReject term`
  and the corresponding `borrowCheckFailed? fuel term = true` verdict.
  Runtime-only reference constants are handled by the executable source-syntax
  classifier `sourceTerm?`: when the finite checker fails and `sourceTerm?`
  is false, `certifyBorrowRejectOfNonSource?` produces a
  `CertifiedBorrowReject`, with
  `borrowReject_of_certifyBorrowRejectOfNonSource?` and
  `borrowOutcomeWitness_of_certifyBorrowRejectOfNonSource?` exposing only the
  proof-facing rejection/outcome statements to examples.  The
  distinction is necessary because fuel-bounded search can fail on typable
  terms (`borrowUnknown?_zero_on_typable_unit`), and this is recorded as the
  theorem `borrowCheck?_false_not_rejection_complete`.

- **Lemma 4.11 (Preservation) uses the assignment-local borrow frame, not
  `BorrowSafeEnv`.**  The old global premise was enough to rule out dangling
  dereference-write counterexamples, but it also rejected valid joined
  environments whose conflicts are irrelevant to the write being performed.
  Preservation now gets the needed fact from `AssignmentBorrowSafety`: for a
  dereference assignment, only the roots that can supply authority for that
  dereference must be borrow-safe against the rest of the environment.  This is
  the local condition used to prove the `&mut` leaf-exclusivity bridge in the
  assignment case.

- **Runtime validity is stronger than Definition 4.3.**  `ValidRuntimeState`
  contains the paper's `ValidState`, plus explicit invariants for the abstract
  store model: store owners are allocated, store owner targets are heap
  locations, heap slots have root lifetime, and term owner targets are heap
  locations.  These are implicit in the paper's intended heap-allocation model.
  The owner-cycle fact needed by assignment is derived locally from
  `ValidPartialValue.no_owned_path_to_storage`, not assumed globally.

- **Assignment follows the reference implementation, not the printed rule.**
  The assignment step reads the overwritten slot, writes the new value, and then
  drops the overwritten old value from the post-write store.  The printed
  appendix proof appears to use the wrong order in Lemma 9.6 and omits the drop
  in the assignment case of Lemma 9.8.  Conceptually, the repaired proof first
  establishes abstraction for the post-write store, then proves that dropping
  the old owner graph preserves every value still represented by the result
  environment.

- **Fresh declaration coherence is explicit.**  `T-Declare` carries
  `FreshUpdateCoherenceObligations`.  A syntactically well-formed type such as
  an empty borrow target list can still be incoherent as an environment slot, so
  the declaration rule records the missing root-transport and fresh-root facts.

- **Assignment is strengthened.**  `T-Assign` rechecks that the lhs is typeable
  after typing the rhs, requires shape compatibility and rhs well-formedness at
  the target lifetime, and carries explicit rank/coherence obligations:
  `EnvWriteRhsBorrowTargetsBelow`, `EnvWriteCoherenceObligations`, and
  `ContainedBorrowsWellFormed` for the result.  These avoid borrow cycles and
  supply the facts needed by preservation.  The result-side obligations are
  rule-carried invariants, not extra premises on the final safety statements.

- **Borrow well-formedness is preserved per target.**  Runtime borrow
  well-formedness uses `BorrowTargetsWellFormed`, which requires each target to
  be individually typeable, outlive the borrow lifetime, have a base slot that
  survives for that lifetime.  Joint target-list typing is still required where
  coherence or shape arguments need it, but it is not used as the global
  invariant: environment joins can merge target lists whose pointee types do not
  have a joint type.

- **Well-formed environments carry extra borrow invariants.**  `WellFormedEnv`
  is augmented with `Coherent` and `Linearizable`.  `Coherent` records joint
  target-list typing for contained borrows when reborrowing needs it.
  `Linearizable` comes from the follow-up material and gives a rank function
  forbidding cyclic borrow references.

- **Progress exposes the finite-store operational assumption.**
  `OperationalStoreProgress` packages the paper's finite-store totality facts
  — fresh heap addresses exist and drops are total — as an explicit premise of
  Lemma 4.10.  This is the intended interface for the abstract partial-map
  store model and is discharged for concrete/empty stores.  Its step-stable
  form is `ProgramStore.FiniteSupport` (finitely many allocated locations),
  which implies it (`OperationalStoreProgress.of_finiteSupport`), is preserved
  by reduction (`FiniteSupport.step`), and powers the reachable-state results.

- **Theorem 4.12 is proven in the paper's total form.**  `SoundState` is the
  step-stable soundness invariant (re-established by the step theorem
  `SoundState.step`), giving progress and terminal preservation at every
  reachable state (`no_stuck_states`: no reachable state is stuck) and
  termination (`SoundState.terminatesAsValue`, via the step-decreasing size
  measure `step_size_lt`).  `theorem_4_12_typeAndBorrowSafety_total` and
  `emptyInitial_typeAndBorrowSafety_total` conclude the paper's claim —
  execution reaches a terminal value and that state is safe — with
  termination proven rather than assumed.  `SoundState` carries the
  originating typed run rather than a re-typing of the intermediate
  continuation; a literal continuation re-typing is unavailable in this
  calculus, since a declaration whose initialiser block declares the same
  variable reaches safe intermediate states whose continuation is not
  typeable (the runtime store already holds the inner variable's slot while
  `T-Declare` requires the outer binder fresh).

- **Write fan-out requires initialized typed leaves.**  `WriteBorrowTargets`
  carries an initialized full-lvalue typing witness for each concrete fan-out
  branch.  The paper's schematic fan-out rule does not spell this out; without
  it, fan-out can reinitialize `undef` leaves and break shape preservation.

- **Positive-rank weak updates make leaf shape compatibility explicit.**
  `UpdateAtPath.weak` carries the local `ShapeCompatible` premise needed for
  shape preservation.  The paper's `update_k` weak leaf case is written over a
  full old type and relies on `T-Assign`'s shape premise; the Lean relation is
  over `PartialTy`, so the full-type/compatible-leaf assumption is stated
  directly.

- **Terminal preservation/safety is source-continuation scoped.**  Lemma 4.11
  and the terminal-safety half of Theorem 4.12 assume `SourceTerm`.  Arbitrary
  runtime constants can already contain references in unevaluated continuations;
  `SourceTerm` is therefore not derivable from typability for arbitrary
  nonempty store typings.  Source-initial empty-store theorems derive it from
  typability (`termTyping_empty_sourceTerm`), so the empty-initial Lemma 4.11
  and Theorem 4.12 wrappers have no `SourceTerm` premise.

- **`R-Declare` is an update rule; freshness is proof-side.**  The small-step
  `Step.declare` constructor updates the variable slot directly.  The freshness
  condition needed by the paper-intended declaration semantics is recovered from
  `T-Declare`, safe abstraction, and preservation.  Thus the raw reduction
  relation is broader than the typed states covered by soundness.

- **Some final wrappers expose store-typing well-formedness premises.**
  Premises such as `StoreTypingRefsWellFormed` relate runtime value typing and
  store typing to environment/lifetime well-formedness.  They are proof
  interface obligations, not extra source typing rules.

- **Theorem 4.12 assumes terminal execution.**  The paper states existence of a
  terminal run, relying on termination of the core calculus.  The mechanisation
  keeps this separate: `typeAndBorrowSafety` takes an explicit
  `TerminatesAsValue` witness and proves safety for that terminal run.  The
  nontermination-friendly component is exposed as progress.

- **Progress exposes the finite-store operational assumption.**
  `OperationalStoreProgress` packages fresh-allocation, drop, assignment, and
  lifetime-drop totality facts.  This is not intended as a theorem weakening:
  it is the Lean interface for the paper's finite/well-behaved store model, and
  is discharged by concrete finite stores.

- **General runtime safety has no global borrow-safety premise.**  Arbitrary
  nonempty runtime wrappers still require source syntax, runtime validity,
  store typing, well-formed environments, safe abstraction, and the finite-store
  operational assumptions, but not `BorrowSafeEnv`.  The typing derivation
  itself supplies the local borrow-safety facts needed by assignments.
