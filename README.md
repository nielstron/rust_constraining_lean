# lw_rust

Lean mechanisation of the core FR calculus from the paper "A Lightweight Formalism for Reference Lifetimes and
Borrowing in Rust", extended with if/else constructs, diverging panic statements, and while loops.
It additionally includes a formalization of the extractor and completion definitions from the Rust Constraining paper and shows that the extractor is indeed complete. The main argument is around the fact that follow-up statements can only add conflicts to the type- and borrow system and thus partial code is usually more permissible than the completed code.

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

 - For ITE, we enforce BorrowSafeEnv for the resulting merged environment, and that inserting the merged type of the returned value
   into the merged environment remains borrow safe (TyBorrowSafeAgainstEnv, e.g. relevant if a borrow type is returned)..
   This removes the edge case outlined in the paper that merging type- and borrow-safe
   branches can result in an unsafe environment explicitly.
   The type system thus rejects a few more programs.

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

- **Lemma 4.11 (Preservation) carries a premises the paper does not
  have.**
   `BorrowSafeEnv Γ₁` — *likely paper bug:* the printed lemma appears false
     without it.  Counterexample sketch: `x : Box(Box int)`,
     `p ↦ &mut [*x]`, `q ↦ &mut [**x]` is well-formed with `S ∼ Γ` but not
     borrow safe (`*x ⋈ **x`); `*p = box 5` is typeable (`q`'s target is
     based at `x`, not `p`, so it does not write-prohibit `*p`) yet leaves
     `q`'s stored reference dangling into the dropped old box, breaking
     `S₂ ∼ Γ₂`.

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

- **General runtime safety exposes an initial borrow-safety premise.**  For
  arbitrary nonempty runtime store typings, the terminal-safety wrappers carry
  `BorrowSafeEnv` for the input environment.  Source-initial empty-store
  wrappers discharge this premise from the empty environment.
