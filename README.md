# Rust Constraining Formalization

Lean mechanisation of the core FR calculus from the paper "A Lightweight Formalism for Reference Lifetimes and
Borrowing in Rust" (`Paper`).

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
  a plain `Coherent env₃`, the stale-retarget guard
  `EnvWriteNoStaleBorrowTargets`, and the minimal
  `EnvWriteRhsTargetsWellFormed` for the result (the broad result
  `ContainedBorrowsWellFormed` is now derived, and the former structured
  `EnvWriteCoherenceObligations` has been flattened to `Coherent env₃`; see the
  coherence-obligations deviation below),
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
    **genuinely necessary; NOT derivable**.  `Linearizable` is Definition 11
    of `lw_rust_followup.pdf`, whose Lemmas 1–4 prove in prose that the
    typing rules preserve linearizability — but only for the follow-up's
    *single-target* borrow grammar.  In FR proper, Definition 3.23's
    weak-update union creates multi-target borrows even without
    conditionals (`*q = &mut b` through `q : &mut [p]` turns `p : &mut [a]`
    into `p : &mut [a, b]`), and a reachable two-stage fan-out duplication
    followed by a fan-out write of a moved-out duplicate installs a borrow
    into its own target's slot — a rank self edge.  The witness premise
    rules such writes out; without it preservation is false as stated.
  - *Former coherence obligations* — the compatibility coherence side
    condition from the stale-aware/multi-target development has been removed
    in the current single-target branch-free core.  Remaining preservation
    work is about the strict/initialized well-formedness walk and runtime
    frame arguments, not a global coherence predicate.

    `T-Assign`'s result CBWF **is derived** (no longer a carried premise),
    but it is *not* derivable from the paper's premises alone: a write through a multi-target mutable borrow `&mut[x,z]`
    whose targets have different lifetimes fans the RHS into both slots, while
    `targetLifetime` is only the *intersection* of the targets' lifetimes, so it
    cannot bound the RHS by the longer-lived slot — the broad result CBWF was
    genuinely load-bearing there.  `T-Assign` therefore now carries the strictly
    *minimal* obligation `EnvWriteRhsTargetsWellFormed env₃ rhsTy` (only the
    RHS-origin borrow edges must outlive the slot they are injected into; the
    old-origin borrows are derived via the keystone).  That minimal obligation is
    much weaker than the broad result CBWF (e.g. it follows from it via
    `EnvWriteRhsTargetsWellFormed.of_containedBorrowsWellFormed`) and is shown to
    reject the multi-target counterexample
    (`Examples/TypeSafetyReject.lean`).
  - *No stale surviving borrow targets* (`EnvWriteNoStaleBorrowTargets`) —
    **genuinely additional relative to the printed rules**: neither
    `lw_rust.pdf`'s `T-Assign` nor the follow-up's simplified `T-Assign` has an
    equivalent premise.  The closest printed premise is
    `¬writeProhibited(Γ₃, w)`, but that only checks the assigned lvalue after the
    write.  The mechanised guard additionally says that no surviving borrow
    target in the result may read through any effective write produced by this
    assignment.  It is currently load-bearing in preservation for stale-retarget
    configurations such as writing `p` while another surviving borrow target is
    `*p`.
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

  In summary: the stale-retarget guard, the RHS-target lifetime bound, and
  the rank witness close gaps where the printed claims are false as stated
  (all three arise from Definition 3.23's multi-target write fan-out, which
  exists in the core independently of conditionals); the coherence
  obligations and the post-initialiser freshness are believed admissible for
  source programs but lack a formalised admissibility proof.

## Improvements

This section notes down changes done to the paper that strengthen its results or otherwise were necessary for correctness.
These deviations from the paper should be kept.

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
  (See the coherence-obligations deviation above for why this is not yet
  derived.)

- **Assignment is strengthened.**  `T-Assign` rechecks that the lhs is typeable
  after typing the rhs, requires shape compatibility and rhs well-formedness at
  the target lifetime.  The old rank/coherence/fan-out obligations from the
  multi-target development are gone in the current single-target branch-free
  core; the remaining proof work is to rebuild the strict write/frame
  preservation facts.

- **Borrow well-formedness is preserved per target.**  Runtime borrow
  well-formedness uses `BorrowTargetsWellFormed`, which requires each target to
  be individually typeable, outlive the borrow lifetime, have a base slot that
  survives for that lifetime.  Joint target-list typing is still required where
  coherence or shape arguments need it, but it is not used as the global
  invariant: environment joins can merge target lists whose pointee types do not
  have a joint type.

- **Well-formed environments are exactly the paper's Definition 4.8.**
  `WellFormedEnv` / `WellFormedEnvWhenInitialized` contain only the paper's two
  ingredients (contained borrows well-formed, slots outlive the current
  lifetime).  The former compatibility coherence predicate has been deleted;
  facts the old conjuncts supplied elsewhere are re-derived, notably the
  Linearizable-dependent update-self lemma (false for two-part-well-formed
  environments, which admit self-borrows) is replaced by witness-carrying
  `WriteProhibitedVia` chain lemmas that transport across writes.

- **Progress exposes the finite-store operational assumption.**
  `OperationalStoreProgress` packages the paper's finite-store totality facts
  — fresh heap addresses exist and drops are total — as an explicit premise of
  Lemma 4.10.  This is the intended interface for the abstract partial-map
  store model and is discharged for concrete/empty stores.  Its step-stable
  form is `ProgramStore.FiniteSupport` (finitely many allocated locations),
  which implies it (`OperationalStoreProgress.of_finiteSupport`), is preserved
  by reduction (`FiniteSupport.step`), and powers the reachable-state results.

- **Theorem 4.12 is proven in the paper's total form for source terms.**
  `terminatesAsValue` constructs the terminal multistep by recursion over the
  typing derivation, using preservation of evaluated subterms to recover the
  safe abstraction needed by later operations.  `step_size_lt` records the
  operational reason this works: every step strictly decreases syntax size.
  `theorem_4_12_typeAndBorrowSafety_total` and
  `emptyInitial_typeAndBorrowSafety_total` conclude the paper's claim for
  source programs — execution reaches a terminal value and that state is safe
  — with termination proven rather than assumed.

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

- **Theorem 4.12 also exposes the conditional bridge.**  The lower-level
  `typeAndBorrowSafety` theorem accepts an explicit `TerminatesAsValue`
  witness, while `theorem_4_12_typeAndBorrowSafety_total` and
  `emptyInitial_typeAndBorrowSafety_total` derive the terminal run for source
  programs.  The nontermination-friendly component remains exposed as progress.

- **Progress exposes the finite-store operational assumption.**
  `OperationalStoreProgress` packages fresh-allocation, drop, assignment, and
  lifetime-drop totality facts.  This is not intended as a theorem weakening:
  it is the Lean interface for the paper's finite/well-behaved store model, and
  is discharged by concrete finite stores.

- **General runtime safety exposes an initial borrow-safety premise.**  For
  arbitrary nonempty runtime store typings, the terminal-safety wrappers carry
  `BorrowSafeEnv` for the input environment.  Source-initial empty-store
  wrappers discharge this premise from the empty environment.
