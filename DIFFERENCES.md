# Differences between the Lean formalization and the published FR papers

This comparison describes the canonical `FWRust.Paper` calculus.  It contains
the paper's core language, its Section 6.1 Boolean/equality/conditional
extension, finite borrow-target lists, and the additional while-loop
formalization described in `WHILE.md`.

### 1. Rule premises relative to the printed figures

The canonical calculus uses the paper's finite lists of possible borrow
targets.  Conditionals join alternative branch states, and environment writes
therefore implement the corresponding weak-update fan-out.  This differs from
the follow-up paper's reduced single-target presentation.

Deviations and explicit repairs in the core rules are:

- `T-Block`'s `LifetimeChild` premise formalizes the paper's ambient lexical
  nesting assumption in a slightly stronger form: the block lifetime must be
  an immediate child of the enclosing one, where the paper assumes nesting.
- `T-Assign` checks the lhs typing, shape compatibility, and rhs
  well-formedness in the post-rhs environment `env₂`; the printed core rule
  types the lhs in the pre-rhs environment `Γ₁` (the follow-up rule also uses
  the post-rhs environment).
- `T-Assign` additionally carries local stale-target, RHS-target lifetime,
  rank/write, and initialized-coherence obligations.  These are witnesses for
  this particular write, not global assumptions on every environment join.
  Machine-checked counterexamples show that the unguarded multi-target write
  rule does not preserve the required invariant.
- `T-Declare` checks freshness both before and after its initializer and carries
  fresh-slot coherence obligations.  Post-initializer freshness rejects a
  shadow chain such as `let mut x = (let mut x = t)`, which Section 5.2 rules
  out.
- `CopyTy` counts `unit` and Section 6.1's `bool` as copyable in addition to
  `int` and immutable borrows.
- `L-Borrow` uses strengthened `BorrowTargetsWellFormedInSlot` and
  `BorrowTargetsWellFormed` predicates: each also requires a borrow target's
  base-variable slot to outlive the reference.  The printed Definition 4.8(i)
  does not constrain that base slot through an arbitrary lvalue path.
- Borrow strengthening reflects target-list non-emptiness.  This prevents an
  uninhabited empty loan from being strengthened into a usable dereference;
  source borrows are born nonempty and joins only add targets.
- `T-Eq` explicitly records hygiene for its anonymous ghost slot.  The slot
  keeps the left operand live while typing the right operand and must be
  unaddressable by source syntax before it is erased.

### 2. The conditional rule is deliberately premise-minimal

The canonical `T-If` constructor has only guard typing, two branch typings, a
type join, and an environment join.  It does not assume same-shaped branch and
join environments, joined strong type well-formedness, global joined
coherence, a global borrow-graph ranking, or joined `BorrowSafeEnv`.

Earlier proofs treated a join as though both branches had executed into one
runtime store.  The Lean proof instead transports only the selected branch
through the join's upper-bound map.  Its initialized-target invariant
distinguishes live runtime information from stale protection information, and
backward lvalue transport is structural over the finite typing derivation.
The needed weak joined well-formedness is derived.  `T-IF.md` gives the full
premise-by-premise explanation.

### 3. Metatheorem interfaces and the strong borrow-safety claim

General progress makes the abstract store's step-readiness explicit through
`OperationalStoreProgress`.  General terminal preservation assumes a source
continuation, runtime and store-typing validity, a well-formed input
environment, and safe abstraction.  These assumptions describe the concrete
starting state.  Global joined coherence, linearizability, and borrow safety
are not hidden preservation premises; assignment and declaration carry their
necessary obligations locally in the typing derivation.

The source-initial wrappers derive source syntax, runtime/store validity,
finite support, safe abstraction, and initial well-formedness from typing at
the empty environment and empty store typing.

The repository does not claim the old standalone strong Corollary 4.14 that
every target retained in a generalized joined annotation is a live runtime
borrow.  Such a target can be stale protection information from the branch
that did not run.  The mechanized guarantee is instead `TerminalStateSafe`,
whose `WhenInitialized` validity obligations require full target validity only
for targets that are actually initialized.  This is the property preserved by
conditionals without rejecting safe programs.

### 4. Native while loops are beyond the paper

`whileLoop` and the runtime-only `whileCond` and `whileBody` phases are an
extension beyond Pearce (2021).  Six operational rules ensure that each body
runs at its lexical lifetime, its result is discarded, and that lifetime is
dropped before the next guard evaluation.

The normal `T-While` rule has seven premises: `LifetimeChild`, an entry/back
edge `EnvJoin`, weak initialized-target well-formedness of the invariant,
equality-ghost name hygiene, invariant-side condition and body typing, and the
body-scope drop equality.  It does not assume same shape, global coherence,
global ranking, joined borrow safety, body-result well-formedness, or duplicate
entry-side typings.  `T-WhileDiv` has four premises because a syntactically
diverging body has no completed back edge.

Safety for loops is not a termination claim.  The all-prefix theorem says that
every finitely reachable state is terminal or can step.  Total terminal-safety
wrappers require both `MissingFree` and `LoopFree`.

### 5. Operational-rule differences

Lean's R-Assign reads the old slot, writes the new value, then drops the old
value from the post-write store.  This follows the reference implementation's
order rather than the printed drop-then-write rule; the printed appendix proof
appears to use the write-then-drop order in Lemma 9.6.

Lean's raw R-Declare relation is an update rule and does not itself require a
fresh variable.  Freshness follows from `T-Declare` for typed states, so the
untyped reduction relation is broader than the soundness theorem's domain.

### 6. Abstract store model

`ProgramStore` is an arbitrary `Location → Option StoreSlot`.  Progress
therefore takes `OperationalStoreProgress`, which finite support implies, and
runtime validity adds concrete-store invariants: owners are allocated, owner
targets are on the heap, and heap slots have the root lifetime.  These package
the paper's implicit finite heap model.

### 7. Lifetimes are a concrete tree order

Lifetimes are paths ordered by prefix, the canonical lexical-nesting model,
rather than an arbitrary partial order.
