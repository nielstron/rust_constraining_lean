# FW Rust conditionals

The canonical `FWRust.Paper` calculus mechanizes the control-flow extension
proposed in Section 6.1 of Pearce's FW Rust paper.  Booleans, equality,
conditionals, and finite borrow-target lists live in the same syntax, typing,
semantics, and metatheory as the core language.

## Language and dynamics

Equality evaluates its operands from left to right and produces a Boolean.
Conditionals evaluate only their guard before selecting a branch; branches are
not evaluation contexts, so the unselected branch never executes.

Conditionals merge static borrow states.  A borrow type therefore carries a
finite list of possible lvalue targets.  `PartialTyJoin` and `EnvJoin` are
relational least upper bounds, and borrow weakening corresponds to inclusion
of target sets.

## Minimal conditional rule

`TermTyping.ite` has only five premises:

1. the guard has type `bool`;
2. the true branch is typed from the post-guard environment;
3. the false branch is typed from that same environment;
4. the result type is the branch-type join; and
5. the result environment is the branch-environment join.

It does **not** assume any of the conditions added by earlier formalizations:

- same-shaped branch and join environments;
- strong well-formedness of the joined result type;
- global coherence of the joined environment;
- global linearizability, or a borrow-graph ranking, of the joined environment;
- borrow safety of the joined environment.

The proof replaces those global assumptions with facts local to their uses:

- `wellFormedTyWhenInitialized_join` derives stale-aware joined-result
  well-formedness from the branch invariants and the two joins;
- backward lvalue transport is a structural mutual induction over
  `LValTyping` and target-list typing, selecting a nonempty source subset only
  when `T-LvBor` actually dereferences a borrow; and
- assignment uses its own rank/write witnesses rather than requiring every
  static join to admit one global ranking.

The key semantic point is that a join is a static *may* approximation, not a
runtime state obtained by executing both branches.  Preservation transports
the one branch that actually ran into the join.  Targets contributed by the
other branch may remain as conservative protection tokens, but are not treated
as live runtime pointers.  [`T-IF.md`](T-IF.md) gives the proof argument in
detail.

The arbitrary-state cyclic-join regression is deliberately an independence
witness rather than a source-reachability claim: it constructs a coherent exact
join that is not linearizable and checks that a premise-free constant
conditional can still be typed and executed.

## Safety results

The metatheory covers borrow invariance, progress, single- and multi-step
preservation, and type/runtime safety.  For the terminating fragment,
`emptyInitial_typeAndBorrowSafety_total` derives a concrete value execution and
`TerminalStateSafe` from typing at the empty environment and empty store typing.
It requires both `MissingFree` and `LoopFree`, because generated `missing` terms
self-loop and source loops may diverge.

Terminal safety is intentionally stale-aware.  If one branch moves a target
that only the other branch keeps live, the joined annotation may retain that
target as a conservative protection token.  Runtime validity is required for
targets that are actually initialized; requiring every joined target to remain
fully live would reject safe programs.

## Native while loops

The canonical syntax also contains `whileLoop`, `whileCond`, and `whileBody`,
with six small-step loop rules and minimized `T-While` and `T-WhileDiv` typing
constructors.  The normal rule has exactly seven premises: lexical child
scope, an entry/back-edge environment join, weak initialized-target
well-formedness of the invariant, equality-ghost name hygiene, condition and
body typing, and the body-scope drop equality.

It does not restore the historical same-shape, coherence, global ranking,
borrow-safety, body-result well-formedness, or duplicate entry-typing premises.
Loop run decompositions and a loop-local terminal-preservation proof are
integrated into the main metatheory.  `reachableProgressWhenInitialized`
additionally proves that every finitely reachable state, including the
`whileCond` and `whileBody` phases, is terminal or can step.

See [`WHILE.md`](WHILE.md) for the rules, premise audit, transport proof, and
the distinction between reachable-state safety and termination.

## Conditional extraction

`FWRust.Sealor` extends the core frontier extractor with Boolean, equality, and
conditional syntax.  Following
`rust_constraining/constraining/src/ast_copier.rs`, it closes incomplete
branches with the polymorphic diverging `.missing` term: an absent or
incomplete else branch becomes panic, and an incomplete then branch is
completed with panic in both arms.  The accompanying proofs show that a typed
completion yields a typed sealed program and establish the conservative
prefix-checker property.

For a generic recursively incomplete `else if`, the extractor uses a
conservative statement fallback.  Reconstructing the exact outer chain would
require either synthesizing a fresh branch join or rebasing an arbitrary nested
completion into a fresh child lifetime; neither operation follows from the
current completion relation.  This boundary is explicit in the extractor and
its build-checked examples.

## Remaining local corrections

Dropping the extra `T-If` premises does not erase independently necessary
conditions elsewhere in the multi-target calculus:

- W-Bor target inclusion also reflects non-emptiness.  Source borrows are born
  with a target and joins only add targets, so this does not restrict
  source-reachable loans; it prevents an uninhabited empty loan from justifying
  a nonempty dereference after weakening.
- `T-Assign` retains local stale-target, RHS-target lifetime, rank, and
  initialized-coherence obligations.  Machine-checked counterexamples reject
  the unguarded multi-target write rule.
- `T-Declare` retains fresh-slot coherence obligations, and `T-Eq` carries the
  ghost-name hygiene needed to make its anonymous slot unaddressable by source
  syntax.

These are rule- or representation-local invariants, not assumptions on the
result of `T-If`.  Empty-initial theorems discharge the general runtime
validity, finite-support, safe-abstraction, and initial-environment hypotheses.

## Building

```sh
lake build FWRust.Paper
lake build FWRust.Sealor
lake build
```
