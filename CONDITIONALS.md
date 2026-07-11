# FW Rust conditionals

`FWRust.Conditional` mechanizes the control-flow extension proposed in
Section 6.1 of Pearce's FW Rust paper.  It is kept in a separate namespace so
the reduced `FWRust.Paper` calculus and the existing sealor development retain
their current API.

## Language and dynamics

The extension adds Boolean types and values, equality, and conditionals.  Its
small-step semantics includes left-to-right equality contexts, a guard-only
conditional context, Boolean equality results, and branch selection.  Branches
are never evaluation contexts: only the selected branch executes.

Because conditionals merge borrow states, this calculus restores the paper's
finite target lists.  `PartialTyJoin` and `EnvJoin` are relational least upper
bounds; borrow weakening corresponds to target-set inclusion.

## Minimal conditional rule

`TermTyping.ite` has only the five paper-facing premises:

1. the guard has type `bool`;
2. the true branch is typed from the post-guard environment;
3. the false branch is typed from that same environment;
4. the result type is the branch-type join; and
5. the result environment is the branch-environment join.

In particular, it does **not** assume any of the following conditions used by
earlier mechanizations:

- same-shaped branch/join environments;
- strong well-formedness of the joined result type;
- global coherence of the joined environment;
- global linearizability (a borrow-graph ranking) of the joined environment;
- borrow safety of the joined environment.

The proof replaces those assumptions with facts local to their uses:

- `wellFormedTyWhenInitialized_join` derives weak joined-result
  well-formedness from the branch invariants and the two joins;
- backward lvalue transport is a structural mutual induction over
  `LValTyping` and target-list typing, selecting a nonempty source subset only
  when `T-LvBor` actually dereferences a borrow; and
- assignment uses its local rank/write witnesses rather than requiring every
  static join to admit one global ranking.

The arbitrary-state cyclic-join regression is intentionally an independence
witness, not a source-reachability claim: it constructs a coherent exact join
which is not linearizable and checks that the premise-free constant
conditional can still be typed and executed.

## Safety results

The established loop-free equality/conditional fragment proves borrow
invariance, progress, single- and multi-step preservation, and total
type/runtime safety for missing-free source programs.  Its most direct
closed-world result is
`emptyInitial_typeAndBorrowSafety_total`: typing from the empty environment and
empty store typing yields a terminating value, a concrete multistep execution,
and `TerminalStateSafe` for the joined result environment and type.

Terminal safety is deliberately stale-aware.  If one branch moves a target
that only the other branch keeps live, the joined annotation may retain that
target as a conservative protection token.  Runtime validity is required for
the targets that are actually initialized; demanding all joined targets remain
fully live would reject safe programs.

## Native while-loop work

The same namespace now contains native `whileLoop`, `whileCond`, and
`whileBody` terms, six small-step loop rules, and minimized `T-While` and
`T-WhileDiv` constructors.  The normal rule retains only an entry/back-edge
environment join, weak initialized-target well-formedness for the invariant,
ghost-name hygiene, condition/body typing, and body-scope drop equality.  It
does not restore the historical same-shape, coherence, global ranking,
borrow-safety, body-result well-formedness, or duplicate entry-typing premises.

Loop run decompositions and a loop-local finite-run terminal-preservation
helper are integrated into progress, borrow invariance, preservation, and the
headline safety wrappers.  `reachableProgressWhenInitialized` additionally
proves that every finite execution prefix, including `whileCond` and
`whileBody` phases, is terminal or can step.  `MissingFree` alone no longer
implies termination once native loops are admitted: total wrappers also require
`LoopFree`, while actual loops use the all-prefix theorem or terminal safety
conditional on `TerminatesAsValue`.

See [`WHILE.md`](WHILE.md) for the rules, premise audit, transport proof, and
proof map.

## Conditional extractor

`FWRust.Conditional.Sealor` is an isolated frontier extractor for the extended
syntax.  It follows `rust_constraining/constraining/src/ast_copier.rs` by
closing incomplete branches with the polymorphic, diverging `.missing` term:
an absent/incomplete else becomes panic, and an incomplete then branch is
completed with panic in both arms.  The accompanying Lean proofs show that a
well-typed completion yields a well-typed sealed program and establish the
conservative prefix-checker property.

For a generic recursively incomplete `else if`, the current formal extractor
uses a conservative statement fallback.  Rebuilding the exact outer chain
would require either synthesizing a fresh branch join or rebasing an arbitrary
nested completion into a fresh child lifetime; neither operation follows from
the present completion relation.  The limitation is explicit in the extractor
module and its build-checked examples.

## Remaining mechanization corrections

The absence of extra `T-If` premises does not erase independently discovered
issues elsewhere in the multi-target paper calculus:

- W-Bor target inclusion also reflects non-emptiness.  Source borrows are born
  with one target and joins only add targets, so this does not restrict
  source-reachable loans; it prevents an uninhabited empty loan from being used
  to justify a nonempty dereference after weakening.
- T-Assign retains local stale-target, RHS-target lifetime, rank, and
  initialized-coherence obligations.  The development contains
  machine-checked counterexamples to the unguarded multi-target write rule.
- T-Declare retains fresh-slot coherence obligations, and T-Eq carries explicit
  ghost-name hygiene needed to make its anonymous slot unaddressable by source
  syntax.

These are local rule or representation invariants.  None is an assumption on
the result of `T-If`.  The empty-initial headline safety theorem discharges the
general runtime validity, finite-support, safe-abstraction, and initial
environment invariants.

## Building

```sh
lake build FWRust.Conditional
lake build
```

The first command checks the extension and its examples; the second also
checks compatibility with the original core and sealor library.
