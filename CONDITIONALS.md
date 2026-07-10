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

The extension proves borrow invariance, progress, single- and multi-step
preservation, and total type/runtime safety for missing-free source programs.
The most direct closed-world result is
`emptyInitial_typeAndBorrowSafety_total`: typing from the empty environment and
empty store typing yields a terminating value, a concrete multistep execution,
and `TerminalStateSafe` for the joined result environment and type.

Terminal safety is deliberately stale-aware.  If one branch moves a target
that only the other branch keeps live, the joined annotation may retain that
target as a conservative protection token.  Runtime validity is required for
the targets that are actually initialized; demanding all joined targets remain
fully live would reject safe programs.

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
