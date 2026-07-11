# FW Rust while loops

`FWRust.Paper` contains a native small-step representation of
`while` loops.  The loop is an extension beyond the loop-free calculus in the
paper.  It is native rather than a recursive desugaring into `if`: each
iteration must run the body at its lexical body lifetime, discard the body's
result, drop that lifetime, and only then return to the loop head.

The syntax, operational phases, typing rules, run decompositions, progress,
borrow invariance, terminal preservation, and all-finite-prefix no-stuck
theorem are integrated and build checked.  The total-termination wrapper is
intentionally limited to the syntactically missing- and loop-free fragment.

## Syntax and runtime phases

The source form is

```text
whileLoop bodyLifetime condition body
```

Two additional term constructors are runtime-only:

- `whileCond bodyLifetime conditionInFlight condition body` evaluates the
  current condition while retaining pristine copies for the next iteration;
- `whileBody bodyLifetime bodyInFlight condition body` evaluates the current
  scoped body while retaining the original condition and body.

Neither runtime form has a source typing rule.  Soundness reasons about them
through a typing derivation for the original `whileLoop` and a decomposition
of the concrete run.

## Six operational rules

The small-step semantics has exactly six loop rules.

1. `Step.whileStart` changes a source loop into `whileCond`, with a fresh
   in-flight copy of the original condition.
2. `Step.subWhileCond` steps only the in-flight condition, at the loop's
   ambient lifetime.
3. `Step.whileCondFalse` exits with `unit` when the condition is `false`.
4. `Step.whileCondTrue` starts
   `block bodyLifetime [body, val unit]` inside `whileBody` when the condition
   is `true`.
5. `Step.subWhileBody` steps that in-flight block.  Ordinary block semantics
   evaluates the body at `bodyLifetime`.
6. `Step.whileBodyDone` returns to `whileCond` with a fresh condition copy
   after the iteration block has finished.

The trailing `unit` in rule 4 is important.  Ordinary sequence reduction drops
the value produced by `body`; ordinary block-exit reduction then drops
`bodyLifetime`.  The next condition is not started until both events have
happened.

`WhileRunEnds` decomposes a finite run ending in a value into a false exit or
one or more complete true iterations.  `WhileRunReaches` gives the analogous
decomposition for an arbitrary finite execution prefix.

## Minimal normal T-While

Writing the term judgment as
`Gamma1 |- <t : T>^l_sigma -| Gamma2`, the normal rule is:

```text
LifetimeChild l bodyLifetime
EnvJoin GammaEntry GammaBack GammaInv
ContainedBorrowsWellFormedWhenInitialized GammaInv
LoopInvariantNameFresh GammaEntry GammaInv condition body
GammaInv  |- <condition : bool>^l_sigma          -| GammaCond
GammaCond |- <body : BodyTy>^bodyLifetime_sigma  -| GammaBody
GammaBody.dropLifetime bodyLifetime = GammaBack
----------------------------------------------------------------------- T-While
GammaEntry |- <while condition { body } : unit>^l_sigma -| GammaCond
```

These seven premises have distinct roles:

- `LifetimeChild` gives the body its lexical scope.
- `EnvJoin GammaEntry GammaBack GammaInv` states the loop-head fixed point:
  the invariant is the may-join of the first entry and a completed back edge.
- `ContainedBorrowsWellFormedWhenInitialized GammaInv` is the weak invariant
  needed by stale-aware preservation.  Full well-formedness of every stale
  target is not required.
- `LoopInvariantNameFresh` is proof hygiene for equality's anonymous ghost
  slot.  It lets ghost erasure reconstruct the condition and body typing from
  `GammaInv`; it is not a borrow-graph ranking or an aliasing premise.
- the two typing premises check the condition once at the invariant and the
  body once from the post-condition environment;
- the final equality identifies the state after the body scope is dropped
  with the back-edge input to the join.

The result environment is `GammaCond`, because every terminating execution
leaves through a final false evaluation of the condition.  Soundness itself
needs only the two upper-bound maps from entry and back edge to the invariant;
the rule retains the least-upper-bound `EnvJoin` to express the intended
precise fixed point.

## T-WhileDiv

A syntactically diverging body cannot complete a true iteration, so it has no
runtime back edge:

```text
LifetimeChild l bodyLifetime
GammaEntry |- <condition : bool>^l_sigma         -| GammaCond
GammaCond  |- <body : BodyTy>^bodyLifetime_sigma -| GammaBody
Term.Diverges body
-------------------------------------------------------------------- T-WhileDiv
GammaEntry |- <while condition { body } : unit>^l_sigma -| GammaCond
```

The body is still fully type checked.  If the guard is false, the loop exits
at `GammaCond`; if it is true, `Term.Diverges body` rules out a multistep from
the body to a value.  Consequently this rule needs no join, back-edge
well-formedness, or loop invariant.

## Why the historical premises are absent

The decisive observation is the same one used for `T-If`: an environment join
is a static may-approximation, not a concrete store in which all alternatives
coexist.  A running loop has one concrete entry or back-edge state.  The proof
transports that selected state into `GammaInv`; it never constructs a runtime
state containing both histories.

From the join, `EnvJoin.le_left` and `EnvJoin.le_right` provide

```text
GammaEntry <= GammaInv
GammaBack  <= GammaInv.
```

For either map,
`borrowTargetsInitialized_back_of_envStrengthens` reconstructs initialized
target typing in the source environment.  Then
`safeAbstractionWhenInitialized_transport_strengthening` transports the
concrete store to the invariant.  This transport is structural and local to
actual lvalue-typing derivations; it does not unfold or rank the ambient borrow
graph.

That proof architecture removes the historical premises as follows:

- No `EnvJoinSameShape` is needed.  Stale-aware validity permits a joined slot
  to forget initialization while retaining conservative protection loans.
- No global `Coherent` premise is needed.  An actual borrow dereference already
  supplies its own joint target-list typing through `T-LvBor`.
- No global `Linearizable` premise is needed.  Backward lvalue transport is
  structural; assignment retains only its existing local rank/write witness.
- No joined `BorrowSafeEnv` premise is needed.  Entry and back-edge loans are
  alternative histories, and the joined loans conservatively restrict later
  operations rather than asserting simultaneous runtime aliases.
- No `WellFormedTy GammaBody BodyTy l` premise is needed.  The iteration block
  discards the body result before dropping `bodyLifetime`; only `unit` escapes.
- No duplicate entry-side typings of the condition and body are needed.  The
  concrete entry store is transported to `GammaInv`, and every iteration uses
  the single invariant-side derivations.

The two remaining invariant premises should not be conflated with that deleted
bundle.  Weak contained-borrow well-formedness prevents an arbitrary supplied
fixed point from introducing unusable live bases.  Ghost freshness is required
only because `T-Eq` temporarily adds and later erases an anonymous environment
slot.  A future generated-fixpoint certificate could derive both facts
inductively, but the relational rule states them explicitly.

## Terminal safety and safety of divergent runs

`preservation_whileRunEnds` is the loop-local terminal argument.  It inducts on
the finite `WhileRunEnds` derivation:

- a false guard yields a safe `unit` at `GammaCond`;
- a true guard runs the body, drops its result and body lifetime, obtains a
  safe store at `GammaBack`, transports that store through the right join map
  to `GammaInv`, and continues the run induction.

This proves terminal preservation for a loop that reaches a value.  Divergent
runs are covered separately by `reachableProgressWhenInitialized`, whose
result for every finite execution prefix is

```text
every finitely reachable state is terminal or can step.
```

The proof uses `WhileRunReaches` to distinguish condition, exit, body, and
completed-iteration prefixes.  Its focused wrappers
`whileLoop_reachableProgress` and
`whileLoopDiverging_reachableProgress` expose the normal and diverging loop
rules directly.  In the normal case the public theorem lists exactly the seven
`T-While` premises above plus ordinary initial runtime hypotheses; it has no
hidden same-shape, coherence, ranking, or borrow-safety requirement.

## Termination requires both exclusions

Before native loops, excluding `.missing` was enough to recover termination of
the finite source calculus.  It is no longer enough: for example,
`while true { unit }` can be `MissingFree` and still run forever.

The syntax therefore separates two orthogonal predicates:

- `Term.MissingFree` excludes the generated `missing` self-loop;
- `Term.LoopFree` excludes `whileLoop` and its runtime-only phases.

Notably, `.missing` is `LoopFree` but not `MissingFree`, while a loop may be
`MissingFree` but is not `LoopFree`.  A theorem deriving a terminal value from
syntax must require both predicates.  General loop safety should instead be
stated without a termination conclusion, or terminal safety should remain
conditional on an explicit `TerminatesAsValue` witness.

`LoopFree`, the loop-aware size-decrease infrastructure, and the total-safety
wrappers are integrated.  The total wrappers require both predicates; the
general conditional safety theorem remains available with an explicit
`TerminatesAsValue` witness, and all-prefix progress applies without a
termination assumption.
