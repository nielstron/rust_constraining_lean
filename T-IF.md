# Why T-If needs only five premises

The key insight is that a join is a static *may* approximation, not a runtime
state obtained by executing both branches.

If the true branch runs, preservation gives safety for its result environment
and type, `(Γ₃, T₃)`. The joins provide

```text
Γ₃ ⊑ Γ₅        T₃ ⊑ T₅
```

so only that selected state must be transported to `(Γ₅, T₅)`. The false
branch contributes possible static information, but its loans and values do not
simultaneously exist at runtime. The false case is symmetric.

This observation requires separating two notions that historical
formalizations conflated:

- **live information:** currently dereferenceable values and borrow targets;
- **protection information:** stale targets retained conservatively to prohibit
  unsafe writes.

Consequently, the preservation proof uses `WellFormedTyWhenInitialized` and
`ValidPartialValueWhenInitialized`. A target's base must remain valid, but full
target typing is required only when the target is actually initialized. Strong
`WellFormedTy` at the join is intentionally not claimed: it can be false after
one branch moves a value.

The final [`TermTyping.ite`](FWRust/Conditional/Paper/Typing.lean) rule therefore
has only five premises:

1. the guard has type `bool`;
2. the true branch is typed from the post-guard environment;
3. the false branch is typed from the same environment;
4. the result type is the branch-type join; and
5. the result environment is the branch-environment join.

## Why the historical premises can be dropped

### Same-shaped branch and join environments

`EnvJoinSameShape` is unnecessary because a join may legitimately forget
initialization information, for example

```text
ty T ⊔ undef T = undef T.
```

On the live path, the runtime store may still contain the value even though the
joined static environment conservatively says that the slot cannot be used as
initialized. Stale-aware validity supports exactly this loss of static
knowledge, so preservation does not need a same-shape transport.

### Strong well-formedness of the joined result type

Weak well-formedness is derived rather than assumed. Every borrow target in the
joined result type originates in one of the branch result types. The branch
invariant supplies that target's base-slot and lifetime information, and the
environment join transports the base slot while preserving its lifetime. If
the target is actually initialized in the joined environment, its typing
lifetime is bounded directly in that environment.

This argument is implemented by
[`wellFormedTyWhenInitialized_join`](FWRust/Conditional/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean)
and packaged with joined environment well-formedness by
[`wellFormedWhenInitialized_iteJoin_of_obligations`](FWRust/Conditional/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean).

The proof deliberately avoids transporting a full target typing from a branch
to the join. A moved-out target need not remain initialized merely because its
loan annotation survives as a protection token.

### Global joined coherence

An environment join can union borrow-target lists whose targets do not have one
common joint type. Requiring every borrow annotation in the joined environment
to have a joint target-list typing is therefore stronger than the operational
semantics needs.

An actual borrow dereference cannot exploit an incoherent or stale annotation:
`T-LvBor` itself contains an `LValTargetsTyping` premise. Thus the proof uses
joint typing locally, exactly at a dereference that has already established it,
instead of requiring global `Coherent` or `CoherentWhenInitialized` evidence for
the entire joined environment.

### Global linearizability

The historical backward-transport proof recursively unfolded the ambient
borrow graph, so it required a global ranking to justify termination. The
revised
[`lvalTyping_back_of_envStrengthens`](FWRust/Conditional/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean)
instead performs mutual structural induction over an actual finite
`LValTyping`/`LValTargetsTyping` derivation.

In its borrow case:

1. borrow strengthening reveals a source target list contained in the result
   target list;
2. the mutual induction hypotheses transport precisely those member typings
   backward;
3. `LValTargetsTyping.of_nonempty_members_bounded` reconstructs the source
   target-list derivation; and
4. the reconstructed result is used to rebuild the source dereference.

Static cycles are therefore harmless unless an operation supplies an actual
finite derivation that traverses them. No rank is needed merely to type or
preserve a conditional in an arbitrary static environment.

### Global joined borrow safety

Loans contributed by different branches are alternatives, not simultaneous
runtime aliases. Their path-insensitive union may fail a global
`BorrowSafeEnv` predicate even though either concrete execution is safe. The
joined annotations remain conservative protection tokens and can make later
operations less permissive; they do not assert that both branch-local pointers
exist at runtime.

The runtime proof consequently transports the selected branch's store
abstraction and value validity through ordinary strengthening. It does not
interpret the join as a concrete state in which both branches executed.

## The preservation argument

In the `T-If` case of
[`preservation_bounded`](FWRust/Conditional/Paper/Soundness/Lemma_4_11_Preservation.lean),
the operational semantics first identifies the selected branch. Its induction
hypothesis gives terminal safety for that branch environment and result type.
The unselected branch is used only to derive its weak static well-formedness
from its typing derivation.

The proof then:

1. derives weak contained-borrow well-formedness for the environment join;
2. uses `EnvJoin.left_le` or `EnvJoin.right_le` for the selected branch;
3. transports initialized-target evidence backward with
   `borrowTargetsInitialized_back_of_envStrengthens`;
4. obtains result-type strengthening from the type join; and
5. applies `TerminalStateSafe.strengthen_join_strengthening`.

Thus the joined weak environment invariant, joined weak result-type invariant,
safe store abstraction, and terminal value validity are all derived. Joined
same-shape, coherence, linearizability, and borrow safety are neither assumed
nor reconstructed.

## The necessary local correction

The proof is not obtained by deleting every condition indiscriminately. W-Bor
strengthening retains the non-emptiness reflection condition

```text
rightTargets != [] -> leftTargets != [].
```

Without it, `&[] ⊑ &[x]` could produce a real dereference derivation after
strengthening even though no nonempty source target-list derivation could be
reconstructed. Source borrows are born nonempty and joins only add targets, so
this condition does not reject source-reachable loans.

Ranking also remains where it is genuinely used: `T-Assign` carries a local
rank/write witness for the particular mutation being performed. `T-Declare`
retains its fresh-slot coherence obligations, and equality retains its ghost
name hygiene. None of these is an assumption on every `T-If` join.

## Evidence that ranking is not hidden

[`LinearJoinCounterexample.lean`](FWRust/Conditional/Paper/Examples/LinearJoinCounterexample.lean)
constructs an exact coherent environment join and proves that it is not
`Linearizable`. A constant conditional nevertheless types with the five-premise
`T-If` rule and executes to a value in that environment. This is deliberately
an arbitrary-static-state independence witness, not a claim that the cyclic
environment is reachable from an empty source program.

The closed-world result
[`emptyInitial_typeAndBorrowSafety_total`](FWRust/Conditional/Paper/Soundness/InitialStates.lean)
then proves concrete evaluation to a value and `TerminalStateSafe` for
missing-free programs typed from the empty environment, without any global
same-shape, coherence, or linearizability premise on conditional joins.
