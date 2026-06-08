# lw_rust

Lean mechanisation of the core FR/lw-rust calculus from the paper.

## Deviations from the Paper

This section records the places where the mechanised calculus, proof interface,
or runtime model is not a literal transcription of the paper.  Some entries are
proof/interface choices rather than intended semantic changes, but they still
matter when comparing theorem statements.

### Type and Borrow System

- **Variable-only move/borrow sources and borrow targets.**  The paper permits
  general lvalues in move, borrow, and borrow target positions.  The
  mechanisation still adds `LValIsVar` to `T-Move`, `T-MutBorrow`,
  `T-ImmBorrow`, and the borrow-target invariant.  Assignment lhs lvalues are
  not variable-restricted: `T-Assign` uses `EnvWrite` and can write through
  mutable references.  See `LwRust/Paper/Typing.lean`.

- **Restricted block and sequence drops.**  The paper allows general owning
  temporaries and relies on full recursive drop preservation.  The mechanised
  typing rules allow only the no-recursive-owner cases: non-final sequence
  terms must have `NonOwnerTy`, block-local slots must satisfy
  `EnvLifetimeDropSafe`, and `T-Block` types general nonempty term lists.

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

- **Full box replacement is shape-compatible only at exact type.**  The paper's
  shape relation permits owner replacement along matching box shapes.  The
  mechanisation now includes exact `Box<T>` compatibility
  (`ShapeCompatible.tyBox`) so assignment such as `Box<Int> := Box<Int>` is
  accepted, without adding a broad recursive full-box compatibility rule.

- **Borrow well-formedness is preserved per target.**  Runtime borrow
  well-formedness uses `BorrowTargetsWellFormed`, which requires each target to
  be individually typeable, outlive the borrow lifetime, have a base slot that
  survives for that lifetime, and satisfy the variable-target restriction.  Joint
  target-list typing is still required where coherence or shape arguments need
  it, but it is not used as the global invariant: environment joins can merge
  target lists whose pointee types do not have a joint type.

- **Well-formed environments carry extra borrow invariants.**  `WellFormedEnv`
  is augmented with `Coherent` and `Linearizable`.  `Coherent` records joint
  target-list typing for contained borrows when reborrowing needs it.
  `Linearizable` comes from the follow-up material and gives a rank function
  forbidding cyclic borrow references.

- **Write fan-out requires initialized typed leaves.**  `WriteBorrowTargets`
  carries an initialized full-lvalue typing witness for each concrete fan-out
  branch.  The paper's schematic fan-out rule does not spell this out; without
  it, fan-out can reinitialize `undef` leaves and break shape preservation.

- **Recursive selected-target transport is proof-side structure.**  The
  preservation proof derives `PathSelected`/`TargetsPathSelected` from
  `LValTyping` and `LValTargetsTyping` to identify the runtime-selected borrow
  target through arbitrary recursive dereference paths.  This is not an
  additional typing-rule premise; it is the structural invariant already
  enforced by lvalue and borrow-target typing.

- **Terminal preservation/safety is source-continuation scoped.**  Lemma 4.11
  and the terminal-safety half of Theorem 4.12 assume `SourceTerm`.  Arbitrary
  runtime constants can already contain references in unevaluated continuations;
  source-initial empty-store theorems derive `SourceTerm` from typability.

### Runtime and Semantics

- **`R-Declare` is an update rule; freshness is proof-side.**  The small-step
  `Step.declare` constructor updates the variable slot directly.  The freshness
  condition needed by the paper-intended declaration semantics is recovered from
  `T-Declare`, safe abstraction, and preservation.  Thus the raw reduction
  relation is broader than the typed states covered by soundness.

- **Runtime validity is stronger than Definition 4.3.**  `ValidRuntimeState`
  contains the paper's `ValidState`, plus explicit invariants for the abstract
  store model: store owners are allocated, store owner targets are heap
  locations, heap slots have root lifetime, and term owner targets are heap
  locations.  These are implicit in the paper's intended heap-allocation model.
  The owner-cycle fact needed by assignment is derived locally from
  `ValidPartialValue.no_owned_path_to_storage`, not assumed globally.

- **Heap allocation is represented by chosen natural addresses.**  `R-Box`
  chooses a fresh `.heap address` and `boxAt` stores the boxed value at root
  lifetime.  This mirrors the paper's fresh heap location rule, but exposes the
  address witness explicitly.

- **Assignment follows the reference implementation, not the printed rule.**
  The assignment step reads the overwritten slot, writes the new value, and then
  drops the overwritten old value from the post-write store.  The printed
  appendix proof appears to use the wrong order in Lemma 9.6 and omits the drop
  in the assignment case of Lemma 9.8.  Conceptually, the repaired proof first
  establishes abstraction for the post-write store, then proves that dropping
  the old owner graph preserves every value still represented by the result
  environment.

- **The operational semantics still has general block-list rules.**  `R-Seq`,
  `R-BlockA`, and `R-BlockB` operate on arbitrary term lists, as in the paper.
  The typed fragment now also permits general block term lists; the remaining
  sequence restriction is that non-final temporaries must have `NonOwnerTy`.

### Theorem Interface Notes

- **Termination is not hidden in progress.**  The local progress theorem returns
  `ProgressResult store lifetime term` without a termination premise.  The
  terminal safety wrapper is conditional on `TerminatesAsValue`; it does not
  prove global termination.

- **Corollary 4.14 uses the core strengthening.**  The mechanised core result
  exposes the stronger equality-shaped output environment rather than the
  paper's more future-proof `Gamma2 >= Gamma3` shape.  That weakening relation
  should be reintroduced for control flow, loops, and recursive calls.

- **Some final wrappers expose store-typing well-formedness premises.**
  Premises such as `StoreTypingRefsWellFormed` relate runtime value typing and
  store typing to environment/lifetime well-formedness.  They are proof
  interface obligations, not extra source typing rules.
