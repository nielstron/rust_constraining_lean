# lw_rust

Lean mechanisation of the core FR/lw-rust calculus from the paper.

## Deviations from the Paper

This section records the places where the mechanised calculus, proof interface,
or runtime model is not a literal transcription of the paper.  Some entries are
proof/interface choices rather than intended semantic changes, but they still
matter when comparing theorem statements.

### Type and Borrow System

- **Variable-only source lvalues.**  The paper permits general lvalues in move,
  borrow, and borrow target positions.  The mechanisation adds `LValIsVar` to
  `T-Move`, `T-MutBorrow`, `T-ImmBorrow`, and the borrow-target invariant.
  Assignment lhs lvalues are not variable-restricted: `T-Assign` uses `EnvWrite`
  and can write through mutable references.  See `LwRust/Paper/Typing.lean`.

- **Restricted block and sequence drops.**  The paper allows general owning
  temporaries and relies on full recursive drop preservation.  The mechanised
  typing rules admit only the no-recursive-owner cases: non-final sequence
  terms must have `NonOwnerTy`, block-local slots must satisfy
  `EnvLifetimeDropSafe`, and typed blocks are restricted by
  `BlockBodySingleton`.

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

- **Borrow safety for source programs is source-scoped.**  The final
  borrow-safety corollary assumes `SourceTerm`.  Arbitrary runtime constants can
  already contain references, while the source calculus starts from values
  without embedded borrows/owners except those produced by reduction.

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
  The restriction is on the typed fragment used by the soundness proof:
  singleton typed blocks and non-owner sequence temporaries.

### Theorem Interface Notes

- **Open proof debt: Appendix 9.6 runtime update preservation.**  The assignment
  semantics and typing rule now admit owner replacement and dereference
  assignment.  The direct variable and one-step owned-dereference cases are
  mechanized, including `Box<T> := Box<T>`.  The direct mutable-reference
  fan-out case `*p := v` is also mechanized: the runtime-selected strong target
  update is transported to the weak/joined `write_k` result.  Lemma 4.11 still
  has two `sorry`s for the genuinely recursive parts of the repaired Appendix
  9.6 argument: nested owner-chain writes such as `**x := v`, and nested
  mutable-borrow fan-out where recursive `write_k` calls join all possible
  targets.  The missing runtime lemma must prove post-write abstraction first
  and then show that dropping the overwritten old owner graph preserves every
  value still represented by the result environment.

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
