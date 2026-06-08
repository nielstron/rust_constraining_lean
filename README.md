# lw_rust

Lean mechanisation of the core FR/lw-rust calculus from the paper.

## Deviations from the Paper

This section records the places where the mechanised calculus, proof interface,
or runtime model is not a literal transcription of the paper.  Some entries are
proof/interface choices rather than intended semantic changes, but they still
matter when comparing theorem statements.

### Type and Borrow System

- **Variable-only source lvalues.**  The paper permits general lvalues in move,
  borrow, assignment, and borrow target positions.  The mechanisation adds
  `LValIsVar` to `T-Move`, `T-MutBorrow`, `T-ImmBorrow`, `T-Assign`, and the
  borrow-target invariant.  This keeps preservation on variable-rooted writes;
  dereference writes would need stronger dynamic frame/path stability facts.
  See `LwRust/Paper/Typing.lean`.

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
  the target lifetime, restricts the lhs to a variable lvalue, and carries
  explicit rank/coherence obligations:
  `EnvWriteRhsBorrowTargetsBelow` and `EnvWriteCoherenceObligations`.  These
  avoid borrow cycles and supply the facts needed by preservation.

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

- **The operational semantics still has general block-list rules.**  `R-Seq`,
  `R-BlockA`, and `R-BlockB` operate on arbitrary term lists, as in the paper.
  The restriction is on the typed fragment used by the soundness proof:
  singleton typed blocks and non-owner sequence temporaries.

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
