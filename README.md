# Rust Constraining Formalization

Lean mechanisation of the core FR calculus from the paper "A Lightweight
Formalism for Reference Lifetimes and Borrowing in Rust"
(`paper/lw_rust.pdf`), with the follow-up paper's single-target borrow
grammar (`paper/lw_rust_followup.pdf`).

## Scope

The mechanised language is **exactly the paper's core calculus**
(Figure 1):

- The Section 6.1 extension (booleans, equality, conditionals) and the
  synthetic diverging placeholder that earlier versions carried are removed.
  Without conditionals there are no environment joins, and every reduction
  step strictly decreases term size (`step_size_lt`), so the core calculus
  terminates unconditionally and Theorem 4.12 is stated in the paper's total
  form for source programs.
- Borrows are single-target (the follow-up's grammar) and the environment
  write is the follow-up's strong update — no weak-update unions, no
  multi-target fan-out.
- The environment invariant `WellFormedEnv` is **exactly the paper's
  two-part Definition 4.8** (contained borrows well-formed, slots outlive
  the current lifetime).  The `Coherent` and `Linearizable` conjuncts and
  premises that earlier versions added no longer exist anywhere in the
  development.
- The typing rules match the printed figures with **one** extra premise:
  `T-Declare` requires `env₂.fresh x`, mechanising the paper's Section 5.2
  statement that redeclaration is not permitted (the follow-up's `T-Block`
  makes the same assumption).  `T-Block`'s `LifetimeChild` premise
  formalises the paper's ambient lexical-nesting assumption and is not a
  restriction.

The old multi-target development — and with it the rank/linearization
witness, the stale-retarget guard, the coherence obligations, and the
fan-out premises that previous revisions of this file documented — has been
deleted; those premises were only ever needed to control weak-update
fan-out, which no longer exists.

See `DIFFERENCES.md` for the precise, itemised comparison with the paper.

## Proof status

There is no `sorry`, `admit`, or `axiom` anywhere in `LwRust/`.

- **Statics: complete.**  Lemma 4.9 (borrow invariance), Lemma 4.10
  (progress, with the finite-store interface `OperationalStoreProgress`
  made explicit), and the strict environment-preservation walk for
  Definition 4.8 across all typing rules — including the assignment
  strong-update kernel and preservation of borrow safety
  (Definition 4.13 / Corollary 4.14 content, previously unprovable in the
  multi-target system).
- **Runtime half of Lemma 4.11: being rebuilt for the single-target core**
  (this branch).  The per-redex runtime preservation helpers (moves,
  assignments, block exit) and the borrow-hop reduction kernel are proven;
  the final induction that exports `preservation` is not yet reassembled,
  so `theorem_4_12_typeAndBorrowSafety_total` is currently parameterized by
  the terminal-safety hypothesis it will discharge, and the
  `InitialStates`/`Appendix9` call sites of `preservation` do not yet
  build.  `PHASE_D_HARD_SITES.md` tracks the remaining work.

## Corrections kept relative to the printed paper

These deviations strengthen or repair the paper's claims and are intended
to stay:

- **General preservation carries `BorrowSafeEnv Γ₁` (Definition 4.13).**
  The printed Lemma 4.11 appears false without it for arbitrary starting
  states: the development contains machine-checked counterexamples showing
  strict preservation fails from Definition-4.8-only environments.  The
  premise discharges at empty initial states, so the headline theorems
  match the paper's statements.
- **Assignment follows the reference implementation, not the printed
  rule.**  The step reads the overwritten slot, writes the new value, then
  drops the old value from the post-write store; the printed appendix
  proof appears to use the wrong order in Lemma 9.6.
- **Runtime validity is stronger than Definition 4.3.**
  `ValidRuntimeState` adds the abstract-store invariants the paper's heap
  model leaves implicit (owners allocated, owner targets on the heap, heap
  slots at root lifetime).
- **Progress exposes the finite-store operational assumption.**
  `OperationalStoreProgress` (implied by `ProgramStore.FiniteSupport`,
  which is preserved by reduction) packages fresh-allocation and drop
  totality for the abstract partial-map store.
- **Terminal safety is source-continuation scoped.**  Lemma 4.11 and the
  terminal-safety half of Theorem 4.12 assume `SourceTerm`; source-initial
  empty-store wrappers derive it from typability, so the headline
  empty-initial theorems carry no extra premise.
- **`R-Declare` is an update rule; freshness is proof-side.**  The raw
  reduction relation is broader than the typed states covered by
  soundness; the declaration freshness intended by the paper is recovered
  from `T-Declare` and preservation.
- **Preservation currently concludes the stale-aware safety predicate**
  (`TerminalStateSafe` over the `WhenInitialized` value validity family),
  which treats stale borrow annotations as protection tokens.  With
  conditionals removed, stale annotations plausibly cannot arise and the
  strict predicate should be recoverable; that collapse is planned once
  the runtime rebuild is green (see `DIFFERENCES.md` §2).
