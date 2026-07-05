# Rust Constraining Formalization

Lean mechanisation of the core FR calculus from the paper "A Lightweight
Formalism for Reference Lifetimes and Borrowing in Rust"
(`paper/lw_rust.pdf`), with the follow-up paper's single-target borrow
grammar (`paper/lw_rust_followup.pdf`).

## Scope

The mechanised language is **exactly the paper's core calculus**
(Figure 1):

- Borrows are single-target (the follow-up's grammar) and the environment
  write is the follow-up's strong update — no weak-update unions, no
  multi-target fan-out.
- The environment invariant `WellFormedEnv` is the paper's two-part
  Definition 4.8 (contained borrows well-formed, slots outlive the current
  lifetime), with one strengthening kept in part (i): a borrow target's
  *base variable's* slot must also outlive the reference
  (`LValBaseOutlives`; see `DIFFERENCES.md`).
- The typing rules match the printed figures with **one** extra premise:
  `T-Declare` requires `env₂.fresh x`, mechanising the paper's Section 5.2
  statement that redeclaration is not permitted (the follow-up's `T-Block`
  makes the same assumption).  `T-Block`'s `LifetimeChild` premise
  formalises the paper's ambient lexical-nesting assumption in a slightly
  stronger form (immediate child rather than mere nesting).

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
- **Runtime half of Lemma 4.11: complete.**  The per-redex runtime
  preservation helpers (moves, assignments including the mutable-borrow-hop
  write kernel, block exit) are proven, and the whole-term induction now
  exports `preservation` / `lemma_4_11_preservation`.  Theorem 4.12 and the
  empty-initial wrappers call preservation directly.

## Invariant package

The static part is represented in Lean by `StaticInvariantPackage`, with
`StaticInvariantPackage.empty` for the empty environment and
`StaticInvariantPackage.preserve_of_sourceTerm` for source typing.

The empty initial environment/store discharge every invariant needed by the
paper-facing soundness theorems:

- `SourceTerm term`, from typability under `StoreTyping.empty`
  (`termTyping_empty_sourceTerm`).
- Runtime validity and empty store typing
  (`emptyInitialRuntimeSoundnessHypotheses_of_typing`).
- Strict safe abstraction, `ProgramStore.empty ≈ₛ Env.empty`
  (`fullSafeAbstraction_empty`).
- Definition 4.8 well-formedness, `WellFormedEnv Env.empty lifetime`
  (`wellFormedEnv_empty`).
- Definition 4.13 borrow safety, `BorrowSafeEnv Env.empty`
  (`borrowSafeEnv_empty`).
- Finite context support, `Env.FiniteSupport Env.empty`
  (`Env.finiteSupport_empty`).
- The follow-up paper's rank invariant, `Linearizable Env.empty`
  (`Linearizable.empty`).
- Finite/runtime store progress assumptions
  (`ProgramStore.finiteSupport_empty`, `operationalStoreProgress_empty`).

For well-typed source programs, the static invariants are preserved by typing:
`typingPreservesWellFormed_of_sourceTerm` threads `WellFormedEnv`,
`BorrowSafeEnv`, `WellFormedTy`, and `TyBorrowSafeAgainstEnv`;
`typingPreservesLinearizable_of_sourceTerm` threads `Linearizable`; and
`TermTyping.finiteSupport` threads finite environment support.  At runtime,
`preservation` combines those static invariants with `FullSafeAbstraction` and
a terminal multistep to produce `FullTerminalStateSafe`.  Theorem 4.12 derives
finite environment support for arbitrary finite stores via
`Env.FiniteSupport.of_fullSafeAbstraction`, and the empty-initial wrappers use
the empty instances above.  `emptyInitialInvariantPackage_of_typing` packages
the empty base facts and the post-typing static invariants;
`emptyInitial_preservation_with_invariantPackage` adds terminal preservation.

## Corrections kept relative to the printed paper

These deviations strengthen or repair the paper's claims and are intended
to stay:

- **General preservation carries `BorrowSafeEnv Γ₁` (Definition 4.13),
  finite context support, and `Linearizable Γ₁`.**
  The printed Lemma 4.11 appears false without it for arbitrary starting
  states: the development contains machine-checked counterexamples showing
  strict preservation fails from Definition-4.8-only environments.  The
  linearization invariant is the follow-up paper's rank argument for
  assignment cycles; finite environment support is derived in Theorem 4.12
  from finite store support plus full safe abstraction.  These premises
  discharge at empty initial states, so the empty-initial headline theorems
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
- **Final statements are strict; internal helpers are stale-aware.**  The
  headline theorems conclude the strict paper predicates
  (`FullTerminalStateSafe`, strict abstraction `≈ₛ`); the per-redex helper
  lemmas still run over the stale-aware `WhenInitialized` family (stale
  borrow annotations as protection tokens) and upgrade at the end.  With
  conditionals removed, stale annotations plausibly cannot arise; the
  interior collapse is optional cleanup (see `DIFFERENCES.md` §2).
