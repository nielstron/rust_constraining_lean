# Rust Constraining Formalization

Lean mechanisation of the core FR calculus from the paper "A Lightweight
Formalism for Reference Lifetimes and Borrowing in Rust"
(`paper/lw_rust.pdf`), with the follow-up paper's single-target borrow
grammar (`paper/lw_rust_followup.pdf`).

## Scope

The mechanised language is the paper's core calculus
(Figure 1):

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

See `emptyInitialInvariantPackage_of_typing`: from
`Env.empty`/`StoreTyping.empty`, a well-typed program starts with
`StaticInvariantPackage Env.empty lifetime` and preserves it to the output
environment.  The underlying facts are `StaticInvariantPackage.empty` and
`StaticInvariantPackage.preserve_of_sourceTerm`.

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
- **`T-Declare`'s freshness check is stated on the post-initializer `Γ₂`**
  rather than the printed `Γ₁`. We read the printed `x ∉ dom(Γ₁)` as a
  typo, since only the `Γ₂` form rejects the shadow chain
  `let mut x = (let mut x = t)` that Section 5.2 says is not permitted
  (the follow-up's `T-Block` makes the same assumption), and on well-formed
  environments `Γ₂`-freshness implies `Γ₁`-freshness.
- **`T-Block`'s `LifetimeChild` premise
  formalises the paper's ambient lexical-nesting assumption in a slightly
  stronger form** (immediate child rather than mere nesting).
- **LValBaseOutlives** Definition 4.8(i) and L-Borrow carry an extra "borrow target's base slot outlives the reference" conjunct not present in the printed definitions.
- **`R-Declare` is an update rule; freshness is proof-side.**  The raw
  reduction relation is broader than the typed states covered by
  soundness; the declaration freshness intended by the paper is recovered
  from `T-Declare` and preservation.
