# Rust Constraining Formalization

Lean mechanisation of FWRust (FeatherWeight Rust), the core FR calculus from
the paper "A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust"
(`paper/fw_rust.pdf`), with the follow-up paper's single-target borrow
grammar (`paper/fw_rust_followup.pdf`).

## Scope

The mechanised language is the paper's core calculus (Figure 1).

See `DIFFERENCES.md` for the precise, itemised comparison with the paper.

## Corrections kept relative to the printed paper

These deviations strengthen or repair the paper's claims and are intended
to stay:

- **General preservation carries `BorrowSafeEnv Γ₁`, finite context support, and `Linearizable Γ₁`.**
  The printed Lemma 4.11 appears false without it for arbitrary starting
  states: the development contains machine-checked counterexamples showing
  strict preservation fails from Definition-4.8-only environments.  The
  linearization invariant is the follow-up paper's rank argument for
  assignment cycles; finite environment support is derived in Theorem 4.12
  from finite store support plus full safe abstraction.  These premises
  discharge at empty initial states, so the empty-initial headline theorems
  match the paper's statements.
- **Assignment follows the reference implementation, not the printed rule.**
  The step reads the overwritten slot, writes the new value, then
  drops the old value from the post-write store; the printed appendix
  proof appears to use the wrong order in Lemma 9.6.
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
- **`T-Block`'s `LifetimeChild` premise**
  formalises the paper's ambient lexical-nesting assumption in a slightly
  stronger form (immediate child rather than mere nesting).
- **LValBaseOutlives** Definition 4.8(i) and L-Borrow carry an extra "borrow target's base slot outlives the reference" conjunct not present in the printed definitions.
- **`R-Declare` is an update rule; freshness is proof-side.**  The raw
  reduction relation is broader than the typed states covered by
  soundness; the declaration freshness intended by the paper is recovered
  from `T-Declare` and preservation.
