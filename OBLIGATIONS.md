# Remaining Obligations

State: there is no `sorry`, `admit`, or Lean `axiom` anywhere in `LwRust/`.
The former critical gap, whole-term Lemma 4.11 preservation, is now compiled
and exported.

## Closed: Lemma 4.11 preservation

`LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean` now exports:

- `preservation_bounded`
- `preservation`
- `Soundness.lemma_4_11_preservation`

The proof follows the paper's typing induction and uses the follow-up paper's
rank/linearization cycle argument for assignment.  The final theorem concludes
`FullTerminalStateSafe`; Theorem 4.12 and the empty-initial wrappers call it
directly instead of taking a `terminalSafety` premise.

The general preservation theorem carries the proof-side invariants needed by
the mechanization:

- `BorrowSafeEnv env₁`
- `Env.FiniteSupport env₁`
- `Linearizable env₁`

For Theorem 4.12, finite environment support is derived from finite store
support plus `FullSafeAbstraction`.  Empty-initial wrappers discharge
linearization with `Linearizable.empty`.

## Optional Cleanup

The final theorem statements already conclude the strict paper predicates
(`FullTerminalStateSafe`, strict abstraction `≈ₛ`).  The per-redex helper lemmas
still use the stale-aware `WhenInitialized` family internally and upgrade at
the end (`TerminalStateSafe.full_of_wellFormed`).  Collapsing that interior to
strict predicates would simplify the development but is not needed for the
headline theorems.

## Paper-Sync Items To Keep Documented

Tracked in `DIFFERENCES.md`; listed here as potential future work:

- `LValBaseOutlives`: Definition 4.8(i) and L-Borrow carry an extra
  "borrow target's base slot outlives the reference" conjunct not present in
  the printed definitions.  Either keep documented or attempt removal.
- `T-Block`'s `LifetimeChild` requires an immediate child lifetime; the paper
  only assumes nesting.
- `T-Assign` checks the lhs typing / shape / rhs well-formedness in the
  post-rhs environment, matching the follow-up convention rather than the
  core paper's pre-rhs `Γ₁`.
- `CopyTy` counts `unit` as copyable, while printed Definition 3.6 lists only
  `int` and immutable borrows.
