# Differences between the Lean formalization and `paper/`

Scope: comparison of the Lean development under `LwRust/Paper/` with
`paper/lw_rust.pdf` (the core FR calculus) and `paper/lw_rust_followup.pdf`.
The references point to actual definitions, constructors, or theorem
statements, not source comments.

There is no `sorry`, `admit`, Lean `axiom`, or other proof escape hatch in
`LwRust/`.

## Summary

The formalization now covers **exactly the paper's core calculus** (Figure 1):
the Section 6.1 extension (booleans, equality, conditionals) and the synthetic
diverging `missing` placeholder that earlier versions carried have been
removed.  The restored extractor subsystem is cut back to the current core
syntax and uses the core `ϵ`/unit term for expression holes while omitting
unavailable statement-position fragments, rather than reintroducing `missing`.
Consequently there are no environment joins from control flow, and the
termination of the core calculus is unconditional: every reduction step
strictly decreases term size (`step_size_lt`), and Theorem 4.12's total form
(`theorem_4_12_typeAndBorrowSafety_total`,
`emptyInitial_typeAndBorrowSafety_total`) states terminal execution plus
safety for well-typed source programs with no divergence caveats.  The
single-target runtime preservation proof is compiled and exported as
`preservation` / `lemma_4_11_preservation`; Theorem 4.12 and the empty-initial
wrappers call it directly rather than carrying a terminal-safety assumption.

`WellFormedEnv` and its stale-aware variant are the paper's two-part
Definition 4.8 (contained borrows well-formed, slots outlive the current
lifetime).  The old `Coherent` conjunct is gone.  The follow-up paper's
`LinearizedBy`/`Linearizable` rank vocabulary is restored as proof-side
infrastructure for the assignment cycle argument, but it is not a conjunct of
`WellFormedEnv` and is not a typing-rule premise.  One strengthening remains
in part (i) — and likewise in `WellFormedTy`'s L-Borrow case: the borrow
target's *base variable's* slot must also outlive the reference
(`LValBaseOutlives`), a conjunct not present in the printed definitions (see
§1a below).

## Remaining differences

### 1. Rule premises relative to the printed figures

Borrows are single-target (the follow-up paper's grammar): without
conditionals there are no joins, so target lists — which only ever modelled
join uncertainty — are gone, and the `write` function is the follow-up's
strong update (no weak-update unions, no fan-out).  With that, every
previously-necessary extra premise became removable:

- `T-Assign` carries exactly the paper's six premises (rhs typing, lvalue
  typing, shape compatibility, rhs well-formedness at the target lifetime,
  the environment write, and `¬ writeProhibited` on the result).  The
  historical coherence, rank, stale-target, and rhs-target lifetime premises
  are not rule premises.  `LinearizedBy`/`Linearizable` exist only as
  follow-up-paper proof infrastructure for preservation's cycle exclusion.
- `T-Declare` carries one extra premise: `env₂.fresh x`.  The literal rule
  admits the shadow chain `let mut x = (let mut x = t)`; the paper's
  Section 5.2 explicitly treats redeclaration as not permitted, so this
  mechanizes paper intent (the follow-up's T-Block states the same
  assumption).

Smaller deviations in and around the rules:

- `T-Block`'s `LifetimeChild` premise formalizes the paper's ambient lexical
  nesting assumption in a slightly stronger form: the block lifetime must be
  an *immediate* child of the enclosing one, where the paper only assumes
  nesting.
- `T-Assign` evaluates the lhs typing, shape compatibility, and rhs
  well-formedness in the post-rhs environment `env₂`; the printed core rule
  types `w : ⟨T̃₁⟩^m` in the pre-rhs `Γ₁` (the follow-up's rule also uses the
  post-rhs environment).
- `CopyTy` additionally counts `unit` as copyable; printed Definition 3.6
  lists only `int` and immutable borrows (the follow-up's complement
  characterization agrees with the Lean definition).

### 1a. `LValBaseOutlives` strengthening of Definition 4.8(i) / L-Borrow

`BorrowTargetsWellFormedInSlot` (Definition 4.8(i)) and
`BorrowTargetsWellFormed` (L-Borrow, reached through `WellFormedTy` premises
of `T-Block` and `T-Assign`) each carry a third conjunct: the slot of the
borrow target's base variable must outlive the reference.  The printed
definitions only require `Γ ⊢ w : ⟨T⟩^m ∧ m ≥ n`; since lvalue typing
returns the target's lifetime without constraining intervening base slots,
this is a genuine extra requirement of the mechanisation.

### 2. Final statements are strict; the stale-aware family is internal

The headline theorem statements conclude the strict paper predicates
(`FullTerminalStateSafe`: strict abstraction `≈ₛ` plus `ValidValue`),
matching the paper's `S₂ ∼ Γ₂` and value validity.  The per-redex
preservation helpers in the development still run over the stale-aware
`WhenInitialized` family — stale borrow annotations treated as protection
tokens rather than fully dereferenceable borrows — and upgrade to the strict
form at the end (`TerminalStateSafe.full_of_wellFormed`).  With conditionals
removed, stale annotations plausibly cannot arise at all; collapsing the
interior to the strict predicates is optional cleanup
(`OBLIGATIONS.md` §2).

### 3. Non-initial preservation wrappers carry derived-invariant hypotheses

Beyond Definition 4.8, general (arbitrary starting state) preservation carries
`BorrowSafeEnv Γ₁` (paper Definition 4.13), finite environment support, and
the follow-up paper's `Linearizable Γ₁` rank invariant.  The rank invariant is
used exactly for the assignment-cycle exclusion; it is not a typing-rule
premise.  The finite-environment premise is derived in Theorem 4.12 from
finite store support plus full safe abstraction.  These hypotheses are
necessary: the development contains machine-checked counterexamples
(`strict_envWrite_target_preservation_counterexample`,
`strict_assign_rule_result_counterexample`) showing strict preservation fails
from Definition-4.8-only states.  They discharge at the empty initial
environment, so the empty-initial headline theorems match the paper's
statements.

### 4. Assignment operational semantics order

Lean's R-Assign reads the old slot, writes the new value, then drops the old
value from the post-write store — the reference implementation's order rather
than the printed rule's drop-then-write (the printed appendix proof appears
to use the wrong order in Lemma 9.6).

### 5. Abstract store model premises

`ProgramStore` is an arbitrary `Location → Option StoreSlot`; progress
therefore takes `OperationalStoreProgress` (implied by finite support), and
runtime validity (`ValidRuntimeState`) adds concrete-store invariants (owners
allocated, owner targets on the heap, heap slots at root lifetime).  These
package the paper's implicit finite heap model.

### 6. Lifetimes are a concrete tree order

Lifetimes are paths with prefix order, the canonical lexical-nesting model,
rather than an arbitrary partial order.

### 7. Corollary 4.14 is not reproduced as a standalone theorem

The paper's global borrow-safe-environment corollary is not established as a
separate theorem; borrow safety is instead threaded as a preservation
hypothesis/conclusion pair.  (The old fan-out counterexample to its
preservation died with multi-target borrows.)
