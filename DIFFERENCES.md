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
removed, along with the extractor subsystem that depended on `missing`.
Consequently there are no environment joins from control flow, and the
termination of the core calculus is unconditional: every reduction step
strictly decreases term size (`step_size_lt`), and Theorem 4.12's total form
(`theorem_4_12_typeAndBorrowSafety_total`,
`emptyInitial_typeAndBorrowSafety_total`) states terminal execution plus
safety for well-typed source programs with no divergence caveats.  While the
single-target runtime preservation proof is being reassembled (see the
README's proof status), the total form is parameterized by the
terminal-safety hypothesis that the `preservation` export will discharge.

`WellFormedEnv` and its stale-aware variant are now **exactly the paper's
two-part Definition 4.8** (contained borrows well-formed, slots outlive the
current lifetime).  The `Coherent` and `Linearizable` conjuncts that earlier
versions added to the invariant are gone.

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
  historical coherence, linearizability/rank, stale-target, and rhs-target
  lifetime premises are all deleted; `Coherent`, `Linearizable`, and their
  supporting definitions no longer exist in the development.
- `T-Declare` carries one extra premise: `env₂.fresh x`.  The literal rule
  admits the shadow chain `let mut x = (let mut x = t)`; the paper's
  Section 5.2 explicitly treats redeclaration as not permitted, so this
  mechanizes paper intent (the follow-up's T-Block states the same
  assumption).

`T-Block`'s `LifetimeChild` premise formalizes the paper's ambient lexical
nesting assumption and is not a restriction.

### 2. Preservation concludes the stale-aware safety predicate

Lemma 4.11's mechanised form concludes `TerminalStateSafe` built on
`SafeAbstraction` and `ValidPartialValueWhenInitialized` — stale borrow
annotations are treated as protection tokens rather than fully
dereferenceable borrows.  With conditionals removed, stale annotations
plausibly cannot arise at all and the strict predicate may be provable; that
collapse has not been carried out.  Progress and step theorems are stated
over the same invariant, so the non-stuckness story is unaffected.

### 3. Non-initial preservation wrappers carry derived-invariant hypotheses

Beyond Definition 4.8, general (arbitrary starting state) preservation carries
`BorrowSafeEnv Γ₁` (paper Definition 4.13) and, for the strict borrow
invariant across assignment, the result-type compatibility
`TyBorrowSafeAgainstEnv` of the written type (paper Lemma 4.9's conclusion).
Both are necessary: the development contains machine-checked counterexamples
(`strict_envWrite_target_preservation_counterexample`,
`strict_assign_rule_result_counterexample`) showing strict preservation fails
from Definition-4.8-only states.  Both hypotheses discharge at the empty
initial environment, so the headline theorems match the paper's statements.

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

## Bottom line

The mechanised language is now exactly the paper's core calculus with the
follow-up's single-target borrow grammar and strong-update write, the
environment invariant is exactly Definition 4.8, and coherence and
linearizability are gone from the development entirely.  The typing rules
carry a single extra premise relative to the printed figures
(`env₂.fresh x` on `T-Declare`, mechanizing the papers' stated
no-redeclaration assumption).  The strict collapse of the stale-aware
runtime predicates is in progress (see §2).
