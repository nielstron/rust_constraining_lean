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
`emptyInitial_typeAndBorrowSafety_total`) proves terminal execution plus
safety for well-typed source programs with no divergence caveats.

`WellFormedEnv` and its stale-aware variant are now **exactly the paper's
two-part Definition 4.8** (contained borrows well-formed, slots outlive the
current lifetime).  The `Coherent` and `Linearizable` conjuncts that earlier
versions added to the invariant are gone.

## Remaining differences

### 1. T-Assign and T-Declare carry premises beyond the printed rules

Each is documented in the rule docstrings (`LwRust/Paper/Typing.lean`,
`TermTyping.declare` / `TermTyping.assign`) together with the concrete gap it
closes.  Three are *provably necessary* — the printed claims are false as
stated without them — and all three stem from the multi-target fan-out of the
paper's own `write` function (Definition 3.23), which exists in the core
independently of conditionals (weak-update unions create multi-target borrow
lists, e.g. `*q = &mut b` through `q : &mut [p]` turns `p : &mut [a]` into
`p : &mut [a, b]`):

- `EnvWriteNoStaleBorrowTargets` (assign): a fan-out write affects bases other
  than `base lhs`, which `¬ writeProhibited(Γ₃, w)` never inspects, so a
  surviving borrow target could silently re-aim.
- `EnvWriteRhsTargetsWellFormed` (assign): the paper's `Γ₂ ⊢ T₂ ≽ m` bounds
  RHS-installed borrow targets only by the *intersection* of the written
  targets' lifetimes; with heterogeneous target lifetimes the longer-lived
  written slot is not bounded, breaking the result borrow invariant.
- the rank witness `∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ
  env₃ rhsTy` (assign): linearizability (the follow-up paper's acyclicity
  invariant) is *not* preserved by the bare rule.  The follow-up's Lemma 4
  covers only its single-target borrow grammar; in FR proper, a reachable
  two-stage fan-out duplication followed by a fan-out write of a moved-out
  duplicate installs a borrow into its own target's slot (a rank self edge).

Two more are believed admissible for source programs but their derivations
are open metatheory (neither paper develops it):

- `env₂.fresh x` (declare): the literal rule admits the shadow chain
  `let mut x = (let mut x = t)`; the paper's Section 5.2 explicitly treats
  redeclaration as not permitted, so this mechanizes paper intent.
- Historical target-list coherence premises from the stale-aware/multi-target
  development are no longer live in the current single-target branch-free core.
  The compatibility coherence side condition has been deleted rather than
  threaded as a trivial invariant.

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

Beyond `WellFormedEnvWhenInitialized` (paper Definition 4.8), the current
preservation rebuild no longer carries the deleted compatibility coherence
hypothesis.  `BorrowSafeEnv Γ₁` remains a likely paper bug fix (see README):
the printed lemma appears false without it (`p ↦ &mut [*x]`,
`q ↦ &mut [**x]` is well-formed but not borrow safe, and `*p = box 5` then
dangles `q`).

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

### 7. Corollary 4.14 is not reproduced

The paper's global borrow-safe-environment corollary is not established as a
theorem; `BorrowSafeEnv` preservation across assignment is in fact false for
the mechanised write relation (fan-out duplication installs the same loan
under two bases).  The development uses local prohibitions and the
rule-carried obligations instead.

## Bottom line

The mechanised language is now exactly the paper's core calculus, the
environment invariant is exactly Definition 4.8, and the headline theorem is
the paper's total Theorem 4.12 for source programs.  The typing rules carry
five extra premises relative to the printed figures: three provably necessary
(the printed system's preservation claims are false without them — all
traceable to Definition 3.23's multi-target write fan-out), and two believed
admissible but awaiting a hereditary-coherence admissibility proof.
