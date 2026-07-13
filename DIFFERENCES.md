# Differences between the Lean formalization and the published FR papers

### 1. Rule premises relative to the printed figures

Borrows are single-target (the follow-up paper's grammar): without
conditionals there are no joins, so target lists — which only ever modelled
join uncertainty — are gone, and the `write` function is the follow-up's
strong update (no weak-update unions, no fan-out).

Smaller deviations in and around the rules:

- `T-Block`'s `LifetimeChild` premise formalizes the paper's ambient lexical
  nesting assumption in a slightly stronger form: the block lifetime must be
  an *immediate* child of the enclosing one, where the paper only assumes
  nesting.
- `T-Assign` evaluates the lhs typing, shape compatibility, and rhs
  well-formedness in the post-rhs environment `env₂`; the printed core rule
  types `w : ⟨T̃₁⟩^m` in the pre-rhs `Γ₁` (the follow-up's rule also uses the
  post-rhs environment).
- `T-Declare` checks freshness in the post-initializer environment `Γ₂`, not
  the printed `Γ₁`.  Only the `Γ₂` form rejects a shadow chain such as
  `let mut x = (let mut x = t)`, which Section 5.2 rules out.  On well-formed
  environments, `Γ₂`-freshness also implies `Γ₁`-freshness.
- `CopyTy` additionally counts `unit` as copyable; printed Definition 3.6
  lists only `int` and immutable borrows (the follow-up's complement
  characterization agrees with the Lean definition).
- `L-Borrow` uses strengthened `BorrowTargetsWellFormedInSlot` (Definition
  4.8(i)) and `BorrowTargetsWellFormed` predicates: each carries a third
  conjunct requiring the borrow target's base-variable slot to outlive the
  reference.  The printed definitions only require
  `Γ ⊢ w : ⟨T⟩^m ∧ m ≥ n`; since lvalue typing returns the target's lifetime
  without constraining intervening base slots, this is a genuine extra
  requirement of the mechanisation.

### 2. Non-initial preservation wrappers carry derived-invariant hypotheses

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

Terminal preservation is scoped to source continuations: Lemma 4.11 and the
terminal-safety part of Theorem 4.12 take a `SourceTerm` premise.  The
empty-store, empty-environment wrappers derive this premise from typability,
so the headline source-initial theorems do not expose it.

### 3. Operational-rule differences

Lean's R-Assign reads the old slot, writes the new value, then drops the old
value from the post-write store — the reference implementation's order rather
than the printed rule's drop-then-write (the printed appendix proof appears
to use the wrong order in Lemma 9.6).

Lean's raw R-Declare relation is an update rule and does not itself require a
fresh variable.  Freshness is recovered from `T-Declare` for the typed states
covered by preservation; the untyped reduction relation is consequently
broader than the soundness theorem's domain.

### 4. Abstract store model premises

`ProgramStore` is an arbitrary `Location → Option StoreSlot`; progress
therefore takes `OperationalStoreProgress` (implied by finite support), and
runtime validity (`ValidRuntimeState`) adds concrete-store invariants (owners
allocated, owner targets on the heap, heap slots at root lifetime).  These
package the paper's implicit finite heap model.

### 5. Lifetimes are a concrete tree order

Lifetimes are paths with prefix order, the canonical lexical-nesting model,
rather than an arbitrary partial order.
