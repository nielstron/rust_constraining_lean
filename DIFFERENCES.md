# Differences between the Lean formalization and `paper/`

Scope: I compared the Lean development under `LwRust/Paper/` with
`paper/lw_rust.pdf` and `paper/lw_rust_followup.pdf`.  I did not treat source
comments as evidence; the references below point to the actual definitions,
constructors, or theorem statements that matter.

I did not find `sorry`, `admit`, Lean `axiom`, or unsafe proof escape hatches in
`LwRust/`.  The main issue is therefore not that proofs are unfinished, but that
some mechanized statements are stronger, weaker, or conditional compared with
the paper statements.

## Summary

The Lean development contains the core lightweight Rust syntax, lvalue typing,
borrow/read/write conflict checks, small-step semantics, progress, and
preservation infrastructure.  It also incorporates the follow-up paper's
linearizability idea and the Section 6 boolean/equality/conditional extension.

The mechanized headline result is close to the paper's Theorem 4.12 for the
terminating core calculus: Lean now proves terminal execution for source terms
that satisfy `Term.MissingFree`.  The integrated language still includes a
well-typed diverging `missing` term, so lower-level generated-term safety keeps
an explicit terminal multistep input.  Preservation also concludes a weaker
"when initialized" safety predicate rather than the full paper
safe-abstraction/value-validity conclusion.

## Major Differences

### 1. Terminal existence is proved only for missing-free terms

The paper's Theorem 4.12 states that a well-typed program evaluates to some
terminal value, using the fact that the core calculus has no looping construct.

Lean's paper-facing wrapper now requires:

- `Term.MissingFree term`, excluding the generated diverging placeholder.
- finite store support, the concrete-store condition used to discharge
  allocation/drop totality.

This is still a real integrated-language distinction:
`.missing` is part of `Term` (`LwRust/Paper/Syntax.lean:87-103`), has a self-loop
step (`LwRust/Paper/InductiveSemantics.lean:16-19`), is typable at loan-free
well-formed types (`LwRust/Paper/Typing.lean:2032-2039`), and cannot multistep to
a value (`LwRust/Paper/InductiveSemantics.lean:207-211`).

Conclusion: Lean proves the paper-style terminal-existence theorem for the
missing-free source fragment, while generated terms containing `.missing` remain
covered by the conditional terminal-safety bridge.

### 2. Preservation concludes a weaker final safety predicate

The paper's Lemma 4.11 concludes a valid final state, ordinary safe abstraction
of the output environment, and ordinary value validity at the result type.

Lean's preservation theorem requires a source-term hypothesis and concludes
`TerminalStateSafe`, not `FullTerminalStateSafe`
(`LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean:11663-11680`,
`11694-11707`).  The weaker terminal predicate uses
`SafeAbstraction` and `ValidPartialValueWhenInitialized`
(`LwRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean:50-64`).

The weak validity relation accepts a stale borrow annotation without resolving
the runtime reference through one of its static targets when the target list is
not fully initialized
(`LwRust/Paper/Soundness/Helpers/FullSafeAbstraction.lean:117-156`,
`1182-1190`).  Ordinary `ValidPartialValue` does require the reference location
to match one of the listed targets
(`LwRust/Paper/Soundness/Helpers/FullSafeAbstraction.lean:53-99`).

Conclusion: preservation is meaningful, but it is weaker than the paper's stated
full final abstraction result.  It relies on stale loan annotations being treated
as protection tokens rather than fully dereferenceable borrow values.

Important nuance: this weaker initialized invariant is not a problem for
next-step progress.  Lean has progress/step theorems stated directly over
`SafeAbstraction`, and over the same
`WellFormedEnvWhenInitialized` preservation invariant
(`LwRust/Paper/Soundness/Theorem_4_12_TypeAndBorrowSafety.lean:70-100`,
`126-140`, `247-296`).  For the purpose "a non-terminal typed current state can
step", requiring the weaker initialized invariant is stronger, not weaker.  The
difference is in the final safety guarantee: the terminal state is proved safe
only under the stale-aware initialized abstraction, not under the paper's full
borrow-target-resolving abstraction.

### 3. `WellFormedEnv` is strengthened by extra maintained invariants

The paper's Definition 4.8 has two ingredients: contained borrow targets are
well-formed and environment slots outlive the current lifetime.

Lean's `WellFormedEnv` is:

- `ContainedBorrowsWellFormed`
- `EnvSlotsOutlive`
- `Coherent`
- `Linearizable`

See `LwRust/Paper/Typing.lean:1332-1346` and `1374-1382`.  `Linearizable` is
defined by a rank function over variables
(`LwRust/Paper/Typing.lean:950-964`), reflecting the follow-up paper's cyclic
environment fix.

Conclusion: this is not a trivializing assumption, but it narrows the theorem's
input states compared with the original paper's Definition 4.8.  The original
paper's theorem is not formalized using only the original two-part environment
well-formedness condition.

### 4. Assignment typing is stricter than paper T-Assign

The paper's T-Assign checks RHS typing, LHS lvalue typing, shape compatibility,
well-formed RHS type at the target lifetime, environment write, and absence of a
write prohibition after the write.

Lean's `TermTyping.assign` adds several extra premises:

- no stale surviving borrow targets through effective writes
  (`EnvWriteNoStaleBorrowTargets`)
- a rank witness preserving linearizability through RHS borrow targets
- coherence of the result environment
- well-formedness of RHS target lists in the result environment

See `LwRust/Paper/Typing.lean:2089-2103`.  The environment write machinery also
requires branch target leaves to be fully typable when writing through mutable
borrow target fan-out (`LwRust/Paper/Typing.lean:1812-1838`).

Conclusion: the Lean assignment rule can reject programs accepted by the paper's
surface rule unless these additional obligations are derivable.  These premises
are proof-strengthening invariants, not assumptions of safety itself, but they
are part of the type system being formalized.

### 5. Declaration typing is stricter than paper T-Declare

The paper declaration rule requires the declared variable to be fresh in the
input environment and then updates the environment after typing the initializer.

Lean's declaration rule additionally requires the variable to remain fresh in the
post-initializer environment and carries explicit coherence obligations for the
fresh update (`LwRust/Paper/Typing.lean:1056-1082`, `2080-2088`).

Conclusion: this is a conservative strengthening of the source rule.  It is
reasonable for avoiding shadowing/freshness corner cases, but it is still a
difference from the stated rule.

### 6. Assignment operational semantics has a different order

In the paper's R-Assign rule, the old value is dropped before writing the new
value into the destination.

Lean's R-Assign reads the old slot, writes the new value, then drops the old
value from the post-write store
(`LwRust/Paper/InductiveSemantics.lean:48-54`).

Conclusion: the operational relation differs on arbitrary states.  This may be
observationally equivalent on the well-typed/valid fragment because owning
references are constrained, but the Lean rule is not the same small-step rule as
the paper.

### 7. Progress has an explicit store-totality hypothesis

The paper's store is a finite partial map, so fresh heap allocation, writes to
readable locations, and finite drops are available from the concrete model.

Lean's `ProgramStore` is an arbitrary function
`Location -> Option StoreSlot` (`LwRust/Paper/Runtime.lean:29-30`), so progress
requires `OperationalStoreProgress`
(`LwRust/Paper/Soundness/Lemma_4_10_Progress.lean:40-49`,
`1408-1419`).  Finite support implies this property
(`LwRust/Paper/Soundness/Lemma_4_10_Progress.lean:331-413`).

Conclusion: this is not a trivializing assumption; it compensates for a more
abstract store representation.  The paper-like finite-store case is covered, but
the most general progress theorem has an extra premise.

### 8. Runtime validity is stronger than paper valid state

Lean's `ValidState` matches the paper-style state validity fairly closely
(`LwRust/Paper/Soundness/Helpers/Validity.lean:454-463`).  Preservation and the
headline theorem use `ValidRuntimeState`, which additionally requires:

- every owned location in the store is allocated
- every store-owned reference targets a heap location
- heap slots have root lifetime
- term-owned references target heap locations

See `LwRust/Paper/Soundness/Helpers/Validity.lean:389-417`, `472-474`.

Conclusion: these are concrete-store invariants made explicit for Lean's
abstract store model.  They are restrictions on admissible initial states, not
proof holes, but the theorem is stronger in its hypotheses than the paper's
plain `ValidState`.

### 9. Borrow invariance is not the same paper-facing result

The paper's Lemma 4.9 is phrased as preserving well-formedness after extending
the output environment with a fresh result slot.

Lean's paper-facing borrow-invariance wrapper concludes
`WellFormedEnvWhenInitialized env2 lifetime`
(`LwRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean:16059-16071`).

Conclusion: the preservation infrastructure does prove substantial invariant
preservation, but the exported lemma is weaker/different from the paper's stated
fresh-result-slot well-formedness result.

### 10. Borrow-safe-environment corollary is not established as in the paper

The paper has Definition 4.13 and Corollary 4.14 for borrow-safe environments.
Lean defines `BorrowSafeEnv` (`LwRust/Paper/Typing.lean:1384-1403`), but the main
Theorem 4.12 path does not conclude the paper's global borrow-safe-environment
corollary.  The development instead relies on local read/write prohibitions,
assignment-side stale-target restrictions, coherence, and the initialized
preservation invariant.

Conclusion: the key operational non-stuckness and conditional preservation
results are present, but the paper's separate global borrow-safety corollary is
not reproduced as a matching theorem.

## Smaller or Structural Differences

### 11. The language includes extensions beyond the core paper calculus

Lean includes booleans, equality, and conditionals
(`LwRust/Paper/Syntax.lean:41-48`, `69-74`, `101-103`;
`LwRust/Paper/InductiveSemantics.lean:100-144`;
`LwRust/Paper/Typing.lean:2113-2158`).  These correspond to the paper's Section
6 extension rather than the Section 3 core.

Lean also includes `.missing`, which is not in the paper core and is the reason
the integrated theorem cannot derive termination.

Conclusion: results are for an extended language, not exactly the original core
calculus.

### 12. Lifetimes are a concrete tree order, not an arbitrary partial order

The paper presents lifetimes abstractly with an outlives partial order and active
lifetime sequencing.  Lean represents lifetimes as paths and `contains` as prefix
(`LwRust/Paper/Syntax.lean:19-24`, `82-85`), with child lifetimes represented by
immediate path extension (`LwRust/Paper/Typing.lean:323-339`).

Conclusion: this is a reasonable lexical-lifetime implementation choice, but it
is a restriction compared with an arbitrary partial-order presentation.

### 13. Follow-up linearizability is integrated but not exactly the same package

The follow-up paper introduces linearizable typing to rule out cyclic lvalue
typing and to justify termination of the type algorithm.  Lean integrates this
idea as a rank-function invariant on environments
(`LwRust/Paper/Typing.lean:950-964`) and uses it throughout well-formedness and
assignment preservation.

The Lean rank function is not stated as injective; strict decrease is enough for
well-foundedness.  The invariant also tracks live variables occurring in partial
types, so moved-out `undef` shadows are handled differently from a simple
syntactic occurrence check.

Conclusion: the important acyclicity idea from the follow-up paper is present,
but it is used as a maintained invariant for relational typing/preservation
rather than as a standalone formalization of the exact algorithmic theorem.

## Bottom Line

The formalization does not appear to smuggle in an assumption that the program is
already safe, and the proofs are not completed by obvious proof holes.  However,
the formalized results differ significantly from the papers:

- The paper's terminal-existence theorem is proved for the missing-free source
  fragment; generated `.missing` terms still use the conditional terminal-safety
  bridge.
- Preservation concludes a weaker initialized/stale-loan safety predicate.
- The type system is strengthened with coherence, linearizability, and
  assignment/declaration obligations not present in the original rules.
- The assignment step rule is ordered differently from the paper.
- Several extra runtime/store assumptions are required because the mechanization
  uses an abstract store model.

So the Lean development establishes many key elements of the papers, especially
the borrow-aware typing and non-stuckness story, but it does not establish the
paper results verbatim.
