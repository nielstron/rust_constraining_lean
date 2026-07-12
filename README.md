# Rust Constraining Formalization

Lean mechanisation of FWRust (FeatherWeight Rust), the core FR calculus from
the paper "A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust"
[1], with the follow-up paper's corrections for non-cyclicity [2].

## Setup

Install Lean through [elan](https://github.com/leanprover/elan), then run from
the repository root:

```sh
lake build
```

The pinned Lean toolchain and dependencies are specified by `lean-toolchain`
and `lake-manifest.json`; Lake retrieves them automatically.  To use Mathlib's
precompiled cache before building, optionally run `lake exe cache get`.

## Scope

`FWRust.Paper` is the canonical calculus.  It contains the core language,
finite borrow-target lists, Booleans and equality, Section 6.1 conditionals,
and a native while-loop extension.  It also contains the corrected typing
rules and operational semantics from [1], including the non-cyclicity lessons
from [2].

The conditional metatheory proves progress, preservation, and total
empty-initial type/runtime safety for the missing- and loop-free fragment.  Its
five-premise `T-If` rule does not assume the historical same-shape, joined
well-formedness, coherence, global linearizability, or joined borrow-safety
conditions.  The key is to treat a join as a static may-approximation and
transport only the branch that actually ran, using stale-aware initialized
validity.  See `T-IF.md` for the argument.

Loops have a source form, two runtime phases, six reduction rules, and minimal
normal and diverging typing rules.  The proofs cover progress, weak borrow
invariance, terminal preservation, and every finite execution prefix.  The
normal loop rule similarly avoids historical same-shape, coherence, global
ranking, and borrow-safety premises.  Because loops can diverge, the theorem
that derives termination from syntax requires both `MissingFree` and
`LoopFree`; loop programs instead use the all-prefix no-stuck theorem or
terminal safety conditional on a terminating run.  See `WHILE.md`.

`FWRust.Sealor` is the corresponding frontier extractor and generative-compiler
development.  It retains the core let/assignment/box/borrow/copy frontiers and
adds Boolean, equality, conditional, and native-while syntax.  Its generated
loop frontiers are `whileStart`, `whileCondition`, and `whileBody`.  Once the
guard is complete, partial bodies follow `ast_copier.rs`: for example,
`while x { xxx;` becomes the ordinary FW Rust term
`while x { xxx; missing }`.  No extractor-only loop term is added.  The
bottom-effect rule for diverging `missing` lets it inherit the omitted suffix's
static output environment, subject to finite-support and weak-well-formedness
certificates derived from the typed completion.  The proof therefore reuses
the completion's invariant-side guard typing and does not restore historical
entry-side `T-While` premises.  Conservative `MayMentions` hygiene treats the
unknown suffix as potentially mentioning every name.  Before a complete guard
exists, `whileStart` and `whileCondition` conservatively seal to `missing`.
Incomplete conditional branches use the same diverging placeholder.

See `PAPER_CLAIMS.md` for a claim-by-claim map from the paper to Lean
declarations.
See `DIFFERENCES.md` for the precise, itemised comparison of changes to claims
in [1,2].
See `CONDITIONALS.md` for the conditional extension, its minimized `T-If`
interface, and the remaining local mechanization corrections.
See `WHILE.md` for the native loop phases, minimized `T-While` rules, and the
distinction between terminal preservation, reachable-state safety, and
termination.

## References

[1] David J. Pearce. “A Lightweight Formalism for Reference Lifetimes and
Borrowing in Rust.” *ACM Transactions on Programming Languages and Systems*
43(1), Article 3, 2021. https://doi.org/10.1145/3443420

[2] Etienne Payet, David J. Pearce, and Fausto Spoto. “On the Termination of
Borrow Checking in Featherweight Rust.” *NASA Formal Methods (NFM 2022)*,
pages 411–430, 2022. https://doi.org/10.1007/978-3-031-06773-0_22
