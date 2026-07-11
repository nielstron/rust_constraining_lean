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

The mechanised language includes both the paper's reduced core calculus
(`FWRust.Paper`) and its Section 6.1 control-flow extension with equality and
conditionals (`FWRust.Conditional`).  The loop-free extension restores finite
borrow target lists and proves progress, preservation, and total empty-initial
type/runtime safety without the historical joined-environment shape,
well-formedness, coherence, or linearizability premises on `T-If`.

The conditional namespace now also contains a native while-loop syntax,
six-rule operational semantics, and minimal normal/diverging typing rules.
The loop rules are integrated through progress, weak borrow invariance,
terminal preservation, and an all-finite-prefix theorem showing that every
reachable state is terminal or can step.  The normal proof uses initialized
back-transport rather than the historical same-shape, coherence, global
ranking, or borrow-safety assumptions.  Total termination is stated only for
the separate `MissingFree` and `LoopFree` fragment.  See `WHILE.md` for the
exact rules and proof map.

The repository further contains a mechanization of the corrected typing rules
and operational semantics from [1] (including adaptations suggested by [2]),
as well as the sealor and completeness/soundness techniques developed in the
paper.

See `PAPER_CLAIMS.md` for a claim-by-claim map from the paper to Lean
declarations.
See `DIFFERENCES.md` for the precise, itemised comparison of changes to claims
in [1,2].
See `CONDITIONALS.md` for the conditional extension, its minimized `T-If`
interface, and the remaining local mechanization corrections.
See `WHILE.md` for the native loop phases, minimized `T-While` rules, and the
distinction between terminal preservation, reachable-state safety, and
termination.

`FWRust.Conditional.Sealor` provides the isolated conditional extractor:
incomplete `if` branches are closed with the typed diverging `missing` term,
following the panic insertion strategy of `rust_constraining`'s
`ast_copier.rs`, without changing the reduced-core sealor.

## References

[1] David J. Pearce. “A Lightweight Formalism for Reference Lifetimes and
Borrowing in Rust.” *ACM Transactions on Programming Languages and Systems*
43(1), Article 3, 2021. https://doi.org/10.1145/3443420

[2] Etienne Payet, David J. Pearce, and Fausto Spoto. “On the Termination of
Borrow Checking in Featherweight Rust.” *NASA Formal Methods (NFM 2022)*,
pages 411–430, 2022. https://doi.org/10.1007/978-3-031-06773-0_22
