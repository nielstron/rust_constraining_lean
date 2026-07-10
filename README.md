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

The mechanised language is the paper's core calculus. The repository further contains a mechanization of the corrected typing rules and operational semantics from [1] (including adaptations suggested by [2]).
Finally the repository contains the sealor and completeness/soundness techniques developed in the paper.

See `PAPER_CLAIMS.md` for a claim-by-claim map from the paper to Lean
declarations.
See `DIFFERENCES.md` for the precise, itemised comparison of changes to claims
in [1,2].

## References

[1] David J. Pearce. “A Lightweight Formalism for Reference Lifetimes and
Borrowing in Rust.” *ACM Transactions on Programming Languages and Systems*
43(1), Article 3, 2021. https://doi.org/10.1145/3443420

[2] Etienne Payet, David J. Pearce, and Fausto Spoto. “On the Termination of
Borrow Checking in Featherweight Rust.” *NASA Formal Methods (NFM 2022)*,
pages 411–430, 2022. https://doi.org/10.1007/978-3-031-06773-0_22
