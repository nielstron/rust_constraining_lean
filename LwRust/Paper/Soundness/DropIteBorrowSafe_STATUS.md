# Status: `BorrowSafeEnv` removed from join typing

Current branch status:

- `TermTyping.ite` does not require `BorrowSafeEnv` for the joined environment.
- `TermTyping.ite` still carries `TyBorrowSafeAgainstEnv env₅ joinTy` for the
  result type.
- `TermTyping.whileLoopJoin` does not require `BorrowSafeEnv` for the loop
  invariant environment.  It still carries the invariant's contained-borrow,
  coherence, and linearization obligations, plus the entry-side condition/body
  derivations needed by the conservative extractor.
- The old strengthened Corollary 4.14 claim that every static output
  environment is `BorrowSafeEnv` has been removed.  That statement is false for
  joined conditionals because joins can merge borrow target lists.
- The public Corollary 4.14 wrappers now expose the globally valid part:
  well-formedness of the static output environment.  The terminal weakening in
  Theorem 4.12 keeps terminal runtime safety and well-formed result extension,
  but deliberately omits the false static `BorrowSafeEnv` conclusion.
- Preservation and reachable progress no longer thread static `BorrowSafeEnv`
  through recursive subterm states.  Assignment now uses
  `AssignmentBorrowSafety`: direct root writes need no global borrow-safe
  environment, while dereference writes require `BorrowSafeRoot` only for the
  roots in the dereference's static `BorrowAuthorityGuard` closure.  Unrelated
  crossed-join conflicts elsewhere in the environment do not block the
  assignment premise.

Validated locally:

```sh
lake build LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety \
  LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety \
  LwRust.Paper.Soundness.InitialStates \
  LwRust.Paper.Examples.SwappedBorrowJoin \
  LwRust.Paper.Examples.WhileJoinPass \
  LwRust.Extractor
```
