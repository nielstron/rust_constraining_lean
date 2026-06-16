# Status: `BorrowSafeEnv` removed from `T-If`

Current branch status:

- `TermTyping.ite` does not require `BorrowSafeEnv` for the joined environment.
- `TermTyping.ite` still carries `TyBorrowSafeAgainstEnv env₅ joinTy` for the
  result type.
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
  environment, while dereference writes still require the existing witness where
  the write frame consumes it.

Validated locally:

```sh
lake build LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety \
  LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety \
  LwRust.Paper.Soundness.InitialStates
```
