import LwRust.Paper.Examples.Operational
import LwRust.Paper.Examples.TypeSafetyPass
import LwRust.Paper.Examples.WhileJoinPass
import LwRust.Paper.Examples.TypeSafetyReject
import LwRust.Paper.Examples.ThinningFalse
import LwRust.Paper.Examples.SwappedBorrowJoin

/-!
Build-checked paper examples.

The public checker-example modules are structured as readable programs ending
in one executable checker verdict.  Proof-heavy derivations and certificates are
kept under `LwRust.Paper.Examples.Internal`.

* `Operational` contains reduction witnesses for the operational examples.
* `TypeSafetyPass` contains accepted checker examples.
* `TypeSafetyReject` contains rejected checker examples.
* `WhileJoinPass` contains the accepted join-based loop example.
* `SwappedBorrowJoin` contains the crossed-borrow join examples and the local
  assignment follow-ups as complete programs.
-/
