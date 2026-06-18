import LwRust.Paper.Examples.Operational
import LwRust.Paper.Examples.TypeSafetyPass
import LwRust.Paper.Examples.WhileJoinPass
import LwRust.Paper.Examples.TypeSafetyReject
import LwRust.Paper.Examples.ThinningFalse
import LwRust.Paper.Examples.SwappedBorrowJoin
import LwRust.Paper.Examples.Internal.CheckerTactic

/-!
Build-checked paper examples.

The public checker-example modules are structured as readable programs ending
in checker-backed accepted, failed, unknown, or certified-rejected statements.
Accepted examples state the inductive `borrowCheck` property.  Certified
logical rejections state the inductive `borrowReject` property and include a
proof-carrying executable outcome witness.  Finite failed and unknown
executable verdicts are exposed through witness Props only when no logical
rejection certificate is available.

* `Operational` contains reduction witnesses for the operational examples.
* `TypeSafetyPass` contains accepted checker examples.
* `TypeSafetyReject` contains complete programs with proof-carrying executable
  non-acceptance verdicts and certified rejections where available.
* `WhileJoinPass` contains the accepted join-based loop example.
* `SwappedBorrowJoin` contains the crossed-borrow join examples and the local
  assignment follow-ups as complete programs.
* `Internal.CheckerTactic` contains anonymous build-checked coverage for the
  lower-level finite-environment checker tactic.
-/
