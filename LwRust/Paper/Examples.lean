import LwRust.Paper.Examples.Operational
import LwRust.Paper.Examples.TypeSafetyPass
import LwRust.Paper.Examples.TypeSafetyReject
import LwRust.Paper.Examples.ThinningFalse
import LwRust.Paper.Examples.StaleBoxedBorrow

/-!
Build-checked paper examples.

* `Operational` contains reduction witnesses for the operational examples.
* `TypeSafetyPass` contains accepted examples with type-safety corollaries.
* `TypeSafetyReject` contains rejected examples and the specific failed premise.
* `StaleBoxedBorrow` records why stale loan annotations are conservative
  protection tokens, not necessarily live dereferenceable borrows.
-/
