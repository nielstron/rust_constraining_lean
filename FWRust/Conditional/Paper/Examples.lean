import FWRust.Conditional.Paper.Examples.Operational
import FWRust.Conditional.Paper.Examples.NoStaleRegression
import FWRust.Conditional.Paper.Examples.TypeSafetyPass
import FWRust.Conditional.Paper.Examples.TypeSafetyReject
import FWRust.Conditional.Paper.Examples.ThinningFalse
import FWRust.Conditional.Paper.Examples.StaleBoxedBorrow
import FWRust.Conditional.Paper.Examples.BoxDerefPending
import FWRust.Conditional.Paper.Examples.LinearJoinCounterexample
import FWRust.Conditional.Paper.Examples.WhileSafety

/-!
Build-checked paper examples.

* `Operational` contains reduction witnesses for the operational examples.
* `NoStaleRegression` contains a source-shaped regression for the no-stale
  assignment side condition.
* `TypeSafetyPass` contains accepted examples with type-safety corollaries.
* `TypeSafetyReject` contains rejected examples and the specific failed premise.
* `StaleBoxedBorrow` records why stale loan annotations are conservative
  protection tokens, not necessarily live dereferenceable borrows.
* `BoxDerefPending` records declared-box lvalue examples for full box lvalue
  projection.
* `LinearJoinCounterexample` separates join coherence from global static
  linearizability and checks the premise-free constant conditional regression.
* `WhileSafety` checks a terminating loop and shows that T-While accepts an
  invariant whose live loans form a non-linearizable cycle.
-/
