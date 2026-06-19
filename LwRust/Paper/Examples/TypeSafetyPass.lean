import LwRust.Paper.BorrowChecker

/-!
Accepted examples, written as readable checker inputs.

This module keeps each public example in the same shape:

* the complete example code, with each Lean line annotated by the intended
  Rust source line;
* final theorems state the inductive type/borrow-checking property, proved by
  running the executable checker through its soundness bridge.
-/

namespace LwRust
namespace Paper

open Core

/-! ## Closed scalar comparison -/

def scalarCopyComparisonExample : Term :=
  .eq
    (.val (.int 1)) -- Rust: 1
    (.val (.int 1)) -- Rust: == 1

theorem scalarCopyComparisonExample_accepted :
    borrowCheck scalarCopyComparisonExample := by
  borrow_check

/-! ## Closed if/else returning integers -/

def ifThenElseIntExample : Term :=
  .ite
    (.val (.bool true)) -- Rust: if true
    (.val (.int 1))     -- Rust: { 1 }
    (.val (.int 2))     -- Rust: else { 2 }

theorem ifThenElseIntExample_accepted :
    borrowCheck ifThenElseIntExample := by
  borrow_check

/-! ## Closed if/else with a nontrivial condition -/

def ifEqThenElseIntExample : Term :=
  .ite
    (.eq
      (.val (.int 1)) -- Rust: if 1
      (.val (.int 1))) -- Rust: == 1
    (.val (.int 1))    -- Rust: { 1 }
    (.val (.int 2))    -- Rust: else { 2 }

theorem ifEqThenElseIntExample_accepted :
    borrowCheck ifEqThenElseIntExample := by
  borrow_check

/-! ## Pointer retarget/write if -/

def pointerIfAssignmentExample : Term :=
  .block [0] [
    .letMut "x" (.val (.int 0)),        -- Rust: let mut x = 0;
    .letMut "y" (.val (.int 0)),        -- Rust: let mut y = 0;
    .letMut "p" (.borrow true (.var "x")),
      -- Rust: let mut p = &mut x;
    .ite
      (.eq
        (.copy (.deref (.var "p")))     -- Rust: if *p
        (.val (.int 1)))                -- Rust: == 1
      (.assign
        (.var "p")                      -- Rust: p
        (.borrow true (.var "y")))      -- Rust: = &mut y;
      (.assign
        (.deref (.var "p"))             -- Rust: *p
        (.val (.int 1)))                -- Rust: = 1;
  ]

theorem pointerIfAssignmentExample_accepted :
    borrowCheck pointerIfAssignmentExample := by
  borrow_check

theorem pointerIfAssignmentExample_lowFuelUnknown :
    borrowUnknownWitness 3 pointerIfAssignmentExample := by
  borrow_check[3]

end Paper
end LwRust
