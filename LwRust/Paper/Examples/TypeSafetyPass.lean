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

/-! ## Joined reborrows keep runtime branch correlation -/

def swappedBorrowJoinA : LVal := .var "a"
def swappedBorrowJoinB : LVal := .var "b"
def swappedBorrowJoinC : LVal := .var "c"
def swappedBorrowJoinD : LVal := .var "d"
def swappedBorrowJoinX : LVal := .var "x"
def swappedBorrowJoinY : LVal := .var "y"

def swappedBorrowJoinCondition : Term :=
  .eq
    (.copy swappedBorrowJoinA)                       -- Rust: if a
    (.copy swappedBorrowJoinB)                       -- Rust: == b

def swappedBorrowJoinTrueBranch : Term :=
  .block [0, 0] [
    .assign
      swappedBorrowJoinX                             -- Rust: x
      (.borrow true swappedBorrowJoinA),             -- Rust: = &mut a;
    .assign
      swappedBorrowJoinY                             -- Rust: y
      (.borrow true swappedBorrowJoinB)              -- Rust: = &mut b;
  ]

def swappedBorrowJoinFalseBranch : Term :=
  .block [0, 0] [
    .assign
      swappedBorrowJoinX                             -- Rust: x
      (.borrow true swappedBorrowJoinB),             -- Rust: = &mut b;
    .assign
      swappedBorrowJoinY                             -- Rust: y
      (.borrow true swappedBorrowJoinA)              -- Rust: = &mut a;
  ]

def swappedBorrowJoinWriteExample : Term :=
  .block [0] [
    .letMut "a" (.val (.int 0)),                    -- Rust: let mut a = 0;
    .letMut "b" (.val (.int 0)),                    -- Rust: let mut b = 0;
    .letMut "c" (.val (.int 0)),                    -- Rust: let mut c = 0;
    .letMut "d" (.val (.int 0)),                    -- Rust: let mut d = 0;
    .letMut "x" (.borrow true swappedBorrowJoinC),  -- Rust: let mut x = &mut c;
    .letMut "y" (.borrow true swappedBorrowJoinD),  -- Rust: let mut y = &mut d;
    .ite
      swappedBorrowJoinCondition
      swappedBorrowJoinTrueBranch
      swappedBorrowJoinFalseBranch,
    .assign
      (.deref swappedBorrowJoinX)                   -- Rust: *x
      (.val (.int 1))                               -- Rust: = 1;
  ]

theorem swappedBorrowJoinWriteExample_accepted :
    borrowCheck swappedBorrowJoinWriteExample := by
  borrow_check

theorem swappedBorrowJoinWriteExample_checkerTrue :
    borrowCheck? 256 swappedBorrowJoinWriteExample = true := by
  native_decide

/-! ## Nested mutable reborrow through a borrow cell -/

def nestedMutableReborrowWriteExample : Term :=
  .block [0] [
    .letMut "a" (.val (.int 0)),                    -- Rust: let mut a = 0;
    .letMut "q" (.borrow true (.var "a")),          -- Rust: let mut q = &mut a;
    .letMut "x" (.borrow true (.var "q")),          -- Rust: let mut x = &mut q;
    .assign
      (.deref (.deref (.var "x")))                  -- Rust: **x
      (.val (.int 1))                               -- Rust: = 1;
  ]

theorem nestedMutableReborrowWriteExample_accepted :
    borrowCheck nestedMutableReborrowWriteExample := by
  borrow_check

theorem nestedMutableReborrowWriteExample_checkerTrue :
    borrowCheck? 512 nestedMutableReborrowWriteExample = true := by
  native_decide

end Paper
end LwRust
