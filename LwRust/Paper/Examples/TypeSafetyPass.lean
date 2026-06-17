import LwRust.Paper.Examples.Internal.TypeSafetyPass

/-!
Accepted examples, written as readable checker inputs.

The proof-heavy derivations live in `LwRust.Paper.Examples.Internal`.
This module keeps each public example in the same shape:

* the complete example code, with each Lean line annotated by the intended
  Rust source line;
* final theorems for the closed scalar/control-flow examples state the
  inductive type/borrow-checking property via proof-carrying checker
  certificates; the effectful pointer example still exposes the raw executable
  checker verdict until a closed certificate is added for its setup block.
-/

namespace LwRust
namespace Paper

open Core

/-! ## Closed scalar comparison -/

def scalarCopyComparisonExample : Term :=
  .eq
    (.val (.int 1)) -- Rust: 1
    (.val (.int 1)) -- Rust: == 1

private def scalarCopyComparisonExample_certified :
    CertifiedBorrowCheck 32 scalarCopyComparisonExample :=
  CertifiedBorrowCheck.ofTermCheck
    ({ checked := by native_decide
       typing := by
        simpa [scalarCopyComparisonExample, scalarCopyComparison] using
          scalarCopyComparison_typing } :
      CertifiedTermCheck 32 FiniteEnv.empty StoreTyping.empty Lifetime.root
        scalarCopyComparisonExample .bool FiniteEnv.empty)

theorem scalarCopyComparisonExample_accepted :
    borrowCheck scalarCopyComparisonExample := by
  exact scalarCopyComparisonExample_certified.borrowCheck

/-! ## Closed if/else returning integers -/

def ifThenElseIntExample : Term :=
  .ite
    (.val (.bool true)) -- Rust: if true
    (.val (.int 1))     -- Rust: { 1 }
    (.val (.int 2))     -- Rust: else { 2 }

private def ifThenElseIntExample_certified :
    CertifiedBorrowCheck 32 ifThenElseIntExample :=
  CertifiedBorrowCheck.ofTermCheck
    ({ checked := by native_decide
       typing := by
        simpa [ifThenElseIntExample, ifThenElseInt] using
          ifThenElseInt_typing } :
      CertifiedTermCheck 32 FiniteEnv.empty StoreTyping.empty Lifetime.root
        ifThenElseIntExample .int FiniteEnv.empty)

theorem ifThenElseIntExample_accepted :
    borrowCheck ifThenElseIntExample := by
  exact ifThenElseIntExample_certified.borrowCheck

/-! ## Closed if/else with a nontrivial condition -/

def ifEqThenElseIntExample : Term :=
  .ite
    (.eq
      (.val (.int 1)) -- Rust: if 1
      (.val (.int 1))) -- Rust: == 1
    (.val (.int 1))    -- Rust: { 1 }
    (.val (.int 2))    -- Rust: else { 2 }

private def ifEqThenElseIntExample_certified :
    CertifiedBorrowCheck 64 ifEqThenElseIntExample :=
  CertifiedBorrowCheck.ofTermCheck
    ({ checked := by native_decide
       typing := by
        simpa [ifEqThenElseIntExample, ifEqThenElseInt, scalarCopyComparison]
          using ifEqThenElseInt_typing } :
      CertifiedTermCheck 64 FiniteEnv.empty StoreTyping.empty Lifetime.root
        ifEqThenElseIntExample .int FiniteEnv.empty)

theorem ifEqThenElseIntExample_accepted :
    borrowCheck ifEqThenElseIntExample := by
  exact ifEqThenElseIntExample_certified.borrowCheck

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
    borrowCheck? 256 pointerIfAssignmentExample = true := by
  native_decide

end Paper
end LwRust
