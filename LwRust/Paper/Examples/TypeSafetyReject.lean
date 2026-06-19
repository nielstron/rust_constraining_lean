import LwRust.Paper.BorrowCheckerSoundness
import LwRust.Paper.Examples.Internal.TypeSafetyReject
import LwRust.Paper.Examples.Operational

/-!
Examples not accepted by the executable checker, written as readable checker
inputs.

Certified logical rejections state the inductive `borrowReject` property.
Finite checker failure is still shown separately from non-typability
certificates.
-/

namespace LwRust
namespace Paper

open Core

/-! ## Runtime reference constants are not source programs -/

def rawBorrowedReferenceConstantExample : Term :=
  .val (.ref { location := .var "x", owner := false })
    -- Rust: no source expression; this is a runtime reference value.

theorem rawBorrowedReferenceConstantExample_rejected :
    borrowReject rawBorrowedReferenceConstantExample := by
  simpa [rawBorrowedReferenceConstantExample, rawBorrowedReferenceConstant]
    using rawBorrowedReferenceConstant_borrowRejected

theorem rawBorrowedReferenceConstantExample_notAcceptedByChecker :
    borrowCheck? 64 rawBorrowedReferenceConstantExample = false := by
  native_decide

theorem rawBorrowedReferenceConstantExample_rejectedByChecker :
    borrowCheckFailed? 64 rawBorrowedReferenceConstantExample = true := by
  borrow_run

def boxedRawBorrowedReferenceConstantExample : Term :=
  .box
    (.val (.ref { location := .var "x", owner := false }))
    -- Rust: box <runtime-only borrowed reference>

theorem boxedRawBorrowedReferenceConstantExample_rejected :
    borrowReject boxedRawBorrowedReferenceConstantExample := by
  simpa [boxedRawBorrowedReferenceConstantExample,
    boxedRawBorrowedReferenceConstant, rawBorrowedReferenceConstant]
    using boxedRawBorrowedReferenceConstant_borrowRejected

theorem boxedRawBorrowedReferenceConstantExample_notAcceptedByChecker :
    borrowCheck? 64 boxedRawBorrowedReferenceConstantExample = false := by
  native_decide

theorem boxedRawBorrowedReferenceConstantExample_rejectedByChecker :
    borrowCheckFailed? 64 boxedRawBorrowedReferenceConstantExample = true := by
  borrow_run

/-! ## Assigning through a mutably borrowed place -/

def invalidBorrowExampleProgram : Term :=
  .block InvalidBorrowExample.l [
    .letMut "x" (.val (.int 0)),       -- Rust: let mut x = 0;
    .letMut "y" (.borrow true (.var "x")), -- Rust: let mut y = &mut x;
    .assign (.var "x") (.val (.int 1)) -- Rust: x = 1;
  ]

theorem invalidBorrowExampleProgram_rejected :
    borrowReject invalidBorrowExampleProgram := by
  simpa [invalidBorrowExampleProgram, InvalidBorrowExample.invalidProgram,
    InvalidBorrowExample.declareX, InvalidBorrowExample.declareY,
    InvalidBorrowExample.assignX, InvalidBorrowExample.x, InvalidBorrowExample.l]
    using invalidBorrowExample_borrowRejected

theorem invalidBorrowExampleProgram_notAcceptedByChecker :
    borrowCheck? 256 invalidBorrowExampleProgram = false := by
  native_decide

theorem invalidBorrowExampleProgram_rejectedByChecker :
    borrowCheckFailed? 256 invalidBorrowExampleProgram = true := by
  borrow_run

/-! ## Letting a borrow escape its source lifetime -/

def invalidEscapingBorrowExampleProgram : Term :=
  .block InvalidEscapingBorrowExample.l [
    .letMut "x" (.val (.int 0)),             -- Rust: let mut x = 0;
    .letMut "y" (.borrow true (.var "x")),   -- Rust: let mut y = &mut x;
    .block InvalidEscapingBorrowExample.m [
      .letMut "z" (.val (.int 0)),           -- Rust: let mut z = 0;
      .assign
        (.var "y")                           -- Rust: y
        (.borrow true (.var "z"))            -- Rust: = &mut z;
    ],
    .letMut "w" (.move (.var "y"))           -- Rust: let mut w = y;
  ]

theorem invalidEscapingBorrowExampleProgram_rejected :
    borrowReject invalidEscapingBorrowExampleProgram := by
  simpa [invalidEscapingBorrowExampleProgram,
    InvalidEscapingBorrowExample.invalidProgram,
    InvalidEscapingBorrowExample.declareX,
    InvalidEscapingBorrowExample.declareY,
    InvalidEscapingBorrowExample.declareZ,
    InvalidEscapingBorrowExample.assignYBorrowZ,
    InvalidEscapingBorrowExample.innerBlock,
    InvalidEscapingBorrowExample.declareW,
    InvalidEscapingBorrowExample.x,
    InvalidEscapingBorrowExample.y,
    InvalidEscapingBorrowExample.z,
    InvalidEscapingBorrowExample.l,
    InvalidEscapingBorrowExample.m]
    using invalidEscapingBorrowExample_borrowRejected

theorem invalidEscapingBorrowExampleProgram_notAcceptedByChecker :
    borrowCheck? 256 invalidEscapingBorrowExampleProgram = false := by
  native_decide

theorem invalidEscapingBorrowExampleProgram_rejectedByChecker :
    borrowCheckFailed? 256 invalidEscapingBorrowExampleProgram = true := by
  borrow_run

/-! ## Joined reborrow with incoherent nested targets -/

def nestedIncoherentJoinProgram : Term :=
  .block [0] [                                      -- Rust: {
    .letMut "c" (.val (.int 0)),                    -- Rust: let mut c = 0;
    .letMut "d" (.val (.bool true)),                -- Rust: let mut d = true;
    .letMut "a" (.borrow true (.var "c")),          -- Rust: let mut a = &mut c;
    .letMut "b" (.borrow true (.var "d")),          -- Rust: let mut b = &mut d;
    .letMut "z"                                    -- Rust: let mut z =
      (.ite
        (.val (.bool true))                         -- Rust: if true
        (.borrow true (.var "a"))                   -- Rust: { &mut a }
        (.borrow true (.var "b")))                  -- Rust: else { &mut b };
  ]                                                 -- Rust: }

theorem nestedIncoherentJoinProgram_failedByChecker :
    borrowCheckFailureWitness 256 nestedIncoherentJoinProgram := by
  borrow_check

theorem nestedIncoherentJoinProgram_notAcceptedByChecker :
    borrowCheck? 256 nestedIncoherentJoinProgram = false := by
  native_decide

theorem nestedIncoherentJoinProgram_rejectedByChecker :
    borrowCheckFailed? 256 nestedIncoherentJoinProgram = true := by
  exact borrowCheckFailureWitness_checked
    nestedIncoherentJoinProgram_failedByChecker

/-! ## Assignment after a non-uniform nested borrow join -/

def nestedBorrowShapeMismatchProgram : Term :=
  .block [0] [                                      -- Rust: {
    .letMut "c" (.val (.int 0)),                    -- Rust: let mut c = 0;
    .letMut "d" (.val (.int 0)),                    -- Rust: let mut d = 0;
    .letMut "a" (.borrow false (.var "c")),         -- Rust: let mut a = &c;
    .letMut "b" (.borrow false (.var "d")),         -- Rust: let mut b = &d;
    .letMut "x"                                    -- Rust: let mut x =
      (.ite
        (.val (.bool true))                         -- Rust: if true
        (.borrow false (.var "a"))                  -- Rust: { &a }
        (.borrow false (.var "b"))),                -- Rust: else { &b };
    .assign
      (.var "x")                                    -- Rust: x
      (.borrow false (.var "a"))                    -- Rust: = &a;
  ]                                                 -- Rust: }

theorem nestedBorrowShapeMismatchProgram_failedByChecker :
    borrowCheckFailureWitness 256 nestedBorrowShapeMismatchProgram := by
  borrow_check

theorem nestedBorrowShapeMismatchProgram_notAcceptedByChecker :
    borrowCheck? 256 nestedBorrowShapeMismatchProgram = false := by
  native_decide

theorem nestedBorrowShapeMismatchProgram_rejectedByChecker :
    borrowCheckFailed? 256 nestedBorrowShapeMismatchProgram = true := by
  exact borrowCheckFailureWitness_checked
    nestedBorrowShapeMismatchProgram_failedByChecker

/-! ## Reborrow assignment through a dereference changes the wrong frame -/

def derefBorrowReassignmentProgram : Term :=
  .block [0] [                                      -- Rust: {
    .letMut "a" (.val (.int 0)),                    -- Rust: let mut a = 0;
    .letMut "b" (.val (.int 0)),                    -- Rust: let mut b = 0;
    .letMut "q" (.borrow true (.var "a")),          -- Rust: let mut q = &mut a;
    .letMut "p" (.borrow true (.var "q")),          -- Rust: let mut p = &mut q;
    .assign
      (.deref (.var "p"))                           -- Rust: *p
      (.borrow true (.var "b"))                     -- Rust: = &mut b;
  ]                                                 -- Rust: }

theorem derefBorrowReassignmentProgram_failedByChecker :
    borrowCheckFailureWitness 256 derefBorrowReassignmentProgram := by
  borrow_check

theorem derefBorrowReassignmentProgram_notAcceptedByChecker :
    borrowCheck? 256 derefBorrowReassignmentProgram = false := by
  native_decide

theorem derefBorrowReassignmentProgram_rejectedByChecker :
    borrowCheckFailed? 256 derefBorrowReassignmentProgram = true := by
  exact borrowCheckFailureWitness_checked
    derefBorrowReassignmentProgram_failedByChecker

/-! ## Reborrowing through a reference cell blocks later cell replacement -/

def nestedReferenceInvalidationProgram : Term :=
  .block [0] [                                      -- Rust: {
    .letMut "b" (.val (.int 0)),                    -- Rust: let mut b = 0;
    .letMut "c" (.val (.int 1)),                    -- Rust: let mut c = 1;
    .letMut "a" (.borrow true (.var "b")),          -- Rust: let mut a = &mut b;
    .letMut "p" (.borrow true (.var "a")),          -- Rust: let mut p = &mut a;
    .letMut "q" (.borrow true (.deref (.var "a"))), -- Rust: let mut q = &mut *a;
    .assign
      (.deref (.var "p"))                           -- Rust: *p
      (.borrow true (.var "c")),                    -- Rust: = &mut c;
    .assign
      (.deref (.var "q"))                           -- Rust: *q
      (.val (.int 2))                               -- Rust: = 2;
  ]                                                 -- Rust: }

theorem nestedReferenceInvalidationProgram_failedByChecker :
    borrowCheckFailureWitness 256 nestedReferenceInvalidationProgram := by
  borrow_check

theorem nestedReferenceInvalidationProgram_notAcceptedByChecker :
    borrowCheck? 256 nestedReferenceInvalidationProgram = false := by
  native_decide

theorem nestedReferenceInvalidationProgram_rejectedByChecker :
    borrowCheckFailed? 256 nestedReferenceInvalidationProgram = true := by
  exact borrowCheckFailureWitness_checked
    nestedReferenceInvalidationProgram_failedByChecker

/-! ## Reborrowing inside an owned box blocks replacing the box root -/

def boxedReborrowInvalidationProgram : Term :=
  .block [0] [                                      -- Rust: {
    .letMut "b" (.box (.val (.int 0))),             -- Rust: let mut b = Box::new(0);
    .letMut "q" (.borrow true (.deref (.var "b"))), -- Rust: let mut q = &mut *b;
    .letMut "p" (.borrow true (.var "b")),          -- Rust: let mut p = &mut b;
    .assign
      (.deref (.var "p"))                           -- Rust: *p
      (.box (.val (.int 1))),                       -- Rust: = Box::new(1);
    .assign
      (.deref (.var "q"))                           -- Rust: *q
      (.val (.int 2))                               -- Rust: = 2;
  ]                                                 -- Rust: }

theorem boxedReborrowInvalidationProgram_failedByChecker :
    borrowCheckFailureWitness 256 boxedReborrowInvalidationProgram := by
  borrow_check

theorem boxedReborrowInvalidationProgram_notAcceptedByChecker :
    borrowCheck? 256 boxedReborrowInvalidationProgram = false := by
  native_decide

theorem boxedReborrowInvalidationProgram_rejectedByChecker :
    borrowCheckFailed? 256 boxedReborrowInvalidationProgram = true := by
  exact borrowCheckFailureWitness_checked
    boxedReborrowInvalidationProgram_failedByChecker

end Paper
end LwRust
