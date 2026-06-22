import LwRust.Paper.BorrowCheckerSoundness
import LwRust.Paper.Examples.Internal.TypeSafetyReject
import LwRust.Paper.Examples.Operational

/-!
Examples not accepted by the executable checker, written as readable checker
inputs.

Certified logical rejections state the inductive `borrowReject` property.
Finite checker failure is still shown for examples that do not yet have a
non-typability certificate; `borrowUnknownWitness` records cases where the
current finite checker cannot classify the program.
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
  borrow_reject

def boxedRawBorrowedReferenceConstantExample : Term :=
  .box
    (.val (.ref { location := .var "x", owner := false }))
    -- Rust: box <runtime-only borrowed reference>

theorem boxedRawBorrowedReferenceConstantExample_rejected :
    borrowReject boxedRawBorrowedReferenceConstantExample := by
  borrow_reject

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
    using
      (show borrowReject InvalidBorrowExample.invalidProgram from by
        borrow_check using invalidBorrowExample_borrowRejection)

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
    using
      (show borrowReject InvalidEscapingBorrowExample.invalidProgram from by
        borrow_check using invalidEscapingBorrowExample_borrowRejection)

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
          (.block [0, 0] [                            -- Rust: {
            .borrow true (.var "a")                   -- Rust: &mut a
          ])
          (.block [0, 0] [                            -- Rust: else {
            .borrow true (.var "b")                   -- Rust: &mut b
          ]))                                         -- Rust: };
  ]                                                 -- Rust: }

theorem nestedIncoherentJoinProgram_failedByChecker :
    borrowCheckFailureWitness 256 nestedIncoherentJoinProgram := by
  borrow_check

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
          (.block [0, 0] [                            -- Rust: {
            .borrow false (.var "a")                  -- Rust: &a
          ])
          (.block [0, 0] [                            -- Rust: else {
            .borrow false (.var "b")                  -- Rust: &b
          ])),                                        -- Rust: };
    .assign
      (.var "x")                                    -- Rust: x
      (.borrow false (.var "a"))                    -- Rust: = &a;
  ]                                                 -- Rust: }

theorem nestedBorrowShapeMismatchProgram_unknownByChecker :
    borrowUnknownWitness 256 nestedBorrowShapeMismatchProgram := by
  borrow_check

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

end Paper
end LwRust
