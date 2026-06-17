import LwRust.Paper.Examples.Internal.TypeSafetyReject

/-!
Rejected examples, written as readable checker inputs.

The internal module keeps the proof-carrying rejection certificates and
operational stuck-state witnesses.  This module shows each complete program and
ends with the executable checker rejecting it.
-/

namespace LwRust
namespace Paper

open Core

/-! ## Runtime reference constants are not source programs -/

def rawBorrowedReferenceConstantExample : Term :=
  .val (.ref { location := .var "x", owner := false })
    -- Rust: no source expression; this is a runtime reference value.

theorem rawBorrowedReferenceConstantExample_rejected :
    borrowReject? 32 rawBorrowedReferenceConstantExample = true := by
  native_decide

def boxedRawBorrowedReferenceConstantExample : Term :=
  .box
    (.val (.ref { location := .var "x", owner := false }))
    -- Rust: box <runtime-only borrowed reference>

theorem boxedRawBorrowedReferenceConstantExample_rejected :
    borrowReject? 32 boxedRawBorrowedReferenceConstantExample = true := by
  native_decide

/-! ## Assigning through a mutably borrowed place -/

def invalidBorrowExampleProgram : Term :=
  .block InvalidBorrowExample.l [
    .letMut "x" (.val (.int 0)),       -- Rust: let mut x = 0;
    .letMut "y" (.borrow true (.var "x")), -- Rust: let mut y = &mut x;
    .assign (.var "x") (.val (.int 1)) -- Rust: x = 1;
  ]

theorem invalidBorrowExampleProgram_rejected :
    borrowReject? 128 invalidBorrowExampleProgram = true := by
  native_decide

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
    borrowReject? 128 invalidEscapingBorrowExampleProgram = true := by
  native_decide

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

theorem nestedIncoherentJoinProgram_rejected :
    borrowReject? 256 nestedIncoherentJoinProgram = true := by
  native_decide

end Paper
end LwRust
