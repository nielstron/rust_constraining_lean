import LwRust.Paper.BorrowChecker
import LwRust.Paper.Examples.Internal.Reject.SwappedBorrowJoin

/-!
Crossed mutable-borrow examples for the local assignment authority check.

The examples below are closed checker inputs: the late-initialized Rust locals
`x` and `y` are represented by ordinary dummy initializers, then overwritten in
both branches.
-/

namespace LwRust
namespace Paper

open Core

/-! ## The crossed if itself is accepted -/

def swappedBorrowCrossedIfProgram : Term :=
  .block [0] [                                -- Rust: {
    .letMut "a" (.val (.int 0)),              -- Rust: let mut a = 0;
    .letMut "b" (.val (.int 0)),              -- Rust: let mut b = 0;
    .letMut "c" (.val (.int 0)),              -- Rust: let mut c = 0;
    .letMut "d" (.val (.int 0)),              -- Rust: let mut d = 0;
    .letMut "x" (.borrow true (.var "c")),    -- Rust: let mut x = &mut c;
    .letMut "y" (.borrow true (.var "d")),    -- Rust: let mut y = &mut d;
    .ite
      (.eq
        (.copy (.var "a"))                    -- Rust: if a
        (.copy (.var "b")))                   -- Rust: == b
      (.block [0, 0] [                        -- Rust: {
        .assign (.var "x")                    -- Rust: x
          (.borrow true (.var "a")),          -- Rust: = &mut a;
        .assign (.var "y")                    -- Rust: y
          (.borrow true (.var "b"))           -- Rust: = &mut b;
      ])
      (.block [0, 0] [                        -- Rust: } else {
        .assign (.var "x")                    -- Rust: x
          (.borrow true (.var "b")),          -- Rust: = &mut b;
        .assign (.var "y")                    -- Rust: y
          (.borrow true (.var "a"))           -- Rust: = &mut a;
      ])                                      -- Rust: }
  ]                                           -- Rust: }

theorem swappedBorrowCrossedIfProgram_accepted :
    borrowCheck swappedBorrowCrossedIfProgram := by
  borrow_check

/-! ## Appending `*x = 1` produces a finite checker failure -/

def swappedBorrowDerefXAfterIfProgram : Term :=
  .block [0] [                                -- Rust: {
    .letMut "a" (.val (.int 0)),              -- Rust: let mut a = 0;
    .letMut "b" (.val (.int 0)),              -- Rust: let mut b = 0;
    .letMut "c" (.val (.int 0)),              -- Rust: let mut c = 0;
    .letMut "d" (.val (.int 0)),              -- Rust: let mut d = 0;
    .letMut "x" (.borrow true (.var "c")),    -- Rust: let mut x = &mut c;
    .letMut "y" (.borrow true (.var "d")),    -- Rust: let mut y = &mut d;
    .ite
      (.eq
        (.copy (.var "a"))                    -- Rust: if a
        (.copy (.var "b")))                   -- Rust: == b
      (.block [0, 0] [                        -- Rust: {
        .assign (.var "x")                    -- Rust: x
          (.borrow true (.var "a")),          -- Rust: = &mut a;
        .assign (.var "y")                    -- Rust: y
          (.borrow true (.var "b"))           -- Rust: = &mut b;
      ])
      (.block [0, 0] [                        -- Rust: } else {
        .assign (.var "x")                    -- Rust: x
          (.borrow true (.var "b")),          -- Rust: = &mut b;
        .assign (.var "y")                    -- Rust: y
          (.borrow true (.var "a"))           -- Rust: = &mut a;
      ]),                                     -- Rust: }
    .assign
      (.deref (.var "x"))                     -- Rust: *x
      (.val (.int 1))                         -- Rust: = 1;
  ]                                           -- Rust: }

theorem swappedBorrowDerefXAfterIfProgram_failedByChecker :
    borrowCheckFailureWitness 256 swappedBorrowDerefXAfterIfProgram := by
  borrow_check

theorem swappedBorrowDerefXAfterIfProgram_rejected :
    borrowReject swappedBorrowDerefXAfterIfProgram := by
  simpa [swappedBorrowDerefXAfterIfProgram,
    SwappedBorrowJoinReject.derefXAfterIfProgram,
    SwappedBorrowJoinReject.condition,
    SwappedBorrowJoinReject.trueBranch,
    SwappedBorrowJoinReject.falseBranch,
    SwappedBorrowJoinReject.l, SwappedBorrowJoinReject.m,
    SwappedBorrowJoinReject.a, SwappedBorrowJoinReject.b,
    SwappedBorrowJoinReject.c, SwappedBorrowJoinReject.d,
    SwappedBorrowJoinReject.x, SwappedBorrowJoinReject.y]
    using SwappedBorrowJoinReject.borrowRejected

theorem swappedBorrowDerefXAfterIfProgram_outcomeWitness :
    borrowOutcomeWitness 256 swappedBorrowDerefXAfterIfProgram
      (some SwappedBorrowJoinReject.borrowRejection) := by
  simpa [swappedBorrowDerefXAfterIfProgram,
    SwappedBorrowJoinReject.derefXAfterIfProgram,
    SwappedBorrowJoinReject.condition,
    SwappedBorrowJoinReject.trueBranch,
    SwappedBorrowJoinReject.falseBranch,
    SwappedBorrowJoinReject.l, SwappedBorrowJoinReject.m,
    SwappedBorrowJoinReject.a, SwappedBorrowJoinReject.b,
    SwappedBorrowJoinReject.c, SwappedBorrowJoinReject.d,
    SwappedBorrowJoinReject.x, SwappedBorrowJoinReject.y]
    using
      (show borrowOutcomeWitness 256
          SwappedBorrowJoinReject.derefXAfterIfProgram
          (some SwappedBorrowJoinReject.borrowRejection) from by
        borrow_check using SwappedBorrowJoinReject.borrowRejection)

theorem swappedBorrowDerefXAfterIfProgram_noCheckWitness (fuel : Nat) :
    ¬ borrowCheckWitness fuel swappedBorrowDerefXAfterIfProgram := by
  simpa [swappedBorrowDerefXAfterIfProgram,
    SwappedBorrowJoinReject.derefXAfterIfProgram,
    SwappedBorrowJoinReject.condition,
    SwappedBorrowJoinReject.trueBranch,
    SwappedBorrowJoinReject.falseBranch,
    SwappedBorrowJoinReject.l, SwappedBorrowJoinReject.m,
    SwappedBorrowJoinReject.a, SwappedBorrowJoinReject.b,
    SwappedBorrowJoinReject.c, SwappedBorrowJoinReject.d,
    SwappedBorrowJoinReject.x, SwappedBorrowJoinReject.y]
    using SwappedBorrowJoinReject.noBorrowCheckWitness fuel

theorem swappedBorrowDerefXAfterIfProgram_checkerFalse (fuel : Nat) :
    borrowCheck? fuel swappedBorrowDerefXAfterIfProgram = false := by
  simpa [swappedBorrowDerefXAfterIfProgram,
    SwappedBorrowJoinReject.derefXAfterIfProgram,
    SwappedBorrowJoinReject.condition,
    SwappedBorrowJoinReject.trueBranch,
    SwappedBorrowJoinReject.falseBranch,
    SwappedBorrowJoinReject.l, SwappedBorrowJoinReject.m,
    SwappedBorrowJoinReject.a, SwappedBorrowJoinReject.b,
    SwappedBorrowJoinReject.c, SwappedBorrowJoinReject.d,
    SwappedBorrowJoinReject.x, SwappedBorrowJoinReject.y]
    using SwappedBorrowJoinReject.checkerFalse fuel

theorem swappedBorrowDerefXAfterIfProgram_notAcceptedByChecker :
    borrowCheck? 256 swappedBorrowDerefXAfterIfProgram = false := by
  simpa [swappedBorrowDerefXAfterIfProgram,
    SwappedBorrowJoinReject.derefXAfterIfProgram,
    SwappedBorrowJoinReject.condition,
    SwappedBorrowJoinReject.trueBranch,
    SwappedBorrowJoinReject.falseBranch,
    SwappedBorrowJoinReject.l, SwappedBorrowJoinReject.m,
    SwappedBorrowJoinReject.a, SwappedBorrowJoinReject.b,
    SwappedBorrowJoinReject.c, SwappedBorrowJoinReject.d,
    SwappedBorrowJoinReject.x, SwappedBorrowJoinReject.y]
    using SwappedBorrowJoinReject.checkerFalse 256

/-! ## Appending an unrelated root assignment is accepted -/

def swappedBorrowUnrelatedRootAssignmentProgram : Term :=
  .block [0] [                                -- Rust: {
    .letMut "a" (.val (.int 0)),              -- Rust: let mut a = 0;
    .letMut "b" (.val (.int 0)),              -- Rust: let mut b = 0;
    .letMut "c" (.val (.int 0)),              -- Rust: let mut c = 0;
    .letMut "d" (.val (.int 0)),              -- Rust: let mut d = 0;
    .letMut "e" (.val (.int 0)),              -- Rust: let mut e = 0;
    .letMut "x" (.borrow true (.var "c")),    -- Rust: let mut x = &mut c;
    .letMut "y" (.borrow true (.var "d")),    -- Rust: let mut y = &mut d;
    .ite
      (.eq
        (.copy (.var "a"))                    -- Rust: if a
        (.copy (.var "b")))                   -- Rust: == b
      (.block [0, 0] [                        -- Rust: {
        .assign (.var "x")                    -- Rust: x
          (.borrow true (.var "a")),          -- Rust: = &mut a;
        .assign (.var "y")                    -- Rust: y
          (.borrow true (.var "b"))           -- Rust: = &mut b;
      ])
      (.block [0, 0] [                        -- Rust: } else {
        .assign (.var "x")                    -- Rust: x
          (.borrow true (.var "b")),          -- Rust: = &mut b;
        .assign (.var "y")                    -- Rust: y
          (.borrow true (.var "a"))           -- Rust: = &mut a;
      ]),                                     -- Rust: }
    .assign
      (.var "e")                              -- Rust: e
      (.val (.int 1))                         -- Rust: = 1;
  ]                                           -- Rust: }

theorem swappedBorrowUnrelatedRootAssignmentProgram_accepted :
    borrowCheck swappedBorrowUnrelatedRootAssignmentProgram := by
  borrow_check

/-! ## Appending an unrelated dereference assignment is accepted -/

def swappedBorrowUnrelatedDerefAssignmentProgram : Term :=
  .block [0] [                                -- Rust: {
    .letMut "a" (.val (.int 0)),              -- Rust: let mut a = 0;
    .letMut "b" (.val (.int 0)),              -- Rust: let mut b = 0;
    .letMut "c" (.val (.int 0)),              -- Rust: let mut c = 0;
    .letMut "d" (.val (.int 0)),              -- Rust: let mut d = 0;
    .letMut "e" (.val (.int 0)),              -- Rust: let mut e = 0;
    .letMut "p" (.borrow true (.var "e")),    -- Rust: let mut p = &mut e;
    .letMut "x" (.borrow true (.var "c")),    -- Rust: let mut x = &mut c;
    .letMut "y" (.borrow true (.var "d")),    -- Rust: let mut y = &mut d;
    .ite
      (.eq
        (.copy (.var "a"))                    -- Rust: if a
        (.copy (.var "b")))                   -- Rust: == b
      (.block [0, 0] [                        -- Rust: {
        .assign (.var "x")                    -- Rust: x
          (.borrow true (.var "a")),          -- Rust: = &mut a;
        .assign (.var "y")                    -- Rust: y
          (.borrow true (.var "b"))           -- Rust: = &mut b;
      ])
      (.block [0, 0] [                        -- Rust: } else {
        .assign (.var "x")                    -- Rust: x
          (.borrow true (.var "b")),          -- Rust: = &mut b;
        .assign (.var "y")                    -- Rust: y
          (.borrow true (.var "a"))           -- Rust: = &mut a;
      ]),                                     -- Rust: }
    .assign
      (.deref (.var "p"))                     -- Rust: *p
      (.val (.int 1))                         -- Rust: = 1;
  ]                                           -- Rust: }

theorem swappedBorrowUnrelatedDerefAssignmentProgram_accepted :
    borrowCheck swappedBorrowUnrelatedDerefAssignmentProgram := by
  borrow_check

end Paper
end LwRust
