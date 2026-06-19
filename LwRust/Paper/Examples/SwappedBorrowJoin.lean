import LwRust.Paper.BorrowChecker

/-!
Crossed mutable-borrow examples for joined target lists.

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

/-! ## Appending `*x = 1` is accepted -/

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

theorem swappedBorrowDerefXAfterIfProgram_accepted :
    borrowCheck swappedBorrowDerefXAfterIfProgram := by
  borrow_check

theorem swappedBorrowDerefXAfterIfProgram_checkerTrue :
    borrowCheck? 256 swappedBorrowDerefXAfterIfProgram = true := by
  borrow_run

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
