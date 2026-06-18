import LwRust.Paper.BorrowChecker

/-!
Accepted `while` example for the join-based loop rule.

The final theorem proves the inductive `borrowCheck` property by running the
executable checker on a closed source program whose setup lines are ordinary
`letMut`s in the outer block.
-/

namespace LwRust
namespace Paper

open Core

def whileJoinRetargetLoopExample : Term :=
  .block [0] [
    .letMut "x" (.val (.int 0)),       -- Rust: let mut x = 0;
    .letMut "y" (.val (.int 0)),       -- Rust: let mut y = 0;
    .letMut "q" (.borrow false (.var "x")),
      -- Rust: let mut q = &x;
    .whileLoop [0, 0]                  -- Rust: while
      (.eq
        (.copy (.deref (.var "q")))    -- Rust: *q
        (.val (.int 0)))               -- Rust: == 0
      (.assign
        (.var "q")                     -- Rust: q
        (.borrow false (.var "y")))    -- Rust: = &y;
  ]

theorem whileJoinRetargetLoopExample_accepted :
    borrowCheck whileJoinRetargetLoopExample := by
  borrow_check

end Paper
end LwRust
