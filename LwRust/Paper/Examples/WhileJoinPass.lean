import LwRust.Paper.Examples.Internal.WhileJoinPass

/-!
Accepted `while` example for the join-based loop rule.

The derivation details are hidden in `Examples.Internal.WhileJoinPass`.  The
public example is a closed source program whose setup lines are ordinary
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
    borrowCheck? 256 whileJoinRetargetLoopExample = true := by
  native_decide

end Paper
end LwRust
