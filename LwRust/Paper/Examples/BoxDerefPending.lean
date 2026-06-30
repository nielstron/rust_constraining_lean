import LwRust.Paper.Typing

/-!
Pending examples for declared boxes as lvalues.

The paper treats `box T` as an owned pointer type: if `p : box int`, then `*p`
is an lvalue of type `int`.  The current mechanization stores declared boxes as
full types (`.ty (.box inner)`) but `T-LvBox` only descends through the partial
projection shape (`.box inner`).  The Rust-style snippets below are the programs
whose typing derivations should be added when full boxes are bridged into
lvalue/path typing.
-/

namespace LwRust
namespace Paper

open Core

namespace BoxDerefPending

/--
Rust-style:

```rust
{
    let mut p = box 0;
    *p
}
```
-/
def declaredBoxReadProgram : Term :=
  .block [0]
    [ .letMut "p" (.box (.val (.int 0)))
    , .move (.deref (.var "p"))
    ]

/--
Rust-style:

```rust
{
    let mut p = box 0;
    *p = 1;
}
```
-/
def declaredBoxWriteProgram : Term :=
  .block [0]
    [ .letMut "p" (.box (.val (.int 0)))
    , .assign (.deref (.var "p")) (.val (.int 1))
    ]

/--
Rust-style:

```rust
{
    let mut p = box 0;
    let mut r = &mut *p;
}
```
-/
def declaredBoxBorrowProgram : Term :=
  .block [0]
    [ .letMut "p" (.box (.val (.int 0)))
    , .letMut "r" (.borrow true (.deref (.var "p")))
    ]

/--
Environment shape after `let mut p = box 0`.
-/
def declaredBoxIntSlot : EnvSlot :=
  { ty := .ty (.box .int), lifetime := Lifetime.root }

def declaredBoxIntEnv : Env :=
  Env.empty.update "p" declaredBoxIntSlot

theorem declaredBoxInt_var_typing :
    LValTyping declaredBoxIntEnv (.var "p") (.ty (.box .int))
      Lifetime.root := by
  exact @LValTyping.var declaredBoxIntEnv "p" declaredBoxIntSlot (by
    simp [declaredBoxIntEnv, declaredBoxIntSlot])

end BoxDerefPending

end Paper
end LwRust
