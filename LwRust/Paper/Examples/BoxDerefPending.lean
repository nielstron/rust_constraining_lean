import LwRust.Paper.Typing

/-!
Pending examples for declared boxes as lvalues.

The paper treats `box T` as an owned pointer type: if `p : box int`, then `*p`
is an lvalue of type `int`.  The current mechanization stores declared boxes as
full types (`.ty (.box inner)`) but `T-LvBox` only descends through the partial
projection shape (`.box inner`).  The Rust-style snippets below are therefore
the intended examples; the commented Lean variants are the proof obligations
that should compile once full boxes are bridged into lvalue/path typing.
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

/-!
Intended Lean variants after the full-box bridge exists:

```lean
example :
    LValTyping declaredBoxIntEnv (.deref (.var "p")) (.ty .int)
      Lifetime.root := by
  exact LValTyping.boxFull declaredBoxInt_var_typing

example :
    Mutable declaredBoxIntEnv (.deref (.var "p")) := by
  have hpMutable : Mutable declaredBoxIntEnv (.var "p") := by
    exact Mutable.var (slot := declaredBoxIntSlot) (by
      simp [declaredBoxIntEnv, declaredBoxIntSlot])
  exact Mutable.boxFull declaredBoxInt_var_typing hpMutable

example : ∃ env',
    EnvWrite 0 declaredBoxIntEnv (.deref (.var "p")) .int env' := by
  refine ⟨declaredBoxIntEnv.update "p" declaredBoxIntSlot, ?_⟩
  refine EnvWrite.intro
    (lv := .deref (.var "p"))
    (slot := declaredBoxIntSlot)
    (ty := .int)
    (updatedTy := .ty (.box .int))
    ?slot
    ?update
  · simp [declaredBoxIntEnv, declaredBoxIntSlot]
  · exact UpdateAtPath.boxFull (path := []) (inner := .int)
      UpdateAtPath.strong

example : ∃ env',
    EnvMove declaredBoxIntEnv (.deref (.var "p")) env' := by
  refine ⟨declaredBoxIntEnv.update "p"
    { declaredBoxIntSlot with ty := .box (.undef .int) }, ?_⟩
  refine ⟨declaredBoxIntSlot, .box (.undef .int), ?slot, ?strike, rfl⟩
  · simp [declaredBoxIntEnv, declaredBoxIntSlot]
  · rfl
```
-/

end BoxDerefPending

end Paper
end LwRust
