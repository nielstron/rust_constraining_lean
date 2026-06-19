import LwRust.Paper.BorrowChecker.Executable
import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
Runtime shape of a mutable reborrow through a reference.

The prefix

```
let mut a = 0;
let mut x = &mut a;
let mut y = &mut *x;
```

is accepted by the executable checker.  At runtime, `y` stores a concrete
reference to `a`, not a reference to the expression `*x`; `*x` remains the static
target expression used by the type environment.

This is why an invariant saying "no two live borrow roots resolve to the same
concrete location" is too strong.  The safety property has to be about later
writes being authorized and not invalidating live dependencies.
-/

namespace LwRust
namespace Paper

open Core

namespace ReborrowRuntimeShape

def l : Lifetime := [0]

def a : LVal := .var "a"
def x : LVal := .var "x"
def y : LVal := .var "y"

def reborrowPrefixProgram : Term :=
  .block [0] [
    .letMut "a" (.val (.int 0)),
    .letMut "x" (.borrow true a),
    .letMut "y" (.borrow true (.deref x))
  ]

theorem reborrowPrefixProgram_checker_accepts :
    borrowCheck? 256 reborrowPrefixProgram = true := by
  native_decide

def envAfterY : Env :=
  ((Env.empty.update "a" { ty := .ty .int, lifetime := l }).update "x"
      { ty := .ty (.borrow true [a]), lifetime := l }).update "y"
    { ty := .ty (.borrow true [.deref x]), lifetime := l }

def storeAfterY : ProgramStore :=
  ((ProgramStore.empty.declare "a" l (.int 0)).declare "x" l
      (.ref { location := .var "a", owner := false })).declare "y" l
    (.ref { location := .var "a", owner := false })

theorem storeAfterY_slot_x :
    storeAfterY.slotAt (.var "x") =
      some
        { value := .value (.ref { location := .var "a", owner := false }),
          lifetime := l } := by
  simp [storeAfterY, ProgramStore.declare, ProgramStore.update, l]

theorem storeAfterY_slot_y :
    storeAfterY.slotAt (.var "y") =
      some
        { value := .value (.ref { location := .var "a", owner := false }),
          lifetime := l } := by
  simp [storeAfterY, ProgramStore.declare, ProgramStore.update, l]

theorem storeAfterY_loc_a :
    storeAfterY.loc a = some (.var "a") := by
  simp [storeAfterY, ProgramStore.declare, ProgramStore.update,
    ProgramStore.loc, a]

theorem storeAfterY_loc_deref_x :
    storeAfterY.loc (.deref x) = some (.var "a") := by
  simp [storeAfterY, ProgramStore.declare, ProgramStore.update,
    ProgramStore.loc, x, l]

theorem storeAfterY_loc_deref_y :
    storeAfterY.loc (.deref y) = some (.var "a") := by
  simp [storeAfterY, ProgramStore.declare, ProgramStore.update,
    ProgramStore.loc, y, l]

theorem envAfterY_contains_x :
    envAfterY ⊢ "x" ↝ (.borrow true [a]) := by
  exact ⟨{ ty := .ty (.borrow true [a]), lifetime := l },
    by simp [envAfterY], PartialTyContains.here⟩

theorem envAfterY_contains_y :
    envAfterY ⊢ "y" ↝ (.borrow true [.deref x]) := by
  exact ⟨{ ty := .ty (.borrow true [.deref x]), lifetime := l },
    by simp [envAfterY], PartialTyContains.here⟩

theorem storeAfterY_x_selects_a :
    SelectedTarget storeAfterY "x" a := by
  refine ⟨.var "x",
    { value := .value (.ref { location := .var "a", owner := false }),
      lifetime := l },
    .var "a", Or.inl rfl, ?_, rfl, ?_⟩
  · exact storeAfterY_slot_x
  · exact storeAfterY_loc_a

theorem storeAfterY_y_selects_deref_x :
    SelectedTarget storeAfterY "y" (.deref x) := by
  refine ⟨.var "y",
    { value := .value (.ref { location := .var "a", owner := false }),
      lifetime := l },
    .var "a", Or.inl rfl, ?_, rfl, ?_⟩
  · exact storeAfterY_slot_y
  · exact storeAfterY_loc_deref_x

theorem storeAfterY_not_locationBorrowSafe :
    ¬ RuntimeLocationBorrowSafety storeAfterY envAfterY := by
  intro hsafe
  have hxy : "x" = "y" :=
    hsafe "x" "y" true [a] [.deref x] a (.deref x) (.var "a")
      envAfterY_contains_x envAfterY_contains_y
      (by simp [a]) (by simp)
      storeAfterY_x_selects_a storeAfterY_y_selects_deref_x
      storeAfterY_loc_a storeAfterY_loc_deref_x
  simp at hxy

end ReborrowRuntimeShape

end Paper
end LwRust
