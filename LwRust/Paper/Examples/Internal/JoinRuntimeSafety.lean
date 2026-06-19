import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
Concrete runtime shape of a joined mutable-borrow environment.

The joined type environment below is the abstract post-state of the crossed
branch pattern

```
if cond {
  x = &mut a; y = &mut b;
} else {
  x = &mut b; y = &mut a;
}
```

The static target lists for `x` and `y` overlap after the join, so the old
all-target `BorrowSafeRoot` predicate is false.  The concrete branch store,
however, still contains one runtime reference per variable; the stale joined-in
targets are not `SelectedTarget`s.
-/

namespace LwRust
namespace Paper

open Core

namespace JoinRuntimeSafetyExample

def l : Lifetime := [0]

def a : LVal := .var "a"
def b : LVal := .var "b"
def c : LVal := .var "c"
def d : LVal := .var "d"
def x : LVal := .var "x"
def y : LVal := .var "y"

def joinedEnv : Env :=
  (((((Env.empty.update "a" { ty := .ty .int, lifetime := l }).update "b"
      { ty := .ty .int, lifetime := l }).update "c"
      { ty := .ty .int, lifetime := l }).update "d"
      { ty := .ty .int, lifetime := l }).update "x"
      { ty := .ty (.borrow true [a, b]), lifetime := l }).update "y"
      { ty := .ty (.borrow true [b, a]), lifetime := l }

def trueBranchStore : ProgramStore :=
  ProgramStore.declare
    (ProgramStore.declare
      (ProgramStore.declare
        (ProgramStore.declare
          (ProgramStore.declare
            (ProgramStore.declare ProgramStore.empty "a" l (.int 0))
            "b" l (.int 0))
          "c" l (.int 0))
        "d" l (.int 0))
      "x" l (.ref { location := .var "a", owner := false }))
    "y" l (.ref { location := .var "b", owner := false })

theorem trueBranchStore_slot_x :
    trueBranchStore.slotAt (.var "x") =
      some
        { value := .value (.ref { location := .var "a", owner := false }),
          lifetime := l } := by
  simp [trueBranchStore, ProgramStore.declare, ProgramStore.update, l]

theorem trueBranchStore_slot_y :
    trueBranchStore.slotAt (.var "y") =
      some
        { value := .value (.ref { location := .var "b", owner := false }),
          lifetime := l } := by
  simp [trueBranchStore, ProgramStore.declare, ProgramStore.update, l]

theorem trueBranchStore_loc_a :
    trueBranchStore.loc a = some (.var "a") := by
  simp [trueBranchStore, ProgramStore.declare, ProgramStore.update,
    ProgramStore.loc, a]

theorem trueBranchStore_loc_b :
    trueBranchStore.loc b = some (.var "b") := by
  simp [trueBranchStore, ProgramStore.declare, ProgramStore.update,
    ProgramStore.loc, b]

theorem joinedEnv_contains_x :
    joinedEnv ⊢ "x" ↝ (.borrow true [a, b]) := by
  exact ⟨{ ty := .ty (.borrow true [a, b]), lifetime := l },
    by simp [joinedEnv], PartialTyContains.here⟩

theorem joinedEnv_contains_y :
    joinedEnv ⊢ "y" ↝ (.borrow true [b, a]) := by
  exact ⟨{ ty := .ty (.borrow true [b, a]), lifetime := l },
    by simp [joinedEnv], PartialTyContains.here⟩

theorem joinedEnv_not_static_borrowSafeRoot_x :
    ¬ BorrowSafeRoot joinedEnv "x" := by
  intro hsafe
  have hxy : "x" = "y" :=
    hsafe "y" true [a, b] [b, a] a a
      joinedEnv_contains_x joinedEnv_contains_y
      (by simp [a]) (by simp [a]) (by simp [PathConflicts, a])
  simp at hxy

theorem trueBranchStore_x_selects_a :
    SelectedTarget trueBranchStore "x" a := by
  refine ⟨.var "x",
    { value := .value (.ref { location := .var "a", owner := false }),
      lifetime := l },
    .var "a", Or.inl rfl, ?_, rfl, ?_⟩
  · exact trueBranchStore_slot_x
  · exact trueBranchStore_loc_a

theorem trueBranchStore_y_selects_b :
    SelectedTarget trueBranchStore "y" b := by
  refine ⟨.var "y",
    { value := .value (.ref { location := .var "b", owner := false }),
      lifetime := l },
    .var "b", Or.inl rfl, ?_, rfl, ?_⟩
  · exact trueBranchStore_slot_y
  · exact trueBranchStore_loc_b

theorem trueBranchStore_not_ownsAt_x {owned : Location} :
    ¬ ProgramStore.OwnsAt trueBranchStore owned (.var "x") := by
  rintro ⟨lifetime, hslot⟩
  have hx :
      trueBranchStore.slotAt (.var "x") =
        some
          { value := .value (.ref { location := .var "a", owner := false }),
            lifetime := l } := by
    exact trueBranchStore_slot_x
  rw [hx] at hslot
  simp [owningRef] at hslot

theorem trueBranchStore_not_ownsAt_y {owned : Location} :
    ¬ ProgramStore.OwnsAt trueBranchStore owned (.var "y") := by
  rintro ⟨lifetime, hslot⟩
  have hy :
      trueBranchStore.slotAt (.var "y") =
        some
          { value := .value (.ref { location := .var "b", owner := false }),
            lifetime := l } := by
    exact trueBranchStore_slot_y
  rw [hy] at hslot
  simp [owningRef] at hslot

theorem trueBranchStore_not_ownsTransitively_from_x {cell : Location} :
    ¬ ProgramStore.OwnsTransitively trueBranchStore (.var "x") cell := by
  intro howns
  cases howns with
  | direct hfirst =>
      exact trueBranchStore_not_ownsAt_x hfirst
  | trans hfirst _htail =>
      exact trueBranchStore_not_ownsAt_x hfirst

theorem trueBranchStore_not_ownsTransitively_from_y {cell : Location} :
    ¬ ProgramStore.OwnsTransitively trueBranchStore (.var "y") cell := by
  intro howns
  cases howns with
  | direct hfirst =>
      exact trueBranchStore_not_ownsAt_y hfirst
  | trans hfirst _htail =>
      exact trueBranchStore_not_ownsAt_y hfirst

theorem trueBranchStore_x_not_selects_b :
    ¬ SelectedTarget trueBranchStore "x" b := by
  rintro ⟨cell, cellSlot, loc, hprotected, hslot, hvalue, hloc⟩
  rcases hprotected with hcell | howns
  · subst hcell
    have hslotEq :
        cellSlot =
          { value := .value (.ref { location := .var "a", owner := false }),
            lifetime := l } := by
      have hx :
          trueBranchStore.slotAt (.var "x") =
            some
              { value := .value (.ref { location := .var "a", owner := false }),
                lifetime := l } := by
        exact trueBranchStore_slot_x
      exact Option.some.inj (hslot.symm.trans hx)
    subst hslotEq
    have hlocEqA : loc = .var "a" := by
      simpa using hvalue.symm
    have hlocEqB : loc = .var "b" := by
      exact Option.some.inj (hloc.symm.trans trueBranchStore_loc_b)
    simp [hlocEqA] at hlocEqB
  · exact trueBranchStore_not_ownsTransitively_from_x howns

theorem trueBranchStore_y_not_selects_a :
    ¬ SelectedTarget trueBranchStore "y" a := by
  rintro ⟨cell, cellSlot, loc, hprotected, hslot, hvalue, hloc⟩
  rcases hprotected with hcell | howns
  · subst hcell
    have hslotEq :
        cellSlot =
          { value := .value (.ref { location := .var "b", owner := false }),
            lifetime := l } := by
      have hy :
          trueBranchStore.slotAt (.var "y") =
            some
              { value := .value (.ref { location := .var "b", owner := false }),
                lifetime := l } := by
        exact trueBranchStore_slot_y
      exact Option.some.inj (hslot.symm.trans hy)
    subst hslotEq
    have hlocEqB : loc = .var "b" := by
      simpa using hvalue.symm
    have hlocEqA : loc = .var "a" := by
      exact Option.some.inj (hloc.symm.trans trueBranchStore_loc_a)
    simp [hlocEqB] at hlocEqA
  · exact trueBranchStore_not_ownsTransitively_from_y howns

theorem trueBranchStore_joined_xy_no_selected_conflict
    {targetX targetY : LVal} :
    targetX ∈ [a, b] →
    targetY ∈ [b, a] →
    SelectedTarget trueBranchStore "x" targetX →
    SelectedTarget trueBranchStore "y" targetY →
    targetX ⋈ targetY →
    False := by
  intro hmemX hmemY hselX hselY hconflict
  rcases List.mem_cons.mp hmemX with htargetX | htargetX
  · subst htargetX
    rcases List.mem_cons.mp hmemY with htargetY | htargetY
    · subst htargetY
      simp [PathConflicts, LVal.base, a, b] at hconflict
    · simp at htargetY
      subst htargetY
      exact trueBranchStore_y_not_selects_a hselY
  · simp at htargetX
    subst htargetX
    exact trueBranchStore_x_not_selects_b hselX

end JoinRuntimeSafetyExample

end Paper
end LwRust
