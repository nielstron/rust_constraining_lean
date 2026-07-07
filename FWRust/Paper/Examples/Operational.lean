import FWRust.Paper.InductiveSemantics

/-!
Operational paper examples from Section 3.2.4 and Section 3.3.

These examples are reduction witnesses, not typing derivations.  The two
`Invalid*` namespaces intentionally show programs that the operational semantics
can run into bad states when the type-and-borrow discipline is ignored.
-/

namespace FWRust
namespace Paper

open Core

namespace EvaluationContextExamples

def l : Lifetime := [9]
def x : LVal := .var "x"
def y : LVal := .var "y"

def Sxy : ProgramStore :=
  (ProgramStore.empty.declare "x" l (.int 0)).declare "y" l (.int 1)

def yBoxSubterm : Term :=
  .box (.copy y)

/-- Paper Section 3.2.3: `box y` reduces by reducing the subterm `y`. -/
theorem box_copy_y_subterm_step :
    Step Sxy l yBoxSubterm Sxy (.box (.val (.int 1))) := by
  unfold yBoxSubterm y Sxy l
  exact Step.subBox (Step.copy (valueLifetime := [9]) (by
    simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.update]))

def assignYThenAssignX : Term :=
  .block l [.assign y (.val (.int 2)), .assign x (.move y)]

/--
Paper Section 3.2.3: the head of a sequence is an evaluation context, so
`y = 2; x = y` steps to `unit; x = y` after updating `y`.
-/
theorem assign_y_then_assign_x_head_step :
    Step Sxy l assignYThenAssignX
      (Sxy.update (.var "y") { value := .value (.int 2), lifetime := l })
      (.block l [.val .unit, .assign x (.move y)]) := by
  unfold assignYThenAssignX Sxy x y l
  refine Step.blockA (Step.assign
    (oldSlot := { value := .value (.int 1), lifetime := [9] })
    (store₂ := ((ProgramStore.empty.declare "x" [9] (.int 0)).declare "y" [9] (.int 1)).update
      (.var "y") { value := .value (.int 2), lifetime := [9] })
    ?_ ?_ ?_)
  · simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.update]
  · rfl
  · exact ProgramStore.Drops.nonOwner (by intro ref; left; simp)
      ProgramStore.Drops.nil

end EvaluationContextExamples

namespace WorkedExample

def l : Lifetime := [0]
def m : Lifetime := [0, 0]

def x : LVal := .var "x"
def y : LVal := .var "y"
def z : LVal := .var "z"
def derefY : LVal := .deref y

def owned (location : Location) : Value :=
  .ref { location := location, owner := true }

def borrowed (location : Location) : Value :=
  .ref { location := location, owner := false }

def unitDrops (store : ProgramStore) :
    Drops store [.value .unit] store := by
  exact ProgramStore.Drops.nonOwner (by intro ref; left; simp) ProgramStore.Drops.nil

def intDrops (store : ProgramStore) (n : Int) :
    Drops store [.value (.int n)] store := by
  exact ProgramStore.Drops.nonOwner (by intro ref; left; simp) ProgramStore.Drops.nil

def borrowDrops (store : ProgramStore) (location : Location) :
    Drops store [.value (borrowed location)] store := by
  refine ProgramStore.Drops.nonOwner ?_ ProgramStore.Drops.nil
  intro ref
  by_cases h : (PartialValue.value (borrowed location)) = .value (.ref ref)
  · right
    cases h
    rfl
  · left
    exact h

def undefDrops (store : ProgramStore) :
    Drops store [.undef] store := by
  exact ProgramStore.Drops.nonOwner (by intro ref; left; simp) ProgramStore.Drops.nil

def S0 : ProgramStore := ProgramStore.empty
def Sx : ProgramStore := S0.declare "x" l (.int 1)
def SxHeap1 : ProgramStore := (Sx.boxAt 1 (.int 1)).fst
def S4 : ProgramStore := SxHeap1.declare "y" l (owned (.heap 1))
def S4Heap2 : ProgramStore := (S4.boxAt 2 (.int 0)).fst
def S5 : ProgramStore := S4Heap2.declare "z" m (owned (.heap 2))
def S6 : ProgramStore :=
  (S5.update (.var "y") { value := .value (borrowed (.var "z")), lifetime := l }).erase
    (.heap 1)
def S6AfterMoveZ : ProgramStore :=
  S6.update (.var "z") { value := .undef, lifetime := m }
def S7 : ProgramStore :=
  S6AfterMoveZ.update (.var "y")
    { value := .value (owned (.heap 2)), lifetime := l }
def S8 : ProgramStore :=
  S7.update (.heap 2) { value := .undef, lifetime := Lifetime.root }
def S9 : ProgramStore :=
  S8.erase (.var "z")
def Sfinal : ProgramStore :=
  ((S9.erase (.var "x")).erase (.var "y")).erase (.heap 2)

def declareX : Term := .letMut "x" (.val (.int 1))
def declareY : Term := .letMut "y" (.box (.copy x))
def declareZ : Term := .letMut "z" (.box (.val (.int 0)))
def assignBorrowZ : Term := .assign y (.borrow false z)
def assignMoveZ : Term := .assign y (.move z)
def readThroughY : Term := .move derefY
def innerBlock : Term :=
  .block m [declareZ, assignBorrowZ, assignMoveZ, readThroughY]
def workedProgram : Term :=
  .block l [declareX, declareY, innerBlock]

theorem declare_x_step :
    Step S0 l workedProgram Sx (.block l [.val .unit, declareY, innerBlock]) := by
  unfold workedProgram declareX S0 Sx l
  exact Step.blockA (Step.declare rfl)

theorem seq_after_declare_x :
    Step Sx l (.block l [.val .unit, declareY, innerBlock])
      Sx (.block l [declareY, innerBlock]) := by
  exact Step.seq (unitDrops _)

theorem copy_x_for_y_box :
    Step Sx l (.block l [declareY, innerBlock])
      Sx (.block l [.letMut "y" (.box (.val (.int 1))), innerBlock]) := by
  unfold declareY x
  exact Step.blockA (Step.subDeclare (Step.subBox (Step.copy (valueLifetime := l) (by
    simp [Sx, S0, l, ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.update]))))

theorem allocate_y_box :
    Step Sx l (.block l [.letMut "y" (.box (.val (.int 1))), innerBlock])
      SxHeap1 (.block l [.letMut "y" (.val (owned (.heap 1))), innerBlock]) := by
  unfold SxHeap1 owned
  exact Step.blockA (Step.subDeclare (Step.box (address := 1)
    (ref := { location := .heap 1, owner := true }) (by
    simp [Sx, S0, l, ProgramStore.fresh, ProgramStore.declare,
      ProgramStore.update]) (by simp [ProgramStore.boxAt])))

theorem declare_y_step :
    Step SxHeap1 l (.block l [.letMut "y" (.val (owned (.heap 1))), innerBlock])
      S4 (.block l [.val .unit, innerBlock]) := by
  unfold S4 owned
  exact Step.blockA (Step.declare rfl)

theorem seq_after_declare_y :
    Step S4 l (.block l [.val .unit, innerBlock]) S4 (.block l [innerBlock]) := by
  exact Step.seq (unitDrops _)

theorem allocate_z_box :
    Step S4 l innerBlock S4Heap2
      (.block m [.letMut "z" (.val (owned (.heap 2))), assignBorrowZ, assignMoveZ, readThroughY]) := by
  unfold innerBlock declareZ owned
  exact Step.blockA (Step.subDeclare (Step.box (address := 2)
    (ref := { location := .heap 2, owner := true }) (by
    simp [S4, SxHeap1, Sx, S0, l, ProgramStore.fresh,
      ProgramStore.boxAt, ProgramStore.declare, ProgramStore.update])
    (by simp [S4Heap2, ProgramStore.boxAt])))

theorem declare_z_step :
    Step S4Heap2 l
      (.block m [.letMut "z" (.val (owned (.heap 2))), assignBorrowZ, assignMoveZ, readThroughY])
      S5 (.block m [.val .unit, assignBorrowZ, assignMoveZ, readThroughY]) := by
  unfold S5 owned
  exact Step.blockA (Step.declare rfl)

theorem seq_after_declare_z :
    Step S5 m (.block m [.val .unit, assignBorrowZ, assignMoveZ, readThroughY])
      S5 (.block m [assignBorrowZ, assignMoveZ, readThroughY]) := by
  exact Step.seq (unitDrops _)

theorem borrow_z_under_assignment :
    Step S5 m assignBorrowZ S5 (.assign y (.val (borrowed (.var "z")))) := by
  unfold assignBorrowZ z borrowed
  exact Step.subAssign (Step.borrow (by simp [ProgramStore.loc]))

theorem assign_y_borrow_z :
    Step S5 m (.assign y (.val (borrowed (.var "z")))) S6 (.val .unit) := by
  refine Step.assign
    (store₂ := S5.update (.var "y") { value := .value (borrowed (.var "z")), lifetime := l })
    (oldSlot := { value := .value (owned (.heap 1)), lifetime := l }) ?_ ?_ ?_
  · simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, S5, S4Heap2, S4, SxHeap1, Sx, S0, y, l, m,
      owned]
  · simp [ProgramStore.write, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, S5, S4Heap2, S4, SxHeap1, Sx, S0, y, l, m,
      borrowed, owned]
  · refine ProgramStore.Drops.ownerPresent
      (slot := { value := .value (.int 1), lifetime := Lifetime.root }) rfl ?_ ?_
    · simp [ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update, S5, S4Heap2,
        S4, SxHeap1, Sx, S0, l, m, borrowed, owned]
    · simpa [ProgramStore.erase, ProgramStore.update, S6, S5, S4Heap2, S4, SxHeap1,
        Sx, S0, y, l, m, borrowed, owned] using
        intDrops
          ((S5.update (.var "y")
            { value := .value (borrowed (.var "z")), lifetime := l }).erase (.heap 1)) 1

theorem move_z_under_assignment :
    Step S6 m assignMoveZ S6AfterMoveZ (.assign y (.val (owned (.heap 2)))) := by
  unfold assignMoveZ S6AfterMoveZ S6 S5 S4Heap2 S4 SxHeap1 Sx S0 y z l m borrowed owned
  exact Step.subAssign (Step.move (valueLifetime := [0, 0])
    (by simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, ProgramStore.erase])
    (by simp [ProgramStore.write, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, ProgramStore.erase]))

theorem assign_y_move_z :
    Step S6AfterMoveZ m (.assign y (.val (owned (.heap 2)))) S7 (.val .unit) := by
  refine Step.assign
    (store₂ := S7)
    (oldSlot := { value := .value (borrowed (.var "z")), lifetime := l }) ?_ ?_ ?_
  · simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, ProgramStore.erase, S6AfterMoveZ, S6, S5,
      S4Heap2, S4, SxHeap1, Sx, S0, y, l, m, borrowed, owned]
  · simp [ProgramStore.write, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, ProgramStore.erase, S7, S6AfterMoveZ, S6,
      S5, S4Heap2, S4, SxHeap1, Sx, S0, y, l, m, borrowed, owned]
  · exact borrowDrops _ (.var "z")

theorem read_through_y_step :
    Step S7 m readThroughY S8 (.val (.int 0)) := by
  unfold readThroughY derefY S8 S7 S6AfterMoveZ S6 S5 S4Heap2 S4 SxHeap1 Sx S0
    y l m borrowed owned
  exact Step.move (valueLifetime := Lifetime.root)
    (by simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, ProgramStore.erase])
    (by simp [ProgramStore.write, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, ProgramStore.erase])

theorem drop_inner_lifetime :
    DropsLifetime S8 m S9 := by
  refine ProgramStore.DropsLifetime.intro
    (dropSet := [.value (.ref { location := .var "z", owner := true })]) ?_ ?_
  · intro value
    constructor
    · intro hmem
      simp at hmem
      subst hmem
      refine ⟨.var "z", { value := .undef, lifetime := m }, ?_, rfl, rfl⟩
      simp [S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
        l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
        ProgramStore.erase]
    · intro h
      rcases h with ⟨location, slot, hslot, hlifetime, hvalue⟩
      subst hvalue
      simp
      cases location with
      | var name =>
          by_cases hy : name = "y"
          · subst hy
            simp [S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
              l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
              ProgramStore.erase] at hslot
            cases hslot
            simp [m] at hlifetime
          · by_cases hz : name = "z"
            · subst hz
              rfl
            · simp [S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
                l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
                ProgramStore.erase, hy, hz] at hslot
              by_cases hx : name = "x"
              · subst hx
                simp at hslot
                cases hslot
                simp [m] at hlifetime
              · simp [hx] at hslot
      | heap address =>
          by_cases h2 : address = 2
          · subst h2
            simp [S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
              l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
              ProgramStore.erase] at hslot
            cases hslot
            simp [m] at hlifetime
            contradiction
          · by_cases h1 : address = 1
            · subst h1
              simp [S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
                l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
                ProgramStore.erase] at hslot
            · simp [S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
                l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
                ProgramStore.erase, h1, h2] at hslot
  · refine ProgramStore.Drops.ownerPresent
      (slot := { value := .undef, lifetime := m }) rfl ?_ ?_
    · simp [S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
        l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
        ProgramStore.erase]
    · unfold S9
      exact ProgramStore.Drops.nonOwner (by intro ref; left; simp) ProgramStore.Drops.nil

theorem inner_block_returns_zero :
    Step S8 l (.block m [.val (.int 0)]) S9 (.val (.int 0)) := by
  exact Step.blockB drop_inner_lifetime

theorem drop_outer_lifetime :
    DropsLifetime S9 l Sfinal := by
  refine ProgramStore.DropsLifetime.intro
    (dropSet := [
      .value (.ref { location := .var "x", owner := true }),
      .value (.ref { location := .var "y", owner := true })]) ?_ ?_
  · intro value
    constructor
    · intro hmem
      simp at hmem
      rcases hmem with hvalue | hvalue
      · subst hvalue
        refine ⟨.var "x", { value := .value (.int 1), lifetime := l }, ?_, rfl, rfl⟩
        simp [S9, S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
          l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
          ProgramStore.erase]
      · subst hvalue
        refine ⟨.var "y", { value := .value (owned (.heap 2)), lifetime := l }, ?_, rfl, rfl⟩
        simp [S9, S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
          l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
          ProgramStore.erase, owned]
    · intro h
      rcases h with ⟨location, slot, hslot, hlifetime, hvalue⟩
      subst hvalue
      simp
      cases location with
      | var name =>
          by_cases hx : name = "x"
          · subst hx
            left
            rfl
          · by_cases hy : name = "y"
            · subst hy
              right
              rfl
            · simp [S9, S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
                l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
                ProgramStore.erase, hx, hy] at hslot
              by_cases hz : name = "z"
              · subst hz
                simp at hslot
              · simp [hz] at hslot
      | heap address =>
          by_cases h2 : address = 2
          · subst h2
            simp [S9, S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
              l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
              ProgramStore.erase] at hslot
            cases hslot
            simp [l] at hlifetime
            contradiction
          · by_cases h1 : address = 1
            · subst h1
              simp [S9, S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
                l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
                ProgramStore.erase] at hslot
            · simp [S9, S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
                l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
                ProgramStore.erase, h1, h2] at hslot
  · refine ProgramStore.Drops.ownerPresent
      (slot := { value := .value (.int 1), lifetime := l }) rfl ?_ ?_
    · simp [S9, S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
        l, m, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
        ProgramStore.erase]
    · refine ProgramStore.Drops.nonOwner (by intro ref; left; simp) ?_
      refine ProgramStore.Drops.ownerPresent
        (slot := { value := .value (owned (.heap 2)), lifetime := l }) rfl ?_ ?_
      · simp [S9, S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
          l, m, owned, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
          ProgramStore.erase]
      · refine ProgramStore.Drops.ownerPresent
          (slot := { value := .undef, lifetime := Lifetime.root }) rfl ?_ ?_
        · simp [S9, S8, S7, S6AfterMoveZ, S6, S5, S4Heap2, S4, SxHeap1, Sx, S0,
            l, m, owned, ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update,
            ProgramStore.erase]
        · unfold Sfinal
          exact undefDrops _

theorem outer_block_returns_zero :
    Step S9 l (.block l [.val (.int 0)]) Sfinal (.val (.int 0)) := by
  exact Step.blockB drop_outer_lifetime

def paperState4Term : Term :=
  .block l [innerBlock]

def paperState5Term : Term :=
  .block l [.block m [assignBorrowZ, assignMoveZ, readThroughY]]

def paperState6Term : Term :=
  .block l [.block m [assignMoveZ, readThroughY]]

def paperState7Term : Term :=
  .block l [.block m [readThroughY]]

def paperState8Term : Term :=
  .block l [.block m [.val (.int 0)]]

/-- Paper Section 3.2.4, state (4). -/
theorem workedProgram_to_paper_state4 :
    MultiStep S0 l workedProgram S4 paperState4Term := by
  unfold paperState4Term
  exact MultiStep.trans declare_x_step <|
    MultiStep.trans seq_after_declare_x <|
    MultiStep.trans copy_x_for_y_box <|
    MultiStep.trans allocate_y_box <|
    MultiStep.trans declare_y_step <|
    MultiStep.trans seq_after_declare_y <|
    MultiStep.refl

/-- Paper Section 3.2.4, state (5). -/
theorem workedProgram_to_paper_state5 :
    MultiStep S0 l workedProgram S5 paperState5Term := by
  unfold paperState5Term
  exact MultiStep.trans declare_x_step <|
    MultiStep.trans seq_after_declare_x <|
    MultiStep.trans copy_x_for_y_box <|
    MultiStep.trans allocate_y_box <|
    MultiStep.trans declare_y_step <|
    MultiStep.trans seq_after_declare_y <|
    MultiStep.trans (Step.blockA allocate_z_box) <|
    MultiStep.trans (Step.blockA declare_z_step) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.refl

/-- Paper Section 3.2.4, state (6). -/
theorem workedProgram_to_paper_state6 :
    MultiStep S0 l workedProgram S6 paperState6Term := by
  unfold paperState6Term
  exact MultiStep.trans declare_x_step <|
    MultiStep.trans seq_after_declare_x <|
    MultiStep.trans copy_x_for_y_box <|
    MultiStep.trans allocate_y_box <|
    MultiStep.trans declare_y_step <|
    MultiStep.trans seq_after_declare_y <|
    MultiStep.trans (Step.blockA allocate_z_box) <|
    MultiStep.trans (Step.blockA declare_z_step) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA borrow_z_under_assignment)) <|
    MultiStep.trans (Step.blockA (Step.blockA assign_y_borrow_z)) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.refl

/-- Paper Section 3.2.4, state (7). -/
theorem workedProgram_to_paper_state7 :
    MultiStep S0 l workedProgram S7 paperState7Term := by
  unfold paperState7Term
  exact MultiStep.trans declare_x_step <|
    MultiStep.trans seq_after_declare_x <|
    MultiStep.trans copy_x_for_y_box <|
    MultiStep.trans allocate_y_box <|
    MultiStep.trans declare_y_step <|
    MultiStep.trans seq_after_declare_y <|
    MultiStep.trans (Step.blockA allocate_z_box) <|
    MultiStep.trans (Step.blockA declare_z_step) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA borrow_z_under_assignment)) <|
    MultiStep.trans (Step.blockA (Step.blockA assign_y_borrow_z)) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA move_z_under_assignment)) <|
    MultiStep.trans (Step.blockA (Step.blockA assign_y_move_z)) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.refl

/-- Paper Section 3.2.4, state (8). -/
theorem workedProgram_to_paper_state8 :
    MultiStep S0 l workedProgram S8 paperState8Term := by
  unfold paperState8Term
  exact MultiStep.trans declare_x_step <|
    MultiStep.trans seq_after_declare_x <|
    MultiStep.trans copy_x_for_y_box <|
    MultiStep.trans allocate_y_box <|
    MultiStep.trans declare_y_step <|
    MultiStep.trans seq_after_declare_y <|
    MultiStep.trans (Step.blockA allocate_z_box) <|
    MultiStep.trans (Step.blockA declare_z_step) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA borrow_z_under_assignment)) <|
    MultiStep.trans (Step.blockA (Step.blockA assign_y_borrow_z)) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA move_z_under_assignment)) <|
    MultiStep.trans (Step.blockA (Step.blockA assign_y_move_z)) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA read_through_y_step)) <|
    MultiStep.refl

theorem workedProgram_reduces_to_zero :
    MultiStep S0 l workedProgram Sfinal (.val (.int 0)) := by
  exact MultiStep.trans declare_x_step <|
    MultiStep.trans seq_after_declare_x <|
    MultiStep.trans copy_x_for_y_box <|
    MultiStep.trans allocate_y_box <|
    MultiStep.trans declare_y_step <|
    MultiStep.trans seq_after_declare_y <|
    MultiStep.trans (Step.blockA allocate_z_box) <|
    MultiStep.trans (Step.blockA declare_z_step) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA borrow_z_under_assignment)) <|
    MultiStep.trans (Step.blockA (Step.blockA assign_y_borrow_z)) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA move_z_under_assignment)) <|
    MultiStep.trans (Step.blockA (Step.blockA assign_y_move_z)) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA read_through_y_step)) <|
    MultiStep.trans (Step.blockA inner_block_returns_zero) <|
    MultiStep.trans outer_block_returns_zero <|
    MultiStep.refl

end WorkedExample

namespace InvalidBorrowExample

/-!
Section 3.3 example (9).  Operationally this program reduces to `unit`, but it
is intentionally not type-and-borrow safe: `x` is assigned while mutably
borrowed by `y`.
-/

def l : Lifetime := [1]

def x : LVal := .var "x"
def y : LVal := .var "y"

def borrowed (location : Location) : Value :=
  .ref { location := location, owner := false }

def unitDrops (store : ProgramStore) :
    Drops store [.value .unit] store := by
  exact ProgramStore.Drops.nonOwner (by intro ref; left; simp) ProgramStore.Drops.nil

def intDrops (store : ProgramStore) (n : Int) :
    Drops store [.value (.int n)] store := by
  exact ProgramStore.Drops.nonOwner (by intro ref; left; simp) ProgramStore.Drops.nil

def borrowDrops (store : ProgramStore) (location : Location) :
    Drops store [.value (borrowed location)] store := by
  refine ProgramStore.Drops.nonOwner ?_ ProgramStore.Drops.nil
  intro ref
  by_cases h : (PartialValue.value (borrowed location)) = .value (.ref ref)
  · right
    cases h
    rfl
  · left
    exact h

def S0 : ProgramStore := ProgramStore.empty
def Sx : ProgramStore := S0.declare "x" l (.int 0)
def Sy : ProgramStore := Sx.declare "y" l (borrowed (.var "x"))
def Sassigned : ProgramStore :=
  Sy.update (.var "x") { value := .value (.int 1), lifetime := l }
def Sfinal : ProgramStore :=
  (Sassigned.erase (.var "x")).erase (.var "y")

def declareX : Term := .letMut "x" (.val (.int 0))
def declareY : Term := .letMut "y" (.borrow true x)
def assignX : Term := .assign x (.val (.int 1))
def invalidProgram : Term := .block l [declareX, declareY, assignX]

theorem declare_x_step :
    Step S0 l invalidProgram Sx (.block l [.val .unit, declareY, assignX]) := by
  unfold invalidProgram declareX S0 Sx l
  exact Step.blockA (Step.declare rfl)

theorem seq_after_declare_x :
    Step Sx l (.block l [.val .unit, declareY, assignX])
      Sx (.block l [declareY, assignX]) := by
  exact Step.seq (unitDrops _)

theorem borrow_x_under_declare_y :
    Step Sx l (.block l [declareY, assignX])
      Sx (.block l [.letMut "y" (.val (borrowed (.var "x"))), assignX]) := by
  unfold declareY x borrowed
  exact Step.blockA (Step.subDeclare (Step.borrow (by simp [ProgramStore.loc])))

theorem declare_y_step :
    Step Sx l (.block l [.letMut "y" (.val (borrowed (.var "x"))), assignX])
      Sy (.block l [.val .unit, assignX]) := by
  unfold Sy borrowed
  exact Step.blockA (Step.declare rfl)

theorem seq_after_declare_y :
    Step Sy l (.block l [.val .unit, assignX])
      Sy (.block l [assignX]) := by
  exact Step.seq (unitDrops _)

theorem assign_x_while_borrowed_step :
    Step Sy l (.block l [assignX]) Sassigned (.block l [.val .unit]) := by
  unfold assignX Sassigned Sy Sx S0 x l borrowed
  exact Step.blockA (Step.assign
    (oldSlot := { value := .value (.int 0), lifetime := [1] })
    (store₂ := Sassigned)
    (by simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.update])
    (by
      unfold Sassigned Sy Sx S0 l borrowed
      rfl)
    (intDrops _ 0))

theorem drop_invalid_lifetime :
    DropsLifetime Sassigned l Sfinal := by
  refine ProgramStore.DropsLifetime.intro
    (dropSet := [
      .value (.ref { location := .var "x", owner := true }),
      .value (.ref { location := .var "y", owner := true })]) ?_ ?_
  · intro value
    constructor
    · intro hmem
      simp at hmem
      rcases hmem with hvalue | hvalue
      · subst hvalue
        refine ⟨.var "x", { value := .value (.int 1), lifetime := l }, ?_, rfl, rfl⟩
        simp [Sassigned, Sy, Sx, S0, l, ProgramStore.declare, ProgramStore.update]
      · subst hvalue
        refine ⟨.var "y", { value := .value (borrowed (.var "x")), lifetime := l }, ?_, rfl, rfl⟩
        simp [Sassigned, Sy, Sx, S0, l, borrowed, ProgramStore.declare, ProgramStore.update]
    · intro h
      rcases h with ⟨location, slot, hslot, hlifetime, hvalue⟩
      subst hvalue
      simp
      cases location with
      | var name =>
          by_cases hx : name = "x"
          · subst hx
            left
            rfl
          · by_cases hy : name = "y"
            · subst hy
              right
              rfl
            · simp [Sassigned, Sy, Sx, S0, l, ProgramStore.declare,
                ProgramStore.update, hx, hy] at hslot
      | heap address =>
          simp [Sassigned, Sy, Sx, S0, l, ProgramStore.declare,
            ProgramStore.update] at hslot
  · refine ProgramStore.Drops.ownerPresent
      (slot := { value := .value (.int 1), lifetime := l }) rfl ?_ ?_
    · simp [Sassigned, Sy, Sx, S0, l, ProgramStore.declare, ProgramStore.update]
    · refine ProgramStore.Drops.nonOwner (by intro ref; left; simp) ?_
      refine ProgramStore.Drops.ownerPresent
        (slot := { value := .value (borrowed (.var "x")), lifetime := l }) rfl ?_ ?_
      · simp [Sassigned, Sy, Sx, S0, l, borrowed, ProgramStore.declare,
          ProgramStore.update, ProgramStore.erase]
      · unfold Sfinal
        exact borrowDrops _ (.var "x")

theorem invalid_program_returns_unit :
    Step Sassigned l (.block l [.val .unit]) Sfinal (.val .unit) := by
  exact Step.blockB drop_invalid_lifetime

theorem invalidProgram_reduces_to_unit :
    MultiStep S0 l invalidProgram Sfinal (.val .unit) := by
  exact MultiStep.trans declare_x_step <|
    MultiStep.trans seq_after_declare_x <|
    MultiStep.trans borrow_x_under_declare_y <|
    MultiStep.trans declare_y_step <|
    MultiStep.trans seq_after_declare_y <|
    MultiStep.trans assign_x_while_borrowed_step <|
    MultiStep.trans invalid_program_returns_unit <|
    MultiStep.refl

end InvalidBorrowExample

namespace InvalidEscapingBorrowExample

/-!
Section 3.3 example (10).  Operationally this can reduce past the inner block
and move `y` into `w`, but it is not type-and-borrow safe: after the inner block,
`y` contains a borrowed reference to `z`, whose lifetime has ended.
A read of `w` afterwards would get the program stuck.
-/

def l : Lifetime := [2]
def m : Lifetime := [2, 0]

def x : LVal := .var "x"
def y : LVal := .var "y"
def z : LVal := .var "z"

def borrowed (location : Location) : Value :=
  .ref { location := location, owner := false }

def unitDrops (store : ProgramStore) :
    Drops store [.value .unit] store := by
  exact ProgramStore.Drops.nonOwner (by intro ref; left; simp) ProgramStore.Drops.nil

def intDrops (store : ProgramStore) (n : Int) :
    Drops store [.value (.int n)] store := by
  exact ProgramStore.Drops.nonOwner (by intro ref; left; simp) ProgramStore.Drops.nil

def borrowDrops (store : ProgramStore) (location : Location) :
    Drops store [.value (borrowed location)] store := by
  refine ProgramStore.Drops.nonOwner ?_ ProgramStore.Drops.nil
  intro ref
  by_cases h : (PartialValue.value (borrowed location)) = .value (.ref ref)
  · right
    cases h
    rfl
  · left
    exact h

def S0 : ProgramStore := ProgramStore.empty
def Sx : ProgramStore := S0.declare "x" l (.int 0)
def SyX : ProgramStore := Sx.declare "y" l (borrowed (.var "x"))
def Sz : ProgramStore := SyX.declare "z" m (.int 0)
def SyZ : ProgramStore :=
  Sz.update (.var "y") { value := .value (borrowed (.var "z")), lifetime := l }
def SafterInner : ProgramStore :=
  SyZ.erase (.var "z")
def SafterMoveY : ProgramStore :=
  SafterInner.update (.var "y") { value := .undef, lifetime := l }
def Sw : ProgramStore :=
  SafterMoveY.declare "w" l (borrowed (.var "z"))

def declareX : Term := .letMut "x" (.val (.int 0))
def declareY : Term := .letMut "y" (.borrow true x)
def declareZ : Term := .letMut "z" (.val (.int 0))
def assignYBorrowZ : Term := .assign y (.borrow true z)
def innerBlock : Term := .block m [declareZ, assignYBorrowZ]
def declareW : Term := .letMut "w" (.move y)
def invalidProgram : Term := .block l [declareX, declareY, innerBlock, declareW]

theorem declare_x_step :
    Step S0 l invalidProgram Sx (.block l [.val .unit, declareY, innerBlock, declareW]) := by
  unfold invalidProgram declareX S0 Sx l
  exact Step.blockA (Step.declare rfl)

theorem seq_after_declare_x :
    Step Sx l (.block l [.val .unit, declareY, innerBlock, declareW])
      Sx (.block l [declareY, innerBlock, declareW]) := by
  exact Step.seq (unitDrops _)

theorem borrow_x_under_declare_y :
    Step Sx l (.block l [declareY, innerBlock, declareW])
      Sx (.block l [.letMut "y" (.val (borrowed (.var "x"))), innerBlock, declareW]) := by
  unfold declareY x borrowed
  exact Step.blockA (Step.subDeclare (Step.borrow (by simp [ProgramStore.loc])))

theorem declare_y_step :
    Step Sx l (.block l [.letMut "y" (.val (borrowed (.var "x"))), innerBlock, declareW])
      SyX (.block l [.val .unit, innerBlock, declareW]) := by
  unfold SyX borrowed
  exact Step.blockA (Step.declare rfl)

theorem seq_after_declare_y :
    Step SyX l (.block l [.val .unit, innerBlock, declareW])
      SyX (.block l [innerBlock, declareW]) := by
  exact Step.seq (unitDrops _)

theorem declare_z_step :
    Step SyX l innerBlock Sz (.block m [.val .unit, assignYBorrowZ]) := by
  unfold innerBlock declareZ Sz
  exact Step.blockA (Step.declare rfl)

theorem seq_after_declare_z :
    Step Sz m (.block m [.val .unit, assignYBorrowZ])
      Sz (.block m [assignYBorrowZ]) := by
  exact Step.seq (unitDrops _)

theorem borrow_z_under_assignment :
    Step Sz m assignYBorrowZ Sz (.assign y (.val (borrowed (.var "z")))) := by
  unfold assignYBorrowZ z borrowed
  exact Step.subAssign (Step.borrow (by simp [ProgramStore.loc]))

theorem assign_y_borrow_z :
    Step Sz m (.assign y (.val (borrowed (.var "z")))) SyZ (.val .unit) := by
  refine Step.assign
    (store₂ := SyZ)
    (oldSlot := { value := .value (borrowed (.var "x")), lifetime := l }) ?_ ?_ ?_
  · simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.update, Sz, SyX, Sx, S0, y, l, m, borrowed]
  · simp [ProgramStore.write, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.update, SyZ, Sz, SyX, Sx, S0, y, l, m, borrowed]
  · exact borrowDrops _ (.var "x")

theorem drop_inner_lifetime :
    DropsLifetime SyZ m SafterInner := by
  refine ProgramStore.DropsLifetime.intro
    (dropSet := [.value (.ref { location := .var "z", owner := true })]) ?_ ?_
  · intro value
    constructor
    · intro hmem
      simp at hmem
      subst hmem
      refine ⟨.var "z", { value := .value (.int 0), lifetime := m }, ?_, rfl, rfl⟩
      simp [SyZ, Sz, SyX, Sx, S0, l, m, borrowed, ProgramStore.declare,
        ProgramStore.update]
    · intro h
      rcases h with ⟨location, slot, hslot, hlifetime, hvalue⟩
      subst hvalue
      simp
      cases location with
      | var name =>
          by_cases hx : name = "x"
          · subst hx
            simp [SyZ, Sz, SyX, Sx, S0, l, m, borrowed, ProgramStore.declare,
              ProgramStore.update] at hslot
            cases hslot
            simp [m] at hlifetime
          · by_cases hy : name = "y"
            · subst hy
              simp [SyZ, Sz, SyX, Sx, S0, l, m, borrowed, ProgramStore.declare,
                ProgramStore.update] at hslot
              cases hslot
              simp [m] at hlifetime
            · by_cases hz : name = "z"
              · subst hz
                rfl
              · simp [SyZ, Sz, SyX, Sx, S0, l, m, borrowed, ProgramStore.declare,
                  ProgramStore.update, hx, hy, hz] at hslot
      | heap address =>
          simp [SyZ, Sz, SyX, Sx, S0, l, m, borrowed, ProgramStore.declare,
            ProgramStore.update] at hslot
  · refine ProgramStore.Drops.ownerPresent
      (slot := { value := .value (.int 0), lifetime := m }) rfl ?_ ?_
    · simp [SyZ, Sz, SyX, Sx, S0, l, m, borrowed, ProgramStore.declare,
        ProgramStore.update]
    · unfold SafterInner
      exact intDrops _ 0

theorem inner_block_returns_unit :
    Step SyZ l (.block m [.val .unit]) SafterInner (.val .unit) := by
  exact Step.blockB drop_inner_lifetime

theorem seq_after_inner_block :
    Step SafterInner l (.block l [.val .unit, declareW])
      SafterInner (.block l [declareW]) := by
  exact Step.seq (unitDrops _)

theorem move_y_under_declare_w :
    Step SafterInner l (.block l [declareW])
      SafterMoveY (.block l [.letMut "w" (.val (borrowed (.var "z")))]) := by
  unfold declareW SafterMoveY SafterInner SyZ Sz SyX Sx S0 y l m borrowed
  exact Step.blockA (Step.subDeclare (Step.move (valueLifetime := [2])
    (by simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.update, ProgramStore.erase])
    (by simp [ProgramStore.write, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.update, ProgramStore.erase])))

theorem declare_w_with_escaping_borrow :
    Step SafterMoveY l (.block l [.letMut "w" (.val (borrowed (.var "z")))])
      Sw (.block l [.val .unit]) := by
  unfold Sw borrowed
  exact Step.blockA (Step.declare rfl)

theorem w_points_to_dropped_z :
    Sw.read (.var "w") =
      some { value := .value (borrowed (.var "z")), lifetime := l } := by
  simp [Sw, SafterMoveY, SafterInner, SyZ, Sz, SyX, Sx, S0, l, m, borrowed,
    ProgramStore.read, ProgramStore.loc, ProgramStore.declare, ProgramStore.update,
    ProgramStore.erase]

theorem z_has_been_dropped :
    Sw.slotAt (.var "z") = none := by
  simp [Sw, SafterMoveY, SafterInner, SyZ, Sz, SyX, Sx, S0, l, m, borrowed,
    ProgramStore.declare, ProgramStore.update, ProgramStore.erase]

theorem read_deref_w_after_z_dropped :
    Sw.read (.deref (.var "w")) = none := by
  simp [Sw, SafterMoveY, SafterInner, SyZ, Sz, SyX, Sx, S0, l, m, borrowed,
    ProgramStore.read, ProgramStore.loc, ProgramStore.declare, ProgramStore.update,
    ProgramStore.erase]

theorem deref_w_after_z_dropped_is_stuck :
    ¬ ∃ store' term', Step Sw l (.move (.deref (.var "w"))) store' term' := by
  intro h
  rcases h with ⟨store', term', hstep⟩
  cases hstep with
  | move hread _ =>
      simp [read_deref_w_after_z_dropped] at hread

theorem invalidProgram_reduces_to_escaping_borrow_state :
    MultiStep S0 l invalidProgram Sw (.block l [.val .unit]) := by
  exact MultiStep.trans declare_x_step <|
    MultiStep.trans seq_after_declare_x <|
    MultiStep.trans borrow_x_under_declare_y <|
    MultiStep.trans declare_y_step <|
    MultiStep.trans seq_after_declare_y <|
    MultiStep.trans (Step.blockA declare_z_step) <|
    MultiStep.trans (Step.blockA (Step.seq (unitDrops _))) <|
    MultiStep.trans (Step.blockA (Step.blockA borrow_z_under_assignment)) <|
    MultiStep.trans (Step.blockA (Step.blockA assign_y_borrow_z)) <|
    MultiStep.trans (Step.blockA inner_block_returns_unit) <|
    MultiStep.trans seq_after_inner_block <|
    MultiStep.trans move_y_under_declare_w <|
    MultiStep.trans declare_w_with_escaping_borrow <|
    MultiStep.refl

end InvalidEscapingBorrowExample

end Paper
end FWRust
