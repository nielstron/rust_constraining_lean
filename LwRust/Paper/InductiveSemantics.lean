import LwRust.Paper.Runtime

/-!
Inductive presentation of the small-step operational semantics from Section 3.2.
-/

namespace LwRust
namespace Paper

open Core

/--
Paper Section 3.2 reduction relation:
`S₁ ▷ t₁ -→ S₂ ▷ t₂` in lifetime context `l`.
-/
inductive Step : ProgramStore → Lifetime → Term → ProgramStore → Term → Prop where
  /-- R-Copy. -/
  | copy {store : ProgramStore} {lifetime valueLifetime : Lifetime}
      {lv : LVal} {value : Value} :
      store.read lv = some { value := .value value, lifetime := valueLifetime } →
      Step store lifetime (.copy lv) store (.val value)

  /-- R-Move. -/
  | move {store₁ store₂ : ProgramStore} {lifetime valueLifetime : Lifetime}
      {lv : LVal} {value : Value} :
      store₁.read lv = some { value := .value value, lifetime := valueLifetime } →
      store₁.write lv .undef = some store₂ →
      Step store₁ lifetime (.move lv) store₂ (.val value)

  /-- R-Box. -/
  | box {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {address : Nat} {value : Value} {ref : Reference} :
      store₁.fresh (.heap address) →
      store₁.boxAt address value = (store₂, ref) →
      Step store₁ lifetime (.box (.val value)) store₂ (.val (.ref ref))

  /-- R-Borrow. -/
  | borrow {store : ProgramStore} {lifetime : Lifetime} {mutable : Bool}
      {lv : LVal} {location : Location} :
      store.loc lv = some location →
      Step store lifetime (.borrow mutable lv) store
        (.val (.ref { location := location, owner := false }))

  /-- R-Assign. -/
  | assign {store₁ store₂ store₃ : ProgramStore} {lifetime : Lifetime}
      {lhs : LVal} {oldSlot : StoreSlot} {value : Value} :
      store₁.read lhs = some oldSlot →
      Drops store₁ [oldSlot.value] store₂ →
      store₂.write lhs (.value value) = some store₃ →
      Step store₁ lifetime (.assign lhs (.val value)) store₃ (.val .unit)

  /-- R-Declare. -/
  | declare {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {x : Name} {value : Value} :
      store₂ = store₁.declare x lifetime value →
      Step store₁ lifetime (.letMut x (.val value)) store₂ (.val .unit)

  /-- R-Seq.  The paper's sequence syntax is represented by the term list in a block. -/
  | seq {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {value : Value} {next : Term} {rest : List Term} :
      Drops store₁ [.value value] store₂ →
      Step store₁ lifetime (.block lifetime (.val value :: next :: rest))
        store₂ (.block lifetime (next :: rest))

  /-- R-BlockA. -/
  | blockA {store₁ store₂ : ProgramStore} {lifetime blockLifetime : Lifetime}
      {term term' : Term} {rest : List Term} :
      Step store₁ blockLifetime term store₂ term' →
      Step store₁ lifetime (.block blockLifetime (term :: rest))
        store₂ (.block blockLifetime (term' :: rest))

  /-- R-BlockB. -/
  | blockB {store₁ store₂ : ProgramStore} {lifetime blockLifetime : Lifetime}
      {value : Value} :
      DropsLifetime store₁ blockLifetime store₂ →
      Step store₁ lifetime (.block blockLifetime [.val value]) store₂ (.val value)

  /-- R-Sub, `box E` evaluation-context instance. -/
  | subBox {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {term term' : Term} :
      Step store₁ lifetime term store₂ term' →
      Step store₁ lifetime (.box term) store₂ (.box term')

  /-- R-Sub, `let mut x = E` evaluation-context instance. -/
  | subDeclare {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {x : Name} {term term' : Term} :
      Step store₁ lifetime term store₂ term' →
      Step store₁ lifetime (.letMut x term) store₂ (.letMut x term')

  /-- R-Sub, `w = E` evaluation-context instance. -/
  | subAssign {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {lhs : LVal} {rhs rhs' : Term} :
      Step store₁ lifetime rhs store₂ rhs' →
      Step store₁ lifetime (.assign lhs rhs) store₂ (.assign lhs rhs')

/--
Paper Lemma 4.11 uses the reflexive-transitive closure of the reduction
relation; this is that multi-step relation.
-/
inductive MultiStep : ProgramStore → Lifetime → Term → ProgramStore → Term → Prop where
  | refl {store : ProgramStore} {lifetime : Lifetime} {term : Term} :
      MultiStep store lifetime term store term
  | trans {store₁ store₂ store₃ : ProgramStore} {lifetime : Lifetime}
      {term₁ term₂ term₃ : Term} :
      Step store₁ lifetime term₁ store₂ term₂ →
      MultiStep store₂ lifetime term₂ store₃ term₃ →
      MultiStep store₁ lifetime term₁ store₃ term₃

/--
Paper Lemmas 4.10 and 4.11 distinguish terminal states, represented here as
terms already reduced to a runtime value.
-/
def Terminal : Term → Prop
  | .val _ => True
  | _ => False

theorem terminal_iff_value (term : Term) :
    Terminal term ↔ ∃ value, term = .val value := by
  cases term <;> simp [Terminal]

theorem value_terminal (value : Value) :
    Terminal (.val value) := by
  trivial

theorem value_no_step {store store' : ProgramStore} {lifetime : Lifetime}
    {value : Value} {term' : Term} :
    ¬ Step store lifetime (.val value) store' term' := by
  intro h
  cases h

theorem terminal_no_step {store store' : ProgramStore} {lifetime : Lifetime}
    {term term' : Term} :
    Terminal term →
    ¬ Step store lifetime term store' term' := by
  intro hterminal hstep
  rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
  subst hterm
  exact value_no_step hstep

theorem multistep_value_inv {store finalStore : ProgramStore} {lifetime : Lifetime}
    {value : Value} {term : Term} :
    MultiStep store lifetime (.val value) finalStore term →
    finalStore = store ∧ term = .val value := by
  intro h
  cases h with
  | refl =>
      exact ⟨rfl, rfl⟩
  | trans hstep _ =>
      exact False.elim (value_no_step hstep)

theorem multistep_terminal_inv {store finalStore : ProgramStore} {lifetime : Lifetime}
    {term finalTerm : Term} :
    Terminal term →
    MultiStep store lifetime term finalStore finalTerm →
    finalStore = store ∧ finalTerm = term := by
  intro hterminal hmulti
  cases hmulti with
  | refl =>
      exact ⟨rfl, rfl⟩
  | trans hstep _ =>
      exact False.elim (terminal_no_step hterminal hstep)

theorem multistep_append {store₁ store₂ store₃ : ProgramStore} {lifetime : Lifetime}
    {term₁ term₂ term₃ : Term} :
    MultiStep store₁ lifetime term₁ store₂ term₂ →
    MultiStep store₂ lifetime term₂ store₃ term₃ →
    MultiStep store₁ lifetime term₁ store₃ term₃ := by
  intro hleft hright
  induction hleft with
  | refl =>
      exact hright
  | trans hstep _ ih =>
      exact MultiStep.trans hstep (ih hright)

theorem step_multistep {store store' : ProgramStore} {lifetime : Lifetime}
    {term term' : Term} :
    Step store lifetime term store' term' →
    MultiStep store lifetime term store' term' := by
  intro hstep
  exact MultiStep.trans hstep MultiStep.refl

theorem multistep_box_context {store finalStore : ProgramStore} {lifetime : Lifetime}
    {term finalTerm : Term} :
    MultiStep store lifetime term finalStore finalTerm →
    MultiStep store lifetime (.box term) finalStore (.box finalTerm) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subBox hstep) ih

theorem multistep_declare_context {store finalStore : ProgramStore} {lifetime : Lifetime}
    {x : Name} {term finalTerm : Term} :
    MultiStep store lifetime term finalStore finalTerm →
    MultiStep store lifetime (.letMut x term) finalStore (.letMut x finalTerm) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subDeclare hstep) ih

theorem multistep_assign_context {store finalStore : ProgramStore} {lifetime : Lifetime}
    {lhs : LVal} {rhs finalRhs : Term} :
    MultiStep store lifetime rhs finalStore finalRhs →
    MultiStep store lifetime (.assign lhs rhs) finalStore (.assign lhs finalRhs) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subAssign hstep) ih

theorem multistep_block_context {store finalStore : ProgramStore}
    {lifetime blockLifetime : Lifetime} {term finalTerm : Term} {rest : List Term} :
    MultiStep store blockLifetime term finalStore finalTerm →
    MultiStep store lifetime (.block blockLifetime (term :: rest))
      finalStore (.block blockLifetime (finalTerm :: rest)) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.blockA hstep) ih

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

def S0 : ProgramStore := ProgramStore.empty
def Sx : ProgramStore := S0.declare "x" l (.int 1)
def SxHeap1 : ProgramStore := (Sx.boxAt 1 (.int 1)).fst
def S4 : ProgramStore := SxHeap1.declare "y" l (owned (.heap 1))
def S4Heap2 : ProgramStore := (S4.boxAt 2 (.int 0)).fst
def S5 : ProgramStore := S4Heap2.declare "z" m (owned (.heap 2))
def S6 : ProgramStore :=
  (S5.erase (.heap 1)).update (.var "y")
    { value := .value (borrowed (.var "z")), lifetime := l }
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
    (store₂ := S5.erase (.heap 1))
    (oldSlot := { value := .value (owned (.heap 1)), lifetime := l }) ?_ ?_ ?_
  · simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, S5, S4Heap2, S4, SxHeap1, Sx, S0, y, l, m,
      owned]
  · refine ProgramStore.Drops.ownerPresent
      (slot := { value := .value (.int 1), lifetime := Lifetime.root }) rfl ?_ ?_
    · simp [ProgramStore.declare, ProgramStore.boxAt, ProgramStore.update, S5, S4Heap2,
        S4, SxHeap1, Sx, S0, l, m, owned]
    · exact intDrops (S5.erase (.heap 1)) 1
  · simp [ProgramStore.write, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, ProgramStore.erase, S6, S5, S4Heap2,
      S4, SxHeap1, Sx, S0, y, l, m, borrowed, owned]

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
    (store₂ := S6AfterMoveZ)
    (oldSlot := { value := .value (borrowed (.var "z")), lifetime := l }) ?_ ?_ ?_
  · simp [ProgramStore.read, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, ProgramStore.erase, S6AfterMoveZ, S6, S5,
      S4Heap2, S4, SxHeap1, Sx, S0, y, l, m, borrowed, owned]
  · exact borrowDrops _ (.var "z")
  · simp [ProgramStore.write, ProgramStore.loc, ProgramStore.declare,
      ProgramStore.boxAt, ProgramStore.update, ProgramStore.erase, S7, S6AfterMoveZ, S6,
      S5, S4Heap2, S4, SxHeap1, Sx, S0, y, l, m, borrowed, owned]

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
            simp [l, m] at hlifetime
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
                simp [l, m] at hlifetime
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

end WorkedExample

end Paper
end LwRust
