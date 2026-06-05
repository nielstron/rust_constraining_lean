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

end Paper
end LwRust
