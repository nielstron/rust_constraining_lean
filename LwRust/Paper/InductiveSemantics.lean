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
      store₁.write lhs (.value value) = some store₂ →
      Drops store₂ [oldSlot.value] store₃ →
      Step store₁ lifetime (.assign lhs (.val value)) store₃ (.val .unit)

  /-- R-Declare. -/
  | declare {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {x : Name} {value : Value} :
      store₂ = store₁.declare x lifetime value →
      Step store₁ lifetime (.letMut x (.val value)) store₂ (.val .unit)

  /-- R-Seq.  The paper's sequence syntax is represented by the term list in a block. -/
  | seq {store₁ store₂ : ProgramStore} {lifetime blockLifetime : Lifetime}
      {value : Value} {next : Term} {rest : List Term} :
      Drops store₁ [.value value] store₂ →
      Step store₁ lifetime (.block blockLifetime (.val value :: next :: rest))
        store₂ (.block blockLifetime (next :: rest))

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

  /-- R-EqalT, Section 6.1.1. -/
  | eqTrue {store : ProgramStore} {lifetime : Lifetime} {value : Value} :
      Step store lifetime (.eq (.val value) (.val value)) store
        (.val (.bool true))

  /-- R-EqalF, Section 6.1.1. -/
  | eqFalse {store : ProgramStore} {lifetime : Lifetime} {left right : Value} :
      left ≠ right →
      Step store lifetime (.eq (.val left) (.val right)) store
        (.val (.bool false))

  /-- R-IfT, Section 6.1.1. -/
  | iteTrue {store : ProgramStore} {lifetime : Lifetime}
      {trueBranch falseBranch : Term} :
      Step store lifetime (.ite (.val (.bool true)) trueBranch falseBranch)
        store trueBranch

  /-- R-IfF, Section 6.1.1. -/
  | iteFalse {store : ProgramStore} {lifetime : Lifetime}
      {trueBranch falseBranch : Term} :
      Step store lifetime (.ite (.val (.bool false)) trueBranch falseBranch)
        store falseBranch

  /-- R-Sub, `E == t` evaluation-context instance (Definition 6.1). -/
  | subEqLeft {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {lhs lhs' rhs : Term} :
      Step store₁ lifetime lhs store₂ lhs' →
      Step store₁ lifetime (.eq lhs rhs) store₂ (.eq lhs' rhs)

  /-- R-Sub, `v == E` evaluation-context instance (Definition 6.1). -/
  | subEqRight {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {value : Value} {rhs rhs' : Term} :
      Step store₁ lifetime rhs store₂ rhs' →
      Step store₁ lifetime (.eq (.val value) rhs) store₂
        (.eq (.val value) rhs')

  /-- R-Sub, `if E {t}m else {s}n` evaluation-context instance
  (Definition 6.1).  The branches are deliberately *not* evaluation contexts,
  so a conditional reduces only through `R-IfT`/`R-IfF` once the condition is
  a value; erroneous conditions (e.g. an integer) are stuck. -/
  | subIte {store₁ store₂ : ProgramStore} {lifetime : Lifetime}
      {condition condition' trueBranch falseBranch : Term} :
      Step store₁ lifetime condition store₂ condition' →
      Step store₁ lifetime (.ite condition trueBranch falseBranch) store₂
        (.ite condition' trueBranch falseBranch)

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

theorem multistep_first_step_of_not_terminal {store finalStore : ProgramStore}
    {lifetime : Lifetime} {term : Term} {finalValue : Value} :
    ¬ Terminal term →
    MultiStep store lifetime term finalStore (.val finalValue) →
    ∃ store' term',
      Step store lifetime term store' term' ∧
      MultiStep store' lifetime term' finalStore (.val finalValue) := by
  intro hnotTerminal hmulti
  cases hmulti with
  | refl =>
      exact False.elim (hnotTerminal (value_terminal finalValue))
  | trans hstep hrest =>
      exact ⟨_, _, hstep, hrest⟩

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

theorem multistep_box_to_value_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {term : Term} {finalValue : Value} :
    MultiStep store lifetime (.box term) finalStore (.val finalValue) →
    ∃ midStore value,
      MultiStep store lifetime term midStore (.val value) ∧
      Step midStore lifetime (.box (.val value)) finalStore (.val finalValue) := by
  intro hmulti
  generalize hstart : Term.box term = start at hmulti
  generalize hend : Term.val finalValue = final at hmulti
  induction hmulti generalizing term finalValue with
  | refl =>
      cases hstart
      cases hend
  | trans hstep hrest ih =>
      cases hstart
      cases hstep with
      | box hfresh hbox =>
          rename_i address boxedValue ref
          rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
          subst hstore
          rw [hterm] at hend
          injection hend with hvalue
          subst hvalue
          rw [hterm]
          exact ⟨_, boxedValue, MultiStep.refl,
            Step.box hfresh hbox⟩
      | subBox hinnerStep =>
          rcases ih rfl hend with ⟨midStore, value, hinnerMulti, hboxStep⟩
          exact ⟨midStore, value, MultiStep.trans hinnerStep hinnerMulti, hboxStep⟩

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

theorem multistep_declare_to_value_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {x : Name} {term : Term} {finalValue : Value} :
    MultiStep store lifetime (.letMut x term) finalStore (.val finalValue) →
    ∃ midStore value,
      MultiStep store lifetime term midStore (.val value) ∧
      Step midStore lifetime (.letMut x (.val value)) finalStore (.val finalValue) := by
  intro hmulti
  generalize hstart : Term.letMut x term = start at hmulti
  generalize hend : Term.val finalValue = final at hmulti
  induction hmulti generalizing x term finalValue with
  | refl =>
      cases hstart
      cases hend
  | trans hstep hrest ih =>
      cases hstart
      cases hstep with
      | declare hstore =>
          rename_i declaredValue
          rcases multistep_value_inv hrest with ⟨hfinalStore, hterm⟩
          subst hfinalStore
          rw [hterm] at hend
          injection hend with hvalue
          subst hvalue
          rw [hterm]
          exact ⟨_, declaredValue, MultiStep.refl, Step.declare hstore⟩
      | subDeclare hinnerStep =>
          rcases ih rfl hend with ⟨midStore, value, hinnerMulti, hdeclareStep⟩
          exact ⟨midStore, value, MultiStep.trans hinnerStep hinnerMulti,
            hdeclareStep⟩

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

theorem multistep_assign_to_value_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {rhs : Term} {finalValue : Value} :
    MultiStep store lifetime (.assign lhs rhs) finalStore (.val finalValue) →
    ∃ midStore value,
      MultiStep store lifetime rhs midStore (.val value) ∧
      Step midStore lifetime (.assign lhs (.val value)) finalStore (.val finalValue) := by
  intro hmulti
  generalize hstart : Term.assign lhs rhs = start at hmulti
  generalize hend : Term.val finalValue = final at hmulti
  induction hmulti generalizing lhs rhs finalValue with
  | refl =>
      cases hstart
      cases hend
  | trans hstep hrest ih =>
      cases hstart
      cases hstep with
      | assign hread hwrite hdrops =>
          rename_i assignedValue
          rcases multistep_value_inv hrest with ⟨hfinalStore, hterm⟩
          subst hfinalStore
          rw [hterm] at hend
          injection hend with hvalue
          subst hvalue
          rw [hterm]
          exact ⟨_, assignedValue, MultiStep.refl,
            Step.assign hread hwrite hdrops⟩
      | subAssign hinnerStep =>
          rcases ih rfl hend with ⟨midStore, value, hinnerMulti, hassignStep⟩
          exact ⟨midStore, value, MultiStep.trans hinnerStep hinnerMulti,
            hassignStep⟩

/--
Every reduction step strictly decreases the structural term size: the core
calculus is terminating.
-/
theorem step_size_lt {store store' : ProgramStore} {lifetime : Lifetime}
    {term term' : Term} :
    Step store lifetime term store' term' →
    term'.size < term.size := by
  intro hstep
  induction hstep with
  | copy _ => simp [Term.size]
  | move _ _ => simp [Term.size]
  | box _ _ => simp [Term.size]
  | borrow _ => simp [Term.size]
  | assign _ _ _ => simp [Term.size]
  | declare _ => simp [Term.size]
  | seq _ => simp [Term.size, Term.sizeList]
  | blockA _ ih =>
      simp only [Term.size, Term.sizeList]
      omega
  | blockB _ => simp [Term.size, Term.sizeList]
  | subBox _ ih =>
      simp only [Term.size]
      omega
  | subDeclare _ ih =>
      simp only [Term.size]
      omega
  | subAssign _ ih =>
      simp only [Term.size]
      omega
  | eqTrue => simp [Term.size]
  | eqFalse _ => simp [Term.size]
  | iteTrue =>
      rename_i trueBranch falseBranch
      have := Term.size_pos falseBranch
      simp only [Term.size]
      omega
  | iteFalse =>
      rename_i trueBranch falseBranch
      have := Term.size_pos trueBranch
      simp only [Term.size]
      omega
  | subEqLeft _ ih =>
      simp only [Term.size]
      omega
  | subEqRight _ ih =>
      simp only [Term.size]
      omega
  | subIte _ ih =>
      simp only [Term.size]
      omega

/--
Prefix inversion for `box` runs: an arbitrary partial execution is either
still inside the operand, or the operand finished and the box redex fired,
after which the term is a value and the run is over.
-/
theorem multistep_box_prefix_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {term finalTerm : Term} :
    MultiStep store lifetime (.box term) finalStore finalTerm →
    (∃ term', finalTerm = .box term' ∧
      MultiStep store lifetime term finalStore term') ∨
    (∃ midStore value, MultiStep store lifetime term midStore (.val value) ∧
      Step midStore lifetime (.box (.val value)) finalStore finalTerm) := by
  intro hmulti
  generalize hstart : Term.box term = start at hmulti
  induction hmulti generalizing term with
  | refl =>
      cases hstart
      exact Or.inl ⟨term, rfl, MultiStep.refl⟩
  | trans hstep hrest ih =>
      cases hstart
      cases hstep with
      | box hfresh hbox =>
          rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
          subst hstore
          subst hterm
          exact Or.inr ⟨_, _, MultiStep.refl, Step.box hfresh hbox⟩
      | subBox hinner =>
          rcases ih rfl with ⟨term', hfinal, hms⟩ | ⟨midStore, value, hms, hredex⟩
          · exact Or.inl ⟨term', hfinal, MultiStep.trans hinner hms⟩
          · exact Or.inr ⟨midStore, value, MultiStep.trans hinner hms, hredex⟩

/-- Prefix inversion for `let mut` runs. -/
theorem multistep_declare_prefix_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {x : Name} {term finalTerm : Term} :
    MultiStep store lifetime (.letMut x term) finalStore finalTerm →
    (∃ term', finalTerm = .letMut x term' ∧
      MultiStep store lifetime term finalStore term') ∨
    (∃ midStore value, MultiStep store lifetime term midStore (.val value) ∧
      Step midStore lifetime (.letMut x (.val value)) finalStore finalTerm) := by
  intro hmulti
  generalize hstart : Term.letMut x term = start at hmulti
  induction hmulti generalizing term with
  | refl =>
      cases hstart
      exact Or.inl ⟨term, rfl, MultiStep.refl⟩
  | trans hstep hrest ih =>
      cases hstart
      cases hstep with
      | declare hstore =>
          rcases multistep_value_inv hrest with ⟨hstoreEq, hterm⟩
          subst hstoreEq
          subst hterm
          exact Or.inr ⟨_, _, MultiStep.refl, Step.declare hstore⟩
      | subDeclare hinner =>
          rcases ih rfl with ⟨term', hfinal, hms⟩ | ⟨midStore, value, hms, hredex⟩
          · exact Or.inl ⟨term', hfinal, MultiStep.trans hinner hms⟩
          · exact Or.inr ⟨midStore, value, MultiStep.trans hinner hms, hredex⟩

/-- Prefix inversion for assignment runs. -/
theorem multistep_assign_prefix_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {rhs finalTerm : Term} :
    MultiStep store lifetime (.assign lhs rhs) finalStore finalTerm →
    (∃ rhs', finalTerm = .assign lhs rhs' ∧
      MultiStep store lifetime rhs finalStore rhs') ∨
    (∃ midStore value, MultiStep store lifetime rhs midStore (.val value) ∧
      Step midStore lifetime (.assign lhs (.val value)) finalStore finalTerm) := by
  intro hmulti
  generalize hstart : Term.assign lhs rhs = start at hmulti
  induction hmulti generalizing rhs with
  | refl =>
      cases hstart
      exact Or.inl ⟨rhs, rfl, MultiStep.refl⟩
  | trans hstep hrest ih =>
      cases hstart
      cases hstep with
      | assign hread hwrite hdrops =>
          rcases multistep_value_inv hrest with ⟨hstoreEq, hterm⟩
          subst hstoreEq
          subst hterm
          exact Or.inr ⟨_, _, MultiStep.refl, Step.assign hread hwrite hdrops⟩
      | subAssign hinner =>
          rcases ih rfl with ⟨rhs', hfinal, hms⟩ | ⟨midStore, value, hms, hredex⟩
          · exact Or.inl ⟨rhs', hfinal, MultiStep.trans hinner hms⟩
          · exact Or.inr ⟨midStore, value, MultiStep.trans hinner hms, hredex⟩

/--
Prefix inversion for block runs: an arbitrary partial execution is either
still inside the head term, or the head finished and the block continued
through a sequence drop (more terms remain) or the block-exit lifetime drop
(last term).
-/
theorem multistep_block_prefix_inv {store finalStore : ProgramStore}
    {lifetime blockLifetime : Lifetime} {term finalTerm : Term}
    {rest : List Term} :
    MultiStep store lifetime (.block blockLifetime (term :: rest))
      finalStore finalTerm →
    (∃ term', finalTerm = .block blockLifetime (term' :: rest) ∧
      MultiStep store blockLifetime term finalStore term') ∨
    (∃ midStore value,
      MultiStep store blockLifetime term midStore (.val value) ∧
      ((∃ next rest' dropStore, rest = next :: rest' ∧
          Drops midStore [.value value] dropStore ∧
          MultiStep dropStore lifetime (.block blockLifetime (next :: rest'))
            finalStore finalTerm) ∨
       (rest = [] ∧ ∃ dropStore,
          DropsLifetime midStore blockLifetime dropStore ∧
          finalStore = dropStore ∧ finalTerm = .val value))) := by
  intro hmulti
  generalize hstart : Term.block blockLifetime (term :: rest) = start at hmulti
  induction hmulti generalizing term with
  | refl =>
      cases hstart
      exact Or.inl ⟨term, rfl, MultiStep.refl⟩
  | trans hstep hrest ih =>
      cases hstart
      cases hstep with
      | seq hdrops =>
          exact Or.inr ⟨_, _, MultiStep.refl,
            Or.inl ⟨_, _, _, rfl, hdrops, hrest⟩⟩
      | blockA hhead =>
          rcases ih rfl with ⟨term', hfinal, hms⟩ |
            ⟨midStore, value, hms, hcont⟩
          · exact Or.inl ⟨term', hfinal, MultiStep.trans hhead hms⟩
          · exact Or.inr ⟨midStore, value, MultiStep.trans hhead hms, hcont⟩
      | blockB hdropsL =>
          rcases multistep_value_inv hrest with ⟨hstoreEq, hterm⟩
          subst hstoreEq
          subst hterm
          exact Or.inr ⟨_, _, MultiStep.refl,
            Or.inr ⟨rfl, _, hdropsL, rfl, rfl⟩⟩

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

theorem multistep_block_to_value_first_step_inv {store finalStore : ProgramStore}
    {lifetime blockLifetime : Lifetime} {terms : List Term} {finalValue : Value} :
    MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
    (∃ value next rest store',
      terms = .val value :: next :: rest ∧
      Drops store [.value value] store' ∧
      MultiStep store' lifetime (.block blockLifetime (next :: rest))
        finalStore (.val finalValue)) ∨
    (∃ term rest store' term',
      terms = term :: rest ∧
      Step store blockLifetime term store' term' ∧
      MultiStep store' lifetime (.block blockLifetime (term' :: rest))
        finalStore (.val finalValue)) ∨
    (∃ value store',
      terms = [.val value] ∧
      DropsLifetime store blockLifetime store' ∧
      MultiStep store' lifetime (.val value) finalStore (.val finalValue)) := by
  intro hmulti
  rcases multistep_first_step_of_not_terminal
      (term := .block blockLifetime terms)
      (by simp [Terminal]) hmulti with
    ⟨store', term', hstep, hrest⟩
  cases hstep with
  | seq hdrops =>
      exact Or.inl ⟨_, _, _, store', rfl, hdrops, hrest⟩
  | blockA hhead =>
      exact Or.inr (Or.inl ⟨_, _, store', _, rfl, hhead, hrest⟩)
  | blockB hdrops =>
      exact Or.inr (Or.inr ⟨_, store', rfl, hdrops, hrest⟩)

/--
Operational decomposition for a nonempty block body: before the block can
finish, its head term reaches a value, and the block then continues from the
value-headed body.
-/
theorem multistep_block_head_to_value_inv {store finalStore : ProgramStore}
    {lifetime blockLifetime : Lifetime} {term : Term} {rest : List Term}
    {finalValue : Value} :
    MultiStep store lifetime (.block blockLifetime (term :: rest))
      finalStore (.val finalValue) →
    ∃ midStore value,
      MultiStep store blockLifetime term midStore (.val value) ∧
      MultiStep midStore lifetime (.block blockLifetime (.val value :: rest))
        finalStore (.val finalValue) := by
  intro hmulti
  generalize hcurrentEq :
      (Term.block blockLifetime (term :: rest)) = current at hmulti
  generalize htargetEq : (Term.val finalValue) = target at hmulti
  induction hmulti generalizing term rest finalValue with
  | refl =>
      cases hcurrentEq
      cases htargetEq
  | trans hstep htail ih =>
      cases hcurrentEq
      cases htargetEq
      cases hstep with
      | seq hdrops =>
          exact ⟨_, _, MultiStep.refl,
            MultiStep.trans (Step.seq hdrops) htail⟩
      | blockA hhead =>
          rcases ih rfl rfl with ⟨midStore, value, hheadTail, hblockTail⟩
          exact ⟨midStore, value, MultiStep.trans hhead hheadTail, hblockTail⟩
      | blockB hdrops =>
          exact ⟨_, _, MultiStep.refl,
            MultiStep.trans (Step.blockB hdrops) htail⟩

theorem multistep_eq_left_context {store finalStore : ProgramStore}
    {lifetime : Lifetime} {lhs finalLhs rhs : Term} :
    MultiStep store lifetime lhs finalStore finalLhs →
    MultiStep store lifetime (.eq lhs rhs) finalStore (.eq finalLhs rhs) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subEqLeft hstep) ih

theorem multistep_eq_right_context {store finalStore : ProgramStore}
    {lifetime : Lifetime} {value : Value} {rhs finalRhs : Term} :
    MultiStep store lifetime rhs finalStore finalRhs →
    MultiStep store lifetime (.eq (.val value) rhs) finalStore
      (.eq (.val value) finalRhs) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subEqRight hstep) ih

theorem multistep_ite_context {store finalStore : ProgramStore}
    {lifetime : Lifetime} {condition finalCondition trueBranch falseBranch : Term} :
    MultiStep store lifetime condition finalStore finalCondition →
    MultiStep store lifetime (.ite condition trueBranch falseBranch) finalStore
      (.ite finalCondition trueBranch falseBranch) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subIte hstep) ih

/--
Prefix inversion for equality runs: an arbitrary partial execution is still
inside the left operand, or the left operand finished and the run is still
inside the right operand, or both operands finished and the comparison redex
fired (after which the term is a value and the run is over).
-/
theorem multistep_eq_prefix_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {lhs rhs finalTerm : Term} :
    MultiStep store lifetime (.eq lhs rhs) finalStore finalTerm →
    (∃ lhs', finalTerm = .eq lhs' rhs ∧
      MultiStep store lifetime lhs finalStore lhs') ∨
    (∃ midStore leftValue,
      MultiStep store lifetime lhs midStore (.val leftValue) ∧
      ((∃ rhs', finalTerm = .eq (.val leftValue) rhs' ∧
          MultiStep midStore lifetime rhs finalStore rhs') ∨
       (∃ rightStore rightValue,
          MultiStep midStore lifetime rhs rightStore (.val rightValue) ∧
          Step rightStore lifetime (.eq (.val leftValue) (.val rightValue))
            finalStore finalTerm))) := by
  intro hmulti
  generalize hstart : Term.eq lhs rhs = start at hmulti
  induction hmulti generalizing lhs rhs with
  | refl =>
      cases hstart
      exact Or.inl ⟨lhs, rfl, MultiStep.refl⟩
  | trans hstep hrest ih =>
      cases hstart
      cases hstep with
      | eqTrue =>
          rcases multistep_value_inv hrest with ⟨hstoreEq, hterm⟩
          subst hstoreEq
          subst hterm
          exact Or.inr ⟨_, _, MultiStep.refl,
            Or.inr ⟨_, _, MultiStep.refl, Step.eqTrue⟩⟩
      | eqFalse hne =>
          rcases multistep_value_inv hrest with ⟨hstoreEq, hterm⟩
          subst hstoreEq
          subst hterm
          exact Or.inr ⟨_, _, MultiStep.refl,
            Or.inr ⟨_, _, MultiStep.refl, Step.eqFalse hne⟩⟩
      | subEqLeft hinner =>
          rcases ih rfl with ⟨lhs', hfinal, hms⟩ |
            ⟨midStore, leftValue, hleft, hcase⟩
          · exact Or.inl ⟨lhs', hfinal, MultiStep.trans hinner hms⟩
          · exact Or.inr ⟨midStore, leftValue,
              MultiStep.trans hinner hleft, hcase⟩
      | subEqRight hinner =>
          rcases ih rfl with ⟨lhs', hfinal, hms⟩ |
            ⟨midStore, leftValue, hleft, hcase⟩
          · -- The left operand is already a value, so the "still in the left
            -- operand" disjunct of the tail run collapses by value inversion.
            rcases multistep_value_inv hms with ⟨hstoreEq, hterm⟩
            subst hstoreEq
            subst hterm
            exact Or.inr ⟨_, _, MultiStep.refl,
              Or.inl ⟨_, hfinal, MultiStep.trans hinner MultiStep.refl⟩⟩
          · rcases multistep_value_inv hleft with ⟨hstoreEq, hterm⟩
            subst hstoreEq
            injection hterm with hvalueEq
            subst hvalueEq
            rcases hcase with ⟨rhs', hfinal, hms⟩ |
              ⟨rightStore, rightValue, hms, hredex⟩
            · exact Or.inr ⟨_, _, MultiStep.refl,
                Or.inl ⟨rhs', hfinal, MultiStep.trans hinner hms⟩⟩
            · exact Or.inr ⟨_, _, MultiStep.refl,
                Or.inr ⟨rightStore, rightValue,
                  MultiStep.trans hinner hms, hredex⟩⟩

/--
Prefix inversion for conditional runs: an arbitrary partial execution is
still inside the condition, or the condition finished with a Boolean and the
run continued inside the chosen branch.
-/
theorem multistep_ite_prefix_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {condition trueBranch falseBranch finalTerm : Term} :
    MultiStep store lifetime (.ite condition trueBranch falseBranch)
      finalStore finalTerm →
    (∃ condition', finalTerm = .ite condition' trueBranch falseBranch ∧
      MultiStep store lifetime condition finalStore condition') ∨
    (∃ midStore,
      MultiStep store lifetime condition midStore (.val (.bool true)) ∧
      MultiStep midStore lifetime trueBranch finalStore finalTerm) ∨
    (∃ midStore,
      MultiStep store lifetime condition midStore (.val (.bool false)) ∧
      MultiStep midStore lifetime falseBranch finalStore finalTerm) := by
  intro hmulti
  generalize hstart : Term.ite condition trueBranch falseBranch = start at hmulti
  induction hmulti generalizing condition with
  | refl =>
      cases hstart
      exact Or.inl ⟨condition, rfl, MultiStep.refl⟩
  | trans hstep hrest ih =>
      cases hstart
      cases hstep with
      | iteTrue =>
          exact Or.inr (Or.inl ⟨_, MultiStep.refl, hrest⟩)
      | iteFalse =>
          exact Or.inr (Or.inr ⟨_, MultiStep.refl, hrest⟩)
      | subIte hinner =>
          rcases ih rfl with ⟨condition', hfinal, hms⟩ |
            ⟨midStore, hcond, hbranch⟩ | ⟨midStore, hcond, hbranch⟩
          · exact Or.inl ⟨condition', hfinal, MultiStep.trans hinner hms⟩
          · exact Or.inr (Or.inl ⟨midStore, MultiStep.trans hinner hcond, hbranch⟩)
          · exact Or.inr (Or.inr ⟨midStore, MultiStep.trans hinner hcond, hbranch⟩)

/--
Operational decomposition of a complete equality run: both operands reach
values, then the comparison redex fires.
-/
theorem multistep_eq_to_value_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {lhs rhs : Term} {finalValue : Value} :
    MultiStep store lifetime (.eq lhs rhs) finalStore (.val finalValue) →
    ∃ midStore leftValue rightStore rightValue,
      MultiStep store lifetime lhs midStore (.val leftValue) ∧
      MultiStep midStore lifetime rhs rightStore (.val rightValue) ∧
      Step rightStore lifetime (.eq (.val leftValue) (.val rightValue))
        finalStore (.val finalValue) := by
  intro hmulti
  rcases multistep_eq_prefix_inv hmulti with
    ⟨lhs', hfinal, _⟩ | ⟨midStore, leftValue, hleft, hcase⟩
  · simp at hfinal
  · rcases hcase with ⟨rhs', hfinal, _⟩ |
      ⟨rightStore, rightValue, hright, hredex⟩
    · simp at hfinal
    · exact ⟨midStore, leftValue, rightStore, rightValue, hleft, hright, hredex⟩

/--
Operational decomposition of a complete conditional run: the condition
reaches a Boolean, then the chosen branch runs to the final value.
-/
theorem multistep_ite_to_value_inv {store finalStore : ProgramStore}
    {lifetime : Lifetime} {condition trueBranch falseBranch : Term}
    {finalValue : Value} :
    MultiStep store lifetime (.ite condition trueBranch falseBranch)
      finalStore (.val finalValue) →
    ∃ midStore,
      (MultiStep store lifetime condition midStore (.val (.bool true)) ∧
        MultiStep midStore lifetime trueBranch finalStore (.val finalValue)) ∨
      (MultiStep store lifetime condition midStore (.val (.bool false)) ∧
        MultiStep midStore lifetime falseBranch finalStore (.val finalValue)) := by
  intro hmulti
  rcases multistep_ite_prefix_inv hmulti with
    ⟨condition', hfinal, _⟩ | ⟨midStore, hcond, hbranch⟩ |
    ⟨midStore, hcond, hbranch⟩
  · simp at hfinal
  · exact ⟨midStore, Or.inl ⟨hcond, hbranch⟩⟩
  · exact ⟨midStore, Or.inr ⟨hcond, hbranch⟩⟩

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

end InvalidEscapingBorrowExample

end Paper
end LwRust
