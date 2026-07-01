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
  /-- R-Missing: synthetic placeholder diverges when evaluated. -/
  | missing {store : ProgramStore} {lifetime : Lifetime} :
      Step store lifetime .missing store .missing

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

theorem multistep_missing_inv {store finalStore : ProgramStore} {lifetime : Lifetime}
    {term : Term} :
    MultiStep store lifetime .missing finalStore term →
    finalStore = store ∧ term = .missing := by
  intro hmulti
  generalize hstart : Term.missing = start at hmulti
  induction hmulti with
  | refl =>
      cases hstart
      exact ⟨rfl, rfl⟩
  | trans hstep _hrest ih =>
      cases hstart
      cases hstep
      exact ih rfl

theorem multistep_missing_not_value {store finalStore : ProgramStore}
    {lifetime : Lifetime} {value : Value} :
    ¬ MultiStep store lifetime .missing finalStore (.val value) := by
  intro hmulti
  exact Term.noConfusion (multistep_missing_inv hmulti).2

/-- Values do not diverge. -/
theorem _root_.LwRust.Core.Term.Diverges.no_value {value : Value} :
    ¬ Term.Diverges (.val value) := by
  intro hdiv
  cases hdiv

/-- Syntactic divergence is stable under reduction: the diverging member of a
block is never popped (it is not a value) and steps to a diverging term. -/
theorem _root_.LwRust.Core.Term.Diverges.step {store store' : ProgramStore} {lifetime : Lifetime}
    {term term' : Term} :
    Term.Diverges term →
    Step store lifetime term store' term' →
    Term.Diverges term' := by
  intro hdiv
  induction hdiv generalizing store store' lifetime term' with
  | missing =>
      intro hstep
      cases hstep
      exact .missing
  | block hmem hinner ih =>
      intro hstep
      cases hstep with
      | seq _hdrops =>
          rcases List.mem_cons.mp hmem with heq | hmem'
          · exact absurd (heq ▸ hinner) Term.Diverges.no_value
          · exact .block hmem' hinner
      | blockA hstepHead =>
          rcases List.mem_cons.mp hmem with heq | hmem'
          · subst heq
            exact .block List.mem_cons_self (ih hstepHead)
          · exact .block (List.mem_cons.mpr (Or.inr hmem')) hinner
      | blockB _hdrops =>
          rcases List.mem_singleton.mp hmem with heq
          exact absurd (heq ▸ hinner) Term.Diverges.no_value

/-- Syntactic divergence is stable under arbitrary execution. -/
theorem _root_.LwRust.Core.Term.Diverges.multiStep {store finalStore : ProgramStore}
    {lifetime : Lifetime} {term finalTerm : Term} :
    MultiStep store lifetime term finalStore finalTerm →
    Term.Diverges term →
    Term.Diverges finalTerm := by
  intro hmulti
  induction hmulti with
  | refl => exact id
  | trans hstep _hrest ih => exact fun hdiv => ih (hdiv.step hstep)

/-- A diverging term never reduces to a value.  This is what discharges the
dead-branch path of `T-IfDiv` in preservation: an execution that selects the
diverging branch never terminates, so terminal-state obligations are
vacuous. -/
theorem diverges_multistep_not_value {store finalStore : ProgramStore}
    {lifetime : Lifetime} {term : Term} {value : Value} :
    Term.Diverges term →
    ¬ MultiStep store lifetime term finalStore (.val value) :=
  fun hdiv hmulti => Term.Diverges.no_value (hdiv.multiStep hmulti)

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

theorem MultiStep.subBox {store store' : ProgramStore} {lifetime : Lifetime}
    {term term' : Term} :
    MultiStep store lifetime term store' term' →
    MultiStep store lifetime (.box term) store' (.box term') := by
  intro hmulti
  induction hmulti with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subBox hstep) ih

theorem MultiStep.subDeclare {store store' : ProgramStore} {lifetime : Lifetime}
    {x : Name} {term term' : Term} :
    MultiStep store lifetime term store' term' →
    MultiStep store lifetime (.letMut x term) store' (.letMut x term') := by
  intro hmulti
  induction hmulti with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subDeclare hstep) ih

theorem MultiStep.subAssign {store store' : ProgramStore} {lifetime : Lifetime}
    {lhs : LVal} {rhs rhs' : Term} :
    MultiStep store lifetime rhs store' rhs' →
    MultiStep store lifetime (.assign lhs rhs) store' (.assign lhs rhs') := by
  intro hmulti
  induction hmulti with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subAssign hstep) ih

theorem MultiStep.subEqLeft {store store' : ProgramStore} {lifetime : Lifetime}
    {lhs lhs' rhs : Term} :
    MultiStep store lifetime lhs store' lhs' →
    MultiStep store lifetime (.eq lhs rhs) store' (.eq lhs' rhs) := by
  intro hmulti
  induction hmulti with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subEqLeft hstep) ih

theorem MultiStep.subEqRight {store store' : ProgramStore} {lifetime : Lifetime}
    {value : Value} {rhs rhs' : Term} :
    MultiStep store lifetime rhs store' rhs' →
    MultiStep store lifetime (.eq (.val value) rhs) store' (.eq (.val value) rhs') := by
  intro hmulti
  induction hmulti with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subEqRight hstep) ih

theorem MultiStep.subIte {store store' : ProgramStore} {lifetime : Lifetime}
    {condition condition' trueBranch falseBranch : Term} :
    MultiStep store lifetime condition store' condition' →
    MultiStep store lifetime (.ite condition trueBranch falseBranch)
      store' (.ite condition' trueBranch falseBranch) := by
  intro hmulti
  induction hmulti with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.subIte hstep) ih

theorem MultiStep.blockHead {store store' : ProgramStore}
    {outerLifetime blockLifetime : Lifetime} {term term' : Term}
    {rest : List Term} :
    MultiStep store blockLifetime term store' term' →
    MultiStep store outerLifetime (.block blockLifetime (term :: rest))
      store' (.block blockLifetime (term' :: rest)) := by
  intro hmulti
  induction hmulti with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.blockA hstep) ih

theorem step_multistep {store store' : ProgramStore} {lifetime : Lifetime}
    {term term' : Term} :
    Step store lifetime term store' term' →
    MultiStep store lifetime term store' term' := by
  intro hstep
  exact MultiStep.trans hstep MultiStep.refl

theorem Term.MissingFree.step {store store' : ProgramStore}
    {lifetime : Lifetime} {term term' : Term} :
    term.MissingFree →
    Step store lifetime term store' term' →
    term'.MissingFree := by
  intro hfree hstep
  induction hstep with
  | missing =>
      exact False.elim hfree
  | copy _ | move _ _ | box _ _ | borrow _ | assign _ _ _ | declare _
    | eqTrue | eqFalse _ =>
      trivial
  | seq _hdrops =>
      exact hfree.2
  | blockA _ ih =>
      exact ⟨ih hfree.1, hfree.2⟩
  | blockB _hdrops =>
      trivial
  | subBox _ ih =>
      exact ih hfree
  | subDeclare _ ih =>
      exact ih hfree
  | subAssign _ ih =>
      exact ih hfree
  | iteTrue =>
      exact hfree.2.1
  | iteFalse =>
      exact hfree.2.2
  | subEqLeft _ ih =>
      exact ⟨ih hfree.1, hfree.2⟩
  | subEqRight _ ih =>
      exact ⟨trivial, ih hfree.2⟩
  | subIte _ ih =>
      exact ⟨ih hfree.1, hfree.2⟩

theorem step_size_lt {store store' : ProgramStore} {lifetime : Lifetime}
    {term term' : Term} :
    term.MissingFree →
    Step store lifetime term store' term' →
    term'.size < term.size := by
  intro hfree hstep
  induction hstep with
  | missing =>
      exact False.elim hfree
  | copy _ | move _ _ | box _ _ | borrow _ | assign _ _ _ | declare _
    | seq _ | blockB _ | eqTrue | eqFalse _ =>
      simp [Term.size, Term.sizeList]
  | iteTrue | iteFalse =>
      simp [Term.size]
      omega
  | blockA _ ih =>
      have hinner := ih hfree.1
      simp [Term.size, Term.sizeList]
      omega
  | subBox _ ih | subDeclare _ ih | subAssign _ ih =>
      have hinner := ih hfree
      simp [Term.size]
      omega
  | subEqLeft _ ih =>
      have hinner := ih hfree.1
      simp [Term.size]
      omega
  | subEqRight _ ih =>
      have hinner := ih hfree.2
      simp [Term.size]
      omega
  | subIte _ ih =>
      have hinner := ih hfree.1
      simp [Term.size]
      omega

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

end Paper
end LwRust
