import LwRust.Paper.Runtime

/-!
Inductive presentation of the paper operational semantics.
-/

namespace LwRust
namespace Paper

open Core

mutual
  /--
  Paper Section 3 big-step evaluation relation.
  -/
  inductive Evaluates : State → Lifetime → Term → State → Value → Prop where
    | val {state : State} {lifetime : Lifetime} {value : Value} :
        Evaluates state lifetime (.val value) state value
    | copy {state : State} {lifetime : Lifetime} {lv : LVal} {value : Value} :
        state.readLVal lv = .ok value →
        Evaluates state lifetime (.access .copy lv) state value
    | temp {state : State} {lifetime : Lifetime} {lv : LVal} {value : Value} :
        state.readLVal lv = .ok value →
        Evaluates state lifetime (.access .temp lv) state value
    | move {state state' : State} {lifetime : Lifetime} {lv : LVal} {value : Value} :
        state.readLVal lv = .ok value →
        state.writeLVal lv none = .ok state' →
        Evaluates state lifetime (.access .move lv) state' value
    | borrow {state : State} {lifetime : Lifetime} {mutable : Bool} {lv : LVal} {ref : Reference} :
        locate state lv = .ok ref →
        Evaluates state lifetime (.borrow mutable lv) state (.ref ref.borrowed)
    | box {state state₁ state₂ : State} {lifetime : Lifetime} {term : Term}
        {value : Value} {ref : Reference} :
        Evaluates state lifetime term state₁ value →
        state₁.allocate Lifetime.root value = (state₂, ref) →
        Evaluates state lifetime (.box term) state₂ (.ref ref)
    | letMut {state state₁ state₂ : State} {lifetime : Lifetime} {x : Name}
        {initialiser : Term} {value : Value} {ref : Reference} :
        Evaluates state lifetime initialiser state₁ value →
        state₁.allocate lifetime value = (state₂, ref) →
        Evaluates state lifetime (.letMut x initialiser) (state₂.putVar x ref) .unit
    | assign {state state₁ state₂ : State} {lifetime : Lifetime} {lhs : LVal} {rhs : Term}
        {value : Value} :
        Evaluates state lifetime rhs state₁ value →
        state₁.writeLVal lhs (some value) = .ok state₂ →
        Evaluates state lifetime (.assign lhs rhs) state₂ .unit
    | block {state state₁ : State} {lifetime blockLifetime : Lifetime} {terms : List Term}
        {value : Value} :
        EvaluatesSeq state blockLifetime terms state₁ value →
        Evaluates state lifetime (.block blockLifetime terms) (state₁.dropLifetime blockLifetime) value
    | tuple {state state' : State} {lifetime : Lifetime} {terms : List Term}
        {values : List Value} :
        EvaluatesTerms state lifetime terms state' values →
        Evaluates state lifetime (.tuple terms) state' (.tuple values)
    | ifTrue {state state₁ state₂ state' : State} {lifetime : Lifetime} {eq : Bool}
        {lhs rhs trueBlock falseBlock : Term} {lhsValue rhsValue value : Value} :
        Evaluates state lifetime lhs state₁ lhsValue →
        Evaluates state₁ lifetime rhs state₂ rhsValue →
        (lhsValue == rhsValue) = eq →
        Evaluates state₂ lifetime trueBlock state' value →
        Evaluates state lifetime (.ifElse eq lhs rhs trueBlock falseBlock) state' value
    | ifFalse {state state₁ state₂ state' : State} {lifetime : Lifetime} {eq : Bool}
        {lhs rhs trueBlock falseBlock : Term} {lhsValue rhsValue value : Value} :
        Evaluates state lifetime lhs state₁ lhsValue →
        Evaluates state₁ lifetime rhs state₂ rhsValue →
        (lhsValue == rhsValue) ≠ eq →
        Evaluates state₂ lifetime falseBlock state' value →
        Evaluates state lifetime (.ifElse eq lhs rhs trueBlock falseBlock) state' value

  /--
  Paper Section 3 big-step evaluation relation for statement/block sequences.
  -/
  inductive EvaluatesSeq : State → Lifetime → List Term → State → Value → Prop where
    | nil {state : State} {lifetime : Lifetime} :
        EvaluatesSeq state lifetime [] state .unit
    | single {state state' : State} {lifetime : Lifetime} {term : Term}
        {value : Value} :
        Evaluates state lifetime term state' value →
        EvaluatesSeq state lifetime [term] state' value
    | cons {state state₁ state₂ : State} {lifetime : Lifetime} {term next : Term}
        {rest : List Term} {ignored value : Value} :
        Evaluates state lifetime term state₁ ignored →
        EvaluatesSeq state₁ lifetime (next :: rest) state₂ value →
        EvaluatesSeq state lifetime (term :: next :: rest) state₂ value

  /--
  Paper Section 3 big-step evaluation relation for tuple argument lists.
  -/
  inductive EvaluatesTerms : State → Lifetime → List Term → State → List Value → Prop where
    | nil {state : State} {lifetime : Lifetime} :
        EvaluatesTerms state lifetime [] state []
    | cons {state state₁ state₂ : State} {lifetime : Lifetime} {term : Term} {terms : List Term}
        {value : Value} {values : List Value} :
        Evaluates state lifetime term state₁ value →
        EvaluatesTerms state₁ lifetime terms state₂ values →
        EvaluatesTerms state lifetime (term :: terms) state₂ (value :: values)
end

/--
Paper Section 3 operational reduction relation, with evaluation contexts from
Paper Definition 3.5 represented directly as congruence constructors.
-/
inductive Step : State → Lifetime → Term → State → Term → Prop where
  | copy {state : State} {lifetime : Lifetime} {lv : LVal} {value : Value} :
      state.readLVal lv = .ok value →
      Step state lifetime (.access .copy lv) state (.val value)
  | temp {state : State} {lifetime : Lifetime} {lv : LVal} {value : Value} :
      state.readLVal lv = .ok value →
      Step state lifetime (.access .temp lv) state (.val value)
  | move {state state' : State} {lifetime : Lifetime} {lv : LVal} {value : Value} :
      state.readLVal lv = .ok value →
      state.writeLVal lv none = .ok state' →
      Step state lifetime (.access .move lv) state' (.val value)
  | borrow {state : State} {lifetime : Lifetime} {mutable : Bool} {lv : LVal} {ref : Reference} :
      locate state lv = .ok ref →
      Step state lifetime (.borrow mutable lv) state (.val (.ref ref.borrowed))
  | boxValue {state state' : State} {lifetime : Lifetime} {value : Value}
      {ref : Reference} :
      state.allocate Lifetime.root value = (state', ref) →
      Step state lifetime (.box (.val value)) state' (.val (.ref ref))
  | letMutValue {state state' : State} {lifetime : Lifetime} {x : Name}
      {value : Value} {ref : Reference} :
      state.allocate lifetime value = (state', ref) →
      Step state lifetime (.letMut x (.val value)) (state'.putVar x ref) (.val .unit)
  | assignValue {state state' : State} {lifetime : Lifetime} {lhs : LVal}
      {value : Value} :
      state.writeLVal lhs (some value) = .ok state' →
      Step state lifetime (.assign lhs (.val value)) state' (.val .unit)
  | blockNil {state : State} {lifetime blockLifetime : Lifetime} :
      Step state lifetime (.block blockLifetime []) (state.dropLifetime blockLifetime) (.val .unit)
  | blockValue {state : State} {lifetime blockLifetime : Lifetime} {value : Value} :
      Step state lifetime (.block blockLifetime [.val value])
        (state.dropLifetime blockLifetime) (.val value)
  | blockSingleSub {state state' : State} {lifetime blockLifetime : Lifetime}
      {term term' : Term} :
      Step state blockLifetime term state' term' →
      Step state lifetime (.block blockLifetime [term])
        state' (.block blockLifetime [term'])
  | tupleValues {state : State} {lifetime : Lifetime} {values : List Value} :
      Step state lifetime (.tuple (values.map Term.val)) state (.val (.tuple values))
  | tupleHeadSub {state state' : State} {lifetime : Lifetime}
      {term term' : Term} {rest : List Term} :
      Step state lifetime term state' term' →
      Step state lifetime (.tuple (term :: rest)) state' (.tuple (term' :: rest))
  | tupleTailSub {state state' : State} {lifetime : Lifetime}
      {value : Value} {next : Term} {rest terms' : List Term} :
      Step state lifetime (.tuple (next :: rest)) state' (.tuple terms') →
      Step state lifetime (.tuple (.val value :: next :: rest))
        state' (.tuple (.val value :: terms'))
  | ifTrue {state : State} {lifetime : Lifetime} {eq : Bool}
      {lhsValue rhsValue : Value} {trueBlock falseBlock : Term} :
      (lhsValue == rhsValue) = eq →
      Step state lifetime (.ifElse eq (.val lhsValue) (.val rhsValue) trueBlock falseBlock)
        state trueBlock
  | ifFalse {state : State} {lifetime : Lifetime} {eq : Bool}
      {lhsValue rhsValue : Value} {trueBlock falseBlock : Term} :
      (lhsValue == rhsValue) ≠ eq →
      Step state lifetime (.ifElse eq (.val lhsValue) (.val rhsValue) trueBlock falseBlock)
        state falseBlock
  | ifLhsSub {state state' : State} {lifetime : Lifetime} {eq : Bool}
      {lhs lhs' rhs trueBlock falseBlock : Term} :
      Step state lifetime lhs state' lhs' →
      Step state lifetime (.ifElse eq lhs rhs trueBlock falseBlock)
        state' (.ifElse eq lhs' rhs trueBlock falseBlock)
  | ifRhsSub {state state' : State} {lifetime : Lifetime} {eq : Bool}
      {lhsValue : Value} {rhs rhs' trueBlock falseBlock : Term} :
      Step state lifetime rhs state' rhs' →
      Step state lifetime (.ifElse eq (.val lhsValue) rhs trueBlock falseBlock)
        state' (.ifElse eq (.val lhsValue) rhs' trueBlock falseBlock)
  | boxSub {state state' : State} {lifetime : Lifetime} {term term' : Term} :
      Step state lifetime term state' term' →
      Step state lifetime (.box term) state' (.box term')
  | letMutSub {state state' : State} {lifetime : Lifetime} {x : Name} {term term' : Term} :
      Step state lifetime term state' term' →
      Step state lifetime (.letMut x term) state' (.letMut x term')
  | assignSub {state state' : State} {lifetime : Lifetime} {lhs : LVal} {rhs rhs' : Term} :
      Step state lifetime rhs state' rhs' →
      Step state lifetime (.assign lhs rhs) state' (.assign lhs rhs')
  | blockHeadSub {state state' : State} {lifetime blockLifetime : Lifetime}
      {term term' next : Term} {rest : List Term} :
      Step state blockLifetime term state' term' →
      Step state lifetime (.block blockLifetime (term :: next :: rest))
        state' (.block blockLifetime (term' :: next :: rest))
  | blockHeadValue {state : State} {lifetime blockLifetime : Lifetime}
      {value : Value} {next : Term} {rest : List Term} :
      Step state lifetime (.block blockLifetime (.val value :: next :: rest))
        state (.block blockLifetime (next :: rest))

/--
Paper Lemma 4.11 uses the reflexive-transitive closure of the reduction
relation; this is that multi-step relation.
-/
inductive MultiStep : State → Lifetime → Term → State → Term → Prop where
  | refl {state : State} {lifetime : Lifetime} {term : Term} :
      MultiStep state lifetime term state term
  | trans {state₁ state₂ state₃ : State} {lifetime : Lifetime} {term₁ term₂ term₃ : Term} :
      Step state₁ lifetime term₁ state₂ term₂ →
      MultiStep state₂ lifetime term₂ state₃ term₃ →
      MultiStep state₁ lifetime term₁ state₃ term₃

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

theorem value_no_step {state state' : State} {lifetime : Lifetime}
    {value : Value} {term' : Term} :
    ¬ Step state lifetime (.val value) state' term' := by
  intro h
  cases h

theorem terminal_no_step {state state' : State} {lifetime : Lifetime}
    {term term' : Term} :
    Terminal term →
    ¬ Step state lifetime term state' term' := by
  intro hterminal hstep
  rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
  subst hterm
  exact value_no_step hstep

theorem multistep_value_inv {state finalState : State} {lifetime : Lifetime}
    {value : Value} {term : Term} :
    MultiStep state lifetime (.val value) finalState term →
    finalState = state ∧ term = .val value := by
  intro h
  cases h with
  | refl =>
      exact ⟨rfl, rfl⟩
  | trans hstep _ =>
      exact False.elim (value_no_step hstep)

theorem multistep_terminal_inv {state finalState : State} {lifetime : Lifetime}
    {term finalTerm : Term} :
    Terminal term →
    MultiStep state lifetime term finalState finalTerm →
    finalState = state ∧ finalTerm = term := by
  intro hterminal hmulti
  cases hmulti with
  | refl =>
      exact ⟨rfl, rfl⟩
  | trans hstep _ =>
      exact False.elim (terminal_no_step hterminal hstep)

theorem multistep_append {state₁ state₂ state₃ : State} {lifetime : Lifetime}
    {term₁ term₂ term₃ : Term} :
    MultiStep state₁ lifetime term₁ state₂ term₂ →
    MultiStep state₂ lifetime term₂ state₃ term₃ →
    MultiStep state₁ lifetime term₁ state₃ term₃ := by
  intro hleft hright
  induction hleft with
  | refl =>
      exact hright
  | trans hstep _ ih =>
      exact MultiStep.trans hstep (ih hright)

theorem step_multistep {state state' : State} {lifetime : Lifetime}
    {term term' : Term} :
    Step state lifetime term state' term' →
    MultiStep state lifetime term state' term' := by
  intro hstep
  exact MultiStep.trans hstep MultiStep.refl

theorem multistep_box_context {state finalState : State} {lifetime : Lifetime}
    {term finalTerm : Term} :
    MultiStep state lifetime term finalState finalTerm →
    MultiStep state lifetime (.box term) finalState (.box finalTerm) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.boxSub hstep) ih

theorem multistep_let_mut_context {state finalState : State} {lifetime : Lifetime}
    {x : Name} {term finalTerm : Term} :
    MultiStep state lifetime term finalState finalTerm →
    MultiStep state lifetime (.letMut x term) finalState (.letMut x finalTerm) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.letMutSub hstep) ih

theorem multistep_assign_context {state finalState : State} {lifetime : Lifetime}
    {lhs : LVal} {rhs finalRhs : Term} :
    MultiStep state lifetime rhs finalState finalRhs →
    MultiStep state lifetime (.assign lhs rhs) finalState (.assign lhs finalRhs) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.assignSub hstep) ih

theorem multistep_if_lhs_context {state finalState : State} {lifetime : Lifetime}
    {eq : Bool} {lhs finalLhs rhs trueBlock falseBlock : Term} :
    MultiStep state lifetime lhs finalState finalLhs →
    MultiStep state lifetime (.ifElse eq lhs rhs trueBlock falseBlock)
      finalState (.ifElse eq finalLhs rhs trueBlock falseBlock) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.ifLhsSub hstep) ih

theorem multistep_if_rhs_context {state finalState : State} {lifetime : Lifetime}
    {eq : Bool} {lhsValue : Value} {rhs finalRhs trueBlock falseBlock : Term} :
    MultiStep state lifetime rhs finalState finalRhs →
    MultiStep state lifetime (.ifElse eq (.val lhsValue) rhs trueBlock falseBlock)
      finalState (.ifElse eq (.val lhsValue) finalRhs trueBlock falseBlock) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.ifRhsSub hstep) ih

theorem multistep_tuple_head_context {state finalState : State} {lifetime : Lifetime}
    {term finalTerm : Term} {rest : List Term} :
    MultiStep state lifetime term finalState finalTerm →
    MultiStep state lifetime (.tuple (term :: rest))
      finalState (.tuple (finalTerm :: rest)) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.tupleHeadSub hstep) ih

theorem multistep_block_single_context {state finalState : State}
    {lifetime blockLifetime : Lifetime} {term finalTerm : Term} :
    MultiStep state blockLifetime term finalState finalTerm →
    MultiStep state lifetime (.block blockLifetime [term])
      finalState (.block blockLifetime [finalTerm]) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.blockSingleSub hstep) ih

theorem multistep_block_head_context {state finalState : State}
    {lifetime blockLifetime : Lifetime} {term finalTerm next : Term} {rest : List Term} :
    MultiStep state blockLifetime term finalState finalTerm →
    MultiStep state lifetime (.block blockLifetime (term :: next :: rest))
      finalState (.block blockLifetime (finalTerm :: next :: rest)) := by
  intro h
  induction h with
  | refl =>
      exact MultiStep.refl
  | trans hstep _ ih =>
      exact MultiStep.trans (Step.blockHeadSub hstep) ih

end Paper
end LwRust
