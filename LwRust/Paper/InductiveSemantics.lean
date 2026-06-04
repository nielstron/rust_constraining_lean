import LwRust.Core.BorrowChecker
import LwRust.Core.OperationalSemantics

/-!
Inductive presentation of the executable core semantics and checker.

The constructors mirror `Core.OperationalSemantics.eval` and
`Core.BorrowChecker.checkTerm`.  These relations are used by the paper proof
statements; adequacy back to the executable functions is stated separately in
`LwRust.Paper.Adequacy`.
-/

namespace LwRust
namespace Paper

open Core

abbrev State := OperationalSemantics.State
abbrev Cell := OperationalSemantics.Cell

mutual
  inductive ValueHasType : Value → Ty → Prop where
    | unit : ValueHasType .unit Ty.unit
    | int (n : Int) : ValueHasType (.int n) Ty.int
    | tuple {values : List Value} {tys : List Ty} :
        ValuesHaveTypes values tys →
        ValueHasType (.tuple values) (.tuple tys)

    -- TODO: This context-free fallback is only for the executable `execute`
    -- theorem, which discards the final store.  The paper preservation theorem
    -- below uses `ValueAbstracts`, which is store-aware.
    | ref {r : Reference} :
        ValueHasType (.ref r) (.borrow false [])

    -- TODO: Moved values should only appear inside the store; connecting this to
    -- `Ty.undef` requires the executable store typing invariant.
    | moved {ty : Ty} :
        ValueHasType .moved (.undef ty)

  inductive ValuesHaveTypes : List Value → List Ty → Prop where
    | nil : ValuesHaveTypes [] []
    | cons {value : Value} {values : List Value} {ty : Ty} {tys : List Ty} :
        ValueHasType value ty →
        ValuesHaveTypes values tys →
        ValuesHaveTypes (value :: values) (ty :: tys)
end

mutual
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
        OperationalSemantics.locate state lv = .ok ref →
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

  inductive EvaluatesTerms : State → Lifetime → List Term → State → List Value → Prop where
    | nil {state : State} {lifetime : Lifetime} :
        EvaluatesTerms state lifetime [] state []
    | cons {state state₁ state₂ : State} {lifetime : Lifetime} {term : Term} {terms : List Term}
        {value : Value} {values : List Value} :
        Evaluates state lifetime term state₁ value →
        EvaluatesTerms state₁ lifetime terms state₂ values →
        EvaluatesTerms state lifetime (term :: terms) state₂ (value :: values)
end

mutual
  inductive Checks : Env → Lifetime → Term → Env → Ty → Prop where
    | unit {env : Env} {lifetime : Lifetime} :
        Checks env lifetime (.val .unit) env Ty.unit
    | int {env : Env} {lifetime : Lifetime} (n : Int) :
        Checks env lifetime (.val (.int n)) env Ty.int
    | runtimeTuple {env : Env} {lifetime : Lifetime} {fields : List Value} :
        Checks env lifetime (.val (.tuple fields)) env (Ty.tuple (fields.map (fun _ => Ty.unit)))
    | accessCopy {env : Env} {lifetime : Lifetime} {lv : LVal} {ty : Ty} {targetLifetime : Lifetime} :
        BorrowChecker.typeOf env lv = .ok (ty, targetLifetime) →
        BorrowChecker.Ty.defined ty = true →
        BorrowChecker.Ty.copyable ty = true →
        BorrowChecker.readProhibited env lv = false →
        Checks env lifetime (.access .copy lv) env ty
    | accessTemp {env : Env} {lifetime : Lifetime} {lv : LVal} {ty : Ty} {targetLifetime : Lifetime} :
        BorrowChecker.typeOf env lv = .ok (ty, targetLifetime) →
        BorrowChecker.Ty.defined ty = true →
        BorrowChecker.readProhibited env lv = false →
        Checks env lifetime (.access .temp lv) env ty
    | accessMove {env env' : Env} {lifetime : Lifetime} {lv : LVal} {ty : Ty}
        {targetLifetime : Lifetime} :
        BorrowChecker.typeOf env lv = .ok (ty, targetLifetime) →
        BorrowChecker.Ty.defined ty = true →
        BorrowChecker.writeProhibited env lv = false →
        BorrowChecker.move env lv = .ok env' →
        Checks env lifetime (.access .move lv) env' ty
    | borrowImm {env : Env} {lifetime targetLifetime : Lifetime} {lv : LVal} {ty : Ty} :
        BorrowChecker.typeOf env lv = .ok (ty, targetLifetime) →
        BorrowChecker.Ty.defined ty = true →
        BorrowChecker.readProhibited env lv = false →
        Checks env lifetime (.borrow false lv) env (.borrow false [lv])
    | borrowMut {env : Env} {lifetime targetLifetime : Lifetime} {lv : LVal} {ty : Ty} :
        BorrowChecker.typeOf env lv = .ok (ty, targetLifetime) →
        BorrowChecker.Ty.defined ty = true →
        BorrowChecker.writeProhibited env lv = false →
        BorrowChecker.mutLVal env lv = .ok true →
        Checks env lifetime (.borrow true lv) env (.borrow true [lv])
    | box {env env' : Env} {lifetime : Lifetime} {term : Term} {ty : Ty} :
        Checks env lifetime term env' ty →
        Checks env lifetime (.box term) env' (.box ty)
    | letMut {env env' : Env} {lifetime : Lifetime} {x : Name} {initialiser : Term}
        {ty : Ty} :
        Env.get env x = none →
        Checks env lifetime initialiser env' ty →
        Checks env lifetime (.letMut x initialiser)
          (Env.put env' x { ty := ty, lifetime := lifetime }) Ty.unit
    | assign {env env₁ env₂ : Env} {lifetime targetLifetime : Lifetime} {lhs : LVal}
        {rhs : Term} {lhsTy rhsTy : Ty} :
        BorrowChecker.typeOf env lhs = .ok (lhsTy, targetLifetime) →
        Checks env lifetime rhs env₁ rhsTy →
        BorrowChecker.compatible env₁ lhsTy rhsTy = .ok true →
        BorrowChecker.Ty.within env₁ targetLifetime rhsTy = .ok true →
        BorrowChecker.write env₁ lhs rhsTy true = .ok env₂ →
        BorrowChecker.writeProhibited env₂ lhs = false →
        Checks env lifetime (.assign lhs rhs) env₂ Ty.unit
    | block {env env' : Env} {lifetime blockLifetime : Lifetime} {terms : List Term}
        {ty : Ty} :
        ChecksSeq env blockLifetime terms env' ty →
        BorrowChecker.Ty.within env' lifetime ty = .ok true →
        BorrowChecker.scopedAfterDrop env' blockLifetime = .ok true →
        Checks env lifetime (.block blockLifetime terms) (Env.dropLifetime env' blockLifetime) ty
    | tuple {env env' : Env} {lifetime : Lifetime} {terms : List Term} {tys : List Ty}
        {temps : List Name} :
        ChecksTerms env lifetime terms 0 env' tys temps →
        Checks env lifetime (.tuple terms) (Env.removeMany env' temps) (.tuple tys)
    | ifElse {env env₁ env₂ env₃ trueEnv falseEnv joinedEnv : Env} {lifetime : Lifetime}
        {eq : Bool} {lhs rhs trueBlock falseBlock : Term} {lhsTy rhsTy trueTy falseTy resultTy : Ty} :
        (fresh : Name) →
        fresh = "?" ++ toString env.length →
        Checks env lifetime lhs env₁ lhsTy →
        Checks (Env.put env₁ fresh { ty := lhsTy, lifetime := Lifetime.root }) lifetime rhs env₂ rhsTy →
        env₃ = Env.erase env₂ fresh →
        BorrowChecker.compatible env₃ lhsTy rhsTy = .ok true →
        BorrowChecker.Ty.copyable lhsTy = true →
        BorrowChecker.Ty.copyable rhsTy = true →
        Checks env₃ lifetime trueBlock trueEnv trueTy →
        Checks env₃ lifetime falseBlock falseEnv falseTy →
        BorrowChecker.joinEnv trueEnv falseEnv = .ok joinedEnv →
        BorrowChecker.compatible joinedEnv trueTy falseTy = .ok true →
        BorrowChecker.Ty.union trueTy falseTy = .ok resultTy →
        Checks env lifetime (.ifElse eq lhs rhs trueBlock falseBlock) joinedEnv resultTy

  inductive ChecksSeq : Env → Lifetime → List Term → Env → Ty → Prop where
    | nil {env : Env} {lifetime : Lifetime} :
        ChecksSeq env lifetime [] env Ty.unit
    | single {env env' : Env} {lifetime : Lifetime} {term : Term} {ty : Ty} :
        Checks env lifetime term env' ty →
        ChecksSeq env lifetime [term] env' ty
    | cons {env env₁ env₂ : Env} {lifetime : Lifetime} {term next : Term}
        {rest : List Term} {termTy resultTy : Ty} :
        Checks env lifetime term env₁ termTy →
        ChecksSeq env₁ lifetime (next :: rest) env₂ resultTy →
        ChecksSeq env lifetime (term :: next :: rest) env₂ resultTy

  inductive ChecksTerms :
      Env → Lifetime → List Term → Nat → Env → List Ty → List Name → Prop where
    | nil {env : Env} {lifetime : Lifetime} {n : Nat} :
        ChecksTerms env lifetime [] n env [] []
    | cons {env env₁ env₂ env₃ : Env} {lifetime : Lifetime} {term : Term}
        {terms : List Term} {n : Nat} {ty : Ty} {tys : List Ty} {names : List Name} :
        Checks env lifetime term env₁ ty →
        env₂ = Env.put env₁ ("?" ++ toString n) { ty := ty, lifetime := Lifetime.root } →
        ChecksTerms env₂ lifetime terms (n + 1) env₃ tys names →
        ChecksTerms env lifetime (term :: terms) n env₃ (ty :: tys) (("?" ++ toString n) :: names)
end

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
      OperationalSemantics.locate state lv = .ok ref →
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
  | tupleValues {state : State} {lifetime : Lifetime} {values : List Value} :
      Step state lifetime (.tuple (values.map Term.val)) state (.val (.tuple values))
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

inductive MultiStep : State → Lifetime → Term → State → Term → Prop where
  | refl {state : State} {lifetime : Lifetime} {term : Term} :
      MultiStep state lifetime term state term
  | trans {state₁ state₂ state₃ : State} {lifetime : Lifetime} {term₁ term₂ term₃ : Term} :
      Step state₁ lifetime term₁ state₂ term₂ →
      MultiStep state₂ lifetime term₂ state₃ term₃ →
      MultiStep state₁ lifetime term₁ state₃ term₃

def Terminal : Term → Prop
  | .val _ => True
  | _ => False

end Paper
end LwRust
