import LwRust.Paper.InductiveSemantics

/-!
Store and environment abstraction predicates used by the paper proof.
-/

namespace LwRust
namespace Paper

open Core

def ownerRefsInReference (ref : Reference) : List Reference :=
  if ref.owner then [ref] else []

mutual
  def ownerRefsInValue : Value → List Reference
    | .unit => []
    | .int _ => []
    | .ref ref => ownerRefsInReference ref
    | .tuple fields => ownerRefsInValues fields
    | .moved => []

  def ownerRefsInValues : List Value → List Reference
    | [] => []
    | value :: values => ownerRefsInValue value ++ ownerRefsInValues values
end

mutual
  def ownerRefsInTerm : Term → List Reference
    | .val value => ownerRefsInValue value
    | .letMut _ initialiser => ownerRefsInTerm initialiser
    | .assign _ rhs => ownerRefsInTerm rhs
    | .block _ terms => ownerRefsInTerms terms
    | .access _ _ => []
    | .borrow _ _ => []
    | .box operand => ownerRefsInTerm operand
    | .tuple terms => ownerRefsInTerms terms
    | .ifElse _ lhs rhs trueBlock falseBlock =>
        ownerRefsInTerm lhs ++ ownerRefsInTerm rhs ++
          ownerRefsInTerm trueBlock ++ ownerRefsInTerm falseBlock
    | .invoke _ args => ownerRefsInTerms args

  def ownerRefsInTerms : List Term → List Reference
    | [] => []
    | term :: terms => ownerRefsInTerm term ++ ownerRefsInTerms terms
end

def ownerRefsInCell (cell : Cell) : List Reference :=
  match cell.value with
  | none => []
  | some value => ownerRefsInValue value

def ownerRefsInHeap : List (Nat × Cell) → List Reference
  | [] => []
  | (_, cell) :: rest => ownerRefsInCell cell ++ ownerRefsInHeap rest

def ownerRefsInState (state : State) : List Reference :=
  (state.vars.map Prod.snd).filter (fun ref => ref.owner) ++ ownerRefsInHeap state.heap

def PairwiseDisjoint [BEq α] (values : List α) : Prop :=
  ∀ a, values.countP (fun b => b == a) ≤ 1

structure StoreTyping where
  tyOf : Nat → Option Ty

mutual
  inductive ValueAbstracts (state : State) : Value → Ty → Prop where
    | unit : ValueAbstracts state .unit Ty.unit
    | int (n : Int) : ValueAbstracts state (.int n) Ty.int
    | tuple {values : List Value} {tys : List Ty} :
        ValuesAbstract state values tys →
        ValueAbstracts state (.tuple values) (.tuple tys)
    | box {ref : Reference} {cell : Cell} {ty : Ty} :
        ref.owner = true →
        state.getCell ref.address = some cell →
        PartialValueAbstracts state cell.value ty →
        ValueAbstracts state (.ref ref) (.box ty)
    | borrow {ref : Reference} {mutable : Bool} {lvals : List LVal} {lv : LVal} :
        ref.owner = false →
        lv ∈ lvals →
        OperationalSemantics.locate state lv = .ok ref →
        ValueAbstracts state (.ref ref) (.borrow mutable lvals)

  inductive ValuesAbstract (state : State) : List Value → List Ty → Prop where
    | nil : ValuesAbstract state [] []
    | cons {value : Value} {values : List Value} {ty : Ty} {tys : List Ty} :
        ValueAbstracts state value ty →
        ValuesAbstract state values tys →
        ValuesAbstract state (value :: values) (ty :: tys)

  inductive PartialValueAbstracts (state : State) : Option Value → Ty → Prop where
    | none {ty : Ty} :
        PartialValueAbstracts state none (.undef ty)
    | moved {ty : Ty} :
        PartialValueAbstracts state (some .moved) (.undef ty)
    | some {value : Value} {ty : Ty} :
        ValueAbstracts state value ty →
        PartialValueAbstracts state (some value) ty
end

def ValidTerm (term : Term) : Prop :=
  PairwiseDisjoint (ownerRefsInTerm term)

def ValidState (state : State) (term : Term) : Prop :=
  PairwiseDisjoint (ownerRefsInState state ++ ownerRefsInTerm term)

def StoreAbstractsCell (state : State) (storeTyping : StoreTyping) (entry : Nat × Cell) : Prop :=
  ∀ ty, storeTyping.tyOf entry.fst = some ty → PartialValueAbstracts state entry.snd.value ty

-- TODO: This captures Definition 4.4 for heap cells locally, but does not yet
-- account for the paper's full store typing over all distinct values occurring
-- in the term and store.
def StoreAbstracts (state : State) (_term : Term) (storeTyping : StoreTyping) : Prop :=
  ∀ entry, entry ∈ state.heap → StoreAbstractsCell state storeTyping entry

def WellFormedEnv (_state : State) (env : Env) (lifetime : Lifetime) : Prop :=
  ∀ entry,
    entry ∈ env →
    lifetime.contains entry.snd.lifetime ∧
      BorrowChecker.Ty.refsWithin env entry.snd.lifetime entry.snd.ty = .ok true

def EnvAbstracts (state : State) (env : Env) : Prop :=
  ∀ x slot,
    Env.get env x = some slot →
    ∃ ref cell,
      state.getVar x = some ref ∧
      state.getCell ref.address = some cell ∧
      cell.lifetime = slot.lifetime ∧
      PartialValueAbstracts state cell.value slot.ty

theorem value_typing {env env' : Env} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    Checks env lifetime (.val value) env' ty →
    env' = env := by
  intro h
  cases h <;> rfl

theorem location {state : State} {env : Env} {lv : LVal} {ty : Ty}
    {ambientLifetime targetLifetime : Lifetime} :
    EnvAbstracts state env →
    WellFormedEnv state env ambientLifetime →
    BorrowChecker.typeOf env lv = .ok (ty, targetLifetime) →
    ∃ ref cell,
      OperationalSemantics.locate state lv = .ok ref ∧
      state.getCell ref.address = some cell ∧
      PartialValueAbstracts state cell.value ty := by
  -- TODO: Port paper Lemma 9.3.  The proof follows the structure of
  -- `BorrowChecker.typeOf` and `OperationalSemantics.locate`, using
  -- `EnvAbstracts` for variables and `ValueAbstracts.borrow` for dereferences.
  sorry

theorem read_preservation {state : State} {env : Env} {lv : LVal} {ty : Ty}
    {ambientLifetime targetLifetime : Lifetime} :
    EnvAbstracts state env →
    WellFormedEnv state env ambientLifetime →
    BorrowChecker.typeOf env lv = .ok (ty, targetLifetime) →
    BorrowChecker.Ty.defined ty = true →
    ∃ value,
      state.readLVal lv = .ok value ∧
      ValueAbstracts state value ty := by
  -- TODO: Port paper Corollary 9.4 from `location`; the `defined` premise rules
  -- out `none` and `moved` partial values.
  sorry

end Paper
end LwRust
