import LwRust.Paper.Syntax

/-!
Inductive presentation of the paper borrow checker.
-/

namespace LwRust
namespace Paper

open Core

structure EnvSlot where
  ty : PartialTy
  lifetime : Lifetime
  deriving BEq, Repr

abbrev Slot := EnvSlot

abbrev Env := List (Name × EnvSlot)

namespace Env

def empty : Env := []

def get (env : Env) (x : Name) : Option EnvSlot :=
  match env with
  | [] => none
  | (y, s) :: rest => if x == y then some s else get rest x

def erase (env : Env) (x : Name) : Env :=
  env.filter (fun entry => entry.fst != x)

def put (env : Env) (x : Name) (slot : EnvSlot) : Env :=
  (x, slot) :: erase env x

def dropLifetime (env : Env) (lifetime : Lifetime) : Env :=
  env.filter (fun entry => entry.snd.lifetime != lifetime)

def names (env : Env) : List Name :=
  env.map Prod.fst

end Env

namespace BorrowChecker

/--
Paper checker relation for l-value typing.

TODO: The dereference-through-borrow constructor currently tracks one borrowed
target rather than the paper's full union/min-lifetime calculation.
-/
inductive TypeOf : Env → LVal → Ty → Lifetime → Prop where
  | var {env : Env} {x : Name} {slot : Slot} :
      Env.get env x = some slot →
      TypeOf env (LVal.var x) slot.ty slot.lifetime
  | derefBox {env : Env} {lv : LVal} {ty : Ty} {lifetime : Lifetime} :
      TypeOf env lv (.box ty) lifetime →
      TypeOf env (LVal.deref lv) ty lifetime
  | derefBorrow {env : Env} {lv target : LVal} {mutable : Bool}
      {targets : List LVal} {ty : Ty} {lifetime targetLifetime : Lifetime} :
      TypeOf env lv (.borrow mutable targets) lifetime →
      target ∈ targets →
      TypeOf env target ty targetLifetime →
      TypeOf env (LVal.deref lv) ty targetLifetime
  | index {env : Env} {lv : LVal} {fields : List Ty} {i : Nat}
      {ty : Ty} {lifetime : Lifetime} :
      TypeOf env lv (.tuple fields) lifetime →
      fields[i]? = some ty →
      TypeOf env (LVal.index lv i) ty lifetime

/--
Paper checker predicate for defined types.
-/
inductive TyDefined : Ty → Prop where
  | unit : TyDefined .unit
  | int : TyDefined .int
  | borrow {mutable : Bool} {lvals : List LVal} : TyDefined (.borrow mutable lvals)
  | box {ty : Ty} : TyDefined ty → TyDefined (.box ty)
  | tuple {tys : List Ty} : (∀ ty, ty ∈ tys → TyDefined ty) → TyDefined (.tuple tys)

/--
Paper checker predicate for copyable types.
-/
inductive Copyable : Ty → Prop where
  | unit : Copyable .unit
  | int : Copyable .int
  | borrow {lvals : List LVal} : Copyable (.borrow false lvals)
  | tuple {tys : List Ty} : (∀ ty, ty ∈ tys → Copyable ty) → Copyable (.tuple tys)

/--
Paper checker predicate for references in a type being within a lifetime.
-/
def RefsWithin (_env : Env) (_lifetime : Lifetime) (_ty : Ty) : Prop :=
  True

/--
Paper checker predicate for assigning a type within a lifetime.
-/
def Within (env : Env) (lifetime : Lifetime) (ty : Ty) : Prop :=
  RefsWithin env lifetime ty

/--
Paper checker predicate for read permission.
-/
def ReadAllowed (_env : Env) (_lv : LVal) : Prop :=
  True

/--
Paper checker predicate for write permission.
-/
def WriteAllowed (_env : Env) (_lv : LVal) : Prop :=
  True

/--
Paper checker predicate for mutable l-values.
-/
def MutLVal (_env : Env) (_lv : LVal) : Prop :=
  True

/--
Paper checker relation for moving out of an l-value.
-/
inductive Move : Env → LVal → Env → Prop where
  | intro {env env' : Env} {lv : LVal} : Move env lv env'

/--
Paper checker relation for writing an l-value type.
-/
inductive Write : Env → LVal → Ty → Bool → Env → Prop where
  | intro {env env' : Env} {lv : LVal} {ty : Ty} {strong : Bool} :
      Write env lv ty strong env'

/--
Paper checker predicate for type compatibility.
-/
def Compatible (_env : Env) (_lhs rhs : Ty) : Prop :=
  TyDefined rhs

/--
Paper checker relation for type union.
-/
inductive Union : Ty → Ty → Ty → Prop where
  | left {lhs rhs : Ty} : TyDefined lhs → Union lhs rhs lhs
  | right {lhs rhs : Ty} : TyDefined rhs → Union lhs rhs rhs

/--
Paper checker predicate for dropping a lifetime from an environment.
-/
def ScopedAfterDrop (_env : Env) (_dropped : Lifetime) : Prop :=
  True

/--
Paper checker relation for joining branch environments.
-/
inductive JoinEnv : Env → Env → Env → Prop where
  | intro {lhs rhs joined : Env} : JoinEnv lhs rhs joined

end BorrowChecker

mutual
  /--
  Store-free value typing bridge used only by bridge-level executable wrappers.

  TODO: This is intentionally weaker than Paper Definition 4.4.  Paper
  preservation uses the store-aware `ValueAbstracts` relation instead.
  -/
  inductive ValueHasType : Value → Ty → Prop where
    | unit : ValueHasType .unit Ty.unit
    | int (n : Int) : ValueHasType (.int n) Ty.int
    | tuple {values : List Value} {tys : List Ty} :
        ValuesHaveTypes values tys →
        ValueHasType (.tuple values) (.tuple tys)

    -- TODO: This context-free fallback is only for bridge-level statements that
    -- do not expose the final store.  Paper preservation uses `ValueAbstracts`.
    | ref {r : Reference} :
        ValueHasType (.ref r) (.borrow false [])

    -- TODO: Moved values should only appear inside the store; connecting this to
    -- `Ty.undef` requires a store typing invariant.
    | moved {ty : Ty} :
        ValueHasType .moved (.undef ty)

  /--
  Executable-soundness value typing bridge, list version of `ValueHasType`.
  -/
  inductive ValuesHaveTypes : List Value → List Ty → Prop where
    | nil : ValuesHaveTypes [] []
    | cons {value : Value} {values : List Value} {ty : Ty} {tys : List Ty} :
        ValueHasType value ty →
        ValuesHaveTypes values tys →
        ValuesHaveTypes (value :: values) (ty :: tys)
end

mutual
  /--
  Paper Section 3 borrow-checker/type-checker judgment.
  -/
  inductive Checks : Env → Lifetime → Term → Env → Ty → Prop where
    | unit {env : Env} {lifetime : Lifetime} :
        Checks env lifetime (.val .unit) env Ty.unit
    | int {env : Env} {lifetime : Lifetime} (n : Int) :
        Checks env lifetime (.val (.int n)) env Ty.int
    | runtimeTuple {env : Env} {lifetime : Lifetime} {fields : List Value} {tys : List Ty} :
        ValuesHaveTypes fields tys →
        Checks env lifetime (.val (.tuple fields)) env (Ty.tuple tys)
    | accessCopy {env : Env} {lifetime : Lifetime} {lv : LVal} {ty : Ty} {targetLifetime : Lifetime} :
        BorrowChecker.TypeOf env lv ty targetLifetime →
        BorrowChecker.TyDefined ty →
        BorrowChecker.Copyable ty →
        BorrowChecker.ReadAllowed env lv →
        Checks env lifetime (.access .copy lv) env ty
    | accessTemp {env : Env} {lifetime : Lifetime} {lv : LVal} {ty : Ty} {targetLifetime : Lifetime} :
        BorrowChecker.TypeOf env lv ty targetLifetime →
        BorrowChecker.TyDefined ty →
        BorrowChecker.ReadAllowed env lv →
        Checks env lifetime (.access .temp lv) env ty
    | accessMove {env env' : Env} {lifetime : Lifetime} {lv : LVal} {ty : Ty}
        {targetLifetime : Lifetime} :
        BorrowChecker.TypeOf env lv ty targetLifetime →
        BorrowChecker.TyDefined ty →
        BorrowChecker.WriteAllowed env lv →
        BorrowChecker.Move env lv env' →
        Checks env lifetime (.access .move lv) env' ty
    | borrowImm {env : Env} {lifetime targetLifetime : Lifetime} {lv : LVal} {ty : Ty} :
        BorrowChecker.TypeOf env lv ty targetLifetime →
        BorrowChecker.TyDefined ty →
        BorrowChecker.ReadAllowed env lv →
        Checks env lifetime (.borrow false lv) env (.borrow false [lv])
    | borrowMut {env : Env} {lifetime targetLifetime : Lifetime} {lv : LVal} {ty : Ty} :
        BorrowChecker.TypeOf env lv ty targetLifetime →
        BorrowChecker.TyDefined ty →
        BorrowChecker.WriteAllowed env lv →
        BorrowChecker.MutLVal env lv →
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
        BorrowChecker.TypeOf env lhs lhsTy targetLifetime →
        Checks env lifetime rhs env₁ rhsTy →
        BorrowChecker.Compatible env₁ lhsTy rhsTy →
        BorrowChecker.Within env₁ targetLifetime rhsTy →
        BorrowChecker.Write env₁ lhs rhsTy true env₂ →
        BorrowChecker.WriteAllowed env₂ lhs →
        Checks env lifetime (.assign lhs rhs) env₂ Ty.unit
    | block {env env' : Env} {lifetime blockLifetime : Lifetime} {terms : List Term}
        {ty : Ty} :
        ChecksSeq env blockLifetime terms env' ty →
        BorrowChecker.Within env' lifetime ty →
        BorrowChecker.ScopedAfterDrop env' blockLifetime →
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
        BorrowChecker.Compatible env₃ lhsTy rhsTy →
        BorrowChecker.Copyable lhsTy →
        BorrowChecker.Copyable rhsTy →
        Checks env₃ lifetime trueBlock trueEnv trueTy →
        Checks env₃ lifetime falseBlock falseEnv falseTy →
        BorrowChecker.JoinEnv trueEnv falseEnv joinedEnv →
        BorrowChecker.Compatible joinedEnv trueTy falseTy →
        BorrowChecker.Union trueTy falseTy resultTy →
        Checks env lifetime (.ifElse eq lhs rhs trueBlock falseBlock) joinedEnv resultTy

  /--
  Paper Section 3 checker judgment for block sequences.
  -/
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

  /--
  Paper Section 3 checker judgment for tuple elements and checker-only
  temporaries.
  -/
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

end Paper
end LwRust
