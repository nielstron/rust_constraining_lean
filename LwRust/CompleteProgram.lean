import Std
import LwRust.Definitions

/-!
The complete toy language shared by the checkers and extractors.

A complete program is a list of statements.  Function definitions are
statements, whether they appear at top level or inside another function body.
The language deliberately has only enough structure to make validity nontrivial.
-/

namespace LwRust

inductive Ty where
  | never
  | bool
  | int
  | prod (fields : List Ty)
  | sum (variants : List Ty)
  | fn (params : List Ty) (ret : Ty)
  | sharedRef (τ : Ty)
  | mutRef (τ : Ty)
  deriving Repr

def Ty.size : Ty → Nat
  | Ty.never => 0
  | Ty.bool => 1
  | Ty.int => 1
  | Ty.prod fields => fields.foldl (fun acc τ => acc + τ.size) 0
  | Ty.sum variants => 1 + variants.foldl (fun acc τ => max acc τ.size) 0
  | Ty.fn _ _ => 1
  | Ty.sharedRef _ => 1
  | Ty.mutRef _ => 1

abbrev Name := String

inductive Place where
  | var (x : Name)
  | field (base : Place) (index : Nat)
  deriving Repr

structure FunSig where
  params : List Ty
  ret : Ty
  requiresMut : List Place := []
  deriving Repr

abbrev VarEnv := Name → Option Ty
abbrev FunEnv := Name → Option FunSig

structure Env where
  vars : VarEnv
  funs : FunEnv
  ret : Option Ty

def Env.empty : Env :=
  { vars := fun _ => none, funs := fun _ => none, ret := none }

def Env.withFun (Γ : Env) (f : Name) (sig : FunSig) : Env :=
  { Γ with
    vars := fun x => if x = f then some (Ty.fn sig.params sig.ret) else Γ.vars x,
    funs := fun g => if g = f then some sig else Γ.funs g }

def Env.withVar (Γ : Env) (x : Name) (τ : Ty) : Env :=
  { Γ with vars := fun y => if y = x then some τ else Γ.vars y }

def Env.withReturn (Γ : Env) (τ : Ty) : Env :=
  { Γ with ret := some τ }

def Place.root : Place → Name
  | Place.var x => x
  | Place.field base _ => base.root

def Place.path : Place → List Nat
  | Place.var _ => []
  | Place.field base i => base.path ++ [i]

def List.isPrefix {α : Type} : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y ∧ List.isPrefix xs ys

def Place.overlaps (p q : Place) : Prop :=
  p.root = q.root ∧
    (List.isPrefix p.path q.path ∨ List.isPrefix q.path p.path)

def Place.isAtOrBelow (child parent : Place) : Prop :=
  child.root = parent.root ∧ List.isPrefix parent.path child.path

theorem List.isPrefix_refl {α : Type} (xs : List α) :
    List.isPrefix xs xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
      exact ⟨rfl, ih⟩

theorem Place.overlaps_refl (p : Place) : Place.overlaps p p := by
  exact ⟨rfl, Or.inl (List.isPrefix_refl p.path)⟩

def paramsToVars : List (Name × Ty) → VarEnv
  | [] => fun _ => none
  | (x, τ) :: rest =>
      fun y => if y = x then some τ else paramsToVars rest y

mutual

inductive Expr where
  | panic
  | bool (b : Bool)
  | int (n : Int)
  | place (p : Place)
  | deref (p : Place)
  | add (lhs rhs : Expr)
  | eq (lhs rhs : Expr)
  | call (f : Name) (args : List Expr)
  | caseTag (p : Place) (branches : List (List Stmt))
  deriving Repr

inductive Stmt where
  | expr (e : Expr)
  | letStmt (x : Name) (τ : Ty) (e : Expr)
  | assign (p : Place) (e : Expr)
  | block (body : List Stmt)
  | funDef
      (name : Name)
      (params : List (Name × Ty))
      (ret : Ty)
      (body : List Stmt)
  deriving Repr

end

abbrev Block := List Stmt
abbrev Program := Block

namespace Expr

/- Compatibility shims for proof names that still talk about the old
copy/move split.  These are not constructors; the complete language has a
single place-expression form whose effect is determined by type. -/
abbrev copy (p : Place) : Expr := Expr.place p
abbrev move (p : Place) : Expr := Expr.place p

end Expr

namespace CompleteDsl

def tyInt := Ty.int
def tyBool := Ty.bool
def tyProd := Ty.prod
def tySum := Ty.sum
def expr := Stmt.expr

/- `clet` and `cass` expose core statements. `cmove dst <- src` below is
legacy syntax for `cass dst := Expr.place src`; there is no move-assignment
statement in the complete language. -/
def letStmt := Stmt.letStmt
def assign := Stmt.assign

def panic := Stmt.expr Expr.panic
def block := Stmt.block
def fn := Stmt.funDef

end CompleteDsl

/-!
Object-language concrete syntax.

These syntax categories are intentionally separate from Lean `term` syntax.
They expose the constructor order used by the generated partial grammar:
children before the current frontier are complete, the frontier child is
partial, and children after it are absent.
-/

declare_syntax_cat cty
declare_syntax_cat cplace
declare_syntax_cat cexpr
declare_syntax_cat cstmt
declare_syntax_cat cblock
declare_syntax_cat cbranch
declare_syntax_cat cparam

syntax (name := ctyNever) "cty_never" : cty
syntax (name := ctyBool) "cty_bool" : cty
syntax (name := ctyInt) "cty_int" : cty
syntax (name := ctyProd) "cty_prod" "[" cty,* "]" : cty
syntax (name := ctySum) "cty_sum" "[" cty,* "]" : cty
syntax (name := ctyFn) "cty_fn" "(" cty,* ")" "=>" cty : cty
syntax (name := ctySharedRef) "&" cty : cty
syntax (name := ctyMutRef) "&mut" cty : cty

syntax (name := cplaceVar) ident : cplace
syntax (name := cplaceField) cplace "." num : cplace

syntax (name := cexprPanic) "cexpr_panic" : cexpr
syntax (name := cexprTrue) "cexpr_true" : cexpr
syntax (name := cexprFalse) "cexpr_false" : cexpr
syntax (name := cexprInt) num : cexpr
syntax (name := cexprPlace) cplace : cexpr
syntax (name := cexprDeref) "*" cplace : cexpr
syntax (name := cexprName) ident : cexpr
syntax (name := cexprAdd) cexpr "+" cexpr : cexpr
syntax (name := cexprEq) cexpr "==" cexpr : cexpr
syntax (name := cexprCall) ident "(" cexpr,* ")" : cexpr
syntax (name := cexprCaseTag) "cexpr_case_tag" cplace "{" cblock,* "}" : cexpr

syntax (name := cbranchNamed) ident "=>" cblock : cbranch
syntax (name := cparamNamed) ident ":" cty : cparam

syntax (name := cstmtExpr) cexpr : cstmt
syntax (name := cstmtLet) "cstmt_let" ident ":" cty ":=" cexpr : cstmt
syntax (name := cstmtAssign) cplace ":=" cexpr : cstmt
syntax (name := cstmtBlock) cblock : cstmt
syntax (name := cstmtFunDef) "cstmt_fn" ident "(" cparam,* ")" ":" cty "=>" cblock : cstmt

syntax (name := cblockBraces) "{" cstmt,* "}" : cblock

/-- Legacy syntax -/

syntax "cty_int" : term
syntax "cty_bool" : term
syntax "*" ident : term
syntax "cexpr" term : term
syntax "clet" ident ":" term ":=" term : term
syntax "cass" ident ":=" term : term
syntax "cmove" ident "<-" ident : term
syntax "cpanic" : term
syntax "cblock" term : term
syntax "cfn" ident "()" ":" term "=>" term : term

macro_rules
  | `(cty_int) => `(Ty.int)
  | `(cty_bool) => `(Ty.bool)
  | `(cexpr $e:term) => `(CompleteDsl.expr $e)
  | `(cpanic) => `(CompleteDsl.panic)
  | `(cblock $body:term) => `(CompleteDsl.block $body)

macro "*" name:ident : term => do
  let varName := name.getId.toString
  `(Expr.deref (Place.var $(Lean.quote varName)))

macro "cass" name:ident ":=" e:term : term => do
  let varName := name.getId.toString
  `(CompleteDsl.assign (Place.var $(Lean.quote varName)) $e)

macro "clet" name:ident ":" τ:term ":=" e:term : term => do
  let varName := name.getId.toString
  `(CompleteDsl.letStmt $(Lean.quote varName) $τ $e)

macro "cmove" dst:ident "<-" src:ident : term => do
  let dstName := dst.getId.toString
  let srcName := src.getId.toString
  `(CompleteDsl.assign
    (Place.var $(Lean.quote dstName)) (Expr.place (Place.var $(Lean.quote srcName))))

macro "cfn" name:ident "()" ":" ret:term "=>" body:term : term => do
  let fnName := name.getId.toString
  `(CompleteDsl.fn $(Lean.quote fnName) [] $ret $body)

end LwRust
