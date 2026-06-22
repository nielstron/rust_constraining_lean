import Std

/-!
Syntax for the core FR calculus in Figure 1 of `lw_rust.pdf`.
-/

namespace LwRust
namespace Core

abbrev Name := String

/--
Reference lifetime names are paths in the lexical lifetime tree.

This is intentionally a wrapper rather than an abbreviation for `List Nat`, so
we can give lifetimes their own order without changing Lean's existing list
order.
-/
structure Lifetime where
  path : List Nat
  deriving BEq, DecidableEq, Repr

instance : Coe (List Nat) Lifetime where
  coe path := { path := path }

inductive LVal where
  | var (name : Name)
  | deref (operand : LVal)
  deriving BEq, DecidableEq, Repr

/--
Paper Section 2.2's abstract location: a chunk of allocated storage.  The core
semantics names stack-allocated variable locations by variable name and heap
locations by a fresh natural.
-/
inductive Location where
  | var (name : Name)
  | heap (address : Nat)
  deriving BEq, DecidableEq, Repr

mutual
  inductive Ty where
    | unit
    | int
    | borrow (mutable : Bool) (targets : List LVal)
    | box (element : Ty)
    /-- Section 6.1 control-flow extension (Figure 5): Boolean type. -/
    | bool
    deriving BEq, DecidableEq, Repr

  inductive PartialTy where
    | ty (type : Ty)
    | box (element : PartialTy)
    | undef (shape : Ty)
    deriving BEq, DecidableEq, Repr
end

instance : Coe Ty PartialTy where
  coe := PartialTy.ty

structure Reference where
  location : Location
  owner : Bool
  deriving BEq, DecidableEq, Repr

def Reference.borrowed (ref : Reference) : Reference :=
  { ref with owner := false }

inductive Value where
  | unit
  | int (value : Int)
  | ref (location : Reference)
  /-- Section 6.1 control-flow extension (Figure 5): `true` / `false`. -/
  | bool (value : Bool)
  deriving BEq, DecidableEq, Repr

inductive PartialValue where
  | value (value : Value)
  | undef
  deriving BEq, DecidableEq, Repr

def Lifetime.root : Lifetime := { path := [] }

def Lifetime.contains (outer inner : Lifetime) : Bool :=
  outer.path.isPrefixOf inner.path

inductive Term where
  | block (lifetime : Lifetime) (terms : List Term)
  | letMut (name : Name) (initialiser : Term)
  | assign (lhs : LVal) (rhs : Term)
  | box (operand : Term)
  | borrow (mutable : Bool) (operand : LVal)
  | move (operand : LVal)
  | copy (operand : LVal)
  | val (value : Value)
  /-- Synthetic extractor placeholder, analogous to `ast_copier`'s polymorphic
  `__missing__<T>() -> T`. It is source-like generated syntax and diverges at
  runtime, so it also plays the role of Rust's `panic!()`: a diverging
  expression usable at any (loan-free) type. -/
  | missing
  /-- Section 6.1 control-flow extension (Figure 5): equality comparator and conditional -/
  | eq (lhs rhs : Term)
  | ite (condition trueBranch falseBranch : Term)
  /-- While loop (beyond the paper, which is loop-free): `while condition
  { body }`.  The body is scoped like a block under `bodyLifetime`.  The
  loop does not reduce by syntactic unfolding — copying the body under a
  fresh block would detach its lexical block lifetimes from the ambient
  chain — but through the two in-flight runtime forms below. -/
  | whileLoop (bodyLifetime : Lifetime) (condition body : Term)
  /-- Runtime form: the condition copy in the first slot is being evaluated;
  the original condition and body are retained for later iterations. -/
  | whileCond (bodyLifetime : Lifetime) (conditionInFlight condition body : Term)
  /-- Runtime form: the body (wrapped in a block, so block reduction manages
  the body scope) is being evaluated; once it yields a value the iteration's
  result is dropped and the loop re-enters `whileCond`. -/
  | whileBody (bodyLifetime : Lifetime) (bodyInFlight condition body : Term)
  deriving BEq, Repr

mutual
  /-- Structural size of a term.  This is still useful for the original core
  calculus, but generated `.missing` terms self-loop and therefore do not
  strictly decrease. -/
  def Term.size : Term → Nat
    | .block _ terms => 1 + Term.sizeList terms
    | .letMut _ initialiser => 1 + initialiser.size
    | .assign _ rhs => 1 + rhs.size
    | .box operand => 1 + operand.size
    | .borrow _ _ => 2
    | .move _ => 2
    | .copy _ => 2
    | .val _ => 1
    | .missing => 1
    | .eq lhs rhs => 1 + lhs.size + rhs.size
    | .ite condition trueBranch falseBranch =>
        1 + condition.size + trueBranch.size + falseBranch.size
    | .whileLoop _ condition body => 1 + condition.size + body.size
    | .whileCond _ conditionInFlight condition body =>
        1 + conditionInFlight.size + condition.size + body.size
    | .whileBody _ bodyInFlight condition body =>
        1 + bodyInFlight.size + condition.size + body.size

  def Term.sizeList : List Term → Nat
    | [] => 0
    | term :: rest => term.size + Term.sizeList rest
end

def Term.IsBlock : Term → Prop
  | .block _ _ => True
  | _ => False

def Term.isBlock : Term → Bool
  | .block _ _ => true
  | _ => false

@[simp] theorem Term.isBlock_eq_true_iff {term : Term} :
    term.isBlock = true ↔ term.IsBlock := by
  cases term <;> simp [Term.isBlock, Term.IsBlock]

inductive Term.Diverges : Term → Prop where
  | missing : Term.Diverges .missing
  | block {lifetime : Lifetime} {terms : List Term} {term : Term} :
      term ∈ terms →
      Term.Diverges term →
      Term.Diverges (.block lifetime terms)

end Core
end LwRust
