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
    deriving BEq, Repr

  inductive PartialTy where
    | ty (type : Ty)
    | box (element : PartialTy)
    | undef (shape : Ty)
    deriving BEq, Repr
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

def Lifetime.min? (lhs rhs : Lifetime) : Option Lifetime :=
  if lhs.contains rhs then some rhs
  else if rhs.contains lhs then some lhs
  else none

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

  def Term.sizeList : List Term → Nat
    | [] => 0
    | term :: rest => term.size + Term.sizeList rest
end

theorem Term.size_pos : ∀ term : Term, 0 < term.size := by
  intro term
  cases term <;> simp [Term.size] <;> omega

/--
Syntactic divergence: a conservative approximation of "never evaluates to a
value", modelling rustc's never-type (`!`) propagation.  `Term.missing` plays
the role of `panic!()` (it self-loops at runtime), and a block diverges when
one of its statements does — control cannot reach the block's end.

This powers the divergence-aware conditional rule `T-IfDiv`
(`TermTyping.iteDiverging`), the analogue of rustc treating a
`panic!()`-terminated branch as unreachable at the merge point.
-/
inductive Term.Diverges : Term → Prop where
  | missing : Term.Diverges .missing
  | block {lifetime : Lifetime} {terms : List Term} {term : Term} :
      term ∈ terms →
      Term.Diverges term →
      Term.Diverges (.block lifetime terms)


end Core
end LwRust
