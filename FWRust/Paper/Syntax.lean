import Std

/-!
Syntax for the core FR calculus in Figure 1 of `fw_rust.pdf`.
-/

namespace FWRust
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
    | borrow (mutable : Bool) (target : LVal)
    | box (element : Ty)
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
  deriving BEq, Repr

mutual
  /-- Structural size of a term.  Every reduction step strictly decreases it,
  which is what makes the core calculus terminating. -/
  def Term.size : Term → Nat
    | .block _ terms => 1 + Term.sizeList terms
    | .letMut _ initialiser => 1 + initialiser.size
    | .assign _ rhs => 1 + rhs.size
    | .box operand => 1 + operand.size
    | .borrow _ _ => 2
    | .move _ => 2
    | .copy _ => 2
    | .val _ => 1

  def Term.sizeList : List Term → Nat
    | [] => 0
    | term :: rest => term.size + Term.sizeList rest
end

end Core
end FWRust
