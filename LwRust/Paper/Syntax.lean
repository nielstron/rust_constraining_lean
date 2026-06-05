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
  deriving BEq, Repr

inductive PartialValue where
  | value (value : Value)
  | undef
  deriving BEq, Repr

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
  deriving BEq, Repr


end Core
end LwRust
