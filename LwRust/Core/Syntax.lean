import Std

/-!
Core syntax for the Featherweight Rust implementation.

This is a direct executable representation of the Java syntax in
`FeatherweightRust/src/featherweightrust/core/Syntax.java`, with two deliberate
adaptations:

* values are separated from reducible terms, instead of Java values also being
  terms through inheritance;
* tuple path elements are present in the shared path datatype so that the
  tuple extension can reuse the core l-value machinery.
-/

namespace LwRust
namespace Core

abbrev Name := String
abbrev Lifetime := List Nat

def Lifetime.root : Lifetime := []

def Lifetime.contains (outer inner : Lifetime) : Bool :=
  outer.isPrefixOf inner

def Lifetime.min? (lhs rhs : Lifetime) : Option Lifetime :=
  if lhs.contains rhs then some rhs
  else if rhs.contains lhs then some lhs
  else none

inductive PathElem where
  | deref
  | index (i : Nat)
  deriving BEq, DecidableEq, Repr

abbrev Path := List PathElem

namespace Path

def conflicts : Path → Path → Bool
  | [], _ => true
  | _, [] => true
  | x :: xs, y :: ys =>
      let elemConflict :=
        match x, y with
        | .deref, .deref => true
        | .index i, .index j => i == j
        -- TODO: Java throws for incomparable extension elements; the executable
        -- Lean model treats mixed elements conservatively as conflicting.
        | _, _ => true
      elemConflict && conflicts xs ys

end Path

structure LVal where
  name : Name
  path : Path := []
  deriving BEq, DecidableEq, Repr

namespace LVal

def var (x : Name) : LVal := { name := x, path := [] }
def deref (lv : LVal) : LVal := { lv with path := lv.path ++ [.deref] }
def index (lv : LVal) (i : Nat) : LVal := { lv with path := lv.path ++ [.index i] }

def conflicts (lhs rhs : LVal) : Bool :=
  lhs.name == rhs.name && Path.conflicts lhs.path rhs.path

def traverse (lv : LVal) (p : Path) (i : Nat) : LVal :=
  { lv with path := lv.path ++ p.drop i }

end LVal

structure Reference where
  address : Nat
  path : List Nat := []
  owner : Bool := true
  deriving BEq, DecidableEq, Repr

namespace Reference

def borrowed (r : Reference) : Reference :=
  { r with owner := false }

def atIndex (r : Reference) (i : Nat) : Reference :=
  { r with path := r.path ++ [i], owner := false }

end Reference

inductive Ty where
  | unit
  | int
  | borrow (mutable : Bool) (lvals : List LVal)
  | box (element : Ty)
  | tuple (fields : List Ty)
  | undef (shape : Ty)
  deriving BEq, Repr

inductive Value where
  | unit
  | int (n : Int)
  | ref (r : Reference)
  | tuple (fields : List Value)
  deriving BEq, Repr

inductive AccessKind where
  | move
  | copy
  | temp
  deriving BEq, DecidableEq, Repr

inductive Term where
  | val (v : Value)
  | letMut (x : Name) (initialiser : Term)
  | assign (lhs : LVal) (rhs : Term)
  | block (lifetime : Lifetime) (terms : List Term)
  | access (kind : AccessKind) (operand : LVal)
  | borrow (mutable : Bool) (operand : LVal)
  | box (operand : Term)
  | tuple (terms : List Term)
  | ifElse (eq : Bool) (lhs rhs : Term) (trueBlock falseBlock : Term)
  | invoke (name : Name) (args : List Term)
  deriving BEq, Repr

namespace Term

def int (n : Int) : Term := .val (.int n)
def unit : Term := .val .unit
def move (lv : LVal) : Term := .access .move lv
def copy (lv : LVal) : Term := .access .copy lv
def temp (lv : LVal) : Term := .access .temp lv
def immBorrow (lv : LVal) : Term := .borrow false lv
def mutBorrow (lv : LVal) : Term := .borrow true lv

end Term

structure Slot where
  ty : Ty
  lifetime : Lifetime
  deriving BEq, Repr

abbrev Env := List (Name × Slot)

namespace Env

def empty : Env := []

def get (env : Env) (x : Name) : Option Slot :=
  match env with
  | [] => none
  | (y, s) :: rest => if x == y then some s else get rest x

def erase (env : Env) (x : Name) : Env :=
  env.filter (fun entry => entry.fst != x)

def put (env : Env) (x : Name) (slot : Slot) : Env :=
  (x, slot) :: erase env x

def removeMany (env : Env) (xs : List Name) : Env :=
  xs.foldl erase env

def dropLifetime (env : Env) (lifetime : Lifetime) : Env :=
  env.filter (fun entry => entry.snd.lifetime != lifetime)

def names (env : Env) : List Name :=
  env.map Prod.fst

end Env

end Core
end LwRust
