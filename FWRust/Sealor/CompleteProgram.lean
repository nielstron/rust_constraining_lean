import FWRust.Paper.Syntax

/-!
Complete FWRust aliases and constructor helpers for the sealor development.
-/

namespace ConservativeSealor

abbrev Name := FWRust.Core.Name
abbrev Lifetime := FWRust.Core.Lifetime
abbrev LVal := FWRust.Core.LVal
abbrev Location := FWRust.Core.Location
abbrev Ty := FWRust.Core.Ty
abbrev Value := FWRust.Core.Value
abbrev Reference := FWRust.Core.Reference
abbrev Term := FWRust.Core.Term
abbrev Program := Term

namespace CompleteDsl

def tyUnit : Ty := .unit
def tyInt : Ty := .int
def tyBorrow (mutable : Bool) (target : LVal) : Ty :=
  .borrow mutable target
def tyBox (element : Ty) : Ty := .box element

def lvalVar (x : Name) : LVal := .var x
def lvalDeref (operand : LVal) : LVal := .deref operand

def unit : Term := .val .unit
def int (n : Int) : Term := .val (.int n)
def block (lifetime : Lifetime) (terms : List Term) : Term :=
  .block lifetime terms
def letMut (x : Name) (initialiser : Term) : Term :=
  .letMut x initialiser
def assign (lhs : LVal) (rhs : Term) : Term :=
  .assign lhs rhs
def box (operand : Term) : Term := .box operand
def borrow (mutable : Bool) (operand : LVal) : Term :=
  .borrow mutable operand
def move (operand : LVal) : Term := .move operand
def copy (operand : LVal) : Term := .copy operand

end CompleteDsl

end ConservativeSealor
