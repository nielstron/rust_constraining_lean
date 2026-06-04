import LwRust.Core.OperationalSemantics

/-!
Complete object-language surface used by the translated tests.

The constructors mirror the concrete Featherweight Rust syntax:

* `let mut x = e`
* `x = e`, `*x = e`, `x.0 = e`
* blocks `{ ... }`
* accesses `x` (move), `!x` (copy), borrows `&x` / `&mut x`
* `box e`, tuples, and `if e == e { ... } else { ... }`

Function declarations/invocations are represented in `Extensions.Functions`,
but their checker/evaluator translation is still marked TODO there.
-/

namespace LwRust
namespace CompleteProgram

open Core

def root : Lifetime := Lifetime.root
def l (parts : List Nat) : Lifetime := parts

def var (x : Name) : LVal := LVal.var x
def deref (lv : LVal) : LVal := lv.deref
def field (lv : LVal) (i : Nat) : LVal := lv.index i

def int (n : Int) : Term := Term.int n
def unit : Term := Term.unit
def move (lv : LVal) : Term := Term.move lv
def copy (lv : LVal) : Term := Term.copy lv
def temp (lv : LVal) : Term := Term.temp lv
def borrow (lv : LVal) : Term := Term.immBorrow lv
def borrowMut (lv : LVal) : Term := Term.mutBorrow lv
def box (t : Term) : Term := Term.box t
def tuple (ts : List Term) : Term := Term.tuple ts
def letMut (x : Name) (initialiser : Term) : Term := Term.letMut x initialiser
def assign (lhs : LVal) (rhs : Term) : Term := Term.assign lhs rhs
def block (lifetime : Lifetime) (terms : List Term) : Term := Term.block lifetime terms
def ifEq (lhs rhs trueBlock falseBlock : Term) : Term := Term.ifElse true lhs rhs trueBlock falseBlock
def ifNe (lhs rhs trueBlock falseBlock : Term) : Term := Term.ifElse false lhs rhs trueBlock falseBlock
def invoke (name : Name) (args : List Term) : Term := Term.invoke name args

def check := Core.BorrowChecker.checkProgram
def execute := Core.OperationalSemantics.execute

end CompleteProgram
end LwRust
