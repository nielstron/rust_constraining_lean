import LwRust.CompleteProgram

namespace LwRust
namespace Tests
namespace CoreTests

open Core
open CompleteProgram

def x := var "x"
def y := var "y"
def z := var "z"

def top (terms : List Term) : Term := block [0] terms
def inner (terms : List Term) : Term := block [0, 0] terms

def runsToBool (program : Term) (value : Value) : Bool :=
  match execute program with
  | Except.ok actual => actual == value
  | Except.error _ => false

abbrev runsTo (program : Term) (value : Value) : Prop :=
  runsToBool program value = true

def invalidBool (program : Term) : Bool :=
  match check program with
  | Except.ok _ => false
  | Except.error _ => true

abbrev invalid (program : Term) : Prop :=
  invalidBool program = true

example : runsTo (top [letMut "x" (int 123), move x]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), copy x]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), letMut "y" (move x), move y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), letMut "y" (copy x), move y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 123), move y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 123), assign x (int 2), move y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), inner [letMut "y" (int 123), move y]]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), inner [assign x (int 123)], move x]) (.int 123) := by native_decide
example : runsTo (top [int 123]) (.int 123) := by native_decide
example : runsTo (top [inner [int 1], int 123]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), letMut "y" (int 1)]) .unit := by native_decide

example :
    runsTo (top [letMut "x" (box (int 123)), move (deref x)]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (int 1)), assign (deref x) (int 123), copy (deref x)]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (box (int 1))), assign (deref (deref x)) (int 123), copy (deref (deref x))]) (.int 123) := by
  native_decide

example : invalid (top [letMut "x" (int 123), letMut "y" (move x), move x]) := by native_decide
example : invalid (top [letMut "x" (box (int 1)), letMut "y" (copy x)]) := by native_decide
example : invalid (top [letMut "x" (int 123), letMut "y" (borrowMut x), letMut "z" (copy y)]) := by native_decide
example : invalid (top [letMut "x" (int 123), letMut "y" (borrowMut x), assign x (int 1)]) := by native_decide
example : invalid (top [assign x (int 123)]) := by native_decide
example : invalid (top [letMut "x" (int 123), assign y (int 123)]) := by native_decide
example : invalid (top [letMut "x" (box (int 1)), move x, move x]) := by native_decide
example : invalid (top [letMut "x" (int 123), letMut "y" (borrow x), move (deref y)]) := by native_decide
example : invalid (top [letMut "x" (int 123), borrow x]) := by native_decide

-- TODO: The remaining Java `CoreTests` are parser-level regression cases. They
-- should be ported once a Lean parser or a generator from the Java strings
-- exists; the executable checker/evaluator above already exposes the needed
-- AST-level surface.

end CoreTests
end Tests
end LwRust
