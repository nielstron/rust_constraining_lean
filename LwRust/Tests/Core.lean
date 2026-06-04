import LwRust.Core.OperationalSemantics
import LwRust.Core.ProgramSpace

namespace LwRust
namespace Tests
namespace CoreTests

open Core

def x := var "x"
def y := var "y"
def z := var "z"
def p := var "p"
def q := var "q"
def w := var "w"
def x1 := var "x1"
def x2 := var "x2"

def top (terms : List Term) : Term := block [0] terms
def inner (terms : List Term) : Term := block [0, 0] terms
def inner2 (terms : List Term) : Term := block [0, 0, 0] terms

def runsToBool (program : Term) (value : Value) : Bool :=
  match OperationalSemantics.execute program with
  | Except.ok actual => actual == value
  | Except.error _ => false

abbrev runsTo (program : Term) (value : Value) : Prop :=
  runsToBool program value = true

def invalidBool (program : Term) : Bool :=
  match BorrowChecker.checkProgram program with
  | Except.ok _ => false
  | Except.error _ => true

abbrev invalid (program : Term) : Prop :=
  invalidBool program = true

namespace ProgramSpaceTests

def tinyConfig : ProgramSpace.Config :=
  { intCount := 1, maxVariables := 1, maxBlockDepth := 1, maxBlockWidth := 1 }

def tinyDefinedConfig : ProgramSpace.Config :=
  { intCount := 1, maxVariables := 2, maxBlockDepth := 1, maxBlockWidth := 2 }

def allCheckWithoutUndeclaredErrors (programs : List Term) : Bool :=
  programs.all (fun program =>
    match BorrowChecker.checkProgram program with
    | .ok _ => true
    | .error msg => msg != "variable undeclared")

example : ProgramSpace.Config.render tinyConfig = "P{1,1,1,1}" := by native_decide
example : (ProgramSpace.domain tinyConfig).isEmpty = false := by native_decide
example : (ProgramSpace.definedVariablePrograms tinyDefinedConfig 2).isEmpty = false := by native_decide
example : allCheckWithoutUndeclaredErrors (ProgramSpace.definedVariablePrograms tinyDefinedConfig 2) = true := by
  native_decide

end ProgramSpaceTests

example : runsTo (top [letMut "x" (int 123), move x]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), copy x]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), letMut "y" (move x), move y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), letMut "y" (move x), copy y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), letMut "y" (copy x), move y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 123), move y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 123), copy y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), letMut "y" (int 1), move x]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), letMut "y" (int 1), copy x]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 123), assign x (int 2), move y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 123), assign x (int 2), copy y]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), inner [letMut "y" (int 123), move y]]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), inner [letMut "y" (int 123), copy y]]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), inner [assign x (int 123)], move x]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 1), inner [assign x (int 123)], copy x]) (.int 123) := by native_decide
example :
    runsTo (top [letMut "x" (box (int 0)), inner [letMut "y" (move x), assign x (box (int 1))], move (deref x)])
      (.int 1) := by
  native_decide
example :
    runsTo (top [letMut "x" (box (int 0)), inner [letMut "y" (move x), assign x (box (int 1))], copy (deref x)])
      (.int 1) := by
  native_decide
example : runsTo (top [letMut "x" (box (int 0)), assign x (box (int 1)), move (deref x)]) (.int 1) := by
  native_decide
example : runsTo (top [letMut "x" (box (int 0)), assign x (box (int 1)), copy (deref x)]) (.int 1) := by
  native_decide
example : runsTo (top [int 123]) (.int 123) := by native_decide
example : runsTo (top [inner [int 1], int 123]) (.int 123) := by native_decide
example : runsTo (top [inner [inner2 [int 1], int 2], int 123]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), letMut "y" (int 1)]) .unit := by native_decide
example : runsTo (top [inner [int 1]]) (.int 1) := by native_decide
example : runsTo (top [inner [letMut "x" (int 123), move x]]) (.int 123) := by native_decide
example : runsTo (top [letMut "x" (int 123), inner [move x]]) (.int 123) := by native_decide

example :
    runsTo (top [letMut "x" (box (int 123)), move (deref x)]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (int 1)), assign (deref x) (int 123), copy (deref x)]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (box (int 1))), assign (deref (deref x)) (int 123), copy (deref (deref x))]) (.int 123) := by
  native_decide

example : runsTo (top [box (int 123), int 1]) (.int 1) := by native_decide
example : runsTo (top [letMut "x" (box (int 123)), move x, int 1]) (.int 1) := by native_decide
example : runsTo (top [letMut "x" (int 123), box (borrow x), move x]) (.int 123) := by native_decide

example :
    runsTo (top [letMut "y" (box (int 123)), letMut "x" (move (deref y)), move x]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "y" (box (int 123)), letMut "x" (copy (deref y)), move (deref y)]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "y" (int 123), letMut "z" (box (borrow y)), letMut "x" (move (deref z)), copy (deref x)])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "y" (int 123), letMut "z" (box (borrow y)), letMut "x" (copy (deref z)), copy (deref x)])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "y" (int 123), letMut "z" (box (borrow y)), letMut "x" (copy (deref z)), copy (deref (deref z))])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (box (int 123))), letMut "y" (move (deref x)), move (deref y)])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (box (int 123))), letMut "y" (move (deref x)), copy (deref y)])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (int 1)), inner [letMut "y" (box (int 123)), assign x (move y)], move (deref x)])
      (.int 123) := by
  native_decide

example : runsTo (top [letMut "x" (int 123), letMut "y" (borrow x), copy (deref y)]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 123), letMut "y" (borrow x), letMut "z" (copy (deref y)), move z])
      (.int 123) := by
  native_decide

example : runsTo (top [letMut "x" (int 123), inner [letMut "y" (borrow x), copy (deref y)]]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 123), inner [letMut "y" (borrow x), letMut "z" (copy y), copy (deref y)]])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (borrowMut x),
      inner [letMut "w" (int 123), letMut "z" (borrow w), copy (deref z)]])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 123), letMut "y" (box (borrowMut x)), letMut "z" (move (deref y)), copy (deref z)])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 123), letMut "y" (borrow x), letMut "z" (borrowMut y), copy (deref (deref z))])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x1" (int 1), letMut "x2" (int 123), letMut "y" (borrow x1), letMut "z" (borrowMut y),
      assign (deref z) (borrow x2), copy (deref (deref z))])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrowMut y),
      assign (deref (deref z)) (int 123), copy (deref (deref z))])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (box (borrowMut x)),
      assign (deref (deref y)) (int 123), copy (deref (deref y))])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (int 1)), letMut "y" (borrowMut x),
      assign (deref (deref y)) (int 123), copy (deref (deref y))])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 0), letMut "y" (int 123), letMut "p" (borrowMut x),
      inner [letMut "q" (borrowMut p), assign (deref q) (borrowMut y)], copy (deref p)])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (borrowMut x),
      inner [letMut "z" (borrowMut (deref y)), assign (deref z) (int 123)], copy (deref y)])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrow (deref y)), copy (deref y)])
      (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrowMut (deref y)), copy (deref z)])
      (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (borrow x), letMut "z" (borrow (deref y)), copy (deref z)])
      (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrowMut (deref y)),
      letMut "w" (borrowMut (deref z)), copy (deref w)])
      (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (box (move x)),
      inner [letMut "z" (borrowMut (deref y)), assign (deref z) (int 123)], move (deref y)])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (int 1)),
      inner [letMut "y" (borrowMut (deref x)), assign (deref y) (int 123)], move (deref x)])
      (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (int 1)), letMut "y" (box (borrow (deref x))),
      assign (deref y) (borrow (deref x))]) .unit := by
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
example : invalid (top [letMut "x" (int 123), letMut "y" (borrow x), move y]) := by native_decide
example : invalid (top [inner [letMut "x" (int 123), letMut "y" (borrow x), move y]]) := by native_decide
example : invalid (top [letMut "x" (int 123), letMut "y" (borrow x), inner [move y]]) := by native_decide
example : invalid (top [letMut "x" (int 123), inner [letMut "y" (int 1)], assign y (int 123)]) := by native_decide
example : invalid (top [letMut "x" (box (int 1)), letMut "y" (move x), assign (deref x) (int 123)]) := by native_decide
example : invalid (top [letMut "x" (int 0), assign (deref x) (int 0)]) := by native_decide
example : invalid (top [letMut "x" (box (int 1)), letMut "y" (borrow x), move x, move (deref y)]) := by native_decide
example : invalid (top [letMut "y" (int 123), letMut "z" (box (borrow y)), letMut "x" (move (deref z)), move (deref x)]) := by native_decide
example : invalid (top [letMut "y" (int 123), letMut "z" (box (borrow y)), letMut "x" (copy (deref z)), move (deref x)]) := by native_decide
example : invalid (top [letMut "x" (int 123), letMut "y" (borrow x), letMut "z" (borrowMut x)]) := by native_decide
example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x),
      inner [letMut "w" (int 123), letMut "z" (borrow w), move (deref z)]]) := by
  native_decide
example :
    invalid (top [letMut "x" (int 123), letMut "y" (box (borrowMut x)), letMut "z" (move (deref y)), move (deref z)]) := by
  native_decide
example :
    invalid (top [letMut "x" (int 123), letMut "y" (borrow x), letMut "z" (borrowMut y), move (deref (deref z))]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrow (deref y)), move (deref z)]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrowMut (deref y)),
      letMut "w" (borrowMut (deref z)), move (deref w)]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrowMut (deref y)),
      move (deref y)]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrow (deref y)),
      assign (deref y) (int 2)]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrow (deref y)),
      assign (deref z) (int 2)]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrowMut (deref y)),
      letMut "w" (borrowMut (deref y))]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 0),
      inner [letMut "y" (borrowMut x), assign y (borrowMut (deref y)), assign x (move (deref y))]]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrowMut (deref y)),
      letMut "w" (borrowMut (deref z)), move (deref z)]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrow (deref y)),
      letMut "w" (borrowMut (deref z))]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrowMut (deref y)),
      copy (deref y)]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x), letMut "z" (borrow y),
      letMut "w" (borrowMut (deref (deref z)))]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrow x), letMut "z" (borrowMut y),
      letMut "w" (borrowMut (deref (deref z)))]) := by
  native_decide

example :
    invalid (top [letMut "x1" (int 1), letMut "x2" (int 1), letMut "p" (borrow x1),
      letMut "q" (borrowMut p), assign (deref q) (borrow x2), letMut "w" (borrowMut (deref (deref q)))]) := by
  native_decide

example : invalid (top [letMut "x" (int 0), letMut "y" (borrow x), assign y (borrow (deref y))]) := by
  native_decide

example : invalid (top [letMut "x" (int 0), letMut "y" (borrowMut x), assign y (borrowMut (deref y))]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 0), letMut "y" (borrow x), letMut "z" (borrow (deref y)),
      assign y (borrow (deref z))]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 0), letMut "y" (borrowMut x), letMut "z" (borrowMut (deref y)),
      assign y (borrowMut (deref z))]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 0),
      inner [letMut "p" (borrow x), inner2 [letMut "y" (int 1), assign p (borrow y)]]]) := by
  native_decide

-- TODO: Port the remaining Java `CoreTests`. Most can be expressed directly as
-- AST tests like the cases above; a parser or generator from the Java strings
-- would make the rest less error-prone.

end CoreTests
end Tests
end LwRust
