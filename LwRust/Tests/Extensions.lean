import LwRust.Extensions.Tuples
import LwRust.Extensions.ControlFlow
import LwRust.Extensions.Functions

namespace LwRust
namespace Tests
namespace ExtensionTests

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

namespace TupleTests

example : runsTo (top [tuple [int 1, int 2]]) (.tuple [.int 1, .int 2]) := by native_decide
example : runsTo (top [letMut "x" (tuple [int 1, int 2])]) .unit := by native_decide
example : runsTo (top [letMut "x" (tuple [int 1, int 2]), move x]) (.tuple [.int 1, .int 2]) := by native_decide
example : runsTo (top [letMut "x" (int 1), tuple [move x, int 2]]) (.tuple [.int 1, .int 2]) := by native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 2), tuple [move x, move y]]) (.tuple [.int 1, .int 2]) := by
  native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 2), tuple [copy x, move y]]) (.tuple [.int 1, .int 2]) := by
  native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 2), tuple [move x, copy y]]) (.tuple [.int 1, .int 2]) := by
  native_decide
example : runsTo (top [letMut "x" (int 1), letMut "y" (int 2), tuple [copy x, copy y]]) (.tuple [.int 1, .int 2]) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 0, int 0]), assign x (tuple [int 1, int 2]), copy x]) (.tuple [.int 1, .int 2]) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 0, int 0]), assign x (tuple [int 1, int 2]), move x]) (.tuple [.int 1, .int 2]) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (tuple [borrow x, borrow x]),
      letMut "z" (move (field y 0)), copy (deref z)]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (tuple [borrow x, borrow x]),
      letMut "z" (move (field y 1)), copy (deref z)]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (tuple [borrowMut x, int 2]),
      letMut "z" (move (field y 0)), copy (deref z)]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (tuple [borrowMut x, int 2]),
      letMut "z" (move (field y 1)), move z]) (.int 2) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), move (field x 0)]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), copy (field x 1)]) (.int 2) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), copy (field x 0)]) (.int 1) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), move (field x 1)]) (.int 2) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [tuple [int 1, int 2], int 3]), move (field x 0)])
      (.tuple [.int 1, .int 2]) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 3, tuple [int 1, int 2]]), move (field x 1)])
      (.tuple [.int 1, .int 2]) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (borrow (field x 0)), copy (deref y)])
      (.int 1) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (borrow (field x 1)), copy (deref y)])
      (.int 2) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (borrow (field x 0)), copy x])
      (.tuple [.int 1, .int 2]) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (borrow (field x 1)), copy x])
      (.tuple [.int 1, .int 2]) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (borrowMut (field x 0)), move (field x 1)])
      (.int 2) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (borrowMut (field x 1)), move (field x 0)])
      (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [int 0, int 2]), inner [letMut "y" (borrowMut (field x 0)), assign (deref y) (int 1)], move x])
      (.tuple [.int 1, .int 2]) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 0]), inner [letMut "y" (borrowMut (field x 1)), assign (deref y) (int 2)], move x])
      (.tuple [.int 1, .int 2]) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [box (int 1), box (int 2)]), letMut "y" (move (field x 0)), letMut "z" (move (field x 1)), move (deref y)])
      (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [box (int 1), box (int 2)]), letMut "y" (move (field x 0)), letMut "z" (move (field x 1)), move (deref z)])
      (.int 2) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [box (int 1), int 2]), letMut "y" (move (field x 0)), assign (field x 0) (box (int 3)), move (deref (field x 0))])
      (.int 3) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [box (int 0), box (int 2)]), letMut "y" (move (field x 0)),
      assign (field x 0) (box (int 1)), tuple [move (deref (field x 0)), move (deref (field x 1))]])
      (.tuple [.int 1, .int 2]) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [box (int 1), box (int 1)]), letMut "y" (move (field x 1)),
      assign (field x 1) (box (int 2)), tuple [move (deref (field x 0)), move (deref (field x 1))]])
      (.tuple [.int 1, .int 2]) := by
  native_decide
example :
    runsTo (top [letMut "x" (int 1), inner [letMut "y" (tuple [borrow x, borrow x])],
      letMut "z" (borrowMut x), copy (deref z)]) (.int 1) := by
  native_decide
example :
    runsTo (top [letMut "x1" (int 1), letMut "x2" (int 2), letMut "y" (tuple [borrowMut x1, borrowMut x2]),
      letMut "z" (move (field y 0)), letMut "w" (move (field y 1)), copy (deref w)])
      (.int 2) := by
  native_decide
example :
    runsTo (top [letMut "x1" (int 1), letMut "x2" (int 2), letMut "y" (tuple [borrowMut x1, borrowMut x2]),
      letMut "z" (move (field y 0)), letMut "w" (move (field y 1)), copy (deref z)])
      (.int 1) := by
  native_decide
example :
    runsTo (top [letMut "x" (int 1), letMut "y" (tuple [borrowMut x, int 2]),
      letMut "z" (move (field y 0)), move (field y 1)])
      (.int 2) := by
  native_decide
example :
    runsTo (top [letMut "x" (int 1), letMut "y" (tuple [int 2, borrowMut x]),
      letMut "z" (move (field y 1)), move (field y 0)])
      (.int 2) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (copy (field x 0)), move (field x 0)])
      (.int 1) := by
  native_decide
example :
    runsTo (top [letMut "x" (int 1), letMut "y" (tuple [borrowMut x, int 2]),
      letMut "z" (copy (field y 1)), move (field y 1)])
      (.int 2) := by
  native_decide
example :
    runsTo (top [letMut "x" (int 1), letMut "y" (tuple [int 2, borrowMut x]),
      letMut "z" (copy (field y 0)), move (field y 0)])
      (.int 2) := by
  native_decide
example :
    runsTo (top [letMut "x" (tuple [int 0, int 0]), assign (field x 0) (int 1),
      assign (field x 1) (int 2), move x])
      (.tuple [.int 1, .int 2]) := by
  native_decide

example :
    invalid (top [letMut "x" (tuple [box (int 1), box (int 2)]), letMut "y" (move (field x 0)), move x]) := by
  native_decide
example : invalid (top [letMut "x" (tuple [move x, int 1])]) := by native_decide
example : invalid (top [letMut "x" (tuple [int 1, move x])]) := by native_decide
example : invalid (top [letMut "x" (box (int 1)), tuple [move x, move x]]) := by native_decide
example : invalid (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (move (field x 0)), move (field x 0)]) := by
  native_decide
example : invalid (top [letMut "x" (tuple [int 1, int 2]), assign x (int 1)]) := by native_decide
example : invalid (top [letMut "x" (int 1), assign x (tuple [int 1, int 2])]) := by native_decide
example : invalid (top [letMut "x" (int 0), letMut "y" (tuple [borrowMut x, borrowMut x])]) := by native_decide
example : invalid (top [letMut "x" (int 1), letMut "y" (tuple [borrow x, borrow x]),
  letMut "z" (move (field y 0)), move (deref z)]) := by
  native_decide
example : invalid (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (borrow (field x 0)), move (deref y)]) := by
  native_decide
example : invalid (top [letMut "x" (int 0), letMut "y" (tuple [borrowMut x, int 1]), letMut "z" (borrowMut x)]) := by
  native_decide
example : invalid (top [letMut "x" (int 0), letMut "y" (tuple [int 1, borrowMut x]), letMut "z" (borrowMut x)]) := by
  native_decide
example : invalid (top [letMut "x" (tuple [int 0, int 0]), letMut "y" (borrowMut (field x 0)), move x]) := by
  native_decide
example : invalid (top [letMut "x" (tuple [int 0, int 0]), letMut "y" (borrowMut (field x 1)), move x]) := by
  native_decide
example :
    invalid (top [letMut "x" (tuple [box (int 1), box (int 2)]), letMut "y" (move (field x 0)),
      letMut "z" (move (field x 0))]) := by
  native_decide
example :
    invalid (top [letMut "x" (tuple [box (int 1), box (int 2)]), letMut "y" (move (field x 1)),
      letMut "z" (move (field x 1))]) := by
  native_decide
example : invalid (top [letMut "x" (tuple [int 1, int 2]), letMut "y" (move (field x 2))]) := by
  native_decide
example : invalid (top [letMut "x" (tuple [int 1, int 2, int 3]), letMut "y" (move (field x 3))]) := by
  native_decide
example :
    invalid (top [letMut "x1" (int 1), letMut "x2" (int 2), letMut "y" (tuple [borrowMut x1, borrowMut x2]),
      letMut "z" (move (field y 0)), letMut "w" (move (field y 1)), move (deref w)]) := by
  native_decide
example :
    invalid (top [letMut "x1" (int 1), letMut "x2" (int 2), letMut "y" (tuple [borrowMut x1, borrowMut x2]),
      letMut "z" (move (field y 0)), letMut "w" (move (field y 1)), move (deref z)]) := by
  native_decide

-- TODO: Port the remaining `TupleTests.java` cases. Parser-level forms such
-- as copying a tuple expression directly, e.g. `!(x,y)`, do not yet have a
-- source AST counterpart in this Lean translation.

end TupleTests

namespace ControlFlowTests

def condX := temp x
def condY := temp y
def alt (terms : List Term) : Term := block [0, 1] terms
def branchL (terms : List Term) : Term := block [0, 0, 0] terms
def branchR (terms : List Term) : Term := block [0, 0, 1] terms

example :
    runsTo (top [letMut "x" (int 1), ifEq condX condX (inner [int 1]) (block [0, 1] [int 2])]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 1), ifEq condX condY (inner [int 1]) (alt [int 2])])
      (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 2), ifEq condX condY (inner [int 1]) (block [0, 1] [int 2])]) (.int 2) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 1), letMut "z" (borrow y),
      ifEq condX condX (inner [assign z (borrow x)]) (alt [assign z (borrow x)])]) .unit := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 1), letMut "z" (borrow y),
      ifEq condX condX (inner [assign z (borrow x)]) (alt [])]) .unit := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 2), letMut "p" (borrow x),
      ifEq condX condX (inner [assign p (borrow y)]) (block [0, 1] []),
      copy (deref p)]) (.int 2) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (int 1)),
      ifEq (temp (deref x)) (temp (deref x)) (inner [assign x (box (int 2))]) (block [0, 1] [assign x (box (int 3))]),
      move (deref x)]) (.int 2) := by
  native_decide

example :
    runsTo (top [letMut "x" (box (int 3)),
      ifNe (temp (deref x)) (temp (deref x)) (inner [assign x (box (int 2))]) (alt [assign x (box (int 1))]),
      move (deref x)]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (ifEq condX condX (inner []) (alt []))]) .unit := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (box (int 1)),
      ifEq condX condX (inner [letMut "p" (move (deref y))]) (alt [letMut "q" (move (deref y))]),
      assign (deref y) (int 1)]) .unit := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 1), letMut "z" (box (borrowMut x)),
      ifEq condY condY (inner [letMut "p" (move (deref z))]) (alt [letMut "q" (move (deref z))]),
      assign (deref z) (borrowMut y)]) .unit := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "p" (borrow x), letMut "q" (borrow x),
      ifEq (temp (deref p)) (temp (deref q)) (inner [int 1]) (block [0, 1] [int 2])]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 2), letMut "p" (borrow x),
      ifEq condX condX (inner [assign p (borrow y)]) (block [0, 1] []),
      copy (deref p)]) (.int 2) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 2), letMut "p" (borrow x),
      ifNe condX condX (inner []) (block [0, 1] [assign p (borrow y)]),
      copy (deref p)]) (.int 2) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 2),
      inner [letMut "p" (borrowMut x),
        ifEq condY condY (branchL [assign p (borrowMut y)]) (branchR []),
        assign (deref p) (int 123)],
      move x]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 2),
      inner [letMut "p" (borrowMut x),
        ifEq condY condY (branchL [assign p (borrowMut y)]) (branchR []),
        assign (deref p) (int 123)],
      move y]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 2),
      inner [letMut "p" (borrowMut x),
        ifNe condY condY (branchL [assign p (borrowMut y)]) (branchR []),
        assign (deref p) (int 123)],
      move x]) (.int 123) := by
  native_decide

example :
    runsTo (top [letMut "a" (int 1), letMut "x" (int 2), letMut "y" (int 3),
      letMut "p" (borrowMut x), letMut "q" (borrowMut y),
      ifEq (temp (var "a")) (temp (var "a")) (inner [assign p (borrowMut (var "a"))]) (alt [assign q (borrowMut (var "a"))])])
      .unit := by
  native_decide

example : invalid (top [ifEq condX condX (inner []) (block [0, 1] [])]) := by native_decide
example :
    invalid (top [letMut "x" (int 1), ifEq condX condX (inner []) (block [0, 1] [int 1])]) := by
  native_decide
example :
    invalid (top [letMut "x" (int 1), ifEq condX condX (inner [borrow x]) (block [0, 1] [])]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (int 2), letMut "p" (borrow x),
      ifEq condX condX (inner [assign p (borrow y)]) (block [0, 1] []),
      move (deref p)]) := by
  native_decide
example :
    invalid (top [letMut "x" (int 1), letMut "y" (int 2), letMut "z" (borrow y),
      ifNe condX condX (inner [assign z (borrow x)]) (alt []), letMut "w" (move (deref z)), move w]) := by
  native_decide
example : invalid (top [letMut "x" (int 1), ifEq condX (temp y) (inner []) (alt [])]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x),
      ifEq (move y) (borrowMut x) (inner []) (alt [])]) := by
  native_decide

example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner []) (alt [box (int 1)])]) := by
  native_decide

example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner [int 1]) (alt [])]) := by
  native_decide
example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner []) (alt [int 1])]) := by
  native_decide
example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner [borrow x]) (alt [int 1])]) := by
  native_decide
example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner [borrow x]) (alt [borrowMut x])]) := by
  native_decide
example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner [borrow x]) (alt [box (int 1)])]) := by
  native_decide
example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner [box (int 1)]) (alt [])]) := by
  native_decide
example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner [box (int 1)]) (alt [int 1])]) := by
  native_decide
example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner [box (int 1)]) (alt [borrow x])]) := by
  native_decide
example : invalid (top [letMut "x" (int 1), ifEq condX condX (inner [box (int 1)]) (alt [borrowMut x])]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (box (int 1)),
      ifEq condX condX (inner [letMut "p" (move y)]) (alt [letMut "q" (move y)]),
      assign (deref y) (box (int 1))]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (box (int 1)),
      ifEq condX condX (inner []) (alt [letMut "q" (move y)]), move (deref y)]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (box (int 1)),
      ifEq condX condX (inner [letMut "p" (move y)]) (alt []), move (deref y)]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (int 2), letMut "p" (borrowMut x),
      ifEq condY condY (inner [assign p (borrow y)]) (alt [])]) := by
  native_decide
example :
    invalid (top [letMut "x" (int 1), letMut "p" (borrow x),
      ifEq condX condX (inner [letMut "y" (int 2), assign p (borrow y)]) (alt [])]) := by
  native_decide

example :
    invalid (top [letMut "x" (int 1), letMut "y" (borrowMut x),
      ifEq (borrowMut x) (move y) (inner []) (alt [])]) := by
  native_decide

example : invalid (top [letMut "x" (int 1), ifEq (borrowMut x) (borrowMut x) (inner []) (alt [])]) := by
  native_decide

example :
    invalid (top [letMut "x1" (int 1), letMut "x2" (int 2),
      letMut "y1" (borrowMut x1), letMut "y2" (borrowMut x2),
      ifEq (move (var "y1")) (move (var "y2")) (inner []) (alt [])]) := by
  native_decide

example :
    invalid (top [letMut "x1" (box (int 1)), ifEq (move x1) (move x1) (inner []) (alt [])]) := by
  native_decide
example :
    invalid (top [letMut "x1" (box (int 1)), letMut "x2" (box (int 2)),
      ifEq (move x1) (move x2) (inner []) (alt [])]) := by
  native_decide
example :
    invalid (top [letMut "x" (int 1), letMut "y" (int 1),
      ifEq (borrowMut x) (borrowMut y) (inner [int 1]) (alt [int 2])]) := by
  native_decide
example :
    invalid (top [letMut "x" (int 1), letMut "y" (int 1),
      ifEq (borrowMut x) (borrowMut y) (inner [int 1]) (alt [int 2]), move x]) := by
  native_decide
example :
    invalid (top [letMut "x" (int 1), letMut "q" (borrowMut x),
      inner [letMut "y" (int 2), ifEq (temp y) (temp y) (branchL []) (branchR [assign q (borrowMut y)])],
      copy (deref q)]) := by
  native_decide

-- TODO: The Java parser's temporary-access marking is represented manually
-- here with `temp`; a parser translation would remove this manual annotation.

end ControlFlowTests

namespace FunctionTests

open LwRust.Extensions.Functions

def call := LwRust.Extensions.Functions.invoke

def fnRunsToBool (decls : List FunctionDeclaration) (program : Term) (value : Value) : Bool :=
  match LwRust.Extensions.Functions.execute decls program with
  | Except.ok actual => actual == value
  | Except.error _ => false

abbrev fnRunsTo (decls : List FunctionDeclaration) (program : Term) (value : Value) : Prop :=
  fnRunsToBool decls program value = true

def fnInvalidBool (decls : List FunctionDeclaration) (program : Term) : Bool :=
  match LwRust.Extensions.Functions.checkProgram decls program with
  | Except.ok _ => false
  | Except.error _ => true

abbrev fnInvalid (decls : List FunctionDeclaration) (program : Term) : Prop :=
  fnInvalidBool decls program = true

def fnBody (terms : List Term) : Term := block [1] terms

def fConst : FunctionDeclaration :=
  { name := "f", params := [], ret := .int, body := fnBody [int 1] }

def fConstParam : FunctionDeclaration :=
  { name := "f", params := [("x", .int)], ret := .int, body := fnBody [int 1] }

def idInt : FunctionDeclaration :=
  { name := "id", params := [("x", .int)], ret := .int, body := fnBody [move (var "x")] }

def selFirst : FunctionDeclaration :=
  { name := "sel", params := [("x", .int), ("y", .int)], ret := .int, body := fnBody [move (var "x")] }

def selSecond : FunctionDeclaration :=
  { name := "sel", params := [("x", .int), ("y", .int)], ret := .int, body := fnBody [move (var "y")] }

def idBoxInt : FunctionDeclaration :=
  { name := "id", params := [("x", .box .int)], ret := .box .int, body := fnBody [move (var "x")] }

def idBorrowInt : FunctionDeclaration :=
  { name := "id", params := [("x", .borrow false "a" .int)], ret := .borrow false "a" .int,
    body := fnBody [move (var "x")] }

def idMutBorrowInt : FunctionDeclaration :=
  { name := "id", params := [("x", .borrow true "a" .int)], ret := .borrow true "a" .int,
    body := fnBody [move (var "x")] }

def idBorrowBorrowInt : FunctionDeclaration :=
  { name := "id", params := [("x", .borrow false "a" (.borrow false "b" .int))],
    ret := .borrow false "a" (.borrow false "b" .int),
    body := fnBody [move (var "x")] }

def idMutBorrowBorrowInt : FunctionDeclaration :=
  { name := "id", params := [("x", .borrow true "a" (.borrow false "b" .int))],
    ret := .borrow true "a" (.borrow false "b" .int),
    body := fnBody [move (var "x")] }

def idBoxBorrowInt : FunctionDeclaration :=
  { name := "id", params := [("x", .box (.borrow false "a" .int))],
    ret := .box (.borrow false "a" .int),
    body := fnBody [move (var "x")] }

def idBoxMutBorrowInt : FunctionDeclaration :=
  { name := "id", params := [("x", .box (.borrow true "a" .int))],
    ret := .box (.borrow true "a" .int),
    body := fnBody [move (var "x")] }

def idTupleInt : FunctionDeclaration :=
  { name := "id", params := [("x", .tuple [.int, .int])], ret := .tuple [.int, .int],
    body := fnBody [move (var "x")] }

def firstTupleInt : FunctionDeclaration :=
  { name := "first", params := [("x", .tuple [.int, .int])], ret := .int,
    body := fnBody [move (field (var "x") 0)] }

def boxToInt : FunctionDeclaration :=
  { name := "id", params := [("x", .box .int)], ret := .int,
    body := fnBody [copy (deref (var "x"))] }

def boxMutBorrowToMutBorrow : FunctionDeclaration :=
  { name := "id", params := [("x", .box (.borrow true "a" .int))], ret := .borrow true "a" .int,
    body := fnBody [move (deref (var "x"))] }

def returnMutSecond : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow true "a" .int), ("y", .borrow true "b" .int)],
    ret := .borrow true "b" .int,
    body := fnBody [move (var "y")] }

def returnMutFirst : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow true "a" .int), ("y", .borrow true "b" .int)],
    ret := .borrow true "a" .int,
    body := fnBody [move (var "x")] }

def sideEffectImmFromMut : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow true "a" (.borrow false "b" .int)), ("y", .borrow true "b" .int)],
    ret := .unit,
    body := fnBody [] }

def writeBoxInt : FunctionDeclaration :=
  { name := "write", params := [("x", .box .int)], ret := .unit,
    body := fnBody [assign (deref (var "x")) (int 1)] }

def writeMutInt : FunctionDeclaration :=
  { name := "write", params := [("x", .borrow true "a" .int)], ret := .unit,
    body := fnBody [assign (deref (var "x")) (int 1)] }

def sideEffectImmFromImm : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow true "a" (.borrow false "b" .int)), ("y", .borrow false "b" .int)],
    ret := .unit,
    body := fnBody [] }

def sideEffectMutFromMut : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow true "a" (.borrow true "b" .int)), ("y", .borrow true "b" .int)],
    ret := .unit,
    body := fnBody [] }

def assignBorrowParam : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow false "a" .int), ("y", .borrow false "a" .int)],
    ret := .unit,
    body := fnBody [assign (var "x") (move (var "y"))] }

def assignMutBorrowParam : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow true "a" .int), ("y", .borrow true "a" .int)],
    ret := .unit,
    body := fnBody [assign (var "x") (move (var "y"))] }

def writeNestedBorrowParam : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow true "a" (.borrow false "b" .int)), ("y", .borrow false "b" .int)],
    ret := .unit,
    body := fnBody [assign (deref (var "x")) (move (var "y"))] }

def nestedParameterWitness : FunctionDeclaration :=
  { name := "f",
    params := [("x", .borrow true "a" (.borrow false "b" .int)), ("y", .borrow false "c" .int),
      ("z", .borrow false "b" (.borrow false "c" .int))],
    ret := .unit,
    body := fnBody [] }

def badUnknownBody : FunctionDeclaration :=
  { name := "id", params := [("x", .int)], ret := .int,
    body := fnBody [move (var "y")] }

def badReturnBox : FunctionDeclaration :=
  { name := "id", params := [("x", .int)], ret := .box .int, body := fnBody [move (var "x")] }

def badReturnBorrow : FunctionDeclaration :=
  { name := "id", params := [("x", .int)], ret := .borrow false "a" .int,
    body := fnBody [move (var "x")] }

def badReturnMutBorrow : FunctionDeclaration :=
  { name := "id", params := [("x", .int)], ret := .borrow true "a" .int,
    body := fnBody [move (var "x")] }

def badImmToMutReturn : FunctionDeclaration :=
  { name := "id", params := [("x", .borrow false "a" .int)], ret := .borrow true "a" .int,
    body := fnBody [move (var "x")] }

def badLocalBorrowReturn : FunctionDeclaration :=
  { name := "id", params := [("x", .borrow false "a" .int)], ret := .borrow false "a" .int,
    body := fnBody [letMut "y" (int 0), borrow (var "y")] }

def badLocalMutBorrowReturn : FunctionDeclaration :=
  { name := "id", params := [("x", .borrow true "a" .int)], ret := .borrow true "a" .int,
    body := fnBody [letMut "y" (int 0), borrowMut (var "y")] }

def badReturnMutDifferentLifetime : FunctionDeclaration :=
  { name := "id", params := [("x", .borrow true "a" .int)], ret := .borrow true "b" .int,
    body := fnBody [move (var "x")] }

def badReturnNestedMutDifferentLifetime : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow true "a" (.borrow false "b" .int))],
    ret := .borrow true "a" (.borrow false "a" .int),
    body := fnBody [move (var "x")] }

def badLocalSideEffect : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow true "a" (.borrow false "b" .int))], ret := .unit,
    body := fnBody [letMut "y" (int 0), assign (deref (var "x")) (borrow (var "y"))] }

def badSharedReturnMutSecond : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow false "a" .int), ("y", .borrow true "a" .int)],
    ret := .borrow true "a" .int,
    body := fnBody [move (var "y")] }

def badSharedReturnFirst : FunctionDeclaration :=
  { name := "f", params := [("x", .borrow false "a" .int), ("y", .borrow true "a" .int)],
    ret := .borrow false "a" .int,
    body := fnBody [move (var "x")] }

example : fnRunsTo [fConst] (top [call "f" []]) (.int 1) := by native_decide

example :
    fnRunsTo [fConstParam] (top [letMut "a" (int 1), call "f" [move (var "a")]]) (.int 1) := by
  native_decide

example : fnRunsTo [idInt] (top [call "id" [int 1]]) (.int 1) := by native_decide

example : fnRunsTo [selFirst] (top [call "sel" [int 1, int 2]]) (.int 1) := by native_decide

example : fnRunsTo [selSecond] (top [call "sel" [int 1, int 2]]) (.int 2) := by native_decide

example :
    fnRunsTo [idInt] (top [letMut "x" (int 2), call "id" [int 1], move (var "x")]) (.int 2) := by
  native_decide

example :
    fnRunsTo [idBoxInt] (top [letMut "p" (call "id" [box (int 1)]), move (deref (var "p"))]) (.int 1) := by
  native_decide

example :
    fnRunsTo [idBorrowInt]
      (top [letMut "v" (int 1), letMut "p" (call "id" [borrow (var "v")]), copy (deref (var "p"))])
      (.int 1) := by
  native_decide

example :
    fnRunsTo [idMutBorrowInt]
      (top [letMut "v" (int 1), letMut "p" (call "id" [borrowMut (var "v")]), copy (deref (var "p"))])
      (.int 1) := by
  native_decide

example :
    fnRunsTo [idBorrowBorrowInt]
      (top [letMut "v" (int 1), letMut "u" (borrow (var "v")), letMut "p" (call "id" [borrow (var "u")]),
        copy (deref (deref (var "p")))])
      (.int 1) := by
  native_decide

example :
    fnRunsTo [idMutBorrowBorrowInt]
      (top [letMut "v" (int 1), letMut "u" (borrow (var "v")), letMut "p" (call "id" [borrowMut (var "u")]),
        copy (deref (deref (var "p")))])
      (.int 1) := by
  native_decide

example : fnRunsTo [idBoxBorrowInt] (top [int 1]) (.int 1) := by native_decide

example : fnRunsTo [idBoxMutBorrowInt] (top [int 1]) (.int 1) := by native_decide

example : fnRunsTo [idTupleInt] (top [call "id" [tuple [int 1, int 2]]]) (.tuple [.int 1, .int 2]) := by
  native_decide

example : fnRunsTo [firstTupleInt] (top [call "first" [tuple [int 1, int 2]]]) (.int 1) := by
  native_decide

example : fnRunsTo [boxToInt] (top [int 1]) (.int 1) := by native_decide

example : fnRunsTo [boxMutBorrowToMutBorrow] (top [int 1]) (.int 1) := by native_decide

example :
    fnRunsTo [returnMutSecond]
      (top [letMut "u" (int 1), letMut "v" (int 2),
        letMut "w" (call "f" [borrowMut (var "u"), borrowMut (var "v")]),
        letMut "a" (borrowMut (var "u"))])
      .unit := by
  native_decide

example :
    fnRunsTo [returnMutFirst]
      (top [letMut "u" (int 1), letMut "v" (int 2),
        letMut "w" (call "f" [borrowMut (var "u"), borrowMut (var "v")]),
        letMut "a" (borrowMut (var "v"))])
      .unit := by
  native_decide

example :
    fnRunsTo [assignBorrowParam] (top [letMut "u" (int 1), call "f" [borrow (var "u"), borrow (var "u")]])
      .unit := by
  native_decide

example :
    fnRunsTo [assignMutBorrowParam]
      (top [letMut "u" (int 1), letMut "v" (int 2), call "f" [borrowMut (var "u"), borrowMut (var "v")]])
      .unit := by
  native_decide

example :
    fnRunsTo [writeNestedBorrowParam]
      (top [letMut "x" (int 0),
        block [0, 0] [letMut "y" (int 1),
          block [0, 0, 0] [letMut "p" (borrow (var "y")), call "f" [borrowMut (var "p"), borrow (var "x")]]]])
      .unit := by
  native_decide

example :
    fnRunsTo [nestedParameterWitness]
      (top [letMut "u" (int 1),
        block [0, 0] [letMut "v" (int 2), letMut "p" (borrow (var "u")),
          block [0, 0, 0] [letMut "q" (borrow (var "v")),
            letMut "w" (call "f" [borrowMut (var "q"), borrow (var "u"), borrow (var "p")])]]])
      .unit := by
  native_decide

example : fnRunsTo [writeBoxInt] (top [call "write" [box (int 0)]]) .unit := by native_decide

example :
    fnRunsTo [writeMutInt]
      (top [letMut "v" (int 0), call "write" [borrowMut (var "v")], move (var "v")]) (.int 1) := by
  native_decide

example :
    fnRunsTo [sideEffectImmFromMut]
      (top [letMut "u" (int 1), letMut "v" (int 2), letMut "p" (borrow (var "u")),
        letMut "w" (call "f" [borrowMut (var "p"), borrowMut (var "v")]),
        letMut "a" (borrowMut (var "v"))])
      .unit := by
  native_decide

example : fnInvalid [] (top [call "missing" []]) := by native_decide

example : fnInvalid [idInt] (top [call "id" []]) := by native_decide

example : fnInvalid [idInt] (top [call "id" [int 1, int 2]]) := by native_decide

example : fnInvalid [idInt] (top [letMut "x" (box (int 1)), call "id" [move (var "x")]]) := by native_decide

example : fnInvalid [idTupleInt] (top [call "id" [tuple [int 1, box (int 2)]]]) := by native_decide

example : fnInvalid [badUnknownBody] (top []) := by native_decide

example :
    fnInvalid [returnMutSecond]
      (top [letMut "u" (int 1), letMut "v" (int 2),
        letMut "w" (call "f" [borrowMut (var "u"), borrowMut (var "v")]),
        letMut "a" (borrowMut (var "v"))]) := by
  native_decide

example :
    fnInvalid [returnMutFirst]
      (top [letMut "u" (int 1), letMut "v" (int 2),
        letMut "w" (call "f" [borrowMut (var "u"), borrowMut (var "v")]),
        letMut "a" (borrowMut (var "u"))]) := by
  native_decide

example :
    fnInvalid [sideEffectImmFromImm]
      (top [letMut "u" (int 1), letMut "v" (int 2), letMut "p" (borrow (var "u")),
        letMut "w" (call "f" [borrowMut (var "p"), borrow (var "v")]),
        letMut "a" (borrowMut (var "v"))]) := by
  native_decide

example :
    fnInvalid [sideEffectImmFromImm]
      (top [letMut "u" (int 1), letMut "v" (int 2), letMut "p" (borrow (var "u")),
        letMut "w" (call "f" [borrowMut (var "p"), borrow (var "v")]),
        letMut "a" (borrowMut (var "u"))]) := by
  native_decide

example :
    fnInvalid [sideEffectMutFromMut]
      (top [letMut "u" (int 1), letMut "v" (int 2), letMut "p" (borrowMut (var "u")),
        letMut "w" (call "f" [borrowMut (var "p"), borrowMut (var "v")]),
        letMut "a" (borrowMut (var "v"))]) := by
  native_decide

example :
    fnInvalid [sideEffectMutFromMut]
      (top [letMut "u" (int 1), letMut "v" (int 2), letMut "p" (borrowMut (var "u")),
        letMut "w" (call "f" [borrowMut (var "p"), borrowMut (var "v")]),
        letMut "a" (borrowMut (var "u"))]) := by
  native_decide

example : fnInvalid [badReturnBox] (top []) := by native_decide
example : fnInvalid [badReturnBorrow] (top []) := by native_decide
example : fnInvalid [badReturnMutBorrow] (top []) := by native_decide
example : fnInvalid [badImmToMutReturn] (top []) := by native_decide
example : fnInvalid [badLocalBorrowReturn] (top []) := by native_decide
example : fnInvalid [badLocalMutBorrowReturn] (top []) := by native_decide
example : fnInvalid [badReturnMutDifferentLifetime] (top []) := by native_decide
example : fnInvalid [badReturnNestedMutDifferentLifetime] (top []) := by native_decide
example : fnInvalid [badLocalSideEffect] (top []) := by native_decide

example :
    fnInvalid [badSharedReturnMutSecond]
      (top [letMut "u" (int 1), letMut "v" (int 2),
        letMut "w" (call "f" [borrow (var "u"), borrowMut (var "v")]),
        letMut "a" (borrowMut (var "v"))]) := by
  native_decide

example :
    fnInvalid [badSharedReturnFirst]
      (top [letMut "u" (int 1), letMut "v" (int 2),
        letMut "w" (call "f" [borrow (var "u"), borrowMut (var "v")]),
        letMut "a" (borrowMut (var "u"))]) := by
  native_decide

example :
    fnInvalid [writeNestedBorrowParam]
      (top [letMut "x" (int 0),
        block [0, 0] [letMut "p" (borrow (var "x")),
          block [0, 0, 0] [letMut "y" (int 1), call "f" [borrowMut (var "p"), borrow (var "y")]]]]) := by
  native_decide

example :
    fnInvalid [writeNestedBorrowParam]
      (top [letMut "x" (int 0),
        block [0, 0] [letMut "y" (int 1),
          block [0, 0, 0] [letMut "p" (borrow (var "x")), call "f" [borrowMut (var "p"), borrow (var "y")]]]]) := by
  native_decide

-- TODO: Port the remaining `FunctionTests.java` lifetime-polymorphism cases
-- after `Functions.java`'s full subtype-driven `bind`/`lift` machinery is
-- translated.

end FunctionTests

end ExtensionTests
end Tests
end LwRust
