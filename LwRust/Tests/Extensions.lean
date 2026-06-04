import LwRust.Extensions.Tuples
import LwRust.Extensions.ControlFlow
import LwRust.Extensions.Functions

namespace LwRust
namespace Tests
namespace ExtensionTests

open Core
open CompleteProgram

def x := var "x"
def y := var "y"
def z := var "z"
def p := var "p"

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

namespace TupleTests

example : runsTo (top [tuple [int 1, int 2]]) (.tuple [.int 1, .int 2]) := by native_decide
example : runsTo (top [letMut "x" (tuple [int 1, int 2]), move x]) (.tuple [.int 1, .int 2]) := by native_decide
example : runsTo (top [letMut "x" (int 1), tuple [move x, int 2]]) (.tuple [.int 1, .int 2]) := by native_decide
example :
    runsTo (top [letMut "x" (tuple [int 0, int 0]), assign x (tuple [int 1, int 2]), copy x]) (.tuple [.int 1, .int 2]) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), move (field x 0)]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [int 1, int 2]), copy (field x 1)]) (.int 2) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [int 0, int 2]), inner [letMut "y" (borrowMut (field x 0)), assign (deref y) (int 1)], move x])
      (.tuple [.int 1, .int 2]) := by
  native_decide

example :
    runsTo (top [letMut "x" (tuple [box (int 1), box (int 2)]), letMut "y" (move (field x 0)), letMut "z" (move (field x 1)), move (deref y)])
      (.int 1) := by
  native_decide

example :
    invalid (top [letMut "x" (tuple [box (int 1), box (int 2)]), letMut "y" (move (field x 0)), move x]) := by
  native_decide

-- TODO: Port the rest of `TupleTests.java`; in particular, cases involving
-- mutable borrows inside tuples should be exhaustively mirrored after the
-- runtime tuple-null TODO is resolved.

end TupleTests

namespace ControlFlowTests

def condX := temp x
def condY := temp y

example :
    runsTo (top [letMut "x" (int 1), ifEq condX condX (inner [int 1]) (block [0, 1] [int 2])]) (.int 1) := by
  native_decide

example :
    runsTo (top [letMut "x" (int 1), letMut "y" (int 2), ifEq condX condY (inner [int 1]) (block [0, 1] [int 2])]) (.int 2) := by
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

example : invalid (top [ifEq condX condX (inner []) (block [0, 1] [])]) := by native_decide
example :
    invalid (top [letMut "x" (int 1), ifEq condX condX (inner []) (block [0, 1] [int 1])]) := by
  native_decide
example :
    invalid (top [letMut "x" (int 1), ifEq condX condX (inner [borrow x]) (block [0, 1] [])]) := by
  native_decide

-- TODO: Port all remaining `ControlFlowTests.java` cases. The Java parser's
-- temporary-access marking is represented manually here with `temp`.

end ControlFlowTests

namespace FunctionTests

def functionTodoBool : Bool :=
  match check (top [LwRust.Extensions.Functions.invoke "f" []]) with
  | Except.error msg => msg == "TODO functions extension typing is not adequately translated yet"
  | Except.ok _ => false

example :
    functionTodoBool = true := by
  native_decide

-- TODO: Translate `FunctionTests.java` after `Functions.java` signatures,
-- declaration environments, and invocation semantics are implemented.

end FunctionTests

end ExtensionTests
end Tests
end LwRust
