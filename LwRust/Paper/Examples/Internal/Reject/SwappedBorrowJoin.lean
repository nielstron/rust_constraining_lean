import LwRust.Paper.BorrowChecker

/-!
Compatibility module for the crossed-borrow dereference example.

This example used to be rejected by the assignment-local static authority check.
After removing that check, the executable checker accepts it: the joined target
lists are static over-approximations, while the runtime store contains only the
executed branch's concrete references.
-/

namespace LwRust
namespace Paper

open Core

namespace SwappedBorrowJoinReject

def l : Lifetime := [0]
def m : Lifetime := [0, 0]

def a : LVal := .var "a"
def b : LVal := .var "b"
def c : LVal := .var "c"
def d : LVal := .var "d"
def x : LVal := .var "x"
def y : LVal := .var "y"

def condition : Term := .eq (.copy a) (.copy b)

def trueBranch : Term := .block m [
  .assign x (.borrow true a),
  .assign y (.borrow true b)
]

def falseBranch : Term := .block m [
  .assign x (.borrow true b),
  .assign y (.borrow true a)
]

def derefXAfterIfProgram : Term := .block l [
  .letMut "a" (.val (.int 0)),
  .letMut "b" (.val (.int 0)),
  .letMut "c" (.val (.int 0)),
  .letMut "d" (.val (.int 0)),
  .letMut "x" (.borrow true c),
  .letMut "y" (.borrow true d),
  .ite condition trueBranch falseBranch,
  .assign (.deref x) (.val (.int 1))
]

theorem accepted : borrowCheck derefXAfterIfProgram := by
  borrow_check

theorem checkerTrue : borrowCheck? 256 derefXAfterIfProgram = true := by
  borrow_run

end SwappedBorrowJoinReject

end Paper
end LwRust
