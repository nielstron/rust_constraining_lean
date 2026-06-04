import LwRust.CompleteProgram

/-!
Function extension syntax boundary.

Java source: `FeatherweightRust/src/featherweightrust/extensions/Functions.java`.

TODO: Function signatures, lifetime instantiation, subtyping/supertyping, and
call-frame operational semantics have not yet been adequately translated. The
core AST contains `Term.invoke` so programs using calls are represented, but
`BorrowChecker.checkTerm` and `OperationalSemantics.eval` deliberately reject
invocation with TODO errors until the Java `Functions.Checker` and
`Functions.Semantics` logic is translated.
-/

namespace LwRust
namespace Extensions
namespace Functions

open Core

inductive Signature where
  | unit
  | int
  | borrow (mutable : Bool) (lifetimeName : String) (sig : Signature)
  | box (sig : Signature)
  | tuple (fields : List Signature)
  deriving BEq, Repr

structure FunctionDeclaration where
  name : Name
  params : List (Name × Signature)
  ret : Signature
  body : Term
  deriving BEq, Repr

def invoke := CompleteProgram.invoke

end Functions
end Extensions
end LwRust
