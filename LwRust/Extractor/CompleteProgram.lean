import LwRust.Paper.Syntax

/-!
Complete LwRust programs for the extractor development.

This mainly defines a syntax for complete LwRust programs
so that we can derive partial programs from them.
-/

namespace ConservativeExtractor

abbrev Name := LwRust.Core.Name
abbrev Lifetime := LwRust.Core.Lifetime
abbrev LVal := LwRust.Core.LVal
abbrev Location := LwRust.Core.Location
abbrev Ty := LwRust.Core.Ty
abbrev Value := LwRust.Core.Value
abbrev Reference := LwRust.Core.Reference
abbrev Term := LwRust.Core.Term
abbrev Program := Term

namespace CompleteDsl

def tyUnit : Ty := .unit
def tyInt : Ty := .int
def tyBool : Ty := .bool
def tyBorrow (mutable : Bool) (targets : List LVal) (pointee : Ty) : Ty :=
  .borrow mutable targets pointee
def tyBox (element : Ty) : Ty := .box element

def lvalVar (x : Name) : LVal := .var x
def lvalDeref (operand : LVal) : LVal := .deref operand

def unit : Term := .val .unit
def int (n : Int) : Term := .val (.int n)
def bool (b : Bool) : Term := .val (.bool b)
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
def eq (lhs rhs : Term) : Term := .eq lhs rhs
def ite (condition trueBranch falseBranch : Term) : Term :=
  .ite condition trueBranch falseBranch

end CompleteDsl

/-!
Object-language syntax declarations used by the partial-program generator.
They intentionally mirror the constructors of `LwRust.Core`.
-/

declare_syntax_cat cty
declare_syntax_cat clval
declare_syntax_cat cterm

syntax (name := ctyUnit) "cty_unit" : cty
syntax (name := ctyInt) "cty_int" : cty
syntax (name := ctyBool) "cty_bool" : cty
syntax (name := ctyBorrowShared) "&" "[" clval,* "]" : cty
syntax (name := ctyBorrowMut) "&" "mut" "[" clval,* "]" : cty
syntax (name := ctyBox) "box" cty : cty

syntax (name := clvalVar) ident : clval
syntax (name := clvalDeref) "*" clval : clval

syntax (name := ctermUnit) "()" : cterm
syntax (name := ctermInt) num : cterm
syntax (name := ctermTrue) "true" : cterm
syntax (name := ctermFalse) "false" : cterm
syntax (name := ctermBlock) "block" term "{" cterm,* "}" : cterm
syntax (name := ctermLetMut) "let" "mut" ident ":=" cterm : cterm
syntax (name := ctermAssign) clval ":=" cterm : cterm
syntax (name := ctermBox) "box" cterm : cterm
syntax (name := ctermBorrowShared) "&" clval : cterm
syntax (name := ctermBorrowMut) "&" "mut" clval : cterm
syntax (name := ctermMove) clval : cterm
syntax (name := ctermCopy) "copy" clval : cterm
syntax (name := ctermEq) cterm "==" cterm : cterm
syntax (name := ctermIte) "if" cterm cterm "else" cterm : cterm
syntax (name := ctermWhile) "while" term cterm cterm : cterm

/-!
Checked constructor annotations for the generator.

The generator derives partial syntax from the `syntax` declarations above and
reads these `_ctor` abbreviations for the corresponding complete AST shape.
Keeping this information in Lean, instead of in the Python script, makes stale
constructor references fail during the Lean build.
-/

namespace SyntaxCtor

abbrev ctyUnit_ctor : Ty :=
  show Ty from .unit

abbrev ctyInt_ctor : Ty :=
  show Ty from .int

abbrev ctyBool_ctor : Ty :=
  show Ty from .bool

abbrev ctyBorrowShared_ctor (targets : List LVal) : Ty :=
  LwRust.Core.Ty.borrow Bool.false targets .unit

abbrev ctyBorrowMut_ctor (targets : List LVal) : Ty :=
  LwRust.Core.Ty.borrow Bool.true targets .unit

abbrev ctyBox_ctor (element : Ty) : Ty :=
  show Ty from (.box element)

abbrev clvalVar_ctor (x : Name) : LVal :=
  show LVal from (.var x)

abbrev clvalDeref_ctor (operand : LVal) : LVal :=
  show LVal from (.deref operand)

abbrev ctermUnit_ctor : Term :=
  show Term from .val .unit

abbrev ctermInt_ctor (n : Int) : Term :=
  show Term from (.val (.int n))

abbrev ctermTrue_ctor : Term :=
  LwRust.Core.Term.val (LwRust.Core.Value.bool Bool.true)

abbrev ctermFalse_ctor : Term :=
  LwRust.Core.Term.val (LwRust.Core.Value.bool Bool.false)

abbrev ctermBlock_ctor (lifetime : Lifetime) (terms : List Term) : Term :=
  show Term from (.block lifetime terms)

abbrev ctermLetMut_ctor (name : Name) (initialiser : Term) : Term :=
  show Term from (.letMut name initialiser)

abbrev ctermAssign_ctor (lhs : LVal) (rhs : Term) : Term :=
  show Term from (.assign lhs rhs)

abbrev ctermBox_ctor (operand : Term) : Term :=
  show Term from (.box operand)

abbrev ctermBorrowShared_ctor (operand : LVal) : Term :=
  LwRust.Core.Term.borrow Bool.false operand

abbrev ctermBorrowMut_ctor (operand : LVal) : Term :=
  LwRust.Core.Term.borrow Bool.true operand

abbrev ctermMove_ctor (operand : LVal) : Term :=
  show Term from (.move operand)

abbrev ctermCopy_ctor (operand : LVal) : Term :=
  show Term from (.copy operand)

abbrev ctermEq_ctor (lhs rhs : Term) : Term :=
  show Term from (.eq lhs rhs)

abbrev ctermIte_ctor (condition trueBranch falseBranch : Term) : Term :=
  show Term from (.ite condition trueBranch falseBranch)

abbrev ctermWhile_ctor (bodyLifetime : Lifetime) (condition body : Term) : Term :=
  show Term from (.whileLoop bodyLifetime condition body)

end SyntaxCtor

end ConservativeExtractor
