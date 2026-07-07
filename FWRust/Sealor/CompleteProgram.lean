import FWRust.Paper.Syntax

/-!
Complete FWRust programs for the sealor development.

This mainly defines a syntax for complete FWRust programs
so that we can derive partial programs from them.
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

/-!
Object-language syntax declarations used by the partial-program generator.
They intentionally mirror the constructors of `FWRust.Core`.
-/

declare_syntax_cat cty
declare_syntax_cat clval
declare_syntax_cat cterm

syntax (name := ctyUnit) "cty_unit" : cty
syntax (name := ctyInt) "cty_int" : cty
syntax (name := ctyBorrowShared) "&" clval : cty
syntax (name := ctyBorrowMut) "&" "mut" clval : cty
syntax (name := ctyBox) "box" cty : cty

syntax (name := clvalVar) ident : clval
syntax (name := clvalDeref) "*" clval : clval

syntax (name := ctermUnit) "()" : cterm
syntax (name := ctermInt) num : cterm
syntax (name := ctermBlock) "block" term "{" cterm,* "}" : cterm
syntax (name := ctermLetMut) "let" "mut" ident ":=" cterm : cterm
syntax (name := ctermAssign) clval ":=" cterm : cterm
syntax (name := ctermBox) "box" cterm : cterm
syntax (name := ctermBorrowShared) "&" clval : cterm
syntax (name := ctermBorrowMut) "&" "mut" clval : cterm
syntax (name := ctermMove) clval : cterm
syntax (name := ctermCopy) "copy" clval : cterm

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

abbrev ctyBorrowShared_ctor (target : LVal) : Ty :=
  FWRust.Core.Ty.borrow Bool.false target

abbrev ctyBorrowMut_ctor (target : LVal) : Ty :=
  FWRust.Core.Ty.borrow Bool.true target

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

abbrev ctermBlock_ctor (lifetime : Lifetime) (terms : List Term) : Term :=
  show Term from (.block lifetime terms)

abbrev ctermLetMut_ctor (name : Name) (initialiser : Term) : Term :=
  show Term from (.letMut name initialiser)

abbrev ctermAssign_ctor (lhs : LVal) (rhs : Term) : Term :=
  show Term from (.assign lhs rhs)

abbrev ctermBox_ctor (operand : Term) : Term :=
  show Term from (.box operand)

abbrev ctermBorrowShared_ctor (operand : LVal) : Term :=
  FWRust.Core.Term.borrow Bool.false operand

abbrev ctermBorrowMut_ctor (operand : LVal) : Term :=
  FWRust.Core.Term.borrow Bool.true operand

abbrev ctermMove_ctor (operand : LVal) : Term :=
  show Term from (.move operand)

abbrev ctermCopy_ctor (operand : LVal) : Term :=
  show Term from (.copy operand)

end SyntaxCtor

end ConservativeSealor
