import LwRust.Paper.Syntax

/-!
Complete LwRust programs for the extractor development.

The copied extractor used a richer toy language with statements, functions,
products, sums, and loops.  LwRust's complete syntax is the core syntax from
`LwRust.Paper.Syntax`: complete programs are `Core.Term`s.
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
def tyBorrow (mutable : Bool) (targets : List LVal) : Ty :=
  .borrow mutable targets
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
syntax (name := ctyBorrowMut) "&mut" "[" clval,* "]" : cty
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
syntax (name := ctermBorrowMut) "&mut" clval : cterm
syntax (name := ctermMove) "move" clval : cterm
syntax (name := ctermCopy) "copy" clval : cterm
syntax (name := ctermEq) cterm "==" cterm : cterm
syntax (name := ctermIte) "if" cterm cterm "else" cterm : cterm

end ConservativeExtractor
