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

/-- Source-level terms without explicit block-lifetime annotations. -/
inductive RawTerm where
  | block (terms : List RawTerm)
  | letMut (name : Name) (initialiser : RawTerm)
  | assign (lhs : LVal) (rhs : RawTerm)
  | box (operand : RawTerm)
  | borrow (mutable : Bool) (operand : LVal)
  | move (operand : LVal)
  | copy (operand : LVal)
  | val (value : Value)
  deriving Repr

abbrev RawProgram := RawTerm

namespace RawTerm

/-- Deterministic child lifetime chosen by the annotation pass for a block. -/
def childLifetime (lifetime : Lifetime) : Lifetime :=
  { path := lifetime.path ++ [0] }

mutual

/-- Algorithmically insert block-lifetime annotations. -/
def annotate (currentLifetime : Lifetime) : RawTerm → Term
  | .block terms =>
      let blockLifetime := childLifetime currentLifetime
      .block blockLifetime (annotateList blockLifetime terms)
  | .letMut name initialiser =>
      .letMut name (annotate currentLifetime initialiser)
  | .assign lhs rhs =>
      .assign lhs (annotate currentLifetime rhs)
  | .box operand =>
      .box (annotate currentLifetime operand)
  | .borrow mutable operand =>
      .borrow mutable operand
  | .move operand =>
      .move operand
  | .copy operand =>
      .copy operand
  | .val value =>
      .val value

def annotateList (currentLifetime : Lifetime) : List RawTerm → List Term
  | [] => []
  | term :: rest =>
      annotate currentLifetime term :: annotateList currentLifetime rest

end

def annotateProgram : RawProgram → Program :=
  annotate LwRust.Core.Lifetime.root

@[simp] theorem annotateList_append (currentLifetime : Lifetime)
    (xs ys : List RawTerm) :
    annotateList currentLifetime (xs ++ ys) =
      annotateList currentLifetime xs ++ annotateList currentLifetime ys := by
  induction xs with
  | nil => rfl
  | cons term rest ih =>
      simp [annotateList, ih]

mutual

/--
`Annotates raw annotated` says that `annotated` is one possible insertion of
block-lifetime annotations into the unannotated source term `raw`.

The relation is deliberately structural: block annotations may choose any
lifetime, including one that is not a valid child of its parent.  Validity of
those choices is checked later by `TermTyping`.
-/
inductive Annotates : RawTerm → Term → Prop where
  | block {terms : List RawTerm} {blockLifetime : Lifetime}
      {annotatedTerms : List Term} :
      AnnotatesList terms annotatedTerms →
      Annotates (.block terms) (.block blockLifetime annotatedTerms)
  | letMut {name : Name} {initialiser : RawTerm} {annotatedInitialiser : Term} :
      Annotates initialiser annotatedInitialiser →
      Annotates (.letMut name initialiser) (.letMut name annotatedInitialiser)
  | assign {lhs : LVal} {rhs : RawTerm} {annotatedRhs : Term} :
      Annotates rhs annotatedRhs →
      Annotates (.assign lhs rhs) (.assign lhs annotatedRhs)
  | box {operand : RawTerm} {annotatedOperand : Term} :
      Annotates operand annotatedOperand →
      Annotates (.box operand) (.box annotatedOperand)
  | borrow {mutable : Bool} {operand : LVal} :
      Annotates (.borrow mutable operand) (.borrow mutable operand)
  | move {operand : LVal} :
      Annotates (.move operand) (.move operand)
  | copy {operand : LVal} :
      Annotates (.copy operand) (.copy operand)
  | val {value : Value} :
      Annotates (.val value) (.val value)

inductive AnnotatesList : List RawTerm → List Term → Prop where
  | nil :
      AnnotatesList [] []
  | cons {term : RawTerm} {rest : List RawTerm}
      {annotatedTerm : Term} {annotatedRest : List Term} :
      Annotates term annotatedTerm →
      AnnotatesList rest annotatedRest →
      AnnotatesList (term :: rest) (annotatedTerm :: annotatedRest)

end

def AnnotatesProgram (raw : RawProgram) (annotated : Program) : Prop :=
  Annotates raw annotated

mutual

theorem annotate_annotates (currentLifetime : Lifetime) :
    ∀ raw : RawTerm, Annotates raw (annotate currentLifetime raw)
  | .block terms =>
      Annotates.block (annotateList_annotates (childLifetime currentLifetime) terms)
  | .letMut _ initialiser =>
      Annotates.letMut (annotate_annotates currentLifetime initialiser)
  | .assign _ rhs =>
      Annotates.assign (annotate_annotates currentLifetime rhs)
  | .box operand =>
      Annotates.box (annotate_annotates currentLifetime operand)
  | .borrow _ _ =>
      Annotates.borrow
  | .move _ =>
      Annotates.move
  | .copy _ =>
      Annotates.copy
  | .val _ =>
      Annotates.val

theorem annotateList_annotates (currentLifetime : Lifetime) :
    ∀ raws : List RawTerm,
      AnnotatesList raws (annotateList currentLifetime raws)
  | [] => AnnotatesList.nil
  | term :: rest =>
      AnnotatesList.cons
        (annotate_annotates currentLifetime term)
        (annotateList_annotates currentLifetime rest)

end

theorem annotateProgram_annotates (raw : RawProgram) :
    AnnotatesProgram raw (annotateProgram raw) :=
  annotate_annotates LwRust.Core.Lifetime.root raw

end RawTerm

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

namespace RawCompleteDsl

def unit : RawTerm := .val .unit
def int (n : Int) : RawTerm := .val (.int n)
def block (terms : List RawTerm) : RawTerm := .block terms
def letMut (x : Name) (initialiser : RawTerm) : RawTerm :=
  .letMut x initialiser
def assign (lhs : LVal) (rhs : RawTerm) : RawTerm :=
  .assign lhs rhs
def box (operand : RawTerm) : RawTerm := .box operand
def borrow (mutable : Bool) (operand : LVal) : RawTerm :=
  .borrow mutable operand
def move (operand : LVal) : RawTerm := .move operand
def copy (operand : LVal) : RawTerm := .copy operand

end RawCompleteDsl

/-!
Object-language syntax declarations used by the partial-program generator.
They intentionally mirror the constructors of `LwRust.Core`.
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
syntax (name := ctermBlock) "block" "{" cterm,* "}" : cterm
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
  LwRust.Core.Ty.borrow Bool.false target

abbrev ctyBorrowMut_ctor (target : LVal) : Ty :=
  LwRust.Core.Ty.borrow Bool.true target

abbrev ctyBox_ctor (element : Ty) : Ty :=
  show Ty from (.box element)

abbrev clvalVar_ctor (x : Name) : LVal :=
  show LVal from (.var x)

abbrev clvalDeref_ctor (operand : LVal) : LVal :=
  show LVal from (.deref operand)

abbrev ctermUnit_ctor : RawTerm :=
  show RawTerm from .val .unit

abbrev ctermInt_ctor (n : Int) : RawTerm :=
  show RawTerm from (.val (.int n))

abbrev ctermBlock_ctor (terms : List RawTerm) : RawTerm :=
  show RawTerm from (.block terms)

abbrev ctermLetMut_ctor (name : Name) (initialiser : RawTerm) : RawTerm :=
  show RawTerm from (.letMut name initialiser)

abbrev ctermAssign_ctor (lhs : LVal) (rhs : RawTerm) : RawTerm :=
  show RawTerm from (.assign lhs rhs)

abbrev ctermBox_ctor (operand : RawTerm) : RawTerm :=
  show RawTerm from (.box operand)

abbrev ctermBorrowShared_ctor (operand : LVal) : RawTerm :=
  RawTerm.borrow Bool.false operand

abbrev ctermBorrowMut_ctor (operand : LVal) : RawTerm :=
  RawTerm.borrow Bool.true operand

abbrev ctermMove_ctor (operand : LVal) : RawTerm :=
  show RawTerm from (.move operand)

abbrev ctermCopy_ctor (operand : LVal) : RawTerm :=
  show RawTerm from (.copy operand)

end SyntaxCtor

end ConservativeExtractor
