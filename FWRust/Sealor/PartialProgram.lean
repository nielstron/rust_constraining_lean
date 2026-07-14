import FWRust.Sealor.CompleteProgram

/-!
Partial FWRust syntax and its completion relation.
-/

namespace ConservativeSealor

inductive PartialName where
  | done (x : Name)
  | prefix (x : Name)
  deriving Repr

mutual

inductive PartialTerms where
  | cutoff
  | done (xs : List Term)
  | elems (pre : List Term) (tail : Option PartialTerm)
  deriving Repr

inductive PartialLVal where
  -- Nothing decoded at the lvalue frontier.
  | cutoff
  | done (x : LVal)
  -- partial syntax: `name ...`
  | varX (x : PartialName)
  -- partial syntax: `* lval ...`
  | derefOperand (operand : PartialLVal)
  deriving Repr

inductive PartialTerm where
  -- Nothing decoded at the term frontier, including keyword-only prefixes.
  | cutoff
  | done (x : Term)
  -- partial syntax: `num ...`
  | intN (n : Int)
  -- partial syntax: `block lifetime { term,* ...`
  | blockTerms (lifetime : Lifetime) (terms : PartialTerms)
  -- partial syntax: `let mut name ...`
  | letMutName (name : PartialName)
  -- partial syntax: `let mut name := term ...`
  | letMutRhs (name : Name) (term : PartialTerm)
  -- partial syntax: `lval ...`
  | lvalStart (lval : PartialLVal)
  -- partial syntax: `lval := term ...`
  | assignRhs (lhs : LVal) (rhs : PartialTerm)
  -- partial syntax: `box term ...`
  | boxOperand (operand : PartialTerm)
  -- partial syntax: `& lval ...`
  | borrowSharedOperand (operand : PartialLVal)
  -- partial syntax: `& mut lval ...`
  | borrowMutOperand (operand : PartialLVal)
  -- partial syntax: `copy lval ...`
  | copyOperand (operand : PartialLVal)
  deriving Repr

end

abbrev PartialProgram := PartialTerm

/-- A nonempty generated name fragment realizes exactly the names whose text
extends that fragment. -/
def NamePrefix (fragment complete : Name) : Prop :=
  fragment ≠ "" ∧ String.isPrefixOf fragment complete = true

/-- Prefixing for canonical decimal integer spellings. This intentionally does
not model radix prefixes, digit separators, or other surface syntax. -/
def DecimalIntPrefix (fragment complete : Int) : Prop :=
  String.isPrefixOf fragment.repr complete.repr = true

inductive CompletesName : PartialName → Name → Prop where
  | done {x} :
      CompletesName (PartialName.done x) x
  | prefix {x y} :
      NamePrefix x y →
      CompletesName (PartialName.prefix x) y

mutual

inductive CompletesTerms : PartialTerms → List Term → Prop where
  | done {xs} :
      CompletesTerms (PartialTerms.done xs) xs
  | cutoff {xs} :
      CompletesTerms PartialTerms.cutoff xs
  | elemsDone {pre suffix : List Term} :
      CompletesTerms (PartialTerms.elems pre none) (pre ++ suffix)
  | elemsTail {pre suffix : List Term} {frontier : PartialTerm}
      {frontierCompletion : Term} :
      CompletesTerm frontier frontierCompletion →
      CompletesTerms (PartialTerms.elems pre (some frontier))
        (pre ++ frontierCompletion :: suffix)

inductive CompletesLVal : PartialLVal → LVal → Prop where
  | done {x} :
      CompletesLVal (PartialLVal.done x) x
  | cutoff {x} :
      CompletesLVal PartialLVal.cutoff x
  -- partial syntax: `name ...`
  | clvalVar_varX {x : PartialName} {x' : Name} :
      CompletesName x x' →
      CompletesLVal (PartialLVal.varX x) (CompleteProgram.lvalVar x')
  -- partial syntax: `* lval ...`
  | clvalDeref_derefOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesLVal (PartialLVal.derefOperand operand)
        (CompleteProgram.lvalDeref operand')

inductive CompletesTerm : PartialTerm → Term → Prop where
  | done {x} :
      CompletesTerm (PartialTerm.done x) x
  | cutoff {x} :
      CompletesTerm PartialTerm.cutoff x
  -- partial syntax: `num ...`
  | ctermInt_intN {fragment completion : Int} :
      DecimalIntPrefix fragment completion →
      CompletesTerm (PartialTerm.intN fragment) (CompleteProgram.int completion)
  -- partial syntax: `block lifetime { term,* ...`
  | ctermBlock_blockTerms {lifetime : Lifetime} {terms : PartialTerms} {terms' : List Term} :
      CompletesTerms terms terms' →
      CompletesTerm (PartialTerm.blockTerms lifetime terms)
        (CompleteProgram.block lifetime terms')
  -- partial syntax: `let mut name ...`
  | ctermLetMut_letMutName {name : PartialName} {name' : Name} {initialiser : Term} :
      CompletesName name name' →
      CompletesTerm (PartialTerm.letMutName name)
        (CompleteProgram.letMut name' initialiser)
  -- partial syntax: `let mut name := term ...`
  | ctermLetMut_letMutRhs {name : Name} {term : PartialTerm} {term' : Term} :
      CompletesTerm term term' →
      CompletesTerm (PartialTerm.letMutRhs name term)
        (CompleteProgram.letMut name term')
  -- partial syntax: `lval ...`
  | ctermAssign_lvalStart {lval : PartialLVal} {lval' : LVal} {rhs : Term} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval)
        (CompleteProgram.assign lval' rhs)
  -- partial syntax: `lval := term ...`
  | ctermAssign_assignRhs {lhs : LVal} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.assignRhs lhs rhs)
        (CompleteProgram.assign lhs rhs')
  -- partial syntax: `box term ...`
  | ctermBox_boxOperand {operand : PartialTerm} {operand' : Term} :
      CompletesTerm operand operand' →
      CompletesTerm (PartialTerm.boxOperand operand) (CompleteProgram.box operand')
  -- partial syntax: `& lval ...`
  | ctermBorrowShared_borrowSharedOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowSharedOperand operand)
        (CompleteProgram.borrow false operand')
  -- partial syntax: `& mut lval ...`
  | ctermBorrowMut_borrowMutOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowMutOperand operand)
        (CompleteProgram.borrow true operand')
  -- partial syntax: `lval ...`
  | ctermMove_lvalStart {lval : PartialLVal} {lval' : LVal} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval) (CompleteProgram.move lval')
  -- partial syntax: `copy lval ...`
  | ctermCopy_copyOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.copyOperand operand) (CompleteProgram.copy operand')

end

abbrev CompletesProgram : PartialProgram → Program → Prop :=
  CompletesTerm

end ConservativeSealor
