import FWRust.Sealor.CompleteProgram

/-!
Partial FWRust syntax and its completion relation.
-/

namespace ConservativeSealor
namespace Generated

inductive PartialName where
  | cutoff
  | done (x : Name)
  | prefix (x : Name)
  deriving Repr

mutual

inductive PartialTerms where
  | cutoff
  | done (xs : List Term)
  | elems (pre : List Term) (tail : Option PartialTerm)
  deriving Repr

inductive PartialTy where
  | cutoff
  | done (x : Ty)
  -- partial syntax: `& lval ...`
  | borrowSharedTargets (target : PartialLVal)
  -- partial syntax: `& mut lval ...`
  | borrowMutTargets (target : PartialLVal)
  -- partial syntax: `box ty ...`
  | boxElement (element : PartialTy)
  -- partial syntax: `& ...`
  | tokenAmpStart
  -- partial syntax: `box ...`
  | boxStart
  deriving Repr

inductive PartialLVal where
  | cutoff
  | done (x : LVal)
  -- partial syntax: `name ...`
  | varX (x : PartialName)
  -- partial syntax: `* lval ...`
  | derefOperand (operand : PartialLVal)
  -- partial syntax: `* ...`
  | derefStart
  deriving Repr

inductive PartialTerm where
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
  -- partial syntax: `block ...`
  | blockStart
  -- partial syntax: `let ...`
  | letMutStart
  -- partial syntax: `box ...`
  | boxStart
  -- partial syntax: `& ...`
  | tokenAmpStart
  -- partial syntax: `copy ...`
  | copyStart
  deriving Repr

end

abbrev PartialProgram := PartialTerm

inductive CompletesName : PartialName → Name → Prop where
  | done {x} :
      CompletesName (PartialName.done x) x
  | cutoff {x} :
      CompletesName PartialName.cutoff x
  | prefix {x y} :
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

inductive CompletesTy : PartialTy → Ty → Prop where
  | done {x} :
      CompletesTy (PartialTy.done x) x
  | cutoff {x} :
      CompletesTy PartialTy.cutoff x
  -- partial syntax: `& lval ...`
  | ctyBorrowShared_borrowSharedTargets {target : PartialLVal} {target' : LVal} :
      CompletesLVal target target' →
      CompletesTy (PartialTy.borrowSharedTargets target)
        (CompleteDsl.tyBorrow false target')
  -- partial syntax: `& mut lval ...`
  | ctyBorrowMut_borrowMutTargets {target : PartialLVal} {target' : LVal} :
      CompletesLVal target target' →
      CompletesTy (PartialTy.borrowMutTargets target)
        (CompleteDsl.tyBorrow true target')
  -- partial syntax: `box ty ...`
  | ctyBox_boxElement {element : PartialTy} {element' : Ty} :
      CompletesTy element element' →
      CompletesTy (PartialTy.boxElement element) (CompleteDsl.tyBox element')
  -- partial syntax: `& ...`
  | ctyBorrowShared_tokenAmpStart {target : LVal} :
      CompletesTy (PartialTy.tokenAmpStart)
        (CompleteDsl.tyBorrow false target)
  -- partial syntax: `& ...`
  | ctyBorrowMut_tokenAmpStart {target : LVal} :
      CompletesTy (PartialTy.tokenAmpStart)
        (CompleteDsl.tyBorrow true target)
  -- partial syntax: `box ...`
  | ctyBox_boxStart {element : Ty} :
      CompletesTy (PartialTy.boxStart) (CompleteDsl.tyBox element)

inductive CompletesLVal : PartialLVal → LVal → Prop where
  | done {x} :
      CompletesLVal (PartialLVal.done x) x
  | cutoff {x} :
      CompletesLVal PartialLVal.cutoff x
  -- partial syntax: `name ...`
  | clvalVar_varX {x : PartialName} {x' : Name} :
      CompletesName x x' →
      CompletesLVal (PartialLVal.varX x) (CompleteDsl.lvalVar x')
  -- partial syntax: `* lval ...`
  | clvalDeref_derefOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesLVal (PartialLVal.derefOperand operand)
        (CompleteDsl.lvalDeref operand')
  -- partial syntax: `* ...`
  | clvalDeref_derefStart {operand : LVal} :
      CompletesLVal (PartialLVal.derefStart) (CompleteDsl.lvalDeref operand)

inductive CompletesTerm : PartialTerm → Term → Prop where
  | done {x} :
      CompletesTerm (PartialTerm.done x) x
  | cutoff {x} :
      CompletesTerm PartialTerm.cutoff x
  -- partial syntax: `num ...`
  | ctermInt_intN {n : Int} :
      CompletesTerm (PartialTerm.intN n) (CompleteDsl.int n)
  -- partial syntax: `block lifetime { term,* ...`
  | ctermBlock_blockTerms {lifetime : Lifetime} {terms : PartialTerms} {terms' : List Term} :
      CompletesTerms terms terms' →
      CompletesTerm (PartialTerm.blockTerms lifetime terms)
        (CompleteDsl.block lifetime terms')
  -- partial syntax: `let mut name ...`
  | ctermLetMut_letMutName {name : PartialName} {name' : Name} {initialiser : Term} :
      CompletesName name name' →
      CompletesTerm (PartialTerm.letMutName name)
        (CompleteDsl.letMut name' initialiser)
  -- partial syntax: `let mut name := term ...`
  | ctermLetMut_letMutRhs {name : Name} {term : PartialTerm} {term' : Term} :
      CompletesTerm term term' →
      CompletesTerm (PartialTerm.letMutRhs name term)
        (CompleteDsl.letMut name term')
  -- partial syntax: `lval ...`
  | ctermAssign_lvalStart {lval : PartialLVal} {lval' : LVal} {rhs : Term} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval)
        (CompleteDsl.assign lval' rhs)
  -- partial syntax: `lval := term ...`
  | ctermAssign_assignRhs {lhs : LVal} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.assignRhs lhs rhs)
        (CompleteDsl.assign lhs rhs')
  -- partial syntax: `box term ...`
  | ctermBox_boxOperand {operand : PartialTerm} {operand' : Term} :
      CompletesTerm operand operand' →
      CompletesTerm (PartialTerm.boxOperand operand) (CompleteDsl.box operand')
  -- partial syntax: `& lval ...`
  | ctermBorrowShared_borrowSharedOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowSharedOperand operand)
        (CompleteDsl.borrow false operand')
  -- partial syntax: `& mut lval ...`
  | ctermBorrowMut_borrowMutOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowMutOperand operand)
        (CompleteDsl.borrow true operand')
  -- partial syntax: `lval ...`
  | ctermMove_lvalStart {lval : PartialLVal} {lval' : LVal} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval) (CompleteDsl.move lval')
  -- partial syntax: `copy lval ...`
  | ctermCopy_copyOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.copyOperand operand) (CompleteDsl.copy operand')
  -- partial syntax: `block ...`
  | ctermBlock_blockStart {lifetime : Lifetime} {terms : List Term} :
      CompletesTerm (PartialTerm.blockStart) (CompleteDsl.block lifetime terms)
  -- partial syntax: `let ...`
  | ctermLetMut_letMutStart {name : Name} {initialiser : Term} :
      CompletesTerm (PartialTerm.letMutStart)
        (CompleteDsl.letMut name initialiser)
  -- partial syntax: `box ...`
  | ctermBox_boxStart {operand : Term} :
      CompletesTerm (PartialTerm.boxStart) (CompleteDsl.box operand)
  -- partial syntax: `& ...`
  | ctermBorrowShared_tokenAmpStart {operand : LVal} :
      CompletesTerm (PartialTerm.tokenAmpStart)
        (CompleteDsl.borrow false operand)
  -- partial syntax: `& ...`
  | ctermBorrowMut_tokenAmpStart {operand : LVal} :
      CompletesTerm (PartialTerm.tokenAmpStart)
        (CompleteDsl.borrow true operand)
  -- partial syntax: `copy ...`
  | ctermCopy_copyStart {operand : LVal} :
      CompletesTerm (PartialTerm.copyStart) (CompleteDsl.copy operand)

end


end Generated
end ConservativeSealor
