import LwRust.Extractor.CompleteProgram

/-!
Template for grammar-derived partial syntax.

The generator replaces the marker below with declarations derived from the
complete LwRust syntax facade in `LwRust.Extractor.CompleteProgram`.
-/

namespace ConservativeExtractor
namespace Generated

inductive PartialName where
  | cutoff
  | done (x : Name)
  | prefix (x : Name)
  deriving Repr

mutual

inductive PartialTerms where
  | cutoff
  | done (xs : List RawTerm)
  | elems (pre : List RawTerm) (tail : Option PartialTerm)
  deriving Repr

inductive PartialTy where
  | cutoff
  | done (x : Ty)
  -- partial syntax: `& lval ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  | borrowSharedTargets (target : PartialLVal)
  -- partial syntax: `& mut lval ...`
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | borrowMutTargets (target : PartialLVal)
  -- partial syntax: `box ty ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | boxElement (element : PartialTy)
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | tokenAmpStart
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | boxStart
  deriving Repr

inductive PartialLVal where
  | cutoff
  | done (x : LVal)
  -- partial syntax: `name ...`
  -- derived from: SyntaxCtor.clvalVar_ctor {x}
  | varX (x : PartialName)
  -- partial syntax: `* lval ...`
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | derefOperand (operand : PartialLVal)
  -- partial syntax: `* ...`
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | derefStart
  deriving Repr

inductive PartialTerm where
  | cutoff
  | done (x : RawTerm)
  -- partial syntax: `num ...`
  -- derived from: SyntaxCtor.ctermInt_ctor {n}
  | intN (n : Int)
  -- partial syntax: `block { term,* ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {terms}
  | blockTerms (terms : PartialTerms)
  -- partial syntax: `let mut name ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutName (name : PartialName)
  -- partial syntax: `let mut name := term ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutRhs (name : Name) (term : PartialTerm)
  -- partial syntax: `lval ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  -- derived from: SyntaxCtor.ctermMove_ctor {operand}
  | lvalStart (lval : PartialLVal)
  -- partial syntax: `lval := term ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | assignRhs (lhs : LVal) (rhs : PartialTerm)
  -- partial syntax: `box term ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | boxOperand (operand : PartialTerm)
  -- partial syntax: `& lval ...`
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | borrowSharedOperand (operand : PartialLVal)
  -- partial syntax: `& mut lval ...`
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | borrowMutOperand (operand : PartialLVal)
  -- partial syntax: `copy lval ...`
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | copyOperand (operand : PartialLVal)
  -- partial syntax: `block ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {terms}
  | blockStart
  -- partial syntax: `let ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutStart
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | boxStart
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | tokenAmpStart
  -- partial syntax: `copy ...`
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
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

inductive CompletesTerms : PartialTerms → List RawTerm → Prop where
  | done {xs} :
      CompletesTerms (PartialTerms.done xs) xs
  | cutoff {xs} :
      CompletesTerms PartialTerms.cutoff xs
  | elemsDone {pre suffix : List RawTerm} :
      CompletesTerms (PartialTerms.elems pre none) (pre ++ suffix)
  | elemsTail {pre suffix : List RawTerm} {frontier : PartialTerm}
      {frontierCompletion : RawTerm} :
      CompletesTerm frontier frontierCompletion →
      CompletesTerms (PartialTerms.elems pre (some frontier))
        (pre ++ frontierCompletion :: suffix)

inductive CompletesTy : PartialTy → Ty → Prop where
  | done {x} :
      CompletesTy (PartialTy.done x) x
  | cutoff {x} :
      CompletesTy PartialTy.cutoff x
  -- partial syntax: `& lval ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  | ctyBorrowShared_borrowSharedTargets {target : PartialLVal} {target' : LVal} :
      CompletesLVal target target' →
      CompletesTy (PartialTy.borrowSharedTargets target) (SyntaxCtor.ctyBorrowShared_ctor target')
  -- partial syntax: `& mut lval ...`
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | ctyBorrowMut_borrowMutTargets {target : PartialLVal} {target' : LVal} :
      CompletesLVal target target' →
      CompletesTy (PartialTy.borrowMutTargets target) (SyntaxCtor.ctyBorrowMut_ctor target')
  -- partial syntax: `box ty ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | ctyBox_boxElement {element : PartialTy} {element' : Ty} :
      CompletesTy element element' →
      CompletesTy (PartialTy.boxElement element) (SyntaxCtor.ctyBox_ctor element')
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  | ctyBorrowShared_tokenAmpStart {target : LVal} :
      CompletesTy (PartialTy.tokenAmpStart) (SyntaxCtor.ctyBorrowShared_ctor target)
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | ctyBorrowMut_tokenAmpStart {target : LVal} :
      CompletesTy (PartialTy.tokenAmpStart) (SyntaxCtor.ctyBorrowMut_ctor target)
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | ctyBox_boxStart {element : Ty} :
      CompletesTy (PartialTy.boxStart) (SyntaxCtor.ctyBox_ctor element)

inductive CompletesLVal : PartialLVal → LVal → Prop where
  | done {x} :
      CompletesLVal (PartialLVal.done x) x
  | cutoff {x} :
      CompletesLVal PartialLVal.cutoff x
  -- partial syntax: `name ...`
  -- derived from: SyntaxCtor.clvalVar_ctor {x}
  | clvalVar_varX {x : PartialName} {x' : Name} :
      CompletesName x x' →
      CompletesLVal (PartialLVal.varX x) (SyntaxCtor.clvalVar_ctor x')
  -- partial syntax: `* lval ...`
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | clvalDeref_derefOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesLVal (PartialLVal.derefOperand operand) (SyntaxCtor.clvalDeref_ctor operand')
  -- partial syntax: `* ...`
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | clvalDeref_derefStart {operand : LVal} :
      CompletesLVal (PartialLVal.derefStart) (SyntaxCtor.clvalDeref_ctor operand)

inductive CompletesTerm : PartialTerm → RawTerm → Prop where
  | done {x} :
      CompletesTerm (PartialTerm.done x) x
  | cutoff {x} :
      CompletesTerm PartialTerm.cutoff x
  -- partial syntax: `num ...`
  -- derived from: SyntaxCtor.ctermInt_ctor {n}
  | ctermInt_intN {n : Int} :
      CompletesTerm (PartialTerm.intN n) (SyntaxCtor.ctermInt_ctor n)
  -- partial syntax: `block { term,* ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {terms}
  | ctermBlock_blockTerms {terms : PartialTerms} {terms' : List RawTerm} :
      CompletesTerms terms terms' →
      CompletesTerm (PartialTerm.blockTerms terms) (SyntaxCtor.ctermBlock_ctor terms')
  -- partial syntax: `let mut name ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutName {name : PartialName} {name' : Name} {initialiser : RawTerm} :
      CompletesName name name' →
      CompletesTerm (PartialTerm.letMutName name) (SyntaxCtor.ctermLetMut_ctor name' initialiser)
  -- partial syntax: `let mut name := term ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutRhs {name : Name} {term : PartialTerm} {term' : RawTerm} :
      CompletesTerm term term' →
      CompletesTerm (PartialTerm.letMutRhs name term) (SyntaxCtor.ctermLetMut_ctor name term')
  -- partial syntax: `lval ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | ctermAssign_lvalStart {lval : PartialLVal} {lval' : LVal} {rhs : RawTerm} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval) (SyntaxCtor.ctermAssign_ctor lval' rhs)
  -- partial syntax: `lval := term ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | ctermAssign_assignRhs {lhs : LVal} {rhs : PartialTerm} {rhs' : RawTerm} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.assignRhs lhs rhs) (SyntaxCtor.ctermAssign_ctor lhs rhs')
  -- partial syntax: `box term ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | ctermBox_boxOperand {operand : PartialTerm} {operand' : RawTerm} :
      CompletesTerm operand operand' →
      CompletesTerm (PartialTerm.boxOperand operand) (SyntaxCtor.ctermBox_ctor operand')
  -- partial syntax: `& lval ...`
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | ctermBorrowShared_borrowSharedOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowSharedOperand operand) (SyntaxCtor.ctermBorrowShared_ctor operand')
  -- partial syntax: `& mut lval ...`
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | ctermBorrowMut_borrowMutOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowMutOperand operand) (SyntaxCtor.ctermBorrowMut_ctor operand')
  -- partial syntax: `lval ...`
  -- derived from: SyntaxCtor.ctermMove_ctor {operand}
  | ctermMove_lvalStart {lval : PartialLVal} {lval' : LVal} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval) (SyntaxCtor.ctermMove_ctor lval')
  -- partial syntax: `copy lval ...`
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | ctermCopy_copyOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.copyOperand operand) (SyntaxCtor.ctermCopy_ctor operand')
  -- partial syntax: `block ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {terms}
  | ctermBlock_blockStart {terms : List RawTerm} :
      CompletesTerm (PartialTerm.blockStart) (SyntaxCtor.ctermBlock_ctor terms)
  -- partial syntax: `let ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutStart {name : Name} {initialiser : RawTerm} :
      CompletesTerm (PartialTerm.letMutStart) (SyntaxCtor.ctermLetMut_ctor name initialiser)
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | ctermBox_boxStart {operand : RawTerm} :
      CompletesTerm (PartialTerm.boxStart) (SyntaxCtor.ctermBox_ctor operand)
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | ctermBorrowShared_tokenAmpStart {operand : LVal} :
      CompletesTerm (PartialTerm.tokenAmpStart) (SyntaxCtor.ctermBorrowShared_ctor operand)
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | ctermBorrowMut_tokenAmpStart {operand : LVal} :
      CompletesTerm (PartialTerm.tokenAmpStart) (SyntaxCtor.ctermBorrowMut_ctor operand)
  -- partial syntax: `copy ...`
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | ctermCopy_copyStart {operand : LVal} :
      CompletesTerm (PartialTerm.copyStart) (SyntaxCtor.ctermCopy_ctor operand)

end


end Generated
end ConservativeExtractor
