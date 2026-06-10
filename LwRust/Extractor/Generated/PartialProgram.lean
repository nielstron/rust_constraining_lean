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

inductive PartialLVals where
  | cutoff
  | done (xs : List LVal)
  | elems (pre : List LVal) (tail : Option PartialLVal)
  deriving Repr

inductive PartialTerms where
  | cutoff
  | done (xs : List Term)
  | elems (pre : List Term) (tail : Option PartialTerm)
  deriving Repr

inductive PartialTy where
  | cutoff
  | done (x : Ty)
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {targets}
  | borrowSharedTargets (targets : PartialLVals)
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {targets}
  | borrowMutTargets (targets : PartialLVals)
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | boxElement (element : PartialTy)
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {targets}
  | tokenAmpStart
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {targets}
  | borrowMutStart
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | boxStart
  deriving Repr

inductive PartialLVal where
  | cutoff
  | done (x : LVal)
  -- derived from: SyntaxCtor.clvalVar_ctor {x}
  | varX (x : PartialName)
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | derefOperand (operand : PartialLVal)
  | derefStart
  deriving Repr

inductive PartialTerm where
  | cutoff
  | done (x : Term)
  -- derived from: SyntaxCtor.ctermInt_ctor {n}
  | intN (n : Int)
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | blockTerms (lifetime : Lifetime) (terms : PartialTerms)
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutName (name : PartialName)
  | letMutInitialiser (name : Name) (initialiser : PartialTerm)
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | assignLhs (lhs : PartialLVal)
  | assignRhs (lhs : LVal) (rhs : PartialTerm)
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | boxOperand (operand : PartialTerm)
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | borrowSharedOperand (operand : PartialLVal)
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | borrowMutOperand (operand : PartialLVal)
  -- derived from: SyntaxCtor.ctermMove_ctor {operand}
  | moveOperand (operand : PartialLVal)
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | copyOperand (operand : PartialLVal)
  -- derived from: SyntaxCtor.ctermEq_ctor {lhs} {rhs}
  | termPrefix (lhs : PartialTerm)
  | eqRhs (lhs : Term) (rhs : PartialTerm)
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | iteCondition (condition : PartialTerm)
  | iteTrueBranch (condition : Term) (trueBranch : PartialTerm)
  | iteFalseBranch (condition : Term) (trueBranch : Term) (falseBranch : PartialTerm)
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | blockStart
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutStart
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | boxStart
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | tokenAmpStart
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | borrowMutStart
  -- derived from: SyntaxCtor.ctermMove_ctor {operand}
  | moveStart
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | copyStart
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | iteStart
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

inductive CompletesLVals : PartialLVals → List LVal → Prop where
  | done {xs} :
      CompletesLVals (PartialLVals.done xs) xs
  | cutoff {xs} :
      CompletesLVals PartialLVals.cutoff xs
  | elemsDone {pre suffix : List LVal} :
      CompletesLVals (PartialLVals.elems pre none) (pre ++ suffix)
  | elemsTail {pre suffix : List LVal} {frontier : PartialLVal}
      {frontierCompletion : LVal} :
      CompletesLVal frontier frontierCompletion →
      CompletesLVals (PartialLVals.elems pre (some frontier))
        (pre ++ frontierCompletion :: suffix)

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
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {targets}
  | ctyBorrowShared_borrowSharedTargets {targets : PartialLVals} {targets' : List LVal} :
      CompletesLVals targets targets' →
      CompletesTy (PartialTy.borrowSharedTargets targets) (SyntaxCtor.ctyBorrowShared_ctor targets')
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {targets}
  | ctyBorrowMut_borrowMutTargets {targets : PartialLVals} {targets' : List LVal} :
      CompletesLVals targets targets' →
      CompletesTy (PartialTy.borrowMutTargets targets) (SyntaxCtor.ctyBorrowMut_ctor targets')
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | ctyBox_boxElement {element : PartialTy} {element' : Ty} :
      CompletesTy element element' →
      CompletesTy (PartialTy.boxElement element) (SyntaxCtor.ctyBox_ctor element')
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {targets}
  | ctyBorrowShared_tokenAmpStart {targets : List LVal} :
      CompletesTy (PartialTy.tokenAmpStart) (SyntaxCtor.ctyBorrowShared_ctor targets)
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {targets}
  | ctyBorrowMut_tokenAmpStart {targets : List LVal} :
      CompletesTy (PartialTy.tokenAmpStart) (SyntaxCtor.ctyBorrowMut_ctor targets)
  | ctyBorrowMut_borrowMutStart {targets : List LVal} :
      CompletesTy (PartialTy.borrowMutStart) (SyntaxCtor.ctyBorrowMut_ctor targets)
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | ctyBox_boxStart {element : Ty} :
      CompletesTy (PartialTy.boxStart) (SyntaxCtor.ctyBox_ctor element)

inductive CompletesLVal : PartialLVal → LVal → Prop where
  | done {x} :
      CompletesLVal (PartialLVal.done x) x
  | cutoff {x} :
      CompletesLVal PartialLVal.cutoff x
  -- derived from: SyntaxCtor.clvalVar_ctor {x}
  | clvalVar_varX {x : PartialName} {x' : Name} :
      CompletesName x x' →
      CompletesLVal (PartialLVal.varX x) (SyntaxCtor.clvalVar_ctor x')
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | clvalDeref_derefOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesLVal (PartialLVal.derefOperand operand) (SyntaxCtor.clvalDeref_ctor operand')
  | clvalDeref_derefStart {operand : LVal} :
      CompletesLVal (PartialLVal.derefStart) (SyntaxCtor.clvalDeref_ctor operand)

inductive CompletesTerm : PartialTerm → Term → Prop where
  | done {x} :
      CompletesTerm (PartialTerm.done x) x
  | cutoff {x} :
      CompletesTerm PartialTerm.cutoff x
  -- derived from: SyntaxCtor.ctermInt_ctor {n}
  | ctermInt_intN {n : Int} :
      CompletesTerm (PartialTerm.intN n) (SyntaxCtor.ctermInt_ctor n)
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | ctermBlock_blockTerms {lifetime : Lifetime} {terms : PartialTerms} {terms' : List Term} :
      CompletesTerms terms terms' →
      CompletesTerm (PartialTerm.blockTerms lifetime terms) (SyntaxCtor.ctermBlock_ctor lifetime terms')
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutName {name : PartialName} {name' : Name} {initialiser : Term} :
      CompletesName name name' →
      CompletesTerm (PartialTerm.letMutName name) (SyntaxCtor.ctermLetMut_ctor name' initialiser)
  | ctermLetMut_letMutInitialiser {name : Name} {initialiser : PartialTerm} {initialiser' : Term} :
      CompletesTerm initialiser initialiser' →
      CompletesTerm (PartialTerm.letMutInitialiser name initialiser) (SyntaxCtor.ctermLetMut_ctor name initialiser')
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | ctermAssign_assignLhs {lhs : PartialLVal} {lhs' : LVal} {rhs : Term} :
      CompletesLVal lhs lhs' →
      CompletesTerm (PartialTerm.assignLhs lhs) (SyntaxCtor.ctermAssign_ctor lhs' rhs)
  | ctermAssign_assignRhs {lhs : LVal} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.assignRhs lhs rhs) (SyntaxCtor.ctermAssign_ctor lhs rhs')
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | ctermBox_boxOperand {operand : PartialTerm} {operand' : Term} :
      CompletesTerm operand operand' →
      CompletesTerm (PartialTerm.boxOperand operand) (SyntaxCtor.ctermBox_ctor operand')
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | ctermBorrowShared_borrowSharedOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowSharedOperand operand) (SyntaxCtor.ctermBorrowShared_ctor operand')
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | ctermBorrowMut_borrowMutOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowMutOperand operand) (SyntaxCtor.ctermBorrowMut_ctor operand')
  -- derived from: SyntaxCtor.ctermMove_ctor {operand}
  | ctermMove_moveOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.moveOperand operand) (SyntaxCtor.ctermMove_ctor operand')
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | ctermCopy_copyOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.copyOperand operand) (SyntaxCtor.ctermCopy_ctor operand')
  -- derived from: SyntaxCtor.ctermEq_ctor {lhs} {rhs}
  | ctermEq_termPrefix {lhs : PartialTerm} {lhs' : Term} {rhs : Term} :
      CompletesTerm lhs lhs' →
      CompletesTerm (PartialTerm.termPrefix lhs) (SyntaxCtor.ctermEq_ctor lhs' rhs)
  | ctermEq_eqRhs {lhs : Term} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.eqRhs lhs rhs) (SyntaxCtor.ctermEq_ctor lhs rhs')
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | ctermIte_iteCondition {condition : PartialTerm} {condition' : Term} {trueBranch : Term} {falseBranch : Term} :
      CompletesTerm condition condition' →
      CompletesTerm (PartialTerm.iteCondition condition) (SyntaxCtor.ctermIte_ctor condition' trueBranch falseBranch)
  | ctermIte_iteTrueBranch {condition : Term} {trueBranch : PartialTerm} {trueBranch' : Term} {falseBranch : Term} :
      CompletesTerm trueBranch trueBranch' →
      CompletesTerm (PartialTerm.iteTrueBranch condition trueBranch) (SyntaxCtor.ctermIte_ctor condition trueBranch' falseBranch)
  | ctermIte_iteFalseBranch {condition : Term} {trueBranch : Term} {falseBranch : PartialTerm} {falseBranch' : Term} :
      CompletesTerm falseBranch falseBranch' →
      CompletesTerm (PartialTerm.iteFalseBranch condition trueBranch falseBranch) (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch')
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | ctermBlock_blockStart {lifetime : Lifetime} {terms : List Term} :
      CompletesTerm (PartialTerm.blockStart) (SyntaxCtor.ctermBlock_ctor lifetime terms)
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutStart {name : Name} {initialiser : Term} :
      CompletesTerm (PartialTerm.letMutStart) (SyntaxCtor.ctermLetMut_ctor name initialiser)
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | ctermBox_boxStart {operand : Term} :
      CompletesTerm (PartialTerm.boxStart) (SyntaxCtor.ctermBox_ctor operand)
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | ctermBorrowShared_tokenAmpStart {operand : LVal} :
      CompletesTerm (PartialTerm.tokenAmpStart) (SyntaxCtor.ctermBorrowShared_ctor operand)
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | ctermBorrowMut_tokenAmpStart {operand : LVal} :
      CompletesTerm (PartialTerm.tokenAmpStart) (SyntaxCtor.ctermBorrowMut_ctor operand)
  | ctermBorrowMut_borrowMutStart {operand : LVal} :
      CompletesTerm (PartialTerm.borrowMutStart) (SyntaxCtor.ctermBorrowMut_ctor operand)
  -- derived from: SyntaxCtor.ctermMove_ctor {operand}
  | ctermMove_moveStart {operand : LVal} :
      CompletesTerm (PartialTerm.moveStart) (SyntaxCtor.ctermMove_ctor operand)
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | ctermCopy_copyStart {operand : LVal} :
      CompletesTerm (PartialTerm.copyStart) (SyntaxCtor.ctermCopy_ctor operand)
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | ctermIte_iteStart {condition : Term} {trueBranch : Term} {falseBranch : Term} :
      CompletesTerm (PartialTerm.iteStart) (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch)

end


end Generated
end ConservativeExtractor
