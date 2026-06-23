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
  -- derived from: SyntaxSemantics.ctyBorrowShared {targets}
  | borrowSharedTargets (targets : PartialLVals)
  -- derived from: SyntaxSemantics.ctyBorrowMut {targets}
  | borrowMutTargets (targets : PartialLVals)
  -- derived from: SyntaxSemantics.ctyBox {element}
  | boxElement (element : PartialTy)
  -- derived from: SyntaxSemantics.ctyBorrowShared {targets}
  | borrowSharedStart
  -- derived from: SyntaxSemantics.ctyBox {element}
  | boxStart
  deriving Repr

inductive PartialLVal where
  | cutoff
  | done (x : LVal)
  -- derived from: SyntaxSemantics.clvalVar {x}
  | varX (x : PartialName)
  -- derived from: SyntaxSemantics.clvalDeref {operand}
  | derefOperand (operand : PartialLVal)
  | derefStart
  deriving Repr

inductive PartialTerm where
  | cutoff
  | done (x : Term)
  -- derived from: SyntaxSemantics.ctermInt {n}
  | intN (n : Int)
  -- derived from: SyntaxSemantics.ctermBlock {lifetime} {terms}
  | blockTerms (lifetime : Lifetime) (terms : PartialTerms)
  -- derived from: SyntaxSemantics.ctermLetMut {name} {initialiser}
  | letMutName (name : PartialName)
  | letMutInitialiser (name : Name) (initialiser : PartialTerm)
  -- derived from: SyntaxSemantics.ctermAssign {lhs} {rhs}
  | assignLhs (lhs : PartialLVal)
  | assignRhs (lhs : LVal) (rhs : PartialTerm)
  -- derived from: SyntaxSemantics.ctermBox {operand}
  | boxOperand (operand : PartialTerm)
  -- derived from: SyntaxSemantics.ctermBorrowShared {operand}
  | borrowSharedOperand (operand : PartialLVal)
  -- derived from: SyntaxSemantics.ctermBorrowMut {operand}
  | borrowMutOperand (operand : PartialLVal)
  -- derived from: SyntaxSemantics.ctermMove {operand}
  | moveOperand (operand : PartialLVal)
  -- derived from: SyntaxSemantics.ctermCopy {operand}
  | copyOperand (operand : PartialLVal)
  -- derived from: SyntaxSemantics.ctermEq {lhs} {rhs}
  | termPrefix (lhs : PartialTerm)
  | eqRhs (lhs : Term) (rhs : PartialTerm)
  -- derived from: SyntaxSemantics.ctermIte {condition} {trueBranch} {falseBranch}
  | iteCondition (condition : PartialTerm)
  | iteTrueBranch (condition : Term) (trueBranch : PartialTerm)
  | iteFalseBranch (condition : Term) (trueBranch : Term) (falseBranch : PartialTerm)
  -- derived from: SyntaxSemantics.ctermWhile {bodyLifetime} {condition} {body}
  | whileCondition (bodyLifetime : Lifetime) (condition : PartialTerm)
  | whileBody (bodyLifetime : Lifetime) (condition : Term) (body : PartialTerm)
  -- derived from: SyntaxSemantics.ctermBlock {lifetime} {terms}
  | blockStart
  -- derived from: SyntaxSemantics.ctermLetMut {name} {initialiser}
  | letMutStart
  -- derived from: SyntaxSemantics.ctermBox {operand}
  | boxStart
  -- derived from: SyntaxSemantics.ctermBorrowShared {operand}
  | borrowSharedStart
  -- derived from: SyntaxSemantics.ctermCopy {operand}
  | copyStart
  -- derived from: SyntaxSemantics.ctermIte {condition} {trueBranch} {falseBranch}
  | iteStart
  -- derived from: SyntaxSemantics.ctermWhile {bodyLifetime} {condition} {body}
  | whileStart
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
  -- derived from: SyntaxSemantics.ctyBorrowShared {targets}
  | ctyBorrowShared_borrowSharedTargets {targets : PartialLVals} {targets' : List LVal} :
      CompletesLVals targets targets' →
      CompletesTy (PartialTy.borrowSharedTargets targets) (SyntaxSemantics.ctyBorrowShared targets')
  -- derived from: SyntaxSemantics.ctyBorrowMut {targets}
  | ctyBorrowMut_borrowMutTargets {targets : PartialLVals} {targets' : List LVal} :
      CompletesLVals targets targets' →
      CompletesTy (PartialTy.borrowMutTargets targets) (SyntaxSemantics.ctyBorrowMut targets')
  -- derived from: SyntaxSemantics.ctyBox {element}
  | ctyBox_boxElement {element : PartialTy} {element' : Ty} :
      CompletesTy element element' →
      CompletesTy (PartialTy.boxElement element) (SyntaxSemantics.ctyBox element')
  -- derived from: SyntaxSemantics.ctyBorrowShared {targets}
  | ctyBorrowShared_borrowSharedStart {targets : List LVal} :
      CompletesTy (PartialTy.borrowSharedStart) (SyntaxSemantics.ctyBorrowShared targets)
  -- derived from: SyntaxSemantics.ctyBorrowMut {targets}
  | ctyBorrowMut_borrowSharedStart {targets : List LVal} :
      CompletesTy (PartialTy.borrowSharedStart) (SyntaxSemantics.ctyBorrowMut targets)
  -- derived from: SyntaxSemantics.ctyBox {element}
  | ctyBox_boxStart {element : Ty} :
      CompletesTy (PartialTy.boxStart) (SyntaxSemantics.ctyBox element)

inductive CompletesLVal : PartialLVal → LVal → Prop where
  | done {x} :
      CompletesLVal (PartialLVal.done x) x
  | cutoff {x} :
      CompletesLVal PartialLVal.cutoff x
  -- derived from: SyntaxSemantics.clvalVar {x}
  | clvalVar_varX {x : PartialName} {x' : Name} :
      CompletesName x x' →
      CompletesLVal (PartialLVal.varX x) (SyntaxSemantics.clvalVar x')
  -- derived from: SyntaxSemantics.clvalDeref {operand}
  | clvalDeref_derefOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesLVal (PartialLVal.derefOperand operand) (SyntaxSemantics.clvalDeref operand')
  | clvalDeref_derefStart {operand : LVal} :
      CompletesLVal (PartialLVal.derefStart) (SyntaxSemantics.clvalDeref operand)

inductive CompletesTerm : PartialTerm → Term → Prop where
  | done {x} :
      CompletesTerm (PartialTerm.done x) x
  | cutoff {x} :
      CompletesTerm PartialTerm.cutoff x
  -- derived from: SyntaxSemantics.ctermInt {n}
  | ctermInt_intN {n : Int} :
      CompletesTerm (PartialTerm.intN n) (SyntaxSemantics.ctermInt n)
  -- derived from: SyntaxSemantics.ctermBlock {lifetime} {terms}
  | ctermBlock_blockTerms {lifetime : Lifetime} {terms : PartialTerms} {terms' : List Term} :
      CompletesTerms terms terms' →
      CompletesTerm (PartialTerm.blockTerms lifetime terms) (SyntaxSemantics.ctermBlock lifetime terms')
  -- derived from: SyntaxSemantics.ctermLetMut {name} {initialiser}
  | ctermLetMut_letMutName {name : PartialName} {name' : Name} {initialiser : Term} :
      CompletesName name name' →
      CompletesTerm (PartialTerm.letMutName name) (SyntaxSemantics.ctermLetMut name' initialiser)
  | ctermLetMut_letMutInitialiser {name : Name} {initialiser : PartialTerm} {initialiser' : Term} :
      CompletesTerm initialiser initialiser' →
      CompletesTerm (PartialTerm.letMutInitialiser name initialiser) (SyntaxSemantics.ctermLetMut name initialiser')
  -- derived from: SyntaxSemantics.ctermAssign {lhs} {rhs}
  | ctermAssign_assignLhs {lhs : PartialLVal} {lhs' : LVal} {rhs : Term} :
      CompletesLVal lhs lhs' →
      CompletesTerm (PartialTerm.assignLhs lhs) (SyntaxSemantics.ctermAssign lhs' rhs)
  | ctermAssign_assignRhs {lhs : LVal} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.assignRhs lhs rhs) (SyntaxSemantics.ctermAssign lhs rhs')
  -- derived from: SyntaxSemantics.ctermBox {operand}
  | ctermBox_boxOperand {operand : PartialTerm} {operand' : Term} :
      CompletesTerm operand operand' →
      CompletesTerm (PartialTerm.boxOperand operand) (SyntaxSemantics.ctermBox operand')
  -- derived from: SyntaxSemantics.ctermBorrowShared {operand}
  | ctermBorrowShared_borrowSharedOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowSharedOperand operand) (SyntaxSemantics.ctermBorrowShared operand')
  -- derived from: SyntaxSemantics.ctermBorrowMut {operand}
  | ctermBorrowMut_borrowMutOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowMutOperand operand) (SyntaxSemantics.ctermBorrowMut operand')
  -- derived from: SyntaxSemantics.ctermMove {operand}
  | ctermMove_moveOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.moveOperand operand) (SyntaxSemantics.ctermMove operand')
  -- derived from: SyntaxSemantics.ctermCopy {operand}
  | ctermCopy_copyOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.copyOperand operand) (SyntaxSemantics.ctermCopy operand')
  -- derived from: SyntaxSemantics.ctermEq {lhs} {rhs}
  | ctermEq_termPrefix {lhs : PartialTerm} {lhs' : Term} {rhs : Term} :
      CompletesTerm lhs lhs' →
      CompletesTerm (PartialTerm.termPrefix lhs) (SyntaxSemantics.ctermEq lhs' rhs)
  | ctermEq_eqRhs {lhs : Term} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.eqRhs lhs rhs) (SyntaxSemantics.ctermEq lhs rhs')
  -- derived from: SyntaxSemantics.ctermIte {condition} {trueBranch} {falseBranch}
  | ctermIte_iteCondition {condition : PartialTerm} {condition' : Term} {trueBranch : Term} {falseBranch : Term} :
      CompletesTerm condition condition' →
      CompletesTerm (PartialTerm.iteCondition condition) (SyntaxSemantics.ctermIte condition' trueBranch falseBranch)
  | ctermIte_iteTrueBranch {condition : Term} {trueBranch : PartialTerm} {trueBranch' : Term} {falseBranch : Term} :
      CompletesTerm trueBranch trueBranch' →
      CompletesTerm (PartialTerm.iteTrueBranch condition trueBranch) (SyntaxSemantics.ctermIte condition trueBranch' falseBranch)
  | ctermIte_iteFalseBranch {condition : Term} {trueBranch : Term} {falseBranch : PartialTerm} {falseBranch' : Term} :
      CompletesTerm falseBranch falseBranch' →
      CompletesTerm (PartialTerm.iteFalseBranch condition trueBranch falseBranch) (SyntaxSemantics.ctermIte condition trueBranch falseBranch')
  -- derived from: SyntaxSemantics.ctermWhile {bodyLifetime} {condition} {body}
  | ctermWhile_whileCondition {bodyLifetime : Lifetime} {condition : PartialTerm} {condition' : Term} {body : Term} :
      CompletesTerm condition condition' →
      CompletesTerm (PartialTerm.whileCondition bodyLifetime condition) (SyntaxSemantics.ctermWhile bodyLifetime condition' body)
  | ctermWhile_whileBody {bodyLifetime : Lifetime} {condition : Term} {body : PartialTerm} {body' : Term} :
      CompletesTerm body body' →
      CompletesTerm (PartialTerm.whileBody bodyLifetime condition body) (SyntaxSemantics.ctermWhile bodyLifetime condition body')
  -- derived from: SyntaxSemantics.ctermBlock {lifetime} {terms}
  | ctermBlock_blockStart {lifetime : Lifetime} {terms : List Term} :
      CompletesTerm (PartialTerm.blockStart) (SyntaxSemantics.ctermBlock lifetime terms)
  -- derived from: SyntaxSemantics.ctermLetMut {name} {initialiser}
  | ctermLetMut_letMutStart {name : Name} {initialiser : Term} :
      CompletesTerm (PartialTerm.letMutStart) (SyntaxSemantics.ctermLetMut name initialiser)
  -- derived from: SyntaxSemantics.ctermBox {operand}
  | ctermBox_boxStart {operand : Term} :
      CompletesTerm (PartialTerm.boxStart) (SyntaxSemantics.ctermBox operand)
  -- derived from: SyntaxSemantics.ctermBorrowShared {operand}
  | ctermBorrowShared_borrowSharedStart {operand : LVal} :
      CompletesTerm (PartialTerm.borrowSharedStart) (SyntaxSemantics.ctermBorrowShared operand)
  -- derived from: SyntaxSemantics.ctermBorrowMut {operand}
  | ctermBorrowMut_borrowSharedStart {operand : LVal} :
      CompletesTerm (PartialTerm.borrowSharedStart) (SyntaxSemantics.ctermBorrowMut operand)
  -- derived from: SyntaxSemantics.ctermCopy {operand}
  | ctermCopy_copyStart {operand : LVal} :
      CompletesTerm (PartialTerm.copyStart) (SyntaxSemantics.ctermCopy operand)
  -- derived from: SyntaxSemantics.ctermIte {condition} {trueBranch} {falseBranch}
  | ctermIte_iteStart {condition : Term} {trueBranch : Term} {falseBranch : Term} :
      CompletesTerm (PartialTerm.iteStart) (SyntaxSemantics.ctermIte condition trueBranch falseBranch)
  -- derived from: SyntaxSemantics.ctermWhile {bodyLifetime} {condition} {body}
  | ctermWhile_whileStart {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
      CompletesTerm (PartialTerm.whileStart) (SyntaxSemantics.ctermWhile bodyLifetime condition body)

end


end Generated
end ConservativeExtractor
