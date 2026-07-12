import FWRust.Sealor.CompleteProgram

/-!
Template for grammar-derived partial syntax.

The generator replaces the marker below with declarations derived from the
complete FWRust syntax facade in `FWRust.Sealor.CompleteProgram`.
-/

namespace ConservativeSealor
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
  -- partial syntax: `& lval ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  | borrowSharedTargets (target : PartialLVal)
  -- partial syntax: `& mut lval ...`
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | borrowMutTargets (target : PartialLVal)
  -- partial syntax: `& [ lval,* ...`
  -- derived from: SyntaxCtor.ctyBorrowSharedMany_ctor {targets}
  | borrowSharedManyTargets (targets : PartialLVals)
  -- partial syntax: `& mut [ lval,* ...`
  -- derived from: SyntaxCtor.ctyBorrowMutMany_ctor {targets}
  | borrowMutManyTargets (targets : PartialLVals)
  -- partial syntax: `box ty ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | boxElement (element : PartialTy)
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  -- derived from: SyntaxCtor.ctyBorrowSharedMany_ctor {targets}
  -- derived from: SyntaxCtor.ctyBorrowMutMany_ctor {targets}
  | tokenAmpStart
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | boxStart
  -- partial syntax: `& mut ...`
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  -- derived from: SyntaxCtor.ctyBorrowMutMany_ctor {targets}
  | borrowMutPrefix2
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
  | done (x : Term)
  -- partial syntax: `num ...`
  -- derived from: SyntaxCtor.ctermInt_ctor {n}
  | intN (n : Int)
  -- partial syntax: `block lifetime { term,* ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | blockTerms (lifetime : Lifetime) (terms : PartialTerms)
  -- partial syntax: `let mut name ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutName (name : PartialName)
  -- partial syntax: `let mut name := term ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutRhs (name : Name) (term : PartialTerm)
  -- partial syntax: `lval ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  -- derived from: SyntaxCtor.ctermMove_ctor {operand}
  -- derived from: SyntaxCtor.ctermEq_ctor (SyntaxCtor.ctermMove_ctor {lval}) {rhs}
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
  -- partial syntax: `term ...`
  -- derived from: SyntaxCtor.ctermEq_ctor {lhs} {rhs}
  | termPrefix (lhs : PartialTerm)
  -- partial syntax: `term == term ...`
  -- derived from: SyntaxCtor.ctermEq_ctor {lhs} {rhs}
  | eqRhs (lhs : Term) (rhs : PartialTerm)
  -- partial syntax: `if term ...`
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | iteCondition (condition : PartialTerm)
  -- partial syntax: `if term term ...`
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | iteTrueBranch (condition : Term) (trueBranch : PartialTerm)
  -- partial syntax: `if term term else term ...`
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | iteFalseBranch (condition : Term) (trueBranch : Term) (falseBranch : PartialTerm)
  -- partial syntax: `while lifetime term ...`
  -- derived from: SyntaxCtor.ctermWhile_ctor {bodyLifetime} {condition} {body}
  | whileCondition (bodyLifetime : Lifetime) (condition : PartialTerm)
  -- partial syntax: `while lifetime term term ...`
  -- derived from: SyntaxCtor.ctermWhile_ctor {bodyLifetime} {condition} {body}
  | whileBody (bodyLifetime : Lifetime) (condition : Term) (body : PartialTerm)
  -- partial syntax: `block ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
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
  -- partial syntax: `if ...`
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | iteStart
  -- partial syntax: `while ...`
  -- derived from: SyntaxCtor.ctermWhile_ctor {bodyLifetime} {condition} {body}
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
  -- partial syntax: `& [ lval,* ...`
  -- derived from: SyntaxCtor.ctyBorrowSharedMany_ctor {targets}
  | ctyBorrowSharedMany_borrowSharedManyTargets {targets : PartialLVals} {targets' : List LVal} :
      CompletesLVals targets targets' →
      CompletesTy (PartialTy.borrowSharedManyTargets targets) (SyntaxCtor.ctyBorrowSharedMany_ctor targets')
  -- partial syntax: `& mut [ lval,* ...`
  -- derived from: SyntaxCtor.ctyBorrowMutMany_ctor {targets}
  | ctyBorrowMutMany_borrowMutManyTargets {targets : PartialLVals} {targets' : List LVal} :
      CompletesLVals targets targets' →
      CompletesTy (PartialTy.borrowMutManyTargets targets) (SyntaxCtor.ctyBorrowMutMany_ctor targets')
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
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctyBorrowSharedMany_ctor {targets}
  | ctyBorrowSharedMany_tokenAmpStart {targets : List LVal} :
      CompletesTy (PartialTy.tokenAmpStart) (SyntaxCtor.ctyBorrowSharedMany_ctor targets)
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctyBorrowMutMany_ctor {targets}
  | ctyBorrowMutMany_tokenAmpStart {targets : List LVal} :
      CompletesTy (PartialTy.tokenAmpStart) (SyntaxCtor.ctyBorrowMutMany_ctor targets)
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | ctyBox_boxStart {element : Ty} :
      CompletesTy (PartialTy.boxStart) (SyntaxCtor.ctyBox_ctor element)
  -- partial syntax: `& mut ...`
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | ctyBorrowMut_borrowMutPrefix2 {target : LVal} :
      CompletesTy (PartialTy.borrowMutPrefix2) (SyntaxCtor.ctyBorrowMut_ctor target)
  -- partial syntax: `& mut ...`
  -- derived from: SyntaxCtor.ctyBorrowMutMany_ctor {targets}
  | ctyBorrowMutMany_borrowMutPrefix2 {targets : List LVal} :
      CompletesTy (PartialTy.borrowMutPrefix2) (SyntaxCtor.ctyBorrowMutMany_ctor targets)

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

inductive CompletesTerm : PartialTerm → Term → Prop where
  | done {x} :
      CompletesTerm (PartialTerm.done x) x
  | cutoff {x} :
      CompletesTerm PartialTerm.cutoff x
  -- partial syntax: `num ...`
  -- derived from: SyntaxCtor.ctermInt_ctor {n}
  | ctermInt_intN {n : Int} :
      CompletesTerm (PartialTerm.intN n) (SyntaxCtor.ctermInt_ctor n)
  -- partial syntax: `block lifetime { term,* ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | ctermBlock_blockTerms {lifetime : Lifetime} {terms : PartialTerms} {terms' : List Term} :
      CompletesTerms terms terms' →
      CompletesTerm (PartialTerm.blockTerms lifetime terms) (SyntaxCtor.ctermBlock_ctor lifetime terms')
  -- partial syntax: `let mut name ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutName {name : PartialName} {name' : Name} {initialiser : Term} :
      CompletesName name name' →
      CompletesTerm (PartialTerm.letMutName name) (SyntaxCtor.ctermLetMut_ctor name' initialiser)
  -- partial syntax: `let mut name := term ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutRhs {name : Name} {term : PartialTerm} {term' : Term} :
      CompletesTerm term term' →
      CompletesTerm (PartialTerm.letMutRhs name term) (SyntaxCtor.ctermLetMut_ctor name term')
  -- partial syntax: `lval ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | ctermAssign_lvalStart {lval : PartialLVal} {lval' : LVal} {rhs : Term} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval) (SyntaxCtor.ctermAssign_ctor lval' rhs)
  -- partial syntax: `lval := term ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | ctermAssign_assignRhs {lhs : LVal} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.assignRhs lhs rhs) (SyntaxCtor.ctermAssign_ctor lhs rhs')
  -- partial syntax: `box term ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | ctermBox_boxOperand {operand : PartialTerm} {operand' : Term} :
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
  -- partial syntax: `term ...`
  -- derived from: SyntaxCtor.ctermEq_ctor {lhs} {rhs}
  | ctermEq_termPrefix {lhs : PartialTerm} {lhs' : Term} {rhs : Term} :
      CompletesTerm lhs lhs' →
      CompletesTerm (PartialTerm.termPrefix lhs) (SyntaxCtor.ctermEq_ctor lhs' rhs)
  -- partial syntax: `term == term ...`
  -- derived from: SyntaxCtor.ctermEq_ctor {lhs} {rhs}
  | ctermEq_eqRhs {lhs : Term} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.eqRhs lhs rhs) (SyntaxCtor.ctermEq_ctor lhs rhs')
  -- partial syntax: `if term ...`
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | ctermIte_iteCondition {condition : PartialTerm} {condition' : Term} {trueBranch : Term} {falseBranch : Term} :
      CompletesTerm condition condition' →
      CompletesTerm (PartialTerm.iteCondition condition) (SyntaxCtor.ctermIte_ctor condition' trueBranch falseBranch)
  -- partial syntax: `if term term ...`
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | ctermIte_iteTrueBranch {condition : Term} {trueBranch : PartialTerm} {trueBranch' : Term} {falseBranch : Term} :
      CompletesTerm trueBranch trueBranch' →
      CompletesTerm (PartialTerm.iteTrueBranch condition trueBranch) (SyntaxCtor.ctermIte_ctor condition trueBranch' falseBranch)
  -- partial syntax: `if term term else term ...`
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | ctermIte_iteFalseBranch {condition : Term} {trueBranch : Term} {falseBranch : PartialTerm} {falseBranch' : Term} :
      CompletesTerm falseBranch falseBranch' →
      CompletesTerm (PartialTerm.iteFalseBranch condition trueBranch falseBranch) (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch')
  -- partial syntax: `while lifetime term ...`
  -- derived from: SyntaxCtor.ctermWhile_ctor {bodyLifetime} {condition} {body}
  | ctermWhile_whileCondition {bodyLifetime : Lifetime} {condition : PartialTerm} {condition' : Term} {body : Term} :
      CompletesTerm condition condition' →
      CompletesTerm (PartialTerm.whileCondition bodyLifetime condition) (SyntaxCtor.ctermWhile_ctor bodyLifetime condition' body)
  -- partial syntax: `while lifetime term term ...`
  -- derived from: SyntaxCtor.ctermWhile_ctor {bodyLifetime} {condition} {body}
  | ctermWhile_whileBody {bodyLifetime : Lifetime} {condition : Term} {body : PartialTerm} {body' : Term} :
      CompletesTerm body body' →
      CompletesTerm (PartialTerm.whileBody bodyLifetime condition body) (SyntaxCtor.ctermWhile_ctor bodyLifetime condition body')
  -- partial syntax: `block ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | ctermBlock_blockStart {lifetime : Lifetime} {terms : List Term} :
      CompletesTerm (PartialTerm.blockStart) (SyntaxCtor.ctermBlock_ctor lifetime terms)
  -- partial syntax: `let ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutStart {name : Name} {initialiser : Term} :
      CompletesTerm (PartialTerm.letMutStart) (SyntaxCtor.ctermLetMut_ctor name initialiser)
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | ctermBox_boxStart {operand : Term} :
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
  -- partial syntax: `if ...`
  -- derived from: SyntaxCtor.ctermIte_ctor {condition} {trueBranch} {falseBranch}
  | ctermIte_iteStart {condition : Term} {trueBranch : Term} {falseBranch : Term} :
      CompletesTerm (PartialTerm.iteStart) (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch)
  -- partial syntax: `while ...`
  -- derived from: SyntaxCtor.ctermWhile_ctor {bodyLifetime} {condition} {body}
  | ctermWhile_whileStart {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
      CompletesTerm (PartialTerm.whileStart) (SyntaxCtor.ctermWhile_ctor bodyLifetime condition body)
  -- partial syntax: `lval ...`
  -- derived from: SyntaxCtor.ctermEq_ctor (SyntaxCtor.ctermMove_ctor {lval}) {rhs}
  | ctermEq_lvalStart {lval : PartialLVal} {lval' : LVal} {rhs : Term} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval) (SyntaxCtor.ctermEq_ctor (SyntaxCtor.ctermMove_ctor lval') rhs)

end


end Generated
end ConservativeSealor
