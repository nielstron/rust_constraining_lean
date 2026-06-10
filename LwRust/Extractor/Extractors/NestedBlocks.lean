import LwRust.Extractor.Checkers

/-!
A syntax-directed LwRust frontier extractor.

For list frontiers, the extractor keeps the complete prefix and recursively
extracts the single partial tail.  For expression/term frontiers, it reconstructs
the LwRust constructor and fills unavailable siblings with `unit`.
-/

namespace ConservativeExtractor

def defaultName : Name := "_"

def defaultLVal : LVal :=
  SyntaxCtor.clvalVar_ctor defaultName

def defaultTerm : Term :=
  SyntaxCtor.ctermUnit_ctor

def defaultTy : Ty :=
  SyntaxCtor.ctyUnit_ctor

mutual

def extractTy : PartialTy → Ty
  | Generated.PartialTy.cutoff => defaultTy
  | Generated.PartialTy.done ty => ty
  | Generated.PartialTy.borrowSharedTargets targets =>
      SyntaxCtor.ctyBorrowShared_ctor (extractLVals targets)
  | Generated.PartialTy.borrowMutTargets targets =>
      SyntaxCtor.ctyBorrowMut_ctor (extractLVals targets)
  | Generated.PartialTy.boxElement element =>
      SyntaxCtor.ctyBox_ctor (extractTy element)
  | Generated.PartialTy.tokenAmpStart =>
      SyntaxCtor.ctyBorrowShared_ctor []
  | Generated.PartialTy.borrowMutStart =>
      SyntaxCtor.ctyBorrowMut_ctor []
  | Generated.PartialTy.boxStart =>
      SyntaxCtor.ctyBox_ctor defaultTy

def extractLVal : PartialLVal → LVal
  | Generated.PartialLVal.cutoff => defaultLVal
  | Generated.PartialLVal.done lv => lv
  | Generated.PartialLVal.varX (Generated.PartialName.done x) =>
      SyntaxCtor.clvalVar_ctor x
  | Generated.PartialLVal.varX (Generated.PartialName.prefix x) =>
      SyntaxCtor.clvalVar_ctor x
  | Generated.PartialLVal.varX Generated.PartialName.cutoff =>
      defaultLVal
  | Generated.PartialLVal.derefStart =>
      SyntaxCtor.clvalDeref_ctor defaultLVal
  | Generated.PartialLVal.derefOperand operand =>
      SyntaxCtor.clvalDeref_ctor (extractLVal operand)

def extractLVals : PartialLVals → List LVal
  | Generated.PartialLVals.cutoff => []
  | Generated.PartialLVals.done xs => xs
  | Generated.PartialLVals.elems pre none => pre
  | Generated.PartialLVals.elems pre (some tail) => pre ++ [extractLVal tail]

def extractTerm : PartialTerm → Term
  | Generated.PartialTerm.cutoff => defaultTerm
  | Generated.PartialTerm.done term => term
  | Generated.PartialTerm.intN n => SyntaxCtor.ctermInt_ctor n
  | Generated.PartialTerm.blockStart =>
      SyntaxCtor.ctermBlock_ctor LwRust.Core.Lifetime.root []
  | Generated.PartialTerm.blockTerms lifetime terms =>
      SyntaxCtor.ctermBlock_ctor lifetime (extractTerms terms)
  | Generated.PartialTerm.letMutStart =>
      SyntaxCtor.ctermLetMut_ctor defaultName defaultTerm
  | Generated.PartialTerm.letMutName (Generated.PartialName.done x) =>
      SyntaxCtor.ctermLetMut_ctor x defaultTerm
  | Generated.PartialTerm.letMutName (Generated.PartialName.prefix x) =>
      SyntaxCtor.ctermLetMut_ctor x defaultTerm
  | Generated.PartialTerm.letMutName Generated.PartialName.cutoff =>
      SyntaxCtor.ctermLetMut_ctor defaultName defaultTerm
  | Generated.PartialTerm.letMutInitialiser name initialiser =>
      SyntaxCtor.ctermLetMut_ctor name (extractTerm initialiser)
  | Generated.PartialTerm.assignLhs lhs =>
      SyntaxCtor.ctermAssign_ctor (extractLVal lhs) defaultTerm
  | Generated.PartialTerm.assignRhs lhs rhs =>
      SyntaxCtor.ctermAssign_ctor lhs (extractTerm rhs)
  | Generated.PartialTerm.boxStart =>
      SyntaxCtor.ctermBox_ctor defaultTerm
  | Generated.PartialTerm.boxOperand operand =>
      SyntaxCtor.ctermBox_ctor (extractTerm operand)
  | Generated.PartialTerm.tokenAmpStart =>
      SyntaxCtor.ctermBorrowShared_ctor defaultLVal
  | Generated.PartialTerm.borrowSharedOperand operand =>
      SyntaxCtor.ctermBorrowShared_ctor (extractLVal operand)
  | Generated.PartialTerm.borrowMutStart =>
      SyntaxCtor.ctermBorrowMut_ctor defaultLVal
  | Generated.PartialTerm.borrowMutOperand operand =>
      SyntaxCtor.ctermBorrowMut_ctor (extractLVal operand)
  | Generated.PartialTerm.moveStart =>
      SyntaxCtor.ctermMove_ctor defaultLVal
  | Generated.PartialTerm.moveOperand operand =>
      SyntaxCtor.ctermMove_ctor (extractLVal operand)
  | Generated.PartialTerm.copyStart =>
      SyntaxCtor.ctermCopy_ctor defaultLVal
  | Generated.PartialTerm.copyOperand operand =>
      SyntaxCtor.ctermCopy_ctor (extractLVal operand)
  | Generated.PartialTerm.termPrefix lhs =>
      SyntaxCtor.ctermEq_ctor (extractTerm lhs) defaultTerm
  | Generated.PartialTerm.eqRhs lhs rhs =>
      SyntaxCtor.ctermEq_ctor lhs (extractTerm rhs)
  | Generated.PartialTerm.iteStart =>
      SyntaxCtor.ctermIte_ctor (SyntaxCtor.ctermTrue_ctor) defaultTerm defaultTerm
  | Generated.PartialTerm.iteCondition condition =>
      SyntaxCtor.ctermIte_ctor (extractTerm condition) defaultTerm defaultTerm
  | Generated.PartialTerm.iteTrueBranch condition trueBranch =>
      SyntaxCtor.ctermIte_ctor condition (extractTerm trueBranch) defaultTerm
  | Generated.PartialTerm.iteFalseBranch condition trueBranch falseBranch =>
      SyntaxCtor.ctermIte_ctor condition trueBranch (extractTerm falseBranch)

def extractTerms : PartialTerms → List Term
  | Generated.PartialTerms.cutoff => []
  | Generated.PartialTerms.done xs => xs
  | Generated.PartialTerms.elems pre none => pre
  | Generated.PartialTerms.elems pre (some tail) => pre ++ [extractTerm tail]

end

def extractProgram : PartialProgram → Program :=
  extractTerm

theorem extractProgram_wellTyped_of_completion
    {p : PartialProgram} {full : Program}
    (hCompletion : CompletesProgram p full)
    (hFull : ProgramWellTyped full) :
    ProgramWellTyped (extractProgram p) := by
  sorry

theorem extractor_wellTyped_conservative :
    Conservative ProgramWellTyped CompletesProgram extractProgram := by
  intro p hInvalid full hCompletion hFull
  exact hInvalid (extractProgram_wellTyped_of_completion hCompletion hFull)

theorem extractor_wellTyped_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CompletesProgram
      (ExtractorPrefixChecker programWellTyped extractProgram) := by
  exact conservative_extractors_give_complete_prefix_checkers
    extractor_wellTyped_conservative
    programWellTyped_complete

end ConservativeExtractor
