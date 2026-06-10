import LwRust.Extractor.Extractors.Empty

/-!
A syntax-directed LwRust frontier extractor.

For list frontiers, the extractor keeps the complete prefix and recursively
extracts the single partial tail.  For expression/term frontiers, it reconstructs
the LwRust constructor and fills unavailable siblings with `unit`.
-/

namespace ConservativeExtractor

mutual

def extractLVal : PartialLVal → LVal
  | Generated.PartialLVal.cutoff => .var "_"
  | Generated.PartialLVal.done lv => lv
  | Generated.PartialLVal.varName (Generated.PartialName.done x) => .var x
  | Generated.PartialLVal.varName (Generated.PartialName.prefix x) => .var x
  | Generated.PartialLVal.varName Generated.PartialName.cutoff => .var "_"
  | Generated.PartialLVal.derefOperand operand => .deref (extractLVal operand)

def extractLVals : PartialLVals → List LVal
  | Generated.PartialLVals.cutoff => []
  | Generated.PartialLVals.done xs => xs
  | Generated.PartialLVals.elems pre none => pre
  | Generated.PartialLVals.elems pre (some tail) => pre ++ [extractLVal tail]

def extractValue : PartialValue → Value
  | Generated.PartialValue.cutoff => .unit
  | Generated.PartialValue.done value => value
  | Generated.PartialValue.intValue n => .int n
  | Generated.PartialValue.boolValue b => .bool b

def extractTerm : PartialTerm → Term
  | Generated.PartialTerm.cutoff => .val .unit
  | Generated.PartialTerm.done term => term
  | Generated.PartialTerm.blockTerms lifetime terms =>
      .block lifetime (extractTerms terms)
  | Generated.PartialTerm.letMutName (Generated.PartialName.done x) =>
      .letMut x (.val .unit)
  | Generated.PartialTerm.letMutName (Generated.PartialName.prefix x) =>
      .letMut x (.val .unit)
  | Generated.PartialTerm.letMutName Generated.PartialName.cutoff =>
      .letMut "_" (.val .unit)
  | Generated.PartialTerm.letMutInitialiser name initialiser =>
      .letMut name (extractTerm initialiser)
  | Generated.PartialTerm.assignLhs lhs =>
      .assign (extractLVal lhs) (.val .unit)
  | Generated.PartialTerm.assignRhs lhs rhs =>
      .assign lhs (extractTerm rhs)
  | Generated.PartialTerm.boxOperand operand =>
      .box (extractTerm operand)
  | Generated.PartialTerm.borrowOperand mutable operand =>
      .borrow mutable (extractLVal operand)
  | Generated.PartialTerm.moveOperand operand =>
      .move (extractLVal operand)
  | Generated.PartialTerm.copyOperand operand =>
      .copy (extractLVal operand)
  | Generated.PartialTerm.valValue value =>
      .val (extractValue value)
  | Generated.PartialTerm.eqLhs lhs =>
      .eq (extractTerm lhs) (.val .unit)
  | Generated.PartialTerm.eqRhs lhs rhs =>
      .eq lhs (extractTerm rhs)
  | Generated.PartialTerm.iteCondition condition =>
      .ite (extractTerm condition) (.val .unit) (.val .unit)
  | Generated.PartialTerm.iteTrueBranch condition trueBranch =>
      .ite condition (extractTerm trueBranch) (.val .unit)
  | Generated.PartialTerm.iteFalseBranch condition trueBranch falseBranch =>
      .ite condition trueBranch (extractTerm falseBranch)

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
      (ExtractorPrefixChecker exactProgramChecker extractProgram) := by
  exact conservative_extractors_give_complete_prefix_checkers
    extractor_wellTyped_conservative
    exactProgramChecker_complete

theorem extractProgram_borrow_of_completion
    {p : PartialProgram} {full : Program}
    (_hCompletion : CompletesProgram p full)
    (_hFull : ProgramBorrowOk full) :
    ProgramBorrowOk (extractProgram p) := by
  trivial

theorem extractor_borrow_conservative :
    Conservative ProgramBorrowOk CompletesProgram extractProgram := by
  intro p hInvalid full hCompletion hFull
  exact hInvalid (extractProgram_borrow_of_completion hCompletion hFull)

theorem extractor_borrow_prefixChecker_complete :
    PrefixCheckerComplete ProgramBorrowOk CompletesProgram
      (ExtractorPrefixChecker exactBorrowChecker extractProgram) := by
  exact conservative_extractors_give_complete_prefix_checkers
    extractor_borrow_conservative
    exactBorrowChecker_complete

theorem extractProgram_lifetimeBorrow_of_completion
    {p : PartialProgram} {full : Program}
    (hCompletion : CompletesProgram p full)
    (hFull : ProgramLifetimeBorrowOk full) :
    ProgramLifetimeBorrowOk (extractProgram p) := by
  sorry

theorem extractor_lifetimeBorrow_conservative :
    Conservative ProgramLifetimeBorrowOk CompletesProgram
      extractProgram := by
  intro p hInvalid full hCompletion hFull
  exact hInvalid
    (extractProgram_lifetimeBorrow_of_completion hCompletion hFull)

theorem extractor_lifetimeBorrow_prefixChecker_complete :
    PrefixCheckerComplete ProgramLifetimeBorrowOk CompletesProgram
      (ExtractorPrefixChecker exactLifetimeBorrowChecker extractProgram) := by
  exact conservative_extractors_give_complete_prefix_checkers
    extractor_lifetimeBorrow_conservative
    exactLifetimeBorrowChecker_complete

end ConservativeExtractor
