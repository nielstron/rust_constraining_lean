import LwRust.Extractor.Checkers

/-!
A syntax-directed LwRust frontier extractor.

For list frontiers, the extractor keeps the complete prefix and recursively
extracts the single partial tail.  For incomplete expression/term frontiers, it
follows `ast_copier`'s `visit_expr`/`visit_expr_stmt` split: extract useful child
expressions as statements, but do not rebuild a constraining parent expression
such as assignment with a placeholder operand.
-/

namespace ConservativeExtractor

def missingName : Name := "_"

def missingLVal : LVal :=
  SyntaxCtor.clvalVar_ctor missingName

def missingTerm : Term :=
  .missing

def childLifetime (lifetime : Lifetime) : Lifetime :=
  { path := lifetime.path ++ [0] }

mutual

def extractLVal : PartialLVal → LVal
  | Generated.PartialLVal.cutoff => missingLVal
  | Generated.PartialLVal.done lv => lv
  | Generated.PartialLVal.varX (Generated.PartialName.done x) =>
      SyntaxCtor.clvalVar_ctor x
  | Generated.PartialLVal.varX (Generated.PartialName.prefix x) =>
      SyntaxCtor.clvalVar_ctor x
  | Generated.PartialLVal.varX Generated.PartialName.cutoff =>
      missingLVal
  | Generated.PartialLVal.derefStart =>
      SyntaxCtor.clvalDeref_ctor missingLVal
  | Generated.PartialLVal.derefOperand operand =>
      SyntaxCtor.clvalDeref_ctor (extractLVal operand)

def extractLVals : PartialLVals → List LVal
  | Generated.PartialLVals.cutoff => []
  | Generated.PartialLVals.done xs => xs
  | Generated.PartialLVals.elems pre none => pre
  | Generated.PartialLVals.elems pre (some tail) => pre ++ [extractLVal tail]

/-- Extract a partial expression in value position.

For an incomplete non-block expression, this mirrors `ast_copier.visit_expr`:
emit the statement-oriented extraction of the partial expression and finish with
`missingTerm`, rather than rebuilding the partial parent constructor.
-/
def extractTerm (currentLifetime : Lifetime) : PartialTerm → Term
  | Generated.PartialTerm.cutoff => missingTerm
  | Generated.PartialTerm.done term => term
  | Generated.PartialTerm.intN n => SyntaxCtor.ctermInt_ctor n
  | Generated.PartialTerm.blockStart =>
      SyntaxCtor.ctermBlock_ctor (childLifetime currentLifetime) [missingTerm]
  | Generated.PartialTerm.blockTerms lifetime terms =>
      SyntaxCtor.ctermBlock_ctor lifetime (extractTerms lifetime terms)
  | frontier =>
      SyntaxCtor.ctermBlock_ctor (childLifetime currentLifetime)
        (extractTermStmts currentLifetime frontier ++ [missingTerm])

/-- Extract a partial expression in statement position.

This is intentionally conservative: rebuilding `lhs := missingTerm` can mask
the actual frontier that `ast_copier.visit_expr_stmt` would inspect.  We
therefore only keep child expressions that the copier recursively visits.
-/
def extractTermStmts (currentLifetime : Lifetime) : PartialTerm → List Term
  | Generated.PartialTerm.cutoff => []
  | Generated.PartialTerm.done term => [term]
  | Generated.PartialTerm.intN _ => []
  | Generated.PartialTerm.blockStart =>
      [SyntaxCtor.ctermBlock_ctor (childLifetime currentLifetime) [missingTerm]]
  | Generated.PartialTerm.blockTerms lifetime terms =>
      [SyntaxCtor.ctermBlock_ctor lifetime (extractTerms lifetime terms)]
  | Generated.PartialTerm.letMutStart => []
  | Generated.PartialTerm.letMutName _ => []
  | Generated.PartialTerm.letMutInitialiser _ initialiser =>
      extractTermStmts currentLifetime initialiser
  | Generated.PartialTerm.assignLhs _ => []
  | Generated.PartialTerm.assignRhs _ rhs =>
      extractTermStmts currentLifetime rhs
  | Generated.PartialTerm.boxStart => []
  | Generated.PartialTerm.boxOperand operand =>
      extractTermStmts currentLifetime operand
  | Generated.PartialTerm.tokenAmpStart => []
  | Generated.PartialTerm.borrowSharedOperand _ => []
  | Generated.PartialTerm.borrowMutStart => []
  | Generated.PartialTerm.borrowMutOperand _ => []
  | Generated.PartialTerm.moveStart => []
  | Generated.PartialTerm.moveOperand _ => []
  | Generated.PartialTerm.copyStart => []
  | Generated.PartialTerm.copyOperand _ => []
  | Generated.PartialTerm.termPrefix lhs =>
      extractTermStmts currentLifetime lhs
  | Generated.PartialTerm.eqRhs lhs rhs =>
      lhs :: extractTermStmts currentLifetime rhs
  | Generated.PartialTerm.iteStart => []
  | Generated.PartialTerm.iteCondition condition =>
      extractTermStmts currentLifetime condition
  | Generated.PartialTerm.iteTrueBranch condition trueBranch =>
      condition :: extractTermStmts currentLifetime trueBranch
  | Generated.PartialTerm.iteFalseBranch condition trueBranch falseBranch =>
      condition :: trueBranch :: extractTermStmts currentLifetime falseBranch

def extractTerms (currentLifetime : Lifetime) : PartialTerms → List Term
  | Generated.PartialTerms.cutoff => []
  | Generated.PartialTerms.done xs => xs
  | Generated.PartialTerms.elems pre none => pre
  | Generated.PartialTerms.elems pre (some tail) =>
      pre ++ extractTermStmts currentLifetime tail ++ [missingTerm]

end

def extractProgram : PartialProgram → Program :=
  extractTerm LwRust.Core.Lifetime.root

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
