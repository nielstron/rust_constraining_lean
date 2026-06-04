import LwRust.Definitions
import LwRust.PartialProgram

/-!
A generated-grammar nested frontier extractor.

The handwritten partial-program syntax used to let a `PartialStmt` complete
directly to a `Block`.  In the generated grammar that expressivity lives at the
statement-list level:

  * `CompletesStmt : PartialStmt → Stmt → Prop`
  * `CompletesStmts : PartialStmts → Block → Prop`

The extractor follows that shape: list frontiers keep their completed prefix and
then recursively mine checks from the single partial tail.
-/

namespace LwRust

def panicStmt : Stmt := Stmt.expr Expr.panic

def panicBlock : Block := [panicStmt]

def flattenBlocks : List Block → Block
  | [] => []
  | block :: rest => block ++ flattenBlocks rest

mutual

def extractExprsChecks : PartialExprs → Block
  | Generated.PartialExprs.done es => es.map Stmt.expr
  | Generated.PartialExprs.cutoff => []
  | Generated.PartialExprs.elems pre none => pre.map Stmt.expr
  | Generated.PartialExprs.elems pre (some tail) =>
      pre.map Stmt.expr ++ extractExprChecks tail

def extractBlocksChecks : PartialBlocks → Block
  | Generated.PartialBlocks.done blocks => flattenBlocks blocks
  | Generated.PartialBlocks.cutoff => []
  | Generated.PartialBlocks.elems pre none => flattenBlocks pre
  | Generated.PartialBlocks.elems pre (some tail) =>
      flattenBlocks pre ++ extractBlock tail

def extractExprChecks : PartialExpr → Block
  | Generated.PartialExpr.cutoff => []
  | Generated.PartialExpr.done _ => []
  | Generated.PartialExpr.intN _ => []
  | Generated.PartialExpr.exprPrefix lhs => extractExprChecks lhs
  | Generated.PartialExpr.addRhs lhs rhs => Stmt.expr lhs :: extractExprChecks rhs
  | Generated.PartialExpr.eqRhs lhs rhs => Stmt.expr lhs :: extractExprChecks rhs
  | Generated.PartialExpr.callArgs _ args => extractExprsChecks args
  | Generated.PartialExpr.caseTagBranches _ branches => extractBlocksChecks branches
  | _ => []

def extractStmt : PartialStmt → Block
  | Generated.PartialStmt.done s => [s]
  | Generated.PartialStmt.cutoff => []
  | Generated.PartialStmt.exprE e => extractExprChecks e
  | Generated.PartialStmt.letE _ _ e => extractExprChecks e
  | Generated.PartialStmt.assignE _ e => extractExprChecks e
  | Generated.PartialStmt.blockBody body => [Stmt.block (extractBlock body)]
  | Generated.PartialStmt.funDefBody name params ret body =>
      [Stmt.funDef name params ret (extractBlock body)]
  | _ => []

def extractStmts : PartialStmts → Block
  | Generated.PartialStmts.done xs => xs
  | Generated.PartialStmts.cutoff => []
  | Generated.PartialStmts.elems pre none => pre
  | Generated.PartialStmts.elems pre (some tail) => pre ++ extractStmt tail

def extractBlock : PartialBlock → Block
  | Generated.PartialBlock.done body => body
  | Generated.PartialBlock.cutoff => []
  | Generated.PartialBlock.bracesStmts stmts => extractStmts stmts

end

def extractProgram : PartialProgram → Program := extractBlock

end LwRust
