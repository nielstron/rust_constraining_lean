import LwRust.Generated.PartialProgram

/-!
Compatibility import for the generated partial-program grammar.

The partial syntax and completion relations are generated from the checked
complete syntax in `CompleteProgram.lean`; this module only re-exports those
declarations at the `LwRust` namespace expected by the rest of
the formalization.
-/

namespace LwRust

export Generated (
  PartialName
  PartialTys
  PartialExprs
  PartialStmts
  PartialBlocks
  PartialParams
  PartialTy
  PartialPlace
  PartialExpr
  PartialStmt
  PartialBlock
  PartialBranch
  PartialParam
  PartialProgram
  CompletesName
  CompletesTys
  CompletesExprs
  CompletesStmts
  CompletesBlocks
  CompletesParams
  CompletesTy
  CompletesPlace
  CompletesExpr
  CompletesStmt
  CompletesBlock
  CompletesBranch
  CompletesParam
)

abbrev CompletesProgram : PartialProgram → Program → Prop :=
  CompletesBlock

end LwRust
