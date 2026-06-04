import LwRust.CompleteProgram

/-!
Template for grammar-derived partial syntax.

The generator replaces the marker below with declarations derived from the
complete syntax in `CompleteProgram.lean`.
-/

namespace LwRust
namespace Generated

inductive PartialName where
  | cutoff
  | done (x : Name)
  | prefix (x : Name)
  deriving Repr

mutual

inductive PartialTys where
  | cutoff
  | done (xs : List Ty)
  | elems (pre : List Ty) (tail : Option PartialTy)
  deriving Repr

inductive PartialExprs where
  | cutoff
  | done (xs : List Expr)
  | elems (pre : List Expr) (tail : Option PartialExpr)
  deriving Repr

inductive PartialStmts where
  | cutoff
  | done (xs : List Stmt)
  | elems (pre : List Stmt) (tail : Option PartialStmt)
  deriving Repr

inductive PartialBlocks where
  | cutoff
  | done (xs : List Block)
  | elems (pre : List Block) (tail : Option PartialBlock)
  deriving Repr

inductive PartialParams where
  | cutoff
  | done (xs : List (Name × Ty))
  | elems (pre : List (Name × Ty)) (tail : Option PartialParam)
  deriving Repr

inductive PartialTy where
  | cutoff
  | done (x : Ty)
  -- derived from: Ty.prod {fields}
  | prodFields (fields : PartialTys)
  -- derived from: Ty.sum {variants}
  | sumVariants (variants : PartialTys)
  -- derived from: Ty.fn {params} {ret}
  | fnParamTys (params : PartialTys)
  | fnRet (params : List Ty) (ret : PartialTy)
  -- derived from: Ty.sharedRef {τ}
  | sharedRefΤ (τ : PartialTy)
  -- derived from: Ty.mutRef {τ}
  | mutRefΤ (τ : PartialTy)
  deriving Repr

inductive PartialPlace where
  | cutoff
  | done (x : Place)
  -- derived from: Place.var {x}
  | varX (x : PartialName)
  -- derived from: Place.field {base} {index}
  | fieldBase (base : PartialPlace)
  | fieldIndex (base : Place) (index : Nat)
  | fieldDot (base : Place)
  deriving Repr

inductive PartialExpr where
  | cutoff
  | done (x : Expr)
  -- derived from: Expr.int {n}
  | intN (n : Int)
  -- derived from: Expr.place {p}
  | placeP (p : PartialPlace)
  -- derived from: Expr.deref {p}
  | derefP (p : PartialPlace)
  -- derived from: Expr.place (Place.var {f}); Expr.call {f} {args}
  | namePrefix (f : PartialName)
  -- derived from: Expr.add {lhs} {rhs}; Expr.eq {lhs} {rhs}
  | exprPrefix (lhs : PartialExpr)
  -- derived from: Expr.add {lhs} {rhs}
  | addRhs (lhs : Expr) (rhs : PartialExpr)
  -- derived from: Expr.eq {lhs} {rhs}
  | eqRhs (lhs : Expr) (rhs : PartialExpr)
  -- derived from: Expr.call {f} {args}
  | callArgs (f : Name) (args : PartialExprs)
  -- derived from: Expr.caseTag {p} {branches}
  | caseTagP (p : PartialPlace)
  | caseTagBranches (p : Place) (branches : PartialBlocks)
  deriving Repr

inductive PartialStmt where
  | cutoff
  | done (x : Stmt)
  -- derived from: Stmt.expr {e}
  | exprE (e : PartialExpr)
  -- derived from: Stmt.letStmt {x} {τ} {e}
  | letX (x : PartialName)
  | letΤ (x : Name) (τ : PartialTy)
  | letE (x : Name) (τ : Ty) (e : PartialExpr)
  -- derived from: Stmt.assign {p} {e}
  | assignP (p : PartialPlace)
  | assignE (p : Place) (e : PartialExpr)
  -- derived from: Stmt.block {body}
  | blockBody (body : PartialBlock)
  -- derived from: Stmt.funDef {name} {params} {ret} {body}
  | funDefName (name : PartialName)
  | funDefParams (name : Name) (params : PartialParams)
  | funDefRet (name : Name) (params : List (Name × Ty)) (ret : PartialTy)
  | funDefBody (name : Name) (params : List (Name × Ty)) (ret : Ty) (body : PartialBlock)
  deriving Repr

inductive PartialBlock where
  | cutoff
  | done (x : Block)
  -- derived from: {stmts}
  | bracesStmts (stmts : PartialStmts)
  deriving Repr

inductive PartialBranch where
  | cutoff
  | done (x : (Name × Block))
  -- derived from: ({x}, {body})
  | namedX (x : PartialName)
  | namedBody (x : Name) (body : PartialBlock)
  deriving Repr

inductive PartialParam where
  | cutoff
  | done (x : (Name × Ty))
  -- derived from: ({x}, {τ})
  | namedX (x : PartialName)
  | namedΤ (x : Name) (τ : PartialTy)
  deriving Repr

end

abbrev PartialProgram := PartialBlock

inductive CompletesName : PartialName → Name → Prop where
  | done {x} :
      CompletesName (PartialName.done x) x
  | cutoff {x} :
      CompletesName PartialName.cutoff x
  | prefix {x y} :
      CompletesName (PartialName.prefix x) y

mutual

inductive CompletesTys : PartialTys → List Ty → Prop where
  | done {xs} :
      CompletesTys (PartialTys.done xs) xs
  | cutoff {xs} :
      CompletesTys PartialTys.cutoff xs
  | elemsDone {pre : List Ty} {suffix : List Ty} :
      CompletesTys (PartialTys.elems pre none) (pre ++ suffix)
  | elemsTail {pre : List Ty} {suffix : List Ty} {frontier : PartialTy} {frontierCompletion : Ty} :
      CompletesTy frontier frontierCompletion →
      CompletesTys (PartialTys.elems pre (some frontier)) (pre ++ frontierCompletion :: suffix)

inductive CompletesExprs : PartialExprs → List Expr → Prop where
  | done {xs} :
      CompletesExprs (PartialExprs.done xs) xs
  | cutoff {xs} :
      CompletesExprs PartialExprs.cutoff xs
  | elemsDone {pre : List Expr} {suffix : List Expr} :
      CompletesExprs (PartialExprs.elems pre none) (pre ++ suffix)
  | elemsTail {pre : List Expr} {suffix : List Expr} {frontier : PartialExpr} {frontierCompletion : Expr} :
      CompletesExpr frontier frontierCompletion →
      CompletesExprs (PartialExprs.elems pre (some frontier)) (pre ++ frontierCompletion :: suffix)

inductive CompletesStmts : PartialStmts → List Stmt → Prop where
  | done {xs} :
      CompletesStmts (PartialStmts.done xs) xs
  | cutoff {xs} :
      CompletesStmts PartialStmts.cutoff xs
  | elemsDone {pre : List Stmt} {suffix : List Stmt} :
      CompletesStmts (PartialStmts.elems pre none) (pre ++ suffix)
  | elemsTail {pre : List Stmt} {suffix : List Stmt} {frontier : PartialStmt} {frontierCompletion : Stmt} :
      CompletesStmt frontier frontierCompletion →
      CompletesStmts (PartialStmts.elems pre (some frontier)) (pre ++ frontierCompletion :: suffix)

inductive CompletesBlocks : PartialBlocks → List Block → Prop where
  | done {xs} :
      CompletesBlocks (PartialBlocks.done xs) xs
  | cutoff {xs} :
      CompletesBlocks PartialBlocks.cutoff xs
  | elemsDone {pre : List Block} {suffix : List Block} :
      CompletesBlocks (PartialBlocks.elems pre none) (pre ++ suffix)
  | elemsTail {pre : List Block} {suffix : List Block} {frontier : PartialBlock} {frontierCompletion : Block} :
      CompletesBlock frontier frontierCompletion →
      CompletesBlocks (PartialBlocks.elems pre (some frontier)) (pre ++ frontierCompletion :: suffix)

inductive CompletesParams : PartialParams → List (Name × Ty) → Prop where
  | done {xs} :
      CompletesParams (PartialParams.done xs) xs
  | cutoff {xs} :
      CompletesParams PartialParams.cutoff xs
  | elemsDone {pre : List (Name × Ty)} {suffix : List (Name × Ty)} :
      CompletesParams (PartialParams.elems pre none) (pre ++ suffix)
  | elemsTail {pre : List (Name × Ty)} {suffix : List (Name × Ty)} {frontier : PartialParam} {frontierCompletion : (Name × Ty)} :
      CompletesParam frontier frontierCompletion →
      CompletesParams (PartialParams.elems pre (some frontier)) (pre ++ frontierCompletion :: suffix)

inductive CompletesTy : PartialTy → Ty → Prop where
  | done {x} :
      CompletesTy (PartialTy.done x) x
  | cutoff {x} :
      CompletesTy PartialTy.cutoff x
  -- derived from: Ty.prod {fields}
  | ctyProd_prodFields {fields : PartialTys} {fields' : List Ty} :
      CompletesTys fields fields' →
      CompletesTy (PartialTy.prodFields fields) (Ty.prod fields')
  -- derived from: Ty.sum {variants}
  | ctySum_sumVariants {variants : PartialTys} {variants' : List Ty} :
      CompletesTys variants variants' →
      CompletesTy (PartialTy.sumVariants variants) (Ty.sum variants')
  -- derived from: Ty.fn {params} {ret}
  | ctyFn_fnParamTys {params : PartialTys} {params' : List Ty} {ret : Ty} :
      CompletesTys params params' →
      CompletesTy (PartialTy.fnParamTys params) (Ty.fn params' ret)
  | ctyFn_fnRet {params : List Ty} {ret : PartialTy} {ret' : Ty} :
      CompletesTy ret ret' →
      CompletesTy (PartialTy.fnRet params ret) (Ty.fn params ret')
  -- derived from: Ty.sharedRef {τ}
  | ctySharedRef_sharedRefΤ {τ : PartialTy} {τ' : Ty} :
      CompletesTy τ τ' →
      CompletesTy (PartialTy.sharedRefΤ τ) (Ty.sharedRef τ')
  -- derived from: Ty.mutRef {τ}
  | ctyMutRef_mutRefΤ {τ : PartialTy} {τ' : Ty} :
      CompletesTy τ τ' →
      CompletesTy (PartialTy.mutRefΤ τ) (Ty.mutRef τ')

inductive CompletesPlace : PartialPlace → Place → Prop where
  | done {x} :
      CompletesPlace (PartialPlace.done x) x
  | cutoff {x} :
      CompletesPlace PartialPlace.cutoff x
  -- derived from: Place.var {x}
  | cplaceVar_varX {x : PartialName} {x' : Name} :
      CompletesName x x' →
      CompletesPlace (PartialPlace.varX x) (Place.var x')
  -- derived from: Place.field {base} {index}
  | cplaceField_fieldBase {base : PartialPlace} {base' : Place} {index : Nat} :
      CompletesPlace base base' →
      CompletesPlace (PartialPlace.fieldBase base) (Place.field base' index)
  | cplaceField_fieldIndex {base : Place} {index : Nat} :
      CompletesPlace (PartialPlace.fieldIndex base index) (Place.field base index)
  | cplaceField_fieldDot {base : Place} {index : Nat} :
      CompletesPlace (PartialPlace.fieldDot base) (Place.field base index)

inductive CompletesExpr : PartialExpr → Expr → Prop where
  | done {x} :
      CompletesExpr (PartialExpr.done x) x
  | cutoff {x} :
      CompletesExpr PartialExpr.cutoff x
  -- derived from: Expr.int {n}
  | cexprInt_intN {n : Int} :
      CompletesExpr (PartialExpr.intN n) (Expr.int n)
  -- derived from: Expr.place {p}
  | cexprPlace_placeP {p : PartialPlace} {p' : Place} :
      CompletesPlace p p' →
      CompletesExpr (PartialExpr.placeP p) (Expr.place p')
  -- derived from: Expr.deref {p}
  | cexprDeref_derefP {p : PartialPlace} {p' : Place} :
      CompletesPlace p p' →
      CompletesExpr (PartialExpr.derefP p) (Expr.deref p')
  -- derived from: Expr.place (Place.var {f})
  | cexprName_namePrefix {f : PartialName} {f' : Name} :
      CompletesName f f' →
      CompletesExpr (PartialExpr.namePrefix f) (Expr.place (Place.var f'))
  -- derived from: Expr.add {lhs} {rhs}
  | cexprAdd_exprPrefix {lhs : PartialExpr} {lhs' : Expr} {rhs : Expr} :
      CompletesExpr lhs lhs' →
      CompletesExpr (PartialExpr.exprPrefix lhs) (Expr.add lhs' rhs)
  | cexprAdd_addRhs {lhs : Expr} {rhs : PartialExpr} {rhs' : Expr} :
      CompletesExpr rhs rhs' →
      CompletesExpr (PartialExpr.addRhs lhs rhs) (Expr.add lhs rhs')
  -- derived from: Expr.eq {lhs} {rhs}
  | cexprEq_exprPrefix {lhs : PartialExpr} {lhs' : Expr} {rhs : Expr} :
      CompletesExpr lhs lhs' →
      CompletesExpr (PartialExpr.exprPrefix lhs) (Expr.eq lhs' rhs)
  | cexprEq_eqRhs {lhs : Expr} {rhs : PartialExpr} {rhs' : Expr} :
      CompletesExpr rhs rhs' →
      CompletesExpr (PartialExpr.eqRhs lhs rhs) (Expr.eq lhs rhs')
  -- derived from: Expr.call {f} {args}
  | cexprCall_namePrefix {f : PartialName} {f' : Name} {args : List Expr} :
      CompletesName f f' →
      CompletesExpr (PartialExpr.namePrefix f) (Expr.call f' args)
  | cexprCall_callArgs {f : Name} {args : PartialExprs} {args' : List Expr} :
      CompletesExprs args args' →
      CompletesExpr (PartialExpr.callArgs f args) (Expr.call f args')
  -- derived from: Expr.caseTag {p} {branches}
  | cexprCaseTag_caseTagP {p : PartialPlace} {p' : Place} {branches : List (List Stmt)} :
      CompletesPlace p p' →
      CompletesExpr (PartialExpr.caseTagP p) (Expr.caseTag p' branches)
  | cexprCaseTag_caseTagBranches {p : Place} {branches : PartialBlocks} {branches' : List Block} :
      CompletesBlocks branches branches' →
      CompletesExpr (PartialExpr.caseTagBranches p branches) (Expr.caseTag p branches')

inductive CompletesStmt : PartialStmt → Stmt → Prop where
  | done {x} :
      CompletesStmt (PartialStmt.done x) x
  | cutoff {x} :
      CompletesStmt PartialStmt.cutoff x
  -- derived from: Stmt.expr {e}
  | cstmtExpr_exprE {e : PartialExpr} {e' : Expr} :
      CompletesExpr e e' →
      CompletesStmt (PartialStmt.exprE e) (Stmt.expr e')
  -- derived from: Stmt.letStmt {x} {τ} {e}
  | cstmtLet_letX {x : PartialName} {x' : Name} {τ : Ty} {e : Expr} :
      CompletesName x x' →
      CompletesStmt (PartialStmt.letX x) (Stmt.letStmt x' τ e)
  | cstmtLet_letΤ {x : Name} {τ : PartialTy} {τ' : Ty} {e : Expr} :
      CompletesTy τ τ' →
      CompletesStmt (PartialStmt.letΤ x τ) (Stmt.letStmt x τ' e)
  | cstmtLet_letE {x : Name} {τ : Ty} {e : PartialExpr} {e' : Expr} :
      CompletesExpr e e' →
      CompletesStmt (PartialStmt.letE x τ e) (Stmt.letStmt x τ e')
  -- derived from: Stmt.assign {p} {e}
  | cstmtAssign_assignP {p : PartialPlace} {p' : Place} {e : Expr} :
      CompletesPlace p p' →
      CompletesStmt (PartialStmt.assignP p) (Stmt.assign p' e)
  | cstmtAssign_assignE {p : Place} {e : PartialExpr} {e' : Expr} :
      CompletesExpr e e' →
      CompletesStmt (PartialStmt.assignE p e) (Stmt.assign p e')
  -- derived from: Stmt.block {body}
  | cstmtBlock_blockBody {body : PartialBlock} {body' : Block} :
      CompletesBlock body body' →
      CompletesStmt (PartialStmt.blockBody body) (Stmt.block body')
  -- derived from: Stmt.funDef {name} {params} {ret} {body}
  | cstmtFunDef_funDefName {name : PartialName} {name' : Name} {params : List (Name × Ty)} {ret : Ty} {body : List Stmt} :
      CompletesName name name' →
      CompletesStmt (PartialStmt.funDefName name) (Stmt.funDef name' params ret body)
  | cstmtFunDef_funDefParams {name : Name} {params : PartialParams} {params' : List (Name × Ty)} {ret : Ty} {body : List Stmt} :
      CompletesParams params params' →
      CompletesStmt (PartialStmt.funDefParams name params) (Stmt.funDef name params' ret body)
  | cstmtFunDef_funDefRet {name : Name} {params : List (Name × Ty)} {ret : PartialTy} {ret' : Ty} {body : List Stmt} :
      CompletesTy ret ret' →
      CompletesStmt (PartialStmt.funDefRet name params ret) (Stmt.funDef name params ret' body)
  | cstmtFunDef_funDefBody {name : Name} {params : List (Name × Ty)} {ret : Ty} {body : PartialBlock} {body' : Block} :
      CompletesBlock body body' →
      CompletesStmt (PartialStmt.funDefBody name params ret body) (Stmt.funDef name params ret body')

inductive CompletesBlock : PartialBlock → Block → Prop where
  | done {x} :
      CompletesBlock (PartialBlock.done x) x
  | cutoff {x} :
      CompletesBlock PartialBlock.cutoff x
  -- derived from: {stmts}
  | cblockBraces_bracesStmts {stmts : PartialStmts} {stmts' : List Stmt} :
      CompletesStmts stmts stmts' →
      CompletesBlock (PartialBlock.bracesStmts stmts) (stmts')

inductive CompletesBranch : PartialBranch → (Name × Block) → Prop where
  | done {x} :
      CompletesBranch (PartialBranch.done x) x
  | cutoff {x} :
      CompletesBranch PartialBranch.cutoff x
  -- derived from: ({x}, {body})
  | cbranchNamed_namedX {x : PartialName} {x' : Name} {body : Block} :
      CompletesName x x' →
      CompletesBranch (PartialBranch.namedX x) ((x', body))
  | cbranchNamed_namedBody {x : Name} {body : PartialBlock} {body' : Block} :
      CompletesBlock body body' →
      CompletesBranch (PartialBranch.namedBody x body) ((x, body'))

inductive CompletesParam : PartialParam → (Name × Ty) → Prop where
  | done {x} :
      CompletesParam (PartialParam.done x) x
  | cutoff {x} :
      CompletesParam PartialParam.cutoff x
  -- derived from: ({x}, {τ})
  | cparamNamed_namedX {x : PartialName} {x' : Name} {τ : Ty} :
      CompletesName x x' →
      CompletesParam (PartialParam.namedX x) ((x', τ))
  | cparamNamed_namedΤ {x : Name} {τ : PartialTy} {τ' : Ty} :
      CompletesTy τ τ' →
      CompletesParam (PartialParam.namedΤ x τ) ((x, τ'))

end

end Generated
end LwRust
