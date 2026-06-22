import LwRust.Extractor.Checkers

/-!
A syntax-directed LwRust frontier extractor mirroring `rust_constraining`'s
`ast_copier.rs`.

Correspondence with `ast_copier`:

* `extractTerm` ↔ `visit_expr`: extract a partial expression in value
  position (only reached at the program root).
* `extractTermStmts` ↔ `visit_expr_stmt`: demote a partial expression to the
  statement extraction of the child expressions the copier recursively
  visits, without rebuilding a constraining parent expression.
* `extractTerms` ↔ `visit_stmts`: keep the complete statement prefix,
  statement-extract the partial tail, and close the block with `missingTerm`
  exactly as `visit_stmts` closes an incomplete block with `__missing__()}`.

Deviations from `ast_copier`, each forced by the LwRust type system rather
than chosen freely:

* Assignments: `ast_copier` rebuilds `lhs = <rhs extraction>;` around a
  partial right-hand side.  `T-Assign` carries environment-dependent
  obligations (lhs re-typing, shape compatibility, write coherence, borrow
  target bounds) stated in the environment *after* the full right-hand side;
  they do not transport to the environment of a truncated right-hand side, so
  only the statement extraction of the right-hand side is kept.
* Conditionals are rebuilt the way `ast_copier` rebuilds them — `if cond
  { … } else { …; panic!() }` — using the divergence-aware rule `T-IfDiv`
  (`TermTyping.iteDiverging`), the calculus' counterpart of rustc's
  never-type propagation: the truncated branch is fully checked but, since it
  diverges, contributes nothing to the merge.  Branch and loop-body frontiers
  are extracted through `extractBlockTerm`, so rebuilt `if`/`while` bodies are
  always syntactic blocks.  Unrealistic non-block branch frontiers from the
  generated grammar are replaced by a synthesized diverging block.
* Value position: `ast_copier` wraps the statement extraction in an anonymous
  `{ …; __missing__() }` block.  LwRust blocks carry explicit lifetimes and
  `T-Block` pins them to the ambient lifetime chain, so source statements
  (which may contain source blocks with source lifetimes) cannot be relocated
  under a synthesized block.  `extractTerm` instead keeps the first extracted
  statement, or `missingTerm` if there is none.
* Lvalues: there is no chameleon lvalue analogous to `__missing__<T>()` — a
  placeholder in lvalue position cannot be conservative — so lvalue frontiers
  are dropped, matching `ast_copier`, which never synthesizes a place
  expression.
-/

namespace ConservativeExtractor

/-- The LwRust analogue of `ast_copier`'s `__missing__<T>()` placeholder. -/
abbrev missingTerm : Term :=
  .missing

/-- The lifetime of a synthesized block nested directly below `lifetime`.
Source blocks keep their source lifetime; only blocks invented by the
extractor (for an unopened block frontier) use this. -/
def childLifetime (lifetime : Lifetime) : Lifetime :=
  { path := lifetime.path ++ [0] }

/-- A synthesized diverging block nested directly below `lifetime`. -/
def missingBlockTerm (lifetime : Lifetime) : Term :=
  SyntaxCtor.ctermBlock_ctor (childLifetime lifetime) [missingTerm]

/-- Syntactic block test for complete terms used in block-position extraction. -/
def termIsBlock : Term → Bool
  | .block _ _ => Bool.true
  | _ => Bool.false

/-- Keep an already block-shaped complete term; otherwise replace it by a
synthetic block.  This is only used in Rust block positions (`if` branches and
while bodies), where a complete non-block term is outside the intended source
grammar. -/
def blockOrMissing (currentLifetime : Lifetime) : Term → Term
  | .block lifetime terms => .block lifetime terms
  | _ => missingBlockTerm currentLifetime

mutual

/-- Syntactic Rust-shape restriction: every source `if` branch and `while`
body is a block.  This is intentionally separate from typing. -/
def controlBodiesBlock : Term → Prop
  | .block _ terms => controlBodiesBlockList terms
  | .letMut _ initialiser => controlBodiesBlock initialiser
  | .assign _ rhs => controlBodiesBlock rhs
  | .box operand => controlBodiesBlock operand
  | .borrow _ _ => True
  | .move _ => True
  | .copy _ => True
  | .val _ => True
  | .missing => True
  | .eq lhs rhs => controlBodiesBlock lhs ∧ controlBodiesBlock rhs
  | .ite condition trueBranch falseBranch =>
      controlBodiesBlock condition ∧
        termIsBlock trueBranch = Bool.true ∧ controlBodiesBlock trueBranch ∧
        termIsBlock falseBranch = Bool.true ∧ controlBodiesBlock falseBranch
  | .whileLoop _ condition body =>
      controlBodiesBlock condition ∧
        termIsBlock body = Bool.true ∧ controlBodiesBlock body
  | .whileCond _ conditionInFlight condition body =>
      controlBodiesBlock conditionInFlight ∧ controlBodiesBlock condition ∧
        controlBodiesBlock body
  | .whileBody _ bodyInFlight condition body =>
      controlBodiesBlock bodyInFlight ∧ controlBodiesBlock condition ∧
        controlBodiesBlock body

/-- List form of `controlBodiesBlock` for block bodies. -/
def controlBodiesBlockList : List Term → Prop
  | [] => True
  | term :: rest => controlBodiesBlock term ∧ controlBodiesBlockList rest

end

/-- Completion relation restricted to Rust-shaped outputs. -/
def BlockOutputCompletesProgram (p : PartialProgram) (full : Program) : Prop :=
  CompletesProgram p full ∧ controlBodiesBlock full

mutual

/-- Extract a partial expression in value position (`ast_copier.visit_expr`).

`currentLifetime` is the lifetime at which the extracted term will be typed.
This is only reached at the program root; see the module docstring for why
the statement extraction cannot be wrapped in a synthesized block here. -/
def extractTerm (currentLifetime : Lifetime) : PartialTerm → Term
  | Generated.PartialTerm.cutoff => missingTerm
  | Generated.PartialTerm.done term => term
  | Generated.PartialTerm.intN n => SyntaxCtor.ctermInt_ctor n
  | Generated.PartialTerm.blockStart =>
      SyntaxCtor.ctermBlock_ctor (childLifetime currentLifetime) [missingTerm]
  | Generated.PartialTerm.blockTerms lifetime terms =>
      SyntaxCtor.ctermBlock_ctor lifetime (extractTerms lifetime terms)
  | frontier =>
      (extractTermStmts currentLifetime frontier).headD missingTerm
termination_by p => (sizeOf p, 1)

/-- Extract a frontier that sits in a Rust block position, such as an `if`
branch or while body.  The result is always syntactically a block. -/
def extractBlockTerm (currentLifetime : Lifetime) : PartialTerm → Term
  | Generated.PartialTerm.done term => blockOrMissing currentLifetime term
  | Generated.PartialTerm.blockStart => missingBlockTerm currentLifetime
  | Generated.PartialTerm.blockTerms lifetime terms =>
      SyntaxCtor.ctermBlock_ctor lifetime (extractTerms lifetime terms)
  | _ => missingBlockTerm currentLifetime
termination_by p => (sizeOf p, 1)

/-- Extract a partial expression in statement position
(`ast_copier.visit_expr_stmt`): keep the child expressions the copier
recursively visits, do not rebuild a constraining parent.

`currentLifetime` is the lifetime at which the extracted statements will be
typed — the body lifetime of the enclosing block. -/
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
      [SyntaxCtor.ctermIte_ctor condition
        (extractBlockTerm currentLifetime trueBranch)
        (missingBlockTerm currentLifetime)]
  | Generated.PartialTerm.iteFalseBranch condition trueBranch falseBranch =>
      if termIsBlock trueBranch then
        [SyntaxCtor.ctermIte_ctor condition trueBranch
          (extractBlockTerm currentLifetime falseBranch)]
      else
        [SyntaxCtor.ctermIte_ctor condition
          (missingBlockTerm currentLifetime)
          (missingBlockTerm currentLifetime)]
  | Generated.PartialTerm.whileStart => []
  | Generated.PartialTerm.whileCondition _bodyLifetime condition =>
      extractTermStmts currentLifetime condition
  | Generated.PartialTerm.whileBody bodyLifetime condition body =>
      [SyntaxCtor.ctermWhile_ctor bodyLifetime condition
        (extractBlockTerm bodyLifetime body)]
termination_by p => (sizeOf p, 0)

/-- Extract a block body frontier (`ast_copier.visit_stmts`): keep the
complete prefix, statement-extract the partial tail, close with
`missingTerm`.  The closing placeholder both mirrors `visit_stmts` writing
`__missing__()}` and keeps the body non-empty (T-Seq has no empty
sequence). -/
def extractTerms (currentLifetime : Lifetime) : PartialTerms → List Term
  | Generated.PartialTerms.cutoff => [missingTerm]
  | Generated.PartialTerms.done xs => xs
  | Generated.PartialTerms.elems pre none => pre ++ [missingTerm]
  | Generated.PartialTerms.elems pre (some tail) =>
      pre ++ extractTermStmts currentLifetime tail ++ [missingTerm]
termination_by ps => (sizeOf ps, 0)

end

def extractProgram : PartialProgram → Program :=
  extractTerm LwRust.Core.Lifetime.root

/-!
Typing transport: a well-typed completion yields a well-typed extraction.

The proof threads the typing derivation of the completion through the
extraction.  Complete subterms reuse their sub-derivations verbatim (in the
same environment, store typing, and lifetime they had in the completion), and
every synthesized `missingTerm` is typed at `.unit` by `T-Missing`.
-/

section TypedExtraction

open LwRust.Paper

theorem tyLoanFree_unit : TyLoanFree .unit := by
  intro _mutable _targets hcontains
  cases hcontains

/-- Sequential statement typing: `TermListTyping` without a result type, so
that it also covers the empty statement run.  The statement extraction of a
frontier is typed by this relation; closing the run with `missingTerm`
upgrades it to a `TermListTyping` of result type `.unit`. -/
inductive StmtsTyping :
    Env → StoreTyping → Lifetime → List Term → Env → Prop where
  | nil {env : Env} {typing : StoreTyping} {lifetime : Lifetime} :
      StmtsTyping env typing lifetime [] env
  | cons {env₁ env₂ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
      {term : Term} {rest : List Term} {ty : Ty} :
      TermTyping env₁ typing lifetime term ty env₂ →
      StmtsTyping env₂ typing lifetime rest env₃ →
      StmtsTyping env₁ typing lifetime (term :: rest) env₃

theorem termListTyping_toStmts {typing : StoreTyping} {lifetime : Lifetime}
    {terms : List Term} :
    ∀ {env env₂ : Env} {ty : Ty},
      TermListTyping env typing lifetime terms ty env₂ →
      StmtsTyping env typing lifetime terms env₂ := by
  induction terms with
  | nil =>
      intro env env₂ ty hlist
      cases hlist
  | cons term rest ih =>
      intro env env₂ ty hlist
      cases hlist with
      | singleton hterm => exact .cons hterm .nil
      | cons hterm hrest => exact .cons hterm (ih hrest)

theorem stmtsTyping_append {env mid env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {xs ys : List Term}
    (hxs : StmtsTyping env typing lifetime xs mid) :
    StmtsTyping mid typing lifetime ys env₂ →
    StmtsTyping env typing lifetime (xs ++ ys) env₂ := by
  induction hxs with
  | nil => exact fun hys => hys
  | cons hterm _ ih => exact fun hys => .cons hterm (ih hys)

theorem stmtsTyping_append_inv {typing : StoreTyping} {lifetime : Lifetime}
    {xs ys : List Term} :
    ∀ {env env₂ : Env},
      StmtsTyping env typing lifetime (xs ++ ys) env₂ →
      ∃ mid, StmtsTyping env typing lifetime xs mid ∧
        StmtsTyping mid typing lifetime ys env₂ := by
  induction xs with
  | nil =>
      intro env env₂ hstmts
      exact ⟨env, .nil, hstmts⟩
  | cons x xs ih =>
      intro env env₂ hstmts
      cases hstmts with
      | cons hterm hrest =>
          obtain ⟨mid, hxs, hys⟩ := ih hrest
          exact ⟨mid, .cons hterm hxs, hys⟩

/-- Closing an extracted statement run with `missingTerm` yields a block body
of result type `.unit`. -/
theorem stmtsTyping_missing_closed {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List Term}
    (hstmts : StmtsTyping env typing lifetime stmts env₂) :
    TermListTyping env typing lifetime (stmts ++ [missingTerm]) .unit env₂ := by
  induction hstmts with
  | nil => exact .singleton (.missing .unit tyLoanFree_unit)
  | cons hterm _ ih => exact .cons hterm ih

/-- The synthesized block for an unopened block frontier types
unconditionally. -/
theorem missingBlock_typed {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping env typing lifetime
      (missingBlockTerm lifetime) .unit
      (env.dropLifetime (childLifetime lifetime)) :=
  TermTyping.block ⟨0, rfl⟩
    (TermListTyping.singleton (TermTyping.missing WellFormedTy.unit tyLoanFree_unit))
    WellFormedTy.unit rfl

/-- The synthesized block is syntactically diverging because its only term is
`missingTerm`. -/
theorem missingBlock_diverging {lifetime : Lifetime} :
    LwRust.Core.Term.Diverges (missingBlockTerm lifetime) := by
  unfold missingBlockTerm SyntaxCtor.ctermBlock_ctor
  exact LwRust.Core.Term.Diverges.block (by simp)
    LwRust.Core.Term.Diverges.missing

/-- `blockOrMissing` always produces a block-shaped term. -/
theorem blockOrMissing_isBlock {currentLifetime : Lifetime} {term : Term} :
    termIsBlock (blockOrMissing currentLifetime term) = Bool.true := by
  cases term <;> simp [blockOrMissing, missingBlockTerm, termIsBlock]

/-- Block-position extraction always produces a block-shaped term. -/
theorem extractBlockTerm_isBlock {currentLifetime : Lifetime} {p : PartialTerm} :
    termIsBlock (extractBlockTerm currentLifetime p) = Bool.true := by
  cases p <;> simp [extractBlockTerm, missingBlockTerm, termIsBlock]
  case done term =>
      exact blockOrMissing_isBlock

/-- A complete term kept in block position, or a synthesized block replacing it,
is always typable from the same input state when the complete term was typable. -/
theorem blockOrMissing_typed {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (htyped : TermTyping env typing lifetime term ty env₂) :
    ∃ ty' env', TermTyping env typing lifetime
      (blockOrMissing lifetime term) ty' env' := by
  cases term <;> simp [blockOrMissing]
  · exact ⟨ty, env₂, htyped⟩
  all_goals
    exact ⟨.unit, env.dropLifetime (childLifetime lifetime), missingBlock_typed⟩

/-- Every non-`done` body extraction ends in (hence contains) `missingTerm`,
so the rebuilt block diverges. -/
theorem extractTerms_diverging {currentLifetime : Lifetime} {ps : PartialTerms}
    (hne : ∀ xs, ps ≠ Generated.PartialTerms.done xs) :
    missingTerm ∈ extractTerms currentLifetime ps := by
  cases ps with
  | cutoff => simp [extractTerms]
  | done xs => exact absurd rfl (hne xs)
  | elems pre tail =>
      cases tail with
      | none => simp [extractTerms]
      | some tailTerm => simp [extractTerms]

theorem headD_typed {env env' : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List Term}
    (hstmts : StmtsTyping env typing lifetime stmts env') :
    ∃ ty' env'', TermTyping env typing lifetime
      (stmts.headD missingTerm) ty' env'' := by
  cases hstmts with
  | nil => exact ⟨.unit, env, .missing .unit tyLoanFree_unit⟩
  | cons hfirst _ => exact ⟨_, _, hfirst⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
mutual

/-- Value-position transport: only reached at the program root. -/
theorem extractTerm_typed {currentLifetime : Lifetime} {p : PartialTerm}
    {completion : Term} {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerm p completion)
    (htyped : TermTyping env typing currentLifetime completion ty env₂) :
    ∃ ty' env', TermTyping env typing currentLifetime
      (extractTerm currentLifetime p) ty' env' := by
  cases p
  case cutoff =>
      simp only [extractTerm]
      exact ⟨.unit, env, .missing .unit tyLoanFree_unit⟩
  case done =>
      cases hcomp
      simp only [extractTerm]
      exact ⟨ty, env₂, htyped⟩
  case intN =>
      cases hcomp
      simp only [extractTerm]
      exact ⟨ty, env₂, htyped⟩
  case blockStart =>
      simp only [extractTerm]
      exact ⟨.unit, _, missingBlock_typed⟩
  case blockTerms blockLifetime terms =>
      cases hcomp with
      | ctermBlock_blockTerms hterms =>
          cases htyped with
          | «block» hchild hlist hwf heq =>
              obtain ⟨ty', envBody, hlist', hdisj⟩ :=
                extractTerms_typed hterms hlist
              simp only [extractTerm]
              refine ⟨ty', envBody.dropLifetime blockLifetime,
                TermTyping.block hchild hlist' ?_ rfl⟩
              rcases hdisj with rfl | ⟨rfl, rfl⟩
              · exact WellFormedTy.unit
              · exact hwf
  all_goals
    simp only [extractTerm]
    obtain ⟨env', hstmts⟩ := extractTermStmts_typed hcomp htyped
    exact headD_typed hstmts
termination_by (sizeOf p, 1)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (simp_wf
       try subst_vars
       first
       | exact Prod.Lex.right _ (by omega)
       | exact Prod.Lex.left _ _ (by try simp; omega))

/-- Block-position transport: the extracted frontier is a block and is typable
from the same input state as any well-typed completion. -/
theorem extractBlockTerm_typed {currentLifetime : Lifetime} {p : PartialTerm}
    {completion : Term} {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerm p completion)
    (htyped : TermTyping env typing currentLifetime completion ty env₂) :
    ∃ ty' env', TermTyping env typing currentLifetime
      (extractBlockTerm currentLifetime p) ty' env' := by
  cases p
  case done =>
      cases hcomp
      simp only [extractBlockTerm]
      exact blockOrMissing_typed htyped
  case blockStart =>
      simp only [extractBlockTerm]
      exact ⟨.unit, _, missingBlock_typed⟩
  case blockTerms blockLifetime terms =>
      cases hcomp with
      | ctermBlock_blockTerms hterms =>
          cases htyped with
          | «block» hchild hlist hwf heq =>
              obtain ⟨ty', envBody, hlist', hdisj⟩ :=
                extractTerms_typed hterms hlist
              simp only [extractBlockTerm]
              refine ⟨ty', envBody.dropLifetime blockLifetime,
                TermTyping.block hchild hlist' ?_ rfl⟩
              rcases hdisj with rfl | ⟨rfl, rfl⟩
              · exact WellFormedTy.unit
              · exact hwf
  all_goals
    simp only [extractBlockTerm]
    exact ⟨.unit, _, missingBlock_typed⟩
termination_by (sizeOf p, 1)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (simp_wf
       try subst_vars
       first
       | exact Prod.Lex.right _ (by omega)
       | exact Prod.Lex.left _ _ (by try simp; omega))

/-- Statement-position transport: the statement extraction of a frontier
types sequentially from the same starting environment as the completion. -/
theorem extractTermStmts_typed {currentLifetime : Lifetime} {p : PartialTerm}
    {completion : Term} {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerm p completion)
    (htyped : TermTyping env typing currentLifetime completion ty env₂) :
    ∃ env', StmtsTyping env typing currentLifetime
      (extractTermStmts currentLifetime p) env' := by
  cases hcomp
  case done =>
      simp only [extractTermStmts]
      exact ⟨env₂, .cons htyped .nil⟩
  case ctermBlock_blockStart =>
      simp only [extractTermStmts]
      exact ⟨_, .cons missingBlock_typed .nil⟩
  case ctermBlock_blockTerms hterms =>
      cases htyped with
      | «block» hchild hlist hwf heq =>
          obtain ⟨ty', envBody, hlist', hdisj⟩ :=
            extractTerms_typed hterms hlist
          simp only [extractTermStmts]
          refine ⟨envBody.dropLifetime _,
            .cons (TermTyping.block hchild hlist' ?_ rfl) .nil⟩
          rcases hdisj with rfl | ⟨rfl, rfl⟩
          · exact WellFormedTy.unit
          · exact hwf
  case ctermLetMut_letMutInitialiser hinit =>
      cases htyped with
      | declare _ hinit' _ _ _ =>
          simp only [extractTermStmts]
          exact extractTermStmts_typed hinit hinit'
  case ctermAssign_assignRhs hrhs =>
      cases htyped with
      | assign _ hrhs' _ _ _ _ _ _ _ _ =>
          simp only [extractTermStmts]
          exact extractTermStmts_typed hrhs hrhs'
  case ctermBox_boxOperand hoperand =>
      cases htyped with
      | «box» hoperand' =>
          simp only [extractTermStmts]
          exact extractTermStmts_typed hoperand hoperand'
  case ctermEq_termPrefix hlhs =>
      cases htyped with
      | eq hlhs' =>
          simp only [extractTermStmts]
          exact extractTermStmts_typed hlhs hlhs'
  case ctermEq_eqRhs hrhs =>
      cases htyped with
      | eq hlhs' _ _ hrhs' =>
          obtain ⟨env', hstmts⟩ := extractTermStmts_typed hrhs hrhs'
          simp only [extractTermStmts]
          exact ⟨env', .cons hlhs' hstmts⟩
  case ctermIte_iteCondition hcondition =>
      simp only [extractTermStmts]
      cases htyped with
      | ite hcondition' =>
          exact extractTermStmts_typed hcondition hcondition'
      | iteDiverging hcondition' =>
          exact extractTermStmts_typed hcondition hcondition'
  case ctermIte_iteTrueBranch condition trueBranch trueCompletion
      falseCompletion htrue =>
      obtain ⟨envMid, hcondition', tyLive, envOut, htrue'⟩ :
          ∃ envMid,
            TermTyping env typing currentLifetime condition .bool envMid ∧
            ∃ tyLive envOut,
              TermTyping envMid typing currentLifetime trueCompletion tyLive
                envOut := by
        cases htyped with
        | ite hcondition' htrue' => exact ⟨_, hcondition', _, _, htrue'⟩
        | iteDiverging hcondition' htrue' => exact ⟨_, hcondition', _, _, htrue'⟩
      simp only [extractTermStmts]
      obtain ⟨tyLive', envLive, hlive⟩ := extractBlockTerm_typed htrue htrue'
      exact ⟨envLive, .cons
        (TermTyping.iteDiverging hcondition' hlive
          missingBlock_typed missingBlock_diverging) .nil⟩
  case ctermIte_iteFalseBranch condition trueBranch falseBranch
      falseCompletion hfalse =>
      obtain ⟨envMid, hcondition', tyLive, envOut, htrue', tyDead, envDead,
          hfalse'⟩ :
          ∃ envMid,
            TermTyping env typing currentLifetime condition .bool envMid ∧
            ∃ tyLive envOut,
              TermTyping envMid typing currentLifetime trueBranch tyLive
                envOut ∧
              ∃ tyDead envDead,
                TermTyping envMid typing currentLifetime falseCompletion
                  tyDead envDead := by
        cases htyped with
        | ite hcondition' htrue' hfalse' =>
            exact ⟨_, hcondition', _, _, htrue', _, _, hfalse'⟩
        | iteDiverging hcondition' htrue' hfalse' =>
            exact ⟨_, hcondition', _, _, htrue', _, _, hfalse'⟩
      simp only [extractTermStmts]
      cases htrueBlock : termIsBlock trueBranch
      case «false» =>
          simp
          exact ⟨envMid.dropLifetime (childLifetime currentLifetime), .cons
            (TermTyping.iteDiverging hcondition' missingBlock_typed
              missingBlock_typed missingBlock_diverging) .nil⟩
      case «true» =>
          cases trueBranch <;> simp [termIsBlock] at htrueBlock
          case «block» trueLifetime trueTerms =>
              cases falseBranch
              case done =>
                  cases hfalse
                  cases falseCompletion <;> simp [extractBlockTerm, blockOrMissing]
                  · exact ⟨env₂, .cons htyped .nil⟩
                  all_goals
                    exact ⟨envOut, .cons
                      (TermTyping.iteDiverging hcondition' htrue'
                        missingBlock_typed missingBlock_diverging) .nil⟩
              case blockTerms blockLifetime terms =>
                  cases hfalse with
                  | ctermBlock_blockTerms hterms =>
                      cases terms
                      case done xs =>
                          cases hterms
                          simp [extractBlockTerm, extractTerms]
                          exact ⟨env₂, .cons htyped .nil⟩
                      all_goals
                        cases hfalse' with
                        | «block» hchild hlist hwf _heq =>
                            obtain ⟨tyBody, envBody, hlist', hdisj⟩ :=
                              extractTerms_typed hterms hlist
                            simp [extractBlockTerm]
                            refine ⟨envOut, .cons
                              (TermTyping.iteDiverging hcondition' htrue'
                                (TermTyping.block hchild hlist' ?_ rfl)
                                (.block (extractTerms_diverging nofun) .missing))
                              .nil⟩
                            rcases hdisj with rfl | ⟨rfl, rfl⟩
                            · exact WellFormedTy.unit
                            · exact hwf
              all_goals
                simp [extractBlockTerm]
                exact ⟨envOut, .cons
                  (TermTyping.iteDiverging hcondition' htrue'
                    missingBlock_typed missingBlock_diverging) .nil⟩
  case ctermWhile_whileCondition hcondition =>
      simp only [extractTermStmts]
      cases htyped with
      | whileLoop hchild hcondition' hbody hwellTy hdropEq =>
          exact extractTermStmts_typed hcondition hcondition'
      | whileLoopDiverging hchild hcondition' hbody hdiverges =>
          exact extractTermStmts_typed hcondition hcondition'
      | whileLoopJoin hchild hjoin hss1 hss2 hcbwf hcoh hlin hcondInv
          hbodyInv hwellTy hdropEq hcondEntry hbodyEntry =>
          exact extractTermStmts_typed hcondition hcondEntry
  case ctermWhile_whileBody bodyLifetime condition body bodyCompletion
      hbody =>
      obtain ⟨envMid, hchild', hcondition', tyBody, envBody, hbody'⟩ :
          ∃ envMid,
            LifetimeChild currentLifetime bodyLifetime ∧
            TermTyping env typing currentLifetime condition .bool envMid ∧
            ∃ tyBody envBody,
              TermTyping envMid typing bodyLifetime bodyCompletion tyBody
                envBody := by
        cases htyped with
        | whileLoop hchild hcondition' hbody' _ _ =>
            exact ⟨_, hchild, hcondition', _, _, hbody'⟩
        | whileLoopDiverging hchild hcondition' hbody' _ =>
            exact ⟨_, hchild, hcondition', _, _, hbody'⟩
        | whileLoopJoin hchild _ _ _ _ _ _ _ _ _ _ hcondEntry hbodyEntry =>
            exact ⟨_, hchild, hcondEntry, _, _, hbodyEntry⟩
      simp only [extractTermStmts]
      cases body
      case done =>
          cases hbody
          cases bodyCompletion <;> simp [extractBlockTerm, blockOrMissing]
          · exact ⟨env₂, .cons htyped .nil⟩
          all_goals
            exact ⟨envMid, .cons
              (TermTyping.whileLoopDiverging hchild' hcondition'
                missingBlock_typed missingBlock_diverging) .nil⟩
      case blockTerms blockLifetime terms =>
          cases hbody with
          | ctermBlock_blockTerms hterms =>
              cases terms
              case done xs =>
                  cases hterms
                  simp [extractBlockTerm, extractTerms]
                  exact ⟨env₂, .cons htyped .nil⟩
              all_goals
                cases hbody' with
                | «block» hchild₂ hlist hwf _heq =>
                    obtain ⟨tyBlock, envBlock, hlist', hdisj⟩ :=
                      extractTerms_typed hterms hlist
                    simp [extractBlockTerm]
                    refine ⟨envMid, .cons
                      (TermTyping.whileLoopDiverging hchild' hcondition'
                        (TermTyping.block hchild₂ hlist' ?_ rfl)
                        (.block (extractTerms_diverging nofun) .missing))
                      .nil⟩
                    rcases hdisj with rfl | ⟨rfl, rfl⟩
                    · exact WellFormedTy.unit
                    · exact hwf
      all_goals
        simp [extractBlockTerm]
        exact ⟨envMid, .cons
          (TermTyping.whileLoopDiverging hchild' hcondition'
            missingBlock_typed missingBlock_diverging) .nil⟩
  all_goals
    simp only [extractTermStmts]
    exact ⟨env, .nil⟩
termination_by (sizeOf p, 0)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (simp_wf
       try subst_vars
       first
       | exact Prod.Lex.right _ (by omega)
       | exact Prod.Lex.left _ _ (by try simp; omega))

/-- Block-body transport: the extracted body types with result type either
`.unit` (frontier closed by `missingTerm`) or the completion's result type
and environment (fully complete body). -/
theorem extractTerms_typed {currentLifetime : Lifetime} {ps : PartialTerms}
    {completions : List Term} {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerms ps completions)
    (hlist : TermListTyping env typing currentLifetime completions ty env₂) :
    ∃ ty' env', TermListTyping env typing currentLifetime
        (extractTerms currentLifetime ps) ty' env' ∧
      (ty' = .unit ∨ (ty' = ty ∧ env' = env₂)) := by
  cases hcomp
  case done =>
      simp only [extractTerms]
      exact ⟨ty, env₂, hlist, Or.inr ⟨rfl, rfl⟩⟩
  case cutoff =>
      simp only [extractTerms]
      exact ⟨.unit, env, .singleton (.missing .unit tyLoanFree_unit),
        Or.inl rfl⟩
  case elemsDone =>
      obtain ⟨mid, hpre, _⟩ :=
        stmtsTyping_append_inv (termListTyping_toStmts hlist)
      simp only [extractTerms]
      exact ⟨.unit, mid, stmtsTyping_missing_closed hpre, Or.inl rfl⟩
  case elemsTail hfrontier =>
      obtain ⟨mid, hpre, hrest⟩ :=
        stmtsTyping_append_inv (termListTyping_toStmts hlist)
      cases hrest with
      | cons hfrontier' hsuffix =>
          obtain ⟨env', hstmts⟩ := extractTermStmts_typed hfrontier hfrontier'
          simp only [extractTerms]
          refine ⟨.unit, env', ?_, Or.inl rfl⟩
          have happend :=
            stmtsTyping_missing_closed (stmtsTyping_append hpre hstmts)
          simpa [List.append_assoc] using happend
termination_by (sizeOf ps, 0)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (simp_wf
       try subst_vars
       first
       | exact Prod.Lex.right _ (by omega)
       | exact Prod.Lex.left _ _ (by try simp; omega))

end

theorem extractProgram_wellTyped_of_completion
    {p : PartialProgram} {full : Program}
    (hCompletion : CompletesProgram p full)
    (hFull : ProgramWellTyped full) :
    ProgramWellTyped (extractProgram p) := by
  obtain ⟨ty, env, htyped⟩ := hFull
  obtain ⟨ty', env', htyped'⟩ := extractTerm_typed hCompletion htyped
  exact ⟨ty', env', htyped'⟩

theorem extractProgram_wellTyped_of_blockOutput_completion
    {p : PartialProgram} {full : Program}
    (hCompletion : BlockOutputCompletesProgram p full)
    (hFull : ProgramWellTyped full) :
    ProgramWellTyped (extractProgram p) := by
  exact extractProgram_wellTyped_of_completion hCompletion.1 hFull

end TypedExtraction

theorem extractor_wellTyped_conservative :
    Conservative ProgramWellTyped CompletesProgram extractProgram := by
  intro p hInvalid full hCompletion hFull
  exact hInvalid (extractProgram_wellTyped_of_completion hCompletion hFull)

theorem extractor_wellTyped_blockOutput_conservative :
    Conservative ProgramWellTyped BlockOutputCompletesProgram extractProgram := by
  intro p hInvalid full hCompletion hFull
  exact hInvalid
    (extractProgram_wellTyped_of_blockOutput_completion hCompletion hFull)

theorem extractor_wellTyped_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CompletesProgram
      (ExtractorPrefixChecker programWellTyped extractProgram) := by
  exact conservative_extractors_give_complete_prefix_checkers
    extractor_wellTyped_conservative
    programWellTyped_complete

theorem extractor_wellTyped_blockOutput_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped BlockOutputCompletesProgram
      (ExtractorPrefixChecker programWellTyped extractProgram) := by
  exact conservative_extractors_give_complete_prefix_checkers
    extractor_wellTyped_blockOutput_conservative
    programWellTyped_complete

end ConservativeExtractor
