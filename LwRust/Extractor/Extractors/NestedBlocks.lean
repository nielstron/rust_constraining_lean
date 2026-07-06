import LwRust.Extractor.Checkers

/-!
A syntax-directed LwRust frontier extractor mirroring the expression/statement
split in `rust_constraining`'s `ast_copier.rs`, cut down to the current core
syntax.

The extractor works over unannotated source syntax (`RawTerm`).  Block
lifetimes are inserted only by `RawTerm.annotateProgram`, before the existing
annotated core type checker is run.

The old extractor used a synthetic diverging `missing` term.  The current core
calculus has no such term, so this version uses `rawEpsilonTerm` (`()`) where
an expression is required and omits unavailable statement-position fragments.
Incomplete block-body frontiers are closed with a final `rawEpsilonTerm`.
Partial assignment frontiers keep only the RHS statement extraction; the LHS is
not rebuilt.  Integer frontiers and bare block-start frontiers are treated as
unavailable fragments rather than as self-contained generated terms.
-/

namespace ConservativeExtractor

/-- The annotated core-calculus replacement for the old `missing` expression. -/
abbrev epsilonTerm : Term :=
  .val .unit

/-- The unannotated source counterpart of `epsilonTerm`. -/
abbrev rawEpsilonTerm : RawTerm :=
  .val .unit

mutual

/-- Extract a partial expression in value position (`ast_copier.visit_expr`). -/
def extractTerm : PartialTerm → RawTerm
  | Generated.PartialTerm.cutoff => rawEpsilonTerm
  | Generated.PartialTerm.done term => term
  | Generated.PartialTerm.intN _ => rawEpsilonTerm
  | Generated.PartialTerm.blockTerms terms =>
      .block (extractTerms terms)
  | frontier =>
      (extractTermStmts frontier).headD rawEpsilonTerm

/-- Extract a partial expression in statement position
(`ast_copier.visit_expr_stmt`): recursively keep child expressions that can
still constrain later checking, but do not rebuild constraining parents around
partial frontiers. -/
def extractTermStmts : PartialTerm → List RawTerm
  | Generated.PartialTerm.cutoff => []
  | Generated.PartialTerm.done term => [term]
  | Generated.PartialTerm.intN _ => []
  | Generated.PartialTerm.blockStart => []
  | Generated.PartialTerm.blockTerms terms =>
      [.block (extractTerms terms)]
  | Generated.PartialTerm.letMutStart => []
  | Generated.PartialTerm.letMutName _ => []
  | Generated.PartialTerm.letMutRhs _ term =>
      extractTermStmts term
  | Generated.PartialTerm.lvalStart _ => []
  | Generated.PartialTerm.assignRhs _ rhs =>
      extractTermStmts rhs
  | Generated.PartialTerm.boxStart => []
  | Generated.PartialTerm.boxOperand operand =>
      extractTermStmts operand
  | Generated.PartialTerm.tokenAmpStart => []
  | Generated.PartialTerm.borrowSharedOperand _ => []
  | Generated.PartialTerm.borrowMutOperand _ => []
  | Generated.PartialTerm.copyStart => []
  | Generated.PartialTerm.copyOperand _ => []
termination_by p => (sizeOf p, 0)

/-- Extract a block-body frontier (`ast_copier.visit_stmts`), preserving the
complete statement prefix and statement-extracting the single partial tail.
Incomplete bodies are closed with `rawEpsilonTerm`, the source replacement for
the old `missing` placeholder. -/
def extractTerms : PartialTerms → List RawTerm
  | Generated.PartialTerms.cutoff => [rawEpsilonTerm]
  | Generated.PartialTerms.done xs => xs
  | Generated.PartialTerms.elems pre none => pre ++ [rawEpsilonTerm]
  | Generated.PartialTerms.elems pre (some tail) =>
      pre ++ extractTermStmts tail ++ [rawEpsilonTerm]
termination_by ps => (sizeOf ps, 0)

end

def extractProgram : PartialProgram → RawProgram :=
  extractTerm

/-- Extract raw source syntax, annotate it algorithmically, then typecheck. -/
def nestedBlocksPrefixChecker : PartialProgram → Prop :=
  ExtractorPrefixChecker rawProgramWellTyped extractProgram

section TypedExtraction

open LwRust.Paper

theorem epsilonTerm_typed {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping env typing lifetime epsilonTerm .unit env :=
  TermTyping.const ValueTyping.unit

/-- Sequential statement typing without committing to a final result type. -/
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
  | cons _ xs ih =>
      intro env env₂ hstmts
      cases hstmts with
      | cons hterm hrest =>
          obtain ⟨mid, hxs, hys⟩ := ih hrest
          exact ⟨mid, .cons hterm hxs, hys⟩

/-- Closing an extracted statement run with epsilon yields a block body of
result type `.unit`. -/
theorem stmtsTyping_epsilon_closed {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List Term}
    (hstmts : StmtsTyping env typing lifetime stmts env₂) :
    TermListTyping env typing lifetime (stmts ++ [epsilonTerm]) .unit env₂ := by
  induction hstmts with
  | nil => exact .singleton epsilonTerm_typed
  | cons hterm _ ih => exact .cons hterm ih

theorem rawEpsilonTerm_typed {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping env typing lifetime
      (RawTerm.annotate lifetime rawEpsilonTerm) .unit env := by
  simpa [rawEpsilonTerm, RawTerm.annotate] using
    (epsilonTerm_typed (env := env) (typing := typing) (lifetime := lifetime))

theorem rawHeadD_typed {env env' : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List RawTerm}
    (hstmts : StmtsTyping env typing lifetime
      (RawTerm.annotateList lifetime stmts) env') :
    ∃ ty' env'', TermTyping env typing lifetime
      (RawTerm.annotate lifetime (stmts.headD rawEpsilonTerm)) ty' env'' := by
  cases stmts with
  | nil =>
      exact ⟨.unit, env, rawEpsilonTerm_typed⟩
  | cons term rest =>
      cases hstmts with
      | cons hfirst _ =>
          exact ⟨_, _, by simpa [RawTerm.annotateList] using hfirst⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
mutual

theorem extractTerm_typed {p : PartialTerm} {completion : RawTerm}
    {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    {currentLifetime : Lifetime}
    (hcomp : CompletesTerm p completion)
    (htyped : TermTyping env typing currentLifetime
      (RawTerm.annotate currentLifetime completion) ty env₂) :
    ∃ ty' env', TermTyping env typing currentLifetime
      (RawTerm.annotate currentLifetime (extractTerm p)) ty' env' := by
  cases p
  case done =>
      cases hcomp
      simp only [extractTerm]
      exact ⟨ty, env₂, htyped⟩
  case cutoff =>
      simp only [extractTerm]
      exact ⟨.unit, env, rawEpsilonTerm_typed⟩
  case intN =>
      cases hcomp
      simp only [extractTerm]
      exact ⟨.unit, env, rawEpsilonTerm_typed⟩
  case blockTerms terms =>
      cases hcomp with
      | ctermBlock_blockTerms hterms =>
          cases htyped with
          | «block» hchild hlist hwf _ =>
              obtain ⟨ty', envBody, hlist', hdisj⟩ :=
                extractTerms_typed hterms hlist
              simp only [extractTerm, RawTerm.annotate]
              refine ⟨ty', envBody.dropLifetime (RawTerm.childLifetime currentLifetime),
                TermTyping.block hchild hlist' ?_ rfl⟩
              rcases hdisj with rfl | ⟨rfl, rfl⟩
              · exact WellFormedTy.unit
              · exact hwf
  all_goals
    simp only [extractTerm]
    obtain ⟨env', hstmts⟩ := extractTermStmts_typed hcomp htyped
    exact rawHeadD_typed hstmts

theorem extractTermStmts_typed {p : PartialTerm} {completion : RawTerm}
    {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    {currentLifetime : Lifetime}
    (hcomp : CompletesTerm p completion)
    (htyped : TermTyping env typing currentLifetime
      (RawTerm.annotate currentLifetime completion) ty env₂) :
    ∃ env', StmtsTyping env typing currentLifetime
      (RawTerm.annotateList currentLifetime (extractTermStmts p)) env' := by
  cases hcomp
  case done =>
      simp only [extractTermStmts, RawTerm.annotateList]
      exact ⟨env₂, .cons htyped .nil⟩
  case ctermBlock_blockTerms hterms =>
      cases htyped with
      | «block» hchild hlist hwf _ =>
          obtain ⟨ty', envBody, hlist', hdisj⟩ :=
            extractTerms_typed hterms hlist
          simp only [extractTermStmts, RawTerm.annotateList, RawTerm.annotate]
          refine ⟨envBody.dropLifetime (RawTerm.childLifetime currentLifetime),
            .cons (TermTyping.block hchild hlist' ?_ rfl) .nil⟩
          rcases hdisj with rfl | ⟨rfl, rfl⟩
          · exact WellFormedTy.unit
          · exact hwf
  case ctermLetMut_letMutRhs hinit =>
      cases htyped with
      | declare hinit' _ _ =>
          simp only [extractTermStmts]
          exact extractTermStmts_typed hinit hinit'
  case ctermAssign_assignRhs hrhs =>
      cases htyped with
      | assign hrhs' _ _ _ _ _ =>
          simp only [extractTermStmts]
          exact extractTermStmts_typed hrhs hrhs'
  case ctermBox_boxOperand hoperand =>
      cases htyped with
      | «box» hoperand' =>
          simp only [extractTermStmts]
          exact extractTermStmts_typed hoperand hoperand'
  all_goals
    simp only [extractTermStmts, RawTerm.annotateList]
    exact ⟨env, .nil⟩
termination_by (sizeOf p, 0)
decreasing_by
  all_goals decreasing_tactic

theorem extractTerms_typed {ps : PartialTerms} {completions : List RawTerm}
    {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    {currentLifetime : Lifetime}
    (hcomp : CompletesTerms ps completions)
    (hlist : TermListTyping env typing currentLifetime
      (RawTerm.annotateList currentLifetime completions) ty env₂) :
    ∃ ty' env', TermListTyping env typing currentLifetime
        (RawTerm.annotateList currentLifetime (extractTerms ps)) ty' env' ∧
      (ty' = .unit ∨ (ty' = ty ∧ env' = env₂)) := by
  cases hcomp
  case done =>
      simp only [extractTerms]
      exact ⟨ty, env₂, hlist, Or.inr ⟨rfl, rfl⟩⟩
  case cutoff =>
      simp only [extractTerms, RawTerm.annotateList]
      exact ⟨.unit, env, .singleton rawEpsilonTerm_typed, Or.inl rfl⟩
  case elemsDone pre suffix =>
      have hstmts : StmtsTyping env typing currentLifetime
          (RawTerm.annotateList currentLifetime pre ++
            RawTerm.annotateList currentLifetime suffix) env₂ := by
        simpa [RawTerm.annotateList_append] using
          (termListTyping_toStmts hlist)
      obtain ⟨mid, hpre, _⟩ := stmtsTyping_append_inv hstmts
      simp only [extractTerms]
      refine ⟨.unit, mid, ?_, Or.inl rfl⟩
      have hclosed := stmtsTyping_epsilon_closed hpre
      simpa [RawTerm.annotateList_append, RawTerm.annotateList,
        rawEpsilonTerm, RawTerm.annotate]
        using hclosed
  case elemsTail pre suffix _frontier frontierCompletion hfrontier =>
      have hstmts : StmtsTyping env typing currentLifetime
          (RawTerm.annotateList currentLifetime pre ++
            RawTerm.annotateList currentLifetime (frontierCompletion :: suffix)) env₂ := by
        simpa [RawTerm.annotateList_append, RawTerm.annotateList] using
          (termListTyping_toStmts hlist)
      obtain ⟨mid, hpre, hrest⟩ := stmtsTyping_append_inv hstmts
      cases hrest with
      | cons hfrontier' _ =>
          obtain ⟨env', hstmts⟩ := extractTermStmts_typed hfrontier hfrontier'
          simp only [extractTerms]
          refine ⟨.unit, env', ?_, Or.inl rfl⟩
          have hclosed :=
            stmtsTyping_epsilon_closed (stmtsTyping_append hpre hstmts)
          simpa [RawTerm.annotateList_append, RawTerm.annotateList,
            rawEpsilonTerm, RawTerm.annotate, List.append_assoc] using hclosed
termination_by (sizeOf ps, 0)
decreasing_by
  all_goals decreasing_tactic

end

theorem extractProgram_wellTyped_of_completion
    {p : PartialProgram} {full : RawProgram}
    (hCompletion : CompletesProgram p full)
    (hFull : RawProgramWellTyped full) :
    RawProgramWellTyped (extractProgram p) := by
  obtain ⟨ty, env, htyped⟩ := hFull
  obtain ⟨ty', env', htyped'⟩ :=
    extractTerm_typed hCompletion htyped
  exact ⟨ty', env', htyped'⟩

theorem nestedBlocksPrefixChecker_complete :
    PrefixCheckerComplete RawProgramWellTyped CompletesProgram
      nestedBlocksPrefixChecker := by
  intro p hp
  rcases hp with ⟨full, hCompletion, hFull⟩
  exact extractProgram_wellTyped_of_completion hCompletion hFull

end TypedExtraction

/--
At a block-body statement boundary, the extracted raw block is one generated
completion of the partial block.
-/
theorem extractProgram_completedStatementBoundary_completes
    {pre : List RawTerm} :
    CompletesProgram
      (Generated.PartialTerm.blockTerms
        (Generated.PartialTerms.elems pre none))
      (extractProgram
        (Generated.PartialTerm.blockTerms
          (Generated.PartialTerms.elems pre none))) := by
  simpa [CompletesProgram, extractProgram, extractTerm, extractTerms] using
    (Generated.CompletesTerm.ctermBlock_blockTerms
      (Generated.CompletesTerms.elemsDone
        (pre := pre) (suffix := [rawEpsilonTerm])))

/--
Soundness at a completed-statement boundary: if this extracted approximation
checks after annotation, there is a well-typed raw completion of the partial
block.
-/
theorem extractProgram_completedStatementBoundary_sound
    {pre : List RawTerm}
    (hExtracted : RawProgramWellTyped
      (extractProgram
        (Generated.PartialTerm.blockTerms
          (Generated.PartialTerms.elems pre none)))) :
    Completable RawProgramWellTyped CompletesProgram
      (Generated.PartialTerm.blockTerms
        (Generated.PartialTerms.elems pre none)) := by
  exact ⟨_,
    extractProgram_completedStatementBoundary_completes,
    hExtracted⟩

end ConservativeExtractor
