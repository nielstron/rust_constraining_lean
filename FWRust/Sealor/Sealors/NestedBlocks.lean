import FWRust.Sealor.Checkers

/-!
A syntax-directed FWRust frontier sealor mirroring the expression/statement
split in `../rust_constraining/constraining/src/ast_copier.rs`, specialized to
the FWRust core syntax.

The old sealor used a synthetic diverging `missing` term.  The current core
calculus has no such term, so this version uses `epsilonTerm` (`()`) where an
expression is required and omits unavailable statement-position fragments.
Incomplete block-body frontiers are closed with a final `epsilonTerm`.  Partial
assignment frontiers keep only the sealed RHS statement; the LHS is not
rebuilt.  Integer frontiers and bare block-start frontiers are treated as
unavailable fragments rather than as self-contained generated terms.
-/

namespace ConservativeSealor

/-- The core-calculus replacement for the old `missing` expression. -/
abbrev epsilonTerm : Term :=
  .val .unit

mutual

/-- Seal a partial expression in value position (`ast_copier.visit_expr`). -/
def sealTerm (currentLifetime : Lifetime) : PartialTerm → Term
  | Generated.PartialTerm.cutoff => epsilonTerm
  | Generated.PartialTerm.done term => term
  | Generated.PartialTerm.intN _ => epsilonTerm
  | Generated.PartialTerm.blockTerms lifetime terms =>
      CompleteDsl.block lifetime (sealTerms lifetime terms)
  | frontier =>
      (sealTermStmts currentLifetime frontier).headD epsilonTerm
termination_by p => (sizeOf p, 1)

/-- Seal a partial expression in statement position
(`ast_copier.visit_expr_stmt`): recursively keep child expressions that can
still constrain later checking, but do not rebuild constraining parents around
partial frontiers. -/
def sealTermStmts (currentLifetime : Lifetime) : PartialTerm → List Term
  | Generated.PartialTerm.cutoff => []
  | Generated.PartialTerm.done term => [term]
  | Generated.PartialTerm.intN _ => []
  | Generated.PartialTerm.blockStart => []
  | Generated.PartialTerm.blockTerms lifetime terms =>
      [CompleteDsl.block lifetime (sealTerms lifetime terms)]
  | Generated.PartialTerm.letMutStart => []
  | Generated.PartialTerm.letMutName _ => []
  | Generated.PartialTerm.letMutRhs _ term =>
      sealTermStmts currentLifetime term
  | Generated.PartialTerm.lvalStart _ => []
  | Generated.PartialTerm.assignRhs _ rhs =>
      sealTermStmts currentLifetime rhs
  | Generated.PartialTerm.boxStart => []
  | Generated.PartialTerm.boxOperand operand =>
      sealTermStmts currentLifetime operand
  | Generated.PartialTerm.tokenAmpStart => []
  | Generated.PartialTerm.borrowSharedOperand _ => []
  | Generated.PartialTerm.borrowMutOperand _ => []
  | Generated.PartialTerm.copyStart => []
  | Generated.PartialTerm.copyOperand _ => []
termination_by p => (sizeOf p, 0)

/-- Seal a block-body frontier (`ast_copier.visit_stmts`), preserving the
complete statement prefix and sealing the single partial tail.
Incomplete bodies are closed with `epsilonTerm`, the core replacement for the
old `missing` placeholder. -/
def sealTerms (currentLifetime : Lifetime) : PartialTerms → List Term
  | Generated.PartialTerms.cutoff => [epsilonTerm, epsilonTerm]
  | Generated.PartialTerms.done xs => xs
  | Generated.PartialTerms.elems pre none =>
      pre ++ [epsilonTerm, epsilonTerm]
  | Generated.PartialTerms.elems pre (some tail) =>
      pre ++ [sealTerm currentLifetime tail, epsilonTerm]
termination_by ps => (sizeOf ps, 0)

end

def sealProgram : PartialProgram → Program :=
  sealTerm FWRust.Core.Lifetime.root

/-- Convenience checker using the nested-block sealor. -/
def nestedBlocksPrefixChecker : PartialProgram → Prop :=
  SealorPrefixChecker programWellTyped sealProgram

section TypedSealing

open FWRust.Paper

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

/-- Closing a sealed statement run with epsilon yields a block body of
result type `.unit`. -/
theorem stmtsTyping_epsilon_closed {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List Term}
    (hstmts : StmtsTyping env typing lifetime stmts env₂) :
    TermListTyping env typing lifetime (stmts ++ [epsilonTerm]) .unit env₂ := by
  induction hstmts with
  | nil => exact .singleton epsilonTerm_typed
  | cons hterm _ ih => exact .cons hterm ih

/-- Closing a statement run with the sealed tail and a final epsilon gives the
paper's block-body shape `pre ++ [seal tail, epsilon]`. -/
theorem stmtsTyping_term_epsilon_closed {env mid env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {stmts : List Term}
    {term : Term} {ty : Ty}
    (hstmts : StmtsTyping env typing lifetime stmts mid)
    (hterm : TermTyping mid typing lifetime term ty env₂) :
    TermListTyping env typing lifetime
      (stmts ++ [term, epsilonTerm]) .unit env₂ := by
  have happend : StmtsTyping env typing lifetime (stmts ++ [term]) env₂ :=
    stmtsTyping_append hstmts (.cons hterm .nil)
  simpa [List.append_assoc] using stmtsTyping_epsilon_closed happend

theorem headD_typed {env env' : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List Term}
    (hstmts : StmtsTyping env typing lifetime stmts env') :
    ∃ ty' env'', TermTyping env typing lifetime
      (stmts.headD epsilonTerm) ty' env'' := by
  cases hstmts with
  | nil => exact ⟨.unit, env, epsilonTerm_typed⟩
  | cons hfirst _ => exact ⟨_, _, hfirst⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
mutual

theorem sealTerm_typed {currentLifetime : Lifetime} {p : PartialTerm}
    {completion : Term} {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerm p completion)
    (htyped : TermTyping env typing currentLifetime completion ty env₂) :
    ∃ ty' env', TermTyping env typing currentLifetime
      (sealTerm currentLifetime p) ty' env' := by
  cases p
  case cutoff =>
      simp only [sealTerm]
      exact ⟨.unit, env, epsilonTerm_typed⟩
  case done =>
      cases hcomp
      simp only [sealTerm]
      exact ⟨ty, env₂, htyped⟩
  case intN =>
      cases hcomp
      simp only [sealTerm]
      exact ⟨.unit, env, epsilonTerm_typed⟩
  case blockStart =>
      simp only [sealTerm, sealTermStmts]
      exact ⟨.unit, env, epsilonTerm_typed⟩
  case blockTerms blockLifetime terms =>
      cases hcomp with
      | ctermBlock_blockTerms hterms =>
          cases htyped with
          | «block» hchild hlist hwf _ =>
              obtain ⟨ty', envBody, hlist', hdisj⟩ :=
                sealTerms_typed hterms hlist
              simp only [sealTerm]
              refine ⟨ty', envBody.dropLifetime blockLifetime,
                TermTyping.block hchild hlist' ?_ rfl⟩
              rcases hdisj with rfl | ⟨rfl, rfl⟩
              · exact WellFormedTy.unit
              · exact hwf
  all_goals
    simp only [sealTerm]
    obtain ⟨env', hstmts⟩ := sealTermStmts_typed hcomp htyped
    exact headD_typed hstmts
termination_by (sizeOf p, 1)
decreasing_by
  all_goals subst_vars; decreasing_tactic

theorem sealTermStmts_typed {currentLifetime : Lifetime} {p : PartialTerm}
    {completion : Term} {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerm p completion)
    (htyped : TermTyping env typing currentLifetime completion ty env₂) :
    ∃ env', StmtsTyping env typing currentLifetime
      (sealTermStmts currentLifetime p) env' := by
  cases hcomp
  case done =>
      simp only [sealTermStmts]
      exact ⟨env₂, .cons htyped .nil⟩
  case ctermBlock_blockTerms hterms =>
      cases htyped with
      | «block» hchild hlist hwf _ =>
          obtain ⟨ty', envBody, hlist', hdisj⟩ :=
            sealTerms_typed hterms hlist
          simp only [sealTermStmts]
          refine ⟨envBody.dropLifetime _,
            .cons (TermTyping.block hchild hlist' ?_ rfl) .nil⟩
          rcases hdisj with rfl | ⟨rfl, rfl⟩
          · exact WellFormedTy.unit
          · exact hwf
  case ctermLetMut_letMutRhs hinit =>
      cases htyped with
      | declare hinit' _ _ =>
          simp only [sealTermStmts]
          exact sealTermStmts_typed hinit hinit'
  case ctermAssign_assignRhs hrhs =>
      cases htyped with
      | assign hrhs' _ _ _ _ _ =>
          simp only [sealTermStmts]
          exact sealTermStmts_typed hrhs hrhs'
  case ctermBox_boxOperand hoperand =>
      cases htyped with
      | «box» hoperand' =>
          simp only [sealTermStmts]
          exact sealTermStmts_typed hoperand hoperand'
  all_goals
    simp only [sealTermStmts]
    exact ⟨env, .nil⟩
termination_by (sizeOf p, 0)
decreasing_by
  all_goals decreasing_tactic

theorem sealTerms_typed {currentLifetime : Lifetime} {ps : PartialTerms}
    {completions : List Term} {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerms ps completions)
    (hlist : TermListTyping env typing currentLifetime completions ty env₂) :
    ∃ ty' env', TermListTyping env typing currentLifetime
        (sealTerms currentLifetime ps) ty' env' ∧
      (ty' = .unit ∨ (ty' = ty ∧ env' = env₂)) := by
  cases hcomp
  case done =>
      simp only [sealTerms]
      exact ⟨ty, env₂, hlist, Or.inr ⟨rfl, rfl⟩⟩
  case cutoff =>
      simp only [sealTerms]
      exact ⟨.unit, env, .cons epsilonTerm_typed (.singleton epsilonTerm_typed),
        Or.inl rfl⟩
  case elemsDone =>
      obtain ⟨mid, hpre, _⟩ :=
        stmtsTyping_append_inv (termListTyping_toStmts hlist)
      simp only [sealTerms]
      exact ⟨.unit, mid,
        stmtsTyping_term_epsilon_closed hpre epsilonTerm_typed, Or.inl rfl⟩
  case elemsTail hfrontier =>
      obtain ⟨mid, hpre, hrest⟩ :=
        stmtsTyping_append_inv (termListTyping_toStmts hlist)
      cases hrest with
      | cons hfrontier' _ =>
          obtain ⟨ty', env', hsealed⟩ := sealTerm_typed hfrontier hfrontier'
          simp only [sealTerms]
          exact ⟨.unit, env',
            stmtsTyping_term_epsilon_closed hpre hsealed, Or.inl rfl⟩
termination_by (sizeOf ps, 0)
decreasing_by
  all_goals decreasing_tactic

end

theorem sealProgram_wellTyped_of_completion
    {p : PartialProgram} {full : Program}
    (hCompletion : CompletesProgram p full)
    (hFull : ProgramWellTyped full) :
    ProgramWellTyped (sealProgram p) := by
  obtain ⟨ty, env, htyped⟩ := hFull
  obtain ⟨ty', env', htyped'⟩ := sealTerm_typed hCompletion htyped
  exact ⟨ty', env', htyped'⟩

theorem nestedBlocksPrefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CompletesProgram
      nestedBlocksPrefixChecker := by
  intro p _ hp
  rcases hp with ⟨full, hCompletion, hFull⟩
  exact sealProgram_wellTyped_of_completion hCompletion hFull

/-- String-level global completeness, conditional only on the parser bridge
from extendable strings to the partial-syntax realization relation. -/
theorem nestedBlocksPrefixChecker_complete_on_strings
    (parse : String → Option Program)
    (decode : String → PartialProgram)
    (hDecode : ∀ rawPrefix,
      Completable ProgramWellTyped (StringExtensionCompletes parse) rawPrefix →
      Completable ProgramWellTyped CompletesProgram (decode rawPrefix)) :
    PrefixCheckerComplete ProgramWellTyped (StringExtensionCompletes parse)
      (fun rawPrefix => nestedBlocksPrefixChecker (decode rawPrefix)) :=
  partialSyntax_completeness_lifts_to_strings parse decode
    nestedBlocksPrefixChecker_complete hDecode

end TypedSealing

section StatementBoundary

open FWRust.Paper

/-- Partial programs exactly at a completed block-statement boundary. -/
def CompletedStatementBoundary (partialProgram : PartialProgram) : Prop :=
  ∃ lifetime pre,
    partialProgram = Generated.PartialTerm.blockTerms lifetime
      (Generated.PartialTerms.elems pre none)

/--
At a block-body statement boundary, the sealed block is one generated
completion of the partial block.
-/
theorem sealProgram_completedStatementBoundary_completes
    {lifetime : Lifetime} {pre : List Term} :
    CompletesProgram
      (Generated.PartialTerm.blockTerms lifetime
        (Generated.PartialTerms.elems pre none))
      (sealProgram
        (Generated.PartialTerm.blockTerms lifetime
          (Generated.PartialTerms.elems pre none))) := by
  simpa [CompletesProgram, sealProgram, sealTerm, sealTerms] using
      (Generated.CompletesTerm.ctermBlock_blockTerms
      (Generated.CompletesTerms.elemsDone
        (pre := pre) (suffix := [epsilonTerm, epsilonTerm])))

/-- Paper-level statement-boundary soundness for arbitrary typing environments,
store typings, ambient lifetimes, and result types.  The sealed term itself is
a well-typed realization of the partial block. -/
theorem sealProgram_completedStatementBoundary_sound_general
    {blockLifetime currentLifetime : Lifetime} {pre : List Term}
    {env result : Env} {typing : StoreTyping} {ty : Ty}
    (hSealed : TermTyping env typing currentLifetime
      (sealProgram
        (Generated.PartialTerm.blockTerms blockLifetime
          (Generated.PartialTerms.elems pre none))) ty result) :
    ∃ completion completionTy completionResult,
      CompletesProgram
        (Generated.PartialTerm.blockTerms blockLifetime
          (Generated.PartialTerms.elems pre none)) completion ∧
      TermTyping env typing currentLifetime completion completionTy
        completionResult := by
  exact ⟨_, ty, result,
    sealProgram_completedStatementBoundary_completes, hSealed⟩

/--
Soundness at a completed-statement boundary: if this sealed approximation checks,
there is a well-typed completion of the partial block.
-/
theorem sealProgram_completedStatementBoundary_sound
    {lifetime : Lifetime} {pre : List Term}
    (hSealed : ProgramWellTyped
      (sealProgram
        (Generated.PartialTerm.blockTerms lifetime
          (Generated.PartialTerms.elems pre none)))) :
    Completable ProgramWellTyped CompletesProgram
      (Generated.PartialTerm.blockTerms lifetime
        (Generated.PartialTerms.elems pre none)) := by
  exact ⟨_,
    sealProgram_completedStatementBoundary_completes,
    hSealed⟩

/-- The generated prefix checker is sound on completed statement boundaries. -/
theorem nestedBlocksPrefixChecker_sound_on_completedStatementBoundaries :
    PrefixCheckerSoundOn CompletedStatementBoundary ProgramWellTyped
      CompletesProgram nestedBlocksPrefixChecker := by
  intro partialProgram hBoundary hAccepted
  rcases hBoundary with ⟨lifetime, pre, rfl⟩
  exact sealProgram_completedStatementBoundary_sound hAccepted

/-- String-level selective soundness, conditional on the parser bridge from
partial-syntax realizations back to actual string extensions. -/
theorem nestedBlocksPrefixChecker_sound_on_statementBoundary_strings
    (parse : String → Option Program)
    (decode : String → PartialProgram)
    (StringStatementBoundary : String → Prop)
    (hBoundary : ∀ rawPrefix,
      StringStatementBoundary rawPrefix →
      CompletedStatementBoundary (decode rawPrefix))
    (hRealizes : ∀ rawPrefix complete,
      CompletesProgram (decode rawPrefix) complete →
      StringExtensionCompletes parse rawPrefix complete) :
    PrefixCheckerSoundOn StringStatementBoundary ProgramWellTyped
      (StringExtensionCompletes parse)
      (fun rawPrefix => nestedBlocksPrefixChecker (decode rawPrefix)) :=
  partialSyntax_soundness_lifts_to_strings parse decode
    StringStatementBoundary
    nestedBlocksPrefixChecker_sound_on_completedStatementBoundaries
    hBoundary hRealizes

end StatementBoundary

end ConservativeSealor
