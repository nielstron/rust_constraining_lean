import FWRust.Sealor.Checkers

/-!
A syntax-directed FWRust frontier extractor mirroring `rust_constraining`'s
`ast_copier.rs`.

Correspondence with `ast_copier`:

* `sealTerm` ↔ `visit_expr`: extract a partial expression in value
  position (only reached at the program root).
* `sealTermStmts` ↔ `visit_expr_stmt`: demote a partial expression to the
  statement extraction of the child expressions the copier recursively
  visits, without rebuilding a constraining parent expression.
* `sealTerms` ↔ `visit_stmts`: keep the complete statement prefix,
  statement-extract the partial tail, and close the block with `missingTerm`
  exactly as `visit_stmts` closes an incomplete block with `__missing__()}`.

Deviations from `ast_copier`, each forced by the FWRust type system rather
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
  diverges, contributes nothing to the merge.  This works whenever the
  truncated branch is block-shaped (every branch of a real Rust `if` is); for
  the unrealistic non-block branch frontiers of the generated grammar the
  extraction falls back to the condition plus the frontier branch's statement
  extraction.  (Sequencing *both* branches as statements would be wrong: the
  branches are typed in the same environment, so their effects must not be
  chained.)
* Value position: `ast_copier` wraps the statement extraction in an anonymous
  `{ …; __missing__() }` block.  FWRust blocks carry explicit lifetimes and
  `T-Block` pins them to the ambient lifetime chain, so source statements
  (which may contain source blocks with source lifetimes) cannot be relocated
  under a synthesized block.  `sealTerm` instead keeps the first extracted
  statement, or `missingTerm` if there is none.
* Lvalues: there is no chameleon lvalue analogous to `__missing__<T>()` — a
  placeholder in lvalue position cannot be conservative — so lvalue frontiers
  are dropped, matching `ast_copier`, which never synthesizes a place
  expression.
-/

namespace ConservativeSealor

/-- The FWRust analogue of `ast_copier`'s `__missing__<T>()` placeholder. -/
abbrev missingTerm : Term :=
  .missing

/-- Compatibility constant retained from the reduced calculus.  The sealor
itself now uses `missingTerm`; this unit epsilon remains available to old
clients with its original meaning. -/
abbrev epsilonTerm : Term :=
  .val .unit

/-- The lifetime of a synthesized block nested directly below `lifetime`.
Source blocks keep their source lifetime; only blocks invented by the
extractor (for an unopened block frontier) use this. -/
def childLifetime (lifetime : Lifetime) : Lifetime :=
  { path := lifetime.path ++ [0] }

/-- Branch frontiers for which a conditional can be rebuilt: the value
extraction of such a frontier is either the forced completion itself (`done`,
fully-completed blocks) or a diverging term (`cutoff`, block frontiers closed
by `missingTerm`).  Real Rust `if` branches are always blocks, so this covers
every realistic frontier; the remaining shapes fall back to statement
extraction. -/
def branchRebuildable : PartialTerm → Bool
  | Generated.PartialTerm.done _ => Bool.true
  | Generated.PartialTerm.cutoff => Bool.true
  | Generated.PartialTerm.blockStart => Bool.true
  | Generated.PartialTerm.blockTerms _ _ => Bool.true
  | _ => Bool.false

mutual

/-- Extract a partial expression in value position (`ast_copier.visit_expr`).

`currentLifetime` is the lifetime at which the extracted term will be typed.
This is only reached at the program root; see the module docstring for why
the statement extraction cannot be wrapped in a synthesized block here. -/
def sealTerm (currentLifetime : Lifetime) : PartialTerm → Term
  | Generated.PartialTerm.cutoff => missingTerm
  | Generated.PartialTerm.done term => term
  | Generated.PartialTerm.intN n => SyntaxCtor.ctermInt_ctor n
  | Generated.PartialTerm.blockStart =>
      SyntaxCtor.ctermBlock_ctor (childLifetime currentLifetime) [missingTerm]
  | Generated.PartialTerm.blockTerms lifetime terms =>
      SyntaxCtor.ctermBlock_ctor lifetime (sealTerms lifetime terms)
  | frontier =>
      (sealTermStmts currentLifetime frontier).headD missingTerm
termination_by p => (sizeOf p, 1)

/-- Extract a partial expression in statement position
(`ast_copier.visit_expr_stmt`): keep the child expressions the copier
recursively visits, do not rebuild a constraining parent.

`currentLifetime` is the lifetime at which the extracted statements will be
typed — the body lifetime of the enclosing block. -/
def sealTermStmts (currentLifetime : Lifetime) : PartialTerm → List Term
  | Generated.PartialTerm.cutoff => []
  | Generated.PartialTerm.done term => [term]
  | Generated.PartialTerm.intN _ => []
  | Generated.PartialTerm.blockStart =>
      [SyntaxCtor.ctermBlock_ctor (childLifetime currentLifetime) [missingTerm]]
  | Generated.PartialTerm.blockTerms lifetime terms =>
      [SyntaxCtor.ctermBlock_ctor lifetime (sealTerms lifetime terms)]
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
  | Generated.PartialTerm.termPrefix lhs =>
      sealTermStmts currentLifetime lhs
  | Generated.PartialTerm.eqRhs lhs _ =>
      [lhs]
  | Generated.PartialTerm.iteStart => []
  | Generated.PartialTerm.iteCondition condition =>
      sealTermStmts currentLifetime condition
  | Generated.PartialTerm.iteTrueBranch condition trueBranch =>
      if branchRebuildable trueBranch then
        [SyntaxCtor.ctermIte_ctor condition
          (sealTerm currentLifetime trueBranch) missingTerm]
      else
        condition :: sealTermStmts currentLifetime trueBranch
  | Generated.PartialTerm.iteFalseBranch condition trueBranch falseBranch =>
      if branchRebuildable falseBranch then
        [SyntaxCtor.ctermIte_ctor condition trueBranch
          (sealTerm currentLifetime falseBranch)]
      else
        condition :: sealTermStmts currentLifetime falseBranch
termination_by p => (sizeOf p, 0)

/-- Extract a block body frontier (`ast_copier.visit_stmts`): keep the
complete prefix, statement-extract the partial tail, close with
`missingTerm`.  The closing placeholder both mirrors `visit_stmts` writing
`__missing__()}` and keeps the body non-empty (T-Seq has no empty
sequence). -/
def sealTerms (currentLifetime : Lifetime) : PartialTerms → List Term
  | Generated.PartialTerms.cutoff => [missingTerm]
  | Generated.PartialTerms.done xs => xs
  | Generated.PartialTerms.elems pre none => pre ++ [missingTerm]
  | Generated.PartialTerms.elems pre (some tail) =>
      pre ++ sealTermStmts currentLifetime tail ++ [missingTerm]
termination_by ps => (sizeOf ps, 0)

end

def sealProgram : PartialProgram → Program :=
  sealTerm FWRust.Core.Lifetime.root

/-- The prefix checker induced by the nested-block sealor. -/
def nestedBlocksPrefixChecker : PartialProgram → Prop :=
  SealorPrefixChecker programWellTyped sealProgram

/-!
Typing transport: a well-typed completion yields a well-typed extraction.

The proof threads the typing derivation of the completion through the
extraction.  Complete subterms reuse their sub-derivations verbatim (in the
same environment, store typing, and lifetime they had in the completion), and
every synthesized `missingTerm` is typed at `.unit` by `T-Missing`.
-/

section TypedSealing

open FWRust.Paper

theorem tyLoanFree_unit : TyLoanFree .unit := by
  intro mutable targets hcontains
  cases hcontains

theorem epsilonTerm_typed {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping env typing lifetime epsilonTerm .unit env :=
  TermTyping.const ValueTyping.unit

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

/-- Backwards-compatible name for `stmtsTyping_missing_closed`. -/
theorem stmtsTyping_epsilon_closed {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List Term}
    (hstmts : StmtsTyping env typing lifetime stmts env₂) :
    TermListTyping env typing lifetime (stmts ++ [epsilonTerm]) .unit env₂ := by
  induction hstmts with
  | nil => exact .singleton epsilonTerm_typed
  | cons hterm _ ih => exact .cons hterm ih

/-- Closing a typed statement run with one typed term and the diverging
epsilon/missing placeholder preserves the old helper interface. -/
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

/-- The synthesized block for an unopened block frontier types
unconditionally. -/
theorem missingBlock_typed {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping env typing lifetime
      (SyntaxCtor.ctermBlock_ctor (childLifetime lifetime) [missingTerm])
      .unit (env.dropLifetime (childLifetime lifetime)) :=
  TermTyping.block ⟨0, rfl⟩
    (TermListTyping.singleton (TermTyping.missing WellFormedTy.unit tyLoanFree_unit))
    WellFormedTy.unit rfl

/-- Every non-`done` body extraction ends in (hence contains) `missingTerm`,
so the rebuilt block diverges. -/
theorem sealTerms_diverging {currentLifetime : Lifetime} {ps : PartialTerms}
    (hne : ∀ xs, ps ≠ Generated.PartialTerms.done xs) :
    missingTerm ∈ sealTerms currentLifetime ps := by
  cases ps with
  | cutoff => simp [sealTerms]
  | done xs => exact absurd rfl (hne xs)
  | elems pre tail =>
      cases tail with
      | none => simp [sealTerms]
      | some tailTerm => simp [sealTerms]

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
theorem sealTerm_typed {currentLifetime : Lifetime} {p : PartialTerm}
    {completion : Term} {env env₂ : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerm p completion)
    (htyped : TermTyping env typing currentLifetime completion ty env₂) :
    ∃ ty' env', TermTyping env typing currentLifetime
      (sealTerm currentLifetime p) ty' env' := by
  cases p
  case cutoff =>
      simp only [sealTerm]
      exact ⟨.unit, env, .missing .unit tyLoanFree_unit⟩
  case done =>
      cases hcomp
      simp only [sealTerm]
      exact ⟨ty, env₂, htyped⟩
  case intN =>
      cases hcomp
      simp only [sealTerm]
      exact ⟨ty, env₂, htyped⟩
  case blockStart =>
      simp only [sealTerm]
      exact ⟨.unit, _, missingBlock_typed⟩
  case blockTerms blockLifetime terms =>
      cases hcomp with
      | ctermBlock_blockTerms hterms =>
          cases htyped with
          | «block» hchild hlist hwf heq =>
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
  all_goals
    first
    | decreasing_tactic
    | (simp_wf
       try subst_vars
       exact Prod.Lex.right _ (by omega))

/-- Statement-position transport: the statement extraction of a frontier
types sequentially from the same starting environment as the completion. -/
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
  case ctermBlock_blockStart =>
      simp only [sealTermStmts]
      exact ⟨_, .cons missingBlock_typed .nil⟩
  case ctermBlock_blockTerms hterms =>
      cases htyped with
      | «block» hchild hlist hwf heq =>
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
      | declare _ hinit' _ _ _ =>
          simp only [sealTermStmts]
          exact sealTermStmts_typed hinit hinit'
  case ctermAssign_assignRhs hrhs =>
      cases htyped with
      | assign hrhs' _ _ _ _ _ _ _ _ =>
          simp only [sealTermStmts]
          exact sealTermStmts_typed hrhs hrhs'
  case ctermBox_boxOperand hoperand =>
      cases htyped with
      | «box» hoperand' =>
          simp only [sealTermStmts]
          exact sealTermStmts_typed hoperand hoperand'
  case ctermEq_termPrefix hlhs =>
      cases htyped with
      | eq hlhs' =>
          simp only [sealTermStmts]
          exact sealTermStmts_typed hlhs hlhs'
  case ctermEq_eqRhs hrhs =>
      cases htyped with
      | eq hlhs' =>
          simp only [sealTermStmts]
          exact ⟨_, .cons hlhs' .nil⟩
  case ctermIte_iteCondition hcondition =>
      simp only [sealTermStmts]
      cases htyped with
      | ite hcondition' =>
          exact sealTermStmts_typed hcondition hcondition'
      | iteDiverging hcondition' =>
          exact sealTermStmts_typed hcondition hcondition'
      | iteTrueDiverging hcondition' =>
          exact sealTermStmts_typed hcondition hcondition'
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
        | iteTrueDiverging hcondition' htrue' =>
            exact ⟨_, hcondition', _, _, htrue'⟩
      simp only [sealTermStmts]
      cases hrebuild : branchRebuildable trueBranch with
      | «true» =>
          simp
          obtain ⟨tyLive', envLive, hlive⟩ := sealTerm_typed htrue htrue'
          exact ⟨envLive, .cons
            (TermTyping.iteDiverging hcondition' hlive
              (TermTyping.missing WellFormedTy.unit tyLoanFree_unit)
              .missing) .nil⟩
      | «false» =>
          simp
          obtain ⟨env', hstmts⟩ := sealTermStmts_typed htrue htrue'
          exact ⟨env', .cons hcondition' hstmts⟩
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
        | iteTrueDiverging hcondition' htrue' hfalse' =>
            exact ⟨_, hcondition', _, _, htrue', _, _, hfalse'⟩
      simp only [sealTermStmts]
      cases falseBranch
      case done falseTerm =>
          cases hfalse
          simp [branchRebuildable, sealTerm]
          exact ⟨env₂, .cons htyped .nil⟩
      case cutoff =>
          simp [branchRebuildable, sealTerm]
          exact ⟨envOut, .cons
            (TermTyping.iteDiverging hcondition' htrue'
              (TermTyping.missing WellFormedTy.unit tyLoanFree_unit)
              .missing) .nil⟩
      case blockStart =>
          simp [branchRebuildable, sealTerm]
          exact ⟨envOut, .cons
            (TermTyping.iteDiverging hcondition' htrue' missingBlock_typed
              (.block (by simp) .missing)) .nil⟩
      case blockTerms blockLifetime terms =>
          cases hfalse with
          | ctermBlock_blockTerms hterms =>
              cases terms
              case done xs =>
                  cases hterms
                  simp [branchRebuildable, sealTerm, sealTerms]
                  exact ⟨env₂, .cons htyped .nil⟩
              all_goals
                cases hfalse' with
                | «block» hchild hlist hwf _heq =>
                    obtain ⟨tyBody, envBody, hlist', hdisj⟩ :=
                      sealTerms_typed hterms hlist
                    simp [branchRebuildable, sealTerm]
                    refine ⟨envOut, .cons
                      (TermTyping.iteDiverging hcondition' htrue'
                        (TermTyping.block hchild hlist' ?_ rfl)
                        (.block (sealTerms_diverging nofun) .missing))
                      .nil⟩
                    rcases hdisj with rfl | ⟨rfl, rfl⟩
                    · exact WellFormedTy.unit
                    · exact hwf
      all_goals
        obtain ⟨env', hstmts⟩ := sealTermStmts_typed hfalse hfalse'
        simp only [sealTermStmts, branchRebuildable] at hstmts ⊢
        exact ⟨env', .cons hcondition' hstmts⟩
  all_goals
    simp only [sealTermStmts]
    exact ⟨env, .nil⟩
termination_by (sizeOf p, 0)
decreasing_by
  all_goals decreasing_tactic

/-- Block-body transport: the extracted body types with result type either
`.unit` (frontier closed by `missingTerm`) or the completion's result type
and environment (fully complete body). -/
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
      exact ⟨.unit, env, .singleton (.missing .unit tyLoanFree_unit),
        Or.inl rfl⟩
  case elemsDone =>
      obtain ⟨mid, hpre, _⟩ :=
        stmtsTyping_append_inv (termListTyping_toStmts hlist)
      simp only [sealTerms]
      exact ⟨.unit, mid, stmtsTyping_missing_closed hpre, Or.inl rfl⟩
  case elemsTail hfrontier =>
      obtain ⟨mid, hpre, hrest⟩ :=
        stmtsTyping_append_inv (termListTyping_toStmts hlist)
      cases hrest with
      | cons hfrontier' hsuffix =>
          obtain ⟨env', hstmts⟩ := sealTermStmts_typed hfrontier hfrontier'
          simp only [sealTerms]
          refine ⟨.unit, env', ?_, Or.inl rfl⟩
          have happend :=
            stmtsTyping_missing_closed (stmtsTyping_append hpre hstmts)
          simpa [List.append_assoc] using happend
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

end TypedSealing

theorem sealor_wellTyped_conservative :
    Conservative ProgramWellTyped CompletesProgram sealProgram := by
  intro p hInvalid full hCompletion hFull
  exact hInvalid (sealProgram_wellTyped_of_completion hCompletion hFull)

theorem sealor_wellTyped_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CompletesProgram
      (SealorPrefixChecker programWellTyped sealProgram) := by
  exact conservative_sealors_give_complete_prefix_checkers
    sealor_wellTyped_conservative
    programWellTyped_complete

/-- Public completeness theorem retained under the canonical sealor API. -/
theorem nestedBlocksPrefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CompletesProgram
      nestedBlocksPrefixChecker :=
  sealor_wellTyped_prefixChecker_complete

/-- String-level global completeness, conditional only on the parser bridge
from extendable strings to the generated partial-syntax realization relation. -/
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

section StatementBoundary

open FWRust.Paper

/-- Partial programs exactly at a completed block-statement boundary. -/
def CompletedStatementBoundary (partialProgram : PartialProgram) : Prop :=
  ∃ lifetime pre,
    partialProgram = Generated.PartialTerm.blockTerms lifetime
      (Generated.PartialTerms.elems pre none)

/-- At a block-body statement boundary, the sealed block itself is one
generated completion of the partial block. -/
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
        (pre := pre) (suffix := [missingTerm])))

/-- Paper-level statement-boundary soundness for arbitrary typing
environments, store typings, ambient lifetimes, and result types. -/
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

/-- If a sealed statement-boundary approximation checks, the original
partial block has a well-typed completion. -/
theorem sealProgram_completedStatementBoundary_sound
    {lifetime : Lifetime} {pre : List Term}
    (hSealed : ProgramWellTyped
      (sealProgram
        (Generated.PartialTerm.blockTerms lifetime
          (Generated.PartialTerms.elems pre none)))) :
    Completable ProgramWellTyped CompletesProgram
      (Generated.PartialTerm.blockTerms lifetime
        (Generated.PartialTerms.elems pre none)) := by
  exact ⟨_, sealProgram_completedStatementBoundary_completes, hSealed⟩

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
