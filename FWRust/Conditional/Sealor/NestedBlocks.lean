import FWRust.Sealor.Definitions
import FWRust.Conditional.Paper.Typing
import FWRust.Conditional.Sealor.PartialProgram

/-!
# Conditional frontier sealor

This is the conditional-language counterpart of `FWRust.Sealor`'s
nested-block sealor.  It follows the expression/statement split in
`rust_constraining`'s `ast_copier.rs`:

* a completed prefix is kept;
* incomplete blocks are closed by the typed, diverging `Term.missing`;
* a completed then branch with no completed else branch becomes
  `if c { t } else { missing }`;
* an incomplete then branch is sealed with a diverging completion in both
  branches, matching the copier's `{ panic!() } else { panic!() }` fallback;
* an incomplete else branch is the diverging branch of `T-IfDiv`;
* non-block branch frontiers fall back to conservative statement extraction.
  In particular, this fallback does not claim to reproduce the copier's
  outer `else if` chain exactly.

The last distinction is forced by the generic completion theorem.  Rebuilding
`if c { t } else { seal p }` would require fresh type and environment joins
between `t` and `seal p`; typing the complete program supplies joins only for
the unknown completion of `p`, and sealing may deliberately change its result
type and environment.  Placing the sealed frontier in a fresh diverging block
would avoid those joins, but would instead require retyping arbitrary retained
terms at a new child lifetime.  Such lifetime rebasing is false in general for
nested blocks and declarations.  The statement fallback below retains the
typed frontier evidence without adding either historical premise.

No declaration in the reduced `FWRust.Sealor` namespace is changed.
-/

namespace FWRust.Conditional.Sealor

open FWRust.Conditional.Core
open FWRust.Conditional.Paper

/-- The object-language analogue of the copier's polymorphic
`__missing__()`/`panic!()` completion. -/
abbrev missingTerm : Term :=
  .missing

/-- A lifetime for the block synthesized when the parser has seen only `{`. -/
def childLifetime (lifetime : Lifetime) : Lifetime :=
  { path := lifetime.path ++ [0] }

mutual

/-- Seal a partial expression in value position. -/
def sealTerm (currentLifetime : Lifetime) : PartialTerm → Term
  | .cutoff => missingTerm
  | .done term => term
  | .blockStart => .block (childLifetime currentLifetime) [missingTerm]
  | .blockTerms lifetime terms => .block lifetime (sealTerms lifetime terms)
  | frontier => (sealTermStmts currentLifetime frontier).headD missingTerm

/-- Seal a partial expression in statement position.  For the generic
non-block fallback, only evidence from the branch containing the parser
frontier is retained; see the module note for why reconstructing the outer
conditional would require an unavailable join or lifetime-rebasing premise. -/
def sealTermStmts (currentLifetime : Lifetime) : PartialTerm → List Term
  | .cutoff => []
  | .done term => [term]
  | .blockStart => [.block (childLifetime currentLifetime) [missingTerm]]
  | .blockTerms lifetime terms => [.block lifetime (sealTerms lifetime terms)]
  | .eqLhs lhs => sealTermStmts currentLifetime lhs
  | .eqRhs lhs _rhs => [lhs]
  | .iteStart => []
  | .iteCondition condition => sealTermStmts currentLifetime condition
  | .iteTrueBranch condition (.done trueTerm) =>
      [.ite condition trueTerm missingTerm]
  | .iteTrueBranch condition .cutoff =>
      [.ite condition missingTerm missingTerm]
  | .iteTrueBranch condition .blockStart =>
      [.ite condition
        (.block (childLifetime currentLifetime) [missingTerm]) missingTerm]
  | .iteTrueBranch condition (.blockTerms lifetime (.done terms)) =>
      [.ite condition (.block lifetime terms) missingTerm]
  | .iteTrueBranch condition (.blockTerms lifetime terms) =>
      [.ite condition (.block lifetime (sealTerms lifetime terms)) missingTerm]
  | .iteTrueBranch condition trueBranch =>
      condition :: sealTermStmts currentLifetime trueBranch
  | .iteFalseBranch condition trueBranch (.done falseTerm) =>
      [.ite condition trueBranch falseTerm]
  | .iteFalseBranch condition trueBranch .cutoff =>
      [.ite condition trueBranch missingTerm]
  | .iteFalseBranch condition trueBranch .blockStart =>
      [.ite condition trueBranch
        (.block (childLifetime currentLifetime) [missingTerm])]
  | .iteFalseBranch condition trueBranch
      (.blockTerms lifetime (.done terms)) =>
      [.ite condition trueBranch (.block lifetime terms)]
  | .iteFalseBranch condition trueBranch (.blockTerms lifetime terms) =>
      [.ite condition trueBranch (.block lifetime (sealTerms lifetime terms))]
  | .iteFalseBranch condition _trueBranch falseBranch =>
      condition :: sealTermStmts currentLifetime falseBranch
termination_by p => (sizeOf p, 0)

/-- Seal a block-body frontier, keeping its completed prefix and closing every
incomplete body with `missingTerm`. -/
def sealTerms (currentLifetime : Lifetime) : PartialTerms → List Term
  | .cutoff => [missingTerm]
  | .done terms => terms
  | .elems pre none => pre ++ [missingTerm]
  | .elems pre (some frontier) =>
      pre ++ sealTermStmts currentLifetime frontier ++ [missingTerm]
termination_by p => (sizeOf p, 0)

end

def sealProgram : PartialProgram → Program :=
  sealTerm Lifetime.root

def ProgramWellTyped (program : Program) : Prop :=
  ∃ ty env,
    TermTyping Env.empty StoreTyping.empty Lifetime.root program ty env

def programWellTyped : Program → Prop :=
  ProgramWellTyped

/-- The checker induced by sealing and the extended FW Rust type checker. -/
def nestedBlocksPrefixChecker : PartialProgram → Prop :=
  ConservativeSealor.SealorPrefixChecker programWellTyped sealProgram

section TypedSealing

theorem tyLoanFree_unit : TyLoanFree .unit := by
  intro mutable targets hcontains
  cases hcontains

theorem missingTerm_typed {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping env typing lifetime missingTerm .unit env :=
  TermTyping.missing WellFormedTy.unit tyLoanFree_unit

/-- Sequential typing without fixing the last statement's result type. -/
inductive StmtsTyping :
    Env → StoreTyping → Lifetime → List Term → Env → Prop where
  | nil {env : Env} {typing : StoreTyping} {lifetime : Lifetime} :
      StmtsTyping env typing lifetime [] env
  | cons {env₁ env₂ env₃ : Env} {typing : StoreTyping}
      {lifetime : Lifetime} {term : Term} {rest : List Term} {ty : Ty} :
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

theorem stmtsTyping_missing_closed {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {stmts : List Term}
    (hstmts : StmtsTyping env typing lifetime stmts env₂) :
    TermListTyping env typing lifetime (stmts ++ [missingTerm]) .unit env₂ := by
  induction hstmts with
  | nil => exact .singleton missingTerm_typed
  | cons hterm _ ih => exact .cons hterm ih

theorem missingBlock_typed {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping env typing lifetime
      (.block (childLifetime lifetime) [missingTerm]) .unit
      (env.dropLifetime (childLifetime lifetime)) :=
  TermTyping.block ⟨0, rfl⟩ (.singleton missingTerm_typed)
    WellFormedTy.unit rfl

/-- Every incomplete sealed block body contains the diverging placeholder. -/
theorem missing_mem_sealTerms {currentLifetime : Lifetime}
    {p : PartialTerms}
    (hne : ∀ terms, p ≠ .done terms) :
    missingTerm ∈ sealTerms currentLifetime p := by
  cases p with
  | cutoff => simp [sealTerms]
  | done terms => exact absurd rfl (hne terms)
  | elems pre frontier =>
      cases frontier <;> simp [sealTerms]

/-- Consequently every incomplete sealed block is syntactically diverging. -/
theorem incompleteBlock_diverges {currentLifetime blockLifetime : Lifetime}
    {p : PartialTerms}
    (hne : ∀ terms, p ≠ .done terms) :
    Term.Diverges (.block blockLifetime (sealTerms currentLifetime p)) :=
  .block (missing_mem_sealTerms hne) .missing

theorem headD_typed {env env' : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List Term}
    (hstmts : StmtsTyping env typing lifetime stmts env') :
    ∃ ty' env'', TermTyping env typing lifetime
      (stmts.headD missingTerm) ty' env'' := by
  cases hstmts with
  | nil => exact ⟨.unit, env, missingTerm_typed⟩
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
      exact ⟨.unit, env, missingTerm_typed⟩
  case done =>
      cases hcomp
      simp only [sealTerm]
      exact ⟨ty, env₂, htyped⟩
  case blockStart =>
      simp only [sealTerm]
      exact ⟨.unit, _, missingBlock_typed⟩
  case blockTerms blockLifetime terms =>
      cases hcomp with
      | blockTerms hterms =>
          cases htyped with
          | block hchild hlist hwf _ =>
              obtain ⟨ty', envBody, hlist', hresult⟩ :=
                sealTerms_typed hterms hlist
              simp only [sealTerm]
              refine ⟨ty', envBody.dropLifetime blockLifetime,
                TermTyping.block hchild hlist' ?_ rfl⟩
              rcases hresult with rfl | ⟨rfl, rfl⟩
              · exact WellFormedTy.unit
              · exact hwf
  all_goals
    simp only [sealTerm]
    obtain ⟨env', hstmts⟩ := sealTermStmts_typed hcomp htyped
    exact headD_typed hstmts

theorem sealTermStmts_typed {currentLifetime : Lifetime}
    {p : PartialTerm} {completion : Term} {env env₂ : Env}
    {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerm p completion)
    (htyped : TermTyping env typing currentLifetime completion ty env₂) :
    ∃ env', StmtsTyping env typing currentLifetime
      (sealTermStmts currentLifetime p) env' := by
  cases hcomp
  case done =>
      simp only [sealTermStmts]
      exact ⟨env₂, .cons htyped .nil⟩
  case blockStart =>
      simp only [sealTermStmts]
      exact ⟨_, .cons missingBlock_typed .nil⟩
  case blockTerms hterms =>
      cases htyped with
      | block hchild hlist hwf _ =>
          obtain ⟨ty', envBody, hlist', hresult⟩ :=
            sealTerms_typed hterms hlist
          simp only [sealTermStmts]
          refine ⟨envBody.dropLifetime _,
            .cons (TermTyping.block hchild hlist' ?_ rfl) .nil⟩
          rcases hresult with rfl | ⟨rfl, rfl⟩
          · exact WellFormedTy.unit
          · exact hwf
  case eqLhs hlhs =>
      cases htyped with
      | eq hlhs' =>
          simp only [sealTermStmts]
          exact sealTermStmts_typed hlhs hlhs'
  case eqRhs hrhs =>
      cases htyped with
      | eq hlhs' =>
          simp only [sealTermStmts]
          exact ⟨_, .cons hlhs' .nil⟩
  case iteCondition hcondition =>
      simp only [sealTermStmts]
      cases htyped with
      | ite hcondition' =>
          exact sealTermStmts_typed hcondition hcondition'
      | iteDiverging hcondition' =>
          exact sealTermStmts_typed hcondition hcondition'
      | iteTrueDiverging hcondition' =>
          exact sealTermStmts_typed hcondition hcondition'
  case iteTrueBranch condition trueBranch trueCompletion falseCompletion htrue =>
      obtain ⟨envMid, hcondition', tyLive, envOut, htrue'⟩ :
          ∃ envMid,
            TermTyping env typing currentLifetime condition .bool envMid ∧
            ∃ tyLive envOut,
              TermTyping envMid typing currentLifetime trueCompletion tyLive
                envOut := by
        cases htyped with
        | ite hcondition' htrue' => exact ⟨_, hcondition', _, _, htrue'⟩
        | iteDiverging hcondition' htrue' =>
            exact ⟨_, hcondition', _, _, htrue'⟩
        | iteTrueDiverging hcondition' htrue' =>
            exact ⟨_, hcondition', _, _, htrue'⟩
      cases trueBranch
      case done trueTerm =>
          cases htrue
          simp only [sealTermStmts]
          exact ⟨envOut, .cons
            (TermTyping.iteDiverging hcondition' htrue' missingTerm_typed
              .missing) .nil⟩
      case cutoff =>
          simp only [sealTermStmts]
          exact ⟨envMid, .cons
            (TermTyping.iteDiverging hcondition' missingTerm_typed
              missingTerm_typed .missing) .nil⟩
      case blockStart =>
          simp only [sealTermStmts]
          exact ⟨_, .cons
            (TermTyping.iteDiverging hcondition' missingBlock_typed
              missingTerm_typed .missing) .nil⟩
      case blockTerms blockLifetime terms =>
          cases htrue with
          | blockTerms hterms =>
              cases terms
              case done xs =>
                  cases hterms
                  simp only [sealTermStmts]
                  exact ⟨envOut, .cons
                    (TermTyping.iteDiverging hcondition' htrue'
                      missingTerm_typed .missing) .nil⟩
              all_goals
                cases htrue' with
                | block hchild hlist hwf _ =>
                    obtain ⟨tyBody, envBody, hlist', hresult⟩ :=
                      sealTerms_typed hterms hlist
                    simp only [sealTermStmts]
                    refine ⟨_, .cons
                      (TermTyping.iteDiverging hcondition'
                        (TermTyping.block hchild hlist' ?_ rfl)
                        missingTerm_typed .missing) .nil⟩
                    rcases hresult with rfl | ⟨rfl, rfl⟩
                    · exact WellFormedTy.unit
                    · exact hwf
      all_goals
        obtain ⟨env', hstmts⟩ := sealTermStmts_typed htrue htrue'
        simp only [sealTermStmts] at hstmts ⊢
        exact ⟨env', .cons hcondition' hstmts⟩
  case iteFalseBranch condition trueBranch falseBranch falseCompletion hfalse =>
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
      cases falseBranch
      case done falseTerm =>
          cases hfalse
          simp only [sealTermStmts]
          exact ⟨env₂, .cons htyped .nil⟩
      case cutoff =>
          simp only [sealTermStmts]
          exact ⟨envOut, .cons
            (TermTyping.iteDiverging hcondition' htrue' missingTerm_typed
              .missing) .nil⟩
      case blockStart =>
          simp only [sealTermStmts]
          exact ⟨envOut, .cons
            (TermTyping.iteDiverging hcondition' htrue' missingBlock_typed
              (.block (by simp [missingTerm]) .missing)) .nil⟩
      case blockTerms blockLifetime terms =>
          cases hfalse with
          | blockTerms hterms =>
              cases terms
              case done xs =>
                  cases hterms
                  simp only [sealTermStmts]
                  exact ⟨env₂, .cons htyped .nil⟩
              all_goals
                cases hfalse' with
                | block hchild hlist hwf _ =>
                    obtain ⟨tyBody, envBody, hlist', hresult⟩ :=
                      sealTerms_typed hterms hlist
                    simp only [sealTermStmts]
                    refine ⟨envOut, .cons
                      (TermTyping.iteDiverging hcondition' htrue'
                        (TermTyping.block hchild hlist' ?_ rfl)
                        (incompleteBlock_diverges nofun)) .nil⟩
                    rcases hresult with rfl | ⟨rfl, rfl⟩
                    · exact WellFormedTy.unit
                    · exact hwf
      all_goals
        obtain ⟨env', hstmts⟩ := sealTermStmts_typed hfalse hfalse'
        simp only [sealTermStmts] at hstmts ⊢
        exact ⟨env', .cons hcondition' hstmts⟩
  all_goals
    simp only [sealTermStmts]
    exact ⟨env, .nil⟩
termination_by (sizeOf p, 0)
decreasing_by
  all_goals decreasing_tactic

theorem sealTerms_typed {currentLifetime : Lifetime} {p : PartialTerms}
    {completions : List Term} {env env₂ : Env} {typing : StoreTyping}
    {ty : Ty}
    (hcomp : CompletesTerms p completions)
    (hlist : TermListTyping env typing currentLifetime completions ty env₂) :
    ∃ ty' env', TermListTyping env typing currentLifetime
        (sealTerms currentLifetime p) ty' env' ∧
      (ty' = .unit ∨ (ty' = ty ∧ env' = env₂)) := by
  cases hcomp
  case done =>
      simp only [sealTerms]
      exact ⟨ty, env₂, hlist, Or.inr ⟨rfl, rfl⟩⟩
  case cutoff =>
      simp only [sealTerms]
      exact ⟨.unit, env, .singleton missingTerm_typed, Or.inl rfl⟩
  case elemsDone =>
      obtain ⟨mid, hprefix, _⟩ :=
        stmtsTyping_append_inv (termListTyping_toStmts hlist)
      simp only [sealTerms]
      exact ⟨.unit, mid, stmtsTyping_missing_closed hprefix, Or.inl rfl⟩
  case elemsFrontier hfrontier =>
      obtain ⟨mid, hprefix, hrest⟩ :=
        stmtsTyping_append_inv (termListTyping_toStmts hlist)
      cases hrest with
      | cons hfrontier' _ =>
          obtain ⟨env', hstmts⟩ :=
            sealTermStmts_typed hfrontier hfrontier'
          simp only [sealTerms]
          refine ⟨.unit, env', ?_, Or.inl rfl⟩
          have happend := stmtsTyping_missing_closed
            (stmtsTyping_append hprefix hstmts)
          simpa [List.append_assoc] using happend
termination_by (sizeOf p, 0)
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

/-- Conditional sealor completeness: any partial frontier having a well-typed
completion seals to a well-typed conditional-language program. -/
theorem nestedBlocksPrefixChecker_complete :
    ConservativeSealor.PrefixCheckerComplete ProgramWellTyped CompletesProgram
      nestedBlocksPrefixChecker := by
  intro p hcompletable
  rcases hcompletable with ⟨full, hCompletion, hFull⟩
  exact sealProgram_wellTyped_of_completion hCompletion hFull

/-- The equivalent contrapositive/conservativity formulation. -/
theorem sealProgram_conservative :
    ConservativeSealor.Conservative ProgramWellTyped CompletesProgram
      sealProgram := by
  intro p hInvalid full hCompletion hFull
  exact hInvalid (sealProgram_wellTyped_of_completion hCompletion hFull)

end TypedSealing

end FWRust.Conditional.Sealor
