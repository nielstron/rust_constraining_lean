import LwRust.Extractor.Extractors.NestedBlocks

/-!
Completeness of the nested-block extractor for a relaxed control-flow typing
relation.

The strict mechanisation checks borrow safety after `if`/`while` environment
joins so that the global borrow-safety theorem can thread a safe environment
through all typing rules.  This file keeps the same syntax, extractor, and all
non-join obligations, but defines a relaxed typing relation that does not
enforce the post-merge borrow-safety premises:

* `T-If` omits `BorrowSafeEnv` for the joined environment and
  `TyBorrowSafeAgainstEnv` for the joined result type.
* `T-While` omits `BorrowSafeEnv` for the loop invariant environment.

The result below is only extractor completeness for that relaxed checker.  It
does not claim preservation or borrow safety for the relaxed system.
-/

namespace LwRust
namespace Paper

open Core

mutual

/-- Typing with borrow-safety checks omitted after control-flow joins. -/
inductive RelaxedTermTyping : Env → StoreTyping → Lifetime → Term → Ty → Env → Prop where
  /-- T-Const. -/
  | const {env : Env} {typing : StoreTyping} {lifetime : Lifetime}
      {value : Value} {ty : Ty} :
      ValueTyping typing value ty →
      RelaxedTermTyping env typing lifetime (.val value) ty env
  /-- T-Missing. -/
  | missing {env : Env} {typing : StoreTyping} {lifetime : Lifetime}
      {ty : Ty} :
      WellFormedTy env ty lifetime →
      TyLoanFree ty →
      RelaxedTermTyping env typing lifetime .missing ty env
  /-- T-Copy. -/
  | copy {env : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
      {lv : LVal} {ty : Ty} :
      LValTyping env lv (.ty ty) valueLifetime →
      CopyTy ty →
      ¬ ReadProhibited env lv →
      RelaxedTermTyping env typing lifetime (.copy lv) ty env
  /-- T-Move. -/
  | move {env1 env2 : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
      {lv : LVal} {ty : Ty} :
      LValTyping env1 lv (.ty ty) valueLifetime →
      ¬ WriteProhibited env1 lv →
      EnvMove env1 lv env2 →
      RelaxedTermTyping env1 typing lifetime (.move lv) ty env2
  /-- T-MutBorrow. -/
  | mutBorrow {env : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
      {lv : LVal} {ty : Ty} :
      LValTyping env lv (.ty ty) valueLifetime →
      Mutable env lv →
      ¬ WriteProhibited env lv →
      RelaxedTermTyping env typing lifetime
        (Term.borrow Bool.true lv) (Ty.borrow Bool.true [lv]) env
  /-- T-ImmBorrow. -/
  | immBorrow {env : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
      {lv : LVal} {ty : Ty} :
      LValTyping env lv (.ty ty) valueLifetime →
      ¬ ReadProhibited env lv →
      RelaxedTermTyping env typing lifetime
        (Term.borrow Bool.false lv) (Ty.borrow Bool.false [lv]) env
  /-- T-Box. -/
  | box {env1 env2 : Env} {typing : StoreTyping} {lifetime : Lifetime}
      {term : Term} {ty : Ty} :
      RelaxedTermTyping env1 typing lifetime term ty env2 →
      RelaxedTermTyping env1 typing lifetime (.box term) (.box ty) env2
  /-- T-Block. -/
  | block {env1 env2 env3 : Env} {typing : StoreTyping}
      {lifetime blockLifetime : Lifetime} {terms : List Term} {ty : Ty} :
      LifetimeChild lifetime blockLifetime →
      RelaxedTermListTyping env1 typing blockLifetime terms ty env2 →
      WellFormedTy env2 ty lifetime →
      env3 = env2.dropLifetime blockLifetime →
      RelaxedTermTyping env1 typing lifetime (.block blockLifetime terms) ty env3
  /-- T-Declare. -/
  | declare {env1 env2 env3 : Env} {typing : StoreTyping} {lifetime : Lifetime}
      {x : Name} {term : Term} {ty : Ty} :
      env1.fresh x →
      RelaxedTermTyping env1 typing lifetime term ty env2 →
      env2.fresh x →
      FreshUpdateCoherenceObligations env2 x ty lifetime →
      env3 = env2.update x { ty := .ty ty, lifetime := lifetime } →
      RelaxedTermTyping env1 typing lifetime (.letMut x term) .unit env3
  /-- T-Assign. -/
  | assign {env1 env2 env3 : Env} {typing : StoreTyping}
      {lifetime targetLifetime : Lifetime} {lhs : LVal}
      {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
      RelaxedTermTyping env1 typing lifetime rhs rhsTy env2 →
      LValTyping env2 lhs oldTy targetLifetime →
      ShapeCompatible env2 oldTy (.ty rhsTy) →
      WellFormedTy env2 rhsTy targetLifetime →
      EnvWrite 0 env2 lhs rhsTy env3 →
      (∃ phi, LinearizedBy phi env2 ∧ EnvWriteRhsBorrowTargetsBelow phi env3 rhsTy) →
      Coherent env3 →
      EnvWriteRhsTargetsWellFormed env3 rhsTy →
      ¬ WriteProhibited env3 lhs →
      RelaxedTermTyping env1 typing lifetime (.assign lhs rhs) .unit env3
  /-- T-Eq. -/
  | eq {env1 env2 env3 envGhost : Env} {ghost : Name}
      {typing : StoreTyping} {lifetime : Lifetime}
      {lhs rhs : Term} {lhsTy rhsTy : Ty} :
      RelaxedTermTyping env1 typing lifetime lhs lhsTy env2 →
      env2.fresh ghost →
      Env.TypeNameFresh env2 ghost →
      ghost ∉ Ty.vars lhsTy →
      StoreTyping.TypeNameFresh typing ghost →
      RelaxedTermTyping
        (env2.update ghost { ty := .ty lhsTy, lifetime := lifetime })
        typing lifetime rhs rhsTy envGhost →
      ¬ LwRust.Paper.Term.Mentions ghost rhs →
      env3 = envGhost.erase ghost →
      CopyTy lhsTy →
      CopyTy rhsTy →
      ShapeCompatible env3 (.ty lhsTy) (.ty rhsTy) →
      RelaxedTermTyping env1 typing lifetime (.eq lhs rhs) .bool env3
  /-- T-If, without post-join borrow-safety checks. -/
  | ite {env1 env2 env3 env4 env5 : Env} {typing : StoreTyping}
      {lifetime : Lifetime} {condition trueBranch falseBranch : Term}
      {trueTy falseTy joinTy : Ty} :
      RelaxedTermTyping env1 typing lifetime condition .bool env2 →
      RelaxedTermTyping env2 typing lifetime trueBranch trueTy env3 →
      RelaxedTermTyping env2 typing lifetime falseBranch falseTy env4 →
      PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy) →
      EnvJoin env3 env4 env5 →
      EnvJoinSameShape env3 env5 →
      EnvJoinSameShape env4 env5 →
      WellFormedTy env5 joinTy lifetime →
      Coherent env5 →
      Linearizable env5 →
      RelaxedTermTyping env1 typing lifetime (.ite condition trueBranch falseBranch)
        joinTy env5
  /-- T-IfDiv. -/
  | iteDiverging {env1 env2 env3 env4 : Env} {typing : StoreTyping}
      {lifetime : Lifetime} {condition trueBranch falseBranch : Term}
      {trueTy falseTy : Ty} :
      RelaxedTermTyping env1 typing lifetime condition .bool env2 →
      RelaxedTermTyping env2 typing lifetime trueBranch trueTy env3 →
      RelaxedTermTyping env2 typing lifetime falseBranch falseTy env4 →
      falseBranch.Diverges →
      RelaxedTermTyping env1 typing lifetime
        (.ite condition trueBranch falseBranch) trueTy env3
  /-- T-IfDivT. -/
  | iteTrueDiverging {env1 env2 env3 env4 : Env} {typing : StoreTyping}
      {lifetime : Lifetime} {condition trueBranch falseBranch : Term}
      {trueTy falseTy : Ty} :
      RelaxedTermTyping env1 typing lifetime condition .bool env2 →
      RelaxedTermTyping env2 typing lifetime trueBranch trueTy env3 →
      RelaxedTermTyping env2 typing lifetime falseBranch falseTy env4 →
      trueBranch.Diverges →
      RelaxedTermTyping env1 typing lifetime
        (.ite condition trueBranch falseBranch) falseTy env4
  /-- T-WhileDiv. -/
  | whileLoopDiverging {env1 env2 env3 : Env} {typing : StoreTyping}
      {lifetime bodyLifetime : Lifetime} {condition body : Term}
      {bodyTy : Ty} :
      LifetimeChild lifetime bodyLifetime →
      RelaxedTermTyping env1 typing lifetime condition .bool env2 →
      RelaxedTermTyping env2 typing bodyLifetime body bodyTy env3 →
      body.Diverges →
      RelaxedTermTyping env1 typing lifetime
        (.whileLoop bodyLifetime condition body) .unit env2
  /-- T-While, without post-join borrow-safety checks. -/
  | whileLoop {env1 envBack envInv env2 envEntry2 env3 envEntry3 : Env}
      {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
      {condition body : Term} {bodyTy bodyEntryTy : Ty} :
      LifetimeChild lifetime bodyLifetime →
      EnvJoin env1 envBack envInv →
      EnvJoinSameShape env1 envInv →
      EnvJoinSameShape envBack envInv →
      ContainedBorrowsWellFormed envInv →
      Coherent envInv →
      Linearizable envInv →
      RelaxedTermTyping envInv typing lifetime condition .bool env2 →
      RelaxedTermTyping env2 typing bodyLifetime body bodyTy env3 →
      WellFormedTy env3 bodyTy lifetime →
      env3.dropLifetime bodyLifetime = envBack →
      RelaxedTermTyping env1 typing lifetime condition .bool envEntry2 →
      RelaxedTermTyping envEntry2 typing bodyLifetime body bodyEntryTy envEntry3 →
      RelaxedTermTyping env1 typing lifetime
        (.whileLoop bodyLifetime condition body) .unit env2

inductive RelaxedTermListTyping :
    Env → StoreTyping → Lifetime → List Term → Ty → Env → Prop where
  /-- T-Seq, singleton sequence. -/
  | singleton {env1 env2 : Env} {typing : StoreTyping} {lifetime : Lifetime}
      {term : Term} {ty : Ty} :
      RelaxedTermTyping env1 typing lifetime term ty env2 →
      RelaxedTermListTyping env1 typing lifetime [term] ty env2
  /-- T-Seq, environment threading through `t1; ...; tn`. -/
  | cons {env1 env2 env3 : Env} {typing : StoreTyping} {lifetime : Lifetime}
      {term : Term} {rest : List Term} {termTy finalTy : Ty} :
      RelaxedTermTyping env1 typing lifetime term termTy env2 →
      RelaxedTermListTyping env2 typing lifetime rest finalTy env3 →
      RelaxedTermListTyping env1 typing lifetime (term :: rest) finalTy env3

end

end Paper
end LwRust

namespace ConservativeExtractor

open LwRust.Paper

/-- Complete-program checker using the relaxed join typing relation. -/
def ProgramRelaxedWellTyped (program : Program) : Prop :=
  ∃ ty env,
    RelaxedTermTyping Env.empty StoreTyping.empty LwRust.Core.Lifetime.root
      program ty env

def programRelaxedWellTyped : Program → Prop :=
  ProgramRelaxedWellTyped

theorem programRelaxedWellTyped_complete :
    CheckerComplete ProgramRelaxedWellTyped programRelaxedWellTyped := by
  intro program hprogram
  exact hprogram

section RelaxedTypedExtraction

/-- Sequential statement typing for relaxed typing. -/
inductive RelaxedStmtsTyping :
    Env → StoreTyping → Lifetime → List Term → Env → Prop where
  | nil {env : Env} {typing : StoreTyping} {lifetime : Lifetime} :
      RelaxedStmtsTyping env typing lifetime [] env
  | cons {env1 env2 env3 : Env} {typing : StoreTyping} {lifetime : Lifetime}
      {term : Term} {rest : List Term} {ty : Ty} :
      RelaxedTermTyping env1 typing lifetime term ty env2 →
      RelaxedStmtsTyping env2 typing lifetime rest env3 →
      RelaxedStmtsTyping env1 typing lifetime (term :: rest) env3

theorem relaxedTermListTyping_toStmts {typing : StoreTyping} {lifetime : Lifetime}
    {terms : List Term} :
    ∀ {env env2 : Env} {ty : Ty},
      RelaxedTermListTyping env typing lifetime terms ty env2 →
      RelaxedStmtsTyping env typing lifetime terms env2 := by
  induction terms with
  | nil =>
      intro env env2 ty hlist
      cases hlist
  | cons term rest ih =>
      intro env env2 ty hlist
      cases hlist with
      | singleton hterm => exact .cons hterm .nil
      | cons hterm hrest => exact .cons hterm (ih hrest)

theorem relaxedStmtsTyping_append {env mid env2 : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {xs ys : List Term}
    (hxs : RelaxedStmtsTyping env typing lifetime xs mid) :
    RelaxedStmtsTyping mid typing lifetime ys env2 →
    RelaxedStmtsTyping env typing lifetime (xs ++ ys) env2 := by
  induction hxs with
  | nil => exact fun hys => hys
  | cons hterm _ ih => exact fun hys => .cons hterm (ih hys)

theorem relaxedStmtsTyping_append_inv {typing : StoreTyping} {lifetime : Lifetime}
    {xs ys : List Term} :
    ∀ {env env2 : Env},
      RelaxedStmtsTyping env typing lifetime (xs ++ ys) env2 →
      ∃ mid, RelaxedStmtsTyping env typing lifetime xs mid ∧
        RelaxedStmtsTyping mid typing lifetime ys env2 := by
  induction xs with
  | nil =>
      intro env env2 hstmts
      exact ⟨env, .nil, hstmts⟩
  | cons x xs ih =>
      intro env env2 hstmts
      cases hstmts with
      | cons hterm hrest =>
          obtain ⟨mid, hxs, hys⟩ := ih hrest
          exact ⟨mid, .cons hterm hxs, hys⟩

/-- Closing a relaxed statement run with `missingTerm` yields a block body. -/
theorem relaxedStmtsTyping_missing_closed {env env2 : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List Term}
    (hstmts : RelaxedStmtsTyping env typing lifetime stmts env2) :
    RelaxedTermListTyping env typing lifetime (stmts ++ [missingTerm]) .unit env2 := by
  induction hstmts with
  | nil => exact .singleton (.missing WellFormedTy.unit tyLoanFree_unit)
  | cons hterm _ ih => exact .cons hterm ih

/-- The synthesized block for an unopened block frontier types in the relaxed relation. -/
theorem relaxedMissingBlock_typed {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} :
    RelaxedTermTyping env typing lifetime
      (SyntaxCtor.ctermBlock_ctor (childLifetime lifetime) [missingTerm])
      .unit (env.dropLifetime (childLifetime lifetime)) :=
  RelaxedTermTyping.block ⟨0, rfl⟩
    (RelaxedTermListTyping.singleton
      (RelaxedTermTyping.missing WellFormedTy.unit tyLoanFree_unit))
    WellFormedTy.unit rfl

theorem relaxedHeadD_typed {env env' : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {stmts : List Term}
    (hstmts : RelaxedStmtsTyping env typing lifetime stmts env') :
    ∃ ty' env'', RelaxedTermTyping env typing lifetime
      (stmts.headD missingTerm) ty' env'' := by
  cases hstmts with
  | nil => exact ⟨.unit, env, .missing WellFormedTy.unit tyLoanFree_unit⟩
  | cons hfirst _ => exact ⟨_, _, hfirst⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
mutual

/-- Value-position transport for the relaxed typing relation. -/
theorem extractTerm_relaxedTyped {currentLifetime : Lifetime} {p : PartialTerm}
    {completion : Term} {env env2 : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerm p completion)
    (htyped : RelaxedTermTyping env typing currentLifetime completion ty env2) :
    ∃ ty' env', RelaxedTermTyping env typing currentLifetime
      (extractTerm currentLifetime p) ty' env' := by
  cases p
  case cutoff =>
      simp only [extractTerm]
      exact ⟨.unit, env, .missing WellFormedTy.unit tyLoanFree_unit⟩
  case done =>
      cases hcomp
      simp only [extractTerm]
      exact ⟨ty, env2, htyped⟩
  case intN =>
      cases hcomp
      simp only [extractTerm]
      exact ⟨ty, env2, htyped⟩
  case blockStart =>
      simp only [extractTerm]
      exact ⟨.unit, _, relaxedMissingBlock_typed⟩
  case blockTerms blockLifetime terms =>
      cases hcomp with
      | ctermBlock_blockTerms hterms =>
          cases htyped with
          | «block» hchild hlist hwf heq =>
              obtain ⟨ty', envBody, hlist', hdisj⟩ :=
                extractTerms_relaxedTyped hterms hlist
              simp only [extractTerm]
              refine ⟨ty', envBody.dropLifetime blockLifetime,
                RelaxedTermTyping.block hchild hlist' ?_ rfl⟩
              rcases hdisj with rfl | ⟨rfl, rfl⟩
              · exact WellFormedTy.unit
              · exact hwf
  all_goals
    simp only [extractTerm]
    obtain ⟨env', hstmts⟩ := extractTermStmts_relaxedTyped hcomp htyped
    exact relaxedHeadD_typed hstmts
termination_by (sizeOf p, 1)
decreasing_by
  all_goals
    first
    | decreasing_tactic
    | (simp_wf
       try subst_vars
       exact Prod.Lex.right _ (by omega))

/-- Statement-position transport for the relaxed typing relation. -/
theorem extractTermStmts_relaxedTyped {currentLifetime : Lifetime} {p : PartialTerm}
    {completion : Term} {env env2 : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerm p completion)
    (htyped : RelaxedTermTyping env typing currentLifetime completion ty env2) :
    ∃ env', RelaxedStmtsTyping env typing currentLifetime
      (extractTermStmts currentLifetime p) env' := by
  cases hcomp
  case done =>
      simp only [extractTermStmts]
      exact ⟨env2, .cons htyped .nil⟩
  case ctermBlock_blockStart =>
      simp only [extractTermStmts]
      exact ⟨_, .cons relaxedMissingBlock_typed .nil⟩
  case ctermBlock_blockTerms hterms =>
      cases htyped with
      | «block» hchild hlist hwf heq =>
          obtain ⟨ty', envBody, hlist', hdisj⟩ :=
            extractTerms_relaxedTyped hterms hlist
          simp only [extractTermStmts]
          refine ⟨envBody.dropLifetime _,
            .cons (RelaxedTermTyping.block hchild hlist' ?_ rfl) .nil⟩
          rcases hdisj with rfl | ⟨rfl, rfl⟩
          · exact WellFormedTy.unit
          · exact hwf
  case ctermLetMut_letMutRhs hinit =>
      cases htyped with
      | declare _ hinit' _ _ _ =>
          simp only [extractTermStmts]
          exact extractTermStmts_relaxedTyped hinit hinit'
  case ctermAssign_assignRhs hrhs =>
      cases htyped with
      | assign hrhs' _ _ _ _ _ _ _ _ =>
          simp only [extractTermStmts]
          exact extractTermStmts_relaxedTyped hrhs hrhs'
  case ctermBox_boxOperand hoperand =>
      cases htyped with
      | «box» hoperand' =>
          simp only [extractTermStmts]
          exact extractTermStmts_relaxedTyped hoperand hoperand'
  case ctermEq_termPrefix hlhs =>
      simp only [SyntaxCtor.ctermEq_ctor] at htyped
      change RelaxedTermTyping env typing currentLifetime (.eq _ _) ty env2 at htyped
      cases htyped with
      | eq hlhs' =>
          simp only [extractTermStmts]
          exact extractTermStmts_relaxedTyped hlhs hlhs'
  case ctermEq_eqRhs hrhs =>
      simp only [SyntaxCtor.ctermEq_ctor] at htyped
      change RelaxedTermTyping env typing currentLifetime (.eq _ _) ty env2 at htyped
      cases htyped with
      | eq hlhs' =>
          simp only [extractTermStmts]
          exact ⟨_, .cons hlhs' .nil⟩
  case ctermIte_iteCondition hcondition =>
      simp only [extractTermStmts]
      cases htyped with
      | ite hcondition' =>
          exact extractTermStmts_relaxedTyped hcondition hcondition'
      | iteDiverging hcondition' =>
          exact extractTermStmts_relaxedTyped hcondition hcondition'
      | iteTrueDiverging hcondition' =>
          exact extractTermStmts_relaxedTyped hcondition hcondition'
  case ctermIte_iteTrueBranch condition trueBranch trueCompletion
      falseCompletion htrue =>
      obtain ⟨envMid, hcondition', tyLive, envOut, htrue'⟩ :
          ∃ envMid,
            RelaxedTermTyping env typing currentLifetime condition .bool envMid ∧
            ∃ tyLive envOut,
              RelaxedTermTyping envMid typing currentLifetime trueCompletion tyLive
                envOut := by
        cases htyped with
        | ite hcondition' htrue' => exact ⟨_, hcondition', _, _, htrue'⟩
        | iteDiverging hcondition' htrue' => exact ⟨_, hcondition', _, _, htrue'⟩
        | iteTrueDiverging hcondition' htrue' => exact ⟨_, hcondition', _, _, htrue'⟩
      cases trueBranch
      case done trueTerm =>
          cases htrue
          rw [extractTermStmts.eq_22]
          exact ⟨envOut, .cons
            (RelaxedTermTyping.iteDiverging hcondition' htrue'
              (RelaxedTermTyping.missing WellFormedTy.unit tyLoanFree_unit)
              .missing) .nil⟩
      case cutoff =>
          rw [extractTermStmts.eq_23]
          exact ⟨envMid, .cons
            (RelaxedTermTyping.iteTrueDiverging hcondition'
              (RelaxedTermTyping.missing WellFormedTy.unit tyLoanFree_unit)
              (RelaxedTermTyping.const ValueTyping.unit)
              .missing) .nil⟩
      case blockStart =>
          rw [extractTermStmts.eq_24]
          exact ⟨envMid, .cons
            (RelaxedTermTyping.iteTrueDiverging hcondition'
              relaxedMissingBlock_typed
              (RelaxedTermTyping.const ValueTyping.unit)
              (.block (by simp) .missing)) .nil⟩
      case blockTerms blockLifetime terms =>
          cases htrue with
          | ctermBlock_blockTerms hterms =>
              cases terms
              case done xs =>
                  cases hterms
                  rw [extractTermStmts.eq_25]
                  exact ⟨envOut, .cons
                    (RelaxedTermTyping.iteDiverging hcondition' htrue'
                      (RelaxedTermTyping.missing WellFormedTy.unit tyLoanFree_unit)
                      .missing) .nil⟩
              all_goals
                cases htrue' with
                | «block» hchild hlist hwf _heq =>
                    obtain ⟨tyBody, envBody, hlist', hdisj⟩ :=
                      extractTerms_relaxedTyped hterms hlist
                    rw [extractTermStmts.eq_26
                      (x_1 := by intro xs hdone; cases hdone)]
                    refine ⟨envMid, .cons
                      (RelaxedTermTyping.iteTrueDiverging hcondition'
                        (RelaxedTermTyping.block hchild hlist' ?_ rfl)
                        (RelaxedTermTyping.const ValueTyping.unit)
                        (.block (extractTerms_diverging nofun) .missing))
                      .nil⟩
                    rcases hdisj with rfl | ⟨rfl, rfl⟩
                    · exact WellFormedTy.unit
                    · exact hwf
      all_goals
        obtain ⟨env', hstmts⟩ := extractTermStmts_relaxedTyped htrue htrue'
        simp only [extractTermStmts] at hstmts ⊢
        exact ⟨env', .cons hcondition' hstmts⟩
  case ctermIte_iteFalseBranch condition trueBranch falseBranch
      falseCompletion hfalse =>
      obtain ⟨envMid, hcondition', tyLive, envOut, htrue', tyDead, envDead,
          hfalse'⟩ :
          ∃ envMid,
            RelaxedTermTyping env typing currentLifetime condition .bool envMid ∧
            ∃ tyLive envOut,
              RelaxedTermTyping envMid typing currentLifetime trueBranch tyLive
                envOut ∧
              ∃ tyDead envDead,
                RelaxedTermTyping envMid typing currentLifetime falseCompletion
                  tyDead envDead := by
        cases htyped with
        | ite hcondition' htrue' hfalse' =>
            exact ⟨_, hcondition', _, _, htrue', _, _, hfalse'⟩
        | iteDiverging hcondition' htrue' hfalse' =>
            exact ⟨_, hcondition', _, _, htrue', _, _, hfalse'⟩
        | iteTrueDiverging hcondition' htrue' hfalse' =>
            exact ⟨_, hcondition', _, _, htrue', _, _, hfalse'⟩
      simp only [extractTermStmts]
      cases falseBranch
      case done falseTerm =>
          cases hfalse
          simp [branchRebuildable, extractTerm]
          exact ⟨env2, .cons htyped .nil⟩
      case cutoff =>
          simp [branchRebuildable, extractTerm]
          exact ⟨envOut, .cons
            (RelaxedTermTyping.iteDiverging hcondition' htrue'
              (RelaxedTermTyping.missing WellFormedTy.unit tyLoanFree_unit)
              .missing) .nil⟩
      case blockStart =>
          simp [branchRebuildable, extractTerm]
          exact ⟨envOut, .cons
            (RelaxedTermTyping.iteDiverging hcondition' htrue' relaxedMissingBlock_typed
              (.block (by simp) .missing)) .nil⟩
      case blockTerms blockLifetime terms =>
          cases hfalse with
          | ctermBlock_blockTerms hterms =>
              cases terms
              case done xs =>
                  cases hterms
                  simp [branchRebuildable, extractTerm, extractTerms]
                  exact ⟨env2, .cons htyped .nil⟩
              all_goals
                cases hfalse' with
                | «block» hchild hlist hwf _heq =>
                    obtain ⟨tyBody, envBody, hlist', hdisj⟩ :=
                      extractTerms_relaxedTyped hterms hlist
                    simp [branchRebuildable, extractTerm]
                    refine ⟨envOut, .cons
                      (RelaxedTermTyping.iteDiverging hcondition' htrue'
                        (RelaxedTermTyping.block hchild hlist' ?_ rfl)
                        (.block (extractTerms_diverging nofun) .missing))
                      .nil⟩
                    rcases hdisj with rfl | ⟨rfl, rfl⟩
                    · exact WellFormedTy.unit
                    · exact hwf
      all_goals
        obtain ⟨env', hstmts⟩ := extractTermStmts_relaxedTyped hfalse hfalse'
        simp only [extractTermStmts, branchRebuildable] at hstmts ⊢
        exact ⟨env', .cons hcondition' hstmts⟩
  case ctermWhile_whileCondition hcondition =>
      simp only [extractTermStmts]
      cases htyped with
      | whileLoopDiverging hchild hcondition' hbody hdiverges =>
          exact extractTermStmts_relaxedTyped hcondition hcondition'
      | whileLoop hchild hjoin hss1 hss2 hcbwf hcoh hlin hcondInv
          hbodyInv hwellTy hdropEq hcondEntry hbodyEntry =>
          exact extractTermStmts_relaxedTyped hcondition hcondEntry
  case ctermWhile_whileBody bodyLifetime condition body bodyCompletion
      hbody =>
      obtain ⟨envMid, hchild', hcondition', tyBody, envBody, hbody'⟩ :
          ∃ envMid,
            LifetimeChild currentLifetime bodyLifetime ∧
            RelaxedTermTyping env typing currentLifetime condition .bool envMid ∧
            ∃ tyBody envBody,
              RelaxedTermTyping envMid typing bodyLifetime bodyCompletion tyBody
                envBody := by
        cases htyped with
        | whileLoopDiverging hchild hcondition' hbody' _ =>
            exact ⟨_, hchild, hcondition', _, _, hbody'⟩
        | whileLoop hchild _ _ _ _ _ _ _ _ _ _ hcondEntry hbodyEntry =>
            exact ⟨_, hchild, hcondEntry, _, _, hbodyEntry⟩
      simp only [extractTermStmts]
      cases body
      case done bodyTerm =>
          cases hbody
          simp [branchRebuildable, extractTerm]
          exact ⟨env2, .cons htyped .nil⟩
      case cutoff =>
          simp [branchRebuildable, extractTerm]
          exact ⟨envMid, .cons
            (RelaxedTermTyping.whileLoopDiverging hchild' hcondition'
              (RelaxedTermTyping.missing WellFormedTy.unit tyLoanFree_unit)
              .missing) .nil⟩
      case blockStart =>
          simp [branchRebuildable, extractTerm]
          exact ⟨envMid, .cons
            (RelaxedTermTyping.whileLoopDiverging hchild' hcondition'
              relaxedMissingBlock_typed (.block (by simp) .missing)) .nil⟩
      case blockTerms blockLifetime terms =>
          cases hbody with
          | ctermBlock_blockTerms hterms =>
              cases terms
              case done xs =>
                  cases hterms
                  simp [branchRebuildable, extractTerm, extractTerms]
                  exact ⟨env2, .cons htyped .nil⟩
              all_goals
                cases hbody' with
                | «block» hchild2 hlist hwf _heq =>
                    obtain ⟨tyBlock, envBlock, hlist', hdisj⟩ :=
                      extractTerms_relaxedTyped hterms hlist
                    simp [branchRebuildable, extractTerm]
                    refine ⟨envMid, .cons
                      (RelaxedTermTyping.whileLoopDiverging hchild' hcondition'
                        (RelaxedTermTyping.block hchild2 hlist' ?_ rfl)
                        (.block (extractTerms_diverging nofun) .missing))
                      .nil⟩
                    rcases hdisj with rfl | ⟨rfl, rfl⟩
                    · exact WellFormedTy.unit
                    · exact hwf
      all_goals
        simp only [branchRebuildable]
        exact ⟨envMid, .cons
          (RelaxedTermTyping.whileLoopDiverging hchild' hcondition'
            (RelaxedTermTyping.missing WellFormedTy.unit tyLoanFree_unit)
            .missing) .nil⟩
  all_goals
    first
    | exact extractTermStmts_relaxedTyped (by assumption) htyped
    | simp only [extractTermStmts]
      exact ⟨env, .nil⟩
termination_by (sizeOf p, 0)
decreasing_by
  all_goals decreasing_tactic

/-- Block-body transport for the relaxed typing relation. -/
theorem extractTerms_relaxedTyped {currentLifetime : Lifetime} {ps : PartialTerms}
    {completions : List Term} {env env2 : Env} {typing : StoreTyping} {ty : Ty}
    (hcomp : CompletesTerms ps completions)
    (hlist : RelaxedTermListTyping env typing currentLifetime completions ty env2) :
    ∃ ty' env', RelaxedTermListTyping env typing currentLifetime
        (extractTerms currentLifetime ps) ty' env' ∧
      (ty' = .unit ∨ (ty' = ty ∧ env' = env2)) := by
  cases hcomp
  case done =>
      simp only [extractTerms]
      exact ⟨ty, env2, hlist, Or.inr ⟨rfl, rfl⟩⟩
  case cutoff =>
      simp only [extractTerms]
      exact ⟨.unit, env, .singleton
        (.missing WellFormedTy.unit tyLoanFree_unit), Or.inl rfl⟩
  case elemsDone =>
      obtain ⟨mid, hpre, _⟩ :=
        relaxedStmtsTyping_append_inv (relaxedTermListTyping_toStmts hlist)
      simp only [extractTerms]
      exact ⟨.unit, mid, relaxedStmtsTyping_missing_closed hpre, Or.inl rfl⟩
  case elemsTail hfrontier =>
      obtain ⟨mid, hpre, hrest⟩ :=
        relaxedStmtsTyping_append_inv (relaxedTermListTyping_toStmts hlist)
      cases hrest with
      | cons hfrontier' hsuffix =>
          obtain ⟨env', hstmts⟩ := extractTermStmts_relaxedTyped hfrontier hfrontier'
          simp only [extractTerms]
          refine ⟨.unit, env', ?_, Or.inl rfl⟩
          have happend :=
            relaxedStmtsTyping_missing_closed (relaxedStmtsTyping_append hpre hstmts)
          simpa [List.append_assoc] using happend
termination_by (sizeOf ps, 0)
decreasing_by
  all_goals decreasing_tactic

end

theorem extractProgram_relaxedWellTyped_of_completion
    {p : PartialProgram} {full : Program}
    (hCompletion : CompletesProgram p full)
    (hFull : ProgramRelaxedWellTyped full) :
    ProgramRelaxedWellTyped (extractProgram p) := by
  obtain ⟨ty, env, htyped⟩ := hFull
  obtain ⟨ty', env', htyped'⟩ := extractTerm_relaxedTyped hCompletion htyped
  exact ⟨ty', env', htyped'⟩

end RelaxedTypedExtraction

theorem extractor_relaxedWellTyped_conservative :
    Conservative ProgramRelaxedWellTyped CompletesProgram extractProgram := by
  intro p hInvalid full hCompletion hFull
  exact hInvalid (extractProgram_relaxedWellTyped_of_completion hCompletion hFull)

theorem extractor_relaxedWellTyped_prefixChecker_complete :
    PrefixCheckerComplete ProgramRelaxedWellTyped CompletesProgram
      (ExtractorPrefixChecker programRelaxedWellTyped extractProgram) := by
  exact conservative_extractors_give_complete_prefix_checkers
    extractor_relaxedWellTyped_conservative
    programRelaxedWellTyped_complete

end ConservativeExtractor
