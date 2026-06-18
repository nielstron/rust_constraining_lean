import LwRust.Paper.BorrowChecker.Executable

/-!
Completeness-facing fuel bounds for the executable borrow/type checker.
-/

namespace LwRust
namespace Paper

open Core

section FuelBoundNoExhaustion

private theorem except_error_ne_fuelExhausted {α : Type} {message : String}
    (hmessage : message ≠ "borrow checker fuel exhausted") :
    (Except.error message : Except String α) ≠
      .error "borrow checker fuel exhausted" := by
  simp [hmessage]

private theorem check_error_ne_fuelExhausted
    {result : Except String CheckResult} {message : String}
    (hcheck : result = .error message)
    (hresult : result ≠ .error "borrow checker fuel exhausted") :
    message ≠ "borrow checker fuel exhausted" := by
  intro hmessage
  subst hmessage
  exact hresult hcheck

attribute [local simp] Bind.bind Pure.pure Except.bind Except.map Except.pure
  Functor.mapConst discard ensure fromOption

mutual
  theorem checkTerm?_ne_fuelExhausted_of_bound (term : Term) :
      ∀ {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
        {lifetime : Lifetime},
        termContainsWhile? term = false →
          termCheckerFuelBound term ≤ fuel →
            checkTerm? fuel env typing lifetime term ≠
              .error "borrow checker fuel exhausted" := by
    intro fuel env typing lifetime hwhile hbound
    cases fuel with
    | zero =>
        have hpos := termCheckerFuelBound_pos term
        omega
    | succ fuel =>
        cases term with
        | block blockLifetime terms =>
            simp [termContainsWhile?, termCheckerFuelBound] at hwhile hbound
            have hterms :
                checkTermList? fuel env typing blockLifetime terms ≠
                  .error "borrow checker fuel exhausted" :=
              checkTermList?_ne_fuelExhausted_of_bound terms hwhile (by omega)
            cases hchild : isLifetimeChild lifetime blockLifetime
            · simp [checkTerm?, ensure, hchild]
            · cases hcheck : checkTermList? fuel env typing blockLifetime terms with
              | error message =>
                  have hmessage :=
                    check_error_ne_fuelExhausted hcheck hterms
                  simp [checkTerm?, ensure, hchild, hcheck, hmessage]
              | ok result =>
                  cases hwell :
                      wellFormedTy fuel result.env result.ty lifetime
                  · simp [checkTerm?, ensure, hchild, hcheck, hwell]
                  · simp [checkTerm?, ensure, hchild, hcheck, hwell]
        | letMut name initialiser =>
            simp [termContainsWhile?, termCheckerFuelBound] at hwhile hbound
            have hinitialiser :
                checkTerm? fuel env typing lifetime initialiser ≠
                  .error "borrow checker fuel exhausted" :=
              checkTerm?_ne_fuelExhausted_of_bound initialiser hwhile (by omega)
            cases hfreshIn : env.fresh name
            · simp [checkTerm?, ensure, hfreshIn]
            · cases hcheck : checkTerm? fuel env typing lifetime initialiser with
              | error message =>
                  have hmessage :=
                    check_error_ne_fuelExhausted hcheck hinitialiser
                  simp [checkTerm?, ensure, hfreshIn, hcheck, hmessage]
              | ok result =>
                  cases hfreshOut : result.env.fresh name
                  · simp [checkTerm?, ensure, hfreshIn, hcheck, hfreshOut]
                  · let env' :=
                      result.env.update name
                        { ty := .ty result.ty, lifetime := lifetime }
                    cases hkit : wellFormedKit fuel env'
                    · simp [checkTerm?, ensure, hfreshIn, hcheck, hfreshOut,
                        env', hkit]
                    · simp [checkTerm?, ensure, hfreshIn, hcheck, hfreshOut,
                        env', hkit]
        | assign lhs rhs =>
            simp [termContainsWhile?, termCheckerFuelBound] at hwhile hbound
            have hrhs :
                checkTerm? fuel env typing lifetime rhs ≠
                  .error "borrow checker fuel exhausted" :=
              checkTerm?_ne_fuelExhausted_of_bound rhs hwhile (by omega)
            cases hleft : lvalType? fuel env lhs with
            | none =>
                simp [checkTerm?, fromOption, hleft]
            | some before =>
                rcases before with ⟨oldTy, targetLifetime⟩
                cases hcheck : checkTerm? fuel env typing lifetime rhs with
                | error message =>
                    have hmessage :=
                      check_error_ne_fuelExhausted hcheck hrhs
                    simp [checkTerm?, fromOption, hleft, hcheck, hmessage]
                | ok rhsResult =>
                    cases hsafe : assignmentBorrowSafety rhsResult.env lhs
                    · simp [checkTerm?, fromOption, ensure, hleft, hcheck,
                        hsafe]
                    · cases hafter :
                          lvalType? fuel rhsResult.env lhs with
                      | none =>
                          simp [checkTerm?, fromOption, ensure, hleft, hcheck,
                            hsafe, hafter]
                      | some after =>
                          rcases after with ⟨oldTyAfter, targetLifetimeAfter⟩
                          cases holdTy :
                              decide (oldTyAfter = oldTy)
                          · simp [checkTerm?, fromOption, ensure, hleft,
                              hcheck, hsafe, hafter, holdTy]
                          · cases hlifetime :
                                decide (targetLifetimeAfter = targetLifetime)
                            · simp [checkTerm?, fromOption, ensure, hleft,
                                hcheck, hsafe, hafter, holdTy, hlifetime]
                            · cases hshape :
                                  shapeCompatiblePartialTy fuel rhsResult.env
                                    oldTy (.ty rhsResult.ty)
                              · simp [checkTerm?, fromOption, ensure, hleft,
                                  hcheck, hsafe, hafter, holdTy, hlifetime,
                                  hshape]
                              · cases hwell :
                                    wellFormedTy fuel rhsResult.env
                                      rhsResult.ty targetLifetime
                                · simp [checkTerm?, fromOption, ensure, hleft,
                                    hcheck, hsafe, hafter, holdTy, hlifetime,
                                    hshape, hwell]
                                · cases hwrite :
                                      envWrite? fuel 0 rhsResult.env lhs
                                        rhsResult.ty with
                                  | none =>
                                      simp [checkTerm?, fromOption, ensure,
                                        hleft, hcheck, hsafe, hafter, holdTy,
                                        hlifetime, hshape, hwell, hwrite]
                                  | some written =>
                                      cases houtside :
                                          envEqOutside rhsResult.env written
                                            (LVal.base lhs) with
                                      | false =>
                                          simp [checkTerm?, fromOption, ensure,
                                            hleft, hcheck, hsafe, hafter,
                                            holdTy, hlifetime, hshape, hwell,
                                            hwrite, houtside]
                                      | true =>
                                          cases hbelow :
                                              rhsBorrowTargetsBelow rhsResult.env
                                                written rhsResult.ty with
                                          | false =>
                                              simp [checkTerm?, fromOption,
                                                ensure, hleft, hcheck, hsafe,
                                                hafter, holdTy, hlifetime,
                                                hshape, hwell, hwrite,
                                                houtside, hbelow]
                                          | true =>
                                              cases hcontained :
                                                    containedBorrowsWellFormed
                                                      fuel written <;>
                                                cases hlinear :
                                                  linearizable written <;>
                                                cases hcoherent :
                                                  coherentNonempty fuel
                                                    written <;>
                                                cases hroot :
                                                  rootCoherent fuel written
                                                    (LVal.base lhs) <;>
                                                cases hnotWrite :
                                                  writeProhibited written lhs <;>
                                                simp [checkTerm?, fromOption,
                                                  ensure, hleft, hcheck, hsafe,
                                                  hafter, holdTy, hlifetime,
                                                  hshape, hwell, hwrite,
                                                  houtside, hbelow, hcontained,
                                                  hlinear, hcoherent, hroot,
                                                  hnotWrite]
        | box operand =>
            simp [termContainsWhile?, termCheckerFuelBound] at hwhile hbound
            have hoperand :
                checkTerm? fuel env typing lifetime operand ≠
                  .error "borrow checker fuel exhausted" :=
              checkTerm?_ne_fuelExhausted_of_bound operand hwhile (by omega)
            cases hcheck : checkTerm? fuel env typing lifetime operand with
            | error message =>
                have hmessage :=
                  check_error_ne_fuelExhausted hcheck hoperand
                simp [checkTerm?, hcheck, hmessage]
            | ok result =>
                simp [checkTerm?, hcheck]
        | borrow mutable lv =>
            cases htype : lvalType? fuel env lv with
            | none =>
                simp [checkTerm?, fromOption, htype]
            | some result =>
                rcases result with ⟨partialTy, valueLifetime⟩
                cases partialTy with
                | ty ty =>
                    cases mutable
                    · cases hread : readProhibited env lv <;>
                        simp [checkTerm?, fromOption, ensure, htype, hread]
                    · cases hmutable : mutableLVal fuel env lv <;>
                        cases hwrite : writeProhibited env lv <;>
                          simp [checkTerm?, fromOption, ensure, htype,
                            hmutable, hwrite]
                | box inner =>
                    simp [checkTerm?, fromOption, htype]
                | undef ty =>
                    simp [checkTerm?, fromOption, htype]
        | move lv =>
            cases htype : lvalType? fuel env lv with
            | none =>
                simp [checkTerm?, fromOption, htype]
            | some result =>
                rcases result with ⟨partialTy, valueLifetime⟩
                cases partialTy with
                | ty ty =>
                    cases hwrite : writeProhibited env lv
                    · cases hmove : envMove? env lv <;>
                        simp [checkTerm?, fromOption, ensure, htype, hwrite,
                          hmove]
                    · simp [checkTerm?, fromOption, ensure, htype, hwrite]
                | box inner =>
                    simp [checkTerm?, fromOption, htype]
                | undef ty =>
                    simp [checkTerm?, fromOption, htype]
        | copy lv =>
            cases htype : lvalType? fuel env lv with
            | none =>
                simp [checkTerm?, fromOption, htype]
            | some result =>
                rcases result with ⟨partialTy, valueLifetime⟩
                cases partialTy with
                | ty ty =>
                    cases hcopy : copyTy ty <;>
                      cases hread : readProhibited env lv <;>
                        simp [checkTerm?, fromOption, ensure, htype, hcopy,
                          hread]
                | box inner =>
                    simp [checkTerm?, fromOption, htype]
                | undef ty =>
                    simp [checkTerm?, fromOption, htype]
        | val value =>
            cases hty : valueTy? typing value <;>
              simp [checkTerm?, fromOption, hty]
        | missing =>
            simp [checkTerm?]
        | eq lhs rhs =>
            simp [termContainsWhile?, termCheckerFuelBound] at hwhile hbound
            have hlhs :
                checkTerm? fuel env typing lifetime lhs ≠
                  .error "borrow checker fuel exhausted" :=
              checkTerm?_ne_fuelExhausted_of_bound lhs hwhile.1 (by omega)
            have hrhs :
                ∀ {env' : FiniteEnv},
                  checkTerm? fuel env' typing lifetime rhs ≠
                    .error "borrow checker fuel exhausted" := by
              intro env'
              exact checkTerm?_ne_fuelExhausted_of_bound rhs hwhile.2
                (by omega)
            cases hlhsCheck : checkTerm? fuel env typing lifetime lhs with
            | error message =>
                have hmessage :=
                  check_error_ne_fuelExhausted hlhsCheck hlhs
                simp [checkTerm?, hlhsCheck, hmessage]
            | ok lhsResult =>
                cases hlhsCopy : copyTy lhsResult.ty
                · simp [checkTerm?, hlhsCheck, ensure, hlhsCopy]
                · let ghost := freshGhostName lhsResult.env rhs
                  cases hghostFresh : lhsResult.env.fresh ghost
                  · simp [checkTerm?, hlhsCheck, ensure, hlhsCopy, ghost,
                      hghostFresh]
                  · let ghostEnv :=
                      lhsResult.env.update ghost
                        { ty := .ty lhsResult.ty, lifetime := lifetime }
                    cases hkit : wellFormedKit fuel ghostEnv
                    · simp [checkTerm?, hlhsCheck, ensure, hlhsCopy, ghost,
                        hghostFresh, ghostEnv, hkit]
                    · cases hghost :
                          checkTerm? fuel ghostEnv typing lifetime rhs with
                      | error message =>
                          have hmessage :=
                            check_error_ne_fuelExhausted hghost
                              (hrhs (env' := ghostEnv))
                          simp [checkTerm?, hlhsCheck, ensure, hlhsCopy,
                            ghost, hghostFresh, ghostEnv, hkit, hghost,
                            hmessage]
                      | ok ghostResult =>
                          cases hrhsCheck :
                              checkTerm? fuel lhsResult.env typing lifetime
                                rhs with
                          | error message =>
                              have hmessage :=
                                check_error_ne_fuelExhausted hrhsCheck
                                  (hrhs (env' := lhsResult.env))
                              simp [checkTerm?, hlhsCheck, ensure, hlhsCopy,
                                ghost, hghostFresh, ghostEnv, hkit, hghost,
                                hrhsCheck, hmessage]
                          | ok rhsResult =>
                              cases hrhsCopy : copyTy rhsResult.ty
                              · simp [checkTerm?, hlhsCheck, ensure, hlhsCopy,
                                  ghost, hghostFresh, ghostEnv, hkit, hghost,
                                  hrhsCheck, hrhsCopy]
                              · cases hshape :
                                    shapeCompatiblePartialTy fuel rhsResult.env
                                      (.ty lhsResult.ty) (.ty rhsResult.ty)
                                · simp [checkTerm?, hlhsCheck, ensure,
                                    hlhsCopy, ghost, hghostFresh, ghostEnv,
                                    hkit, hghost, hrhsCheck, hrhsCopy, hshape]
                                · simp [checkTerm?, hlhsCheck, ensure,
                                    hlhsCopy, ghost, hghostFresh, ghostEnv,
                                    hkit, hghost, hrhsCheck, hrhsCopy, hshape]
        | ite condition trueBranch falseBranch =>
            simp [termContainsWhile?, termCheckerFuelBound] at hwhile hbound
            have hcondition :
                checkTerm? fuel env typing lifetime condition ≠
                  .error "borrow checker fuel exhausted" :=
              checkTerm?_ne_fuelExhausted_of_bound condition hwhile.1.1
                (by omega)
            have htrue :
                ∀ {env' : FiniteEnv},
                  checkTerm? fuel env' typing lifetime trueBranch ≠
                    .error "borrow checker fuel exhausted" := by
              intro env'
              exact checkTerm?_ne_fuelExhausted_of_bound trueBranch
                hwhile.1.2 (by omega)
            have hfalse :
                ∀ {env' : FiniteEnv},
                  checkTerm? fuel env' typing lifetime falseBranch ≠
                    .error "borrow checker fuel exhausted" := by
              intro env'
              exact checkTerm?_ne_fuelExhausted_of_bound falseBranch
                hwhile.2 (by omega)
            cases hconditionCheck :
                checkTerm? fuel env typing lifetime condition with
            | error message =>
                have hmessage :=
                  check_error_ne_fuelExhausted hconditionCheck hcondition
                simp [checkTerm?, hconditionCheck, hmessage]
            | ok conditionResult =>
                cases hconditionTy :
                    decide (conditionResult.ty = .bool)
                · simp [checkTerm?, ensure, hconditionCheck, hconditionTy]
                · cases htrueCheck :
                      checkTerm? fuel conditionResult.env typing lifetime
                        trueBranch with
                  | error message =>
                      have hmessage :=
                        check_error_ne_fuelExhausted htrueCheck
                          (htrue (env' := conditionResult.env))
                      simp [checkTerm?, ensure, hconditionCheck,
                        hconditionTy, htrueCheck, hmessage]
                  | ok thenResult =>
                      cases hfalseCheck :
                          checkTerm? fuel conditionResult.env typing lifetime
                            falseBranch with
                      | error message =>
                          have hmessage :=
                            check_error_ne_fuelExhausted hfalseCheck
                              (hfalse (env' := conditionResult.env))
                          simp [checkTerm?, ensure, hconditionCheck,
                            hconditionTy, htrueCheck, hfalseCheck, hmessage]
                      | ok falseResult =>
                          cases hjoinTy :
                              partialTyJoin? (.ty thenResult.ty)
                                (.ty falseResult.ty) with
                          | none =>
                              cases hdiv : termDiverges falseBranch <;>
                                simp [checkTerm?, ensure, hconditionCheck,
                                  hconditionTy, htrueCheck, hfalseCheck,
                                  hjoinTy, hdiv]
                          | some joinPartial =>
                              cases joinPartial with
                              | ty joinTy =>
                                    cases hjoinEnv :
                                        envJoin? thenResult.env falseResult.env with
                                  | none =>
                                      cases hdiv : termDiverges falseBranch <;>
                                        simp [checkTerm?, ensure,
                                          hconditionCheck, hconditionTy,
                                          htrueCheck, hfalseCheck, hjoinTy,
                                          hjoinEnv, hdiv]
                                  | some joinEnv =>
                                      cases hthenShape :
                                          envJoinSameShape thenResult.env
                                            joinEnv
                                      <;> cases hfalseShape :
                                          envJoinSameShape falseResult.env
                                            joinEnv
                                      <;> cases hwell :
                                          wellFormedTy fuel joinEnv joinTy
                                            lifetime
                                      <;> cases hkit : wellFormedKit fuel joinEnv
                                      <;> cases hsafe :
                                          tyBorrowSafeAgainstEnv joinEnv joinTy
                                      <;> simp [checkTerm?, ensure,
                                        hconditionCheck, hconditionTy,
                                        htrueCheck, hfalseCheck, hjoinTy,
                                        hjoinEnv, hthenShape, hfalseShape,
                                        hwell, hkit, hsafe]
                              | box inner =>
                                  cases hdiv : termDiverges falseBranch <;>
                                    simp [checkTerm?, ensure, hconditionCheck,
                                      hconditionTy, htrueCheck, hfalseCheck,
                                      hjoinTy, hdiv]
                              | undef ty =>
                                  cases hdiv : termDiverges falseBranch <;>
                                    simp [checkTerm?, ensure, hconditionCheck,
                                      hconditionTy, htrueCheck, hfalseCheck,
                                      hjoinTy, hdiv]
        | whileLoop bodyLifetime condition body =>
            simp [termContainsWhile?] at hwhile
        | whileCond bodyLifetime conditionInFlight condition body =>
            simp [termContainsWhile?] at hwhile
        | whileBody bodyLifetime bodyInFlight condition body =>
            simp [termContainsWhile?] at hwhile

  theorem checkTermList?_ne_fuelExhausted_of_bound (terms : List Term) :
      ∀ {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
        {lifetime : Lifetime},
        termListContainsWhile? terms = false →
          termListCheckerFuelBound terms ≤ fuel →
            checkTermList? fuel env typing lifetime terms ≠
              .error "borrow checker fuel exhausted" := by
    intro fuel env typing lifetime hwhile hbound
    cases terms with
    | nil =>
        simp [checkTermList?]
    | cons term rest =>
        cases rest with
        | nil =>
            simp [termListContainsWhile?, termListCheckerFuelBound] at hwhile hbound
            have hterm :
                checkTerm? fuel env typing lifetime term ≠
                  .error "borrow checker fuel exhausted" :=
              checkTerm?_ne_fuelExhausted_of_bound term (fuel := fuel)
                (env := env) (typing := typing) (lifetime := lifetime)
                hwhile (by omega)
            simpa [checkTermList?] using hterm
        | cons restHead restTail =>
            simp [termListContainsWhile?, termListCheckerFuelBound] at hwhile hbound
            have hhead :
                checkTerm? fuel env typing lifetime term ≠
                  .error "borrow checker fuel exhausted" :=
              checkTerm?_ne_fuelExhausted_of_bound term (fuel := fuel)
                (env := env) (typing := typing) (lifetime := lifetime)
                hwhile.1 (by omega)
            have hrestWhile :
                termListContainsWhile? (restHead :: restTail) = false := by
              simpa [termListContainsWhile?] using hwhile.2
            have hrest :
                ∀ {env' : FiniteEnv},
                  checkTermList? fuel env' typing lifetime
                      (restHead :: restTail) ≠
                    .error "borrow checker fuel exhausted" := by
              intro env'
              exact checkTermList?_ne_fuelExhausted_of_bound
                (restHead :: restTail) (fuel := fuel) (env := env')
                (typing := typing) (lifetime := lifetime) hrestWhile
                (by
                  simp [termListCheckerFuelBound]
                  omega)
            cases hcheck : checkTerm? fuel env typing lifetime term with
            | error message =>
                have hmessage :=
                  check_error_ne_fuelExhausted hcheck hhead
                simp [checkTermList?, hcheck, hmessage]
            | ok headResult =>
                cases htail :
                    checkTermList? fuel headResult.env typing lifetime
                      (restHead :: restTail) with
                | error message =>
                    have hmessage :=
                      check_error_ne_fuelExhausted htail
                        (hrest (env' := headResult.env))
                    simp [checkTermList?, hcheck, htail, hmessage]
                | ok result =>
                    simp [checkTermList?, hcheck, htail]
end

theorem checkProgram?_ne_fuelExhausted_of_fuelBound {term : Term} :
    termContainsWhile? term = false →
      checkProgram? (termCheckerFuelBound term) term ≠
        .error "borrow checker fuel exhausted" := by
  intro hwhile
  exact checkTerm?_ne_fuelExhausted_of_bound term hwhile le_rfl

end FuelBoundNoExhaustion
/--
Completeness of the executable checker at a particular fuel.

For the fuel-bound rejection result, this is the property to prove for the
loop-free/no-`missing` fragment at `termCheckerFuelBound term`: every
declarative closed typing derivation is found by the executable checker at
that fuel.
-/
def borrowCheckCompleteAt (fuel : Nat) (term : Term) : Prop :=
  borrowCheck term → borrowCheck? fuel term = true

/--
Unconditional fuel-bound checker completeness is false: `.missing` is
declaratively typable at any loan-free, well-formed type, but the executable
checker intentionally refuses to infer a type for it.
-/
theorem borrowCheckCompleteAt_fuelBound_not_all_terms :
    ¬ ∀ term, borrowCheckCompleteAt (termCheckerFuelBound term) term := by
  intro hcomplete
  have hcheck : borrowCheck Term.missing := by
    exact ⟨.unit, Env.empty,
      TermTyping.missing WellFormedTy.unit (by
        intro mutable targets hcontains
        cases hcontains)⟩
  have hnotAccepted :
      borrowCheck? (termCheckerFuelBound Term.missing) Term.missing = false := by
    native_decide
  have haccepted := hcomplete Term.missing hcheck
  rw [hnotAccepted] at haccepted
  cases haccepted

theorem borrowReject_of_borrowCheckFailed?_of_completeAt
    {fuel : Nat} {term : Term} :
    borrowCheckCompleteAt fuel term →
      borrowCheckFailed? fuel term = true →
        borrowReject term := by
  intro hcomplete hfailed hcheck
  have haccepted := hcomplete hcheck
  have hnotFailed := borrowCheckFailed?_false_of_borrowCheck? haccepted
  rw [hfailed] at hnotFailed
  cases hnotFailed

theorem borrowReject_of_borrowCheckFailed?_fuelBound
    {term : Term} :
    borrowCheckCompleteAt (termCheckerFuelBound term) term →
      borrowCheckFailed? (termCheckerFuelBound term) term = true →
        borrowReject term :=
  borrowReject_of_borrowCheckFailed?_of_completeAt

end Paper
end LwRust
