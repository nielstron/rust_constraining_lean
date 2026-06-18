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

section BasicReflectionCompleteness

attribute [local simp] Bind.bind Pure.pure Except.bind Except.map Except.pure
  Functor.mapConst discard ensure fromOption

theorem valueTy?_complete {typing : StoreTyping} {value : Value}
    {ty : Ty} :
    ValueTyping typing value ty → valueTy? typing value = some ty := by
  intro h
  cases h with
  | unit => rfl
  | int => rfl
  | bool => rfl
  | ref hlookup => exact hlookup

theorem copyTy_complete {ty : Ty} :
    CopyTy ty → copyTy ty = true := by
  intro h
  cases h <;> rfl

theorem isLifetimeChild_complete {parent child : Lifetime} :
    LifetimeChild parent child → isLifetimeChild parent child = true := by
  intro h
  rcases parent with ⟨parentPath⟩
  rcases child with ⟨childPath⟩
  rcases h with ⟨label, hpath⟩
  change childPath = parentPath ++ [label] at hpath
  subst childPath
  simp [isLifetimeChild]

theorem lvalType?_var_complete {fuel : Nat} {env : FiniteEnv}
    {name : Name} {slot : EnvSlot} :
    0 < fuel →
      env.toEnv.slotAt name = some slot →
        lvalType? fuel env (.var name) = some (slot.ty, slot.lifetime) := by
  intro hfuel hslot
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      change env.lookup name = some slot at hslot
      simp [lvalType?, hslot]

theorem fresh_complete {env : FiniteEnv} {name : Name} :
    env.toEnv.fresh name → env.fresh name = true := by
  intro hfresh
  change env.lookup name = none at hfresh
  simp [FiniteEnv.fresh, hfresh]

theorem copyTy_complete_of_eqv {left right : Ty} :
    Ty.eqv left right →
      CopyTy left →
        copyTy right = true := by
  intro heqv hcopy
  cases hcopy with
  | unit =>
      cases right <;> simp [Ty.eqv, copyTy] at heqv ⊢
  | int =>
      cases right <;> simp [Ty.eqv, copyTy] at heqv ⊢
  | bool =>
      cases right <;> simp [Ty.eqv, copyTy] at heqv ⊢
  | immBorrow =>
      cases right <;> simp [Ty.eqv, copyTy] at heqv ⊢
      rename_i mutable targets
      cases mutable <;> simp at heqv ⊢

theorem ty_eqv_bool_right_eq {ty : Ty} :
    Ty.eqv ty .bool → ty = .bool := by
  intro heqv
  cases ty <;> simp [Ty.eqv] at heqv ⊢

mutual
  theorem ty_eqv_sameShape {left right : Ty} :
      Ty.eqv left right → Ty.sameShape left right := by
    intro h
    cases left <;> cases right <;> simp [Ty.eqv, Ty.sameShape] at h ⊢
    · exact h.1
    · exact ty_eqv_sameShape h

  theorem partialTy_eqv_sameShape {left right : PartialTy} :
      PartialTy.eqv left right → PartialTy.sameShape left right := by
    intro h
    cases left <;> cases right <;> simp [PartialTy.eqv,
      PartialTy.sameShape] at h ⊢
    · exact ty_eqv_sameShape h
    · exact partialTy_eqv_sameShape h
    · exact ty_eqv_sameShape h
end

mutual
  theorem Ty.eqv_trans {left middle right : Ty} :
      Ty.eqv left middle → Ty.eqv middle right → Ty.eqv left right := by
    intro hleftMiddle hmiddleRight
    cases left <;> cases middle <;> cases right <;>
      simp [Ty.eqv] at hleftMiddle hmiddleRight ⊢
    · rcases hleftMiddle with ⟨hleftMiddleMutable,
        hleftMiddleTargets, hmiddleLeftTargets⟩
      rcases hmiddleRight with ⟨hmiddleRightMutable,
        hmiddleRightTargets, hrightMiddleTargets⟩
      subst hleftMiddleMutable
      subst hmiddleRightMutable
      exact ⟨rfl,
        fun target htarget => hmiddleRightTargets (hleftMiddleTargets htarget),
        fun target htarget => hmiddleLeftTargets (hrightMiddleTargets htarget)⟩
    · exact Ty.eqv_trans hleftMiddle hmiddleRight

  theorem PartialTy.eqv_trans {left middle right : PartialTy} :
      PartialTy.eqv left middle →
        PartialTy.eqv middle right →
          PartialTy.eqv left right := by
    intro hleftMiddle hmiddleRight
    cases left <;> cases middle <;> cases right <;>
      simp [PartialTy.eqv] at hleftMiddle hmiddleRight ⊢
    · exact Ty.eqv_trans hleftMiddle hmiddleRight
    · exact PartialTy.eqv_trans hleftMiddle hmiddleRight
    · exact Ty.eqv_trans hleftMiddle hmiddleRight
end

theorem partialTy_eqv_ty_left_inv {left : Ty} {right : PartialTy} :
    PartialTy.eqv (.ty left) right →
      ∃ rightTy, right = .ty rightTy ∧ Ty.eqv left rightTy := by
  intro h
  cases right <;> simp [PartialTy.eqv] at h
  · exact ⟨_, rfl, h⟩

theorem partialTy_eqv_box_left_inv {left : PartialTy} {right : PartialTy} :
    PartialTy.eqv (.box left) right →
      ∃ rightInner, right = .box rightInner ∧ PartialTy.eqv left rightInner := by
  intro h
  cases right <;> simp [PartialTy.eqv] at h
  · exact ⟨_, rfl, h⟩

theorem ty_eqv_borrow_left_inv {mutable : Bool} {targets : List LVal}
    {right : Ty} :
    Ty.eqv (.borrow mutable targets) right →
      ∃ checkedTargets,
        right = .borrow mutable checkedTargets ∧
          targets ⊆ checkedTargets ∧ checkedTargets ⊆ targets := by
  intro h
  cases right <;> simp [Ty.eqv] at h
  rename_i checkedMutable checkedTargets
  rcases h with ⟨hmutable, htargetsChecked, hcheckedTargets⟩
  subst hmutable
  exact ⟨checkedTargets, rfl, htargetsChecked, hcheckedTargets⟩

mutual
  theorem tyJoin?_some_of_sameShape_complete {left right : Ty} :
      Ty.sameShape left right → ∃ join, tyJoin? left right = some join := by
    intro hshape
    cases hjoin : tyJoin? left right with
    | some join =>
        exact ⟨join, rfl⟩
    | none =>
        exfalso
        cases left <;> cases right <;>
          simp [Ty.sameShape, tyJoin?] at hshape hjoin
        all_goals try contradiction
        rcases tyJoin?_some_of_sameShape_complete hshape with ⟨join, hsome⟩
        exact hjoin join hsome

  theorem partialTyJoin?_some_of_sameShape_complete {left right : PartialTy} :
      PartialTy.sameShape left right →
        ∃ join, partialTyJoin? left right = some join := by
    intro hshape
    cases hjoin : partialTyJoin? left right with
    | some join =>
        exact ⟨join, rfl⟩
    | none =>
        exfalso
        cases left <;> cases right <;>
          simp [PartialTy.sameShape, partialTyJoin?] at hshape hjoin
        · rcases tyJoin?_some_of_sameShape_complete hshape with
            ⟨join, hsome⟩
          exact hjoin join hsome
        · rcases partialTyJoin?_some_of_sameShape_complete hshape with
            ⟨join, hsome⟩
          exact hjoin join hsome
        · rcases tyJoin?_some_of_sameShape_complete hshape with
            ⟨join, hsome⟩
          exact hjoin join hsome
end

theorem partialTyStrengthens_undef_to_undef_inv_for_completeness
    {left right : Ty} :
    PartialTyStrengthens (.undef left) (.undef right) →
      PartialTyStrengthens (.ty left) (.ty right) := by
  intro h
  cases h with
  | reflex =>
      exact PartialTyStrengthens.reflex
  | undefLeft hinner =>
      exact hinner

theorem partialTyJoin_ty_undef_for_completeness {left right join : Ty} :
    PartialTyJoin (.ty left) (.ty right) (.ty join) →
      PartialTyJoin (.ty left) (.undef right) (.undef join) := by
  intro hjoin
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.intoUndef
        (PartialTyUnion.left_strengthens hjoin)
    · subst hcandidate
      exact PartialTyStrengthens.undefLeft
        (PartialTyUnion.right_strengthens hjoin)
  · intro upper hupper
    have hleftUpper : PartialTyStrengthens (.ty left) upper :=
      hupper (by simp)
    have hrightUpper : PartialTyStrengthens (.undef right) upper :=
      hupper (by simp)
    cases upper with
    | ty _ =>
        exact False.elim (PartialTyStrengthens.not_undef_to_ty hrightUpper)
    | box _ =>
        exact False.elim (PartialTyStrengthens.not_undef_to_box hrightUpper)
    | undef _ =>
        exact PartialTyStrengthens.undefLeft
          (hjoin.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact PartialTyStrengthens.ty_to_undef_inv hleftUpper
            · subst hcandidate
              exact
                partialTyStrengthens_undef_to_undef_inv_for_completeness
                  hrightUpper))

theorem partialTyJoin_undef_ty_for_completeness {left right join : Ty} :
    PartialTyJoin (.ty left) (.ty right) (.ty join) →
      PartialTyJoin (.undef left) (.ty right) (.undef join) := by
  intro hjoin
  exact PartialTyUnion.symm
    (partialTyJoin_ty_undef_for_completeness
      (PartialTyUnion.symm hjoin))

theorem partialTyJoin_undef_undef_for_completeness {left right join : Ty} :
    PartialTyJoin (.ty left) (.ty right) (.ty join) →
      PartialTyJoin (.undef left) (.undef right) (.undef join) := by
  intro hjoin
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.undefLeft
        (PartialTyUnion.left_strengthens hjoin)
    · subst hcandidate
      exact PartialTyStrengthens.undefLeft
        (PartialTyUnion.right_strengthens hjoin)
  · intro upper hupper
    have hleftUpper : PartialTyStrengthens (.undef left) upper :=
      hupper (by simp)
    have hrightUpper : PartialTyStrengthens (.undef right) upper :=
      hupper (by simp)
    cases upper with
    | ty _ =>
        exact False.elim (PartialTyStrengthens.not_undef_to_ty hleftUpper)
    | box _ =>
        exact False.elim (PartialTyStrengthens.not_undef_to_box hleftUpper)
    | undef _ =>
        exact PartialTyStrengthens.undefLeft
          (hjoin.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact
                partialTyStrengthens_undef_to_undef_inv_for_completeness
                  hleftUpper
            · subst hcandidate
              exact
                partialTyStrengthens_undef_to_undef_inv_for_completeness
                  hrightUpper))

mutual
  theorem tyJoin?_sound_for_completeness :
      ∀ {left right join : Ty},
        tyJoin? left right = some join →
          PartialTyJoin (.ty left) (.ty right) (.ty join) := by
    intro left
    cases left with
    | unit =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        subst h
        exact PartialTyJoin.self (.ty .unit)
    | int =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        subst h
        exact PartialTyJoin.self (.ty .int)
    | bool =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        subst h
        exact PartialTyJoin.self (.ty .bool)
    | borrow mutable leftTargets =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        next mutable' rightTargets =>
          by_cases hmutable : mutable = mutable'
          · subst hmutable
            simp at h
            cases h
            constructor
            · intro candidate hcandidate
              simp at hcandidate
              rcases hcandidate with hcandidate | hcandidate
              · subst hcandidate
                exact PartialTyStrengthens.borrow (by
                  intro target htarget
                  exact mem_unionLVals.mpr (Or.inl htarget))
              · subst hcandidate
                exact PartialTyStrengthens.borrow (by
                  intro target htarget
                  exact mem_unionLVals.mpr (Or.inr htarget))
            · intro upper hupper
              have hleftUpper :
                  PartialTyStrengthens
                    (.ty (.borrow mutable leftTargets)) upper :=
                hupper (by simp)
              have hrightUpper :
                  PartialTyStrengthens
                    (.ty (.borrow mutable rightTargets)) upper :=
                hupper (by simp)
              cases hleftUpper with
              | reflex =>
                  have hsubRight :=
                    PartialTyStrengthens.borrow_subset hrightUpper
                  exact PartialTyStrengthens.borrow (by
                    intro target htarget
                    rcases mem_unionLVals.mp htarget with hmem | hmem
                    · exact hmem
                    · exact hsubRight hmem)
              | borrow hsubLeft =>
                  have hsubRight :=
                    PartialTyStrengthens.borrow_subset hrightUpper
                  exact PartialTyStrengthens.borrow (by
                    intro target htarget
                    rcases mem_unionLVals.mp htarget with hmem | hmem
                    · exact hsubLeft hmem
                    · exact hsubRight hmem)
              | intoUndef hinner =>
                  rcases PartialTyStrengthens.from_borrow_inv hinner with
                    ⟨targetTargets, rfl, hsubLeft⟩
                  have hsubRight : rightTargets ⊆ targetTargets := by
                    cases hrightUpper with
                    | intoUndef hinner' =>
                        exact PartialTyStrengthens.borrow_subset hinner'
                  exact PartialTyStrengthens.intoUndef
                    (PartialTyStrengthens.borrow (by
                      intro target htarget
                      rcases mem_unionLVals.mp htarget with hmem | hmem
                      · exact hsubLeft hmem
                      · exact hsubRight hmem))
          · simp [hmutable] at h
    | box leftInner =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        next rightInner =>
          cases hinner : tyJoin? leftInner rightInner with
          | none =>
              simp [hinner] at h
          | some inner =>
              simp [hinner] at h
              cases h
              exact PartialTyUnion.tyBox
                (tyJoin?_sound_for_completeness hinner)
end

theorem partialTyJoin?_sound_for_completeness :
    ∀ {left right join : PartialTy},
      partialTyJoin? left right = some join →
        PartialTyJoin left right join
  | .ty left, .ty right, join, h => by
      cases hty : tyJoin? left right with
      | none =>
          simp [partialTyJoin?, hty] at h
      | some ty =>
          simp [partialTyJoin?, hty] at h
          cases h
          exact tyJoin?_sound_for_completeness hty
  | .ty left, .box right, join, h => by
      simp [partialTyJoin?] at h
  | .ty left, .undef right, join, h => by
      cases hty : tyJoin? left right with
      | none =>
          simp [partialTyJoin?, hty] at h
      | some ty =>
          simp [partialTyJoin?, hty] at h
          cases h
          exact partialTyJoin_ty_undef_for_completeness
            (tyJoin?_sound_for_completeness hty)
  | .box left, .ty right, join, h => by
      simp [partialTyJoin?] at h
  | .box left, .box right, join, h => by
      cases hinner : partialTyJoin? left right with
      | none =>
          simp [partialTyJoin?, hinner] at h
      | some inner =>
          simp [partialTyJoin?, hinner] at h
          cases h
          exact PartialTyUnion.box
            (partialTyJoin?_sound_for_completeness hinner)
  | .box left, .undef right, join, h => by
      simp [partialTyJoin?] at h
  | .undef left, .ty right, join, h => by
      cases hty : tyJoin? left right with
      | none =>
          simp [partialTyJoin?, hty] at h
      | some ty =>
          simp [partialTyJoin?, hty] at h
          cases h
          exact partialTyJoin_undef_ty_for_completeness
            (tyJoin?_sound_for_completeness hty)
  | .undef left, .box right, join, h => by
      simp [partialTyJoin?] at h
  | .undef left, .undef right, join, h => by
      cases hty : tyJoin? left right with
      | none =>
          simp [partialTyJoin?, hty] at h
      | some ty =>
          simp [partialTyJoin?, hty] at h
          cases h
          exact partialTyJoin_undef_undef_for_completeness
            (tyJoin?_sound_for_completeness hty)

theorem tyJoin?_complete_of_eqv_of_partialTyJoin
    {left right join checkedLeft checkedRight : Ty} :
    Ty.eqv left checkedLeft →
      Ty.eqv right checkedRight →
        PartialTyJoin (.ty left) (.ty right) (.ty join) →
          ∃ checkedJoin,
            tyJoin? checkedLeft checkedRight = some checkedJoin ∧
              Ty.eqv join checkedJoin := by
  intro hleftEqv hrightEqv hjoin
  have hleftJoinShape : Ty.sameShape left join :=
    ty_sameShape_of_strengthens
      (show PartialTyStrengthens (.ty left) (.ty join) from
        PartialTyUnion.left_strengthens hjoin)
  have hrightJoinShape : Ty.sameShape right join :=
    ty_sameShape_of_strengthens
      (show PartialTyStrengthens (.ty right) (.ty join) from
        PartialTyUnion.right_strengthens hjoin)
  have hcheckedShape : Ty.sameShape checkedLeft checkedRight :=
    Ty.sameShape_trans
      (Ty.sameShape_symm (ty_eqv_sameShape hleftEqv))
      (Ty.sameShape_trans
        (Ty.sameShape_trans hleftJoinShape
          (Ty.sameShape_symm hrightJoinShape))
        (ty_eqv_sameShape hrightEqv))
  rcases tyJoin?_some_of_sameShape_complete hcheckedShape with
    ⟨checkedJoin, hcheckedJoin⟩
  have hcheckedJoinSound :
      PartialTyUnion (.ty checkedLeft) (.ty checkedRight)
        (.ty checkedJoin) :=
    tyJoin?_sound_for_completeness hcheckedJoin
  have heqv :
      PartialTy.eqv (.ty join) (.ty checkedJoin) :=
    PartialTyUnion.eqv_of_eqv hjoin
      (show PartialTy.eqv (.ty left) (.ty checkedLeft) from hleftEqv)
      (show PartialTy.eqv (.ty right) (.ty checkedRight) from hrightEqv)
      hcheckedJoinSound
  exact ⟨checkedJoin, hcheckedJoin, by simpa [PartialTy.eqv] using heqv⟩

theorem envJoinStep?_some_of_sameShape
    {left right result : FiniteEnv} {name : Name} :
    (left.lookup name = none ∧ right.lookup name = none) ∨
      (∃ leftSlot rightSlot,
        left.lookup name = some leftSlot ∧
          right.lookup name = some rightSlot ∧
            leftSlot.lifetime = rightSlot.lifetime ∧
              PartialTy.sameShape leftSlot.ty rightSlot.ty) →
      ∃ result',
        envJoinStep? left right result name = some result' := by
  intro hcompatible
  unfold envJoinStep?
  rcases hcompatible with hnone | hsome
  · rcases hnone with ⟨hleft, hright⟩
    simp [hleft, hright]
  · rcases hsome with
      ⟨leftSlot, rightSlot, hleft, hright, hlifetime, hshape⟩
    rcases partialTyJoin?_some_of_sameShape_complete hshape with
      ⟨joinTy, hjoinTy⟩
    simp [hleft, hright, hlifetime, hjoinTy]

theorem envJoinNames?_some_of_steps
    {left right result : FiniteEnv} :
    ∀ {names : List Name},
      (∀ name, name ∈ names →
        ∀ result, ∃ result',
          envJoinStep? left right result name = some result') →
        ∃ out, envJoinNames? left right names result = some out
  | [], _hsteps => by
      simp [envJoinNames?]
  | name :: rest, hsteps => by
      rcases hsteps name (by simp) result with ⟨result', hstep⟩
      have hrestSteps :
          ∀ restName, restName ∈ rest →
            ∀ result, ∃ result',
              envJoinStep? left right result restName = some result' := by
        intro restName hmem
        exact hsteps restName (by simp [hmem])
      rcases envJoinNames?_some_of_steps (result := result') hrestSteps with
        ⟨out, hout⟩
      refine ⟨out, ?_⟩
      simp [envJoinNames?, hstep, hout]

theorem envJoin?_some_of_envJoinSameShape_complete
    {left right : FiniteEnv} {join : Env} :
    EnvJoin left.toEnv right.toEnv join →
      EnvJoinSameShape left.toEnv join →
        EnvJoinSameShape right.toEnv join →
          ∃ joinFinite, envJoin? left right = some joinFinite := by
  intro hjoin hleftShape hrightShape
  unfold envJoin?
  let names := unionNames left.support right.support
  apply envJoinNames?_some_of_steps
  intro name hmem result
  have hleftUpper : EnvStrengthens left.toEnv join :=
    EnvJoin.left_le hjoin
  have hrightUpper : EnvStrengthens right.toEnv join :=
    EnvJoin.right_le hjoin
  have hcompatible :
      (left.lookup name = none ∧ right.lookup name = none) ∨
        (∃ leftSlot rightSlot,
          left.lookup name = some leftSlot ∧
            right.lookup name = some rightSlot ∧
              leftSlot.lifetime = rightSlot.lifetime ∧
                PartialTy.sameShape leftSlot.ty rightSlot.ty) := by
    rcases (mem_unionNames.mp hmem) with hleftMem | hrightMem
    · rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hleftMem) with
        ⟨leftSlot, hleftSlot⟩
      have hleftUpperAt := hleftUpper name
      change
        match left.lookup name, join.slotAt name with
        | none, none => True
        | some leftSlot, some rightSlot =>
            leftSlot.lifetime = rightSlot.lifetime ∧
              PartialTyStrengthens leftSlot.ty rightSlot.ty
        | _, _ => False at hleftUpperAt
      rw [hleftSlot] at hleftUpperAt
      cases hjoinSlot : join.slotAt name with
      | none =>
          simp [hjoinSlot] at hleftUpperAt
      | some joinSlot =>
          rw [hjoinSlot] at hleftUpperAt
          rcases hleftUpperAt with ⟨hleftLifetime, _hleftStrength⟩
          have hrightUpperAt := hrightUpper name
          change
            match right.lookup name, join.slotAt name with
            | none, none => True
            | some rightSlot, some joinSlot =>
                rightSlot.lifetime = joinSlot.lifetime ∧
                  PartialTyStrengthens rightSlot.ty joinSlot.ty
            | _, _ => False at hrightUpperAt
          rw [hjoinSlot] at hrightUpperAt
          cases hrightSlot : right.lookup name with
          | none =>
              simp [hrightSlot] at hrightUpperAt
          | some rightSlot =>
              simp [hrightSlot] at hrightUpperAt
              rcases hrightUpperAt with ⟨hrightLifetime, _hrightStrength⟩
              have hleftSame :
                  PartialTy.sameShape leftSlot.ty joinSlot.ty :=
                hleftShape name leftSlot joinSlot hleftSlot hjoinSlot
              have hrightSame :
                  PartialTy.sameShape rightSlot.ty joinSlot.ty :=
                hrightShape name rightSlot joinSlot hrightSlot hjoinSlot
              exact Or.inr
                ⟨leftSlot, rightSlot, hleftSlot, rfl,
                  hleftLifetime.trans hrightLifetime.symm,
                  PartialTy.sameShape_trans hleftSame
                    (PartialTy.sameShape_symm hrightSame)⟩
    · rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hrightMem) with
        ⟨rightSlot, hrightSlot⟩
      have hrightUpperAt := hrightUpper name
      change
        match right.lookup name, join.slotAt name with
        | none, none => True
        | some rightSlot, some joinSlot =>
            rightSlot.lifetime = joinSlot.lifetime ∧
              PartialTyStrengthens rightSlot.ty joinSlot.ty
        | _, _ => False at hrightUpperAt
      rw [hrightSlot] at hrightUpperAt
      cases hjoinSlot : join.slotAt name with
      | none =>
          simp [hjoinSlot] at hrightUpperAt
      | some joinSlot =>
          rw [hjoinSlot] at hrightUpperAt
          rcases hrightUpperAt with ⟨hrightLifetime, _hrightStrength⟩
          have hleftUpperAt := hleftUpper name
          change
            match left.lookup name, join.slotAt name with
            | none, none => True
            | some leftSlot, some joinSlot =>
                leftSlot.lifetime = joinSlot.lifetime ∧
                  PartialTyStrengthens leftSlot.ty joinSlot.ty
            | _, _ => False at hleftUpperAt
          rw [hjoinSlot] at hleftUpperAt
          cases hleftSlot : left.lookup name with
          | none =>
              simp [hleftSlot] at hleftUpperAt
          | some leftSlot =>
              simp [hleftSlot] at hleftUpperAt
              rcases hleftUpperAt with ⟨hleftLifetime, _hleftStrength⟩
              have hleftSame :
                  PartialTy.sameShape leftSlot.ty joinSlot.ty :=
                hleftShape name leftSlot joinSlot hleftSlot hjoinSlot
              have hrightSame :
                  PartialTy.sameShape rightSlot.ty joinSlot.ty :=
                hrightShape name rightSlot joinSlot hrightSlot hjoinSlot
              exact Or.inr
                ⟨leftSlot, rightSlot, rfl, hrightSlot,
                  hleftLifetime.trans hrightLifetime.symm,
                  PartialTy.sameShape_trans hleftSame
                    (PartialTy.sameShape_symm hrightSame)⟩
  exact envJoinStep?_some_of_sameShape hcompatible

theorem envJoinSameShape_complete {branch join : FiniteEnv} :
    EnvStrengthens branch.toEnv join.toEnv →
      EnvJoinSameShape branch.toEnv join.toEnv →
        envJoinSameShape branch join = true := by
  intro hstrength hshape
  unfold envJoinSameShape
  exact List.all_eq_true.mpr (by
    intro name hmem
    rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hmem) with
      ⟨branchSlot, hbranchSlot⟩
    have hstrengthAt := hstrength name
    change
      match branch.lookup name, join.lookup name with
      | none, none => True
      | some branchSlot, some joinSlot =>
          branchSlot.lifetime = joinSlot.lifetime ∧
            PartialTyStrengthens branchSlot.ty joinSlot.ty
      | _, _ => False at hstrengthAt
    rw [hbranchSlot] at hstrengthAt
    cases hjoinSlot : join.lookup name with
    | none =>
        simp [hjoinSlot] at hstrengthAt
    | some joinSlot =>
        have hsame : PartialTy.sameShape branchSlot.ty joinSlot.ty :=
          hshape name branchSlot joinSlot hbranchSlot hjoinSlot
        simp [hbranchSlot, partialTySameShape_complete hsame])

theorem lifetimeOutlives_antisymm {left right : Lifetime} :
    left ≤ right → right ≤ left → left = right := by
  intro hleftRight hrightLeft
  rcases left with ⟨leftPath⟩
  rcases right with ⟨rightPath⟩
  have hleftPrefix : leftPath <+: rightPath := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hleftRight
  have hrightPrefix : rightPath <+: leftPath := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hrightLeft
  have hleftLength : leftPath.length ≤ rightPath.length :=
    List.IsPrefix.length_le hleftPrefix
  have hrightLength : rightPath.length ≤ leftPath.length :=
    List.IsPrefix.length_le hrightPrefix
  have hlength : leftPath.length = rightPath.length :=
    Nat.le_antisymm hleftLength hrightLength
  have hpath : leftPath = rightPath :=
    List.IsPrefix.eq_of_length hleftPrefix hlength
  cases hpath
  rfl

theorem LifetimeIntersection.unique {left right first second : Lifetime} :
    LifetimeIntersection left right first →
      LifetimeIntersection left right second →
        first = second := by
  intro hfirst hsecond
  exact lifetimeOutlives_antisymm
    (hfirst.2 hsecond.1)
    (hsecond.2 hfirst.1)

theorem lifetimeIntersection?_complete
    {left right intersection : Lifetime} :
    LifetimeIntersection left right intersection →
      lifetimeIntersection? left right = some intersection := by
  intro hintersection
  have hleft : left ≤ intersection :=
    LifetimeIntersection.left_le hintersection
  have hright : right ≤ intersection :=
    LifetimeIntersection.right_le hintersection
  rcases LifetimeOutlives.comparable_of_common_inner hleft hright with
    hleftRight | hrightLeft
  · have hintersectionRight : intersection ≤ right :=
      hintersection.2 (by
        intro lifetime hmem
        simp at hmem
        rcases hmem with hleftMem | hrightMem
        · simpa [hleftMem] using hleftRight
        · simpa [hrightMem] using LifetimeOutlives.refl right)
    have hrightIntersection : right = intersection :=
      lifetimeOutlives_antisymm hright hintersectionRight
    unfold lifetimeIntersection?
    have hleftRightBool : left.contains right = true := by
      simpa [LifetimeOutlives] using hleftRight
    rw [hleftRightBool]
    exact congrArg some hrightIntersection
  · by_cases hleftRightBool : left.contains right
    · have hleftRight : left ≤ right := by
        simpa [LifetimeOutlives] using hleftRightBool
      have hintersectionRight : intersection ≤ right :=
        hintersection.2 (by
          intro lifetime hmem
          simp at hmem
          rcases hmem with hleftMem | hrightMem
          · simpa [hleftMem] using hleftRight
          · simpa [hrightMem] using LifetimeOutlives.refl right)
      have hrightIntersection : right = intersection :=
        lifetimeOutlives_antisymm hright hintersectionRight
      unfold lifetimeIntersection?
      rw [hleftRightBool]
      exact congrArg some hrightIntersection
    · have hintersectionLeft : intersection ≤ left :=
        hintersection.2 (by
          intro lifetime hmem
          simp at hmem
          rcases hmem with hleftMem | hrightMem
          · simpa [hleftMem] using LifetimeOutlives.refl left
          · simpa [hrightMem] using hrightLeft)
      have hleftIntersection : left = intersection :=
        lifetimeOutlives_antisymm hleft hintersectionLeft
      unfold lifetimeIntersection?
      have hrightLeftBool : right.contains left = true := by
        simpa [LifetimeOutlives] using hrightLeft
      have hleftRightFalse : left.contains right = false :=
        Bool.eq_false_iff.mpr hleftRightBool
      rw [hleftRightFalse, hrightLeftBool]
      exact congrArg some hleftIntersection

theorem lifetimeIntersection?_some_of_intersection_complete
    {left right intersection : Lifetime} :
    LifetimeIntersection left right intersection →
      ∃ computed, lifetimeIntersection? left right = some computed := by
  intro hintersection
  exact ⟨intersection, lifetimeIntersection?_complete hintersection⟩

theorem lvalTargetsTyping_lifetime_le_of_all_members
    {env : Env} {targets : List LVal} {partialTy : PartialTy}
    {lifetime outer : Lifetime} :
    LValTargetsTyping env targets partialTy lifetime →
      (∀ target ty targetLifetime,
        target ∈ targets →
          LValTyping env target (.ty ty) targetLifetime →
            targetLifetime ≤ outer) →
        lifetime ≤ outer := by
  intro htargets
  exact LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets _partialTy lifetime _ =>
      (∀ target ty targetLifetime,
        target ∈ targets →
          LValTyping env target (.ty ty) targetLifetime →
            targetLifetime ≤ outer) →
        lifetime ≤ outer)
    (by
      intro _x _slot _hslot
      trivial)
    (by
      intro _lv _inner _lifetime _htyping _ih
      trivial)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets _ihBorrow _ihTargets
      trivial)
    (by
      intro target ty targetLifetime htarget _ihTarget hmembers
      exact hmembers target ty targetLifetime (by simp) htarget)
    (by
      intro target rest headTy headLifetime restLifetime lifetime restTy
        unionTy hhead hrest _hunion hintersection _ihHead ihRest hmembers
      exact LifetimeIntersection.le_of_le hintersection
        (hmembers target headTy headLifetime (by simp) hhead)
        (ihRest (by
          intro selected selectedTy selectedLifetime hselected hselectedTyping
          exact hmembers selected selectedTy selectedLifetime
            (by simp [hselected]) hselectedTyping)))
    htargets

theorem lvalTargetsTyping_lifetime_eq_of_subset_of_member_lifetime_eq
    {env : Env} {leftTargets rightTargets : List LVal}
    {leftTy rightTy : PartialTy}
    {leftLifetime rightLifetime : Lifetime}
    (hdet :
      ∀ {target : LVal},
        target ∈ leftTargets ∨ target ∈ rightTargets →
        ∀ {left right : Ty} {leftLifetime rightLifetime : Lifetime},
          LValTyping env target (.ty left) leftLifetime →
          LValTyping env target (.ty right) rightLifetime →
            leftLifetime = rightLifetime)
    (hleft : LValTargetsTyping env leftTargets leftTy leftLifetime)
    (hright : LValTargetsTyping env rightTargets rightTy rightLifetime)
    (hleftRight : leftTargets.Subset rightTargets)
    (hrightLeft : rightTargets.Subset leftTargets) :
    leftLifetime = rightLifetime := by
  apply lifetimeOutlives_antisymm
  · exact lvalTargetsTyping_lifetime_le_of_all_members hleft (by
      intro target ty targetLifetime htargetLeft htargetTyping
      rcases lvalTargetsTyping_member_strengthens_outlives hright target
          (hleftRight htargetLeft) with
        ⟨rightMemberTy, rightTargetLifetime, hrightTyping, _hstrength,
          hrightLifetime⟩
      have hlifetimeEq :
          targetLifetime = rightTargetLifetime :=
        hdet (Or.inl htargetLeft) htargetTyping hrightTyping
      simpa [hlifetimeEq] using hrightLifetime)
  · exact lvalTargetsTyping_lifetime_le_of_all_members hright (by
      intro target ty targetLifetime htargetRight htargetTyping
      rcases lvalTargetsTyping_member_strengthens_outlives hleft target
          (hrightLeft htargetRight) with
        ⟨leftMemberTy, leftTargetLifetime, hleftTyping, _hstrength,
          hleftLifetime⟩
      have hlifetimeEq :
          leftTargetLifetime = targetLifetime :=
        hdet (Or.inr htargetRight) hleftTyping htargetTyping
      simpa [← hlifetimeEq] using hleftLifetime)

private theorem lvalTyping_lifetime_eq_of_linearizedBy_rank {env : Env}
    {φ : Name → Nat} (hφ : LinearizedBy φ env) :
    ∀ (rankBound sizeBound : Nat) {lv : LVal}
      {left right : PartialTy} {leftLifetime rightLifetime : Lifetime},
      φ (LVal.base lv) < rankBound →
      sizeOf lv < sizeBound →
      LValTyping env lv left leftLifetime →
      LValTyping env lv right rightLifetime →
        leftLifetime = rightLifetime := by
  intro rankBound
  induction rankBound with
  | zero =>
      intro sizeBound lv left right leftLifetime rightLifetime hrank _hsize
        _hleft _hright
      exact False.elim (Nat.not_lt_zero _ hrank)
  | succ rankBound ihRank =>
      intro sizeBound
      induction sizeBound with
      | zero =>
          intro lv left right leftLifetime rightLifetime _hrank hsize _hleft
            _hright
          exact False.elim (Nat.not_lt_zero _ hsize)
      | succ sizeBound ihSize =>
          intro lv left right leftLifetime rightLifetime hrank hsize hleft
            hright
          cases hleft with
          | var hleftSlot =>
              cases hright with
              | var hrightSlot =>
                  have hslotEq := Option.some.inj
                    (hleftSlot.symm.trans hrightSlot)
                  subst hslotEq
                  rfl
          | box hleftSource =>
              rename_i source
              cases hright with
              | box hrightSource =>
                  exact ihSize
                    (by simpa [LVal.base] using hrank)
                    (by
                      simp at hsize ⊢
                      omega)
                    hleftSource hrightSource
              | borrow hrightSource hrightTargets =>
                  have hsourceEqv :=
                    lvalTyping_eqv_of_linearizedBy hφ hleftSource
                      hrightSource
                  simp [PartialTy.eqv] at hsourceEqv
          | borrow hleftSource hleftTargets =>
              rename_i source _mutable _sourceTargets _borrowLifetime
              cases hright with
              | box hrightSource =>
                  have hsourceEqv :=
                    lvalTyping_eqv_of_linearizedBy hφ hleftSource
                      hrightSource
                  simp [PartialTy.eqv] at hsourceEqv
              | borrow hrightSource hrightTargets =>
                  have hsourceEqv :=
                    lvalTyping_eqv_of_linearizedBy hφ hleftSource
                      hrightSource
                  simp [PartialTy.eqv, Ty.eqv] at hsourceEqv
                  rcases hsourceEqv with
                    ⟨hmutableEq, hleftRight, hrightLeft⟩
                  subst hmutableEq
                  refine
                    lvalTargetsTyping_lifetime_eq_of_subset_of_member_lifetime_eq
                      ?_ hleftTargets hrightTargets hleftRight hrightLeft
                  intro target htargetMem leftTy rightTy leftTargetLifetime
                    rightTargetLifetime hleftTarget hrightTarget
                  have htargetRank :
                      φ (LVal.base target) < rankBound := by
                    have hsourceRank :
                        φ (LVal.base source) < rankBound + 1 := by
                      simpa [LVal.base] using hrank
                    rcases htargetMem with htargetLeft | htargetRight
                    · have hlt :=
                        (lvalTyping_vars_rank_lt hφ).1 hleftSource
                          (LVal.base target)
                          (by
                            simp [PartialTy.vars, Ty.vars]
                            exact ⟨target, htargetLeft, rfl⟩)
                      omega
                    · have hlt :=
                        (lvalTyping_vars_rank_lt hφ).1 hrightSource
                          (LVal.base target)
                          (by
                            simp [PartialTy.vars, Ty.vars]
                            exact ⟨target, htargetRight, rfl⟩)
                      omega
                  exact ihRank (sizeOf target + 1)
                    (by simpa using htargetRank)
                    (Nat.lt_succ_self _)
                    hleftTarget hrightTarget

theorem lvalTyping_lifetime_eq_of_linearizedBy {env : Env}
    {φ : Name → Nat} (hφ : LinearizedBy φ env)
    {lv : LVal} {left right : PartialTy}
    {leftLifetime rightLifetime : Lifetime} :
    LValTyping env lv left leftLifetime →
      LValTyping env lv right rightLifetime →
        leftLifetime = rightLifetime := by
  intro hleft hright
  exact lvalTyping_lifetime_eq_of_linearizedBy_rank hφ
    (φ (LVal.base lv) + 1) (sizeOf lv + 1)
    (Nat.lt_succ_self _) (Nat.lt_succ_self _) hleft hright

def LValCompleteAt (fuel : Nat) (env : FiniteEnv) : Prop :=
  ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
    LValTyping env.toEnv lv partialTy lifetime →
      ∃ checkedTy checkedLifetime,
        lvalType? fuel env lv = some (checkedTy, checkedLifetime) ∧
          PartialTy.eqv partialTy checkedTy ∧
            checkedLifetime = lifetime

def MutableCompleteAt (fuel : Nat) (env : FiniteEnv) : Prop :=
  ∀ {lv : LVal}, Mutable env.toEnv lv → mutableLVal fuel env lv = true

def LValCompleteAgainst (fuel : Nat) (finite : FiniteEnv) (env : Env) : Prop :=
  ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
    LValTyping env lv partialTy lifetime →
      ∃ checkedTy checkedLifetime,
        lvalType? fuel finite lv = some (checkedTy, checkedLifetime) ∧
          PartialTy.eqv partialTy checkedTy ∧
            checkedLifetime = lifetime

def MutableCompleteAgainst (fuel : Nat) (finite : FiniteEnv) (env : Env) : Prop :=
  ∀ {lv : LVal}, Mutable env lv → mutableLVal fuel finite lv = true

theorem LValCompleteAgainst.toEnv {fuel : Nat} {env : FiniteEnv} :
    LValCompleteAt fuel env →
      LValCompleteAgainst fuel env env.toEnv := by
  intro hcomplete lv partialTy lifetime htyping
  exact hcomplete htyping

theorem MutableCompleteAgainst.toEnv {fuel : Nat} {env : FiniteEnv} :
    MutableCompleteAt fuel env →
      MutableCompleteAgainst fuel env env.toEnv := by
  intro hcomplete lv hmutable
  exact hcomplete hmutable

def EnvSlotEqv (left right : EnvSlot) : Prop :=
  left.lifetime = right.lifetime ∧ PartialTy.eqv left.ty right.ty

def FiniteEnvEqv (finite : FiniteEnv) (env : Env) : Prop :=
  (∀ {name : Name} {slot : EnvSlot},
    finite.lookup name = some slot →
      ∃ envSlot,
        env.slotAt name = some envSlot ∧ EnvSlotEqv slot envSlot) ∧
  (∀ {name : Name} {envSlot : EnvSlot},
    env.slotAt name = some envSlot →
      ∃ slot,
        finite.lookup name = some slot ∧ EnvSlotEqv slot envSlot)

theorem envSlotEqv_refl (slot : EnvSlot) :
    EnvSlotEqv slot slot := by
  exact ⟨rfl, PartialTy.eqv_refl _⟩

theorem finiteEnvEqv_toEnv (env : FiniteEnv) :
    FiniteEnvEqv env env.toEnv := by
  constructor
  · intro name slot hslot
    exact ⟨slot, hslot, envSlotEqv_refl slot⟩
  · intro name slot hslot
    exact ⟨slot, hslot, envSlotEqv_refl slot⟩

theorem finiteEnvEqv_fresh_toEnv_of_fresh
    {finite : FiniteEnv} {env : Env} {name : Name} :
    FiniteEnvEqv finite env →
      env.fresh name →
        finite.toEnv.fresh name := by
  intro heqv hfresh
  change finite.lookup name = none
  cases hlookup : finite.lookup name with
  | none =>
      rfl
  | some slot =>
      rcases heqv.1 hlookup with ⟨envSlot, henvSlot, _heqvSlot⟩
      change env.slotAt name = none at hfresh
      rw [henvSlot] at hfresh
      cases hfresh

theorem finiteEnvEqv_fresh_of_toEnv_fresh
    {finite : FiniteEnv} {env : Env} {name : Name} :
    FiniteEnvEqv finite env →
      finite.toEnv.fresh name →
        env.fresh name := by
  intro heqv hfresh
  change env.slotAt name = none
  cases hslot : env.slotAt name with
  | none =>
      rfl
  | some envSlot =>
      rcases heqv.2 hslot with ⟨slot, hlookup, _heqvSlot⟩
      change finite.lookup name = none at hfresh
      rw [hlookup] at hfresh
      cases hfresh

theorem finiteEnvEqv_update
    {finite : FiniteEnv} {env : Env} {name : Name}
    {slot envSlot : EnvSlot} :
    FiniteEnvEqv finite env →
      EnvSlotEqv slot envSlot →
        FiniteEnvEqv (finite.update name slot) (env.update name envSlot) := by
  intro heqv hslotEqv
  constructor
  · intro needle updatedSlot hlookup
    by_cases hneedle : needle = name
    · subst hneedle
      rw [FiniteEnv.lookup_update_eq] at hlookup
      cases hlookup
      exact ⟨envSlot, by simp [Env.update], hslotEqv⟩
    · rw [FiniteEnv.lookup_update_ne finite slot hneedle] at hlookup
      rcases heqv.1 hlookup with ⟨oldEnvSlot, holdEnvSlot, holdEqv⟩
      exact ⟨oldEnvSlot, by simp [Env.update, hneedle, holdEnvSlot], holdEqv⟩
  · intro needle updatedEnvSlot henvLookup
    by_cases hneedle : needle = name
    · subst hneedle
      simp [Env.update] at henvLookup
      cases henvLookup
      exact ⟨slot, FiniteEnv.lookup_update_eq finite needle slot, hslotEqv⟩
    · have henvOld : env.slotAt needle = some updatedEnvSlot := by
        simpa [Env.update, hneedle] using henvLookup
      rcases heqv.2 henvOld with ⟨oldSlot, holdSlot, holdEqv⟩
      exact
        ⟨oldSlot,
          by simpa [FiniteEnv.lookup_update_ne finite slot hneedle] using holdSlot,
          holdEqv⟩

theorem envEqOutside_update_self
    (env : FiniteEnv) (name : Name) (slot : EnvSlot) :
    envEqOutside env (env.update name slot) name = true := by
  unfold envEqOutside
  exact List.all_eq_true.mpr (by
    intro candidate _hmem
    by_cases hcandidate : candidate = name
    · simp [hcandidate]
    · have hlookup :
          (env.update name slot).lookup candidate = env.lookup candidate :=
        FiniteEnv.lookup_update_ne env slot hcandidate
      simp [hcandidate, hlookup])

theorem envJoin?_some_of_envJoinSameShape_complete_against
    {left right : FiniteEnv} {leftEnv rightEnv join : Env} :
    FiniteEnvEqv left leftEnv →
      FiniteEnvEqv right rightEnv →
        EnvJoin leftEnv rightEnv join →
          EnvJoinSameShape leftEnv join →
            EnvJoinSameShape rightEnv join →
              ∃ joinFinite, envJoin? left right = some joinFinite := by
  intro heqvLeft heqvRight hjoin hleftShape hrightShape
  unfold envJoin?
  let names := unionNames left.support right.support
  apply envJoinNames?_some_of_steps
  intro name hmem result
  have hleftUpper : EnvStrengthens leftEnv join :=
    EnvJoin.left_le hjoin
  have hrightUpper : EnvStrengthens rightEnv join :=
    EnvJoin.right_le hjoin
  have hcompatible :
      (left.lookup name = none ∧ right.lookup name = none) ∨
        (∃ leftSlot rightSlot,
          left.lookup name = some leftSlot ∧
            right.lookup name = some rightSlot ∧
              leftSlot.lifetime = rightSlot.lifetime ∧
                PartialTy.sameShape leftSlot.ty rightSlot.ty) := by
    rcases (mem_unionNames.mp hmem) with hleftMem | hrightMem
    · rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hleftMem) with
        ⟨leftSlot, hleftSlot⟩
      rcases heqvLeft.1 hleftSlot with
        ⟨leftEnvSlot, hleftEnvSlot, hleftSlotEqv⟩
      have hleftUpperAt := hleftUpper name
      change
        match leftEnv.slotAt name, join.slotAt name with
        | none, none => True
        | some leftSlot, some joinSlot =>
            leftSlot.lifetime = joinSlot.lifetime ∧
              PartialTyStrengthens leftSlot.ty joinSlot.ty
        | _, _ => False at hleftUpperAt
      rw [hleftEnvSlot] at hleftUpperAt
      cases hjoinSlot : join.slotAt name with
      | none =>
          simp [hjoinSlot] at hleftUpperAt
      | some joinSlot =>
          rw [hjoinSlot] at hleftUpperAt
          rcases hleftUpperAt with ⟨hleftLifetime, _hleftStrength⟩
          have hrightUpperAt := hrightUpper name
          change
            match rightEnv.slotAt name, join.slotAt name with
            | none, none => True
            | some rightSlot, some joinSlot =>
                rightSlot.lifetime = joinSlot.lifetime ∧
                  PartialTyStrengthens rightSlot.ty joinSlot.ty
            | _, _ => False at hrightUpperAt
          rw [hjoinSlot] at hrightUpperAt
          cases hrightEnvSlot : rightEnv.slotAt name with
          | none =>
              simp [hrightEnvSlot] at hrightUpperAt
          | some rightEnvSlot =>
              rw [hrightEnvSlot] at hrightUpperAt
              rcases hrightUpperAt with ⟨hrightLifetime, _hrightStrength⟩
              rcases heqvRight.2 hrightEnvSlot with
                ⟨rightSlot, hrightSlot, hrightSlotEqv⟩
              have hlifetime : leftSlot.lifetime = rightSlot.lifetime := by
                calc
                  leftSlot.lifetime = leftEnvSlot.lifetime := hleftSlotEqv.1
                  _ = joinSlot.lifetime := hleftLifetime
                  _ = rightEnvSlot.lifetime := hrightLifetime.symm
                  _ = rightSlot.lifetime := hrightSlotEqv.1.symm
              have hleftSame :
                  PartialTy.sameShape leftSlot.ty leftEnvSlot.ty :=
                partialTy_eqv_sameShape hleftSlotEqv.2
              have hleftJoinSame :
                  PartialTy.sameShape leftEnvSlot.ty joinSlot.ty :=
                hleftShape name leftEnvSlot joinSlot hleftEnvSlot hjoinSlot
              have hrightJoinSame :
                  PartialTy.sameShape rightEnvSlot.ty joinSlot.ty :=
                hrightShape name rightEnvSlot joinSlot hrightEnvSlot hjoinSlot
              have hrightSame :
                  PartialTy.sameShape rightSlot.ty rightEnvSlot.ty :=
                partialTy_eqv_sameShape hrightSlotEqv.2
              exact Or.inr
                ⟨leftSlot, rightSlot, hleftSlot, hrightSlot, hlifetime,
                  PartialTy.sameShape_trans hleftSame
                    (PartialTy.sameShape_trans hleftJoinSame
                      (PartialTy.sameShape_trans
                        (PartialTy.sameShape_symm hrightJoinSame)
                        (PartialTy.sameShape_symm hrightSame)))⟩
    · rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hrightMem) with
        ⟨rightSlot, hrightSlot⟩
      rcases heqvRight.1 hrightSlot with
        ⟨rightEnvSlot, hrightEnvSlot, hrightSlotEqv⟩
      have hrightUpperAt := hrightUpper name
      change
        match rightEnv.slotAt name, join.slotAt name with
        | none, none => True
        | some rightSlot, some joinSlot =>
            rightSlot.lifetime = joinSlot.lifetime ∧
              PartialTyStrengthens rightSlot.ty joinSlot.ty
        | _, _ => False at hrightUpperAt
      rw [hrightEnvSlot] at hrightUpperAt
      cases hjoinSlot : join.slotAt name with
      | none =>
          simp [hjoinSlot] at hrightUpperAt
      | some joinSlot =>
          rw [hjoinSlot] at hrightUpperAt
          rcases hrightUpperAt with ⟨hrightLifetime, _hrightStrength⟩
          have hleftUpperAt := hleftUpper name
          change
            match leftEnv.slotAt name, join.slotAt name with
            | none, none => True
            | some leftSlot, some joinSlot =>
                leftSlot.lifetime = joinSlot.lifetime ∧
                  PartialTyStrengthens leftSlot.ty joinSlot.ty
            | _, _ => False at hleftUpperAt
          rw [hjoinSlot] at hleftUpperAt
          cases hleftEnvSlot : leftEnv.slotAt name with
          | none =>
              simp [hleftEnvSlot] at hleftUpperAt
          | some leftEnvSlot =>
              rw [hleftEnvSlot] at hleftUpperAt
              rcases hleftUpperAt with ⟨hleftLifetime, _hleftStrength⟩
              rcases heqvLeft.2 hleftEnvSlot with
                ⟨leftSlot, hleftSlot, hleftSlotEqv⟩
              have hlifetime : leftSlot.lifetime = rightSlot.lifetime := by
                calc
                  leftSlot.lifetime = leftEnvSlot.lifetime := hleftSlotEqv.1
                  _ = joinSlot.lifetime := hleftLifetime
                  _ = rightEnvSlot.lifetime := hrightLifetime.symm
                  _ = rightSlot.lifetime := hrightSlotEqv.1.symm
              have hleftSame :
                  PartialTy.sameShape leftSlot.ty leftEnvSlot.ty :=
                partialTy_eqv_sameShape hleftSlotEqv.2
              have hleftJoinSame :
                  PartialTy.sameShape leftEnvSlot.ty joinSlot.ty :=
                hleftShape name leftEnvSlot joinSlot hleftEnvSlot hjoinSlot
              have hrightJoinSame :
                  PartialTy.sameShape rightEnvSlot.ty joinSlot.ty :=
                hrightShape name rightEnvSlot joinSlot hrightEnvSlot hjoinSlot
              have hrightSame :
                  PartialTy.sameShape rightSlot.ty rightEnvSlot.ty :=
                partialTy_eqv_sameShape hrightSlotEqv.2
              exact Or.inr
                ⟨leftSlot, rightSlot, hleftSlot, hrightSlot, hlifetime,
                  PartialTy.sameShape_trans hleftSame
                    (PartialTy.sameShape_trans hleftJoinSame
                      (PartialTy.sameShape_trans
                        (PartialTy.sameShape_symm hrightJoinSame)
                        (PartialTy.sameShape_symm hrightSame)))⟩
  exact envJoinStep?_some_of_sameShape hcompatible

theorem envJoinSameShape_complete_against
    {branch joinFinite : FiniteEnv} {branchEnv joinEnv : Env} :
    FiniteEnvEqv branch branchEnv →
      FiniteEnvEqv joinFinite joinEnv →
        EnvStrengthens branchEnv joinEnv →
          EnvJoinSameShape branchEnv joinEnv →
            envJoinSameShape branch joinFinite = true := by
  intro heqvBranch heqvJoin hstrength hshape
  unfold envJoinSameShape
  exact List.all_eq_true.mpr (by
    intro name hmem
    rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hmem) with
      ⟨branchSlot, hbranchSlot⟩
    rcases heqvBranch.1 hbranchSlot with
      ⟨branchEnvSlot, hbranchEnvSlot, hbranchEqv⟩
    have hstrengthAt := hstrength name
    change
      match branchEnv.slotAt name, joinEnv.slotAt name with
      | none, none => True
      | some branchSlot, some joinSlot =>
          branchSlot.lifetime = joinSlot.lifetime ∧
            PartialTyStrengthens branchSlot.ty joinSlot.ty
      | _, _ => False at hstrengthAt
    rw [hbranchEnvSlot] at hstrengthAt
    cases hjoinEnvSlot : joinEnv.slotAt name with
    | none =>
        simp [hjoinEnvSlot] at hstrengthAt
    | some joinEnvSlot =>
        rcases heqvJoin.2 hjoinEnvSlot with
          ⟨joinFiniteSlot, hjoinFiniteSlot, hjoinEqv⟩
        have hbranchSame :
            PartialTy.sameShape branchSlot.ty branchEnvSlot.ty :=
          partialTy_eqv_sameShape hbranchEqv.2
        have henvSame :
            PartialTy.sameShape branchEnvSlot.ty joinEnvSlot.ty :=
          hshape name branchEnvSlot joinEnvSlot hbranchEnvSlot hjoinEnvSlot
        have hjoinSame :
            PartialTy.sameShape joinFiniteSlot.ty joinEnvSlot.ty :=
          partialTy_eqv_sameShape hjoinEqv.2
        have hsame :
            PartialTy.sameShape branchSlot.ty joinFiniteSlot.ty :=
          PartialTy.sameShape_trans hbranchSame
            (PartialTy.sameShape_trans henvSame
              (PartialTy.sameShape_symm hjoinSame))
        simp [hbranchSlot, hjoinFiniteSlot, partialTySameShape_complete hsame])

theorem finiteEnvEqv_of_envJoin?_of_envJoin
    {left right joinFinite : FiniteEnv} {joinEnv : Env} :
    envJoin? left right = some joinFinite →
      EnvJoin left.toEnv right.toEnv joinEnv →
        FiniteEnvEqv joinFinite joinEnv := by
  intro hrun hjoin
  constructor
  · intro name joinSlot hjoinFiniteSlot
    have hspec := envJoin?_slotSpec hrun name
    cases hleft : left.lookup name with
    | none =>
        cases hright : right.lookup name with
        | none =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
        | some rightSlot =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
    | some leftSlot =>
        cases hright : right.lookup name with
        | none =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
        | some rightSlot =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
            rcases hspec with ⟨hleftRightLife, hjoinLife, hjoinTy⟩
            have hleftUpper := (EnvJoin.left_le hjoin) name
            change
              match left.lookup name, joinEnv.slotAt name with
              | none, none => True
              | some leftSlot, some joinSlot =>
                  leftSlot.lifetime = joinSlot.lifetime ∧
                    PartialTyStrengthens leftSlot.ty joinSlot.ty
              | _, _ => False at hleftUpper
            rw [hleft] at hleftUpper
            cases hjoinEnvSlot : joinEnv.slotAt name with
            | none =>
                simp [hjoinEnvSlot] at hleftUpper
            | some envJoinSlot =>
                rcases EnvJoin.slot_union hjoin hleft hright hjoinEnvSlot with
                  ⟨hleftLifeEnv, _hrightLifeEnv, henvJoinTy⟩
                refine ⟨envJoinSlot, rfl, ?_⟩
                constructor
                · exact hjoinLife.trans hleftLifeEnv
                · exact PartialTyUnion.eqv_of_eqv hjoinTy
                    (PartialTy.eqv_refl _) (PartialTy.eqv_refl _)
                    henvJoinTy
  · intro name envJoinSlot hjoinEnvSlot
    rcases EnvJoin.lifetimesPreserved_left hjoin name envJoinSlot
        hjoinEnvSlot with
      ⟨leftSlot, hleft, hleftLife⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin name envJoinSlot
        hjoinEnvSlot with
      ⟨rightSlot, hright, _hrightLife⟩
    change left.lookup name = some leftSlot at hleft
    change right.lookup name = some rightSlot at hright
    have hspec := envJoin?_slotSpec hrun name
    cases hjoinFiniteSlot : joinFinite.lookup name with
    | none =>
        simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
    | some finiteJoinSlot =>
        simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
        rcases hspec with ⟨_hleftRightLife, hfiniteJoinLife, hfiniteJoinTy⟩
        rcases EnvJoin.slot_union hjoin hleft hright hjoinEnvSlot with
          ⟨_hleftLifeEnv, _hrightLifeEnv, henvJoinTy⟩
        refine ⟨finiteJoinSlot, rfl, ?_⟩
        constructor
        · exact hfiniteJoinLife.trans hleftLife
        · exact PartialTyUnion.eqv_of_eqv hfiniteJoinTy
            (PartialTy.eqv_refl _) (PartialTy.eqv_refl _)
            henvJoinTy

theorem finiteEnvEqv_of_envJoin?_of_envJoin_against
    {left right joinFinite : FiniteEnv} {leftEnv rightEnv joinEnv : Env} :
    FiniteEnvEqv left leftEnv →
      FiniteEnvEqv right rightEnv →
        envJoin? left right = some joinFinite →
          EnvJoin leftEnv rightEnv joinEnv →
            FiniteEnvEqv joinFinite joinEnv := by
  intro heqvLeft heqvRight hrun hjoin
  constructor
  · intro name joinSlot hjoinFiniteSlot
    have hspec := envJoin?_slotSpec hrun name
    cases hleft : left.lookup name with
    | none =>
        cases hright : right.lookup name with
        | none =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
        | some rightSlot =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
    | some leftSlot =>
        cases hright : right.lookup name with
        | none =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
        | some rightSlot =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
            rcases hspec with ⟨_hleftRightLife, hjoinLife, hjoinTy⟩
            rcases heqvLeft.1 hleft with
              ⟨leftEnvSlot, hleftEnvSlot, hleftEqv⟩
            rcases heqvRight.1 hright with
              ⟨rightEnvSlot, hrightEnvSlot, hrightEqv⟩
            have hleftUpper := (EnvJoin.left_le hjoin) name
            change
              match leftEnv.slotAt name, joinEnv.slotAt name with
              | none, none => True
              | some leftSlot, some joinSlot =>
                  leftSlot.lifetime = joinSlot.lifetime ∧
                    PartialTyStrengthens leftSlot.ty joinSlot.ty
              | _, _ => False at hleftUpper
            rw [hleftEnvSlot] at hleftUpper
            cases hjoinEnvSlot : joinEnv.slotAt name with
            | none =>
                simp [hjoinEnvSlot] at hleftUpper
            | some envJoinSlot =>
                rcases EnvJoin.slot_union hjoin hleftEnvSlot hrightEnvSlot
                    hjoinEnvSlot with
                  ⟨hleftLifeEnv, _hrightLifeEnv, henvJoinTy⟩
                refine ⟨envJoinSlot, rfl, ?_⟩
                constructor
                · exact hjoinLife.trans (hleftEqv.1.trans hleftLifeEnv)
                · exact PartialTyUnion.eqv_of_eqv hjoinTy
                    hleftEqv.2 hrightEqv.2 henvJoinTy
  · intro name envJoinSlot hjoinEnvSlot
    rcases EnvJoin.lifetimesPreserved_left hjoin name envJoinSlot
        hjoinEnvSlot with
      ⟨leftEnvSlot, hleftEnvSlot, hleftLife⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin name envJoinSlot
        hjoinEnvSlot with
      ⟨rightEnvSlot, hrightEnvSlot, _hrightLife⟩
    rcases heqvLeft.2 hleftEnvSlot with
      ⟨leftSlot, hleft, hleftEqv⟩
    rcases heqvRight.2 hrightEnvSlot with
      ⟨rightSlot, hright, hrightEqv⟩
    have hspec := envJoin?_slotSpec hrun name
    cases hjoinFiniteSlot : joinFinite.lookup name with
    | none =>
        simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
    | some finiteJoinSlot =>
        simp [EnvJoinSlotSpec, hleft, hright, hjoinFiniteSlot] at hspec
        rcases hspec with ⟨_hleftRightLife, hfiniteJoinLife, hfiniteJoinTy⟩
        rcases EnvJoin.slot_union hjoin hleftEnvSlot hrightEnvSlot
            hjoinEnvSlot with
          ⟨_hleftLifeEnv, _hrightLifeEnv, henvJoinTy⟩
        refine ⟨finiteJoinSlot, rfl, ?_⟩
        constructor
        · exact hfiniteJoinLife.trans (hleftEqv.1.trans hleftLife)
        · exact PartialTyUnion.eqv_of_eqv hfiniteJoinTy
            hleftEqv.2 hrightEqv.2 henvJoinTy

theorem envJoin?_complete_against
    {left right : FiniteEnv} {leftEnv rightEnv joinEnv : Env} :
    FiniteEnvEqv left leftEnv →
      FiniteEnvEqv right rightEnv →
        EnvJoin leftEnv rightEnv joinEnv →
          EnvJoinSameShape leftEnv joinEnv →
            EnvJoinSameShape rightEnv joinEnv →
              ∃ joinFinite,
                envJoin? left right = some joinFinite ∧
                  FiniteEnvEqv joinFinite joinEnv := by
  intro heqvLeft heqvRight hjoin hleftShape hrightShape
  rcases envJoin?_some_of_envJoinSameShape_complete_against
      heqvLeft heqvRight hjoin hleftShape hrightShape with
    ⟨joinFinite, hrun⟩
  exact ⟨joinFinite, hrun,
    finiteEnvEqv_of_envJoin?_of_envJoin_against
      heqvLeft heqvRight hrun hjoin⟩

theorem envJoinStep?_entriesReflectLookup
    {left right result result' : FiniteEnv} {name : Name} :
    envJoinStep? left right result name = some result' →
      FiniteEnv.EntriesReflectLookup result →
        FiniteEnv.EntriesReflectLookup result' := by
  intro hrun hreflect
  unfold envJoinStep? at hrun
  cases hleft : left.lookup name <;>
    cases hright : right.lookup name <;>
      simp [hleft, hright] at hrun
  · cases hrun
    exact hreflect
  · rename_i leftSlot rightSlot
    by_cases hlife : leftSlot.lifetime = rightSlot.lifetime
    · cases hjoin : partialTyJoin? leftSlot.ty rightSlot.ty with
      | none =>
          simp [hlife, hjoin] at hrun
      | some joinTy =>
          simp [hlife, hjoin] at hrun
          cases hrun
          exact FiniteEnv.entriesReflectLookup_update hreflect
    · simp [hlife] at hrun

theorem envJoinNames?_entriesReflectLookup
    {left right result out : FiniteEnv} {names : List Name} :
    envJoinNames? left right names result = some out →
      FiniteEnv.EntriesReflectLookup result →
        FiniteEnv.EntriesReflectLookup out := by
  induction names generalizing result with
  | nil =>
      intro hrun hreflect
      simp [envJoinNames?] at hrun
      cases hrun
      exact hreflect
  | cons name names ih =>
      intro hrun hreflect
      simp [envJoinNames?] at hrun
      cases hstep : envJoinStep? left right result name with
      | none =>
          simp [hstep] at hrun
      | some result' =>
          simp [hstep] at hrun
          exact ih hrun (envJoinStep?_entriesReflectLookup hstep hreflect)

theorem envJoin?_entriesReflectLookup
    {left right join : FiniteEnv} :
    envJoin? left right = some join →
      FiniteEnv.EntriesReflectLookup join := by
  intro hrun
  unfold envJoin? at hrun
  exact envJoinNames?_entriesReflectLookup hrun
    FiniteEnv.entriesReflectLookup_empty

mutual
  theorem tyBorrowTargetsFuelBounded_of_tyJoin?
      {fuel : Nat} :
      ∀ {left right join : Ty},
        tyJoin? left right = some join →
          tyBorrowTargetsFuelBounded fuel left →
            tyBorrowTargetsFuelBounded fuel right →
              tyBorrowTargetsFuelBounded fuel join := by
    intro left right join hjoin hleftBounded hrightBounded
    cases left with
    | unit =>
        cases right <;>
          simp [tyJoin?, tyBorrowTargetsFuelBounded] at hjoin hleftBounded hrightBounded ⊢
        cases hjoin
        trivial
    | int =>
        cases right <;>
          simp [tyJoin?, tyBorrowTargetsFuelBounded] at hjoin hleftBounded hrightBounded ⊢
        cases hjoin
        trivial
    | bool =>
        cases right <;>
          simp [tyJoin?, tyBorrowTargetsFuelBounded] at hjoin hleftBounded hrightBounded ⊢
        cases hjoin
        trivial
    | borrow leftMutable leftTargets =>
        cases right <;>
          simp [tyJoin?, tyBorrowTargetsFuelBounded] at hjoin hleftBounded hrightBounded ⊢
        rename_i rightMutable rightTargets
        cases leftMutable <;> cases rightMutable <;>
          simp at hjoin hleftBounded hrightBounded ⊢
        all_goals
          cases hjoin
          intro target htarget
          rcases mem_unionLVals.mp htarget with htarget | htarget
          · exact hleftBounded target htarget
          · exact hrightBounded target htarget
    | box leftInner =>
        cases right <;> simp [tyJoin?] at hjoin
        rename_i rightInner
        cases hinner : tyJoin? leftInner rightInner with
        | none =>
            simp [hinner] at hjoin
        | some innerJoin =>
            simp [hinner] at hjoin
            cases hjoin
            simp [tyBorrowTargetsFuelBounded] at hleftBounded hrightBounded ⊢
            exact tyBorrowTargetsFuelBounded_of_tyJoin? hinner
              hleftBounded hrightBounded

  theorem partialTyBorrowTargetsFuelBounded_of_partialTyJoin?
      {fuel : Nat} :
      ∀ {left right join : PartialTy},
        partialTyJoin? left right = some join →
          partialTyBorrowTargetsFuelBounded fuel left →
            partialTyBorrowTargetsFuelBounded fuel right →
              partialTyBorrowTargetsFuelBounded fuel join := by
    intro left right join hjoin hleftBounded hrightBounded
    cases left with
    | ty leftTy =>
        cases right <;>
          simp [partialTyJoin?, partialTyBorrowTargetsFuelBounded] at hjoin hleftBounded hrightBounded ⊢
        · rename_i rightTy
          cases htyJoin : tyJoin? leftTy rightTy with
          | none =>
              simp [htyJoin] at hjoin
          | some joinedTy =>
              simp [htyJoin] at hjoin
              cases hjoin
              exact tyBorrowTargetsFuelBounded_of_tyJoin? htyJoin
                hleftBounded hrightBounded
        · rename_i rightTy
          cases htyJoin : tyJoin? leftTy rightTy with
          | none =>
              simp [htyJoin] at hjoin
          | some joinedTy =>
              simp [htyJoin] at hjoin
              cases hjoin
              exact tyBorrowTargetsFuelBounded_of_tyJoin? htyJoin
                hleftBounded hrightBounded
    | box leftInner =>
        cases right <;> simp [partialTyJoin?] at hjoin
        rename_i rightInner
        cases hinner : partialTyJoin? leftInner rightInner with
        | none =>
            simp [hinner] at hjoin
        | some innerJoin =>
            simp [hinner] at hjoin
            cases hjoin
            simp [partialTyBorrowTargetsFuelBounded] at hleftBounded hrightBounded ⊢
            exact partialTyBorrowTargetsFuelBounded_of_partialTyJoin? hinner
              hleftBounded hrightBounded
    | undef leftTy =>
        cases right <;>
          simp [partialTyJoin?, partialTyBorrowTargetsFuelBounded] at hjoin hleftBounded hrightBounded ⊢
        · rename_i rightTy
          cases htyJoin : tyJoin? leftTy rightTy with
          | none =>
              simp [htyJoin] at hjoin
          | some joinedTy =>
              simp [htyJoin] at hjoin
              cases hjoin
              exact tyBorrowTargetsFuelBounded_of_tyJoin? htyJoin
                hleftBounded hrightBounded
        · rename_i rightTy
          cases htyJoin : tyJoin? leftTy rightTy with
          | none =>
              simp [htyJoin] at hjoin
          | some joinedTy =>
              simp [htyJoin] at hjoin
              cases hjoin
              exact tyBorrowTargetsFuelBounded_of_tyJoin? htyJoin
                hleftBounded hrightBounded
end

theorem envBorrowTargetsFuelBounded_envJoinStep?
    {fuel : Nat} {left right result result' : FiniteEnv} {name : Name} :
    envJoinStep? left right result name = some result' →
      envBorrowTargetsFuelBounded fuel left →
        envBorrowTargetsFuelBounded fuel right →
          envBorrowTargetsFuelBounded fuel result →
            envBorrowTargetsFuelBounded fuel result' := by
  intro hrun hleftBounded hrightBounded hresultBounded
  unfold envJoinStep? at hrun
  cases hleft : left.lookup name <;>
    cases hright : right.lookup name <;>
      simp [hleft, hright] at hrun
  · cases hrun
    exact hresultBounded
  · rename_i leftSlot rightSlot
    by_cases hlife : leftSlot.lifetime = rightSlot.lifetime
    · cases hjoin : partialTyJoin? leftSlot.ty rightSlot.ty with
      | none =>
          simp [hlife, hjoin] at hrun
      | some joinedTy =>
          simp [hlife, hjoin] at hrun
          cases hrun
          exact envBorrowTargetsFuelBounded_update hresultBounded
            (partialTyBorrowTargetsFuelBounded_of_partialTyJoin? hjoin
              (hleftBounded hleft) (hrightBounded hright))
    · simp [hlife] at hrun

theorem envBorrowTargetsFuelBounded_envJoinNames?
    {fuel : Nat} {left right result out : FiniteEnv} {names : List Name} :
    envJoinNames? left right names result = some out →
      envBorrowTargetsFuelBounded fuel left →
        envBorrowTargetsFuelBounded fuel right →
          envBorrowTargetsFuelBounded fuel result →
            envBorrowTargetsFuelBounded fuel out := by
  induction names generalizing result with
  | nil =>
      intro hrun _hleftBounded _hrightBounded hresultBounded
      simp [envJoinNames?] at hrun
      cases hrun
      exact hresultBounded
  | cons name names ih =>
      intro hrun hleftBounded hrightBounded hresultBounded
      simp [envJoinNames?] at hrun
      cases hstep : envJoinStep? left right result name with
      | none =>
          simp [hstep] at hrun
      | some result' =>
          simp [hstep] at hrun
          exact ih hrun hleftBounded hrightBounded
            (envBorrowTargetsFuelBounded_envJoinStep? hstep hleftBounded
              hrightBounded hresultBounded)

theorem envBorrowTargetsFuelBounded_envJoin?
    {fuel : Nat} {left right join : FiniteEnv} :
    envJoin? left right = some join →
      envBorrowTargetsFuelBounded fuel left →
        envBorrowTargetsFuelBounded fuel right →
          envBorrowTargetsFuelBounded fuel join := by
  intro hrun hleftBounded hrightBounded
  unfold envJoin? at hrun
  exact envBorrowTargetsFuelBounded_envJoinNames? hrun hleftBounded
    hrightBounded (envBorrowTargetsFuelBounded_empty fuel)

theorem finiteEnvEqv_dropLifetime
    {finite : FiniteEnv} {env : Env} {lifetime : Lifetime} :
    FiniteEnvEqv finite env →
      FiniteEnvEqv (finite.dropLifetime lifetime) (env.dropLifetime lifetime) := by
  intro heqv
  constructor
  · intro name slot hlookup
    have hdrop :
        (finite.toEnv.dropLifetime lifetime).slotAt name = some slot := by
      have htoEnv := congrArg (fun env => env.slotAt name)
        (FiniteEnv.toEnv_dropLifetime finite lifetime)
      rw [← htoEnv]
      exact hlookup
    cases hfinite : finite.lookup name with
    | none =>
        simp [Env.dropLifetime, FiniteEnv.toEnv, hfinite] at hdrop
    | some oldSlot =>
        by_cases holdLifetime : oldSlot.lifetime = lifetime
        · simp [Env.dropLifetime, FiniteEnv.toEnv, hfinite, holdLifetime] at hdrop
        · simp [Env.dropLifetime, FiniteEnv.toEnv, hfinite, holdLifetime] at hdrop
          subst hdrop
          rcases heqv.1 hfinite with ⟨envSlot, henvSlot, hslotEqv⟩
          have henvLifetime : envSlot.lifetime ≠ lifetime := by
            intro h
            exact holdLifetime (hslotEqv.1.trans h)
          exact
            ⟨envSlot,
              by simp [Env.dropLifetime, henvSlot, henvLifetime],
              hslotEqv⟩
  · intro name envSlot hlookup
    cases henv : env.slotAt name with
    | none =>
        simp [Env.dropLifetime, henv] at hlookup
    | some oldEnvSlot =>
        by_cases holdLifetime : oldEnvSlot.lifetime = lifetime
        · simp [Env.dropLifetime, henv, holdLifetime] at hlookup
        · simp [Env.dropLifetime, henv, holdLifetime] at hlookup
          subst hlookup
          rcases heqv.2 henv with ⟨slot, hfiniteSlot, hslotEqv⟩
          have hfiniteLifetime : slot.lifetime ≠ lifetime := by
            intro h
            exact holdLifetime (hslotEqv.1.symm.trans h)
          refine ⟨slot, ?_, hslotEqv⟩
          have hdrop :
              (finite.toEnv.dropLifetime lifetime).slotAt name = some slot := by
            simp [Env.dropLifetime, FiniteEnv.toEnv, hfiniteSlot,
              hfiniteLifetime]
          have htoEnv := congrArg (fun env => env.slotAt name)
            (FiniteEnv.toEnv_dropLifetime finite lifetime)
          change (finite.dropLifetime lifetime).toEnv.slotAt name = some slot
          rw [htoEnv]
          exact hdrop

theorem envBorrowTargetsFuelBounded_dropLifetime
    {fuel : Nat} {env : FiniteEnv} {lifetime : Lifetime} :
    envBorrowTargetsFuelBounded fuel env →
      envBorrowTargetsFuelBounded fuel (env.dropLifetime lifetime) := by
  intro henv name slot hlookup
  have hdrop := congrArg (fun env => env.slotAt name)
    (FiniteEnv.toEnv_dropLifetime env lifetime)
  change
    (env.dropLifetime lifetime).lookup name =
      (env.toEnv.dropLifetime lifetime).slotAt name at hdrop
  cases henvLookup : env.lookup name with
  | none =>
      simp [Env.dropLifetime, FiniteEnv.toEnv, henvLookup] at hdrop
      rw [hlookup] at hdrop
      cases hdrop
  | some oldSlot =>
      by_cases holdLifetime : oldSlot.lifetime = lifetime
      · simp [Env.dropLifetime, FiniteEnv.toEnv, henvLookup,
          holdLifetime] at hdrop
        rw [hlookup] at hdrop
        cases hdrop
      · simp [Env.dropLifetime, FiniteEnv.toEnv, henvLookup,
          holdLifetime] at hdrop
        rw [hlookup] at hdrop
        cases hdrop
        exact henv henvLookup

theorem partialTyContains_borrow_of_eqv_left_aux
    {left right : PartialTy} {needle : Ty} :
    PartialTy.eqv left right →
      PartialTyContains left needle →
        ∀ {mutable : Bool} {targets : List LVal},
          needle = .borrow mutable targets →
            ∃ rightTargets,
              PartialTyContains right (.borrow mutable rightTargets) ∧
                targets ⊆ rightTargets := by
  intro heqv hcontains
  induction hcontains generalizing right with
  | here =>
      intro mutable targets hneedle
      cases hneedle
      cases right <;> simp [PartialTy.eqv] at heqv
      rename_i rightTy
      cases rightTy <;> simp [Ty.eqv] at heqv
      rename_i rightMutable rightTargets
      rcases heqv with ⟨hmutable, hleftRight, _hrightLeft⟩
      cases hmutable
      exact ⟨rightTargets, PartialTyContains.here, hleftRight⟩
  | tyBox _hinner ih =>
      intro mutable targets hneedle
      cases right <;> simp [PartialTy.eqv] at heqv
      rename_i rightTy
      cases rightTy <;> simp [Ty.eqv] at heqv
      rename_i rightInner
      rcases ih (right := .ty rightInner) heqv hneedle with
        ⟨rightTargets, hcontainsRight, hsubset⟩
      exact ⟨rightTargets, PartialTyContains.tyBox hcontainsRight, hsubset⟩
  | box _hinner ih =>
      intro mutable targets hneedle
      cases right <;> simp [PartialTy.eqv] at heqv
      rename_i rightInner
      rcases ih (right := rightInner) heqv hneedle with
        ⟨rightTargets, hcontainsRight, hsubset⟩
      exact ⟨rightTargets, PartialTyContains.box hcontainsRight, hsubset⟩

theorem partialTyContains_borrow_of_eqv_left
    {left right : PartialTy} {mutable : Bool} {targets : List LVal} :
    PartialTy.eqv left right →
      PartialTyContains left (.borrow mutable targets) →
        ∃ rightTargets,
          PartialTyContains right (.borrow mutable rightTargets) ∧
            targets ⊆ rightTargets := by
  intro heqv hcontains
  exact partialTyContains_borrow_of_eqv_left_aux heqv hcontains rfl

theorem partialTy_vars_of_eqv_left
    {left right : PartialTy} {name : Name} :
    PartialTy.eqv left right →
      name ∈ PartialTy.vars left →
        name ∈ PartialTy.vars right := by
  intro heqv hmem
  rcases mem_partialTy_vars_iff.mp hmem with
    ⟨mutable, targets, target, hcontains, htarget, hbase⟩
  rcases partialTyContains_borrow_of_eqv_left heqv hcontains with
    ⟨rightTargets, hcontainsRight, hsubset⟩
  exact mem_partialTy_vars_iff.mpr
    ⟨mutable, rightTargets, target, hcontainsRight, hsubset htarget, hbase⟩

theorem ty_vars_of_eqv_left {left right : Ty} {name : Name} :
    Ty.eqv left right →
      name ∈ Ty.vars left →
        name ∈ Ty.vars right := by
  intro heqv hmem
  exact partialTy_vars_of_eqv_left (show PartialTy.eqv (.ty left) (.ty right) from heqv)
    hmem

theorem lval_base_mem_lvalNames (lv : LVal) :
    LVal.base lv ∈ lvalNames lv := by
  induction lv with
  | var name =>
      simp [LVal.base, lvalNames]
  | deref lv ih =>
      simpa [LVal.base, lvalNames] using ih

theorem lval_base_ne_of_not_mem_lvalNames {name : Name} {lv : LVal} :
    name ∉ lvalNames lv →
      LVal.base lv ≠ name := by
  intro hnot hbase
  exact hnot (by simpa [hbase] using lval_base_mem_lvalNames lv)

theorem targetNames_foldl_preserves
    {targets : List LVal} {acc : List Name} {name : Name} :
    name ∈ acc →
      name ∈ targets.foldl
        (fun names target => unionNames names (lvalNames target)) acc := by
  induction targets generalizing acc with
  | nil =>
      intro hmem
      exact hmem
  | cons target rest ih =>
      intro hmem
      apply ih
      exact (mem_unionNames).mpr (Or.inl hmem)

theorem target_base_mem_targetNames_foldl
    {targets : List LVal} {acc : List Name} {target : LVal} :
    target ∈ targets →
      LVal.base target ∈ targets.foldl
        (fun names target => unionNames names (lvalNames target)) acc := by
  induction targets generalizing acc with
  | nil =>
      intro hmem
      cases hmem
  | cons first rest ih =>
      intro hmem
      rw [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · apply targetNames_foldl_preserves (targets := rest)
        exact (mem_unionNames).mpr
          (Or.inr (by
            simpa [hhead] using lval_base_mem_lvalNames target))
      ·
        exact ih (acc := unionNames acc (lvalNames first)) htail

theorem ty_vars_mem_tyNames {ty : Ty} {name : Name} :
    name ∈ Ty.vars ty → name ∈ tyNames ty := by
  exact (Ty.rec
    (motive_1 := fun ty => ∀ name, name ∈ Ty.vars ty → name ∈ tyNames ty)
    (motive_2 := fun partialTy =>
      ∀ name, name ∈ PartialTy.vars partialTy → name ∈ partialTyNames partialTy)
    (by
      intro name hmem
      simp [Ty.vars] at hmem)
    (by
      intro name hmem
      simp [Ty.vars] at hmem)
    (by
      intro mutable targets name hmem
      rcases List.mem_map.mp hmem with ⟨target, htarget, hbase⟩
      simpa [tyNames, hbase] using
        (target_base_mem_targetNames_foldl
          (targets := targets) (acc := []) htarget))
    (by
      intro inner ih name hmem
      exact ih name hmem)
    (by
      intro name hmem
      simp [Ty.vars] at hmem)
    (by
      intro ty ih name hmem
      exact ih name hmem)
    (by
      intro inner ih name hmem
      exact ih name hmem)
    (by
      intro shape ih name hmem
      simp [PartialTy.vars] at hmem)
    ty name)

theorem partialTy_vars_mem_partialTyNames
    {partialTy : PartialTy} {name : Name} :
    name ∈ PartialTy.vars partialTy → name ∈ partialTyNames partialTy := by
  exact (PartialTy.rec
    (motive_1 := fun ty => ∀ name, name ∈ Ty.vars ty → name ∈ tyNames ty)
    (motive_2 := fun partialTy =>
      ∀ name, name ∈ PartialTy.vars partialTy → name ∈ partialTyNames partialTy)
    (by
      intro name hmem
      simp [Ty.vars] at hmem)
    (by
      intro name hmem
      simp [Ty.vars] at hmem)
    (by
      intro mutable targets name hmem
      rcases List.mem_map.mp hmem with ⟨target, htarget, hbase⟩
      simpa [tyNames, hbase] using
        (target_base_mem_targetNames_foldl
          (targets := targets) (acc := []) htarget))
    (by
      intro inner ih name hmem
      exact ih name hmem)
    (by
      intro name hmem
      simp [Ty.vars] at hmem)
    (by
      intro ty ih name hmem
      exact ih name hmem)
    (by
      intro inner ih name hmem
      exact ih name hmem)
    (by
      intro shape ih name hmem
      simp [PartialTy.vars] at hmem)
    partialTy name)

theorem envNames_foldl_preserves
    {entries : List (Name × EnvSlot)} {acc : List Name} {name : Name} :
    name ∈ acc →
      name ∈ entries.foldl
        (fun names entry =>
          unionNames (insertName names entry.1) (partialTyNames entry.2.ty))
        acc := by
  induction entries generalizing acc with
  | nil =>
      intro hmem
      exact hmem
  | cons entry rest ih =>
      intro hmem
      apply ih
      exact (mem_unionNames).mpr
        (Or.inl ((mem_insertName).mpr (Or.inl hmem)))

theorem envNames_entry_name_mem_foldl
    {entries : List (Name × EnvSlot)} {acc : List Name}
    {name : Name} {slot : EnvSlot} :
    (name, slot) ∈ entries →
      name ∈ entries.foldl
        (fun names entry =>
          unionNames (insertName names entry.1) (partialTyNames entry.2.ty))
        acc := by
  induction entries generalizing acc with
  | nil =>
      intro hmem
      cases hmem
  | cons entry rest ih =>
      intro hmem
      rcases entry with ⟨entryName, entrySlot⟩
      cases hmem with
      | head =>
        apply envNames_foldl_preserves (entries := rest)
        exact (mem_unionNames).mpr
          (Or.inl ((mem_insertName).mpr (Or.inr rfl)))
      | tail _ htail =>
        exact ih
          (acc := unionNames (insertName acc entryName)
            (partialTyNames entrySlot.ty)) htail

theorem envNames_entry_vars_mem_foldl
    {entries : List (Name × EnvSlot)} {acc : List Name}
    {name dep : Name} {slot : EnvSlot} :
    (name, slot) ∈ entries →
      dep ∈ PartialTy.vars slot.ty →
        dep ∈ entries.foldl
          (fun names entry =>
            unionNames (insertName names entry.1) (partialTyNames entry.2.ty))
          acc := by
  induction entries generalizing acc with
  | nil =>
      intro hmem _hdep
      cases hmem
  | cons entry rest ih =>
      intro hmem hdep
      rcases entry with ⟨entryName, entrySlot⟩
      cases hmem with
      | head =>
        apply envNames_foldl_preserves (entries := rest)
        exact (mem_unionNames).mpr
          (Or.inr (partialTy_vars_mem_partialTyNames hdep))
      | tail _ htail =>
        exact ih
          (acc := unionNames (insertName acc entryName)
            (partialTyNames entrySlot.ty)) htail hdep

theorem envNames_entry_name_mem {env : FiniteEnv}
    {name : Name} {slot : EnvSlot} :
    (name, slot) ∈ env.entries → name ∈ envNames env := by
  intro hentry
  exact envNames_entry_name_mem_foldl (acc := []) hentry

theorem envNames_entry_vars_mem {env : FiniteEnv}
    {name dep : Name} {slot : EnvSlot} :
    (name, slot) ∈ env.entries →
      dep ∈ PartialTy.vars slot.ty →
        dep ∈ envNames env := by
  intro hentry hdep
  exact envNames_entry_vars_mem_foldl (acc := []) hentry hdep

theorem envNames_lookup_vars_mem {env : FiniteEnv}
    {name dep : Name} {slot : EnvSlot} :
    env.lookup name = some slot →
      dep ∈ PartialTy.vars slot.ty →
        dep ∈ envNames env := by
  intro hslot hdep
  exact envNames_entry_vars_mem (FiniteEnv.lookupEntries_mem hslot) hdep

theorem envNames_lookup_name_mem {env : FiniteEnv}
    {name : Name} {slot : EnvSlot} :
    env.lookup name = some slot → name ∈ envNames env := by
  intro hslot
  exact envNames_entry_name_mem (FiniteEnv.lookupEntries_mem hslot)

theorem ty_vars_mem_envNames_of_wellFormedTy_eqv
    {finite : FiniteEnv} {env : Env} {checkedTy declTy : Ty}
    {lifetime : Lifetime} {dep : Name} :
    FiniteEnvEqv finite env →
      Ty.eqv checkedTy declTy →
        WellFormedTy env declTy lifetime →
          dep ∈ Ty.vars checkedTy →
            dep ∈ envNames finite := by
  intro heqv htyEqv hwell hdep
  have hdepDecl : dep ∈ Ty.vars declTy :=
    ty_vars_of_eqv_left htyEqv hdep
  rcases wellFormedTy_vars_in_env hwell dep hdepDecl with
    ⟨envSlot, henvSlot⟩
  rcases heqv.2 henvSlot with ⟨finiteSlot, hlookup, _hslotEqv⟩
  exact envNames_lookup_name_mem hlookup

theorem freshNameOfLength_length (fuel : Nat) :
    (freshNameOfLength fuel).length = fuel := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      have hunit : ("_" : String).length = 1 := by
        native_decide
      simp [freshNameOfLength, String.length_append, ih, hunit]
      omega

theorem name_length_le_maxNameLength_of_mem
    {used : List Name} {name : Name} :
    name ∈ used → name.length ≤ maxNameLength used := by
  induction used with
  | nil =>
      intro hmem
      cases hmem
  | cons head rest ih =>
      intro hmem
      rw [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · rw [hhead]
        exact Nat.le_max_left head.length (maxNameLength rest)
      · exact Nat.le_trans (ih htail)
          (Nat.le_max_right head.length (maxNameLength rest))

theorem freshNameFrom_not_mem (used : List Name) :
    freshNameFrom used ∉ used := by
  intro hmem
  have hle := name_length_le_maxNameLength_of_mem hmem
  simp [freshNameFrom, freshNameOfLength_length] at hle

theorem freshNameFrom_union_not_mem_left
    (left right : List Name) :
    freshNameFrom (unionNames left right) ∉ left := by
  intro hmem
  exact freshNameFrom_not_mem (unionNames left right)
    ((mem_unionNames).mpr (Or.inl hmem))

theorem freshNameFrom_union_not_mem_right
    (left right : List Name) :
    freshNameFrom (unionNames left right) ∉ right := by
  intro hmem
  exact freshNameFrom_not_mem (unionNames left right)
    ((mem_unionNames).mpr (Or.inr hmem))

theorem freshGhostName_not_mem_envNames
    (env : FiniteEnv) (term : Term) :
    freshGhostName env term ∉ envNames env := by
  simpa [freshGhostName] using
    freshNameFrom_union_not_mem_left (envNames env) (termNames term)

theorem freshGhostName_not_mem_termNames
    (env : FiniteEnv) (term : Term) :
    freshGhostName env term ∉ termNames term := by
  simpa [freshGhostName] using
    freshNameFrom_union_not_mem_right (envNames env) (termNames term)

theorem lval_base_ne_freshGhostName_of_mem_termNames
    {finite : FiniteEnv} {term : Term} {lv : LVal} :
    LVal.base lv ∈ termNames term →
      LVal.base lv ≠ freshGhostName finite term := by
  intro hmem hbase
  exact freshGhostName_not_mem_termNames finite term
    (by simpa [← hbase] using hmem)

theorem freshGhostName_ne_lval_base_of_mem_termNames
    {finite : FiniteEnv} {term : Term} {lv : LVal} :
    LVal.base lv ∈ termNames term →
      freshGhostName finite term ≠ LVal.base lv := by
  intro hmem hbase
  exact lval_base_ne_freshGhostName_of_mem_termNames hmem hbase.symm

theorem freshGhostName_ne_of_lookup
    {env : FiniteEnv} {term : Term} {name : Name} {slot : EnvSlot} :
    env.lookup name = some slot →
      freshGhostName env term ≠ name := by
  intro hlookup hname
  exact freshGhostName_not_mem_envNames env term
    (by simpa [hname] using envNames_lookup_name_mem hlookup)

theorem freshGhostName_not_mem_lookup_vars
    {env : FiniteEnv} {term : Term} {name dep : Name} {slot : EnvSlot} :
    env.lookup name = some slot →
      dep = freshGhostName env term →
        dep ∉ PartialTy.vars slot.ty := by
  intro hlookup hdep hmem
  subst dep
  exact freshGhostName_not_mem_envNames env term
    (envNames_lookup_vars_mem hlookup hmem)

theorem freshGhostName_fresh (env : FiniteEnv) (term : Term) :
    env.fresh (freshGhostName env term) = true := by
  cases hlookup : env.lookup (freshGhostName env term) with
  | none =>
      simp [FiniteEnv.fresh, hlookup]
  | some slot =>
      have hmem : freshGhostName env term ∈ envNames env :=
        envNames_lookup_name_mem hlookup
      exact False.elim (freshGhostName_not_mem_envNames env term hmem)

theorem freshGhostName_toEnv_fresh (env : FiniteEnv) (term : Term) :
    env.toEnv.fresh (freshGhostName env term) :=
  FiniteEnv.fresh_sound (freshGhostName_fresh env term)

theorem linearizedBy_of_finiteEnvEqv_left
    {finite : FiniteEnv} {env : Env} {φ : Name → Nat} :
    FiniteEnvEqv finite env →
      LinearizedBy φ env →
        LinearizedBy φ finite.toEnv := by
  intro heqv hlinear name slot hslot dep hdep
  rcases heqv.1 hslot with ⟨envSlot, henvSlot, hslotEqv⟩
  exact hlinear name envSlot henvSlot dep
    (partialTy_vars_of_eqv_left hslotEqv.2 hdep)

theorem linearizable_of_finiteEnvEqv_left
    {finite : FiniteEnv} {env : Env} :
    FiniteEnvEqv finite env →
      Linearizable env →
        Linearizable finite.toEnv := by
  intro heqv hlinear
  rcases hlinear with ⟨φ, hφ⟩
  exact ⟨φ, linearizedBy_of_finiteEnvEqv_left heqv hφ⟩

theorem envContains_borrow_of_finiteEnvEqv_left
    {finite : FiniteEnv} {env : Env} {name : Name}
    {mutable : Bool} {targets : List LVal} :
    FiniteEnvEqv finite env →
      finite.toEnv ⊢ name ↝ (.borrow mutable targets) →
        ∃ envTargets,
          env ⊢ name ↝ (.borrow mutable envTargets) ∧
            targets ⊆ envTargets := by
  intro heqv hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsSlot⟩
  rcases heqv.1 hslot with ⟨envSlot, henvSlot, hslotEqv⟩
  rcases partialTyContains_borrow_of_eqv_left hslotEqv.2 hcontainsSlot with
    ⟨envTargets, hcontainsEnvSlot, hsubset⟩
  exact ⟨envTargets, ⟨envSlot, henvSlot, hcontainsEnvSlot⟩, hsubset⟩

theorem envContains_borrow_of_finiteEnvEqv_right
    {finite : FiniteEnv} {env : Env} {name : Name}
    {mutable : Bool} {targets : List LVal} :
    FiniteEnvEqv finite env →
      env ⊢ name ↝ (.borrow mutable targets) →
        ∃ finiteTargets,
          finite.toEnv ⊢ name ↝ (.borrow mutable finiteTargets) ∧
            targets ⊆ finiteTargets := by
  intro heqv hcontains
  rcases hcontains with ⟨envSlot, henvSlot, hcontainsSlot⟩
  rcases heqv.2 henvSlot with ⟨slot, hslot, hslotEqv⟩
  rcases partialTyContains_borrow_of_eqv_left
      (PartialTy.eqv_symm hslotEqv.2) hcontainsSlot with
    ⟨finiteTargets, hcontainsFiniteSlot, hsubset⟩
  exact ⟨finiteTargets, ⟨slot, hslot, hcontainsFiniteSlot⟩, hsubset⟩

theorem readProhibited_of_finiteEnvEqv_left
    {finite : FiniteEnv} {env : Env} {lv : LVal} :
    FiniteEnvEqv finite env →
      ReadProhibited finite.toEnv lv →
        ReadProhibited env lv := by
  intro heqv hread
  rcases hread with ⟨name, targets, target, hcontains, htarget, hconflict⟩
  rcases envContains_borrow_of_finiteEnvEqv_left heqv hcontains with
    ⟨envTargets, hcontainsEnv, hsubset⟩
  exact ⟨name, envTargets, target, hcontainsEnv, hsubset htarget, hconflict⟩

theorem writeProhibited_of_finiteEnvEqv_left
    {finite : FiniteEnv} {env : Env} {lv : LVal} :
    FiniteEnvEqv finite env →
      WriteProhibited finite.toEnv lv →
        WriteProhibited env lv := by
  intro heqv hwrite
  cases hwrite with
  | inl hread =>
      exact Or.inl (readProhibited_of_finiteEnvEqv_left heqv hread)
  | inr himm =>
      rcases himm with ⟨name, targets, target, hcontains, htarget, hconflict⟩
      rcases envContains_borrow_of_finiteEnvEqv_left heqv hcontains with
        ⟨envTargets, hcontainsEnv, hsubset⟩
      exact Or.inr
        ⟨name, envTargets, target, hcontainsEnv, hsubset htarget, hconflict⟩

theorem not_readProhibited_toEnv_of_finiteEnvEqv
    {finite : FiniteEnv} {env : Env} {lv : LVal} :
    FiniteEnvEqv finite env →
      ¬ ReadProhibited env lv →
        ¬ ReadProhibited finite.toEnv lv := by
  intro heqv hnot hread
  exact hnot (readProhibited_of_finiteEnvEqv_left heqv hread)

theorem not_writeProhibited_toEnv_of_finiteEnvEqv
    {finite : FiniteEnv} {env : Env} {lv : LVal} :
    FiniteEnvEqv finite env →
      ¬ WriteProhibited env lv →
        ¬ WriteProhibited finite.toEnv lv := by
  intro heqv hnot hwrite
  exact hnot (writeProhibited_of_finiteEnvEqv_left heqv hwrite)

theorem not_lvalTyping_empty {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    ¬ LValTyping FiniteEnv.empty.toEnv lv partialTy lifetime := by
  intro htyping
  exact LValTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => False)
    (motive_2 := fun _targets _partialTy _lifetime _ => False)
    (by
      intro _x _slot hslot
      simp [FiniteEnv.empty, FiniteEnv.toEnv, FiniteEnv.lookup,
        FiniteEnv.lookupEntries] at hslot)
    (by
      intro _lv _inner _lifetime _hsource ih
      exact ih)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hsource _htargets ihSource _ihTargets
      exact ihSource)
    (by
      intro _target _ty _lifetime _htarget ihTarget
      exact ihTarget)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime
        _restTy _unionTy _hhead _hrest _hunion _hintersection ihHead _ihRest
      exact ihHead)
    htyping

theorem LValCompleteAt.empty (fuel : Nat) :
    LValCompleteAt fuel FiniteEnv.empty := by
  intro lv partialTy lifetime htyping
  exact False.elim (not_lvalTyping_empty htyping)

theorem MutableCompleteAt.empty (fuel : Nat) :
    MutableCompleteAt fuel FiniteEnv.empty := by
  intro lv hmutable
  cases hmutable with
  | var hslot =>
      simp [FiniteEnv.empty, FiniteEnv.toEnv, FiniteEnv.lookup,
        FiniteEnv.lookupEntries] at hslot
  | box htyping _hmutable =>
      exact False.elim (not_lvalTyping_empty htyping)
  | borrow htyping _htargets =>
      exact False.elim (not_lvalTyping_empty htyping)

theorem containedBorrowsWellFormed_empty_check (fuel : Nat) :
    containedBorrowsWellFormed fuel FiniteEnv.empty = true := by
  simp [containedBorrowsWellFormed, FiniteEnv.empty]

theorem coherent_empty_check (fuel : Nat) :
    coherent fuel FiniteEnv.empty = true := by
  simp [coherent, FiniteEnv.empty]

theorem linearizable_empty_check :
    linearizable FiniteEnv.empty = true := by
  simp [linearizable, envNames, FiniteEnv.empty]

theorem wellFormedKit_empty_check (fuel : Nat) :
    wellFormedKit fuel FiniteEnv.empty = true := by
  simp [wellFormedKit, containedBorrowsWellFormed_empty_check,
    coherent_empty_check, linearizable_empty_check]

theorem lvalTyping_contained_borrow_targets_fuelBounded
    {fuel : Nat} {env : FiniteEnv}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
    {mutable : Bool} {targets : List LVal} :
    envBorrowTargetsFuelBounded fuel env →
      LValTyping env.toEnv lv partialTy lifetime →
        PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target, target ∈ targets →
            lvalCheckerFuelBound target < fuel := by
  intro henv htyping
  exact LValTyping.rec
    (motive_1 := fun _lv partialTy _lifetime _ =>
      ∀ {mutable : Bool} {targets : List LVal},
        PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target, target ∈ targets →
            lvalCheckerFuelBound target < fuel)
    (motive_2 := fun _targets partialTy _lifetime _ =>
      ∀ {mutable : Bool} {targets : List LVal},
        PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target, target ∈ targets →
            lvalCheckerFuelBound target < fuel)
    (by
      intro _x _slot hslot _mutable _targets hcontains
      exact envBorrowTargetsFuelBounded_contains henv hslot hcontains)
    (by
      intro _lv _inner _lifetime _hsource ih _mutable _targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _mutable _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hsource _htargets _ihSource ihTargets _containedMutable
        _containedTargets hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime
        _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
        _mutable _targets hcontains target htarget
      rcases PartialTyUnion.contained_borrow_member hunion hcontains
          htarget with hheadContains | hrestContains
      · rcases hheadContains with ⟨headTargets, hcontainsHead,
          htargetHead⟩
        exact ihHead hcontainsHead target htargetHead
      · rcases hrestContains with ⟨restTargets, hcontainsRest,
          htargetRest⟩
        exact ihRest hcontainsRest target htargetRest)
    htyping

theorem lvalTargetsTyping_contained_borrow_targets_fuelBounded
    {fuel : Nat} {env : FiniteEnv}
    {sourceTargets : List LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} {mutable : Bool} {targets : List LVal} :
    envBorrowTargetsFuelBounded fuel env →
      LValTargetsTyping env.toEnv sourceTargets partialTy lifetime →
        PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target, target ∈ targets →
            lvalCheckerFuelBound target < fuel := by
  intro henv htyping
  exact LValTargetsTyping.rec
    (motive_1 := fun _lv partialTy _lifetime _ =>
      ∀ {mutable : Bool} {targets : List LVal},
        PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target, target ∈ targets →
            lvalCheckerFuelBound target < fuel)
    (motive_2 := fun _targets partialTy _lifetime _ =>
      ∀ {mutable : Bool} {targets : List LVal},
        PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target, target ∈ targets →
            lvalCheckerFuelBound target < fuel)
    (by
      intro _x _slot hslot _mutable _targets hcontains
      exact envBorrowTargetsFuelBounded_contains henv hslot hcontains)
    (by
      intro _lv _inner _lifetime _hsource ih _mutable _targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _mutable _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hsource _htargets _ihSource ihTargets _containedMutable
        _containedTargets hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime
        _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
        _mutable _targets hcontains target htarget
      rcases PartialTyUnion.contained_borrow_member hunion hcontains
          htarget with hheadContains | hrestContains
      · rcases hheadContains with ⟨headTargets, hcontainsHead,
          htargetHead⟩
        exact ihHead hcontainsHead target htargetHead
      · rcases hrestContains with ⟨restTargets, hcontainsRest,
          htargetRest⟩
        exact ihRest hcontainsRest target htargetRest)
    htyping

theorem lvalTyping_borrow_targets_fuelBounded
    {fuel : Nat} {env : FiniteEnv} {lv : LVal}
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    envBorrowTargetsFuelBounded fuel env →
      LValTyping env.toEnv lv (.ty (.borrow mutable targets)) lifetime →
        ∀ target, target ∈ targets →
          lvalCheckerFuelBound target < fuel := by
  intro henv htyping
  exact lvalTyping_contained_borrow_targets_fuelBounded henv htyping
    PartialTyContains.here

theorem lifetimeOutlives_complete {outer inner : Lifetime} :
    outer ≤ inner →
      lifetimeOutlives outer inner = true := by
  intro houtlives
  simpa [lifetimeOutlives, LifetimeOutlives] using houtlives

theorem lvalBaseOutlives_complete {env : FiniteEnv} {lv : LVal}
    {lifetime : Lifetime} :
    LValBaseOutlives env.toEnv lv lifetime →
      lvalBaseOutlives env lv lifetime = true := by
  rintro ⟨slot, hslot, houtlives⟩
  change env.lookup (LVal.base lv) = some slot at hslot
  simp [lvalBaseOutlives, hslot, lifetimeOutlives_complete houtlives]

theorem lvalBaseOutlives_complete_against
    {finite : FiniteEnv} {env : Env} {lv : LVal}
    {lifetime : Lifetime} :
    FiniteEnvEqv finite env →
      LValBaseOutlives env lv lifetime →
        lvalBaseOutlives finite lv lifetime = true := by
  intro heqv hbase
  rcases hbase with ⟨envSlot, henvSlot, houtlives⟩
  rcases heqv.2 henvSlot with ⟨slot, hslot, hslotEqv⟩
  have houtlivesFinite : slot.lifetime ≤ lifetime := by
    simpa [hslotEqv.1] using houtlives
  simp [lvalBaseOutlives, hslot, lifetimeOutlives_complete houtlivesFinite]

theorem lvalType?_some_fuelBound :
    ∀ {fuel : Nat} {env : FiniteEnv} {lv : LVal}
      {result : PartialTy × Lifetime},
      lvalType? fuel env lv = some result →
        lvalCheckerFuelBound lv ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro env lv result h
      simp [lvalType?] at h
  | succ fuel ih =>
      intro env lv result h
      cases lv with
      | var name =>
          simp [lvalCheckerFuelBound]
      | deref source =>
          cases hsource : lvalType? fuel env source with
          | none =>
              simp [lvalType?, hsource] at h
          | some sourceResult =>
              have hsourceBound : lvalCheckerFuelBound source ≤ fuel :=
                ih hsource
              cases sourceResult with
              | mk sourceTy sourceLifetime =>
                  cases sourceTy with
                  | box inner =>
                      simp [lvalType?, hsource] at h
                      simp [lvalCheckerFuelBound]
                      omega
                  | ty sourceFullTy =>
                      cases sourceFullTy with
                      | borrow mutable targets =>
                          cases htargets :
                              lvalTargetsType? fuel env targets with
                          | none =>
                              simp [lvalType?, hsource, htargets] at h
                          | some targetsResult =>
                              simp [lvalType?, hsource, htargets] at h
                              simp [lvalCheckerFuelBound]
                              omega
                      | unit =>
                          simp [lvalType?, hsource] at h
                      | int =>
                          simp [lvalType?, hsource] at h
                      | bool =>
                          simp [lvalType?, hsource] at h
                      | box inner =>
                          simp [lvalType?, hsource] at h
                  | undef fullTy =>
                      simp [lvalType?, hsource] at h

theorem borrowTargetsWellFormed_complete
    {fuel : Nat} {env : FiniteEnv} {targets : List LVal}
    {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      BorrowTargetsWellFormed env.toEnv targets lifetime →
        borrowTargetsWellFormed fuel env targets lifetime = true := by
  intro hcomplete htargets
  cases htargets with
  | intro htarget =>
      unfold borrowTargetsWellFormed
      exact List.all_eq_true.mpr (by
        intro target hmem
        rcases htarget target hmem with
          ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
        rcases hcomplete htyping with
          ⟨checkedTy, checkedLifetime, hchecked, heqv, hlifetime⟩
        rcases partialTy_eqv_ty_left_inv heqv with
          ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
        subst hcheckedTy
        simp [hchecked, hlifetime, lifetimeOutlives_complete houtlives,
          lvalBaseOutlives_complete hbase])

theorem borrowTargetsWellFormed_complete_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env}
    {targets : List LVal} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      FiniteEnvEqv finite env →
        BorrowTargetsWellFormed env targets lifetime →
          borrowTargetsWellFormed fuel finite targets lifetime = true := by
  intro hcomplete heqv htargets
  cases htargets with
  | intro htarget =>
      unfold borrowTargetsWellFormed
      exact List.all_eq_true.mpr (by
        intro target hmem
        rcases htarget target hmem with
          ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
        rcases hcomplete htyping with
          ⟨checkedTy, checkedLifetime, hchecked, heqvTy, hlifetime⟩
        rcases partialTy_eqv_ty_left_inv heqvTy with
          ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
        subst hcheckedTy
        simp [hchecked, hlifetime, lifetimeOutlives_complete houtlives,
          lvalBaseOutlives_complete_against heqv hbase])

theorem borrowTargetsWellFormedInSlot_complete
    {fuel : Nat} {env : FiniteEnv} {targets : List LVal}
    {slotLifetime : Lifetime} :
    LValCompleteAt fuel env →
      BorrowTargetsWellFormedInSlot env.toEnv slotLifetime targets →
        borrowTargetsWellFormed fuel env targets slotLifetime = true := by
  intro hcomplete htargets
  unfold BorrowTargetsWellFormedInSlot at htargets
  unfold borrowTargetsWellFormed
  exact List.all_eq_true.mpr (by
    intro target hmem
    rcases htargets target hmem with
      ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
    rcases hcomplete htyping with
      ⟨checkedTy, checkedLifetime, hchecked, heqv, hlifetime⟩
    rcases partialTy_eqv_ty_left_inv heqv with
      ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
    subst hcheckedTy
    simp [hchecked, hlifetime, lifetimeOutlives_complete houtlives,
      lvalBaseOutlives_complete hbase])

theorem borrowTargetsWellFormedInSlot_of_subset
    {env : Env} {left right : List LVal} {slotLifetime : Lifetime} :
    BorrowTargetsWellFormedInSlot env slotLifetime right →
      left ⊆ right →
        BorrowTargetsWellFormedInSlot env slotLifetime left := by
  intro hright hsubset target htarget
  exact hright target (hsubset htarget)

theorem borrowTargetsWellFormedInSlot_complete_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env}
    {targets : List LVal} {slotLifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      FiniteEnvEqv finite env →
        BorrowTargetsWellFormedInSlot env slotLifetime targets →
          borrowTargetsWellFormed fuel finite targets slotLifetime = true := by
  intro hcomplete heqv htargets
  unfold BorrowTargetsWellFormedInSlot at htargets
  unfold borrowTargetsWellFormed
  exact List.all_eq_true.mpr (by
    intro target hmem
    rcases htargets target hmem with
      ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
    rcases hcomplete htyping with
      ⟨checkedTy, checkedLifetime, hchecked, heqvTy, hlifetime⟩
    rcases partialTy_eqv_ty_left_inv heqvTy with
      ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
    subst hcheckedTy
    simp [hchecked, hlifetime, lifetimeOutlives_complete houtlives,
      lvalBaseOutlives_complete_against heqv hbase])

theorem wellFormedTy_complete {fuel : Nat} {env : FiniteEnv}
    {ty : Ty} {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      WellFormedTy env.toEnv ty lifetime →
        wellFormedTy fuel env ty lifetime = true := by
  intro hcomplete hwell
  induction hwell with
  | unit =>
      simp [wellFormedTy]
  | int =>
      simp [wellFormedTy]
  | bool =>
      simp [wellFormedTy]
  | borrow htargets =>
      simp [wellFormedTy, borrowTargetsWellFormed_complete hcomplete htargets]
  | box _hinner ih =>
      simp [wellFormedTy, ih]

theorem wellFormedTy_complete_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      FiniteEnvEqv finite env →
        WellFormedTy env ty lifetime →
          wellFormedTy fuel finite ty lifetime = true := by
  intro hcomplete heqv hwell
  induction hwell with
  | unit =>
      simp [wellFormedTy]
  | int =>
      simp [wellFormedTy]
  | bool =>
      simp [wellFormedTy]
  | borrow htargets =>
      simp [wellFormedTy,
        borrowTargetsWellFormed_complete_against hcomplete heqv htargets]
  | box _hinner ih =>
      simp [wellFormedTy, ih]

theorem borrowTargetsWellFormed_of_subset
    {env : Env} {left right : List LVal} {lifetime : Lifetime} :
    BorrowTargetsWellFormed env right lifetime →
      left ⊆ right →
        BorrowTargetsWellFormed env left lifetime := by
  intro hright hsubset
  cases hright with
  | intro htarget =>
      exact BorrowTargetsWellFormed.intro (by
        intro target hmem
        exact htarget target (hsubset hmem))

theorem wellFormedTy_of_eqv_left
    {env : Env} {lifetime : Lifetime} :
    ∀ {left right : Ty},
      Ty.eqv left right →
        WellFormedTy env right lifetime →
          WellFormedTy env left lifetime := by
  intro left
  refine Ty.rec
    (motive_1 := fun left =>
      ∀ {right : Ty},
        Ty.eqv left right →
          WellFormedTy env right lifetime →
            WellFormedTy env left lifetime)
    (motive_2 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro right heqv hwell
    cases right <;> simp [Ty.eqv] at heqv
    exact WellFormedTy.unit
  · intro right heqv hwell
    cases right <;> simp [Ty.eqv] at heqv
    exact WellFormedTy.int
  · intro leftMutable leftTargets right heqv hwell
    cases right <;> simp [Ty.eqv] at heqv
    rcases heqv with ⟨hmutable, hleftRight, _hrightLeft⟩
    subst hmutable
    cases hwell with
    | borrow htargets =>
        exact WellFormedTy.borrow
          (borrowTargetsWellFormed_of_subset htargets hleftRight)
  · intro leftInner ih right heqv hwell
    cases right <;> simp [Ty.eqv] at heqv
    cases hwell with
    | box hinner =>
        exact WellFormedTy.box (ih heqv hinner)
  · intro right heqv hwell
    cases right <;> simp [Ty.eqv] at heqv
    exact WellFormedTy.bool
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial

theorem wellFormedTy_complete_against_of_eqv
    {fuel : Nat} {finite : FiniteEnv} {env : Env}
    {checkedTy declTy : Ty} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      FiniteEnvEqv finite env →
        Ty.eqv checkedTy declTy →
          WellFormedTy env declTy lifetime →
            wellFormedTy fuel finite checkedTy lifetime = true := by
  intro hcomplete heqv htyEqv hwell
  exact wellFormedTy_complete_against hcomplete heqv
    (wellFormedTy_of_eqv_left htyEqv hwell)

theorem containedBorrowsWellFormed_update_fresh_ty
    {env : Env} {name : Name} {ty : Ty} {lifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
      WellFormedTy env ty lifetime →
        env.fresh name →
          ContainedBorrowsWellFormed
            (env.update name { ty := .ty ty, lifetime := lifetime }) := by
  intro hcontained hwell hfresh slotName envSlot mutable targets hslot hcontains
  by_cases hslotName : slotName = name
  · subst hslotName
    have hslotEq :
        envSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = envSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hcontainedEq :
        containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
        simpa [Env.update] using hcontainedSlot
      exact h.symm
    subst hcontainedEq
    exact borrowTargetsWellFormedInSlot_update_fresh
      (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
      (borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwell hcontainsTy)
  · have hslotOld : env.slotAt slotName = some envSlot := by
      simpa [Env.update, hslotName] using hslot
    have hcontainsOld : env ⊢ slotName ↝ Ty.borrow mutable targets := by
      rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hcontainedOld : env.slotAt slotName = some containedSlot := by
        simpa [Env.update, hslotName] using hcontainedSlot
      exact ⟨containedSlot, hcontainedOld, hcontainsTy⟩
    exact borrowTargetsWellFormedInSlot_update_fresh
      (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
      (hcontained slotName envSlot mutable targets hslotOld hcontainsOld)

theorem containedBorrowsWellFormed_update_fresh_ty_of_eqv_left
    {env : Env} {name : Name} {checkedTy declTy : Ty}
    {lifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
      WellFormedTy env declTy lifetime →
        env.fresh name →
          Ty.eqv checkedTy declTy →
            ContainedBorrowsWellFormed
              (env.update name { ty := .ty checkedTy, lifetime := lifetime }) := by
  intro hcontained hwell hfresh htyEqv
  exact containedBorrowsWellFormed_update_fresh_ty hcontained
    (wellFormedTy_of_eqv_left htyEqv hwell) hfresh

theorem borrowTargetsWellFormed_fuelBounded
    {fuel : Nat} {env : FiniteEnv} {targets : List LVal}
    {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      BorrowTargetsWellFormed env.toEnv targets lifetime →
        ∀ target, target ∈ targets →
          lvalCheckerFuelBound target < fuel + 1 := by
  intro hcomplete htargets target htargetMem
  cases htargets with
  | intro htarget =>
      rcases htarget target htargetMem with
        ⟨targetTy, targetLifetime, htyping, _houtlives, _hbase⟩
      rcases hcomplete htyping with
        ⟨checkedTy, checkedLifetime, hchecked, _heqv, _hlifetime⟩
      have hbound := lvalType?_some_fuelBound hchecked
      omega

theorem borrowTargetsWellFormed_fuelBounded_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env}
    {targets : List LVal} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      BorrowTargetsWellFormed env targets lifetime →
        ∀ target, target ∈ targets →
          lvalCheckerFuelBound target < fuel + 1 := by
  intro hcomplete htargets target htargetMem
  cases htargets with
  | intro htarget =>
      rcases htarget target htargetMem with
        ⟨targetTy, targetLifetime, htyping, _houtlives, _hbase⟩
      rcases hcomplete htyping with
        ⟨checkedTy, checkedLifetime, hchecked, _heqv, _hlifetime⟩
      have hbound := lvalType?_some_fuelBound hchecked
      omega

theorem wellFormedTy_borrowTargetsFuelBounded
    {fuel : Nat} {env : FiniteEnv} {ty : Ty} {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      WellFormedTy env.toEnv ty lifetime →
        tyBorrowTargetsFuelBounded (fuel + 1) ty := by
  intro hcomplete hwell
  induction hwell with
  | unit =>
      simp [tyBorrowTargetsFuelBounded]
  | int =>
      simp [tyBorrowTargetsFuelBounded]
  | bool =>
      simp [tyBorrowTargetsFuelBounded]
  | borrow htargets =>
      simpa [tyBorrowTargetsFuelBounded] using
        borrowTargetsWellFormed_fuelBounded hcomplete htargets
  | box _hinner ih =>
      simpa [tyBorrowTargetsFuelBounded] using ih

theorem wellFormedTy_borrowTargetsFuelBounded_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      WellFormedTy env ty lifetime →
        tyBorrowTargetsFuelBounded (fuel + 1) ty := by
  intro hcomplete hwell
  induction hwell with
  | unit =>
      simp [tyBorrowTargetsFuelBounded]
  | int =>
      simp [tyBorrowTargetsFuelBounded]
  | bool =>
      simp [tyBorrowTargetsFuelBounded]
  | borrow htargets =>
      simpa [tyBorrowTargetsFuelBounded] using
        borrowTargetsWellFormed_fuelBounded_against hcomplete htargets
  | box _hinner ih =>
      simpa [tyBorrowTargetsFuelBounded] using ih

theorem envBorrowTargetsFuelBounded_update_of_wellFormedTy
    {fuel : Nat} {env : FiniteEnv} {name : Name}
    {ty : Ty} {lifetime : Lifetime} :
    envBorrowTargetsFuelBounded fuel env →
      LValCompleteAt fuel env →
        WellFormedTy env.toEnv ty lifetime →
          envBorrowTargetsFuelBounded (fuel + 1)
            (env.update name { ty := .ty ty, lifetime := lifetime }) := by
  intro henv hcomplete hwell
  exact envBorrowTargetsFuelBounded_update
    (envBorrowTargetsFuelBounded_mono (by omega) henv)
    (show partialTyBorrowTargetsFuelBounded (fuel + 1) (.ty ty) from
      wellFormedTy_borrowTargetsFuelBounded hcomplete hwell)

theorem envBorrowTargetsFuelBounded_update_of_wellFormedTy_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {name : Name}
    {checkedTy declTy : Ty} {lifetime : Lifetime} :
    envBorrowTargetsFuelBounded fuel finite →
      LValCompleteAgainst fuel finite env →
        Ty.eqv checkedTy declTy →
          WellFormedTy env declTy lifetime →
            envBorrowTargetsFuelBounded (fuel + 1)
              (finite.update name { ty := .ty checkedTy, lifetime := lifetime }) := by
  intro henv hcomplete htyEqv hwell
  exact envBorrowTargetsFuelBounded_update
    (envBorrowTargetsFuelBounded_mono (by omega) henv)
    (show partialTyBorrowTargetsFuelBounded (fuel + 1) (.ty checkedTy) from
      wellFormedTy_borrowTargetsFuelBounded_against hcomplete
        (wellFormedTy_of_eqv_left htyEqv hwell))

theorem lvalTargetsType?_complete_of_lvalComplete
    {fuel : Nat} {env : FiniteEnv} {targets : List LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      Linearizable env.toEnv →
        LValTargetsTyping env.toEnv targets partialTy lifetime →
          ∃ checkedTy checkedLifetime,
            lvalTargetsType? fuel env targets =
                some (checkedTy, checkedLifetime) ∧
              PartialTy.eqv partialTy checkedTy ∧
                checkedLifetime = lifetime := by
  intro hcomplete _hlinear htargets
  exact LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy lifetime _ =>
      ∃ checkedTy checkedLifetime,
        lvalTargetsType? fuel env targets =
            some (checkedTy, checkedLifetime) ∧
          PartialTy.eqv partialTy checkedTy ∧
            checkedLifetime = lifetime)
    (by
      intro _x _slot _hslot
      trivial)
    (by
      intro _lv _inner _lifetime _htyping _ih
      trivial)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets _ihBorrow _ihTargets
      trivial)
    (by
      intro target ty targetLifetime htarget _ihTarget
      rcases hcomplete htarget with
        ⟨checkedTy, checkedLifetime, hchecked, heqv, hlifetime⟩
      rcases partialTy_eqv_ty_left_inv heqv with
        ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
      subst hcheckedTy
      subst hlifetime
      refine ⟨.ty checkedFullTy, checkedLifetime, ?_, ?_, rfl⟩
      · simp [lvalTargetsType?, hchecked]
      · exact hcheckedEqv)
    (by
      intro target rest headTy headLifetime restLifetime lifetime restTy
        unionTy hhead hrest hunion hintersection _ihHead ihRest
      rcases LValTargetsTyping.output_full hrest with
        ⟨restFullTy, hrestFull⟩
      subst hrestFull
      rcases PartialTyUnion.ty_ty_full hunion with
        ⟨unionFullTy, hunionFull⟩
      subst hunionFull
      rcases hcomplete hhead with
        ⟨checkedHeadTy, checkedHeadLifetime, hheadChecked,
          hheadEqv, hheadLifetime⟩
      rcases partialTy_eqv_ty_left_inv hheadEqv with
        ⟨checkedHeadFullTy, hcheckedHeadTy, hcheckedHeadEqv⟩
      subst hcheckedHeadTy
      subst hheadLifetime
      rcases ihRest with
        ⟨checkedRestTy, checkedRestLifetime, hrestChecked,
          hrestEqv, hrestLifetime⟩
      rcases partialTy_eqv_ty_left_inv hrestEqv with
        ⟨checkedRestFullTy, hcheckedRestTy, hcheckedRestEqv⟩
      subst hcheckedRestTy
      subst hrestLifetime
      have hheadUnionShape : Ty.sameShape headTy unionFullTy :=
        ty_sameShape_of_strengthens
          (by
            simpa using
              (PartialTyUnion.left_strengthens hunion :
                PartialTyStrengthens (.ty headTy) (.ty unionFullTy)))
      have hrestUnionShape : Ty.sameShape restFullTy unionFullTy :=
        ty_sameShape_of_strengthens
          (by
            simpa using
              (PartialTyUnion.right_strengthens hunion :
                PartialTyStrengthens (.ty restFullTy) (.ty unionFullTy)))
      have hheadRestShape : Ty.sameShape checkedHeadFullTy checkedRestFullTy :=
        Ty.sameShape_trans
          (Ty.sameShape_symm (ty_eqv_sameShape hcheckedHeadEqv))
          (Ty.sameShape_trans
            (Ty.sameShape_trans hheadUnionShape
              (Ty.sameShape_symm hrestUnionShape))
            (ty_eqv_sameShape hcheckedRestEqv))
      rcases tyJoin?_some_of_sameShape_complete hheadRestShape with
        ⟨joinFullTy, hjoin⟩
      have hjoinSound :
          PartialTyUnion (.ty checkedHeadFullTy) (.ty checkedRestFullTy)
            (.ty joinFullTy) :=
        tyJoin?_sound_for_completeness hjoin
      refine ⟨.ty joinFullTy, lifetime, ?_, ?_, rfl⟩
      · cases rest with
        | nil =>
            cases hrest
        | cons restHead restTail =>
            simp [lvalTargetsType?, hheadChecked, hrestChecked,
              partialTyJoin?, hjoin,
              lifetimeIntersection?_complete hintersection]
      · exact PartialTyUnion.eqv_of_eqv hunion
          (show PartialTy.eqv (.ty headTy) (.ty checkedHeadFullTy) from
            hcheckedHeadEqv)
          (show PartialTy.eqv (.ty restFullTy) (.ty checkedRestFullTy) from
            hcheckedRestEqv)
          hjoinSound)
    htargets

theorem lvalTargetsType?_complete_of_lvalCompleteAgainst
    {fuel : Nat} {finite : FiniteEnv} {env : Env}
    {targets : List LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      LValTargetsTyping env targets partialTy lifetime →
        ∃ checkedTy checkedLifetime,
          lvalTargetsType? fuel finite targets =
              some (checkedTy, checkedLifetime) ∧
            PartialTy.eqv partialTy checkedTy ∧
              checkedLifetime = lifetime := by
  intro hcomplete htargets
  exact LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy lifetime _ =>
      ∃ checkedTy checkedLifetime,
        lvalTargetsType? fuel finite targets =
            some (checkedTy, checkedLifetime) ∧
          PartialTy.eqv partialTy checkedTy ∧
            checkedLifetime = lifetime)
    (by
      intro _x _slot _hslot
      trivial)
    (by
      intro _lv _inner _lifetime _htyping _ih
      trivial)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets _ihBorrow _ihTargets
      trivial)
    (by
      intro target ty targetLifetime htarget _ihTarget
      rcases hcomplete htarget with
        ⟨checkedTy, checkedLifetime, hchecked, heqv, hlifetime⟩
      rcases partialTy_eqv_ty_left_inv heqv with
        ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
      subst hcheckedTy
      subst hlifetime
      refine ⟨.ty checkedFullTy, checkedLifetime, ?_, ?_, rfl⟩
      · simp [lvalTargetsType?, hchecked]
      · exact hcheckedEqv)
    (by
      intro target rest headTy headLifetime restLifetime lifetime restTy
        unionTy hhead hrest hunion hintersection _ihHead ihRest
      rcases LValTargetsTyping.output_full hrest with
        ⟨restFullTy, hrestFull⟩
      subst hrestFull
      rcases PartialTyUnion.ty_ty_full hunion with
        ⟨unionFullTy, hunionFull⟩
      subst hunionFull
      rcases hcomplete hhead with
        ⟨checkedHeadTy, checkedHeadLifetime, hheadChecked,
          hheadEqv, hheadLifetime⟩
      rcases partialTy_eqv_ty_left_inv hheadEqv with
        ⟨checkedHeadFullTy, hcheckedHeadTy, hcheckedHeadEqv⟩
      subst hcheckedHeadTy
      subst hheadLifetime
      rcases ihRest with
        ⟨checkedRestTy, checkedRestLifetime, hrestChecked,
          hrestEqv, hrestLifetime⟩
      rcases partialTy_eqv_ty_left_inv hrestEqv with
        ⟨checkedRestFullTy, hcheckedRestTy, hcheckedRestEqv⟩
      subst hcheckedRestTy
      subst hrestLifetime
      have hheadUnionShape : Ty.sameShape headTy unionFullTy :=
        ty_sameShape_of_strengthens
          (by
            simpa using
              (PartialTyUnion.left_strengthens hunion :
                PartialTyStrengthens (.ty headTy) (.ty unionFullTy)))
      have hrestUnionShape : Ty.sameShape restFullTy unionFullTy :=
        ty_sameShape_of_strengthens
          (by
            simpa using
              (PartialTyUnion.right_strengthens hunion :
                PartialTyStrengthens (.ty restFullTy) (.ty unionFullTy)))
      have hheadRestShape : Ty.sameShape checkedHeadFullTy checkedRestFullTy :=
        Ty.sameShape_trans
          (Ty.sameShape_symm (ty_eqv_sameShape hcheckedHeadEqv))
          (Ty.sameShape_trans
            (Ty.sameShape_trans hheadUnionShape
              (Ty.sameShape_symm hrestUnionShape))
            (ty_eqv_sameShape hcheckedRestEqv))
      rcases tyJoin?_some_of_sameShape_complete hheadRestShape with
        ⟨joinFullTy, hjoin⟩
      have hjoinSound :
          PartialTyUnion (.ty checkedHeadFullTy) (.ty checkedRestFullTy)
            (.ty joinFullTy) :=
        tyJoin?_sound_for_completeness hjoin
      refine ⟨.ty joinFullTy, lifetime, ?_, ?_, rfl⟩
      · cases rest with
        | nil =>
            cases hrest
        | cons restHead restTail =>
            simp [lvalTargetsType?, hheadChecked, hrestChecked,
              partialTyJoin?, hjoin,
              lifetimeIntersection?_complete hintersection]
      · exact PartialTyUnion.eqv_of_eqv hunion
          (show PartialTy.eqv (.ty headTy) (.ty checkedHeadFullTy) from
            hcheckedHeadEqv)
          (show PartialTy.eqv (.ty restFullTy) (.ty checkedRestFullTy) from
            hcheckedRestEqv)
          hjoinSound)
    htargets

theorem lvalTargetsType?_type_complete_of_lvalComplete_subset
    {fuel : Nat} {env : FiniteEnv}
    {targets selectedTargets : List LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      Linearizable env.toEnv →
        LValTargetsTyping env.toEnv targets partialTy lifetime →
          selectedTargets ≠ [] →
            selectedTargets.Subset targets →
              targets.Subset selectedTargets →
                ∃ checkedTy checkedLifetime,
                  lvalTargetsType? fuel env selectedTargets =
                      some (checkedTy, checkedLifetime) ∧
                    PartialTy.eqv partialTy checkedTy ∧
                      checkedLifetime = lifetime := by
  intro hcomplete hlinear htargets hselectedNonempty hselectedTargets
    htargetsSelected
  rcases hlinear with ⟨φ, hφ⟩
  rcases LValTargetsTyping.output_full htargets with
    ⟨sourceTy, hsourceFull⟩
  subst hsourceFull
  rcases lvalTargetsTyping_of_nonempty_subset htargets hselectedNonempty
      hselectedTargets with
    ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength,
      _houtlives⟩
  have hdet :
      ∀ {lv : LVal} {left right : Ty}
        {leftLifetime rightLifetime : Lifetime},
        LValTyping env.toEnv lv (.ty left) leftLifetime →
        LValTyping env.toEnv lv (.ty right) rightLifetime →
          PartialTy.eqv (.ty left) (.ty right) := by
    intro lv left right leftLifetime rightLifetime hleft hright
    exact lvalTyping_eqv_of_linearizedBy hφ hleft hright
  have htargetsEqv :
      PartialTy.eqv (.ty sourceTy) (.ty selectedTy) :=
    lvalTargetsTyping_eqv_of_subset_of_lval_eqv hdet htargets
      hselectedTyping htargetsSelected hselectedTargets
  have hlifetime :
      selectedLifetime = lifetime := by
    apply lvalTargetsTyping_lifetime_eq_of_subset_of_member_lifetime_eq
      (env := env.toEnv)
      (leftTargets := selectedTargets) (rightTargets := targets)
      (leftTy := .ty selectedTy) (rightTy := .ty sourceTy)
      (leftLifetime := selectedLifetime) (rightLifetime := lifetime)
    · intro target _htargetMem left right leftLifetime rightLifetime hleft
        hright
      exact lvalTyping_lifetime_eq_of_linearizedBy hφ hleft hright
    · exact hselectedTyping
    · exact htargets
    · exact hselectedTargets
    · exact htargetsSelected
  rcases lvalTargetsType?_complete_of_lvalComplete hcomplete ⟨φ, hφ⟩
      hselectedTyping with
    ⟨checkedTy, checkedLifetime, hchecked, hselectedEqv,
      hcheckedLifetime⟩
  exact ⟨checkedTy, checkedLifetime, hchecked,
    PartialTy.eqv_trans htargetsEqv hselectedEqv,
    by rw [hcheckedLifetime, hlifetime]⟩

theorem lvalTargetsType?_type_complete_of_lvalCompleteAgainst_subset
    {fuel : Nat} {finite : FiniteEnv} {env : Env}
    {targets selectedTargets : List LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      Linearizable env →
        LValTargetsTyping env targets partialTy lifetime →
          selectedTargets ≠ [] →
            selectedTargets.Subset targets →
              targets.Subset selectedTargets →
                ∃ checkedTy checkedLifetime,
                  lvalTargetsType? fuel finite selectedTargets =
                      some (checkedTy, checkedLifetime) ∧
                    PartialTy.eqv partialTy checkedTy ∧
                      checkedLifetime = lifetime := by
  intro hcomplete hlinear htargets hselectedNonempty hselectedTargets
    htargetsSelected
  rcases hlinear with ⟨φ, hφ⟩
  rcases LValTargetsTyping.output_full htargets with
    ⟨sourceTy, hsourceFull⟩
  subst hsourceFull
  rcases lvalTargetsTyping_of_nonempty_subset htargets hselectedNonempty
      hselectedTargets with
    ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength,
      _houtlives⟩
  have hdet :
      ∀ {lv : LVal} {left right : Ty}
        {leftLifetime rightLifetime : Lifetime},
        LValTyping env lv (.ty left) leftLifetime →
        LValTyping env lv (.ty right) rightLifetime →
          PartialTy.eqv (.ty left) (.ty right) := by
    intro lv left right leftLifetime rightLifetime hleft hright
    exact lvalTyping_eqv_of_linearizedBy hφ hleft hright
  have htargetsEqv :
      PartialTy.eqv (.ty sourceTy) (.ty selectedTy) :=
    lvalTargetsTyping_eqv_of_subset_of_lval_eqv hdet htargets
      hselectedTyping htargetsSelected hselectedTargets
  have hlifetime :
      selectedLifetime = lifetime := by
    apply lvalTargetsTyping_lifetime_eq_of_subset_of_member_lifetime_eq
      (env := env)
      (leftTargets := selectedTargets) (rightTargets := targets)
      (leftTy := .ty selectedTy) (rightTy := .ty sourceTy)
      (leftLifetime := selectedLifetime) (rightLifetime := lifetime)
    · intro target _htargetMem left right leftLifetime rightLifetime hleft
        hright
      exact lvalTyping_lifetime_eq_of_linearizedBy hφ hleft hright
    · exact hselectedTyping
    · exact htargets
    · exact hselectedTargets
    · exact htargetsSelected
  rcases lvalTargetsType?_complete_of_lvalCompleteAgainst hcomplete
      hselectedTyping with
    ⟨checkedTy, checkedLifetime, hchecked, hselectedEqv,
      hcheckedLifetime⟩
  exact ⟨checkedTy, checkedLifetime, hchecked,
    PartialTy.eqv_trans htargetsEqv hselectedEqv,
    by rw [hcheckedLifetime, hlifetime]⟩

theorem lvalType?_box_complete_step
    {fuel : Nat} {env : FiniteEnv} {lv : LVal}
    {inner : PartialTy} {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      LValTyping env.toEnv lv (.box inner) lifetime →
        ∃ checkedTy checkedLifetime,
          lvalType? (fuel + 1) env (.deref lv) =
              some (checkedTy, checkedLifetime) ∧
            PartialTy.eqv inner checkedTy ∧
              checkedLifetime = lifetime := by
  intro hcomplete htyping
  rcases hcomplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, hlifetime⟩
  rcases partialTy_eqv_box_left_inv heqv with
    ⟨checkedInner, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  refine ⟨checkedInner, checkedLifetime, ?_, hcheckedEqv, hlifetime⟩
  simp [lvalType?, hchecked]

theorem lvalType?_borrow_type_complete_step
    {fuel : Nat} {env : FiniteEnv} {lv : LVal}
    {mutable : Bool} {targets : List LVal}
    {borrowLifetime targetLifetime : Lifetime} {targetTy : PartialTy} :
    LValCompleteAt fuel env →
      Linearizable env.toEnv →
        LValTyping env.toEnv lv (.ty (.borrow mutable targets)) borrowLifetime →
          LValTargetsTyping env.toEnv targets targetTy targetLifetime →
            ∃ checkedTy checkedLifetime,
              lvalType? (fuel + 1) env (.deref lv) =
                  some (checkedTy, checkedLifetime) ∧
                PartialTy.eqv targetTy checkedTy ∧
                  checkedLifetime = targetLifetime := by
  intro hcomplete hlinear hborrowTyping htargets
  rcases hcomplete hborrowTyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  rcases ty_eqv_borrow_left_inv hcheckedEqv with
    ⟨checkedTargets, hcheckedFullTy, htargetsChecked,
      hcheckedTargets⟩
  subst hcheckedFullTy
  have hcheckedTargetsNonempty : checkedTargets ≠ [] := by
    intro hnil
    cases targets with
    | nil =>
        exact LValTargetsTyping.nil_false htargets
    | cons target rest =>
        have htarget : target ∈ checkedTargets :=
          htargetsChecked (by simp)
        simp [hnil] at htarget
  rcases lvalTargetsType?_type_complete_of_lvalComplete_subset
      hcomplete hlinear htargets hcheckedTargetsNonempty
      hcheckedTargets htargetsChecked with
    ⟨checkedTargetTy, checkedTargetLifetime, htargetsCheckedType,
      htargetEqv, htargetLifetime⟩
  refine ⟨checkedTargetTy, checkedTargetLifetime, ?_, htargetEqv,
    htargetLifetime⟩
  simp [lvalType?, hchecked, htargetsCheckedType]

theorem lvalType?_type_complete_step
    {fuel : Nat} {env : FiniteEnv} {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      Linearizable env.toEnv →
        LValTyping env.toEnv lv partialTy lifetime →
          ∃ checkedTy checkedLifetime,
            lvalType? (fuel + 1) env lv =
                some (checkedTy, checkedLifetime) ∧
              PartialTy.eqv partialTy checkedTy ∧
                checkedLifetime = lifetime := by
  intro hcomplete hlinear htyping
  cases htyping with
  | var hslot =>
      rename_i name slot
      change env.lookup name = some slot at hslot
      refine ⟨slot.ty, slot.lifetime, ?_, PartialTy.eqv_refl _, rfl⟩
      simp [lvalType?, hslot]
  | box hsource =>
      rcases lvalType?_box_complete_step hcomplete hsource with
        ⟨checkedTy, checkedLifetime, hchecked, heqv, hlifetime⟩
      exact ⟨checkedTy, checkedLifetime, hchecked, heqv, hlifetime⟩
  | borrow hsource htargets =>
      exact lvalType?_borrow_type_complete_step hcomplete hlinear
        hsource htargets

theorem lvalType?_box_complete_step_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {lv : LVal}
    {inner : PartialTy} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      LValTyping env lv (.box inner) lifetime →
        ∃ checkedTy checkedLifetime,
          lvalType? (fuel + 1) finite (.deref lv) =
              some (checkedTy, checkedLifetime) ∧
            PartialTy.eqv inner checkedTy ∧
              checkedLifetime = lifetime := by
  intro hcomplete htyping
  rcases hcomplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, hlifetime⟩
  rcases partialTy_eqv_box_left_inv heqv with
    ⟨checkedInner, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  refine ⟨checkedInner, checkedLifetime, ?_, hcheckedEqv, hlifetime⟩
  simp [lvalType?, hchecked]

theorem lvalType?_borrow_type_complete_step_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {lv : LVal}
    {mutable : Bool} {targets : List LVal}
    {borrowLifetime targetLifetime : Lifetime} {targetTy : PartialTy} :
    LValCompleteAgainst fuel finite env →
      Linearizable env →
        LValTyping env lv (.ty (.borrow mutable targets)) borrowLifetime →
          LValTargetsTyping env targets targetTy targetLifetime →
            ∃ checkedTy checkedLifetime,
              lvalType? (fuel + 1) finite (.deref lv) =
                  some (checkedTy, checkedLifetime) ∧
                PartialTy.eqv targetTy checkedTy ∧
                  checkedLifetime = targetLifetime := by
  intro hcomplete hlinear hborrowTyping htargets
  rcases hcomplete hborrowTyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  rcases ty_eqv_borrow_left_inv hcheckedEqv with
    ⟨checkedTargets, hcheckedFullTy, htargetsChecked,
      hcheckedTargets⟩
  subst hcheckedFullTy
  have hcheckedTargetsNonempty : checkedTargets ≠ [] := by
    intro hnil
    cases targets with
    | nil =>
        exact LValTargetsTyping.nil_false htargets
    | cons target rest =>
        have htarget : target ∈ checkedTargets :=
          htargetsChecked (by simp)
        simp [hnil] at htarget
  rcases lvalTargetsType?_type_complete_of_lvalCompleteAgainst_subset
      hcomplete hlinear htargets hcheckedTargetsNonempty
      hcheckedTargets htargetsChecked with
    ⟨checkedTargetTy, checkedTargetLifetime, htargetsCheckedType,
      htargetEqv, htargetLifetime⟩
  refine ⟨checkedTargetTy, checkedTargetLifetime, ?_, htargetEqv,
    htargetLifetime⟩
  simp [lvalType?, hchecked, htargetsCheckedType]

theorem lvalType?_type_complete_step_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      Linearizable env →
        FiniteEnvEqv finite env →
          LValTyping env lv partialTy lifetime →
            ∃ checkedTy checkedLifetime,
              lvalType? (fuel + 1) finite lv =
                  some (checkedTy, checkedLifetime) ∧
                PartialTy.eqv partialTy checkedTy ∧
                  checkedLifetime = lifetime := by
  intro hcomplete hlinear heqv htyping
  cases htyping with
  | var hslot =>
      rename_i name slot
      rcases heqv.2 hslot with ⟨finiteSlot, hfiniteSlot, hslotEqv⟩
      refine
        ⟨finiteSlot.ty, finiteSlot.lifetime, ?_,
          PartialTy.eqv_symm hslotEqv.2, hslotEqv.1⟩
      simp [lvalType?, hfiniteSlot]
  | box hsource =>
      rcases lvalType?_box_complete_step_against hcomplete hsource with
        ⟨checkedTy, checkedLifetime, hchecked, heqvTy, hlifetime⟩
      exact ⟨checkedTy, checkedLifetime, hchecked, heqvTy, hlifetime⟩
  | borrow hsource htargets =>
      exact lvalType?_borrow_type_complete_step_against hcomplete hlinear
        hsource htargets

theorem LValCompleteAgainst.step
    {fuel : Nat} {finite : FiniteEnv} {env : Env} :
    LValCompleteAgainst fuel finite env →
      Linearizable env →
        FiniteEnvEqv finite env →
          LValCompleteAgainst (fuel + 1) finite env := by
  intro hcomplete hlinear heqv lv partialTy lifetime htyping
  exact lvalType?_type_complete_step_against hcomplete hlinear heqv htyping

theorem LValCompleteAgainst.mono
    {fuel bigger : Nat} {finite : FiniteEnv} {env : Env} :
    LValCompleteAgainst fuel finite env →
      Linearizable env →
        FiniteEnvEqv finite env →
          fuel ≤ bigger →
            LValCompleteAgainst bigger finite env := by
  intro hcomplete hlinear heqv hle
  induction hle with
  | refl =>
      exact hcomplete
  | step _ ih =>
      exact LValCompleteAgainst.step ih hlinear heqv

theorem targetsAllHaveTy?_complete
    {fuel : Nat} {env : FiniteEnv} {targets : List LVal} {ty : Ty} :
    (∀ target, target ∈ targets →
      ∃ lifetime, lvalType? fuel env target = some (.ty ty, lifetime)) →
      targetsAllHaveTy? fuel env ty targets = true := by
  intro htargets
  induction targets with
  | nil =>
      simp [targetsAllHaveTy?]
  | cons head rest ih =>
      rcases htargets head (by simp) with ⟨headLifetime, hhead⟩
      have hrest :
          ∀ target, target ∈ rest →
            ∃ lifetime, lvalType? fuel env target = some (.ty ty, lifetime) := by
        intro target htarget
        exact htargets target (by simp [htarget])
      simp [targetsAllHaveTy?, hhead, ih hrest]

theorem targetListCommonTy?_complete_nil
    {fuel : Nat} {env : FiniteEnv} :
    targetListCommonTy? fuel env [] = some none := by
  rfl

theorem targetListCommonTy?_complete_cons
    {fuel : Nat} {env : FiniteEnv} {head : LVal}
    {rest : List LVal} {ty : Ty} :
    (∀ target, target ∈ head :: rest →
      ∃ lifetime, lvalType? fuel env target = some (.ty ty, lifetime)) →
      targetListCommonTy? fuel env (head :: rest) = some (some ty) := by
  intro htargets
  rcases htargets head (by simp) with ⟨headLifetime, hhead⟩
  have hrest :
      ∀ target, target ∈ rest →
        ∃ lifetime, lvalType? fuel env target = some (.ty ty, lifetime) := by
    intro target htarget
    exact htargets target (by simp [htarget])
  simp [targetListCommonTy?, hhead, targetsAllHaveTy?_complete hrest]

theorem mutableLVal_box_complete_step
    {fuel : Nat} {env : FiniteEnv} {lv : LVal}
    {inner : PartialTy} {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      LValTyping env.toEnv lv (.box inner) lifetime →
        mutableLVal fuel env lv = true →
          mutableLVal (fuel + 1) env (.deref lv) = true := by
  intro hcomplete htyping hmutable
  rcases hcomplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_box_left_inv heqv with
    ⟨checkedInner, hcheckedTy, _hcheckedEqv⟩
  subst hcheckedTy
  simp [mutableLVal, hchecked, hmutable]

theorem mutableLVal_borrow_complete_step
    {fuel : Nat} {env : FiniteEnv} {lv : LVal}
    {targets : List LVal} {lifetime : Lifetime} :
    LValCompleteAt fuel env →
      LValTyping env.toEnv lv (.ty (.borrow true targets)) lifetime →
        (∀ target, target ∈ targets → mutableLVal fuel env target = true) →
          mutableLVal (fuel + 1) env (.deref lv) = true := by
  intro hcomplete htyping htargets
  rcases hcomplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  rcases ty_eqv_borrow_left_inv hcheckedEqv with
    ⟨checkedTargets, hcheckedFullTy, _htargetsChecked,
      hcheckedTargets⟩
  subst hcheckedFullTy
  simp [mutableLVal, hchecked]
  intro target htarget
  exact htargets target (hcheckedTargets htarget)

theorem mutableLVal_box_complete_step_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {lv : LVal}
    {inner : PartialTy} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      LValTyping env lv (.box inner) lifetime →
        mutableLVal fuel finite lv = true →
          mutableLVal (fuel + 1) finite (.deref lv) = true := by
  intro hcomplete htyping hmutable
  rcases hcomplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_box_left_inv heqv with
    ⟨checkedInner, hcheckedTy, _hcheckedEqv⟩
  subst hcheckedTy
  simp [mutableLVal, hchecked, hmutable]

theorem mutableLVal_borrow_complete_step_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {lv : LVal}
    {targets : List LVal} {lifetime : Lifetime} :
    LValCompleteAgainst fuel finite env →
      LValTyping env lv (.ty (.borrow true targets)) lifetime →
        (∀ target, target ∈ targets → mutableLVal fuel finite target = true) →
          mutableLVal (fuel + 1) finite (.deref lv) = true := by
  intro hcomplete htyping htargets
  rcases hcomplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  rcases ty_eqv_borrow_left_inv hcheckedEqv with
    ⟨checkedTargets, hcheckedFullTy, _htargetsChecked,
      hcheckedTargets⟩
  subst hcheckedFullTy
  simp [mutableLVal, hchecked]
  intro target htarget
  exact htargets target (hcheckedTargets htarget)

theorem MutableCompleteAgainst.step
    {fuel : Nat} {finite : FiniteEnv} {env : Env} :
    LValCompleteAgainst fuel finite env →
      MutableCompleteAgainst fuel finite env →
        FiniteEnvEqv finite env →
          MutableCompleteAgainst (fuel + 1) finite env := by
  intro hlvalComplete hmutableComplete heqv lv hmutable
  cases hmutable with
  | var hslot =>
      rcases heqv.2 hslot with ⟨finiteSlot, hfiniteSlot, _hslotEqv⟩
      simp [mutableLVal, hfiniteSlot]
  | box htyping hsourceMutable =>
      exact mutableLVal_box_complete_step_against hlvalComplete htyping
        (hmutableComplete hsourceMutable)
  | borrow htyping htargets =>
      exact mutableLVal_borrow_complete_step_against hlvalComplete htyping
        (by
          intro target htarget
          exact hmutableComplete (htargets target htarget))

theorem CompleteAgainst.mono
    {fuel bigger : Nat} {finite : FiniteEnv} {env : Env} :
    LValCompleteAgainst fuel finite env →
      MutableCompleteAgainst fuel finite env →
        Linearizable env →
          FiniteEnvEqv finite env →
            fuel ≤ bigger →
              LValCompleteAgainst bigger finite env ∧
                MutableCompleteAgainst bigger finite env := by
  intro hlval hmutable hlinear heqv hle
  induction hle with
  | refl =>
      exact ⟨hlval, hmutable⟩
  | step _ ih =>
      exact
        ⟨LValCompleteAgainst.step ih.1 hlinear heqv,
          MutableCompleteAgainst.step ih.1 ih.2 heqv⟩

theorem strike?_complete {path : Path} {source struck : PartialTy} :
    Strike path source struck → strike? path source = some struck := by
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike, strike?]
  | cons _ rest ih =>
      cases source <;> cases struck <;> simp [Strike, strike?]
      intro h
      have hrec := ih h
      simp [hrec]

theorem strike?_complete_of_eqv
    {path : Path} {sourceFinite sourceDecl struckDecl : PartialTy} :
    PartialTy.eqv sourceFinite sourceDecl →
      Strike path sourceDecl struckDecl →
        ∃ struckFinite,
          strike? path sourceFinite = some struckFinite ∧
            PartialTy.eqv struckFinite struckDecl := by
  induction path generalizing sourceFinite sourceDecl struckDecl with
  | nil =>
      intro heqv hstrike
      cases sourceDecl <;> cases struckDecl <;> simp [Strike] at hstrike
      rename_i declTy struckTy
      subst hstrike
      cases sourceFinite <;> simp [PartialTy.eqv] at heqv
      rename_i finiteTy
      exact ⟨.undef finiteTy, by simp [strike?], heqv⟩
  | cons _ rest ih =>
      intro heqv hstrike
      cases sourceDecl <;> cases struckDecl <;> simp [Strike] at hstrike
      rename_i declInner struckInner
      cases sourceFinite <;> simp [PartialTy.eqv] at heqv
      rename_i finiteInner
      rcases ih heqv hstrike with
        ⟨struckFiniteInner, hstruck, hstruckEqv⟩
      exact ⟨.box struckFiniteInner, by simp [strike?, hstruck], hstruckEqv⟩

theorem envMove?_complete {env : FiniteEnv} {lv : LVal} {moved : Env} :
    EnvMove env.toEnv lv moved →
      ∃ movedFinite,
        envMove? env lv = some movedFinite ∧ movedFinite.toEnv = moved := by
  intro hmove
  rcases hmove with ⟨slot, struck, hslot, hstrike, rfl⟩
  change env.lookup (LVal.base lv) = some slot at hslot
  refine ⟨env.update (LVal.base lv) { slot with ty := struck }, ?_, ?_⟩
  · simp [envMove?, hslot, strike?_complete hstrike]
  · simp [FiniteEnv.toEnv_update]

theorem envMove?_complete_against
    {finite : FiniteEnv} {env moved : Env} {lv : LVal} :
    FiniteEnvEqv finite env →
      EnvMove env lv moved →
        ∃ movedFinite,
          envMove? finite lv = some movedFinite ∧
            FiniteEnvEqv movedFinite moved := by
  intro heqv hmove
  rcases hmove with ⟨envSlot, struckDecl, henvSlot, hstrike, hmoved⟩
  rcases heqv.2 henvSlot with ⟨finiteSlot, hfiniteSlot, hslotEqv⟩
  rcases strike?_complete_of_eqv hslotEqv.2 hstrike with
    ⟨struckFinite, hstruckFinite, hstruckEqv⟩
  subst hmoved
  refine
    ⟨finite.update (LVal.base lv) { finiteSlot with ty := struckFinite },
      ?_, ?_⟩
  · simp [envMove?, hfiniteSlot, hstruckFinite]
  · exact finiteEnvEqv_update heqv
      (show EnvSlotEqv { finiteSlot with ty := struckFinite }
          { envSlot with ty := struckDecl } from
        ⟨by simp [hslotEqv.1], hstruckEqv⟩)

theorem updateAtPath?_complete_strong
    {fuel : Nat} {env : FiniteEnv} {oldTy : PartialTy} {rhsTy : Ty} :
    0 < fuel →
      updateAtPath? fuel 0 env [] oldTy rhsTy = some (env, .ty rhsTy) := by
  intro hfuel
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      simp [updateAtPath?]

theorem envWrite?_complete_var_strong
    {fuel : Nat} {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {rhsTy : Ty} :
    0 < fuel →
      env.lookup name = some slot →
        envWrite? fuel 0 env (.var name) rhsTy =
          some (env.update name { slot with ty := .ty rhsTy }) := by
  intro hfuel hslot
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      simp [envWrite?, updateAtPath?, LVal.base, LVal.path, hslot]

theorem envWrite?_complete_of_updateAtPath?_eqv
    {fuel rank : Nat} {finite updatedFinite : FiniteEnv}
    {env updatedEnv : Env} {lv : LVal} {finiteSlot envSlot : EnvSlot}
    {updatedFiniteTy updatedDeclTy : PartialTy}
    {rhsCheckedTy : Ty} :
    FiniteEnvEqv finite env →
      finite.lookup (LVal.base lv) = some finiteSlot →
        env.slotAt (LVal.base lv) = some envSlot →
          updateAtPath? fuel rank finite (LVal.path lv) finiteSlot.ty
              rhsCheckedTy =
            some (updatedFinite, updatedFiniteTy) →
            FiniteEnvEqv updatedFinite updatedEnv →
              EnvSlotEqv { finiteSlot with ty := updatedFiniteTy }
                { envSlot with ty := updatedDeclTy } →
                ∃ writtenFinite,
                  envWrite? fuel rank finite lv rhsCheckedTy =
                    some writtenFinite ∧
                  FiniteEnvEqv writtenFinite
                    (updatedEnv.update (LVal.base lv)
                      { envSlot with ty := updatedDeclTy }) := by
  intro _heqv hfiniteSlot _henvSlot hupdate heqvUpdated hslotEqv
  refine
    ⟨updatedFinite.update (LVal.base lv)
        { finiteSlot with ty := updatedFiniteTy }, ?_, ?_⟩
  · simp [envWrite?, hfiniteSlot, hupdate]
  · exact finiteEnvEqv_update heqvUpdated hslotEqv

theorem envWrite?_complete_var_strong_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {name : Name}
    {envSlot : EnvSlot} {rhsCheckedTy rhsDeclTy : Ty} :
    0 < fuel →
      FiniteEnvEqv finite env →
        env.slotAt name = some envSlot →
          Ty.eqv rhsCheckedTy rhsDeclTy →
            ∃ writtenFinite,
              envWrite? fuel 0 finite (.var name) rhsCheckedTy =
                some writtenFinite ∧
              FiniteEnvEqv writtenFinite
                (env.update name { envSlot with ty := .ty rhsDeclTy }) := by
  intro hfuel heqv henvSlot htyEqv
  rcases heqv.2 henvSlot with ⟨finiteSlot, hfiniteSlot, hslotEqv⟩
  refine
    ⟨finite.update name { finiteSlot with ty := .ty rhsCheckedTy },
      envWrite?_complete_var_strong hfuel hfiniteSlot, ?_⟩
  exact finiteEnvEqv_update heqv
    (show EnvSlotEqv
        { finiteSlot with ty := .ty rhsCheckedTy }
        { envSlot with ty := .ty rhsDeclTy } from
      ⟨by simp [hslotEqv.1], htyEqv⟩)

theorem checkTerm?_complete_const {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    0 < fuel →
      ValueTyping typing value ty →
        checkTerm? fuel env typing lifetime (.val value) =
          .ok { ty := ty, env := env } := by
  intro hfuel htyping
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      simp [checkTerm?, valueTy?_complete htyping]

theorem checkTerm?_complete_const_eqv
    {fuel : Nat} {finite : FiniteEnv} {env : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    0 < fuel →
      FiniteEnvEqv finite env →
        ValueTyping typing value ty →
          ∃ result,
            checkTerm? fuel finite typing lifetime (.val value) =
              .ok result ∧
            Ty.eqv result.ty ty ∧
              FiniteEnvEqv result.env env := by
  intro hfuel heqv htyping
  refine ⟨{ ty := ty, env := finite }, ?_, Ty.eqv_refl ty, heqv⟩
  exact checkTerm?_complete_const hfuel htyping

theorem borrowCheck?_complete_val {value : Value} :
    borrowCheck (.val value) →
      borrowCheck? (termCheckerFuelBound (.val value)) (.val value) = true := by
  rintro ⟨ty, env, htyping⟩
  cases htyping with
  | const hvalue =>
      unfold borrowCheck? borrowCheckVerdict? checkProgram?
      simp [termCheckerFuelBound, checkTerm?, valueTy?_complete hvalue]

end BasicReflectionCompleteness

section BorrowProhibitionCompleteness

mutual
  theorem tyContainsBorrow_of_mem :
      ∀ {ty : Ty} {mutable : Bool} {targets : List LVal},
        (mutable, targets) ∈ tyBorrows ty →
          PartialTyContains (.ty ty) (.borrow mutable targets) := by
    intro ty mutable targets h
    cases ty with
    | unit =>
        simp [tyBorrows] at h
    | int =>
        simp [tyBorrows] at h
    | bool =>
        simp [tyBorrows] at h
    | borrow borrowMutable borrowTargets =>
        simp [tyBorrows] at h
        rcases h with ⟨rfl, rfl⟩
        exact PartialTyContains.here
    | box inner =>
        exact PartialTyContains.tyBox
          (tyContainsBorrow_of_mem (by simpa [tyBorrows] using h))

  theorem partialTyContainsBorrow_of_mem :
      ∀ {partialTy : PartialTy} {mutable : Bool} {targets : List LVal},
        (mutable, targets) ∈ partialTyBorrows partialTy →
          PartialTyContains partialTy (.borrow mutable targets) := by
    intro partialTy mutable targets h
    cases partialTy with
    | ty ty =>
        exact tyContainsBorrow_of_mem h
    | box inner =>
        exact PartialTyContains.box
          (partialTyContainsBorrow_of_mem
            (by simpa [partialTyBorrows] using h))
    | undef ty =>
        simp [partialTyBorrows] at h
end

theorem partialTyContainsBorrow_mem_aux {partialTy : PartialTy}
    {needle : Ty}
    (hcontains : PartialTyContains partialTy needle) :
    ∀ {mutable : Bool} {targets : List LVal},
      needle = .borrow mutable targets →
        (mutable, targets) ∈ partialTyBorrows partialTy := by
  induction hcontains with
  | here =>
      intro mutable targets hneedle
      cases hneedle
      simp [partialTyBorrows, tyBorrows]
  | tyBox _ ih =>
      intro mutable targets hneedle
      simpa [partialTyBorrows, tyBorrows] using ih hneedle
  | box _ ih =>
      intro mutable targets hneedle
      simpa [partialTyBorrows] using ih hneedle

theorem partialTyContainsBorrow_mem {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyContains partialTy (.borrow mutable targets) →
      (mutable, targets) ∈ partialTyBorrows partialTy := by
  intro hcontains
  exact partialTyContainsBorrow_mem_aux hcontains rfl

theorem containedBorrowsWellFormed_complete
    {fuel : Nat} {env : FiniteEnv} :
    FiniteEnv.EntriesReflectLookup env →
      LValCompleteAt fuel env →
        ContainedBorrowsWellFormed env.toEnv →
          containedBorrowsWellFormed fuel env = true := by
  intro hreflect hcomplete hcontained
  unfold containedBorrowsWellFormed
  exact List.all_eq_true.mpr (by
    intro entry hentry
    rcases entry with ⟨name, slot⟩
    exact List.all_eq_true.mpr (by
      intro borrow hborrow
      rcases borrow with ⟨mutable, targets⟩
      have hslot : env.toEnv.slotAt name = some slot := by
        change env.lookup name = some slot
        exact hreflect hentry
      have hcontains :
          env.toEnv ⊢ name ↝ Ty.borrow mutable targets :=
        ⟨slot, hslot, partialTyContainsBorrow_of_mem hborrow⟩
      exact borrowTargetsWellFormedInSlot_complete hcomplete
        (hcontained name slot mutable targets hslot hcontains)))

theorem containedBorrowsWellFormed_complete_against
    {fuel : Nat} {finite : FiniteEnv} {env : Env} :
    FiniteEnv.EntriesReflectLookup finite →
      LValCompleteAgainst fuel finite env →
        FiniteEnvEqv finite env →
          ContainedBorrowsWellFormed env →
            containedBorrowsWellFormed fuel finite = true := by
  intro hreflect hcomplete heqv hcontained
  unfold containedBorrowsWellFormed
  exact List.all_eq_true.mpr (by
    intro entry hentry
    rcases entry with ⟨name, slot⟩
    exact List.all_eq_true.mpr (by
      intro borrow hborrow
      rcases borrow with ⟨mutable, targets⟩
      have hslot : finite.lookup name = some slot :=
        hreflect hentry
      rcases heqv.1 hslot with ⟨envSlot, henvSlot, hslotEqv⟩
      have hcontainsFiniteSlot :
          PartialTyContains slot.ty (.borrow mutable targets) :=
        partialTyContainsBorrow_of_mem hborrow
      rcases partialTyContains_borrow_of_eqv_left hslotEqv.2
          hcontainsFiniteSlot with
        ⟨envTargets, hcontainsEnvSlot, hsubset⟩
      have hcontainsEnv :
          env ⊢ name ↝ Ty.borrow mutable envTargets :=
        ⟨envSlot, henvSlot, hcontainsEnvSlot⟩
      have htargets :
          BorrowTargetsWellFormedInSlot env envSlot.lifetime targets :=
        borrowTargetsWellFormedInSlot_of_subset
          (hcontained name envSlot mutable envTargets henvSlot hcontainsEnv)
          hsubset
      have hslotLifetime : slot.lifetime = envSlot.lifetime := hslotEqv.1
      simpa [hslotLifetime] using
        (borrowTargetsWellFormedInSlot_complete_against
          hcomplete heqv htargets)))

theorem wellFormedKit_complete_against_of_coherent_linearizable
    {fuel : Nat} {finite : FiniteEnv} {env : Env} :
    FiniteEnv.EntriesReflectLookup finite →
      LValCompleteAgainst fuel finite env →
        FiniteEnvEqv finite env →
          ContainedBorrowsWellFormed env →
            coherent fuel finite = true →
              linearizable finite = true →
                wellFormedKit fuel finite = true := by
  intro hreflect hcomplete heqv hcontained hcoherent hlinear
  have hcontainedCheck :
      containedBorrowsWellFormed fuel finite = true :=
    containedBorrowsWellFormed_complete_against hreflect hcomplete heqv
      hcontained
  simp [wellFormedKit, hcontainedCheck, hcoherent, hlinear]

mutual
  def TyCoherentCompleteWitness : Nat → Env → Ty → Prop
    | _, _, .unit => True
    | _, _, .int => True
    | _, _, .bool => True
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner =>
        TyCoherentCompleteWitness fuel env inner
    | 0, _, .borrow _ _ => False
    | fuel + 1, env, .borrow _ targets =>
        ∃ targetTy targetLifetime,
          LValTargetsTyping env targets (.ty targetTy) targetLifetime ∧
            TyCoherentCompleteWitness fuel env targetTy

  def PartialTyCoherentCompleteWitness : Nat → Env → PartialTy → Prop
    | fuel, env, .ty ty => TyCoherentCompleteWitness fuel env ty
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner =>
        PartialTyCoherentCompleteWitness fuel env inner
    | _, _, .undef _ => True
end

theorem coherentCompleteWitness_of_eqv_left (fuel : Nat) :
    (∀ {env : Env} {left right : Ty},
      Linearizable env →
        Ty.eqv left right →
          TyCoherentCompleteWitness fuel env right →
            TyCoherentCompleteWitness fuel env left) ∧
    (∀ {env : Env} {left right : PartialTy},
      Linearizable env →
        PartialTy.eqv left right →
          PartialTyCoherentCompleteWitness fuel env right →
            PartialTyCoherentCompleteWitness fuel env left) := by
  induction fuel with
  | zero =>
      constructor
      · intro env left right _hlinear heqv hwitness
        cases left <;> cases right <;>
          simp [Ty.eqv, TyCoherentCompleteWitness] at heqv hwitness ⊢
      · intro env left right _hlinear heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                cases leftTy <;> cases rightTy <;>
                  simp [PartialTy.eqv, Ty.eqv,
                    PartialTyCoherentCompleteWitness,
                    TyCoherentCompleteWitness] at heqv hwitness ⊢
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right with
            | box rightInner =>
                simp [PartialTy.eqv, PartialTyCoherentCompleteWitness] at heqv hwitness
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | undef leftTy =>
            cases right with
            | undef rightTy =>
                simp [PartialTyCoherentCompleteWitness]
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | box _ =>
                simp [PartialTy.eqv] at heqv
  | succ fuel ih =>
      have hty :
          ∀ {env : Env} {left right : Ty},
            Linearizable env →
              Ty.eqv left right →
                TyCoherentCompleteWitness (fuel + 1) env right →
                  TyCoherentCompleteWitness (fuel + 1) env left := by
        intro env left right hlinear heqv hwitness
        cases left with
        | unit =>
            cases right <;>
              simp [Ty.eqv, TyCoherentCompleteWitness] at heqv hwitness ⊢
        | int =>
            cases right <;>
              simp [Ty.eqv, TyCoherentCompleteWitness] at heqv hwitness ⊢
        | bool =>
            cases right <;>
              simp [Ty.eqv, TyCoherentCompleteWitness] at heqv hwitness ⊢
        | box leftInner =>
            cases right with
            | box rightInner =>
                exact ih.1 hlinear
                  (by simpa [Ty.eqv] using heqv)
                  (by simpa [TyCoherentCompleteWitness] using hwitness)
            | unit =>
                simp [Ty.eqv] at heqv
            | int =>
                simp [Ty.eqv] at heqv
            | borrow _ _ =>
                simp [Ty.eqv] at heqv
            | bool =>
                simp [Ty.eqv] at heqv
        | borrow leftMutable leftTargets =>
            cases right with
            | borrow rightMutable rightTargets =>
                rcases (by simpa [Ty.eqv] using heqv) with
                  ⟨hmutable, hleftRight, hrightLeft⟩
                subst hmutable
                have hwitnessBorrow :
                    ∃ targetTy targetLifetime,
                      LValTargetsTyping env rightTargets (.ty targetTy)
                        targetLifetime ∧
                        TyCoherentCompleteWitness fuel env targetTy := by
                  simpa [TyCoherentCompleteWitness] using hwitness
                rcases hwitnessBorrow with
                  ⟨targetTy, targetLifetime, htargets, htargetWitness⟩
                have hleftNonempty : leftTargets ≠ [] := by
                  intro hnil
                  cases rightTargets with
                  | nil =>
                      exact LValTargetsTyping.nil_false htargets
                  | cons head tail =>
                      have hmem : head ∈ leftTargets :=
                        hrightLeft (by simp)
                      simp [hnil] at hmem
                rcases lvalTargetsTyping_of_nonempty_subset htargets
                    hleftNonempty hleftRight with
                  ⟨leftTargetTy, leftTargetLifetime, hleftTargets,
                    _hstrength, _houtlives⟩
                rcases hlinear with ⟨φ, hφ⟩
                have hdet :
                    ∀ {lv : LVal} {left right : Ty}
                      {leftLifetime rightLifetime : Lifetime},
                      LValTyping env lv (.ty left) leftLifetime →
                      LValTyping env lv (.ty right) rightLifetime →
                        PartialTy.eqv (.ty left) (.ty right) := by
                  intro lv left right leftLifetime rightLifetime hleft hright
                  exact lvalTyping_eqv_of_linearizedBy hφ hleft hright
                have htargetEqv :
                    PartialTy.eqv (.ty leftTargetTy) (.ty targetTy) :=
                  lvalTargetsTyping_eqv_of_subset_of_lval_eqv hdet
                    hleftTargets htargets hleftRight hrightLeft
                have htargetEqvTy : Ty.eqv leftTargetTy targetTy := by
                  simpa [PartialTy.eqv] using htargetEqv
                refine ⟨leftTargetTy, leftTargetLifetime, hleftTargets, ?_⟩
                exact ih.1 ⟨φ, hφ⟩ htargetEqvTy htargetWitness
            | unit =>
                simp [Ty.eqv] at heqv
            | int =>
                simp [Ty.eqv] at heqv
            | box _ =>
                simp [Ty.eqv] at heqv
            | bool =>
                simp [Ty.eqv] at heqv
      have hpartial :
          ∀ {env : Env} {left right : PartialTy},
            Linearizable env →
              PartialTy.eqv left right →
                PartialTyCoherentCompleteWitness (fuel + 1) env right →
                  PartialTyCoherentCompleteWitness (fuel + 1) env left := by
        intro env left right hlinear heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                exact hty hlinear
                  (by simpa [PartialTy.eqv] using heqv)
                  (by simpa [PartialTyCoherentCompleteWitness] using hwitness)
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right with
            | box rightInner =>
                exact ih.2 hlinear
                  (by simpa [PartialTy.eqv] using heqv)
                  (by simpa [PartialTyCoherentCompleteWitness] using hwitness)
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | undef leftTy =>
            cases right with
            | undef rightTy =>
                trivial
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | box _ =>
                simp [PartialTy.eqv] at heqv
      exact ⟨hty, hpartial⟩

theorem tyCoherentCompleteWitness_of_eqv_left
    {fuel : Nat} {env : Env} {left right : Ty} :
    Linearizable env →
      Ty.eqv left right →
        TyCoherentCompleteWitness fuel env right →
          TyCoherentCompleteWitness fuel env left :=
  (coherentCompleteWitness_of_eqv_left fuel).1

theorem partialTyCoherentCompleteWitness_of_eqv_left
    {fuel : Nat} {env : Env} {left right : PartialTy} :
    Linearizable env →
      PartialTy.eqv left right →
        PartialTyCoherentCompleteWitness fuel env right →
          PartialTyCoherentCompleteWitness fuel env left :=
  (coherentCompleteWitness_of_eqv_left fuel).2

theorem coherentCompleteWitness_complete_against (fuel : Nat) :
    (∀ {finite : FiniteEnv} {env : Env} {ty checkedTy : Ty},
      (∀ smaller, smaller < fuel → LValCompleteAgainst smaller finite env) →
        Linearizable env →
          Ty.eqv checkedTy ty →
            TyCoherentCompleteWitness fuel env ty →
              tyCoherent fuel finite checkedTy = true) ∧
    (∀ {finite : FiniteEnv} {env : Env}
        {partialTy checkedPartialTy : PartialTy},
      (∀ smaller, smaller < fuel → LValCompleteAgainst smaller finite env) →
        Linearizable env →
          PartialTy.eqv checkedPartialTy partialTy →
            PartialTyCoherentCompleteWitness fuel env partialTy →
              partialTyCoherent fuel finite checkedPartialTy = true) := by
  induction fuel with
  | zero =>
      constructor
      · intro finite env ty checkedTy _hcomplete _hlinear heqv hwitness
        cases checkedTy <;> cases ty <;>
          simp [Ty.eqv, TyCoherentCompleteWitness, tyCoherent] at heqv hwitness ⊢
      · intro finite env partialTy checkedPartialTy _hcomplete _hlinear heqv
          hwitness
        cases checkedPartialTy with
        | ty checkedTy =>
            cases partialTy with
            | ty ty =>
                cases checkedTy <;> cases ty <;>
                  simp [PartialTy.eqv, Ty.eqv,
                    PartialTyCoherentCompleteWitness,
                    TyCoherentCompleteWitness, partialTyCoherent,
                    tyCoherent] at heqv hwitness ⊢
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box checkedInner =>
            cases partialTy with
            | box inner =>
                simp [PartialTy.eqv, PartialTyCoherentCompleteWitness] at heqv hwitness
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | undef checkedTy =>
            cases partialTy with
            | undef ty =>
                simp [partialTyCoherent]
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | box _ =>
                simp [PartialTy.eqv] at heqv
  | succ fuel ih =>
      have hty :
          ∀ {finite : FiniteEnv} {env : Env} {ty checkedTy : Ty},
            (∀ smaller, smaller < fuel + 1 →
              LValCompleteAgainst smaller finite env) →
              Linearizable env →
                Ty.eqv checkedTy ty →
                  TyCoherentCompleteWitness (fuel + 1) env ty →
                    tyCoherent (fuel + 1) finite checkedTy = true := by
        intro finite env ty checkedTy hcomplete hlinear heqv hwitness
        cases checkedTy with
        | unit =>
            cases ty <;>
              simp [Ty.eqv, TyCoherentCompleteWitness, tyCoherent] at heqv hwitness ⊢
        | int =>
            cases ty <;>
              simp [Ty.eqv, TyCoherentCompleteWitness, tyCoherent] at heqv hwitness ⊢
        | borrow checkedMutable checkedTargets =>
            cases ty with
            | borrow mutable targets =>
                rcases (by simpa [Ty.eqv] using heqv) with
                  ⟨hmutable, hcheckedTargets, htargetsChecked⟩
                subst hmutable
                have hwitnessBorrow :
                    ∃ targetTy targetLifetime,
                      LValTargetsTyping env targets (.ty targetTy)
                        targetLifetime ∧
                        TyCoherentCompleteWitness fuel env targetTy := by
                  simpa [TyCoherentCompleteWitness] using hwitness
                rcases hwitnessBorrow with
                  ⟨targetTy, targetLifetime, hwitnessTargets⟩
                rcases hwitnessTargets with ⟨htargets, htargetWitness⟩
                have hcheckedNonempty : checkedTargets ≠ [] := by
                  intro hnil
                  cases targets with
                  | nil =>
                      exact LValTargetsTyping.nil_false htargets
                  | cons head tail =>
                      have hmem : head ∈ checkedTargets :=
                        htargetsChecked (by simp)
                      simp [hnil] at hmem
                have hcompleteTargets :
                    LValCompleteAgainst fuel finite env :=
                  hcomplete fuel (Nat.lt_succ_self fuel)
                rcases
                    lvalTargetsType?_type_complete_of_lvalCompleteAgainst_subset
                      hcompleteTargets hlinear htargets hcheckedNonempty
                      hcheckedTargets htargetsChecked with
                  ⟨checkedTargetPartial, checkedTargetLifetime,
                    hcheckedTargetsType, htargetEqv, _htargetLifetime⟩
                rcases partialTy_eqv_ty_left_inv htargetEqv with
                  ⟨checkedTargetTy, hcheckedTargetPartial, htargetTyEqv⟩
                subst hcheckedTargetPartial
                have hcompleteTargetTy :
                    ∀ smaller, smaller < fuel →
                      LValCompleteAgainst smaller finite env := by
                  intro smaller hlt
                  exact hcomplete smaller
                    (Nat.lt_trans hlt (Nat.lt_succ_self fuel))
                have htargetCoherent :
                    tyCoherent fuel finite checkedTargetTy = true :=
                  ih.1 hcompleteTargetTy hlinear
                    (Ty.eqv_symm htargetTyEqv) htargetWitness
                simp [tyCoherent, hcheckedTargetsType, htargetCoherent]
            | unit =>
                simp [Ty.eqv] at heqv
            | int =>
                simp [Ty.eqv] at heqv
            | box _ =>
                simp [Ty.eqv] at heqv
            | bool =>
                simp [Ty.eqv] at heqv
        | box checkedInner =>
            cases ty with
            | box inner =>
                have hcompleteInner :
                    ∀ smaller, smaller < fuel →
                      LValCompleteAgainst smaller finite env := by
                  intro smaller hlt
                  exact hcomplete smaller
                    (Nat.lt_trans hlt (Nat.lt_succ_self fuel))
                exact ih.1 hcompleteInner hlinear
                  (by simpa [Ty.eqv] using heqv)
                  (by
                    simpa [TyCoherentCompleteWitness] using hwitness)
            | unit =>
                simp [Ty.eqv] at heqv
            | int =>
                simp [Ty.eqv] at heqv
            | borrow _ _ =>
                simp [Ty.eqv] at heqv
            | bool =>
                simp [Ty.eqv] at heqv
        | bool =>
            cases ty <;>
              simp [Ty.eqv, TyCoherentCompleteWitness, tyCoherent] at heqv hwitness ⊢
      have hpartial :
          ∀ {finite : FiniteEnv} {env : Env}
              {partialTy checkedPartialTy : PartialTy},
            (∀ smaller, smaller < fuel + 1 →
              LValCompleteAgainst smaller finite env) →
              Linearizable env →
                PartialTy.eqv checkedPartialTy partialTy →
                  PartialTyCoherentCompleteWitness (fuel + 1) env partialTy →
                    partialTyCoherent (fuel + 1) finite checkedPartialTy = true := by
        intro finite env partialTy checkedPartialTy hcomplete hlinear heqv
          hwitness
        cases checkedPartialTy with
        | ty checkedTy =>
            cases partialTy with
            | ty ty =>
                exact hty hcomplete hlinear
                  (by simpa [PartialTy.eqv] using heqv)
                  (by
                    simpa [PartialTyCoherentCompleteWitness] using hwitness)
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box checkedInner =>
            cases partialTy with
            | box inner =>
                have hcompleteInner :
                    ∀ smaller, smaller < fuel →
                      LValCompleteAgainst smaller finite env := by
                  intro smaller hlt
                  exact hcomplete smaller
                    (Nat.lt_trans hlt (Nat.lt_succ_self fuel))
                exact ih.2 hcompleteInner hlinear
                  (by simpa [PartialTy.eqv] using heqv)
                  (by
                    simpa [PartialTyCoherentCompleteWitness] using hwitness)
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | undef checkedTy =>
            cases partialTy with
            | undef ty =>
                simp [partialTyCoherent]
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | box _ =>
                simp [PartialTy.eqv] at heqv
      exact ⟨hty, hpartial⟩

def CoherentCompleteWitness (fuel : Nat) (env : Env) : Prop :=
  ∀ {name : Name} {slot : EnvSlot},
    env.slotAt name = some slot →
      PartialTyCoherentCompleteWitness fuel env slot.ty

theorem coherentCompleteWitness_update_fresh_aux (fuel : Nat) :
    (∀ {env : Env} {name : Name} {slot : EnvSlot} {ty : Ty},
      env.fresh name →
        TyCoherentCompleteWitness fuel env ty →
          TyCoherentCompleteWitness fuel (env.update name slot) ty) ∧
    (∀ {env : Env} {name : Name} {slot : EnvSlot} {partialTy : PartialTy},
      env.fresh name →
        PartialTyCoherentCompleteWitness fuel env partialTy →
          PartialTyCoherentCompleteWitness fuel (env.update name slot)
            partialTy) := by
  induction fuel with
  | zero =>
      constructor
      · intro env name slot ty hfresh hwitness
        cases ty <;> simp [TyCoherentCompleteWitness] at hwitness ⊢
      · intro env name slot partialTy hfresh hwitness
        cases partialTy with
        | ty ty =>
            cases ty <;>
              simp [PartialTyCoherentCompleteWitness,
                TyCoherentCompleteWitness] at hwitness ⊢
        | box inner =>
            simp [PartialTyCoherentCompleteWitness] at hwitness
        | undef shape =>
            simp [PartialTyCoherentCompleteWitness]
  | succ fuel ih =>
      have hty :
          ∀ {env : Env} {name : Name} {slot : EnvSlot} {ty : Ty},
            env.fresh name →
              TyCoherentCompleteWitness (fuel + 1) env ty →
                TyCoherentCompleteWitness (fuel + 1)
                  (env.update name slot) ty := by
        intro env name slot ty hfresh hwitness
        cases ty with
        | unit =>
            trivial
        | int =>
            trivial
        | bool =>
            trivial
        | box inner =>
            exact ih.1 hfresh
              (by simpa [TyCoherentCompleteWitness] using hwitness)
        | borrow mutable targets =>
            have hwitnessBorrow :
                ∃ targetTy targetLifetime,
                  LValTargetsTyping env targets (.ty targetTy) targetLifetime ∧
                    TyCoherentCompleteWitness fuel env targetTy := by
              simpa [TyCoherentCompleteWitness] using hwitness
            rcases hwitnessBorrow with
              ⟨targetTy, targetLifetime, htargets, htargetWitness⟩
            refine ⟨targetTy, targetLifetime, ?_, ?_⟩
            · exact LValTargetsTyping.update_fresh (slot := slot) hfresh htargets
            · exact ih.1 hfresh htargetWitness
      have hpartial :
          ∀ {env : Env} {name : Name} {slot : EnvSlot}
              {partialTy : PartialTy},
            env.fresh name →
              PartialTyCoherentCompleteWitness (fuel + 1) env partialTy →
                PartialTyCoherentCompleteWitness (fuel + 1)
                  (env.update name slot) partialTy := by
        intro env name slot partialTy hfresh hwitness
        cases partialTy with
        | ty ty =>
            exact hty
              hfresh (by
                simpa [PartialTyCoherentCompleteWitness] using hwitness)
        | box inner =>
            exact ih.2 hfresh
              (by simpa [PartialTyCoherentCompleteWitness] using hwitness)
        | undef shape =>
            trivial
      exact ⟨hty, hpartial⟩

theorem tyCoherentCompleteWitness_update_fresh
    {fuel : Nat} {env : Env} {name : Name} {slot : EnvSlot} {ty : Ty} :
    env.fresh name →
      TyCoherentCompleteWitness fuel env ty →
        TyCoherentCompleteWitness fuel (env.update name slot) ty :=
  (coherentCompleteWitness_update_fresh_aux fuel).1

theorem partialTyCoherentCompleteWitness_update_fresh
    {fuel : Nat} {env : Env} {name : Name} {slot : EnvSlot}
    {partialTy : PartialTy} :
    env.fresh name →
      PartialTyCoherentCompleteWitness fuel env partialTy →
        PartialTyCoherentCompleteWitness fuel (env.update name slot)
          partialTy :=
  (coherentCompleteWitness_update_fresh_aux fuel).2

theorem coherentCompleteWitness_update_fresh_ty
    {fuel : Nat} {env : Env} {name : Name}
    {ty : Ty} {lifetime : Lifetime} :
    env.fresh name →
      CoherentCompleteWitness fuel env →
        TyCoherentCompleteWitness fuel env ty →
          CoherentCompleteWitness fuel
            (env.update name { ty := .ty ty, lifetime := lifetime }) := by
  intro hfresh hwitness htyWitness slotName slot hslot
  by_cases hslotName : slotName = name
  · subst hslotName
    have hslotEq :
        slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    exact partialTyCoherentCompleteWitness_update_fresh
      (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
      (by simpa [PartialTyCoherentCompleteWitness] using htyWitness)
  · have hslotOld : env.slotAt slotName = some slot := by
      simpa [Env.update, hslotName] using hslot
    exact partialTyCoherentCompleteWitness_update_fresh
      (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
      (hwitness hslotOld)

theorem coherentCompleteWitness_update_fresh_ty_of_eqv_left
    {fuel : Nat} {env : Env} {name : Name}
    {checkedTy declTy : Ty} {lifetime : Lifetime} :
    Linearizable env →
      env.fresh name →
        CoherentCompleteWitness fuel env →
          Ty.eqv checkedTy declTy →
            TyCoherentCompleteWitness fuel env declTy →
              CoherentCompleteWitness fuel
                (env.update name
                  { ty := .ty checkedTy, lifetime := lifetime }) := by
  intro hlinear hfresh hwitness htyEqv htyWitness
  exact coherentCompleteWitness_update_fresh_ty hfresh hwitness
    (tyCoherentCompleteWitness_of_eqv_left hlinear htyEqv htyWitness)

theorem coherent_complete_against_of_witness
    {fuel : Nat} {finite : FiniteEnv} {env : Env} :
    FiniteEnv.EntriesReflectLookup finite →
      FiniteEnvEqv finite env →
        (∀ smaller, smaller < fuel →
          LValCompleteAgainst smaller finite env) →
          Linearizable env →
            CoherentCompleteWitness fuel env →
              coherent fuel finite = true := by
  intro hreflect heqv hcomplete hlinear hwitness
  unfold coherent
  exact List.all_eq_true.mpr (by
    intro entry hentry
    rcases entry with ⟨name, slot⟩
    have hlookup : finite.lookup name = some slot :=
      hreflect hentry
    rcases heqv.1 hlookup with ⟨envSlot, henvSlot, hslotEqv⟩
    exact (coherentCompleteWitness_complete_against fuel).2
      hcomplete hlinear hslotEqv.2 (hwitness henvSlot))

theorem wellFormedKit_complete_against_of_witness
    {fuel : Nat} {finite : FiniteEnv} {env : Env} :
    FiniteEnv.EntriesReflectLookup finite →
      FiniteEnvEqv finite env →
        (∀ smaller, smaller ≤ fuel →
          LValCompleteAgainst smaller finite env) →
          Linearizable env →
            ContainedBorrowsWellFormed env →
              CoherentCompleteWitness fuel env →
                linearizable finite = true →
                  wellFormedKit fuel finite = true := by
  intro hreflect heqv hcomplete hlinear hcontained hcoherentWitness
    hlinearCheck
  have hcontainedCheck :
      containedBorrowsWellFormed fuel finite = true :=
    containedBorrowsWellFormed_complete_against hreflect
      (hcomplete fuel (Nat.le_refl fuel)) heqv hcontained
  have hcoherentCheck : coherent fuel finite = true :=
    coherent_complete_against_of_witness hreflect heqv
      (by
        intro smaller hlt
        exact hcomplete smaller (Nat.le_of_lt hlt))
      hlinear hcoherentWitness
  simp [wellFormedKit, hcontainedCheck, hcoherentCheck, hlinearCheck]

theorem optionGetD_le_foldl_max_from_acc
    {options : List (Option Nat)} {acc : Nat} :
    acc ≤ options.foldl (fun maxRank rank =>
      Nat.max maxRank (rank.getD 0)) acc := by
  induction options generalizing acc with
  | nil =>
      exact Nat.le_refl acc
  | cons head rest ih =>
      exact Nat.le_trans (Nat.le_max_left acc (head.getD 0)) ih

theorem optionGetD_le_foldl_max_of_mem
    {options : List (Option Nat)} {acc : Nat} {rank : Option Nat} :
    rank ∈ options →
      rank.getD 0 ≤ options.foldl (fun maxRank rank =>
        Nat.max maxRank (rank.getD 0)) acc := by
  intro hmem
  induction options generalizing acc with
  | nil =>
      cases hmem
  | cons head rest ih =>
      cases hmem with
      | head =>
          exact Nat.le_trans (Nat.le_max_right acc (rank.getD 0))
            optionGetD_le_foldl_max_from_acc
      | tail _ htail =>
          exact ih (acc := Nat.max acc (head.getD 0)) htail

theorem rankOf?_dep_lt_of_some
    {fuel : Nat} {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {rootRank depRank : Nat} {dep : Name} :
    rankOf? (fuel + 1) env name = some rootRank →
      env.lookup name = some slot →
        dep ∈ PartialTy.vars slot.ty →
          rankOf? fuel env dep = some depRank →
            depRank < rootRank := by
  intro hroot hslot hdep hdepRank
  simp [rankOf?, hslot] at hroot
  let ranks := (PartialTy.vars slot.ty).map (rankOf? fuel env)
  have hdepMem : some depRank ∈ ranks := by
    exact List.mem_map.mpr ⟨dep, hdep, hdepRank⟩
  have hdepLe :
      depRank ≤ ranks.foldl (fun maxRank rank =>
        Nat.max maxRank (rank.getD 0)) 0 := by
    simpa using
      (optionGetD_le_foldl_max_of_mem (acc := 0) hdepMem)
  rw [← hroot.2]
  simpa [ranks, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    Nat.lt_succ_of_le hdepLe

theorem rankOf?_some_of_linearizedBy_bound
    {fuel : Nat} {env : FiniteEnv} {φ : Name → Nat} {name : Name} :
    LinearizedBy φ env.toEnv →
      φ name < fuel →
        ∃ rank, rankOf? fuel env name = some rank := by
  intro hlinear hbound
  induction fuel generalizing name with
  | zero =>
      omega
  | succ fuel ih =>
      cases hslot : env.lookup name with
      | none =>
          exact ⟨0, by simp [rankOf?, hslot]⟩
      | some slot =>
          let deps := PartialTy.vars slot.ty
          let ranks := deps.map (rankOf? fuel env)
          have hdepsSome :
              ranks.any Option.isNone = false := by
            cases hany : ranks.any Option.isNone
            · rfl
            · exfalso
              rcases List.any_eq_true.mp hany with ⟨rankOpt, hrankOpt,
                hisNone⟩
              rcases List.mem_map.mp hrankOpt with ⟨dep, hdep, hrankDep⟩
              have hdepBound : φ dep < fuel := by
                have hdepLtName : φ dep < φ name :=
                  hlinear name slot hslot dep hdep
                omega
              rcases ih hdepBound with ⟨depRank, hdepRank⟩
              subst hrankDep
              simp [hdepRank] at hisNone
          refine
            ⟨1 + ranks.foldl (fun maxRank rank =>
              Nat.max maxRank (rank.getD 0)) 0, ?_⟩
          simp only [rankOf?, hslot]
          change
            (if ranks.any Option.isNone then none
             else
              some (1 + ranks.foldl (fun maxRank rank =>
                Nat.max maxRank (rank.getD 0)) 0)) =
                some (1 + ranks.foldl (fun maxRank rank =>
                  Nat.max maxRank (rank.getD 0)) 0)
          simp [hdepsSome]

theorem rankOf?_stable_of_some
    {fuel : Nat} {env : FiniteEnv} {name : Name} {rank : Nat} :
    rankOf? fuel env name = some rank →
      rankOf? (fuel + 1) env name = some rank := by
  induction fuel generalizing name rank with
  | zero =>
      intro h
      simp [rankOf?] at h
  | succ fuel ih =>
      intro h
      cases hslot : env.lookup name with
      | none =>
          simp [rankOf?, hslot] at h ⊢
          exact h
      | some slot =>
          simp [rankOf?, hslot] at h
          let oldRanks := (PartialTy.vars slot.ty).map (rankOf? fuel env)
          let newRanks := (PartialTy.vars slot.ty).map (rankOf? (fuel + 1) env)
          have hnewRanksEq : newRanks = oldRanks := by
            apply List.map_congr_left
            intro dep hdep
            cases hold : rankOf? fuel env dep with
            | none =>
                exact False.elim (h.1 dep hdep hold)
            | some depRank =>
                exact ih hold
          have hdepsNew :
              ∀ dep, dep ∈ PartialTy.vars slot.ty →
                ¬ rankOf? (fuel + 1) env dep = none := by
            intro dep hdep hnone
            cases hold : rankOf? fuel env dep with
            | none =>
                exact h.1 dep hdep hold
            | some depRank =>
                have hnew : rankOf? (fuel + 1) env dep = some depRank :=
                  ih hold
                rw [hnew] at hnone
                cases hnone
          have hfoldNew :
              1 + newRanks.foldl (fun maxRank rank =>
                Nat.max maxRank (rank.getD 0)) 0 = rank := by
            rw [hnewRanksEq]
            simpa [oldRanks] using h.2
          simp only [rankOf?, hslot]
          change
            (if newRanks.any Option.isNone then none
             else
              some (1 + newRanks.foldl (fun maxRank rank =>
                Nat.max maxRank (rank.getD 0)) 0)) = some rank
          have hnewSome : newRanks.any Option.isNone = false := by
            cases hany : newRanks.any Option.isNone
            · rfl
            · exfalso
              rcases List.any_eq_true.mp hany with ⟨rankOpt, hrankOpt,
                hisNone⟩
              rcases List.mem_map.mp hrankOpt with ⟨dep, hdep, hrankDep⟩
              cases hdepRank : rankOf? (fuel + 1) env dep with
              | none =>
                  exact hdepsNew dep hdep hdepRank
              | some depRank =>
                  subst hrankDep
                  simp [hdepRank] at hisNone
          simp [hnewSome, hfoldNew]

theorem linearizable_complete_of_rankOf?_spec {env : FiniteEnv} :
    (∀ {name : Name} {slot : EnvSlot},
      (name, slot) ∈ env.entries →
        ∃ rootRank,
          rankOf? ((envNames env).length + 1) env name = some rootRank ∧
            ∀ dep, dep ∈ PartialTy.vars slot.ty →
              ∃ depRank,
                rankOf? ((envNames env).length + 1) env dep = some depRank ∧
                  depRank < rootRank) →
      linearizable env = true := by
  intro hspec
  unfold linearizable
  exact List.all_eq_true.mpr (by
    intro entry hentry
    rcases entry with ⟨name, slot⟩
    rcases hspec hentry with ⟨rootRank, hrootRank, hdeps⟩
    change
      (match rankOf? ((envNames env).length + 1) env name with
      | none => false
      | some rootRank =>
          (PartialTy.vars slot.ty).all (fun dep =>
            match rankOf? ((envNames env).length + 1) env dep with
            | some depRank => depRank < rootRank
            | none => false)) = true
    rw [hrootRank]
    exact List.all_eq_true.mpr (by
      intro dep hdep
      rcases hdeps dep hdep with ⟨depRank, hdepRank, hlt⟩
      change
        (match rankOf? ((envNames env).length + 1) env dep with
        | some depRank => depRank < rootRank
        | none => false) = true
      rw [hdepRank]
      simpa using hlt))

theorem linearizable_complete_of_bounded_linearizedBy
    {env : FiniteEnv} {φ : Name → Nat} :
    FiniteEnv.EntriesReflectLookup env →
      LinearizedBy φ env.toEnv →
        (∀ {name : Name} {slot : EnvSlot},
          (name, slot) ∈ env.entries → φ name < (envNames env).length + 1) →
        linearizable env = true := by
  intro hreflect hlinear hbounded
  apply linearizable_complete_of_rankOf?_spec
  intro name slot hentry
  have hslot : env.lookup name = some slot :=
    hreflect hentry
  rcases rankOf?_some_of_linearizedBy_bound hlinear (hbounded hentry) with
    ⟨rootRank, hrootRank⟩
  refine ⟨rootRank, hrootRank, ?_⟩
  intro dep hdep
  have hdepBound : φ dep < (envNames env).length + 1 := by
    have hdepLtName : φ dep < φ name :=
      hlinear name slot hslot dep hdep
    have hnameBound := hbounded hentry
    omega
  rcases rankOf?_some_of_linearizedBy_bound hlinear hdepBound with
    ⟨depRank, hdepRank⟩
  refine ⟨depRank, hdepRank, ?_⟩
  have hdepPrev :
      rankOf? (envNames env).length env dep = some depRank := by
    cases hlen : (envNames env).length with
    | zero =>
        have hdepBoundZero : φ dep < 1 := by
          simpa [hlen] using hdepBound
        have hnameBoundZero : φ name < 1 := by
          simpa [hlen] using hbounded hentry
        have hdepLtName : φ dep < φ name :=
          hlinear name slot hslot dep hdep
        omega
    | succ pred =>
        -- Rank stability is one-way from smaller to larger, so the predecessor
        -- rank comes from the bounded-rank lemma directly in the nonzero case.
        have hdepBoundPred : φ dep < pred + 1 := by
          simpa [hlen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (show φ dep < (envNames env).length from by
              have hdepLtName : φ dep < φ name :=
                hlinear name slot hslot dep hdep
              have hnameBound := hbounded hentry
              omega)
        rcases rankOf?_some_of_linearizedBy_bound hlinear hdepBoundPred with
          ⟨depRankPred, hdepRankPred⟩
        have hstable :
            rankOf? (pred + 1 + 1) env dep = some depRankPred :=
          rankOf?_stable_of_some hdepRankPred
        have hsame : depRankPred = depRank := by
          rw [hlen] at hdepRank
          rw [hstable] at hdepRank
          exact Option.some.inj hdepRank
        subst hsame
        simpa [hlen] using hdepRankPred
  exact rankOf?_dep_lt_of_some hrootRank hslot hdep hdepPrev

theorem filter_length_le_of_imp_mem
    {α : Type} {items : List α} {lower upper : α → Bool}
    (himp : ∀ item, item ∈ items → lower item = true → upper item = true) :
    (items.filter lower).length ≤ (items.filter upper).length := by
  induction items with
  | nil =>
      simp
  | cons head tail ih =>
      have himpTail :
          ∀ item, item ∈ tail →
            lower item = true → upper item = true := by
        intro item hmem hlower
        exact himp item (by simp [hmem]) hlower
      by_cases hlowerHead : lower head = true
      · have hupperHead : upper head = true :=
          himp head (by simp) hlowerHead
        simpa [List.filter, hlowerHead, hupperHead] using ih himpTail
      · have hlowerHeadFalse : lower head = false :=
          Bool.eq_false_iff.mpr hlowerHead
        by_cases hupperHead : upper head = true
        · have hle := ih himpTail
          simpa [List.filter, hlowerHeadFalse, hupperHead] using
            Nat.le_succ_of_le hle
        · have hupperHeadFalse : upper head = false :=
            Bool.eq_false_iff.mpr hupperHead
          simpa [List.filter, hlowerHeadFalse, hupperHeadFalse] using
            ih himpTail

theorem filter_length_lt_of_imp_of_witness
    {α : Type} {items : List α} {lower upper : α → Bool}
    (himp : ∀ item, item ∈ items → lower item = true → upper item = true)
    (hwitness :
      ∃ item, item ∈ items ∧ lower item = false ∧ upper item = true) :
    (items.filter lower).length < (items.filter upper).length := by
  induction items with
  | nil =>
      rcases hwitness with ⟨item, hmem, _hlower, _hupper⟩
      cases hmem
  | cons head tail ih =>
      have himpTail :
          ∀ item, item ∈ tail →
            lower item = true → upper item = true := by
        intro item hmem hlower
        exact himp item (by simp [hmem]) hlower
      by_cases hlowerHead : lower head = true
      · have hupperHead : upper head = true :=
          himp head (by simp) hlowerHead
        have hwitnessTail :
            ∃ item, item ∈ tail ∧
              lower item = false ∧ upper item = true := by
          rcases hwitness with ⟨item, hmem, hlower, hupper⟩
          cases hmem with
          | head =>
            rw [hlowerHead] at hlower
            cases hlower
          | tail _ htail =>
            exact ⟨item, htail, hlower, hupper⟩
        simpa [List.filter, hlowerHead, hupperHead] using
          ih himpTail hwitnessTail
      · have hlowerHeadFalse : lower head = false :=
          Bool.eq_false_iff.mpr hlowerHead
        by_cases hupperHead : upper head = true
        · have hsub :
              (tail.filter lower).length ≤
                (tail.filter upper).length :=
            filter_length_le_of_imp_mem himpTail
          simpa [List.filter, hlowerHeadFalse, hupperHead] using
            Nat.lt_succ_of_le hsub
        · have hupperHeadFalse : upper head = false :=
            Bool.eq_false_iff.mpr hupperHead
          have hwitnessTail :
              ∃ item, item ∈ tail ∧
                lower item = false ∧ upper item = true := by
            rcases hwitness with ⟨item, hmem, hlower, hupper⟩
            cases hmem with
            | head =>
              rw [hupperHeadFalse] at hupper
              cases hupper
            | tail _ htail =>
              exact ⟨item, htail, hlower, hupper⟩
          simpa [List.filter, hlowerHeadFalse, hupperHeadFalse] using
            ih himpTail hwitnessTail

def boundedLinearRank (env : FiniteEnv) (φ : Name → Nat) (name : Name) :
    Nat :=
  ((envNames env).filter
    (fun candidate => decide (φ candidate < φ name))).length

theorem boundedLinearRank_lt
    {env : FiniteEnv} {φ : Name → Nat} {name dep : Name}
    {slot : EnvSlot} :
    LinearizedBy φ env.toEnv →
      env.lookup name = some slot →
        dep ∈ PartialTy.vars slot.ty →
          boundedLinearRank env φ dep < boundedLinearRank env φ name := by
  intro hlinear hslot hdep
  have hdepLtName : φ dep < φ name :=
    hlinear name slot hslot dep hdep
  unfold boundedLinearRank
  apply filter_length_lt_of_imp_of_witness
  · intro candidate _hmem hlower
    have hlowerProp :
        φ candidate < φ dep := by
      exact of_decide_eq_true hlower
    exact decide_eq_true (Nat.lt_trans hlowerProp hdepLtName)
  · refine ⟨dep, envNames_lookup_vars_mem hslot hdep, ?_, ?_⟩
    · exact decide_eq_false (by exact Nat.lt_irrefl (φ dep))
    · exact decide_eq_true hdepLtName

theorem boundedLinearRank_bounded
    {env : FiniteEnv} {φ : Name → Nat} {name : Name} :
    boundedLinearRank env φ name < (envNames env).length + 1 := by
  unfold boundedLinearRank
  exact Nat.lt_succ_of_le
    (List.length_filter_le
      (fun candidate => decide (φ candidate < φ name)) (envNames env))

theorem linearizedBy_boundedLinearRank
    {env : FiniteEnv} {φ : Name → Nat} :
    LinearizedBy φ env.toEnv →
      LinearizedBy (boundedLinearRank env φ) env.toEnv := by
  intro hlinear name slot hslot dep hdep
  exact boundedLinearRank_lt hlinear hslot hdep

theorem linearizable_complete_of_linearizedBy
    {env : FiniteEnv} {φ : Name → Nat} :
    FiniteEnv.EntriesReflectLookup env →
      LinearizedBy φ env.toEnv →
        linearizable env = true := by
  intro hreflect hlinear
  exact linearizable_complete_of_bounded_linearizedBy
    hreflect
    (linearizedBy_boundedLinearRank hlinear)
    (by
      intro name slot _hentry
      exact boundedLinearRank_bounded)

theorem linearizable_complete_against
    {finite : FiniteEnv} {env : Env} :
    FiniteEnv.EntriesReflectLookup finite →
      FiniteEnvEqv finite env →
        Linearizable env →
          linearizable finite = true := by
  intro hreflect heqv hlinear
  rcases hlinear with ⟨φ, hφ⟩
  exact linearizable_complete_of_linearizedBy hreflect
    (linearizedBy_of_finiteEnvEqv_left heqv hφ)

theorem linearizable_update_fresh_ty_of_eqv_left
    {env : Env} {name : Name} {checkedTy declTy : Ty}
    {lifetime : Lifetime} :
    Linearizable env →
      ContainedBorrowsWellFormed env →
        env.fresh name →
          WellFormedTy env declTy lifetime →
            Ty.eqv checkedTy declTy →
              Linearizable
                (env.update name
                  { ty := .ty checkedTy, lifetime := lifetime }) := by
  intro hlinear hcontained hfresh hwell htyEqv
  rcases hlinear with ⟨φ, hφ⟩
  have hnameNotInChecked : name ∉ Ty.vars checkedTy := by
    intro hnameMem
    have hnameDecl : name ∈ Ty.vars declTy :=
      ty_vars_of_eqv_left htyEqv hnameMem
    rcases wellFormedTy_vars_in_env hwell name hnameDecl with
      ⟨slot, hslot⟩
    change env.slotAt name = none at hfresh
    rw [hslot] at hfresh
    cases hfresh
  refine
    ⟨fun candidate =>
      if candidate = name then
        (Ty.vars checkedTy).foldr
          (fun dep rank => Nat.max (φ dep + 1) rank) 0
      else
        φ candidate, ?_⟩
  intro slotName slot hslot dep hdep
  by_cases hslotName : slotName = name
  ·
    have hslotEq :
        slot = { ty := PartialTy.ty checkedTy, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty checkedTy, lifetime := lifetime } = slot := by
        simpa [Env.update, hslotName] using hslot
      exact h.symm
    subst hslotEq
    have hdepTy : dep ∈ Ty.vars checkedTy := by
      simpa [PartialTy.vars] using hdep
    have hdepNe : dep ≠ name := by
      intro hdepEq
      exact hnameNotInChecked (by simpa [hdepEq] using hdepTy)
    simp only [hslotName, if_true, if_neg hdepNe]
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      (mem_foldr_max_succ hdepTy)
  · have hslotOld : env.slotAt slotName = some slot := by
      simpa [Env.update, hslotName] using hslot
    have hdepNe : dep ≠ name := by
      intro hdepEq
      rcases containedBorrows_slot_vars_in_env hcontained hslotOld dep hdep with
        ⟨depSlot, hdepSlot⟩
      rw [hdepEq] at hdepSlot
      change env.slotAt name = none at hfresh
      rw [hdepSlot] at hfresh
      cases hfresh
    simp only [if_neg hslotName, if_neg hdepNe]
    exact hφ slotName slot hslotOld dep hdep

theorem linearizedBy_update_freshGhostName
    {finite : FiniteEnv} {term : Term} {slot : EnvSlot}
    {φ : Name → Nat} :
    LinearizedBy φ finite.toEnv →
      (∀ dep, dep ∈ PartialTy.vars slot.ty → dep ∈ envNames finite) →
        LinearizedBy
          (fun name =>
            if name = freshGhostName finite term then
              (PartialTy.vars slot.ty).foldr
                (fun dep rank => Nat.max (φ dep + 1) rank) 0
            else
              φ name)
          (finite.update (freshGhostName finite term) slot).toEnv := by
  intro hlinear hslotVars name updatedSlot hlookup dep hdep
  by_cases hname : name = freshGhostName finite term
  · subst hname
    have hslotEq : updatedSlot = slot := by
      have h :
          slot = updatedSlot := by
        simpa [FiniteEnv.toEnv_update, Env.update] using hlookup
      exact h.symm
    subst hslotEq
    have hdepNe : dep ≠ freshGhostName finite term := by
      intro hdepEq
      exact freshGhostName_not_mem_envNames finite term
        (by
          rw [← hdepEq]
          exact hslotVars dep hdep)
    simp only [if_neg hdepNe]
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      (mem_foldr_max_succ hdep)
  · have hlookupOld : finite.lookup name = some updatedSlot := by
      have h :
          finite.toEnv.slotAt name = some updatedSlot := by
        simpa [FiniteEnv.toEnv_update, Env.update, hname] using hlookup
      exact h
    have hdepNe : dep ≠ freshGhostName finite term := by
      exact fun hdepEq =>
        freshGhostName_not_mem_lookup_vars hlookupOld hdepEq hdep
    simp only [if_neg hname, if_neg hdepNe]
    exact hlinear name updatedSlot hlookupOld dep hdep

theorem linearizable_update_freshGhostName
    {finite : FiniteEnv} {term : Term} {slot : EnvSlot} :
    Linearizable finite.toEnv →
      (∀ dep, dep ∈ PartialTy.vars slot.ty → dep ∈ envNames finite) →
        Linearizable
          (finite.update (freshGhostName finite term) slot).toEnv := by
  intro hlinear hslotVars
  rcases hlinear with ⟨φ, hφ⟩
  exact ⟨_, linearizedBy_update_freshGhostName hφ hslotVars⟩

theorem linearizable_complete_update_freshGhostName
    {finite : FiniteEnv} {term : Term} {slot : EnvSlot} :
    FiniteEnv.EntriesReflectLookup finite →
      Linearizable finite.toEnv →
        (∀ dep, dep ∈ PartialTy.vars slot.ty → dep ∈ envNames finite) →
          linearizable
            (finite.update (freshGhostName finite term) slot) = true := by
  intro hreflect hlinear hslotVars
  rcases hlinear with ⟨φ, hφ⟩
  exact linearizable_complete_of_linearizedBy
    (FiniteEnv.entriesReflectLookup_update hreflect)
    (linearizedBy_update_freshGhostName hφ hslotVars)

theorem linearizable_complete_update_freshGhostName_of_wellFormedTy_eqv
    {finite : FiniteEnv} {env : Env} {term : Term}
    {checkedTy declTy : Ty} {lifetime : Lifetime} :
    FiniteEnv.EntriesReflectLookup finite →
      FiniteEnvEqv finite env →
        Linearizable env →
          Ty.eqv checkedTy declTy →
            WellFormedTy env declTy lifetime →
              linearizable
                (finite.update (freshGhostName finite term)
                  { ty := .ty checkedTy, lifetime := lifetime }) = true := by
  intro hreflect heqv hlinear htyEqv hwell
  exact linearizable_complete_update_freshGhostName hreflect
    (linearizable_of_finiteEnvEqv_left heqv hlinear)
    (by
      intro dep hdep
      exact ty_vars_mem_envNames_of_wellFormedTy_eqv
        heqv htyEqv hwell (by simpa [PartialTy.vars] using hdep))

theorem wellFormedKit_complete_against_of_witness_complete
    {fuel : Nat} {finite : FiniteEnv} {env : Env} :
    FiniteEnv.EntriesReflectLookup finite →
      FiniteEnvEqv finite env →
        (∀ smaller, smaller ≤ fuel →
          LValCompleteAgainst smaller finite env) →
          Linearizable env →
            ContainedBorrowsWellFormed env →
              CoherentCompleteWitness fuel env →
                wellFormedKit fuel finite = true := by
  intro hreflect heqv hcomplete hlinear hcontained hcoherentWitness
  exact wellFormedKit_complete_against_of_witness
    hreflect heqv hcomplete hlinear hcontained hcoherentWitness
    (linearizable_complete_against hreflect heqv hlinear)

theorem wellFormedKit_complete_update_freshGhostName_of_eqv_left
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {term : Term}
    {checkedTy declTy : Ty} {lifetime : Lifetime} :
    FiniteEnv.EntriesReflectLookup finite →
      FiniteEnvEqv finite env →
        (∀ smaller, smaller ≤ fuel →
          LValCompleteAgainst smaller
            (finite.update (freshGhostName finite term)
              { ty := .ty checkedTy, lifetime := lifetime })
            (env.update (freshGhostName finite term)
              { ty := .ty checkedTy, lifetime := lifetime })) →
          Linearizable env →
            ContainedBorrowsWellFormed env →
              CoherentCompleteWitness fuel env →
                Ty.eqv checkedTy declTy →
                  WellFormedTy env declTy lifetime →
                    TyCoherentCompleteWitness fuel env declTy →
                      wellFormedKit fuel
                        (finite.update (freshGhostName finite term)
                          { ty := .ty checkedTy, lifetime := lifetime }) =
                        true := by
  intro hreflect heqv hcomplete hlinear hcontained hwitness htyEqv hwell
    htyWitness
  have hfresh :
      env.fresh (freshGhostName finite term) :=
    finiteEnvEqv_fresh_of_toEnv_fresh heqv
      (freshGhostName_toEnv_fresh finite term)
  exact wellFormedKit_complete_against_of_witness_complete
    (FiniteEnv.entriesReflectLookup_update hreflect)
    (finiteEnvEqv_update heqv (envSlotEqv_refl _))
    hcomplete
    (linearizable_update_fresh_ty_of_eqv_left hlinear hcontained
      hfresh hwell htyEqv)
    (containedBorrowsWellFormed_update_fresh_ty_of_eqv_left hcontained
      hwell hfresh htyEqv)
    (coherentCompleteWitness_update_fresh_ty_of_eqv_left hlinear
      hfresh hwitness htyEqv htyWitness)

theorem envBorrowEdges_mem_exists_entry {entries : List (Name × EnvSlot)}
    {root : Name} {mutable : Bool} {targets : List LVal} :
    (root, mutable, targets) ∈
        entries.foldr
          (fun entry edges =>
            (partialTyBorrows entry.2.ty).map
                (fun borrow => (entry.1, borrow.1, borrow.2)) ++ edges)
          [] →
      ∃ slot,
        (root, slot) ∈ entries ∧
          (mutable, targets) ∈ partialTyBorrows slot.ty := by
  induction entries with
  | nil =>
      intro h
      simp at h
  | cons entry rest ih =>
      intro h
      rcases entry with ⟨entryName, entrySlot⟩
      change
        (root, mutable, targets) ∈
          (partialTyBorrows entrySlot.ty).map
              (fun borrow => (entryName, borrow.1, borrow.2)) ++
            rest.foldr
              (fun entry edges =>
                (partialTyBorrows entry.2.ty).map
                    (fun borrow => (entry.1, borrow.1, borrow.2)) ++ edges)
              [] at h
      rcases List.mem_append.mp h with hhead | hrest
      · rcases List.mem_map.mp hhead with ⟨borrow, hborrow, hedge⟩
        cases hedge
        exact ⟨entrySlot, List.mem_cons_self, hborrow⟩
      · rcases ih hrest with ⟨slot, hentry, hborrow⟩
        exact ⟨slot, List.mem_cons_of_mem _ hentry, hborrow⟩

theorem envBorrowEdges_contains_sound {env : FiniteEnv}
    {root : Name} {mutable : Bool} {targets : List LVal} :
    FiniteEnv.EntriesReflectLookup env →
      (root, mutable, targets) ∈ envBorrowEdges env →
        env.toEnv ⊢ root ↝ Ty.borrow mutable targets := by
  intro hreflect hedge
  rcases envBorrowEdges_mem_exists_entry hedge with
    ⟨slot, hentry, hborrow⟩
  exact ⟨slot, hreflect hentry,
    partialTyContainsBorrow_of_mem hborrow⟩

theorem envBorrowEdges_mem_of_entry {entries : List (Name × EnvSlot)}
    {entry : Name × EnvSlot} {borrow : Bool × List LVal} :
    entry ∈ entries →
      borrow ∈ partialTyBorrows entry.2.ty →
        (entry.1, borrow.1, borrow.2) ∈
          entries.foldr
            (fun entry edges =>
              (partialTyBorrows entry.2.ty).map
                  (fun borrow => (entry.1, borrow.1, borrow.2)) ++ edges)
            [] := by
  intro hentry hborrow
  induction entries with
  | nil =>
      cases hentry
  | cons head rest ih =>
      cases hentry with
      | head =>
          exact List.mem_append_left _ (List.mem_map.mpr
            ⟨borrow, hborrow, rfl⟩)
      | tail _ htail =>
          exact List.mem_append_right _
            (ih htail)

theorem envBorrowEdges_contains_complete {env : FiniteEnv}
    {root : Name} {mutable : Bool} {targets : List LVal} :
    env.toEnv ⊢ root ↝ Ty.borrow mutable targets →
      (root, mutable, targets) ∈ envBorrowEdges env := by
  rintro ⟨slot, hslot, hcontains⟩
  exact envBorrowEdges_mem_of_entry (FiniteEnv.lookupEntries_mem hslot)
    (partialTyContainsBorrow_mem hcontains)

theorem readProhibited_true_sound {env : FiniteEnv} {lv : LVal} :
    FiniteEnv.EntriesReflectLookup env →
      readProhibited env lv = true →
        ReadProhibited env.toEnv lv := by
  intro hreflect htrue
  rw [readProhibited, List.any_eq_true] at htrue
  rcases htrue with ⟨edge, hedge, hconflictInEdge⟩
  rcases edge with ⟨root, mutable, targets⟩
  rcases Bool.and_eq_true_iff.mp hconflictInEdge with
    ⟨hmutable, htargets⟩
  have hmutableEq : mutable = true := by
    simpa using hmutable
  subst mutable
  rcases List.any_eq_true.mp htargets with
    ⟨target, htarget, hconflict⟩
  exact ⟨root, targets, target,
    envBorrowEdges_contains_sound hreflect hedge, htarget,
    by simpa [pathConflicts, PathConflicts] using hconflict⟩

theorem readProhibited_complete {env : FiniteEnv} {lv : LVal} :
    FiniteEnv.EntriesReflectLookup env →
      ¬ ReadProhibited env.toEnv lv →
        readProhibited env lv = false := by
  intro hreflect hnot
  cases hread : readProhibited env lv
  · rfl
  · exact False.elim (hnot (readProhibited_true_sound hreflect hread))

theorem writeProhibited_true_sound {env : FiniteEnv} {lv : LVal} :
    FiniteEnv.EntriesReflectLookup env →
      writeProhibited env lv = true →
        WriteProhibited env.toEnv lv := by
  intro hreflect htrue
  unfold writeProhibited at htrue
  cases hread : readProhibited env lv
  · have hany :
        (envBorrowEdges env).any (fun edge =>
          edge.2.2.any (fun target => pathConflicts target lv)) = true := by
      simpa [hread] using htrue
    rw [List.any_eq_true] at hany
    rcases hany with ⟨edge, hedge, htargetInEdge⟩
    rcases edge with ⟨root, mutable, targets⟩
    rcases List.any_eq_true.mp htargetInEdge with
      ⟨target, htarget, hconflict⟩
    have hcontains :
        env.toEnv ⊢ root ↝ Ty.borrow mutable targets :=
      envBorrowEdges_contains_sound hreflect hedge
    cases mutable
    · exact Or.inr ⟨root, targets, target, hcontains, htarget,
        by simpa [pathConflicts, PathConflicts] using hconflict⟩
    · exact Or.inl ⟨root, targets, target, hcontains, htarget,
        by simpa [pathConflicts, PathConflicts] using hconflict⟩
  · exact Or.inl (readProhibited_true_sound hreflect hread)

theorem writeProhibited_complete {env : FiniteEnv} {lv : LVal} :
    FiniteEnv.EntriesReflectLookup env →
      ¬ WriteProhibited env.toEnv lv →
        writeProhibited env lv = false := by
  intro hreflect hnot
  cases hwrite : writeProhibited env lv
  · rfl
  · exact False.elim (hnot (writeProhibited_true_sound hreflect hwrite))

theorem tyBorrowSafeAgainstEnv_of_finiteEnvEqv_left
    {finite : FiniteEnv} {env : Env} {checkedTy declTy : Ty} :
    FiniteEnvEqv finite env →
      Ty.eqv checkedTy declTy →
        TyBorrowSafeAgainstEnv env declTy →
          TyBorrowSafeAgainstEnv finite.toEnv checkedTy := by
  intro heqv htyEqv hsafe
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther
      hcontainsChecked hcontainsFinite htargetMutable htargetOther hconflict
    rcases partialTyContains_borrow_of_eqv_left
        (show PartialTy.eqv (.ty checkedTy) (.ty declTy) from htyEqv)
        hcontainsChecked with
      ⟨declTargetsMutable, hcontainsDecl, hsubsetDecl⟩
    rcases envContains_borrow_of_finiteEnvEqv_left heqv hcontainsFinite with
      ⟨envTargetsOther, hcontainsEnv, hsubsetEnv⟩
    exact hsafe.1 declTargetsMutable mutable envTargetsOther x
      targetMutable targetOther hcontainsDecl hcontainsEnv
      (hsubsetDecl htargetMutable) (hsubsetEnv htargetOther) hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsFinite hcontainsChecked htargetMutable htargetOther hconflict
    rcases envContains_borrow_of_finiteEnvEqv_left heqv hcontainsFinite with
      ⟨envTargetsMutable, hcontainsEnv, hsubsetEnv⟩
    rcases partialTyContains_borrow_of_eqv_left
        (show PartialTy.eqv (.ty checkedTy) (.ty declTy) from htyEqv)
        hcontainsChecked with
      ⟨declTargetsOther, hcontainsDecl, hsubsetDecl⟩
    exact hsafe.2 x envTargetsMutable mutable declTargetsOther
      targetMutable targetOther hcontainsEnv hcontainsDecl
      (hsubsetEnv htargetMutable) (hsubsetDecl htargetOther) hconflict

theorem tyBorrowSafeAgainstEnv_complete {env : FiniteEnv} {ty : Ty} :
    FiniteEnv.EntriesReflectLookup env →
      TyBorrowSafeAgainstEnv env.toEnv ty →
        tyBorrowSafeAgainstEnv env ty = true := by
  intro hreflect hsafe
  let tyBorrowList : List (Bool × List LVal) := tyBorrows ty
  let envBorrowList : List (Name × Bool × List LVal) := envBorrowEdges env
  have hleft :
      tyBorrowList.all (fun tyBorrow =>
        if tyBorrow.1 then
          envBorrowList.all (fun envBorrow =>
            tyBorrow.2.all (fun targetMutable =>
              envBorrow.2.2.all (fun targetOther =>
                !pathConflicts targetMutable targetOther)))
        else
          true) = true := by
    refine List.all_eq_true.mpr ?_
    intro (tyBorrow : Bool × List LVal) htyBorrow
    rcases tyBorrow with ⟨mutable, targetsMutable⟩
    cases mutable with
    | false =>
        rfl
    | true =>
        change
          envBorrowList.all (fun envBorrow =>
            targetsMutable.all (fun targetMutable =>
              envBorrow.2.2.all (fun targetOther =>
                !pathConflicts targetMutable targetOther))) = true
        refine List.all_eq_true.mpr ?_
        intro (envBorrow : Name × Bool × List LVal) henvBorrow
        rcases envBorrow with ⟨root, borrowMutable, targetsOther⟩
        change
          (targetsMutable.all (fun targetMutable =>
            targetsOther.all (fun targetOther =>
              !pathConflicts targetMutable targetOther))) = true
        exact List.all_eq_true.mpr (by
          intro targetMutable htargetMutable
          exact List.all_eq_true.mpr (by
            intro targetOther htargetOther
            cases hconflict : pathConflicts targetMutable targetOther
            · rfl
            · exfalso
              exact hsafe.1 targetsMutable borrowMutable targetsOther root
                targetMutable targetOther
                (tyContainsBorrow_of_mem (by simpa [tyBorrowList] using htyBorrow))
                (envBorrowEdges_contains_sound hreflect
                  (by simpa [envBorrowList] using henvBorrow))
                htargetMutable htargetOther
                (by
                  simpa [pathConflicts, PathConflicts] using hconflict)))
  have hright :
      envBorrowList.all (fun envBorrow =>
        if envBorrow.2.1 then
          tyBorrowList.all (fun tyBorrow =>
            envBorrow.2.2.all (fun targetMutable =>
              tyBorrow.2.all (fun targetOther =>
                !pathConflicts targetMutable targetOther)))
        else
          true) = true := by
    refine List.all_eq_true.mpr ?_
    intro (envBorrow : Name × Bool × List LVal) henvBorrow
    rcases envBorrow with ⟨root, mutableRoot, targetsMutable⟩
    cases mutableRoot with
    | false =>
        rfl
    | true =>
        change
          tyBorrowList.all (fun tyBorrow =>
            targetsMutable.all (fun targetMutable =>
              tyBorrow.2.all (fun targetOther =>
                !pathConflicts targetMutable targetOther))) = true
        refine List.all_eq_true.mpr ?_
        intro (tyBorrow : Bool × List LVal) htyBorrow
        rcases tyBorrow with ⟨borrowMutable, targetsOther⟩
        change
          (targetsMutable.all (fun targetMutable =>
            targetsOther.all (fun targetOther =>
              !pathConflicts targetMutable targetOther))) = true
        exact List.all_eq_true.mpr (by
          intro targetMutable htargetMutable
          exact List.all_eq_true.mpr (by
            intro targetOther htargetOther
            cases hconflict : pathConflicts targetMutable targetOther
            · rfl
            · exfalso
              exact hsafe.2 root targetsMutable borrowMutable targetsOther
                targetMutable targetOther
                (envBorrowEdges_contains_sound hreflect
                  (by simpa [envBorrowList] using henvBorrow))
                (tyContainsBorrow_of_mem (by simpa [tyBorrowList] using htyBorrow))
                htargetMutable htargetOther
                (by
                  simpa [pathConflicts, PathConflicts] using hconflict)))
  unfold tyBorrowSafeAgainstEnv
  change
    (tyBorrowList.all (fun tyBorrow =>
      if tyBorrow.1 then
        envBorrowList.all (fun envBorrow =>
          tyBorrow.2.all (fun targetMutable =>
            envBorrow.2.2.all (fun targetOther =>
              !pathConflicts targetMutable targetOther)))
      else
        true) &&
      envBorrowList.all (fun envBorrow =>
        if envBorrow.2.1 then
          tyBorrowList.all (fun tyBorrow =>
            envBorrow.2.2.all (fun targetMutable =>
              tyBorrow.2.all (fun targetOther =>
                !pathConflicts targetMutable targetOther)))
        else
        true)) = true
  exact Bool.and_eq_true_iff.mpr ⟨hleft, hright⟩

theorem tyBorrowSafeAgainstEnv_complete_against
    {finite : FiniteEnv} {env : Env} {checkedTy declTy : Ty} :
    FiniteEnv.EntriesReflectLookup finite →
      FiniteEnvEqv finite env →
        Ty.eqv checkedTy declTy →
          TyBorrowSafeAgainstEnv env declTy →
            tyBorrowSafeAgainstEnv finite checkedTy = true := by
  intro hreflect heqv htyEqv hsafe
  exact tyBorrowSafeAgainstEnv_complete hreflect
    (tyBorrowSafeAgainstEnv_of_finiteEnvEqv_left heqv htyEqv hsafe)

theorem borrowSafeRoot_of_finiteEnvEqv_left
    {finite : FiniteEnv} {env : Env} {root : Name} :
    FiniteEnvEqv finite env →
      BorrowSafeRoot env root →
        BorrowSafeRoot finite.toEnv root := by
  intro heqv hsafe y mutable targetsMutable targetsOther targetMutable
    targetOther hrootFinite hotherFinite htargetMutable htargetOther
    hconflict
  rcases envContains_borrow_of_finiteEnvEqv_left heqv hrootFinite with
    ⟨envTargetsMutable, hrootEnv, hsubsetMutable⟩
  rcases envContains_borrow_of_finiteEnvEqv_left heqv hotherFinite with
    ⟨envTargetsOther, hotherEnv, hsubsetOther⟩
  exact hsafe y mutable envTargetsMutable envTargetsOther targetMutable
    targetOther hrootEnv hotherEnv (hsubsetMutable htargetMutable)
    (hsubsetOther htargetOther) hconflict

theorem borrowSafeRoot_complete {env : FiniteEnv} {root : Name} :
    FiniteEnv.EntriesReflectLookup env →
      BorrowSafeRoot env.toEnv root →
        borrowSafeRoot env root = true := by
  intro hreflect hsafe
  unfold borrowSafeRoot
  refine List.all_eq_true.mpr ?_
  intro rootBorrow hrootBorrow
  rcases rootBorrow with ⟨borrowRoot, mutableRoot, targetsMutable⟩
  rcases List.mem_filter.mp hrootBorrow with ⟨hrootEdge, hrootFilter⟩
  rcases Bool.and_eq_true_iff.mp hrootFilter with
    ⟨hrootEqBool, hmutableRootBool⟩
  have hrootEq : borrowRoot = root := by
    simpa using hrootEqBool
  have hmutableRoot : mutableRoot = true := by
    simpa using hmutableRootBool
  subst borrowRoot
  subst mutableRoot
  refine List.all_eq_true.mpr ?_
  intro otherBorrow hotherBorrow
  rcases otherBorrow with ⟨otherRoot, otherMutable, targetsOther⟩
  refine List.all_eq_true.mpr ?_
  intro targetMutable htargetMutable
  refine List.all_eq_true.mpr ?_
  intro targetOther htargetOther
  cases hconflict : pathConflicts targetMutable targetOther
  · rfl
  · have hsameRoot : root = otherRoot :=
      hsafe otherRoot otherMutable targetsMutable targetsOther targetMutable
        targetOther
        (envBorrowEdges_contains_sound hreflect hrootEdge)
        (envBorrowEdges_contains_sound hreflect hotherBorrow)
        htargetMutable htargetOther
        (by simpa [pathConflicts, PathConflicts] using hconflict)
    simpa using hsameRoot

theorem borrowSafeRoot_complete_against
    {finite : FiniteEnv} {env : Env} {root : Name} :
    FiniteEnv.EntriesReflectLookup finite →
      FiniteEnvEqv finite env →
        BorrowSafeRoot env root →
          borrowSafeRoot finite root = true := by
  intro hreflect heqv hsafe
  exact borrowSafeRoot_complete hreflect
    (borrowSafeRoot_of_finiteEnvEqv_left heqv hsafe)

theorem borrowAuthorityGuard_of_finiteEnvEqv_left
    {finite : FiniteEnv} {env : Env} {base root : Name} :
    FiniteEnvEqv finite env →
      BorrowAuthorityGuard finite.toEnv base root →
        BorrowAuthorityGuard env base root := by
  intro heqv hguard
  induction hguard with
  | base =>
      exact BorrowAuthorityGuard.base
  | step hcontainer hcontains htarget ih =>
      rcases envContains_borrow_of_finiteEnvEqv_left heqv hcontains with
        ⟨envTargets, hcontainsEnv, hsubset⟩
      exact BorrowAuthorityGuard.step ih hcontainsEnv (hsubset htarget)

theorem assignmentBorrowSafety_of_finiteEnvEqv_left
    {finite : FiniteEnv} {env : Env} {lhs : LVal} :
    FiniteEnvEqv finite env →
      AssignmentBorrowSafety env lhs →
        AssignmentBorrowSafety finite.toEnv lhs := by
  intro heqv hsafe
  cases lhs with
  | var name =>
      trivial
  | deref source =>
      intro root hguard
      exact borrowSafeRoot_of_finiteEnvEqv_left heqv
        (hsafe root (borrowAuthorityGuard_of_finiteEnvEqv_left heqv hguard))

end BorrowProhibitionCompleteness

section PrimitiveTermCompleteness

attribute [local simp] Bind.bind Pure.pure Except.bind Except.map Except.pure
  Functor.mapConst discard ensure fromOption

theorem checkTerm?_complete_copy_of_lvalComplete
    {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAt fuel env →
      FiniteEnv.EntriesReflectLookup env →
        LValTyping env.toEnv lv (.ty ty) valueLifetime →
          CopyTy ty →
            ¬ ReadProhibited env.toEnv lv →
              ∃ result,
                checkTerm? (fuel + 1) env typing lifetime (.copy lv) =
                  .ok result := by
  intro hlvalComplete hreflect htyping hcopy hnotRead
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  have hcopyChecked : copyTy checkedFullTy = true :=
    copyTy_complete_of_eqv hcheckedEqv hcopy
  have hread : readProhibited env lv = false :=
    readProhibited_complete hreflect hnotRead
  refine ⟨{ ty := checkedFullTy, env := env }, ?_⟩
  simp [checkTerm?, hchecked, hcopyChecked, hread]

theorem checkTerm?_complete_move_of_lvalComplete
    {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {moved : Env} :
    LValCompleteAt fuel env →
      FiniteEnv.EntriesReflectLookup env →
        LValTyping env.toEnv lv (.ty ty) valueLifetime →
          ¬ WriteProhibited env.toEnv lv →
            EnvMove env.toEnv lv moved →
              ∃ result,
                checkTerm? (fuel + 1) env typing lifetime (.move lv) =
                  .ok result ∧ result.env.toEnv = moved := by
  intro hlvalComplete hreflect htyping hnotWrite hmove
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
  subst hcheckedTy
  have hwrite : writeProhibited env lv = false :=
    writeProhibited_complete hreflect hnotWrite
  rcases envMove?_complete hmove with
    ⟨movedFinite, hmoved, hmovedEnv⟩
  refine ⟨{ ty := checkedFullTy, env := movedFinite }, ?_, hmovedEnv⟩
  simp [checkTerm?, hchecked, hwrite, hmoved]

theorem checkTerm?_complete_immBorrow_of_lvalComplete
    {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAt fuel env →
      FiniteEnv.EntriesReflectLookup env →
        LValTyping env.toEnv lv (.ty ty) valueLifetime →
          ¬ ReadProhibited env.toEnv lv →
            ∃ result,
              checkTerm? (fuel + 1) env typing lifetime (.borrow false lv) =
                .ok result := by
  intro hlvalComplete hreflect htyping hnotRead
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
  subst hcheckedTy
  have hread : readProhibited env lv = false :=
    readProhibited_complete hreflect hnotRead
  refine ⟨{ ty := .borrow false [lv], env := env }, ?_⟩
  simp [checkTerm?, hchecked, hread]

theorem checkTerm?_complete_mutBorrow_of_lvalComplete
    {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAt fuel env →
      FiniteEnv.EntriesReflectLookup env →
        LValTyping env.toEnv lv (.ty ty) valueLifetime →
          mutableLVal fuel env lv = true →
            ¬ WriteProhibited env.toEnv lv →
              ∃ result,
                checkTerm? (fuel + 1) env typing lifetime (.borrow true lv) =
                  .ok result := by
  intro hlvalComplete hreflect htyping hmutable hnotWrite
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
  subst hcheckedTy
  have hwrite : writeProhibited env lv = false :=
    writeProhibited_complete hreflect hnotWrite
  refine ⟨{ ty := .borrow true [lv], env := env }, ?_⟩
  simp [checkTerm?, hchecked, hmutable, hwrite]

theorem checkTerm?_complete_mutBorrow_of_lvalComplete_of_mutableComplete
    {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAt fuel env →
      MutableCompleteAt fuel env →
        FiniteEnv.EntriesReflectLookup env →
          LValTyping env.toEnv lv (.ty ty) valueLifetime →
            Mutable env.toEnv lv →
              ¬ WriteProhibited env.toEnv lv →
                ∃ result,
                  checkTerm? (fuel + 1) env typing lifetime (.borrow true lv) =
                    .ok result := by
  intro hlvalComplete hmutableComplete hreflect htyping hmutable hnotWrite
  exact checkTerm?_complete_mutBorrow_of_lvalComplete hlvalComplete hreflect
    htyping (hmutableComplete hmutable) hnotWrite

theorem checkTerm?_complete_copy_of_lvalCompleteAgainst
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAgainst fuel finite env →
      FiniteEnvEqv finite env →
        FiniteEnv.EntriesReflectLookup finite →
          LValTyping env lv (.ty ty) valueLifetime →
            CopyTy ty →
              ¬ ReadProhibited env lv →
                ∃ result,
                  checkTerm? (fuel + 1) finite typing lifetime (.copy lv) =
                    .ok result := by
  intro hlvalComplete heqvEnv hreflect htyping hcopy hnotRead
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  have hcopyChecked : copyTy checkedFullTy = true :=
    copyTy_complete_of_eqv hcheckedEqv hcopy
  have hnotReadFinite : ¬ ReadProhibited finite.toEnv lv :=
    not_readProhibited_toEnv_of_finiteEnvEqv heqvEnv hnotRead
  have hread : readProhibited finite lv = false :=
    readProhibited_complete hreflect hnotReadFinite
  refine ⟨{ ty := checkedFullTy, env := finite }, ?_⟩
  simp [checkTerm?, hchecked, hcopyChecked, hread]

theorem checkTerm?_complete_copy_of_lvalCompleteAgainst_eqv
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAgainst fuel finite env →
      FiniteEnvEqv finite env →
        FiniteEnv.EntriesReflectLookup finite →
          LValTyping env lv (.ty ty) valueLifetime →
            CopyTy ty →
              ¬ ReadProhibited env lv →
                ∃ result,
                  checkTerm? (fuel + 1) finite typing lifetime (.copy lv) =
                    .ok result ∧
                  Ty.eqv result.ty ty ∧
                    FiniteEnvEqv result.env env := by
  intro hlvalComplete heqvEnv hreflect htyping hcopy hnotRead
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  have hcopyChecked : copyTy checkedFullTy = true :=
    copyTy_complete_of_eqv hcheckedEqv hcopy
  have hnotReadFinite : ¬ ReadProhibited finite.toEnv lv :=
    not_readProhibited_toEnv_of_finiteEnvEqv heqvEnv hnotRead
  have hread : readProhibited finite lv = false :=
    readProhibited_complete hreflect hnotReadFinite
  refine
    ⟨{ ty := checkedFullTy, env := finite }, ?_,
      Ty.eqv_symm hcheckedEqv, heqvEnv⟩
  simp [checkTerm?, hchecked, hcopyChecked, hread]

theorem checkTerm?_complete_move_of_lvalCompleteAgainst
    {fuel : Nat} {finite : FiniteEnv} {env moved : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {lv : LVal} {ty : Ty} :
    LValCompleteAgainst fuel finite env →
      FiniteEnvEqv finite env →
        FiniteEnv.EntriesReflectLookup finite →
          LValTyping env lv (.ty ty) valueLifetime →
            ¬ WriteProhibited env lv →
              EnvMove env lv moved →
                ∃ result,
                  checkTerm? (fuel + 1) finite typing lifetime (.move lv) =
                    .ok result ∧
                  Ty.eqv result.ty ty ∧
                    FiniteEnvEqv result.env moved := by
  intro hlvalComplete heqvEnv hreflect htyping hnotWrite hmove
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, hcheckedEqv⟩
  subst hcheckedTy
  have hnotWriteFinite : ¬ WriteProhibited finite.toEnv lv :=
    not_writeProhibited_toEnv_of_finiteEnvEqv heqvEnv hnotWrite
  have hwrite : writeProhibited finite lv = false :=
    writeProhibited_complete hreflect hnotWriteFinite
  rcases envMove?_complete_against heqvEnv hmove with
    ⟨movedFinite, hmoved, hmovedEqv⟩
  refine
    ⟨{ ty := checkedFullTy, env := movedFinite }, ?_,
      Ty.eqv_symm hcheckedEqv, hmovedEqv⟩
  simp [checkTerm?, hchecked, hwrite, hmoved]

theorem checkTerm?_complete_immBorrow_of_lvalCompleteAgainst
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAgainst fuel finite env →
      FiniteEnvEqv finite env →
        FiniteEnv.EntriesReflectLookup finite →
          LValTyping env lv (.ty ty) valueLifetime →
            ¬ ReadProhibited env lv →
              ∃ result,
                checkTerm? (fuel + 1) finite typing lifetime
                    (.borrow false lv) =
                  .ok result := by
  intro hlvalComplete heqvEnv hreflect htyping hnotRead
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
  subst hcheckedTy
  have hnotReadFinite : ¬ ReadProhibited finite.toEnv lv :=
    not_readProhibited_toEnv_of_finiteEnvEqv heqvEnv hnotRead
  have hread : readProhibited finite lv = false :=
    readProhibited_complete hreflect hnotReadFinite
  refine ⟨{ ty := .borrow false [lv], env := finite }, ?_⟩
  simp [checkTerm?, hchecked, hread]

theorem checkTerm?_complete_immBorrow_of_lvalCompleteAgainst_eqv
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAgainst fuel finite env →
      FiniteEnvEqv finite env →
        FiniteEnv.EntriesReflectLookup finite →
          LValTyping env lv (.ty ty) valueLifetime →
            ¬ ReadProhibited env lv →
              ∃ result,
                checkTerm? (fuel + 1) finite typing lifetime
                    (.borrow false lv) =
                  .ok result ∧
                Ty.eqv result.ty (.borrow false [lv]) ∧
                  FiniteEnvEqv result.env env := by
  intro hlvalComplete heqvEnv hreflect htyping hnotRead
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
  subst hcheckedTy
  have hnotReadFinite : ¬ ReadProhibited finite.toEnv lv :=
    not_readProhibited_toEnv_of_finiteEnvEqv heqvEnv hnotRead
  have hread : readProhibited finite lv = false :=
    readProhibited_complete hreflect hnotReadFinite
  refine
    ⟨{ ty := .borrow false [lv], env := finite }, ?_,
      Ty.eqv_refl _, heqvEnv⟩
  simp [checkTerm?, hchecked, hread]

theorem checkTerm?_complete_mutBorrow_of_lvalCompleteAgainst
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAgainst fuel finite env →
      MutableCompleteAgainst fuel finite env →
        FiniteEnvEqv finite env →
          FiniteEnv.EntriesReflectLookup finite →
            LValTyping env lv (.ty ty) valueLifetime →
              Mutable env lv →
                ¬ WriteProhibited env lv →
                  ∃ result,
                    checkTerm? (fuel + 1) finite typing lifetime
                        (.borrow true lv) =
                      .ok result := by
  intro hlvalComplete hmutableComplete heqvEnv hreflect htyping hmutable
    hnotWrite
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
  subst hcheckedTy
  have hnotWriteFinite : ¬ WriteProhibited finite.toEnv lv :=
    not_writeProhibited_toEnv_of_finiteEnvEqv heqvEnv hnotWrite
  have hwrite : writeProhibited finite lv = false :=
    writeProhibited_complete hreflect hnotWriteFinite
  refine ⟨{ ty := .borrow true [lv], env := finite }, ?_⟩
  simp [checkTerm?, hchecked, hmutableComplete hmutable, hwrite]

theorem checkTerm?_complete_mutBorrow_of_lvalCompleteAgainst_eqv
    {fuel : Nat} {finite : FiniteEnv} {env : Env} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    LValCompleteAgainst fuel finite env →
      MutableCompleteAgainst fuel finite env →
        FiniteEnvEqv finite env →
          FiniteEnv.EntriesReflectLookup finite →
            LValTyping env lv (.ty ty) valueLifetime →
              Mutable env lv →
                ¬ WriteProhibited env lv →
                  ∃ result,
                    checkTerm? (fuel + 1) finite typing lifetime
                        (.borrow true lv) =
                      .ok result ∧
                    Ty.eqv result.ty (.borrow true [lv]) ∧
                      FiniteEnvEqv result.env env := by
  intro hlvalComplete hmutableComplete heqvEnv hreflect htyping hmutable
    hnotWrite
  rcases hlvalComplete htyping with
    ⟨checkedTy, checkedLifetime, hchecked, heqv, _hlifetime⟩
  rcases partialTy_eqv_ty_left_inv heqv with
    ⟨checkedFullTy, hcheckedTy, _hcheckedEqv⟩
  subst hcheckedTy
  have hnotWriteFinite : ¬ WriteProhibited finite.toEnv lv :=
    not_writeProhibited_toEnv_of_finiteEnvEqv heqvEnv hnotWrite
  have hwrite : writeProhibited finite lv = false :=
    writeProhibited_complete hreflect hnotWriteFinite
  refine
    ⟨{ ty := .borrow true [lv], env := finite }, ?_,
      Ty.eqv_refl _, heqvEnv⟩
  simp [checkTerm?, hchecked, hmutableComplete hmutable, hwrite]

end PrimitiveTermCompleteness

section StructuralTermCompleteness

attribute [local simp] Bind.bind Pure.pure Except.bind Except.map Except.pure
  Functor.mapConst discard ensure fromOption

theorem checkTerm?_complete_box_of_ok
    {fuel : Nat} {env result : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    checkTerm? fuel env typing lifetime term = .ok { ty := ty, env := result } →
      checkTerm? (fuel + 1) env typing lifetime (.box term) =
        .ok { ty := .box ty, env := result } := by
  intro hterm
  simp [checkTerm?, hterm]

theorem checkTerm?_complete_box_of_ok_eqv
    {fuel : Nat} {env : FiniteEnv} {declEnv : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {checkedTy declTy : Ty} {resultEnv : FiniteEnv} :
    checkTerm? fuel env typing lifetime term =
        .ok { ty := checkedTy, env := resultEnv } →
      Ty.eqv checkedTy declTy →
        FiniteEnvEqv resultEnv declEnv →
          ∃ result,
            checkTerm? (fuel + 1) env typing lifetime (.box term) =
              .ok result ∧
            Ty.eqv result.ty (.box declTy) ∧
              FiniteEnvEqv result.env declEnv := by
  intro hterm htyEqv heqvEnv
  refine ⟨{ ty := .box checkedTy, env := resultEnv }, ?_, htyEqv, heqvEnv⟩
  simp [checkTerm?, hterm]

theorem checkTermList?_complete_singleton_of_ok
    {fuel : Nat} {env result : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    checkTerm? fuel env typing lifetime term = .ok { ty := ty, env := result } →
      checkTermList? fuel env typing lifetime [term] =
        .ok { ty := ty, env := result } := by
  intro hterm
  simp [checkTermList?, hterm]

theorem checkTermList?_complete_singleton_of_ok_eqv
    {fuel : Nat} {env resultEnv : FiniteEnv} {declEnv : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {checkedTy declTy : Ty} :
    checkTerm? fuel env typing lifetime term =
        .ok { ty := checkedTy, env := resultEnv } →
      Ty.eqv checkedTy declTy →
        FiniteEnvEqv resultEnv declEnv →
          ∃ result,
            checkTermList? fuel env typing lifetime [term] =
              .ok result ∧
            Ty.eqv result.ty declTy ∧
              FiniteEnvEqv result.env declEnv := by
  intro hterm htyEqv heqv
  refine ⟨{ ty := checkedTy, env := resultEnv }, ?_, htyEqv, heqv⟩
  simp [checkTermList?, hterm]

theorem checkTermList?_complete_cons_of_ok
    {fuel : Nat} {env mid result : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {rest : List Term}
    {termTy finalTy : Ty} :
    checkTerm? fuel env typing lifetime term = .ok { ty := termTy, env := mid } →
      checkTermList? fuel mid typing lifetime rest =
          .ok { ty := finalTy, env := result } →
        checkTermList? fuel env typing lifetime (term :: rest) =
          .ok { ty := finalTy, env := result } := by
  intro hterm hrest
  cases rest with
  | nil =>
      simp [checkTermList?] at hrest
  | cons restHead restTail =>
      simp [checkTermList?, hterm, hrest]

theorem checkTermList?_complete_cons_of_ok_eqv
    {fuel : Nat} {env mid resultEnv : FiniteEnv} {declEnv : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {rest : List Term} {termTy finalCheckedTy finalDeclTy : Ty} :
    checkTerm? fuel env typing lifetime term = .ok { ty := termTy, env := mid } →
      checkTermList? fuel mid typing lifetime rest =
          .ok { ty := finalCheckedTy, env := resultEnv } →
        Ty.eqv finalCheckedTy finalDeclTy →
          FiniteEnvEqv resultEnv declEnv →
            ∃ result,
              checkTermList? fuel env typing lifetime (term :: rest) =
                .ok result ∧
              Ty.eqv result.ty finalDeclTy ∧
                FiniteEnvEqv result.env declEnv := by
  intro hterm hrest htyEqv heqv
  refine ⟨{ ty := finalCheckedTy, env := resultEnv }, ?_, htyEqv, heqv⟩
  exact checkTermList?_complete_cons_of_ok hterm hrest

theorem checkTerm?_complete_block_of_list_ok
    {fuel : Nat} {env bodyEnv : FiniteEnv} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {terms : List Term} {ty : Ty} :
    LValCompleteAt fuel bodyEnv →
      LifetimeChild lifetime blockLifetime →
        TermListTyping env.toEnv typing blockLifetime terms ty bodyEnv.toEnv →
          WellFormedTy bodyEnv.toEnv ty lifetime →
            checkTermList? fuel env typing blockLifetime terms =
                .ok { ty := ty, env := bodyEnv } →
              checkTerm? (fuel + 1) env typing lifetime
                  (.block blockLifetime terms) =
                .ok { ty := ty, env := bodyEnv.dropLifetime blockLifetime } := by
  intro hlvalComplete hchild _hbody hwell hterms
  have hchildCheck : isLifetimeChild lifetime blockLifetime = true :=
    isLifetimeChild_complete hchild
  have hwellCheck : wellFormedTy fuel bodyEnv ty lifetime = true :=
    wellFormedTy_complete hlvalComplete hwell
  simp [checkTerm?, hchildCheck, hterms, hwellCheck]

theorem checkTerm?_complete_block_of_list_ok_eqv
    {fuel : Nat} {env bodyEnv : FiniteEnv} {bodyDeclEnv : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {checkedTy declTy : Ty} :
    LValCompleteAgainst fuel bodyEnv bodyDeclEnv →
      FiniteEnvEqv bodyEnv bodyDeclEnv →
        LifetimeChild lifetime blockLifetime →
          checkTermList? fuel env typing blockLifetime terms =
              .ok { ty := checkedTy, env := bodyEnv } →
            Ty.eqv checkedTy declTy →
              WellFormedTy bodyDeclEnv declTy lifetime →
                ∃ result,
                  checkTerm? (fuel + 1) env typing lifetime
                      (.block blockLifetime terms) =
                    .ok result ∧
                  Ty.eqv result.ty declTy ∧
                    FiniteEnvEqv result.env
                      (bodyDeclEnv.dropLifetime blockLifetime) := by
  intro hlvalComplete heqv hchild hterms htyEqv hwell
  have hchildCheck : isLifetimeChild lifetime blockLifetime = true :=
    isLifetimeChild_complete hchild
  have hwellCheck : wellFormedTy fuel bodyEnv checkedTy lifetime = true :=
    wellFormedTy_complete_against_of_eqv hlvalComplete heqv htyEqv hwell
  refine
    ⟨{ ty := checkedTy, env := bodyEnv.dropLifetime blockLifetime }, ?_,
      htyEqv, ?_⟩
  · simp [checkTerm?, hchildCheck, hterms, hwellCheck]
  · exact finiteEnvEqv_dropLifetime heqv

theorem checkTerm?_complete_letMut_of_ok
    {fuel : Nat} {env initEnv : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {name : Name} {initialiser : Term} {ty : Ty} :
    env.toEnv.fresh name →
      checkTerm? fuel env typing lifetime initialiser =
          .ok { ty := ty, env := initEnv } →
        initEnv.toEnv.fresh name →
          wellFormedKit fuel
              (initEnv.update name { ty := .ty ty, lifetime := lifetime }) =
            true →
            checkTerm? (fuel + 1) env typing lifetime
                (.letMut name initialiser) =
              .ok
                { ty := .unit,
                  env := initEnv.update name
                    { ty := .ty ty, lifetime := lifetime } } := by
  intro hfreshIn hinitialiser hfreshOut hkit
  have hfreshInCheck : env.fresh name = true :=
    fresh_complete hfreshIn
  have hfreshOutCheck : initEnv.fresh name = true :=
    fresh_complete hfreshOut
  simp [checkTerm?, hfreshInCheck, hinitialiser, hfreshOutCheck, hkit]

theorem checkTerm?_complete_letMut_of_ok_eqv
    {fuel : Nat} {env initEnv : FiniteEnv} {declEnv initDeclEnv : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {name : Name}
    {initialiser : Term} {checkedTy declTy : Ty} :
    FiniteEnvEqv env declEnv →
      FiniteEnvEqv initEnv initDeclEnv →
        declEnv.fresh name →
          checkTerm? fuel env typing lifetime initialiser =
              .ok { ty := checkedTy, env := initEnv } →
            initDeclEnv.fresh name →
              Ty.eqv checkedTy declTy →
                wellFormedKit fuel
                    (initEnv.update name
                      { ty := .ty checkedTy, lifetime := lifetime }) =
                  true →
                  ∃ result,
                    checkTerm? (fuel + 1) env typing lifetime
                        (.letMut name initialiser) =
                      .ok result ∧
                    Ty.eqv result.ty .unit ∧
                      FiniteEnvEqv result.env
                        (initDeclEnv.update name
                          { ty := .ty declTy, lifetime := lifetime }) := by
  intro heqvIn heqvInit hfreshIn hinitialiser hfreshOut htyEqv hkit
  have hfreshInCheck : env.fresh name = true :=
    fresh_complete (finiteEnvEqv_fresh_toEnv_of_fresh heqvIn hfreshIn)
  have hfreshOutCheck : initEnv.fresh name = true :=
    fresh_complete (finiteEnvEqv_fresh_toEnv_of_fresh heqvInit hfreshOut)
  refine
    ⟨{ ty := .unit,
       env := initEnv.update name
        { ty := .ty checkedTy, lifetime := lifetime } }, ?_,
      Ty.eqv_refl _, ?_⟩
  · simp [checkTerm?, hfreshInCheck, hinitialiser, hfreshOutCheck, hkit]
  · exact finiteEnvEqv_update heqvInit
      (show EnvSlotEqv
          { ty := .ty checkedTy, lifetime := lifetime }
          { ty := .ty declTy, lifetime := lifetime } from
        ⟨rfl, htyEqv⟩)

theorem checkTerm?_complete_assign_of_ok_eqv
    {fuel : Nat} {env rhsEnv written : FiniteEnv} {declEnv : Env}
    {typing : StoreTyping} {lifetime targetLifetime targetLifetimeAfter : Lifetime}
    {lhs : LVal} {rhs : Term} {oldTy oldTyAfter : PartialTy}
    {rhsCheckedTy : Ty} :
    lvalType? fuel env lhs = some (oldTy, targetLifetime) →
      checkTerm? fuel env typing lifetime rhs =
          .ok { ty := rhsCheckedTy, env := rhsEnv } →
        assignmentBorrowSafety rhsEnv lhs = true →
          lvalType? fuel rhsEnv lhs =
              some (oldTyAfter, targetLifetimeAfter) →
            oldTyAfter = oldTy →
              targetLifetimeAfter = targetLifetime →
                shapeCompatiblePartialTy fuel rhsEnv oldTy (.ty rhsCheckedTy) =
                  true →
                  wellFormedTy fuel rhsEnv rhsCheckedTy targetLifetime = true →
                    envWrite? fuel 0 rhsEnv lhs rhsCheckedTy = some written →
                      envEqOutside rhsEnv written (LVal.base lhs) = true →
                        rhsBorrowTargetsBelow rhsEnv written rhsCheckedTy =
                          true →
                          containedBorrowsWellFormed fuel written = true →
                            linearizable written = true →
                              coherentNonempty fuel written = true →
                                rootCoherent fuel written (LVal.base lhs) =
                                  true →
                                  writeProhibited written lhs = false →
                                    FiniteEnvEqv written declEnv →
                                      ∃ result,
                                        checkTerm? (fuel + 1) env typing
                                            lifetime (.assign lhs rhs) =
                                          .ok result ∧
                                        Ty.eqv result.ty .unit ∧
                                          FiniteEnvEqv result.env declEnv := by
  intro hbefore hrhs hsafe hafter holdTy hlifetime hshape hwell hwrite
    houtside hbelow hcontained hlinear hcoherent hroot hnotWrite heqv
  subst oldTyAfter
  subst targetLifetimeAfter
  refine ⟨{ ty := .unit, env := written }, ?_, Ty.eqv_refl _, heqv⟩
  simp [checkTerm?, hbefore, hrhs, hsafe, hafter, hshape, hwell, hwrite,
    houtside, hbelow, hcontained, hlinear, hcoherent, hroot, hnotWrite]

theorem checkTerm?_complete_eq_of_ok_eqv
    {fuel : Nat} {env lhsEnv rhsEnv : FiniteEnv} {rhsDeclEnv : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lhs rhs : Term}
    {lhsCheckedTy rhsCheckedTy : Ty} {ghostResult : CheckResult} :
    checkTerm? fuel env typing lifetime lhs =
        .ok { ty := lhsCheckedTy, env := lhsEnv } →
      copyTy lhsCheckedTy = true →
        wellFormedKit fuel
            (lhsEnv.update (freshGhostName lhsEnv rhs)
              { ty := .ty lhsCheckedTy, lifetime := lifetime }) =
          true →
          checkTerm? fuel
              (lhsEnv.update (freshGhostName lhsEnv rhs)
                { ty := .ty lhsCheckedTy, lifetime := lifetime })
              typing lifetime rhs =
            .ok ghostResult →
            checkTerm? fuel lhsEnv typing lifetime rhs =
                .ok { ty := rhsCheckedTy, env := rhsEnv } →
              copyTy rhsCheckedTy = true →
                shapeCompatiblePartialTy fuel rhsEnv
                    (.ty lhsCheckedTy) (.ty rhsCheckedTy) =
                  true →
                  FiniteEnvEqv rhsEnv rhsDeclEnv →
                    ∃ result,
                      checkTerm? (fuel + 1) env typing lifetime (.eq lhs rhs) =
                        .ok result ∧
                      Ty.eqv result.ty .bool ∧
                        FiniteEnvEqv result.env rhsDeclEnv := by
  intro hlhs hlhsCopy hghostKit hghost hrhs hrhsCopy hshape heqv
  refine ⟨{ ty := .bool, env := rhsEnv }, ?_, Ty.eqv_refl _, heqv⟩
  simp [checkTerm?, hlhs, hlhsCopy, freshGhostName_fresh, hghostKit,
    hghost, hrhs, hrhsCopy, hshape]

theorem checkTerm?_complete_ite_join_of_ok_eqv
    {fuel : Nat} {env conditionEnv trueEnv falseEnv joinEnv : FiniteEnv}
    {declEnv : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term}
    {trueCheckedTy falseCheckedTy joinCheckedTy declTy : Ty} :
    checkTerm? fuel env typing lifetime condition =
        .ok { ty := .bool, env := conditionEnv } →
      checkTerm? fuel conditionEnv typing lifetime trueBranch =
          .ok { ty := trueCheckedTy, env := trueEnv } →
        checkTerm? fuel conditionEnv typing lifetime falseBranch =
            .ok { ty := falseCheckedTy, env := falseEnv } →
          partialTyJoin? (.ty trueCheckedTy) (.ty falseCheckedTy) =
              some (.ty joinCheckedTy) →
            envJoin? trueEnv falseEnv = some joinEnv →
              envJoinSameShape trueEnv joinEnv = true →
                envJoinSameShape falseEnv joinEnv = true →
                  wellFormedTy fuel joinEnv joinCheckedTy lifetime = true →
                    wellFormedKit fuel joinEnv = true →
                      tyBorrowSafeAgainstEnv joinEnv joinCheckedTy = true →
                        Ty.eqv joinCheckedTy declTy →
                          FiniteEnvEqv joinEnv declEnv →
                            ∃ result,
                              checkTerm? (fuel + 1) env typing lifetime
                                  (.ite condition trueBranch falseBranch) =
                                .ok result ∧
                              Ty.eqv result.ty declTy ∧
                                FiniteEnvEqv result.env declEnv := by
  intro hcondition htrue hfalse hjoin henvJoin hsameTrue hsameFalse hwell
    hkit hsafe htyEqv heqv
  refine ⟨{ ty := joinCheckedTy, env := joinEnv }, ?_, htyEqv, heqv⟩
  simp [checkTerm?, hcondition, htrue, hfalse, hjoin, henvJoin, hsameTrue,
    hsameFalse, hwell, hkit, hsafe]

theorem checkTerm?_complete_ite_of_ok_eqv
    {fuel : Nat} {env conditionEnv trueEnv falseEnv : FiniteEnv}
    {conditionDeclEnv trueDeclEnv falseDeclEnv joinDeclEnv : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term}
    {conditionCheckedTy trueCheckedTy falseCheckedTy trueDeclTy falseDeclTy
      joinDeclTy : Ty} :
    checkTerm? fuel env typing lifetime condition =
        .ok { ty := conditionCheckedTy, env := conditionEnv } →
      Ty.eqv conditionCheckedTy .bool →
        FiniteEnvEqv conditionEnv conditionDeclEnv →
          checkTerm? fuel conditionEnv typing lifetime trueBranch =
              .ok { ty := trueCheckedTy, env := trueEnv } →
            Ty.eqv trueCheckedTy trueDeclTy →
              FiniteEnvEqv trueEnv trueDeclEnv →
                checkTerm? fuel conditionEnv typing lifetime falseBranch =
                    .ok { ty := falseCheckedTy, env := falseEnv } →
                  Ty.eqv falseCheckedTy falseDeclTy →
                    FiniteEnvEqv falseEnv falseDeclEnv →
                      PartialTyJoin (.ty trueDeclTy) (.ty falseDeclTy)
                        (.ty joinDeclTy) →
                        EnvJoin trueDeclEnv falseDeclEnv joinDeclEnv →
                          EnvJoinSameShape trueDeclEnv joinDeclEnv →
                            EnvJoinSameShape falseDeclEnv joinDeclEnv →
                              WellFormedTy joinDeclEnv joinDeclTy lifetime →
                                ContainedBorrowsWellFormed joinDeclEnv →
                                  CoherentCompleteWitness fuel joinDeclEnv →
                                    Linearizable joinDeclEnv →
                                      TyBorrowSafeAgainstEnv joinDeclEnv
                                        joinDeclTy →
                                        (∀ smaller {joinFinite},
                                          smaller ≤ fuel →
                                            envJoin? trueEnv falseEnv =
                                              some joinFinite →
                                              LValCompleteAgainst smaller
                                                joinFinite joinDeclEnv) →
                                          ∃ result,
                                            checkTerm? (fuel + 1) env typing
                                                lifetime
                                                (.ite condition trueBranch
                                                  falseBranch) =
                                              .ok result ∧
                                            Ty.eqv result.ty joinDeclTy ∧
                                              FiniteEnvEqv result.env
                                                joinDeclEnv := by
  intro hcondition hconditionEqv _heqvCondition htrue htrueEqv heqvTrue
    hfalse hfalseEqv heqvFalse htyJoin henvJoin hsameTrue hsameFalse hwell
    hcontained hcoherent hlinear hsafe hcompleteJoin
  have hconditionTy : conditionCheckedTy = .bool :=
    ty_eqv_bool_right_eq hconditionEqv
  subst conditionCheckedTy
  rcases tyJoin?_complete_of_eqv_of_partialTyJoin
      (Ty.eqv_symm htrueEqv) (Ty.eqv_symm hfalseEqv) htyJoin with
    ⟨joinCheckedTy, hcheckedJoin, hjoinEqv⟩
  rcases envJoin?_complete_against
      heqvTrue heqvFalse henvJoin hsameTrue hsameFalse with
    ⟨joinFinite, hjoinRun, heqvJoin⟩
  have hreflect : FiniteEnv.EntriesReflectLookup joinFinite :=
    envJoin?_entriesReflectLookup hjoinRun
  have hcomplete :
      ∀ smaller, smaller ≤ fuel →
        LValCompleteAgainst smaller joinFinite joinDeclEnv := by
    intro smaller hle
    exact hcompleteJoin smaller hle hjoinRun
  have hsameTrueCheck : envJoinSameShape trueEnv joinFinite = true :=
    envJoinSameShape_complete_against heqvTrue heqvJoin
      (EnvJoin.left_le henvJoin) hsameTrue
  have hsameFalseCheck : envJoinSameShape falseEnv joinFinite = true :=
    envJoinSameShape_complete_against heqvFalse heqvJoin
      (EnvJoin.right_le henvJoin) hsameFalse
  have hjoinCheckedDecl : Ty.eqv joinCheckedTy joinDeclTy :=
    Ty.eqv_symm hjoinEqv
  have hwellCheck :
      wellFormedTy fuel joinFinite joinCheckedTy lifetime = true :=
    wellFormedTy_complete_against_of_eqv
      (hcomplete fuel (Nat.le_refl fuel)) heqvJoin hjoinCheckedDecl hwell
  have hkitCheck : wellFormedKit fuel joinFinite = true :=
    wellFormedKit_complete_against_of_witness_complete
      hreflect heqvJoin hcomplete hlinear hcontained hcoherent
  have hsafeCheck :
      tyBorrowSafeAgainstEnv joinFinite joinCheckedTy = true :=
    tyBorrowSafeAgainstEnv_complete_against hreflect heqvJoin
      hjoinCheckedDecl hsafe
  exact checkTerm?_complete_ite_join_of_ok_eqv hcondition htrue hfalse
    (by simp [partialTyJoin?, hcheckedJoin]) hjoinRun hsameTrueCheck
    hsameFalseCheck hwellCheck hkitCheck hsafeCheck hjoinCheckedDecl heqvJoin

end StructuralTermCompleteness

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
Uniform statement of fuel-bound completeness on the fragment where the
executable checker is intended to be complete: no synthetic `missing`
placeholders and no loop forms.
-/
def borrowCheckCompleteOnFuelBoundCheckableTerms : Prop :=
  ∀ term,
    termContainsMissing? term = false →
      termContainsWhile? term = false →
        borrowCheckCompleteAt (termCheckerFuelBound term) term

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

/--
Contrapositive form of executable completeness.

Unlike `borrowReject_of_borrowCheckFailed?_of_completeAt`, this works for any
non-accepting boolean result, including checker outcomes currently classified
as `.unknown`.  Once fuel-bound completeness has been proved for a fragment,
`borrowCheck? = false` is enough to show logical rejection on that fragment.
-/
theorem borrowReject_of_borrowCheck?_eq_false_of_completeAt
    {fuel : Nat} {term : Term} :
    borrowCheckCompleteAt fuel term →
      borrowCheck? fuel term = false →
        borrowReject term := by
  intro hcomplete hfalse hcheck
  have htrue := hcomplete hcheck
  rw [hfalse] at htrue
  cases htrue

theorem borrowReject_of_borrowCheck?_eq_false_fuelBound
    {term : Term} :
    borrowCheckCompleteAt (termCheckerFuelBound term) term →
      borrowCheck? (termCheckerFuelBound term) term = false →
        borrowReject term :=
  borrowReject_of_borrowCheck?_eq_false_of_completeAt

theorem borrowReject_of_borrowCheck?_eq_false_fuelBound_of_checkableComplete
    (hcomplete : borrowCheckCompleteOnFuelBoundCheckableTerms)
    {term : Term} :
    termContainsMissing? term = false →
      termContainsWhile? term = false →
        borrowCheck? (termCheckerFuelBound term) term = false →
          borrowReject term := by
  intro hmissing hwhile hfalse
  exact borrowReject_of_borrowCheck?_eq_false_fuelBound
    (hcomplete term hmissing hwhile) hfalse

end Paper
end LwRust
