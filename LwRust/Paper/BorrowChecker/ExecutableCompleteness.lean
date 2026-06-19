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
                have hfits : lvalFitsFuel fuel lhs = true :=
                  lvalFitsFuel_of_lvalCheckerFuelBound_lt (by omega)
                simp [checkTerm?, fromOption, lvalTypeOrError?, hleft,
                  hfits]
            | some before =>
                rcases before with ⟨oldTy, targetLifetime⟩
                cases hcheck : checkTerm? fuel env typing lifetime rhs with
                | error message =>
                    have hmessage :=
                      check_error_ne_fuelExhausted hcheck hrhs
                    simp [checkTerm?, fromOption, hleft, hcheck, hmessage]
                | ok rhsResult =>
                    cases hafter :
                        lvalType? fuel rhsResult.env lhs with
                      | none =>
                          have hfits : lvalFitsFuel fuel lhs = true :=
                            lvalFitsFuel_of_lvalCheckerFuelBound_lt
                              (by omega)
                          simp [checkTerm?, fromOption, ensure, hleft, hcheck,
                            hafter, lvalTypeOrError?, hfits]
                      | some after =>
                          rcases after with ⟨oldTyAfter, targetLifetimeAfter⟩
                          cases holdTy :
                              decide (oldTyAfter = oldTy)
                          · simp [checkTerm?, fromOption, ensure, hleft,
                              hcheck, hafter, holdTy]
                          · cases hlifetime :
                                decide (targetLifetimeAfter = targetLifetime)
                            · simp [checkTerm?, fromOption, ensure, hleft,
                                hcheck, hafter, holdTy, hlifetime]
                            · cases hshape :
                                  shapeCompatiblePartialTy fuel rhsResult.env
                                    oldTy (.ty rhsResult.ty)
                              · simp [checkTerm?, fromOption, ensure, hleft,
                                  hcheck, hafter, holdTy, hlifetime,
                                  hshape]
                              · cases hwell :
                                    wellFormedTy fuel rhsResult.env
                                      rhsResult.ty targetLifetime
                                · simp [checkTerm?, fromOption, ensure, hleft,
                                    hcheck, hafter, holdTy, hlifetime,
                                    hshape, hwell]
                                · cases hwrite :
                                      envWrite? fuel 0 rhsResult.env lhs
                                        rhsResult.ty with
                                  | none =>
                                      simp [checkTerm?, fromOption, ensure,
                                        hleft, hcheck, hafter, holdTy,
                                        hlifetime, hshape, hwell, hwrite]
                                  | some written =>
                                      cases houtside :
                                          envEqOutside rhsResult.env written
                                            (LVal.base lhs) with
                                      | false =>
                                          simp [checkTerm?, fromOption, ensure,
                                            hleft, hcheck, hafter,
                                            holdTy, hlifetime, hshape, hwell,
                                            hwrite, houtside]
                                      | true =>
                                          cases hbelow :
                                              rhsBorrowTargetsBelow rhsResult.env
                                                written rhsResult.ty with
                                          | false =>
                                              simp [checkTerm?, fromOption,
                                                ensure, hleft, hcheck,
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
                                                  ensure, hleft, hcheck,
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
                have hfits : lvalFitsFuel fuel lv = true :=
                  lvalFitsFuel_of_lvalCheckerFuelBound_lt (by
                    simp [termCheckerFuelBound] at hbound
                    omega)
                simp [checkTerm?, fromOption, lvalTypeOrError?, htype,
                  hfits]
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
                have hfits : lvalFitsFuel fuel lv = true :=
                  lvalFitsFuel_of_lvalCheckerFuelBound_lt (by
                    simp [termCheckerFuelBound] at hbound
                    omega)
                simp [checkTerm?, fromOption, lvalTypeOrError?, htype,
                  hfits]
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
                have hfits : lvalFitsFuel fuel lv = true :=
                  lvalFitsFuel_of_lvalCheckerFuelBound_lt (by
                    simp [termCheckerFuelBound] at hbound
                    omega)
                simp [checkTerm?, fromOption, lvalTypeOrError?, htype,
                  hfits]
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

theorem checkTermList?_complete_singleton_of_ok
    {fuel : Nat} {env result : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    checkTerm? fuel env typing lifetime term = .ok { ty := ty, env := result } →
      checkTermList? fuel env typing lifetime [term] =
        .ok { ty := ty, env := result } := by
  intro hterm
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
