import LwRust.Extractor.RelaxedPreservationFacts
import LwRust.Extractor.RelaxedWellFormed

/-!
# Preservation cases for relaxed control-flow joins

This file packages the preservation proof obligation for relaxed `T-If`.
The statement is deliberately an induction-case lemma: it assumes path-sensitive
preservation hypotheses for the condition and both branches, then proves the
whole conditional without any `BorrowSafeEnv` premise for the joined
environment.
-/

namespace LwRust
namespace Paper

open Core

/--
The relaxed `T-If` preservation case.  The selected branch supplies the exact
runtime witness; the non-selected branch is used only for well-formedness of the
join.  No borrow-safety fact about the joined environment is required.
-/
theorem relaxed_preservation_ite_case
    {store finalStore : ProgramStore} {env₁ env₂ env₃ env₄ env₅ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term}
    {trueTy falseTy joinTy : Ty} {finalValue : Value} :
    SourceTerm (.ite condition trueBranch falseBranch) →
    ValidRuntimeState store (.ite condition trueBranch falseBranch) →
    ValidStoreTyping store (.ite condition trueBranch falseBranch) typing →
    WellFormedEnv env₁ lifetime →
    RuntimeExactEnvWitness store lifetime env₁ →
    RelaxedTermTyping env₁ typing lifetime condition .bool env₂ →
    RelaxedTermTyping env₂ typing lifetime trueBranch trueTy env₃ →
    RelaxedTermTyping env₂ typing lifetime falseBranch falseTy env₄ →
    PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy) →
    EnvJoin env₃ env₄ env₅ →
    EnvJoinSameShape env₃ env₅ →
    EnvJoinSameShape env₄ env₅ →
    WellFormedTy env₅ joinTy lifetime →
    Coherent env₅ →
    Linearizable env₅ →
    (∀ {storeC finalStoreC : ProgramStore} {finalValueC : Value},
      ValidRuntimeState storeC condition →
      ValidStoreTyping storeC condition typing →
      WellFormedEnv env₁ lifetime →
      RuntimeExactEnvWitness storeC lifetime env₁ →
      MultiStep storeC lifetime condition finalStoreC (.val finalValueC) →
      WellFormedEnv env₂ lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreC lifetime finalValueC
          env₂ .bool) →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT trueBranch →
      ValidStoreTyping storeT trueBranch typing →
      WellFormedEnv env₂ lifetime →
      RuntimeExactEnvWitness storeT lifetime env₂ →
      MultiStep storeT lifetime trueBranch finalStoreT (.val finalValueT) →
      WellFormedEnv env₃ lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreT lifetime finalValueT
          env₃ trueTy) →
    (∀ {storeF finalStoreF : ProgramStore} {finalValueF : Value},
      ValidRuntimeState storeF falseBranch →
      ValidStoreTyping storeF falseBranch typing →
      WellFormedEnv env₂ lifetime →
      RuntimeExactEnvWitness storeF lifetime env₂ →
      MultiStep storeF lifetime falseBranch finalStoreF (.val finalValueF) →
      WellFormedEnv env₄ lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreF lifetime finalValueF
          env₄ falseTy) →
    MultiStep store lifetime (.ite condition trueBranch falseBranch)
      finalStore (.val finalValue) →
    WellFormedEnv env₅ lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue env₅ joinTy := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hwitness
    _hcondition htrue hfalse htyJoin henvJoin hsameLeft hsameRight
    _hwellJoin hcoherent hlinear ihCondition ihTrue ihFalse hmulti
  rcases multistep_ite_to_value_inv hmulti with
    ⟨midStore, hchosen⟩
  have hsourceCondition : SourceTerm condition :=
    SourceTerm.ite_condition hsource
  have hsourceTrue : SourceTerm trueBranch :=
    SourceTerm.ite_trueBranch hsource
  have hsourceFalse : SourceTerm falseBranch :=
    SourceTerm.ite_falseBranch hsource
  have hvalidCondition : ValidRuntimeState store condition :=
    validRuntimeState_of_sourceTerm hsourceCondition hvalidRuntime
  have hstoreTypingCondition : ValidStoreTyping store condition typing :=
    hvalidStoreTyping.ite_condition
  rcases hchosen with htrueChosen | hfalseChosen
  · rcases htrueChosen with ⟨hconditionMulti, htrueMulti⟩
    rcases ihCondition hvalidCondition hstoreTypingCondition hwellFormed
        hwitness hconditionMulti with
      ⟨hwellCondition, hterminalCondition⟩
    have hvalidTrue : ValidRuntimeState midStore trueBranch :=
      validRuntimeState_of_sourceTerm hsourceTrue hterminalCondition.1.1
    have hstoreTypingTrue : ValidStoreTyping midStore trueBranch typing :=
      validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
        hvalidStoreTyping.ite_trueBranch
    rcases ihTrue hvalidTrue hstoreTypingTrue hwellCondition
        hterminalCondition.2 htrueMulti with
      ⟨hwellTrue, hterminalTrue⟩
    have hvalidFalse : ValidRuntimeState midStore falseBranch :=
      validRuntimeState_of_sourceTerm hsourceFalse hterminalCondition.1.1
    have hwellFalse : WellFormedEnv env₄ lifetime :=
      (relaxed_typingPreservesWellFormed_of_sourceTerm hsourceFalse
        hvalidFalse.1 hwellCondition
        (RuntimeExactEnvWitness.safe hterminalCondition.2) hfalse).1
    exact terminalStateSafe_ite_join_left_path htyJoin henvJoin hsameLeft
      hsameRight hcoherent hlinear hwellTrue hwellFalse hterminalTrue
  · rcases hfalseChosen with ⟨hconditionMulti, hfalseMulti⟩
    rcases ihCondition hvalidCondition hstoreTypingCondition hwellFormed
        hwitness hconditionMulti with
      ⟨hwellCondition, hterminalCondition⟩
    have hvalidFalse : ValidRuntimeState midStore falseBranch :=
      validRuntimeState_of_sourceTerm hsourceFalse hterminalCondition.1.1
    have hstoreTypingFalse : ValidStoreTyping midStore falseBranch typing :=
      validStoreTyping_sourceTerm_of_validStoreTyping hsourceFalse
        hvalidStoreTyping.ite_falseBranch
    rcases ihFalse hvalidFalse hstoreTypingFalse hwellCondition
        hterminalCondition.2 hfalseMulti with
      ⟨hwellFalse, hterminalFalse⟩
    have hvalidTrue : ValidRuntimeState midStore trueBranch :=
      validRuntimeState_of_sourceTerm hsourceTrue hterminalCondition.1.1
    have hwellTrue : WellFormedEnv env₃ lifetime :=
      (relaxed_typingPreservesWellFormed_of_sourceTerm hsourceTrue
        hvalidTrue.1 hwellCondition
        (RuntimeExactEnvWitness.safe hterminalCondition.2) htrue).1
    exact terminalStateSafe_ite_join_right_path htyJoin henvJoin hsameLeft
      hsameRight hcoherent hlinear hwellTrue hwellFalse hterminalFalse

/--
Direct local preservation wrapper for `T-If` with ordinarily typed subterms and
no joined borrow-safety premise.

This is the preservation analogue of
`relaxed_progress_ite_of_termTyping_without_join_borrow_safety`: the condition
and both branches may be ordinary strict typing derivations, while the whole
conditional is assembled through relaxed `T-If`.
-/
theorem relaxed_preservation_ite_case_of_termTyping_without_join_borrow_safety
    {store finalStore : ProgramStore} {env₁ env₂ env₃ env₄ env₅ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term}
    {trueTy falseTy joinTy : Ty} {finalValue : Value} :
    SourceTerm (.ite condition trueBranch falseBranch) →
    ValidRuntimeState store (.ite condition trueBranch falseBranch) →
    ValidStoreTyping store (.ite condition trueBranch falseBranch) typing →
    WellFormedEnv env₁ lifetime →
    RuntimeExactEnvWitness store lifetime env₁ →
    TermTyping env₁ typing lifetime condition .bool env₂ →
    TermTyping env₂ typing lifetime trueBranch trueTy env₃ →
    TermTyping env₂ typing lifetime falseBranch falseTy env₄ →
    PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy) →
    EnvJoin env₃ env₄ env₅ →
    EnvJoinSameShape env₃ env₅ →
    EnvJoinSameShape env₄ env₅ →
    WellFormedTy env₅ joinTy lifetime →
    Coherent env₅ →
    Linearizable env₅ →
    (∀ {storeC finalStoreC : ProgramStore} {finalValueC : Value},
      ValidRuntimeState storeC condition →
      ValidStoreTyping storeC condition typing →
      WellFormedEnv env₁ lifetime →
      RuntimeExactEnvWitness storeC lifetime env₁ →
      MultiStep storeC lifetime condition finalStoreC (.val finalValueC) →
      WellFormedEnv env₂ lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreC lifetime finalValueC
          env₂ .bool) →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT trueBranch →
      ValidStoreTyping storeT trueBranch typing →
      WellFormedEnv env₂ lifetime →
      RuntimeExactEnvWitness storeT lifetime env₂ →
      MultiStep storeT lifetime trueBranch finalStoreT (.val finalValueT) →
      WellFormedEnv env₃ lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreT lifetime finalValueT
          env₃ trueTy) →
    (∀ {storeF finalStoreF : ProgramStore} {finalValueF : Value},
      ValidRuntimeState storeF falseBranch →
      ValidStoreTyping storeF falseBranch typing →
      WellFormedEnv env₂ lifetime →
      RuntimeExactEnvWitness storeF lifetime env₂ →
      MultiStep storeF lifetime falseBranch finalStoreF (.val finalValueF) →
      WellFormedEnv env₄ lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreF lifetime finalValueF
          env₄ falseTy) →
    MultiStep store lifetime (.ite condition trueBranch falseBranch)
      finalStore (.val finalValue) →
    WellFormedEnv env₅ lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue env₅
        joinTy := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hwitness
    hcondition htrue hfalse htyJoin henvJoin hsameLeft hsameRight hwellJoin
    hcoherent hlinear ihCondition ihTrue ihFalse hmulti
  exact relaxed_preservation_ite_case hsource hvalidRuntime hvalidStoreTyping
    hwellFormed hwitness (TermTyping.toRelaxed hcondition)
    (TermTyping.toRelaxed htrue) (TermTyping.toRelaxed hfalse) htyJoin
    henvJoin hsameLeft hsameRight hwellJoin hcoherent hlinear ihCondition
    ihTrue ihFalse hmulti

/--
Typed relaxed `T-If` preservation case.

This is the stronger shape needed for the relaxed rule: after the condition
chooses a branch, only that branch provides the exact runtime value type.  The
proof then weakens that selected exact type to the joined approximation.
-/
theorem relaxed_preservation_ite_typed_case
    {store finalStore : ProgramStore} {env₁ env₂ env₃ env₄ env₅ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term}
    {trueTy falseTy joinTy : Ty} {finalValue : Value} :
    SourceTerm (.ite condition trueBranch falseBranch) →
    ValidRuntimeState store (.ite condition trueBranch falseBranch) →
    ValidStoreTyping store (.ite condition trueBranch falseBranch) typing →
    WellFormedEnv env₁ lifetime →
    RuntimeExactEnvWitness store lifetime env₁ →
    RelaxedTermTyping env₁ typing lifetime condition .bool env₂ →
    RelaxedTermTyping env₂ typing lifetime trueBranch trueTy env₃ →
    RelaxedTermTyping env₂ typing lifetime falseBranch falseTy env₄ →
    PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy) →
    EnvJoin env₃ env₄ env₅ →
    EnvJoinSameShape env₃ env₅ →
    EnvJoinSameShape env₄ env₅ →
    WellFormedTy env₅ joinTy lifetime →
    Coherent env₅ →
    Linearizable env₅ →
    (∀ {storeC finalStoreC : ProgramStore} {finalValueC : Value},
      ValidRuntimeState storeC condition →
      ValidStoreTyping storeC condition typing →
      WellFormedEnv env₁ lifetime →
      RuntimeExactEnvWitness storeC lifetime env₁ →
      MultiStep storeC lifetime condition finalStoreC (.val finalValueC) →
      WellFormedEnv env₂ lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreC lifetime finalValueC
          env₂ .bool) →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT trueBranch →
      ValidStoreTyping storeT trueBranch typing →
      WellFormedEnv env₂ lifetime →
      RuntimeExactEnvWitness storeT lifetime env₂ →
      MultiStep storeT lifetime trueBranch finalStoreT (.val finalValueT) →
      WellFormedEnv env₃ lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreT lifetime finalValueT
          env₃ trueTy) →
    (∀ {storeF finalStoreF : ProgramStore} {finalValueF : Value},
      ValidRuntimeState storeF falseBranch →
      ValidStoreTyping storeF falseBranch typing →
      WellFormedEnv env₂ lifetime →
      RuntimeExactEnvWitness storeF lifetime env₂ →
      MultiStep storeF lifetime falseBranch finalStoreF (.val finalValueF) →
      WellFormedEnv env₄ lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreF lifetime finalValueF
          env₄ falseTy) →
    MultiStep store lifetime (.ite condition trueBranch falseBranch)
      finalStore (.val finalValue) →
    WellFormedEnv env₅ lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue env₅
        joinTy := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hwitness
    _hcondition htrue hfalse htyJoin henvJoin hsameLeft hsameRight
    _hwellJoin hcoherent hlinear ihCondition ihTrue ihFalse hmulti
  rcases multistep_ite_to_value_inv hmulti with
    ⟨midStore, hchosen⟩
  have hsourceCondition : SourceTerm condition :=
    SourceTerm.ite_condition hsource
  have hsourceTrue : SourceTerm trueBranch :=
    SourceTerm.ite_trueBranch hsource
  have hsourceFalse : SourceTerm falseBranch :=
    SourceTerm.ite_falseBranch hsource
  have hvalidCondition : ValidRuntimeState store condition :=
    validRuntimeState_of_sourceTerm hsourceCondition hvalidRuntime
  have hstoreTypingCondition : ValidStoreTyping store condition typing :=
    hvalidStoreTyping.ite_condition
  rcases hchosen with htrueChosen | hfalseChosen
  · rcases htrueChosen with ⟨hconditionMulti, htrueMulti⟩
    rcases ihCondition hvalidCondition hstoreTypingCondition hwellFormed
        hwitness hconditionMulti with
      ⟨hwellCondition, hterminalCondition⟩
    have hwitnessCondition : RuntimeExactEnvWitness midStore lifetime env₂ :=
      RuntimeExactTypedValueWitness.to_runtime hterminalCondition.2
    have hvalidTrue : ValidRuntimeState midStore trueBranch :=
      validRuntimeState_of_sourceTerm hsourceTrue hterminalCondition.1.1
    have hstoreTypingTrue : ValidStoreTyping midStore trueBranch typing :=
      validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
        hvalidStoreTyping.ite_trueBranch
    rcases ihTrue hvalidTrue hstoreTypingTrue hwellCondition
        hwitnessCondition htrueMulti with
      ⟨hwellTrue, hterminalTrue⟩
    have hvalidFalse : ValidRuntimeState midStore falseBranch :=
      validRuntimeState_of_sourceTerm hsourceFalse hterminalCondition.1.1
    have hwellFalse : WellFormedEnv env₄ lifetime :=
      (relaxed_typingPreservesWellFormed_of_sourceTerm hsourceFalse
        hvalidFalse.1 hwellCondition
        (RuntimeExactEnvWitness.safe hwitnessCondition) hfalse).1
    exact terminalStateSafe_ite_join_left_typed htyJoin henvJoin hsameLeft
      hsameRight hcoherent hlinear hwellTrue hwellFalse hterminalTrue
  · rcases hfalseChosen with ⟨hconditionMulti, hfalseMulti⟩
    rcases ihCondition hvalidCondition hstoreTypingCondition hwellFormed
        hwitness hconditionMulti with
      ⟨hwellCondition, hterminalCondition⟩
    have hwitnessCondition : RuntimeExactEnvWitness midStore lifetime env₂ :=
      RuntimeExactTypedValueWitness.to_runtime hterminalCondition.2
    have hvalidFalse : ValidRuntimeState midStore falseBranch :=
      validRuntimeState_of_sourceTerm hsourceFalse hterminalCondition.1.1
    have hstoreTypingFalse : ValidStoreTyping midStore falseBranch typing :=
      validStoreTyping_sourceTerm_of_validStoreTyping hsourceFalse
        hvalidStoreTyping.ite_falseBranch
    rcases ihFalse hvalidFalse hstoreTypingFalse hwellCondition
        hwitnessCondition hfalseMulti with
      ⟨hwellFalse, hterminalFalse⟩
    have hvalidTrue : ValidRuntimeState midStore trueBranch :=
      validRuntimeState_of_sourceTerm hsourceTrue hterminalCondition.1.1
    have hwellTrue : WellFormedEnv env₃ lifetime :=
      (relaxed_typingPreservesWellFormed_of_sourceTerm hsourceTrue
        hvalidTrue.1 hwellCondition
        (RuntimeExactEnvWitness.safe hwitnessCondition) htrue).1
    exact terminalStateSafe_ite_join_right_typed htyJoin henvJoin hsameLeft
      hsameRight hcoherent hlinear hwellTrue hwellFalse hterminalFalse

/--
Typed local preservation wrapper for `T-If` with ordinarily typed subterms and
no joined borrow-safety premise.

The selected branch supplies the exact typed terminal witness; the joined
environment is only the static approximation.
-/
theorem
    relaxed_preservation_ite_typed_case_of_termTyping_without_join_borrow_safety
    {store finalStore : ProgramStore} {env₁ env₂ env₃ env₄ env₅ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term}
    {trueTy falseTy joinTy : Ty} {finalValue : Value} :
    SourceTerm (.ite condition trueBranch falseBranch) →
    ValidRuntimeState store (.ite condition trueBranch falseBranch) →
    ValidStoreTyping store (.ite condition trueBranch falseBranch) typing →
    WellFormedEnv env₁ lifetime →
    RuntimeExactEnvWitness store lifetime env₁ →
    TermTyping env₁ typing lifetime condition .bool env₂ →
    TermTyping env₂ typing lifetime trueBranch trueTy env₃ →
    TermTyping env₂ typing lifetime falseBranch falseTy env₄ →
    PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy) →
    EnvJoin env₃ env₄ env₅ →
    EnvJoinSameShape env₃ env₅ →
    EnvJoinSameShape env₄ env₅ →
    WellFormedTy env₅ joinTy lifetime →
    Coherent env₅ →
    Linearizable env₅ →
    (∀ {storeC finalStoreC : ProgramStore} {finalValueC : Value},
      ValidRuntimeState storeC condition →
      ValidStoreTyping storeC condition typing →
      WellFormedEnv env₁ lifetime →
      RuntimeExactEnvWitness storeC lifetime env₁ →
      MultiStep storeC lifetime condition finalStoreC (.val finalValueC) →
      WellFormedEnv env₂ lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreC lifetime finalValueC
          env₂ .bool) →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT trueBranch →
      ValidStoreTyping storeT trueBranch typing →
      WellFormedEnv env₂ lifetime →
      RuntimeExactEnvWitness storeT lifetime env₂ →
      MultiStep storeT lifetime trueBranch finalStoreT (.val finalValueT) →
      WellFormedEnv env₃ lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreT lifetime finalValueT
          env₃ trueTy) →
    (∀ {storeF finalStoreF : ProgramStore} {finalValueF : Value},
      ValidRuntimeState storeF falseBranch →
      ValidStoreTyping storeF falseBranch typing →
      WellFormedEnv env₂ lifetime →
      RuntimeExactEnvWitness storeF lifetime env₂ →
      MultiStep storeF lifetime falseBranch finalStoreF (.val finalValueF) →
      WellFormedEnv env₄ lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreF lifetime finalValueF
          env₄ falseTy) →
    MultiStep store lifetime (.ite condition trueBranch falseBranch)
      finalStore (.val finalValue) →
    WellFormedEnv env₅ lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue env₅
        joinTy := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hwitness
    hcondition htrue hfalse htyJoin henvJoin hsameLeft hsameRight hwellJoin
    hcoherent hlinear ihCondition ihTrue ihFalse hmulti
  exact relaxed_preservation_ite_typed_case hsource hvalidRuntime
    hvalidStoreTyping hwellFormed hwitness (TermTyping.toRelaxed hcondition)
    (TermTyping.toRelaxed htrue) (TermTyping.toRelaxed hfalse) htyJoin
    henvJoin hsameLeft hsameRight hwellJoin hcoherent hlinear ihCondition
    ihTrue ihFalse hmulti

/--
The relaxed `T-IfDiv` preservation case.  If the false branch is marked
diverging, any terminating execution must pass through the true branch, so the
true-branch path-sensitive induction hypothesis supplies the result directly.
-/
theorem relaxed_preservation_iteDiverging_case
    {store finalStore : ProgramStore} {env₁ env₂ env₃ env₄ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term}
    {trueTy falseTy : Ty} {finalValue : Value} :
    SourceTerm (.ite condition trueBranch falseBranch) →
    ValidRuntimeState store (.ite condition trueBranch falseBranch) →
    ValidStoreTyping store (.ite condition trueBranch falseBranch) typing →
    WellFormedEnv env₁ lifetime →
    RuntimeExactEnvWitness store lifetime env₁ →
    RelaxedTermTyping env₁ typing lifetime condition .bool env₂ →
    RelaxedTermTyping env₂ typing lifetime trueBranch trueTy env₃ →
    RelaxedTermTyping env₂ typing lifetime falseBranch falseTy env₄ →
    falseBranch.Diverges →
    (∀ {storeC finalStoreC : ProgramStore} {finalValueC : Value},
      ValidRuntimeState storeC condition →
      ValidStoreTyping storeC condition typing →
      WellFormedEnv env₁ lifetime →
      RuntimeExactEnvWitness storeC lifetime env₁ →
      MultiStep storeC lifetime condition finalStoreC (.val finalValueC) →
      WellFormedEnv env₂ lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreC lifetime finalValueC
          env₂ .bool) →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT trueBranch →
      ValidStoreTyping storeT trueBranch typing →
      WellFormedEnv env₂ lifetime →
      RuntimeExactEnvWitness storeT lifetime env₂ →
      MultiStep storeT lifetime trueBranch finalStoreT (.val finalValueT) →
      WellFormedEnv env₃ lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreT lifetime finalValueT
          env₃ trueTy) →
    MultiStep store lifetime (.ite condition trueBranch falseBranch)
      finalStore (.val finalValue) →
    WellFormedEnv env₃ lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue env₃ trueTy := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hwitness
    _hcondition _htrue _hfalse hdiverges ihCondition ihTrue hmulti
  rcases multistep_ite_to_value_inv hmulti with
    ⟨midStore, hchosen⟩
  have hsourceCondition : SourceTerm condition :=
    SourceTerm.ite_condition hsource
  have hsourceTrue : SourceTerm trueBranch :=
    SourceTerm.ite_trueBranch hsource
  have hvalidCondition : ValidRuntimeState store condition :=
    validRuntimeState_of_sourceTerm hsourceCondition hvalidRuntime
  have hstoreTypingCondition : ValidStoreTyping store condition typing :=
    hvalidStoreTyping.ite_condition
  rcases hchosen with htrueChosen | hfalseChosen
  · rcases htrueChosen with ⟨hconditionMulti, htrueMulti⟩
    rcases ihCondition hvalidCondition hstoreTypingCondition hwellFormed
        hwitness hconditionMulti with
      ⟨hwellCondition, hterminalCondition⟩
    have hvalidTrue : ValidRuntimeState midStore trueBranch :=
      validRuntimeState_of_sourceTerm hsourceTrue hterminalCondition.1.1
    have hstoreTypingTrue : ValidStoreTyping midStore trueBranch typing :=
      validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
        hvalidStoreTyping.ite_trueBranch
    exact ihTrue hvalidTrue hstoreTypingTrue hwellCondition
      hterminalCondition.2 htrueMulti
  · rcases hfalseChosen with ⟨_hconditionMulti, hfalseMulti⟩
    exact False.elim (diverges_multistep_not_value hdiverges hfalseMulti)

/--
The singleton block preservation case for path-sensitive relaxed preservation.

The block/drop mechanics are discharged by
`PathSensitiveTerminalStateSafe.block_value_drop`.  The explicit
`hwellTyExact` premise records the remaining exact/approx obligation: after the
body finishes, the block result type must be well formed in the exact runtime
environment carried by the selected path.
-/
theorem relaxed_preservation_block_singleton_case
    {store finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm (.block blockLifetime [term]) →
    ValidRuntimeState store (.block blockLifetime [term]) →
    ValidStoreTyping store (.block blockLifetime [term]) typing →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₁ blockLifetime →
    RuntimeExactEnvWitness store blockLifetime env₁ →
    RelaxedTermTyping env₁ typing blockLifetime term ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT term →
      ValidStoreTyping storeT term typing →
      WellFormedEnv env₁ blockLifetime →
      RuntimeExactEnvWitness storeT blockLifetime env₁ →
      MultiStep storeT blockLifetime term finalStoreT (.val finalValueT) →
      WellFormedEnv env₂ blockLifetime ∧
        PathSensitiveTerminalStateSafe finalStoreT blockLifetime finalValueT
          env₂ ty) →
    (∀ {storeV : ProgramStore} {valueV : Value} {exactEnv : Env},
      PathSensitiveTerminalStateSafe storeV blockLifetime valueV env₂ ty →
      WellFormedEnv exactEnv blockLifetime →
      BorrowSafeEnv exactEnv →
      storeV ∼ₛ exactEnv →
      EnvSameShapeStrengthening exactEnv env₂ →
      WellFormedTy exactEnv ty lifetime) →
    MultiStep store lifetime (.block blockLifetime [term])
      finalStore (.val finalValue) →
    WellFormedEnv env₃ lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue env₃ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hchild hwellFormed hwitness
    _hterm hwellTy henv₃ ihTerm hwellTyExact hmulti
  subst henv₃
  rcases multistep_block_head_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
  have hsourceHead : SourceTerm term :=
    SourceTerm.block_head hsource
  rcases ihTerm
      (validRuntimeState_block_singleton_inner hvalidRuntime)
      (validStoreTyping_block_singleton_inner hvalidStoreTyping)
      hwellFormed hwitness hinnerMulti with
    ⟨hwellInner, hterminalInner⟩
  rcases Env.dropLifetime_preserves_wellFormed_child
      hchild hwellInner hwellTy rfl with
    ⟨hwellDrop, _hwellTyDrop⟩
  have hvalidBlockValue :
      ValidRuntimeState midStore (.block blockLifetime [.val value]) :=
    validRuntimeState_block_singleton_value_of_value hterminalInner.1.1
  have hterminalDrop :
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue
        (env₂.dropLifetime blockLifetime) ty :=
    PathSensitiveTerminalStateSafe.block_value_drop
      hterminalInner hvalidBlockValue hchild hwellInner hwellTy
      (by
        intro exactEnv hwellExact hborrowExact hsafeExact hmapExactApprox
        exact hwellTyExact hterminalInner hwellExact hborrowExact
          hsafeExact hmapExactApprox)
      hblockValueMulti
  exact ⟨hwellDrop, hterminalDrop⟩

/--
Typed singleton block preservation.

This uses the selected exact value type for the final `R-BlockB` step and then
weakens the terminal result to the approximate post-drop environment.  The
remaining block-specific side condition is only parent-lifetime well-formedness
of that selected exact result type.
-/
theorem relaxed_preservation_block_singleton_typed_case
    {store finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm (.block blockLifetime [term]) →
    ValidRuntimeState store (.block blockLifetime [term]) →
    ValidStoreTyping store (.block blockLifetime [term]) typing →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₁ blockLifetime →
    RuntimeExactEnvWitness store blockLifetime env₁ →
    RelaxedTermTyping env₁ typing blockLifetime term ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT term →
      ValidStoreTyping storeT term typing →
      WellFormedEnv env₁ blockLifetime →
      RuntimeExactEnvWitness storeT blockLifetime env₁ →
      MultiStep storeT blockLifetime term finalStoreT (.val finalValueT) →
      WellFormedEnv env₂ blockLifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreT blockLifetime
          finalValueT env₂ ty) →
    (∀ {storeV : ProgramStore} {valueV : Value}
        {exactEnv : Env} {exactTy : Ty},
      PathSensitiveTypedTerminalStateSafe storeV blockLifetime valueV env₂ ty →
      WellFormedEnv exactEnv blockLifetime →
      BorrowSafeEnv exactEnv →
      storeV ∼ₛ exactEnv →
      EnvSameShapeStrengthening exactEnv env₂ →
      PartialTyStrengthens (.ty exactTy) (.ty ty) →
      ValidValue storeV valueV exactTy →
      WellFormedTy exactEnv exactTy blockLifetime →
      TyBorrowSafeAgainstEnv exactEnv exactTy →
      WellFormedTy exactEnv exactTy lifetime) →
    MultiStep store lifetime (.block blockLifetime [term])
      finalStore (.val finalValue) →
    WellFormedEnv env₃ lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue env₃
        ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hchild hwellFormed hwitness
    _hterm hwellTy henv₃ ihTerm hwellTyExact hmulti
  subst henv₃
  rcases multistep_block_head_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
  rcases ihTerm
      (validRuntimeState_block_singleton_inner hvalidRuntime)
      (validStoreTyping_block_singleton_inner hvalidStoreTyping)
      hwellFormed hwitness hinnerMulti with
    ⟨hwellInner, hterminalInner⟩
  rcases Env.dropLifetime_preserves_wellFormed_child
      hchild hwellInner hwellTy rfl with
    ⟨hwellDrop, _hwellTyDrop⟩
  have hvalidBlockValue :
      ValidRuntimeState midStore (.block blockLifetime [.val value]) :=
    validRuntimeState_block_singleton_value_of_value hterminalInner.1.1
  have hterminalDrop :
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        (env₂.dropLifetime blockLifetime) ty :=
    PathSensitiveTypedTerminalStateSafe.block_value_drop
      hterminalInner hvalidBlockValue hchild hwellInner hwellTy
      (by
        intro exactEnv exactTy hwellExact hborrowExact hsafeExact
          hmapExactApprox hstrength hvalidExact hwellTyExactBlock
          hsafeTyExact
        exact hwellTyExact hterminalInner hwellExact hborrowExact
          hsafeExact hmapExactApprox hstrength hvalidExact
          hwellTyExactBlock hsafeTyExact)
      hblockValueMulti
  exact ⟨hwellDrop, hterminalDrop⟩

/--
Hook-packaged typed singleton block preservation.

The theorem is definitionally the same as
`relaxed_preservation_block_singleton_typed_case`, but the parent-lifetime
exact-type obligation is exposed through `TypedBlockResultWellFormedHook`.
-/
theorem relaxed_preservation_block_singleton_typed_case_of_hook
    {store finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm (.block blockLifetime [term]) →
    ValidRuntimeState store (.block blockLifetime [term]) →
    ValidStoreTyping store (.block blockLifetime [term]) typing →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₁ blockLifetime →
    RuntimeExactEnvWitness store blockLifetime env₁ →
    RelaxedTermTyping env₁ typing blockLifetime term ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT term →
      ValidStoreTyping storeT term typing →
      WellFormedEnv env₁ blockLifetime →
      RuntimeExactEnvWitness storeT blockLifetime env₁ →
      MultiStep storeT blockLifetime term finalStoreT (.val finalValueT) →
      WellFormedEnv env₂ blockLifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreT blockLifetime
          finalValueT env₂ ty) →
    TypedBlockResultWellFormedHook blockLifetime lifetime env₂ ty →
    MultiStep store lifetime (.block blockLifetime [term])
      finalStore (.val finalValue) →
    WellFormedEnv env₃ lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue env₃
        ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hchild hwellFormed hwitness
    hterm hwellTy henv₃ ihTerm hwellTyExact hmulti
  exact relaxed_preservation_block_singleton_typed_case
    hsource hvalidRuntime hvalidStoreTyping hchild hwellFormed hwitness hterm
    hwellTy henv₃ ihTerm
    (by
      intro storeV valueV exactEnv exactTy hsafeTyped hwellExact
        hborrowExact hsafeExact hmapExactApprox hstrength hvalidExact
        hwellTyExactBlock hsafeTyExact
      exact hwellTyExact hsafeTyped hwellExact hborrowExact hsafeExact
        hmapExactApprox hstrength hvalidExact hwellTyExactBlock hsafeTyExact)
    hmulti

/--
The nonempty sequence block case for path-sensitive relaxed preservation.  After
the head term terminates, `R-Seq` drops the head value; the exact runtime witness
is preserved by `RuntimeExactEnvWitness.seq_value_drop`, and the tail block IH
continues with the same approximate environment `env₂`.
-/
theorem relaxed_preservation_block_cons_case
    {store finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {term next : Term} {restTail : List Term}
    {termTy finalTy : Ty} {finalValue : Value} :
    SourceTerm (.block blockLifetime (term :: next :: restTail)) →
    ValidRuntimeState store (.block blockLifetime (term :: next :: restTail)) →
    ValidStoreTyping store (.block blockLifetime (term :: next :: restTail))
      typing →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₁ blockLifetime →
    RuntimeExactEnvWitness store blockLifetime env₁ →
    RelaxedTermTyping env₁ typing blockLifetime term termTy env₂ →
    RelaxedTermListTyping env₂ typing blockLifetime (next :: restTail)
      finalTy env₃ →
    WellFormedTy env₃ finalTy lifetime →
    (∀ {storeH finalStoreH : ProgramStore} {finalValueH : Value},
      ValidRuntimeState storeH term →
      ValidStoreTyping storeH term typing →
      WellFormedEnv env₁ blockLifetime →
      RuntimeExactEnvWitness storeH blockLifetime env₁ →
      MultiStep storeH blockLifetime term finalStoreH (.val finalValueH) →
      WellFormedEnv env₂ blockLifetime ∧
        PathSensitiveTerminalStateSafe finalStoreH blockLifetime finalValueH
          env₂ termTy) →
    (∀ {storeTail finalStoreTail : ProgramStore} {finalValueTail : Value},
      LifetimeChild lifetime blockLifetime →
      ValidRuntimeState storeTail (.block blockLifetime (next :: restTail)) →
      ValidStoreTyping storeTail (.block blockLifetime (next :: restTail))
        typing →
      WellFormedEnv env₂ blockLifetime →
      RuntimeExactEnvWitness storeTail blockLifetime env₂ →
      WellFormedTy env₃ finalTy lifetime →
      MultiStep storeTail lifetime (.block blockLifetime (next :: restTail))
        finalStoreTail (.val finalValueTail) →
      WellFormedEnv (env₃.dropLifetime blockLifetime) lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreTail lifetime finalValueTail
          (env₃.dropLifetime blockLifetime) finalTy) →
    MultiStep store lifetime (.block blockLifetime (term :: next :: restTail))
      finalStore (.val finalValue) →
    WellFormedEnv (env₃.dropLifetime blockLifetime) lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue
        (env₃.dropLifetime blockLifetime) finalTy := by
  intro hsource hvalidRuntime hvalidStoreTyping hchild hwellFormed hwitness
    _hterm _hrest hwellTy ihHead ihRest hmulti
  have hsourceHead : SourceTerm term :=
    SourceTerm.block_head hsource
  have hsourceTail : SourceTerm (.block blockLifetime (next :: restTail)) :=
    SourceTerm.block_tail hsource
  rcases multistep_block_head_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
  rcases ihHead
      (validRuntimeState_block_head hvalidRuntime)
      (validStoreTyping_block_head hvalidStoreTyping)
      hwellFormed hwitness hinnerMulti with
    ⟨hwellInner, hterminalInner⟩
  have hvalueBlockValid :
      ValidRuntimeState midStore
        (.block blockLifetime (.val value :: next :: restTail)) :=
    validRuntimeState_block_value_cons_of_value_source_tail
      hsourceTail hterminalInner.1.1
  have htailStoreTypingAtMid :
      ValidStoreTyping midStore (.block blockLifetime (next :: restTail))
        typing :=
    validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
      (validStoreTyping_block_tail_of_cons hvalidStoreTyping)
  rcases multistep_block_to_value_first_step_inv hblockValueMulti with
    hseqCase | hblockACase | hblockBCase
  · rcases hseqCase with
      ⟨seqValue, seqNext, seqRest, storeAfter, hterms, hdrops, htailMulti⟩
    cases hterms
    have hseqStep :
        Step midStore lifetime
          (.block blockLifetime (.val value :: next :: restTail))
          storeAfter (.block blockLifetime (next :: restTail)) :=
      Step.seq hdrops
    have hvalidTailAfter :
        ValidRuntimeState storeAfter (.block blockLifetime (next :: restTail)) :=
      validRuntimeState_seq_step hvalueBlockValid hseqStep
    have hwitnessTailAfter :
        RuntimeExactEnvWitness storeAfter blockLifetime env₂ :=
      RuntimeExactEnvWitness.seq_value_drop hterminalInner.2
        hvalueBlockValid hdrops
    have htailStoreTyping :
        ValidStoreTyping storeAfter (.block blockLifetime (next :: restTail))
          typing :=
      validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
        htailStoreTypingAtMid
    exact ihRest hchild hvalidTailAfter htailStoreTyping hwellInner
      hwitnessTailAfter hwellTy htailMulti
  · rcases hblockACase with
      ⟨blockTerm, blockRest, storeAfter, termAfter, hterms, hstep,
        _htailMulti⟩
    cases hterms
    exact False.elim (value_no_step hstep)
  · rcases hblockBCase with
      ⟨blockValue, storeAfter, hterms, _hdrops, _htailMulti⟩
    cases hterms

/--
Typed nonempty sequence block preservation.

The head term's typed terminal witness is only needed to recover the runtime
exact environment after `R-Seq`; the typed result for the whole block is supplied
by the tail block IH.
-/
theorem relaxed_preservation_block_cons_typed_case
    {store finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {term next : Term} {restTail : List Term}
    {termTy finalTy : Ty} {finalValue : Value} :
    SourceTerm (.block blockLifetime (term :: next :: restTail)) →
    ValidRuntimeState store (.block blockLifetime (term :: next :: restTail)) →
    ValidStoreTyping store (.block blockLifetime (term :: next :: restTail))
      typing →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₁ blockLifetime →
    RuntimeExactEnvWitness store blockLifetime env₁ →
    RelaxedTermTyping env₁ typing blockLifetime term termTy env₂ →
    RelaxedTermListTyping env₂ typing blockLifetime (next :: restTail)
      finalTy env₃ →
    WellFormedTy env₃ finalTy lifetime →
    (∀ {storeH finalStoreH : ProgramStore} {finalValueH : Value},
      ValidRuntimeState storeH term →
      ValidStoreTyping storeH term typing →
      WellFormedEnv env₁ blockLifetime →
      RuntimeExactEnvWitness storeH blockLifetime env₁ →
      MultiStep storeH blockLifetime term finalStoreH (.val finalValueH) →
      WellFormedEnv env₂ blockLifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreH blockLifetime
          finalValueH env₂ termTy) →
    (∀ {storeTail finalStoreTail : ProgramStore} {finalValueTail : Value},
      LifetimeChild lifetime blockLifetime →
      ValidRuntimeState storeTail (.block blockLifetime (next :: restTail)) →
      ValidStoreTyping storeTail (.block blockLifetime (next :: restTail))
        typing →
      WellFormedEnv env₂ blockLifetime →
      RuntimeExactEnvWitness storeTail blockLifetime env₂ →
      WellFormedTy env₃ finalTy lifetime →
      MultiStep storeTail lifetime (.block blockLifetime (next :: restTail))
        finalStoreTail (.val finalValueTail) →
      WellFormedEnv (env₃.dropLifetime blockLifetime) lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreTail lifetime
          finalValueTail (env₃.dropLifetime blockLifetime) finalTy) →
    MultiStep store lifetime (.block blockLifetime (term :: next :: restTail))
      finalStore (.val finalValue) →
    WellFormedEnv (env₃.dropLifetime blockLifetime) lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        (env₃.dropLifetime blockLifetime) finalTy := by
  intro hsource hvalidRuntime hvalidStoreTyping hchild hwellFormed hwitness
    _hterm _hrest hwellTy ihHead ihRest hmulti
  have hsourceTail : SourceTerm (.block blockLifetime (next :: restTail)) :=
    SourceTerm.block_tail hsource
  rcases multistep_block_head_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
  rcases ihHead
      (validRuntimeState_block_head hvalidRuntime)
      (validStoreTyping_block_head hvalidStoreTyping)
      hwellFormed hwitness hinnerMulti with
    ⟨hwellInner, hterminalInner⟩
  have hvalueBlockValid :
      ValidRuntimeState midStore
        (.block blockLifetime (.val value :: next :: restTail)) :=
    validRuntimeState_block_value_cons_of_value_source_tail
      hsourceTail hterminalInner.1.1
  have htailStoreTypingAtMid :
      ValidStoreTyping midStore (.block blockLifetime (next :: restTail))
        typing :=
    validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
      (validStoreTyping_block_tail_of_cons hvalidStoreTyping)
  rcases multistep_block_to_value_first_step_inv hblockValueMulti with
    hseqCase | hblockACase | hblockBCase
  · rcases hseqCase with
      ⟨seqValue, seqNext, seqRest, storeAfter, hterms, hdrops, htailMulti⟩
    cases hterms
    have hseqStep :
        Step midStore lifetime
          (.block blockLifetime (.val value :: next :: restTail))
          storeAfter (.block blockLifetime (next :: restTail)) :=
      Step.seq hdrops
    have hvalidTailAfter :
        ValidRuntimeState storeAfter (.block blockLifetime (next :: restTail)) :=
      validRuntimeState_seq_step hvalueBlockValid hseqStep
    have hwitnessTailAfter :
        RuntimeExactEnvWitness storeAfter blockLifetime env₂ :=
      RuntimeExactEnvWitness.seq_value_drop
        (RuntimeExactTypedValueWitness.to_runtime hterminalInner.2)
        hvalueBlockValid hdrops
    have htailStoreTyping :
        ValidStoreTyping storeAfter (.block blockLifetime (next :: restTail))
          typing :=
      validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
        htailStoreTypingAtMid
    exact ihRest hchild hvalidTailAfter htailStoreTyping hwellInner
      hwitnessTailAfter hwellTy htailMulti
  · rcases hblockACase with
      ⟨blockTerm, blockRest, storeAfter, termAfter, hterms, hstep,
        _htailMulti⟩
    cases hterms
    exact False.elim (value_no_step hstep)
  · rcases hblockBCase with
      ⟨blockValue, storeAfter, hterms, _hdrops, _htailMulti⟩
    cases hterms

end Paper
end LwRust
