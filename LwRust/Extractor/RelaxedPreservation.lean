import LwRust.Extractor.RelaxedPreservationFrontier

/-!
# Top-level preservation skeleton for relaxed `T-If`

This file assembles the checked relaxed preservation cases into a recursive
preservation theorem shape.  The theorem is path-sensitive: runtime safety is
carried by an exact selected environment that strengthens to the static
approximation.
-/

namespace LwRust
namespace Paper

open Core

/--
Non-control-flow obligations for untyped path-sensitive relaxed preservation.

There is deliberately no `ite` field.  The relaxed `T-If` case itself is closed
by `relaxed_preservation_ite_case` without `BorrowSafeEnv` or
`TyBorrowSafeAgainstEnv` for the joined environment.
-/
structure RelaxedPreservationHooks : Prop where
  move {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {store : ProgramStore} {approxIn approxOut : Env} :
      RuntimeExactEnvWitness store lifetime approxIn →
      WellFormedEnv approxIn lifetime →
      LValTyping approxIn lv (.ty ty) valueLifetime →
      ¬ WriteProhibited approxIn lv →
      EnvMove approxIn lv approxOut →
      ∀ exactIn,
        WellFormedEnv exactIn lifetime →
        BorrowSafeEnv exactIn →
        store ∼ₛ exactIn →
        EnvSameShapeStrengthening exactIn approxIn →
        ∃ exactOut exactTy valueLifetime,
          ExactMoveTransport lifetime lv ty exactTy exactIn exactOut
            approxOut valueLifetime
  declare {lifetime : Lifetime} {x : Name} {ty : Ty}
    {storeV storeAfter : ProgramStore} {value finalValueV : Value}
    {approxInit approxOut : Env} :
      PathSensitiveTerminalStateSafe storeV lifetime value approxInit ty →
      ValidRuntimeState storeV (.letMut x (.val value)) →
      Step storeV lifetime (.letMut x (.val value)) storeAfter
        (.val finalValueV) →
      ∀ exactIn,
        WellFormedEnv exactIn lifetime →
        BorrowSafeEnv exactIn →
        storeV ∼ₛ exactIn →
        EnvSameShapeStrengthening exactIn approxInit →
        ∃ exactTy,
          ValidValue storeV value exactTy ∧
            ExactDeclareTransport lifetime x ty exactTy exactIn approxOut
  assign {lifetime : Lifetime} {lhs : LVal} {rhsTy : Ty}
    {storeV storeAfter : ProgramStore} {value finalValueV : Value}
    {approxRhs approxOut : Env} :
      PathSensitiveTerminalStateSafe storeV lifetime value approxRhs rhsTy →
      ValidRuntimeState storeV (.assign lhs (.val value)) →
      Step storeV lifetime (.assign lhs (.val value)) storeAfter
        (.val finalValueV) →
      ∀ exactIn,
        WellFormedEnv exactIn lifetime →
        BorrowSafeEnv exactIn →
        storeV ∼ₛ exactIn →
        EnvSameShapeStrengthening exactIn approxRhs →
        ∃ exactOut oldTy targetLifetime rhsWellLifetime,
          ExactAssignTransport lifetime lhs rhsTy exactIn exactOut approxOut
            oldTy targetLifetime rhsWellLifetime
  blockResult {blockLifetime parentLifetime : Lifetime}
    {storeV : ProgramStore} {valueV : Value} {approxEnv : Env} {ty : Ty}
    {exactEnv : Env} :
      PathSensitiveTerminalStateSafe storeV blockLifetime valueV approxEnv ty →
      WellFormedEnv exactEnv blockLifetime →
      BorrowSafeEnv exactEnv →
      storeV ∼ₛ exactEnv →
      EnvSameShapeStrengthening exactEnv approxEnv →
      WellFormedTy exactEnv ty parentLifetime

theorem relaxed_preservation_bounded_with_hooks
    (hooks : RelaxedPreservationHooks) (fuel : Nat)
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    term.size ≤ fuel →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    RuntimeExactEnvWitness store lifetime env₁ →
    RelaxedTermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    WellFormedEnv env₂ lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue env₂ ty := by
  induction fuel generalizing store finalStore env₁ env₂ typing lifetime term ty
      finalValue with
  | zero =>
      intro hsize _hsource _hvalidRuntime _hvalidStoreTyping _hwellFormed
        _hwitness _htyping _hmulti
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
      intro hsize hsource hvalidRuntime hvalidStoreTyping hwellFormed
        hwitness htyping hmulti
      refine
        (RelaxedTermTyping.rec
          (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
            term.size ≤ fuel.succ →
            currentTyping = typing →
            SourceTerm term →
            ∀ (store finalStore : ProgramStore) (finalValue : Value),
              ValidRuntimeState store term →
              ValidStoreTyping store term currentTyping →
              WellFormedEnv env lifetime →
              RuntimeExactEnvWitness store lifetime env →
              MultiStep store lifetime term finalStore (.val finalValue) →
              WellFormedEnv env₂ lifetime ∧
                PathSensitiveTerminalStateSafe finalStore lifetime finalValue
                  env₂ ty)
          (motive_2 := fun env currentTyping blockLifetime terms ty env₂ _ =>
            Term.size (.block blockLifetime terms) ≤ fuel.succ →
            currentTyping = typing →
            SourceTerm (.block blockLifetime terms) →
            ∀ (outerLifetime : Lifetime) (store finalStore : ProgramStore)
              (finalValue : Value),
              LifetimeChild outerLifetime blockLifetime →
              ValidRuntimeState store (.block blockLifetime terms) →
              ValidStoreTyping store (.block blockLifetime terms)
                currentTyping →
              WellFormedEnv env blockLifetime →
              RuntimeExactEnvWitness store blockLifetime env →
              WellFormedTy env₂ ty outerLifetime →
              MultiStep store outerLifetime (.block blockLifetime terms)
                finalStore (.val finalValue) →
              WellFormedEnv (env₂.dropLifetime blockLifetime)
                  outerLifetime ∧
                PathSensitiveTerminalStateSafe finalStore outerLifetime
                  finalValue (env₂.dropLifetime blockLifetime) ty)
          ?constCase ?missingCase ?copyCase ?moveCase ?mutBorrowCase
          ?immBorrowCase ?boxCase ?blockCase ?declareCase ?assignCase ?eqCase
          ?iteCase ?iteDivergingCase ?singletonCase ?consCase htyping hsize
          rfl hsource store finalStore
          finalValue hvalidRuntime hvalidStoreTyping hwellFormed hwitness
          hmulti)
      case constCase =>
        intro _env _typing _lifetime _value _ty hvalueTyping _hsize
          htypingEq _hsource store finalStore finalValue hvalidRuntime
          hvalidStoreTyping hwellFormed hwitness hmulti
        cases htypingEq
        have htermTyping :
            TermTyping _env typing _lifetime (.val _value) _ty _env :=
          TermTyping.const hvalueTyping
        have hterminal :
            TerminalStateSafe finalStore finalValue _env _ty :=
          preservation_multistep_runtime_value hvalidRuntime
            hvalidStoreTyping (RuntimeExactEnvWitness.safe hwitness)
            htermTyping hmulti
        rcases multistep_value_inv hmulti with ⟨hstoreEq, _htermEq⟩
        exact ⟨hwellFormed,
          ⟨hterminal, RuntimeExactEnvWitness.of_store_eq hstoreEq hwitness⟩⟩
      case missingCase =>
        intro _env _typing _lifetime _ty _hwellTy _hloanFree _hsize
          _htypingEq _hsource _store _finalStore _finalValue
          _hvalidRuntime _hvalidStoreTyping _hwellFormed _hwitness hmulti
        exact False.elim (multistep_missing_not_value hmulti)
      case copyCase =>
        intro _env _typing _lifetime _valueLifetime _lv _ty hLv hcopy
          hnotRead _hsize htypingEq _hsource store finalStore finalValue
          hvalidRuntime _hvalidStoreTyping hwellFormed hwitness hmulti
        cases htypingEq
        exact ⟨hwellFormed,
          pathSensitive_copy_case (typing := typing) hwellFormed hwitness
            hvalidRuntime hLv hcopy hnotRead hmulti⟩
      case moveCase =>
        intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty hLv
          hnotWrite hmove _hsize htypingEq hsource store finalStore
          finalValue hvalidRuntime hvalidStoreTyping hwellFormed hwitness
          hmulti
        cases htypingEq
        exact relaxed_preservation_move_case_of_exactTransport
          (typing := typing) hsource hvalidRuntime hvalidStoreTyping
          hwellFormed hwitness hLv hnotWrite hmove
          (hooks.move hwitness hwellFormed hLv hnotWrite hmove) hmulti
      case mutBorrowCase =>
        intro _env _typing _lifetime _valueLifetime _lv _ty hLv hmutable
          hnotWrite _hsize htypingEq _hsource store finalStore finalValue
          hvalidRuntime _hvalidStoreTyping hwellFormed hwitness hmulti
        cases htypingEq
        exact ⟨hwellFormed,
          pathSensitive_mutBorrow_case (typing := typing) hwitness
            hvalidRuntime hLv hmutable hnotWrite hmulti⟩
      case immBorrowCase =>
        intro _env _typing _lifetime _valueLifetime _lv _ty hLv hnotRead
          _hsize htypingEq _hsource store finalStore finalValue hvalidRuntime
          _hvalidStoreTyping hwellFormed hwitness hmulti
        cases htypingEq
        exact ⟨hwellFormed,
          pathSensitive_immBorrow_case (typing := typing) hwitness
            hvalidRuntime hLv hnotRead hmulti⟩
      case boxCase =>
        intro _env₁ _env₂ _typing _lifetime _term _ty hterm ih hsize
          htypingEq hsource store finalStore finalValue hvalidRuntime
          hvalidStoreTyping hwellFormed hwitness hmulti
        cases htypingEq
        exact relaxed_preservation_box_case hsource hvalidRuntime
          hvalidStoreTyping hwellFormed hwitness hterm
          (by
            intro storeT finalStoreT finalValueT hvalidTerm hvalidStoreTerm
              hwellTerm hwitnessTerm hmultiTerm
            exact ih (by simp [Term.size] at hsize ⊢; omega)
              rfl (SourceTerm.box_inner hsource) storeT finalStoreT
              finalValueT hvalidTerm hvalidStoreTerm hwellTerm hwitnessTerm
              hmultiTerm)
          hmulti
      case blockCase =>
        intro _env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms
          _ty hchild hterms hwellTy hdrop ih hsize htypingEq hsource store
          finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
          hwitness hmulti
        cases htypingEq
        subst hdrop
        exact ih hsize rfl hsource _lifetime store finalStore finalValue
          hchild hvalidRuntime hvalidStoreTyping
          (WellFormedEnv.weaken hwellFormed
            (LifetimeChild.outlives hchild))
          (RuntimeExactEnvWitness.weaken hwitness
            (LifetimeChild.outlives hchild))
          hwellTy hmulti
      case declareCase =>
        intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty hfresh
          hterm hfreshOut hcoh henv₃ ih hsize htypingEq hsource store
          finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
          hwitness hmulti
        cases htypingEq
        exact relaxed_preservation_declare_case_of_exactTransport hsource
          hvalidRuntime hvalidStoreTyping hwellFormed hwitness hfresh hterm
          hfreshOut hcoh henv₃
          (by
            intro storeT finalStoreT finalValueT hvalidTerm hvalidStoreTerm
              hwellTerm hwitnessTerm hmultiTerm
            exact ih (by simp [Term.size] at hsize ⊢; omega)
              rfl (SourceTerm.declare_inner hsource) storeT finalStoreT
              finalValueT hvalidTerm hvalidStoreTerm hwellTerm hwitnessTerm
              hmultiTerm)
          (by
            intro storeV storeAfter value finalValueV hsafeValue
              hvalidDeclare hstep
            exact hooks.declare hsafeValue hvalidDeclare hstep)
          hmulti
      case assignCase =>
        intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs
          _oldTy _rhs _rhsTy hRhs hLhsPost hshape hwellTy hwrite hranked
          hcoh hcontained hnotWrite ih hsize htypingEq hsource store
          finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
          hwitness hmulti
        cases htypingEq
        exact relaxed_preservation_assign_case_of_exactTransport hsource
          hvalidRuntime hvalidStoreTyping hwellFormed hwitness hRhs hLhsPost
          hshape hwellTy hwrite hranked hcoh hcontained hnotWrite
          (by
            intro storeR finalStoreR finalValueR hvalidRhs hvalidStoreRhs
              hwellRhs hwitnessRhs hmultiRhs
            exact ih (by simp [Term.size] at hsize ⊢; omega)
              rfl (SourceTerm.assign_inner hsource) storeR finalStoreR
              finalValueR hvalidRhs hvalidStoreRhs hwellRhs hwitnessRhs
              hmultiRhs)
          (by
            intro storeV storeAfter value finalValueV hsafeValue hvalidAssign
              hstep
            exact hooks.assign hsafeValue hvalidAssign hstep)
          hmulti
      case eqCase =>
        intro _env₁ _env₂ _env₃ _envGhost _ghost _typing _lifetime _lhs
          _rhs _lhsTy _rhsTy hLhs hfresh htypeFresh htyFresh hstoreFresh
          hghostRhs hnotMention henvEq hcopyL hcopyR hshape ihL ihGhost
          hsize htypingEq hsource store finalStore finalValue hvalidRuntime
          hvalidStoreTyping hwellFormed hwitness hmulti
        cases htypingEq
        exact relaxed_preservation_eq_case hsource hvalidRuntime
          hvalidStoreTyping hwellFormed hwitness hLhs hfresh htypeFresh
          htyFresh hstoreFresh hghostRhs hnotMention henvEq hcopyL hcopyR
          hshape
          (by
            intro storeL finalStoreL finalValueL hvalidL hvalidStoreL hwellL
              hwitnessL hmultiL
            exact ihL (by simp [Term.size] at hsize ⊢; omega)
              rfl (SourceTerm.eq_lhs hsource) storeL finalStoreL finalValueL
              hvalidL hvalidStoreL hwellL hwitnessL hmultiL)
          (by
            intro storeR finalStoreR finalValueR hRhsErased hvalidR
              hvalidStoreR hwellR hwitnessR hmultiR
            have hsourceRight : SourceTerm _rhs :=
              SourceTerm.eq_rhs hsource
            exact ihFuel
              (by simp [Term.size] at hsize ⊢; omega)
              hsourceRight hvalidR hvalidStoreR hwellR hwitnessR
              hRhsErased hmultiR)
          hmulti
      case iteCase =>
        intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
          _trueBranch _falseBranch _trueTy _falseTy _joinTy hcondition
          htrue hfalse hjoin henvJoin hsameLeft hsameRight hwellJoin
          hcoherent hlinear ihCondition ihTrue ihFalse hsize htypingEq
          hsource store finalStore finalValue hvalidRuntime hvalidStoreTyping
          hwellFormed hwitness hmulti
        cases htypingEq
        exact relaxed_preservation_ite_case hsource hvalidRuntime
          hvalidStoreTyping hwellFormed hwitness hcondition htrue hfalse
          hjoin henvJoin hsameLeft hsameRight hwellJoin hcoherent hlinear
          (by
            intro storeC finalStoreC finalValueC hvalidC hvalidStoreC hwellC
              hwitnessC hmultiC
            exact ihCondition
              (by simp [Term.size] at hsize ⊢; omega)
              rfl (SourceTerm.ite_condition hsource) storeC finalStoreC
              finalValueC hvalidC hvalidStoreC hwellC hwitnessC hmultiC)
          (by
            intro storeT finalStoreT finalValueT hvalidT hvalidStoreT hwellT
              hwitnessT hmultiT
            exact ihTrue
              (by simp [Term.size] at hsize ⊢; omega)
              rfl (SourceTerm.ite_trueBranch hsource) storeT finalStoreT
              finalValueT hvalidT hvalidStoreT hwellT hwitnessT hmultiT)
          (by
            intro storeF finalStoreF finalValueF hvalidF hvalidStoreF hwellF
              hwitnessF hmultiF
            exact ihFalse
              (by simp [Term.size] at hsize ⊢; omega)
              rfl (SourceTerm.ite_falseBranch hsource) storeF finalStoreF
              finalValueF hvalidF hvalidStoreF hwellF hwitnessF hmultiF)
          hmulti
      case iteDivergingCase =>
        intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition
          _trueBranch _falseBranch _trueTy _falseTy hcondition htrue hfalse
          hdiverges ihCondition ihTrue _ihFalse hsize htypingEq hsource store
          finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
          hwitness hmulti
        cases htypingEq
        exact relaxed_preservation_iteDiverging_case hsource hvalidRuntime
          hvalidStoreTyping hwellFormed hwitness hcondition htrue hfalse
          hdiverges
          (by
            intro storeC finalStoreC finalValueC hvalidC hvalidStoreC hwellC
              hwitnessC hmultiC
            exact ihCondition
              (by simp [Term.size] at hsize ⊢; omega)
              rfl (SourceTerm.ite_condition hsource) storeC finalStoreC
              finalValueC hvalidC hvalidStoreC hwellC hwitnessC hmultiC)
          (by
            intro storeT finalStoreT finalValueT hvalidT hvalidStoreT hwellT
              hwitnessT hmultiT
            exact ihTrue
              (by simp [Term.size] at hsize ⊢; omega)
              rfl (SourceTerm.ite_trueBranch hsource) storeT finalStoreT
              finalValueT hvalidT hvalidStoreT hwellT hwitnessT hmultiT)
          hmulti
      case singletonCase =>
        intro _env₁ _env₂ _typing _lifetime _term _ty hterm ih hsize
          htypingEq hsource outerLifetime store finalStore finalValue hchild
          hvalidRuntime hvalidStoreTyping hwellFormed hwitness hwellTy hmulti
        cases htypingEq
        exact relaxed_preservation_block_singleton_case hsource hvalidRuntime
          hvalidStoreTyping hchild hwellFormed hwitness hterm hwellTy rfl
          (by
            intro storeT finalStoreT finalValueT hvalidTerm hvalidStoreTerm
              hwellTerm hwitnessTerm hmultiTerm
            exact ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
              rfl (SourceTerm.block_head hsource) storeT finalStoreT
              finalValueT hvalidTerm hvalidStoreTerm hwellTerm hwitnessTerm
              hmultiTerm)
          (by
            intro storeV valueV exactEnv hsafeValue hwellExact hborrowExact
              hsafeExact hmapExactApprox
            exact hooks.blockResult hsafeValue hwellExact hborrowExact
              hsafeExact hmapExactApprox)
          hmulti
      case consCase =>
        intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy
          _finalTy hterm hrest ihHead ihRest hsize htypingEq hsource
          outerLifetime store finalStore finalValue hchild hvalidRuntime
          hvalidStoreTyping hwellFormed hwitness hwellTy hmulti
        cases htypingEq
        cases _rest with
        | nil =>
            cases hrest
        | cons next restTail =>
            exact relaxed_preservation_block_cons_case hsource hvalidRuntime
              hvalidStoreTyping hchild hwellFormed hwitness hterm hrest
              hwellTy
              (by
                intro storeH finalStoreH finalValueH hvalidHead
                  hvalidStoreHead hwellHead hwitnessHead hmultiHead
                exact ihHead
                  (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
                  rfl (SourceTerm.block_head hsource) storeH finalStoreH
                  finalValueH hvalidHead hvalidStoreHead hwellHead
                  hwitnessHead hmultiHead)
              (by
                intro storeTail finalStoreTail finalValueTail hchildTail
                  hvalidTail hvalidStoreTail hwellTail hwitnessTail hwellTyTail
                  hmultiTail
                exact ihRest
                  (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
                  rfl (SourceTerm.block_tail hsource) outerLifetime storeTail
                  finalStoreTail finalValueTail hchildTail hvalidTail
                  hvalidStoreTail hwellTail hwitnessTail hwellTyTail
                  hmultiTail)
              hmulti

theorem relaxed_preservation_with_hooks
    (hooks : RelaxedPreservationHooks)
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    RuntimeExactEnvWitness store lifetime env₁ →
    RelaxedTermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    WellFormedEnv env₂ lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue env₂ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hwitness htyping
    hmulti
  exact relaxed_preservation_bounded_with_hooks hooks term.size (Nat.le_refl _)
    hsource hvalidRuntime hvalidStoreTyping hwellFormed hwitness htyping hmulti

/--
Ordinary typing can use the relaxed preservation skeleton after erasing the
strict `T-If` borrow-safety payload.

The remaining assumptions are exactly the non-control-flow exact-transport
hooks; there is still no `ite` hook.
-/
theorem relaxed_preservation_with_hooks_of_termTyping
    (hooks : RelaxedPreservationHooks)
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    RuntimeExactEnvWitness store lifetime env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    WellFormedEnv env₂ lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue env₂ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hwitness htyping
    hmulti
  exact relaxed_preservation_with_hooks hooks hsource hvalidRuntime
    hvalidStoreTyping hwellFormed hwitness (TermTyping.toRelaxed htyping)
    hmulti

/--
Direct preservation wrapper for a conditional whose condition and branches are
ordinarily typed, but whose join is only typed by relaxed `T-If`.

The statement deliberately has no `BorrowSafeEnv env₅` or
`TyBorrowSafeAgainstEnv env₅ joinTy` premise.  Any remaining assumptions are the
same non-control-flow exact-transport hooks used by the relaxed preservation
skeleton.
-/
theorem relaxed_preservation_ite_of_termTyping_without_join_borrow_safety
    (hooks : RelaxedPreservationHooks)
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
    MultiStep store lifetime (.ite condition trueBranch falseBranch)
      finalStore (.val finalValue) →
    WellFormedEnv env₅ lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue env₅
        joinTy := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hwitness
    hcondition htrue hfalse hjoin henvJoin hsameLeft hsameRight hwellJoin
    hcoherent hlinear hmulti
  exact relaxed_preservation_with_hooks hooks hsource hvalidRuntime
    hvalidStoreTyping hwellFormed hwitness
    (RelaxedTermTyping.ite_of_termTyping_without_join_borrow_safety
      hcondition htrue hfalse hjoin henvJoin hsameLeft hsameRight hwellJoin
      hcoherent hlinear)
    hmulti

end Paper
end LwRust
