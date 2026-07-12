import FWRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety

/-!
# Reachable-state safety for native while loops
-/

namespace FWRust
namespace Paper

open Core

private theorem terminalPreservationWhenInitialized
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnvWhenInitialized env₁ lifetime →
    SafeAbstraction store env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource hvalid hstoreTyping hwell hsafe htyping hmulti
  exact preservation_bounded term.size (Nat.le_refl _) hsource hvalid
    hstoreTyping hwell hsafe htyping hmulti

/-- Every finite prefix of a source-typed execution remains able to progress.

The invariant is deliberately the initialized/stale-aware one.  In
particular, this theorem has no `BorrowSafeEnv`, same-shape, coherence, or
linearizability assumption. -/
theorem reachableProgressWhenInitialized_bounded (fuel : Nat)
    {store store' : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term term' : Term}
    {ty : Ty} :
    term.size ≤ fuel →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnvWhenInitialized env₁ lifetime →
    store ∼ₛ env₁ →
    store.FiniteSupport →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term store' term' →
    ProgressResult store' lifetime term' := by
  induction fuel generalizing store store' env₁ env₂ typing lifetime term term' ty with
  | zero =>
      intro hsize _hsource _hvalidRuntime _hvalidStoreTyping _hwellFormed
        _hsafe _hfinite _htyping _hmulti
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
  intro hsize hsource hvalidRuntime hvalidStoreTyping hwellFormed hsafe
    hfinite htyping hmulti
  refine TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      term.size ≤ fuel.succ →
      currentTyping = typing →
      SourceTerm term →
      ∀ (store store' : ProgramStore) (term' : Term),
        ValidRuntimeState store term →
        ValidStoreTyping store term currentTyping →
        WellFormedEnvWhenInitialized env lifetime →
        store ∼ₛ env →
        store.FiniteSupport →
        MultiStep store lifetime term store' term' →
        ProgressResult store' lifetime term')
    (motive_2 := fun env currentTyping blockLifetime terms ty env₂ _ =>
      Term.size (.block blockLifetime terms) ≤ fuel.succ →
      currentTyping = typing →
      SourceTerm (.block blockLifetime terms) →
      ∀ (outerLifetime : Lifetime) (store store' : ProgramStore)
        (term' : Term),
        LifetimeChild outerLifetime blockLifetime →
        ValidRuntimeState store (.block blockLifetime terms) →
        ValidStoreTyping store (.block blockLifetime terms) currentTyping →
        WellFormedEnvWhenInitialized env blockLifetime →
        store ∼ₛ env →
        store.FiniteSupport →
        MultiStep store outerLifetime (.block blockLifetime terms)
          store' term' →
        ProgressResult store' outerLifetime term')
    ?const ?missing ?copy ?move ?mutBorrow ?immBorrow ?box ?block
    ?declare ?assign ?eq ?ite ?iteDiverging ?iteTrueDiverging
    ?whileLoopDiverging ?whileLoop ?singleton ?cons
    htyping hsize rfl hsource store store' term' hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hfinite hmulti
  -- T-Const: values are terminal; runs from them are empty.
  case const =>
    intro _env _typing _lifetime _value _ty _hvalueTyping _hsize _htypingEq
      _hsource store store' term' _hvalid _hvst _hwf _hsafe _hfs hmulti
    rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
    subst hstore
    subst hterm
    exact Or.inl (value_terminal _)
  case missing =>
    intro _env₁ _env₂ _typing _lifetime _ty _hloanFree _hfinite
      _hwellBridge _hsize _htypingEq
      _hsource store store' term' _hvalid _hvst _hwf _hsafe _hfs hmulti
    rcases multistep_missing_inv hmulti with ⟨hstore, hterm⟩
    subst hstore
    subst hterm
    exact Or.inr ⟨_, .missing, Step.missing⟩
  -- T-Copy: a single redex; afterwards the term is a value.
  case copy =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hcopy hnotRead
      _hsize htypingEq _hsource store store' term' _hvalid _hvst hwf
      hsafe _hfs hmulti
    cases htypingEq
    cases hmulti with
    | refl =>
        exact progress_copy_typing (typing := typing) hsafe
          (TermTyping.copy hLv hcopy hnotRead)
    | trans hstep hrest =>
        cases hstep with
        | copy _hread =>
            rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
            subst hstore
            subst hterm
            exact Or.inl (value_terminal _)
  -- T-Move.
  case move =>
    intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty hLv hnotWrite
      hmove _hsize htypingEq _hsource store store' term' _hvalid _hvst hwf
      hsafe _hfs hmulti
    cases htypingEq
    cases hmulti with
    | refl =>
        exact progress_move_typing (typing := typing) hsafe
          (TermTyping.move hLv hnotWrite hmove)
    | trans hstep hrest =>
        cases hstep with
        | move _hread _hwrite =>
            rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
            subst hstore
            subst hterm
            exact Or.inl (value_terminal _)
  -- T-MutBorrow.
  case mutBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hmutable hnotWrite
      _hsize htypingEq _hsource store store' term' _hvalid _hvst hwf
      hsafe _hfs hmulti
    cases htypingEq
    cases hmulti with
    | refl =>
        exact progress_borrow_typing (typing := typing) hsafe
          (TermTyping.mutBorrow hLv hmutable hnotWrite)
    | trans hstep hrest =>
        cases hstep with
        | borrow _hloc =>
            rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
            subst hstore
            subst hterm
            exact Or.inl (value_terminal _)
  -- T-ImmBorrow.
  case immBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hnotRead _hsize
      htypingEq _hsource store store' term' _hvalid _hvst hwf hsafe _hfs
      hmulti
    cases htypingEq
    cases hmulti with
    | refl =>
        exact progress_borrow_typing (typing := typing) hsafe
          (TermTyping.immBorrow hLv hnotRead)
    | trans hstep hrest =>
        cases hstep with
        | borrow _hloc =>
            rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
            subst hstore
            subst hterm
            exact Or.inl (value_terminal _)
  -- T-Box: either still inside the operand, or the box redex ended the run.
  case box =>
    intro _env₁ _env₂ _typing _lifetime _term _ty hterm ih hsize htypingEq
      hsource store store' term' hvalid hvst hwf hsafe hfs hmulti
    cases htypingEq
    rcases multistep_box_prefix_inv hmulti with
      ⟨inner', hfinal, hms⟩ | ⟨midStore, value, _hms, hredex⟩
    · subst hfinal
      have hprogress :=
        ih (by simp [Term.size] at hsize ⊢; omega)
          rfl (SourceTerm.box_inner hsource) store store' inner'
          (validRuntimeState_box_inner hvalid)
          (validStoreTyping_box_inner hvst) hwf hsafe hfs hms
      rcases hprogress with hterminal | ⟨storeNext, termNext, hstep⟩
      · rcases (terminal_iff_value inner').mp hterminal with ⟨value, hvalue⟩
        subst hvalue
        exact progress_box_value
          (OperationalStoreProgress.of_finiteSupport (hfs.multiStep hms))
      · exact Or.inr ⟨storeNext, .box termNext, Step.subBox hstep⟩
    · cases hredex with
      | box _hfresh _hbox => exact Or.inl (value_terminal _)
      | subBox hinner => exact False.elim (value_no_step hinner)
  -- T-Block: delegate to the body induction at the block lifetime.
  case block =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty
      hblockChild _hterms _hwellTy _hdrop ih hsize htypingEq hsource store
      store' term' hvalid hvst hwf hsafe hfs hmulti
    cases htypingEq
    exact ih hsize rfl hsource _lifetime store store' term' hblockChild hvalid
      hvst (WellFormedEnvWhenInitialized.weaken hwf
        (LifetimeChild.outlives hblockChild))
      hsafe hfs hmulti
  -- T-Declare: either still inside the initialiser, or the declare redex
  -- ended the run.
  case declare =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty _hfresh _hterm
      _hfreshOut _hcoh _henv ih hsize htypingEq hsource store store' term'
      hvalid hvst hwf hsafe hfs hmulti
    cases htypingEq
    rcases multistep_declare_prefix_inv hmulti with
      ⟨inner', hfinal, hms⟩ | ⟨midStore, value, _hms, hredex⟩
    · subst hfinal
      have hprogress :=
        ih (by simp [Term.size] at hsize ⊢; omega)
          rfl (SourceTerm.declare_inner hsource) store store' inner'
          (validRuntimeState_declare_inner hvalid)
          (validStoreTyping_declare_inner hvst) hwf hsafe hfs hms
      rcases hprogress with hterminal | ⟨storeNext, termNext, hstep⟩
      · rcases (terminal_iff_value inner').mp hterminal with ⟨value, hvalue⟩
        subst hvalue
        exact Or.inr ⟨store'.declare _x _lifetime value, .val .unit,
          Step.declare rfl⟩
      · exact Or.inr ⟨storeNext, .letMut _x termNext, Step.subDeclare hstep⟩
    · cases hredex with
      | declare _hstore => exact Or.inl (value_terminal _)
      | subDeclare hinner => exact False.elim (value_no_step hinner)
  -- T-Assign: either still inside the rhs (with the redex available once it
  -- is a value), or the assignment redex ended the run.
  case assign =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs
      _rhsTy hRhs hLhsPost _hshape _hwellTy _hwrite _hnoStale _hranked _hcoh
      _hcontained _hnotWrite ih hsize htypingEq hsource store store' term'
      hvalid hvst hwf hsafe hfs hmulti
    cases htypingEq
    have hsourceRhs : SourceTerm _rhs := SourceTerm.assign_inner hsource
    rcases multistep_assign_prefix_inv hmulti with
      ⟨rhs', hfinal, hms⟩ | ⟨midStore, value, _hms, hredex⟩
    · subst hfinal
      have hprogress :=
        ih (by simp [Term.size] at hsize ⊢; omega)
          rfl hsourceRhs store store' rhs'
          (validRuntimeState_assign_inner hvalid)
          (validStoreTyping_assign_inner hvst) hwf hsafe hfs hms
      rcases hprogress with hterminal | ⟨storeNext, termNext, hstep⟩
      · rcases (terminal_iff_value rhs').mp hterminal with ⟨value, hvalue⟩
        subst hvalue
        -- the rhs finished: re-establish the post-rhs invariants and fire
        -- the assignment redex
        have hterminalRhs :=
          terminalPreservationWhenInitialized hsourceRhs
            (validRuntimeState_assign_inner hvalid)
            (validStoreTyping_assign_inner hvst) hwf hsafe hRhs hms
        rcases read_defined_of_allocated
            (lvalTyping_allocated_location_of_safe_whenInitialized
              hterminalRhs.2.1 hLhsPost) with ⟨slot, hread⟩
        rcases (OperationalStoreProgress.of_finiteSupport
            (hfs.multiStep hms)).assignValue _lhs slot value hread with
          ⟨storeAfterWrite, storeAfterDrop, hwrite, hdrops⟩
        exact Or.inr ⟨storeAfterDrop, .val .unit,
          Step.assign hread hwrite hdrops⟩
      · exact Or.inr ⟨storeNext, .assign _lhs termNext,
          Step.subAssign hstep⟩
    · cases hredex with
      | assign _hread _hwrite _hdrops => exact Or.inl (value_terminal _)
      | subAssign hinner => exact False.elim (value_no_step hinner)
  -- T-Eq.
  case eq =>
    intro _env₁ _env₂ _env₃ _envGhost _ghost _typing _lifetime _lhs _rhs
      _lhsTy _rhsTy _hLhs hfresh htypeFresh htyFresh hstoreFresh hghostRhs
      hnotMention _henvEq _hcopyL _hcopyR _hshape ihL _ihGhost hsize
      htypingEq hsource store store' term' hvalid hvst hwf hsafe hfs
      hmulti
    cases htypingEq
    have _hRhsErased : TermTyping _env₂ typing _lifetime _rhs _rhsTy
        (_envGhost.erase _ghost) :=
      TermTyping.erase_ghost
        (env := _env₂)
        (ghostSlot := { ty := .ty _lhsTy, lifetime := _lifetime })
        hfresh htypeFresh (by
          intro hmem
          exact htyFresh (Ty.vars_subset_allVars (ty := _lhsTy) hmem))
        hstoreFresh hnotMention hghostRhs
    have hsourceLeft : SourceTerm _lhs := SourceTerm.eq_lhs hsource
    have hsourceRight : SourceTerm _rhs := SourceTerm.eq_rhs hsource
    have hvstLeft : ValidStoreTyping store _lhs typing :=
      hvst.eq_lhs
    have hvstRightSource : ValidStoreTyping store _rhs typing :=
      hvst.eq_rhs
    rcases multistep_eq_prefix_inv hmulti with
      ⟨lhs', hfinal, hmsLeft⟩ |
      ⟨midStore, leftValue, hmsLeft, hcase⟩
    · subst hfinal
      have hprogressLeft :=
        ihL (by simp [Term.size] at hsize ⊢; omega)
          rfl hsourceLeft store store' lhs'
          (validRuntimeState_of_sourceTerm hsourceLeft hvalid)
          hvstLeft hwf hsafe hfs hmsLeft
      rcases hprogressLeft with hterminalLeft | hstepLeft
      · rcases (terminal_iff_value lhs').mp hterminalLeft with
          ⟨leftValue, hleftValue⟩
        subst hleftValue
        have hterminalLeftState :=
          terminalPreservationWhenInitialized hsourceLeft
            (validRuntimeState_of_sourceTerm hsourceLeft hvalid)
            hvstLeft hwf hsafe _hLhs hmsLeft
        have hwellLeft : WellFormedEnvWhenInitialized _env₂ _lifetime :=
          (typingPreservesWellFormedWhenInitialized_of_sourceTerm
            hsourceLeft hwf _hLhs).1
        have hvalidRight : ValidRuntimeState store' _rhs :=
          validRuntimeState_of_sourceTerm hsourceRight hterminalLeftState.1
        have hvstRight : ValidStoreTyping store' _rhs typing :=
          validStoreTyping_sourceTerm_of_validStoreTyping hsourceRight
            hvstRightSource
        have hprogressRight : ProgressResult store' _lifetime _rhs := by
          exact typeAndBorrowProgress hvalidRight hvstRight hwellLeft.2
            hterminalLeftState.2.1
            (OperationalStoreProgress.of_finiteSupport
              (ProgramStore.FiniteSupport.multiStep hmsLeft hfs))
            _hRhsErased
        rcases hprogressRight with hterminalRight | hstepRight
        · rcases (terminal_iff_value _rhs).mp hterminalRight with
            ⟨rightValue, hrightValue⟩
          subst hrightValue
          exact progress_eq_values
        · exact progress_subEqRight hstepRight
      · exact progress_subEqLeft hstepLeft
    · have hterminalLeftState :=
        terminalPreservationWhenInitialized hsourceLeft
          (validRuntimeState_of_sourceTerm hsourceLeft hvalid)
          hvstLeft hwf hsafe _hLhs hmsLeft
      have hvalidRight : ValidRuntimeState midStore _rhs :=
        validRuntimeState_of_sourceTerm hsourceRight hterminalLeftState.1
      have hvstRight : ValidStoreTyping midStore _rhs typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceRight
          hvstRightSource
      have hwellLeft : WellFormedEnvWhenInitialized _env₂ _lifetime :=
        (typingPreservesWellFormedWhenInitialized_of_sourceTerm
          hsourceLeft hwf _hLhs).1
      rcases hcase with ⟨rhs', hfinal, hmsRight⟩ |
        ⟨rightStore, rightValue, hmsRight, hredex⟩
      · subst hfinal
        have hprogressRight : ProgressResult store' _lifetime rhs' := by
          exact ihFuel
            (env₁ := _env₂)
            (env₂ := _envGhost.erase _ghost)
            (typing := typing)
            (lifetime := _lifetime)
            (term := _rhs)
            (term' := rhs')
            (ty := _rhsTy)
            (by simp [Term.size] at hsize ⊢; omega)
            hsourceRight hvalidRight hvstRight hwellLeft
            hterminalLeftState.2.1
            (ProgramStore.FiniteSupport.multiStep hmsLeft hfs)
            _hRhsErased hmsRight
        rcases hprogressRight with hterminalRight | hstepRight
        · rcases (terminal_iff_value rhs').mp hterminalRight with
            ⟨rightValue, hrightValue⟩
          subst hrightValue
          exact progress_eq_values
        · exact progress_subEqRight hstepRight
      · cases hredex with
        | eqTrue => exact Or.inl (value_terminal _)
        | eqFalse _hne => exact Or.inl (value_terminal _)
        | subEqLeft hinner => exact False.elim (value_no_step hinner)
        | subEqRight hinner => exact False.elim (value_no_step hinner)
  -- T-If.
  case ite =>
    intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
      _trueBranch _falseBranch _trueTy _falseTy _joinTy _hcondition _htrue
      _hfalse _hjoin _henvJoin ihCondition ihTrue
      ihFalse hsize htypingEq hsource store store' term' hvalid hvst hwf
      hsafe hfs hmulti
    cases htypingEq
    have hsourceCondition : SourceTerm _condition :=
      SourceTerm.ite_condition hsource
    have hsourceTrue : SourceTerm _trueBranch :=
      SourceTerm.ite_trueBranch hsource
    have hsourceFalse : SourceTerm _falseBranch :=
      SourceTerm.ite_falseBranch hsource
    have hvstCondition : ValidStoreTyping store _condition typing :=
      hvst.ite_condition
    have hvstTrueSource : ValidStoreTyping store _trueBranch typing :=
      hvst.ite_trueBranch
    have hvstFalseSource : ValidStoreTyping store _falseBranch typing :=
      hvst.ite_falseBranch
    rcases multistep_ite_prefix_inv hmulti with
      ⟨condition', hfinal, hmsCondition⟩ |
      ⟨midStore, hmsCondition, hmsTrue⟩ |
      ⟨midStore, hmsCondition, hmsFalse⟩
    · subst hfinal
      have hprogressCondition :=
        ihCondition (by simp [Term.size] at hsize ⊢; omega)
          rfl hsourceCondition store store' condition'
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe hfs hmsCondition
      rcases hprogressCondition with hterminalCondition | hstepCondition
      · rcases (terminal_iff_value condition').mp hterminalCondition with
          ⟨conditionValue, hconditionValue⟩
        subst hconditionValue
        have hterminalConditionState :=
          terminalPreservationWhenInitialized hsourceCondition
            (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
            hvstCondition hwf hsafe _hcondition hmsCondition
        cases hterminalConditionState.2.2 with
        | bool =>
            rename_i b
            cases b
            · exact Or.inr ⟨store', _falseBranch, Step.iteFalse⟩
            · exact Or.inr ⟨store', _trueBranch, Step.iteTrue⟩
      · exact progress_subIte hstepCondition
    · have hterminalConditionState :=
        terminalPreservationWhenInitialized hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hvalidTrue : ValidRuntimeState midStore _trueBranch :=
        validRuntimeState_of_sourceTerm hsourceTrue hterminalConditionState.1
      have hvstTrue : ValidStoreTyping midStore _trueBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
          hvstTrueSource
      exact ihTrue (by simp [Term.size] at hsize ⊢; omega)
        rfl hsourceTrue midStore store' term' hvalidTrue hvstTrue
        (typingPreservesWellFormedWhenInitialized_of_sourceTerm
          hsourceCondition hwf _hcondition).1
        hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsTrue
    · have hterminalConditionState :=
        terminalPreservationWhenInitialized hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hvalidFalse : ValidRuntimeState midStore _falseBranch :=
        validRuntimeState_of_sourceTerm hsourceFalse hterminalConditionState.1
      have hvstFalse : ValidStoreTyping midStore _falseBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceFalse
          hvstFalseSource
      exact ihFalse (by simp [Term.size] at hsize ⊢; omega)
        rfl hsourceFalse midStore store' term' hvalidFalse hvstFalse
        (typingPreservesWellFormedWhenInitialized_of_sourceTerm
          hsourceCondition hwf _hcondition).1
        hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsFalse
  -- T-IfDiv: every path recurses into a premise IH; the dead branch is
  -- typed, so execution inside it keeps progressing.
  case iteDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition _trueBranch
      _falseBranch _trueTy _falseTy _hcondition _htrue _hfalse _hdiverges
      ihCondition ihTrue ihFalse hsize htypingEq hsource store store' term'
      hvalid hvst hwf hsafe hfs hmulti
    cases htypingEq
    have hsourceCondition : SourceTerm _condition :=
      SourceTerm.ite_condition hsource
    have hsourceTrue : SourceTerm _trueBranch :=
      SourceTerm.ite_trueBranch hsource
    have hsourceFalse : SourceTerm _falseBranch :=
      SourceTerm.ite_falseBranch hsource
    have hvstCondition : ValidStoreTyping store _condition typing :=
      hvst.ite_condition
    have hvstTrueSource : ValidStoreTyping store _trueBranch typing :=
      hvst.ite_trueBranch
    have hvstFalseSource : ValidStoreTyping store _falseBranch typing :=
      hvst.ite_falseBranch
    rcases multistep_ite_prefix_inv hmulti with
      ⟨condition', hfinal, hmsCondition⟩ |
      ⟨midStore, hmsCondition, hmsTrue⟩ |
      ⟨midStore, hmsCondition, hmsFalse⟩
    · subst hfinal
      have hprogressCondition :=
        ihCondition (by simp [Term.size] at hsize ⊢; omega)
          rfl hsourceCondition store store' condition'
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe hfs hmsCondition
      rcases hprogressCondition with hterminalCondition | hstepCondition
      · rcases (terminal_iff_value condition').mp hterminalCondition with
          ⟨conditionValue, hconditionValue⟩
        subst hconditionValue
        have hterminalConditionState :=
          terminalPreservationWhenInitialized hsourceCondition
            (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
            hvstCondition hwf hsafe _hcondition hmsCondition
        cases hterminalConditionState.2.2 with
        | bool =>
            rename_i b
            cases b
            · exact Or.inr ⟨store', _falseBranch, Step.iteFalse⟩
            · exact Or.inr ⟨store', _trueBranch, Step.iteTrue⟩
      · exact progress_subIte hstepCondition
    · have hterminalConditionState :=
        terminalPreservationWhenInitialized hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hvalidTrue : ValidRuntimeState midStore _trueBranch :=
        validRuntimeState_of_sourceTerm hsourceTrue hterminalConditionState.1
      have hvstTrue : ValidStoreTyping midStore _trueBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
          hvstTrueSource
      exact ihTrue (by simp [Term.size] at hsize ⊢; omega)
        rfl hsourceTrue midStore store' term' hvalidTrue hvstTrue
        (typingPreservesWellFormedWhenInitialized_of_sourceTerm
          hsourceCondition hwf _hcondition).1
        hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsTrue
    · have hterminalConditionState :=
        terminalPreservationWhenInitialized hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hvalidFalse : ValidRuntimeState midStore _falseBranch :=
        validRuntimeState_of_sourceTerm hsourceFalse hterminalConditionState.1
      have hvstFalse : ValidStoreTyping midStore _falseBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceFalse
          hvstFalseSource
      exact ihFalse (by simp [Term.size] at hsize ⊢; omega)
        rfl hsourceFalse midStore store' term' hvalidFalse hvstFalse
        (typingPreservesWellFormedWhenInitialized_of_sourceTerm
          hsourceCondition hwf _hcondition).1
        hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsFalse
  case iteTrueDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition _trueBranch
      _falseBranch _trueTy _falseTy _hcondition _htrue _hfalse _hdiverges
      ihCondition ihTrue ihFalse hsize htypingEq hsource store store' term'
      hvalid hvst hwf hsafe hfs hmulti
    cases htypingEq
    have hsourceCondition : SourceTerm _condition :=
      SourceTerm.ite_condition hsource
    have hsourceTrue : SourceTerm _trueBranch :=
      SourceTerm.ite_trueBranch hsource
    have hsourceFalse : SourceTerm _falseBranch :=
      SourceTerm.ite_falseBranch hsource
    have hvstCondition : ValidStoreTyping store _condition typing :=
      hvst.ite_condition
    have hvstTrueSource : ValidStoreTyping store _trueBranch typing :=
      hvst.ite_trueBranch
    have hvstFalseSource : ValidStoreTyping store _falseBranch typing :=
      hvst.ite_falseBranch
    rcases multistep_ite_prefix_inv hmulti with
      ⟨condition', hfinal, hmsCondition⟩ |
      ⟨midStore, hmsCondition, hmsTrue⟩ |
      ⟨midStore, hmsCondition, hmsFalse⟩
    · subst hfinal
      have hprogressCondition :=
        ihCondition (by simp [Term.size] at hsize ⊢; omega)
          rfl hsourceCondition store store' condition'
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe hfs hmsCondition
      rcases hprogressCondition with hterminalCondition | hstepCondition
      · rcases (terminal_iff_value condition').mp hterminalCondition with
          ⟨conditionValue, hconditionValue⟩
        subst hconditionValue
        have hterminalConditionState :=
          terminalPreservationWhenInitialized hsourceCondition
            (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
            hvstCondition hwf hsafe _hcondition hmsCondition
        cases hterminalConditionState.2.2 with
        | bool =>
            rename_i b
            cases b
            · exact Or.inr ⟨store', _falseBranch, Step.iteFalse⟩
            · exact Or.inr ⟨store', _trueBranch, Step.iteTrue⟩
      · exact progress_subIte hstepCondition
    · have hterminalConditionState :=
        terminalPreservationWhenInitialized hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hvalidTrue : ValidRuntimeState midStore _trueBranch :=
        validRuntimeState_of_sourceTerm hsourceTrue hterminalConditionState.1
      have hvstTrue : ValidStoreTyping midStore _trueBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
          hvstTrueSource
      exact ihTrue (by simp [Term.size] at hsize ⊢; omega)
        rfl hsourceTrue midStore store' term' hvalidTrue hvstTrue
        (typingPreservesWellFormedWhenInitialized_of_sourceTerm
          hsourceCondition hwf _hcondition).1
        hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsTrue
    · have hterminalConditionState :=
        terminalPreservationWhenInitialized hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hvalidFalse : ValidRuntimeState midStore _falseBranch :=
        validRuntimeState_of_sourceTerm hsourceFalse hterminalConditionState.1
      have hvstFalse : ValidStoreTyping midStore _falseBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceFalse
          hvstFalseSource
      exact ihFalse (by simp [Term.size] at hsize ⊢; omega)
        rfl hsourceFalse midStore store' term' hvalidFalse hvstFalse
        (typingPreservesWellFormedWhenInitialized_of_sourceTerm
          hsourceCondition hwf _hcondition).1
        hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsFalse
  -- T-WhileDiv: the diverging body never completes an iteration; mid-body
  -- states still progress because the body is fully typed.
  case whileLoopDiverging =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition _body
      _bodyTy hchild _hcondition _hbody hdiverges ihCondition ihBody hsize
      htypingEq hsource store store' term' hvalid hvst hwf hsafe hfs
      hmulti
    cases htypingEq
    have hsourceCondition : SourceTerm _condition :=
      SourceTerm.while_condition hsource
    have hsourceBody : SourceTerm _body := SourceTerm.while_body hsource
    have hvstCondition : ValidStoreTyping store _condition typing :=
      hvst.while_condition
    have hvstBody : ValidStoreTyping store _body typing :=
      hvst.while_body
    have hblockDiverges :
        Term.Diverges (.block _bodyLifetime [_body, .val .unit]) :=
      .block (by simp) hdiverges
    cases hmulti with
    | refl => exact Or.inr ⟨store, _, Step.whileStart⟩
    | trans hstep hrest =>
        cases hstep
        have hreaches :=
          multistep_while_form_prefix_inv hrest (WhileForm.cond _)
        have hmain :
            ∀ form startStore current currentStore,
              WhileRunReaches _lifetime _bodyLifetime _condition _body form
                startStore current currentStore →
              form = .whileCond _bodyLifetime _condition _condition _body →
              startStore ∼ₛ _env₁ →
              ValidRuntimeState startStore _condition →
              startStore.FiniteSupport →
              ProgressResult currentStore _lifetime current := by
          intro form startStore current currentStore hreach
          induction hreach with
          | condPhase =>
              rename_i conditionInFlight conditionInFlight' s₀ s₁ hms
              intro heq hsafe' hvalid' hfs'
              cases heq
              have hvst' : ValidStoreTyping s₀ _condition typing :=
                validStoreTyping_sourceTerm_of_validStoreTyping
                  hsourceCondition hvstCondition
              rcases ihCondition
                  (by simp [Term.size] at hsize ⊢; omega)
                  rfl hsourceCondition s₀ s₁ _ hvalid' hvst' hwf hsafe'
                  hfs' hms with hterminal | hstepCond
              · rcases (terminal_iff_value _).mp hterminal with ⟨v, hv⟩
                subst hv
                have hterminalState :=
                  terminalPreservationWhenInitialized hsourceCondition
                    hvalid' hvst' hwf hsafe'
                    _hcondition hms
                cases hterminalState.2.2 with
                | bool =>
                    rename_i b
                    cases b
                    · exact Or.inr ⟨_, _, Step.whileCondFalse⟩
                    · exact Or.inr ⟨_, _, Step.whileCondTrue⟩
              · rcases hstepCond with ⟨s₂, c', hstepInner⟩
                exact Or.inr ⟨s₂, _, Step.subWhileCond hstepInner⟩
          | exited =>
              intro _heq _hsafe' _hvalid' _hfs'
              exact Or.inl (value_terminal _)
          | enterBody =>
              rename_i conditionInFlight bodyInFlight' s₀ s₁ s₂ hcond
                hblockRun
              intro heq hsafe' hvalid' hfs'
              cases heq
              have hvst' : ValidStoreTyping s₀ _condition typing :=
                validStoreTyping_sourceTerm_of_validStoreTyping
                  hsourceCondition hvstCondition
              have hterminalCondState :=
                terminalPreservationWhenInitialized hsourceCondition
                  hvalid' hvst' hwf hsafe'
                  _hcondition hcond
              have hfs₁ := hfs'.multiStep hcond
              have hwfCondOut :
                  WellFormedEnvWhenInitialized _env₂ _lifetime :=
                (typingPreservesWellFormedWhenInitialized_of_sourceTerm
                  hsourceCondition hwf _hcondition).1
              have hwfBody :
                  WellFormedEnvWhenInitialized _env₂ _bodyLifetime :=
                WellFormedEnvWhenInitialized.weaken hwfCondOut
                  (LifetimeChild.outlives hchild)
              have hvalidBody :=
                validRuntimeState_of_sourceTerm hsourceBody
                  hterminalCondState.1
              have hvstBody' : ValidStoreTyping s₁ _body typing :=
                validStoreTyping_sourceTerm_of_validStoreTyping hsourceBody
                  hvstBody
              have hstoreOps :=
                OperationalStoreProgress.of_finiteSupport
                  (hfs₁.multiStep hblockRun)
              rcases multistep_block_prefix_inv hblockRun with
                ⟨head', hcurrent, hheadRun⟩ |
                ⟨midStore, value, hheadRun, hcont⟩
              · subst hcurrent
                have hheadProgress :=
                  ihBody
                    (by simp [Term.size] at hsize ⊢; omega)
                    rfl hsourceBody s₁ s₂ head' hvalidBody hvstBody'
                    hwfBody hterminalCondState.2.1
                    hfs₁ hheadRun
                rcases progress_block_of_head_progress
                    (lifetime := _lifetime) hstoreOps hheadProgress with
                  hterminal | ⟨s₃, t₃, hstepBlock⟩
                · exact absurd hterminal (by simp [Terminal])
                · exact Or.inr ⟨s₃, _, Step.subWhileBody hstepBlock⟩
              · exact absurd hheadRun
                  (diverges_multistep_not_value hdiverges)
          | iterate =>
              rename_i conditionInFlight current' s₀ s₁ s₂ s₃ blockValue
                hcond hblockRun _hrest _ih
              intro heq _hsafe' _hvalid' _hfs'
              cases heq
              exact absurd hblockRun
                (diverges_multistep_not_value hblockDiverges)
          | bodyPhase =>
              intro heq _hsafe' _hvalid' _hfs'
              cases heq
          | bodyDone =>
              intro heq _hsafe' _hvalid' _hfs'
              cases heq
        exact hmain _ _ _ _ hreaches rfl hsafe
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid) hfs
  -- T-While: entry and completed back edges transport into the weak may-invariant.
  case whileLoop =>
    intro _env₁ _envBack _envInv _env₂ _env₃ _typing _lifetime
      _bodyLifetime _condition _body _bodyTy hchild hjoin hcontained
      _hnameFresh _hcondInv _hbodyInv hdropEq ihCondInv ihBodyInv
      hsize htypingEq hsource store store' term' hvalid hvst hwf
      hsafe hfs hmulti
    cases htypingEq
    have hsourceCondition : SourceTerm _condition :=
      SourceTerm.while_condition hsource
    have hsourceBody : SourceTerm _body := SourceTerm.while_body hsource
    have hsourceIterBlock :
        SourceTerm (.block _bodyLifetime [_body, .val .unit]) := by
      intro v hmem
      simp [termValues] at hmem
      rcases hmem with hbody | hunit
      · exact hsourceBody v hbody
      · subst hunit; trivial
    have hvstCondition : ValidStoreTyping store _condition typing :=
      hvst.while_condition
    have hvstBody : ValidStoreTyping store _body typing :=
      hvst.while_body
    have hvstIterBlock :
        ValidStoreTyping store (.block _bodyLifetime [_body, .val .unit])
          typing := by
      intro value hmem
      simp [termValues] at hmem
      rcases hmem with hbody | hunit
      · exact hvst value (by simp [termValues]; exact Or.inr hbody)
      · subst hunit
        exact ⟨.unit, ValueTyping.unit, ValidPartialValue.unit⟩
    have hentryStrengthens : EnvStrengthens _env₁ _envInv :=
      EnvJoin.le_left hjoin
    have hbackStrengthens : EnvStrengthens _envBack _envInv :=
      EnvJoin.le_right hjoin
    have hentryInitBack :
        ∀ {targets : List LVal},
          BorrowTargetsInitialized _envInv targets →
            BorrowTargetsInitialized _env₁ targets := by
      intro targets hinitialized
      exact borrowTargetsInitialized_back_of_envStrengthens
        hentryStrengthens hinitialized
    have hbackInitBack :
        ∀ {targets : List LVal},
          BorrowTargetsInitialized _envInv targets →
            BorrowTargetsInitialized _envBack targets := by
      intro targets hinitialized
      exact borrowTargetsInitialized_back_of_envStrengthens
        hbackStrengthens hinitialized
    have hwfInv : WellFormedEnvWhenInitialized _envInv _lifetime :=
      ⟨hcontained,
        EnvSlotsOutlive.of_lifetimesPreserved hwf.2
          (EnvStrengthens.lifetimesPreserved hentryStrengthens)⟩
    have hiterTyping :
        TermTyping _env₂ typing _lifetime
          (.block _bodyLifetime [_body, .val .unit]) .unit
          (_env₃.dropLifetime _bodyLifetime) :=
      TermTyping.block hchild
        (TermListTyping.cons _hbodyInv
          (TermListTyping.singleton (TermTyping.const ValueTyping.unit)))
        WellFormedTy.unit rfl
    cases hmulti with
    | refl => exact Or.inr ⟨store, _, Step.whileStart⟩
    | trans hstep hrest =>
        cases hstep
        have hreaches :=
          multistep_while_form_prefix_inv hrest (WhileForm.cond _)
        have hmain :
            ∀ form startStore current currentStore,
              WhileRunReaches _lifetime _bodyLifetime _condition _body form
                startStore current currentStore →
              form = .whileCond _bodyLifetime _condition _condition _body →
              SafeAbstraction startStore _envInv →
              ValidRuntimeState startStore _condition →
              startStore.FiniteSupport →
              ProgressResult currentStore _lifetime current := by
          intro form startStore current currentStore hreach
          induction hreach with
          | condPhase =>
              rename_i conditionInFlight conditionInFlight' s₀ s₁ hms
              intro heq hsafe' hvalid' hfs'
              cases heq
              have hvst' : ValidStoreTyping s₀ _condition typing :=
                validStoreTyping_sourceTerm_of_validStoreTyping
                  hsourceCondition hvstCondition
              rcases ihCondInv
                  (by simp [Term.size] at hsize ⊢; omega)
                  rfl hsourceCondition s₀ s₁ _ hvalid' hvst' hwfInv hsafe'
                  hfs' hms with hterminal | hstepCond
              · rcases (terminal_iff_value _).mp hterminal with ⟨v, hv⟩
                subst hv
                have hterminalState :=
                  terminalPreservationWhenInitialized hsourceCondition
                    hvalid' hvst' hwfInv hsafe' _hcondInv hms
                cases hterminalState.2.2 with
                | bool =>
                    rename_i b
                    cases b
                    · exact Or.inr ⟨_, _, Step.whileCondFalse⟩
                    · exact Or.inr ⟨_, _, Step.whileCondTrue⟩
              · rcases hstepCond with ⟨s₂, c', hstepInner⟩
                exact Or.inr ⟨s₂, _, Step.subWhileCond hstepInner⟩
          | exited =>
              intro _heq _hsafe' _hvalid' _hfs'
              exact Or.inl (value_terminal _)
          | enterBody =>
              rename_i conditionInFlight bodyInFlight' s₀ s₁ s₂ hcond
                hblockRun
              intro heq hsafe' hvalid' hfs'
              cases heq
              have hvst' : ValidStoreTyping s₀ _condition typing :=
                validStoreTyping_sourceTerm_of_validStoreTyping
                  hsourceCondition hvstCondition
              have hterminalCondState :=
                terminalPreservationWhenInitialized hsourceCondition hvalid'
                  hvst' hwfInv hsafe' _hcondInv hcond
              have hfs₁ := hfs'.multiStep hcond
              have hwfCondOut :
                  WellFormedEnvWhenInitialized _env₂ _lifetime :=
                (typingPreservesWellFormedWhenInitialized_of_sourceTerm
                  hsourceCondition hwfInv _hcondInv).1
              have hwfBody :
                  WellFormedEnvWhenInitialized _env₂ _bodyLifetime :=
                WellFormedEnvWhenInitialized.weaken hwfCondOut
                  (LifetimeChild.outlives hchild)
              have hvalidBody :=
                validRuntimeState_of_sourceTerm hsourceBody
                  hterminalCondState.1
              have hvstBody' : ValidStoreTyping s₁ _body typing :=
                validStoreTyping_sourceTerm_of_validStoreTyping hsourceBody
                  hvstBody
              have hstoreOps :=
                OperationalStoreProgress.of_finiteSupport
                  (hfs₁.multiStep hblockRun)
              rcases multistep_block_prefix_inv hblockRun with
                ⟨head', hcurrent, hheadRun⟩ |
                ⟨midStore, value, hheadRun, hcont⟩
              · subst hcurrent
                have hheadProgress :=
                  ihBodyInv
                    (by simp [Term.size] at hsize ⊢; omega)
                    rfl hsourceBody s₁ s₂ head' hvalidBody hvstBody'
                    hwfBody hterminalCondState.2.1 hfs₁ hheadRun
                rcases progress_block_of_head_progress
                    (lifetime := _lifetime) hstoreOps hheadProgress with
                  hterminal | ⟨s₃, t₃, hstepBlock⟩
                · exact absurd hterminal (by simp [Terminal])
                · exact Or.inr ⟨s₃, _, Step.subWhileBody hstepBlock⟩
              · rcases hcont with
                  ⟨next, rest', dropStore, heqrest, _hdrops, hcontRun⟩ |
                  ⟨heqnil, _⟩
                · cases heqrest
                  rcases multistep_block_prefix_inv hcontRun with
                    ⟨head₂, hcurrent₂, hrun₂⟩ |
                    ⟨mid₂, v₂, hrun₂, hcont₂⟩
                  · subst hcurrent₂
                    obtain ⟨hmidEq, hheadEq⟩ := multistep_value_inv hrun₂
                    subst hmidEq
                    subst hheadEq
                    rcases progress_block_value
                        (lifetime := _lifetime)
                        (blockLifetime := _bodyLifetime)
                        (value := Value.unit) hstoreOps with
                      hterminal | ⟨s₃, t₃, hstepBlock⟩
                    · exact absurd hterminal (by simp [Terminal])
                    · exact Or.inr ⟨s₃, _, Step.subWhileBody hstepBlock⟩
                  · obtain ⟨hmidEq, hvalEq⟩ := multistep_value_inv hrun₂
                    subst hmidEq
                    rcases hcont₂ with
                      ⟨_, _, _, heq', _⟩ | ⟨_, _, _, _, hcurrentVal⟩
                    · cases heq'
                    · subst hcurrentVal
                      cases hvalEq
                      exact Or.inr ⟨_, _, Step.whileBodyDone⟩
                · cases heqnil
          | iterate =>
              rename_i conditionInFlight current' s₀ s₁ s₂ s₃ blockValue
                hcond hblockRun _hrest ih
              intro heq hsafe' hvalid' hfs'
              cases heq
              have hvst' : ValidStoreTyping s₀ _condition typing :=
                validStoreTyping_sourceTerm_of_validStoreTyping
                  hsourceCondition hvstCondition
              have hterminalCondState :=
                terminalPreservationWhenInitialized hsourceCondition hvalid'
                  hvst' hwfInv hsafe' _hcondInv hcond
              have hfs₁ := hfs'.multiStep hcond
              have hwfCondOut :
                  WellFormedEnvWhenInitialized _env₂ _lifetime :=
                (typingPreservesWellFormedWhenInitialized_of_sourceTerm
                  hsourceCondition hwfInv _hcondInv).1
              have hterminalBlock :=
                terminalPreservationWhenInitialized hsourceIterBlock
                  (validRuntimeState_of_sourceTerm hsourceIterBlock
                    hterminalCondState.1)
                  (validStoreTyping_sourceTerm_of_validStoreTyping
                    hsourceIterBlock hvstIterBlock)
                  hwfCondOut hterminalCondState.2.1 hiterTyping hblockRun
              have hsafeBack : SafeAbstraction s₂ _envBack := by
                rw [← hdropEq]
                exact hterminalBlock.2.1
              have hsafeInv : SafeAbstraction s₂ _envInv :=
                safeAbstractionWhenInitialized_transport_strengthening
                  hbackInitBack hsafeBack hbackStrengthens
              exact ih rfl hsafeInv
                (validRuntimeState_of_sourceTerm hsourceCondition
                  hterminalBlock.1)
                (hfs₁.multiStep hblockRun)
          | bodyPhase =>
              intro heq _hsafe' _hvalid' _hfs'
              cases heq
          | bodyDone =>
              intro heq _hsafe' _hvalid' _hfs'
              cases heq
        have hsafeInv : SafeAbstraction store _envInv :=
          safeAbstractionWhenInitialized_transport_strengthening
            hentryInitBack hsafe hentryStrengthens
        exact hmain _ _ _ _ hreaches rfl hsafeInv
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid) hfs
  -- T-Seq singleton: in-flight head, or the block-exit drop ended the run.
  case singleton =>
    intro _env₁ _env₂ _typing _blockLifetime _term _ty hterm ih hsize htypingEq
      hsource outerLifetime store store' term' _hchild hvalid hvst hwf hsafe
      hfs hmulti
    cases htypingEq
    rcases multistep_block_prefix_inv hmulti with
      ⟨head', hfinal, hms⟩ | ⟨midStore, value, _hms, hcont⟩
    · subst hfinal
      have hprogress :=
        ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl (SourceTerm.block_head hsource) store store' head'
          (validRuntimeState_block_singleton_inner hvalid)
          (validStoreTyping_block_singleton_inner hvst) hwf hsafe hfs
          hms
      exact progress_block_of_head_progress
        (OperationalStoreProgress.of_finiteSupport (hfs.multiStep hms))
        hprogress
    · rcases hcont with ⟨next, rest', _, heq, _, _⟩ | ⟨_, _, _, _, hterm'⟩
      · cases heq
      · subst hterm'
        exact Or.inl (value_terminal _)
  -- T-Seq cons: in-flight head, or the head finished, its value was
  -- dropped, and the block continued from the tail.
  case cons =>
    intro _env₁ _env₂ _env₃ _typing _blockLifetime _term _rest _termTy
      _finalTy hterm hrest ihHead ihRest hsize htypingEq hsource outerLifetime
      store store' term' hchild hvalid hvst hwf hsafe hfs hmulti
    cases htypingEq
    cases _rest with
    | nil => cases hrest
    | cons next restTail =>
    have hsourceHead : SourceTerm _term := SourceTerm.block_head hsource
    have hsourceTail : SourceTerm (.block _blockLifetime (next :: restTail)) :=
      SourceTerm.block_tail hsource
    rcases multistep_block_prefix_inv hmulti with
      ⟨head', hfinal, hms⟩ | ⟨midStore, value, hmsHead, hcont⟩
    · subst hfinal
      have hprogress :=
        ihHead (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceHead store store' head'
          (validRuntimeState_block_head hvalid)
          (validStoreTyping_block_head hvst) hwf hsafe hfs hms
      exact progress_block_of_head_progress
        (OperationalStoreProgress.of_finiteSupport (hfs.multiStep hms))
        hprogress
    · rcases hcont with
        ⟨next', rest'', dropStore, heq, hdrops, hmsTail⟩ | ⟨heq, _⟩
      · cases heq
        -- the head finished: re-establish the mid-state invariants and
        -- recurse into the tail
        have hterminalHeadRuntime :=
          terminalPreservationWhenInitialized hsourceHead
            (validRuntimeState_block_head hvalid)
            (validStoreTyping_block_head hvst) hwf hsafe hterm hmsHead
        have hwellInner :
            WellFormedEnvWhenInitialized _env₂ _blockLifetime :=
          (typingPreservesWellFormedWhenInitialized_of_sourceTerm
            hsourceHead hwf hterm).1
        have hvalueBlockValid :
            ValidRuntimeState midStore
              (.block _blockLifetime (.val value :: next :: restTail)) :=
          validRuntimeState_block_value_cons_of_value_source_tail
            hsourceTail hterminalHeadRuntime.1
        have hseqStep :
            Step midStore outerLifetime
              (.block _blockLifetime (.val value :: next :: restTail))
              dropStore (.block _blockLifetime (next :: restTail)) :=
          Step.seq hdrops
        have hvalidTailAfter :
            ValidRuntimeState dropStore
              (.block _blockLifetime (next :: restTail)) :=
          validRuntimeState_seq_step hvalueBlockValid hseqStep
        have hsafeTailAfter : dropStore ∼ₛ _env₂ :=
          safeAbstraction_seq_value_drop_whenInitialized
            hterminalHeadRuntime.2.1 hvalueBlockValid hwellInner hdrops
        have htailStoreTyping :
            ValidStoreTyping dropStore
              (.block _blockLifetime (next :: restTail)) typing :=
          validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
            (validStoreTyping_block_tail_of_cons hvst)
        exact ihRest
          (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceTail outerLifetime dropStore store' term'
          hchild hvalidTailAfter htailStoreTyping hwellInner
          hsafeTailAfter
          ((hfs.multiStep hmsHead).drops hdrops)
          hmsTail
      · cases heq

/-- Public all-prefix progress theorem with the structural fuel hidden. -/
theorem reachableProgressWhenInitialized
    {store store' : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term term' : Term}
    {ty : Ty} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnvWhenInitialized env₁ lifetime →
    SafeAbstraction store env₁ →
    store.FiniteSupport →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term store' term' →
    ProgressResult store' lifetime term' := by
  intro hsource hvalid hstoreTyping hwell hsafe hfinite htyping hmulti
  exact reachableProgressWhenInitialized_bounded term.size (Nat.le_refl _)
    hsource hvalid hstoreTyping hwell hsafe hfinite htyping hmulti

/-- Divergence-friendly reachable-state safety for the minimal normal
`T-While` rule.  The seven rule premises are exposed directly so the theorem
cannot hide any historical joined-environment assumptions. -/
theorem whileLoop_reachableProgress
    {store currentStore : ProgramStore}
    {env₁ envBack envInv env₂ env₃ : Env} {typing : StoreTyping}
    {lifetime bodyLifetime : Lifetime} {condition body current : Term}
    {bodyTy : Ty}
    (hchild : LifetimeChild lifetime bodyLifetime)
    (hjoin : EnvJoin env₁ envBack envInv)
    (hcontained : ContainedBorrowsWellFormedWhenInitialized envInv)
    (hnameFresh : LoopInvariantNameFresh env₁ envInv condition body)
    (hcondition : TermTyping envInv typing lifetime condition .bool env₂)
    (hbody : TermTyping env₂ typing bodyLifetime body bodyTy env₃)
    (hdrop : env₃.dropLifetime bodyLifetime = envBack)
    (hsource : SourceTerm (.whileLoop bodyLifetime condition body))
    (hvalid : ValidRuntimeState store
      (.whileLoop bodyLifetime condition body))
    (hstoreTyping : ValidStoreTyping store
      (.whileLoop bodyLifetime condition body) typing)
    (hwell : WellFormedEnvWhenInitialized env₁ lifetime)
    (hsafe : SafeAbstraction store env₁)
    (hfinite : store.FiniteSupport)
    (hreaches : MultiStep store lifetime
      (.whileLoop bodyLifetime condition body) currentStore current) :
    ProgressResult currentStore lifetime current := by
  exact reachableProgressWhenInitialized hsource hvalid hstoreTyping hwell
    hsafe hfinite
    (TermTyping.whileLoop hchild hjoin hcontained hnameFresh hcondition hbody
      hdrop)
    hreaches

/-- Reachable-state safety for `T-WhileDiv`.  A true iteration cannot finish,
but every finite prefix inside its fully checked body still progresses. -/
theorem whileLoopDiverging_reachableProgress
    {store currentStore : ProgramStore} {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
    {condition body current : Term} {bodyTy : Ty}
    (hchild : LifetimeChild lifetime bodyLifetime)
    (hcondition : TermTyping env₁ typing lifetime condition .bool env₂)
    (hbody : TermTyping env₂ typing bodyLifetime body bodyTy env₃)
    (hdiverges : Term.Diverges body)
    (hsource : SourceTerm (.whileLoop bodyLifetime condition body))
    (hvalid : ValidRuntimeState store
      (.whileLoop bodyLifetime condition body))
    (hstoreTyping : ValidStoreTyping store
      (.whileLoop bodyLifetime condition body) typing)
    (hwell : WellFormedEnvWhenInitialized env₁ lifetime)
    (hsafe : SafeAbstraction store env₁)
    (hfinite : store.FiniteSupport)
    (hreaches : MultiStep store lifetime
      (.whileLoop bodyLifetime condition body) currentStore current) :
    ProgressResult currentStore lifetime current := by
  exact reachableProgressWhenInitialized hsource hvalid hstoreTyping hwell
    hsafe hfinite
    (TermTyping.whileLoopDiverging hchild hcondition hbody hdiverges)
    hreaches



end Paper
end FWRust
