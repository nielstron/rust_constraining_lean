import LwRust.Extractor.RelaxedProgress
import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
# Well-formedness for relaxed control-flow joins

The ordinary well-formedness induction does not use the strict `T-If`
post-join borrow-safety premises.  This file mirrors the source-term
well-formedness result for `RelaxedTermTyping`.
-/

namespace LwRust
namespace Paper

open Core

theorem RelaxedTermTyping.retype_of_sourceTerm {env₁ env₂ : Env}
    {typing typing' : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    (∀ ghost, StoreTyping.TypeNameFresh typing' ghost) →
    SourceTerm term →
    RelaxedTermTyping env₁ typing lifetime term ty env₂ →
    RelaxedTermTyping env₁ typing' lifetime term ty env₂ := by
  intro hfreshTyping hsource htyping
  exact RelaxedTermTyping.rec
    (motive_1 := fun env _t l term ty env₂ _ =>
      SourceTerm term → RelaxedTermTyping env typing' l term ty env₂)
    (motive_2 := fun env _t blockLifetime terms ty env₂ _ =>
      SourceTerm (.block blockLifetime terms) →
        RelaxedTermListTyping env typing' blockLifetime terms ty env₂)
    (fun {_env _typing _lifetime value _ty} hvalueTyping hsource => by
      have hsourceValue : SourceValue value :=
        hsource value (by simp [termValues])
      cases hvalueTyping with
      | unit | int | bool => exact RelaxedTermTyping.const (by constructor)
      | ref _hlookup => exact absurd hsourceValue (by simp [SourceValue]))
    (fun hwellTy hloanFree _hsource =>
      RelaxedTermTyping.missing hwellTy hloanFree)
    (fun hLv hcopy hread _hsource =>
      RelaxedTermTyping.copy hLv hcopy hread)
    (fun hLv hwrite hmove _hsource =>
      RelaxedTermTyping.move hLv hwrite hmove)
    (fun hLv hmutable hwrite _hsource =>
      RelaxedTermTyping.mutBorrow hLv hmutable hwrite)
    (fun hLv hread _hsource =>
      RelaxedTermTyping.immBorrow hLv hread)
    (fun _hterm ih hsource =>
      RelaxedTermTyping.box (ih (SourceTerm.box_inner hsource)))
    (fun hchild _hterms hwellTy hdrop ih hsource =>
      RelaxedTermTyping.block hchild (ih hsource) hwellTy hdrop)
    (fun hfresh _hterm hfreshOut hcoh henv ih hsource =>
      RelaxedTermTyping.declare hfresh (ih (SourceTerm.declare_inner hsource))
        hfreshOut hcoh henv)
    (fun _hRhs hLhsPost hshape hwf hwrite hranked hcoh hcontained
        hnotWrite ih hsource =>
      RelaxedTermTyping.assign (ih (SourceTerm.assign_inner hsource)) hLhsPost
        hshape hwf hwrite hranked hcoh hcontained hnotWrite)
    (fun _hLhs hfresh htypeFresh htyFresh _hstoreFresh _hghostRhs hnotMention henvEq
        hcopyL hcopyR hshape ihL ihGhost hsource =>
      RelaxedTermTyping.eq (ihL (SourceTerm.eq_lhs hsource)) hfresh
        htypeFresh htyFresh (hfreshTyping _)
        (ihGhost (SourceTerm.eq_rhs hsource))
        hnotMention henvEq hcopyL hcopyR hshape)
    (fun _hcondition _htrue _hfalse hjoin henvJoin hsameLeft hsameRight
        hwellJoin hcoherent hlinear ihCondition ihTrue ihFalse hsource =>
      RelaxedTermTyping.ite (ihCondition (SourceTerm.ite_condition hsource))
        (ihTrue (SourceTerm.ite_trueBranch hsource))
        (ihFalse (SourceTerm.ite_falseBranch hsource))
        hjoin henvJoin hsameLeft hsameRight hwellJoin hcoherent hlinear)
    (fun _hcondition _htrue _hfalse hdiverges ihCondition ihTrue ihFalse
        hsource =>
      RelaxedTermTyping.iteDiverging
        (ihCondition (SourceTerm.ite_condition hsource))
        (ihTrue (SourceTerm.ite_trueBranch hsource))
        (ihFalse (SourceTerm.ite_falseBranch hsource))
        hdiverges)
    (fun _hterm ih hsource =>
      RelaxedTermListTyping.singleton (ih (SourceTerm.block_head hsource)))
    (fun _hterm _hrest ihHead ihRest hsource =>
      RelaxedTermListTyping.cons (ihHead (SourceTerm.block_head hsource))
        (ihRest (SourceTerm.block_tail hsource)))
    htyping hsource

theorem relaxed_typingPreservesWellFormed_of_ruleCarriedObligations_core_bounded
    (fuel : Nat) {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    term.size ≤ fuel →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    WellFormedEnv env₁ lifetime →
    RelaxedTermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  induction fuel generalizing env₁ env₂ typing lifetime term ty with
  | zero =>
      intro hsize _hrefs _hwellFormed _htyping
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
      intro hsize hrefs hwellFormed htyping
      refine RelaxedTermTyping.rec
        (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
          term.size ≤ fuel.succ →
          currentTyping = typing →
          WellFormedEnv env lifetime →
          WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
        (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
          Term.size (.block lifetime terms) ≤ fuel.succ →
          currentTyping = typing →
          WellFormedEnv env lifetime →
          WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
        (fun {_env _typing _lifetime _value _ty} hvalueTyping _hsize
            htypingEq hwellFormed =>
          by
            subst htypingEq
            exact ⟨hwellFormed,
              valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
        (fun {_env _typing _lifetime _ty} hwellTy _hloanFree _hsize
            _htypingEq hwellFormed =>
          ⟨hwellFormed, hwellTy⟩)
        (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
            _hsize _htypingEq hwellFormed =>
          ⟨hwellFormed, copyTy_result_wellFormed hwellFormed hLv hcopy⟩)
        (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
            hLv hnotWrite hmove _hsize _htypingEq hwellFormed =>
          move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
        (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable
            _hwrite _hsize _htypingEq hwellFormed =>
          ⟨hwellFormed,
            WellFormedTy.borrow
              (BorrowTargetsWellFormed.singleton hLv
                (LValTyping.lifetime_outlives_one hwellFormed hLv)
                (LValTyping.base_outlives_one hwellFormed hLv))⟩)
        (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
            _hsize _htypingEq hwellFormed =>
          ⟨hwellFormed,
            WellFormedTy.borrow
              (BorrowTargetsWellFormed.singleton hLv
                (LValTyping.lifetime_outlives_one hwellFormed hLv)
                (LValTyping.base_outlives_one hwellFormed hLv))⟩)
        (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih hsize
            htypingEq hwellFormed =>
          let result := ih
            (by simp [Term.size] at hsize ⊢; omega)
            htypingEq hwellFormed
          ⟨result.1, WellFormedTy.box result.2⟩)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
            hblockChild _hterms hwellTy hdrop ih hsize htypingEq hwellFormed =>
          let bodyResult :=
            ih hsize htypingEq
              (WellFormedEnv.weaken hwellFormed
                (LifetimeChild.outlives hblockChild))
          Env.dropLifetime_preserves_wellFormed_child
            hblockChild bodyResult.1 hwellTy hdrop)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
            _hfresh _hterm hfreshOut hcohObligations henv₃ ih hsize htypingEq
            hwellFormed =>
          by
            let result := ih
              (by simp [Term.size] at hsize ⊢; omega)
              htypingEq hwellFormed
            refine ⟨?_, WellFormedTy.unit⟩
            rw [henv₃]
            exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
              result.1 result.2 hfreshOut hcohObligations)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs
              _oldTy _rhs _rhsTy}
            hRhs _hLhsPost hshape hwellRhs hwrite hranked hwriteCoh hcontained
            hnotWrite ih hsize htypingEq hwellFormed =>
          by
            let result := ih
              (by simp [Term.size] at hsize ⊢; omega)
              htypingEq hwellFormed
            rcases hranked with
              ⟨φ, hlinBy, hbelow⟩
            have hlin3By :=
              EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
                hwrite hlinBy hbelow
            have hcoh3 := hwriteCoh
            have hcbwf3 := containedBorrowsWellFormed_assign result.1.1 hcoh3
              (Linearizable.of_linearizedBy hlin3By) hcontained hwrite hnotWrite
            exact ⟨⟨hcbwf3,
                EnvWrite.preserves_slotsOutlive result.1.2.1 hwrite,
                hcoh3,
                Linearizable.of_linearizedBy hlin3By⟩,
                WellFormedTy.unit⟩)
        (fun {_env₁ _env₂ _env₃ _envGhost _ghost _typing _lifetime _lhs _rhs
              _lhsTy _rhsTy}
            _hLhs hfresh htypeFresh htyFresh hstoreFresh hghostRhs hnotMention
            henvEq _hcopyL _hcopyR _hshape ihL _ihGhost hsize htypingEq
            hwellFormed =>
          by
            subst htypingEq
            let leftResult := ihL
              (by simp [Term.size] at hsize ⊢; omega)
              rfl hwellFormed
            have hRhsErased : RelaxedTermTyping _env₂ _typing _lifetime _rhs _rhsTy
                (_envGhost.erase _ghost) :=
              RelaxedTermTyping.erase_ghost
                (env := _env₂)
                (ghostSlot := { ty := .ty _lhsTy, lifetime := _lifetime })
                hfresh htypeFresh
                (by simpa [PartialTy.vars] using htyFresh)
                hstoreFresh hnotMention hghostRhs
            have rightResult :=
              ihFuel
                (env₁ := _env₂)
                (env₂ := _envGhost.erase _ghost)
                (typing := _typing)
                (lifetime := _lifetime)
                (term := _rhs)
                (ty := _rhsTy)
                (by simp [Term.size] at hsize ⊢; omega)
                hrefs leftResult.1 hRhsErased
            exact ⟨by simpa [henvEq] using rightResult.1, WellFormedTy.bool⟩)
        (fun {_env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
              _trueBranch _falseBranch _trueTy _falseTy _joinTy}
            _hcondition _htrue _hfalse _hjoin _henvJoin _hsameLeft _hsameRight
            hwellJoin hcoherent hlinear ihCondition ihTrue ihFalse hsize
            htypingEq hwellFormed =>
          let conditionResult := ihCondition
            (by simp [Term.size] at hsize ⊢; omega)
            htypingEq hwellFormed
          let trueResult := ihTrue
            (by simp [Term.size] at hsize ⊢; omega)
            htypingEq conditionResult.1
          let falseResult := ihFalse
            (by simp [Term.size] at hsize ⊢; omega)
            htypingEq conditionResult.1
          ⟨⟨containedBorrowsWellFormed_join _henvJoin _hsameLeft _hsameRight
              trueResult.1.1 falseResult.1.1 hcoherent hlinear, by
              exact EnvSlotsOutlive.of_lifetimesPreserved trueResult.1.2.1
                (EnvJoin.lifetimesPreserved_left _henvJoin),
            hcoherent, hlinear⟩, hwellJoin⟩)
        (fun {_env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition
              _trueBranch _falseBranch _trueTy _falseTy}
            _hcondition _htrue _hfalse _hdiverges ihCondition ihTrue _ihFalse
            hsize htypingEq hwellFormed =>
          let conditionResult := ihCondition
            (by simp [Term.size] at hsize ⊢; omega)
            htypingEq hwellFormed
          ihTrue
            (by simp [Term.size] at hsize ⊢; omega)
            htypingEq conditionResult.1)
        (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih hsize
            htypingEq hwellFormed =>
          ih
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq hwellFormed)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
            _hterm _hrest ihHead ihRest hsize htypingEq hwellFormed =>
          let headResult := ihHead
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq hwellFormed
          ihRest
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq headResult.1)
        htyping hsize rfl hwellFormed

theorem relaxed_typingPreservesWellFormed_of_ruleCarriedObligations
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    RelaxedTermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact relaxed_typingPreservesWellFormed_of_ruleCarriedObligations_core_bounded
    term.size (Nat.le_refl _) hrefs hwellFormed htyping

theorem relaxed_typingPreservesWellFormed_of_sourceTerm
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    SourceTerm term →
    ValidState store term →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    RelaxedTermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hsource hvalidState hwellFormed hsafe htyping
  exact relaxed_typingPreservesWellFormed_of_ruleCarriedObligations
    (fun env lifetime => storeTypingRefsWellFormed_empty env lifetime)
    hvalidState (sourceTerm_validStoreTyping_empty_any hsource) hwellFormed
    hsafe (RelaxedTermTyping.retype_of_sourceTerm
      (fun ghost => StoreTyping.empty_typeNameFresh ghost) hsource htyping)

end Paper
end LwRust
