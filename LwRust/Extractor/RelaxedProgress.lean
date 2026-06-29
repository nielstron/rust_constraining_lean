import LwRust.Extractor.RelaxedMergeCompleteness
import LwRust.Paper.Soundness.Lemma_4_10_Progress

/-!
# Progress for relaxed control-flow joins

`RelaxedTermTyping` is the experimental relation whose `T-If` rule omits the
post-join borrow-safety checks.  This file proves that those checks are not
needed for local progress: progress only inspects the current redex and the
input environment that safely abstracts the current store.
-/

namespace LwRust
namespace Paper

open Core

theorem RelaxedTermTyping.erase_ghost_pack {ghost : Name} {env : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty}
    {envOut : Env} :
    RelaxedTermTyping env typing lifetime term ty envOut →
    Env.TypeNameFresh (env.erase ghost) ghost →
    StoreTyping.TypeNameFresh typing ghost →
    ¬ Term.Mentions ghost term →
    RelaxedTermTyping (env.erase ghost) typing lifetime term ty
      (envOut.erase ghost) ∧
    Env.TypeNameFresh (envOut.erase ghost) ghost ∧
    ghost ∉ Ty.allVars ty := by
  intro htyping
  exact RelaxedTermTyping.rec
    (motive_1 := fun env typing lifetime term ty envOut _ =>
      Env.TypeNameFresh (env.erase ghost) ghost →
      StoreTyping.TypeNameFresh typing ghost →
      ¬ Term.Mentions ghost term →
      RelaxedTermTyping (env.erase ghost) typing lifetime term ty
        (envOut.erase ghost) ∧
      Env.TypeNameFresh (envOut.erase ghost) ghost ∧
      ghost ∉ Ty.allVars ty)
    (motive_2 := fun env typing lifetime terms ty envOut _ =>
      Env.TypeNameFresh (env.erase ghost) ghost →
      StoreTyping.TypeNameFresh typing ghost →
      ¬ TermList.Mentions ghost terms →
      RelaxedTermListTyping (env.erase ghost) typing lifetime terms ty
        (envOut.erase ghost) ∧
      Env.TypeNameFresh (envOut.erase ghost) ghost ∧
      ghost ∉ Ty.allVars ty)
    (by
      intro _env _typing _lifetime _value _ty hvalue hfresh hstore _hnot
      exact ⟨RelaxedTermTyping.const hvalue, hfresh,
        ValueTyping.typeNameFresh hvalue hstore⟩)
    (by
      intro _env _typing _lifetime _ty hwell hloan hfresh _hstore _hnot
      have htyFresh : ghost ∉ Ty.allVars _ty :=
        Ty.no_allVars_of_loanFree hloan ghost
      exact ⟨RelaxedTermTyping.missing
        (WellFormedTy.erase_ghost hwell hfresh htyFresh) hloan,
        hfresh, htyFresh⟩)
    (by
      intro _env _typing _lifetime _valueLifetime lv _ty hLv hcopy hnotRead
        hfresh _hstore hnot
      have hnotLv : ¬ LVal.Mentions ghost lv := by
        simpa [Term.Mentions] using hnot
      have hLvErased := LValTyping.erase_ghost.1 hLv hfresh hnotLv
      have htyFresh : ghost ∉ Ty.allVars _ty := by
        have := LValTyping.typeNameFresh.1 hLvErased hfresh
        simpa [PartialTy.allVars] using this
      exact ⟨RelaxedTermTyping.copy hLvErased hcopy (by
        intro hread
        exact hnotRead (ReadProhibited.erase_to_env hread)),
        hfresh, htyFresh⟩)
    (by
      intro _env₁ _env₂ _typing _lifetime _valueLifetime lv _ty hLv hnotWrite
        hmove hfresh _hstore hnot
      have hnotLv : ¬ LVal.Mentions ghost lv := by
        simpa [Term.Mentions] using hnot
      have hLvErased := LValTyping.erase_ghost.1 hLv hfresh hnotLv
      have htyFresh : ghost ∉ Ty.allVars _ty := by
        have := LValTyping.typeNameFresh.1 hLvErased hfresh
        simpa [PartialTy.allVars] using this
      have hmoveErased := EnvMove.erase_ghost hmove hnotLv
      exact ⟨RelaxedTermTyping.move hLvErased (by
        intro hwrite
        exact hnotWrite (WriteProhibited.erase_to_env hwrite))
        hmoveErased,
        EnvMove.typeNameFresh_erase hmove hfresh hnotLv,
        htyFresh⟩)
    (by
      intro _env _typing _lifetime _valueLifetime lv _ty hLv hmutable hnotWrite
        hfresh _hstore hnot
      have hnotLv : ¬ LVal.Mentions ghost lv := by
        simpa [Term.Mentions] using hnot
      have hLvErased := LValTyping.erase_ghost.1 hLv hfresh hnotLv
      have hresultFresh : ghost ∉ Ty.allVars (Ty.borrow Bool.true [lv]) := by
        intro hv
        simp [Ty.allVars] at hv
        exact hnotLv ((LVal.mentions_iff_base (ghost := ghost) lv).2 hv.symm)
      exact ⟨RelaxedTermTyping.mutBorrow hLvErased
        (Mutable.erase_ghost hmutable hfresh hnotLv)
        (by
          intro hwrite
          exact hnotWrite (WriteProhibited.erase_to_env hwrite)),
        hfresh, hresultFresh⟩)
    (by
      intro _env _typing _lifetime _valueLifetime lv _ty hLv hnotRead
        hfresh _hstore hnot
      have hnotLv : ¬ LVal.Mentions ghost lv := by
        simpa [Term.Mentions] using hnot
      have hLvErased := LValTyping.erase_ghost.1 hLv hfresh hnotLv
      have hresultFresh : ghost ∉ Ty.allVars (Ty.borrow Bool.false [lv]) := by
        intro hv
        simp [Ty.allVars] at hv
        exact hnotLv ((LVal.mentions_iff_base (ghost := ghost) lv).2 hv.symm)
      exact ⟨RelaxedTermTyping.immBorrow hLvErased
        (by
          intro hread
          exact hnotRead (ReadProhibited.erase_to_env hread)),
        hfresh, hresultFresh⟩)
    (by
      intro _env₁ _env₂ _typing _lifetime _innerTerm _innerTy _hInner ih
        hfresh hstore hnot
      have hnotInner : ¬ Term.Mentions ghost _innerTerm := by
        simpa [Term.Mentions] using hnot
      rcases ih hfresh hstore hnotInner with
        ⟨hInnerErased, hfreshOut, htyFresh⟩
      exact ⟨RelaxedTermTyping.box hInnerErased, hfreshOut,
        by simpa [Ty.allVars] using htyFresh⟩)
    (by
      intro _env₁ env₂ _env₃ _typing _lifetime blockLifetime terms _ty hchild
        _hterms hwell hdrop ih hfresh hstore hnot
      have hnotTerms : ¬ TermList.Mentions ghost terms := by
        simpa [Term.Mentions] using hnot
      rcases ih hfresh hstore hnotTerms with
        ⟨htermsErased, hfreshTerms, htyFresh⟩
      subst hdrop
      exact ⟨RelaxedTermTyping.block hchild htermsErased
        (WellFormedTy.erase_ghost hwell hfreshTerms htyFresh)
        (Env.dropLifetime_erase env₂ ghost blockLifetime),
        by
          simpa [Env.dropLifetime_erase env₂ ghost blockLifetime] using
            Env.typeNameFresh_dropLifetime hfreshTerms,
        htyFresh⟩)
    (by
      intro _env₁ env₂ _env₃ _typing lifetime x init _ty hfreshX _hinit
        hfreshOutX hoblig henv ih hfresh hstore hnot
      have hxGhost : x ≠ ghost := by
        intro hx
        exact hnot (by simp [Term.Mentions, hx])
      have hnotInit : ¬ Term.Mentions ghost init := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ih hfresh hstore hnotInit with
        ⟨hinitErased, hfreshInit, htyFresh⟩
      subst henv
      have heraseUpdate :=
        Env.erase_update_ne env₂ (x := ghost) (y := x)
          { ty := .ty _ty, lifetime := lifetime } hxGhost
      rw [heraseUpdate]
      exact ⟨RelaxedTermTyping.declare
        (Env.erase_fresh_of_ne hfreshX hxGhost)
        hinitErased
        (Env.erase_fresh_of_ne hfreshOutX hxGhost)
        (FreshUpdateCoherenceObligations.erase_ghost hoblig
          hfreshInit hxGhost htyFresh)
        rfl,
        Env.typeNameFresh_update hfreshInit
          (by simpa [PartialTy.allVars] using htyFresh),
        by simp [Ty.allVars]⟩)
    (by
      intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime lhs oldTy rhs
        rhsTy _hRhs hLhs hshape hwell hwrite hranked hcoh hcontained
        hnotWrite ih hfresh hstore hnot
      have hnotRhs : ¬ Term.Mentions ghost rhs := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotLhs : ¬ LVal.Mentions ghost lhs := by
        intro hmention
        have hbase := (LVal.mentions_iff_base (ghost := ghost) lhs).1 hmention
        exact hnot (by simp [Term.Mentions, hbase])
      rcases ih hfresh hstore hnotRhs with
        ⟨hRhsErased, hfreshRhs, hrhsFresh⟩
      have hLhsErased := LValTyping.erase_ghost.1 hLhs hfreshRhs hnotLhs
      have holdFresh : ghost ∉ PartialTy.allVars oldTy :=
        LValTyping.typeNameFresh.1 hLhsErased hfreshRhs
      have hwriteErased :=
        EnvWrite.erase_ghost hwrite hfreshRhs hnotLhs hrhsFresh
      have hfreshWrite :=
        EnvWrite.typeNameFresh_erase hwrite hfreshRhs hnotLhs hrhsFresh
      rcases hranked with ⟨φ, hlinear, hrhsBelow⟩
      exact ⟨RelaxedTermTyping.assign hRhsErased hLhsErased
        (ShapeCompatible.erase_ghost hshape hfreshRhs holdFresh
          (by simpa [PartialTy.allVars] using hrhsFresh))
        (WellFormedTy.erase_ghost hwell hfreshRhs hrhsFresh)
        hwriteErased
        ⟨φ, LinearizedBy.erase_ghost hlinear,
          EnvWriteRhsBorrowTargetsBelow.erase_ghost hrhsBelow⟩
        (Coherent.erase_ghost hcoh hfreshWrite)
        (EnvWriteRhsTargetsWellFormed.erase_ghost hcontained hfreshWrite)
        (by
          intro hwriteProhibited
          exact hnotWrite (WriteProhibited.erase_to_env hwriteProhibited)),
        hfreshWrite,
        by simp [Ty.allVars]⟩)
    (by
      intro env₁ env₂ _env₃ envGhost localGhost _typing lifetime lhs rhs
        lhsTy rhsTy _hLhs hlocalFresh hlocalTypeFresh hlocalTyFresh
        hstoreLocal hRhsGhost hnotLocalRhs henvEq hcopyL hcopyR hshape
        ihL ihRhs hfresh hstore hnot
      have hnotLhs : ¬ Term.Mentions ghost lhs := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotRhs : ¬ Term.Mentions ghost rhs := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ihL hfresh hstore hnotLhs with
        ⟨hLhsErased, hfreshLhs, hlhsFresh⟩
      by_cases hsame : localGhost = ghost
      · subst localGhost
        have hRhsForEq :
            RelaxedTermTyping
              ((env₂.erase ghost).update ghost
                { ty := .ty lhsTy, lifetime := lifetime })
              _typing lifetime rhs rhsTy envGhost := by
          simpa [Env.erase_of_fresh hlocalFresh] using hRhsGhost
        have hinputFresh :
            Env.TypeNameFresh
              ((env₂.update ghost { ty := .ty lhsTy, lifetime := lifetime }).erase
                ghost)
              ghost := by
          simpa [Env.erase_update_same_of_fresh hlocalFresh] using
            hlocalTypeFresh
        rcases ihRhs hinputFresh hstoreLocal hnotLocalRhs with
          ⟨_hRhsErased, hfreshRhs, _hrhsFresh⟩
        subst henvEq
        have hEqTyping :
            RelaxedTermTyping (env₁.erase ghost) _typing lifetime (.eq lhs rhs) .bool
              (envGhost.erase ghost) :=
          RelaxedTermTyping.eq hLhsErased
            (Env.fresh_erase env₂ ghost)
            hfreshLhs hlocalTyFresh hstoreLocal hRhsForEq hnotLocalRhs rfl
            hcopyL hcopyR hshape
        exact ⟨by simpa using hEqTyping,
          by simpa using hfreshRhs,
          by simp [Ty.allVars]⟩
      · have hinputFresh :
            Env.TypeNameFresh
              ((env₂.update localGhost
                { ty := .ty lhsTy, lifetime := lifetime }).erase ghost)
              ghost := by
          rw [Env.erase_update_ne env₂ (x := ghost) (y := localGhost)
            { ty := .ty lhsTy, lifetime := lifetime } hsame]
          exact Env.typeNameFresh_update hfreshLhs
            (by simpa [PartialTy.allVars] using hlhsFresh)
        rcases ihRhs hinputFresh hstore hnotRhs with
          ⟨hRhsErasedRaw, hfreshRhsRaw, hrhsFresh⟩
        have hRhsErased :
            RelaxedTermTyping
              ((env₂.erase ghost).update localGhost
                { ty := .ty lhsTy, lifetime := lifetime })
              _typing lifetime rhs rhsTy (envGhost.erase ghost) := by
          simpa [Env.erase_update_ne env₂ (x := ghost) (y := localGhost)
            { ty := .ty lhsTy, lifetime := lifetime } hsame] using
            hRhsErasedRaw
        subst henvEq
        have hfreshShape :
            Env.TypeNameFresh ((envGhost.erase localGhost).erase ghost) ghost := by
          rw [Env.erase_comm envGhost localGhost ghost]
          exact Env.typeNameFresh_erase hfreshRhsRaw
        have hshapeErased :
            ShapeCompatible ((envGhost.erase localGhost).erase ghost)
              (.ty lhsTy) (.ty rhsTy) :=
          ShapeCompatible.erase_ghost hshape hfreshShape
            (by simpa [PartialTy.allVars] using hlhsFresh)
            (by simpa [PartialTy.allVars] using hrhsFresh)
        have hEqTyping :
            RelaxedTermTyping (env₁.erase ghost) _typing lifetime (.eq lhs rhs) .bool
              ((envGhost.erase ghost).erase localGhost) :=
          RelaxedTermTyping.eq hLhsErased
            (Env.erase_fresh_of_ne hlocalFresh hsame)
            (Env.typeNameFresh_erase hlocalTypeFresh)
            hlocalTyFresh hstoreLocal hRhsErased hnotLocalRhs rfl
            hcopyL hcopyR
            (by
              rw [← Env.erase_comm envGhost localGhost ghost]
              exact hshapeErased)
        exact ⟨by
            rw [Env.erase_comm envGhost localGhost ghost]
            exact hEqTyping,
          by
            rw [Env.erase_comm envGhost localGhost ghost]
            exact Env.typeNameFresh_erase hfreshRhsRaw,
          by simp [Ty.allVars]⟩)
    (by
      intro _env₁ _env₂ env₃ env₄ env₅ _typing _lifetime condition trueBranch
        falseBranch trueTy falseTy joinTy _hcondition _htrue _hfalse htyJoin
        henvJoin hsameLeft hsameRight hwellJoin hcoherent hlinear
        ihCondition ihTrue ihFalse hfresh hstore hnot
      have hnotCondition : ¬ Term.Mentions ghost condition := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotTrue : ¬ Term.Mentions ghost trueBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotFalse : ¬ Term.Mentions ghost falseBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ihCondition hfresh hstore hnotCondition with
        ⟨hconditionErased, hfreshCond, _hboolFresh⟩
      rcases ihTrue hfreshCond hstore hnotTrue with
        ⟨htrueErased, hfreshTrue, htrueTyFresh⟩
      rcases ihFalse hfreshCond hstore hnotFalse with
        ⟨hfalseErased, hfreshFalse, hfalseTyFresh⟩
      have hjoinTyFresh : ghost ∉ Ty.allVars joinTy := by
        have hpartial :=
          PartialTyJoin.allVars_fresh htyJoin
            (by simpa [PartialTy.allVars] using htrueTyFresh)
            (by simpa [PartialTy.allVars] using hfalseTyFresh)
        simpa [PartialTy.allVars] using hpartial
      have hfreshJoin : Env.TypeNameFresh (env₅.erase ghost) ghost :=
        EnvJoin.typeNameFresh_erase henvJoin hfreshTrue hfreshFalse
      exact ⟨RelaxedTermTyping.ite hconditionErased htrueErased hfalseErased
        htyJoin (EnvJoin.erase_ghost henvJoin)
        (EnvJoinSameShape.erase_ghost hsameLeft)
        (EnvJoinSameShape.erase_ghost hsameRight)
        (WellFormedTy.erase_ghost hwellJoin hfreshJoin hjoinTyFresh)
        (Coherent.erase_ghost hcoherent hfreshJoin)
        (Linearizable.erase_ghost hlinear),
        hfreshJoin, hjoinTyFresh⟩)
    (by
      intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime condition trueBranch
        falseBranch _trueTy _falseTy _hcondition _htrue _hfalse hdiverges
        ihCondition ihTrue ihFalse hfresh hstore hnot
      have hnotCondition : ¬ Term.Mentions ghost condition := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotTrue : ¬ Term.Mentions ghost trueBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotFalse : ¬ Term.Mentions ghost falseBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ihCondition hfresh hstore hnotCondition with
        ⟨hconditionErased, hfreshCond, _hboolFresh⟩
      rcases ihTrue hfreshCond hstore hnotTrue with
        ⟨htrueErased, hfreshTrue, htrueFresh⟩
      rcases ihFalse hfreshCond hstore hnotFalse with
        ⟨hfalseErased, _hfreshFalse, _hfalseFresh⟩
      exact ⟨RelaxedTermTyping.iteDiverging hconditionErased htrueErased
        hfalseErased hdiverges, hfreshTrue, htrueFresh⟩)
    (by
      intro _env₁ _env₂ _typing _lifetime singletonTerm _ty _hterm ih
        hfresh hstore hnot
      have hnotTerm : ¬ Term.Mentions ghost singletonTerm := by
        intro hmention
        exact hnot (by simp [TermList.Mentions, hmention])
      rcases ih hfresh hstore hnotTerm with
        ⟨htermErased, hfreshOut, htyFresh⟩
      exact ⟨RelaxedTermListTyping.singleton htermErased, hfreshOut, htyFresh⟩)
    (by
      intro _env₁ _env₂ _env₃ _typing _lifetime head rest _headTy _finalTy
        _hhead _hrest ihHead ihRest hfresh hstore hnot
      have hnotHead : ¬ Term.Mentions ghost head := by
        intro hmention
        exact hnot (by simp [TermList.Mentions, hmention])
      have hnotRest : ¬ TermList.Mentions ghost rest := by
        intro hmention
        exact hnot (by simp [TermList.Mentions, hmention])
      rcases ihHead hfresh hstore hnotHead with
        ⟨hheadErased, hfreshHead, _hheadFresh⟩
      rcases ihRest hfreshHead hstore hnotRest with
        ⟨hrestErased, hfreshRest, hfinalFresh⟩
      exact ⟨RelaxedTermListTyping.cons hheadErased hrestErased,
        hfreshRest, hfinalFresh⟩)
    htyping

theorem RelaxedTermTyping.erase_ghost {env envGhost : Env} {ghost : Name}
    {ghostSlot : EnvSlot} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    env.fresh ghost →
    Env.TypeNameFresh env ghost →
    ghost ∉ PartialTy.vars ghostSlot.ty →
    StoreTyping.TypeNameFresh typing ghost →
    ¬ Term.Mentions ghost term →
    RelaxedTermTyping (env.update ghost ghostSlot) typing lifetime term ty envGhost →
    RelaxedTermTyping env typing lifetime term ty (envGhost.erase ghost) := by
  intro hfresh htypeFresh _hslotFresh hstoreFresh hnot htyping
  have hinput :
      Env.TypeNameFresh ((env.update ghost ghostSlot).erase ghost) ghost := by
    simpa [Env.erase_update_same_of_fresh hfresh] using htypeFresh
  rcases RelaxedTermTyping.erase_ghost_pack htyping hinput hstoreFresh hnot with
    ⟨herased, _hfreshOut, _htyFresh⟩
  simpa [Env.erase_update_same_of_fresh hfresh] using herased

theorem relaxed_progress_typing_bounded {store : ProgramStore} (fuel : Nat)
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    term.size ≤ fuel →
    ValidStoreTyping store term typing →
    EnvSlotsOutlive env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    RelaxedTermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  induction fuel generalizing env₁ env₂ typing lifetime term ty with
  | zero =>
      intro hsize _hvalidStoreTyping _hslotsOutlive _hsafe _hstore _htyping
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
      intro hsize hvalidStoreTyping hslotsOutlive hsafe hstore htyping
      revert hsize hvalidStoreTyping hslotsOutlive hsafe hstore
      refine RelaxedTermTyping.rec
        (motive_1 := fun env typing lifetime term ty env₂ _ =>
          term.size ≤ fuel.succ →
          ValidStoreTyping store term typing →
          EnvSlotsOutlive env lifetime →
          store ∼ₛ env →
          OperationalStoreProgress store →
          ProgressResult store lifetime term)
        (motive_2 := fun env typing blockLifetime terms ty env₂ _ =>
          Term.size (.block blockLifetime terms) ≤ fuel.succ →
          ValidStoreTyping store (.block blockLifetime terms) typing →
          ∀ lifetime,
            EnvSlotsOutlive env blockLifetime →
            store ∼ₛ env →
            OperationalStoreProgress store →
            ProgressResult store lifetime (.block blockLifetime terms))
        ?caseConst ?caseMissing ?caseCopy ?caseMove ?caseMutBorrow
        ?caseImmBorrow ?caseBox ?caseBlock ?caseDeclare ?caseAssign ?caseEq
        ?caseIte ?caseIteDiverging ?caseSingleton ?caseCons htyping
      case caseConst =>
        intro _env _typing lifetime value _ty _hvalue _hsize _hvst _hwf
          _hsafe _hstore
        exact progress_value store lifetime value
      case caseMissing =>
        intro _env _typing _lifetime _ty _hwellTy _hloanFree _hsize _hvst
          _hwf _hsafe _hstore
        exact Or.inr ⟨store, .missing, Step.missing⟩
      case caseCopy =>
        intro _env _typing lifetime _valueLifetime _lv _ty hLv _hcopy
          _hreadProhibited _hsize _hvst _hwf hsafe _hstore
        rcases progress_copy_lval_of_safe hsafe hLv with ⟨value, hstep⟩
        exact Or.inr ⟨store, .val value, hstep⟩
      case caseMove =>
        intro _env₁ _env₂ _typing lifetime _valueLifetime _lv _ty hLv
          _hwriteProhibited _hmove _hsize _hvst _hwf hsafe _hstore
        rcases progress_move_lval_of_safe hsafe hLv with
          ⟨value, store', hstep⟩
        exact Or.inr ⟨store', .val value, hstep⟩
      case caseMutBorrow =>
        intro _env _typing lifetime _valueLifetime _lv _ty hLv _hmutable
          _hwriteProhibited _hsize _hvst _hwf hsafe _hstore
        rcases progress_borrow_lval_of_safe (mutable := Bool.true) hsafe hLv with
          ⟨location, hstep⟩
        exact Or.inr
          ⟨store, .val (.ref { location := location, owner := Bool.false }), hstep⟩
      case caseImmBorrow =>
        intro _env _typing lifetime _valueLifetime _lv _ty hLv _hreadProhibited
          _hsize _hvst _hwf hsafe _hstore
        rcases progress_borrow_lval_of_safe (mutable := Bool.false) hsafe hLv with
          ⟨location, hstep⟩
        exact Or.inr
          ⟨store, .val (.ref { location := location, owner := Bool.false }), hstep⟩
      case caseBox =>
        intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih hsize hvst
          hwf hsafe hstore
        exact (ih (by simp [Term.size] at hsize ⊢; omega)
          (validStoreTyping_box_inner hvst) hwf hsafe hstore).elim_value
          (fun value hterm => by
            subst hterm
            exact progress_box_value hstore)
          progress_subBox
      case caseBlock =>
        intro _env₁ _env₂ _env₃ _typing lifetime _blockLifetime _terms _ty
          hchild _hterms _hwellTy _hdrop ih hsize hvst houtlives hsafe hstore
        exact ih hsize hvst lifetime
          (EnvSlotsOutlive.weaken houtlives (LifetimeChild.outlives hchild))
          hsafe hstore
      case caseDeclare =>
        intro _env₁ _env₂ _env₃ _typing lifetime _x _term _ty _hfresh _hterm
          _hfreshOut _hcoh _henv ih hsize hvst hwf hsafe hstore
        exact (ih (by simp [Term.size] at hsize ⊢; omega)
          (validStoreTyping_declare_inner hvst) hwf hsafe hstore).elim_value
          (fun value hterm => by
            subst hterm
            exact Or.inr
              ⟨store.declare _x lifetime value, .val .unit, Step.declare rfl⟩)
          progress_subDeclare
      case caseAssign =>
        intro _env₁ _env₂ _env₃ _typing lifetime _targetLifetime _lhs _oldTy
          _rhs _rhsTy hRhs hLhsPost _hshape _hwfTy _hwrite _hranked _hcoh
          _hcontained _hnotWrite ih hsize hvst _hwf hsafe hstore
        exact (ih (by simp [Term.size] at hsize ⊢; omega)
          (validStoreTyping_assign_inner hvst) _hwf hsafe hstore).elim_value
          (fun value hrhs => by
            subst hrhs
            cases hRhs with
            | const _hvalue =>
                rcases read_defined_of_allocated
                    (lvalTyping_allocated_location_of_safe hsafe hLhsPost) with
                  ⟨oldSlot, hread⟩
                exact progress_assign_value hstore hread)
          progress_subAssign
      case caseEq =>
        intro _env₁ _env₂ _env₃ _envGhost _ghost _typing lifetime lhs rhs lhsTy
          _rhsTy hLhs hfresh htypeFresh htyFresh hstoreFresh hghostRhs
          hnotMention _henvEq _hcopyL _hcopyR _hshape ihL _ihGhost hsize hvst
          hwf hsafe hstore
        rcases ihL (by simp [Term.size] at hsize ⊢; omega) hvst.eq_lhs hwf hsafe
            hstore with
          hterminalL | hstepL
        · rcases (terminal_iff_value lhs).mp hterminalL with
            ⟨lhsValue, hlhs⟩
          subst hlhs
          cases hLhs with
          | const _hvalueL =>
              have hRhs :=
                RelaxedTermTyping.erase_ghost
                  (env := _env₁)
                  (ghostSlot := { ty := .ty lhsTy, lifetime := lifetime })
                  hfresh htypeFresh
                  (by simpa [PartialTy.vars] using htyFresh)
                  hstoreFresh hnotMention hghostRhs
              rcases ihFuel (by simp [Term.size] at hsize ⊢; omega)
                  hvst.eq_rhs hwf hsafe hstore hRhs with
                hterminalR | hstepR
              · rcases (terminal_iff_value rhs).mp hterminalR with
                  ⟨rhsValue, hrhs⟩
                subst hrhs
                exact progress_eq_values
              · exact progress_subEqRight hstepR
        · exact progress_subEqLeft hstepL
      case caseIte =>
        intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime condition
          _trueBranch _falseBranch _trueTy _falseTy _joinTy hcondition _htrue
          _hfalse _hjoin _henvJoin _hsameLeft _hsameRight _hwellJoin
          _hcoherent _hlinear ihCondition _ihTrue _ihFalse hsize hvst hwf hsafe
          hstore
        rcases ihCondition (by simp [Term.size] at hsize ⊢; omega)
            hvst.ite_condition hwf hsafe hstore with
          hterminalCondition | hstepCondition
        · rcases (terminal_iff_value condition).mp hterminalCondition with
            ⟨conditionValue, hconditionValue⟩
          subst hconditionValue
          cases hcondition with
          | const hvalueTyping =>
              exact progress_ite_value hvalueTyping hvst.ite_condition
        · exact progress_subIte hstepCondition
      case caseIteDiverging =>
        intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime condition _trueBranch
          _falseBranch _trueTy _falseTy hcondition _htrue _hfalse _hdiverges
          ihCondition _ihTrue _ihFalse hsize hvst hwf hsafe hstore
        rcases ihCondition (by simp [Term.size] at hsize ⊢; omega)
            hvst.ite_condition hwf hsafe hstore with
          hterminalCondition | hstepCondition
        · rcases (terminal_iff_value condition).mp hterminalCondition with
            ⟨conditionValue, hconditionValue⟩
          subst hconditionValue
          cases hcondition with
          | const hvalueTyping =>
              exact progress_ite_value hvalueTyping hvst.ite_condition
        · exact progress_subIte hstepCondition
      case caseSingleton =>
        intro _env₁ _env₂ _typing _blockLifetime _term _ty _hterm ih hsize
          hvst outerLifetime hwf hsafe hstore
        exact progress_block_of_head_progress hstore
          (ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            (validStoreTyping_block_singleton_inner hvst) hwf hsafe hstore)
      case caseCons =>
        intro _env₁ _env₂ _env₃ _typing _blockLifetime _term _rest _termTy
          _finalTy _hterm _hrest ihHead _ihRest hsize hvst outerLifetime hwf
          hsafe hstore
        exact progress_block_of_head_progress hstore
          (ihHead (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            (validStoreTyping_block_head hvst) hwf hsafe hstore)

theorem relaxed_progress_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidStoreTyping store term typing →
    EnvSlotsOutlive env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    RelaxedTermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hvalidStoreTyping hslotsOutlive hsafe hstore htyping
  exact relaxed_progress_typing_bounded term.size (Nat.le_refl _)
    hvalidStoreTyping hslotsOutlive hsafe hstore htyping

/--
Ordinary typing can use the relaxed progress proof after erasing the strict
`T-If` borrow-safety payload.
-/
theorem relaxed_progress_typing_of_termTyping {store : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    ValidStoreTyping store term typing →
    EnvSlotsOutlive env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hvalidStoreTyping hslotsOutlive hsafe hstore htyping
  exact relaxed_progress_typing hvalidStoreTyping hslotsOutlive hsafe hstore
    (TermTyping.toRelaxed htyping)

/--
Direct progress wrapper for a conditional whose subterms are ordinarily typed,
but whose join is only typed by relaxed `T-If`.

The statement deliberately has no `BorrowSafeEnv env₅` or
`TyBorrowSafeAgainstEnv env₅ joinTy` premise: progress only needs the current
store abstraction for the input environment and the ordinary static join shape.
-/
theorem relaxed_progress_ite_of_termTyping_without_join_borrow_safety
    {store : ProgramStore} {env₁ env₂ env₃ env₄ env₅ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term}
    {trueTy falseTy joinTy : Ty} :
    ValidStoreTyping store (.ite condition trueBranch falseBranch) typing →
    EnvSlotsOutlive env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
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
    ProgressResult store lifetime (.ite condition trueBranch falseBranch) := by
  intro hvalidStoreTyping hslotsOutlive hsafe hstore hcondition htrue hfalse
    hjoin henvJoin hsameLeft hsameRight hwellJoin hcoherent hlinear
  exact relaxed_progress_typing hvalidStoreTyping hslotsOutlive hsafe hstore
    (RelaxedTermTyping.ite_of_termTyping_without_join_borrow_safety
      hcondition htrue hfalse hjoin henvJoin hsameLeft hsameRight hwellJoin
      hcoherent hlinear)

end Paper
end LwRust
