import FWRust.Paper.Soundness.Lemma_4_11_Preservation

/-!
# Theorem 4.12 (Type and Borrow Safety)

Paper statement (Section 4.5):

> Let `S₁ ▷ t` be a valid state; let `σ` be a store typing where `S₁ ▷ t ⊢ σ`;
> let `Γ₁` be a well-formed typing environment with respect to a lifetime `l`
> where `S₁ ∼ Γ₁`; let `Γ₂` be a typing environment; and let `T` be a type.  If
> `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂`, then `⟨S₁ ▷ t ⟶* S₂ ▷ v⟩^l` for some terminal
> state `S₂ ▷ v`.

The paper states terminal existence directly and then notes in Section 4.5.2
that this relies on termination of the presented calculus.  The integrated
mechanization includes both generated `.missing`, a well-typed self-looping
placeholder, and source `while` loops.  The lower-level `typeAndBorrowSafety`
theorem therefore remains conditional on an explicit `TerminatesAsValue`
witness, while the total wrapper proves that witness for the syntactically
terminating fragment satisfying both `Term.MissingFree` and `Term.LoopFree`.

The preservation-backed terminal safety component is scoped to `SourceTerm`
continuations for arbitrary runtime store typings.  Empty-initial wrappers such
as `emptyInitial_typeAndBorrowSafety` derive `SourceTerm` from typability under
`StoreTyping.empty`; their total forms require both exclusion predicates.
-/

namespace FWRust
namespace Paper

open Core



/-! ## Section 4.5: Type and Borrow Safety -/

/-- A term terminates when it multisteps to a runtime value. -/
def TerminatesAsValue (store : ProgramStore) (lifetime : Lifetime) (term : Term) : Prop :=
  ∃ finalStore finalValue,
    MultiStep store lifetime term finalStore (.val finalValue)

theorem validPartialValueWhenInitialized_bool_inv {env : Env}
    {store : ProgramStore} {value : Value} :
    ValidPartialValueWhenInitialized env store (.value value) (.ty .bool) →
    value = .bool true ∨ value = .bool false := by
  intro hvalid
  cases hvalid with
  | bool =>
      rename_i value
      cases value <;> simp

/--
Missing- and loop-free source continuations terminate.

For source-shaped terms that syntactically exclude both generated `missing` and
source `while`, the typed evaluation tree is finite: each recursive call follows
a proper subterm, while terminal preservation supplies the safe abstraction
needed to continue after a subterm has evaluated.
-/
theorem terminatesAsValue_missingFree_bounded
    (fuel : Nat) {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    term.size ≤ fuel →
    SourceTerm term →
    term.MissingFree →
    term.LoopFree →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnvWhenInitialized env₁ lifetime →
    store ∼ₛ env₁ →
    store.FiniteSupport →
    TermTyping env₁ typing lifetime term ty env₂ →
    TerminatesAsValue store lifetime term := by
  induction fuel generalizing store env₁ env₂ typing lifetime term ty with
  | zero =>
      intro hsize _hsource _hfree _hloopFree _hvalidRuntime _hvalidStoreTyping
        _hwellFormed _hsafe _hfinite _htyping
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
  intro hsize hsource hfree hloopFree hvalidRuntime hvalidStoreTyping hwellFormed hsafe
    hfinite htyping
  refine TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      term.size ≤ fuel.succ →
      SourceTerm term →
      term.MissingFree →
      term.LoopFree →
      ∀ store,
        ValidRuntimeState store term →
        ValidStoreTyping store term currentTyping →
        WellFormedEnvWhenInitialized env lifetime →
        store ∼ₛ env →
        store.FiniteSupport →
        TerminatesAsValue store lifetime term)
    (motive_2 := fun env currentTyping blockLifetime terms _ty _env₂ _ =>
      Term.size (.block blockLifetime terms) ≤ fuel.succ →
      SourceTerm (.block blockLifetime terms) →
      Term.MissingFree (.block blockLifetime terms) →
      Term.LoopFree (.block blockLifetime terms) →
      ∀ outerLifetime store,
        LifetimeChild outerLifetime blockLifetime →
        ValidRuntimeState store (.block blockLifetime terms) →
        ValidStoreTyping store (.block blockLifetime terms) currentTyping →
        WellFormedEnvWhenInitialized env blockLifetime →
        store ∼ₛ env →
        store.FiniteSupport →
        TerminatesAsValue store outerLifetime (.block blockLifetime terms))
    ?const ?missing ?copy ?move ?mutBorrow ?immBorrow ?box ?block
    ?declare ?assign ?eq ?ite ?iteDiverging ?iteTrueDiverging
    ?whileLoopDiverging ?whileLoop
    ?singleton ?cons htyping hsize hsource hfree hloopFree store hvalidRuntime
    hvalidStoreTyping hwellFormed hsafe hfinite
  case const =>
    intro _env _typing _lifetime value _ty _hvalueTyping _hsize _hsource _hfree
      _hloopFree
      store _hvalidRuntime _hvalidStoreTyping _hwellFormed _hsafe _hfinite
    exact ⟨store, value, MultiStep.refl⟩
  case missing =>
    intro _env₁ _env₂ _typing _lifetime _ty _hloanFree _hfinite
      _hwellBridge _hsize _hsource hfree
      _hloopFree
      _store _hvalidRuntime _hvalidStoreTyping _hwellFormed _hsafe _hfinite
    exact False.elim hfree
  case copy =>
    intro _env _typing _lifetime _valueLifetime lv _ty hLv hcopy hnotRead
      _hsize _hsource _hfree _hloopFree store _hvalidRuntime _hvalidStoreTyping
      _hwellFormed hsafe _hfinite
    have htermTyping : TermTyping _env _typing _lifetime (.copy lv) _ty _env :=
      TermTyping.copy hLv hcopy hnotRead
    rcases progress_copy_typing_whenInitialized hsafe htermTyping with hterminal |
      ⟨store', term', hstep⟩
    · cases hterminal
    · cases hstep with
      | copy hread =>
          exact ⟨_, _, MultiStep.trans (Step.copy hread) MultiStep.refl⟩
  case move =>
    intro _env₁ _env₂ _typing _lifetime _valueLifetime lv _ty hLv hnotWrite
      hmove _hsize _hsource _hfree _hloopFree store _hvalidRuntime _hvalidStoreTyping
      _hwellFormed hsafe _hfinite
    have htermTyping : TermTyping _env₁ _typing _lifetime (.move lv) _ty _env₂ :=
      TermTyping.move hLv hnotWrite hmove
    rcases progress_move_typing_whenInitialized hsafe htermTyping with hterminal |
      ⟨store', term', hstep⟩
    · cases hterminal
    · cases hstep with
      | move hread hwrite =>
          exact ⟨_, _, MultiStep.trans (Step.move hread hwrite) MultiStep.refl⟩
  case mutBorrow =>
    intro _env _typing _lifetime _valueLifetime lv _ty hLv hmutable hnotWrite
      _hsize _hsource _hfree _hloopFree store _hvalidRuntime _hvalidStoreTyping
      _hwellFormed hsafe _hfinite
    have htermTyping :
        TermTyping _env _typing _lifetime (.borrow true lv) (.borrow true [lv]) _env :=
      TermTyping.mutBorrow hLv hmutable hnotWrite
    rcases progress_borrow_typing_whenInitialized hsafe htermTyping with hterminal |
      ⟨store', term', hstep⟩
    · cases hterminal
    · cases hstep with
      | borrow hloc =>
          exact ⟨_, _, MultiStep.trans (Step.borrow hloc) MultiStep.refl⟩
  case immBorrow =>
    intro _env _typing _lifetime _valueLifetime lv _ty hLv hnotRead
      _hsize _hsource _hfree _hloopFree store _hvalidRuntime _hvalidStoreTyping
      _hwellFormed hsafe _hfinite
    have htermTyping :
        TermTyping _env _typing _lifetime (.borrow false lv) (.borrow false [lv]) _env :=
      TermTyping.immBorrow hLv hnotRead
    rcases progress_borrow_typing_whenInitialized hsafe htermTyping with hterminal |
      ⟨store', term', hstep⟩
    · cases hterminal
    · cases hstep with
      | borrow hloc =>
          exact ⟨_, _, MultiStep.trans (Step.borrow hloc) MultiStep.refl⟩
  case box =>
    intro _env₁ _env₂ _typing _lifetime inner _ty hinner ih hsize hsource hfree
      hloopFree store hvalidRuntime hvalidStoreTyping hwellFormed hsafe hfinite
    rcases ih (by simp [Term.size] at hsize ⊢; omega)
        (SourceTerm.box_inner hsource)
        (Term.MissingFree.box_inner hfree)
        (Term.LoopFree.box_inner hloopFree)
        store
        (validRuntimeState_of_sourceTerm (SourceTerm.box_inner hsource) hvalidRuntime)
        (validStoreTyping_box_inner hvalidStoreTyping)
        hwellFormed hsafe hfinite with
      ⟨midStore, value, hmultiInner⟩
    have hfiniteMid : midStore.FiniteSupport :=
      hfinite.multiStep hmultiInner
    rcases (OperationalStoreProgress.of_finiteSupport hfiniteMid).freshHeap with
      ⟨address, hfresh⟩
    exact ⟨(midStore.boxAt address value).1, .ref (midStore.boxAt address value).2,
      multistep_append (MultiStep.subBox hmultiInner)
        (MultiStep.trans
          (Step.box (address := address) (ref := (midStore.boxAt address value).2)
            hfresh rfl)
          MultiStep.refl)⟩
  case block =>
    intro _env₁ _env₂ _env₃ _typing _lifetime blockLifetime terms _ty hchild
      _hterms _hwellTy _hdrop ih hsize hsource hfree hloopFree store hvalidRuntime
      hvalidStoreTyping hwellFormed hsafe hfinite
    exact ih hsize hsource hfree hloopFree _lifetime store hchild hvalidRuntime
      hvalidStoreTyping
      (WellFormedEnvWhenInitialized.weaken hwellFormed
        (LifetimeChild.outlives hchild))
      hsafe hfinite
  case declare =>
    intro _env₁ _env₂ _env₃ _typing _lifetime x inner _ty _hfresh hinner
      _hfreshOut _hcoh _henv ih hsize hsource hfree hloopFree store hvalidRuntime
      hvalidStoreTyping hwellFormed hsafe hfinite
    rcases ih (by simp [Term.size] at hsize ⊢; omega)
        (SourceTerm.declare_inner hsource)
        (Term.MissingFree.declare_inner hfree)
        (Term.LoopFree.declare_inner hloopFree)
        store
        (validRuntimeState_declare_inner hvalidRuntime)
        (validStoreTyping_declare_inner hvalidStoreTyping)
        hwellFormed hsafe hfinite with
      ⟨midStore, value, hmultiInner⟩
    exact ⟨midStore.declare x _lifetime value, .unit,
      multistep_append (MultiStep.subDeclare hmultiInner)
        (MultiStep.trans (Step.declare rfl) MultiStep.refl)⟩
  case assign =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime lhs _oldTy rhs
      rhsTy hRhs hLhsPost hshape hwellTy hwrite hnoStale hranked hcoh
      hcontained hnotWrite ih hsize hsource hfree hloopFree store hvalidRuntime
      hvalidStoreTyping hwellFormed hsafe hfinite
    rcases ih (by simp [Term.size] at hsize ⊢; omega)
        (SourceTerm.assign_inner hsource)
        (Term.MissingFree.assign_inner hfree)
        (Term.LoopFree.assign_inner hloopFree)
        store
        (validRuntimeState_of_sourceTerm (SourceTerm.assign_inner hsource)
          hvalidRuntime)
        (validStoreTyping_assign_inner hvalidStoreTyping)
        hwellFormed hsafe hfinite with
      ⟨midStore, value, hmultiRhs⟩
    have hterminalRhs :
        TerminalStateSafe midStore value _env₂ rhsTy :=
      preservation_bounded rhs.size (Nat.le_refl _) (SourceTerm.assign_inner hsource)
        (validRuntimeState_of_sourceTerm (SourceTerm.assign_inner hsource)
          hvalidRuntime)
        (validStoreTyping_assign_inner hvalidStoreTyping)
        hwellFormed hsafe hRhs hmultiRhs
    have hfiniteMid : midStore.FiniteSupport :=
      hfinite.multiStep hmultiRhs
    rcases read_defined_of_allocated
        (lvalTyping_allocated_location_of_safe_whenInitialized
          hterminalRhs.2.1 hLhsPost) with
      ⟨oldSlot, hread⟩
    rcases (OperationalStoreProgress.of_finiteSupport hfiniteMid).assignValue
        lhs oldSlot value hread with
      ⟨storeAfterWrite, storeAfterDrop, hwriteStore, hdrops⟩
    exact ⟨storeAfterDrop, .unit,
      multistep_append (MultiStep.subAssign hmultiRhs)
        (MultiStep.trans (Step.assign hread hwriteStore hdrops) MultiStep.refl)⟩
  case eq =>
    intro _env₁ _env₂ _env₃ _envGhost ghost _typing _lifetime lhs rhs lhsTy
      rhsTy hLhs hfresh htypeFresh htyFresh hstoreFresh hghostRhs hnotMention
      henvEq _hcopyL _hcopyR _hshape ihL _ihGhost hsize hsource hfree hloopFree store
      hvalidRuntime hvalidStoreTyping hwellFormed hsafe hfinite
    rcases ihL (by simp [Term.size] at hsize ⊢; omega)
        (SourceTerm.eq_lhs hsource)
        (Term.MissingFree.eq_lhs hfree)
        (Term.LoopFree.eq_lhs hloopFree)
        store
        (validRuntimeState_of_sourceTerm (SourceTerm.eq_lhs hsource) hvalidRuntime)
        hvalidStoreTyping.eq_lhs
        hwellFormed hsafe hfinite with
      ⟨midStore, leftValue, hmultiLeft⟩
    have hterminalLeft :
        TerminalStateSafe midStore leftValue _env₂ lhsTy :=
      preservation_bounded lhs.size (Nat.le_refl _) (SourceTerm.eq_lhs hsource)
        (validRuntimeState_of_sourceTerm (SourceTerm.eq_lhs hsource) hvalidRuntime)
        hvalidStoreTyping.eq_lhs hwellFormed hsafe hLhs hmultiLeft
    have hRhs : TermTyping _env₂ _typing _lifetime rhs rhsTy
        (_envGhost.erase ghost) :=
      TermTyping.erase_ghost
        (env := _env₂)
        (ghostSlot := { ty := .ty lhsTy, lifetime := _lifetime })
        hfresh htypeFresh
        (by
          intro hmem
          exact htyFresh (Ty.vars_subset_allVars hmem))
        hstoreFresh hnotMention hghostRhs
    have hwellLeft : WellFormedEnvWhenInitialized _env₂ _lifetime :=
      (typingPreservesWellFormedWhenInitialized_of_sourceTerm
        (SourceTerm.eq_lhs hsource) hwellFormed hLhs).1
    have hfiniteMid : midStore.FiniteSupport :=
      hfinite.multiStep hmultiLeft
    rcases ihFuel (by simp [Term.size] at hsize ⊢; omega)
        (SourceTerm.eq_rhs hsource)
        (Term.MissingFree.eq_rhs hfree)
        (Term.LoopFree.eq_rhs hloopFree)
        (validRuntimeState_of_sourceTerm (SourceTerm.eq_rhs hsource)
          hterminalLeft.1)
        (validStoreTyping_sourceTerm_of_validStoreTyping
          (SourceTerm.eq_rhs hsource) hvalidStoreTyping.eq_rhs)
        hwellLeft hterminalLeft.2.1 hfiniteMid hRhs with
      ⟨rightStore, rightValue, hmultiRight⟩
    by_cases heq : leftValue = rightValue
    · subst heq
      exact ⟨rightStore, .bool true,
        multistep_append (MultiStep.subEqLeft hmultiLeft)
          (multistep_append (MultiStep.subEqRight hmultiRight)
            (MultiStep.trans Step.eqTrue MultiStep.refl))⟩
    · exact ⟨rightStore, .bool false,
        multistep_append (MultiStep.subEqLeft hmultiLeft)
          (multistep_append (MultiStep.subEqRight hmultiRight)
            (MultiStep.trans (Step.eqFalse heq) MultiStep.refl))⟩
  case ite =>
    intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime condition trueBranch
      falseBranch _trueTy _falseTy _joinTy hcondition _htrue _hfalse _hjoin
      _henvJoin ihCondition ihTrue ihFalse
      hsize hsource hfree hloopFree store hvalidRuntime hvalidStoreTyping hwellFormed
      hsafe hfinite
    rcases ihCondition (by simp [Term.size] at hsize ⊢; omega)
        (SourceTerm.ite_condition hsource)
        (Term.MissingFree.ite_condition hfree)
        (Term.LoopFree.ite_condition hloopFree)
        store
        (validRuntimeState_of_sourceTerm (SourceTerm.ite_condition hsource)
          hvalidRuntime)
        hvalidStoreTyping.ite_condition
        hwellFormed hsafe hfinite with
      ⟨midStore, conditionValue, hmultiCondition⟩
    have hterminalCondition :
        TerminalStateSafe midStore conditionValue _env₂ .bool :=
      preservation_bounded condition.size (Nat.le_refl _)
        (SourceTerm.ite_condition hsource)
        (validRuntimeState_of_sourceTerm (SourceTerm.ite_condition hsource)
          hvalidRuntime)
        hvalidStoreTyping.ite_condition hwellFormed hsafe hcondition
        hmultiCondition
    have hwellCondition : WellFormedEnvWhenInitialized _env₂ _lifetime :=
      (typingPreservesWellFormedWhenInitialized_of_sourceTerm
        (SourceTerm.ite_condition hsource) hwellFormed hcondition).1
    have hfiniteMid : midStore.FiniteSupport :=
      hfinite.multiStep hmultiCondition
    rcases validPartialValueWhenInitialized_bool_inv
        hterminalCondition.2.2 with htrueValue | hfalseValue
    · subst htrueValue
      rcases ihTrue (by simp [Term.size] at hsize ⊢; omega)
          (SourceTerm.ite_trueBranch hsource)
          (Term.MissingFree.ite_trueBranch hfree)
          (Term.LoopFree.ite_trueBranch hloopFree)
          midStore
          (validRuntimeState_of_sourceTerm (SourceTerm.ite_trueBranch hsource)
            hterminalCondition.1)
          (validStoreTyping_sourceTerm_of_validStoreTyping
            (SourceTerm.ite_trueBranch hsource) hvalidStoreTyping.ite_trueBranch)
          hwellCondition hterminalCondition.2.1 hfiniteMid with
        ⟨finalStore, finalValue, hmultiTrue⟩
      exact ⟨finalStore, finalValue,
        multistep_append (MultiStep.subIte hmultiCondition)
          (MultiStep.trans Step.iteTrue hmultiTrue)⟩
    · subst hfalseValue
      rcases ihFalse (by simp [Term.size] at hsize ⊢; omega)
          (SourceTerm.ite_falseBranch hsource)
          (Term.MissingFree.ite_falseBranch hfree)
          (Term.LoopFree.ite_falseBranch hloopFree)
          midStore
          (validRuntimeState_of_sourceTerm (SourceTerm.ite_falseBranch hsource)
            hterminalCondition.1)
          (validStoreTyping_sourceTerm_of_validStoreTyping
            (SourceTerm.ite_falseBranch hsource) hvalidStoreTyping.ite_falseBranch)
          hwellCondition hterminalCondition.2.1 hfiniteMid with
        ⟨finalStore, finalValue, hmultiFalse⟩
      exact ⟨finalStore, finalValue,
        multistep_append (MultiStep.subIte hmultiCondition)
          (MultiStep.trans Step.iteFalse hmultiFalse)⟩
  case iteDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition _trueBranch
      _falseBranch _trueTy _falseTy _hcondition _htrue _hfalse hdiverges
      _ihCondition _ihTrue _ihFalse _hsize _hsource hfree _hloopFree _store _hvalidRuntime
      _hvalidStoreTyping _hwellFormed _hsafe _hfinite
    exact False.elim
      ((Term.MissingFree.not_diverges
        (Term.MissingFree.ite_falseBranch hfree)) hdiverges)
  case iteTrueDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition _trueBranch
      _falseBranch _trueTy _falseTy _hcondition _htrue _hfalse hdiverges
      _ihCondition _ihTrue _ihFalse _hsize _hsource hfree _hloopFree _store _hvalidRuntime
      _hvalidStoreTyping _hwellFormed _hsafe _hfinite
    exact False.elim
      ((Term.MissingFree.not_diverges
        (Term.MissingFree.ite_trueBranch hfree)) hdiverges)
  case whileLoopDiverging =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition _body
      _bodyTy _hchild _hcondition _hbody _hdiverges _ihCondition _ihBody
      _hsize _hsource _hfree hloopFree _store _hvalidRuntime
      _hvalidStoreTyping _hwellFormed _hsafe _hfinite
    exact False.elim hloopFree
  case whileLoop =>
    intro _env₁ _envBack _envInv _env₂ _env₃ _typing _lifetime
      _bodyLifetime _condition _body _bodyTy _hchild _hjoin _hcontained
      _hnameFresh _hcondition _hbody _hdrop _ihCondition _ihBody
      _hsize _hsource _hfree hloopFree _store _hvalidRuntime
      _hvalidStoreTyping _hwellFormed _hsafe _hfinite
    exact False.elim hloopFree
  case singleton =>
    intro _env₁ _env₂ _typing blockLifetime inner _ty hinner ih hsize hsource
      hfree hloopFree outerLifetime store hchild hvalidRuntime hvalidStoreTyping hwellFormed
      hsafe hfinite
    rcases ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        (SourceTerm.block_head hsource)
        (Term.MissingFree.block_head hfree)
        (Term.LoopFree.block_head hloopFree)
        store
        (validRuntimeState_block_singleton_inner hvalidRuntime)
        (validStoreTyping_block_singleton_inner hvalidStoreTyping)
        hwellFormed hsafe hfinite with
      ⟨midStore, value, hmultiInner⟩
    have hfiniteMid : midStore.FiniteSupport :=
      hfinite.multiStep hmultiInner
    rcases (OperationalStoreProgress.of_finiteSupport hfiniteMid).dropLifetime
        blockLifetime with
      ⟨storeAfterDrop, hdrops⟩
    exact ⟨storeAfterDrop, value,
      multistep_append (MultiStep.blockHead (outerLifetime := outerLifetime)
        (rest := []) hmultiInner)
        (MultiStep.trans (Step.blockB (lifetime := outerLifetime) hdrops)
          MultiStep.refl)⟩
  case cons =>
    intro _env₁ _env₂ _env₃ _typing blockLifetime head rest _termTy _finalTy
      hhead hrest ihHead ihRest hsize hsource hfree hloopFree outerLifetime store hchild
      hvalidRuntime hvalidStoreTyping hwellFormed hsafe hfinite
    cases rest with
    | nil =>
        cases hrest
    | cons next restTail =>
        have hsourceHead : SourceTerm head :=
          SourceTerm.block_head hsource
        have hsourceTail : SourceTerm (.block blockLifetime (next :: restTail)) :=
          SourceTerm.block_tail hsource
        have hfreeHead : head.MissingFree :=
          Term.MissingFree.block_head hfree
        have hfreeTail : Term.MissingFree (.block blockLifetime (next :: restTail)) :=
          Term.MissingFree.block_tail hfree
        have hloopFreeHead : head.LoopFree :=
          Term.LoopFree.block_head hloopFree
        have hloopFreeTail : Term.LoopFree
            (.block blockLifetime (next :: restTail)) :=
          Term.LoopFree.block_tail hloopFree
        rcases ihHead (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            hsourceHead hfreeHead hloopFreeHead store
            (validRuntimeState_block_head hvalidRuntime)
            (validStoreTyping_block_head hvalidStoreTyping)
            hwellFormed hsafe hfinite with
          ⟨midStore, value, hmultiHead⟩
        have hterminalHead :
            TerminalStateSafe midStore value _env₂ _termTy :=
          preservation_bounded head.size (Nat.le_refl _) hsourceHead
            (validRuntimeState_block_head hvalidRuntime)
            (validStoreTyping_block_head hvalidStoreTyping)
            hwellFormed hsafe hhead hmultiHead
        have hwellInner : WellFormedEnvWhenInitialized _env₂ blockLifetime :=
          (typingPreservesWellFormedWhenInitialized_of_sourceTerm hsourceHead
            hwellFormed hhead).1
        have hfiniteMid : midStore.FiniteSupport :=
          hfinite.multiStep hmultiHead
        rcases (OperationalStoreProgress.of_finiteSupport hfiniteMid).dropValue
            value with
          ⟨storeAfterDrop, hdrops⟩
        have hseqStep :
            Step midStore outerLifetime
              (.block blockLifetime (.val value :: next :: restTail))
              storeAfterDrop (.block blockLifetime (next :: restTail)) :=
          Step.seq hdrops
        have hvalueBlockValid :
            ValidRuntimeState midStore
              (.block blockLifetime (.val value :: next :: restTail)) :=
          validRuntimeState_block_value_cons_of_value_source_tail
            hsourceTail hterminalHead.1
        have hvalidTailAfter :
            ValidRuntimeState storeAfterDrop
              (.block blockLifetime (next :: restTail)) :=
          validRuntimeState_seq_step hvalueBlockValid hseqStep
        have hsafeTailAfter :
            storeAfterDrop ∼ₛ _env₂ :=
          safeAbstraction_seq_value_drop_whenInitialized hterminalHead.2.1
            hvalueBlockValid hwellInner hdrops
        have htailStoreTyping :
            ValidStoreTyping storeAfterDrop
              (.block blockLifetime (next :: restTail)) _typing :=
          validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
            (validStoreTyping_block_tail_of_cons hvalidStoreTyping)
        have hfiniteAfterDrop : storeAfterDrop.FiniteSupport :=
          hfiniteMid.step hseqStep
        rcases ihRest (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            hsourceTail hfreeTail hloopFreeTail outerLifetime storeAfterDrop hchild
            hvalidTailAfter htailStoreTyping hwellInner hsafeTailAfter
            hfiniteAfterDrop with
          ⟨finalStore, finalValue, hmultiTail⟩
        exact ⟨finalStore, finalValue,
          multistep_append
            (MultiStep.blockHead (outerLifetime := outerLifetime)
              (rest := next :: restTail) hmultiHead)
            (MultiStep.trans hseqStep hmultiTail)⟩

theorem terminatesAsValue_missingFree {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    SourceTerm term →
    term.MissingFree →
    term.LoopFree →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnvWhenInitialized env₁ lifetime →
    store ∼ₛ env₁ →
    store.FiniteSupport →
    TermTyping env₁ typing lifetime term ty env₂ →
    TerminatesAsValue store lifetime term := by
  intro hsource hfree hloopFree hvalidRuntime hvalidStoreTyping hwellFormed hsafe hfinite
    htyping
  exact terminatesAsValue_missingFree_bounded term.size (Nat.le_refl _)
    hsource hfree hloopFree hvalidRuntime hvalidStoreTyping hwellFormed hsafe hfinite
    htyping

/--
The nontermination-friendly progress component of Theorem 4.12.

This is the part that remains valid when loops or recursion are added: a
well-typed current state is either already terminal or has a valid next step.
-/
theorem typeAndBorrowProgress {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    EnvSlotsOutlive env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
  ProgressResult store lifetime term := by
  intro _hvalidRuntime hvalidStoreTyping hslotsOutlive hsafe hstoreProgress htyping
  exact progress_typing hvalidStoreTyping hslotsOutlive hsafe
    hstoreProgress htyping

/--
Progress for the stale-aware initialized invariant.

This is the form to use once a current-state preservation invariant supplies
typing together with `SafeAbstraction`: full borrow-target
resolution is required only when the current typing rule actually dereferences
through those targets.
-/
theorem typeAndBorrowProgress_whenInitialized {store : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    EnvSlotsOutlive env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro _hvalidRuntime hvalidStoreTyping hslotsOutlive hsafe hstoreProgress htyping
  exact progress_typing hvalidStoreTyping hslotsOutlive hsafe hstoreProgress htyping

/--
Non-terminal initialized typed states can step.
-/
theorem typeAndBorrowStep_whenInitialized {store : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    EnvSlotsOutlive env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step store lifetime term store' term' := by
  intro hvalidRuntime hvalidStoreTyping hslotsOutlive hsafe hstoreProgress htyping
    hnotTerminal
  exact (typeAndBorrowProgress_whenInitialized hvalidRuntime hvalidStoreTyping
    hslotsOutlive hsafe hstoreProgress htyping).step_of_not_terminal
    hnotTerminal

/--
Progress under exactly the initialized current-state invariant used by
`preservation_bounded`: runtime validity, store typing, initialized
well-formedness, initialized safe abstraction, and term typing.
-/
theorem typeAndBorrowProgress_of_preservationInvariant {store : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnvWhenInitialized env₁ lifetime →
    SafeAbstraction store env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress htyping
  exact progress_runtime_whenInitialized hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hstoreProgress htyping

/--
Non-terminal states satisfying the same initialized current-state invariant as
`preservation_bounded` can step.
-/
theorem typeAndBorrowStep_of_preservationInvariant {store : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnvWhenInitialized env₁ lifetime →
    SafeAbstraction store env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step store lifetime term store' term' := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress htyping
    hnotTerminal
  exact (typeAndBorrowProgress_of_preservationInvariant hvalidRuntime
    hvalidStoreTyping hwellFormed hsafe hstoreProgress htyping).step_of_not_terminal
    hnotTerminal

/--
Progress from mere typability of the current term.

The output environment and result type are intentionally existential: local
progress does not inspect them.
-/
theorem typeAndBorrowProgress_of_typable {store : ProgramStore} {env₁ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} :
    ValidRuntimeState store term →
      ValidStoreTyping store term typing →
      EnvSlotsOutlive env₁ lifetime →
      store ∼ₛ env₁ →
      OperationalStoreProgress store →
    (∃ env₂ ty, TermTyping env₁ typing lifetime term ty env₂) →
    ProgressResult store lifetime term := by
  intro hvalidRuntime hvalidStoreTyping hslotsOutlive hsafe hstoreProgress htypable
  rcases htypable with ⟨env₂, ty, htyping⟩
  exact typeAndBorrowProgress hvalidRuntime hvalidStoreTyping hslotsOutlive hsafe
    hstoreProgress htyping

/--
Theorem 4.12 bridge, conditional terminal safety.

The paper's core calculus is intended to terminate.  This mechanisation keeps
that fact separate: the theorem is stated with an explicit terminal-run witness
and the Lemma 4.11 preservation conclusion as a premise.  Progress rules out an
initially stuck well-typed state; preservation turns the terminal multistep into
a safe terminal state.
-/
theorem typeAndBorrowSafety_of_preservation
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
      TermTyping env₁ typing lifetime term ty env₂ →
      (∀ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) →
        TerminalStateSafe finalStore finalValue env₂ ty) →
      TerminatesAsValue store lifetime term →
      ProgressResult store lifetime term ∧
        ∃ finalStore finalValue,
          MultiStep store lifetime term finalStore (.val finalValue) ∧
          TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress htyping
    hpreservation hterminates
  rcases hterminates with ⟨finalStore, finalValue, hmulti⟩
  exact ⟨typeAndBorrowProgress hvalidRuntime hvalidStoreTyping hwellFormed.2 hsafe
      hstoreProgress htyping,
    ⟨finalStore, finalValue, hmulti, hpreservation finalStore finalValue hmulti⟩⟩

/--
Theorem 4.12, conditional Type and Borrow Safety for source continuations.

The paper's theorem states terminal existence; this mechanized form is the
conditional safety theorem for an explicitly supplied terminal multistep.
-/
theorem typeAndBorrowSafety {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
      TermTyping env₁ typing lifetime term ty env₂ →
      TerminatesAsValue store lifetime term →
      ProgressResult store lifetime term ∧
        ∃ finalStore finalValue,
          MultiStep store lifetime term finalStore (.val finalValue) ∧
          TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed
    hsafe hstoreProgress htyping hterminates
  exact typeAndBorrowSafety_of_preservation hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hstoreProgress htyping
    (by
      intro finalStore finalValue hmulti
      exact preservation hsource hvalidRuntime hvalidStoreTyping
        hwellFormed hsafe htyping hmulti)
    hterminates

end Paper
end FWRust

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

/-- Theorem 4.12 progress component, without a termination assumption. -/
theorem theorem_4_12_typeAndBorrowProgress
    {store : ProgramStore} {env₁ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
      (hvalid : ValidRuntimeState store term)
      (hstoreTyping : ValidStoreTyping store term typing)
      (hslotsOutlive : EnvSlotsOutlive env₁ lifetime)
      (hsafe : store ∼ₛ env₁)
      (hstore : OperationalStoreProgress store)
    (htyping : ∃ env₂ ty, TermTyping env₁ typing lifetime term ty env₂) :
    ProgressResult store lifetime term :=
  typeAndBorrowProgress_of_typable hvalid hstoreTyping hslotsOutlive hsafe hstore htyping

/-- Theorem 4.12 progress component over the initialized invariant. -/
theorem theorem_4_12_typeAndBorrowProgress_whenInitialized
    {store : ProgramStore} {env₁ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
      (hvalid : ValidRuntimeState store term)
      (hstoreTyping : ValidStoreTyping store term typing)
      (hslotsOutlive : EnvSlotsOutlive env₁ lifetime)
      (hsafe : store ∼ₛ env₁)
      (hstore : OperationalStoreProgress store)
    (htyping : ∃ env₂ ty, TermTyping env₁ typing lifetime term ty env₂) :
    ProgressResult store lifetime term := by
  rcases htyping with ⟨env₂, ty, htyping⟩
  exact typeAndBorrowProgress_whenInitialized hvalid hstoreTyping hslotsOutlive
    hsafe hstore htyping

/--
Initialized typed current states do not get stuck: if the term is not terminal,
the operational semantics has a next step.
-/
theorem theorem_4_12_typeAndBorrowStep_whenInitialized
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
      (hvalid : ValidRuntimeState store term)
      (hstoreTyping : ValidStoreTyping store term typing)
      (hslotsOutlive : EnvSlotsOutlive env₁ lifetime)
      (hsafe : store ∼ₛ env₁)
      (hstore : OperationalStoreProgress store)
      (htyping : TermTyping env₁ typing lifetime term ty env₂)
      (hnotTerminal : ¬ Terminal term) :
    ∃ store' term', Step store lifetime term store' term' :=
  typeAndBorrowStep_whenInitialized hvalid hstoreTyping hslotsOutlive hsafe
    hstore htyping hnotTerminal

/--
Theorem 4.12 progress component under the same initialized current-state
invariant used by preservation.
-/
theorem theorem_4_12_typeAndBorrowStep_of_preservationInvariant
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
      (hvalid : ValidRuntimeState store term)
      (hstoreTyping : ValidStoreTyping store term typing)
      (hwellFormed : WellFormedEnvWhenInitialized env₁ lifetime)
      (hsafe : store ∼ₛ env₁)
      (hstore : OperationalStoreProgress store)
      (htyping : TermTyping env₁ typing lifetime term ty env₂)
      (hnotTerminal : ¬ Terminal term) :
    ∃ store' term', Step store lifetime term store' term' :=
  typeAndBorrowStep_of_preservationInvariant hvalid hstoreTyping hwellFormed
    hsafe hstore htyping hnotTerminal

/--
Theorem 4.12, Type and Borrow Safety for the terminating source fragment.

The lower-level `typeAndBorrowSafety` theorem remains conditional because the
integrated language includes the generated diverging `.missing` term.  This
paper-facing wrapper proves the terminal run for source terms that exclude both
that placeholder and `while`.
-/
theorem theorem_4_12_typeAndBorrowSafety
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hsource : SourceTerm term)
    (hfree : term.MissingFree)
    (hloopFree : term.LoopFree)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (hfinite : store.FiniteSupport)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    :
      ProgressResult store lifetime term ∧
        ∃ finalStore finalValue,
          MultiStep store lifetime term finalStore (.val finalValue) ∧
          TerminalStateSafe finalStore finalValue env₂ ty :=
  typeAndBorrowSafety hsource hvalid hstoreTyping hwellFormed hsafe
    (OperationalStoreProgress.of_finiteSupport hfinite) htyping
    (terminatesAsValue_missingFree hsource hfree hloopFree hvalid hstoreTyping
      (WellFormedEnv.whenInitialized hwellFormed) hsafe hfinite
      htyping)

/--
Theorem 4.12, Type and Borrow Safety, total form.

Generated terms may contain `missing`, which diverges by self-loop, and source
terms may contain nonterminating loops.  For missing- and loop-free source
terms, terminal execution is derived rather than assumed.
-/
theorem theorem_4_12_typeAndBorrowSafety_total
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hsource : SourceTerm term)
    (hfree : term.MissingFree)
    (hloopFree : term.LoopFree)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (hfinite : store.FiniteSupport)
    (htyping : TermTyping env₁ typing lifetime term ty env₂) :
      ProgressResult store lifetime term ∧
        ∃ finalStore finalValue,
          MultiStep store lifetime term finalStore (.val finalValue) ∧
          TerminalStateSafe finalStore finalValue env₂ ty :=
  theorem_4_12_typeAndBorrowSafety hsource hfree hloopFree hvalid hstoreTyping hwellFormed
    hsafe hfinite htyping

end FWRust.Paper.Soundness
