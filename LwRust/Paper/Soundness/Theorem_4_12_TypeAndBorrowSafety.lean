import LwRust.Paper.Soundness.Lemma_4_11_Preservation

/-!
# Theorem 4.12 (Type and Borrow Safety)

Paper statement (Section 4.5):

> Let `S₁ ▷ t` be a valid state; let `σ` be a store typing where `S₁ ▷ t ⊢ σ`;
> let `Γ₁` be a well-formed typing environment with respect to a lifetime `l`
> where `S₁ ∼ Γ₁`; let `Γ₂` be a typing environment; and let `T` be a type.  If
> `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂`, then `⟨S₁ ▷ t ⟶* S₂ ▷ v⟩^l` for some terminal
> state `S₂ ▷ v`.

The paper states terminal existence directly and then notes in Section 4.5.2
that this relies on termination of the presented calculus.  This mechanized
wrapper does not prove normalization; it exposes the terminal run as the
explicit `TerminatesAsValue` witness and then combines Lemma 4.10 (Progress)
with Lemma 4.11 (Preservation).  For nontermination-friendly safety, use the
progress component `typeAndBorrowProgress`, or its non-terminal corollary
`progress_runtime_step`.

The preservation-backed terminal safety component is scoped to `SourceTerm`
continuations for arbitrary runtime store typings.  Empty-initial wrappers such
as `emptyInitial_typeAndBorrowSafety` and
`theorem_4_12_typeAndBorrowSafety_emptyInitial` derive that premise from
typability under `StoreTyping.empty`.
-/

namespace LwRust
namespace Paper

open Core



/-! ## Section 4.5: Type and Borrow Safety -/

/-- A term terminates when it multisteps to a runtime value. -/
def TerminatesAsValue (store : ProgramStore) (lifetime : Lifetime) (term : Term) : Prop :=
  ∃ finalStore finalValue,
    MultiStep store lifetime term finalStore (.val finalValue)

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
  exact progress_typing hvalidStoreTyping hslotsOutlive hsafe hstoreProgress htyping

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
  exact ⟨typeAndBorrowProgress hvalidRuntime hvalidStoreTyping hwellFormed.2.1 hsafe
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

/--
Progress at every reachable state.

This is the step-level invariant re-establishment missing from the
terminal-only preservation statement: starting from a well-typed, well-formed,
borrow-safe source state over a finite-support store, *every* state reachable
by the reduction relation is either terminal or can take a further step.

The proof mirrors the terminal preservation induction: it follows the typing
derivation, decomposes the partial execution with the prefix-inversion lemmas,
re-establishes the mid-state invariants for completed subterms from terminal
preservation (Lemma 4.11), the well-formedness induction (Lemma 4.9), and the
internal borrow-safety induction, and re-establishes the operational store facts
from step-stable finite support.
-/
theorem reachable_progress_bounded
    (hborrowTyping : BorrowSafeTypingPreservation) (fuel : Nat)
    {store store' : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term term' : Term}
    {ty : Ty} :
    term.size ≤ fuel →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    store.FiniteSupport →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term store' term' →
    ProgressResult store' lifetime term' := by
  induction fuel generalizing store store' env₁ env₂ typing lifetime term term' ty with
  | zero =>
      intro hsize _hsource _hvalidRuntime _hvalidStoreTyping _hwellFormed
        _hborrowSafe _hsafe _hfinite _htyping _hmulti
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
  intro hsize hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe
    hfinite htyping hmulti
  refine TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      term.size ≤ fuel.succ →
      currentTyping = typing →
      SourceTerm term →
      ∀ (store store' : ProgramStore) (term' : Term),
        ValidRuntimeState store term →
        ValidStoreTyping store term currentTyping →
        WellFormedEnv env lifetime →
        BorrowSafeEnv env →
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
        WellFormedEnv env blockLifetime →
        BorrowSafeEnv env →
        store ∼ₛ env →
        store.FiniteSupport →
        MultiStep store outerLifetime (.block blockLifetime terms)
          store' term' →
        ProgressResult store' outerLifetime term')
    ?const ?missing ?copy ?move ?mutBorrow ?immBorrow ?box ?block
    ?declare ?assign ?eq ?ite ?iteDiverging ?iteTrueDiverging
    ?singleton ?cons htyping hsize rfl hsource store store' term'
    hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe hfinite hmulti
  -- T-Const: values are terminal; runs from them are empty.
  case const =>
    intro _env _typing _lifetime _value _ty _hvalueTyping _hsize _htypingEq
      _hsource store store' term' _hvalid _hvst _hwf _hbs _hsafe _hfs hmulti
    rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
    subst hstore
    subst hterm
    exact Or.inl (value_terminal _)
  case missing =>
    intro _env _typing _lifetime _ty _hwellTy _hloanFree _hsize _htypingEq
      _hsource store store' term' _hvalid _hvst _hwf _hbs _hsafe _hfs hmulti
    rcases multistep_missing_inv hmulti with ⟨hstore, hterm⟩
    subst hstore
    subst hterm
    exact Or.inr ⟨_, .missing, Step.missing⟩
  -- T-Copy: a single redex; afterwards the term is a value.
  case copy =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hcopy hnotRead
      _hsize htypingEq _hsource store store' term' _hvalid _hvst hwf _hbs
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
      _hbs hsafe _hfs hmulti
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
      _hsize htypingEq _hsource store store' term' _hvalid _hvst hwf _hbs
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
      htypingEq _hsource store store' term' _hvalid _hvst hwf _hbs hsafe _hfs
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
      hsource store store' term' hvalid hvst hwf hbs hsafe hfs hmulti
    cases htypingEq
    rcases multistep_box_prefix_inv hmulti with
      ⟨inner', hfinal, hms⟩ | ⟨midStore, value, _hms, hredex⟩
    · subst hfinal
      have hprogress :=
        ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl (SourceTerm.box_inner hsource) store store' inner'
          (validRuntimeState_box_inner hvalid)
          (validStoreTyping_box_inner hvst) hwf hbs hsafe hfs hms
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
      store' term' hvalid hvst hwf hbs hsafe hfs hmulti
    cases htypingEq
    exact ih hsize rfl hsource _lifetime store store' term' hblockChild hvalid
      hvst (WellFormedEnv.weaken hwf (LifetimeChild.outlives hblockChild)) hbs
      hsafe hfs hmulti
  -- T-Declare: either still inside the initialiser, or the declare redex
  -- ended the run.
  case declare =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty _hfresh _hterm
      _hfreshOut _hcoh _henv ih hsize htypingEq hsource store store' term'
      hvalid hvst hwf hbs hsafe hfs hmulti
    cases htypingEq
    rcases multistep_declare_prefix_inv hmulti with
      ⟨inner', hfinal, hms⟩ | ⟨midStore, value, _hms, hredex⟩
    · subst hfinal
      have hprogress :=
        ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl (SourceTerm.declare_inner hsource) store store' inner'
          (validRuntimeState_declare_inner hvalid)
          (validStoreTyping_declare_inner hvst) hwf hbs hsafe hfs hms
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
      _rhsTy hRhs hLhsPost _hshape _hwellTy _hwrite _hnoStale _hranked
      _hcoh _hcontained _hnotWrite ih hsize htypingEq hsource store store' term'
      hvalid hvst hwf hbs hsafe hfs hmulti
    cases htypingEq
    have hsourceRhs : SourceTerm _rhs := SourceTerm.assign_inner hsource
    rcases multistep_assign_prefix_inv hmulti with
      ⟨rhs', hfinal, hms⟩ | ⟨midStore, value, _hms, hredex⟩
    · subst hfinal
      have hprogress :=
        ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceRhs store store' rhs'
          (validRuntimeState_assign_inner hvalid)
          (validStoreTyping_assign_inner hvst) hwf hbs hsafe hfs hms
      rcases hprogress with hterminal | ⟨storeNext, termNext, hstep⟩
      · rcases (terminal_iff_value rhs').mp hterminal with ⟨value, hvalue⟩
        subst hvalue
        -- the rhs finished: re-establish the post-rhs invariants and fire
        -- the assignment redex
        have hterminalRhs :=
          preservation hsourceRhs (validRuntimeState_assign_inner hvalid)
            (validStoreTyping_assign_inner hvst) hwf hsafe hRhs hms
        rcases lvalTyping_allocated_location_of_safe hterminalRhs.2.1
            hLhsPost with ⟨location, slot, hloc, hslot⟩
        have hread : store'.read _lhs = some slot := by
          simp [ProgramStore.read, hloc, hslot]
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
      htypingEq hsource store store' term' hvalid hvst hwf hbs hsafe hfs
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
        ihL (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceLeft store store' lhs'
          (validRuntimeState_of_sourceTerm hsourceLeft hvalid)
          hvstLeft hwf hbs hsafe hfs hmsLeft
      rcases hprogressLeft with hterminalLeft | hstepLeft
      · rcases (terminal_iff_value lhs').mp hterminalLeft with
          ⟨leftValue, hleftValue⟩
        subst hleftValue
        have hterminalLeftState :=
          preservation hsourceLeft
            (validRuntimeState_of_sourceTerm hsourceLeft hvalid)
            hvstLeft hwf hsafe _hLhs hmsLeft
        have hwellLeft : WellFormedEnv _env₂ _lifetime :=
          (typingPreservesWellFormed_of_sourceTerm hsourceLeft
            (ValidRuntimeState.validState
              (validRuntimeState_of_sourceTerm hsourceLeft hvalid))
            hwf hsafe _hLhs).1
        have hvalidRight : ValidRuntimeState store' _rhs :=
          validRuntimeState_of_sourceTerm hsourceRight hterminalLeftState.1
        have hvstRight : ValidStoreTyping store' _rhs typing :=
          validStoreTyping_sourceTerm_of_validStoreTyping hsourceRight
            hvstRightSource
        have hprogressRight : ProgressResult store' _lifetime _rhs := by
          exact typeAndBorrowProgress hvalidRight hvstRight hwellLeft.2.1
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
        preservation hsourceLeft
          (validRuntimeState_of_sourceTerm hsourceLeft hvalid)
          hvstLeft hwf hsafe _hLhs hmsLeft
      have hborrowSafeLeft : BorrowSafeEnv _env₂ :=
        (hborrowTyping hsourceLeft hbs _hLhs).1
      have hvalidRight : ValidRuntimeState midStore _rhs :=
        validRuntimeState_of_sourceTerm hsourceRight hterminalLeftState.1
      have hvstRight : ValidStoreTyping midStore _rhs typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceRight
          hvstRightSource
      have hwellLeft : WellFormedEnv _env₂ _lifetime :=
        (typingPreservesWellFormed_of_sourceTerm hsourceLeft
          (ValidRuntimeState.validState
            (validRuntimeState_of_sourceTerm hsourceLeft hvalid))
          hwf hsafe _hLhs).1
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
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            hsourceRight hvalidRight hvstRight hwellLeft hborrowSafeLeft
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
      _hfalse _hjoin _henvJoin _hsameLeft _hsameRight _hwellJoin
      _hcoherent _hlinear ihCondition ihTrue ihFalse hsize htypingEq hsource
      store store' term' hvalid hvst hwf hbs hsafe hfs hmulti
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
        ihCondition (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceCondition store store' condition'
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hbs hsafe hfs hmsCondition
      rcases hprogressCondition with hterminalCondition | hstepCondition
      · rcases (terminal_iff_value condition').mp hterminalCondition with
          ⟨conditionValue, hconditionValue⟩
        subst hconditionValue
        have hterminalConditionState :=
          preservation hsourceCondition
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
        preservation hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hborrowSafeCondition : BorrowSafeEnv _env₂ :=
        (hborrowTyping hsourceCondition hbs
          _hcondition).1
      have hvalidTrue : ValidRuntimeState midStore _trueBranch :=
        validRuntimeState_of_sourceTerm hsourceTrue hterminalConditionState.1
      have hvstTrue : ValidStoreTyping midStore _trueBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
          hvstTrueSource
      exact ihTrue (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl hsourceTrue midStore store' term' hvalidTrue hvstTrue
        (typingPreservesWellFormed_of_sourceTerm hsourceCondition
          (ValidRuntimeState.validState
            (validRuntimeState_of_sourceTerm hsourceCondition hvalid))
          hwf hsafe _hcondition).1
        hborrowSafeCondition hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsTrue
    · have hterminalConditionState :=
        preservation hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hborrowSafeCondition : BorrowSafeEnv _env₂ :=
        (hborrowTyping hsourceCondition hbs
          _hcondition).1
      have hvalidFalse : ValidRuntimeState midStore _falseBranch :=
        validRuntimeState_of_sourceTerm hsourceFalse hterminalConditionState.1
      have hvstFalse : ValidStoreTyping midStore _falseBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceFalse
          hvstFalseSource
      exact ihFalse (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl hsourceFalse midStore store' term' hvalidFalse hvstFalse
        (typingPreservesWellFormed_of_sourceTerm hsourceCondition
          (ValidRuntimeState.validState
            (validRuntimeState_of_sourceTerm hsourceCondition hvalid))
          hwf hsafe _hcondition).1
        hborrowSafeCondition hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsFalse
  -- T-IfDiv: every path recurses into a premise IH; the dead branch is
  -- typed, so execution inside it keeps progressing.
  case iteDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition _trueBranch
      _falseBranch _trueTy _falseTy _hcondition _htrue _hfalse _hdiverges
      ihCondition ihTrue ihFalse hsize htypingEq hsource store store' term'
      hvalid hvst hwf hbs hsafe hfs hmulti
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
        ihCondition (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceCondition store store' condition'
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hbs hsafe hfs hmsCondition
      rcases hprogressCondition with hterminalCondition | hstepCondition
      · rcases (terminal_iff_value condition').mp hterminalCondition with
          ⟨conditionValue, hconditionValue⟩
        subst hconditionValue
        have hterminalConditionState :=
          preservation hsourceCondition
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
        preservation hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hborrowSafeCondition : BorrowSafeEnv _env₂ :=
        (hborrowTyping hsourceCondition hbs
          _hcondition).1
      have hvalidTrue : ValidRuntimeState midStore _trueBranch :=
        validRuntimeState_of_sourceTerm hsourceTrue hterminalConditionState.1
      have hvstTrue : ValidStoreTyping midStore _trueBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
          hvstTrueSource
      exact ihTrue (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl hsourceTrue midStore store' term' hvalidTrue hvstTrue
        (typingPreservesWellFormed_of_sourceTerm hsourceCondition
          (ValidRuntimeState.validState
            (validRuntimeState_of_sourceTerm hsourceCondition hvalid))
          hwf hsafe _hcondition).1
        hborrowSafeCondition hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsTrue
    · have hterminalConditionState :=
        preservation hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hborrowSafeCondition : BorrowSafeEnv _env₂ :=
        (hborrowTyping hsourceCondition hbs
          _hcondition).1
      have hvalidFalse : ValidRuntimeState midStore _falseBranch :=
        validRuntimeState_of_sourceTerm hsourceFalse hterminalConditionState.1
      have hvstFalse : ValidStoreTyping midStore _falseBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceFalse
          hvstFalseSource
      exact ihFalse (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl hsourceFalse midStore store' term' hvalidFalse hvstFalse
        (typingPreservesWellFormed_of_sourceTerm hsourceCondition
          (ValidRuntimeState.validState
            (validRuntimeState_of_sourceTerm hsourceCondition hvalid))
          hwf hsafe _hcondition).1
        hborrowSafeCondition hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsFalse
  -- T-IfDivT: symmetric case, with the true branch diverging.
  case iteTrueDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition _trueBranch
      _falseBranch _trueTy _falseTy _hcondition _htrue _hfalse _hdiverges
      ihCondition ihTrue ihFalse hsize htypingEq hsource store store' term'
      hvalid hvst hwf hbs hsafe hfs hmulti
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
        ihCondition (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl hsourceCondition store store' condition'
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hbs hsafe hfs hmsCondition
      rcases hprogressCondition with hterminalCondition | hstepCondition
      · rcases (terminal_iff_value condition').mp hterminalCondition with
          ⟨conditionValue, hconditionValue⟩
        subst hconditionValue
        have hterminalConditionState :=
          preservation hsourceCondition
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
        preservation hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hborrowSafeCondition : BorrowSafeEnv _env₂ :=
        (hborrowTyping hsourceCondition hbs
          _hcondition).1
      have hvalidTrue : ValidRuntimeState midStore _trueBranch :=
        validRuntimeState_of_sourceTerm hsourceTrue hterminalConditionState.1
      have hvstTrue : ValidStoreTyping midStore _trueBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceTrue
          hvstTrueSource
      exact ihTrue (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl hsourceTrue midStore store' term' hvalidTrue hvstTrue
        (typingPreservesWellFormed_of_sourceTerm hsourceCondition
          (ValidRuntimeState.validState
            (validRuntimeState_of_sourceTerm hsourceCondition hvalid))
          hwf hsafe _hcondition).1
        hborrowSafeCondition hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsTrue
    · have hterminalConditionState :=
        preservation hsourceCondition
          (validRuntimeState_of_sourceTerm hsourceCondition hvalid)
          hvstCondition hwf hsafe _hcondition hmsCondition
      have hborrowSafeCondition : BorrowSafeEnv _env₂ :=
        (hborrowTyping hsourceCondition hbs
          _hcondition).1
      have hvalidFalse : ValidRuntimeState midStore _falseBranch :=
        validRuntimeState_of_sourceTerm hsourceFalse hterminalConditionState.1
      have hvstFalse : ValidStoreTyping midStore _falseBranch typing :=
        validStoreTyping_sourceTerm_of_validStoreTyping hsourceFalse
          hvstFalseSource
      exact ihFalse (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        rfl hsourceFalse midStore store' term' hvalidFalse hvstFalse
        (typingPreservesWellFormed_of_sourceTerm hsourceCondition
          (ValidRuntimeState.validState
            (validRuntimeState_of_sourceTerm hsourceCondition hvalid))
          hwf hsafe _hcondition).1
        hborrowSafeCondition hterminalConditionState.2.1
        (hfs.multiStep hmsCondition) hmsFalse
  -- T-Seq singleton: in-flight head, or the block-exit drop ended the run.
  case singleton =>
    intro _env₁ _env₂ _typing _blockLifetime _term _ty hterm ih hsize htypingEq
      hsource outerLifetime store store' term' _hchild hvalid hvst hwf hbs hsafe
      hfs hmulti
    cases htypingEq
    rcases multistep_block_prefix_inv hmulti with
      ⟨head', hfinal, hms⟩ | ⟨midStore, value, _hms, hcont⟩
    · subst hfinal
      have hprogress :=
        ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
          rfl (SourceTerm.block_head hsource) store store' head'
          (validRuntimeState_block_singleton_inner hvalid)
          (validStoreTyping_block_singleton_inner hvst) hwf hbs hsafe hfs
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
      store store' term' hchild hvalid hvst hwf hbs hsafe hfs hmulti
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
          (validStoreTyping_block_head hvst) hwf hbs hsafe hfs hms
      exact progress_block_of_head_progress
        (OperationalStoreProgress.of_finiteSupport (hfs.multiStep hms))
        hprogress
    · rcases hcont with
        ⟨next', rest'', dropStore, heq, hdrops, hmsTail⟩ | ⟨heq, _⟩
      · cases heq
        -- the head finished: re-establish the mid-state invariants and
        -- recurse into the tail
        have hterminalHeadRuntime :=
          preservation hsourceHead (validRuntimeState_block_head hvalid)
            (validStoreTyping_block_head hvst) hwf hsafe hterm hmsHead
        have hwellInner : WellFormedEnv _env₂ _blockLifetime :=
          (typingPreservesWellFormed_of_sourceTerm hsourceHead
            (ValidRuntimeState.validState
              (validRuntimeState_block_head hvalid))
            hwf hsafe hterm).1
        have hborrowSafeInner : BorrowSafeEnv _env₂ :=
          (hborrowTyping hsourceHead hbs hterm).1
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
          safeAbstraction_seq_value_drop
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
          hborrowSafeInner hsafeTailAfter
          ((hfs.multiStep hmsHead).drops hdrops)
          hmsTail
      · cases heq

/-- Public reachable-progress theorem, with the size fuel hidden. -/
theorem reachable_progress {store store' : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term term' : Term}
    {ty : Ty} :
    BorrowSafeTypingPreservation →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    store.FiniteSupport →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term store' term' →
    ProgressResult store' lifetime term' := by
  intro hborrowTyping hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe
    hfinite htyping hmulti
  exact reachable_progress_bounded hborrowTyping term.size (Nat.le_refl _) hsource
    hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe hfinite
    htyping hmulti

/--
The step-stable soundness invariant: the state is a suffix of an execution
from a well-typed, well-formed, borrow-safe source state over a finite-support
store.

This is the invariant that the traditional single-step theorem
(`SoundState.step`) re-establishes, and it is strong enough to apply both
progress (`SoundState.progress`) and terminal preservation
(`SoundState.preservation`) at every state satisfying it.

A literal re-typing of intermediate continuations is not available in this
calculus: a declaration whose initialiser block declares the same variable
reaches intermediate states whose continuation is not typeable (the runtime
store already holds the inner variable's slot, while `T-Declare` requires the
outer binder fresh), even though execution remains safe.  Carrying the
originating typed run sidesteps this while still yielding progress and
preservation at every reachable state.
-/
def SoundState (store : ProgramStore) (lifetime : Lifetime) (term : Term) :
    Prop :=
  ∃ (initialStore : ProgramStore) (initialTerm : Term) (env₁ env₂ : Env)
    (typing : StoreTyping) (ty : Ty),
    SourceTerm initialTerm ∧
    ValidRuntimeState initialStore initialTerm ∧
    ValidStoreTyping initialStore initialTerm typing ∧
    WellFormedEnv env₁ lifetime ∧
    BorrowSafeEnv env₁ ∧
    initialStore ∼ₛ env₁ ∧
    initialStore.FiniteSupport ∧
    TermTyping env₁ typing lifetime initialTerm ty env₂ ∧
    MultiStep initialStore lifetime initialTerm store term

/-- Every well-set-up source state satisfies the soundness invariant. -/
theorem SoundState.initial {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    store.FiniteSupport →
    TermTyping env₁ typing lifetime term ty env₂ →
    SoundState store lifetime term :=
  fun hsource hvalid hvst hwf hbs hsafe hfs htyping =>
    ⟨store, term, env₁, env₂, typing, ty, hsource, hvalid, hvst, hwf, hbs,
      hsafe, hfs, htyping, MultiStep.refl⟩

/--
The traditional step theorem: a reduction step re-establishes the soundness
invariant for the successor state.
-/
theorem SoundState.step {store store' : ProgramStore} {lifetime : Lifetime}
    {term term' : Term} :
    SoundState store lifetime term →
    Step store lifetime term store' term' →
    SoundState store' lifetime term' := by
  rintro ⟨initialStore, initialTerm, env₁, env₂, typing, ty, hsource, hvalid,
    hvst, hwf, hbs, hsafe, hfs, htyping, hreached⟩ hstep
  exact ⟨initialStore, initialTerm, env₁, env₂, typing, ty, hsource, hvalid,
    hvst, hwf, hbs, hsafe, hfs, htyping,
    multistep_append hreached (step_multistep hstep)⟩

/-- The soundness invariant is closed under arbitrary execution. -/
theorem SoundState.multiStep {store store' : ProgramStore}
    {lifetime : Lifetime} {term term' : Term} :
    SoundState store lifetime term →
    MultiStep store lifetime term store' term' →
    SoundState store' lifetime term' := by
  rintro ⟨initialStore, initialTerm, env₁, env₂, typing, ty, hsource, hvalid,
    hvst, hwf, hbs, hsafe, hfs, htyping, hreached⟩ hmulti
  exact ⟨initialStore, initialTerm, env₁, env₂, typing, ty, hsource, hvalid,
    hvst, hwf, hbs, hsafe, hfs, htyping, multistep_append hreached hmulti⟩

/-- Progress holds at every state satisfying the soundness invariant. -/
theorem SoundState.progress {store : ProgramStore} {lifetime : Lifetime}
    {term : Term} :
    BorrowSafeTypingPreservation →
    SoundState store lifetime term →
    ProgressResult store lifetime term := by
  intro hborrowTyping
  rintro ⟨initialStore, initialTerm, env₁, env₂, typing, ty, hsource, hvalid,
    hvst, hwf, hbs, hsafe, hfs, htyping, hreached⟩
  exact reachable_progress hborrowTyping hsource hvalid hvst hwf hbs hsafe hfs htyping
    hreached

/--
Terminal preservation holds at every state satisfying the soundness
invariant: any terminal run from it ends in a safe state.
-/
theorem SoundState.preservation {store finalStore : ProgramStore}
    {lifetime : Lifetime} {term : Term} {finalValue : Value} :
    SoundState store lifetime term →
    MultiStep store lifetime term finalStore (.val finalValue) →
    ∃ env₂ ty, TerminalStateSafe finalStore finalValue env₂ ty := by
  rintro ⟨initialStore, initialTerm, env₁, env₂, typing, ty, hsource, hvalid,
    hvst, hwf, hbs, hsafe, _hfs, htyping, hreached⟩ hmulti
  exact ⟨env₂, ty,
    _root_.LwRust.Paper.preservation hsource hvalid hvst hwf hsafe htyping
      (multistep_append hreached hmulti)⟩

/--
No reachable state is stuck: from a well-typed, well-formed, borrow-safe
source state over a finite-support store, every state reachable by the
reduction relation is either terminal or can take a further step.

This is the composed soundness statement that the paper's Theorem 4.12
implies; unlike the conditional terminal-safety form, it does not assume
termination.
-/
theorem no_stuck_states {store store' : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term term' : Term}
    {ty : Ty} :
    BorrowSafeTypingPreservation →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    store.FiniteSupport →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term store' term' →
    Terminal term' ∨
      ∃ store'' term'', Step store' lifetime term' store'' term'' :=
  fun hborrowTyping hsource hvalid hvst hwf hbs hsafe hfs htyping hmulti =>
    reachable_progress hborrowTyping hsource hvalid hvst hwf hbs hsafe hfs
      htyping hmulti

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

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

/-- Theorem 4.12, conditional Type and Borrow Safety for source continuations.
This currently assumes termination, which is too strong, but we will anyways introduce non-termination later.
-/
theorem theorem_4_12_typeAndBorrowSafety
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hsource : SourceTerm term)
      (hvalid : ValidRuntimeState store term)
      (hstoreTyping : ValidStoreTyping store term typing)
      (hwellFormed : WellFormedEnv env₁ lifetime)
      (hsafe : store ∼ₛ env₁)
    (hstore : OperationalStoreProgress store)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hterminates : TerminatesAsValue store lifetime term) :
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty :=
    typeAndBorrowSafety hsource hvalid
      hstoreTyping hwellFormed hsafe hstore htyping hterminates

/--
Theorem 4.12, unstuckness form: no state reachable from a well-set-up source
state is stuck.  Unlike `theorem_4_12_typeAndBorrowSafety`, this does not
assume termination.
-/
theorem theorem_4_12_no_stuck_states
    {store store' : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term term' : Term} {ty : Ty}
    (hborrowTyping : BorrowSafeTypingPreservation)
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (hfinite : store.FiniteSupport)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hreach : MultiStep store lifetime term store' term') :
    Terminal term' ∨
      ∃ store'' term'', Step store' lifetime term' store'' term'' :=
  no_stuck_states hborrowTyping hsource hvalid hstoreTyping hwellFormed
    hborrowSafe hsafe hfinite htyping hreach

/--
Theorem 4.12, Type and Borrow Safety, total form.

Generated terms may contain `missing`, which diverges by self-loop, so this
interface assumes the terminal multistep instead of deriving termination from
typing.
-/
theorem theorem_4_12_typeAndBorrowSafety_total
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (hfinite : store.FiniteSupport)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hterminates : TerminatesAsValue store lifetime term) :
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty :=
  typeAndBorrowSafety hsource hvalid hstoreTyping hwellFormed
    hsafe (OperationalStoreProgress.of_finiteSupport hfinite) htyping hterminates

end LwRust.Paper.Soundness
