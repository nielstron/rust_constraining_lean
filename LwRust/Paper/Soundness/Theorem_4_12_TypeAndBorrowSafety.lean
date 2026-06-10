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
typability under `StoreTyping.empty`.  For arbitrary nonempty runtime
environments the preservation proof also needs the borrow-safety graph invariant;
the empty-initial wrappers discharge it with `borrowSafeEnv_empty`.
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
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress htyping
  exact progress_runtime hvalidRuntime hvalidStoreTyping hwellFormed hsafe
    hstoreProgress htyping

/--
Progress from mere typability of the current term.

The output environment and result type are intentionally existential: local
progress does not inspect them.
-/
theorem typeAndBorrowProgress_of_typable {store : ProgramStore} {env₁ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} :
    ValidRuntimeState store term →
      ValidStoreTyping store term typing →
      WellFormedEnv env₁ lifetime →
      store ∼ₛ env₁ →
      OperationalStoreProgress store →
    (∃ env₂ ty, TermTyping env₁ typing lifetime term ty env₂) →
    ProgressResult store lifetime term := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress htypable
  rcases htypable with ⟨env₂, ty, htyping⟩
  exact typeAndBorrowProgress hvalidRuntime hvalidStoreTyping hwellFormed hsafe
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
  exact ⟨typeAndBorrowProgress hvalidRuntime hvalidStoreTyping hwellFormed hsafe
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
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    TerminatesAsValue store lifetime term →
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe
    hsafe hstoreProgress htyping hterminates
  exact typeAndBorrowSafety_of_preservation hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hstoreProgress htyping
    (by
      intro finalStore finalValue hmulti
      exact preservation hsource hvalidRuntime hvalidStoreTyping
        hwellFormed hborrowSafe hsafe htyping hmulti)
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
borrow-safety induction (Corollary 4.14), and re-establishes the operational
store facts from step-stable finite support.
-/
theorem reachable_progress {store store' : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term term' : Term}
    {ty : Ty} :
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
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hsafe
    hfinite htyping hmulti
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
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
    -- T-Const: values are terminal; runs from them are empty.
    (fun {_env _typing _lifetime _value _ty} _hvalueTyping _htypingEq _hsource
        store store' term' _hvalid _hvst _hwf _hbs _hsafe _hfs hmulti => by
      rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
      subst hstore
      subst hterm
      exact Or.inl (value_terminal _))
    -- T-Copy: a single redex; afterwards the term is a value.
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy hnotRead
        htypingEq _hsource store store' term' _hvalid _hvst hwf _hbs hsafe
        _hfs hmulti => by
      cases htypingEq
      cases hmulti with
      | refl =>
          exact progress_copy_typing (typing := typing) hwf hsafe
            (TermTyping.copy hLv hcopy hnotRead)
      | trans hstep hrest =>
          cases hstep with
          | copy _hread =>
              rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
              subst hstore
              subst hterm
              exact Or.inl (value_terminal _))
    -- T-Move.
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite
        hmove htypingEq _hsource store store' term' _hvalid _hvst hwf _hbs
        hsafe _hfs hmulti => by
      cases htypingEq
      cases hmulti with
      | refl =>
          exact progress_move_typing (typing := typing) hwf hsafe
            (TermTyping.move hLv hnotWrite hmove)
      | trans hstep hrest =>
          cases hstep with
          | move _hread _hwrite =>
              rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
              subst hstore
              subst hterm
              exact Or.inl (value_terminal _))
    -- T-MutBorrow.
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hmutable
        hnotWrite htypingEq _hsource store store' term' _hvalid _hvst hwf _hbs
        hsafe _hfs hmulti => by
      cases htypingEq
      cases hmulti with
      | refl =>
          exact progress_borrow_typing (typing := typing) hwf hsafe
            (TermTyping.mutBorrow hLv hmutable hnotWrite)
      | trans hstep hrest =>
          cases hstep with
          | borrow _hloc =>
              rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
              subst hstore
              subst hterm
              exact Or.inl (value_terminal _))
    -- T-ImmBorrow.
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hnotRead
        htypingEq _hsource store store' term' _hvalid _hvst hwf _hbs hsafe
        _hfs hmulti => by
      cases htypingEq
      cases hmulti with
      | refl =>
          exact progress_borrow_typing (typing := typing) hwf hsafe
            (TermTyping.immBorrow hLv hnotRead)
      | trans hstep hrest =>
          cases hstep with
          | borrow _hloc =>
              rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
              subst hstore
              subst hterm
              exact Or.inl (value_terminal _))
    -- T-Box: either still inside the operand, or the box redex ended the run.
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih htypingEq hsource
        store store' term' hvalid hvst hwf hbs hsafe hfs hmulti => by
      cases htypingEq
      rcases multistep_box_prefix_inv hmulti with
        ⟨inner', hfinal, hms⟩ | ⟨midStore, value, _hms, hredex⟩
      · subst hfinal
        have hprogress :=
          ih rfl (SourceTerm.box_inner hsource) store store' inner'
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
        | subBox hinner => exact False.elim (value_no_step hinner))
    -- T-Block: delegate to the body induction at the block lifetime.
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild _hterms _hwellTy _hdrop ih htypingEq hsource
        store store' term' hvalid hvst hwf hbs hsafe hfs hmulti =>
      ih htypingEq hsource _lifetime store store' term' hblockChild hvalid
        hvst (WellFormedEnv.weaken hwf (LifetimeChild.outlives hblockChild))
        hbs hsafe hfs hmulti)
    -- T-Declare: either still inside the initialiser, or the declare redex
    -- ended the run.
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm _hfreshOut _hcoh _henv ih htypingEq hsource
        store store' term' hvalid hvst hwf hbs hsafe hfs hmulti => by
      cases htypingEq
      rcases multistep_declare_prefix_inv hmulti with
        ⟨inner', hfinal, hms⟩ | ⟨midStore, value, _hms, hredex⟩
      · subst hfinal
        have hprogress :=
          ih rfl (SourceTerm.declare_inner hsource) store store' inner'
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
        | subDeclare hinner => exact False.elim (value_no_step hinner))
    -- T-Assign: either still inside the rhs (with the redex available once it
    -- is a value), or the assignment redex ended the run.
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy
        _rhs _rhsTy}
        _hLhs hRhs hLhsPost _hshape _hwellTy _hwrite _hranked _hcoh
        _hcontained _hnotWrite ih htypingEq hsource
        store store' term' hvalid hvst hwf hbs hsafe hfs hmulti => by
      cases htypingEq
      have hsourceRhs : SourceTerm _rhs := SourceTerm.assign_inner hsource
      rcases multistep_assign_prefix_inv hmulti with
        ⟨rhs', hfinal, hms⟩ | ⟨midStore, value, _hms, hredex⟩
      · subst hfinal
        have hprogress :=
          ih rfl hsourceRhs store store' rhs'
            (validRuntimeState_assign_inner hvalid)
            (validStoreTyping_assign_inner hvst) hwf hbs hsafe hfs hms
        rcases hprogress with hterminal | ⟨storeNext, termNext, hstep⟩
        · rcases (terminal_iff_value rhs').mp hterminal with ⟨value, hvalue⟩
          subst hvalue
          -- the rhs finished: re-establish the post-rhs invariants and fire
          -- the assignment redex
          have hterminalRhs :=
            preservation hsourceRhs (validRuntimeState_assign_inner hvalid)
              (validStoreTyping_assign_inner hvst) hwf hbs hsafe hRhs hms
          have hwfOut : WellFormedEnv _env₂ _lifetime :=
            (typingPreservesWellFormed_of_sourceTerm hsourceRhs
              (ValidRuntimeState.validState
                (validRuntimeState_assign_inner hvalid))
              hwf hsafe hRhs).1
          rcases lvalTyping_allocated_location hwfOut hterminalRhs.2.1
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
        | subAssign hinner => exact False.elim (value_no_step hinner))
    -- T-Seq singleton: in-flight head, or the block-exit drop ended the run.
    (fun {_env₁ _env₂ _typing _blockLifetime _term _ty} hterm ih htypingEq
        hsource outerLifetime store store' term' _hchild hvalid hvst hwf hbs
        hsafe hfs hmulti => by
      cases htypingEq
      rcases multistep_block_prefix_inv hmulti with
        ⟨head', hfinal, hms⟩ | ⟨midStore, value, _hms, hcont⟩
      · subst hfinal
        have hprogress :=
          ih rfl (SourceTerm.block_head hsource) store store' head'
            (validRuntimeState_block_singleton_inner hvalid)
            (validStoreTyping_block_singleton_inner hvst) hwf hbs hsafe hfs
            hms
        exact progress_block_of_head_progress
          (OperationalStoreProgress.of_finiteSupport (hfs.multiStep hms))
          hprogress
      · rcases hcont with ⟨next, rest', _, heq, _, _⟩ | ⟨_, _, _, _, hterm'⟩
        · cases heq
        · subst hterm'
          exact Or.inl (value_terminal _))
    -- T-Seq cons: in-flight head, or the head finished, its value was
    -- dropped, and the block continued from the tail.
    (fun {_env₁ _env₂ _env₃ _typing _blockLifetime _term _rest _termTy
        _finalTy}
        hterm hrest ihHead ihRest htypingEq hsource outerLifetime store store'
        term' hchild hvalid hvst hwf hbs hsafe hfs hmulti => by
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
          ihHead rfl hsourceHead store store' head'
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
          have hterminalHead :=
            preservation hsourceHead (validRuntimeState_block_head hvalid)
              (validStoreTyping_block_head hvst) hwf hbs hsafe hterm hmsHead
          have hwellInner : WellFormedEnv _env₂ _blockLifetime :=
            (typingPreservesWellFormed_of_sourceTerm hsourceHead
              (ValidRuntimeState.validState
                (validRuntimeState_block_head hvalid))
              hwf hsafe hterm).1
          have hborrowSafeInner : BorrowSafeEnv _env₂ :=
            (typingPreservesBorrowSafeResult_global hsourceHead hbs hterm).1
          have hvalueBlockValid :
              ValidRuntimeState midStore
                (.block _blockLifetime (.val value :: next :: restTail)) :=
            validRuntimeState_block_value_cons_of_value_source_tail
              hsourceTail hterminalHead.1
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
            safeAbstraction_seq_value_drop hterminalHead.2.1
              hvalueBlockValid hwellInner hdrops
          have htailStoreTyping :
              ValidStoreTyping dropStore
                (.block _blockLifetime (next :: restTail)) typing :=
            validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
              (validStoreTyping_block_tail_of_cons hvst)
          exact ihRest rfl hsourceTail outerLifetime dropStore store' term'
            hchild hvalidTailAfter htailStoreTyping hwellInner
            hborrowSafeInner hsafeTailAfter
            ((hfs.multiStep hmsHead).drops hdrops) hmsTail
        · cases heq)
    htyping rfl hsource store store' term' hvalidRuntime hvalidStoreTyping
    hwellFormed hborrowSafe hsafe hfinite hmulti

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
    SoundState store lifetime term →
    ProgressResult store lifetime term := by
  rintro ⟨initialStore, initialTerm, env₁, env₂, typing, ty, hsource, hvalid,
    hvst, hwf, hbs, hsafe, hfs, htyping, hreached⟩
  exact reachable_progress hsource hvalid hvst hwf hbs hsafe hfs htyping
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
    _root_.LwRust.Paper.preservation hsource hvalid hvst hwf hbs hsafe htyping
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
  fun hsource hvalid hvst hwf hbs hsafe hfs htyping hmulti =>
    reachable_progress hsource hvalid hvst hwf hbs hsafe hfs htyping hmulti

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
      (hwellFormed : WellFormedEnv env₁ lifetime)
      (hsafe : store ∼ₛ env₁)
      (hstore : OperationalStoreProgress store)
    (htyping : ∃ env₂ ty, TermTyping env₁ typing lifetime term ty env₂) :
    ProgressResult store lifetime term :=
  typeAndBorrowProgress_of_typable hvalid hstoreTyping hwellFormed hsafe hstore htyping

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
      (hborrowSafe : BorrowSafeEnv env₁)
      (hsafe : store ∼ₛ env₁)
    (hstore : OperationalStoreProgress store)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hterminates : TerminatesAsValue store lifetime term) :
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty :=
    typeAndBorrowSafety hsource hvalid
      hstoreTyping hwellFormed hborrowSafe hsafe hstore htyping hterminates

/--
Corollary 4.14, Borrow Safety (paper interface).

Paper statement (Section 4.5):

> Let `S₁ ▷ t₁` and `S₂ ▷ t₂` be valid states; let `σ` be a store typing where
> `S₁ ▷ t₁ ⊢ σ`; let `Γ₁` be a well-formed borrow safe typing environment with
> respect to a lifetime `l` where `S₁ ∼ Γ₁`; let `Γ₂` be a typing environment;
> and, let `T₁, T₂` be types.  If `Γ₁ ⊢ ⟨t₁ : T₁⟩^l_σ ⊣ Γ₂` where
> `⟨S₁ ▷ t₁ ⟶ S₂ ▷ t₂⟩^l`, then, for arbitrary `γ ∈ fresh`, a well-formed and
> borrow safe typing environment `Γ₃[γ ↦ ⟨T₂⟩^l] ⊑ Γ₂[γ ↦ ⟨T₁⟩^l]` exists
> where `S₂ ∼ Γ₃`.

The output environment is existential and only `⊑`-related (Definition 3.9) to
the static output, which is the future-proof interface for extensions whose
static output conservatively abstracts several execution paths (control flow,
loops, recursive calls).  The calculus core witnesses the statement with
`Γ₃ = Γ₂` and `T₂ = T₁` (the strengthened appendix form is
`corollary_4_14_borrowSafety`); runs are taken to their terminal state, as in
Theorem 4.12.

The fresh-slot coherence obligations (`WellFormedTy` and
`FreshUpdateCoherenceObligations` for the result binding) are carried
explicitly, in line with the mechanisation's rule-carried coherence
obligations for fresh declarations.
-/
theorem corollary_4_14_borrowSafety_weakening
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty}
    {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue))
    (hwellTy : WellFormedTy env₂ ty lifetime)
    (gamma : Name)
    (hfresh : env₂.fresh gamma)
    (hfreshCoherence :
      FreshUpdateCoherenceObligations env₂ gamma ty lifetime) :
    ∃ env₃ resultTy,
      EnvStrengthens
        (env₃.update gamma { ty := .ty resultTy, lifetime := lifetime })
        (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ∧
      WellFormedEnv
        (env₃.update gamma { ty := .ty resultTy, lifetime := lifetime })
        lifetime ∧
      BorrowSafeEnv
        (env₃.update gamma { ty := .ty resultTy, lifetime := lifetime }) ∧
      finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue resultTy := by
  have hterminal :=
    lemma_4_11_preservation hsource hvalid hstoreTyping hwellFormed
      hborrowSafe hsafe htyping hmulti
  have hwf₂ : WellFormedEnv env₂ lifetime :=
    borrowInvariance_of_sourceTerm hsource hvalid.validState
      hwellFormed hsafe htyping
  have hbs :=
    typingPreservesBorrowSafeResult_global hsource hborrowSafe htyping
  exact ⟨env₂, ty, EnvStrengthens.refl _,
    borrowInvariance_result_extension hwf₂ hwellTy hfresh hfreshCoherence,
    hbs.2.2 gamma hfresh, hterminal.2.1, hterminal.2.2⟩

/--
Theorem 4.12, unstuckness form: no state reachable from a well-set-up source
state is stuck.  Unlike `theorem_4_12_typeAndBorrowSafety`, this does not
assume termination.
-/
theorem theorem_4_12_no_stuck_states
    {store store' : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term term' : Term} {ty : Ty}
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
  no_stuck_states hsource hvalid hstoreTyping hwellFormed hborrowSafe hsafe
    hfinite htyping hreach

end LwRust.Paper.Soundness
