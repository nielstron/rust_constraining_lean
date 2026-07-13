import FWRust.Paper.Soundness.InitialStates

/-!
# Lemma 9.8 (Alias Preservation)

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; let `σ` be a
> store typing … Then reduction preserves the validity (no duplicate owning
> references) invariant of states: `S₂ ▷ v` is valid.

Status: **mechanized** for the structural/redex fragments as the `validState`/
`validRuntimeState` preservation lemmas in `FWRust.Paper.Soundness`:

* `validState_blockB`, `validState_seq_step`, `validState_declare` — per-rule
  valid-state preservation fragments;
* `drops_validStore`, `dropsLifetime_validStore`, `validStore_write_*`,
  `validStore_update_*` — store-validity preservation under the primitive
  operations;
* `ValidRuntimeState` bundles Definition 4.3 validity with the explicit
  owner-allocation invariant the concrete store model needs.

The independent theorem
`appendix_9_oneStep_fullPreservation_of_runtime_invariants` below performs the
terminal one-step case split and proves the complete strict terminal package;
Lemma 9.8 is its validity projection.  The separate end-to-end multistep result
remains part of Preservation (Lemma 4.11).
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

/--
The one piece of static information about an already evaluated redex that is
not implied by `ValidRuntimeState` and `ValidStoreTyping`: an assignment's
runtime RHS type must be borrow-safe against the environment into which it is
written.  Every other terminal redex has no additional obligation.
-/
def RuntimeRedexBorrowSafe (env : Env) (typing : StoreTyping) : Term → Prop
  | .assign _ (.val value) =>
      ∀ {ty}, ValueTyping typing value ty → TyBorrowSafeAgainstEnv env ty
  | _ => True

/--
Shared strict one-step preservation theorem for Appendix Lemmas 9.8--9.10.

Unlike the closed source-term Preservation theorem, this theorem works on
already evaluated runtime redexes.  In particular, the operand of `R-Box`,
`R-Declare`, or `R-Assign` may be a runtime reference.  Finite support is not
used by any terminal one-step case.
-/
theorem appendix_9_oneStep_fullPreservation_of_runtime_invariants
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value}
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hredexBorrowSafe : RuntimeRedexBorrowSafe env₁ typing term)
    (hlinear : Linearizable env₁)
    (hsafe : store ≈ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hstep : Step store lifetime term finalStore (.val finalValue)) :
    FullTerminalStateSafe finalStore finalValue env₂ ty := by
  cases hstep with
  | copy hread =>
      cases htyping with
      | copy hLv hcopy hnotRead =>
          have hresult := preservation_copy_step_runtime_of_safe hsafe hvalid
            (TermTyping.copy (typing := typing) hLv hcopy hnotRead)
            (Step.copy (lifetime := lifetime) hread)
          exact ⟨hresult.1, hsafe, hresult.2.2⟩
  | move hread hwrite =>
      rename_i _valueLifetime lv
      cases htyping with
      | move hLv hnotWrite hmove =>
          have hwellOut : WellFormedEnv env₂ lifetime :=
            WellFormedEnv.move hwellFormed hmove hnotWrite
          have hwellTyOut : WellFormedTy env₂ ty lifetime := by
            refine WellFormedTy.move hwellFormed.1 hmove hnotWrite ?_
              (LValTyping.wellFormedTy hwellFormed hLv)
            intro mutable target hcontains
            exact LValTyping.contains_borrow hLv hcontains
          have hterminal :
              TerminalStateSafe finalStore finalValue env₂ ty := by
            cases lv with
            | var x =>
                rcases LValTyping.var_inv hLv with
                  ⟨slot, hslot, htyEq, hlifetimeEq⟩
                cases slot with
                | mk slotTy slotLifetime =>
                    cases htyEq
                    cases hlifetimeEq
                    exact RuntimeFrame.preservation_move_var_multistep_runtime_whenInitialized_of_wellFormed
                      hwellFormed.whenInitialized hsafe.whenInitialized hvalid
                      hslot hmove
                      (TermTyping.move (typing := typing) hLv hnotWrite hmove)
                      (MultiStep.trans
                        (Step.move (lifetime := lifetime) hread hwrite)
                        MultiStep.refl)
            | deref source =>
                cases hLv with
                | box hsourceBox =>
                    exact preservation_move_deref_box_multistep_runtime_whenInitialized_of_wellFormed
                      hwellFormed.whenInitialized hsafe.whenInitialized hvalid
                      hsourceBox hnotWrite hmove
                      (TermTyping.move (typing := typing)
                        (LValTyping.box hsourceBox) hnotWrite hmove)
                      (MultiStep.trans
                        (Step.move (lifetime := lifetime) hread hwrite)
                        MultiStep.refl)
                | boxFull hsourceFull =>
                    exact preservation_move_deref_boxFull_multistep_runtime_whenInitialized_of_wellFormed
                      hwellFormed.whenInitialized hsafe.whenInitialized hvalid
                      hsourceFull hnotWrite hmove
                      (TermTyping.move (typing := typing)
                        (LValTyping.boxFull hsourceFull) hnotWrite hmove)
                      (MultiStep.trans
                        (Step.move (lifetime := lifetime) hread hwrite)
                        MultiStep.refl)
                | borrow hsourceBorrow htargets =>
                    exfalso
                    rcases hmove with
                      ⟨moveSlot, struck, hslot, hstrike, _henv₂⟩
                    have hsourceSlot :
                        env₁.slotAt (LVal.base source) = some moveSlot := by
                      simpa [LVal.base] using hslot
                    have hstrikeAtBorrow :
                        Strike (LVal.path source ++ [()]) moveSlot.ty struck := by
                      simpa [LVal.path] using hstrike
                    rcases LValTyping.strike_suffix hsourceBorrow hsourceSlot
                        hstrikeAtBorrow with
                      ⟨borrowStruck, hborrowStruck⟩
                    cases borrowStruck <;> simp [Strike] at hborrowStruck
          exact TerminalStateSafe.full_of_wellFormed hterminal hwellOut
            hwellTyOut
  | box hfresh hbox =>
      rename_i _address value _ref
      cases htyping with
      | box hinner =>
          cases hinner with
          | const hvalueTyping =>
              rcases hstoreTyping value (by simp [termValues]) with
                ⟨storedTy, hstoredTyping, hvalidValue⟩
              have htyEq : storedTy = _ :=
                valueTyping_deterministic hstoredTyping hvalueTyping
              cases htyEq
              have hresult := preservation_box_step_runtime hstoreTyping
                hsafe.whenInitialized hvalid
                (TermTyping.box (TermTyping.const hvalueTyping))
                (Step.box (lifetime := lifetime) hfresh hbox)
              have hsafeFinal : finalStore ≈ₛ env₁ := by
                cases hbox
                exact safeAbstraction_boxAt hfresh hsafe
              exact ⟨hresult.1, hsafeFinal, hresult.2.2⟩
  | borrow hloc =>
      cases htyping with
      | mutBorrow hLv hmutable hnotWrite =>
          have hresult := preservation_borrow_step_runtime
            hsafe.whenInitialized hvalid
            (TermTyping.mutBorrow (typing := typing) hLv hmutable hnotWrite)
            (Step.borrow (lifetime := lifetime) hloc)
          exact ⟨hresult.1, hsafe, hresult.2.2⟩
      | immBorrow hLv hnotRead =>
          have hresult := preservation_borrow_step_runtime
            hsafe.whenInitialized hvalid
            (TermTyping.immBorrow (typing := typing) hLv hnotRead)
            (Step.borrow (lifetime := lifetime) hloc)
          exact ⟨hresult.1, hsafe, hresult.2.2⟩
  | assign hread hwrite hdrops =>
      rename_i _storeAfterWrite _lhs _oldSlot value
      cases htyping with
      | assign hRhs hLhsPost hshape hwellTy henvWrite hnotWrite =>
          cases hRhs with
          | const hvalueTyping =>
              rcases hstoreTyping value (by simp [termValues]) with
                ⟨storedTy, hstoredTyping, hvalidValue⟩
              have htyEq : storedTy = _ :=
                valueTyping_deterministic hstoredTyping hvalueTyping
              cases htyEq
              exact preservation_assign_step_runtime_of_linearized
                hwellFormed hborrowSafe
                (hredexBorrowSafe hvalueTyping) hsafe hvalid hLhsPost hshape
                hwellTy henvWrite hnotWrite hlinear hvalidValue
                (Step.assign (lifetime := lifetime) hread hwrite hdrops)
  | declare hstore =>
      rename_i x value
      cases htyping with
      | declare hinit hfresh henv₂ =>
          cases hinit with
          | const hvalueTyping =>
              rcases hstoreTyping value (by simp [termValues]) with
                ⟨storedTy, hstoredTyping, hvalidValue⟩
              have htyEq : storedTy = _ :=
                valueTyping_deterministic hstoredTyping hvalueTyping
              cases htyEq
              have hfreshStore : store.fresh (VariableProjection x) :=
                safeAbstraction_store_fresh_var hsafe.whenInitialized hfresh
              have hsafeFinal : finalStore ≈ₛ env₂ := by
                rw [henv₂, hstore]
                exact safeAbstraction_declare hsafe hfresh
                  (validPartialValue_declare hfreshStore hvalidValue)
                  (by
                    intro y envSlot oldValue _hy henvSlot hstoreSlot
                    rcases hsafe.2 y envSlot henvSlot with
                      ⟨safeValue, hsafeStore, hvalidOld⟩
                    have hvalueEq : safeValue = oldValue := by
                      rw [hstoreSlot] at hsafeStore
                      injection hsafeStore with hslotEq
                      exact (congrArg StoreSlot.value hslotEq).symm
                    subst oldValue
                    exact validPartialValue_declare hfreshStore hvalidOld)
              exact ⟨validRuntimeState_declare_step_of_validValue hvalid
                  hfreshStore hvalidValue
                  (Step.declare (lifetime := lifetime) hstore),
                hsafeFinal, ValidPartialValue.unit⟩
  | blockB hdropsLifetime =>
      rename_i blockLifetime
      cases htyping with
      | block hchild hterms hwellTy hdrop =>
          cases hterms with
          | singleton hinner =>
              cases hinner with
              | const hvalueTyping =>
                  rcases hstoreTyping finalValue (by simp [termValues]) with
                    ⟨storedTy, hstoredTyping, hvalidValue⟩
                  have htyEq : storedTy = _ :=
                    valueTyping_deterministic hstoredTyping hvalueTyping
                  cases htyEq
                  have hwellBody : WellFormedEnv env₁ blockLifetime :=
                    WellFormedEnv.weaken hwellFormed
                      (LifetimeChild.outlives hchild)
                  have hterminal :
                      TerminalStateSafe finalStore finalValue
                        (env₁.dropLifetime blockLifetime) ty :=
                    preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop
                      hvalid hsafe.whenInitialized hchild
                      hwellBody.whenInitialized hwellTy
                      hvalidValue.whenInitialized
                      (MultiStep.trans
                        (Step.blockB (lifetime := lifetime) hdropsLifetime)
                        MultiStep.refl)
                  have hstatic :
                      WellFormedEnv (env₁.dropLifetime blockLifetime) lifetime ∧
                        WellFormedTy (env₁.dropLifetime blockLifetime) ty
                          lifetime :=
                    block_preserves_wellFormed hchild hwellBody hwellTy rfl
                  rw [hdrop]
                  exact TerminalStateSafe.full_of_wellFormed hterminal
                    hstatic.1 hstatic.2
          | cons hhead hrest =>
              cases hrest

/--
The Appendix 9.8 one-step conclusion, exposed as the validity projection of
`appendix_9_oneStep_fullPreservation_of_runtime_invariants`.  This is independent
of the global source-term Preservation theorem and accepts already evaluated
runtime redexes.  `RuntimeRedexBorrowSafe` is nontrivial only for assignment,
whose runtime RHS type must be safe against existing environment loans.
-/
theorem lemma_9_8_aliasPreservation_oneStep_of_runtime_invariants
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value}
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hredexBorrowSafe : RuntimeRedexBorrowSafe env₁ typing term)
    (hlinear : Linearizable env₁)
    (hsafe : store ≈ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hstep : Step store lifetime term finalStore (.val finalValue)) :
    ValidState finalStore (.val finalValue) := by
  have hterminal :=
    appendix_9_oneStep_fullPreservation_of_runtime_invariants hvalid
      hstoreTyping hwellFormed hborrowSafe hredexBorrowSafe hlinear hsafe
      htyping hstep
  exact hterminal.1.1

/--
Source-initial one-step form.  Typing from the empty store/environment derives
all concrete runtime invariants automatically, leaving the paper-shaped typing
and reduction premises.
-/
theorem lemma_9_8_aliasPreservation_oneStep_empty
    {finalStore : ProgramStore} {env₂ : Env} {lifetime : Lifetime}
    {term : Term} {ty : Ty} {finalValue : Value}
    (htyping :
      TermTyping Env.empty StoreTyping.empty lifetime term ty env₂)
    (hstep :
      Step ProgramStore.empty lifetime term finalStore (.val finalValue)) :
    ValidState finalStore (.val finalValue) := by
  have hterminal := emptyInitial_preservation htyping
    (MultiStep.trans hstep MultiStep.refl)
  exact hterminal.1.1

end FWRust.Paper.Soundness
