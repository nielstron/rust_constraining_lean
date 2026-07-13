import FWRust.Paper.Soundness.InitialStates

/-!
# Corollary 4.14 (Borrow Safety)

The paper's Appendix strengthens Corollary 4.14 for the branch-free calculus:
the result environment itself remains well formed and borrow safe.  Moreover,
for any fresh name `gamma`, it remains so after installing the result type at
`gamma` with the ambient lifetime.

The general theorem below is source-continuation scoped, consistently with the
strict preservation interface.  The empty-initial wrapper needs no explicit
`SourceTerm` premise because typability under `StoreTyping.empty` implies it.
-/

namespace FWRust.Paper.Soundness

open FWRust.Core FWRust.Paper

/--
The literal printed Corollary 4.14 quantifies `T₂` arbitrarily but has no
premise typing the reduct at `T₂`.  That omission is substantive: an arbitrary
fresh result type need not be well formed.  This small witness is the static
obstruction used below to justify instantiating the otherwise unrelated `T₂`
with the preserved terminal type `T₁`.
-/
theorem corollary_4_14_arbitraryResultType_obstruction
    (lifetime : Lifetime) :
    ¬ WellFormedEnv
      (Env.empty.update "gamma"
        { ty := .ty (.borrow true (.var "missing")), lifetime := lifetime })
      lifetime := by
  intro hwell
  let resultTy : Ty := .borrow true (.var "missing")
  let resultSlot : EnvSlot := { ty := .ty resultTy, lifetime := lifetime }
  have hslot :
      (Env.empty.update "gamma" resultSlot).slotAt "gamma" =
        some resultSlot := by
    simp [Env.update]
  have hcontains :
      Env.empty.update "gamma" resultSlot ⊢ "gamma" ↝ resultTy := by
    exact ⟨resultSlot, hslot, by
      unfold resultSlot resultTy
      exact PartialTyContains.here⟩
  rcases hwell.1 "gamma" resultSlot true (.var "missing") hslot
      (by simpa [resultTy] using hcontains) with
    ⟨_targetTy, _targetLifetime, _htarget, _houtlives, hbase⟩
  rcases hbase with ⟨missingSlot, hmissing, _hslotOutlives⟩
  simp [Env.update, Env.empty, LVal.base] at hmissing

private def printedCounterLifetime : Lifetime := Lifetime.root

private def printedCounterStore : ProgramStore :=
  (ProgramStore.empty.boxAt 0 .unit).1

private def printedCounterRef : Reference :=
  (ProgramStore.empty.boxAt 0 .unit).2

private def printedCounterT₁ : Ty := .box .unit

private def printedCounterT₂ : Ty := .borrow true (.var "missing")

private def printedCounterGamma : Name := "gamma"

private theorem printedCounterTyping :
    TermTyping Env.empty StoreTyping.empty printedCounterLifetime
      (.box (.val .unit)) printedCounterT₁ Env.empty := by
  exact TermTyping.box (TermTyping.const ValueTyping.unit)

private theorem printedCounterStep :
    Step ProgramStore.empty printedCounterLifetime (.box (.val .unit))
      printedCounterStore (.val (.ref printedCounterRef)) := by
  exact Step.box
    (by simp [ProgramStore.fresh, ProgramStore.empty])
    (by rfl)

private theorem printedCounterInitialValid :
    ValidState ProgramStore.empty (.box (.val .unit)) := by
  exact validState_box_value_of_value validState_empty_unit

private theorem printedCounterFinalValid :
    ValidState printedCounterStore (.val (.ref printedCounterRef)) := by
  exact validState_box_step_of_validValue printedCounterInitialValid
    storeOwnersAllocated_empty ValidPartialValue.unit printedCounterStep

private theorem printedCounterStoreTyping :
    ValidStoreTyping ProgramStore.empty (.box (.val .unit)) StoreTyping.empty := by
  intro value hmem
  simp [termValues] at hmem
  subst hmem
  exact ⟨.unit, ValueTyping.unit, ValidPartialValue.unit⟩

/--
Counterexample to Corollary 4.14 read literally with an arbitrary, unrelated
`T₂`.  The empty-initial `box ()` step satisfies every printed premise.  The
conclusion nevertheless fails for `T₂ = &mut missing`: updating both sides at
the same fresh name would require that type to strengthen the preserved
`Box<Unit>` result type (and the chosen `T₂` is not well formed either).
-/
theorem corollary_4_14_printedStatement_counterexample :
    ValidState ProgramStore.empty (.box (.val .unit)) ∧
      ValidState printedCounterStore (.val (.ref printedCounterRef)) ∧
      ValidStoreTyping ProgramStore.empty (.box (.val .unit)) StoreTyping.empty ∧
      WellFormedEnv Env.empty printedCounterLifetime ∧
      BorrowSafeEnv Env.empty ∧
      ProgramStore.empty ≈ₛ Env.empty ∧
      TermTyping Env.empty StoreTyping.empty printedCounterLifetime
        (.box (.val .unit)) printedCounterT₁ Env.empty ∧
      Env.empty.fresh printedCounterGamma ∧
      MultiStep ProgramStore.empty printedCounterLifetime (.box (.val .unit))
        printedCounterStore (.val (.ref printedCounterRef)) ∧
      ¬ ∃ env₃,
        WellFormedEnv
            (env₃.update printedCounterGamma
              { ty := .ty printedCounterT₂,
                lifetime := printedCounterLifetime })
            printedCounterLifetime ∧
          BorrowSafeEnv
            (env₃.update printedCounterGamma
              { ty := .ty printedCounterT₂,
                lifetime := printedCounterLifetime }) ∧
          EnvStrengthens
            (env₃.update printedCounterGamma
              { ty := .ty printedCounterT₂,
                lifetime := printedCounterLifetime })
            (Env.empty.update printedCounterGamma
              { ty := .ty printedCounterT₁,
                lifetime := printedCounterLifetime }) ∧
          printedCounterStore ≈ₛ env₃ := by
  refine ⟨printedCounterInitialValid, printedCounterFinalValid,
    printedCounterStoreTyping, wellFormedEnv_empty _, borrowSafeEnv_empty,
    fullSafeAbstraction_empty, printedCounterTyping,
    by simp [Env.fresh, Env.empty],
    MultiStep.trans printedCounterStep MultiStep.refl, ?_⟩
  rintro ⟨_env₃, _hwell, _hborrowSafe, hstrengthens, _hsafe⟩
  have hstrengthAtGamma := hstrengthens printedCounterGamma
  simp [Env.update, printedCounterT₁, printedCounterT₂] at hstrengthAtGamma
  cases hstrengthAtGamma

/-- Strengthened core form of Corollary 4.14: source typing preserves both
Definition 4.8 well-formedness and Definition 4.13 borrow safety. -/
theorem corollary_4_14_borrowSafety_core
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    SourceTerm term →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ BorrowSafeEnv env₂ := by
  intro hsource hwell hborrowSafe htyping
  rcases typingPreservesWellFormed_of_sourceTerm hsource hwell hborrowSafe
      htyping with
    ⟨hwell₂, hborrowSafe₂, _hwellTy, _htySafe⟩
  exact ⟨hwell₂, hborrowSafe₂⟩

/-- The strengthened static calculus-core result stated as Corollary 4.13 in
the paper's Appendix: an arbitrary fresh result slot can be added while
preserving well-formedness and borrow safety. -/
theorem corollary_4_14_borrowSafety
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} {gamma : Name} :
    SourceTerm term →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    WellFormedEnv
        (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv
        (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource hwell hborrowSafe htyping hfresh
  rcases typingPreservesWellFormed_of_sourceTerm hsource hwell hborrowSafe
      htyping with
    ⟨hwell₂, hborrowSafe₂, hwellTy, htySafe⟩
  exact ⟨WellFormedEnv.update_fresh_ty hwell₂ hwellTy hfresh,
    borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv hborrowSafe₂ htySafe⟩

/-- Empty-initial specialization of the Appendix's static Corollary 4.13.  The
source-term premise and initial invariants are derived from empty typability. -/
theorem corollary_4_14_borrowSafety_emptyInitial
    {env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty} {gamma : Name} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    WellFormedEnv
        (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv
        (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro htyping hfresh
  exact corollary_4_14_borrowSafety
    (termTyping_empty_sourceTerm htyping)
    (wellFormedEnv_empty lifetime)
    borrowSafeEnv_empty htyping hfresh

/--
Corrected dynamic Corollary 4.14 for terminal executions from an arbitrary
state satisfying the mechanisation's concrete invariants.  The paper explicitly
permits `Γ₃ = Γ₂` for the branch-free core.  Because this Lean theorem concerns
a terminal reduct, it additionally repairs the printed unrelated type by taking
`T₂ = T₁`; the resulting strengthening is reflexive.  The unconstrained `T₂`
is refuted by `corollary_4_14_printedStatement_counterexample`.
-/
theorem corollary_4_14_borrowSafety_terminal_of_runtime_invariants
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty}
    {gamma : Name} {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ≈ₛ env₁)
    (hstoreFinite : store.FiniteSupport)
    (hlinear : Linearizable env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hfresh : env₂.fresh gamma)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    ∃ env₃,
      WellFormedEnv
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime })
          lifetime ∧
        BorrowSafeEnv
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime }) ∧
        EnvStrengthens
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime })
          (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ∧
        finalStore ≈ₛ env₃ := by
  have hstatic := corollary_4_14_borrowSafety hsource hwellFormed
    hborrowSafe htyping hfresh
  have henvFinite : Env.FiniteSupport env₁ :=
    Env.FiniteSupport.of_fullSafeAbstraction hstoreFinite hsafe
  have hterminal := lemma_4_11_preservation hsource hvalid hstoreTyping
    hwellFormed hborrowSafe henvFinite hlinear hsafe htyping hmulti
  exact ⟨env₂, hstatic.1, hstatic.2, EnvStrengthens.refl _, hterminal.2.1⟩

/-- One-step specialization of the corrected general dynamic corollary. -/
theorem corollary_4_14_borrowSafety_terminalStep_of_runtime_invariants
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty}
    {gamma : Name} {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ≈ₛ env₁)
    (hstoreFinite : store.FiniteSupport)
    (hlinear : Linearizable env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hfresh : env₂.fresh gamma)
    (hstep : Step store lifetime term finalStore (.val finalValue)) :
    ∃ env₃,
      WellFormedEnv
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime })
          lifetime ∧
        BorrowSafeEnv
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime }) ∧
        EnvStrengthens
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime })
          (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ∧
        finalStore ≈ₛ env₃ := by
  exact corollary_4_14_borrowSafety_terminal_of_runtime_invariants
    hsource hvalid hstoreTyping hwellFormed hborrowSafe hsafe hstoreFinite
    hlinear htyping hfresh (MultiStep.trans hstep MultiStep.refl)

/--
Corollary 4.14's dynamic conclusion for empty-initial executions that have
reached a terminal state.

This is the strongest direct source-initial instance supplied by the current
terminal-preservation theorem.  It repairs the printed unrelated `T₂` by
specializing it to the terminal type `T₁`; independently, it takes `Γ₃ = Γ₂`
as the paper explicitly permits for the branch-free core.  Consequently the
environment-strengthening premise is reflexive.  Initial validity, safe
abstraction, source syntax, finite support, and linearizability are all derived
from empty-initial typability by `emptyInitial_preservation`.
-/
theorem corollary_4_14_borrowSafety_emptyInitial_terminal
    {env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty}
    {gamma : Name} {finalStore : ProgramStore} {finalValue : Value} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
    ∃ env₃,
      WellFormedEnv
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime })
          lifetime ∧
        BorrowSafeEnv
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime }) ∧
        EnvStrengthens
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime })
          (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ∧
        finalStore ≈ₛ env₃ := by
  intro htyping hfresh hmulti
  have hstatic := corollary_4_14_borrowSafety_emptyInitial htyping hfresh
  have hterminal := emptyInitial_preservation htyping hmulti
  exact ⟨env₂, hstatic.1, hstatic.2, EnvStrengthens.refl _, hterminal.2.1⟩

/-- One-step spelling of
`corollary_4_14_borrowSafety_emptyInitial_terminal`, matching the reduction
premise printed in Corollary 4.14. -/
theorem corollary_4_14_borrowSafety_emptyInitial_terminalStep
    {env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty}
    {gamma : Name} {finalStore : ProgramStore} {finalValue : Value} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    Step ProgramStore.empty lifetime term finalStore (.val finalValue) →
    ∃ env₃,
      WellFormedEnv
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime })
          lifetime ∧
        BorrowSafeEnv
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime }) ∧
        EnvStrengthens
          (env₃.update gamma { ty := .ty ty, lifetime := lifetime })
          (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ∧
        finalStore ≈ₛ env₃ := by
  intro htyping hfresh hstep
  exact corollary_4_14_borrowSafety_emptyInitial_terminal htyping hfresh
    (MultiStep.trans hstep MultiStep.refl)

end FWRust.Paper.Soundness
