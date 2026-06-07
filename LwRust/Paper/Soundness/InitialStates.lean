import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety

/-!
# Source-level initial-state corollaries

Concrete specializations of the Section 4 soundness results to source initial
states (empty store, source terms).  These are demonstrations, not part of the
paper-lemma critical path.
-/

namespace LwRust
namespace Paper

open Core


theorem sourceValue_no_owningLocations {value : Value} :
    SourceValue value →
    valueOwningLocations value = [] := by
  intro hsource
  cases value with
  | unit =>
      rfl
  | int _ =>
      rfl
  | ref ref =>
      cases hsource

theorem sourceValues_no_owningLocations {values : List Value} :
    (∀ value, value ∈ values → SourceValue value) →
    List.flatMap valueOwningLocations values = [] := by
  intro hsource
  induction values with
  | nil =>
      rfl
  | cons head tail ih =>
      have hhead : SourceValue head := hsource head (by simp)
      have htail : ∀ value, value ∈ tail → SourceValue value := by
        intro value hmem
        exact hsource value (by simp [hmem])
      calc
        List.flatMap valueOwningLocations (head :: tail)
            = valueOwningLocations head ++ List.flatMap valueOwningLocations tail := rfl
        _ = [] ++ [] := by
          rw [sourceValue_no_owningLocations hhead, ih htail]
        _ = [] := rfl

theorem sourceTerm_no_owningLocations {term : Term} :
    SourceTerm term →
    termOwningLocations term = [] := by
  intro hsource
  exact sourceValues_no_owningLocations hsource

theorem sourceTerm_validTerm {term : Term} :
    SourceTerm term →
    ValidTerm term := by
  intro hsource
  simp [ValidTerm, sourceTerm_no_owningLocations hsource]

theorem sourceTerm_ownerTargetsHeap {term : Term} :
    SourceTerm term →
    TermOwnerTargetsHeap term := by
  intro hsource owned hmem
  simp [sourceTerm_no_owningLocations hsource] at hmem

theorem sourceValue_emptyStoreTyping {store : ProgramStore} {value : Value} :
    SourceValue value →
    ∃ ty, ValueTyping StoreTyping.empty value ty ∧ ValidValue store value ty := by
  intro hsource
  cases value with
  | unit =>
      exact ⟨.unit, ValueTyping.unit, ValidPartialValue.unit⟩
  | int value =>
      exact ⟨.int, ValueTyping.int, ValidPartialValue.int⟩
  | ref ref =>
      cases hsource

theorem sourceValue_validValue_of_empty_valueTyping {store : ProgramStore}
    {value : Value} {ty : Ty} :
    SourceValue value →
    ValueTyping StoreTyping.empty value ty →
    ValidValue store value ty := by
  intro hsource htyping
  rcases sourceValue_emptyStoreTyping (store := store) hsource with
    ⟨sourceTy, hsourceTyping, hvalidValue⟩
  have hty : sourceTy = ty :=
    valueTyping_deterministic hsourceTyping htyping
  subst hty
  exact hvalidValue

theorem sourceValue_empty_valueTyping_borrowFree {value : Value} {ty : Ty} :
    SourceValue value →
    ValueTyping StoreTyping.empty value ty →
    TyBorrowFree ty := by
  intro hsource htyping
  cases value with
  | unit =>
      cases htyping
      exact tyBorrowFree_unit
  | int _ =>
      cases htyping
      exact tyBorrowFree_int
  | ref _ =>
      cases hsource

theorem sourceTerm_empty_valueTyping_borrowFree {term : Term}
    {value : Value} {ty : Ty} :
    SourceTerm term →
    value ∈ termValues term →
    ValueTyping StoreTyping.empty value ty →
    TyBorrowFree ty := by
  intro hsource hmem htyping
  exact sourceValue_empty_valueTyping_borrowFree (hsource value hmem) htyping

theorem sourceInitial_value_borrowSafety_result_extension
    {value : Value} {ty : Ty} {env₂ : Env} {lifetime : Lifetime}
    {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource htyping hwellTy hfresh hfreshCoherence
  cases htyping with
  | const hvalueTyping =>
      exact borrowSafety_value_result_extension_borrowFree
        (TermTyping.const hvalueTyping)
        (wellFormedEnv_empty lifetime)
        hwellTy
        borrowSafeEnv_empty
        (sourceValue_empty_valueTyping_borrowFree hsource hvalueTyping)
        hfresh
        hfreshCoherence

theorem sourceInitial_box_value_borrowSafety_result_extension
    {value : Value} {ty : Ty} {env₂ : Env} {lifetime : Lifetime}
    {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma (.box ty) lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty (.box ty), lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro _hsource htyping hfresh hfreshCoherence
  cases htyping with
  | box hinner =>
      cases hinner with
      | const hvalueTyping =>
          have hinnerFree : TyBorrowFree ty :=
            sourceValue_empty_valueTyping_borrowFree _hsource hvalueTyping
          have hwellTy : WellFormedTy Env.empty ty lifetime := by
            cases hvalueTyping with
            | unit =>
                exact WellFormedTy.unit
            | int =>
                exact WellFormedTy.int
            | ref hlookup =>
                simp [StoreTyping.empty] at hlookup
          have hinnerSafe :
              BorrowSafeEnv
                (Env.empty.update gamma { ty := .ty ty, lifetime := lifetime }) :=
            borrowSafeEnv_update_fresh_borrowFree borrowSafeEnv_empty hinnerFree
          exact borrowSafety_result_extension_box_of_inner
            (wellFormedEnv_empty lifetime)
            hwellTy
            hinnerSafe
            hfresh
            hfreshCoherence

theorem sourceInitial_declare_value_borrowSafety_result_extension
    {x : Name} {value : Value} {env₃ : Env} {lifetime : Lifetime}
    {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    env₃.fresh gamma →
    FreshUpdateCoherenceObligations env₃ gamma .unit lifetime →
    WellFormedEnv (env₃.update gamma { ty := .ty .unit, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₃.update gamma { ty := .ty .unit, lifetime := lifetime }) := by
  intro hsource htyping hfreshGamma hfreshGammaCoherence
  cases htyping with
  | declare hfresh hinit _hfreshOut hcoh henv₃ =>
      cases hinit with
      | const hvalueTyping =>
          rename_i initTy
          have hwellTy : WellFormedTy Env.empty initTy lifetime := by
            cases hvalueTyping with
            | unit =>
                exact WellFormedTy.unit
            | int =>
                exact WellFormedTy.int
            | ref hlookup =>
                simp [StoreTyping.empty] at hlookup
          have hdeclared :
              WellFormedEnv
                  (Env.empty.update x { ty := .ty initTy, lifetime := lifetime })
                  lifetime ∧
            BorrowSafeEnv
                  (Env.empty.update x { ty := .ty initTy, lifetime := lifetime }) := by
            exact sourceInitial_value_borrowSafety_result_extension hsource
              (TermTyping.const hvalueTyping) hwellTy hfresh hcoh
          have hfreshGamma' :
              (Env.empty.update x { ty := .ty initTy, lifetime := lifetime }).fresh
                gamma := by
            simpa [henv₃] using hfreshGamma
          rw [henv₃]
          exact borrowSafety_result_extension_borrowFree
            hdeclared.1
            WellFormedTy.unit
            hdeclared.2
            tyBorrowFree_unit
            hfreshGamma'
            (by simpa [henv₃] using hfreshGammaCoherence)

theorem sourceInitial_blockB_value_borrowSafety_result_extension
    {value : Value} {ty : Ty} {env₂ : Env}
    {lifetime blockLifetime : Lifetime} {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime
      (.block blockLifetime [.val value]) ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource htyping hfresh hfreshCoherence
  cases htyping with
  | block _hblockChild hterms hwellTy hdrop =>
      have hvalueTyping := termListTyping_singleton_value_valueTyping hterms
      have henvList : Env.empty = _ :=
        termListTyping_singleton_value_environment_eq hterms
      subst henvList
      have hdropEmpty : env₂ = Env.empty := by
        simpa [Env.dropLifetime, Env.empty] using hdrop
      subst hdropEmpty
      exact borrowSafety_result_extension_borrowFree
        (wellFormedEnv_empty lifetime)
        hwellTy
        borrowSafeEnv_empty
        (sourceValue_empty_valueTyping_borrowFree hsource hvalueTyping)
        hfresh
        hfreshCoherence

theorem sourceTerm_validStoreTyping_empty {store : ProgramStore} {term : Term} :
    SourceTerm term →
    ValidStoreTyping store term StoreTyping.empty := by
  intro hsource value hmem
  exact sourceValue_emptyStoreTyping (hsource value hmem)

theorem sourceInitialState_valid {term : Term} :
    SourceTerm term →
    ValidState ProgramStore.empty term := by
  intro hsource
  exact ⟨validStore_empty, sourceTerm_validTerm hsource, by
    intro owned _hmem
    exact empty_owns_false owned⟩

theorem sourceInitialRuntimeState_valid {term : Term} :
    SourceTerm term →
    ValidRuntimeState ProgramStore.empty term := by
  intro hsource
  exact ⟨sourceInitialState_valid hsource, storeOwnersAllocated_empty,
    storeOwnerTargetsHeap_empty, heapSlotsRootLifetime_empty,
    sourceTerm_ownerTargetsHeap hsource⟩

/--
Source-level empty-store programs satisfy the initial hypotheses used by the
Section 4 soundness statements.
-/
theorem sourceInitialSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ∼ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    BorrowSafeEnv Env.empty ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    safeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    borrowSafeEnv_empty,
    operationalStoreProgress_empty⟩

/--
Source-level empty-store programs satisfy the mechanised runtime hypotheses,
including the explicit owner-allocation invariant.
-/
theorem sourceInitialRuntimeSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidRuntimeState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ∼ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    BorrowSafeEnv Env.empty ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialRuntimeState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    safeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    borrowSafeEnv_empty,
    operationalStoreProgress_empty⟩

/-- Well-typed source-level terms in the empty initial state satisfy Progress. -/
theorem sourceInitial_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  exact progress
    (sourceInitialState_valid hsource)
    (sourceTerm_validStoreTyping_empty hsource)
    wellFormedEnv_empty_all
    safeAbstraction_empty
    operationalStoreProgress_empty
    htyping

/-- Well-typed source-level terms satisfy Progress from the runtime hypothesis package. -/
theorem sourceInitial_runtime_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  rcases sourceInitialRuntimeSoundnessHypotheses
      (term := term) (lifetime := lifetime) hsource with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, _hwellFormed, _hborrowSafe, hstoreProgress⟩
  exact progress_runtime
    hvalidRuntime
    hvalidStoreTyping
    wellFormedEnv_empty_all
    hsafe
    hstoreProgress
    htyping

/-- Well-typed non-terminal source-level terms in the empty initial state can step. -/
theorem sourceInitial_progress_step {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step ProgramStore.empty lifetime term store' term' := by
  intro hsource htyping hnotTerminal
  exact (sourceInitial_progress hsource htyping).step_of_not_terminal hnotTerminal

/--
Well-typed non-terminal source-level terms can step from the runtime hypothesis
package used by the mechanised soundness statements.
-/
theorem sourceInitial_runtime_progress_step {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step ProgramStore.empty lifetime term store' term' := by
  intro hsource htyping hnotTerminal
  exact (sourceInitial_runtime_progress hsource htyping).step_of_not_terminal hnotTerminal

/--
Source-initial multistep preservation for a block containing a source-level
value.  This is the `R-BlockB` source-level instance of Lemma 4.11.
-/
theorem sourceInitial_blockB_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.block blockLifetime [.val value]) ty env₂ →
    MultiStep ProgramStore.empty lifetime
      (.block blockLifetime [.val value]) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.block blockLifetime [.val value]) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_blockB_value_multistep_runtime_no_slots
    (sourceInitialRuntimeState_valid hsourceTerm)
    safeAbstraction_empty
    htyping
    (empty_no_lifetime_slots blockLifetime)
    (sourceValue_validValue_of_empty_valueTyping hsource
      (blockValueTyping_valueTyping htyping))
    hmulti

/--
Source-initial multistep preservation for `box v` with a source-level value.
This is the `R-Box` source-level instance of Lemma 4.11.
-/
theorem sourceInitial_box_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue (.box ty) := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.box (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_box_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .box (.val value)) hsourceTerm)
    safeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti

/--
Source-initial multistep preservation for `let mut x = v` with a source-level
value.  This is the `R-Declare` source-level instance of Lemma 4.11.
-/
theorem sourceInitial_declare_value_multistep_preservation
    {x : Name} {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    MultiStep ProgramStore.empty lifetime
      (.letMut x (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.letMut x (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_declare_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .letMut x (.val value)) hsourceTerm)
    safeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti

/--
Source-level terminal preservation base case.

This is the source-initial instance of Lemma 4.11 when the program is already a
runtime value.  Since values cannot step, the multistep derivation is reflexive.
-/
theorem sourceInitial_multistep_value_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧
      finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.val value) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_multistep_runtime_value
    (sourceInitialRuntimeState_valid hsourceTerm)
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .val value) hsourceTerm)
    safeAbstraction_empty
    htyping
    hmulti

theorem valueTyping_empty_result_wellFormed {env : Env}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValueTyping StoreTyping.empty value ty →
    WellFormedTy env ty lifetime := by
  intro htyping
  exact valueTyping_result_wellFormed_of_refs
    (storeTypingRefsWellFormed_empty env lifetime) htyping

/-- Source-initial borrow invariance through the rule-carried route. -/
theorem sourceInitial_borrowInvariance {term : Term} {env₂ : Env}
    {lifetime : Lifetime} {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hsource htyping hfresh hfreshCoherence
  exact borrowInvariance_emptyStoreTyping
    hobligations
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

theorem sourceInitial_typeAndBorrowSafety_of_preservation
    {term : Term} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    (∀ finalStore finalValue,
      MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₂ ty) →
    TerminatesAsValue ProgramStore.empty lifetime term →
    ProgressResult ProgramStore.empty lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping hpreservation hterminates
  exact typeAndBorrowSafety_of_preservation
    (sourceInitialRuntimeState_valid hsource)
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    wellFormedEnv_empty_all
    safeAbstraction_empty
    operationalStoreProgress_empty
    htyping
    hpreservation
    hterminates

theorem sourceInitial_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.val value) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.val value) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_multistep_value_preservation hsource htyping hmulti)
    ⟨ProgramStore.empty, value, MultiStep.refl⟩

theorem sourceInitial_blockB_value_typeAndBorrowSafety
    {value : Value} {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime
      (.block blockLifetime [.val value]) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.block blockLifetime [.val value]) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime
          (.block blockLifetime [.val value]) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.block blockLifetime [.val value]) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  rcases drops_empty_lifetime blockLifetime with ⟨storeAfterDrop, hdrops⟩
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_blockB_value_multistep_preservation hsource htyping hmulti)
    ⟨storeAfterDrop, value,
      MultiStep.trans (Step.blockB (lifetime := lifetime) hdrops) MultiStep.refl⟩

theorem sourceInitial_box_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    ProgressResult ProgramStore.empty lifetime (.box (.val value)) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ (.box ty) := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.box (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  let boxed := ProgramStore.empty.boxAt 0 value
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_box_value_multistep_preservation hsource htyping hmulti)
    ⟨boxed.1, .ref boxed.2,
      MultiStep.trans
        (Step.box (address := 0) (ref := boxed.2)
          (by simp [ProgramStore.fresh, ProgramStore.empty])
          (by simp [boxed]))
        MultiStep.refl⟩

theorem sourceInitial_declare_value_typeAndBorrowSafety
    {x : Name} {value : Value} {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    ProgressResult ProgramStore.empty lifetime (.letMut x (.val value)) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.letMut x (.val value)) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₃ .unit := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.letMut x (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_declare_value_multistep_preservation hsource htyping hmulti)
    ⟨ProgramStore.empty.declare x lifetime value, .unit,
      MultiStep.trans (Step.declare (lifetime := lifetime) rfl) MultiStep.refl⟩

/--
Source-initial borrow invariance through the explicit ranked/fresh-coherence
route.

This is the source-program version of
`borrowInvariance_of_rankedAssign_and_declFreshCoherence`: it avoids the legacy
bare write-linearization and fresh-type coherence axioms by making the missing
rank/coherence premises explicit.
-/
theorem sourceInitial_borrowInvariance_of_rankedAssign_and_declFreshCoherence
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    AssignmentRhsEdgesRanked →
    AssignmentWriteCoherenceObligations →
    DeclarationFreshUpdateCoherent →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hupdate hranked hwriteCoherent hdeclFresh hsource htyping hfresh
    hfreshCoherence
  exact borrowInvariance_of_rankedAssign_and_declFreshCoherence
    hupdate
    hranked
    hwriteCoherent
    hdeclFresh
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

/-- Source-initial borrow invariance through the rule-carried obligation route. -/
theorem sourceInitial_borrowInvariance_of_ruleCarriedObligations
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hupdate hsource htyping hfresh hfreshCoherence
  exact borrowInvariance_of_ruleCarriedObligations
    hupdate
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

/--
Source-initial Borrow Safety through the explicit, non-axiomatic
borrow-invariance route.

This is the source-program counterpart of
`borrowSafety_of_rankedAssign_and_declFreshCoherence`: the empty initial store,
environment, and store typing discharge the standard source-state premises, while
the rank/coherence obligations remain explicit instead of hidden behind legacy
axioms.
-/
theorem sourceInitial_borrowSafety_of_rankedAssign_and_declFreshCoherence
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    AssignmentRhsEdgesRanked →
    AssignmentWriteCoherenceObligations →
    DeclarationFreshUpdateCoherent →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hrankedAssign hwriteCoherent
    hdeclFresh hsource htyping hfresh hfreshCoherence
  exact borrowSafety_of_rankedAssign_and_declFreshCoherence
    hupdateObligations
    hborrowObligations
    hrankedAssign
    hwriteCoherent
    hdeclFresh
    hsource
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    borrowSafeEnv_empty
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

/-- Source-initial borrow safety through the rule-carried obligation route. -/
theorem sourceInitial_borrowSafety_of_ruleCarriedObligations
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hsource htyping hfresh hfreshCoherence
  exact borrowSafety_of_ruleCarriedObligations
    hupdateObligations
    hborrowObligations
    hsource
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    borrowSafeEnv_empty
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

end Paper
end LwRust
