import FWRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety

/-!
# Source-level initial-state corollaries

Paper-facing specializations of the Section 4 soundness results to source
initial states (empty store and empty environment).  Typability derives source
syntax and the concrete runtime/static invariants required by the general
kernels, so these declarations expose the paper conclusions without repeating
those proof-side premises.
-/

namespace FWRust
namespace Paper

open Core

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

theorem sourceTerm_validStoreTyping_empty {store : ProgramStore} {term : Term} :
    SourceTerm term →
    ValidStoreTyping store term StoreTyping.empty := by
  intro hsource value hmem
  exact sourceValue_emptyStoreTyping (hsource value hmem)

theorem valueTyping_empty_sourceValue {value : Value} {ty : Ty} :
    ValueTyping StoreTyping.empty value ty →
    SourceValue value := by
  intro htyping
  cases value with
  | unit =>
      trivial
  | int _ =>
      trivial
  | ref ref =>
      cases htyping with
      | ref hlookup =>
          simp [StoreTyping.empty] at hlookup

theorem termTyping_empty_sourceTerm {env₂ : Env} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    SourceTerm term := by
  intro htyping
  refine TermTyping.rec
    (motive_1 := fun _env typing lifetime term _ty _env₂ _ =>
      typing = StoreTyping.empty → SourceTerm term)
    (motive_2 := fun _env typing lifetime terms _ty _env₂ _ =>
      typing = StoreTyping.empty → SourceTerm (.block lifetime terms))
    ?const ?copy ?move ?mutBorrow ?immBorrow ?box ?block
    ?declare ?assign
    ?singleton ?cons htyping rfl
  case const =>
    intro _env _typing _lifetime value _ty hvalueTyping htypingEq
    subst htypingEq
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact valueTyping_empty_sourceValue hvalueTyping
  case copy =>
    intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hcopy _hnotRead
      _htypingEq candidate hmem
    simp [termValues] at hmem
  case move =>
    intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty
      _hLv _hnotWrite _hmove _htypingEq candidate hmem
    simp [termValues] at hmem
  case mutBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty _hLv
      _hmutable _hnotWrite _htypingEq candidate hmem
    simp [termValues] at hmem
  case immBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty _hLv
      _hnotRead _htypingEq candidate hmem
    simp [termValues] at hmem
  case box =>
    intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih htypingEq
      candidate hmem
    exact ih htypingEq candidate (by simpa [termValues] using hmem)
  case block =>
    intro _env₁ _env₂ _env₃ _typing _lifetime blockLifetime _terms _ty
      _hchild _hterms _hwellTy _hdrop ih htypingEq
    exact ih htypingEq
  case declare =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty
      _hterm _hfreshOut _henv₃ ih htypingEq candidate hmem
    exact ih htypingEq candidate (by simpa [termValues] using hmem)
  case assign =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy
      _rhs _rhsTy _hRhs _hLhsPost _hshape _hwellTy _hwrite _hnotWrite ih
      htypingEq candidate hmem
    exact ih htypingEq candidate (by simpa [termValues] using hmem)
  case singleton =>
    intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih htypingEq
      candidate hmem
    simp [termValues] at hmem
    exact ih htypingEq candidate hmem
  case cons =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
      _hterm _hrest ihHead ihRest htypingEq candidate hmem
    simp [termValues] at hmem
    rcases hmem with hhead | htail
    · exact ihHead htypingEq candidate hhead
    · exact ihRest htypingEq candidate (by simpa [termValues] using htail)

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

theorem emptyInitialRuntimeState_valid_of_typing {env₂ : Env}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ValidRuntimeState ProgramStore.empty term := by
  intro htyping
  exact sourceInitialRuntimeState_valid
    (termTyping_empty_sourceTerm htyping)

theorem emptyInitialValidStoreTyping_of_typing {env₂ : Env}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty := by
  intro htyping
  exact sourceTerm_validStoreTyping_empty
    (store := ProgramStore.empty)
    (termTyping_empty_sourceTerm htyping)

/--
Source-level empty-store programs satisfy the initial hypotheses used by the
Section 4 soundness statements.
-/
theorem sourceInitialSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ≈ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    fullSafeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    operationalStoreProgress_empty⟩

/--
Source-level empty-store programs satisfy the mechanised runtime hypotheses,
including the explicit owner-allocation invariant.
-/
theorem sourceInitialRuntimeSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidRuntimeState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ≈ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialRuntimeState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    fullSafeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    operationalStoreProgress_empty⟩

/--
Any program typed from the empty environment and empty store typing satisfies the
runtime assumptions required by progress and preservation.

The remaining proof-side invariants used by the preservation and Theorem 4.12
wrappers are the canonical empty instances: `borrowSafeEnv_empty`,
`Env.finiteSupport_empty`, and `Linearizable.empty`.  Thus the empty initial
state establishes the whole invariant package, and the source-typing
preservation lemmas thread it through well-typed programs.
-/
theorem emptyInitialRuntimeSoundnessHypotheses_of_typing {env₂ : Env}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ValidRuntimeState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
      ProgramStore.empty ≈ₛ Env.empty ∧
      (∀ lifetime, WellFormedEnv Env.empty lifetime) ∧
      OperationalStoreProgress ProgramStore.empty ∧
      (∀ env lifetime, StoreTypingRefsWellFormed env StoreTyping.empty lifetime) := by
  intro htyping
  exact ⟨emptyInitialRuntimeState_valid_of_typing htyping,
    emptyInitialValidStoreTyping_of_typing htyping,
      fullSafeAbstraction_empty,
      wellFormedEnv_empty_all,
      operationalStoreProgress_empty,
      by
        intro env lifetime
        exact storeTypingRefsWellFormed_empty env lifetime⟩

/-- A typed empty-initial program starts with the full invariant package, and
source typing preserves the static package to the output environment. -/
theorem emptyInitialInvariantPackage_of_typing {env₂ : Env}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    SourceTerm term ∧
      ValidRuntimeState ProgramStore.empty term ∧
      ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
      ProgramStore.empty ≈ₛ Env.empty ∧
      ProgramStore.empty.FiniteSupport ∧
      StaticInvariantPackage Env.empty lifetime ∧
      StaticInvariantPackage env₂ lifetime ∧
      WellFormedTy env₂ ty lifetime ∧
      TyBorrowSafeAgainstEnv env₂ ty := by
  intro htyping
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, _hwellFormed, _hprogress,
      _hrefs⟩
  have hsource : SourceTerm term := termTyping_empty_sourceTerm htyping
  have hbase : StaticInvariantPackage Env.empty lifetime :=
    StaticInvariantPackage.empty lifetime
  rcases StaticInvariantPackage.preserve_of_sourceTerm hsource hbase htyping with
    ⟨hresult, hwellTy, htySafe⟩
  exact ⟨hsource, hvalidRuntime, hvalidStoreTyping, hsafe,
    ProgramStore.finiteSupport_empty, hbase, hresult, hwellTy, htySafe⟩

/-- **Lemma 4.10.** Empty-store/source-term instance of Progress. -/
theorem sourceInitial_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  exact progress
    (sourceInitialState_valid hsource)
    (sourceTerm_validStoreTyping_empty hsource)
    (wellFormedEnv_empty _)
    fullSafeAbstraction_empty
    operationalStoreProgress_empty
    htyping

/-- **Lemma 4.10.** Empty-store/source-term Progress via `ValidRuntimeState`. -/
theorem sourceInitial_runtime_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  rcases sourceInitialRuntimeSoundnessHypotheses
      (term := term) (lifetime := lifetime) hsource with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, _hwellFormed, hstoreProgress⟩
  exact progress_runtime
    hvalidRuntime
    hvalidStoreTyping
    (wellFormedEnv_empty _)
    hsafe
    hstoreProgress
    htyping

/-- **Lemma 4.10.** Empty-initial Progress from typing alone. -/
theorem emptyInitial_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro htyping
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, hwellFormed, hstoreProgress,
      _hrefs⟩
  exact typeAndBorrowProgress hvalidRuntime hvalidStoreTyping
    (hwellFormed lifetime) fullSafeAbstraction_empty hstoreProgress htyping

/--
**Lemma 4.11.** Empty-initial Preservation for terminal multisteps, with all
initial runtime assumptions derived from typing.
-/
theorem emptyInitial_preservation {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} {finalStore : ProgramStore} {finalValue : Value} :
      TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
      MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
      FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro htyping hmulti
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, _hwellFormed, _hstoreProgress,
      _hrefs⟩
  have hsource : SourceTerm term := termTyping_empty_sourceTerm htyping
  exact preservation hsource hvalidRuntime hvalidStoreTyping
    (wellFormedEnv_empty lifetime) borrowSafeEnv_empty
    Env.finiteSupport_empty Linearizable.empty fullSafeAbstraction_empty
    htyping hmulti

/-- Empty-initial terminal preservation, bundled with the static invariant
package before and after typing. -/
theorem emptyInitial_preservation_with_invariantPackage
    {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} {finalStore : ProgramStore} {finalValue : Value} :
      TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
      MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
      StaticInvariantPackage Env.empty lifetime ∧
        StaticInvariantPackage env₂ lifetime ∧
        FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro htyping hmulti
  rcases emptyInitialInvariantPackage_of_typing htyping with
    ⟨_hsource, _hvalidRuntime, _hvalidStoreTyping, _hsafe, _hfiniteStore,
      hbase, hresult, _hwellTy, _htySafe⟩
  exact ⟨hbase, hresult, emptyInitial_preservation htyping hmulti⟩

/--
**Lemma 4.11.** Empty-initial paper-facing Preservation wrapper.

Unlike the general runtime preservation wrapper, this has no `SourceTerm`
premise: for empty source store typing, `SourceTerm` follows from typability by
`termTyping_empty_sourceTerm`.
-/
theorem lemma_4_11_preservation_emptyInitial {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} {finalStore : ProgramStore} {finalValue : Value} :
      TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
      MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
      FullTerminalStateSafe finalStore finalValue env₂ ty :=
  emptyInitial_preservation

/--
**Theorem 4.12.** Empty-initial conditional type-and-borrow safety for any term
typed from the empty initial runtime state.
-/
theorem emptyInitial_typeAndBorrowSafety {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    TerminatesAsValue ProgramStore.empty lifetime term →
    ProgressResult ProgramStore.empty lifetime term ∧
        ∃ finalStore finalValue,
          MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) ∧
          FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro htyping hterminates
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, hwellFormed, hstoreProgress,
      _hrefs⟩
  have hsource : SourceTerm term := termTyping_empty_sourceTerm htyping
  rcases hterminates with ⟨finalStore, finalValue, hmulti⟩
  exact ⟨typeAndBorrowProgress hvalidRuntime hvalidStoreTyping
      (hwellFormed lifetime) fullSafeAbstraction_empty hstoreProgress htyping,
    ⟨finalStore, finalValue, hmulti,
      emptyInitial_preservation htyping hmulti⟩⟩

/--
Compatibility wrapper for the earlier conditional Type and Borrow Safety
bridge.  This is not the paper-facing total theorem because it assumes
`TerminatesAsValue`; `emptyInitial_typeAndBorrowSafety_total` below proves the
paper's terminal-existence conclusion from typing alone.

It has no `SourceTerm` premise because `StoreTyping.empty` typability derives
it.
-/
theorem theorem_4_12_typeAndBorrowSafety_emptyInitial {term : Term}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    TerminatesAsValue ProgramStore.empty lifetime term →
    ProgressResult ProgramStore.empty lifetime term ∧
        ∃ finalStore finalValue,
          MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) ∧
          FullTerminalStateSafe finalStore finalValue env₂ ty :=
  emptyInitial_typeAndBorrowSafety

/-- **Lemma 4.10.** Empty-store/source-term non-terminal step corollary. -/
theorem sourceInitial_progress_step {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step ProgramStore.empty lifetime term store' term' := by
  intro hsource htyping hnotTerminal
  exact (sourceInitial_progress hsource htyping).step_of_not_terminal hnotTerminal

/--
**Lemma 4.10.** Empty-store/source-term non-terminal step corollary via
`ValidRuntimeState`.
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
**Lemma 4.11.** Source-initial multistep preservation for a block containing a
source-level value; this is the `R-BlockB` source-level instance.
-/
theorem sourceInitial_blockB_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.block blockLifetime [.val value]) ty env₂ →
    MultiStep ProgramStore.empty lifetime
      (.block blockLifetime [.val value]) finalStore (.val finalValue) →
    FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.block blockLifetime [.val value]) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  rcases preservation_blockB_value_multistep_runtime_no_slots
    (sourceInitialRuntimeState_valid hsourceTerm)
    safeAbstraction_empty
    htyping
    (empty_no_lifetime_slots blockLifetime)
    (sourceValue_validValue_of_empty_valueTyping hsource
      (blockValueTyping_valueTyping htyping))
    hmulti with
    ⟨hvalidFinal, hsafeFinal, hvalueFinal⟩
  have hwellOut := typingPreservesWellFormed_of_sourceTerm hsourceTerm
    (wellFormedEnv_empty lifetime) borrowSafeEnv_empty htyping
  exact ⟨hvalidFinal,
    SafeAbstraction.full_of_containedBorrowsWellFormed hwellOut.1.1
      hsafeFinal,
    hvalueFinal⟩

/--
**Lemma 4.11.** Source-initial multistep preservation for `box v` with a
source-level value; this is the `R-Box` source-level instance.
-/
theorem sourceInitial_box_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) →
    FullTerminalStateSafe finalStore finalValue env₂ (.box ty) := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.box (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  rcases preservation_box_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .box (.val value)) hsourceTerm)
    safeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti with
    ⟨hvalidFinal, hsafeFinal, hvalueFinal⟩
  have hwellOut := typingPreservesWellFormed_of_sourceTerm hsourceTerm
    (wellFormedEnv_empty lifetime) borrowSafeEnv_empty htyping
  exact ⟨hvalidFinal,
    SafeAbstraction.full_of_containedBorrowsWellFormed hwellOut.1.1
      hsafeFinal,
    hvalueFinal⟩

/--
**Lemma 4.11.** Source-initial multistep preservation for `let mut x = v` with a
source-level value; this is the `R-Declare` source-level instance.
-/
theorem sourceInitial_declare_value_multistep_preservation
    {x : Name} {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    MultiStep ProgramStore.empty lifetime
      (.letMut x (.val value)) finalStore (.val finalValue) →
    FullTerminalStateSafe finalStore finalValue env₃ .unit := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.letMut x (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  rcases preservation_declare_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .letMut x (.val value)) hsourceTerm)
    fullSafeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti with
    ⟨hvalidFinal, hsafeFinal, hvalueFinal⟩
  have hwellOut := typingPreservesWellFormed_of_sourceTerm hsourceTerm
    (wellFormedEnv_empty lifetime) borrowSafeEnv_empty htyping
  exact ⟨hvalidFinal,
    SafeAbstraction.full_of_containedBorrowsWellFormed hwellOut.1.1
      hsafeFinal,
    hvalueFinal⟩

/--
**Lemma 4.11.** Source-level terminal preservation base case, where the program
is already a runtime value and the multistep derivation is reflexive.
-/
theorem sourceInitial_multistep_value_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) →
    FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.val value) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  rcases preservation_multistep_runtime_value
    (sourceInitialRuntimeState_valid hsourceTerm)
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .val value) hsourceTerm)
    safeAbstraction_empty
    htyping
    hmulti with
    ⟨hvalidFinal, hsafeFinal, hvalueFinal⟩
  have hwellOut := typingPreservesWellFormed_of_sourceTerm hsourceTerm
    (wellFormedEnv_empty lifetime) borrowSafeEnv_empty htyping
  exact ⟨hvalidFinal,
    SafeAbstraction.full_of_containedBorrowsWellFormed hwellOut.1.1
      hsafeFinal,
    hvalueFinal⟩

/--
Compatibility helper proving only that the source-initial output environment is
well formed.  The paper-facing Lemma 4.9 declaration below additionally installs
the essential fresh result slot.
-/
theorem sourceInitial_borrowInvariance_full {term : Term} {env₂ : Env}
    {lifetime : Lifetime} {ty : Ty} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime := by
  intro hsource htyping
  exact (typingPreservesWellFormed_of_sourceTerm hsource
    (wellFormedEnv_empty lifetime) borrowSafeEnv_empty htyping).1

/-- Static core of the missing-borrow-safety obstruction. -/
theorem lemma_4_9_static_missingBorrowSafety_obstruction :
    ∃ env₁ env₃ typing lifetime term ty,
      WellFormedEnv env₁ lifetime ∧
        SourceTerm term ∧
        TermTyping env₁ typing lifetime term ty env₃ ∧
        ¬ WellFormedEnv env₃ lifetime := by
  rcases EnvWriteStrictCounterexample.strict_assign_rule_result_counterexample with
    ⟨env₁, env₂, env₃, typing, lifetime, lhs, rhs, oldTy,
      targetLifetime, rhsTy, hwell, hsource, hRhs, hLhs, hshape,
      hwellTy, hwrite, hnotWrite, hnotContained⟩
  refine ⟨env₁, env₃, typing, lifetime, .assign lhs rhs, .unit,
    hwell, hsource, ?_, ?_⟩
  · exact TermTyping.assign hRhs hLhs hshape hwellTy hwrite hnotWrite
  · intro hwell₃
    exact hnotContained hwell₃.1

/--
Counterexample to the full printed premises of Lemma 4.9.

Unlike the static projection above, this packages a concrete valid program
store, valid store typing, and strict `FullSafeAbstraction`, as well as the
well-formed source environment and typing derivation.  The output name is
fresh, but adding the result slot still does not yield a well-formed
environment.  The source environment is explicitly not borrow safe.
-/
theorem lemma_4_9_missingBorrowSafety_obstruction :
    ∃ store env₁ env₂ typing lifetime term ty gamma,
      SourceTerm term ∧
        ValidState store term ∧
        ValidStoreTyping store term typing ∧
        store ≈ₛ env₁ ∧
        WellFormedEnv env₁ lifetime ∧
        ¬ BorrowSafeEnv env₁ ∧
        TermTyping env₁ typing lifetime term ty env₂ ∧
        env₂.fresh gamma ∧
        ¬ WellFormedEnv
          (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
          lifetime :=
  EnvWriteStrictCounterexample.lemma_4_9_printedStatement_counterexample

/--
**Lemma 4.9 (Borrow Invariance), corrected paper-shaped form.**

The conclusion is the one printed in the paper: after typing, installing the
result type at an arbitrary fresh name yields an environment well formed at
the ambient lifetime.  The extra `SourceTerm` and `BorrowSafeEnv` premises are
exactly the invariants needed by the mechanised T-Assign proof; finite support
and linearizability are not exposed here because this result does not use
them.  The obstruction immediately above shows that borrow safety cannot be
dropped for the current typing relation.
-/
theorem lemma_4_9_borrowInvariance
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} {gamma : Name} :
    SourceTerm term →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    WellFormedEnv
      (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hsource hwell hborrowSafe htyping hfresh
  rcases typingPreservesWellFormed_of_sourceTerm
      hsource hwell hborrowSafe htyping with
    ⟨hwell₂, _hborrowSafe₂, hwellTy, _htySafe⟩
  exact WellFormedEnv.update_fresh_ty hwell₂ hwellTy hfresh

/--
**Lemma 4.9 (Borrow Invariance), exact empty-initial specialization.**

This has the paper's fresh-result-slot conclusion, rather than only proving
that the output environment is well formed.  All proof-side hypotheses absent
from the printed statement are derived from empty-initial typability:
`SourceTerm term`, well-formedness and borrow safety of `Env.empty`.

The unrestricted printed statement is not valid for the mechanised typing
relation without a borrow-safety premise; see
`strict_assign_rule_result_counterexample` for the T-Assign obstruction.
-/
theorem lemma_4_9_borrowInvariance_emptyInitial
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    WellFormedEnv
      (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro htyping hfresh
  exact lemma_4_9_borrowInvariance
    (termTyping_empty_sourceTerm htyping)
    (wellFormedEnv_empty lifetime) borrowSafeEnv_empty htyping hfresh

/-- Initialized compatibility form; unlike Lemma 4.9, this omits its fresh result slot. -/
theorem sourceInitial_borrowInvariance {term : Term} {env₂ : Env}
    {lifetime : Lifetime} {ty : Ty} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime := by
  intro hsource htyping
  exact WellFormedEnv.whenInitialized
    (sourceInitial_borrowInvariance_full hsource htyping)

/--
**Theorem 4.12.** Source-initial conditional type-and-borrow safety bridge from
an already-proved preservation conclusion.
-/
theorem sourceInitial_typeAndBorrowSafety_of_preservation
    {term : Term} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
      (∀ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
        FullTerminalStateSafe finalStore finalValue env₂ ty) →
      TerminatesAsValue ProgramStore.empty lifetime term →
      ProgressResult ProgramStore.empty lifetime term ∧
        ∃ finalStore finalValue,
          MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) ∧
          FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping hpreservation hterminates
  rcases hterminates with ⟨finalStore, finalValue, hmulti⟩
  exact ⟨typeAndBorrowProgress
      (sourceInitialRuntimeState_valid hsource)
      (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
      (wellFormedEnv_empty lifetime)
      fullSafeAbstraction_empty
      operationalStoreProgress_empty
      htyping,
    ⟨finalStore, finalValue, hmulti,
      hpreservation finalStore finalValue hmulti⟩⟩

/--
**Theorem 4.12.** Source-initial type-and-borrow safety for a source value; the
termination witness is reflexive.
-/
theorem sourceInitial_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.val value) ∧
        ∃ finalStore finalValue,
          MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) ∧
          FullTerminalStateSafe finalStore finalValue env₂ ty := by
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

/--
**Theorem 4.12.** Source-initial type-and-borrow safety for singleton value
blocks, using the `R-BlockB` Lemma 4.11 instance.
-/
theorem sourceInitial_blockB_value_typeAndBorrowSafety
    {value : Value} {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime
      (.block blockLifetime [.val value]) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.block blockLifetime [.val value]) ∧
        ∃ finalStore finalValue,
          MultiStep ProgramStore.empty lifetime
            (.block blockLifetime [.val value]) finalStore (.val finalValue) ∧
          FullTerminalStateSafe finalStore finalValue env₂ ty := by
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
      exact sourceInitial_blockB_value_multistep_preservation
        hsource htyping hmulti)
    ⟨storeAfterDrop, value,
      MultiStep.trans (Step.blockB (lifetime := lifetime) hdrops) MultiStep.refl⟩

/--
**Theorem 4.12.** Source-initial type-and-borrow safety for `box v`, using the
`R-Box` Lemma 4.11 instance.
-/
theorem sourceInitial_box_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    ProgressResult ProgramStore.empty lifetime (.box (.val value)) ∧
        ∃ finalStore finalValue,
          MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) ∧
          FullTerminalStateSafe finalStore finalValue env₂ (.box ty) := by
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

/--
**Theorem 4.12.** Source-initial type-and-borrow safety for `let mut x = v`,
using the `R-Declare` Lemma 4.11 instance.
-/
theorem sourceInitial_declare_value_typeAndBorrowSafety
    {x : Name} {value : Value} {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    ProgressResult ProgramStore.empty lifetime (.letMut x (.val value)) ∧
        ∃ finalStore finalValue,
          MultiStep ProgramStore.empty lifetime (.letMut x (.val value)) finalStore (.val finalValue) ∧
          FullTerminalStateSafe finalStore finalValue env₃ .unit := by
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
      exact sourceInitial_declare_value_multistep_preservation
        hsource htyping hmulti)
    ⟨ProgramStore.empty.declare x lifetime value, .unit,
      MultiStep.trans (Step.declare (lifetime := lifetime) rfl) MultiStep.refl⟩

/--
Compatibility alias for output-environment well-formedness.  It omits the
fresh result slot of paper Lemma 4.9.  The historical name is retained for
callers; the current typing derivation already carries the required assignment
and declaration facts.
-/
theorem sourceInitial_borrowInvariance_of_rankedAssign_and_declFreshCoherence
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
      :
      SourceTerm term →
      TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
      WellFormedEnvWhenInitialized env₂ lifetime := by
  intro hsource htyping
  exact WellFormedEnv.whenInitialized
    (sourceInitial_borrowInvariance_full hsource htyping)

theorem sourceInitial_borrowInvariance_of_rankedAssign_and_declFreshCoherence_full
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
      :
      SourceTerm term →
      TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
      WellFormedEnv env₂ lifetime := by
  intro hsource htyping
  exact sourceInitial_borrowInvariance_full hsource htyping

/-- Compatibility alias omitting paper Lemma 4.9's fresh result slot. -/
theorem sourceInitial_borrowInvariance_of_ruleCarriedObligations
      {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty} :
      SourceTerm term →
      TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
      WellFormedEnvWhenInitialized env₂ lifetime := by
  intro hsource htyping
  exact WellFormedEnv.whenInitialized
    (sourceInitial_borrowInvariance_full hsource htyping)

theorem sourceInitial_borrowInvariance_of_ruleCarriedObligations_full
      {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty} :
      SourceTerm term →
      TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
      WellFormedEnv env₂ lifetime := by
  intro hsource htyping
  exact sourceInitial_borrowInvariance_full hsource htyping

/--
**Theorem 4.12, empty-initial terminal-safety form.**  Any term typed from the
empty initial environment and store typing has a safe terminal state.
-/
theorem emptyInitial_typeAndBorrowSafety_total {term : Term}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime term finalStore
          (.val finalValue) ∧
        FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro htyping
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, hwellFormed, _hstoreProgress,
      _hrefs⟩
  have hsource : SourceTerm term := termTyping_empty_sourceTerm htyping
  rcases terminatesAsValue hsource hvalidRuntime hvalidStoreTyping
      (hwellFormed lifetime) borrowSafeEnv_empty Linearizable.empty
      fullSafeAbstraction_empty ProgramStore.finiteSupport_empty htyping with
    ⟨finalStore, finalValue, hmulti⟩
  exact ⟨finalStore, finalValue, hmulti,
    preservation hsource hvalidRuntime hvalidStoreTyping
      (hwellFormed lifetime) borrowSafeEnv_empty Env.finiteSupport_empty
      Linearizable.empty fullSafeAbstraction_empty htyping hmulti⟩

end Paper
end FWRust
