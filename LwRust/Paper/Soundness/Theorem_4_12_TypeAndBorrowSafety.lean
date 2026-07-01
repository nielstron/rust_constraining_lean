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
  exact progress_typing hvalidStoreTyping hslotsOutlive hsafe.whenInitialized
    hstoreProgress htyping

/--
Progress for the stale-aware initialized invariant.

This is the form to use once a current-state preservation invariant supplies
typing together with `SafeAbstractionWhenInitialized`: full borrow-target
resolution is required only when the current typing rule actually dereferences
through those targets.
-/
theorem typeAndBorrowProgress_whenInitialized {store : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    EnvSlotsOutlive env₁ lifetime →
    SafeAbstractionWhenInitialized store env₁ →
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
    SafeAbstractionWhenInitialized store env₁ →
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
    SafeAbstractionWhenInitialized store env₁ →
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
    SafeAbstractionWhenInitialized store env₁ →
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
        TerminalStateSafeWhenInitialized finalStore finalValue env₂ ty) →
      TerminatesAsValue store lifetime term →
      ProgressResult store lifetime term ∧
        ∃ finalStore finalValue,
          MultiStep store lifetime term finalStore (.val finalValue) ∧
          TerminalStateSafeWhenInitialized finalStore finalValue env₂ ty := by
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
          TerminalStateSafeWhenInitialized finalStore finalValue env₂ ty := by
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

/-- Theorem 4.12 progress component over the initialized invariant. -/
theorem theorem_4_12_typeAndBorrowProgress_whenInitialized
    {store : ProgramStore} {env₁ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
      (hvalid : ValidRuntimeState store term)
      (hstoreTyping : ValidStoreTyping store term typing)
      (hslotsOutlive : EnvSlotsOutlive env₁ lifetime)
      (hsafe : SafeAbstractionWhenInitialized store env₁)
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
      (hsafe : SafeAbstractionWhenInitialized store env₁)
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
      (hsafe : SafeAbstractionWhenInitialized store env₁)
      (hstore : OperationalStoreProgress store)
      (htyping : TermTyping env₁ typing lifetime term ty env₂)
      (hnotTerminal : ¬ Terminal term) :
    ∃ store' term', Step store lifetime term store' term' :=
  typeAndBorrowStep_of_preservationInvariant hvalid hstoreTyping hwellFormed
    hsafe hstore htyping hnotTerminal

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
          TerminalStateSafeWhenInitialized finalStore finalValue env₂ ty :=
      typeAndBorrowSafety hsource hvalid
        hstoreTyping hwellFormed hsafe hstore htyping hterminates

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
          TerminalStateSafeWhenInitialized finalStore finalValue env₂ ty :=
    typeAndBorrowSafety hsource hvalid hstoreTyping hwellFormed
      hsafe (OperationalStoreProgress.of_finiteSupport hfinite) htyping hterminates

end LwRust.Paper.Soundness
