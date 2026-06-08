import LwRust.Paper.Soundness.Lemma_4_11_Preservation

/-!
# Theorem 4.12 (Type and Borrow Safety)

Paper statement (Section 4.5):

> Let `S₁ ▷ t` be a valid state; let `σ` be a store typing where `S₁ ▷ t ⊢ σ`;
> let `Γ₁` be a well-formed typing environment with respect to a lifetime `l`
> where `S₁ ∼ Γ₁`; let `Γ₂` be a typing environment; and let `T` be a type.  If
> `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂`, then `⟨S₁ ▷ t ⟶* S₂ ▷ v⟩^l` for some terminal
> state `S₂ ▷ v`.

The paper's statement assumes termination; here that is the explicit
`TerminatesAsValue` witness.  Follows from Lemma 4.10 (Progress) and Lemma 4.11
(Preservation).  The mechanized paper-facing wrapper uses the strengthened
singleton/drop-safe block typing rule, so the final statement carries no
external runtime-preservation premise.
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
Theorem 4.12 bridge, Type and Borrow Safety.

The paper's core calculus is terminating, while this mechanisation keeps the
operational semantics relational.  Therefore the theorem is stated with an
explicit termination witness and the Lemma 4.11 preservation conclusion as a
premise.  Progress rules out an initially stuck well-typed state; preservation
turns the terminal multistep into the safe terminal state promised by the paper.
-/
theorem typeAndBorrowSafety_of_preservation
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
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
  exact ⟨progress_runtime hvalidRuntime hvalidStoreTyping hwellFormed hsafe
      hstoreProgress htyping,
    ⟨finalStore, finalValue, hmulti, hpreservation finalStore finalValue hmulti⟩⟩

/--
Theorem 4.12, Type and Borrow Safety.

The paper assumes termination; here that assumption is represented by an
explicit multistep witness to a final runtime value.
-/
theorem typeAndBorrowSafety {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    TerminatesAsValue store lifetime term →
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hrefs hvalidRuntime hvalidStoreTyping hwellFormed hsafe
    hstoreProgress htyping hterminates
  exact typeAndBorrowSafety_of_preservation hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hstoreProgress htyping
    (by
      intro finalStore finalValue hmulti
      exact preservation hrefs hvalidRuntime hvalidStoreTyping
        (hwellFormed lifetime) hsafe htyping hmulti)
    hterminates

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Theorem 4.12, Type and Borrow Safety. -/
theorem theorem_4_12_typeAndBorrowSafety
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hrefs : ∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : ∀ lifetime, WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (hstore : OperationalStoreProgress store)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hterminates : TerminatesAsValue store lifetime term) :
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty :=
  typeAndBorrowSafety hrefs hvalid
    hstoreTyping hwellFormed hsafe hstore htyping hterminates

end LwRust.Paper.Soundness
