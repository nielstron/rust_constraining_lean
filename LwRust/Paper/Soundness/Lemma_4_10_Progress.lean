import LwRust.Paper.Soundness

/-!
# Lemma 4.10 (Progress)

Paper statement (Section 4.4):

> Let `S₁ ▷ t₁` be a valid state; let `σ` be a store typing where `S₁ ▷ t₁ ⊢ σ`;
> let `Γ₁` be a well-formed typing environment with respect to a lifetime `l`
> where `S₁ ∼ Γ₁`; let `Γ₂` be a typing environment; and let `T` be a type.
> If `Γ₁ ⊢ ⟨t₁ : T⟩^l_σ ⊣ Γ₂`, then either `t₁ ∈ Value` or
> `⟨S₁ ▷ t₁ ⟶ S₂ ▷ t₂⟩^l` for some state `S₂ ▷ t₂`.

Status: **fully proven** (closed proof, no obligations).  `OperationalStoreProgress`
is the explicit drop/allocation availability premise the abstract store model
needs (it holds for all concrete stores, see `ConcreteProgramStore`).
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Lemma 4.10, Progress. -/
theorem lemma_4_10_progress
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hvalid : ValidState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : ∀ lifetime, WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (hstore : OperationalStoreProgress store)
    (htyping : TermTyping env₁ typing lifetime term ty env₂) :
    ProgressResult store lifetime term :=
  progress hvalid hstoreTyping hwellFormed hsafe hstore htyping

end LwRust.Paper.Soundness
