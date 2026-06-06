import LwRust.Paper.Soundness

/-!
# Lemma 4.11 (Preservation)

Paper statement (Section 4.4):

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; let `σ` be a
> store typing where `S₁ ▷ t ⊢ σ`; let `Γ₁` be a well-formed typing environment
> with respect to a lifetime `l` where `S₁ ∼ Γ₁`; let `Γ₂` be a typing
> environment; and let `T` be a type.  If `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂` and
> `⟨S₁ ▷ t ⟶* S₂ ▷ v⟩^l`, then `S₂ ▷ v` remains valid where `S₂ ∼ Γ₂` and
> `S₂ ▷ v ∼ T`.

Status: **conditional** on `RuntimePreservationObligations` (the move/assign/block
runtime cases — Appendix Lemmas 9.5 Drop Preservation, 9.6 Update Preservation,
9.8 Alias Preservation, 9.9 Value Preservation, 9.10 Store Preservation).  No
concrete instance is discharged yet; the structural cases (value/copy/borrow/box/
declare) are already proven inside `preservation`.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Lemma 4.11, Preservation (conditional on the runtime move/assign/block
preservation obligations). -/
theorem lemma_4_11_preservation
    (hobligations : RuntimePreservationObligations)
    {store finalStore : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {finalValue : Value}
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    TerminalStateSafe finalStore finalValue env₂ ty :=
  preservation hobligations hvalid hstoreTyping hwellFormed hsafe htyping hmulti

end LwRust.Paper.Soundness
