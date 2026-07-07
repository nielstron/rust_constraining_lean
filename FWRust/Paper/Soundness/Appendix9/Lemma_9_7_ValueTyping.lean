import FWRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Lemma 9.7 (Value Typing)

> Let `Γ₁` be a well-formed typing environment with respect to a lifetime `l`.
> Typing a runtime value is exactly `T-Const`, so it leaves the environment
> unchanged: if `Γ₁ ⊢ ⟨v : T⟩^l_σ ⊣ Γ₂` then `Γ₁ = Γ₂`.

Status: **fully proven** (`valueTyping_environment_eq`).
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

theorem lemma_9_7_valueTyping
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value : Value} {ty : Ty}
    (htyping : TermTyping env₁ typing lifetime (.val value) ty env₂) :
    env₁ = env₂ :=
  valueTyping_environment_eq htyping

end FWRust.Paper.Soundness
