import LwRust.Paper.Soundness

/-!
# Corollary 4.14 (Borrow Safety)

Paper statement (Section 4.5.1):

> Let `S₁ ▷ t₁` and `S₂ ▷ t₂` be valid states; … let `Γ₁` be a well-formed
> *borrow safe* typing environment with respect to a lifetime `l` where
> `S₁ ∼ Γ₁`; … If `Γ₁ ⊢ ⟨t₁ : T₁⟩^l_σ ⊣ Γ₂` where `⟨S₁ ▷ t₁ ⟶* S₂ ▷ t₂⟩^l`,
> then, for arbitrary `γ ∈ fresh`, a well-formed and borrow safe typing
> environment `Γ₃[γ ↦ T₂^l] ⊑ Γ₂[γ ↦ T₁^l]` exists where `S₂ ∼ Γ₃`.

For the calculus core this strengthens to `Γ₂ = Γ₃`, which is the mechanized
form below: typing from a well-formed borrow-safe environment yields a
well-formed *and* borrow-safe result environment.

Status: the `UpdateBorrowInvariantObligations` half (Borrow Invariance, 4.9) is
supplied via `updateBorrowInvariantObligations_appendix96`; the borrow-safety
half is **conditional** on `BorrowSafetyPreservationObligations`
(the value/move/assign/block borrow-safety cases), not yet discharged.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Corollary 4.14, Borrow Safety (core/strengthened form `Γ₂ = Γ₃`),
conditional on `BorrowSafetyPreservationObligations`. -/
theorem corollary_4_14_borrowSafety
    (hborrowObligations : BorrowSafetyPreservationObligations)
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {gamma : Name}
    (hrefs : ∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime)
    (hvalidState : ValidState store term)
    (hvalidStoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hfresh : env₂.fresh gamma) :
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
        lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) :=
  borrowSafety updateBorrowInvariantObligations_appendix96 hborrowObligations
    hrefs hvalidState hvalidStoreTyping hwellFormed hborrowSafe hsafe htyping hfresh

end LwRust.Paper.Soundness
