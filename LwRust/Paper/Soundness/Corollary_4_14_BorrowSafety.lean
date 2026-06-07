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

Status: unconditional as a paper-facing statement, but it depends on explicit
sorried lemmas through `updateBorrowInvariantObligations_from_sorries` and
`borrowSafetyPreservationObligations_from_sorries`.  In the borrow-safety half,
the global mutual term/list induction is source-scoped: `T-Const` only handles
source values, whose types are borrow-free.  Assignment leaves the local
`EnvWrite` frame obligation, now with the root-independent RHS
`TyBorrowSafeAgainstEnv` invariant made explicit.  Move result-extension is
proved constructively from the `LValTyping`/`Strike` origin lemma.  Blocks are
handled by the global term/list induction, which carries that same
root-independent result-type invariant through `dropLifetime`.  The final result
binding also carries `FreshUpdateCoherenceObligations`, because the bare paper
phrase `γ ∈ fresh` is too weak for the strengthened `Coherent` invariant.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Corollary 4.14, Borrow Safety (core/strengthened form `Γ₂ = Γ₃`). -/
theorem corollary_4_14_borrowSafety
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {gamma : Name}
    (hrefs : ∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime)
    (hvalidState : ValidState store term)
    (hvalidStoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (hsource : SourceTerm term)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hfresh : env₂.fresh gamma)
    (hfreshCoherence : FreshUpdateCoherenceObligations env₂ gamma ty lifetime) :
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
        lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) :=
  borrowSafety_of_ruleCarriedObligations
    updateBorrowInvariantObligations_from_sorries
    borrowSafetyPreservationObligations_from_sorries
    hsource hrefs hvalidState hvalidStoreTyping hwellFormed hborrowSafe hsafe htyping
    hfresh hfreshCoherence

end LwRust.Paper.Soundness
