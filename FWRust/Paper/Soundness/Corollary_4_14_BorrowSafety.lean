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

/-- Corollary 4.14 in the strengthened form stated for the calculus core in the
paper's Appendix: an arbitrary fresh result slot can be added while preserving
well-formedness and borrow safety. -/
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

/-- Empty-initial paper-facing Corollary 4.14.  The source-term premise and
initial invariants are derived from empty-store typability. -/
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

end FWRust.Paper.Soundness
