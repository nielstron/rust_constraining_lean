import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
# Corollary 4.14 (Well-Formed Output)

The paper's original borrow-safety corollary is too strong for this mechanized
control-flow calculus: conditional and loop joins can produce well-formed output
environments whose borrow target lists are not globally borrow-safe.  The
surviving global result is output well-formedness, supplied by Lemma 4.9.

This file also keeps small borrow-free helper lemmas used by examples and
source-initial wrappers.
-/

namespace LwRust
namespace Paper

open Core

theorem partialTyBorrowFree_ty {ty : Ty} :
    TyBorrowFree ty →
    PartialTyBorrowFree (.ty ty) := by
  intro hfree mutable targets hcontains
  exact hfree mutable targets hcontains

@[simp] theorem partialTyBorrowFree_undef (ty : Ty) :
    PartialTyBorrowFree (.undef ty) := by
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem partialTyBorrowFree_box {ty : PartialTy} :
    PartialTyBorrowFree ty →
    PartialTyBorrowFree (.box ty) := by
  intro hfree mutable targets hcontains
  cases hcontains with
  | box hinner =>
      exact hfree mutable targets hinner

@[simp] theorem tyBorrowFree_unit :
    TyBorrowFree .unit := by
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_int :
    TyBorrowFree .int := by
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_bool :
    TyBorrowFree .bool := by
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_box {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowFree (.box ty) := by
  intro hfree mutable targets hcontains
  cases hcontains with
  | tyBox hinner =>
      exact hfree mutable targets hinner

theorem tyBorrowSafeAgainstEnv_borrowFree {env : Env} {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowSafeAgainstEnv env ty := by
  intro hfree
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      _hborrow _htargetMutable _htargetOther _hconflict
    exact False.elim (hfree true _ hcontains)
  · intro x targetsMutable mutable targetsOther targetMutable targetOther _hborrow
      hcontains _htargetMutable _htargetOther _hconflict
    exact False.elim (hfree mutable _ hcontains)

theorem TyBorrowSafeAgainstEnv.dropLifetime {env : Env} {ty : Ty}
    {lifetime : Lifetime} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv (env.dropLifetime lifetime) ty := by
  intro hsafe
  rcases hsafe with ⟨hsafeLeft, hsafeRight⟩
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther
      hcontainsResult hcontainsOther htargetResult htargetOther hconflict
    rcases hcontainsOther with ⟨slot, hslot, hcontainsTy⟩
    rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨holdSlot, _hnotDropped⟩
    exact hsafeLeft targetsMutable mutable targetsOther x targetMutable targetOther
      hcontainsResult ⟨slot, holdSlot, hcontainsTy⟩
      htargetResult htargetOther hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsOther hcontainsResult htargetResult htargetOther hconflict
    rcases hcontainsOther with ⟨slot, hslot, hcontainsTy⟩
    rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨holdSlot, _hnotDropped⟩
    exact hsafeRight x targetsMutable mutable targetsOther targetMutable targetOther
      ⟨slot, holdSlot, hcontainsTy⟩ hcontainsResult
      htargetResult htargetOther hconflict

theorem TyBorrowSafeAgainstEnv.box {env : Env} {ty : Ty} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv env (.box ty) := by
  intro hsafe
  rcases hsafe with ⟨hsafeLeft, hsafeRight⟩
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther
      hcontainsResult hcontainsOther htargetResult htargetOther hconflict
    cases hcontainsResult with
    | tyBox hinner =>
        exact hsafeLeft targetsMutable mutable targetsOther x targetMutable targetOther
          hinner hcontainsOther htargetResult htargetOther hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsOther hcontainsResult htargetResult htargetOther hconflict
    cases hcontainsResult with
    | tyBox hinner =>
        exact hsafeRight x targetsMutable mutable targetsOther targetMutable targetOther
          hcontainsOther hinner htargetResult htargetOther hconflict

theorem corollary_4_14_wellFormedOutput
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact borrowInvariance_of_ruleCarriedObligations
    hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Corollary 4.14, weakened form: the static output remains well-formed. -/
theorem corollary_4_14_borrowSafety
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hvalidState : ValidState store term)
    (_hvalidStoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (hsource : SourceTerm term)
    (htyping : TermTyping env₁ typing lifetime term ty env₂) :
    WellFormedEnv env₂ lifetime :=
  borrowInvariance_of_sourceTerm hsource hvalidState hwellFormed hsafe htyping

end LwRust.Paper.Soundness
