import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
# Borrow-Safety Helpers

Phase D1 keeps borrow safety as a single-target invariant.  The old
target-list selection, join, and fan-out helper layer has been removed; this
file now contains only the small structural facts still useful to downstream
preservation statements.
-/

namespace LwRust
namespace Paper

open Core

theorem partialTyContains_borrow_iff_eq {mutable : Bool} {target : LVal}
    {needle : Ty} :
    PartialTyContains (.ty (.borrow mutable target)) needle ↔
      Ty.borrow mutable target = needle := by
  constructor
  · intro hcontains
    cases hcontains with
    | here => rfl
  · intro hty
    subst hty
    exact PartialTyContains.here

theorem partialTyBorrowFree_ty {ty : Ty} :
    TyBorrowFree ty →
    PartialTyBorrowFree (.ty ty) := by
  intro hfree mutable target hcontains
  exact hfree mutable target hcontains

@[simp] theorem partialTyBorrowFree_undef (ty : Ty) :
    PartialTyBorrowFree (.undef ty) := by
  intro mutable target hcontains
  cases hcontains

@[simp] theorem partialTyBorrowFree_box {ty : PartialTy} :
    PartialTyBorrowFree ty →
    PartialTyBorrowFree (.box ty) := by
  intro hfree mutable target hcontains
  cases hcontains with
  | box hinner => exact hfree mutable target hinner

@[simp] theorem tyBorrowFree_unit :
    TyBorrowFree .unit := by
  intro mutable target hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_int :
    TyBorrowFree .int := by
  intro mutable target hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_box {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowFree (.box ty) := by
  intro hfree mutable target hcontains
  cases hcontains with
  | tyBox hinner => exact hfree mutable target hinner

@[simp] theorem borrowSafeEnv_empty :
    BorrowSafeEnv Env.empty := by
  intro x y mutable targetMutable targetOther hcontainsMutable _hcontainsOther
    _hconflict
  rcases hcontainsMutable with ⟨slot, hslot, _⟩
  change none = some slot at hslot
  cases hslot

theorem EnvContains.update_fresh_ne {env : Env} {x y : Name} {slot : EnvSlot}
    {ty : Ty} :
    y ≠ x →
    (env.update x slot) ⊢ y ↝ ty →
    env ⊢ y ↝ ty := by
  intro hy hcontains
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  exact ⟨containedSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩

theorem EnvContains.dropLifetime_of_contains {env : Env} {lifetime : Lifetime}
    {x : Name} {ty : Ty} :
    env.dropLifetime lifetime ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  unfold Env.dropLifetime at hslot
  cases henv : env.slotAt x with
  | none =>
      simp [henv] at hslot
  | some envSlot =>
      by_cases hlife : envSlot.lifetime = lifetime
      · simp [henv, hlife] at hslot
      · have hslotEq : envSlot = slot := by
          simpa [henv, hlife] using hslot
        exact ⟨envSlot, henv, by simpa [hslotEq] using hcontainsTy⟩

theorem pathConflicts_symm {left right : LVal} :
    left ⋈ right →
    right ⋈ left := by
  intro h
  exact h.symm

theorem partialTyContains_borrow_injective {partialTy : PartialTy}
    {mutable₁ mutable₂ : Bool} {target₁ target₂ : LVal} :
    PartialTyContains partialTy (.borrow mutable₁ target₁) →
    PartialTyContains partialTy (.borrow mutable₂ target₂) →
    mutable₁ = mutable₂ ∧ target₁ = target₂ := by
  have hgeneral :
      ∀ {partialTy needle₁},
        PartialTyContains partialTy needle₁ →
        ∀ {mutable₁ mutable₂ : Bool} {target₁ target₂ : LVal},
          needle₁ = .borrow mutable₁ target₁ →
          PartialTyContains partialTy (.borrow mutable₂ target₂) →
          mutable₁ = mutable₂ ∧ target₁ = target₂ := by
    intro partialTy needle₁ hleft
    induction hleft with
    | here =>
        intro mutable₁ mutable₂ target₁ target₂ hneedle hright
        subst hneedle
        cases hright with
        | here => exact ⟨rfl, rfl⟩
    | tyBox _hinner ih =>
        intro mutable₁ mutable₂ target₁ target₂ hneedle hright
        cases hright with
        | tyBox hrightInner => exact ih hneedle hrightInner
    | box _hinner ih =>
        intro mutable₁ mutable₂ target₁ target₂ hneedle hright
        cases hright with
        | box hrightInner => exact ih hneedle hrightInner
  intro hleft hright
  exact hgeneral hleft rfl hright

theorem partialTyContains_mut_imm_false {partialTy : PartialTy}
    {mutableTarget immTarget : LVal} :
    PartialTyContains partialTy (.borrow true mutableTarget) →
    PartialTyContains partialTy (.borrow false immTarget) →
    False := by
  intro hmut himm
  rcases partialTyContains_borrow_injective hmut himm with ⟨hbool, _⟩
  cases hbool

theorem borrowSafeEnv_update_partialBorrowFree {env : Env} {x : Name}
    {slot : EnvSlot} :
    BorrowSafeEnv env →
    PartialTyBorrowFree slot.ty →
    BorrowSafeEnv (env.update x slot) := by
  intro hsafe hborrowFree y z mutable targetMutable targetOther
    hcontainsMutable hcontainsOther hconflict
  by_cases hy : y = x
  · subst hy
    rcases hcontainsMutable with ⟨containedSlot, hslot, hcontainsTy⟩
    have hslotEq : containedSlot = slot := by
      have h : slot = containedSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    exact False.elim (hborrowFree true targetMutable hcontainsTy)
  · by_cases hz : z = x
    · subst hz
      rcases hcontainsOther with ⟨containedSlot, hslot, hcontainsTy⟩
      have hslotEq : containedSlot = slot := by
        have h : slot = containedSlot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      exact False.elim (hborrowFree mutable targetOther hcontainsTy)
    · exact hsafe y z mutable targetMutable targetOther
        (EnvContains.update_fresh_ne hy hcontainsMutable)
        (EnvContains.update_fresh_ne hz hcontainsOther)
        hconflict

theorem borrowSafeEnv_update_fresh_borrowFree {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    TyBorrowFree ty →
    BorrowSafeEnv (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hborrowFree
  exact borrowSafeEnv_update_partialBorrowFree hsafe
    (partialTyBorrowFree_ty hborrowFree)

theorem partialTyLoanFree_ty {ty : Ty} (hfree : TyLoanFree ty) :
    PartialTyLoanFree (.ty ty) :=
  hfree

theorem borrowSafeEnv_update_partialLoanFree {env : Env} {x : Name}
    {slot : EnvSlot} :
    BorrowSafeEnv env →
    PartialTyLoanFree slot.ty →
    BorrowSafeEnv (env.update x slot) := by
  exact borrowSafeEnv_update_partialBorrowFree

theorem borrowSafeEnv_update_fresh_loanFree {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    TyLoanFree ty →
    BorrowSafeEnv (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hloanFree
  exact borrowSafeEnv_update_partialLoanFree hsafe
    (partialTyLoanFree_ty hloanFree)

theorem tyBorrowSafeAgainstEnv_loanFree {env : Env} {ty : Ty} :
    TyLoanFree ty →
    TyBorrowSafeAgainstEnv env ty := by
  intro hfree
  constructor
  · intro targetMutable mutable targetOther x hcontains _hother hconflict
    exact hfree true targetMutable hcontains
  · intro x targetMutable mutable targetOther _hcontainsMutable hcontains
      _hconflict
    exact hfree mutable targetOther hcontains

theorem tyBorrowSafeAgainstEnv_borrowFree {env : Env} {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowSafeAgainstEnv env ty := by
  exact tyBorrowSafeAgainstEnv_loanFree

theorem TyBorrowSafeAgainstEnv.dropLifetime {env : Env} {ty : Ty}
    {lifetime : Lifetime} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv (env.dropLifetime lifetime) ty := by
  intro hsafeTy
  constructor
  · intro targetMutable mutable targetOther x hcontains hother hconflict
    exact hsafeTy.1 targetMutable mutable targetOther x hcontains
      (EnvContains.dropLifetime_of_contains hother) hconflict
  · intro x targetMutable mutable targetOther hcontainsMutable hcontains hconflict
    exact hsafeTy.2 x targetMutable mutable targetOther
      (EnvContains.dropLifetime_of_contains hcontainsMutable) hcontains
      hconflict

theorem borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env ty →
    BorrowSafeEnv (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hsafeTy a b mutable targetMutable targetOther
    hcontainsMutable hcontainsOther hconflict
  by_cases ha : a = x
  ·
    rcases hcontainsMutable with ⟨containedSlot, hslot, hcontainsTy⟩
    have hslotEq :
        containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h : { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
        simpa [Env.update, ha] using hslot
      exact h.symm
    subst hslotEq
    by_cases hb : b = x
    · exact ha.trans hb.symm
    · exact False.elim
        (hsafeTy.1 targetMutable mutable targetOther b hcontainsTy
          (EnvContains.update_fresh_ne hb hcontainsOther) hconflict)
  · by_cases hb : b = x
    ·
      rcases hcontainsOther with ⟨containedSlot, hslot, hcontainsTy⟩
      have hslotEq :
          containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h : { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
          simpa [Env.update, hb] using hslot
        exact h.symm
      subst hslotEq
      exact False.elim
        (hsafeTy.2 a targetMutable mutable targetOther
          (EnvContains.update_fresh_ne ha hcontainsMutable)
          hcontainsTy hconflict)
    · exact hsafe a b mutable targetMutable targetOther
        (EnvContains.update_fresh_ne ha hcontainsMutable)
        (EnvContains.update_fresh_ne hb hcontainsOther)
        hconflict

theorem borrowSafeEnv_dropLifetime {env : Env} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    BorrowSafeEnv (env.dropLifetime lifetime) := by
  intro hsafe x y mutable targetMutable targetOther
    hcontainsMutable hcontainsOther hconflict
  exact hsafe x y mutable targetMutable targetOther
    (EnvContains.dropLifetime_of_contains hcontainsMutable)
    (EnvContains.dropLifetime_of_contains hcontainsOther)
    hconflict

theorem borrowSafety_block_drop {env env' : Env} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env' = env.dropLifetime lifetime →
    BorrowSafeEnv env' := by
  intro hsafe henv'
  rw [henv']
  exact borrowSafeEnv_dropLifetime hsafe

theorem tyBorrowSafeAgainstEnv_mutBorrow {env : Env} {lv : LVal} :
    ¬ WriteProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow true lv) := by
  intro hnotWrite
  constructor
  · intro targetMutable mutable targetOther x hcontains hother hconflict
    have hEq := partialTyContains_borrow_iff_eq.mp hcontains
    cases hEq
    cases mutable
    · exact hnotWrite (Or.inr ⟨x, targetOther, hother, hconflict.symm⟩)
    · exact hnotWrite (Or.inl ⟨x, targetOther, hother, hconflict.symm⟩)
  · intro x targetMutable mutable targetOther hcontainsMutable hcontains hconflict
    have hEq := partialTyContains_borrow_iff_eq.mp hcontains
    cases hEq
    exact hnotWrite (Or.inl ⟨x, targetMutable, hcontainsMutable, hconflict⟩)

theorem tyBorrowSafeAgainstEnv_immBorrow {env : Env} {lv : LVal} :
    ¬ ReadProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow false lv) := by
  intro hnotRead
  constructor
  · intro targetMutable mutable targetOther x hcontains _hother _hconflict
    have hEq := partialTyContains_borrow_iff_eq.mp hcontains
    cases hEq
  · intro x targetMutable mutable targetOther hcontainsMutable hcontains hconflict
    have hEq := partialTyContains_borrow_iff_eq.mp hcontains
    cases hEq
    exact hnotRead ⟨x, targetMutable, hcontainsMutable, hconflict⟩

theorem TyBorrowSafeAgainstEnv.box {env : Env} {ty : Ty} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv env (.box ty) := by
  intro hsafeTy
  constructor
  · intro targetMutable mutable targetOther x hcontains hother hconflict
    cases hcontains with
    | tyBox hinner =>
        exact hsafeTy.1 targetMutable mutable targetOther x hinner hother
          hconflict
  · intro x targetMutable mutable targetOther hcontainsMutable hcontains hconflict
    cases hcontains with
    | tyBox hinner =>
        exact hsafeTy.2 x targetMutable mutable targetOther hcontainsMutable
          hinner hconflict

end Paper
end LwRust
