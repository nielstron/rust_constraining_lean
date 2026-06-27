import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
# Borrow-Safety Helpers

Internal borrow-safety preservation facts used by preservation and reachable
progress.  This file intentionally does not state a paper-facing borrow-safety
corollary; it only keeps the helper induction and local frame lemmas that are
still needed by the current Section 4 proofs.
-/

namespace LwRust
namespace Paper

open Core

/-! ## Borrow-safety predicates and frame facts -/

theorem partialTyContains_borrow_iff_eq {mutable : Bool} {targets : List LVal}
    {pointee needle : Ty} :
    PartialTyContains (.ty (.borrow mutable targets pointee)) needle ↔
      Ty.borrow mutable targets pointee = needle := by
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
  intro hfree mutable targets pointee hcontains
  exact hfree mutable targets pointee hcontains

@[simp] theorem partialTyBorrowFree_undef (ty : Ty) :
    PartialTyBorrowFree (.undef ty) := by
  intro mutable targets pointee hcontains
  cases hcontains

@[simp] theorem partialTyBorrowFree_box {ty : PartialTy} :
    PartialTyBorrowFree ty →
    PartialTyBorrowFree (.box ty) := by
  intro hfree mutable targets pointee hcontains
  cases hcontains with
  | box hinner =>
      exact hfree mutable targets pointee hinner

@[simp] theorem tyBorrowFree_unit :
    TyBorrowFree .unit := by
  intro mutable targets pointee hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_int :
    TyBorrowFree .int := by
  intro mutable targets pointee hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_bool :
    TyBorrowFree .bool := by
  intro mutable targets pointee hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_box {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowFree (.box ty) := by
  intro hfree mutable targets pointee hcontains
  cases hcontains with
  | tyBox hinner =>
      exact hfree mutable targets pointee hinner

@[simp] theorem borrowSafeEnv_empty :
    BorrowSafeEnv Env.empty := by
  intro x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
    targetMutable targetOther hcontains _ _ _ _
  rcases hcontains with ⟨slot, hslot, _hcontainsTy⟩
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

theorem pathConflicts_symm {left right : LVal} :
    left ⋈ right →
    right ⋈ left := by
  intro h
  exact h.symm

theorem partialTyContains_borrow_injective {partialTy : PartialTy}
    {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal}
    {pointee₁ pointee₂ : Ty} :
    PartialTyContains partialTy (.borrow mutable₁ targets₁ pointee₁) →
    PartialTyContains partialTy (.borrow mutable₂ targets₂ pointee₂) →
    mutable₁ = mutable₂ ∧ targets₁ = targets₂ ∧ pointee₁ = pointee₂ := by
  have hgeneral :
      ∀ {partialTy needle₁},
        PartialTyContains partialTy needle₁ →
        ∀ {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal}
          {pointee₁ pointee₂ : Ty},
          needle₁ = .borrow mutable₁ targets₁ pointee₁ →
          PartialTyContains partialTy (.borrow mutable₂ targets₂ pointee₂) →
          mutable₁ = mutable₂ ∧ targets₁ = targets₂ ∧ pointee₁ = pointee₂ := by
    intro partialTy needle₁ hleft
    induction hleft with
    | here =>
        intro mutable₁ mutable₂ targets₁ targets₂ pointee₁ pointee₂ hneedle hright
        subst hneedle
        cases hright with
        | here => exact ⟨rfl, rfl, rfl⟩
    | tyBox _hinner ih =>
        intro mutable₁ mutable₂ targets₁ targets₂ pointee₁ pointee₂ hneedle hright
        cases hright with
        | tyBox hrightInner => exact ih hneedle hrightInner
    | box _hinner ih =>
        intro mutable₁ mutable₂ targets₁ targets₂ pointee₁ pointee₂ hneedle hright
        cases hright with
        | box hrightInner => exact ih hneedle hrightInner
  intro hleft hright
  exact hgeneral hleft rfl hright

theorem partialTyContains_mut_imm_false {partialTy : PartialTy}
    {mutableTargets immTargets : List LVal} {mutablePointee immPointee : Ty} :
    PartialTyContains partialTy (.borrow true mutableTargets mutablePointee) →
    PartialTyContains partialTy (.borrow false immTargets immPointee) →
    False := by
  intro hmut himm
  rcases partialTyContains_borrow_injective hmut himm with ⟨hbool, _htargets, _hpointee⟩
  cases hbool

theorem borrowSafeEnv_update_partialBorrowFree {env : Env} {x : Name}
    {slot : EnvSlot} :
    BorrowSafeEnv env →
    PartialTyBorrowFree slot.ty →
    BorrowSafeEnv (env.update x slot) := by
  intro hsafe hborrowFree y z mutable targetsMutable targetsOther pointeeMutable
    pointeeOther targetMutable targetOther hcontainsMutable hcontainsOther
    htargetMutable htargetOther hconflict
  by_cases hy : y = x
  · have hcontainsMutableAtX :
        (env.update x slot) ⊢ x ↝ Ty.borrow true targetsMutable pointeeMutable := by
      simpa [hy] using hcontainsMutable
    exact False.elim
      (by
        rcases hcontainsMutableAtX with ⟨containedSlot, hslot, hcontainsTy⟩
        have hslotEq : containedSlot = slot := by
          have h : slot = containedSlot := by
            simpa [Env.update] using hslot
          exact h.symm
        subst hslotEq
        exact hborrowFree true targetsMutable pointeeMutable hcontainsTy)
  · by_cases hz : z = x
    · have hcontainsOtherAtX :
          (env.update x slot) ⊢ x ↝ Ty.borrow mutable targetsOther pointeeOther := by
        simpa [hz] using hcontainsOther
      exact False.elim
        (by
          rcases hcontainsOtherAtX with ⟨containedSlot, hslot, hcontainsTy⟩
          have hslotEq : containedSlot = slot := by
            have h : slot = containedSlot := by
              simpa [Env.update] using hslot
            exact h.symm
          subst hslotEq
          exact hborrowFree mutable targetsOther pointeeOther hcontainsTy)
    · exact hsafe y z mutable targetsMutable targetsOther pointeeMutable pointeeOther
        targetMutable targetOther
        (EnvContains.update_fresh_ne hy hcontainsMutable)
        (EnvContains.update_fresh_ne hz hcontainsOther)
        htargetMutable htargetOther hconflict

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

/-- Loan-free analogue of `borrowSafeEnv_update_partialBorrowFree`: a slot
whose contained borrows claim no targets cannot participate in a conflict. -/
theorem borrowSafeEnv_update_partialLoanFree {env : Env} {x : Name}
    {slot : EnvSlot} :
    BorrowSafeEnv env →
    PartialTyLoanFree slot.ty →
    BorrowSafeEnv (env.update x slot) := by
  intro hsafe hloanFree y z mutable targetsMutable targetsOther pointeeMutable
    pointeeOther targetMutable targetOther hcontainsMutable hcontainsOther
    htargetMutable htargetOther hconflict
  by_cases hy : y = x
  · have hcontainsMutableAtX :
        (env.update x slot) ⊢ x ↝ Ty.borrow true targetsMutable pointeeMutable := by
      simpa [hy] using hcontainsMutable
    exact False.elim
      (by
        rcases hcontainsMutableAtX with ⟨containedSlot, hslot, hcontainsTy⟩
        have hslotEq : containedSlot = slot := by
          have h : slot = containedSlot := by
            simpa [Env.update] using hslot
          exact h.symm
        subst hslotEq
        have hempty : targetsMutable = [] :=
          PartialTyLoanFree.empty_targets hloanFree hcontainsTy
        subst hempty
        simp at htargetMutable)
  · by_cases hz : z = x
    · have hcontainsOtherAtX :
          (env.update x slot) ⊢ x ↝ Ty.borrow mutable targetsOther pointeeOther := by
        simpa [hz] using hcontainsOther
      exact False.elim
        (by
          rcases hcontainsOtherAtX with ⟨containedSlot, hslot, hcontainsTy⟩
          have hslotEq : containedSlot = slot := by
            have h : slot = containedSlot := by
              simpa [Env.update] using hslot
            exact h.symm
          subst hslotEq
          have hempty : targetsOther = [] :=
            PartialTyLoanFree.empty_targets hloanFree hcontainsTy
          subst hempty
          simp at htargetOther)
    · exact hsafe y z mutable targetsMutable targetsOther pointeeMutable pointeeOther
        targetMutable targetOther
        (EnvContains.update_fresh_ne hy hcontainsMutable)
        (EnvContains.update_fresh_ne hz hcontainsOther)
        htargetMutable htargetOther hconflict

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
  · intro targetsMutable mutable targetsOther pointeeMutable pointeeOther x
      targetMutable targetOther hcontains _hother htargetMutable _htargetOther
      _hconflict
    have hempty : targetsMutable = [] :=
      TyLoanFree.empty_targets hfree hcontains
    subst hempty
    simp at htargetMutable
  · intro x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther _hcontainsMutable hcontains _htargetMutable
      htargetOther _hconflict
    have hempty : targetsOther = [] :=
      TyLoanFree.empty_targets hfree hcontains
    subst hempty
    simp at htargetOther

theorem tyBorrowSafeAgainstEnv_borrowFree {env : Env} {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowSafeAgainstEnv env ty := by
  intro hfree
  constructor
  · intro targetsMutable mutable targetsOther pointeeMutable pointeeOther x
      targetMutable targetOther hcontains _hother _htargetMutable _htargetOther
      _hconflict
    exact hfree true targetsMutable pointeeMutable hcontains
  · intro x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther _hcontainsMutable hcontains _htargetMutable
      _htargetOther _hconflict
    exact hfree mutable targetsOther pointeeOther hcontains

theorem TyBorrowSafeAgainstEnv.dropLifetime {env : Env} {ty : Ty}
    {lifetime : Lifetime} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv (env.dropLifetime lifetime) ty := by
  intro hsafeTy
  constructor
  · intro targetsMutable mutable targetsOther pointeeMutable pointeeOther x
      targetMutable targetOther hcontains hother htargetMutable htargetOther
      hconflict
    exact hsafeTy.1 targetsMutable mutable targetsOther pointeeMutable pointeeOther
      x targetMutable targetOther hcontains
      (EnvContains.dropLifetime_of_contains hother)
      htargetMutable htargetOther hconflict
  · intro x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther hcontainsMutable hcontains htargetMutable
      htargetOther hconflict
    exact hsafeTy.2 x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther
      (EnvContains.dropLifetime_of_contains hcontainsMutable) hcontains
      htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env ty →
    BorrowSafeEnv (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hsafeTy a b mutable targetsMutable targetsOther pointeeMutable
    pointeeOther targetMutable targetOther hcontainsMutable hcontainsOther
    htargetMutable htargetOther hconflict
  by_cases ha : a = x
  · subst a
    have hcontainsMutableAtX :
        (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢
          x ↝ Ty.borrow true targetsMutable pointeeMutable := by
      simpa using hcontainsMutable
    rcases hcontainsMutableAtX with ⟨containedSlot, hslot, hcontainsTy⟩
    have hslotEq :
        containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    by_cases hb : b = x
    · exact hb.symm
    · exact False.elim
        (hsafeTy.1 targetsMutable mutable targetsOther pointeeMutable pointeeOther
          b targetMutable targetOther hcontainsTy
          (EnvContains.update_fresh_ne hb hcontainsOther)
          htargetMutable htargetOther hconflict)
  · by_cases hb : b = x
    · subst b
      have hcontainsOtherAtX :
          (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢
            x ↝ Ty.borrow mutable targetsOther pointeeOther := by
        simpa using hcontainsOther
      rcases hcontainsOtherAtX with ⟨containedSlot, hslot, hcontainsTy⟩
      have hslotEq :
          containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      exact False.elim
        (hsafeTy.2 a targetsMutable mutable targetsOther pointeeMutable pointeeOther
          targetMutable targetOther
          (EnvContains.update_fresh_ne ha hcontainsMutable)
          hcontainsTy htargetMutable htargetOther hconflict)
    · exact hsafe a b mutable targetsMutable targetsOther pointeeMutable pointeeOther
        targetMutable targetOther
        (EnvContains.update_fresh_ne ha hcontainsMutable)
        (EnvContains.update_fresh_ne hb hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_dropLifetime {env : Env} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    BorrowSafeEnv (env.dropLifetime lifetime) := by
  intro hsafe x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
    targetMutable targetOther hcontainsMutable hcontainsOther htargetMutable
    htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
    targetMutable targetOther
    (EnvContains.dropLifetime_of_contains hcontainsMutable)
    (EnvContains.dropLifetime_of_contains hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafety_block_drop {env env' : Env} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env' = env.dropLifetime lifetime →
    BorrowSafeEnv env' := by
  intro hsafe henv'
  rw [henv']
  exact borrowSafeEnv_dropLifetime hsafe

theorem LValTyping.no_readProhibited_targets_of_immBorrow {env : Env} :
    BorrowSafeEnv env →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {borrowTargets borrowPointee},
        PartialTyContains partialTy (.borrow false borrowTargets borrowPointee) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ ReadProhibited env target) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {borrowTargets borrowPointee},
        PartialTyContains partialTy (.borrow false borrowTargets borrowPointee) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ ReadProhibited env target) := by
  intro hsafe
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ∀ {borrowTargets borrowPointee},
          PartialTyContains partialTy (.borrow false borrowTargets borrowPointee) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (motive_2 := fun targets partialTy lifetime _ =>
        ∀ {borrowTargets borrowPointee},
          PartialTyContains partialTy (.borrow false borrowTargets borrowPointee) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (by
        intro x slot hslot borrowTargets borrowPointee hcontains target htarget hread
        rcases hread with
          ⟨borrower, mutableTargets, mutablePointee, mutableTarget,
            hmutableContains, hmutableTarget, hconflict⟩
        by_cases hsame : borrower = x
        · subst hsame
          rcases hmutableContains with ⟨mutableSlot, hmutableSlot, hmutableTy⟩
          rw [hslot] at hmutableSlot
          injection hmutableSlot with hslotEq
          subst hslotEq
          exact partialTyContains_mut_imm_false hmutableTy hcontains
        · have hsafeContradiction :
              borrower = x := by
            exact hsafe borrower x false mutableTargets borrowTargets
              mutablePointee borrowPointee mutableTarget target
              hmutableContains
              ⟨slot, hslot, hcontains⟩
              hmutableTarget
              htarget
              hconflict
          exact hsame hsafeContradiction)
      (by
        intro _lv _inner _lifetime _htyping ih borrowTargets borrowPointee
          hcontains target htarget hread
        exact ih (PartialTyContains.box hcontains) target htarget hread)
      (by
        intro _lv _mutable _targets _pointee _borrowLifetime _targetLifetime
          _hborrow _htargets _ihBorrow ihTargets borrowTargets _borrowPointee
          hcontains target htarget hread
        exact ihTargets hcontains target htarget hread)
      (by
        intro _ty _hvars borrowTargets _borrowPointee hcontains target htarget _hread
        have hempty : borrowTargets = [] :=
          PartialTyLoanFree.empty_targets
            (partialTy := .ty _ty)
            (by simpa [PartialTyLoanFree, PartialTy.allVars] using _hvars)
            hcontains
        subst hempty
        cases htarget)
      (by
        intro target ty lifetime _htarget ihTarget borrowTargets _borrowPointee
          hcontains selected hselected hread
        exact ihTarget hcontains selected hselected hread)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion _hintersection ihHead ihRest borrowTargets
          _borrowPointee hcontains selected hselected hread
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead hread
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest hread)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ∀ {borrowTargets borrowPointee},
          PartialTyContains partialTy (.borrow false borrowTargets borrowPointee) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (motive_2 := fun targets partialTy lifetime _ =>
        ∀ {borrowTargets borrowPointee},
          PartialTyContains partialTy (.borrow false borrowTargets borrowPointee) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (by
        intro x slot hslot borrowTargets borrowPointee hcontains target htarget hread
        rcases hread with
          ⟨borrower, mutableTargets, mutablePointee, mutableTarget,
            hmutableContains, hmutableTarget, hconflict⟩
        by_cases hsame : borrower = x
        · subst hsame
          rcases hmutableContains with ⟨mutableSlot, hmutableSlot, hmutableTy⟩
          rw [hslot] at hmutableSlot
          injection hmutableSlot with hslotEq
          subst hslotEq
          exact partialTyContains_mut_imm_false hmutableTy hcontains
        · have hsafeContradiction :
              borrower = x := by
            exact hsafe borrower x false mutableTargets borrowTargets
              mutablePointee borrowPointee mutableTarget target
              hmutableContains
              ⟨slot, hslot, hcontains⟩
              hmutableTarget
              htarget
              hconflict
          exact hsame hsafeContradiction)
      (by
        intro _lv _inner _lifetime _htyping ih borrowTargets borrowPointee
          hcontains target htarget hread
        exact ih (PartialTyContains.box hcontains) target htarget hread)
      (by
        intro _lv _mutable _targets _pointee _borrowLifetime _targetLifetime
          _hborrow _htargets _ihBorrow ihTargets borrowTargets _borrowPointee
          hcontains target htarget hread
        exact ihTargets hcontains target htarget hread)
      (by
        intro _ty _hvars borrowTargets _borrowPointee hcontains target htarget _hread
        have hempty : borrowTargets = [] :=
          PartialTyLoanFree.empty_targets
            (partialTy := .ty _ty)
            (by simpa [PartialTyLoanFree, PartialTy.allVars] using _hvars)
            hcontains
        subst hempty
        cases htarget)
      (by
        intro target ty lifetime _htarget ihTarget borrowTargets _borrowPointee
          hcontains selected hselected hread
        exact ihTarget hcontains selected hselected hread)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion _hintersection ihHead ihRest borrowTargets
          _borrowPointee hcontains selected hselected hread
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead hread
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest hread)
      htyping

theorem borrowSafeEnv_update_fresh_mutBorrow {env : Env} {gamma : Name}
    {lv : LVal} {pointee : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    ¬ WriteProhibited env lv →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow true [lv] pointee), lifetime := lifetime }) := by
  intro hsafe _hfresh hnotWrite x y mutable targetsMutable targetsOther
    pointeeMutable pointeeOther targetMutable targetOther hcontainsMutable
    hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow true [lv] pointee), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable pointeeMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow true [lv] pointee), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow true [lv] pointee), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq : Ty.borrow true [lv] pointee =
        Ty.borrow true targetsMutable pointeeMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    injection hborrowEq with _hmut htargetsMutable _hpointee
    subst htargetsMutable
    have htargetMutableEq : targetMutable = lv := by
      simpa using htargetMutable
    have hconflictLv : lv ⋈ targetOther := by
      simpa [htargetMutableEq] using hconflict
    by_cases hy : y = gamma
    · exact hx.trans hy.symm
    · have hcontainsOtherOld : env ⊢ y ↝ Ty.borrow mutable targetsOther pointeeOther :=
        EnvContains.update_fresh_ne hy hcontainsOther
      have hwrite : WriteProhibited env lv := by
        cases mutable with
        | false =>
            exact Or.inr ⟨y, targetsOther, pointeeOther, targetOther, hcontainsOtherOld,
              htargetOther, pathConflicts_symm hconflictLv⟩
        | true =>
            exact Or.inl ⟨y, targetsOther, pointeeOther, targetOther, hcontainsOtherOld,
              htargetOther, pathConflicts_symm hconflictLv⟩
      exact False.elim (hnotWrite hwrite)
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow true [lv] pointee), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther pointeeOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow true [lv] pointee), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow true [lv] pointee), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq : Ty.borrow true [lv] pointee =
          Ty.borrow mutable targetsOther pointeeOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargetsOther _hpointee
      subst htargetsOther
      have htargetOtherEq : targetOther = lv := by
        simpa using htargetOther
      have hconflictLv : targetMutable ⋈ lv := by
        simpa [htargetOtherEq] using hconflict
      have hcontainsMutableOld : env ⊢ x ↝ Ty.borrow true targetsMutable pointeeMutable :=
        EnvContains.update_fresh_ne hx hcontainsMutable
      have hwrite : WriteProhibited env lv :=
        Or.inl ⟨x, targetsMutable, pointeeMutable, targetMutable, hcontainsMutableOld,
          htargetMutable, hconflictLv⟩
      exact False.elim (hnotWrite hwrite)
    · exact hsafe x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
        targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_fresh_immBorrow {env : Env} {gamma : Name}
    {lv : LVal} {pointee : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    ¬ ReadProhibited env lv →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow false [lv] pointee), lifetime := lifetime }) := by
  intro hsafe hfresh hnotRead x y mutable targetsMutable targetsOther
    pointeeMutable pointeeOther targetMutable targetOther hcontainsMutable
    hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow false [lv] pointee), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable pointeeMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow false [lv] pointee), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow false [lv] pointee), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq :
        Ty.borrow false [lv] pointee = Ty.borrow true targetsMutable pointeeMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    cases hborrowEq
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow false [lv] pointee), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther pointeeOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow false [lv] pointee), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow false [lv] pointee), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq :
          Ty.borrow false [lv] pointee = Ty.borrow mutable targetsOther pointeeOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargets _hpointee
      have htargetOtherEq : targetOther = lv := by
        cases htargets
        simpa using htargetOther
      subst htargetOtherEq
      exact False.elim (hnotRead ⟨x, targetsMutable, pointeeMutable, targetMutable,
        EnvContains.update_fresh_ne hx hcontainsMutable,
        htargetMutable,
        hconflict⟩)
    · exact hsafe x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
        targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_fresh_immBorrowMany {env : Env} {gamma : Name}
    {targets : List LVal} {pointee : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    (∀ target, target ∈ targets → ¬ ReadProhibited env target) →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow false targets pointee), lifetime := lifetime }) := by
  intro hsafe hfresh hnotRead x y mutable targetsMutable targetsOther
    pointeeMutable pointeeOther targetMutable targetOther hcontainsMutable
    hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow false targets pointee), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable pointeeMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow false targets pointee), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow false targets pointee), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq :
        Ty.borrow false targets pointee = Ty.borrow true targetsMutable pointeeMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    cases hborrowEq
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow false targets pointee), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther pointeeOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow false targets pointee), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow false targets pointee), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq :
          Ty.borrow false targets pointee = Ty.borrow mutable targetsOther pointeeOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargets _hpointee
      subst htargets
      exact False.elim
        (hnotRead targetOther htargetOther
          ⟨x, targetsMutable, pointeeMutable, targetMutable,
            EnvContains.update_fresh_ne hx hcontainsMutable,
            htargetMutable,
            hconflict⟩)
    · exact hsafe x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
        targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem tyBorrowSafeAgainstEnv_mutBorrow {env : Env} {lv : LVal} {pointee : Ty} :
    ¬ WriteProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow true [lv] pointee) := by
  intro hnotWrite
  constructor
  · intro targetsMutable mutable targetsOther pointeeMutable pointeeOther x
      targetMutable targetOther hcontains hother htargetMutable htargetOther
      hconflict
    have hborrowEq : Ty.borrow true [lv] pointee =
        Ty.borrow true targetsMutable pointeeMutable :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmut htargetsMutable _hpointee
    subst htargetsMutable
    have htargetMutableEq : targetMutable = lv := by
      simpa using htargetMutable
    have hconflictLv : lv ⋈ targetOther := by
      simpa [htargetMutableEq] using hconflict
    have hwrite : WriteProhibited env lv := by
      cases mutable with
      | false =>
          exact Or.inr ⟨x, targetsOther, pointeeOther, targetOther, hother,
            htargetOther, pathConflicts_symm hconflictLv⟩
      | true =>
          exact Or.inl ⟨x, targetsOther, pointeeOther, targetOther, hother,
            htargetOther, pathConflicts_symm hconflictLv⟩
    exact hnotWrite hwrite
  · intro x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther hcontainsMutable hcontains htargetMutable
      htargetOther hconflict
    have hborrowEq : Ty.borrow true [lv] pointee =
        Ty.borrow mutable targetsOther pointeeOther :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmutable htargetsOther _hpointee
    subst htargetsOther
    have htargetOtherEq : targetOther = lv := by
      simpa using htargetOther
    have hconflictLv : targetMutable ⋈ lv := by
      simpa [htargetOtherEq] using hconflict
    exact hnotWrite
      (Or.inl ⟨x, targetsMutable, pointeeMutable, targetMutable, hcontainsMutable,
        htargetMutable, hconflictLv⟩)

theorem tyBorrowSafeAgainstEnv_immBorrowMany {env : Env} {targets : List LVal}
    {pointee : Ty} :
    (∀ target, target ∈ targets → ¬ ReadProhibited env target) →
    TyBorrowSafeAgainstEnv env (.borrow false targets pointee) := by
  intro hnotRead
  constructor
  · intro targetsMutable mutable targetsOther pointeeMutable pointeeOther x
      targetMutable targetOther hcontains _hother _htargetMutable _htargetOther
      _hconflict
    have hborrowEq :
        Ty.borrow false targets pointee = Ty.borrow true targetsMutable pointeeMutable :=
      partialTyContains_borrow_iff_eq.mp hcontains
    cases hborrowEq
  · intro x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther hcontainsMutable hcontains htargetMutable
      htargetOther hconflict
    have hborrowEq :
        Ty.borrow false targets pointee =
          Ty.borrow mutable targetsOther pointeeOther :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmutable htargets _hpointee
    subst htargets
    exact hnotRead targetOther htargetOther
      ⟨x, targetsMutable, pointeeMutable, targetMutable, hcontainsMutable,
        htargetMutable, hconflict⟩

theorem tyBorrowSafeAgainstEnv_immBorrow {env : Env} {lv : LVal} {pointee : Ty} :
    ¬ ReadProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow false [lv] pointee) := by
  intro hnotRead
  exact tyBorrowSafeAgainstEnv_immBorrowMany
    (by
      intro target htarget
      have htargetEq : target = lv := by
        simpa using htarget
      subst htargetEq
      exact hnotRead)

theorem PartialTyContains.tyBox_borrow_inv {inner : Ty} {mutable : Bool}
    {targets : List LVal} {pointee : Ty} :
    PartialTyContains (.ty (.box inner)) (.borrow mutable targets pointee) →
    PartialTyContains (.ty inner) (.borrow mutable targets pointee) := by
  intro hcontains
  cases hcontains with
  | tyBox hinner => exact hinner

theorem TyBorrowSafeAgainstEnv.box {env : Env} {ty : Ty} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv env (.box ty) := by
  intro hsafeTy
  constructor
  · intro targetsMutable mutable targetsOther pointeeMutable pointeeOther x
      targetMutable targetOther hcontains hother htargetMutable htargetOther
      hconflict
    exact hsafeTy.1 targetsMutable mutable targetsOther pointeeMutable pointeeOther
      x targetMutable targetOther
      (PartialTyContains.tyBox_borrow_inv hcontains) hother
      htargetMutable htargetOther hconflict
  · intro x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther hcontainsMutable hcontains htargetMutable
      htargetOther hconflict
    exact hsafeTy.2 x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther
      hcontainsMutable (PartialTyContains.tyBox_borrow_inv hcontains)
      htargetMutable htargetOther hconflict

/-! ## Source-Level Initial States -/

theorem sourceValue_valueTyping_borrowFree {typing : StoreTyping} {value : Value}
    {ty : Ty} :
    SourceValue value →
    ValueTyping typing value ty →
    TyBorrowFree ty := by
  intro hsource htyping
  cases value with
  | unit =>
      cases htyping
      exact tyBorrowFree_unit
  | int _ =>
      cases htyping
      exact tyBorrowFree_int
  | bool _ =>
      cases htyping
      exact tyBorrowFree_bool
  | ref _ =>
      cases hsource

/-- A struck partial type contains no live full type.

`Strike` replaces the moved leaf by `undef` and only rebuilds boxes on the way
back to the root, so no `PartialTyContains` derivation can start from the struck
result. -/
theorem PartialTyContains.not_strike_result {path : Path} {source struck : PartialTy}
    {needle : Ty} :
    Strike path source struck →
    ¬ PartialTyContains struck needle := by
  intro hstrike hcontains
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains
  | cons _ path ih =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains with
      | box hinner =>
          exact ih hstrike hinner

theorem List.Unit_cons_append_eq_append_cons (path suffix : List Unit) :
    () :: (path ++ suffix) = path ++ (() :: suffix) := by
  induction path with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head
      simp [ih]

/-- A `Strike` following an lvalue path can be decomposed at the partial type
selected by the lvalue typing derivation.

The borrow-dereference case is where this lemma pays for itself: `Strike` can
only step through `PartialTy.box`, so it cannot take one more selector after an
lvalue whose selected type is a full borrow. -/
theorem LValTyping.strike_suffix_at_type {env : Env} :
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {slot struck suffix},
        env.slotAt (LVal.base lv) = some slot →
        Strike (LVal.path lv ++ suffix) slot.ty struck →
        ∃ struckAt, Strike suffix partialTy struckAt) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime → True) := by
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy _lifetime _ =>
        ∀ {slot struck suffix},
          env.slotAt (LVal.base lv) = some slot →
          Strike (LVal.path lv ++ suffix) slot.ty struck →
          ∃ struckAt, Strike suffix partialTy struckAt)
      (motive_2 := fun _targets _partialTy _lifetime _ => True)
      (by
        intro x envSlot hslot slot struck suffix hbase hstrike
        have hbase' : env.slotAt x = some slot := by
          simpa [LVal.base] using hbase
        have hslotEq : envSlot = slot := by
          have hsomeEq : some envSlot = some slot := by
            rw [← hslot, hbase']
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact ⟨struck, by simpa [LVal.path] using hstrike⟩)
      (by
        intro lv inner lifetime _htyping ih slot struck suffix hbase hstrike
        have hstrikeAtParent :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        rcases ih hbase hstrikeAtParent with ⟨parentStruck, hparentStruck⟩
        cases parentStruck with
        | ty parentTy =>
            simp [Strike] at hparentStruck
        | box innerStruck =>
            exact ⟨innerStruck, by simpa [Strike] using hparentStruck⟩
        | undef parentTy =>
            simp [Strike] at hparentStruck)
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          _hborrow _htargets ihBorrow _ihTargets slot struck suffix hbase hstrike
        have hstrikeAtBorrow :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        rcases ihBorrow hbase hstrikeAtBorrow with ⟨borrowStruck, hborrowStruck⟩
        simp [Strike] at hborrowStruck)
      (by
        intro _ty _hvars
        trivial)
      (by
        intro target ty lifetime _htarget _ihTarget
        trivial)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest _hunion _hintersection _ihHead _ihRest
        trivial)
      htyping
  · intro targets partialTy lifetime _htyping
    trivial

/-- If an lvalue is moved by `Strike`, every borrow contained in its selected
partial type was already contained in the moved base slot.

This is the static origin fact needed to prove the moved result type is safe
against the post-move environment.  The proof follows the lvalue spine.  Box
dereferences push the obligation one selector back toward the base slot; borrow
dereferences are impossible because `Strike` cannot continue below a full borrow
leaf. -/
theorem LValTyping.contains_base_of_strike_suffix {env : Env} :
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {slot struck suffix needle},
        env.slotAt (LVal.base lv) = some slot →
        Strike (LVal.path lv ++ suffix) slot.ty struck →
        PartialTyContains partialTy needle →
        env ⊢ LVal.base lv ↝ needle) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime → True) := by
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy _lifetime _ =>
        ∀ {slot struck suffix needle},
          env.slotAt (LVal.base lv) = some slot →
          Strike (LVal.path lv ++ suffix) slot.ty struck →
          PartialTyContains partialTy needle →
          env ⊢ LVal.base lv ↝ needle)
      (motive_2 := fun _targets _partialTy _lifetime _ => True)
      (by
        intro x envSlot hslot slot _struck _suffix needle hbase _hstrike hcontains
        have hbase' : env.slotAt x = some slot := by
          simpa [LVal.base] using hbase
        have hslotEq : envSlot = slot := by
          have hsomeEq : some envSlot = some slot := by
            rw [← hslot, hbase']
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact ⟨envSlot, hslot, hcontains⟩)
      (by
        intro lv inner lifetime _htyping ih slot struck suffix needle hbase hstrike
          hcontains
        have hstrikeAtParent :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        exact ih hbase hstrikeAtParent (PartialTyContains.box hcontains))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets _ihBorrow _ihTargets slot struck suffix needle hbase hstrike
          _hcontains
        have hstrikeAtBorrow :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        rcases (LValTyping.strike_suffix_at_type.1 hborrow hbase hstrikeAtBorrow) with
          ⟨borrowStruck, hborrowStruck⟩
        simp [Strike] at hborrowStruck)
      (by
        intro _ty _hvars
        trivial)
      (by
        intro target ty lifetime _htarget _ihTarget
        trivial)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest _hunion _hintersection _ihHead _ihRest
        trivial)
      htyping
  · intro targets partialTy lifetime _htyping
    trivial

theorem LValTyping.contains_base_of_strike {env : Env} {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} {slot : EnvSlot}
    {struck : PartialTy}
    {needle : Ty} :
    LValTyping env lv partialTy lifetime →
    env.slotAt (LVal.base lv) = some slot →
    Strike (LVal.path lv) slot.ty struck →
    PartialTyContains partialTy needle →
    env ⊢ LVal.base lv ↝ needle := by
  intro htyping hslot hstrike hcontains
  simpa using
    (LValTyping.contains_base_of_strike_suffix.1 htyping
      (slot := slot) (struck := struck) (suffix := []) hslot
      (by simpa using hstrike) hcontains)

/-- The base slot struck by an `EnvMove` cannot still contain a live borrow in
the moved environment. -/
theorem EnvContains.move_base_same_false {env env' : Env} {lv : LVal}
    {mutable : Bool} {targets : List LVal} {pointee : Ty} :
    EnvMove env lv env' →
    ¬ env' ⊢ LVal.base lv ↝ Ty.borrow mutable targets pointee := by
  intro hmove hcontains
  rcases hmove with ⟨slot, struck, _hslot, hstrike, henv'⟩
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq :
      containedSlot = { slot with ty := struck } := by
    have h :
        { slot with ty := struck } = containedSlot := by
      simpa [henv', Env.update] using hcontainedSlot
    exact h.symm
  subst hcontainedSlotEq
  exact PartialTyContains.not_strike_result hstrike hcontainsTy

/-- Moving an lval preserves borrow safety of the environment before adding the
result binding.

`EnvMove` only strikes part of a slot to `undef`; every contained borrow still
visible in the moved environment was already contained in the source
environment.  Thus the original borrow-safety relation applies directly. -/
theorem borrowSafeEnv_move {env env' : Env} {lv : LVal} :
    BorrowSafeEnv env →
    EnvMove env lv env' →
    BorrowSafeEnv env' := by
  intro hsafe hmove x y mutable targetsMutable targetsOther pointeeMutable
    pointeeOther targetMutable targetOther hcontainsMutable hcontainsOther
    htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
    targetMutable targetOther
    (EnvContains.of_move hmove hcontainsMutable)
    (EnvContains.of_move hmove hcontainsOther)
    htargetMutable htargetOther hconflict

theorem tyBorrowSafeAgainstEnv_move_of_base_contains {env env₂ : Env}
    {lv : LVal} {ty : Ty} :
    BorrowSafeEnv env →
    EnvMove env lv env₂ →
    (∀ mutable targets pointee,
      PartialTyContains (.ty ty) (.borrow mutable targets pointee) →
      env ⊢ LVal.base lv ↝ Ty.borrow mutable targets pointee) →
    TyBorrowSafeAgainstEnv env₂ ty := by
  intro hsafe hmove hbaseContains
  constructor
  · intro targetsMutable mutable targetsOther pointeeMutable pointeeOther x
      targetMutable targetOther hcontainsTy hcontainsOther htargetMutable
      htargetOther hconflict
    by_cases hxBase : x = LVal.base lv
    · subst hxBase
      exact False.elim (EnvContains.move_base_same_false hmove hcontainsOther)
    · have hcontainsOtherOld :
          env ⊢ x ↝ Ty.borrow mutable targetsOther pointeeOther :=
        EnvContains.of_move hmove hcontainsOther
      have hbaseEq :
          LVal.base lv = x :=
        hsafe (LVal.base lv) x mutable targetsMutable targetsOther
          pointeeMutable pointeeOther targetMutable targetOther
          (hbaseContains true targetsMutable pointeeMutable hcontainsTy)
          hcontainsOtherOld
          htargetMutable htargetOther hconflict
      exact False.elim (hxBase hbaseEq.symm)
  · intro x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther hcontainsMutable hcontainsTy htargetMutable
      htargetOther hconflict
    by_cases hxBase : x = LVal.base lv
    · subst hxBase
      exact False.elim (EnvContains.move_base_same_false hmove hcontainsMutable)
    · have hcontainsMutableOld :
          env ⊢ x ↝ Ty.borrow true targetsMutable pointeeMutable :=
        EnvContains.of_move hmove hcontainsMutable
      have hbaseEq :
          x = LVal.base lv :=
        hsafe x (LVal.base lv) mutable targetsMutable targetsOther
          pointeeMutable pointeeOther targetMutable targetOther hcontainsMutableOld
          (hbaseContains mutable targetsOther pointeeOther hcontainsTy)
          htargetMutable htargetOther hconflict
      exact False.elim (hxBase hbaseEq)

/--
Constructor-level borrow-safety landmarks used by the source-scoped
borrow-safety induction.

The assignment field consumes the RHS induction result: `BorrowSafeEnv env₂`
plus the root-independent fact that the RHS type has no borrow-target conflicts
with `env₂`.  Block bodies are handled by the mutual term/list induction below:
the induction carries `TyBorrowSafeAgainstEnv` through `dropLifetime`, so there
is no separate block-list obligation here.
-/
structure BorrowSafetyPreservationObligations : Prop where
  envWrite {env₁ env₂ env₃ : Env}
      {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
      {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
      BorrowSafeEnv env₂ →
      TyBorrowSafeAgainstEnv env₂ rhsTy →
      LValTyping env₂ lhs oldTy targetLifetime →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      ShapeCompatible env₂ oldTy (.ty rhsTy) →
      WellFormedTy env₂ rhsTy targetLifetime →
      EnvWrite 0 env₂ lhs rhsTy env₃ →
      (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
      ¬ WriteProhibited env₃ lhs →
      BorrowSafeEnv env₃

/-- Remaining explicit `EnvWrite` borrow-safety frame obligation.

The global term-typing induction supplies both `BorrowSafeEnv env₂` and the RHS
root-independent type/environment invariant.  The latter is part of the real
assignment argument: `BorrowSafeEnv env₂` alone does not say that borrow targets
contained in `rhsTy` are safe against existing environment roots.

The remaining hard case is fan-out through a mutable borrow.  If two result roots
receive borrow targets originating from `rhsTy`, `TyBorrowSafeAgainstEnv env₂
rhsTy` is not enough: it only rules out conflicts between `rhsTy` and the
pre-write environment, not conflicts created by duplicating the RHS borrow into
multiple result roots.  Completing this proof likely requires either a
source/result invariant saying RHS-derived borrow targets are safe when
duplicated by this write, or a borrow-inference side condition ruling out such
fan-out for non-borrow-free RHS types.
-/
theorem borrowSafetyPreservation_envWrite
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    BorrowSafeEnv env₂ →
    TyBorrowSafeAgainstEnv env₂ rhsTy →
    LValTyping env₂ lhs oldTy targetLifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
    ¬ WriteProhibited env₃ lhs →
    BorrowSafeEnv env₃ := by
  intro hborrowSafe hsafeTy _hLhsPost _hRhs _hshape _hwellTy hwrite hranked
    _hnotWrite x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
    targetMutable targetOther hcontainsMutable hcontainsOther htargetMutable
    htargetOther hconflict
  rcases hranked with ⟨_φ, _hlinBy, hbelow⟩
  rcases hcontainsMutable with ⟨mutableSlot, hmutableSlot, hmutableContains⟩
  rcases hcontainsOther with ⟨otherSlot, hotherSlot, hotherContains⟩
  have hmutableOrigin :=
    EnvWrite.borrowTargetOrigin_all hwrite x mutableSlot true targetsMutable pointeeMutable
      hmutableSlot hmutableContains targetMutable htargetMutable
  have hotherOrigin :=
    EnvWrite.borrowTargetOrigin_all hwrite y otherSlot mutable targetsOther pointeeOther
      hotherSlot hotherContains targetOther htargetOther
  rcases hmutableOrigin with hmutableOld | hmutableRhs
  · rcases hmutableOld with
      ⟨oldMutableSlot, oldMutableTargets, oldMutablePointee, holdMutableSlot,
        holdMutableContains, holdMutableTarget⟩
    rcases hotherOrigin with hotherOld | hotherRhs
    · rcases hotherOld with
        ⟨oldOtherSlot, oldOtherTargets, oldOtherPointee, holdOtherSlot,
          holdOtherContains, holdOtherTarget⟩
      exact hborrowSafe x y mutable oldMutableTargets oldOtherTargets
        oldMutablePointee oldOtherPointee targetMutable targetOther
        ⟨oldMutableSlot, holdMutableSlot, holdMutableContains⟩
        ⟨oldOtherSlot, holdOtherSlot, holdOtherContains⟩
        holdMutableTarget holdOtherTarget hconflict
    · rcases hotherRhs with
        ⟨rhsOtherTargets, rhsOtherPointee, hrhsOtherContains, hrhsOtherTarget⟩
      exact False.elim
        (hsafeTy.2 x oldMutableTargets mutable rhsOtherTargets oldMutablePointee
          rhsOtherPointee targetMutable targetOther
          ⟨oldMutableSlot, holdMutableSlot, holdMutableContains⟩
          hrhsOtherContains holdMutableTarget hrhsOtherTarget hconflict)
  · rcases hmutableRhs with
      ⟨rhsMutableTargets, rhsMutablePointee, hrhsMutableContains, hrhsMutableTarget⟩
    rcases hotherOrigin with hotherOld | hotherRhs
    · rcases hotherOld with
        ⟨oldOtherSlot, oldOtherTargets, oldOtherPointee, holdOtherSlot,
          holdOtherContains, holdOtherTarget⟩
      exact False.elim
        (hsafeTy.1 rhsMutableTargets mutable oldOtherTargets rhsMutablePointee
          oldOtherPointee y targetMutable targetOther hrhsMutableContains
          ⟨oldOtherSlot, holdOtherSlot, holdOtherContains⟩
          hrhsMutableTarget holdOtherTarget hconflict)
    · rcases hotherRhs with
        ⟨rhsOtherTargets, rhsOtherPointee, hrhsOtherContains, hrhsOtherTarget⟩
      exact hbelow.2 x y mutable targetsMutable targetsOther pointeeMutable
        pointeeOther targetMutable targetOther
        ⟨mutableSlot, hmutableSlot, hmutableContains⟩
        ⟨otherSlot, hotherSlot, hotherContains⟩
        htargetMutable htargetOther hconflict
        ⟨true, rhsMutableTargets, rhsMutablePointee, hrhsMutableContains,
          hrhsMutableTarget⟩
        ⟨mutable, rhsOtherTargets, rhsOtherPointee, hrhsOtherContains,
          hrhsOtherTarget⟩

/-- Concrete borrow-safety package assembled from proved local preservation lemmas. -/
theorem borrowSafetyPreservationObligations_proved :
    BorrowSafetyPreservationObligations where
  envWrite := borrowSafetyPreservation_envWrite

/-- Compatibility wrapper for the old explicit-obligation route.

The explicit global assignment/declaration predicates are no longer required:
the needed facts are carried by the `TermTyping` derivation itself and consumed
by `borrowInvariance_of_ruleCarriedObligations`. -/
theorem borrowInvariance_of_rankedAssign_and_declFreshCoherence
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

/--
Main source-scoped borrow-safety induction.

This is intentionally small: runtime preservation only needs the output
environment to remain borrow-safe, plus a root-independent fact about the result
type so assignment can validate the next write.
-/
theorem typingPreservesBorrowSafeCore {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    SourceTerm term →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    BorrowSafeEnv env₂ ∧
      TyBorrowSafeAgainstEnv env₂ ty := by
  intro hsource hborrowSafe htyping
  let hobligations := borrowSafetyPreservationObligations_proved
  refine TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      SourceTerm term →
        BorrowSafeEnv env →
        BorrowSafeEnv env₂ ∧
          TyBorrowSafeAgainstEnv env₂ ty)
    (motive_2 := fun env _typing lifetime terms _ty env₂ _ =>
      SourceTerm (.block lifetime terms) →
        BorrowSafeEnv env →
        BorrowSafeEnv env₂ ∧
          TyBorrowSafeAgainstEnv env₂ _ty)
    ?const ?missing ?copy ?move ?mutBorrow ?immBorrow ?box ?block
    ?declare ?assign ?eq ?ite ?iteDiverging
    ?whileLoopDiverging ?whileLoop ?singleton ?cons
    htyping hsource hborrowSafe
  case const =>
    intro _env _typing _lifetime _value _ty hvalueTyping hsource hborrowSafe
    have hborrowFree : TyBorrowFree _ty :=
      sourceValue_valueTyping_borrowFree
        (hsource _value (by simp [termValues])) hvalueTyping
    exact ⟨hborrowSafe, tyBorrowSafeAgainstEnv_borrowFree hborrowFree⟩
  case missing =>
    intro _env _typing _lifetime _ty _hwellTy hloanFree _hsource hborrowSafe
    exact ⟨hborrowSafe, tyBorrowSafeAgainstEnv_loanFree hloanFree⟩
  case copy =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hcopy hnotRead
      _hsource hborrowSafe
    refine ⟨hborrowSafe, ?_⟩
    cases hcopy with
    | unit =>
        exact tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit
    | int =>
        exact tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_int
    | bool =>
        exact tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_bool
    | immBorrow =>
        rename_i targets
        exact tyBorrowSafeAgainstEnv_immBorrowMany
          (by
            intro target htarget
            exact (LValTyping.no_readProhibited_targets_of_immBorrow hborrowSafe).1
              hLv PartialTyContains.here target htarget)
  case move =>
    intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty hLv hnotWrite
      hmove _hsource hborrowSafe
    have hcore : BorrowSafeEnv _env₂ :=
      borrowSafeEnv_move hborrowSafe hmove
    have hsafeTy : TyBorrowSafeAgainstEnv _env₂ _ty := by
      rcases hmove with ⟨slot, struck, hslot, hstrike, henv₂⟩
      subst henv₂
      exact tyBorrowSafeAgainstEnv_move_of_base_contains
        hborrowSafe
        ⟨slot, struck, hslot, hstrike, rfl⟩
        (by
          intro mutable targets pointee hcontains
          exact LValTyping.contains_base_of_strike hLv hslot hstrike hcontains)
    exact ⟨hcore, hsafeTy⟩
  case mutBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hmutable hnotWrite
      _hsource hborrowSafe
    exact ⟨hborrowSafe, tyBorrowSafeAgainstEnv_mutBorrow hnotWrite⟩
  case immBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty hLv hnotRead _hsource
      hborrowSafe
    exact ⟨hborrowSafe, tyBorrowSafeAgainstEnv_immBorrow hnotRead⟩
  case box =>
    intro _env₁ _env₂ _typing _lifetime _term _ty hterm ih hsource hborrowSafe
    have hinner := ih (SourceTerm.box_inner hsource) hborrowSafe
    exact ⟨hinner.1, TyBorrowSafeAgainstEnv.box hinner.2⟩
  case block =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty
      hblockChild hterms hwellTy hdrop _ih hsource hborrowSafe
    have hbody := _ih hsource hborrowSafe
    have hbodySafe : BorrowSafeEnv _env₂ :=
      hbody.1
    have hbodyTySafe : TyBorrowSafeAgainstEnv _env₂ _ty :=
      hbody.2
    have hblockTySafe : TyBorrowSafeAgainstEnv _env₃ _ty := by
      rw [hdrop]
      exact TyBorrowSafeAgainstEnv.dropLifetime hbodyTySafe
    have hblockCore :
        BorrowSafeEnv _env₃ :=
      borrowSafety_block_drop hbodySafe hdrop
    exact ⟨hblockCore, hblockTySafe⟩
  case declare =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty hfreshX hterm
      hfreshOut _hcoh henv₃ _ih hsource hborrowSafe
    have hinner := _ih (SourceTerm.declare_inner hsource) hborrowSafe
    have hdeclaredSafe :
        BorrowSafeEnv
          (_env₂.update _x { ty := .ty _ty, lifetime := _lifetime }) := by
      exact borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv hinner.1 hinner.2
    rw [henv₃]
    exact ⟨hdeclaredSafe, tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit⟩
  case assign =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs
      _rhsTy hRhs hLhsPost hshape hwellTy hwrite hranked hcoh
      _hcontained hnotWrite _ih hsource hborrowSafe
    have hRhsSafe := _ih (SourceTerm.assign_inner hsource) hborrowSafe
    have hwriteSafe :
        BorrowSafeEnv _env₃ :=
      hobligations.envWrite hRhsSafe.1 hRhsSafe.2 hLhsPost hRhs hshape hwellTy
        hwrite hranked hnotWrite
    exact ⟨hwriteSafe, tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit⟩
  case eq =>
    intro _env₁ _env₂ _env₃ _envGhost _ghost _typing _lifetime _lhs _rhs
      _lhsTy _rhsTy _hLhs hfresh _htypeFresh _htyFresh _hstoreFresh _hghostRhs
      _hnotMention henvEq _hcopyL _hcopyR _hshape ihL ihGhost hsource hborrowSafe
    have hleft := ihL (SourceTerm.eq_lhs hsource) hborrowSafe
    have hghostSafe :
        BorrowSafeEnv
          (_env₂.update _ghost { ty := .ty _lhsTy, lifetime := _lifetime }) :=
      borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv hleft.1 hleft.2
    have hright := ihGhost (SourceTerm.eq_rhs hsource) hghostSafe
    exact ⟨by simpa [henvEq] using (BorrowSafeEnv.erase (ghost := _ghost) hright.1),
      tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_bool⟩
  case ite =>
    intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
      _trueBranch _falseBranch _trueTy _falseTy _joinTy _hcondition _htrue
      _hfalse _hjoin _henvJoin _hsameLeft _hsameRight _hwellJoin
      _hcoherent _hlinear hborrowSafeJoin hresultSafe ihCondition ihTrue
      ihFalse hsource hborrowSafe
    have hconditionSafe := ihCondition (SourceTerm.ite_condition hsource) hborrowSafe
    have _htrueSafe := ihTrue (SourceTerm.ite_trueBranch hsource) hconditionSafe.1
    have _hfalseSafe := ihFalse (SourceTerm.ite_falseBranch hsource) hconditionSafe.1
    exact ⟨hborrowSafeJoin, hresultSafe⟩
  case iteDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition _trueBranch
      _falseBranch _trueTy _falseTy _hcondition _htrue _hfalse _hdiverges
      ihCondition ihTrue _ihFalse hsource hborrowSafe
    have hconditionSafe :=
      ihCondition (SourceTerm.ite_condition hsource) hborrowSafe
    exact ihTrue (SourceTerm.ite_trueBranch hsource) hconditionSafe.1
  case whileLoopDiverging =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition _body
      _bodyTy _hchild _hcond _hbody _hdiverges ihCond _ihBody hsource
      hborrowSafe
    exact ⟨(ihCond (SourceTerm.while_condition hsource) hborrowSafe).1,
      tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit⟩
  case whileLoop =>
    intro _env₁ _envBack _envInv _env₂ _envEntry₂ _env₃ _envEntry₃ _typing
      _lifetime _bodyLifetime _condition _body _bodyTy _bodyEntryTy _hchild
      _hjoin _hss1 _hss2 _hcbwf _hcoh _hlin hbse _hnameFresh _hcondInv _hbodyInv _hwellTy
      _hdrop _hcondEntry _hbodyEntry ihCondInv _ihBodyInv _ihCondEntry
      _ihBodyEntry hsource _hborrowSafe
    exact ⟨(ihCondInv (SourceTerm.while_condition hsource) hbse).1,
      tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit⟩
  case singleton =>
    intro _env₁ _env₂ _typing _lifetime _term _ty _hterm _ih hsource
      hborrowSafe
    have h := _ih (SourceTerm.block_head hsource) hborrowSafe
    exact h
  case cons =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
      _hterm _hrest _ihHead _ihRest hsource hborrowSafe
    have hhead := _ihHead (SourceTerm.block_head hsource) hborrowSafe
    exact _ihRest (SourceTerm.block_tail hsource) hhead.1

end Paper
end LwRust
