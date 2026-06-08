import LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety

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

Status: the core output-environment statement is proved for the strengthened
rule-carried formulation.  The borrow-safety `EnvWrite` frame obligation is now
proved constructively with the root-independent RHS `TyBorrowSafeAgainstEnv`
invariant and the strengthened RHS/RHS fan-out side condition carried by
`T-Assign`.  The global mutual term/list induction is source-scoped: `T-Const`
only handles source values, whose types are borrow-free.  Move result-extension
is proved constructively from the `LValTyping`/`Strike` origin lemma.  Blocks are
handled by the global term/list induction, which carries that same
root-independent result-type invariant through `dropLifetime`.
-/

namespace LwRust
namespace Paper

open Core


/-! ## Section 4.5.1: Borrow Safety -/

/--
Definition 4.13, borrow-safe environment.

The paper phrases this over variables in `dom(Γ)` and borrowed lvals inside
contained borrow types.  The containment premises already imply the relevant
variables are present in the environment.
-/
def BorrowSafeEnv (env : Env) : Prop :=
  ∀ x y mutable targetsMutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ (&mut targetsMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    x = y

def TyBorrowFree (ty : Ty) : Prop :=
  ∀ mutable targets, ¬ PartialTyContains (.ty ty) (.borrow mutable targets)

def PartialTyBorrowFree (ty : PartialTy) : Prop :=
  ∀ mutable targets, ¬ PartialTyContains ty (.borrow mutable targets)

theorem partialTyContains_borrow_iff_eq {mutable : Bool} {targets : List LVal}
    {needle : Ty} :
    PartialTyContains (.ty (.borrow mutable targets)) needle ↔
      Ty.borrow mutable targets = needle := by
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

@[simp] theorem tyBorrowFree_box {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowFree (.box ty) := by
  intro hfree mutable targets hcontains
  cases hcontains with
  | tyBox hinner =>
      exact hfree mutable targets hinner

theorem partialTyBorrowFree_box_inv {ty : PartialTy} :
    PartialTyBorrowFree (.box ty) →
    PartialTyBorrowFree ty := by
  intro hfree mutable targets hcontains
  exact hfree mutable targets (PartialTyContains.box hcontains)

/-- A borrow-free fresh slot cannot be the root of a borrow-typed lval.

This discharges the fresh-root half of `FreshUpdateCoherenceObligations` for
borrow-free declarations/results.  The old-root transport half is separate:
borrow typings rooted in existing variables may dereference old borrow targets,
and transporting those target-list typings back to the old environment is the
explicit old-root transport condition.
-/
theorem LValTyping.update_fresh_root_partialTyBorrowFree {env : Env} {x : Name}
    {ty : Ty} {slotLifetime : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {valueLifetime : Lifetime} :
    TyBorrowFree ty →
    LVal.base lv = x →
    LValTyping (env.update x { ty := .ty ty, lifetime := slotLifetime })
      lv partialTy valueLifetime →
    PartialTyBorrowFree partialTy := by
  intro hfree hbase htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _valueLifetime _ =>
      LVal.base lv = x → PartialTyBorrowFree partialTy)
    (motive_2 := fun _targets _partialTy _valueLifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping hbase
  · intro y envSlot hslot hbase
    have hy : y = x := by simpa [LVal.base] using hbase
    subst hy
    have hslotEq :
        envSlot = { ty := PartialTy.ty ty, lifetime := slotLifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := slotLifetime } = envSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    exact partialTyBorrowFree_ty hfree
  · intro lv inner lifetime _hsource ih hbase
    exact partialTyBorrowFree_box_inv (ih (by simpa [LVal.base] using hbase))
  · intro lv mutable targets borrowLifetime targetLifetime targetTy _hborrow _htargets
      ihBorrow _ihTargets hbase
    have hsourceFree :
        PartialTyBorrowFree (.ty (.borrow mutable targets)) :=
      ihBorrow (by simpa [LVal.base] using hbase)
    exact False.elim (hsourceFree mutable targets PartialTyContains.here)
  · intro target ty lifetime _htarget _ih
    trivial
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

theorem LValTyping.update_fresh_root_not_borrow_of_tyBorrowFree {env : Env}
    {x : Name} {ty : Ty} {slotLifetime : Lifetime} {lv : LVal}
    {mutable : Bool} {targets : List LVal} {borrowLifetime : Lifetime} :
    TyBorrowFree ty →
    LVal.base lv = x →
    ¬ LValTyping (env.update x { ty := .ty ty, lifetime := slotLifetime })
      lv (.ty (.borrow mutable targets)) borrowLifetime := by
  intro hfree hbase htyping
  have hpartialFree :=
    LValTyping.update_fresh_root_partialTyBorrowFree hfree hbase htyping
  exact hpartialFree mutable targets PartialTyContains.here

/-- Borrow-free fresh-update coherence, with only old-root transport left open.

For fresh-root lvals the declared type contains no borrows, so a borrow-typed
lval rooted at the fresh variable is impossible.  Callers still have to supply
the old-root transport fact, which is the nontrivial part for lvals rooted in the
pre-existing environment.
-/
theorem FreshUpdateCoherenceObligations.of_tyBorrowFree
    {env : Env} {x : Name} {ty : Ty} {lifetime : Lifetime} :
    TyBorrowFree ty →
    (∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LVal.base lv ≠ x →
      LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
        lv (.ty (.borrow mutable targets)) borrowLifetime →
      ∃ oldBorrowLifetime,
        LValTyping env lv (.ty (.borrow mutable targets)) oldBorrowLifetime) →
    FreshUpdateCoherenceObligations env x ty lifetime := by
  intro hfree holdTransport
  refine ⟨?_, ?_⟩
  · intro lv mutable targets borrowLifetime hbase htyping
    exact holdTransport hbase htyping
  · intro lv mutable targets borrowLifetime hbase htyping
    exact False.elim
      (LValTyping.update_fresh_root_not_borrow_of_tyBorrowFree hfree hbase htyping)

theorem not_tyBorrowFree_borrow (mutable : Bool) (targets : List LVal) :
    ¬ TyBorrowFree (.borrow mutable targets) := by
  intro hfree
  exact hfree mutable targets PartialTyContains.here

@[simp] theorem borrowSafeEnv_empty :
    BorrowSafeEnv Env.empty := by
  intro x y mutable targetsMutable targetsOther targetMutable targetOther hcontains _ _ _ _
  rcases hcontains with ⟨slot, hslot, _hcontainsTy⟩
  simp [Env.empty] at hslot

theorem EnvContains.update_fresh_ne {env : Env} {x y : Name} {slot : EnvSlot}
    {ty : Ty} :
    y ≠ x →
    (env.update x slot) ⊢ y ↝ ty →
    env ⊢ y ↝ ty := by
  intro hy hcontains
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  exact ⟨containedSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩

theorem EnvContains.update_box_borrow_to_inner {env : Env} {gamma x : Name}
    {ty : Ty} {lifetime : Lifetime} {mutable : Bool} {targets : List LVal} :
    (env.update gamma { ty := .ty (.box ty), lifetime := lifetime }) ⊢ x ↝
      (Ty.borrow mutable targets) →
    (env.update gamma { ty := .ty ty, lifetime := lifetime }) ⊢ x ↝
      (Ty.borrow mutable targets) := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hx : x = gamma
  · subst hx
    have hslotEq :
        slot = { ty := PartialTy.ty (.box ty), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (.box ty), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    cases hcontainsTy with
    | tyBox hinner =>
        exact ⟨{ ty := PartialTy.ty ty, lifetime := lifetime },
          by simp [Env.update], hinner⟩
  · exact ⟨slot, by simpa [Env.update, hx] using hslot, hcontainsTy⟩

theorem pathConflicts_symm {left right : LVal} :
    left ⋈ right →
    right ⋈ left := by
  intro h
  exact h.symm

theorem partialTyContains_borrow_injective {partialTy : PartialTy}
    {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal} :
    PartialTyContains partialTy (.borrow mutable₁ targets₁) →
    PartialTyContains partialTy (.borrow mutable₂ targets₂) →
    mutable₁ = mutable₂ ∧ targets₁ = targets₂ := by
  revert mutable₁ mutable₂ targets₁ targets₂
  refine PartialTy.rec
    (motive_1 := fun ty =>
      ∀ {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal},
        PartialTyContains (.ty ty) (.borrow mutable₁ targets₁) →
        PartialTyContains (.ty ty) (.borrow mutable₂ targets₂) →
        mutable₁ = mutable₂ ∧ targets₁ = targets₂)
    (motive_2 := fun partialTy =>
      ∀ {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal},
        PartialTyContains partialTy (.borrow mutable₁ targets₁) →
        PartialTyContains partialTy (.borrow mutable₂ targets₂) →
        mutable₁ = mutable₂ ∧ targets₁ = targets₂)
    ?unit ?int ?borrow ?boxTy ?ty ?boxPartial ?undef partialTy
  · intro mutable₁ mutable₂ targets₁ targets₂ hleft
    cases hleft
  · intro mutable₁ mutable₂ targets₁ targets₂ hleft
    cases hleft
  · intro mutable targets mutable₁ mutable₂ targets₁ targets₂ hleft hright
    cases hleft with
    | here =>
        cases hright with
        | here =>
            exact ⟨rfl, rfl⟩
  · intro inner ih mutable₁ mutable₂ targets₁ targets₂ hleft hright
    cases hleft with
    | tyBox hleftInner =>
        cases hright with
        | tyBox hrightInner =>
            exact ih hleftInner hrightInner
  · intro ty ih mutable₁ mutable₂ targets₁ targets₂ hleft hright
    exact ih hleft hright
  · intro inner ih mutable₁ mutable₂ targets₁ targets₂ hleft hright
    cases hleft with
    | box hleftInner =>
        cases hright with
        | box hrightInner =>
            exact ih hleftInner hrightInner
  · intro shape _ih mutable₁ mutable₂ targets₁ targets₂ hleft
    cases hleft

theorem partialTyContains_mut_imm_false {partialTy : PartialTy}
    {mutableTargets immTargets : List LVal} :
    PartialTyContains partialTy (.borrow true mutableTargets) →
    PartialTyContains partialTy (.borrow false immTargets) →
    False := by
  intro hmut himm
  rcases partialTyContains_borrow_injective hmut himm with ⟨hbool, _htargets⟩
  cases hbool

theorem not_envContains_update_fresh_same_of_borrowFree {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} {borrowTy : Ty} :
    TyBorrowFree ty →
    borrowTy = .borrow mutable targets →
    ¬ (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢ x ↝ borrowTy := by
  intro hborrowFree hborrowTy hcontains
  subst hborrowTy
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  have hslotEq :
      containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
    have h :
        { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
      simpa [Env.update] using hslot
    exact h.symm
  subst hslotEq
  exact hborrowFree mutable targets hcontainsTy

theorem borrowSafeEnv_update_partialBorrowFree {env : Env} {x : Name}
    {slot : EnvSlot} :
    BorrowSafeEnv env →
    PartialTyBorrowFree slot.ty →
    BorrowSafeEnv (env.update x slot) := by
  intro hsafe hborrowFree y z mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hy : y = x
  · have hcontainsMutableAtX :
        (env.update x slot) ⊢ x ↝ Ty.borrow true targetsMutable := by
      simpa [hy] using hcontainsMutable
    exact False.elim
      (by
        rcases hcontainsMutableAtX with ⟨containedSlot, hslot, hcontainsTy⟩
        have hslotEq : containedSlot = slot := by
          have h : slot = containedSlot := by
            simpa [Env.update] using hslot
          exact h.symm
        subst hslotEq
        exact hborrowFree true targetsMutable hcontainsTy)
  · by_cases hz : z = x
    · have hcontainsOtherAtX :
          (env.update x slot) ⊢ x ↝ Ty.borrow mutable targetsOther := by
        simpa [hz] using hcontainsOther
      exact False.elim
        (by
          rcases hcontainsOtherAtX with ⟨containedSlot, hslot, hcontainsTy⟩
          have hslotEq : containedSlot = slot := by
            have h : slot = containedSlot := by
              simpa [Env.update] using hslot
            exact h.symm
          subst hslotEq
          exact hborrowFree mutable targetsOther hcontainsTy)
    · exact hsafe y z mutable targetsMutable targetsOther targetMutable targetOther
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

/-- A result type is borrow-safe against an environment when installing it as a
new root would introduce no borrow-target conflict with any existing root.

This is the root-independent part of result-extension.  It avoids relying on
the existence of a globally fresh name, which is especially important for block
results: a name can be fresh after `dropLifetime` precisely because a block-local
slot with that name was removed. -/
def TyBorrowSafeAgainstEnv (env : Env) (ty : Ty) : Prop :=
  (∀ targetsMutable mutable targetsOther x targetMutable targetOther,
    PartialTyContains (.ty ty) (.borrow true targetsMutable) →
    env ⊢ x ↝ Ty.borrow mutable targetsOther →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False) ∧
  (∀ x targetsMutable mutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ Ty.borrow true targetsMutable →
    PartialTyContains (.ty ty) (.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False)

theorem tyBorrowSafeAgainstEnv_borrowFree {env : Env} {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowSafeAgainstEnv env ty := by
  intro hfree
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      _hother _htargetMutable _htargetOther _hconflict
    exact hfree true targetsMutable hcontains
  · intro x targetsMutable mutable targetsOther targetMutable targetOther _hcontainsMutable
      hcontains _htargetMutable _htargetOther _hconflict
    exact hfree mutable targetsOther hcontains

theorem TyBorrowSafeAgainstEnv.dropLifetime {env : Env} {ty : Ty}
    {lifetime : Lifetime} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv (env.dropLifetime lifetime) ty := by
  intro hsafeTy
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      hother htargetMutable htargetOther hconflict
    exact hsafeTy.1 targetsMutable mutable targetsOther x targetMutable targetOther
      hcontains (EnvContains.dropLifetime_of_contains hother)
      htargetMutable htargetOther hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther hcontainsMutable
      hcontains htargetMutable htargetOther hconflict
    exact hsafeTy.2 x targetsMutable mutable targetsOther targetMutable targetOther
      (EnvContains.dropLifetime_of_contains hcontainsMutable) hcontains
      htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env ty →
    BorrowSafeEnv (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hsafeTy a b mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases ha : a = x
  · subst a
    have hcontainsMutableAtX :
        (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢
          x ↝ Ty.borrow true targetsMutable := by
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
        (hsafeTy.1 targetsMutable mutable targetsOther b targetMutable targetOther
          hcontainsTy
          (EnvContains.update_fresh_ne hb hcontainsOther)
          htargetMutable htargetOther hconflict)
  · by_cases hb : b = x
    · subst b
      have hcontainsOtherAtX :
          (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢
            x ↝ Ty.borrow mutable targetsOther := by
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
        (hsafeTy.2 a targetsMutable mutable targetsOther targetMutable targetOther
          (EnvContains.update_fresh_ne ha hcontainsMutable)
          hcontainsTy htargetMutable htargetOther hconflict)
    · exact hsafe a b mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne ha hcontainsMutable)
        (EnvContains.update_fresh_ne hb hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_of_update_fresh {env : Env} {x : Name} {slot : EnvSlot} :
    env.fresh x →
    BorrowSafeEnv (env.update x slot) →
    BorrowSafeEnv env := by
  intro hfresh hsafe y z mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe y z mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.update_fresh_of_old hfresh hcontainsMutable)
    (EnvContains.update_fresh_of_old hfresh hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafeEnv_move_var {env env' : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.slotAt x = some { ty := .ty ty, lifetime := lifetime } →
    EnvMove env (.var x) env' →
    BorrowSafeEnv env' := by
  intro hsafe hslot hmove
  rcases hmove with ⟨slot, struck, hbaseSlot, hstrike, henv'⟩
  simp [LVal.base, LVal.path] at hbaseSlot hstrike henv'
  rw [hslot] at hbaseSlot
  injection hbaseSlot with hslotEq
  subst hslotEq
  cases struck with
  | ty struckTy =>
      cases hstrike
  | box struckInner =>
      cases hstrike
  | undef shape =>
      have hshape : ty = shape := hstrike
      subst hshape
      rw [henv']
      exact borrowSafeEnv_update_partialBorrowFree hsafe
        (partialTyBorrowFree_undef ty)

theorem borrowSafeEnv_dropLifetime {env : Env} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    BorrowSafeEnv (env.dropLifetime lifetime) := by
  intro hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
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

theorem borrowSafeEnv_dropLifetime_update_of_update {env : Env} {x : Name}
    {slot : EnvSlot} {dropped : Lifetime} :
    slot.lifetime ≠ dropped →
    BorrowSafeEnv (env.update x slot) →
    BorrowSafeEnv ((env.dropLifetime dropped).update x slot) := by
  intro hslotLifetime hsafe
  have hdropSafe :
      BorrowSafeEnv ((env.update x slot).dropLifetime dropped) :=
    borrowSafeEnv_dropLifetime hsafe
  rwa [Env.dropLifetime_update_ne hslotLifetime] at hdropSafe

theorem borrowSafeEnv_block_result_extension_of_body_extension {env₂ env₃ : Env}
    {lifetime blockLifetime : Lifetime} {ty : Ty} {gamma : Name} :
    LifetimeChild lifetime blockLifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) →
    BorrowSafeEnv (env₃.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hchild hdrop hbodySafe
  rw [hdrop]
  exact borrowSafeEnv_dropLifetime_update_of_update
    (x := gamma)
    (slot := { ty := .ty ty, lifetime := lifetime })
    (by
      intro hEq
      exact LifetimeChild.ne hchild hEq)
    hbodySafe

theorem LValTyping.no_readProhibited_targets_of_immBorrow {env : Env} :
    BorrowSafeEnv env →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {borrowTargets},
        PartialTyContains partialTy (.borrow false borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ ReadProhibited env target) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {borrowTargets},
        PartialTyContains partialTy (.borrow false borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ ReadProhibited env target) := by
  intro hsafe
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (motive_2 := fun targets partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (by
        intro x slot hslot borrowTargets hcontains target htarget hread
        rcases hread with
          ⟨borrower, mutableTargets, mutableTarget, hmutableContains,
            hmutableTarget, hconflict⟩
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
              mutableTarget target
              hmutableContains
              ⟨slot, hslot, hcontains⟩
              hmutableTarget
              htarget
              hconflict
          exact hsame hsafeContradiction)
      (by
        intro _lv _inner _lifetime _htyping ih borrowTargets hcontains target
          htarget hread
        exact ih (PartialTyContains.box hcontains) target htarget hread)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets borrowTargets hcontains target
          htarget hread
        exact ihTargets hcontains target htarget hread)
      (by
        intro target ty lifetime _htarget ihTarget borrowTargets hcontains selected
          hselected hread
        exact ihTarget hcontains selected hselected hread)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion _hintersection ihHead ihRest borrowTargets hcontains
          selected hselected hread
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
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (motive_2 := fun targets partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (by
        intro x slot hslot borrowTargets hcontains target htarget hread
        rcases hread with
          ⟨borrower, mutableTargets, mutableTarget, hmutableContains,
            hmutableTarget, hconflict⟩
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
              mutableTarget target
              hmutableContains
              ⟨slot, hslot, hcontains⟩
              hmutableTarget
              htarget
              hconflict
          exact hsame hsafeContradiction)
      (by
        intro _lv _inner _lifetime _htyping ih borrowTargets hcontains target
          htarget hread
        exact ih (PartialTyContains.box hcontains) target htarget hread)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets borrowTargets hcontains target
          htarget hread
        exact ihTargets hcontains target htarget hread)
      (by
        intro target ty lifetime _htarget ihTarget borrowTargets hcontains selected
          hselected hread
        exact ihTarget hcontains selected hselected hread)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion _hintersection ihHead ihRest borrowTargets hcontains
          selected hselected hread
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead hread
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest hread)
      htyping

theorem borrowSafeEnv_update_fresh_mutBorrow {env : Env} {gamma : Name}
    {lv : LVal} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    ¬ WriteProhibited env lv →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) := by
  intro hsafe _hfresh hnotWrite x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq : Ty.borrow true [lv] = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    injection hborrowEq with _hmut htargetsMutable
    subst htargetsMutable
    have htargetMutableEq : targetMutable = lv := by
      simpa using htargetMutable
    have hconflictLv : lv ⋈ targetOther := by
      simpa [htargetMutableEq] using hconflict
    by_cases hy : y = gamma
    · exact hx.trans hy.symm
    · have hcontainsOtherOld : env ⊢ y ↝ Ty.borrow mutable targetsOther :=
        EnvContains.update_fresh_ne hy hcontainsOther
      have hwrite : WriteProhibited env lv := by
        cases mutable with
        | false =>
            exact Or.inr ⟨y, targetsOther, targetOther, hcontainsOtherOld,
              htargetOther, pathConflicts_symm hconflictLv⟩
        | true =>
            exact Or.inl ⟨y, targetsOther, targetOther, hcontainsOtherOld,
              htargetOther, pathConflicts_symm hconflictLv⟩
      exact False.elim (hnotWrite hwrite)
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq : Ty.borrow true [lv] = Ty.borrow mutable targetsOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargetsOther
      subst htargetsOther
      have htargetOtherEq : targetOther = lv := by
        simpa using htargetOther
      have hconflictLv : targetMutable ⋈ lv := by
        simpa [htargetOtherEq] using hconflict
      have hcontainsMutableOld : env ⊢ x ↝ Ty.borrow true targetsMutable :=
        EnvContains.update_fresh_ne hx hcontainsMutable
      have hwrite : WriteProhibited env lv :=
        Or.inl ⟨x, targetsMutable, targetMutable, hcontainsMutableOld,
          htargetMutable, hconflictLv⟩
      exact False.elim (hnotWrite hwrite)
    · exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_fresh_immBorrow {env : Env} {gamma : Name}
    {lv : LVal} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    ¬ ReadProhibited env lv →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) := by
  intro hsafe hfresh hnotRead x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq :
        Ty.borrow false [lv] = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    cases hborrowEq
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq :
          Ty.borrow false [lv] = Ty.borrow mutable targetsOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargets
      have htargetOtherEq : targetOther = lv := by
        cases htargets
        simpa using htargetOther
      subst htargetOtherEq
      exact False.elim (hnotRead ⟨x, targetsMutable, targetMutable,
        EnvContains.update_fresh_ne hx hcontainsMutable,
        htargetMutable,
        hconflict⟩)
    · exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_fresh_immBorrowMany {env : Env} {gamma : Name}
    {targets : List LVal} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    (∀ target, target ∈ targets → ¬ ReadProhibited env target) →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow false targets), lifetime := lifetime }) := by
  intro hsafe hfresh hnotRead x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow false targets), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq :
        Ty.borrow false targets = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    cases hborrowEq
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow false targets), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq :
          Ty.borrow false targets = Ty.borrow mutable targetsOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargets
      subst htargets
      exact False.elim
        (hnotRead targetOther htargetOther
          ⟨x, targetsMutable, targetMutable,
            EnvContains.update_fresh_ne hx hcontainsMutable,
            htargetMutable,
            hconflict⟩)
    · exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem tyBorrowSafeAgainstEnv_mutBorrow {env : Env} {lv : LVal} :
    ¬ WriteProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow true [lv]) := by
  intro hnotWrite
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      hother htargetMutable htargetOther hconflict
    have hborrowEq : Ty.borrow true [lv] = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmut htargetsMutable
    subst htargetsMutable
    have htargetMutableEq : targetMutable = lv := by
      simpa using htargetMutable
    have hconflictLv : lv ⋈ targetOther := by
      simpa [htargetMutableEq] using hconflict
    have hwrite : WriteProhibited env lv := by
      cases mutable with
      | false =>
          exact Or.inr ⟨x, targetsOther, targetOther, hother,
            htargetOther, pathConflicts_symm hconflictLv⟩
      | true =>
          exact Or.inl ⟨x, targetsOther, targetOther, hother,
            htargetOther, pathConflicts_symm hconflictLv⟩
    exact hnotWrite hwrite
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable hcontains htargetMutable htargetOther hconflict
    have hborrowEq : Ty.borrow true [lv] = Ty.borrow mutable targetsOther :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmutable htargetsOther
    subst htargetsOther
    have htargetOtherEq : targetOther = lv := by
      simpa using htargetOther
    have hconflictLv : targetMutable ⋈ lv := by
      simpa [htargetOtherEq] using hconflict
    exact hnotWrite
      (Or.inl ⟨x, targetsMutable, targetMutable, hcontainsMutable,
        htargetMutable, hconflictLv⟩)

theorem tyBorrowSafeAgainstEnv_immBorrowMany {env : Env} {targets : List LVal} :
    (∀ target, target ∈ targets → ¬ ReadProhibited env target) →
    TyBorrowSafeAgainstEnv env (.borrow false targets) := by
  intro hnotRead
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      _hother _htargetMutable _htargetOther _hconflict
    have hborrowEq :
        Ty.borrow false targets = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontains
    cases hborrowEq
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable hcontains htargetMutable htargetOther hconflict
    have hborrowEq :
        Ty.borrow false targets = Ty.borrow mutable targetsOther :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmutable htargets
    subst htargets
    exact hnotRead targetOther htargetOther
      ⟨x, targetsMutable, targetMutable, hcontainsMutable,
        htargetMutable, hconflict⟩

theorem tyBorrowSafeAgainstEnv_immBorrow {env : Env} {lv : LVal} :
    ¬ ReadProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow false [lv]) := by
  intro hnotRead
  exact tyBorrowSafeAgainstEnv_immBorrowMany
    (by
      intro target htarget
      have htargetEq : target = lv := by
        simpa using htarget
      subst htargetEq
      exact hnotRead)

theorem PartialTyContains.tyBox_borrow_inv {inner : Ty} {mutable : Bool}
    {targets : List LVal} :
    PartialTyContains (.ty (.box inner)) (.borrow mutable targets) →
    PartialTyContains (.ty inner) (.borrow mutable targets) := by
  intro hcontains
  cases hcontains with
  | tyBox hinner => exact hinner

theorem TyBorrowSafeAgainstEnv.box {env : Env} {ty : Ty} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv env (.box ty) := by
  intro hsafeTy
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      hother htargetMutable htargetOther hconflict
    exact hsafeTy.1 targetsMutable mutable targetsOther x targetMutable targetOther
      (PartialTyContains.tyBox_borrow_inv hcontains) hother
      htargetMutable htargetOther hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther hcontainsMutable
      hcontains htargetMutable htargetOther hconflict
    exact hsafeTy.2 x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable (PartialTyContains.tyBox_borrow_inv hcontains)
      htargetMutable htargetOther hconflict

theorem borrowSafety_immBorrow_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow false lv) (.borrow false [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) := by
  intro hsafe htyping hfresh
  cases htyping with
  | immBorrow _hLv _hvar hnotRead =>
      exact borrowSafeEnv_update_fresh_immBorrow hsafe hfresh hnotRead

theorem borrowSafety_mutBorrow_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow true lv) (.borrow true [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) := by
  intro hsafe htyping hfresh
  cases htyping with
  | mutBorrow _hLv _hvar _hmutable hnotWrite =>
      exact borrowSafeEnv_update_fresh_mutBorrow hsafe hfresh hnotWrite

/--
Borrow-free result extension with the fresh-coherence gap exposed.

The fresh-root coherence case is discharged by `TyBorrowFree`; the only
remaining well-formedness premise is old-root transport for borrow typings in
the extended environment.  This is the proof-carrying replacement shape for the
legacy `borrowSafety_result_extension_borrowFree` below.
-/
theorem borrowSafety_result_extension_borrowFree_of_oldRootTransport {env : Env}
    {gamma : Name} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env.fresh gamma →
    (∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LVal.base lv ≠ gamma →
      LValTyping (env.update gamma { ty := .ty ty, lifetime := lifetime })
        lv (.ty (.borrow mutable targets)) borrowLifetime →
      ∃ oldBorrowLifetime,
        LValTyping env lv (.ty (.borrow mutable targets)) oldBorrowLifetime) →
    WellFormedEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hwellFormed hwellTy hborrowSafe hborrowFree hfresh holdTransport
  exact ⟨
    borrowInvariance_result_extension_of_coherenceObligations
      hwellFormed hwellTy hfresh
      (FreshUpdateCoherenceObligations.of_tyBorrowFree hborrowFree holdTransport),
    borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree⟩

/--
Corollary 4.14 support: extending the output environment with a fresh,
borrow-free result slot preserves both well-formedness and borrow safety.

The remaining borrow-safety work is the paper's typing-rule induction showing
that the output environment of a well-typed term is itself borrow safe.  This
theorem packages the final result-extension step from the corollary.

This is a legacy shortcut: its well-formedness half goes through
`borrowInvariance_result_extension`, which depends on `Coherent.update_fresh_ty`.
Use `borrowSafety_result_extension_borrowFree_of_oldRootTransport` when the
old-root transport obligation is available.
-/
theorem borrowSafety_result_extension_borrowFree {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env.fresh gamma →
    FreshUpdateCoherenceObligations env gamma ty lifetime →
    WellFormedEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hwellFormed hwellTy hborrowSafe hborrowFree hfresh hfreshCoherence
  exact ⟨borrowInvariance_result_extension hwellFormed hwellTy hfresh hfreshCoherence,
    borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree⟩

theorem borrowSafeEnv_update_box_of_update_inner {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) →
    BorrowSafeEnv (env.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.update_box_borrow_to_inner hcontainsMutable)
    (EnvContains.update_box_borrow_to_inner hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafety_result_extension_box_of_inner {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) →
    env.fresh gamma →
    FreshUpdateCoherenceObligations env gamma (.box ty) lifetime →
    WellFormedEnv (env.update gamma { ty := .ty (.box ty), lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro hwellFormed hwellTy hinnerSafe hfresh hfreshCoherence
  exact ⟨borrowInvariance_result_extension hwellFormed
      (WellFormedTy.box hwellTy) hfresh hfreshCoherence,
    borrowSafeEnv_update_box_of_update_inner hinnerSafe⟩

/--
Corollary 4.14, `T-Const` case: typing a value does not change the environment,
so borrow safety of the result extension follows from the borrow-free shape of
the result type.
-/
theorem borrowSafety_value_result_extension_borrowFree {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty}
    {gamma : Name} :
    TermTyping env typing lifetime (.val value) ty env₂ →
    WellFormedEnv env lifetime →
    WellFormedTy env₂ ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro htyping hwellFormed hwellTy hborrowSafe hborrowFree hfresh hfreshCoherence
  have henv : env = env₂ := valueTyping_environment_eq htyping
  subst henv
  exact borrowSafety_result_extension_borrowFree hwellFormed hwellTy hborrowSafe
    hborrowFree hfresh hfreshCoherence

theorem borrowSafe_value_result_extension_borrowFree {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty}
    {gamma : Name} :
    TermTyping env typing lifetime (.val value) ty env₂ →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro htyping hborrowSafe hborrowFree hfresh
  have henv : env = env₂ := valueTyping_environment_eq htyping
  subst henv
  exact borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree

/-! ## Source-Level Initial States -/

def SourceValue : Value → Prop
  | .unit => True
  | .int _ => True
  | .ref _ => False

def SourceTerm (term : Term) : Prop :=
  ∀ value, value ∈ termValues term → SourceValue value

theorem SourceTerm.block_head {lifetime : Lifetime} {term : Term}
    {rest : List Term} :
    SourceTerm (.block lifetime (term :: rest)) →
    SourceTerm term := by
  intro hsource value hmem
  exact hsource value
    (by
      simp [termValues, hmem])

theorem SourceTerm.block_tail {lifetime : Lifetime} {term : Term}
    {rest : List Term} :
    SourceTerm (.block lifetime (term :: rest)) →
    SourceTerm (.block lifetime rest) := by
  intro hsource value hmem
  exact hsource value
    (by
      simp [termValues] at hmem ⊢
      exact Or.inr hmem)

theorem SourceTerm.box_inner {term : Term} :
    SourceTerm (.box term) →
    SourceTerm term := by
  intro hsource value hmem
  exact hsource value (by simpa [termValues] using hmem)

theorem SourceTerm.declare_inner {x : Name} {term : Term} :
    SourceTerm (.letMut x term) →
    SourceTerm term := by
  intro hsource value hmem
  exact hsource value (by simpa [termValues] using hmem)

theorem SourceTerm.assign_inner {lhs : LVal} {rhs : Term} :
    SourceTerm (.assign lhs rhs) →
    SourceTerm rhs := by
  intro hsource value hmem
  exact hsource value (by simpa [termValues] using hmem)

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

This is the static origin fact needed for non-variable move result-extension.
The proof follows the lvalue spine.  Box dereferences push the obligation one
selector back toward the base slot; borrow dereferences are impossible because
`Strike` cannot continue below a full borrow leaf. -/
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
    {mutable : Bool} {targets : List LVal} :
    EnvMove env lv env' →
    ¬ env' ⊢ LVal.base lv ↝ Ty.borrow mutable targets := by
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
  intro hsafe hmove x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.of_move hmove hcontainsMutable)
    (EnvContains.of_move hmove hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafety_move_borrowFree_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {ty : Ty}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    TyBorrowFree ty →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe htyping hborrowFree
  cases htyping with
  | move _hLv _hvar _hnotWrite hmove =>
      exact borrowSafeEnv_update_fresh_borrowFree
        (borrowSafeEnv_move hsafe hmove) hborrowFree

/-- Result-extension after a move, factored around the one remaining typing
origin fact.

If every borrow contained in the moved result type was contained in the moved
base slot before the move, then adding the moved value as a fresh result root is
borrow safe.  Any old root that conflicts with the fresh result must have been
the moved base by `BorrowSafeEnv env`; but the moved environment no longer
contains live borrows at that base.
-/
theorem borrowSafeEnv_move_result_extension_of_base_contains {env env₂ : Env}
    {lv : LVal} {ty : Ty} {gamma : Name} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    EnvMove env lv env₂ →
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      env ⊢ LVal.base lv ↝ Ty.borrow mutable targets) →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hmove hbaseContains _hfresh a b mutable targetsMutable targetsOther
    targetMutable targetOther hcontainsMutable hcontainsOther htargetMutable
    htargetOther hconflict
  by_cases ha : a = gamma
  · subst a
    have hcontainsMutableAtGamma :
        (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hslotEq :
        containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
        simpa [Env.update] using hcontainedSlot
      exact h.symm
    subst hslotEq
    by_cases hb : b = gamma
    · exact hb.symm
    · have hcontainsOtherMove :
          env₂ ⊢ b ↝ Ty.borrow mutable targetsOther :=
        EnvContains.update_fresh_ne hb hcontainsOther
      by_cases hbBase : b = LVal.base lv
      · subst hbBase
        exact False.elim (EnvContains.move_base_same_false hmove hcontainsOtherMove)
      · have hcontainsOtherOld :
            env ⊢ b ↝ Ty.borrow mutable targetsOther :=
          EnvContains.of_move hmove hcontainsOtherMove
        have hbaseEq :
            LVal.base lv = b :=
          hsafe (LVal.base lv) b mutable targetsMutable targetsOther targetMutable
            targetOther
            (hbaseContains true targetsMutable hcontainsTy)
            hcontainsOtherOld
            htargetMutable htargetOther hconflict
        exact False.elim (hbBase hbaseEq.symm)
  · by_cases hb : b = gamma
    · subst b
      have hcontainsOtherAtGamma :
          (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hslotEq :
          containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
          simpa [Env.update] using hcontainedSlot
        exact h.symm
      subst hslotEq
      have hcontainsMutableMove :
          env₂ ⊢ a ↝ Ty.borrow true targetsMutable :=
        EnvContains.update_fresh_ne ha hcontainsMutable
      by_cases haBase : a = LVal.base lv
      · subst haBase
        exact False.elim (EnvContains.move_base_same_false hmove hcontainsMutableMove)
      · have hcontainsMutableOld :
            env ⊢ a ↝ Ty.borrow true targetsMutable :=
          EnvContains.of_move hmove hcontainsMutableMove
        have hbaseEq :
            a = LVal.base lv :=
          hsafe a (LVal.base lv) mutable targetsMutable targetsOther targetMutable
            targetOther hcontainsMutableOld
            (hbaseContains mutable targetsOther hcontainsTy)
            htargetMutable htargetOther hconflict
        exact False.elim (haBase hbaseEq)
    · exact borrowSafeEnv_move hsafe hmove a b mutable targetsMutable targetsOther
        targetMutable targetOther
        (EnvContains.update_fresh_ne ha hcontainsMutable)
        (EnvContains.update_fresh_ne hb hcontainsOther)
        htargetMutable htargetOther hconflict

theorem tyBorrowSafeAgainstEnv_move_of_base_contains {env env₂ : Env}
    {lv : LVal} {ty : Ty} :
    BorrowSafeEnv env →
    EnvMove env lv env₂ →
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      env ⊢ LVal.base lv ↝ Ty.borrow mutable targets) →
    TyBorrowSafeAgainstEnv env₂ ty := by
  intro hsafe hmove hbaseContains
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontainsTy
      hcontainsOther htargetMutable htargetOther hconflict
    by_cases hxBase : x = LVal.base lv
    · subst hxBase
      exact False.elim (EnvContains.move_base_same_false hmove hcontainsOther)
    · have hcontainsOtherOld :
          env ⊢ x ↝ Ty.borrow mutable targetsOther :=
        EnvContains.of_move hmove hcontainsOther
      have hbaseEq :
          LVal.base lv = x :=
        hsafe (LVal.base lv) x mutable targetsMutable targetsOther targetMutable
          targetOther
          (hbaseContains true targetsMutable hcontainsTy)
          hcontainsOtherOld
          htargetMutable htargetOther hconflict
      exact False.elim (hxBase hbaseEq.symm)
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable hcontainsTy htargetMutable htargetOther hconflict
    by_cases hxBase : x = LVal.base lv
    · subst hxBase
      exact False.elim (EnvContains.move_base_same_false hmove hcontainsMutable)
    · have hcontainsMutableOld :
          env ⊢ x ↝ Ty.borrow true targetsMutable :=
        EnvContains.of_move hmove hcontainsMutable
      have hbaseEq :
          x = LVal.base lv :=
        hsafe x (LVal.base lv) mutable targetsMutable targetsOther targetMutable
          targetOther hcontainsMutableOld
          (hbaseContains mutable targetsOther hcontainsTy)
          htargetMutable htargetOther hconflict
      exact False.elim (hxBase hbaseEq)

theorem EnvContains.move_var_same_false {env env' : Env} {x : Name}
    {slot : EnvSlot} {ty : Ty} {mutable : Bool} {targets : List LVal} :
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    EnvMove env (.var x) env' →
    ¬ env' ⊢ x ↝ Ty.borrow mutable targets := by
  intro _hslot _hslotTy hmove hcontains
  exact EnvContains.move_base_same_false hmove hcontains

theorem borrowSafety_move_var_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {ty : Ty} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.move (.var x)) ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe htyping hfresh a b mutable targetsMutable targetsOther
    targetMutable targetOther hcontainsMutable hcontainsOther htargetMutable
    htargetOther hconflict
  cases htyping with
  | move hLv _hvar hnotWrite hmove =>
      rcases LValTyping.var_inv hLv with
        ⟨sourceSlot, hslotSource, hsourceTy, _hsourceLifetime⟩
      by_cases ha : a = gamma
      · subst a
        have hcontainsMovedMutable :
            env ⊢ x ↝ Ty.borrow true targetsMutable := by
          rcases hcontainsMutable with
            ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
          have hslotEq :
              containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
            have h :
                { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
              simpa [Env.update] using hcontainedSlot
            exact h.symm
          subst hslotEq
          exact ⟨sourceSlot, hslotSource, by
            rw [hsourceTy]
            exact hcontainsTy⟩
        by_cases hb : b = gamma
        · subst b
          exact rfl
        · have hcontainsOtherMove :
              env₂ ⊢ b ↝ Ty.borrow mutable targetsOther :=
            EnvContains.update_fresh_ne hb hcontainsOther
          by_cases hbx : b = x
          · subst b
            exact False.elim
              (EnvContains.move_var_same_false hslotSource hsourceTy hmove
                hcontainsOtherMove)
          · have hcontainsOtherOld :
                env ⊢ b ↝ Ty.borrow mutable targetsOther :=
              EnvContains.of_move hmove hcontainsOtherMove
            have hsafeEq :
                x = b :=
              hsafe x b mutable targetsMutable targetsOther targetMutable
                targetOther hcontainsMovedMutable hcontainsOtherOld
                htargetMutable htargetOther hconflict
            exact False.elim (hbx hsafeEq.symm)
      · by_cases hb : b = gamma
        · subst b
          have hcontainsMovedOther :
              env ⊢ x ↝ Ty.borrow mutable targetsOther := by
            rcases hcontainsOther with
              ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
            have hslotEq :
                containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
              have h :
                  { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
                simpa [Env.update] using hcontainedSlot
              exact h.symm
            subst hslotEq
            exact ⟨sourceSlot, hslotSource, by
              rw [hsourceTy]
              exact hcontainsTy⟩
          have hcontainsMutableMove :
              env₂ ⊢ a ↝ Ty.borrow true targetsMutable :=
            EnvContains.update_fresh_ne ha hcontainsMutable
          by_cases hax : a = x
          · subst a
            exact False.elim
              (EnvContains.move_var_same_false hslotSource hsourceTy hmove
                hcontainsMutableMove)
          · have hcontainsMutableOld :
                env ⊢ a ↝ Ty.borrow true targetsMutable :=
              EnvContains.of_move hmove hcontainsMutableMove
            have hcontainsOtherOld :
                env ⊢ x ↝ Ty.borrow mutable targetsOther :=
              hcontainsMovedOther
            have hsafeEq :
                a = x :=
              hsafe a x mutable targetsMutable targetsOther targetMutable
                targetOther hcontainsMutableOld hcontainsOtherOld
                htargetMutable htargetOther hconflict
            exact False.elim (hax hsafeEq)
        · exact borrowSafeEnv_move hsafe hmove a b mutable targetsMutable
            targetsOther targetMutable targetOther
            (EnvContains.update_fresh_ne ha hcontainsMutable)
            (EnvContains.update_fresh_ne hb hcontainsOther)
            htargetMutable htargetOther hconflict

/-- Structured assignment-level replacement for `AssignmentWritePreservesCoherent`.

This avoids asking directly for `Coherent env₃`.  Instead it asks for the two
lvalue-transport facts that are sufficient to prove coherence of the result:
old-root borrow typings transport back to `env₂`, while borrow typings rooted at
the written base provide their joint target-list typings in `env₃`.
-/
def AssignmentWriteCoherenceObligations : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs)

theorem AssignmentWritePreservesCoherent.of_coherenceObligations
    (hobligations : AssignmentWriteCoherenceObligations) :
    AssignmentWritePreservesCoherent := by
  intro env₁ env₂ env₃ typing lifetime targetLifetime lhs oldTy rhs rhsTy φ
    hwellInitial hwellFormed hlinBy hbelow hLhs htargetLifetime hRhs hshape
    hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_coherent_of_obligations hwellFormed.2.2.1
    (hobligations hwellInitial hwellFormed hlinBy hbelow hLhs htargetLifetime
      hRhs hshape hwellRhs hwrite hnotWrite)

/-- Assignment-level rank side condition for the well-formedness induction.

This packages the rule obligation that `T-Assign` currently does not carry:
after typing the RHS and performing the write, there must be a pre-write
linearization witness such that every newly installed RHS borrow edge is ranked
downward in the result. -/
def AssignmentRhsEdgesRanked : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy

/-- Declaration-level fresh-slot coherence side condition for Lemma 4.9.

The legacy declaration case used `Coherent.update_fresh_ty`, which is false from
`WellFormedTy` alone.  This side condition states the missing local fact for each
`T-Declare`: adding the freshly declared full type must satisfy the explicit
fresh-update coherence obligations.
-/
def DeclarationFreshUpdateCoherent : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {ty : Ty},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₁.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh x →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    FreshUpdateCoherenceObligations env₂ x ty lifetime

/-- Declaration-level decomposition for borrow-free declared types.

For a borrow-free declared/result type, the fresh-root part of
`FreshUpdateCoherenceObligations` is automatic.  The only declaration-local
coherence work left is old-root transport for borrow typings in the extended
environment.
-/
def DeclarationFreshBorrowFreeOldRootTransport : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {ty : Ty},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₁.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh x →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    TyBorrowFree ty ∧
      (∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
        {borrowLifetime : Lifetime},
        LVal.base lv ≠ x →
        LValTyping (env₂.update x { ty := .ty ty, lifetime := lifetime })
          lv (.ty (.borrow mutable targets)) borrowLifetime →
        ∃ oldBorrowLifetime,
          LValTyping env₂ lv (.ty (.borrow mutable targets)) oldBorrowLifetime)

theorem DeclarationFreshUpdateCoherent.of_borrowFreeOldRootTransport
    (hdecl : DeclarationFreshBorrowFreeOldRootTransport) :
    DeclarationFreshUpdateCoherent := by
  intro env₁ env₂ env₃ typing lifetime x term ty hwellInitial hwellResult
    hwellTy hfreshIn hterm hfreshOut henv₃
  rcases hdecl hwellInitial hwellResult hwellTy hfreshIn hterm hfreshOut henv₃ with
    ⟨hborrowFree, holdTransport⟩
  exact FreshUpdateCoherenceObligations.of_tyBorrowFree hborrowFree holdTransport

theorem typingPreservesBorrowSafeResult_mutBorrow_case {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow true lv) (.borrow true [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) := by
  intro hborrowSafe htyping hfresh
  exact borrowSafety_mutBorrow_result_extension hborrowSafe htyping hfresh

theorem typingPreservesBorrowSafeResult_immBorrow_case {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow false lv) (.borrow false [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) := by
  intro hborrowSafe htyping hfresh
  exact borrowSafety_immBorrow_result_extension hborrowSafe htyping hfresh

theorem typingPreservesBorrowSafeResult_copy_case {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {ty : Ty}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hborrowSafe htyping hfresh
  cases htyping with
  | copy hLv hcopy _hnotRead =>
      cases hcopy with
      | int =>
          exact borrowSafeEnv_update_fresh_borrowFree hborrowSafe tyBorrowFree_int
      | immBorrow =>
          rename_i targets
          exact borrowSafeEnv_update_fresh_immBorrowMany hborrowSafe hfresh
            (by
              intro target htarget
              exact (LValTyping.no_readProhibited_targets_of_immBorrow hborrowSafe).1
                hLv PartialTyContains.here target htarget)

/--
Constructor-level borrow-safety landmarks used by the source-scoped Corollary
4.14 route.

Result-extension for `T-Const` is only proved for source values; arbitrary
runtime references need an evaluation/reachability invariant, not a local typing
fact.  The copy, move, mut/imm borrow, box, and declaration shells are proved
directly from the conflict definitions and induction hypotheses.  The assignment
field consumes the full RHS induction result: `BorrowSafeEnv env₂` plus the
root-independent fact that the RHS type has no borrow-target conflicts with
`env₂`.  This avoids baking fresh-name reasoning into assignment; fresh result
installation is a caller-level corollary of the same invariant.  Block bodies
are handled by the mutual term/list induction below: the induction carries
`TyBorrowSafeAgainstEnv` through `dropLifetime`, so there is no separate
block-list obligation here.
-/
structure BorrowSafetyPreservationObligations : Prop where
  envWrite {env₁ env₂ env₃ : Env}
      {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
      {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
      BorrowSafeEnv env₂ →
      TyBorrowSafeAgainstEnv env₂ rhsTy →
      LValTyping env₁ lhs oldTy targetLifetime →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      ShapeCompatible env₂ oldTy (.ty rhsTy) →
      WellFormedTy env₂ rhsTy targetLifetime →
      EnvWrite 0 env₂ lhs rhsTy env₃ →
      (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
      EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
      ¬ WriteProhibited env₃ lhs →
      BorrowSafeEnv env₃

/-- Move borrow-safety preservation, including result-extension.

The proof uses `LValTyping.contains_base_of_strike`: since `EnvMove` follows a
`Strike` path, every borrow contained in the moved result type originated in the
moved base slot.  Once that origin fact is known,
`borrowSafeEnv_move_result_extension_of_base_contains` discharges the fresh
result root.
-/
theorem borrowSafetyPreservation_move
    {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {ty : Ty} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    (∀ x, lv ≠ .var x) →
    ¬ TyBorrowFree ty →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hborrowSafe htyping _hnotVar _hnotBorrowFree hfresh
  cases htyping with
  | move hLv _hvar _hnotWrite hmove =>
      rcases hmove with ⟨slot, struck, hslot, hstrike, henv₂⟩
      subst henv₂
      exact borrowSafeEnv_move_result_extension_of_base_contains
        hborrowSafe
        ⟨slot, struck, hslot, hstrike, rfl⟩
        (by
          intro mutable targets hcontains
          exact LValTyping.contains_base_of_strike hLv hslot hstrike hcontains)
        hfresh

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
    LValTyping env₁ lhs oldTy targetLifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    ¬ WriteProhibited env₃ lhs →
    BorrowSafeEnv env₃ := by
  intro hborrowSafe hsafeTy _hLhs _hRhs _hshape _hwellTy hwrite hranked _hcoh
    _hnotWrite x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  rcases hranked with ⟨_φ, _hlinBy, hbelow⟩
  rcases hcontainsMutable with ⟨mutableSlot, hmutableSlot, hmutableContains⟩
  rcases hcontainsOther with ⟨otherSlot, hotherSlot, hotherContains⟩
  have hmutableOrigin :=
    EnvWrite.borrowTargetOrigin_all hwrite x mutableSlot true targetsMutable
      hmutableSlot hmutableContains targetMutable htargetMutable
  have hotherOrigin :=
    EnvWrite.borrowTargetOrigin_all hwrite y otherSlot mutable targetsOther
      hotherSlot hotherContains targetOther htargetOther
  rcases hmutableOrigin with hmutableOld | hmutableRhs
  · rcases hmutableOld with
      ⟨oldMutableSlot, oldMutableTargets, holdMutableSlot,
        holdMutableContains, holdMutableTarget⟩
    rcases hotherOrigin with hotherOld | hotherRhs
    · rcases hotherOld with
        ⟨oldOtherSlot, oldOtherTargets, holdOtherSlot,
          holdOtherContains, holdOtherTarget⟩
      exact hborrowSafe x y mutable oldMutableTargets oldOtherTargets
        targetMutable targetOther
        ⟨oldMutableSlot, holdMutableSlot, holdMutableContains⟩
        ⟨oldOtherSlot, holdOtherSlot, holdOtherContains⟩
        holdMutableTarget holdOtherTarget hconflict
    · rcases hotherRhs with ⟨rhsOtherTargets, hrhsOtherContains, hrhsOtherTarget⟩
      exact False.elim
        (hsafeTy.2 x oldMutableTargets mutable rhsOtherTargets targetMutable
          targetOther
          ⟨oldMutableSlot, holdMutableSlot, holdMutableContains⟩
          hrhsOtherContains holdMutableTarget hrhsOtherTarget hconflict)
  · rcases hmutableRhs with
      ⟨rhsMutableTargets, hrhsMutableContains, hrhsMutableTarget⟩
    rcases hotherOrigin with hotherOld | hotherRhs
    · rcases hotherOld with
        ⟨oldOtherSlot, oldOtherTargets, holdOtherSlot,
          holdOtherContains, holdOtherTarget⟩
      exact False.elim
        (hsafeTy.1 rhsMutableTargets mutable oldOtherTargets y targetMutable
          targetOther hrhsMutableContains
          ⟨oldOtherSlot, holdOtherSlot, holdOtherContains⟩
          hrhsMutableTarget holdOtherTarget hconflict)
    · rcases hotherRhs with ⟨rhsOtherTargets, hrhsOtherContains, hrhsOtherTarget⟩
      exact hbelow.2 x y mutable targetsMutable targetsOther targetMutable
        targetOther
        ⟨mutableSlot, hmutableSlot, hmutableContains⟩
        ⟨otherSlot, hotherSlot, hotherContains⟩
        htargetMutable htargetOther hconflict
        ⟨true, rhsMutableTargets, hrhsMutableContains, hrhsMutableTarget⟩
        ⟨mutable, rhsOtherTargets, hrhsOtherContains, hrhsOtherTarget⟩

/-- Concrete borrow-safety package assembled from proved local preservation lemmas. -/
theorem borrowSafetyPreservationObligations_proved :
    BorrowSafetyPreservationObligations where
  envWrite := borrowSafetyPreservation_envWrite

/--
Lemma 4.9, Borrow Invariance, stated over the core output environment.  The
older `gamma` result-extension variants remain only as explicitly named
compatibility helpers.
-/
theorem borrowInvariance {store : ProgramStore} {env₁ env₂ : Env}
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
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
      hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact hwellFormedOutput

/--
Borrow invariance through the fully explicit ranked/fresh-coherence route.

This is now a compatibility wrapper around
`borrowInvariance_of_ruleCarriedObligations`; the assignment/declaration
side-condition parameters are supplied by the typing derivation itself.
-/
theorem borrowInvariance_of_rankedAssign_and_declFreshCoherence
    (_hrankedAssign : AssignmentRhsEdgesRanked)
    (_hwriteCoherent : AssignmentWriteCoherenceObligations)
    (_hdeclFresh : DeclarationFreshUpdateCoherent)
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
Main borrow-safety induction behind Corollary 4.14.

The result binding is included in the statement because the paper's corollary
checks borrow-safety after extending the output environment with `γ ↦ <T>^l`.
-/
theorem typingPreservesBorrowSafeResult_global {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    SourceTerm term →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    BorrowSafeEnv env₂ ∧
      TyBorrowSafeAgainstEnv env₂ ty ∧
      ∀ gamma,
        env₂.fresh gamma →
        BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource hborrowSafe htyping
  let hobligations := borrowSafetyPreservationObligations_proved
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      SourceTerm term →
        BorrowSafeEnv env →
        BorrowSafeEnv env₂ ∧
          TyBorrowSafeAgainstEnv env₂ ty ∧
          ∀ gamma,
            env₂.fresh gamma →
            BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }))
    (motive_2 := fun env _typing lifetime terms _ty env₂ _ =>
      SourceTerm (.block lifetime terms) →
        BorrowSafeEnv env →
        BorrowSafeEnv env₂ ∧
          TyBorrowSafeAgainstEnv env₂ _ty)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping hsource hborrowSafe =>
      by
        have hborrowFree : TyBorrowFree _ty :=
          sourceValue_valueTyping_borrowFree
            (hsource _value (by simp [termValues])) hvalueTyping
        refine ⟨hborrowSafe, tyBorrowSafeAgainstEnv_borrowFree hborrowFree, ?_⟩
        intro gamma hfresh
        exact borrowSafe_value_result_extension_borrowFree
          (TermTyping.const hvalueTyping) hborrowSafe
          hborrowFree
          hfresh)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy hnotRead
        _hsource hborrowSafe =>
      ⟨hborrowSafe,
        (by
          cases hcopy with
          | int =>
              exact tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_int
          | immBorrow =>
              rename_i targets
              exact tyBorrowSafeAgainstEnv_immBorrowMany
                (by
                  intro target htarget
                  exact (LValTyping.no_readProhibited_targets_of_immBorrow hborrowSafe).1
                    hLv PartialTyContains.here target htarget)),
        fun gamma hfresh =>
        typingPreservesBorrowSafeResult_copy_case hborrowSafe
          (TermTyping.copy (typing := _typing) hLv hcopy hnotRead) hfresh⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
        hLv hvar hnotWrite hmove _hsource hborrowSafe =>
      by
        have hcore : BorrowSafeEnv _env₂ :=
          borrowSafeEnv_move hborrowSafe hmove
        have hsafeTy : TyBorrowSafeAgainstEnv _env₂ _ty := by
          rcases hmove with ⟨slot, struck, hslot, hstrike, henv₂⟩
          subst henv₂
          exact tyBorrowSafeAgainstEnv_move_of_base_contains
            hborrowSafe
            ⟨slot, struck, hslot, hstrike, rfl⟩
            (by
              intro mutable targets hcontains
              exact LValTyping.contains_base_of_strike hLv hslot hstrike hcontains)
        refine ⟨hcore, hsafeTy, ?_⟩
        intro gamma hfresh
        cases _lv with
        | var x =>
            exact borrowSafety_move_var_result_extension hborrowSafe
              (TermTyping.move (typing := _typing) hLv hvar hnotWrite hmove) hfresh
        | deref lv =>
            by_cases hborrowFree : TyBorrowFree _ty
            · exact borrowSafety_move_borrowFree_result_extension
                (typing := _typing) hborrowSafe
                (TermTyping.move (typing := _typing) hLv hvar hnotWrite hmove)
                hborrowFree
            · exact borrowSafetyPreservation_move (typing := _typing) hborrowSafe
                (TermTyping.move (typing := _typing) hLv hvar hnotWrite hmove)
                (by
                  intro x hvar
                  cases hvar)
                hborrowFree
                hfresh)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hvar hmutable hnotWrite
        _hsource hborrowSafe =>
      ⟨hborrowSafe,
        tyBorrowSafeAgainstEnv_mutBorrow hnotWrite,
        fun gamma hfresh =>
        typingPreservesBorrowSafeResult_mutBorrow_case hborrowSafe
          (TermTyping.mutBorrow (typing := _typing) hLv hvar hmutable hnotWrite) hfresh⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hvar hnotRead
        _hsource hborrowSafe =>
      ⟨hborrowSafe,
        tyBorrowSafeAgainstEnv_immBorrow hnotRead,
        fun gamma hfresh =>
        typingPreservesBorrowSafeResult_immBorrow_case hborrowSafe
          (TermTyping.immBorrow (typing := _typing) hLv hvar hnotRead) hfresh⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih hsource hborrowSafe =>
      by
        have hinner := ih (SourceTerm.box_inner hsource) hborrowSafe
        exact ⟨hinner.1, TyBorrowSafeAgainstEnv.box hinner.2.1, by
          intro gamma hfresh
          exact borrowSafeEnv_update_box_of_update_inner (hinner.2.2 gamma hfresh)⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms _hsingleton hwellTy _hdropSafe hdrop _ih hsource hborrowSafe =>
      by
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
        refine ⟨hblockCore, hblockTySafe, ?_⟩
        intro gamma _hfresh
        exact borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv hblockCore hblockTySafe)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfreshX hterm hfreshOut _hcoh henv₃ _ih
        hsource hborrowSafe =>
      by
        have hinner := _ih (SourceTerm.declare_inner hsource) hborrowSafe
        have hdeclaredSafe :
            BorrowSafeEnv
              (_env₂.update _x { ty := .ty _ty, lifetime := _lifetime }) := by
          exact hinner.2.2 _x hfreshOut
        rw [henv₃]
        exact ⟨hdeclaredSafe,
          tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit,
          fun gamma _hfreshGamma =>
            borrowSafeEnv_update_fresh_borrowFree hdeclaredSafe tyBorrowFree_unit⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs _hLhsPost hshape hwellTy _hvar hwrite hranked hcoh hnotWrite _ih
        hsource hborrowSafe =>
      by
        have hRhsSafe := _ih (SourceTerm.assign_inner hsource) hborrowSafe
        have hwriteSafe :
            BorrowSafeEnv _env₃ :=
          hobligations.envWrite hRhsSafe.1 hRhsSafe.2.1 hLhs hRhs hshape hwellTy
            hwrite hranked hcoh hnotWrite
        exact ⟨hwriteSafe,
          tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit,
          fun _gamma _hfresh =>
          borrowSafeEnv_update_fresh_borrowFree hwriteSafe tyBorrowFree_unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm _ih hsource hborrowSafe =>
      let h := _ih (SourceTerm.block_head hsource) hborrowSafe
      ⟨h.1, h.2.1⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hnonOwner _hrest _ihHead _ihRest hsource hborrowSafe =>
      by
        have hhead := _ihHead (SourceTerm.block_head hsource) hborrowSafe
        exact _ihRest (SourceTerm.block_tail hsource) hhead.1)
    htyping hsource hborrowSafe

theorem typingPreservesBorrowSafeResult {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    SourceTerm term →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource hborrowSafe htyping hfresh
  exact (typingPreservesBorrowSafeResult_global hsource
    hborrowSafe htyping).2.2 gamma hfresh

/--
Borrow Safety through the explicit, proof-carrying borrow-invariance route.

The borrow-safe preservation half is unchanged; the well-formedness half uses
`borrowInvariance_of_rankedAssign_and_declFreshCoherence`.
-/
theorem borrowSafety_of_rankedAssign_and_declFreshCoherence
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    AssignmentRhsEdgesRanked →
    AssignmentWriteCoherenceObligations →
    DeclarationFreshUpdateCoherent →
    SourceTerm term →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ BorrowSafeEnv env₂ := by
  intro hrankedAssign hwriteCoherent
    hdeclFresh hsource hrefs hvalidState hvalidStoreTyping hwellFormed hborrowSafe hsafe
    htyping
  exact ⟨
    borrowInvariance_of_rankedAssign_and_declFreshCoherence
      hrankedAssign hwriteCoherent hdeclFresh hrefs hvalidState
      hvalidStoreTyping hwellFormed hsafe htyping,
    (typingPreservesBorrowSafeResult_global hsource hborrowSafe htyping).1⟩

/--
Borrow safety through the rule-carried borrow-invariance route.

The well-formedness half avoids the legacy write/fresh shortcuts and does not
require global assignment/declaration side predicates; those facts are attached
to the typing derivation.
-/
theorem borrowSafety_of_ruleCarriedObligations
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    SourceTerm term →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ BorrowSafeEnv env₂ := by
  intro hsource hrefs hvalidState hvalidStoreTyping
    hwellFormed hborrowSafe hsafe htyping
  exact ⟨
    borrowInvariance_of_ruleCarriedObligations
      hrefs hvalidState hvalidStoreTyping hwellFormed hsafe
      htyping,
    (typingPreservesBorrowSafeResult_global hsource hborrowSafe htyping).1⟩

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Corollary 4.14, Borrow Safety (core/strengthened form `Γ₂ = Γ₃`). -/
theorem corollary_4_14_borrowSafety
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hrefs : ∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime)
    (hvalidState : ValidState store term)
    (hvalidStoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hsafe : store ∼ₛ env₁)
    (hsource : SourceTerm term)
    (htyping : TermTyping env₁ typing lifetime term ty env₂) :
    WellFormedEnv env₂ lifetime ∧ BorrowSafeEnv env₂ :=
  borrowSafety_of_ruleCarriedObligations
    hsource hrefs hvalidState hvalidStoreTyping hwellFormed hborrowSafe hsafe htyping

end LwRust.Paper.Soundness
