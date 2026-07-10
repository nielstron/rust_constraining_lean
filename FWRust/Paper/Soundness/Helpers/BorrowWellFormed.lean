import FWRust.Paper.Soundness.Helpers.SafeAbstraction

/-!
# Soundness helpers: Borrow well-formedness

Single-target borrow well-formedness and lifetime utilities for the core
calculus.
-/

namespace FWRust
namespace Paper

open Core

theorem PathConflicts.symm {left right : LVal} :
    left ⋈ right →
    right ⋈ left := by
  intro h
  exact Eq.symm h

@[simp] theorem containedBorrowsWellFormed_empty :
    ContainedBorrowsWellFormed Env.empty := by
  intro x slot mutable target hslot _hcontains
  simp [Env.empty] at hslot

@[simp] theorem containedBorrowsWellFormedWhenInitialized_empty :
    ContainedBorrowsWellFormedWhenInitialized Env.empty := by
  intro x slot mutable target hslot _hcontains
  simp [Env.empty] at hslot

@[simp] theorem envSlotsOutlive_empty (lifetime : Lifetime) :
    EnvSlotsOutlive Env.empty lifetime := by
  intro x slot hslot
  simp [Env.empty] at hslot

theorem lvalTyping_empty_false {lv : LVal} {p : PartialTy} {lf : Lifetime}
    (h : LValTyping Env.empty lv p lf) : False := by
  induction lv generalizing p lf with
  | var x =>
      cases h with
      | var hslot => simp [Env.empty] at hslot
  | deref lv ih =>
      cases h with
      | box hb => exact ih hb
      | boxFull hb => exact ih hb
      | borrow hb _ => exact ih hb

@[simp] theorem wellFormedEnvWhenInitialized_empty (lifetime : Lifetime) :
    WellFormedEnvWhenInitialized Env.empty lifetime := by
  exact ⟨containedBorrowsWellFormedWhenInitialized_empty,
    envSlotsOutlive_empty lifetime⟩

@[simp] theorem wellFormedEnv_empty (lifetime : Lifetime) :
    WellFormedEnv Env.empty lifetime := by
  exact ⟨containedBorrowsWellFormed_empty, envSlotsOutlive_empty lifetime⟩

theorem wellFormedEnv_empty_all :
    ∀ lifetime, WellFormedEnv Env.empty lifetime := by
  intro lifetime
  exact wellFormedEnv_empty lifetime

theorem ContainedBorrowsWellFormed.whenInitialized {env : Env} :
    ContainedBorrowsWellFormed env →
    ContainedBorrowsWellFormedWhenInitialized env := by
  intro hcontained x slot mutable target hslot hcontains
  rcases hcontained x slot mutable target hslot hcontains with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  exact ⟨hbase, fun _ => ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩⟩

theorem WellFormedEnv.whenInitialized {env : Env} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedEnvWhenInitialized env lifetime := by
  intro hwell
  exact ⟨ContainedBorrowsWellFormed.whenInitialized hwell.1, hwell.2⟩

theorem LifetimeOutlives.trans {first second third : Lifetime} :
    first ≤ second →
    second ≤ third →
    first ≤ third := by
  intro hfirst hsecond
  simp [LifetimeOutlives, Core.Lifetime.contains] at hfirst hsecond ⊢
  exact hfirst.trans hsecond

theorem LifetimeChild.outlives {parent child : Lifetime} :
    LifetimeChild parent child →
    parent ≤ child := by
  intro hchild
  rcases hchild with ⟨label, hpath⟩
  simp [LifetimeOutlives, Core.Lifetime.contains, hpath]

theorem LifetimeChild.not_child_outlives_parent {parent child : Lifetime} :
    LifetimeChild parent child →
    ¬ child ≤ parent := by
  intro hchild hle
  rcases hchild with ⟨label, hpath⟩
  have hprefix : child.path <+: parent.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hle
  have hlenLe : child.path.length ≤ parent.path.length :=
    hprefix.length_le
  rw [hpath, List.length_append] at hlenLe
  simp at hlenLe

theorem EnvSlotsOutlive.weaken {env : Env} {outer inner : Lifetime} :
    EnvSlotsOutlive env outer →
    outer ≤ inner →
    EnvSlotsOutlive env inner := by
  intro houtlives houterInner x slot hslot
  exact LifetimeOutlives.trans (houtlives x slot hslot) houterInner

theorem WellFormedEnv.weaken {env : Env} {outer inner : Lifetime} :
    WellFormedEnv env outer →
    outer ≤ inner →
    WellFormedEnv env inner := by
  intro hwell houterInner
  exact ⟨hwell.1, EnvSlotsOutlive.weaken hwell.2 houterInner⟩

theorem WellFormedEnvWhenInitialized.weaken {env : Env} {outer inner : Lifetime} :
    WellFormedEnvWhenInitialized env outer →
    outer ≤ inner →
    WellFormedEnvWhenInitialized env inner := by
  intro hwell houterInner
  exact ⟨hwell.1, EnvSlotsOutlive.weaken hwell.2 houterInner⟩

theorem LValTyping.update_fresh_one {env : Env} {x : Name} {slot : EnvSlot}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    env.fresh x →
    LValTyping env lv ty lifetime →
    LValTyping (env.update x slot) lv ty lifetime := by
  intro hfresh htyping
  induction htyping with
  | var hslot =>
      rename_i y envSlot
      by_cases h : y = x
      · subst h
        unfold Env.fresh at hfresh
        rw [hfresh] at hslot
        cases hslot
      · exact LValTyping.var (by simpa [Env.update, h] using hslot)
  | box _ ih =>
      exact LValTyping.box ih
  | boxFull _ ih =>
      exact LValTyping.boxFull ih
  | borrow _ _ ihBorrow ihTarget =>
      exact LValTyping.borrow ihBorrow ihTarget

theorem LValBaseOutlives.weaken {env : Env} {target : LVal}
    {outer inner : Lifetime} :
    LValBaseOutlives env target outer →
    outer ≤ inner →
    LValBaseOutlives env target inner := by
  intro hbase houtlives
  rcases hbase with ⟨slot, hslot, hslotLife⟩
  exact ⟨slot, hslot, LifetimeOutlives.trans hslotLife houtlives⟩

theorem borrowTargetsWellFormedInSlot_update_fresh {env : Env} {x : Name}
    {slot : EnvSlot} {slotLifetime : Lifetime} {target : LVal} :
    env.fresh x →
    BorrowTargetsWellFormedInSlot env slotLifetime target →
    BorrowTargetsWellFormedInSlot (env.update x slot) slotLifetime target := by
  intro hfresh htarget
  rcases htarget with ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  refine ⟨targetTy, targetLifetime,
    LValTyping.update_fresh_one (slot := slot) hfresh htyping, houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  have hbaseNe : LVal.base target ≠ x := by
    intro hbaseEq
    subst hbaseEq
    unfold Env.fresh at hfresh
    rw [hfresh] at hbaseSlot
    cases hbaseSlot
  exact ⟨baseSlot, by simpa [Env.update, hbaseNe] using hbaseSlot, hbaseOutlives⟩

theorem BorrowTargetsWellFormed.inSlot {env : Env} {target : LVal}
    {lifetime : Lifetime} :
    BorrowTargetsWellFormed env target lifetime →
    BorrowTargetsWellFormedInSlot env lifetime target := by
  intro htarget
  cases htarget with
  | intro h => exact h

theorem BorrowTargetsWellFormed.singleton {env : Env} {target : LVal}
    {targetTy : Ty} {targetLifetime lifetime : Lifetime} :
    LValTyping env target (.ty targetTy) targetLifetime →
    targetLifetime ≤ lifetime →
    LValBaseOutlives env target lifetime →
    BorrowTargetsWellFormed env target lifetime := by
  intro htarget houtlives hbase
  exact BorrowTargetsWellFormed.intro
    ⟨targetTy, targetLifetime, htarget, houtlives, hbase⟩

theorem BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed {env : Env}
    {target : LVal} {slotLifetime lifetime : Lifetime} :
    BorrowTargetsWellFormedInSlot env slotLifetime target →
    slotLifetime ≤ lifetime →
    BorrowTargetsWellFormed env target lifetime := by
  intro htarget houtlives
  rcases htarget with ⟨targetTy, targetLifetime, htyping, htargetSlot, hbase⟩
  exact BorrowTargetsWellFormed.intro
    ⟨targetTy, targetLifetime, htyping,
      LifetimeOutlives.trans htargetSlot houtlives,
      LValBaseOutlives.weaken hbase houtlives⟩

theorem EnvContains.borrowTargetsWellFormed {env : Env} {x : Name}
    {mutable : Bool} {target : LVal} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    env ⊢ x ↝ Ty.borrow mutable target →
    BorrowTargetsWellFormed env target lifetime := by
  intro hwell hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
    (hwell.1 x slot mutable target hslot ⟨slot, hslot, hcontainsTy⟩)
    (hwell.2 x slot hslot)

theorem BorrowTargetsWellFormed.member {env : Env} {target : LVal}
    {lifetime : Lifetime} :
    BorrowTargetsWellFormed env target lifetime →
    ∃ targetTy targetLifetime,
      LValTyping env target (.ty targetTy) targetLifetime ∧
        targetLifetime ≤ lifetime ∧
        LValBaseOutlives env target lifetime := by
  intro htarget
  cases htarget with
  | intro h => exact h

theorem BorrowTargetsWellFormed.whenInitialized {env : Env} {target : LVal}
    {lifetime : Lifetime} :
    BorrowTargetsWellFormed env target lifetime →
    BorrowTargetsWellFormedWhenInitialized env target lifetime := by
  intro htarget
  rcases BorrowTargetsWellFormed.member htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  exact ⟨hbase, fun _ => ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩⟩

theorem BorrowTargetsWellFormed.weaken {env : Env} {target : LVal}
    {outer inner : Lifetime} :
    BorrowTargetsWellFormed env target outer →
    outer ≤ inner →
    BorrowTargetsWellFormed env target inner := by
  intro htarget houterInner
  rcases BorrowTargetsWellFormed.member htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  exact BorrowTargetsWellFormed.intro
    ⟨targetTy, targetLifetime, htyping,
      LifetimeOutlives.trans houtlives houterInner,
      LValBaseOutlives.weaken hbase houterInner⟩

theorem BorrowTargetsWellFormedInSlot.weaken {env : Env} {target : LVal}
    {outer inner : Lifetime} :
    BorrowTargetsWellFormedInSlot env outer target →
    outer ≤ inner →
    BorrowTargetsWellFormedInSlot env inner target := by
  intro htarget houtlives
  rcases htarget with ⟨targetTy, targetLifetime, htyping, htargetOuter, hbase⟩
  exact ⟨targetTy, targetLifetime, htyping,
    LifetimeOutlives.trans htargetOuter houtlives,
    LValBaseOutlives.weaken hbase houtlives⟩

theorem BorrowTargetsWellFormedInSlot.whenInitialized {env : Env}
    {target : LVal} {slotLifetime : Lifetime} :
    BorrowTargetsWellFormedInSlot env slotLifetime target →
    BorrowTargetsWellFormedInSlotWhenInitialized env slotLifetime target := by
  intro htarget
  rcases htarget with ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  exact ⟨hbase, fun _ => ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩⟩

theorem BorrowTargetsWellFormedWhenInitialized.weaken {env : Env}
    {target : LVal} {outer inner : Lifetime} :
    BorrowTargetsWellFormedWhenInitialized env target outer →
    outer ≤ inner →
    BorrowTargetsWellFormedWhenInitialized env target inner := by
  intro htarget houtlives
  rcases htarget with ⟨hbase, hinitialized⟩
  exact ⟨LValBaseOutlives.weaken hbase houtlives, fun hinit =>
    let ⟨targetTy, targetLifetime, htyping, htargetOuter, hbase'⟩ :=
      hinitialized hinit
    ⟨targetTy, targetLifetime, htyping,
      LifetimeOutlives.trans htargetOuter houtlives,
      LValBaseOutlives.weaken hbase' houtlives⟩⟩

theorem BorrowTargetsWellFormedInSlotWhenInitialized.weaken {env : Env}
    {target : LVal} {outer inner : Lifetime} :
    BorrowTargetsWellFormedInSlotWhenInitialized env outer target →
    outer ≤ inner →
    BorrowTargetsWellFormedInSlotWhenInitialized env inner target := by
  exact BorrowTargetsWellFormedWhenInitialized.weaken

theorem BorrowTargetsWellFormedWhenInitialized.inSlot {env : Env}
    {target : LVal} {lifetime : Lifetime} :
    BorrowTargetsWellFormedWhenInitialized env target lifetime →
    BorrowTargetsWellFormedInSlotWhenInitialized env lifetime target := by
  intro htarget
  exact htarget

theorem PartialTyBorrowsWellFormedInSlot.weaken {env : Env}
    {outer inner : Lifetime} {partialTy : PartialTy} :
    PartialTyBorrowsWellFormedInSlot env outer partialTy →
    outer ≤ inner →
    PartialTyBorrowsWellFormedInSlot env inner partialTy := by
  intro hpartial houtlives mutable target hcontains
  exact BorrowTargetsWellFormedInSlot.weaken (hpartial hcontains) houtlives

theorem PartialTyBorrowsWellFormedInSlot.whenInitialized {env : Env}
    {slotLifetime : Lifetime} {partialTy : PartialTy} :
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy := by
  intro hpartial mutable target hcontains
  exact BorrowTargetsWellFormedInSlot.whenInitialized (hpartial hcontains)

theorem PartialTyBorrowsWellFormedInSlotWhenInitialized.weaken {env : Env}
    {outer inner : Lifetime} {partialTy : PartialTy} :
    PartialTyBorrowsWellFormedInSlotWhenInitialized env outer partialTy →
    outer ≤ inner →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env inner partialTy := by
  intro hpartial houtlives mutable target hcontains
  exact BorrowTargetsWellFormedInSlotWhenInitialized.weaken
    (hpartial hcontains) houtlives

theorem WellFormedTy.weaken {env : Env} {ty : Ty} {outer inner : Lifetime} :
    WellFormedTy env ty outer →
    outer ≤ inner →
    WellFormedTy env ty inner := by
  intro hwell houtlives
  induction hwell with
  | unit => exact WellFormedTy.unit
  | int => exact WellFormedTy.int
  | borrow htarget =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.weaken htarget houtlives)
  | box _ ih => exact WellFormedTy.box (ih houtlives)

theorem WellFormedTy.whenInitialized {env : Env} {ty : Ty}
    {lifetime : Lifetime} :
    WellFormedTy env ty lifetime →
    WellFormedTyWhenInitialized env ty lifetime := by
  intro hwell
  induction hwell with
  | unit => exact WellFormedTyWhenInitialized.unit
  | int => exact WellFormedTyWhenInitialized.int
  | borrow htarget =>
      exact WellFormedTyWhenInitialized.borrow
        (BorrowTargetsWellFormed.whenInitialized htarget)
  | box _ ih => exact WellFormedTyWhenInitialized.box ih

theorem WellFormedTyWhenInitialized.weaken {env : Env} {ty : Ty}
    {outer inner : Lifetime} :
    WellFormedTyWhenInitialized env ty outer →
    outer ≤ inner →
    WellFormedTyWhenInitialized env ty inner := by
  intro hwell houtlives
  induction hwell with
  | unit => exact WellFormedTyWhenInitialized.unit
  | int => exact WellFormedTyWhenInitialized.int
  | borrow htarget =>
      exact WellFormedTyWhenInitialized.borrow
        (BorrowTargetsWellFormedWhenInitialized.weaken htarget houtlives)
  | box _ ih => exact WellFormedTyWhenInitialized.box (ih houtlives)

theorem borrowTargetsWellFormedInSlot_of_wellFormedTy_contains {env : Env}
    {ty : Ty} {lifetime : Lifetime} {mutable : Bool} {target : LVal} :
    WellFormedTy env ty lifetime →
    PartialTyContains (.ty ty) (.borrow mutable target) →
    BorrowTargetsWellFormedInSlot env lifetime target := by
  intro hwell hcontains
  induction hwell with
  | unit => cases hcontains
  | int => cases hcontains
  | borrow htarget =>
      cases hcontains with
      | here => exact BorrowTargetsWellFormed.inSlot htarget
  | box _ ih =>
      cases hcontains with
      | tyBox hinner => exact ih hinner

theorem borrowTargetsWellFormedInSlotWhenInitialized_of_wellFormedTy_contains
    {env : Env} {ty : Ty} {lifetime : Lifetime} {mutable : Bool}
    {target : LVal} :
    WellFormedTyWhenInitialized env ty lifetime →
    PartialTyContains (.ty ty) (.borrow mutable target) →
    BorrowTargetsWellFormedInSlotWhenInitialized env lifetime target := by
  intro hwell hcontains
  induction hwell with
  | unit => cases hcontains
  | int => cases hcontains
  | borrow htarget =>
      cases hcontains with
      | here => exact BorrowTargetsWellFormedWhenInitialized.inSlot htarget
  | box _ ih =>
      cases hcontains with
      | tyBox hinner => exact ih hinner

theorem PartialTyBorrowsWellFormedInSlot.of_wellFormedTy {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedTy env ty lifetime →
    PartialTyBorrowsWellFormedInSlot env lifetime (.ty ty) := by
  intro hwell mutable target hcontains
  exact borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwell hcontains

theorem PartialTyBorrowsWellFormedInSlotWhenInitialized.of_wellFormedTy
    {env : Env} {ty : Ty} {lifetime : Lifetime} :
    WellFormedTyWhenInitialized env ty lifetime →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env lifetime (.ty ty) := by
  intro hwell mutable target hcontains
  exact borrowTargetsWellFormedInSlotWhenInitialized_of_wellFormedTy_contains
    hwell hcontains

theorem TyBorrowsWellFormedWhenInitialized.of_wellFormedTy {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedTy env ty lifetime →
    TyBorrowsWellFormedWhenInitialized env ty lifetime := by
  intro hwell mutable target hcontains
  exact BorrowTargetsWellFormedInSlot.whenInitialized
    (borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwell hcontains)

theorem PartialTyBorrowsWellFormedInSlot.box {env : Env}
    {slotLifetime : Lifetime} {inner : PartialTy} :
    PartialTyBorrowsWellFormedInSlot env slotLifetime inner →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.box inner) := by
  intro hinner mutable target hcontains
  cases hcontains with
  | box h => exact hinner h

theorem PartialTyBorrowsWellFormedInSlot.box_inv {env : Env}
    {slotLifetime : Lifetime} {inner : PartialTy} :
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.box inner) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
  intro hbox mutable target hcontains
  exact hbox (PartialTyContains.box hcontains)

theorem LValTyping.base_slot_exists {env : Env} :
    ∀ {lv : LVal} {p : PartialTy} {lf : Lifetime}, LValTyping env lv p lf →
      ∃ slot, env.slotAt (LVal.base lv) = some slot := by
  intro lv
  induction lv with
  | var x =>
      intro p lf h
      cases h with
      | var hslot => exact ⟨_, by simpa [LVal.base] using hslot⟩
  | deref lv ih =>
      intro p lf h
      cases h with
      | box hb => simpa [LVal.base] using ih hb
      | boxFull hb => simpa [LVal.base] using ih hb
      | borrow hb _ => simpa [LVal.base] using ih hb

theorem ty_vars_mem_contains {ty : Ty} :
    ∀ v, v ∈ Ty.vars ty →
      ∃ mutable target,
        PartialTyContains (.ty ty) (.borrow mutable target) ∧
        LVal.base target = v := by
  exact Ty.rec
    (motive_1 := fun ty => ∀ v, v ∈ Ty.vars ty →
      ∃ mutable target,
        PartialTyContains (.ty ty) (.borrow mutable target) ∧
        LVal.base target = v)
    (motive_2 := fun pt => ∀ v, v ∈ PartialTy.vars pt →
      ∃ mutable target,
        PartialTyContains pt (.borrow mutable target) ∧
        LVal.base target = v)
    (by intro v hv; simp [Ty.vars] at hv)
    (by intro v hv; simp [Ty.vars] at hv)
    (by
      intro mutable target v hv
      simp [Ty.vars] at hv
      exact ⟨mutable, target, PartialTyContains.here, hv.symm⟩)
    (by
      intro inner ih v hv
      rcases ih v (by simpa [Ty.vars] using hv) with
        ⟨mutable, target, hcontains, hbase⟩
      exact ⟨mutable, target, PartialTyContains.tyBox hcontains, hbase⟩)
    (by
      intro ty ih v hv
      exact ih v (by simpa [PartialTy.vars] using hv))
    (by
      intro inner ih v hv
      rcases ih v (by simpa [PartialTy.vars] using hv) with
        ⟨mutable, target, hcontains, hbase⟩
      exact ⟨mutable, target, PartialTyContains.box hcontains, hbase⟩)
    (by intro shape _ih v hv; simp [PartialTy.vars] at hv)
    ty

theorem partialTy_vars_mem_contains {pt : PartialTy} :
    ∀ v, v ∈ PartialTy.vars pt →
      ∃ mutable target,
        PartialTyContains pt (.borrow mutable target) ∧
        LVal.base target = v := by
  exact PartialTy.rec
    (motive_1 := fun ty => ∀ v, v ∈ Ty.vars ty →
      ∃ mutable target,
        PartialTyContains (.ty ty) (.borrow mutable target) ∧
        LVal.base target = v)
    (motive_2 := fun pt => ∀ v, v ∈ PartialTy.vars pt →
      ∃ mutable target,
        PartialTyContains pt (.borrow mutable target) ∧
        LVal.base target = v)
    (by intro v hv; simp [Ty.vars] at hv)
    (by intro v hv; simp [Ty.vars] at hv)
    (by
      intro mutable target v hv
      simp [Ty.vars] at hv
      exact ⟨mutable, target, PartialTyContains.here, hv.symm⟩)
    (by
      intro inner ih v hv
      rcases ih v (by simpa [Ty.vars] using hv) with
        ⟨mutable, target, hcontains, hbase⟩
      exact ⟨mutable, target, PartialTyContains.tyBox hcontains, hbase⟩)
    (by
      intro ty ih v hv
      exact ih v (by simpa [PartialTy.vars] using hv))
    (by
      intro inner ih v hv
      rcases ih v (by simpa [PartialTy.vars] using hv) with
        ⟨mutable, target, hcontains, hbase⟩
      exact ⟨mutable, target, PartialTyContains.box hcontains, hbase⟩)
    (by intro shape _ih v hv; simp [PartialTy.vars] at hv)
    pt

theorem wellFormedTy_vars_in_env {env : Env} {ty : Ty} {lifetime : Lifetime} :
    WellFormedTy env ty lifetime →
    ∀ v, v ∈ Ty.vars ty → ∃ slot, env.slotAt v = some slot := by
  intro hwf v hv
  rcases partialTy_vars_mem_contains (pt := .ty ty) v
      (by simpa [PartialTy.vars] using hv) with
    ⟨mutable, target, hcontains, hbase⟩
  rcases borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwf hcontains with
    ⟨targetTy, targetLifetime, htyping, _houtlives, _hbaseOutlives⟩
  rw [← hbase]
  exact LValTyping.base_slot_exists htyping

theorem wellFormedTyWhenInitialized_vars_in_env {env : Env} {ty : Ty}
    {lifetime : Lifetime} :
    WellFormedTyWhenInitialized env ty lifetime →
    ∀ v, v ∈ Ty.vars ty → ∃ slot, env.slotAt v = some slot := by
  intro hwell
  induction hwell with
  | unit =>
      intro v hv
      simp [Ty.vars] at hv
  | int =>
      intro v hv
      simp [Ty.vars] at hv
  | borrow htarget =>
      intro v hv
      simp [Ty.vars] at hv
      subst hv
      rcases htarget with ⟨hbase, _hinitialized⟩
      exact hbase.elim (fun slot h => ⟨slot, h.1⟩)
  | box _ ih =>
      intro v hv
      exact ih v (by simpa [Ty.vars] using hv)

theorem containedBorrows_slot_vars_in_env {env : Env} {y : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    env.slotAt y = some slot →
    ∀ v, v ∈ PartialTy.vars slot.ty → ∃ baseSlot, env.slotAt v = some baseSlot := by
  intro hwell hslot v hv
  rcases partialTy_vars_mem_contains (pt := slot.ty) v hv with
    ⟨mutable, target, hcontains, hbase⟩
  rcases hwell y slot mutable target hslot ⟨slot, hslot, hcontains⟩ with
    ⟨targetTy, targetLifetime, htyping, _houtlives, _hbaseOutlives⟩
  rw [← hbase]
  exact LValTyping.base_slot_exists htyping

theorem containedBorrowsWhenInitialized_slot_vars_in_env {env : Env}
    {y : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.slotAt y = some slot →
    ∀ v, v ∈ PartialTy.vars slot.ty → ∃ baseSlot, env.slotAt v = some baseSlot := by
  intro hwell hslot v hv
  rcases partialTy_vars_mem_contains (pt := slot.ty) v hv with
    ⟨mutable, target, hcontains, hbase⟩
  rcases hwell y slot mutable target hslot ⟨slot, hslot, hcontains⟩ with
    ⟨hbaseOutlives, _hinitialized⟩
  rw [← hbase]
  exact hbaseOutlives.elim (fun baseSlot h => ⟨baseSlot, h.1⟩)

theorem mem_foldr_max_succ {l : List Name} {φ : Name → Nat} {v : Name}
    (hv : v ∈ l) :
    φ v + 1 ≤ l.foldr (fun w acc => max (φ w + 1) acc) 0 := by
  induction hv with
  | head as => exact le_max_left _ _
  | tail b _hmem ih => exact le_trans ih (le_max_right _ _)

theorem WellFormedEnv.update_fresh_ty {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    env.fresh x →
    WellFormedEnv (env.update x { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro hwellEnv hwellTy hfresh
  refine ⟨?_, ?_⟩
  · intro y envSlot mutable target hslot hcontains
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          envSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = envSlot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hcontainedEq :
          containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
          simpa [Env.update] using hcontainedSlot
        exact h.symm
      subst hcontainedEq
      exact borrowTargetsWellFormedInSlot_update_fresh
        (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
        (borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwellTy hcontainsTy)
    · have hslotOld : env.slotAt y = some envSlot := by
        simpa [Env.update, hy] using hslot
      have hcontainsOld : env ⊢ y ↝ Ty.borrow mutable target := by
        rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
        have hcontainedOld : env.slotAt y = some containedSlot := by
          simpa [Env.update, hy] using hcontainedSlot
        exact ⟨containedSlot, hcontainedOld, hcontainsTy⟩
      exact borrowTargetsWellFormedInSlot_update_fresh
        (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
        (hwellEnv.1 y envSlot mutable target hslotOld hcontainsOld)
  · intro y envSlot hslot
    by_cases hy : y = x
    · subst hy
      have hslotEq :
          envSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = envSlot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      simpa using LifetimeOutlives.refl lifetime
    · have hslotOld : env.slotAt y = some envSlot := by
        simpa [Env.update, hy] using hslot
      exact hwellEnv.2 y envSlot hslotOld

theorem EnvSlotsOutlive.update_same_lifetime {env : Env} {x : Name}
    {slot : EnvSlot} {current : Lifetime} :
    EnvSlotsOutlive env current →
    slot.lifetime ≤ current →
    EnvSlotsOutlive (env.update x slot) current := by
  intro houtlives hslotLife y updatedSlot hupdated
  by_cases hy : y = x
  · subst hy
    have hslotEq : updatedSlot = slot := by
      exact (Option.some.inj (by simpa [Env.update] using hupdated)).symm
    subst hslotEq
    exact hslotLife
  · have hslotOld : env.slotAt y = some updatedSlot := by
      simpa [Env.update, hy] using hupdated
    exact houtlives y updatedSlot hslotOld

theorem EnvSlotsOutlive.update_current {env : Env} {x : Name}
    {ty : PartialTy} {current : Lifetime} :
    EnvSlotsOutlive env current →
    EnvSlotsOutlive (env.update x { ty := ty, lifetime := current }) current := by
  intro houtlives
  exact EnvSlotsOutlive.update_same_lifetime houtlives
    (LifetimeOutlives.refl current)

theorem EnvSlotsOutlive.erase {env : Env} {x : Name} {current : Lifetime} :
    EnvSlotsOutlive env current →
    EnvSlotsOutlive (env.erase x) current := by
  intro houtlives y slot hslot
  by_cases hy : y = x
  · subst hy
    simp [Env.erase] at hslot
  · have hslotOld : env.slotAt y = some slot := by
      simpa [Env.erase, hy] using hslot
    exact houtlives y slot hslotOld

def EnvLifetimesPreserved (source result : Env) : Prop :=
  ∀ x resultSlot,
    result.slotAt x = some resultSlot →
    ∃ sourceSlot,
      source.slotAt x = some sourceSlot ∧
      sourceSlot.lifetime = resultSlot.lifetime

theorem EnvLifetimesPreserved.trans {first second third : Env} :
    EnvLifetimesPreserved first second →
    EnvLifetimesPreserved second third →
    EnvLifetimesPreserved first third := by
  intro hfs hst x thirdSlot hthird
  rcases hst x thirdSlot hthird with ⟨middleSlot, hmiddle, hmiddleLife⟩
  rcases hfs x middleSlot hmiddle with ⟨firstSlot, hfirst, hfirstLife⟩
  exact ⟨firstSlot, hfirst, hfirstLife.trans hmiddleLife⟩

theorem EnvStrengthens.lifetimesPreserved {source result : Env} :
    EnvStrengthens source result →
    EnvLifetimesPreserved source result := by
  intro hstrength x resultSlot hresult
  have hx := hstrength x
  cases hsource : source.slotAt x with
  | none =>
      rw [hsource, hresult] at hx
      exact False.elim hx
  | some sourceSlot =>
      rw [hsource, hresult] at hx
      exact ⟨sourceSlot, rfl, hx.1⟩

theorem EnvLifetimesPreserved.update_from_source_slot {source middle : Env}
    {x : Name} {sourceSlot : EnvSlot} {updatedTy : PartialTy} :
    EnvLifetimesPreserved source middle →
    source.slotAt x = some sourceSlot →
    EnvLifetimesPreserved source
      (middle.update x { sourceSlot with ty := updatedTy }) := by
  intro hpreserved hsource y rightSlot hright
  by_cases hy : y = x
  · subst hy
    have hrightEq : rightSlot = { sourceSlot with ty := updatedTy } := by
      exact (Option.some.inj (by simpa [Env.update] using hright)).symm
    subst hrightEq
    exact ⟨sourceSlot, hsource, rfl⟩
  · have hmiddle : middle.slotAt y = some rightSlot := by
      simpa [Env.update, hy] using hright
    exact hpreserved y rightSlot hmiddle

theorem EnvSlotsOutlive.of_lifetimesPreserved {source result : Env}
    {current : Lifetime} :
    EnvLifetimesPreserved source result →
    EnvSlotsOutlive source current →
    EnvSlotsOutlive result current := by
  intro hpreserved houtlives x resultSlot hresult
  rcases hpreserved x resultSlot hresult with ⟨sourceSlot, hsource, hlife⟩
  rw [← hlife]
  exact houtlives x sourceSlot hsource

theorem EnvMove.lifetimesSurvive {env moved : Env} {lv : LVal} :
    EnvMove env lv moved →
    EnvLifetimesPreserved env moved := by
  intro hmove
  rcases hmove with ⟨slot, struck, hslot, _hstrike, hmoved⟩
  subst hmoved
  exact EnvLifetimesPreserved.update_from_source_slot
    (fun x resultSlot hresult => ⟨resultSlot, hresult, rfl⟩)
    hslot

theorem LValBaseOutlives.move_of_not_pathConflicts {env env' : Env}
    {moved target : LVal} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ target ⋈ moved →
    LValBaseOutlives env target lifetime →
    LValBaseOutlives env' target lifetime := by
  intro hmove hnotConflict hbase
  rcases hbase with ⟨baseSlot, hbaseSlot, houtlives⟩
  rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv'⟩
  have hbaseNe : LVal.base target ≠ LVal.base moved := by
    intro hbaseEq
    exact hnotConflict hbaseEq
  exact ⟨baseSlot, by
      simpa [henv', Env.update, hbaseNe] using hbaseSlot,
    houtlives⟩

theorem LValBaseOutlives.dropLifetime_child {env : Env}
    {parent child lifetime : Lifetime} {target : LVal} :
    LifetimeChild parent child →
    lifetime ≤ parent →
    LValBaseOutlives env target lifetime →
    LValBaseOutlives (env.dropLifetime child) target lifetime := by
  intro hchild hlifetimeParent hbase
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  exact ⟨baseSlot,
    Env.dropLifetime_slotAt_eq_some.mpr
      ⟨hbaseSlot, by
        intro hbaseLifetime
        subst hbaseLifetime
        exact LifetimeChild.not_child_outlives_parent hchild
          (LifetimeOutlives.trans hbaseOutlives hlifetimeParent)⟩,
    hbaseOutlives⟩

theorem EnvSlotsOutlive.move {env env' : Env} {lv : LVal} {current : Lifetime} :
    EnvMove env lv env' →
    EnvSlotsOutlive env current →
    EnvSlotsOutlive env' current := by
  intro hmove houtlives
  exact EnvSlotsOutlive.of_lifetimesPreserved
    (EnvMove.lifetimesSurvive hmove) houtlives

theorem EnvSlotsOutlive.dropLifetime {env : Env} {dropped current : Lifetime} :
    EnvSlotsOutlive env current →
    EnvSlotsOutlive (env.dropLifetime dropped) current := by
  intro houtlives x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨horig, _hne⟩
  exact houtlives x slot horig

theorem EnvSlotsOutlive.dropLifetime_child {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    EnvSlotsOutlive env parent →
    EnvSlotsOutlive (env.dropLifetime child) parent := by
  intro _hchild houtlives
  exact EnvSlotsOutlive.dropLifetime houtlives

theorem LValTyping.lifetime_outlives_one {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    EnvSlotsOutlive env current →
    LValTyping env lv ty lifetime →
    lifetime ≤ current := by
  intro hslots htyping
  induction htyping with
  | var hslot => exact hslots _ _ hslot
  | box _ ih => exact ih
  | boxFull _ ih => exact ih
  | borrow _ _ _ ihTarget => exact ihTarget

theorem LValTyping.lifetime_outlives_one_of_slots {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    EnvSlotsOutlive env current →
    LValTyping env lv ty lifetime →
    lifetime ≤ current :=
  LValTyping.lifetime_outlives_one

theorem LValTyping.base_outlives_one {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    EnvSlotsOutlive env current →
    LValTyping env lv ty lifetime →
    LValBaseOutlives env lv current := by
  intro hslots htyping
  rcases LValTyping.base_slot_exists htyping with ⟨slot, hslot⟩
  exact ⟨slot, hslot, hslots _ _ hslot⟩

theorem LValTyping.base_outlives_one_of_slots {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    EnvSlotsOutlive env current →
    LValTyping env lv ty lifetime →
    LValBaseOutlives env lv current :=
  LValTyping.base_outlives_one

theorem LValTyping.var_inv {env : Env} {x : Name}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTyping env (.var x) partialTy lifetime →
    ∃ slot, env.slotAt x = some slot ∧
      partialTy = slot.ty ∧ lifetime = slot.lifetime := by
  intro htyping
  cases htyping with
  | var hslot => exact ⟨_, hslot, rfl, rfl⟩

end Paper
end FWRust
