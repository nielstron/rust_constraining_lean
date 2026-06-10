import LwRust.Paper.Soundness.Helpers.SafeAbstraction

/-!
# Soundness helpers: BorrowWellFormed

Section 4.3 machinery: contained-borrow well-formedness, borrow targets, the core well-formed-environment vocabulary.
-/

namespace LwRust
namespace Paper

open Core

/-! ## Section 4.3: Borrow Invariance

`BorrowSafeEnv` (Definition 4.13) itself lives in `LwRust.Paper.Typing`, since
the control-flow extension's `T-If` rule carries it as a join obligation. -/

theorem BorrowSafeEnv.same_root_of_mut_conflict {env : Env}
    {x y : Name} {mutable : Bool}
    {targetsMutable targetsOther : List LVal}
    {targetMutable targetOther : LVal} :
    BorrowSafeEnv env →
    env ⊢ x ↝ (&mut targetsMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    x = y := by
  intro hsafe hmutable hother htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    hmutable hother htargetMutable htargetOther hconflict

theorem BorrowSafeEnv.no_other_root_conflict {env : Env}
    {x y : Name} {mutable : Bool}
    {targetsMutable targetsOther : List LVal}
    {targetMutable targetOther : LVal} :
    BorrowSafeEnv env →
    x ≠ y →
    env ⊢ x ↝ (&mut targetsMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    ¬ targetMutable ⋈ targetOther := by
  intro hsafe hne hmutable hother htargetMutable htargetOther hconflict
  exact hne
    (BorrowSafeEnv.same_root_of_mut_conflict hsafe hmutable hother
      htargetMutable htargetOther hconflict)

theorem PathConflicts.symm {left right : LVal} :
    left ⋈ right →
    right ⋈ left := by
  intro h
  exact Eq.symm h

@[simp] theorem containedBorrowsWellFormed_empty :
    ContainedBorrowsWellFormed Env.empty := by
  intro x slot mutable targets hslot _hcontains
  simp [Env.empty] at hslot

@[simp] theorem envSlotsOutlive_empty (lifetime : Lifetime) :
    EnvSlotsOutlive Env.empty lifetime := by
  intro x slot hslot
  simp [Env.empty] at hslot

theorem lvalTyping_empty_false {lv : LVal} {p : PartialTy} {lf : Lifetime}
    (h : LValTyping Env.empty lv p lf) : False := by
  induction lv generalizing p lf with
  | var x => cases h with | var hslot => simp [Env.empty] at hslot
  | deref lv' ih =>
      cases h with
      | box hb => exact ih hb
      | borrow hb _ => exact ih hb

theorem coherent_empty : Coherent Env.empty := by
  intro lv m T bLf hty
  exact (lvalTyping_empty_false hty).elim

theorem linearizable_empty : Linearizable Env.empty :=
  ⟨fun _ => 0, by intro x slot hslot; simp [Env.empty] at hslot⟩

@[simp] theorem wellFormedEnv_empty (lifetime : Lifetime) :
    WellFormedEnv Env.empty lifetime := by
  exact ⟨containedBorrowsWellFormed_empty, envSlotsOutlive_empty lifetime,
    coherent_empty, linearizable_empty⟩

theorem wellFormedEnv_empty_all :
    ∀ lifetime, WellFormedEnv Env.empty lifetime := by
  intro lifetime
  exact wellFormedEnv_empty lifetime

theorem LValTyping.update_fresh {env : Env} {x : Name} {slot : EnvSlot} :
    env.fresh x →
    (∀ {lv ty lifetime},
      LValTyping env lv ty lifetime →
      LValTyping (env.update x slot) lv ty lifetime) ∧
    (∀ {targets ty lifetime},
    LValTargetsTyping env targets ty lifetime →
    LValTargetsTyping (env.update x slot) targets ty lifetime) := by
  intro hfresh
  constructor
  · intro lv ty lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv ty lifetime _ =>
        LValTyping (env.update x slot) lv ty lifetime)
      (motive_2 := fun targets ty lifetime _ =>
        LValTargetsTyping (env.update x slot) targets ty lifetime)
      (by
        intro y envSlot hslot
        by_cases h : y = x
        · subst h
          unfold Env.fresh at hfresh
          rw [hfresh] at hslot
          cases hslot
        · exact LValTyping.var (by simpa [Env.update, h]))
      (by
        intro lv inner lifetime _htyping ih
        exact LValTyping.box ih)
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          _hborrow _htargets ihBorrow ihTargets
        exact LValTyping.borrow ihBorrow ihTargets)
      (by
        intro target ty lifetime _htarget ihTarget
        exact LValTargetsTyping.singleton ihTarget)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest
        exact LValTargetsTyping.cons ihHead ihRest hunion hintersection)
      htyping
  · intro targets ty lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv ty lifetime _ =>
        LValTyping (env.update x slot) lv ty lifetime)
      (motive_2 := fun targets ty lifetime _ =>
        LValTargetsTyping (env.update x slot) targets ty lifetime)
      (by
        intro y envSlot hslot
        by_cases h : y = x
        · subst h
          unfold Env.fresh at hfresh
          rw [hfresh] at hslot
          cases hslot
        · exact LValTyping.var (by simpa [Env.update, h]))
      (by
        intro lv inner lifetime _htyping ih
        exact LValTyping.box ih)
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          _hborrow _htargets ihBorrow ihTargets
        exact LValTyping.borrow ihBorrow ihTargets)
      (by
        intro target ty lifetime _htarget ihTarget
        exact LValTargetsTyping.singleton ihTarget)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest
        exact LValTargetsTyping.cons ihHead ihRest hunion hintersection)
      htyping

theorem LValTyping.update_fresh_one {env : Env} {x : Name} {slot : EnvSlot}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    env.fresh x →
    LValTyping env lv ty lifetime →
    LValTyping (env.update x slot) lv ty lifetime := by
  intro hfresh htyping
  exact (LValTyping.update_fresh (slot := slot) hfresh).1 htyping

theorem LValTargetsTyping.update_fresh {env : Env} {x : Name} {slot : EnvSlot}
    {targets : List LVal} {ty : PartialTy} {lifetime : Lifetime} :
    env.fresh x →
    LValTargetsTyping env targets ty lifetime →
    LValTargetsTyping (env.update x slot) targets ty lifetime := by
  intro hfresh htyping
  exact (LValTyping.update_fresh (slot := slot) hfresh).2 htyping

/-- The target-list typing judgment is intentionally non-empty. -/
theorem LValTargetsTyping.nil_false {env : Env} {ty : PartialTy}
    {lifetime : Lifetime} :
    ¬ LValTargetsTyping env [] ty lifetime := by
  intro htyping
  cases htyping

theorem borrowTargetsWellFormedInSlot_update_fresh {env : Env} {x : Name}
    {slot : EnvSlot} {slotLifetime : Lifetime} {targets : List LVal} :
    env.fresh x →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    BorrowTargetsWellFormedInSlot (env.update x slot) slotLifetime targets := by
  intro hfresh htargets target hmem
  rcases htargets target hmem with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  refine ⟨targetTy, targetLifetime,
    LValTyping.update_fresh_one (slot := slot) hfresh htyping, houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  have hbaseSlot' :
      (env.update x slot).slotAt (LVal.base target) = some baseSlot := by
    have hbaseNe : LVal.base target ≠ x := by
      intro hbaseEq
      subst hbaseEq
      unfold Env.fresh at hfresh
      rw [hfresh] at hbaseSlot
      cases hbaseSlot
    simpa [Env.update, hbaseNe] using hbaseSlot
  exact ⟨baseSlot, hbaseSlot', hbaseOutlives⟩

theorem BorrowTargetsWellFormed.inSlot {env : Env} {targets : List LVal}
    {lifetime : Lifetime} :
    BorrowTargetsWellFormed env targets lifetime →
    BorrowTargetsWellFormedInSlot env lifetime targets := by
  intro htargets target hmem
  cases htargets with
  | intro hmembers => exact hmembers target hmem

theorem BorrowTargetsWellFormed.singleton {env : Env} {target : LVal}
    {targetTy : Ty} {targetLifetime lifetime : Lifetime} :
    LValTyping env target (.ty targetTy) targetLifetime →
    targetLifetime ≤ lifetime →
    LValBaseOutlives env target lifetime →
    BorrowTargetsWellFormed env [target] lifetime := by
  intro htarget houtlives hbase
  refine BorrowTargetsWellFormed.intro (by
    intro selected hselected
    simp at hselected
    subst hselected
    exact ⟨targetTy, targetLifetime, htarget, houtlives, hbase⟩)

theorem LifetimeOutlives.trans {first second third : Lifetime} :
    first ≤ second →
    second ≤ third →
    first ≤ third := by
  intro hfirst hsecond
  simp [LifetimeOutlives, Core.Lifetime.contains] at hfirst hsecond ⊢
  exact hfirst.trans hsecond

theorem LifetimeOutlives.antisymm {left right : Lifetime} :
    left ≤ right →
    right ≤ left →
    left = right := by
  intro hleftRight hrightLeft
  have hleftPrefix : left.path <+: right.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hleftRight
  have hrightPrefix : right.path <+: left.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hrightLeft
  have hpath : left.path = right.path :=
    hleftPrefix.eq_of_length (hleftPrefix.length_le.antisymm hrightPrefix.length_le)
  cases left
  cases right
  simp at hpath ⊢
  exact hpath

theorem LifetimeChild.outlives {parent child : Lifetime} :
    LifetimeChild parent child →
    parent ≤ child := by
  intro hchild
  rcases hchild with ⟨label, hpath⟩
  simp [LifetimeOutlives, Core.Lifetime.contains, hpath]

theorem LifetimeChild.ne {parent child : Lifetime} :
    LifetimeChild parent child →
    parent ≠ child := by
  intro hchild heq
  rcases hchild with ⟨label, hpath⟩
  have hlen := congrArg (fun lifetime : Lifetime => lifetime.path.length) heq
  simp [hpath] at hlen

theorem LifetimeChild.parent_of_outlives_child_ne {parent child slot : Lifetime} :
    LifetimeChild parent child →
    slot ≤ child →
    slot ≠ child →
    slot ≤ parent := by
  intro hchild hslot hne
  rcases hchild with ⟨label, hpath⟩
  have hslotPrefix : slot.path <+: child.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hslot
  have hparentPrefix : parent.path <+: child.path := by
    simp [hpath]
  have hslotLenLeChild : slot.path.length ≤ child.path.length :=
    hslotPrefix.length_le
  have hslotLenNeChild : slot.path.length ≠ child.path.length := by
    intro hlen
    have hpathEq : slot.path = child.path := hslotPrefix.eq_of_length hlen
    apply hne
    cases slot
    cases child
    simp at hpathEq ⊢
    exact hpathEq
  have hslotLenLtChild : slot.path.length < child.path.length :=
    Nat.lt_of_le_of_ne hslotLenLeChild hslotLenNeChild
  have hslotLenLeParent : slot.path.length ≤ parent.path.length := by
    rw [hpath, List.length_append] at hslotLenLtChild
    simp at hslotLenLtChild
    exact hslotLenLtChild
  have hslotParentPrefix : slot.path <+: parent.path :=
    List.prefix_of_prefix_length_le hslotPrefix hparentPrefix hslotLenLeParent
  simpa [LifetimeOutlives, Core.Lifetime.contains] using hslotParentPrefix

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
  exact ⟨hwell.1, EnvSlotsOutlive.weaken hwell.2.1 houterInner, hwell.2.2.1, hwell.2.2.2⟩

theorem BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed {env : Env}
    {targets : List LVal} {slotLifetime lifetime : Lifetime} :
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    slotLifetime ≤ lifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro htargets houtlives
  refine BorrowTargetsWellFormed.intro ?_
  intro target hmem
  rcases htargets target hmem with
    ⟨targetTy, targetLifetime, htargetTyping, htargetOutlivesSlot, hbase⟩
  refine ⟨targetTy, targetLifetime, htargetTyping,
    LifetimeOutlives.trans htargetOutlivesSlot houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  exact ⟨baseSlot, hbaseSlot, LifetimeOutlives.trans hbaseOutlives houtlives⟩

theorem EnvContains.borrowTargetsWellFormed {env : Env} {x : Name}
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    env ⊢ x ↝ Ty.borrow mutable targets →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
    (hwellFormed.1 x slot mutable targets hslot ⟨slot, hslot, hcontainsTy⟩)
    (hwellFormed.2.1 x slot hslot)

theorem BorrowTargetsWellFormed.member {env : Env} {targets : List LVal}
    {lifetime : Lifetime} :
    BorrowTargetsWellFormed env targets lifetime →
    ∀ target,
      target ∈ targets →
      ∃ targetTy targetLifetime,
        LValTyping env target (.ty targetTy) targetLifetime ∧
        targetLifetime ≤ lifetime ∧
        LValBaseOutlives env target lifetime := by
  intro htargets target hmem
  cases htargets with
  | intro hmembers => exact hmembers target hmem

theorem BorrowTargetsWellFormed.weaken {env : Env} {targets : List LVal}
    {outer inner : Lifetime} :
    BorrowTargetsWellFormed env targets outer →
      outer ≤ inner →
      BorrowTargetsWellFormed env targets inner := by
    intro htargets houterInner
    cases htargets with
    | intro hmembers =>
        refine BorrowTargetsWellFormed.intro ?_
        intro target htarget
        rcases hmembers target htarget with
          ⟨targetTy, targetLifetime, htyping, htOutlives, hbase⟩
        refine ⟨targetTy, targetLifetime, htyping,
          LifetimeOutlives.trans htOutlives houterInner, ?_⟩
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        exact ⟨baseSlot, hbaseSlot,
          LifetimeOutlives.trans hbaseOutlives houterInner⟩

theorem BorrowTargetsWellFormedInSlot.weaken {env : Env} {targets : List LVal}
    {outer inner : Lifetime} :
    BorrowTargetsWellFormedInSlot env outer targets →
    outer ≤ inner →
    BorrowTargetsWellFormedInSlot env inner targets := by
  intro htargets houtlives target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htargetTyping, htargetOutlives, hbase⟩
  refine ⟨targetTy, targetLifetime, htargetTyping,
    LifetimeOutlives.trans htargetOutlives houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  exact ⟨baseSlot, hbaseSlot, LifetimeOutlives.trans hbaseOutlives houtlives⟩

theorem PartialTyBorrowsWellFormedInSlot.weaken {env : Env}
    {partialTy : PartialTy} {outer inner : Lifetime} :
    PartialTyBorrowsWellFormedInSlot env outer partialTy →
    outer ≤ inner →
    PartialTyBorrowsWellFormedInSlot env inner partialTy := by
  intro hpartial houtlives mutable targets hcontains
  exact BorrowTargetsWellFormedInSlot.weaken (hpartial hcontains) houtlives

theorem WellFormedTy.weaken {env : Env} {ty : Ty} {outer inner : Lifetime} :
    WellFormedTy env ty outer →
    outer ≤ inner →
    WellFormedTy env ty inner := by
  intro hwell houtlives
  induction hwell with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | bool =>
      exact WellFormedTy.bool
  | borrow htargets =>
      exact WellFormedTy.borrow (BorrowTargetsWellFormed.weaken htargets houtlives)
  | box _hinner ih =>
      exact WellFormedTy.box (ih houtlives)

theorem borrowTargetsWellFormedInSlot_of_wellFormedTy_contains {env : Env}
    {ty : Ty} {lifetime : Lifetime} {mutable : Bool} {targets : List LVal} :
    WellFormedTy env ty lifetime →
    PartialTyContains (.ty ty) (.borrow mutable targets) →
    BorrowTargetsWellFormedInSlot env lifetime targets := by
  intro hwellTy hcontains
  cases hcontains with
  | here =>
      cases hwellTy with
      | borrow htargets =>
          exact BorrowTargetsWellFormed.inSlot htargets
  | tyBox hinner =>
      cases hwellTy with
      | box hwellInner =>
          exact borrowTargetsWellFormedInSlot_of_wellFormedTy_contains
            hwellInner hinner

theorem PartialTyBorrowsWellFormedInSlot.of_wellFormedTy {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedTy env ty lifetime →
    PartialTyBorrowsWellFormedInSlot env lifetime (.ty ty) := by
  intro hwellTy mutable targets hcontains
  exact borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwellTy hcontains

theorem PartialTyBorrowsWellFormedInSlot.box {env : Env}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    PartialTyBorrowsWellFormedInSlot env lifetime partialTy →
    PartialTyBorrowsWellFormedInSlot env lifetime (.box partialTy) := by
  intro hpartial mutable targets hcontains
  cases hcontains with
  | box hinner =>
      exact hpartial hinner

theorem PartialTyBorrowsWellFormedInSlot.box_inv {env : Env}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    PartialTyBorrowsWellFormedInSlot env lifetime (.box partialTy) →
    PartialTyBorrowsWellFormedInSlot env lifetime partialTy := by
  intro hpartial mutable targets hcontains
  exact hpartial (PartialTyContains.box hcontains)

/-- Every lval typing has a base variable slot. -/
theorem LValTyping.base_slot_exists {env : Env} :
    ∀ {lv : LVal} {p : PartialTy} {lf : Lifetime}, LValTyping env lv p lf →
      ∃ slot, env.slotAt (LVal.base lv) = some slot := by
  intro lv
  induction lv with
  | var x =>
      intro p lf h
      cases h with | var hslot => exact ⟨_, by simpa [LVal.base] using hslot⟩
  | deref lv' ih =>
      intro p lf h
      cases h with
      | box hb => simpa [LVal.base] using ih hb
      | borrow hb _ => simpa [LVal.base] using ih hb

/-- A variable in a (partial) type's `vars` comes from a contained borrow whose
target it is the base of.  (`Ty`/`PartialTy` are mutually inductive, so the proof
goes through the shared recursor.) -/
theorem partialTy_vars_mem_contains {pt : PartialTy} :
    ∀ v, v ∈ PartialTy.vars pt →
      ∃ mutable targets, PartialTyContains pt (.borrow mutable targets) ∧
        ∃ tgt, tgt ∈ targets ∧ LVal.base tgt = v :=
  PartialTy.rec
    (motive_1 := fun t => ∀ v, v ∈ Ty.vars t →
      ∃ mutable targets, PartialTyContains (.ty t) (.borrow mutable targets) ∧
        ∃ tgt, tgt ∈ targets ∧ LVal.base tgt = v)
    (motive_2 := fun pt => ∀ v, v ∈ PartialTy.vars pt →
      ∃ mutable targets, PartialTyContains pt (.borrow mutable targets) ∧
        ∃ tgt, tgt ∈ targets ∧ LVal.base tgt = v)
    (by intro v hv; simp [Ty.vars] at hv)
    (by intro v hv; simp [Ty.vars] at hv)
    (by
      intro m tgts v hv
      simp only [Ty.vars, List.mem_map] at hv
      obtain ⟨tgt, htgt, rfl⟩ := hv
      exact ⟨m, tgts, PartialTyContains.here, tgt, htgt, rfl⟩)
    (by
      intro inner ih v hv
      simp only [Ty.vars] at hv
      obtain ⟨m, tgts, hcontains, tgt, htgt, hbase⟩ := ih v hv
      exact ⟨m, tgts, PartialTyContains.tyBox hcontains, tgt, htgt, hbase⟩)
    (by intro v hv; simp [Ty.vars] at hv)
    (by intro t ih v hv; exact ih v (by simpa [PartialTy.vars] using hv))
    (by
      intro p ih v hv
      simp only [PartialTy.vars] at hv
      obtain ⟨m, tgts, hcontains, w⟩ := ih v hv
      exact ⟨m, tgts, PartialTyContains.box hcontains, w⟩)
    (by intro s _ih v hv;
        exact (List.not_mem_nil (show v ∈ ([] : List Name) from hv)).elim)
    pt

/--
If a mutable-borrow target's base occurs in another root's type, borrow safety
forces that root to be the mutable-borrow authority itself.
-/
theorem BorrowSafeEnv.same_root_of_mut_target_var {env : Env}
    {authority y : Name} {targetsMutable : List LVal} {targetMutable : LVal}
    {slot : EnvSlot} :
    BorrowSafeEnv env →
    env ⊢ authority ↝ (&mut targetsMutable) →
    targetMutable ∈ targetsMutable →
    env.slotAt y = some slot →
    LVal.base targetMutable ∈ PartialTy.vars slot.ty →
    authority = y := by
  intro hsafe hmut htargetMutable hslotY hvars
  rcases partialTy_vars_mem_contains (pt := slot.ty)
      (LVal.base targetMutable) hvars with
    ⟨mutable, targetsOther, hcontainsOther, targetOther, htargetOther,
      hbaseOther⟩
  exact BorrowSafeEnv.same_root_of_mut_conflict hsafe hmut
    ⟨slot, hslotY, hcontainsOther⟩ htargetMutable htargetOther
    (by simp [PathConflicts, hbaseOther])

theorem BorrowSafeEnv.no_other_root_mut_target_var {env : Env}
    {authority y : Name} {targetsMutable : List LVal} {targetMutable : LVal}
    {slot : EnvSlot} :
    BorrowSafeEnv env →
    authority ≠ y →
    env ⊢ authority ↝ (&mut targetsMutable) →
    targetMutable ∈ targetsMutable →
    env.slotAt y = some slot →
    ¬ LVal.base targetMutable ∈ PartialTy.vars slot.ty := by
  intro hsafe hne hmut htargetMutable hslotY hvars
  exact hne
    (BorrowSafeEnv.same_root_of_mut_target_var hsafe hmut htargetMutable
      hslotY hvars)

/--
If a variable at the base of a known mutable-borrow target is write-prohibited,
then every borrow witness responsible for that prohibition lives in the mutable
borrow's authority root.
-/
theorem BorrowSafeEnv.writeProhibited_var_witness_root_of_mut_target
    {env : Env} {authority witness : Name}
    {targetsMutable targetsOther : List LVal} {targetMutable targetOther : LVal}
    {mutable : Bool} :
    BorrowSafeEnv env →
    env ⊢ authority ↝ (&mut targetsMutable) →
    targetMutable ∈ targetsMutable →
    env ⊢ witness ↝ (Ty.borrow mutable targetsOther) →
    targetOther ∈ targetsOther →
    targetOther ⋈ (.var (LVal.base targetMutable)) →
    authority = witness := by
  intro hsafe hmut htargetMutable hother htargetOther hconflict
  exact BorrowSafeEnv.same_root_of_mut_conflict hsafe hmut hother
    htargetMutable htargetOther (by
      simpa [PathConflicts, LVal.base] using hconflict.symm)

theorem BorrowSafeEnv.writeProhibited_var_of_mut_target_authority
    {env : Env} {authority : Name}
    {targetsMutable : List LVal} {targetMutable : LVal} :
    BorrowSafeEnv env →
    env ⊢ authority ↝ (&mut targetsMutable) →
    targetMutable ∈ targetsMutable →
    WriteProhibited env (.var (LVal.base targetMutable)) →
    ∃ mutable targetsOther targetOther,
      env ⊢ authority ↝ (Ty.borrow mutable targetsOther) ∧
        targetOther ∈ targetsOther ∧
        targetOther ⋈ (.var (LVal.base targetMutable)) := by
  intro hsafe hmut htargetMutable hwrite
  cases hwrite with
  | inl hread =>
      rcases hread with
        ⟨witness, targetsOther, targetOther, hother, htargetOther,
          hconflict⟩
      have hauthority :
          authority = witness :=
        BorrowSafeEnv.writeProhibited_var_witness_root_of_mut_target
          hsafe hmut htargetMutable hother htargetOther hconflict
      subst hauthority
      exact ⟨true, targetsOther, targetOther, hother, htargetOther,
        hconflict⟩
  | inr himm =>
      rcases himm with
        ⟨witness, targetsOther, targetOther, hother, htargetOther,
          hconflict⟩
      have hauthority :
          authority = witness :=
        BorrowSafeEnv.writeProhibited_var_witness_root_of_mut_target
          hsafe hmut htargetMutable hother htargetOther hconflict
      subst hauthority
      exact ⟨false, targetsOther, targetOther, hother, htargetOther,
        hconflict⟩

/-- Variables occurring in a well-formed type are bound in the environment (each
is the base of a borrow target, which types in `env`). -/
theorem wellFormedTy_vars_in_env {env : Env} {ty : Ty} {lifetime : Lifetime} :
    WellFormedTy env ty lifetime →
    ∀ v, v ∈ Ty.vars ty → ∃ slot, env.slotAt v = some slot := by
  intro hwf v hv
  obtain ⟨m, tgts, hcontains, tgt, htgt, hbase⟩ :=
    partialTy_vars_mem_contains (pt := .ty ty) v (by simpa [PartialTy.vars] using hv)
  obtain ⟨T, lt, hty, _, _⟩ :=
    borrowTargetsWellFormedInSlot_of_wellFormedTy_contains hwf hcontains tgt htgt
  rw [← hbase]
  exact LValTyping.base_slot_exists hty

/-- Variables in a slot's type of a contained-borrow-well-formed env are bound. -/
theorem containedBorrows_slot_vars_in_env {env : Env} {y : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    env.slotAt y = some slot →
    ∀ v, v ∈ PartialTy.vars slot.ty → ∃ s, env.slotAt v = some s := by
  intro hcontained hslot v hv
  obtain ⟨m, tgts, hcontains, tgt, htgt, hbase⟩ := partialTy_vars_mem_contains v hv
  have hwf := hcontained y slot m tgts hslot ⟨slot, hslot, hcontains⟩
  obtain ⟨T, lt, hty, _, _⟩ := hwf tgt htgt
  rw [← hbase]
  exact LValTyping.base_slot_exists hty

/-- Membership bound for the fresh-variable rank: every listed variable's
`φ + 1` is below the fold-max. -/
theorem mem_foldr_max_succ {l : List Name} {φ : Name → Nat} {v : Name}
    (hv : v ∈ l) :
    φ v + 1 ≤ l.foldr (fun w acc => max (φ w + 1) acc) 0 := by
  induction hv with
  | head as => exact le_max_left _ _
  | tail b _hmem ih => exact le_trans ih (le_max_right _ _)

/-- Explicit declaration-coherence obligation.

`WellFormedTy` carries the paper's per-target borrow invariant.  The mechanised
`Coherent` invariant is stronger: it asks for joint target-list typing for every
borrow that can be reached by lvalue typing.  A fresh declaration of a full type
therefore needs this extra closure fact; it is named here rather than hidden as a
local proof hole inside `WellFormedEnv.update_fresh_ty`.

This is not merely syntactic coherence of borrows contained in `ty`: after
declaring `x : &targets`, lvals such as `*x` can expose the joint target-list
union, and if that union is itself a borrow then `Coherent` needs coherence for
that exposed borrow as well.  The eventual proof should thread a lvalue-level
"declared type is coherent under the current environment" invariant through
term typing, not derive it from `WellFormedTy` alone.

As stated, this obligation is stronger than `WellFormedTy`: for example,
`WellFormedTy.borrow` accepts `&[]` vacuously, while
`LValTargetsTyping.nil_false` shows that no empty target list is jointly
typeable.  The valid replacement requires the lvalue-level
`FreshUpdateCoherenceObligations` side condition below. -/
theorem Coherent.update_fresh_ty {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    Coherent env →
    env.fresh x →
    FreshUpdateCoherenceObligations env x ty lifetime →
    Coherent (env.update x { ty := .ty ty, lifetime := lifetime })
    := by
  intro hcoh hfresh hobligations lv mutable targets borrowLifetime htyping
  by_cases hbase : LVal.base lv = x
  · exact hobligations.fresh_root_coherent hbase htyping
  · rcases hobligations.old_root_transport hbase htyping with
      ⟨oldBorrowLifetime, htypingOld⟩
    rcases hcoh lv mutable targets oldBorrowLifetime htypingOld with
      ⟨targetTy, targetLifetime, htargetsOld⟩
    exact ⟨targetTy, targetLifetime,
      LValTargetsTyping.update_fresh
        (slot := { ty := .ty ty, lifetime := lifetime }) hfresh htargetsOld⟩

/-- Bare `Coherent.update_fresh_ty` is false: `WellFormedTy` accepts `&[]`
vacuously, but coherence requires the target list to be jointly typeable, and
`LValTargetsTyping` is intentionally non-empty. -/
theorem Coherent.update_fresh_ty_bare_counterexample :
    ∃ env x ty lifetime,
      Coherent env ∧ WellFormedTy env ty lifetime ∧ env.fresh x ∧
        ¬ Coherent (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  refine ⟨Env.empty, "x", .borrow false [], Lifetime.root, ?_, ?_, ?_, ?_⟩
  · exact (wellFormedEnv_empty Lifetime.root).2.2.1
  · exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
      intro target htarget
      simp at htarget))
  · simp [Env.fresh, Env.empty]
  · intro hcoh
    have hx :
        (Env.empty.update "x"
          { ty := .ty (.borrow false []), lifetime := Lifetime.root }).slotAt "x" =
          some { ty := .ty (.borrow false []), lifetime := Lifetime.root } := by
      simp [Env.update]
    have htyping :
        LValTyping
          (Env.empty.update "x"
            { ty := .ty (.borrow false []), lifetime := Lifetime.root })
          (.var "x") (.ty (.borrow false [])) Lifetime.root :=
      LValTyping.var hx
    rcases hcoh (.var "x") false [] Lifetime.root htyping with
      ⟨targetTy, targetLifetime, htargets⟩
    exact LValTargetsTyping.nil_false htargets

theorem Coherent.update_fresh_ty_of_obligations {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    Coherent env →
    env.fresh x →
    FreshUpdateCoherenceObligations env x ty lifetime →
    Coherent (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  exact Coherent.update_fresh_ty

theorem WellFormedEnv.update_fresh_ty {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    env.fresh x →
    FreshUpdateCoherenceObligations env x ty lifetime →
    WellFormedEnv (env.update x { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro hwellEnv hwellTy hfresh hcohObligations
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y envSlot mutable targets hslot hcontains
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
      have hcontainsOld : env ⊢ y ↝ Ty.borrow mutable targets := by
        rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
        have hcontainedOld : env.slotAt y = some containedSlot := by
          simpa [Env.update, hy] using hcontainedSlot
        exact ⟨containedSlot, hcontainedOld, hcontainsTy⟩
      exact borrowTargetsWellFormedInSlot_update_fresh
        (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
        (hwellEnv.1 y envSlot mutable targets hslotOld hcontainsOld)
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
      exact LifetimeOutlives.refl lifetime
    · have hslotOld : env.slotAt y = some envSlot := by
        simpa [Env.update, hy] using hslot
      exact hwellEnv.2.1 y envSlot hslotOld
  · exact Coherent.update_fresh_ty hwellEnv.2.2.1 hfresh hcohObligations
  · -- Linearizable: rank the fresh variable strictly above the variables of its
    -- slot type (a finite list); existing ranks unchanged.
    obtain ⟨φ, hφ⟩ := hwellEnv.2.2.2
    have hfreshEq : env.slotAt x = none := hfresh
    have hxnotin : x ∉ Ty.vars ty := by
      intro hx
      obtain ⟨s, hs⟩ := wellFormedTy_vars_in_env hwellTy x hx
      rw [hfreshEq] at hs
      exact absurd hs (by simp)
    refine ⟨fun n => if n = x then
      (Ty.vars ty).foldr (fun w acc => max (φ w + 1) acc) 0 else φ n, ?_⟩
    intro y slot hslot v hv
    by_cases hy : y = x
    · have hslotEq : slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        rw [hy] at hslot
        simpa [Env.update] using hslot.symm
      have hvty : v ∈ Ty.vars ty := by
        rw [hslotEq] at hv; simpa [PartialTy.vars] using hv
      have hvx : v ≠ x := fun h => hxnotin (h ▸ hvty)
      simp only [if_neg hvx, if_pos hy]
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (mem_foldr_max_succ hvty)
    · have hslotOld : env.slotAt y = some slot := by
        simpa [Env.update, hy] using hslot
      obtain ⟨s, hs⟩ := containedBorrows_slot_vars_in_env hwellEnv.1 hslotOld v hv
      have hvx : v ≠ x := by
        intro h; rw [h, hfreshEq] at hs; exact absurd hs (by simp)
      simp only [if_neg hy, if_neg hvx]
      exact hφ y slot hslotOld v hv

/--
Fresh full-type update preserving well-formedness with the declaration
coherence gap made explicit.

This is the proved replacement for uses that should not depend on the false
bare `Coherent.update_fresh_ty` obligation.
-/
theorem WellFormedEnv.update_fresh_ty_of_coherenceObligations {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    env.fresh x →
    FreshUpdateCoherenceObligations env x ty lifetime →
    WellFormedEnv (env.update x { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro hwellEnv hwellTy hfresh hcohObligations
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y envSlot mutable targets hslot hcontains
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
      have hcontainsOld : env ⊢ y ↝ Ty.borrow mutable targets := by
        rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
        have hcontainedOld : env.slotAt y = some containedSlot := by
          simpa [Env.update, hy] using hcontainedSlot
        exact ⟨containedSlot, hcontainedOld, hcontainsTy⟩
      exact borrowTargetsWellFormedInSlot_update_fresh
        (slot := { ty := .ty ty, lifetime := lifetime }) hfresh
        (hwellEnv.1 y envSlot mutable targets hslotOld hcontainsOld)
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
      exact LifetimeOutlives.refl lifetime
    · have hslotOld : env.slotAt y = some envSlot := by
        simpa [Env.update, hy] using hslot
      exact hwellEnv.2.1 y envSlot hslotOld
  · exact Coherent.update_fresh_ty_of_obligations
      hwellEnv.2.2.1 hfresh hcohObligations
  · obtain ⟨φ, hφ⟩ := hwellEnv.2.2.2
    have hfreshEq : env.slotAt x = none := hfresh
    have hxnotin : x ∉ Ty.vars ty := by
      intro hx
      obtain ⟨s, hs⟩ := wellFormedTy_vars_in_env hwellTy x hx
      rw [hfreshEq] at hs
      exact absurd hs (by simp)
    refine ⟨fun n => if n = x then
      (Ty.vars ty).foldr (fun w acc => max (φ w + 1) acc) 0 else φ n, ?_⟩
    intro y slot hslot v hv
    by_cases hy : y = x
    · have hslotEq : slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        rw [hy] at hslot
        simpa [Env.update] using hslot.symm
      have hvty : v ∈ Ty.vars ty := by
        rw [hslotEq] at hv; simpa [PartialTy.vars] using hv
      have hvx : v ≠ x := fun h => hxnotin (h ▸ hvty)
      simp only [if_neg hvx, if_pos hy]
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (mem_foldr_max_succ hvty)
    · have hslotOld : env.slotAt y = some slot := by
        simpa [Env.update, hy] using hslot
      obtain ⟨s, hs⟩ := containedBorrows_slot_vars_in_env hwellEnv.1 hslotOld v hv
      have hvx : v ≠ x := by
        intro h; rw [h, hfreshEq] at hs; exact absurd hs (by simp)
      simp only [if_neg hy, if_neg hvx]
      exact hφ y slot hslotOld v hv

/-- Updating a variable slot without changing its allocation lifetime preserves Definition 4.8(ii). -/
theorem EnvSlotsOutlive.update_same_lifetime {env : Env} {x : Name}
    {slot : EnvSlot} {newTy : PartialTy} {current : Lifetime} :
    EnvSlotsOutlive env current →
    env.slotAt x = some slot →
    EnvSlotsOutlive (env.update x { slot with ty := newTy }) current := by
  intro houtlives hslot y updatedSlot hupdated
  by_cases hy : y = x
  · subst hy
    have hupdatedSlot :
        updatedSlot = { slot with ty := newTy } := by
      have h :
          { slot with ty := newTy } = updatedSlot := by
        simpa [Env.update] using hupdated
      exact h.symm
    subst hupdatedSlot
    exact houtlives _ slot hslot
  · have hold : env.slotAt y = some updatedSlot := by
      simpa [Env.update, hy] using hupdated
    exact houtlives y updatedSlot hold

/--
An environment update relation preserves the allocation lifetime of every slot
that remains in the result.  This isolates the domain/lifetime part of
Appendix Lemma 9.6 from the borrow-target obligations.
-/
def EnvLifetimesPreserved (source result : Env) : Prop :=
  ∀ x resultSlot,
    result.slotAt x = some resultSlot →
    ∃ sourceSlot,
      source.slotAt x = some sourceSlot ∧
      sourceSlot.lifetime = resultSlot.lifetime

@[refl] theorem EnvLifetimesPreserved.refl (env : Env) :
    EnvLifetimesPreserved env env := by
  intro x slot hslot
  exact ⟨slot, hslot, rfl⟩

theorem EnvLifetimesPreserved.trans {first second third : Env} :
    EnvLifetimesPreserved first second →
    EnvLifetimesPreserved second third →
    EnvLifetimesPreserved first third := by
  intro hfirstSecond hsecondThird x slot hslot
  rcases hsecondThird x slot hslot with ⟨secondSlot, hsecondSlot, hlifetime₂⟩
  rcases hfirstSecond x secondSlot hsecondSlot with
    ⟨firstSlot, hfirstSlot, hlifetime₁⟩
  exact ⟨firstSlot, hfirstSlot, by rw [hlifetime₁, hlifetime₂]⟩

theorem EnvStrengthens.lifetimesPreserved {source result : Env} :
    EnvStrengthens source result →
    EnvLifetimesPreserved source result := by
  intro hstrength x resultSlot hresultSlot
  have hx := hstrength x
  cases hsource : source.slotAt x with
  | none =>
      simp [hsource, hresultSlot] at hx
  | some sourceSlot =>
      simp [hsource, hresultSlot] at hx
      exact ⟨sourceSlot, by simp, hx.1⟩

theorem EnvJoin.lifetimesPreserved_left {left right join : Env} :
    EnvJoin left right join →
    EnvLifetimesPreserved left join := by
  intro hjoin
  exact EnvStrengthens.lifetimesPreserved
    (hjoin.1 (by simp))

theorem EnvJoin.lifetimesPreserved_right {left right join : Env} :
    EnvJoin left right join →
    EnvLifetimesPreserved right join := by
  intro hjoin
  exact EnvStrengthens.lifetimesPreserved
    (hjoin.1 (by simp))

theorem EnvLifetimesPreserved.update_from_source_slot {source middle : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvLifetimesPreserved source middle →
    source.slotAt x = some slot →
    EnvLifetimesPreserved source
      (middle.update x { slot with ty := newTy }) := by
  intro hpreserved hslot y resultSlot hresultSlot
  by_cases hy : y = x
  · subst hy
    have hresultSlotEq : resultSlot = { slot with ty := newTy } := by
      have h :
          { slot with ty := newTy } = resultSlot := by
        simpa [Env.update] using hresultSlot
      exact h.symm
    subst hresultSlotEq
    exact ⟨slot, hslot, rfl⟩
  · have hmiddleSlot : middle.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresultSlot
    exact hpreserved y resultSlot hmiddleSlot

theorem EnvSlotsOutlive.of_lifetimesPreserved {source result : Env}
    {current : Lifetime} :
    EnvSlotsOutlive source current →
    EnvLifetimesPreserved source result →
    EnvSlotsOutlive result current := by
  intro houtlives hpreserved x slot hslot
  rcases hpreserved x slot hslot with
    ⟨sourceSlot, hsourceSlot, hlifetime⟩
  rw [← hlifetime]
  exact houtlives x sourceSlot hsourceSlot

theorem UpdateWrite.lifetimesPreserved :
    (∀ {rank env₁ path oldTy ty env₂ updatedTy},
      UpdateAtPath rank env₁ path oldTy ty env₂ updatedTy →
      EnvLifetimesPreserved env₁ env₂) ∧
    (∀ {rank env path targets ty result},
      WriteBorrowTargets rank env path targets ty result →
      EnvLifetimesPreserved env result) ∧
    (∀ {rank env lv ty result},
      EnvWrite rank env lv ty result →
      EnvLifetimesPreserved env result) := by
  constructor
  · intro rank env₁ path oldTy ty env₂ updatedTy hupdate
    exact UpdateAtPath.rec
      (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
        EnvLifetimesPreserved env₁ env₂)
      (motive_2 := fun _rank env _path _targets _ty result _ =>
        EnvLifetimesPreserved env result)
      (motive_3 := fun _rank env _lv _ty result _ =>
        EnvLifetimesPreserved env result)
      (by
        intro env old ty
        exact EnvLifetimesPreserved.refl env)
      (by
        intro env rank old joined ty _hshape _hjoinTy
        exact EnvLifetimesPreserved.refl env)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
        exact ih)
      (by
        intro env₁ env₂ rank path targets ty _hwrites ih
        exact ih)
      (by
        intro rank env path ty
        exact EnvLifetimesPreserved.refl env)
      (by
        intro rank env updated path target ty _hwrite _htyped ih
        exact ih)
      (by
        intro rank env updated restEnv result path target rest ty
          _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
        exact EnvLifetimesPreserved.trans ihWrite
          (EnvJoin.lifetimesPreserved_left hjoin))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
        exact EnvLifetimesPreserved.update_from_source_slot ih hslot)
      hupdate
  · constructor
    · intro rank env path targets ty result hwrites
      exact WriteBorrowTargets.rec
        (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
          EnvLifetimesPreserved env₁ env₂)
        (motive_2 := fun _rank env _path _targets _ty result _ =>
          EnvLifetimesPreserved env result)
        (motive_3 := fun _rank env _lv _ty result _ =>
          EnvLifetimesPreserved env result)
        (by
          intro env old ty
          exact EnvLifetimesPreserved.refl env)
        (by
          intro env rank old joined ty _hshape _hjoinTy
          exact EnvLifetimesPreserved.refl env)
        (by
          intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
          exact ih)
        (by
          intro env₁ env₂ rank path targets ty _hwrites ih
          exact ih)
        (by
          intro rank env path ty
          exact EnvLifetimesPreserved.refl env)
        (by
          intro rank env updated path target ty _hwrite _htyped ih
          exact ih)
        (by
          intro rank env updated restEnv result path target rest ty
            _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
          exact EnvLifetimesPreserved.trans ihWrite
            (EnvJoin.lifetimesPreserved_left hjoin))
        (by
          intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
          exact EnvLifetimesPreserved.update_from_source_slot ih hslot)
        hwrites
    · intro rank env lv ty result hwrite
      exact EnvWrite.rec
        (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
          EnvLifetimesPreserved env₁ env₂)
        (motive_2 := fun _rank env _path _targets _ty result _ =>
          EnvLifetimesPreserved env result)
        (motive_3 := fun _rank env _lv _ty result _ =>
          EnvLifetimesPreserved env result)
        (by
          intro env old ty
          exact EnvLifetimesPreserved.refl env)
        (by
          intro env rank old joined ty _hshape _hjoinTy
          exact EnvLifetimesPreserved.refl env)
        (by
          intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
          exact ih)
        (by
          intro env₁ env₂ rank path targets ty _hwrites ih
          exact ih)
        (by
          intro rank env path ty
          exact EnvLifetimesPreserved.refl env)
        (by
          intro rank env updated path target ty _hwrite _htyped ih
          exact ih)
        (by
          intro rank env updated restEnv result path target rest ty
            _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
          exact EnvLifetimesPreserved.trans ihWrite
            (EnvJoin.lifetimesPreserved_left hjoin))
        (by
          intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
          exact EnvLifetimesPreserved.update_from_source_slot ih hslot)
        hwrite

theorem EnvWrite.lifetimesPreserved {rank : Nat} {env : Env} {lv : LVal}
    {ty : Ty} {result : Env} :
    EnvWrite rank env lv ty result →
    EnvLifetimesPreserved env result :=
  UpdateWrite.lifetimesPreserved.2.2

theorem UpdateAtPath.cons_inv {rank : Nat} {env₁ env₂ : Env}
    {path : List Unit} {oldTy : PartialTy} {ty : Ty}
    {updatedTy : PartialTy} :
    UpdateAtPath rank env₁ (() :: path) oldTy ty env₂ updatedTy →
    (∃ inner updatedInner,
      oldTy = .box inner ∧
      updatedTy = .box updatedInner ∧
      UpdateAtPath rank env₁ path inner ty env₂ updatedInner) ∨
    (∃ targets,
      oldTy = .ty (.borrow true targets) ∧
      updatedTy = .ty (.borrow true targets) ∧
      WriteBorrowTargets (rank + 1) env₁ path targets ty env₂) := by
  intro hupdate
  cases hupdate with
  | box hinner =>
      exact Or.inl ⟨_, _, rfl, rfl, hinner⟩
  | mutBorrow hwrites =>
      exact Or.inr ⟨_, rfl, rfl, hwrites⟩

@[simp] theorem List.Unit_append_singleton (path : List Unit) :
    path ++ [()] = () :: path := by
  induction path with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head
      simp [ih]

@[simp] theorem LVal.path_deref_cons (lv : LVal) :
    LVal.path (.deref lv) = () :: LVal.path lv := by
  simp [LVal.path]

theorem EnvWrite.preserves_slotsOutlive {rank : Nat} {env result : Env}
    {lv : LVal} {ty : Ty} {current : Lifetime} :
    EnvSlotsOutlive env current →
    EnvWrite rank env lv ty result →
    EnvSlotsOutlive result current := by
  intro houtlives hwrite
  exact EnvSlotsOutlive.of_lifetimesPreserved houtlives
    (EnvWrite.lifetimesPreserved hwrite)

def EnvLifetimesSurvive (source result : Env) : Prop :=
  ∀ x sourceSlot,
    source.slotAt x = some sourceSlot →
    ∃ resultSlot,
      result.slotAt x = some resultSlot ∧
      sourceSlot.lifetime = resultSlot.lifetime

@[refl] theorem EnvLifetimesSurvive.refl (env : Env) :
    EnvLifetimesSurvive env env := by
  intro x slot hslot
  exact ⟨slot, hslot, rfl⟩

theorem EnvLifetimesSurvive.trans {first second third : Env} :
    EnvLifetimesSurvive first second →
    EnvLifetimesSurvive second third →
    EnvLifetimesSurvive first third := by
  intro hfirstSecond hsecondThird x slot hslot
  rcases hfirstSecond x slot hslot with ⟨secondSlot, hsecondSlot, hlifetime₁⟩
  rcases hsecondThird x secondSlot hsecondSlot with
    ⟨thirdSlot, hthirdSlot, hlifetime₂⟩
  exact ⟨thirdSlot, hthirdSlot, by rw [hlifetime₁, hlifetime₂]⟩

theorem EnvStrengthens.lifetimesSurvive {source result : Env} :
    EnvStrengthens source result →
    EnvLifetimesSurvive source result := by
  intro hstrength x sourceSlot hsourceSlot
  have hx := hstrength x
  cases hresult : result.slotAt x with
  | none =>
      simp [hsourceSlot, hresult] at hx
  | some resultSlot =>
      simp [hsourceSlot, hresult] at hx
      exact ⟨resultSlot, by simp, hx.1⟩

theorem EnvJoin.lifetimesSurvive_left {left right join : Env} :
    EnvJoin left right join →
    EnvLifetimesSurvive left join := by
  intro hjoin
  exact EnvStrengthens.lifetimesSurvive
    (hjoin.1 (by simp))

theorem EnvJoin.lifetimesSurvive_right {left right join : Env} :
    EnvJoin left right join →
    EnvLifetimesSurvive right join := by
  intro hjoin
  exact EnvStrengthens.lifetimesSurvive
    (hjoin.1 (by simp))

theorem EnvLifetimesSurvive.update_from_source_slot {source middle : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvLifetimesSurvive source middle →
    source.slotAt x = some slot →
    EnvLifetimesSurvive source
      (middle.update x { slot with ty := newTy }) := by
  intro hsurvive hslot y sourceSlot hsourceSlot
  by_cases hy : y = x
  · subst hy
    have hsourceSlotEq : sourceSlot = slot := by
      have hsomeEq : some sourceSlot = some slot := by
        rw [← hsourceSlot, hslot]
      exact Option.some.inj hsomeEq
    exact ⟨{ slot with ty := newTy }, by simp [Env.update], by
      rw [hsourceSlotEq]⟩
  · rcases hsurvive y sourceSlot hsourceSlot with
      ⟨middleSlot, hmiddleSlot, hlifetime⟩
    exact ⟨middleSlot, by simpa [Env.update, hy] using hmiddleSlot, hlifetime⟩

theorem UpdateWrite.lifetimesSurvive :
    (∀ {rank env₁ path oldTy ty env₂ updatedTy},
      UpdateAtPath rank env₁ path oldTy ty env₂ updatedTy →
      EnvLifetimesSurvive env₁ env₂) ∧
    (∀ {rank env path targets ty result},
      WriteBorrowTargets rank env path targets ty result →
      EnvLifetimesSurvive env result) ∧
    (∀ {rank env lv ty result},
      EnvWrite rank env lv ty result →
      EnvLifetimesSurvive env result) := by
  constructor
  · intro rank env₁ path oldTy ty env₂ updatedTy hupdate
    exact UpdateAtPath.rec
      (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
        EnvLifetimesSurvive env₁ env₂)
      (motive_2 := fun _rank env _path _targets _ty result _ =>
        EnvLifetimesSurvive env result)
      (motive_3 := fun _rank env _lv _ty result _ =>
        EnvLifetimesSurvive env result)
      (by
        intro env old ty
        exact EnvLifetimesSurvive.refl env)
      (by
        intro env rank old joined ty _hshape _hjoinTy
        exact EnvLifetimesSurvive.refl env)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
        exact ih)
      (by
        intro env₁ env₂ rank path targets ty _hwrites ih
        exact ih)
      (by
        intro rank env path ty
        exact EnvLifetimesSurvive.refl env)
      (by
        intro rank env updated path target ty _hwrite _htyped ih
        exact ih)
      (by
        intro rank env updated restEnv result path target rest ty
          _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
        exact EnvLifetimesSurvive.trans ihWrite
          (EnvJoin.lifetimesSurvive_left hjoin))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
        exact EnvLifetimesSurvive.update_from_source_slot ih hslot)
      hupdate
  · constructor
    · intro rank env path targets ty result hwrites
      exact WriteBorrowTargets.rec
        (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
          EnvLifetimesSurvive env₁ env₂)
        (motive_2 := fun _rank env _path _targets _ty result _ =>
          EnvLifetimesSurvive env result)
        (motive_3 := fun _rank env _lv _ty result _ =>
          EnvLifetimesSurvive env result)
        (by
          intro env old ty
          exact EnvLifetimesSurvive.refl env)
        (by
          intro env rank old joined ty _hshape _hjoinTy
          exact EnvLifetimesSurvive.refl env)
        (by
          intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
          exact ih)
        (by
          intro env₁ env₂ rank path targets ty _hwrites ih
          exact ih)
        (by
          intro rank env path ty
          exact EnvLifetimesSurvive.refl env)
        (by
          intro rank env updated path target ty _hwrite _htyped ih
          exact ih)
        (by
          intro rank env updated restEnv result path target rest ty
            _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
          exact EnvLifetimesSurvive.trans ihWrite
            (EnvJoin.lifetimesSurvive_left hjoin))
        (by
          intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
          exact EnvLifetimesSurvive.update_from_source_slot ih hslot)
        hwrites
    · intro rank env lv ty result hwrite
      exact EnvWrite.rec
        (motive_1 := fun _rank env₁ _path _oldTy _ty env₂ _updatedTy _ =>
          EnvLifetimesSurvive env₁ env₂)
        (motive_2 := fun _rank env _path _targets _ty result _ =>
          EnvLifetimesSurvive env result)
        (motive_3 := fun _rank env _lv _ty result _ =>
          EnvLifetimesSurvive env result)
        (by
          intro env old ty
          exact EnvLifetimesSurvive.refl env)
        (by
          intro env rank old joined ty _hshape _hjoinTy
          exact EnvLifetimesSurvive.refl env)
        (by
          intro env₁ env₂ rank path inner updatedInner ty _hupdate ih
          exact ih)
        (by
          intro env₁ env₂ rank path targets ty _hwrites ih
          exact ih)
        (by
          intro rank env path ty
          exact EnvLifetimesSurvive.refl env)
        (by
          intro rank env updated path target ty _hwrite _htyped ih
          exact ih)
        (by
          intro rank env updated restEnv result path target rest ty
            _hwrite _htyped _hwrites hjoin ihWrite _ihWrites
          exact EnvLifetimesSurvive.trans ihWrite
            (EnvJoin.lifetimesSurvive_left hjoin))
        (by
          intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
          exact EnvLifetimesSurvive.update_from_source_slot ih hslot)
        hwrite

theorem EnvWrite.lifetimesSurvive {rank : Nat} {env : Env} {lv : LVal}
    {ty : Ty} {result : Env} :
    EnvWrite rank env lv ty result →
    EnvLifetimesSurvive env result :=
  UpdateWrite.lifetimesSurvive.2.2

theorem EnvMove.lifetimesSurvive {env moved : Env} {lv : LVal} :
    EnvMove env lv moved →
    EnvLifetimesSurvive env moved := by
  intro hmove x sourceSlot hsourceSlot
  rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, hmoved⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hsourceSlotEq : sourceSlot = moveSlot := by
      have hsomeEq : some sourceSlot = some moveSlot := by
        rw [← hsourceSlot, hmoveSlot]
      exact Option.some.inj hsomeEq
    exact ⟨{ moveSlot with ty := struck }, by simp [hmoved, Env.update], by
      rw [hsourceSlotEq]⟩
  · exact ⟨sourceSlot, by simpa [hmoved, Env.update, hx] using hsourceSlot, rfl⟩

theorem LValBaseOutlives.write {rank : Nat} {env result : Env}
    {written lv : LVal} {ty : Ty} {current : Lifetime} :
    EnvWrite rank env written ty result →
    LValBaseOutlives env lv current →
    LValBaseOutlives result lv current := by
  intro hwrite hbase
  rcases hbase with ⟨slot, hslot, houtlives⟩
  rcases EnvWrite.lifetimesSurvive hwrite (LVal.base lv) slot hslot with
    ⟨resultSlot, hresultSlot, hlifetime⟩
  exact ⟨resultSlot, hresultSlot, by rw [← hlifetime]; exact houtlives⟩

theorem TermTyping.slot_lifetime_survives :
    (∀ {env₁ typing lifetime term ty env₂},
      TermTyping env₁ typing lifetime term ty env₂ →
      ∀ {x sourceSlot},
        sourceSlot.lifetime ≤ lifetime →
        env₁.slotAt x = some sourceSlot →
        ∃ resultSlot,
          env₂.slotAt x = some resultSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime) ∧
    (∀ {env₁ typing lifetime terms ty env₂},
      TermListTyping env₁ typing lifetime terms ty env₂ →
      ∀ {x sourceSlot},
        sourceSlot.lifetime ≤ lifetime →
        env₁.slotAt x = some sourceSlot →
        ∃ resultSlot,
          env₂.slotAt x = some resultSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime) := by
  constructor
  · intro env₁ typing lifetime term ty env₂ htyping
    exact TermTyping.rec
      (motive_1 := fun env₁ _typing lifetime _term _ty env₂ _ =>
        ∀ {x sourceSlot},
          sourceSlot.lifetime ≤ lifetime →
          env₁.slotAt x = some sourceSlot →
          ∃ resultSlot,
            env₂.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
      (motive_2 := fun env₁ _typing lifetime _terms _ty env₂ _ =>
        ∀ {x sourceSlot},
          sourceSlot.lifetime ≤ lifetime →
          env₁.slotAt x = some sourceSlot →
          ∃ resultSlot,
            env₂.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
      (by
        intro _env _typing _lifetime _value _ty _hvalue x sourceSlot
          _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _ty _hwellTy x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hcopy _hnotRead
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty
          _hLv _hnotWrite hmove x sourceSlot _houtlives hslot
        exact EnvMove.lifetimesSurvive hmove x sourceSlot hslot)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hmutable _hnotWrite
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hnotRead
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih
          x sourceSlot houtlives hslot
        exact ih houtlives hslot)
      (by
        intro _env₁ _env₂ _env₃ _typing lifetime blockLifetime _terms _ty
          hchild _hterms _hwellTy hdrop ih x sourceSlot houtlives hslot
        rcases ih (LifetimeOutlives.trans houtlives (LifetimeChild.outlives hchild))
            hslot with
          ⟨bodySlot, hbodySlot, hbodyLifetime⟩
        subst hdrop
        have hbodyNotDropped : bodySlot.lifetime ≠ blockLifetime := by
          intro hdropped
          have hchildOutlivesParent : blockLifetime ≤ lifetime := by
            rw [← hdropped, ← hbodyLifetime]
            exact houtlives
          exact LifetimeChild.not_child_outlives_parent hchild hchildOutlivesParent
        exact ⟨bodySlot,
          Env.dropLifetime_slotAt_eq_some.mpr ⟨hbodySlot, hbodyNotDropped⟩,
          hbodyLifetime⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing lifetime y _term _ty
          hfresh _hterm _hfreshOut _hcoh henv₃ ih x sourceSlot houtlives hslot
        subst henv₃
        by_cases hxy : x = y
        · subst hxy
          rw [hfresh] at hslot
          cases hslot
        · rcases ih houtlives hslot with ⟨innerSlot, hinnerSlot, hlifetime⟩
          exact ⟨innerSlot, by simpa [Env.update, hxy] using hinnerSlot, hlifetime⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy
          _hLhs _hRhs _hLhsPost _hshape _hwellRhs hwrite _hranked _hcoh _hcontained
          _hnotWrite ih x sourceSlot houtlives hslot
        rcases ih houtlives hslot with ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
        rcases EnvWrite.lifetimesSurvive hwrite x rhsSlot hrhsSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hrhsLifetime, hresultLifetime]⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _lhs _rhs _lhsTy _rhsTy
          _hLhs _hRhs _hcopyLhs _hcopyRhs _hshape ihLhs ihRhs
          x sourceSlot houtlives hslot
        rcases ihLhs houtlives hslot with ⟨midSlot, hmidSlot, hmidLifetime⟩
        have hmidOutlives : midSlot.lifetime ≤ _lifetime := by
          rw [← hmidLifetime]
          exact houtlives
        rcases ihRhs hmidOutlives hmidSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hmidLifetime, hresultLifetime]⟩)
      (by
        intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
          _trueBranch _falseBranch _trueTy _falseTy _joinTy _hcond _htrue _hfalse
          _htyJoin hjoin _hshapeTrue _hshapeFalse _hwellJoin _hcontained _hcoherent _hlin
          _hborrowSafe _hresultSafe ihCond ihTrue _ihFalse x sourceSlot houtlives hslot
        rcases ihCond houtlives hslot with ⟨condSlot, hcondSlot, hcondLifetime⟩
        have hcondOutlives : condSlot.lifetime ≤ _lifetime := by
          rw [← hcondLifetime]
          exact houtlives
        rcases ihTrue hcondOutlives hcondSlot with
          ⟨trueSlot, htrueSlot, htrueLifetime⟩
        rcases (EnvJoin.left_le hjoin).slot_forward htrueSlot with
          ⟨joinSlot, hjoinSlot, hjoinLifetime, _⟩
        exact ⟨joinSlot, hjoinSlot, by
          rw [hcondLifetime, htrueLifetime, hjoinLifetime]⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih
          x sourceSlot houtlives hslot
        exact ih houtlives hslot)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
          _hterm _hrest ihHead ihRest x sourceSlot houtlives hslot
        rcases ihHead houtlives hslot with ⟨midSlot, hmidSlot, hmidLifetime⟩
        have hmidOutlives : midSlot.lifetime ≤ _lifetime := by
          rw [← hmidLifetime]
          exact houtlives
        rcases ihRest hmidOutlives hmidSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hmidLifetime, hresultLifetime]⟩)
      htyping

  · intro env₁ typing lifetime terms ty env₂ htyping
    exact TermListTyping.rec
      (motive_1 := fun env₁ _typing lifetime _term _ty env₂ _ =>
        ∀ {x sourceSlot},
          sourceSlot.lifetime ≤ lifetime →
          env₁.slotAt x = some sourceSlot →
          ∃ resultSlot,
            env₂.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
      (motive_2 := fun env₁ _typing lifetime _terms _ty env₂ _ =>
        ∀ {x sourceSlot},
          sourceSlot.lifetime ≤ lifetime →
          env₁.slotAt x = some sourceSlot →
          ∃ resultSlot,
            env₂.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
      (by
        intro _env _typing _lifetime _value _ty _hvalue x sourceSlot
          _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _ty _hwellTy x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hcopy _hnotRead
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty
          _hLv _hnotWrite hmove x sourceSlot _houtlives hslot
        exact EnvMove.lifetimesSurvive hmove x sourceSlot hslot)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hmutable _hnotWrite
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hnotRead
          x sourceSlot _houtlives hslot
        exact ⟨sourceSlot, hslot, rfl⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih
          x sourceSlot houtlives hslot
        exact ih houtlives hslot)
      (by
        intro _env₁ _env₂ _env₃ _typing lifetime blockLifetime _terms _ty
          hchild _hterms _hwellTy hdrop ih x sourceSlot houtlives hslot
        rcases ih (LifetimeOutlives.trans houtlives (LifetimeChild.outlives hchild))
            hslot with
          ⟨bodySlot, hbodySlot, hbodyLifetime⟩
        subst hdrop
        have hbodyNotDropped : bodySlot.lifetime ≠ blockLifetime := by
          intro hdropped
          have hchildOutlivesParent : blockLifetime ≤ lifetime := by
            rw [← hdropped, ← hbodyLifetime]
            exact houtlives
          exact LifetimeChild.not_child_outlives_parent hchild hchildOutlivesParent
        exact ⟨bodySlot,
          Env.dropLifetime_slotAt_eq_some.mpr ⟨hbodySlot, hbodyNotDropped⟩,
          hbodyLifetime⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing lifetime y _term _ty
          hfresh _hterm _hfreshOut _hcoh henv₃ ih x sourceSlot houtlives hslot
        subst henv₃
        by_cases hxy : x = y
        · subst hxy
          rw [hfresh] at hslot
          cases hslot
        · rcases ih houtlives hslot with ⟨innerSlot, hinnerSlot, hlifetime⟩
          exact ⟨innerSlot, by simpa [Env.update, hxy] using hinnerSlot, hlifetime⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy
          _hLhs _hRhs _hLhsPost _hshape _hwellRhs hwrite _hranked _hcoh _hcontained
          _hnotWrite ih x sourceSlot houtlives hslot
        rcases ih houtlives hslot with ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
        rcases EnvWrite.lifetimesSurvive hwrite x rhsSlot hrhsSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hrhsLifetime, hresultLifetime]⟩)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _lhs _rhs _lhsTy _rhsTy
          _hLhs _hRhs _hcopyLhs _hcopyRhs _hshape ihLhs ihRhs
          x sourceSlot houtlives hslot
        rcases ihLhs houtlives hslot with ⟨midSlot, hmidSlot, hmidLifetime⟩
        have hmidOutlives : midSlot.lifetime ≤ _lifetime := by
          rw [← hmidLifetime]
          exact houtlives
        rcases ihRhs hmidOutlives hmidSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hmidLifetime, hresultLifetime]⟩)
      (by
        intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
          _trueBranch _falseBranch _trueTy _falseTy _joinTy _hcond _htrue _hfalse
          _htyJoin hjoin _hshapeTrue _hshapeFalse _hwellJoin _hcontained _hcoherent _hlin
          _hborrowSafe _hresultSafe ihCond ihTrue _ihFalse x sourceSlot houtlives hslot
        rcases ihCond houtlives hslot with ⟨condSlot, hcondSlot, hcondLifetime⟩
        have hcondOutlives : condSlot.lifetime ≤ _lifetime := by
          rw [← hcondLifetime]
          exact houtlives
        rcases ihTrue hcondOutlives hcondSlot with
          ⟨trueSlot, htrueSlot, htrueLifetime⟩
        rcases (EnvJoin.left_le hjoin).slot_forward htrueSlot with
          ⟨joinSlot, hjoinSlot, hjoinLifetime, _⟩
        exact ⟨joinSlot, hjoinSlot, by
          rw [hcondLifetime, htrueLifetime, hjoinLifetime]⟩)
      (by
        intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih
          x sourceSlot houtlives hslot
        exact ih houtlives hslot)
      (by
        intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
          _hterm _hrest ihHead ihRest x sourceSlot houtlives hslot
        rcases ihHead houtlives hslot with ⟨midSlot, hmidSlot, hmidLifetime⟩
        have hmidOutlives : midSlot.lifetime ≤ _lifetime := by
          rw [← hmidLifetime]
          exact houtlives
        rcases ihRest hmidOutlives hmidSlot with
          ⟨resultSlot, hresultSlot, hresultLifetime⟩
        exact ⟨resultSlot, hresultSlot, by rw [hmidLifetime, hresultLifetime]⟩)
      htyping

theorem LValBaseOutlives.termTyping {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime current : Lifetime}
    {term : Term} {ty : Ty} {lv : LVal} :
    TermTyping env₁ typing lifetime term ty env₂ →
    LValBaseOutlives env₁ lv current →
    current ≤ lifetime →
    LValBaseOutlives env₂ lv current := by
  intro htyping hbase hcurrent
  rcases hbase with ⟨sourceSlot, hsourceSlot, hsourceOutlives⟩
  rcases (TermTyping.slot_lifetime_survives.1 htyping)
      (LifetimeOutlives.trans hsourceOutlives hcurrent)
      hsourceSlot with
    ⟨resultSlot, hresultSlot, hresultLifetime⟩
  exact ⟨resultSlot, hresultSlot, by rw [← hresultLifetime]; exact hsourceOutlives⟩

/-- Definition 3.18 `move(Γ,w)` preserves the lifetime of every surviving slot. -/
theorem EnvSlotsOutlive.move {env env' : Env} {lv : LVal}
    {current : Lifetime} :
    EnvSlotsOutlive env current →
    EnvMove env lv env' →
    EnvSlotsOutlive env' current := by
  intro houtlives hmove
  rcases hmove with ⟨slot, struck, hslot, _hstrike, henv'⟩
  rw [henv']
  exact EnvSlotsOutlive.update_same_lifetime houtlives hslot

/-- Definition 3.20 `drop(Γ,m)` preserves Definition 4.8(ii) for surviving slots. -/
theorem EnvSlotsOutlive.dropLifetime {env : Env} {dropped current : Lifetime} :
    EnvSlotsOutlive env current →
    EnvSlotsOutlive (env.dropLifetime dropped) current := by
  intro houtlives x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨hold, _hnotDropped⟩
  exact houtlives x slot hold

theorem EnvSlotsOutlive.dropLifetime_child {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    EnvSlotsOutlive env child →
    EnvSlotsOutlive (env.dropLifetime child) parent := by
  intro hchild houtlives x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨hold, hnotDropped⟩
  exact LifetimeChild.parent_of_outlives_child_ne hchild
    (houtlives x slot hold) hnotDropped

/--
The final environment-extension step used by Lemma 4.9, Borrow Invariance:
once the type computed by the typing derivation is well formed in the output
environment, adding a fresh result slot preserves well-formedness.
-/
theorem borrowInvariance_result_extension {env₂ : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime := by
  exact WellFormedEnv.update_fresh_ty

/--
Final environment-extension step with fresh-slot coherence made explicit.

This avoids the legacy `Coherent.update_fresh_ty` shortcut by requiring the local
fresh-update coherence obligations for the result binding.
-/
theorem borrowInvariance_result_extension_of_coherenceObligations
    {env₂ : Env} {gamma : Name} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  exact WellFormedEnv.update_fresh_ty_of_coherenceObligations

theorem LifetimeIntersection.le_of_le {left right intersection current : Lifetime} :
    LifetimeIntersection left right intersection →
    left ≤ current →
    right ≤ current →
    intersection ≤ current := by
  intro hintersection hleft hright
  exact hintersection.2 (by
    intro lifetime hmem
    simp at hmem
    rcases hmem with h | h
    · simpa [h] using hleft
    · simpa [h] using hright)

theorem LifetimeIntersection.left_le {left right intersection : Lifetime} :
    LifetimeIntersection left right intersection →
    left ≤ intersection := by
  intro hintersection
  exact hintersection.1 (by simp)

theorem LifetimeIntersection.right_le {left right intersection : Lifetime} :
    LifetimeIntersection left right intersection →
    right ≤ intersection := by
  intro hintersection
  exact hintersection.1 (by simp)

theorem LifetimeIntersection.unique {left right first second : Lifetime} :
    LifetimeIntersection left right first →
    LifetimeIntersection left right second →
    first = second := by
  intro hfirst hsecond
  exact LifetimeOutlives.antisymm
    (hfirst.2 hsecond.1)
    (hsecond.2 hfirst.1)

theorem LifetimeOutlives.comparable_of_common_inner {left right current : Lifetime} :
    left ≤ current →
    right ≤ current →
    left ≤ right ∨ right ≤ left := by
  intro hleft hright
  have hleftPrefix : left.path <+: current.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hleft
  have hrightPrefix : right.path <+: current.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hright
  rcases Nat.le_total left.path.length right.path.length with hlen | hlen
  · have hprefix : left.path <+: right.path :=
      List.prefix_of_prefix_length_le hleftPrefix hrightPrefix hlen
    exact Or.inl (by
      simpa [LifetimeOutlives, Core.Lifetime.contains] using hprefix)
  · have hprefix : right.path <+: left.path :=
      List.prefix_of_prefix_length_le hrightPrefix hleftPrefix hlen
    exact Or.inr (by
      simpa [LifetimeOutlives, Core.Lifetime.contains] using hprefix)

theorem LifetimeIntersection.exists_of_common_inner {left right current : Lifetime} :
    left ≤ current →
    right ≤ current →
    ∃ intersection, LifetimeIntersection left right intersection := by
  intro hleft hright
  rcases LifetimeOutlives.comparable_of_common_inner hleft hright with
    hleftRight | hrightLeft
  · exact ⟨right, LifetimeIntersection.left hleftRight⟩
  · exact ⟨left, LifetimeIntersection.right hrightLeft⟩

theorem LValTargetsTyping.member_lifetime_outlives {env : Env}
    {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime current : Lifetime} :
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ current →
    ∀ target,
      target ∈ targets →
      ∃ targetTy selectedLifetime,
        LValTyping env target (.ty targetTy) selectedLifetime ∧
        selectedLifetime ≤ current := by
  intro htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets _partialTy targetLifetime _ =>
      targetLifetime ≤ current →
      ∀ target,
        target ∈ targets →
        ∃ targetTy selectedLifetime,
          LValTyping env target (.ty targetTy) selectedLifetime ∧
          selectedLifetime ≤ current)
    ?var ?box ?borrow ?singleton ?cons htyping houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget houtlives selected hmem
    simp at hmem
    subst hmem
    exact ⟨ty, lifetime, htarget, houtlives⟩
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest _hunion hintersection _ihHead ihRest houtlives selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ⟨headTy, headLifetime, hhead,
        LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives⟩
    · exact ihRest
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives)
        selected hselected

theorem LValTyping.lifetime_outlives {env : Env} {current : Lifetime} :
    WellFormedEnv env current →
    (∀ {lv ty lifetime},
      LValTyping env lv ty lifetime →
      lifetime ≤ current) ∧
    (∀ {targets ty lifetime},
      LValTargetsTyping env targets ty lifetime →
      lifetime ≤ current) := by
  intro hwellEnv
  constructor
  · intro lv ty lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun _lv _ty lifetime _ => lifetime ≤ current)
      (motive_2 := fun _targets _ty lifetime _ => lifetime ≤ current)
      (by
        intro x slot hslot
        exact hwellEnv.2.1 x slot hslot)
      (by
        intro _lv _inner _lifetime _htyping ih
        exact ih)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets
        exact ihTargets)
      (by
        intro _target _ty _lifetime _htarget ihTarget
        exact ihTarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest
        exact LifetimeIntersection.le_of_le hintersection ihHead ihRest)
      htyping
  · intro targets ty lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv _ty lifetime _ => lifetime ≤ current)
      (motive_2 := fun _targets _ty lifetime _ => lifetime ≤ current)
      (by
        intro x slot hslot
        exact hwellEnv.2.1 x slot hslot)
      (by
        intro _lv _inner _lifetime _htyping ih
        exact ih)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets
        exact ihTargets)
      (by
        intro _target _ty _lifetime _htarget ihTarget
        exact ihTarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest
        exact LifetimeIntersection.le_of_le hintersection ihHead ihRest)
      htyping

theorem LValTyping.lifetime_outlives_one {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    LValTyping env lv ty lifetime →
    lifetime ≤ current := by
  intro hwellEnv htyping
  exact (LValTyping.lifetime_outlives hwellEnv).1 htyping

/-- The lifetime bound `lifetime ≤ current` for a typed lval needs only
`EnvSlotsOutlive env current` (every slot lives at least as long as `current`):
the lval's lifetime is the LUB of the base slots its borrow chain bottoms out at,
each bounded by `current`.  This is the `EnvSlotsOutlive`-only core of
`lifetime_outlives_one`, used to discharge the deref-borrow join lifetime bound
without circular appeal to `ContainedBorrows join`. -/
theorem LValTyping.lifetime_le_of_slotsOutlive {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime}
    (houtlive : EnvSlotsOutlive env current)
    (htyping : LValTyping env lv ty lifetime) :
    lifetime ≤ current := by
  exact LValTyping.rec
    (motive_1 := fun _lv _ty lifetime _ => lifetime ≤ current)
    (motive_2 := fun _targets _ty lifetime _ => lifetime ≤ current)
    (by intro x slot hslot; exact houtlive x slot hslot)
    (by intro _lv _inner _lifetime _htyping ih; exact ih)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets _ihBorrow ihTargets
      exact ihTargets)
    (by intro _target _ty _lifetime _htarget ihTarget; exact ihTarget)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
        _hhead _hrest _hunion hintersection ihHead ihRest
      exact LifetimeIntersection.le_of_le hintersection ihHead ihRest)
    htyping

/-- A target-list typing's union lifetime is bounded by `bound` whenever every
member lval's own typing lifetime is.  The union lifetime is the iterated LUB
(`LifetimeIntersection`) of the members, so it is `≤ bound` exactly when `bound`
is an upper bound of all members (`LifetimeIntersection.le_of_le`).  This is the
per-member fold used by the deref-borrow lifetime bound in the φ-stratified
join/contained-borrow bootstrap. -/
theorem lvalTargetsTyping_le_of_members {e : Env} {bound : Lifetime}
    {T : List LVal} {pt : PartialTy} {lf : Lifetime}
    (htgts : LValTargetsTyping e T pt lf)
    (hmem : ∀ t, t ∈ T → ∀ tt tlf, LValTyping e t (.ty tt) tlf → tlf ≤ bound) :
    lf ≤ bound := by
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _pt _lf _ => True)
    (motive_2 := fun T _pt lf _ =>
      (∀ t, t ∈ T → ∀ tt tlf, LValTyping e t (.ty tt) tlf → tlf ≤ bound) → lf ≤ bound)
    ?var ?box ?borrow ?singleton ?cons htgts hmem
  case var => intros; trivial
  case box => intros; trivial
  case borrow => intros; trivial
  case singleton =>
      intro target ty lifetime htarget _ih hmem
      exact hmem target (by simp) _ _ htarget
  case cons =>
      intro target rest headTy headLife restLife life restTy unionTy
        hhead _hrest hunion hintersection _ihHead ihRest hmem
      exact LifetimeIntersection.le_of_le hintersection
        (hmem target (by simp) _ _ hhead)
        (ihRest (fun t ht => hmem t (List.mem_cons_of_mem _ ht)))

/-- Structural classification of a typed lval: either a needle borrow occurring
in its partial type is `PartialTyContains`-reachable from the *base slot* (the
lval's spine is var/box only, so the borrow is slot-contained), or the spine
passes through a borrow dereference (a reborrow `*u`, with `u` a borrow lval of
the same base, hence same rank).  This is the case split the contained-borrow
bootstrap needs to know whether `ContainedBorrowsWellFormed` applies directly or
the φ-recursion must descend through `u`. -/
theorem lvalTyping_contained_or_reborrow {e : Env} :
    ∀ (lv : LVal) {pt : PartialTy} {lf : Lifetime} {needle : Ty},
      LValTyping e lv pt lf → PartialTyContains pt needle →
      (∃ bs, e.slotAt (LVal.base lv) = some bs ∧ PartialTyContains bs.ty needle) ∨
      (∃ u m0 T0 blf0, LVal.base u = LVal.base lv ∧
        LValTyping e u (.ty (.borrow m0 T0)) blf0) := by
  intro lv
  induction lv with
  | var x =>
      intro pt lf needle h hcontains
      cases h with
      | var hslot => exact Or.inl ⟨_, hslot, hcontains⟩
  | deref lv0 ih =>
      intro pt lf needle h hcontains
      cases h with
      | box hbox =>
          rcases ih hbox (PartialTyContains.box hcontains) with hc | hr
          · left; simpa [LVal.base] using hc
          · right
            rcases hr with ⟨u, m0, T0, blf0, hbase, htyp⟩
            exact ⟨u, m0, T0, blf0, by simpa [LVal.base] using hbase, htyp⟩
      | borrow hbor _htgts =>
          right
          exact ⟨lv0, _, _, _, by simp [LVal.base], hbor⟩

theorem LValTyping.base_outlives_one {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    LValTyping env lv ty lifetime →
    LValBaseOutlives env lv current := by
  intro hwellEnv htyping
  exact LValTyping.rec
    (motive_1 := fun lv _ty _lifetime _ => LValBaseOutlives env lv current)
    (motive_2 := fun _targets _ty _lifetime _ => True)
    (by
      intro x slot hslot
      exact ⟨slot, hslot, hwellEnv.2.1 x slot hslot⟩)
    (by
      intro _lv _inner _lifetime _htyping ih
      exact ih)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets ihBorrow _ihTargets
      exact ihBorrow)
    (by
      intro _target _ty _lifetime _htarget _ihTarget
      trivial)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
        _hhead _hrest _hunion _hintersection _ihHead _ihRest
      trivial)
    htyping

theorem EnvWrite.writeSlot_outlives_current_lifetime {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ∃ writeSlot,
      env₂.slotAt (LVal.base lhs) = some writeSlot ∧
      writeSlot.lifetime ≤ lifetime := by
  intro hwellInitial hLhs hRhs hwrite
  have hbase : LValBaseOutlives env₁ lhs lifetime :=
    LValTyping.base_outlives_one hwellInitial hLhs
  rcases hbase with ⟨sourceSlot, hsourceSlot, hsourceOutlives⟩
  rcases (TermTyping.slot_lifetime_survives.1 hRhs)
      hsourceOutlives hsourceSlot with
    ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
  cases hwrite with
  | intro hwriteSlot _hupdate =>
      rename_i writeEnv writeSlot updatedTy
      have hslotEq : writeSlot = rhsSlot := by
        have hsomeEq : some writeSlot = some rhsSlot := by
          rw [← hwriteSlot, hrhsSlot]
        exact Option.some.inj hsomeEq
      exact ⟨writeSlot, hwriteSlot, by rw [hslotEq, ← hrhsLifetime]; exact hsourceOutlives⟩

theorem LValTyping.var_inv {env : Env} {x : Name}
    {ty : PartialTy} {lifetime : Lifetime} :
    LValTyping env (.var x) ty lifetime →
    ∃ slot,
      env.slotAt x = some slot ∧
      slot.ty = ty ∧
      slot.lifetime = lifetime := by
  intro htyping
  cases htyping with
  | var hslot =>
      exact ⟨_, hslot, rfl, rfl⟩


end Paper
end LwRust
