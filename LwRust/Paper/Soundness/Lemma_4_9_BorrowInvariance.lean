import LwRust.Paper.Soundness.Lemma_4_10_Progress

/-!
# Lemma 4.9 (Borrow Invariance)

Paper statement (Section 4.3):

> Let `S₁ ▷ t` be a valid state; let `σ` be a store typing where `S₁ ▷ t ⊢ σ`;
> let `Γ₁` be a well-formed typing environment with respect to a lifetime `l`
> where `S₁ ∼ Γ₁` and `Γ₂` be an arbitrary typing environment; let `t` be a
> term; and let `T` be a type.  If `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂`, then `Γ₂[γ ↦ T^l]`
> is well-formed with respect to `l` for arbitrary `γ ∈ fresh`.

Status: proved for the strengthened rule-carried formulation that exposes the
explicit fan-out update obligation `UpdateBorrowInvariantObligations`.  The
original paper formulation leaves this obligation implicit in Definition 3.23's
mutable-borrow fan-out; in this mechanisation it is not derivable from the bare
`WriteBorrowTargets` syntax without additional branch rank/coherence evidence.

The borrow invariant is now mechanised **faithfully per target** (Definition
4.8(i): each individual target lval `w` of a contained borrow is typable with
`m ≼ n`), as opposed to the earlier — and unsound — joint target-list typing
`Γ ⊢ ū : ⟨T⟩^m` (Definition 3.21, which belongs to the well-formed *type*
judgement established at borrow creation by `T-LvBor`, not to the runtime
invariant).  This was the root cause that blocked the environment-join case: rule
W-Bor merges the target *lists* of two joined borrows without joining their
pointee types, so the merged list has no joint typing in general, yet each target
keeps its own per-target typing.  With the per-target statement:

* the previously **false** obligation `partialTyUnion_preserves_borrows` is now a
  theorem (`PartialTyBorrowsWellFormedInSlot.of_partialTyUnion`);
* the borrow-target join transport uses the single-lval
  `FullLValTypingJoinTransport` (no joint cons-union landmark);
* the single-lval determinism keystone `lvalTyping_eqv`/`lvalTyping_sameShape`
  (from the linearizability rank φ) is fully proven and unconditional.

The mechanization strengthens the paper's final result-extension phrase
`γ ∈ fresh`: adding `γ ↦ T^l` must satisfy `FreshUpdateCoherenceObligations`.
The bare implication from `WellFormedTy Γ₂ T l` is false (`&[]` is syntactically
well formed but not jointly target-typeable), so this side condition is part of
the faithful axiom-free statement.
-/

namespace LwRust
namespace Paper

open Core


/--
The terminal safety conclusion of Lemma 4.11 / Theorem 4.12: the terminal state
is valid, the final store safely abstracts the output environment, and the
terminal value abstracts the result type.
-/
def TerminalStateSafe (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) :
    Prop :=
  ValidRuntimeState store (.val value) ∧ store ∼ₛ env ∧ ValidValue store value ty

theorem EnvContains.update_same {env : Env} {x : Name} {slot : EnvSlot}
    {ty : Ty} :
    PartialTyContains slot.ty ty →
    (env.update x slot) ⊢ x ↝ ty := by
  intro hcontains
  exact ⟨slot, by simp [Env.update], hcontains⟩

theorem EnvContains.update_fresh_of_old {env : Env} {x y : Name} {slot : EnvSlot}
    {ty : Ty} :
    env.fresh x →
    env ⊢ y ↝ ty →
    (env.update x slot) ⊢ y ↝ ty := by
  intro hfresh hcontains
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  by_cases hy : y = x
  · subst hy
    rw [hfresh] at hslot
    cases hslot
  · exact ⟨containedSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩

theorem pathConflicts_of_base_eq {target left right : LVal} :
    LVal.base left = LVal.base right →
    target ⋈ left →
    target ⋈ right := by
  intro hbase hconflict
  exact hconflict.trans hbase

theorem readProhibited_congr_base {env : Env} {left right : LVal} :
    LVal.base left = LVal.base right →
    (ReadProhibited env left ↔ ReadProhibited env right) := fun hbase => by
  constructor
  · intro hread
    rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    exact ⟨x, targets, target, hcontains, htarget,
      pathConflicts_of_base_eq hbase hconflict⟩
  · intro hread
    rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    exact ⟨x, targets, target, hcontains, htarget,
      pathConflicts_of_base_eq hbase.symm hconflict⟩

theorem writeProhibited_congr_base {env : Env} {left right : LVal} :
    LVal.base left = LVal.base right →
    (WriteProhibited env left ↔ WriteProhibited env right) := fun hbase => by
  constructor
  · intro hwrite
    cases hwrite with
    | inl hread =>
        exact Or.inl ((readProhibited_congr_base hbase).mp hread)
    | inr himm =>
        rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
        exact Or.inr ⟨x, targets, target, hcontains, htarget,
          pathConflicts_of_base_eq hbase hconflict⟩
  · intro hwrite
    cases hwrite with
    | inl hread =>
        exact Or.inl ((readProhibited_congr_base hbase).mpr hread)
    | inr himm =>
        rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
        exact Or.inr ⟨x, targets, target, hcontains, htarget,
          pathConflicts_of_base_eq hbase.symm hconflict⟩

theorem not_writeProhibited_var_base {env : Env} {lv : LVal} :
    ¬ WriteProhibited env lv →
    ¬ WriteProhibited env (.var (LVal.base lv)) := by
  intro hnot hwrite
  exact hnot ((writeProhibited_congr_base
    (env := env) (left := lv) (right := .var (LVal.base lv))
    (by simp [LVal.base])).mpr hwrite)

theorem EnvContains.dropLifetime_of_contains {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    (env.dropLifetime lifetime) ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _hlifetime⟩
  exact ⟨slot, henvSlot, hcontainsTy⟩

theorem LValTyping.var_dropLifetime_child {env : Env} {parent child : Lifetime}
    {x : Name} {slot : EnvSlot} :
    LifetimeChild parent child →
    env.slotAt x = some slot →
    slot.lifetime ≤ parent →
    LValTyping (env.dropLifetime child) (.var x) slot.ty slot.lifetime := by
  intro hchild hslot houtlivesParent
  exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
    ⟨hslot, by
      intro hslotLifetime
      subst hslotLifetime
      exact LifetimeChild.not_child_outlives_parent hchild houtlivesParent⟩)

theorem Env.dropLifetime_update_ne {env : Env} {x : Name} {slot : EnvSlot}
    {dropped : Lifetime} :
    slot.lifetime ≠ dropped →
    (env.update x slot).dropLifetime dropped =
      (env.dropLifetime dropped).update x slot := by
  intro hslotLifetime
  cases env with
  | mk slotAt =>
      simp only [Env.dropLifetime, Env.update]
      congr
      funext y
      by_cases hy : y = x
      · subst hy
        simp [hslotLifetime]
      · simp [hy]

/-! ## Paper-Facing Section 4 Targets -/

/--
The exact well-formedness invariant needed for runtime references in `T-Const`.

`ValueTyping` for references only consults `σ`; it does not itself say that the
type stored in `σ` is well formed in the current environment.  This predicate
names that missing bridge explicitly.
-/
def StoreTypingRefsWellFormed
    (env : Env) (typing : StoreTyping) (lifetime : Lifetime) : Prop :=
  ∀ (ref : Reference) (ty : Ty),
    typing.tyOf ref.location = some ty →
    WellFormedTy env ty lifetime

/-- `T-Const` value well-formedness from an explicit reference-store invariant. -/
theorem valueTyping_result_wellFormed_of_refs {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreTypingRefsWellFormed env typing lifetime →
    ValueTyping typing value ty →
    WellFormedTy env ty lifetime := by
  intro hrefs htyping
  cases htyping with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | ref hlookup =>
      exact hrefs _ _ hlookup

@[simp] theorem storeTypingRefsWellFormed_empty (env : Env) (lifetime : Lifetime) :
    StoreTypingRefsWellFormed env StoreTyping.empty lifetime := by
  intro ref ty hlookup
  simp [StoreTyping.empty] at hlookup

theorem LValTyping.containedBorrowTargetsWellFormed {env : Env} {lv : LVal}
    {partialTy : PartialTy} {mutable : Bool} {targets : List LVal}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed htyping hcontainsTop
  exact LValTyping.rec
    (motive_1 := fun _lv partialTy _ _ =>
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime)
    (motive_2 := fun _targetLvs unionTy _ _ =>
      ∀ {mutable targets},
        PartialTyContains unionTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime)
    (by
      intro x slot hslot mutable targets hcontains
      exact EnvContains.borrowTargetsWellFormed hwellFormed
        ⟨slot, hslot, hcontains⟩)
    (by
      intro _lv inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _mutableBorrow _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets _ihBorrow ihTargets _mutable _targets
        hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
        _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
        _mutable _targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion
          (by
            intro mutable targets hcontainsHead
            exact BorrowTargetsWellFormed.inSlot (ihHead hcontainsHead))
          (by
            intro mutable targets hcontainsRest
            exact BorrowTargetsWellFormed.inSlot (ihRest hcontainsRest))
          hcontains)
        (LifetimeOutlives.refl lifetime))
    htyping
    hcontainsTop

theorem LValTyping.containedBorrowTargetsWellFormed_at_lifetime {env : Env}
    {lv : LVal} {partialTy : PartialTy} {valueLifetime : Lifetime}
    {mutable : Bool} {targets : List LVal} :
    ContainedBorrowsWellFormed env →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormed env targets valueLifetime := by
  intro hcontained htyping hcontainsTop
  exact LValTyping.rec
    (motive_1 := fun _lv partialTy valueLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets valueLifetime)
    (motive_2 := fun _targetLvs unionTy targetLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains unionTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets targetLifetime)
    (by
      intro x slot hslot mutable targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (hcontained x slot mutable targets hslot ⟨slot, hslot, hcontains⟩)
        (LifetimeOutlives.refl slot.lifetime))
    (by
      intro _lv _inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _mutableBorrow _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets _ihBorrow ihTargets _mutable _targets
        hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
        _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
        _mutable _targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion
          (by
            intro mutable targets hcontainsHead
            exact BorrowTargetsWellFormedInSlot.weaken
              (BorrowTargetsWellFormed.inSlot (ihHead hcontainsHead))
              (LifetimeIntersection.left_le hintersection))
          (by
            intro mutable targets hcontainsRest
            exact BorrowTargetsWellFormedInSlot.weaken
              (BorrowTargetsWellFormed.inSlot (ihRest hcontainsRest))
              (LifetimeIntersection.right_le hintersection))
          hcontains)
        (LifetimeOutlives.refl _))
    htyping
    hcontainsTop

theorem LValTyping.lifetime_outlives_of_base_outlives {env : Env}
    {current : Lifetime} :
    ContainedBorrowsWellFormed env →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      LValBaseOutlives env lv current →
      lifetime ≤ current) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → LValBaseOutlives env target current) →
      lifetime ≤ current) := by
  intro hcontained
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormed env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormed_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormed env targets current :=
          BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget⟩
          exact hbaseTarget))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormed env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormed_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormed env targets current :=
          BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget⟩
          exact hbaseTarget))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping

theorem LValTyping.lifetime_outlives_of_base_outlives_one {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    LValTyping env lv partialTy lifetime →
    LValBaseOutlives env lv current →
    lifetime ≤ current := by
  intro hcontained htyping hbase
  exact (LValTyping.lifetime_outlives_of_base_outlives
    (current := current) hcontained).1 htyping hbase

theorem TermTyping.target_lifetime_outlives_surviving_base_slot {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lv : LVal} {oldTy : PartialTy} {term : Term} {ty : Ty}
    {resultSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    LValTyping env₁ lv oldTy targetLifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.slotAt (LVal.base lv) = some resultSlot →
    targetLifetime ≤ resultSlot.lifetime := by
  intro hwellInitial hLv hterm hresultSlot
  rcases LValTyping.base_outlives_one hwellInitial hLv with
    ⟨sourceSlot, hsourceSlot, hsourceOutlivesCurrent⟩
  have hbaseSelf : LValBaseOutlives env₁ lv sourceSlot.lifetime :=
    ⟨sourceSlot, hsourceSlot, LifetimeOutlives.refl sourceSlot.lifetime⟩
  have htargetOutlivesSource :
      targetLifetime ≤ sourceSlot.lifetime :=
    LValTyping.lifetime_outlives_of_base_outlives_one
      hwellInitial.1 hLv hbaseSelf
  rcases (TermTyping.slot_lifetime_survives.1 hterm)
      hsourceOutlivesCurrent hsourceSlot with
    ⟨survivedSlot, hsurvivedSlot, hsurvivedLifetime⟩
  have hslotEq : survivedSlot = resultSlot := by
    have hsomeEq : some survivedSlot = some resultSlot := by
      rw [← hsurvivedSlot, hresultSlot]
    exact Option.some.inj hsomeEq
  rw [← hslotEq, ← hsurvivedLifetime]
  exact htargetOutlivesSource

theorem LValTyping.borrowTargetsWellFormed {env : Env} {lv : LVal}
    {mutable : Bool} {targets : List LVal}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty (.borrow mutable targets)) valueLifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed htyping
  exact LValTyping.containedBorrowTargetsWellFormed hwellFormed htyping
    PartialTyContains.here

theorem wellFormedTy_of_containedBorrowTargets {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      BorrowTargetsWellFormed env targets lifetime) →
    WellFormedTy env ty lifetime := by
  intro htargets
  exact Ty.rec
    (motive_1 := fun ty =>
      (∀ mutable targets,
        PartialTyContains (.ty ty) (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime) →
      WellFormedTy env ty lifetime)
    (motive_2 := fun _partialTy => True)
    (by
      intro _htargets
      exact WellFormedTy.unit)
    (by
      intro _htargets
      exact WellFormedTy.int)
    (by
      intro mutable targets htargets
      exact WellFormedTy.borrow (htargets mutable targets PartialTyContains.here))
    (by
      intro inner ih htargets
      exact WellFormedTy.box (ih (by
        intro mutable targets hcontains
        exact htargets mutable targets (PartialTyContains.tyBox hcontains))))
    (by
      intro _ty _ih
      trivial)
    (by
      intro _partialTy _ih
      trivial)
    (by
      intro _shape _ih
      trivial)
    ty htargets

theorem LValTyping.fullTyWellFormed {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    WellFormedTy env ty lifetime := by
  intro hwellFormed htyping
  exact wellFormedTy_of_containedBorrowTargets (by
    intro mutable targets hcontains
    exact LValTyping.containedBorrowTargetsWellFormed hwellFormed htyping
      hcontains)

/--
The `T-Copy` result type is well formed.

This is intentionally specialized by `copy(T)`: copyable types are only `int`
and immutable borrows, so we do not need a false theorem saying every full type
read from an lval is recursively well formed.
-/
theorem copyBorrowTargetsWellFormed {env : Env} {lv : LVal}
    {targets : List LVal} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty (.borrow false targets)) valueLifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed hLv
  exact LValTyping.borrowTargetsWellFormed hwellFormed hLv

theorem copyTy_result_wellFormed {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    CopyTy ty →
    WellFormedTy env ty lifetime := by
  intro hwellFormed hLv hcopy
  cases hcopy with
  | int =>
      exact WellFormedTy.int
  | immBorrow =>
      exact WellFormedTy.borrow
        (copyBorrowTargetsWellFormed hwellFormed hLv)

theorem PartialTyContains.of_strike {path : Path} {source struck : PartialTy}
    {needle : Ty} :
    Strike path source struck →
    PartialTyContains struck needle →
    PartialTyContains source needle := by
  intro hstrike hcontains
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains
  | cons _ path ih =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains with
      | box hinner =>
          exact PartialTyContains.box (ih hstrike hinner)

theorem LVal.path_deref_append (lv : LVal) (suffix : Path) :
    LVal.path (.deref lv) ++ suffix = LVal.path lv ++ (() :: suffix) := by
  rw [LVal.path, List.append_assoc]
  rfl

theorem EnvContains.of_move {env env' : Env} {lv : LVal} {x : Name}
    {ty : Ty} :
    EnvMove env lv env' →
    env' ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hmove hcontains
  rcases hmove with ⟨slot, struck, hslot, hstrike, henv'⟩
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hcontainedSlotEq :
        containedSlot = { slot with ty := struck } := by
      have h :
          { slot with ty := struck } = containedSlot := by
        simpa [henv', Env.update] using hcontainedSlot
      exact h.symm
    subst hcontainedSlotEq
    exact ⟨slot, hslot, PartialTyContains.of_strike hstrike hcontainsTy⟩
  · have hslotOld : env.slotAt x = some containedSlot := by
      simpa [henv', Env.update, hx] using hcontainedSlot
    exact ⟨containedSlot, hslotOld, hcontainsTy⟩

theorem EnvMove.oldSlot_of_newSlot {env env' : Env} {lv : LVal}
    {x : Name} {newSlot : EnvSlot} :
    EnvMove env lv env' →
    env'.slotAt x = some newSlot →
    ∃ oldSlot,
      env.slotAt x = some oldSlot ∧
      oldSlot.lifetime = newSlot.lifetime := by
  intro hmove hnewSlot
  rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hnewSlotEq :
        newSlot = { moveSlot with ty := struck } := by
      have h :
          { moveSlot with ty := struck } = newSlot := by
        simpa [henv', Env.update] using hnewSlot
      exact h.symm
    subst hnewSlotEq
    exact ⟨moveSlot, hmoveSlot, rfl⟩
  · have holdSlot : env.slotAt x = some newSlot := by
      simpa [henv', Env.update, hx] using hnewSlot
    exact ⟨newSlot, holdSlot, rfl⟩

theorem not_pathConflicts_of_not_writeProhibited_contains {env : Env}
    {lv target : LVal} {x : Name} {mutable : Bool} {targets : List LVal} :
    ¬ WriteProhibited env lv →
    env ⊢ x ↝ Ty.borrow mutable targets →
    target ∈ targets →
    ¬ target ⋈ lv := by
  intro hnotWrite hcontains htarget hconflict
  cases mutable with
  | false =>
      exact hnotWrite (Or.inr ⟨x, targets, target, hcontains, htarget, hconflict⟩)
  | true =>
      exact hnotWrite (Or.inl ⟨x, targets, target, hcontains, htarget, hconflict⟩)

theorem LValTyping.no_writeProhibited_targets {env : Env} {moved : LVal} :
    ¬ WriteProhibited env moved →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        ∀ target,
          target ∈ targets →
          ¬ target ⋈ moved) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {mutable borrowTargets},
        PartialTyContains partialTy (.borrow mutable borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ target ⋈ moved) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains target
          htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains target
          htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping

theorem LValTyping.move_of_not_pathConflicts {env env' : Env} {moved : LVal} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ¬ lv ⋈ moved →
      LValTyping env' lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ moved) →
      LValTargetsTyping env' targets partialTy lifetime) := by
  intro hmove hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ moved →
        LValTyping env' lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ moved) →
        LValTargetsTyping env' targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
        have hx : x ≠ LVal.base moved := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by simpa [henv', Env.update, hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ moved := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ moved := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ moved →
        LValTyping env' lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ moved) →
        LValTargetsTyping env' targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
        have hx : x ≠ LVal.base moved := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by simpa [henv', Env.update, hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ moved := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ moved := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

theorem LValTyping.update_of_not_pathConflicts {env : Env} {x : Name}
    {slot : EnvSlot} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ¬ lv ⋈ (.var x) →
      LValTyping (env.update x slot) lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
      LValTargetsTyping (env.update x slot) targets partialTy lifetime) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) →
        LValTyping (env.update x slot) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping (env.update x slot) targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping (env.update x slot) lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow' PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) →
        LValTyping (env.update x slot) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping (env.update x slot) targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping (env.update x slot) lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow' PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

theorem BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {slotLifetime : Lifetime}
    {targets : List LVal} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    BorrowTargetsWellFormedInSlot (env.update x slot) slotLifetime targets := by
  intro hnotWrite htargets hnotTargets target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  refine ⟨targetTy, targetLifetime,
    (LValTyping.update_of_not_pathConflicts (slot := slot) hnotWrite).1
      htyping (hnotTargets target htarget),
    houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  have hbaseNe : LVal.base target ≠ x := by
    intro hbaseEq
    exact hnotTargets target htarget hbaseEq
  have hbaseSlot' :
      (env.update x slot).slotAt (LVal.base target) = some baseSlot := by
    simpa [Env.update, hbaseNe] using hbaseSlot
  exact ⟨baseSlot, hbaseSlot', hbaseOutlives⟩

theorem PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {slotLifetime : Lifetime}
    {partialTy : PartialTy} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ {mutable targets},
      PartialTyContains partialTy (.borrow mutable targets) →
      ∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    PartialTyBorrowsWellFormedInSlot
      (env.update x slot) slotLifetime partialTy := by
  intro hnotWrite hpartial hnotTargets mutable targets hcontains
  exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
    (slot := slot) hnotWrite (hpartial hcontains)
    (hnotTargets hcontains)

theorem ContainedBorrowsWellFormed.slot_partial {env : Env}
    {x : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    env.slotAt x = some slot →
    PartialTyBorrowsWellFormedInSlot env slot.lifetime slot.ty := by
  intro hcontained hslot mutable targets hcontains
  exact hcontained x slot mutable targets hslot ⟨slot, hslot, hcontains⟩

theorem ContainedBorrowsWellFormed.update_slot {env : Env} {x : Name}
    {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot (env.update x slot) slot.lifetime slot.ty →
    ¬ WriteProhibited (env.update x slot) (.var x) →
    ContainedBorrowsWellFormed (env.update x slot) := by
  intro hcontained hslotTargets hnotWrite y resultSlot mutable targets
    hresultSlot hcontains
  by_cases hy : y = x
  · subst hy
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hresultSlotEq : resultSlot = slot := by
      have h : slot = resultSlot := by
        simpa [Env.update] using hresultSlot
      exact h.symm
    have hcontainedSlotEq : containedSlot = slot := by
      have h : slot = containedSlot := by
        simpa [Env.update] using hcontainedSlot
      exact h.symm
    have hcontainsSlot : PartialTyContains slot.ty (.borrow mutable targets) := by
      simpa [hcontainedSlotEq] using hcontainsTy
    rw [hresultSlotEq]
    exact hslotTargets hcontainsSlot
  · rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hresultSlotOld : env.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresultSlot
    have hcontainedSlotOld : env.slotAt y = some containedSlot := by
      simpa [Env.update, hy] using hcontainedSlot
    have hcontainedSlotEq : containedSlot = resultSlot := by
      have hsomeEq : some containedSlot = some resultSlot := by
        rw [← hcontainedSlotOld, hresultSlotOld]
      exact Option.some.inj hsomeEq
    have htargetsOld :
        BorrowTargetsWellFormedInSlot env resultSlot.lifetime targets := by
      rw [← hcontainedSlotEq]
      exact hcontained y containedSlot mutable targets hcontainedSlotOld
        ⟨containedSlot, hcontainedSlotOld, hcontainsTy⟩
    exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
      (slot := slot) hnotWrite htargetsOld
      (by
        intro target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains
          hnotWrite
          ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
          htarget)

theorem declare_preserves_wellFormed_output_fresh {env₂ env₃ : Env}
    {lifetime : Lifetime} {x : Name} {ty : Ty} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh x →
    FreshUpdateCoherenceObligations env₂ x ty lifetime →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    WellFormedEnv env₃ lifetime := by
  intro hwellFormed hwellTy hfresh hcoh henv₃
  rw [henv₃]
  exact WellFormedEnv.update_fresh_ty hwellFormed hwellTy hfresh hcoh

theorem ContainedBorrowsWellFormed.move {env env' : Env} {lv : LVal}
    {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    ContainedBorrowsWellFormed env' := by
  intro hwellFormed hnotWrite hmove x slot mutable targets hslot hcontains
  rcases EnvMove.oldSlot_of_newSlot hmove hslot with
    ⟨oldSlot, holdSlot, hlifetime⟩
  rcases EnvContains.of_move hmove hcontains with
    ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  have hcontainedOldSlotEq : containedOldSlot = oldSlot := by
    have hsomeEq : some oldSlot = some containedOldSlot := by
      rw [← holdSlot, hcontainedOldSlot]
    injection hsomeEq with heq
    exact heq.symm
  have hlifetimeContained : containedOldSlot.lifetime = slot.lifetime := by
    rw [hcontainedOldSlotEq, hlifetime]
  have htargetsOld :
      BorrowTargetsWellFormedInSlot env containedOldSlot.lifetime targets :=
    hwellFormed.1 x containedOldSlot mutable targets hcontainedOldSlot
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  rw [← hlifetimeContained]
  have hnotTargets : ∀ target, target ∈ targets → ¬ target ⋈ lv := by
    intro target htarget
    exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩ htarget
  intro target htarget
  rcases htargetsOld target htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  exact ⟨targetTy, targetLifetime,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
      htyping (hnotTargets target htarget),
    houtlives,
    LValBaseOutlives.move_of_not_pathConflicts
      hmove (hnotTargets target htarget) hbase⟩

theorem BorrowTargetsWellFormed.move_of_no_pathConflicts {env env' : Env}
    {moved : LVal} {targets : List LVal} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    BorrowTargetsWellFormed env targets lifetime →
    (∀ target, target ∈ targets → ¬ target ⋈ moved) →
    BorrowTargetsWellFormed env' targets lifetime := by
  intro hmove hnotWrite htargets hnotTargets
  cases htargets with
  | intro hmembers =>
      refine BorrowTargetsWellFormed.intro ?_
      intro target htarget
      rcases hmembers target htarget with
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
      exact ⟨targetTy, targetLifetime,
        (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
          htyping (hnotTargets target htarget),
        houtlives,
        LValBaseOutlives.move_of_not_pathConflicts
          hmove (hnotTargets target htarget) hbase⟩

theorem WellFormedTy.move_of_no_pathConflicts {env env' : Env}
    {moved : LVal} {ty : Ty} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    WellFormedTy env ty lifetime →
    (∀ mutable targets target,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      target ∈ targets →
      ¬ target ⋈ moved) →
    WellFormedTy env' ty lifetime := by
  intro hmove hnotWrite hwellTy hnotConflicts
  induction hwellTy with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | borrow htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.move_of_no_pathConflicts
          hmove hnotWrite htargets
          (by
            intro target htarget
            exact hnotConflicts _ _ target PartialTyContains.here htarget))
  | box hinner ih =>
      exact WellFormedTy.box (ih (by
        intro mutable targets target hcontains htarget
        exact hnotConflicts mutable targets target
          (PartialTyContains.tyBox hcontains) htarget))

theorem WellFormedTy.move_result {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedTy env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  have hwellTy : WellFormedTy env ty lifetime :=
    LValTyping.fullTyWellFormed hwellFormed hLv
  exact WellFormedTy.move_of_no_pathConflicts hmove hnotWrite hwellTy
    (by
      intro mutable targets target hcontains htarget
      exact (LValTyping.no_writeProhibited_targets hnotWrite).1
        hLv hcontains target htarget)

/-- `Strike` only removes variables (it replaces a sub-value by `undef`). -/
theorem Strike.vars_subset :
    ∀ {path : Path} {ty struck : PartialTy}, Strike path ty struck →
      ∀ v, v ∈ PartialTy.vars struck → v ∈ PartialTy.vars ty := by
  intro path
  induction path with
  | nil =>
      intro ty struck h v hv
      cases ty with
      | ty t =>
          cases struck with
          | undef t' => simp [PartialTy.vars] at hv
          | ty _ => simp [Strike] at h
          | box _ => simp [Strike] at h
      | box _ => simp [Strike] at h
      | undef _ => simp [Strike] at h
  | cons _ rest ih =>
      intro ty struck h v hv
      cases ty with
      | box inner =>
          cases struck with
          | box struck' =>
              simp only [PartialTy.vars] at hv ⊢
              exact ih (show Strike rest inner struck' from h) v hv
          | ty _ => simp [Strike] at h
          | undef _ => simp [Strike] at h
      | ty _ => simp [Strike] at h
      | undef _ => simp [Strike] at h

/-- `Linearizable` is preserved by a move (the same rank function works; the
moved slot's type loses variables via `Strike`). -/
theorem Linearizable.move {env env' : Env} {lv : LVal}
    (hmove : EnvMove env lv env') (h : Linearizable env) :
    Linearizable env' := by
  rcases hmove with ⟨slot, struck, hslot, hstrike, henv'⟩
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x s hs
  subst henv'
  by_cases hx : x = LVal.base lv
  · subst hx
    have hseq : s = { slot with ty := struck } := by
      have h := hs
      simpa [Env.update] using h.symm
    subst hseq
    intro v hv
    exact hφ (LVal.base lv) slot hslot v
      (Strike.vars_subset hstrike v (by simpa using hv))
  · have hsenv : env.slotAt x = some s := by simpa [Env.update, hx] using hs
    exact hφ x s hsenv

/-- A partial type with no defined `.ty` leaf reachable: every `Strike` result
is of this form, and an lval typing rooted at a struck slot stays in it (so it
can never be a defined borrow). -/
def IsBoxUndef : PartialTy → Prop
  | .ty _ => False
  | .box inner => IsBoxUndef inner
  | .undef _ => True

theorem Strike.isBoxUndef :
    ∀ {path : Path} {ty struck : PartialTy}, Strike path ty struck → IsBoxUndef struck := by
  intro path
  induction path with
  | nil =>
      intro ty struck h
      cases ty with
      | ty t => cases struck with
        | undef _ => trivial
        | ty _ => simp [Strike] at h
        | box _ => simp [Strike] at h
      | box _ => simp [Strike] at h
      | undef _ => simp [Strike] at h
  | cons _ rest ih =>
      intro ty struck h
      cases ty with
      | box inner => cases struck with
        | box struck' =>
            have h' : Strike rest inner struck' := h
            show IsBoxUndef struck'
            exact ih h'
        | ty _ => simp [Strike] at h
        | undef _ => simp [Strike] at h
      | ty _ => simp [Strike] at h
      | undef _ => simp [Strike] at h

/-- An lval typed in the moved environment whose base is the moved variable has a
`Strike`-shaped (box/undef) type — never a defined `.ty` (in particular never a
borrow). -/
theorem LValTyping.isBoxUndef_of_base_moved {env : Env} {lv : LVal}
    {slot : EnvSlot} {struck : PartialTy}
    (_hslot : env.slotAt (LVal.base lv) = some slot)
    (hstrike : Strike (LVal.path lv) slot.ty struck) :
    ∀ {lv' p lf},
      LValTyping (env.update (LVal.base lv) { slot with ty := struck }) lv' p lf →
      LVal.base lv' = LVal.base lv → IsBoxUndef p := by
  intro lv' p lf h
  refine LValTyping.rec
    (motive_1 := fun lv' p _ _ => LVal.base lv' = LVal.base lv → IsBoxUndef p)
    (motive_2 := fun _ _ _ _ => True)
    ?var ?box ?borrow ?singleton ?cons h
  · intro y ySlot hySlot hbase
    have hy : y = LVal.base lv := by simpa [LVal.base] using hbase
    subst hy
    have : ySlot = { slot with ty := struck } := by
      simpa [Env.update] using hySlot.symm
    subst this
    exact Strike.isBoxUndef hstrike
  · intro lv'' inner lifetime _htyping ih hbase
    have := ih (by simpa [LVal.base] using hbase)
    simpa [IsBoxUndef] using this
  · intro lv'' mutable targets _bLf _tLf _tTy hborrow _htargets ihBorrow _ihTargets hbase
    have := ihBorrow (by simpa [LVal.base] using hbase)
    simp [IsBoxUndef] at this
  · intro _ _ _ _ _; trivial
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _; trivial

/-- `Coherent` is preserved by a move.  A defined borrow `lv':&T` in the moved
environment cannot be rooted at the (undef'd) moved variable
(`isBoxUndef_of_base_moved`), so it transports backward to the original
environment (restoring the moved slot is an update with no path conflict), where
`Coherent env` provides a joint typing of `T`; the joint typing then transports
forward across the move (the targets do not conflict with the moved value, by
`¬WriteProhibited`). -/
theorem Coherent.move {env env' : Env} {lv : LVal} {lifetime : Lifetime}
    (hwellFormed : WellFormedEnv env lifetime)
    (hnotWrite : ¬ WriteProhibited env lv)
    (hmove : EnvMove env lv env')
    (hcohEnv : Coherent env) : Coherent env' := by
  have hmoveCopy := hmove
  rcases hmoveCopy with ⟨slot, struck, hslot, hstrike, henv'⟩
  subst henv'
  intro lv' m T bLf hty'
  have hbaseNe : ¬ lv' ⋈ lv := by
    intro hbeq
    have hbu := LValTyping.isBoxUndef_of_base_moved hslot hstrike hty'
      (by simpa [PathConflicts, LVal.base] using hbeq)
    simp [IsBoxUndef] at hbu
  -- restoring the moved slot returns the original environment
  have hrestore :
      (env.update (LVal.base lv) { slot with ty := struck }).update (LVal.base lv) slot
        = env := by
    obtain ⟨g⟩ := env
    simp only [Env.update]
    congr 1
    funext y
    by_cases hy : y = LVal.base lv
    · subst hy; simpa using hslot.symm
    · simp [hy]
  have hnotWriteVarEnv : ¬ WriteProhibited env (.var (LVal.base lv)) :=
    not_writeProhibited_var_base hnotWrite
  have hnotWriteVar :
      ¬ WriteProhibited
        ((env.update (LVal.base lv) { slot with ty := struck }).update (LVal.base lv) slot)
        (.var (LVal.base lv)) := by rw [hrestore]; exact hnotWriteVarEnv
  -- backward typing: env' → env (restore update, no conflict)
  have htyEnvRestore :
      LValTyping ((env.update (LVal.base lv) { slot with ty := struck }).update
        (LVal.base lv) slot) lv' (.ty (.borrow m T)) bLf :=
    (LValTyping.update_of_not_pathConflicts hnotWriteVar).1 hty'
      (by simpa [PathConflicts, LVal.base] using hbaseNe)
  have htyEnv : LValTyping env lv' (.ty (.borrow m T)) bLf := by
    rwa [hrestore] at htyEnvRestore
  rcases hcohEnv lv' m T bLf htyEnv with ⟨ty, lt, htgtsEnv⟩
  -- targets do not conflict with the moved value
  have hnotTargets : ∀ target, target ∈ T → ¬ target ⋈ lv := by
    intro target htarget
    exact (LValTyping.no_writeProhibited_targets hnotWrite).1 htyEnv
      PartialTyContains.here target htarget
  -- forward transport of the joint typing across the move
  exact ⟨ty, lt,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).2 htgtsEnv hnotTargets⟩

/--
Move Preservation for well-formed environments, used in Lemma 4.9.

This is the proof obligation described in the `T-Move` case of the paper:
`move(Γ, w)` replaces the moved component by `undef`, and the
`¬writeProhibited(Γ, w)` premise prevents this from invalidating any surviving
borrow target.
-/
theorem move_preserves_wellFormed {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedEnv env' lifetime ∧ WellFormedTy env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  refine ⟨⟨ContainedBorrowsWellFormed.move hwellFormed hnotWrite hmove,
      EnvSlotsOutlive.move hwellFormed.2.1 hmove, ?_, ?_⟩,
    WellFormedTy.move_result hwellFormed hLv hnotWrite hmove⟩
  · exact Coherent.move hwellFormed hnotWrite hmove hwellFormed.2.2.1
  · exact Linearizable.move hmove hwellFormed.2.2.2

theorem EnvWrite.preserves_containedBorrowsWellFormed_var {env result : Env}
    {lifetime targetLifetime : Lifetime} {x : Name}
    {oldTy : PartialTy} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    LValTyping env (.var x) oldTy targetLifetime →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite 0 env (.var x) rhsTy result →
    ¬ WriteProhibited result (.var x) →
    ContainedBorrowsWellFormed result := by
  intro hwellFormed hLhs hwellRhs hwrite hnotWrite
  rcases LValTyping.var_inv hLhs with
    ⟨lhsSlot, hlhsSlot, _holdTy, hlhsLifetime⟩
  cases hwrite with
  | intro hwriteSlot hupdate =>
      rename_i writeEnv writeSlot updatedTy
      simp [LVal.base, LVal.path] at hwriteSlot hupdate
      have hslotEq : writeSlot = lhsSlot := by
        have hsomeEq : some writeSlot = some lhsSlot := by
          rw [← hwriteSlot, hlhsSlot]
        exact Option.some.inj hsomeEq
      cases hupdate with
      | strong =>
          have hnotWrite' :
              ¬ WriteProhibited
                (env.update x { writeSlot with ty := PartialTy.ty rhsTy })
                (.var x) := by
            simpa [LVal.base] using hnotWrite
          have hslotTargets :
              PartialTyBorrowsWellFormedInSlot
                (env.update x { writeSlot with ty := PartialTy.ty rhsTy })
                writeSlot.lifetime
                ({ writeSlot with ty := PartialTy.ty rhsTy }).ty := by
            intro mutable targets hcontainsTy
            have htargetsEnv :
                BorrowTargetsWellFormedInSlot env targetLifetime targets :=
              borrowTargetsWellFormedInSlot_of_wellFormedTy_contains
                hwellRhs hcontainsTy
            have htargetsEnvAtSlot :
                BorrowTargetsWellFormedInSlot env writeSlot.lifetime targets := by
              rw [hslotEq, hlhsLifetime]
              exact htargetsEnv
            exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
              (x := x)
              (slot := { writeSlot with ty := PartialTy.ty rhsTy }) hnotWrite'
              htargetsEnvAtSlot
              (by
                intro target htarget
                have hcontainsUpdated :
                    (env.update x { writeSlot with ty := PartialTy.ty rhsTy }) ⊢
                      x ↝ Ty.borrow mutable targets :=
                  ⟨{ writeSlot with ty := PartialTy.ty rhsTy },
                    by simp [Env.update],
                    hcontainsTy⟩
                exact not_pathConflicts_of_not_writeProhibited_contains
                  hnotWrite'
                  hcontainsUpdated
                  htarget)
          simpa [LVal.base] using
            ContainedBorrowsWellFormed.update_slot
              hwellFormed.1 hslotTargets hnotWrite'

/-- Remaining update invariant needed by Lemma 4.9.

The `W-Weak` union case is no longer a caller obligation:
`PartialTyBorrowsWellFormedInSlot.of_partialTyUnion` proves it directly for the
per-target invariant.  The package now only records the non-local mutable-borrow
fan-out fact, where branch writes and joins must preserve observer target
well-formedness.
-/
structure UpdateBorrowInvariantObligations : Prop where
  writeBorrowTargets_preserves_containedBorrowsWellFormed
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets

/-- Initialized-leaf fact for Appendix 9.6 fan-out writes.

Documented rule strengthening: `WriteBorrowTargets.singleton/cons` now carry a
full typing for the concrete branch target `prependPath path target`.  Without
that premise, the bare fan-out syntax could write through arbitrary partial
paths, including reinitialising `undef` leaves, so branch shape would not be
derivable.  With it, the existing matching lemma
`writeLeafTy_of_lvalTyping` supplies exactly the initialized-leaf witness needed
by `EnvWrite.shapePreserved_init` and `WriteBorrowTargets.shapePreserved_init`. -/
theorem WriteBorrowTargets.initialized_leaves_appendix96
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    WriteBorrowTargets rank env path targets rhsTy result →
    ∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy := by
  intro _htargets hwrites
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _rank env path targets rhsTy _result _ =>
      ∀ target, target ∈ targets → ∀ targetSlot,
        env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
        WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
  case nil =>
    intro rank env path ty target htarget
    simp at htarget
  case singleton =>
    intro rank env updated path target ty _hwrite htyped _ih selected hselected slot hslot
    rw [List.mem_singleton] at hselected
    subst hselected
    rcases htyped with ⟨leafTy, leafLifetime, htyping⟩
    have hleaf :=
      writeLeafTy_of_lvalTyping htyping hslot [] ty WriteLeafTy.leaf
    simpa using hleaf
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite htyped _hwrites _hjoin _ihWrite ihRest selected hselected slot hslot
    rcases List.mem_cons.mp hselected with hhead | htail
    · subst hhead
      rcases htyped with ⟨leafTy, leafLifetime, htyping⟩
      have hleaf :=
        writeLeafTy_of_lvalTyping htyping hslot [] ty WriteLeafTy.leaf
      simpa using hleaf
    · exact ihRest selected htail slot hslot
  case intro => intros; trivial

/--
`ContainedBorrowsWellFormedIn source observer` says that every borrow contained
in `source` has targets that are also well formed in `observer`, at the
containing slot's lifetime.

This is the cross-branch invariant needed by `writeBorrowTargets`: when two
branch environments are joined, contained borrows from one branch can be
validated in the joined environment only if their targets are available on the
other branch as well.
-/
def ContainedBorrowsWellFormedIn (source observer : Env) : Prop :=
  ∀ {x slot mutable targets},
    source.slotAt x = some slot →
    source ⊢ x ↝ Ty.borrow mutable targets →
    BorrowTargetsWellFormedInSlot observer slot.lifetime targets

/--
Join transport needed for Definition 4.8(i).

This is the lval-shaped part of the Appendix 9.6 join argument: if the same
borrow target is fully typed on both branches, and both typings live long
enough for the observer slot, then the joined environment also gives that
target a full type at a lifetime that still lives long enough.
-/
structure FullLValTypingJoinTransport : Prop where
  full
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftTy) leftLifetime →
    LValTyping right target (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join target (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure LValTargetsTypingJoinTransport : Prop where
  targets
    {left right join : Env} {targets : List LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTargetsTyping left targets (.ty leftTy) leftLifetime →
    LValTargetsTyping right targets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join targets (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure DerefLValTypingJoinTransport : Prop where
  deref
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.ty leftTy) leftLifetime →
    LValTyping right (.deref source) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure DerefLValTypingJoinTransportWithUnion : Prop where
  deref
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.ty leftTy) leftLifetime →
    LValTyping right (.deref source) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
          joinLifetime ≤ current

structure FullLValTypingJoinTransportWithUnion : Prop where
  full
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftTy) leftLifetime →
    LValTyping right target (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join target (.ty joinTy) joinLifetime ∧
          joinLifetime ≤ current

structure BoxFullLValTypingJoinTransport : Prop where
  boxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join source (.box (.ty joinTy)) joinLifetime ∧
        joinLifetime ≤ current

structure DerefBoxFullLValTypingJoinTransport : Prop where
  derefBoxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.box (.ty leftTy)) leftLifetime →
    LValTyping right (.deref source) (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.box (.ty joinTy)) joinLifetime ∧
        joinLifetime ≤ current

structure BoxBoxFullLValTypingJoinTransport : Prop where
  boxBoxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.box (.ty leftTy))) leftLifetime →
    LValTyping right source (.box (.box (.ty rightTy))) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join source (.box (.box (.ty joinTy))) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefBoxFullLValTypingJoinTransport.of_boxBoxFull
    (htransport : BoxBoxFullLValTypingJoinTransport) :
    DerefBoxFullLValTypingJoinTransport where
  derefBoxFull := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleft hright hleftOutlives hrightOutlives
    have hleftSource :
        LValTyping left source (.box (.box (.ty leftTy))) leftLifetime :=
      LValTyping.deref_box_full_inv hleft
    have hrightSource :
        LValTyping right source (.box (.box (.ty rightTy))) rightLifetime :=
      LValTyping.deref_box_full_inv hright
    rcases htransport.boxBoxFull hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftSource hrightSource
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, hjoinSource, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, LValTyping.box hjoinSource, hjoinOutlives⟩

theorem BoxFullLValTypingJoinTransport.of_derefBoxFull
    (hderef : DerefBoxFullLValTypingJoinTransport) :
    BoxFullLValTypingJoinTransport where
  boxFull := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleft hright hleftOutlives hrightOutlives
    cases source with
    | var x =>
        exact LValTyping.var_join_box_full_bounded hjoin hleft hright
          hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.derefBoxFull hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleft hright hleftOutlives hrightOutlives

structure DerefLValTypingJoinConstructorLandmarks : Prop where
  box_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  box_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {rightMutable : Bool} {rightTargets : List LVal}
    {leftLifetime rightBorrowLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftMutable : Bool} {leftTargets : List LVal}
    {leftBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty}
    {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal}
    {leftBorrowLifetime rightBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefLValTypingJoinConstructorLandmarks.box_box_of_boxFull
    (hbox : BoxFullLValTypingJoinTransport)
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright hleftOutlives hrightOutlives
  rcases hbox.boxFull hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hright hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, LValTyping.box hjoinTyping, hjoinOutlives⟩

theorem LValTyping.deref_borrow_from_aligned_targets
    {env : Env} {source : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime targetLifetime current : Lifetime} {targetTy : Ty} :
    LValTyping env source (.ty (.borrow mutable targets)) borrowLifetime →
    LValTargetsTyping env targets (.ty targetTy) targetLifetime →
    targetLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping env (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hborrow htargets houtlives
  exact ⟨targetTy, targetLifetime,
    LValTyping.borrow hborrow htargets,
    houtlives⟩

structure DerefLValTypingJoinConstructorSplitLandmarks : Prop where
  boxFull :
    BoxFullLValTypingJoinTransport
  box_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {rightMutable : Bool} {rightTargets : List LVal}
    {leftLifetime rightBorrowLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftMutable : Bool} {leftTargets : List LVal}
    {leftBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty}
    {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal}
    {leftBorrowLifetime rightBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefLValTypingJoinConstructorLandmarks.of_split
    (hlandmarks : DerefLValTypingJoinConstructorSplitLandmarks) :
    DerefLValTypingJoinConstructorLandmarks where
  box_box := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft hleft hright
      hleftOutlives hrightOutlives
    exact DerefLValTypingJoinConstructorLandmarks.box_box_of_boxFull
      hlandmarks.boxFull hjoin hleftContained hrightContained hleftInRight
      hrightInLeft hleft hright hleftOutlives hrightOutlives
  box_borrow := by
    intro left right join source leftTy rightTy rightMutable rightTargets
      leftLifetime rightBorrowLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleft hright hrightTargets
      hleftOutlives hrightOutlives
    exact hlandmarks.box_borrow hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hright hrightTargets
      hleftOutlives hrightOutlives
  borrow_box := by
    intro left right join source leftTy rightTy leftMutable leftTargets
      leftBorrowLifetime leftLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleft hleftTargets hright
      hleftOutlives hrightOutlives
    exact hlandmarks.borrow_box hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hleftTargets hright
      hleftOutlives hrightOutlives
  borrow_borrow := by
    intro left right join source leftTy rightTy leftMutable rightMutable
      leftTargets rightTargets leftBorrowLifetime rightBorrowLifetime leftLifetime
      rightLifetime current hjoin hleftContained hrightContained hleftInRight
      hrightInLeft hleft hleftTargets hright hrightTargets hleftOutlives
      hrightOutlives
    exact hlandmarks.borrow_borrow hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hleftTargets hright hrightTargets
      hleftOutlives hrightOutlives

theorem DerefLValTypingJoinTransport.of_constructorLandmarks
    (hlandmarks : DerefLValTypingJoinConstructorLandmarks) :
    DerefLValTypingJoinTransport where
  deref := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases hleftTyping with
    | box hleftSource =>
        cases hrightTyping with
        | box hrightSource =>
            exact hlandmarks.box_box hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hrightSource
              hleftOutlives hrightOutlives
        | borrow hrightSource hrightTargets =>
            exact hlandmarks.box_borrow hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hrightSource hrightTargets
              hleftOutlives hrightOutlives
    | borrow hleftSource hleftTargets =>
        cases hrightTyping with
        | box hrightSource =>
            exact hlandmarks.borrow_box hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hleftTargets hrightSource
              hleftOutlives hrightOutlives
        | borrow hrightSource hrightTargets =>
            exact hlandmarks.borrow_borrow hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hleftTargets hrightSource hrightTargets
              hleftOutlives hrightOutlives

theorem FullLValTypingJoinTransport.of_deref
    (hderef : DerefLValTypingJoinTransport) :
    FullLValTypingJoinTransport where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases target with
    | var x =>
        exact LValTyping.var_join_full_bounded hjoin hleftTyping hrightTyping
          hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.deref hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleftTyping hrightTyping
          hleftOutlives hrightOutlives

theorem DerefLValTypingJoinTransportWithUnion.to_deref
    (htransport : DerefLValTypingJoinTransportWithUnion) :
    DerefLValTypingJoinTransport where
  deref := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    rcases htransport.deref hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftTyping hrightTyping
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, _hunion, hjoinTyping, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩

theorem FullLValTypingJoinTransportWithUnion.to_full
    (htransport : FullLValTypingJoinTransportWithUnion) :
    FullLValTypingJoinTransport where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    rcases htransport.full hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftTyping hrightTyping
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, _hunion, hjoinTyping, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩

theorem FullLValTypingJoinTransportWithUnion.of_deref
    (hderef : DerefLValTypingJoinTransportWithUnion) :
    FullLValTypingJoinTransportWithUnion where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases target with
    | var x =>
        exact LValTyping.var_join_full_bounded_with_union hjoin
          hleftTyping hrightTyping hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.deref hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleftTyping hrightTyping
          hleftOutlives hrightOutlives

def BorrowTargetsTransport (source target : Env) : Prop :=
  ∀ {slotLifetime targets},
    BorrowTargetsWellFormedInSlot source slotLifetime targets →
    BorrowTargetsWellFormedInSlot target slotLifetime targets

@[refl] theorem BorrowTargetsTransport.refl (env : Env) :
    BorrowTargetsTransport env env := by
  intro slotLifetime targets htargets
  exact htargets

theorem BorrowTargetsTransport.trans {first second third : Env} :
    BorrowTargetsTransport first second →
    BorrowTargetsTransport second third →
    BorrowTargetsTransport first third := by
  intro hfirstSecond hsecondThird slotLifetime targets htargets
  exact hsecondThird (hfirstSecond htargets)

/-- Observer-target transport across a join via the runtime invariants
(one-directional: `source → left → join`).  Here `ContainedBorrows join` is
already established (the bootstrap runs first), so each transported target's
lifetime is bounded by the *unbounded*-strength invariant — packaged through the
rank-bounded `fullJoinTransport` with the per-target bound `N := φ(base t)+1` and
`hcontN` derived from the full `hcontJoin`. -/
theorem BorrowTargetsTransport.join_viaInvariants_left
    {source left right join : Env}
    (hjoin : EnvJoin left right join)
    (hstrL : ∀ x sE, left.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hlinJoin : Linearizable join) (hcohJoin : Coherent join)
    (hcontJoin : ContainedBorrowsWellFormed join)
    (hsourceLeft : BorrowTargetsTransport source left) :
    BorrowTargetsTransport source join := by
  obtain ⟨φ, hφJoin⟩ := hlinJoin
  intro slotLifetime targets htargets
  have hleft := hsourceLeft htargets
  intro target htarget
  rcases hleft target htarget with ⟨leftTy, leftLf, hleftTyping, _hleftOutlives, hleftBase⟩
  have hjoinBase := LValBaseOutlives.join_left hjoin hleftBase
  rcases fullJoinTransport_viaInvariants (N := φ (LVal.base target) + 1)
      hstrL hφJoin hcohJoin
      (fun x' slot' m' T' _ hslot' hcont' => hcontJoin x' slot' m' T' hslot' hcont')
      (Nat.lt_succ_self _) hleftTyping hjoinBase
    with ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives, hjoinBase⟩

theorem ContainedBorrowsWellFormedIn.of_transport {source observer : Env} :
    ContainedBorrowsWellFormed source →
    BorrowTargetsTransport source observer →
    ContainedBorrowsWellFormedIn source observer := by
  intro hcontained htransport x slot mutable targets hslot hcontains
  exact htransport (hcontained x slot mutable targets hslot hcontains)

theorem ContainedBorrowsWellFormed.in_self {env : Env} :
    ContainedBorrowsWellFormed env →
    ContainedBorrowsWellFormedIn env env := by
  intro hcontained x slot mutable targets hslot hcontains
  exact hcontained x slot mutable targets hslot hcontains

theorem LValTargetsTyping.join_full_singleton_of_fullLValTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTargetsTyping left [target] (.ty leftTy) leftLifetime →
    LValTargetsTyping right [target] (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join [target] (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleftTargets hrightTargets hleftOutlives hrightOutlives
  cases hleftTargets with
  | singleton hleft =>
      cases hrightTargets with
      | singleton hright =>
          rcases htransport.full hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleft hright
              hleftOutlives hrightOutlives with
            ⟨joinTy, joinLifetime, hjoinTarget, hjoinOutlives⟩
          exact ⟨joinTy, joinLifetime,
            LValTargetsTyping.singleton hjoinTarget, hjoinOutlives⟩
      | cons _hhead hrest _hunion _hintersection =>
          cases hrest
  | cons _hhead hrest _hunion _hintersection =>
      cases hrest

theorem LValTargetsTyping.join_full_cons_of_parts
    {join : Env} {target : LVal} {rest : List LVal}
    {headTy restTy unionTy : Ty}
    {headLifetime restLifetime lifetime current : Lifetime} :
    LValTyping join target (.ty headTy) headLifetime →
    LValTargetsTyping join rest (.ty restTy) restLifetime →
    PartialTyUnion (.ty headTy) (.ty restTy) (.ty unionTy) →
    LifetimeIntersection headLifetime restLifetime lifetime →
    lifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join (target :: rest) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hhead hrest hunion hintersection houtlives
  exact ⟨unionTy, lifetime,
    LValTargetsTyping.cons hhead hrest hunion hintersection,
    houtlives⟩

structure LValTargetsTypingJoinConsTypeUnionLandmark : Prop where
  typeUnion
    {left right join : Env} {target : LVal} {rest : List LVal}
    {leftHeadTy rightHeadTy leftRestTy rightRestTy leftTy rightTy : Ty}
    {joinHeadTy joinRestTy : Ty}
    {leftHeadLifetime rightHeadLifetime leftRestLifetime rightRestLifetime
      leftLifetime rightLifetime joinHeadLifetime joinRestLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftHeadTy) leftHeadLifetime →
    LValTyping right target (.ty rightHeadTy) rightHeadLifetime →
    LValTargetsTyping left rest (.ty leftRestTy) leftRestLifetime →
    LValTargetsTyping right rest (.ty rightRestTy) rightRestLifetime →
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty rightHeadTy) (.ty rightRestTy) (.ty rightTy) →
    LifetimeIntersection leftHeadLifetime leftRestLifetime leftLifetime →
    LifetimeIntersection rightHeadLifetime rightRestLifetime rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    LValTyping join target (.ty joinHeadTy) joinHeadLifetime →
    LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime →
    joinHeadLifetime ≤ current →
    joinRestLifetime ≤ current →
    ∃ joinTy, PartialTyUnion (.ty joinHeadTy) (.ty joinRestTy) (.ty joinTy)

structure LValTargetsTypingJoinConsLandmark : Prop where
  cons
    {left right join : Env} {target : LVal} {rest : List LVal}
    {leftHeadTy rightHeadTy leftRestTy rightRestTy leftTy rightTy : Ty}
    {leftHeadLifetime rightHeadLifetime leftRestLifetime rightRestLifetime
      leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftHeadTy) leftHeadLifetime →
    LValTyping right target (.ty rightHeadTy) rightHeadLifetime →
    LValTargetsTyping left rest (.ty leftRestTy) leftRestLifetime →
    LValTargetsTyping right rest (.ty rightRestTy) rightRestLifetime →
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty rightHeadTy) (.ty rightRestTy) (.ty rightTy) →
    LifetimeIntersection leftHeadLifetime leftRestLifetime leftLifetime →
    LifetimeIntersection rightHeadLifetime rightRestLifetime rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    (∃ joinHeadTy joinHeadLifetime,
      LValTyping join target (.ty joinHeadTy) joinHeadLifetime ∧
        joinHeadLifetime ≤ current) →
    (∃ joinRestTy joinRestLifetime,
      LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime ∧
        joinRestLifetime ≤ current) →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join (target :: rest) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem LValTargetsTypingJoinConsLandmark.of_typeUnion
    (htypeUnion : LValTargetsTypingJoinConsTypeUnionLandmark) :
    LValTargetsTypingJoinConsLandmark where
  cons := by
    intro left right join target rest leftHeadTy rightHeadTy leftRestTy rightRestTy
      leftTy rightTy leftHeadLifetime rightHeadLifetime leftRestLifetime
      rightRestLifetime leftLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleftHead hrightHead hleftRest
      hrightRest hleftUnion hrightUnion hleftIntersection hrightIntersection
      hleftOutlives hrightOutlives hjoinHead hjoinRest
    rcases hjoinHead with
      ⟨joinHeadTy, joinHeadLifetime, hjoinHeadTyping, hjoinHeadOutlives⟩
    rcases hjoinRest with
      ⟨joinRestTy, joinRestLifetime, hjoinRestTyping, hjoinRestOutlives⟩
    rcases htypeUnion.typeUnion hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftHead hrightHead hleftRest hrightRest
        hleftUnion hrightUnion hleftIntersection hrightIntersection
        hleftOutlives hrightOutlives hjoinHeadTyping hjoinRestTyping
        hjoinHeadOutlives hjoinRestOutlives with
      ⟨joinTy, hjoinUnion⟩
    rcases LifetimeIntersection.exists_of_common_inner
        hjoinHeadOutlives hjoinRestOutlives with
      ⟨joinLifetime, hjoinIntersection⟩
    exact LValTargetsTyping.join_full_cons_of_parts
      hjoinHeadTyping hjoinRestTyping hjoinUnion hjoinIntersection
      (LifetimeIntersection.le_of_le hjoinIntersection
        hjoinHeadOutlives hjoinRestOutlives)

theorem LValTargetsTypingJoinTransport.of_full_and_cons
    (hfull : FullLValTypingJoinTransport)
    (hcons : LValTargetsTypingJoinConsLandmark) :
    LValTargetsTypingJoinTransport := by
  constructor
  intro left right join targets leftTy rightTy leftLifetime rightLifetime current
    hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleftTargets hrightTargets hleftOutlives hrightOutlives
  induction targets generalizing leftTy rightTy leftLifetime rightLifetime current with
  | nil =>
      cases hleftTargets
  | cons target rest ih =>
      by_cases hrestNil : rest = []
      · subst hrestNil
        cases hleftTargets with
        | singleton hleftTarget =>
            cases hrightTargets with
            | singleton hrightTarget =>
                rcases hfull.full hjoin hleftContained hrightContained
                    hleftInRight hrightInLeft hleftTarget hrightTarget
                    hleftOutlives hrightOutlives with
                  ⟨joinTy, joinLifetime, hjoinTarget, hjoinOutlives⟩
                exact ⟨joinTy, joinLifetime,
                  LValTargetsTyping.singleton hjoinTarget, hjoinOutlives⟩
            | cons _hrightHead hrightRest _hrightUnion _hrightIntersection =>
                cases hrightRest
        | cons _hleftHead hleftRest _hleftUnion _hleftIntersection =>
            cases hleftRest
      · rcases LValTargetsTyping.cons_full_inv hrestNil hleftTargets with
          ⟨leftHeadTy, leftHeadLifetime, leftRestTy, leftRestLifetime,
            hleftHead, hleftRest, hleftUnion, hleftIntersection⟩
        rcases LValTargetsTyping.cons_full_inv hrestNil hrightTargets with
          ⟨rightHeadTy, rightHeadLifetime, rightRestTy, rightRestLifetime,
            hrightHead, hrightRest, hrightUnion, hrightIntersection⟩
        have hleftHeadOutlives : leftHeadLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.left_le hleftIntersection) hleftOutlives
        have hrightHeadOutlives : rightHeadLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.left_le hrightIntersection) hrightOutlives
        have hleftRestOutlives : leftRestLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.right_le hleftIntersection) hleftOutlives
        have hrightRestOutlives : rightRestLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.right_le hrightIntersection) hrightOutlives
        have hjoinHead :
            ∃ joinHeadTy joinHeadLifetime,
              LValTyping join target (.ty joinHeadTy) joinHeadLifetime ∧
                joinHeadLifetime ≤ current :=
          hfull.full hjoin hleftContained hrightContained hleftInRight
            hrightInLeft hleftHead hrightHead hleftHeadOutlives
            hrightHeadOutlives
        have hjoinRest :
            ∃ joinRestTy joinRestLifetime,
              LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime ∧
                joinRestLifetime ≤ current :=
          ih hleftRest hrightRest hleftRestOutlives hrightRestOutlives
        exact hcons.cons hjoin hleftContained hrightContained hleftInRight
          hrightInLeft hleftHead hrightHead hleftRest hrightRest
          hleftUnion hrightUnion hleftIntersection hrightIntersection
          hleftOutlives hrightOutlives hjoinHead hjoinRest

theorem BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {targets : List LVal}
    {slotLifetime : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright target htarget
  -- Per-target invariant: each target is typed in both branches; transport the
  -- single typing across the join via the single-lval full join transport.  No
  -- joint target-list typing of the merged list is needed, so the list-level
  -- cons-union landmark is no longer required here.
  rcases hleft target htarget with
    ⟨leftTy, leftLifetime, hleftTyping, hleftOutlives, hleftBase⟩
  rcases hright target htarget with
    ⟨rightTy, rightLifetime, hrightTyping, hrightOutlives, _hrightBase⟩
  rcases htransport.full hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleftTyping hrightTyping
      hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives,
    LValBaseOutlives.join_left hjoin hleftBase⟩

theorem EnvJoin.preserves_observerTargets_of_lvalTargetsTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {targets : List LVal}
    {slotLifetime : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport

theorem BorrowTargetsTransport.join_observer
    (htransport : FullLValTypingJoinTransport)
    {source left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsTransport source left →
    BorrowTargetsTransport source right →
    BorrowTargetsTransport source join := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright slotLifetime targets htargets
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport hjoin hleftContained hrightContained hleftInRight hrightInLeft
    (hleft htargets) (hright htargets)

theorem ContainedBorrowsWellFormedIn.join_observer
    (htransport : FullLValTypingJoinTransport)
    {source left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    ContainedBorrowsWellFormedIn source left →
    ContainedBorrowsWellFormedIn source right →
    ContainedBorrowsWellFormedIn source join := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright x slot mutable targets hslot hcontains
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport hjoin hleftContained hrightContained hleftInRight hrightInLeft
    (hleft hslot hcontains)
    (hright hslot hcontains)

theorem ContainedBorrowsWellFormedIn.join_source
    {left right join observer : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormedIn left observer →
    ContainedBorrowsWellFormedIn right observer →
    ContainedBorrowsWellFormedIn join observer := by
  intro hjoin hleft hright x joinSlot mutable targets hjoinSlot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq : containedSlot = joinSlot := by
    have hsomeEq : some containedSlot = some joinSlot := by
      rw [← hcontainedSlot, hjoinSlot]
    exact Option.some.inj hsomeEq
  have hcontainsJoin : PartialTyContains joinSlot.ty (.borrow mutable targets) := by
    simpa [hcontainedSlotEq] using hcontainsTy
  rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
    ⟨leftSlot, hleftSlot, _hleftLifetime⟩
  rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
    ⟨rightSlot, hrightSlot, _hrightLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨hleftLife, hrightLife, hunion⟩
  exact BorrowTargetsWellFormedInSlot.of_partialTyUnion
    (env := observer) (lifetime := joinSlot.lifetime) hunion
    (by
      intro leftMutable leftTargets hcontainsLeft
      have htargets :
          BorrowTargetsWellFormedInSlot observer leftSlot.lifetime leftTargets :=
        hleft hleftSlot ⟨leftSlot, hleftSlot, hcontainsLeft⟩
      simpa [hleftLife] using htargets)
    (by
      intro rightMutable rightTargets hcontainsRight
      have htargets :
          BorrowTargetsWellFormedInSlot observer rightSlot.lifetime rightTargets :=
        hright hrightSlot ⟨rightSlot, hrightSlot, hcontainsRight⟩
      simpa [hrightLife] using htargets)
    hcontainsJoin

/--
Branch-specific contained-borrow join preservation.

The unconditional statement "contained borrows are preserved by every
environment join" is too strong for partial environments: a borrow introduced
on one branch may have targets that are not fully typable on the other branch.
The `writeBorrowTargets` cons case supplies precisely the missing cross-branch
premises via its observer-target induction hypotheses.
-/
theorem ContainedBorrowsWellFormed.join_of_crossBranchTargets
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    ContainedBorrowsWellFormed join := by
  intro hjoin hleftContained hrightContained hleftTargetsRight hrightTargetsLeft
  exact ContainedBorrowsWellFormed.join_of_inSlot hjoin
    (by
      intro x slot mutable targets hslot hcontains
      exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
        htransport hjoin hleftContained hrightContained
        hleftTargetsRight hrightTargetsLeft
        (hleftContained x slot mutable targets hslot hcontains)
        (hleftTargetsRight hslot hcontains))
    (by
      intro x slot mutable targets hslot hcontains
      exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
        htransport hjoin hleftContained hrightContained
        hleftTargetsRight hrightTargetsLeft
        (hrightTargetsLeft hslot hcontains)
        (hrightContained x slot mutable targets hslot hcontains))

structure UpdateBorrowInvariantCrossLandmarks : Prop where
  envWrite_preserves_core
    {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env

/-- Rank side condition needed for preserving one common linearization witness
through a mutable-borrow fan-out.

For every concrete branch write, each *new borrow edge* whose target came from
the RHS type must point to a strictly lower-ranked base.  This is the local
acyclicity premise behind the old bare `EnvWrite.preserves_linearizedBy`
obligation. -/
def WriteBorrowTargetsRhsVarsBelowBranches (φ : Name → Nat) (rank : Nat)
    (env : Env) (path : Path) (writeTargets : List LVal) (rhsTy : Ty) : Prop :=
  ∀ target, target ∈ writeTargets → ∀ updated,
    EnvWrite rank env (prependPath path target) rhsTy updated →
    EnvWriteRhsBorrowTargetsBelow φ updated rhsTy

/-- Coherence obligations for every branch and branch join in a mutable-borrow
fan-out write.

This is the fan-out analogue of the strengthened assignment coherence premise.
Each concrete branch write must expose the write-coherence transport needed by
`EnvWrite.preserves_coherent_of_obligations`; each cons join must expose the
join-coherence transport needed by `EnvJoin.preserves_coherent_of_obligations`.
-/
structure WriteBorrowTargetsCoherenceObligations
    (rank : Nat) (env : Env) (path : Path) (writeTargets : List LVal)
    (rhsTy : Ty) : Prop where
  write
    (target : LVal) :
    target ∈ writeTargets →
    ∀ updated,
      EnvWrite rank env (prependPath path target) rhsTy updated →
      EnvWriteCoherenceObligations env updated (LVal.base (prependPath path target))
  join
    (target : LVal) (rest : List LVal) :
    target ∈ writeTargets →
    (∀ t, t ∈ rest → t ∈ writeTargets) →
    ∀ updated restEnv result,
      EnvWrite rank env (prependPath path target) rhsTy updated →
      WriteBorrowTargets rank env path rest rhsTy restEnv →
      EnvJoin updated restEnv result →
      EnvJoinCoherenceObligations updated restEnv result

/-- Constructive variant of `WriteBorrowTargets.preserves_core_of_crossLandmarks`
that does not use the bare `EnvWrite.preserves_linearizedBy` axiom.

The extra `WriteBorrowTargetsRhsVarsBelowBranches` premise is the small
borrow-inference/rank side condition needed to keep the same linearization witness
across every fan-out branch. -/
theorem WriteBorrowTargets.preserves_core_of_crossLandmarks
    (hlandmarks : UpdateBorrowInvariantCrossLandmarks)
    {rank : Nat} {env result : Env} {path : Path}
    {writeTargets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime}
    {φ : Name → Nat} :
    0 < rank →
    Coherent env →
    LinearizedBy φ env →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    (∀ target, target ∈ writeTargets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    WriteBorrowTargetsRhsVarsBelowBranches φ rank env path writeTargets rhsTy →
    WriteBorrowTargetsCoherenceObligations rank env path writeTargets rhsTy →
    WriteBorrowTargets rank env path writeTargets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro hrank hcoh hφ hcontained hrhs hleaf hbelow hfanoutCoh hwrites
  exact (WriteBorrowTargets.rec
    (motive_1 := fun _rank _env _path _oldTy _rhsTy _result _updatedTy _ =>
      True)
    (motive_2 := fun _rank env _path _writeTargets constructorTy result _ =>
      0 < _rank → Coherent env → LinearizedBy φ env →
      ∀ {slotLifetime},
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        (∀ target, target ∈ _writeTargets → ∀ targetSlot,
          env.slotAt (LVal.base (prependPath _path target)) = some targetSlot →
          WriteLeafTy env (LVal.path (prependPath _path target))
            targetSlot.ty constructorTy) →
        WriteBorrowTargetsRhsVarsBelowBranches φ _rank env _path _writeTargets constructorTy →
        WriteBorrowTargetsCoherenceObligations _rank env _path _writeTargets constructorTy →
        (ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env) ∧
          Coherent result ∧ LinearizedBy φ result)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by intro env old ty; trivial)
    (by intro env rank old joined ty _hshape _hjoin; trivial)
    (by intro env₁ env₂ rank path inner updatedInner ty hupdate ih; trivial)
    (by intro env₁ env₂ rank path targets ty hwrites ih; trivial)
    (by
      intro rank env path ty _hrank hcoh hlinBy slotLifetime hcontained _hrhs _hleaf
        _hbelow _hfanoutCoh
      exact ⟨⟨hcontained, BorrowTargetsTransport.refl env,
        ContainedBorrowsWellFormed.in_self hcontained⟩, hcoh, hlinBy⟩)
    (by
      intro rank env updated path target ty hwrite _htyped _ih
        hrank hcoh hlinBy slotLifetime hcontained hrhs _hleaf hbelow hfanoutCoh
      have hlinEnv : Linearizable env := Linearizable.of_linearizedBy hlinBy
      have hlinUBy :=
        EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
          hwrite hlinBy (hbelow target (by simp) updated hwrite)
      have hlinU := Linearizable.of_linearizedBy hlinUBy
      have hcohU := EnvWrite.preserves_coherent_of_obligations hcoh
        (hfanoutCoh.write target (by simp) updated hwrite)
      exact ⟨hlandmarks.envWrite_preserves_core hrank hcontained hrhs hwrite,
        hcohU, hlinUBy⟩)
    (by
      intro rank env updated restEnv result path target rest ty
        hwrite _htyped hwrites hjoin _ihWrite ihWrites
        hrank hcoh hlinBy slotLifetime hcontained hrhs hleaf hbelow hfanoutCoh
      have hlinEnv : Linearizable env := Linearizable.of_linearizedBy hlinBy
      have hlinUBy :=
        EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
          hwrite hlinBy (hbelow target (by simp) updated hwrite)
      have hlinU := Linearizable.of_linearizedBy hlinUBy
      have hcohU := EnvWrite.preserves_coherent_of_obligations hcoh
        (hfanoutCoh.write target (by simp) updated hwrite)
      rcases hlandmarks.envWrite_preserves_core hrank hcontained hrhs hwrite with
        ⟨hupdatedContained, hupdatedTransport, hupdatedInEnv⟩
      have hleafRest :
          ∀ t, t ∈ rest → ∀ slot,
            env.slotAt (LVal.base (prependPath path t)) = some slot →
            WriteLeafTy env (LVal.path (prependPath path t)) slot.ty ty := by
        intro t ht slot hslot
        exact hleaf t (List.mem_cons_of_mem target ht) slot hslot
      have hbelowRest :
          WriteBorrowTargetsRhsVarsBelowBranches φ rank env path rest ty := by
        intro t ht branch hbranch
        exact hbelow t (List.mem_cons_of_mem target ht) branch hbranch
      have hfanoutCohRest :
          WriteBorrowTargetsCoherenceObligations rank env path rest ty := {
        write := by
          intro t ht branch hbranch
          exact hfanoutCoh.write t (List.mem_cons_of_mem target ht) branch hbranch
        join := by
          intro t later ht hlater branch laterEnv branchResult hbranch hlaterWrites hbranchJoin
          exact hfanoutCoh.join t later (List.mem_cons_of_mem target ht)
            (fun u hu => List.mem_cons_of_mem target (hlater u hu))
            branch laterEnv branchResult hbranch hlaterWrites hbranchJoin
      }
      rcases ihWrites hrank hcoh hlinBy hcontained hrhs hleafRest hbelowRest
          hfanoutCohRest with
        ⟨⟨hrestContained, _hrestTransport, hrestInEnv⟩, hcohRest, hlinRestBy⟩
      have hlinRest := Linearizable.of_linearizedBy hlinRestBy
      have hlinRBy := EnvJoin.preserves_linearizedBy hjoin hlinUBy hlinRestBy
      have hlinR := Linearizable.of_linearizedBy hlinRBy
      have hjoinCoh : EnvJoinCoherenceObligations updated restEnv result :=
        hfanoutCoh.join target rest (by simp)
          (fun t ht => List.mem_cons_of_mem target ht)
          updated restEnv result hwrite hwrites hjoin
      have hcohR := EnvJoin.preserves_coherent_of_obligations hcohU hcohRest hjoinCoh
      have hupdShape : EnvShapePreserved env updated :=
        EnvWrite.shapePreserved_init hrank hwrite
          (fun slot hslot => hleaf target (by simp) slot hslot)
      have hrestShape : EnvShapePreserved env restEnv :=
        WriteBorrowTargets.shapePreserved_init hrank hwrites
          (fun t ht slot hslot =>
            hleaf t (List.mem_cons_of_mem target ht) slot hslot)
      have hbranch : ∀ x sL sR, updated.slotAt x = some sL → restEnv.slotAt x = some sR →
          PartialTy.sameShape sL.ty sR.ty :=
        EnvShapePreserved.branch_sameShape hupdShape hrestShape
      have hstrL := EnvJoin.fanOutShapeMap_left hjoin hbranch
      have hstrR := EnvJoin.fanOutShapeMap_right hjoin hbranch
      have hcontJoin :=
        ContainedBorrowsWellFormed.join_viaInvariants hjoin hstrL hstrR hlinR hcohR
          hupdatedContained hrestContained
      refine ⟨⟨hcontJoin,
        BorrowTargetsTransport.join_viaInvariants_left hjoin hstrL hlinR hcohR
          hcontJoin hupdatedTransport,
        ContainedBorrowsWellFormedIn.join_source hjoin hupdatedInEnv hrestInEnv⟩,
        hcohR, hlinRBy⟩)
    (by intro rank env₁ env₂ lv slot ty updatedTy hslot hupdate ih; trivial)
    hwrites hrank hcoh hφ hcontained hrhs hleaf hbelow hfanoutCoh).1

theorem UpdateBorrowInvariantObligations.of_crossLandmarks
    (hlandmarks : UpdateBorrowInvariantCrossLandmarks)
    (hfanoutRanked :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty} {φ : Name → Nat},
        WriteBorrowTargetsRhsVarsBelowBranches φ rank env path targets rhsTy)
    (hfanoutCoherence :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty},
        WriteBorrowTargetsCoherenceObligations rank env path targets rhsTy) :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed := by
    intro rank env result path targets rhsTy slotLifetime
      hrank hcoh hlin hcontained htargets hleaf hrhs hwrites
    rcases hlin with ⟨φ, hφ⟩
    rcases WriteBorrowTargets.preserves_core_of_crossLandmarks
        hlandmarks hrank hcoh hφ hcontained hrhs hleaf
        (hfanoutRanked (rank := rank) (env := env) (path := path)
          (targets := targets) (rhsTy := rhsTy) (φ := φ))
        (hfanoutCoherence (rank := rank) (env := env) (path := path)
          (targets := targets) (rhsTy := rhsTy))
        hwrites with
      ⟨hresultContained, htransport, _hresultInEnv⟩
    exact ⟨hresultContained, htransport htargets⟩

-- The deref-of-borrow join transport landmark (`borrow_borrow`, formerly the
-- `FullLValTypingJoinTransport` chain) is no longer needed: the write fan-out
-- driver (`WriteBorrowTargets.preserves_core_of_crossLandmarks`) now establishes
-- borrow-target join preservation directly and one-directionally via the
-- transport keystone (`ContainedBorrowsWellFormed.join_viaInvariants` etc.),
-- supplied with the runtime invariants `Coherent`/`Linearizable`.  The old
-- symmetric `FullLValTypingJoinTransport` structure and its consumers remain in
-- the file as dead (proven) scaffolding.

/-- Old borrow-target transport for one write, derived from the transport keystone.

This is one of the constructive pieces behind the legacy single-write Appendix
9.6 claim below.  It deliberately exposes the runtime facts the keystone needs:
the write result must be shape-preserving/strengthening from the source, already
linearized, coherent, and contained-borrow well formed.
-/
theorem EnvWrite.borrowTargetsTransport_of_shapeMap
    {rank : Nat} {env result : Env} {lv : LVal} {rhsTy : Ty}
    {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    BorrowTargetsTransport env result := by
  intro hwrite hshapeMap hlinResult hcohResult hcontainedResult
    slotLifetime targets htargets target htarget
  rcases htargets target htarget with
    ⟨sourceTy, sourceLifetime, hsourceTyping, hsourceOutlives, hsourceBase⟩
  have hresultBase : LValBaseOutlives result target slotLifetime :=
    LValBaseOutlives.write hwrite hsourceBase
  rcases fullJoinTransport_viaInvariants
      (source := env) (join := result) (target := target)
      (sourceTy := sourceTy) (sourceLifetime := sourceLifetime)
      (current := slotLifetime) (φ := φ) (N := φ (LVal.base target) + 1)
      hshapeMap hlinResult hcohResult
      (fun x slot mutable targets _hrank hslot hcontains =>
        hcontainedResult x slot mutable targets hslot hcontains)
      (Nat.lt_succ_self _) hsourceTyping hresultBase with
    ⟨resultTy, resultLifetime, hresultTyping, hresultOutlives⟩
  exact ⟨resultTy, resultLifetime, hresultTyping, hresultOutlives, hresultBase⟩

/-- Constructive packaging of the parts of the legacy single-write core claim
once the result-side invariants have been established separately.

The nontrivial old-target transport component is proved by
`EnvWrite.borrowTargetsTransport_of_shapeMap`; the two contained-borrow facts are
kept explicit because those are structural update obligations, not consequences
of a bare `EnvWrite` plus RHS well-formedness alone.
-/
theorem EnvWrite.preserves_core_appendix96_of_result_invariants
    {rank : Nat} {env result : Env} {lv : LVal} {rhsTy : Ty}
    {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    ContainedBorrowsWellFormedIn result env →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro hwrite hshapeMap hlinResult hcohResult hcontainedResult hresultInEnv
  exact ⟨hcontainedResult,
    EnvWrite.borrowTargetsTransport_of_shapeMap
      hwrite hshapeMap hlinResult hcohResult hcontainedResult,
    hresultInEnv⟩

/-- Appendix 9.6 core preservation for one positive-rank write, with the
result-side invariants exposed.

This is the proved replacement for the old bare claim.  A single `EnvWrite` plus
RHS per-target well-formedness is not enough to derive old-target transport; the
caller must also provide the shape map and result-side linearization/coherence
and contained-borrow facts needed by the transport keystone. -/
theorem EnvWrite.preserves_core_appendix96
    {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} {slotLifetime : Lifetime} {φ : Name → Nat} :
    0 < rank →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    ContainedBorrowsWellFormedIn result env →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro _hrank _hcontained _hrhs hwrite hshape hlinResult hcohResult
    hcontainedResult hresultInEnv
  exact EnvWrite.preserves_core_appendix96_of_result_invariants
    hwrite hshape hlinResult hcohResult hcontainedResult hresultInEnv

/-- Legacy packaging of Appendix 9.6 cross-landmarks.

The broad single-write field is no longer hidden behind an axiom.  Older callers
that still want this package must provide that compatibility premise explicitly;
the proved replacement is `EnvWrite.preserves_core_appendix96`, whose statement
exposes the result-side invariants needed for old-target transport.
-/
theorem updateBorrowInvariantCrossLandmarks_appendix96
    (hwriteCore :
      ∀ {rank : Nat} {env result : Env} {lv : LVal}
        {rhsTy : Ty} {slotLifetime : Lifetime},
        0 < rank →
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
        EnvWrite rank env lv rhsTy result →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env) :
    UpdateBorrowInvariantCrossLandmarks where
  envWrite_preserves_core := by
    intro rank env result lv rhsTy slotLifetime hrank hcontained hrhs hwrite
    exact hwriteCore hrank hcontained hrhs hwrite

structure UpdateBorrowInvariantLandmarks : Prop where
  envWrite_preserves_observerTargets
    {rank : Nat} {env result : Env} {lv : LVal}
    {observerTargets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime observerTargets
  envJoin_preserves_containedBorrowsWellFormed
    {left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormed join
  envJoin_preserves_observerTargets
    {left right join : Env} {targets : List LVal} {slotLifetime : Lifetime} :
    EnvJoin left right join →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets

theorem WriteBorrowTargets.preserves_observerTargets_of_landmarks
    (hlandmarks : UpdateBorrowInvariantLandmarks)
    {rank : Nat} {env result : Env} {path : Path}
    {writeTargets observerTargets : List LVal} {rhsTy : Ty}
    {slotLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path writeTargets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime observerTargets := by
  intro hcontained hobservers hrhs hwrites
  exact WriteBorrowTargets.rec
    (motive_1 := fun _rank _env _path _oldTy _rhsTy _result _updatedTy _ =>
      True)
    (motive_2 := fun _rank env _path _writeTargets constructorTy result _ =>
      ∀ {observerTargets slotLifetime},
        ContainedBorrowsWellFormed env →
        BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsWellFormedInSlot result slotLifetime observerTargets)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by
      intro env old ty
      trivial)
    (by
      intro env rank old joined ty _hshape _hjoin
      trivial)
    (by
      intro env₁ env₂ rank path inner updatedInner ty hupdate ih
      trivial)
    (by
      intro env₁ env₂ rank path targets ty hwrites ih
      trivial)
    (by
      intro rank env path ty observerTargets slotLifetime hcontained hobservers _hrhs
      exact ⟨hcontained, hobservers⟩)
    (by
      intro rank env updated path target ty hwrite _htyped _ih
        observerTargets slotLifetime hcontained hobservers hrhs
      exact hlandmarks.envWrite_preserves_observerTargets
        hcontained hobservers hrhs hwrite)
    (by
      intro rank env updated restEnv result path target rest ty
        hwrite _htyped _hwrites hjoin _ihWrite ihWrites
        observerTargets slotLifetime hcontained hobservers hrhs
      rcases hlandmarks.envWrite_preserves_observerTargets
          hcontained hobservers hrhs hwrite with
        ⟨hupdatedContained, hupdatedObservers⟩
      rcases ihWrites hcontained hobservers hrhs with
        ⟨hrestContained, hrestObservers⟩
      exact ⟨
        hlandmarks.envJoin_preserves_containedBorrowsWellFormed
          hjoin hupdatedContained hrestContained,
        hlandmarks.envJoin_preserves_observerTargets hjoin
          hupdatedObservers hrestObservers⟩)
    (by
      intro rank env₁ env₂ lv slot ty updatedTy hslot hupdate ih
      trivial)
    hwrites hcontained hobservers hrhs

theorem UpdateBorrowInvariantObligations.of_landmarks
    (hlandmarks : UpdateBorrowInvariantLandmarks) :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed := by
    intro rank env result path targets rhsTy slotLifetime
      _hrank _hcoh _hlin hcontained htargets _hleaf hrhs hwrites
    exact WriteBorrowTargets.preserves_observerTargets_of_landmarks
      hlandmarks hcontained htargets hrhs hwrites

/--
Definition 3.23 `writeBorrowTargets` borrow-invariant obligation.

This is the remaining paper-level update invariant needed by Lemma 4.9.  The
legacy theorem `updateBorrowInvariantObligations_appendix96` below records the
old Appendix 9.6 target as explicit result-side rank/coherence premises rather
than hiding them as axioms.
-/
theorem WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets := by
  exact hobligations.writeBorrowTargets_preserves_containedBorrowsWellFormed

/-- Appendix Lemma 9.6 package for the borrow-target fan-out.

This is an obligation-parametric compatibility route: the broad write-core and
fan-out rank/coherence facts are explicit premises until the remaining
result-side update obligations are proved constructively.
-/
theorem updateBorrowInvariantObligations_appendix96
    (hwriteCore :
      ∀ {rank : Nat} {env result : Env} {lv : LVal}
        {rhsTy : Ty} {slotLifetime : Lifetime},
        0 < rank →
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
        EnvWrite rank env lv rhsTy result →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env)
    (hfanoutRanked :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty} {φ : Name → Nat},
        WriteBorrowTargetsRhsVarsBelowBranches φ rank env path targets rhsTy)
    (hfanoutCoherence :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty},
        WriteBorrowTargetsCoherenceObligations rank env path targets rhsTy) :
    UpdateBorrowInvariantObligations := by
  exact UpdateBorrowInvariantObligations.of_crossLandmarks
    (updateBorrowInvariantCrossLandmarks_appendix96 hwriteCore)
    hfanoutRanked hfanoutCoherence

/--
Appendix Lemma 9.6 at the Definition 3.23 update-relation level.

The statement tracks both components needed by the enclosing `write` rule:
the intermediate environment remains contained-borrow well formed, and the
partial type returned by `update_k` has well-formed contained borrows at the
allocation lifetime of the slot being rebuilt.
-/
theorem UpdateAtPath.preserves_containedBorrowsWellFormed_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {rank : Nat} {env result : Env} {path : Path}
    {oldTy updatedTy : PartialTy} {rhsTy : Ty} {slotLifetime : Lifetime} :
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime oldTy →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    UpdateAtPath rank env path oldTy rhsTy result updatedTy →
    ContainedBorrowsWellFormed result ∧
      PartialTyBorrowsWellFormedInSlot result slotLifetime updatedTy := by
  intro hcoh hlin hcontained holdTy hrhsTy hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun _rank env _path oldTy constructorTy result updatedTy _ =>
      Coherent env → Linearizable env →
      ∀ {slotLifetime},
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime oldTy →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        ContainedBorrowsWellFormed result ∧
          PartialTyBorrowsWellFormedInSlot result slotLifetime updatedTy)
    (motive_2 := fun _rank _env _path _targets _rhsTy _result _ => True)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by
      intro env old ty hcoh hlin slotLifetime hcontained _holdTy hrhsTy
      exact ⟨hcontained, hrhsTy⟩)
    (by
      intro env rank old joined ty _hshape hjoin hcoh hlin slotLifetime hcontained holdTy hrhsTy
      exact ⟨hcontained,
        PartialTyBorrowsWellFormedInSlot.of_partialTyUnion
          (by simpa [PartialTyUnion] using hjoin) holdTy hrhsTy⟩)
    (by
      intro env₁ env₂ rank path inner updatedInner ty _hinner ih
        hcoh hlin slotLifetime hcontained holdTy hrhsTy
      rcases ih hcoh hlin hcontained
          (PartialTyBorrowsWellFormedInSlot.box_inv holdTy)
          hrhsTy with
        ⟨hcontainedResult, hupdatedInner⟩
      exact ⟨hcontainedResult, PartialTyBorrowsWellFormedInSlot.box hupdatedInner⟩)
    (by
      intro env₁ env₂ rank path targets ty hwrites _ih
        hcoh hlin slotLifetime hcontained holdTy hrhsTy
      have htargets :
          BorrowTargetsWellFormedInSlot env₁ slotLifetime targets :=
        holdTy PartialTyContains.here
      have htargetLeaves :
          ∀ target, target ∈ targets → ∀ targetSlot,
            env₁.slotAt (LVal.base (prependPath path target)) = some targetSlot →
            WriteLeafTy env₁ (LVal.path (prependPath path target)) targetSlot.ty ty :=
        WriteBorrowTargets.initialized_leaves_appendix96 htargets hwrites
      rcases WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
          hobligations (Nat.succ_pos rank) hcoh hlin hcontained htargets htargetLeaves
          hrhsTy hwrites with
        ⟨hcontainedResult, htargetsResult⟩
      exact ⟨hcontainedResult, by
        intro mutable selected hcontains
        cases hcontains
        exact htargetsResult⟩)
    (by
      intro rank env path ty
      trivial)
    (by
      intro rank env updated path target ty _hwrite _ih
      trivial)
    (by
      intro rank env updated restEnv result path target rest ty
        _hwrite _hwrites _hjoin _ihWrite _ihWrites
      trivial)
    (by
      intro rank env₁ env₂ lv slot ty updatedTy _hslot _hupdate _ih
      trivial)
    hupdate hcoh hlin hcontained holdTy hrhsTy

/--
Appendix Lemma 9.6, `W-Box` branch of Definition 3.23.

Updating through an owned box recursively updates the boxed partial type, then
replaces the original base slot with `.box updatedInner`.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_box_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ writeEnv env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {inner updatedInner oldTy : PartialTy}
    {rhs : Term} {rhsTy : Ty} {writeSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    env₂.slotAt (LVal.base lhs) = some writeSlot →
    writeSlot.ty = .box inner →
    UpdateAtPath 0 env₂ (LVal.path lhs) inner rhsTy writeEnv updatedInner →
    env₃ = writeEnv.update (LVal.base lhs)
      { writeSlot with ty := .box updatedInner } →
    ¬ WriteProhibited env₃ (.deref lhs) →
    ContainedBorrowsWellFormed env₃ := by
  intro hwellInitial hwellFormed hLhs _htargetLifetime hRhs _hshape hwellRhs
    hwriteSlot hwriteTy hinnerUpdate henv₃ hnotWrite
  subst henv₃
  have htargetOutlivesSlot :
      targetLifetime ≤ writeSlot.lifetime :=
    TermTyping.target_lifetime_outlives_surviving_base_slot
      hwellInitial hLhs hRhs (by simpa [LVal.base] using hwriteSlot)
  have hslotPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime writeSlot.ty :=
    ContainedBorrowsWellFormed.slot_partial hwellFormed.1 hwriteSlot
  have hinnerPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime inner := by
    rw [hwriteTy] at hslotPartial
    exact PartialTyBorrowsWellFormedInSlot.box_inv hslotPartial
  have hrhsPartialAtTarget :
      PartialTyBorrowsWellFormedInSlot env₂ targetLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellRhs
  have hrhsPartialAtSlot :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.weaken
      hrhsPartialAtTarget htargetOutlivesSlot
  rcases UpdateAtPath.preserves_containedBorrowsWellFormed_appendix96
      hobligations hwellFormed.2.2.1 hwellFormed.2.2.2 hwellFormed.1 hinnerPartial
      hrhsPartialAtSlot hinnerUpdate with
    ⟨hcontainedWriteEnv, hupdatedInnerPartial⟩
  have hnotWriteVar :
      ¬ WriteProhibited
        (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
        (.var (LVal.base lhs)) := by
    exact not_writeProhibited_var_base hnotWrite
  have hslotTargets :
      PartialTyBorrowsWellFormedInSlot
        (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
        writeSlot.lifetime
        ({ writeSlot with ty := .box updatedInner }).ty := by
    change PartialTyBorrowsWellFormedInSlot
      (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
      writeSlot.lifetime
      (.box updatedInner)
    have hboxedPartial :
        PartialTyBorrowsWellFormedInSlot writeEnv writeSlot.lifetime
          (.box updatedInner) :=
      PartialTyBorrowsWellFormedInSlot.box hupdatedInnerPartial
    intro mutable targets hcontains
    have htransported :
        PartialTyBorrowsWellFormedInSlot
          (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
          writeSlot.lifetime
          (.box updatedInner) :=
      PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts
        (x := LVal.base lhs)
        (slot := { writeSlot with ty := .box updatedInner })
        (partialTy := .box updatedInner)
        hnotWriteVar
        hboxedPartial
        (by
          intro mutable targets hcontains target htarget
          have hcontainsUpdated :
              (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner }) ⊢
                LVal.base lhs ↝ Ty.borrow mutable targets :=
            ⟨{ writeSlot with ty := .box updatedInner },
              by simp [Env.update],
              hcontains⟩
          exact not_pathConflicts_of_not_writeProhibited_contains
            hnotWriteVar hcontainsUpdated htarget)
    exact htransported hcontains
  exact ContainedBorrowsWellFormed.update_slot
    hcontainedWriteEnv hslotTargets hnotWriteVar

/--
Appendix Lemma 9.6, `W-MutB` branch of Definition 3.23.

Updating through a mutable borrow writes every possible borrowed target at
`rank + 1` and joins the resulting environments.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_mutBorrow_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {targets : List LVal} {oldTy : PartialTy}
    {rhs : Term} {rhsTy : Ty} {writeSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    env₂.slotAt (LVal.base lhs) = some writeSlot →
    writeSlot.ty = .ty (.borrow true targets) →
    WriteBorrowTargets 1 env₂ (LVal.path lhs) targets rhsTy env₃ →
    ¬ WriteProhibited
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
      (.deref lhs) →
    ContainedBorrowsWellFormed
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) }) := by
  intro hwellInitial hwellFormed hLhs _htargetLifetime hRhs _hshape hwellRhs
    hwriteSlot hwriteTy hwrites hnotWrite
  have htargetOutlivesSlot :
      targetLifetime ≤ writeSlot.lifetime :=
    TermTyping.target_lifetime_outlives_surviving_base_slot
      hwellInitial hLhs hRhs (by simpa [LVal.base] using hwriteSlot)
  have hslotPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime writeSlot.ty :=
    ContainedBorrowsWellFormed.slot_partial hwellFormed.1 hwriteSlot
  have htargetsOld :
      BorrowTargetsWellFormedInSlot env₂ writeSlot.lifetime targets := by
    rw [hwriteTy] at hslotPartial
    exact hslotPartial PartialTyContains.here
  have hrhsPartialAtTarget :
      PartialTyBorrowsWellFormedInSlot env₂ targetLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellRhs
  have hrhsPartialAtSlot :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.weaken
      hrhsPartialAtTarget htargetOutlivesSlot
  have htargetLeaves :
      ∀ target, target ∈ targets → ∀ targetSlot,
        env₂.slotAt (LVal.base (prependPath (LVal.path lhs) target)) = some targetSlot →
        WriteLeafTy env₂ (LVal.path (prependPath (LVal.path lhs) target))
          targetSlot.ty rhsTy :=
    WriteBorrowTargets.initialized_leaves_appendix96 htargetsOld hwrites
  rcases WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
      hobligations (by decide : 0 < 1) hwellFormed.2.2.1 hwellFormed.2.2.2
        hwellFormed.1 htargetsOld htargetLeaves hrhsPartialAtSlot hwrites with
    ⟨hcontainedWriteEnv, htargetsResult⟩
  have hnotWriteVar :
      ¬ WriteProhibited
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        (.var (LVal.base lhs)) := by
    exact not_writeProhibited_var_base hnotWrite
  have htargetsFinal :
      BorrowTargetsWellFormedInSlot
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        writeSlot.lifetime targets :=
    BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
      (x := LVal.base lhs)
      (slot := { writeSlot with ty := .ty (.borrow true targets) })
      hnotWriteVar
      htargetsResult
      (by
        intro target htarget
        have hcontainsUpdated :
            (env₃.update (LVal.base lhs)
              { writeSlot with ty := .ty (.borrow true targets) }) ⊢
              LVal.base lhs ↝ Ty.borrow true targets :=
          ⟨{ writeSlot with ty := .ty (.borrow true targets) },
            by simp [Env.update],
            PartialTyContains.here⟩
        exact not_pathConflicts_of_not_writeProhibited_contains
          hnotWriteVar hcontainsUpdated htarget)
  have hslotTargets :
      PartialTyBorrowsWellFormedInSlot
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        writeSlot.lifetime
        ({ writeSlot with ty := .ty (.borrow true targets) }).ty := by
    change PartialTyBorrowsWellFormedInSlot
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
      writeSlot.lifetime
      (.ty (.borrow true targets))
    intro mutable selected hcontains
    cases hcontains
    exact htargetsFinal
  exact ContainedBorrowsWellFormed.update_slot
    hcontainedWriteEnv hslotTargets hnotWriteVar

/--
Appendix Lemma 9.6, dereference/update component.

This is the part that needs the mutual induction over Definition 3.23:
`W-Box` recurses into the path, while `W-MutB` switches to
`writeBorrowTargets` and uses the environment-join borrow invariant.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ (.deref lhs) rhsTy env₃ →
    ¬ WriteProhibited env₃ (.deref lhs) →
    ContainedBorrowsWellFormed env₃ := by
  intro hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  cases hwrite with
  | intro hwriteSlot hupdate =>
      rename_i writeEnv writeSlot updatedTy
      simp [LVal.base] at hwriteSlot
      have hupdateCons :
          UpdateAtPath 0 env₂ (() :: LVal.path lhs) writeSlot.ty rhsTy
            writeEnv updatedTy := by
        simpa [LVal.path_deref_cons] using hupdate
      rcases UpdateAtPath.cons_inv hupdateCons with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, hwriteTy, hupdatedTy, hinnerUpdate⟩
        have hnotWriteBox :
            ¬ WriteProhibited
              (writeEnv.update (LVal.base lhs)
                { writeSlot with ty := .box updatedInner })
              (.deref lhs) := by
          simpa [LVal.base, hupdatedTy] using hnotWrite
        simpa [LVal.base, hupdatedTy] using
          EnvWrite.preserves_containedBorrowsWellFormed_deref_box_appendix96
            hobligations
            (lhs := lhs)
            hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
            hwriteSlot hwriteTy hinnerUpdate rfl hnotWriteBox
      · rcases hborrow with ⟨targets, hwriteTy, hupdatedTy, hwrites⟩
        have hwritesOne :
            WriteBorrowTargets 1 env₂ (LVal.path lhs) targets rhsTy writeEnv := by
          simpa using hwrites
        have hnotWriteBorrow :
            ¬ WriteProhibited
              (writeEnv.update (LVal.base lhs)
                { writeSlot with ty := .ty (.borrow true targets) })
              (.deref lhs) := by
          simpa [LVal.base, hupdatedTy] using hnotWrite
        simpa [LVal.base, hupdatedTy] using
          EnvWrite.preserves_containedBorrowsWellFormed_deref_mutBorrow_appendix96
            hobligations
            (lhs := lhs)
            hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
            hwriteSlot hwriteTy hwritesOne hnotWriteBorrow

/--
Appendix Lemma 9.6, borrow-target component.

The proof is the paper's induction over Definition 3.23:

* `W-Strong`/`W-Weak` reduce to replacing the base slot and checking the
  contained borrows of the updated partial type.
* `W-Box` is the recursive path case.
* `W-MutB` uses the corresponding induction over `writeBorrowTargets`, whose
  cons case is discharged by the environment-join borrow invariant.

The statement is deliberately at the assignment boundary rather than at a
syntactic variable case.  The right-hand side may change the environment from
`env₁` to `env₂`, and a write through `*w` may fan out through mutable-borrow
targets before joining the resulting environments.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_appendix96
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ContainedBorrowsWellFormed env₃ := by
  intro hobligations hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
    hwrite hnotWrite
  cases lhs with
  | var x =>
      rcases LValTyping.var_inv hLhs with
        ⟨sourceSlot, hsourceSlot, _hsourceTy, hsourceLifetime⟩
      cases hwrite with
      | intro hwriteSlot hupdate =>
          rename_i writeEnv writeSlot updatedTy
          simp [LVal.base] at hwriteSlot
          rcases (TermTyping.slot_lifetime_survives.1 hRhs)
              (by simpa [hsourceLifetime] using htargetLifetime)
              hsourceSlot with
            ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
          have hwriteSlotEq : writeSlot = rhsSlot := by
            have hsomeEq : some writeSlot = some rhsSlot := by
              rw [← hwriteSlot, hrhsSlot]
            exact Option.some.inj hsomeEq
          have hwriteLifetime : writeSlot.lifetime = targetLifetime := by
            rw [hwriteSlotEq, ← hrhsLifetime, hsourceLifetime]
          have hLhs₂ : LValTyping env₂ (.var x) writeSlot.ty targetLifetime := by
            rw [← hwriteLifetime]
            exact LValTyping.var hwriteSlot
          exact EnvWrite.preserves_containedBorrowsWellFormed_var
            hwellFormed hLhs₂ hwellRhs
            (EnvWrite.intro hwriteSlot hupdate)
            hnotWrite
    | deref lhs =>
        exact EnvWrite.preserves_containedBorrowsWellFormed_deref_appendix96
          hobligations hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
          hwrite hnotWrite

theorem EnvWrite.preserves_containedBorrowsWellFormed {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ContainedBorrowsWellFormed env₃ := by
  exact EnvWrite.preserves_containedBorrowsWellFormed_appendix96

/-- Assignment/update well-formedness using the precise RHS-edge rank premise.

The caller supplies the linearization witness for the pre-write environment,
proves that every newly installed RHS borrow edge points to a lower-ranked base,
and provides the lvalue-coherence transport facts for the write result. -/
theorem EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  have hlin3By :=
    EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all hwrite hlinBy hbelow
  have hlin3 := Linearizable.of_linearizedBy hlin3By
  have hcoh3 := EnvWrite.preserves_coherent_of_obligations
    hwellFormed.2.2.1 hwriteCoh
  exact ⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations hwellInitial hwellFormed hLhs
      htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite,
    EnvWrite.preserves_slotsOutlive hwellFormed.2.1 hwrite, hcoh3, hlin3⟩

/-- Assignment-level write-coherence side condition.

This is the remaining coherence proof boundary for `T-Assign`: after the RHS is
typed, the ranked write is performed, and the RHS borrow edges are known to point
downward, the resulting environment must be coherent.  The old
`EnvWrite.preserves_coherent` axiom tried to prove this from a per-target RHS
well-formedness premise, which is too weak.  This side condition is stated at the
assignment boundary where the needed typing/shape/rank facts are available.
-/
def AssignmentWritePreservesCoherent : Prop :=
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
    Coherent env₃

/-- Assignment/update well-formedness using explicit rank and coherence premises. -/
theorem EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    AssignmentWritePreservesCoherent →
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
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  have hlin3By :=
    EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all hwrite hlinBy hbelow
  have hlin3 := Linearizable.of_linearizedBy hlin3By
  have hcoh3 := hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact ⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations hwellInitial
      hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite,
    EnvWrite.preserves_slotsOutlive hwellFormed.2.1 hwrite, hcoh3, hlin3⟩

/-- Assignment preservation variant with the explicit RHS-edge rank premise. -/
theorem assign_preserves_wellFormed_of_rhsBorrowTargetsBelow
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow hobligations
    hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs htargetLifetime
    hRhs hshape hwellRhs hwrite hnotWrite

/-- Assignment preservation variant with explicit RHS-edge rank and coherence. -/
theorem assign_preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    AssignmentWritePreservesCoherent →
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
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite

def DropFullLValTypingTransport (env : Env) (parent child : Lifetime) : Prop :=
  ∀ {lv targetTy targetLifetime},
    LValBaseOutlives env lv parent →
    LValTyping env lv (.ty targetTy) targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv (.ty targetTy) targetLifetime

/--
Appendix Lemma 9.5 target-stability fragment.

If an lval is typed in a well-formed block body, its base slot survives the
enclosing parent lifetime, and the reached location also lives at the parent
side, then dropping the immediate child lifetime preserves the lval typing.
-/
theorem LValTyping.dropLifetime_child_of_base_outlives {env : Env}
    {parent child : Lifetime} {lv : LVal} {targetTy : Ty}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    LValBaseOutlives env lv parent →
    LValTyping env lv (.ty targetTy) targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv (.ty targetTy) targetLifetime := by
  intro hchild hwellBody hbase htyping houtlives
  have htransport :
      (∀ {lv partialTy lifetime},
        LValTyping env lv partialTy lifetime →
        LValBaseOutlives env lv parent →
        lifetime ≤ parent →
        LValTyping (env.dropLifetime child) lv partialTy lifetime) ∧
      (∀ {targets partialTy lifetime},
        LValTargetsTyping env targets partialTy lifetime →
        (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
        lifetime ≤ parent →
        LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime) := by
    constructor
    · intro lv partialTy lifetime htyping
      exact LValTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
        (motive_2 := fun targets partialTy lifetime _ =>
          (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
          lifetime ≤ parent →
          LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
        (by
          intro x slot hslot _hbase houtlives
          exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
            ⟨hslot, by
              intro hslotLifetime
              subst hslotLifetime
              exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.box (ih hbase houtlives))
        (by
          intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
            hborrow _htargets ihBorrow ihTargets hbase houtlives
          have hborrowLifetime : _borrowLifetime ≤ parent :=
            LValTyping.lifetime_outlives_of_base_outlives_one
              hwellBody.1 hborrow hbase
          have hwellTargetsAtBorrow :
              BorrowTargetsWellFormed env targets _borrowLifetime :=
            LValTyping.containedBorrowTargetsWellFormed_at_lifetime
              hwellBody.1 hborrow PartialTyContains.here
          have hwellTargets :
              BorrowTargetsWellFormed env targets parent :=
            BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
          exact LValTyping.borrow
            (ihBorrow hbase hborrowLifetime)
            (ihTargets
              (by
                intro target htarget
                rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
                exact hbaseTarget)
              houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
            _hhead _hrest hunion hintersection ihHead ihRest hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
    · intro targets partialTy lifetime htyping
      exact LValTargetsTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
        (motive_2 := fun targets partialTy lifetime _ =>
          (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
          lifetime ≤ parent →
          LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
        (by
          intro x slot hslot _hbase houtlives
          exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
            ⟨hslot, by
              intro hslotLifetime
              subst hslotLifetime
              exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.box (ih hbase houtlives))
        (by
          intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
            hborrow _htargets ihBorrow ihTargets hbase houtlives
          have hborrowLifetime : _borrowLifetime ≤ parent :=
            LValTyping.lifetime_outlives_of_base_outlives_one
              hwellBody.1 hborrow hbase
          have hwellTargetsAtBorrow :
              BorrowTargetsWellFormed env targets _borrowLifetime :=
            LValTyping.containedBorrowTargetsWellFormed_at_lifetime
              hwellBody.1 hborrow PartialTyContains.here
          have hwellTargets :
              BorrowTargetsWellFormed env targets parent :=
            BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
          exact LValTyping.borrow
            (ihBorrow hbase hborrowLifetime)
            (ihTargets
              (by
                intro target htarget
                rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
                exact hbaseTarget)
              houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
            _hhead _hrest hunion hintersection ihHead ihRest hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
  exact htransport.1 htyping hbase houtlives

theorem LValTargetsTyping.dropLifetime_child_of_member_base_outlives {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hbaseTargets htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy targetLifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      targetLifetime ≤ parent →
      LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime)
    ?var ?box ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget hbaseTargets houtlives
    exact LValTargetsTyping.singleton
      (LValTyping.dropLifetime_child_of_base_outlives
        hchild hwellBody (hbaseTargets target (by simp)) htarget houtlives)
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest hbaseTargets houtlives
    exact LValTargetsTyping.cons
      (LValTyping.dropLifetime_child_of_base_outlives hchild hwellBody
        (hbaseTargets target (by simp)) hhead
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives))
      (ihRest
        (by
          intro selected hselected
          exact hbaseTargets selected (by simp [hselected]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives))
      hunion hintersection

theorem LValTargetsTyping.dropLifetime_child_of_wellFormedTargets {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    BorrowTargetsWellFormed env targets parent →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hwellTargets htyping houtlives
  exact LValTargetsTyping.dropLifetime_child_of_member_base_outlives
    hchild hwellBody
    (by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
        ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbase⟩
      exact hbase)
    htyping houtlives

/-- Backward typing across a lifetime drop: `dropLifetime` only *removes* slots
(leaving the rest unchanged), so any typing in the dropped environment also holds
in the original. -/
theorem LValTyping.of_dropLifetime {env : Env} {child : Lifetime}
    {lv : LVal} {p : PartialTy} {lf : Lifetime}
    (h : LValTyping (env.dropLifetime child) lv p lf) : LValTyping env lv p lf := by
  refine LValTyping.rec
    (motive_1 := fun lv p lf _ => LValTyping env lv p lf)
    (motive_2 := fun targets p lf _ => LValTargetsTyping env targets p lf)
    ?var ?box ?borrow ?singleton ?cons h
  · intro x slot hslot
    rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _⟩
    exact LValTyping.var henvSlot
  · intro _lv _inner _lifetime _htyping ih
    exact LValTyping.box ih
  · intro _lv _mutable _targets _bLf _tLf _tTy _hborrow _htargets ihBorrow ihTargets
    exact LValTyping.borrow ihBorrow ihTargets
  · intro _target _ty _lifetime _htarget ih
    exact LValTargetsTyping.singleton ih
  · intro _target _rest _headTy _headLf _restLf _lf _restTy _unionTy
      _hhead _hrest hunion hint ihHead ihRest
    exact LValTargetsTyping.cons ihHead ihRest hunion hint

theorem LValTargetsTyping.dropLifetime_child_of_transport {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    DropFullLValTypingTransport env parent child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro htransport hbaseTargets htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy targetLifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      targetLifetime ≤ parent →
      LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime)
    ?var ?box ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget hbaseTargets houtlives
    exact LValTargetsTyping.singleton
      (htransport (hbaseTargets target (by simp)) htarget houtlives)
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest hbaseTargets houtlives
    exact LValTargetsTyping.cons
      (htransport (hbaseTargets target (by simp)) hhead
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives))
      (ihRest
        (by
          intro selected hselected
          exact hbaseTargets selected (by simp [hselected]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives))
      hunion hintersection

theorem BorrowTargetsWellFormedInSlot.dropLifetime_child_of_transport
    {env : Env} {parent child slotLifetime : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    slotLifetime ≤ parent →
    BorrowTargetsWellFormedInSlot (env.dropLifetime child) slotLifetime targets := by
  intro hchild htransport htargets hslotParent target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htyping, htargetOutlivesSlot, hbase⟩
  have hbaseParent : LValBaseOutlives env target parent := by
    rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
    exact ⟨baseSlot, hbaseSlot,
      LifetimeOutlives.trans hbaseOutlives hslotParent⟩
  refine ⟨targetTy, targetLifetime,
    htransport hbaseParent htyping
      (LifetimeOutlives.trans htargetOutlivesSlot hslotParent),
    htargetOutlivesSlot, ?_⟩
  exact LValBaseOutlives.dropLifetime_child hchild hslotParent hbase

theorem BorrowTargetsWellFormed.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormed env targets parent →
    BorrowTargetsWellFormed (env.dropLifetime child) targets parent := by
  intro hchild htransport htargets
  cases htargets with
  | intro hmembers =>
      refine BorrowTargetsWellFormed.intro ?_
      intro target htarget
      rcases hmembers target htarget with
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
      have hbaseParent : LValBaseOutlives env target parent := by
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        exact ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
      refine ⟨targetTy, targetLifetime,
        htransport hbaseParent htyping houtlives, houtlives, ?_⟩
      exact LValBaseOutlives.dropLifetime_child hchild
        (LifetimeOutlives.refl parent) hbase

theorem WellFormedTy.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    WellFormedTy env ty parent →
    WellFormedTy (env.dropLifetime child) ty parent := by
  intro hchild htransport hwellTy
  induction hwellTy with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | borrow htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.dropLifetime_child_of_transport
          hchild htransport htargets)
  | box _hinner ih =>
      exact WellFormedTy.box (ih hchild htransport)

theorem ContainedBorrowsWellFormed.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    DropFullLValTypingTransport env parent child →
    ContainedBorrowsWellFormed (env.dropLifetime child) := by
  intro hchild hwellBody htransport x slot mutable targets hslot hcontains
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨holdSlot, hslotNeChild⟩
  have holdContains : env ⊢ x ↝ Ty.borrow mutable targets :=
    EnvContains.dropLifetime_of_contains hcontains
  have hslotParent : slot.lifetime ≤ parent :=
    LifetimeChild.parent_of_outlives_child_ne hchild
      (hwellBody.2.1 x slot holdSlot) hslotNeChild
  exact BorrowTargetsWellFormedInSlot.dropLifetime_child_of_transport
    hchild
    htransport
    (hwellBody.1 x slot mutable targets holdSlot holdContains)
    hslotParent

/-- `Linearizable` is preserved by a lifetime drop (the same rank function works;
`dropLifetime` only removes slots). -/
theorem Linearizable.dropLifetime_child {env : Env} {child : Lifetime}
    (h : Linearizable env) : Linearizable (env.dropLifetime child) := by
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _⟩
  exact hφ x slot henvSlot

/-- `Coherent` is preserved by a lifetime drop: a borrow typed in the dropped
environment also types in the original (`of_dropLifetime`), where `Coherent env`
gives its targets a joint typing, which then transports back across the drop
(`dropLifetime_child_of_wellFormedTargets`).  The targets are well formed at
`parent` because the surviving borrow's base outlives `parent`. -/
theorem Coherent.dropLifetime_child {env : Env} {parent child : Lifetime}
    (hchild : LifetimeChild parent child) (hwellBody : WellFormedEnv env child)
    (hcohEnv : Coherent env) : Coherent (env.dropLifetime child) := by
  intro lv m T bLf hty
  have htyEnv := LValTyping.of_dropLifetime hty
  rcases hcohEnv lv m T bLf htyEnv with ⟨ty, lt, htgtsEnv⟩
  rcases LValTyping.base_slot_exists hty with ⟨dslot, hdslot⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hdslot with ⟨henvBase, hneChild⟩
  have hbaseParent : LValBaseOutlives env lv parent := by
    rcases LValTyping.base_outlives_one hwellBody htyEnv with ⟨bslot, hbslot, hble⟩
    have hEq : dslot = bslot := Option.some.inj (henvBase.symm.trans hbslot)
    exact ⟨bslot, hbslot,
      LifetimeChild.parent_of_outlives_child_ne hchild hble (hEq ▸ hneChild)⟩
  have hbLfParent : bLf ≤ parent :=
    LValTyping.lifetime_outlives_of_base_outlives_one hwellBody.1 htyEnv hbaseParent
  have hwellT : BorrowTargetsWellFormed env T parent :=
    BorrowTargetsWellFormed.weaken
      (LValTyping.containedBorrowTargetsWellFormed_at_lifetime hwellBody.1 htyEnv
        PartialTyContains.here)
      hbLfParent
  have hltParent : lt ≤ parent :=
    (LValTyping.lifetime_outlives_of_base_outlives hwellBody.1).2 htgtsEnv (by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellT target htarget with
        ⟨_, _, _, _, hb⟩
      exact hb)
  exact ⟨ty, lt, LValTargetsTyping.dropLifetime_child_of_wellFormedTargets
    hchild hwellBody hwellT htgtsEnv hltParent⟩

/--
Block drop preservation for well-formed environments, used in the `T-Block`
case of Lemma 4.9.

This is the environment side of Appendix Lemma 9.5 together with the
`Γ₂ ⊢ T ≽ l` premise from `T-Block`: dropping the block lifetime removes locals
without invalidating the result type at the enclosing lifetime.
-/
theorem Env.dropLifetime_preserves_wellFormed_child {env env' : Env}
    {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    WellFormedTy env ty parent →
    env' = env.dropLifetime child →
    WellFormedEnv env' parent ∧ WellFormedTy env' ty parent := by
  intro hchild hwellBody hwellTy hdrop
  subst hdrop
  have htransport : DropFullLValTypingTransport env parent child := by
    intro lv targetTy targetLifetime hbase htyping houtlives
    exact LValTyping.dropLifetime_child_of_base_outlives
      hchild hwellBody hbase htyping houtlives
  refine ⟨
    ⟨ContainedBorrowsWellFormed.dropLifetime_child_of_transport
        hchild hwellBody htransport,
      EnvSlotsOutlive.dropLifetime_child hchild hwellBody.2.1,
      Coherent.dropLifetime_child hchild hwellBody hwellBody.2.2.1,
      Linearizable.dropLifetime_child hwellBody.2.2.2⟩,
    WellFormedTy.dropLifetime_child_of_transport hchild htransport hwellTy⟩

theorem block_preserves_wellFormed {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₂ blockLifetime →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnv env₃ lifetime ∧ WellFormedTy env₃ ty lifetime := by
  intro hchild hwellBody _hterms hwellTy hdrop
  exact Env.dropLifetime_preserves_wellFormed_child hchild hwellBody hwellTy hdrop

theorem declare_preserves_wellFormed_of_output_fresh {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name}
    {term : Term} {ty : Ty} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    FreshUpdateCoherenceObligations env₂ x ty lifetime →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    WellFormedEnv env₃ lifetime := by
  intro hwellFormed hwellTy hfresh _hterm hcoh henv₃
  exact declare_preserves_wellFormed_output_fresh hwellFormed hwellTy hfresh hcoh henv₃

/--
Constructor landmarks for Lemma 4.9.

The term-typing induction is small once the update-sensitive constructors are
named at their paper granularity.  The final Lemma 4.9 route below uses the
rule-carried obligation induction instead of manufacturing this legacy landmark
package from broad write-preservation claims.
-/
structure TypingPreservesWellFormedObligations : Prop where
  block_preserves_wellFormed
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₂ blockLifetime →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnv env₃ lifetime ∧ WellFormedTy env₃ ty lifetime
  copy_result_wellFormed
    {env : Env} {lv : LVal} {ty : Ty}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    CopyTy ty →
    WellFormedTy env ty lifetime
  move_preserves_wellFormed
    {env env' : Env} {lv : LVal} {ty : Ty}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedEnv env' lifetime ∧ WellFormedTy env' ty lifetime
  assign_preserves_wellFormed
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime

/--
Lemma 4.9 induction, parameterized by the appendix landmarks.

This is the proof we want to keep clean: each typing constructor is handled
once, while the reusable update/move/copy facts are proved separately.
-/
theorem typingPreservesWellFormed_of_landmarks
    (hlandmarks : TypingPreservesWellFormedObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        hlandmarks.copy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      hlandmarks.move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      hlandmarks.block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcoh henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcoh)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellRhs hwrite _hranked _hwriteCoh hnotWrite ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨hlandmarks.assign_preserves_wellFormed hwellFormed result.1 hLhs
          (LValTyping.lifetime_outlives_one hwellFormed hLhs)
          hRhs hshape hwellRhs hwrite hnotWrite,
        WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
      (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
          _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
        let headResult := ihHead htypingEq hwellFormed
        ihRest htypingEq headResult.1)
      htyping rfl hwellFormed

/-- Lemma 4.9 well-formedness induction using rule-carried obligations.

The assignment rank/write-coherence facts and declaration fresh-slot coherence
fact come from the strengthened `T-Assign` and `T-Declare` constructors. -/
theorem typingPreservesWellFormed_of_ruleCarriedObligations
    (hobligations : UpdateBorrowInvariantObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed, copyTy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcohObligations henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcohObligations)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellRhs hwrite hranked hwriteCoh hnotWrite ih htypingEq
        hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        have htargetLifetime : _targetLifetime ≤ _lifetime :=
          LValTyping.lifetime_outlives_one hwellFormed hLhs
        rcases hranked with
          ⟨φ, hlinBy, hbelow⟩
        have hlin3By :=
          EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
            hwrite hlinBy hbelow
        have hcoh3 := EnvWrite.preserves_coherent_of_obligations
          result.1.2.2.1 hwriteCoh
        exact ⟨⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations
              hwellFormed result.1 hLhs htargetLifetime hRhs hshape hwellRhs
              hwrite hnotWrite,
            EnvWrite.preserves_slotsOutlive result.1.2.1 hwrite,
            hcoh3,
            Linearizable.of_linearizedBy hlin3By⟩,
          WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
      let headResult := ihHead htypingEq hwellFormed
      ihRest htypingEq headResult.1)
    htyping rfl hwellFormed

theorem borrowInvariance_emptyStoreTyping {store : ProgramStore}
    {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    ValidState store term →
    ValidStoreTyping store term StoreTyping.empty →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
    hobligations
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/--
Constructor-level runtime preservation landmarks used by Lemma 4.11.

The value, copy, borrow, box, and declaration cases are discharged by existing
multistep fragments.  The fields isolate the cases still requiring the paper's
general move/update/drop preservation arguments.
-/
structure RuntimePreservationObligations : Prop where
  move {store finalStore : ProgramStore} {env₁ env₂ : Env}
      {typing : StoreTyping} {lifetime : Lifetime}
      {lv : LVal} {ty : Ty} {finalValue : Value} :
      ValidRuntimeState store (.move lv) →
      ValidStoreTyping store (.move lv) typing →
      WellFormedEnv env₁ lifetime →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime (.move lv) ty env₂ →
      MultiStep store lifetime (.move lv) finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₂ ty
  assign {midStore finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
      {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
      {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
      {value finalValue : Value} :
      LValTyping env₁ lhs oldTy targetLifetime →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      ShapeCompatible env₂ oldTy (.ty rhsTy) →
      WellFormedTy env₂ rhsTy targetLifetime →
      EnvWrite 0 env₂ lhs rhsTy env₃ →
      ¬ WriteProhibited env₃ lhs →
      ValidRuntimeState midStore (.assign lhs (.val value)) →
      midStore ∼ₛ env₂ →
      ValidValue midStore value rhsTy →
      Step midStore lifetime (.assign lhs (.val value)) finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₃ .unit
  block {store finalStore : ProgramStore} {env₁ env₃ : Env}
      {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
      {terms : List Term} {ty : Ty} {finalValue : Value} :
      ValidRuntimeState store (.block blockLifetime terms) →
      ValidStoreTyping store (.block blockLifetime terms) typing →
      WellFormedEnv env₁ lifetime →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime (.block blockLifetime terms) ty env₃ →
      MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₃ ty

/--
Borrow invariance through the rule-carried obligation route.

Assignment rank/write-coherence and declaration fresh-slot coherence are part of
the strengthened typing derivation.  The only remaining fresh-coherence premise
is for the final result binding `gamma`, which is added after the term has been
typed.
-/
theorem borrowInvariance_of_ruleCarriedObligations
    (hobligations : UpdateBorrowInvariantObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
      hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/--
Lemma 4.11, Preservation.

This is stated over `ValidRuntimeState`, the mechanised package that contains
Definition 4.3's valid-state condition plus the explicit owner-allocation
invariant needed by our concrete store model.
-/
theorem preservation {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    RuntimePreservationObligations →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hobligations hvalidRuntime hvalidStoreTyping hwellFormed hsafe htyping hmulti
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      ∀ (store finalStore : ProgramStore) (finalValue : Value),
        ValidRuntimeState store term →
        ValidStoreTyping store term typing →
        WellFormedEnv env lifetime →
        store ∼ₛ env →
        MultiStep store lifetime term finalStore (.val finalValue) →
        TerminalStateSafe finalStore finalValue env₂ ty)
    (motive_2 := fun _env _typing _lifetime _terms _ty _env₂ _ => True)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping
        store finalStore finalValue hvalidRuntime hvalidStoreTyping _hwellFormed hsafe
        hmulti =>
      preservation_multistep_runtime_value hvalidRuntime hvalidStoreTyping hsafe
        (TermTyping.const hvalueTyping) hmulti)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy hnotRead
        store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        hmulti =>
      preservation_copy_multistep_runtime hwellFormed hsafe hvalidRuntime
        (TermTyping.copy (typing := _typing) hLv hcopy hnotRead) hmulti)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
        hLv hnotWrite hmove store finalStore finalValue hvalidRuntime hvalidStoreTyping
        hwellFormed hsafe hmulti =>
      hobligations.move hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        (TermTyping.move hLv hnotWrite hmove) hmulti)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hmutable hnotWrite
        store finalStore finalValue hvalidRuntime _hvalidStoreTyping _hwellFormed hsafe
        hmulti =>
      preservation_borrow_multistep_runtime hsafe hvalidRuntime
        (TermTyping.mutBorrow (typing := _typing) hLv hmutable hnotWrite) hmulti)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hnotRead
        store finalStore finalValue hvalidRuntime _hvalidStoreTyping _hwellFormed hsafe
        hmulti =>
      preservation_borrow_multistep_runtime hsafe hvalidRuntime
        (TermTyping.immBorrow (typing := _typing) hLv hnotRead) hmulti)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih
        store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed hsafe hmulti =>
      preservation_box_context_terminal_multistep_runtime
        (by
          intro midStore value hvalidInner hvalidStoreTypingInner hsafeInner
            _hinnerTyping hmultiInner
          exact ih store midStore value hvalidInner hvalidStoreTypingInner
            hwellFormed hsafeInner hmultiInner)
        hvalidRuntime hvalidStoreTyping hsafe (TermTyping.box hterm) hmulti)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop _ih store finalStore finalValue hvalidRuntime
        hvalidStoreTyping hwellFormed hsafe hmulti =>
      hobligations.block hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        (TermTyping.block hblockChild hterms hwellTy hdrop) hmulti)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfresh hterm hfreshOut _hcoh henv₃ ih
        store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        hmulti =>
      by
        rcases multistep_declare_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hdeclareStep⟩
        rcases ih store midStore value
            (validRuntimeState_declare_inner hvalidRuntime)
            (validStoreTyping_declare_inner hvalidStoreTyping)
            hwellFormed hsafe hinnerMulti with
          ⟨hvalidInner, hsafeInner, hvalidValue⟩
        cases hdeclareStep with
        | declare hstore =>
            have hpreserved :=
              preservation_declare_redex_runtime_of_validValue hsafeInner
                hfreshOut
                (validRuntimeState_declare_value_of_value hvalidInner)
                hvalidValue
                (Step.declare (lifetime := _lifetime) hstore)
            rw [henv₃]
            exact hpreserved)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellTy hwrite hranked hcoh hnotWrite _ih store finalStore finalValue
        hvalidRuntime hvalidStoreTyping hwellFormed hsafe hmulti =>
      by
        rcases multistep_assign_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hassignStep⟩
        rcases _ih store midStore value
            (validRuntimeState_assign_inner hvalidRuntime)
            (validStoreTyping_assign_inner hvalidStoreTyping)
            hwellFormed hsafe hinnerMulti with
          ⟨hvalidInner, hsafeInner, hvalidValue⟩
        exact hobligations.assign hLhs hRhs hshape hwellTy hwrite hnotWrite
          (validRuntimeState_assign_value_of_value hvalidInner)
          hsafeInner hvalidValue hassignStep)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm _ih => trivial)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest _ihHead _ihRest => trivial)
    htyping store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
    hsafe hmulti

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Lemma 4.9, with the final fresh-result coherence obligation exposed. -/
theorem lemma_4_9_borrowInvariance
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {gamma : Name}
    (hupdate : UpdateBorrowInvariantObligations)
    (hrefs : ∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime)
    (hvalid : ValidState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hfresh : env₂.fresh gamma)
    (hfreshCoherence : FreshUpdateCoherenceObligations env₂ gamma ty lifetime) :
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime :=
  borrowInvariance_of_ruleCarriedObligations
    hupdate
    hrefs hvalid hstoreTyping hwellFormed hsafe htyping hfresh hfreshCoherence

end LwRust.Paper.Soundness
