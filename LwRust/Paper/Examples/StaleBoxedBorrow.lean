import LwRust.Paper.Soundness.Helpers.BorrowWellFormed

/-!
# Stale boxed borrow annotations

Path-insensitive joins can conservatively retain a loan annotation whose target
has been moved out on another branch.  Such an annotation must still protect the
target from later reads/writes, but it should not force the target to be
currently initialized.  The target's base slot is still present, here as
`x : undef int`.
-/

namespace LwRust
namespace Paper

open Core

def staleBoxedBorrowXSlot : EnvSlot :=
  { ty := .undef .int, lifetime := Lifetime.root }

def staleBoxedBorrowPSlot : EnvSlot :=
  { ty := .box (.ty (.borrow true [.var "x"])), lifetime := Lifetime.root }

def staleBoxedBorrowEnv : Env :=
  { slotAt := fun name =>
      if name = "x" then some staleBoxedBorrowXSlot
      else if name = "p" then some staleBoxedBorrowPSlot
      else none }

def staleBoxedBorrowStore : ProgramStore :=
  { slotAt := fun location =>
      if location = .var "x" then
        some { value := .undef, lifetime := Lifetime.root }
      else if location = .var "p" then
        some
          { value := .value (.ref { location := .heap 0, owner := true }),
            lifetime := Lifetime.root }
      else if location = .heap 0 then
        some
          { value := .value (.ref { location := .var "x", owner := false }),
            lifetime := Lifetime.root }
      else none }

def staleBoxedBorrowTypingShape
    (lv : LVal) (partialTy : PartialTy) (lifetime : Lifetime) : Prop :=
  (lv = .var "x" ∧ partialTy = .undef .int ∧ lifetime = Lifetime.root) ∨
    (lv = .var "p" ∧
      partialTy = .box (.ty (.borrow true [.var "x"])) ∧
      lifetime = Lifetime.root) ∨
    (lv = .deref (.var "p") ∧
      partialTy = .ty (.borrow true [.var "x"]) ∧
      lifetime = Lifetime.root)

theorem staleBoxedBorrowEnv_contains_p :
    staleBoxedBorrowEnv ⊢ "p" ↝ (.borrow true [.var "x"]) := by
  refine ⟨staleBoxedBorrowPSlot, ?_, PartialTyContains.box PartialTyContains.here⟩
  simp [staleBoxedBorrowEnv]

theorem staleBoxedBorrowEnv_x_not_initialized :
    ¬ ∃ ty lifetime,
      LValTyping staleBoxedBorrowEnv (.var "x") (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htyping⟩
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, htyEq, _hlifetimeEq⟩
  have hslotEq : staleBoxedBorrowXSlot = slot := by
    simpa [staleBoxedBorrowEnv] using hslot
  rw [← hslotEq] at htyEq
  simp [staleBoxedBorrowXSlot] at htyEq

theorem staleBoxedBorrowTypingShape_var_x_not_full {ty : Ty}
    {lifetime : Lifetime} :
    ¬ staleBoxedBorrowTypingShape (.var "x") (.ty ty) lifetime := by
  intro hshape
  rcases hshape with hshape | hshape | hshape
  · rcases hshape with ⟨_hlv, hty, _hlifetime⟩
    cases hty
  · rcases hshape with ⟨hlv, _hty, _hlifetime⟩
    simp at hlv
  · rcases hshape with ⟨hlv, _hty, _hlifetime⟩
    cases hlv

theorem staleBoxedBorrowEnv_lvalTyping_shape {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTyping staleBoxedBorrowEnv lv partialTy lifetime →
    staleBoxedBorrowTypingShape lv partialTy lifetime := by
  exact LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      staleBoxedBorrowTypingShape lv partialTy lifetime)
    (motive_2 := fun targets _partialTy _lifetime _ =>
      targets = [.var "x"] → False)
    (by
      intro name slot hslot
      by_cases hx : name = "x"
      · subst hx
        have hslotEq : slot = staleBoxedBorrowXSlot := by
          exact (Option.some.inj
            (by simpa [staleBoxedBorrowEnv] using hslot)).symm
        subst hslotEq
        exact Or.inl ⟨rfl, rfl, rfl⟩
      · by_cases hp : name = "p"
        · subst hp
          have hslotEq : slot = staleBoxedBorrowPSlot := by
            exact (Option.some.inj
              (by simpa [staleBoxedBorrowEnv] using hslot)).symm
          subst hslotEq
          exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
        · have hnone : staleBoxedBorrowEnv.slotAt name = none := by
            simp [staleBoxedBorrowEnv, hx, hp]
          rw [hnone] at hslot
          cases hslot)
    (by
      intro source inner lifetime _hsource ihSource
      rcases ihSource with hsourceShape | hsourceShape | hsourceShape
      · rcases hsourceShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hsourceShape with ⟨hlv, hty, hlifetime⟩
        subst hlv
        cases hty
        exact Or.inr (Or.inr ⟨rfl, rfl, hlifetime⟩)
      · rcases hsourceShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty)
    (by
      intro source mutable targets borrowLifetime targetLifetime targetTy
        _hborrow _htargets ihBorrow ihTargets
      rcases ihBorrow with hborrowShape | hborrowShape | hborrowShape
      · rcases hborrowShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hborrowShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty
      · rcases hborrowShape with ⟨_hlv, hty, _hlifetime⟩
        cases hty
        exact False.elim (ihTargets rfl))
    (by
      intro target ty lifetime _htarget ihTarget htargetsEq
      cases htargetsEq
      exact staleBoxedBorrowTypingShape_var_x_not_full ihTarget)
    (by
      intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
        _hhead _hrest _hunion _hintersection ihHead _ihRest htargetsEq
      cases htargetsEq
      exact staleBoxedBorrowTypingShape_var_x_not_full ihHead)

theorem staleBoxedBorrowEnv_contained_whenInitialized :
    ContainedBorrowsWellFormedWhenInitialized staleBoxedBorrowEnv := by
  intro root slot mutable targets hslot hcontains target htarget
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hrootX : root = "x"
  · subst hrootX
    have hcontainedEq : containedSlot = staleBoxedBorrowXSlot := by
      simpa [staleBoxedBorrowEnv] using hcontainedSlot.symm
    subst hcontainedEq
    cases hcontainsTy
  · by_cases hrootP : root = "p"
    · subst hrootP
      have hcontainedEq : containedSlot = staleBoxedBorrowPSlot := by
        simpa [staleBoxedBorrowEnv] using hcontainedSlot.symm
      subst hcontainedEq
      have htargetsEq : targets = [.var "x"] := by
        cases hcontainsTy with
        | box hinner =>
            cases hinner
            rfl
      subst htargetsEq
      simp at htarget
      subst htarget
      refine ⟨?_, ?_⟩
      · exact ⟨staleBoxedBorrowXSlot, by
          simp [staleBoxedBorrowEnv, LVal.base],
          LifetimeOutlives.refl Lifetime.root⟩
      · intro hinitialized
        exact (staleBoxedBorrowEnv_x_not_initialized hinitialized).elim
    · have hnone : staleBoxedBorrowEnv.slotAt root = none := by
        simp [staleBoxedBorrowEnv, hrootX, hrootP]
      rw [hnone] at hcontainedSlot
      cases hcontainedSlot

theorem staleBoxedBorrowEnv_not_containedBorrowsWellFormed :
    ¬ ContainedBorrowsWellFormed staleBoxedBorrowEnv := by
  intro hcontained
  have htargets :=
    hcontained "p" staleBoxedBorrowPSlot true [.var "x"]
      (by simp [staleBoxedBorrowEnv])
      staleBoxedBorrowEnv_contains_p (.var "x") (by simp)
  rcases htargets with ⟨ty, lifetime, htyping, _houtlives, _hbase⟩
  exact staleBoxedBorrowEnv_x_not_initialized ⟨ty, lifetime, htyping⟩

theorem staleBoxedBorrowEnv_readProhibited_x :
    ReadProhibited staleBoxedBorrowEnv (.var "x") := by
  exact ⟨"p", [.var "x"], .var "x", staleBoxedBorrowEnv_contains_p,
    by simp, by simp [PathConflicts, LVal.base]⟩

theorem staleBoxedBorrowEnv_writeProhibited_x :
    WriteProhibited staleBoxedBorrowEnv (.var "x") :=
  Or.inl staleBoxedBorrowEnv_readProhibited_x

theorem staleBoxedBorrowEnv_exposes_stale_borrow :
    LValTyping staleBoxedBorrowEnv (.deref (.var "p"))
      (.ty (.borrow true [.var "x"])) Lifetime.root := by
  have hp : staleBoxedBorrowEnv.slotAt "p" = some staleBoxedBorrowPSlot := by
    simp [staleBoxedBorrowEnv]
  exact LValTyping.box (LValTyping.var hp)

theorem staleBoxedBorrowEnv_no_double_deref_typing :
    ¬ ∃ partialTy lifetime,
      LValTyping staleBoxedBorrowEnv (.deref (.deref (.var "p")))
        partialTy lifetime := by
  rintro ⟨partialTy, lifetime, htyping⟩
  have hshape := staleBoxedBorrowEnv_lvalTyping_shape htyping
  rcases hshape with hshape | hshape | hshape
  · rcases hshape with ⟨hlv, _hty, _hlifetime⟩
    cases hlv
  · rcases hshape with ⟨hlv, _hty, _hlifetime⟩
    cases hlv
  · rcases hshape with ⟨hlv, _hty, _hlifetime⟩
    cases hlv

theorem staleBoxedBorrowEnv_targets_not_initialized :
    ¬ BorrowTargetsInitialized staleBoxedBorrowEnv [.var "x"] := by
  intro hinitialized
  exact staleBoxedBorrowEnv_x_not_initialized
    (hinitialized (.var "x") (by simp))

theorem staleBoxedBorrowEnv_coherent_whenInitialized :
    CoherentWhenInitialized staleBoxedBorrowEnv := by
  intro lv mutable targets borrowLifetime htyping hinitialized
  have hshape := staleBoxedBorrowEnv_lvalTyping_shape htyping
  rcases hshape with hshape | hshape | hshape
  · rcases hshape with ⟨_hlv, hty, _hlifetime⟩
    cases hty
  · rcases hshape with ⟨_hlv, hty, _hlifetime⟩
    cases hty
  · rcases hshape with ⟨_hlv, hty, _hlifetime⟩
    cases hty
    exact (staleBoxedBorrowEnv_targets_not_initialized hinitialized).elim

def staleBoxedBorrowRank : Name → Nat :=
  fun name => if name = "p" then 1 else 0

theorem staleBoxedBorrowEnv_linearizedBy :
    LinearizedBy staleBoxedBorrowRank staleBoxedBorrowEnv := by
  intro name slot hslot v hv
  by_cases hx : name = "x"
  · subst hx
    have hslotEq : slot = staleBoxedBorrowXSlot := by
      exact (Option.some.inj
        (by simpa [staleBoxedBorrowEnv] using hslot)).symm
    subst hslotEq
    simp [staleBoxedBorrowXSlot, PartialTy.vars] at hv
  · by_cases hp : name = "p"
    · subst hp
      have hslotEq : slot = staleBoxedBorrowPSlot := by
        exact (Option.some.inj
          (by simpa [staleBoxedBorrowEnv] using hslot)).symm
      subst hslotEq
      have hvx : v = "x" := by
        simpa [staleBoxedBorrowPSlot, PartialTy.vars, Ty.vars, LVal.base] using hv
      subst hvx
      simp [staleBoxedBorrowRank]
    · have hnone : staleBoxedBorrowEnv.slotAt name = none := by
        simp [staleBoxedBorrowEnv, hx, hp]
      rw [hnone] at hslot
      cases hslot

theorem staleBoxedBorrowEnv_linearizable :
    Linearizable staleBoxedBorrowEnv :=
  ⟨staleBoxedBorrowRank, staleBoxedBorrowEnv_linearizedBy⟩

theorem staleBoxedBorrowEnv_slots_outlive_root :
    EnvSlotsOutlive staleBoxedBorrowEnv Lifetime.root := by
  intro name slot hslot
  by_cases hx : name = "x"
  · subst hx
    have hslotEq : slot = staleBoxedBorrowXSlot := by
      exact (Option.some.inj
        (by simpa [staleBoxedBorrowEnv] using hslot)).symm
    subst hslotEq
    exact LifetimeOutlives.refl Lifetime.root
  · by_cases hp : name = "p"
    · subst hp
      have hslotEq : slot = staleBoxedBorrowPSlot := by
        exact (Option.some.inj
          (by simpa [staleBoxedBorrowEnv] using hslot)).symm
      subst hslotEq
      exact LifetimeOutlives.refl Lifetime.root
    · have hnone : staleBoxedBorrowEnv.slotAt name = none := by
        simp [staleBoxedBorrowEnv, hx, hp]
      rw [hnone] at hslot
      cases hslot

theorem staleBoxedBorrowEnv_wellFormed_whenInitialized :
    WellFormedEnvWhenInitialized staleBoxedBorrowEnv Lifetime.root :=
  ⟨staleBoxedBorrowEnv_contained_whenInitialized,
    staleBoxedBorrowEnv_slots_outlive_root,
    staleBoxedBorrowEnv_coherent_whenInitialized,
    staleBoxedBorrowEnv_linearizable⟩

theorem staleBoxedBorrowStore_safe_whenInitialized :
    SafeAbstractionWhenInitialized staleBoxedBorrowStore staleBoxedBorrowEnv := by
  constructor
  · intro name
    constructor
    · intro hstore
      rcases hstore with ⟨slot, hslot⟩
      by_cases hx : name = "x"
      · subst hx
        exact ⟨staleBoxedBorrowXSlot, by simp [staleBoxedBorrowEnv]⟩
      · by_cases hp : name = "p"
        · subst hp
          exact ⟨staleBoxedBorrowPSlot, by simp [staleBoxedBorrowEnv]⟩
        · have hnone :
            staleBoxedBorrowStore.slotAt (VariableProjection name) = none := by
            simp [staleBoxedBorrowStore, VariableProjection, hx, hp]
          rw [hnone] at hslot
          cases hslot
    · intro henv
      rcases henv with ⟨envSlot, henvSlot⟩
      by_cases hx : name = "x"
      · subst hx
        exact ⟨{ value := .undef, lifetime := Lifetime.root }, by
          simp [staleBoxedBorrowStore, VariableProjection]⟩
      · by_cases hp : name = "p"
        · subst hp
          exact ⟨
            { value := .value (.ref { location := .heap 0, owner := true }),
              lifetime := Lifetime.root }, by
              simp [staleBoxedBorrowStore, VariableProjection]⟩
        · have hnone : staleBoxedBorrowEnv.slotAt name = none := by
            simp [staleBoxedBorrowEnv, hx, hp]
          rw [hnone] at henvSlot
          cases henvSlot
  · intro name envSlot henvSlot
    by_cases hx : name = "x"
    · subst hx
      have hslotEq : envSlot = staleBoxedBorrowXSlot := by
        exact (Option.some.inj
          (by simpa [staleBoxedBorrowEnv] using henvSlot)).symm
      subst hslotEq
      exact ⟨.undef, by
          simp [staleBoxedBorrowStore, VariableProjection,
            staleBoxedBorrowXSlot],
        ValidPartialValueWhenInitialized.undef⟩
    · by_cases hp : name = "p"
      · subst hp
        have hslotEq : envSlot = staleBoxedBorrowPSlot := by
          exact (Option.some.inj
            (by simpa [staleBoxedBorrowEnv] using henvSlot)).symm
        subst hslotEq
        refine ⟨.value (.ref { location := .heap 0, owner := true }), ?_, ?_⟩
        · simp [staleBoxedBorrowStore, VariableProjection,
            staleBoxedBorrowPSlot]
        · refine ValidPartialValueWhenInitialized.box
            (slot :=
              { value := .value (.ref { location := .var "x", owner := false }),
                lifetime := Lifetime.root }) ?heapSlot ?inner
          · simp [staleBoxedBorrowStore]
          · exact ValidPartialValueWhenInitialized.borrowStale
              (location := .var "x") (mutable := true)
              (targets := [.var "x"])
              staleBoxedBorrowEnv_targets_not_initialized
      · have hnone : staleBoxedBorrowEnv.slotAt name = none := by
          simp [staleBoxedBorrowEnv, hx, hp]
        rw [hnone] at henvSlot
        cases henvSlot

theorem staleBoxedBorrowEnv_not_coherent :
    ¬ Coherent staleBoxedBorrowEnv := by
  intro hcoherent
  rcases hcoherent (.deref (.var "p")) true [.var "x"] Lifetime.root
      staleBoxedBorrowEnv_exposes_stale_borrow with
    ⟨targetTy, targetLifetime, htargets⟩
  cases htargets with
  | singleton htarget =>
      exact staleBoxedBorrowEnv_x_not_initialized
        ⟨targetTy, targetLifetime, htarget⟩
  | cons _hhead hrest _hunion _hintersection =>
      cases hrest

theorem staleBoxedBorrowEnv_not_wellFormedEnv :
    ¬ WellFormedEnv staleBoxedBorrowEnv Lifetime.root := by
  intro hwell
  exact staleBoxedBorrowEnv_not_coherent hwell.2.2.1

end Paper
end LwRust
