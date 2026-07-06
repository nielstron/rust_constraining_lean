import LwRust.Paper.Soundness.Helpers.BorrowWellFormed

/-!
# Soundness helpers: Appendix preliminaries

Single-target preliminaries that remain after deleting target-list joins and
fan-out write machinery.
-/

namespace LwRust
namespace Paper

open Core

theorem partialTyStrengthens_trans {left middle right : PartialTy} :
    PartialTyStrengthens left middle →
    PartialTyStrengthens middle right →
    PartialTyStrengthens left right := by
  exact partialTyStrengthens_trans_safe

theorem PartialTyStrengthens.to_unit_inv {sourceTy : Ty} :
    PartialTyStrengthens (.ty sourceTy) (.ty .unit) →
    sourceTy = .unit := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.to_int_inv {sourceTy : Ty} :
    PartialTyStrengthens (.ty sourceTy) (.ty .int) →
    sourceTy = .int := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.to_box_ty_inv {sourceTy inner : Ty} :
    PartialTyStrengthens (.ty sourceTy) (.ty (.box inner)) →
    ∃ sourceInner,
      sourceTy = .box sourceInner ∧
        PartialTyStrengthens (.ty sourceInner) (.ty inner) := by
  intro hstrength
  cases hstrength with
  | reflex => exact ⟨inner, rfl, PartialTyStrengthens.reflex⟩
  | tyBox hinner => exact ⟨_, rfl, hinner⟩

theorem PartialTyStrengthens.from_unit_inv {targetTy : Ty} :
    PartialTyStrengthens (.ty .unit) (.ty targetTy) →
    targetTy = .unit := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.from_int_inv {targetTy : Ty} :
    PartialTyStrengthens (.ty .int) (.ty targetTy) →
    targetTy = .int := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.from_box_ty_inv {sourceInner targetTy : Ty} :
    PartialTyStrengthens (.ty (.box sourceInner)) (.ty targetTy) →
    ∃ targetInner,
      targetTy = .box targetInner ∧
        PartialTyStrengthens (.ty sourceInner) (.ty targetInner) := by
  intro hstrength
  cases hstrength with
  | reflex => exact ⟨sourceInner, rfl, PartialTyStrengthens.reflex⟩
  | tyBox hinner => exact ⟨_, rfl, hinner⟩

theorem PartialTyStrengthens.from_borrow_inv {mutable : Bool}
    {sourceTarget : LVal} {targetTy : Ty} :
    PartialTyStrengthens (.ty (.borrow mutable sourceTarget)) (.ty targetTy) →
    targetTy = .borrow mutable sourceTarget := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.to_borrow_right {source : PartialTy}
    {mutable : Bool} {target : LVal} :
    PartialTyStrengthens source (.ty (.borrow mutable target)) →
    source = .ty (.borrow mutable target) := by
  intro hstrength
  cases hstrength
  · rfl

theorem PartialTyStrengthens.box_inv {left right : PartialTy} :
    PartialTyStrengthens (.box left) (.box right) →
    PartialTyStrengthens left right := by
  intro hstrength
  cases hstrength with
  | reflex => exact PartialTyStrengthens.reflex
  | box hinner => exact hinner

theorem PartialTyStrengthens.not_undef_to_ty {left right : Ty} :
    ¬ PartialTyStrengthens (.undef left) (.ty right) := by
  intro hstrength
  cases hstrength

theorem PartialTyStrengthens.not_undef_to_box {left : Ty} {right : PartialTy} :
    ¬ PartialTyStrengthens (.undef left) (.box right) := by
  intro hstrength
  cases hstrength

theorem PartialTyStrengthens.not_ty_to_box {left : Ty} {right : PartialTy} :
    ¬ PartialTyStrengthens (.ty left) (.box right) := by
  intro hstrength
  cases hstrength

theorem PartialTyStrengthens.ty_to_undef_inv {left right : Ty} :
    PartialTyStrengthens (.ty left) (.undef right) →
    PartialTyStrengthens (.ty left) (.ty right) := by
  intro hstrength
  cases hstrength with
  | intoUndef hinner => exact hinner

theorem PartialTyStrengthens.box_to_undef_inv {left : PartialTy} {right : Ty} :
    PartialTyStrengthens (.box left) (.undef right) →
    ∃ inner,
      right = .box inner ∧
        PartialTyStrengthens left (.undef inner) := by
  intro hstrength
  cases hstrength with
  | boxIntoUndef hinner => exact ⟨_, rfl, hinner⟩

theorem PartialTyStrengthens.to_ty_right {source : PartialTy} {target : Ty} :
    PartialTyStrengthens source (.ty target) →
    ∃ sourceTy, source = .ty sourceTy := by
  intro hstrength
  cases hstrength with
  | reflex => exact ⟨target, rfl⟩
  | tyBox => exact ⟨_, rfl⟩

theorem LValTyping.deref_box_inv {env : Env} {source : LVal}
    {inner : PartialTy} {lifetime : Lifetime} :
    LValTyping env (.deref source) (.box inner) lifetime →
    LValTyping env source (.box (.box inner)) lifetime := by
  intro htyping
  cases htyping with
  | box hsource => exact hsource

@[refl] theorem Ty.sameShape_refl (a : Ty) : Ty.sameShape a a := by
  exact Ty.rec
    (motive_1 := fun a => Ty.sameShape a a)
    (motive_2 := fun p => PartialTy.sameShape p p)
    (by trivial)
    (by trivial)
    (by intro _ _; rfl)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    a

@[refl] theorem PartialTy.sameShape_refl (a : PartialTy) :
    PartialTy.sameShape a a := by
  exact PartialTy.rec
    (motive_1 := fun a => Ty.sameShape a a)
    (motive_2 := fun p => PartialTy.sameShape p p)
    (by trivial)
    (by trivial)
    (by intro _ _; rfl)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    a

theorem Ty.sameShape_symm {a b : Ty} (h : Ty.sameShape a b) :
    Ty.sameShape b a := by
  have key : ∀ a b, Ty.sameShape a b → Ty.sameShape b a := by
    intro a
    refine Ty.rec (motive_1 := fun a => ∀ b, Ty.sameShape a b → Ty.sameShape b a)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b h; cases b <;> simp_all [Ty.sameShape]
    · intro b h; cases b <;> simp_all [Ty.sameShape]
    · intro _ _ b h; cases b <;> simp_all [Ty.sameShape]
    · intro _ ih b h
      cases b with
      | box t' => exact ih t' h
      | unit => simp [Ty.sameShape] at h
      | int => simp [Ty.sameShape] at h
      | borrow _ _ => simp [Ty.sameShape] at h
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b h

theorem PartialTy.sameShape_symm {a b : PartialTy}
    (h : PartialTy.sameShape a b) : PartialTy.sameShape b a := by
  cases a <;> cases b <;>
    simp_all [PartialTy.sameShape] <;>
    first
      | exact Ty.sameShape_symm (by assumption)
      | exact (PartialTy.sameShape_symm (by assumption))

theorem Ty.sameShape_trans {a b c : Ty}
    (h₁ : Ty.sameShape a b) (h₂ : Ty.sameShape b c) : Ty.sameShape a c := by
  have key : ∀ a b c, Ty.sameShape a b → Ty.sameShape b c → Ty.sameShape a c := by
    intro a
    refine Ty.rec
      (motive_1 := fun a => ∀ b c, Ty.sameShape a b → Ty.sameShape b c →
        Ty.sameShape a c)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.sameShape]
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.sameShape]
    · intro _ _ b c h1 h2; cases b <;> cases c <;> simp_all [Ty.sameShape]
    · intro _ ih b c h1 h2
      cases b with
      | box tb =>
          cases c with
          | box tc => exact ih tb tc h1 h2
          | unit => simp [Ty.sameShape] at h2
          | int => simp [Ty.sameShape] at h2
          | borrow _ _ => simp [Ty.sameShape] at h2
      | unit => simp [Ty.sameShape] at h1
      | int => simp [Ty.sameShape] at h1
      | borrow _ _ => simp [Ty.sameShape] at h1
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b c h₁ h₂

theorem PartialTy.sameShape_trans {a b c : PartialTy}
    (h₁ : PartialTy.sameShape a b) (h₂ : PartialTy.sameShape b c) :
    PartialTy.sameShape a c := by
  cases a <;> cases b <;> cases c <;>
    simp_all [PartialTy.sameShape] <;>
    first
      | exact Ty.sameShape_trans (by assumption) (by assumption)
      | exact PartialTy.sameShape_trans (by assumption) (by assumption)

def EnvShapePreserved (source result : Env) : Prop :=
  ∀ x resultSlot, result.slotAt x = some resultSlot →
    ∃ sourceSlot, source.slotAt x = some sourceSlot ∧
      PartialTy.sameShape sourceSlot.ty resultSlot.ty

@[refl] theorem EnvShapePreserved.refl (env : Env) :
    EnvShapePreserved env env := by
  intro x slot hslot
  exact ⟨slot, hslot, PartialTy.sameShape_refl slot.ty⟩

theorem EnvShapePreserved.trans {first second third : Env} :
    EnvShapePreserved first second →
    EnvShapePreserved second third →
    EnvShapePreserved first third := by
  intro h12 h23 x slot hslot
  rcases h23 x slot hslot with ⟨secondSlot, hsecondSlot, hshape23⟩
  rcases h12 x secondSlot hsecondSlot with ⟨firstSlot, hfirstSlot, hshape12⟩
  exact ⟨firstSlot, hfirstSlot, PartialTy.sameShape_trans hshape12 hshape23⟩

theorem EnvShapePreserved.branch_sameShape {source left right : Env} :
    EnvShapePreserved source left →
    EnvShapePreserved source right →
    ∀ x leftSlot rightSlot,
      left.slotAt x = some leftSlot →
      right.slotAt x = some rightSlot →
      PartialTy.sameShape leftSlot.ty rightSlot.ty := by
  intro hleft hright x leftSlot rightSlot hleftSlot hrightSlot
  rcases hleft x leftSlot hleftSlot with
    ⟨sourceLeftSlot, hsourceLeftSlot, hshapeLeft⟩
  rcases hright x rightSlot hrightSlot with
    ⟨sourceRightSlot, hsourceRightSlot, hshapeRight⟩
  have hsourceEq : sourceLeftSlot = sourceRightSlot :=
    Option.some.inj (hsourceLeftSlot.symm.trans hsourceRightSlot)
  subst hsourceEq
  exact PartialTy.sameShape_trans (PartialTy.sameShape_symm hshapeLeft) hshapeRight

theorem EnvShapePreserved.update_from_source_slot {source middle : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvShapePreserved source middle →
    source.slotAt x = some slot →
    PartialTy.sameShape slot.ty newTy →
    EnvShapePreserved source (middle.update x { slot with ty := newTy }) := by
  intro hpres hslot hshape y resultSlot hresultSlot
  by_cases hy : y = x
  · subst hy
    have hresultSlotEq : resultSlot = { slot with ty := newTy } := by
      exact (Option.some.inj (by simpa [Env.update] using hresultSlot)).symm
    subst hresultSlotEq
    exact ⟨slot, hslot, hshape⟩
  · have hmiddleSlot : middle.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresultSlot
    exact hpres y resultSlot hmiddleSlot

@[refl] theorem Ty.eqv_refl (t : Ty) : Ty.eqv t t := by
  exact Ty.rec
    (motive_1 := fun t => Ty.eqv t t)
    (motive_2 := fun p => PartialTy.eqv p p)
    (by trivial)
    (by trivial)
    (by intro _ _; exact ⟨rfl, rfl⟩)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    t

@[refl] theorem PartialTy.eqv_refl (pt : PartialTy) : PartialTy.eqv pt pt := by
  exact PartialTy.rec
    (motive_1 := fun t => Ty.eqv t t)
    (motive_2 := fun p => PartialTy.eqv p p)
    (by trivial)
    (by trivial)
    (by intro _ _; exact ⟨rfl, rfl⟩)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    (by intro _ ih; exact ih)
    pt

theorem ShapeCompatible.symm {env : Env} {left right : PartialTy} :
    ShapeCompatible env left right →
    ShapeCompatible env right left := by
  intro h
  induction h with
  | unit => exact ShapeCompatible.unit
  | int => exact ShapeCompatible.int
  | tyBox _ ih => exact ShapeCompatible.tyBox ih
  | box _ ih => exact ShapeCompatible.box ih
  | borrow hleft hright hshape ih =>
      exact ShapeCompatible.borrow hright hleft ih
  | undefLeft _ ih => exact ShapeCompatible.undefRight ih
  | undefRight _ ih => exact ShapeCompatible.undefLeft ih

theorem PartialTy.sameShape_of_shapeCompatible {env : Env} {a b : Ty} :
    ShapeCompatible env (.ty a) (.ty b) → PartialTy.sameShape (.ty a) (.ty b) := by
  intro h
  have aux : ∀ {left right : PartialTy}, ShapeCompatible env left right →
      (match left, right with
      | .ty _, .ty _ => PartialTy.sameShape left right
      | _, _ => True) := by
    intro left right hcompat
    induction hcompat with
    | unit => simp [PartialTy.sameShape, Ty.sameShape]
    | int => simp [PartialTy.sameShape, Ty.sameShape]
    | tyBox _ ih => simpa [PartialTy.sameShape, Ty.sameShape] using ih
    | box _ _ => trivial
    | borrow => simp [PartialTy.sameShape, Ty.sameShape]
    | undefLeft _ _ => trivial
    | undefRight _ _ => simp
  exact aux (left := .ty a) (right := .ty b) h

theorem ty_sameShape_of_strengthens {a b : Ty}
    (h : PartialTyStrengthens (.ty a) (.ty b)) :
    Ty.sameShape a b := by
  have aux : ∀ {left right : PartialTy}, PartialTyStrengthens left right →
      (match left, right with
      | .ty leftTy, .ty rightTy => Ty.sameShape leftTy rightTy
      | _, _ => True) := by
    intro left right hstrength
    induction hstrength with
    | reflex =>
        rename_i ty
        cases ty <;> try trivial
    | box _ _ => trivial
    | tyBox _ ih => simpa [Ty.sameShape] using ih
    | undefLeft _ _ => trivial
    | intoUndef _ _ => trivial
    | boxIntoUndef _ _ => trivial
  simpa using aux h

end Paper
end LwRust
