import FWRust.Paper.Soundness.Helpers.BorrowWellFormed

/-!
# Soundness helpers: AppendixPrelim

Appendix 9.1 preliminary lemmas (strengthening, type unions, etc.).
-/

namespace FWRust
namespace Paper

open Core

/-! ## Appendix 9.1: Preliminary Lemmas -/

/-- A binary type union strengthens its left input. -/
theorem PartialTyUnion.left_strengthens {left right union : PartialTy} :
    PartialTyUnion left right union →
    PartialTyStrengthens left union := by
  intro h
  exact h.1 (by simp)

/-- A binary type union strengthens its right input. -/
theorem PartialTyUnion.right_strengthens {left right union : PartialTy} :
    PartialTyUnion left right union →
    PartialTyStrengthens right union := by
  intro h
  exact h.1 (by simp)

theorem PartialTyUnion.symm {left right union : PartialTy} :
    PartialTyUnion left right union →
    PartialTyUnion right left union := by
  intro hunion
  simpa [PartialTyUnion, PartialTyJoin, Set.pair_comm] using hunion

/-- Lemma 9.2, Transitive Strengthening. -/
theorem partialTyStrengthens_trans {left middle right : PartialTy} :
    PartialTyStrengthens left middle →
    PartialTyStrengthens middle right →
    PartialTyStrengthens left right := by
  intro hleft hright
  induction hleft generalizing right with
  | reflex =>
      exact hright
  | box hbox ih =>
      cases hright with
      | reflex =>
          exact PartialTyStrengthens.box hbox
      | box hinner =>
          exact PartialTyStrengthens.box (ih hinner)
      | boxIntoUndef hinner =>
          exact PartialTyStrengthens.boxIntoUndef (ih hinner)
  | tyBox hbox ih =>
      cases hright with
      | reflex =>
          exact PartialTyStrengthens.tyBox hbox
      | tyBox hinner =>
          exact PartialTyStrengthens.tyBox (ih hinner)
      | intoUndef hinner =>
          cases hinner with
          | reflex =>
              exact PartialTyStrengthens.intoUndef
                (PartialTyStrengthens.tyBox hbox)
          | tyBox hrightInner =>
              exact PartialTyStrengthens.intoUndef
                (PartialTyStrengthens.tyBox (ih hrightInner))
  | borrow hsubset₁ hnonempty₁ =>
      cases hright with
      | reflex =>
          exact PartialTyStrengthens.borrow hsubset₁ hnonempty₁
      | borrow hsubset₂ hnonempty₂ =>
          exact PartialTyStrengthens.borrow
            (fun target hmem => hsubset₂ (hsubset₁ hmem))
            (fun hrightNonempty => hnonempty₁ (hnonempty₂ hrightNonempty))
      | intoUndef hinner =>
          cases hinner with
          | reflex =>
            exact PartialTyStrengthens.intoUndef
                (PartialTyStrengthens.borrow hsubset₁ hnonempty₁)
          | borrow hsubset₂ hnonempty₂ =>
              exact PartialTyStrengthens.intoUndef
                (PartialTyStrengthens.borrow
                  (fun target hmem => hsubset₂ (hsubset₁ hmem))
                  (fun hrightNonempty => hnonempty₁ (hnonempty₂ hrightNonempty)))
  | undefLeft hundef ih =>
      cases hright with
      | reflex =>
          exact PartialTyStrengthens.undefLeft hundef
      | undefLeft hinner =>
          exact PartialTyStrengthens.undefLeft (ih hinner)
  | intoUndef hundef ih =>
      cases hright with
      | reflex =>
          exact PartialTyStrengthens.intoUndef hundef
      | undefLeft hinner =>
          exact PartialTyStrengthens.intoUndef
            (ih hinner)
  | boxIntoUndef hundef ih =>
      cases hright with
      | reflex =>
          exact PartialTyStrengthens.boxIntoUndef hundef
      | undefLeft hinner =>
          cases hinner with
          | reflex =>
              exact PartialTyStrengthens.boxIntoUndef hundef
          | tyBox hbox =>
              exact PartialTyStrengthens.boxIntoUndef
                (ih (PartialTyStrengthens.undefLeft hbox))

theorem PartialTyStrengthens.borrow_subset {mutable : Bool}
    {leftTargets rightTargets : List LVal} :
    PartialTyStrengthens (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets)) →
    leftTargets.Subset rightTargets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      intro target hmem
      exact hmem
  | borrow hsubset _hnonempty =>
      exact hsubset

theorem PartialTyStrengthens.borrow_nonempty {mutable : Bool}
    {leftTargets rightTargets : List LVal} :
    PartialTyStrengthens (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets)) →
    rightTargets ≠ [] →
    leftTargets ≠ [] := by
  intro hstrength
  cases hstrength with
  | reflex =>
      intro hright
      exact hright
  | borrow _hsubset hnonempty =>
      exact hnonempty

theorem PartialTyStrengthens.to_borrow_inv {sourceTy : Ty}
    {mutable : Bool} {targets : List LVal} :
    PartialTyStrengthens (.ty sourceTy) (.ty (.borrow mutable targets)) →
    ∃ sourceTargets,
      sourceTy = .borrow mutable sourceTargets ∧
      sourceTargets.Subset targets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨targets, rfl, by intro target hmem; exact hmem⟩
  | borrow hsubset _hnonempty =>
      exact ⟨_, rfl, hsubset⟩

theorem PartialTyStrengthens.to_borrow_inv_nonempty {sourceTy : Ty}
    {mutable : Bool} {targets : List LVal} :
    PartialTyStrengthens (.ty sourceTy) (.ty (.borrow mutable targets)) →
    ∃ sourceTargets,
      sourceTy = .borrow mutable sourceTargets ∧
      sourceTargets.Subset targets ∧
      (targets ≠ [] → sourceTargets ≠ []) := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨targets, rfl, by intro target hmem; exact hmem, fun h => h⟩
  | borrow hsubset hnonempty =>
      exact ⟨_, rfl, hsubset, hnonempty⟩

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

theorem PartialTyStrengthens.to_bool_inv {sourceTy : Ty} :
    PartialTyStrengthens (.ty sourceTy) (.ty .bool) →
    sourceTy = .bool := by
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
  | reflex =>
      exact ⟨inner, rfl, PartialTyStrengthens.reflex⟩
  | tyBox hinner =>
      exact ⟨_, rfl, hinner⟩

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

theorem PartialTyStrengthens.from_bool_inv {targetTy : Ty} :
    PartialTyStrengthens (.ty .bool) (.ty targetTy) →
    targetTy = .bool := by
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
  | reflex =>
      exact ⟨sourceInner, rfl, PartialTyStrengthens.reflex⟩
  | tyBox hinner =>
      exact ⟨_, rfl, hinner⟩

theorem PartialTyStrengthens.from_borrow_inv {mutable : Bool}
    {sourceTargets : List LVal} {targetTy : Ty} :
    PartialTyStrengthens (.ty (.borrow mutable sourceTargets)) (.ty targetTy) →
    ∃ targetTargets,
      targetTy = .borrow mutable targetTargets ∧
        sourceTargets.Subset targetTargets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨sourceTargets, rfl, by intro target hmem; exact hmem⟩
  | borrow hsubset _hnonempty =>
      exact ⟨_, rfl, hsubset⟩

theorem PartialTyStrengthens.to_borrow_right {source : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyStrengthens source (.ty (.borrow mutable targets)) →
    ∃ sourceTargets,
      source = .ty (.borrow mutable sourceTargets) ∧
      sourceTargets.Subset targets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨targets, rfl, by intro target hmem; exact hmem⟩
  | borrow hsubset _hnonempty =>
      exact ⟨_, rfl, hsubset⟩

theorem PartialTyStrengthens.to_borrow_right_nonempty {source : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyStrengthens source (.ty (.borrow mutable targets)) →
    ∃ sourceTargets,
      source = .ty (.borrow mutable sourceTargets) ∧
      sourceTargets.Subset targets ∧
      (targets ≠ [] → sourceTargets ≠ []) := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨targets, rfl, by intro target hmem; exact hmem, fun h => h⟩
  | borrow hsubset hnonempty =>
      exact ⟨_, rfl, hsubset, hnonempty⟩

theorem PartialTyStrengthens.box_inv {left right : PartialTy} :
    PartialTyStrengthens (.box left) (.box right) →
    PartialTyStrengthens left right := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact PartialTyStrengthens.reflex
  | box hinner =>
      exact hinner

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
  | intoUndef hinner =>
      exact hinner

theorem PartialTyStrengthens.box_to_undef_inv {left : PartialTy} {right : Ty} :
    PartialTyStrengthens (.box left) (.undef right) →
    ∃ inner,
      right = .box inner ∧
        PartialTyStrengthens left (.undef inner) := by
  intro hstrength
  cases hstrength with
  | boxIntoUndef hinner =>
      exact ⟨_, rfl, hinner⟩

theorem PartialTyStrengthens.to_ty_right {source : PartialTy} {target : Ty} :
    PartialTyStrengthens source (.ty target) →
    ∃ sourceTy, source = .ty sourceTy := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨target, rfl⟩
  | borrow _hsubset =>
      exact ⟨.borrow _ _, rfl⟩
  | tyBox _hinner =>
      exact ⟨.box _, rfl⟩

theorem PartialTyUnion.ty_ty_full {left right : Ty} {union : PartialTy} :
    PartialTyUnion (.ty left) (.ty right) union →
    ∃ ty, union = .ty ty := by
  intro hunion
  have hleftStrength := PartialTyUnion.left_strengthens hunion
  cases hleftStrength with
  | reflex =>
      exact ⟨left, rfl⟩
  | borrow hsubset =>
      exact ⟨.borrow _ _, rfl⟩
  | tyBox _hinner =>
      exact ⟨.box _, rfl⟩
  | intoUndef hleftRight =>
      rename_i upperTy
      have hrightStrength := PartialTyUnion.right_strengthens hunion
      cases hrightStrength with
      | intoUndef hrightUpper =>
      have hupper : (.ty upperTy) ∈ upperBounds ({.ty left, .ty right} : Set PartialTy) := by
        intro candidate hcandidate
        simp at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst hcandidate
          show PartialTyStrengthens (.ty left) (.ty upperTy)
          exact hleftRight
        · subst hcandidate
          show PartialTyStrengthens (.ty right) (.ty upperTy)
          exact hrightUpper
      have hundefLeTy :
          PartialTyStrengthens (.undef upperTy) (.ty upperTy) := by
        simpa [partialTy_le_iff] using hunion.2 hupper
      exact False.elim (PartialTyStrengthens.not_undef_to_ty hundefLeTy)

theorem LValTargetsTyping.output_full {env : Env}
    {targets : List LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTargetsTyping env targets partialTy lifetime →
    ∃ ty, partialTy = .ty ty := by
  intro htyping
  exact LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun _targets partialTy _lifetime _ =>
      ∃ ty, partialTy = .ty ty)
    (by
      intro _x _slot _hslot
      trivial)
    (by
      intro _lv _inner _lifetime _htyping _ih
      trivial)
    (by
      intro _lv _inner _lifetime _htyping _ih
      trivial)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets _ihBorrow _ihTargets
      trivial)
    (by
      intro _target ty _lifetime _htarget _ihTarget
      exact ⟨ty, rfl⟩)
    (by
      intro _target _rest headTy _headLifetime _restLifetime _lifetime restTy
        unionTy _hhead _hrest hunion _hintersection _ihHead ihRest
      rcases ihRest with ⟨restFull, hrestFull⟩
      subst hrestFull
      exact PartialTyUnion.ty_ty_full hunion)
    htyping

theorem LValTargetsTyping.not_box {env : Env}
    {targets : List LVal} {inner : PartialTy} {lifetime : Lifetime} :
    ¬ LValTargetsTyping env targets (.box inner) lifetime := by
  intro htyping
  rcases LValTargetsTyping.output_full htyping with ⟨ty, hfull⟩
  cases hfull

theorem LValTyping.deref_box_inv {env : Env} {source : LVal}
    {inner : PartialTy} {lifetime : Lifetime} :
    LValTyping env (.deref source) (.box inner) lifetime →
    LValTyping env source (.box (.box inner)) lifetime := by
  intro htyping
  cases htyping with
  | box hsource =>
      exact hsource
  | borrow _hborrow htargets =>
      exact False.elim (LValTargetsTyping.not_box htargets)

theorem PartialTyUnion.box_box_shape {left right union : PartialTy} :
    PartialTyUnion (.box left) (.box right) union →
    ∃ inner, union = .box inner := by
  intro hunion
  have hleftStrength := PartialTyUnion.left_strengthens hunion
  cases hleftStrength with
  | reflex =>
      exact ⟨left, rfl⟩
  | box hleftInner =>
      exact ⟨_, rfl⟩
  | boxIntoUndef hleftUpper =>
      rename_i upperTy
      have hrightStrength := PartialTyUnion.right_strengthens hunion
      cases hrightStrength with
      | boxIntoUndef hrightUpper =>
          have hupper :
              (.box (.undef upperTy)) ∈ upperBounds ({.box left, .box right} : Set PartialTy) := by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact PartialTyStrengthens.box hleftUpper
            · subst hcandidate
              exact PartialTyStrengthens.box hrightUpper
          have hundefLeBox :
              PartialTyStrengthens (.undef (.box upperTy)) (.box (.undef upperTy)) := by
            simpa [partialTy_le_iff] using hunion.2 hupper
          exact False.elim (PartialTyStrengthens.not_undef_to_box hundefLeBox)

theorem PartialTyUnion.tyBox {left right union : Ty} :
    PartialTyUnion (.ty left) (.ty right) (.ty union) →
    PartialTyUnion (.ty (.box left)) (.ty (.box right)) (.ty (.box union)) := by
  intro hunion
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.tyBox (PartialTyUnion.left_strengthens hunion)
    · subst hcandidate
      exact PartialTyStrengthens.tyBox (PartialTyUnion.right_strengthens hunion)
  · intro upper hupper
    have hleftUpper :
        PartialTyStrengthens (.ty (.box left)) upper :=
      hupper (.ty (.box left)) (by simp)
    have hrightUpper :
        PartialTyStrengthens (.ty (.box right)) upper :=
      hupper (.ty (.box right)) (by simp)
    cases hleftUpper with
    | reflex =>
        rcases PartialTyStrengthens.from_box_ty_inv hrightUpper with
          ⟨rightUpper, hupperEq, hrightInner⟩
        cases hupperEq
        have hunionLeft : PartialTyStrengthens (.ty union) (.ty left) :=
          hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact PartialTyStrengthens.reflex
            · subst hcandidate
              exact hrightInner)
        exact PartialTyStrengthens.tyBox hunionLeft
    | tyBox hleftInner =>
        rename_i upperInner
        rcases PartialTyStrengthens.from_box_ty_inv hrightUpper with
          ⟨rightUpper, hupperEq, hrightInner⟩
        cases hupperEq
        have hunionUpper : PartialTyStrengthens (.ty union) (.ty upperInner) :=
          hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact hleftInner
            · subst hcandidate
              exact hrightInner)
        exact PartialTyStrengthens.tyBox hunionUpper
    | intoUndef hleftInner =>
        rename_i upperTy
        rcases PartialTyStrengthens.from_box_ty_inv hleftInner with
          ⟨leftUpper, hupperTyEq, hleftInnerTy⟩
        cases hupperTyEq
        have hrightInnerFull :
            PartialTyStrengthens (.ty (.box right)) (.ty (.box leftUpper)) :=
          PartialTyStrengthens.ty_to_undef_inv hrightUpper
        rcases PartialTyStrengthens.from_box_ty_inv hrightInnerFull with
          ⟨rightUpper, hrightEq, hrightInner⟩
        cases hrightEq
        have hunionUpper : PartialTyStrengthens (.ty union) (.ty leftUpper) :=
          hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact hleftInnerTy
            · subst hcandidate
              exact hrightInner)
        exact PartialTyStrengthens.intoUndef
          (PartialTyStrengthens.tyBox hunionUpper)

theorem PartialTyUnion.tyBox_inv {left right union : Ty} :
    PartialTyUnion (.ty (.box left)) (.ty (.box right)) (.ty (.box union)) →
    PartialTyUnion (.ty left) (.ty right) (.ty union) := by
  intro hunion
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      rcases PartialTyStrengthens.from_box_ty_inv
          (PartialTyUnion.left_strengthens hunion) with
        ⟨leftUpper, hupperEq, hleftInner⟩
      cases hupperEq
      exact hleftInner
    · subst hcandidate
      rcases PartialTyStrengthens.from_box_ty_inv
          (PartialTyUnion.right_strengthens hunion) with
        ⟨rightUpper, hupperEq, hrightInner⟩
      cases hupperEq
      exact hrightInner
  · intro upper hupper
    cases upper with
    | ty upperTy =>
        have hboxedUpper :
            (.ty (.box upperTy)) ∈
              upperBounds ({.ty (.box left), .ty (.box right)} : Set PartialTy) := by
          intro candidate hcandidate
          simp at hcandidate
          rcases hcandidate with hcandidate | hcandidate
          · subst hcandidate
            exact PartialTyStrengthens.tyBox
              (hupper (.ty left) (by simp))
          · subst hcandidate
            exact PartialTyStrengthens.tyBox
              (hupper (.ty right) (by simp))
        rcases PartialTyStrengthens.from_box_ty_inv (hunion.2 hboxedUpper) with
          ⟨unionUpper, hupperEq, hunionInner⟩
        cases hupperEq
        exact hunionInner
    | undef upperTy =>
        have hboxedUpper :
            (.undef (.box upperTy)) ∈
              upperBounds ({.ty (.box left), .ty (.box right)} : Set PartialTy) := by
          intro candidate hcandidate
          simp at hcandidate
          rcases hcandidate with hcandidate | hcandidate
          · subst hcandidate
            exact PartialTyStrengthens.intoUndef
              (PartialTyStrengthens.tyBox
                (PartialTyStrengthens.ty_to_undef_inv
                  (hupper (.ty left) (by simp))))
          · subst hcandidate
            exact PartialTyStrengthens.intoUndef
              (PartialTyStrengthens.tyBox
                (PartialTyStrengthens.ty_to_undef_inv
                  (hupper (.ty right) (by simp))))
        have hboxedUnionToUndef :
            PartialTyStrengthens (.ty (.box union)) (.ty (.box upperTy)) :=
          PartialTyStrengthens.ty_to_undef_inv (hunion.2 hboxedUpper)
        rcases PartialTyStrengthens.from_box_ty_inv hboxedUnionToUndef with
          ⟨unionUpper, hupperEq, hunionInner⟩
        cases hupperEq
        exact PartialTyStrengthens.intoUndef hunionInner
    | box upperInner =>
        have hleftUpper : PartialTyStrengthens (.ty left) (.box upperInner) :=
          hupper (.ty left) (show (.ty left : PartialTy) ∈
            ({.ty left, .ty right} : Set PartialTy) by simp)
        exact False.elim
          (PartialTyStrengthens.not_ty_to_box hleftUpper)

theorem PartialTyUnion.borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal} :
    leftTargets ≠ [] →
    rightTargets ≠ [] →
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable (leftTargets ++ rightTargets))) := by
  intro hleftNonempty hrightNonempty
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.borrow
        (by
        intro target hmem
        exact List.mem_append.mpr (Or.inl hmem))
        (fun _ => hleftNonempty)
    · subst hcandidate
      exact PartialTyStrengthens.borrow
        (by
        intro target hmem
        exact List.mem_append.mpr (Or.inr hmem))
        (fun _ => hrightNonempty)
  · intro upper hupper
    have hleftUpper :
        PartialTyStrengthens (.ty (.borrow mutable leftTargets)) upper :=
      hupper (.ty (.borrow mutable leftTargets)) (by simp)
    have hrightUpper :
        PartialTyStrengthens (.ty (.borrow mutable rightTargets)) upper :=
      hupper (.ty (.borrow mutable rightTargets)) (by simp)
    cases hleftUpper with
    | reflex =>
        have hrightSubset : rightTargets.Subset leftTargets :=
          PartialTyStrengthens.borrow_subset hrightUpper
        exact PartialTyStrengthens.borrow
          (by
          intro target hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hmem
          · exact hrightSubset hmem)
          (fun _ happendEmpty => hleftNonempty (_root_.List.eq_nil_of_append_eq_nil happendEmpty).1)
    | borrow hleftSubset hleftUpperNonempty =>
        rename_i upperTargets
        have hrightSubset : rightTargets.Subset upperTargets :=
          PartialTyStrengthens.borrow_subset hrightUpper
        exact PartialTyStrengthens.borrow
          (List.append_subset_of_subset_of_subset hleftSubset hrightSubset)
          (fun _ happendEmpty => hleftNonempty (_root_.List.eq_nil_of_append_eq_nil happendEmpty).1)
    | intoUndef hleftInner =>
        rename_i upperTy
        have hleftBorrow :
            ∃ upperTargets,
              upperTy = .borrow mutable upperTargets ∧
                leftTargets.Subset upperTargets ∧
                (upperTargets ≠ [] → leftTargets ≠ []) := by
          cases hleftInner with
          | reflex =>
              exact ⟨leftTargets, rfl, fun _ h => h, fun h => h⟩
          | borrow hsubset hnonempty =>
              exact ⟨_, rfl, hsubset, hnonempty⟩
        rcases hleftBorrow with
          ⟨upperTargets, hupperTy, hleftSubset, hleftUpperNonempty⟩
        subst hupperTy
        have hrightSubset : rightTargets.Subset upperTargets := by
          cases hrightUpper with
          | intoUndef hrightInner =>
              cases hrightInner with
              | reflex =>
                  exact fun _ h => h
              | borrow hsubset _hnonempty =>
                  exact hsubset
        exact PartialTyStrengthens.intoUndef
          (PartialTyStrengthens.borrow
            (List.append_subset_of_subset_of_subset hleftSubset hrightSubset)
            (fun _ happendEmpty =>
              hleftNonempty (_root_.List.eq_nil_of_append_eq_nil happendEmpty).1))

theorem PartialTyJoin.ty_of_common_upper {a b u : Ty} :
    PartialTyStrengthens (.ty a) (.ty u) →
    PartialTyStrengthens (.ty b) (.ty u) →
    ∃ j, PartialTyJoin (.ty a) (.ty b) (.ty j) ∧
      PartialTyStrengthens (.ty j) (.ty u) := by
  have key : ∀ u, ∀ a b,
      PartialTyStrengthens (.ty a) (.ty u) →
      PartialTyStrengthens (.ty b) (.ty u) →
      ∃ j, PartialTyJoin (.ty a) (.ty b) (.ty j) ∧
        PartialTyStrengthens (.ty j) (.ty u) := by
    refine Ty.rec
      (motive_1 := fun u => ∀ a b,
        PartialTyStrengthens (.ty a) (.ty u) →
        PartialTyStrengthens (.ty b) (.ty u) →
        ∃ j, PartialTyJoin (.ty a) (.ty b) (.ty j) ∧
          PartialTyStrengthens (.ty j) (.ty u))
      (motive_2 := fun _ => True)
      ?unit ?int ?borrow ?box ?bool ?partialTy ?partialBox ?partialUndef
    · intro a b ha hb
      have haEq := PartialTyStrengthens.to_unit_inv ha
      have hbEq := PartialTyStrengthens.to_unit_inv hb
      subst haEq
      subst hbEq
      exact ⟨.unit, PartialTyJoin.self (.ty .unit),
        PartialTyStrengthens.reflex⟩
    · intro a b ha hb
      have haEq := PartialTyStrengthens.to_int_inv ha
      have hbEq := PartialTyStrengthens.to_int_inv hb
      subst haEq
      subst hbEq
      exact ⟨.int, PartialTyJoin.self (.ty .int),
        PartialTyStrengthens.reflex⟩
    · intro mutable targets a b ha hb
      rcases PartialTyStrengthens.to_borrow_inv_nonempty ha with
        ⟨aTargets, haEq, haSub, haNonempty⟩
      rcases PartialTyStrengthens.to_borrow_inv_nonempty hb with
        ⟨bTargets, hbEq, hbSub, hbNonempty⟩
      subst haEq
      subst hbEq
      by_cases htargets : targets = []
      · subst htargets
        have haEmpty : aTargets = [] := by
          cases aTargets with
          | nil => rfl
          | cons head tail =>
              have : head ∈ ([] : List LVal) := haSub (by simp)
              cases this
        have hbEmpty : bTargets = [] := by
          cases bTargets with
          | nil => rfl
          | cons head tail =>
              have : head ∈ ([] : List LVal) := hbSub (by simp)
              cases this
        subst haEmpty
        subst hbEmpty
        exact ⟨.borrow mutable [], PartialTyJoin.self (.ty (.borrow mutable [])),
          PartialTyStrengthens.reflex⟩
      · refine ⟨.borrow mutable (aTargets ++ bTargets), ?_, ?_⟩
        · exact PartialTyUnion.borrow_append
            (haNonempty htargets) (hbNonempty htargets)
        · exact PartialTyStrengthens.borrow
            (List.append_subset_of_subset_of_subset haSub hbSub)
            (fun _ happendEmpty =>
              (haNonempty htargets) (_root_.List.eq_nil_of_append_eq_nil happendEmpty).1)
    · intro inner ih a b ha hb
      rcases PartialTyStrengthens.to_box_ty_inv ha with
        ⟨aInner, haEq, haInner⟩
      rcases PartialTyStrengthens.to_box_ty_inv hb with
        ⟨bInner, hbEq, hbInner⟩
      subst haEq
      subst hbEq
      rcases ih aInner bInner haInner hbInner with ⟨j, hj, hjUpper⟩
      refine ⟨.box j, ?_, ?_⟩
      · exact PartialTyUnion.tyBox hj
      · exact PartialTyStrengthens.tyBox hjUpper
    · intro a b ha hb
      have haEq := PartialTyStrengthens.to_bool_inv ha
      have hbEq := PartialTyStrengthens.to_bool_inv hb
      subst haEq
      subst hbEq
      exact ⟨.bool, PartialTyJoin.self (.ty .bool),
        PartialTyStrengthens.reflex⟩
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key u a b

/-- Definition 3.22 shape compatibility is symmetric. -/
theorem ShapeCompatible.symm {env : Env} {left right : PartialTy} :
    ShapeCompatible env left right →
    ShapeCompatible env right left := by
  intro h
  induction h with
  | unit => exact ShapeCompatible.unit
  | int => exact ShapeCompatible.int
  | bool => exact ShapeCompatible.bool
  | tyBox _hinner ih => exact ShapeCompatible.tyBox ih
  | box _hinner ih => exact ShapeCompatible.box ih
  | borrow hleft hright _hcompat ih => exact ShapeCompatible.borrow hright hleft ih
  | undefLeft _hinner ih => exact ShapeCompatible.undefRight ih
  | undefRight _hinner ih => exact ShapeCompatible.undefLeft ih

theorem PartialTyUnion.box_inv {left right union : PartialTy} :
    PartialTyUnion (.box left) (.box right) (.box union) →
    PartialTyUnion left right union := by
  intro hunion
  constructor
  · intro ty hty
    simp at hty
    rcases hty with hty | hty
    · subst hty
      exact PartialTyStrengthens.box_inv (PartialTyUnion.left_strengthens hunion)
    · subst hty
      exact PartialTyStrengthens.box_inv (PartialTyUnion.right_strengthens hunion)
  · intro candidate hcandidate
    have hboxedUpper :
        (.box candidate) ∈ upperBounds ({.box left, .box right} : Set PartialTy) := by
      intro ty hty
      simp at hty
      rcases hty with hty | hty
      · subst hty
        exact PartialTyStrengthens.box (hcandidate left (by simp))
      · subst hty
        exact PartialTyStrengthens.box (hcandidate right (by simp))
    exact PartialTyStrengthens.box_inv (hunion.2 hboxedUpper)

theorem PartialTyUnion.box {left right union : PartialTy} :
    PartialTyUnion left right union →
    PartialTyUnion (.box left) (.box right) (.box union) := by
  intro hunion
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.box (PartialTyUnion.left_strengthens hunion)
    · subst hcandidate
      exact PartialTyStrengthens.box (PartialTyUnion.right_strengthens hunion)
  · intro upper hupper
    have hleftUpper :
        PartialTyStrengthens (.box left) upper :=
      hupper (.box left) (by simp)
    have hrightUpper :
        PartialTyStrengthens (.box right) upper :=
      hupper (.box right) (by simp)
    cases hleftUpper with
    | reflex =>
        have hrightLeft :
            PartialTyStrengthens right left :=
          PartialTyStrengthens.box_inv hrightUpper
        have hunionLeft : PartialTyStrengthens union left := by
          exact hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact PartialTyStrengthens.reflex
            · subst hcandidate
              exact hrightLeft)
        exact PartialTyStrengthens.box hunionLeft
    | box hleftInner =>
        rename_i upperInner
        have hrightInner :
            PartialTyStrengthens right upperInner :=
          PartialTyStrengthens.box_inv hrightUpper
        have hunionUpper : PartialTyStrengthens union upperInner := by
          exact hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact hleftInner
            · subst hcandidate
              exact hrightInner)
        exact PartialTyStrengthens.box hunionUpper
    | boxIntoUndef hleftInner =>
        rename_i upperTy
        rcases PartialTyStrengthens.box_to_undef_inv hrightUpper with
          ⟨rightUpper, hupperTy, hrightInner⟩
        have hrightUpperEq : rightUpper = upperTy := by
          injection hupperTy with hinner
          exact hinner.symm
        subst hrightUpperEq
        have hunionUpper : PartialTyStrengthens union (.undef rightUpper) := by
          exact hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact hleftInner
            · subst hcandidate
              exact hrightInner)
        exact PartialTyStrengthens.boxIntoUndef hunionUpper

theorem PartialTyUnion.borrow_member {mutable : Bool}
    {leftTargets rightTargets unionTargets : List LVal} {target : LVal} :
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable unionTargets)) →
    target ∈ unionTargets →
    target ∈ leftTargets ∨ target ∈ rightTargets := by
  intro hunion hmem
  by_contra hnot
  have hnotLeft : target ∉ leftTargets := by
    intro h
    exact hnot (Or.inl h)
  have hnotRight : target ∉ rightTargets := by
    intro h
    exact hnot (Or.inr h)
  have hleftSubsetUnion : leftTargets.Subset unionTargets := by
    exact PartialTyStrengthens.borrow_subset
      (PartialTyUnion.left_strengthens hunion)
  have hrightSubsetUnion : rightTargets.Subset unionTargets := by
    exact PartialTyStrengthens.borrow_subset
      (PartialTyUnion.right_strengthens hunion)
  have hunionNonempty : unionTargets ≠ [] := by
    intro hunionEmpty
    rw [hunionEmpty] at hmem
    cases hmem
  have hleftNonempty : leftTargets ≠ [] :=
    PartialTyStrengthens.borrow_nonempty
      (PartialTyUnion.left_strengthens hunion) hunionNonempty
  have hrightNonempty : rightTargets ≠ [] :=
    PartialTyStrengthens.borrow_nonempty
      (PartialTyUnion.right_strengthens hunion) hunionNonempty
  have hleftLeFilter : PartialTyStrengthens (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable (unionTargets.filter (fun x => x ≠ target)))) := by
    refine PartialTyStrengthens.borrow ?_ (fun _ => hleftNonempty)
    intro x hx
    have hxUnion := hleftSubsetUnion hx
    have hne : x ≠ target := by
      intro heq
      subst heq
      exact hnotLeft hx
    simp [hxUnion, hne]
  have hrightLeFilter : PartialTyStrengthens (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable (unionTargets.filter (fun x => x ≠ target)))) := by
    refine PartialTyStrengthens.borrow ?_ (fun _ => hrightNonempty)
    intro x hx
    have hxUnion := hrightSubsetUnion hx
    have hne : x ≠ target := by
      intro heq
      subst heq
      exact hnotRight hx
    simp [hxUnion, hne]
  have hunionLeFilter : PartialTyStrengthens (.ty (.borrow mutable unionTargets))
      (.ty (.borrow mutable (unionTargets.filter (fun x => x ≠ target)))) := by
    exact hunion.2 (by
      intro ty hty
      simp at hty
      rcases hty with hty | hty
      · simpa [hty] using hleftLeFilter
      · simpa [hty] using hrightLeFilter)
  have hsubsetFilter :
      unionTargets.Subset (unionTargets.filter (fun x => x ≠ target)) := by
    exact PartialTyStrengthens.borrow_subset hunionLeFilter
  have hfiltered : target ∈ unionTargets.filter (fun x => x ≠ target) :=
    hsubsetFilter hmem
  simp at hfiltered

theorem PartialTyUnion.contained_borrow_member {left right union : PartialTy}
    {mutable : Bool} {targets : List LVal} {target : LVal} :
    PartialTyUnion left right union →
    PartialTyContains union (.borrow mutable targets) →
    target ∈ targets →
    (∃ leftTargets,
      PartialTyContains left (.borrow mutable leftTargets) ∧ target ∈ leftTargets) ∨
    (∃ rightTargets,
      PartialTyContains right (.borrow mutable rightTargets) ∧ target ∈ rightTargets) := by
  refine PartialTy.rec
    (motive_1 := fun unionTy =>
      ∀ left right mutable targets target,
        PartialTyUnion left right (.ty unionTy) →
        PartialTyContains (.ty unionTy) (.borrow mutable targets) →
        target ∈ targets →
        (∃ leftTargets,
          PartialTyContains left (.borrow mutable leftTargets) ∧
            target ∈ leftTargets) ∨
        (∃ rightTargets,
          PartialTyContains right (.borrow mutable rightTargets) ∧
            target ∈ rightTargets))
    (motive_2 := fun union =>
      ∀ left right mutable targets target,
        PartialTyUnion left right union →
        PartialTyContains union (.borrow mutable targets) →
        target ∈ targets →
        (∃ leftTargets,
          PartialTyContains left (.borrow mutable leftTargets) ∧
            target ∈ leftTargets) ∨
        (∃ rightTargets,
          PartialTyContains right (.borrow mutable rightTargets) ∧
            target ∈ rightTargets))
    ?unit ?int ?borrow ?boxTy ?bool ?ty ?boxPartial ?undef union
    left right mutable targets target
  · intro left right mutable targets target _hunion hcontains _htarget
    cases hcontains
  · intro left right mutable targets target _hunion hcontains _htarget
    cases hcontains
  · intro unionMutable unionTargets left right mutable targets target hunion
      hcontains htarget
    cases hcontains with
    | here =>
      rcases PartialTyStrengthens.to_borrow_right
          (PartialTyUnion.left_strengthens hunion) with
        ⟨leftTargets, rfl, _hleftSubset⟩
      rcases PartialTyStrengthens.to_borrow_right
          (PartialTyUnion.right_strengthens hunion) with
        ⟨rightTargets, rfl, _hrightSubset⟩
      rcases PartialTyUnion.borrow_member hunion htarget with hleft | hright
      · exact Or.inl ⟨leftTargets, PartialTyContains.here, hleft⟩
      · exact Or.inr ⟨rightTargets, PartialTyContains.here, hright⟩
  · intro inner ih left right mutable targets target hunion hcontains htarget
    cases hcontains with
    | tyBox hinner =>
      rcases PartialTyStrengthens.to_ty_right
          (PartialTyUnion.left_strengthens hunion) with
        ⟨leftTy, hleftEq⟩
      subst hleftEq
      rcases PartialTyStrengthens.to_box_ty_inv
          (PartialTyUnion.left_strengthens hunion) with
        ⟨leftInner, hleftInnerEq, _hleftInnerLe⟩
      subst hleftInnerEq
      rcases PartialTyStrengthens.to_ty_right
          (PartialTyUnion.right_strengthens hunion) with
        ⟨rightTy, hrightEq⟩
      subst hrightEq
      rcases PartialTyStrengthens.to_box_ty_inv
          (PartialTyUnion.right_strengthens hunion) with
        ⟨rightInner, hrightInnerEq, _hrightInnerLe⟩
      subst hrightInnerEq
      rcases ih _ _ mutable targets target
          (PartialTyUnion.tyBox_inv hunion) hinner htarget with
        hleftBorrow | hrightBorrow
      · rcases hleftBorrow with ⟨leftTargets, hcontainsLeft, hleftMem⟩
        exact Or.inl
          ⟨leftTargets, PartialTyContains.tyBox hcontainsLeft, hleftMem⟩
      · rcases hrightBorrow with ⟨rightTargets, hcontainsRight, hrightMem⟩
        exact Or.inr
          ⟨rightTargets, PartialTyContains.tyBox hcontainsRight, hrightMem⟩
  · intro left right mutable targets target _hunion hcontains _htarget
    cases hcontains
  · intro ty ih left right mutable targets target hunion hcontains htarget
    exact ih left right mutable targets target hunion hcontains htarget
  · intro inner ih left right mutable targets target hunion hcontains htarget
    cases hcontains with
    | box hinner =>
      have hleft := PartialTyUnion.left_strengthens hunion
      cases hleft with
      | reflex =>
          exact Or.inl ⟨targets, PartialTyContains.box hinner, htarget⟩
      | box hleftInner =>
          have hright := PartialTyUnion.right_strengthens hunion
          cases hright with
          | reflex =>
              exact Or.inr ⟨targets, PartialTyContains.box hinner, htarget⟩
          | box hrightInner =>
              rcases ih _ _ mutable targets target
                  (PartialTyUnion.box_inv hunion) hinner htarget with
                hleftBorrow | hrightBorrow
              · rcases hleftBorrow with ⟨leftTargets, hcontainsLeft, hleftMem⟩
                exact Or.inl
                  ⟨leftTargets, PartialTyContains.box hcontainsLeft, hleftMem⟩
              · rcases hrightBorrow with ⟨rightTargets, hcontainsRight, hrightMem⟩
                exact Or.inr
                  ⟨rightTargets, PartialTyContains.box hcontainsRight, hrightMem⟩
  · intro shape _ih left right mutable targets target _hunion hcontains _htarget
    cases hcontains

/-- A variable occurs in a partial type iff it is the base of some target of a
borrow contained (through box nesting) in that type. -/
theorem mem_partialTy_vars_iff {pt : PartialTy} {v : Name} :
    v ∈ PartialTy.vars pt ↔
    ∃ mutable targets target,
      PartialTyContains pt (.borrow mutable targets) ∧
        target ∈ targets ∧ LVal.base target = v := by
  refine PartialTy.rec
    (motive_1 := fun t =>
      v ∈ Ty.vars t ↔
      ∃ mutable targets target,
        PartialTyContains (.ty t) (.borrow mutable targets) ∧
          target ∈ targets ∧ LVal.base target = v)
    (motive_2 := fun pt =>
      v ∈ PartialTy.vars pt ↔
      ∃ mutable targets target,
        PartialTyContains pt (.borrow mutable targets) ∧
          target ∈ targets ∧ LVal.base target = v)
    ?unit ?int ?borrow ?boxTy ?bool ?ty ?boxPartial ?undef pt
  · constructor
    · intro h; simp [Ty.vars] at h
    · rintro ⟨_, _, _, hc, _, _⟩; cases hc
  · constructor
    · intro h; simp [Ty.vars] at h
    · rintro ⟨_, _, _, hc, _, _⟩; cases hc
  · intro mutable tgts
    constructor
    · intro h
      simp only [Ty.vars, List.mem_map] at h
      rcases h with ⟨tgt, htgt, hbase⟩
      exact ⟨mutable, tgts, tgt, PartialTyContains.here, htgt, hbase⟩
    · rintro ⟨m, targets, tgt, hc, htgt, hbase⟩
      cases hc
      simp only [Ty.vars, List.mem_map]
      exact ⟨tgt, htgt, hbase⟩
  · intro inner ih
    constructor
    · intro h
      simp only [Ty.vars] at h
      rcases ih.mp h with ⟨m, tgts, tgt, hc, htgt, hbase⟩
      exact ⟨m, tgts, tgt, PartialTyContains.tyBox hc, htgt, hbase⟩
    · rintro ⟨m, targets, tgt, hc, htgt, hbase⟩
      cases hc with
      | tyBox hinner =>
          simp only [Ty.vars]
          exact ih.mpr ⟨m, targets, tgt, hinner, htgt, hbase⟩
  · constructor
    · intro h; simp [Ty.vars] at h
    · rintro ⟨_, _, _, hc, _, _⟩; cases hc
  · intro t ih
    simpa [PartialTy.vars] using ih
  · intro inner ih
    constructor
    · intro h
      simp only [PartialTy.vars] at h
      rcases ih.mp h with ⟨m, tgts, tgt, hc, htgt, hbase⟩
      exact ⟨m, tgts, tgt, PartialTyContains.box hc, htgt, hbase⟩
    · rintro ⟨m, targets, tgt, hc, htgt, hbase⟩
      cases hc with
      | box hinner =>
          simp only [PartialTy.vars]
          exact ih.mpr ⟨m, targets, tgt, hinner, htgt, hbase⟩
  · intro shape _ih
    constructor
    · intro h; simp [PartialTy.vars] at h
    · rintro ⟨_, _, _, hc, _, _⟩; cases hc

/-- Every variable of a union type comes from one of the two joined types. -/
theorem partialTyUnion_vars_subset {a b u : PartialTy} {v : Name} :
    PartialTyUnion a b u →
    v ∈ PartialTy.vars u →
    v ∈ PartialTy.vars a ∨ v ∈ PartialTy.vars b := by
  intro hunion hv
  rcases mem_partialTy_vars_iff.mp hv with
    ⟨mutable, targets, target, hcontains, htarget, hbase⟩
  rcases PartialTyUnion.contained_borrow_member hunion hcontains htarget with
    ⟨leftTargets, hcl, htl⟩ |
    ⟨rightTargets, hcr, htr⟩
  · exact Or.inl
      (mem_partialTy_vars_iff.mpr
        ⟨mutable, leftTargets, target, hcl, htl, hbase⟩)
  · exact Or.inr
      (mem_partialTy_vars_iff.mpr
        ⟨mutable, rightTargets, target, hcr, htr, hbase⟩)

/--
`lw_rust_followup` Proposition 2 (rank decrease).

In a linearizable environment with rank `φ`, every variable occurring in the
type of an lval has strictly smaller rank than the lval's base variable.  This
is the well-founded measure that justifies recursion over `LValTyping` (and
hence shape-determinism of borrow-target unions).
-/
theorem lvalTyping_vars_rank_lt {env : Env} {φ : Name → Nat}
    (hφ : ∀ x slot, env.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    (∀ {lv : LVal} {pt : PartialTy} {life : Lifetime},
      LValTyping env lv pt life →
      ∀ v, v ∈ PartialTy.vars pt → φ v < φ (LVal.base lv)) ∧
    (∀ {tgts : List LVal} {pt : PartialTy} {life : Lifetime},
      LValTargetsTyping env tgts pt life →
      ∀ v, v ∈ PartialTy.vars pt → ∃ t, t ∈ tgts ∧ φ v < φ (LVal.base t)) := by
  refine ⟨fun {lv pt life} htyping => ?_, fun {tgts pt life} htyping => ?_⟩
  · exact LValTyping.rec
      (motive_1 := fun lv pt _life _ =>
        ∀ v, v ∈ PartialTy.vars pt → φ v < φ (LVal.base lv))
      (motive_2 := fun tgts pt _life _ =>
        ∀ v, v ∈ PartialTy.vars pt → ∃ t, t ∈ tgts ∧ φ v < φ (LVal.base t))
      (fun {x slot} h v hv => hφ x slot h v hv)
      (fun {lv' inner _life} _htyping ih v hv => ih v hv)
      (fun {lv' inner _life} _htyping ih v hv =>
        ih v (by simpa [PartialTy.vars, Ty.vars] using hv))
      (fun {lv'} {mutable} {targets} {borrowLife} {targetLife} {targetTy}
          _hborrow _htargets ihBorrow ihTargets v hv => by
        rcases ihTargets v hv with ⟨t, ht, hvt⟩
        exact lt_trans hvt
          (ihBorrow (LVal.base t)
            (mem_partialTy_vars_iff.mpr
              ⟨mutable, targets, t, PartialTyContains.here, ht, rfl⟩)))
      (fun {target ty _life} _htarget ihTarget v hv =>
        ⟨target, by simp, ihTarget v hv⟩)
      (fun {target rest headTy headLife restLife _life restTy unionTy}
          _hhead _hrest hunion _hintersection ihHead ihRest v hv => by
        rcases partialTyUnion_vars_subset hunion hv with hh | hr
        · exact ⟨target, by simp, ihHead v hh⟩
        · rcases ihRest v hr with ⟨t, ht, hvt⟩
          exact ⟨t, List.mem_cons_of_mem _ ht, hvt⟩)
      htyping
  · exact LValTargetsTyping.rec
      (motive_1 := fun lv pt _life _ =>
        ∀ v, v ∈ PartialTy.vars pt → φ v < φ (LVal.base lv))
      (motive_2 := fun tgts pt _life _ =>
        ∀ v, v ∈ PartialTy.vars pt → ∃ t, t ∈ tgts ∧ φ v < φ (LVal.base t))
      (fun {x slot} h v hv => hφ x slot h v hv)
      (fun {lv' inner _life} _htyping ih v hv => ih v hv)
      (fun {lv' inner _life} _htyping ih v hv =>
        ih v (by simpa [PartialTy.vars, Ty.vars] using hv))
      (fun {lv'} {mutable} {targets} {borrowLife} {targetLife} {targetTy}
          _hborrow _htargets ihBorrow ihTargets v hv => by
        rcases ihTargets v hv with ⟨t, ht, hvt⟩
        exact lt_trans hvt
          (ihBorrow (LVal.base t)
            (mem_partialTy_vars_iff.mpr
              ⟨mutable, targets, t, PartialTyContains.here, ht, rfl⟩)))
      (fun {target ty _life} _htarget ihTarget v hv =>
        ⟨target, by simp, ihTarget v hv⟩)
      (fun {target rest headTy headLife restLife _life restTy unionTy}
          _hhead _hrest hunion _hintersection ihHead ihRest v hv => by
        rcases partialTyUnion_vars_subset hunion hv with hh | hr
        · exact ⟨target, by simp, ihHead v hh⟩
        · rcases ihRest v hr with ⟨t, ht, hvt⟩
          exact ⟨t, List.mem_cons_of_mem _ ht, hvt⟩)
      htyping

@[refl] theorem Ty.sameShape_refl (t : Ty) : Ty.sameShape t t := by
  refine Ty.rec (motive_1 := fun t => Ty.sameShape t t)
    (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · trivial
  · trivial
  · intro _ _; rfl
  · intro _ ih; exact ih
  · trivial
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial

@[refl] theorem PartialTy.sameShape_refl (pt : PartialTy) :
    PartialTy.sameShape pt pt := by
  refine PartialTy.rec (motive_1 := fun t => Ty.sameShape t t)
    (motive_2 := fun pt => PartialTy.sameShape pt pt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pt
  · trivial
  · trivial
  · intro _ _; rfl
  · intro _ ih; exact ih
  · trivial
  · intro _ ih; exact ih
  · intro _ ih; exact ih
  · intro _ ih; exact ih

theorem Ty.sameShape_symm {a b : Ty} (h : Ty.sameShape a b) :
    Ty.sameShape b a := by
  have key : ∀ a b, Ty.sameShape a b → Ty.sameShape b a := by
    intro a
    refine Ty.rec (motive_1 := fun a => ∀ b, Ty.sameShape a b → Ty.sameShape b a)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b h; cases b <;> simp_all [Ty.sameShape]
    · intro b h; cases b <;> simp_all [Ty.sameShape]
    · intro _ _ b h; cases b <;> simp_all [Ty.sameShape]
    · intro _ ih b h
      cases b with
      | box t' => exact ih t' h
      | unit => simp [Ty.sameShape] at h
      | int => simp [Ty.sameShape] at h
      | borrow _ _ => simp [Ty.sameShape] at h
      | bool => simp [Ty.sameShape] at h
    · intro b h; cases b <;> simp_all [Ty.sameShape]
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
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
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
          | bool => simp [Ty.sameShape] at h2
      | unit => simp [Ty.sameShape] at h1
      | int => simp [Ty.sameShape] at h1
      | borrow _ _ => simp [Ty.sameShape] at h1
      | bool => simp [Ty.sameShape] at h1
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.sameShape]
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

/-- Forward shape preservation across an environment transformation: every slot
present in `result` comes from a `sameShape` slot of `source`.  This is the
shape-stability invariant tracked through `EnvWrite`/`UpdateAtPath`/
`WriteBorrowTargets` (the Appendix 9.6 shape fragment). -/
def EnvShapePreserved (source result : Env) : Prop :=
  ∀ x resultSlot, result.slotAt x = some resultSlot →
    ∃ sourceSlot, source.slotAt x = some sourceSlot ∧
      PartialTy.sameShape sourceSlot.ty resultSlot.ty

@[refl] theorem EnvShapePreserved.refl (env : Env) :
    EnvShapePreserved env env := by
  intro x slot hslot
  exact ⟨slot, hslot, PartialTy.sameShape_refl _⟩

theorem EnvShapePreserved.trans {first second third : Env} :
    EnvShapePreserved first second →
    EnvShapePreserved second third →
    EnvShapePreserved first third := by
  intro h12 h23 x slot hslot
  rcases h23 x slot hslot with ⟨secondSlot, hsecondSlot, hshape23⟩
  rcases h12 x secondSlot hsecondSlot with ⟨firstSlot, hfirstSlot, hshape12⟩
  exact ⟨firstSlot, hfirstSlot, PartialTy.sameShape_trans hshape12 hshape23⟩

/-- If two branch environments both preserve slot shape from a common source,
then any slot present in both branches has the same shape in both branches. -/
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
      have h : { slot with ty := newTy } = resultSlot := by
        simpa [Env.update] using hresultSlot
      exact h.symm
    subst hresultSlotEq
    exact ⟨slot, hslot, hshape⟩
  · have hmiddleSlot : middle.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresultSlot
    exact hpres y resultSlot hmiddleSlot

/-- Leaf shape-compatibility premise for a `Definition 3.23` write of `ty`
through `path` into `oldTy`.  Stated as an inductive (so the borrow fan-out case
may reference the relation at a *longer* path — through `prependPath` — without a
structural-termination obstruction).  At the leaf the old type must be shape
compatible with the written type; `box` peels one layer; `borrow` requires each
target's onward write to be leaf-compatible. -/
inductive WriteShapeCompat (env : Env) : List Unit → PartialTy → Ty → Prop where
  | leaf {oldTy : PartialTy} {ty : Ty} :
      ShapeCompatible env oldTy (.ty ty) →
      WriteShapeCompat env [] oldTy ty
  | box {path : List Unit} {inner : PartialTy} {ty : Ty} :
      WriteShapeCompat env path inner ty →
      WriteShapeCompat env (() :: path) (.box inner) ty
  | boxFull {path : List Unit} {inner : Ty} {ty : Ty} :
      WriteShapeCompat env path (.ty inner) ty →
      WriteShapeCompat env (() :: path) (.ty (.box inner)) ty
  | borrow {path : List Unit} {targets : List LVal} {ty : Ty} :
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteShapeCompat env (LVal.path (prependPath path t)) tslot.ty ty) →
      WriteShapeCompat env (() :: path) (.ty (.borrow true targets)) ty

@[refl] theorem Ty.eqv_refl (t : Ty) : Ty.eqv t t := by
  refine Ty.rec (motive_1 := fun t => Ty.eqv t t)
    (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · trivial
  · trivial
  · intro _ _; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  · intro _ ih; exact ih
  · trivial
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial

@[refl] theorem PartialTy.eqv_refl (pt : PartialTy) : PartialTy.eqv pt pt := by
  refine PartialTy.rec (motive_1 := fun t => Ty.eqv t t)
    (motive_2 := fun pt => PartialTy.eqv pt pt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pt
  · trivial
  · trivial
  · intro _ _; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  · intro _ ih; exact ih
  · trivial
  · intro _ ih; exact ih
  · intro _ ih; exact ih
  · intro _ ih; exact ih

/-- Shape compatibility of full types implies structural same-shape. -/
theorem PartialTy.sameShape_of_shapeCompatible {env : Env} {a b : Ty} :
    ShapeCompatible env (.ty a) (.ty b) → PartialTy.sameShape (.ty a) (.ty b) := by
  intro h
  have aux : ∀ {left right : PartialTy},
      ShapeCompatible env left right →
      ∀ {a b : Ty}, left = .ty a → right = .ty b →
        PartialTy.sameShape (.ty a) (.ty b) := by
    intro left right h
    induction h with
    | unit =>
        intro a b hleft hright
        cases hleft; cases hright
        simp [PartialTy.sameShape, Ty.sameShape]
    | int =>
        intro a b hleft hright
        cases hleft; cases hright
        simp [PartialTy.sameShape, Ty.sameShape]
    | bool =>
        intro a b hleft hright
        cases hleft; cases hright
        simp [PartialTy.sameShape, Ty.sameShape]
    | tyBox _hinner ih =>
        intro a b hleft hright
        cases hleft; cases hright
        simpa [PartialTy.sameShape, Ty.sameShape] using ih rfl rfl
    | box _hinner _ih =>
        intro _a _b hleft _hright
        cases hleft
    | borrow _ =>
        intro a b hleft hright
        cases hleft; cases hright
        simp [PartialTy.sameShape, Ty.sameShape]
    | undefLeft _hinner _ih =>
        intro _a _b hleft _hright
        cases hleft
    | undefRight _hinner _ih =>
        intro _a _b _hleft hright
        cases hright
  exact aux h rfl rfl

theorem ty_sameShape_of_strengthens {a b : Ty}
    (h : PartialTyStrengthens (.ty a) (.ty b)) : Ty.sameShape a b := by
  have aux : ∀ {left right : PartialTy},
      PartialTyStrengthens left right →
      ∀ {a b : Ty}, left = .ty a → right = .ty b → Ty.sameShape a b := by
    intro left right h
    induction h with
    | reflex =>
        intro a b hleft hright
        cases hleft; cases hright
        exact Ty.sameShape_refl _
    | box _hinner _ih =>
        intro _a _b hleft _hright
        cases hleft
    | tyBox _hinner ih =>
        intro a b hleft hright
        cases hleft; cases hright
        simpa [Ty.sameShape] using ih rfl rfl
    | borrow _ =>
        intro a b hleft hright
        cases hleft; cases hright
        simp [Ty.sameShape]
    | undefLeft _hinner _ih =>
        intro _a _b hleft _hright
        cases hleft
    | intoUndef _hinner _ih =>
        intro _a _b _hleft hright
        cases hright
    | boxIntoUndef _hinner _ih =>
        intro _a _b hleft _hright
        cases hleft
  exact aux h rfl rfl

/-- W-Weak preserves shape: if the old slot type is shape compatible with the
written full type, their join has the same shape as the old type.  The
`ShapeCompatible` premise is what excludes the degenerate `box`/`undef` cases (a
box can never be shape compatible with a full non-box `.ty`), and is exactly the
premise the assignment rules already carry. -/
theorem partialTyJoin_sameShape {env : Env} {old joined : PartialTy} {ty : Ty}
    (hshape : ShapeCompatible env old (.ty ty))
    (hjoin : PartialTyJoin old (.ty ty) joined) :
    PartialTy.sameShape old joined := by
  have hleft : PartialTyStrengthens old joined :=
    PartialTyUnion.left_strengthens hjoin
  cases hshape with
  | unit =>
      have hbound : joined ≤ (PartialTy.ty .unit) :=
        hjoin.2 (by intro p hp; simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff] at hp; rcases hp with rfl | rfl <;> rfl)
      cases joined with
      | ty u => have := PartialTyStrengthens.to_unit_inv hbound; subst this; trivial
      | box _ => cases hbound
      | undef _ => cases hbound
  | int =>
      have hbound : joined ≤ (PartialTy.ty .int) :=
        hjoin.2 (by intro p hp; simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff] at hp; rcases hp with rfl | rfl <;> rfl)
      cases joined with
      | ty u => have := PartialTyStrengthens.to_int_inv hbound; subst this; trivial
      | box _ => cases hbound
      | undef _ => cases hbound
  | bool =>
      have hbound : joined ≤ (PartialTy.ty .bool) :=
        hjoin.2 (by intro p hp; simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff] at hp; rcases hp with rfl | rfl <;> rfl)
      cases joined with
      | ty u => have := PartialTyStrengthens.to_bool_inv hbound; subst this; trivial
      | box _ => cases hbound
      | undef _ => cases hbound
  | tyBox hinner =>
      rcases PartialTyUnion.ty_ty_full hjoin with ⟨joinedTy, hjoinedEq⟩
      subst hjoinedEq
      rcases PartialTyStrengthens.from_box_ty_inv hleft with
        ⟨joinedInner, hjoinedTyEq, hinnerLe⟩
      subst hjoinedTyEq
      have hinnerShape : Ty.sameShape _ joinedInner :=
        ty_sameShape_of_strengthens hinnerLe
      simpa [PartialTy.sameShape, Ty.sameShape] using hinnerShape
  | borrow _hinner =>
      rcases PartialTyUnion.ty_ty_full hjoin with ⟨joinedTy, hjoinedEq⟩
      subst hjoinedEq
      exact ty_sameShape_of_strengthens hleft
  | undefLeft hinner =>
      cases hleft with
      | reflex => exact PartialTy.sameShape_refl _
      | undefLeft h => exact ty_sameShape_of_strengthens h

/-- The union of `.ty head` with a full `.ty rest` has the same shape as `head`
(the right operand must match `head`'s shape for the join to exist). -/
theorem partialTyUnion_ty_left_sameShape {head rest union : Ty} :
    PartialTyUnion (.ty head) (.ty rest) (.ty union) →
    Ty.sameShape union head := by
  intro hunion
  have hstr : PartialTyStrengthens (.ty head) (.ty union) :=
    PartialTyUnion.left_strengthens hunion
  cases head with
  | unit =>
      have : union = .unit := PartialTyStrengthens.from_unit_inv hstr
      subst this; simp [Ty.sameShape]
  | int =>
      have : union = .int := PartialTyStrengthens.from_int_inv hstr
      subst this; simp [Ty.sameShape]
  | bool =>
      have : union = .bool := PartialTyStrengthens.from_bool_inv hstr
      subst this; simp [Ty.sameShape]
  | borrow m tgts =>
      rcases PartialTyStrengthens.from_borrow_inv hstr with
        ⟨ut, hunionEq, _hsubset⟩
      subst hunionEq
      simp [Ty.sameShape]
  | box t =>
      rcases PartialTyStrengthens.from_box_ty_inv hstr with
        ⟨unionInner, hunionEq, hinnerStr⟩
      subst hunionEq
      exact Ty.sameShape_symm (by
        simpa [Ty.sameShape] using ty_sameShape_of_strengthens hinnerStr)

/-- **Unconditional left-shape preservation for a `.ty`-left join.**  When the
left operand is a *defined* type `.ty a` (not `.undef`), the join with any
`.ty rhsTy` preserves its shape — no `ShapeCompatible` premise needed.  The
`.undef`-left case is genuinely excluded: re-initialisation `.undef int ⊔ .ty int
= .ty int` changes shape, which is why `partialTyJoin_sameShape` carries the
`ShapeCompatible` hypothesis.  For positive-rank writes through *initialised*
borrow targets the leaf is always `.ty`, so this is the form the fan-out needs. -/
theorem partialTyJoin_ty_left_sameShape {a rhsTy : Ty} {joined : PartialTy} :
    PartialTyJoin (.ty a) (.ty rhsTy) joined →
    PartialTy.sameShape (.ty a) joined := by
  intro hjoin
  have ha : PartialTyStrengthens (.ty a) joined :=
    PartialTyUnion.left_strengthens hjoin
  have hr : PartialTyStrengthens (.ty rhsTy) joined := by
    have := hjoin.1 (show (.ty rhsTy : PartialTy) ∈
      ({.ty a, .ty rhsTy} : Set PartialTy) by simp)
    simpa using this
  cases joined with
  | box j => exact absurd ha (PartialTyStrengthens.not_ty_to_box)
  | ty u =>
      exact Ty.sameShape_symm (partialTyUnion_ty_left_sameShape hjoin)
  | undef u =>
      exfalso
      have hau : PartialTyStrengthens (.ty a) (.ty u) :=
        PartialTyStrengthens.ty_to_undef_inv ha
      have hru : PartialTyStrengthens (.ty rhsTy) (.ty u) :=
        PartialTyStrengthens.ty_to_undef_inv hr
      have hub : (.ty u : PartialTy) ∈
          upperBounds ({.ty a, .ty rhsTy} : Set PartialTy) := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hau
        · exact hru
      exact PartialTyStrengthens.not_undef_to_ty (hjoin.2 hub)

/-- If two `sameShape` partial types have a union, the union has that same shape.
(The `sameShape a b` premise rules out the degenerate `.ty ⊔ .undef` join that
would otherwise change the shape.) -/
theorem partialTyUnion_sameShape_of_sameShape {a b c : PartialTy}
    (hunion : PartialTyUnion a b c) (hab : PartialTy.sameShape a b) :
    PartialTy.sameShape a c := by
  have key : ∀ (a : PartialTy),
      ∀ b c, PartialTyUnion a b c → PartialTy.sameShape a b →
        PartialTy.sameShape a c := by
    intro a
    refine PartialTy.rec
      (motive_1 := fun _ => True)
      (motive_2 := fun a => ∀ b c, PartialTyUnion a b c →
        PartialTy.sameShape a b → PartialTy.sameShape a c)
      (by trivial) (by trivial) (by intro _ _; trivial) (by intro _ _; trivial)
      (by trivial) ?tyCase ?boxCase ?undefCase a
    · intro au _ b c hunion hab
      cases b with
      | ty bu =>
          rcases PartialTyUnion.ty_ty_full hunion with ⟨cu, hc⟩
          subst hc
          exact Ty.sameShape_symm (partialTyUnion_ty_left_sameShape hunion)
      | box _ => simp [PartialTy.sameShape] at hab
      | undef _ => simp [PartialTy.sameShape] at hab
    · intro ap ihBox b c hunion hab
      cases b with
      | box bp =>
          rcases PartialTyUnion.box_box_shape hunion with ⟨cp, hc⟩
          subst hc
          exact ihBox bp cp (PartialTyUnion.box_inv hunion) hab
      | ty _ => simp [PartialTy.sameShape] at hab
      | undef _ => simp [PartialTy.sameShape] at hab
    · intro au _ b c hunion hab
      cases b with
      | undef bu =>
          have hleft := PartialTyUnion.left_strengthens hunion
          cases hleft with
          | reflex => exact PartialTy.sameShape_refl _
          | undefLeft h => exact ty_sameShape_of_strengthens h
      | ty _ => simp [PartialTy.sameShape] at hab
      | box _ => simp [PartialTy.sameShape] at hab
  exact key a b c hunion hab

theorem lvalTargetsTyping_member_strengthens {env : Env}
    {targets : List LVal} {unionTy : PartialTy} {lifetime : Lifetime} :
    LValTargetsTyping env targets unionTy lifetime →
    ∀ target,
      target ∈ targets →
      ∃ ty targetLifetime,
        LValTyping env target (.ty ty) targetLifetime ∧
        PartialTyStrengthens (.ty ty) unionTy := by
  intro htargets
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun targets unionTy _ _ =>
      ∀ target,
        target ∈ targets →
        ∃ ty targetLifetime,
          LValTyping env target (.ty ty) targetLifetime ∧
          PartialTyStrengthens (.ty ty) unionTy)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htargets
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _htyping _htargets _ihTyping _ihTargets
    trivial
  · intro target ty targetLifetime htyping _ihTyping selected hmem
    simp at hmem
    subst hmem
    exact ⟨ty, targetLifetime, htyping, PartialTyStrengthens.reflex⟩
  · intro target rest headTy headLifetime _restLifetime _lifetime _restTy unionTy
      hhead _hrest hunion _hintersection _ihHead ihRest selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ⟨headTy, headLifetime, hhead, PartialTyUnion.left_strengthens hunion⟩
    · rcases ihRest selected hselected with
        ⟨ty, selectedLifetime, htyping, hstrength⟩
      exact ⟨ty, selectedLifetime, htyping,
        partialTyStrengthens_trans hstrength
          (PartialTyUnion.right_strengthens hunion)⟩

theorem lvalTargetsTyping_member_bounds {env : Env}
    {targets : List LVal} {unionTy : PartialTy} {lifetime : Lifetime} :
    LValTargetsTyping env targets unionTy lifetime →
    ∀ target,
      target ∈ targets →
      ∃ ty targetLifetime,
        LValTyping env target (.ty ty) targetLifetime ∧
        PartialTyStrengthens (.ty ty) unionTy ∧
        targetLifetime ≤ lifetime := by
  intro htargets
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun targets unionTy lifetime _ =>
      ∀ target,
        target ∈ targets →
        ∃ ty targetLifetime,
          LValTyping env target (.ty ty) targetLifetime ∧
          PartialTyStrengthens (.ty ty) unionTy ∧
          targetLifetime ≤ lifetime)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htargets
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _htyping _htargets _ihTyping _ihTargets
    trivial
  · intro target ty targetLifetime htyping _ihTarget selected hmem
    simp at hmem
    subst hmem
    exact ⟨ty, targetLifetime, htyping, PartialTyStrengthens.reflex,
      LifetimeOutlives.refl _⟩
  · intro target rest headTy headLifetime _restLifetime _lifetime _restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ⟨headTy, headLifetime, hhead,
        PartialTyUnion.left_strengthens hunion,
        LifetimeIntersection.left_le hintersection⟩
    · rcases ihRest selected hselected with
        ⟨ty, selectedLifetime, htyping, hstrength, hle⟩
      exact ⟨ty, selectedLifetime, htyping,
        partialTyStrengthens_trans hstrength
          (PartialTyUnion.right_strengthens hunion),
        LifetimeOutlives.trans hle
          (LifetimeIntersection.right_le hintersection)⟩

theorem LValTargetsTyping.transport_subset_of_members {source result : Env}
    {targets sub : List LVal} {pty : PartialTy} {lifetime : Lifetime} :
    LValTargetsTyping result targets pty lifetime →
    sub ≠ [] →
    sub ⊆ targets →
    (∀ target, target ∈ sub → ∀ resultTy resultLifetime,
      LValTyping result target (.ty resultTy) resultLifetime →
      ∃ sourceTy sourceLifetime,
        LValTyping source target (.ty sourceTy) sourceLifetime ∧
          PartialTyStrengthens (.ty sourceTy) (.ty resultTy) ∧
          sourceLifetime ≤ resultLifetime) →
    ∃ sourceTy sourceLifetime,
      LValTargetsTyping source sub (.ty sourceTy) sourceLifetime ∧
        PartialTyStrengthens (.ty sourceTy) pty ∧
        sourceLifetime ≤ lifetime := by
  intro htargets hsubNonempty hsub hmember
  rcases LValTargetsTyping.output_full htargets with ⟨upperTy, hpty⟩
  subst hpty
  induction sub with
  | nil =>
      exact False.elim (hsubNonempty rfl)
  | cons head rest ih =>
      have hheadInTargets : head ∈ targets := hsub (by simp)
      rcases lvalTargetsTyping_member_bounds htargets head hheadInTargets with
        ⟨resultHeadTy, resultHeadLifetime, hresultHead,
          hresultHeadStrength, hresultHeadLifetime⟩
      rcases hmember head (by simp) resultHeadTy resultHeadLifetime
          hresultHead with
        ⟨sourceHeadTy, sourceHeadLifetime, hsourceHead,
          hsourceHeadStrength, hsourceHeadLifetime⟩
      cases rest with
      | nil =>
          refine ⟨sourceHeadTy, sourceHeadLifetime,
            LValTargetsTyping.singleton hsourceHead, ?_, ?_⟩
          · exact partialTyStrengthens_trans hsourceHeadStrength
              hresultHeadStrength
          · exact LifetimeOutlives.trans hsourceHeadLifetime
              hresultHeadLifetime
      | cons restHead restTail =>
          have hrestNonempty : restHead :: restTail ≠ [] := by simp
          have hrestSubset : (restHead :: restTail) ⊆ targets := by
            intro target htarget
            exact hsub (List.mem_cons_of_mem head htarget)
          have hrestMember :
              ∀ target, target ∈ restHead :: restTail →
                ∀ resultTy resultLifetime,
                  LValTyping result target (.ty resultTy) resultLifetime →
                  ∃ sourceTy sourceLifetime,
                    LValTyping source target (.ty sourceTy) sourceLifetime ∧
                      PartialTyStrengthens (.ty sourceTy) (.ty resultTy) ∧
                      sourceLifetime ≤ resultLifetime := by
            intro target htarget resultTy resultLifetime htyping
            exact hmember target (List.mem_cons_of_mem head htarget)
              resultTy resultLifetime htyping
          rcases ih hrestNonempty hrestSubset hrestMember with
            ⟨restSourceTy, restSourceLifetime, hrestSource,
              hrestStrength, hrestLifetime⟩
          have hsourceHeadToUpper :
              PartialTyStrengthens (.ty sourceHeadTy) (.ty upperTy) :=
            partialTyStrengthens_trans hsourceHeadStrength hresultHeadStrength
          rcases PartialTyJoin.ty_of_common_upper hsourceHeadToUpper
              hrestStrength with
            ⟨joinedTy, hjoin, hjoinedStrength⟩
          have hsourceHeadLifetimeToUpper : sourceHeadLifetime ≤ lifetime :=
            LifetimeOutlives.trans hsourceHeadLifetime hresultHeadLifetime
          rcases LifetimeIntersection.of_common_upper
              hsourceHeadLifetimeToUpper hrestLifetime with
            ⟨joinedLifetime, hintersection, hjoinedLifetime⟩
          exact ⟨joinedTy, joinedLifetime,
            LValTargetsTyping.cons hsourceHead hrestSource hjoin hintersection,
            hjoinedStrength, hjoinedLifetime⟩

/-- A nonempty list of lvalues can be assembled into a target-list typing when
each member has a full source typing below one common type and lifetime.

This deliberately uses only the structure of the selected list.  In
particular, it neither assumes nor constructs a global ranking of lvalues;
duplicates and arbitrary ordering are handled by looking up the member witness
again at each list position. -/
theorem LValTargetsTyping.of_nonempty_members_bounded {env : Env}
    {targets : List LVal} {upperTy : Ty} {upperLifetime : Lifetime} :
    targets ≠ [] →
    (∀ target, target ∈ targets →
      ∃ sourceTy sourceLifetime,
        LValTyping env target (.ty sourceTy) sourceLifetime ∧
          PartialTyStrengthens (.ty sourceTy) (.ty upperTy) ∧
          sourceLifetime ≤ upperLifetime) →
    ∃ sourceTy sourceLifetime,
      LValTargetsTyping env targets (.ty sourceTy) sourceLifetime ∧
        PartialTyStrengthens (.ty sourceTy) (.ty upperTy) ∧
        sourceLifetime ≤ upperLifetime := by
  intro hnonempty hmember
  induction targets with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons head rest ih =>
      rcases hmember head (by simp) with
        ⟨headTy, headLifetime, hhead, hheadStrength, hheadLifetime⟩
      cases rest with
      | nil =>
          exact ⟨headTy, headLifetime, LValTargetsTyping.singleton hhead,
            hheadStrength, hheadLifetime⟩
      | cons restHead restTail =>
          have hrestNonempty : restHead :: restTail ≠ [] := by simp
          have hrestMember :
              ∀ target, target ∈ restHead :: restTail →
                ∃ sourceTy sourceLifetime,
                  LValTyping env target (.ty sourceTy) sourceLifetime ∧
                    PartialTyStrengthens (.ty sourceTy) (.ty upperTy) ∧
                    sourceLifetime ≤ upperLifetime := by
            intro target htarget
            exact hmember target (List.mem_cons_of_mem head htarget)
          rcases ih hrestNonempty hrestMember with
            ⟨restTy, restLifetime, hrest, hrestStrength, hrestLifetime⟩
          rcases PartialTyJoin.ty_of_common_upper hheadStrength hrestStrength with
            ⟨jointTy, hjoin, hjointStrength⟩
          rcases LifetimeIntersection.of_common_upper
              hheadLifetime hrestLifetime with
            ⟨jointLifetime, hintersection, hjointLifetime⟩
          exact ⟨jointTy, jointLifetime,
            LValTargetsTyping.cons hhead hrest hjoin hintersection,
            hjointStrength, hjointLifetime⟩

/-- A join is an upper bound of its left branch (`Γ₁ ⊑ Γ₁ ⊔ Γ₂`). -/
theorem EnvJoin.le_left {left right join : Env}
    (h : EnvJoin left right join) : left ≤ join :=
  h.1 (Set.mem_insert _ _)

/-- A join is an upper bound of its right branch (`Γ₂ ⊑ Γ₁ ⊔ Γ₂`). -/
theorem EnvJoin.le_right {left right join : Env}
    (h : EnvJoin left right join) : right ≤ join :=
  h.1 (Set.mem_insert_of_mem _ rfl)

/-- Slots present in both branches of a join have the same shape when legacy
same-shape-to-join evidence is available.  Current `T-If` no longer requires
this premise; this helper remains for compatibility with full-invariant
transport lemmas. -/
theorem EnvJoin.branches_sameShape {left right join : Env}
    (hjoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join) :
    ∀ x leftSlot rightSlot,
      left.slotAt x = some leftSlot →
      right.slotAt x = some rightSlot →
      PartialTy.sameShape leftSlot.ty rightSlot.ty := by
  intro x leftSlot rightSlot hleft hright
  have hle := EnvJoin.le_left hjoin x
  rw [hleft] at hle
  cases hjoinSlot : join.slotAt x with
  | none =>
      rw [hjoinSlot] at hle
      exact False.elim hle
  | some joinSlot =>
      exact PartialTy.sameShape_trans
        (hsameLeft x leftSlot joinSlot hleft hjoinSlot)
        (PartialTy.sameShape_symm
          (hsameRight x rightSlot joinSlot hright hjoinSlot))

end Paper
end FWRust
