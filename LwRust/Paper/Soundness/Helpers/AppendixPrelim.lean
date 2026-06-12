import LwRust.Paper.Soundness.Helpers.BorrowWellFormed

/-!
# Soundness helpers: AppendixPrelim

Appendix 9.1 preliminary lemmas (strengthening, type unions, etc.).
-/

namespace LwRust
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
  | borrow hsubset₁ =>
      cases hright with
      | reflex =>
          exact PartialTyStrengthens.borrow hsubset₁
      | borrow hsubset₂ =>
          exact PartialTyStrengthens.borrow
            (fun target hmem => hsubset₂ (hsubset₁ hmem))
      | intoUndef hinner =>
          cases hinner with
          | reflex =>
              exact PartialTyStrengthens.intoUndef
                (PartialTyStrengthens.borrow hsubset₁)
          | borrow hsubset₂ =>
              exact PartialTyStrengthens.intoUndef
                (PartialTyStrengthens.borrow
                  (fun target hmem => hsubset₂ (hsubset₁ hmem)))
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
  | borrow hsubset =>
      exact hsubset

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
  | borrow hsubset =>
      exact ⟨_, rfl, hsubset⟩

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
  | borrow hsubset =>
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
  | borrow hsubset =>
      exact ⟨_, rfl, hsubset⟩

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

theorem PartialTyStrengthens.not_box_to_ty {left : PartialTy} {right : Ty} :
    ¬ PartialTyStrengthens (.box left) (.ty right) := by
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

theorem PartialTyStrengthens.ty_to_ty_inv {left right : Ty} :
    PartialTyStrengthens (.ty left) (.ty right) →
    left = right ∨
      (∃ mutable leftTargets rightTargets,
        left = .borrow mutable leftTargets ∧
        right = .borrow mutable rightTargets ∧
        leftTargets.Subset rightTargets) ∨
      (∃ leftInner rightInner,
        left = .box leftInner ∧
        right = .box rightInner ∧
        PartialTyStrengthens (.ty leftInner) (.ty rightInner)) := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact Or.inl rfl
  | borrow hsubset =>
      exact Or.inr (Or.inl ⟨_, _, _, rfl, rfl, hsubset⟩)
  | tyBox hinner =>
      exact Or.inr (Or.inr ⟨_, _, rfl, rfl, hinner⟩)

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

theorem PartialTyUnion.right_full_of_ty_union {headTy resultTy : Ty}
    {restTy : PartialTy} :
    PartialTyUnion (.ty headTy) restTy (.ty resultTy) →
    ∃ restFull, restTy = .ty restFull := by
  intro hunion
  exact PartialTyStrengthens.to_ty_right
    (PartialTyUnion.right_strengthens hunion)

theorem PartialTyUnion.left_full_of_ty_union {resultTy : Ty}
    {leftTy rightTy : PartialTy} :
    PartialTyUnion leftTy rightTy (.ty resultTy) →
    ∃ leftFull, leftTy = .ty leftFull := by
  intro hunion
  exact PartialTyStrengthens.to_ty_right
    (PartialTyUnion.left_strengthens hunion)

theorem LValTargetsTyping.cons_full_inv {env : Env}
    {target : LVal} {rest : List LVal} {ty : Ty}
    {lifetime : Lifetime} :
    rest ≠ [] →
    LValTargetsTyping env (target :: rest) (.ty ty) lifetime →
    ∃ headTy headLifetime restTy restLifetime,
      LValTyping env target (.ty headTy) headLifetime ∧
        LValTargetsTyping env rest (.ty restTy) restLifetime ∧
        PartialTyUnion (.ty headTy) (.ty restTy) (.ty ty) ∧
        LifetimeIntersection headLifetime restLifetime lifetime := by
  intro hrest htyping
  cases htyping with
  | singleton _htarget =>
      simp at hrest
  | cons hhead hrestTyping hunion hintersection =>
      rcases PartialTyUnion.right_full_of_ty_union hunion with
        ⟨restTy, hrestTy⟩
      subst hrestTy
      exact ⟨_, _, restTy, _, hhead, hrestTyping, hunion, hintersection⟩

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

theorem LValTyping.deref_box_full_inv {env : Env} {source : LVal}
    {ty : Ty} {lifetime : Lifetime} :
    LValTyping env (.deref source) (.box (.ty ty)) lifetime →
    LValTyping env source (.box (.box (.ty ty))) lifetime := by
  exact LValTyping.deref_box_inv

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

theorem PartialTyUnion.not_box_borrow {left union : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    ¬ PartialTyUnion (.box left) (.ty (.borrow mutable targets)) union := by
  intro hunion
  have hleftStrength := PartialTyUnion.left_strengthens hunion
  have hrightStrength := PartialTyUnion.right_strengthens hunion
  cases hleftStrength with
  | reflex =>
      exact PartialTyStrengthens.not_ty_to_box hrightStrength
  | box hbox =>
      exact PartialTyStrengthens.not_ty_to_box hrightStrength
  | boxIntoUndef hboxUndef =>
      rename_i upperTy
      have hrightTy :
          PartialTyStrengthens (.ty (.borrow mutable targets)) (.ty (.box upperTy)) :=
        PartialTyStrengthens.ty_to_undef_inv hrightStrength
      cases hrightTy

theorem PartialTyUnion.not_borrow_box {right union : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    ¬ PartialTyUnion (.ty (.borrow mutable targets)) (.box right) union := by
  intro hunion
  exact PartialTyUnion.not_box_borrow (PartialTyUnion.symm hunion)

theorem PartialTyUnion.borrow_borrow_shape {mutable : Bool}
    {leftTargets rightTargets : List LVal} {union : PartialTy} :
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets)) union →
    ∃ unionTargets,
      union = .ty (.borrow mutable unionTargets) ∧
        leftTargets.Subset unionTargets ∧
        rightTargets.Subset unionTargets := by
  intro hunion
  rcases PartialTyUnion.ty_ty_full hunion with ⟨unionTy, hunionTy⟩
  have hleftStrength :
      PartialTyStrengthens (.ty (.borrow mutable leftTargets))
        (.ty unionTy) := by
    rw [← hunionTy]
    exact PartialTyUnion.left_strengthens hunion
  have hrightStrength :
      PartialTyStrengthens (.ty (.borrow mutable rightTargets))
        (.ty unionTy) := by
    rw [← hunionTy]
    exact PartialTyUnion.right_strengthens hunion
  cases hleftStrength with
  | reflex =>
      have hrightSubset :
          rightTargets.Subset leftTargets :=
        PartialTyStrengthens.borrow_subset hrightStrength
      exact ⟨leftTargets, hunionTy, by intro target hmem; exact hmem, hrightSubset⟩
  | borrow hleftSubset =>
      rename_i unionTargets
      have hrightSubset :
          rightTargets.Subset unionTargets :=
        PartialTyStrengthens.borrow_subset hrightStrength
      exact ⟨unionTargets, hunionTy, hleftSubset, hrightSubset⟩

theorem PartialTyUnion.borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal} :
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable (leftTargets ++ rightTargets))) := by
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        exact List.mem_append_left rightTargets htarget)
    · subst hcandidate
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        exact List.mem_append_right leftTargets htarget)
  · intro upper hupper
    have hleftUpper :
        PartialTyStrengthens (.ty (.borrow mutable leftTargets)) upper :=
      hupper (by simp)
    have hrightUpper :
        PartialTyStrengthens (.ty (.borrow mutable rightTargets)) upper :=
      hupper (by simp)
    cases hleftUpper with
    | reflex =>
        have hrightSubset :
            rightTargets.Subset leftTargets :=
          PartialTyStrengthens.borrow_subset hrightUpper
        exact PartialTyStrengthens.borrow (by
          intro target htarget
          rcases List.mem_append.mp htarget with hleft | hright
          · exact hleft
          · exact hrightSubset hright)
    | borrow hleftSubset =>
        rename_i upperTargets
        have hrightSubset :
            rightTargets.Subset upperTargets :=
          PartialTyStrengthens.borrow_subset hrightUpper
        exact PartialTyStrengthens.borrow (by
          intro target htarget
          rcases List.mem_append.mp htarget with hleft | hright
          · exact hleftSubset hleft
          · exact hrightSubset hright)
    | intoUndef hleftInner =>
        rename_i upperTy
        have hrightInner :
            PartialTyStrengthens (.ty (.borrow mutable rightTargets)) (.ty upperTy) :=
          PartialTyStrengthens.ty_to_undef_inv hrightUpper
        have happendInner :
            PartialTyStrengthens
              (.ty (.borrow mutable (leftTargets ++ rightTargets))) (.ty upperTy) := by
          cases hleftInner with
          | reflex =>
              have hrightSubset :
                  rightTargets.Subset leftTargets :=
                PartialTyStrengthens.borrow_subset hrightInner
              exact PartialTyStrengthens.borrow (by
                intro target htarget
                rcases List.mem_append.mp htarget with hleft | hright
                · exact hleft
                · exact hrightSubset hright)
          | borrow hleftSubset =>
              rename_i upperTargets
              have hrightSubset :
                  rightTargets.Subset upperTargets :=
                PartialTyStrengthens.borrow_subset hrightInner
              exact PartialTyStrengthens.borrow (by
                intro target htarget
                rcases List.mem_append.mp htarget with hleft | hright
                · exact hleftSubset hleft
                · exact hrightSubset hright)
        exact PartialTyStrengthens.intoUndef happendInner

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
      hupper (by simp)
    have hrightUpper :
        PartialTyStrengthens (.ty (.box right)) upper :=
      hupper (by simp)
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
            exact PartialTyStrengthens.tyBox (hupper (by simp))
          · subst hcandidate
            exact PartialTyStrengthens.tyBox (hupper (by simp))
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
                (PartialTyStrengthens.ty_to_undef_inv (hupper (by simp))))
          · subst hcandidate
            exact PartialTyStrengthens.intoUndef
              (PartialTyStrengthens.tyBox
                (PartialTyStrengthens.ty_to_undef_inv (hupper (by simp))))
        have hboxedUnionToUndef :
            PartialTyStrengthens (.ty (.box union)) (.ty (.box upperTy)) :=
          PartialTyStrengthens.ty_to_undef_inv (hunion.2 hboxedUpper)
        rcases PartialTyStrengthens.from_box_ty_inv hboxedUnionToUndef with
          ⟨unionUpper, hupperEq, hunionInner⟩
        cases hupperEq
        exact PartialTyStrengthens.intoUndef hunionInner
    | box upperInner =>
        have hleftUpper : PartialTyStrengthens (.ty left) (.box upperInner) :=
          hupper (show (.ty left : PartialTy) ∈
            ({.ty left, .ty right} : Set PartialTy) by simp)
        exact False.elim
          (PartialTyStrengthens.not_ty_to_box hleftUpper)

/--
Bounded join existence.  If two full types both strengthen a common full bound
`boundTy`, then their union exists and is itself bounded by `boundTy`.

This is the order-theoretic fact behind faithful borrow-target-list joins: the
union target list arising from a write-through-borrow is well typed precisely
because shape compatibility forces every joined component under one common bound
(see `LValTargetsTyping.of_members_bounded`).
-/
theorem partialTyUnion_exists_of_le_bound {leftTy rightTy boundTy : Ty} :
    PartialTyStrengthens (.ty leftTy) (.ty boundTy) →
    PartialTyStrengthens (.ty rightTy) (.ty boundTy) →
    ∃ unionTy,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty unionTy) ∧
        PartialTyStrengthens (.ty unionTy) (.ty boundTy) := by
  intro hleft hright
  have aux : ∀ boundTy : Ty, ∀ leftTy rightTy : Ty,
      PartialTyStrengthens (.ty leftTy) (.ty boundTy) →
      PartialTyStrengthens (.ty rightTy) (.ty boundTy) →
      ∃ unionTy,
        PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty unionTy) ∧
          PartialTyStrengthens (.ty unionTy) (.ty boundTy) := by
    refine Ty.rec
      (motive_1 := fun boundTy => ∀ leftTy rightTy : Ty,
        PartialTyStrengthens (.ty leftTy) (.ty boundTy) →
        PartialTyStrengthens (.ty rightTy) (.ty boundTy) →
        ∃ unionTy,
          PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty unionTy) ∧
            PartialTyStrengthens (.ty unionTy) (.ty boundTy))
      (motive_2 := fun _ => True) ?unit ?int ?borrow ?box ?bool ?ty ?partialBox ?undef
    · intro leftTy rightTy hleft hright
      have hl : leftTy = .unit := PartialTyStrengthens.to_unit_inv hleft
      have hr : rightTy = .unit := PartialTyStrengthens.to_unit_inv hright
      subst hl; subst hr
      exact ⟨.unit, PartialTyUnion.self _, PartialTyStrengthens.reflex⟩
    · intro leftTy rightTy hleft hright
      have hl : leftTy = .int := PartialTyStrengthens.to_int_inv hleft
      have hr : rightTy = .int := PartialTyStrengthens.to_int_inv hright
      subst hl; subst hr
      exact ⟨.int, PartialTyUnion.self _, PartialTyStrengthens.reflex⟩
    · intro mutable boundTargets leftTy rightTy hleft hright
      rcases PartialTyStrengthens.to_borrow_inv hleft with
        ⟨leftTargets, hleftEq, hleftSubset⟩
      rcases PartialTyStrengthens.to_borrow_inv hright with
        ⟨rightTargets, hrightEq, hrightSubset⟩
      subst hleftEq; subst hrightEq
      refine ⟨.borrow mutable (leftTargets ++ rightTargets),
        PartialTyUnion.borrow_append,
        PartialTyStrengthens.borrow ?_⟩
      intro target htarget
      rcases List.mem_append.mp htarget with hmem | hmem
      · exact hleftSubset hmem
      · exact hrightSubset hmem
    · intro inner ih leftTy rightTy hleft hright
      rcases PartialTyStrengthens.to_box_ty_inv hleft with
        ⟨leftInner, hleftEq, hleftInnerLe⟩
      rcases PartialTyStrengthens.to_box_ty_inv hright with
        ⟨rightInner, hrightEq, hrightInnerLe⟩
      subst hleftEq; subst hrightEq
      rcases ih leftInner rightInner hleftInnerLe hrightInnerLe with
        ⟨unionInner, hunionInner, hunionInnerLe⟩
      exact ⟨.box unionInner, PartialTyUnion.tyBox hunionInner,
        PartialTyStrengthens.tyBox hunionInnerLe⟩
    · intro leftTy rightTy hleft hright
      have hl : leftTy = .bool := PartialTyStrengthens.to_bool_inv hleft
      have hr : rightTy = .bool := PartialTyStrengthens.to_bool_inv hright
      subst hl; subst hr
      exact ⟨.bool, PartialTyUnion.self _, PartialTyStrengthens.reflex⟩
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact aux boundTy leftTy rightTy hleft hright

theorem PartialTyUnion.not_borrow_mismatch {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal} {union : PartialTy} :
    leftMutable ≠ rightMutable →
    ¬ PartialTyUnion (.ty (.borrow leftMutable leftTargets))
      (.ty (.borrow rightMutable rightTargets)) union := by
  intro hmutableNe hunion
  rcases PartialTyUnion.ty_ty_full hunion with ⟨unionTy, hunionTy⟩
  have hleftStrength :
      PartialTyStrengthens (.ty (.borrow leftMutable leftTargets))
        (.ty unionTy) := by
    rw [← hunionTy]
    exact PartialTyUnion.left_strengthens hunion
  have hrightStrength :
      PartialTyStrengthens (.ty (.borrow rightMutable rightTargets))
        (.ty unionTy) := by
    rw [← hunionTy]
    exact PartialTyUnion.right_strengthens hunion
  cases hleftStrength with
  | reflex =>
      cases hrightStrength with
      | reflex =>
          exact hmutableNe rfl
      | borrow _hsubset =>
          exact hmutableNe rfl
  | borrow _hsubset =>
      cases hrightStrength with
      | reflex =>
          exact hmutableNe rfl
      | borrow _hsubsetRight =>
          exact hmutableNe rfl

theorem PartialTyUnion.full_connected_union_exists
    {leftHeadTy leftRestTy rightHeadTy rightRestTy leftTy joinHeadTy joinRestTy : Ty} :
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty leftHeadTy) (.ty rightHeadTy) (.ty joinHeadTy) →
    PartialTyUnion (.ty leftRestTy) (.ty rightRestTy) (.ty joinRestTy) →
    ∃ joinTy, PartialTyUnion (.ty joinHeadTy) (.ty joinRestTy) (.ty joinTy) := by
  intro hleftUnion hheadUnion hrestUnion
  have aux : ∀ joinHeadTy : Ty,
      ∀ leftHeadTy leftRestTy rightHeadTy rightRestTy leftTy joinRestTy : Ty,
        PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
        PartialTyUnion (.ty leftHeadTy) (.ty rightHeadTy) (.ty joinHeadTy) →
        PartialTyUnion (.ty leftRestTy) (.ty rightRestTy) (.ty joinRestTy) →
        ∃ joinTy, PartialTyUnion (.ty joinHeadTy) (.ty joinRestTy) (.ty joinTy) := by
    refine Ty.rec
      (motive_1 := fun joinHeadTy =>
        ∀ leftHeadTy leftRestTy rightHeadTy rightRestTy leftTy joinRestTy : Ty,
          PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
          PartialTyUnion (.ty leftHeadTy) (.ty rightHeadTy) (.ty joinHeadTy) →
          PartialTyUnion (.ty leftRestTy) (.ty rightRestTy) (.ty joinRestTy) →
          ∃ joinTy, PartialTyUnion (.ty joinHeadTy) (.ty joinRestTy) (.ty joinTy))
      (motive_2 := fun _ => True) ?unit ?int ?borrow ?box ?bool ?ty ?partialBox ?undef
    · intro leftHeadTy leftRestTy rightHeadTy rightRestTy leftTy joinRestTy
        hleftUnion hheadUnion hrestUnion
      have hleftHeadUnit : leftHeadTy = .unit :=
        PartialTyStrengthens.to_unit_inv
          (PartialTyUnion.left_strengthens hheadUnion)
      have hrightHeadUnit : rightHeadTy = .unit :=
        PartialTyStrengthens.to_unit_inv
          (PartialTyUnion.right_strengthens hheadUnion)
      subst hleftHeadUnit
      have hleftTyUnit : leftTy = .unit :=
        PartialTyStrengthens.from_unit_inv
          (PartialTyUnion.left_strengthens hleftUnion)
      subst hleftTyUnit
      have hleftRestUnit : leftRestTy = .unit :=
        PartialTyStrengthens.to_unit_inv
          (PartialTyUnion.right_strengthens hleftUnion)
      subst hleftRestUnit
      have hjoinRestUnit : joinRestTy = .unit :=
        PartialTyStrengthens.from_unit_inv
          (PartialTyUnion.left_strengthens hrestUnion)
      subst hjoinRestUnit
      exact ⟨.unit, PartialTyUnion.self (.ty .unit)⟩
    · intro leftHeadTy leftRestTy rightHeadTy rightRestTy leftTy joinRestTy
        hleftUnion hheadUnion hrestUnion
      have hleftHeadInt : leftHeadTy = .int :=
        PartialTyStrengthens.to_int_inv
          (PartialTyUnion.left_strengthens hheadUnion)
      have hrightHeadInt : rightHeadTy = .int :=
        PartialTyStrengthens.to_int_inv
          (PartialTyUnion.right_strengthens hheadUnion)
      subst hleftHeadInt
      have hleftTyInt : leftTy = .int :=
        PartialTyStrengthens.from_int_inv
          (PartialTyUnion.left_strengthens hleftUnion)
      subst hleftTyInt
      have hleftRestInt : leftRestTy = .int :=
        PartialTyStrengthens.to_int_inv
          (PartialTyUnion.right_strengthens hleftUnion)
      subst hleftRestInt
      have hjoinRestInt : joinRestTy = .int :=
        PartialTyStrengthens.from_int_inv
          (PartialTyUnion.left_strengthens hrestUnion)
      subst hjoinRestInt
      exact ⟨.int, PartialTyUnion.self (.ty .int)⟩
    · intro mutable joinHeadTargets leftHeadTy leftRestTy rightHeadTy rightRestTy
        leftTy joinRestTy hleftUnion hheadUnion hrestUnion
      rcases PartialTyStrengthens.to_borrow_inv
          (PartialTyUnion.left_strengthens hheadUnion) with
        ⟨leftHeadTargets, hleftHeadEq, _hleftHeadSubset⟩
      rcases PartialTyStrengthens.to_borrow_inv
          (PartialTyUnion.right_strengthens hheadUnion) with
        ⟨rightHeadTargets, hrightHeadEq, _hrightHeadSubset⟩
      subst hleftHeadEq
      rcases PartialTyStrengthens.from_borrow_inv
          (PartialTyUnion.left_strengthens hleftUnion) with
        ⟨_leftHeadUpperTargets, hleftTyEq, _hleftTySubset⟩
      subst hleftTyEq
      rcases PartialTyStrengthens.to_borrow_inv
          (PartialTyUnion.right_strengthens hleftUnion) with
        ⟨leftRestTargets, hleftRestEq, _hleftRestSubset⟩
      subst hleftRestEq
      rcases PartialTyStrengthens.from_borrow_inv
          (PartialTyUnion.left_strengthens hrestUnion) with
        ⟨_leftRestUpperTargets, hjoinRestEq, _hjoinRestSubset⟩
      subst hjoinRestEq
      exact ⟨.borrow mutable (joinHeadTargets ++ _),
        PartialTyUnion.borrow_append⟩
    · intro joinHeadInner ih leftHeadTy leftRestTy rightHeadTy rightRestTy leftTy
        joinRestTy hleftUnion hheadUnion hrestUnion
      rcases PartialTyStrengthens.to_box_ty_inv
          (PartialTyUnion.left_strengthens hheadUnion) with
        ⟨leftHeadInner, hleftHeadEq, _hleftHeadLe⟩
      rcases PartialTyStrengthens.to_box_ty_inv
          (PartialTyUnion.right_strengthens hheadUnion) with
        ⟨rightHeadInner, hrightHeadEq, _hrightHeadLe⟩
      subst hleftHeadEq; subst hrightHeadEq
      rcases PartialTyStrengthens.from_box_ty_inv
          (PartialTyUnion.left_strengthens hleftUnion) with
        ⟨leftInner, hleftTyEq, _hleftHeadUpper⟩
      subst hleftTyEq
      rcases PartialTyStrengthens.to_box_ty_inv
          (PartialTyUnion.right_strengthens hleftUnion) with
        ⟨leftRestInner, hleftRestEq, _hleftRestUpper⟩
      subst hleftRestEq
      rcases PartialTyStrengthens.from_box_ty_inv
          (PartialTyUnion.left_strengthens hrestUnion) with
        ⟨joinRestInner, hjoinRestEq, _hjoinRestUpper⟩
      subst hjoinRestEq
      rcases PartialTyStrengthens.to_box_ty_inv
          (PartialTyUnion.right_strengthens hrestUnion) with
        ⟨rightRestInner, hrightRestEq, _hrightRestUpper⟩
      subst hrightRestEq
      have hleftInnerUnion :
          PartialTyUnion (.ty leftHeadInner) (.ty leftRestInner) (.ty leftInner) :=
        PartialTyUnion.tyBox_inv hleftUnion
      have hheadInnerUnion :
          PartialTyUnion (.ty leftHeadInner) (.ty rightHeadInner) (.ty joinHeadInner) :=
        PartialTyUnion.tyBox_inv hheadUnion
      have hrestInnerUnion :
          PartialTyUnion (.ty leftRestInner) (.ty rightRestInner) (.ty joinRestInner) :=
        PartialTyUnion.tyBox_inv hrestUnion
      rcases ih leftHeadInner leftRestInner rightHeadInner rightRestInner leftInner
          joinRestInner hleftInnerUnion hheadInnerUnion hrestInnerUnion with
        ⟨joinInner, hjoinInner⟩
      exact ⟨.box joinInner, PartialTyUnion.tyBox hjoinInner⟩
    · intro leftHeadTy leftRestTy rightHeadTy rightRestTy leftTy joinRestTy
        hleftUnion hheadUnion hrestUnion
      have hleftHeadBool : leftHeadTy = .bool :=
        PartialTyStrengthens.to_bool_inv
          (PartialTyUnion.left_strengthens hheadUnion)
      have hrightHeadBool : rightHeadTy = .bool :=
        PartialTyStrengthens.to_bool_inv
          (PartialTyUnion.right_strengthens hheadUnion)
      subst hleftHeadBool
      have hleftTyBool : leftTy = .bool :=
        PartialTyStrengthens.from_bool_inv
          (PartialTyUnion.left_strengthens hleftUnion)
      subst hleftTyBool
      have hleftRestBool : leftRestTy = .bool :=
        PartialTyStrengthens.to_bool_inv
          (PartialTyUnion.right_strengthens hleftUnion)
      subst hleftRestBool
      have hjoinRestBool : joinRestTy = .bool :=
        PartialTyStrengthens.from_bool_inv
          (PartialTyUnion.left_strengthens hrestUnion)
      subst hjoinRestBool
      exact ⟨.bool, PartialTyUnion.self (.ty .bool)⟩
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact aux joinHeadTy leftHeadTy leftRestTy rightHeadTy rightRestTy leftTy
    joinRestTy hleftUnion hheadUnion hrestUnion

theorem ShapeCompatible.full_partialTyUnion_exists {env : Env}
    {left right : Ty} :
    ShapeCompatible env (.ty left) (.ty right) →
    ∃ unionTy, PartialTyUnion (.ty left) (.ty right) (.ty unionTy) := by
  intro hshape
  have aux : ∀ {leftPt rightPt : PartialTy},
      ShapeCompatible env leftPt rightPt →
      ∀ {left right : Ty}, leftPt = .ty left → rightPt = .ty right →
        ∃ unionTy, PartialTyUnion (.ty left) (.ty right) (.ty unionTy) := by
    intro leftPt rightPt h
    induction h with
    | unit =>
        intro left right hleft hright
        cases hleft; cases hright
        exact ⟨.unit, PartialTyUnion.self (.ty .unit)⟩
    | int =>
        intro left right hleft hright
        cases hleft; cases hright
        exact ⟨.int, PartialTyUnion.self (.ty .int)⟩
    | bool =>
        intro left right hleft hright
        cases hleft; cases hright
        exact ⟨.bool, PartialTyUnion.self (.ty .bool)⟩
    | tyBox _hinner ih =>
        intro left right hleft hright
        cases hleft; cases hright
        rcases ih rfl rfl with ⟨unionInner, hunionInner⟩
        exact ⟨.box unionInner, PartialTyUnion.tyBox hunionInner⟩
    | box _hinner _ih =>
        intro _left _right hleft _hright
        cases hleft
    | borrow _hleft _hright _hcompatible =>
        intro left right hleft hright
        cases hleft; cases hright
        exact ⟨.borrow _ (_ ++ _), PartialTyUnion.borrow_append⟩
    | undefLeft _hinner _ih =>
        intro _left _right hleft _hright
        cases hleft
    | undefRight _hinner _ih =>
        intro _left _right _hleft hright
        cases hright
  exact aux hshape rfl rfl

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

/-- `ShapeCompatible` transports along a target-subset on the left borrow: if a
borrow `&[m]T` is shape-compatible with `b` and `T' ⊆ T`, then `&[m]T'` is too.
(S-Bor only needs every left target to share the common pointee type; a subset
still does.)  This is the bridge that specialises a *joint* borrow's
`ShapeCompatible` to each *member* borrow (member targets ⊆ union targets) — the
piece the fan-out `hbranch` shape argument needs. -/
theorem ShapeCompatible.of_subset_targets_left {env : Env} {m : Bool}
    {T T' : List LVal} {b : PartialTy}
    (h : ShapeCompatible env (.ty (.borrow m T)) b)
    (hsub : ∀ t, t ∈ T' → t ∈ T) :
    ShapeCompatible env (.ty (.borrow m T')) b := by
  cases h with
  | borrow hleft hright hsc =>
      exact ShapeCompatible.borrow (fun t ht => hleft t (hsub t ht)) hright hsc
  | undefRight hinner =>
      cases hinner with
      | borrow hleft hright hsc =>
          exact ShapeCompatible.undefRight
            (ShapeCompatible.borrow (fun t ht => hleft t (hsub t ht)) hright hsc)

theorem PartialTyUnion.undef_left_ty {left right union : Ty} :
    PartialTyUnion (.ty left) (.ty right) (.ty union) →
    PartialTyUnion (.undef left) (.ty right) (.undef union) := by
  intro hunion
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.undefLeft
        (PartialTyUnion.left_strengthens hunion)
    · subst hcandidate
      exact PartialTyStrengthens.intoUndef
        (PartialTyUnion.right_strengthens hunion)
  · intro upper hupper
    have hleftUpper :
        PartialTyStrengthens (.undef left) upper :=
      hupper (by simp)
    have hrightUpper :
        PartialTyStrengthens (.ty right) upper :=
      hupper (by simp)
    cases hleftUpper with
    | reflex =>
        have hrightLeft :
            PartialTyStrengthens (.ty right) (.ty left) :=
          PartialTyStrengthens.ty_to_undef_inv hrightUpper
        have hunionLeft : PartialTyStrengthens (.ty union) (.ty left) :=
          hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact PartialTyStrengthens.reflex
            · subst hcandidate
              exact hrightLeft)
        exact PartialTyStrengthens.undefLeft hunionLeft
    | undefLeft hleftInner =>
        rename_i upperTy
        have hrightInner :
            PartialTyStrengthens (.ty right) (.ty upperTy) :=
          PartialTyStrengthens.ty_to_undef_inv hrightUpper
        have hunionUpper : PartialTyStrengthens (.ty union) (.ty upperTy) :=
          hunion.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact hleftInner
            · subst hcandidate
              exact hrightInner)
        exact PartialTyStrengthens.undefLeft hunionUpper

theorem PartialTyUnion.ty_undef_right {left right union : Ty} :
    PartialTyUnion (.ty left) (.ty right) (.ty union) →
    PartialTyUnion (.ty left) (.undef right) (.undef union) := by
  intro hunion
  exact PartialTyUnion.symm
    (PartialTyUnion.undef_left_ty (PartialTyUnion.symm hunion))

theorem ShapeCompatible.right_full_partialTyUnion_exists {env : Env}
    {oldTy : PartialTy} {rhsTy : Ty} :
    ShapeCompatible env oldTy (.ty rhsTy) →
    ∃ unionTy, PartialTyUnion oldTy (.ty rhsTy) unionTy := by
  intro hshape
  cases hshape with
  | unit =>
      exact ⟨.ty .unit, PartialTyUnion.self (.ty .unit)⟩
  | int =>
      exact ⟨.ty .int, PartialTyUnion.self (.ty .int)⟩
  | bool =>
      exact ⟨.ty .bool, PartialTyUnion.self (.ty .bool)⟩
  | tyBox hinner =>
      rcases ShapeCompatible.full_partialTyUnion_exists hinner with
        ⟨unionInner, hunionInner⟩
      exact ⟨.ty (.box unionInner), PartialTyUnion.tyBox hunionInner⟩
  | borrow _hcompatible =>
      exact ⟨.ty (.borrow _ (_ ++ _)), PartialTyUnion.borrow_append⟩
  | undefLeft hinner =>
      rcases ShapeCompatible.full_partialTyUnion_exists hinner with
        ⟨unionTy, hunion⟩
      exact ⟨.undef unionTy, PartialTyUnion.undef_left_ty hunion⟩

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
        exact PartialTyStrengthens.box (hcandidate (by simp))
      · subst hty
        exact PartialTyStrengthens.box (hcandidate (by simp))
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
      hupper (by simp)
    have hrightUpper :
        PartialTyStrengthens (.box right) upper :=
      hupper (by simp)
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
  have hleftLeFilter : PartialTyStrengthens (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable (unionTargets.filter (fun x => x ≠ target)))) := by
    apply PartialTyStrengthens.borrow
    intro x hx
    have hxUnion := hleftSubsetUnion hx
    have hne : x ≠ target := by
      intro heq
      subst heq
      exact hnotLeft hx
    simp [hxUnion, hne]
  have hrightLeFilter : PartialTyStrengthens (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable (unionTargets.filter (fun x => x ≠ target)))) := by
    apply PartialTyStrengthens.borrow
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
    ⟨leftTargets, hcl, htl⟩ | ⟨rightTargets, hcr, htr⟩
  · exact Or.inl
      (mem_partialTy_vars_iff.mpr ⟨mutable, leftTargets, target, hcl, htl, hbase⟩)
  · exact Or.inr
      (mem_partialTy_vars_iff.mpr ⟨mutable, rightTargets, target, hcr, htr, hbase⟩)

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
      (fun {lv' mutable targets borrowLife targetLife targetTy} _hborrow _htargets
          ihBorrow ihTargets v hv => by
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
      (fun {lv' mutable targets borrowLife targetLife targetTy} _hborrow _htargets
          ihBorrow ihTargets v hv => by
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

/-- Every variable occurring in a typed lval's type has a base slot that outlives
the lval's own base slot.  (`vars pt` are exactly the bases of the borrow targets
syntactically inside `pt`; each such target outlives its containing borrow's slot,
and that chains up the spine.)  Proved by *plain* mutual structural recursion —
the type's variables are structurally smaller, so no rank induction is needed:
`var` uses the contained-borrow invariant's base-outlives directly; `box` lifts
through the inner type; `deref`-borrow chains the targets-motive (each `v` is
below some target `s`) with the borrow-motive (`s` is below `bs`); the
target-list cases recurse through the union's variable split. -/
theorem lvalTyping_vars_base_le {e : Env} (hcont : ContainedBorrowsWellFormed e) :
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping e lv pt lf →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs →
      ∀ v, v ∈ PartialTy.vars pt →
        ∀ {vbs : EnvSlot}, e.slotAt v = some vbs → vbs.lifetime ≤ bs.lifetime := by
  intro lv pt lf htyping
  refine LValTyping.rec
    (motive_1 := fun lv pt _lf _ =>
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs →
      ∀ v, v ∈ PartialTy.vars pt →
        ∀ {vbs : EnvSlot}, e.slotAt v = some vbs → vbs.lifetime ≤ bs.lifetime)
    (motive_2 := fun tgts pt _lf _ =>
      ∀ v, v ∈ PartialTy.vars pt → ∀ {vbs : EnvSlot}, e.slotAt v = some vbs →
        ∃ s, s ∈ tgts ∧ ∃ sbs, e.slotAt (LVal.base s) = some sbs ∧
          vbs.lifetime ≤ sbs.lifetime)
    ?var ?box ?borrow ?singleton ?cons htyping
  case var =>
      intro x slot hslot bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs
      have hsb : slot = bs := Option.some.inj (hslot.symm.trans hbs)
      subst hsb
      obtain ⟨m, tgts, hcontains, tgt, htgt, hbasetgt⟩ :=
        partialTy_vars_mem_contains v hv
      have hbtw := hcont x slot m tgts hslot ⟨slot, hslot, hcontains⟩
      obtain ⟨tt, tlf, _htyp, _hle, ⟨tgtbs, htgtbs, htgtbsle⟩⟩ :=
        hbtw tgt htgt
      rw [hbasetgt] at htgtbs
      have hvbseq : vbs = tgtbs := Option.some.inj (hvbs.symm.trans htgtbs)
      subst hvbseq
      exact htgtbsle
  case box =>
      intro lv0 inner lifetime _hlv0 ih bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs
      exact ih hbs v (by simpa [PartialTy.vars] using hv) hvbs
  case borrow =>
      intro lv0 mutable targets borrowLife targetLife targetTy _hbor _htgts
        ihBorrow ihTargets bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs
      obtain ⟨s, hs, sbs, hsbs, hvsbs⟩ := ihTargets v hv hvbs
      have hsbase : LVal.base s ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
        mem_partialTy_vars_iff.mpr ⟨mutable, targets, s, PartialTyContains.here, hs, rfl⟩
      exact LifetimeOutlives.trans hvsbs (ihBorrow hbs (LVal.base s) hsbase hsbs)
  case singleton =>
      intro target ty lifetime htarget _ih v hv vbs hvbs
      obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists htarget
      exact ⟨target, by simp, tbs, htbs, _ih htbs v hv hvbs⟩
  case cons =>
      intro target rest headTy headLife restLife life restTy unionTy
        hhead _hrest hunion _hintersection ihHead ihRest v hv vbs hvbs
      rcases partialTyUnion_vars_subset hunion hv with hh | hr
      · obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists hhead
        exact ⟨target, by simp, tbs, htbs, ihHead htbs v hh hvbs⟩
      · obtain ⟨s, hs, sbs, hsbs, hvsbs⟩ := ihRest v hr hvbs
        exact ⟨s, List.mem_cons_of_mem _ hs, sbs, hsbs, hvsbs⟩

/-- **Rank-bounded** form of `lvalTyping_vars_base_le`: only the contained-borrow
invariant at slots of rank `< N` is needed to bound the variables of an lval of
base-rank `< N`.  (The spine vars share the base rank; the target vars are
strictly smaller by `lvalTyping_vars_rank_lt` — so every `hcontN` query stays
below `N`.)  This is what lets the join's `ContainedBorrows` be *bootstrapped* by
strong rank induction: at rank `n` the targets (rank `< n`) are bounded using only
the rank-`<n` invariant supplied by the induction hypothesis. -/
theorem lvalTyping_vars_base_le_bounded {e : Env} {φ : Name → Nat} (N : Nat)
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcontN : ∀ x slot mutable T, φ x < N → e.slotAt x = some slot →
        e ⊢ x ↝ Ty.borrow mutable T → BorrowTargetsWellFormedInSlot e slot.lifetime T) :
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping e lv pt lf → φ (LVal.base lv) < N →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs →
      ∀ v, v ∈ PartialTy.vars pt →
        ∀ {vbs : EnvSlot}, e.slotAt v = some vbs → vbs.lifetime ≤ bs.lifetime := by
  intro lv pt lf htyping
  refine LValTyping.rec
    (motive_1 := fun lv pt _lf _ =>
      φ (LVal.base lv) < N →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs →
      ∀ v, v ∈ PartialTy.vars pt →
        ∀ {vbs : EnvSlot}, e.slotAt v = some vbs → vbs.lifetime ≤ bs.lifetime)
    (motive_2 := fun tgts pt _lf _ =>
      (∀ s, s ∈ tgts → φ (LVal.base s) < N) →
      ∀ v, v ∈ PartialTy.vars pt → ∀ {vbs : EnvSlot}, e.slotAt v = some vbs →
        ∃ s, s ∈ tgts ∧ ∃ sbs, e.slotAt (LVal.base s) = some sbs ∧
          vbs.lifetime ≤ sbs.lifetime)
    ?var ?box ?borrow ?singleton ?cons htyping
  case var =>
      intro x slot hslot hxN bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs hxN
      have hsb : slot = bs := Option.some.inj (hslot.symm.trans hbs)
      subst hsb
      obtain ⟨m, tgts, hcontains, tgt, htgt, hbasetgt⟩ :=
        partialTy_vars_mem_contains v hv
      have hbtw := hcontN x slot m tgts hxN hslot ⟨slot, hslot, hcontains⟩
      obtain ⟨tt, tlf, _htyp, _hle, ⟨tgtbs, htgtbs, htgtbsle⟩⟩ :=
        hbtw tgt htgt
      rw [hbasetgt] at htgtbs
      have hvbseq : vbs = tgtbs := Option.some.inj (hvbs.symm.trans htgtbs)
      subst hvbseq
      exact htgtbsle
  case box =>
      intro lv0 inner lifetime _hlv0 ih hxN bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs hxN
      exact ih hxN hbs v (by simpa [PartialTy.vars] using hv) hvbs
  case borrow =>
      intro lv0 mutable targets borrowLife targetLife targetTy hbor _htgts
        ihBorrow ihTargets hxN bs hbs v hv vbs hvbs
      simp only [LVal.base] at hbs hxN
      have htgtsN : ∀ s, s ∈ targets → φ (LVal.base s) < N := by
        intro s hs
        have hsbase : LVal.base s ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr ⟨mutable, targets, s, PartialTyContains.here, hs, rfl⟩
        exact lt_trans ((lvalTyping_vars_rank_lt hφ).1 hbor _ hsbase) hxN
      obtain ⟨s, hs, sbs, hsbs, hvsbs⟩ := ihTargets htgtsN v hv hvbs
      have hsbase : LVal.base s ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
        mem_partialTy_vars_iff.mpr ⟨mutable, targets, s, PartialTyContains.here, hs, rfl⟩
      exact LifetimeOutlives.trans hvsbs (ihBorrow hxN hbs (LVal.base s) hsbase hsbs)
  case singleton =>
      intro target ty lifetime htarget _ih hsN v hv vbs hvbs
      obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists htarget
      exact ⟨target, by simp, tbs, htbs, _ih (hsN target (by simp)) htbs v hv hvbs⟩
  case cons =>
      intro target rest headTy headLife restLife life restTy unionTy
        hhead _hrest hunion _hintersection ihHead ihRest hsN v hv vbs hvbs
      rcases partialTyUnion_vars_subset hunion hv with hh | hr
      · obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists hhead
        exact ⟨target, by simp, tbs, htbs,
          ihHead (hsN target (by simp)) htbs v hh hvbs⟩
      · obtain ⟨s, hs, sbs, hsbs, hvsbs⟩ :=
          ihRest (fun s' hs' => hsN s' (List.mem_cons_of_mem _ hs')) v hr hvbs
        exact ⟨s, List.mem_cons_of_mem _ hs, sbs, hsbs, hvsbs⟩

/-- **Foundation stone of the lifetime bound.**  In a linearizable
(`hφ`), contained-borrow-well-formed (`hcont`) environment, every typed lval's
lifetime is bounded by its base slot's lifetime.  Proved by strong induction on
the base rank `φ`, structural on the lval: `var` is reflexive; `box` recurses
structurally; the `deref`-of-borrow case folds the per-target bound
(`lvalTargetsTyping_le_of_members`) where each target `t` (strictly smaller rank
via `lvalTyping_vars_rank_lt`) is bounded by `t`'s base slot (rank IH) and that
slot outlives `bs` (the contained-borrow invariant's base-outlives).  The
remaining *reborrow* sub-case (the borrow lies behind a deref, not slot-contained)
is the deeper φ-recursion — isolated here. -/
theorem lvalTyping_lifetime_le_base {e : Env} {φ : Name → Nat}
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcont : ContainedBorrowsWellFormed e) :
    ∀ (lv : LVal) {pt : PartialTy} {lf : Lifetime},
      LValTyping e lv pt lf →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs → lf ≤ bs.lifetime := by
  suffices h : ∀ (n : Nat) (lv : LVal), φ (LVal.base lv) = n →
      ∀ {pt lf}, LValTyping e lv pt lf →
        ∀ {bs}, e.slotAt (LVal.base lv) = some bs → lf ≤ bs.lifetime by
    intro lv pt lf htyping bs hbs
    exact h (φ (LVal.base lv)) lv rfl htyping hbs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase pt lf hp bs hbs
        cases hp with
        | var hslot =>
            rename_i slot
            simp only [LVal.base] at hbs
            have heq : slot = bs := Option.some.inj (hslot.symm.trans hbs)
            rw [heq]
            exact LifetimeOutlives.refl _
    | deref lv' ihStruct =>
        intro hbase pt lf hp bs hbs
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        have hbs' : e.slotAt (LVal.base lv') = some bs := by simpa [LVal.base] using hbs
        cases hp with
        | box hbox => exact ihStruct hbase' hbox hbs'
        | borrow hbor htgts =>
            rename_i mutb T blf
            refine lvalTargetsTyping_le_of_members htgts (fun t ht tt tlf htyp => ?_)
            have hvar : LVal.base t ∈ PartialTy.vars (.ty (.borrow mutb T)) :=
              mem_partialTy_vars_iff.mpr ⟨mutb, T, t, PartialTyContains.here, ht, rfl⟩
            have hrankt : φ (LVal.base t) < n := by
              have hlt := (lvalTyping_vars_rank_lt hφ).1 hbor _ hvar
              simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
            obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists htyp
            -- tlf ≤ tbs.lifetime by the rank IH; tbs.lifetime ≤ bs.lifetime since
            -- `base t` occurs in `lv'`'s borrow type (uniform — no contained/reborrow split)
            exact LifetimeOutlives.trans
              (ihRank _ hrankt t rfl htyp htbs)
              (lvalTyping_vars_base_le hcont hbor hbs' (LVal.base t) hvar htbs)

/-- **Rank-bounded** form of `lvalTyping_lifetime_le_base`: only the rank-`<N`
contained-borrow invariant is needed to bound the lifetime of an lval of base
rank `<N`.  This is the tool the join `ContainedBorrows` bootstrap applies to each
fan-out target (rank `<n`) using the strong-induction hypothesis (rank-`<n`
invariant), breaking the circularity of the unbounded foundation stone (which
needs `ContainedBorrows` of the env being established). -/
theorem lvalTyping_lifetime_le_base_bounded {e : Env} {φ : Name → Nat} (N : Nat)
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcontN : ∀ x slot mutable T, φ x < N → e.slotAt x = some slot →
        e ⊢ x ↝ Ty.borrow mutable T → BorrowTargetsWellFormedInSlot e slot.lifetime T) :
    ∀ (lv : LVal), φ (LVal.base lv) < N → ∀ {pt : PartialTy} {lf : Lifetime},
      LValTyping e lv pt lf →
      ∀ {bs : EnvSlot}, e.slotAt (LVal.base lv) = some bs → lf ≤ bs.lifetime := by
  suffices h : ∀ (n : Nat) (lv : LVal),
      φ (LVal.base lv) = n → φ (LVal.base lv) < N →
      ∀ {pt lf}, LValTyping e lv pt lf →
        ∀ {bs}, e.slotAt (LVal.base lv) = some bs → lf ≤ bs.lifetime by
    intro lv hlvN pt lf htyping bs hbs
    exact h (φ (LVal.base lv)) lv rfl hlvN htyping hbs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase _hlvN pt lf hp bs hbs
        cases hp with
        | var hslot =>
            rename_i slot
            simp only [LVal.base] at hbs
            have heq : slot = bs := Option.some.inj (hslot.symm.trans hbs)
            rw [heq]; exact LifetimeOutlives.refl _
    | deref lv' ihStruct =>
        intro hbase hlvN pt lf hp bs hbs
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        have hlvN' : φ (LVal.base lv') < N := by simpa [LVal.base] using hlvN
        have hbs' : e.slotAt (LVal.base lv') = some bs := by simpa [LVal.base] using hbs
        cases hp with
        | box hbox => exact ihStruct hbase' hlvN' hbox hbs'
        | borrow hbor htgts =>
            rename_i mutb T blf
            refine lvalTargetsTyping_le_of_members htgts (fun t ht tt tlf htyp => ?_)
            have hvar : LVal.base t ∈ PartialTy.vars (.ty (.borrow mutb T)) :=
              mem_partialTy_vars_iff.mpr ⟨mutb, T, t, PartialTyContains.here, ht, rfl⟩
            have hrankt : φ (LVal.base t) < n := by
              have hlt := (lvalTyping_vars_rank_lt hφ).1 hbor _ hvar
              simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
            have hrankt' : φ (LVal.base t) < N := lt_trans hrankt (hbase' ▸ hlvN')
            obtain ⟨tbs, htbs⟩ := LValTyping.base_slot_exists htyp
            exact LifetimeOutlives.trans
              (ihRank _ hrankt t rfl hrankt' htyp htbs)
              (lvalTyping_vars_base_le_bounded N hφ hcontN hbor hlvN'
                hbs' (LVal.base t) hvar htbs)

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

theorem Ty.sameShape_of_eqv {a b : Ty} (h : Ty.eqv a b) : Ty.sameShape a b := by
  have key : ∀ a b, Ty.eqv a b → Ty.sameShape a b := by
    intro a
    refine Ty.rec (motive_1 := fun a => ∀ b, Ty.eqv a b → Ty.sameShape a b)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b h; cases b <;> simp_all [Ty.eqv, Ty.sameShape]
    · intro b h; cases b <;> simp_all [Ty.eqv, Ty.sameShape]
    · intro _ _ b h; cases b <;> simp_all [Ty.eqv, Ty.sameShape]
    · intro _ ih b h
      cases b with
      | box t' => exact ih t' h
      | unit => simp [Ty.eqv] at h
      | int => simp [Ty.eqv] at h
      | borrow _ _ => simp [Ty.eqv] at h
      | bool => simp [Ty.eqv] at h
    · intro b h; cases b <;> simp_all [Ty.eqv, Ty.sameShape]
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b h

theorem Ty.eqv_symm {a b : Ty} (h : Ty.eqv a b) : Ty.eqv b a := by
  have key : ∀ a b, Ty.eqv a b → Ty.eqv b a := by
    intro a
    refine Ty.rec (motive_1 := fun a => ∀ b, Ty.eqv a b → Ty.eqv b a)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b h; cases b <;> simp_all [Ty.eqv]
    · intro b h; cases b <;> simp_all [Ty.eqv]
    · intro ma ta b h
      cases b with
      | borrow mb tb =>
          simp only [Ty.eqv] at h ⊢
          exact ⟨h.1.symm, h.2.2, h.2.1⟩
      | unit => simp [Ty.eqv] at h
      | int => simp [Ty.eqv] at h
      | box _ => simp [Ty.eqv] at h
      | bool => simp [Ty.eqv] at h
    · intro _ ih b h
      cases b with
      | box t' => exact ih t' h
      | unit => simp [Ty.eqv] at h
      | int => simp [Ty.eqv] at h
      | borrow _ _ => simp [Ty.eqv] at h
      | bool => simp [Ty.eqv] at h
    · intro b h; cases b <;> simp_all [Ty.eqv]
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b h

theorem Ty.eqv_trans {a b c : Ty} (h₁ : Ty.eqv a b) (h₂ : Ty.eqv b c) :
    Ty.eqv a c := by
  have key : ∀ a b c, Ty.eqv a b → Ty.eqv b c → Ty.eqv a c := by
    intro a
    refine Ty.rec
      (motive_1 := fun a => ∀ b c, Ty.eqv a b → Ty.eqv b c → Ty.eqv a c)
      (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.eqv]
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.eqv]
    · intro ma ta b c h1 h2
      cases b with
      | borrow mb tb =>
          cases c with
          | borrow mc tc =>
              simp only [Ty.eqv] at h1 h2 ⊢
              exact ⟨h1.1.trans h2.1, fun x hx => h2.2.1 (h1.2.1 hx),
                fun x hx => h1.2.2 (h2.2.2 hx)⟩
          | unit => simp [Ty.eqv] at h2
          | int => simp [Ty.eqv] at h2
          | box _ => simp [Ty.eqv] at h2
          | bool => simp [Ty.eqv] at h2
      | unit => simp [Ty.eqv] at h1
      | int => simp [Ty.eqv] at h1
      | box _ => simp [Ty.eqv] at h1
      | bool => simp [Ty.eqv] at h1
    · intro _ ih b c h1 h2
      cases b with
      | box tb =>
          cases c with
          | box tc => exact ih tb tc h1 h2
          | unit => simp [Ty.eqv] at h2
          | int => simp [Ty.eqv] at h2
          | borrow _ _ => simp [Ty.eqv] at h2
          | bool => simp [Ty.eqv] at h2
      | unit => simp [Ty.eqv] at h1
      | int => simp [Ty.eqv] at h1
      | borrow _ _ => simp [Ty.eqv] at h1
      | bool => simp [Ty.eqv] at h1
    · intro b c h1 h2; cases b <;> cases c <;> simp_all [Ty.eqv]
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact key a b c h₁ h₂

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

theorem PartialTy.sameShape_of_eqv {a b : PartialTy} (h : PartialTy.eqv a b) :
    PartialTy.sameShape a b := by
  cases a <;> cases b <;>
    first
      | (simp only [PartialTy.eqv] at h; simp only [PartialTy.sameShape];
         exact Ty.sameShape_of_eqv h)
      | (simp only [PartialTy.eqv] at h; simp only [PartialTy.sameShape];
         exact PartialTy.sameShape_of_eqv h)
      | (simp [PartialTy.eqv] at h)

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
    | borrow _ _ _ =>
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

/-- The union target list of two same-`mutable` borrows is subset-equivalent to
the append of the operand target lists (`U` is the LUB, so `U ⊆ L ++ R`, while
`L, R ⊆ U` since `U` is an upper bound). -/
theorem partialTyUnion_borrow_targetsEquiv {m : Bool} {L R U : List LVal} :
    PartialTyUnion (.ty (.borrow m L)) (.ty (.borrow m R)) (.ty (.borrow m U)) →
    U ⊆ L ++ R ∧ (L ++ R) ⊆ U := by
  intro hunion
  refine ⟨?_, ?_⟩
  · have hmem : (PartialTy.ty (.borrow m (L ++ R))) ∈
        upperBounds ({PartialTy.ty (.borrow m L),
          PartialTy.ty (.borrow m R)} : Set PartialTy) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact PartialTyStrengthens.borrow (List.subset_append_left L R)
      · exact PartialTyStrengthens.borrow (List.subset_append_right L R)
    exact PartialTyStrengthens.borrow_subset (hunion.2 hmem)
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact PartialTyStrengthens.borrow_subset
        (PartialTyUnion.left_strengthens hunion) h
    · exact PartialTyStrengthens.borrow_subset
        (PartialTyUnion.right_strengthens hunion) h

/-- The union operation respects `eqv`: joining `eqv`-related heads and rests
yields `eqv`-related unions. -/
theorem partialTyUnion_eqv {headA restA tyA headB restB tyB : Ty}
    (hhead : Ty.eqv headA headB) (hrest : Ty.eqv restA restB)
    (hunionA : PartialTyUnion (.ty headA) (.ty restA) (.ty tyA))
    (hunionB : PartialTyUnion (.ty headB) (.ty restB) (.ty tyB)) :
    Ty.eqv tyA tyB := by
  have aux : ∀ headA : Ty, ∀ restA tyA headB restB tyB : Ty,
      Ty.eqv headA headB → Ty.eqv restA restB →
      PartialTyUnion (.ty headA) (.ty restA) (.ty tyA) →
      PartialTyUnion (.ty headB) (.ty restB) (.ty tyB) →
      Ty.eqv tyA tyB := by
    refine Ty.rec
      (motive_1 := fun headA => ∀ restA tyA headB restB tyB : Ty,
        Ty.eqv headA headB → Ty.eqv restA restB →
        PartialTyUnion (.ty headA) (.ty restA) (.ty tyA) →
        PartialTyUnion (.ty headB) (.ty restB) (.ty tyB) →
        Ty.eqv tyA tyB)
      (motive_2 := fun _ => True) ?unit ?int ?borrow ?box ?bool ?ty ?partialBox ?undef
    · intro restA tyA headB restB tyB hhead hrest hunionA hunionB
      have hb : headB = .unit := by cases headB <;> simp_all [Ty.eqv]
      subst hb
      have htyA : tyA = .unit :=
        PartialTyStrengthens.from_unit_inv (PartialTyUnion.left_strengthens hunionA)
      have htyB : tyB = .unit :=
        PartialTyStrengthens.from_unit_inv (PartialTyUnion.left_strengthens hunionB)
      subst htyA; subst htyB; trivial
    · intro restA tyA headB restB tyB hhead hrest hunionA hunionB
      have hb : headB = .int := by cases headB <;> simp_all [Ty.eqv]
      subst hb
      have htyA : tyA = .int :=
        PartialTyStrengthens.from_int_inv (PartialTyUnion.left_strengthens hunionA)
      have htyB : tyB = .int :=
        PartialTyStrengthens.from_int_inv (PartialTyUnion.left_strengthens hunionB)
      subst htyA; subst htyB; trivial
    · intro mA tA restA tyA headB restB tyB hhead hrest hunionA hunionB
      cases headB with
      | borrow mB tB =>
          simp only [Ty.eqv] at hhead
          obtain ⟨rfl, htAB, htBA⟩ := hhead
          rcases PartialTyStrengthens.from_borrow_inv
            (PartialTyUnion.left_strengthens hunionA) with ⟨UA, htyAeq, _⟩
          subst htyAeq
          rcases PartialTyStrengthens.to_borrow_inv
            (PartialTyUnion.right_strengthens hunionA) with ⟨rA, hrestAeq, _⟩
          subst hrestAeq
          rcases partialTyUnion_borrow_targetsEquiv hunionA with ⟨hUA_app, _⟩
          rcases PartialTyStrengthens.from_borrow_inv
            (PartialTyUnion.left_strengthens hunionB) with ⟨UB, htyBeq, _⟩
          subst htyBeq
          rcases PartialTyStrengthens.to_borrow_inv
            (PartialTyUnion.right_strengthens hunionB) with ⟨rB, hrestBeq, _⟩
          subst hrestBeq
          rcases partialTyUnion_borrow_targetsEquiv hunionB with ⟨hUB_app, happ_UB⟩
          rcases partialTyUnion_borrow_targetsEquiv hunionA with ⟨_, happ_UA⟩
          simp only [Ty.eqv] at hrest
          obtain ⟨_, hrAB, hrBA⟩ := hrest
          refine ⟨rfl, ?_, ?_⟩
          · intro x hx
            rcases List.mem_append.mp (hUA_app hx) with h | h
            · exact happ_UB (List.mem_append_left _ (htAB h))
            · exact happ_UB (List.mem_append_right _ (hrAB h))
          · intro x hx
            rcases List.mem_append.mp (hUB_app hx) with h | h
            · exact happ_UA (List.mem_append_left _ (htBA h))
            · exact happ_UA (List.mem_append_right _ (hrBA h))
      | unit => simp [Ty.eqv] at hhead
      | int => simp [Ty.eqv] at hhead
      | box _ => simp [Ty.eqv] at hhead
      | bool => simp [Ty.eqv] at hhead
    · intro hA ih restA tyA headB restB tyB hhead hrest hunionA hunionB
      cases headB with
      | box hB =>
          rcases PartialTyStrengthens.from_box_ty_inv
              (PartialTyUnion.left_strengthens hunionA) with
            ⟨tyAInner, htyAeq, _hheadAUpper⟩
          subst htyAeq
          rcases PartialTyStrengthens.to_box_ty_inv
              (PartialTyUnion.right_strengthens hunionA) with
            ⟨restAInner, hrestAeq, _hrestAUpper⟩
          subst hrestAeq
          rcases PartialTyStrengthens.from_box_ty_inv
              (PartialTyUnion.left_strengthens hunionB) with
            ⟨tyBInner, htyBeq, _hheadBUpper⟩
          subst htyBeq
          rcases PartialTyStrengthens.to_box_ty_inv
              (PartialTyUnion.right_strengthens hunionB) with
            ⟨restBInner, hrestBeq, _hrestBUpper⟩
          subst hrestBeq
          have hheadInner : Ty.eqv hA hB := by
            simpa [Ty.eqv] using hhead
          have hrestInner : Ty.eqv restAInner restBInner := by
            simpa [Ty.eqv] using hrest
          simpa [Ty.eqv] using
            ih restAInner tyAInner hB restBInner tyBInner hheadInner hrestInner
              (PartialTyUnion.tyBox_inv hunionA)
              (PartialTyUnion.tyBox_inv hunionB)
      | unit => simp [Ty.eqv] at hhead
      | int => simp [Ty.eqv] at hhead
      | borrow _ _ => simp [Ty.eqv] at hhead
      | bool => simp [Ty.eqv] at hhead
    · intro restA tyA headB restB tyB hhead hrest hunionA hunionB
      have hb : headB = .bool := by cases headB <;> simp_all [Ty.eqv]
      subst hb
      have htyA : tyA = .bool :=
        PartialTyStrengthens.from_bool_inv (PartialTyUnion.left_strengthens hunionA)
      have htyB : tyB = .bool :=
        PartialTyStrengthens.from_bool_inv (PartialTyUnion.left_strengthens hunionB)
      subst htyA; subst htyB; trivial
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact aux headA restA tyA headB restB tyB hhead hrest hunionA hunionB

/-- Strengthening within full types preserves shape: the strengthening rules
that keep a `.ty` a `.ty` (W-Reflex, W-Bor) never change the head constructor. -/
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
  | borrow hL hR hpointee =>
      rename_i mutable leftTargets rightTargets leftTy rightTy
      have hbound : joined ≤
          (PartialTy.ty (.borrow mutable (leftTargets ++ rightTargets))) :=
        hjoin.2 (by
          intro p hp
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
          rcases hp with rfl | rfl
          · exact PartialTyStrengthens.borrow (by
              intro t ht; exact List.mem_append_left _ ht)
          · exact PartialTyStrengthens.borrow (by
              intro t ht; exact List.mem_append_right _ ht))
      cases joined with
      | ty u =>
          rcases PartialTyStrengthens.to_borrow_inv hbound with ⟨st, hu, _⟩
          subst hu; rfl
      | box _ => cases hbound
      | undef _ => cases hbound
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
      rcases PartialTyStrengthens.from_borrow_inv hstr with ⟨ut, hu, _⟩
      subst hu; simp [Ty.sameShape]
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

/-- The union type of a (non-empty) target list has the shape of any one of its
members' types; combined with member determinism this fixes the union shape. -/
theorem lvalTargetsTyping_unionTy_sameShape_head {env : Env}
    {tgts : List LVal} {head : LVal} {rest : List LVal}
    {u headTy : Ty} {lu lhead : Lifetime} :
    tgts = head :: rest →
    LValTargetsTyping env tgts (.ty u) lu →
    LValTyping env head (.ty headTy) lhead →
    (∀ ma mb lma lmb,
      LValTyping env head (.ty ma) lma → LValTyping env head (.ty mb) lmb →
      Ty.sameShape ma mb) →
    Ty.sameShape u headTy := by
  intro htgts htyping hhead hdet
  cases htyping with
  | singleton hfirst =>
      -- tgts = [head], u = first's type
      simp only [List.cons.injEq] at htgts
      obtain ⟨rfl, _⟩ := htgts
      exact hdet _ _ _ _ hfirst hhead
  | cons hheadA hrestA hunionA hintA =>
      rename_i target rest' headTyA headLifeA restLifeA restTyA
      simp only [List.cons.injEq] at htgts
      obtain ⟨rfl, _⟩ := htgts
      -- u is the union of headTyA and restTyA; its shape = headTyA's = headTy's
      have huShapeHeadA : Ty.sameShape u headTyA := by
        rcases LValTargetsTyping.output_full hrestA with ⟨restTyVal, hrestFull⟩
        subst hrestFull
        exact partialTyUnion_ty_left_sameShape hunionA
      have hheadSame : Ty.sameShape headTyA headTy := hdet _ _ _ _ hheadA hhead
      exact Ty.sameShape_trans huShapeHeadA hheadSame

/-- Two target-list typings of the *same* list have same-shaped union types,
given per-member shape determinism. (The union shape is fixed by any member.) -/
theorem lvalTargetsTyping_sameList_sameShape {env : Env} {tgts : List LVal}
    {tyA tyB : Ty} {lA lB : Lifetime}
    (hdet : ∀ m, m ∈ tgts → ∀ ma mb lma lmb,
      LValTyping env m (.ty ma) lma → LValTyping env m (.ty mb) lmb →
      Ty.sameShape ma mb)
    (htA : LValTargetsTyping env tgts (.ty tyA) lA)
    (htB : LValTargetsTyping env tgts (.ty tyB) lB) :
    Ty.sameShape tyA tyB := by
  cases htA with
  | singleton hA =>
      cases htB with
      | singleton hB =>
          rename_i target
          exact hdet target (by simp) _ _ _ _ hA hB
      | cons _ hrB _ _ => cases hrB
  | cons hhA hrA huA hiA =>
      cases htB with
      | singleton _ => cases hrA
      | cons hhB hrB huB hiB =>
          rename_i target rest headTyA _ _ restTyA headTyB _ _ restTyB
          rcases LValTargetsTyping.output_full hrA with ⟨rA, hrAfull⟩
          rcases LValTargetsTyping.output_full hrB with ⟨rB, hrBfull⟩
          subst hrAfull; subst hrBfull
          have hA : Ty.sameShape tyA headTyA :=
            partialTyUnion_ty_left_sameShape huA
          have hB : Ty.sameShape tyB headTyB :=
            partialTyUnion_ty_left_sameShape huB
          have hheads : Ty.sameShape headTyA headTyB :=
            hdet target (by simp) _ _ _ _ hhA hhB
          exact Ty.sameShape_trans hA
            (Ty.sameShape_trans hheads (Ty.sameShape_symm hB))

/-- `eqv` version of `lvalTargetsTyping_sameList_sameShape`: two target-list
typings of the same list have `eqv` union types (so borrow target lists are
subset-equivalent), given per-member `eqv` determinism. -/
theorem lvalTargetsTyping_sameList_eqv {env : Env} :
    ∀ (tgts : List LVal) {tyA tyB : Ty} {lA lB : Lifetime},
    (∀ m, m ∈ tgts → ∀ ma mb lma lmb,
      LValTyping env m (.ty ma) lma → LValTyping env m (.ty mb) lmb →
      Ty.eqv ma mb) →
    LValTargetsTyping env tgts (.ty tyA) lA →
    LValTargetsTyping env tgts (.ty tyB) lB →
    Ty.eqv tyA tyB := by
  intro tgts
  induction tgts with
  | nil => intro tyA tyB lA lB _ htA _; cases htA
  | cons head tail ih =>
      intro tyA tyB lA lB hdet htA htB
      cases htA with
      | singleton hA =>
          cases htB with
          | singleton hB => exact hdet head (by simp) _ _ _ _ hA hB
          | cons _ hrB _ _ => cases hrB
      | cons hhA hrA huA hiA =>
          cases htB with
          | singleton _ => cases hrA
          | cons hhB hrB huB hiB =>
              rcases LValTargetsTyping.output_full hrA with ⟨rTyA, hrAfull⟩
              rcases LValTargetsTyping.output_full hrB with ⟨rTyB, hrBfull⟩
              subst hrAfull; subst hrBfull
              have hheadEqv := hdet head (by simp) _ _ _ _ hhA hhB
              have hrestEqv :=
                ih (fun m hm => hdet m (List.mem_cons_of_mem head hm)) hrA hrB
              exact partialTyUnion_eqv hheadEqv hrestEqv huA huB

/--
Target-list typing records a finite union of the target types.  Any selected
target therefore has a full type that strengthens the union type.
-/
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
    ?var ?box ?borrow ?singleton ?cons htargets
  · intro _x _slot _hslot
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

theorem lvalTargetsTyping_ty_le_of_members {env : Env}
    {targets : List LVal} {unionTy boundTy : Ty} {lifetime : Lifetime} :
    LValTargetsTyping env targets (.ty unionTy) lifetime →
    (∀ target, target ∈ targets → ∀ memberTy memberLifetime,
      LValTyping env target (.ty memberTy) memberLifetime →
      PartialTyStrengthens (.ty memberTy) (.ty boundTy)) →
    PartialTyStrengthens (.ty unionTy) (.ty boundTy) := by
  intro htargets hmem
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun targets partialTy _ _ =>
      ∀ {unionTy : Ty}, partialTy = .ty unionTy →
        (∀ target, target ∈ targets → ∀ memberTy memberLifetime,
          LValTyping env target (.ty memberTy) memberLifetime →
          PartialTyStrengthens (.ty memberTy) (.ty boundTy)) →
        PartialTyStrengthens (.ty unionTy) (.ty boundTy))
    ?var ?box ?borrow ?singleton ?cons htargets rfl hmem
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _htyping _htargets _ihTyping _ihTargets
    trivial
  · intro target ty targetLifetime htyping _ihTyping unionTy hfull hmem
    cases hfull
    exact hmem target (by simp) ty targetLifetime htyping
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead hrest hunion _hintersection _ihHead ihRest selectedTy hfull hmem
    cases hfull
    rcases PartialTyUnion.right_full_of_ty_union hunion with
      ⟨restFull, hrestFull⟩
    subst hrestFull
    have hheadLe : PartialTyStrengthens (.ty headTy) (.ty boundTy) :=
      hmem target (by simp) headTy headLifetime hhead
    have hrestLe : PartialTyStrengthens (.ty restFull) (.ty boundTy) :=
      ihRest rfl (fun member hmember memberTy memberLifetime htyping =>
        hmem member (List.mem_cons_of_mem target hmember)
          memberTy memberLifetime htyping)
    exact hunion.2 (by
      intro candidate hcandidate
      simp at hcandidate
      rcases hcandidate with hcandidate | hcandidate
      · subst hcandidate
        exact hheadLe
      · subst hcandidate
        exact hrestLe)

theorem partialTyStrengthens_ty_of_eqv {left right : Ty} :
    Ty.eqv left right →
    PartialTyStrengthens (.ty left) (.ty right) := by
  intro heqv
  have aux : ∀ left : Ty, ∀ right : Ty, Ty.eqv left right →
      PartialTyStrengthens (.ty left) (.ty right) := by
    refine Ty.rec
      (motive_1 := fun left => ∀ right : Ty, Ty.eqv left right →
        PartialTyStrengthens (.ty left) (.ty right))
      (motive_2 := fun _ => True) ?unit ?int ?borrow ?box ?bool ?ty ?partialBox ?undef
    · intro right heqv
      cases right <;> simp_all [Ty.eqv]
    · intro right heqv
      cases right <;> simp_all [Ty.eqv]
    · intro mutable leftTargets right heqv
      cases right with
      | borrow rightMutable rightTargets =>
          simp only [Ty.eqv] at heqv
          obtain ⟨rfl, hsubset, _⟩ := heqv
          exact PartialTyStrengthens.borrow hsubset
      | unit => simp [Ty.eqv] at heqv
      | int => simp [Ty.eqv] at heqv
      | box _ => simp [Ty.eqv] at heqv
      | bool => simp [Ty.eqv] at heqv
    · intro leftInner ih right heqv
      cases right with
      | box rightInner =>
          exact PartialTyStrengthens.tyBox (ih rightInner (by simpa [Ty.eqv] using heqv))
      | unit => simp [Ty.eqv] at heqv
      | int => simp [Ty.eqv] at heqv
      | borrow _ _ => simp [Ty.eqv] at heqv
      | bool => simp [Ty.eqv] at heqv
    · intro right heqv
      cases right <;> simp_all [Ty.eqv]
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact aux left right heqv

theorem partialTyStrengthens_of_eqv :
    {left right : PartialTy} → PartialTy.eqv left right → PartialTyStrengthens left right
  | .ty _, .ty _, heqv => partialTyStrengthens_ty_of_eqv heqv
  | .box left, .box right, heqv =>
      PartialTyStrengthens.box (partialTyStrengthens_of_eqv (left := left) (right := right) heqv)
  | .undef _, .undef _, heqv =>
      PartialTyStrengthens.undefLeft (partialTyStrengthens_ty_of_eqv heqv)
  | .ty _, .box _, heqv => by simp [PartialTy.eqv] at heqv
  | .ty _, .undef _, heqv => by simp [PartialTy.eqv] at heqv
  | .box _, .ty _, heqv => by simp [PartialTy.eqv] at heqv
  | .box _, .undef _, heqv => by simp [PartialTy.eqv] at heqv
  | .undef _, .ty _, heqv => by simp [PartialTy.eqv] at heqv
  | .undef _, .box _, heqv => by simp [PartialTy.eqv] at heqv

theorem partialTyStrengthens_eqv_right {c a b : PartialTy}
    (hca : PartialTyStrengthens c a) (hab : PartialTy.eqv a b) :
    PartialTyStrengthens c b :=
  partialTyStrengthens_trans hca (partialTyStrengthens_of_eqv hab)

theorem Ty.eqv_of_strengthens_both {left right : Ty} :
    PartialTyStrengthens (.ty left) (.ty right) →
    PartialTyStrengthens (.ty right) (.ty left) →
    Ty.eqv left right := by
  intro hlr hrl
  have aux : ∀ left : Ty, ∀ right : Ty,
      PartialTyStrengthens (.ty left) (.ty right) →
      PartialTyStrengthens (.ty right) (.ty left) →
      Ty.eqv left right := by
    refine Ty.rec
      (motive_1 := fun left => ∀ right : Ty,
        PartialTyStrengthens (.ty left) (.ty right) →
        PartialTyStrengthens (.ty right) (.ty left) →
        Ty.eqv left right)
      (motive_2 := fun _ => True) ?unit ?int ?borrow ?box ?bool ?ty ?partialBox ?undef
    · intro right hlr _hrl
      have hright : right = .unit := PartialTyStrengthens.from_unit_inv hlr
      subst hright
      trivial
    · intro right hlr _hrl
      have hright : right = .int := PartialTyStrengthens.from_int_inv hlr
      subst hright
      trivial
    · intro mutable leftTargets right hlr hrl
      rcases PartialTyStrengthens.from_borrow_inv hlr with
        ⟨rightTargets, hrightEq, hleftSubset⟩
      subst hrightEq
      have hrightSubset : rightTargets.Subset leftTargets :=
        PartialTyStrengthens.borrow_subset hrl
      exact ⟨rfl, hleftSubset, hrightSubset⟩
    · intro leftInner ih right hlr hrl
      rcases PartialTyStrengthens.from_box_ty_inv hlr with
        ⟨rightInner, hrightEq, hinnerLr⟩
      subst hrightEq
      rcases PartialTyStrengthens.from_box_ty_inv hrl with
        ⟨leftInner', hleftEq, hinnerRl⟩
      cases hleftEq
      exact ih rightInner hinnerLr hinnerRl
    · intro right hlr _hrl
      have hright : right = .bool := PartialTyStrengthens.from_bool_inv hlr
      subst hright
      trivial
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
  exact aux left right hlr hrl

/-- A target of the union borrow comes from some member's borrow targets. -/
theorem lvalTargetsTyping_borrowTargets_mem {env : Env} :
    ∀ {tgts : List LVal} {m : Bool} {U : List LVal} {lu : Lifetime},
    LValTargetsTyping env tgts (.ty (.borrow m U)) lu →
    ∀ x, x ∈ U →
      ∃ t, t ∈ tgts ∧ ∃ tt lt,
        LValTyping env t (.ty (.borrow m tt)) lt ∧ x ∈ tt := by
  intro tgts
  induction tgts with
  | nil => intro m U lu ht; cases ht
  | cons head tail ih =>
      intro m U lu ht x hx
      cases ht with
      | singleton hfirst =>
          exact ⟨head, by simp, U, _, hfirst, hx⟩
      | cons hhA hrA huA hiA =>
          rcases LValTargetsTyping.output_full hrA with ⟨rTy, hrFull⟩
          subst hrFull
          rcases PartialTyStrengthens.to_borrow_inv
            (PartialTyUnion.left_strengthens huA) with ⟨headTgts, hheadEq, _⟩
          subst hheadEq
          rcases PartialTyStrengthens.to_borrow_inv
            (PartialTyUnion.right_strengthens huA) with ⟨restTgts, hrestEq, _⟩
          subst hrestEq
          rcases partialTyUnion_borrow_targetsEquiv huA with ⟨hU_app, _⟩
          rcases List.mem_append.mp (hU_app hx) with h | h
          · exact ⟨head, by simp, headTgts, _, hhA, h⟩
          · rcases ih hrA x h with ⟨t, ht, tt, lt, htty, hxtt⟩
            exact ⟨t, List.mem_cons_of_mem head ht, tt, lt, htty, hxtt⟩

/-- Two target-list typings of subset-equivalent lists have `eqv` union types.
Generalises `lvalTargetsTyping_sameList_eqv` to lists with the same member set,
which is what relates reborrow chains (whose target lists are subset-equivalent
LUB witnesses). -/
theorem lvalTargetsTyping_subsetEquiv_eqv {env : Env}
    {tgtsA tgtsB : List LVal} {tyA tyB : Ty} {lA lB : Lifetime}
    (hAB : tgtsA ⊆ tgtsB) (hBA : tgtsB ⊆ tgtsA)
    (hdet : ∀ m, m ∈ tgtsA ++ tgtsB → ∀ ma mb lma lmb,
      LValTyping env m (.ty ma) lma → LValTyping env m (.ty mb) lmb → Ty.eqv ma mb)
    (htA : LValTargetsTyping env tgtsA (.ty tyA) lA)
    (htB : LValTargetsTyping env tgtsB (.ty tyB) lB) :
    Ty.eqv tyA tyB := by
  have hABStrength : PartialTyStrengthens (.ty tyA) (.ty tyB) :=
    lvalTargetsTyping_ty_le_of_members htA
      (fun target htarget memberTy memberLifetime htyping =>
        let ⟨otherTy, otherLifetime, hotherTyping, hotherLe⟩ :=
          lvalTargetsTyping_member_strengthens htB target (hAB htarget)
        have heqv : Ty.eqv memberTy otherTy :=
          hdet target (List.mem_append_left _ htarget)
            memberTy otherTy memberLifetime otherLifetime htyping hotherTyping
        partialTyStrengthens_trans (partialTyStrengthens_ty_of_eqv heqv) hotherLe)
  have hBAStrength : PartialTyStrengthens (.ty tyB) (.ty tyA) :=
    lvalTargetsTyping_ty_le_of_members htB
      (fun target htarget memberTy memberLifetime htyping =>
        let ⟨otherTy, otherLifetime, hotherTyping, hotherLe⟩ :=
          lvalTargetsTyping_member_strengthens htA target (hBA htarget)
        have heqv : Ty.eqv memberTy otherTy :=
          hdet target (List.mem_append_right _ htarget)
            memberTy otherTy memberLifetime otherLifetime htyping hotherTyping
        partialTyStrengthens_trans (partialTyStrengthens_ty_of_eqv heqv) hotherLe)
  exact Ty.eqv_of_strengthens_both hABStrength hBAStrength

/-- Two environments whose common slots carry `eqv` types.  This is the relation
preserved by the write-fan-out join (both sides are one environment modified by
writing the same right-hand type), and it is what lets two branch typings of the
same lval be related across environments. -/
def EnvEqvCompat (e1 e2 : Env) : Prop :=
  ∀ x slotA slotB, e1.slotAt x = some slotA → e2.slotAt x = some slotB →
    PartialTy.eqv slotA.ty slotB.ty

/-- Cross-environment version of `lvalTargetsTyping_subsetEquiv_eqv`: the two
target-list typings live in possibly-different environments `e1`, `e2`, related
only through the cross-environment member determinism `hdet`.  The proof is
identical to the single-environment version (every member fact is taken in its
own environment; the two sides are linked only via `hdet`). -/
theorem lvalTargetsTyping_subsetEquiv_eqv_cross {e1 e2 : Env}
    {tgtsA tgtsB : List LVal} {tyA tyB : Ty} {lA lB : Lifetime}
    (hAB : tgtsA ⊆ tgtsB) (hBA : tgtsB ⊆ tgtsA)
    (hdet : ∀ m, m ∈ tgtsA ++ tgtsB → ∀ ma mb lma lmb,
      LValTyping e1 m (.ty ma) lma → LValTyping e2 m (.ty mb) lmb → Ty.eqv ma mb)
    (htA : LValTargetsTyping e1 tgtsA (.ty tyA) lA)
    (htB : LValTargetsTyping e2 tgtsB (.ty tyB) lB) :
    Ty.eqv tyA tyB := by
  have hABStrength : PartialTyStrengthens (.ty tyA) (.ty tyB) :=
    lvalTargetsTyping_ty_le_of_members htA
      (fun target htarget memberTy memberLifetime htyping =>
        let ⟨otherTy, otherLifetime, hotherTyping, hotherLe⟩ :=
          lvalTargetsTyping_member_strengthens htB target (hAB htarget)
        have heqv : Ty.eqv memberTy otherTy :=
          hdet target (List.mem_append_left _ htarget)
            memberTy otherTy memberLifetime otherLifetime htyping hotherTyping
        partialTyStrengthens_trans (partialTyStrengthens_ty_of_eqv heqv) hotherLe)
  have hBAStrength : PartialTyStrengthens (.ty tyB) (.ty tyA) :=
    lvalTargetsTyping_ty_le_of_members htB
      (fun target htarget memberTy memberLifetime htyping =>
        let ⟨otherTy, otherLifetime, hotherTyping, hotherLe⟩ :=
          lvalTargetsTyping_member_strengthens htA target (hBA htarget)
        have heqv : Ty.eqv memberTy otherTy :=
          Ty.eqv_symm (hdet target (List.mem_append_right _ htarget)
            otherTy memberTy otherLifetime memberLifetime hotherTyping htyping)
        partialTyStrengthens_trans (partialTyStrengthens_ty_of_eqv heqv) hotherLe)
  exact Ty.eqv_of_strengthens_both hABStrength hBAStrength

/-- Single-lval type determinism (`eqv` form): in a linearizable environment,
any two typings of the same lval have `eqv` types (same shape, and borrow target
lists subset-equivalent).  Proved by strong induction on the rank of the lval's
base variable, with an inner structural induction on the lval (the dereference
recursion stays at the same rank, while borrow-target recursion strictly lowers
the rank via `lvalTyping_vars_rank_lt`). -/
theorem lvalTyping_eqv {env : Env} {φ : Name → Nat}
    (hφ : ∀ x slot, env.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    ∀ (lv : LVal) {a b : PartialTy} {la lb : Lifetime},
      LValTyping env lv a la → LValTyping env lv b lb → PartialTy.eqv a b := by
  suffices h : ∀ (n : Nat) (lv : LVal), φ (LVal.base lv) = n →
      ∀ {a b : PartialTy} {la lb : Lifetime},
        LValTyping env lv a la → LValTyping env lv b lb → PartialTy.eqv a b by
    intro lv a b la lb ha hb
    exact h (φ (LVal.base lv)) lv rfl ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase a b la lb ha hb
        cases ha with
        | var hslot =>
            cases hb with
            | var hslot' =>
                have heq := Option.some.inj (hslot.symm.trans hslot')
                rw [heq]
    | deref lv' ihStruct =>
        intro hbase a b la lb ha hb
        have hbase' : φ (LVal.base lv') = n := by
          simpa [LVal.base] using hbase
        cases ha with
        | box hboxA =>
            cases hb with
            | box hboxB =>
                have hbox := ihStruct hbase' hboxA hboxB
                exact hbox
            | borrow hborB htB =>
                have hbad := ihStruct hbase' hboxA hborB
                simp [PartialTy.eqv] at hbad
        | borrow hborA htA =>
            cases hb with
            | box hboxB =>
                have hbad := ihStruct hbase' hborA hboxB
                simp [PartialTy.eqv] at hbad
            | borrow hborB htB =>
                rename_i mutA tgtsA borrowLifeA mutB tgtsB borrowLifeB
                -- member determinism: borrow targets have strictly smaller rank.
                have hmemDet : ∀ (tgts : List LVal),
                    (∀ t : LVal, t ∈ tgts → φ (LVal.base t) < n) →
                    ∀ m : LVal, m ∈ tgts → ∀ ma mb lma lmb,
                      LValTyping env m (.ty ma) lma →
                      LValTyping env m (.ty mb) lmb → Ty.eqv ma mb := by
                  intro tgts hlow m hm ma mb lma lmb hma hmb
                  have := ihRank (φ (LVal.base m)) (hlow m hm) m rfl hma hmb
                  simpa [PartialTy.eqv] using this
                -- both borrow lvals have lower-rank targets (rank lemma)
                have hlowA : ∀ t : LVal, t ∈ tgtsA → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutA tgtsA)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hborA _ hvar
                  have hxn : φ (LVal.base lv') = n := hbase'
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hxn
                have hlowB : ∀ t : LVal, t ∈ tgtsB → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutB tgtsB)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hborB _ hvar
                  have hxn : φ (LVal.base lv') = n := hbase'
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hxn
                -- lv' is the same lval in both, so its borrow types are eqv:
                -- mutA = mutB and tgtsA, tgtsB are subset-equivalent.
                have hlvEqv : PartialTy.eqv (.ty (.borrow mutA tgtsA))
                    (.ty (.borrow mutB tgtsB)) :=
                  ihStruct hbase' hborA hborB
                simp only [PartialTy.eqv, Ty.eqv] at hlvEqv
                obtain ⟨rfl, htAB, htBA⟩ := hlvEqv
                rcases LValTargetsTyping.output_full htA with ⟨aTy, haFull⟩
                rcases LValTargetsTyping.output_full htB with ⟨bTy, hbFull⟩
                subst haFull; subst hbFull
                -- relate the two unions over subset-equivalent target lists
                have heqv : Ty.eqv aTy bTy :=
                  lvalTargetsTyping_subsetEquiv_eqv htAB htBA
                    (hmemDet (tgtsA ++ tgtsB) (by
                      intro t ht
                      rcases List.mem_append.mp ht with h | h
                      · exact hlowA t h
                      · exact hlowB t h))
                    htA htB
                simpa [PartialTy.eqv] using heqv
    -- end deref

/-- Cross-environment single-lval determinism: two typings of the same lval in
`eqv`-compatible environments have `eqv` types.  This is the keystone for joining
deref-of-borrow typings across the write-fan-out join — it is the cross-env
mirror of `lvalTyping_eqv`, with the same φ-rank/structural induction and the
cross-env `lvalTargetsTyping_subsetEquiv_eqv_cross` in the reborrow case. -/
theorem lvalTyping_eqv_cross {e1 e2 : Env} {φ : Name → Nat}
    (hcompat : EnvEqvCompat e1 e2)
    (hφ1 : ∀ x slot, e1.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hφ2 : ∀ x slot, e2.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    ∀ (lv : LVal) {a b : PartialTy} {la lb : Lifetime},
      LValTyping e1 lv a la → LValTyping e2 lv b lb → PartialTy.eqv a b := by
  suffices h : ∀ (n : Nat) (lv : LVal), φ (LVal.base lv) = n →
      ∀ {a b : PartialTy} {la lb : Lifetime},
        LValTyping e1 lv a la → LValTyping e2 lv b lb → PartialTy.eqv a b by
    intro lv a b la lb ha hb
    exact h (φ (LVal.base lv)) lv rfl ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase a b la lb ha hb
        cases ha with
        | var hslotA =>
            cases hb with
            | var hslotB => exact hcompat x _ _ hslotA hslotB
    | deref lv' ihStruct =>
        intro hbase a b la lb ha hb
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        cases ha with
        | box hboxA =>
            cases hb with
            | box hboxB =>
                have hbox := ihStruct hbase' hboxA hboxB
                exact hbox
            | borrow hborB htB =>
                have hbad := ihStruct hbase' hboxA hborB
                simp [PartialTy.eqv] at hbad
        | borrow hborA htA =>
            cases hb with
            | box hboxB =>
                have hbad := ihStruct hbase' hborA hboxB
                simp [PartialTy.eqv] at hbad
            | borrow hborB htB =>
                rename_i mutA tgtsA borrowLifeA mutB tgtsB borrowLifeB
                have hmemDet : ∀ (tgts : List LVal),
                    (∀ t : LVal, t ∈ tgts → φ (LVal.base t) < n) →
                    ∀ m : LVal, m ∈ tgts → ∀ ma mb lma lmb,
                      LValTyping e1 m (.ty ma) lma →
                      LValTyping e2 m (.ty mb) lmb → Ty.eqv ma mb := by
                  intro tgts hlow m hm ma mb lma lmb hma hmb
                  have := ihRank (φ (LVal.base m)) (hlow m hm) m rfl hma hmb
                  simpa [PartialTy.eqv] using this
                have hlowA : ∀ t : LVal, t ∈ tgtsA → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutA tgtsA)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ1).1 hborA _ hvar
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
                have hlowB : ∀ t : LVal, t ∈ tgtsB → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutB tgtsB)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ2).1 hborB _ hvar
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
                have hlvEqv : PartialTy.eqv (.ty (.borrow mutA tgtsA))
                    (.ty (.borrow mutB tgtsB)) :=
                  ihStruct hbase' hborA hborB
                simp only [PartialTy.eqv, Ty.eqv] at hlvEqv
                obtain ⟨rfl, htAB, htBA⟩ := hlvEqv
                rcases LValTargetsTyping.output_full htA with ⟨aTy, haFull⟩
                rcases LValTargetsTyping.output_full htB with ⟨bTy, hbFull⟩
                subst haFull; subst hbFull
                have heqv : Ty.eqv aTy bTy :=
                  lvalTargetsTyping_subsetEquiv_eqv_cross htAB htBA
                    (hmemDet (tgtsA ++ tgtsB) (by
                      intro t ht
                      rcases List.mem_append.mp ht with h | h
                      · exact hlowA t h
                      · exact hlowB t h))
                    htA htB
                simpa [PartialTy.eqv] using heqv
    -- end deref

/-- Single-lval shape determinism (the coarse `sameShape` form used downstream),
derived from `lvalTyping_eqv`. -/
theorem lvalTyping_sameShape {env : Env} {φ : Name → Nat}
    (hφ : ∀ x slot, env.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) :
    ∀ (lv : LVal) {a b : PartialTy} {la lb : Lifetime},
      LValTyping env lv a la → LValTyping env lv b lb → PartialTy.sameShape a b := by
  intro lv a b la lb ha hb
  exact PartialTy.sameShape_of_eqv (lvalTyping_eqv hφ lv ha hb)

/-- A join is an upper bound of its left branch (`Γ₁ ⊑ Γ₁ ⊔ Γ₂`). -/
theorem EnvJoin.le_left {left right join : Env}
    (h : EnvJoin left right join) : left ≤ join :=
  h.1 (Set.mem_insert _ _)

/-- A join is an upper bound of its right branch (`Γ₂ ⊑ Γ₁ ⊔ Γ₂`). -/
theorem EnvJoin.le_right {left right join : Env}
    (h : EnvJoin left right join) : right ≤ join :=
  h.1 (Set.mem_insert_of_mem _ rfl)

/-- Slots present in both branches of a join have the same shape: each
branch slot is `sameShape` to the join slot (the `EnvJoinSameShape` rule
premises), and shapes compose through the join.  This is the cross-branch
fact needed by the same-shape strengthening maps of `T-IfJoin` and
`T-WhileJoin`. -/
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

/-- One-directional target-list transport at the type level.  Given a sub-list
inclusion `tgts ⊆ tgts'` of borrow targets jointly typed in two environments
`e` (type `pTy`) and `e'` (type `jTy`), together with per-member transport facts
(`hmem`: each shared member's `e`-type is `sameShape` and strengthens to its
`e'`-type), the joint types are `sameShape` and `pTy` strengthens to `jTy`.

  The proof uses the target-list union as a LUB: each member type in `tgts`
  strengthens to the corresponding member type in `tgts'`, and that member type
  strengthens to `jTy`; therefore `jTy` is an upper bound for the original list. -/
theorem lvalTargetsTyping_subset_strengthen {e e' : Env}
    {tgts tgts' : List LVal} {pTy jTy : Ty} {lf jLf : Lifetime}
    (hsub : tgts ⊆ tgts')
    (hmem : ∀ m, m ∈ tgts → ∀ mE mE' lmE lmE',
      LValTyping e m (.ty mE) lmE → LValTyping e' m (.ty mE') lmE' →
      Ty.sameShape mE mE' ∧ PartialTyStrengthens (.ty mE) (.ty mE'))
    (htgts : LValTargetsTyping e tgts (.ty pTy) lf)
    (htgts' : LValTargetsTyping e' tgts' (.ty jTy) jLf) :
    Ty.sameShape pTy jTy ∧ PartialTyStrengthens (.ty pTy) (.ty jTy) := by
  obtain ⟨h, hhmem⟩ : ∃ h, h ∈ tgts := by
    cases htgts with
    | singleton _ => exact ⟨_, List.mem_cons_self⟩
    | cons _ _ _ _ => exact ⟨_, List.mem_cons_self⟩
  obtain ⟨hE, hElt, hEty, hEle⟩ := lvalTargetsTyping_member_strengthens htgts h hhmem
  obtain ⟨hE', hE'lt, hE'ty, hE'le⟩ :=
    lvalTargetsTyping_member_strengthens htgts' h (hsub hhmem)
  obtain ⟨hmemShape, hmemStr⟩ := hmem h hhmem _ _ _ _ hEty hE'ty
  have hsameShape : Ty.sameShape pTy jTy := by
    have h1 : Ty.sameShape hE pTy := ty_sameShape_of_strengthens hEle
    have h2 : Ty.sameShape hE' jTy := ty_sameShape_of_strengthens hE'le
    exact Ty.sameShape_trans (Ty.sameShape_trans (Ty.sameShape_symm h1) hmemShape) h2
  refine ⟨hsameShape, ?_⟩
  exact lvalTargetsTyping_ty_le_of_members htgts
    (fun target htarget memberTy memberLifetime htyping =>
      let ⟨otherTy, otherLifetime, hotherTyping, hotherLe⟩ :=
        lvalTargetsTyping_member_strengthens htgts' target (hsub htarget)
      have hmemberStr : PartialTyStrengthens (.ty memberTy) (.ty otherTy) :=
        (hmem target htarget memberTy otherTy memberLifetime otherLifetime
          htyping hotherTyping).2
      partialTyStrengthens_trans hmemberStr hotherLe)


end Paper
end LwRust
