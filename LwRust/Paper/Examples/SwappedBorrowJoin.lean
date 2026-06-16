import LwRust.Paper.Typing

/-!
Build-checked conditional-join example for the crossed mutable-borrow pattern:

```text
let mut a = 0;
let mut b = 0;
let mut x;
let mut y;
if a == b {
  x = &mut a;
  y = &mut b;
} else {
  x = &mut b;
  y = &mut a;
}
```

  The declarations are represented by the pre-if environment below: `a` and `b`
  are initialized integers, while `x` and `y` are mutable-borrow-shaped slots with
  empty target lists.  The important point is the post-if join environment:
  `x : &mut [a, b]` and `y : &mut [b, a]`.  The join is accepted by `T-If`, while
  later dereference assignment through `x` is rejected by the assignment-local
  authority check.
-/

namespace LwRust
namespace Paper

open Core

def swappedBorrowA : LVal := .var "a"
def swappedBorrowB : LVal := .var "b"
def swappedBorrowX : LVal := .var "x"
def swappedBorrowY : LVal := .var "y"
def swappedBorrowC : LVal := .var "c"
def swappedBorrowP : LVal := .var "p"

def swappedBorrowIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def swappedBorrowSlot (targets : List LVal) : EnvSlot :=
  { ty := .ty (.borrow true targets), lifetime := Lifetime.root }

def swappedBorrowEnv (xTargets yTargets : List LVal) : Env :=
  ((((Env.empty.update "a" swappedBorrowIntSlot).update
    "b" swappedBorrowIntSlot).update
    "x" (swappedBorrowSlot xTargets)).update
    "y" (swappedBorrowSlot yTargets))

def swappedBorrowPreIfEnv : Env :=
  swappedBorrowEnv [] []

def swappedBorrowThenEnv : Env :=
  swappedBorrowEnv [swappedBorrowA] [swappedBorrowB]

def swappedBorrowThenXEnv : Env :=
  swappedBorrowPreIfEnv.update "x" (swappedBorrowSlot [swappedBorrowA])

def swappedBorrowElseEnv : Env :=
  swappedBorrowEnv [swappedBorrowB] [swappedBorrowA]

def swappedBorrowElseXEnv : Env :=
  swappedBorrowPreIfEnv.update "x" (swappedBorrowSlot [swappedBorrowB])

def swappedBorrowJoinEnv : Env :=
  swappedBorrowEnv [swappedBorrowA, swappedBorrowB]
    [swappedBorrowB, swappedBorrowA]

private theorem swappedBorrow_env_ext (left right : Env)
    (h : ∀ x, left.slotAt x = right.slotAt x) : left = right := by
  cases left with
  | mk leftSlotAt =>
      cases right with
      | mk rightSlotAt =>
          have hfun : leftSlotAt = rightSlotAt := funext h
          subst hfun
          rfl

private theorem swappedBorrowEnv_slotAt_a (xTargets yTargets : List LVal) :
    (swappedBorrowEnv xTargets yTargets).slotAt "a" =
      some swappedBorrowIntSlot := by
  simp [swappedBorrowEnv, Env.update]

private theorem swappedBorrowEnv_slotAt_b (xTargets yTargets : List LVal) :
    (swappedBorrowEnv xTargets yTargets).slotAt "b" =
      some swappedBorrowIntSlot := by
  simp [swappedBorrowEnv, Env.update]

private theorem swappedBorrowEnv_slotAt_x (xTargets yTargets : List LVal) :
    (swappedBorrowEnv xTargets yTargets).slotAt "x" =
      some (swappedBorrowSlot xTargets) := by
  simp [swappedBorrowEnv, Env.update]

private theorem swappedBorrowEnv_slotAt_y (xTargets yTargets : List LVal) :
    (swappedBorrowEnv xTargets yTargets).slotAt "y" =
      some (swappedBorrowSlot yTargets) := by
  simp [swappedBorrowEnv, Env.update]

private theorem swappedBorrowEnv_slotAt_none (xTargets yTargets : List LVal)
    {name : Name} (hy : name ≠ "y") (hx : name ≠ "x") (hb : name ≠ "b")
    (ha : name ≠ "a") :
    (swappedBorrowEnv xTargets yTargets).slotAt name = none := by
  simp [swappedBorrowEnv, Env.update, Env.empty, hy, hx, hb, ha]

private theorem swappedBorrowEnv_update_x (xTargets yTargets xTargets' :
    List LVal) :
    (swappedBorrowEnv xTargets yTargets).update "x"
        (swappedBorrowSlot xTargets') =
      swappedBorrowEnv xTargets' yTargets := by
  apply swappedBorrow_env_ext
  intro name
  by_cases hy : name = "y" <;> by_cases hx : name = "x" <;>
    by_cases hb : name = "b" <;> by_cases ha : name = "a" <;>
    simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
      Env.update, Env.empty, hy, hx, hb, ha]

private theorem swappedBorrowEnv_update_y (xTargets yTargets yTargets' :
    List LVal) :
    (swappedBorrowEnv xTargets yTargets).update "y"
        (swappedBorrowSlot yTargets') =
      swappedBorrowEnv xTargets yTargets' := by
  apply swappedBorrow_env_ext
  intro name
  by_cases hy : name = "y" <;> by_cases hx : name = "x" <;>
    by_cases hb : name = "b" <;> by_cases ha : name = "a" <;>
    simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
      Env.update, Env.empty, hy, hx, hb, ha]

private theorem swappedBorrowThenXEnv_eq :
    swappedBorrowThenXEnv = swappedBorrowEnv [swappedBorrowA] [] := by
  rw [swappedBorrowThenXEnv, swappedBorrowPreIfEnv, swappedBorrowEnv_update_x]

private theorem swappedBorrowElseXEnv_eq :
    swappedBorrowElseXEnv = swappedBorrowEnv [swappedBorrowB] [] := by
  rw [swappedBorrowElseXEnv, swappedBorrowPreIfEnv, swappedBorrowEnv_update_x]

private theorem swappedBorrow_partialTyStrengthens_borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal} {joined : PartialTy}
    (hleft : PartialTyStrengthens (.ty (.borrow mutable leftTargets)) joined)
    (hright : PartialTyStrengthens (.ty (.borrow mutable rightTargets)) joined) :
    PartialTyStrengthens (.ty (.borrow mutable (leftTargets ++ rightTargets)))
      joined := by
  have borrowSubset : ∀ {targets joinedTargets : List LVal},
      PartialTyStrengthens (.ty (.borrow mutable targets))
        (.ty (.borrow mutable joinedTargets)) →
      targets.Subset joinedTargets := by
    intro targets joinedTargets hstrength target hmem
    cases hstrength with
    | reflex =>
        exact hmem
    | borrow hsubset =>
        exact hsubset hmem
  cases hleft with
  | reflex =>
      have hsubRight := borrowSubset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hmem
        · exact hsubRight hmem)
  | borrow hsubLeft =>
      have hsubRight := borrowSubset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem)
  | intoUndef hleft' =>
      cases hright with
      | intoUndef hright' =>
          cases hleft' with
          | reflex =>
              have hsubRight := borrowSubset hright'
              exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
                intro target htarget
                rcases List.mem_append.mp htarget with hmem | hmem
                · exact hmem
                · exact hsubRight hmem))
          | borrow hsubLeft =>
              have hsubRight := borrowSubset hright'
              exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
                intro target htarget
                rcases List.mem_append.mp htarget with hmem | hmem
                · exact hsubLeft hmem
                · exact hsubRight hmem))

private theorem swappedBorrow_a_typing {xTargets yTargets : List LVal} :
    LValTyping (swappedBorrowEnv xTargets yTargets) swappedBorrowA
      (.ty .int) Lifetime.root := by
  exact @LValTyping.var (swappedBorrowEnv xTargets yTargets) "a"
    swappedBorrowIntSlot (by
      simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
        Env.update])

private theorem swappedBorrow_b_typing {xTargets yTargets : List LVal} :
    LValTyping (swappedBorrowEnv xTargets yTargets) swappedBorrowB
      (.ty .int) Lifetime.root := by
  exact @LValTyping.var (swappedBorrowEnv xTargets yTargets) "b"
    swappedBorrowIntSlot (by
      simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
        Env.update])

private theorem swappedBorrow_x_typing {xTargets yTargets : List LVal} :
    LValTyping (swappedBorrowEnv xTargets yTargets) swappedBorrowX
      (.ty (.borrow true xTargets)) Lifetime.root := by
  exact @LValTyping.var (swappedBorrowEnv xTargets yTargets) "x"
    (swappedBorrowSlot xTargets) (by
      simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
        Env.update])

private theorem swappedBorrow_y_typing {xTargets yTargets : List LVal} :
    LValTyping (swappedBorrowEnv xTargets yTargets) swappedBorrowY
      (.ty (.borrow true yTargets)) Lifetime.root := by
  exact @LValTyping.var (swappedBorrowEnv xTargets yTargets) "y"
    (swappedBorrowSlot yTargets) (by
      simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
        Env.update])

private theorem swappedBorrow_targets_a {xTargets yTargets : List LVal} :
    LValTargetsTyping (swappedBorrowEnv xTargets yTargets) [swappedBorrowA]
      (.ty .int) Lifetime.root :=
  LValTargetsTyping.singleton swappedBorrow_a_typing

private theorem swappedBorrow_targets_b {xTargets yTargets : List LVal} :
    LValTargetsTyping (swappedBorrowEnv xTargets yTargets) [swappedBorrowB]
      (.ty .int) Lifetime.root :=
  LValTargetsTyping.singleton swappedBorrow_b_typing

private theorem swappedBorrow_targets_ab {xTargets yTargets : List LVal} :
    LValTargetsTyping (swappedBorrowEnv xTargets yTargets)
      [swappedBorrowA, swappedBorrowB] (.ty .int) Lifetime.root :=
  LValTargetsTyping.cons swappedBorrow_a_typing
    (LValTargetsTyping.singleton swappedBorrow_b_typing)
    (PartialTyUnion.self (.ty .int))
    (LifetimeIntersection.self Lifetime.root)

private theorem swappedBorrow_targets_ba {xTargets yTargets : List LVal} :
    LValTargetsTyping (swappedBorrowEnv xTargets yTargets)
      [swappedBorrowB, swappedBorrowA] (.ty .int) Lifetime.root :=
  LValTargetsTyping.cons swappedBorrow_b_typing
    (LValTargetsTyping.singleton swappedBorrow_a_typing)
    (PartialTyUnion.self (.ty .int))
    (LifetimeIntersection.self Lifetime.root)

private theorem swappedBorrow_a_mutable {xTargets yTargets : List LVal} :
    Mutable (swappedBorrowEnv xTargets yTargets) swappedBorrowA :=
  @Mutable.var (swappedBorrowEnv xTargets yTargets) "a" swappedBorrowIntSlot
    (by
      simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
        Env.update])

private theorem swappedBorrow_b_mutable {xTargets yTargets : List LVal} :
    Mutable (swappedBorrowEnv xTargets yTargets) swappedBorrowB :=
  @Mutable.var (swappedBorrowEnv xTargets yTargets) "b" swappedBorrowIntSlot
    (by
      simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
        Env.update])

private def SwappedBorrowGoodTargets (targets : List LVal) : Prop :=
  ∀ target ∈ targets, target = swappedBorrowA ∨ target = swappedBorrowB

private theorem swappedBorrow_empty_good :
    SwappedBorrowGoodTargets [] := by
  intro target htarget
  cases htarget

private theorem swappedBorrow_a_good :
    SwappedBorrowGoodTargets [swappedBorrowA] := by
  intro target htarget
  simp at htarget
  exact Or.inl htarget

private theorem swappedBorrow_b_good :
    SwappedBorrowGoodTargets [swappedBorrowB] := by
  intro target htarget
  simp at htarget
  exact Or.inr htarget

private theorem swappedBorrow_ab_good :
    SwappedBorrowGoodTargets [swappedBorrowA, swappedBorrowB] := by
  intro target htarget
  simpa using htarget

private theorem swappedBorrow_ba_good :
    SwappedBorrowGoodTargets [swappedBorrowB, swappedBorrowA] := by
  intro target htarget
  simp at htarget
  rcases htarget with htarget | htarget
  · exact Or.inr htarget
  · exact Or.inl htarget

private theorem swappedBorrow_target_typing {xTargets yTargets : List LVal}
    {target : LVal}
    (htarget : target = swappedBorrowA ∨ target = swappedBorrowB) :
    LValTyping (swappedBorrowEnv xTargets yTargets) target (.ty .int)
      Lifetime.root := by
  rcases htarget with rfl | rfl
  · exact swappedBorrow_a_typing
  · exact swappedBorrow_b_typing

private theorem swappedBorrow_target_base_outlives
    {xTargets yTargets : List LVal} {target : LVal}
    (htarget : target = swappedBorrowA ∨ target = swappedBorrowB) :
    LValBaseOutlives (swappedBorrowEnv xTargets yTargets) target
      Lifetime.root := by
  rcases htarget with rfl | rfl
  · exact ⟨swappedBorrowIntSlot, by
      simpa [swappedBorrowA, LVal.base] using
        swappedBorrowEnv_slotAt_a xTargets yTargets,
      LifetimeOutlives.refl Lifetime.root⟩
  · exact ⟨swappedBorrowIntSlot, by
      simpa [swappedBorrowB, LVal.base] using
        swappedBorrowEnv_slotAt_b xTargets yTargets,
      LifetimeOutlives.refl Lifetime.root⟩

private theorem swappedBorrow_goodTarget_wellFormed
    {xTargets yTargets : List LVal} {target : LVal}
    (htarget : target = swappedBorrowA ∨ target = swappedBorrowB) :
    ∃ targetTy targetLifetime,
      LValTyping (swappedBorrowEnv xTargets yTargets) target
        (.ty targetTy) targetLifetime ∧
      targetLifetime ≤ Lifetime.root ∧
      LValBaseOutlives (swappedBorrowEnv xTargets yTargets) target
        Lifetime.root := by
  exact ⟨.int, Lifetime.root, swappedBorrow_target_typing htarget,
    LifetimeOutlives.refl Lifetime.root,
    swappedBorrow_target_base_outlives htarget⟩

private theorem swappedBorrow_borrow_wellFormed {xTargets yTargets targets :
    List LVal} {mutable : Bool}
    (hgood : SwappedBorrowGoodTargets targets) :
    WellFormedTy (swappedBorrowEnv xTargets yTargets)
      (.borrow mutable targets) Lifetime.root := by
  exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
    intro target htarget
    exact swappedBorrow_goodTarget_wellFormed (hgood target htarget)))

private theorem swappedBorrow_shape_borrow {xTargets yTargets leftTargets
    rightTargets : List LVal} {mutable : Bool}
    (hleft : SwappedBorrowGoodTargets leftTargets)
    (hright : SwappedBorrowGoodTargets rightTargets) :
    ShapeCompatible (swappedBorrowEnv xTargets yTargets)
      (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets)) := by
  refine ShapeCompatible.borrow ?left ?right ShapeCompatible.int
  · intro target htarget
    exact ⟨Lifetime.root, swappedBorrow_target_typing (hleft target htarget)⟩
  · intro target htarget
    exact ⟨Lifetime.root, swappedBorrow_target_typing (hright target htarget)⟩

private theorem swappedBorrowEnv_drop_body_lifetime
    (xTargets yTargets : List LVal) :
    (swappedBorrowEnv xTargets yTargets).dropLifetime [0] =
      swappedBorrowEnv xTargets yTargets := by
  apply swappedBorrow_env_ext
  intro name
  by_cases hy : name = "y" <;> by_cases hx : name = "x" <;>
    by_cases hb : name = "b" <;> by_cases ha : name = "a" <;>
    simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
      Env.dropLifetime, Env.update, Env.empty, Lifetime.root, hy, hx, hb, ha]

private theorem swappedBorrow_old_root_int (xTargets yTargets : List LVal) :
    ∀ {lv partialTy lifetime},
      LVal.base lv ≠ "x" →
      LVal.base lv ≠ "y" →
      LValTyping (swappedBorrowEnv xTargets yTargets) lv partialTy lifetime →
      (lv = swappedBorrowA ∨ lv = swappedBorrowB) ∧
        partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  intro lv
  induction lv with
  | var name =>
      intro partialTy lifetime hbaseX hbaseY htyping
      cases htyping with
      | var hslot =>
          rename_i slot
          by_cases hy : name = "y"
          · subst hy
            simp [LVal.base] at hbaseY
          · by_cases hx : name = "x"
            · subst hx
              simp [LVal.base] at hbaseX
            · by_cases hb : name = "b"
              · subst hb
                have hslotEq : slot = swappedBorrowIntSlot :=
                  Option.some.inj
                    (hslot.symm.trans
                      (swappedBorrowEnv_slotAt_b xTargets yTargets))
                subst slot
                simp [swappedBorrowB, swappedBorrowIntSlot]
              · by_cases ha : name = "a"
                · subst ha
                  have hslotEq : slot = swappedBorrowIntSlot :=
                    Option.some.inj
                      (hslot.symm.trans
                        (swappedBorrowEnv_slotAt_a xTargets yTargets))
                  subst slot
                  simp [swappedBorrowA, swappedBorrowIntSlot]
                · have hnone :
                      (swappedBorrowEnv xTargets yTargets).slotAt name =
                        none :=
                    swappedBorrowEnv_slotAt_none xTargets yTargets hy hx hb ha
                  rw [hslot] at hnone
                  cases hnone
  | deref lv ih =>
      intro partialTy lifetime hbaseX hbaseY htyping
      cases htyping with
      | box hinner =>
          rcases ih (by simpa [LVal.base] using hbaseX)
              (by simpa [LVal.base] using hbaseY) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy
      | borrow hinner _htargets =>
          rcases ih (by simpa [LVal.base] using hbaseX)
              (by simpa [LVal.base] using hbaseY) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy

private theorem swappedBorrow_no_good_targets_borrow
    (xTargets yTargets : List LVal) {targets : List LVal}
    (htargets : SwappedBorrowGoodTargets targets) {mutable : Bool}
    {borrowTargets : List LVal} {lifetime : Lifetime} :
    ¬ LValTargetsTyping (swappedBorrowEnv xTargets yTargets) targets
      (.ty (.borrow mutable borrowTargets)) lifetime := by
  intro htyping
  generalize hpartialTy :
      (PartialTy.ty (Ty.borrow mutable borrowTargets)) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases htargets _ List.mem_cons_self with rfl | rfl
      all_goals
        rcases swappedBorrow_old_root_int xTargets yTargets
            (by simp [swappedBorrowA, swappedBorrowB, LVal.base])
            (by simp [swappedBorrowA, swappedBorrowB, LVal.base]) htarget with
          ⟨_, htargetTy, _⟩
        rw [← hpartialTy] at htargetTy
        cases htargetTy
  | cons hhead hrest hunion _hlifetime =>
      rcases htargets _ List.mem_cons_self with rfl | rfl
      all_goals
        rcases swappedBorrow_old_root_int xTargets yTargets
            (by simp [swappedBorrowA, swappedBorrowB, LVal.base])
            (by simp [swappedBorrowA, swappedBorrowB, LVal.base]) hhead with
          ⟨_, hheadTy, _⟩
        injection hheadTy with hheadTy
        subst hheadTy
        have hupper : PartialTyStrengthens (.ty .int) partialTy :=
          hunion.1 (by simp)
        rw [← hpartialTy] at hupper
        cases hupper

private theorem swappedBorrow_no_good_targets_box
    (xTargets yTargets : List LVal) {targets : List LVal}
    (htargets : SwappedBorrowGoodTargets targets) {inner : PartialTy}
    {lifetime : Lifetime} :
    ¬ LValTargetsTyping (swappedBorrowEnv xTargets yTargets) targets
      (.box inner) lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases htargets _ List.mem_cons_self with rfl | rfl
      all_goals
        rcases swappedBorrow_old_root_int xTargets yTargets
            (by simp [swappedBorrowA, swappedBorrowB, LVal.base])
            (by simp [swappedBorrowA, swappedBorrowB, LVal.base]) htarget with
          ⟨_, htargetTy, _⟩
        rw [← hpartialTy] at htargetTy
        cases htargetTy
  | cons hhead hrest hunion _hlifetime =>
      rcases htargets _ List.mem_cons_self with rfl | rfl
      all_goals
        rcases swappedBorrow_old_root_int xTargets yTargets
            (by simp [swappedBorrowA, swappedBorrowB, LVal.base])
            (by simp [swappedBorrowA, swappedBorrowB, LVal.base]) hhead with
          ⟨_, hheadTy, _⟩
        injection hheadTy with hheadTy
        subst hheadTy
        have hupper : PartialTyStrengthens (.ty .int) partialTy :=
          hunion.1 (by simp)
        rw [← hpartialTy] at hupper
        cases hupper

private theorem swappedBorrow_x_root_facts (xTargets yTargets : List LVal)
    (hxGood : SwappedBorrowGoodTargets xTargets) : ∀ {lv},
    LVal.base lv = "x" →
    (∀ {inner lifetime},
      ¬ LValTyping (swappedBorrowEnv xTargets yTargets) lv
        (.box inner) lifetime) ∧
    (∀ {mutable targets lifetime},
      LValTyping (swappedBorrowEnv xTargets yTargets) lv
        (.ty (.borrow mutable targets)) lifetime →
      lv = swappedBorrowX ∧ mutable = true ∧ targets = xTargets ∧
        lifetime = Lifetime.root) := by
  intro lv
  induction lv with
  | var name =>
      intro hbase
      constructor
      · intro inner lifetime htyping
        generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : name = "x" := by simpa [LVal.base] using hbase
            subst hx
            have hslotEq : slot = swappedBorrowSlot xTargets :=
              Option.some.inj
                (hslot.symm.trans
                  (swappedBorrowEnv_slotAt_x xTargets yTargets))
            subst slot
            simp [swappedBorrowSlot] at hpartialTy
      · intro mutable targets lifetime htyping
        generalize hpartialTy :
            (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : name = "x" := by simpa [LVal.base] using hbase
            subst hx
            have hslotEq : slot = swappedBorrowSlot xTargets :=
              Option.some.inj
                (hslot.symm.trans
                  (swappedBorrowEnv_slotAt_x xTargets yTargets))
            subst slot
            simp [swappedBorrowSlot] at hpartialTy
            rcases hpartialTy with ⟨rfl, rfl⟩
            simp [swappedBorrowX, swappedBorrowSlot]
  | deref lv ih =>
      intro hbase
      have ihp := ih (by simpa [LVal.base] using hbase)
      constructor
      · intro inner lifetime htyping
        cases htyping with
        | box hinner =>
            exact ihp.1 hinner
        | borrow hinner htargets =>
            rcases ihp.2 hinner with ⟨rfl, rfl, rfl, rfl⟩
            exact swappedBorrow_no_good_targets_box _ _
              hxGood htargets
      · intro mutable targets lifetime htyping
        cases htyping with
        | box hinner =>
            exact False.elim (ihp.1 hinner)
        | borrow hinner htargets =>
            rcases ihp.2 hinner with ⟨rfl, rfl, rfl, rfl⟩
            exact False.elim
              (swappedBorrow_no_good_targets_borrow _ _
                hxGood htargets)

private theorem swappedBorrow_y_root_facts (xTargets yTargets : List LVal)
    (hyGood : SwappedBorrowGoodTargets yTargets) : ∀ {lv},
    LVal.base lv = "y" →
    (∀ {inner lifetime},
      ¬ LValTyping (swappedBorrowEnv xTargets yTargets) lv
        (.box inner) lifetime) ∧
    (∀ {mutable targets lifetime},
      LValTyping (swappedBorrowEnv xTargets yTargets) lv
        (.ty (.borrow mutable targets)) lifetime →
      lv = swappedBorrowY ∧ mutable = true ∧ targets = yTargets ∧
        lifetime = Lifetime.root) := by
  intro lv
  induction lv with
  | var name =>
      intro hbase
      constructor
      · intro inner lifetime htyping
        generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hy : name = "y" := by simpa [LVal.base] using hbase
            subst hy
            have hslotEq : slot = swappedBorrowSlot yTargets :=
              Option.some.inj
                (hslot.symm.trans
                  (swappedBorrowEnv_slotAt_y xTargets yTargets))
            subst slot
            simp [swappedBorrowSlot] at hpartialTy
      · intro mutable targets lifetime htyping
        generalize hpartialTy :
            (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hy : name = "y" := by simpa [LVal.base] using hbase
            subst hy
            have hslotEq : slot = swappedBorrowSlot yTargets :=
              Option.some.inj
                (hslot.symm.trans
                  (swappedBorrowEnv_slotAt_y xTargets yTargets))
            subst slot
            simp [swappedBorrowSlot] at hpartialTy
            rcases hpartialTy with ⟨rfl, rfl⟩
            simp [swappedBorrowY, swappedBorrowSlot]
  | deref lv ih =>
      intro hbase
      have ihp := ih (by simpa [LVal.base] using hbase)
      constructor
      · intro inner lifetime htyping
        cases htyping with
        | box hinner =>
            exact ihp.1 hinner
        | borrow hinner htargets =>
            rcases ihp.2 hinner with ⟨rfl, rfl, rfl, rfl⟩
            exact swappedBorrow_no_good_targets_box _ _
              hyGood htargets
      · intro mutable targets lifetime htyping
        cases htyping with
        | box hinner =>
            exact False.elim (ihp.1 hinner)
        | borrow hinner htargets =>
            rcases ihp.2 hinner with ⟨rfl, rfl, rfl, rfl⟩
            exact False.elim
              (swappedBorrow_no_good_targets_borrow _ _
                hyGood htargets)

private theorem swappedBorrowEnv_contained
    (xTargets yTargets : List LVal)
    (hxGood : SwappedBorrowGoodTargets xTargets)
    (hyGood : SwappedBorrowGoodTargets yTargets) :
    ContainedBorrowsWellFormed (swappedBorrowEnv xTargets yTargets) := by
  intro root slot mutable targets hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hy : root = "y"
  · subst hy
    have hslotEq : slot = swappedBorrowSlot yTargets :=
      Option.some.inj
        (hslot.symm.trans (swappedBorrowEnv_slotAt_y xTargets yTargets))
    subst slot
    have hcontainedEq : containedSlot = swappedBorrowSlot yTargets :=
      Option.some.inj
        (hcontainedSlot.symm.trans
          (swappedBorrowEnv_slotAt_y xTargets yTargets))
    subst containedSlot
    simp [swappedBorrowSlot] at hcontainsTy
    cases hcontainsTy with
    | here =>
        intro target htarget
        exact swappedBorrow_goodTarget_wellFormed (hyGood target htarget)
  · by_cases hx : root = "x"
    · subst hx
      have hslotEq : slot = swappedBorrowSlot xTargets :=
        Option.some.inj
          (hslot.symm.trans (swappedBorrowEnv_slotAt_x xTargets yTargets))
      subst slot
      have hcontainedEq : containedSlot = swappedBorrowSlot xTargets :=
        Option.some.inj
          (hcontainedSlot.symm.trans
            (swappedBorrowEnv_slotAt_x xTargets yTargets))
      subst containedSlot
      simp [swappedBorrowSlot] at hcontainsTy
      cases hcontainsTy with
      | here =>
          intro target htarget
          exact swappedBorrow_goodTarget_wellFormed (hxGood target htarget)
    · by_cases hb : root = "b"
      · subst hb
        have hcontainedEq : containedSlot = swappedBorrowIntSlot :=
          Option.some.inj
            (hcontainedSlot.symm.trans
              (swappedBorrowEnv_slotAt_b xTargets yTargets))
        subst containedSlot
        simp [swappedBorrowIntSlot] at hcontainsTy
        cases hcontainsTy
      · by_cases ha : root = "a"
        · subst ha
          have hcontainedEq : containedSlot = swappedBorrowIntSlot :=
            Option.some.inj
              (hcontainedSlot.symm.trans
                (swappedBorrowEnv_slotAt_a xTargets yTargets))
          subst containedSlot
          simp [swappedBorrowIntSlot] at hcontainsTy
          cases hcontainsTy
        · have hnone :
              (swappedBorrowEnv xTargets yTargets).slotAt root = none :=
            swappedBorrowEnv_slotAt_none xTargets yTargets hy hx hb ha
          rw [hslot] at hnone
          cases hnone

private theorem swappedBorrowEnv_coherent (xTargets yTargets : List LVal)
    (hxGood : SwappedBorrowGoodTargets xTargets)
    (hyGood : SwappedBorrowGoodTargets yTargets)
    (hxJoint : ∃ ty lifetime,
      LValTargetsTyping (swappedBorrowEnv xTargets yTargets) xTargets
        (.ty ty) lifetime)
    (hyJoint : ∃ ty lifetime,
      LValTargetsTyping (swappedBorrowEnv xTargets yTargets) yTargets
        (.ty ty) lifetime) :
    Coherent (swappedBorrowEnv xTargets yTargets) := by
  intro lv mutable targets borrowLifetime htyping
  by_cases hx : LVal.base lv = "x"
  · rcases (swappedBorrow_x_root_facts xTargets yTargets hxGood hx).2
      htyping with ⟨rfl, rfl, rfl, rfl⟩
    exact hxJoint
  · by_cases hy : LVal.base lv = "y"
    · rcases (swappedBorrow_y_root_facts xTargets yTargets hyGood hy).2
        htyping with ⟨rfl, rfl, rfl, rfl⟩
      exact hyJoint
    · rcases swappedBorrow_old_root_int xTargets yTargets hx hy htyping with
        ⟨_, hpartialTy, _⟩
      cases hpartialTy

private def swappedBorrowRank : Name → Nat :=
  fun name => if name = "x" ∨ name = "y" then 1 else 0

private theorem swappedBorrowEnv_linearizedBy (xTargets yTargets : List LVal)
    (hxGood : SwappedBorrowGoodTargets xTargets)
    (hyGood : SwappedBorrowGoodTargets yTargets) :
    LinearizedBy swappedBorrowRank (swappedBorrowEnv xTargets yTargets) := by
  intro root slot hslot v hv
  by_cases hy : root = "y"
  · subst hy
    have hslotEq : slot = swappedBorrowSlot yTargets :=
      Option.some.inj
        (hslot.symm.trans (swappedBorrowEnv_slotAt_y xTargets yTargets))
    subst slot
    simp [swappedBorrowSlot, PartialTy.vars, Ty.vars] at hv
    rcases hv with ⟨target, htarget, rfl⟩
    rcases hyGood target htarget with rfl | rfl <;>
      simp [swappedBorrowRank, swappedBorrowA, swappedBorrowB, LVal.base]
  · by_cases hx : root = "x"
    · subst hx
      have hslotEq : slot = swappedBorrowSlot xTargets :=
        Option.some.inj
          (hslot.symm.trans (swappedBorrowEnv_slotAt_x xTargets yTargets))
      subst slot
      simp [swappedBorrowSlot, PartialTy.vars, Ty.vars] at hv
      rcases hv with ⟨target, htarget, rfl⟩
      rcases hxGood target htarget with rfl | rfl <;>
        simp [swappedBorrowRank, swappedBorrowA, swappedBorrowB, LVal.base]
    · by_cases hb : root = "b"
      · subst hb
        have hslotEq : slot = swappedBorrowIntSlot :=
          Option.some.inj
            (hslot.symm.trans (swappedBorrowEnv_slotAt_b xTargets yTargets))
        subst slot
        simp [swappedBorrowIntSlot, PartialTy.vars, Ty.vars] at hv
      · by_cases ha : root = "a"
        · subst ha
          have hslotEq : slot = swappedBorrowIntSlot :=
            Option.some.inj
              (hslot.symm.trans (swappedBorrowEnv_slotAt_a xTargets yTargets))
          subst slot
          simp [swappedBorrowIntSlot, PartialTy.vars, Ty.vars] at hv
        · have hnone :
              (swappedBorrowEnv xTargets yTargets).slotAt root = none :=
            swappedBorrowEnv_slotAt_none xTargets yTargets hy hx hb ha
          rw [hslot] at hnone
          cases hnone

private theorem swappedBorrowEnv_linearizable (xTargets yTargets : List LVal)
    (hxGood : SwappedBorrowGoodTargets xTargets)
    (hyGood : SwappedBorrowGoodTargets yTargets) :
    Linearizable (swappedBorrowEnv xTargets yTargets) :=
  ⟨swappedBorrowRank, swappedBorrowEnv_linearizedBy xTargets yTargets
    hxGood hyGood⟩

private theorem swappedBorrowEnv_borrow_root_facts
    (xTargets yTargets : List LVal) {root : Name} {mutable : Bool}
    {targets : List LVal} :
    (swappedBorrowEnv xTargets yTargets) ⊢ root ↝
      (Ty.borrow mutable targets) →
    (root = "x" ∧ mutable = true ∧ targets = xTargets) ∨
      (root = "y" ∧ mutable = true ∧ targets = yTargets) := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hy : root = "y"
  · subst hy
    have hslotEq : slot = swappedBorrowSlot yTargets :=
      Option.some.inj
        (hslot.symm.trans (swappedBorrowEnv_slotAt_y xTargets yTargets))
    subst slot
    simp [swappedBorrowSlot] at hcontains
    cases hcontains with
    | here =>
        exact Or.inr ⟨rfl, rfl, rfl⟩
  · by_cases hx : root = "x"
    · subst hx
      have hslotEq : slot = swappedBorrowSlot xTargets :=
        Option.some.inj
          (hslot.symm.trans (swappedBorrowEnv_slotAt_x xTargets yTargets))
      subst slot
      simp [swappedBorrowSlot] at hcontains
      cases hcontains with
      | here =>
          exact Or.inl ⟨rfl, rfl, rfl⟩
    · by_cases hb : root = "b"
      · subst hb
        have hslotEq : slot = swappedBorrowIntSlot :=
          Option.some.inj
            (hslot.symm.trans (swappedBorrowEnv_slotAt_b xTargets yTargets))
        subst slot
        simp [swappedBorrowIntSlot] at hcontains
        cases hcontains
      · by_cases ha : root = "a"
        · subst ha
          have hslotEq : slot = swappedBorrowIntSlot :=
            Option.some.inj
              (hslot.symm.trans (swappedBorrowEnv_slotAt_a xTargets yTargets))
          subst slot
          simp [swappedBorrowIntSlot] at hcontains
          cases hcontains
        · have hnone :
              (swappedBorrowEnv xTargets yTargets).slotAt root = none :=
            swappedBorrowEnv_slotAt_none xTargets yTargets hy hx hb ha
          rw [hslot] at hnone
          cases hnone

private theorem swappedBorrowEnv_rhs_borrow_targets_below
    (xTargets yTargets rhsTargets : List LVal) (writeRoot : Name)
    (hxGood : SwappedBorrowGoodTargets xTargets)
    (hyGood : SwappedBorrowGoodTargets yTargets)
    (hrootOfRhs :
      ∀ root mutable targets target,
        (swappedBorrowEnv xTargets yTargets) ⊢ root ↝
          (Ty.borrow mutable targets) →
        target ∈ targets →
        target ∈ rhsTargets →
        root = writeRoot) :
    EnvWriteRhsBorrowTargetsBelow swappedBorrowRank
      (swappedBorrowEnv xTargets yTargets) (.borrow true rhsTargets) := by
  constructor
  · intro root slot mutable targets target hslot hcontains htarget _hrhs
    rcases swappedBorrowEnv_borrow_root_facts xTargets yTargets
        ⟨slot, hslot, hcontains⟩ with hroot | hroot
    · rcases hroot with ⟨rfl, rfl, rfl⟩
      rcases hxGood target htarget with rfl | rfl <;>
        simp [swappedBorrowRank, swappedBorrowA, swappedBorrowB, LVal.base]
    · rcases hroot with ⟨rfl, rfl, rfl⟩
      rcases hyGood target htarget with rfl | rfl <;>
        simp [swappedBorrowRank, swappedBorrowA, swappedBorrowB, LVal.base]
  · intro root other mutable targetsMutable targetsOther targetMutable targetOther
      hcontainsMutable hcontainsOther htargetMutable htargetOther _hconflict
      hrhsMutable hrhsOther
    rcases hrhsMutable with
      ⟨_rhsMutable, rhsTargetsMutable, hcontainsRhsMutable,
        htargetRhsMutable⟩
    rcases hrhsOther with
      ⟨_rhsOtherMutable, rhsTargetsOther, hcontainsRhsOther,
        htargetRhsOther⟩
    cases hcontainsRhsMutable with
    | here =>
        cases hcontainsRhsOther with
        | here =>
            have hroot := hrootOfRhs root true targetsMutable targetMutable
              hcontainsMutable htargetMutable htargetRhsMutable
            have hother := hrootOfRhs other mutable targetsOther targetOther
              hcontainsOther htargetOther htargetRhsOther
            exact hroot.trans hother.symm

private theorem swappedBorrowEnv_sameShape {xTargets yTargets xTargets' yTargets' :
    List LVal} :
    EnvJoinSameShape (swappedBorrowEnv xTargets yTargets)
      (swappedBorrowEnv xTargets' yTargets') := by
  intro x branchSlot joinSlot hbranch hjoinSlot
  by_cases hy : x = "y"
  · subst hy
    simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
      Env.update] at hbranch hjoinSlot
    cases hbranch
    cases hjoinSlot
    simp [PartialTy.sameShape, Ty.sameShape]
  · by_cases hx : x = "x"
    · subst hx
      simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
        Env.update] at hbranch hjoinSlot
      cases hbranch
      cases hjoinSlot
      simp [PartialTy.sameShape, Ty.sameShape]
    · by_cases hb : x = "b"
      · subst hb
        simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
          Env.update] at hbranch hjoinSlot
        cases hbranch
        cases hjoinSlot
        simp [PartialTy.sameShape, Ty.sameShape]
      · by_cases ha : x = "a"
        · subst ha
          simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
            Env.update] at hbranch hjoinSlot
          cases hbranch
          cases hjoinSlot
          simp [PartialTy.sameShape, Ty.sameShape]
        · simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
            Env.update, Env.empty, hy, hx, hb, ha] at hbranch

private theorem swappedBorrowThen_le_join :
    EnvStrengthens swappedBorrowThenEnv swappedBorrowJoinEnv := by
  intro name
  by_cases hy : name = "y"
  · subst hy
    rw [show swappedBorrowThenEnv.slotAt "y" =
        some (swappedBorrowSlot [swappedBorrowB]) by
          exact swappedBorrowEnv_slotAt_y _ _,
      show swappedBorrowJoinEnv.slotAt "y" =
        some (swappedBorrowSlot [swappedBorrowB, swappedBorrowA]) by
          exact swappedBorrowEnv_slotAt_y _ _]
    exact ⟨rfl, PartialTyStrengthens.borrow (by
      intro target htarget
      simp at htarget ⊢
      exact Or.inl htarget)⟩
  · by_cases hx : name = "x"
    · subst hx
      rw [show swappedBorrowThenEnv.slotAt "x" =
          some (swappedBorrowSlot [swappedBorrowA]) by
            exact swappedBorrowEnv_slotAt_x _ _,
        show swappedBorrowJoinEnv.slotAt "x" =
          some (swappedBorrowSlot [swappedBorrowA, swappedBorrowB]) by
            exact swappedBorrowEnv_slotAt_x _ _]
      exact ⟨rfl, PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inl htarget)⟩
    · by_cases hb : name = "b"
      · subst hb
        rw [show swappedBorrowThenEnv.slotAt "b" =
            some swappedBorrowIntSlot by exact swappedBorrowEnv_slotAt_b _ _,
          show swappedBorrowJoinEnv.slotAt "b" =
            some swappedBorrowIntSlot by exact swappedBorrowEnv_slotAt_b _ _]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · by_cases ha : name = "a"
        · subst ha
          rw [show swappedBorrowThenEnv.slotAt "a" =
              some swappedBorrowIntSlot by exact swappedBorrowEnv_slotAt_a _ _,
            show swappedBorrowJoinEnv.slotAt "a" =
              some swappedBorrowIntSlot by exact swappedBorrowEnv_slotAt_a _ _]
          exact ⟨rfl, PartialTyStrengthens.reflex⟩
        · simp [swappedBorrowThenEnv, swappedBorrowJoinEnv,
            swappedBorrowEnv, Env.update, Env.empty, hy, hx, hb, ha]

private theorem swappedBorrowElse_le_join :
    EnvStrengthens swappedBorrowElseEnv swappedBorrowJoinEnv := by
  intro name
  by_cases hy : name = "y"
  · subst hy
    rw [show swappedBorrowElseEnv.slotAt "y" =
        some (swappedBorrowSlot [swappedBorrowA]) by
          exact swappedBorrowEnv_slotAt_y _ _,
      show swappedBorrowJoinEnv.slotAt "y" =
        some (swappedBorrowSlot [swappedBorrowB, swappedBorrowA]) by
          exact swappedBorrowEnv_slotAt_y _ _]
    exact ⟨rfl, PartialTyStrengthens.borrow (by
      intro target htarget
      simp at htarget ⊢
      exact Or.inr htarget)⟩
  · by_cases hx : name = "x"
    · subst hx
      rw [show swappedBorrowElseEnv.slotAt "x" =
          some (swappedBorrowSlot [swappedBorrowB]) by
            exact swappedBorrowEnv_slotAt_x _ _,
        show swappedBorrowJoinEnv.slotAt "x" =
          some (swappedBorrowSlot [swappedBorrowA, swappedBorrowB]) by
            exact swappedBorrowEnv_slotAt_x _ _]
      exact ⟨rfl, PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inr htarget)⟩
    · by_cases hb : name = "b"
      · subst hb
        rw [show swappedBorrowElseEnv.slotAt "b" =
            some swappedBorrowIntSlot by exact swappedBorrowEnv_slotAt_b _ _,
          show swappedBorrowJoinEnv.slotAt "b" =
            some swappedBorrowIntSlot by exact swappedBorrowEnv_slotAt_b _ _]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · by_cases ha : name = "a"
        · subst ha
          rw [show swappedBorrowElseEnv.slotAt "a" =
              some swappedBorrowIntSlot by exact swappedBorrowEnv_slotAt_a _ _,
            show swappedBorrowJoinEnv.slotAt "a" =
              some swappedBorrowIntSlot by exact swappedBorrowEnv_slotAt_a _ _]
          exact ⟨rfl, PartialTyStrengthens.reflex⟩
        · simp [swappedBorrowElseEnv, swappedBorrowJoinEnv,
            swappedBorrowEnv, Env.update, Env.empty, hy, hx, hb, ha]

private theorem swappedBorrowJoin_least {env' : Env}
    (hthen : EnvStrengthens swappedBorrowThenEnv env')
    (helse : EnvStrengthens swappedBorrowElseEnv env') :
    EnvStrengthens swappedBorrowJoinEnv env' := by
  intro name
  by_cases hy : name = "y"
  · subst hy
    rcases EnvStrengthens.slot_forward hthen
        (show swappedBorrowThenEnv.slotAt "y" =
          some (swappedBorrowSlot [swappedBorrowB]) by
          exact swappedBorrowEnv_slotAt_y _ _) with
      ⟨slotB, hslotB, hlife, hstrB⟩
    rcases EnvStrengthens.slot_forward helse
        (show swappedBorrowElseEnv.slotAt "y" =
          some (swappedBorrowSlot [swappedBorrowA]) by
          exact swappedBorrowEnv_slotAt_y _ _) with
      ⟨slotA, hslotA, _hlifeA, hstrA⟩
    have hslotEq : slotA = slotB := Option.some.inj (hslotA.symm.trans hslotB)
    subst hslotEq
    rw [show swappedBorrowJoinEnv.slotAt "y" =
        some (swappedBorrowSlot [swappedBorrowB, swappedBorrowA]) by
        exact swappedBorrowEnv_slotAt_y _ _, hslotA]
    have hjoined :
        PartialTyStrengthens
          (.ty (.borrow true ([swappedBorrowB] ++ [swappedBorrowA])))
          slotA.ty :=
      swappedBorrow_partialTyStrengthens_borrow_append hstrB hstrA
    exact ⟨hlife, by simpa [swappedBorrowSlot] using hjoined⟩
  · by_cases hx : name = "x"
    · subst hx
      rcases EnvStrengthens.slot_forward hthen
          (show swappedBorrowThenEnv.slotAt "x" =
            some (swappedBorrowSlot [swappedBorrowA]) by
            exact swappedBorrowEnv_slotAt_x _ _) with
        ⟨slotA, hslotA, hlife, hstrA⟩
      rcases EnvStrengthens.slot_forward helse
          (show swappedBorrowElseEnv.slotAt "x" =
            some (swappedBorrowSlot [swappedBorrowB]) by
            exact swappedBorrowEnv_slotAt_x _ _) with
        ⟨slotB, hslotB, _hlifeB, hstrB⟩
      have hslotEq : slotB = slotA := Option.some.inj (hslotB.symm.trans hslotA)
      subst hslotEq
      rw [show swappedBorrowJoinEnv.slotAt "x" =
          some (swappedBorrowSlot [swappedBorrowA, swappedBorrowB]) by
          exact swappedBorrowEnv_slotAt_x _ _, hslotB]
      have hjoined :
          PartialTyStrengthens
            (.ty (.borrow true ([swappedBorrowA] ++ [swappedBorrowB])))
            slotB.ty :=
        swappedBorrow_partialTyStrengthens_borrow_append hstrA hstrB
      exact ⟨hlife, by simpa [swappedBorrowSlot] using hjoined⟩
    · by_cases hb : name = "b"
      · subst hb
        rcases EnvStrengthens.slot_forward hthen
            (show swappedBorrowThenEnv.slotAt "b" =
              some swappedBorrowIntSlot by
              exact swappedBorrowEnv_slotAt_b _ _) with
          ⟨slot', hslot', hlife, hstr⟩
        rw [show swappedBorrowJoinEnv.slotAt "b" =
            some swappedBorrowIntSlot by
            exact swappedBorrowEnv_slotAt_b _ _, hslot']
        exact ⟨hlife, hstr⟩
      · by_cases ha : name = "a"
        · subst ha
          rcases EnvStrengthens.slot_forward hthen
              (show swappedBorrowThenEnv.slotAt "a" =
                some swappedBorrowIntSlot by
                exact swappedBorrowEnv_slotAt_a _ _) with
            ⟨slot', hslot', hlife, hstr⟩
          rw [show swappedBorrowJoinEnv.slotAt "a" =
              some swappedBorrowIntSlot by
              exact swappedBorrowEnv_slotAt_a _ _, hslot']
          exact ⟨hlife, hstr⟩
        · have hthenNone : swappedBorrowThenEnv.slotAt name = none :=
            swappedBorrowEnv_slotAt_none _ _ hy hx hb ha
          have hjoinNone : swappedBorrowJoinEnv.slotAt name = none :=
            swappedBorrowEnv_slotAt_none _ _ hy hx hb ha
          have h := hthen name
          rw [hthenNone] at h
          rw [hjoinNone]
          cases hslot : env'.slotAt name with
          | none =>
              trivial
          | some slot =>
              rw [hslot] at h
              cases h

private theorem swappedBorrow_envJoin :
    EnvJoin swappedBorrowThenEnv swappedBorrowElseEnv swappedBorrowJoinEnv := by
  constructor
  · intro env henv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at henv
    rcases henv with rfl | rfl
    · exact swappedBorrowThen_le_join
    · exact swappedBorrowElse_le_join
  · intro env' henv'
    exact swappedBorrowJoin_least (henv' (by simp)) (henv' (by simp))

private theorem swappedBorrowJoin_contained :
    ContainedBorrowsWellFormed swappedBorrowJoinEnv :=
  swappedBorrowEnv_contained [swappedBorrowA, swappedBorrowB]
    [swappedBorrowB, swappedBorrowA] swappedBorrow_ab_good swappedBorrow_ba_good

private theorem swappedBorrowJoin_coherent :
    Coherent swappedBorrowJoinEnv :=
  swappedBorrowEnv_coherent [swappedBorrowA, swappedBorrowB]
    [swappedBorrowB, swappedBorrowA] swappedBorrow_ab_good swappedBorrow_ba_good
    ⟨.int, Lifetime.root, swappedBorrow_targets_ab⟩
    ⟨.int, Lifetime.root, swappedBorrow_targets_ba⟩

private theorem swappedBorrowJoin_linearizable :
    Linearizable swappedBorrowJoinEnv :=
  swappedBorrowEnv_linearizable [swappedBorrowA, swappedBorrowB]
    [swappedBorrowB, swappedBorrowA] swappedBorrow_ab_good swappedBorrow_ba_good

private theorem swappedBorrowJoin_obligations :
    EnvJoin swappedBorrowThenEnv swappedBorrowElseEnv swappedBorrowJoinEnv ∧
    ContainedBorrowsWellFormed swappedBorrowJoinEnv ∧
    Coherent swappedBorrowJoinEnv ∧
    Linearizable swappedBorrowJoinEnv :=
  ⟨swappedBorrow_envJoin, swappedBorrowJoin_contained,
    swappedBorrowJoin_coherent, swappedBorrowJoin_linearizable⟩

def swappedBorrowCondition : Term :=
  .eq (.copy swappedBorrowA) (.copy swappedBorrowB)

private def swappedBorrowEqGhostEnv : Env :=
  swappedBorrowPreIfEnv.update "γ" { ty := .ty .int, lifetime := Lifetime.root }

private theorem swappedBorrowPreIf_not_readProhibited (lv : LVal) :
    ¬ ReadProhibited swappedBorrowPreIfEnv lv := by
  simp [ReadProhibited, EnvContains, swappedBorrowPreIfEnv, swappedBorrowEnv,
    swappedBorrowSlot, swappedBorrowIntSlot, Env.update, Env.empty,
    PathConflicts]
  intro root targets slot hslot hcontains target htarget
  by_cases hy : root = "y"
  · subst hy
    simp at hslot
    subst hslot
    cases hcontains
    simp at htarget
  · by_cases hx : root = "x"
    · subst hx
      simp [hy] at hslot
      subst hslot
      cases hcontains
      simp at htarget
    · by_cases hb : root = "b"
      · subst hb
        simp [hy, hx] at hslot
        subst hslot
        cases hcontains
      · by_cases ha : root = "a"
        · subst ha
          simp [hy, hx, hb] at hslot
          subst hslot
          cases hcontains
        · simp [hy, hx, hb, ha] at hslot

private theorem swappedBorrowEnv_not_writeProhibited_var
    {xTargets yTargets : List LVal} {name : Name}
    (hxTargets : ∀ target, target ∈ xTargets → LVal.base target ≠ name)
    (hyTargets : ∀ target, target ∈ yTargets → LVal.base target ≠ name) :
    ¬ WriteProhibited (swappedBorrowEnv xTargets yTargets) (.var name) := by
  intro hwrite
  have noRead :
      ¬ ReadProhibited (swappedBorrowEnv xTargets yTargets) (.var name) := by
    intro hread
    rcases hread with ⟨root, targets, target, hcontains, htarget, hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hy : root = "y"
    · subst hy
      have hslotTy : slot.ty = .ty (.borrow true yTargets) := by
        simpa [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy with
      | here =>
          exact hyTargets target htarget (by
            simpa [PathConflicts, LVal.base] using hconflict)
    · by_cases hx : root = "x"
      · subst hx
        have hslotTy : slot.ty = .ty (.borrow true xTargets) := by
          simpa [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy with
        | here =>
            exact hxTargets target htarget (by
              simpa [PathConflicts, LVal.base] using hconflict)
      · by_cases hb : root = "b"
        · subst hb
          have hslotTy : slot.ty = .ty .int := by
            simpa [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · by_cases ha : root = "a"
          · subst ha
            have hslotTy : slot.ty = .ty .int := by
              simpa [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
                Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
            rw [hslotTy] at hcontainsTy
            cases hcontainsTy
          · have hnone :
                (swappedBorrowEnv xTargets yTargets).slotAt root = none := by
              simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
                Env.update, Env.empty, hy, hx, hb, ha]
            rw [hslot] at hnone
            cases hnone
  rcases hwrite with hread | himm
  · exact noRead hread
  · rcases himm with ⟨root, targets, target, hcontains, _htarget, _hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hy : root = "y"
    · subst hy
      have hslotTy : slot.ty = .ty (.borrow true yTargets) := by
        simpa [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hx : root = "x"
      · subst hx
        have hslotTy : slot.ty = .ty (.borrow true xTargets) := by
          simpa [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hb : root = "b"
        · subst hb
          have hslotTy : slot.ty = .ty .int := by
            simpa [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · by_cases ha : root = "a"
          · subst ha
            have hslotTy : slot.ty = .ty .int := by
              simpa [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
                Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
            rw [hslotTy] at hcontainsTy
            cases hcontainsTy
          · have hnone :
                (swappedBorrowEnv xTargets yTargets).slotAt root = none := by
              simp [swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
                Env.update, Env.empty, hy, hx, hb, ha]
            rw [hslot] at hnone
            cases hnone

private theorem swappedBorrowEqGhost_b_typing :
    LValTyping swappedBorrowEqGhostEnv swappedBorrowB (.ty .int) Lifetime.root := by
  exact @LValTyping.var swappedBorrowEqGhostEnv "b" swappedBorrowIntSlot (by
    simp [swappedBorrowEqGhostEnv, swappedBorrowPreIfEnv, swappedBorrowEnv,
      swappedBorrowSlot, swappedBorrowIntSlot, Env.update])

private theorem swappedBorrowEqGhost_not_readProhibited (lv : LVal) :
    ¬ ReadProhibited swappedBorrowEqGhostEnv lv := by
  simp [ReadProhibited, EnvContains, swappedBorrowEqGhostEnv,
    swappedBorrowPreIfEnv, swappedBorrowEnv, swappedBorrowSlot,
    swappedBorrowIntSlot, Env.update, Env.empty, PathConflicts]
  intro root targets slot hslot hcontains target htarget
  by_cases hγ : root = "γ"
  · subst hγ
    simp at hslot
    subst hslot
    cases hcontains
  · by_cases hy : root = "y"
    · subst hy
      simp [hγ] at hslot
      subst hslot
      cases hcontains
      simp at htarget
    · by_cases hx : root = "x"
      · subst hx
        simp [hγ, hy] at hslot
        subst hslot
        cases hcontains
        simp at htarget
      · by_cases hb : root = "b"
        · subst hb
          simp [hγ, hy, hx] at hslot
          subst hslot
          cases hcontains
        · by_cases ha : root = "a"
          · subst ha
            simp [hγ, hy, hx, hb] at hslot
            subst hslot
            cases hcontains
          · simp [hγ, hy, hx, hb, ha] at hslot

private theorem swappedBorrowCondition_typing {typing : StoreTyping} :
    TermTyping swappedBorrowPreIfEnv typing Lifetime.root
      swappedBorrowCondition .bool swappedBorrowPreIfEnv := by
  unfold swappedBorrowCondition
  exact TermTyping.eq (ghost := "γ")
    (TermTyping.copy swappedBorrow_a_typing CopyTy.int
      (swappedBorrowPreIf_not_readProhibited swappedBorrowA))
    (by
      simp [Env.fresh, swappedBorrowPreIfEnv, swappedBorrowEnv,
        swappedBorrowSlot, swappedBorrowIntSlot, Env.update, Env.empty])
    (TermTyping.copy swappedBorrowEqGhost_b_typing CopyTy.int
      (swappedBorrowEqGhost_not_readProhibited swappedBorrowB))
    (TermTyping.copy swappedBorrow_b_typing CopyTy.int
      (swappedBorrowPreIf_not_readProhibited swappedBorrowB))
    CopyTy.int
    CopyTy.int
    ShapeCompatible.int

private theorem swappedBorrow_write_x_a :
    EnvWrite 0 swappedBorrowPreIfEnv swappedBorrowX
      (.borrow true [swappedBorrowA]) swappedBorrowThenXEnv := by
  simpa [swappedBorrowThenXEnv, swappedBorrowX, LVal.base,
      swappedBorrowSlot] using
    (@EnvWrite.intro 0 swappedBorrowPreIfEnv swappedBorrowPreIfEnv
      swappedBorrowX (swappedBorrowSlot []) (.borrow true [swappedBorrowA])
      (.ty (.borrow true [swappedBorrowA]))
      (by
        show swappedBorrowPreIfEnv.slotAt "x" = some (swappedBorrowSlot [])
        simp [swappedBorrowPreIfEnv, swappedBorrowEnv, swappedBorrowSlot,
          swappedBorrowIntSlot, Env.update])
      UpdateAtPath.strong)

private theorem swappedBorrow_write_y_b :
    EnvWrite 0 swappedBorrowThenXEnv swappedBorrowY
      (.borrow true [swappedBorrowB]) swappedBorrowThenEnv := by
  have hwrite :
      EnvWrite 0 swappedBorrowThenXEnv swappedBorrowY
        (.borrow true [swappedBorrowB])
        (swappedBorrowThenXEnv.update "y"
          (swappedBorrowSlot [swappedBorrowB])) := by
    simpa [swappedBorrowY, LVal.base, swappedBorrowSlot] using
      (@EnvWrite.intro 0 swappedBorrowThenXEnv swappedBorrowThenXEnv
        swappedBorrowY (swappedBorrowSlot [])
        (.borrow true [swappedBorrowB])
        (.ty (.borrow true [swappedBorrowB]))
        (by
          show swappedBorrowThenXEnv.slotAt "y" = some (swappedBorrowSlot [])
          simp [swappedBorrowThenXEnv_eq, swappedBorrowEnv_slotAt_y])
        UpdateAtPath.strong)
  rw [swappedBorrowThenXEnv_eq, swappedBorrowEnv_update_y] at hwrite
  simpa [swappedBorrowThenXEnv_eq, swappedBorrowThenEnv] using hwrite

private theorem swappedBorrow_write_x_b :
    EnvWrite 0 swappedBorrowPreIfEnv swappedBorrowX
      (.borrow true [swappedBorrowB]) swappedBorrowElseXEnv := by
  simpa [swappedBorrowElseXEnv, swappedBorrowX, LVal.base,
      swappedBorrowSlot] using
    (@EnvWrite.intro 0 swappedBorrowPreIfEnv swappedBorrowPreIfEnv
      swappedBorrowX (swappedBorrowSlot []) (.borrow true [swappedBorrowB])
      (.ty (.borrow true [swappedBorrowB]))
      (by
        show swappedBorrowPreIfEnv.slotAt "x" = some (swappedBorrowSlot [])
        simp [swappedBorrowPreIfEnv, swappedBorrowEnv, swappedBorrowSlot,
          swappedBorrowIntSlot, Env.update])
      UpdateAtPath.strong)

private theorem swappedBorrow_write_y_a :
    EnvWrite 0 swappedBorrowElseXEnv swappedBorrowY
      (.borrow true [swappedBorrowA]) swappedBorrowElseEnv := by
  have hwrite :
      EnvWrite 0 swappedBorrowElseXEnv swappedBorrowY
        (.borrow true [swappedBorrowA])
        (swappedBorrowElseXEnv.update "y"
          (swappedBorrowSlot [swappedBorrowA])) := by
    simpa [swappedBorrowY, LVal.base, swappedBorrowSlot] using
      (@EnvWrite.intro 0 swappedBorrowElseXEnv swappedBorrowElseXEnv
        swappedBorrowY (swappedBorrowSlot [])
        (.borrow true [swappedBorrowA])
        (.ty (.borrow true [swappedBorrowA]))
        (by
          show swappedBorrowElseXEnv.slotAt "y" = some (swappedBorrowSlot [])
          simp [swappedBorrowElseXEnv_eq, swappedBorrowEnv_slotAt_y])
        UpdateAtPath.strong)
  rw [swappedBorrowElseXEnv_eq, swappedBorrowEnv_update_y] at hwrite
  simpa [swappedBorrowElseXEnv_eq, swappedBorrowElseEnv] using hwrite

private theorem swappedBorrow_ranked_x_a :
    ∃ φ, LinearizedBy φ swappedBorrowPreIfEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ swappedBorrowThenXEnv
        (.borrow true [swappedBorrowA]) := by
  refine ⟨swappedBorrowRank, ?linearized, ?below⟩
  · simpa [swappedBorrowPreIfEnv] using
      swappedBorrowEnv_linearizedBy [] [] swappedBorrow_empty_good
        swappedBorrow_empty_good
  · simpa [swappedBorrowThenXEnv_eq] using
      swappedBorrowEnv_rhs_borrow_targets_below
        [swappedBorrowA] [] [swappedBorrowA] "x"
        swappedBorrow_a_good swappedBorrow_empty_good (by
          intro root mutable targets target hcontains htarget _hrhs
          rcases swappedBorrowEnv_borrow_root_facts [swappedBorrowA] []
              hcontains with hroot | hroot
          · exact hroot.1
          · rcases hroot with ⟨rfl, rfl, rfl⟩
            cases htarget)

private theorem swappedBorrow_ranked_y_b :
    ∃ φ, LinearizedBy φ swappedBorrowThenXEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ swappedBorrowThenEnv
        (.borrow true [swappedBorrowB]) := by
  refine ⟨swappedBorrowRank, ?linearized, ?below⟩
  · simpa [swappedBorrowThenXEnv_eq] using
      swappedBorrowEnv_linearizedBy [swappedBorrowA] [] swappedBorrow_a_good
        swappedBorrow_empty_good
  · simpa [swappedBorrowThenEnv] using
      swappedBorrowEnv_rhs_borrow_targets_below
        [swappedBorrowA] [swappedBorrowB] [swappedBorrowB] "y"
        swappedBorrow_a_good swappedBorrow_b_good (by
          intro root mutable targets target hcontains htarget hrhs
          rcases swappedBorrowEnv_borrow_root_facts [swappedBorrowA]
              [swappedBorrowB] hcontains with hroot | hroot
          · rcases hroot with ⟨rfl, rfl, rfl⟩
            simp [swappedBorrowA, swappedBorrowB] at htarget hrhs
            rw [htarget] at hrhs
            simp at hrhs
          · exact hroot.1)

private theorem swappedBorrow_ranked_x_b :
    ∃ φ, LinearizedBy φ swappedBorrowPreIfEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ swappedBorrowElseXEnv
        (.borrow true [swappedBorrowB]) := by
  refine ⟨swappedBorrowRank, ?linearized, ?below⟩
  · simpa [swappedBorrowPreIfEnv] using
      swappedBorrowEnv_linearizedBy [] [] swappedBorrow_empty_good
        swappedBorrow_empty_good
  · simpa [swappedBorrowElseXEnv_eq] using
      swappedBorrowEnv_rhs_borrow_targets_below
        [swappedBorrowB] [] [swappedBorrowB] "x"
        swappedBorrow_b_good swappedBorrow_empty_good (by
          intro root mutable targets target hcontains htarget _hrhs
          rcases swappedBorrowEnv_borrow_root_facts [swappedBorrowB] []
              hcontains with hroot | hroot
          · exact hroot.1
          · rcases hroot with ⟨rfl, rfl, rfl⟩
            cases htarget)

private theorem swappedBorrow_ranked_y_a :
    ∃ φ, LinearizedBy φ swappedBorrowElseXEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ swappedBorrowElseEnv
        (.borrow true [swappedBorrowA]) := by
  refine ⟨swappedBorrowRank, ?linearized, ?below⟩
  · simpa [swappedBorrowElseXEnv_eq] using
      swappedBorrowEnv_linearizedBy [swappedBorrowB] [] swappedBorrow_b_good
        swappedBorrow_empty_good
  · simpa [swappedBorrowElseEnv] using
      swappedBorrowEnv_rhs_borrow_targets_below
        [swappedBorrowB] [swappedBorrowA] [swappedBorrowA] "y"
        swappedBorrow_b_good swappedBorrow_a_good (by
          intro root mutable targets target hcontains htarget hrhs
          rcases swappedBorrowEnv_borrow_root_facts [swappedBorrowB]
              [swappedBorrowA] hcontains with hroot | hroot
          · rcases hroot with ⟨rfl, rfl, rfl⟩
            simp [swappedBorrowA, swappedBorrowB] at htarget hrhs
            rw [htarget] at hrhs
            simp at hrhs
          · exact hroot.1)

private theorem swappedBorrowThenX_contained :
    ContainedBorrowsWellFormed swappedBorrowThenXEnv := by
  simpa [swappedBorrowThenXEnv_eq] using
    swappedBorrowEnv_contained [swappedBorrowA] [] swappedBorrow_a_good
      swappedBorrow_empty_good

private theorem swappedBorrowThen_contained :
    ContainedBorrowsWellFormed swappedBorrowThenEnv :=
  swappedBorrowEnv_contained [swappedBorrowA] [swappedBorrowB]
    swappedBorrow_a_good swappedBorrow_b_good

private theorem swappedBorrowElseX_contained :
    ContainedBorrowsWellFormed swappedBorrowElseXEnv := by
  simpa [swappedBorrowElseXEnv_eq] using
    swappedBorrowEnv_contained [swappedBorrowB] [] swappedBorrow_b_good
      swappedBorrow_empty_good

private theorem swappedBorrowElse_contained :
    ContainedBorrowsWellFormed swappedBorrowElseEnv :=
  swappedBorrowEnv_contained [swappedBorrowB] [swappedBorrowA]
    swappedBorrow_b_good swappedBorrow_a_good

private theorem swappedBorrow_coherent_x_a :
    EnvWriteCoherenceObligations swappedBorrowPreIfEnv swappedBorrowThenXEnv
      "x" := by
  simpa [swappedBorrowPreIfEnv, swappedBorrowThenXEnv_eq] using
    (show EnvWriteCoherenceObligations (swappedBorrowEnv [] [])
        (swappedBorrowEnv [swappedBorrowA] []) "x" from by
      constructor
      · intro lv mutable targets borrowLifetime hbase htyping
        by_cases hy : LVal.base lv = "y"
        · rcases (swappedBorrow_y_root_facts [swappedBorrowA] []
              swappedBorrow_empty_good hy).2 htyping with
            ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨⟨Lifetime.root, swappedBorrow_y_typing⟩, by
            intro targetTy targetLifetime htargets
            cases htargets⟩
        · rcases swappedBorrow_old_root_int [swappedBorrowA] [] hbase hy
              htyping with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy
      · intro lv mutable targets borrowLifetime hbase htyping
        rcases (swappedBorrow_x_root_facts [swappedBorrowA] []
            swappedBorrow_a_good hbase).2 htyping with
          ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨.int, Lifetime.root, swappedBorrow_targets_a⟩)

private theorem swappedBorrow_coherent_y_b :
    EnvWriteCoherenceObligations swappedBorrowThenXEnv swappedBorrowThenEnv
      "y" := by
  simpa [swappedBorrowThenXEnv_eq, swappedBorrowThenEnv] using
    (show EnvWriteCoherenceObligations
        (swappedBorrowEnv [swappedBorrowA] [])
        (swappedBorrowEnv [swappedBorrowA] [swappedBorrowB]) "y" from by
      constructor
      · intro lv mutable targets borrowLifetime hbase htyping
        by_cases hx : LVal.base lv = "x"
        · rcases (swappedBorrow_x_root_facts [swappedBorrowA]
              [swappedBorrowB] swappedBorrow_a_good hx).2 htyping with
            ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨⟨Lifetime.root, swappedBorrow_x_typing⟩, by
            intro targetTy targetLifetime _htargets
            exact ⟨.int, Lifetime.root, swappedBorrow_targets_a⟩⟩
        · rcases swappedBorrow_old_root_int [swappedBorrowA]
              [swappedBorrowB] hx hbase htyping with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy
      · intro lv mutable targets borrowLifetime hbase htyping
        rcases (swappedBorrow_y_root_facts [swappedBorrowA]
            [swappedBorrowB] swappedBorrow_b_good hbase).2 htyping with
          ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨.int, Lifetime.root, swappedBorrow_targets_b⟩)

private theorem swappedBorrow_coherent_x_b :
    EnvWriteCoherenceObligations swappedBorrowPreIfEnv swappedBorrowElseXEnv
      "x" := by
  simpa [swappedBorrowPreIfEnv, swappedBorrowElseXEnv_eq] using
    (show EnvWriteCoherenceObligations (swappedBorrowEnv [] [])
        (swappedBorrowEnv [swappedBorrowB] []) "x" from by
      constructor
      · intro lv mutable targets borrowLifetime hbase htyping
        by_cases hy : LVal.base lv = "y"
        · rcases (swappedBorrow_y_root_facts [swappedBorrowB] []
              swappedBorrow_empty_good hy).2 htyping with
            ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨⟨Lifetime.root, swappedBorrow_y_typing⟩, by
            intro targetTy targetLifetime htargets
            cases htargets⟩
        · rcases swappedBorrow_old_root_int [swappedBorrowB] [] hbase hy
              htyping with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy
      · intro lv mutable targets borrowLifetime hbase htyping
        rcases (swappedBorrow_x_root_facts [swappedBorrowB] []
            swappedBorrow_b_good hbase).2 htyping with
          ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨.int, Lifetime.root, swappedBorrow_targets_b⟩)

private theorem swappedBorrow_coherent_y_a :
    EnvWriteCoherenceObligations swappedBorrowElseXEnv swappedBorrowElseEnv
      "y" := by
  simpa [swappedBorrowElseXEnv_eq, swappedBorrowElseEnv] using
    (show EnvWriteCoherenceObligations
        (swappedBorrowEnv [swappedBorrowB] [])
        (swappedBorrowEnv [swappedBorrowB] [swappedBorrowA]) "y" from by
      constructor
      · intro lv mutable targets borrowLifetime hbase htyping
        by_cases hx : LVal.base lv = "x"
        · rcases (swappedBorrow_x_root_facts [swappedBorrowB]
              [swappedBorrowA] swappedBorrow_b_good hx).2 htyping with
            ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨⟨Lifetime.root, swappedBorrow_x_typing⟩, by
            intro targetTy targetLifetime _htargets
            exact ⟨.int, Lifetime.root, swappedBorrow_targets_b⟩⟩
        · rcases swappedBorrow_old_root_int [swappedBorrowB]
              [swappedBorrowA] hx hbase htyping with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy
      · intro lv mutable targets borrowLifetime hbase htyping
        rcases (swappedBorrow_y_root_facts [swappedBorrowB]
            [swappedBorrowA] swappedBorrow_a_good hbase).2 htyping with
          ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨.int, Lifetime.root, swappedBorrow_targets_a⟩)

private theorem swappedBorrowPreIf_not_writeProhibited_a :
    ¬ WriteProhibited swappedBorrowPreIfEnv swappedBorrowA := by
  simpa [swappedBorrowPreIfEnv, swappedBorrowA] using
    (swappedBorrowEnv_not_writeProhibited_var
      (xTargets := []) (yTargets := []) (name := "a")
      (by intro target htarget; cases htarget)
      (by intro target htarget; cases htarget))

private theorem swappedBorrowPreIf_not_writeProhibited_b :
    ¬ WriteProhibited swappedBorrowPreIfEnv swappedBorrowB := by
  simpa [swappedBorrowPreIfEnv, swappedBorrowB] using
    (swappedBorrowEnv_not_writeProhibited_var
      (xTargets := []) (yTargets := []) (name := "b")
      (by intro target htarget; cases htarget)
      (by intro target htarget; cases htarget))

private theorem swappedBorrowThenX_not_writeProhibited_b :
    ¬ WriteProhibited swappedBorrowThenXEnv swappedBorrowB := by
  simpa [swappedBorrowThenXEnv_eq, swappedBorrowB] using
    (swappedBorrowEnv_not_writeProhibited_var
      (xTargets := [swappedBorrowA]) (yTargets := []) (name := "b")
      (by
        intro target htarget
        simp [swappedBorrowA] at htarget
        subst target
        simp [LVal.base])
      (by intro target htarget; cases htarget))

private theorem swappedBorrowElseX_not_writeProhibited_a :
    ¬ WriteProhibited swappedBorrowElseXEnv swappedBorrowA := by
  simpa [swappedBorrowElseXEnv_eq, swappedBorrowA] using
    (swappedBorrowEnv_not_writeProhibited_var
      (xTargets := [swappedBorrowB]) (yTargets := []) (name := "a")
      (by
        intro target htarget
        simp [swappedBorrowB] at htarget
        subst target
        simp [LVal.base])
      (by intro target htarget; cases htarget))

private theorem swappedBorrowThenX_not_writeProhibited_x :
    ¬ WriteProhibited swappedBorrowThenXEnv swappedBorrowX := by
  simpa [swappedBorrowThenXEnv_eq, swappedBorrowX] using
    (swappedBorrowEnv_not_writeProhibited_var
      (xTargets := [swappedBorrowA]) (yTargets := []) (name := "x")
      (by
        intro target htarget
        simp [swappedBorrowA] at htarget
        subst target
        simp [LVal.base])
      (by intro target htarget; cases htarget))

private theorem swappedBorrowElseX_not_writeProhibited_x :
    ¬ WriteProhibited swappedBorrowElseXEnv swappedBorrowX := by
  simpa [swappedBorrowElseXEnv_eq, swappedBorrowX] using
    (swappedBorrowEnv_not_writeProhibited_var
      (xTargets := [swappedBorrowB]) (yTargets := []) (name := "x")
      (by
        intro target htarget
        simp [swappedBorrowB] at htarget
        subst target
        simp [LVal.base])
      (by intro target htarget; cases htarget))

private theorem swappedBorrowThen_not_writeProhibited_y :
    ¬ WriteProhibited swappedBorrowThenEnv swappedBorrowY := by
  simpa [swappedBorrowThenEnv, swappedBorrowY] using
    (swappedBorrowEnv_not_writeProhibited_var
      (xTargets := [swappedBorrowA]) (yTargets := [swappedBorrowB])
      (name := "y")
      (by
        intro target htarget
        simp [swappedBorrowA] at htarget
        subst target
        simp [LVal.base])
      (by
        intro target htarget
        simp [swappedBorrowB] at htarget
        subst target
        simp [LVal.base]))

private theorem swappedBorrowElse_not_writeProhibited_y :
    ¬ WriteProhibited swappedBorrowElseEnv swappedBorrowY := by
  simpa [swappedBorrowElseEnv, swappedBorrowY] using
    (swappedBorrowEnv_not_writeProhibited_var
      (xTargets := [swappedBorrowB]) (yTargets := [swappedBorrowA])
      (name := "y")
      (by
        intro target htarget
        simp [swappedBorrowB] at htarget
        subst target
        simp [LVal.base])
      (by
        intro target htarget
        simp [swappedBorrowA] at htarget
        subst target
        simp [LVal.base]))

private theorem swappedBorrow_assign_x_a_typing {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping swappedBorrowPreIfEnv typing lifetime
      (.assign swappedBorrowX (.borrow true swappedBorrowA)) .unit
      swappedBorrowThenXEnv := by
  exact TermTyping.assign
    swappedBorrow_x_typing
    (TermTyping.mutBorrow swappedBorrow_a_typing swappedBorrow_a_mutable
      swappedBorrowPreIf_not_writeProhibited_a)
    (by trivial)
    swappedBorrow_x_typing
    (swappedBorrow_shape_borrow swappedBorrow_empty_good swappedBorrow_a_good)
    (swappedBorrow_borrow_wellFormed swappedBorrow_a_good)
    swappedBorrow_write_x_a
    swappedBorrow_ranked_x_a
    swappedBorrow_coherent_x_a
    swappedBorrowThenX_contained
    swappedBorrowThenX_not_writeProhibited_x

private theorem swappedBorrow_assign_y_b_typing {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping swappedBorrowThenXEnv typing lifetime
      (.assign swappedBorrowY (.borrow true swappedBorrowB)) .unit
      swappedBorrowThenEnv := by
  have hyTyping :
      LValTyping swappedBorrowThenXEnv swappedBorrowY
        (.ty (.borrow true [])) Lifetime.root := by
    simpa [swappedBorrowThenXEnv_eq] using
      (swappedBorrow_y_typing :
        LValTyping (swappedBorrowEnv [swappedBorrowA] []) swappedBorrowY
          (.ty (.borrow true [])) Lifetime.root)
  have hbTyping :
      LValTyping swappedBorrowThenXEnv swappedBorrowB (.ty .int)
        Lifetime.root := by
    simpa [swappedBorrowThenXEnv_eq] using
      (swappedBorrow_b_typing :
        LValTyping (swappedBorrowEnv [swappedBorrowA] []) swappedBorrowB
          (.ty .int) Lifetime.root)
  have hbMutable : Mutable swappedBorrowThenXEnv swappedBorrowB := by
    simpa [swappedBorrowThenXEnv_eq] using
      (swappedBorrow_b_mutable :
        Mutable (swappedBorrowEnv [swappedBorrowA] []) swappedBorrowB)
  exact TermTyping.assign
    hyTyping
    (TermTyping.mutBorrow hbTyping hbMutable
      swappedBorrowThenX_not_writeProhibited_b)
    (by trivial)
    hyTyping
    (by
      simpa [swappedBorrowThenXEnv_eq] using
        (swappedBorrow_shape_borrow
          (xTargets := [swappedBorrowA]) (yTargets := [])
          swappedBorrow_empty_good swappedBorrow_b_good))
    (by
      simpa [swappedBorrowThenXEnv_eq] using
        (swappedBorrow_borrow_wellFormed
          (xTargets := [swappedBorrowA]) (yTargets := [])
          swappedBorrow_b_good))
    swappedBorrow_write_y_b
    swappedBorrow_ranked_y_b
    swappedBorrow_coherent_y_b
    swappedBorrowThen_contained
    swappedBorrowThen_not_writeProhibited_y

private theorem swappedBorrow_assign_x_b_typing {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping swappedBorrowPreIfEnv typing lifetime
      (.assign swappedBorrowX (.borrow true swappedBorrowB)) .unit
      swappedBorrowElseXEnv := by
  exact TermTyping.assign
    swappedBorrow_x_typing
    (TermTyping.mutBorrow swappedBorrow_b_typing swappedBorrow_b_mutable
      swappedBorrowPreIf_not_writeProhibited_b)
    (by trivial)
    swappedBorrow_x_typing
    (swappedBorrow_shape_borrow swappedBorrow_empty_good swappedBorrow_b_good)
    (swappedBorrow_borrow_wellFormed swappedBorrow_b_good)
    swappedBorrow_write_x_b
    swappedBorrow_ranked_x_b
    swappedBorrow_coherent_x_b
    swappedBorrowElseX_contained
    swappedBorrowElseX_not_writeProhibited_x

private theorem swappedBorrow_assign_y_a_typing {typing : StoreTyping}
    {lifetime : Lifetime} :
    TermTyping swappedBorrowElseXEnv typing lifetime
      (.assign swappedBorrowY (.borrow true swappedBorrowA)) .unit
      swappedBorrowElseEnv := by
  have hyTyping :
      LValTyping swappedBorrowElseXEnv swappedBorrowY
        (.ty (.borrow true [])) Lifetime.root := by
    simpa [swappedBorrowElseXEnv_eq] using
      (swappedBorrow_y_typing :
        LValTyping (swappedBorrowEnv [swappedBorrowB] []) swappedBorrowY
          (.ty (.borrow true [])) Lifetime.root)
  have haTyping :
      LValTyping swappedBorrowElseXEnv swappedBorrowA (.ty .int)
        Lifetime.root := by
    simpa [swappedBorrowElseXEnv_eq] using
      (swappedBorrow_a_typing :
        LValTyping (swappedBorrowEnv [swappedBorrowB] []) swappedBorrowA
          (.ty .int) Lifetime.root)
  have haMutable : Mutable swappedBorrowElseXEnv swappedBorrowA := by
    simpa [swappedBorrowElseXEnv_eq] using
      (swappedBorrow_a_mutable :
        Mutable (swappedBorrowEnv [swappedBorrowB] []) swappedBorrowA)
  exact TermTyping.assign
    hyTyping
    (TermTyping.mutBorrow haTyping haMutable
      swappedBorrowElseX_not_writeProhibited_a)
    (by trivial)
    hyTyping
    (by
      simpa [swappedBorrowElseXEnv_eq] using
        (swappedBorrow_shape_borrow
          (xTargets := [swappedBorrowB]) (yTargets := [])
          swappedBorrow_empty_good swappedBorrow_a_good))
    (by
      simpa [swappedBorrowElseXEnv_eq] using
        (swappedBorrow_borrow_wellFormed
          (xTargets := [swappedBorrowB]) (yTargets := [])
          swappedBorrow_a_good))
    swappedBorrow_write_y_a
    swappedBorrow_ranked_y_a
    swappedBorrow_coherent_y_a
    swappedBorrowElse_contained
    swappedBorrowElse_not_writeProhibited_y

def swappedBorrowThenBranch : Term :=
  .block [0]
    [ .assign swappedBorrowX (.borrow true swappedBorrowA)
    , .assign swappedBorrowY (.borrow true swappedBorrowB)
    ]

def swappedBorrowElseBranch : Term :=
  .block [0]
    [ .assign swappedBorrowX (.borrow true swappedBorrowB)
    , .assign swappedBorrowY (.borrow true swappedBorrowA)
    ]

def swappedBorrowIf : Term :=
  .ite swappedBorrowCondition swappedBorrowThenBranch swappedBorrowElseBranch

private theorem swappedBorrowThenBranch_typing {typing : StoreTyping} :
    TermTyping swappedBorrowPreIfEnv typing Lifetime.root
      swappedBorrowThenBranch .unit swappedBorrowThenEnv := by
  unfold swappedBorrowThenBranch
  exact TermTyping.block
    (⟨0, rfl⟩ : LifetimeChild Lifetime.root ([0] : Lifetime))
    (TermListTyping.cons
      (swappedBorrow_assign_x_a_typing (typing := typing)
        (lifetime := ([0] : Lifetime)))
      (TermListTyping.singleton
        (swappedBorrow_assign_y_b_typing (typing := typing)
          (lifetime := ([0] : Lifetime)))))
    WellFormedTy.unit
    (by
      simpa [swappedBorrowThenEnv] using
        (swappedBorrowEnv_drop_body_lifetime [swappedBorrowA]
          [swappedBorrowB]).symm)

private theorem swappedBorrowElseBranch_typing {typing : StoreTyping} :
    TermTyping swappedBorrowPreIfEnv typing Lifetime.root
      swappedBorrowElseBranch .unit swappedBorrowElseEnv := by
  unfold swappedBorrowElseBranch
  exact TermTyping.block
    (⟨0, rfl⟩ : LifetimeChild Lifetime.root ([0] : Lifetime))
    (TermListTyping.cons
      (swappedBorrow_assign_x_b_typing (typing := typing)
        (lifetime := ([0] : Lifetime)))
      (TermListTyping.singleton
        (swappedBorrow_assign_y_a_typing (typing := typing)
          (lifetime := ([0] : Lifetime)))))
    WellFormedTy.unit
    (by
      simpa [swappedBorrowElseEnv] using
        (swappedBorrowEnv_drop_body_lifetime [swappedBorrowB]
          [swappedBorrowA]).symm)

/--
The current `T-If` rule can type this conditional from the initial environment,
with no global borrow-safety premise for the joined environment.
-/
theorem swappedBorrowIf_typing_from_branch_derivations
    {typing : StoreTyping} :
    TermTyping swappedBorrowPreIfEnv typing Lifetime.root
      swappedBorrowIf .unit swappedBorrowJoinEnv := by
  unfold swappedBorrowIf
  have hthenShape : EnvJoinSameShape swappedBorrowThenEnv swappedBorrowJoinEnv :=
    swappedBorrowEnv_sameShape
  have helseShape : EnvJoinSameShape swappedBorrowElseEnv swappedBorrowJoinEnv :=
    swappedBorrowEnv_sameShape
  exact TermTyping.ite
    swappedBorrowCondition_typing
    swappedBorrowThenBranch_typing
    swappedBorrowElseBranch_typing
    (PartialTyJoin.self (.ty .unit))
    swappedBorrowJoin_obligations.1
    hthenShape
    helseShape
    WellFormedTy.unit
    swappedBorrowJoin_obligations.2.1
    swappedBorrowJoin_obligations.2.2.1
    swappedBorrowJoin_obligations.2.2.2
    (by
      constructor
      · intro _targetsMutable _mutable _targetsOther _x _targetMutable
          _targetOther hcontains _hborrow _htargetMutable _htargetOther
          _hconflict
        cases hcontains
      · intro _x _targetsMutable _mutable _targetsOther _targetMutable
          _targetOther _hborrow hcontains _htargetMutable _htargetOther
          _hconflict
        cases hcontains)

/-- Unrelated direct root assignments are no longer blocked by the crossed join. -/
theorem swappedBorrowJoin_root_assignment_frame_safe :
    AssignmentBorrowSafety swappedBorrowJoinEnv (.var "c") := by
  trivial

theorem swappedBorrowJoin_deref_x_assignment_frame_not_safe :
    ¬ AssignmentBorrowSafety swappedBorrowJoinEnv (.deref swappedBorrowX) := by
  intro hsafe
  have hroot : BorrowSafeRoot swappedBorrowJoinEnv "x" := by
    exact hsafe "x" (by
      simpa [swappedBorrowX, LVal.base] using
        (BorrowAuthorityGuard.base :
          BorrowAuthorityGuard swappedBorrowJoinEnv "x" "x"))
  have hx : swappedBorrowJoinEnv ⊢ "x" ↝
      (.borrow true [swappedBorrowA, swappedBorrowB]) := by
    refine ⟨swappedBorrowSlot [swappedBorrowA, swappedBorrowB], ?_,
      PartialTyContains.here⟩
    simp [swappedBorrowJoinEnv, swappedBorrowEnv, swappedBorrowSlot,
      swappedBorrowIntSlot, Env.update]
  have hy : swappedBorrowJoinEnv ⊢ "y" ↝
      (.borrow true [swappedBorrowB, swappedBorrowA]) := by
    refine ⟨swappedBorrowSlot [swappedBorrowB, swappedBorrowA], ?_,
      PartialTyContains.here⟩
    simp [swappedBorrowJoinEnv, swappedBorrowEnv, swappedBorrowSlot,
      swappedBorrowIntSlot, Env.update]
  have hxy : "x" = "y" :=
    hroot "y" true [swappedBorrowA, swappedBorrowB]
      [swappedBorrowB, swappedBorrowA] swappedBorrowA swappedBorrowA
      hx hy (by simp) (by simp) (by simp [PathConflicts, swappedBorrowA])
  contradiction

def swappedBorrowJoinWithPEnv : Env :=
  (swappedBorrowJoinEnv.update "c" swappedBorrowIntSlot).update
    "p" (swappedBorrowSlot [swappedBorrowC])

theorem swappedBorrowJoinWithP_p_targets {targets : List LVal} :
    swappedBorrowJoinWithPEnv ⊢ "p" ↝ (.borrow true targets) →
    targets = [swappedBorrowC] := by
  rintro ⟨slot, hslot, hcontains⟩
  have hslotTy : slot.ty = .ty (.borrow true [swappedBorrowC]) := by
    simpa [swappedBorrowJoinWithPEnv, swappedBorrowSlot, Env.update] using
      (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
  rw [hslotTy] at hcontains
  cases hcontains
  rfl

theorem swappedBorrowJoinWithP_c_no_mut {targets : List LVal} :
    ¬ swappedBorrowJoinWithPEnv ⊢ "c" ↝ (.borrow true targets) := by
  rintro ⟨slot, hslot, hcontains⟩
  have hslotTy : slot.ty = .ty .int := by
    simpa [swappedBorrowJoinWithPEnv, swappedBorrowJoinEnv, swappedBorrowEnv,
      swappedBorrowSlot, swappedBorrowIntSlot, Env.update] using
      (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
  rw [hslotTy] at hcontains
  cases hcontains

theorem swappedBorrowJoinWithP_guard_p_or_c {root : Name} :
    BorrowAuthorityGuard swappedBorrowJoinWithPEnv "p" root →
    root = "p" ∨ root = "c" := by
  intro hguard
  induction hguard with
  | base =>
      exact Or.inl rfl
  | step hcontainer hnode hmem ih =>
      rcases ih with hcontainerRoot | hcontainerRoot
      · subst hcontainerRoot
        have htargets := swappedBorrowJoinWithP_p_targets hnode
        subst htargets
        simp [swappedBorrowC] at hmem
        right
        simpa [LVal.base] using congrArg LVal.base hmem
      · subst hcontainerRoot
        exact False.elim (swappedBorrowJoinWithP_c_no_mut hnode)

theorem swappedBorrowJoinWithP_p_borrowSafeRoot :
    BorrowSafeRoot swappedBorrowJoinWithPEnv "p" := by
  intro y mutable targetsMutable targetsOther targetMutable targetOther
    hp hother htargetMutable htargetOther hconflict
  have htargetsMutable := swappedBorrowJoinWithP_p_targets hp
  subst htargetsMutable
  simp [swappedBorrowC] at htargetMutable
  subst htargetMutable
  by_cases hyp : y = "p"
  · exact hyp.symm
  exfalso
  rcases hother with ⟨slot, hslot, hcontains⟩
  by_cases hy : y = "y"
  · subst hy
    have hslotTy : slot.ty =
        .ty (.borrow true [swappedBorrowB, swappedBorrowA]) := by
      simpa [swappedBorrowJoinWithPEnv, swappedBorrowJoinEnv, swappedBorrowEnv,
        swappedBorrowSlot, swappedBorrowIntSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hcontains
    cases hcontains with
    | here =>
        simp [swappedBorrowB, swappedBorrowA] at htargetOther
        rcases htargetOther with htargetOther | htargetOther
        · subst htargetOther
          simp [PathConflicts, LVal.base] at hconflict
        · subst htargetOther
          simp [PathConflicts, LVal.base] at hconflict
  · by_cases hx : y = "x"
    · subst hx
      have hslotTy : slot.ty =
          .ty (.borrow true [swappedBorrowA, swappedBorrowB]) := by
        simpa [swappedBorrowJoinWithPEnv, swappedBorrowJoinEnv, swappedBorrowEnv,
          swappedBorrowSlot, swappedBorrowIntSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontains
      cases hcontains with
      | here =>
          simp [swappedBorrowA, swappedBorrowB] at htargetOther
          rcases htargetOther with htargetOther | htargetOther
          · subst htargetOther
            simp [PathConflicts, LVal.base] at hconflict
          · subst htargetOther
            simp [PathConflicts, LVal.base] at hconflict
    · by_cases hc : y = "c"
      · subst hc
        have hslotTy : slot.ty = .ty .int := by
          simpa [swappedBorrowJoinWithPEnv, swappedBorrowJoinEnv, swappedBorrowEnv,
            swappedBorrowSlot, swappedBorrowIntSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontains
        cases hcontains
      · by_cases hb : y = "b"
        · subst hb
          have hslotTy : slot.ty = .ty .int := by
            simpa [swappedBorrowJoinWithPEnv, swappedBorrowJoinEnv, swappedBorrowEnv,
              swappedBorrowSlot, swappedBorrowIntSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontains
          cases hcontains
        · by_cases ha : y = "a"
          · subst ha
            have hslotTy : slot.ty = .ty .int := by
              simpa [swappedBorrowJoinWithPEnv, swappedBorrowJoinEnv,
                swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
                Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
            rw [hslotTy] at hcontains
            cases hcontains
          · have hnone : swappedBorrowJoinWithPEnv.slotAt y = none := by
              simp [swappedBorrowJoinWithPEnv, swappedBorrowJoinEnv,
                swappedBorrowEnv, swappedBorrowSlot, swappedBorrowIntSlot,
                Env.update, Env.empty, hyp, hy, hx, hc, hb, ha]
            rw [hslot] at hnone
            cases hnone

theorem swappedBorrowJoinWithP_c_borrowSafeRoot :
    BorrowSafeRoot swappedBorrowJoinWithPEnv "c" := by
  intro y mutable targetsMutable targetsOther targetMutable targetOther
    hmutable _hother _htargetMutable _htargetOther _hconflict
  exact False.elim (swappedBorrowJoinWithP_c_no_mut hmutable)

/-- An unrelated dereference assignment is not blocked by the crossed `x/y` join. -/
theorem swappedBorrowJoin_unrelated_deref_assignment_frame_safe :
    AssignmentBorrowSafety swappedBorrowJoinWithPEnv (.deref swappedBorrowP) := by
  intro root hguard
  rcases swappedBorrowJoinWithP_guard_p_or_c (by
      simpa [swappedBorrowP, LVal.base] using hguard) with hroot | hroot
  · subst hroot
    exact swappedBorrowJoinWithP_p_borrowSafeRoot
  · subst hroot
    exact swappedBorrowJoinWithP_c_borrowSafeRoot

end Paper
end LwRust
