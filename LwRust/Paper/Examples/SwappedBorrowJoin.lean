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

def swappedBorrowElseEnv : Env :=
  swappedBorrowEnv [swappedBorrowB] [swappedBorrowA]

def swappedBorrowJoinEnv : Env :=
  swappedBorrowEnv [swappedBorrowA, swappedBorrowB]
    [swappedBorrowB, swappedBorrowA]

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

def swappedBorrowCondition : Term :=
  .eq (.copy swappedBorrowA) (.copy swappedBorrowB)

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

/--
The current `T-If` rule can type this conditional from the usual branch and
join obligations, with no global borrow-safety premise for the joined
environment.
-/
theorem swappedBorrowIf_typing_from_branch_derivations
    {typing : StoreTyping}
    (hcondition :
      TermTyping swappedBorrowPreIfEnv typing Lifetime.root
        swappedBorrowCondition .bool swappedBorrowPreIfEnv)
    (hthen :
      TermTyping swappedBorrowPreIfEnv typing Lifetime.root
        swappedBorrowThenBranch .unit swappedBorrowThenEnv)
    (helse :
      TermTyping swappedBorrowPreIfEnv typing Lifetime.root
        swappedBorrowElseBranch .unit swappedBorrowElseEnv)
    (hjoin : EnvJoin swappedBorrowThenEnv swappedBorrowElseEnv
      swappedBorrowJoinEnv)
    (hcontained : ContainedBorrowsWellFormed swappedBorrowJoinEnv)
    (hcoherent : Coherent swappedBorrowJoinEnv)
    (hlinear : Linearizable swappedBorrowJoinEnv) :
    TermTyping swappedBorrowPreIfEnv typing Lifetime.root
      swappedBorrowIf .unit swappedBorrowJoinEnv := by
  unfold swappedBorrowIf
  have hthenShape : EnvJoinSameShape swappedBorrowThenEnv swappedBorrowJoinEnv :=
    swappedBorrowEnv_sameShape
  have helseShape : EnvJoinSameShape swappedBorrowElseEnv swappedBorrowJoinEnv :=
    swappedBorrowEnv_sameShape
  exact TermTyping.ite
    hcondition
    hthen
    helse
    (PartialTyJoin.self (.ty .unit))
    hjoin
    hthenShape
    helseShape
    WellFormedTy.unit
    hcontained
    hcoherent
    hlinear
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
