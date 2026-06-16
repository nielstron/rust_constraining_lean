import LwRust.Paper.Soundness.InitialStates

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
`x : &mut [a, b]` and `y : &mut [b, a]`.  That environment is intentionally not
`BorrowSafeEnv`, so this file witnesses the kind of `T-If` join that the old
borrow-safe premise would reject.
-/

namespace LwRust
namespace Paper

open Core

def swappedBorrowA : LVal := .var "a"
def swappedBorrowB : LVal := .var "b"
def swappedBorrowX : LVal := .var "x"
def swappedBorrowY : LVal := .var "y"

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
join obligations.  Notice that there is no `BorrowSafeEnv swappedBorrowJoinEnv`
premise here; the theorem below proves that such a premise would be impossible.
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
    (hthenShape : EnvJoinSameShape swappedBorrowThenEnv swappedBorrowJoinEnv)
    (helseShape : EnvJoinSameShape swappedBorrowElseEnv swappedBorrowJoinEnv)
    (hcontained : ContainedBorrowsWellFormed swappedBorrowJoinEnv)
    (hcoherent : Coherent swappedBorrowJoinEnv)
    (hlinear : Linearizable swappedBorrowJoinEnv) :
    TermTyping swappedBorrowPreIfEnv typing Lifetime.root
      swappedBorrowIf .unit swappedBorrowJoinEnv := by
  unfold swappedBorrowIf
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
    (tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit)

theorem swappedBorrowJoinEnv_not_borrowSafe :
    ¬ BorrowSafeEnv swappedBorrowJoinEnv := by
  intro hsafe
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
    hsafe "x" "y" true [swappedBorrowA, swappedBorrowB]
      [swappedBorrowB, swappedBorrowA] swappedBorrowA swappedBorrowA
      hx hy (by simp) (by simp) (by simp [PathConflicts, swappedBorrowA])
  contradiction

theorem swappedBorrowJoin_old_TIf_borrowSafe_premise_impossible :
    ¬ BorrowSafeEnv swappedBorrowJoinEnv :=
  swappedBorrowJoinEnv_not_borrowSafe

/-- Unrelated direct root assignments are no longer blocked by the crossed join. -/
theorem swappedBorrowJoin_root_assignment_frame_safe :
    AssignmentBorrowSafety swappedBorrowJoinEnv (.var "c") := by
  trivial

/--
Dereference assignments still need the old global witness.  This is the part
that remains conservative relative to rustc after a path-insensitive join.
-/
theorem swappedBorrowJoin_deref_assignment_frame_safe_iff :
    AssignmentBorrowSafety swappedBorrowJoinEnv (.deref swappedBorrowX) ↔
      BorrowSafeEnv swappedBorrowJoinEnv :=
  Iff.rfl

end Paper
end LwRust
