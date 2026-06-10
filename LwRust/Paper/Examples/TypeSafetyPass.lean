import LwRust.Paper.Soundness.InitialStates

/-!
Build-checked accepted paper-style examples.

Each `*_typeSafety` theorem invokes the empty-initial form of Theorem 4.12:
from a typing derivation, the program reduces to a terminal value whose final
state is safe.
-/

namespace LwRust
namespace Paper

open Core

/--
Accepted scalar comparison example: two copyable integer values can be compared,
and Theorem 4.12 gives terminal-state safety.
-/
def scalarCopyComparison : Term :=
  .eq (.val (.int 1)) (.val (.int 1))

theorem scalarCopyComparison_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root
      scalarCopyComparison .bool Env.empty := by
  unfold scalarCopyComparison
  exact TermTyping.eq
    (TermTyping.const ValueTyping.int)
    (TermTyping.const ValueTyping.int)
    CopyTy.int
    CopyTy.int
    ShapeCompatible.int

theorem scalarCopyComparison_typeSafety :
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty Lifetime.root scalarCopyComparison finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue Env.empty .bool :=
  emptyInitial_typeAndBorrowSafety_total scalarCopyComparison_typing

/--
Accepted `if/else` example for the control-flow extension: both branches return
the same borrow-free type, and the joined environment is empty and borrow safe.
-/
def ifThenElseInt : Term :=
  .ite (.val (.bool true)) (.val (.int 1)) (.val (.int 2))

theorem ifThenElseInt_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root
      ifThenElseInt .int Env.empty := by
  unfold ifThenElseInt
  refine TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    (TermTyping.const ValueTyping.int)
    (TermTyping.const ValueTyping.int)
    (PartialTyJoin.self (.ty .int))
    ?join ?leftShape ?rightShape
    WellFormedTy.int
    containedBorrowsWellFormed_empty
    coherent_empty
    linearizable_empty
    borrowSafeEnv_empty
    (tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_int)
  · simp [EnvJoin, IsLUB, IsLeast, upperBounds, lowerBounds]
  · intro x branchSlot joinSlot hbranch
    simp [Env.empty] at hbranch
  · intro x branchSlot joinSlot hbranch
    simp [Env.empty] at hbranch

theorem ifThenElseInt_typeSafety :
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty Lifetime.root ifThenElseInt finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue Env.empty .int :=
  emptyInitial_typeAndBorrowSafety_total ifThenElseInt_typing

/--
Accepted `if/else` example with a nontrivial boolean guard.  The conditional
still joins to the empty borrow-safe environment.
-/
def ifEqThenElseInt : Term :=
  .ite scalarCopyComparison (.val (.int 1)) (.val (.int 2))

theorem ifEqThenElseInt_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root
      ifEqThenElseInt .int Env.empty := by
  unfold ifEqThenElseInt
  refine TermTyping.ite
    scalarCopyComparison_typing
    (TermTyping.const ValueTyping.int)
    (TermTyping.const ValueTyping.int)
    (PartialTyJoin.self (.ty .int))
    ?join ?leftShape ?rightShape
    WellFormedTy.int
    containedBorrowsWellFormed_empty
    coherent_empty
    linearizable_empty
    borrowSafeEnv_empty
    (tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_int)
  · simp [EnvJoin, IsLUB, IsLeast, upperBounds, lowerBounds]
  · intro x branchSlot joinSlot hbranch
    simp [Env.empty] at hbranch
  · intro x branchSlot joinSlot hbranch
    simp [Env.empty] at hbranch

theorem ifEqThenElseInt_typeSafety :
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty Lifetime.root ifEqThenElseInt finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue Env.empty .int :=
  emptyInitial_typeAndBorrowSafety_total ifEqThenElseInt_typing

/--
Accepted `if/else` with nontrivial pointer effects in the branches.

The starting environment contains `x : int`, `y : int`, and `p : &mut x`.
The guard compares through the pointer with `*p == 1`.  The true branch
retargets the pointer with `p = &mut y`; the false branch writes through the
pointer with `*p = 1`.  Since `x` and `y` have compatible shape, the branch
environments join to `p : &mut [y, x]`.
-/
def pointerIfXSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def pointerIfYSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def pointerIfPXSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "x"]), lifetime := Lifetime.root }

def pointerIfPYSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "y"]), lifetime := Lifetime.root }

def pointerIfJoinPSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "y", .var "x"]), lifetime := Lifetime.root }

def pointerIfEnv : Env :=
  ((Env.empty.update "x" pointerIfXSlot).update "y" pointerIfYSlot).update
    "p" pointerIfPXSlot

def pointerIfRetargetEnv : Env :=
  pointerIfEnv.update "p" pointerIfPYSlot

def pointerIfWriteEnv : Env :=
  (pointerIfEnv.update "x" pointerIfXSlot).update "p" pointerIfPXSlot

def pointerIfJoinEnv : Env :=
  ((Env.empty.update "x" pointerIfXSlot).update "y" pointerIfYSlot).update
    "p" pointerIfJoinPSlot

def pointerRetargetBranch : Term :=
  .assign (.var "p") (.borrow true (.var "y"))

def pointerWriteBranch : Term :=
  .assign (.deref (.var "p")) (.val (.int 1))

def ifPointerAssignment : Term :=
  .ite (.eq (.copy (.deref (.var "p"))) (.val (.int 1)))
    pointerRetargetBranch pointerWriteBranch

theorem pointerIf_x_typing :
    LValTyping pointerIfEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfEnv "x" pointerIfXSlot (by
    simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
      Env.update])

theorem pointerIf_y_typing :
    LValTyping pointerIfEnv (.var "y") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfEnv "y" pointerIfYSlot (by
    simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update])

theorem pointerIf_p_typing :
    LValTyping pointerIfEnv (.var "p")
      (.ty (.borrow true [.var "x"])) Lifetime.root := by
  exact @LValTyping.var pointerIfEnv "p" pointerIfPXSlot (by
    simp [pointerIfEnv, pointerIfPXSlot, Env.update])

theorem pointerIf_deref_p_typing :
    LValTyping pointerIfEnv (.deref (.var "p")) (.ty .int) Lifetime.root := by
  exact LValTyping.borrow pointerIf_p_typing
    (LValTargetsTyping.singleton pointerIf_x_typing)

theorem pointerIf_not_readProhibited_deref_p :
    ¬ ReadProhibited pointerIfEnv (.deref (.var "p")) := by
  intro hread
  rcases hread with ⟨root, targets, target, hcontains, htarget, hconflict⟩
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hroot : root = "p"
  · subst hroot
    have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
      simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hcontainsTy
    cases hcontainsTy with
    | here =>
        simp at htarget
        subst htarget
        simp [PathConflicts, LVal.base] at hconflict
  · by_cases hrootY : root = "y"
    · subst hrootY
      have hslotTy : slot.ty = .ty .int := by
        simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hrootX : root = "x"
      · subst hrootX
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · have hnone : pointerIfEnv.slotAt root = none := by
          simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update, Env.empty, hroot, hrootY, hrootX]
        rw [hslot] at hnone
        cases hnone

theorem pointerIfCondition_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      (.eq (.copy (.deref (.var "p"))) (.val (.int 1))) .bool pointerIfEnv := by
  exact TermTyping.eq
    (TermTyping.copy pointerIf_deref_p_typing CopyTy.int
      pointerIf_not_readProhibited_deref_p)
    (TermTyping.const ValueTyping.int)
    CopyTy.int
    CopyTy.int
    ShapeCompatible.int

theorem pointerIf_not_writeProhibited_y :
    ¬ WriteProhibited pointerIfEnv (.var "y") := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨root, targets, target, hcontains, htarget, hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
        simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy with
      | here =>
          simp at htarget
          subst htarget
          simp [PathConflicts, LVal.base] at hconflict
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfEnv.slotAt root = none := by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone
  · rcases himm with ⟨root, targets, target, hcontains, htarget, hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
        simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfEnv.slotAt root = none := by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone

theorem pointerIf_y_mutable : Mutable pointerIfEnv (.var "y") :=
  @Mutable.var pointerIfEnv "y" pointerIfYSlot
    (by simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update])

theorem pointerIfRetarget_y_typing :
    LValTyping pointerIfRetargetEnv (.var "y") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfRetargetEnv "y" pointerIfYSlot (by
    simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot, pointerIfPYSlot,
      Env.update])

theorem pointerIfRetarget_p_typing :
    LValTyping pointerIfRetargetEnv (.var "p")
      (.ty (.borrow true [.var "y"])) Lifetime.root := by
  exact @LValTyping.var pointerIfRetargetEnv "p" pointerIfPYSlot (by
    simp [pointerIfRetargetEnv, pointerIfPYSlot, Env.update])

theorem pointerIf_borrow_y_wellFormed :
    WellFormedTy pointerIfEnv (.borrow true [.var "y"]) Lifetime.root := by
  exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
    intro target htarget
    simp at htarget
    subst htarget
    exact ⟨.int, Lifetime.root, pointerIf_y_typing,
      LifetimeOutlives.refl Lifetime.root,
      ⟨pointerIfYSlot, by
        simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update,
          LVal.base],
        LifetimeOutlives.refl Lifetime.root⟩⟩))

theorem pointerIf_shape_px_py :
    ShapeCompatible pointerIfEnv
      (.ty (.borrow true [.var "x"])) (.ty (.borrow true [.var "y"])) := by
  refine ShapeCompatible.borrow ?left ?right ShapeCompatible.int
  · intro target htarget
    simp at htarget
    subst htarget
    exact ⟨Lifetime.root, pointerIf_x_typing⟩
  · intro target htarget
    simp at htarget
    subst htarget
    exact ⟨Lifetime.root, pointerIf_y_typing⟩

theorem pointerIf_retarget_write :
    EnvWrite 0 pointerIfEnv (.var "p") (.borrow true [.var "y"])
      pointerIfRetargetEnv := by
  simpa [pointerIfRetargetEnv, pointerIfPYSlot, pointerIfPXSlot, LVal.base] using
    (@EnvWrite.intro 0 pointerIfEnv pointerIfEnv (.var "p")
      pointerIfPXSlot (.borrow true [.var "y"]) (.ty (.borrow true [.var "y"]))
      (by
        show pointerIfEnv.slotAt "p" = some pointerIfPXSlot
        simp [pointerIfEnv, pointerIfPXSlot, Env.update])
      UpdateAtPath.strong)

theorem pointerIf_retarget_ranked :
    ∃ φ, LinearizedBy φ pointerIfEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ pointerIfRetargetEnv (.borrow true [.var "y"]) := by
  let φ : Name → Nat := fun name => if name = "p" then 1 else 0
  refine ⟨φ, ?linearized, ?below⟩
  · intro root slot hslot v hv
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
        simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
      subst v
      simp [φ, LVal.base]
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars] at hv
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hv
          simp [PartialTy.vars, Ty.vars] at hv
        · have hnone : pointerIfEnv.slotAt root = none := by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone
  · constructor
    · intro root slot mutable targets target hslot hcontains htarget hrhs
      rcases hrhs with ⟨rhsMutable, rhsTargets, hrhsContains, hrhsTarget⟩
      cases hrhsContains with
      | here =>
          by_cases hp : root = "p"
          · subst hp
            have hslotTy : slot.ty = .ty (.borrow true [.var "y"]) := by
              simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfPYSlot,
                Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
            rw [hslotTy] at hcontains
            cases hcontains with
            | here =>
                simp at htarget
                subst htarget
                simp [φ, LVal.base]
          · by_cases hy : root = "y"
            · subst hy
              have hslotTy : slot.ty = .ty .int := by
                simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
                  pointerIfPYSlot, Env.update] using
                  (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
              rw [hslotTy] at hcontains
              cases hcontains
            · by_cases hx : root = "x"
              · subst hx
                have hslotTy : slot.ty = .ty .int := by
                  simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                    pointerIfYSlot, pointerIfPYSlot, Env.update] using
                    (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
                rw [hslotTy] at hcontains
                cases hcontains
              · have hnone : pointerIfRetargetEnv.slotAt root = none := by
                  simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                    pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty, hp, hy, hx]
                rw [hslot] at hnone
                cases hnone
    · intro root other mutable targetsMutable targetsOther targetMutable targetOther
        hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
        _hrhsMutable _hrhsOther
      rcases hcontainsMutable with ⟨slot, hslot, hcontainsTy⟩
      rcases hcontainsOther with ⟨otherSlot, hotherSlot, hotherContainsTy⟩
      by_cases hp : root = "p"
      · subst hp
        by_cases hother : other = "p"
        · exact hother.symm
        · have hotherNoBorrow : False := by
            by_cases hy : other = "y"
            · subst hy
              have hty : otherSlot.ty = .ty .int := by
                simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
                  pointerIfPYSlot, Env.update] using
                  (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                    hotherSlot).symm
              rw [hty] at hotherContainsTy
              cases hotherContainsTy
            · by_cases hx : other = "x"
              · subst hx
                have hty : otherSlot.ty = .ty .int := by
                  simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                    pointerIfYSlot, pointerIfPYSlot, Env.update] using
                    (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                      hotherSlot).symm
                rw [hty] at hotherContainsTy
                cases hotherContainsTy
              · have hnone : pointerIfRetargetEnv.slotAt other = none := by
                  simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                    pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty, hother, hy, hx]
                rw [hotherSlot] at hnone
                cases hnone
          exact False.elim hotherNoBorrow
      · have hrootNoBorrow : False := by
          by_cases hy : root = "y"
          · subst hy
            have hty : slot.ty = .ty .int := by
              simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
                pointerIfPYSlot, Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
            rw [hty] at hcontainsTy
            cases hcontainsTy
          · by_cases hx : root = "x"
            · subst hx
              have hty : slot.ty = .ty .int := by
                simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                  pointerIfYSlot, pointerIfPYSlot, Env.update] using
                  (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
              rw [hty] at hcontainsTy
              cases hcontainsTy
            · have hnone : pointerIfRetargetEnv.slotAt root = none := by
                simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                  pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty, hp, hy, hx]
              rw [hslot] at hnone
              cases hnone
        exact False.elim hrootNoBorrow

theorem pointerIfRetarget_not_writeProhibited_p :
    ¬ WriteProhibited pointerIfRetargetEnv (.var "p") := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨root, targets, target, hcontains, htarget, hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "y"]) := by
        simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfPYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy with
      | here =>
          simp at htarget
          subst htarget
          simp [PathConflicts, LVal.base] at hconflict
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPYSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfRetargetEnv.slotAt root = none := by
            simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone
  · rcases himm with ⟨root, targets, target, hcontains, htarget, hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "y"]) := by
        simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfPYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPYSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfRetargetEnv.slotAt root = none := by
            simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone

theorem pointerIfEnv_contained :
    ContainedBorrowsWellFormed pointerIfEnv := by
  intro root slot mutable targets hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hp : root = "p"
  · subst hp
    have hcontainedTy : containedSlot.ty = .ty (.borrow true [.var "x"]) := by
      simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
          hcontainedSlot).symm
    rw [hcontainedTy] at hcontainsTy
    cases hcontainsTy with
    | here =>
        intro target htarget
        simp at htarget
        subst htarget
        exact ⟨.int, Lifetime.root, pointerIf_x_typing,
          LifetimeOutlives.refl Lifetime.root,
          ⟨pointerIfXSlot, by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, LVal.base],
            LifetimeOutlives.refl Lifetime.root⟩⟩
  · by_cases hy : root = "y"
    · subst hy
      have hcontainedTy : containedSlot.ty = .ty .int := by
        simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
            hcontainedSlot).symm
      rw [hcontainedTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hx : root = "x"
      · subst hx
        have hcontainedTy : containedSlot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hcontainedSlot).symm
        rw [hcontainedTy] at hcontainsTy
        cases hcontainsTy
      · have hnone : pointerIfEnv.slotAt root = none := by
          simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update, Env.empty, hp, hy, hx]
        rw [hslot] at hnone
        cases hnone

theorem pointerIfRetarget_slot_borrows_wellFormed :
    PartialTyBorrowsWellFormedInSlot pointerIfRetargetEnv
      pointerIfPYSlot.lifetime pointerIfPYSlot.ty := by
  intro mutable targets hcontains
  cases hcontains with
  | here =>
      intro target htarget
      simp at htarget
      subst htarget
      exact ⟨.int, Lifetime.root, pointerIfRetarget_y_typing,
        LifetimeOutlives.refl Lifetime.root,
        ⟨pointerIfYSlot, by
          simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPYSlot, Env.update, LVal.base],
          LifetimeOutlives.refl Lifetime.root⟩⟩

theorem pointerIfRetarget_contained :
    ContainedBorrowsWellFormed pointerIfRetargetEnv := by
  simpa [pointerIfRetargetEnv] using
    (ContainedBorrowsWellFormed.update_slot
      (env := pointerIfEnv) (x := "p") (slot := pointerIfPYSlot)
      pointerIfEnv_contained pointerIfRetarget_slot_borrows_wellFormed
      pointerIfRetarget_not_writeProhibited_p)

axiom pointerIfRetarget_coherent :
    EnvWriteCoherenceObligations pointerIfEnv pointerIfRetargetEnv "p"

theorem pointerRetargetBranch_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      pointerRetargetBranch .unit pointerIfRetargetEnv := by
  unfold pointerRetargetBranch
  exact TermTyping.assign
    pointerIf_p_typing
    (TermTyping.mutBorrow pointerIf_y_typing pointerIf_y_mutable
      pointerIf_not_writeProhibited_y)
    pointerIf_p_typing
    pointerIf_shape_px_py
    pointerIf_borrow_y_wellFormed
    pointerIf_retarget_write
    pointerIf_retarget_ranked
    pointerIfRetarget_coherent
    pointerIfRetarget_contained
    pointerIfRetarget_not_writeProhibited_p

axiom pointerWriteBranch_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      pointerWriteBranch .unit pointerIfWriteEnv

axiom ifPointerAssignment_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      ifPointerAssignment .unit pointerIfJoinEnv

end Paper
end LwRust
