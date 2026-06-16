import LwRust.Paper.BorrowChecker
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
  exact TermTyping.eq (ghost := "γ")
    (TermTyping.const ValueTyping.int)
    (by simp [Env.fresh, Env.empty])
    (TermTyping.const ValueTyping.int)
    (TermTyping.const ValueTyping.int)
    CopyTy.int
    CopyTy.int
    ShapeCompatible.int

theorem scalarCopyComparison_checker_accepts :
    borrowCheck? 32 scalarCopyComparison = true := by
  native_decide

theorem scalarCopyComparison_terminates :
    TerminatesAsValue ProgramStore.empty Lifetime.root scalarCopyComparison := by
  unfold scalarCopyComparison
  exact ⟨ProgramStore.empty, .bool true,
    MultiStep.trans Step.eqTrue MultiStep.refl⟩

theorem scalarCopyComparison_typeSafety :
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty Lifetime.root scalarCopyComparison finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue Env.empty .bool :=
  emptyInitial_typeAndBorrowSafety_total scalarCopyComparison_typing
    scalarCopyComparison_terminates

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
    (tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_int)
  · simp [EnvJoin, IsLUB, IsLeast, upperBounds, lowerBounds]
  · intro x branchSlot joinSlot hbranch
    simp [Env.empty] at hbranch
  · intro x branchSlot joinSlot hbranch
    simp [Env.empty] at hbranch

theorem ifThenElseInt_checker_accepts :
    borrowCheck? 32 ifThenElseInt = true := by
  native_decide

theorem ifThenElseInt_terminates :
    TerminatesAsValue ProgramStore.empty Lifetime.root ifThenElseInt := by
  unfold ifThenElseInt
  exact ⟨ProgramStore.empty, .int 1,
    MultiStep.trans Step.iteTrue MultiStep.refl⟩

theorem ifThenElseInt_typeSafety :
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty Lifetime.root ifThenElseInt finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue Env.empty .int :=
  emptyInitial_typeAndBorrowSafety_total ifThenElseInt_typing
    ifThenElseInt_terminates

/--
Accepted `if/else` example with a nontrivial boolean guard.  The conditional
still joins to the empty environment.
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
    (tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_int)
  · simp [EnvJoin, IsLUB, IsLeast, upperBounds, lowerBounds]
  · intro x branchSlot joinSlot hbranch
    simp [Env.empty] at hbranch
  · intro x branchSlot joinSlot hbranch
    simp [Env.empty] at hbranch

theorem ifEqThenElseInt_checker_accepts :
    borrowCheck? 64 ifEqThenElseInt = true := by
  native_decide

theorem ifEqThenElseInt_terminates :
    TerminatesAsValue ProgramStore.empty Lifetime.root ifEqThenElseInt := by
  unfold ifEqThenElseInt scalarCopyComparison
  exact ⟨ProgramStore.empty, .int 1,
    MultiStep.trans (Step.subIte Step.eqTrue)
      (MultiStep.trans Step.iteTrue MultiStep.refl)⟩

theorem ifEqThenElseInt_typeSafety :
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty Lifetime.root ifEqThenElseInt finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue Env.empty .int :=
  emptyInitial_typeAndBorrowSafety_total ifEqThenElseInt_typing
    ifEqThenElseInt_terminates

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
  exact TermTyping.eq (ghost := "γ")
    (TermTyping.copy pointerIf_deref_p_typing CopyTy.int
      pointerIf_not_readProhibited_deref_p)
    (by simp [Env.fresh, pointerIfEnv, pointerIfXSlot, pointerIfYSlot,
      pointerIfPXSlot, Env.update, Env.empty])
    (TermTyping.const ValueTyping.int)
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

theorem pointerIfEnv_borrow_root_p {root : Name} {mutable : Bool}
    {targets : List LVal} :
    pointerIfEnv ⊢ root ↝ (Ty.borrow mutable targets) →
    root = "p" := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hp : root = "p"
  · exact hp
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

theorem pointerIfEnv_p_targets {targets : List LVal} :
    pointerIfEnv ⊢ "p" ↝ (&mut targets) →
    targets = [.var "x"] := by
  rintro ⟨slot, hslot, hcontains⟩
  have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
    simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
      (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
  rw [hslotTy] at hcontains
  cases hcontains
  rfl

theorem pointerIfEnv_x_no_mut {targets : List LVal} :
    ¬ pointerIfEnv ⊢ "x" ↝ (&mut targets) := by
  rintro ⟨slot, hslot, hcontains⟩
  have hslotTy : slot.ty = .ty .int := by
    simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
      Env.update] using
      (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
  rw [hslotTy] at hcontains
  cases hcontains

theorem pointerIfEnv_p_borrowSafeRoot :
    BorrowSafeRoot pointerIfEnv "p" := by
  intro y mutable targetsMutable targetsOther targetMutable targetOther
    _hmutable hother _htargetMutable _htargetOther _hconflict
  exact (pointerIfEnv_borrow_root_p hother).symm

theorem pointerIfEnv_x_borrowSafeRoot :
    BorrowSafeRoot pointerIfEnv "x" := by
  intro y mutable targetsMutable targetsOther targetMutable targetOther
    hmutable _hother _htargetMutable _htargetOther _hconflict
  exact False.elim (pointerIfEnv_x_no_mut hmutable)

theorem pointerIfEnv_guard_p_or_x {root : Name} :
    BorrowAuthorityGuard pointerIfEnv "p" root →
    root = "p" ∨ root = "x" := by
  intro hguard
  induction hguard with
  | base =>
      exact Or.inl rfl
  | step hcontainer hnode hmem ih =>
      rcases ih with hcontainerRoot | hcontainerRoot
      · subst hcontainerRoot
        have htargets := pointerIfEnv_p_targets hnode
        subst htargets
        simp at hmem
        right
        simpa [LVal.base] using congrArg LVal.base hmem
      · subst hcontainerRoot
        exact False.elim (pointerIfEnv_x_no_mut hnode)

theorem pointerIf_deref_p_assignmentSafe :
    AssignmentBorrowSafety pointerIfEnv (.deref (.var "p")) := by
  intro root hguard
  rcases pointerIfEnv_guard_p_or_x (by simpa [LVal.base] using hguard) with
    hroot | hroot
  · subst hroot
    exact pointerIfEnv_p_borrowSafeRoot
  · subst hroot
    exact pointerIfEnv_x_borrowSafeRoot

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

theorem pointerIfRetarget_old_root_int : ∀ {lv partialTy lifetime},
    LVal.base lv ≠ "p" →
    LValTyping pointerIfRetargetEnv lv partialTy lifetime →
    (lv = .var "x" ∨ lv = .var "y") ∧
      partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  intro lv
  induction lv with
  | var x =>
      intro partialTy lifetime hbase htyping
      cases htyping with
      | var hslot =>
          rename_i slot
          by_cases hx : x = "x"
          · subst hx
            have hslotExpected :
                pointerIfRetargetEnv.slotAt "x" = some pointerIfXSlot := by
              simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                pointerIfYSlot, pointerIfPYSlot, Env.update]
            have hslotEq : slot = pointerIfXSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst slot
            simp [pointerIfXSlot]
          · by_cases hy : x = "y"
            · subst hy
              have hslotExpected :
                  pointerIfRetargetEnv.slotAt "y" = some pointerIfYSlot := by
                simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
                  pointerIfPYSlot, Env.update]
              have hslotEq : slot = pointerIfYSlot :=
                Option.some.inj (hslot.symm.trans hslotExpected)
              subst slot
              simp [pointerIfYSlot]
            · by_cases hp : x = "p"
              · subst hp
                simp [LVal.base] at hbase
              · have hnone : pointerIfRetargetEnv.slotAt x = none := by
                  simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                    pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty,
                    hx, hy, hp]
                rw [hslot] at hnone
                cases hnone
  | deref lv ih =>
      intro partialTy lifetime hbase htyping
      cases htyping with
      | box hinner =>
          rcases ih (by simpa [LVal.base] using hbase) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy
      | borrow hinner _htargets =>
          rcases ih (by simpa [LVal.base] using hbase) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy

theorem pointerIfRetarget_no_y_targets_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping pointerIfRetargetEnv [.var "y"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htyping
  generalize hpartialTy :
      (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIfRetarget_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      cases hrest

theorem pointerIfRetarget_no_y_targets_box {inner lifetime} :
    ¬ LValTargetsTyping pointerIfRetargetEnv [.var "y"] (.box inner)
      lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIfRetarget_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      cases hrest

theorem pointerIfRetarget_p_root_facts : ∀ {lv},
    LVal.base lv = "p" →
    (∀ {inner lifetime},
      ¬ LValTyping pointerIfRetargetEnv lv (.box inner) lifetime) ∧
    (∀ {mutable targets lifetime},
      LValTyping pointerIfRetargetEnv lv
        (.ty (.borrow mutable targets)) lifetime →
      lv = .var "p" ∧ mutable = true ∧ targets = [.var "y"] ∧
        lifetime = Lifetime.root) := by
  intro lv
  induction lv with
  | var x =>
      intro hbase
      constructor
      · intro inner lifetime htyping
        generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : x = "p" := by
              simpa [LVal.base] using hbase
            subst hx
            have hslotExpected :
                pointerIfRetargetEnv.slotAt "p" = some pointerIfPYSlot := by
              simp [pointerIfRetargetEnv, pointerIfPYSlot, Env.update]
            have hslotEq : slot = pointerIfPYSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst slot
            simp [pointerIfPYSlot] at hpartialTy
      · intro mutable targets lifetime htyping
        generalize hpartialTy :
            (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : x = "p" := by
              simpa [LVal.base] using hbase
            subst hx
            have hslotExpected :
                pointerIfRetargetEnv.slotAt "p" = some pointerIfPYSlot := by
              simp [pointerIfRetargetEnv, pointerIfPYSlot, Env.update]
            have hslotEq : slot = pointerIfPYSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst slot
            simp [pointerIfPYSlot] at hpartialTy
            rcases hpartialTy with ⟨rfl, rfl⟩
            simp [pointerIfPYSlot]
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
            exact pointerIfRetarget_no_y_targets_box htargets
      · intro mutable targets lifetime htyping
        cases htyping with
        | box hinner =>
            exact False.elim (ihp.1 hinner)
        | borrow hinner htargets =>
            rcases ihp.2 hinner with ⟨rfl, rfl, rfl, rfl⟩
            exact False.elim (pointerIfRetarget_no_y_targets_borrow htargets)

theorem pointerIfRetarget_coherent :
    EnvWriteCoherenceObligations pointerIfEnv pointerIfRetargetEnv "p" := by
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    rcases pointerIfRetarget_old_root_int hbase htyping with
      ⟨_, hpartialTy, _⟩
    cases hpartialTy
  · intro lv mutable targets borrowLifetime hbase htyping
    rcases (pointerIfRetarget_p_root_facts hbase).2 htyping with
      ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨.int, Lifetime.root,
      LValTargetsTyping.singleton pointerIfRetarget_y_typing⟩

theorem pointerRetargetBranch_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      pointerRetargetBranch .unit pointerIfRetargetEnv := by
  unfold pointerRetargetBranch
  exact TermTyping.assign
    pointerIf_p_typing
    (TermTyping.mutBorrow pointerIf_y_typing pointerIf_y_mutable
      pointerIf_not_writeProhibited_y)
    (by trivial)
    pointerIf_p_typing
    pointerIf_shape_px_py
    pointerIf_borrow_y_wellFormed
    pointerIf_retarget_write
    pointerIf_retarget_ranked
    pointerIfRetarget_coherent
    pointerIfRetarget_contained
    pointerIfRetarget_not_writeProhibited_p

theorem pointerIf_write_x :
    EnvWrite 1 pointerIfEnv (.var "x") .int
      (pointerIfEnv.update "x" pointerIfXSlot) := by
  simpa [pointerIfXSlot, LVal.base] using
    (@EnvWrite.intro 1 pointerIfEnv pointerIfEnv (.var "x")
      pointerIfXSlot .int (.ty .int)
      (by
        show pointerIfEnv.slotAt "x" = some pointerIfXSlot
        simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
          Env.update])
      (UpdateAtPath.weak ShapeCompatible.int (PartialTyJoin.self (.ty .int))))

theorem pointerIf_write_deref_p :
    EnvWrite 0 pointerIfEnv (.deref (.var "p")) .int pointerIfWriteEnv := by
  have htargets : WriteBorrowTargets 1 pointerIfEnv [] [.var "x"] .int
      (pointerIfEnv.update "x" pointerIfXSlot) := by
    exact WriteBorrowTargets.singleton pointerIf_write_x
      ⟨.int, Lifetime.root, pointerIf_x_typing⟩
  simpa [pointerIfWriteEnv, pointerIfPXSlot, pointerIfXSlot, LVal.base,
      LVal.path] using
    (@EnvWrite.intro 0 pointerIfEnv (pointerIfEnv.update "x" pointerIfXSlot)
      (.deref (.var "p")) pointerIfPXSlot .int
      (.ty (.borrow true [.var "x"]))
      (by
        show pointerIfEnv.slotAt "p" = some pointerIfPXSlot
        simp [pointerIfEnv, pointerIfPXSlot, Env.update])
      (@UpdateAtPath.mutBorrow pointerIfEnv
        (pointerIfEnv.update "x" pointerIfXSlot) 0 [] [.var "x"] .int
        htargets))

theorem pointerIf_write_ranked :
    ∃ φ, LinearizedBy φ pointerIfEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ pointerIfWriteEnv .int := by
  refine ⟨pointerIf_retarget_ranked.choose,
    pointerIf_retarget_ranked.choose_spec.1, ?below⟩
  · constructor
    · intro root slot mutable targets target hslot hcontains _htarget hrhs
      rcases hrhs with ⟨rhsMutable, rhsTargets, hrhsContains, _hrhsTarget⟩
      cases hrhsContains
    · intro root other mutable targetsMutable targetsOther targetMutable targetOther
        hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
        hrhsMutable _hrhsOther
      rcases hrhsMutable with ⟨rhsMutable, rhsTargets, hrhsContains, _hrhsTarget⟩
      cases hrhsContains

theorem pointerIf_old_root_int : ∀ {lv partialTy lifetime},
    LVal.base lv ≠ "p" →
    LValTyping pointerIfEnv lv partialTy lifetime →
    (lv = .var "x" ∨ lv = .var "y") ∧
      partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  intro lv
  induction lv with
  | var x =>
      intro partialTy lifetime hbase htyping
      cases htyping with
      | var hslot =>
          rename_i slot
          by_cases hx : x = "x"
          · subst hx
            have hslotExpected : pointerIfEnv.slotAt "x" = some pointerIfXSlot := by
              simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
                Env.update]
            have hslotEq : slot = pointerIfXSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst slot
            simp [pointerIfXSlot]
          · by_cases hy : x = "y"
            · subst hy
              have hslotExpected : pointerIfEnv.slotAt "y" = some pointerIfYSlot := by
                simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update]
              have hslotEq : slot = pointerIfYSlot :=
                Option.some.inj (hslot.symm.trans hslotExpected)
              subst slot
              simp [pointerIfYSlot]
            · by_cases hp : x = "p"
              · subst hp
                simp [LVal.base] at hbase
              · have hnone : pointerIfEnv.slotAt x = none := by
                  simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot,
                    pointerIfPXSlot, Env.update, Env.empty, hx, hy, hp]
                rw [hslot] at hnone
                cases hnone
  | deref lv ih =>
      intro partialTy lifetime hbase htyping
      cases htyping with
      | box hinner =>
          rcases ih (by simpa [LVal.base] using hbase) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy
      | borrow hinner _htargets =>
          rcases ih (by simpa [LVal.base] using hbase) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy

theorem pointerIf_no_x_targets_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping pointerIfEnv [.var "x"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htyping
  generalize hpartialTy :
      (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIf_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      cases hrest

theorem pointerIf_no_x_targets_box {inner lifetime} :
    ¬ LValTargetsTyping pointerIfEnv [.var "x"] (.box inner) lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIf_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      cases hrest

theorem pointerIf_p_root_facts : ∀ {lv},
    LVal.base lv = "p" →
    (∀ {inner lifetime}, ¬ LValTyping pointerIfEnv lv (.box inner) lifetime) ∧
    (∀ {mutable targets lifetime},
      LValTyping pointerIfEnv lv (.ty (.borrow mutable targets)) lifetime →
      lv = .var "p" ∧ mutable = true ∧ targets = [.var "x"] ∧
        lifetime = Lifetime.root) := by
  intro lv
  induction lv with
  | var x =>
      intro hbase
      constructor
      · intro inner lifetime htyping
        generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : x = "p" := by simpa [LVal.base] using hbase
            subst hx
            have hslotExpected : pointerIfEnv.slotAt "p" = some pointerIfPXSlot := by
              simp [pointerIfEnv, pointerIfPXSlot, Env.update]
            have hslotEq : slot = pointerIfPXSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst slot
            simp [pointerIfPXSlot] at hpartialTy
      · intro mutable targets lifetime htyping
        generalize hpartialTy :
            (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : x = "p" := by simpa [LVal.base] using hbase
            subst hx
            have hslotExpected : pointerIfEnv.slotAt "p" = some pointerIfPXSlot := by
              simp [pointerIfEnv, pointerIfPXSlot, Env.update]
            have hslotEq : slot = pointerIfPXSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst slot
            simp [pointerIfPXSlot] at hpartialTy
            rcases hpartialTy with ⟨rfl, rfl⟩
            simp [pointerIfPXSlot]
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
            exact pointerIf_no_x_targets_box htargets
      · intro mutable targets lifetime htyping
        cases htyping with
        | box hinner =>
            exact False.elim (ihp.1 hinner)
        | borrow hinner htargets =>
            rcases ihp.2 hinner with ⟨rfl, rfl, rfl, rfl⟩
            exact False.elim (pointerIf_no_x_targets_borrow htargets)

theorem pointerIf_coherent : Coherent pointerIfEnv := by
  intro lv mutable targets borrowLifetime htyping
  by_cases hbase : LVal.base lv = "p"
  · rcases (pointerIf_p_root_facts hbase).2 htyping with
      ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨.int, Lifetime.root, LValTargetsTyping.singleton pointerIf_x_typing⟩
  · rcases pointerIf_old_root_int hbase htyping with ⟨_, hpartialTy, _⟩
    cases hpartialTy

theorem env_ext_local (left right : Env)
    (h : ∀ x, left.slotAt x = right.slotAt x) : left = right := by
  cases left with
  | mk leftSlotAt =>
      cases right with
      | mk rightSlotAt =>
          have hfun : leftSlotAt = rightSlotAt := funext h
          subst hfun
          rfl

theorem pointerIfWriteEnv_eq : pointerIfWriteEnv = pointerIfEnv := by
  apply env_ext_local
  intro name
  by_cases hp : name = "p" <;> by_cases hx : name = "x" <;>
    by_cases hy : name = "y" <;>
    simp [pointerIfWriteEnv, pointerIfEnv, pointerIfXSlot, pointerIfYSlot,
      pointerIfPXSlot, Env.update, Env.empty, hp, hx, hy]

theorem pointerIf_write_coherent :
    EnvWriteCoherenceObligations pointerIfEnv pointerIfWriteEnv "p" := by
  rw [pointerIfWriteEnv_eq]
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    exact ⟨⟨borrowLifetime, htyping⟩,
      fun targetTy targetLifetime htargets =>
        ⟨targetTy, targetLifetime, htargets⟩⟩
  · intro lv mutable targets borrowLifetime hbase htyping
    exact pointerIf_coherent lv mutable targets borrowLifetime htyping

theorem pointerIf_not_writeProhibited_deref_p :
    ¬ WriteProhibited pointerIfWriteEnv (.deref (.var "p")) := by
  rw [pointerIfWriteEnv_eq]
  intro hwrite
  rcases hwrite with hread | himm
  · exact pointerIf_not_readProhibited_deref_p (by
      simpa using hread)
  · rcases himm with ⟨root, targets, target, hcontains, htarget, hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
        simpa [pointerIfWriteEnv, pointerIfEnv, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfWriteEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPXSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfWriteEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPXSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfEnv.slotAt root = none := by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone

theorem pointerWriteBranch_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      pointerWriteBranch .unit pointerIfWriteEnv := by
  unfold pointerWriteBranch
  exact TermTyping.assign
    pointerIf_deref_p_typing
    (TermTyping.const ValueTyping.int)
    pointerIf_deref_p_assignmentSafe
    pointerIf_deref_p_typing
    ShapeCompatible.int
    WellFormedTy.int
    pointerIf_write_deref_p
    pointerIf_write_ranked
    pointerIf_write_coherent
    (by simpa [pointerIfWriteEnv_eq] using pointerIfEnv_contained)
    pointerIf_not_writeProhibited_deref_p

/-- Two borrow types strengthening into the same partial type can be merged:
the appended target list still strengthens into it.  This is the least-upper-
bound argument for the `p` slot of the branch join. -/
theorem partialTyStrengthens_borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal}
    {joined : PartialTy}
    (hleft : PartialTyStrengthens (.ty (.borrow mutable leftTargets)) joined)
    (hright : PartialTyStrengthens (.ty (.borrow mutable rightTargets)) joined) :
    PartialTyStrengthens (.ty (.borrow mutable (leftTargets ++ rightTargets)))
      joined := by
  cases hleft with
  | reflex =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hmem
        · exact hsubRight hmem)
  | borrow hsubLeft =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem)
  | intoUndef hinner =>
      rcases PartialTyStrengthens.from_borrow_inv hinner with
        ⟨targetTargets, rfl, hsubLeft⟩
      have hsubRight : rightTargets ⊆ targetTargets := by
        cases hright with
        | intoUndef hinner' => exact PartialTyStrengthens.borrow_subset hinner'
      exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem))

theorem pointerIfJoin_x_typing :
    LValTyping pointerIfJoinEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfJoinEnv "x" pointerIfXSlot (by
    simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot, pointerIfJoinPSlot,
      Env.update])

theorem pointerIfJoin_y_typing :
    LValTyping pointerIfJoinEnv (.var "y") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfJoinEnv "y" pointerIfYSlot (by
    simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot, Env.update])

theorem pointerIfJoin_old_root_int : ∀ {lv partialTy lifetime},
    LVal.base lv ≠ "p" →
    LValTyping pointerIfJoinEnv lv partialTy lifetime →
    (lv = .var "x" ∨ lv = .var "y") ∧
      partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  intro lv
  induction lv with
  | var x =>
      intro partialTy lifetime hbase htyping
      cases htyping with
      | var hslot =>
          rename_i slot
          by_cases hx : x = "x"
          · subst hx
            have hslotExpected :
                pointerIfJoinEnv.slotAt "x" = some pointerIfXSlot := by
              simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
                pointerIfJoinPSlot, Env.update]
            have hslotEq : slot = pointerIfXSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst slot
            simp [pointerIfXSlot]
          · by_cases hy : x = "y"
            · subst hy
              have hslotExpected :
                  pointerIfJoinEnv.slotAt "y" = some pointerIfYSlot := by
                simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
                  Env.update]
              have hslotEq : slot = pointerIfYSlot :=
                Option.some.inj (hslot.symm.trans hslotExpected)
              subst slot
              simp [pointerIfYSlot]
            · by_cases hp : x = "p"
              · subst hp
                simp [LVal.base] at hbase
              · have hnone : pointerIfJoinEnv.slotAt x = none := by
                  simp [pointerIfJoinEnv, Env.update, Env.empty, hx, hy, hp]
                rw [hslot] at hnone
                cases hnone
  | deref lv ih =>
      intro partialTy lifetime hbase htyping
      cases htyping with
      | box hinner =>
          rcases ih (by simpa [LVal.base] using hbase) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy
      | borrow hinner _htargets =>
          rcases ih (by simpa [LVal.base] using hbase) hinner with
            ⟨_, hpartialTy, _⟩
          cases hpartialTy

theorem pointerIfJoin_no_targets_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping pointerIfJoinEnv [.var "y", .var "x"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htyping
  generalize hpartialTy :
      (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
  cases htyping with
  | cons hhead _hrest hunion _hlifetime =>
      rcases pointerIfJoin_old_root_int (by simp [LVal.base]) hhead with
        ⟨_, hheadTy, _⟩
      injection hheadTy with hheadTy
      subst hheadTy
      have hupper : PartialTyStrengthens (.ty .int) partialTy :=
        hunion.1 (by simp)
      rw [← hpartialTy] at hupper
      cases PartialTyStrengthens.from_int_inv hupper

theorem pointerIfJoin_no_targets_box {inner lifetime} :
    ¬ LValTargetsTyping pointerIfJoinEnv [.var "y", .var "x"] (.box inner)
      lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
  cases htyping with
  | cons hhead _hrest hunion _hlifetime =>
      rcases pointerIfJoin_old_root_int (by simp [LVal.base]) hhead with
        ⟨_, hheadTy, _⟩
      injection hheadTy with hheadTy
      subst hheadTy
      have hupper : PartialTyStrengthens (.ty .int) partialTy :=
        hunion.1 (by simp)
      rw [← hpartialTy] at hupper
      cases hupper

theorem pointerIfJoin_p_root_facts : ∀ {lv},
    LVal.base lv = "p" →
    (∀ {inner lifetime},
      ¬ LValTyping pointerIfJoinEnv lv (.box inner) lifetime) ∧
    (∀ {mutable targets lifetime},
      LValTyping pointerIfJoinEnv lv
        (.ty (.borrow mutable targets)) lifetime →
      lv = .var "p" ∧ mutable = true ∧ targets = [.var "y", .var "x"] ∧
        lifetime = Lifetime.root) := by
  intro lv
  induction lv with
  | var x =>
      intro hbase
      constructor
      · intro inner lifetime htyping
        generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : x = "p" := by simpa [LVal.base] using hbase
            subst hx
            have hslotExpected :
                pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot := by
              simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update]
            have hslotEq : slot = pointerIfJoinPSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst slot
            simp [pointerIfJoinPSlot] at hpartialTy
      · intro mutable targets lifetime htyping
        generalize hpartialTy :
            (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
        cases htyping with
        | var hslot =>
            rename_i slot
            have hx : x = "p" := by simpa [LVal.base] using hbase
            subst hx
            have hslotExpected :
                pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot := by
              simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update]
            have hslotEq : slot = pointerIfJoinPSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst slot
            simp [pointerIfJoinPSlot] at hpartialTy
            rcases hpartialTy with ⟨rfl, rfl⟩
            simp [pointerIfJoinPSlot]
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
            exact pointerIfJoin_no_targets_box htargets
      · intro mutable targets lifetime htyping
        cases htyping with
        | box hinner =>
            exact False.elim (ihp.1 hinner)
        | borrow hinner htargets =>
            rcases ihp.2 hinner with ⟨rfl, rfl, rfl, rfl⟩
            exact False.elim (pointerIfJoin_no_targets_borrow htargets)

theorem pointerIfJoin_coherent : Coherent pointerIfJoinEnv := by
  intro lv mutable targets borrowLifetime htyping
  by_cases hbase : LVal.base lv = "p"
  · rcases (pointerIfJoin_p_root_facts hbase).2 htyping with
      ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨.int, Lifetime.root,
      LValTargetsTyping.cons pointerIfJoin_y_typing
        (LValTargetsTyping.singleton pointerIfJoin_x_typing)
        (PartialTyUnion.self (.ty .int))
        (LifetimeIntersection.self Lifetime.root)⟩
  · rcases pointerIfJoin_old_root_int hbase htyping with ⟨_, hpartialTy, _⟩
    cases hpartialTy

theorem pointerIfJoin_contained :
    ContainedBorrowsWellFormed pointerIfJoinEnv := by
  intro root slot mutable targets hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hp : root = "p"
  · subst hp
    have hslotExpected :
        pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot := by
      simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update]
    have hslotEq : slot = pointerIfJoinPSlot :=
      Option.some.inj (hslot.symm.trans hslotExpected)
    subst slot
    have hcontainedTy :
        containedSlot.ty = .ty (.borrow true [.var "y", .var "x"]) := by
      simpa [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
          hcontainedSlot).symm
    rw [hcontainedTy] at hcontainsTy
    cases hcontainsTy with
    | here =>
        intro target htarget
        simp at htarget
        rcases htarget with rfl | rfl
        · exact ⟨.int, Lifetime.root, pointerIfJoin_y_typing,
            LifetimeOutlives.refl Lifetime.root,
            ⟨pointerIfYSlot, by
              simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
                Env.update, LVal.base],
              LifetimeOutlives.refl Lifetime.root⟩⟩
        · exact ⟨.int, Lifetime.root, pointerIfJoin_x_typing,
            LifetimeOutlives.refl Lifetime.root,
            ⟨pointerIfXSlot, by
              simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
                pointerIfJoinPSlot, Env.update, LVal.base],
              LifetimeOutlives.refl Lifetime.root⟩⟩
  · by_cases hy : root = "y"
    · subst hy
      have hcontainedTy : containedSlot.ty = .ty .int := by
        simpa [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
            hcontainedSlot).symm
      rw [hcontainedTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hx : root = "x"
      · subst hx
        have hcontainedTy : containedSlot.ty = .ty .int := by
          simpa [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
            pointerIfJoinPSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hcontainedSlot).symm
        rw [hcontainedTy] at hcontainsTy
        cases hcontainsTy
      · have hnone : pointerIfJoinEnv.slotAt root = none := by
          simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]
        rw [hslot] at hnone
        cases hnone

theorem pointerIfJoin_linearizable : Linearizable pointerIfJoinEnv := by
  refine ⟨fun name => if name = "p" then 1 else 0, ?_⟩
  intro root slot hslot v hv
  by_cases hp : root = "p"
  · subst hp
    have hslotTy : slot.ty = .ty (.borrow true [.var "y", .var "x"]) := by
      simpa [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hv
    simp [PartialTy.vars, Ty.vars, LVal.base] at hv
    rcases hv with rfl | rfl <;> simp
  · by_cases hy : root = "y"
    · subst hy
      have hslotTy : slot.ty = .ty .int := by
        simpa [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · by_cases hx : root = "x"
      · subst hx
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
            pointerIfJoinPSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars] at hv
      · have hnone : pointerIfJoinEnv.slotAt root = none := by
          simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]
        rw [hslot] at hnone
        cases hnone

theorem pointerIfRetarget_le_join :
    EnvStrengthens pointerIfRetargetEnv pointerIfJoinEnv := by
  intro name
  by_cases hp : name = "p"
  · subst hp
    rw [show pointerIfRetargetEnv.slotAt "p" = some pointerIfPYSlot by
        simp [pointerIfRetargetEnv, pointerIfPYSlot, Env.update],
      show pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot by
        simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update]]
    have hsub : List.Subset [LVal.var "y"] [LVal.var "y", LVal.var "x"] := by
      intro target htarget
      simp at htarget
      subst htarget
      simp
    exact ⟨rfl, PartialTyStrengthens.borrow hsub⟩
  · by_cases hy : name = "y"
    · subst hy
      rw [show pointerIfRetargetEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPYSlot, Env.update],
        show pointerIfJoinEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
            Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hx : name = "x"
      · subst hx
        rw [show pointerIfRetargetEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update],
          show pointerIfJoinEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
              pointerIfJoinPSlot, Env.update]]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · rw [show pointerIfRetargetEnv.slotAt name = none by
            simp [pointerIfRetargetEnv, pointerIfEnv, Env.update, Env.empty,
              hp, hy, hx],
          show pointerIfJoinEnv.slotAt name = none by
            simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]]
        trivial

theorem pointerIfWrite_le_join :
    EnvStrengthens pointerIfWriteEnv pointerIfJoinEnv := by
  rw [pointerIfWriteEnv_eq]
  intro name
  by_cases hp : name = "p"
  · subst hp
    rw [show pointerIfEnv.slotAt "p" = some pointerIfPXSlot by
        simp [pointerIfEnv, pointerIfPXSlot, Env.update],
      show pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot by
        simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update]]
    have hsub : List.Subset [LVal.var "x"] [LVal.var "y", LVal.var "x"] := by
      intro target htarget
      simp at htarget
      subst htarget
      simp
    exact ⟨rfl, PartialTyStrengthens.borrow hsub⟩
  · by_cases hy : name = "y"
    · subst hy
      rw [show pointerIfEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update],
        show pointerIfJoinEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
            Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hx : name = "x"
      · subst hx
        rw [show pointerIfEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot,
              pointerIfPXSlot, Env.update],
          show pointerIfJoinEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
              pointerIfJoinPSlot, Env.update]]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · rw [show pointerIfEnv.slotAt name = none by
            simp [pointerIfEnv, Env.update, Env.empty, hp, hy, hx],
          show pointerIfJoinEnv.slotAt name = none by
            simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]]
        trivial

theorem pointerIfJoin_least {env' : Env}
    (hret : EnvStrengthens pointerIfRetargetEnv env')
    (hwrite : EnvStrengthens pointerIfWriteEnv env') :
    EnvStrengthens pointerIfJoinEnv env' := by
  rw [pointerIfWriteEnv_eq] at hwrite
  intro name
  by_cases hp : name = "p"
  · subst hp
    rcases EnvStrengthens.slot_forward hret (show
        pointerIfRetargetEnv.slotAt "p" = some pointerIfPYSlot by
          simp [pointerIfRetargetEnv, pointerIfPYSlot, Env.update]) with
      ⟨slotY, hslotY, hlife, hstrY⟩
    rcases EnvStrengthens.slot_forward hwrite (show
        pointerIfEnv.slotAt "p" = some pointerIfPXSlot by
          simp [pointerIfEnv, pointerIfPXSlot, Env.update]) with
      ⟨slotX, hslotX, _hlifeX, hstrX⟩
    have hslotEq : slotX = slotY := Option.some.inj (hslotX.symm.trans hslotY)
    subst hslotEq
    rw [show pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot by
        simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update], hslotX]
    have hY : PartialTyStrengthens (.ty (.borrow true [.var "y"])) slotX.ty :=
      hstrY
    have hX : PartialTyStrengthens (.ty (.borrow true [.var "x"])) slotX.ty :=
      hstrX
    have hYX : PartialTyStrengthens
        (.ty (.borrow true ([.var "y"] ++ [.var "x"]))) slotX.ty :=
      partialTyStrengthens_borrow_append hY hX
    exact ⟨hlife, by simpa [pointerIfJoinPSlot] using hYX⟩
  · by_cases hy : name = "y"
    · subst hy
      rcases EnvStrengthens.slot_forward hret (show
          pointerIfRetargetEnv.slotAt "y" = some pointerIfYSlot by
            simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
              pointerIfPYSlot, Env.update]) with
        ⟨slot', hslot', hlife, hstr⟩
      rw [show pointerIfJoinEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
            Env.update], hslot']
      exact ⟨hlife, hstr⟩
    · by_cases hx : name = "x"
      · subst hx
        rcases EnvStrengthens.slot_forward hret (show
            pointerIfRetargetEnv.slotAt "x" = some pointerIfXSlot by
              simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                pointerIfYSlot, pointerIfPYSlot, Env.update]) with
          ⟨slot', hslot', hlife, hstr⟩
        rw [show pointerIfJoinEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
              pointerIfJoinPSlot, Env.update], hslot']
        exact ⟨hlife, hstr⟩
      · have hretNone : pointerIfRetargetEnv.slotAt name = none := by
          simp [pointerIfRetargetEnv, pointerIfEnv, Env.update, Env.empty,
            hp, hy, hx]
        have hjoinNone : pointerIfJoinEnv.slotAt name = none := by
          simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]
        have h := hret name
        rw [hretNone] at h
        rw [hjoinNone]
        cases henvSlot : env'.slotAt name with
        | none =>
            trivial
        | some envSlot =>
            rw [henvSlot] at h
            cases h

theorem pointerIf_envJoin :
    EnvJoin pointerIfRetargetEnv pointerIfWriteEnv pointerIfJoinEnv := by
  constructor
  · intro env henv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at henv
    rcases henv with rfl | rfl
    · exact pointerIfRetarget_le_join
    · exact pointerIfWrite_le_join
  · intro env' henv'
    exact pointerIfJoin_least (henv' (by simp)) (henv' (by simp))

theorem pointerIfRetarget_join_sameShape :
    EnvJoinSameShape pointerIfRetargetEnv pointerIfJoinEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  by_cases hp : name = "p"
  · subst hp
    have hbranchTy : branchSlot.ty = .ty (.borrow true [.var "y"]) := by
      simpa [pointerIfRetargetEnv, pointerIfPYSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
    have hjoinTy : joinSlot.ty = .ty (.borrow true [.var "y", .var "x"]) := by
      simpa [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
    simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
  · by_cases hy : name = "y"
    · subst hy
      have hbranchTy : branchSlot.ty = .ty .int := by
        simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
          pointerIfPYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
      have hjoinTy : joinSlot.ty = .ty .int := by
        simpa [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
      simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
    · by_cases hx : name = "x"
      · subst hx
        have hbranchTy : branchSlot.ty = .ty .int := by
          simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
            pointerIfYSlot, pointerIfPYSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hbranch).symm
        have hjoinTy : joinSlot.ty = .ty .int := by
          simpa [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
            pointerIfJoinPSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hjoin).symm
        simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
      · have hnone : pointerIfRetargetEnv.slotAt name = none := by
          simp [pointerIfRetargetEnv, pointerIfEnv, Env.update, Env.empty,
            hp, hy, hx]
        rw [hbranch] at hnone
        cases hnone

theorem pointerIfWrite_join_sameShape :
    EnvJoinSameShape pointerIfWriteEnv pointerIfJoinEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  rw [pointerIfWriteEnv_eq] at hbranch
  by_cases hp : name = "p"
  · subst hp
    have hbranchTy : branchSlot.ty = .ty (.borrow true [.var "x"]) := by
      simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
    have hjoinTy : joinSlot.ty = .ty (.borrow true [.var "y", .var "x"]) := by
      simpa [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
    simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
  · by_cases hy : name = "y"
    · subst hy
      have hbranchTy : branchSlot.ty = .ty .int := by
        simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
      have hjoinTy : joinSlot.ty = .ty .int := by
        simpa [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
      simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
    · by_cases hx : name = "x"
      · subst hx
        have hbranchTy : branchSlot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hbranch).symm
        have hjoinTy : joinSlot.ty = .ty .int := by
          simpa [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
            pointerIfJoinPSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hjoin).symm
        simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
      · have hnone : pointerIfEnv.slotAt name = none := by
          simp [pointerIfEnv, Env.update, Env.empty, hp, hy, hx]
        rw [hbranch] at hnone
        cases hnone

theorem ifPointerAssignment_join_obligations :
    EnvJoin pointerIfRetargetEnv pointerIfWriteEnv pointerIfJoinEnv ∧
    EnvJoinSameShape pointerIfRetargetEnv pointerIfJoinEnv ∧
      EnvJoinSameShape pointerIfWriteEnv pointerIfJoinEnv ∧
      ContainedBorrowsWellFormed pointerIfJoinEnv ∧
      Coherent pointerIfJoinEnv ∧
      Linearizable pointerIfJoinEnv :=
    ⟨pointerIf_envJoin, pointerIfRetarget_join_sameShape,
      pointerIfWrite_join_sameShape, pointerIfJoin_contained,
      pointerIfJoin_coherent, pointerIfJoin_linearizable⟩

theorem ifPointerAssignment_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      ifPointerAssignment .unit pointerIfJoinEnv := by
  unfold ifPointerAssignment
  exact TermTyping.ite
    pointerIfCondition_typing
    pointerRetargetBranch_typing
    pointerWriteBranch_typing
    (PartialTyJoin.self (.ty .unit))
    ifPointerAssignment_join_obligations.1
    ifPointerAssignment_join_obligations.2.1
    ifPointerAssignment_join_obligations.2.2.1
    WellFormedTy.unit
    ifPointerAssignment_join_obligations.2.2.2.1
    ifPointerAssignment_join_obligations.2.2.2.2.1
    ifPointerAssignment_join_obligations.2.2.2.2.2
    (tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit)

end Paper
end LwRust
