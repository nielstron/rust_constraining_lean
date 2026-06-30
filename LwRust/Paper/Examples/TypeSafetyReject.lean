import LwRust.Paper.Examples.Operational
import LwRust.Paper.Soundness.Helpers.Frame
import LwRust.Paper.Soundness.InitialStates

/-!
Build-checked rejected examples.

These files state rejection as negated typing derivations.  That keeps the
Lean build green while showing that the type-and-borrow safety theorem cannot
be applied to the program.
-/

namespace LwRust
namespace Paper

open Core

def invalidBorrowIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := InvalidBorrowExample.l }

def invalidBorrowYSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [InvalidBorrowExample.x]),
    lifetime := InvalidBorrowExample.l }

/--
Runtime references are not source-level constants over the empty store typing.
This is the small closed-form version of the paper's distinction between
source programs and values created by the operational semantics.
-/
def rawBorrowedReferenceConstant : Term :=
  .val (.ref { location := .var "x", owner := false })

theorem rawBorrowedReferenceConstant_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        rawBorrowedReferenceConstant ty env := by
  rintro ⟨ty, env, htyping⟩
  unfold rawBorrowedReferenceConstant at htyping
  cases htyping with
  | const hvalue =>
      cases hvalue with
      | ref hlookup =>
          simp [StoreTyping.empty] at hlookup

def boxedRawBorrowedReferenceConstant : Term :=
  .box rawBorrowedReferenceConstant

theorem boxedRawBorrowedReferenceConstant_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        boxedRawBorrowedReferenceConstant ty env := by
  rintro ⟨ty, env, htyping⟩
  unfold boxedRawBorrowedReferenceConstant rawBorrowedReferenceConstant at htyping
  cases htyping with
  | box hinner =>
      cases hinner with
      | const hvalue =>
          cases hvalue with
          | ref hlookup =>
              simp [StoreTyping.empty] at hlookup

/--
Paper Section 3.3 example (10), after the invalid borrow has escaped its inner
block: dereferencing `w` is neither terminal nor step-able.
-/
theorem escapingBorrow_stuck_after_inner_drop :
    ¬ ProgressResult InvalidEscapingBorrowExample.Sw
      InvalidEscapingBorrowExample.l
      (.move (.deref (.var "w"))) := by
  intro hprogress
  rcases hprogress with hterminal | ⟨store', term', hstep⟩
  · simp [Terminal] at hterminal
  · exact InvalidEscapingBorrowExample.deref_w_after_z_dropped_is_stuck
      ⟨store', term', hstep⟩

/--
Paper Section 3.3 example (9).  This is the exact program
`{ let mut x = 0; let mut y = &mut x; x = 1; }`.
-/
theorem invalidBorrowExample_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty InvalidBorrowExample.l
        InvalidBorrowExample.invalidProgram ty env := by
  rintro ⟨ty, env, htyping⟩
  unfold InvalidBorrowExample.invalidProgram at htyping
  cases htyping with
  | block _hchild hbody _hwellTy _hdrop =>
      cases hbody with
      | cons hdeclareX htail =>
          cases htail with
          | cons hdeclareY htail2 =>
              cases htail2 with
              | singleton hassign =>
                  cases hdeclareX with
                  | declare _freshX hinitX _freshXOut _cohX hxEnv =>
                      cases hinitX with
                      | const _ =>
                          cases hdeclareY with
                          | declare _freshY hinitY _freshYOut _cohY hyEnv =>
                              cases hinitY with
                              | mutBorrow _hLvY _mutableY _notWriteY =>
                                  rename_i _valueLifetimeY borrowedTy
                                  cases hassign with
                                  | assign _hRhs _hLhsPost _hshape _hwell
                                      hwrite _hnoStale _hranked _hcoh
                                      _hcontained hnotWrite =>
                                      cases _hRhs with
                                      | const hvalue =>
                                      cases hvalue
                                      cases hwrite with
                                      | intro hslot hupdate =>
                                          subst hxEnv
                                          subst hyEnv
                                          cases hupdate with
                                          | strong =>
                                          exact hnotWrite (by
                                            left
                                            refine ⟨"y", [InvalidBorrowExample.x],
                                              InvalidBorrowExample.x, ?_,
                                              by simp, by simp [PathConflicts]⟩
                                            refine ⟨
                                              { ty := .ty (Ty.borrow true
                                                  [InvalidBorrowExample.x]),
                                                lifetime := InvalidBorrowExample.l },
                                              ?_, PartialTyContains.here⟩
                                            simp [Env.update, InvalidBorrowExample.x,
                                              InvalidBorrowExample.l, LVal.base])
              | cons _hhead htail => cases htail

/-- Paper Section 6.1.3's joined environment after
`if ... { p = &mut a; } else { q = &mut a; }`. -/
def rootIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def paperConditionalPSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [.var "x", .var "a"]),
    lifetime := Lifetime.root }

def paperConditionalQSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [.var "y", .var "a"]),
    lifetime := Lifetime.root }

def paperConditionalJoinEnv : Env :=
  (((((Env.empty.update "a" rootIntSlot).update "x" rootIntSlot).update
    "y" rootIntSlot).update "p" paperConditionalPSlot).update
    "q" paperConditionalQSlot)

def paperRejectedIfElse : Term :=
  .ite (.val (.bool true))
    (.assign (.var "p") (.borrow true (.var "a")))
    (.assign (.var "q") (.borrow true (.var "a")))

/--
The paper notes that the Section 6.1.3 conditional join is not borrow safe:
`p` and `q` may both contain mutable borrows whose target lists include `a`.
This remains the counterexample to a global `BorrowSafeEnv` conclusion for
joined approximations.  The relaxed `T-If` rule no longer rejects the join for
that reason; runtime safety must be stated path-sensitively.
-/
theorem paperConditionalJoinEnv_not_borrowSafe :
    ¬ BorrowSafeEnv paperConditionalJoinEnv := by
  intro hsafe
  have hp : paperConditionalJoinEnv ⊢ "p" ↝
      (.borrow true [.var "x", .var "a"]) := by
    refine ⟨paperConditionalPSlot, ?_, PartialTyContains.here⟩
    simp [paperConditionalJoinEnv, paperConditionalPSlot, paperConditionalQSlot,
      rootIntSlot, Env.update]
  have hq : paperConditionalJoinEnv ⊢ "q" ↝
      (.borrow true [.var "y", .var "a"]) := by
    refine ⟨paperConditionalQSlot, ?_, PartialTyContains.here⟩
    simp [paperConditionalJoinEnv, paperConditionalPSlot, paperConditionalQSlot,
      rootIntSlot, Env.update]
  have hpq : "p" = "q" :=
    hsafe "p" "q" true [.var "x", .var "a"] [.var "y", .var "a"]
      (.var "a") (.var "a") hp hq (by simp) (by simp)
      (by simp [PathConflicts, LVal.base])
  contradiction

theorem paperRejectedIfElse_join_rejected :
    ¬ BorrowSafeEnv paperConditionalJoinEnv :=
  paperConditionalJoinEnv_not_borrowSafe

/--
Ordinary safe abstraction does not determine the selected runtime alias
invariant used by the assignment-through-borrow frame proof.

Both `x` and `y` safely abstract borrow-typed roots whose concrete runtime
references point at `a`.  That is allowed by `S ∼ Γ`, but it violates
`RuntimeSelectedBorrowSafe`: the selected mutable target of `x` conflicts with
the selected immutable target of `y`.
-/
def runtimeAliasAName : Name := "a"
def runtimeAliasXName : Name := "x"
def runtimeAliasYName : Name := "y"

def runtimeAliasALVal : LVal := .var runtimeAliasAName
def runtimeAliasALoc : Location := .var runtimeAliasAName

def runtimeAliasIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def runtimeAliasXSlot : EnvSlot :=
  { ty := .ty (.borrow true [runtimeAliasALVal]),
    lifetime := Lifetime.root }

def runtimeAliasYSlot : EnvSlot :=
  { ty := .ty (.borrow false [runtimeAliasALVal]),
    lifetime := Lifetime.root }

def runtimeAliasEnv : Env :=
  { slotAt := fun z =>
      if z = runtimeAliasAName then some runtimeAliasIntSlot
      else if z = runtimeAliasXName then some runtimeAliasXSlot
      else if z = runtimeAliasYName then some runtimeAliasYSlot
      else none }

def runtimeAliasBorrowedA : Value :=
  .ref { location := runtimeAliasALoc, owner := false }

def runtimeAliasStore : ProgramStore :=
  { slotAt := fun location =>
      if location = .var runtimeAliasAName then
        some (StoreSlot.mk (PartialValue.value (.int 0)) Lifetime.root)
      else if location = .var runtimeAliasXName then
        some (StoreSlot.mk (PartialValue.value runtimeAliasBorrowedA)
          Lifetime.root)
      else if location = .var runtimeAliasYName then
        some (StoreSlot.mk (PartialValue.value runtimeAliasBorrowedA)
          Lifetime.root)
      else none }

theorem runtimeAliasEnv_a :
    runtimeAliasEnv.slotAt runtimeAliasAName =
      some runtimeAliasIntSlot := by
  simp [runtimeAliasEnv, runtimeAliasAName]

theorem runtimeAliasEnv_x :
    runtimeAliasEnv.slotAt runtimeAliasXName =
      some runtimeAliasXSlot := by
  simp [runtimeAliasEnv, runtimeAliasXName, runtimeAliasAName]

theorem runtimeAliasEnv_y :
    runtimeAliasEnv.slotAt runtimeAliasYName =
      some runtimeAliasYSlot := by
  simp [runtimeAliasEnv, runtimeAliasYName, runtimeAliasXName,
    runtimeAliasAName]

theorem runtimeAliasStore_a :
    runtimeAliasStore.slotAt (VariableProjection runtimeAliasAName) =
      some (StoreSlot.mk (PartialValue.value (.int 0)) Lifetime.root) := by
  simp [runtimeAliasStore, VariableProjection, runtimeAliasAName]

theorem runtimeAliasStore_x :
    runtimeAliasStore.slotAt (VariableProjection runtimeAliasXName) =
      some (StoreSlot.mk (PartialValue.value runtimeAliasBorrowedA)
        Lifetime.root) := by
  simp [runtimeAliasStore, VariableProjection, runtimeAliasXName,
    runtimeAliasAName]

theorem runtimeAliasStore_y :
    runtimeAliasStore.slotAt (VariableProjection runtimeAliasYName) =
      some (StoreSlot.mk (PartialValue.value runtimeAliasBorrowedA)
        Lifetime.root) := by
  simp [runtimeAliasStore, VariableProjection, runtimeAliasYName,
    runtimeAliasXName, runtimeAliasAName]

theorem runtimeAliasStore_loc_a :
    runtimeAliasStore.loc runtimeAliasALVal = some runtimeAliasALoc := by
  simp [runtimeAliasALVal, runtimeAliasALoc]

theorem runtimeAliasStore_safe :
    runtimeAliasStore ∼ₛ runtimeAliasEnv := by
  constructor
  · intro z
    constructor
    · intro hstore
      by_cases ha : z = runtimeAliasAName
      · subst ha
        exact ⟨runtimeAliasIntSlot, runtimeAliasEnv_a⟩
      · by_cases hx : z = runtimeAliasXName
        · subst hx
          exact ⟨runtimeAliasXSlot, runtimeAliasEnv_x⟩
        · by_cases hy : z = runtimeAliasYName
          · subst hy
            exact ⟨runtimeAliasYSlot, runtimeAliasEnv_y⟩
          · rcases hstore with ⟨slot, hslot⟩
            simp [runtimeAliasStore, VariableProjection, ha, hx, hy] at hslot
    · intro henv
      by_cases ha : z = runtimeAliasAName
      · subst ha
        exact ⟨StoreSlot.mk (PartialValue.value (.int 0)) Lifetime.root,
          runtimeAliasStore_a⟩
      · by_cases hx : z = runtimeAliasXName
        · subst hx
          exact ⟨StoreSlot.mk (PartialValue.value runtimeAliasBorrowedA)
              Lifetime.root,
            runtimeAliasStore_x⟩
        · by_cases hy : z = runtimeAliasYName
          · subst hy
            exact ⟨StoreSlot.mk (PartialValue.value runtimeAliasBorrowedA)
                Lifetime.root,
              runtimeAliasStore_y⟩
          · rcases henv with ⟨slot, hslot⟩
            simp [runtimeAliasEnv, ha, hx, hy] at hslot
  · intro z envSlot henv
    by_cases ha : z = runtimeAliasAName
    · subst ha
      have hslotEq : envSlot = runtimeAliasIntSlot :=
        Option.some.inj (henv.symm.trans runtimeAliasEnv_a)
      subst hslotEq
      exact ⟨.value (.int 0), runtimeAliasStore_a, ValidPartialValue.int⟩
    · by_cases hx : z = runtimeAliasXName
      · subst hx
        have hslotEq : envSlot = runtimeAliasXSlot :=
          Option.some.inj (henv.symm.trans runtimeAliasEnv_x)
        subst hslotEq
        exact ⟨PartialValue.value runtimeAliasBorrowedA, runtimeAliasStore_x,
          ValidPartialValue.borrow (target := runtimeAliasALVal) (by simp)
            runtimeAliasStore_loc_a⟩
      · by_cases hy : z = runtimeAliasYName
        · subst hy
          have hslotEq : envSlot = runtimeAliasYSlot :=
            Option.some.inj (henv.symm.trans runtimeAliasEnv_y)
          subst hslotEq
          exact ⟨PartialValue.value runtimeAliasBorrowedA, runtimeAliasStore_y,
            ValidPartialValue.borrow (target := runtimeAliasALVal) (by simp)
              runtimeAliasStore_loc_a⟩
        · simp [runtimeAliasEnv, ha, hx, hy] at henv

theorem runtimeAliasStore_not_runtimeSelectedBorrowSafe :
    ¬ RuntimeFrame.RuntimeSelectedBorrowSafe runtimeAliasStore
      runtimeAliasEnv := by
  intro hsafe
  let xEvidence :
      RuntimeFrame.ValidPartialValueEvidence runtimeAliasStore
        (.value runtimeAliasBorrowedA) runtimeAliasXSlot.ty :=
    RuntimeFrame.ValidPartialValueEvidence.borrow
      (store := runtimeAliasStore) (location := runtimeAliasALoc)
      (mutable := true) (targets := [runtimeAliasALVal])
      runtimeAliasALVal (by simp) runtimeAliasStore_loc_a
  let yEvidence :
      RuntimeFrame.ValidPartialValueEvidence runtimeAliasStore
        (.value runtimeAliasBorrowedA) runtimeAliasYSlot.ty :=
    RuntimeFrame.ValidPartialValueEvidence.borrow
      (store := runtimeAliasStore) (location := runtimeAliasALoc)
      (mutable := false) (targets := [runtimeAliasALVal])
      runtimeAliasALVal (by simp) runtimeAliasStore_loc_a
  have hxSelected :
      RuntimeFrame.EvidenceSelectedBorrow runtimeAliasStore xEvidence true
        [runtimeAliasALVal] runtimeAliasALVal :=
    RuntimeFrame.EvidenceSelectedBorrow.borrow rfl
  have hySelected :
      RuntimeFrame.EvidenceSelectedBorrow runtimeAliasStore yEvidence false
        [runtimeAliasALVal] runtimeAliasALVal :=
    RuntimeFrame.EvidenceSelectedBorrow.borrow rfl
  have hconflict : runtimeAliasALVal ⋈ runtimeAliasALVal := by
    simp [PathConflicts]
  have hxy : runtimeAliasXName = runtimeAliasYName :=
    hsafe runtimeAliasXName runtimeAliasYName runtimeAliasXSlot
      runtimeAliasYSlot (.value runtimeAliasBorrowedA)
      (.value runtimeAliasBorrowedA) runtimeAliasEnv_x runtimeAliasEnv_y
      runtimeAliasStore_x runtimeAliasStore_y xEvidence yEvidence false
      [runtimeAliasALVal] [runtimeAliasALVal] runtimeAliasALVal
      runtimeAliasALVal hxSelected hySelected hconflict
  simp [runtimeAliasXName, runtimeAliasYName] at hxy

/--
The selected-runtime issue is not only proof bureaucracy.  If `x` selects `a`
while `y` selects `*a`, replacing the box stored in `a` and dropping the old box
leaves `y` pointing at the erased heap cell.  The initial store still safely
abstracts the static environment, so ordinary `S ∼ Γ` is too weak for the
assignment-through-borrow frame step.
-/
def staleAName : Name := "a"
def staleXName : Name := "x"
def staleYName : Name := "y"

def staleALVal : LVal := .var staleAName
def staleXLVal : LVal := .var staleXName
def staleDerefALVal : LVal := .deref staleALVal

def staleHeapOld : Location := .heap 1
def staleHeapNew : Location := .heap 2

def staleASlot : EnvSlot :=
  { ty := .ty (.box .int), lifetime := Lifetime.root }

def staleXSlot : EnvSlot :=
  { ty := .ty (.borrow true [staleALVal]), lifetime := Lifetime.root }

def staleYSlot : EnvSlot :=
  { ty := .ty (.borrow false [staleDerefALVal]),
    lifetime := Lifetime.root }

def staleEnv : Env :=
  { slotAt := fun z =>
      if z = staleAName then some staleASlot
      else if z = staleXName then some staleXSlot
      else if z = staleYName then some staleYSlot
      else none }

def staleOwnedOld : Value :=
  .ref { location := staleHeapOld, owner := true }

def staleOwnedNew : Value :=
  .ref { location := staleHeapNew, owner := true }

def staleBorrowA : Value :=
  .ref { location := .var staleAName, owner := false }

def staleBorrowOldDerefA : Value :=
  .ref { location := staleHeapOld, owner := false }

def staleStore : ProgramStore :=
  { slotAt := fun location =>
      if location = .var staleAName then
        some { value := .value staleOwnedOld, lifetime := Lifetime.root }
      else if location = staleHeapOld then
        some { value := .value (.int 0), lifetime := Lifetime.root }
      else if location = staleHeapNew then
        some { value := .value (.int 1), lifetime := Lifetime.root }
      else if location = .var staleXName then
        some { value := .value staleBorrowA, lifetime := Lifetime.root }
      else if location = .var staleYName then
        some { value := .value staleBorrowOldDerefA, lifetime := Lifetime.root }
      else none }

def staleFinalStore : ProgramStore :=
  (staleStore.update (.var staleAName)
    { value := .value staleOwnedNew, lifetime := Lifetime.root }).erase
      staleHeapOld

theorem staleEnv_a :
    staleEnv.slotAt staleAName = some staleASlot := by
  simp [staleEnv, staleAName]

theorem staleEnv_x :
    staleEnv.slotAt staleXName = some staleXSlot := by
  simp [staleEnv, staleXName, staleAName]

theorem staleEnv_y :
    staleEnv.slotAt staleYName = some staleYSlot := by
  simp [staleEnv, staleYName, staleXName, staleAName]

theorem staleDerefA_not_full_typed :
    ¬ ∃ ty lifetime, LValTyping staleEnv staleDerefALVal (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htyping⟩
  cases htyping with
  | box hsource =>
      rcases LValTyping.var_inv hsource with ⟨slot, hslot, hty, _hlifetime⟩
      have hslotEq : slot = staleASlot :=
        Option.some.inj (hslot.symm.trans staleEnv_a)
      subst hslotEq
      simp [staleASlot] at hty
  | borrow hsource _htargets =>
      rcases LValTyping.var_inv hsource with ⟨slot, hslot, hty, _hlifetime⟩
      have hslotEq : slot = staleASlot :=
        Option.some.inj (hslot.symm.trans staleEnv_a)
      subst hslotEq
      simp [staleASlot] at hty

/--
The stale target graph is admissible for plain safe abstraction, but it is not a
well-formed typing environment: the slot `y : &[*a]` would require `*a` to have
a full lvalue type, while `a` itself has the full value type `Box<Int>`.
-/
theorem staleEnv_not_wellFormed :
    ¬ WellFormedEnv staleEnv Lifetime.root := by
  intro hwellFormed
  have hcontains :
      staleEnv ⊢ staleYName ↝ Ty.borrow false [staleDerefALVal] :=
    ⟨staleYSlot, staleEnv_y, PartialTyContains.here⟩
  obtain ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩ :=
    hwellFormed.1 staleYName staleYSlot false [staleDerefALVal] staleEnv_y
      hcontains staleDerefALVal (by simp)
  exact staleDerefA_not_full_typed
    ⟨targetTy, targetLifetime, htargetTyping⟩

theorem staleEnv_not_borrowSafe :
    ¬ BorrowSafeEnv staleEnv := by
  intro hsafe
  have hx : staleEnv ⊢ staleXName ↝ Ty.borrow true [staleALVal] :=
    ⟨staleXSlot, staleEnv_x, PartialTyContains.here⟩
  have hy : staleEnv ⊢ staleYName ↝ Ty.borrow false [staleDerefALVal] :=
    ⟨staleYSlot, staleEnv_y, PartialTyContains.here⟩
  have hxy := hsafe staleXName staleYName false [staleALVal]
    [staleDerefALVal] staleALVal staleDerefALVal hx hy
    (by simp) (by simp)
    (by simp [PathConflicts, staleALVal, staleDerefALVal, LVal.base])
  simp [staleXName, staleYName] at hxy

theorem staleStore_a :
    staleStore.slotAt (VariableProjection staleAName) =
      some { value := .value staleOwnedOld, lifetime := Lifetime.root } := by
  simp [staleStore, VariableProjection, staleAName]

theorem staleStore_heapOld :
    staleStore.slotAt staleHeapOld =
      some { value := .value (.int 0), lifetime := Lifetime.root } := by
  simp [staleStore, staleHeapOld, staleAName]

theorem staleStore_heapNew :
    staleStore.slotAt staleHeapNew =
      some { value := .value (.int 1), lifetime := Lifetime.root } := by
  simp [staleStore, staleHeapNew, staleHeapOld, staleAName]

theorem staleStore_x :
    staleStore.slotAt (VariableProjection staleXName) =
      some { value := .value staleBorrowA, lifetime := Lifetime.root } := by
  simp [staleStore, VariableProjection, staleXName, staleHeapNew, staleHeapOld,
    staleAName]

theorem staleStore_y :
    staleStore.slotAt (VariableProjection staleYName) =
      some { value := .value staleBorrowOldDerefA, lifetime := Lifetime.root } := by
  simp [staleStore, VariableProjection, staleYName, staleXName, staleHeapNew,
    staleHeapOld, staleAName]

theorem staleStore_loc_a :
    staleStore.loc staleALVal = some (.var staleAName) := by
  simp [staleALVal]

theorem staleStore_loc_deref_a :
    staleStore.loc staleDerefALVal = some staleHeapOld := by
  simp [ProgramStore.loc, staleDerefALVal, staleALVal, staleStore,
    staleOwnedOld, staleHeapOld, staleAName]

theorem staleFinalStore_y :
    staleFinalStore.slotAt (VariableProjection staleYName) =
      some { value := .value staleBorrowOldDerefA, lifetime := Lifetime.root } := by
  simp [staleFinalStore, ProgramStore.update, ProgramStore.erase, staleStore,
    VariableProjection, staleYName, staleXName, staleAName, staleHeapNew,
    staleHeapOld]

theorem staleFinalStore_loc_deref_a :
    staleFinalStore.loc staleDerefALVal = some staleHeapNew := by
  simp [ProgramStore.loc, staleDerefALVal, staleALVal, staleFinalStore,
    ProgramStore.update, ProgramStore.erase, staleOwnedNew, staleHeapOld,
    staleHeapNew, staleAName]

theorem staleStore_safe :
    staleStore ∼ₛ staleEnv := by
  constructor
  · intro z
    constructor
    · intro hstore
      by_cases ha : z = staleAName
      · subst ha
        exact ⟨staleASlot, staleEnv_a⟩
      · by_cases hx : z = staleXName
        · subst hx
          exact ⟨staleXSlot, staleEnv_x⟩
        · by_cases hy : z = staleYName
          · subst hy
            exact ⟨staleYSlot, staleEnv_y⟩
          · rcases hstore with ⟨slot, hslot⟩
            simp [staleStore, VariableProjection, staleHeapNew, staleHeapOld,
              ha, hx, hy] at hslot
    · intro henv
      by_cases ha : z = staleAName
      · subst ha
        exact ⟨{ value := .value staleOwnedOld, lifetime := Lifetime.root },
          staleStore_a⟩
      · by_cases hx : z = staleXName
        · subst hx
          exact ⟨{ value := .value staleBorrowA, lifetime := Lifetime.root },
            staleStore_x⟩
        · by_cases hy : z = staleYName
          · subst hy
            exact ⟨(StoreSlot.mk (.value staleBorrowOldDerefA) Lifetime.root),
              staleStore_y⟩
          · rcases henv with ⟨slot, hslot⟩
            simp [staleEnv, ha, hx, hy] at hslot
  · intro z envSlot henv
    by_cases ha : z = staleAName
    · subst ha
      have hslotEq : envSlot = staleASlot :=
        Option.some.inj (henv.symm.trans staleEnv_a)
      subst hslotEq
      exact ⟨.value staleOwnedOld, staleStore_a,
        ValidPartialValue.boxFull staleStore_heapOld ValidPartialValue.int⟩
    · by_cases hx : z = staleXName
      · subst hx
        have hslotEq : envSlot = staleXSlot :=
          Option.some.inj (henv.symm.trans staleEnv_x)
        subst hslotEq
        exact ⟨.value staleBorrowA, staleStore_x,
          ValidPartialValue.borrow (target := staleALVal) (by simp)
            staleStore_loc_a⟩
      · by_cases hy : z = staleYName
        · subst hy
          have hslotEq : envSlot = staleYSlot :=
            Option.some.inj (henv.symm.trans staleEnv_y)
          subst hslotEq
          exact ⟨.value staleBorrowOldDerefA, staleStore_y,
            ValidPartialValue.borrow (target := staleDerefALVal) (by simp)
              staleStore_loc_deref_a⟩
        · simp [staleEnv, ha, hx, hy] at henv

theorem staleFinalStore_not_safe :
    ¬ staleFinalStore ∼ₛ staleEnv := by
  intro hsafe
  rcases hsafe.2 staleYName staleYSlot staleEnv_y with
    ⟨value, hstore, hvalid⟩
  have hvalueEq : value = .value staleBorrowOldDerefA := by
    have hslotEq :
        { value := value, lifetime := Lifetime.root } =
          ({ value := .value staleBorrowOldDerefA,
              lifetime := Lifetime.root } : StoreSlot) :=
      Option.some.inj (hstore.symm.trans staleFinalStore_y)
    exact congrArg StoreSlot.value hslotEq
  subst hvalueEq
  cases hvalid with
  | borrow hmem hloc =>
      simp at hmem
      subst hmem
      have hlocNew := staleFinalStore_loc_deref_a
      rw [hloc] at hlocNew
      cases hlocNew

/--
A well-typed-shape stale-retarget configuration for the relaxed preservation
frontier.

The important shape is:

* `s : &mut[p]`
* `p : &mut[a]`
* `y : &[*p]`

The store initially has `s` pointing at `p`, `p` pointing at `a`, and `y`
pointing at the runtime resolution of `*p`, namely `a`.  Retargeting `p` to `b`
leaves `y` stale: its concrete reference still points at `a`, but its static
target `*p` now resolves to `b`.
-/
def retargetAName : Name := "retarget_a"
def retargetBName : Name := "retarget_b"
def retargetPName : Name := "retarget_p"
def retargetSName : Name := "retarget_s"
def retargetYName : Name := "retarget_y"

def retargetALVal : LVal := .var retargetAName
def retargetBLVal : LVal := .var retargetBName
def retargetPLVal : LVal := .var retargetPName
def retargetSLVal : LVal := .var retargetSName
def retargetDerefPLVal : LVal := .deref retargetPLVal
def retargetDerefDerefSLVal : LVal := .deref (.deref retargetSLVal)

def retargetIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def retargetPSlot : EnvSlot :=
  { ty := .ty (.borrow true [retargetALVal]), lifetime := Lifetime.root }

def retargetSSlot : EnvSlot :=
  { ty := .ty (.borrow true [retargetPLVal]), lifetime := Lifetime.root }

def retargetYSlot : EnvSlot :=
  { ty := .ty (.borrow false [retargetDerefPLVal]),
    lifetime := Lifetime.root }

def retargetEnv : Env :=
  { slotAt := fun z =>
      if z = retargetAName then some retargetIntSlot
      else if z = retargetBName then some retargetIntSlot
      else if z = retargetPName then some retargetPSlot
      else if z = retargetSName then some retargetSSlot
      else if z = retargetYName then some retargetYSlot
      else none }

def retargetBorrowA : Value :=
  .ref { location := .var retargetAName, owner := false }

def retargetBorrowB : Value :=
  .ref { location := .var retargetBName, owner := false }

def retargetBorrowP : Value :=
  .ref { location := .var retargetPName, owner := false }

def retargetStore : ProgramStore :=
  { slotAt := fun location =>
      if location = .var retargetAName then
        some { value := .value (.int 0), lifetime := Lifetime.root }
      else if location = .var retargetBName then
        some { value := .value (.int 1), lifetime := Lifetime.root }
      else if location = .var retargetPName then
        some { value := .value retargetBorrowA, lifetime := Lifetime.root }
      else if location = .var retargetSName then
        some { value := .value retargetBorrowP, lifetime := Lifetime.root }
      else if location = .var retargetYName then
        some { value := .value retargetBorrowA, lifetime := Lifetime.root }
      else none }

def retargetStoreAfter : ProgramStore :=
  retargetStore.update (.var retargetPName)
    { value := .value retargetBorrowB, lifetime := Lifetime.root }

def retargetOldPStoreSlot : StoreSlot :=
  { value := .value retargetBorrowA, lifetime := Lifetime.root }

theorem retargetEnv_a :
    retargetEnv.slotAt retargetAName = some retargetIntSlot := by
  simp [retargetEnv, retargetAName]

theorem retargetEnv_b :
    retargetEnv.slotAt retargetBName = some retargetIntSlot := by
  simp [retargetEnv, retargetBName, retargetAName]

theorem retargetEnv_p :
    retargetEnv.slotAt retargetPName = some retargetPSlot := by
  simp [retargetEnv, retargetPName, retargetBName, retargetAName]

theorem retargetEnv_s :
    retargetEnv.slotAt retargetSName = some retargetSSlot := by
  simp [retargetEnv, retargetSName, retargetPName, retargetBName,
    retargetAName]

theorem retargetEnv_y :
    retargetEnv.slotAt retargetYName = some retargetYSlot := by
  simp [retargetEnv, retargetYName, retargetSName, retargetPName,
    retargetBName, retargetAName]

theorem retarget_a_typing :
    LValTyping retargetEnv retargetALVal (.ty .int) Lifetime.root := by
  exact LValTyping.var retargetEnv_a

theorem retarget_b_typing :
    LValTyping retargetEnv retargetBLVal (.ty .int) Lifetime.root := by
  exact LValTyping.var retargetEnv_b

theorem retarget_p_typing :
    LValTyping retargetEnv retargetPLVal
      (.ty (.borrow true [retargetALVal])) Lifetime.root := by
  exact LValTyping.var retargetEnv_p

theorem retarget_s_typing :
    LValTyping retargetEnv retargetSLVal
      (.ty (.borrow true [retargetPLVal])) Lifetime.root := by
  exact LValTyping.var retargetEnv_s

theorem retarget_y_typing :
    LValTyping retargetEnv (.var retargetYName)
      (.ty (.borrow false [retargetDerefPLVal])) Lifetime.root := by
  exact LValTyping.var retargetEnv_y

theorem retarget_deref_p_typing :
    LValTyping retargetEnv retargetDerefPLVal (.ty .int) Lifetime.root := by
  exact LValTyping.borrow retarget_p_typing
    (LValTargetsTyping.singleton retarget_a_typing)

theorem retarget_deref_s_typing :
    LValTyping retargetEnv (.deref retargetSLVal)
      (.ty (.borrow true [retargetALVal])) Lifetime.root := by
  exact LValTyping.borrow retarget_s_typing
    (LValTargetsTyping.singleton retarget_p_typing)

theorem retarget_strictPrefix_misses_alias_path :
    ¬ LVal.StrictPrefixOf retargetPLVal retargetDerefDerefSLVal := by
  intro hprefix
  simpa [LVal.StrictPrefixOf, retargetPLVal, retargetDerefDerefSLVal,
    retargetSLVal, LVal.base, retargetPName, retargetSName] using hprefix.1

theorem retarget_mayReadThrough_catches_alias_path :
    EnvMayReadThrough retargetEnv retargetPLVal retargetDerefDerefSLVal := by
  exact EnvMayReadThrough.borrowTarget_deref_deref retarget_s_typing (by simp)

theorem retargetEnv_contained :
    ContainedBorrowsWellFormed retargetEnv := by
  intro root slot mutable targets hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases ha : root = retargetAName
  · subst ha
    have hcontainedTy : containedSlot.ty = .ty .int := by
      simpa [retargetEnv, retargetIntSlot, retargetAName] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
          hcontainedSlot).symm
    rw [hcontainedTy] at hcontainsTy
    cases hcontainsTy
  · by_cases hb : root = retargetBName
    · subst hb
      have hcontainedTy : containedSlot.ty = .ty .int := by
        simpa [retargetEnv, retargetIntSlot, retargetBName, retargetAName] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
            hcontainedSlot).symm
      rw [hcontainedTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hp : root = retargetPName
      · subst hp
        have hcontainedTy :
            containedSlot.ty = .ty (.borrow true [retargetALVal]) := by
          simpa [retargetEnv, retargetPSlot, retargetPName, retargetBName,
            retargetAName] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hcontainedSlot).symm
        rw [hcontainedTy] at hcontainsTy
        cases hcontainsTy with
        | here =>
            intro target htarget
            simp at htarget
            subst htarget
            exact ⟨.int, Lifetime.root, retarget_a_typing,
              LifetimeOutlives.refl Lifetime.root,
              ⟨retargetIntSlot, by
                simp [retargetEnv, retargetALVal, retargetAName, LVal.base],
                LifetimeOutlives.refl Lifetime.root⟩⟩
      · by_cases hs : root = retargetSName
        · subst hs
          have hcontainedTy :
              containedSlot.ty = .ty (.borrow true [retargetPLVal]) := by
            simpa [retargetEnv, retargetSSlot, retargetSName, retargetPName,
              retargetBName, retargetAName] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                hcontainedSlot).symm
          rw [hcontainedTy] at hcontainsTy
          cases hcontainsTy with
          | here =>
              intro target htarget
              simp at htarget
              subst htarget
              exact ⟨.borrow true [retargetALVal], Lifetime.root,
                retarget_p_typing, LifetimeOutlives.refl Lifetime.root,
                ⟨retargetPSlot, by
                  simp [retargetEnv, retargetPLVal, retargetPName,
                    retargetBName, retargetAName, LVal.base],
                  LifetimeOutlives.refl Lifetime.root⟩⟩
        · by_cases hy : root = retargetYName
          · subst hy
            have hcontainedTy :
                containedSlot.ty =
                  .ty (.borrow false [retargetDerefPLVal]) := by
              simpa [retargetEnv, retargetYSlot, retargetYName, retargetSName,
                retargetPName, retargetBName, retargetAName] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                  hcontainedSlot).symm
            rw [hcontainedTy] at hcontainsTy
            cases hcontainsTy with
            | here =>
                intro target htarget
                simp at htarget
                subst htarget
                exact ⟨.int, Lifetime.root, retarget_deref_p_typing,
                  LifetimeOutlives.refl Lifetime.root,
                  ⟨retargetPSlot, by
                    simp [retargetEnv, retargetDerefPLVal, retargetPLVal,
                      retargetPName, retargetBName, retargetAName, LVal.base],
                    LifetimeOutlives.refl Lifetime.root⟩⟩
          · have hnone : retargetEnv.slotAt root = none := by
              simp [retargetEnv, ha, hb, hp, hs, hy]
            rw [hslot] at hnone
            cases hnone

def retargetRank (name : Name) : Nat :=
  if name = retargetSName then 2
  else if name = retargetYName then 2
  else if name = retargetPName then 1
  else 0

theorem retargetEnv_linearized :
    LinearizedBy retargetRank retargetEnv := by
  intro root slot hslot v hv
  by_cases ha : root = retargetAName
  · subst ha
    have hslotTy : slot.ty = .ty .int := by
      simpa [retargetEnv, retargetIntSlot, retargetAName] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hv
    simp [PartialTy.vars, Ty.vars] at hv
  · by_cases hb : root = retargetBName
    · subst hb
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetEnv, retargetIntSlot, retargetBName, retargetAName] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · by_cases hp : root = retargetPName
      · subst hp
        have hslotTy :
            slot.ty = .ty (.borrow true [retargetALVal]) := by
          simpa [retargetEnv, retargetPSlot, retargetPName, retargetBName,
            retargetAName] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars, retargetALVal] at hv
        subst v
        simp [retargetRank, LVal.base, retargetAName,
          retargetPName, retargetSName, retargetYName]
      · by_cases hs : root = retargetSName
        · subst hs
          have hslotTy :
              slot.ty = .ty (.borrow true [retargetPLVal]) := by
            simpa [retargetEnv, retargetSSlot, retargetSName, retargetPName,
              retargetBName, retargetAName] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                hslot).symm
          rw [hslotTy] at hv
          simp [PartialTy.vars, Ty.vars, retargetPLVal] at hv
          subst v
          simp [retargetRank, LVal.base, retargetPName,
            retargetSName, retargetYName]
        · by_cases hy : root = retargetYName
          · subst hy
            have hslotTy :
                slot.ty =
                  .ty (.borrow false [retargetDerefPLVal]) := by
              simpa [retargetEnv, retargetYSlot, retargetYName, retargetSName,
                retargetPName, retargetBName, retargetAName] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                  hslot).symm
            rw [hslotTy] at hv
            simp [PartialTy.vars, Ty.vars, retargetDerefPLVal, retargetPLVal] at hv
            subst v
            simp [retargetRank, LVal.base,
              retargetPName, retargetYName, retargetSName]
          · have hnone : retargetEnv.slotAt root = none := by
              simp [retargetEnv, ha, hb, hp, hs, hy]
            rw [hslot] at hnone
            cases hnone

theorem retargetEnv_linearizable :
    Linearizable retargetEnv :=
  ⟨retargetRank, retargetEnv_linearized⟩

theorem retargetEnv_slotsOutlive :
    EnvSlotsOutlive retargetEnv Lifetime.root := by
  intro root slot hslot
  by_cases ha : root = retargetAName
  · subst ha
    have hslotEq : slot = retargetIntSlot :=
      Option.some.inj (hslot.symm.trans retargetEnv_a)
    subst hslotEq
    exact LifetimeOutlives.refl Lifetime.root
  · by_cases hb : root = retargetBName
    · subst hb
      have hslotEq : slot = retargetIntSlot :=
        Option.some.inj (hslot.symm.trans retargetEnv_b)
      subst hslotEq
      exact LifetimeOutlives.refl Lifetime.root
    · by_cases hp : root = retargetPName
      · subst hp
        have hslotEq : slot = retargetPSlot :=
          Option.some.inj (hslot.symm.trans retargetEnv_p)
        subst hslotEq
        exact LifetimeOutlives.refl Lifetime.root
      · by_cases hs : root = retargetSName
        · subst hs
          have hslotEq : slot = retargetSSlot :=
            Option.some.inj (hslot.symm.trans retargetEnv_s)
          subst hslotEq
          exact LifetimeOutlives.refl Lifetime.root
        · by_cases hy : root = retargetYName
          · subst hy
            have hslotEq : slot = retargetYSlot :=
              Option.some.inj (hslot.symm.trans retargetEnv_y)
            subst hslotEq
            exact LifetimeOutlives.refl Lifetime.root
          · have hnone : retargetEnv.slotAt root = none := by
              simp [retargetEnv, ha, hb, hp, hs, hy]
            rw [hslot] at hnone
            cases hnone

theorem retargetEnv_no_box_typing :
    ∀ {lv inner lifetime},
      ¬ LValTyping retargetEnv lv (.box inner) lifetime := by
  intro lv
  induction lv with
  | var root =>
      intro inner lifetime htyping
      generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
      cases htyping with
      | var hslot =>
          rename_i slot
          by_cases ha : root = retargetAName
          · subst ha
            have hslotEq : slot = retargetIntSlot :=
              Option.some.inj (hslot.symm.trans retargetEnv_a)
            subst hslotEq
            simp [retargetIntSlot] at hpartialTy
          · by_cases hb : root = retargetBName
            · subst hb
              have hslotEq : slot = retargetIntSlot :=
                Option.some.inj (hslot.symm.trans retargetEnv_b)
              subst hslotEq
              simp [retargetIntSlot] at hpartialTy
            · by_cases hp : root = retargetPName
              · subst hp
                have hslotEq : slot = retargetPSlot :=
                  Option.some.inj (hslot.symm.trans retargetEnv_p)
                subst hslotEq
                simp [retargetPSlot] at hpartialTy
              · by_cases hs : root = retargetSName
                · subst hs
                  have hslotEq : slot = retargetSSlot :=
                    Option.some.inj (hslot.symm.trans retargetEnv_s)
                  subst hslotEq
                  simp [retargetSSlot] at hpartialTy
                · by_cases hy : root = retargetYName
                  · subst hy
                    have hslotEq : slot = retargetYSlot :=
                      Option.some.inj (hslot.symm.trans retargetEnv_y)
                    subst hslotEq
                    simp [retargetYSlot] at hpartialTy
                  · have hnone : retargetEnv.slotAt root = none := by
                      simp [retargetEnv, ha, hb, hp, hs, hy]
                    rw [hslot] at hnone
                    cases hnone
  | deref lv ih =>
      intro inner lifetime htyping
      cases htyping with
      | box hinner =>
          exact ih hinner
      | borrow _hinner htargets =>
          exact LValTargetsTyping.not_box htargets

theorem retarget_a_full_typing_int {ty : Ty} {lifetime : Lifetime} :
    LValTyping retargetEnv retargetALVal (.ty ty) lifetime →
    ty = .int ∧ lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetIntSlot :=
    Option.some.inj (hslot.symm.trans retargetEnv_a)
  subst hslotEq
  simp [retargetIntSlot] at hty hlifetime
  exact ⟨hty.symm, hlifetime.symm⟩

theorem retarget_b_full_typing_int {ty : Ty} {lifetime : Lifetime} :
    LValTyping retargetEnv retargetBLVal (.ty ty) lifetime →
    ty = .int ∧ lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetIntSlot :=
    Option.some.inj (hslot.symm.trans retargetEnv_b)
  subst hslotEq
  simp [retargetIntSlot] at hty hlifetime
  exact ⟨hty.symm, hlifetime.symm⟩

theorem retarget_p_borrow_typing_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTyping retargetEnv retargetPLVal
      (.ty (.borrow mutable targets)) lifetime →
    mutable = true ∧ targets = [retargetALVal] ∧
      lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetPSlot :=
    Option.some.inj (hslot.symm.trans retargetEnv_p)
  subst hslotEq
  simp [retargetPSlot] at hty hlifetime
  rcases hty with ⟨hmutable, htargets⟩
  exact ⟨hmutable, htargets.symm, hlifetime.symm⟩

theorem retarget_s_borrow_typing_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTyping retargetEnv retargetSLVal
      (.ty (.borrow mutable targets)) lifetime →
    mutable = true ∧ targets = [retargetPLVal] ∧
      lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetSSlot :=
    Option.some.inj (hslot.symm.trans retargetEnv_s)
  subst hslotEq
  simp [retargetSSlot] at hty hlifetime
  rcases hty with ⟨hmutable, htargets⟩
  exact ⟨hmutable, htargets.symm, hlifetime.symm⟩

theorem retarget_y_borrow_typing_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTyping retargetEnv (.var retargetYName)
      (.ty (.borrow mutable targets)) lifetime →
    mutable = false ∧ targets = [retargetDerefPLVal] ∧
      lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetYSlot :=
    Option.some.inj (hslot.symm.trans retargetEnv_y)
  subst hslotEq
  simp [retargetYSlot] at hty hlifetime
  rcases hty with ⟨hmutable, htargets⟩
  exact ⟨hmutable, htargets.symm, hlifetime.symm⟩

theorem retarget_a_targets_not_borrow
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTargetsTyping retargetEnv [retargetALVal]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      rcases retarget_a_full_typing_int htarget with ⟨hty, _hlifetime⟩
      cases hty
  | cons _hhead hrest _hunion _hlifetime =>
      have hne := LValTargetsTyping.targets_ne_nil hrest
      simp at hne

theorem retarget_p_targets_borrow_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTargetsTyping retargetEnv [retargetPLVal]
      (.ty (.borrow mutable targets)) lifetime →
    mutable = true ∧ targets = [retargetALVal] ∧
      lifetime = Lifetime.root := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      exact retarget_p_borrow_typing_facts htarget
  | cons _hhead hrest _hunion _hlifetime =>
      have hne := LValTargetsTyping.targets_ne_nil hrest
      simp at hne

theorem retarget_deref_p_full_typing_int
    {ty : Ty} {lifetime : Lifetime} :
    LValTyping retargetEnv retargetDerefPLVal (.ty ty) lifetime →
    ty = .int ∧ lifetime = Lifetime.root := by
  intro htyping
  cases htyping with
  | box hinner =>
      exact False.elim (retargetEnv_no_box_typing hinner)
  | borrow hinner htargets =>
      rcases retarget_p_borrow_typing_facts hinner with
        ⟨_hmutable, htargetsEq, _hlifetime⟩
      subst htargetsEq
      cases htargets with
      | singleton htarget =>
          exact retarget_a_full_typing_int htarget
      | cons _hhead hrest _hunion _hlifetime =>
          have hne := LValTargetsTyping.targets_ne_nil hrest
          simp at hne

theorem retarget_deref_p_targets_not_borrow
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTargetsTyping retargetEnv [retargetDerefPLVal]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      rcases retarget_deref_p_full_typing_int htarget with
        ⟨hty, _hlifetime⟩
      cases hty
  | cons _hhead hrest _hunion _hlifetime =>
      have hne := LValTargetsTyping.targets_ne_nil hrest
      simp at hne

theorem retarget_deref_s_borrow_typing_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTyping retargetEnv (.deref retargetSLVal)
      (.ty (.borrow mutable targets)) lifetime →
    mutable = true ∧ targets = [retargetALVal] ∧
      lifetime = Lifetime.root := by
  intro htyping
  cases htyping with
  | box hinner =>
      exact False.elim (retargetEnv_no_box_typing hinner)
  | borrow hinner htargets =>
      rcases retarget_s_borrow_typing_facts hinner with
        ⟨_hmutable, htargetsEq, _hlifetime⟩
      subst htargetsEq
      exact retarget_p_targets_borrow_facts htargets

theorem retargetEnv_borrow_lval_facts :
    ∀ {lv mutable targets lifetime},
      LValTyping retargetEnv lv (.ty (.borrow mutable targets)) lifetime →
      (lv = retargetPLVal ∧ mutable = true ∧
          targets = [retargetALVal] ∧ lifetime = Lifetime.root) ∨
      (lv = retargetSLVal ∧ mutable = true ∧
          targets = [retargetPLVal] ∧ lifetime = Lifetime.root) ∨
      (lv = .var retargetYName ∧ mutable = false ∧
          targets = [retargetDerefPLVal] ∧ lifetime = Lifetime.root) ∨
      (lv = .deref retargetSLVal ∧ mutable = true ∧
          targets = [retargetALVal] ∧ lifetime = Lifetime.root) := by
  intro lv
  induction lv with
  | var root =>
      intro mutable targets lifetime htyping
      generalize hpartialTy :
        (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
      cases htyping with
      | var hslot =>
          rename_i slot
          by_cases ha : root = retargetAName
          · subst ha
            have hslotEq : slot = retargetIntSlot :=
              Option.some.inj (hslot.symm.trans retargetEnv_a)
            subst hslotEq
            simp [retargetIntSlot] at hpartialTy
          · by_cases hb : root = retargetBName
            · subst hb
              have hslotEq : slot = retargetIntSlot :=
                Option.some.inj (hslot.symm.trans retargetEnv_b)
              subst hslotEq
              simp [retargetIntSlot] at hpartialTy
            · by_cases hp : root = retargetPName
              · subst hp
                have hslotEq : slot = retargetPSlot :=
                  Option.some.inj (hslot.symm.trans retargetEnv_p)
                subst hslotEq
                simp [retargetPSlot] at hpartialTy
                rcases hpartialTy with ⟨hmutable, htargets⟩
                left
                exact ⟨rfl, hmutable, htargets, rfl⟩
              · by_cases hs : root = retargetSName
                · subst hs
                  have hslotEq : slot = retargetSSlot :=
                    Option.some.inj (hslot.symm.trans retargetEnv_s)
                  subst hslotEq
                  simp [retargetSSlot] at hpartialTy
                  rcases hpartialTy with ⟨hmutable, htargets⟩
                  right
                  left
                  exact ⟨rfl, hmutable, htargets, rfl⟩
                · by_cases hy : root = retargetYName
                  · subst hy
                    have hslotEq : slot = retargetYSlot :=
                      Option.some.inj (hslot.symm.trans retargetEnv_y)
                    subst hslotEq
                    simp [retargetYSlot] at hpartialTy
                    rcases hpartialTy with ⟨hmutable, htargets⟩
                    right
                    right
                    left
                    exact ⟨rfl, hmutable, htargets, rfl⟩
                  · have hnone : retargetEnv.slotAt root = none := by
                      simp [retargetEnv, ha, hb, hp, hs, hy]
                    rw [hslot] at hnone
                    cases hnone
  | deref lv ih =>
      intro mutable targets lifetime htyping
      cases htyping with
      | box hinner =>
          exact False.elim (retargetEnv_no_box_typing hinner)
      | borrow hinner htargets =>
          rcases ih hinner with hp | hs | hy | hds
          · rcases hp with ⟨hlv, _hmutable, htargetsEq, _hlifetime⟩
            subst hlv
            subst htargetsEq
            exact False.elim (retarget_a_targets_not_borrow htargets)
          · rcases hs with ⟨hlv, _hmutable, htargetsEq, _hlifetime⟩
            subst hlv
            subst htargetsEq
            rcases retarget_p_targets_borrow_facts htargets with
              ⟨hmutable, htargetsOuter, hlifetimeOuter⟩
            right
            right
            right
            exact ⟨rfl, hmutable, htargetsOuter, hlifetimeOuter⟩
          · rcases hy with ⟨hlv, _hmutable, htargetsEq, _hlifetime⟩
            subst hlv
            subst htargetsEq
            exact False.elim (retarget_deref_p_targets_not_borrow htargets)
          · rcases hds with ⟨hlv, _hmutable, htargetsEq, _hlifetime⟩
            subst hlv
            subst htargetsEq
            exact False.elim (retarget_a_targets_not_borrow htargets)

theorem retargetEnv_coherent :
    Coherent retargetEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases retargetEnv_borrow_lval_facts htyping with hp | hs | hy | hds
  · rcases hp with ⟨_hlv, _hmutable, htargets, _hlifetime⟩
    subst htargets
    exact ⟨.int, Lifetime.root,
      LValTargetsTyping.singleton retarget_a_typing⟩
  · rcases hs with ⟨_hlv, _hmutable, htargets, _hlifetime⟩
    subst htargets
    exact ⟨.borrow true [retargetALVal], Lifetime.root,
      LValTargetsTyping.singleton retarget_p_typing⟩
  · rcases hy with ⟨_hlv, _hmutable, htargets, _hlifetime⟩
    subst htargets
    exact ⟨.int, Lifetime.root,
      LValTargetsTyping.singleton retarget_deref_p_typing⟩
  · rcases hds with ⟨_hlv, _hmutable, htargets, _hlifetime⟩
    subst htargets
    exact ⟨.int, Lifetime.root,
      LValTargetsTyping.singleton retarget_a_typing⟩

theorem retargetEnv_wellFormed :
    WellFormedEnv retargetEnv Lifetime.root :=
  ⟨retargetEnv_contained, retargetEnv_slotsOutlive, retargetEnv_coherent,
    retargetEnv_linearizable⟩

theorem retarget_partialTyStrengthens_borrow_append {mutable : Bool}
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
        ⟨targetTargets, htargetEq, hsubLeft⟩
      cases htargetEq
      have hsubRight : rightTargets ⊆ targetTargets := by
        cases hright with
        | intoUndef hinner' => exact PartialTyStrengthens.borrow_subset hinner'
      exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem))

theorem retarget_join_borrow_a_b :
    PartialTyJoin (.ty (.borrow true [retargetALVal]))
      (.ty (.borrow true [retargetBLVal]))
      (.ty (.borrow true [retargetALVal, retargetBLVal])) := by
  refine ⟨?upper, ?least⟩
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget
        subst htarget
        simp)
    · subst hcandidate
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget
        subst htarget
        simp)
  · intro upper hupper
    have hleft : PartialTyStrengthens (.ty (.borrow true [retargetALVal])) upper :=
      hupper (.ty (.borrow true [retargetALVal])) (by simp)
    have hright : PartialTyStrengthens (.ty (.borrow true [retargetBLVal])) upper :=
      hupper (.ty (.borrow true [retargetBLVal])) (by simp)
    simpa using
      (retarget_partialTyStrengthens_borrow_append hleft hright)

def retargetPJoinedSlot : EnvSlot :=
  { ty := .ty (.borrow true [retargetALVal, retargetBLVal]),
    lifetime := Lifetime.root }

def retargetWriteInnerEnv : Env :=
  retargetEnv.update retargetPName retargetPJoinedSlot

def retargetWriteEnv : Env :=
  retargetWriteInnerEnv.update retargetSName retargetSSlot

theorem retarget_shape_borrow_a_b :
    ShapeCompatible retargetEnv
      (.ty (.borrow true [retargetALVal]))
      (.ty (.borrow true [retargetBLVal])) := by
  exact ShapeCompatible.borrow
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, retarget_a_typing⟩)
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, retarget_b_typing⟩)
    ShapeCompatible.int

theorem retarget_write_p_rank1 :
    EnvWrite 1 retargetEnv retargetPLVal
      (.borrow true [retargetBLVal]) retargetWriteInnerEnv := by
  simpa [retargetWriteInnerEnv, retargetPJoinedSlot, retargetPSlot,
    retargetPLVal, LVal.base] using
    (@EnvWrite.intro 1 retargetEnv retargetEnv retargetPLVal
      retargetPSlot (.borrow true [retargetBLVal])
      (.ty (.borrow true [retargetALVal, retargetBLVal]))
      retargetEnv_p
      (by
        simpa [retargetPSlot, retargetPLVal, LVal.path] using
          (@UpdateAtPath.weak retargetEnv 0
            (.ty (.borrow true [retargetALVal]))
            (.ty (.borrow true [retargetALVal, retargetBLVal]))
            (.borrow true [retargetBLVal])
            retarget_shape_borrow_a_b retarget_join_borrow_a_b)))

theorem retarget_write_targets_p_rank1 :
    WriteBorrowTargets 1 retargetEnv [] [retargetPLVal]
      (.borrow true [retargetBLVal]) retargetWriteInnerEnv := by
  exact WriteBorrowTargets.singleton retarget_write_p_rank1
    ⟨.borrow true [retargetALVal], Lifetime.root, by
      simpa [prependPath] using retarget_p_typing⟩

theorem retarget_write_deref_s :
    EnvWrite 0 retargetEnv (.deref retargetSLVal)
      (.borrow true [retargetBLVal]) retargetWriteEnv := by
  simpa [retargetWriteEnv, retargetSSlot, retargetSLVal, LVal.base,
    LVal.path] using
    (@EnvWrite.intro 0 retargetEnv retargetWriteInnerEnv
      (.deref retargetSLVal) retargetSSlot
      (.borrow true [retargetBLVal])
      (.ty (.borrow true [retargetPLVal]))
      retargetEnv_s
      (@UpdateAtPath.mutBorrow retargetEnv retargetWriteInnerEnv 0 []
        [retargetPLVal] (.borrow true [retargetBLVal])
        retarget_write_targets_p_rank1))

theorem retarget_write_p_rank1_effective_write :
    EnvWriteEffectiveWrite 1 retargetEnv retargetPLVal
      (.borrow true [retargetBLVal]) retargetWriteInnerEnv retargetPLVal := by
  simpa [retargetWriteInnerEnv, retargetPJoinedSlot, retargetPSlot,
    retargetPLVal, LVal.base] using
    (@EnvWriteEffectiveWrite.intro 1 retargetEnv retargetEnv retargetPLVal
      retargetPLVal retargetPSlot (.borrow true [retargetBLVal])
      (.ty (.borrow true [retargetALVal, retargetBLVal]))
      retargetEnv_p
      (by
        simpa [retargetPSlot, retargetPLVal, LVal.base, LVal.path] using
          (@UpdateAtPathEffectiveWrite.weak retargetEnv retargetPName 0
            (.ty (.borrow true [retargetALVal]))
            (.ty (.borrow true [retargetALVal, retargetBLVal]))
            (.borrow true [retargetBLVal])
            retarget_shape_borrow_a_b retarget_join_borrow_a_b)))

theorem retarget_write_targets_p_rank1_effective_write :
    WriteBorrowTargetsEffectiveWrite 1 retargetEnv [] [retargetPLVal]
      (.borrow true [retargetBLVal]) retargetWriteInnerEnv retargetPLVal := by
  exact WriteBorrowTargetsEffectiveWrite.singleton
    retarget_write_p_rank1_effective_write

theorem retarget_write_deref_s_effective_write_p :
    EnvWriteEffectiveWrite 0 retargetEnv (.deref retargetSLVal)
      (.borrow true [retargetBLVal]) retargetWriteEnv retargetPLVal := by
  simpa [retargetWriteEnv, retargetSSlot, retargetSLVal, LVal.base,
    LVal.path] using
    (@EnvWriteEffectiveWrite.intro 0 retargetEnv retargetWriteInnerEnv
      (.deref retargetSLVal) retargetPLVal retargetSSlot
      (.borrow true [retargetBLVal])
      (.ty (.borrow true [retargetPLVal]))
      retargetEnv_s
      (@UpdateAtPathEffectiveWrite.mutBorrow retargetEnv retargetWriteInnerEnv
        retargetSName 0 [] [retargetPLVal]
        (.borrow true [retargetBLVal]) retargetPLVal
        retarget_write_targets_p_rank1_effective_write))

theorem retarget_b_mutable :
    Mutable retargetEnv retargetBLVal :=
  @Mutable.var retargetEnv retargetBName retargetIntSlot retargetEnv_b

theorem retarget_borrow_b_wellFormed :
    WellFormedTy retargetEnv (.borrow true [retargetBLVal])
      Lifetime.root := by
  exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
    intro target htarget
    simp at htarget
    subst htarget
    exact ⟨.int, Lifetime.root, retarget_b_typing,
      LifetimeOutlives.refl Lifetime.root,
      ⟨retargetIntSlot, by
        simp [retargetEnv, retargetBLVal, retargetBName, retargetAName,
          LVal.base],
        LifetimeOutlives.refl Lifetime.root⟩⟩))

theorem retargetEnv_not_writeProhibited_b :
    ¬ WriteProhibited retargetEnv retargetBLVal := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨root, targets, target, hcontains, htarget,
      hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases ha : root = retargetAName
    · subst ha
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetEnv, retargetIntSlot, retargetAName] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hb : root = retargetBName
      · subst hb
        have hslotTy : slot.ty = .ty .int := by
          simpa [retargetEnv, retargetIntSlot, retargetBName, retargetAName] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hp : root = retargetPName
        · subst hp
          have hslotTy :
              slot.ty = .ty (.borrow true [retargetALVal]) := by
            simpa [retargetEnv, retargetPSlot, retargetPName, retargetBName,
              retargetAName] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy with
          | here =>
              simp at htarget
              subst htarget
              simp [PathConflicts, retargetALVal, retargetBLVal, LVal.base,
                retargetAName, retargetBName] at hconflict
        · by_cases hs : root = retargetSName
          · subst hs
            have hslotTy :
                slot.ty = .ty (.borrow true [retargetPLVal]) := by
              simpa [retargetEnv, retargetSSlot, retargetSName, retargetPName,
                retargetBName, retargetAName] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                  hslot).symm
            rw [hslotTy] at hcontainsTy
            cases hcontainsTy with
            | here =>
                simp at htarget
                subst htarget
                simp [PathConflicts, retargetPLVal, retargetBLVal, LVal.base,
                  retargetPName, retargetBName] at hconflict
          · by_cases hy : root = retargetYName
            · subst hy
              have hslotTy :
                  slot.ty =
                    .ty (.borrow false [retargetDerefPLVal]) := by
                simpa [retargetEnv, retargetYSlot, retargetYName, retargetSName,
                  retargetPName, retargetBName, retargetAName] using
                  (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                    hslot).symm
              rw [hslotTy] at hcontainsTy
              cases hcontainsTy
            · have hnone : retargetEnv.slotAt root = none := by
                simp [retargetEnv, ha, hb, hp, hs, hy]
              rw [hslot] at hnone
              cases hnone
  · rcases himm with ⟨root, targets, target, hcontains, htarget,
      hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases ha : root = retargetAName
    · subst ha
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetEnv, retargetIntSlot, retargetAName] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hb : root = retargetBName
      · subst hb
        have hslotTy : slot.ty = .ty .int := by
          simpa [retargetEnv, retargetIntSlot, retargetBName, retargetAName] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hp : root = retargetPName
        · subst hp
          have hslotTy :
              slot.ty = .ty (.borrow true [retargetALVal]) := by
            simpa [retargetEnv, retargetPSlot, retargetPName, retargetBName,
              retargetAName] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · by_cases hs : root = retargetSName
          · subst hs
            have hslotTy :
                slot.ty = .ty (.borrow true [retargetPLVal]) := by
              simpa [retargetEnv, retargetSSlot, retargetSName, retargetPName,
                retargetBName, retargetAName] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                  hslot).symm
            rw [hslotTy] at hcontainsTy
            cases hcontainsTy
          · by_cases hy : root = retargetYName
            · subst hy
              have hslotTy :
                  slot.ty =
                    .ty (.borrow false [retargetDerefPLVal]) := by
                simpa [retargetEnv, retargetYSlot, retargetYName, retargetSName,
                  retargetPName, retargetBName, retargetAName] using
                  (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                    hslot).symm
              rw [hslotTy] at hcontainsTy
              cases hcontainsTy with
              | here =>
                  simp at htarget
                  subst htarget
                  simp [PathConflicts, retargetDerefPLVal, retargetPLVal,
                    retargetBLVal, LVal.base, retargetPName, retargetBName]
                    at hconflict
            · have hnone : retargetEnv.slotAt root = none := by
                simp [retargetEnv, ha, hb, hp, hs, hy]
              rw [hslot] at hnone
              cases hnone

theorem retarget_borrow_b_typing :
    TermTyping retargetEnv StoreTyping.empty Lifetime.root
      (.borrow true retargetBLVal) (.borrow true [retargetBLVal])
      retargetEnv := by
  exact TermTyping.mutBorrow retarget_b_typing retarget_b_mutable
    retargetEnv_not_writeProhibited_b

theorem retargetWriteEnv_a :
    retargetWriteEnv.slotAt retargetAName = some retargetIntSlot := by
  simp [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv, Env.update,
    retargetAName, retargetBName, retargetPName, retargetSName]

theorem retargetWriteEnv_b :
    retargetWriteEnv.slotAt retargetBName = some retargetIntSlot := by
  simp [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv, Env.update,
    retargetAName, retargetBName, retargetPName, retargetSName]

theorem retargetWriteEnv_p :
    retargetWriteEnv.slotAt retargetPName = some retargetPJoinedSlot := by
  simp [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv, Env.update,
    retargetAName, retargetBName, retargetPName, retargetSName]

theorem retargetWriteEnv_s :
    retargetWriteEnv.slotAt retargetSName = some retargetSSlot := by
  simp [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv, Env.update,
    retargetAName, retargetBName, retargetPName, retargetSName]

theorem retargetWriteEnv_y :
    retargetWriteEnv.slotAt retargetYName = some retargetYSlot := by
  simp [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv, Env.update,
    retargetAName, retargetBName, retargetPName, retargetSName,
    retargetYName]

theorem retarget_write_deref_s_not_noStale :
    ¬ EnvWriteNoStaleBorrowTargets 0 retargetEnv (.deref retargetSLVal)
      (.borrow true [retargetBLVal]) retargetWriteEnv := by
  intro hnoStale
  exact hnoStale retargetPLVal retargetYName retargetYSlot false
    [retargetDerefPLVal] retargetDerefPLVal
    retarget_write_deref_s_effective_write_p retargetWriteEnv_y
    ⟨retargetYSlot, retargetWriteEnv_y, PartialTyContains.here⟩
    (by simp)
    (EnvMayReadThrough.direct (by
      simp [LVal.StrictPrefixOf, StrictPathPrefix, retargetPLVal,
        retargetDerefPLVal, LVal.base, LVal.path]))

theorem retargetWrite_a_typing :
    LValTyping retargetWriteEnv retargetALVal (.ty .int) Lifetime.root := by
  exact LValTyping.var retargetWriteEnv_a

theorem retargetWrite_b_typing :
    LValTyping retargetWriteEnv retargetBLVal (.ty .int) Lifetime.root := by
  exact LValTyping.var retargetWriteEnv_b

theorem retargetWrite_p_typing :
    LValTyping retargetWriteEnv retargetPLVal
      (.ty (.borrow true [retargetALVal, retargetBLVal]))
      Lifetime.root := by
  exact LValTyping.var retargetWriteEnv_p

theorem retargetWrite_s_typing :
    LValTyping retargetWriteEnv retargetSLVal
      (.ty (.borrow true [retargetPLVal])) Lifetime.root := by
  exact LValTyping.var retargetWriteEnv_s

theorem retargetWrite_y_typing :
    LValTyping retargetWriteEnv (.var retargetYName)
      (.ty (.borrow false [retargetDerefPLVal])) Lifetime.root := by
  exact LValTyping.var retargetWriteEnv_y

theorem retargetWrite_targets_a_b_typing :
    LValTargetsTyping retargetWriteEnv [retargetALVal, retargetBLVal]
      (.ty .int) Lifetime.root := by
  exact LValTargetsTyping.cons retargetWrite_a_typing
    (LValTargetsTyping.singleton retargetWrite_b_typing)
    (PartialTyUnion.self (.ty .int))
    (LifetimeIntersection.self Lifetime.root)

theorem retargetWrite_deref_p_typing :
    LValTyping retargetWriteEnv retargetDerefPLVal (.ty .int)
      Lifetime.root := by
  exact LValTyping.borrow retargetWrite_p_typing
    retargetWrite_targets_a_b_typing

theorem retargetWrite_deref_s_typing :
    LValTyping retargetWriteEnv (.deref retargetSLVal)
      (.ty (.borrow true [retargetALVal, retargetBLVal]))
      Lifetime.root := by
  exact LValTyping.borrow retargetWrite_s_typing
    (LValTargetsTyping.singleton retargetWrite_p_typing)

theorem retargetWriteEnv_contains_b_root
    {root : Name} {mutable : Bool} {targets : List LVal} :
    retargetWriteEnv ⊢ root ↝ (.borrow mutable targets) →
    retargetBLVal ∈ targets →
    root = retargetPName ∧ mutable = true ∧
      targets = [retargetALVal, retargetBLVal] := by
  rintro ⟨slot, hslot, hcontains⟩ hb
  by_cases ha : root = retargetAName
  · subst ha
    have hslotTy : slot.ty = .ty .int := by
      simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
        retargetIntSlot, Env.update, retargetAName, retargetBName,
        retargetPName, retargetSName] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hcontains
    cases hcontains
  · by_cases hbroot : root = retargetBName
    · subst hbroot
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
          retargetIntSlot, Env.update, retargetAName, retargetBName,
          retargetPName, retargetSName] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontains
      cases hcontains
    · by_cases hp : root = retargetPName
      · subst hp
        have hslotTy :
            slot.ty =
              .ty (.borrow true [retargetALVal, retargetBLVal]) := by
          simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
            retargetPJoinedSlot, Env.update, retargetAName, retargetBName,
            retargetPName, retargetSName] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hslot).symm
        rw [hslotTy] at hcontains
        cases hcontains with
        | here =>
            exact ⟨rfl, rfl, rfl⟩
      · by_cases hs : root = retargetSName
        · subst hs
          have hslotTy :
              slot.ty = .ty (.borrow true [retargetPLVal]) := by
            simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
              retargetSSlot, Env.update, retargetAName, retargetBName,
              retargetPName, retargetSName] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                hslot).symm
          rw [hslotTy] at hcontains
          cases hcontains with
          | here =>
              simp [retargetBLVal, retargetPLVal, retargetBName,
                retargetPName] at hb
        · by_cases hy : root = retargetYName
          · subst hy
            have hslotTy :
                slot.ty = .ty (.borrow false [retargetDerefPLVal]) := by
              simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
                retargetYSlot, Env.update, retargetAName, retargetBName,
                retargetPName, retargetSName, retargetYName] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                  hslot).symm
            rw [hslotTy] at hcontains
            cases hcontains with
            | here =>
                simp [retargetBLVal, retargetDerefPLVal, retargetPLVal,
                  retargetBName, retargetPName] at hb
          · have hnone : retargetWriteEnv.slotAt root = none := by
              have ha' : root ≠ "retarget_a" := by
                simpa [retargetAName] using ha
              have hb' : root ≠ "retarget_b" := by
                simpa [retargetBName] using hbroot
              have hp' : root ≠ "retarget_p" := by
                simpa [retargetPName] using hp
              have hs' : root ≠ "retarget_s" := by
                simpa [retargetSName] using hs
              have hy' : root ≠ "retarget_y" := by
                simpa [retargetYName] using hy
              simp [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
                Env.update, retargetAName, retargetBName, retargetPName,
                retargetSName, retargetYName, ha', hb', hp', hs', hy']
            rw [hslot] at hnone
            cases hnone

theorem retarget_write_ranked :
    ∃ φ, LinearizedBy φ retargetEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ retargetWriteEnv
        (.borrow true [retargetBLVal]) := by
  refine ⟨retargetRank, retargetEnv_linearized, ?below⟩
  constructor
  · intro root slot mutable targets target hslot hcontains htarget hrhs
    rcases hrhs with ⟨rhsMutable, rhsTargets, hrhsContains, hrhsTarget⟩
    cases hrhsContains with
    | here =>
        simp at hrhsTarget
        subst hrhsTarget
        rcases retargetWriteEnv_contains_b_root
            ⟨slot, hslot, hcontains⟩ htarget with
          ⟨hroot, _hmutable, _htargets⟩
        subst hroot
        simp [retargetRank, retargetBLVal, LVal.base,
          retargetBName, retargetPName, retargetSName, retargetYName]
  · intro root other mutable targetsMutable targetsOther targetMutable targetOther
      hcontainsMutable hcontainsOther htargetMutable htargetOther _hconflict
      hrhsMutable hrhsOther
    rcases hrhsMutable with
      ⟨rhsMutable, rhsTargets, hrhsContains, hrhsTarget⟩
    cases hrhsContains with
    | here =>
        simp at hrhsTarget
        subst hrhsTarget
        rcases retargetWriteEnv_contains_b_root hcontainsMutable
            htargetMutable with
          ⟨hroot, _hmutableRoot, _htargetsRoot⟩
        rcases hrhsOther with
          ⟨rhsMutableOther, rhsTargetsOther, hrhsContainsOther,
            hrhsTargetOther⟩
        cases hrhsContainsOther with
        | here =>
            simp at hrhsTargetOther
            subst hrhsTargetOther
            rcases retargetWriteEnv_contains_b_root hcontainsOther
                htargetOther with
              ⟨hother, _hmutableOther, _htargetsOther⟩
            exact hroot.trans hother.symm

theorem retargetWriteEnv_rhsTargetsWellFormed :
    EnvWriteRhsTargetsWellFormed retargetWriteEnv
      (.borrow true [retargetBLVal]) := by
  intro root slot mutable targets target hslot hcontains htarget hrhs
  rcases hrhs with ⟨rhsMutable, rhsTargets, hrhsContains, hrhsTarget⟩
  cases hrhsContains with
  | here =>
      simp at hrhsTarget
      subst hrhsTarget
      rcases retargetWriteEnv_contains_b_root ⟨slot, hslot, hcontains⟩
          htarget with
        ⟨hroot, _hmutable, _htargets⟩
      subst hroot
      have hslotEq : slot = retargetPJoinedSlot :=
        Option.some.inj (hslot.symm.trans retargetWriteEnv_p)
      subst hslotEq
      exact ⟨.int, Lifetime.root, retargetWrite_b_typing,
        by exact LifetimeOutlives.refl Lifetime.root,
        ⟨retargetIntSlot, by
          simpa [retargetBLVal, LVal.base] using retargetWriteEnv_b,
          by exact LifetimeOutlives.refl Lifetime.root⟩⟩

theorem retargetWriteEnv_no_target_conflicts_s
    {root : Name} {mutable : Bool} {targets : List LVal} {target : LVal} :
    retargetWriteEnv ⊢ root ↝ (.borrow mutable targets) →
    target ∈ targets →
    target ⋈ (.deref retargetSLVal) →
    False := by
  rintro ⟨slot, hslot, hcontains⟩ htarget hconflict
  by_cases ha : root = retargetAName
  · subst ha
    have hslotTy : slot.ty = .ty .int := by
      simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
        retargetIntSlot, Env.update, retargetAName, retargetBName,
        retargetPName, retargetSName] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hcontains
    cases hcontains
  · by_cases hb : root = retargetBName
    · subst hb
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
          retargetIntSlot, Env.update, retargetAName, retargetBName,
          retargetPName, retargetSName] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontains
      cases hcontains
    · by_cases hp : root = retargetPName
      · subst hp
        have hslotTy :
            slot.ty =
              .ty (.borrow true [retargetALVal, retargetBLVal]) := by
          simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
            retargetPJoinedSlot, Env.update, retargetAName, retargetBName,
            retargetPName, retargetSName] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hslot).symm
        rw [hslotTy] at hcontains
        cases hcontains with
        | here =>
            simp at htarget
            rcases htarget with htarget | htarget
            · subst htarget
              simp [PathConflicts, retargetALVal, retargetSLVal, LVal.base,
                retargetAName, retargetSName] at hconflict
            · subst htarget
              simp [PathConflicts, retargetBLVal, retargetSLVal, LVal.base,
                retargetBName, retargetSName] at hconflict
      · by_cases hs : root = retargetSName
        · subst hs
          have hslotTy :
              slot.ty = .ty (.borrow true [retargetPLVal]) := by
            simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
              retargetSSlot, Env.update, retargetAName, retargetBName,
              retargetPName, retargetSName] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                hslot).symm
          rw [hslotTy] at hcontains
          cases hcontains with
          | here =>
              simp at htarget
              subst htarget
              simp [PathConflicts, retargetPLVal, retargetSLVal, LVal.base,
                retargetPName, retargetSName] at hconflict
        · by_cases hy : root = retargetYName
          · subst hy
            have hslotTy :
                slot.ty = .ty (.borrow false [retargetDerefPLVal]) := by
              simpa [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
                retargetYSlot, Env.update, retargetAName, retargetBName,
                retargetPName, retargetSName, retargetYName] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                  hslot).symm
            rw [hslotTy] at hcontains
            cases hcontains with
            | here =>
                simp at htarget
                subst htarget
                simp [PathConflicts, retargetDerefPLVal, retargetPLVal,
                  retargetSLVal, LVal.base, retargetPName, retargetSName]
                  at hconflict
          · have hnone : retargetWriteEnv.slotAt root = none := by
              have ha' : root ≠ "retarget_a" := by
                simpa [retargetAName] using ha
              have hb' : root ≠ "retarget_b" := by
                simpa [retargetBName] using hb
              have hp' : root ≠ "retarget_p" := by
                simpa [retargetPName] using hp
              have hs' : root ≠ "retarget_s" := by
                simpa [retargetSName] using hs
              have hy' : root ≠ "retarget_y" := by
                simpa [retargetYName] using hy
              simp [retargetWriteEnv, retargetWriteInnerEnv, retargetEnv,
                Env.update, retargetAName, retargetBName, retargetPName,
                retargetSName, retargetYName, ha', hb', hp', hs', hy']
            rw [hslot] at hnone
            cases hnone

theorem retargetWriteEnv_not_writeProhibited_deref_s :
    ¬ WriteProhibited retargetWriteEnv (.deref retargetSLVal) := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨root, targets, target, hcontains, htarget,
      hconflict⟩
    exact retargetWriteEnv_no_target_conflicts_s hcontains htarget hconflict
  · rcases himm with ⟨root, targets, target, hcontains, htarget,
      hconflict⟩
    exact retargetWriteEnv_no_target_conflicts_s hcontains htarget hconflict

theorem retargetWriteEnv_no_box_typing :
    ∀ {lv inner lifetime},
      ¬ LValTyping retargetWriteEnv lv (.box inner) lifetime := by
  intro lv
  induction lv with
  | var root =>
      intro inner lifetime htyping
      generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
      cases htyping with
      | var hslot =>
          rename_i slot
          by_cases ha : root = retargetAName
          · subst ha
            have hslotEq : slot = retargetIntSlot :=
              Option.some.inj (hslot.symm.trans retargetWriteEnv_a)
            subst hslotEq
            simp [retargetIntSlot] at hpartialTy
          · by_cases hb : root = retargetBName
            · subst hb
              have hslotEq : slot = retargetIntSlot :=
                Option.some.inj (hslot.symm.trans retargetWriteEnv_b)
              subst hslotEq
              simp [retargetIntSlot] at hpartialTy
            · by_cases hp : root = retargetPName
              · subst hp
                have hslotEq : slot = retargetPJoinedSlot :=
                  Option.some.inj (hslot.symm.trans retargetWriteEnv_p)
                subst hslotEq
                simp [retargetPJoinedSlot] at hpartialTy
              · by_cases hs : root = retargetSName
                · subst hs
                  have hslotEq : slot = retargetSSlot :=
                    Option.some.inj (hslot.symm.trans retargetWriteEnv_s)
                  subst hslotEq
                  simp [retargetSSlot] at hpartialTy
                · by_cases hy : root = retargetYName
                  · subst hy
                    have hslotEq : slot = retargetYSlot :=
                      Option.some.inj (hslot.symm.trans retargetWriteEnv_y)
                    subst hslotEq
                    simp [retargetYSlot] at hpartialTy
                  · have hnone : retargetWriteEnv.slotAt root = none := by
                      have ha' : root ≠ "retarget_a" := by
                        simpa [retargetAName] using ha
                      have hb' : root ≠ "retarget_b" := by
                        simpa [retargetBName] using hb
                      have hp' : root ≠ "retarget_p" := by
                        simpa [retargetPName] using hp
                      have hs' : root ≠ "retarget_s" := by
                        simpa [retargetSName] using hs
                      have hy' : root ≠ "retarget_y" := by
                        simpa [retargetYName] using hy
                      simp [retargetWriteEnv, retargetWriteInnerEnv,
                        retargetEnv, Env.update, retargetAName,
                        retargetBName, retargetPName, retargetSName,
                        retargetYName, ha', hb', hp', hs', hy']
                    rw [hslot] at hnone
                    cases hnone
  | deref lv ih =>
      intro inner lifetime htyping
      cases htyping with
      | box hinner =>
          exact ih hinner
      | borrow _hinner htargets =>
          exact LValTargetsTyping.not_box htargets

theorem retargetWrite_a_full_typing_int {ty : Ty} {lifetime : Lifetime} :
    LValTyping retargetWriteEnv retargetALVal (.ty ty) lifetime →
    ty = .int ∧ lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetIntSlot :=
    Option.some.inj (hslot.symm.trans retargetWriteEnv_a)
  subst hslotEq
  simp [retargetIntSlot] at hty hlifetime
  exact ⟨hty.symm, hlifetime.symm⟩

theorem retargetWrite_b_full_typing_int {ty : Ty} {lifetime : Lifetime} :
    LValTyping retargetWriteEnv retargetBLVal (.ty ty) lifetime →
    ty = .int ∧ lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetIntSlot :=
    Option.some.inj (hslot.symm.trans retargetWriteEnv_b)
  subst hslotEq
  simp [retargetIntSlot] at hty hlifetime
  exact ⟨hty.symm, hlifetime.symm⟩

theorem retargetWrite_p_borrow_typing_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTyping retargetWriteEnv retargetPLVal
      (.ty (.borrow mutable targets)) lifetime →
    mutable = true ∧ targets = [retargetALVal, retargetBLVal] ∧
      lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetPJoinedSlot :=
    Option.some.inj (hslot.symm.trans retargetWriteEnv_p)
  subst hslotEq
  simp [retargetPJoinedSlot] at hty hlifetime
  rcases hty with ⟨hmutable, htargets⟩
  exact ⟨hmutable, htargets.symm, hlifetime.symm⟩

theorem retargetWrite_s_borrow_typing_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTyping retargetWriteEnv retargetSLVal
      (.ty (.borrow mutable targets)) lifetime →
    mutable = true ∧ targets = [retargetPLVal] ∧
      lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetSSlot :=
    Option.some.inj (hslot.symm.trans retargetWriteEnv_s)
  subst hslotEq
  simp [retargetSSlot] at hty hlifetime
  rcases hty with ⟨hmutable, htargets⟩
  exact ⟨hmutable, htargets.symm, hlifetime.symm⟩

theorem retargetWrite_y_borrow_typing_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTyping retargetWriteEnv (.var retargetYName)
      (.ty (.borrow mutable targets)) lifetime →
    mutable = false ∧ targets = [retargetDerefPLVal] ∧
      lifetime = Lifetime.root := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlifetime⟩
  have hslotEq : slot = retargetYSlot :=
    Option.some.inj (hslot.symm.trans retargetWriteEnv_y)
  subst hslotEq
  simp [retargetYSlot] at hty hlifetime
  rcases hty with ⟨hmutable, htargets⟩
  exact ⟨hmutable, htargets.symm, hlifetime.symm⟩

theorem retargetWrite_targets_a_b_not_borrow
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTargetsTyping retargetWriteEnv [retargetALVal, retargetBLVal]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  rcases lvalTargetsTyping_member_strengthens htargets retargetALVal
      (by simp) with
    ⟨selectedTy, selectedLifetime, hselected, hstrength⟩
  rcases retargetWrite_a_full_typing_int hselected with
    ⟨hselectedTy, _hselectedLifetime⟩
  subst hselectedTy
  have hcontr : Ty.borrow mutable targets = Ty.int :=
    PartialTyStrengthens.from_int_inv hstrength
  cases hcontr

theorem retargetWrite_p_targets_borrow_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTargetsTyping retargetWriteEnv [retargetPLVal]
      (.ty (.borrow mutable targets)) lifetime →
    mutable = true ∧ targets = [retargetALVal, retargetBLVal] ∧
      lifetime = Lifetime.root := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      exact retargetWrite_p_borrow_typing_facts htarget
  | cons _hhead hrest _hunion _hlifetime =>
      have hne := LValTargetsTyping.targets_ne_nil hrest
      simp at hne

theorem retargetWrite_deref_p_full_typing_int
    {ty : Ty} {lifetime : Lifetime} :
    LValTyping retargetWriteEnv retargetDerefPLVal (.ty ty) lifetime →
    ty = Ty.int := by
  intro htyping
  cases htyping with
  | box hinner =>
      exact False.elim (retargetWriteEnv_no_box_typing hinner)
  | borrow hinner htargets =>
      rcases retargetWrite_p_borrow_typing_facts hinner with
        ⟨_hmutable, htargetsEq, _hlifetime⟩
      subst htargetsEq
      rcases lvalTargetsTyping_member_strengthens htargets retargetALVal
          (by simp) with
        ⟨selectedTy, selectedLifetime, hselected, hstrength⟩
      rcases retargetWrite_a_full_typing_int hselected with
        ⟨hselectedTy, _hselectedLifetime⟩
      subst hselectedTy
      exact PartialTyStrengthens.from_int_inv hstrength

theorem retargetWrite_deref_p_targets_not_borrow
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTargetsTyping retargetWriteEnv [retargetDerefPLVal]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      have hty := retargetWrite_deref_p_full_typing_int htarget
      cases hty
  | cons _hhead hrest _hunion _hlifetime =>
      have hne := LValTargetsTyping.targets_ne_nil hrest
      simp at hne

theorem retargetWrite_deref_s_borrow_typing_facts
    {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
    LValTyping retargetWriteEnv (.deref retargetSLVal)
      (.ty (.borrow mutable targets)) lifetime →
    mutable = true ∧ targets = [retargetALVal, retargetBLVal] ∧
      lifetime = Lifetime.root := by
  intro htyping
  cases htyping with
  | box hinner =>
      exact False.elim (retargetWriteEnv_no_box_typing hinner)
  | borrow hinner htargets =>
      rcases retargetWrite_s_borrow_typing_facts hinner with
        ⟨_hmutable, htargetsEq, _hlifetime⟩
      subst htargetsEq
      exact retargetWrite_p_targets_borrow_facts htargets

theorem retargetWriteEnv_borrow_lval_facts :
    ∀ {lv mutable targets lifetime},
      LValTyping retargetWriteEnv lv (.ty (.borrow mutable targets)) lifetime →
      (lv = retargetPLVal ∧ mutable = true ∧
          targets = [retargetALVal, retargetBLVal] ∧
          lifetime = Lifetime.root) ∨
      (lv = retargetSLVal ∧ mutable = true ∧
          targets = [retargetPLVal] ∧ lifetime = Lifetime.root) ∨
      (lv = .var retargetYName ∧ mutable = false ∧
          targets = [retargetDerefPLVal] ∧ lifetime = Lifetime.root) ∨
      (lv = .deref retargetSLVal ∧ mutable = true ∧
          targets = [retargetALVal, retargetBLVal] ∧
          lifetime = Lifetime.root) := by
  intro lv
  induction lv with
  | var root =>
      intro mutable targets lifetime htyping
      generalize hpartialTy :
        (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
      cases htyping with
      | var hslot =>
          rename_i slot
          by_cases ha : root = retargetAName
          · subst ha
            have hslotEq : slot = retargetIntSlot :=
              Option.some.inj (hslot.symm.trans retargetWriteEnv_a)
            subst hslotEq
            simp [retargetIntSlot] at hpartialTy
          · by_cases hb : root = retargetBName
            · subst hb
              have hslotEq : slot = retargetIntSlot :=
                Option.some.inj (hslot.symm.trans retargetWriteEnv_b)
              subst hslotEq
              simp [retargetIntSlot] at hpartialTy
            · by_cases hp : root = retargetPName
              · subst hp
                have hslotEq : slot = retargetPJoinedSlot :=
                  Option.some.inj (hslot.symm.trans retargetWriteEnv_p)
                subst hslotEq
                simp [retargetPJoinedSlot] at hpartialTy
                rcases hpartialTy with ⟨hmutable, htargets⟩
                left
                exact ⟨rfl, hmutable, htargets, rfl⟩
              · by_cases hs : root = retargetSName
                · subst hs
                  have hslotEq : slot = retargetSSlot :=
                    Option.some.inj (hslot.symm.trans retargetWriteEnv_s)
                  subst hslotEq
                  simp [retargetSSlot] at hpartialTy
                  rcases hpartialTy with ⟨hmutable, htargets⟩
                  right
                  left
                  exact ⟨rfl, hmutable, htargets, rfl⟩
                · by_cases hy : root = retargetYName
                  · subst hy
                    have hslotEq : slot = retargetYSlot :=
                      Option.some.inj (hslot.symm.trans retargetWriteEnv_y)
                    subst hslotEq
                    simp [retargetYSlot] at hpartialTy
                    rcases hpartialTy with ⟨hmutable, htargets⟩
                    right
                    right
                    left
                    exact ⟨rfl, hmutable, htargets, rfl⟩
                  · have hnone : retargetWriteEnv.slotAt root = none := by
                      have ha' : root ≠ "retarget_a" := by
                        simpa [retargetAName] using ha
                      have hb' : root ≠ "retarget_b" := by
                        simpa [retargetBName] using hb
                      have hp' : root ≠ "retarget_p" := by
                        simpa [retargetPName] using hp
                      have hs' : root ≠ "retarget_s" := by
                        simpa [retargetSName] using hs
                      have hy' : root ≠ "retarget_y" := by
                        simpa [retargetYName] using hy
                      simp [retargetWriteEnv, retargetWriteInnerEnv,
                        retargetEnv, Env.update, retargetAName,
                        retargetBName, retargetPName, retargetSName,
                        retargetYName, ha', hb', hp', hs', hy']
                    rw [hslot] at hnone
                    cases hnone
  | deref lv ih =>
      intro mutable targets lifetime htyping
      cases htyping with
      | box hinner =>
          exact False.elim (retargetWriteEnv_no_box_typing hinner)
      | borrow hinner htargets =>
          rcases ih hinner with hp | hs | hy | hds
          · rcases hp with ⟨hlv, _hmutable, htargetsEq, _hlifetime⟩
            subst hlv
            subst htargetsEq
            exact False.elim (retargetWrite_targets_a_b_not_borrow htargets)
          · rcases hs with ⟨hlv, _hmutable, htargetsEq, _hlifetime⟩
            subst hlv
            subst htargetsEq
            rcases retargetWrite_p_targets_borrow_facts htargets with
              ⟨hmutable, htargetsOuter, hlifetimeOuter⟩
            right
            right
            right
            exact ⟨rfl, hmutable, htargetsOuter, hlifetimeOuter⟩
          · rcases hy with ⟨hlv, _hmutable, htargetsEq, _hlifetime⟩
            subst hlv
            subst htargetsEq
            exact False.elim (retargetWrite_deref_p_targets_not_borrow htargets)
          · rcases hds with ⟨hlv, _hmutable, htargetsEq, _hlifetime⟩
            subst hlv
            subst htargetsEq
            exact False.elim (retargetWrite_targets_a_b_not_borrow htargets)

theorem retargetWriteEnv_coherent :
    Coherent retargetWriteEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases retargetWriteEnv_borrow_lval_facts htyping with hp | hs | hy | hds
  · rcases hp with ⟨_hlv, _hmutable, htargets, _hlifetime⟩
    subst htargets
    exact ⟨.int, Lifetime.root, retargetWrite_targets_a_b_typing⟩
  · rcases hs with ⟨_hlv, _hmutable, htargets, _hlifetime⟩
    subst htargets
    exact ⟨.borrow true [retargetALVal, retargetBLVal], Lifetime.root,
      LValTargetsTyping.singleton retargetWrite_p_typing⟩
  · rcases hy with ⟨_hlv, _hmutable, htargets, _hlifetime⟩
    subst htargets
    exact ⟨.int, Lifetime.root,
      LValTargetsTyping.singleton retargetWrite_deref_p_typing⟩
  · rcases hds with ⟨_hlv, _hmutable, htargets, _hlifetime⟩
    subst htargets
    exact ⟨.int, Lifetime.root, retargetWrite_targets_a_b_typing⟩

def retargetAssignTerm : Term :=
  .assign (.deref retargetSLVal) (.borrow true retargetBLVal)

theorem retargetAssign_not_typing :
    ¬ TermTyping retargetEnv StoreTyping.empty Lifetime.root
      retargetAssignTerm .unit retargetWriteEnv := by
  intro htyping
  unfold retargetAssignTerm at htyping
  cases htyping with
  | assign hRhs _hLhsPost _hshape _hwell _hwrite hnoStale _hranked
      _hcoh _hcontained _hnotWrite =>
      cases hRhs with
      | mutBorrow _hlv _hmutable _hnotWrite =>
          exact retarget_write_deref_s_not_noStale hnoStale

theorem retargetStore_a :
    retargetStore.slotAt (VariableProjection retargetAName) =
      some { value := .value (.int 0), lifetime := Lifetime.root } := by
  simp [retargetStore, VariableProjection, retargetAName]

theorem retargetStore_b :
    retargetStore.slotAt (VariableProjection retargetBName) =
      some { value := .value (.int 1), lifetime := Lifetime.root } := by
  simp [retargetStore, VariableProjection, retargetBName, retargetAName]

theorem retargetStore_p :
    retargetStore.slotAt (VariableProjection retargetPName) =
      some { value := .value retargetBorrowA, lifetime := Lifetime.root } := by
  simp [retargetStore, VariableProjection, retargetPName, retargetBName,
    retargetAName]

theorem retargetStore_p_var :
    retargetStore.slotAt (.var retargetPName) =
      some retargetOldPStoreSlot := by
  simpa [VariableProjection, retargetOldPStoreSlot] using retargetStore_p

theorem retargetStore_s :
    retargetStore.slotAt (VariableProjection retargetSName) =
      some { value := .value retargetBorrowP, lifetime := Lifetime.root } := by
  simp [retargetStore, VariableProjection, retargetSName, retargetPName,
    retargetBName, retargetAName]

theorem retargetStore_y :
    retargetStore.slotAt (VariableProjection retargetYName) =
      some { value := .value retargetBorrowA, lifetime := Lifetime.root } := by
  simp [retargetStore, VariableProjection, retargetYName, retargetSName,
    retargetPName, retargetBName, retargetAName]

theorem retargetStore_loc_a :
    retargetStore.loc retargetALVal = some (.var retargetAName) := by
  simp [retargetALVal]

theorem retargetStore_loc_b :
    retargetStore.loc retargetBLVal = some (.var retargetBName) := by
  simp [retargetBLVal]

theorem retargetStore_loc_p :
    retargetStore.loc retargetPLVal = some (.var retargetPName) := by
  simp [retargetPLVal]

theorem retargetStore_loc_s :
    retargetStore.loc retargetSLVal = some (.var retargetSName) := by
  simp [retargetSLVal]

theorem retargetStore_loc_deref_p :
    retargetStore.loc retargetDerefPLVal = some (.var retargetAName) := by
  simp [ProgramStore.loc, retargetDerefPLVal, retargetPLVal, retargetStore,
    retargetBorrowA, retargetPName, retargetBName, retargetAName]

theorem retargetStoreAfter_p :
    retargetStoreAfter.slotAt (VariableProjection retargetPName) =
      some { value := .value retargetBorrowB, lifetime := Lifetime.root } := by
  simp [retargetStoreAfter, ProgramStore.update, VariableProjection,
    retargetPName]

theorem retargetStoreAfter_y :
    retargetStoreAfter.slotAt (VariableProjection retargetYName) =
      some { value := .value retargetBorrowA, lifetime := Lifetime.root } := by
  simp [retargetStoreAfter, ProgramStore.update, retargetStore,
    VariableProjection, retargetYName, retargetSName, retargetPName,
    retargetBName, retargetAName]

theorem retargetStoreAfter_loc_deref_p :
    retargetStoreAfter.loc retargetDerefPLVal =
      some (.var retargetBName) := by
  simp [ProgramStore.loc, retargetDerefPLVal, retargetPLVal,
    retargetStoreAfter, ProgramStore.update, retargetBorrowB,
    retargetPName]

theorem retargetStore_loc_deref_s :
    retargetStore.loc (.deref retargetSLVal) = some (.var retargetPName) := by
  simp [ProgramStore.loc, retargetSLVal, retargetStore, retargetBorrowP,
    retargetSName, retargetPName, retargetBName, retargetAName]

theorem retargetStore_read_deref_s :
    retargetStore.read (.deref retargetSLVal) =
      some retargetOldPStoreSlot := by
  unfold ProgramStore.read
  rw [retargetStore_loc_deref_s]
  exact retargetStore_p_var

theorem retargetStore_write_deref_s_borrow_b :
    retargetStore.write (.deref retargetSLVal) (.value retargetBorrowB) =
      some retargetStoreAfter := by
  unfold ProgramStore.write
  rw [retargetStore_loc_deref_s]
  simp [retargetStore_p_var, retargetStoreAfter, retargetOldPStoreSlot]

theorem retargetAssign_borrow_step :
    Step retargetStore Lifetime.root retargetAssignTerm retargetStore
      (.assign (.deref retargetSLVal) (.val retargetBorrowB)) := by
  unfold retargetAssignTerm retargetBorrowB
  exact Step.subAssign (Step.borrow retargetStore_loc_b)

theorem retargetAssign_finish_step :
    Step retargetStore Lifetime.root
      (.assign (.deref retargetSLVal) (.val retargetBorrowB))
      retargetStoreAfter (.val .unit) := by
  refine Step.assign
    (oldSlot := retargetOldPStoreSlot)
    (store₂ := retargetStoreAfter) ?_ ?_ ?_
  · exact retargetStore_read_deref_s
  · exact retargetStore_write_deref_s_borrow_b
  · exact ProgramStore.Drops.nonOwner
      (partialValueNonOwner_borrowed (.var retargetAName))
      ProgramStore.Drops.nil

theorem retargetAssign_multistep :
    MultiStep retargetStore Lifetime.root retargetAssignTerm
      retargetStoreAfter (.val .unit) := by
  exact MultiStep.trans retargetAssign_borrow_step
    (MultiStep.trans retargetAssign_finish_step MultiStep.refl)

theorem retargetAssign_source :
    SourceTerm retargetAssignTerm := by
  intro value hmem
  simp [retargetAssignTerm, termValues] at hmem

theorem retargetAssign_validStoreTyping :
    ValidStoreTyping retargetStore retargetAssignTerm StoreTyping.empty := by
  exact sourceTerm_validStoreTyping_empty retargetAssign_source

theorem retargetStore_no_ownsAt {owned storage : Location} :
    ¬ ProgramStore.OwnsAt retargetStore owned storage := by
  intro howns
  rcases howns with ⟨lifetime, hslot⟩
  cases storage with
  | var name =>
      by_cases ha : name = retargetAName
      · subst ha
        simp [retargetStore, owningRef, retargetAName] at hslot
      · by_cases hb : name = retargetBName
        · subst hb
          simp [retargetStore, owningRef, retargetBName, retargetAName] at hslot
        · by_cases hp : name = retargetPName
          · subst hp
            simp [retargetStore, owningRef, retargetBorrowA, retargetPName,
              retargetBName, retargetAName] at hslot
          · by_cases hs : name = retargetSName
            · subst hs
              simp [retargetStore, owningRef, retargetBorrowP, retargetSName,
                retargetPName, retargetBName, retargetAName] at hslot
            · by_cases hy : name = retargetYName
              · subst hy
                simp [retargetStore, owningRef, retargetBorrowA, retargetYName,
                  retargetSName, retargetPName, retargetBName, retargetAName]
                  at hslot
              · have ha' : name ≠ "retarget_a" := by
                  simpa [retargetAName] using ha
                have hb' : name ≠ "retarget_b" := by
                  simpa [retargetBName] using hb
                have hp' : name ≠ "retarget_p" := by
                  simpa [retargetPName] using hp
                have hs' : name ≠ "retarget_s" := by
                  simpa [retargetSName] using hs
                have hy' : name ≠ "retarget_y" := by
                  simpa [retargetYName] using hy
                simp [retargetStore, retargetAName, retargetBName,
                  retargetPName, retargetSName, retargetYName, ha', hb', hp',
                  hs', hy'] at hslot
  | heap address =>
      simp [retargetStore, owningRef] at hslot

theorem retargetStore_no_owns {owned : Location} :
    ¬ ProgramStore.Owns retargetStore owned := by
  intro howns
  rcases howns with ⟨storage, hownsAt⟩
  exact retargetStore_no_ownsAt hownsAt

theorem retargetStore_validRuntime :
    ValidRuntimeState retargetStore retargetAssignTerm := by
  refine ⟨?state, ?allocated, ?ownerHeap, ?heapRoot, ?termOwnerHeap⟩
  · refine ⟨?validStore, ?validTerm, ?disjoint⟩
    · intro owned storage₁ storage₂ h₁ _h₂
      exact False.elim (retargetStore_no_ownsAt h₁)
    · exact sourceTerm_validTerm retargetAssign_source
    · intro owned hmem howns
      simp [retargetAssignTerm, termOwningLocations, termValues] at hmem
  · intro owned howns
    exact False.elim (retargetStore_no_owns howns)
  · intro owned howns
    exact False.elim (retargetStore_no_owns howns)
  · intro address slot hslot
    simp [retargetStore] at hslot
  · exact sourceTerm_ownerTargetsHeap retargetAssign_source

theorem retargetStore_safe :
    retargetStore ∼ₛ retargetEnv := by
  constructor
  · intro z
    constructor
    · intro hstore
      by_cases ha : z = retargetAName
      · subst ha
        exact ⟨retargetIntSlot, retargetEnv_a⟩
      · by_cases hb : z = retargetBName
        · subst hb
          exact ⟨retargetIntSlot, retargetEnv_b⟩
        · by_cases hp : z = retargetPName
          · subst hp
            exact ⟨retargetPSlot, retargetEnv_p⟩
          · by_cases hs : z = retargetSName
            · subst hs
              exact ⟨retargetSSlot, retargetEnv_s⟩
            · by_cases hy : z = retargetYName
              · subst hy
                exact ⟨retargetYSlot, retargetEnv_y⟩
              · rcases hstore with ⟨slot, hslot⟩
                simp [retargetStore, VariableProjection, ha, hb, hp, hs, hy] at hslot
    · intro henv
      by_cases ha : z = retargetAName
      · subst ha
        exact ⟨_, retargetStore_a⟩
      · by_cases hb : z = retargetBName
        · subst hb
          exact ⟨_, retargetStore_b⟩
        · by_cases hp : z = retargetPName
          · subst hp
            exact ⟨_, retargetStore_p⟩
          · by_cases hs : z = retargetSName
            · subst hs
              exact ⟨_, retargetStore_s⟩
            · by_cases hy : z = retargetYName
              · subst hy
                exact ⟨_, retargetStore_y⟩
              · rcases henv with ⟨slot, hslot⟩
                simp [retargetEnv, ha, hb, hp, hs, hy] at hslot
  · intro z envSlot henv
    by_cases ha : z = retargetAName
    · subst ha
      have hslotEq : envSlot = retargetIntSlot :=
        Option.some.inj (henv.symm.trans retargetEnv_a)
      subst hslotEq
      exact ⟨.value (.int 0), retargetStore_a, ValidPartialValue.int⟩
    · by_cases hb : z = retargetBName
      · subst hb
        have hslotEq : envSlot = retargetIntSlot :=
          Option.some.inj (henv.symm.trans retargetEnv_b)
        subst hslotEq
        exact ⟨.value (.int 1), retargetStore_b, ValidPartialValue.int⟩
      · by_cases hp : z = retargetPName
        · subst hp
          have hslotEq : envSlot = retargetPSlot :=
            Option.some.inj (henv.symm.trans retargetEnv_p)
          subst hslotEq
          exact ⟨.value retargetBorrowA, retargetStore_p,
            ValidPartialValue.borrow (target := retargetALVal) (by simp)
              retargetStore_loc_a⟩
        · by_cases hs : z = retargetSName
          · subst hs
            have hslotEq : envSlot = retargetSSlot :=
              Option.some.inj (henv.symm.trans retargetEnv_s)
            subst hslotEq
            exact ⟨.value retargetBorrowP, retargetStore_s,
              ValidPartialValue.borrow (target := retargetPLVal) (by simp)
                retargetStore_loc_p⟩
          · by_cases hy : z = retargetYName
            · subst hy
              have hslotEq : envSlot = retargetYSlot :=
                Option.some.inj (henv.symm.trans retargetEnv_y)
              subst hslotEq
              exact ⟨.value retargetBorrowA, retargetStore_y,
                ValidPartialValue.borrow (target := retargetDerefPLVal)
                  (by simp) retargetStore_loc_deref_p⟩
            · simp [retargetEnv, ha, hb, hp, hs, hy] at henv

theorem retargetStoreAfter_not_safe :
    ¬ retargetStoreAfter ∼ₛ retargetEnv := by
  intro hsafe
  rcases hsafe.2 retargetYName retargetYSlot retargetEnv_y with
    ⟨value, hstore, hvalid⟩
  have hvalueEq : value = .value retargetBorrowA := by
    have hslotEq :
        { value := value, lifetime := Lifetime.root } =
          ({ value := .value retargetBorrowA,
              lifetime := Lifetime.root } : StoreSlot) :=
      Option.some.inj (hstore.symm.trans retargetStoreAfter_y)
    exact congrArg StoreSlot.value hslotEq
  subst hvalueEq
  cases hvalid with
  | borrow hmem hloc =>
      simp at hmem
      subst hmem
      have hlocNew := retargetStoreAfter_loc_deref_p
      rw [hloc] at hlocNew
      simp [retargetAName, retargetBName] at hlocNew

theorem retargetStoreAfter_not_safe_writeEnv :
    ¬ retargetStoreAfter ∼ₛ retargetWriteEnv := by
  intro hsafe
  rcases hsafe.2 retargetYName retargetYSlot retargetWriteEnv_y with
    ⟨value, hstore, hvalid⟩
  have hvalueEq : value = .value retargetBorrowA := by
    have hslotEq :
        { value := value, lifetime := Lifetime.root } =
          ({ value := .value retargetBorrowA,
              lifetime := Lifetime.root } : StoreSlot) :=
      Option.some.inj (hstore.symm.trans retargetStoreAfter_y)
    exact congrArg StoreSlot.value hslotEq
  subst hvalueEq
  cases hvalid with
  | borrow hmem hloc =>
      simp at hmem
      subst hmem
      have hlocNew := retargetStoreAfter_loc_deref_p
      rw [hloc] at hlocNew
      simp [retargetAName, retargetBName] at hlocNew

theorem retargetAssign_not_terminal_safe :
    ¬ TerminalStateSafe retargetStoreAfter .unit retargetWriteEnv .unit := by
  intro hterminal
  exact retargetStoreAfter_not_safe_writeEnv hterminal.2.1

theorem retargetAssign_rejected_by_noStale :
    ¬ TermTyping retargetEnv StoreTyping.empty Lifetime.root
      retargetAssignTerm .unit retargetWriteEnv :=
  retargetAssign_not_typing

/-! ### The minimal RHS-target obligation rejects the multi-target fan-out
counterexample.

The broad `ContainedBorrowsWellFormed` of the assign result was load-bearing
exactly because writing through a multi-target borrow `&mut[x,z]` whose targets
have different lifetimes fans the RHS into a longer-lived slot, and the lhs's
`targetLifetime` is only the *intersection* of the targets' lifetimes.  The
minimal replacement `EnvWriteRhsTargetsWellFormed` is UNSATISFIABLE in exactly
that situation: here the result slot `x @ [0]` holds a borrow of `w @ [0,0]`
(the RHS edge), and `[0,0]` does not outlive `[0]`, so the obligation fails — it
rejects the dangling write, confirming the replacement is sound, not merely
derivable. -/
def fanoutRejectSlotX : EnvSlot :=
  { ty := .ty (.borrow true [.var "w"]), lifetime := ([0] : Lifetime) }

def fanoutRejectSlotW : EnvSlot :=
  { ty := .ty .int, lifetime := ([0, 0] : Lifetime) }

def fanoutRejectEnv : Env :=
  { slotAt := fun n =>
      if n = "x" then some fanoutRejectSlotX
      else if n = "w" then some fanoutRejectSlotW else none }

example :
    ¬ EnvWriteRhsTargetsWellFormed fanoutRejectEnv (.borrow true [.var "w"]) := by
  intro h
  obtain ⟨tTy, tLf, htyp, hle, _⟩ :=
    h "x" fanoutRejectSlotX true [.var "w"] (.var "w")
      (by simp [fanoutRejectEnv])
      (PartialTyContains.here)
      (by simp)
      ⟨true, [.var "w"], PartialTyContains.here, by simp⟩
  rcases LValTyping.var_inv htyp with ⟨slot, hslot, _hty, hlf⟩
  simp only [fanoutRejectEnv, if_neg (by decide : ("w" : Name) ≠ "x")] at hslot
  injection hslot with hslotEq
  subst hslotEq
  rw [← hlf] at hle
  simp [fanoutRejectSlotW, fanoutRejectSlotX, LifetimeOutlives,
    Core.Lifetime.contains] at hle

end Paper
end LwRust
