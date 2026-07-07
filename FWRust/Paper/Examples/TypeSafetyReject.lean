import FWRust.Paper.Examples.Operational
import FWRust.Paper.Soundness.Helpers.Frame
import FWRust.Paper.Soundness.InitialStates

/-!
Build-checked type-safety examples.

The first examples state rejection as negated typing derivations.  The final
section is a positive regression test for ordinary mutable-borrow assignment:
`let mut x = 0; let mut p = &mut x; *p = 1`.
-/

namespace FWRust
namespace Paper

open Core

def invalidBorrowIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := InvalidBorrowExample.l }

def invalidBorrowYSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true InvalidBorrowExample.x),
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
                  | declare hinitX _hfreshOutX hxEnv =>
                      cases hinitX with
                      | const _ =>
                          cases hdeclareY with
                          | declare hinitY _hfreshOutY hyEnv =>
                              cases hinitY with
                              | mutBorrow _hLvY _mutableY _notWriteY =>
                                  rename_i _valueLifetimeY borrowedTy
                                  cases hassign with
                                    | assign _hRhs _hLhsPost _hshape _hwell
                                        hwrite hnotWrite =>
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
                                            refine ⟨"y", InvalidBorrowExample.x, ?_,
                                              by simp [PathConflicts]⟩
                                            refine ⟨
                                              { ty := .ty (Ty.borrow true
                                                  InvalidBorrowExample.x),
                                                lifetime := InvalidBorrowExample.l },
                                              ?_, PartialTyContains.here⟩
                                            simp [Env.update, InvalidBorrowExample.x,
                                              InvalidBorrowExample.l, LVal.base])
              | cons _hhead htail => cases htail

namespace MutableBorrowAssignmentExample

def l : Lifetime := [0]
def x : LVal := .var "x"
def p : LVal := .var "p"

def xSlot : EnvSlot :=
  { ty := .ty .int, lifetime := l }

def pSlot : EnvSlot :=
  { ty := .ty (.borrow true x), lifetime := l }

def envX : Env :=
  Env.empty.update "x" xSlot

def envP : Env :=
  envX.update "p" pSlot

def prefixTerms : List Term :=
  [.letMut "x" (.val (.int 0)),
    .letMut "p" (.borrow true x)]

private theorem envX_slot_x : envX.slotAt "x" = some xSlot := by
  simp [envX]

private theorem envP_slot_x : envP.slotAt "x" = some xSlot := by
  simp [envP, envX, Env.update]

private theorem envP_slot_p : envP.slotAt "p" = some pSlot := by
  simp [envP]

private theorem envX_no_borrow_contains {y : Name} {mutable : Bool}
    {target : LVal} :
    ¬ envX ⊢ y ↝ (.borrow mutable target) := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hy : y = "x"
  · subst hy
    have hslotEq : slot = xSlot :=
      Option.some.inj (hslot.symm.trans envX_slot_x)
    subst hslotEq
    cases hcontains
  · simp [envX, Env.empty, Env.update, hy] at hslot

private theorem envX_not_writeProhibited_x :
    ¬ WriteProhibited envX x := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨_holder, _target, hcontains, _hconflict⟩
    exact envX_no_borrow_contains hcontains
  · rcases himm with ⟨_holder, _target, hcontains, _hconflict⟩
    exact envX_no_borrow_contains hcontains

private theorem envX_x_typing :
    LValTyping envX x (.ty .int) l := by
  exact LValTyping.var (slot := xSlot) envX_slot_x

private theorem envX_x_mutable :
    Mutable envX x := by
  exact Mutable.var envX_slot_x

private theorem borrow_x_typing :
    TermTyping envX StoreTyping.empty l (.borrow true x) (.borrow true x) envX := by
  exact TermTyping.mutBorrow envX_x_typing envX_x_mutable
    envX_not_writeProhibited_x

private theorem declare_x_typing :
    TermTyping Env.empty StoreTyping.empty l
      (.letMut "x" (.val (.int 0))) .unit envX := by
  unfold envX xSlot l
  exact TermTyping.declare
    (TermTyping.const ValueTyping.int)
    (by simp [Env.fresh, Env.empty])
    rfl

private theorem envX_fresh_p : envX.fresh "p" := by
  simp [Env.fresh, envX, Env.update, Env.empty]

private theorem declare_p_typing :
    TermTyping envX StoreTyping.empty l
      (.letMut "p" (.borrow true x)) .unit envP := by
  unfold envP pSlot
  exact TermTyping.declare borrow_x_typing envX_fresh_p rfl

private theorem prefix_typing :
    TermListTyping Env.empty StoreTyping.empty l prefixTerms .unit envP := by
  unfold prefixTerms
  exact TermListTyping.cons declare_x_typing
    (TermListTyping.singleton declare_p_typing)

private theorem envP_p_contains :
    envP ⊢ "p" ↝ (.borrow true x) := by
  exact ⟨pSlot, envP_slot_p, by
    unfold pSlot
    exact PartialTyContains.here⟩

private theorem envP_guard_x :
    ChainGuard envP (LVal.base (.deref p)) "x" := by
  exact ChainGuard.step ChainGuard.base envP_p_contains rfl

private theorem envP_writeProhibited_x :
    WriteProhibited envP (.var "x") :=
  WriteProhibited.of_contains_conflict envP_p_contains
    (by simp [PathConflicts, x, LVal.base])

/--
The typed empty-initial prefix creates a nontrivial `ChainGuard` node that is
write-prohibited by the very mutable borrow that placed it on the chain.
-/
theorem empty_typed_prefix_has_guarded_writeProhibited_node :
    ∃ env y,
      TermListTyping Env.empty StoreTyping.empty l prefixTerms .unit env ∧
        ChainGuard env (LVal.base (.deref p)) y ∧
        WriteProhibited env (.var y) := by
  exact ⟨envP, "x", prefix_typing, envP_guard_x, envP_writeProhibited_x⟩

private theorem envP_x_typing :
    LValTyping envP x (.ty .int) l := by
  exact LValTyping.var (slot := xSlot) envP_slot_x

private theorem envP_p_typing :
    LValTyping envP p (.ty (.borrow true x)) l := by
  exact LValTyping.var (slot := pSlot) envP_slot_p

private theorem envP_deref_p_typing :
    LValTyping envP (.deref p) (.ty .int) l := by
  exact LValTyping.borrow envP_p_typing envP_x_typing

def afterWriteX : Env :=
  envP.update "x" xSlot

def afterAssign : Env :=
  afterWriteX.update "p" pSlot

private theorem write_x :
    EnvWrite envP x .int afterWriteX := by
  unfold afterWriteX x xSlot
  exact EnvWrite.intro
    (env₁ := envP) (env₂ := envP) (lv := .var "x") (slot := xSlot)
    (ty := .int) (updatedTy := .ty .int)
    envP_slot_x
    UpdateAtPath.strong

private theorem write_deref_p :
    EnvWrite envP (.deref p) .int afterAssign := by
  have hupdate :
      UpdateAtPath envP (LVal.path (.deref p)) pSlot.ty .int afterWriteX
        pSlot.ty := by
    change UpdateAtPath envP [()] (.ty (.borrow true x)) .int afterWriteX
      (.ty (.borrow true x))
    exact UpdateAtPath.mutBorrow write_x
  unfold afterAssign p pSlot
  exact EnvWrite.intro
    (env₁ := envP) (env₂ := afterWriteX) (lv := .deref (.var "p"))
    (slot := pSlot) (ty := .int) (updatedTy := pSlot.ty)
    envP_slot_p
    hupdate

private theorem afterAssign_slot_x : afterAssign.slotAt "x" = some xSlot := by
  simp [afterAssign, afterWriteX, envP, envX, Env.update]

private theorem afterAssign_slot_p : afterAssign.slotAt "p" = some pSlot := by
  simp [afterAssign]

private theorem afterAssign_contains_borrow_base_ne_p {holder : Name}
    {mutable : Bool} {target : LVal} :
    afterAssign ⊢ holder ↝ (.borrow mutable target) →
    LVal.base target ≠ "p" := by
  intro hcontains hbase
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hhp : holder = "p"
  · subst hhp
    have hslotEq : slot = pSlot :=
      Option.some.inj (hslot.symm.trans afterAssign_slot_p)
    subst hslotEq
    cases hcontainsTy with
    | here =>
        simp [x, LVal.base] at hbase
  · by_cases hhx : holder = "x"
    · subst hhx
      have hslotEq : slot = xSlot :=
        Option.some.inj (hslot.symm.trans afterAssign_slot_x)
      subst hslotEq
      cases hcontainsTy
    · simp [afterAssign, afterWriteX, envP, envX, Env.empty, Env.update,
        hhp, hhx] at hslot

private theorem afterAssign_not_writeProhibited_deref_p :
    ¬ WriteProhibited afterAssign (.deref p) := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨_holder, _target, hcontains, hconflict⟩
    exact afterAssign_contains_borrow_base_ne_p hcontains
      (by simpa [PathConflicts, p, LVal.base] using hconflict)
  · rcases himm with ⟨_holder, _target, hcontains, hconflict⟩
    exact afterAssign_contains_borrow_base_ne_p hcontains
      (by simpa [PathConflicts, p, LVal.base] using hconflict)

/--
The same empty-initial prefix reaches an environment where the ordinary write
`*p = 1` satisfies the current `T-Assign` side conditions.
-/
theorem standard_mut_borrow_assignment_side_conditions :
    ∃ envBefore envAfter lhs rhs oldTy targetLifetime rhsTy,
      TermListTyping Env.empty StoreTyping.empty l prefixTerms .unit envBefore ∧
        TermTyping envBefore StoreTyping.empty l rhs rhsTy envBefore ∧
        LValTyping envBefore lhs oldTy targetLifetime ∧
        ShapeCompatible envBefore oldTy (.ty rhsTy) ∧
        WellFormedTy envBefore rhsTy targetLifetime ∧
        EnvWrite envBefore lhs rhsTy envAfter ∧
        ¬ WriteProhibited envAfter lhs := by
  exact ⟨envP, afterAssign, .deref p, .val (.int 1), .ty .int, l, .int,
    prefix_typing,
    TermTyping.const ValueTyping.int,
    envP_deref_p_typing,
    ShapeCompatible.int,
    WellFormedTy.int,
    write_deref_p,
    afterAssign_not_writeProhibited_deref_p⟩

theorem standard_mut_borrow_assignment_typing :
    TermListTyping Env.empty StoreTyping.empty l
      (prefixTerms ++ [.assign (.deref p) (.val (.int 1))])
      .unit afterAssign := by
  unfold prefixTerms
  exact TermListTyping.cons declare_x_typing
    (TermListTyping.cons declare_p_typing
      (TermListTyping.singleton
        (TermTyping.assign
          (TermTyping.const ValueTyping.int)
          envP_deref_p_typing
          ShapeCompatible.int
          WellFormedTy.int
          write_deref_p
          afterAssign_not_writeProhibited_deref_p)))

end MutableBorrowAssignmentExample

end Paper
end FWRust
