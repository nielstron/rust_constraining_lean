import LwRust.Paper.BorrowCheckerSoundness

/-!
Internal non-typeability proof for the crossed-borrow dereference example.

The public example file keeps the readable source-shaped program.  This module
contains the environment normal forms and typing inversions needed to turn the
finite checker failure into a logical `borrowReject`.
-/

namespace LwRust
namespace Paper

open Core

namespace SwappedBorrowJoinReject

def l : Lifetime := [0]
def m : Lifetime := [0, 0]

def a : LVal := .var "a"
def b : LVal := .var "b"
def c : LVal := .var "c"
def d : LVal := .var "d"
def x : LVal := .var "x"
def y : LVal := .var "y"

def condition : Term := .eq (.copy a) (.copy b)

def trueBranch : Term := .block m [
  .assign x (.borrow true a),
  .assign y (.borrow true b)
]

def falseBranch : Term := .block m [
  .assign x (.borrow true b),
  .assign y (.borrow true a)
]

def tail : List Term := [
  .ite condition trueBranch falseBranch,
  .assign (.deref x) (.val (.int 1))
]

def derefXAfterIfProgram : Term := .block l [
  .letMut "a" (.val (.int 0)),
  .letMut "b" (.val (.int 0)),
  .letMut "c" (.val (.int 0)),
  .letMut "d" (.val (.int 0)),
  .letMut "x" (.borrow true c),
  .letMut "y" (.borrow true d),
  .ite condition trueBranch falseBranch,
  .assign (.deref x) (.val (.int 1))
]

private def intSlot : EnvSlot := { ty := .ty .int, lifetime := l }
private def xCSlot : EnvSlot := { ty := .ty (.borrow true [c]), lifetime := l }
private def yDSlot : EnvSlot := { ty := .ty (.borrow true [d]), lifetime := l }
private def xASlot : EnvSlot := { ty := .ty (.borrow true [a]), lifetime := l }
private def yASlot : EnvSlot := { ty := .ty (.borrow true [a]), lifetime := l }

private def afterA : Env := Env.empty.update "a" intSlot
private def afterB : Env := afterA.update "b" intSlot
private def afterC : Env := afterB.update "c" intSlot
private def afterD : Env := afterC.update "d" intSlot
private def afterX : Env := afterD.update "x" xCSlot
private def preIf : Env := afterX.update "y" yDSlot

private theorem trueBranch_x_slot_of_typing {ty env} :
    TermTyping preIf StoreTyping.empty l trueBranch ty env →
    env.slotAt "x" = some xASlot := by
  intro htyping
  unfold trueBranch at htyping
  cases htyping with
  | block _hchild hbody _hwellTy hdrop =>
      cases hbody with
      | cons hassignX htail =>
          cases htail with
          | singleton hassignY =>
              cases hassignX with
              | assign _hLhs hRhs _hsafe _hLhsPost _hshape _hwell hwriteX
                  _hranked _hcoh _hcontained _hnotWrite =>
                  cases hRhs with
                  | mutBorrow _ _ _ =>
                      have hxSlot : preIf.slotAt "x" = some xCSlot := by
                        simp [preIf, afterX, afterD, afterC, afterB, afterA,
                          xCSlot]
                      have hxEnv := envWrite_zero_var_eq hxSlot hwriteX
                      subst hxEnv
                      cases hassignY with
                      | assign _hLhsY hRhsY _hsafeY _hLhsPostY _hshapeY
                          _hwellY hwriteY _hrankedY _hcohY _hcontainedY
                          _hnotWriteY =>
                          cases hRhsY with
                          | mutBorrow _ _ _ =>
                              have hySlot :
                                  (preIf.update "x"
                                    { ty := .ty (.borrow true [a]),
                                      lifetime := xCSlot.lifetime }).slotAt
                                      "y" = some yDSlot := by
                                simp [preIf, afterX, afterD, afterC, afterB,
                                  afterA, xCSlot, yDSlot]
                              have hyEnv := envWrite_zero_var_eq hySlot hwriteY
                              rw [hyEnv] at hdrop
                              rw [hdrop]
                              simp [preIf, afterX, afterD, afterC, afterB,
                                afterA, xCSlot, yDSlot, xASlot, l, m]
          | cons _ htail => cases htail

private theorem falseBranch_y_slot_of_typing {ty env} :
    TermTyping preIf StoreTyping.empty l falseBranch ty env →
    env.slotAt "y" = some yASlot := by
  intro htyping
  unfold falseBranch at htyping
  cases htyping with
  | block _hchild hbody _hwellTy hdrop =>
      cases hbody with
      | cons hassignX htail =>
          cases htail with
          | singleton hassignY =>
              cases hassignX with
              | assign _hLhs hRhs _hsafe _hLhsPost _hshape _hwell hwriteX
                  _hranked _hcoh _hcontained _hnotWrite =>
                  cases hRhs with
                  | mutBorrow _ _ _ =>
                      have hxSlot : preIf.slotAt "x" = some xCSlot := by
                        simp [preIf, afterX, afterD, afterC, afterB, afterA,
                          xCSlot]
                      have hxEnv := envWrite_zero_var_eq hxSlot hwriteX
                      subst hxEnv
                      cases hassignY with
                      | assign _hLhsY hRhsY _hsafeY _hLhsPostY _hshapeY
                          _hwellY hwriteY _hrankedY _hcohY _hcontainedY
                          _hnotWriteY =>
                          cases hRhsY with
                          | mutBorrow _ _ _ =>
                              have hySlot :
                                  (preIf.update "x"
                                    { ty := .ty (.borrow true [b]),
                                      lifetime := xCSlot.lifetime }).slotAt
                                      "y" = some yDSlot := by
                                simp [preIf, afterX, afterD, afterC, afterB,
                                  afterA, xCSlot, yDSlot]
                              have hyEnv := envWrite_zero_var_eq hySlot hwriteY
                              rw [hyEnv] at hdrop
                              rw [hdrop]
                              simp [preIf, afterX, afterD, afterC, afterB,
                                afterA, xCSlot, yDSlot, yASlot, l, m]
          | cons _ htail => cases htail

private theorem condition_preserves_preIf {env} :
    TermTyping preIf StoreTyping.empty l condition .bool env →
    env = preIf := by
  intro htyping
  unfold condition at htyping
  cases htyping with
  | eq hleft _hghostFresh _hghost hright _hcopyLeft _hcopyRight _hshape =>
      cases hleft with
      | copy _hLvLeft _hcopy _hread =>
          cases hright with
          | copy _hLvRight _hcopyR _hreadR =>
              rfl

private theorem falseBranch_not_diverges : ¬ falseBranch.Diverges := by
  intro hdiv
  unfold falseBranch at hdiv
  cases hdiv with
  | block hmem hinner =>
      simp at hmem
      rcases hmem with hfirst | hsecond
      · subst hfirst
        cases hinner
      · subst hsecond
        cases hinner

private theorem borrow_target_survives_strengthen_sameShape
    {partialTy : PartialTy} {mutable : Bool} {target : LVal}
    {targets : List LVal} :
    PartialTyStrengthens (.ty (.borrow mutable targets)) partialTy →
    PartialTy.sameShape (.ty (.borrow mutable targets)) partialTy →
    target ∈ targets →
    ∃ joinedTargets,
      partialTy = .ty (.borrow mutable joinedTargets) ∧
        target ∈ joinedTargets := by
  intro hstrength hshape hmem
  cases hstrength with
  | reflex =>
      exact ⟨targets, rfl, hmem⟩
  | borrow hsubset =>
      exact ⟨_, rfl, hsubset hmem⟩
  | intoUndef _hinner =>
      simp [PartialTy.sameShape] at hshape

private theorem join_deref_x_not_assignment_safe
    {trueEnv falseEnv joinEnv : Env}
    (hjoin : EnvJoin trueEnv falseEnv joinEnv)
    (hsameTrue : EnvJoinSameShape trueEnv joinEnv)
    (hsameFalse : EnvJoinSameShape falseEnv joinEnv)
    (hxTrue : trueEnv.slotAt "x" = some xASlot)
    (hyFalse : falseEnv.slotAt "y" = some yASlot) :
    ¬ AssignmentBorrowSafety joinEnv (.deref x) := by
  intro hsafe
  rcases EnvStrengthens.slot_forward (EnvJoin.left_le hjoin) hxTrue with
    ⟨xJoinSlot, hxJoin, _hxLifetime, hxStrength⟩
  have hxShape : PartialTy.sameShape xASlot.ty xJoinSlot.ty :=
    hsameTrue "x" xASlot xJoinSlot hxTrue hxJoin
  rcases borrow_target_survives_strengthen_sameShape
      (target := a)
      (by simpa [xASlot] using hxStrength)
      (by simpa [xASlot] using hxShape)
      (by simp [a]) with
    ⟨xTargets, hxTy, hxMem⟩
  have hxContains : joinEnv ⊢ "x" ↝ (&mut xTargets) := by
    exact ⟨xJoinSlot, hxJoin, by
      rw [hxTy]
      exact PartialTyContains.here⟩
  rcases EnvStrengthens.slot_forward (EnvJoin.right_le hjoin) hyFalse with
    ⟨yJoinSlot, hyJoin, _hyLifetime, hyStrength⟩
  have hyShape : PartialTy.sameShape yASlot.ty yJoinSlot.ty :=
    hsameFalse "y" yASlot yJoinSlot hyFalse hyJoin
  rcases borrow_target_survives_strengthen_sameShape
      (target := a)
      (by simpa [yASlot] using hyStrength)
      (by simpa [yASlot] using hyShape)
      (by simp [a]) with
    ⟨yTargets, hyTy, hyMem⟩
  have hyContains : joinEnv ⊢ "y" ↝ (&mut yTargets) := by
    exact ⟨yJoinSlot, hyJoin, by
      rw [hyTy]
      exact PartialTyContains.here⟩
  have hrootSafe : BorrowSafeRoot joinEnv "x" := by
    have hguard : BorrowAuthorityGuard joinEnv (LVal.base x) "x" := by
      change BorrowAuthorityGuard joinEnv "x" "x"
      exact BorrowAuthorityGuard.base
    exact hsafe "x" hguard
  have hxy : "x" = "y" :=
    hrootSafe "y" true xTargets yTargets a a hxContains hyContains
      hxMem hyMem (by simp [PathConflicts, a, LVal.base])
  simp at hxy

private theorem tail_after_preIf_not_typable :
    ¬ ∃ ty env, TermListTyping preIf StoreTyping.empty l tail ty env := by
  rintro ⟨_ty, _env, htyping⟩
  unfold tail at htyping
  cases htyping with
  | cons hite htail =>
      cases htail with
      | singleton hassign =>
          cases hite with
          | ite hcond htrue hfalse _hpty hjoin hsameTrue hsameFalse _hwell
              _hcont _hcoh _hlin _htySafe =>
              have hcondEnv := condition_preserves_preIf hcond
              rw [hcondEnv] at htrue hfalse
              cases hassign with
              | assign _hLhs hRhs hsafe _hLhsPost _hshape _hwellRhs _hwrite
                  _hranked _hcoherence _hcontained _hnotWrite =>
                  cases hRhs with
                  | const hvalue =>
                      cases hvalue
                      exact join_deref_x_not_assignment_safe hjoin hsameTrue
                        hsameFalse
                        (trueBranch_x_slot_of_typing htrue)
                        (falseBranch_y_slot_of_typing hfalse)
                        hsafe
          | iteDiverging _hcond _htrue _hfalse hdiv =>
              exact falseBranch_not_diverges hdiv
      | cons _ htail => cases htail

private theorem derefXAfterIfProgram_no_types_at {lifetime : Lifetime} :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty lifetime derefXAfterIfProgram
        ty env := by
  rintro ⟨_ty, _env, htyping⟩
  unfold derefXAfterIfProgram at htyping
  cases htyping with
  | block _hchild hbody _hwellTy _hdrop =>
      cases hbody with
      | cons hdeclareA htail1 =>
          cases htail1 with
          | cons hdeclareB htail2 =>
              cases htail2 with
              | cons hdeclareC htail3 =>
                  cases htail3 with
                  | cons hdeclareD htail4 =>
                      cases htail4 with
                      | cons hdeclareX htail5 =>
                          cases htail5 with
                          | cons hdeclareY htail6 =>
                              cases hdeclareA with
                              | declare _freshA hinitA _freshAOut _cohA
                                  haEnv =>
                                  cases hinitA with
                                  | const hvalueA =>
                                      cases hvalueA
                                      subst haEnv
                                      cases hdeclareB with
                                      | declare _freshB hinitB _freshBOut
                                          _cohB hbEnv =>
                                          cases hinitB with
                                          | const hvalueB =>
                                              cases hvalueB
                                              subst hbEnv
                                              cases hdeclareC with
                                              | declare _freshC hinitC
                                                  _freshCOut _cohC hcEnv =>
                                                  cases hinitC with
                                                  | const hvalueC =>
                                                      cases hvalueC
                                                      subst hcEnv
                                                      cases hdeclareD with
                                                      | declare _freshD hinitD
                                                          _freshDOut _cohD
                                                          hdEnv =>
                                                          cases hinitD with
                                                          | const hvalueD =>
                                                              cases hvalueD
                                                              subst hdEnv
                                                              cases hdeclareX
                                                              with
                                                              | declare _freshX
                                                                  hinitX
                                                                  _freshXOut
                                                                  _cohX hxEnv =>
                                                                  cases hinitX
                                                                  with
                                                                  | mutBorrow
                                                                      _hLvX
                                                                      _hMutableX
                                                                      _hNotWriteX =>
                                                                      subst hxEnv
                                                                      cases
                                                                        hdeclareY
                                                                      with
                                                                      | declare
                                                                          _freshY
                                                                          hinitY
                                                                          _freshYOut
                                                                          _cohY
                                                                          hyEnv =>
                                                                          cases
                                                                            hinitY
                                                                          with
                                                                          | mutBorrow
                                                                              _hLvY
                                                                              _hMutableY
                                                                              _hNotWriteY =>
                                                                              subst hyEnv
                                                                              exact
                                                                                tail_after_preIf_not_typable
                                                                                ⟨_, _, by
                                                                                  simpa [tail, preIf,
                                                                                    afterX, afterD,
                                                                                    afterC, afterB,
                                                                                    afterA, intSlot,
                                                                                    xCSlot, yDSlot,
                                                                                    c, d, l] using
                                                                                    htail6⟩

private theorem derefXAfterIfProgram_no_root_types :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        derefXAfterIfProgram ty env := by
  exact derefXAfterIfProgram_no_types_at
    (lifetime := Lifetime.root)

def rejection :
    CertifiedTermReject 256 FiniteEnv.empty StoreTyping.empty
      Lifetime.root derefXAfterIfProgram :=
  { checked := by borrow_run
    notyping := by simpa using derefXAfterIfProgram_no_root_types }

def borrowRejection :
    CertifiedBorrowReject 256 derefXAfterIfProgram :=
  CertifiedBorrowReject.ofTermReject rejection

theorem rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        derefXAfterIfProgram ty env := by
  borrow_check using rejection

theorem borrowRejected :
    borrowReject derefXAfterIfProgram := by
  borrow_check using borrowRejection

theorem noBorrowCheckWitness (fuel : Nat) :
    ¬ borrowCheckWitness fuel derefXAfterIfProgram := by
  exact borrowReject_no_borrowCheckWitness (fuel := fuel) borrowRejected

theorem checkerFalse (fuel : Nat) :
    borrowCheck? fuel derefXAfterIfProgram = false := by
  exact borrowCheck?_eq_false_of_borrowReject (fuel := fuel) borrowRejected

end SwappedBorrowJoinReject

end Paper
end LwRust
