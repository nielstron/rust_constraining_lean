import LwRust.Paper.BorrowCheckerSoundness
import LwRust.Paper.Examples.Operational
import LwRust.Paper.Soundness.InitialStates

/-!
Internal non-typeability proof for the escaping-borrow rejection example.

The public example file should show the complete program and the final
accepted/rejected statement.  This module keeps the proof-specific environment
normal forms and typing inversions out of that surface.
-/

namespace LwRust
namespace Paper

open Core

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

private def escapingBorrowIntSlotOuter : EnvSlot :=
  { ty := .ty .int, lifetime := InvalidEscapingBorrowExample.l }

private def escapingBorrowYSlotX : EnvSlot :=
  { ty := .ty (Ty.borrow true [InvalidEscapingBorrowExample.x]),
    lifetime := InvalidEscapingBorrowExample.l }

private def escapingBorrowIntSlotInner : EnvSlot :=
  { ty := .ty .int, lifetime := InvalidEscapingBorrowExample.m }

private def escapingBorrowAfterX : Env :=
  Env.empty.update "x" escapingBorrowIntSlotOuter

private def escapingBorrowAfterY : Env :=
  escapingBorrowAfterX.update "y" escapingBorrowYSlotX

private def escapingBorrowInnerAfterZ : Env :=
  escapingBorrowAfterY.update "z" escapingBorrowIntSlotInner

private theorem escapingBorrow_rhs_not_well_formed :
    ¬ WellFormedTy escapingBorrowInnerAfterZ
        (.borrow true [InvalidEscapingBorrowExample.z])
        InvalidEscapingBorrowExample.l := by
  intro h
  cases h with
  | borrow htargets =>
      cases htargets with
      | intro htarget =>
          rcases htarget InvalidEscapingBorrowExample.z
              (by simp [InvalidEscapingBorrowExample.z]) with
            ⟨_targetTy, _targetLifetime, hzt, houtlives, _hbase⟩
          rcases LValTyping.var_inv hzt with
            ⟨slot, hslot, _hslotTy, hslotLifetime⟩
          simp [escapingBorrowInnerAfterZ, escapingBorrowAfterY,
            escapingBorrowAfterX, escapingBorrowIntSlotInner,
            escapingBorrowIntSlotOuter, escapingBorrowYSlotX,
            InvalidEscapingBorrowExample.l, InvalidEscapingBorrowExample.m] at hslot
          subst hslot
          rw [← hslotLifetime] at houtlives
          simp [LifetimeOutlives, Core.Lifetime.contains,
            InvalidEscapingBorrowExample.l] at houtlives

private theorem escapingBorrow_assign_not_typable :
    ¬ ∃ ty env,
      TermTyping escapingBorrowInnerAfterZ StoreTyping.empty
        InvalidEscapingBorrowExample.m
        InvalidEscapingBorrowExample.assignYBorrowZ ty env := by
  rintro ⟨_ty, _env, htyping⟩
  unfold InvalidEscapingBorrowExample.assignYBorrowZ at htyping
  cases htyping with
  | assign _hLhs hRhs _hBorrowSafe hLhsPost _hshape hwell _hwrite
      _hranked _hcoherence _hcontained _hnotWrite =>
      cases hRhs with
      | mutBorrow _hLv _hmutable _hnotWriteRhs =>
          rcases LValTyping.var_inv hLhsPost with
            ⟨slot, hslot, _hslotTy, hslotLifetime⟩
          simp [escapingBorrowInnerAfterZ, escapingBorrowAfterY,
            escapingBorrowAfterX, escapingBorrowIntSlotInner,
            escapingBorrowIntSlotOuter, escapingBorrowYSlotX,
            InvalidEscapingBorrowExample.l, InvalidEscapingBorrowExample.m] at hslot
          subst hslot
          rw [← hslotLifetime] at hwell
          exact escapingBorrow_rhs_not_well_formed (by
            simpa [InvalidEscapingBorrowExample.z,
              InvalidEscapingBorrowExample.l] using hwell)

private theorem escapingBorrow_inner_block_not_typable :
    ¬ ∃ ty env,
      TermTyping escapingBorrowAfterY StoreTyping.empty
        InvalidEscapingBorrowExample.l
        InvalidEscapingBorrowExample.innerBlock ty env := by
  rintro ⟨_ty, _env, htyping⟩
  unfold InvalidEscapingBorrowExample.innerBlock at htyping
  cases htyping with
  | block _hchild hbody _hwellTy _hdrop =>
      cases hbody with
      | cons hdeclareZ htail =>
          cases htail with
          | singleton hassign =>
              cases hdeclareZ with
              | declare _freshZ hinitZ _freshZOut _cohZ hzEnv =>
                  cases hinitZ with
                  | const hvalueZ =>
                      cases hvalueZ
                      subst hzEnv
                      exact escapingBorrow_assign_not_typable
                        ⟨_, _, by
                          simpa [escapingBorrowInnerAfterZ,
                            escapingBorrowAfterY, escapingBorrowAfterX,
                            escapingBorrowIntSlotInner,
                            InvalidEscapingBorrowExample.declareZ,
                            InvalidEscapingBorrowExample.assignYBorrowZ,
                            InvalidEscapingBorrowExample.z,
                            InvalidEscapingBorrowExample.m] using hassign⟩
          | cons _hhead htail => cases htail

private theorem invalidEscapingBorrowExample_no_types_at
    {lifetime : Lifetime} :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty lifetime
        InvalidEscapingBorrowExample.invalidProgram ty env := by
  rintro ⟨_ty, _env, htyping⟩
  unfold InvalidEscapingBorrowExample.invalidProgram at htyping
  cases htyping with
  | block _hchild hbody _hwellTy _hdrop =>
      cases hbody with
      | cons hdeclareX htail =>
          cases htail with
          | cons hdeclareY htail2 =>
              cases htail2 with
              | cons hinner _htail3 =>
                  cases hdeclareX with
                  | declare _freshX hinitX _freshXOut _cohX hxEnv =>
                      cases hinitX with
                      | const hvalueX =>
                          cases hvalueX
                          cases hdeclareY with
                          | declare _freshY hinitY _freshYOut _cohY hyEnv =>
                              cases hinitY with
                              | mutBorrow _hLvY _mutableY _notWriteY =>
                                  subst hxEnv
                                  subst hyEnv
                                  exact escapingBorrow_inner_block_not_typable
                                    ⟨_, _, by
                                      simpa [escapingBorrowAfterY,
                                        escapingBorrowAfterX,
                                        escapingBorrowIntSlotOuter,
                                        escapingBorrowYSlotX,
                                        InvalidEscapingBorrowExample.declareX,
                                        InvalidEscapingBorrowExample.declareY,
                                        InvalidEscapingBorrowExample.innerBlock,
                                        InvalidEscapingBorrowExample.x,
                                        InvalidEscapingBorrowExample.l] using hinner⟩

private theorem invalidEscapingBorrowExample_no_types :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty InvalidEscapingBorrowExample.l
        InvalidEscapingBorrowExample.invalidProgram ty env := by
  exact invalidEscapingBorrowExample_no_types_at
    (lifetime := InvalidEscapingBorrowExample.l)

private theorem invalidEscapingBorrowExample_no_root_types :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        InvalidEscapingBorrowExample.invalidProgram ty env := by
  exact invalidEscapingBorrowExample_no_types_at (lifetime := Lifetime.root)

def invalidEscapingBorrowExample_rejection :
    CertifiedTermReject 128 FiniteEnv.empty StoreTyping.empty
      InvalidEscapingBorrowExample.l InvalidEscapingBorrowExample.invalidProgram :=
  { checked := by borrow_run
    notyping := by simpa using invalidEscapingBorrowExample_no_types }

def invalidEscapingBorrowExample_root_rejection :
    CertifiedTermReject 128 FiniteEnv.empty StoreTyping.empty
      Lifetime.root InvalidEscapingBorrowExample.invalidProgram :=
  { checked := by borrow_run
    notyping := by simpa using invalidEscapingBorrowExample_no_root_types }

def invalidEscapingBorrowExample_borrowRejection :
    CertifiedBorrowReject 128 InvalidEscapingBorrowExample.invalidProgram :=
  CertifiedBorrowReject.ofTermReject
    invalidEscapingBorrowExample_root_rejection

theorem invalidEscapingBorrowExample_notAcceptedByExecutableChecker :
    borrowCheck? 256 InvalidEscapingBorrowExample.invalidProgram = false := by
  native_decide

theorem invalidEscapingBorrowExample_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty InvalidEscapingBorrowExample.l
        InvalidEscapingBorrowExample.invalidProgram ty env := by
  borrow_check using invalidEscapingBorrowExample_rejection

theorem invalidEscapingBorrowExample_borrowRejected :
    borrowReject InvalidEscapingBorrowExample.invalidProgram := by
  exact CertifiedBorrowReject.borrowReject
    invalidEscapingBorrowExample_borrowRejection

end Paper
end LwRust
