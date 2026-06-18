import LwRust.Paper.BorrowCheckerSoundness
import LwRust.Paper.Examples.Operational
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

private def invalidBorrowIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := InvalidBorrowExample.l }

private def invalidBorrowYSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [InvalidBorrowExample.x]),
    lifetime := InvalidBorrowExample.l }

private def invalidBorrowAfterX : Env :=
  Env.empty.update "x" invalidBorrowIntSlot

private def invalidBorrowAfterY : Env :=
  invalidBorrowAfterX.update "y" invalidBorrowYSlot

/--
Runtime references are not source-level constants over the empty store typing.
This is the small closed-form version of the paper's distinction between
source programs and values created by the operational semantics.
-/
def rawBorrowedReferenceConstant : Term :=
  .val (.ref { location := .var "x", owner := false })

def rawBorrowedReferenceConstant_rejection :
    CertifiedTermReject 32 FiniteEnv.empty StoreTyping.empty Lifetime.root
      rawBorrowedReferenceConstant :=
  CertifiedTermReject.ofNonSource (by borrow_run) (by native_decide)

def rawBorrowedReferenceConstant_borrowRejection :
    CertifiedBorrowReject 32 rawBorrowedReferenceConstant :=
  CertifiedBorrowReject.ofTermReject rawBorrowedReferenceConstant_rejection

theorem rawBorrowedReferenceConstant_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        rawBorrowedReferenceConstant ty env := by
  borrow_check using rawBorrowedReferenceConstant_rejection

theorem rawBorrowedReferenceConstant_borrowRejected :
    borrowReject rawBorrowedReferenceConstant := by
  borrow_check using rawBorrowedReferenceConstant_borrowRejection

theorem rawBorrowedReferenceConstant_borrowOutcome_witness :
    borrowOutcomeWitness 32 rawBorrowedReferenceConstant
      (some rawBorrowedReferenceConstant_borrowRejection) := by
  borrow_check using rawBorrowedReferenceConstant_borrowRejection

def boxedRawBorrowedReferenceConstant : Term :=
  .box rawBorrowedReferenceConstant

def boxedRawBorrowedReferenceConstant_rejection :
    CertifiedTermReject 32 FiniteEnv.empty StoreTyping.empty Lifetime.root
      boxedRawBorrowedReferenceConstant :=
  CertifiedTermReject.ofNonSource (by borrow_run) (by native_decide)

def boxedRawBorrowedReferenceConstant_borrowRejection :
    CertifiedBorrowReject 32 boxedRawBorrowedReferenceConstant :=
  CertifiedBorrowReject.ofTermReject boxedRawBorrowedReferenceConstant_rejection

theorem boxedRawBorrowedReferenceConstant_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        boxedRawBorrowedReferenceConstant ty env := by
  borrow_check using boxedRawBorrowedReferenceConstant_rejection

theorem boxedRawBorrowedReferenceConstant_borrowRejected :
    borrowReject boxedRawBorrowedReferenceConstant := by
  borrow_check using boxedRawBorrowedReferenceConstant_borrowRejection

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
private theorem invalidBorrowExample_assign_not_typable :
    ¬ ∃ ty env,
      TermTyping invalidBorrowAfterY StoreTyping.empty InvalidBorrowExample.l
        InvalidBorrowExample.assignX ty env := by
  exact no_assign_value_var_typing_of_surviving_borrow
    (env := invalidBorrowAfterY)
    (typing := StoreTyping.empty)
    (lifetime := InvalidBorrowExample.l)
    (written := "x")
    (borrower := "y")
    (writtenSlot := invalidBorrowIntSlot)
    (borrowSlot := invalidBorrowYSlot)
    (mutable := true)
    (targets := [InvalidBorrowExample.x])
    (target := InvalidBorrowExample.x)
    (value := .int 1)
    (by
      simp [invalidBorrowAfterY, invalidBorrowAfterX, invalidBorrowIntSlot,
        invalidBorrowYSlot, InvalidBorrowExample.x])
    (by simp)
    (by
      simp [invalidBorrowAfterY, invalidBorrowAfterX, invalidBorrowIntSlot,
        invalidBorrowYSlot])
    (by exact PartialTyContains.here)
    (by simp [InvalidBorrowExample.x])
    (by simp [PathConflicts, InvalidBorrowExample.x, LVal.base])

private theorem invalidBorrowExample_no_types_at {lifetime : Lifetime} :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty lifetime
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
                      | const hvalueX =>
                          cases hvalueX
                          cases hdeclareY with
                          | declare _freshY hinitY _freshYOut _cohY hyEnv =>
                              cases hinitY with
                              | mutBorrow _hLvY _mutableY _notWriteY =>
                                  subst hxEnv
                                  subst hyEnv
                                  exact invalidBorrowExample_assign_not_typable
                                    ⟨_, _, by
                                      simpa [invalidBorrowAfterY,
                                        invalidBorrowAfterX,
                                        invalidBorrowIntSlot,
                                        invalidBorrowYSlot,
                                        InvalidBorrowExample.assignX,
                                        InvalidBorrowExample.x] using hassign⟩
              | cons _hhead htail => cases htail

private theorem invalidBorrowExample_no_types :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty InvalidBorrowExample.l
        InvalidBorrowExample.invalidProgram ty env := by
  exact invalidBorrowExample_no_types_at (lifetime := InvalidBorrowExample.l)

private theorem invalidBorrowExample_no_root_types :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        InvalidBorrowExample.invalidProgram ty env := by
  exact invalidBorrowExample_no_types_at (lifetime := Lifetime.root)

def invalidBorrowExample_rejection :
    CertifiedTermReject 128 FiniteEnv.empty StoreTyping.empty
      InvalidBorrowExample.l InvalidBorrowExample.invalidProgram :=
  { checked := by borrow_run
    notyping := by simpa using invalidBorrowExample_no_types }

def invalidBorrowExample_root_rejection :
    CertifiedTermReject 128 FiniteEnv.empty StoreTyping.empty
      Lifetime.root InvalidBorrowExample.invalidProgram :=
  { checked := by borrow_run
    notyping := by simpa using invalidBorrowExample_no_root_types }

def invalidBorrowExample_borrowRejection :
    CertifiedBorrowReject 128 InvalidBorrowExample.invalidProgram :=
  CertifiedBorrowReject.ofTermReject invalidBorrowExample_root_rejection

theorem invalidBorrowExample_failedByChecker :
    borrowCheckFailureWitness 128 InvalidBorrowExample.invalidProgram := by
  borrow_check[128]

theorem invalidBorrowExample_notAcceptedByChecker :
    ¬ borrowCheckWitness 128 InvalidBorrowExample.invalidProgram := by
  borrow_check[128]

theorem invalidBorrowExample_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty InvalidBorrowExample.l
        InvalidBorrowExample.invalidProgram ty env := by
  borrow_check using invalidBorrowExample_rejection

theorem invalidBorrowExample_borrowRejected :
    borrowReject InvalidBorrowExample.invalidProgram := by
  borrow_check using invalidBorrowExample_borrowRejection

end Paper
end LwRust
