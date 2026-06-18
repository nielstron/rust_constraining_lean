import LwRust.Paper.BorrowCheckerSoundness
import LwRust.Paper.Examples.Operational

/-!
Internal non-typeability proof for the invalid assignment-through-borrow
example.
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
  rintro ⟨_ty, _env, htyping⟩
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
