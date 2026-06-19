import LwRust.Paper.BorrowChecker.ExecutableSoundness
import LwRust.Paper.Examples.Operational

/-!
Internal non-typeability proof for the invalid assignment-through-borrow
example.
-/

namespace LwRust
namespace Paper

open Core

private theorem writeProhibited_of_slot_borrow_conflict {env : Env}
    {borrower : Name} {slot : EnvSlot} {mutable : Bool}
    {targets : List LVal} {target written : LVal}
    (hslot : env.slotAt borrower = some slot)
    (hcontains : PartialTyContains slot.ty (.borrow mutable targets))
    (hmem : target ∈ targets)
    (hconflict : target ⋈ written) :
    WriteProhibited env written := by
  cases mutable
  · right
    exact ⟨borrower, targets, target, ⟨slot, hslot, hcontains⟩,
      hmem, hconflict⟩
  · left
    exact ⟨borrower, targets, target, ⟨slot, hslot, hcontains⟩,
      hmem, hconflict⟩

private theorem writeProhibited_var_after_direct_write_of_surviving_borrow
    {env result : Env} {written borrower : Name}
    {writtenSlot borrowSlot : EnvSlot} {mutable : Bool}
    {targets : List LVal} {target : LVal} {rhsTy : Ty}
    (hwrittenSlot : env.slotAt written = some writtenSlot)
    (hborrowerNe : borrower ≠ written)
    (hborrowSlot : env.slotAt borrower = some borrowSlot)
    (hcontains :
      PartialTyContains borrowSlot.ty (.borrow mutable targets))
    (hmem : target ∈ targets)
    (hconflict : target ⋈ (.var written))
    (hwrite : EnvWrite 0 env (.var written) rhsTy result) :
    WriteProhibited result (.var written) := by
  have hresult := envWrite_zero_var_eq hwrittenSlot hwrite
  subst result
  have hborrowSlot' :
      (env.update written { writtenSlot with ty := .ty rhsTy }).slotAt
        borrower = some borrowSlot := by
    rw [Env.update_slotAt_ne]
    exact hborrowSlot
    exact hborrowerNe
  exact writeProhibited_of_slot_borrow_conflict hborrowSlot'
    hcontains hmem hconflict

private theorem no_assign_value_var_typing_of_surviving_borrow {env : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {written borrower : Name}
    {writtenSlot borrowSlot : EnvSlot} {mutable : Bool}
    {targets : List LVal} {target : LVal} {value : Value}
    (hwrittenSlot : env.slotAt written = some writtenSlot)
    (hborrowerNe : borrower ≠ written)
    (hborrowSlot : env.slotAt borrower = some borrowSlot)
    (hcontains :
      PartialTyContains borrowSlot.ty (.borrow mutable targets))
    (hmem : target ∈ targets)
    (hconflict : target ⋈ (.var written)) :
    ¬ ∃ ty outEnv,
      TermTyping env typing lifetime
        (.assign (.var written) (.val value)) ty outEnv := by
  rintro ⟨_ty, _outEnv, htyping⟩
  cases htyping with
  | assign _hLhs hRhs _hLhsPost _hshape _hwellRhs hwrite
      _hranked _hcoherence _hcontained hnotWrite =>
      cases hRhs with
      | const _hvalue =>
          exact hnotWrite
            (writeProhibited_var_after_direct_write_of_surviving_borrow
              hwrittenSlot hborrowerNe hborrowSlot hcontains hmem
              hconflict hwrite)

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

theorem invalidBorrowExample_notAcceptedByExecutableChecker :
    borrowCheck? 256 InvalidBorrowExample.invalidProgram = false := by
  native_decide

theorem invalidBorrowExample_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty InvalidBorrowExample.l
        InvalidBorrowExample.invalidProgram ty env := by
  borrow_check using invalidBorrowExample_rejection

theorem invalidBorrowExample_borrowRejected :
    borrowReject InvalidBorrowExample.invalidProgram := by
  exact CertifiedBorrowReject.borrowReject invalidBorrowExample_borrowRejection

end Paper
end LwRust
