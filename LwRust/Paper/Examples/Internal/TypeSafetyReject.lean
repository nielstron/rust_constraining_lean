import LwRust.Paper.BorrowCheckerSoundness
import LwRust.Paper.Examples.Internal.Reject.InvalidEscapingBorrow
import LwRust.Paper.Examples.Internal.Reject.InvalidBorrow
import LwRust.Paper.Examples.Operational

/-!
Build-checked rejected examples.

These files state rejection as negated typing derivations.  That keeps the
Lean build green while showing that the type-and-borrow safety theorem cannot
be applied to the program.
-/

namespace LwRust
namespace Paper

open Core

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
  exact CertifiedBorrowReject.borrowReject
    rawBorrowedReferenceConstant_borrowRejection

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
  exact CertifiedBorrowReject.borrowReject
    boxedRawBorrowedReferenceConstant_borrowRejection

end Paper
end LwRust
