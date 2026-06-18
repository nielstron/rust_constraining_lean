import LwRust.Paper.BorrowCheckerSoundness

/-!
Small build-checked coverage for the executable-checker tactic surface.

The public examples use the closed-program `borrowCheck` bridge.  These
anonymous internal examples keep the lower-level finite-environment bridge
checked without adding public example statements.
-/

namespace LwRust
namespace Paper

open Core

example :
    TermTyping FiniteEnv.empty.toEnv StoreTyping.empty Lifetime.root
      (.val .unit) .unit FiniteEnv.empty.toEnv := by
  borrow_check[8, FiniteEnv.empty, FiniteEnv.empty]

example :
    TermListTyping FiniteEnv.empty.toEnv StoreTyping.empty Lifetime.root
      [.val .unit] .unit FiniteEnv.empty.toEnv := by
  borrow_check[8, FiniteEnv.empty, FiniteEnv.empty]

example :
    CheckedTermTypingWitness 8 FiniteEnv.empty StoreTyping.empty Lifetime.root
      (.val .unit) .unit FiniteEnv.empty := by
  exact checkedTermTypingWitness_of_checkTermMatches?
    (fun env lifetime => storeTypingRefsWellFormed_empty env lifetime)
    (by simp [FiniteEnv.toEnv_empty, wellFormedEnv_empty])
    (by native_decide)

example :
    Nonempty
      (CertifiedTermCheck 8 FiniteEnv.empty StoreTyping.empty Lifetime.root
        (.val .unit) .unit FiniteEnv.empty) := by
  exact certifiedTermCheck_of_checkTermMatches?
    (fun env lifetime => storeTypingRefsWellFormed_empty env lifetime)
    (by simp [FiniteEnv.toEnv_empty, wellFormedEnv_empty])
    (by native_decide)

example (hcomplete : borrowCheckCompleteOnFuelBoundCheckableTerms) :
    borrowReject (.copy (.var "x")) := by
  borrow_reject[hcomplete]

end Paper
end LwRust
