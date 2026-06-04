import LwRust.Paper.Adequacy
import LwRust.Paper.Preservation
import LwRust.Paper.Progress

namespace LwRust
namespace Paper

open Core

theorem type_borrow_safety :
    ∀ (state : State) (term : Term) (storeTyping : StoreTyping) (env env' : Env)
      (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    ∃ finalState value, MultiStep state lifetime term finalState (.val value) := by
  -- TODO: Port Theorem 4.12.  The proof should combine `paper_progress`,
  -- `paper_preservation`, and the borrow invariance lemma.
  sorry

theorem progress :
    ∀ term ty,
    BorrowChecker.checkProgram term = .ok ty →
    ∃ value, OperationalSemantics.execute term = .ok value := by
  -- TODO: Prove via inductive checker/evaluator relations plus adequacy lemmas
  -- for `BorrowChecker.checkProgram` and `OperationalSemantics.execute`.
  sorry

theorem soundness :
    ∀ term ty value,
    BorrowChecker.checkProgram term = .ok ty →
    OperationalSemantics.execute term = .ok value →
    ValueHasType value ty := by
  -- TODO: `execute` hides the final store, so this weaker theorem still uses
  -- `ValueHasType`.  A store-returning executable theorem should use
  -- `ValueAbstracts finalState value ty`.
  sorry

end Paper
end LwRust
