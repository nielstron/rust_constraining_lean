import LwRust.Paper.Adequacy
import LwRust.Paper.Preservation
import LwRust.Paper.Progress

namespace LwRust
namespace Paper

open Core

/--
Paper Lemma 4.9 (Borrow Invariance).

Typing preserves well-formedness of the output environment under the translated
checker relation.
-/
theorem borrow_invariance :
    ∀ (state : State) (term : Term) (storeTyping : StoreTyping) (env env' : Env)
      (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    WellFormedEnv state env' lifetime := by
  -- TODO: Port Paper Lemma 4.9 by induction on the translated checker
  -- relation.
  sorry

theorem paper_terminates :
    ∀ (state : State) (term : Term) (storeTyping : StoreTyping) (env env' : Env)
      (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    ∃ finalState value, MultiStep state lifetime term finalState (.val value) := by
  -- TODO: Prove termination of the core small-step semantics by a structural
  -- measure on terms.  The core has no loops or recursive invocation; function
  -- invocation is handled only in `Extensions.Functions`.
  sorry

/--
Paper Theorem 4.12 (Type and Borrow Safety).

This is the paper-level safety statement over the translated validity,
abstraction, checker, and small-step relations.
-/
theorem type_borrow_safety :
    ∀ (state : State) (term : Term) (storeTyping : StoreTyping) (env env' : Env)
      (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    ∃ finalState value, MultiStep state lifetime term finalState (.val value) := by
  intro state term storeTyping env env' lifetime ty hvalid hstore hwf henv hcheck
  exact paper_terminates state term storeTyping env env' lifetime ty
    hvalid hstore hwf henv hcheck

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
