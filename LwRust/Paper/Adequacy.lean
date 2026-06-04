import LwRust.Paper.StoreTyping

namespace LwRust
namespace Paper

open Core

theorem eval_adequate {state state' : State} {lifetime : Lifetime} {term : Term}
    {value : Value} :
    OperationalSemantics.eval state lifetime term = .ok (state', value) →
    Evaluates state lifetime term state' value := by
  -- TODO: Prove by induction following the recursive structure of
  -- `OperationalSemantics.eval`, `evalSeq`, and `evalTerms`.
  sorry

theorem eval_complete {state state' : State} {lifetime : Lifetime} {term : Term}
    {value : Value} :
    Evaluates state lifetime term state' value →
    OperationalSemantics.eval state lifetime term = .ok (state', value) := by
  -- TODO: Prove by induction on `Evaluates`.
  sorry

theorem check_adequate {env env' : Env} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    BorrowChecker.checkTerm env lifetime term = .ok (env', ty) →
    Checks env lifetime term env' ty := by
  -- TODO: Prove by induction over the recursive structure of
  -- `BorrowChecker.checkTerm`, `checkSeq`, and `carry`.
  sorry

end Paper
end LwRust
