import LwRust.Paper.StoreTyping

namespace LwRust
namespace Paper

open Core

theorem paper_preservation :
    ∀ (state : State) (term : Term) (finalState : State) (value : Value)
      (storeTyping : StoreTyping) (env env' : Env) (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    MultiStep state lifetime term finalState (.val value) →
    ValidState finalState (.val value) ∧
      EnvAbstracts finalState env' ∧
      ValueAbstracts finalState value ty := by
  -- TODO: Port Lemma 4.11 using Alias Preservation, Value Preservation, and
  -- Store Preservation (paper Lemmas 9.8, 9.9, and 9.10).
  sorry

end Paper
end LwRust
