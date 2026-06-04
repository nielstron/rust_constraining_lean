import LwRust.Paper.StoreTyping

namespace LwRust
namespace Paper

open Core

theorem paper_progress :
    ∀ (state : State) (term : Term) (storeTyping : StoreTyping) (env env' : Env)
      (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    Terminal term ∨ ∃ state' term', Step state lifetime term state' term' := by
  -- TODO: Port Lemma 4.10 using `location` and `read_preservation`.
  sorry

end Paper
end LwRust
