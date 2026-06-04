import LwRust.Paper.StoreTyping

namespace LwRust
namespace Paper

open Core

/--
Paper Lemma 9.8 (Alias Preservation), terminal-value base case.

This is the already-terminal fragment of alias preservation: a value cannot
take a nontrivial step, so no new owner aliases are introduced by reduction.
-/
theorem alias_preservation_value_multistep {state finalState : State} {lifetime : Lifetime}
    {value finalValue : Value} :
    MultiStep state lifetime (.val value) finalState (.val finalValue) →
    ValidState state (.val value) →
    ValidState finalState (.val finalValue) := by
  intro hmulti hvalid
  have hinv := multistep_value_inv hmulti
  rcases hinv with ⟨hstate, hterm⟩
  cases hstate
  cases hterm
  exact hvalid

/--
Paper Lemma 9.9 (Value Preservation), value/multi-step base case.

This proves the already-terminal fragment used by the larger preservation
argument.
-/
theorem preservation_value_multistep {state finalState : State} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    MultiStep state lifetime (.val value) finalState (.val finalValue) →
    ValueAbstracts state value ty →
    finalState = state ∧ finalValue = value ∧ ValueAbstracts finalState finalValue ty := by
  intro hmulti habs
  have hinv := multistep_value_inv hmulti
  rcases hinv with ⟨hstate, hterm⟩
  cases hstate
  cases hterm
  exact ⟨rfl, rfl, habs⟩

/--
Paper Lemma 9.8 (Alias Preservation).

Reduction from a valid state to a terminal value preserves validity of the
final state.
-/
theorem alias_preservation :
    ∀ (state : State) (term : Term) (finalState : State) (value : Value)
      (storeTyping : StoreTyping) (env env' : Env) (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    MultiStep state lifetime term finalState (.val value) →
    ValidState finalState (.val value) := by
  -- TODO: Port Paper Lemma 9.8 for all reduction cases.
  sorry

/--
Paper Lemma 9.9 (Value Preservation).

Reduction from a well-typed term to a terminal value preserves the value
abstraction for the term's type.
-/
theorem value_preservation :
    ∀ (state : State) (term : Term) (finalState : State) (value : Value)
      (storeTyping : StoreTyping) (env env' : Env) (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    MultiStep state lifetime term finalState (.val value) →
    ValueAbstracts finalState value ty := by
  -- TODO: Port Paper Lemma 9.9 for all typing and reduction cases.
  sorry

/--
Paper Lemma 9.10 (Store Preservation).

Reduction from a well-typed term to a terminal value preserves safe abstraction
of the output type environment by the final runtime state.
-/
theorem store_preservation :
    ∀ (state : State) (term : Term) (finalState : State) (value : Value)
      (storeTyping : StoreTyping) (env env' : Env) (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    MultiStep state lifetime term finalState (.val value) →
    EnvAbstracts finalState env' := by
  -- TODO: Port Paper Lemma 9.10 for all typing and reduction cases.
  sorry

/--
Paper Lemma 4.11 (Preservation).

If a valid, abstracting state takes zero or more small steps to a value, then
the final state remains valid, abstracts the output environment, and the value
abstracts the checker type.
-/
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
  -- TODO: Combine `alias_preservation`, `store_preservation`, and
  -- `value_preservation`.
  sorry

end Paper
end LwRust
