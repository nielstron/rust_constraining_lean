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
  have hinv := multistep_terminal_inv (value_terminal value) hmulti
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
  have hinv := multistep_terminal_inv (value_terminal value) hmulti
  rcases hinv with ⟨hstate, hterm⟩
  cases hstate
  cases hterm
  exact ⟨rfl, rfl, habs⟩

/--
Paper Lemma 9.10 (Store Preservation), value/multi-step base case.

Checking a runtime value leaves the type environment unchanged, and a value
state cannot take a nontrivial step.
-/
theorem store_preservation_value_multistep {state finalState : State} {lifetime : Lifetime}
    {value finalValue : Value} {env env' : Env} {ty : Ty} :
    MultiStep state lifetime (.val value) finalState (.val finalValue) →
    Checks env lifetime (.val value) env' ty →
    EnvAbstracts state env →
    EnvAbstracts finalState env' := by
  intro hmulti hcheck henv
  have hinv := multistep_terminal_inv (value_terminal value) hmulti
  have henvEq := value_typing hcheck
  rcases hinv with ⟨hstate, _⟩
  cases hstate
  cases henvEq
  exact henv

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
  intro state term finalState value storeTyping env env' lifetime ty
    hvalid hstore hwf henv hcheck hsteps
  cases hcheck with
  | unit =>
      exact alias_preservation_value_multistep hsteps hvalid
  | int n =>
      exact alias_preservation_value_multistep hsteps hvalid
  | runtimeTuple hfields =>
      exact alias_preservation_value_multistep hsteps hvalid
  | accessCopy =>
      -- TODO: Paper Lemma 9.8, read/copy case.
      sorry
  | accessTemp =>
      -- TODO: Paper Lemma 9.8, read/temp case.
      sorry
  | accessMove =>
      -- TODO: Paper Lemma 9.8, move case.
      sorry
  | borrowImm =>
      -- TODO: Paper Lemma 9.8, immutable-borrow case.
      sorry
  | borrowMut =>
      -- TODO: Paper Lemma 9.8, mutable-borrow case.
      sorry
  | box =>
      -- TODO: Paper Lemma 9.8, box allocation case.
      sorry
  | letMut =>
      -- TODO: Paper Lemma 9.8, local allocation case.
      sorry
  | assign =>
      -- TODO: Paper Lemma 9.8, assignment/write case.
      sorry
  | block =>
      -- TODO: Paper Lemma 9.8, block/drop-lifetime case.
      sorry
  | tuple =>
      -- TODO: Paper Lemma 9.8, tuple evaluation-context case.
      sorry
  | ifElse =>
      -- TODO: Paper Lemma 9.8, conditional case.
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
  intro state term finalState value storeTyping env env' lifetime ty
    hvalid hstore hwf henv hcheck hsteps
  cases hcheck with
  | unit =>
      rcases preservation_value_multistep hsteps (ValueAbstracts.unit (state := state)) with
        ⟨_, _, hvalue⟩
      exact hvalue
  | int n =>
      rcases preservation_value_multistep hsteps (ValueAbstracts.int (state := state) n) with
        ⟨_, _, hvalue⟩
      exact hvalue
  | runtimeTuple hfields =>
      -- TODO: Paper Lemma 9.9, runtime tuple value case.  This needs the bridge
      -- from store-free `ValuesHaveTypes` to store-aware `ValuesAbstract`.
      sorry
  | accessCopy =>
      -- TODO: Paper Lemma 9.9, read/copy case.
      sorry
  | accessTemp =>
      -- TODO: Paper Lemma 9.9, read/temp case.
      sorry
  | accessMove =>
      -- TODO: Paper Lemma 9.9, move case.
      sorry
  | borrowImm =>
      -- TODO: Paper Lemma 9.9, immutable-borrow case.
      sorry
  | borrowMut =>
      -- TODO: Paper Lemma 9.9, mutable-borrow case.
      sorry
  | box =>
      -- TODO: Paper Lemma 9.9, box allocation case.
      sorry
  | letMut =>
      -- TODO: Paper Lemma 9.9, local allocation case.
      sorry
  | assign =>
      -- TODO: Paper Lemma 9.9, assignment/write case.
      sorry
  | block =>
      -- TODO: Paper Lemma 9.9, block/drop-lifetime case.
      sorry
  | tuple =>
      -- TODO: Paper Lemma 9.9, tuple evaluation-context case.
      sorry
  | ifElse =>
      -- TODO: Paper Lemma 9.9, conditional case.
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
  intro state term finalState value storeTyping env env' lifetime ty
    hvalid hstore hwf henv hcheck hsteps
  cases hcheck with
  | unit =>
      exact store_preservation_value_multistep hsteps (Checks.unit (env := env) (lifetime := lifetime)) henv
  | int n =>
      exact store_preservation_value_multistep hsteps (Checks.int (env := env) (lifetime := lifetime) n) henv
  | runtimeTuple hfields =>
      exact store_preservation_value_multistep hsteps
        (Checks.runtimeTuple (env := env) (lifetime := lifetime) hfields) henv
  | accessCopy =>
      -- TODO: Paper Lemma 9.10, read/copy case.
      sorry
  | accessTemp =>
      -- TODO: Paper Lemma 9.10, read/temp case.
      sorry
  | accessMove =>
      -- TODO: Paper Lemma 9.10, move case.
      sorry
  | borrowImm =>
      -- TODO: Paper Lemma 9.10, immutable-borrow case.
      sorry
  | borrowMut =>
      -- TODO: Paper Lemma 9.10, mutable-borrow case.
      sorry
  | box =>
      -- TODO: Paper Lemma 9.10, box allocation case.
      sorry
  | letMut =>
      -- TODO: Paper Lemma 9.10, local allocation case.
      sorry
  | assign =>
      -- TODO: Paper Lemma 9.10, assignment/write case.
      sorry
  | block =>
      -- TODO: Paper Lemma 9.10, block/drop-lifetime case.
      sorry
  | tuple =>
      -- TODO: Paper Lemma 9.10, tuple evaluation-context case.
      sorry
  | ifElse =>
      -- TODO: Paper Lemma 9.10, conditional case.
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
  intro state term finalState value storeTyping env env' lifetime ty
    hvalid hstore hwf henv hcheck hsteps
  exact ⟨
    alias_preservation state term finalState value storeTyping env env' lifetime ty
      hvalid hstore hwf henv hcheck hsteps,
    store_preservation state term finalState value storeTyping env env' lifetime ty
      hvalid hstore hwf henv hcheck hsteps,
    value_preservation state term finalState value storeTyping env env' lifetime ty
      hvalid hstore hwf henv hcheck hsteps
  ⟩

end Paper
end LwRust
