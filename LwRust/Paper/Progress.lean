import LwRust.Paper.StoreTyping

namespace LwRust
namespace Paper

open Core

theorem progress_value {state : State} {lifetime : Lifetime} {value : Value} :
    Terminal (.val value) ∨ ∃ state' term', Step state lifetime (.val value) state' term' := by
  left
  exact value_terminal value

theorem progress_copy_of_read {state : State} {lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    state.readLVal lv = .ok value →
    ∃ state' term', Step state lifetime (.access .copy lv) state' term' := by
  intro hread
  exact ⟨state, .val value, Step.copy hread⟩

theorem progress_temp_of_read {state : State} {lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    state.readLVal lv = .ok value →
    ∃ state' term', Step state lifetime (.access .temp lv) state' term' := by
  intro hread
  exact ⟨state, .val value, Step.temp hread⟩

theorem progress_move_of_read_write {state state' : State} {lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    state.readLVal lv = .ok value →
    state.writeLVal lv none = .ok state' →
    ∃ nextState term', Step state lifetime (.access .move lv) nextState term' := by
  intro hread hwrite
  exact ⟨state', .val value, Step.move hread hwrite⟩

theorem progress_borrow_of_locate {state : State} {lifetime : Lifetime}
    {mutable : Bool} {lv : LVal} {ref : Reference} :
    locate state lv = .ok ref →
    ∃ state' term', Step state lifetime (.borrow mutable lv) state' term' := by
  intro hloc
  exact ⟨state, .val (.ref ref.borrowed), Step.borrow hloc⟩

theorem progress_box_value {state state' : State} {lifetime : Lifetime}
    {value : Value} {ref : Reference} :
    state.allocate Lifetime.root value = (state', ref) →
    ∃ nextState term', Step state lifetime (.box (.val value)) nextState term' := by
  intro halloc
  exact ⟨state', .val (.ref ref), Step.boxValue halloc⟩

theorem progress_let_mut_value {state state' : State} {lifetime : Lifetime}
    {x : Name} {value : Value} {ref : Reference} :
    state.allocate lifetime value = (state', ref) →
    ∃ nextState term', Step state lifetime (.letMut x (.val value)) nextState term' := by
  intro halloc
  exact ⟨state'.putVar x ref, .val .unit, Step.letMutValue halloc⟩

theorem progress_box_context {state : State} {lifetime : Lifetime} {term : Term} :
    (Terminal term ∨ ∃ state' term', Step state lifetime term state' term') →
    ∃ state' term', Step state lifetime (.box term) state' term' := by
  intro hprogress
  cases hprogress with
  | inl hterminal =>
      rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
      subst hterm
      cases halloc : state.allocate Lifetime.root value with
      | mk state' ref =>
          exact progress_box_value halloc
  | inr hstep =>
      rcases hstep with ⟨state', term', hstep⟩
      exact ⟨state', .box term', Step.boxSub hstep⟩

theorem progress_let_mut_context {state : State} {lifetime : Lifetime}
    {x : Name} {term : Term} :
    (Terminal term ∨ ∃ state' term', Step state lifetime term state' term') →
    ∃ state' term', Step state lifetime (.letMut x term) state' term' := by
  intro hprogress
  cases hprogress with
  | inl hterminal =>
      rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
      subst hterm
      cases halloc : state.allocate lifetime value with
      | mk state' ref =>
          exact progress_let_mut_value halloc
  | inr hstep =>
      rcases hstep with ⟨state', term', hstep⟩
      exact ⟨state', .letMut x term', Step.letMutSub hstep⟩

theorem progress_assign_context {state : State} {lifetime : Lifetime}
    {lhs : LVal} {rhs : Term} :
    (Terminal rhs ∨ ∃ state' rhs', Step state lifetime rhs state' rhs') →
    (∀ value, rhs = .val value → ∃ state', state.writeLVal lhs (some value) = .ok state') →
    ∃ state' term', Step state lifetime (.assign lhs rhs) state' term' := by
  intro hprogress hwrite
  cases hprogress with
  | inl hterminal =>
      rcases (terminal_iff_value rhs).mp hterminal with ⟨value, hrhs⟩
      rcases hwrite value hrhs with ⟨state', hwrite'⟩
      subst hrhs
      exact ⟨state', .val .unit, Step.assignValue hwrite'⟩
  | inr hstep =>
      rcases hstep with ⟨state', rhs', hstep⟩
      exact ⟨state', .assign lhs rhs', Step.assignSub hstep⟩

theorem progress_block_empty {state : State} {lifetime blockLifetime : Lifetime} :
    ∃ state' term', Step state lifetime (.block blockLifetime []) state' term' := by
  exact ⟨state.dropLifetime blockLifetime, .val .unit, Step.blockNil⟩

theorem progress_block_single_value {state : State} {lifetime blockLifetime : Lifetime}
    {value : Value} :
    ∃ state' term', Step state lifetime (.block blockLifetime [.val value]) state' term' := by
  exact ⟨state.dropLifetime blockLifetime, .val value, Step.blockValue⟩

theorem progress_block_single_context {state : State} {lifetime blockLifetime : Lifetime}
    {term : Term} :
    (Terminal term ∨ ∃ state' term', Step state blockLifetime term state' term') →
    ∃ state' block',
      Step state lifetime (.block blockLifetime [term]) state' block' := by
  intro hprogress
  cases hprogress with
  | inl hterminal =>
      rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
      subst hterm
      exact progress_block_single_value
  | inr hstep =>
      rcases hstep with ⟨state', term', hstep⟩
      exact ⟨state', .block blockLifetime [term'], Step.blockSingleSub hstep⟩

theorem progress_block_head_context {state : State} {lifetime blockLifetime : Lifetime}
    {term next : Term} {rest : List Term} :
    (Terminal term ∨ ∃ state' term', Step state blockLifetime term state' term') →
    ∃ state' block',
      Step state lifetime (.block blockLifetime (term :: next :: rest)) state' block' := by
  intro hprogress
  cases hprogress with
  | inl hterminal =>
      rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
      subst hterm
      exact ⟨state, .block blockLifetime (next :: rest), Step.blockHeadValue⟩
  | inr hstep =>
      rcases hstep with ⟨state', term', hstep⟩
      exact ⟨state', .block blockLifetime (term' :: next :: rest), Step.blockHeadSub hstep⟩

theorem progress_tuple_values {state : State} {lifetime : Lifetime} {values : List Value} :
    ∃ state' term', Step state lifetime (.tuple (values.map Term.val)) state' term' := by
  exact ⟨state, .val (.tuple values), Step.tupleValues⟩

theorem progress_tuple_head_context {state : State} {lifetime : Lifetime}
    {term : Term} {rest : List Term} :
    (∃ state' term', Step state lifetime term state' term') →
    ∃ state' tuple',
      Step state lifetime (.tuple (term :: rest)) state' tuple' := by
  intro hstep
  rcases hstep with ⟨state', term', hstep⟩
  exact ⟨state', .tuple (term' :: rest), Step.tupleHeadSub hstep⟩

theorem progress_tuple_tail_context {state : State} {lifetime : Lifetime}
    {value : Value} {next : Term} {rest : List Term} :
    (∃ state' terms', Step state lifetime (.tuple (next :: rest)) state' (.tuple terms')) →
    ∃ state' tuple',
      Step state lifetime (.tuple (.val value :: next :: rest)) state' tuple' := by
  intro hstep
  rcases hstep with ⟨state', terms', hstep⟩
  exact ⟨state', .tuple (.val value :: terms'), Step.tupleTailSub hstep⟩

theorem progress_if_context {state : State} {lifetime : Lifetime} {eq : Bool}
    {lhs rhs trueBlock falseBlock : Term} :
    (Terminal lhs ∨ ∃ state' lhs', Step state lifetime lhs state' lhs') →
    (∀ lhsValue, lhs = .val lhsValue →
      Terminal rhs ∨ ∃ state' rhs', Step state lifetime rhs state' rhs') →
    ∃ state' term', Step state lifetime (.ifElse eq lhs rhs trueBlock falseBlock) state' term' := by
  intro hlhs hrhs
  cases hlhs with
  | inr hstep =>
      rcases hstep with ⟨state', lhs', hstep⟩
      exact ⟨state', .ifElse eq lhs' rhs trueBlock falseBlock, Step.ifLhsSub hstep⟩
  | inl hterminal =>
      rcases (terminal_iff_value lhs).mp hterminal with ⟨lhsValue, hlhsValue⟩
      have hrhsProgress := hrhs lhsValue hlhsValue
      subst hlhsValue
      cases hrhsProgress with
      | inr hstep =>
          rcases hstep with ⟨state', rhs', hstep⟩
          exact ⟨state', .ifElse eq (.val lhsValue) rhs' trueBlock falseBlock, Step.ifRhsSub hstep⟩
      | inl hterminalRhs =>
          rcases (terminal_iff_value rhs).mp hterminalRhs with ⟨rhsValue, hrhsValue⟩
          subst hrhsValue
          by_cases hcmp : (lhsValue == rhsValue) = eq
          · exact ⟨state, trueBlock, Step.ifTrue hcmp⟩
          · exact ⟨state, falseBlock, Step.ifFalse hcmp⟩

/--
Paper Lemma 4.10 (Progress), induction over the translated checker relation.

The theorem proves the paper progress conclusion for the core cases currently
covered by the store abstraction bridge. Remaining cases are documented by
localized `TODO`s in the proof body.
-/
theorem progress_for_checks {state : State} {env env' : Env} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    Terminal term ∨ ∃ state' term', Step state lifetime term state' term' := by
  intro hwf henv hcheck
  revert hwf henv
  refine Checks.rec
    (motive_1 := fun env lifetime term env' ty _ =>
      WellFormedEnv state env lifetime →
      EnvAbstracts state env →
      Terminal term ∨ ∃ state' term', Step state lifetime term state' term')
    (motive_2 := fun env lifetime terms env' ty _ =>
      WellFormedEnv state env lifetime →
      EnvAbstracts state env →
      ∀ outerLifetime,
        ∃ state' term', Step state outerLifetime (.block lifetime terms) state' term')
    (motive_3 := fun env lifetime terms _ env' tys temps _ =>
      WellFormedEnv state env lifetime →
      EnvAbstracts state env →
      ∃ state' term', Step state lifetime (.tuple terms) state' term')
    ?unit ?int ?runtimeTuple ?accessCopy ?accessTemp ?accessMove
    ?borrowImm ?borrowMut ?box ?letMut ?assign ?block ?tuple ?ifElse
    ?seqNil ?seqSingle ?seqCons ?termsNil ?termsCons hcheck
  · intro env lifetime _ _
    exact progress_value
  · intro env lifetime n _ _
    exact progress_value
  · intro env lifetime fields tys hfields _ _
    exact progress_value
  · intro env lifetime lv ty targetLifetime htype hdefined _ _ hwf henv
    right
    rcases read_preservation henv hwf htype hdefined with ⟨value, hread, _⟩
    exact progress_copy_of_read hread
  · intro env lifetime lv ty targetLifetime htype hdefined _ hwf henv
    right
    rcases read_preservation henv hwf htype hdefined with ⟨value, hread, _⟩
    exact progress_temp_of_read hread
  · intro env env' lifetime lv ty targetLifetime htype hdefined hwriteProhibited _ hwf henv
    right
    rcases read_preservation henv hwf htype hdefined with ⟨value, hread, _⟩
    rcases move_write_progress henv hwf htype hdefined hwriteProhibited with ⟨state', hwrite⟩
    exact progress_move_of_read_write hread hwrite
  · intro env lifetime targetLifetime lv ty htype _ _ hwf henv
    right
    rcases location henv hwf htype with ⟨ref, _, hloc, _, _⟩
    exact progress_borrow_of_locate hloc
  · intro env lifetime targetLifetime lv ty htype _ _ _ hwf henv
    right
    rcases location henv hwf htype with ⟨ref, _, hloc, _, _⟩
    exact progress_borrow_of_locate hloc
  · intro env env' lifetime term ty _ ih hwf henv
    right
    exact progress_box_context (ih hwf henv)
  · intro env env' lifetime x initialiser ty _ _ ih hwf henv
    right
    exact progress_let_mut_context (ih hwf henv)
  · intro env env₁ env₂ lifetime targetLifetime lhs rhs lhsTy rhsTy
      htype hrhs _ _ _ hwriteProhibited ih hwf henv
    right
    cases ih hwf henv with
    | inr hstep =>
        rcases hstep with ⟨state', rhs', hstep⟩
        exact ⟨state', .assign lhs rhs', Step.assignSub hstep⟩
    | inl hterminal =>
        rcases (terminal_iff_value rhs).mp hterminal with ⟨value, hrhsValue⟩
        subst hrhsValue
        -- TODO: The terminal RHS case needs a preservation lemma showing that
        -- the checked RHS value abstracts `rhsTy` and that the environment used
        -- by `assign_write_progress` is the post-RHS environment.
        sorry
  · intro env env' lifetime blockLifetime terms ty hseq _ _ ihseq hwf henv
    right
    -- TODO: This needs a weakening lemma from the ambient lifetime to the block
    -- lifetime for `WellFormedEnv`.
    sorry
  · intro env env' lifetime terms tys temps hterms ihterms hwf henv
    right
    exact ihterms hwf henv
  · intro env env₁ env₂ env₃ trueEnv falseEnv joinedEnv lifetime eq lhs rhs
      trueBlock falseBlock lhsTy rhsTy trueTy falseTy resultTy fresh _ hlhs hrhs _
      _ _ _ _ _ _ _ _ ihlhs ihrhs _ _ hwf henv
    cases ihlhs hwf henv with
    | inr hstep =>
        right
        rcases hstep with ⟨state', lhs', hstep⟩
        exact ⟨state', .ifElse eq lhs' rhs trueBlock falseBlock, Step.ifLhsSub hstep⟩
    | inl hterminal =>
        rcases (terminal_iff_value lhs).mp hterminal with ⟨lhsValue, hlhsValue⟩
        subst hlhsValue
        -- TODO: The terminal LHS case needs `env_abstracts_put_type_only`,
        -- `well_formed_put_type_only`, and preservation for the checked LHS
        -- value before applying the RHS recursive hypothesis.
        sorry
  · intro env lifetime hwf henv outerLifetime
    exact progress_block_empty
  · intro env env' lifetime term ty hterm ih hwf henv outerLifetime
    exact progress_block_single_context (ih hwf henv)
  · intro env env₁ env₂ lifetime term next rest termTy resultTy hterm hrest
      ihterm ihrest hwf henv outerLifetime
    exact progress_block_head_context (ihterm hwf henv)
  · intro env lifetime n hwf henv
    simpa using (progress_tuple_values (state := state) (lifetime := lifetime) (values := []))
  · intro env env₁ env₂ env₃ lifetime term terms n ty tys names hterm htemp hterms
      ihterm ihterms hwf henv
    cases ihterm hwf henv with
    | inr hstep =>
        exact progress_tuple_head_context hstep
    | inl hterminal =>
        rcases (terminal_iff_value term).mp hterminal with ⟨value, htermValue⟩
        subst htermValue
        cases hterms with
        | nil =>
            simpa using
              (progress_tuple_values (state := state) (lifetime := lifetime) (values := [value]))
        | cons =>
            -- TODO: If the head is a value and the tail is nonempty, use
            -- `value_typing`, `env_abstracts_put_type_only`, and
            -- `well_formed_put_type_only` to recurse on the tail, then lift
            -- with `progress_tuple_tail_context`.
            sorry

/--
Paper Lemma 4.10 (Progress).

Direct statement using the translated validity, store abstraction,
environment abstraction, and inductive checker relations.
-/
theorem paper_progress :
    ∀ (state : State) (term : Term) (storeTyping : StoreTyping) (env env' : Env)
      (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    Terminal term ∨ ∃ state' term', Step state lifetime term state' term' := by
  intro state term _ env env' lifetime ty _ _ hwf henv hcheck
  exact progress_for_checks hwf henv hcheck

end Paper
end LwRust
