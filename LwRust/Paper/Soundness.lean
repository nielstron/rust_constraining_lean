import LwRust.Paper.Preservation
import LwRust.Paper.Progress

namespace LwRust
namespace Paper

open Core

/--
Paper Lemma 4.9 (Borrow Invariance), runtime-value base case.

Value typing leaves the environment unchanged, so well-formedness is preserved
immediately.
-/
theorem borrow_invariance_value {state : State} {env env' : Env} {lifetime : Lifetime}
    {value : Value} {ty : Ty} :
    Checks env lifetime (.val value) env' ty →
    WellFormedEnv state env lifetime →
    WellFormedEnv state env' lifetime := by
  intro hcheck hwf
  cases value_typing hcheck
  exact hwf

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
  intro state term storeTyping env env' lifetime ty _ _ hwf _ hcheck
  revert hwf
  refine Checks.rec
    (motive_1 := fun env lifetime _term env' _ty _ =>
      WellFormedEnv state env lifetime → WellFormedEnv state env' lifetime)
    (motive_2 := fun env lifetime _terms env' _ty _ =>
      WellFormedEnv state env lifetime → WellFormedEnv state env' lifetime)
    (motive_3 := fun env lifetime _terms _ env' _tys _temps _ =>
      WellFormedEnv state env lifetime → WellFormedEnv state env' lifetime)
    ?unit ?int ?runtimeTuple ?accessCopy ?accessTemp ?accessMove
    ?borrowImm ?borrowMut ?box ?letMut ?assign ?block ?tuple ?ifElse
    ?seqNil ?seqSingle ?seqCons ?termsNil ?termsCons hcheck
  · intro env lifetime hwf
    exact hwf
  · intro env lifetime n hwf
    exact hwf
  · intro env lifetime fields tys hfields hwf
    exact hwf
  · intro env lifetime lv ty targetLifetime htype hdefined hcopy hread hwf
    exact hwf
  · intro env lifetime lv ty targetLifetime htype hdefined hread hwf
    exact hwf
  · intro env env' lifetime lv ty targetLifetime htype hdefined hwrite hmove hwf
    -- TODO: Paper Lemma 4.9, move case.  This needs an environment lemma
    -- showing `BorrowChecker.Move` preserves Definition 4.8.
    sorry
  · intro env lifetime targetLifetime lv ty htype hdefined hread hwf
    exact hwf
  · intro env lifetime targetLifetime lv ty htype hdefined hwrite hmut hwf
    exact hwf
  · intro env env' lifetime term ty hterm ih hwf
    exact ih hwf
  · intro env env' lifetime x initialiser ty hfresh hinit ih hwf
    have hwfInit := ih hwf
    -- TODO: Paper Lemma 4.9, let case.  This needs the regular environment
    -- extension lemma for adding a runtime variable after allocation.
    sorry
  · intro env env₁ env₂ lifetime targetLifetime lhs rhs lhsTy rhsTy
      htype hrhs hcompat hwithin hwrite hwriteProhibited ih hwf
    have hwfRhs := ih hwf
    -- TODO: Paper Lemma 4.9, assignment case.  This needs an environment lemma
    -- showing `BorrowChecker.Write` preserves Definition 4.8.
    sorry
  · intro env env' lifetime blockLifetime terms ty hseq hwithin hscoped ih hwf
    -- TODO: Paper Lemma 4.9, block case.  The sequence is checked at
    -- `blockLifetime`, so this needs the lifetime weakening/extension fact
    -- relating the ambient and block lifetimes, then a drop-lifetime lemma.
    sorry
  · intro env env' lifetime terms tys temps hterms ih hwf
    have hwfTerms := ih hwf
    -- TODO: Paper Lemma 4.9, tuple case.  This needs a `removeMany` lemma for
    -- checker-only temporaries and the references-within obligations.
    sorry
  · intro env env₁ env₂ env₃ trueEnv falseEnv joinedEnv lifetime eq lhs rhs
      trueBlock falseBlock lhsTy rhsTy trueTy falseTy resultTy fresh hfresh hlhs hrhs
      henv₃ hcompat hcopyL hcopyR htrue hfalse hjoin hcompatBranches hunion
      ihlhs ihrhs ihtrue ihfalse hwf
    have hwfLhs := ihlhs hwf
    -- TODO: Paper Lemma 4.9, conditional case.  This needs temporary
    -- environment extension/erasure lemmas plus preservation of
    -- well-formedness by `BorrowChecker.JoinEnv`.
    sorry
  · intro env lifetime hwf
    exact hwf
  · intro env env' lifetime term ty hterm ih hwf
    exact ih hwf
  · intro env env₁ env₂ lifetime term next rest termTy resultTy hterm hrest ihterm ihrest hwf
    exact ihrest (ihterm hwf)
  · intro env lifetime n hwf
    exact hwf
  · intro env env₁ env₂ env₃ lifetime term terms n ty tys names hterm htemp hterms
      ihterm ihterms hwf
    have hwfTerm := ihterm hwf
    -- TODO: Paper Lemma 4.9, tuple-carry case.  The paper checker inserts
    -- root-lifetime type-only temporaries; preserving Definition 4.8 needs the
    -- temporary-extension lemma with `refsWithin` exposed.
    sorry

/--
Termination premise used to assemble Paper Theorem 4.12 for the recursion-free
core calculus.

TODO: The paper argues termination informally for the core; this Lean statement
is the structural termination component needed before applying Progress and
Preservation.
-/
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
Strengthened form of Paper Theorem 4.12 (Type and Borrow Safety).

This packages the terminal-state conclusion with the preservation conclusions
from Paper Lemma 4.11.
-/
theorem type_borrow_safety_preserved :
    ∀ (state : State) (term : Term) (storeTyping : StoreTyping) (env env' : Env)
      (lifetime : Lifetime) (ty : Ty),
    ValidState state term →
    StoreAbstracts state term storeTyping →
    WellFormedEnv state env lifetime →
    EnvAbstracts state env →
    Checks env lifetime term env' ty →
    ∃ finalState value,
      MultiStep state lifetime term finalState (.val value) ∧
      ValidState finalState (.val value) ∧
      EnvAbstracts finalState env' ∧
      ValueAbstracts finalState value ty := by
  intro state term storeTyping env env' lifetime ty hvalid hstore hwf henv hcheck
  rcases paper_terminates state term storeTyping env env' lifetime ty
      hvalid hstore hwf henv hcheck with
    ⟨finalState, value, hsteps⟩
  have hpreservation :=
    paper_preservation state term finalState value storeTyping env env' lifetime ty
      hvalid hstore hwf henv hcheck hsteps
  rcases hpreservation with ⟨hvalidFinal, henvFinal, hvalue⟩
  exact ⟨finalState, value, hsteps, hvalidFinal, henvFinal, hvalue⟩

/--
Paper Theorem 4.12 (Type and Borrow Safety), exact terminal-state conclusion.

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
  rcases type_borrow_safety_preserved state term storeTyping env env' lifetime ty
      hvalid hstore hwf henv hcheck with
    ⟨finalState, value, hsteps, _, _, _⟩
  exact ⟨finalState, value, hsteps⟩

end Paper
end LwRust
