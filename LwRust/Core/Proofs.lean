import LwRust.Core.Syntax

/-!
Formal proof layer for the core calculus.

The executable translation in `Core.BorrowChecker` mirrors the Java
implementation with stateful environments, partial moves, borrows and heap
locations.  That is useful for running the translated tests, but it is not yet
structured as a relational metatheory.  This file introduces a small
proof-oriented core fragment and proves the standard progress and preservation
facts for it.

TODO: Extend these theorems from the pure core fragment below to the full FR
core in `Core.Syntax`, including stores, l-values, box ownership, borrowing,
lifetimes, environment/store consistency, drop preservation, and the borrow
invariance lemmas from `lw_rust.pdf`.
-/

namespace LwRust
namespace Core
namespace Proofs

inductive PTy where
  | unit
  | int
  | bool
  deriving DecidableEq, Repr

inductive PTerm where
  | unit
  | int (n : Int)
  | bool (b : Bool)
  | add (lhs rhs : PTerm)
  | eq (lhs rhs : PTerm)
  | ite (cond thenTerm elseTerm : PTerm)
  deriving DecidableEq, Repr

inductive Value : PTerm → Prop where
  | unit : Value .unit
  | int (n : Int) : Value (.int n)
  | bool (b : Bool) : Value (.bool b)

inductive HasType : PTerm → PTy → Prop where
  | unit : HasType .unit .unit
  | int (n : Int) : HasType (.int n) .int
  | bool (b : Bool) : HasType (.bool b) .bool
  | add {lhs rhs : PTerm} :
      HasType lhs .int →
      HasType rhs .int →
      HasType (.add lhs rhs) .int
  | eq {lhs rhs : PTerm} {τ : PTy} :
      HasType lhs τ →
      HasType rhs τ →
      HasType (.eq lhs rhs) .bool
  | ite {cond thenTerm elseTerm : PTerm} {τ : PTy} :
      HasType cond .bool →
      HasType thenTerm τ →
      HasType elseTerm τ →
      HasType (.ite cond thenTerm elseTerm) τ

inductive Step : PTerm → PTerm → Prop where
  | addLeft {lhs lhs' rhs : PTerm} :
      Step lhs lhs' →
      Step (.add lhs rhs) (.add lhs' rhs)
  | addRight {n : Int} {rhs rhs' : PTerm} :
      Step rhs rhs' →
      Step (.add (.int n) rhs) (.add (.int n) rhs')
  | addInts (m n : Int) :
      Step (.add (.int m) (.int n)) (.int (m + n))
  | eqLeft {lhs lhs' rhs : PTerm} :
      Step lhs lhs' →
      Step (.eq lhs rhs) (.eq lhs' rhs)
  | eqRight {v rhs rhs' : PTerm} :
      Value v →
      Step rhs rhs' →
      Step (.eq v rhs) (.eq v rhs')
  | eqUnit :
      Step (.eq .unit .unit) (.bool true)
  | eqInts (m n : Int) :
      Step (.eq (.int m) (.int n)) (.bool (m == n))
  | eqBools (p q : Bool) :
      Step (.eq (.bool p) (.bool q)) (.bool (p == q))
  | iteCond {cond cond' thenTerm elseTerm : PTerm} :
      Step cond cond' →
      Step (.ite cond thenTerm elseTerm) (.ite cond' thenTerm elseTerm)
  | iteTrue {thenTerm elseTerm : PTerm} :
      Step (.ite (.bool true) thenTerm elseTerm) thenTerm
  | iteFalse {thenTerm elseTerm : PTerm} :
      Step (.ite (.bool false) thenTerm elseTerm) elseTerm

inductive MultiStep : PTerm → PTerm → Prop where
  | refl (t : PTerm) : MultiStep t t
  | trans {t₁ t₂ t₃ : PTerm} :
      Step t₁ t₂ →
      MultiStep t₂ t₃ →
      MultiStep t₁ t₃

theorem canonical_int {t : PTerm} :
    Value t → HasType t .int → ∃ n, t = .int n := by
  intro hv ht
  cases hv with
  | unit => cases ht
  | int n => exact ⟨n, rfl⟩
  | bool b => cases ht

theorem canonical_bool {t : PTerm} :
    Value t → HasType t .bool → ∃ b, t = .bool b := by
  intro hv ht
  cases hv with
  | unit => cases ht
  | int n => cases ht
  | bool b => exact ⟨b, rfl⟩

theorem canonical_same_values {lhs rhs : PTerm} {τ : PTy} :
    Value lhs →
    Value rhs →
    HasType lhs τ →
    HasType rhs τ →
    (lhs = .unit ∧ rhs = .unit) ∨
      (∃ m n, lhs = .int m ∧ rhs = .int n) ∨
      (∃ p q, lhs = .bool p ∧ rhs = .bool q) := by
  intro hlv hrv hlt hrt
  cases τ with
  | unit =>
      cases hlv <;> cases hlt
      cases hrv <;> cases hrt
      exact Or.inl ⟨rfl, rfl⟩
  | int =>
      rcases canonical_int hlv hlt with ⟨m, rfl⟩
      rcases canonical_int hrv hrt with ⟨n, rfl⟩
      exact Or.inr (Or.inl ⟨m, n, rfl, rfl⟩)
  | bool =>
      rcases canonical_bool hlv hlt with ⟨p, rfl⟩
      rcases canonical_bool hrv hrt with ⟨q, rfl⟩
      exact Or.inr (Or.inr ⟨p, q, rfl, rfl⟩)

theorem progress {t : PTerm} {τ : PTy} :
    HasType t τ → Value t ∨ ∃ t', Step t t' := by
  intro ht
  induction ht with
  | unit => exact Or.inl Value.unit
  | int n => exact Or.inl (Value.int n)
  | bool b => exact Or.inl (Value.bool b)
  | add hL hR ihL ihR =>
      cases ihL with
      | inr hstep =>
          rcases hstep with ⟨lhs', hs⟩
          exact Or.inr ⟨.add lhs' _, Step.addLeft hs⟩
      | inl hvL =>
          rcases canonical_int hvL hL with ⟨m, rfl⟩
          cases ihR with
          | inr hstep =>
              rcases hstep with ⟨rhs', hs⟩
              exact Or.inr ⟨.add (.int m) rhs', Step.addRight hs⟩
          | inl hvR =>
              rcases canonical_int hvR hR with ⟨n, rfl⟩
              exact Or.inr ⟨.int (m + n), Step.addInts m n⟩
  | eq hL hR ihL ihR =>
      cases ihL with
      | inr hstep =>
          rcases hstep with ⟨lhs', hs⟩
          exact Or.inr ⟨.eq lhs' _, Step.eqLeft hs⟩
      | inl hvL =>
          cases ihR with
          | inr hstep =>
              rcases hstep with ⟨rhs', hs⟩
              exact Or.inr ⟨.eq _ rhs', Step.eqRight hvL hs⟩
          | inl hvR =>
              rcases canonical_same_values hvL hvR hL hR with hunit | hnums | hbools
              · rcases hunit with ⟨rfl, rfl⟩
                exact Or.inr ⟨.bool true, Step.eqUnit⟩
              · rcases hnums with ⟨m, n, rfl, rfl⟩
                exact Or.inr ⟨.bool (m == n), Step.eqInts m n⟩
              · rcases hbools with ⟨p, q, rfl, rfl⟩
                exact Or.inr ⟨.bool (p == q), Step.eqBools p q⟩
  | ite hC hT hE ihC ihT ihE =>
      cases ihC with
      | inr hstep =>
          rcases hstep with ⟨cond', hs⟩
          exact Or.inr ⟨.ite cond' _ _, Step.iteCond hs⟩
      | inl hvC =>
          rcases canonical_bool hvC hC with ⟨b, rfl⟩
          cases b
          · exact Or.inr ⟨_, Step.iteFalse⟩
          · exact Or.inr ⟨_, Step.iteTrue⟩

theorem preservation {t t' : PTerm} {τ : PTy} :
    HasType t τ → Step t t' → HasType t' τ := by
  intro ht hs
  induction hs generalizing τ with
  | addLeft hs ih =>
      cases ht with
      | add hL hR =>
          exact HasType.add (ih hL) hR
  | addRight hs ih =>
      cases ht with
      | add hL hR =>
          exact HasType.add hL (ih hR)
  | addInts m n =>
      cases ht
      exact HasType.int (m + n)
  | eqLeft hs ih =>
      cases ht with
      | eq hL hR =>
          exact HasType.eq (ih hL) hR
  | eqRight hv hs ih =>
      cases ht with
      | eq hL hR =>
          exact HasType.eq hL (ih hR)
  | eqUnit =>
      cases ht
      exact HasType.bool true
  | eqInts m n =>
      cases ht
      exact HasType.bool (m == n)
  | eqBools p q =>
      cases ht
      exact HasType.bool (p == q)
  | iteCond hs ih =>
      cases ht with
      | ite hC hT hE =>
          exact HasType.ite (ih hC) hT hE
  | iteTrue =>
      cases ht with
      | ite hC hT hE => exact hT
  | iteFalse =>
      cases ht with
      | ite hC hT hE => exact hE

theorem preservation_multi {t t' : PTerm} {τ : PTy} :
    HasType t τ → MultiStep t t' → HasType t' τ := by
  intro ht hs
  induction hs with
  | refl _ => exact ht
  | trans hstep hmulti ih =>
      exact ih (preservation ht hstep)

/-- Type soundness for one reduction step: a well-typed pure-core term is
either already a value or can step to another well-typed term. -/
theorem soundness_step {t : PTerm} {τ : PTy} :
    HasType t τ →
      Value t ∨ ∃ t', Step t t' ∧ HasType t' τ := by
  intro ht
  cases progress ht with
  | inl hv => exact Or.inl hv
  | inr hs =>
      rcases hs with ⟨t', hstep⟩
      exact Or.inr ⟨t', hstep, preservation ht hstep⟩

/-- Multi-step type soundness: after any number of pure-core reduction steps, a
well-typed term is still either a value or can continue stepping. -/
theorem soundness_multi {t t' : PTerm} {τ : PTy} :
    HasType t τ →
    MultiStep t t' →
      Value t' ∨ ∃ t'', Step t' t'' ∧ HasType t'' τ := by
  intro ht hsteps
  exact soundness_step (preservation_multi ht hsteps)

theorem normal_form_value {t : PTerm} {τ : PTy} :
    HasType t τ →
    (∀ t', ¬ Step t t') →
    Value t := by
  intro ht hnormal
  cases progress ht with
  | inl hv => exact hv
  | inr hstep =>
      rcases hstep with ⟨t', hs⟩
      exact False.elim (hnormal t' hs)

/-!
The next fragment is deliberately closer to the executable translation: it uses
the actual `Core.Term` and `Core.Ty` constructors, but restricts terms to pure
values and blocks.  It is still not the full borrow/store calculus from the
paper; the TODO at the top of this file records the missing store invariants.
-/

namespace PureFR

inductive PureValue : Term → Prop where
  | unit : PureValue (Term.val LwRust.Core.Value.unit)
  | int (n : Int) : PureValue (Term.val (LwRust.Core.Value.int n))

mutual
  inductive PureHasType : Term → Ty → Prop where
    | unit : PureHasType (Term.val LwRust.Core.Value.unit) Ty.unit
    | int (n : Int) : PureHasType (Term.val (LwRust.Core.Value.int n)) Ty.int
    | block {lifetime : Lifetime} {terms : List Term} {ty : Ty} :
        PureHasSeq terms ty →
        PureHasType (.block lifetime terms) ty

  inductive PureHasSeq : List Term → Ty → Prop where
    | nil : PureHasSeq [] .unit
    | single {term : Term} {ty : Ty} :
        PureHasType term ty →
        PureHasSeq [term] ty
    | cons {term next : Term} {rest : List Term} {termTy resultTy : Ty} :
        PureHasType term termTy →
        PureHasSeq (next :: rest) resultTy →
        PureHasSeq (term :: next :: rest) resultTy
end

inductive PureStep : Term → Term → Prop where
  | blockNil {lifetime : Lifetime} :
      PureStep (.block lifetime []) (.val .unit)
  | blockSingleStep {lifetime : Lifetime} {term term' : Term} :
      PureStep term term' →
      PureStep (.block lifetime [term]) (.block lifetime [term'])
  | blockSingleValue {lifetime : Lifetime} {term : Term} :
      PureValue term →
      PureStep (.block lifetime [term]) term
  | blockHeadStep {lifetime : Lifetime} {term term' next : Term} {rest : List Term} :
      PureStep term term' →
      PureStep (.block lifetime (term :: next :: rest)) (.block lifetime (term' :: next :: rest))
  | blockHeadValue {lifetime : Lifetime} {term next : Term} {rest : List Term} :
      PureValue term →
      PureStep (.block lifetime (term :: next :: rest)) (.block lifetime (next :: rest))

inductive PureMultiStep : Term → Term → Prop where
  | refl (term : Term) : PureMultiStep term term
  | trans {term₁ term₂ term₃ : Term} :
      PureStep term₁ term₂ →
      PureMultiStep term₂ term₃ →
      PureMultiStep term₁ term₃

theorem pure_value_has_no_step {term term' : Term} :
    PureValue term → ¬ PureStep term term' := by
  intro hv hs
  cases hv <;> cases hs

mutual
  theorem pure_progress {term : Term} {ty : Ty} :
      PureHasType term ty → PureValue term ∨ ∃ term', PureStep term term' := by
    intro ht
    cases ht with
    | unit => exact Or.inl PureValue.unit
    | int n => exact Or.inl (PureValue.int n)
    | block hseq =>
        exact Or.inr (pure_seq_progress hseq)

  theorem pure_seq_progress {lifetime : Lifetime} {terms : List Term} {ty : Ty} :
      PureHasSeq terms ty → ∃ term', PureStep (.block lifetime terms) term' := by
    intro hseq
    cases hseq with
    | nil => exact ⟨.val .unit, PureStep.blockNil⟩
    | single hterm =>
        cases pure_progress hterm with
        | inl hv => exact ⟨_, PureStep.blockSingleValue hv⟩
        | inr hstep =>
            rcases hstep with ⟨term', hs⟩
            exact ⟨_, PureStep.blockSingleStep hs⟩
    | cons hterm hrest =>
        cases pure_progress hterm with
        | inl hv => exact ⟨_, PureStep.blockHeadValue hv⟩
        | inr hstep =>
            rcases hstep with ⟨term', hs⟩
            exact ⟨_, PureStep.blockHeadStep hs⟩
end

theorem pure_block_progress {lifetime : Lifetime} {terms : List Term} {ty : Ty} :
    PureHasSeq terms ty → ∃ term', PureStep (.block lifetime terms) term' := by
  intro hseq
  cases hseq with
  | nil => exact ⟨.val .unit, PureStep.blockNil⟩
  | single hterm =>
      cases pure_progress hterm with
      | inl hv => exact ⟨_, PureStep.blockSingleValue hv⟩
      | inr hstep =>
          rcases hstep with ⟨term', hs⟩
          exact ⟨_, PureStep.blockSingleStep hs⟩
  | cons hterm hrest =>
      cases pure_progress hterm with
      | inl hv => exact ⟨_, PureStep.blockHeadValue hv⟩
      | inr hstep =>
          rcases hstep with ⟨term', hs⟩
          exact ⟨_, PureStep.blockHeadStep hs⟩

theorem pure_progress_term {term : Term} {ty : Ty} :
    PureHasType term ty → PureValue term ∨ ∃ term', PureStep term term' := by
  intro ht
  cases ht with
  | unit => exact Or.inl PureValue.unit
  | int n => exact Or.inl (PureValue.int n)
  | block hseq => exact Or.inr (pure_block_progress hseq)

theorem pure_preservation {term term' : Term} {ty : Ty} :
    PureHasType term ty → PureStep term term' → PureHasType term' ty := by
  intro ht hs
  induction hs generalizing ty with
  | blockNil =>
      cases ht with
      | block hseq =>
          cases hseq
          exact PureHasType.unit
  | blockSingleStep hs ih =>
      cases ht with
      | block hseq =>
          cases hseq with
          | single hterm =>
              exact PureHasType.block (PureHasSeq.single (ih hterm))
  | blockSingleValue hv =>
      cases ht with
      | block hseq =>
          cases hseq with
          | single hterm => exact hterm
  | blockHeadStep hs ih =>
      cases ht with
      | block hseq =>
          cases hseq with
          | cons hterm hrest =>
              exact PureHasType.block (PureHasSeq.cons (ih hterm) hrest)
  | blockHeadValue hv =>
      cases ht with
      | block hseq =>
          cases hseq with
          | cons hterm hrest =>
              exact PureHasType.block hrest

theorem pure_preservation_multi {term term' : Term} {ty : Ty} :
    PureHasType term ty → PureMultiStep term term' → PureHasType term' ty := by
  intro ht hsteps
  induction hsteps with
  | refl _ => exact ht
  | trans hstep hmulti ih =>
      exact ih (pure_preservation ht hstep)

/-- Type soundness for the Featherweight-Rust-shaped pure fragment. -/
theorem pure_soundness_step {term : Term} {ty : Ty} :
    PureHasType term ty →
      PureValue term ∨ ∃ term', PureStep term term' ∧ PureHasType term' ty := by
  intro ht
  cases pure_progress_term ht with
  | inl hv => exact Or.inl hv
  | inr hstep =>
      rcases hstep with ⟨term', hs⟩
      exact Or.inr ⟨term', hs, pure_preservation ht hs⟩

/-- Multi-step type soundness for the Featherweight-Rust-shaped pure fragment:
after any finite reduction sequence, a well-typed pure term is either a value or
can step again to a term of the same type. -/
theorem pure_soundness_multi {term term' : Term} {ty : Ty} :
    PureHasType term ty →
    PureMultiStep term term' →
      PureValue term' ∨ ∃ term'', PureStep term' term'' ∧ PureHasType term'' ty := by
  intro ht hsteps
  exact pure_soundness_step (pure_preservation_multi ht hsteps)

theorem pure_normal_form_value {term : Term} {ty : Ty} :
    PureHasType term ty →
    (∀ term', ¬ PureStep term term') →
    PureValue term := by
  intro ht hnormal
  cases pure_progress_term ht with
  | inl hv => exact hv
  | inr hstep =>
      rcases hstep with ⟨term', hs⟩
      exact False.elim (hnormal term' hs)

end PureFR

end Proofs
end Core
end LwRust
