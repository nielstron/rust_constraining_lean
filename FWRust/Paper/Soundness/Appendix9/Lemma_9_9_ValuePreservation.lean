import FWRust.Paper.Soundness.Appendix9.Lemma_9_8_AliasPreservation

/-!
# Lemma 9.9 (Value Preservation)

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; … then the final
> value is abstracted by the result type: `S₂ ▷ v ∼ T`.

The multistep theorem remains a value-validity projection of Preservation
(Lemma 4.11).  The one-step theorem instead projects the independent shared
terminal-redex proof in Lemma 9.8, which accepts already evaluated runtime
values and uses no finite-support premise.  The file also exposes representative
redex-level frame lemmas for move/value cases.
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

/--
Appendix 9.9, Value Preservation: the value-abstraction projection of
Lemma 4.11.
-/
theorem lemma_9_9_valuePreservation
    {store finalStore : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    Env.FiniteSupport env₁ →
    Linearizable env₁ →
    store ≈ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    ValidValue finalStore finalValue ty := by
    intro hsource hvalid hstoreTyping hwellFormed hborrowSafe hfinite hlinear
      hsafe htyping hmulti
    exact (lemma_4_11_preservation hsource hvalid hstoreTyping hwellFormed
      hborrowSafe hfinite hlinear hsafe htyping hmulti).2.2

/--
The Appendix 9.9 one-step conclusion, exposed as the value projection of
`appendix_9_oneStep_fullPreservation_of_runtime_invariants`, not of the global
source-term theorem.  `RuntimeRedexBorrowSafe` supplies the assignment-only
static fact that runtime validity and store typing do not record.
-/
theorem lemma_9_9_valuePreservation_oneStep_of_runtime_invariants
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value}
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hredexBorrowSafe : RuntimeRedexBorrowSafe env₁ typing term)
    (hlinear : Linearizable env₁)
    (hsafe : store ≈ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hstep : Step store lifetime term finalStore (.val finalValue)) :
    ValidValue finalStore finalValue ty := by
  exact
    (appendix_9_oneStep_fullPreservation_of_runtime_invariants hvalid
      hstoreTyping hwellFormed hborrowSafe hredexBorrowSafe hlinear hsafe
      htyping hstep).2.2

/-- Source-initial one-step value preservation with all extra invariants derived. -/
theorem lemma_9_9_valuePreservation_oneStep_empty
    {finalStore : ProgramStore} {env₂ : Env} {lifetime : Lifetime}
    {term : Term} {ty : Ty} {finalValue : Value}
    (htyping :
      TermTyping Env.empty StoreTyping.empty lifetime term ty env₂)
    (hstep :
      Step ProgramStore.empty lifetime term finalStore (.val finalValue)) :
    ValidValue finalStore finalValue ty := by
  exact (emptyInitial_preservation htyping
    (MultiStep.trans hstep MultiStep.refl)).2.2

/--
Appendix 9.9, `R-Move` post-write value preservation under the concrete frame
condition that the overwritten location is not inspected by the moved value's
pre-write abstraction.
-/
theorem lemma_9_9_move_postwrite_frame {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ≈ₛ env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    (∀ updated slot,
      store.loc lv = some updated →
      store.slotAt updated = some slot →
      ∀ ℓ, RuntimeFrame.Reaches store (.value value) (.ty ty) ℓ → ℓ ≠ updated) →
    ValidValue store' value ty :=
  valuePreservation_move_step_of_not_reaches

/-- Appendix 9.9, `R-Move` post-write value preservation for unit results. -/
theorem lemma_9_9_move_unit_postwrite {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    WellFormedEnv env current →
    store ≈ₛ env →
    TermTyping env typing lifetime (.move lv) .unit env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .unit :=
  valuePreservation_move_step_unit_post

/-- Appendix 9.9, `R-Move` post-write value preservation for integer results. -/
theorem lemma_9_9_move_int_postwrite {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    WellFormedEnv env current →
    store ≈ₛ env →
    TermTyping env typing lifetime (.move lv) .int env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .int :=
  valuePreservation_move_step_int_post

end FWRust.Paper.Soundness
