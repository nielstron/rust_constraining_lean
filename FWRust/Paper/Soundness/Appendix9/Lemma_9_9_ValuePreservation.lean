import FWRust.Paper.Soundness.Lemma_4_11_Preservation

/-!
# Lemma 9.9 (Value Preservation)

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; … then the final
> value is abstracted by the result type: `S₂ ▷ v ∼ T`.

Status: proved as the value-validity projection of Preservation (Lemma 4.11).
The file also exposes representative redex-level frame lemmas for move/value
cases.
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
    store ∼ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    ValidValue finalStore finalValue ty := by
    intro hsource hvalid hstoreTyping hwellFormed hborrowSafe hfinite hlinear
      hsafe htyping hmulti
    exact (lemma_4_11_preservation hsource hvalid hstoreTyping hwellFormed
      hborrowSafe hfinite hlinear hsafe htyping hmulti).2.2

/--
Appendix 9.9, `R-Move` post-write value preservation under the concrete frame
condition that the overwritten location is not inspected by the moved value's
pre-write abstraction.
-/
theorem lemma_9_9_move_postwrite_frame {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ env →
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
    store ∼ env →
    TermTyping env typing lifetime (.move lv) .unit env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .unit :=
  valuePreservation_move_step_unit_post

/-- Appendix 9.9, `R-Move` post-write value preservation for integer results. -/
theorem lemma_9_9_move_int_postwrite {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    WellFormedEnv env current →
    store ∼ env →
    TermTyping env typing lifetime (.move lv) .int env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .int :=
  valuePreservation_move_step_int_post

end FWRust.Paper.Soundness
