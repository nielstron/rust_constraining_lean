import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety

/-!
# Lemma 9.9 (Value Preservation)

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; … then the final
> value is abstracted by the result type: `S₂ ▷ v ∼ T`.

Status: **in progress** — this is the `ValidValue finalStore finalValue ty`
conjunct of `TerminalStateSafe`, established by Preservation (Lemma 4.11).  The
base cases (`R-Copy`, pre-write `R-Move` via Corollary 9.4, post-write `R-Move`
for ground `unit`/`int` results and under the explicit reachability frame
condition, `&[mut] w` via Lemma 9.3, `box`/`declare` via the multistep fragments
`preservation_box_context_terminal_multistep_runtime`,
`preservation_declare_multistep_runtime`) are mechanized; the move/assign/block
cases are the corresponding `RuntimePreservationObligations` fields.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/--
Appendix 9.9, `R-Move` post-write value preservation under the concrete frame
condition that the overwritten location is not inspected by the moved value's
pre-write abstraction.
-/
theorem lemma_9_9_move_postwrite_frame {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
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
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) .unit env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .unit :=
  valuePreservation_move_step_unit_post

/-- Appendix 9.9, `R-Move` post-write value preservation for integer results. -/
theorem lemma_9_9_move_int_postwrite {store store' : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {current lifetime : Lifetime}
    {lv : LVal} {value : Value} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing lifetime (.move lv) .int env₂ →
    Step store lifetime (.move lv) store' (.val value) →
    ValidValue store' value .int :=
  valuePreservation_move_step_int_post

end LwRust.Paper.Soundness
