import FWRust.Paper.Soundness.Appendix9.Lemma_9_3_Location

/-!
# Corollary 9.4 (Read Preservation)

> Let `S` be a program store; let `Γ` be a well-formed typing environment where
> `S ∼ Γ`.  If `Γ ⊢ w : T^m` then `read(S, w)` is defined and its value is
> abstracted by `T` (`S ⊢ read(S, w) ∼ T`).

The defined-read and value-abstraction claims are fully proven below.  The
printed claim that the returned slot has exactly lifetime `m` is not asserted:
`lemma_9_3_lifetime_index_counterexample` proves that equality false for a
well-formed, safely abstracted boxed value in the current encoding.
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

/--
Paper-shaped read preservation with the actual allocation lifetime exposed
separately.  The read is defined, contains a full value, and that value has the
typed lval's full type.  No false equality between `slotLifetime` and the lval
typing lifetime is hidden in the statement.
-/
theorem corollary_9_4_read_value
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {lv : LVal} {ty : Ty} {lifetime : Lifetime}
    (hwellFormed : WellFormedEnv env current)
    (hsafe : store ≈ₛ env)
    (htyping : LValTyping env lv (.ty ty) lifetime) :
    ∃ value slotLifetime,
      store.read lv =
        some { value := .value value, lifetime := slotLifetime } ∧
      ValidValue store value ty := by
  rcases readPreservation hwellFormed hsafe htyping with
    ⟨value, ⟨partialValue, slotLifetime⟩, hread, hvalue, hvalid⟩
  cases hvalue
  exact ⟨value, slotLifetime, hread, hvalid⟩

/-- Compatibility packaging of the same result with the complete runtime slot. -/
theorem corollary_9_4_readPreservation
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {lv : LVal} {ty : Ty} {lifetime : Lifetime}
    (hwellFormed : WellFormedEnv env current)
    (hsafe : store ≈ₛ env)
    (htyping : LValTyping env lv (.ty ty) lifetime) :
    ∃ value slot,
      store.read lv = some slot ∧
        slot.value = .value value ∧
        ValidValue store value ty :=
  readPreservation hwellFormed hsafe htyping

end FWRust.Paper.Soundness
