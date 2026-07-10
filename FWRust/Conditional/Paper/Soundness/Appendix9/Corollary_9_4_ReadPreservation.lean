import FWRust.Conditional.Paper.Soundness.Helpers.BorrowSafety

/-!
# Corollary 9.4 (Read Preservation)

> Let `S` be a program store; let `Γ` be a well-formed typing environment where
> `S ∼ Γ`.  If `Γ ⊢ w : T^m` then `read(S, w)` is defined and its value is
> abstracted by `T` (`S ⊢ read(S, w) ∼ T`).

Status: **fully proven** (`readPreservation`).  Follows from Lemma 9.3 and
Definition 3.2.
-/

namespace FWRust.Conditional.Paper.Soundness

open FWRust.Conditional.Paper FWRust.Conditional.Core

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

end FWRust.Conditional.Paper.Soundness
