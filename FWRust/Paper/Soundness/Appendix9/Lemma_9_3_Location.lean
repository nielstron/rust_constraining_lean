import FWRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Lemma 9.3 (Location)

> Let `S` be a program store; let `Γ` be a well-formed typing environment where
> `S ∼ Γ`; let `w` be an lval and `T̃` a partial type.  If `Γ ⊢ w : T̃^m` then
> `loc(S, w)` is defined (and reads/writes through `w` are well defined).

Status: mechanized as the location-availability facts feeding
`readPreservation`/`progress`; see `lvalTyping_allocated_location` and
`readPreservation_of_location` in `FWRust.Paper.Soundness`.  The end-to-end
"read is defined and valid" packaging is Corollary 9.4 below.
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

/-- Lemma 9.3, location availability for a typed lval (proven): `loc(S, w)` is
defined and points to an allocated slot. -/
theorem lemma_9_3_location
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {lv : LVal} {ty : Ty} {lifetime : Lifetime}
    (hwellFormed : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (htyping : LValTyping env lv (.ty ty) lifetime) :
    ∃ location slot,
      store.loc lv = some location ∧ store.slotAt location = some slot :=
  lvalTyping_allocated_location hwellFormed hsafe htyping

end FWRust.Paper.Soundness
