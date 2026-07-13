import FWRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Lemma 9.3 (Location)

> Let `S` be a program store; let `Γ` be a well-formed typing environment where
> `S ∼ Γ`; let `w` be an lval and `T̃` a partial type.  If `Γ ⊢ w : T̃^m` then
> `loc(S, w)` is defined (and reads/writes through `w` are well defined).

The location and partial-value claims are mechanized below.  The printed
allocation-lifetime equality is deliberately separated: it is false for the
current concrete encoding because `LValTyping.boxFull` retains the lifetime of
the box variable while `ProgramStore.boxAt` gives its heap slot
`Lifetime.root`.  `lemma_9_3_lifetime_index_counterexample` is a closed Lean
witness of that mismatch.
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

/--
The valid-location/value content of Lemma 9.3, for the paper's arbitrary
partial type.  This is the strongest faithful statement supported by the
current encoding without asserting that the reached slot has the lval's
typing lifetime; the counterexample below shows that extra equality is false.
-/
theorem lemma_9_3_location_value
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {lv : LVal} {ty : PartialTy} {lifetime : Lifetime}
    (_hwellFormed : WellFormedEnv env current)
    (hsafe : store ≈ₛ env)
    (htyping : LValTyping env lv ty lifetime) :
    ∃ location slot,
      store.loc lv = some location ∧
      store.slotAt location = some slot ∧
      ValidPartialValue store slot.value ty := by
  induction htyping with
  | var hslot =>
      exact location_var hsafe hslot
  | box _hbox ih =>
      exact location_box ih
  | boxFull _hbox ih =>
      exact location_boxFull ih
  | borrow _hborrow _htarget ihBorrow ihTarget =>
      rcases ihBorrow with
        ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hvalidBorrow with
      | borrow htargetLocFromBorrow =>
          rcases ihTarget with
            ⟨targetLocation, targetSlot, htargetLoc, htargetSlot,
              htargetValid⟩
          have hlocationEq : targetLocation = _ :=
            Option.some.inj (htargetLoc.symm.trans htargetLocFromBorrow)
          subst hlocationEq
          exact ⟨targetLocation, targetSlot, by
              simp [ProgramStore.loc, hsourceLoc, hsourceSlot],
            htargetSlot, htargetValid⟩

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

/--
Concrete obstruction to the lifetime-indexed conclusion printed in Lemma 9.3
(and reused in Corollary 9.4).  A child-lifetime variable owns a `boxAt` heap
slot.  The dereferenced lval is typed at the child lifetime, but the heap slot
returned by `read` has the root lifetime.  All of the paper-facing
well-formedness, safe-abstraction, and lval-typing premises hold.
-/
theorem lemma_9_3_lifetime_index_counterexample :
    ∃ (store : ProgramStore) (env : Env) (current : Lifetime)
      (lv : LVal) (ty : Ty) (lifetime : Lifetime) (slot : StoreSlot),
      WellFormedEnv env current ∧
      store ≈ₛ env ∧
      LValTyping env lv (.ty ty) lifetime ∧
      store.read lv = some slot ∧
      slot.lifetime ≠ lifetime := by
  let child : Lifetime := ([0] : Lifetime)
  let heapStore : ProgramStore :=
    (ProgramStore.empty.boxAt 0 (.int 7)).1
  let owner : Reference :=
    (ProgramStore.empty.boxAt 0 (.int 7)).2
  let store : ProgramStore :=
    heapStore.declare "x" child (.ref owner)
  let env : Env := Env.empty.update "x"
    { ty := .ty (.box .int), lifetime := child }
  have hfreshHeap : ProgramStore.empty.fresh (.heap 0) := by
    simp [ProgramStore.fresh]
  have hfreshVar : heapStore.fresh (.var "x") := by
    simp [heapStore, ProgramStore.fresh, ProgramStore.boxAt,
      ProgramStore.update]
  have hownerValidHeap :
      ValidValue heapStore (.ref owner) (.box .int) := by
    exact validValue_boxAt_ref hfreshHeap
      (show ValidValue ProgramStore.empty (.int 7) .int from
        ValidPartialValue.int)
  have hownerValidStore :
      ValidValue store (.ref owner) (.box .int) := by
    exact validPartialValue_declare hfreshVar hownerValidHeap
  have hheapSafe : heapStore ≈ₛ Env.empty := by
    exact safeAbstraction_boxAt hfreshHeap fullSafeAbstraction_empty
  have hfull : store ≈ₛ env := by
    exact safeAbstraction_declare hheapSafe
      (by simp [Env.fresh, Env.empty]) hownerValidStore
      (by
        intro y envSlot oldValue _hy henvSlot _hstoreSlot
        simp [Env.empty] at henvSlot)
  have hwell : WellFormedEnv env child := by
    exact WellFormedEnv.update_fresh_ty (wellFormedEnv_empty child)
      (WellFormedTy.box WellFormedTy.int)
      (by simp [Env.fresh, Env.empty])
  have htyping :
      LValTyping env (.deref (.var "x")) (.ty .int) child := by
    apply LValTyping.boxFull
    exact LValTyping.var (env := env) (x := "x")
      (slot := { ty := .ty (.box .int), lifetime := child })
      (by simp [env])
  let slot : StoreSlot :=
    { value := .value (.int 7), lifetime := Lifetime.root }
  refine ⟨store, env, child, .deref (.var "x"), .int, child, slot,
    hwell, hfull, htyping, ?_, ?_⟩
  · simp [store, heapStore, owner, slot, ProgramStore.read,
      ProgramStore.loc, ProgramStore.declare, ProgramStore.boxAt,
      ProgramStore.update]
  · simp [slot, child, Lifetime.root]

end FWRust.Paper.Soundness
