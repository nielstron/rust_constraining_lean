import LwRust.Paper.Soundness.Helpers.ValuePreservation
import LwRust.Paper.Soundness.Helpers.GhostErasure

/-!
# Lemma 4.10 (Progress)

Paper statement (Section 4.4):

> Let `S₁ ▷ t₁` be a valid state; let `σ` be a store typing where `S₁ ▷ t₁ ⊢ σ`;
> let `Γ₁` be a well-formed typing environment with respect to a lifetime `l`
> where `S₁ ∼ Γ₁`; let `Γ₂` be a typing environment; and let `T` be a type.
> If `Γ₁ ⊢ ⟨t₁ : T⟩^l_σ ⊣ Γ₂`, then either `t₁ ∈ Value` or
> `⟨S₁ ▷ t₁ ⟶ S₂ ▷ t₂⟩^l` for some state `S₂ ▷ t₂`.

Status: **fully proven** (closed proof, no obligations).  `OperationalStoreProgress`
is the explicit drop/allocation availability premise the abstract store model
needs (it holds for all concrete stores, see `ConcreteProgramStore`).

This file carries all the progress-support material (Section 4.4) needed to
prove the lemma; it ends with the paper-facing statement `lemma_4_10_progress`.
-/

namespace LwRust
namespace Paper

open Core

/-! ## Section 4.4: Progress Support -/

/-- Lemma 4.10 result shape: a term is terminal or can take one step. -/
def ProgressResult (store : ProgramStore) (lifetime : Lifetime) (term : Term) : Prop :=
  Terminal term ∨ ∃ store' term', Step store lifetime term store' term'

/--
Operational totality facts the paper gets from finite program stores.

Our `ProgramStore` is an abstract partial map, so these are separated as an
explicit progress assumption instead of being postulated globally.
-/
structure OperationalStoreProgress (store : ProgramStore) : Prop where
  freshHeap : ∃ address, store.fresh (.heap address)
  dropValue : ∀ value : Value, ∃ store', Drops store [.value value] store'
  dropPartial : ∀ value : PartialValue, ∃ store', Drops store [value] store'
  assignValue : ∀ lhs oldSlot value,
    store.read lhs = some oldSlot →
    ∃ storeAfterWrite storeAfterDrop,
      store.write lhs (.value value) = some storeAfterWrite ∧
      Drops storeAfterWrite [oldSlot.value] storeAfterDrop
  dropLifetime : ∀ lifetime : Lifetime, ∃ store', DropsLifetime store lifetime store'

/-! ### Drop Existence Fragments -/

theorem drops_nonOwner {store : ProgramStore} {value : PartialValue} :
    PartialValueNonOwner value →
    Drops store [value] store := by
  intro hnonOwner
  exact ProgramStore.Drops.nonOwner hnonOwner ProgramStore.Drops.nil

/--
Finite-support drop existence.

The paper treats stores as finite maps, so recursive `drop` always terminates:
an owning-reference drop either finds no slot or erases one supported location
before continuing.  This lemma is the abstract support-based form used to derive
operational progress for concrete finite stores.
-/
theorem drops_exists_of_supported :
    ∀ (support : Finset Location) (store : ProgramStore) (values : List PartialValue),
      (∀ location slot, store.slotAt location = some slot → location ∈ support) →
      ∃ store', Drops store values store'
  | support, store, [], _hsupported => ⟨store, ProgramStore.Drops.nil⟩
  | support, store, value :: rest, hsupported => by
      cases value with
      | undef =>
          rcases drops_exists_of_supported support store rest hsupported with
            ⟨store', hdrops⟩
          exact ⟨store', ProgramStore.Drops.nonOwner partialValueNonOwner_undef hdrops⟩
      | value runtimeValue =>
          cases runtimeValue with
          | unit =>
              rcases drops_exists_of_supported support store rest hsupported with
                ⟨store', hdrops⟩
              exact ⟨store', ProgramStore.Drops.nonOwner partialValueNonOwner_unit hdrops⟩
          | int n =>
              rcases drops_exists_of_supported support store rest hsupported with
                ⟨store', hdrops⟩
              exact ⟨store', ProgramStore.Drops.nonOwner (partialValueNonOwner_int n) hdrops⟩
          | bool b =>
              rcases drops_exists_of_supported support store rest hsupported with
                ⟨store', hdrops⟩
              exact ⟨store', ProgramStore.Drops.nonOwner (partialValueNonOwner_bool b) hdrops⟩
          | ref ref =>
              cases howner : ref.owner with
              | false =>
                  rcases drops_exists_of_supported support store rest hsupported with
                    ⟨store', hdrops⟩
                  exact ⟨store', ProgramStore.Drops.nonOwner (by
                    cases ref with
                    | mk location owner =>
                        simp at howner
                        subst howner
                        exact partialValueNonOwner_borrowed location) hdrops⟩
              | true =>
                  by_cases hpresent : ∃ slot, store.slotAt ref.location = some slot
                  · rcases hpresent with ⟨slot, hslot⟩
                    have hmem : ref.location ∈ support :=
                      hsupported ref.location slot hslot
                    have hsupportedErase :
                        ∀ location slot',
                          (store.erase ref.location).slotAt location = some slot' →
                          location ∈ support.erase ref.location := by
                      intro location slot' hslot'
                      by_cases hsame : location = ref.location
                      · subst hsame
                        simp [ProgramStore.erase] at hslot'
                      · have hslotOriginal : store.slotAt location = some slot' := by
                          simpa [ProgramStore.erase, hsame] using hslot'
                        exact Finset.mem_erase.mpr
                          ⟨hsame, hsupported location slot' hslotOriginal⟩
                    rcases drops_exists_of_supported (support.erase ref.location)
                        (store.erase ref.location) (slot.value :: rest) hsupportedErase with
                      ⟨store', hdrops⟩
                    exact ⟨store',
                      ProgramStore.Drops.ownerPresent howner hslot hdrops⟩
                  · have hmissing : store.slotAt ref.location = none := by
                      cases hslot : store.slotAt ref.location with
                      | none => rfl
                      | some slot =>
                          exact False.elim (hpresent ⟨slot, hslot⟩)
                    rcases drops_exists_of_supported support store rest hsupported with
                      ⟨store', hdrops⟩
                    exact ⟨store',
                      ProgramStore.Drops.ownerMissing howner hmissing hdrops⟩
termination_by support _store values => support.card + values.length
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have hcard : (support.erase ref.location).card < support.card :=
        Finset.card_erase_lt_of_mem hmem
      omega

private theorem drops_nonOwner_primitive : ∀ {v : PartialValue},
    PartialValueNonOwner v →
    ∃ store', Drops ProgramStore.empty [v] store' :=
  fun {v} hnonOwner => ⟨ProgramStore.empty, drops_nonOwner hnonOwner⟩

theorem drops_empty_value (value : Value) :
    ∃ store', Drops ProgramStore.empty [.value value] store' := by
  cases value with
  | unit | int _ | bool _ =>
      exact drops_nonOwner_primitive (by intro ref; exact Or.inl (by simp))
  | ref ref =>
      cases howner : ref.owner with
      | false =>
          exact ⟨ProgramStore.empty,
            drops_nonOwner (by
              intro candidate
              by_cases href : PartialValue.value (Value.ref ref) =
                  PartialValue.value (Value.ref candidate)
              · injection href with hrefValue
                injection hrefValue with hrefRef
                subst hrefRef
                exact Or.inr howner
              · exact Or.inl href)⟩
      | true =>
          exact ⟨ProgramStore.empty,
            ProgramStore.Drops.ownerMissing howner (by simp [ProgramStore.empty])
              ProgramStore.Drops.nil⟩

theorem drops_empty_partial (value : PartialValue) :
    ∃ store', Drops ProgramStore.empty [value] store' := by
  cases value with
  | undef =>
      exact drops_nonOwner_primitive (by intro ref; exact Or.inl (by simp))
  | value value =>
      exact drops_empty_value value

theorem drops_empty_lifetime (lifetime : Lifetime) :
    ∃ store', DropsLifetime ProgramStore.empty lifetime store' := by
  exact ⟨ProgramStore.empty, ProgramStore.DropsLifetime.intro (dropSet := []) (by
      intro value
      constructor
      · intro hmem
        cases hmem
      · intro h
        rcases h with ⟨location, slot, hslot, _hlifetime, _hvalue⟩
        simp [ProgramStore.empty] at hslot)
    ProgramStore.Drops.nil⟩

/-! ### Finite-support stores -/

/--
A program store with finitely many allocated locations.

This is the step-stable form of the paper's finite-store model: every
operational totality fact in `OperationalStoreProgress` follows from it
(`OperationalStoreProgress.of_finiteSupport`), and, unlike
`OperationalStoreProgress` itself, it is preserved by reduction steps
(`ProgramStore.FiniteSupport.step`).
-/
def ProgramStore.FiniteSupport (store : ProgramStore) : Prop :=
  ∃ support : Finset Location,
    ∀ location slot, store.slotAt location = some slot → location ∈ support

theorem ProgramStore.finiteSupport_empty : ProgramStore.empty.FiniteSupport :=
  ⟨∅, by intro location slot h; simp [ProgramStore.empty] at h⟩

theorem ProgramStore.FiniteSupport.update {store : ProgramStore}
    {location : Location} {slot : StoreSlot} :
    store.FiniteSupport → (store.update location slot).FiniteSupport := by
  rintro ⟨support, hsupport⟩
  refine ⟨insert location support, ?_⟩
  intro candidate slot' hslot'
  by_cases hsame : candidate = location
  · subst hsame
    exact Finset.mem_insert_self _ _
  · rw [ProgramStore.update_slotAt_ne _ _ hsame] at hslot'
    exact Finset.mem_insert_of_mem (hsupport candidate slot' hslot')

theorem ProgramStore.FiniteSupport.erase {store : ProgramStore}
    {location : Location} :
    store.FiniteSupport → (store.erase location).FiniteSupport := by
  rintro ⟨support, hsupport⟩
  refine ⟨support, ?_⟩
  intro candidate slot' hslot'
  by_cases hsame : candidate = location
  · subst hsame
    simp at hslot'
  · rw [ProgramStore.erase_slotAt_ne _ hsame] at hslot'
    exact hsupport candidate slot' hslot'

theorem ProgramStore.FiniteSupport.write {store store' : ProgramStore}
    {lv : LVal} {value : PartialValue} :
    store.write lv value = some store' →
    store.FiniteSupport →
    store'.FiniteSupport := by
  intro hwrite hfs
  simp only [ProgramStore.write, Option.bind_eq_bind, Option.bind_eq_some_iff] at hwrite
  rcases hwrite with ⟨location, _hloc, slot, _hslot, hstore'⟩
  cases hstore'
  exact hfs.update

theorem ProgramStore.FiniteSupport.declare {store : ProgramStore}
    {x : Name} {lifetime : Lifetime} {value : Value} :
    store.FiniteSupport → (store.declare x lifetime value).FiniteSupport :=
  ProgramStore.FiniteSupport.update

theorem ProgramStore.FiniteSupport.boxAt {store store' : ProgramStore}
    {address : Nat} {value : Value} {ref : Reference} :
    store.boxAt address value = (store', ref) →
    store.FiniteSupport →
    store'.FiniteSupport := by
  intro hbox hfs
  have hstore' : store' = store.update (.heap address)
      { value := .value value, lifetime := Lifetime.root } :=
    (congrArg Prod.fst hbox).symm
  subst hstore'
  exact hfs.update

theorem ProgramStore.FiniteSupport.drops {store store' : ProgramStore}
    {values : List PartialValue} :
    Drops store values store' →
    store.FiniteSupport →
    store'.FiniteSupport := by
  intro hdrops
  induction hdrops with
  | nil => exact id
  | nonOwner _ _ ih | ownerMissing _ _ _ ih => exact ih
  | ownerPresent _ _ _ ih => exact fun hfs => ih hfs.erase

theorem ProgramStore.FiniteSupport.dropsLifetime {store store' : ProgramStore}
    {lifetime : Lifetime} :
    DropsLifetime store lifetime store' →
    store.FiniteSupport →
    store'.FiniteSupport := by
  rintro ⟨_, hdrops⟩
  exact ProgramStore.FiniteSupport.drops hdrops

/-- Finite support is preserved by every reduction step. -/
theorem ProgramStore.FiniteSupport.step {store store' : ProgramStore}
    {lifetime : Lifetime} {term term' : Term} :
    Step store lifetime term store' term' →
    store.FiniteSupport →
    store'.FiniteSupport := by
  intro hstep
  induction hstep with
  | missing | copy _ | borrow _ => exact id
  | move _ hwrite => exact ProgramStore.FiniteSupport.write hwrite
  | box _ hbox => exact ProgramStore.FiniteSupport.boxAt hbox
  | assign _ hwrite hdrops =>
      exact fun hfs =>
        ProgramStore.FiniteSupport.drops hdrops
          (ProgramStore.FiniteSupport.write hwrite hfs)
  | declare hstore =>
      exact fun hfs => hstore ▸ hfs.declare
  | seq hdrops => exact ProgramStore.FiniteSupport.drops hdrops
  | blockA _ ih => exact ih
  | blockB hdrops => exact ProgramStore.FiniteSupport.dropsLifetime hdrops
  | subBox _ ih | subDeclare _ ih | subAssign _ ih => exact ih
  | eqTrue | eqFalse _ | iteTrue | iteFalse => exact id
  | subEqLeft _ ih | subEqRight _ ih | subIte _ ih => exact ih

/-- Finite support is preserved along any execution. -/
theorem ProgramStore.FiniteSupport.multiStep {store store' : ProgramStore}
    {lifetime : Lifetime} {term term' : Term} :
    MultiStep store lifetime term store' term' →
    store.FiniteSupport →
    store'.FiniteSupport := by
  intro hmulti
  induction hmulti with
  | refl => exact id
  | trans hstep _ ih => exact fun hfs => ih (hfs.step hstep)

private theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) :
    x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons head tail ih =>
      rcases List.mem_cons.mp h with hhead | htail
      · subst hhead
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

/--
Every operational totality fact needed by Progress holds for finite-support
stores.  This discharges `OperationalStoreProgress` at every reachable state
via `ProgramStore.FiniteSupport.multiStep`.
-/
theorem OperationalStoreProgress.of_finiteSupport {store : ProgramStore} :
    store.FiniteSupport →
    OperationalStoreProgress store := by
  rintro ⟨support, hsupport⟩
  constructor
  · -- a fresh heap address exists beyond the finitely many allocated ones
    classical
    refine ⟨(support.toList.filterMap fun location =>
        match location with
        | .heap address => some address
        | .var _ => none).foldr max 0 + 1, ?_⟩
    cases hslot : store.slotAt
        (.heap ((support.toList.filterMap fun location =>
          match location with
          | .heap address => some address
          | .var _ => none).foldr max 0 + 1)) with
    | none => exact hslot
    | some slot =>
        exfalso
        have haddr : ((support.toList.filterMap fun location =>
            match location with
            | .heap address => some address
            | .var _ => none).foldr max 0 + 1) ∈
            (support.toList.filterMap fun location =>
              match location with
              | .heap address => some address
              | .var _ => none) :=
          List.mem_filterMap.mpr ⟨_, Finset.mem_toList.mpr (hsupport _ _ hslot), rfl⟩
        exact Nat.not_succ_le_self _ (le_foldr_max haddr)
  · intro value
    exact drops_exists_of_supported support store [.value value] hsupport
  · intro value
    exact drops_exists_of_supported support store [value] hsupport
  · -- writes to readable lvals succeed, and the old value can be dropped
    intro lhs oldSlot value hread
    cases hloc : store.loc lhs with
    | none => simp [ProgramStore.read, hloc] at hread
    | some location =>
    have hslot : store.slotAt location = some oldSlot := by
      simpa [ProgramStore.read, hloc] using hread
    have hsupportAfter : ∀ candidate slot',
        (store.update location
          { oldSlot with value := .value value }).slotAt candidate =
            some slot' →
        candidate ∈ support := by
      intro candidate slot' hslot'
      by_cases hsame : candidate = location
      · subst hsame
        exact hsupport candidate oldSlot hslot
      · rw [ProgramStore.update_slotAt_ne _ _ hsame] at hslot'
        exact hsupport candidate slot' hslot'
    rcases drops_exists_of_supported support _ [oldSlot.value] hsupportAfter
      with ⟨storeAfterDrop, hdrops⟩
    exact ⟨store.update location { oldSlot with value := .value value },
      storeAfterDrop, by simp [ProgramStore.write, hloc, hslot], hdrops⟩
  · -- the slots of any lifetime form a finite drop set
    intro lifetime
    classical
    have hpred :
        DecidablePred fun location : Location =>
          ∃ slot, store.slotAt location = some slot ∧
            slot.lifetime = lifetime :=
      fun _ => Classical.propDecidable _
    rcases drops_exists_of_supported support store
        (((support.filter fun location =>
            ∃ slot, store.slotAt location = some slot ∧
              slot.lifetime = lifetime).toList.map
          fun location => PartialValue.value (.ref { location := location, owner := true })))
        hsupport with ⟨store', hdrops⟩
    refine ⟨store', ProgramStore.DropsLifetime.intro ?_ hdrops⟩
    intro value
    constructor
    · intro hmem
      rcases List.mem_map.mp hmem with ⟨location, hmemFilter, hvalue⟩
      rcases Finset.mem_filter.mp (Finset.mem_toList.mp hmemFilter) with
        ⟨_hmemSupport, slot, hslot, hlifetime⟩
      exact ⟨location, slot, hslot, hlifetime, hvalue.symm⟩
    · rintro ⟨location, slot, hslot, hlifetime, hvalue⟩
      subst hvalue
      exact List.mem_map.mpr ⟨location,
        Finset.mem_toList.mpr (Finset.mem_filter.mpr
          ⟨hsupport location slot hslot, slot, hslot, hlifetime⟩), rfl⟩

@[simp] theorem operationalStoreProgress_empty :
    OperationalStoreProgress ProgramStore.empty := by
  constructor
  · exact ⟨0, by simp [ProgramStore.fresh, ProgramStore.empty]⟩
  · exact drops_empty_value
  · exact drops_empty_partial
  · intro lhs oldSlot value hread
    simp [ProgramStore.read, ProgramStore.empty] at hread
  · exact drops_empty_lifetime

/--
A program store bundled with the operational witnesses needed by Progress.

This is intentionally a certified wrapper around `ProgramStore`, not a
replacement for the paper's mathematical store.  The bare `ProgramStore` is an
arbitrary partial-map function, so progress cannot prove freshness/drop/write
totality for every inhabitant without an additional finite/well-behaved-store
invariant.
-/
structure OperationalProgramStore where
  toProgramStore : ProgramStore
  progress : OperationalStoreProgress toProgramStore

namespace OperationalProgramStore

instance : Coe OperationalProgramStore ProgramStore where
  coe store := store.toProgramStore

@[simp] theorem operationalStoreProgress (store : OperationalProgramStore) :
    OperationalStoreProgress (store : ProgramStore) :=
  store.progress

@[simp] def empty : OperationalProgramStore :=
  { toProgramStore := ProgramStore.empty
    progress := operationalStoreProgress_empty }

end OperationalProgramStore

theorem ProgressResult.step_of_not_terminal {store : ProgramStore}
    {lifetime : Lifetime} {term : Term} :
    ProgressResult store lifetime term →
    ¬ Terminal term →
    ∃ store' term', Step store lifetime term store' term' := by
  intro hprogress hnotTerminal
  rcases hprogress with hterminal | hstep
  · exact False.elim (hnotTerminal hterminal)
  · exact hstep

/-- Case split on a sub-term's progress result: either the sub-term is
already a value, or its step lifts to the surrounding context.  The two
lifetimes differ when the sub-term steps under a block lifetime. -/
theorem ProgressResult.elim_value {store : ProgramStore}
    {inner outer : Lifetime} {term big : Term}
    (hprogress : ProgressResult store inner term)
    (hvalue : ∀ value, term = .val value → ProgressResult store outer big)
    (hstep : (∃ store' term', Step store inner term store' term') →
      ProgressResult store outer big) :
    ProgressResult store outer big := by
  rcases hprogress with hterminal | h
  · rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
    exact hvalue value hterm
  · exact hstep h

/-- Lemma 4.10, `T-Const`/value case. -/
theorem progress_value (store : ProgramStore) (lifetime : Lifetime) (value : Value) :
    ProgressResult store lifetime (.val value) := by
  exact Or.inl (value_terminal value)

/-- Lemma 4.10, `R-Copy` lval base case. -/
theorem progress_copy_lval_of_safe {store : ProgramStore} {env : Env}
    {stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ value,
      Step store stepLifetime (.copy lv) store (.val value) := by
  intro hsafe htyping
  rcases readPreservation_of_safe hsafe htyping with
    ⟨value, runtimeSlot, hread, hslotValue, _hvalid⟩
  rcases runtimeSlot with ⟨partialValue, runtimeLifetime⟩
  cases hslotValue
  exact ⟨value, Step.copy (valueLifetime := runtimeLifetime) hread⟩

theorem progress_copy_lval {store : ProgramStore} {env : Env}
    {current stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ value,
      Step store stepLifetime (.copy lv) store (.val value) := by
  intro _hwellFormed hsafe htyping
  exact progress_copy_lval_of_safe hsafe htyping

/-- Lemma 4.10, `R-Move` lval base case. -/
theorem progress_move_lval_of_safe {store : ProgramStore} {env : Env}
    {stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ value store',
      Step store stepLifetime (.move lv) store' (.val value) := by
  intro hsafe htyping
  have hlocation : LValLocationAbstraction store lv (.ty ty) :=
    lvalTyping_defined_location_of_safe hsafe htyping
  rcases readPreservation_of_location hlocation with
    ⟨value, runtimeSlot, hread, hslotValue, _hvalid⟩
  rcases write_defined_of_location (value := PartialValue.undef) hlocation with
    ⟨store', hwrite⟩
  rcases runtimeSlot with ⟨partialValue, runtimeLifetime⟩
  cases hslotValue
  exact ⟨value, store', Step.move (valueLifetime := runtimeLifetime) hread hwrite⟩

theorem progress_move_lval {store : ProgramStore} {env : Env}
    {current stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ value store',
      Step store stepLifetime (.move lv) store' (.val value) := by
  intro _hwellFormed hsafe htyping
  exact progress_move_lval_of_safe hsafe htyping

/-- Lemma 4.10, `R-Borrow` lval base case. -/
theorem progress_borrow_lval_of_safe {store : ProgramStore} {env : Env}
    {stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {mutable : Bool} :
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ location,
      Step store stepLifetime (.borrow mutable lv) store
        (.val (.ref { location := location, owner := false })) := by
  intro hsafe htyping
  rcases lvalTyping_defined_location_of_safe hsafe htyping with
    ⟨location, slot, hloc, _hslot, _hvalid⟩
  exact ⟨location, Step.borrow hloc⟩

theorem progress_borrow_lval {store : ProgramStore} {env : Env}
    {current stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {mutable : Bool} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ location,
      Step store stepLifetime (.borrow mutable lv) store
        (.val (.ref { location := location, owner := false })) := by
  intro _hwellFormed hsafe htyping
  exact progress_borrow_lval_of_safe (mutable := mutable) hsafe htyping

/-- Lemma 4.10, `box E` evaluation-context case. -/
theorem progress_subBox {store : ProgramStore} {lifetime : Lifetime}
    {term : Term} :
    (∃ store' term', Step store lifetime term store' term') →
    ProgressResult store lifetime (.box term) :=
  fun ⟨store', term', hstep⟩ => Or.inr ⟨store', .box term', Step.subBox hstep⟩

/-- Lemma 4.10, `let mut x = E` evaluation-context case. -/
theorem progress_subDeclare {store : ProgramStore} {lifetime : Lifetime}
    {x : Name} {term : Term} :
    (∃ store' term', Step store lifetime term store' term') →
    ProgressResult store lifetime (.letMut x term) :=
  fun ⟨store', term', hstep⟩ =>
    Or.inr ⟨store', .letMut x term', Step.subDeclare hstep⟩

/-- Lemma 4.10, `w = E` evaluation-context case. -/
theorem progress_subAssign {store : ProgramStore} {lifetime : Lifetime}
    {lhs : LVal} {rhs : Term} :
    (∃ store' rhs', Step store lifetime rhs store' rhs') →
    ProgressResult store lifetime (.assign lhs rhs) :=
  fun ⟨store', rhs', hstep⟩ =>
    Or.inr ⟨store', .assign lhs rhs', Step.subAssign hstep⟩

theorem progress_subEqLeft {store : ProgramStore} {lifetime : Lifetime}
    {lhs rhs : Term} :
    (∃ store' lhs', Step store lifetime lhs store' lhs') →
    ProgressResult store lifetime (.eq lhs rhs) :=
  fun ⟨store', lhs', hstep⟩ =>
    Or.inr ⟨store', .eq lhs' rhs, Step.subEqLeft hstep⟩

theorem progress_subEqRight {store : ProgramStore} {lifetime : Lifetime}
    {value : Value} {rhs : Term} :
    (∃ store' rhs', Step store lifetime rhs store' rhs') →
    ProgressResult store lifetime (.eq (.val value) rhs) :=
  fun ⟨store', rhs', hstep⟩ =>
    Or.inr ⟨store', .eq (.val value) rhs', Step.subEqRight hstep⟩

theorem progress_subIte {store : ProgramStore} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term} :
    (∃ store' condition', Step store lifetime condition store' condition') →
    ProgressResult store lifetime (.ite condition trueBranch falseBranch) :=
  fun ⟨store', condition', hstep⟩ =>
    Or.inr ⟨store', .ite condition' trueBranch falseBranch, Step.subIte hstep⟩

theorem progress_eq_values {store : ProgramStore} {lifetime : Lifetime}
    {lhs rhs : Value} :
    ProgressResult store lifetime (.eq (.val lhs) (.val rhs)) := by
  by_cases heq : lhs = rhs
  · subst heq
    exact Or.inr ⟨store, .val (.bool true), Step.eqTrue⟩
  · exact Or.inr ⟨store, .val (.bool false), Step.eqFalse heq⟩

theorem valid_bool_value_of_terminal_typing {store : ProgramStore}
    {typing : StoreTyping} {value : Value} :
    ValueTyping typing value .bool →
    ValidStoreTyping store (.val value) typing →
    value = .bool true ∨ value = .bool false := by
  intro htyping hvalidStoreTyping
  rcases hvalidStoreTyping value (by simp [termValues]) with
    ⟨validTy, hvalueTyping, hvalidValue⟩
  have hvalidTy : validTy = .bool := ValueTyping.deterministic hvalueTyping htyping
  subst hvalidTy
  cases hvalidValue with
  | bool =>
      rename_i b
      cases b <;> simp

theorem progress_ite_value {store : ProgramStore} {typing : StoreTyping}
    {lifetime : Lifetime} {condition : Value} {trueBranch falseBranch : Term} :
    ValueTyping typing condition .bool →
    ValidStoreTyping store (.val condition) typing →
    ProgressResult store lifetime (.ite (.val condition) trueBranch falseBranch) := by
  intro htyping hvalidStoreTyping
  rcases valid_bool_value_of_terminal_typing htyping hvalidStoreTyping with htrue | hfalse
  · subst htrue
    exact Or.inr ⟨store, trueBranch, Step.iteTrue⟩
  · subst hfalse
    exact Or.inr ⟨store, falseBranch, Step.iteFalse⟩

/-- Lemma 4.10, block-head evaluation-context case. -/
theorem progress_block_head {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {term : Term} {rest : List Term} :
    (∃ store' term', Step store blockLifetime term store' term') →
    ProgressResult store lifetime (.block blockLifetime (term :: rest)) :=
  fun ⟨store', term', hstep⟩ =>
    Or.inr ⟨store', .block blockLifetime (term' :: rest), Step.blockA hstep⟩

/-- Lemma 4.10, typed `box E` context case. -/
theorem progress_box_context_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    ProgressResult store lifetime term →
    ¬ Terminal term →
    ProgressResult store lifetime (.box term) := by
  intro _htyping hprogress hnotTerminal
  exact progress_subBox (hprogress.step_of_not_terminal hnotTerminal)

/-- Lemma 4.10, typed `let mut x = E` context case. -/
theorem progress_declare_context_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name} {term : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime (.letMut x term) ty env₂ →
    ProgressResult store lifetime term →
    ¬ Terminal term →
    ProgressResult store lifetime (.letMut x term) := by
  intro _htyping hprogress hnotTerminal
  exact progress_subDeclare (hprogress.step_of_not_terminal hnotTerminal)

/-- Lemma 4.10, typed `w = E` context case. -/
theorem progress_assign_context_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lhs : LVal} {rhs : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime (.assign lhs rhs) ty env₂ →
    ProgressResult store lifetime rhs →
    ¬ Terminal rhs →
    ProgressResult store lifetime (.assign lhs rhs) := by
  intro _htyping hprogress hnotTerminal
  exact progress_subAssign (hprogress.step_of_not_terminal hnotTerminal)

/-- Lemma 4.10, `T-Copy` base case. -/
theorem progress_copy_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {stepLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    store ∼ₛ env →
    TermTyping env typing stepLifetime (.copy lv) ty env₂ →
    ProgressResult store stepLifetime (.copy lv) := by
  intro hsafe htyping
  cases htyping with
  | copy hLv _copyTy _hreadProhibited =>
      rcases progress_copy_lval_of_safe hsafe hLv with ⟨value, hstep⟩
      exact Or.inr ⟨store, .val value, hstep⟩

/-- Lemma 4.10, `T-Move` base case. -/
theorem progress_move_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {stepLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    store ∼ₛ env →
    TermTyping env typing stepLifetime (.move lv) ty env₂ →
    ProgressResult store stepLifetime (.move lv) := by
  intro hsafe htyping
  cases htyping with
  | move hLv _hwriteProhibited _hmove =>
      rcases progress_move_lval_of_safe hsafe hLv with ⟨value, store', hstep⟩
      exact Or.inr ⟨store', .val value, hstep⟩

/-- Lemma 4.10, `T-MutBorrow`/`T-ImmBorrow` base case. -/
theorem progress_borrow_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {stepLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {mutable : Bool} :
    store ∼ₛ env →
    TermTyping env typing stepLifetime (.borrow mutable lv) ty env₂ →
    ProgressResult store stepLifetime (.borrow mutable lv) := by
  intro hsafe htyping
  cases htyping with
  | mutBorrow hLv _hmut _hwriteProhibited =>
      rcases progress_borrow_lval_of_safe (mutable := true) hsafe hLv with
        ⟨location, hstep⟩
      exact Or.inr ⟨store, .val (.ref { location := location, owner := false }), hstep⟩
  | immBorrow hLv _hreadProhibited =>
      rcases progress_borrow_lval_of_safe (mutable := false) hsafe hLv with
        ⟨location, hstep⟩
      exact Or.inr ⟨store, .val (.ref { location := location, owner := false }), hstep⟩

/--
Lemma 4.10, `R-Box` value case.

The paper obtains a fresh heap location from finiteness of stores.  Our
`ProgramStore` is an abstract partial map, so this case is stated with the
fresh address witness as an explicit premise.
-/
theorem progress_box_value_at {store : ProgramStore} {lifetime : Lifetime}
    {address : Nat} {value : Value} :
    store.fresh (.heap address) →
    ProgressResult store lifetime (.box (.val value)) := by
  intro hfresh
  exact Or.inr ⟨(store.boxAt address value).1,
    .val (.ref (store.boxAt address value).2),
    Step.box (address := address) (ref := (store.boxAt address value).2)
      hfresh rfl⟩

theorem progress_box_value {store : ProgramStore} {lifetime : Lifetime} {value : Value} :
    OperationalStoreProgress store →
    ProgressResult store lifetime (.box (.val value)) := by
  intro hstore
  rcases hstore.freshHeap with ⟨address, hfresh⟩
  exact progress_box_value_at (address := address) hfresh

/-- Lemma 4.10, `R-Assign` value case, with the required write/drop witnesses. -/
theorem progress_assign_value_at {store storeAfterWrite storeAfterDrop : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot} {value : Value} :
    store.read lhs = some oldSlot →
    store.write lhs (.value value) = some storeAfterWrite →
    Drops storeAfterWrite [oldSlot.value] storeAfterDrop →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hread hwrite hdrops
  exact Or.inr ⟨storeAfterDrop, .val .unit, Step.assign hread hwrite hdrops⟩

theorem progress_assign_value {store : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot} {value : Value} :
    OperationalStoreProgress store →
    store.read lhs = some oldSlot →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hstore hread
  rcases hstore.assignValue lhs oldSlot value hread with
    ⟨storeAfterWrite, storeAfterDrop, hwrite, hdrops⟩
  exact progress_assign_value_at hread hwrite hdrops

/-- Lemma 4.10, `T-Assign` value case. -/
theorem progress_assign_value_typing_of_safe {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lhs : LVal}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    OperationalStoreProgress store →
    TermTyping env typing lifetime (.assign lhs (.val value)) ty env₂ →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hsafe hstore htyping
  cases htyping with
  | assign hRhs hLhsPost hshape _hwf _hwriteEnv _hranked _hcoh
      _hcontained _hnotWriteProhibited =>
      cases hRhs with
      | const _hvalue =>
          rcases read_defined_of_allocated
              (lvalTyping_allocated_location_of_safe hsafe hLhsPost) with
            ⟨oldSlot, hread⟩
          exact progress_assign_value hstore hread

theorem progress_assign_value_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lhs : LVal}
    {value : Value} {ty : Ty} :
    store ∼ₛ env →
    OperationalStoreProgress store →
    TermTyping env typing lifetime (.assign lhs (.val value)) ty env₂ →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hsafe hstore htyping
  exact progress_assign_value_typing_of_safe hsafe hstore htyping

/--
Lemma 4.10, `R-Seq` value case, with the required drop witness.

For abstract stores, existence of this witness is not automatic without a
finite/drop-normalisation invariant.
-/
theorem progress_seq_value_at {store storeAfterDrop : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    Drops store [.value value] storeAfterDrop →
    ProgressResult store lifetime (.block blockLifetime (.val value :: next :: rest)) := by
  intro hdrops
  exact Or.inr ⟨storeAfterDrop, .block blockLifetime (next :: rest), Step.seq hdrops⟩

theorem progress_seq_value {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} {next : Term} {rest : List Term} :
    OperationalStoreProgress store →
    ProgressResult store lifetime (.block blockLifetime (.val value :: next :: rest)) := by
  intro hstore
  rcases hstore.dropValue value with ⟨store', hdrops⟩
  exact progress_seq_value_at (storeAfterDrop := store') hdrops

/--
Lemma 4.10, `R-BlockB` value case, with the required lifetime-drop witness.
-/
theorem progress_block_value_at {store storeAfterDrop : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} :
    DropsLifetime store blockLifetime storeAfterDrop →
    ProgressResult store lifetime (.block blockLifetime [.val value]) := by
  intro hdrops
  exact Or.inr ⟨storeAfterDrop, .val value, Step.blockB hdrops⟩

theorem progress_block_value {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {value : Value} :
    OperationalStoreProgress store →
    ProgressResult store lifetime (.block blockLifetime [.val value]) := by
  intro hstore
  rcases hstore.dropLifetime blockLifetime with ⟨store', hdrops⟩
  exact progress_block_value_at (storeAfterDrop := store') hdrops

/-- Lemma 4.10, `T-Declare` value case. -/
theorem progress_declare_value_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name}
    {value : Value} {ty : Ty} :
    TermTyping env typing lifetime (.letMut x (.val value)) ty env₂ →
    ProgressResult store lifetime (.letMut x (.val value)) := by
  intro htyping
  cases htyping with
  | declare _hfresh _hinit _hfreshOut _hcoh _henv =>
      exact Or.inr ⟨store.declare x lifetime value, .val .unit, Step.declare rfl⟩

/-- Lemma 4.10, composed `T-Box` progress case. -/
theorem progress_box_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    ProgressResult store lifetime term →
    ProgressResult store lifetime (.box term) := by
  intro hstore _htyping hprogress
  exact hprogress.elim_value
    (fun value hterm => by subst hterm; exact progress_box_value hstore)
    progress_subBox

/-- Lemma 4.10, composed `T-Declare` progress case. -/
theorem progress_declare_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name} {term : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime (.letMut x term) ty env₂ →
    ProgressResult store lifetime term →
    ProgressResult store lifetime (.letMut x term) := by
  intro htyping hprogress
  exact hprogress.elim_value
    (fun value hterm => by
      subst hterm; exact progress_declare_value_typing htyping)
    progress_subDeclare

/-- Lemma 4.10, composed `T-Assign` progress case. -/
theorem progress_assign_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lhs : LVal}
    {rhs : Term} {ty : Ty} :
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime (.assign lhs rhs) ty env₂ →
    ProgressResult store lifetime rhs →
    ProgressResult store lifetime (.assign lhs rhs) := by
  intro hsafe hstore htyping hprogress
  exact hprogress.elim_value
    (fun value hrhs => by
      subst hrhs
      exact progress_assign_value_typing hsafe hstore htyping)
    progress_subAssign

/-- Lemma 4.10, composed block-head progress case. -/
theorem progress_block_of_head_progress {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {term : Term} {rest : List Term} :
    OperationalStoreProgress store →
    ProgressResult store blockLifetime term →
    ProgressResult store lifetime (.block blockLifetime (term :: rest)) := by
  intro hstore hprogress
  exact hprogress.elim_value
    (fun value hterm => by
      subst hterm
      cases rest with
      | nil => exact progress_block_value hstore
      | cons next rest => exact progress_seq_value hstore)
    progress_block_head

/-- Well-formedness is downward monotone along the lifetime order: only the
slot-outliving component mentions the lifetime, and outliving an outer
lifetime implies outliving anything inside it. -/
theorem WellFormedEnv.of_outlives {env : Env} {outer inner : Lifetime} :
    WellFormedEnv env outer →
    outer ≤ inner →
    WellFormedEnv env inner := by
  intro hwf houtlives
  exact ⟨hwf.1,
    fun x slot hslot => LifetimeOutlives.trans (hwf.2.1 x slot hslot) houtlives,
    hwf.2.2.1, hwf.2.2.2⟩

/--
Lemma 4.10, Progress.

Progress only uses the lifetime-outliving component of well-formedness.  Blocks
step their body under the block lifetime, where slot outliving follows from the
enclosing lifetime by downward monotonicity (`EnvSlotsOutlive.weaken`).
-/
theorem progress_typing_bounded {store : ProgramStore} (fuel : Nat)
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    term.size ≤ fuel →
    ValidStoreTyping store term typing →
    EnvSlotsOutlive env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  induction fuel generalizing env₁ env₂ typing lifetime term ty with
  | zero =>
      intro hsize _hvalidStoreTyping _hslotsOutlive _hsafe _hstore _htyping
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
  intro hsize hvalidStoreTyping hslotsOutlive hsafe hstore htyping
  revert hsize hvalidStoreTyping hslotsOutlive hsafe hstore
  refine TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      term.size ≤ fuel.succ →
      ValidStoreTyping store term typing →
      EnvSlotsOutlive env lifetime →
      store ∼ₛ env →
      OperationalStoreProgress store →
      ProgressResult store lifetime term)
    (motive_2 := fun env typing blockLifetime terms ty env₂ _ =>
      Term.size (.block blockLifetime terms) ≤ fuel.succ →
      ValidStoreTyping store (.block blockLifetime terms) typing →
      ∀ lifetime,
        EnvSlotsOutlive env blockLifetime →
        store ∼ₛ env →
        OperationalStoreProgress store →
        ProgressResult store lifetime (.block blockLifetime terms))
    ?const ?missing ?copy ?move ?mutBorrow ?immBorrow ?box ?block ?declare ?assign ?eq ?ite
    ?iteDiverging ?iteTrueDiverging ?singleton ?cons htyping
  case const =>
    intro _env _typing lifetime value _ty _hvalue _hsize _hvst _hwf _hsafe _hstore
    exact progress_value store lifetime value
  case missing =>
    intro _env _typing lifetime _ty _hwellTy _hloanFree _hsize _hvst _hwf _hsafe _hstore
    exact Or.inr ⟨store, .missing, Step.missing⟩
  case copy =>
    intro _env _typing lifetime _valueLifetime _lv _ty hLv hcopy hreadProhibited
      _hsize _hvst hwf hsafe _hstore
    exact progress_copy_typing (typing := _typing) hsafe
      (TermTyping.copy (typing := _typing) hLv hcopy hreadProhibited)
  case move =>
    intro _env₁ _env₂ _typing lifetime _valueLifetime _lv _ty hLv hwriteProhibited hmove
      _hsize _hvst hwf hsafe _hstore
    exact progress_move_typing (typing := _typing) hsafe
      (TermTyping.move (typing := _typing) hLv hwriteProhibited hmove)
  case mutBorrow =>
    intro _env _typing lifetime _valueLifetime _lv _ty hLv hmutable hwriteProhibited
      _hsize _hvst hwf hsafe _hstore
    exact progress_borrow_typing (typing := _typing) hsafe
      (TermTyping.mutBorrow (typing := _typing) hLv hmutable hwriteProhibited)
  case immBorrow =>
    intro _env _typing lifetime _valueLifetime _lv _ty hLv hreadProhibited
      _hsize _hvst hwf hsafe _hstore
    exact progress_borrow_typing (typing := _typing) hsafe
      (TermTyping.immBorrow (typing := _typing) hLv hreadProhibited)
  case box =>
    intro _env₁ _env₂ _typing _lifetime _term _ty hterm ih hsize hvst hwf hsafe hstore
    exact progress_box_typing hstore (TermTyping.box hterm)
      (ih (by simp [Term.size] at hsize ⊢; omega)
        (validStoreTyping_box_inner hvst) hwf hsafe hstore)
  case block =>
    intro _env₁ _env₂ _env₃ _typing lifetime _blockLifetime _terms _ty hchild _hterms
      _hwellTy _hdrop ih hsize hvst houtlives hsafe hstore
    exact ih hsize hvst lifetime
      (EnvSlotsOutlive.weaken houtlives (LifetimeChild.outlives hchild)) hsafe hstore
  case declare =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty hfresh hterm hfreshOut
      hcoh henv ih hsize hvst hwf hsafe hstore
    exact progress_declare_typing (TermTyping.declare hfresh hterm hfreshOut hcoh henv)
      (ih (by simp [Term.size] at hsize ⊢; omega)
        (validStoreTyping_declare_inner hvst) hwf hsafe hstore)
  case assign =>
    intro _env₁ _env₂ _env₃ _typing lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy
      hRhs hLhsPost hshape hwfTy hwrite hnoStale hranked hcoh hcontained hnotWrite
      ih hsize hvst hwf hsafe hstore
    exact progress_assign_typing hsafe hstore
      (TermTyping.assign hRhs hLhsPost hshape hwfTy hwrite hnoStale hranked hcoh
        hcontained hnotWrite)
      (ih (by simp [Term.size] at hsize ⊢; omega)
        (validStoreTyping_assign_inner hvst) hwf hsafe hstore)
  case eq =>
    intro _env₁ _env₂ _env₃ _envGhost _ghost _typing lifetime lhs rhs lhsTy
      rhsTy hLhs hfresh htypeFresh htyFresh hstoreFresh hghostRhs hnotMention _henvEq
      _hcopyL _hcopyR _hshape ihL _ihGhost hsize hvst hwf hsafe hstore
    rcases ihL (by simp [Term.size] at hsize ⊢; omega) hvst.eq_lhs hwf hsafe hstore with
      hterminalL | hstepL
    · rcases (terminal_iff_value lhs).mp hterminalL with ⟨lhsValue, hlhs⟩
      subst hlhs
      cases hLhs with
      | const _hvalueL =>
          have hRhs :=
                    TermTyping.erase_ghost
                      (env := _env₁)
                      (ghostSlot := { ty := .ty lhsTy, lifetime := lifetime })
                      hfresh htypeFresh
                      (by
                        intro hv
                        exact htyFresh
                          (Ty.vars_subset_allVars (ty := lhsTy)
                            (by simpa [PartialTy.vars] using hv)))
                      hstoreFresh hnotMention hghostRhs
          rcases ihFuel (by simp [Term.size] at hsize ⊢; omega)
              hvst.eq_rhs hwf hsafe hstore hRhs with
            hterminalR | hstepR
          · rcases (terminal_iff_value rhs).mp hterminalR with ⟨rhsValue, hrhs⟩
            subst hrhs
            exact progress_eq_values
          · exact progress_subEqRight hstepR
    · exact progress_subEqLeft hstepL
  case ite =>
    intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing lifetime condition trueBranch
      falseBranch trueTy falseTy joinTy hcondition _htrue _hfalse _hjoin _henvJoin
      _hwellJoin _hcoherent _hlinear ihCondition
      _ihTrue _ihFalse hsize hvst hwf hsafe hstore
    rcases ihCondition (by simp [Term.size] at hsize ⊢; omega)
        hvst.ite_condition hwf hsafe hstore with
      hterminalCondition | hstepCondition
    · rcases (terminal_iff_value condition).mp hterminalCondition with
        ⟨conditionValue, hconditionValue⟩
      subst hconditionValue
      cases hcondition with
      | const hvalueTyping =>
          exact progress_ite_value hvalueTyping hvst.ite_condition
    · exact progress_subIte hstepCondition
  case iteDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing lifetime condition trueBranch
      falseBranch trueTy falseTy hcondition _htrue _hfalse _hdiverges
      ihCondition _ihTrue _ihFalse hsize hvst hwf hsafe hstore
    rcases ihCondition (by simp [Term.size] at hsize ⊢; omega)
        hvst.ite_condition hwf hsafe hstore with
      hterminalCondition | hstepCondition
    · rcases (terminal_iff_value condition).mp hterminalCondition with
        ⟨conditionValue, hconditionValue⟩
      subst hconditionValue
      cases hcondition with
      | const hvalueTyping =>
          exact progress_ite_value hvalueTyping hvst.ite_condition
    · exact progress_subIte hstepCondition
  case iteTrueDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing lifetime condition trueBranch
      falseBranch trueTy falseTy hcondition _htrue _hfalse _hdiverges
      ihCondition _ihTrue _ihFalse hsize hvst hwf hsafe hstore
    rcases ihCondition (by simp [Term.size] at hsize ⊢; omega)
        hvst.ite_condition hwf hsafe hstore with
      hterminalCondition | hstepCondition
    · rcases (terminal_iff_value condition).mp hterminalCondition with
        ⟨conditionValue, hconditionValue⟩
      subst hconditionValue
      cases hcondition with
      | const hvalueTyping =>
          exact progress_ite_value hvalueTyping hvst.ite_condition
    · exact progress_subIte hstepCondition
  case singleton =>
    intro _env₁ _env₂ _typing _blockLifetime _term _ty _hterm ih hsize hvst outerLifetime
      hwf hsafe hstore
    exact progress_block_of_head_progress hstore
      (ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        (validStoreTyping_block_singleton_inner hvst) hwf hsafe hstore)
  case cons =>
    intro _env₁ _env₂ _env₃ _typing _blockLifetime _term _rest _termTy _finalTy
      _hterm _hrest ihHead _ihRest hsize hvst outerLifetime hwf hsafe hstore
    exact progress_block_of_head_progress hstore
      (ihHead (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        (validStoreTyping_block_head hvst) hwf hsafe hstore)

theorem progress_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidStoreTyping store term typing →
    EnvSlotsOutlive env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hvalidStoreTyping hslotsOutlive hsafe hstore htyping
  exact progress_typing_bounded term.size (Nat.le_refl _)
    hvalidStoreTyping hslotsOutlive hsafe hstore htyping

/-- Lemma 4.10, Progress for a non-empty typed sequence represented as a block body. -/
theorem progress_termList_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    ValidStoreTyping store (.block blockLifetime terms) typing →
    EnvSlotsOutlive env₁ blockLifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    ProgressResult store lifetime (.block blockLifetime terms) := by
  intro hvalidStoreTyping hslotsOutlive hsafe hstore htyping
  cases htyping with
  | singleton hterm =>
      exact progress_block_of_head_progress hstore
        (progress_typing (validStoreTyping_block_singleton_inner hvalidStoreTyping)
          hslotsOutlive hsafe hstore hterm)
  | cons hterm _hrest =>
      exact progress_block_of_head_progress hstore
        (progress_typing (validStoreTyping_block_head hvalidStoreTyping)
          hslotsOutlive hsafe hstore hterm)

/--
Lemma 4.10, paper-facing Progress statement.

`ValidState` and `ValidStoreTyping` are retained as premises to match the paper.
The current proof uses the safe-abstraction, well-formed-environment, and
operational-store-progress hypotheses directly.
-/
theorem progress {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro _hvalidState hvalidStoreTyping hwellFormed hsafe hstore htyping
  exact progress_typing hvalidStoreTyping hwellFormed.2.1 hsafe hstore htyping

/-- Lemma 4.10, Progress for the mechanised runtime-validity package. -/
theorem progress_runtime {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstore htyping
  exact progress hvalidRuntime.1 hvalidStoreTyping hwellFormed hsafe hstore htyping

/-- Lemma 4.10, Progress for a certified operational store. -/
theorem OperationalProgramStore.progressResult {store : OperationalProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidState (store : ProgramStore) term →
    ValidStoreTyping (store : ProgramStore) term typing →
    WellFormedEnv env₁ lifetime →
    (store : ProgramStore) ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult (store : ProgramStore) lifetime term := by
  intro hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact Paper.progress hvalidState hvalidStoreTyping hwellFormed hsafe store.progress htyping

/--
Lemma 4.10, Progress for the mechanised runtime-validity package over a
certified operational store.
-/
theorem OperationalProgramStore.progress_runtime {store : OperationalProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState (store : ProgramStore) term →
    ValidStoreTyping (store : ProgramStore) term typing →
    WellFormedEnv env₁ lifetime →
    (store : ProgramStore) ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult (store : ProgramStore) lifetime term := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe htyping
  exact Paper.progress_runtime hvalidRuntime hvalidStoreTyping hwellFormed hsafe
    store.progress htyping

/--
Lemma 4.10, non-terminal form.

This is the phrasing used when applying Progress inside the final soundness
argument: if the term is not already a value, one reduction step exists.
-/
theorem progress_step {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step store lifetime term store' term' := by
  intro hvalidState hvalidStoreTyping hwellFormed hsafe hstore htyping hnotTerminal
  exact (progress hvalidState hvalidStoreTyping hwellFormed hsafe hstore htyping).step_of_not_terminal
    hnotTerminal

/-- Lemma 4.10, non-terminal form for the mechanised runtime-validity package. -/
theorem progress_runtime_step {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step store lifetime term store' term' := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstore htyping hnotTerminal
  exact (progress_runtime hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstore htyping).step_of_not_terminal
    hnotTerminal

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Lemma 4.10, Progress. -/
theorem lemma_4_10_progress
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hvalid : ValidState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (hstore : OperationalStoreProgress store)
    (htyping : TermTyping env₁ typing lifetime term ty env₂) :
    ProgressResult store lifetime term :=
  progress hvalid hstoreTyping hwellFormed hsafe hstore htyping

end LwRust.Paper.Soundness
