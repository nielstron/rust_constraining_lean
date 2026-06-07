import LwRust.Paper.Soundness.Helpers.ValuePreservation

/-!
Soundness infrastructure for the core FR calculus.

This file starts with Section 4.1's validity definitions.  Later sections build
on these with safe abstractions, progress, preservation, and the final
type-and-borrow safety theorem.
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

theorem drops_empty_value (value : Value) :
    ∃ store', Drops ProgramStore.empty [.value value] store' := by
  cases value with
  | unit =>
      exact ⟨ProgramStore.empty,
        drops_nonOwner (by intro ref; exact Or.inl (by simp))⟩
  | int value =>
      exact ⟨ProgramStore.empty,
        drops_nonOwner (by intro ref; exact Or.inl (by simp))⟩
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
      exact ⟨ProgramStore.empty,
        drops_nonOwner (by intro ref; exact Or.inl (by simp))⟩
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

@[simp] theorem operationalStoreProgress_empty :
    OperationalStoreProgress ProgramStore.empty := by
  constructor
  · exact ⟨0, by simp [ProgramStore.fresh, ProgramStore.empty]⟩
  · exact drops_empty_value
  · exact drops_empty_partial
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

/-- Lemma 4.10, `T-Const`/value case. -/
theorem progress_value (store : ProgramStore) (lifetime : Lifetime) (value : Value) :
    ProgressResult store lifetime (.val value) := by
  exact Or.inl (value_terminal value)

/-- Lemma 4.10, `R-Copy` lval base case. -/
theorem progress_copy_lval {store : ProgramStore} {env : Env}
    {current stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ value,
      Step store stepLifetime (.copy lv) store (.val value) := by
  intro hwellFormed hsafe htyping
  rcases readPreservation hwellFormed hsafe htyping with
    ⟨value, runtimeSlot, hread, hslotValue, _hvalid⟩
  rcases runtimeSlot with ⟨partialValue, runtimeLifetime⟩
  cases hslotValue
  exact ⟨value, Step.copy (valueLifetime := runtimeLifetime) hread⟩

/-- Lemma 4.10, `R-Move` lval base case. -/
theorem progress_move_lval {store : ProgramStore} {env : Env}
    {current stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ value store',
      Step store stepLifetime (.move lv) store' (.val value) := by
  intro hwellFormed hsafe htyping
  have hlocation : LValLocationAbstraction store lv (.ty ty) :=
    lvalTyping_defined_location hwellFormed hsafe htyping
  rcases readPreservation_of_location hlocation with
    ⟨value, runtimeSlot, hread, hslotValue, _hvalid⟩
  rcases write_defined_of_location (value := PartialValue.undef) hlocation with
    ⟨store', hwrite⟩
  rcases runtimeSlot with ⟨partialValue, runtimeLifetime⟩
  cases hslotValue
  exact ⟨value, store', Step.move (valueLifetime := runtimeLifetime) hread hwrite⟩

/-- Lemma 4.10, `R-Borrow` lval base case. -/
theorem progress_borrow_lval {store : ProgramStore} {env : Env}
    {current stepLifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {mutable : Bool} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) valueLifetime →
    ∃ location,
      Step store stepLifetime (.borrow mutable lv) store
        (.val (.ref { location := location, owner := false })) := by
  intro hwellFormed hsafe htyping
  rcases lvalTyping_defined_location hwellFormed hsafe htyping with
    ⟨location, slot, hloc, _hslot, _hvalid⟩
  exact ⟨location, Step.borrow hloc⟩

/-- Lemma 4.10, `box E` evaluation-context case. -/
theorem progress_subBox {store : ProgramStore} {lifetime : Lifetime}
    {term : Term} :
    (∃ store' term', Step store lifetime term store' term') →
    ProgressResult store lifetime (.box term) := by
  intro hstep
  rcases hstep with ⟨store', term', hstep⟩
  exact Or.inr ⟨store', .box term', Step.subBox hstep⟩

/-- Lemma 4.10, `let mut x = E` evaluation-context case. -/
theorem progress_subDeclare {store : ProgramStore} {lifetime : Lifetime}
    {x : Name} {term : Term} :
    (∃ store' term', Step store lifetime term store' term') →
    ProgressResult store lifetime (.letMut x term) := by
  intro hstep
  rcases hstep with ⟨store', term', hstep⟩
  exact Or.inr ⟨store', .letMut x term', Step.subDeclare hstep⟩

/-- Lemma 4.10, `w = E` evaluation-context case. -/
theorem progress_subAssign {store : ProgramStore} {lifetime : Lifetime}
    {lhs : LVal} {rhs : Term} :
    (∃ store' rhs', Step store lifetime rhs store' rhs') →
    ProgressResult store lifetime (.assign lhs rhs) := by
  intro hstep
  rcases hstep with ⟨store', rhs', hstep⟩
  exact Or.inr ⟨store', .assign lhs rhs', Step.subAssign hstep⟩

/-- Lemma 4.10, block-head evaluation-context case. -/
theorem progress_block_head {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {term : Term} {rest : List Term} :
    (∃ store' term', Step store blockLifetime term store' term') →
    ProgressResult store lifetime (.block blockLifetime (term :: rest)) := by
  intro hstep
  rcases hstep with ⟨store', term', hstep⟩
  exact Or.inr ⟨store', .block blockLifetime (term' :: rest), Step.blockA hstep⟩

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
    {typing : StoreTyping} {current stepLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing stepLifetime (.copy lv) ty env₂ →
    ProgressResult store stepLifetime (.copy lv) := by
  intro hwellFormed hsafe htyping
  cases htyping with
  | copy hLv _copyTy _hreadProhibited =>
      rcases progress_copy_lval hwellFormed hsafe hLv with ⟨value, hstep⟩
      exact Or.inr ⟨store, .val value, hstep⟩

/-- Lemma 4.10, `T-Move` base case. -/
theorem progress_move_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current stepLifetime : Lifetime} {lv : LVal} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing stepLifetime (.move lv) ty env₂ →
    ProgressResult store stepLifetime (.move lv) := by
  intro hwellFormed hsafe htyping
  cases htyping with
  | move hLv _hwriteProhibited _hmove =>
      rcases progress_move_lval hwellFormed hsafe hLv with ⟨value, store', hstep⟩
      exact Or.inr ⟨store', .val value, hstep⟩

/-- Lemma 4.10, `T-MutBorrow`/`T-ImmBorrow` base case. -/
theorem progress_borrow_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current stepLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {mutable : Bool} :
    WellFormedEnv env current →
    store ∼ₛ env →
    TermTyping env typing stepLifetime (.borrow mutable lv) ty env₂ →
    ProgressResult store stepLifetime (.borrow mutable lv) := by
  intro hwellFormed hsafe htyping
  cases htyping with
  | mutBorrow hLv _hmut _hwriteProhibited =>
      rcases progress_borrow_lval (mutable := true) hwellFormed hsafe hLv with
        ⟨location, hstep⟩
      exact Or.inr ⟨store, .val (.ref { location := location, owner := false }), hstep⟩
  | immBorrow hLv _hreadProhibited =>
      rcases progress_borrow_lval (mutable := false) hwellFormed hsafe hLv with
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

/-- Lemma 4.10, `R-Assign` value case, with the required drop/write witnesses. -/
theorem progress_assign_value_at {store storeAfterDrop storeAfterWrite : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot} {value : Value} :
    store.read lhs = some oldSlot →
    Drops store [oldSlot.value] storeAfterDrop →
    storeAfterDrop.write lhs (.value value) = some storeAfterWrite →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hread hdrops hwrite
  exact Or.inr ⟨storeAfterWrite, .val .unit, Step.assign hread hdrops hwrite⟩

theorem progress_assign_value {store : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {oldSlot : StoreSlot} {value : Value} :
    PartialValueNonOwner oldSlot.value →
    store.read lhs = some oldSlot →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hnonOwner hread
  let hdrops : Drops store [oldSlot.value] store := drops_nonOwner hnonOwner
  rcases write_defined_of_allocated (store := store) (lv := lhs)
      (value := PartialValue.value value) (allocated_of_read hread) with
    ⟨storeAfterWrite, hwrite⟩
  exact progress_assign_value_at hread hdrops hwrite

/-- Lemma 4.10, `T-Assign` value case. -/
theorem progress_assign_value_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lhs : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    OperationalStoreProgress store →
    TermTyping env typing lifetime (.assign lhs (.val value)) ty env₂ →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hwellFormed hsafe _hstore htyping
  cases htyping with
  | assign hLhs hRhs hshape _hwf _hwriteEnv _hranked _hcoh _hnotWriteProhibited =>
      rcases read_defined_of_allocated
          (lvalTyping_allocated_location hwellFormed hsafe hLhs) with
        ⟨oldSlot, hread⟩
      cases hRhs with
      | const _hvalue =>
          have hnonOwner :
              PartialValueNonOwner oldSlot.value :=
            lvalTyping_read_nonOwner_of_shapeCompatible
              hwellFormed hsafe hLhs hshape hread
          exact progress_assign_value hnonOwner hread

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
  rcases hprogress with hterminal | hstep
  · rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
    subst hterm
    exact progress_box_value hstore
  · exact progress_subBox hstep

/-- Lemma 4.10, composed `T-Declare` progress case. -/
theorem progress_declare_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name} {term : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime (.letMut x term) ty env₂ →
    ProgressResult store lifetime term →
    ProgressResult store lifetime (.letMut x term) := by
  intro htyping hprogress
  rcases hprogress with hterminal | hstep
  · rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
    subst hterm
    exact progress_declare_value_typing htyping
  · exact progress_subDeclare hstep

/-- Lemma 4.10, composed `T-Assign` progress case. -/
theorem progress_assign_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lhs : LVal}
    {rhs : Term} {ty : Ty} :
    WellFormedEnv env₁ current →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime (.assign lhs rhs) ty env₂ →
    ProgressResult store lifetime rhs →
    ProgressResult store lifetime (.assign lhs rhs) := by
  intro hwellFormed hsafe hstore htyping hprogress
  rcases hprogress with hterminal | hstep
  · rcases (terminal_iff_value rhs).mp hterminal with ⟨value, hrhs⟩
    subst hrhs
    exact progress_assign_value_typing hwellFormed hsafe hstore htyping
  · exact progress_subAssign hstep

/-- Lemma 4.10, composed block-head progress case. -/
theorem progress_block_of_head_progress {store : ProgramStore}
    {lifetime blockLifetime : Lifetime} {term : Term} {rest : List Term} :
    OperationalStoreProgress store →
    ProgressResult store blockLifetime term →
    ProgressResult store lifetime (.block blockLifetime (term :: rest)) := by
  intro hstore hprogress
  rcases hprogress with hterminal | hstep
  · rcases (terminal_iff_value term).mp hterminal with ⟨value, hterm⟩
    subst hterm
    cases rest with
    | nil =>
        exact progress_block_value hstore
    | cons next rest =>
        exact progress_seq_value hstore
  · exact progress_block_head hstep

/--
Lemma 4.10, Progress.

The paper states well-formedness for the current lifetime.  Because blocks step
their body under the block lifetime while the block itself steps under the
enclosing lifetime, this mechanised statement takes the well-formedness premise
for every lifetime needed by nested blocks.
-/
theorem progress_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hwellFormed hsafe hstore htyping
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      (∀ lifetime, WellFormedEnv env lifetime) →
      store ∼ₛ env →
      OperationalStoreProgress store →
      ProgressResult store lifetime term)
    (motive_2 := fun env typing blockLifetime terms ty env₂ _ =>
      ∀ lifetime,
        (∀ lifetime, WellFormedEnv env lifetime) →
        store ∼ₛ env →
        OperationalStoreProgress store →
        ProgressResult store lifetime (.block blockLifetime terms))
    (fun {_env _typing lifetime value _ty} _hvalue hwellFormed hsafe hstore =>
      progress_value store lifetime value)
    (fun {_env _typing lifetime _valueLifetime _lv _ty} hLv hcopy hreadProhibited
        hwellFormed hsafe _hstore =>
      progress_copy_typing (typing := _typing) (hwellFormed lifetime) hsafe
        (TermTyping.copy (typing := _typing) hLv hcopy hreadProhibited))
    (fun {_env₁ _env₂ _typing lifetime _valueLifetime _lv _ty} hLv hwriteProhibited hmove
        hwellFormed hsafe _hstore =>
      progress_move_typing (typing := _typing) (hwellFormed lifetime) hsafe
        (TermTyping.move (typing := _typing) hLv hwriteProhibited hmove))
    (fun {_env _typing lifetime _valueLifetime _lv _ty} hLv hmutable hwriteProhibited
        hwellFormed hsafe _hstore =>
      progress_borrow_typing (typing := _typing) (hwellFormed lifetime) hsafe
        (TermTyping.mutBorrow (typing := _typing) hLv hmutable hwriteProhibited))
    (fun {_env _typing lifetime _valueLifetime _lv _ty} hLv hreadProhibited
        hwellFormed hsafe _hstore =>
      progress_borrow_typing (typing := _typing) (hwellFormed lifetime) hsafe
        (TermTyping.immBorrow (typing := _typing) hLv hreadProhibited))
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih
        hwellFormed hsafe hstore =>
      progress_box_typing hstore (TermTyping.box hterm)
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _env₃ _typing lifetime _blockLifetime _terms _ty}
        _hblockChild _hterms _hwellTy _hdrop ih hwellFormed hsafe hstore =>
      ih lifetime hwellFormed hsafe hstore)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfresh hterm hfreshOut hcoh henv ih
        hwellFormed hsafe hstore =>
      progress_declare_typing (TermTyping.declare hfresh hterm hfreshOut hcoh henv)
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _env₃ _typing lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwf hwrite hranked hcoh hnotWriteProhibited ih hwellFormed
        hsafe hstore =>
      progress_assign_typing (hwellFormed lifetime) hsafe hstore
        (TermTyping.assign hLhs hRhs hshape hwf hwrite hranked hcoh hnotWriteProhibited)
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _typing _blockLifetime _term _ty} _hterm ih
        outerLifetime hwellFormed hsafe hstore =>
      progress_block_of_head_progress hstore
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _env₃ _typing _blockLifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead _ihRest outerLifetime hwellFormed hsafe hstore =>
      progress_block_of_head_progress hstore
        (ihHead hwellFormed hsafe hstore))
    htyping hwellFormed hsafe hstore

/-- Lemma 4.10, Progress for a non-empty typed sequence represented as a block body. -/
theorem progress_termList_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    ProgressResult store lifetime (.block blockLifetime terms) := by
  intro hwellFormed hsafe hstore htyping
  cases htyping with
  | singleton hterm =>
      exact progress_block_of_head_progress hstore
        (progress_typing hwellFormed hsafe hstore hterm)
  | cons hterm _hrest =>
      exact progress_block_of_head_progress hstore
        (progress_typing hwellFormed hsafe hstore hterm)

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
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro _hvalidState _hvalidStoreTyping hwellFormed hsafe hstore htyping
  exact progress_typing hwellFormed hsafe hstore htyping

/-- Lemma 4.10, Progress for the mechanised runtime-validity package. -/
theorem progress_runtime {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
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
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
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
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
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
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
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
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step store lifetime term store' term' := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstore htyping hnotTerminal
  exact (progress_runtime hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstore htyping).step_of_not_terminal
    hnotTerminal

/-- Lemma 4.10, `R-Copy` variable-lval base case. -/
theorem progress_copy_var {store : ProgramStore} {env : Env}
    {lifetime : Lifetime} {x : Name} {slot : EnvSlot} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    ∃ value,
      Step store lifetime (.copy (.var x)) store (.val value) := by
  intro hsafe henv hty
  rcases readPreservation_var (store := store) (env := env)
      (x := x) (slot := slot) (ty := ty) hsafe henv hty with
    ⟨value, runtimeSlot, hread, hvalue, _hvalid⟩
  rcases runtimeSlot with ⟨partialValue, valueLifetime⟩
  cases hvalue
  exact ⟨value, Step.copy (valueLifetime := valueLifetime) hread⟩

/-- Lemma 4.10, `R-Move` variable-lval base case. -/
theorem progress_move_var {store : ProgramStore} {env : Env}
    {lifetime : Lifetime} {x : Name} {slot : EnvSlot} {ty : Ty} :
    store ∼ₛ env →
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    ∃ value store',
      Step store lifetime (.move (.var x)) store' (.val value) := by
  intro hsafe henv hty
  have hlocation :
      LValLocationAbstraction store (.var x) (.ty ty) := by
    simpa [hty] using location_var (store := store) (env := env) hsafe henv
  rcases readPreservation_of_location hlocation with
    ⟨value, runtimeSlot, hread, hvalue, _hvalid⟩
  rcases write_defined_of_location (value := PartialValue.undef) hlocation with
    ⟨store', hwrite⟩
  rcases runtimeSlot with ⟨partialValue, valueLifetime⟩
  cases hvalue
  exact ⟨value, store', Step.move (valueLifetime := valueLifetime) hread hwrite⟩

/-- Lemma 4.10, `R-Borrow` variable-lval base case. -/
theorem progress_borrow_var (store : ProgramStore) (lifetime : Lifetime)
    (mutable : Bool) (x : Name) :
    Step store lifetime (.borrow mutable (.var x)) store
      (.val (.ref { location := .var x, owner := false })) := by
  exact Step.borrow (by simp [ProgramStore.loc])

/-! ## Section 4.5: Type and Borrow Safety -/

/-- A term terminates when it multisteps to a runtime value. -/
def TerminatesAsValue (store : ProgramStore) (lifetime : Lifetime) (term : Term) : Prop :=
  ∃ finalStore finalValue,
    MultiStep store lifetime term finalStore (.val finalValue)

/--
The terminal safety conclusion of Lemma 4.11 / Theorem 4.12: the terminal state
is valid, the final store safely abstracts the output environment, and the
terminal value abstracts the result type.
-/
def TerminalStateSafe (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) :
    Prop :=
  ValidRuntimeState store (.val value) ∧ store ∼ₛ env ∧ ValidValue store value ty

theorem terminalStateSafe_assign_unit_of_postconditions {store : ProgramStore}
    {env : Env} :
    ValidRuntimeState store (.val .unit) →
    store ∼ₛ env →
    TerminalStateSafe store .unit env .unit := by
  intro hvalidRuntime hsafe
  exact ⟨hvalidRuntime, hsafe, ValidPartialValue.unit⟩

/--
Theorem 4.12 bridge, Type and Borrow Safety.

The paper's core calculus is terminating, while this mechanisation keeps the
operational semantics relational.  Therefore the theorem is stated with an
explicit termination witness and the Lemma 4.11 preservation conclusion as a
premise.  Progress rules out an initially stuck well-typed state; preservation
turns the terminal multistep into the safe terminal state promised by the paper.
-/
theorem typeAndBorrowSafety_of_preservation
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    (∀ finalStore finalValue,
      MultiStep store lifetime term finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₂ ty) →
    TerminatesAsValue store lifetime term →
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress htyping
    hpreservation hterminates
  rcases hterminates with ⟨finalStore, finalValue, hmulti⟩
  exact ⟨progress_runtime hvalidRuntime hvalidStoreTyping hwellFormed hsafe
      hstoreProgress htyping,
    ⟨finalStore, finalValue, hmulti, hpreservation finalStore finalValue hmulti⟩⟩

/-! ## Section 4.5.1: Borrow Safety -/

/--
Definition 4.13, borrow-safe environment.

The paper phrases this over variables in `dom(Γ)` and borrowed lvals inside
contained borrow types.  The containment premises already imply the relevant
variables are present in the environment.
-/
def BorrowSafeEnv (env : Env) : Prop :=
  ∀ x y mutable targetsMutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ (&mut targetsMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    x = y

def TyBorrowFree (ty : Ty) : Prop :=
  ∀ mutable targets, ¬ PartialTyContains (.ty ty) (.borrow mutable targets)

def PartialTyBorrowFree (ty : PartialTy) : Prop :=
  ∀ mutable targets, ¬ PartialTyContains ty (.borrow mutable targets)

theorem partialTyContains_borrow_iff_eq {mutable : Bool} {targets : List LVal}
    {needle : Ty} :
    PartialTyContains (.ty (.borrow mutable targets)) needle ↔
      Ty.borrow mutable targets = needle := by
  constructor
  · intro hcontains
    cases hcontains with
    | here => rfl
  · intro hty
    subst hty
    exact PartialTyContains.here

theorem partialTyBorrowFree_ty {ty : Ty} :
    TyBorrowFree ty →
    PartialTyBorrowFree (.ty ty) := by
  intro hfree mutable targets hcontains
  exact hfree mutable targets hcontains

@[simp] theorem partialTyBorrowFree_undef (ty : Ty) :
    PartialTyBorrowFree (.undef ty) := by
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem partialTyBorrowFree_box {ty : PartialTy} :
    PartialTyBorrowFree ty →
    PartialTyBorrowFree (.box ty) := by
  intro hfree mutable targets hcontains
  cases hcontains with
  | box hinner =>
      exact hfree mutable targets hinner

@[simp] theorem tyBorrowFree_unit :
    TyBorrowFree .unit := by
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_int :
    TyBorrowFree .int := by
  intro mutable targets hcontains
  cases hcontains

@[simp] theorem tyBorrowFree_box {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowFree (.box ty) := by
  intro hfree mutable targets hcontains
  cases hcontains with
  | tyBox hinner =>
      exact hfree mutable targets hinner

theorem partialTyBorrowFree_box_inv {ty : PartialTy} :
    PartialTyBorrowFree (.box ty) →
    PartialTyBorrowFree ty := by
  intro hfree mutable targets hcontains
  exact hfree mutable targets (PartialTyContains.box hcontains)

/-- A borrow-free fresh slot cannot be the root of a borrow-typed lval.

This discharges the fresh-root half of `FreshUpdateCoherenceObligations` for
borrow-free declarations/results.  The old-root transport half is separate:
borrow typings rooted in existing variables may dereference old borrow targets,
and transporting those target-list typings back to the old environment is the
real remaining obligation.
-/
theorem LValTyping.update_fresh_root_partialTyBorrowFree {env : Env} {x : Name}
    {ty : Ty} {slotLifetime : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {valueLifetime : Lifetime} :
    TyBorrowFree ty →
    LVal.base lv = x →
    LValTyping (env.update x { ty := .ty ty, lifetime := slotLifetime })
      lv partialTy valueLifetime →
    PartialTyBorrowFree partialTy := by
  intro hfree hbase htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _valueLifetime _ =>
      LVal.base lv = x → PartialTyBorrowFree partialTy)
    (motive_2 := fun _targets _partialTy _valueLifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping hbase
  · intro y envSlot hslot hbase
    have hy : y = x := by simpa [LVal.base] using hbase
    subst hy
    have hslotEq :
        envSlot = { ty := PartialTy.ty ty, lifetime := slotLifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := slotLifetime } = envSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    exact partialTyBorrowFree_ty hfree
  · intro lv inner lifetime _hsource ih hbase
    exact partialTyBorrowFree_box_inv (ih (by simpa [LVal.base] using hbase))
  · intro lv mutable targets borrowLifetime targetLifetime targetTy _hborrow _htargets
      ihBorrow _ihTargets hbase
    have hsourceFree :
        PartialTyBorrowFree (.ty (.borrow mutable targets)) :=
      ihBorrow (by simpa [LVal.base] using hbase)
    exact False.elim (hsourceFree mutable targets PartialTyContains.here)
  · intro target ty lifetime _htarget _ih
    trivial
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

theorem LValTyping.update_fresh_root_not_borrow_of_tyBorrowFree {env : Env}
    {x : Name} {ty : Ty} {slotLifetime : Lifetime} {lv : LVal}
    {mutable : Bool} {targets : List LVal} {borrowLifetime : Lifetime} :
    TyBorrowFree ty →
    LVal.base lv = x →
    ¬ LValTyping (env.update x { ty := .ty ty, lifetime := slotLifetime })
      lv (.ty (.borrow mutable targets)) borrowLifetime := by
  intro hfree hbase htyping
  have hpartialFree :=
    LValTyping.update_fresh_root_partialTyBorrowFree hfree hbase htyping
  exact hpartialFree mutable targets PartialTyContains.here

/-- Borrow-free fresh-update coherence, with only old-root transport left open.

For fresh-root lvals the declared type contains no borrows, so a borrow-typed
lval rooted at the fresh variable is impossible.  Callers still have to supply
the old-root transport fact, which is the nontrivial part for lvals rooted in the
pre-existing environment.
-/
theorem FreshUpdateCoherenceObligations.of_tyBorrowFree
    {env : Env} {x : Name} {ty : Ty} {lifetime : Lifetime} :
    TyBorrowFree ty →
    (∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LVal.base lv ≠ x →
      LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
        lv (.ty (.borrow mutable targets)) borrowLifetime →
      ∃ oldBorrowLifetime,
        LValTyping env lv (.ty (.borrow mutable targets)) oldBorrowLifetime) →
    FreshUpdateCoherenceObligations env x ty lifetime := by
  intro hfree holdTransport
  refine ⟨?_, ?_⟩
  · intro lv mutable targets borrowLifetime hbase htyping
    exact holdTransport hbase htyping
  · intro lv mutable targets borrowLifetime hbase htyping
    exact False.elim
      (LValTyping.update_fresh_root_not_borrow_of_tyBorrowFree hfree hbase htyping)

theorem not_tyBorrowFree_borrow (mutable : Bool) (targets : List LVal) :
    ¬ TyBorrowFree (.borrow mutable targets) := by
  intro hfree
  exact hfree mutable targets PartialTyContains.here

@[simp] theorem borrowSafeEnv_empty :
    BorrowSafeEnv Env.empty := by
  intro x y mutable targetsMutable targetsOther targetMutable targetOther hcontains _ _ _ _
  rcases hcontains with ⟨slot, hslot, _hcontainsTy⟩
  simp [Env.empty] at hslot

theorem EnvContains.update_fresh_ne {env : Env} {x y : Name} {slot : EnvSlot}
    {ty : Ty} :
    y ≠ x →
    (env.update x slot) ⊢ y ↝ ty →
    env ⊢ y ↝ ty := by
  intro hy hcontains
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  exact ⟨containedSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩

theorem EnvContains.update_same {env : Env} {x : Name} {slot : EnvSlot}
    {ty : Ty} :
    PartialTyContains slot.ty ty →
    (env.update x slot) ⊢ x ↝ ty := by
  intro hcontains
  exact ⟨slot, by simp [Env.update], hcontains⟩

theorem EnvContains.update_fresh_of_old {env : Env} {x y : Name} {slot : EnvSlot}
    {ty : Ty} :
    env.fresh x →
    env ⊢ y ↝ ty →
    (env.update x slot) ⊢ y ↝ ty := by
  intro hfresh hcontains
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  by_cases hy : y = x
  · subst hy
    rw [hfresh] at hslot
    cases hslot
  · exact ⟨containedSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩

theorem EnvContains.update_box_borrow_to_inner {env : Env} {gamma x : Name}
    {ty : Ty} {lifetime : Lifetime} {mutable : Bool} {targets : List LVal} :
    (env.update gamma { ty := .ty (.box ty), lifetime := lifetime }) ⊢ x ↝
      (Ty.borrow mutable targets) →
    (env.update gamma { ty := .ty ty, lifetime := lifetime }) ⊢ x ↝
      (Ty.borrow mutable targets) := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hx : x = gamma
  · subst hx
    have hslotEq :
        slot = { ty := PartialTy.ty (.box ty), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (.box ty), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    cases hcontainsTy with
    | tyBox hinner =>
        exact ⟨{ ty := PartialTy.ty ty, lifetime := lifetime },
          by simp [Env.update], hinner⟩
  · exact ⟨slot, by simpa [Env.update, hx] using hslot, hcontainsTy⟩

theorem pathConflicts_symm {left right : LVal} :
    left ⋈ right →
    right ⋈ left := by
  intro h
  exact h.symm

theorem pathConflicts_of_base_eq {target left right : LVal} :
    LVal.base left = LVal.base right →
    target ⋈ left →
    target ⋈ right := by
  intro hbase hconflict
  exact hconflict.trans hbase

theorem readProhibited_congr_base {env : Env} {left right : LVal} :
    LVal.base left = LVal.base right →
    (ReadProhibited env left ↔ ReadProhibited env right) := fun hbase => by
  constructor
  · intro hread
    rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    exact ⟨x, targets, target, hcontains, htarget,
      pathConflicts_of_base_eq hbase hconflict⟩
  · intro hread
    rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    exact ⟨x, targets, target, hcontains, htarget,
      pathConflicts_of_base_eq hbase.symm hconflict⟩

theorem writeProhibited_congr_base {env : Env} {left right : LVal} :
    LVal.base left = LVal.base right →
    (WriteProhibited env left ↔ WriteProhibited env right) := fun hbase => by
  constructor
  · intro hwrite
    cases hwrite with
    | inl hread =>
        exact Or.inl ((readProhibited_congr_base hbase).mp hread)
    | inr himm =>
        rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
        exact Or.inr ⟨x, targets, target, hcontains, htarget,
          pathConflicts_of_base_eq hbase hconflict⟩
  · intro hwrite
    cases hwrite with
    | inl hread =>
        exact Or.inl ((readProhibited_congr_base hbase).mpr hread)
    | inr himm =>
        rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
        exact Or.inr ⟨x, targets, target, hcontains, htarget,
          pathConflicts_of_base_eq hbase.symm hconflict⟩

theorem not_writeProhibited_var_base {env : Env} {lv : LVal} :
    ¬ WriteProhibited env lv →
    ¬ WriteProhibited env (.var (LVal.base lv)) := by
  intro hnot hwrite
  exact hnot ((writeProhibited_congr_base
    (env := env) (left := lv) (right := .var (LVal.base lv))
    (by simp [LVal.base])).mpr hwrite)

theorem partialTyContains_borrow_injective {partialTy : PartialTy}
    {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal} :
    PartialTyContains partialTy (.borrow mutable₁ targets₁) →
    PartialTyContains partialTy (.borrow mutable₂ targets₂) →
    mutable₁ = mutable₂ ∧ targets₁ = targets₂ := by
  revert mutable₁ mutable₂ targets₁ targets₂
  refine PartialTy.rec
    (motive_1 := fun ty =>
      ∀ {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal},
        PartialTyContains (.ty ty) (.borrow mutable₁ targets₁) →
        PartialTyContains (.ty ty) (.borrow mutable₂ targets₂) →
        mutable₁ = mutable₂ ∧ targets₁ = targets₂)
    (motive_2 := fun partialTy =>
      ∀ {mutable₁ mutable₂ : Bool} {targets₁ targets₂ : List LVal},
        PartialTyContains partialTy (.borrow mutable₁ targets₁) →
        PartialTyContains partialTy (.borrow mutable₂ targets₂) →
        mutable₁ = mutable₂ ∧ targets₁ = targets₂)
    ?unit ?int ?borrow ?boxTy ?ty ?boxPartial ?undef partialTy
  · intro mutable₁ mutable₂ targets₁ targets₂ hleft
    cases hleft
  · intro mutable₁ mutable₂ targets₁ targets₂ hleft
    cases hleft
  · intro mutable targets mutable₁ mutable₂ targets₁ targets₂ hleft hright
    cases hleft with
    | here =>
        cases hright with
        | here =>
            exact ⟨rfl, rfl⟩
  · intro inner ih mutable₁ mutable₂ targets₁ targets₂ hleft hright
    cases hleft with
    | tyBox hleftInner =>
        cases hright with
        | tyBox hrightInner =>
            exact ih hleftInner hrightInner
  · intro ty ih mutable₁ mutable₂ targets₁ targets₂ hleft hright
    exact ih hleft hright
  · intro inner ih mutable₁ mutable₂ targets₁ targets₂ hleft hright
    cases hleft with
    | box hleftInner =>
        cases hright with
        | box hrightInner =>
            exact ih hleftInner hrightInner
  · intro shape _ih mutable₁ mutable₂ targets₁ targets₂ hleft
    cases hleft

theorem partialTyContains_mut_imm_false {partialTy : PartialTy}
    {mutableTargets immTargets : List LVal} :
    PartialTyContains partialTy (.borrow true mutableTargets) →
    PartialTyContains partialTy (.borrow false immTargets) →
    False := by
  intro hmut himm
  rcases partialTyContains_borrow_injective hmut himm with ⟨hbool, _htargets⟩
  cases hbool

theorem not_envContains_update_fresh_same_of_borrowFree {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} {borrowTy : Ty} :
    TyBorrowFree ty →
    borrowTy = .borrow mutable targets →
    ¬ (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢ x ↝ borrowTy := by
  intro hborrowFree hborrowTy hcontains
  subst hborrowTy
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  have hslotEq :
      containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
    have h :
        { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
      simpa [Env.update] using hslot
    exact h.symm
  subst hslotEq
  exact hborrowFree mutable targets hcontainsTy

theorem borrowSafeEnv_update_partialBorrowFree {env : Env} {x : Name}
    {slot : EnvSlot} :
    BorrowSafeEnv env →
    PartialTyBorrowFree slot.ty →
    BorrowSafeEnv (env.update x slot) := by
  intro hsafe hborrowFree y z mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hy : y = x
  · have hcontainsMutableAtX :
        (env.update x slot) ⊢ x ↝ Ty.borrow true targetsMutable := by
      simpa [hy] using hcontainsMutable
    exact False.elim
      (by
        rcases hcontainsMutableAtX with ⟨containedSlot, hslot, hcontainsTy⟩
        have hslotEq : containedSlot = slot := by
          have h : slot = containedSlot := by
            simpa [Env.update] using hslot
          exact h.symm
        subst hslotEq
        exact hborrowFree true targetsMutable hcontainsTy)
  · by_cases hz : z = x
    · have hcontainsOtherAtX :
          (env.update x slot) ⊢ x ↝ Ty.borrow mutable targetsOther := by
        simpa [hz] using hcontainsOther
      exact False.elim
        (by
          rcases hcontainsOtherAtX with ⟨containedSlot, hslot, hcontainsTy⟩
          have hslotEq : containedSlot = slot := by
            have h : slot = containedSlot := by
              simpa [Env.update] using hslot
            exact h.symm
          subst hslotEq
          exact hborrowFree mutable targetsOther hcontainsTy)
    · exact hsafe y z mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hy hcontainsMutable)
        (EnvContains.update_fresh_ne hz hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_fresh_borrowFree {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    TyBorrowFree ty →
    BorrowSafeEnv (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hborrowFree
  exact borrowSafeEnv_update_partialBorrowFree hsafe
    (partialTyBorrowFree_ty hborrowFree)

theorem EnvContains.dropLifetime_of_contains {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    (env.dropLifetime lifetime) ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _hlifetime⟩
  exact ⟨slot, henvSlot, hcontainsTy⟩

/-- A result type is borrow-safe against an environment when installing it as a
new root would introduce no borrow-target conflict with any existing root.

This is the root-independent part of result-extension.  It avoids relying on
the existence of a globally fresh name, which is especially important for block
results: a name can be fresh after `dropLifetime` precisely because a block-local
slot with that name was removed. -/
def TyBorrowSafeAgainstEnv (env : Env) (ty : Ty) : Prop :=
  (∀ targetsMutable mutable targetsOther x targetMutable targetOther,
    PartialTyContains (.ty ty) (.borrow true targetsMutable) →
    env ⊢ x ↝ Ty.borrow mutable targetsOther →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False) ∧
  (∀ x targetsMutable mutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ Ty.borrow true targetsMutable →
    PartialTyContains (.ty ty) (.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False)

theorem tyBorrowSafeAgainstEnv_borrowFree {env : Env} {ty : Ty} :
    TyBorrowFree ty →
    TyBorrowSafeAgainstEnv env ty := by
  intro hfree
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      _hother _htargetMutable _htargetOther _hconflict
    exact hfree true targetsMutable hcontains
  · intro x targetsMutable mutable targetsOther targetMutable targetOther _hcontainsMutable
      hcontains _htargetMutable _htargetOther _hconflict
    exact hfree mutable targetsOther hcontains

theorem TyBorrowSafeAgainstEnv.dropLifetime {env : Env} {ty : Ty}
    {lifetime : Lifetime} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv (env.dropLifetime lifetime) ty := by
  intro hsafeTy
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      hother htargetMutable htargetOther hconflict
    exact hsafeTy.1 targetsMutable mutable targetsOther x targetMutable targetOther
      hcontains (EnvContains.dropLifetime_of_contains hother)
      htargetMutable htargetOther hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther hcontainsMutable
      hcontains htargetMutable htargetOther hconflict
    exact hsafeTy.2 x targetsMutable mutable targetsOther targetMutable targetOther
      (EnvContains.dropLifetime_of_contains hcontainsMutable) hcontains
      htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env ty →
    BorrowSafeEnv (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hsafeTy a b mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases ha : a = x
  · subst a
    have hcontainsMutableAtX :
        (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢
          x ↝ Ty.borrow true targetsMutable := by
      simpa using hcontainsMutable
    rcases hcontainsMutableAtX with ⟨containedSlot, hslot, hcontainsTy⟩
    have hslotEq :
        containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    by_cases hb : b = x
    · exact hb.symm
    · exact False.elim
        (hsafeTy.1 targetsMutable mutable targetsOther b targetMutable targetOther
          hcontainsTy
          (EnvContains.update_fresh_ne hb hcontainsOther)
          htargetMutable htargetOther hconflict)
  · by_cases hb : b = x
    · subst b
      have hcontainsOtherAtX :
          (env.update x { ty := .ty ty, lifetime := lifetime }) ⊢
            x ↝ Ty.borrow mutable targetsOther := by
        simpa using hcontainsOther
      rcases hcontainsOtherAtX with ⟨containedSlot, hslot, hcontainsTy⟩
      have hslotEq :
          containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      exact False.elim
        (hsafeTy.2 a targetsMutable mutable targetsOther targetMutable targetOther
          (EnvContains.update_fresh_ne ha hcontainsMutable)
          hcontainsTy htargetMutable htargetOther hconflict)
    · exact hsafe a b mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne ha hcontainsMutable)
        (EnvContains.update_fresh_ne hb hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_of_update_fresh {env : Env} {x : Name} {slot : EnvSlot} :
    env.fresh x →
    BorrowSafeEnv (env.update x slot) →
    BorrowSafeEnv env := by
  intro hfresh hsafe y z mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe y z mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.update_fresh_of_old hfresh hcontainsMutable)
    (EnvContains.update_fresh_of_old hfresh hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafeEnv_move_var {env env' : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.slotAt x = some { ty := .ty ty, lifetime := lifetime } →
    EnvMove env (.var x) env' →
    BorrowSafeEnv env' := by
  intro hsafe hslot hmove
  rcases hmove with ⟨slot, struck, hbaseSlot, hstrike, henv'⟩
  simp [LVal.base, LVal.path] at hbaseSlot hstrike henv'
  rw [hslot] at hbaseSlot
  injection hbaseSlot with hslotEq
  subst hslotEq
  cases struck with
  | ty struckTy =>
      cases hstrike
  | box struckInner =>
      cases hstrike
  | undef shape =>
      have hshape : ty = shape := hstrike
      subst hshape
      rw [henv']
      exact borrowSafeEnv_update_partialBorrowFree hsafe
        (partialTyBorrowFree_undef ty)

theorem borrowSafety_move_var {env env' : Env} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {x : Name} {ty : Ty} :
    BorrowSafeEnv env →
    env.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    TermTyping env typing lifetime (.move (.var x)) ty env' →
    BorrowSafeEnv env' := by
  intro hsafe hslot htyping
  cases htyping with
  | move _hLv _hnotWrite hmove =>
      exact borrowSafeEnv_move_var hsafe hslot hmove

theorem LValTyping.var_dropLifetime_child {env : Env} {parent child : Lifetime}
    {x : Name} {slot : EnvSlot} :
    LifetimeChild parent child →
    env.slotAt x = some slot →
    slot.lifetime ≤ parent →
    LValTyping (env.dropLifetime child) (.var x) slot.ty slot.lifetime := by
  intro hchild hslot houtlivesParent
  exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
    ⟨hslot, by
      intro hslotLifetime
      subst hslotLifetime
      exact LifetimeChild.not_child_outlives_parent hchild houtlivesParent⟩)

theorem borrowSafeEnv_dropLifetime {env : Env} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    BorrowSafeEnv (env.dropLifetime lifetime) := by
  intro hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.dropLifetime_of_contains hcontainsMutable)
    (EnvContains.dropLifetime_of_contains hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafety_block_drop {env env' : Env} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env' = env.dropLifetime lifetime →
    BorrowSafeEnv env' := by
  intro hsafe henv'
  rw [henv']
  exact borrowSafeEnv_dropLifetime hsafe

theorem Env.dropLifetime_update_ne {env : Env} {x : Name} {slot : EnvSlot}
    {dropped : Lifetime} :
    slot.lifetime ≠ dropped →
    (env.update x slot).dropLifetime dropped =
      (env.dropLifetime dropped).update x slot := by
  intro hslotLifetime
  cases env with
  | mk slotAt =>
      simp only [Env.dropLifetime, Env.update]
      congr
      funext y
      by_cases hy : y = x
      · subst hy
        simp [hslotLifetime]
      · simp [hy]

theorem borrowSafeEnv_dropLifetime_update_of_update {env : Env} {x : Name}
    {slot : EnvSlot} {dropped : Lifetime} :
    slot.lifetime ≠ dropped →
    BorrowSafeEnv (env.update x slot) →
    BorrowSafeEnv ((env.dropLifetime dropped).update x slot) := by
  intro hslotLifetime hsafe
  have hdropSafe :
      BorrowSafeEnv ((env.update x slot).dropLifetime dropped) :=
    borrowSafeEnv_dropLifetime hsafe
  rwa [Env.dropLifetime_update_ne hslotLifetime] at hdropSafe

theorem borrowSafeEnv_block_result_extension_of_body_extension {env₂ env₃ : Env}
    {lifetime blockLifetime : Lifetime} {ty : Ty} {gamma : Name} :
    LifetimeChild lifetime blockLifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) →
    BorrowSafeEnv (env₃.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hchild hdrop hbodySafe
  rw [hdrop]
  exact borrowSafeEnv_dropLifetime_update_of_update
    (x := gamma)
    (slot := { ty := .ty ty, lifetime := lifetime })
    (by
      intro hEq
      exact LifetimeChild.ne hchild hEq)
    hbodySafe

theorem borrowSafety_copy {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {lv : LVal} {ty : Ty} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    BorrowSafeEnv env₂ := by
  intro hsafe htyping
  cases htyping
  exact hsafe

theorem LValTyping.no_readProhibited_targets_of_immBorrow {env : Env} :
    BorrowSafeEnv env →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {borrowTargets},
        PartialTyContains partialTy (.borrow false borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ ReadProhibited env target) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {borrowTargets},
        PartialTyContains partialTy (.borrow false borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ ReadProhibited env target) := by
  intro hsafe
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (motive_2 := fun targets partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (by
        intro x slot hslot borrowTargets hcontains target htarget hread
        rcases hread with
          ⟨borrower, mutableTargets, mutableTarget, hmutableContains,
            hmutableTarget, hconflict⟩
        by_cases hsame : borrower = x
        · subst hsame
          rcases hmutableContains with ⟨mutableSlot, hmutableSlot, hmutableTy⟩
          rw [hslot] at hmutableSlot
          injection hmutableSlot with hslotEq
          subst hslotEq
          exact partialTyContains_mut_imm_false hmutableTy hcontains
        · have hsafeContradiction :
              borrower = x := by
            exact hsafe borrower x false mutableTargets borrowTargets
              mutableTarget target
              hmutableContains
              ⟨slot, hslot, hcontains⟩
              hmutableTarget
              htarget
              hconflict
          exact hsame hsafeContradiction)
      (by
        intro _lv _inner _lifetime _htyping ih borrowTargets hcontains target
          htarget hread
        exact ih (PartialTyContains.box hcontains) target htarget hread)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets borrowTargets hcontains target
          htarget hread
        exact ihTargets hcontains target htarget hread)
      (by
        intro target ty lifetime _htarget ihTarget borrowTargets hcontains selected
          hselected hread
        exact ihTarget hcontains selected hselected hread)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion _hintersection ihHead ihRest borrowTargets hcontains
          selected hselected hread
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead hread
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest hread)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (motive_2 := fun targets partialTy lifetime _ =>
        ∀ {borrowTargets},
          PartialTyContains partialTy (.borrow false borrowTargets) →
          ∀ target,
            target ∈ borrowTargets →
            ¬ ReadProhibited env target)
      (by
        intro x slot hslot borrowTargets hcontains target htarget hread
        rcases hread with
          ⟨borrower, mutableTargets, mutableTarget, hmutableContains,
            hmutableTarget, hconflict⟩
        by_cases hsame : borrower = x
        · subst hsame
          rcases hmutableContains with ⟨mutableSlot, hmutableSlot, hmutableTy⟩
          rw [hslot] at hmutableSlot
          injection hmutableSlot with hslotEq
          subst hslotEq
          exact partialTyContains_mut_imm_false hmutableTy hcontains
        · have hsafeContradiction :
              borrower = x := by
            exact hsafe borrower x false mutableTargets borrowTargets
              mutableTarget target
              hmutableContains
              ⟨slot, hslot, hcontains⟩
              hmutableTarget
              htarget
              hconflict
          exact hsame hsafeContradiction)
      (by
        intro _lv _inner _lifetime _htyping ih borrowTargets hcontains target
          htarget hread
        exact ih (PartialTyContains.box hcontains) target htarget hread)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets borrowTargets hcontains target
          htarget hread
        exact ihTargets hcontains target htarget hread)
      (by
        intro target ty lifetime _htarget ihTarget borrowTargets hcontains selected
          hselected hread
        exact ihTarget hcontains selected hselected hread)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion _hintersection ihHead ihRest borrowTargets hcontains
          selected hselected hread
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead hread
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest hread)
      htyping

theorem borrowSafety_borrow {env env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {lv : LVal} {mutable : Bool} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow mutable lv) (.borrow mutable [lv]) env₂ →
    BorrowSafeEnv env₂ := by
  intro hsafe htyping
  cases htyping with
  | mutBorrow =>
      exact hsafe
  | immBorrow =>
      exact hsafe

theorem borrowSafeEnv_update_fresh_mutBorrow {env : Env} {gamma : Name}
    {lv : LVal} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    ¬ WriteProhibited env lv →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) := by
  intro hsafe _hfresh hnotWrite x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq : Ty.borrow true [lv] = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    injection hborrowEq with _hmut htargetsMutable
    subst htargetsMutable
    have htargetMutableEq : targetMutable = lv := by
      simpa using htargetMutable
    have hconflictLv : lv ⋈ targetOther := by
      simpa [htargetMutableEq] using hconflict
    by_cases hy : y = gamma
    · exact hx.trans hy.symm
    · have hcontainsOtherOld : env ⊢ y ↝ Ty.borrow mutable targetsOther :=
        EnvContains.update_fresh_ne hy hcontainsOther
      have hwrite : WriteProhibited env lv := by
        cases mutable with
        | false =>
            exact Or.inr ⟨y, targetsOther, targetOther, hcontainsOtherOld,
              htargetOther, pathConflicts_symm hconflictLv⟩
        | true =>
            exact Or.inl ⟨y, targetsOther, targetOther, hcontainsOtherOld,
              htargetOther, pathConflicts_symm hconflictLv⟩
      exact False.elim (hnotWrite hwrite)
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow true [lv]), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq : Ty.borrow true [lv] = Ty.borrow mutable targetsOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargetsOther
      subst htargetsOther
      have htargetOtherEq : targetOther = lv := by
        simpa using htargetOther
      have hconflictLv : targetMutable ⋈ lv := by
        simpa [htargetOtherEq] using hconflict
      have hcontainsMutableOld : env ⊢ x ↝ Ty.borrow true targetsMutable :=
        EnvContains.update_fresh_ne hx hcontainsMutable
      have hwrite : WriteProhibited env lv :=
        Or.inl ⟨x, targetsMutable, targetMutable, hcontainsMutableOld,
          htargetMutable, hconflictLv⟩
      exact False.elim (hnotWrite hwrite)
    · exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_fresh_immBorrow {env : Env} {gamma : Name}
    {lv : LVal} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    ¬ ReadProhibited env lv →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) := by
  intro hsafe hfresh hnotRead x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq :
        Ty.borrow false [lv] = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    cases hborrowEq
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow false [lv]), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq :
          Ty.borrow false [lv] = Ty.borrow mutable targetsOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargets
      have htargetOtherEq : targetOther = lv := by
        cases htargets
        simpa using htargetOther
      subst htargetOtherEq
      exact False.elim (hnotRead ⟨x, targetsMutable, targetMutable,
        EnvContains.update_fresh_ne hx hcontainsMutable,
        htargetMutable,
        hconflict⟩)
    · exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem borrowSafeEnv_update_fresh_immBorrowMany {env : Env} {gamma : Name}
    {targets : List LVal} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    env.fresh gamma →
    (∀ target, target ∈ targets → ¬ ReadProhibited env target) →
    BorrowSafeEnv
      (env.update gamma { ty := .ty (.borrow false targets), lifetime := lifetime }) := by
  intro hsafe hfresh hnotRead x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  by_cases hx : x = gamma
  · have hcontainsMutableAtGamma :
        (env.update gamma { ty := .ty (.borrow false targets), lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa [hx] using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨slot, hslot, hcontainsTy⟩
    have hslotEq :
        slot = { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } = slot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    have hborrowEq :
        Ty.borrow false targets = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontainsTy
    cases hborrowEq
  · by_cases hy : y = gamma
    · have hcontainsOtherAtGamma :
          (env.update gamma { ty := .ty (.borrow false targets), lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa [hy] using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨slot, hslot, hcontainsTy⟩
      have hslotEq :
          slot = { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty (Ty.borrow false targets), lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have hborrowEq :
          Ty.borrow false targets = Ty.borrow mutable targetsOther :=
        partialTyContains_borrow_iff_eq.mp hcontainsTy
      injection hborrowEq with _hmutable htargets
      subst htargets
      exact False.elim
        (hnotRead targetOther htargetOther
          ⟨x, targetsMutable, targetMutable,
            EnvContains.update_fresh_ne hx hcontainsMutable,
            htargetMutable,
            hconflict⟩)
    · exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
        (EnvContains.update_fresh_ne hx hcontainsMutable)
        (EnvContains.update_fresh_ne hy hcontainsOther)
        htargetMutable htargetOther hconflict

theorem tyBorrowSafeAgainstEnv_mutBorrow {env : Env} {lv : LVal} :
    ¬ WriteProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow true [lv]) := by
  intro hnotWrite
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      hother htargetMutable htargetOther hconflict
    have hborrowEq : Ty.borrow true [lv] = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmut htargetsMutable
    subst htargetsMutable
    have htargetMutableEq : targetMutable = lv := by
      simpa using htargetMutable
    have hconflictLv : lv ⋈ targetOther := by
      simpa [htargetMutableEq] using hconflict
    have hwrite : WriteProhibited env lv := by
      cases mutable with
      | false =>
          exact Or.inr ⟨x, targetsOther, targetOther, hother,
            htargetOther, pathConflicts_symm hconflictLv⟩
      | true =>
          exact Or.inl ⟨x, targetsOther, targetOther, hother,
            htargetOther, pathConflicts_symm hconflictLv⟩
    exact hnotWrite hwrite
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable hcontains htargetMutable htargetOther hconflict
    have hborrowEq : Ty.borrow true [lv] = Ty.borrow mutable targetsOther :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmutable htargetsOther
    subst htargetsOther
    have htargetOtherEq : targetOther = lv := by
      simpa using htargetOther
    have hconflictLv : targetMutable ⋈ lv := by
      simpa [htargetOtherEq] using hconflict
    exact hnotWrite
      (Or.inl ⟨x, targetsMutable, targetMutable, hcontainsMutable,
        htargetMutable, hconflictLv⟩)

theorem tyBorrowSafeAgainstEnv_immBorrowMany {env : Env} {targets : List LVal} :
    (∀ target, target ∈ targets → ¬ ReadProhibited env target) →
    TyBorrowSafeAgainstEnv env (.borrow false targets) := by
  intro hnotRead
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      _hother _htargetMutable _htargetOther _hconflict
    have hborrowEq :
        Ty.borrow false targets = Ty.borrow true targetsMutable :=
      partialTyContains_borrow_iff_eq.mp hcontains
    cases hborrowEq
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable hcontains htargetMutable htargetOther hconflict
    have hborrowEq :
        Ty.borrow false targets = Ty.borrow mutable targetsOther :=
      partialTyContains_borrow_iff_eq.mp hcontains
    injection hborrowEq with _hmutable htargets
    subst htargets
    exact hnotRead targetOther htargetOther
      ⟨x, targetsMutable, targetMutable, hcontainsMutable,
        htargetMutable, hconflict⟩

theorem tyBorrowSafeAgainstEnv_immBorrow {env : Env} {lv : LVal} :
    ¬ ReadProhibited env lv →
    TyBorrowSafeAgainstEnv env (.borrow false [lv]) := by
  intro hnotRead
  exact tyBorrowSafeAgainstEnv_immBorrowMany
    (by
      intro target htarget
      have htargetEq : target = lv := by
        simpa using htarget
      subst htargetEq
      exact hnotRead)

theorem PartialTyContains.tyBox_borrow_inv {inner : Ty} {mutable : Bool}
    {targets : List LVal} :
    PartialTyContains (.ty (.box inner)) (.borrow mutable targets) →
    PartialTyContains (.ty inner) (.borrow mutable targets) := by
  intro hcontains
  cases hcontains with
  | tyBox hinner => exact hinner

theorem TyBorrowSafeAgainstEnv.box {env : Env} {ty : Ty} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv env (.box ty) := by
  intro hsafeTy
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontains
      hother htargetMutable htargetOther hconflict
    exact hsafeTy.1 targetsMutable mutable targetsOther x targetMutable targetOther
      (PartialTyContains.tyBox_borrow_inv hcontains) hother
      htargetMutable htargetOther hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther hcontainsMutable
      hcontains htargetMutable htargetOther hconflict
    exact hsafeTy.2 x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable (PartialTyContains.tyBox_borrow_inv hcontains)
      htargetMutable htargetOther hconflict

theorem borrowSafety_immBorrow_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow false lv) (.borrow false [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) := by
  intro hsafe htyping hfresh
  cases htyping with
  | immBorrow _hLv hnotRead =>
      exact borrowSafeEnv_update_fresh_immBorrow hsafe hfresh hnotRead

theorem borrowSafety_mutBorrow_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow true lv) (.borrow true [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) := by
  intro hsafe htyping hfresh
  cases htyping with
  | mutBorrow _hLv _hmutable hnotWrite =>
      exact borrowSafeEnv_update_fresh_mutBorrow hsafe hfresh hnotWrite

theorem borrowSafety_box_context {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    (TermTyping env₁ typing lifetime term ty env₂ → BorrowSafeEnv env₂) →
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    BorrowSafeEnv env₂ := by
  intro hinner htyping
  cases htyping with
  | box hterm =>
      exact hinner hterm

theorem borrowSafety_block_context {env₁ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    (∀ env₂, TermListTyping env₁ typing blockLifetime terms ty env₂ → BorrowSafeEnv env₂) →
    TermTyping env₁ typing lifetime (.block blockLifetime terms) ty env₃ →
    BorrowSafeEnv env₃ := by
  intro htermsSafe htyping
  cases htyping with
  | block _hblockChild hterms _hwellTy hdrop =>
      exact borrowSafety_block_drop (htermsSafe _ hterms) hdrop

/--
Borrow-free result extension with the fresh-coherence gap exposed.

The fresh-root coherence case is discharged by `TyBorrowFree`; the only
remaining well-formedness premise is old-root transport for borrow typings in
the extended environment.  This is the axiom-clean replacement shape for the
legacy `borrowSafety_result_extension_borrowFree` below.
-/
theorem borrowSafety_result_extension_borrowFree_of_oldRootTransport {env : Env}
    {gamma : Name} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env.fresh gamma →
    (∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LVal.base lv ≠ gamma →
      LValTyping (env.update gamma { ty := .ty ty, lifetime := lifetime })
        lv (.ty (.borrow mutable targets)) borrowLifetime →
      ∃ oldBorrowLifetime,
        LValTyping env lv (.ty (.borrow mutable targets)) oldBorrowLifetime) →
    WellFormedEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hwellFormed hwellTy hborrowSafe hborrowFree hfresh holdTransport
  exact ⟨
    borrowInvariance_result_extension_of_coherenceObligations
      hwellFormed hwellTy hfresh
      (FreshUpdateCoherenceObligations.of_tyBorrowFree hborrowFree holdTransport),
    borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree⟩

/--
Corollary 4.14 support: extending the output environment with a fresh,
borrow-free result slot preserves both well-formedness and borrow safety.

The remaining borrow-safety work is the paper's typing-rule induction showing
that the output environment of a well-typed term is itself borrow safe.  This
theorem packages the final result-extension step from the corollary.

This is a legacy shortcut: its well-formedness half goes through
`borrowInvariance_result_extension`, which depends on `Coherent.update_fresh_ty`.
Use `borrowSafety_result_extension_borrowFree_of_oldRootTransport` when the
old-root transport obligation is available.
-/
theorem borrowSafety_result_extension_borrowFree {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env.fresh gamma →
    FreshUpdateCoherenceObligations env gamma ty lifetime →
    WellFormedEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hwellFormed hwellTy hborrowSafe hborrowFree hfresh hfreshCoherence
  exact ⟨borrowInvariance_result_extension hwellFormed hwellTy hfresh hfreshCoherence,
    borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree⟩

theorem borrowSafety_result_extension_unit {env : Env} {gamma : Name}
    {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    env.fresh gamma →
    FreshUpdateCoherenceObligations env gamma .unit lifetime →
    WellFormedEnv (env.update gamma { ty := .ty .unit, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty .unit, lifetime := lifetime }) := by
  intro hwellFormed hborrowSafe hfresh hfreshCoherence
  exact borrowSafety_result_extension_borrowFree hwellFormed WellFormedTy.unit
    hborrowSafe tyBorrowFree_unit hfresh hfreshCoherence

theorem borrowSafeEnv_update_box_of_update_inner {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) →
    BorrowSafeEnv (env.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.update_box_borrow_to_inner hcontainsMutable)
    (EnvContains.update_box_borrow_to_inner hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafety_result_extension_box_of_inner {env : Env} {gamma : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    BorrowSafeEnv (env.update gamma { ty := .ty ty, lifetime := lifetime }) →
    env.fresh gamma →
    FreshUpdateCoherenceObligations env gamma (.box ty) lifetime →
    WellFormedEnv (env.update gamma { ty := .ty (.box ty), lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro hwellFormed hwellTy hinnerSafe hfresh hfreshCoherence
  exact ⟨borrowInvariance_result_extension hwellFormed
      (WellFormedTy.box hwellTy) hfresh hfreshCoherence,
    borrowSafeEnv_update_box_of_update_inner hinnerSafe⟩

/--
Corollary 4.14, `T-Const` case: typing a value does not change the environment,
so borrow safety of the result extension follows from the borrow-free shape of
the result type.
-/
theorem borrowSafety_value_result_extension_borrowFree {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty}
    {gamma : Name} :
    TermTyping env typing lifetime (.val value) ty env₂ →
    WellFormedEnv env lifetime →
    WellFormedTy env₂ ty lifetime →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro htyping hwellFormed hwellTy hborrowSafe hborrowFree hfresh hfreshCoherence
  have henv : env = env₂ := valueTyping_environment_eq htyping
  subst henv
  exact borrowSafety_result_extension_borrowFree hwellFormed hwellTy hborrowSafe
    hborrowFree hfresh hfreshCoherence

theorem borrowSafe_value_result_extension_borrowFree {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty}
    {gamma : Name} :
    TermTyping env typing lifetime (.val value) ty env₂ →
    BorrowSafeEnv env →
    TyBorrowFree ty →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro htyping hborrowSafe hborrowFree hfresh
  have henv : env = env₂ := valueTyping_environment_eq htyping
  subst henv
  exact borrowSafeEnv_update_fresh_borrowFree hborrowSafe hborrowFree

/-! ## Source-Level Initial States -/

def SourceValue : Value → Prop
  | .unit => True
  | .int _ => True
  | .ref _ => False

def SourceTerm (term : Term) : Prop :=
  ∀ value, value ∈ termValues term → SourceValue value

theorem SourceTerm.block_head {lifetime : Lifetime} {term : Term}
    {rest : List Term} :
    SourceTerm (.block lifetime (term :: rest)) →
    SourceTerm term := by
  intro hsource value hmem
  exact hsource value
    (by
      simp [termValues, hmem])

theorem SourceTerm.block_tail {lifetime : Lifetime} {term : Term}
    {rest : List Term} :
    SourceTerm (.block lifetime (term :: rest)) →
    SourceTerm (.block lifetime rest) := by
  intro hsource value hmem
  exact hsource value
    (by
      simp [termValues] at hmem ⊢
      exact Or.inr hmem)

theorem SourceTerm.box_inner {term : Term} :
    SourceTerm (.box term) →
    SourceTerm term := by
  intro hsource value hmem
  exact hsource value (by simpa [termValues] using hmem)

theorem SourceTerm.declare_inner {x : Name} {term : Term} :
    SourceTerm (.letMut x term) →
    SourceTerm term := by
  intro hsource value hmem
  exact hsource value (by simpa [termValues] using hmem)

theorem SourceTerm.assign_inner {lhs : LVal} {rhs : Term} :
    SourceTerm (.assign lhs rhs) →
    SourceTerm rhs := by
  intro hsource value hmem
  exact hsource value (by simpa [termValues] using hmem)

theorem sourceValue_no_owningLocations {value : Value} :
    SourceValue value →
    valueOwningLocations value = [] := by
  intro hsource
  cases value with
  | unit =>
      rfl
  | int _ =>
      rfl
  | ref ref =>
      cases hsource

theorem sourceValues_no_owningLocations {values : List Value} :
    (∀ value, value ∈ values → SourceValue value) →
    List.flatMap valueOwningLocations values = [] := by
  intro hsource
  induction values with
  | nil =>
      rfl
  | cons head tail ih =>
      have hhead : SourceValue head := hsource head (by simp)
      have htail : ∀ value, value ∈ tail → SourceValue value := by
        intro value hmem
        exact hsource value (by simp [hmem])
      calc
        List.flatMap valueOwningLocations (head :: tail)
            = valueOwningLocations head ++ List.flatMap valueOwningLocations tail := rfl
        _ = [] ++ [] := by
          rw [sourceValue_no_owningLocations hhead, ih htail]
        _ = [] := rfl

theorem sourceTerm_no_owningLocations {term : Term} :
    SourceTerm term →
    termOwningLocations term = [] := by
  intro hsource
  exact sourceValues_no_owningLocations hsource

theorem sourceTerm_validTerm {term : Term} :
    SourceTerm term →
    ValidTerm term := by
  intro hsource
  simp [ValidTerm, sourceTerm_no_owningLocations hsource]

theorem sourceValue_emptyStoreTyping {store : ProgramStore} {value : Value} :
    SourceValue value →
    ∃ ty, ValueTyping StoreTyping.empty value ty ∧ ValidValue store value ty := by
  intro hsource
  cases value with
  | unit =>
      exact ⟨.unit, ValueTyping.unit, ValidPartialValue.unit⟩
  | int value =>
      exact ⟨.int, ValueTyping.int, ValidPartialValue.int⟩
  | ref ref =>
      cases hsource

theorem sourceValue_validValue_of_empty_valueTyping {store : ProgramStore}
    {value : Value} {ty : Ty} :
    SourceValue value →
    ValueTyping StoreTyping.empty value ty →
    ValidValue store value ty := by
  intro hsource htyping
  rcases sourceValue_emptyStoreTyping (store := store) hsource with
    ⟨sourceTy, hsourceTyping, hvalidValue⟩
  have hty : sourceTy = ty :=
    valueTyping_deterministic hsourceTyping htyping
  subst hty
  exact hvalidValue

theorem sourceValue_empty_valueTyping_borrowFree {value : Value} {ty : Ty} :
    SourceValue value →
    ValueTyping StoreTyping.empty value ty →
    TyBorrowFree ty := by
  intro hsource htyping
  cases value with
  | unit =>
      cases htyping
      exact tyBorrowFree_unit
  | int _ =>
      cases htyping
      exact tyBorrowFree_int
  | ref _ =>
      cases hsource

theorem sourceValue_valueTyping_borrowFree {typing : StoreTyping} {value : Value}
    {ty : Ty} :
    SourceValue value →
    ValueTyping typing value ty →
    TyBorrowFree ty := by
  intro hsource htyping
  cases value with
  | unit =>
      cases htyping
      exact tyBorrowFree_unit
  | int _ =>
      cases htyping
      exact tyBorrowFree_int
  | ref _ =>
      cases hsource

theorem sourceTerm_empty_valueTyping_borrowFree {term : Term}
    {value : Value} {ty : Ty} :
    SourceTerm term →
    value ∈ termValues term →
    ValueTyping StoreTyping.empty value ty →
    TyBorrowFree ty := by
  intro hsource hmem htyping
  exact sourceValue_empty_valueTyping_borrowFree (hsource value hmem) htyping

theorem sourceInitial_value_borrowSafety_result_extension
    {value : Value} {ty : Ty} {env₂ : Env} {lifetime : Lifetime}
    {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource htyping hwellTy hfresh hfreshCoherence
  cases htyping with
  | const hvalueTyping =>
      exact borrowSafety_value_result_extension_borrowFree
        (TermTyping.const hvalueTyping)
        (wellFormedEnv_empty lifetime)
        hwellTy
        borrowSafeEnv_empty
        (sourceValue_empty_valueTyping_borrowFree hsource hvalueTyping)
        hfresh
        hfreshCoherence

theorem sourceInitial_box_value_borrowSafety_result_extension
    {value : Value} {ty : Ty} {env₂ : Env} {lifetime : Lifetime}
    {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma (.box ty) lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty (.box ty), lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro _hsource htyping hfresh hfreshCoherence
  cases htyping with
  | box hinner =>
      cases hinner with
      | const hvalueTyping =>
          have hinnerFree : TyBorrowFree ty :=
            sourceValue_empty_valueTyping_borrowFree _hsource hvalueTyping
          have hwellTy : WellFormedTy Env.empty ty lifetime := by
            cases hvalueTyping with
            | unit =>
                exact WellFormedTy.unit
            | int =>
                exact WellFormedTy.int
            | ref hlookup =>
                simp [StoreTyping.empty] at hlookup
          have hinnerSafe :
              BorrowSafeEnv
                (Env.empty.update gamma { ty := .ty ty, lifetime := lifetime }) :=
            borrowSafeEnv_update_fresh_borrowFree borrowSafeEnv_empty hinnerFree
          exact borrowSafety_result_extension_box_of_inner
            (wellFormedEnv_empty lifetime)
            hwellTy
            hinnerSafe
            hfresh
            hfreshCoherence

theorem sourceInitial_declare_value_borrowSafety_result_extension
    {x : Name} {value : Value} {env₃ : Env} {lifetime : Lifetime}
    {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    env₃.fresh gamma →
    FreshUpdateCoherenceObligations env₃ gamma .unit lifetime →
    WellFormedEnv (env₃.update gamma { ty := .ty .unit, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₃.update gamma { ty := .ty .unit, lifetime := lifetime }) := by
  intro hsource htyping hfreshGamma hfreshGammaCoherence
  cases htyping with
  | declare hfresh hinit _hfreshOut hcoh henv₃ =>
      cases hinit with
      | const hvalueTyping =>
          rename_i initTy
          have hwellTy : WellFormedTy Env.empty initTy lifetime := by
            cases hvalueTyping with
            | unit =>
                exact WellFormedTy.unit
            | int =>
                exact WellFormedTy.int
            | ref hlookup =>
                simp [StoreTyping.empty] at hlookup
          have hdeclared :
              WellFormedEnv
                  (Env.empty.update x { ty := .ty initTy, lifetime := lifetime })
                  lifetime ∧
            BorrowSafeEnv
                  (Env.empty.update x { ty := .ty initTy, lifetime := lifetime }) := by
            exact sourceInitial_value_borrowSafety_result_extension hsource
              (TermTyping.const hvalueTyping) hwellTy hfresh hcoh
          have hfreshGamma' :
              (Env.empty.update x { ty := .ty initTy, lifetime := lifetime }).fresh
                gamma := by
            simpa [henv₃] using hfreshGamma
          rw [henv₃]
          exact borrowSafety_result_extension_borrowFree
            hdeclared.1
            WellFormedTy.unit
            hdeclared.2
            tyBorrowFree_unit
            hfreshGamma'
            (by simpa [henv₃] using hfreshGammaCoherence)

theorem sourceInitial_blockB_value_borrowSafety_result_extension
    {value : Value} {ty : Ty} {env₂ : Env}
    {lifetime blockLifetime : Lifetime} {gamma : Name} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime
      (.block blockLifetime [.val value]) ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsource htyping hfresh hfreshCoherence
  cases htyping with
  | block _hblockChild hterms hwellTy hdrop =>
      have hvalueTyping := termListTyping_singleton_value_valueTyping hterms
      have henvList : Env.empty = _ :=
        termListTyping_singleton_value_environment_eq hterms
      subst henvList
      have hdropEmpty : env₂ = Env.empty := by
        simpa [Env.dropLifetime, Env.empty] using hdrop
      subst hdropEmpty
      exact borrowSafety_result_extension_borrowFree
        (wellFormedEnv_empty lifetime)
        hwellTy
        borrowSafeEnv_empty
        (sourceValue_empty_valueTyping_borrowFree hsource hvalueTyping)
        hfresh
        hfreshCoherence

theorem sourceTerm_validStoreTyping_empty {store : ProgramStore} {term : Term} :
    SourceTerm term →
    ValidStoreTyping store term StoreTyping.empty := by
  intro hsource value hmem
  exact sourceValue_emptyStoreTyping (hsource value hmem)

theorem sourceInitialState_valid {term : Term} :
    SourceTerm term →
    ValidState ProgramStore.empty term := by
  intro hsource
  exact ⟨validStore_empty, sourceTerm_validTerm hsource, by
    intro owned _hmem
    exact empty_owns_false owned⟩

theorem sourceInitialRuntimeState_valid {term : Term} :
    SourceTerm term →
    ValidRuntimeState ProgramStore.empty term := by
  intro hsource
  exact ⟨sourceInitialState_valid hsource, storeOwnersAllocated_empty⟩

/--
Source-level empty-store programs satisfy the initial hypotheses used by the
Section 4 soundness statements.
-/
theorem sourceInitialSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ∼ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    BorrowSafeEnv Env.empty ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    safeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    borrowSafeEnv_empty,
    operationalStoreProgress_empty⟩

/--
Source-level empty-store programs satisfy the mechanised runtime hypotheses,
including the explicit owner-allocation invariant.
-/
theorem sourceInitialRuntimeSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidRuntimeState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ∼ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    BorrowSafeEnv Env.empty ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialRuntimeState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    safeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    borrowSafeEnv_empty,
    operationalStoreProgress_empty⟩

/-- Well-typed source-level terms in the empty initial state satisfy Progress. -/
theorem sourceInitial_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  exact progress
    (sourceInitialState_valid hsource)
    (sourceTerm_validStoreTyping_empty hsource)
    wellFormedEnv_empty_all
    safeAbstraction_empty
    operationalStoreProgress_empty
    htyping

/-- Well-typed source-level terms satisfy Progress from the runtime hypothesis package. -/
theorem sourceInitial_runtime_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  rcases sourceInitialRuntimeSoundnessHypotheses
      (term := term) (lifetime := lifetime) hsource with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, _hwellFormed, _hborrowSafe, hstoreProgress⟩
  exact progress_runtime
    hvalidRuntime
    hvalidStoreTyping
    wellFormedEnv_empty_all
    hsafe
    hstoreProgress
    htyping

/-- Well-typed non-terminal source-level terms in the empty initial state can step. -/
theorem sourceInitial_progress_step {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step ProgramStore.empty lifetime term store' term' := by
  intro hsource htyping hnotTerminal
  exact (sourceInitial_progress hsource htyping).step_of_not_terminal hnotTerminal

/--
Well-typed non-terminal source-level terms can step from the runtime hypothesis
package used by the mechanised soundness statements.
-/
theorem sourceInitial_runtime_progress_step {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step ProgramStore.empty lifetime term store' term' := by
  intro hsource htyping hnotTerminal
  exact (sourceInitial_runtime_progress hsource htyping).step_of_not_terminal hnotTerminal

/--
Source-initial multistep preservation for a block containing a source-level
value.  This is the `R-BlockB` source-level instance of Lemma 4.11.
-/
theorem sourceInitial_blockB_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.block blockLifetime [.val value]) ty env₂ →
    MultiStep ProgramStore.empty lifetime
      (.block blockLifetime [.val value]) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.block blockLifetime [.val value]) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_blockB_value_multistep_runtime_no_slots
    (sourceInitialRuntimeState_valid hsourceTerm)
    safeAbstraction_empty
    htyping
    (empty_no_lifetime_slots blockLifetime)
    (sourceValue_validValue_of_empty_valueTyping hsource
      (blockValueTyping_valueTyping htyping))
    hmulti

/--
Source-initial multistep preservation for `box v` with a source-level value.
This is the `R-Box` source-level instance of Lemma 4.11.
-/
theorem sourceInitial_box_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue (.box ty) := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.box (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_box_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .box (.val value)) hsourceTerm)
    safeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti

/--
Source-initial multistep preservation for `let mut x = v` with a source-level
value.  This is the `R-Declare` source-level instance of Lemma 4.11.
-/
theorem sourceInitial_declare_value_multistep_preservation
    {x : Name} {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    MultiStep ProgramStore.empty lifetime
      (.letMut x (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.letMut x (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_declare_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .letMut x (.val value)) hsourceTerm)
    safeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti

/--
Source-level terminal preservation base case.

This is the source-initial instance of Lemma 4.11 when the program is already a
runtime value.  Since values cannot step, the multistep derivation is reflexive.
-/
theorem sourceInitial_multistep_value_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧
      finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.val value) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_multistep_runtime_value
    (sourceInitialRuntimeState_valid hsourceTerm)
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .val value) hsourceTerm)
    safeAbstraction_empty
    htyping
    hmulti

/-! ## Paper-Facing Section 4 Targets -/

/--
The exact well-formedness invariant needed for runtime references in `T-Const`.

`ValueTyping` for references only consults `σ`; it does not itself say that the
type stored in `σ` is well formed in the current environment.  This predicate
names that missing bridge explicitly.
-/
def StoreTypingRefsWellFormed
    (env : Env) (typing : StoreTyping) (lifetime : Lifetime) : Prop :=
  ∀ (ref : Reference) (ty : Ty),
    typing.tyOf ref.location = some ty →
    WellFormedTy env ty lifetime

/-- `T-Const` value well-formedness from an explicit reference-store invariant. -/
theorem valueTyping_result_wellFormed_of_refs {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreTypingRefsWellFormed env typing lifetime →
    ValueTyping typing value ty →
    WellFormedTy env ty lifetime := by
  intro hrefs htyping
  cases htyping with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | ref hlookup =>
      exact hrefs _ _ hlookup

@[simp] theorem storeTypingRefsWellFormed_empty (env : Env) (lifetime : Lifetime) :
    StoreTypingRefsWellFormed env StoreTyping.empty lifetime := by
  intro ref ty hlookup
  simp [StoreTyping.empty] at hlookup

theorem valueTyping_empty_result_wellFormed {env : Env}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValueTyping StoreTyping.empty value ty →
    WellFormedTy env ty lifetime := by
  intro htyping
  exact valueTyping_result_wellFormed_of_refs
    (storeTypingRefsWellFormed_empty env lifetime) htyping

theorem LValTyping.containedBorrowTargetsWellFormed {env : Env} {lv : LVal}
    {partialTy : PartialTy} {mutable : Bool} {targets : List LVal}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed htyping hcontainsTop
  exact LValTyping.rec
    (motive_1 := fun _lv partialTy _ _ =>
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime)
    (motive_2 := fun _targetLvs unionTy _ _ =>
      ∀ {mutable targets},
        PartialTyContains unionTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime)
    (by
      intro x slot hslot mutable targets hcontains
      exact EnvContains.borrowTargetsWellFormed hwellFormed
        ⟨slot, hslot, hcontains⟩)
    (by
      intro _lv inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _mutableBorrow _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets _ihBorrow ihTargets _mutable _targets
        hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
        _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
        _mutable _targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion
          (by
            intro mutable targets hcontainsHead
            exact BorrowTargetsWellFormed.inSlot (ihHead hcontainsHead))
          (by
            intro mutable targets hcontainsRest
            exact BorrowTargetsWellFormed.inSlot (ihRest hcontainsRest))
          hcontains)
        (LifetimeOutlives.refl lifetime))
    htyping
    hcontainsTop

theorem LValTyping.containedBorrowTargetsWellFormed_at_lifetime {env : Env}
    {lv : LVal} {partialTy : PartialTy} {valueLifetime : Lifetime}
    {mutable : Bool} {targets : List LVal} :
    ContainedBorrowsWellFormed env →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormed env targets valueLifetime := by
  intro hcontained htyping hcontainsTop
  exact LValTyping.rec
    (motive_1 := fun _lv partialTy valueLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets valueLifetime)
    (motive_2 := fun _targetLvs unionTy targetLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains unionTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets targetLifetime)
    (by
      intro x slot hslot mutable targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (hcontained x slot mutable targets hslot ⟨slot, hslot, hcontains⟩)
        (LifetimeOutlives.refl slot.lifetime))
    (by
      intro _lv _inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _mutableBorrow _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets _ihBorrow ihTargets _mutable _targets
        hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
        _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
        _mutable _targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion
          (by
            intro mutable targets hcontainsHead
            exact BorrowTargetsWellFormedInSlot.weaken
              (BorrowTargetsWellFormed.inSlot (ihHead hcontainsHead))
              (LifetimeIntersection.left_le hintersection))
          (by
            intro mutable targets hcontainsRest
            exact BorrowTargetsWellFormedInSlot.weaken
              (BorrowTargetsWellFormed.inSlot (ihRest hcontainsRest))
              (LifetimeIntersection.right_le hintersection))
          hcontains)
        (LifetimeOutlives.refl _))
    htyping
    hcontainsTop

theorem LValTyping.lifetime_outlives_of_base_outlives {env : Env}
    {current : Lifetime} :
    ContainedBorrowsWellFormed env →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      LValBaseOutlives env lv current →
      lifetime ≤ current) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → LValBaseOutlives env target current) →
      lifetime ≤ current) := by
  intro hcontained
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormed env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormed_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormed env targets current :=
          BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget⟩
          exact hbaseTarget))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormed env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormed_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormed env targets current :=
          BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget⟩
          exact hbaseTarget))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping

theorem LValTyping.lifetime_outlives_of_base_outlives_one {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    LValTyping env lv partialTy lifetime →
    LValBaseOutlives env lv current →
    lifetime ≤ current := by
  intro hcontained htyping hbase
  exact (LValTyping.lifetime_outlives_of_base_outlives
    (current := current) hcontained).1 htyping hbase

theorem TermTyping.target_lifetime_outlives_surviving_base_slot {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lv : LVal} {oldTy : PartialTy} {term : Term} {ty : Ty}
    {resultSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    LValTyping env₁ lv oldTy targetLifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.slotAt (LVal.base lv) = some resultSlot →
    targetLifetime ≤ resultSlot.lifetime := by
  intro hwellInitial hLv hterm hresultSlot
  rcases LValTyping.base_outlives_one hwellInitial hLv with
    ⟨sourceSlot, hsourceSlot, hsourceOutlivesCurrent⟩
  have hbaseSelf : LValBaseOutlives env₁ lv sourceSlot.lifetime :=
    ⟨sourceSlot, hsourceSlot, LifetimeOutlives.refl sourceSlot.lifetime⟩
  have htargetOutlivesSource :
      targetLifetime ≤ sourceSlot.lifetime :=
    LValTyping.lifetime_outlives_of_base_outlives_one
      hwellInitial.1 hLv hbaseSelf
  rcases (TermTyping.slot_lifetime_survives.1 hterm)
      hsourceOutlivesCurrent hsourceSlot with
    ⟨survivedSlot, hsurvivedSlot, hsurvivedLifetime⟩
  have hslotEq : survivedSlot = resultSlot := by
    have hsomeEq : some survivedSlot = some resultSlot := by
      rw [← hsurvivedSlot, hresultSlot]
    exact Option.some.inj hsomeEq
  rw [← hslotEq, ← hsurvivedLifetime]
  exact htargetOutlivesSource

theorem LValTyping.borrowTargetsWellFormed {env : Env} {lv : LVal}
    {mutable : Bool} {targets : List LVal}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty (.borrow mutable targets)) valueLifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed htyping
  exact LValTyping.containedBorrowTargetsWellFormed hwellFormed htyping
    PartialTyContains.here

theorem wellFormedTy_of_containedBorrowTargets {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      BorrowTargetsWellFormed env targets lifetime) →
    WellFormedTy env ty lifetime := by
  intro htargets
  exact Ty.rec
    (motive_1 := fun ty =>
      (∀ mutable targets,
        PartialTyContains (.ty ty) (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime) →
      WellFormedTy env ty lifetime)
    (motive_2 := fun _partialTy => True)
    (by
      intro _htargets
      exact WellFormedTy.unit)
    (by
      intro _htargets
      exact WellFormedTy.int)
    (by
      intro mutable targets htargets
      exact WellFormedTy.borrow (htargets mutable targets PartialTyContains.here))
    (by
      intro inner ih htargets
      exact WellFormedTy.box (ih (by
        intro mutable targets hcontains
        exact htargets mutable targets (PartialTyContains.tyBox hcontains))))
    (by
      intro _ty _ih
      trivial)
    (by
      intro _partialTy _ih
      trivial)
    (by
      intro _shape _ih
      trivial)
    ty htargets

theorem LValTyping.fullTyWellFormed {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    WellFormedTy env ty lifetime := by
  intro hwellFormed htyping
  exact wellFormedTy_of_containedBorrowTargets (by
    intro mutable targets hcontains
    exact LValTyping.containedBorrowTargetsWellFormed hwellFormed htyping
      hcontains)

/--
The `T-Copy` result type is well formed.

This is intentionally specialized by `copy(T)`: copyable types are only `int`
and immutable borrows, so we do not need a false theorem saying every full type
read from an lval is recursively well formed.
-/
theorem copyBorrowTargetsWellFormed {env : Env} {lv : LVal}
    {targets : List LVal} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty (.borrow false targets)) valueLifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed hLv
  exact LValTyping.borrowTargetsWellFormed hwellFormed hLv

theorem copyTy_result_wellFormed {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    CopyTy ty →
    WellFormedTy env ty lifetime := by
  intro hwellFormed hLv hcopy
  cases hcopy with
  | int =>
      exact WellFormedTy.int
  | immBorrow =>
      exact WellFormedTy.borrow
        (copyBorrowTargetsWellFormed hwellFormed hLv)

theorem PartialTyContains.of_strike {path : Path} {source struck : PartialTy}
    {needle : Ty} :
    Strike path source struck →
    PartialTyContains struck needle →
    PartialTyContains source needle := by
  intro hstrike hcontains
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains
  | cons _ path ih =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains with
      | box hinner =>
          exact PartialTyContains.box (ih hstrike hinner)

/-- A struck partial type contains no live full type.

`Strike` replaces the moved leaf by `undef` and only rebuilds boxes on the way
back to the root, so no `PartialTyContains` derivation can start from the struck
result. -/
theorem PartialTyContains.not_strike_result {path : Path} {source struck : PartialTy}
    {needle : Ty} :
    Strike path source struck →
    ¬ PartialTyContains struck needle := by
  intro hstrike hcontains
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains
  | cons _ path ih =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains with
      | box hinner =>
          exact ih hstrike hinner

theorem LVal.path_deref_append (lv : LVal) (suffix : Path) :
    LVal.path (.deref lv) ++ suffix = LVal.path lv ++ (() :: suffix) := by
  rw [LVal.path, List.append_assoc]
  rfl

theorem List.Unit_cons_append_eq_append_cons (path suffix : List Unit) :
    () :: (path ++ suffix) = path ++ (() :: suffix) := by
  induction path with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head
      simp [ih]

/-- A `Strike` following an lvalue path can be decomposed at the partial type
selected by the lvalue typing derivation.

The borrow-dereference case is where this lemma pays for itself: `Strike` can
only step through `PartialTy.box`, so it cannot take one more selector after an
lvalue whose selected type is a full borrow. -/
theorem LValTyping.strike_suffix_at_type {env : Env} :
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {slot struck suffix},
        env.slotAt (LVal.base lv) = some slot →
        Strike (LVal.path lv ++ suffix) slot.ty struck →
        ∃ struckAt, Strike suffix partialTy struckAt) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime → True) := by
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy _lifetime _ =>
        ∀ {slot struck suffix},
          env.slotAt (LVal.base lv) = some slot →
          Strike (LVal.path lv ++ suffix) slot.ty struck →
          ∃ struckAt, Strike suffix partialTy struckAt)
      (motive_2 := fun _targets _partialTy _lifetime _ => True)
      (by
        intro x envSlot hslot slot struck suffix hbase hstrike
        have hbase' : env.slotAt x = some slot := by
          simpa [LVal.base] using hbase
        have hslotEq : envSlot = slot := by
          have hsomeEq : some envSlot = some slot := by
            rw [← hslot, hbase']
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact ⟨struck, by simpa [LVal.path] using hstrike⟩)
      (by
        intro lv inner lifetime _htyping ih slot struck suffix hbase hstrike
        have hstrikeAtParent :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        rcases ih hbase hstrikeAtParent with ⟨parentStruck, hparentStruck⟩
        cases parentStruck with
        | ty parentTy =>
            simp [Strike] at hparentStruck
        | box innerStruck =>
            exact ⟨innerStruck, by simpa [Strike] using hparentStruck⟩
        | undef parentTy =>
            simp [Strike] at hparentStruck)
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          _hborrow _htargets ihBorrow _ihTargets slot struck suffix hbase hstrike
        have hstrikeAtBorrow :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        rcases ihBorrow hbase hstrikeAtBorrow with ⟨borrowStruck, hborrowStruck⟩
        simp [Strike] at hborrowStruck)
      (by
        intro target ty lifetime _htarget _ihTarget
        trivial)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest _hunion _hintersection _ihHead _ihRest
        trivial)
      htyping
  · intro targets partialTy lifetime _htyping
    trivial

/-- If an lvalue is moved by `Strike`, every borrow contained in its selected
partial type was already contained in the moved base slot.

This is the static origin fact needed for non-variable move result-extension.
The proof follows the lvalue spine.  Box dereferences push the obligation one
selector back toward the base slot; borrow dereferences are impossible because
`Strike` cannot continue below a full borrow leaf. -/
theorem LValTyping.contains_base_of_strike_suffix {env : Env} :
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {slot struck suffix needle},
        env.slotAt (LVal.base lv) = some slot →
        Strike (LVal.path lv ++ suffix) slot.ty struck →
        PartialTyContains partialTy needle →
        env ⊢ LVal.base lv ↝ needle) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime → True) := by
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy _lifetime _ =>
        ∀ {slot struck suffix needle},
          env.slotAt (LVal.base lv) = some slot →
          Strike (LVal.path lv ++ suffix) slot.ty struck →
          PartialTyContains partialTy needle →
          env ⊢ LVal.base lv ↝ needle)
      (motive_2 := fun _targets _partialTy _lifetime _ => True)
      (by
        intro x envSlot hslot slot _struck _suffix needle hbase _hstrike hcontains
        have hbase' : env.slotAt x = some slot := by
          simpa [LVal.base] using hbase
        have hslotEq : envSlot = slot := by
          have hsomeEq : some envSlot = some slot := by
            rw [← hslot, hbase']
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact ⟨envSlot, hslot, hcontains⟩)
      (by
        intro lv inner lifetime _htyping ih slot struck suffix needle hbase hstrike
          hcontains
        have hstrikeAtParent :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        exact ih hbase hstrikeAtParent (PartialTyContains.box hcontains))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets _ihBorrow _ihTargets slot struck suffix needle hbase hstrike
          _hcontains
        have hstrikeAtBorrow :
            Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck := by
          simpa [LVal.path_deref_cons, List.Unit_cons_append_eq_append_cons]
            using hstrike
        rcases (LValTyping.strike_suffix_at_type.1 hborrow hbase hstrikeAtBorrow) with
          ⟨borrowStruck, hborrowStruck⟩
        simp [Strike] at hborrowStruck)
      (by
        intro target ty lifetime _htarget _ihTarget
        trivial)
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest _hunion _hintersection _ihHead _ihRest
        trivial)
      htyping
  · intro targets partialTy lifetime _htyping
    trivial

theorem LValTyping.contains_base_of_strike {env : Env} {lv : LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} {slot : EnvSlot}
    {struck : PartialTy}
    {needle : Ty} :
    LValTyping env lv partialTy lifetime →
    env.slotAt (LVal.base lv) = some slot →
    Strike (LVal.path lv) slot.ty struck →
    PartialTyContains partialTy needle →
    env ⊢ LVal.base lv ↝ needle := by
  intro htyping hslot hstrike hcontains
  simpa using
    (LValTyping.contains_base_of_strike_suffix.1 htyping
      (slot := slot) (struck := struck) (suffix := []) hslot
      (by simpa using hstrike) hcontains)

theorem EnvContains.of_move {env env' : Env} {lv : LVal} {x : Name}
    {ty : Ty} :
    EnvMove env lv env' →
    env' ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hmove hcontains
  rcases hmove with ⟨slot, struck, hslot, hstrike, henv'⟩
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hcontainedSlotEq :
        containedSlot = { slot with ty := struck } := by
      have h :
          { slot with ty := struck } = containedSlot := by
        simpa [henv', Env.update] using hcontainedSlot
      exact h.symm
    subst hcontainedSlotEq
    exact ⟨slot, hslot, PartialTyContains.of_strike hstrike hcontainsTy⟩
  · have hslotOld : env.slotAt x = some containedSlot := by
      simpa [henv', Env.update, hx] using hcontainedSlot
    exact ⟨containedSlot, hslotOld, hcontainsTy⟩

/-- The base slot struck by an `EnvMove` cannot still contain a live borrow in
the moved environment. -/
theorem EnvContains.move_base_same_false {env env' : Env} {lv : LVal}
    {mutable : Bool} {targets : List LVal} :
    EnvMove env lv env' →
    ¬ env' ⊢ LVal.base lv ↝ Ty.borrow mutable targets := by
  intro hmove hcontains
  rcases hmove with ⟨slot, struck, _hslot, hstrike, henv'⟩
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq :
      containedSlot = { slot with ty := struck } := by
    have h :
        { slot with ty := struck } = containedSlot := by
      simpa [henv', Env.update] using hcontainedSlot
    exact h.symm
  subst hcontainedSlotEq
  exact PartialTyContains.not_strike_result hstrike hcontainsTy

/-- Moving an lval preserves borrow safety of the environment before adding the
result binding.

`EnvMove` only strikes part of a slot to `undef`; every contained borrow still
visible in the moved environment was already contained in the source
environment.  Thus the original borrow-safety relation applies directly. -/
theorem borrowSafeEnv_move {env env' : Env} {lv : LVal} :
    BorrowSafeEnv env →
    EnvMove env lv env' →
    BorrowSafeEnv env' := by
  intro hsafe hmove x y mutable targetsMutable targetsOther targetMutable
    targetOther hcontainsMutable hcontainsOther htargetMutable htargetOther hconflict
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    (EnvContains.of_move hmove hcontainsMutable)
    (EnvContains.of_move hmove hcontainsOther)
    htargetMutable htargetOther hconflict

theorem borrowSafety_move_borrowFree_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {ty : Ty}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    TyBorrowFree ty →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe htyping hborrowFree
  cases htyping with
  | move _hLv _hnotWrite hmove =>
      exact borrowSafeEnv_update_fresh_borrowFree
        (borrowSafeEnv_move hsafe hmove) hborrowFree

/-- Result-extension after a move, factored around the one remaining typing
origin fact.

If every borrow contained in the moved result type was contained in the moved
base slot before the move, then adding the moved value as a fresh result root is
borrow safe.  Any old root that conflicts with the fresh result must have been
the moved base by `BorrowSafeEnv env`; but the moved environment no longer
contains live borrows at that base.
-/
theorem borrowSafeEnv_move_result_extension_of_base_contains {env env₂ : Env}
    {lv : LVal} {ty : Ty} {gamma : Name} {lifetime : Lifetime} :
    BorrowSafeEnv env →
    EnvMove env lv env₂ →
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      env ⊢ LVal.base lv ↝ Ty.borrow mutable targets) →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hmove hbaseContains _hfresh a b mutable targetsMutable targetsOther
    targetMutable targetOther hcontainsMutable hcontainsOther htargetMutable
    htargetOther hconflict
  by_cases ha : a = gamma
  · subst a
    have hcontainsMutableAtGamma :
        (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ⊢
          gamma ↝ Ty.borrow true targetsMutable := by
      simpa using hcontainsMutable
    rcases hcontainsMutableAtGamma with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hslotEq :
        containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
        simpa [Env.update] using hcontainedSlot
      exact h.symm
    subst hslotEq
    by_cases hb : b = gamma
    · exact hb.symm
    · have hcontainsOtherMove :
          env₂ ⊢ b ↝ Ty.borrow mutable targetsOther :=
        EnvContains.update_fresh_ne hb hcontainsOther
      by_cases hbBase : b = LVal.base lv
      · subst hbBase
        exact False.elim (EnvContains.move_base_same_false hmove hcontainsOtherMove)
      · have hcontainsOtherOld :
            env ⊢ b ↝ Ty.borrow mutable targetsOther :=
          EnvContains.of_move hmove hcontainsOtherMove
        have hbaseEq :
            LVal.base lv = b :=
          hsafe (LVal.base lv) b mutable targetsMutable targetsOther targetMutable
            targetOther
            (hbaseContains true targetsMutable hcontainsTy)
            hcontainsOtherOld
            htargetMutable htargetOther hconflict
        exact False.elim (hbBase hbaseEq.symm)
  · by_cases hb : b = gamma
    · subst b
      have hcontainsOtherAtGamma :
          (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) ⊢
            gamma ↝ Ty.borrow mutable targetsOther := by
        simpa using hcontainsOther
      rcases hcontainsOtherAtGamma with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hslotEq :
          containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
          simpa [Env.update] using hcontainedSlot
        exact h.symm
      subst hslotEq
      have hcontainsMutableMove :
          env₂ ⊢ a ↝ Ty.borrow true targetsMutable :=
        EnvContains.update_fresh_ne ha hcontainsMutable
      by_cases haBase : a = LVal.base lv
      · subst haBase
        exact False.elim (EnvContains.move_base_same_false hmove hcontainsMutableMove)
      · have hcontainsMutableOld :
            env ⊢ a ↝ Ty.borrow true targetsMutable :=
          EnvContains.of_move hmove hcontainsMutableMove
        have hbaseEq :
            a = LVal.base lv :=
          hsafe a (LVal.base lv) mutable targetsMutable targetsOther targetMutable
            targetOther hcontainsMutableOld
            (hbaseContains mutable targetsOther hcontainsTy)
            htargetMutable htargetOther hconflict
        exact False.elim (haBase hbaseEq)
    · exact borrowSafeEnv_move hsafe hmove a b mutable targetsMutable targetsOther
        targetMutable targetOther
        (EnvContains.update_fresh_ne ha hcontainsMutable)
        (EnvContains.update_fresh_ne hb hcontainsOther)
        htargetMutable htargetOther hconflict

theorem tyBorrowSafeAgainstEnv_move_of_base_contains {env env₂ : Env}
    {lv : LVal} {ty : Ty} :
    BorrowSafeEnv env →
    EnvMove env lv env₂ →
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      env ⊢ LVal.base lv ↝ Ty.borrow mutable targets) →
    TyBorrowSafeAgainstEnv env₂ ty := by
  intro hsafe hmove hbaseContains
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther hcontainsTy
      hcontainsOther htargetMutable htargetOther hconflict
    by_cases hxBase : x = LVal.base lv
    · subst hxBase
      exact False.elim (EnvContains.move_base_same_false hmove hcontainsOther)
    · have hcontainsOtherOld :
          env ⊢ x ↝ Ty.borrow mutable targetsOther :=
        EnvContains.of_move hmove hcontainsOther
      have hbaseEq :
          LVal.base lv = x :=
        hsafe (LVal.base lv) x mutable targetsMutable targetsOther targetMutable
          targetOther
          (hbaseContains true targetsMutable hcontainsTy)
          hcontainsOtherOld
          htargetMutable htargetOther hconflict
      exact False.elim (hxBase hbaseEq.symm)
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      hcontainsMutable hcontainsTy htargetMutable htargetOther hconflict
    by_cases hxBase : x = LVal.base lv
    · subst hxBase
      exact False.elim (EnvContains.move_base_same_false hmove hcontainsMutable)
    · have hcontainsMutableOld :
          env ⊢ x ↝ Ty.borrow true targetsMutable :=
        EnvContains.of_move hmove hcontainsMutable
      have hbaseEq :
          x = LVal.base lv :=
        hsafe x (LVal.base lv) mutable targetsMutable targetsOther targetMutable
          targetOther hcontainsMutableOld
          (hbaseContains mutable targetsOther hcontainsTy)
          htargetMutable htargetOther hconflict
      exact False.elim (hxBase hbaseEq)

theorem EnvContains.move_var_same_false {env env' : Env} {x : Name}
    {slot : EnvSlot} {ty : Ty} {mutable : Bool} {targets : List LVal} :
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    EnvMove env (.var x) env' →
    ¬ env' ⊢ x ↝ Ty.borrow mutable targets := by
  intro _hslot _hslotTy hmove hcontains
  exact EnvContains.move_base_same_false hmove hcontains

theorem borrowSafety_move_var_result_extension {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {ty : Ty} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.move (.var x)) ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe htyping hfresh a b mutable targetsMutable targetsOther
    targetMutable targetOther hcontainsMutable hcontainsOther htargetMutable
    htargetOther hconflict
  cases htyping with
  | move hLv hnotWrite hmove =>
      rcases LValTyping.var_inv hLv with
        ⟨sourceSlot, hslotSource, hsourceTy, _hsourceLifetime⟩
      by_cases ha : a = gamma
      · subst a
        have hcontainsMovedMutable :
            env ⊢ x ↝ Ty.borrow true targetsMutable := by
          rcases hcontainsMutable with
            ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
          have hslotEq :
              containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
            have h :
                { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
              simpa [Env.update] using hcontainedSlot
            exact h.symm
          subst hslotEq
          exact ⟨sourceSlot, hslotSource, by
            rw [hsourceTy]
            exact hcontainsTy⟩
        by_cases hb : b = gamma
        · subst b
          exact rfl
        · have hcontainsOtherMove :
              env₂ ⊢ b ↝ Ty.borrow mutable targetsOther :=
            EnvContains.update_fresh_ne hb hcontainsOther
          by_cases hbx : b = x
          · subst b
            exact False.elim
              (EnvContains.move_var_same_false hslotSource hsourceTy hmove
                hcontainsOtherMove)
          · have hcontainsOtherOld :
                env ⊢ b ↝ Ty.borrow mutable targetsOther :=
              EnvContains.of_move hmove hcontainsOtherMove
            have hsafeEq :
                x = b :=
              hsafe x b mutable targetsMutable targetsOther targetMutable
                targetOther hcontainsMovedMutable hcontainsOtherOld
                htargetMutable htargetOther hconflict
            exact False.elim (hbx hsafeEq.symm)
      · by_cases hb : b = gamma
        · subst b
          have hcontainsMovedOther :
              env ⊢ x ↝ Ty.borrow mutable targetsOther := by
            rcases hcontainsOther with
              ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
            have hslotEq :
                containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
              have h :
                  { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
                simpa [Env.update] using hcontainedSlot
              exact h.symm
            subst hslotEq
            exact ⟨sourceSlot, hslotSource, by
              rw [hsourceTy]
              exact hcontainsTy⟩
          have hcontainsMutableMove :
              env₂ ⊢ a ↝ Ty.borrow true targetsMutable :=
            EnvContains.update_fresh_ne ha hcontainsMutable
          by_cases hax : a = x
          · subst a
            exact False.elim
              (EnvContains.move_var_same_false hslotSource hsourceTy hmove
                hcontainsMutableMove)
          · have hcontainsMutableOld :
                env ⊢ a ↝ Ty.borrow true targetsMutable :=
              EnvContains.of_move hmove hcontainsMutableMove
            have hcontainsOtherOld :
                env ⊢ x ↝ Ty.borrow mutable targetsOther :=
              hcontainsMovedOther
            have hsafeEq :
                a = x :=
              hsafe a x mutable targetsMutable targetsOther targetMutable
                targetOther hcontainsMutableOld hcontainsOtherOld
                htargetMutable htargetOther hconflict
            exact False.elim (hax hsafeEq)
        · exact borrowSafeEnv_move hsafe hmove a b mutable targetsMutable
            targetsOther targetMutable targetOther
            (EnvContains.update_fresh_ne ha hcontainsMutable)
            (EnvContains.update_fresh_ne hb hcontainsOther)
            htargetMutable htargetOther hconflict

theorem EnvMove.oldSlot_of_newSlot {env env' : Env} {lv : LVal}
    {x : Name} {newSlot : EnvSlot} :
    EnvMove env lv env' →
    env'.slotAt x = some newSlot →
    ∃ oldSlot,
      env.slotAt x = some oldSlot ∧
      oldSlot.lifetime = newSlot.lifetime := by
  intro hmove hnewSlot
  rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hnewSlotEq :
        newSlot = { moveSlot with ty := struck } := by
      have h :
          { moveSlot with ty := struck } = newSlot := by
        simpa [henv', Env.update] using hnewSlot
      exact h.symm
    subst hnewSlotEq
    exact ⟨moveSlot, hmoveSlot, rfl⟩
  · have holdSlot : env.slotAt x = some newSlot := by
      simpa [henv', Env.update, hx] using hnewSlot
    exact ⟨newSlot, holdSlot, rfl⟩

theorem not_pathConflicts_of_not_writeProhibited_contains {env : Env}
    {lv target : LVal} {x : Name} {mutable : Bool} {targets : List LVal} :
    ¬ WriteProhibited env lv →
    env ⊢ x ↝ Ty.borrow mutable targets →
    target ∈ targets →
    ¬ target ⋈ lv := by
  intro hnotWrite hcontains htarget hconflict
  cases mutable with
  | false =>
      exact hnotWrite (Or.inr ⟨x, targets, target, hcontains, htarget, hconflict⟩)
  | true =>
      exact hnotWrite (Or.inl ⟨x, targets, target, hcontains, htarget, hconflict⟩)

theorem LValTyping.no_writeProhibited_targets {env : Env} {moved : LVal} :
    ¬ WriteProhibited env moved →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        ∀ target,
          target ∈ targets →
          ¬ target ⋈ moved) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {mutable borrowTargets},
        PartialTyContains partialTy (.borrow mutable borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ target ⋈ moved) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains target
          htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains target
          htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping

theorem LValTyping.move_of_not_pathConflicts {env env' : Env} {moved : LVal} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ¬ lv ⋈ moved →
      LValTyping env' lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ moved) →
      LValTargetsTyping env' targets partialTy lifetime) := by
  intro hmove hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ moved →
        LValTyping env' lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ moved) →
        LValTargetsTyping env' targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
        have hx : x ≠ LVal.base moved := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by simpa [henv', Env.update, hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ moved := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ moved := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ moved →
        LValTyping env' lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ moved) →
        LValTargetsTyping env' targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
        have hx : x ≠ LVal.base moved := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by simpa [henv', Env.update, hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ moved := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ moved := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

theorem LValTyping.update_of_not_pathConflicts {env : Env} {x : Name}
    {slot : EnvSlot} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ¬ lv ⋈ (.var x) →
      LValTyping (env.update x slot) lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
      LValTargetsTyping (env.update x slot) targets partialTy lifetime) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) →
        LValTyping (env.update x slot) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping (env.update x slot) targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping (env.update x slot) lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow' PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) →
        LValTyping (env.update x slot) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping (env.update x slot) targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping (env.update x slot) lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow' PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

theorem BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {slotLifetime : Lifetime}
    {targets : List LVal} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    BorrowTargetsWellFormedInSlot (env.update x slot) slotLifetime targets := by
  intro hnotWrite htargets hnotTargets target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  refine ⟨targetTy, targetLifetime,
    (LValTyping.update_of_not_pathConflicts (slot := slot) hnotWrite).1
      htyping (hnotTargets target htarget),
    houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  have hbaseNe : LVal.base target ≠ x := by
    intro hbaseEq
    exact hnotTargets target htarget hbaseEq
  have hbaseSlot' :
      (env.update x slot).slotAt (LVal.base target) = some baseSlot := by
    simpa [Env.update, hbaseNe] using hbaseSlot
  exact ⟨baseSlot, hbaseSlot', hbaseOutlives⟩

theorem PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {slotLifetime : Lifetime}
    {partialTy : PartialTy} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ {mutable targets},
      PartialTyContains partialTy (.borrow mutable targets) →
      ∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    PartialTyBorrowsWellFormedInSlot
      (env.update x slot) slotLifetime partialTy := by
  intro hnotWrite hpartial hnotTargets mutable targets hcontains
  exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
    (slot := slot) hnotWrite (hpartial hcontains)
    (hnotTargets hcontains)

theorem ContainedBorrowsWellFormed.slot_partial {env : Env}
    {x : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    env.slotAt x = some slot →
    PartialTyBorrowsWellFormedInSlot env slot.lifetime slot.ty := by
  intro hcontained hslot mutable targets hcontains
  exact hcontained x slot mutable targets hslot ⟨slot, hslot, hcontains⟩

theorem ContainedBorrowsWellFormed.update_slot {env : Env} {x : Name}
    {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot (env.update x slot) slot.lifetime slot.ty →
    ¬ WriteProhibited (env.update x slot) (.var x) →
    ContainedBorrowsWellFormed (env.update x slot) := by
  intro hcontained hslotTargets hnotWrite y resultSlot mutable targets
    hresultSlot hcontains
  by_cases hy : y = x
  · subst hy
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hresultSlotEq : resultSlot = slot := by
      have h : slot = resultSlot := by
        simpa [Env.update] using hresultSlot
      exact h.symm
    have hcontainedSlotEq : containedSlot = slot := by
      have h : slot = containedSlot := by
        simpa [Env.update] using hcontainedSlot
      exact h.symm
    have hcontainsSlot : PartialTyContains slot.ty (.borrow mutable targets) := by
      simpa [hcontainedSlotEq] using hcontainsTy
    rw [hresultSlotEq]
    exact hslotTargets hcontainsSlot
  · rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hresultSlotOld : env.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresultSlot
    have hcontainedSlotOld : env.slotAt y = some containedSlot := by
      simpa [Env.update, hy] using hcontainedSlot
    have hcontainedSlotEq : containedSlot = resultSlot := by
      have hsomeEq : some containedSlot = some resultSlot := by
        rw [← hcontainedSlotOld, hresultSlotOld]
      exact Option.some.inj hsomeEq
    have htargetsOld :
        BorrowTargetsWellFormedInSlot env resultSlot.lifetime targets := by
      rw [← hcontainedSlotEq]
      exact hcontained y containedSlot mutable targets hcontainedSlotOld
        ⟨containedSlot, hcontainedSlotOld, hcontainsTy⟩
    exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
      (slot := slot) hnotWrite htargetsOld
      (by
        intro target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains
          hnotWrite
          ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
          htarget)

theorem declare_preserves_wellFormed_output_fresh {env₂ env₃ : Env}
    {lifetime : Lifetime} {x : Name} {ty : Ty} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh x →
    FreshUpdateCoherenceObligations env₂ x ty lifetime →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    WellFormedEnv env₃ lifetime := by
  intro hwellFormed hwellTy hfresh hcoh henv₃
  rw [henv₃]
  exact WellFormedEnv.update_fresh_ty hwellFormed hwellTy hfresh hcoh

theorem ContainedBorrowsWellFormed.move {env env' : Env} {lv : LVal}
    {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    ContainedBorrowsWellFormed env' := by
  intro hwellFormed hnotWrite hmove x slot mutable targets hslot hcontains
  rcases EnvMove.oldSlot_of_newSlot hmove hslot with
    ⟨oldSlot, holdSlot, hlifetime⟩
  rcases EnvContains.of_move hmove hcontains with
    ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  have hcontainedOldSlotEq : containedOldSlot = oldSlot := by
    have hsomeEq : some oldSlot = some containedOldSlot := by
      rw [← holdSlot, hcontainedOldSlot]
    injection hsomeEq with heq
    exact heq.symm
  have hlifetimeContained : containedOldSlot.lifetime = slot.lifetime := by
    rw [hcontainedOldSlotEq, hlifetime]
  have htargetsOld :
      BorrowTargetsWellFormedInSlot env containedOldSlot.lifetime targets :=
    hwellFormed.1 x containedOldSlot mutable targets hcontainedOldSlot
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  rw [← hlifetimeContained]
  have hnotTargets : ∀ target, target ∈ targets → ¬ target ⋈ lv := by
    intro target htarget
    exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩ htarget
  intro target htarget
  rcases htargetsOld target htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  exact ⟨targetTy, targetLifetime,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
      htyping (hnotTargets target htarget),
    houtlives,
    LValBaseOutlives.move_of_not_pathConflicts
      hmove (hnotTargets target htarget) hbase⟩

theorem BorrowTargetsWellFormed.move_of_no_pathConflicts {env env' : Env}
    {moved : LVal} {targets : List LVal} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    BorrowTargetsWellFormed env targets lifetime →
    (∀ target, target ∈ targets → ¬ target ⋈ moved) →
    BorrowTargetsWellFormed env' targets lifetime := by
  intro hmove hnotWrite htargets hnotTargets
  cases htargets with
  | intro hmembers =>
      refine BorrowTargetsWellFormed.intro ?_
      intro target htarget
      rcases hmembers target htarget with
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
      exact ⟨targetTy, targetLifetime,
        (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
          htyping (hnotTargets target htarget),
        houtlives,
        LValBaseOutlives.move_of_not_pathConflicts
          hmove (hnotTargets target htarget) hbase⟩

theorem WellFormedTy.move_of_no_pathConflicts {env env' : Env}
    {moved : LVal} {ty : Ty} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    WellFormedTy env ty lifetime →
    (∀ mutable targets target,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      target ∈ targets →
      ¬ target ⋈ moved) →
    WellFormedTy env' ty lifetime := by
  intro hmove hnotWrite hwellTy hnotConflicts
  induction hwellTy with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | borrow htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.move_of_no_pathConflicts
          hmove hnotWrite htargets
          (by
            intro target htarget
            exact hnotConflicts _ _ target PartialTyContains.here htarget))
  | box hinner ih =>
      exact WellFormedTy.box (ih (by
        intro mutable targets target hcontains htarget
        exact hnotConflicts mutable targets target
          (PartialTyContains.tyBox hcontains) htarget))

theorem WellFormedTy.move_result {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedTy env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  have hwellTy : WellFormedTy env ty lifetime :=
    LValTyping.fullTyWellFormed hwellFormed hLv
  exact WellFormedTy.move_of_no_pathConflicts hmove hnotWrite hwellTy
    (by
      intro mutable targets target hcontains htarget
      exact (LValTyping.no_writeProhibited_targets hnotWrite).1
        hLv hcontains target htarget)

/-- `Strike` only removes variables (it replaces a sub-value by `undef`). -/
theorem Strike.vars_subset :
    ∀ {path : Path} {ty struck : PartialTy}, Strike path ty struck →
      ∀ v, v ∈ PartialTy.vars struck → v ∈ PartialTy.vars ty := by
  intro path
  induction path with
  | nil =>
      intro ty struck h v hv
      cases ty with
      | ty t =>
          cases struck with
          | undef t' => simp [PartialTy.vars] at hv
          | ty _ => simp [Strike] at h
          | box _ => simp [Strike] at h
      | box _ => simp [Strike] at h
      | undef _ => simp [Strike] at h
  | cons _ rest ih =>
      intro ty struck h v hv
      cases ty with
      | box inner =>
          cases struck with
          | box struck' =>
              simp only [PartialTy.vars] at hv ⊢
              exact ih (show Strike rest inner struck' from h) v hv
          | ty _ => simp [Strike] at h
          | undef _ => simp [Strike] at h
      | ty _ => simp [Strike] at h
      | undef _ => simp [Strike] at h

/-- `Linearizable` is preserved by a move (the same rank function works; the
moved slot's type loses variables via `Strike`). -/
theorem Linearizable.move {env env' : Env} {lv : LVal}
    (hmove : EnvMove env lv env') (h : Linearizable env) :
    Linearizable env' := by
  rcases hmove with ⟨slot, struck, hslot, hstrike, henv'⟩
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x s hs
  subst henv'
  by_cases hx : x = LVal.base lv
  · subst hx
    have hseq : s = { slot with ty := struck } := by
      have h := hs
      simpa [Env.update] using h.symm
    subst hseq
    intro v hv
    exact hφ (LVal.base lv) slot hslot v
      (Strike.vars_subset hstrike v (by simpa using hv))
  · have hsenv : env.slotAt x = some s := by simpa [Env.update, hx] using hs
    exact hφ x s hsenv

/-- A partial type with no defined `.ty` leaf reachable: every `Strike` result
is of this form, and an lval typing rooted at a struck slot stays in it (so it
can never be a defined borrow). -/
def IsBoxUndef : PartialTy → Prop
  | .ty _ => False
  | .box inner => IsBoxUndef inner
  | .undef _ => True

theorem Strike.isBoxUndef :
    ∀ {path : Path} {ty struck : PartialTy}, Strike path ty struck → IsBoxUndef struck := by
  intro path
  induction path with
  | nil =>
      intro ty struck h
      cases ty with
      | ty t => cases struck with
        | undef _ => trivial
        | ty _ => simp [Strike] at h
        | box _ => simp [Strike] at h
      | box _ => simp [Strike] at h
      | undef _ => simp [Strike] at h
  | cons _ rest ih =>
      intro ty struck h
      cases ty with
      | box inner => cases struck with
        | box struck' =>
            have h' : Strike rest inner struck' := h
            show IsBoxUndef struck'
            exact ih h'
        | ty _ => simp [Strike] at h
        | undef _ => simp [Strike] at h
      | ty _ => simp [Strike] at h
      | undef _ => simp [Strike] at h

/-- An lval typed in the moved environment whose base is the moved variable has a
`Strike`-shaped (box/undef) type — never a defined `.ty` (in particular never a
borrow). -/
theorem LValTyping.isBoxUndef_of_base_moved {env : Env} {lv : LVal}
    {slot : EnvSlot} {struck : PartialTy}
    (_hslot : env.slotAt (LVal.base lv) = some slot)
    (hstrike : Strike (LVal.path lv) slot.ty struck) :
    ∀ {lv' p lf},
      LValTyping (env.update (LVal.base lv) { slot with ty := struck }) lv' p lf →
      LVal.base lv' = LVal.base lv → IsBoxUndef p := by
  intro lv' p lf h
  refine LValTyping.rec
    (motive_1 := fun lv' p _ _ => LVal.base lv' = LVal.base lv → IsBoxUndef p)
    (motive_2 := fun _ _ _ _ => True)
    ?var ?box ?borrow ?singleton ?cons h
  · intro y ySlot hySlot hbase
    have hy : y = LVal.base lv := by simpa [LVal.base] using hbase
    subst hy
    have : ySlot = { slot with ty := struck } := by
      simpa [Env.update] using hySlot.symm
    subst this
    exact Strike.isBoxUndef hstrike
  · intro lv'' inner lifetime _htyping ih hbase
    have := ih (by simpa [LVal.base] using hbase)
    simpa [IsBoxUndef] using this
  · intro lv'' mutable targets _bLf _tLf _tTy hborrow _htargets ihBorrow _ihTargets hbase
    have := ihBorrow (by simpa [LVal.base] using hbase)
    simp [IsBoxUndef] at this
  · intro _ _ _ _ _; trivial
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _; trivial

/-- `Coherent` is preserved by a move.  A defined borrow `lv':&T` in the moved
environment cannot be rooted at the (undef'd) moved variable
(`isBoxUndef_of_base_moved`), so it transports backward to the original
environment (restoring the moved slot is an update with no path conflict), where
`Coherent env` provides a joint typing of `T`; the joint typing then transports
forward across the move (the targets do not conflict with the moved value, by
`¬WriteProhibited`). -/
theorem Coherent.move {env env' : Env} {lv : LVal} {lifetime : Lifetime}
    (hwellFormed : WellFormedEnv env lifetime)
    (hnotWrite : ¬ WriteProhibited env lv)
    (hmove : EnvMove env lv env')
    (hcohEnv : Coherent env) : Coherent env' := by
  have hmoveCopy := hmove
  rcases hmoveCopy with ⟨slot, struck, hslot, hstrike, henv'⟩
  subst henv'
  intro lv' m T bLf hty'
  have hbaseNe : ¬ lv' ⋈ lv := by
    intro hbeq
    have hbu := LValTyping.isBoxUndef_of_base_moved hslot hstrike hty'
      (by simpa [PathConflicts, LVal.base] using hbeq)
    simp [IsBoxUndef] at hbu
  -- restoring the moved slot returns the original environment
  have hrestore :
      (env.update (LVal.base lv) { slot with ty := struck }).update (LVal.base lv) slot
        = env := by
    obtain ⟨g⟩ := env
    simp only [Env.update]
    congr 1
    funext y
    by_cases hy : y = LVal.base lv
    · subst hy; simpa using hslot.symm
    · simp [hy]
  have hnotWriteVarEnv : ¬ WriteProhibited env (.var (LVal.base lv)) :=
    not_writeProhibited_var_base hnotWrite
  have hnotWriteVar :
      ¬ WriteProhibited
        ((env.update (LVal.base lv) { slot with ty := struck }).update (LVal.base lv) slot)
        (.var (LVal.base lv)) := by rw [hrestore]; exact hnotWriteVarEnv
  -- backward typing: env' → env (restore update, no conflict)
  have htyEnvRestore :
      LValTyping ((env.update (LVal.base lv) { slot with ty := struck }).update
        (LVal.base lv) slot) lv' (.ty (.borrow m T)) bLf :=
    (LValTyping.update_of_not_pathConflicts hnotWriteVar).1 hty'
      (by simpa [PathConflicts, LVal.base] using hbaseNe)
  have htyEnv : LValTyping env lv' (.ty (.borrow m T)) bLf := by
    rwa [hrestore] at htyEnvRestore
  rcases hcohEnv lv' m T bLf htyEnv with ⟨ty, lt, htgtsEnv⟩
  -- targets do not conflict with the moved value
  have hnotTargets : ∀ target, target ∈ T → ¬ target ⋈ lv := by
    intro target htarget
    exact (LValTyping.no_writeProhibited_targets hnotWrite).1 htyEnv
      PartialTyContains.here target htarget
  -- forward transport of the joint typing across the move
  exact ⟨ty, lt,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).2 htgtsEnv hnotTargets⟩

/--
Move Preservation for well-formed environments, used in Lemma 4.9.

This is the proof obligation described in the `T-Move` case of the paper:
`move(Γ, w)` replaces the moved component by `undef`, and the
`¬writeProhibited(Γ, w)` premise prevents this from invalidating any surviving
borrow target.
-/
theorem move_preserves_wellFormed {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedEnv env' lifetime ∧ WellFormedTy env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  refine ⟨⟨ContainedBorrowsWellFormed.move hwellFormed hnotWrite hmove,
      EnvSlotsOutlive.move hwellFormed.2.1 hmove, ?_, ?_⟩,
    WellFormedTy.move_result hwellFormed hLv hnotWrite hmove⟩
  · exact Coherent.move hwellFormed hnotWrite hmove hwellFormed.2.2.1
  · exact Linearizable.move hmove hwellFormed.2.2.2

theorem EnvWrite.preserves_containedBorrowsWellFormed_var {env result : Env}
    {lifetime targetLifetime : Lifetime} {x : Name}
    {oldTy : PartialTy} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    LValTyping env (.var x) oldTy targetLifetime →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite 0 env (.var x) rhsTy result →
    ¬ WriteProhibited result (.var x) →
    ContainedBorrowsWellFormed result := by
  intro hwellFormed hLhs hwellRhs hwrite hnotWrite
  rcases LValTyping.var_inv hLhs with
    ⟨lhsSlot, hlhsSlot, _holdTy, hlhsLifetime⟩
  cases hwrite with
  | intro hwriteSlot hupdate =>
      rename_i writeEnv writeSlot updatedTy
      simp [LVal.base, LVal.path] at hwriteSlot hupdate
      have hslotEq : writeSlot = lhsSlot := by
        have hsomeEq : some writeSlot = some lhsSlot := by
          rw [← hwriteSlot, hlhsSlot]
        exact Option.some.inj hsomeEq
      cases hupdate with
      | strong =>
          have hnotWrite' :
              ¬ WriteProhibited
                (env.update x { writeSlot with ty := PartialTy.ty rhsTy })
                (.var x) := by
            simpa [LVal.base] using hnotWrite
          have hslotTargets :
              PartialTyBorrowsWellFormedInSlot
                (env.update x { writeSlot with ty := PartialTy.ty rhsTy })
                writeSlot.lifetime
                ({ writeSlot with ty := PartialTy.ty rhsTy }).ty := by
            intro mutable targets hcontainsTy
            have htargetsEnv :
                BorrowTargetsWellFormedInSlot env targetLifetime targets :=
              borrowTargetsWellFormedInSlot_of_wellFormedTy_contains
                hwellRhs hcontainsTy
            have htargetsEnvAtSlot :
                BorrowTargetsWellFormedInSlot env writeSlot.lifetime targets := by
              rw [hslotEq, hlhsLifetime]
              exact htargetsEnv
            exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
              (x := x)
              (slot := { writeSlot with ty := PartialTy.ty rhsTy }) hnotWrite'
              htargetsEnvAtSlot
              (by
                intro target htarget
                have hcontainsUpdated :
                    (env.update x { writeSlot with ty := PartialTy.ty rhsTy }) ⊢
                      x ↝ Ty.borrow mutable targets :=
                  ⟨{ writeSlot with ty := PartialTy.ty rhsTy },
                    by simp [Env.update],
                    hcontainsTy⟩
                exact not_pathConflicts_of_not_writeProhibited_contains
                  hnotWrite'
                  hcontainsUpdated
                  htarget)
          simpa [LVal.base] using
            ContainedBorrowsWellFormed.update_slot
              hwellFormed.1 hslotTargets hnotWrite'

/-- Remaining update invariant needed by Lemma 4.9.

The `W-Weak` union case is no longer a caller obligation:
`PartialTyBorrowsWellFormedInSlot.of_partialTyUnion` proves it directly for the
per-target invariant.  The package now only records the non-local mutable-borrow
fan-out fact, where branch writes and joins must preserve observer target
well-formedness.
-/
structure UpdateBorrowInvariantObligations : Prop where
  writeBorrowTargets_preserves_containedBorrowsWellFormed
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets

/-- Remaining explicit proof obligation for Appendix 9.6 fan-out writes.

This statement is intentionally kept at the `WriteBorrowTargets` boundary rather
than decomposed into bare join landmarks: unconditional join preservation of
contained borrows is false without the cross-branch target/coherence premises
carried by the fan-out proof.
-/
theorem updateBorrowInvariant_writeBorrowTargets_preserves_containedBorrowsWellFormed
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets := by
  sorry

/-- Concrete update-invariant package assembled from the explicit fan-out debt. -/
theorem updateBorrowInvariantObligations_from_sorries :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed :=
    updateBorrowInvariant_writeBorrowTargets_preserves_containedBorrowsWellFormed

/-- Initialized-leaf fact for Appendix 9.6 fan-out writes.

Documented rule strengthening: `WriteBorrowTargets.singleton/cons` now carry a
full typing for the concrete branch target `prependPath path target`.  Without
that premise, the bare fan-out syntax could write through arbitrary partial
paths, including reinitialising `undef` leaves, so branch shape would not be
derivable.  With it, the existing matching lemma
`writeLeafTy_of_lvalTyping` supplies exactly the initialized-leaf witness needed
by `EnvWrite.shapePreserved_init` and `WriteBorrowTargets.shapePreserved_init`. -/
theorem WriteBorrowTargets.initialized_leaves_appendix96
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    WriteBorrowTargets rank env path targets rhsTy result →
    ∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy := by
  intro _htargets hwrites
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _rank env path targets rhsTy _result _ =>
      ∀ target, target ∈ targets → ∀ targetSlot,
        env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
        WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
  case nil =>
    intro rank env path ty target htarget
    simp at htarget
  case singleton =>
    intro rank env updated path target ty _hwrite htyped _ih selected hselected slot hslot
    rw [List.mem_singleton] at hselected
    subst hselected
    rcases htyped with ⟨leafTy, leafLifetime, htyping⟩
    have hleaf :=
      writeLeafTy_of_lvalTyping htyping hslot [] ty WriteLeafTy.leaf
    simpa using hleaf
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite htyped _hwrites _hjoin _ihWrite ihRest selected hselected slot hslot
    rcases List.mem_cons.mp hselected with hhead | htail
    · subst hhead
      rcases htyped with ⟨leafTy, leafLifetime, htyping⟩
      have hleaf :=
        writeLeafTy_of_lvalTyping htyping hslot [] ty WriteLeafTy.leaf
      simpa using hleaf
    · exact ihRest selected htail slot hslot
  case intro => intros; trivial

/--
`ContainedBorrowsWellFormedIn source observer` says that every borrow contained
in `source` has targets that are also well formed in `observer`, at the
containing slot's lifetime.

This is the cross-branch invariant needed by `writeBorrowTargets`: when two
branch environments are joined, contained borrows from one branch can be
validated in the joined environment only if their targets are available on the
other branch as well.
-/
def ContainedBorrowsWellFormedIn (source observer : Env) : Prop :=
  ∀ {x slot mutable targets},
    source.slotAt x = some slot →
    source ⊢ x ↝ Ty.borrow mutable targets →
    BorrowTargetsWellFormedInSlot observer slot.lifetime targets

/--
Join transport needed for Definition 4.8(i).

This is the lval-shaped part of the Appendix 9.6 join argument: if the same
borrow target is fully typed on both branches, and both typings live long
enough for the observer slot, then the joined environment also gives that
target a full type at a lifetime that still lives long enough.
-/
structure FullLValTypingJoinTransport : Prop where
  full
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftTy) leftLifetime →
    LValTyping right target (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join target (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure LValTargetsTypingJoinTransport : Prop where
  targets
    {left right join : Env} {targets : List LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTargetsTyping left targets (.ty leftTy) leftLifetime →
    LValTargetsTyping right targets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join targets (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure DerefLValTypingJoinTransport : Prop where
  deref
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.ty leftTy) leftLifetime →
    LValTyping right (.deref source) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure DerefLValTypingJoinTransportWithUnion : Prop where
  deref
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.ty leftTy) leftLifetime →
    LValTyping right (.deref source) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
          joinLifetime ≤ current

structure FullLValTypingJoinTransportWithUnion : Prop where
  full
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftTy) leftLifetime →
    LValTyping right target (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join target (.ty joinTy) joinLifetime ∧
          joinLifetime ≤ current

structure BoxFullLValTypingJoinTransport : Prop where
  boxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join source (.box (.ty joinTy)) joinLifetime ∧
        joinLifetime ≤ current

structure DerefBoxFullLValTypingJoinTransport : Prop where
  derefBoxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.box (.ty leftTy)) leftLifetime →
    LValTyping right (.deref source) (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.box (.ty joinTy)) joinLifetime ∧
        joinLifetime ≤ current

structure BoxBoxFullLValTypingJoinTransport : Prop where
  boxBoxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.box (.ty leftTy))) leftLifetime →
    LValTyping right source (.box (.box (.ty rightTy))) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join source (.box (.box (.ty joinTy))) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefBoxFullLValTypingJoinTransport.of_boxBoxFull
    (htransport : BoxBoxFullLValTypingJoinTransport) :
    DerefBoxFullLValTypingJoinTransport where
  derefBoxFull := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleft hright hleftOutlives hrightOutlives
    have hleftSource :
        LValTyping left source (.box (.box (.ty leftTy))) leftLifetime :=
      LValTyping.deref_box_full_inv hleft
    have hrightSource :
        LValTyping right source (.box (.box (.ty rightTy))) rightLifetime :=
      LValTyping.deref_box_full_inv hright
    rcases htransport.boxBoxFull hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftSource hrightSource
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, hjoinSource, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, LValTyping.box hjoinSource, hjoinOutlives⟩

theorem BoxFullLValTypingJoinTransport.of_derefBoxFull
    (hderef : DerefBoxFullLValTypingJoinTransport) :
    BoxFullLValTypingJoinTransport where
  boxFull := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleft hright hleftOutlives hrightOutlives
    cases source with
    | var x =>
        exact LValTyping.var_join_box_full_bounded hjoin hleft hright
          hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.derefBoxFull hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleft hright hleftOutlives hrightOutlives

structure DerefLValTypingJoinConstructorLandmarks : Prop where
  box_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  box_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {rightMutable : Bool} {rightTargets : List LVal}
    {leftLifetime rightBorrowLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftMutable : Bool} {leftTargets : List LVal}
    {leftBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty}
    {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal}
    {leftBorrowLifetime rightBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefLValTypingJoinConstructorLandmarks.box_box_of_boxFull
    (hbox : BoxFullLValTypingJoinTransport)
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright hleftOutlives hrightOutlives
  rcases hbox.boxFull hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hright hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, LValTyping.box hjoinTyping, hjoinOutlives⟩

theorem LValTyping.deref_borrow_from_aligned_targets
    {env : Env} {source : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime targetLifetime current : Lifetime} {targetTy : Ty} :
    LValTyping env source (.ty (.borrow mutable targets)) borrowLifetime →
    LValTargetsTyping env targets (.ty targetTy) targetLifetime →
    targetLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping env (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hborrow htargets houtlives
  exact ⟨targetTy, targetLifetime,
    LValTyping.borrow hborrow htargets,
    houtlives⟩

structure DerefLValTypingJoinConstructorSplitLandmarks : Prop where
  boxFull :
    BoxFullLValTypingJoinTransport
  box_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {rightMutable : Bool} {rightTargets : List LVal}
    {leftLifetime rightBorrowLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftMutable : Bool} {leftTargets : List LVal}
    {leftBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty}
    {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal}
    {leftBorrowLifetime rightBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefLValTypingJoinConstructorLandmarks.of_split
    (hlandmarks : DerefLValTypingJoinConstructorSplitLandmarks) :
    DerefLValTypingJoinConstructorLandmarks where
  box_box := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft hleft hright
      hleftOutlives hrightOutlives
    exact DerefLValTypingJoinConstructorLandmarks.box_box_of_boxFull
      hlandmarks.boxFull hjoin hleftContained hrightContained hleftInRight
      hrightInLeft hleft hright hleftOutlives hrightOutlives
  box_borrow := by
    intro left right join source leftTy rightTy rightMutable rightTargets
      leftLifetime rightBorrowLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleft hright hrightTargets
      hleftOutlives hrightOutlives
    exact hlandmarks.box_borrow hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hright hrightTargets
      hleftOutlives hrightOutlives
  borrow_box := by
    intro left right join source leftTy rightTy leftMutable leftTargets
      leftBorrowLifetime leftLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleft hleftTargets hright
      hleftOutlives hrightOutlives
    exact hlandmarks.borrow_box hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hleftTargets hright
      hleftOutlives hrightOutlives
  borrow_borrow := by
    intro left right join source leftTy rightTy leftMutable rightMutable
      leftTargets rightTargets leftBorrowLifetime rightBorrowLifetime leftLifetime
      rightLifetime current hjoin hleftContained hrightContained hleftInRight
      hrightInLeft hleft hleftTargets hright hrightTargets hleftOutlives
      hrightOutlives
    exact hlandmarks.borrow_borrow hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hleftTargets hright hrightTargets
      hleftOutlives hrightOutlives

theorem DerefLValTypingJoinTransport.of_constructorLandmarks
    (hlandmarks : DerefLValTypingJoinConstructorLandmarks) :
    DerefLValTypingJoinTransport where
  deref := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases hleftTyping with
    | box hleftSource =>
        cases hrightTyping with
        | box hrightSource =>
            exact hlandmarks.box_box hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hrightSource
              hleftOutlives hrightOutlives
        | borrow hrightSource hrightTargets =>
            exact hlandmarks.box_borrow hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hrightSource hrightTargets
              hleftOutlives hrightOutlives
    | borrow hleftSource hleftTargets =>
        cases hrightTyping with
        | box hrightSource =>
            exact hlandmarks.borrow_box hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hleftTargets hrightSource
              hleftOutlives hrightOutlives
        | borrow hrightSource hrightTargets =>
            exact hlandmarks.borrow_borrow hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hleftTargets hrightSource hrightTargets
              hleftOutlives hrightOutlives

theorem FullLValTypingJoinTransport.of_deref
    (hderef : DerefLValTypingJoinTransport) :
    FullLValTypingJoinTransport where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases target with
    | var x =>
        exact LValTyping.var_join_full_bounded hjoin hleftTyping hrightTyping
          hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.deref hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleftTyping hrightTyping
          hleftOutlives hrightOutlives

theorem DerefLValTypingJoinTransportWithUnion.to_deref
    (htransport : DerefLValTypingJoinTransportWithUnion) :
    DerefLValTypingJoinTransport where
  deref := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    rcases htransport.deref hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftTyping hrightTyping
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, _hunion, hjoinTyping, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩

theorem FullLValTypingJoinTransportWithUnion.to_full
    (htransport : FullLValTypingJoinTransportWithUnion) :
    FullLValTypingJoinTransport where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    rcases htransport.full hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftTyping hrightTyping
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, _hunion, hjoinTyping, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩

theorem FullLValTypingJoinTransportWithUnion.of_deref
    (hderef : DerefLValTypingJoinTransportWithUnion) :
    FullLValTypingJoinTransportWithUnion where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases target with
    | var x =>
        exact LValTyping.var_join_full_bounded_with_union hjoin
          hleftTyping hrightTyping hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.deref hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleftTyping hrightTyping
          hleftOutlives hrightOutlives

def BorrowTargetsTransport (source target : Env) : Prop :=
  ∀ {slotLifetime targets},
    BorrowTargetsWellFormedInSlot source slotLifetime targets →
    BorrowTargetsWellFormedInSlot target slotLifetime targets

@[refl] theorem BorrowTargetsTransport.refl (env : Env) :
    BorrowTargetsTransport env env := by
  intro slotLifetime targets htargets
  exact htargets

theorem BorrowTargetsTransport.trans {first second third : Env} :
    BorrowTargetsTransport first second →
    BorrowTargetsTransport second third →
    BorrowTargetsTransport first third := by
  intro hfirstSecond hsecondThird slotLifetime targets htargets
  exact hsecondThird (hfirstSecond htargets)

/-- Observer-target transport across a join via the runtime invariants
(one-directional: `source → left → join`).  Here `ContainedBorrows join` is
already established (the bootstrap runs first), so each transported target's
lifetime is bounded by the *unbounded*-strength invariant — packaged through the
rank-bounded `fullJoinTransport` with the per-target bound `N := φ(base t)+1` and
`hcontN` derived from the full `hcontJoin`. -/
theorem BorrowTargetsTransport.join_viaInvariants_left
    {source left right join : Env}
    (hjoin : EnvJoin left right join)
    (hstrL : ∀ x sE, left.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hlinJoin : Linearizable join) (hcohJoin : Coherent join)
    (hcontJoin : ContainedBorrowsWellFormed join)
    (hsourceLeft : BorrowTargetsTransport source left) :
    BorrowTargetsTransport source join := by
  obtain ⟨φ, hφJoin⟩ := hlinJoin
  intro slotLifetime targets htargets
  have hleft := hsourceLeft htargets
  intro target htarget
  rcases hleft target htarget with ⟨leftTy, leftLf, hleftTyping, _hleftOutlives, hleftBase⟩
  have hjoinBase := LValBaseOutlives.join_left hjoin hleftBase
  rcases fullJoinTransport_viaInvariants (N := φ (LVal.base target) + 1)
      hstrL hφJoin hcohJoin
      (fun x' slot' m' T' _ hslot' hcont' => hcontJoin x' slot' m' T' hslot' hcont')
      (Nat.lt_succ_self _) hleftTyping hjoinBase
    with ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives, hjoinBase⟩

theorem ContainedBorrowsWellFormedIn.of_transport {source observer : Env} :
    ContainedBorrowsWellFormed source →
    BorrowTargetsTransport source observer →
    ContainedBorrowsWellFormedIn source observer := by
  intro hcontained htransport x slot mutable targets hslot hcontains
  exact htransport (hcontained x slot mutable targets hslot hcontains)

theorem ContainedBorrowsWellFormed.in_self {env : Env} :
    ContainedBorrowsWellFormed env →
    ContainedBorrowsWellFormedIn env env := by
  intro hcontained x slot mutable targets hslot hcontains
  exact hcontained x slot mutable targets hslot hcontains

theorem LValTargetsTyping.join_full_singleton_of_fullLValTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTargetsTyping left [target] (.ty leftTy) leftLifetime →
    LValTargetsTyping right [target] (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join [target] (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleftTargets hrightTargets hleftOutlives hrightOutlives
  cases hleftTargets with
  | singleton hleft =>
      cases hrightTargets with
      | singleton hright =>
          rcases htransport.full hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleft hright
              hleftOutlives hrightOutlives with
            ⟨joinTy, joinLifetime, hjoinTarget, hjoinOutlives⟩
          exact ⟨joinTy, joinLifetime,
            LValTargetsTyping.singleton hjoinTarget, hjoinOutlives⟩
      | cons _hhead hrest _hunion _hintersection =>
          cases hrest
  | cons _hhead hrest _hunion _hintersection =>
      cases hrest

theorem LValTargetsTyping.join_full_cons_of_parts
    {join : Env} {target : LVal} {rest : List LVal}
    {headTy restTy unionTy : Ty}
    {headLifetime restLifetime lifetime current : Lifetime} :
    LValTyping join target (.ty headTy) headLifetime →
    LValTargetsTyping join rest (.ty restTy) restLifetime →
    PartialTyUnion (.ty headTy) (.ty restTy) (.ty unionTy) →
    LifetimeIntersection headLifetime restLifetime lifetime →
    lifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join (target :: rest) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hhead hrest hunion hintersection houtlives
  exact ⟨unionTy, lifetime,
    LValTargetsTyping.cons hhead hrest hunion hintersection,
    houtlives⟩

structure LValTargetsTypingJoinConsTypeUnionLandmark : Prop where
  typeUnion
    {left right join : Env} {target : LVal} {rest : List LVal}
    {leftHeadTy rightHeadTy leftRestTy rightRestTy leftTy rightTy : Ty}
    {joinHeadTy joinRestTy : Ty}
    {leftHeadLifetime rightHeadLifetime leftRestLifetime rightRestLifetime
      leftLifetime rightLifetime joinHeadLifetime joinRestLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftHeadTy) leftHeadLifetime →
    LValTyping right target (.ty rightHeadTy) rightHeadLifetime →
    LValTargetsTyping left rest (.ty leftRestTy) leftRestLifetime →
    LValTargetsTyping right rest (.ty rightRestTy) rightRestLifetime →
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty rightHeadTy) (.ty rightRestTy) (.ty rightTy) →
    LifetimeIntersection leftHeadLifetime leftRestLifetime leftLifetime →
    LifetimeIntersection rightHeadLifetime rightRestLifetime rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    LValTyping join target (.ty joinHeadTy) joinHeadLifetime →
    LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime →
    joinHeadLifetime ≤ current →
    joinRestLifetime ≤ current →
    ∃ joinTy, PartialTyUnion (.ty joinHeadTy) (.ty joinRestTy) (.ty joinTy)

structure LValTargetsTypingJoinConsLandmark : Prop where
  cons
    {left right join : Env} {target : LVal} {rest : List LVal}
    {leftHeadTy rightHeadTy leftRestTy rightRestTy leftTy rightTy : Ty}
    {leftHeadLifetime rightHeadLifetime leftRestLifetime rightRestLifetime
      leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftHeadTy) leftHeadLifetime →
    LValTyping right target (.ty rightHeadTy) rightHeadLifetime →
    LValTargetsTyping left rest (.ty leftRestTy) leftRestLifetime →
    LValTargetsTyping right rest (.ty rightRestTy) rightRestLifetime →
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty rightHeadTy) (.ty rightRestTy) (.ty rightTy) →
    LifetimeIntersection leftHeadLifetime leftRestLifetime leftLifetime →
    LifetimeIntersection rightHeadLifetime rightRestLifetime rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    (∃ joinHeadTy joinHeadLifetime,
      LValTyping join target (.ty joinHeadTy) joinHeadLifetime ∧
        joinHeadLifetime ≤ current) →
    (∃ joinRestTy joinRestLifetime,
      LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime ∧
        joinRestLifetime ≤ current) →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join (target :: rest) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem LValTargetsTypingJoinConsLandmark.of_typeUnion
    (htypeUnion : LValTargetsTypingJoinConsTypeUnionLandmark) :
    LValTargetsTypingJoinConsLandmark where
  cons := by
    intro left right join target rest leftHeadTy rightHeadTy leftRestTy rightRestTy
      leftTy rightTy leftHeadLifetime rightHeadLifetime leftRestLifetime
      rightRestLifetime leftLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleftHead hrightHead hleftRest
      hrightRest hleftUnion hrightUnion hleftIntersection hrightIntersection
      hleftOutlives hrightOutlives hjoinHead hjoinRest
    rcases hjoinHead with
      ⟨joinHeadTy, joinHeadLifetime, hjoinHeadTyping, hjoinHeadOutlives⟩
    rcases hjoinRest with
      ⟨joinRestTy, joinRestLifetime, hjoinRestTyping, hjoinRestOutlives⟩
    rcases htypeUnion.typeUnion hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftHead hrightHead hleftRest hrightRest
        hleftUnion hrightUnion hleftIntersection hrightIntersection
        hleftOutlives hrightOutlives hjoinHeadTyping hjoinRestTyping
        hjoinHeadOutlives hjoinRestOutlives with
      ⟨joinTy, hjoinUnion⟩
    rcases LifetimeIntersection.exists_of_common_inner
        hjoinHeadOutlives hjoinRestOutlives with
      ⟨joinLifetime, hjoinIntersection⟩
    exact LValTargetsTyping.join_full_cons_of_parts
      hjoinHeadTyping hjoinRestTyping hjoinUnion hjoinIntersection
      (LifetimeIntersection.le_of_le hjoinIntersection
        hjoinHeadOutlives hjoinRestOutlives)

theorem LValTargetsTypingJoinTransport.of_full_and_cons
    (hfull : FullLValTypingJoinTransport)
    (hcons : LValTargetsTypingJoinConsLandmark) :
    LValTargetsTypingJoinTransport := by
  constructor
  intro left right join targets leftTy rightTy leftLifetime rightLifetime current
    hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleftTargets hrightTargets hleftOutlives hrightOutlives
  induction targets generalizing leftTy rightTy leftLifetime rightLifetime current with
  | nil =>
      cases hleftTargets
  | cons target rest ih =>
      by_cases hrestNil : rest = []
      · subst hrestNil
        cases hleftTargets with
        | singleton hleftTarget =>
            cases hrightTargets with
            | singleton hrightTarget =>
                rcases hfull.full hjoin hleftContained hrightContained
                    hleftInRight hrightInLeft hleftTarget hrightTarget
                    hleftOutlives hrightOutlives with
                  ⟨joinTy, joinLifetime, hjoinTarget, hjoinOutlives⟩
                exact ⟨joinTy, joinLifetime,
                  LValTargetsTyping.singleton hjoinTarget, hjoinOutlives⟩
            | cons _hrightHead hrightRest _hrightUnion _hrightIntersection =>
                cases hrightRest
        | cons _hleftHead hleftRest _hleftUnion _hleftIntersection =>
            cases hleftRest
      · rcases LValTargetsTyping.cons_full_inv hrestNil hleftTargets with
          ⟨leftHeadTy, leftHeadLifetime, leftRestTy, leftRestLifetime,
            hleftHead, hleftRest, hleftUnion, hleftIntersection⟩
        rcases LValTargetsTyping.cons_full_inv hrestNil hrightTargets with
          ⟨rightHeadTy, rightHeadLifetime, rightRestTy, rightRestLifetime,
            hrightHead, hrightRest, hrightUnion, hrightIntersection⟩
        have hleftHeadOutlives : leftHeadLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.left_le hleftIntersection) hleftOutlives
        have hrightHeadOutlives : rightHeadLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.left_le hrightIntersection) hrightOutlives
        have hleftRestOutlives : leftRestLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.right_le hleftIntersection) hleftOutlives
        have hrightRestOutlives : rightRestLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.right_le hrightIntersection) hrightOutlives
        have hjoinHead :
            ∃ joinHeadTy joinHeadLifetime,
              LValTyping join target (.ty joinHeadTy) joinHeadLifetime ∧
                joinHeadLifetime ≤ current :=
          hfull.full hjoin hleftContained hrightContained hleftInRight
            hrightInLeft hleftHead hrightHead hleftHeadOutlives
            hrightHeadOutlives
        have hjoinRest :
            ∃ joinRestTy joinRestLifetime,
              LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime ∧
                joinRestLifetime ≤ current :=
          ih hleftRest hrightRest hleftRestOutlives hrightRestOutlives
        exact hcons.cons hjoin hleftContained hrightContained hleftInRight
          hrightInLeft hleftHead hrightHead hleftRest hrightRest
          hleftUnion hrightUnion hleftIntersection hrightIntersection
          hleftOutlives hrightOutlives hjoinHead hjoinRest

theorem BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {targets : List LVal}
    {slotLifetime : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright target htarget
  -- Per-target invariant: each target is typed in both branches; transport the
  -- single typing across the join via the single-lval full join transport.  No
  -- joint target-list typing of the merged list is needed, so the list-level
  -- cons-union landmark is no longer required here.
  rcases hleft target htarget with
    ⟨leftTy, leftLifetime, hleftTyping, hleftOutlives, hleftBase⟩
  rcases hright target htarget with
    ⟨rightTy, rightLifetime, hrightTyping, hrightOutlives, _hrightBase⟩
  rcases htransport.full hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleftTyping hrightTyping
      hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives,
    LValBaseOutlives.join_left hjoin hleftBase⟩

theorem EnvJoin.preserves_observerTargets_of_lvalTargetsTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {targets : List LVal}
    {slotLifetime : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport

theorem BorrowTargetsTransport.join_observer
    (htransport : FullLValTypingJoinTransport)
    {source left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsTransport source left →
    BorrowTargetsTransport source right →
    BorrowTargetsTransport source join := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright slotLifetime targets htargets
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport hjoin hleftContained hrightContained hleftInRight hrightInLeft
    (hleft htargets) (hright htargets)

theorem ContainedBorrowsWellFormedIn.join_observer
    (htransport : FullLValTypingJoinTransport)
    {source left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    ContainedBorrowsWellFormedIn source left →
    ContainedBorrowsWellFormedIn source right →
    ContainedBorrowsWellFormedIn source join := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright x slot mutable targets hslot hcontains
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport hjoin hleftContained hrightContained hleftInRight hrightInLeft
    (hleft hslot hcontains)
    (hright hslot hcontains)

theorem ContainedBorrowsWellFormedIn.join_source
    {left right join observer : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormedIn left observer →
    ContainedBorrowsWellFormedIn right observer →
    ContainedBorrowsWellFormedIn join observer := by
  intro hjoin hleft hright x joinSlot mutable targets hjoinSlot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq : containedSlot = joinSlot := by
    have hsomeEq : some containedSlot = some joinSlot := by
      rw [← hcontainedSlot, hjoinSlot]
    exact Option.some.inj hsomeEq
  have hcontainsJoin : PartialTyContains joinSlot.ty (.borrow mutable targets) := by
    simpa [hcontainedSlotEq] using hcontainsTy
  rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
    ⟨leftSlot, hleftSlot, _hleftLifetime⟩
  rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
    ⟨rightSlot, hrightSlot, _hrightLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨hleftLife, hrightLife, hunion⟩
  exact BorrowTargetsWellFormedInSlot.of_partialTyUnion
    (env := observer) (lifetime := joinSlot.lifetime) hunion
    (by
      intro leftMutable leftTargets hcontainsLeft
      have htargets :
          BorrowTargetsWellFormedInSlot observer leftSlot.lifetime leftTargets :=
        hleft hleftSlot ⟨leftSlot, hleftSlot, hcontainsLeft⟩
      simpa [hleftLife] using htargets)
    (by
      intro rightMutable rightTargets hcontainsRight
      have htargets :
          BorrowTargetsWellFormedInSlot observer rightSlot.lifetime rightTargets :=
        hright hrightSlot ⟨rightSlot, hrightSlot, hcontainsRight⟩
      simpa [hrightLife] using htargets)
    hcontainsJoin

/--
Branch-specific contained-borrow join preservation.

The unconditional statement "contained borrows are preserved by every
environment join" is too strong for partial environments: a borrow introduced
on one branch may have targets that are not fully typable on the other branch.
The `writeBorrowTargets` cons case supplies precisely the missing cross-branch
premises via its observer-target induction hypotheses.
-/
theorem ContainedBorrowsWellFormed.join_of_crossBranchTargets
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    ContainedBorrowsWellFormed join := by
  intro hjoin hleftContained hrightContained hleftTargetsRight hrightTargetsLeft
  exact ContainedBorrowsWellFormed.join_of_inSlot hjoin
    (by
      intro x slot mutable targets hslot hcontains
      exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
        htransport hjoin hleftContained hrightContained
        hleftTargetsRight hrightTargetsLeft
        (hleftContained x slot mutable targets hslot hcontains)
        (hleftTargetsRight hslot hcontains))
    (by
      intro x slot mutable targets hslot hcontains
      exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
        htransport hjoin hleftContained hrightContained
        hleftTargetsRight hrightTargetsLeft
        (hrightTargetsLeft hslot hcontains)
        (hrightContained x slot mutable targets hslot hcontains))

structure UpdateBorrowInvariantCrossLandmarks : Prop where
  envWrite_preserves_core
    {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env

/-- Rank side condition needed for preserving one common linearization witness
through a mutable-borrow fan-out.

For every concrete branch write, each *new borrow edge* whose target came from
the RHS type must point to a strictly lower-ranked base.  This is the local
acyclicity premise behind the old bare `EnvWrite.preserves_linearizedBy`
obligation. -/
def WriteBorrowTargetsRhsVarsBelowBranches (φ : Name → Nat) (rank : Nat)
    (env : Env) (path : Path) (writeTargets : List LVal) (rhsTy : Ty) : Prop :=
  ∀ target, target ∈ writeTargets → ∀ updated,
    EnvWrite rank env (prependPath path target) rhsTy updated →
    EnvWriteRhsBorrowTargetsBelow φ updated rhsTy

/-- Coherence obligations for every branch and branch join in a mutable-borrow
fan-out write.

This is the fan-out analogue of the strengthened assignment coherence premise.
Each concrete branch write must expose the write-coherence transport needed by
`EnvWrite.preserves_coherent_of_obligations`; each cons join must expose the
join-coherence transport needed by `EnvJoin.preserves_coherent_of_obligations`.
-/
structure WriteBorrowTargetsCoherenceObligations
    (rank : Nat) (env : Env) (path : Path) (writeTargets : List LVal)
    (rhsTy : Ty) : Prop where
  write
    (target : LVal) :
    target ∈ writeTargets →
    ∀ updated,
      EnvWrite rank env (prependPath path target) rhsTy updated →
      EnvWriteCoherenceObligations env updated (LVal.base (prependPath path target))
  join
    (target : LVal) (rest : List LVal) :
    target ∈ writeTargets →
    (∀ t, t ∈ rest → t ∈ writeTargets) →
    ∀ updated restEnv result,
      EnvWrite rank env (prependPath path target) rhsTy updated →
      WriteBorrowTargets rank env path rest rhsTy restEnv →
      EnvJoin updated restEnv result →
      EnvJoinCoherenceObligations updated restEnv result

/-- Constructive variant of `WriteBorrowTargets.preserves_core_of_crossLandmarks`
that does not use the bare `EnvWrite.preserves_linearizedBy` axiom.

The extra `WriteBorrowTargetsRhsVarsBelowBranches` premise is the small
borrow-inference/rank side condition needed to keep the same linearization witness
across every fan-out branch. -/
theorem WriteBorrowTargets.preserves_core_of_crossLandmarks
    (hlandmarks : UpdateBorrowInvariantCrossLandmarks)
    {rank : Nat} {env result : Env} {path : Path}
    {writeTargets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime}
    {φ : Name → Nat} :
    0 < rank →
    Coherent env →
    LinearizedBy φ env →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    (∀ target, target ∈ writeTargets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    WriteBorrowTargetsRhsVarsBelowBranches φ rank env path writeTargets rhsTy →
    WriteBorrowTargetsCoherenceObligations rank env path writeTargets rhsTy →
    WriteBorrowTargets rank env path writeTargets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro hrank hcoh hφ hcontained hrhs hleaf hbelow hfanoutCoh hwrites
  exact (WriteBorrowTargets.rec
    (motive_1 := fun _rank _env _path _oldTy _rhsTy _result _updatedTy _ =>
      True)
    (motive_2 := fun _rank env _path _writeTargets constructorTy result _ =>
      0 < _rank → Coherent env → LinearizedBy φ env →
      ∀ {slotLifetime},
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        (∀ target, target ∈ _writeTargets → ∀ targetSlot,
          env.slotAt (LVal.base (prependPath _path target)) = some targetSlot →
          WriteLeafTy env (LVal.path (prependPath _path target))
            targetSlot.ty constructorTy) →
        WriteBorrowTargetsRhsVarsBelowBranches φ _rank env _path _writeTargets constructorTy →
        WriteBorrowTargetsCoherenceObligations _rank env _path _writeTargets constructorTy →
        (ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env) ∧
          Coherent result ∧ LinearizedBy φ result)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by intro env old ty; trivial)
    (by intro env rank old joined ty _hshape _hjoin; trivial)
    (by intro env₁ env₂ rank path inner updatedInner ty hupdate ih; trivial)
    (by intro env₁ env₂ rank path targets ty hwrites ih; trivial)
    (by
      intro rank env path ty _hrank hcoh hlinBy slotLifetime hcontained _hrhs _hleaf
        _hbelow _hfanoutCoh
      exact ⟨⟨hcontained, BorrowTargetsTransport.refl env,
        ContainedBorrowsWellFormed.in_self hcontained⟩, hcoh, hlinBy⟩)
    (by
      intro rank env updated path target ty hwrite _htyped _ih
        hrank hcoh hlinBy slotLifetime hcontained hrhs _hleaf hbelow hfanoutCoh
      have hlinEnv : Linearizable env := Linearizable.of_linearizedBy hlinBy
      have hlinUBy :=
        EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
          hwrite hlinBy (hbelow target (by simp) updated hwrite)
      have hlinU := Linearizable.of_linearizedBy hlinUBy
      have hcohU := EnvWrite.preserves_coherent_of_obligations hcoh
        (hfanoutCoh.write target (by simp) updated hwrite)
      exact ⟨hlandmarks.envWrite_preserves_core hrank hcontained hrhs hwrite,
        hcohU, hlinUBy⟩)
    (by
      intro rank env updated restEnv result path target rest ty
        hwrite _htyped hwrites hjoin _ihWrite ihWrites
        hrank hcoh hlinBy slotLifetime hcontained hrhs hleaf hbelow hfanoutCoh
      have hlinEnv : Linearizable env := Linearizable.of_linearizedBy hlinBy
      have hlinUBy :=
        EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
          hwrite hlinBy (hbelow target (by simp) updated hwrite)
      have hlinU := Linearizable.of_linearizedBy hlinUBy
      have hcohU := EnvWrite.preserves_coherent_of_obligations hcoh
        (hfanoutCoh.write target (by simp) updated hwrite)
      rcases hlandmarks.envWrite_preserves_core hrank hcontained hrhs hwrite with
        ⟨hupdatedContained, hupdatedTransport, hupdatedInEnv⟩
      have hleafRest :
          ∀ t, t ∈ rest → ∀ slot,
            env.slotAt (LVal.base (prependPath path t)) = some slot →
            WriteLeafTy env (LVal.path (prependPath path t)) slot.ty ty := by
        intro t ht slot hslot
        exact hleaf t (List.mem_cons_of_mem target ht) slot hslot
      have hbelowRest :
          WriteBorrowTargetsRhsVarsBelowBranches φ rank env path rest ty := by
        intro t ht branch hbranch
        exact hbelow t (List.mem_cons_of_mem target ht) branch hbranch
      have hfanoutCohRest :
          WriteBorrowTargetsCoherenceObligations rank env path rest ty := {
        write := by
          intro t ht branch hbranch
          exact hfanoutCoh.write t (List.mem_cons_of_mem target ht) branch hbranch
        join := by
          intro t later ht hlater branch laterEnv branchResult hbranch hlaterWrites hbranchJoin
          exact hfanoutCoh.join t later (List.mem_cons_of_mem target ht)
            (fun u hu => List.mem_cons_of_mem target (hlater u hu))
            branch laterEnv branchResult hbranch hlaterWrites hbranchJoin
      }
      rcases ihWrites hrank hcoh hlinBy hcontained hrhs hleafRest hbelowRest
          hfanoutCohRest with
        ⟨⟨hrestContained, _hrestTransport, hrestInEnv⟩, hcohRest, hlinRestBy⟩
      have hlinRest := Linearizable.of_linearizedBy hlinRestBy
      have hlinRBy := EnvJoin.preserves_linearizedBy hjoin hlinUBy hlinRestBy
      have hlinR := Linearizable.of_linearizedBy hlinRBy
      have hjoinCoh : EnvJoinCoherenceObligations updated restEnv result :=
        hfanoutCoh.join target rest (by simp)
          (fun t ht => List.mem_cons_of_mem target ht)
          updated restEnv result hwrite hwrites hjoin
      have hcohR := EnvJoin.preserves_coherent_of_obligations hcohU hcohRest hjoinCoh
      have hupdShape : EnvShapePreserved env updated :=
        EnvWrite.shapePreserved_init hrank hwrite
          (fun slot hslot => hleaf target (by simp) slot hslot)
      have hrestShape : EnvShapePreserved env restEnv :=
        WriteBorrowTargets.shapePreserved_init hrank hwrites
          (fun t ht slot hslot =>
            hleaf t (List.mem_cons_of_mem target ht) slot hslot)
      have hbranch : ∀ x sL sR, updated.slotAt x = some sL → restEnv.slotAt x = some sR →
          PartialTy.sameShape sL.ty sR.ty :=
        EnvShapePreserved.branch_sameShape hupdShape hrestShape
      have hstrL := EnvJoin.fanOutShapeMap_left hjoin hbranch
      have hstrR := EnvJoin.fanOutShapeMap_right hjoin hbranch
      have hcontJoin :=
        ContainedBorrowsWellFormed.join_viaInvariants hjoin hstrL hstrR hlinR hcohR
          hupdatedContained hrestContained
      refine ⟨⟨hcontJoin,
        BorrowTargetsTransport.join_viaInvariants_left hjoin hstrL hlinR hcohR
          hcontJoin hupdatedTransport,
        ContainedBorrowsWellFormedIn.join_source hjoin hupdatedInEnv hrestInEnv⟩,
        hcohR, hlinRBy⟩)
    (by intro rank env₁ env₂ lv slot ty updatedTy hslot hupdate ih; trivial)
    hwrites hrank hcoh hφ hcontained hrhs hleaf hbelow hfanoutCoh).1

theorem UpdateBorrowInvariantObligations.of_crossLandmarks
    (hlandmarks : UpdateBorrowInvariantCrossLandmarks)
    (hfanoutRanked :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty} {φ : Name → Nat},
        WriteBorrowTargetsRhsVarsBelowBranches φ rank env path targets rhsTy)
    (hfanoutCoherence :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty},
        WriteBorrowTargetsCoherenceObligations rank env path targets rhsTy) :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed := by
    intro rank env result path targets rhsTy slotLifetime
      hrank hcoh hlin hcontained htargets hleaf hrhs hwrites
    rcases hlin with ⟨φ, hφ⟩
    rcases WriteBorrowTargets.preserves_core_of_crossLandmarks
        hlandmarks hrank hcoh hφ hcontained hrhs hleaf
        (hfanoutRanked (rank := rank) (env := env) (path := path)
          (targets := targets) (rhsTy := rhsTy) (φ := φ))
        (hfanoutCoherence (rank := rank) (env := env) (path := path)
          (targets := targets) (rhsTy := rhsTy))
        hwrites with
      ⟨hresultContained, htransport, _hresultInEnv⟩
    exact ⟨hresultContained, htransport htargets⟩

-- The deref-of-borrow join transport landmark (`borrow_borrow`, formerly the
-- `FullLValTypingJoinTransport` chain) is no longer needed: the write fan-out
-- driver (`WriteBorrowTargets.preserves_core_of_crossLandmarks`) now establishes
-- borrow-target join preservation directly and one-directionally via the
-- transport keystone (`ContainedBorrowsWellFormed.join_viaInvariants` etc.),
-- supplied with the runtime invariants `Coherent`/`Linearizable`.  The old
-- symmetric `FullLValTypingJoinTransport` structure and its consumers remain in
-- the file as dead (proven) scaffolding.

/-- Old borrow-target transport for one write, derived from the transport keystone.

This is one of the constructive pieces behind the legacy single-write Appendix
9.6 claim below.  It deliberately exposes the runtime facts the keystone needs:
the write result must be shape-preserving/strengthening from the source, already
linearized, coherent, and contained-borrow well formed.
-/
theorem EnvWrite.borrowTargetsTransport_of_shapeMap
    {rank : Nat} {env result : Env} {lv : LVal} {rhsTy : Ty}
    {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    BorrowTargetsTransport env result := by
  intro hwrite hshapeMap hlinResult hcohResult hcontainedResult
    slotLifetime targets htargets target htarget
  rcases htargets target htarget with
    ⟨sourceTy, sourceLifetime, hsourceTyping, hsourceOutlives, hsourceBase⟩
  have hresultBase : LValBaseOutlives result target slotLifetime :=
    LValBaseOutlives.write hwrite hsourceBase
  rcases fullJoinTransport_viaInvariants
      (source := env) (join := result) (target := target)
      (sourceTy := sourceTy) (sourceLifetime := sourceLifetime)
      (current := slotLifetime) (φ := φ) (N := φ (LVal.base target) + 1)
      hshapeMap hlinResult hcohResult
      (fun x slot mutable targets _hrank hslot hcontains =>
        hcontainedResult x slot mutable targets hslot hcontains)
      (Nat.lt_succ_self _) hsourceTyping hresultBase with
    ⟨resultTy, resultLifetime, hresultTyping, hresultOutlives⟩
  exact ⟨resultTy, resultLifetime, hresultTyping, hresultOutlives, hresultBase⟩

/-- Constructive packaging of the parts of the legacy single-write core claim
once the result-side invariants have been established separately.

The nontrivial old-target transport component is proved by
`EnvWrite.borrowTargetsTransport_of_shapeMap`; the two contained-borrow facts are
kept explicit because those are structural update obligations, not consequences
of a bare `EnvWrite` plus RHS well-formedness alone.
-/
theorem EnvWrite.preserves_core_appendix96_of_result_invariants
    {rank : Nat} {env result : Env} {lv : LVal} {rhsTy : Ty}
    {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    ContainedBorrowsWellFormedIn result env →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro hwrite hshapeMap hlinResult hcohResult hcontainedResult hresultInEnv
  exact ⟨hcontainedResult,
    EnvWrite.borrowTargetsTransport_of_shapeMap
      hwrite hshapeMap hlinResult hcohResult hcontainedResult,
    hresultInEnv⟩

/-- Appendix 9.6 core preservation for one positive-rank write, with the
result-side invariants exposed.

This is the proved replacement for the old bare claim.  A single `EnvWrite` plus
RHS per-target well-formedness is not enough to derive old-target transport; the
caller must also provide the shape map and result-side linearization/coherence
and contained-borrow facts needed by the transport keystone. -/
theorem EnvWrite.preserves_core_appendix96
    {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} {slotLifetime : Lifetime} {φ : Name → Nat} :
    0 < rank →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    ContainedBorrowsWellFormedIn result env →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro _hrank _hcontained _hrhs hwrite hshape hlinResult hcohResult
    hcontainedResult hresultInEnv
  exact EnvWrite.preserves_core_appendix96_of_result_invariants
    hwrite hshape hlinResult hcohResult hcontainedResult hresultInEnv

/-- Source environment for the bare Appendix 9.6 single-write counterexample.

Here `x : &[a]` with `a : int`, and `y : &[*x]`.  Thus `*x` is an old borrow
target that is well formed before the write.
-/
def coreAppendix96Env : Env :=
  (((Env.empty.update "a" { ty := .ty .int, lifetime := Lifetime.root }).update "b"
    { ty := .ty .unit, lifetime := Lifetime.root }).update "x"
      { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root }).update "y"
        { ty := .ty (.borrow false [.deref (.var "x")]), lifetime := Lifetime.root }

/-- Result of weakly writing `&[b]` into `x`, yielding `x : &[a,b]`. -/
def coreAppendix96Result : Env :=
  coreAppendix96Env.update "x"
    { ty := .ty (.borrow false [.var "a", .var "b"]), lifetime := Lifetime.root }

theorem coreAppendix96Env_deref_x_typing :
    LValTyping coreAppendix96Env (.deref (.var "x")) (.ty .int) Lifetime.root := by
  have hx : coreAppendix96Env.slotAt "x" =
      some { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
    simp [coreAppendix96Env, Env.update]
  have ha : coreAppendix96Env.slotAt "a" =
      some { ty := .ty .int, lifetime := Lifetime.root } := by
    simp [coreAppendix96Env, Env.update]
  exact LValTyping.borrow (LValTyping.var hx)
    (LValTargetsTyping.singleton (LValTyping.var ha))

theorem coreAppendix96Result_targets_not_typeable :
    ¬ ∃ ty lifetime,
      LValTargetsTyping coreAppendix96Result [.var "a", .var "b"] (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htargets⟩
  cases htargets with
  | cons hhead hrest hunion _hintersection =>
      rcases LValTyping.var_inv hhead with ⟨headSlot, hheadSlot, hheadTy, _⟩
      have hheadSlotEq : headSlot = { ty := .ty .int, lifetime := Lifetime.root } := by
        have ha : coreAppendix96Result.slotAt "a" =
            some { ty := .ty .int, lifetime := Lifetime.root } := by
          simp [coreAppendix96Result, coreAppendix96Env, Env.update]
        exact Option.some.inj (by rw [← hheadSlot, ha])
      have hheadSlotTy : headSlot.ty = .ty .int := by
        rw [hheadSlotEq]
      cases hrest with
      | singleton htarget =>
          rcases LValTyping.var_inv htarget with ⟨restSlot, hrestSlot, hrestTy, _⟩
          have hrestSlotEq : restSlot = { ty := .ty .unit, lifetime := Lifetime.root } := by
            have hb : coreAppendix96Result.slotAt "b" =
                some { ty := .ty .unit, lifetime := Lifetime.root } := by
              simp [coreAppendix96Result, coreAppendix96Env, Env.update]
            exact Option.some.inj (by rw [← hrestSlot, hb])
          have hrestSlotTy : restSlot.ty = .ty .unit := by
            rw [hrestSlotEq]
          have hheadTyPartialEq : PartialTy.ty _ = PartialTy.ty Ty.int :=
            hheadTy.symm.trans hheadSlotTy
          have hrestTyPartialEq : PartialTy.ty _ = PartialTy.ty Ty.unit :=
            hrestTy.symm.trans hrestSlotTy
          cases hheadTyPartialEq
          cases hrestTyPartialEq
          exact PartialTyUnion.int_unit_full_false hunion
      | cons _hhead2 hrest2 _hunion2 _hintersection2 =>
          exact False.elim (LValTargetsTyping.nil_false hrest2)

theorem coreAppendix96Result_deref_x_not_typeable :
    ¬ ∃ ty lifetime,
      LValTyping coreAppendix96Result (.deref (.var "x")) (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htyping⟩
  cases htyping with
  | box hsource =>
      rcases LValTyping.var_inv hsource with ⟨slot, hslot, hty, _⟩
      have hslotTy : slot.ty = .ty (.borrow false [.var "a", .var "b"]) := by
        simpa [coreAppendix96Result, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      cases hty.symm.trans hslotTy
  | borrow hsource htargets =>
      rcases LValTyping.var_inv hsource with ⟨slot, hslot, hty, _⟩
      have hslotTy : slot.ty = .ty (.borrow false [.var "a", .var "b"]) := by
        simpa [coreAppendix96Result, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      have hsourceTy : PartialTy.ty (.borrow _ _) =
          PartialTy.ty (.borrow false [.var "a", .var "b"]) := hty.symm.trans hslotTy
      cases hsourceTy
      exact coreAppendix96Result_targets_not_typeable ⟨ty, lifetime, htargets⟩

theorem coreAppendix96Env_contained :
    ContainedBorrowsWellFormed coreAppendix96Env := by
  intro z slot mutable targets hslot hcontains
  by_cases hzy : z = "y"
  · subst hzy
    have hslotEq : slot =
        { ty := .ty (.borrow false [.deref (.var "x")]), lifetime := Lifetime.root } := by
      have hy : coreAppendix96Env.slotAt "y" =
          some { ty := .ty (.borrow false [.deref (.var "x")]), lifetime := Lifetime.root } := by
        simp [coreAppendix96Env, Env.update]
      exact Option.some.inj (by rw [← hslot, hy])
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hcontainedTy : containedSlot.ty = .ty (.borrow false [.deref (.var "x")]) := by
      simpa [coreAppendix96Env, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hcontainedSlot).symm
    rw [hcontainedTy] at hcontainsTy
    cases hcontainsTy
    subst hslotEq
    intro target htarget
    simp at htarget
    subst htarget
    refine ⟨.int, Lifetime.root, coreAppendix96Env_deref_x_typing,
      LifetimeOutlives.refl _, ?_⟩
    have hx : coreAppendix96Env.slotAt "x" =
        some { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
      simp [coreAppendix96Env, Env.update]
    exact ⟨_, hx, LifetimeOutlives.refl _⟩
  · by_cases hzx : z = "x"
    · subst hzx
      have hslotEq : slot =
          { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
        have hx : coreAppendix96Env.slotAt "x" =
            some { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
          simp [coreAppendix96Env, Env.update]
        exact Option.some.inj (by rw [← hslot, hx])
      rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hcontainedTy : containedSlot.ty = .ty (.borrow false [.var "a"]) := by
        simpa [coreAppendix96Env, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hcontainedSlot).symm
      rw [hcontainedTy] at hcontainsTy
      cases hcontainsTy
      subst hslotEq
      intro target htarget
      simp at htarget
      subst htarget
      have ha : coreAppendix96Env.slotAt "a" =
          some { ty := .ty .int, lifetime := Lifetime.root } := by
        simp [coreAppendix96Env, Env.update]
      exact ⟨.int, Lifetime.root, LValTyping.var ha,
        LifetimeOutlives.refl _, ⟨_, ha, LifetimeOutlives.refl _⟩⟩
    · by_cases hzb : z = "b"
      · subst hzb
        rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
        have hcontainedTy : containedSlot.ty = .ty .unit := by
          simpa [coreAppendix96Env, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hcontainedSlot).symm
        rw [hcontainedTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hza : z = "a"
        · subst hza
          rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
          have hcontainedTy : containedSlot.ty = .ty .int := by
            simpa [coreAppendix96Env, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hcontainedSlot).symm
          rw [hcontainedTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : coreAppendix96Env.slotAt z = none := by
            simp [coreAppendix96Env, Env.update, Env.empty, hzy, hzx, hzb, hza]
          rw [hslot] at hnone
          cases hnone

theorem coreAppendix96_rhs_wellFormed :
    PartialTyBorrowsWellFormedInSlot coreAppendix96Env Lifetime.root
      (.ty (.borrow false [.var "b"])) := by
  intro mutable targets hcontains
  cases hcontains
  intro target htarget
  simp at htarget
  subst htarget
  have hb : coreAppendix96Env.slotAt "b" =
      some { ty := .ty .unit, lifetime := Lifetime.root } := by
    simp [coreAppendix96Env, Env.update]
  exact ⟨.unit, Lifetime.root, LValTyping.var hb,
    LifetimeOutlives.refl _, ⟨_, hb, LifetimeOutlives.refl _⟩⟩

theorem coreAppendix96_bad_weak_shape_incompatible :
    ¬ ShapeCompatible coreAppendix96Env
      (.ty (.borrow false [.var "a"])) (.ty (.borrow false [.var "b"])) := by
  intro hshape
  cases hshape with
  | borrow hleft hright hpointee =>
      rcases hleft (.var "a") (by simp) with ⟨leftLifetime, hleftTyping⟩
      rcases hright (.var "b") (by simp) with ⟨rightLifetime, hrightTyping⟩
      rcases LValTyping.var_inv hleftTyping with ⟨leftSlot, hleftSlot, hleftTy, _⟩
      rcases LValTyping.var_inv hrightTyping with ⟨rightSlot, hrightSlot, hrightTy, _⟩
      have hleftSlotTy : leftSlot.ty = .ty .int := by
        simpa [coreAppendix96Env, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hleftSlot).symm
      have hrightSlotTy : rightSlot.ty = .ty .unit := by
        simpa [coreAppendix96Env, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hrightSlot).symm
      have hleftTyEq : PartialTy.ty _ = PartialTy.ty Ty.int :=
        hleftTy.symm.trans hleftSlotTy
      have hrightTyEq : PartialTy.ty _ = PartialTy.ty Ty.unit :=
        hrightTy.symm.trans hrightSlotTy
      cases hleftTyEq
      cases hrightTyEq
      cases hpointee

theorem coreAppendix96Env_deref_x_targets :
    BorrowTargetsWellFormedInSlot coreAppendix96Env Lifetime.root [.deref (.var "x")] := by
  intro target htarget
  simp at htarget
  subst htarget
  refine ⟨.int, Lifetime.root, coreAppendix96Env_deref_x_typing,
    LifetimeOutlives.refl _, ?_⟩
  have hx : coreAppendix96Env.slotAt "x" =
      some { ty := .ty (.borrow false [.var "a"]), lifetime := Lifetime.root } := by
    simp [coreAppendix96Env, Env.update]
  exact ⟨_, hx, LifetimeOutlives.refl _⟩

theorem coreAppendix96_transport_fails :
    ¬ BorrowTargetsTransport coreAppendix96Env coreAppendix96Result := by
  intro htransport
  have hresultTargets := htransport coreAppendix96Env_deref_x_targets
  rcases hresultTargets (.deref (.var "x")) (by simp) with
    ⟨targetTy, targetLifetime, htyping, _houtlives, _hbase⟩
  exact coreAppendix96Result_deref_x_not_typeable ⟨targetTy, targetLifetime, htyping⟩

/-- The pre-strengthening Appendix 9.6 counterexample is now rejected locally.

The old weak rule could merge `x : &[a]` with RHS `&[b]`, producing `x :
&[a,b]` and invalidating the old target `*x`.  The strengthened `W-Weak` rule
requires the local `ShapeCompatible` premise, and the theorem above proves that
premise is false in this example.
-/
theorem EnvWrite.preserves_core_appendix96_counterexample_rejected :
    ¬ ShapeCompatible coreAppendix96Env
      (.ty (.borrow false [.var "a"])) (.ty (.borrow false [.var "b"])) :=
  coreAppendix96_bad_weak_shape_incompatible

/-- Legacy packaging of Appendix 9.6 cross-landmarks.

The broad single-write field is no longer hidden behind an axiom.  Older callers
that still want this package must provide that compatibility premise explicitly;
the proved replacement is `EnvWrite.preserves_core_appendix96`, whose statement
exposes the result-side invariants needed for old-target transport.
-/
theorem updateBorrowInvariantCrossLandmarks_appendix96
    (hwriteCore :
      ∀ {rank : Nat} {env result : Env} {lv : LVal}
        {rhsTy : Ty} {slotLifetime : Lifetime},
        0 < rank →
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
        EnvWrite rank env lv rhsTy result →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env) :
    UpdateBorrowInvariantCrossLandmarks where
  envWrite_preserves_core := by
    intro rank env result lv rhsTy slotLifetime hrank hcontained hrhs hwrite
    exact hwriteCore hrank hcontained hrhs hwrite

structure UpdateBorrowInvariantLandmarks : Prop where
  envWrite_preserves_observerTargets
    {rank : Nat} {env result : Env} {lv : LVal}
    {observerTargets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime observerTargets
  envJoin_preserves_containedBorrowsWellFormed
    {left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormed join
  envJoin_preserves_observerTargets
    {left right join : Env} {targets : List LVal} {slotLifetime : Lifetime} :
    EnvJoin left right join →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets

theorem WriteBorrowTargets.preserves_observerTargets_of_landmarks
    (hlandmarks : UpdateBorrowInvariantLandmarks)
    {rank : Nat} {env result : Env} {path : Path}
    {writeTargets observerTargets : List LVal} {rhsTy : Ty}
    {slotLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path writeTargets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime observerTargets := by
  intro hcontained hobservers hrhs hwrites
  exact WriteBorrowTargets.rec
    (motive_1 := fun _rank _env _path _oldTy _rhsTy _result _updatedTy _ =>
      True)
    (motive_2 := fun _rank env _path _writeTargets constructorTy result _ =>
      ∀ {observerTargets slotLifetime},
        ContainedBorrowsWellFormed env →
        BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsWellFormedInSlot result slotLifetime observerTargets)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by
      intro env old ty
      trivial)
    (by
      intro env rank old joined ty _hshape _hjoin
      trivial)
    (by
      intro env₁ env₂ rank path inner updatedInner ty hupdate ih
      trivial)
    (by
      intro env₁ env₂ rank path targets ty hwrites ih
      trivial)
    (by
      intro rank env path ty observerTargets slotLifetime hcontained hobservers _hrhs
      exact ⟨hcontained, hobservers⟩)
    (by
      intro rank env updated path target ty hwrite _htyped _ih
        observerTargets slotLifetime hcontained hobservers hrhs
      exact hlandmarks.envWrite_preserves_observerTargets
        hcontained hobservers hrhs hwrite)
    (by
      intro rank env updated restEnv result path target rest ty
        hwrite _htyped _hwrites hjoin _ihWrite ihWrites
        observerTargets slotLifetime hcontained hobservers hrhs
      rcases hlandmarks.envWrite_preserves_observerTargets
          hcontained hobservers hrhs hwrite with
        ⟨hupdatedContained, hupdatedObservers⟩
      rcases ihWrites hcontained hobservers hrhs with
        ⟨hrestContained, hrestObservers⟩
      exact ⟨
        hlandmarks.envJoin_preserves_containedBorrowsWellFormed
          hjoin hupdatedContained hrestContained,
        hlandmarks.envJoin_preserves_observerTargets hjoin
          hupdatedObservers hrestObservers⟩)
    (by
      intro rank env₁ env₂ lv slot ty updatedTy hslot hupdate ih
      trivial)
    hwrites hcontained hobservers hrhs

theorem UpdateBorrowInvariantObligations.of_landmarks
    (hlandmarks : UpdateBorrowInvariantLandmarks) :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed := by
    intro rank env result path targets rhsTy slotLifetime
      _hrank _hcoh _hlin hcontained htargets _hleaf hrhs hwrites
    exact WriteBorrowTargets.preserves_observerTargets_of_landmarks
      hlandmarks hcontained htargets hrhs hwrites

/--
Definition 3.23 `writeBorrowTargets` borrow-invariant obligation.

This is the remaining paper-level update invariant needed by Lemma 4.9.  The
legacy theorem `updateBorrowInvariantObligations_appendix96` below records the
old Appendix 9.6 target as explicit result-side rank/coherence premises rather
than hiding them as axioms.
-/
theorem WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets := by
  exact hobligations.writeBorrowTargets_preserves_containedBorrowsWellFormed

/-- Appendix Lemma 9.6 package for the borrow-target fan-out.

This is an obligation-parametric compatibility route: the broad write-core and
fan-out rank/coherence facts are explicit premises until the remaining
result-side update obligations are proved constructively.
-/
theorem updateBorrowInvariantObligations_appendix96
    (hwriteCore :
      ∀ {rank : Nat} {env result : Env} {lv : LVal}
        {rhsTy : Ty} {slotLifetime : Lifetime},
        0 < rank →
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
        EnvWrite rank env lv rhsTy result →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env)
    (hfanoutRanked :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty} {φ : Name → Nat},
        WriteBorrowTargetsRhsVarsBelowBranches φ rank env path targets rhsTy)
    (hfanoutCoherence :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty},
        WriteBorrowTargetsCoherenceObligations rank env path targets rhsTy) :
    UpdateBorrowInvariantObligations := by
  exact UpdateBorrowInvariantObligations.of_crossLandmarks
    (updateBorrowInvariantCrossLandmarks_appendix96 hwriteCore)
    hfanoutRanked hfanoutCoherence

/--
Appendix Lemma 9.6 at the Definition 3.23 update-relation level.

The statement tracks both components needed by the enclosing `write` rule:
the intermediate environment remains contained-borrow well formed, and the
partial type returned by `update_k` has well-formed contained borrows at the
allocation lifetime of the slot being rebuilt.
-/
theorem UpdateAtPath.preserves_containedBorrowsWellFormed_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {rank : Nat} {env result : Env} {path : Path}
    {oldTy updatedTy : PartialTy} {rhsTy : Ty} {slotLifetime : Lifetime} :
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime oldTy →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    UpdateAtPath rank env path oldTy rhsTy result updatedTy →
    ContainedBorrowsWellFormed result ∧
      PartialTyBorrowsWellFormedInSlot result slotLifetime updatedTy := by
  intro hcoh hlin hcontained holdTy hrhsTy hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun _rank env _path oldTy constructorTy result updatedTy _ =>
      Coherent env → Linearizable env →
      ∀ {slotLifetime},
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime oldTy →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        ContainedBorrowsWellFormed result ∧
          PartialTyBorrowsWellFormedInSlot result slotLifetime updatedTy)
    (motive_2 := fun _rank _env _path _targets _rhsTy _result _ => True)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by
      intro env old ty hcoh hlin slotLifetime hcontained _holdTy hrhsTy
      exact ⟨hcontained, hrhsTy⟩)
    (by
      intro env rank old joined ty _hshape hjoin hcoh hlin slotLifetime hcontained holdTy hrhsTy
      exact ⟨hcontained,
        PartialTyBorrowsWellFormedInSlot.of_partialTyUnion
          (by simpa [PartialTyUnion] using hjoin) holdTy hrhsTy⟩)
    (by
      intro env₁ env₂ rank path inner updatedInner ty _hinner ih
        hcoh hlin slotLifetime hcontained holdTy hrhsTy
      rcases ih hcoh hlin hcontained
          (PartialTyBorrowsWellFormedInSlot.box_inv holdTy)
          hrhsTy with
        ⟨hcontainedResult, hupdatedInner⟩
      exact ⟨hcontainedResult, PartialTyBorrowsWellFormedInSlot.box hupdatedInner⟩)
    (by
      intro env₁ env₂ rank path targets ty hwrites _ih
        hcoh hlin slotLifetime hcontained holdTy hrhsTy
      have htargets :
          BorrowTargetsWellFormedInSlot env₁ slotLifetime targets :=
        holdTy PartialTyContains.here
      have htargetLeaves :
          ∀ target, target ∈ targets → ∀ targetSlot,
            env₁.slotAt (LVal.base (prependPath path target)) = some targetSlot →
            WriteLeafTy env₁ (LVal.path (prependPath path target)) targetSlot.ty ty :=
        WriteBorrowTargets.initialized_leaves_appendix96 htargets hwrites
      rcases WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
          hobligations (Nat.succ_pos rank) hcoh hlin hcontained htargets htargetLeaves
          hrhsTy hwrites with
        ⟨hcontainedResult, htargetsResult⟩
      exact ⟨hcontainedResult, by
        intro mutable selected hcontains
        cases hcontains
        exact htargetsResult⟩)
    (by
      intro rank env path ty
      trivial)
    (by
      intro rank env updated path target ty _hwrite _ih
      trivial)
    (by
      intro rank env updated restEnv result path target rest ty
        _hwrite _hwrites _hjoin _ihWrite _ihWrites
      trivial)
    (by
      intro rank env₁ env₂ lv slot ty updatedTy _hslot _hupdate _ih
      trivial)
    hupdate hcoh hlin hcontained holdTy hrhsTy

/--
Appendix Lemma 9.6, `W-Box` branch of Definition 3.23.

Updating through an owned box recursively updates the boxed partial type, then
replaces the original base slot with `.box updatedInner`.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_box_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ writeEnv env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {inner updatedInner oldTy : PartialTy}
    {rhs : Term} {rhsTy : Ty} {writeSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    env₂.slotAt (LVal.base lhs) = some writeSlot →
    writeSlot.ty = .box inner →
    UpdateAtPath 0 env₂ (LVal.path lhs) inner rhsTy writeEnv updatedInner →
    env₃ = writeEnv.update (LVal.base lhs)
      { writeSlot with ty := .box updatedInner } →
    ¬ WriteProhibited env₃ (.deref lhs) →
    ContainedBorrowsWellFormed env₃ := by
  intro hwellInitial hwellFormed hLhs _htargetLifetime hRhs _hshape hwellRhs
    hwriteSlot hwriteTy hinnerUpdate henv₃ hnotWrite
  subst henv₃
  have htargetOutlivesSlot :
      targetLifetime ≤ writeSlot.lifetime :=
    TermTyping.target_lifetime_outlives_surviving_base_slot
      hwellInitial hLhs hRhs (by simpa [LVal.base] using hwriteSlot)
  have hslotPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime writeSlot.ty :=
    ContainedBorrowsWellFormed.slot_partial hwellFormed.1 hwriteSlot
  have hinnerPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime inner := by
    rw [hwriteTy] at hslotPartial
    exact PartialTyBorrowsWellFormedInSlot.box_inv hslotPartial
  have hrhsPartialAtTarget :
      PartialTyBorrowsWellFormedInSlot env₂ targetLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellRhs
  have hrhsPartialAtSlot :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.weaken
      hrhsPartialAtTarget htargetOutlivesSlot
  rcases UpdateAtPath.preserves_containedBorrowsWellFormed_appendix96
      hobligations hwellFormed.2.2.1 hwellFormed.2.2.2 hwellFormed.1 hinnerPartial
      hrhsPartialAtSlot hinnerUpdate with
    ⟨hcontainedWriteEnv, hupdatedInnerPartial⟩
  have hnotWriteVar :
      ¬ WriteProhibited
        (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
        (.var (LVal.base lhs)) := by
    exact not_writeProhibited_var_base hnotWrite
  have hslotTargets :
      PartialTyBorrowsWellFormedInSlot
        (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
        writeSlot.lifetime
        ({ writeSlot with ty := .box updatedInner }).ty := by
    change PartialTyBorrowsWellFormedInSlot
      (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
      writeSlot.lifetime
      (.box updatedInner)
    have hboxedPartial :
        PartialTyBorrowsWellFormedInSlot writeEnv writeSlot.lifetime
          (.box updatedInner) :=
      PartialTyBorrowsWellFormedInSlot.box hupdatedInnerPartial
    intro mutable targets hcontains
    have htransported :
        PartialTyBorrowsWellFormedInSlot
          (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
          writeSlot.lifetime
          (.box updatedInner) :=
      PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts
        (x := LVal.base lhs)
        (slot := { writeSlot with ty := .box updatedInner })
        (partialTy := .box updatedInner)
        hnotWriteVar
        hboxedPartial
        (by
          intro mutable targets hcontains target htarget
          have hcontainsUpdated :
              (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner }) ⊢
                LVal.base lhs ↝ Ty.borrow mutable targets :=
            ⟨{ writeSlot with ty := .box updatedInner },
              by simp [Env.update],
              hcontains⟩
          exact not_pathConflicts_of_not_writeProhibited_contains
            hnotWriteVar hcontainsUpdated htarget)
    exact htransported hcontains
  exact ContainedBorrowsWellFormed.update_slot
    hcontainedWriteEnv hslotTargets hnotWriteVar

/--
Appendix Lemma 9.6, `W-MutB` branch of Definition 3.23.

Updating through a mutable borrow writes every possible borrowed target at
`rank + 1` and joins the resulting environments.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_mutBorrow_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {targets : List LVal} {oldTy : PartialTy}
    {rhs : Term} {rhsTy : Ty} {writeSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    env₂.slotAt (LVal.base lhs) = some writeSlot →
    writeSlot.ty = .ty (.borrow true targets) →
    WriteBorrowTargets 1 env₂ (LVal.path lhs) targets rhsTy env₃ →
    ¬ WriteProhibited
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
      (.deref lhs) →
    ContainedBorrowsWellFormed
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) }) := by
  intro hwellInitial hwellFormed hLhs _htargetLifetime hRhs _hshape hwellRhs
    hwriteSlot hwriteTy hwrites hnotWrite
  have htargetOutlivesSlot :
      targetLifetime ≤ writeSlot.lifetime :=
    TermTyping.target_lifetime_outlives_surviving_base_slot
      hwellInitial hLhs hRhs (by simpa [LVal.base] using hwriteSlot)
  have hslotPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime writeSlot.ty :=
    ContainedBorrowsWellFormed.slot_partial hwellFormed.1 hwriteSlot
  have htargetsOld :
      BorrowTargetsWellFormedInSlot env₂ writeSlot.lifetime targets := by
    rw [hwriteTy] at hslotPartial
    exact hslotPartial PartialTyContains.here
  have hrhsPartialAtTarget :
      PartialTyBorrowsWellFormedInSlot env₂ targetLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellRhs
  have hrhsPartialAtSlot :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.weaken
      hrhsPartialAtTarget htargetOutlivesSlot
  have htargetLeaves :
      ∀ target, target ∈ targets → ∀ targetSlot,
        env₂.slotAt (LVal.base (prependPath (LVal.path lhs) target)) = some targetSlot →
        WriteLeafTy env₂ (LVal.path (prependPath (LVal.path lhs) target))
          targetSlot.ty rhsTy :=
    WriteBorrowTargets.initialized_leaves_appendix96 htargetsOld hwrites
  rcases WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
      hobligations (by decide : 0 < 1) hwellFormed.2.2.1 hwellFormed.2.2.2
        hwellFormed.1 htargetsOld htargetLeaves hrhsPartialAtSlot hwrites with
    ⟨hcontainedWriteEnv, htargetsResult⟩
  have hnotWriteVar :
      ¬ WriteProhibited
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        (.var (LVal.base lhs)) := by
    exact not_writeProhibited_var_base hnotWrite
  have htargetsFinal :
      BorrowTargetsWellFormedInSlot
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        writeSlot.lifetime targets :=
    BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
      (x := LVal.base lhs)
      (slot := { writeSlot with ty := .ty (.borrow true targets) })
      hnotWriteVar
      htargetsResult
      (by
        intro target htarget
        have hcontainsUpdated :
            (env₃.update (LVal.base lhs)
              { writeSlot with ty := .ty (.borrow true targets) }) ⊢
              LVal.base lhs ↝ Ty.borrow true targets :=
          ⟨{ writeSlot with ty := .ty (.borrow true targets) },
            by simp [Env.update],
            PartialTyContains.here⟩
        exact not_pathConflicts_of_not_writeProhibited_contains
          hnotWriteVar hcontainsUpdated htarget)
  have hslotTargets :
      PartialTyBorrowsWellFormedInSlot
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        writeSlot.lifetime
        ({ writeSlot with ty := .ty (.borrow true targets) }).ty := by
    change PartialTyBorrowsWellFormedInSlot
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
      writeSlot.lifetime
      (.ty (.borrow true targets))
    intro mutable selected hcontains
    cases hcontains
    exact htargetsFinal
  exact ContainedBorrowsWellFormed.update_slot
    hcontainedWriteEnv hslotTargets hnotWriteVar

/--
Appendix Lemma 9.6, dereference/update component.

This is the part that needs the mutual induction over Definition 3.23:
`W-Box` recurses into the path, while `W-MutB` switches to
`writeBorrowTargets` and uses the environment-join borrow invariant.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ (.deref lhs) rhsTy env₃ →
    ¬ WriteProhibited env₃ (.deref lhs) →
    ContainedBorrowsWellFormed env₃ := by
  intro hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  cases hwrite with
  | intro hwriteSlot hupdate =>
      rename_i writeEnv writeSlot updatedTy
      simp [LVal.base] at hwriteSlot
      have hupdateCons :
          UpdateAtPath 0 env₂ (() :: LVal.path lhs) writeSlot.ty rhsTy
            writeEnv updatedTy := by
        simpa [LVal.path_deref_cons] using hupdate
      rcases UpdateAtPath.cons_inv hupdateCons with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, hwriteTy, hupdatedTy, hinnerUpdate⟩
        have hnotWriteBox :
            ¬ WriteProhibited
              (writeEnv.update (LVal.base lhs)
                { writeSlot with ty := .box updatedInner })
              (.deref lhs) := by
          simpa [LVal.base, hupdatedTy] using hnotWrite
        simpa [LVal.base, hupdatedTy] using
          EnvWrite.preserves_containedBorrowsWellFormed_deref_box_appendix96
            hobligations
            (lhs := lhs)
            hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
            hwriteSlot hwriteTy hinnerUpdate rfl hnotWriteBox
      · rcases hborrow with ⟨targets, hwriteTy, hupdatedTy, hwrites⟩
        have hwritesOne :
            WriteBorrowTargets 1 env₂ (LVal.path lhs) targets rhsTy writeEnv := by
          simpa using hwrites
        have hnotWriteBorrow :
            ¬ WriteProhibited
              (writeEnv.update (LVal.base lhs)
                { writeSlot with ty := .ty (.borrow true targets) })
              (.deref lhs) := by
          simpa [LVal.base, hupdatedTy] using hnotWrite
        simpa [LVal.base, hupdatedTy] using
          EnvWrite.preserves_containedBorrowsWellFormed_deref_mutBorrow_appendix96
            hobligations
            (lhs := lhs)
            hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
            hwriteSlot hwriteTy hwritesOne hnotWriteBorrow

/--
Appendix Lemma 9.6, borrow-target component.

The proof is the paper's induction over Definition 3.23:

* `W-Strong`/`W-Weak` reduce to replacing the base slot and checking the
  contained borrows of the updated partial type.
* `W-Box` is the recursive path case.
* `W-MutB` uses the corresponding induction over `writeBorrowTargets`, whose
  cons case is discharged by the environment-join borrow invariant.

The statement is deliberately at the assignment boundary rather than at a
syntactic variable case.  The right-hand side may change the environment from
`env₁` to `env₂`, and a write through `*w` may fan out through mutable-borrow
targets before joining the resulting environments.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_appendix96
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ContainedBorrowsWellFormed env₃ := by
  intro hobligations hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
    hwrite hnotWrite
  cases lhs with
  | var x =>
      rcases LValTyping.var_inv hLhs with
        ⟨sourceSlot, hsourceSlot, _hsourceTy, hsourceLifetime⟩
      cases hwrite with
      | intro hwriteSlot hupdate =>
          rename_i writeEnv writeSlot updatedTy
          simp [LVal.base] at hwriteSlot
          rcases (TermTyping.slot_lifetime_survives.1 hRhs)
              (by simpa [hsourceLifetime] using htargetLifetime)
              hsourceSlot with
            ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
          have hwriteSlotEq : writeSlot = rhsSlot := by
            have hsomeEq : some writeSlot = some rhsSlot := by
              rw [← hwriteSlot, hrhsSlot]
            exact Option.some.inj hsomeEq
          have hwriteLifetime : writeSlot.lifetime = targetLifetime := by
            rw [hwriteSlotEq, ← hrhsLifetime, hsourceLifetime]
          have hLhs₂ : LValTyping env₂ (.var x) writeSlot.ty targetLifetime := by
            rw [← hwriteLifetime]
            exact LValTyping.var hwriteSlot
          exact EnvWrite.preserves_containedBorrowsWellFormed_var
            hwellFormed hLhs₂ hwellRhs
            (EnvWrite.intro hwriteSlot hupdate)
            hnotWrite
    | deref lhs =>
        exact EnvWrite.preserves_containedBorrowsWellFormed_deref_appendix96
          hobligations hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
          hwrite hnotWrite

theorem EnvWrite.preserves_containedBorrowsWellFormed {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ContainedBorrowsWellFormed env₃ := by
  exact EnvWrite.preserves_containedBorrowsWellFormed_appendix96

/-- Assignment/update well-formedness using the precise RHS-edge rank premise.

The caller supplies the linearization witness for the pre-write environment,
proves that every newly installed RHS borrow edge points to a lower-ranked base,
and provides the lvalue-coherence transport facts for the write result. -/
theorem EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  have hlin3By :=
    EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all hwrite hlinBy hbelow
  have hlin3 := Linearizable.of_linearizedBy hlin3By
  have hcoh3 := EnvWrite.preserves_coherent_of_obligations
    hwellFormed.2.2.1 hwriteCoh
  exact ⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations hwellInitial hwellFormed hLhs
      htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite,
    EnvWrite.preserves_slotsOutlive hwellFormed.2.1 hwrite, hcoh3, hlin3⟩

/-- Assignment-level write-coherence side condition.

This is the remaining coherence proof boundary for `T-Assign`: after the RHS is
typed, the ranked write is performed, and the RHS borrow edges are known to point
downward, the resulting environment must be coherent.  The old
`EnvWrite.preserves_coherent` axiom tried to prove this from a per-target RHS
well-formedness premise, which is too weak.  This side condition is stated at the
assignment boundary where the needed typing/shape/rank facts are available.
-/
def AssignmentWritePreservesCoherent : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    Coherent env₃

/-- Structured assignment-level replacement for `AssignmentWritePreservesCoherent`.

This avoids asking directly for `Coherent env₃`.  Instead it asks for the two
lvalue-transport facts that are sufficient to prove coherence of the result:
old-root borrow typings transport back to `env₂`, while borrow typings rooted at
the written base provide their joint target-list typings in `env₃`.
-/
def AssignmentWriteCoherenceObligations : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs)

theorem AssignmentWritePreservesCoherent.of_coherenceObligations
    (hobligations : AssignmentWriteCoherenceObligations) :
    AssignmentWritePreservesCoherent := by
  intro env₁ env₂ env₃ typing lifetime targetLifetime lhs oldTy rhs rhsTy φ
    hwellInitial hwellFormed hlinBy hbelow hLhs htargetLifetime hRhs hshape
    hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_coherent_of_obligations hwellFormed.2.2.1
    (hobligations hwellInitial hwellFormed hlinBy hbelow hLhs htargetLifetime
      hRhs hshape hwellRhs hwrite hnotWrite)

/-- Assignment/update well-formedness using explicit rank and coherence premises. -/
theorem EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    AssignmentWritePreservesCoherent →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  have hlin3By :=
    EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all hwrite hlinBy hbelow
  have hlin3 := Linearizable.of_linearizedBy hlin3By
  have hcoh3 := hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact ⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations hwellInitial
      hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite,
    EnvWrite.preserves_slotsOutlive hwellFormed.2.1 hwrite, hcoh3, hlin3⟩

/-- Assignment preservation variant with the explicit RHS-edge rank premise. -/
theorem assign_preserves_wellFormed_of_rhsBorrowTargetsBelow
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow hobligations
    hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs htargetLifetime
    hRhs hshape hwellRhs hwrite hnotWrite

/-- Assignment preservation variant with explicit RHS-edge rank and coherence. -/
theorem assign_preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    AssignmentWritePreservesCoherent →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite

def DropFullLValTypingTransport (env : Env) (parent child : Lifetime) : Prop :=
  ∀ {lv targetTy targetLifetime},
    LValBaseOutlives env lv parent →
    LValTyping env lv (.ty targetTy) targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv (.ty targetTy) targetLifetime

/--
Appendix Lemma 9.5 target-stability fragment.

If an lval is typed in a well-formed block body, its base slot survives the
enclosing parent lifetime, and the reached location also lives at the parent
side, then dropping the immediate child lifetime preserves the lval typing.
-/
theorem LValTyping.dropLifetime_child_of_base_outlives {env : Env}
    {parent child : Lifetime} {lv : LVal} {targetTy : Ty}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    LValBaseOutlives env lv parent →
    LValTyping env lv (.ty targetTy) targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv (.ty targetTy) targetLifetime := by
  intro hchild hwellBody hbase htyping houtlives
  have htransport :
      (∀ {lv partialTy lifetime},
        LValTyping env lv partialTy lifetime →
        LValBaseOutlives env lv parent →
        lifetime ≤ parent →
        LValTyping (env.dropLifetime child) lv partialTy lifetime) ∧
      (∀ {targets partialTy lifetime},
        LValTargetsTyping env targets partialTy lifetime →
        (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
        lifetime ≤ parent →
        LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime) := by
    constructor
    · intro lv partialTy lifetime htyping
      exact LValTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
        (motive_2 := fun targets partialTy lifetime _ =>
          (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
          lifetime ≤ parent →
          LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
        (by
          intro x slot hslot _hbase houtlives
          exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
            ⟨hslot, by
              intro hslotLifetime
              subst hslotLifetime
              exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.box (ih hbase houtlives))
        (by
          intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
            hborrow _htargets ihBorrow ihTargets hbase houtlives
          have hborrowLifetime : _borrowLifetime ≤ parent :=
            LValTyping.lifetime_outlives_of_base_outlives_one
              hwellBody.1 hborrow hbase
          have hwellTargetsAtBorrow :
              BorrowTargetsWellFormed env targets _borrowLifetime :=
            LValTyping.containedBorrowTargetsWellFormed_at_lifetime
              hwellBody.1 hborrow PartialTyContains.here
          have hwellTargets :
              BorrowTargetsWellFormed env targets parent :=
            BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
          exact LValTyping.borrow
            (ihBorrow hbase hborrowLifetime)
            (ihTargets
              (by
                intro target htarget
                rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
                exact hbaseTarget)
              houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
            _hhead _hrest hunion hintersection ihHead ihRest hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
    · intro targets partialTy lifetime htyping
      exact LValTargetsTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
        (motive_2 := fun targets partialTy lifetime _ =>
          (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
          lifetime ≤ parent →
          LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
        (by
          intro x slot hslot _hbase houtlives
          exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
            ⟨hslot, by
              intro hslotLifetime
              subst hslotLifetime
              exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.box (ih hbase houtlives))
        (by
          intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
            hborrow _htargets ihBorrow ihTargets hbase houtlives
          have hborrowLifetime : _borrowLifetime ≤ parent :=
            LValTyping.lifetime_outlives_of_base_outlives_one
              hwellBody.1 hborrow hbase
          have hwellTargetsAtBorrow :
              BorrowTargetsWellFormed env targets _borrowLifetime :=
            LValTyping.containedBorrowTargetsWellFormed_at_lifetime
              hwellBody.1 hborrow PartialTyContains.here
          have hwellTargets :
              BorrowTargetsWellFormed env targets parent :=
            BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
          exact LValTyping.borrow
            (ihBorrow hbase hborrowLifetime)
            (ihTargets
              (by
                intro target htarget
                rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
                exact hbaseTarget)
              houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
            _hhead _hrest hunion hintersection ihHead ihRest hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
  exact htransport.1 htyping hbase houtlives

theorem LValTargetsTyping.dropLifetime_child_of_member_base_outlives {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hbaseTargets htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy targetLifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      targetLifetime ≤ parent →
      LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime)
    ?var ?box ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget hbaseTargets houtlives
    exact LValTargetsTyping.singleton
      (LValTyping.dropLifetime_child_of_base_outlives
        hchild hwellBody (hbaseTargets target (by simp)) htarget houtlives)
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest hbaseTargets houtlives
    exact LValTargetsTyping.cons
      (LValTyping.dropLifetime_child_of_base_outlives hchild hwellBody
        (hbaseTargets target (by simp)) hhead
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives))
      (ihRest
        (by
          intro selected hselected
          exact hbaseTargets selected (by simp [hselected]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives))
      hunion hintersection

theorem LValTargetsTyping.dropLifetime_child_of_wellFormedTargets {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    BorrowTargetsWellFormed env targets parent →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hwellTargets htyping houtlives
  exact LValTargetsTyping.dropLifetime_child_of_member_base_outlives
    hchild hwellBody
    (by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
        ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbase⟩
      exact hbase)
    htyping houtlives

/-- Backward typing across a lifetime drop: `dropLifetime` only *removes* slots
(leaving the rest unchanged), so any typing in the dropped environment also holds
in the original. -/
theorem LValTyping.of_dropLifetime {env : Env} {child : Lifetime}
    {lv : LVal} {p : PartialTy} {lf : Lifetime}
    (h : LValTyping (env.dropLifetime child) lv p lf) : LValTyping env lv p lf := by
  refine LValTyping.rec
    (motive_1 := fun lv p lf _ => LValTyping env lv p lf)
    (motive_2 := fun targets p lf _ => LValTargetsTyping env targets p lf)
    ?var ?box ?borrow ?singleton ?cons h
  · intro x slot hslot
    rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _⟩
    exact LValTyping.var henvSlot
  · intro _lv _inner _lifetime _htyping ih
    exact LValTyping.box ih
  · intro _lv _mutable _targets _bLf _tLf _tTy _hborrow _htargets ihBorrow ihTargets
    exact LValTyping.borrow ihBorrow ihTargets
  · intro _target _ty _lifetime _htarget ih
    exact LValTargetsTyping.singleton ih
  · intro _target _rest _headTy _headLf _restLf _lf _restTy _unionTy
      _hhead _hrest hunion hint ihHead ihRest
    exact LValTargetsTyping.cons ihHead ihRest hunion hint

theorem LValTargetsTyping.dropLifetime_child_of_transport {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    DropFullLValTypingTransport env parent child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro htransport hbaseTargets htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy targetLifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      targetLifetime ≤ parent →
      LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime)
    ?var ?box ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget hbaseTargets houtlives
    exact LValTargetsTyping.singleton
      (htransport (hbaseTargets target (by simp)) htarget houtlives)
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest hbaseTargets houtlives
    exact LValTargetsTyping.cons
      (htransport (hbaseTargets target (by simp)) hhead
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives))
      (ihRest
        (by
          intro selected hselected
          exact hbaseTargets selected (by simp [hselected]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives))
      hunion hintersection

theorem BorrowTargetsWellFormedInSlot.dropLifetime_child_of_transport
    {env : Env} {parent child slotLifetime : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    slotLifetime ≤ parent →
    BorrowTargetsWellFormedInSlot (env.dropLifetime child) slotLifetime targets := by
  intro hchild htransport htargets hslotParent target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htyping, htargetOutlivesSlot, hbase⟩
  have hbaseParent : LValBaseOutlives env target parent := by
    rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
    exact ⟨baseSlot, hbaseSlot,
      LifetimeOutlives.trans hbaseOutlives hslotParent⟩
  refine ⟨targetTy, targetLifetime,
    htransport hbaseParent htyping
      (LifetimeOutlives.trans htargetOutlivesSlot hslotParent),
    htargetOutlivesSlot, ?_⟩
  exact LValBaseOutlives.dropLifetime_child hchild hslotParent hbase

theorem BorrowTargetsWellFormed.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormed env targets parent →
    BorrowTargetsWellFormed (env.dropLifetime child) targets parent := by
  intro hchild htransport htargets
  cases htargets with
  | intro hmembers =>
      refine BorrowTargetsWellFormed.intro ?_
      intro target htarget
      rcases hmembers target htarget with
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
      have hbaseParent : LValBaseOutlives env target parent := by
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        exact ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
      refine ⟨targetTy, targetLifetime,
        htransport hbaseParent htyping houtlives, houtlives, ?_⟩
      exact LValBaseOutlives.dropLifetime_child hchild
        (LifetimeOutlives.refl parent) hbase

theorem WellFormedTy.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    WellFormedTy env ty parent →
    WellFormedTy (env.dropLifetime child) ty parent := by
  intro hchild htransport hwellTy
  induction hwellTy with
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | borrow htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.dropLifetime_child_of_transport
          hchild htransport htargets)
  | box _hinner ih =>
      exact WellFormedTy.box (ih hchild htransport)

theorem ContainedBorrowsWellFormed.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    DropFullLValTypingTransport env parent child →
    ContainedBorrowsWellFormed (env.dropLifetime child) := by
  intro hchild hwellBody htransport x slot mutable targets hslot hcontains
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨holdSlot, hslotNeChild⟩
  have holdContains : env ⊢ x ↝ Ty.borrow mutable targets :=
    EnvContains.dropLifetime_of_contains hcontains
  have hslotParent : slot.lifetime ≤ parent :=
    LifetimeChild.parent_of_outlives_child_ne hchild
      (hwellBody.2.1 x slot holdSlot) hslotNeChild
  exact BorrowTargetsWellFormedInSlot.dropLifetime_child_of_transport
    hchild
    htransport
    (hwellBody.1 x slot mutable targets holdSlot holdContains)
    hslotParent

/-- `Linearizable` is preserved by a lifetime drop (the same rank function works;
`dropLifetime` only removes slots). -/
theorem Linearizable.dropLifetime_child {env : Env} {child : Lifetime}
    (h : Linearizable env) : Linearizable (env.dropLifetime child) := by
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _⟩
  exact hφ x slot henvSlot

/-- `Coherent` is preserved by a lifetime drop: a borrow typed in the dropped
environment also types in the original (`of_dropLifetime`), where `Coherent env`
gives its targets a joint typing, which then transports back across the drop
(`dropLifetime_child_of_wellFormedTargets`).  The targets are well formed at
`parent` because the surviving borrow's base outlives `parent`. -/
theorem Coherent.dropLifetime_child {env : Env} {parent child : Lifetime}
    (hchild : LifetimeChild parent child) (hwellBody : WellFormedEnv env child)
    (hcohEnv : Coherent env) : Coherent (env.dropLifetime child) := by
  intro lv m T bLf hty
  have htyEnv := LValTyping.of_dropLifetime hty
  rcases hcohEnv lv m T bLf htyEnv with ⟨ty, lt, htgtsEnv⟩
  rcases LValTyping.base_slot_exists hty with ⟨dslot, hdslot⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hdslot with ⟨henvBase, hneChild⟩
  have hbaseParent : LValBaseOutlives env lv parent := by
    rcases LValTyping.base_outlives_one hwellBody htyEnv with ⟨bslot, hbslot, hble⟩
    have hEq : dslot = bslot := Option.some.inj (henvBase.symm.trans hbslot)
    exact ⟨bslot, hbslot,
      LifetimeChild.parent_of_outlives_child_ne hchild hble (hEq ▸ hneChild)⟩
  have hbLfParent : bLf ≤ parent :=
    LValTyping.lifetime_outlives_of_base_outlives_one hwellBody.1 htyEnv hbaseParent
  have hwellT : BorrowTargetsWellFormed env T parent :=
    BorrowTargetsWellFormed.weaken
      (LValTyping.containedBorrowTargetsWellFormed_at_lifetime hwellBody.1 htyEnv
        PartialTyContains.here)
      hbLfParent
  have hltParent : lt ≤ parent :=
    (LValTyping.lifetime_outlives_of_base_outlives hwellBody.1).2 htgtsEnv (by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellT target htarget with
        ⟨_, _, _, _, hb⟩
      exact hb)
  exact ⟨ty, lt, LValTargetsTyping.dropLifetime_child_of_wellFormedTargets
    hchild hwellBody hwellT htgtsEnv hltParent⟩

/--
Block drop preservation for well-formed environments, used in the `T-Block`
case of Lemma 4.9.

This is the environment side of Appendix Lemma 9.5 together with the
`Γ₂ ⊢ T ≽ l` premise from `T-Block`: dropping the block lifetime removes locals
without invalidating the result type at the enclosing lifetime.
-/
theorem Env.dropLifetime_preserves_wellFormed_child {env env' : Env}
    {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    WellFormedTy env ty parent →
    env' = env.dropLifetime child →
    WellFormedEnv env' parent ∧ WellFormedTy env' ty parent := by
  intro hchild hwellBody hwellTy hdrop
  subst hdrop
  have htransport : DropFullLValTypingTransport env parent child := by
    intro lv targetTy targetLifetime hbase htyping houtlives
    exact LValTyping.dropLifetime_child_of_base_outlives
      hchild hwellBody hbase htyping houtlives
  refine ⟨
    ⟨ContainedBorrowsWellFormed.dropLifetime_child_of_transport
        hchild hwellBody htransport,
      EnvSlotsOutlive.dropLifetime_child hchild hwellBody.2.1,
      Coherent.dropLifetime_child hchild hwellBody hwellBody.2.2.1,
      Linearizable.dropLifetime_child hwellBody.2.2.2⟩,
    WellFormedTy.dropLifetime_child_of_transport hchild htransport hwellTy⟩

theorem block_preserves_wellFormed {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₂ blockLifetime →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnv env₃ lifetime ∧ WellFormedTy env₃ ty lifetime := by
  intro hchild hwellBody _hterms hwellTy hdrop
  exact Env.dropLifetime_preserves_wellFormed_child hchild hwellBody hwellTy hdrop

theorem declare_preserves_wellFormed_of_output_fresh {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name}
    {term : Term} {ty : Ty} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    FreshUpdateCoherenceObligations env₂ x ty lifetime →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    WellFormedEnv env₃ lifetime := by
  intro hwellFormed hwellTy hfresh _hterm hcoh henv₃
  exact declare_preserves_wellFormed_output_fresh hwellFormed hwellTy hfresh hcoh henv₃

/--
Constructor landmarks for Lemma 4.9.

The term-typing induction is small once the update-sensitive constructors are
named at their paper granularity.  The final Lemma 4.9 route below uses the
rule-carried obligation induction instead of manufacturing this legacy landmark
package from broad write-preservation claims.
-/
structure TypingPreservesWellFormedObligations : Prop where
  block_preserves_wellFormed
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₂ blockLifetime →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnv env₃ lifetime ∧ WellFormedTy env₃ ty lifetime
  copy_result_wellFormed
    {env : Env} {lv : LVal} {ty : Ty}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    CopyTy ty →
    WellFormedTy env ty lifetime
  move_preserves_wellFormed
    {env env' : Env} {lv : LVal} {ty : Ty}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedEnv env' lifetime ∧ WellFormedTy env' ty lifetime
  assign_preserves_wellFormed
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime

/--
Lemma 4.9 induction, parameterized by the appendix landmarks.

This is the proof we want to keep clean: each typing constructor is handled
once, while the reusable update/move/copy facts are proved separately.
-/
theorem typingPreservesWellFormed_of_landmarks
    (hlandmarks : TypingPreservesWellFormedObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        hlandmarks.copy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      hlandmarks.move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      hlandmarks.block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcoh henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcoh)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellRhs hwrite _hranked _hwriteCoh hnotWrite ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨hlandmarks.assign_preserves_wellFormed hwellFormed result.1 hLhs
          (LValTyping.lifetime_outlives_one hwellFormed hLhs)
          hRhs hshape hwellRhs hwrite hnotWrite,
        WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
      (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
          _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
        let headResult := ihHead htypingEq hwellFormed
        ihRest htypingEq headResult.1)
      htyping rfl hwellFormed

/-- Assignment-level rank side condition for the well-formedness induction.

This packages the rule obligation that `T-Assign` currently does not carry:
after typing the RHS and performing the write, there must be a pre-write
linearization witness such that every newly installed RHS borrow edge is ranked
downward in the result. -/
def AssignmentRhsEdgesRanked : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy

/-- Declaration-level fresh-slot coherence side condition for Lemma 4.9.

The legacy declaration case used `Coherent.update_fresh_ty`, which is false from
`WellFormedTy` alone.  This side condition states the missing local fact for each
`T-Declare`: adding the freshly declared full type must satisfy the explicit
fresh-update coherence obligations.
-/
def DeclarationFreshUpdateCoherent : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {ty : Ty},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₁.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh x →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    FreshUpdateCoherenceObligations env₂ x ty lifetime

/-- Declaration-level decomposition for borrow-free declared types.

For a borrow-free declared/result type, the fresh-root part of
`FreshUpdateCoherenceObligations` is automatic.  The only declaration-local
coherence work left is old-root transport for borrow typings in the extended
environment.
-/
def DeclarationFreshBorrowFreeOldRootTransport : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {ty : Ty},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₁.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh x →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    TyBorrowFree ty ∧
      (∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
        {borrowLifetime : Lifetime},
        LVal.base lv ≠ x →
        LValTyping (env₂.update x { ty := .ty ty, lifetime := lifetime })
          lv (.ty (.borrow mutable targets)) borrowLifetime →
        ∃ oldBorrowLifetime,
          LValTyping env₂ lv (.ty (.borrow mutable targets)) oldBorrowLifetime)

theorem DeclarationFreshUpdateCoherent.of_borrowFreeOldRootTransport
    (hdecl : DeclarationFreshBorrowFreeOldRootTransport) :
    DeclarationFreshUpdateCoherent := by
  intro env₁ env₂ env₃ typing lifetime x term ty hwellInitial hwellResult
    hwellTy hfreshIn hterm hfreshOut henv₃
  rcases hdecl hwellInitial hwellResult hwellTy hfreshIn hterm hfreshOut henv₃ with
    ⟨hborrowFree, holdTransport⟩
  exact FreshUpdateCoherenceObligations.of_tyBorrowFree hborrowFree holdTransport

/-- Lemma 4.9 well-formedness induction using the rule-carried ranked-assignment
side condition instead of the false bare `EnvWrite.preserves_linearizedBy`.

The `AssignmentRhsEdgesRanked` parameter is kept for compatibility with older
callers; after strengthening `T-Assign`, the proof consumes the rank witness
stored directly in the assignment typing derivation. -/
theorem typingPreservesWellFormed_of_assignmentRhsEdgesRanked
    (hobligations : UpdateBorrowInvariantObligations)
    (_hrankedAssign : AssignmentRhsEdgesRanked)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed, copyTy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcoh henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcoh)
      (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
          hLhs hRhs hshape hwellRhs hwrite hranked hwriteCoh hnotWrite ih htypingEq
          hwellFormed =>
        by
          let result := ih htypingEq hwellFormed
          have htargetLifetime : _targetLifetime ≤ _lifetime :=
            LValTyping.lifetime_outlives_one hwellFormed hLhs
          rcases hranked with
            ⟨φ, hlinBy, hbelow⟩
          exact ⟨assign_preserves_wellFormed_of_rhsBorrowTargetsBelow hobligations
              hwellFormed result.1 hlinBy hbelow hwriteCoh hLhs htargetLifetime
              hRhs hshape hwellRhs hwrite hnotWrite,
            WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
      let headResult := ihHead htypingEq hwellFormed
      ihRest htypingEq headResult.1)
    htyping rfl hwellFormed

/-- Lemma 4.9 well-formedness induction using rule-carried obligations.

The assignment rank/write-coherence facts and declaration fresh-slot coherence
fact come from the strengthened `T-Assign` and `T-Declare` constructors. -/
theorem typingPreservesWellFormed_of_ruleCarriedObligations
    (hobligations : UpdateBorrowInvariantObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed, copyTy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcohObligations henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcohObligations)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellRhs hwrite hranked hwriteCoh hnotWrite ih htypingEq
        hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        have htargetLifetime : _targetLifetime ≤ _lifetime :=
          LValTyping.lifetime_outlives_one hwellFormed hLhs
        rcases hranked with
          ⟨φ, hlinBy, hbelow⟩
        have hlin3By :=
          EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
            hwrite hlinBy hbelow
        have hcoh3 := EnvWrite.preserves_coherent_of_obligations
          result.1.2.2.1 hwriteCoh
        exact ⟨⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations
              hwellFormed result.1 hLhs htargetLifetime hRhs hshape hwellRhs
              hwrite hnotWrite,
            EnvWrite.preserves_slotsOutlive result.1.2.1 hwrite,
            hcoh3,
            Linearizable.of_linearizedBy hlin3By⟩,
          WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
      let headResult := ihHead htypingEq hwellFormed
      ihRest htypingEq headResult.1)
    htyping rfl hwellFormed

/-- Compatibility wrapper for the older explicit-premise API.

The premise names are now rule-carried by `TermTyping`; callers should prefer
`typingPreservesWellFormed_of_ruleCarriedObligations`. -/
theorem typingPreservesWellFormed_of_rankedAssign_and_declFreshCoherence
    (hobligations : UpdateBorrowInvariantObligations)
    (_hrankedAssign : AssignmentRhsEdgesRanked)
    (_hwriteCoherent : AssignmentWriteCoherenceObligations)
    (_hdeclFresh : DeclarationFreshUpdateCoherent)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  exact typingPreservesWellFormed_of_ruleCarriedObligations hobligations

/--
Lemma 4.9 wrapper used by the later borrow-invariance statements.

The term-typing induction itself lives in `typingPreservesWellFormed_of_landmarks`.
This wrapper uses the strengthened typing rules: assignment rank/write coherence
and declaration fresh-slot coherence are carried by `TermTyping`, while
`UpdateBorrowInvariantObligations` supplies the remaining contained-borrow update
facts.
-/
theorem typingPreservesWellFormed_of_storeTypingRefs
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact typingPreservesWellFormed_of_ruleCarriedObligations hobligations
    hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping

theorem typingPreservesWellFormed_emptyStoreTyping
    {store : ProgramStore} {env₁ env₂ : Env}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    UpdateBorrowInvariantObligations →
    ValidState store term →
    ValidStoreTyping store term StoreTyping.empty →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hobligations hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact typingPreservesWellFormed_of_storeTypingRefs
    hobligations
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    hvalidState hvalidStoreTyping hwellFormed hsafe htyping

theorem borrowInvariance_emptyStoreTyping {store : ProgramStore}
    {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    ValidState store term →
    ValidStoreTyping store term StoreTyping.empty →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
    hobligations
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

theorem borrowInvariance_of_storeTypingRefs {store : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
    hfresh hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
      hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/-- Source-initial borrow invariance through the rule-carried route. -/
theorem sourceInitial_borrowInvariance {term : Term} {env₂ : Env}
    {lifetime : Lifetime} {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hsource htyping hfresh hfreshCoherence
  exact borrowInvariance_emptyStoreTyping
    hobligations
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

theorem sourceInitial_typeAndBorrowSafety_of_preservation
    {term : Term} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    (∀ finalStore finalValue,
      MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₂ ty) →
    TerminatesAsValue ProgramStore.empty lifetime term →
    ProgressResult ProgramStore.empty lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping hpreservation hterminates
  exact typeAndBorrowSafety_of_preservation
    (sourceInitialRuntimeState_valid hsource)
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    wellFormedEnv_empty_all
    safeAbstraction_empty
    operationalStoreProgress_empty
    htyping
    hpreservation
    hterminates

theorem sourceInitial_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.val value) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.val value) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_multistep_value_preservation hsource htyping hmulti)
    ⟨ProgramStore.empty, value, MultiStep.refl⟩

theorem sourceInitial_blockB_value_typeAndBorrowSafety
    {value : Value} {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime
      (.block blockLifetime [.val value]) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.block blockLifetime [.val value]) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime
          (.block blockLifetime [.val value]) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.block blockLifetime [.val value]) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  rcases drops_empty_lifetime blockLifetime with ⟨storeAfterDrop, hdrops⟩
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_blockB_value_multistep_preservation hsource htyping hmulti)
    ⟨storeAfterDrop, value,
      MultiStep.trans (Step.blockB (lifetime := lifetime) hdrops) MultiStep.refl⟩

theorem sourceInitial_box_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    ProgressResult ProgramStore.empty lifetime (.box (.val value)) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ (.box ty) := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.box (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  let boxed := ProgramStore.empty.boxAt 0 value
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_box_value_multistep_preservation hsource htyping hmulti)
    ⟨boxed.1, .ref boxed.2,
      MultiStep.trans
        (Step.box (address := 0) (ref := boxed.2)
          (by simp [ProgramStore.fresh, ProgramStore.empty])
          (by simp [boxed]))
        MultiStep.refl⟩

theorem sourceInitial_declare_value_typeAndBorrowSafety
    {x : Name} {value : Value} {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    ProgressResult ProgramStore.empty lifetime (.letMut x (.val value)) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.letMut x (.val value)) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₃ .unit := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.letMut x (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_declare_value_multistep_preservation hsource htyping hmulti)
    ⟨ProgramStore.empty.declare x lifetime value, .unit,
      MultiStep.trans (Step.declare (lifetime := lifetime) rfl) MultiStep.refl⟩

theorem preservation_value_case {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
  exact preservation_multistep_runtime_value hvalidRuntime hvalidStoreTyping
    hsafe htyping hmulti

theorem preservation_box_value_case {store finalStore : ProgramStore}
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    ValidStoreTyping store (.box (.val value)) typing →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.box (.val value)) →
    TermTyping env₁ typing lifetime (.box (.val value)) (.box ty) env₂ →
    MultiStep store lifetime (.box (.val value)) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ (.box ty) := by
  intro hvalidStoreTyping hsafe hvalidRuntime htyping hmulti
  exact preservation_box_multistep_runtime hvalidStoreTyping hsafe hvalidRuntime
    htyping hmulti

theorem preservation_declare_value_case {store finalStore : ProgramStore}
    {env₁ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {value finalValue : Value} :
    ValidStoreTyping store (.letMut x (.val value)) typing →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.letMut x (.val value)) →
    TermTyping env₁ typing lifetime (.letMut x (.val value)) .unit env₃ →
    MultiStep store lifetime (.letMut x (.val value)) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₃ .unit := by
  intro hvalidStoreTyping hsafe hvalidRuntime htyping hmulti
  exact preservation_declare_multistep_runtime hvalidStoreTyping hsafe hvalidRuntime
    htyping hmulti

theorem preservation_blockB_value_no_slots_case {store finalStore : ProgramStore}
    {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    store ∼ₛ env →
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    (∀ location slot,
      store.slotAt location = some slot →
      slot.lifetime ≠ blockLifetime) →
    ValidValue store value ty →
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env' ty := by
  intro hvalidRuntime hsafe htyping hnoSlots hvalidValue hmulti
  exact preservation_blockB_value_multistep_runtime_no_slots hvalidRuntime hsafe
    htyping hnoSlots hvalidValue hmulti

theorem typingPreservesBorrowSafeResult_mutBorrow_case {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow true lv) (.borrow true [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow true [lv]), lifetime := lifetime }) := by
  intro hborrowSafe htyping hfresh
  exact borrowSafety_mutBorrow_result_extension hborrowSafe htyping hfresh

theorem typingPreservesBorrowSafeResult_immBorrow_case {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.borrow false lv) (.borrow false [lv]) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.borrow false [lv]), lifetime := lifetime }) := by
  intro hborrowSafe htyping hfresh
  exact borrowSafety_immBorrow_result_extension hborrowSafe htyping hfresh

theorem typingPreservesBorrowSafeResult_copy_case {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal} {ty : Ty}
    {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.copy lv) ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hborrowSafe htyping hfresh
  cases htyping with
  | copy hLv hcopy _hnotRead =>
      cases hcopy with
      | int =>
          exact borrowSafeEnv_update_fresh_borrowFree hborrowSafe tyBorrowFree_int
      | immBorrow =>
          rename_i targets
          exact borrowSafeEnv_update_fresh_immBorrowMany hborrowSafe hfresh
            (by
              intro target htarget
              exact (LValTyping.no_readProhibited_targets_of_immBorrow hborrowSafe).1
                hLv PartialTyContains.here target htarget)

theorem typingPreservesBorrowSafeResult_box_case {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty}
    {gamma : Name} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) →
    TermTyping env₁ typing lifetime (.box term) (.box ty) env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty (.box ty), lifetime := lifetime }) := by
  intro _hwellFormed _hwellTy hinnerSafe _htyping _hfresh
  exact borrowSafeEnv_update_box_of_update_inner hinnerSafe

theorem typingPreservesBorrowSafeResult_unit_case {env₂ : Env}
    {lifetime : Lifetime} {gamma : Name} :
    WellFormedEnv env₂ lifetime →
    BorrowSafeEnv env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv
      (env₂.update gamma { ty := .ty .unit, lifetime := lifetime }) := by
  intro _hwellFormed hborrowSafe _hfresh
  exact borrowSafeEnv_update_fresh_borrowFree hborrowSafe tyBorrowFree_unit

/--
Constructor-level borrow-safety landmarks used by the source-scoped Corollary
4.14 route.

Result-extension for `T-Const` is only proved for source values; arbitrary
runtime references need an evaluation/reachability invariant, not a local typing
fact.  The copy, move, mut/imm borrow, box, and declaration shells are proved
directly from the conflict definitions and induction hypotheses.  The assignment
field consumes the full RHS induction result: `BorrowSafeEnv env₂` plus the
root-independent fact that the RHS type has no borrow-target conflicts with
`env₂`.  This avoids baking fresh-name reasoning into assignment; fresh result
installation is a caller-level corollary of the same invariant.  Block bodies
are handled by the mutual term/list induction below: the induction carries
`TyBorrowSafeAgainstEnv` through `dropLifetime`, so there is no separate
block-list obligation here.
-/
structure BorrowSafetyPreservationObligations : Prop where
  envWrite {env₁ env₂ env₃ : Env}
      {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
      {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
      BorrowSafeEnv env₂ →
      TyBorrowSafeAgainstEnv env₂ rhsTy →
      LValTyping env₁ lhs oldTy targetLifetime →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      ShapeCompatible env₂ oldTy (.ty rhsTy) →
      WellFormedTy env₂ rhsTy targetLifetime →
      EnvWrite 0 env₂ lhs rhsTy env₃ →
      (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
      EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
      ¬ WriteProhibited env₃ lhs →
      BorrowSafeEnv env₃

/-- Move borrow-safety preservation, including result-extension.

The proof uses `LValTyping.contains_base_of_strike`: since `EnvMove` follows a
`Strike` path, every borrow contained in the moved result type originated in the
moved base slot.  Once that origin fact is known,
`borrowSafeEnv_move_result_extension_of_base_contains` discharges the fresh
result root.
-/
theorem borrowSafetyPreservation_move
    {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {ty : Ty} {gamma : Name} :
    BorrowSafeEnv env →
    TermTyping env typing lifetime (.move lv) ty env₂ →
    (∀ x, lv ≠ .var x) →
    ¬ TyBorrowFree ty →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hborrowSafe htyping _hnotVar _hnotBorrowFree hfresh
  cases htyping with
  | move hLv _hnotWrite hmove =>
      rcases hmove with ⟨slot, struck, hslot, hstrike, henv₂⟩
      subst henv₂
      exact borrowSafeEnv_move_result_extension_of_base_contains
        hborrowSafe
        ⟨slot, struck, hslot, hstrike, rfl⟩
        (by
          intro mutable targets hcontains
          exact LValTyping.contains_base_of_strike hLv hslot hstrike hcontains)
        hfresh

/-- Remaining explicit `EnvWrite` borrow-safety frame obligation.

The global term-typing induction supplies both `BorrowSafeEnv env₂` and the RHS
root-independent type/environment invariant.  The latter is part of the real
assignment argument: `BorrowSafeEnv env₂` alone does not say that borrow targets
contained in `rhsTy` are safe against existing environment roots.

The remaining hard case is fan-out through a mutable borrow.  If two result roots
receive borrow targets originating from `rhsTy`, `TyBorrowSafeAgainstEnv env₂
rhsTy` is not enough: it only rules out conflicts between `rhsTy` and the
pre-write environment, not conflicts created by duplicating the RHS borrow into
multiple result roots.  Completing this proof likely requires either a
source/result invariant saying RHS-derived borrow targets are safe when
duplicated by this write, or a borrow-inference side condition ruling out such
fan-out for non-borrow-free RHS types.
-/
theorem borrowSafetyPreservation_envWrite
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    BorrowSafeEnv env₂ →
    TyBorrowSafeAgainstEnv env₂ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    ¬ WriteProhibited env₃ lhs →
    BorrowSafeEnv env₃ := by
  sorry

/-- Concrete borrow-safety package assembled from the explicit sorried lemmas. -/
theorem borrowSafetyPreservationObligations_from_sorries :
    BorrowSafetyPreservationObligations where
  envWrite := borrowSafetyPreservation_envWrite

theorem typingPreservesWellFormed_of_updateBorrowInvariant
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact typingPreservesWellFormed_of_storeTypingRefs hobligations hrefs hvalidState
    hvalidStoreTyping hwellFormed hsafe htyping

/-- Lemma 4.9 core statement: typing preserves environment well-formedness.

The remaining update-specific invariant work is explicit in
`UpdateBorrowInvariantObligations`; assignment rank/write-coherence and
declaration fresh-slot coherence are carried by the typing derivation itself. -/
theorem typingPreservesWellFormed {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  exact typingPreservesWellFormed_of_ruleCarriedObligations
    hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping

/--
Constructor-level runtime preservation landmarks used by Lemma 4.11.

The value, copy, borrow, box, and declaration cases are discharged by existing
multistep fragments.  The fields isolate the cases still requiring the paper's
general move/update/drop preservation arguments.
-/
structure RuntimePreservationObligations : Prop where
  move {store finalStore : ProgramStore} {env₁ env₂ : Env}
      {typing : StoreTyping} {lifetime : Lifetime}
      {lv : LVal} {ty : Ty} {finalValue : Value} :
      ValidRuntimeState store (.move lv) →
      ValidStoreTyping store (.move lv) typing →
      WellFormedEnv env₁ lifetime →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime (.move lv) ty env₂ →
      MultiStep store lifetime (.move lv) finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₂ ty
  assign {midStore finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
      {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
      {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
      {value finalValue : Value} :
      LValTyping env₁ lhs oldTy targetLifetime →
      TermTyping env₁ typing lifetime rhs rhsTy env₂ →
      ShapeCompatible env₂ oldTy (.ty rhsTy) →
      WellFormedTy env₂ rhsTy targetLifetime →
      EnvWrite 0 env₂ lhs rhsTy env₃ →
      ¬ WriteProhibited env₃ lhs →
      ValidRuntimeState midStore (.assign lhs (.val value)) →
      midStore ∼ₛ env₂ →
      ValidValue midStore value rhsTy →
      Step midStore lifetime (.assign lhs (.val value)) finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₃ .unit
  block {store finalStore : ProgramStore} {env₁ env₃ : Env}
      {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
      {terms : List Term} {ty : Ty} {finalValue : Value} :
      ValidRuntimeState store (.block blockLifetime terms) →
      ValidStoreTyping store (.block blockLifetime terms) typing →
      WellFormedEnv env₁ lifetime →
      store ∼ₛ env₁ →
      TermTyping env₁ typing lifetime (.block blockLifetime terms) ty env₃ →
      MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₃ ty

/-- Remaining explicit runtime preservation obligation for moves. -/
theorem runtimePreservation_move
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {lv : LVal} {ty : Ty} {finalValue : Value} :
    ValidRuntimeState store (.move lv) →
    ValidStoreTyping store (.move lv) typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.move lv) ty env₂ →
    MultiStep store lifetime (.move lv) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  sorry

/-- Remaining explicit runtime preservation obligation for assignment redexes.

The global Preservation induction handles RHS evaluation and passes the resulting
valid runtime state, safe abstraction, and value abstraction into this local
redex/update obligation.  This is not a pure typing obligation: the redex proof
must establish post-step runtime validity and `finalStore ∼ₛ env₃` after the
drop/write sequence, then package them with
`terminalStateSafe_assign_unit_of_postconditions`.
-/
theorem runtimePreservation_assign
    {midStore finalStore : ProgramStore} {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {value finalValue : Value} :
    LValTyping env₁ lhs oldTy targetLifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ValidRuntimeState midStore (.assign lhs (.val value)) →
    midStore ∼ₛ env₂ →
    ValidValue midStore value rhsTy →
    Step midStore lifetime (.assign lhs (.val value)) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₃ .unit := by
  sorry

/-- Remaining explicit runtime preservation obligation for blocks. -/
theorem runtimePreservation_block
    {store finalStore : ProgramStore} {env₁ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} {finalValue : Value} :
    ValidRuntimeState store (.block blockLifetime terms) →
    ValidStoreTyping store (.block blockLifetime terms) typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime (.block blockLifetime terms) ty env₃ →
    MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₃ ty := by
  sorry

/-- Concrete runtime-preservation package assembled from explicit sorried lemmas. -/
theorem runtimePreservationObligations_from_sorries :
    RuntimePreservationObligations where
  move := runtimePreservation_move
  assign := runtimePreservation_assign
  block := runtimePreservation_block

/--
Lemma 4.9, Borrow Invariance.

The paper phrases the conclusion as well-formedness of the output environment
extended with a fresh result binding `γ ↦ <T>^l`.

The final result binding must satisfy `FreshUpdateCoherenceObligations`; the
bare implication from `WellFormedTy` is false for borrow types such as `&[]`.
-/
theorem borrowInvariance {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
    hfresh hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
      hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/--
Borrow invariance through the ranked-assignment typing-preservation route.

This is the non-vacuous replacement for the old route through the bare
`EnvWrite.preserves_linearizedBy` axiom: assignment must supply the local
`AssignmentRhsEdgesRanked` obligation saying newly installed RHS borrow edges
are ranked downward in a pre-write linearization.
-/
theorem borrowInvariance_of_assignmentRhsEdgesRanked
    (hobligations : UpdateBorrowInvariantObligations)
    (hrankedAssign : AssignmentRhsEdgesRanked)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_assignmentRhsEdgesRanked
      hobligations hrankedAssign hrefs hvalidState hvalidStoreTyping hwellFormed
      hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension hwellFormedOutput hwellFormedTy hfresh
    hfreshCoherence

/--
Borrow invariance through the ranked-assignment route and the explicit
fresh-result coherence obligation.

Compared with `borrowInvariance_of_assignmentRhsEdgesRanked`, this removes the
dependency on the legacy `Coherent.update_fresh_ty` axiom.  The remaining
coherence work is split into:
* assignment/write coherence, carried by `hobligations`;
* fresh result-slot coherence, carried by `hfreshCoherence`.
-/
theorem borrowInvariance_of_assignmentRhsEdgesRanked_and_freshCoherence
    (hobligations : UpdateBorrowInvariantObligations)
    (hrankedAssign : AssignmentRhsEdgesRanked)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_assignmentRhsEdgesRanked
      hobligations hrankedAssign hrefs hvalidState hvalidStoreTyping hwellFormed
      hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/--
Borrow invariance through the rule-carried obligation route.

Assignment rank/write-coherence and declaration fresh-slot coherence are part of
the strengthened typing derivation.  The only remaining fresh-coherence premise
is for the final result binding `gamma`, which is added after the term has been
typed.
-/
theorem borrowInvariance_of_ruleCarriedObligations
    (hobligations : UpdateBorrowInvariantObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
      hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact borrowInvariance_result_extension_of_coherenceObligations
    hwellFormedOutput hwellFormedTy hfresh hfreshCoherence

/--
Borrow invariance through the fully explicit ranked/fresh-coherence route.

This version avoids both legacy false/too-weak axioms already isolated in this
file: bare write linearization and fresh-type coherence from `WellFormedTy`
alone.  This is now a compatibility wrapper around
`borrowInvariance_of_ruleCarriedObligations`; the assignment/declaration
side-condition parameters are supplied by the typing derivation itself.
-/
theorem borrowInvariance_of_rankedAssign_and_declFreshCoherence
    (hobligations : UpdateBorrowInvariantObligations)
    (_hrankedAssign : AssignmentRhsEdgesRanked)
    (_hwriteCoherent : AssignmentWriteCoherenceObligations)
    (_hdeclFresh : DeclarationFreshUpdateCoherent)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping hfresh
    hfreshCoherence
  exact borrowInvariance_of_ruleCarriedObligations
    hobligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
    hfresh hfreshCoherence

/--
Source-initial borrow invariance through the explicit ranked/fresh-coherence
route.

This is the source-program version of
`borrowInvariance_of_rankedAssign_and_declFreshCoherence`: it avoids the legacy
bare write-linearization and fresh-type coherence axioms by making the missing
rank/coherence premises explicit.
-/
theorem sourceInitial_borrowInvariance_of_rankedAssign_and_declFreshCoherence
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    AssignmentRhsEdgesRanked →
    AssignmentWriteCoherenceObligations →
    DeclarationFreshUpdateCoherent →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hupdate hranked hwriteCoherent hdeclFresh hsource htyping hfresh
    hfreshCoherence
  exact borrowInvariance_of_rankedAssign_and_declFreshCoherence
    hupdate
    hranked
    hwriteCoherent
    hdeclFresh
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

/-- Source-initial borrow invariance through the rule-carried obligation route. -/
theorem sourceInitial_borrowInvariance_of_ruleCarriedObligations
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime := by
  intro hupdate hsource htyping hfresh hfreshCoherence
  exact borrowInvariance_of_ruleCarriedObligations
    hupdate
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

/--
Lemma 4.11, Preservation.

This is stated over `ValidRuntimeState`, the mechanised package that contains
Definition 4.3's valid-state condition plus the explicit owner-allocation
invariant needed by our concrete store model.
-/
theorem preservation {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    RuntimePreservationObligations →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hobligations hvalidRuntime hvalidStoreTyping hwellFormed hsafe htyping hmulti
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      ∀ (store finalStore : ProgramStore) (finalValue : Value),
        ValidRuntimeState store term →
        ValidStoreTyping store term typing →
        WellFormedEnv env lifetime →
        store ∼ₛ env →
        MultiStep store lifetime term finalStore (.val finalValue) →
        TerminalStateSafe finalStore finalValue env₂ ty)
    (motive_2 := fun _env _typing _lifetime _terms _ty _env₂ _ => True)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping
        store finalStore finalValue hvalidRuntime hvalidStoreTyping _hwellFormed hsafe
        hmulti =>
      preservation_multistep_runtime_value hvalidRuntime hvalidStoreTyping hsafe
        (TermTyping.const hvalueTyping) hmulti)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy hnotRead
        store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        hmulti =>
      preservation_copy_multistep_runtime hwellFormed hsafe hvalidRuntime
        (TermTyping.copy (typing := _typing) hLv hcopy hnotRead) hmulti)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
        hLv hnotWrite hmove store finalStore finalValue hvalidRuntime hvalidStoreTyping
        hwellFormed hsafe hmulti =>
      hobligations.move hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        (TermTyping.move hLv hnotWrite hmove) hmulti)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hmutable hnotWrite
        store finalStore finalValue hvalidRuntime _hvalidStoreTyping _hwellFormed hsafe
        hmulti =>
      preservation_borrow_multistep_runtime hsafe hvalidRuntime
        (TermTyping.mutBorrow (typing := _typing) hLv hmutable hnotWrite) hmulti)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hnotRead
        store finalStore finalValue hvalidRuntime _hvalidStoreTyping _hwellFormed hsafe
        hmulti =>
      preservation_borrow_multistep_runtime hsafe hvalidRuntime
        (TermTyping.immBorrow (typing := _typing) hLv hnotRead) hmulti)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih
        store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed hsafe hmulti =>
      preservation_box_context_terminal_multistep_runtime
        (by
          intro midStore value hvalidInner hvalidStoreTypingInner hsafeInner
            _hinnerTyping hmultiInner
          exact ih store midStore value hvalidInner hvalidStoreTypingInner
            hwellFormed hsafeInner hmultiInner)
        hvalidRuntime hvalidStoreTyping hsafe (TermTyping.box hterm) hmulti)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop _ih store finalStore finalValue hvalidRuntime
        hvalidStoreTyping hwellFormed hsafe hmulti =>
      hobligations.block hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        (TermTyping.block hblockChild hterms hwellTy hdrop) hmulti)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfresh hterm hfreshOut _hcoh henv₃ ih
        store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed hsafe
        hmulti =>
      by
        rcases multistep_declare_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hdeclareStep⟩
        rcases ih store midStore value
            (validRuntimeState_declare_inner hvalidRuntime)
            (validStoreTyping_declare_inner hvalidStoreTyping)
            hwellFormed hsafe hinnerMulti with
          ⟨hvalidInner, hsafeInner, hvalidValue⟩
        cases hdeclareStep with
        | declare hstore =>
            have hpreserved :=
              preservation_declare_redex_runtime_of_validValue hsafeInner
                hfreshOut
                (validRuntimeState_declare_value_of_value hvalidInner)
                hvalidValue
                (Step.declare (lifetime := _lifetime) hstore)
            rw [henv₃]
            exact hpreserved)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellTy hwrite hranked hcoh hnotWrite _ih store finalStore finalValue
        hvalidRuntime hvalidStoreTyping hwellFormed hsafe hmulti =>
      by
        rcases multistep_assign_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hassignStep⟩
        rcases _ih store midStore value
            (validRuntimeState_assign_inner hvalidRuntime)
            (validStoreTyping_assign_inner hvalidStoreTyping)
            hwellFormed hsafe hinnerMulti with
          ⟨hvalidInner, hsafeInner, hvalidValue⟩
        exact hobligations.assign hLhs hRhs hshape hwellTy hwrite hnotWrite
          (validRuntimeState_assign_value_of_value hvalidInner)
          hsafeInner hvalidValue hassignStep)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm _ih => trivial)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest _ihHead _ihRest => trivial)
    htyping store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
    hsafe hmulti

/--
Theorem 4.12, Type and Borrow Safety.

The paper assumes termination; here that assumption is represented by an
explicit multistep witness to a final runtime value.
-/
theorem typeAndBorrowSafety {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    RuntimePreservationObligations →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    (∀ lifetime, WellFormedEnv env₁ lifetime) →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    TerminatesAsValue store lifetime term →
    ProgressResult store lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep store lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hobligations hvalidRuntime hvalidStoreTyping hwellFormed hsafe hstoreProgress
    htyping hterminates
  exact typeAndBorrowSafety_of_preservation hvalidRuntime hvalidStoreTyping
    hwellFormed hsafe hstoreProgress htyping
    (by
      intro finalStore finalValue hmulti
      exact preservation hobligations hvalidRuntime hvalidStoreTyping
        (hwellFormed lifetime) hsafe htyping hmulti)
    hterminates

/--
Main borrow-safety induction behind Corollary 4.14.

The result binding is included in the statement because the paper's corollary
checks borrow-safety after extending the output environment with `γ ↦ <T>^l`.
-/
theorem typingPreservesBorrowSafeResult_global {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    BorrowSafeEnv env₂ ∧
      TyBorrowSafeAgainstEnv env₂ ty ∧
      ∀ gamma,
        env₂.fresh gamma →
        BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hobligations hsource hborrowSafe htyping
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      SourceTerm term →
        BorrowSafeEnv env →
        BorrowSafeEnv env₂ ∧
          TyBorrowSafeAgainstEnv env₂ ty ∧
          ∀ gamma,
            env₂.fresh gamma →
            BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }))
    (motive_2 := fun env _typing lifetime terms _ty env₂ _ =>
      SourceTerm (.block lifetime terms) →
        BorrowSafeEnv env →
        BorrowSafeEnv env₂ ∧
          TyBorrowSafeAgainstEnv env₂ _ty)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping hsource hborrowSafe =>
      by
        have hborrowFree : TyBorrowFree _ty :=
          sourceValue_valueTyping_borrowFree
            (hsource _value (by simp [termValues])) hvalueTyping
        refine ⟨hborrowSafe, tyBorrowSafeAgainstEnv_borrowFree hborrowFree, ?_⟩
        intro gamma hfresh
        exact borrowSafe_value_result_extension_borrowFree
          (TermTyping.const hvalueTyping) hborrowSafe
          hborrowFree
          hfresh)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy hnotRead
        _hsource hborrowSafe =>
      ⟨hborrowSafe,
        (by
          cases hcopy with
          | int =>
              exact tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_int
          | immBorrow =>
              rename_i targets
              exact tyBorrowSafeAgainstEnv_immBorrowMany
                (by
                  intro target htarget
                  exact (LValTyping.no_readProhibited_targets_of_immBorrow hborrowSafe).1
                    hLv PartialTyContains.here target htarget)),
        fun gamma hfresh =>
        typingPreservesBorrowSafeResult_copy_case hborrowSafe
          (TermTyping.copy (typing := _typing) hLv hcopy hnotRead) hfresh⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
        hLv hnotWrite hmove _hsource hborrowSafe =>
      by
        have hcore : BorrowSafeEnv _env₂ :=
          borrowSafeEnv_move hborrowSafe hmove
        have hsafeTy : TyBorrowSafeAgainstEnv _env₂ _ty := by
          rcases hmove with ⟨slot, struck, hslot, hstrike, henv₂⟩
          subst henv₂
          exact tyBorrowSafeAgainstEnv_move_of_base_contains
            hborrowSafe
            ⟨slot, struck, hslot, hstrike, rfl⟩
            (by
              intro mutable targets hcontains
              exact LValTyping.contains_base_of_strike hLv hslot hstrike hcontains)
        refine ⟨hcore, hsafeTy, ?_⟩
        intro gamma hfresh
        cases _lv with
        | var x =>
            exact borrowSafety_move_var_result_extension hborrowSafe
              (TermTyping.move (typing := _typing) hLv hnotWrite hmove) hfresh
        | deref lv =>
            by_cases hborrowFree : TyBorrowFree _ty
            · exact borrowSafety_move_borrowFree_result_extension
                (typing := _typing) hborrowSafe
                (TermTyping.move (typing := _typing) hLv hnotWrite hmove)
                hborrowFree
            · exact borrowSafetyPreservation_move (typing := _typing) hborrowSafe
                (TermTyping.move (typing := _typing) hLv hnotWrite hmove)
                (by
                  intro x hvar
                  cases hvar)
                hborrowFree
                hfresh)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hmutable hnotWrite
        _hsource hborrowSafe =>
      ⟨hborrowSafe,
        tyBorrowSafeAgainstEnv_mutBorrow hnotWrite,
        fun gamma hfresh =>
        typingPreservesBorrowSafeResult_mutBorrow_case hborrowSafe
          (TermTyping.mutBorrow (typing := _typing) hLv hmutable hnotWrite) hfresh⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hnotRead
        _hsource hborrowSafe =>
      ⟨hborrowSafe,
        tyBorrowSafeAgainstEnv_immBorrow hnotRead,
        fun gamma hfresh =>
        typingPreservesBorrowSafeResult_immBorrow_case hborrowSafe
          (TermTyping.immBorrow (typing := _typing) hLv hnotRead) hfresh⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih hsource hborrowSafe =>
      by
        have hinner := ih (SourceTerm.box_inner hsource) hborrowSafe
        exact ⟨hinner.1, TyBorrowSafeAgainstEnv.box hinner.2.1, by
          intro gamma hfresh
          exact borrowSafeEnv_update_box_of_update_inner (hinner.2.2 gamma hfresh)⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop _ih hsource hborrowSafe =>
      by
        have hbody := _ih hsource hborrowSafe
        have hbodySafe : BorrowSafeEnv _env₂ :=
          hbody.1
        have hbodyTySafe : TyBorrowSafeAgainstEnv _env₂ _ty :=
          hbody.2
        have hblockTySafe : TyBorrowSafeAgainstEnv _env₃ _ty := by
          rw [hdrop]
          exact TyBorrowSafeAgainstEnv.dropLifetime hbodyTySafe
        have hblockCore :
            BorrowSafeEnv _env₃ :=
          borrowSafety_block_drop hbodySafe hdrop
        refine ⟨hblockCore, hblockTySafe, ?_⟩
        intro gamma _hfresh
        exact borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv hblockCore hblockTySafe)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfreshX hterm hfreshOut _hcoh henv₃ _ih
        hsource hborrowSafe =>
      by
        have hinner := _ih (SourceTerm.declare_inner hsource) hborrowSafe
        have hdeclaredSafe :
            BorrowSafeEnv
              (_env₂.update _x { ty := .ty _ty, lifetime := _lifetime }) := by
          exact hinner.2.2 _x hfreshOut
        rw [henv₃]
        exact ⟨hdeclaredSafe,
          tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit,
          fun gamma _hfreshGamma =>
            borrowSafeEnv_update_fresh_borrowFree hdeclaredSafe tyBorrowFree_unit⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hshape hwellTy hwrite hranked hcoh hnotWrite _ih hsource hborrowSafe =>
      by
        have hRhsSafe := _ih (SourceTerm.assign_inner hsource) hborrowSafe
        have hwriteSafe :
            BorrowSafeEnv _env₃ :=
          hobligations.envWrite hRhsSafe.1 hRhsSafe.2.1 hLhs hRhs hshape hwellTy
            hwrite hranked hcoh hnotWrite
        exact ⟨hwriteSafe,
          tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit,
          fun _gamma _hfresh =>
          borrowSafeEnv_update_fresh_borrowFree hwriteSafe tyBorrowFree_unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm _ih hsource hborrowSafe =>
      let h := _ih (SourceTerm.block_head hsource) hborrowSafe
      ⟨h.1, h.2.1⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest _ihHead _ihRest hsource hborrowSafe =>
      by
        have hhead := _ihHead (SourceTerm.block_head hsource) hborrowSafe
        exact _ihRest (SourceTerm.block_tail hsource) hhead.1)
    htyping hsource hborrowSafe

theorem typingPreservesBorrowSafeResult {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hobligations hsource hborrowSafe htyping hfresh
  exact (typingPreservesBorrowSafeResult_global hobligations hsource
    hborrowSafe htyping).2.2 gamma hfresh

/--
Corollary 4.14, Borrow Safety.

Starting from a borrow-safe environment, the output environment extended with
the fresh result binding is both well-formed and borrow-safe.

The well-formedness half uses `borrowInvariance`, so the final result binding
coherence premise is explicit here as well.
-/
theorem borrowSafety {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hsource hrefs hvalidState hvalidStoreTyping
    hwellFormed hborrowSafe hsafe htyping hfresh hfreshCoherence
  exact ⟨
    borrowInvariance hupdateObligations hrefs hvalidState hvalidStoreTyping
      hwellFormed hsafe htyping hfresh hfreshCoherence,
      typingPreservesBorrowSafeResult hborrowObligations hsource
        hborrowSafe htyping hfresh⟩

/--
Borrow Safety through the explicit, non-axiomatic borrow-invariance route.

The borrow-safe preservation half is unchanged; the well-formedness half uses
`borrowInvariance_of_rankedAssign_and_declFreshCoherence`, so the remaining
coherence/rank obligations are explicit premises rather than hidden axioms.
-/
theorem borrowSafety_of_rankedAssign_and_declFreshCoherence
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    AssignmentRhsEdgesRanked →
    AssignmentWriteCoherenceObligations →
    DeclarationFreshUpdateCoherent →
    SourceTerm term →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hrankedAssign hwriteCoherent
    hdeclFresh hsource hrefs hvalidState hvalidStoreTyping hwellFormed hborrowSafe hsafe
    htyping hfresh hfreshCoherence
  exact ⟨
    borrowInvariance_of_rankedAssign_and_declFreshCoherence
      hupdateObligations hrankedAssign hwriteCoherent hdeclFresh hrefs hvalidState
      hvalidStoreTyping hwellFormed hsafe htyping hfresh hfreshCoherence,
    typingPreservesBorrowSafeResult hborrowObligations hsource
      hborrowSafe htyping hfresh⟩

/--
Borrow safety through the rule-carried borrow-invariance route.

The well-formedness half avoids the legacy write/fresh axioms and does not
require global assignment/declaration side predicates; those facts are attached
to the typing derivation.
-/
theorem borrowSafety_of_ruleCarriedObligations
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hsource hrefs hvalidState hvalidStoreTyping
    hwellFormed hborrowSafe hsafe htyping hfresh hfreshCoherence
  exact ⟨
    borrowInvariance_of_ruleCarriedObligations
      hupdateObligations hrefs hvalidState hvalidStoreTyping hwellFormed hsafe
      htyping hfresh hfreshCoherence,
    typingPreservesBorrowSafeResult hborrowObligations hsource
      hborrowSafe htyping hfresh⟩

/--
Source-initial Borrow Safety through the explicit, non-axiomatic
borrow-invariance route.

This is the source-program counterpart of
`borrowSafety_of_rankedAssign_and_declFreshCoherence`: the empty initial store,
environment, and store typing discharge the standard source-state premises, while
the rank/coherence obligations remain explicit instead of hidden behind legacy
axioms.
-/
theorem sourceInitial_borrowSafety_of_rankedAssign_and_declFreshCoherence
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    AssignmentRhsEdgesRanked →
    AssignmentWriteCoherenceObligations →
    DeclarationFreshUpdateCoherent →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hrankedAssign hwriteCoherent
    hdeclFresh hsource htyping hfresh hfreshCoherence
  exact borrowSafety_of_rankedAssign_and_declFreshCoherence
    hupdateObligations
    hborrowObligations
    hrankedAssign
    hwriteCoherent
    hdeclFresh
    hsource
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    borrowSafeEnv_empty
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

/-- Source-initial borrow safety through the rule-carried obligation route. -/
theorem sourceInitial_borrowSafety_of_ruleCarriedObligations
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    {gamma : Name} :
    UpdateBorrowInvariantObligations →
    BorrowSafetyPreservationObligations →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    env₂.fresh gamma →
    FreshUpdateCoherenceObligations env₂ gamma ty lifetime →
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime ∧
      BorrowSafeEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime }) := by
  intro hupdateObligations hborrowObligations hsource htyping hfresh hfreshCoherence
  exact borrowSafety_of_ruleCarriedObligations
    hupdateObligations
    hborrowObligations
    hsource
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    borrowSafeEnv_empty
    safeAbstraction_empty
    htyping
    hfresh
    hfreshCoherence

end Paper
end LwRust

