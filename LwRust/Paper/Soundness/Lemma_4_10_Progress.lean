import LwRust.Paper.Soundness.Helpers.ValuePreservation

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
theorem progress_assign_value_typing {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {current lifetime : Lifetime} {lhs : LVal}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    OperationalStoreProgress store →
    TermTyping env typing lifetime (.assign lhs (.val value)) ty env₂ →
    ProgressResult store lifetime (.assign lhs (.val value)) := by
  intro hwellFormed hsafe hstore htyping
  cases htyping with
  | assign _hLhs hRhs hLhsPost hshape _hwf _hwriteEnv _hranked _hcoh
      _hcontained _hnotWriteProhibited =>
      cases hRhs with
      | const _hvalue =>
          rcases read_defined_of_allocated
              (lvalTyping_allocated_location hwellFormed hsafe hLhsPost) with
            ⟨oldSlot, hread⟩
          exact progress_assign_value hstore hread

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

The paper states well-formedness for the current lifetime; blocks step their
body under the block lifetime, where well-formedness follows from the
enclosing lifetime by downward monotonicity (`WellFormedEnv.of_outlives`).
-/
theorem progress_typing {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    OperationalStoreProgress store →
    TermTyping env₁ typing lifetime term ty env₂ →
    ProgressResult store lifetime term := by
  intro hwellFormed hsafe hstore htyping
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty env₂ _ =>
      WellFormedEnv env lifetime →
      store ∼ₛ env →
      OperationalStoreProgress store →
      ProgressResult store lifetime term)
    (motive_2 := fun env typing blockLifetime terms ty env₂ _ =>
      ∀ lifetime,
        WellFormedEnv env blockLifetime →
        store ∼ₛ env →
        OperationalStoreProgress store →
        ProgressResult store lifetime (.block blockLifetime terms))
    (fun {_env _typing lifetime value _ty} _hvalue hwellFormed hsafe hstore =>
      progress_value store lifetime value)
    (fun {_env _typing lifetime _valueLifetime _lv _ty} hLv hcopy hreadProhibited
        hwellFormed hsafe _hstore =>
      progress_copy_typing (typing := _typing) hwellFormed hsafe
        (TermTyping.copy (typing := _typing) hLv hcopy hreadProhibited))
    (fun {_env₁ _env₂ _typing lifetime _valueLifetime _lv _ty} hLv hwriteProhibited hmove
        hwellFormed hsafe _hstore =>
      progress_move_typing (typing := _typing) hwellFormed hsafe
        (TermTyping.move (typing := _typing) hLv hwriteProhibited hmove))
    (fun {_env _typing lifetime _valueLifetime _lv _ty} hLv hmutable hwriteProhibited
        hwellFormed hsafe _hstore =>
      progress_borrow_typing (typing := _typing) hwellFormed hsafe
        (TermTyping.mutBorrow (typing := _typing) hLv hmutable hwriteProhibited))
    (fun {_env _typing lifetime _valueLifetime _lv _ty} hLv hreadProhibited
        hwellFormed hsafe _hstore =>
      progress_borrow_typing (typing := _typing) hwellFormed hsafe
        (TermTyping.immBorrow (typing := _typing) hLv hreadProhibited))
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} hterm ih
        hwellFormed hsafe hstore =>
      progress_box_typing hstore (TermTyping.box hterm)
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _env₃ _typing lifetime _blockLifetime _terms _ty}
        hblockChild _hterms _hwellTy _hdrop ih hwellFormed hsafe hstore =>
      ih lifetime
        (WellFormedEnv.of_outlives hwellFormed (LifetimeChild.outlives hblockChild))
        hsafe hstore)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfresh hterm hfreshOut hcoh henv ih
        hwellFormed hsafe hstore =>
      progress_declare_typing (TermTyping.declare hfresh hterm hfreshOut hcoh henv)
        (ih hwellFormed hsafe hstore))
    (fun {_env₁ _env₂ _env₃ _typing lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hLhsPost hshape hwf hwrite hranked hcoh hcontained
        hnotWriteProhibited ih
        hwellFormed hsafe hstore =>
      progress_assign_typing hwellFormed hsafe hstore
        (TermTyping.assign hLhs hRhs hLhsPost hshape hwf hwrite hranked hcoh
          hcontained hnotWriteProhibited)
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
    WellFormedEnv env₁ blockLifetime →
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
    WellFormedEnv env₁ lifetime →
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
