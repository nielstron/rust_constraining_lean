import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
# Lemma 4.11 (Preservation)

Paper statement (Section 4.4):

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; let `σ` be a
> store typing where `S₁ ▷ t ⊢ σ`; let `Γ₁` be a well-formed typing environment
> with respect to a lifetime `l` where `S₁ ∼ Γ₁`; let `Γ₂` be a typing
> environment; and let `T` be a type.  If `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂` and
> `⟨S₁ ▷ t ⟶* S₂ ▷ v⟩^l`, then `S₂ ▷ v` remains valid where `S₂ ∼ Γ₂` and
> `S₂ ▷ v ∼ T`.

Status: unconditional as a paper-facing statement, but it depends on explicit
sorried runtime lemmas through `runtimePreservationObligations_from_sorries`.
The assignment case is handled by the global Preservation induction and leaves
only the final assignment-redex/update obligation.  The structural cases
(value/copy/borrow/box/declare) are already proven inside `preservation`; block
still needs the term-list/block-step preservation argument.
-/

namespace LwRust
namespace Paper

open Core

/-! ### Store-update frame primitives (Appendix 9.10 support)

A move/assign updates exactly one store location.  These lemmas isolate when
such an update leaves an unrelated slot lookup and `loc` resolution unchanged.
-/

/-- Updating a location leaves the lookup at any *other* location unchanged. -/
theorem ProgramStore.slotAt_update_ne {store : ProgramStore}
    {updated location : Location} {slot : StoreSlot} :
    location ≠ updated →
    (store.update updated slot).slotAt location = store.slotAt location := by
  intro hne
  simp [ProgramStore.update, hne]

/-- `loc` for a variable lval reads no slot, so it is store-independent. -/
@[simp] theorem ProgramStore.loc_var (store : ProgramStore) (x : Name) :
    store.loc (.var x) = some (.var x) := by
  simp [ProgramStore.loc]

/--
The locations whose slots are inspected while resolving `loc store lv`.  A
variable reads nothing; a deref reads the slot at the location its source
resolves to, plus whatever the source reads.
-/
inductive LocReads (store : ProgramStore) : LVal → Location → Prop where
  | here {lv : LVal} {location : Location} :
      store.loc lv = some location →
      LocReads store (.deref lv) location
  | there {lv : LVal} {location : Location} :
      LocReads store lv location →
      LocReads store (.deref lv) location

/-- If an update misses every location `loc` reads while resolving `lv`, the
resolution is unchanged. -/
theorem loc_update_of_not_locReads {store : ProgramStore}
    {updated : Location} {slot : StoreSlot} :
    ∀ {lv : LVal} {location : Location},
      store.loc lv = some location →
      (∀ mid, LocReads store lv mid → mid ≠ updated) →
      (store.update updated slot).loc lv = some location := by
  intro lv
  induction lv with
  | var x =>
      intro location hloc _hreads
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      intro location hloc hreads
      -- resolve the source location
      cases hsource : store.loc lv with
      | none => simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          have hsourceNe : source ≠ updated :=
            hreads source (LocReads.here hsource)
          have hsource' : (store.update updated slot).loc lv = some source := by
            refine ih hsource ?_
            intro mid hmid
            exact hreads mid (LocReads.there hmid)
          -- the deref reads the slot at `source`; it is unchanged since source ≠ updated
          have hslotEq :
              (store.update updated slot).slotAt source = store.slotAt source :=
            ProgramStore.slotAt_update_ne hsourceNe
          have hlocEq :
              (store.update updated slot).loc (.deref lv) = store.loc (.deref lv) := by
            simp [ProgramStore.loc, hsource, hsource', hslotEq]
          rw [hlocEq]; exact hloc

/--
The store locations whose slots are inspected while checking
`ValidPartialValue store v ty`.  Owned (box) references read their pointee slot
and recurse; a borrow reads the slots `loc` traverses to resolve its target.
Ground values read nothing.
-/
inductive Reaches (store : ProgramStore) : PartialValue → PartialTy → Location → Prop where
  | boxHere {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      Reaches store (.value (.ref { location := location, owner := true })) (.box inner)
        location
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy} {ℓ : Location} :
      store.slotAt location = some slot →
      Reaches store slot.value inner ℓ →
      Reaches store (.value (.ref { location := location, owner := true })) (.box inner) ℓ
  | boxFullHere {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      Reaches store (.value (.ref { location := location, owner := true })) (.ty (.box ty))
        location
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty} {ℓ : Location} :
      store.slotAt location = some slot →
      Reaches store slot.value (.ty ty) ℓ →
      Reaches store (.value (.ref { location := location, owner := true })) (.ty (.box ty)) ℓ
  | borrow {location ℓ : Location} {mutable : Bool} {targets : List LVal} {target : LVal} :
      target ∈ targets →
      store.loc target = some location →
      LocReads store target ℓ →
      Reaches store (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable targets)) ℓ

/-- Frame lemma for `ValidPartialValue`: updating a location the value's
validity derivation never inspects preserves the abstraction. -/
theorem validPartialValue_update_of_not_reaches {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValue store v ty →
      (∀ ℓ, Reaches store v ty ℓ → ℓ ≠ updated) →
      ValidPartialValue (store.update updated newSlot) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit => intro _; exact ValidPartialValue.unit
  | int => intro _; exact ValidPartialValue.int
  | undef => intro _; exact ValidPartialValue.undef
  | borrow hmem hloc =>
      intro hreach
      refine ValidPartialValue.borrow hmem ?_
      refine loc_update_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hmem hloc hmidReads)
  | @box location slot inner hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated := hreach location (Reaches.boxHere hslot)
      refine ValidPartialValue.box
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]; exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxInner hslot hℓ))
  | @boxFull location slot ty hslot _hinner ih =>
      intro hreach
      have hlocNe : location ≠ updated := hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull
        (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.slotAt_update_ne hlocNe]; exact hslot
      · exact ih (fun ℓ hℓ => hreach ℓ (Reaches.boxFullInner hslot hℓ))

/-- Ground (non-reference) values inspect no store location. -/
theorem reaches_unit_false {store : ProgramStore} {ℓ : Location} :
    ¬ Reaches store (.value .unit) (.ty .unit) ℓ := by
  intro h; cases h

theorem reaches_int_false {store : ProgramStore} {n : Int} {ℓ : Location} :
    ¬ Reaches store (.value (.int n)) (.ty .int) ℓ := by
  intro h; cases h

theorem reaches_undef_false {store : ProgramStore} {ty : Ty} {ℓ : Location} :
    ¬ Reaches store .undef (.undef ty) ℓ := by
  intro h; cases h

/-- `ValidValue` specialization of the store-update frame. -/
theorem validValue_update_of_not_reaches {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} {value : Value} {ty : Ty} :
    ValidValue store value ty →
    (∀ ℓ, Reaches store (.value value) (.ty ty) ℓ → ℓ ≠ updated) →
    ValidValue (store.update updated newSlot) value ty :=
  validPartialValue_update_of_not_reaches

/-- Reverse-abstraction bridge (variable case): a store borrow reference sitting
in a variable's slot reflects an env borrow type at that variable whose target
list contains a target resolving to the referenced location. -/
theorem env_borrow_of_store_var_borrow {store : ProgramStore} {env : Env}
    {z : Name} {ℓ : Location} {lifetime : Lifetime} :
    store ∼ₛ env →
    store.slotAt (VariableProjection z) =
      some { value := .value (.ref { location := ℓ, owner := false }),
             lifetime := lifetime } →
    ∃ envSlot mutable targets target,
      env.slotAt z = some envSlot ∧
      envSlot.ty = .ty (.borrow mutable targets) ∧
      target ∈ targets ∧
      store.loc target = some ℓ := by
  intro hsafe hstoreSlot
  have hdomain : ∃ envSlot, env.slotAt z = some envSlot :=
    (hsafe.1 z).mp ⟨_, hstoreSlot⟩
  rcases hdomain with ⟨⟨envTy, envLf⟩, henvSlot⟩
  rcases hsafe.2 z _ henvSlot with ⟨value, hstoreSlot', hvalid⟩
  -- the store slot is unique, so `value` is the borrow reference
  rw [hstoreSlot] at hstoreSlot'
  simp only [Option.some.injEq, StoreSlot.mk.injEq] at hstoreSlot'
  obtain ⟨hvalueEq, _⟩ := hstoreSlot'
  subst hvalueEq
  -- a borrow reference (owner := false) is only valid at a borrow type
  cases hvalid with
  | borrow hmem hloc =>
      exact ⟨_, _, _, _, henvSlot, rfl, hmem, hloc⟩

theorem terminalStateSafe_assign_unit_of_postconditions {store : ProgramStore}
    {env : Env} :
    ValidRuntimeState store (.val .unit) →
    store ∼ₛ env →
    TerminalStateSafe store .unit env .unit := by
  intro hvalidRuntime hsafe
  exact ⟨hvalidRuntime, hsafe, ValidPartialValue.unit⟩

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

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Lemma 4.11, Preservation. -/
theorem lemma_4_11_preservation
    {store finalStore : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {finalValue : Value}
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    TerminalStateSafe finalStore finalValue env₂ ty :=
  preservation runtimePreservationObligations_from_sorries hvalid hstoreTyping
    hwellFormed hsafe htyping hmulti

end LwRust.Paper.Soundness
