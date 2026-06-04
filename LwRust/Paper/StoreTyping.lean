import LwRust.Paper.BorrowChecker
import LwRust.Paper.InductiveSemantics

/-!
Store and environment abstraction predicates used by the paper proof.
-/

namespace LwRust
namespace Paper

open Core

/--
Paper Definitions 4.1 and 4.3 (Valid Term / Valid State), helper for collecting
owned references from a reference value.
-/
def ownerRefsInReference (ref : Reference) : List Reference :=
  if ref.owner then [ref] else []

mutual
  /--
  Paper Definitions 4.1 and 4.3 (Valid Term / Valid State), helper for the
  sequence of owned references contained in a runtime value.
  -/
  def ownerRefsInValue : Value → List Reference
    | .unit => []
    | .int _ => []
    | .ref ref => ownerRefsInReference ref
    | .tuple fields => ownerRefsInValues fields
    | .moved => []

  /--
  Paper Definitions 4.1 and 4.3 (Valid Term / Valid State), list version of
  `ownerRefsInValue`.
  -/
  def ownerRefsInValues : List Value → List Reference
    | [] => []
    | value :: values => ownerRefsInValue value ++ ownerRefsInValues values
end

mutual
  /--
  Paper Definition 4.1 (Valid Term), helper for collecting owned references
  contained in a term.
  -/
  def ownerRefsInTerm : Term → List Reference
    | .val value => ownerRefsInValue value
    | .letMut _ initialiser => ownerRefsInTerm initialiser
    | .assign _ rhs => ownerRefsInTerm rhs
    | .block _ terms => ownerRefsInTerms terms
    | .access _ _ => []
    | .borrow _ _ => []
    | .box operand => ownerRefsInTerm operand
    | .tuple terms => ownerRefsInTerms terms
    | .ifElse _ lhs rhs trueBlock falseBlock =>
        ownerRefsInTerm lhs ++ ownerRefsInTerm rhs ++
          ownerRefsInTerm trueBlock ++ ownerRefsInTerm falseBlock
    | .invoke _ args => ownerRefsInTerms args

  /--
  Paper Definition 4.1 (Valid Term), list version of `ownerRefsInTerm`.
  -/
  def ownerRefsInTerms : List Term → List Reference
    | [] => []
    | term :: terms => ownerRefsInTerm term ++ ownerRefsInTerms terms
end

/--
Paper Definition 4.2 (Valid Store), helper for collecting owned references from
a store cell.
-/
def ownerRefsInCell (cell : Cell) : List Reference :=
  match cell.value with
  | none => []
  | some value => ownerRefsInValue value

/--
Paper Definition 4.2 (Valid Store), helper for collecting owned references from
the heap.
-/
def ownerRefsInHeap : List (Nat × Cell) → List Reference
  | [] => []
  | (_, cell) :: rest => ownerRefsInCell cell ++ ownerRefsInHeap rest

/--
Paper Definitions 4.2 and 4.3 (Valid Store / Valid State), helper for
collecting owned references from the runtime state.
-/
def ownerRefsInState (state : State) : List Reference :=
  (state.vars.map Prod.snd).filter (fun ref => ref.owner) ++ ownerRefsInHeap state.heap

/--
Paper Definitions 4.1, 4.2, and 4.3 encode validity as pairwise disjointness of
owned references.
-/
def PairwiseDisjoint [BEq α] (values : List α) : Prop :=
  ∀ a, values.countP (fun b => b == a) ≤ 1

/--
Paper Definition 4.5 (Valid Store Typing), represented as a finite-address type
assignment for heap cells.
-/
structure StoreTyping where
  tyOf : Nat → Option Ty

mutual
  /--
  Paper Definition 4.4 (Valid Type), store-aware abstraction for complete
  runtime values.
  -/
  inductive ValueAbstracts (state : State) : Value → Ty → Prop where
    | unit : ValueAbstracts state .unit Ty.unit
    | int (n : Int) : ValueAbstracts state (.int n) Ty.int
    | tuple {values : List Value} {tys : List Ty} :
        ValuesAbstract state values tys →
        ValueAbstracts state (.tuple values) (.tuple tys)
    | box {ref : Reference} {cell : Cell} {ty : Ty} :
        ref.owner = true →
        state.getCell ref.address = some cell →
        PartialValueAbstracts state cell.value ty →
        ValueAbstracts state (.ref ref) (.box ty)
    | borrow {ref : Reference} {mutable : Bool} {lvals : List LVal} {lv : LVal} :
        ref.owner = false →
        lv ∈ lvals →
        locate state lv = .ok ref →
        ValueAbstracts state (.ref ref) (.borrow mutable lvals)

  /--
  Paper Definition 4.4 (Valid Type), list version for tuple fields.
  -/
  inductive ValuesAbstract (state : State) : List Value → List Ty → Prop where
    | nil : ValuesAbstract state [] []
    | cons {value : Value} {values : List Value} {ty : Ty} {tys : List Ty} :
        ValueAbstracts state value ty →
        ValuesAbstract state values tys →
        ValuesAbstract state (value :: values) (ty :: tys)

  /--
  Paper Definition 4.4 (Valid Type), partial-value abstraction including
  deallocated and moved values.
  -/
  inductive PartialValueAbstracts (state : State) : Option Value → Ty → Prop where
    | none {ty : Ty} :
        PartialValueAbstracts state none (.undef ty)
    | moved {ty : Ty} :
        PartialValueAbstracts state (some .moved) (.undef ty)
    | some {value : Value} {ty : Ty} :
        ValueAbstracts state value ty →
        PartialValueAbstracts state (some value) ty
end

/--
Paper Definition 4.1 (Valid Term).
-/
def ValidTerm (term : Term) : Prop :=
  PairwiseDisjoint (ownerRefsInTerm term)

/--
Paper Definition 4.3 (Valid State).
-/
def ValidState (state : State) (term : Term) : Prop :=
  PairwiseDisjoint (ownerRefsInState state ++ ownerRefsInTerm term)

/--
Paper Definition 4.5 (Valid Store Typing), single heap-cell obligation.
-/
def StoreAbstractsCell (state : State) (storeTyping : StoreTyping) (entry : Nat × Cell) : Prop :=
  ∀ ty, storeTyping.tyOf entry.fst = some ty → PartialValueAbstracts state entry.snd.value ty

/--
Paper Definition 4.5 (Valid Store Typing).

TODO: This captures Definition 4.4 for heap cells locally, but does not yet
account for the paper's full store typing over all distinct values occurring in
the term and store.
-/
def StoreAbstracts (state : State) (_term : Term) (storeTyping : StoreTyping) : Prop :=
  ∀ entry, entry ∈ state.heap → StoreAbstractsCell state storeTyping entry

/--
Paper Definition 4.8 (Well-formed Environment).

Each environment slot must outlive the ambient lifetime, matching the direction
used by the paper checker's within/references-within predicates.
-/
def WellFormedEnv (_state : State) (env : Env) (lifetime : Lifetime) : Prop :=
  ∀ entry,
    entry ∈ env →
    entry.snd.lifetime.contains lifetime ∧
      BorrowChecker.RefsWithin env entry.snd.lifetime entry.snd.ty

/--
Paper Definition 4.7 (Safe Abstraction), implementation artifact.

These checker-only names are introduced for tuple and conditional temporaries;
they have type-environment entries but no runtime store cells.
-/
def TypeOnlyName (x : Name) : Prop :=
  x.startsWith "?" = true

theorem type_only_generated (n : Nat) :
    TypeOnlyName ("?" ++ toString n) := by
  simp [TypeOnlyName]

theorem type_only_generated_for_env (env : Env) :
    TypeOnlyName ("?" ++ toString env.length) := by
  simp [TypeOnlyName]

/--
Paper Definition 4.7 (Safe Abstraction).

The Lean version additionally permits checker-only temporary names such as
`?0`; those names exist only in the type environment and have no runtime cell.
-/
def EnvAbstracts (state : State) (env : Env) : Prop :=
  ∀ x slot,
    Env.get env x = some slot →
    TypeOnlyName x ∨
      ∃ ref cell,
        state.getVar x = some ref ∧
        state.getCell ref.address = some cell ∧
        cell.lifetime = slot.lifetime ∧
        PartialValueAbstracts state cell.value slot.ty

/--
Support lemma for Paper Definition 4.8 (Well-formed Environment).
-/
theorem well_formed_empty {state : State} {lifetime : Lifetime} :
    WellFormedEnv state Env.empty lifetime := by
  intro entry hmem
  cases hmem

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction).
-/
theorem env_abstracts_empty {state : State} :
    EnvAbstracts state Env.empty := by
  intro x slot hget
  cases hget

/--
Support lemma for Paper Corollary 9.4 (Read Preservation).
-/
theorem partial_value_defined {state : State} {value : Value} {ty : Ty} :
    PartialValueAbstracts state (some value) ty →
    BorrowChecker.TyDefined ty →
    ValueAbstracts state value ty := by
  intro hpartial hdefined
  cases hpartial with
  | moved =>
      cases hdefined
  | some hvalue =>
      exact hvalue

/--
Support lemma for Paper Corollary 9.4 (Read Preservation).

Live partial values are complete value abstractions.
-/
theorem partial_value_live {state : State} {value : Value} {ty : Ty} :
    PartialValueAbstracts state (some value) ty →
    value ≠ .moved →
    ValueAbstracts state value ty := by
  intro h hlive
  cases h with
  | moved =>
      exact False.elim (hlive rfl)
  | some hv =>
      exact hv

mutual
  /--
  Support lemma for Paper Lemma 9.7 (Value Typing).

  Complete value abstraction preserves tuple arity.
  -/
  theorem value_abstract_preserves_tuple_arity {state : State} {value : Value} {ty : Ty} :
      ValueAbstracts state value ty →
      match value, ty with
      | .tuple values, .tuple tys => values.length = tys.length
      | _, _ => True := by
    intro h
    cases h with
    | unit => trivial
    | int _ => trivial
    | tuple hvalues =>
        exact values_abstract_length hvalues
    | box _ _ _ => trivial
    | borrow _ _ _ => trivial

  /--
  Support lemma for Paper Lemma 9.7 (Value Typing), list form.
  -/
  theorem values_abstract_length {state : State} {values : List Value} {tys : List Ty} :
      ValuesAbstract state values tys →
      values.length = tys.length := by
    intro h
    cases h with
    | nil => rfl
    | cons _ hvalues =>
        simp [values_abstract_length hvalues]
end

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction).
-/
theorem env_abstracts_get {state : State} {env : Env} {x : Name} {slot : Slot} :
    EnvAbstracts state env →
    Env.get env x = some slot →
    TypeOnlyName x ∨
    ∃ ref cell,
      state.getVar x = some ref ∧
      state.getCell ref.address = some cell ∧
      cell.lifetime = slot.lifetime ∧
      PartialValueAbstracts state cell.value slot.ty := by
  intro henv hget
  exact henv x slot hget

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction), runtime-name case.
-/
theorem env_abstracts_runtime_get {state : State} {env : Env} {x : Name} {slot : Slot} :
    EnvAbstracts state env →
    ¬ TypeOnlyName x →
    Env.get env x = some slot →
    ∃ ref cell,
      state.getVar x = some ref ∧
      state.getCell ref.address = some cell ∧
      cell.lifetime = slot.lifetime ∧
      PartialValueAbstracts state cell.value slot.ty := by
  intro henv hnotTemp hget
  cases henv x slot hget with
  | inl htemp => exact False.elim (hnotTemp htemp)
  | inr hruntime => exact hruntime

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction), erasure lookup.
-/
theorem env_get_erase_of_get_ne {env : Env} {x y : Name} {slot : Slot} :
    y ≠ x →
    Env.get (Env.erase env x) y = some slot →
    Env.get env y = some slot := by
  intro hyx
  unfold Env.erase
  induction env with
  | nil =>
      simp [Env.get]
  | cons entry rest ih =>
      cases entry with
      | mk z s =>
          by_cases hz : z = x
          · subst hz
            simp [Env.get, hyx]
            intro hget
            exact ih hget
          · simp [Env.get, hz]
            intro hget
            by_cases hyz : y = z
            · simp [hyz]
              simp [hyz] at hget
              exact hget
            · simp [hyz]
              simp [hyz] at hget
              exact ih hget

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction), update lookup.
-/
theorem env_get_put_same {env : Env} {x : Name} {slot : Slot} :
    Env.get (Env.put env x slot) x = some slot := by
  unfold Env.put
  simp [Env.get]

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction), update lookup.
-/
theorem env_get_put_of_ne {env : Env} {x y : Name} {slot result : Slot} :
    y ≠ x →
    Env.get (Env.put env x slot) y = some result →
    Env.get env y = some result := by
  intro hyx hget
  unfold Env.put at hget
  simp [Env.get, hyx] at hget
  exact env_get_erase_of_get_ne hyx hget

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction), erasure lookup.
-/
theorem env_get_erase_self (env : Env) (x : Name) :
    Env.get (Env.erase env x) x = none := by
  unfold Env.erase
  induction env with
  | nil =>
      simp [Env.get]
  | cons entry rest ih =>
      cases entry with
      | mk z s =>
          by_cases hzx : z = x
          · subst hzx
            simp [ih]
          · have hxz : x ≠ z := fun h => hzx h.symm
            simp [Env.get, hzx, hxz, ih]

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction), erasure lookup.

Any successful lookup after erasure was already a successful lookup before
erasure.
-/
theorem env_get_of_get_erase {env : Env} {x y : Name} {slot : Slot} :
    Env.get (Env.erase env x) y = some slot →
    Env.get env y = some slot := by
  intro hget
  by_cases hyx : y = x
  · subst hyx
    rw [env_get_erase_self] at hget
    cases hget
  · exact env_get_erase_of_get_ne hyx hget

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction).

Adding a checker-only temporary preserves the runtime abstraction relation.
-/
theorem env_abstracts_put_type_only {state : State} {env : Env} {x : Name} {slot : Slot} :
    EnvAbstracts state env →
    TypeOnlyName x →
    EnvAbstracts state (Env.put env x slot) := by
  intro henv hx y yslot hget
  unfold Env.put at hget
  simp [Env.get] at hget
  by_cases hyx : y = x
  · subst hyx
    left
    exact hx
  · have hgetErase : Env.get (Env.erase env x) y = some yslot := by
      simpa [hyx] using hget
    exact henv y yslot (env_get_erase_of_get_ne hyx hgetErase)

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction).

Erasing a checker environment entry preserves safe abstraction.
-/
theorem env_abstracts_erase {state : State} {env : Env} {x : Name} :
    EnvAbstracts state env →
    EnvAbstracts state (Env.erase env x) := by
  intro henv y slot hget
  exact henv y slot (env_get_of_get_erase hget)

/--
Support lemma for Paper Definition 4.7 (Safe Abstraction).

Removing several checker environment entries preserves safe abstraction.
-/
theorem env_abstracts_remove_many {state : State} {env : Env} {xs : List Name} :
    EnvAbstracts state env →
    EnvAbstracts state (Env.removeMany env xs) := by
  intro henv
  induction xs generalizing env with
  | nil =>
      simpa [Env.removeMany] using henv
  | cons x xs ih =>
      simpa [Env.removeMany] using ih (env_abstracts_erase (state := state) (env := env) (x := x) henv)

/--
Support lemma for Paper Lemma 4.9 (Borrow Invariance).
-/
theorem well_formed_put_type_only {state : State} {env : Env} {x : Name} {slot : Slot}
    {lifetime : Lifetime} :
    WellFormedEnv state env lifetime →
    TypeOnlyName x →
    slot.lifetime.contains lifetime →
    BorrowChecker.RefsWithin (Env.put env x slot) slot.lifetime slot.ty →
    WellFormedEnv state (Env.put env x slot) lifetime := by
  intro hwf _ hcontains hrefs entry hmem
  simp [Env.put] at hmem
  rcases hmem with rfl | htail
  · exact ⟨hcontains, hrefs⟩
  · have hin : entry ∈ env := (List.mem_filter.mp htail).1
    rcases hwf entry hin with ⟨hlifetime, _⟩
    exact ⟨hlifetime, trivial⟩

/--
Paper Lemma 9.7 (Value Typing), restricted to the part currently formalized:
checking a runtime value does not change the type environment.
-/
theorem value_typing {env env' : Env} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    Checks env lifetime (.val value) env' ty →
    env' = env := by
  intro h
  cases h <;> rfl

/--
Paper Lemma 9.3 (Location Lemma), variable case.

TODO: This case is stated separately because checker-only names are permitted
in `EnvAbstracts`; a runtime-name premise is needed to rule those out.
-/
theorem location_var {state : State} {env : Env} {x : Name} {ty : Ty}
    {ambientLifetime targetLifetime : Lifetime} :
    EnvAbstracts state env →
    WellFormedEnv state env ambientLifetime →
    BorrowChecker.TypeOf env (LVal.var x) ty targetLifetime →
    ∃ ref cell,
      locate state (LVal.var x) = .ok ref ∧
      state.getCell ref.address = some cell ∧
      PartialValueAbstracts state cell.value ty := by
  -- TODO: This is immediate from `EnvAbstracts` for runtime names.  The current
  -- statement still allows checker-only names, which have no runtime location.
  sorry

/--
Paper Lemma 9.3 (Location Lemma).

If an l-value has a type in the borrow-checker environment, then locating the
same l-value in an abstracting runtime state succeeds and reaches a cell whose
partial value abstracts that type.
-/
theorem location {state : State} {env : Env} {lv : LVal} {ty : Ty}
    {ambientLifetime targetLifetime : Lifetime} :
    EnvAbstracts state env →
    WellFormedEnv state env ambientLifetime →
    BorrowChecker.TypeOf env lv ty targetLifetime →
    ∃ ref cell,
      locate state lv = .ok ref ∧
      state.getCell ref.address = some cell ∧
      PartialValueAbstracts state cell.value ty := by
  -- TODO: Port paper Lemma 9.3.  The proof follows the structure of
  -- `BorrowChecker.TypeOf` and `locate`, using
  -- `EnvAbstracts` for variables and `ValueAbstracts.borrow` for dereferences.
  sorry

/--
Paper Corollary 9.4 (Read Preservation).

Reading a well-typed, defined l-value from an abstracting runtime state returns
a value abstracting the borrow-checker type.
-/
theorem read_preservation {state : State} {env : Env} {lv : LVal} {ty : Ty}
    {ambientLifetime targetLifetime : Lifetime} :
    EnvAbstracts state env →
    WellFormedEnv state env ambientLifetime →
    BorrowChecker.TypeOf env lv ty targetLifetime →
    BorrowChecker.TyDefined ty →
    ∃ value,
      state.readLVal lv = .ok value ∧
      ValueAbstracts state value ty := by
  -- TODO: Port paper Corollary 9.4 from `location`; the `defined` premise rules
  -- out `none` and `moved` partial values.
  sorry

/--
Support lemma for Paper Lemma 4.10 (Progress), move-write case.
-/
theorem move_write_progress {state : State} {env : Env} {lv : LVal} {ty : Ty}
    {ambientLifetime targetLifetime : Lifetime} :
    EnvAbstracts state env →
    WellFormedEnv state env ambientLifetime →
    BorrowChecker.TypeOf env lv ty targetLifetime →
    BorrowChecker.TyDefined ty →
    BorrowChecker.WriteAllowed env lv →
    ∃ state', state.writeLVal lv none = .ok state' := by
  -- TODO: This is the write side of progress for moves.  It should follow from
  -- `location`, absence of write-prohibiting borrows, and definedness of the
  -- target value.
  sorry

/--
Support lemma for Paper Lemma 4.10 (Progress), assignment-write case.
-/
theorem assign_write_progress {state : State} {env : Env} {lv : LVal} {ty : Ty}
    {value : Value} {ambientLifetime targetLifetime : Lifetime} :
    EnvAbstracts state env →
    WellFormedEnv state env ambientLifetime →
    BorrowChecker.TypeOf env lv ty targetLifetime →
    BorrowChecker.TyDefined ty →
    BorrowChecker.WriteAllowed env lv →
    ValueAbstracts state value ty →
    ∃ state', state.writeLVal lv (some value) = .ok state' := by
  -- TODO: Port the assignment-write case of progress; this is the same location
  -- argument as `move_write_progress`, with `Value.writePath` preserving shape.
  sorry

end Paper
end LwRust
