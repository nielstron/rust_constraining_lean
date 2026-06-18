import LwRust.Paper.BorrowChecker.ExecutableSoundness
import LwRust.Paper.BorrowChecker.ExecutableCompleteness
import LwRust.Paper.Soundness.InitialStates

/-!
# Executable checker bridge to type-and-borrow safety

The executable checker itself proves accepted runs by reflecting them to
`TermTyping`.  This module packages the next step: for closed programs checked
from the empty source environment and store typing, accepted checker runs
establish the empty-initial progress, preservation, and no-stuckness interfaces
used by the soundness development.
-/

namespace LwRust
namespace Paper

open Core

def sourceValue? : Value → Bool
  | .unit => true
  | .int _ => true
  | .bool _ => true
  | .ref _ => false

def sourceTerm? (term : Term) : Bool :=
  (termValues term).all sourceValue?

theorem sourceValue?_eq_true_iff {value : Value} :
    sourceValue? value = true ↔ SourceValue value := by
  cases value <;> simp [sourceValue?, SourceValue]

theorem sourceTerm?_eq_true_iff {term : Term} :
    sourceTerm? term = true ↔ SourceTerm term := by
  unfold sourceTerm? SourceTerm
  constructor
  · intro hterm value hmem
    exact sourceValue?_eq_true_iff.mp
      (List.all_eq_true.mp hterm value hmem)
  · intro hsource
    exact List.all_eq_true.mpr (by
      intro value hmem
      exact sourceValue?_eq_true_iff.mpr (hsource value hmem))

theorem not_sourceTerm_of_sourceTerm?_false {term : Term} :
    sourceTerm? term = false → ¬ SourceTerm term := by
  intro hfalse hsource
  have htrue := sourceTerm?_eq_true_iff.mpr hsource
  rw [hfalse] at htrue
  cases htrue

/--
If a term is not source syntax, it cannot have an empty-store source typing.
This is the reusable rejection reason for runtime-only reference constants.
-/
theorem no_empty_typing_of_sourceTerm?_false {term : Term}
    {lifetime : Lifetime} :
    sourceTerm? term = false →
      ¬ ∃ ty env,
        TermTyping Env.empty StoreTyping.empty lifetime term ty env := by
  intro hnotSource htyping
  rcases htyping with ⟨ty, env, htyping⟩
  exact not_sourceTerm_of_sourceTerm?_false hnotSource
    (termTyping_empty_sourceTerm htyping)

namespace CertifiedTermReject

def ofNonSource {fuel : Nat} {lifetime : Lifetime} {term : Term}
    (checked :
      checkTermFails? fuel FiniteEnv.empty StoreTyping.empty lifetime term =
        true)
    (notSource : sourceTerm? term = false) :
    CertifiedTermReject fuel FiniteEnv.empty StoreTyping.empty lifetime term :=
  { checked := checked
    notyping := no_empty_typing_of_sourceTerm?_false notSource }

end CertifiedTermReject

namespace CertifiedBorrowReject

def ofNonSource {fuel : Nat} {term : Term}
    (checked :
      checkTermFails? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term =
        true)
    (notSource : sourceTerm? term = false) :
    CertifiedBorrowReject fuel term :=
  CertifiedBorrowReject.ofTermReject
    (CertifiedTermReject.ofNonSource checked notSource)

end CertifiedBorrowReject

def certifyBorrowRejectOfNonSource? (fuel : Nat) (term : Term) :
    Option (CertifiedBorrowReject fuel term) :=
  if hchecked :
      checkTermFails? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term =
        true then
    if hsource : sourceTerm? term = false then
      some (CertifiedBorrowReject.ofNonSource hchecked hsource)
    else
      none
  else
    none

theorem certifyBorrowRejectOfNonSource?_found_iff {fuel : Nat} {term : Term} :
    CertifiedBorrowReject.found?
        (certifyBorrowRejectOfNonSource? fuel term) = true ↔
      checkTermFails? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term =
        true ∧
        sourceTerm? term = false := by
  unfold certifyBorrowRejectOfNonSource? CertifiedBorrowReject.found?
  by_cases hchecked :
      checkTermFails? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term =
        true
  · by_cases hsource : sourceTerm? term = false <;> simp [hchecked, hsource]
  · simp [hchecked]

theorem borrowReject_of_certifyBorrowRejectOfNonSource?
    {fuel : Nat} {term : Term} :
    CertifiedBorrowReject.found?
        (certifyBorrowRejectOfNonSource? fuel term) = true →
      borrowReject term :=
  CertifiedBorrowReject.borrowReject_of_found?

theorem borrowReject_of_certifyBorrowRejectOfNonSource?_fuelBound
    {term : Term} :
    CertifiedBorrowReject.found?
        (certifyBorrowRejectOfNonSource? (termCheckerFuelBound term) term) =
          true →
      borrowReject term :=
  borrowReject_of_certifyBorrowRejectOfNonSource?
    (fuel := termCheckerFuelBound term)

syntax (name := borrow_reject_complete_tactic)
  "borrow_reject" "[" term "]" : tactic
syntax (name := borrow_reject_tactic)
  "borrow_reject" (" using " term)? : tactic

macro_rules
  | `(tactic| borrow_reject[$complete]) =>
      `(tactic|
        exact
          LwRust.Paper.borrowReject_of_borrowCheck?_eq_false_fuelBound_of_checkableComplete
            $complete (by native_decide) (by native_decide) (by native_decide))

macro_rules
  | `(tactic| borrow_reject using $certificate) =>
      `(tactic|
        first
        | exact LwRust.Paper.CertifiedBorrowReject.borrowReject $certificate
        | exact LwRust.Paper.CertifiedBorrowReject.borrowReject_of_found?
            (certificate? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowOutcome.sound $certificate
        | exact LwRust.Paper.CertifiedBorrowOutcome.sound_of_found?
            (outcome? := $certificate) (by native_decide)
        | exact $certificate)

macro_rules
  | `(tactic| borrow_reject) =>
      `(tactic|
        exact LwRust.Paper.borrowReject_of_certifyBorrowRejectOfNonSource?_fuelBound
          (by native_decide))

theorem borrowOutcomeWitness_of_certifyBorrowRejectOfNonSource?
    {fuel : Nat} {term : Term} :
    CertifiedBorrowReject.found?
        (certifyBorrowRejectOfNonSource? fuel term) = true →
      borrowOutcomeWitness fuel term
        (certifyBorrowRejectOfNonSource? fuel term) := by
  intro hfound
  cases hcertificate :
      certifyBorrowRejectOfNonSource? fuel term with
  | none =>
      simp [CertifiedBorrowReject.found?, hcertificate] at hfound
  | some certificate =>
      exact (borrowOutcome?_eq_true_iff_witness).1
        (borrowOutcome?_of_certifiedReject certificate)

theorem writeProhibited_of_slot_borrow_conflict {env : Env}
    {borrower : Name} {slot : EnvSlot} {mutable : Bool}
    {targets : List LVal} {target written : LVal}
    (hslot : env.slotAt borrower = some slot)
    (hcontains : PartialTyContains slot.ty (.borrow mutable targets))
    (hmem : target ∈ targets)
    (hconflict : target ⋈ written) :
    WriteProhibited env written := by
  cases mutable
  · right
    exact ⟨borrower, targets, target, ⟨slot, hslot, hcontains⟩,
      hmem, hconflict⟩
  · left
    exact ⟨borrower, targets, target, ⟨slot, hslot, hcontains⟩,
      hmem, hconflict⟩

theorem writeProhibited_var_after_direct_write_of_surviving_borrow
    {env result : Env} {written borrower : Name}
    {writtenSlot borrowSlot : EnvSlot} {mutable : Bool}
    {targets : List LVal} {target : LVal} {rhsTy : Ty}
    (hwrittenSlot : env.slotAt written = some writtenSlot)
    (hborrowerNe : borrower ≠ written)
    (hborrowSlot : env.slotAt borrower = some borrowSlot)
    (hcontains :
      PartialTyContains borrowSlot.ty (.borrow mutable targets))
    (hmem : target ∈ targets)
    (hconflict : target ⋈ (.var written))
    (hwrite : EnvWrite 0 env (.var written) rhsTy result) :
    WriteProhibited result (.var written) := by
  have hresult := envWrite_zero_var_eq hwrittenSlot hwrite
  subst result
  have hborrowSlot' :
      (env.update written { writtenSlot with ty := .ty rhsTy }).slotAt
        borrower = some borrowSlot := by
    rw [Env.update_slotAt_ne]
    exact hborrowSlot
    exact hborrowerNe
  exact writeProhibited_of_slot_borrow_conflict hborrowSlot'
    hcontains hmem hconflict

theorem no_assign_value_var_typing_of_surviving_borrow {env : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {written borrower : Name}
    {writtenSlot borrowSlot : EnvSlot} {mutable : Bool}
    {targets : List LVal} {target : LVal} {value : Value}
    (hwrittenSlot : env.slotAt written = some writtenSlot)
    (hborrowerNe : borrower ≠ written)
    (hborrowSlot : env.slotAt borrower = some borrowSlot)
    (hcontains :
      PartialTyContains borrowSlot.ty (.borrow mutable targets))
    (hmem : target ∈ targets)
    (hconflict : target ⋈ (.var written)) :
    ¬ ∃ ty outEnv,
      TermTyping env typing lifetime
        (.assign (.var written) (.val value)) ty outEnv := by
  rintro ⟨ty, outEnv, htyping⟩
  cases htyping with
  | assign _hLhs hRhs _hRhsSafe _hLhsPost _hshape _hwellRhs hwrite
      _hranked _hcoherence _hcontained hnotWrite =>
      cases hRhs with
      | const _hvalue =>
          exact hnotWrite
            (writeProhibited_var_after_direct_write_of_surviving_borrow
              hwrittenSlot hborrowerNe hborrowSlot hcontains hmem
              hconflict hwrite)

/--
An accepted proof-facing checker result establishes the reusable sound-state
invariant for the empty initial runtime store.
-/
theorem borrowCheck_emptyInitial_soundState {term : Term} :
    borrowCheck term → SoundState ProgramStore.empty Lifetime.root term := by
  rintro ⟨ty, env, htyping⟩
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, hwellFormed,
      _hstoreProgress, _hrefs⟩
  exact SoundState.initial
    (termTyping_empty_sourceTerm htyping)
    hvalidRuntime
    hvalidStoreTyping
    (hwellFormed Lifetime.root)
    hsafe
    ProgramStore.finiteSupport_empty
    htyping

/--
The executable checker directly supplies the sound-state invariant whenever
`borrowCheck?` accepts.
-/
theorem borrowCheck?_emptyInitial_soundState {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true →
      SoundState ProgramStore.empty Lifetime.root term := by
  intro hcheck
  exact borrowCheck_emptyInitial_soundState (borrowCheck?_sound hcheck)

/--
Proof-facing checker acceptance entails empty-initial progress.
-/
theorem borrowCheck_emptyInitial_progress {term : Term} :
    borrowCheck term →
      ProgressResult ProgramStore.empty Lifetime.root term := by
  intro hcheck
  exact (borrowCheck_emptyInitial_soundState hcheck).progress

/--
Executable checker acceptance entails empty-initial progress.
-/
theorem borrowCheck?_emptyInitial_progress {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true →
      ProgressResult ProgramStore.empty Lifetime.root term := by
  intro hcheck
  exact borrowCheck_emptyInitial_progress (borrowCheck?_sound hcheck)

/--
Proof-facing checker acceptance entails terminal preservation for any terminal
run from the empty initial store.
-/
theorem borrowCheck_emptyInitial_preservation {term : Term}
    {finalStore : ProgramStore} {finalValue : Value} :
    borrowCheck term →
      MultiStep ProgramStore.empty Lifetime.root term finalStore
        (.val finalValue) →
        ∃ ty env, TerminalStateSafe finalStore finalValue env ty := by
  rintro ⟨ty, env, htyping⟩ hmulti
  exact ⟨ty, env, emptyInitial_preservation htyping hmulti⟩

/--
Executable checker acceptance entails terminal preservation for any terminal
run from the empty initial store.
-/
theorem borrowCheck?_emptyInitial_preservation {fuel : Nat} {term : Term}
    {finalStore : ProgramStore} {finalValue : Value} :
    borrowCheck? fuel term = true →
      MultiStep ProgramStore.empty Lifetime.root term finalStore
        (.val finalValue) →
        ∃ ty env, TerminalStateSafe finalStore finalValue env ty := by
  intro hcheck
  exact borrowCheck_emptyInitial_preservation (borrowCheck?_sound hcheck)

/--
Proof-facing checker acceptance entails no-stuckness for every state reachable
from the empty initial store.
-/
theorem borrowCheck_emptyInitial_no_stuck_states {term term' : Term}
    {store' : ProgramStore} :
    borrowCheck term →
      MultiStep ProgramStore.empty Lifetime.root term store' term' →
        Terminal term' ∨
          ∃ store'' term'', Step store' Lifetime.root term' store'' term'' := by
  rintro ⟨ty, env, htyping⟩ hreach
  exact emptyInitial_no_stuck_states htyping hreach

/--
Executable checker acceptance entails no-stuckness for every state reachable
from the empty initial store.
-/
theorem borrowCheck?_emptyInitial_no_stuck_states {fuel : Nat}
    {term term' : Term} {store' : ProgramStore} :
    borrowCheck? fuel term = true →
      MultiStep ProgramStore.empty Lifetime.root term store' term' →
        Terminal term' ∨
          ∃ store'' term'', Step store' Lifetime.root term' store'' term'' := by
  intro hcheck
  exact borrowCheck_emptyInitial_no_stuck_states (borrowCheck?_sound hcheck)

/--
Proof-facing checker acceptance composes with the conditional terminal-safety
form of Theorem 4.12 for empty-initial programs.
-/
theorem borrowCheck_emptyInitial_typeAndBorrowSafety {term : Term} :
    borrowCheck term →
      TerminatesAsValue ProgramStore.empty Lifetime.root term →
        ProgressResult ProgramStore.empty Lifetime.root term ∧
          ∃ finalStore finalValue ty env,
            MultiStep ProgramStore.empty Lifetime.root term finalStore
              (.val finalValue) ∧
              TerminalStateSafe finalStore finalValue env ty := by
  rintro ⟨ty, env, htyping⟩ hterminates
  rcases emptyInitial_typeAndBorrowSafety htyping hterminates with
    ⟨hprogress, finalStore, finalValue, hmulti, hsafe⟩
  exact ⟨hprogress, finalStore, finalValue, ty, env, hmulti, hsafe⟩

/--
Executable checker acceptance composes with the conditional terminal-safety
form of Theorem 4.12 for empty-initial programs.
-/
theorem borrowCheck?_emptyInitial_typeAndBorrowSafety {fuel : Nat}
    {term : Term} :
    borrowCheck? fuel term = true →
      TerminatesAsValue ProgramStore.empty Lifetime.root term →
        ProgressResult ProgramStore.empty Lifetime.root term ∧
          ∃ finalStore finalValue ty env,
            MultiStep ProgramStore.empty Lifetime.root term finalStore
              (.val finalValue) ∧
              TerminalStateSafe finalStore finalValue env ty := by
  intro hcheck
  exact borrowCheck_emptyInitial_typeAndBorrowSafety (borrowCheck?_sound hcheck)

end Paper
end LwRust
