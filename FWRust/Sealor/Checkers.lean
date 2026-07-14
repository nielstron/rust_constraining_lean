import FWRust.Sealor.Definitions
import FWRust.Sealor.PartialProgram
import FWRust.Paper.Typing

/-!
Shared complete-program checker predicates for sealor examples.

This is based on the FWRust typing rules.
-/

namespace ConservativeSealor

def ProgramWellTyped (program : Program) : Prop :=
  ∃ ty env,
    FWRust.Paper.TermTyping FWRust.Paper.Env.empty
      FWRust.Paper.StoreTyping.empty FWRust.Core.Lifetime.root
      program ty env

def programWellTyped : Program → Prop :=
  ProgramWellTyped

theorem programWellTyped_complete :
    CheckerComplete ProgramWellTyped programWellTyped := by
  intro program hprogram
  exact hprogram

theorem programWellTyped_sound :
    CheckerSound ProgramWellTyped programWellTyped := by
  intro program hprogram
  exact hprogram

theorem programWellTyped_exact :
    CheckerExact ProgramWellTyped programWellTyped :=
  ⟨programWellTyped_complete, programWellTyped_sound⟩

end ConservativeSealor
