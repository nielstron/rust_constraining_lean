import LwRust.Extractor.Definitions
import LwRust.Extractor.PartialProgram
import LwRust.Paper.Typing

/-!
Shared complete-program checker predicates for extractor examples.

This is based on the LW-Rust typing rules.
-/

namespace ConservativeExtractor

def ProgramWellTyped (program : Program) : Prop :=
  ∃ ty env,
    LwRust.Paper.TermTyping LwRust.Paper.Env.empty
      LwRust.Paper.StoreTyping.empty LwRust.Core.Lifetime.root
      program ty env

def programWellTyped : Program → Prop :=
  ProgramWellTyped

theorem programWellTyped_complete :
    CheckerComplete ProgramWellTyped programWellTyped := by
  intro program hprogram
  exact hprogram

end ConservativeExtractor
