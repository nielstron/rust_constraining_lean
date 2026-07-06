import LwRust.Extractor.Definitions
import LwRust.Extractor.PartialProgram
import LwRust.Extractor.AnnotationCompleteness
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

def RawProgramWellTyped (program : RawProgram) : Prop :=
  ProgramWellTyped (RawTerm.annotateProgram program)

def RawProgramHasWellTypedAnnotation (program : RawProgram) : Prop :=
  ∃ annotated,
    RawTerm.AnnotatesProgram program annotated ∧ ProgramWellTyped annotated

theorem rawProgramWellTyped_of_wellTypedAnnotation {program : RawProgram} :
    RawProgramHasWellTypedAnnotation program →
    RawProgramWellTyped program := by
  rintro ⟨annotated, hannotated, ty, env, htyping⟩
  rcases AnnotationCompleteness.canonical_program_typing_of_annotates
      hannotated htyping with
    ⟨envCanon, hcanonical⟩
  exact ⟨ty, envCanon, hcanonical⟩

def rawProgramWellTyped : RawProgram → Prop :=
  RawProgramWellTyped

theorem rawProgramWellTyped_complete :
    CheckerComplete RawProgramWellTyped rawProgramWellTyped := by
  intro program hprogram
  exact hprogram

end ConservativeExtractor
