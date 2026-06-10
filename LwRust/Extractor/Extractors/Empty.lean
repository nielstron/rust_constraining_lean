import LwRust.Extractor.Checkers

/-!
The trivial LwRust extractor.

The conservativeness proofs are deliberately left as `sorry` placeholders,
matching the current state of the copied extractor work.
-/

namespace ConservativeExtractor

def emptyProgram : Program :=
  .val .unit

def emptyProgramExtractor (_ : PartialProgram) : Program :=
  emptyProgram

theorem emptyProgramExtractor_wellTyped_conservative :
    Conservative ProgramWellTyped CompletesProgram emptyProgramExtractor := by
  sorry

theorem emptyProgramExtractor_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CompletesProgram
      (ExtractorPrefixChecker programWellTyped emptyProgramExtractor) := by
  exact conservative_extractors_give_complete_prefix_checkers
    emptyProgramExtractor_wellTyped_conservative
    programWellTyped_complete

end ConservativeExtractor
