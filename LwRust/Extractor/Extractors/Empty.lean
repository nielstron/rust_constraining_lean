import LwRust.Extractor.Checkers

/-!
The trivial LwRust extractor.

It discards the partial program and returns `()`, which is always well typed,
so it is (vacuously) conservative — and correspondingly useless as a prefix
checker: it accepts every prefix.  It exists to demonstrate that
conservativity alone is cheap; the value of an extractor is its precision
(see `NestedBlocks`).
-/

namespace ConservativeExtractor

def emptyProgram : RawProgram :=
  .val .unit

def emptyProgramExtractor (_ : PartialProgram) : RawProgram :=
  emptyProgram

theorem emptyProgramExtractor_wellTyped_conservative :
    Conservative RawProgramWellTyped CompletesProgram emptyProgramExtractor := by
  intro p hInvalid full _hCompletion hFull
  exact hInvalid ⟨.unit, LwRust.Paper.Env.empty, by
    simpa [RawProgramWellTyped, RawTerm.annotateProgram, RawTerm.annotate,
      emptyProgram, emptyProgramExtractor] using
      (LwRust.Paper.TermTyping.const LwRust.Paper.ValueTyping.unit)⟩

theorem emptyProgramExtractor_prefixChecker_complete :
    PrefixCheckerComplete RawProgramWellTyped CompletesProgram
      (ExtractorPrefixChecker rawProgramWellTyped emptyProgramExtractor) := by
  exact conservative_extractors_give_complete_prefix_checkers
    emptyProgramExtractor_wellTyped_conservative
    rawProgramWellTyped_complete

end ConservativeExtractor
