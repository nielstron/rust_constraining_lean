import FWRust.Sealor.Checkers

/-!
The trivial FWRust sealor.

It discards the partial program and returns `()`, which is always well typed,
so it is (vacuously) conservative — and correspondingly useless as a prefix
checker: it accepts every prefix.  It exists to demonstrate that
conservativity alone is cheap; the value of a sealor is its precision
(see `NestedBlocks`).
-/

namespace ConservativeSealor

def emptyProgram : Program :=
  .val .unit

def emptyProgramSealor (_ : PartialProgram) : Program :=
  emptyProgram

theorem emptyProgramSealor_wellTyped_conservative :
    Conservative ProgramWellTyped CompletesProgram emptyProgramSealor := by
  intro p hInvalid full _hCompletion hFull
  exact hInvalid ⟨.unit, FWRust.Paper.Env.empty,
    FWRust.Paper.TermTyping.const FWRust.Paper.ValueTyping.unit⟩

theorem emptyProgramSealor_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CompletesProgram
      (SealorPrefixChecker programWellTyped emptyProgramSealor) := by
  exact conservative_sealors_give_complete_prefix_checkers
    emptyProgramSealor_wellTyped_conservative
    programWellTyped_complete

end ConservativeSealor
