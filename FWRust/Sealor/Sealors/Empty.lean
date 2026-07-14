import FWRust.Sealor.Checkers

/-!
The trivial FWRust sealor.

It discards the partial program and returns `()`, which is always well typed,
so it is (vacuously) complete — and correspondingly useless as a prefix
checker: it accepts every prefix.  It exists to demonstrate that
sealor completeness alone is cheap; the value of a sealor is its precision
(see `NestedBlocks`).
-/

namespace ConservativeSealor

def emptyProgram : Program :=
  .val .unit

def emptyProgramSealor (_ : PartialProgram) : Program :=
  emptyProgram

theorem emptyProgramSealor_complete :
    SealorComplete ProgramWellTyped CompletesProgram emptyProgramSealor := by
  intro _p _hGlobal _hCompletable
  exact ⟨.unit, FWRust.Paper.Env.empty,
    FWRust.Paper.TermTyping.const FWRust.Paper.ValueTyping.unit⟩

theorem emptyProgramSealor_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CompletesProgram
      (SealorPrefixChecker programWellTyped emptyProgramSealor) := by
  exact sealor_completeness_lifts_to_prefix_checkers
    (Class := fun _ => True)
    emptyProgramSealor_complete
    programWellTyped_complete

end ConservativeSealor
