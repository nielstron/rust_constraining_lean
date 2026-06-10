import LwRust.Extractor.Definitions
import LwRust.Extractor.PartialProgram
import LwRust.Paper.Typing

/-!
The trivial LwRust extractor.

The semantic checker predicates below are the intended integration points with
the LwRust typing/borrow-safety development.  Their final completeness and
conservativeness proofs are deliberately left as `sorry` placeholders, matching
the current state of the copied extractor work.
-/

namespace ConservativeExtractor

def emptyProgram : Program :=
  .val .unit

def emptyProgramExtractor (_ : PartialProgram) : Program :=
  emptyProgram

def ProgramWellTyped (program : Program) : Prop :=
  ∃ ty env,
    LwRust.Paper.TermTyping LwRust.Paper.Env.empty
      LwRust.Paper.StoreTyping.empty LwRust.Core.Lifetime.root
      program ty env

def ProgramBorrowOk (_program : Program) : Prop :=
  True

def ProgramLifetimeBorrowOk (program : Program) : Prop :=
  ProgramWellTyped program ∧ ProgramBorrowOk program

def exactProgramChecker : Program → Prop :=
  ProgramWellTyped

def exactBorrowChecker : Program → Prop :=
  ProgramBorrowOk

def exactLifetimeBorrowChecker : Program → Prop :=
  ProgramLifetimeBorrowOk

theorem exactProgramChecker_complete :
    CheckerComplete ProgramWellTyped exactProgramChecker := by
  intro program hprogram
  exact hprogram

theorem exactBorrowChecker_complete :
    CheckerComplete ProgramBorrowOk exactBorrowChecker := by
  intro program hprogram
  exact hprogram

theorem exactLifetimeBorrowChecker_complete :
    CheckerComplete ProgramLifetimeBorrowOk exactLifetimeBorrowChecker := by
  intro program hprogram
  exact hprogram

theorem emptyProgramExtractor_wellTyped_conservative :
    Conservative ProgramWellTyped CompletesProgram emptyProgramExtractor := by
  sorry

theorem emptyProgramExtractor_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CompletesProgram
      (ExtractorPrefixChecker exactProgramChecker emptyProgramExtractor) := by
  exact conservative_extractors_give_complete_prefix_checkers
    emptyProgramExtractor_wellTyped_conservative
    exactProgramChecker_complete

theorem emptyProgramExtractor_borrow_conservative :
    Conservative ProgramBorrowOk CompletesProgram emptyProgramExtractor := by
  intro p hInvalid full hCompletes hFull
  exact hInvalid trivial

theorem emptyProgramExtractor_borrow_prefixChecker_complete :
    PrefixCheckerComplete ProgramBorrowOk CompletesProgram
      (ExtractorPrefixChecker exactBorrowChecker emptyProgramExtractor) := by
  exact conservative_extractors_give_complete_prefix_checkers
    emptyProgramExtractor_borrow_conservative
    exactBorrowChecker_complete

theorem emptyProgramExtractor_lifetimeBorrow_conservative :
    Conservative ProgramLifetimeBorrowOk CompletesProgram
      emptyProgramExtractor := by
  sorry

theorem emptyProgramExtractor_lifetimeBorrow_prefixChecker_complete :
    PrefixCheckerComplete ProgramLifetimeBorrowOk CompletesProgram
      (ExtractorPrefixChecker exactLifetimeBorrowChecker
        emptyProgramExtractor) := by
  exact conservative_extractors_give_complete_prefix_checkers
    emptyProgramExtractor_lifetimeBorrow_conservative
    exactLifetimeBorrowChecker_complete

end ConservativeExtractor
