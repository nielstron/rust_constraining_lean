import LwRust.Extractor.Generated.PartialProgram

/-!
Compatibility import for the generated partial-program grammar.
-/

namespace ConservativeExtractor

export Generated (
  PartialName
  PartialTerms
  PartialTy
  PartialLVal
  PartialTerm
  PartialProgram
  CompletesName
  CompletesTerms
  CompletesTy
  CompletesLVal
  CompletesTerm
)

abbrev CompletesProgram : PartialProgram → RawProgram → Prop :=
  CompletesTerm

end ConservativeExtractor
