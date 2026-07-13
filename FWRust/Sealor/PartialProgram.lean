import FWRust.Sealor.Generated.PartialProgram

/-!
Compatibility import for the generated partial-program grammar.
-/

namespace ConservativeSealor

export Generated (
  PartialInt
  PartialName
  PartialTerms
  PartialTy
  PartialLVal
  PartialTerm
  PartialProgram
  CompletesInt
  CompletesName
  CompletesTerms
  CompletesTy
  CompletesLVal
  CompletesTerm
)

abbrev CompletesProgram : PartialProgram → Program → Prop :=
  CompletesTerm

end ConservativeSealor
