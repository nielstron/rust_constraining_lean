import FWRust.Sealor.Generated.PartialProgram

/-!
Compatibility import for the generated partial-program grammar.
-/

namespace ConservativeSealor

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

abbrev CompletesProgram : PartialProgram → Program → Prop :=
  CompletesTerm

end ConservativeSealor
