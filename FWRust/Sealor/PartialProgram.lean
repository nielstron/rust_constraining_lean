import FWRust.Sealor.Generated.PartialProgram

/-!
Public facade for the partial-program grammar and completion relation.
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
