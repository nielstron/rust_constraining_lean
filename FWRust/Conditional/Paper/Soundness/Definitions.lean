import FWRust.Conditional.Paper.Soundness

/-!
# Section 4 definitions

Index of the Section 4 definitions and their mechanized counterparts in
`FWRust.Conditional.Paper.Soundness`.

| Paper | Name | Mechanized |
| --- | --- | --- |
| Def 4.1 | Valid Term | `ValidTerm` |
| Def 4.2 | Valid Store | `ValidStore` |
| Def 4.3 | Valid State | `ValidState` (runtime package: `ValidRuntimeState`) |
| Def 4.4 | Valid Type (`S ⊢ v⊥ ∼ T̃`) | `ValidPartialValue` / `ValidValue` |
| Def 4.5 | Valid Store Typing (`S ▷ t ⊢ σ`) | `ValidStoreTyping` |
| Def 4.6 | Variable Projection (`Θ`) | `VariableProjection` |
| Def 4.7 | Safe Abstraction (`S ∼ Γ`) | `SafeAbstraction` (notation `∼ₛ`); full variant: `FullSafeAbstraction` (notation `≈ₛ`) |
| Def 4.8 | Well-formed Environment | `WellFormedEnv` (`ContainedBorrowsWellFormed` ∧ `EnvSlotsOutlive`) |
| Def 4.13 | Borrow Safe Environment | `BorrowSafeEnv` |

These are re-exported here so downstream files can `open FWRust.Conditional.Paper.Soundness`
and refer to the definitions by their paper name.
-/

namespace FWRust.Conditional.Paper.Soundness

open FWRust.Conditional.Paper

-- Re-export the mechanized definitions under this namespace.
export FWRust.Conditional.Paper
  (ValidTerm ValidStore ValidState ValidRuntimeState ValidPartialValue ValidValue
   ValidStoreTyping VariableProjection SafeAbstraction FullSafeAbstraction WellFormedEnv
   ContainedBorrowsWellFormed EnvSlotsOutlive BorrowSafeEnv)

end FWRust.Conditional.Paper.Soundness
