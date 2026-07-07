import FWRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Lemma 9.2 (Transitive Strengthening)

> Let `T̃₁, T̃₂` and `T̃₃` be partial types.  If `T̃₁ ⊑ T̃₂` and `T̃₂ ⊑ T̃₃`
> then `T̃₁ ⊑ T̃₃`.

Status: **fully proven** (`partialTyStrengthens_trans`).
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

theorem lemma_9_2_transitiveStrengthening
    {left middle right : PartialTy}
    (h₁ : PartialTyStrengthens left middle)
    (h₂ : PartialTyStrengthens middle right) :
    PartialTyStrengthens left right :=
  partialTyStrengthens_trans h₁ h₂

end FWRust.Paper.Soundness
