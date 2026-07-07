import FWRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Lemma 9.1 (Safe Strengthening)

> Let `S` be a program store; let `Γ` be a well-formed typing environment where
> `S ∼ Γ`; let `T₁, T₂` be types where `T₁ ⊑ T₂`; and let `v` be a value.  If
> `S ⊢ v ∼ T₁` then `S ⊢ v ∼ T₂`.

Status: **fully proven** (`safeStrengthening`).
-/

namespace FWRust.Paper.Soundness

open FWRust.Paper FWRust.Core

theorem lemma_9_1_safeStrengthening
    {store : ProgramStore} {env : Env} {lifetime : Lifetime}
    {left right : Ty} {value : Value}
    (hwellFormed : WellFormedEnv env lifetime)
    (hsafe : store ∼ₛ env)
    (hstrength : PartialTyStrengthens (.ty left) (.ty right))
    (hvalid : ValidValue store value left) :
    ValidValue store value right :=
  safeStrengthening hwellFormed hsafe hstrength hvalid

end FWRust.Paper.Soundness
