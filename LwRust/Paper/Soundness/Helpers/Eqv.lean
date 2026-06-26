import LwRust.Paper.Soundness.Helpers.AppendixPrelim

/-!
# Soundness helpers: Eqv

Exact type equivalence utilities.  The main strengthening transport now uses
ordinary `PartialTy.eqv`; `eqvX` remains only as a stricter local relation.
-/

namespace LwRust
namespace Paper

open Core

/-! ### Exact type equivalence (`eqvX`)

`eqvX` is stricter than `Ty.eqv`: box contents must be syntactically equal.
Exact target-list determinism is intentionally not stated here: target-list
joins may reorder borrow-target lists under boxes, so `eqvX` would be too
strong for those joins. -/

/-- Exact type equivalence: like `Ty.eqv` but `box` contents must be *equal*. -/
def Ty.eqvX : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .bool, .bool => True
  | .borrow m₁ t₁ p₁, .borrow m₂ t₂ p₂ =>
      m₁ = m₂ ∧ t₁ ⊆ t₂ ∧ t₂ ⊆ t₁ ∧ p₁ = p₂
  | .box t₁, .box t₂ => t₁ = t₂
  | _, _ => False

/-- Partial-type version of `Ty.eqvX`. -/
def PartialTy.eqvX : PartialTy → PartialTy → Prop
  | .ty t₁, .ty t₂ => Ty.eqvX t₁ t₂
  | .box p₁, .box p₂ => PartialTy.eqvX p₁ p₂
  | .undef t₁, .undef t₂ => Ty.eqvX t₁ t₂
  | _, _ => False

@[refl] theorem Ty.eqvX_refl : (a : Ty) → Ty.eqvX a a
  | .unit => trivial
  | .int => trivial
  | .bool => trivial
  | .borrow _ _ _ =>
      ⟨rfl, (fun _ h => h), (fun _ h => h), rfl⟩
  | .box _ => rfl

@[refl] theorem PartialTy.eqvX_refl : (a : PartialTy) → PartialTy.eqvX a a
  | .ty t => Ty.eqvX_refl t
  | .box p => PartialTy.eqvX_refl p
  | .undef t => Ty.eqvX_refl t

end Paper
end LwRust
