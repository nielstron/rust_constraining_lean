import FWRust.Paper.Soundness.Helpers.AppendixPrelim

/-!
# Soundness helpers: Eqv

Exact type-equivalence utilities.  `eqvX` is a local relation stricter than
ordinary `PartialTy.eqv`.
-/

namespace FWRust
namespace Paper

open Core

/-! ### Exact type equivalence (`eqvX`)

`eqvX` is stricter than `Ty.eqv`: box contents must be syntactically equal.
Borrow targets are single lvalues in the branch-free core, so borrow equivalence
records exact target equality. -/

/-- Exact type equivalence: like `Ty.eqv` but `box` contents must be *equal*. -/
def Ty.eqvX : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .borrow m₁ t₁, .borrow m₂ t₂ =>
      m₁ = m₂ ∧ t₁ = t₂
  | .box t₁, .box t₂ => t₁ = t₂
  | _, _ => False

/-- Partial-type version of `Ty.eqvX`. -/
def PartialTy.eqvX : PartialTy → PartialTy → Prop
  | .ty t₁, .ty t₂ => Ty.eqvX t₁ t₂
  | .box p₁, .box p₂ => PartialTy.eqvX p₁ p₂
  | .undef t₁, .undef t₂ => Ty.eqvX t₁ t₂
  | _, _ => False

@[refl] theorem Ty.eqvX_refl (a : Ty) : Ty.eqvX a a := by
  cases a <;> simp [Ty.eqvX]

@[refl] theorem PartialTy.eqvX_refl : (a : PartialTy) → PartialTy.eqvX a a
  | .ty t => Ty.eqvX_refl t
  | .box p => PartialTy.eqvX_refl p
  | .undef t => Ty.eqvX_refl t

end Paper
end FWRust
