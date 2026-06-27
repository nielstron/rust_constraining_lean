import LwRust.Paper.Soundness.Helpers.Thinning

/-!
SCRATCH: concrete counterexample showing the static `parallelWriteCoherent`
(fan-out / deref-lhs branch) is FALSE.

A fan-out write `*a := rhs` through the mutable borrow `a : &mut[b] (&mut[] int)`
writes the RHS borrow `rhs : &mut[c] int` into the conduit target `b`.  The leaf
at `b` weak-joins `&mut[] int ⊔ &mut[c] int = &mut[c] int`, while the conduit
borrow in `a`'s slot (whose *pointee annotation* is `&mut[] int`) is left frozen.
The frozen annotation now disagrees with `b`'s grown type, so `env₃` is
incoherent — even though all the static T-Assign-carried premises hold.
-/

namespace LwRust
namespace Paper
open Core

private def na : Name := "a"
private def nb : Name := "b"
private def nc : Name := "c"

/-- Pointee annotation `P = &mut[] int`. -/
private def Pty : Ty := .borrow true [] .int
/-- The conduit borrow type stored at `a`: `&mut[b] (&mut[] int)`. -/
private def aTy : Ty := .borrow true [.var nb] Pty
/-- `b`'s original leaf: `&mut[] int` (= `P`). -/
private def bOldTy : Ty := .borrow true [] .int
/-- `b`'s grown leaf after the fan-out write: `&mut[c] int`. -/
private def bNewTy : Ty := .borrow true [.var nc] .int
/-- RHS type written: `&mut[c] int`. -/
private def rhsTy : Ty := .borrow true [.var nc] .int

private def aSlot : EnvSlot := { ty := .ty aTy, lifetime := Lifetime.root }
private def bOldSlot : EnvSlot := { ty := .ty bOldTy, lifetime := Lifetime.root }
private def bNewSlot : EnvSlot := { ty := .ty bNewTy, lifetime := Lifetime.root }
private def cSlot : EnvSlot := { ty := .ty .int, lifetime := Lifetime.root }

/-- Pre-write strong environment `env₂`. -/
private def env2 : Env :=
  (((Env.empty.update nc cSlot).update nb bOldSlot).update na aSlot)

/-- Post-write strong environment `env₃`: `a` frozen, `b` grown. -/
private def env3 : Env :=
  (env2.update nb bNewSlot).update na aSlot

private def lhs : LVal := .deref (.var na)

-- slot computations -----------------------------------------------------------

private theorem env2_a : env2.slotAt na = some aSlot := by
  simp [env2, Env.update, na, nb, nc]
private theorem env2_b : env2.slotAt nb = some bOldSlot := by
  simp [env2, Env.update, na, nb, nc]
private theorem env3_a : env3.slotAt na = some aSlot := by
  simp [env3, env2, Env.update, na, nb, nc]
private theorem env3_b : env3.slotAt nb = some bNewSlot := by
  simp [env3, env2, Env.update, na, nb, nc]
private theorem env3_c : env3.slotAt nc = some cSlot := by
  simp [env3, env2, Env.update, na, nb, nc]

/-! ## The fan-out write genuinely produces `env₃`. -/

private theorem write_inner :
    EnvWrite 1 env2 (.var nb) rhsTy (env2.update nb bNewSlot) := by
  refine EnvWrite.intro (slot := bOldSlot) (by simpa [LVal.base] using env2_b) ?_
  have hshape : ShapeCompatible env2 (.ty bOldTy) (.ty rhsTy) :=
    ShapeCompatible.borrow ShapeCompatible.int
  have hjoin : PartialTyJoin (.ty bOldTy) (.ty rhsTy) (.ty bNewTy) :=
    partialTyUnion_borrow_append (mutable := true) (Ta := []) (Tb := [.var nc]) (p := .int)
  exact UpdateAtPath.weak (rank := 0) (env := env2)
    (old := .ty bOldTy) (ty := rhsTy) (joined := .ty bNewTy) hshape hjoin

private theorem the_write : EnvWrite 0 env2 lhs rhsTy env3 := by
  have hwbt : WriteBorrowTargets 1 env2 [] [.var nb] rhsTy
      (env2.update nb bNewSlot) :=
    WriteBorrowTargets.singleton write_inner
      ⟨bOldTy, Lifetime.root, LValTyping.var (slot := bOldSlot) env2_b⟩
  have hmut := UpdateAtPath.mutBorrow (rank := 0) (env₁ := env2)
    (path := []) (targets := [.var nb]) (oldPointee := Pty) (ty := rhsTy) hwbt
  exact EnvWrite.intro (slot := aSlot) (by simpa [lhs, LVal.base] using env2_a) hmut

/-! ## `env₃` is NOT coherent. -/

private theorem nb_only_grown {pty : PartialTy} {lf : Lifetime}
    (h : LValTyping env3 (.var nb) pty lf) : pty = .ty bNewTy := by
  rcases LValTyping.var_inv h with ⟨slot, hslot, hty, _⟩
  rw [env3_b] at hslot
  have : slot = bNewSlot := (Option.some.inj hslot).symm
  subst this
  simpa [bNewSlot] using hty.symm

theorem env3_not_coherent : ¬ Coherent env3 := by
  intro hcoh
  have haTy : LValTyping env3 (.var na) (.ty (.borrow true [.var nb] Pty)) Lifetime.root :=
    LValTyping.var (slot := aSlot) env3_a
  obtain ⟨lf, htargets⟩ :=
    hcoh (.var na) true [.var nb] Pty Lifetime.root haTy
  cases htargets with
  | singleton hhead =>
      have hh := nb_only_grown hhead
      simp [Pty, bNewTy, nc] at hh
  | cons hhead _hrest hunion _hinter =>
      have hh := nb_only_grown hhead
      rw [hh] at hunion
      have hle := PartialTyUnion.left_strengthens hunion
      rcases PartialTyStrengthens.from_borrow_inv hle with ⟨T', heq, hsub⟩
      have hmem : LVal.var nc ∈ T' := hsub (show LVal.var nc ∈ [LVal.var nc] by simp)
      simp only [Pty, Ty.borrow.injEq, true_and, and_true] at heq
      subst heq
      simp at hmem

/-! All remaining T-Assign-carried premises (`Coherent env₂`, `ContainedBorrowsWellFormed env₃`,
the linearization + `EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy`,
`EnvWriteRhsTargetsWellFormed env₃ rhsTy`, `¬ WriteProhibited env₃ lhs`, and the
RHS-origin joint typing) are simultaneously satisfiable on this instance (see the
report). Hence `Coherent env₃` is genuinely INDEPENDENT and `parallelWriteCoherent`
is false. -/

end Paper
end LwRust
