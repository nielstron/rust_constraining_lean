import LwRust.Paper.Typing

/-!
The old environment-thinning counterexample no longer applies after borrow
types carry their pointee type explicitly.

Previously, strengthening could shrink `p : &mut [y]` to `p : &mut []`, which
erased the only evidence that `*p` had type `int`.  With the refactored borrow
type, both slots carry the pointee annotation `int`; the empty target list is
accepted only because `int` mentions no live variables.
-/

namespace LwRust
namespace Paper

open Core

private def thinY : Name := "y"
private def thinP : Name := "p"

private def thinYSlot : EnvSlot :=
  { ty := .ty Ty.int, lifetime := Lifetime.root }

private def thinWeakPSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [LVal.var thinY] Ty.int),
    lifetime := Lifetime.root }

private def thinStrongPSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [] Ty.int), lifetime := Lifetime.root }

/-- `y : int`, `p : &mut int [y]` — the weaker, join-widened environment. -/
def thinWeakEnv : Env :=
  (Env.empty.update thinY thinYSlot).update thinP thinWeakPSlot

/-- `y : int`, `p : &mut int []` — the stronger, entry-side environment. -/
def thinStrongEnv : Env :=
  (Env.empty.update thinY thinYSlot).update thinP thinStrongPSlot

theorem thinStrongEnv_strengthens : EnvStrengthens thinStrongEnv thinWeakEnv := by
  intro x
  by_cases hp : x = thinP
  · subst hp
    simp [thinStrongEnv, thinWeakEnv, Env.update]
    exact ⟨rfl, PartialTyStrengthens.borrow (List.nil_subset _)⟩
  · by_cases hy : x = thinY
    · subst hy
      simp [thinStrongEnv, thinWeakEnv, Env.update, thinY, thinP]
    · simp [thinStrongEnv, thinWeakEnv, Env.update, Env.empty, hp, hy]

theorem thinWeakEnv_types_copy_deref :
    TermTyping thinWeakEnv StoreTyping.empty Lifetime.root
      (.copy (.deref (.var thinP))) .int thinWeakEnv := by
  refine TermTyping.copy (valueLifetime := Lifetime.root) ?_ CopyTy.int ?_
  · exact LValTyping.borrow
      (LValTyping.var
        (slot := thinWeakPSlot)
        (by simp [thinWeakEnv, Env.update]))
      (LValTargetsTyping.singleton
        (LValTyping.var
          (slot := thinYSlot)
          (by simp [thinWeakEnv, Env.update, thinY, thinP])))
  · rintro ⟨x, targets, pointee, target, ⟨slot, hslot, hcontains⟩, hmem, hconf⟩
    by_cases hp : x = thinP
    · subst hp
      simp [thinWeakEnv, Env.update] at hslot
      subst hslot
      cases hcontains
      simp at hmem
      subst hmem
      simp [PathConflicts, LVal.base, thinY, thinP] at hconf
    · by_cases hy : x = thinY
      · subst hy
        simp [thinWeakEnv, Env.update, thinY, thinP] at hslot
        subst hslot
        cases hcontains
      · simp [thinWeakEnv, Env.update, Env.empty, hp, hy] at hslot

theorem thinStrongEnv_types_copy_deref :
    TermTyping thinStrongEnv StoreTyping.empty Lifetime.root
      (.copy (.deref (.var thinP))) .int thinStrongEnv := by
  refine TermTyping.copy (valueLifetime := Lifetime.root) ?_ CopyTy.int ?_
  · exact LValTyping.borrow
      (LValTyping.var
        (slot := thinStrongPSlot)
        (by simp [thinStrongEnv, Env.update]))
      (LValTargetsTyping.empty (by simp [Ty.allVars]))
  · rintro ⟨x, targets, pointee, target, ⟨slot, hslot, hcontains⟩, hmem, _hconf⟩
    by_cases hp : x = thinP
    · subst hp
      simp [thinStrongEnv, Env.update] at hslot
      subst hslot
      cases hcontains
      cases hmem
    · by_cases hy : x = thinY
      · subst hy
        simp [thinStrongEnv, Env.update, thinY, thinP] at hslot
        subst hslot
        cases hcontains
      · simp [thinStrongEnv, Env.update, Env.empty, hp, hy] at hslot

end Paper
end LwRust
