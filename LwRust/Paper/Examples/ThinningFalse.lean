import LwRust.Paper.Soundness.Helpers.BorrowWellFormed

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
private def thinZ : Name := "z"

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

/-!
The pointee annotation fixes the original example, but unrestricted thinning is
still false.  Strengthening can shrink a borrow target list to `[]`; the strong
side can type the dereference from the annotated pointee, while a weaker
environment may add a target whose base variable is not in the environment.
-/

private def thinMissingWeakPSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [LVal.var thinZ] Ty.int),
    lifetime := Lifetime.root }

private def thinMissingStrongPSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [] Ty.int), lifetime := Lifetime.root }

def thinMissingWeakEnv : Env :=
  Env.empty.update thinP thinMissingWeakPSlot

def thinMissingStrongEnv : Env :=
  Env.empty.update thinP thinMissingStrongPSlot

theorem thinMissingStrongEnv_strengthens :
    EnvStrengthens thinMissingStrongEnv thinMissingWeakEnv := by
  intro x
  by_cases hp : x = thinP
  · subst hp
    simp [thinMissingStrongEnv, thinMissingWeakEnv, Env.update]
    exact ⟨rfl, PartialTyStrengthens.borrow (List.nil_subset _)⟩
  · simp [thinMissingStrongEnv, thinMissingWeakEnv, Env.update, Env.empty, hp]

theorem thinMissingStrongEnv_types_copy_deref :
    TermTyping thinMissingStrongEnv StoreTyping.empty Lifetime.root
      (.copy (.deref (.var thinP))) .int thinMissingStrongEnv := by
  refine TermTyping.copy (valueLifetime := Lifetime.root) ?_ CopyTy.int ?_
  · exact LValTyping.borrow
      (LValTyping.var
        (slot := thinMissingStrongPSlot)
        (by simp [thinMissingStrongEnv, Env.update]))
      (LValTargetsTyping.empty (by simp [Ty.allVars]))
  · rintro ⟨x, targets, pointee, target, ⟨slot, hslot, hcontains⟩, hmem, _hconf⟩
    by_cases hp : x = thinP
    · subst hp
      simp [thinMissingStrongEnv, Env.update] at hslot
      subst hslot
      cases hcontains
      cases hmem
    · simp [thinMissingStrongEnv, Env.update, Env.empty, hp] at hslot

private theorem thinMissingWeakEnv_no_var_z :
    ∀ {pty lifetime},
      ¬ LValTyping thinMissingWeakEnv (.var thinZ) pty lifetime := by
  intro pty lifetime htyping
  cases htyping with
  | var hslot =>
      simp [thinMissingWeakEnv, Env.update, Env.empty, thinP, thinZ] at hslot

private theorem thinMissingWeakEnv_no_targets_z :
    ¬ LValTargetsTyping thinMissingWeakEnv [LVal.var thinZ] (.ty Ty.int)
      Lifetime.root := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      exact thinMissingWeakEnv_no_var_z htarget
  | cons hhead _hrest _hunion _hintersection =>
      exact thinMissingWeakEnv_no_var_z hhead

theorem thinMissingWeakEnv_not_types_deref :
    ¬ LValTyping thinMissingWeakEnv (.deref (.var thinP)) (.ty Ty.int)
      Lifetime.root := by
  intro htyping
  cases htyping with
  | box hbox =>
      rcases LValTyping.var_inv hbox with ⟨slot, hslot, hty, _hlife⟩
      have hslotEq : slot = thinMissingWeakPSlot := by
        simpa [thinMissingWeakEnv, Env.update] using hslot.symm
      subst hslotEq
      simp [thinMissingWeakPSlot] at hty
  | borrow hborrow htargets =>
      rcases LValTyping.var_inv hborrow with ⟨slot, hslot, hty, _hlife⟩
      have hslotEq : slot = thinMissingWeakPSlot := by
        simpa [thinMissingWeakEnv, Env.update] using hslot.symm
      subst hslotEq
      cases hty
      exact thinMissingWeakEnv_no_targets_z htargets

end Paper
end LwRust
