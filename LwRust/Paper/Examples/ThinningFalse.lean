import LwRust.Paper.Typing

/-!
The environment-thinning (weakening) metatheorem is **false** for this type
system.

Thinning would say: a typing derivation survives re-basing on a ⊑-stronger
input environment (`EnvStrengthens envStrong envWeak`).  This is the
"thinning metatheorem the paper does not provide" already noted for `T-Eq`
in the README, and it is what an NLL-style join-invariant while rule
(`T-WhileJoin`) would need in order to keep the conservative extractor's
transport working: a join-typed loop types its condition from the *widened*
invariant environment, while a truncated rebuild needs it from the
un-widened entry environment.

The counterexample: strengthening may shrink a borrow's target list to empty
(`W-Bor` is target-subset, so `&mut [] ⊑ &mut [y]`), and environment joins
generate exactly such same-shape pairs — yet `T-LvBor` cannot type a
dereference through an empty target list (`LValTargetsTyping` is non-empty
by construction).  Concretely, `copy *p` types from `p : ⟨&mut [y]⟩` but not
from the ⊑-stronger `p : ⟨&mut []⟩`.
-/

namespace LwRust
namespace Paper

open Core

private def thinY : Name := "y"
private def thinP : Name := "p"

/-- `y : ⟨int⟩, p : ⟨&mut [y]⟩` — the weaker (join-widened) environment. -/
def thinWeakEnv : Env :=
  (Env.empty.update thinY { ty := .ty .int, lifetime := Lifetime.root }).update
    thinP { ty := .ty (.borrow true [.var thinY]), lifetime := Lifetime.root }

/-- `y : ⟨int⟩, p : ⟨&mut []⟩` — the ⊑-stronger (entry) environment. -/
def thinStrongEnv : Env :=
  (Env.empty.update thinY { ty := .ty .int, lifetime := Lifetime.root }).update
    thinP { ty := .ty (.borrow true []), lifetime := Lifetime.root }

theorem thinStrongEnv_strengthens : EnvStrengthens thinStrongEnv thinWeakEnv := by
  intro x
  by_cases hp : x = thinP
  · subst hp
    simp [thinStrongEnv, thinWeakEnv, Env.update]
    exact PartialTyStrengthens.borrow (List.nil_subset _)
  · by_cases hy : x = thinY
    · subst hy
      simp [thinStrongEnv, thinWeakEnv, Env.update, thinY, thinP]
    · simp [thinStrongEnv, thinWeakEnv, Env.update, Env.empty, hp, hy]

/-- `copy *p` types from the weaker environment. -/
theorem thinWeakEnv_types_copy_deref :
    TermTyping thinWeakEnv StoreTyping.empty Lifetime.root
      (.copy (.deref (.var thinP))) .int thinWeakEnv := by
  refine TermTyping.copy (valueLifetime := Lifetime.root) ?_ CopyTy.int ?_
  · exact LValTyping.borrow
      (LValTyping.var
        (slot := { ty := .ty (.borrow true [.var thinY]),
                   lifetime := Lifetime.root })
        (by simp [thinWeakEnv, Env.update]))
      (LValTargetsTyping.singleton
        (LValTyping.var (slot := { ty := .ty .int, lifetime := Lifetime.root })
          (by simp [thinWeakEnv, Env.update, thinY, thinP])))
  · rintro ⟨x, targets, target, ⟨slot, hslot, hcontains⟩, hmem, hconf⟩
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

/-- No dereference of `p` types from the stronger environment: its borrow
has no targets, and `LValTargetsTyping` has no empty case. -/
private theorem lvalTyping_var_inv {env : Env} {x : Name} {pt : PartialTy}
    {lifetime : Lifetime} (h : LValTyping env (.var x) pt lifetime) :
    ∃ slot, env.slotAt x = some slot ∧ pt = slot.ty := by
  cases h with
  | var hslot => exact ⟨_, hslot, rfl⟩

theorem thinStrongEnv_no_deref_typing (partialTy : PartialTy)
    (lifetime : Lifetime) :
    ¬ LValTyping thinStrongEnv (.deref (.var thinP)) partialTy lifetime := by
  intro h
  cases h with
  | box hinner =>
      obtain ⟨slot, hslot, hty⟩ := lvalTyping_var_inv hinner
      simp [thinStrongEnv, Env.update] at hslot
      subst hslot
      cases hty
  | borrow hp htargets =>
      obtain ⟨slot, hslot, hty⟩ := lvalTyping_var_inv hp
      simp [thinStrongEnv, Env.update] at hslot
      subst hslot
      cases hty
      cases htargets

/-- Thinning is false: same-shape ⊑-related environments and a term typable
from the weaker but not the stronger one. -/
theorem thinning_false :
    ¬ (∀ (envStrong envWeak env₂ : Env) (typing : StoreTyping)
        (lifetime : Lifetime) (term : Term) (ty : Ty),
        EnvStrengthens envStrong envWeak →
        TermTyping envWeak typing lifetime term ty env₂ →
        ∃ ty' env₂', TermTyping envStrong typing lifetime term ty' env₂') := by
  intro hthinning
  rcases hthinning _ _ _ _ _ _ _ thinStrongEnv_strengthens
      thinWeakEnv_types_copy_deref with ⟨ty', env₂', h⟩
  cases h with
  | copy hLv _hcopy _hread => exact thinStrongEnv_no_deref_typing _ _ hLv

end Paper
end LwRust
