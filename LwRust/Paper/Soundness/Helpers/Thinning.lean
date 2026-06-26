import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
# Coherence-preserving environment thinning

The NLL loop rule `TermTyping.whileLoop` types the loop condition and body from
the *widened* invariant environment `envInv = env₁ ⊔ envBack`.  The conservative
extractor, when it truncates a loop, needs the same condition/body derivations
re-rooted at the un-widened *entry* environment `env₁`.

In general this re-rooting (environment *thinning*) is false — shrinking a
borrow's target list can make a dereference typeless (`Examples/ThinningFalse`).
But the only obstruction is a target list shrinking to *empty*, and `Coherent`
forbids that: every borrow it sees has jointly-typeable (hence non-empty)
targets.  So thinning holds whenever the strong (entry) environment is coherent.

This file proves that coherence-preserving thinning for `LValTyping`,
`LValTargetsTyping`, `TermTyping`, and `TermListTyping`, tracking that the
thinned result type `⊑`-strengthens the original.
-/

namespace LwRust
namespace Paper

open Core

/-- `EnvStrengthens` is the per-slot backward reading: a weak-side slot has a
`⊑`-stronger strong-side slot at the same name with the same lifetime. -/
theorem EnvStrengthens.slot_backward {envS envW : Env} {x : Name}
    {slotW : EnvSlot} :
    EnvStrengthens envS envW →
    envW.slotAt x = some slotW →
    ∃ slotS,
      envS.slotAt x = some slotS ∧
      slotS.lifetime = slotW.lifetime ∧
      PartialTyStrengthens slotS.ty slotW.ty := by
  intro hstr hslotW
  have h := hstr x
  rw [hslotW] at h
  cases hslotS : envS.slotAt x with
  | none => rw [hslotS] at h; exact False.elim h
  | some slotS =>
      rw [hslotS] at h
      exact ⟨slotS, rfl, h.1, h.2⟩

/-- Each borrowed target's pointee type `⊑`-strengthens into the union type of
the whole target list. -/
theorem LValTargetsTyping.member_le {env : Env} {targets : List LVal}
    {unionTy : PartialTy} {lifetime : Lifetime} :
    LValTargetsTyping env targets unionTy lifetime →
    ∀ t ∈ targets,
      ∃ ptee lt,
        LValTyping env t (.ty ptee) lt ∧
        PartialTyStrengthens (.ty ptee) unionTy := by
  intro h
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun targets unionTy _ _ =>
      ∀ t ∈ targets,
        ∃ ptee lt, LValTyping env t (.ty ptee) lt ∧
          PartialTyStrengthens (.ty ptee) unionTy)
    ?_ ?_ ?_ ?_ ?_ h
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro target ty lifetime htarget _ihtarget t ht
    have ht' := List.eq_of_mem_singleton ht
    subst ht'
    exact ⟨ty, lifetime, htarget, PartialTyStrengthens.reflex⟩
  · intro target rest headTy headLife restLife life restTy unionTy
      hhead _hrest hunion _hintersection _ihHead ihRest t ht
    rcases List.mem_cons.mp ht with rfl | htRest
    · exact ⟨headTy, headLife, hhead, PartialTyUnion.left_strengthens hunion⟩
    · rcases ihRest t htRest with ⟨ptee, lt, htyp, hle⟩
      exact ⟨ptee, lt, htyp,
        partialTyStrengthens_trans hle (PartialTyUnion.right_strengthens hunion)⟩

/-! ## Monotonicity of `LValTyping` across environment strengthening

Given *both* a strong-env and a weak-env typing of the same lval, the strong
pointee type `⊑`-strengthens the weak one.  No coherence or linearizability is
needed: we recurse on the strong derivation and compare it to the weak one node
by node.  This is the engine that supplies the output `⊑`-obligation in the
borrow case of `thin`. -/

/-- A union built over `targetsS` strengthens any weak-env type that
upper-bounds the same (super)list `targetsW ⊇ targetsS`. -/
theorem LValTargetsTyping.mono {envS : Env} {targetsS : List LVal}
    {pS : PartialTy} {lfS : Lifetime} {envW : Env} {targetsW : List LVal}
    {pW : PartialTy} {lfW : Lifetime} :
    LValTargetsTyping envS targetsS pS lfS →
    EnvStrengthens envS envW →
    targetsS.Subset targetsW →
    LValTargetsTyping envW targetsW pW lfW →
    PartialTyStrengthens pS pW := by
  intro hS
  refine (LValTargetsTyping.rec
    (motive_1 := fun lv pS _ _ =>
      ∀ {envW pW lfW}, EnvStrengthens envS envW →
        LValTyping envW lv pW lfW → PartialTyStrengthens pS pW)
    (motive_2 := fun ts pS _ _ =>
      ∀ {envW pW targetsW lfW}, EnvStrengthens envS envW →
        ts.Subset targetsW → LValTargetsTyping envW targetsW pW lfW →
        PartialTyStrengthens pS pW)
    ?var ?box ?borrow ?singleton ?cons hS)
  · -- var
    intro x slot hslot envW pW lfW hstr hW
    cases hW with
    | var hslotW =>
        rcases EnvStrengthens.slot_forward hstr hslot with
          ⟨slotW, hslotW', _hlf, hle⟩
        rw [hslotW] at hslotW'
        cases hslotW'
        exact hle
  · -- box
    intro lv inner lifetime _hbS ih envW pW lfW hstr hW
    cases hW with
    | box hbW => exact PartialTyStrengthens.box_inv (ih hstr hbW)
    | borrow hborW _ => cases ih hstr hborW
  · -- borrow
    intro lv mutable targets borrowLifetime targetLifetime targetTy
      hborS _htgtS ihBor ihTgt envW pW lfW hstr hW
    cases hW with
    | box hbW => cases ihBor hstr hbW
    | borrow hborW htgtW =>
        rcases PartialTyStrengthens.from_borrow_inv (ihBor hstr hborW) with
          ⟨tgtTargetsW, htyEq, hsub⟩
        cases htyEq
        exact ihTgt hstr hsub htgtW
  · -- singleton
    intro target ty lifetime _htS ihT envW pW targetsW lfW hstr hsub hW
    have hmem : target ∈ targetsW := hsub (List.mem_singleton_self target)
    rcases LValTargetsTyping.member_le hW target hmem with
      ⟨pteeW, ltW, htypW, hleW⟩
    exact partialTyStrengthens_trans (ihT hstr htypW) hleW
  · -- cons
    intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hheadS _hrestS hunion _hint ihHead ihRest envW pW targetsW lfW hstr hsub hW
    rcases List.cons_subset.mp hsub with ⟨hheadMem, hrestSub⟩
    rcases LValTargetsTyping.member_le hW target hheadMem with
      ⟨pteeW, ltW, htypW, hleW⟩
    have hheadLe : PartialTyStrengthens (.ty headTy) pW :=
      partialTyStrengthens_trans (ihHead hstr htypW) hleW
    have hrestLe : PartialTyStrengthens restTy pW := ihRest hstr hrestSub hW
    have hub : pW ∈ upperBounds ({(.ty headTy), restTy} : Set PartialTy) := by
      intro z hz
      rcases hz with hz | hz
      · subst hz; exact hheadLe
      · rw [Set.mem_singleton_iff] at hz; subst hz; exact hrestLe
    exact hunion.2 hub

/-- Monotonicity for a single lval (the `motive_1` projection). -/
theorem LValTyping.mono {envS : Env} {lv : LVal} {pS : PartialTy}
    {lfS : Lifetime} {envW : Env} {pW : PartialTy} {lfW : Lifetime} :
    LValTyping envS lv pS lfS →
    EnvStrengthens envS envW →
    LValTyping envW lv pW lfW →
    PartialTyStrengthens pS pW := by
  intro hS
  refine (LValTyping.rec
    (motive_1 := fun lv pS _ _ =>
      ∀ {envW pW lfW}, EnvStrengthens envS envW →
        LValTyping envW lv pW lfW → PartialTyStrengthens pS pW)
    (motive_2 := fun ts pS _ _ =>
      ∀ {envW pW targetsW lfW}, EnvStrengthens envS envW →
        ts.Subset targetsW → LValTargetsTyping envW targetsW pW lfW →
        PartialTyStrengthens pS pW)
    ?var ?box ?borrow ?singleton ?cons hS)
  · intro x slot hslot envW pW lfW hstr hW
    cases hW with
    | var hslotW =>
        rcases EnvStrengthens.slot_forward hstr hslot with
          ⟨slotW, hslotW', _hlf, hle⟩
        rw [hslotW] at hslotW'
        cases hslotW'
        exact hle
  · intro lv inner lifetime _hbS ih envW pW lfW hstr hW
    cases hW with
    | box hbW => exact PartialTyStrengthens.box_inv (ih hstr hbW)
    | borrow hborW _ => cases ih hstr hborW
  · intro lv mutable targets borrowLifetime targetLifetime targetTy
      hborS _htgtS ihBor ihTgt envW pW lfW hstr hW
    cases hW with
    | box hbW => cases ihBor hstr hbW
    | borrow hborW htgtW =>
        rcases PartialTyStrengthens.from_borrow_inv (ihBor hstr hborW) with
          ⟨tgtTargetsW, htyEq, hsub⟩
        cases htyEq
        exact ihTgt hstr hsub htgtW
  · intro target ty lifetime _htS ihT envW pW targetsW lfW hstr hsub hW
    have hmem : target ∈ targetsW := hsub (List.mem_singleton_self target)
    rcases LValTargetsTyping.member_le hW target hmem with
      ⟨pteeW, ltW, htypW, hleW⟩
    exact partialTyStrengthens_trans (ihT hstr htypW) hleW
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hheadS _hrestS hunion _hint ihHead ihRest envW pW targetsW lfW hstr hsub hW
    rcases List.cons_subset.mp hsub with ⟨hheadMem, hrestSub⟩
    rcases LValTargetsTyping.member_le hW target hheadMem with
      ⟨pteeW, ltW, htypW, hleW⟩
    have hheadLe : PartialTyStrengthens (.ty headTy) pW :=
      partialTyStrengthens_trans (ihHead hstr htypW) hleW
    have hrestLe : PartialTyStrengthens restTy pW := ihRest hstr hrestSub hW
    have hub : pW ∈ upperBounds ({(.ty headTy), restTy} : Set PartialTy) := by
      intro z hz
      rcases hz with hz | hz
      · subst hz; exact hheadLe
      · rw [Set.mem_singleton_iff] at hz; subst hz; exact hrestLe
    exact hunion.2 hub

/-! ## Coherence-preserving lval thinning

For a weak-env typing of an lval, coherence of the strong env produces a
strong-env typing of the *same* lval with a `⊑`-stronger type. -/

/-- Coherence-preserving thinning of a single lval typing. -/
theorem LValTyping.thin {envW : Env} {lv : LVal} {pW : PartialTy}
    {lfW : Lifetime} {envS : Env} :
    LValTyping envW lv pW lfW →
    EnvStrengthens envS envW →
    Coherent envS →
    ∃ pS lfS, LValTyping envS lv pS lfS ∧ PartialTyStrengthens pS pW := by
  intro hW
  refine (LValTyping.rec
    (motive_1 := fun lv pW _ _ =>
      ∀ {envS}, EnvStrengthens envS envW → Coherent envS →
        ∃ pS lfS, LValTyping envS lv pS lfS ∧ PartialTyStrengthens pS pW)
    (motive_2 := fun _ _ _ _ => True)
    ?var ?box ?borrow ?singleton ?cons hW)
  · -- var
    intro x slot hslot envS hstr hcoh
    rcases EnvStrengthens.slot_backward hstr hslot with
      ⟨slotS, hslotS, _hlf, hle⟩
    exact ⟨slotS.ty, slotS.lifetime, LValTyping.var hslotS, hle⟩
  · -- box
    intro lv inner lifetime _hbW ih envS hstr hcoh
    rcases ih hstr hcoh with ⟨pS, lfS, hbS, hle⟩
    cases hle with
    | reflex =>
        exact ⟨inner, lfS, LValTyping.box hbS, PartialTyStrengthens.reflex⟩
    | box hinner =>
        exact ⟨_, lfS, LValTyping.box hbS, hinner⟩
  · -- borrow
    intro lv mutable targets borrowLifetime targetLifetime targetTy
      _hborW _htgtW ihBor _ihTgt envS hstr hcoh
    rcases ihBor hstr hcoh with ⟨pBorS, lfBorS, hborS, hborLe⟩
    rcases PartialTyStrengthens.to_borrow_right hborLe with ⟨targetsS, hpEq, hsub⟩
    subst hpEq
    rcases hcoh lv mutable targetsS lfBorS hborS with ⟨tyS, lifeS, htgtS⟩
    exact ⟨.ty tyS, lifeS, LValTyping.borrow hborS htgtS,
      LValTargetsTyping.mono htgtS hstr hsub _htgtW⟩
  · intros; trivial
  · intros; trivial

end Paper
end LwRust
