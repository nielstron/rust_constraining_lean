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
    ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · -- empty: the target list is `[]`, so membership is vacuous
    intro _ _ t ht
    simp at ht
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

/-! ## `CopyTy` is preserved downward under `⊑`

A `⊑`-stronger type of a copy type is still a copy type: `unit`/`int`/`bool`
can only strengthen from themselves, and an immutable borrow `&T` strengthens
only from an immutable borrow `&T'` (with a subset target list), which is still
`immBorrow`-`CopyTy`. -/

/-- If `tyS ⊑ ty` and `ty` is a copy type, then so is `tyS`. -/
theorem CopyTy.of_strengthens {tyS ty : Ty} :
    PartialTyStrengthens (.ty tyS) (.ty ty) → CopyTy ty → CopyTy tyS := by
  intro hstr hcopy
  cases hcopy with
  | unit => rw [PartialTyStrengthens.to_unit_inv hstr]; exact CopyTy.unit
  | int => rw [PartialTyStrengthens.to_int_inv hstr]; exact CopyTy.int
  | bool => rw [PartialTyStrengthens.to_bool_inv hstr]; exact CopyTy.bool
  | immBorrow =>
      rcases PartialTyStrengthens.to_borrow_inv hstr with ⟨srcTargets, hEq, _⟩
      rw [hEq]; exact CopyTy.immBorrow

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
    ?var ?box ?borrow ?empty ?singleton ?cons hW)
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
    intro lv mutable targets pointee borrowLifetime targetLifetime
      _hborW _htgtW ihBor _ihTgt envS hstr hcoh
    rcases ihBor hstr hcoh with ⟨pBorS, lfBorS, hborS, hborLe⟩
    rcases PartialTyStrengthens.to_borrow_right hborLe with ⟨targetsS, hpEq, _hsub⟩
    subst hpEq
    -- The pointee annotation is preserved by `⊑`, so coherence of `envS`
    -- re-types the (possibly shrunk) target list against the *same* pointee.
    rcases hcoh lv mutable targetsS pointee lfBorS hborS with ⟨lifeS, htgtS⟩
    exact ⟨.ty pointee, lifeS, LValTyping.borrow hborS htgtS,
      PartialTyStrengthens.reflex⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-! ## Coherence under a single-slot update

The variable-lhs (single-slot) branch of an assignment write changes exactly the
base slot.  Borrows *not* rooted at that slot transport their joint typing back
and forth across the update (no path conflict), reusing the source coherence;
borrows rooted at the updated slot are supplied by the `hnew` obligation. -/

/-- `Coherent` is preserved by a single-slot update, given source coherence and
a coherence witness for borrows rooted at the updated slot.  This is the
write analogue of `Coherent.move`. -/
theorem Coherent.update_slot {env : Env} {b : Name} {origSlot newSlot : EnvSlot}
    (hcoh : Coherent env)
    (horig : env.slotAt b = some origSlot)
    (hnotWriteEnv : ¬ WriteProhibited env (.var b))
    (hnotWriteUpd : ¬ WriteProhibited (env.update b newSlot) (.var b))
    (hnew : ∀ lv m T P bl,
       LValTyping (env.update b newSlot) lv (.ty (.borrow m T P)) bl →
       LVal.base lv = b →
       ∃ lf, LValTargetsTyping (env.update b newSlot) T (.ty P) lf) :
    Coherent (env.update b newSlot) := by
  intro lv' m T pointee bLf hty'
  by_cases hbase : LVal.base lv' = b
  · exact hnew lv' m T pointee bLf hty' hbase
  · have hnoconf : ¬ lv' ⋈ (.var b) := by
      simpa [PathConflicts, LVal.base] using hbase
    have hrestore : (env.update b newSlot).update b origSlot = env := by
      obtain ⟨g⟩ := env
      simp only [Env.update]
      congr 1
      funext y
      by_cases hy : y = b
      · subst hy; simpa using horig.symm
      · simp [hy]
    have hnotWriteRestore :
        ¬ WriteProhibited ((env.update b newSlot).update b origSlot) (.var b) := by
      rw [hrestore]; exact hnotWriteEnv
    have htyEnv : LValTyping env lv' (.ty (.borrow m T pointee)) bLf := by
      have h := (LValTyping.update_of_not_pathConflicts hnotWriteRestore).1 hty' hnoconf
      rwa [hrestore] at h
    rcases hcoh lv' m T pointee bLf htyEnv with ⟨lt, htgtsEnv⟩
    have hnotTargets : ∀ target, target ∈ T → ¬ target ⋈ (.var b) := by
      intro target htarget
      exact (LValTyping.no_writeProhibited_targets hnotWriteEnv).1 htyEnv
        PartialTyContains.here target htarget
    exact ⟨lt, (LValTyping.update_of_not_pathConflicts hnotWriteUpd).2 htgtsEnv hnotTargets⟩

/-- **Single-slot (variable-lhs) branch of `parallelWriteCoherent`.**

When the strong assignment write is a single base-slot update
(`EnvWrite.sameShapeStrengthening_or_singleSlot`, second disjunct), strong-side
coherence of the result follows from coherence of the pre-write environment plus
a coherence witness `hnew` for the borrows installed into the updated slot from
the RHS.  The `hnew` obligation is genuinely needed: it is the *joint*
typeability of the RHS-origin borrows, which is strictly stronger than the
per-target `WellFormedTy`/`EnvWriteRhsTargetsWellFormed` obligations (see the
deviation note at `Typing.lean` `BorrowTargetsWellFormed`). -/
theorem parallelWriteCoherent_singleSlot {env₂ₛ env₃ₛ : Env} {lhs : LVal}
    {slot : EnvSlot} {updatedTy : PartialTy}
    (hcoh₂ : Coherent env₂ₛ)
    (hslot : env₂ₛ.slotAt (LVal.base lhs) = some slot)
    (henv₃ : env₃ₛ = env₂ₛ.update (LVal.base lhs) { slot with ty := updatedTy })
    (hnotWrite₂ : ¬ WriteProhibited env₂ₛ lhs)
    (hnotWrite₃ : ¬ WriteProhibited env₃ₛ lhs)
    (hnew : ∀ lv m T P bl,
       LValTyping env₃ₛ lv (.ty (.borrow m T P)) bl →
       LVal.base lv = LVal.base lhs →
       ∃ lf, LValTargetsTyping env₃ₛ T (.ty P) lf) :
    Coherent env₃ₛ := by
  subst henv₃
  exact Coherent.update_slot hcoh₂ hslot
    (not_writeProhibited_var_base hnotWrite₂)
    (not_writeProhibited_var_base hnotWrite₃)
    hnew

/-! ## Deep strengthening

The flat `PartialTyStrengthens` fixes a borrow's pointee annotation, so it
cannot relate `&[lv](&[a]int)` to `&[lv](&[a,b]int)`.  But thinning a borrow
*operand* changes exactly that nested pointee.  `TyDeepStrengthens` recurses
into borrow pointees and box elements: a borrow deep-strengthens another iff
they share mutability, the target list shrinks, *and* the pointees deep-
strengthen.  This is the output relation that the eventual `thin` tracks, in
place of the unprovable flat conjunct. -/

/-- Structural "deep" strengthening of full types: recurses into borrow
pointees and box elements. -/
inductive TyDeepStrengthens : Ty → Ty → Prop where
  | refl {ty : Ty} :
      TyDeepStrengthens ty ty
  | borrow {mutable : Bool} {leftTargets rightTargets : List LVal}
      {leftPointee rightPointee : Ty} :
      leftTargets.Subset rightTargets →
      TyDeepStrengthens leftPointee rightPointee →
      TyDeepStrengthens (.borrow mutable leftTargets leftPointee)
        (.borrow mutable rightTargets rightPointee)
  | box {left right : Ty} :
      TyDeepStrengthens left right →
      TyDeepStrengthens (.box left) (.box right)

attribute [refl] TyDeepStrengthens.refl

/-- Deep strengthening of partial types: recurses into the full-type leaves
via `TyDeepStrengthens` while keeping the flat `undef` transitions. -/
inductive PartialTyDeepStrengthens : PartialTy → PartialTy → Prop where
  | ty {left right : Ty} :
      TyDeepStrengthens left right →
      PartialTyDeepStrengthens (.ty left) (.ty right)
  | box {left right : PartialTy} :
      PartialTyDeepStrengthens left right →
      PartialTyDeepStrengthens (.box left) (.box right)
  | undefLeft {left right : Ty} :
      TyDeepStrengthens left right →
      PartialTyDeepStrengthens (.undef left) (.undef right)
  | intoUndef {left right : Ty} :
      TyDeepStrengthens left right →
      PartialTyDeepStrengthens (.ty left) (.undef right)
  | boxIntoUndef {left : PartialTy} {right : Ty} :
      PartialTyDeepStrengthens left (.undef right) →
      PartialTyDeepStrengthens (.box left) (.undef (.box right))

/-- Deep strengthening of full types is transitive. -/
theorem TyDeepStrengthens.trans {a b c : Ty} :
    TyDeepStrengthens a b → TyDeepStrengthens b c → TyDeepStrengthens a c := by
  intro hab hbc
  induction hab generalizing c with
  | refl => exact hbc
  | borrow hsub _hp ih =>
      cases hbc with
      | refl => exact .borrow hsub (ih .refl)
      | borrow hsub' hp' => exact .borrow (hsub.trans hsub') (ih hp')
  | box _hinner ih =>
      cases hbc with
      | refl => exact .box (ih .refl)
      | box hinner' => exact .box (ih hinner')

/-- Deep strengthening preserves the structural shape of full types. -/
theorem TyDeepStrengthens.sameShape {a b : Ty} :
    TyDeepStrengthens a b → Ty.sameShape a b := by
  intro h
  induction h with
  | refl => exact Ty.sameShape_refl _
  | borrow _ _ ih => exact ⟨rfl, ih⟩
  | box _ ih => exact ih

/-- Deep strengthening of partial types is reflexive. -/
@[refl] theorem PartialTyDeepStrengthens.refl (pt : PartialTy) :
    PartialTyDeepStrengthens pt pt := by
  cases pt with
  | ty t => exact .ty .refl
  | box p => exact .box (PartialTyDeepStrengthens.refl p)
  | undef t => exact .undefLeft .refl

/-- Deep strengthening of partial types is transitive. -/
theorem PartialTyDeepStrengthens.trans {a b c : PartialTy} :
    PartialTyDeepStrengthens a b → PartialTyDeepStrengthens b c →
    PartialTyDeepStrengthens a c := by
  intro hab hbc
  induction hab generalizing c with
  | ty h =>
      cases hbc with
      | ty h' => exact .ty (h.trans h')
      | intoUndef h' => exact .intoUndef (h.trans h')
  | box _h ih =>
      cases hbc with
      | box h' => exact .box (ih h')
      | boxIntoUndef h' => exact .boxIntoUndef (ih h')
  | undefLeft h =>
      cases hbc with
      | undefLeft h' => exact .undefLeft (h.trans h')
  | intoUndef h =>
      cases hbc with
      | undefLeft h' => exact .intoUndef (h.trans h')
  | boxIntoUndef _hinner ih =>
      cases hbc with
      | undefLeft h' =>
          cases h' with
          | refl => exact .boxIntoUndef (ih (.undefLeft .refl))
          | box hr3 => exact .boxIntoUndef (ih (.undefLeft hr3))

/-- Flat strengthening implies deep strengthening. -/
theorem PartialTyDeepStrengthens.of_flat {p q : PartialTy} :
    PartialTyStrengthens p q → PartialTyDeepStrengthens p q := by
  intro h
  induction h with
  | reflex => exact PartialTyDeepStrengthens.refl _
  | box _ ih => exact .box ih
  | tyBox _ ih =>
      cases ih with
      | ty hd => exact .ty (.box hd)
  | borrow hsub => exact .ty (.borrow hsub .refl)
  | undefLeft _ ih =>
      cases ih with
      | ty hd => exact .undefLeft hd
  | intoUndef _ ih =>
      cases ih with
      | ty hd => exact .intoUndef hd
  | boxIntoUndef _ ih => exact .boxIntoUndef ih

/-! ## Joint-typing append combinator

Two jointly-typed target lists at the *same* borrow pointee `P` combine into a
joint typing of their concatenation, provided their list lifetimes have an
intersection (the order-theoretic LUB in the prefix order on lifetimes).  This
is the "append" construction the codebase otherwise lacks; it is the glue that
re-assembles a grown borrow target list `W = Wold ++ Wrhs` from its two
sub-typings. -/

/-- If `a ⊑ U` then `U` is already the union of `a` and `U`. -/
theorem partialTyUnion_self_of_le {a U : PartialTy} (h : PartialTyStrengthens a U) :
    PartialTyUnion a U U := by
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact h
    · exact PartialTyStrengthens.reflex
  · intro y hy
    exact hy (by simp)

/-- **LUB representative freedom.**  If `j` is a join (LUB) of `{a, b}` and `z` is
*any* upper bound of `{a, b}` that is `⊑` the existing join `j`, then `z` is itself
a join of `{a, b}`.  (`z` upper-bounds `{a,b}` and `z ⊑ j ⊑` every upper bound, so
`z` is least among upper bounds.)  This is the reusable engine that lets the
empty/cons cases of `parallelWriteCoherent` swap the algorithmic union for an
`≈`-equivalent representative. -/
theorem partialTyJoin_pick_eqv_bound {a b j z : PartialTy}
    (hj : PartialTyJoin a b j) (haz : a ≤ z) (hbz : b ≤ z) (hzj : z ≤ j) :
    PartialTyJoin a b z := by
  refine ⟨?_, ?_⟩
  · -- z is an upper bound of {a, b}
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact haz
    · exact hbz
  · -- z is below every upper bound: z ⊑ j ⊑ w
    intro w hw
    exact partialTyStrengthens_trans hzj (hj.2 hw)

/-- Lifetimes below a common lifetime are comparable (the prefix order is a tree;
two prefixes of a common path form a chain). -/
theorem lifetime_comparable_of_le {a b u : Lifetime}
    (ha : a ≤ u) (hb : b ≤ u) : a ≤ b ∨ b ≤ a := by
  simp only [lifetime_le_iff_outlives, LifetimeOutlives, Core.Lifetime.contains,
    List.isPrefixOf_iff_prefix] at ha hb ⊢
  exact List.prefix_or_prefix_of_prefix ha hb

/-- The prefix order on lifetimes is antisymmetric. -/
theorem lifetime_le_antisymm {a b : Lifetime} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  obtain ⟨pa⟩ := a
  obtain ⟨pb⟩ := b
  simp only [lifetime_le_iff_outlives, LifetimeOutlives, Core.Lifetime.contains,
    List.isPrefixOf_iff_prefix] at hab hba
  have hpath : pa = pb :=
    hab.sublist.eq_of_length (Nat.le_antisymm hab.length_le hba.length_le)
  subst hpath; rfl

/-- A bounded pair of lifetimes has an intersection (LUB). -/
theorem exists_lifetimeIntersection_of_le {a b u : Lifetime}
    (ha : a ≤ u) (hb : b ≤ u) : ∃ m, LifetimeIntersection a b m := by
  rcases lifetime_comparable_of_le ha hb with h | h
  · exact ⟨b, LifetimeIntersection.left h⟩
  · exact ⟨a, LifetimeIntersection.right h⟩

/-- Reassociation of lifetime intersections:
`(headLife ∩ restLife) ∩ lf2 = headLife ∩ (restLife ∩ lf2)`. -/
theorem LifetimeIntersection.assoc_recombine
    {headLife restLife lf1 lf2 lf tailLf : Lifetime}
    (hHeadRest : LifetimeIntersection headLife restLife lf1)
    (hOuter : LifetimeIntersection lf1 lf2 lf)
    (hTail : LifetimeIntersection restLife lf2 tailLf) :
    LifetimeIntersection headLife tailLf lf := by
  have hHeadLf : headLife ≤ lf :=
    LifetimeOutlives.trans hHeadRest.left_le hOuter.left_le
  have hRestLf : restLife ≤ lf :=
    LifetimeOutlives.trans hHeadRest.right_le hOuter.left_le
  have hLf2Lf : lf2 ≤ lf := hOuter.right_le
  have hTailLf : tailLf ≤ lf := hTail.le_of_le hRestLf hLf2Lf
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hHeadLf
    · exact hTailLf
  · intro y hy
    have hHeadY : headLife ≤ y := hy (by simp)
    have hTailY : tailLf ≤ y := hy (by simp)
    have hRestY : restLife ≤ y := LifetimeOutlives.trans hTail.left_le hTailY
    have hLf2Y : lf2 ≤ y := LifetimeOutlives.trans hTail.right_le hTailY
    have hLf1Y : lf1 ≤ y := hHeadRest.le_of_le hHeadY hRestY
    exact hOuter.le_of_le hLf1Y hLf2Y

/-- Inductive core of the append combinator: the first list may type at any
union type `U1` *bounded* by `.ty P`; the second is fixed at `.ty P`. -/
theorem LValTargetsTyping.append_le {env : Env} {P : Ty} {L2 : List LVal}
    {lf2 : Lifetime} (h2 : LValTargetsTyping env L2 (.ty P) lf2) :
    ∀ {L1 : List LVal} {U1 : PartialTy} {lf1 : Lifetime},
      LValTargetsTyping env L1 U1 lf1 → PartialTyStrengthens U1 (.ty P) →
      ∀ {lf : Lifetime}, LifetimeIntersection lf1 lf2 lf →
      LValTargetsTyping env (L1 ++ L2) (.ty P) lf := by
  intro L1 U1 lf1 h1
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun L1 U1 lf1 _ =>
      PartialTyStrengthens U1 (.ty P) →
      ∀ {lf : Lifetime}, LifetimeIntersection lf1 lf2 lf →
      LValTargetsTyping env (L1 ++ L2) (.ty P) lf)
    ?_ ?_ ?_ ?_ ?_ ?_ h1
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · -- empty: L1 = [], lf1 = root
    intro ty _hvars _hU1 lf hinter
    have hroot : Lifetime.root ≤ lf2 := by
      simp [LifetimeOutlives, Core.Lifetime.contains, Lifetime.root]
    have hlf2le : lf2 ≤ lf := hinter.right_le
    have hlelf2 : lf ≤ lf2 := hinter.le_of_le hroot (LifetimeOutlives.refl lf2)
    have heq : lf = lf2 := lifetime_le_antisymm hlelf2 hlf2le
    subst heq
    simpa using h2
  · -- singleton: L1 = [target], target : .ty ty
    intro target ty lifetime htarget _ih hU1 lf hinter
    exact LValTargetsTyping.cons htarget h2 (partialTyUnion_self_of_le hU1) hinter
  · -- cons: L1 = target :: rest
    intro target rest headTy headLife restLife life restTy unionTy
      hhead hrest hunion hintersect _ihHead ihRest hU1 lf hinter
    have hHeadLe : PartialTyStrengthens (.ty headTy) (.ty P) :=
      partialTyStrengthens_trans (PartialTyUnion.left_strengthens hunion) hU1
    have hRestLe : PartialTyStrengthens restTy (.ty P) :=
      partialTyStrengthens_trans (PartialTyUnion.right_strengthens hunion) hU1
    -- both `restLife` and `lf2` are below `lf`, so their intersection exists
    have hRestLf : restLife ≤ lf :=
      LifetimeOutlives.trans hintersect.right_le hinter.left_le
    have hLf2Lf : lf2 ≤ lf := hinter.right_le
    obtain ⟨tailLf, htail⟩ := exists_lifetimeIntersection_of_le hRestLf hLf2Lf
    have htailTyping : LValTargetsTyping env (rest ++ L2) (.ty P) tailLf :=
      ihRest hRestLe htail
    have hrecombine : LifetimeIntersection headLife tailLf lf :=
      LifetimeIntersection.assoc_recombine hintersect hinter htail
    exact LValTargetsTyping.cons hhead htailTyping
      (partialTyUnion_self_of_le hHeadLe) hrecombine

/-- **Append combinator.**  Two joint typings at the same borrow pointee `P`
combine into a joint typing of the concatenation, given a lifetime
intersection. -/
theorem LValTargetsTyping.append {env : Env} {L1 L2 : List LVal} {P : Ty}
    {lf1 lf2 lf : Lifetime}
    (h1 : LValTargetsTyping env L1 (.ty P) lf1)
    (h2 : LValTargetsTyping env L2 (.ty P) lf2)
    (hinter : LifetimeIntersection lf1 lf2 lf) :
    LValTargetsTyping env (L1 ++ L2) (.ty P) lf :=
  h2.append_le h1 PartialTyStrengthens.reflex hinter

/-! ## Per-target deep transport across same-shape strengthening

The existing per-lval transport `lvalTyping_transport_of_sameShapeStrengthening`
re-types an lval in the (weaker) `result` env with a *flat*-strengthened type.
For a borrow *target* (a full type `.ty ptee`) this bridges to `TyDeepStrengthens`
via step 1, giving the deep-strengthening relation the eventual `thin` must
track.  (Note this is the *per-target* half; the full joint-typing transport at a
*fixed* pointee is not derivable from these hypotheses alone — transporting a
target weakens its type, which may exceed the borrow pointee, so result-side
well-formedness is genuinely required.  See the report.) -/

/-- Flat `.ty`-strengthening yields deep full-type strengthening. -/
theorem TyDeepStrengthens.of_flat_ty {a b : Ty}
    (h : PartialTyStrengthens (.ty a) (.ty b)) : TyDeepStrengthens a b := by
  cases PartialTyDeepStrengthens.of_flat h with
  | ty hd => exact hd

/-- A borrow target transports across a same-shape strengthening to a result
typing whose pointee deep-strengthens from the source pointee. -/
theorem LValTyping.target_transport_deep {source result : Env}
    (hmap : EnvSameShapeStrengthening source result)
    (hcoh : Coherent result) (hlin : Linearizable result)
    {w : LVal} {ptee : Ty} {lf : Lifetime}
    (hw : LValTyping source w (.ty ptee) lf) :
    ∃ ptee' lf', LValTyping result w (.ty ptee') lf' ∧ TyDeepStrengthens ptee ptee' := by
  obtain ⟨pty', lf', htyp', hstr, hshape⟩ :=
    lvalTyping_transport_of_sameShapeStrengthening hmap hcoh hlin hw
  cases pty' with
  | ty ty' => exact ⟨ty', lf', htyp', TyDeepStrengthens.of_flat_ty hstr⟩
  | box _ => exact absurd hstr PartialTyStrengthens.not_ty_to_box
  | undef _ => simp [PartialTy.sameShape] at hshape

/-! ## Joint-typing transport at a fixed pointee

To re-assemble a borrow's joint target typing in the (weaker) `result` env we
transport each target.  The catch (see the deviation note above): a transported
target type *weakens*, so the union of the transported targets may exceed the
borrow pointee `P`.  A result-side bound (each target re-types to a type `⊑ P`,
with a common lifetime ceiling) re-pins the union back to `P` — collectively, not
per target.  The engine `LValTargetsTyping.transport_bounded` produces a result
joint typing whose union is `≈ P` (mutually `⊑`); see the report for why the
*exact*-`P` wrapper (and `parallelWriteCoherent`) is blocked at borrow-target
list order for singleton/empty target lists. -/

/-- The union is the *least* upper bound: any common upper bound of the inputs
dominates it. -/
theorem PartialTyUnion.least {a b u z : PartialTy}
    (h : PartialTyUnion a b u)
    (ha : PartialTyStrengthens a z) (hb : PartialTyStrengthens b z) :
    PartialTyStrengthens u z := by
  apply h.2
  intro c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · exact ha
  · exact hb

/-- The concatenation of two borrow target lists (same mutability/pointee) is the
join of the two borrow types. -/
theorem partialTyUnion_borrow_append {mutable : Bool} {Ta Tb : List LVal} {p : Ty} :
    PartialTyUnion (.ty (.borrow mutable Ta p)) (.ty (.borrow mutable Tb p))
      (.ty (.borrow mutable (Ta ++ Tb) p)) := by
  constructor
  · intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact PartialTyStrengthens.borrow (fun t ht => List.mem_append.mpr (Or.inl ht))
    · exact PartialTyStrengthens.borrow (fun t ht => List.mem_append.mpr (Or.inr ht))
  · intro w hw
    have hwa : PartialTyStrengthens (.ty (.borrow mutable Ta p)) w := hw (by simp)
    have hwb : PartialTyStrengthens (.ty (.borrow mutable Tb p)) w := hw (by simp)
    cases hwa with
    | reflex =>
        rcases PartialTyStrengthens.from_borrow_inv hwb with ⟨Tt, hweq2, hTbTa⟩
        injection hweq2 with _ hTeq _
        subst hTeq
        exact PartialTyStrengthens.borrow
          (List.append_subset.mpr ⟨fun t ht => ht, hTbTa⟩)
    | borrow hTaTw =>
        rcases PartialTyStrengthens.from_borrow_inv hwb with ⟨Tt, hweq2, hTbTw⟩
        injection hweq2 with _ hTeq _
        subst hTeq
        exact PartialTyStrengthens.borrow (List.append_subset.mpr ⟨hTaTw, hTbTw⟩)
    | intoUndef hinner =>
        rcases PartialTyStrengthens.from_borrow_inv hinner with ⟨Tw, hueq, hTaTw⟩
        subst hueq
        have hwb' : PartialTyStrengthens (.ty (.borrow mutable Tb p))
            (.ty (.borrow mutable Tw p)) :=
          PartialTyStrengthens.ty_to_undef_inv hwb
        rcases PartialTyStrengthens.from_borrow_inv hwb' with ⟨Tt, hweq2, hTbTw⟩
        injection hweq2 with _ hTeq _
        subst hTeq
        exact PartialTyStrengthens.intoUndef
          (PartialTyStrengthens.borrow (List.append_subset.mpr ⟨hTaTw, hTbTw⟩))

/-- Two full types bounded above by a common full type have a join (which is also
bounded by it).  The partial-type lattice is bounded-complete on the `.ty`
fragment used by `LValTargetsTyping`. -/
theorem tyUnion_exists_of_le : ∀ {z a b : Ty},
    PartialTyStrengthens (.ty a) (.ty z) → PartialTyStrengthens (.ty b) (.ty z) →
    ∃ u : Ty, PartialTyUnion (.ty a) (.ty b) (.ty u) ∧
      PartialTyStrengthens (.ty u) (.ty z) := by
  intro z
  refine Ty.rec
    (motive_1 := fun z => ∀ {a b : Ty},
      PartialTyStrengthens (.ty a) (.ty z) → PartialTyStrengthens (.ty b) (.ty z) →
      ∃ u : Ty, PartialTyUnion (.ty a) (.ty b) (.ty u) ∧
        PartialTyStrengthens (.ty u) (.ty z))
    (motive_2 := fun _ => True)
    ?unit ?int ?borrow ?box ?bool ?pty ?pbox ?undef z
  · intro a b ha hb
    have ha' : a = .unit := PartialTyStrengthens.to_unit_inv ha
    have hb' : b = .unit := PartialTyStrengthens.to_unit_inv hb
    subst ha'; subst hb'
    exact ⟨.unit, PartialTyUnion.self _, PartialTyStrengthens.reflex⟩
  · intro a b ha hb
    have ha' : a = .int := PartialTyStrengthens.to_int_inv ha
    have hb' : b = .int := PartialTyStrengthens.to_int_inv hb
    subst ha'; subst hb'
    exact ⟨.int, PartialTyUnion.self _, PartialTyStrengthens.reflex⟩
  · intro mutable targets pointee _ihPointee a b ha hb
    rcases PartialTyStrengthens.to_borrow_inv ha with ⟨Ta, ha', hTaTz⟩
    subst ha'
    rcases PartialTyStrengthens.to_borrow_inv hb with ⟨Tb, hb', hTbTz⟩
    subst hb'
    exact ⟨.borrow mutable (Ta ++ Tb) pointee, partialTyUnion_borrow_append,
      PartialTyStrengthens.borrow (List.append_subset.mpr ⟨hTaTz, hTbTz⟩)⟩
  · intro inner ih a b ha hb
    rcases PartialTyStrengthens.to_box_ty_inv ha with ⟨ai, ha', hai⟩
    subst ha'
    rcases PartialTyStrengthens.to_box_ty_inv hb with ⟨bi, hb', hbi⟩
    subst hb'
    rcases ih hai hbi with ⟨ui, huni, hub⟩
    exact ⟨.box ui, PartialTyUnion.tyBox huni, PartialTyStrengthens.tyBox hub⟩
  · intro a b ha hb
    have ha' : a = .bool := PartialTyStrengthens.to_bool_inv ha
    have hb' : b = .bool := PartialTyStrengthens.to_bool_inv hb
    subst ha'; subst hb'
    exact ⟨.bool, PartialTyUnion.self _, PartialTyStrengthens.reflex⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- **Env monotonicity of lval typing, given both typings.**  When an lval is
typed in *both* a stronger `source` and a same-shape-weaker `result`, the source
type `⊑`-strengthens into the result type.  No coherence needed: the result
typing is supplied, not constructed. -/
theorem lvalTyping_mono_of_both {source result : Env}
    (hmap : EnvSameShapeStrengthening source result) :
    ∀ {lv : LVal} {p p' : PartialTy} {lf lf' : Lifetime},
      LValTyping source lv p lf → LValTyping result lv p' lf' →
      PartialTyStrengthens p p' := by
  intro lv
  induction lv with
  | var x =>
      intro p p' lf lf' hs hr
      cases hs with
      | var hslotS =>
        cases hr with
        | var hslotR =>
          rcases hmap.1 x _ hslotR with ⟨s2, hs2, _, hstr, _⟩
          have heq : s2 = _ := Option.some.inj (hs2.symm.trans hslotS)
          subst heq
          exact hstr
  | deref lv0 ih =>
      intro p p' lf lf' hs hr
      cases hs with
      | box hsb =>
          cases hr with
          | box hrb => exact PartialTyStrengthens.box_inv (ih hsb hrb)
          | borrow hrbor _ => exact (by cases ih hsb hrbor)
      | borrow hsbor _ =>
          cases hr with
          | box hrb => exact absurd (ih hsbor hrb) PartialTyStrengthens.not_ty_to_box
          | borrow hrbor _ =>
              have hbb := ih hsbor hrbor
              rcases PartialTyStrengthens.from_borrow_inv hbb with ⟨_, heq, _⟩
              injection heq with _ _ hp
              subst hp
              exact PartialTyStrengthens.reflex

/-- **Joint-typing transport engine.**  A source joint typing transports to a
result joint typing whose union is bounded by `.ty P` (and dominates the source
union), provided each target re-types in `result` to a type `⊑ .ty P` under a
common lifetime ceiling `commonLife`. -/
theorem LValTargetsTyping.transport_bounded {source result : Env} {P : Ty}
    {commonLife : Lifetime}
    (hmap : EnvSameShapeStrengthening source result) :
    ∀ {W : List LVal} {U : PartialTy} {lf : Lifetime},
      LValTargetsTyping source W U lf →
      PartialTyStrengthens U (.ty P) →
      (∀ w ∈ W, ∃ qw lqw, LValTyping result w (.ty qw) lqw ∧
        PartialTyStrengthens (.ty qw) (.ty P) ∧ lqw ≤ commonLife) →
      ∃ U' lf', LValTargetsTyping result W U' lf' ∧
        PartialTyStrengthens U U' ∧ PartialTyStrengthens U' (.ty P) ∧
        lf' ≤ commonLife := by
  intro W U lf h
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun W U _ _ =>
      PartialTyStrengthens U (.ty P) →
      (∀ w ∈ W, ∃ qw lqw, LValTyping result w (.ty qw) lqw ∧
        PartialTyStrengthens (.ty qw) (.ty P) ∧ lqw ≤ commonLife) →
      ∃ U' lf', LValTargetsTyping result W U' lf' ∧
        PartialTyStrengthens U U' ∧ PartialTyStrengthens U' (.ty P) ∧
        lf' ≤ commonLife)
    ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · -- empty: W = [], U = .ty ty
    intro ty hvars hUP _hRI
    refine ⟨.ty ty, Lifetime.root, LValTargetsTyping.empty hvars,
      PartialTyStrengthens.reflex, hUP, ?_⟩
    simp [LifetimeOutlives, Core.Lifetime.contains, Lifetime.root]
  · -- singleton: W = [target]
    intro target ty lifetime htarget _ih hUP hRI
    rcases hRI target (by simp) with ⟨qw, lqw, htyp_r, hqwP, hlq⟩
    exact ⟨.ty qw, lqw, LValTargetsTyping.singleton htyp_r,
      lvalTyping_mono_of_both hmap htarget htyp_r, hqwP, hlq⟩
  · -- cons: W = target :: rest
    intro target rest headTy headLife restLife life restTy unionTy
      hhead hrest hunion hintersect _ihHead ihRest hUP hRI
    rcases hRI target (by simp) with ⟨qh, lqh, hhd_r, hqhP, hlqh⟩
    have hrestUP : PartialTyStrengthens restTy (.ty P) :=
      partialTyStrengthens_trans (PartialTyUnion.right_strengthens hunion) hUP
    rcases ihRest hrestUP (fun w hw => hRI w (List.mem_cons.mpr (Or.inr hw))) with
      ⟨restU', restLf', hrest_r, hrestMono, hrestU'P, hrestLfBound⟩
    rcases LValTargetsTyping.output_full hrest_r with ⟨restU'Ty, hrestEq⟩
    subst hrestEq
    rcases tyUnion_exists_of_le hqhP hrestU'P with ⟨u, hjoinU, hub⟩
    obtain ⟨lf', hlf'inter⟩ :=
      exists_lifetimeIntersection_of_le hlqh hrestLfBound
    refine ⟨.ty u, lf', LValTargetsTyping.cons hhd_r hrest_r hjoinU hlf'inter, ?_, hub,
      LifetimeIntersection.le_of_le hlf'inter hlqh hrestLfBound⟩
    refine PartialTyUnion.least hunion ?_ ?_
    · exact partialTyStrengthens_trans (lvalTyping_mono_of_both hmap hhead hhd_r)
        (PartialTyUnion.left_strengthens hjoinU)
    · exact partialTyStrengthens_trans hrestMono (PartialTyUnion.right_strengthens hjoinU)

end Paper
end LwRust
