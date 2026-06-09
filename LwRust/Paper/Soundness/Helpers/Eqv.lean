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
After recursive full-box strengthening, ordinary `Ty.eqv` is strong enough for
strengthening transport.  Exact target-list determinism is intentionally not
stated here: target-list joins may reorder borrow-target lists under boxes, so
`eqvX` would be too strong for those joins. -/

/-- Exact type equivalence: like `Ty.eqv` but `box` contents must be *equal*. -/
def Ty.eqvX : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .borrow m₁ t₁, .borrow m₂ t₂ => m₁ = m₂ ∧ t₁ ⊆ t₂ ∧ t₂ ⊆ t₁
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

theorem Ty.eqv_of_eqvX : {a b : Ty} → Ty.eqvX a b → Ty.eqv a b
  | .unit, .unit, _ => trivial
  | .int, .int, _ => trivial
  | .borrow _ _, .borrow _ _, h => h
  | .box _, .box _, h => by simp only [Ty.eqvX] at h; subst h; exact Ty.eqv_refl _
  | .unit, .int, h => by simp only [Ty.eqvX] at h
  | .unit, .borrow _ _, h => by simp only [Ty.eqvX] at h
  | .unit, .box _, h => by simp only [Ty.eqvX] at h
  | .int, .unit, h => by simp only [Ty.eqvX] at h
  | .int, .borrow _ _, h => by simp only [Ty.eqvX] at h
  | .int, .box _, h => by simp only [Ty.eqvX] at h
  | .borrow _ _, .unit, h => by simp only [Ty.eqvX] at h
  | .borrow _ _, .int, h => by simp only [Ty.eqvX] at h
  | .borrow _ _, .box _, h => by simp only [Ty.eqvX] at h
  | .box _, .unit, h => by simp only [Ty.eqvX] at h
  | .box _, .int, h => by simp only [Ty.eqvX] at h
  | .box _, .borrow _ _, h => by simp only [Ty.eqvX] at h

theorem PartialTy.eqv_of_eqvX : {a b : PartialTy} → PartialTy.eqvX a b → PartialTy.eqv a b
  | .ty _, .ty _, h => Ty.eqv_of_eqvX h
  | .box p1, .box p2, h => PartialTy.eqv_of_eqvX (a := p1) (b := p2) h
  | .undef _, .undef _, h => Ty.eqv_of_eqvX h
  | .ty _, .box _, h => by simp only [PartialTy.eqvX] at h
  | .ty _, .undef _, h => by simp only [PartialTy.eqvX] at h
  | .box _, .ty _, h => by simp only [PartialTy.eqvX] at h
  | .box _, .undef _, h => by simp only [PartialTy.eqvX] at h
  | .undef _, .ty _, h => by simp only [PartialTy.eqvX] at h
  | .undef _, .box _, h => by simp only [PartialTy.eqvX] at h

theorem PartialTy.sameShape_of_eqvX {a b : PartialTy} (h : PartialTy.eqvX a b) :
    PartialTy.sameShape a b :=
  PartialTy.sameShape_of_eqv (PartialTy.eqv_of_eqvX h)

/-- `Ty`-level core: an `eqvX` pair of full types strengthens (left to right). -/
theorem partialTyStrengthens_ty_of_eqvX {t1 t2 : Ty} (h : Ty.eqvX t1 t2) :
    PartialTyStrengthens (.ty t1) (.ty t2) := by
  cases t1 <;> cases t2 <;> simp only [Ty.eqvX] at h <;>
    first
      | exact PartialTyStrengthens.reflex
      | (obtain ⟨rfl, hsub, _⟩ := h; exact PartialTyStrengthens.borrow hsub)
      | (subst h; exact PartialTyStrengthens.reflex)

/-- `eqvX` types strengthen to one another (the reflex-case core of the transfer
below). -/
theorem partialTyStrengthens_of_eqvX :
    {a b : PartialTy} → PartialTy.eqvX a b → PartialTyStrengthens a b
  | .ty _, .ty _, h => partialTyStrengthens_ty_of_eqvX h
  | .box _, .box _, h => PartialTyStrengthens.box (partialTyStrengthens_of_eqvX h)
  | .undef _, .undef _, h => PartialTyStrengthens.undefLeft (partialTyStrengthens_ty_of_eqvX h)
  | .ty _, .box _, h => by simp only [PartialTy.eqvX] at h
  | .ty _, .undef _, h => by simp only [PartialTy.eqvX] at h
  | .box _, .ty _, h => by simp only [PartialTy.eqvX] at h
  | .box _, .undef _, h => by simp only [PartialTy.eqvX] at h
  | .undef _, .ty _, h => by simp only [PartialTy.eqvX] at h
  | .undef _, .box _, h => by simp only [PartialTy.eqvX] at h

/-- Strengthening transfers along `eqvX` on the right: `c ⊑ a` and `a ≈X b` give
`c ⊑ b`.  This is the wall-breaking lemma — it holds for `eqvX` (but **not** for
`eqv`) precisely because `eqvX` keeps `Ty.box` contents exact. -/
theorem partialTyStrengthens_eqvX_right {c a b : PartialTy}
    (hca : PartialTyStrengthens c a) (hab : PartialTy.eqvX a b) :
    PartialTyStrengthens c b := by
  induction hca generalizing b with
  | reflex => exact partialTyStrengthens_of_eqvX hab
  | @box cL aL _hcL ih =>
      cases b with
      | box bL => exact PartialTyStrengthens.box (ih (by simpa [PartialTy.eqvX] using hab))
      | ty _ => simp [PartialTy.eqvX] at hab
      | undef _ => simp [PartialTy.eqvX] at hab
  | @tyBox cT aT hinner _ih =>
      cases b with
      | ty tb =>
          cases tb with
          | box bT =>
              simp only [PartialTy.eqvX, Ty.eqvX] at hab
              subst hab
              exact PartialTyStrengthens.tyBox hinner
          | unit => simp [PartialTy.eqvX, Ty.eqvX] at hab
          | int => simp [PartialTy.eqvX, Ty.eqvX] at hab
          | borrow _ _ => simp [PartialTy.eqvX, Ty.eqvX] at hab
      | box _ => simp [PartialTy.eqvX] at hab
      | undef _ => simp [PartialTy.eqvX] at hab
  | @borrow m cL aL hsub =>
      cases b with
      | ty tb =>
          cases tb with
          | borrow m' bL =>
              simp only [PartialTy.eqvX, Ty.eqvX] at hab
              obtain ⟨rfl, haLbL, _⟩ := hab
              exact PartialTyStrengthens.borrow (fun x hx => haLbL (hsub hx))
          | unit => simp [PartialTy.eqvX, Ty.eqvX] at hab
          | int => simp [PartialTy.eqvX, Ty.eqvX] at hab
          | box _ => simp [PartialTy.eqvX, Ty.eqvX] at hab
      | box _ => simp [PartialTy.eqvX] at hab
      | undef _ => simp [PartialTy.eqvX] at hab
  | @undefLeft cT aT _h ih =>
      cases b with
      | undef bT =>
          exact PartialTyStrengthens.undefLeft (ih (by simpa [PartialTy.eqvX] using hab))
      | ty _ => simp [PartialTy.eqvX] at hab
      | box _ => simp [PartialTy.eqvX] at hab
  | @intoUndef cT aT _h ih =>
      cases b with
      | undef bT =>
          exact PartialTyStrengthens.intoUndef (ih (by simpa [PartialTy.eqvX] using hab))
      | ty _ => simp [PartialTy.eqvX] at hab
      | box _ => simp [PartialTy.eqvX] at hab
  | @boxIntoUndef cL aT h _ih =>
      cases b with
      | undef bT =>
          have hbox : Ty.eqvX (.box aT) bT := by simpa [PartialTy.eqvX] using hab
          have : bT = .box aT := by cases bT <;> simp_all [Ty.eqvX]
          subst this
          exact PartialTyStrengthens.boxIntoUndef h
      | ty _ => simp [PartialTy.eqvX] at hab
      | box _ => simp [PartialTy.eqvX] at hab

/-- **Strengthening transport** (the join/strengthen keystone).  If the source
environment `e` strengthens to `e'` at the slot level *shape-preservingly*
(`hstr`), both are linearizable, and `e'` is `Coherent`, then any `LValTyping` in
`e` transports to `e'` with a `sameShape`, strengthened type.

Proved by strong induction on the rank of the lval's base variable (φ from
`Linearizable e`), structural on the lval.  The deref-borrow case is the crux:
the inner borrow lval transports (structural IH) to a borrow `&tgts'` in `e'`;
`Coherent e'` supplies a joint typing of `tgts'`; and the two joint types are
related via `lvalTargetsTyping_subset_strengthen`, whose per-member facts come
from the rank IH (strictly smaller targets) reconciled in `e'` by
`lvalTyping_eqv` + `partialTyStrengthens_eqv_right`.  Recursive full-box
strengthening makes ordinary `eqv` strong enough here; exact boxed contents are
not stable for target-list joins. -/
theorem lvalTyping_strengthen_transport {e e' : Env} {φ : Name → Nat}
    (hstr : ∀ x sE, e.slotAt x = some sE →
      ∃ sE', e'.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hφ' : ∀ x slot, e'.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcoh' : Coherent e') :
    ∀ (lv : LVal) {p : PartialTy} {lf : Lifetime},
      LValTyping e lv p lf →
      ∃ p' lf', LValTyping e' lv p' lf' ∧
        PartialTy.sameShape p p' ∧ PartialTyStrengthens p p' := by
  suffices h : ∀ (n : Nat) (lv : LVal), φ (LVal.base lv) = n →
      ∀ {p : PartialTy} {lf : Lifetime},
        LValTyping e lv p lf →
        ∃ p' lf', LValTyping e' lv p' lf' ∧
          PartialTy.sameShape p p' ∧ PartialTyStrengthens p p' by
    intro lv p lf hp
    exact h (φ (LVal.base lv)) lv rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro lv
    induction lv with
    | var x =>
        intro _hbase p lf hp
        cases hp with
        | var hslot =>
            rcases hstr x _ hslot with ⟨sE', hsE', hshape, hstrong⟩
            exact ⟨sE'.ty, sE'.lifetime, LValTyping.var hsE', hshape, hstrong⟩
    | deref lv' ihStruct =>
        intro hbase p lf hp
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        cases hp with
        | box hbox =>
            rcases ihStruct hbase' hbox with ⟨pw', lfw', hw', hshapeW, hstrongW⟩
            cases pw' with
            | box inner' =>
                refine ⟨inner', lfw', LValTyping.box hw', ?_, ?_⟩
                · simpa [PartialTy.sameShape] using hshapeW
                · cases hstrongW with
                  | reflex => exact PartialTyStrengthens.reflex
                  | box hh => exact hh
            | ty _ => simp [PartialTy.sameShape] at hshapeW
            | undef _ => simp [PartialTy.sameShape] at hshapeW
        | borrow hbor htgts =>
            rename_i mutb tgts bLf
            rcases ihStruct hbase' hbor with ⟨pw', lfw', hw', hshapeW, hstrongW⟩
            cases pw' with
            | ty tw' =>
                rcases PartialTyStrengthens.from_borrow_inv hstrongW with
                  ⟨tgts', htw'eq, hsub⟩
                subst htw'eq
                rcases hcoh' lv' mutb tgts' lfw' hw' with ⟨jTy, jLf, htgts'⟩
                rcases LValTargetsTyping.output_full htgts with ⟨pTy, hpFull⟩
                subst hpFull
                have hlow : ∀ t : LVal, t ∈ tgts → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutb tgts)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hbor _ hvar
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
                have hmem : ∀ m, m ∈ tgts → ∀ mE mE' lmE lmE',
                    LValTyping e m (.ty mE) lmE → LValTyping e' m (.ty mE') lmE' →
                    Ty.sameShape mE mE' ∧ PartialTyStrengthens (.ty mE) (.ty mE') := by
                  intro m hmtgts mE mE' lmE lmE' hmE hmE'
                  rcases ihRank (φ (LVal.base m)) (hlow m hmtgts) m rfl hmE with
                    ⟨pm', lfm', hm', hshapeM, hstrongM⟩
                  have heqv : PartialTy.eqv pm' (.ty mE') :=
                    lvalTyping_eqv hφ' m hm' hmE'
                  have hsh : PartialTy.sameShape (.ty mE) (.ty mE') :=
                    PartialTy.sameShape_trans hshapeM (PartialTy.sameShape_of_eqv heqv)
                  refine ⟨by simpa [PartialTy.sameShape] using hsh, ?_⟩
                  exact partialTyStrengthens_eqv_right hstrongM heqv
                rcases lvalTargetsTyping_subset_strengthen hsub hmem htgts htgts' with
                  ⟨hshapeJoint, hstrongJoint⟩
                exact ⟨.ty jTy, jLf, LValTyping.borrow hw' htgts',
                  by simpa [PartialTy.sameShape] using hshapeJoint, hstrongJoint⟩
            | box _ => simp [PartialTy.sameShape] at hshapeW
            | undef _ => simp [PartialTy.sameShape] at hshapeW

/-- **Rank-bounded** transport keystone: `Coherent e'` restricted to lvals of
rank `≤ N` suffices to transport lvals of rank `≤ N` (the keystone only queries
`Coherent e'` at the transported lval's own rank).  This is what lets
`Coherent`/`ContainedBorrows` on a join/write be *bootstrapped* by strong rank
induction (the full keystone assumes `Coherent e'` outright and cannot). -/
theorem lvalTyping_strengthen_transport_bounded {e e' : Env} {φ : Name → Nat}
    (N : Nat)
    (hstr : ∀ x sE, e.slotAt x = some sE →
      ∃ sE', e'.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hφ : ∀ x slot, e.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hφ' : ∀ x slot, e'.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x)
    (hcoh' : ∀ lv'' m'' T'' bLf'', φ (LVal.base lv'') ≤ N →
      LValTyping e' lv'' (.ty (.borrow m'' T'')) bLf'' →
      ∃ ty lt, LValTargetsTyping e' T'' (.ty ty) lt) :
    ∀ (lv : LVal), φ (LVal.base lv) ≤ N → ∀ {p : PartialTy} {lf : Lifetime},
      LValTyping e lv p lf →
      ∃ p' lf', LValTyping e' lv p' lf' ∧
        PartialTy.sameShape p p' ∧ PartialTyStrengthens p p' := by
  suffices h : ∀ (n : Nat), n ≤ N → ∀ (lv : LVal), φ (LVal.base lv) = n →
      ∀ {p : PartialTy} {lf : Lifetime},
        LValTyping e lv p lf →
        ∃ p' lf', LValTyping e' lv p' lf' ∧
          PartialTy.sameShape p p' ∧ PartialTyStrengthens p p' by
    intro lv hle p lf hp
    exact h (φ (LVal.base lv)) hle lv rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihRank =>
    intro hNle lv
    induction lv with
    | var x =>
        intro _hbase p lf hp
        cases hp with
        | var hslot =>
            rcases hstr x _ hslot with ⟨sE', hsE', hshape, hstrong⟩
            exact ⟨sE'.ty, sE'.lifetime, LValTyping.var hsE', hshape, hstrong⟩
    | deref lv' ihStruct =>
        intro hbase p lf hp
        have hbase' : φ (LVal.base lv') = n := by simpa [LVal.base] using hbase
        cases hp with
        | box hbox =>
            rcases ihStruct hbase' hbox with ⟨pw', lfw', hw', hshapeW, hstrongW⟩
            cases pw' with
            | box inner' =>
                refine ⟨inner', lfw', LValTyping.box hw', ?_, ?_⟩
                · simpa [PartialTy.sameShape] using hshapeW
                · cases hstrongW with
                  | reflex => exact PartialTyStrengthens.reflex
                  | box hh => exact hh
            | ty _ => simp [PartialTy.sameShape] at hshapeW
            | undef _ => simp [PartialTy.sameShape] at hshapeW
        | borrow hbor htgts =>
            rename_i mutb tgts bLf
            rcases ihStruct hbase' hbor with ⟨pw', lfw', hw', hshapeW, hstrongW⟩
            cases pw' with
            | ty tw' =>
                rcases PartialTyStrengthens.from_borrow_inv hstrongW with
                  ⟨tgts', htw'eq, hsub⟩
                subst htw'eq
                rcases hcoh' lv' mutb tgts' lfw' (by omega) hw' with
                  ⟨jTy, jLf, htgts'⟩
                rcases LValTargetsTyping.output_full htgts with ⟨pTy, hpFull⟩
                subst hpFull
                have hlow : ∀ t : LVal, t ∈ tgts → φ (LVal.base t) < n := by
                  intro t ht
                  have hvar : LVal.base t ∈ PartialTy.vars
                      (.ty (.borrow mutb tgts)) := by
                    simp only [PartialTy.vars, Ty.vars, List.mem_map]
                    exact ⟨t, ht, rfl⟩
                  have hlt := (lvalTyping_vars_rank_lt hφ).1 hbor _ hvar
                  simpa [LVal.base] using lt_of_lt_of_eq hlt hbase'
                have hmem : ∀ m, m ∈ tgts → ∀ mE mE' lmE lmE',
                    LValTyping e m (.ty mE) lmE → LValTyping e' m (.ty mE') lmE' →
                    Ty.sameShape mE mE' ∧ PartialTyStrengthens (.ty mE) (.ty mE') := by
                  intro m hmtgts mE mE' lmE lmE' hmE hmE'
                  rcases ihRank (φ (LVal.base m)) (hlow m hmtgts)
                      (by have := hlow m hmtgts; omega) m rfl hmE with
                    ⟨pm', lfm', hm', hshapeM, hstrongM⟩
                  have heqv : PartialTy.eqv pm' (.ty mE') :=
                    lvalTyping_eqv hφ' m hm' hmE'
                  have hsh : PartialTy.sameShape (.ty mE) (.ty mE') :=
                    PartialTy.sameShape_trans hshapeM (PartialTy.sameShape_of_eqv heqv)
                  refine ⟨by simpa [PartialTy.sameShape] using hsh, ?_⟩
                  exact partialTyStrengthens_eqv_right hstrongM heqv
                rcases lvalTargetsTyping_subset_strengthen hsub hmem htgts htgts' with
                  ⟨hshapeJoint, hstrongJoint⟩
                exact ⟨.ty jTy, jLf, LValTyping.borrow hw' htgts',
                  by simpa [PartialTy.sameShape] using hshapeJoint, hstrongJoint⟩
            | box _ => simp [PartialTy.sameShape] at hshapeW
            | undef _ => simp [PartialTy.sameShape] at hshapeW


end Paper
end LwRust
