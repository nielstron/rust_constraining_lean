import LwRust.Paper.Soundness.Helpers.RuntimeFacts

/-!
# Ghost-slot erasure

Thinning lemmas for the anonymous equality slot.  The key invariant is that the
erased name is absent from every type reachable through the remaining
environment; this includes `undef` shadows because shape compatibility can still
inspect their carried type.
-/

namespace LwRust
namespace Paper

open Core

namespace Env

theorem fresh_erase (env : Env) (x : Name) :
    (env.erase x).fresh x := by
  simp [Env.fresh]

theorem erase_fresh_of_ne {env : Env} {x y : Name} :
    env.fresh y →
    y ≠ x →
    (env.erase x).fresh y := by
  intro hfresh hne
  unfold Env.fresh at hfresh ⊢
  simpa [Env.erase, hne] using hfresh

theorem erase_comm (env : Env) (x y : Name) :
    (env.erase x).erase y = (env.erase y).erase x := by
  cases env with
  | mk slotAt =>
      simp [Env.erase]
      funext z
      by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp [hzx, hzy]

@[simp] theorem erase_idem (env : Env) (x : Name) :
    (env.erase x).erase x = env.erase x := by
  cases env with
  | mk slotAt =>
      simp [Env.erase]
      funext z
      by_cases hz : z = x <;> simp [hz]

theorem erase_of_fresh {env : Env} {x : Name} :
    env.fresh x →
    env.erase x = env := by
  intro hfresh
  cases env with
  | mk slotAt =>
      unfold Env.fresh at hfresh
      simp [Env.erase]
      funext y
      by_cases hy : y = x
      · subst hy
        simpa using hfresh.symm
      · simp [hy]

theorem erase_update_ne (env : Env) {x y : Name} (slot : EnvSlot) :
    y ≠ x →
    (env.update y slot).erase x = (env.erase x).update y slot := by
  intro hne
  cases env with
  | mk slotAt =>
      simp [Env.erase, Env.update]
      funext z
      by_cases hzY : z = y
      · subst hzY
        simp [hne]
      · simp [hzY]

theorem erase_update_same_of_fresh {env : Env} {x : Name} {slot : EnvSlot} :
    env.fresh x →
    (env.update x slot).erase x = env := by
  intro hfresh
  cases env with
  | mk slotAt =>
      unfold Env.fresh at hfresh
      simp [Env.erase, Env.update]
      funext y
      by_cases hy : y = x
      · rw [hy]
        simpa using hfresh.symm
      · simp [hy]

theorem dropLifetime_erase (env : Env) (x : Name) (lifetime : Lifetime) :
    (env.dropLifetime lifetime).erase x =
      (env.erase x).dropLifetime lifetime := by
  cases env with
  | mk slotAt =>
      simp [Env.erase, Env.dropLifetime]
      funext y
      by_cases hy : y = x
      · subst hy
        simp
      · simp [hy]

theorem typeNameFresh_update {env : Env} {x ghost : Name} {slot : EnvSlot} :
    Env.TypeNameFresh env ghost →
    ghost ∉ PartialTy.allVars slot.ty →
    Env.TypeNameFresh (env.update x slot) ghost := by
  intro hfresh hslotFresh y candidate hslot
  by_cases hy : y = x
  · subst hy
    simp [Env.update] at hslot
    subst hslot
    exact hslotFresh
  · exact hfresh y candidate (by simpa [Env.update, hy] using hslot)

theorem typeNameFresh_erase {env : Env} {x ghost : Name} :
    Env.TypeNameFresh env ghost →
    Env.TypeNameFresh (env.erase x) ghost := by
  intro hfresh y slot hslot
  by_cases hy : y = x
  · subst hy
    simp [Env.erase] at hslot
  · exact hfresh y slot (by simpa [Env.erase, hy] using hslot)

theorem typeNameFresh_dropLifetime {env : Env} {lifetime : Lifetime}
    {ghost : Name} :
    Env.TypeNameFresh env ghost →
    Env.TypeNameFresh (env.dropLifetime lifetime) ghost := by
  intro hfresh x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨hslotOrig, _hne⟩
  exact hfresh x slot hslotOrig

end Env

theorem ValueTyping.typeNameFresh {typing : StoreTyping} {value : Value}
    {ty : Ty} {ghost : Name} :
    ValueTyping typing value ty →
    StoreTyping.TypeNameFresh typing ghost →
    ghost ∉ Ty.allVars ty := by
  intro hvalue hfresh
  cases hvalue with
  | unit => simp [Ty.allVars]
  | int => simp [Ty.allVars]
  | bool => simp [Ty.allVars]
  | ref hlookup =>
      exact hfresh _ _ hlookup

namespace LVal

@[simp] theorem mentions_iff_base {ghost : Name} :
    ∀ lv : LVal, LVal.Mentions ghost lv ↔ LVal.base lv = ghost
  | .var x => by simp [LVal.Mentions, LVal.base]
  | .deref lv => by simpa [LVal.Mentions, LVal.base] using mentions_iff_base (ghost := ghost) lv

theorem base_ne_of_not_mentions {ghost : Name} {lv : LVal} :
    ¬ LVal.Mentions ghost lv →
    LVal.base lv ≠ ghost := by
  intro hnot hbase
  exact hnot ((mentions_iff_base (ghost := ghost) lv).2 hbase)

theorem not_mentions_of_base_ne {ghost : Name} {lv : LVal} :
    LVal.base lv ≠ ghost →
    ¬ LVal.Mentions ghost lv := by
  intro hbase hmention
  exact hbase ((mentions_iff_base (ghost := ghost) lv).1 hmention)

end LVal

namespace PartialTy

theorem allVars_box {inner : PartialTy} {v : Name} :
    v ∈ PartialTy.allVars (.box inner) ↔ v ∈ PartialTy.allVars inner := by
  simp [PartialTy.allVars]

theorem vars_fresh_of_allVars_fresh {pt : PartialTy} {v : Name} :
    v ∉ PartialTy.allVars pt →
    v ∉ PartialTy.vars pt := by
  intro hfresh hmem
  exact hfresh (PartialTy.vars_subset_allVars (partialTy := pt) hmem)

end PartialTy

namespace Ty

def eraseName (ghost : Name) : Ty → Ty
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .borrow mutable targets =>
      .borrow mutable (targets.filter (fun target =>
        decide (LVal.base target ≠ ghost)))
  | .box inner => .box (eraseName ghost inner)

theorem no_allVars_of_loanFree :
    ∀ {ty : Ty}, TyLoanFree ty → ∀ v, v ∉ Ty.allVars ty
  | .unit, _ => by
      intro v hv
      simpa [Ty.allVars] using hv
  | .int, _ => by
      intro v hv
      simpa [Ty.allVars] using hv
  | .bool, _ => by
      intro v hv
      simpa [Ty.allVars] using hv
  | .borrow mutable targets, hloan => by
      intro v _hv
      exact (hloan mutable targets PartialTyContains.here).elim
  | .box inner, hloan => by
      intro v hv
      exact Ty.no_allVars_of_loanFree (ty := inner) (by
        intro mutable targets hcontains
        exact hloan mutable targets (PartialTyContains.tyBox hcontains))
        v (by simpa [Ty.allVars] using hv)

theorem no_vars_of_loanFree {ty : Ty} :
    TyLoanFree ty →
    ∀ v, v ∉ Ty.vars ty := by
  intro hloan v hv
  exact Ty.no_allVars_of_loanFree hloan v
    (Ty.vars_subset_allVars (ty := ty) hv)

end Ty

namespace PartialTy

def eraseName (ghost : Name) : PartialTy → PartialTy
  | .ty ty => .ty (Ty.eraseName ghost ty)
  | .box inner => .box (PartialTy.eraseName ghost inner)
  | .undef ty => .undef (Ty.eraseName ghost ty)

end PartialTy

theorem Ty.eraseName_no_vars (ghost : Name) :
    ∀ ty : Ty, ghost ∉ Ty.vars (Ty.eraseName ghost ty)
  | .unit => by simp [Ty.eraseName, Ty.vars]
  | .int => by simp [Ty.eraseName, Ty.vars]
  | .bool => by simp [Ty.eraseName, Ty.vars]
  | .box inner => by
      simpa [Ty.eraseName, Ty.vars] using Ty.eraseName_no_vars ghost inner
  | .borrow mutable targets => by
      intro hv
      simp [Ty.eraseName, Ty.vars, List.mem_map, List.mem_filter] at hv
      rcases hv with ⟨target, hmemKeep, hbase⟩
      exact hmemKeep.2 hbase

theorem Ty.eraseName_no_allVars (ghost : Name) :
    ∀ ty : Ty, ghost ∉ Ty.allVars (Ty.eraseName ghost ty)
  | .unit => by simp [Ty.eraseName, Ty.allVars]
  | .int => by simp [Ty.eraseName, Ty.allVars]
  | .bool => by simp [Ty.eraseName, Ty.allVars]
  | .box inner => by
      simpa [Ty.eraseName, Ty.allVars] using Ty.eraseName_no_allVars ghost inner
  | .borrow mutable targets => by
      intro hv
      simp [Ty.eraseName, Ty.allVars, List.mem_map, List.mem_filter] at hv
      rcases hv with ⟨target, hmemKeep, hbase⟩
      exact hmemKeep.2 hbase

theorem Ty.eraseName_eq_of_allVars_fresh {ghost : Name} :
    ∀ ty : Ty, ghost ∉ Ty.allVars ty → Ty.eraseName ghost ty = ty
  | .unit, _ => rfl
  | .int, _ => rfl
  | .bool, _ => rfl
  | .box inner, hfresh => by
      simp [Ty.eraseName, Ty.eraseName_eq_of_allVars_fresh inner
        (by simpa [Ty.allVars] using hfresh)]
  | .borrow mutable targets, hfresh => by
      have htargets :
          targets.filter (fun target => decide (LVal.base target ≠ ghost)) =
            targets := by
        exact List.filter_eq_self.mpr (by
          intro target hmem
          apply decide_eq_true
          intro hbase
          exact hfresh (by
            simp [Ty.allVars, List.mem_map]
            exact ⟨target, hmem, hbase⟩))
      change Ty.borrow mutable
        (targets.filter (fun target => decide (LVal.base target ≠ ghost))) =
          Ty.borrow mutable targets
      rw [htargets]

theorem PartialTy.eraseName_no_allVars (ghost : Name) :
    ∀ partialTy : PartialTy, ghost ∉ PartialTy.allVars
      (PartialTy.eraseName ghost partialTy)
  | .ty ty => by
      simpa [PartialTy.eraseName, PartialTy.allVars] using
        Ty.eraseName_no_allVars ghost ty
  | .box inner => by
      simpa [PartialTy.eraseName, PartialTy.allVars] using
        PartialTy.eraseName_no_allVars ghost inner
  | .undef ty => by
      simpa [PartialTy.eraseName, PartialTy.allVars] using
        Ty.eraseName_no_allVars ghost ty

theorem Ty.eraseName_strengthens_of_fresh {ghost : Name} :
    ∀ ty : Ty,
      ghost ∉ Ty.allVars ty →
      PartialTyStrengthens (.ty ty) (.ty (Ty.eraseName ghost ty))
  | .unit, _ => PartialTyStrengthens.reflex
  | .int, _ => PartialTyStrengthens.reflex
  | .bool, _ => PartialTyStrengthens.reflex
  | .box inner, hfresh => by
      exact PartialTyStrengthens.tyBox
        (Ty.eraseName_strengthens_of_fresh inner
          (by simpa [Ty.allVars] using hfresh))
  | .borrow mutable targets, hfresh => by
      have hfilter :
          targets.filter (fun target => decide (LVal.base target ≠ ghost)) =
            targets := by
        exact List.filter_eq_self.mpr (by
          intro target hmem
          apply decide_eq_true
          intro hbase
          exact hfresh (by
            simp [Ty.allVars, List.mem_map]
            exact ⟨target, hmem, hbase⟩))
      change PartialTyStrengthens (.ty (.borrow mutable targets))
        (.ty (.borrow mutable
          (targets.filter (fun target => decide (LVal.base target ≠ ghost)))))
      rw [hfilter]

theorem PartialTy.eraseName_strengthens_of_fresh {ghost : Name} :
    ∀ partialTy : PartialTy,
      ghost ∉ PartialTy.allVars partialTy →
      PartialTyStrengthens partialTy (PartialTy.eraseName ghost partialTy)
  | .ty ty, hfresh => by
      simpa [PartialTy.eraseName] using
        Ty.eraseName_strengthens_of_fresh ty
          (by simpa [PartialTy.allVars] using hfresh)
  | .box inner, hfresh => by
      exact PartialTyStrengthens.box
        (PartialTy.eraseName_strengthens_of_fresh inner
          (by simpa [PartialTy.allVars] using hfresh))
  | .undef ty, hfresh => by
      exact PartialTyStrengthens.undefLeft
        (Ty.eraseName_strengthens_of_fresh ty
          (by simpa [PartialTy.allVars] using hfresh))

theorem PartialTyStrengthens.allVars_mono {left right : PartialTy}
    {v : Name} :
    PartialTyStrengthens left right →
    v ∈ PartialTy.allVars left →
    v ∈ PartialTy.allVars right := by
  intro hstrength
  induction hstrength with
  | reflex =>
      intro hv
      exact hv
  | box _hinner ih =>
      intro hv
      exact ih (by simpa [PartialTy.allVars] using hv)
  | tyBox _hinner ih =>
      intro hv
      exact ih (by simpa [PartialTy.allVars, Ty.allVars] using hv)
  | borrow hsubset =>
      intro hv
      simp [PartialTy.allVars, Ty.allVars, List.mem_map] at hv ⊢
      rcases hv with ⟨target, hmem, hbase⟩
      exact ⟨target, hsubset hmem, hbase⟩
  | undefLeft _hinner ih =>
      intro hv
      exact ih (by simpa [PartialTy.allVars] using hv)
  | intoUndef _hinner ih =>
      intro hv
      exact ih (by simpa [PartialTy.allVars] using hv)
  | boxIntoUndef _hinner ih =>
      intro hv
      exact ih (by simpa [PartialTy.allVars, Ty.allVars] using hv)

theorem PartialTyStrengthens.to_eraseName_of_fresh {left right : PartialTy}
    {ghost : Name} :
    PartialTyStrengthens left right →
    ghost ∉ PartialTy.allVars left →
    PartialTyStrengthens left (PartialTy.eraseName ghost right) := by
  intro hstrength
  induction hstrength with
  | reflex =>
      intro hfresh
      exact PartialTy.eraseName_strengthens_of_fresh _ hfresh
  | box _hinner ih =>
      intro hfresh
      exact PartialTyStrengthens.box
        (ih (by simpa [PartialTy.allVars] using hfresh))
  | tyBox _hinner ih =>
      intro hfresh
      exact PartialTyStrengthens.tyBox
        (ih (by simpa [PartialTy.allVars, Ty.allVars] using hfresh))
  | @borrow mutable leftTargets rightTargets hsubset =>
      intro hfresh
      rw [PartialTy.eraseName, Ty.eraseName]
      exact PartialTyStrengthens.borrow (by
        intro target hmem
        simp [List.mem_filter]
        constructor
        · exact hsubset hmem
        · intro hbase
          exact hfresh (by
            simp [PartialTy.allVars, Ty.allVars, List.mem_map]
            exact ⟨target, hmem, hbase⟩))
  | undefLeft _hinner ih =>
      intro hfresh
      exact PartialTyStrengthens.undefLeft
        (ih (by simpa [PartialTy.allVars] using hfresh))
  | intoUndef _hinner ih =>
      intro hfresh
      exact PartialTyStrengthens.intoUndef
        (ih (by simpa [PartialTy.allVars] using hfresh))
  | boxIntoUndef _hinner ih =>
      intro hfresh
      exact PartialTyStrengthens.boxIntoUndef
        (ih (by simpa [PartialTy.allVars] using hfresh))

theorem PartialTyJoin.allVars_fresh {left right join : PartialTy} {ghost : Name} :
    PartialTyJoin left right join →
    ghost ∉ PartialTy.allVars left →
    ghost ∉ PartialTy.allVars right →
    ghost ∉ PartialTy.allVars join := by
  intro hjoin hleftFresh hrightFresh hmem
  have herasedUpper :
      PartialTy.eraseName ghost join ∈
        upperBounds ({left, right} : Set PartialTy) := by
    intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.to_eraseName_of_fresh
        (PartialTyUnion.left_strengthens hjoin) hleftFresh
    · subst hcandidate
      exact PartialTyStrengthens.to_eraseName_of_fresh
        (PartialTyUnion.right_strengthens hjoin) hrightFresh
  have hjoinLeErased :
      PartialTyStrengthens join (PartialTy.eraseName ghost join) :=
    hjoin.2 herasedUpper
  exact PartialTy.eraseName_no_allVars ghost join
    (PartialTyStrengthens.allVars_mono hjoinLeErased hmem)

theorem PartialTyJoin.ty_ty_vars_fresh {left right joinTy : Ty}
    {ghost : Name} :
    PartialTyJoin (.ty left) (.ty right) (.ty joinTy) →
    ghost ∉ Ty.vars left →
    ghost ∉ Ty.vars right →
    ghost ∉ Ty.vars joinTy := by
  intro hjoin hleft hright hv
  have hvPartial : ghost ∈ PartialTy.vars (.ty joinTy) := by
    simpa [PartialTy.vars] using hv
  rcases partialTyUnion_vars_subset hjoin hvPartial with hvLeft | hvRight
  · exact hleft (by simpa [PartialTy.vars] using hvLeft)
  · exact hright (by simpa [PartialTy.vars] using hvRight)

theorem LValTyping.typeNameFresh {env : Env} {ghost : Name} :
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      Env.TypeNameFresh env ghost →
      ghost ∉ PartialTy.allVars partialTy) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      Env.TypeNameFresh env ghost →
      ghost ∉ PartialTy.allVars partialTy) := by
  constructor
  · intro lv partialTy lifetime htyping hfresh
    exact LValTyping.rec
      (motive_1 := fun _lv partialTy _lifetime _ =>
        Env.TypeNameFresh env ghost → ghost ∉ PartialTy.allVars partialTy)
      (motive_2 := fun _targets partialTy _lifetime _ =>
        Env.TypeNameFresh env ghost → ghost ∉ PartialTy.allVars partialTy)
      (by
        intro x slot hslot hfresh
        exact hfresh x slot hslot)
      (by
        intro _lv _inner _lifetime _hinner ih hfresh
        simpa [PartialTy.allVars] using ih hfresh)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets hfresh
        exact ihTargets hfresh)
      (by
        intro _target _ty _lifetime _htarget ihTarget hfresh
        exact ihTarget hfresh)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime
          _restTy _unionTy _hhead hrest hunion _hintersection ihHead ihRest
          hfresh hvAll
        rcases LValTargetsTyping.output_full hrest with ⟨restFull, hrestFull⟩
        subst hrestFull
        rcases PartialTyUnion.ty_ty_full hunion with ⟨unionFull, hunionFull⟩
        subst hunionFull
        exact PartialTyJoin.allVars_fresh hunion (ihHead hfresh) (ihRest hfresh) hvAll)
      htyping hfresh
  · intro targets partialTy lifetime htyping hfresh
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv partialTy _lifetime _ =>
        Env.TypeNameFresh env ghost → ghost ∉ PartialTy.allVars partialTy)
      (motive_2 := fun _targets partialTy _lifetime _ =>
        Env.TypeNameFresh env ghost → ghost ∉ PartialTy.allVars partialTy)
      (by
        intro x slot hslot hfresh
        exact hfresh x slot hslot)
      (by
        intro _lv _inner _lifetime _hinner ih hfresh
        simpa [PartialTy.allVars] using ih hfresh)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets hfresh
        exact ihTargets hfresh)
      (by
        intro _target _ty _lifetime _htarget ihTarget hfresh
        exact ihTarget hfresh)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime
          _restTy _unionTy _hhead hrest hunion _hintersection ihHead ihRest
          hfresh hvAll
        rcases LValTargetsTyping.output_full hrest with ⟨restFull, hrestFull⟩
        subst hrestFull
        rcases PartialTyUnion.ty_ty_full hunion with ⟨unionFull, hunionFull⟩
        subst hunionFull
        exact PartialTyJoin.allVars_fresh hunion (ihHead hfresh) (ihRest hfresh) hvAll)
      htyping hfresh

theorem LValTyping.erase_ghost {env : Env} {ghost : Name} :
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      Env.TypeNameFresh (env.erase ghost) ghost →
      ¬ LVal.Mentions ghost lv →
      LValTyping (env.erase ghost) lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      Env.TypeNameFresh (env.erase ghost) ghost →
      (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
      LValTargetsTyping (env.erase ghost) targets partialTy lifetime) := by
  constructor
  · intro lv partialTy lifetime htyping hfresh hnotMention
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        ¬ LVal.Mentions ghost lv →
        LValTyping (env.erase ghost) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
        LValTargetsTyping (env.erase ghost) targets partialTy lifetime)
      (by
        intro x slot hslot _hfresh hnotMention
        have hne : x ≠ ghost :=
          LVal.base_ne_of_not_mentions (lv := .var x) hnotMention
        exact LValTyping.var (by simpa [Env.erase, hne] using hslot))
      (by
        intro _lv _inner _lifetime _hinner ih hfresh hnotMention
        exact LValTyping.box
          (ih hfresh (by simpa [LVal.Mentions] using hnotMention)))
      (by
        intro _lv mutable targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets ihBorrow ihTargets hfresh hnotMention
        have hborrowErased :=
          ihBorrow hfresh (by simpa [LVal.Mentions] using hnotMention)
        have hborrowFresh :
            ghost ∉ PartialTy.allVars (.ty (.borrow mutable targets)) :=
          (LValTyping.typeNameFresh.1 hborrowErased hfresh)
        have htargetsNot :
            ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target := by
          intro target hmem htargetMention
          have hbase : LVal.base target = ghost :=
            (LVal.mentions_iff_base (ghost := ghost) target).1 htargetMention
          exact hborrowFresh (by
            simp [PartialTy.allVars, Ty.allVars, List.mem_map]
            exact ⟨target, hmem, hbase⟩)
        exact LValTyping.borrow hborrowErased (ihTargets hfresh htargetsNot))
      (by
        intro _target _ty _lifetime _htarget ihTarget hfresh hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget hfresh (hnotTargets _ (by simp))))
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime
          _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
          hfresh hnotTargets
        exact LValTargetsTyping.cons
          (ihHead hfresh (hnotTargets _ (by simp)))
          (ihRest hfresh (by
            intro candidate hmem
            exact hnotTargets candidate (by simp [hmem])))
          hunion hintersection)
      htyping hfresh hnotMention
  · intro targets partialTy lifetime htyping hfresh hnotTargets
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        ¬ LVal.Mentions ghost lv →
        LValTyping (env.erase ghost) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
        LValTargetsTyping (env.erase ghost) targets partialTy lifetime)
      (by
        intro x slot hslot _hfresh hnotMention
        have hne : x ≠ ghost :=
          LVal.base_ne_of_not_mentions (lv := .var x) hnotMention
        exact LValTyping.var (by simpa [Env.erase, hne] using hslot))
      (by
        intro _lv _inner _lifetime _hinner ih hfresh hnotMention
        exact LValTyping.box
          (ih hfresh (by simpa [LVal.Mentions] using hnotMention)))
      (by
        intro _lv mutable targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets ihBorrow ihTargets hfresh hnotMention
        have hborrowErased :=
          ihBorrow hfresh (by simpa [LVal.Mentions] using hnotMention)
        have hborrowFresh :
            ghost ∉ PartialTy.allVars (.ty (.borrow mutable targets)) :=
          (LValTyping.typeNameFresh.1 hborrowErased hfresh)
        have htargetsNot :
            ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target := by
          intro target hmem htargetMention
          have hbase : LVal.base target = ghost :=
            (LVal.mentions_iff_base (ghost := ghost) target).1 htargetMention
          exact hborrowFresh (by
            simp [PartialTy.allVars, Ty.allVars, List.mem_map]
            exact ⟨target, hmem, hbase⟩)
        exact LValTyping.borrow hborrowErased (ihTargets hfresh htargetsNot))
      (by
        intro _target _ty _lifetime _htarget ihTarget hfresh hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget hfresh (hnotTargets _ (by simp))))
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime
          _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
          hfresh hnotTargets
        exact LValTargetsTyping.cons
          (ihHead hfresh (hnotTargets _ (by simp)))
          (ihRest hfresh (by
            intro candidate hmem
            exact hnotTargets candidate (by simp [hmem])))
          hunion hintersection)
      htyping hfresh hnotTargets

theorem LValTyping.erase_to_env {env : Env} {ghost : Name} :
    (∀ {lv partialTy lifetime},
      LValTyping (env.erase ghost) lv partialTy lifetime →
      LValTyping env lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping (env.erase ghost) targets partialTy lifetime →
      LValTargetsTyping env targets partialTy lifetime) := by
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        LValTyping env lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        LValTargetsTyping env targets partialTy lifetime)
      (by
        intro x slot hslot
        by_cases hx : x = ghost
        · subst hx
          simp [Env.erase] at hslot
        · exact LValTyping.var (by simpa [Env.erase, hx] using hslot))
      (by
        intro _lv _inner _lifetime _hinner ih
        exact LValTyping.box ih)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets ihBorrow ihTargets
        exact LValTyping.borrow ihBorrow ihTargets)
      (by
        intro _target _ty _lifetime _htarget ihTarget
        exact LValTargetsTyping.singleton ihTarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime
          _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
        exact LValTargetsTyping.cons ihHead ihRest hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        LValTyping env lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        LValTargetsTyping env targets partialTy lifetime)
      (by
        intro x slot hslot
        by_cases hx : x = ghost
        · subst hx
          simp [Env.erase] at hslot
        · exact LValTyping.var (by simpa [Env.erase, hx] using hslot))
      (by
        intro _lv _inner _lifetime _hinner ih
        exact LValTyping.box ih)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets ihBorrow ihTargets
        exact LValTyping.borrow ihBorrow ihTargets)
      (by
        intro _target _ty _lifetime _htarget ihTarget
        exact LValTargetsTyping.singleton ihTarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _lifetime
          _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
        exact LValTargetsTyping.cons ihHead ihRest hunion hintersection)
      htyping

theorem LValTyping.not_mentions_of_fresh {env : Env} {ghost : Name}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    env.fresh ghost →
    LValTyping env lv partialTy lifetime →
    ¬ LVal.Mentions ghost lv := by
  intro hfresh htyping
  have hbaseNe : LVal.base lv ≠ ghost := by
    intro hbase
    rcases LValTyping.base_slot_exists htyping with ⟨slot, hslot⟩
    unfold Env.fresh at hfresh
    rw [hbase] at hslot
    rw [hslot] at hfresh
    contradiction
  exact LVal.not_mentions_of_base_ne hbaseNe

theorem LValTargetsTyping.not_mentions_of_fresh {env : Env} {ghost : Name}
    {targets : List LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    env.fresh ghost →
    LValTargetsTyping env targets partialTy lifetime →
    ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target := by
  intro hfresh htargets
  exact LValTargetsTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      ¬ LVal.Mentions ghost lv)
    (motive_2 := fun targets partialTy lifetime _ =>
      ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target)
    (by
      intro x slot hslot
      have hx : x ≠ ghost := by
        intro hx
        subst hx
        unfold Env.fresh at hfresh
        rw [hslot] at hfresh
        contradiction
      exact LVal.not_mentions_of_base_ne (lv := .var x) hx)
    (by
      intro _lv _inner _lifetime _hinner ih
      intro hmention
      exact ih (by simpa [LVal.Mentions] using hmention))
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets ihBorrow _ihTargets
      intro hmention
      exact ihBorrow (by simpa [LVal.Mentions] using hmention))
    (by
      intro target _ty _lifetime _htarget ihTarget candidate hmem
      simp at hmem
      subst hmem
      exact ihTarget)
    (by
      intro target rest _headTy _headLifetime _restLifetime _lifetime
        _restTy _unionTy _hhead _hrest _hunion _hinter ihHead ihRest
        candidate hmem
      simp at hmem
      rcases hmem with hmem | hmem
      · subst hmem
        exact ihHead
      · exact ihRest candidate hmem)
    htargets

theorem EnvContains.erase_to_env {env : Env} {ghost x : Name} {ty : Ty} :
    (env.erase ghost) ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  rintro ⟨slot, hslot, hcontains⟩
  by_cases hx : x = ghost
  · subst hx
    simp [Env.erase] at hslot
  · exact ⟨slot, by simpa [Env.erase, hx] using hslot, hcontains⟩

theorem ReadProhibited.erase_to_env {env : Env} {ghost : Name} {lv : LVal} :
    ReadProhibited (env.erase ghost) lv →
    ReadProhibited env lv := by
  rintro ⟨x, targets, target, hcontains, hmem, hconflict⟩
  exact ⟨x, targets, target, EnvContains.erase_to_env hcontains, hmem,
    hconflict⟩

theorem WriteProhibited.erase_to_env {env : Env} {ghost : Name} {lv : LVal} :
    WriteProhibited (env.erase ghost) lv →
    WriteProhibited env lv := by
  intro h
  rcases h with hread | ⟨x, targets, target, hcontains, hmem, hconflict⟩
  · exact Or.inl (ReadProhibited.erase_to_env hread)
  · exact Or.inr ⟨x, targets, target, EnvContains.erase_to_env hcontains,
      hmem, hconflict⟩

theorem LValBaseOutlives.erase_ghost {env : Env} {ghost : Name}
    {lv : LVal} {lifetime : Lifetime} :
    ¬ LVal.Mentions ghost lv →
    LValBaseOutlives env lv lifetime →
    LValBaseOutlives (env.erase ghost) lv lifetime := by
  intro hnot hbase
  rcases hbase with ⟨slot, hslot, houtlives⟩
  have hne : LVal.base lv ≠ ghost :=
    LVal.base_ne_of_not_mentions hnot
  exact ⟨slot, by simpa [Env.erase, hne] using hslot, houtlives⟩

theorem Mutable.erase_ghost {env : Env} {ghost : Name} {lv : LVal} :
    Mutable env lv →
    Env.TypeNameFresh (env.erase ghost) ghost →
    ¬ LVal.Mentions ghost lv →
    Mutable (env.erase ghost) lv := by
  intro hmutable hfresh hnotMention
  induction hmutable with
  | var hslot =>
      rename_i x slot
      have hne : x ≠ ghost :=
        LVal.base_ne_of_not_mentions (lv := .var x) hnotMention
      exact Mutable.var (by simpa [Env.erase, hne] using hslot)
  | box hLv _hmutable ih =>
      exact Mutable.box
        (LValTyping.erase_ghost.1 hLv hfresh
          (by simpa [LVal.Mentions] using hnotMention))
        (ih (by simpa [LVal.Mentions] using hnotMention))
  | borrow hLv htargets ih =>
      rename_i source targets lifetime
      have hLvErased :=
        LValTyping.erase_ghost.1 hLv hfresh
          (by simpa [LVal.Mentions] using hnotMention)
      have hborrowFresh :
          ghost ∉ PartialTy.allVars (.ty (.borrow true targets)) :=
        LValTyping.typeNameFresh.1 hLvErased hfresh
      have htargetsNot :
          ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target := by
        intro target hmem htargetMention
        have hbase : LVal.base target = ghost :=
          (LVal.mentions_iff_base (ghost := ghost) target).1 htargetMention
        exact hborrowFresh (by
          simp [PartialTy.allVars, Ty.allVars, List.mem_map]
          exact ⟨target, hmem, hbase⟩)
      exact Mutable.borrow hLvErased (by
        intro target hmem
        exact ih target hmem (htargetsNot target hmem))

theorem EnvMove.erase_ghost {env moved : Env} {ghost : Name} {lv : LVal} :
    EnvMove env lv moved →
    ¬ LVal.Mentions ghost lv →
    EnvMove (env.erase ghost) lv (moved.erase ghost) := by
  intro hmove hnotMention
  rcases hmove with ⟨slot, struck, hslot, hstrike, rfl⟩
  have hbaseNe : LVal.base lv ≠ ghost :=
    LVal.base_ne_of_not_mentions hnotMention
  refine ⟨slot, struck, ?_, hstrike, ?_⟩
  · simpa [Env.erase, hbaseNe] using hslot
  · exact Env.erase_update_ne env (x := ghost) (y := LVal.base lv)
      { slot with ty := struck } hbaseNe

theorem Strike.allVars_fresh {path : Path} {source struck : PartialTy}
    {ghost : Name} :
    Strike path source struck →
    ghost ∉ PartialTy.allVars source →
    ghost ∉ PartialTy.allVars struck := by
  intro hstrike
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike ⊢
      subst hstrike
      intro hfresh
      simpa [PartialTy.allVars] using hfresh
  | cons _ path ih =>
      cases source with
      | ty sourceTy =>
          cases struck <;> simp [Strike] at hstrike
      | undef sourceTy =>
          cases struck <;> simp [Strike] at hstrike
      | box inner =>
          cases struck with
          | ty struckTy => simp [Strike] at hstrike
          | undef struckTy => simp [Strike] at hstrike
          | box struckInner =>
              simp [Strike] at hstrike ⊢
              intro hfresh
              exact ih (source := inner) (struck := struckInner) hstrike hfresh

theorem EnvMove.typeNameFresh_erase {env moved : Env} {ghost : Name}
    {lv : LVal} :
    EnvMove env lv moved →
    Env.TypeNameFresh (env.erase ghost) ghost →
    ¬ LVal.Mentions ghost lv →
    Env.TypeNameFresh (moved.erase ghost) ghost := by
  intro hmove hfresh hnot x slot hslot
  rcases hmove with ⟨oldSlot, struck, hbaseSlot, hstrike, rfl⟩
  have hbaseNe : LVal.base lv ≠ ghost :=
    LVal.base_ne_of_not_mentions hnot
  by_cases hx : x = LVal.base lv
  · subst hx
    simp [Env.erase, Env.update, hbaseNe] at hslot
    subst hslot
    have holdFresh :
        ghost ∉ PartialTy.allVars oldSlot.ty := by
      exact hfresh (LVal.base lv) oldSlot
        (by simpa [Env.erase, hbaseNe] using hbaseSlot)
    exact Strike.allVars_fresh hstrike holdFresh
  · exact hfresh x slot (by
      by_cases hxGhost : x = ghost
      · subst hxGhost
        simp [Env.erase] at hslot
      · simpa [Env.erase, Env.update, hx, hxGhost] using hslot)

theorem WellFormedTy.erase_ghost {env : Env} {ghost : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedTy env ty lifetime →
    Env.TypeNameFresh (env.erase ghost) ghost →
    ghost ∉ Ty.allVars ty →
    WellFormedTy (env.erase ghost) ty lifetime := by
  intro hwell hfresh htyFresh
  induction hwell with
  | unit => exact WellFormedTy.unit
  | int => exact WellFormedTy.int
  | bool => exact WellFormedTy.bool
  | box _hinner ih =>
      exact WellFormedTy.box (ih (by simpa [Ty.allVars] using htyFresh))
  | borrow htargets =>
      rename_i mutable targets lifetime
      refine WellFormedTy.borrow ?_
      cases htargets with
      | intro hmembers =>
          refine BorrowTargetsWellFormed.intro ?_
          intro target hmem
          rcases hmembers target hmem with
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbase⟩
          have htargetNot : ¬ LVal.Mentions ghost target := by
            intro hmention
            have hbaseEq : LVal.base target = ghost :=
              (LVal.mentions_iff_base (ghost := ghost) target).1 hmention
            exact htyFresh (by
              simp [Ty.allVars, List.mem_map]
              exact ⟨target, hmem, hbaseEq⟩)
          exact ⟨targetTy, targetLifetime,
            LValTyping.erase_ghost.1 htargetTyping hfresh htargetNot,
            houtlives,
            LValBaseOutlives.erase_ghost htargetNot hbase⟩

private theorem not_mentions_of_mem_borrow_allVars {ghost : Name}
    {mutable : Bool} {targets : List LVal} :
    ghost ∉ PartialTy.allVars (.ty (.borrow mutable targets)) →
    ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target := by
  intro hfresh target hmem hmention
  have hbase : LVal.base target = ghost :=
    (LVal.mentions_iff_base (ghost := ghost) target).1 hmention
  exact hfresh (by
    simp [PartialTy.allVars, Ty.allVars, List.mem_map]
    exact ⟨target, hmem, hbase⟩)

private theorem not_mentions_of_partialTy_contains_allVars {ghost : Name}
    {partialTy : PartialTy} {mutable : Bool} {targets : List LVal} :
    ghost ∉ PartialTy.allVars partialTy →
    PartialTyContains partialTy (.borrow mutable targets) →
    ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target := by
  intro hfresh hcontains target hmem hmention
  have hbase : LVal.base target = ghost :=
    (LVal.mentions_iff_base (ghost := ghost) target).1 hmention
  have hv : ghost ∈ PartialTy.vars partialTy :=
    mem_partialTy_vars_iff.mpr
      ⟨mutable, targets, target, hcontains, hmem, hbase⟩
  exact hfresh (PartialTy.vars_subset_allVars (partialTy := partialTy) hv)

private theorem fresh_target_ty_of_target {env : Env} {ghost : Name}
    {target : LVal} {targetTy : Ty} {targetLifetime : Lifetime} :
    Env.TypeNameFresh (env.erase ghost) ghost →
    LValTyping (env.erase ghost) target (.ty targetTy) targetLifetime →
    ghost ∉ PartialTy.allVars (.ty targetTy) := by
  intro hfresh htyping
  exact LValTyping.typeNameFresh.1 htyping hfresh

theorem ShapeCompatible.erase_ghost_pack {env : Env} {ghost : Name} :
    (∀ {left right},
      ShapeCompatible env left right →
      Env.TypeNameFresh (env.erase ghost) ghost →
      ghost ∉ PartialTy.allVars left →
      ghost ∉ PartialTy.allVars right →
      ShapeCompatible (env.erase ghost) left right) ∧
    (∀ {left right},
      ShapeCompatible env left right →
      Env.TypeNameFresh (env.erase ghost) ghost →
      ghost ∉ PartialTy.allVars left →
      ShapeCompatible (env.erase ghost) left left) ∧
    (∀ {left right},
      ShapeCompatible env left right →
      Env.TypeNameFresh (env.erase ghost) ghost →
      ghost ∉ PartialTy.allVars right →
      ShapeCompatible (env.erase ghost) right right) := by
  suffices h :
      ∀ {left right} (hshape : ShapeCompatible env left right),
        (Env.TypeNameFresh (env.erase ghost) ghost →
          ghost ∉ PartialTy.allVars left →
          ghost ∉ PartialTy.allVars right →
          ShapeCompatible (env.erase ghost) left right) ∧
        (Env.TypeNameFresh (env.erase ghost) ghost →
          ghost ∉ PartialTy.allVars left →
          ShapeCompatible (env.erase ghost) left left) ∧
        (Env.TypeNameFresh (env.erase ghost) ghost →
          ghost ∉ PartialTy.allVars right →
          ShapeCompatible (env.erase ghost) right right) by
    exact ⟨
      (fun hshape hfresh hleftFresh hrightFresh =>
        (h hshape).1 hfresh hleftFresh hrightFresh),
      (fun hshape hfresh hleftFresh =>
        (h hshape).2.1 hfresh hleftFresh),
      (fun hshape hfresh hrightFresh =>
        (h hshape).2.2 hfresh hrightFresh)⟩
  intro left right hshape
  induction hshape with
  | unit =>
      exact ⟨
        (by intro _ _ _; exact ShapeCompatible.unit),
        (by intro _ _; exact ShapeCompatible.unit),
        (by intro _ _; exact ShapeCompatible.unit)⟩
  | int =>
      exact ⟨
        (by intro _ _ _; exact ShapeCompatible.int),
        (by intro _ _; exact ShapeCompatible.int),
        (by intro _ _; exact ShapeCompatible.int)⟩
  | bool =>
      exact ⟨
        (by intro _ _ _; exact ShapeCompatible.bool),
        (by intro _ _; exact ShapeCompatible.bool),
        (by intro _ _; exact ShapeCompatible.bool)⟩
  | tyBox _hinner ih =>
      exact ⟨
        (by
          intro hfresh hleftFresh hrightFresh
          exact ShapeCompatible.tyBox
            (ih.1 hfresh
              (by simpa [PartialTy.allVars, Ty.allVars] using hleftFresh)
              (by simpa [PartialTy.allVars, Ty.allVars] using hrightFresh))),
        (by
          intro hfresh hleftFresh
          exact ShapeCompatible.tyBox
            (ih.2.1 hfresh
              (by simpa [PartialTy.allVars, Ty.allVars] using hleftFresh))),
        (by
          intro hfresh hrightFresh
          exact ShapeCompatible.tyBox
            (ih.2.2 hfresh
              (by simpa [PartialTy.allVars, Ty.allVars] using hrightFresh)))⟩
  | box _hinner ih =>
      exact ⟨
        (by
          intro hfresh hleftFresh hrightFresh
          exact ShapeCompatible.box
            (ih.1 hfresh
              (by simpa [PartialTy.allVars] using hleftFresh)
              (by simpa [PartialTy.allVars] using hrightFresh))),
        (by
          intro hfresh hleftFresh
          exact ShapeCompatible.box
            (ih.2.1 hfresh
              (by simpa [PartialTy.allVars] using hleftFresh))),
        (by
          intro hfresh hrightFresh
          exact ShapeCompatible.box
            (ih.2.2 hfresh
              (by simpa [PartialTy.allVars] using hrightFresh)))⟩
  | @borrow mutable leftTargets rightTargets leftTy rightTy hleft hright _hinner ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hfresh hleftFresh hrightFresh
        have hleftNot :=
          not_mentions_of_mem_borrow_allVars (ghost := ghost) hleftFresh
        have hrightNot :=
          not_mentions_of_mem_borrow_allVars (ghost := ghost) hrightFresh
        have hleftErased :
            ∀ leftTarget, leftTarget ∈ leftTargets →
              ∃ leftLifetime,
                LValTyping (env.erase ghost) leftTarget (.ty leftTy) leftLifetime := by
          intro target hmem
          rcases hleft target hmem with ⟨life, htyping⟩
          exact ⟨life, LValTyping.erase_ghost.1 htyping hfresh
            (hleftNot target hmem)⟩
        have hrightErased :
            ∀ rightTarget, rightTarget ∈ rightTargets →
              ∃ rightLifetime,
                LValTyping (env.erase ghost) rightTarget (.ty rightTy) rightLifetime := by
          intro target hmem
          rcases hright target hmem with ⟨life, htyping⟩
          exact ⟨life, LValTyping.erase_ghost.1 htyping hfresh
            (hrightNot target hmem)⟩
        cases leftTargets with
        | nil =>
            cases rightTargets with
            | nil =>
                exact ShapeCompatible.borrow
                  (leftTy := .unit) (rightTy := .unit)
                  (by intro target hmem; cases hmem)
                  (by intro target hmem; cases hmem)
                  ShapeCompatible.unit
            | cons rightHead rightTail =>
                rcases hrightErased rightHead (by simp) with
                  ⟨_rightLife, hrightHead⟩
                have hrightTyFresh :
                    ghost ∉ PartialTy.allVars (.ty rightTy) :=
                  fresh_target_ty_of_target hfresh hrightHead
                exact ShapeCompatible.borrow
                  (leftTy := rightTy) (rightTy := rightTy)
                  (by intro target hmem; cases hmem)
                  hrightErased
                  (ih.2.2 hfresh hrightTyFresh)
        | cons leftHead leftTail =>
            rcases hleftErased leftHead (by simp) with
              ⟨_leftLife, hleftHead⟩
            have hleftTyFresh :
                ghost ∉ PartialTy.allVars (.ty leftTy) :=
              fresh_target_ty_of_target hfresh hleftHead
            cases rightTargets with
            | nil =>
                exact ShapeCompatible.borrow
                  (leftTy := leftTy) (rightTy := leftTy)
                  hleftErased
                  (by intro target hmem; cases hmem)
                  (ih.2.1 hfresh hleftTyFresh)
            | cons rightHead rightTail =>
                rcases hrightErased rightHead (by simp) with
                  ⟨_rightLife, hrightHead⟩
                have hrightTyFresh :
                    ghost ∉ PartialTy.allVars (.ty rightTy) :=
                  fresh_target_ty_of_target hfresh hrightHead
                exact ShapeCompatible.borrow hleftErased hrightErased
                  (ih.1 hfresh hleftTyFresh hrightTyFresh)
      · intro hfresh hleftFresh
        have hleftNot :=
          not_mentions_of_mem_borrow_allVars (ghost := ghost) hleftFresh
        have hleftErased :
            ∀ leftTarget, leftTarget ∈ leftTargets →
              ∃ leftLifetime,
                LValTyping (env.erase ghost) leftTarget (.ty leftTy) leftLifetime := by
          intro target hmem
          rcases hleft target hmem with ⟨life, htyping⟩
          exact ⟨life, LValTyping.erase_ghost.1 htyping hfresh
            (hleftNot target hmem)⟩
        cases leftTargets with
        | nil =>
            exact ShapeCompatible.borrow
              (leftTy := .unit) (rightTy := .unit)
              (by intro target hmem; cases hmem)
              (by intro target hmem; cases hmem)
              ShapeCompatible.unit
        | cons leftHead leftTail =>
            rcases hleftErased leftHead (by simp) with
              ⟨_leftLife, hleftHead⟩
            have hleftTyFresh :
                ghost ∉ PartialTy.allVars (.ty leftTy) :=
              fresh_target_ty_of_target hfresh hleftHead
            exact ShapeCompatible.borrow hleftErased hleftErased
              (ih.2.1 hfresh hleftTyFresh)
      · intro hfresh hrightFresh
        have hrightNot :=
          not_mentions_of_mem_borrow_allVars (ghost := ghost) hrightFresh
        have hrightErased :
            ∀ rightTarget, rightTarget ∈ rightTargets →
              ∃ rightLifetime,
                LValTyping (env.erase ghost) rightTarget (.ty rightTy) rightLifetime := by
          intro target hmem
          rcases hright target hmem with ⟨life, htyping⟩
          exact ⟨life, LValTyping.erase_ghost.1 htyping hfresh
            (hrightNot target hmem)⟩
        cases rightTargets with
        | nil =>
            exact ShapeCompatible.borrow
              (leftTy := .unit) (rightTy := .unit)
              (by intro target hmem; cases hmem)
              (by intro target hmem; cases hmem)
              ShapeCompatible.unit
        | cons rightHead rightTail =>
            rcases hrightErased rightHead (by simp) with
              ⟨_rightLife, hrightHead⟩
            have hrightTyFresh :
                ghost ∉ PartialTy.allVars (.ty rightTy) :=
              fresh_target_ty_of_target hfresh hrightHead
            exact ShapeCompatible.borrow hrightErased hrightErased
              (ih.2.2 hfresh hrightTyFresh)
  | @undefLeft leftTy rightPt _hinner ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hfresh hleftFresh hrightFresh
        exact ShapeCompatible.undefLeft
          (ih.1 hfresh
            (by simpa [PartialTy.allVars] using hleftFresh)
            hrightFresh)
      · intro hfresh hleftFresh
        have hleftTyFresh :
            ghost ∉ PartialTy.allVars (.ty leftTy) := by
          simpa [PartialTy.allVars] using hleftFresh
        exact ShapeCompatible.undefLeft
          (ShapeCompatible.undefRight
            (ih.2.1 hfresh hleftTyFresh))
      · intro hfresh hrightFresh
        exact ih.2.2 hfresh hrightFresh
  | @undefRight leftPt rightTy _hinner ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hfresh hleftFresh hrightFresh
        exact ShapeCompatible.undefRight
          (ih.1 hfresh hleftFresh
            (by simpa [PartialTy.allVars] using hrightFresh))
      · intro hfresh hleftFresh
        exact ih.2.1 hfresh hleftFresh
      · intro hfresh hrightFresh
        have hrightTyFresh :
            ghost ∉ PartialTy.allVars (.ty rightTy) := by
          simpa [PartialTy.allVars] using hrightFresh
        exact ShapeCompatible.undefRight
          (ShapeCompatible.undefLeft
            (ih.2.2 hfresh hrightTyFresh))

theorem ShapeCompatible.erase_ghost {env : Env} {ghost : Name}
    {left right : PartialTy} :
    ShapeCompatible env left right →
    Env.TypeNameFresh (env.erase ghost) ghost →
    ghost ∉ PartialTy.allVars left →
    ghost ∉ PartialTy.allVars right →
    ShapeCompatible (env.erase ghost) left right :=
  ShapeCompatible.erase_ghost_pack.1

theorem PartialTyJoin.allVars_fresh_of_shapeCompatible {env : Env}
    {old joined : PartialTy} {ty : Ty} {ghost : Name} :
    ShapeCompatible env old (.ty ty) →
    PartialTyJoin old (.ty ty) joined →
    ghost ∉ PartialTy.allVars old →
    ghost ∉ Ty.allVars ty →
    ghost ∉ PartialTy.allVars joined := by
  intro _hshape hjoin hold hty
  exact PartialTyJoin.allVars_fresh hjoin hold
    (by simpa [PartialTy.allVars] using hty)

theorem BorrowTargetsWellFormedInSlot.erase_ghost {env : Env} {ghost : Name}
    {slotLifetime : Lifetime} {targets : List LVal} :
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    Env.TypeNameFresh (env.erase ghost) ghost →
    (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
    BorrowTargetsWellFormedInSlot (env.erase ghost) slotLifetime targets := by
  intro hwell hfresh hnot target hmem
  rcases hwell target hmem with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  exact ⟨targetTy, targetLifetime,
    LValTyping.erase_ghost.1 htyping hfresh (hnot target hmem),
    houtlives,
    LValBaseOutlives.erase_ghost (hnot target hmem) hbase⟩

theorem ContainedBorrowsWellFormed.erase_ghost {env : Env} {ghost : Name} :
    ContainedBorrowsWellFormed env →
    Env.TypeNameFresh (env.erase ghost) ghost →
    ContainedBorrowsWellFormed (env.erase ghost) := by
  intro hcontained hfresh x slot mutable targets hslot hcontains
  rcases hcontains with ⟨containsSlot, hcontainsSlot, hcontainsTy⟩
  have hslotEq : slot = containsSlot := by
    rw [hslot] at hcontainsSlot
    exact Option.some.inj hcontainsSlot
  subst containsSlot
  have hslotOrig : env.slotAt x = some slot := by
    by_cases hx : x = ghost
    · subst hx
      simp [Env.erase] at hslot
    · simpa [Env.erase, hx] using hslot
  have hslotFresh : ghost ∉ PartialTy.allVars slot.ty :=
    hfresh x slot hslot
  have htargetsNot :
      ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target :=
    not_mentions_of_partialTy_contains_allVars hslotFresh hcontainsTy
  exact BorrowTargetsWellFormedInSlot.erase_ghost
    (hcontained x slot mutable targets hslotOrig
      ⟨slot, hslotOrig, hcontainsTy⟩)
    hfresh htargetsNot

theorem EnvWriteRhsTargetsWellFormed.erase_ghost {result : Env} {rhsTy : Ty}
    {ghost : Name} :
    EnvWriteRhsTargetsWellFormed result rhsTy →
    Env.TypeNameFresh (result.erase ghost) ghost →
    EnvWriteRhsTargetsWellFormed (result.erase ghost) rhsTy := by
  intro hrhs hfresh x slot mutable targets target hslot hcontains htarget hrhsOrigin
  have hslotOrig : result.slotAt x = some slot := by
    by_cases hx : x = ghost
    · subst hx; simp [Env.erase] at hslot
    · simpa [Env.erase, hx] using hslot
  have hslotFresh : ghost ∉ PartialTy.allVars slot.ty := hfresh x slot hslot
  have hnotTarget : ¬ LVal.Mentions ghost target :=
    not_mentions_of_partialTy_contains_allVars hslotFresh hcontains target htarget
  rcases hrhs x slot mutable targets target hslotOrig hcontains htarget hrhsOrigin with
    ⟨tTy, tLf, htyp, hle, hbase⟩
  exact ⟨tTy, tLf,
    LValTyping.erase_ghost.1 htyp hfresh hnotTarget,
    hle,
    LValBaseOutlives.erase_ghost hnotTarget hbase⟩

theorem Coherent.erase_ghost {env : Env} {ghost : Name} :
    Coherent env →
    Env.TypeNameFresh (env.erase ghost) ghost →
    Coherent (env.erase ghost) := by
  intro hcoherent hfresh lv mutable targets borrowLifetime htyping
  have htypingEnv : LValTyping env lv (.ty (.borrow mutable targets)) borrowLifetime :=
    LValTyping.erase_to_env.1 htyping
  rcases hcoherent lv mutable targets borrowLifetime htypingEnv with
    ⟨targetTy, targetLifetime, htargets⟩
  have hborrowFresh :
      ghost ∉ PartialTy.allVars (.ty (.borrow mutable targets)) :=
    LValTyping.typeNameFresh.1 htyping hfresh
  have htargetsNot :
      ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target :=
    not_mentions_of_mem_borrow_allVars hborrowFresh
  exact ⟨targetTy, targetLifetime, LValTyping.erase_ghost.2 htargets hfresh htargetsNot⟩

theorem LinearizedBy.erase_ghost {φ : Name → Nat} {env : Env}
    {ghost : Name} :
    LinearizedBy φ env →
    LinearizedBy φ (env.erase ghost) := by
  intro hlinear x slot hslot v hv
  by_cases hx : x = ghost
  · subst hx
    simp [Env.erase] at hslot
  · exact hlinear x slot (by simpa [Env.erase, hx] using hslot) v hv

theorem Linearizable.erase_ghost {env : Env} {ghost : Name} :
    Linearizable env →
    Linearizable (env.erase ghost) := by
  rintro ⟨φ, hlinear⟩
  exact ⟨φ, LinearizedBy.erase_ghost hlinear⟩

theorem TyBorrowSafeAgainstEnv.erase_ghost {env : Env} {ghost : Name}
    {ty : Ty} :
    TyBorrowSafeAgainstEnv env ty →
    TyBorrowSafeAgainstEnv (env.erase ghost) ty := by
  rintro ⟨hleft, hright⟩
  constructor
  · intro targetsMutable mutable targetsOther x
      targetMutable targetOther hcontains henv htargetMutable htargetOther
      hconflict
    exact hleft targetsMutable mutable targetsOther x
      targetMutable targetOther hcontains (EnvContains.erase_to_env henv)
      htargetMutable htargetOther hconflict
  · intro x targetsMutable mutable targetsOther
      targetMutable targetOther henv hcontains htargetMutable htargetOther
      hconflict
    exact hright x targetsMutable mutable targetsOther
      targetMutable targetOther (EnvContains.erase_to_env henv) hcontains
      htargetMutable htargetOther hconflict

theorem EnvStrengthens.erase_ghost {left right : Env} {ghost : Name} :
    EnvStrengthens left right →
    EnvStrengthens (left.erase ghost) (right.erase ghost) := by
  intro hstrength x
  by_cases hx : x = ghost
  · subst hx
    simp [Env.erase]
  · simpa [Env.erase, hx] using hstrength x

theorem EnvJoin.erase_ghost {left right join : Env} {ghost : Name} :
    EnvJoin left right join →
    EnvJoin (left.erase ghost) (right.erase ghost) (join.erase ghost) := by
  intro hjoin
  apply EnvJoin.of_isLUB
  have hjoinLUB := EnvJoin.isLUB hjoin
  refine ⟨?upper, ?least⟩
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with rfl | rfl
    ·
      exact EnvStrengthens.erase_ghost (by simpa using hjoinLUB.1 (by simp))
    ·
      exact EnvStrengthens.erase_ghost (by simpa using hjoinLUB.1 (by simp))
  · intro ub hub
    let ubPlus : Env :=
      { slotAt := fun x => if x = ghost then join.slotAt ghost else ub.slotAt x }
    have hubPlus : ubPlus ∈ upperBounds ({left, right} : Set Env) := by
      intro candidate hcandidate
      simp at hcandidate
      rcases hcandidate with rfl | rfl
      ·
        intro x
        by_cases hx : x = ghost
        · simpa [ubPlus, hx] using EnvJoin.left_le hjoin x
        · have hleftErase := hub (Set.mem_insert _ _)
          simpa [ubPlus, Env.erase, hx] using hleftErase x
      ·
        intro x
        by_cases hx : x = ghost
        · simpa [ubPlus, hx] using EnvJoin.right_le hjoin x
        · have hrightErase := hub (Set.mem_insert_of_mem _ rfl)
          simpa [ubPlus, Env.erase, hx] using hrightErase x
    have hleastJoin : EnvStrengthens join ubPlus :=
      by simpa using hjoinLUB.2 hubPlus
    intro x
    by_cases hx : x = ghost
    · have hleftErase : EnvStrengthens (left.erase ghost) ub :=
        by simpa using hub (Set.mem_insert _ _)
      have hubGhost : ub.slotAt x = none := by
        have hcoord := hleftErase x
        cases h : ub.slotAt x with
        | none => rfl
        | some slot =>
            have hghostSome : ub.slotAt ghost = some slot := by
              rw [← hx]
              exact h
            have hcoordFalse := hcoord
            rw [hx] at hcoordFalse
            simp [Env.erase, hghostSome] at hcoordFalse
      have hghostNone : ub.slotAt ghost = none := by
        rw [← hx]
        exact hubGhost
      rw [hx]
      simp [Env.erase, hghostNone]
    · simpa [Env.erase, hx, ubPlus] using hleastJoin x

theorem EnvJoin.typeNameFresh_erase {left right join : Env} {ghost : Name} :
    EnvJoin left right join →
    Env.TypeNameFresh (left.erase ghost) ghost →
    Env.TypeNameFresh (right.erase ghost) ghost →
    Env.TypeNameFresh (join.erase ghost) ghost := by
  intro hjoin hleftFresh hrightFresh x joinSlot hjoinSlot
  by_cases hx : x = ghost
  · subst hx
    simp [Env.erase] at hjoinSlot
  · have hjoinOrig : join.slotAt x = some joinSlot := by
      simpa [Env.erase, hx] using hjoinSlot
    rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinOrig with
      ⟨leftSlot, hleftSlot, _hleftLife⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinOrig with
      ⟨rightSlot, hrightSlot, _hrightLife⟩
    rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinOrig with
      ⟨_lifetime, _hlifetime, hslotJoin⟩
    have hleftSlotFresh : ghost ∉ PartialTy.allVars leftSlot.ty :=
      hleftFresh x leftSlot (by simpa [Env.erase, hx] using hleftSlot)
    have hrightSlotFresh : ghost ∉ PartialTy.allVars rightSlot.ty :=
      hrightFresh x rightSlot (by simpa [Env.erase, hx] using hrightSlot)
    exact PartialTyJoin.allVars_fresh hslotJoin hleftSlotFresh
      hrightSlotFresh

theorem EnvJoinSameShape.erase_ghost {branch join : Env} {ghost : Name} :
    EnvJoinSameShape branch join →
    EnvJoinSameShape (branch.erase ghost) (join.erase ghost) := by
  intro hsame x branchSlot joinSlot hbranch hjoin
  by_cases hx : x = ghost
  · subst hx
    simp [Env.erase] at hbranch
  · exact hsame x branchSlot joinSlot
      (by simpa [Env.erase, hx] using hbranch)
      (by simpa [Env.erase, hx] using hjoin)

theorem FreshUpdateCoherenceObligations.erase_ghost {env : Env}
    {x ghost : Name} {ty : Ty} {lifetime : Lifetime} :
    FreshUpdateCoherenceObligations env x ty lifetime →
    Env.TypeNameFresh (env.erase ghost) ghost →
    x ≠ ghost →
    ghost ∉ Ty.allVars ty →
    FreshUpdateCoherenceObligations (env.erase ghost) x ty lifetime := by
  intro hoblig hfresh hxGhost htyFresh
  constructor
  · intro lv mutable targets borrowLifetime hbaseNe htyping
    have hupdateErase :
        ((env.erase ghost).update x { ty := .ty ty, lifetime := lifetime }) =
          (env.update x { ty := .ty ty, lifetime := lifetime }).erase ghost := by
      exact (Env.erase_update_ne env (x := ghost) (y := x)
        { ty := .ty ty, lifetime := lifetime } hxGhost).symm
    have htypingErased :
        LValTyping
          ((env.update x { ty := .ty ty, lifetime := lifetime }).erase ghost)
          lv (.ty (.borrow mutable targets)) borrowLifetime := by
      simpa [hupdateErase] using htyping
    have htypingOrig :
      LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
        lv (.ty (.borrow mutable targets)) borrowLifetime :=
      LValTyping.erase_to_env.1 htypingErased
    rcases hoblig.old_root_transport hbaseNe htypingOrig with
      ⟨oldBorrowLifetime, holdTyping⟩
    have hupdateFresh :
        ((env.erase ghost).update x { ty := .ty ty, lifetime := lifetime }).fresh ghost := by
      unfold Env.fresh
      simp [Env.update, hxGhost.symm]
    have hnot : ¬ LVal.Mentions ghost lv := by
      exact LValTyping.not_mentions_of_fresh
        hupdateFresh htyping
    exact ⟨oldBorrowLifetime,
      LValTyping.erase_ghost.1 holdTyping hfresh hnot⟩
  · intro lv mutable targets borrowLifetime hbaseEq htyping
    have hupdateErase :
        ((env.erase ghost).update x { ty := .ty ty, lifetime := lifetime }) =
          (env.update x { ty := .ty ty, lifetime := lifetime }).erase ghost := by
      exact (Env.erase_update_ne env (x := ghost) (y := x)
        { ty := .ty ty, lifetime := lifetime } hxGhost).symm
    have htypingErased :
        LValTyping
          ((env.update x { ty := .ty ty, lifetime := lifetime }).erase ghost)
          lv (.ty (.borrow mutable targets)) borrowLifetime := by
      simpa [hupdateErase] using htyping
    have htypingOrig :
      LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
        lv (.ty (.borrow mutable targets)) borrowLifetime :=
      LValTyping.erase_to_env.1 htypingErased
    rcases hoblig.fresh_root_coherent hbaseEq htypingOrig with
      ⟨targetTy, targetLifetime, htargets⟩
    have hborrowFresh :
        ghost ∉ PartialTy.allVars (.ty (.borrow mutable targets)) :=
      LValTyping.typeNameFresh.1 htyping (by
        exact Env.typeNameFresh_update hfresh
          (by simpa [PartialTy.allVars] using htyFresh))
    have htargetsNot :
        ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target :=
      not_mentions_of_mem_borrow_allVars hborrowFresh
    refine ⟨targetTy, targetLifetime, ?_⟩
    have htargetsErased :=
      LValTyping.erase_ghost.2 htargets
        (by
          rw [← hupdateErase]
          exact Env.typeNameFresh_update hfresh
            (by simpa [PartialTy.allVars] using htyFresh))
        htargetsNot
    simpa [hupdateErase] using htargetsErased

theorem EnvWriteRhsBorrowTargetsBelow.erase_ghost {φ : Name → Nat}
    {result : Env} {rhsTy : Ty} {ghost : Name} :
    EnvWriteRhsBorrowTargetsBelow φ result rhsTy →
    EnvWriteRhsBorrowTargetsBelow φ (result.erase ghost) rhsTy := by
  rintro ⟨hrank, hconflicts⟩
  constructor
  · intro x slot mutable targets target hslot hcontains htarget hrhs
    have hslotOrig : result.slotAt x = some slot := by
      by_cases hx : x = ghost
      · subst hx
        simp [Env.erase] at hslot
      · simpa [Env.erase, hx] using hslot
    exact hrank x slot mutable targets target hslotOrig hcontains htarget hrhs
  · intro x y mutable targetsMutable targetsOther
      targetMutable targetOther hx hy htargetMutable htargetOther hconflict
      hrhsMutable hrhsOther
    exact hconflicts x y mutable targetsMutable targetsOther
      targetMutable targetOther (EnvContains.erase_to_env hx)
      (EnvContains.erase_to_env hy) htargetMutable htargetOther hconflict
      hrhsMutable hrhsOther

private theorem prependPath_not_mentions {path : List Unit} {target : LVal}
    {ghost : Name} :
    ¬ LVal.Mentions ghost target →
    ¬ LVal.Mentions ghost (prependPath path target) := by
  intro hnot hmention
  have hbase : LVal.base target = ghost := by
    have hprepBase : LVal.base (prependPath path target) = ghost :=
      (LVal.mentions_iff_base (ghost := ghost) _).1 hmention
    simpa [base_prependPath] using hprepBase
  exact hnot ((LVal.mentions_iff_base (ghost := ghost) target).2 hbase)

mutual
  theorem UpdateAtPath.erase_ghost {rank : Nat} {env₁ env₂ : Env}
      {path : List Unit} {oldTy updatedTy : PartialTy} {ty : Ty}
      {ghost : Name} :
      UpdateAtPath rank env₁ path oldTy ty env₂ updatedTy →
      Env.TypeNameFresh (env₁.erase ghost) ghost →
      ghost ∉ PartialTy.allVars oldTy →
      ghost ∉ Ty.allVars ty →
      UpdateAtPath rank (env₁.erase ghost) path oldTy ty
        (env₂.erase ghost) updatedTy := by
    intro hupdate hfresh holdFresh htyFresh
    exact UpdateAtPath.rec
      (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
        Env.TypeNameFresh (env₁.erase ghost) ghost →
        ghost ∉ PartialTy.allVars oldTy →
        ghost ∉ Ty.allVars ty →
        UpdateAtPath rank (env₁.erase ghost) path oldTy ty
          (env₂.erase ghost) updatedTy)
      (motive_2 := fun rank env path targets ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
        ghost ∉ Ty.allVars ty →
        WriteBorrowTargets rank (env.erase ghost) path targets ty
          (result.erase ghost))
      (motive_3 := fun rank env lv ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        ¬ LVal.Mentions ghost lv →
        ghost ∉ Ty.allVars ty →
        EnvWrite rank (env.erase ghost) lv ty (result.erase ghost))
      (by
        intro env old ty hfresh holdFresh htyFresh
        exact UpdateAtPath.strong)
      (by
        intro env rank old joined ty hshape hjoin hfresh holdFresh htyFresh
        exact UpdateAtPath.weak
          (ShapeCompatible.erase_ghost hshape hfresh holdFresh
            (by simpa [PartialTy.allVars] using htyFresh))
          hjoin)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hinner ih
          hfresh holdFresh htyFresh
        exact UpdateAtPath.box
          (ih hfresh (by simpa [PartialTy.allVars] using holdFresh)
            htyFresh))
      (by
        intro env₁ env₂ rank path targets ty _htargets ih hfresh holdFresh htyFresh
        have htargetsNot :
            ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target :=
          not_mentions_of_mem_borrow_allVars holdFresh
        exact UpdateAtPath.mutBorrow (ih hfresh htargetsNot htyFresh))
      (by
        intro rank env path ty hfresh hnot htyFresh
        exact WriteBorrowTargets.nil)
      (by
        intro rank env updated path target ty hwrite hleaf ihWrite
          hfresh hnot htyFresh
        have htargetNot : ¬ LVal.Mentions ghost (prependPath path target) :=
          prependPath_not_mentions (hnot target (by simp))
        rcases hleaf with ⟨leafTy, leafLifetime, hleafTyping⟩
        exact WriteBorrowTargets.singleton
          (ihWrite hfresh htargetNot htyFresh)
          ⟨leafTy, leafLifetime,
            LValTyping.erase_ghost.1 hleafTyping hfresh htargetNot⟩)
      (by
        intro rank env updated restEnv result path target rest ty hwrite hleaf
          _hrest hjoin ihWrite ihRest hfresh hnot htyFresh
        have htargetNot : ¬ LVal.Mentions ghost (prependPath path target) :=
          prependPath_not_mentions (hnot target (by simp))
        have hrestNot :
            ∀ target, target ∈ rest → ¬ LVal.Mentions ghost target := by
          intro candidate hmem
          exact hnot candidate (by simp [hmem])
        rcases hleaf with ⟨leafTy, leafLifetime, hleafTyping⟩
        exact WriteBorrowTargets.cons
          (ihWrite hfresh htargetNot htyFresh)
          ⟨leafTy, leafLifetime,
            LValTyping.erase_ghost.1 hleafTyping hfresh htargetNot⟩
          (ihRest hfresh hrestNot htyFresh)
          (EnvJoin.erase_ghost hjoin))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ihUpdate
          hfresh hnot htyFresh
        have hbaseNe : LVal.base lv ≠ ghost :=
          LVal.base_ne_of_not_mentions hnot
        have hslotErased :
            (env₁.erase ghost).slotAt (LVal.base lv) = some slot := by
          simpa [Env.erase, hbaseNe] using hslot
        have hslotFresh : ghost ∉ PartialTy.allVars slot.ty :=
          hfresh (LVal.base lv) slot hslotErased
        have hupdateErased :
            UpdateAtPath rank (env₁.erase ghost) (LVal.path lv) slot.ty ty
              (env₂.erase ghost) updatedTy :=
          ihUpdate hfresh hslotFresh htyFresh
        rw [Env.erase_update_ne env₂ (x := ghost) (y := LVal.base lv)
          { slot with ty := updatedTy } hbaseNe]
        exact EnvWrite.intro hslotErased hupdateErased)
      hupdate hfresh holdFresh htyFresh

  theorem WriteBorrowTargets.erase_ghost {rank : Nat} {env result : Env}
      {path : List Unit} {targets : List LVal} {ty : Ty} {ghost : Name} :
      WriteBorrowTargets rank env path targets ty result →
      Env.TypeNameFresh (env.erase ghost) ghost →
      (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
      ghost ∉ Ty.allVars ty →
      WriteBorrowTargets rank (env.erase ghost) path targets ty
        (result.erase ghost) := by
    intro htargets hfresh hnot htyFresh
    exact WriteBorrowTargets.rec
      (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
        Env.TypeNameFresh (env₁.erase ghost) ghost →
        ghost ∉ PartialTy.allVars oldTy →
        ghost ∉ Ty.allVars ty →
        UpdateAtPath rank (env₁.erase ghost) path oldTy ty
          (env₂.erase ghost) updatedTy)
      (motive_2 := fun rank env path targets ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
        ghost ∉ Ty.allVars ty →
        WriteBorrowTargets rank (env.erase ghost) path targets ty
          (result.erase ghost))
      (motive_3 := fun rank env lv ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        ¬ LVal.Mentions ghost lv →
        ghost ∉ Ty.allVars ty →
        EnvWrite rank (env.erase ghost) lv ty (result.erase ghost))
      (by
        intro env old ty hfresh holdFresh htyFresh
        exact UpdateAtPath.strong)
      (by
        intro env rank old joined ty hshape hjoin hfresh holdFresh htyFresh
        exact UpdateAtPath.weak
          (ShapeCompatible.erase_ghost hshape hfresh holdFresh
            (by simpa [PartialTy.allVars] using htyFresh))
          hjoin)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hinner ih
          hfresh holdFresh htyFresh
        exact UpdateAtPath.box
          (ih hfresh (by simpa [PartialTy.allVars] using holdFresh)
            htyFresh))
      (by
        intro env₁ env₂ rank path targets ty _htargets ih hfresh holdFresh htyFresh
        have htargetsNot :
            ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target :=
          not_mentions_of_mem_borrow_allVars holdFresh
        exact UpdateAtPath.mutBorrow (ih hfresh htargetsNot htyFresh))
      (by
        intro rank env path ty hfresh hnot htyFresh
        exact WriteBorrowTargets.nil)
      (by
        intro rank env updated path target ty hwrite hleaf ihWrite
          hfresh hnot htyFresh
        have htargetNot : ¬ LVal.Mentions ghost (prependPath path target) :=
          prependPath_not_mentions (hnot target (by simp))
        rcases hleaf with ⟨leafTy, leafLifetime, hleafTyping⟩
        exact WriteBorrowTargets.singleton
          (ihWrite hfresh htargetNot htyFresh)
          ⟨leafTy, leafLifetime,
            LValTyping.erase_ghost.1 hleafTyping hfresh htargetNot⟩)
      (by
        intro rank env updated restEnv result path target rest ty hwrite hleaf
          _hrest hjoin ihWrite ihRest hfresh hnot htyFresh
        have htargetNot : ¬ LVal.Mentions ghost (prependPath path target) :=
          prependPath_not_mentions (hnot target (by simp))
        have hrestNot :
            ∀ target, target ∈ rest → ¬ LVal.Mentions ghost target := by
          intro candidate hmem
          exact hnot candidate (by simp [hmem])
        rcases hleaf with ⟨leafTy, leafLifetime, hleafTyping⟩
        exact WriteBorrowTargets.cons
          (ihWrite hfresh htargetNot htyFresh)
          ⟨leafTy, leafLifetime,
            LValTyping.erase_ghost.1 hleafTyping hfresh htargetNot⟩
          (ihRest hfresh hrestNot htyFresh)
          (EnvJoin.erase_ghost hjoin))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ihUpdate
          hfresh hnot htyFresh
        have hbaseNe : LVal.base lv ≠ ghost :=
          LVal.base_ne_of_not_mentions hnot
        have hslotErased :
            (env₁.erase ghost).slotAt (LVal.base lv) = some slot := by
          simpa [Env.erase, hbaseNe] using hslot
        have hslotFresh : ghost ∉ PartialTy.allVars slot.ty :=
          hfresh (LVal.base lv) slot hslotErased
        have hupdateErased :
            UpdateAtPath rank (env₁.erase ghost) (LVal.path lv) slot.ty ty
              (env₂.erase ghost) updatedTy :=
          ihUpdate hfresh hslotFresh htyFresh
        rw [Env.erase_update_ne env₂ (x := ghost) (y := LVal.base lv)
          { slot with ty := updatedTy } hbaseNe]
        exact EnvWrite.intro hslotErased hupdateErased)
      htargets hfresh hnot htyFresh

  theorem EnvWrite.erase_ghost {rank : Nat} {env₁ env₂ : Env}
      {lv : LVal} {ty : Ty} {ghost : Name} :
      EnvWrite rank env₁ lv ty env₂ →
      Env.TypeNameFresh (env₁.erase ghost) ghost →
      ¬ LVal.Mentions ghost lv →
      ghost ∉ Ty.allVars ty →
      EnvWrite rank (env₁.erase ghost) lv ty (env₂.erase ghost) := by
    intro hwrite hfresh hnot htyFresh
    exact EnvWrite.rec
      (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
        Env.TypeNameFresh (env₁.erase ghost) ghost →
        ghost ∉ PartialTy.allVars oldTy →
        ghost ∉ Ty.allVars ty →
        UpdateAtPath rank (env₁.erase ghost) path oldTy ty
          (env₂.erase ghost) updatedTy)
      (motive_2 := fun rank env path targets ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
        ghost ∉ Ty.allVars ty →
        WriteBorrowTargets rank (env.erase ghost) path targets ty
          (result.erase ghost))
      (motive_3 := fun rank env lv ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        ¬ LVal.Mentions ghost lv →
        ghost ∉ Ty.allVars ty →
        EnvWrite rank (env.erase ghost) lv ty (result.erase ghost))
      (by
        intro env old ty hfresh holdFresh htyFresh
        exact UpdateAtPath.strong)
      (by
        intro env rank old joined ty hshape hjoin hfresh holdFresh htyFresh
        exact UpdateAtPath.weak
          (ShapeCompatible.erase_ghost hshape hfresh holdFresh
            (by simpa [PartialTy.allVars] using htyFresh))
          hjoin)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hinner ih
          hfresh holdFresh htyFresh
        exact UpdateAtPath.box
          (ih hfresh (by simpa [PartialTy.allVars] using holdFresh)
            htyFresh))
      (by
        intro env₁ env₂ rank path targets ty _htargets ih hfresh holdFresh htyFresh
        have htargetsNot :
            ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target :=
          not_mentions_of_mem_borrow_allVars holdFresh
        exact UpdateAtPath.mutBorrow (ih hfresh htargetsNot htyFresh))
      (by
        intro rank env path ty hfresh hnot htyFresh
        exact WriteBorrowTargets.nil)
      (by
        intro rank env updated path target ty hwrite hleaf ihWrite
          hfresh hnot htyFresh
        have htargetNot : ¬ LVal.Mentions ghost (prependPath path target) :=
          prependPath_not_mentions (hnot target (by simp))
        rcases hleaf with ⟨leafTy, leafLifetime, hleafTyping⟩
        exact WriteBorrowTargets.singleton
          (ihWrite hfresh htargetNot htyFresh)
          ⟨leafTy, leafLifetime,
            LValTyping.erase_ghost.1 hleafTyping hfresh htargetNot⟩)
      (by
        intro rank env updated restEnv result path target rest ty hwrite hleaf
          _hrest hjoin ihWrite ihRest hfresh hnot htyFresh
        have htargetNot : ¬ LVal.Mentions ghost (prependPath path target) :=
          prependPath_not_mentions (hnot target (by simp))
        have hrestNot :
            ∀ target, target ∈ rest → ¬ LVal.Mentions ghost target := by
          intro candidate hmem
          exact hnot candidate (by simp [hmem])
        rcases hleaf with ⟨leafTy, leafLifetime, hleafTyping⟩
        exact WriteBorrowTargets.cons
          (ihWrite hfresh htargetNot htyFresh)
          ⟨leafTy, leafLifetime,
            LValTyping.erase_ghost.1 hleafTyping hfresh htargetNot⟩
          (ihRest hfresh hrestNot htyFresh)
          (EnvJoin.erase_ghost hjoin))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ihUpdate
          hfresh hnot htyFresh
        have hbaseNe : LVal.base lv ≠ ghost :=
          LVal.base_ne_of_not_mentions hnot
        have hslotErased :
            (env₁.erase ghost).slotAt (LVal.base lv) = some slot := by
          simpa [Env.erase, hbaseNe] using hslot
        have hslotFresh : ghost ∉ PartialTy.allVars slot.ty :=
          hfresh (LVal.base lv) slot hslotErased
        have hupdateErased :
            UpdateAtPath rank (env₁.erase ghost) (LVal.path lv) slot.ty ty
              (env₂.erase ghost) updatedTy :=
          ihUpdate hfresh hslotFresh htyFresh
        rw [Env.erase_update_ne env₂ (x := ghost) (y := LVal.base lv)
          { slot with ty := updatedTy } hbaseNe]
        exact EnvWrite.intro hslotErased hupdateErased)
      hwrite hfresh hnot htyFresh
end

mutual
  theorem UpdateAtPath.typeNameFresh_erase {rank : Nat} {env₁ env₂ : Env}
      {path : List Unit} {oldTy updatedTy : PartialTy} {ty : Ty}
      {ghost : Name} :
      UpdateAtPath rank env₁ path oldTy ty env₂ updatedTy →
      Env.TypeNameFresh (env₁.erase ghost) ghost →
      ghost ∉ PartialTy.allVars oldTy →
      ghost ∉ Ty.allVars ty →
      Env.TypeNameFresh (env₂.erase ghost) ghost ∧
        ghost ∉ PartialTy.allVars updatedTy := by
    intro hupdate hfresh holdFresh htyFresh
    exact UpdateAtPath.rec
      (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
        Env.TypeNameFresh (env₁.erase ghost) ghost →
        ghost ∉ PartialTy.allVars oldTy →
        ghost ∉ Ty.allVars ty →
        Env.TypeNameFresh (env₂.erase ghost) ghost ∧
          ghost ∉ PartialTy.allVars updatedTy)
      (motive_2 := fun rank env path targets ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
        ghost ∉ Ty.allVars ty →
        Env.TypeNameFresh (result.erase ghost) ghost)
      (motive_3 := fun rank env lv ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        ¬ LVal.Mentions ghost lv →
        ghost ∉ Ty.allVars ty →
        Env.TypeNameFresh (result.erase ghost) ghost)
      (by
        intro env old ty hfresh holdFresh htyFresh
        exact ⟨hfresh, by simpa [PartialTy.allVars] using htyFresh⟩)
      (by
        intro env rank old joined ty hshape hjoin hfresh holdFresh htyFresh
        exact ⟨hfresh,
          PartialTyJoin.allVars_fresh_of_shapeCompatible hshape hjoin
            holdFresh htyFresh⟩)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hinner ih
          hfresh holdFresh htyFresh
        rcases ih hfresh (by simpa [PartialTy.allVars] using holdFresh)
          htyFresh with ⟨hfreshOut, hupdatedFresh⟩
        exact ⟨hfreshOut, by simpa [PartialTy.allVars] using hupdatedFresh⟩)
      (by
        intro env₁ env₂ rank path targets ty _htargets ih hfresh holdFresh htyFresh
        have htargetsNot :
            ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target :=
          not_mentions_of_mem_borrow_allVars holdFresh
        refine ⟨ih hfresh htargetsNot htyFresh, ?_⟩
        intro hv
        simp [PartialTy.allVars, Ty.allVars, List.mem_map] at hv
        rcases hv with ⟨target, hmem, hbase⟩
        exact holdFresh (by
          simp [PartialTy.allVars, Ty.allVars, List.mem_map]
          exact ⟨target, hmem, hbase⟩))
      (by
        intro rank env path ty hfresh _hnot _htyFresh
        exact hfresh)
      (by
        intro rank env updated path target ty _hwrite _hleaf ihWrite
          hfresh hnot htyFresh
        exact ihWrite hfresh (prependPath_not_mentions (hnot target (by simp)))
          htyFresh)
      (by
        intro rank env updated restEnv result path target rest ty _hwrite
          _hleaf _hrest hjoin ihWrite ihRest hfresh hnot htyFresh
        have htargetNot : ¬ LVal.Mentions ghost (prependPath path target) :=
          prependPath_not_mentions (hnot target (by simp))
        have hrestNot :
            ∀ target, target ∈ rest → ¬ LVal.Mentions ghost target := by
          intro candidate hmem
          exact hnot candidate (by simp [hmem])
        exact EnvJoin.typeNameFresh_erase hjoin
          (ihWrite hfresh htargetNot htyFresh)
          (ihRest hfresh hrestNot htyFresh))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ihUpdate
          hfresh hnot htyFresh
        have hbaseNe : LVal.base lv ≠ ghost :=
          LVal.base_ne_of_not_mentions hnot
        have hslotErased :
            (env₁.erase ghost).slotAt (LVal.base lv) = some slot := by
          simpa [Env.erase, hbaseNe] using hslot
        have hslotFresh : ghost ∉ PartialTy.allVars slot.ty :=
          hfresh (LVal.base lv) slot hslotErased
        rcases ihUpdate hfresh hslotFresh htyFresh with
          ⟨hfreshEnv₂, hupdatedFresh⟩
        rw [Env.erase_update_ne env₂ (x := ghost) (y := LVal.base lv)
          { slot with ty := updatedTy } hbaseNe]
        exact Env.typeNameFresh_update hfreshEnv₂ hupdatedFresh)
      hupdate hfresh holdFresh htyFresh

  theorem WriteBorrowTargets.typeNameFresh_erase {rank : Nat}
      {env result : Env} {path : List Unit} {targets : List LVal}
      {ty : Ty} {ghost : Name} :
      WriteBorrowTargets rank env path targets ty result →
      Env.TypeNameFresh (env.erase ghost) ghost →
      (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
      ghost ∉ Ty.allVars ty →
      Env.TypeNameFresh (result.erase ghost) ghost := by
    intro htargets hfresh hnot htyFresh
    exact WriteBorrowTargets.rec
      (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
        Env.TypeNameFresh (env₁.erase ghost) ghost →
        ghost ∉ PartialTy.allVars oldTy →
        ghost ∉ Ty.allVars ty →
        Env.TypeNameFresh (env₂.erase ghost) ghost ∧
          ghost ∉ PartialTy.allVars updatedTy)
      (motive_2 := fun rank env path targets ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
        ghost ∉ Ty.allVars ty →
        Env.TypeNameFresh (result.erase ghost) ghost)
      (motive_3 := fun rank env lv ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        ¬ LVal.Mentions ghost lv →
        ghost ∉ Ty.allVars ty →
        Env.TypeNameFresh (result.erase ghost) ghost)
      (by
        intro env old ty hfresh holdFresh htyFresh
        exact ⟨hfresh, by simpa [PartialTy.allVars] using htyFresh⟩)
      (by
        intro env rank old joined ty hshape hjoin hfresh holdFresh htyFresh
        exact ⟨hfresh,
          PartialTyJoin.allVars_fresh_of_shapeCompatible hshape hjoin
            holdFresh htyFresh⟩)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hinner ih
          hfresh holdFresh htyFresh
        rcases ih hfresh (by simpa [PartialTy.allVars] using holdFresh)
          htyFresh with ⟨hfreshOut, hupdatedFresh⟩
        exact ⟨hfreshOut, by simpa [PartialTy.allVars] using hupdatedFresh⟩)
      (by
        intro env₁ env₂ rank path targets ty _htargets ih hfresh holdFresh htyFresh
        have htargetsNot :
            ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target :=
          not_mentions_of_mem_borrow_allVars holdFresh
        refine ⟨ih hfresh htargetsNot htyFresh, ?_⟩
        intro hv
        simp [PartialTy.allVars, Ty.allVars, List.mem_map] at hv
        rcases hv with ⟨target, hmem, hbase⟩
        exact holdFresh (by
          simp [PartialTy.allVars, Ty.allVars, List.mem_map]
          exact ⟨target, hmem, hbase⟩))
      (by
        intro rank env path ty hfresh _hnot _htyFresh
        exact hfresh)
      (by
        intro rank env updated path target ty _hwrite _hleaf ihWrite
          hfresh hnot htyFresh
        exact ihWrite hfresh (prependPath_not_mentions (hnot target (by simp)))
          htyFresh)
      (by
        intro rank env updated restEnv result path target rest ty _hwrite
          _hleaf _hrest hjoin ihWrite ihRest hfresh hnot htyFresh
        have htargetNot : ¬ LVal.Mentions ghost (prependPath path target) :=
          prependPath_not_mentions (hnot target (by simp))
        have hrestNot :
            ∀ target, target ∈ rest → ¬ LVal.Mentions ghost target := by
          intro candidate hmem
          exact hnot candidate (by simp [hmem])
        exact EnvJoin.typeNameFresh_erase hjoin
          (ihWrite hfresh htargetNot htyFresh)
          (ihRest hfresh hrestNot htyFresh))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ihUpdate
          hfresh hnot htyFresh
        have hbaseNe : LVal.base lv ≠ ghost :=
          LVal.base_ne_of_not_mentions hnot
        have hslotErased :
            (env₁.erase ghost).slotAt (LVal.base lv) = some slot := by
          simpa [Env.erase, hbaseNe] using hslot
        have hslotFresh : ghost ∉ PartialTy.allVars slot.ty :=
          hfresh (LVal.base lv) slot hslotErased
        rcases ihUpdate hfresh hslotFresh htyFresh with
          ⟨hfreshEnv₂, hupdatedFresh⟩
        rw [Env.erase_update_ne env₂ (x := ghost) (y := LVal.base lv)
          { slot with ty := updatedTy } hbaseNe]
        exact Env.typeNameFresh_update hfreshEnv₂ hupdatedFresh)
      htargets hfresh hnot htyFresh

  theorem EnvWrite.typeNameFresh_erase {rank : Nat} {env result : Env}
      {lv : LVal} {ty : Ty} {ghost : Name} :
      EnvWrite rank env lv ty result →
      Env.TypeNameFresh (env.erase ghost) ghost →
      ¬ LVal.Mentions ghost lv →
      ghost ∉ Ty.allVars ty →
      Env.TypeNameFresh (result.erase ghost) ghost := by
    intro hwrite hfresh hnot htyFresh
    exact EnvWrite.rec
      (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
        Env.TypeNameFresh (env₁.erase ghost) ghost →
        ghost ∉ PartialTy.allVars oldTy →
        ghost ∉ Ty.allVars ty →
        Env.TypeNameFresh (env₂.erase ghost) ghost ∧
          ghost ∉ PartialTy.allVars updatedTy)
      (motive_2 := fun rank env path targets ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        (∀ target, target ∈ targets → ¬ LVal.Mentions ghost target) →
        ghost ∉ Ty.allVars ty →
        Env.TypeNameFresh (result.erase ghost) ghost)
      (motive_3 := fun rank env lv ty result _ =>
        Env.TypeNameFresh (env.erase ghost) ghost →
        ¬ LVal.Mentions ghost lv →
        ghost ∉ Ty.allVars ty →
        Env.TypeNameFresh (result.erase ghost) ghost)
      (by
        intro env old ty hfresh holdFresh htyFresh
        exact ⟨hfresh, by simpa [PartialTy.allVars] using htyFresh⟩)
      (by
        intro env rank old joined ty hshape hjoin hfresh holdFresh htyFresh
        exact ⟨hfresh,
          PartialTyJoin.allVars_fresh_of_shapeCompatible hshape hjoin
            holdFresh htyFresh⟩)
      (by
        intro env₁ env₂ rank path inner updatedInner ty _hinner ih
          hfresh holdFresh htyFresh
        rcases ih hfresh (by simpa [PartialTy.allVars] using holdFresh)
          htyFresh with ⟨hfreshOut, hupdatedFresh⟩
        exact ⟨hfreshOut, by simpa [PartialTy.allVars] using hupdatedFresh⟩)
      (by
        intro env₁ env₂ rank path targets ty _htargets ih hfresh holdFresh htyFresh
        have htargetsNot :
            ∀ target, target ∈ targets → ¬ LVal.Mentions ghost target :=
          not_mentions_of_mem_borrow_allVars holdFresh
        refine ⟨ih hfresh htargetsNot htyFresh, ?_⟩
        intro hv
        simp [PartialTy.allVars, Ty.allVars, List.mem_map] at hv
        rcases hv with ⟨target, hmem, hbase⟩
        exact holdFresh (by
          simp [PartialTy.allVars, Ty.allVars, List.mem_map]
          exact ⟨target, hmem, hbase⟩))
      (by
        intro rank env path ty hfresh _hnot _htyFresh
        exact hfresh)
      (by
        intro rank env updated path target ty _hwrite _hleaf ihWrite
          hfresh hnot htyFresh
        exact ihWrite hfresh (prependPath_not_mentions (hnot target (by simp)))
          htyFresh)
      (by
        intro rank env updated restEnv result path target rest ty _hwrite
          _hleaf _hrest hjoin ihWrite ihRest hfresh hnot htyFresh
        have htargetNot : ¬ LVal.Mentions ghost (prependPath path target) :=
          prependPath_not_mentions (hnot target (by simp))
        have hrestNot :
            ∀ target, target ∈ rest → ¬ LVal.Mentions ghost target := by
          intro candidate hmem
          exact hnot candidate (by simp [hmem])
        exact EnvJoin.typeNameFresh_erase hjoin
          (ihWrite hfresh htargetNot htyFresh)
          (ihRest hfresh hrestNot htyFresh))
      (by
        intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ihUpdate
          hfresh hnot htyFresh
        have hbaseNe : LVal.base lv ≠ ghost :=
          LVal.base_ne_of_not_mentions hnot
        have hslotErased :
            (env₁.erase ghost).slotAt (LVal.base lv) = some slot := by
          simpa [Env.erase, hbaseNe] using hslot
        have hslotFresh : ghost ∉ PartialTy.allVars slot.ty :=
          hfresh (LVal.base lv) slot hslotErased
        rcases ihUpdate hfresh hslotFresh htyFresh with
          ⟨hfreshEnv₂, hupdatedFresh⟩
        rw [Env.erase_update_ne env₂ (x := ghost) (y := LVal.base lv)
          { slot with ty := updatedTy } hbaseNe]
        exact Env.typeNameFresh_update hfreshEnv₂ hupdatedFresh)
      hwrite hfresh hnot htyFresh
  end

theorem TermTyping.erase_ghost_pack {ghost : Name} {env : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} {ty : Ty}
    {envOut : Env} :
    TermTyping env typing lifetime term ty envOut →
    Env.TypeNameFresh (env.erase ghost) ghost →
    StoreTyping.TypeNameFresh typing ghost →
    ¬ Term.Mentions ghost term →
    TermTyping (env.erase ghost) typing lifetime term ty
      (envOut.erase ghost) ∧
    Env.TypeNameFresh (envOut.erase ghost) ghost ∧
    ghost ∉ Ty.allVars ty := by
  intro htyping
  exact TermTyping.rec
    (motive_1 := fun env typing lifetime term ty envOut _ =>
      Env.TypeNameFresh (env.erase ghost) ghost →
      StoreTyping.TypeNameFresh typing ghost →
      ¬ Term.Mentions ghost term →
      TermTyping (env.erase ghost) typing lifetime term ty
        (envOut.erase ghost) ∧
      Env.TypeNameFresh (envOut.erase ghost) ghost ∧
      ghost ∉ Ty.allVars ty)
    (motive_2 := fun env typing lifetime terms ty envOut _ =>
      Env.TypeNameFresh (env.erase ghost) ghost →
      StoreTyping.TypeNameFresh typing ghost →
      ¬ TermList.Mentions ghost terms →
      TermListTyping (env.erase ghost) typing lifetime terms ty
        (envOut.erase ghost) ∧
      Env.TypeNameFresh (envOut.erase ghost) ghost ∧
      ghost ∉ Ty.allVars ty)
    (by
      intro env typing lifetime value ty hvalue hfresh hstore _hnot
      exact ⟨TermTyping.const hvalue, hfresh,
        ValueTyping.typeNameFresh hvalue hstore⟩)
    (by
      intro env typing lifetime ty hwell hloan hfresh _hstore _hnot
      have htyFresh : ghost ∉ Ty.allVars ty :=
        Ty.no_allVars_of_loanFree hloan ghost
      exact ⟨TermTyping.missing
        (WellFormedTy.erase_ghost hwell hfresh htyFresh) hloan,
        hfresh, htyFresh⟩)
    (by
      intro env typing lifetime valueLifetime lv ty hLv hcopy hnotRead
        hfresh _hstore hnot
      have hnotLv : ¬ LVal.Mentions ghost lv := by
        simpa [Term.Mentions] using hnot
      have hLvErased := LValTyping.erase_ghost.1 hLv hfresh hnotLv
      have htyFresh : ghost ∉ Ty.allVars ty := by
        have := LValTyping.typeNameFresh.1 hLvErased hfresh
        simpa [PartialTy.allVars] using this
      exact ⟨TermTyping.copy hLvErased hcopy (by
        intro hread
        exact hnotRead (ReadProhibited.erase_to_env hread)),
        hfresh, htyFresh⟩)
    (by
      intro env₁ env₂ typing lifetime valueLifetime lv ty hLv hnotWrite
        hmove hfresh _hstore hnot
      have hnotLv : ¬ LVal.Mentions ghost lv := by
        simpa [Term.Mentions] using hnot
      have hLvErased := LValTyping.erase_ghost.1 hLv hfresh hnotLv
      have htyFresh : ghost ∉ Ty.allVars ty := by
        have := LValTyping.typeNameFresh.1 hLvErased hfresh
        simpa [PartialTy.allVars] using this
      have hmoveErased := EnvMove.erase_ghost hmove hnotLv
      exact ⟨TermTyping.move hLvErased (by
        intro hwrite
        exact hnotWrite (WriteProhibited.erase_to_env hwrite))
        hmoveErased,
        EnvMove.typeNameFresh_erase hmove hfresh hnotLv,
        htyFresh⟩)
    (by
      intro env typing lifetime valueLifetime lv ty hLv hmutable hnotWrite
        hfresh _hstore hnot
      have hnotLv : ¬ LVal.Mentions ghost lv := by
        simpa [Term.Mentions] using hnot
      have hLvErased := LValTyping.erase_ghost.1 hLv hfresh hnotLv
      have htyFresh : ghost ∉ Ty.allVars ty := by
        have := LValTyping.typeNameFresh.1 hLvErased hfresh
        simpa [PartialTy.allVars] using this
      have hresultFresh : ghost ∉ Ty.allVars (.borrow true [lv]) := by
        intro hv
        simp [Ty.allVars, List.mem_map] at hv
        exact hnotLv ((LVal.mentions_iff_base (ghost := ghost) lv).2 hv.symm)
      exact ⟨TermTyping.mutBorrow hLvErased
        (Mutable.erase_ghost hmutable hfresh hnotLv)
        (by
          intro hwrite
          exact hnotWrite (WriteProhibited.erase_to_env hwrite)),
        hfresh, hresultFresh⟩)
    (by
      intro env typing lifetime valueLifetime lv ty hLv hnotRead
        hfresh _hstore hnot
      have hnotLv : ¬ LVal.Mentions ghost lv := by
        simpa [Term.Mentions] using hnot
      have hLvErased := LValTyping.erase_ghost.1 hLv hfresh hnotLv
      have htyFresh : ghost ∉ Ty.allVars ty := by
        have := LValTyping.typeNameFresh.1 hLvErased hfresh
        simpa [PartialTy.allVars] using this
      have hresultFresh : ghost ∉ Ty.allVars (.borrow false [lv]) := by
        intro hv
        simp [Ty.allVars, List.mem_map] at hv
        exact hnotLv ((LVal.mentions_iff_base (ghost := ghost) lv).2 hv.symm)
      exact ⟨TermTyping.immBorrow hLvErased
        (by
          intro hread
          exact hnotRead (ReadProhibited.erase_to_env hread)),
        hfresh, hresultFresh⟩)
    (by
      intro env₁ env₂ typing lifetime innerTerm innerTy hInner ih
        hfresh hstore hnot
      have hnotInner : ¬ Term.Mentions ghost innerTerm := by
        simpa [Term.Mentions] using hnot
      rcases ih hfresh hstore hnotInner with
        ⟨hInnerErased, hfreshOut, htyFresh⟩
      exact ⟨TermTyping.box hInnerErased, hfreshOut,
        by simpa [Ty.allVars] using htyFresh⟩)
    (by
      intro env₁ env₂ env₃ typing lifetime blockLifetime terms ty hchild
        hterms hwell hdrop ih hfresh hstore hnot
      have hnotTerms : ¬ TermList.Mentions ghost terms := by
        simpa [Term.Mentions] using hnot
      rcases ih hfresh hstore hnotTerms with
        ⟨htermsErased, hfreshTerms, htyFresh⟩
      subst hdrop
      exact ⟨TermTyping.block hchild htermsErased
        (WellFormedTy.erase_ghost hwell hfreshTerms htyFresh)
        (Env.dropLifetime_erase env₂ ghost blockLifetime),
        by
          simpa [Env.dropLifetime_erase env₂ ghost blockLifetime] using
            Env.typeNameFresh_dropLifetime hfreshTerms,
        htyFresh⟩)
    (by
      intro env₁ env₂ env₃ typing lifetime x init ty hfreshX hinit
        hfreshOutX hoblig henv ih hfresh hstore hnot
      have hxGhost : x ≠ ghost := by
        intro hx
        exact hnot (by simp [Term.Mentions, hx])
      have hnotInit : ¬ Term.Mentions ghost init := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ih hfresh hstore hnotInit with
        ⟨hinitErased, hfreshInit, htyFresh⟩
      subst henv
      have heraseUpdate :=
        Env.erase_update_ne env₂ (x := ghost) (y := x)
          { ty := .ty ty, lifetime := lifetime } hxGhost
      rw [heraseUpdate]
      exact ⟨TermTyping.declare
        (Env.erase_fresh_of_ne hfreshX hxGhost)
        hinitErased
        (Env.erase_fresh_of_ne hfreshOutX hxGhost)
        (FreshUpdateCoherenceObligations.erase_ghost hoblig
          hfreshInit hxGhost htyFresh)
        rfl,
        Env.typeNameFresh_update hfreshInit
          (by simpa [PartialTy.allVars] using htyFresh),
                by simp [Ty.allVars]⟩)
    (by
      intro env₁ env₂ env₃ typing lifetime targetLifetime lhs oldTy rhs
        rhsTy hRhs hLhs hshape hwell hwrite hranked hcoh hcontained
        hnotWrite ih hfresh hstore hnot
      have hnotRhs : ¬ Term.Mentions ghost rhs := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotLhs : ¬ LVal.Mentions ghost lhs := by
        intro hmention
        have hbase := (LVal.mentions_iff_base (ghost := ghost) lhs).1 hmention
        exact hnot (by simp [Term.Mentions, hbase])
      rcases ih hfresh hstore hnotRhs with
        ⟨hRhsErased, hfreshRhs, hrhsFresh⟩
      have hLhsErased := LValTyping.erase_ghost.1 hLhs hfreshRhs hnotLhs
      have holdFresh : ghost ∉ PartialTy.allVars oldTy :=
        LValTyping.typeNameFresh.1 hLhsErased hfreshRhs
      have hwriteErased :=
        EnvWrite.erase_ghost hwrite hfreshRhs hnotLhs hrhsFresh
      have hfreshWrite :=
        EnvWrite.typeNameFresh_erase hwrite hfreshRhs hnotLhs hrhsFresh
      rcases hranked with ⟨φ, hlinear, hrhsBelow⟩
      have hbaseNe : LVal.base lhs ≠ ghost :=
        LVal.base_ne_of_not_mentions hnotLhs
      exact ⟨TermTyping.assign hRhsErased hLhsErased
        (ShapeCompatible.erase_ghost hshape hfreshRhs holdFresh
          (by simpa [PartialTy.allVars] using hrhsFresh))
        (WellFormedTy.erase_ghost hwell hfreshRhs hrhsFresh)
        hwriteErased
        ⟨φ, LinearizedBy.erase_ghost hlinear,
          EnvWriteRhsBorrowTargetsBelow.erase_ghost hrhsBelow⟩
        (Coherent.erase_ghost hcoh hfreshWrite)
        (EnvWriteRhsTargetsWellFormed.erase_ghost hcontained hfreshWrite)
        (by
          intro hwriteProhibited
          exact hnotWrite (WriteProhibited.erase_to_env hwriteProhibited)),
        hfreshWrite,
                by simp [Ty.allVars]⟩)
    (by
      intro env₁ env₂ env₃ envGhost localGhost typing lifetime lhs rhs
        lhsTy rhsTy hLhs hlocalFresh hlocalTypeFresh hlocalTyFresh
        hstoreLocal hRhsGhost hnotLocalRhs henvEq hcopyL hcopyR hshape
        ihL ihRhs hfresh hstore hnot
      have hnotLhs : ¬ Term.Mentions ghost lhs := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotRhs : ¬ Term.Mentions ghost rhs := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ihL hfresh hstore hnotLhs with
        ⟨hLhsErased, hfreshLhs, hlhsFresh⟩
      by_cases hsame : localGhost = ghost
      · subst localGhost
        have hRhsForEq :
            TermTyping
              ((env₂.erase ghost).update ghost
                { ty := .ty lhsTy, lifetime := lifetime })
              typing lifetime rhs rhsTy envGhost := by
          simpa [Env.erase_of_fresh hlocalFresh] using hRhsGhost
        have hinputFresh :
            Env.TypeNameFresh
              ((env₂.update ghost { ty := .ty lhsTy, lifetime := lifetime }).erase
                ghost)
              ghost := by
          simpa [Env.erase_update_same_of_fresh hlocalFresh] using
            hlocalTypeFresh
        rcases ihRhs hinputFresh hstoreLocal hnotLocalRhs with
          ⟨_hRhsErased, hfreshRhs, hrhsFresh⟩
        subst henvEq
        have hEqTyping :
            TermTyping (env₁.erase ghost) typing lifetime (.eq lhs rhs) .bool
              (envGhost.erase ghost) :=
          TermTyping.eq hLhsErased
            (Env.fresh_erase env₂ ghost)
            hfreshLhs hlhsFresh hstoreLocal hRhsForEq hnotLocalRhs rfl
            hcopyL hcopyR hshape
        exact ⟨by simpa using hEqTyping,
          by simpa using hfreshRhs,
                  by simp [Ty.allVars]⟩
      · have hinputFresh :
            Env.TypeNameFresh
              ((env₂.update localGhost
                { ty := .ty lhsTy, lifetime := lifetime }).erase ghost)
              ghost := by
          rw [Env.erase_update_ne env₂ (x := ghost) (y := localGhost)
            { ty := .ty lhsTy, lifetime := lifetime } hsame]
          exact Env.typeNameFresh_update hfreshLhs
            (by simpa [PartialTy.allVars] using hlhsFresh)
        rcases ihRhs hinputFresh hstore hnotRhs with
          ⟨hRhsErasedRaw, hfreshRhsRaw, hrhsFresh⟩
        have hRhsErased :
            TermTyping
              ((env₂.erase ghost).update localGhost
                { ty := .ty lhsTy, lifetime := lifetime })
              typing lifetime rhs rhsTy (envGhost.erase ghost) := by
          simpa [Env.erase_update_ne env₂ (x := ghost) (y := localGhost)
            { ty := .ty lhsTy, lifetime := lifetime } hsame] using
            hRhsErasedRaw
        subst henvEq
        have hfreshShape :
            Env.TypeNameFresh ((envGhost.erase localGhost).erase ghost) ghost := by
          rw [Env.erase_comm envGhost localGhost ghost]
          exact Env.typeNameFresh_erase hfreshRhsRaw
        have hshapeErased :
            ShapeCompatible ((envGhost.erase localGhost).erase ghost)
              (.ty lhsTy) (.ty rhsTy) :=
          ShapeCompatible.erase_ghost hshape hfreshShape
            (by simpa [PartialTy.allVars] using hlhsFresh)
            (by simpa [PartialTy.allVars] using hrhsFresh)
        have hEqTyping :
            TermTyping (env₁.erase ghost) typing lifetime (.eq lhs rhs) .bool
              ((envGhost.erase ghost).erase localGhost) :=
          TermTyping.eq hLhsErased
            (Env.erase_fresh_of_ne hlocalFresh hsame)
            (Env.typeNameFresh_erase hlocalTypeFresh)
            hlocalTyFresh hstoreLocal hRhsErased hnotLocalRhs rfl
            hcopyL hcopyR
            (by
              rw [← Env.erase_comm envGhost localGhost ghost]
              exact hshapeErased)
        exact ⟨by
            rw [Env.erase_comm envGhost localGhost ghost]
            exact hEqTyping,
          by
            rw [Env.erase_comm envGhost localGhost ghost]
            exact Env.typeNameFresh_erase hfreshRhsRaw,
          by simp [Ty.allVars]⟩)
    (by
      intro env₁ env₂ env₃ env₄ env₅ typing lifetime condition trueBranch
        falseBranch trueTy falseTy joinTy hcondition htrue hfalse htyJoin
        henvJoin hsameLeft hsameRight hwellJoin hcoherent hlinear
        hborrowSafe hresultSafe ihCondition ihTrue ihFalse
        hfresh hstore hnot
      have hnotCondition : ¬ Term.Mentions ghost condition := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotTrue : ¬ Term.Mentions ghost trueBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotFalse : ¬ Term.Mentions ghost falseBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ihCondition hfresh hstore hnotCondition with
        ⟨hconditionErased, hfreshCond, _hboolFresh⟩
      rcases ihTrue hfreshCond hstore hnotTrue with
        ⟨htrueErased, hfreshTrue, htrueTyFresh⟩
      rcases ihFalse hfreshCond hstore hnotFalse with
        ⟨hfalseErased, hfreshFalse, hfalseTyFresh⟩
      have hjoinTyFresh : ghost ∉ Ty.allVars joinTy := by
        have hpartial :=
          PartialTyJoin.allVars_fresh htyJoin
            (by simpa [PartialTy.allVars] using htrueTyFresh)
            (by simpa [PartialTy.allVars] using hfalseTyFresh)
        simpa [PartialTy.allVars] using hpartial
      have hfreshJoin : Env.TypeNameFresh (env₅.erase ghost) ghost :=
        EnvJoin.typeNameFresh_erase henvJoin hfreshTrue hfreshFalse
      exact ⟨TermTyping.ite hconditionErased htrueErased hfalseErased
        htyJoin (EnvJoin.erase_ghost henvJoin)
        (EnvJoinSameShape.erase_ghost hsameLeft)
        (EnvJoinSameShape.erase_ghost hsameRight)
        (WellFormedTy.erase_ghost hwellJoin hfreshJoin hjoinTyFresh)
        (Coherent.erase_ghost hcoherent hfreshJoin)
        (Linearizable.erase_ghost hlinear)
        (BorrowSafeEnv.erase hborrowSafe)
        (TyBorrowSafeAgainstEnv.erase_ghost hresultSafe),
        hfreshJoin, hjoinTyFresh⟩)
    (by
      intro env₁ env₂ env₃ env₄ typing lifetime condition trueBranch
        falseBranch trueTy falseTy hcondition htrue hfalse hdiverges
        ihCondition ihTrue ihFalse hfresh hstore hnot
      have hnotCondition : ¬ Term.Mentions ghost condition := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotTrue : ¬ Term.Mentions ghost trueBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotFalse : ¬ Term.Mentions ghost falseBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ihCondition hfresh hstore hnotCondition with
        ⟨hconditionErased, hfreshCond, _hboolFresh⟩
      rcases ihTrue hfreshCond hstore hnotTrue with
        ⟨htrueErased, hfreshTrue, htrueFresh⟩
      rcases ihFalse hfreshCond hstore hnotFalse with
        ⟨hfalseErased, _hfreshFalse, _hfalseFresh⟩
      exact ⟨TermTyping.iteDiverging hconditionErased htrueErased
        hfalseErased hdiverges, hfreshTrue, htrueFresh⟩)
    (by
      intro env₁ env₂ env₃ env₄ typing lifetime condition trueBranch
        falseBranch trueTy falseTy hcondition htrue hfalse hdiverges
        ihCondition ihTrue ihFalse hfresh hstore hnot
      have hnotCondition : ¬ Term.Mentions ghost condition := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotTrue : ¬ Term.Mentions ghost trueBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotFalse : ¬ Term.Mentions ghost falseBranch := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ihCondition hfresh hstore hnotCondition with
        ⟨hconditionErased, hfreshCond, _hboolFresh⟩
      rcases ihTrue hfreshCond hstore hnotTrue with
        ⟨htrueErased, _hfreshTrue, _htrueFresh⟩
      rcases ihFalse hfreshCond hstore hnotFalse with
        ⟨hfalseErased, hfreshFalse, hfalseFresh⟩
      exact ⟨TermTyping.iteTrueDiverging hconditionErased htrueErased
        hfalseErased hdiverges, hfreshFalse, hfalseFresh⟩)
    (by
      intro env₁ env₂ env₃ typing lifetime bodyLifetime condition body
        bodyTy hchild hcondition hbody hdiverges ihCondition ihBody
        hfresh hstore hnot
      have hnotCondition : ¬ Term.Mentions ghost condition := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotBody : ¬ Term.Mentions ghost body := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      rcases ihCondition hfresh hstore hnotCondition with
        ⟨hconditionErased, hfreshCond, _hboolFresh⟩
      rcases ihBody hfreshCond hstore hnotBody with
        ⟨hbodyErased, _hfreshBody, _hbodyFresh⟩
      exact ⟨TermTyping.whileLoopDiverging hchild hconditionErased
        hbodyErased hdiverges, hfreshCond, by simp [Ty.allVars]⟩)
    (by
      intro env₁ envBack envInv env₂ envEntry₂ env₃ envEntry₃ typing
        lifetime bodyLifetime condition body bodyTy bodyEntryTy hchild
        hjoin hsameEntry hsameBack hcontained hcoherent hlinear hborrowSafe
        hnameFresh hcondition hbody hbodyWell hdrop hentryCondition hentryBody
        ihCondition ihBody ihEntryCondition ihEntryBody hfresh hstore hnot
      have hnotCondition : ¬ Term.Mentions ghost condition := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hnotBody : ¬ Term.Mentions ghost body := by
        intro hmention
        exact hnot (by simp [Term.Mentions, hmention])
      have hfreshInv : Env.TypeNameFresh (envInv.erase ghost) ghost := by
        simpa [Env.eraseMany] using
          hnameFresh [ghost] ghost (by simpa [Env.eraseMany] using hfresh)
            hnotCondition hnotBody
      have hnameFreshErased :
          LoopInvariantNameFresh (env₁.erase ghost) (envInv.erase ghost)
            condition body := by
        intro erased checked hentryFresh hcheckedCondition hcheckedBody
        have h :=
          hnameFresh (ghost :: erased) checked
            (by simpa [Env.eraseMany] using hentryFresh)
            hcheckedCondition hcheckedBody
        simpa [Env.eraseMany] using h
      rcases ihEntryCondition hfresh hstore hnotCondition with
        ⟨hentryConditionErased, hfreshEntryCond, _hboolFresh⟩
      rcases ihEntryBody hfreshEntryCond hstore hnotBody with
        ⟨hentryBodyErased, _hfreshEntryBody, _hbodyEntryFresh⟩
      rcases ihCondition hfreshInv hstore hnotCondition with
        ⟨hconditionErased, hfreshCond, _hboolFresh2⟩
      rcases ihBody hfreshCond hstore hnotBody with
        ⟨hbodyErased, hfreshBody, hbodyFresh⟩
      have hdropErased :
          (env₃.erase ghost).dropLifetime bodyLifetime =
            envBack.erase ghost := by
        rw [← Env.dropLifetime_erase env₃ ghost bodyLifetime]
        simpa [hdrop]
      exact ⟨TermTyping.whileLoop hchild
        (EnvJoin.erase_ghost hjoin)
        (EnvJoinSameShape.erase_ghost hsameEntry)
        (EnvJoinSameShape.erase_ghost hsameBack)
        (ContainedBorrowsWellFormed.erase_ghost hcontained hfreshInv)
        (Coherent.erase_ghost hcoherent hfreshInv)
        (Linearizable.erase_ghost hlinear)
        (BorrowSafeEnv.erase hborrowSafe)
        hnameFreshErased
        hconditionErased hbodyErased
        (WellFormedTy.erase_ghost hbodyWell hfreshBody hbodyFresh)
        hdropErased hentryConditionErased hentryBodyErased,
                hfreshCond, by simp [Ty.allVars]⟩)
    (by
      intro env₁ env₂ typing lifetime singletonTerm ty hterm ih
        hfresh hstore hnot
      have hnotTerm : ¬ Term.Mentions ghost singletonTerm := by
        intro hmention
        exact hnot (by simp [TermList.Mentions, hmention])
      rcases ih hfresh hstore hnotTerm with
        ⟨htermErased, hfreshOut, htyFresh⟩
      exact ⟨TermListTyping.singleton htermErased, hfreshOut, htyFresh⟩)
    (by
      intro env₁ env₂ env₃ typing lifetime head rest headTy finalTy
        hhead hrest ihHead ihRest hfresh hstore hnot
      have hnotHead : ¬ Term.Mentions ghost head := by
        intro hmention
        exact hnot (by simp [TermList.Mentions, hmention])
      have hnotRest : ¬ TermList.Mentions ghost rest := by
        intro hmention
        exact hnot (by simp [TermList.Mentions, hmention])
      rcases ihHead hfresh hstore hnotHead with
        ⟨hheadErased, hfreshHead, _hheadFresh⟩
      rcases ihRest hfreshHead hstore hnotRest with
        ⟨hrestErased, hfreshRest, hfinalFresh⟩
      exact ⟨TermListTyping.cons hheadErased hrestErased,
        hfreshRest, hfinalFresh⟩)
    htyping

theorem TermTyping.erase_ghost {env envGhost : Env} {ghost : Name}
    {ghostSlot : EnvSlot} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    env.fresh ghost →
    Env.TypeNameFresh env ghost →
    ghost ∉ PartialTy.vars ghostSlot.ty →
    StoreTyping.TypeNameFresh typing ghost →
    ¬ Term.Mentions ghost term →
    TermTyping (env.update ghost ghostSlot) typing lifetime term ty envGhost →
    TermTyping env typing lifetime term ty (envGhost.erase ghost) := by
  intro hfresh htypeFresh _hslotFresh hstoreFresh hnot htyping
  have hinput :
      Env.TypeNameFresh ((env.update ghost ghostSlot).erase ghost) ghost := by
    simpa [Env.erase_update_same_of_fresh hfresh] using htypeFresh
  rcases TermTyping.erase_ghost_pack htyping hinput hstoreFresh hnot with
    ⟨herased, _hfreshOut, _htyFresh⟩
  simpa [Env.erase_update_same_of_fresh hfresh] using herased

end Paper
end LwRust
