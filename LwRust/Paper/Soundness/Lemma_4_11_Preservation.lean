import LwRust.Paper.Soundness.Helpers.BorrowSafety

/-!
# Lemma 4.11 (Preservation)

Fresh Phase D3 rebuild.  The old multi-target preservation development has
been moved to `Lemma_4_11_Preservation.lean.reference` for consultation while
this file is rebuilt around the single-target typing rules.
-/

namespace LwRust
namespace Paper

open Core

/-- Source terms carry no runtime-owned values, so any valid runtime context
gives a valid runtime package for the source subterm itself. -/
theorem validRuntimeState_of_sourceTerm {store : ProgramStore} {context term : Term} :
    SourceTerm term →
    ValidRuntimeState store context →
    ValidRuntimeState store term := by
  intro hsource hvalid
  exact ⟨⟨hvalid.1.1, sourceTerm_validTerm hsource, by
      intro owned hmem
      have hnone := sourceTerm_no_owningLocations hsource
      rw [hnone] at hmem
      cases hmem⟩,
    hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1,
    sourceTerm_ownerTargetsHeap hsource⟩

theorem UpdateAtPath.lifetimesPreserved {env₁ env₂ : Env}
    {path : List Unit} {old : PartialTy} {ty : Ty} {updated : PartialTy} :
    UpdateAtPath env₁ path old ty env₂ updated →
    EnvLifetimesPreserved env₁ env₂ := by
  intro hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun _path _old _ty result _updated _ =>
      EnvLifetimesPreserved env₁ result)
    (motive_2 := fun _lv _ty result _ =>
      EnvLifetimesPreserved env₁ result)
    (fun {old ty} =>
      by
        intro x resultSlot hresult
        exact ⟨resultSlot, hresult, rfl⟩)
    (fun _hinner ih => ih)
    (fun _hinner ih => ih)
    (fun _hwrite ih => ih)
    (fun hslot _hupdate ih =>
      EnvLifetimesPreserved.update_from_source_slot ih hslot)
    hupdate

theorem EnvWrite.lifetimesPreserved {env result : Env}
    {lv : LVal} {ty : Ty} :
    EnvWrite env lv ty result →
    EnvLifetimesPreserved env result := by
  intro hwrite
  exact EnvWrite.rec
    (motive_1 := fun _path _old _ty result _updated _ =>
      EnvLifetimesPreserved env result)
    (motive_2 := fun _lv _ty result _ =>
      EnvLifetimesPreserved env result)
    (fun {old ty} =>
      by
        intro x resultSlot hresult
        exact ⟨resultSlot, hresult, rfl⟩)
    (fun _hinner ih => ih)
    (fun _hinner ih => ih)
    (fun _hwrite ih => ih)
    (fun hslot _hupdate ih =>
      EnvLifetimesPreserved.update_from_source_slot ih hslot)
    hwrite

theorem UpdateAtPath.lifetimesSurvive {env₁ env₂ : Env}
    {path : List Unit} {old : PartialTy} {ty : Ty} {updated : PartialTy} :
    UpdateAtPath env₁ path old ty env₂ updated →
    ∀ x sourceSlot,
      env₁.slotAt x = some sourceSlot →
      ∃ resultSlot,
        env₂.slotAt x = some resultSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime := by
  intro hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun _path _old _ty result _updated _ =>
      ∀ x sourceSlot,
        env₁.slotAt x = some sourceSlot →
        ∃ resultSlot,
          result.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
    (motive_2 := fun _lv _ty result _ =>
      ∀ x sourceSlot,
        env₁.slotAt x = some sourceSlot →
        ∃ resultSlot,
          result.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
    (by
      intro _old _ty x sourceSlot hsource
      exact ⟨sourceSlot, hsource, rfl⟩)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih x sourceSlot hsource
      exact ih x sourceSlot hsource)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih x sourceSlot hsource
      exact ih x sourceSlot hsource)
    (by
      intro _env₂ _path _target _ty _hwrite ih x sourceSlot hsource
      exact ih x sourceSlot hsource)
    (by
      intro _env₂ lv slot ty updatedTy hslot _hupdate ih x sourceSlot hsource
      by_cases hx : x = LVal.base lv
      · subst hx
        have hsourceEq : sourceSlot = slot := by
          exact (Option.some.inj (hsource.symm.trans hslot))
        exact ⟨{ slot with ty := updatedTy },
          by simp [Env.update],
          by simp [hsourceEq]⟩
      · rcases ih x sourceSlot hsource with
          ⟨midSlot, hmidSlot, hlife⟩
        exact ⟨midSlot, by
            simpa [Env.update, hx] using hmidSlot,
          hlife⟩)
    hupdate

theorem EnvWrite.lifetimesSurvive {env result : Env}
    {lv : LVal} {ty : Ty} :
    EnvWrite env lv ty result →
    ∀ x sourceSlot,
      env.slotAt x = some sourceSlot →
      ∃ resultSlot,
        result.slotAt x = some resultSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime := by
  intro hwrite
  exact EnvWrite.rec
    (motive_1 := fun _path _old _ty result _updated _ =>
      ∀ x sourceSlot,
        env.slotAt x = some sourceSlot →
        ∃ resultSlot,
          result.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
    (motive_2 := fun _lv _ty result _ =>
      ∀ x sourceSlot,
        env.slotAt x = some sourceSlot →
        ∃ resultSlot,
          result.slotAt x = some resultSlot ∧
            sourceSlot.lifetime = resultSlot.lifetime)
    (by
      intro _old _ty x sourceSlot hsource
      exact ⟨sourceSlot, hsource, rfl⟩)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih x sourceSlot hsource
      exact ih x sourceSlot hsource)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih x sourceSlot hsource
      exact ih x sourceSlot hsource)
    (by
      intro _env₂ _path _target _ty _hwrite ih x sourceSlot hsource
      exact ih x sourceSlot hsource)
    (by
      intro _env₂ lv slot ty updatedTy hslot _hupdate ih x sourceSlot hsource
      by_cases hx : x = LVal.base lv
      · subst hx
        have hsourceEq : sourceSlot = slot := by
          exact (Option.some.inj (hsource.symm.trans hslot))
        exact ⟨{ slot with ty := updatedTy },
          by simp [Env.update],
          by simp [hsourceEq]⟩
      · rcases ih x sourceSlot hsource with
          ⟨midSlot, hmidSlot, hlife⟩
        exact ⟨midSlot, by
            simpa [Env.update, hx] using hmidSlot,
          hlife⟩)
    hwrite

theorem EnvSlotsOutlive.write {env result : Env} {lv : LVal}
    {ty : Ty} {current : Lifetime} :
    EnvWrite env lv ty result →
    EnvSlotsOutlive env current →
    EnvSlotsOutlive result current := by
  intro hwrite houtlives
  exact EnvSlotsOutlive.of_lifetimesPreserved
    (EnvWrite.lifetimesPreserved hwrite) houtlives

theorem LValBaseOutlives.write {env result : Env} {lv target : LVal}
    {ty : Ty} {lifetime : Lifetime} :
    EnvWrite env lv ty result →
    LValBaseOutlives env target lifetime →
    LValBaseOutlives result target lifetime := by
  intro hwrite hbase
  rcases hbase with ⟨sourceSlot, hsourceSlot, houtlives⟩
  rcases EnvWrite.lifetimesSurvive hwrite (LVal.base target) sourceSlot
      hsourceSlot with
    ⟨resultSlot, hresultSlot, hlife⟩
  exact ⟨resultSlot, hresultSlot, by
    rw [← hlife]
    exact houtlives⟩

theorem LValBaseOutlives.of_write {env result : Env} {lv target : LVal}
    {ty : Ty} {lifetime : Lifetime} :
    EnvWrite env lv ty result →
    LValBaseOutlives result target lifetime →
    LValBaseOutlives env target lifetime := by
  intro hwrite hbase
  rcases hbase with ⟨resultSlot, hresultSlot, houtlives⟩
  rcases EnvWrite.lifetimesPreserved hwrite (LVal.base target) resultSlot
      hresultSlot with
    ⟨sourceSlot, hsourceSlot, hlife⟩
  exact ⟨sourceSlot, hsourceSlot, by
    rw [hlife]
    exact houtlives⟩

theorem Strike.contains_borrow {path : Path} {source struck : PartialTy}
    {mutable : Bool} {target : LVal} :
    Strike path source struck →
    PartialTyContains struck (.borrow mutable target) →
    PartialTyContains source (.borrow mutable target) := by
  intro hstrike hcontains
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      subst hstrike
      cases hcontains
  | cons _ tail ih =>
      cases source with
      | ty sourceTy =>
          cases sourceTy <;> cases struck <;> simp [Strike] at hstrike
          rename_i inner struckInner
          cases hcontains with
          | box hinner =>
              exact PartialTyContains.tyBox (ih hstrike hinner)
      | box inner =>
          cases struck <;> simp [Strike] at hstrike
          rename_i struckInner
          cases hcontains with
          | box hinner =>
              exact PartialTyContains.box (ih hstrike hinner)
      | undef shape =>
          cases struck <;> simp [Strike] at hstrike

theorem Strike.vars_subset {path : Path} {source struck : PartialTy} :
    Strike path source struck →
    ∀ v, v ∈ PartialTy.vars struck → v ∈ PartialTy.vars source := by
  intro hstrike
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      intro v hv
      simp [PartialTy.vars] at hv
  | cons _ tail ih =>
      cases source with
      | ty sourceTy =>
          cases sourceTy <;> cases struck <;> simp [Strike] at hstrike
          intro v hv
          exact ih hstrike v hv
      | box inner =>
          cases struck <;> simp [Strike] at hstrike
          intro v hv
          exact ih hstrike v hv
      | undef shape =>
          cases struck <;> simp [Strike] at hstrike

theorem PartialTyContains.partialTyRebox_borrow_inv {updated : PartialTy}
    {mutable : Bool} {target : LVal} :
    PartialTyContains (partialTyRebox updated) (.borrow mutable target) →
    PartialTyContains updated (.borrow mutable target) := by
  intro hcontains
  cases updated with
  | ty inner =>
      cases hcontains with
      | tyBox hinner => exact hinner
  | box inner =>
      cases hcontains with
      | box hinner => exact hinner
  | undef shape =>
      cases hcontains with
      | box hinner => exact hinner

theorem UpdateAtPath.contains_borrow {env₁ env₂ : Env} {path : List Unit}
    {old updated : PartialTy} {rhsTy : Ty} {mutable : Bool}
    {target : LVal} :
    UpdateAtPath env₁ path old rhsTy env₂ updated →
    PartialTyContains updated (.borrow mutable target) →
    PartialTyContains (.ty rhsTy) (.borrow mutable target) ∨
      PartialTyContains old (.borrow mutable target) := by
  intro hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun _path old rhsTy _env₂ updated _ =>
      PartialTyContains updated (.borrow mutable target) →
      PartialTyContains (.ty rhsTy) (.borrow mutable target) ∨
        PartialTyContains old (.borrow mutable target))
    (motive_2 := fun _lv _rhsTy _env₂ _ => True)
    (by
      intro old ty hcontains
      exact Or.inl hcontains)
    (by
      intro env₂ path inner updatedInner ty _hinner ih hcontains
      cases hcontains with
      | box hinner =>
          exact (ih hinner).elim Or.inl
            (fun hold => Or.inr (PartialTyContains.box hold)))
    (by
      intro env₂ path inner updatedInner ty _hinner ih hcontains
      have hinnerContains :
          PartialTyContains _ (.borrow mutable target) :=
        PartialTyContains.partialTyRebox_borrow_inv hcontains
      exact (ih hinnerContains).elim Or.inl
        (fun hold => Or.inr (PartialTyContains.tyBox hold)))
    (by
      intro env₂ path writeTarget ty _hwrite _ih hcontains
      exact Or.inr hcontains)
    (by
      intro env₂ lv slot ty updatedTy _hslot _hupdate _ih
      trivial)
    hupdate

theorem EnvMove.contains_borrow_source {env moved : Env} {lv : LVal}
    {x : Name} {slot : EnvSlot} {mutable : Bool} {target : LVal} :
    EnvMove env lv moved →
    moved.slotAt x = some slot →
    moved ⊢ x ↝ (.borrow mutable target) →
    env ⊢ x ↝ (.borrow mutable target) := by
  intro hmove hslot hcontains
  rcases hmove with ⟨sourceSlot, struck, hsourceSlot, hstrike, hmoved⟩
  subst hmoved
  by_cases hx : x = LVal.base lv
  · subst hx
    have hslotEq : slot = { sourceSlot with ty := struck } := by
      exact (Option.some.inj (by simpa [Env.update] using hslot)).symm
    subst hslotEq
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hcontainedEq : containedSlot = { sourceSlot with ty := struck } := by
      exact (Option.some.inj (by simpa [Env.update] using hcontainedSlot)).symm
    subst hcontainedEq
    exact ⟨sourceSlot, hsourceSlot,
      Strike.contains_borrow hstrike hcontainsTy⟩
  · have hslotOld : env.slotAt x = some slot := by
      simpa [Env.update, hx] using hslot
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hcontainedOld : env.slotAt x = some containedSlot := by
      simpa [Env.update, hx] using hcontainedSlot
    exact ⟨containedSlot, hcontainedOld, hcontainsTy⟩

theorem UpdateAtPath.contains_borrow_result {env₁ env₂ : Env}
    {path : List Unit} {old updated : PartialTy} {rhsTy : Ty}
    {x : Name} {mutable : Bool} {target : LVal} :
    UpdateAtPath env₁ path old rhsTy env₂ updated →
    env₂ ⊢ x ↝ (.borrow mutable target) →
    PartialTyContains (.ty rhsTy) (.borrow mutable target) ∨
      env₁ ⊢ x ↝ (.borrow mutable target) := by
  intro hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun _path _old rhsTy result _updated _ =>
      result ⊢ x ↝ (.borrow mutable target) →
      PartialTyContains (.ty rhsTy) (.borrow mutable target) ∨
        env₁ ⊢ x ↝ (.borrow mutable target))
    (motive_2 := fun _lv rhsTy result _ =>
      result ⊢ x ↝ (.borrow mutable target) →
      PartialTyContains (.ty rhsTy) (.borrow mutable target) ∨
        env₁ ⊢ x ↝ (.borrow mutable target))
    (by
      intro _old _ty hcontains
      exact Or.inr hcontains)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih hcontains
      exact ih hcontains)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih hcontains
      exact ih hcontains)
    (by
      intro _env₂ _path _writeTarget _ty _hwrite ih hcontains
      exact ih hcontains)
    (by
      intro _env₂ lv slot ty updatedTy hslot hupdate ih hcontains
      rcases hcontains with ⟨resultSlot, hresultSlot, hcontainsTy⟩
      by_cases hx : x = LVal.base lv
      · subst hx
        have hresultSlotEq :
            resultSlot = { slot with ty := updatedTy } := by
          exact (Option.some.inj (by simpa [Env.update] using hresultSlot)).symm
        subst hresultSlotEq
        rcases UpdateAtPath.contains_borrow hupdate hcontainsTy with
          hcontainsRhs | hcontainsOld
        · exact Or.inl hcontainsRhs
        · exact Or.inr ⟨slot, hslot, hcontainsOld⟩
      · have henv₂Contains :
            _env₂ ⊢ x ↝ (.borrow mutable target) := by
          exact ⟨resultSlot, by
              simpa [Env.update, hx] using hresultSlot,
            hcontainsTy⟩
        exact ih henv₂Contains)
    hupdate

theorem EnvWrite.contains_borrow_source {env result : Env} {lv : LVal}
    {rhsTy : Ty} {x : Name} {mutable : Bool} {target : LVal} :
    EnvWrite env lv rhsTy result →
    result ⊢ x ↝ (.borrow mutable target) →
    PartialTyContains (.ty rhsTy) (.borrow mutable target) ∨
      env ⊢ x ↝ (.borrow mutable target) := by
  intro hwrite hcontains
  exact EnvWrite.rec
    (motive_1 := fun _path _old rhsTy result _updated _ =>
      result ⊢ x ↝ (.borrow mutable target) →
      PartialTyContains (.ty rhsTy) (.borrow mutable target) ∨
        env ⊢ x ↝ (.borrow mutable target))
    (motive_2 := fun _lv rhsTy result _ =>
      result ⊢ x ↝ (.borrow mutable target) →
      PartialTyContains (.ty rhsTy) (.borrow mutable target) ∨
        env ⊢ x ↝ (.borrow mutable target))
    (by
      intro _old _ty hcontains
      exact Or.inr hcontains)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih hcontains
      exact ih hcontains)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih hcontains
      exact ih hcontains)
    (by
      intro _env₂ _path _writeTarget _ty _hwrite ih hcontains
      exact ih hcontains)
    (by
      intro _env₂ lv slot ty updatedTy hslot hupdate ih hcontains
      rcases hcontains with ⟨resultSlot, hresultSlot, hcontainsTy⟩
      by_cases hx : x = LVal.base lv
      · subst hx
        have hresultSlotEq :
            resultSlot = { slot with ty := updatedTy } := by
          exact (Option.some.inj (by simpa [Env.update] using hresultSlot)).symm
        subst hresultSlotEq
        rcases UpdateAtPath.contains_borrow hupdate hcontainsTy with
          hcontainsRhs | hcontainsOld
        · exact Or.inl hcontainsRhs
        · exact Or.inr ⟨slot, hslot, hcontainsOld⟩
      · have henv₂Contains :
            _env₂ ⊢ x ↝ (.borrow mutable target) := by
          exact ⟨resultSlot, by
              simpa [Env.update, hx] using hresultSlot,
            hcontainsTy⟩
        exact ih henv₂Contains)
    hwrite hcontains

theorem EnvWrite.var_inv {env result : Env} {x : Name} {rhsTy : Ty} :
    EnvWrite env (.var x) rhsTy result →
    ∃ slot,
      env.slotAt x = some slot ∧
        result = env.update x { slot with ty := .ty rhsTy } := by
  intro hwrite
  cases hwrite with
  | intro hslot hupdate =>
      simp [LVal.base, LVal.path] at hslot hupdate
      cases hupdate with
      | strong =>
          exact ⟨_, hslot, rfl⟩

theorem WriteProhibited.of_contains_conflict {env : Env} {x : Name}
    {mutable : Bool} {target lv : LVal} :
    env ⊢ x ↝ (.borrow mutable target) →
    target ⋈ lv →
    WriteProhibited env lv := by
  intro hcontains hconflict
  cases mutable with
  | false =>
      exact Or.inr ⟨x, target, hcontains, hconflict⟩
  | true =>
      exact Or.inl ⟨x, target, hcontains, hconflict⟩

theorem not_pathConflicts_of_not_writeProhibited_contains {env : Env}
    {x : Name} {mutable : Bool} {target lv : LVal} :
    ¬ WriteProhibited env lv →
    env ⊢ x ↝ (.borrow mutable target) →
    ¬ target ⋈ lv := by
  intro hnotWrite hcontains hconflict
  exact hnotWrite (WriteProhibited.of_contains_conflict hcontains hconflict)

theorem BorrowSafeEnv.move {env moved : Env} {lv : LVal} :
    BorrowSafeEnv env →
    EnvMove env lv moved →
    BorrowSafeEnv moved := by
  intro hsafe hmove x y mutable targetMutable targetOther
    hcontainsMutable hcontainsOther hconflict
  rcases hcontainsMutable with ⟨slotX, hslotX, hcontainsMutableTy⟩
  rcases hcontainsOther with ⟨slotY, hslotY, hcontainsOtherTy⟩
  exact hsafe x y mutable targetMutable targetOther
    (EnvMove.contains_borrow_source hmove hslotX
      ⟨slotX, hslotX, hcontainsMutableTy⟩)
    (EnvMove.contains_borrow_source hmove hslotY
      ⟨slotY, hslotY, hcontainsOtherTy⟩)
    hconflict

theorem LValTyping.contains_borrow {env : Env} :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {mutable : Bool} {target : LVal},
      LValTyping env lv partialTy lifetime →
      PartialTyContains partialTy (.borrow mutable target) →
      ∃ x, env ⊢ x ↝ (.borrow mutable target) := by
  intro lv partialTy lifetime mutable target htyping
  induction htyping with
  | var hslot =>
      intro hcontains
      exact ⟨_, ⟨_, hslot, hcontains⟩⟩
  | box _ ih =>
      intro hcontains
      exact ih (PartialTyContains.box hcontains)
  | boxFull _ ih =>
      intro hcontains
      exact ih (PartialTyContains.tyBox hcontains)
  | borrow _ _ ihBorrow ihTarget =>
      intro hcontains
      exact ihTarget hcontains

theorem LValTyping.move_to_source_of_no_conflicts {env moved : Env}
    {movedLv : LVal} :
    EnvMove env movedLv moved →
    (∀ x mutable target,
      moved ⊢ x ↝ (.borrow mutable target) →
      ¬ target ⋈ movedLv) →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      ¬ lv ⋈ movedLv →
      LValTyping moved lv partialTy lifetime →
      LValTyping env lv partialTy lifetime := by
  intro hmove hnoConflicts lv partialTy lifetime hnotConflict htyping
  induction htyping with
  | var hslot =>
      rename_i x slot
      rcases hmove with ⟨sourceSlot, struck, hsourceSlot, _hstrike, hmoved⟩
      have hx : x ≠ LVal.base movedLv := by
        intro hbase
        exact hnotConflict hbase
      have hslotOld : env.slotAt x = some slot := by
        simpa [hmoved, Env.update, hx] using hslot
      exact LValTyping.var hslotOld
  | box _ ih =>
      exact LValTyping.box (ih hnotConflict)
  | boxFull _ ih =>
      exact LValTyping.boxFull (ih hnotConflict)
  | borrow hborrow htarget ihBorrow ihTarget =>
      rename_i lv target mutable borrowLifetime targetLifetime targetTy
      have hborrowSource :
          LValTyping env lv (.ty (.borrow mutable target)) borrowLifetime :=
        ihBorrow hnotConflict
      rcases LValTyping.contains_borrow hborrow PartialTyContains.here with
        ⟨x, hcontains⟩
      have htargetNoConflict : ¬ target ⋈ movedLv :=
        hnoConflicts x mutable target hcontains
      exact LValTyping.borrow hborrowSource (ihTarget htargetNoConflict)

theorem LValTyping.deterministic {env : Env} {lv : LVal} :
    ∀ {left : PartialTy} {leftLifetime : Lifetime}
      {right : PartialTy} {rightLifetime : Lifetime},
      LValTyping env lv left leftLifetime →
      LValTyping env lv right rightLifetime →
      left = right ∧ leftLifetime = rightLifetime := by
  intro left leftLifetime right rightLifetime hleft
  induction hleft generalizing right rightLifetime with
  | var hslot =>
      intro hright
      cases hright with
      | var hslotRight =>
          rw [hslot] at hslotRight
          have hslotEq := Option.some.inj hslotRight
          cases hslotEq
          exact ⟨rfl, rfl⟩
  | box _ ih =>
      intro hright
      cases hright with
      | box hsourceRight =>
          rcases ih hsourceRight with ⟨hty, hlife⟩
          cases hty
          exact ⟨rfl, hlife⟩
      | boxFull hsourceRight =>
          rcases ih hsourceRight with ⟨hty, _hlife⟩
          cases hty
      | borrow hborrowRight _htargetRight =>
          rcases ih hborrowRight with ⟨hty, _hlife⟩
          cases hty
  | boxFull _ ih =>
      intro hright
      cases hright with
      | box hsourceRight =>
          rcases ih hsourceRight with ⟨hty, _hlife⟩
          cases hty
      | boxFull hsourceRight =>
          rcases ih hsourceRight with ⟨hty, hlife⟩
          cases hty
          exact ⟨rfl, hlife⟩
      | borrow hborrowRight _htargetRight =>
          rcases ih hborrowRight with ⟨hty, _hlife⟩
          cases hty
  | borrow hborrow htarget ihBorrow ihTarget =>
      intro hright
      cases hright with
      | box hsourceRight =>
          rcases ihBorrow hsourceRight with ⟨hty, _hlife⟩
          cases hty
      | boxFull hsourceRight =>
          rcases ihBorrow hsourceRight with ⟨hty, _hlife⟩
          cases hty
      | borrow hborrowRight htargetRight =>
          rcases ihBorrow hborrowRight with ⟨hborrowTy, _hborrowLife⟩
          cases hborrowTy
          rcases ihTarget htargetRight with ⟨htargetTy, htargetLife⟩
          cases htargetTy
          exact ⟨rfl, htargetLife⟩

theorem ContainedBorrowsWellFormedWhenInitialized.move {env moved : Env}
    {lv : LVal} :
    ContainedBorrowsWellFormedWhenInitialized env →
    EnvMove env lv moved →
    ¬ WriteProhibited env lv →
    ContainedBorrowsWellFormedWhenInitialized moved := by
  intro hcontained hmove hnotWrite x slot mutable target hslot hcontainsMoved
  have hcontainsSource :
      env ⊢ x ↝ (.borrow mutable target) :=
    EnvMove.contains_borrow_source hmove hslot hcontainsMoved
  rcases hcontainsSource with
    ⟨sourceSlot, hsourceSlot, hsourceContainsTy⟩
  have htargetOld :
      BorrowTargetsWellFormedInSlotWhenInitialized
        env sourceSlot.lifetime target :=
    hcontained x sourceSlot mutable target hsourceSlot
      ⟨sourceSlot, hsourceSlot, hsourceContainsTy⟩
  have hlife : sourceSlot.lifetime = slot.lifetime := by
    rcases EnvMove.lifetimesSurvive hmove x slot hslot with
      ⟨preservedSlot, hpreservedSlot, hpreservedLife⟩
    have hslotEq : preservedSlot = sourceSlot := by
      rw [hsourceSlot] at hpreservedSlot
      exact (Option.some.inj hpreservedSlot).symm
    simpa [hslotEq] using hpreservedLife
  have htargetNoConflict : ¬ target ⋈ lv :=
    not_pathConflicts_of_not_writeProhibited_contains hnotWrite
      ⟨sourceSlot, hsourceSlot, hsourceContainsTy⟩
  rcases htargetOld with ⟨hbaseOld, hinitializedOld⟩
  have hbaseMovedSource :
      LValBaseOutlives moved target sourceSlot.lifetime :=
    LValBaseOutlives.move_of_not_pathConflicts hmove htargetNoConflict hbaseOld
  have hbaseMoved :
      LValBaseOutlives moved target slot.lifetime := by
    simpa [hlife] using hbaseMovedSource
  refine ⟨hbaseMoved, ?_⟩
  intro hinitMoved
  rcases hinitMoved with ⟨targetTy, targetLifetime, htypingMoved⟩
  have hnoConflicts :
      ∀ y containedMutable containedTarget,
        moved ⊢ y ↝ (.borrow containedMutable containedTarget) →
        ¬ containedTarget ⋈ lv := by
    intro y containedMutable containedTarget hcontains
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hsource :
        env ⊢ y ↝ (.borrow containedMutable containedTarget) :=
      EnvMove.contains_borrow_source hmove hcontainedSlot
        ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite hsource
  have htypingSource :
      LValTyping env target (.ty targetTy) targetLifetime :=
    LValTyping.move_to_source_of_no_conflicts hmove hnoConflicts
      htargetNoConflict htypingMoved
  rcases hinitializedOld ⟨targetTy, targetLifetime, htypingSource⟩ with
    ⟨oldTargetTy, oldTargetLifetime, htypingOld, houtlivesOld, _hbaseOld'⟩
  rcases LValTyping.deterministic htypingOld htypingSource with
    ⟨hpartialEq, hlifetimeEq⟩
  cases hpartialEq
  cases hlifetimeEq
  exact ⟨targetTy, targetLifetime, htypingMoved, by
      simpa [hlife] using houtlivesOld,
    hbaseMoved⟩

theorem WellFormedEnvWhenInitialized.move {env moved : Env}
    {lv : LVal} {current : Lifetime} :
    WellFormedEnvWhenInitialized env current →
    EnvMove env lv moved →
    ¬ WriteProhibited env lv →
    WellFormedEnvWhenInitialized moved current := by
  intro hwell hmove hnotWrite
  exact ⟨ContainedBorrowsWellFormedWhenInitialized.move hwell.1 hmove hnotWrite,
    EnvSlotsOutlive.move hmove hwell.2⟩

theorem PartialTyBorrowsWellFormedInSlotWhenInitialized.box_inv {env : Env}
    {slotLifetime : Lifetime} {inner : PartialTy} :
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime (.box inner) →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime inner := by
  intro hbox mutable target hcontains
  exact hbox (PartialTyContains.box hcontains)

theorem wellFormedTyWhenInitialized_of_partialTyBorrows
    {env : Env} {ty : Ty} {lifetime : Lifetime} :
    PartialTyBorrowsWellFormedInSlotWhenInitialized env lifetime (.ty ty) →
    WellFormedTyWhenInitialized env ty lifetime := by
  exact Ty.rec
    (motive_1 := fun ty =>
      PartialTyBorrowsWellFormedInSlotWhenInitialized env lifetime (.ty ty) →
      WellFormedTyWhenInitialized env ty lifetime)
    (motive_2 := fun _partialTy => True)
    (by
      intro _hborrows
      exact WellFormedTyWhenInitialized.unit)
    (by
      intro _hborrows
      exact WellFormedTyWhenInitialized.int)
    (by
      intro mutable target hborrows
      exact WellFormedTyWhenInitialized.borrow
        (hborrows PartialTyContains.here))
    (by
      intro inner ih hborrows
      exact WellFormedTyWhenInitialized.box
        (ih (by
          intro mutable target hcontains
          exact hborrows (PartialTyContains.tyBox hcontains))))
    (by intro _type _ih; trivial)
    (by intro _inner _ih; trivial)
    (by intro _shape _ih; trivial)
    ty

theorem LValTyping.partialTyBorrowsWellFormedInSlotWhenInitialized
    {env : Env} :
    ContainedBorrowsWellFormedWhenInitialized env →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
      PartialTyBorrowsWellFormedInSlotWhenInitialized env lifetime partialTy := by
  intro hcontained lv partialTy lifetime htyping
  induction htyping with
  | var hslot =>
      intro mutable target hcontains
      exact hcontained _ _ mutable target hslot ⟨_, hslot, hcontains⟩
  | box _ ih =>
      exact PartialTyBorrowsWellFormedInSlotWhenInitialized.box_inv ih
  | boxFull _ ih =>
      intro mutable target hcontains
      exact ih (PartialTyContains.tyBox hcontains)
  | borrow _ _ _ ihTarget =>
      exact ihTarget

theorem LValTyping.wellFormedTyWhenInitialized {env : Env}
    {current : Lifetime} {lv : LVal} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env current →
    LValTyping env lv (.ty ty) lifetime →
    WellFormedTyWhenInitialized env ty current := by
  intro hwell htyping
  have hselected :
      PartialTyBorrowsWellFormedInSlotWhenInitialized env lifetime (.ty ty) :=
    LValTyping.partialTyBorrowsWellFormedInSlotWhenInitialized hwell.1 htyping
  have hty : WellFormedTyWhenInitialized env ty lifetime :=
    wellFormedTyWhenInitialized_of_partialTyBorrows hselected
  exact WellFormedTyWhenInitialized.weaken hty
    (LValTyping.lifetime_outlives_one hwell.2 htyping)

theorem ValueTyping.wellFormedTyWhenInitialized_of_sourceValue
    {env : Env} {typing : StoreTyping} {value : Value} {ty : Ty}
    {lifetime : Lifetime} :
    SourceValue value →
    ValueTyping typing value ty →
    WellFormedTyWhenInitialized env ty lifetime := by
  intro hsource htyping
  cases htyping with
  | unit =>
      exact WellFormedTyWhenInitialized.unit
  | int =>
      exact WellFormedTyWhenInitialized.int
  | ref _hlookup =>
      cases hsource

namespace RuntimeFrame

theorem loc_erase_of_not_locReads {store : ProgramStore}
    {erased : Location} :
    ∀ {lv : LVal} {location : Location},
      store.loc lv = some location →
      (∀ mid, LocReads store lv mid → mid ≠ erased) →
      (store.erase erased).loc lv = some location := by
  intro lv
  induction lv with
  | var x =>
      intro location hloc _hreads
      simpa [ProgramStore.loc] using hloc
  | deref lv ih =>
      intro location hloc hreads
      cases hsource : store.loc lv with
      | none =>
          simp [ProgramStore.loc, hsource] at hloc
      | some source =>
          have hsourceNe : source ≠ erased :=
            hreads source (LocReads.here hsource)
          have hsource' : (store.erase erased).loc lv = some source := by
            refine ih hsource ?_
            intro mid hmid
            exact hreads mid (LocReads.there hmid)
          have hslotEq :
              (store.erase erased).slotAt source = store.slotAt source := by
            rw [ProgramStore.erase_slotAt_ne]
            exact hsourceNe
          have hlocEq :
              (store.erase erased).loc (.deref lv) =
                store.loc (.deref lv) := by
            simp [ProgramStore.loc, hsource, hsource', hslotEq]
          rw [hlocEq]
          exact hloc

theorem validPartialValueSkeleton_erase_of_not_owner_reaches
    {store : ProgramStore} {erased : Location} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValueSkeleton store v ty →
      (∀ location, OwnerReaches store v ty location → location ≠ erased) →
      ValidPartialValueSkeleton (store.erase erased) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit =>
      intro _howners
      exact ValidPartialValueSkeleton.unit
  | int =>
      intro _howners
      exact ValidPartialValueSkeleton.int
  | undef =>
      intro _howners
      exact ValidPartialValueSkeleton.undef
  | borrow =>
      intro _howners
      exact ValidPartialValueSkeleton.borrow
  | undefOf hinner hstrength ih =>
      intro howners
      exact ValidPartialValueSkeleton.undefOf
        (ih (fun location hreach =>
          howners location (OwnerReaches.undefOf hinner hstrength hreach)))
        hstrength
  | box hslot _hinner ih =>
      intro howners
      rename_i location slot inner
      have hlocNe : location ≠ erased :=
        howners location (OwnerReaches.boxHere hslot)
      refine ValidPartialValueSkeleton.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun reached hreach =>
          howners reached (OwnerReaches.boxInner hslot hreach))
  | boxFull hslot _hinner ih =>
      intro howners
      rename_i location slot ty
      have hlocNe : location ≠ erased :=
        howners location (OwnerReaches.boxFullHere hslot)
      refine ValidPartialValueSkeleton.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun reached hreach =>
          howners reached (OwnerReaches.boxFullInner hslot hreach))

theorem validPartialValue_erase_of_not_reaches
    {store : ProgramStore} {erased : Location} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValue store v ty →
      (∀ location, Reaches store v ty location → location ≠ erased) →
      ValidPartialValue (store.erase erased) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit =>
      intro _hreach
      exact ValidPartialValue.unit
  | int =>
      intro _hreach
      exact ValidPartialValue.int
  | undef =>
      intro _hreach
      exact ValidPartialValue.undef
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValue.undefOf
        (validPartialValueSkeleton_erase_of_not_owner_reaches hinner
          (fun location howner =>
            hreach location (Reaches.undefOf hinner hstrength howner)))
        hstrength
  | borrow hloc =>
      intro hreach
      refine ValidPartialValue.borrow ?_
      refine loc_erase_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hloc hmidReads)
  | box hslot _hinner ih =>
      intro hreach
      rename_i location slot inner
      have hlocNe : location ≠ erased :=
        hreach location (Reaches.boxHere hslot)
      refine ValidPartialValue.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun reached hreached =>
          hreach reached (Reaches.boxInner hslot hreached))
  | boxFull hslot _hinner ih =>
      intro hreach
      rename_i location slot ty
      have hlocNe : location ≠ erased :=
        hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun reached hreached =>
          hreach reached (Reaches.boxFullInner hslot hreached))

theorem validPartialValueWhenInitialized_erase_of_not_reaches
    {env : Env} {store : ProgramStore} {erased : Location} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValueWhenInitialized env store v ty →
      (∀ location, Reaches store v ty location → location ≠ erased) →
      ValidPartialValueWhenInitialized env (store.erase erased) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValueWhenInitialized.undefOf
        (validPartialValueSkeleton_erase_of_not_owner_reaches hinner
          (fun location howner =>
            hreach location (Reaches.undefOf hinner hstrength howner)))
        hstrength
  | borrowLive hinitialized hloc =>
      intro hreach
      refine ValidPartialValueWhenInitialized.borrowLive hinitialized ?_
      refine loc_erase_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid (Reaches.borrow hloc hmidReads)
  | borrowStale hstale =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.borrowStale hstale
  | box hslot _hinner ih =>
      intro hreach
      rename_i location slot inner
      have hlocNe : location ≠ erased :=
        hreach location (Reaches.boxHere hslot)
      refine ValidPartialValueWhenInitialized.box (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun reached hreached =>
          hreach reached (Reaches.boxInner hslot hreached))
  | boxFull hslot _hinner ih =>
      intro hreach
      rename_i location slot ty
      have hlocNe : location ≠ erased :=
        hreach location (Reaches.boxFullHere hslot)
      refine ValidPartialValueWhenInitialized.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne]
        · exact hslot
        · exact hlocNe
      · exact ih (fun reached hreached =>
          hreach reached (Reaches.boxFullInner hslot hreached))

theorem ownerReaches_erase_to_store {store : ProgramStore}
    {erased : Location} {value : PartialValue} {ty : PartialTy}
    {location : Location} :
    OwnerReaches (store.erase erased) value ty location →
    OwnerReaches store value ty location := by
  intro hreach
  induction hreach with
  | undefOf hvalid hstrength _hinner ih =>
      exact OwnerReaches.undefOf
        (validPartialValueSkeleton_erase_to_store hvalid) hstrength ih
  | boxHere hslot =>
      exact OwnerReaches.boxHere (slotAt_of_erase_slotAt hslot)
  | boxInner hslot _hinner ih =>
      exact OwnerReaches.boxInner (slotAt_of_erase_slotAt hslot) ih
  | boxFullHere hslot =>
      exact OwnerReaches.boxFullHere (slotAt_of_erase_slotAt hslot)
  | boxFullInner hslot _hinner ih =>
      exact OwnerReaches.boxFullInner (slotAt_of_erase_slotAt hslot) ih

theorem reaches_erase_to_store {store : ProgramStore}
    {erased : Location} {value : PartialValue} {ty : PartialTy}
    {location : Location} :
    Reaches (store.erase erased) value ty location →
    Reaches store value ty location := by
  intro hreach
  induction hreach with
  | undefOf hvalid hstrength hinner =>
      exact Reaches.undefOf
        (validPartialValueSkeleton_erase_to_store hvalid)
        hstrength
        (ownerReaches_erase_to_store hinner)
  | boxHere hslot =>
      exact Reaches.boxHere (slotAt_of_erase_slotAt hslot)
  | boxInner hslot _hinner ih =>
      exact Reaches.boxInner (slotAt_of_erase_slotAt hslot) ih
  | boxFullHere hslot =>
      exact Reaches.boxFullHere (slotAt_of_erase_slotAt hslot)
  | boxFullInner hslot _hinner ih =>
      exact Reaches.boxFullInner (slotAt_of_erase_slotAt hslot) ih
  | borrow hloc hreads =>
      exact Reaches.borrow (loc_erase_some_to_store hloc)
        (locReads_erase_to_store hreads)

theorem store_owns_of_ownerReaches_stored {store : ProgramStore}
    {storage location : Location} {value : PartialValue} {ty : PartialTy}
    {lifetime : Lifetime} :
    store.slotAt storage = some { value := value, lifetime := lifetime } →
    OwnerReaches store value ty location →
    ProgramStore.Owns store location := by
  intro hstored hreach
  induction hreach generalizing storage lifetime with
  | undefOf _hvalid _hstrength _hinner ih =>
      exact ih hstored
  | boxHere =>
      rename_i ownerLocation _slot _inner hslot
      exact ⟨storage, lifetime, by
        simpa [owningRef] using hstored⟩
  | boxInner hslot _hinner ih =>
      exact ih hslot
  | boxFullHere =>
      rename_i ownerLocation _slot _ty hslot
      exact ⟨storage, lifetime, by
        simpa [owningRef] using hstored⟩
  | boxFullInner hslot _hinner ih =>
      exact ih hslot

theorem store_owns_of_reaches_stored_validPartialValue {store : ProgramStore}
    {storage location : Location} {value : PartialValue} {ty : PartialTy}
    {lifetime : Lifetime} :
    store.slotAt storage = some { value := value, lifetime := lifetime } →
    ValidPartialValue store value ty →
    OwnerReaches store value ty location →
    ProgramStore.Owns store location := by
  intro hstored _hvalid hreach
  exact store_owns_of_ownerReaches_stored hstored hreach

theorem store_owns_of_reaches_stored_validPartialValueWhenInitialized
    {env : Env} {store : ProgramStore}
    {storage location : Location} {value : PartialValue} {ty : PartialTy}
    {lifetime : Lifetime} :
    store.slotAt storage = some { value := value, lifetime := lifetime } →
    ValidPartialValueWhenInitialized env store value ty →
    OwnerReaches store value ty location →
    ProgramStore.Owns store location := by
  intro hstored _hvalid hreach
  exact store_owns_of_ownerReaches_stored hstored hreach

/-- A runtime location is protected by the variable root whose slot owns it,
possibly through a chain of heap ownership edges. -/
def ProtectedByBase (store : ProgramStore) (root : Name)
    (location : Location) : Prop :=
  location = VariableProjection root ∨
    ProgramStore.OwnsTransitively store (VariableProjection root) location

namespace ProtectedByBase

theorem root {store : ProgramStore} {root : Name} :
    ProtectedByBase store root (VariableProjection root) :=
  Or.inl rfl

theorem trans_owned {store : ProgramStore} {root : Name}
    {storage owned : Location} :
    ProtectedByBase store root storage →
    ProgramStore.OwnsAt store owned storage →
    ProtectedByBase store root owned := by
  intro hprotected howns
  cases hprotected with
  | inl hroot =>
      subst hroot
      exact Or.inr (ProgramStore.OwnsTransitively.direct howns)
  | inr hpath =>
      exact Or.inr (ProgramStore.OwnsTransitively.trans_right hpath howns)

end ProtectedByBase

theorem lval_loc_protectedBySomeBase {store : ProgramStore}
    {env : Env} {current : Lifetime} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env lv partialTy lifetime →
      store.loc lv = some location →
      ∃ root, ProtectedByBase store root location := by
  intro hwellFormed hsafe lv partialTy lifetime location htyping
  induction htyping generalizing location with
  | var hslot =>
      intro hloc
      simp [ProgramStore.loc] at hloc
      exact ⟨_, Or.inl hloc.symm⟩
  | @box source inner sourceLifetime hsource ih =>
      intro hloc
      have hsourceAbs :
          LValLocationAbstraction store source (.box inner) := by
        simpa [LValDefinedLocationAbstraction] using
          lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
          have hlocEq : location = ownedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          rcases ih hsourceLoc with ⟨root, hprotectedSource⟩
          have hownsAt :
              ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact ⟨root, by
            simpa [hlocEq] using
              ProtectedByBase.trans_owned hprotectedSource hownsAt⟩
  | @boxFull source inner sourceLifetime hsource ih =>
      intro hloc
      have hsourceAbs :
          LValLocationAbstraction store source (.ty (.box inner)) := by
        simpa [LValDefinedLocationAbstraction] using
          lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @boxFull ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
          have hlocEq : location = ownedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          rcases ih hsourceLoc with ⟨root, hprotectedSource⟩
          have hownsAt :
              ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact ⟨root, by
            simpa [hlocEq] using
              ProtectedByBase.trans_owned hprotectedSource hownsAt⟩
  | @borrow source target mutable borrowLifetime targetLifetime targetTy
      hsource htarget ihSource ihTarget =>
      intro hloc
      have hsourceAbs :
          LValLocationAbstraction store source (.ty (.borrow mutable target)) := by
        simpa [LValDefinedLocationAbstraction] using
          lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrow borrowedLocation mutable target htargetLoc =>
          have hlocEq : location = borrowedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          rcases ihTarget htargetLoc with ⟨root, hprotected⟩
          exact ⟨root, by simpa [hlocEq] using hprotected⟩

theorem locReads_protectedBySomeBase {store : ProgramStore}
    {env : Env} {current : Lifetime} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env lv partialTy lifetime →
      LocReads store lv location →
      ∃ root, ProtectedByBase store root location := by
  intro hwellFormed hsafe lv partialTy lifetime location htyping
  induction htyping with
  | var hslot =>
      intro hreads
      cases hreads
  | box hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          exact lval_loc_protectedBySomeBase hwellFormed hsafe hsource hloc
      | there hsourceReads =>
          exact ih hsourceReads
  | boxFull hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          exact lval_loc_protectedBySomeBase hwellFormed hsafe hsource hloc
      | there hsourceReads =>
          exact ih hsourceReads
  | borrow hsource htarget ihSource ihTarget =>
      intro hreads
      cases hreads with
      | here hloc =>
          exact lval_loc_protectedBySomeBase hwellFormed hsafe hsource hloc
      | there hsourceReads =>
          exact ihSource hsourceReads

theorem lval_loc_protectedBySomeBase_whenInitialized {store : ProgramStore}
    {env : Env} :
    SafeAbstraction store env →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env lv partialTy lifetime →
      store.loc lv = some location →
      ∃ root, ProtectedByBase store root location := by
  intro hsafe lv partialTy lifetime location htyping
  induction htyping generalizing location with
  | var hslot =>
      intro hloc
      simp [ProgramStore.loc] at hloc
      exact ⟨_, Or.inl hloc.symm⟩
  | box hsource ih =>
      intro hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store _ (.box _) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
          have hlocEq : location = ownedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          rcases ih hsourceLoc with ⟨root, hprotectedSource⟩
          have hownsAt :
              ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact ⟨root, by
            simpa [hlocEq] using
              ProtectedByBase.trans_owned hprotectedSource hownsAt⟩
  | boxFull hsource ih =>
      intro hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store _ (.ty (.box _)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @boxFull ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
          have hlocEq : location = ownedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          rcases ih hsourceLoc with ⟨root, hprotectedSource⟩
          have hownsAt :
              ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact ⟨root, by
            simpa [hlocEq] using
              ProtectedByBase.trans_owned hprotectedSource hownsAt⟩
  | borrow hsource htarget ihSource ihTarget =>
      intro hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store _
            (.ty (.borrow _ _)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrowLive borrowedLocation mutable target _hinitialized htargetLoc =>
          have hlocEq : location = borrowedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          rcases ihTarget htargetLoc with ⟨root, hprotected⟩
          exact ⟨root, by simpa [hlocEq] using hprotected⟩
      | @borrowStale borrowedLocation mutable target hstale =>
          exact False.elim (hstale ⟨_, _, htarget⟩)

theorem locReads_protectedBySomeBase_whenInitialized {store : ProgramStore}
    {env : Env} :
    SafeAbstraction store env →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env lv partialTy lifetime →
      LocReads store lv location →
      ∃ root, ProtectedByBase store root location := by
  intro hsafe lv partialTy lifetime location htyping
  induction htyping with
  | var hslot =>
      intro hreads
      cases hreads
  | box hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          exact lval_loc_protectedBySomeBase_whenInitialized hsafe hsource hloc
      | there hsourceReads =>
          exact ih hsourceReads
  | boxFull hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          exact lval_loc_protectedBySomeBase_whenInitialized hsafe hsource hloc
      | there hsourceReads =>
          exact ih hsourceReads
  | borrow hsource htarget ihSource ihTarget =>
      intro hreads
      cases hreads with
      | here hloc =>
          exact lval_loc_protectedBySomeBase_whenInitialized hsafe hsource hloc
      | there hsourceReads =>
          exact ihSource hsourceReads

inductive BorrowDependency (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | borrow {location dependency : Location} {mutable : Bool}
      {target : LVal} :
      store.loc target = some location →
      LocReads store target dependency →
      BorrowDependency store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable target)) dependency
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {dependency : Location} :
      store.slotAt location = some slot →
      BorrowDependency store slot.value inner dependency →
      BorrowDependency store
        (.value (.ref { location := location, owner := true }))
        (.box inner) dependency
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {dependency : Location} :
      store.slotAt location = some slot →
      BorrowDependency store slot.value (.ty ty) dependency →
      BorrowDependency store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) dependency

theorem BorrowDependency.protectedBySomeBase
    {env : Env} {store : ProgramStore} {current slotLifetime : Lifetime} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ∀ {value : PartialValue} {partialTy : PartialTy}
      {dependency : Location},
      PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
      BorrowDependency store value partialTy dependency →
      ∃ root, ProtectedByBase store root dependency := by
  intro hwellFormed hsafe value partialTy dependency hborrows hdependency
  induction hdependency generalizing slotLifetime with
  | borrow hloc hreads =>
      rcases hborrows PartialTyContains.here with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      exact locReads_protectedBySomeBase hwellFormed hsafe htargetTyping
        hreads
  | boxInner _hslot _hinner ih =>
      exact ih (by
        intro mutable target hcontains
        exact hborrows (PartialTyContains.box hcontains))
  | boxFullInner _hslot _hinner ih =>
      exact ih (by
        intro mutable target hcontains
        exact hborrows (PartialTyContains.tyBox hcontains))

/-- Borrow-resolution locations that matter for an initialized target. -/
inductive BorrowDependencyWhenInitialized (env : Env) (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | borrow {location dependency : Location} {mutable : Bool}
      {target : LVal} :
      TargetInitialized env target →
      store.loc target = some location →
      LocReads store target dependency →
      BorrowDependencyWhenInitialized env store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable target)) dependency
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {dependency : Location} :
      store.slotAt location = some slot →
      BorrowDependencyWhenInitialized env store slot.value inner dependency →
      BorrowDependencyWhenInitialized env store
        (.value (.ref { location := location, owner := true }))
        (.box inner) dependency
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {dependency : Location} :
      store.slotAt location = some slot →
      BorrowDependencyWhenInitialized env store slot.value (.ty ty) dependency →
      BorrowDependencyWhenInitialized env store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) dependency

theorem BorrowDependencyWhenInitialized.protectedBySomeBase
    {env : Env} {store : ProgramStore} :
    SafeAbstraction store env →
    ∀ {value : PartialValue} {partialTy : PartialTy}
      {dependency : Location},
      BorrowDependencyWhenInitialized env store value partialTy dependency →
      ∃ root, ProtectedByBase store root dependency := by
  intro hsafe value partialTy dependency hdependency
  induction hdependency with
  | borrow hinitialized _hloc hreads =>
      rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
      exact locReads_protectedBySomeBase_whenInitialized hsafe htargetTyping hreads
  | boxInner _hslot _hinner ih =>
      exact ih
  | boxFullInner _hslot _hinner ih =>
      exact ih

/-- Runtime locations inspected by initialized value validity.  Stale borrow
annotations intentionally contribute no runtime read dependencies. -/
inductive ReachesWhenInitialized (env : Env) (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | undefOf {value : PartialValue} {oldTy : PartialTy} {ty : Ty}
      {location : Location} :
      ValidPartialValueSkeleton store value oldTy →
      PartialTyStrengthens oldTy (.undef ty) →
      OwnerReaches store value oldTy location →
      ReachesWhenInitialized env store value (.undef ty) location
  | boxHere {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := true }))
        (.box inner) location
  | boxInner {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {reached : Location} :
      store.slotAt location = some slot →
      ReachesWhenInitialized env store slot.value inner reached →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := true }))
        (.box inner) reached
  | boxFullHere {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) location
  | boxFullInner {location : Location} {slot : StoreSlot} {ty : Ty}
      {reached : Location} :
      store.slotAt location = some slot →
      ReachesWhenInitialized env store slot.value (.ty ty) reached →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) reached
  | borrow {location reached : Location} {mutable : Bool} {target : LVal} :
      TargetInitialized env target →
      store.loc target = some location →
      LocReads store target reached →
      ReachesWhenInitialized env store
        (.value (.ref { location := location, owner := false }))
        (.ty (.borrow mutable target)) reached

theorem reachesWhenInitialized_erase_to_store {env : Env}
    {store : ProgramStore} {erased : Location} {value : PartialValue}
    {ty : PartialTy} {location : Location} :
    ReachesWhenInitialized env (store.erase erased) value ty location →
    ReachesWhenInitialized env store value ty location := by
  intro hreach
  induction hreach with
  | undefOf hvalid hstrength hinner =>
      exact ReachesWhenInitialized.undefOf
        (validPartialValueSkeleton_erase_to_store hvalid) hstrength
        (ownerReaches_erase_to_store hinner)
  | boxHere hslot =>
      exact ReachesWhenInitialized.boxHere (slotAt_of_erase_slotAt hslot)
  | boxInner hslot _hinner ih =>
      exact ReachesWhenInitialized.boxInner (slotAt_of_erase_slotAt hslot) ih
  | boxFullHere hslot =>
      exact ReachesWhenInitialized.boxFullHere (slotAt_of_erase_slotAt hslot)
  | boxFullInner hslot _hinner ih =>
      exact ReachesWhenInitialized.boxFullInner (slotAt_of_erase_slotAt hslot) ih
  | borrow hinitialized hloc hreads =>
      exact ReachesWhenInitialized.borrow hinitialized
        (loc_erase_some_to_store hloc) (locReads_erase_to_store hreads)

theorem validPartialValueWhenInitialized_erase_of_not_live_reaches {env : Env}
    {store : ProgramStore} {erased : Location} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValueWhenInitialized env store v ty →
      (∀ location, ReachesWhenInitialized env store v ty location →
        location ≠ erased) →
      ValidPartialValueWhenInitialized env (store.erase erased) v ty := by
  intro v ty hvalid
  induction hvalid with
  | unit =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      intro hreach
      exact ValidPartialValueWhenInitialized.undefOf
        (validPartialValueSkeleton_erase_of_not_owner_reaches hinner
          (fun location howner =>
            hreach location
              (ReachesWhenInitialized.undefOf hinner hstrength howner)))
        hstrength
  | borrowLive hinitialized hloc =>
      intro hreach
      refine ValidPartialValueWhenInitialized.borrowLive hinitialized ?_
      refine loc_erase_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid
        (ReachesWhenInitialized.borrow hinitialized hloc hmidReads)
  | borrowStale hstale =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.borrowStale hstale
  | box hslot _hinner ih =>
      intro hreach
      rename_i location slot inner
      have hlocNe : location ≠ erased :=
        hreach location (ReachesWhenInitialized.boxHere hslot)
      refine ValidPartialValueWhenInitialized.box (location := location)
        (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne store hlocNe]
        exact hslot
      · exact ih (fun reached hreached =>
          hreach reached (ReachesWhenInitialized.boxInner hslot hreached))
  | boxFull hslot _hinner ih =>
      intro hreach
      rename_i location slot ty
      have hlocNe : location ≠ erased :=
        hreach location (ReachesWhenInitialized.boxFullHere hslot)
      refine ValidPartialValueWhenInitialized.boxFull (location := location)
        (slot := slot) ?_ ?_
      · rw [ProgramStore.erase_slotAt_ne store hlocNe]
        exact hslot
      · exact ih (fun reached hreached =>
          hreach reached (ReachesWhenInitialized.boxFullInner hslot hreached))

theorem validPartialValueWhenInitialized_drops_of_avoids_live_reaches
    {env : Env} {store store' : ProgramStore}
    {values : List PartialValue} {value : PartialValue} {ty : PartialTy} :
    Drops store values store' →
    ValidPartialValueWhenInitialized env store value ty →
    (∀ location, ReachesWhenInitialized env store value ty location →
      DropsAvoids store values location) →
    ValidPartialValueWhenInitialized env store' value ty := by
  intro hdrops hvalid havoids
  induction hdrops generalizing value ty with
  | nil =>
      exact hvalid
  | nonOwner hnonOwner _hdrops ih =>
      exact ih hvalid (by
        intro location hreach
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner _ hrest => exact hrest
        | ownerMissing howner _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerPresent howner _ _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner))
  | ownerMissing howner hmissing _hdrops ih =>
      exact ih hvalid (by
        intro location hreach
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ _ hrest => exact hrest
        | ownerPresent _ hpresent _ _ =>
            rw [hmissing] at hpresent
            cases hpresent)
  | ownerPresent howner hpresent _hdrops ih =>
      rename_i storeBefore _storeAfter ref erasedSlot rest
      have hnotErased :
          ∀ location,
            ReachesWhenInitialized env storeBefore value ty location →
              location ≠ ref.location := by
        intro location hreach hlocation
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ hmissing _ =>
            rw [hpresent] at hmissing
            cases hmissing
        | ownerPresent _ _ hne _ =>
            exact hne hlocation.symm
      have hvalidErased :
          ValidPartialValueWhenInitialized env
            (storeBefore.erase ref.location) value ty :=
        validPartialValueWhenInitialized_erase_of_not_live_reaches
          hvalid hnotErased
      exact ih hvalidErased (by
        intro location hreachErased
        have hreachStore :
            ReachesWhenInitialized env storeBefore value ty location :=
          reachesWhenInitialized_erase_to_store hreachErased
        have havoid := havoids location hreachStore
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ hmissing _ =>
            rw [hpresent] at hmissing
            cases hmissing
        | ownerPresent _ hpresent' _ hrest =>
            rw [hpresent] at hpresent'
            cases hpresent'
            exact hrest)

theorem dropsAvoids_of_ownsTransitively_unprotected_values
    {store store' : ProgramStore} {values : List PartialValue}
    {root : Name} {storage owned : Location} :
    Drops store values store' →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    (∀ value, value ∈ values → ∀ owned,
      owned ∈ partialValueOwningLocations value →
      ProtectedByBase store root owned → False) →
    ProtectedByBase store root storage →
    DropsAvoids store values storage →
    ProgramStore.OwnsTransitively store storage owned →
    DropsAvoids store values owned := by
  intro hdrops hvalidStore hheap hvaluesHeap hdisjoint
    hprotectedStorage havoidStorage hpath
  induction hpath generalizing root with
  | direct howns =>
      have hprotectedOwned :
          ProtectedByBase store root _ :=
        ProtectedByBase.trans_owned hprotectedStorage howns
      exact dropsAvoids_of_protected_owner hdrops hvalidStore howns
        havoidStorage (by
          intro value hmem howned
          exact hdisjoint value hmem _ howned hprotectedOwned)
  | trans hfirst _htail ih =>
      have hprotectedMiddle :
          ProtectedByBase store root _ :=
        ProtectedByBase.trans_owned hprotectedStorage hfirst
      have havoidMiddle : DropsAvoids store values _ :=
        dropsAvoids_of_protected_owner hdrops hvalidStore hfirst
          havoidStorage (by
            intro value hmem howned
            exact hdisjoint value hmem _ howned hprotectedMiddle)
      exact ih hdisjoint hprotectedMiddle havoidMiddle

theorem dropsAvoids_of_protectedByBase_unprotected_values
    {store store' : ProgramStore} {values : List PartialValue}
    {root : Name} {location : Location} :
    Drops store values store' →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    (∀ value, value ∈ values → ∀ owned,
      owned ∈ partialValueOwningLocations value →
      ProtectedByBase store root owned → False) →
    ProtectedByBase store root location →
    DropsAvoids store values location := by
  intro hdrops hvalidStore hheap hvaluesHeap hdisjoint hprotected
  cases hprotected with
  | inl hroot =>
      subst hroot
      exact dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hvaluesHeap
  | inr hpath =>
      have havoidRoot :
          DropsAvoids store values (VariableProjection root) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hvaluesHeap
      exact dropsAvoids_of_ownsTransitively_unprotected_values
        hdrops hvalidStore hheap hvaluesHeap hdisjoint
        (ProtectedByBase.root (store := store) (root := root))
        havoidRoot hpath

theorem dropsAvoids_of_borrowDependency_unprotected_values
    {env : Env} {store store' : ProgramStore} {current slotLifetime : Lifetime}
    {values : List PartialValue} {value : PartialValue}
    {partialTy : PartialTy} {dependency : Location} :
    Drops store values store' →
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ value, value ∈ values → ∀ owned,
      owned ∈ partialValueOwningLocations value →
      ∀ root, ProtectedByBase store root owned → False) →
    BorrowDependency store value partialTy dependency →
    DropsAvoids store values dependency := by
  intro hdrops hwellFormed hsafe hvalidStore hheap hvaluesHeap hborrows
    hdisjoint hdependency
  rcases BorrowDependency.protectedBySomeBase hwellFormed hsafe hborrows
      hdependency with
    ⟨root, hprotected⟩
  exact dropsAvoids_of_protectedByBase_unprotected_values
    hdrops hvalidStore hheap hvaluesHeap
    (by
      intro value hmem owned howned hprotectedOwned
      exact hdisjoint value hmem owned howned root hprotectedOwned)
    hprotected

theorem dropsAvoids_of_borrowDependencyWhenInitialized_unprotected_values
    {env : Env} {store store' : ProgramStore}
    {values : List PartialValue} {value : PartialValue}
    {partialTy : PartialTy} {dependency : Location} :
    Drops store values store' →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    (∀ value, value ∈ values → ∀ owned,
      owned ∈ partialValueOwningLocations value →
      ∀ root, ProtectedByBase store root owned → False) →
    BorrowDependencyWhenInitialized env store value partialTy dependency →
    DropsAvoids store values dependency := by
  intro hdrops hsafe hvalidStore hheap hvaluesHeap hdisjoint hdependency
  rcases BorrowDependencyWhenInitialized.protectedBySomeBase hsafe hdependency with
    ⟨root, hprotected⟩
  exact dropsAvoids_of_protectedByBase_unprotected_values
    hdrops hvalidStore hheap hvaluesHeap
    (by
      intro value hmem owned howned hprotectedOwned
      exact hdisjoint value hmem owned howned root hprotectedOwned)
    hprotected

theorem dropsAvoids_of_ownerReaches_stored
    {store store' : ProgramStore} {values : List PartialValue}
    {storage location : Location} {value : PartialValue}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    Drops store values store' →
    ValidStore store →
    store.slotAt storage = some { value := value, lifetime := lifetime } →
    DropsAvoids store values storage →
    (∀ reached,
      OwnerReaches store value partialTy reached →
      ∀ dropValue, dropValue ∈ values →
        reached ∈ partialValueOwningLocations dropValue → False) →
    OwnerReaches store value partialTy location →
    DropsAvoids store values location := by
  intro hdrops hvalidStore hstored havoidStorage hdisjoint hreach
  induction hreach generalizing storage lifetime with
  | undefOf _hvalid _hstrength _hinner ih =>
      exact ih hstored havoidStorage (by
        intro reached howner dropValue hmem howned
        exact hdisjoint reached
          (OwnerReaches.undefOf _hvalid _hstrength howner)
          dropValue hmem howned)
  | boxHere hslot =>
      rename_i ownerLocation _slot _inner
      have hownsAt :
          ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨lifetime, by simpa [owningRef] using hstored⟩
      exact dropsAvoids_of_protected_owner hdrops hvalidStore hownsAt
        havoidStorage (by
          intro dropValue hmem howned
          exact hdisjoint ownerLocation (OwnerReaches.boxHere hslot)
            dropValue hmem howned)
  | boxInner hslot _hinner ih =>
      rename_i ownerLocation ownerSlot inner reached
      have hownsAt :
          ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨lifetime, by simpa [owningRef] using hstored⟩
      have havoidOwner :
          DropsAvoids store values ownerLocation :=
        dropsAvoids_of_protected_owner hdrops hvalidStore hownsAt
          havoidStorage (by
            intro dropValue hmem howned
            exact hdisjoint ownerLocation (OwnerReaches.boxHere hslot)
              dropValue hmem howned)
      exact ih hslot havoidOwner (by
        intro innerReached howner dropValue hmem howned
        exact hdisjoint innerReached (OwnerReaches.boxInner hslot howner)
          dropValue hmem howned)
  | boxFullHere hslot =>
      rename_i ownerLocation _slot _ty
      have hownsAt :
          ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨lifetime, by simpa [owningRef] using hstored⟩
      exact dropsAvoids_of_protected_owner hdrops hvalidStore hownsAt
        havoidStorage (by
          intro dropValue hmem howned
          exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hslot)
            dropValue hmem howned)
  | boxFullInner hslot _hinner ih =>
      rename_i ownerLocation ownerSlot ty reached
      have hownsAt :
          ProgramStore.OwnsAt store ownerLocation storage :=
        ⟨lifetime, by simpa [owningRef] using hstored⟩
      have havoidOwner :
          DropsAvoids store values ownerLocation :=
        dropsAvoids_of_protected_owner hdrops hvalidStore hownsAt
          havoidStorage (by
            intro dropValue hmem howned
            exact hdisjoint ownerLocation (OwnerReaches.boxFullHere hslot)
              dropValue hmem howned)
      exact ih hslot havoidOwner (by
        intro innerReached howner dropValue hmem howned
        exact hdisjoint innerReached (OwnerReaches.boxFullInner hslot howner)
          dropValue hmem howned)

theorem dropsAvoids_of_reaches_stored_validPartialValue
    {env : Env} {store store' : ProgramStore}
    {values : List PartialValue} {storage location : Location}
    {value : PartialValue} {partialTy : PartialTy}
    {lifetime slotLifetime current : Lifetime} :
    Drops store values store' →
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    store.slotAt storage = some { value := value, lifetime := lifetime } →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    ValidPartialValue store value partialTy →
    DropsAvoids store values storage →
    (∀ reached,
      OwnerReaches store value partialTy reached →
      ∀ dropValue, dropValue ∈ values →
        reached ∈ partialValueOwningLocations dropValue → False) →
    (∀ value, value ∈ values → ∀ owned,
      owned ∈ partialValueOwningLocations value →
      ∀ root, ProtectedByBase store root owned → False) →
    Reaches store value partialTy location →
    DropsAvoids store values location := by
  intro hdrops hwellFormed hsafe hvalidStore hheap hvaluesHeap hstored
    hborrows hvalid havoidStorage hownerDisjoint hprotectedDisjoint hreach
  induction hreach generalizing storage lifetime with
  | undefOf hskel hstrength howner =>
      exact dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
        havoidStorage hownerDisjoint
        (OwnerReaches.undefOf hskel hstrength howner)
  | boxHere hslot =>
      exact dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
        havoidStorage hownerDisjoint (OwnerReaches.boxHere hslot)
  | boxInner hslot _hinner ih =>
      rename_i ownerLocation ownerSlot inner reached
      cases hvalid with
      | box hvalidSlot hinnerValid =>
          have hslotEq : ownerSlot = _ :=
            Option.some.inj (hslot.symm.trans hvalidSlot)
          subst hslotEq
          have havoidOwner :
              DropsAvoids store values ownerLocation :=
            dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
              havoidStorage hownerDisjoint (OwnerReaches.boxHere hslot)
          exact ih hslot
            (PartialTyBorrowsWellFormedInSlot.box_inv hborrows)
            hinnerValid havoidOwner
            (by
              intro innerReached howner dropValue hmem howned
              exact hownerDisjoint innerReached
                (OwnerReaches.boxInner hslot howner) dropValue hmem howned)
  | boxFullHere hslot =>
      exact dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
        havoidStorage hownerDisjoint (OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _hinner ih =>
      rename_i ownerLocation ownerSlot ty reached
      cases hvalid with
      | boxFull hvalidSlot hinnerValid =>
          have hslotEq : ownerSlot = _ :=
            Option.some.inj (hslot.symm.trans hvalidSlot)
          subst hslotEq
          have havoidOwner :
              DropsAvoids store values ownerLocation :=
            dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
              havoidStorage hownerDisjoint (OwnerReaches.boxFullHere hslot)
          exact ih hslot
            (by
              intro mutable target hcontains
              exact hborrows (PartialTyContains.tyBox hcontains))
            hinnerValid havoidOwner
            (by
              intro innerReached howner dropValue hmem howned
              exact hownerDisjoint innerReached
                (OwnerReaches.boxFullInner hslot howner) dropValue hmem howned)
  | borrow hloc hreads =>
      exact dropsAvoids_of_borrowDependency_unprotected_values
        hdrops hwellFormed hsafe hvalidStore hheap hvaluesHeap hborrows
        hprotectedDisjoint (BorrowDependency.borrow hloc hreads)

theorem dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized
    {env : Env} {store store' : ProgramStore}
    {values : List PartialValue} {storage location : Location}
    {value : PartialValue} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    Drops store values store' →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    store.slotAt storage = some { value := value, lifetime := lifetime } →
    ValidPartialValueWhenInitialized env store value partialTy →
    DropsAvoids store values storage →
    (∀ reached,
      OwnerReaches store value partialTy reached →
      ∀ dropValue, dropValue ∈ values →
        reached ∈ partialValueOwningLocations dropValue → False) →
    (∀ dependency,
      BorrowDependencyWhenInitialized env store value partialTy dependency →
        DropsAvoids store values dependency) →
    ReachesWhenInitialized env store value partialTy location →
    DropsAvoids store values location := by
  intro hdrops hsafe hvalidStore hheap hvaluesHeap hstored hvalid
    havoidStorage hownerDisjoint hdependencyFrame hreach
  induction hreach generalizing storage lifetime with
  | undefOf hskel hstrength howner =>
      exact dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
        havoidStorage hownerDisjoint
        (OwnerReaches.undefOf hskel hstrength howner)
  | boxHere hslot =>
      exact dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
        havoidStorage hownerDisjoint (OwnerReaches.boxHere hslot)
  | boxInner hslot _hinner ih =>
      rename_i ownerLocation ownerSlot inner reached
      cases hvalid with
      | box hvalidSlot hinnerValid =>
          have hslotEq : ownerSlot = _ :=
            Option.some.inj (hslot.symm.trans hvalidSlot)
          subst hslotEq
          have havoidOwner :
              DropsAvoids store values ownerLocation :=
            dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
              havoidStorage hownerDisjoint (OwnerReaches.boxHere hslot)
          exact ih hslot hinnerValid havoidOwner
            (by
              intro innerReached howner dropValue hmem howned
              exact hownerDisjoint innerReached
                (OwnerReaches.boxInner hslot howner) dropValue hmem howned)
            (by
              intro dependency hdep
              exact hdependencyFrame dependency
                (BorrowDependencyWhenInitialized.boxInner hslot hdep))
  | boxFullHere hslot =>
      exact dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
        havoidStorage hownerDisjoint (OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _hinner ih =>
      rename_i ownerLocation ownerSlot ty reached
      cases hvalid with
      | boxFull hvalidSlot hinnerValid =>
          have hslotEq : ownerSlot = _ :=
            Option.some.inj (hslot.symm.trans hvalidSlot)
          subst hslotEq
          have havoidOwner :
              DropsAvoids store values ownerLocation :=
            dropsAvoids_of_ownerReaches_stored hdrops hvalidStore hstored
              havoidStorage hownerDisjoint (OwnerReaches.boxFullHere hslot)
          exact ih hslot hinnerValid havoidOwner
            (by
              intro innerReached howner dropValue hmem howned
              exact hownerDisjoint innerReached
                (OwnerReaches.boxFullInner hslot howner) dropValue hmem howned)
            (by
              intro dependency hdep
              exact hdependencyFrame dependency
                (BorrowDependencyWhenInitialized.boxFullInner hslot hdep))
  | borrow hinitialized hloc hreads =>
      cases hvalid with
      | borrowLive _hinitializedValid _hlocValid =>
          exact hdependencyFrame _
            (BorrowDependencyWhenInitialized.borrow hinitialized hloc hreads)
      | borrowStale hstale =>
          exact False.elim (hstale hinitialized)

theorem validPartialValue_drops_of_avoids_reaches
    {store store' : ProgramStore} {values : List PartialValue}
    {value : PartialValue} {ty : PartialTy} :
    Drops store values store' →
    ValidPartialValue store value ty →
    (∀ location, Reaches store value ty location →
      DropsAvoids store values location) →
    ValidPartialValue store' value ty := by
  intro hdrops hvalid havoids
  induction hdrops generalizing value ty with
  | nil =>
      exact hvalid
  | nonOwner hnonOwner _hdrops ih =>
      exact ih hvalid (by
        intro location hreach
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner _ hrest => exact hrest
        | ownerMissing howner _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerPresent howner _ _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner))
  | ownerMissing howner hmissing _hdrops ih =>
      exact ih hvalid (by
        intro location hreach
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ _ hrest => exact hrest
        | ownerPresent _ hpresent _ _ =>
            rw [hmissing] at hpresent
            cases hpresent)
  | ownerPresent howner hpresent _hdrops ih =>
      rename_i storeBefore _storeAfter ref erasedSlot rest
      have hnotErased :
          ∀ location, Reaches storeBefore value ty location →
            location ≠ ref.location := by
        intro location hreach hlocation
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ hmissing _ =>
            rw [hpresent] at hmissing
            cases hmissing
        | ownerPresent _ _ hne _ =>
            exact hne hlocation.symm
      have hvalidErased :
          ValidPartialValue (storeBefore.erase ref.location) value ty :=
        validPartialValue_erase_of_not_reaches hvalid hnotErased
      exact ih hvalidErased (by
        intro location hreachErased
        have hreachStore : Reaches storeBefore value ty location :=
          reaches_erase_to_store hreachErased
        have havoid := havoids location hreachStore
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ hmissing _ =>
            rw [hpresent] at hmissing
            cases hmissing
        | ownerPresent _ hpresent' _ hrest =>
            rw [hpresent] at hpresent'
            cases hpresent'
            exact hrest)

theorem validPartialValueWhenInitialized_drops_of_avoids_reachesWhenInitialized
    {env : Env} {store store' : ProgramStore}
    {values : List PartialValue} {value : PartialValue} {ty : PartialTy} :
    Drops store values store' →
    ValidPartialValueWhenInitialized env store value ty →
    (∀ location, Reaches store value ty location →
      DropsAvoids store values location) →
    ValidPartialValueWhenInitialized env store' value ty := by
  intro hdrops hvalid havoids
  induction hdrops generalizing value ty with
  | nil =>
      exact hvalid
  | nonOwner hnonOwner _hdrops ih =>
      exact ih hvalid (by
        intro location hreach
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner _ hrest => exact hrest
        | ownerMissing howner _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerPresent howner _ _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner))
  | ownerMissing howner hmissing _hdrops ih =>
      exact ih hvalid (by
        intro location hreach
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ _ hrest => exact hrest
        | ownerPresent _ hpresent _ _ =>
            rw [hmissing] at hpresent
            cases hpresent)
  | ownerPresent howner hpresent _hdrops ih =>
      rename_i storeBefore _storeAfter ref erasedSlot rest
      have hnotErased :
          ∀ location, Reaches storeBefore value ty location →
            location ≠ ref.location := by
        intro location hreach hlocation
        have havoid := havoids location hreach
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ hmissing _ =>
            rw [hpresent] at hmissing
            cases hmissing
        | ownerPresent _ _ hne _ =>
            exact hne hlocation.symm
      have hvalidErased :
          ValidPartialValueWhenInitialized env
            (storeBefore.erase ref.location) value ty :=
        validPartialValueWhenInitialized_erase_of_not_reaches hvalid hnotErased
      exact ih hvalidErased (by
        intro location hreachErased
        have hreachStore : Reaches storeBefore value ty location :=
          reaches_erase_to_store hreachErased
        have havoid := havoids location hreachStore
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ hmissing _ =>
            rw [hpresent] at hmissing
            cases hmissing
        | ownerPresent _ hpresent' _ hrest =>
            rw [hpresent] at hpresent'
            cases hpresent'
            exact hrest)

theorem validValue_drops_of_avoids_reaches
    {store store' : ProgramStore} {values : List PartialValue}
    {value : Value} {ty : Ty} :
    Drops store values store' →
    ValidValue store value ty →
    (∀ location, Reaches store (.value value) (.ty ty) location →
      DropsAvoids store values location) →
    ValidValue store' value ty :=
  validPartialValue_drops_of_avoids_reaches

end RuntimeFrame

/-- `R-Seq` preserves the safe abstraction for the remaining sequence env. -/
theorem safeAbstraction_seq_value_drop
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term}
    {rest : List Term} :
    store ≈ₛ env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    WellFormedEnv env blockLifetime →
    Drops store [.value value] store' →
    store' ≈ₛ env := by
  intro hsafe hvalidRuntime hwellFormed hdrops
  have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
    ValueOwnerTargetsHeap.partial
      (TermOwnerTargetsHeap.value
        (termOwnerTargetsHeap_block_head
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [.value value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact hvalueHeap
  constructor
  · intro x
    constructor
    · intro hstore'
      rcases hstore' with ⟨slot, hslot'⟩
      have hslot : store.slotAt (VariableProjection x) = some slot :=
        drops_slotAt_of_slotAt hdrops hslot'
      exact (hsafe.1 x).mp ⟨slot, hslot⟩
    · intro henv
      rcases (hsafe.1 x).mpr henv with ⟨slot, hslot⟩
      have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hdropValuesHeap
      exact ⟨slot, dropsAvoids_slotAt_preserved hdrops havoidVar hslot⟩
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops
        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
        hdropValuesHeap
    have hstoreSlot' :
        store'.slotAt (VariableProjection x) =
          some { value := oldValue, lifetime := envSlot.lifetime } :=
      dropsAvoids_slotAt_preserved hdrops havoidVar hstoreSlot
    have hborrows :
        PartialTyBorrowsWellFormedInSlot env envSlot.lifetime envSlot.ty := by
      intro mutable targets hcontains
      exact hwellFormed.1 x envSlot mutable targets henvSlot
        ⟨envSlot, henvSlot, hcontains⟩
    have hvalidOld' : ValidPartialValue store' oldValue envSlot.ty :=
      RuntimeFrame.validPartialValue_drops_of_avoids_reaches hdrops hvalidOld
        (by
          intro reached hreach
          exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
            hdrops hwellFormed hsafe
            (ValidRuntimeState.validStore hvalidRuntime)
            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
            hdropValuesHeap hstoreSlot hborrows hvalidOld havoidVar
            (by
              intro reached' hreach' dropValue hmem howned
              simp at hmem
              subst hmem
              have hownsReached :
                  ProgramStore.Owns store reached' :=
                RuntimeFrame.store_owns_of_reaches_stored_validPartialValue
                  hstoreSlot hvalidOld hreach'
              exact
                (ValidRuntimeState.storeTermDisjoint hvalidRuntime reached'
                  (by
                    have hhead :
                        reached' ∈ valueOwningLocations value := by
                      simpa [partialValueOwningLocations] using howned
                    simp [termOwningLocations, termValues, hhead]))
                hownsReached)
            (by
              intro dropValue hmem owned howned base hprotectedOwned
              simp at hmem
              subst hmem
              have hownedValue :
                  owned ∈ valueOwningLocations value := by
                simpa [partialValueOwningLocations] using howned
              rcases hprotectedOwned with hroot | hpath
              · subst hroot
                rcases hvalueHeap (VariableProjection base)
                    (by simpa [partialValueOwningLocations] using howned) with
                  ⟨address, hheapLocation⟩
                cases hheapLocation
              · exact
                  (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
                    (by
                      simp [termOwningLocations, termValues]
                      exact Or.inl hownedValue))
                  (ProgramStore.OwnsTransitively.to_owns hpath))
            hreach)
    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩

/--
Factored initialized `R-Seq` store-abstraction frame.

The only nontrivial obligation is the per-slot reach frame: every runtime
location inspected by an environment slot's abstract value must be avoided by
the recursive drop of the sequence head value.
-/
theorem safeAbstraction_seq_value_drop_whenInitialized_of_reaches
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term}
    {rest : List Term} :
    SafeAbstraction store env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    Drops store [.value value] store' →
    (∀ x envSlot oldValue,
      env.slotAt x = some envSlot →
      store.slotAt (VariableProjection x) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ∀ location, RuntimeFrame.Reaches store oldValue envSlot.ty location →
        DropsAvoids store [.value value] location) →
    SafeAbstraction store' env := by
  intro hsafe hvalidRuntime hdrops hframe
  refine safeAbstractionWhenInitialized_of_domain_and_slots ?domain ?slots
  · intro x
    constructor
    · intro hstore'
      rcases hstore' with ⟨slot, hslot'⟩
      have hslot : store.slotAt (VariableProjection x) = some slot :=
        drops_slotAt_of_slotAt hdrops hslot'
      exact (hsafe.1 x).mp ⟨slot, hslot⟩
    · intro henv
      rcases (hsafe.1 x).mpr henv with ⟨slot, hslot⟩
      rcases henv with ⟨envSlot, henvSlot⟩
      rcases hsafe.2 x envSlot henvSlot with ⟨oldValue, hstoreSlot, _hvalidOld⟩
      have hslotEq : slot = { value := oldValue, lifetime := envSlot.lifetime } :=
        Option.some.inj (hslot.symm.trans hstoreSlot)
      subst hslotEq
      have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
        ValueOwnerTargetsHeap.partial
          (TermOwnerTargetsHeap.value
            (termOwnerTargetsHeap_block_head
              (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
      have hdropValuesHeap :
          ∀ dropValue, dropValue ∈ [.value value] →
            PartialValueOwnerTargetsHeap dropValue := by
        intro dropValue hmem
        simp at hmem
        subst hmem
        exact hvalueHeap
      have havoidVar :
          DropsAvoids store [.value value] (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hdropValuesHeap
      exact ⟨{ value := oldValue, lifetime := envSlot.lifetime },
        dropsAvoids_slotAt_preserved hdrops havoidVar hstoreSlot⟩
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
      ValueOwnerTargetsHeap.partial
        (TermOwnerTargetsHeap.value
          (termOwnerTargetsHeap_block_head
            (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
    have hdropValuesHeap :
        ∀ dropValue, dropValue ∈ [.value value] →
          PartialValueOwnerTargetsHeap dropValue := by
      intro dropValue hmem
      simp at hmem
      subst hmem
      exact hvalueHeap
    have havoidVar : DropsAvoids store [.value value] (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops
        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
        hdropValuesHeap
    have hstoreSlot' :
        store'.slotAt (VariableProjection x) =
          some { value := oldValue, lifetime := envSlot.lifetime } :=
      dropsAvoids_slotAt_preserved hdrops havoidVar hstoreSlot
    have hvalidOld' :
        ValidPartialValueWhenInitialized env store' oldValue envSlot.ty :=
      RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_reachesWhenInitialized
        hdrops hvalidOld (hframe x envSlot oldValue henvSlot hstoreSlot)
    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩

/-- `R-Seq` preserves initialized safe abstraction for the remaining sequence
environment after dropping the completed head value. -/
theorem safeAbstraction_seq_value_drop_whenInitialized
    {store store' : ProgramStore} {env : Env}
    {blockLifetime : Lifetime} {value : Value} {next : Term}
    {rest : List Term} :
    SafeAbstraction store env →
    ValidRuntimeState store (.block blockLifetime (.val value :: next :: rest)) →
    WellFormedEnvWhenInitialized env blockLifetime →
    Drops store [.value value] store' →
    SafeAbstraction store' env := by
  intro hsafe hvalidRuntime _hwellFormed hdrops
  have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
    ValueOwnerTargetsHeap.partial
      (TermOwnerTargetsHeap.value
        (termOwnerTargetsHeap_block_head
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [.value value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact hvalueHeap
  refine safeAbstractionWhenInitialized_of_domain_and_slots ?domain ?slots
  · intro x
    constructor
    · intro hstore'
      rcases hstore' with ⟨slot, hslot'⟩
      have hslot : store.slotAt (VariableProjection x) = some slot :=
        drops_slotAt_of_slotAt hdrops hslot'
      exact (hsafe.1 x).mp ⟨slot, hslot⟩
    · intro henv
      rcases (hsafe.1 x).mpr henv with ⟨slot, hslot⟩
      have havoidVar :
          DropsAvoids store [.value value] (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hdropValuesHeap
      exact ⟨slot, dropsAvoids_slotAt_preserved hdrops havoidVar hslot⟩
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    have havoidVar :
        DropsAvoids store [.value value] (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops
        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
        hdropValuesHeap
    have hstoreSlot' :
        store'.slotAt (VariableProjection x) =
          some { value := oldValue, lifetime := envSlot.lifetime } :=
      dropsAvoids_slotAt_preserved hdrops havoidVar hstoreSlot
    have hvalidOld' :
        ValidPartialValueWhenInitialized env store' oldValue envSlot.ty :=
      RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_live_reaches
        hdrops hvalidOld (by
          intro reached hreach
          exact
            RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized
              hdrops hsafe
              (ValidRuntimeState.validStore hvalidRuntime)
              (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
              hdropValuesHeap hstoreSlot hvalidOld havoidVar
              (by
                intro reached' howner dropValue hmem howned
                simp at hmem
                subst hmem
                have hownsReached :
                    ProgramStore.Owns store reached' :=
                  RuntimeFrame.store_owns_of_reaches_stored_validPartialValueWhenInitialized
                    hstoreSlot hvalidOld howner
                exact
                  (ValidRuntimeState.storeTermDisjoint hvalidRuntime reached'
                    (by
                      have hhead :
                          reached' ∈ valueOwningLocations value := by
                        simpa [partialValueOwningLocations] using howned
                      simp [termOwningLocations, termValues, hhead]))
                  hownsReached)
              (by
                intro dependency hdependency
                exact
                  RuntimeFrame.dropsAvoids_of_borrowDependencyWhenInitialized_unprotected_values
                    hdrops hsafe
                    (ValidRuntimeState.validStore hvalidRuntime)
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hdropValuesHeap
                    (by
                      intro dropValue hmem owned howned base hprotectedOwned
                      simp at hmem
                      subst hmem
                      have hownedValue :
                          owned ∈ valueOwningLocations value := by
                        simpa [partialValueOwningLocations] using howned
                      cases hprotectedOwned with
                      | inl hroot =>
                          subst hroot
                          rcases hvalueHeap (VariableProjection base)
                              (by
                                simpa [partialValueOwningLocations] using
                                  howned) with
                            ⟨address, hheapLocation⟩
                          cases hheapLocation
                      | inr hpath =>
                          exact
                            (ValidRuntimeState.storeTermDisjoint
                              hvalidRuntime owned
                              (by
                                simp [termOwningLocations, termValues]
                                exact Or.inl hownedValue))
                            (ProgramStore.OwnsTransitively.to_owns hpath))
                    hdependency)
              hreach)
    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩

/-- First-step decomposition wrapper specialized to `TerminalStateSafe`. -/
theorem preservation_block_terminal_multistep_runtime_whenInitialized_of_first_step
    {store finalStore : ProgramStore} {env' : Env}
    {lifetime blockLifetime : Lifetime} {terms : List Term}
    {finalValue : Value} {ty : Ty} :
    (∀ value next rest store',
      terms = .val value :: next :: rest →
      Drops store [.value value] store' →
      MultiStep store' lifetime (.block blockLifetime (next :: rest))
        finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env' ty) →
    (∀ term rest store' term',
      terms = term :: rest →
      Step store blockLifetime term store' term' →
      MultiStep store' lifetime (.block blockLifetime (term' :: rest))
        finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env' ty) →
    (∀ value store',
      terms = [.val value] →
      DropsLifetime store blockLifetime store' →
      MultiStep store' lifetime (.val value) finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env' ty) →
    MultiStep store lifetime (.block blockLifetime terms) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env' ty := by
  intro hseq hblockA hblockB hmulti
  rcases multistep_block_to_value_first_step_inv hmulti with
    hseqCase | hblockACase | hblockBCase
  · rcases hseqCase with ⟨value, next, rest, store', hterms, hdrops, htail⟩
    exact hseq value next rest store' hterms hdrops htail
  · rcases hblockACase with ⟨term, rest, store', term', hterms, hstep, htail⟩
    exact hblockA term rest store' term' hterms hstep htail
  · rcases hblockBCase with ⟨value, store', hterms, hdrops, htail⟩
    exact hblockB value store' hterms hdrops htail

/-! ### Lifetime-tree facts and static invariant transports (single-target)

Support for the static walk `typingPreservesWellFormedWhenInitialized_of_sourceTerm`:
fresh-declaration update and block lifetime-drop transports for the two-part
`WellFormedEnvWhenInitialized` invariant.
-/

theorem LifetimeChild.parent_of_outlives_child_ne {parent child slot : Lifetime} :
    LifetimeChild parent child →
    slot ≤ child →
    slot ≠ child →
    slot ≤ parent := by
  intro hchild hslot hne
  rcases hchild with ⟨label, hpath⟩
  have hslotPrefix : slot.path <+: child.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hslot
  have hparentPrefix : parent.path <+: child.path := by
    simp [hpath]
  have hslotLenLeChild : slot.path.length ≤ child.path.length :=
    hslotPrefix.length_le
  have hslotLenNeChild : slot.path.length ≠ child.path.length := by
    intro hlen
    have hpathEq : slot.path = child.path := hslotPrefix.eq_of_length hlen
    apply hne
    cases slot
    cases child
    simp at hpathEq ⊢
    exact hpathEq
  have hslotLenLtChild : slot.path.length < child.path.length :=
    Nat.lt_of_le_of_ne hslotLenLeChild hslotLenNeChild
  have hslotLenLeParent : slot.path.length ≤ parent.path.length := by
    rw [hpath, List.length_append] at hslotLenLtChild
    simp at hslotLenLtChild
    exact hslotLenLtChild
  have hslotParentPrefix : slot.path <+: parent.path :=
    List.prefix_of_prefix_length_le hslotPrefix hparentPrefix hslotLenLeParent
  simpa [LifetimeOutlives, Core.Lifetime.contains] using hslotParentPrefix

/-- Forgetting a lifetime drop: a typing in the dropped environment also types
in the original environment. -/
theorem LValTyping.of_dropLifetime {env : Env} {child : Lifetime} :
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping (env.dropLifetime child) lv pt lf →
      LValTyping env lv pt lf := by
  intro lv pt lf htyping
  induction htyping with
  | var hslot =>
      exact .var (Env.dropLifetime_slotAt_eq_some.mp hslot).1
  | box _ ih => exact .box ih
  | boxFull _ ih => exact .boxFull ih
  | borrow _ _ ihBorrow ihTarget => exact .borrow ihBorrow ihTarget

/-- With the initialized borrow invariant, a typing lifetime is bounded by any
lifetime the base slot outlives: variable and box steps inherit the base slot
lifetime, and a borrow hop's result lifetime is bounded by the hop's borrow
lifetime through the slot invariant. -/
theorem LValTyping.lifetime_le_of_base_outlives_whenInitialized {env : Env}
    {parent : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping env lv pt lf →
      LValBaseOutlives env lv parent →
      lf ≤ parent := by
  intro hcbwf lv pt lf htyping
  induction htyping with
  | var hslot =>
      intro hbase
      rcases hbase with ⟨slot', hslot', hle⟩
      have hEq : _ = slot' := Option.some.inj (hslot.symm.trans hslot')
      exact hEq ▸ hle
  | box _ ih => exact ih
  | boxFull _ ih => exact ih
  | borrow hw hu ihBorrow _ihTarget =>
      intro hbase
      have hlfw := ihBorrow hbase
      have hslotWF :=
        LValTyping.partialTyBorrowsWellFormedInSlotWhenInitialized hcbwf hw
          PartialTyContains.here
      rcases hslotWF.2 ⟨_, _, hu⟩ with ⟨ty₀, lf₀, hty₀, hle₀, _hbase₀⟩
      have hdet := LValTyping.deterministic hu hty₀
      exact LifetimeOutlives.trans (hdet.2 ▸ hle₀) hlfw

/-- Reverse fresh-update transport: a typing in the updated environment whose
base is not the fresh name already types in the original environment (borrow
hops stay away from the fresh name because their targets have live base slots
in the original environment). -/
theorem LValTyping.of_update_fresh {env : Env} {x : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.fresh x →
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping (env.update x slot) lv pt lf →
      LVal.base lv ≠ x →
      LValTyping env lv pt lf := by
  intro hcbwf hfresh lv pt lf htyping
  induction htyping with
  | var hslot' =>
      intro hne
      rename_i y s
      have hne' : y ≠ x := hne
      exact .var (by simpa [Env.update, hne'] using hslot')
  | box _ ih =>
      intro hne
      exact .box (ih hne)
  | boxFull _ ih =>
      intro hne
      exact .boxFull (ih hne)
  | borrow hw hu ihBorrow ihTarget =>
      intro hne
      rename_i w u m blf tlf tty
      have hwOld := ihBorrow hne
      have hslotWF :=
        LValTyping.partialTyBorrowsWellFormedInSlotWhenInitialized hcbwf hwOld
          PartialTyContains.here
      rcases hslotWF.1 with ⟨baseSlot, hbaseSlot, _⟩
      have hbaseNe : LVal.base u ≠ x := by
        intro h
        unfold Env.fresh at hfresh
        rw [h, hfresh] at hbaseSlot
        cases hbaseSlot
      exact .borrow hwOld (ihTarget hbaseNe)

theorem LValBaseOutlives.base_ne_of_fresh {env : Env} {x : Name}
    {target : LVal} {lifetime : Lifetime} :
    env.fresh x →
    LValBaseOutlives env target lifetime →
    LVal.base target ≠ x := by
  intro hfresh hbase h
  rcases hbase with ⟨baseSlot, hbaseSlot, _⟩
  unfold Env.fresh at hfresh
  rw [h, hfresh] at hbaseSlot
  cases hbaseSlot

theorem LValBaseOutlives.update_of_base_ne {env : Env} {x : Name}
    {slot : EnvSlot} {target : LVal} {lifetime : Lifetime} :
    LVal.base target ≠ x →
    LValBaseOutlives env target lifetime →
    LValBaseOutlives (env.update x slot) target lifetime := by
  intro hne hbase
  rcases hbase with ⟨baseSlot, hbaseSlot, hle⟩
  exact ⟨baseSlot, by simpa [Env.update, hne] using hbaseSlot, hle⟩

theorem BorrowTargetsWellFormedInSlotWhenInitialized.update_fresh {env : Env}
    {x : Name} {slot : EnvSlot} {slotLifetime : Lifetime} {target : LVal} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.fresh x →
    BorrowTargetsWellFormedInSlotWhenInitialized env slotLifetime target →
    BorrowTargetsWellFormedInSlotWhenInitialized (env.update x slot)
      slotLifetime target := by
  intro hcbwf hfresh htarget
  rcases htarget with ⟨hbase, hcond⟩
  have hbaseNe := LValBaseOutlives.base_ne_of_fresh hfresh hbase
  refine ⟨LValBaseOutlives.update_of_base_ne hbaseNe hbase, ?_⟩
  rintro ⟨ty', lf', hty'⟩
  have htyOld := LValTyping.of_update_fresh hcbwf hfresh hty' hbaseNe
  rcases hcond ⟨_, _, htyOld⟩ with ⟨ty₀, lf₀, hty₀, hle₀, hbase₀⟩
  exact ⟨ty₀, lf₀, LValTyping.update_fresh_one hfresh hty₀, hle₀,
    LValBaseOutlives.update_of_base_ne hbaseNe hbase₀⟩

theorem ValidPartialValueWhenInitialized.update_fresh_env_of_partialTyBorrows
    {env : Env} {store : ProgramStore} {x : Name} {slot : EnvSlot}
    {slotLifetime : Lifetime} {partialTy : PartialTy}
    {value : PartialValue} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.fresh x →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    ValidPartialValueWhenInitialized env store value partialTy →
    ValidPartialValueWhenInitialized (env.update x slot) store value
      partialTy := by
  intro hcbwf hfresh hpartial hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      exact ValidPartialValueWhenInitialized.undefOf hinner hstrength
  | borrowLive hinitialized hloc =>
      rcases hinitialized with ⟨targetTy, targetLifetime, htarget⟩
      exact ValidPartialValueWhenInitialized.borrowLive
        ⟨targetTy, targetLifetime,
          LValTyping.update_fresh_one (slot := slot) hfresh htarget⟩
        hloc
  | borrowStale hstale =>
      have htarget := hpartial PartialTyContains.here
      have hbaseNe := LValBaseOutlives.base_ne_of_fresh hfresh htarget.1
      exact ValidPartialValueWhenInitialized.borrowStale (by
        rintro ⟨targetTy, targetLifetime, htargetTyping⟩
        exact hstale ⟨targetTy, targetLifetime,
          LValTyping.of_update_fresh hcbwf hfresh htargetTyping hbaseNe⟩)
  | box hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.box hslot
        (ih (PartialTyBorrowsWellFormedInSlotWhenInitialized.box_inv hpartial))
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.boxFull hslot
        (ih (by
          intro mutable target hcontains
          exact hpartial (PartialTyContains.tyBox hcontains)))

theorem ValidPartialValueWhenInitialized.update_fresh_env_of_wellFormedTy
    {env : Env} {store : ProgramStore} {x : Name} {slot : EnvSlot}
    {ty : Ty} {lifetime : Lifetime} {value : Value} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.fresh x →
    WellFormedTyWhenInitialized env ty lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    ValidPartialValueWhenInitialized (env.update x slot) store (.value value)
      (.ty ty) := by
  intro hcbwf hfresh hwell hvalid
  induction hwell generalizing value with
  | unit =>
      cases hvalid
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      cases hvalid
      exact ValidPartialValueWhenInitialized.int
  | borrow htargets =>
      cases hvalid with
      | borrowLive hinitialized hloc =>
          rcases hinitialized with ⟨targetTy, targetLifetime, htarget⟩
          exact ValidPartialValueWhenInitialized.borrowLive
            ⟨targetTy, targetLifetime,
              LValTyping.update_fresh_one (slot := slot) hfresh htarget⟩
            hloc
      | borrowStale hstale =>
          have hbaseNe := LValBaseOutlives.base_ne_of_fresh hfresh htargets.1
          exact ValidPartialValueWhenInitialized.borrowStale (by
            rintro ⟨targetTy, targetLifetime, htarget⟩
            exact hstale ⟨targetTy, targetLifetime,
              LValTyping.of_update_fresh hcbwf hfresh htarget hbaseNe⟩)
  | box hinner ih =>
      cases hvalid with
      | boxFull hslot hvalidInner =>
          rcases validPartialValueWhenInitialized_full_value hvalidInner with
            ⟨innerValue, hinnerValue, _hvalidValue⟩
          exact ValidPartialValueWhenInitialized.boxFull hslot
            (by
              rw [hinnerValue]
              exact ih _hvalidValue)

theorem preservation_declare_redex_runtime_whenInitialized_of_validValue
    {store store' : ProgramStore} {env : Env}
    {lifetime : Lifetime} {x : Name} {value : Value} {ty : Ty} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstraction store env →
    env.fresh x →
    ValidRuntimeState store (.letMut x (.val value)) →
    WellFormedTyWhenInitialized env ty lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    Step store lifetime (.letMut x (.val value)) store' (.val .unit) →
    ValidRuntimeState store' (.val .unit) ∧
      SafeAbstraction store'
        (env.update x { ty := .ty ty, lifetime := lifetime }) ∧
      ValidPartialValueWhenInitialized
        (env.update x { ty := .ty ty, lifetime := lifetime }) store'
        (.value .unit) (.ty .unit) := by
  intro hwell hsafe hfresh hvalidRuntime hwellTy hvalidValue hstep
  have hfreshStore : store.fresh (VariableProjection x) :=
    safeAbstractionWhenInitialized_store_fresh_var hsafe hfresh
  cases hstep with
  | declare hstore' =>
      subst hstore'
      let env' := env.update x { ty := .ty ty, lifetime := lifetime }
      have hvalidDeclaredStore :
          ValidPartialValueWhenInitialized env
            (store.declare x lifetime value) (.value value) (.ty ty) :=
        validPartialValueWhenInitialized_declare hfreshStore hvalidValue
      have hvalidNew :
          ValidPartialValueWhenInitialized env'
            (store.declare x lifetime value) (.value value) (.ty ty) :=
        ValidPartialValueWhenInitialized.update_fresh_env_of_wellFormedTy
          hwell.1 hfresh hwellTy hvalidDeclaredStore
      have hpreserveOld :
          ∀ y envSlot oldValue,
            y ≠ x →
            env.slotAt y = some envSlot →
            store.slotAt (VariableProjection y) =
              some { value := oldValue, lifetime := envSlot.lifetime } →
            ValidPartialValueWhenInitialized env'
              (store.declare x lifetime value) oldValue envSlot.ty := by
        intro y envSlot oldValue hyx henvY hstoreY
        rcases hsafe.2 y envSlot henvY with ⟨safeValue, hsafeY, hvalidOld⟩
        rw [hstoreY] at hsafeY
        injection hsafeY with hsafeValueEq
        have hvalueEq : oldValue = safeValue := by
          cases hsafeValueEq
          rfl
        subst hvalueEq
        have hvalidDeclaredOld :
            ValidPartialValueWhenInitialized env
              (store.declare x lifetime value) oldValue envSlot.ty :=
          validPartialValueWhenInitialized_declare hfreshStore hvalidOld
        have hpartial :
            PartialTyBorrowsWellFormedInSlotWhenInitialized env
              envSlot.lifetime envSlot.ty := by
          intro mutable target hcontains
          exact hwell.1 y envSlot mutable target henvY
            ⟨envSlot, henvY, hcontains⟩
        exact
          ValidPartialValueWhenInitialized.update_fresh_env_of_partialTyBorrows
            hwell.1 hfresh hpartial hvalidDeclaredOld
      exact ⟨validRuntimeState_declare_step_of_validValueWhenInitialized
          hvalidRuntime hfreshStore hvalidValue
          (Step.declare (lifetime := lifetime) rfl),
        safeAbstractionWhenInitialized_declare hsafe hfresh hvalidNew
          hpreserveOld,
        ValidPartialValueWhenInitialized.unit⟩

/--
Weak-runtime preservation for a `let mut` context whose initializer evaluates
to a value and then fires `R-Declare`.
-/
theorem preservation_declare_context_terminal_multistep_runtime_whenInitialized
    {store finalStore : ProgramStore}
    {env₁ env₂ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {finalValue : Value} {ty : Ty} :
    (∀ {midStore value},
      ValidRuntimeState store term →
      ValidStoreTyping store term typing →
      WellFormedEnvWhenInitialized env₁ lifetime →
      SafeAbstraction store env₁ →
      TermTyping env₁ typing lifetime term ty env₂ →
      MultiStep store lifetime term midStore (.val value) →
      TerminalStateSafe midStore value env₂ ty) →
    ValidRuntimeState store (.letMut x term) →
    ValidStoreTyping store (.letMut x term) typing →
    WellFormedEnvWhenInitialized env₁ lifetime →
    WellFormedEnvWhenInitialized env₂ lifetime →
    SafeAbstraction store env₁ →
    WellFormedTyWhenInitialized env₂ ty lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.fresh x →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    MultiStep store lifetime (.letMut x term) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₃ .unit := by
  intro hinnerPreservation hvalidRuntime hvalidStoreTyping hwell₁ hwell₂
    hsafe hwellTy hinnerTyping hfreshOut henv₃ hmulti
  rcases multistep_declare_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hdeclareStep⟩
  rcases hinnerPreservation
      (validRuntimeState_declare_inner hvalidRuntime)
      (validStoreTyping_declare_inner hvalidStoreTyping)
      hwell₁ hsafe hinnerTyping hinnerMulti with
    ⟨hvalidInner, hsafeInner, hvalidValue⟩
  cases hdeclareStep with
  | declare hstore' =>
      rw [henv₃]
      exact
        preservation_declare_redex_runtime_whenInitialized_of_validValue
          hwell₂ hsafeInner hfreshOut
          (validRuntimeState_declare_value_of_value hvalidInner)
          hwellTy hvalidValue
          (Step.declare (lifetime := lifetime) hstore')

theorem borrowTargetsWellFormedInSlotWhenInitialized_of_wellFormedTyWhenInitialized_contains
    {env : Env} {ty : Ty} {lifetime : Lifetime} {mutable : Bool}
    {target : LVal} :
    WellFormedTyWhenInitialized env ty lifetime →
    PartialTyContains (.ty ty) (.borrow mutable target) →
    BorrowTargetsWellFormedInSlotWhenInitialized env lifetime target := by
  intro hwellTy hcontains
  induction hwellTy with
  | unit => cases hcontains
  | int => cases hcontains
  | borrow htargets =>
      cases hcontains with
      | here => exact htargets
  | box _ ih =>
      cases hcontains with
      | tyBox hcontains' => exact ih hcontains'

theorem ContainedBorrowsWellFormedWhenInitialized.update_fresh_ty
    {env : Env} {x : Name} {ty : Ty} {lifetime : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    WellFormedTyWhenInitialized env ty lifetime →
    env.fresh x →
    ContainedBorrowsWellFormedWhenInitialized
      (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hcontained hwellTy hfresh y envSlot mutable target hslot hcontains
  by_cases hy : y = x
  · subst hy
    have hslotEq :
        envSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = envSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hcontainedEq :
        containedSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = containedSlot := by
        simpa [Env.update] using hcontainedSlot
      exact h.symm
    subst hcontainedEq
    exact BorrowTargetsWellFormedInSlotWhenInitialized.update_fresh
      hcontained hfresh
      (borrowTargetsWellFormedInSlotWhenInitialized_of_wellFormedTyWhenInitialized_contains
        hwellTy hcontainsTy)
  · have hslotOld : env.slotAt y = some envSlot := by
      simpa [Env.update, hy] using hslot
    have hcontainsOld : env ⊢ y ↝ Ty.borrow mutable target := by
      rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hcontainedOld : env.slotAt y = some containedSlot := by
        simpa [Env.update, hy] using hcontainedSlot
      exact ⟨containedSlot, hcontainedOld, hcontainsTy⟩
    exact BorrowTargetsWellFormedInSlotWhenInitialized.update_fresh
      hcontained hfresh
      (hcontained y envSlot mutable target hslotOld hcontainsOld)

theorem WellFormedEnvWhenInitialized.update_fresh_ty {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env lifetime →
    WellFormedTyWhenInitialized env ty lifetime →
    env.fresh x →
    WellFormedEnvWhenInitialized
      (env.update x { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro hwellEnv hwellTy hfresh
  refine ⟨ContainedBorrowsWellFormedWhenInitialized.update_fresh_ty
      hwellEnv.1 hwellTy hfresh, ?_⟩
  intro y envSlot hslot
  by_cases hy : y = x
  · subst hy
    have hslotEq :
        envSlot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      have h :
          { ty := PartialTy.ty ty, lifetime := lifetime } = envSlot := by
        simpa [Env.update] using hslot
      exact h.symm
    subst hslotEq
    exact LifetimeOutlives.refl lifetime
  · have hslotOld : env.slotAt y = some envSlot := by
      simpa [Env.update, hy] using hslot
    exact hwellEnv.2 y envSlot hslotOld

/-- Forward lifetime-drop transport for typings whose base outlives the parent
lifetime. -/
theorem LValTyping.dropLifetime_child_whenInitialized {env : Env}
    {parent child : Lifetime} :
    LifetimeChild parent child →
    ContainedBorrowsWellFormedWhenInitialized env →
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping env lv pt lf →
      LValBaseOutlives env lv parent →
      LValTyping (env.dropLifetime child) lv pt lf := by
  intro hchild hcbwf lv pt lf htyping
  induction htyping with
  | var hslot =>
      intro hbase
      rcases hbase with ⟨slot', hslot', hle⟩
      have hEq : _ = slot' := Option.some.inj (hslot.symm.trans hslot')
      refine .var (Env.dropLifetime_slotAt_eq_some.mpr ⟨hslot, ?_⟩)
      intro hlifetimeEq
      exact LifetimeChild.not_child_outlives_parent hchild
        (hlifetimeEq ▸ hEq ▸ hle)
  | box _ ih =>
      intro hbase
      exact .box (ih hbase)
  | boxFull _ ih =>
      intro hbase
      exact .boxFull (ih hbase)
  | borrow hw hu ihBorrow ihTarget =>
      intro hbase
      have hslotWF :=
        LValTyping.partialTyBorrowsWellFormedInSlotWhenInitialized hcbwf hw
          PartialTyContains.here
      have hlfw :=
        LValTyping.lifetime_le_of_base_outlives_whenInitialized hcbwf hw hbase
      rcases hslotWF.2 ⟨_, _, hu⟩ with ⟨ty₀, lf₀, hty₀, _hle₀, hbase₀⟩
      have hbaseU : LValBaseOutlives env _ parent :=
        LValBaseOutlives.weaken hbase₀ hlfw
      exact .borrow (ihBorrow hbase) (ihTarget hbaseU)

theorem BorrowTargetsWellFormedInSlotWhenInitialized.dropLifetime_child
    {env : Env} {parent child slotLifetime : Lifetime} {target : LVal} :
    LifetimeChild parent child →
    ContainedBorrowsWellFormedWhenInitialized env →
    slotLifetime ≤ parent →
    BorrowTargetsWellFormedInSlotWhenInitialized env slotLifetime target →
    BorrowTargetsWellFormedInSlotWhenInitialized (env.dropLifetime child)
      slotLifetime target := by
  intro hchild hcbwf hslotLe htarget
  rcases htarget with ⟨hbase, hcond⟩
  refine ⟨LValBaseOutlives.dropLifetime_child hchild hslotLe hbase, ?_⟩
  rintro ⟨ty', lf', hty'⟩
  have htyOld := LValTyping.of_dropLifetime hty'
  rcases hcond ⟨_, _, htyOld⟩ with ⟨ty₀, lf₀, hty₀, hle₀, hbase₀⟩
  exact ⟨ty₀, lf₀,
    LValTyping.dropLifetime_child_whenInitialized hchild hcbwf hty₀
      (LValBaseOutlives.weaken hbase₀ hslotLe), hle₀,
    LValBaseOutlives.dropLifetime_child hchild hslotLe hbase₀⟩

theorem ContainedBorrowsWellFormedWhenInitialized.dropLifetime_child
    {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    ContainedBorrowsWellFormedWhenInitialized env →
    EnvSlotsOutlive env child →
    ContainedBorrowsWellFormedWhenInitialized (env.dropLifetime child) := by
  intro hchild hcbwf hout x slot mutable target hslot hcontains
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨hold, hne⟩
  have hcontOld : env ⊢ x ↝ Ty.borrow mutable target :=
    EnvContains.dropLifetime_of_contains hcontains
  have hslotParent : slot.lifetime ≤ parent :=
    LifetimeChild.parent_of_outlives_child_ne hchild (hout x slot hold) hne
  exact BorrowTargetsWellFormedInSlotWhenInitialized.dropLifetime_child
    hchild hcbwf hslotParent (hcbwf x slot mutable target hold hcontOld)

theorem WellFormedTyWhenInitialized.dropLifetime_child {env : Env}
    {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    ContainedBorrowsWellFormedWhenInitialized env →
    WellFormedTyWhenInitialized env ty parent →
    WellFormedTyWhenInitialized (env.dropLifetime child) ty parent := by
  intro hchild hcbwf hwellTy
  induction hwellTy with
  | unit => exact .unit
  | int => exact .int
  | borrow htargets =>
      exact .borrow
        (BorrowTargetsWellFormedInSlotWhenInitialized.dropLifetime_child
          hchild hcbwf (LifetimeOutlives.refl _) htargets)
  | box _ ih => exact .box (ih hchild)

theorem block_preserves_wellFormedWhenInitialized {env₂ env₃ : Env}
    {lifetime blockLifetime : Lifetime} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnvWhenInitialized env₂ blockLifetime →
    WellFormedTyWhenInitialized env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnvWhenInitialized env₃ lifetime ∧
      WellFormedTyWhenInitialized env₃ ty lifetime := by
  intro hchild hwellBody hwellTy hdrop
  subst hdrop
  refine ⟨⟨ContainedBorrowsWellFormedWhenInitialized.dropLifetime_child hchild
      hwellBody.1 hwellBody.2, ?_⟩,
    WellFormedTyWhenInitialized.dropLifetime_child hchild hwellBody.1 hwellTy⟩
  intro x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨hold, hne⟩
  exact LifetimeChild.parent_of_outlives_child_ne hchild
    (hwellBody.2 x slot hold) hne

/-! ### Strong-update write: slot lifetime characterization

`EnvWrite.slots_characterize` (P2): every slot of the write result exists in the
source with the same lifetime, and any slot whose type changed has a lifetime
that the written lval's typing lifetime outlives.  The proof threads the
original lval typing down the write recursion: box steps extend the current
spine prefix, and mutable-borrow hops rebase the residual typing onto the hop
target (`LValTyping.rebase_hop`).
-/

@[simp] theorem prependPath_deref_comm :
    ∀ (path : List Unit) (lv : LVal),
      prependPath path (.deref lv) = .deref (prependPath path lv)
  | [], _ => rfl
  | () :: path, lv => by
      simp [prependPath, prependPath_deref_comm path lv]

theorem prependPath_path_base :
    ∀ (lv : LVal), prependPath (LVal.path lv) (.var (LVal.base lv)) = lv
  | .var _ => rfl
  | .deref lv => by
      have hcomm := List.Unit_append_singleton_typing (LVal.path lv)
      simp [LVal.path, LVal.base, hcomm, prependPath,
        prependPath_path_base lv]

/-- Hop rebasing: if `wcur` is typed at a mutable borrow of `target`, then any
typing of a deref tower over `.deref wcur` is also a typing of the same tower
over `target` (the tower descends the hop target's type either way). -/
theorem LValTyping.rebase_hop {env : Env} {wcur target : LVal}
    {mutable : Bool} {borrowLifetime : Lifetime} :
    LValTyping env wcur (.ty (.borrow mutable target)) borrowLifetime →
    ∀ (path : List Unit) {pt : PartialTy} {lf : Lifetime},
      LValTyping env (prependPath path (.deref wcur)) pt lf →
      LValTyping env (prependPath path target) pt lf := by
  intro hwcur path
  induction path with
  | nil =>
      intro pt lf htyping
      cases htyping with
      | box hinner =>
          have hdet := LValTyping.deterministic hwcur hinner
          cases hdet.1
      | boxFull hinner =>
          have hdet := LValTyping.deterministic hwcur hinner
          cases hdet.1
      | borrow hw hu =>
          have hdet := LValTyping.deterministic hwcur hw
          cases hdet.1
          exact hu
  | cons head tail ih =>
      intro pt lf htyping
      rw [show prependPath (head :: tail) (.deref wcur) =
          .deref (prependPath tail (.deref wcur)) from rfl] at htyping
      rw [show prependPath (head :: tail) target =
          .deref (prependPath tail target) from rfl]
      cases htyping with
      | box hinner =>
          exact .box (ih hinner)
      | boxFull hinner =>
          exact .boxFull (ih hinner)
      | borrow hw hu =>
          exact .borrow (ih hw) hu

/-- P2: every slot of a strong-update write result exists in the source with
the same lifetime, and any slot whose type changed is outlived by the written
lval's typing lifetime.  The typing is threaded down the write recursion: box
steps extend the current spine prefix (`LValTyping.box`/`.boxFull`), and
mutable-borrow hops rebase the residual typing onto the hop target
(`LValTyping.rebase_hop`); at each `EnvWrite.intro` the written base slot is
bounded through `LValTyping.lifetime_le_of_base_outlives_whenInitialized`. -/
theorem EnvWrite.slots_characterize {env : Env}
    (hcbwf : ContainedBorrowsWellFormedWhenInitialized env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime} :
    EnvWrite env lhs rhsTy env₃ →
    LValTyping env lhs oldTy targetLifetime →
    ∀ y s₃, env₃.slotAt y = some s₃ →
      ∃ s₂, env.slotAt y = some s₂ ∧ s₂.lifetime = s₃.lifetime ∧
        (s₂.ty = s₃.ty ∨ targetLifetime ≤ s₃.lifetime) := by
  intro hwrite
  exact EnvWrite.rec
    (motive_1 := fun path old _ty result _updated _ =>
      ∀ {wcur : LVal} {pt : PartialTy} {lf lfc : Lifetime},
        LValTyping env wcur old lfc →
        LValTyping env (prependPath path wcur) pt lf →
        ∀ y s₃, result.slotAt y = some s₃ →
          ∃ s₂, env.slotAt y = some s₂ ∧ s₂.lifetime = s₃.lifetime ∧
            (s₂.ty = s₃.ty ∨ lf ≤ s₃.lifetime))
    (motive_2 := fun lv _ty result _ =>
      ∀ {pt : PartialTy} {lf : Lifetime},
        LValTyping env lv pt lf →
        ∀ y s₃, result.slotAt y = some s₃ →
          ∃ s₂, env.slotAt y = some s₂ ∧ s₂.lifetime = s₃.lifetime ∧
            (s₂.ty = s₃.ty ∨ lf ≤ s₃.lifetime))
    (by
      -- strong: the environment is unchanged.
      intro _old _ty wcur pt lf lfc _hwcur _hlhs y s₃ hs₃
      exact ⟨s₃, hs₃, rfl, Or.inl rfl⟩)
    (by
      -- box: extend the spine prefix into the partial box.
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
        wcur pt lf lfc hwcur hlhs y s₃ hs₃
      exact ih (LValTyping.box hwcur)
        (by rw [prependPath_deref_comm]; exact hlhs) y s₃ hs₃)
    (by
      -- boxFull: extend the spine prefix into the full box.
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
        wcur pt lf lfc hwcur hlhs y s₃ hs₃
      exact ih (LValTyping.boxFull hwcur)
        (by rw [prependPath_deref_comm]; exact hlhs) y s₃ hs₃)
    (by
      -- mutBorrow: rebase the residual typing onto the hop target.
      intro _env₂ path writeTarget _ty _hwrite ih
        wcur pt lf lfc hwcur hlhs y s₃ hs₃
      exact ih
        (LValTyping.rebase_hop hwcur path
          (by rw [prependPath_deref_comm]; exact hlhs)) y s₃ hs₃)
    (by
      -- intro: the written base slot keeps its lifetime and is bounded by
      -- the typing lifetime; other slots come from the recursion.
      intro _env₂ lv slot _ty updatedTy hslot hupdate ih pt lf hlv y s₃ hs₃
      have hbound : lf ≤ slot.lifetime :=
        LValTyping.lifetime_le_of_base_outlives_whenInitialized hcbwf hlv
          ⟨slot, hslot, LifetimeOutlives.refl _⟩
      by_cases hy : y = LVal.base lv
      · subst hy
        have hs₃Eq : s₃ = { slot with ty := updatedTy } :=
          (Option.some.inj (by simpa [Env.update] using hs₃)).symm
        subst hs₃Eq
        exact ⟨slot, hslot, rfl, Or.inr hbound⟩
      · have hs₃Mid : _env₂.slotAt y = some s₃ := by
          simpa [Env.update, hy] using hs₃
        exact ih (LValTyping.var hslot)
          (by rw [prependPath_path_base]; exact hlv) y s₃ hs₃Mid)
    hwrite

/-- Strict analogue of the batch-1 extraction: a borrow contained in a
strictly well-formed type has well-formed targets. -/
theorem borrowTargetsWellFormed_of_wellFormedTy_contains
    {env : Env} {ty : Ty} {lifetime : Lifetime} {mutable : Bool}
    {target : LVal} :
    WellFormedTy env ty lifetime →
    PartialTyContains (.ty ty) (.borrow mutable target) →
    BorrowTargetsWellFormed env target lifetime := by
  intro hwellTy hcontains
  induction hwellTy with
  | unit => cases hcontains
  | int => cases hcontains
  | borrow htargets =>
      cases hcontains with
      | here => exact htargets
  | box _ ih =>
      cases hcontains with
      | tyBox hcontains' => exact ih hcontains'

/-- Any borrow contained in a slot of the write result has a base slot that
outlives the containing slot: old-origin borrows through the source invariant,
RHS-origin borrows through the strict well-formedness of the written type and
the P2 lifetime bound. -/
theorem envWrite_contains_baseOutlives {env : Env}
    (hcbwf : ContainedBorrowsWellFormedWhenInitialized env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlhsTy : LValTyping env lhs oldTy targetLifetime)
    (hwellTy : WellFormedTy env rhsTy targetLifetime) :
    ∀ {y : Name} {s₃ : EnvSlot} {mutable : Bool} {u : LVal},
      env₃.slotAt y = some s₃ →
      PartialTyContains s₃.ty (.borrow mutable u) →
      LValBaseOutlives env₃ u s₃.lifetime := by
  intro y s₃ mutable u hs₃ hcontains₃
  rcases EnvWrite.slots_characterize hcbwf hwrite hlhsTy y s₃ hs₃ with
    ⟨s₂, hs₂, hlifeEq, hdisj⟩
  rcases hdisj with htyEq | hbound
  · -- Unchanged slot: the borrow was already contained in the source.
    have hcontains₂ : env ⊢ y ↝ (.borrow mutable u) :=
      ⟨s₂, hs₂, htyEq ▸ hcontains₃⟩
    have hslotWF := hcbwf y s₂ mutable u hs₂ hcontains₂
    have hbase := hslotWF.1
    rw [hlifeEq] at hbase
    exact LValBaseOutlives.write hwrite hbase
  · -- Changed slot: decompose the borrow's origin.
    rcases EnvWrite.contains_borrow_source hwrite ⟨s₃, hs₃, hcontains₃⟩ with
      hrhs | hcontains₂
    · rcases borrowTargetsWellFormed_of_wellFormedTy_contains hwellTy hrhs with
        ⟨targetTy, targetLifetime', _htyping, _houtlives, hbase⟩
      exact LValBaseOutlives.weaken (LValBaseOutlives.write hwrite hbase) hbound
    · rcases hcontains₂ with ⟨s₂', hs₂', hcontainsTy₂⟩
      have hs₂Eq : s₂' = s₂ := Option.some.inj (hs₂'.symm.trans hs₂)
      subst hs₂Eq
      have hslotWF := hcbwf y s₂' mutable u hs₂' ⟨s₂', hs₂', hcontainsTy₂⟩
      have hbase := hslotWF.1
      rw [hlifeEq] at hbase
      exact LValBaseOutlives.write hwrite hbase

/-- Master bound: after a strong-update write, every typing lifetime in the
result environment is bounded by any lifetime its base outlives, and every
borrow contained in a typing's result type has a base slot outliving the
typing's lifetime. -/
theorem envWrite_typing_bound {env : Env}
    (hcbwf : ContainedBorrowsWellFormedWhenInitialized env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlhsTy : LValTyping env lhs oldTy targetLifetime)
    (hwellTy : WellFormedTy env rhsTy targetLifetime) :
    ∀ {t : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping env₃ t pt lf →
      (∀ parent, LValBaseOutlives env₃ t parent → lf ≤ parent) ∧
        (∀ {mutable : Bool} {u : LVal},
          PartialTyContains pt (.borrow mutable u) →
          LValBaseOutlives env₃ u lf) := by
  intro t pt lf htyping
  induction htyping with
  | var hslot =>
      rename_i y s₃
      constructor
      · intro parent hbase
        rcases hbase with ⟨s', hs', hle⟩
        have hEq : _ = s' := Option.some.inj (hslot.symm.trans hs')
        exact hEq ▸ hle
      · intro mutable u hcontains
        exact envWrite_contains_baseOutlives hcbwf hwrite hlhsTy hwellTy
          hslot hcontains
  | box _ ih =>
      refine ⟨ih.1, ?_⟩
      intro mutable u hcontains
      exact ih.2 (PartialTyContains.box hcontains)
  | boxFull _ ih =>
      refine ⟨ih.1, ?_⟩
      intro mutable u hcontains
      exact ih.2 (PartialTyContains.tyBox hcontains)
  | borrow hw hu ihBorrow ihTarget =>
      constructor
      · intro parent hbase
        have hblf := ihBorrow.1 parent hbase
        have hbaseU := ihBorrow.2 PartialTyContains.here
        exact LifetimeOutlives.trans (ihTarget.1 _ hbaseU) hblf
      · intro mutable u hcontains
        exact ihTarget.2 hcontains

/-- The initialized borrow invariant is preserved by the strong-update write:
paper Definition 4.8(i) across T-Assign, with no rule-carried obligations
beyond the paper premises. -/
theorem ContainedBorrowsWellFormedWhenInitialized.envWrite {env : Env}
    (hcbwf : ContainedBorrowsWellFormedWhenInitialized env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlhsTy : LValTyping env lhs oldTy targetLifetime)
    (hwellTy : WellFormedTy env rhsTy targetLifetime) :
    ContainedBorrowsWellFormedWhenInitialized env₃ := by
  intro x slot₃ mutable t hslot₃ hcontains₃
  rcases hcontains₃ with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hslotEq : slot₃ = containedSlot :=
    Option.some.inj (hslot₃.symm.trans hcontainedSlot)
  subst hslotEq
  have hbase : LValBaseOutlives env₃ t slot₃.lifetime :=
    envWrite_contains_baseOutlives hcbwf hwrite hlhsTy hwellTy hslot₃
      hcontainsTy
  refine ⟨hbase, ?_⟩
  rintro ⟨ty', lf', hty'⟩
  have hbound :=
    (envWrite_typing_bound hcbwf hwrite hlhsTy hwellTy hty').1
      slot₃.lifetime hbase
  exact ⟨ty', lf', hty', hbound, hbase⟩

/-- Definition 4.8 across T-Assign's write. -/
theorem WellFormedEnvWhenInitialized.envWrite {env : Env} {current : Lifetime}
    (hwell : WellFormedEnvWhenInitialized env current)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlhsTy : LValTyping env lhs oldTy targetLifetime)
    (hwellTy : WellFormedTy env rhsTy targetLifetime) :
    WellFormedEnvWhenInitialized env₃ current :=
  ⟨ContainedBorrowsWellFormedWhenInitialized.envWrite hwell.1 hwrite hlhsTy
      hwellTy,
    EnvSlotsOutlive.write hwrite hwell.2⟩

theorem LValBaseOutlives.move {env moved : Env} {lv target : LVal}
    {lifetime : Lifetime} :
    EnvMove env lv moved →
    LValBaseOutlives env target lifetime →
    LValBaseOutlives moved target lifetime := by
  intro hmove hbase
  rcases hbase with ⟨sourceSlot, hsourceSlot, houtlives⟩
  rcases hmove with ⟨movedSlot, struck, hmovedSlot, _hstrike, hmoved⟩
  subst hmoved
  by_cases hbaseEq : LVal.base target = LVal.base lv
  · have hslotEq : sourceSlot = movedSlot := by
      rw [hbaseEq] at hsourceSlot
      exact Option.some.inj (hsourceSlot.symm.trans hmovedSlot)
    subst hslotEq
    exact ⟨{ sourceSlot with ty := struck },
      by simp [Env.update, hbaseEq], houtlives⟩
  · exact ⟨sourceSlot, by simpa [Env.update, hbaseEq] using hsourceSlot,
      houtlives⟩

/-- The moved-out type stays well formed in the post-move environment: its
loans cannot conflict with the moved place (they would write-prohibit it), so
typings of its targets transport back to the source environment where the
invariant bounds them. -/
theorem WellFormedTyWhenInitialized.move {env moved : Env} {lv : LVal}
    {ty : Ty} {lifetime : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    EnvMove env lv moved →
    ¬ WriteProhibited env lv →
    (∀ {mutable : Bool} {target : LVal},
      PartialTyContains (.ty ty) (.borrow mutable target) →
      env ⊢ (LVal.base lv) ↝ (.borrow mutable target) ∨
        (∃ x, env ⊢ x ↝ (.borrow mutable target))) →
    WellFormedTyWhenInitialized env ty lifetime →
    WellFormedTyWhenInitialized moved ty lifetime := by
  intro hcbwf hmove hnotWrite hcontained hwellTy
  have hnoConflicts :
      ∀ x mutable target,
        moved ⊢ x ↝ (.borrow mutable target) →
        ¬ target ⋈ lv := by
    intro x mutable target hcontains hconflict
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    exact hnotWrite
      (WriteProhibited.of_contains_conflict
        (EnvMove.contains_borrow_source hmove hslot
          ⟨slot, hslot, hcontainsTy⟩) hconflict)
  induction hwellTy with
  | unit => exact .unit
  | int => exact .int
  | borrow htargets =>
      rename_i mutable' target' lifetime'
      rcases htargets with ⟨hbase, hcond⟩
      have hnoConflictTarget : ¬ target' ⋈ lv := by
        intro hconflict
        rcases hcontained (PartialTyContains.here) with hcont | ⟨x, hcont⟩
        · exact hnotWrite
            (WriteProhibited.of_contains_conflict hcont hconflict)
        · exact hnotWrite
            (WriteProhibited.of_contains_conflict hcont hconflict)
      refine .borrow ⟨LValBaseOutlives.move hmove hbase, ?_⟩
      rintro ⟨ty', lf', hty'⟩
      have htyEnv : LValTyping env target' (.ty ty') lf' :=
        LValTyping.move_to_source_of_no_conflicts hmove hnoConflicts
          hnoConflictTarget hty'
      rcases hcond ⟨_, _, htyEnv⟩ with ⟨ty₀, lf₀, hty₀, hle₀, hbase₀⟩
      have hdet := LValTyping.deterministic htyEnv hty₀
      exact ⟨ty', lf', hty', hdet.2 ▸ hle₀,
        LValBaseOutlives.move hmove hbase₀⟩
  | box _ ih =>
      refine .box (ih ?_)
      intro mutable target hcontains
      exact hcontained (PartialTyContains.tyBox hcontains)

/-- The static invariant walk: source-term typing preserves the two-part
Definition 4.8 invariant and yields a well-formed result type, with no
obligations beyond the rule premises. -/
theorem typingPreservesWellFormedWhenInitialized_of_sourceTerm
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    SourceTerm term →
    WellFormedEnvWhenInitialized env₁ lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime ∧
      WellFormedTyWhenInitialized env₂ ty lifetime := by
  intro hsource hwellFormed htyping
  exact TermTyping.rec
    (motive_1 := fun env _typing lifetime term ty env₂ _ =>
      SourceTerm term →
      WellFormedEnvWhenInitialized env lifetime →
      WellFormedEnvWhenInitialized env₂ lifetime ∧
        WellFormedTyWhenInitialized env₂ ty lifetime)
    (motive_2 := fun env _typing blockLifetime terms ty env₂ _ =>
      SourceTerm (.block blockLifetime terms) →
      WellFormedEnvWhenInitialized env blockLifetime →
      WellFormedEnvWhenInitialized env₂ blockLifetime ∧
        WellFormedTyWhenInitialized env₂ ty blockLifetime)
    (by
      -- T-Const: source values are loan-free.
      intro _env _typing _lifetime value _ty hvalue hsource hwell
      exact ⟨hwell,
        ValueTyping.wellFormedTyWhenInitialized_of_sourceValue
          (hsource value (by simp [termValues])) hvalue⟩)
    (by
      -- T-Copy: the environment is unchanged; the copied type comes from a
      -- typed lvalue.
      intro _env _typing _lifetime _valueLifetime _lv _ty hLv _hcopy _hnotRead
        _hsource hwell
      exact ⟨hwell, LValTyping.wellFormedTyWhenInitialized hwell hLv⟩)
    (by
      -- T-Move.
      intro _env₁ _env₂ _typing _lifetime _valueLifetime lv ty hLv hnotWrite
        hmove _hsource hwell
      refine ⟨WellFormedEnvWhenInitialized.move hwell hmove hnotWrite, ?_⟩
      have hwellTy := LValTyping.wellFormedTyWhenInitialized hwell hLv
      refine WellFormedTyWhenInitialized.move hwell.1 hmove hnotWrite ?_
        hwellTy
      intro mutable target hcontains
      rcases LValTyping.contains_borrow hLv hcontains with ⟨x, hcont⟩
      exact Or.inr ⟨x, hcont⟩)
    (by
      -- T-MutBorrow: the created borrow's target is the typed operand.
      intro _env _typing _lifetime _valueLifetime lv _ty hLv _hmutable
        _hnotWrite _hsource hwell
      refine ⟨hwell, .borrow ⟨?_, ?_⟩⟩
      · rcases LValTyping.base_slot_exists hLv with ⟨slot, hslot⟩
        exact ⟨slot, hslot, hwell.2 _ slot hslot⟩
      · rintro ⟨ty', lf', hty'⟩
        refine ⟨ty', lf', hty',
          LValTyping.lifetime_outlives_one hwell.2 hty', ?_⟩
        rcases LValTyping.base_slot_exists hLv with ⟨slot, hslot⟩
        exact ⟨slot, hslot, hwell.2 _ slot hslot⟩)
    (by
      -- T-ImmBorrow.
      intro _env _typing _lifetime _valueLifetime lv _ty hLv _hnotRead
        _hsource hwell
      refine ⟨hwell, .borrow ⟨?_, ?_⟩⟩
      · rcases LValTyping.base_slot_exists hLv with ⟨slot, hslot⟩
        exact ⟨slot, hslot, hwell.2 _ slot hslot⟩
      · rintro ⟨ty', lf', hty'⟩
        refine ⟨ty', lf', hty',
          LValTyping.lifetime_outlives_one hwell.2 hty', ?_⟩
        rcases LValTyping.base_slot_exists hLv with ⟨slot, hslot⟩
        exact ⟨slot, hslot, hwell.2 _ slot hslot⟩)
    (by
      -- T-Box.
      intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih hsource hwell
      have hresult := ih (SourceTerm.box_inner hsource) hwell
      exact ⟨hresult.1, .box hresult.2⟩)
    (by
      -- T-Block.
      intro _env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty
        hchild _hterms hwellTy hdrop ih hsource hwell
      have hbody := ih hsource
        (WellFormedEnvWhenInitialized.weaken hwell
          (LifetimeChild.outlives hchild))
      exact block_preserves_wellFormedWhenInitialized hchild hbody.1
        (WellFormedTy.whenInitialized hwellTy) hdrop)
    (by
      -- T-Declare.
      intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty _hfresh _hterm
        hfreshOut henv₃ ih hsource hwell
      have hinner := ih (SourceTerm.declare_inner hsource) hwell
      refine ⟨?_, .unit⟩
      rw [henv₃]
      exact WellFormedEnvWhenInitialized.update_fresh_ty hinner.1 hinner.2
        hfreshOut)
    (by
      -- T-Assign: Definition 4.8 across the strong-update write.
      intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy
        _rhs _rhsTy hRhs hLhsPost _hshape hwellTy hwrite _hnotWrite ih
        hsource hwell
      have hmid := ih (SourceTerm.assign_inner hsource) hwell
      exact ⟨WellFormedEnvWhenInitialized.envWrite hmid.1 hwrite hLhsPost
          hwellTy, .unit⟩)
    (by
      -- T-Seq singleton.
      intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih hsource hwell
      exact ih (SourceTerm.block_head hsource) hwell)
    (by
      -- T-Seq cons.
      intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
        _hterm _hrest ihHead ihRest hsource hwell
      have hhead := ihHead (SourceTerm.block_head hsource) hwell
      exact ihRest (SourceTerm.block_tail hsource) hhead.1)
    htyping hsource hwellFormed

/-! ### Strict collapse: foundation twins

Strict counterparts of the initialized-conditional projection and bound
lemmas.  With single-target borrows and no joins, moved-out borrow targets
cannot arise, so the strict (paper) predicates are maintainable and the
conditional family becomes obsolete.
-/

theorem LValTyping.partialTyBorrowsWellFormedInSlot {env : Env} :
    ContainedBorrowsWellFormed env →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
      PartialTyBorrowsWellFormedInSlot env lifetime partialTy := by
  intro hcontained lv partialTy lifetime htyping
  induction htyping with
  | var hslot =>
      intro mutable target hcontains
      exact hcontained _ _ mutable target hslot ⟨_, hslot, hcontains⟩
  | box _ ih =>
      exact PartialTyBorrowsWellFormedInSlot.box_inv ih
  | boxFull _ ih =>
      intro mutable target hcontains
      exact ih (PartialTyContains.tyBox hcontains)
  | borrow _ _ _ ihTarget =>
      exact ihTarget

theorem wellFormedTy_of_partialTyBorrows
    {env : Env} {ty : Ty} {lifetime : Lifetime} :
    PartialTyBorrowsWellFormedInSlot env lifetime (.ty ty) →
    WellFormedTy env ty lifetime := by
  exact Ty.rec
    (motive_1 := fun ty =>
      PartialTyBorrowsWellFormedInSlot env lifetime (.ty ty) →
      WellFormedTy env ty lifetime)
    (motive_2 := fun _partialTy => True)
    (by
      intro _hborrows
      exact WellFormedTy.unit)
    (by
      intro _hborrows
      exact WellFormedTy.int)
    (by
      intro mutable target hborrows
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
          (hborrows PartialTyContains.here) (LifetimeOutlives.refl _)))
    (by
      intro inner ih hborrows
      exact WellFormedTy.box
        (ih (by
          intro mutable target hcontains
          exact hborrows (PartialTyContains.tyBox hcontains))))
    (by intro _type _ih; trivial)
    (by intro _inner _ih; trivial)
    (by intro _shape _ih; trivial)
    ty

theorem LValTyping.wellFormedTy {env : Env}
    {current : Lifetime} {lv : LVal} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env current →
    LValTyping env lv (.ty ty) lifetime →
    WellFormedTy env ty current := by
  intro hwell htyping
  have hselected :
      PartialTyBorrowsWellFormedInSlot env lifetime (.ty ty) :=
    LValTyping.partialTyBorrowsWellFormedInSlot hwell.1 htyping
  have hty : WellFormedTy env ty lifetime :=
    wellFormedTy_of_partialTyBorrows hselected
  exact WellFormedTy.weaken hty
    (LValTyping.lifetime_outlives_one hwell.2 htyping)

/-- Strict twin of the initialized lifetime bound: with the strict borrow
invariant the hop case reads the target's typing bound directly. -/
theorem LValTyping.lifetime_le_of_base_outlives {env : Env}
    {parent : Lifetime} :
    ContainedBorrowsWellFormed env →
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping env lv pt lf →
      LValBaseOutlives env lv parent →
      lf ≤ parent := by
  intro hcbwf lv pt lf htyping
  induction htyping with
  | var hslot =>
      intro hbase
      rcases hbase with ⟨slot', hslot', hle⟩
      have hEq : _ = slot' := Option.some.inj (hslot.symm.trans hslot')
      exact hEq ▸ hle
  | box _ ih => exact ih
  | boxFull _ ih => exact ih
  | borrow hw hu ihBorrow _ihTarget =>
      intro hbase
      have hlfw := ihBorrow hbase
      have hslotWF :=
        LValTyping.partialTyBorrowsWellFormedInSlot hcbwf hw
          PartialTyContains.here
      rcases hslotWF with ⟨ty₀, lf₀, hty₀, hle₀, _hbase₀⟩
      have hdet := LValTyping.deterministic hu hty₀
      exact LifetimeOutlives.trans (hdet.2 ▸ hle₀) hlfw

/-- Strict P2 for writes: every result slot comes from a source slot with the
same lifetime, and changed slots are outlived by the written lvalue's typing
lifetime. -/
theorem EnvWrite.slots_characterize_strict {env : Env}
    (hcbwf : ContainedBorrowsWellFormed env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime} :
    EnvWrite env lhs rhsTy env₃ →
    LValTyping env lhs oldTy targetLifetime →
    ∀ y s₃, env₃.slotAt y = some s₃ →
      ∃ s₂, env.slotAt y = some s₂ ∧ s₂.lifetime = s₃.lifetime ∧
        (s₂.ty = s₃.ty ∨ targetLifetime ≤ s₃.lifetime) := by
  intro hwrite
  exact EnvWrite.rec
    (motive_1 := fun path old _ty result _updated _ =>
      ∀ {wcur : LVal} {pt : PartialTy} {lf lfc : Lifetime},
        LValTyping env wcur old lfc →
        LValTyping env (prependPath path wcur) pt lf →
        ∀ y s₃, result.slotAt y = some s₃ →
          ∃ s₂, env.slotAt y = some s₂ ∧ s₂.lifetime = s₃.lifetime ∧
            (s₂.ty = s₃.ty ∨ lf ≤ s₃.lifetime))
    (motive_2 := fun lv _ty result _ =>
      ∀ {pt : PartialTy} {lf : Lifetime},
        LValTyping env lv pt lf →
        ∀ y s₃, result.slotAt y = some s₃ →
          ∃ s₂, env.slotAt y = some s₂ ∧ s₂.lifetime = s₃.lifetime ∧
            (s₂.ty = s₃.ty ∨ lf ≤ s₃.lifetime))
    (by
      intro _old _ty wcur pt lf lfc _hwcur _hlhs y s₃ hs₃
      exact ⟨s₃, hs₃, rfl, Or.inl rfl⟩)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
        wcur pt lf lfc hwcur hlhs y s₃ hs₃
      exact ih (LValTyping.box hwcur)
        (by rw [prependPath_deref_comm]; exact hlhs) y s₃ hs₃)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
        wcur pt lf lfc hwcur hlhs y s₃ hs₃
      exact ih (LValTyping.boxFull hwcur)
        (by rw [prependPath_deref_comm]; exact hlhs) y s₃ hs₃)
    (by
      intro _env₂ path writeTarget _ty _hwrite ih
        wcur pt lf lfc hwcur hlhs y s₃ hs₃
      exact ih
        (LValTyping.rebase_hop hwcur path
          (by rw [prependPath_deref_comm]; exact hlhs)) y s₃ hs₃)
    (by
      intro _env₂ lv slot _ty updatedTy hslot _hupdate ih pt lf hlv y s₃ hs₃
      have hbound : lf ≤ slot.lifetime :=
        LValTyping.lifetime_le_of_base_outlives hcbwf hlv
          ⟨slot, hslot, LifetimeOutlives.refl _⟩
      by_cases hy : y = LVal.base lv
      · subst hy
        have hs₃Eq : s₃ = { slot with ty := updatedTy } :=
          (Option.some.inj (by simpa [Env.update] using hs₃)).symm
        subst hs₃Eq
        exact ⟨slot, hslot, rfl, Or.inr hbound⟩
      · have hs₃Mid : _env₂.slotAt y = some s₃ := by
          simpa [Env.update, hy] using hs₃
        exact ih (LValTyping.var hslot)
          (by rw [prependPath_path_base]; exact hlv) y s₃ hs₃Mid)
    hwrite

/-- Strict write base bound: every borrow contained in the result has a base
slot that outlives the containing result slot. -/
theorem envWrite_contains_baseOutlives_strict {env : Env}
    (hcbwf : ContainedBorrowsWellFormed env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlhsTy : LValTyping env lhs oldTy targetLifetime)
    (hwellTy : WellFormedTy env rhsTy targetLifetime) :
    ∀ {y : Name} {s₃ : EnvSlot} {mutable : Bool} {u : LVal},
      env₃.slotAt y = some s₃ →
      PartialTyContains s₃.ty (.borrow mutable u) →
      LValBaseOutlives env₃ u s₃.lifetime := by
  intro y s₃ mutable u hs₃ hcontains₃
  rcases EnvWrite.slots_characterize_strict hcbwf hwrite hlhsTy y s₃ hs₃ with
    ⟨s₂, hs₂, hlifeEq, hdisj⟩
  rcases hdisj with htyEq | hbound
  · have hcontains₂ : env ⊢ y ↝ (.borrow mutable u) :=
      ⟨s₂, hs₂, htyEq ▸ hcontains₃⟩
    rcases hcbwf y s₂ mutable u hs₂ hcontains₂ with
      ⟨_targetTy, _targetLifetime, _htyping, _houtlives, hbase⟩
    rw [hlifeEq] at hbase
    exact LValBaseOutlives.write hwrite hbase
  · rcases EnvWrite.contains_borrow_source hwrite ⟨s₃, hs₃, hcontains₃⟩ with
      hrhs | hcontains₂
    · rcases borrowTargetsWellFormed_of_wellFormedTy_contains hwellTy hrhs with
        ⟨_targetTy, _targetLifetime, _htyping, _houtlives, hbase⟩
      exact LValBaseOutlives.weaken (LValBaseOutlives.write hwrite hbase) hbound
    · rcases hcontains₂ with ⟨s₂', hs₂', hcontainsTy₂⟩
      have hs₂Eq : s₂' = s₂ := Option.some.inj (hs₂'.symm.trans hs₂)
      subst hs₂Eq
      rcases hcbwf y s₂' mutable u hs₂'
          ⟨s₂', hs₂', hcontainsTy₂⟩ with
        ⟨_targetTy, _targetLifetime, _htyping, _houtlives, hbase⟩
      rw [hlifeEq] at hbase
      exact LValBaseOutlives.write hwrite hbase

/-- Strict write typing bound: post-write lvalue typings have bounded
lifetimes, and borrows contained in their output types have live bases. -/
theorem envWrite_typing_bound_strict {env : Env}
    (hcbwf : ContainedBorrowsWellFormed env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlhsTy : LValTyping env lhs oldTy targetLifetime)
    (hwellTy : WellFormedTy env rhsTy targetLifetime) :
    ∀ {t : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping env₃ t pt lf →
      (∀ parent, LValBaseOutlives env₃ t parent → lf ≤ parent) ∧
        (∀ {mutable : Bool} {u : LVal},
          PartialTyContains pt (.borrow mutable u) →
          LValBaseOutlives env₃ u lf) := by
  intro t pt lf htyping
  induction htyping with
  | var hslot =>
      rename_i y s₃
      constructor
      · intro parent hbase
        rcases hbase with ⟨s', hs', hle⟩
        have hEq : _ = s' := Option.some.inj (hslot.symm.trans hs')
        exact hEq ▸ hle
      · intro mutable u hcontains
        exact envWrite_contains_baseOutlives_strict hcbwf hwrite hlhsTy
          hwellTy hslot hcontains
  | box _ ih =>
      refine ⟨ih.1, ?_⟩
      intro mutable u hcontains
      exact ih.2 (PartialTyContains.box hcontains)
  | boxFull _ ih =>
      refine ⟨ih.1, ?_⟩
      intro mutable u hcontains
      exact ih.2 (PartialTyContains.tyBox hcontains)
  | borrow hw hu ihBorrow ihTarget =>
      constructor
      · intro parent hbase
        have hblf := ihBorrow.1 parent hbase
        have hbaseU := ihBorrow.2 PartialTyContains.here
        exact LifetimeOutlives.trans (ihTarget.1 _ hbaseU) hblf
      · intro mutable u hcontains
        exact ihTarget.2 hcontains

namespace EnvWriteStrictCounterexample

private def l : Lifetime := [0]
private def p : LVal := .var "p"
private def q : LVal := .var "q"
private def r : LVal := .var "r"

private def pSlot : EnvSlot :=
  { ty := .ty (.borrow true q), lifetime := l }

private def qSlot : EnvSlot :=
  { ty := .ty (.borrow true r), lifetime := l }

private def rSlot : EnvSlot :=
  { ty := .ty .int, lifetime := l }

private def env : Env :=
  ((Env.empty.update "r" rSlot).update "q" qSlot).update "p" pSlot

private def rhsTy : Ty := .borrow true (.deref q)

private def envAfterQ : Env :=
  env.update "q" { ty := .ty rhsTy, lifetime := l }

private def result : Env :=
  envAfterQ.update "p" pSlot

private theorem env_slot_p : env.slotAt "p" = some pSlot := by
  simp [env, Env.update]

private theorem env_slot_q : env.slotAt "q" = some qSlot := by
  simp [env, Env.update]

private theorem env_slot_r : env.slotAt "r" = some rSlot := by
  simp [env, Env.update]

private theorem result_slot_p : result.slotAt "p" = some pSlot := by
  simp [result, envAfterQ, Env.update]

private theorem result_slot_q :
    result.slotAt "q" = some { ty := .ty rhsTy, lifetime := l } := by
  simp [result, envAfterQ, Env.update]

private theorem result_slot_r : result.slotAt "r" = some rSlot := by
  simp [result, envAfterQ, env, Env.update]

private theorem env_q_typing :
    LValTyping env q (.ty (.borrow true r)) l := by
  exact LValTyping.var (slot := qSlot) env_slot_q

private theorem env_r_typing :
    LValTyping env r (.ty .int) l := by
  exact LValTyping.var (slot := rSlot) env_slot_r

private theorem env_deref_q_typing :
    LValTyping env (.deref q) (.ty .int) l := by
  exact LValTyping.borrow env_q_typing env_r_typing

private theorem env_p_typing :
    LValTyping env p (.ty (.borrow true q)) l := by
  exact LValTyping.var (slot := pSlot) env_slot_p

private theorem lhs_typing :
    LValTyping env (.deref p) (.ty (.borrow true r)) l := by
  exact LValTyping.borrow env_p_typing env_q_typing

private theorem shape :
    ShapeCompatible env (.ty (.borrow true r)) (.ty rhsTy) := by
  unfold rhsTy
  exact ShapeCompatible.borrow ⟨l, env_r_typing⟩
    ⟨l, env_deref_q_typing⟩ ShapeCompatible.int

private theorem rhs_wellFormed :
    WellFormedTy env rhsTy l := by
  unfold rhsTy
  refine WellFormedTy.borrow (BorrowTargetsWellFormed.singleton
    env_deref_q_typing (LifetimeOutlives.refl _) ?_)
  exact ⟨qSlot, by
    change env.slotAt "q" = some qSlot
    exact env_slot_q, LifetimeOutlives.refl _⟩

private theorem source_containedBorrowsWellFormed :
    ContainedBorrowsWellFormed env := by
  intro x slot mutable target hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hxp : x = "p"
  · subst hxp
    have hslotEq : slot = pSlot := by
      exact Option.some.inj (hslot.symm.trans env_slot_p)
    have hcontainedEq : containedSlot = pSlot := by
      exact Option.some.inj (hcontainedSlot.symm.trans env_slot_p)
    subst hslotEq
    subst hcontainedEq
    cases hcontainsTy with
    | here =>
        exact ⟨.borrow true r, l, env_q_typing, LifetimeOutlives.refl _,
          ⟨qSlot, by
            change env.slotAt "q" = some qSlot
            exact env_slot_q, LifetimeOutlives.refl _⟩⟩
  · by_cases hxq : x = "q"
    · subst hxq
      have hslotEq : slot = qSlot := by
        exact Option.some.inj (hslot.symm.trans env_slot_q)
      have hcontainedEq : containedSlot = qSlot := by
        exact Option.some.inj (hcontainedSlot.symm.trans env_slot_q)
      subst hslotEq
      subst hcontainedEq
      cases hcontainsTy with
      | here =>
          exact ⟨.int, l, env_r_typing, LifetimeOutlives.refl _,
            ⟨rSlot, by
              change env.slotAt "r" = some rSlot
              exact env_slot_r, LifetimeOutlives.refl _⟩⟩
    · by_cases hxr : x = "r"
      · subst hxr
        have hcontainedEq : containedSlot = rSlot := by
          exact Option.some.inj (hcontainedSlot.symm.trans env_slot_r)
        subst hcontainedEq
        cases hcontainsTy
      · have hnone : env.slotAt x = none := by
          simp [env, Env.update, Env.empty, hxp, hxq, hxr]
        rw [hnone] at hslot
        cases hslot

private theorem write :
    EnvWrite env (.deref p) rhsTy result := by
  have hinner : EnvWrite env q rhsTy envAfterQ := by
    unfold envAfterQ
    simpa [q, qSlot, LVal.base] using
      (EnvWrite.intro
        (env₁ := env) (env₂ := env) (lv := q) (slot := qSlot)
        (ty := rhsTy) (updatedTy := .ty rhsTy)
        (by
          change env.slotAt "q" = some qSlot
          exact env_slot_q)
        (by
          unfold qSlot
          exact UpdateAtPath.strong))
  have hupdate :
      UpdateAtPath env (LVal.path (.deref p)) pSlot.ty rhsTy envAfterQ
        pSlot.ty := by
    change UpdateAtPath env [()] (.ty (.borrow true q)) rhsTy envAfterQ
      (.ty (.borrow true q))
    exact UpdateAtPath.mutBorrow hinner
  simpa [result, p, pSlot, q, LVal.base, LVal.path] using
    (EnvWrite.intro
      (env₁ := env) (env₂ := envAfterQ) (lv := .deref p) (slot := pSlot)
      (ty := rhsTy) (updatedTy := pSlot.ty)
      (by
        change env.slotAt "p" = some pSlot
        exact env_slot_p)
      hupdate)

private theorem result_contains_borrow_base_ne_p
    {x : Name} {mutable : Bool} {target : LVal} :
    result ⊢ x ↝ (.borrow mutable target) →
    LVal.base target ≠ "p" := by
  intro hcontains hbase
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hxp : x = "p"
  · subst hxp
    have hslotEq : slot = pSlot := by
      exact Option.some.inj (hslot.symm.trans result_slot_p)
    subst hslotEq
    cases hcontainsTy with
    | here =>
        simp [q, LVal.base] at hbase
  · by_cases hxq : x = "q"
    · subst hxq
      have hslotEq : slot = { ty := .ty rhsTy, lifetime := l } := by
        exact Option.some.inj (hslot.symm.trans result_slot_q)
      subst hslotEq
      cases hcontainsTy with
      | here =>
          simp [q, LVal.base] at hbase
    · by_cases hxr : x = "r"
      · subst hxr
        have hslotEq : slot = rSlot := by
          exact Option.some.inj (hslot.symm.trans result_slot_r)
        subst hslotEq
        cases hcontainsTy
      · simp [result, envAfterQ, env, Env.empty, pSlot, qSlot, rSlot, l,
          hxp, hxq, hxr] at hslot

private theorem result_q_typing :
    LValTyping result q (.ty rhsTy) l := by
  exact LValTyping.var result_slot_q

private theorem result_not_writeProhibited :
    ¬ WriteProhibited result (.deref p) := by
  intro hwriteProhibited
  rcases hwriteProhibited with hread | himm
  · rcases hread with ⟨x, target, hcontains, hconflict⟩
    exact result_contains_borrow_base_ne_p hcontains
      (by simpa [PathConflicts, p, LVal.base] using hconflict)
  · rcases himm with ⟨x, target, hcontains, hconflict⟩
    exact result_contains_borrow_base_ne_p hcontains
      (by simpa [PathConflicts, p, LVal.base] using hconflict)

private theorem no_result_deref_q_typing :
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping result lv pt lf →
      lv = .deref q →
      False := by
  intro lv pt lf htyping
  induction htyping with
  | var _hslot =>
      intro hlv
      cases hlv
  | box hsource _ih =>
      intro hlv
      cases hlv
      have hdet := LValTyping.deterministic hsource result_q_typing
      cases hdet.1
  | boxFull hsource _ih =>
      intro hlv
      cases hlv
      have hdet := LValTyping.deterministic hsource result_q_typing
      unfold rhsTy at hdet
      cases hdet.1
  | borrow hsource _htarget _ihSource ihTarget =>
      intro hlv
      cases hlv
      have hdet := LValTyping.deterministic hsource result_q_typing
      unfold rhsTy at hdet
      cases hdet.1
      exact ihTarget rfl

private theorem result_not_containedBorrowsWellFormed :
    ¬ ContainedBorrowsWellFormed result := by
  intro hcbwf
  have hslotQ :
      result.slotAt "q" = some { ty := .ty rhsTy, lifetime := l } := by
    simp [result, envAfterQ, env, pSlot, qSlot, rSlot, l]
  have hcontainsQ : result ⊢ "q" ↝ (.borrow true (.deref q)) :=
    ⟨{ ty := .ty rhsTy, lifetime := l }, hslotQ, by
      unfold rhsTy
      exact PartialTyContains.here⟩
  rcases hcbwf "q" { ty := .ty rhsTy, lifetime := l } true (.deref q)
      hslotQ hcontainsQ with
    ⟨targetTy, targetLifetime, htyping, _hle, _hbase⟩
  exact no_result_deref_q_typing htyping rfl

/-- The current assign/write premises are insufficient for strict preservation:
they allow a write through `*p` that installs `q : &mut *q`.  The post-write
`WriteProhibited` check for `*p` does not reject it, but the result is not
strictly `ContainedBorrowsWellFormed` because the target `*q` is no longer
typable. -/
theorem strict_envWrite_target_preservation_counterexample :
    ∃ env₀ env₃ lhs oldTy targetLifetime rhsTy,
      ContainedBorrowsWellFormed env₀ ∧
        EnvWrite env₀ lhs rhsTy env₃ ∧
        LValTyping env₀ lhs oldTy targetLifetime ∧
        ShapeCompatible env₀ oldTy (.ty rhsTy) ∧
        WellFormedTy env₀ rhsTy targetLifetime ∧
        ¬ WriteProhibited env₃ lhs ∧
        ¬ ContainedBorrowsWellFormed env₃ := by
  exact ⟨env, result, .deref p, .ty (.borrow true r), l, rhsTy,
    source_containedBorrowsWellFormed, write, lhs_typing, shape,
    rhs_wellFormed, result_not_writeProhibited,
    result_not_containedBorrowsWellFormed⟩

private def z : LVal := .var "z"

private def zSlot : EnvSlot :=
  { ty := .ty rhsTy, lifetime := l }

private def envWithZ : Env :=
  env.update "z" zSlot

private def movedZ : Env :=
  envWithZ.update "z" { ty := .undef rhsTy, lifetime := l }

private def afterMovedQ : Env :=
  movedZ.update "q" { ty := .ty rhsTy, lifetime := l }

private def resultMoved : Env :=
  afterMovedQ.update "p" pSlot

private theorem envWithZ_slot_z : envWithZ.slotAt "z" = some zSlot := by
  simp [envWithZ, Env.update]

private theorem envWithZ_slot_p : envWithZ.slotAt "p" = some pSlot := by
  simp [envWithZ, env, Env.update]

private theorem envWithZ_slot_q : envWithZ.slotAt "q" = some qSlot := by
  simp [envWithZ, env, Env.update]

private theorem envWithZ_slot_r : envWithZ.slotAt "r" = some rSlot := by
  simp [envWithZ, env, Env.update]

private theorem movedZ_slot_z :
    movedZ.slotAt "z" = some { ty := .undef rhsTy, lifetime := l } := by
  simp [movedZ, envWithZ, Env.update]

private theorem movedZ_slot_p : movedZ.slotAt "p" = some pSlot := by
  simp [movedZ, envWithZ, env, Env.update]

private theorem movedZ_slot_q : movedZ.slotAt "q" = some qSlot := by
  simp [movedZ, envWithZ, env, Env.update]

private theorem movedZ_slot_r : movedZ.slotAt "r" = some rSlot := by
  simp [movedZ, envWithZ, env, Env.update]

private theorem resultMoved_slot_p : resultMoved.slotAt "p" = some pSlot := by
  simp [resultMoved, afterMovedQ, Env.update]

private theorem resultMoved_slot_q :
    resultMoved.slotAt "q" = some { ty := .ty rhsTy, lifetime := l } := by
  simp [resultMoved, afterMovedQ, Env.update]

private theorem resultMoved_slot_r : resultMoved.slotAt "r" = some rSlot := by
  simp [resultMoved, afterMovedQ, movedZ, envWithZ, env, Env.update]

private theorem resultMoved_slot_z :
    resultMoved.slotAt "z" = some { ty := .undef rhsTy, lifetime := l } := by
  simp [resultMoved, afterMovedQ, movedZ, envWithZ, Env.update]

private theorem envWithZ_z_typing :
    LValTyping envWithZ z (.ty rhsTy) l := by
  exact LValTyping.var (slot := zSlot) envWithZ_slot_z

private theorem moved_q_typing :
    LValTyping movedZ q (.ty (.borrow true r)) l := by
  exact LValTyping.var (slot := qSlot) movedZ_slot_q

private theorem moved_r_typing :
    LValTyping movedZ r (.ty .int) l := by
  exact LValTyping.var (slot := rSlot) movedZ_slot_r

private theorem moved_deref_q_typing :
    LValTyping movedZ (.deref q) (.ty .int) l := by
  exact LValTyping.borrow moved_q_typing moved_r_typing

private theorem moved_p_typing :
    LValTyping movedZ p (.ty (.borrow true q)) l := by
  exact LValTyping.var (slot := pSlot) movedZ_slot_p

private theorem moved_lhs_typing :
    LValTyping movedZ (.deref p) (.ty (.borrow true r)) l := by
  exact LValTyping.borrow moved_p_typing moved_q_typing

private theorem moved_shape :
    ShapeCompatible movedZ (.ty (.borrow true r)) (.ty rhsTy) := by
  unfold rhsTy
  exact ShapeCompatible.borrow ⟨l, moved_r_typing⟩
    ⟨l, moved_deref_q_typing⟩ ShapeCompatible.int

private theorem moved_rhs_wellFormed :
    WellFormedTy movedZ rhsTy l := by
  unfold rhsTy
  refine WellFormedTy.borrow (BorrowTargetsWellFormed.singleton
    moved_deref_q_typing (LifetimeOutlives.refl _) ?_)
  exact ⟨qSlot, by
    change movedZ.slotAt "q" = some qSlot
    exact movedZ_slot_q, LifetimeOutlives.refl _⟩

private theorem env_slotsOutlive : EnvSlotsOutlive env l := by
  intro x slot hslot
  by_cases hxp : x = "p"
  · subst hxp
    have hslotEq : slot = pSlot :=
      Option.some.inj (hslot.symm.trans env_slot_p)
    subst hslotEq
    simpa [pSlot] using LifetimeOutlives.refl l
  · by_cases hxq : x = "q"
    · subst hxq
      have hslotEq : slot = qSlot :=
        Option.some.inj (hslot.symm.trans env_slot_q)
      subst hslotEq
      simpa [qSlot] using LifetimeOutlives.refl l
    · by_cases hxr : x = "r"
      · subst hxr
        have hslotEq : slot = rSlot :=
          Option.some.inj (hslot.symm.trans env_slot_r)
        subst hslotEq
        simpa [rSlot] using LifetimeOutlives.refl l
      · have hnone : env.slotAt x = none := by
          simp [env, Env.update, Env.empty, hxp, hxq, hxr]
        rw [hnone] at hslot
        cases hslot

private theorem env_wellFormed : WellFormedEnv env l :=
  ⟨source_containedBorrowsWellFormed, env_slotsOutlive⟩

private theorem env_fresh_z : env.fresh "z" := by
  simp [Env.fresh, env, Env.update, Env.empty]

private theorem envWithZ_wellFormed : WellFormedEnv envWithZ l := by
  simpa [envWithZ, zSlot] using
    (WellFormedEnv.update_fresh_ty
      (x := "z") env_wellFormed rhs_wellFormed env_fresh_z)

private theorem envWithZ_not_borrowSafe : ¬ BorrowSafeEnv envWithZ := by
  intro hsafe
  have hp : envWithZ ⊢ "p" ↝ (.borrow true q) :=
    ⟨pSlot, envWithZ_slot_p, by
      unfold pSlot
      exact PartialTyContains.here⟩
  have hz : envWithZ ⊢ "z" ↝ (.borrow true (.deref q)) :=
    ⟨zSlot, envWithZ_slot_z, by
      unfold zSlot rhsTy
      exact PartialTyContains.here⟩
  have hpz : ("p" : Name) = "z" :=
    hsafe "p" "z" true q (.deref q) hp hz
      (by simp [PathConflicts, q, LVal.base])
  simp at hpz

private theorem envWithZ_contains_borrow_base_ne_z
    {x : Name} {mutable : Bool} {target : LVal} :
    envWithZ ⊢ x ↝ (.borrow mutable target) →
    LVal.base target ≠ "z" := by
  intro hcontains hbase
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hxz : x = "z"
  · subst hxz
    have hslotEq : slot = zSlot := by
      exact Option.some.inj (hslot.symm.trans envWithZ_slot_z)
    subst hslotEq
    cases hcontainsTy with
    | here =>
        simp [q, LVal.base] at hbase
  · by_cases hxp : x = "p"
    · subst hxp
      have hslotEq : slot = pSlot := by
        exact Option.some.inj (hslot.symm.trans envWithZ_slot_p)
      subst hslotEq
      cases hcontainsTy with
      | here =>
          simp [q, LVal.base] at hbase
    · by_cases hxq : x = "q"
      · subst hxq
        have hslotEq : slot = qSlot := by
          exact Option.some.inj (hslot.symm.trans envWithZ_slot_q)
        subst hslotEq
        cases hcontainsTy with
        | here =>
            simp [r, LVal.base] at hbase
      · by_cases hxr : x = "r"
        · subst hxr
          have hslotEq : slot = rSlot := by
            exact Option.some.inj (hslot.symm.trans envWithZ_slot_r)
          subst hslotEq
          cases hcontainsTy
        · simp [envWithZ, env, Env.empty, pSlot, qSlot, rSlot, zSlot, l,
            hxp, hxq, hxr, hxz] at hslot

private theorem envWithZ_not_writeProhibited_z :
    ¬ WriteProhibited envWithZ z := by
  intro hwriteProhibited
  rcases hwriteProhibited with hread | himm
  · rcases hread with ⟨x, target, hcontains, hconflict⟩
    exact envWithZ_contains_borrow_base_ne_z hcontains
      (by simpa [PathConflicts, z, LVal.base] using hconflict)
  · rcases himm with ⟨x, target, hcontains, hconflict⟩
    exact envWithZ_contains_borrow_base_ne_z hcontains
      (by simpa [PathConflicts, z, LVal.base] using hconflict)

private theorem move_z : EnvMove envWithZ z movedZ := by
  refine ⟨zSlot, .undef rhsTy, ?_, ?_, ?_⟩
  · exact envWithZ_slot_z
  · change Strike [] zSlot.ty (.undef rhsTy)
    simp [zSlot, Strike]
  · simp [movedZ, z, zSlot, LVal.base]

private theorem rhs_move_typing :
    TermTyping envWithZ StoreTyping.empty l (.move z) rhsTy movedZ := by
  exact TermTyping.move envWithZ_z_typing
    envWithZ_not_writeProhibited_z move_z

private theorem write_moved :
    EnvWrite movedZ (.deref p) rhsTy resultMoved := by
  have hinner : EnvWrite movedZ q rhsTy afterMovedQ := by
    unfold afterMovedQ
    simpa [q, qSlot, LVal.base] using
      (EnvWrite.intro
        (env₁ := movedZ) (env₂ := movedZ) (lv := q) (slot := qSlot)
        (ty := rhsTy) (updatedTy := .ty rhsTy)
        (by
          change movedZ.slotAt "q" = some qSlot
          exact movedZ_slot_q)
        (by
          unfold qSlot
          exact UpdateAtPath.strong))
  have hupdate :
      UpdateAtPath movedZ (LVal.path (.deref p)) pSlot.ty rhsTy afterMovedQ
        pSlot.ty := by
    change UpdateAtPath movedZ [()] (.ty (.borrow true q)) rhsTy afterMovedQ
      (.ty (.borrow true q))
    exact UpdateAtPath.mutBorrow hinner
  simpa [resultMoved, afterMovedQ, p, pSlot, q, LVal.base, LVal.path] using
    (EnvWrite.intro
      (env₁ := movedZ) (env₂ := afterMovedQ) (lv := .deref p) (slot := pSlot)
      (ty := rhsTy) (updatedTy := pSlot.ty)
      (by
        change movedZ.slotAt "p" = some pSlot
        exact movedZ_slot_p)
      hupdate)

private theorem resultMoved_contains_borrow_base_ne_p
    {x : Name} {mutable : Bool} {target : LVal} :
    resultMoved ⊢ x ↝ (.borrow mutable target) →
    LVal.base target ≠ "p" := by
  intro hcontains hbase
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hxp : x = "p"
  · subst hxp
    have hslotEq : slot = pSlot := by
      exact Option.some.inj (hslot.symm.trans resultMoved_slot_p)
    subst hslotEq
    cases hcontainsTy with
    | here =>
        simp [q, LVal.base] at hbase
  · by_cases hxq : x = "q"
    · subst hxq
      have hslotEq : slot = { ty := .ty rhsTy, lifetime := l } := by
        exact Option.some.inj (hslot.symm.trans resultMoved_slot_q)
      subst hslotEq
      cases hcontainsTy with
      | here =>
          simp [q, LVal.base] at hbase
    · by_cases hxr : x = "r"
      · subst hxr
        have hslotEq : slot = rSlot := by
          exact Option.some.inj (hslot.symm.trans resultMoved_slot_r)
        subst hslotEq
        cases hcontainsTy
      · by_cases hxz : x = "z"
        · subst hxz
          have hslotEq : slot = { ty := .undef rhsTy, lifetime := l } := by
            exact Option.some.inj (hslot.symm.trans resultMoved_slot_z)
          subst hslotEq
          cases hcontainsTy
        · simp [resultMoved, afterMovedQ, movedZ, envWithZ, env, Env.empty,
            pSlot, qSlot, rSlot, zSlot, l, hxp, hxq, hxr, hxz] at hslot

private theorem resultMoved_not_writeProhibited :
    ¬ WriteProhibited resultMoved (.deref p) := by
  intro hwriteProhibited
  rcases hwriteProhibited with hread | himm
  · rcases hread with ⟨x, target, hcontains, hconflict⟩
    exact resultMoved_contains_borrow_base_ne_p hcontains
      (by simpa [PathConflicts, p, LVal.base] using hconflict)
  · rcases himm with ⟨x, target, hcontains, hconflict⟩
    exact resultMoved_contains_borrow_base_ne_p hcontains
      (by simpa [PathConflicts, p, LVal.base] using hconflict)

private theorem resultMoved_q_typing :
    LValTyping resultMoved q (.ty rhsTy) l := by
  exact LValTyping.var resultMoved_slot_q

private theorem no_resultMoved_deref_q_typing :
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping resultMoved lv pt lf →
      lv = .deref q →
      False := by
  intro lv pt lf htyping
  induction htyping with
  | var _hslot =>
      intro hlv
      cases hlv
  | box hsource _ih =>
      intro hlv
      cases hlv
      have hdet := LValTyping.deterministic hsource resultMoved_q_typing
      cases hdet.1
  | boxFull hsource _ih =>
      intro hlv
      cases hlv
      have hdet := LValTyping.deterministic hsource resultMoved_q_typing
      unfold rhsTy at hdet
      cases hdet.1
  | borrow hsource _htarget _ihSource ihTarget =>
      intro hlv
      cases hlv
      have hdet := LValTyping.deterministic hsource resultMoved_q_typing
      unfold rhsTy at hdet
      cases hdet.1
      exact ihTarget rfl

private theorem resultMoved_not_containedBorrowsWellFormed :
    ¬ ContainedBorrowsWellFormed resultMoved := by
  intro hcbwf
  have hslotQ :
      resultMoved.slotAt "q" = some { ty := .ty rhsTy, lifetime := l } := by
    exact resultMoved_slot_q
  have hcontainsQ : resultMoved ⊢ "q" ↝ (.borrow true (.deref q)) :=
    ⟨{ ty := .ty rhsTy, lifetime := l }, hslotQ, by
      unfold rhsTy
      exact PartialTyContains.here⟩
  rcases hcbwf "q" { ty := .ty rhsTy, lifetime := l } true (.deref q)
      hslotQ hcontainsQ with
    ⟨targetTy, targetLifetime, htyping, _hle, _hbase⟩
  exact no_resultMoved_deref_q_typing htyping rfl

private theorem source_assign_move_z :
    SourceTerm (.assign (.deref p) (.move z)) := by
  intro value hmem
  simp [termValues] at hmem

private theorem assign_move_z_typing :
    TermTyping envWithZ StoreTyping.empty l
      (.assign (.deref p) (.move z)) .unit resultMoved := by
  exact TermTyping.assign rhs_move_typing moved_lhs_typing moved_shape
    moved_rhs_wellFormed write_moved resultMoved_not_writeProhibited

/-- `WellFormedEnv` alone is too weak for strict assignment preservation.  The
formalized `T-Assign` rule admits this assignment from a strictly well-formed
but not borrow-safe environment: move `z : &mut *q` into `*p`, where
`p : &mut q` and `q : &mut r`.  The witness is therefore not a reachable
source-environment witness under the paper's borrow-safety discipline; it
isolates that the strict proof needs a borrow-safety/reachability premise, not
just Definition 4.8 well-formedness. -/
theorem strict_assign_rule_result_counterexample :
    ∃ env₁ env₃ typing lifetime lhs rhs,
      WellFormedEnv env₁ lifetime ∧
        SourceTerm (.assign lhs rhs) ∧
        TermTyping env₁ typing lifetime (.assign lhs rhs) .unit env₃ ∧
        ¬ ContainedBorrowsWellFormed env₃ := by
  exact ⟨envWithZ, resultMoved, StoreTyping.empty, l, .deref p, .move z,
    envWithZ_wellFormed, source_assign_move_z, assign_move_z_typing,
    resultMoved_not_containedBorrowsWellFormed⟩

end EnvWriteStrictCounterexample

/-- Strict forward lifetime-drop transport. -/
theorem LValTyping.dropLifetime_child_of_base_outlives {env : Env}
    {parent child : Lifetime} :
    LifetimeChild parent child →
    ContainedBorrowsWellFormed env →
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping env lv pt lf →
      LValBaseOutlives env lv parent →
      LValTyping (env.dropLifetime child) lv pt lf := by
  intro hchild hcbwf lv pt lf htyping
  induction htyping with
  | var hslot =>
      intro hbase
      rcases hbase with ⟨slot', hslot', hle⟩
      have hEq : _ = slot' := Option.some.inj (hslot.symm.trans hslot')
      refine .var (Env.dropLifetime_slotAt_eq_some.mpr ⟨hslot, ?_⟩)
      intro hlifetimeEq
      exact LifetimeChild.not_child_outlives_parent hchild
        (hlifetimeEq ▸ hEq ▸ hle)
  | box _ ih =>
      intro hbase
      exact .box (ih hbase)
  | boxFull _ ih =>
      intro hbase
      exact .boxFull (ih hbase)
  | borrow hw hu ihBorrow ihTarget =>
      intro hbase
      have hslotWF :=
        LValTyping.partialTyBorrowsWellFormedInSlot hcbwf hw
          PartialTyContains.here
      have hlfw :=
        LValTyping.lifetime_le_of_base_outlives hcbwf hw hbase
      rcases hslotWF with ⟨ty₀, lf₀, hty₀, _hle₀, hbase₀⟩
      have hbaseU : LValBaseOutlives env _ parent :=
        LValBaseOutlives.weaken hbase₀ hlfw
      exact .borrow (ihBorrow hbase) (ihTarget hbaseU)

theorem BorrowTargetsWellFormedInSlot.dropLifetime_child
    {env : Env} {parent child slotLifetime : Lifetime} {target : LVal} :
    LifetimeChild parent child →
    ContainedBorrowsWellFormed env →
    slotLifetime ≤ parent →
    BorrowTargetsWellFormedInSlot env slotLifetime target →
    BorrowTargetsWellFormedInSlot (env.dropLifetime child)
      slotLifetime target := by
  intro hchild hcbwf hslotLe htarget
  rcases htarget with ⟨ty₀, lf₀, hty₀, hle₀, hbase₀⟩
  exact ⟨ty₀, lf₀,
    LValTyping.dropLifetime_child_of_base_outlives hchild hcbwf hty₀
      (LValBaseOutlives.weaken hbase₀ hslotLe), hle₀,
    LValBaseOutlives.dropLifetime_child hchild hslotLe hbase₀⟩

theorem ContainedBorrowsWellFormed.dropLifetime_child
    {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    ContainedBorrowsWellFormed env →
    EnvSlotsOutlive env child →
    ContainedBorrowsWellFormed (env.dropLifetime child) := by
  intro hchild hcbwf hout x slot mutable target hslot hcontains
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨hold, hne⟩
  have hcontOld : env ⊢ x ↝ Ty.borrow mutable target :=
    EnvContains.dropLifetime_of_contains hcontains
  have hslotParent : slot.lifetime ≤ parent :=
    LifetimeChild.parent_of_outlives_child_ne hchild (hout x slot hold) hne
  exact BorrowTargetsWellFormedInSlot.dropLifetime_child
    hchild hcbwf hslotParent (hcbwf x slot mutable target hold hcontOld)

theorem WellFormedTy.dropLifetime_child {env : Env}
    {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    ContainedBorrowsWellFormed env →
    WellFormedTy env ty parent →
    WellFormedTy (env.dropLifetime child) ty parent := by
  intro hchild hcbwf hwellTy
  induction hwellTy with
  | unit => exact .unit
  | int => exact .int
  | borrow htargets =>
      rcases htargets with ⟨ty₀, lf₀, hty₀, hle₀, hbase₀⟩
      exact .borrow ⟨ty₀, lf₀,
        LValTyping.dropLifetime_child_of_base_outlives hchild hcbwf hty₀
          hbase₀, hle₀,
        LValBaseOutlives.dropLifetime_child hchild
          (LifetimeOutlives.refl _) hbase₀⟩
  | box _ ih => exact .box (ih hchild)

theorem block_preserves_wellFormed {env₂ env₃ : Env}
    {lifetime blockLifetime : Lifetime} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₂ blockLifetime →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnv env₃ lifetime ∧ WellFormedTy env₃ ty lifetime := by
  intro hchild hwellBody hwellTy hdrop
  subst hdrop
  refine ⟨⟨ContainedBorrowsWellFormed.dropLifetime_child hchild
      hwellBody.1 hwellBody.2, ?_⟩,
    WellFormedTy.dropLifetime_child hchild hwellBody.1 hwellTy⟩
  intro x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨hold, hne⟩
  exact LifetimeChild.parent_of_outlives_child_ne hchild
    (hwellBody.2 x slot hold) hne

/-- Strict forward move transport: a typing whose route cannot conflict with
the moved place survives the strike. -/
theorem LValTyping.move_of_no_conflicts {env moved : Env} {movedLv : LVal} :
    ContainedBorrowsWellFormed env →
    EnvMove env movedLv moved →
    ¬ WriteProhibited env movedLv →
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime},
      ¬ lv ⋈ movedLv →
      LValTyping env lv pt lf →
      LValTyping moved lv pt lf := by
  intro hcbwf hmove hnotWrite lv pt lf hnoConflict htyping
  induction htyping with
  | var hslot =>
      rename_i y s
      have hne : y ≠ LVal.base movedLv := hnoConflict
      rcases hmove with ⟨movedSlot, struck, hmovedSlot, _hstrike, hmoved⟩
      subst hmoved
      exact .var (by simpa [Env.update, hne] using hslot)
  | box _ ih =>
      exact .box (ih hnoConflict)
  | boxFull _ ih =>
      exact .boxFull (ih hnoConflict)
  | borrow hw hu ihBorrow ihTarget =>
      rename_i w u m blf tlf tty
      have hcontains :=
        LValTyping.contains_borrow hw PartialTyContains.here
      rcases hcontains with ⟨z, hcont⟩
      have hnoConflictU : ¬ u ⋈ movedLv := by
        intro hconflict
        exact hnotWrite
          (WriteProhibited.of_contains_conflict hcont hconflict)
      exact .borrow (ihBorrow hnoConflict) (ihTarget hnoConflictU)

theorem ContainedBorrowsWellFormed.move {env moved : Env} {lv : LVal} :
    ContainedBorrowsWellFormed env →
    EnvMove env lv moved →
    ¬ WriteProhibited env lv →
    ContainedBorrowsWellFormed moved := by
  intro hcbwf hmove hnotWrite x slot mutable target hslot hcontainsMoved
  have hcontainsSource : env ⊢ x ↝ (.borrow mutable target) :=
    EnvMove.contains_borrow_source hmove hslot hcontainsMoved
  rcases hcontainsSource with ⟨sourceSlot, hsourceSlot, hsourceContainsTy⟩
  have htargetOld :=
    hcbwf x sourceSlot mutable target hsourceSlot
      ⟨sourceSlot, hsourceSlot, hsourceContainsTy⟩
  have hlife : sourceSlot.lifetime = slot.lifetime := by
    rcases hmove with ⟨movedSlot, struck, hmovedSlot, _hstrike, hmoved⟩
    subst hmoved
    by_cases hx : x = LVal.base lv
    · subst hx
      have h₁ : sourceSlot = movedSlot :=
        Option.some.inj (hsourceSlot.symm.trans hmovedSlot)
      have h₂ : slot = { movedSlot with ty := struck } :=
        (Option.some.inj (by simpa [Env.update] using hslot)).symm
      rw [h₁, h₂]
    · have h : env.slotAt x = some slot := by
        simpa [Env.update, hx] using hslot
      rw [Option.some.inj (hsourceSlot.symm.trans h)]
  rcases htargetOld with ⟨ty₀, lf₀, hty₀, hle₀, hbase₀⟩
  have hnoConflictTarget : ¬ target ⋈ lv := by
    intro hconflict
    exact hnotWrite
      (WriteProhibited.of_contains_conflict
        ⟨sourceSlot, hsourceSlot, hsourceContainsTy⟩ hconflict)
  exact ⟨ty₀, lf₀,
    LValTyping.move_of_no_conflicts hcbwf hmove hnotWrite
      hnoConflictTarget hty₀, hlife ▸ hle₀,
    LValBaseOutlives.move hmove (hlife ▸ hbase₀)⟩

theorem WellFormedEnv.move {env moved : Env} {lv : LVal}
    {current : Lifetime} :
    WellFormedEnv env current →
    EnvMove env lv moved →
    ¬ WriteProhibited env lv →
    WellFormedEnv moved current := by
  intro hwell hmove hnotWrite
  refine ⟨ContainedBorrowsWellFormed.move hwell.1 hmove hnotWrite, ?_⟩
  intro x slot hslot
  rcases hmove with ⟨movedSlot, struck, hmovedSlot, _hstrike, hmoved⟩
  subst hmoved
  by_cases hx : x = LVal.base lv
  · subst hx
    have h : slot = { movedSlot with ty := struck } :=
      (Option.some.inj (by simpa [Env.update] using hslot)).symm
    subst h
    exact hwell.2 _ movedSlot hmovedSlot
  · exact hwell.2 x slot (by simpa [Env.update, hx] using hslot)

/-- The moved-out type stays strictly well formed after the move. -/
theorem WellFormedTy.move {env moved : Env} {lv : LVal}
    {ty : Ty} {lifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    EnvMove env lv moved →
    ¬ WriteProhibited env lv →
    (∀ {mutable : Bool} {target : LVal},
      PartialTyContains (.ty ty) (.borrow mutable target) →
      ∃ x, env ⊢ x ↝ (.borrow mutable target)) →
    WellFormedTy env ty lifetime →
    WellFormedTy moved ty lifetime := by
  intro hcbwf hmove hnotWrite hcontained hwellTy
  induction hwellTy with
  | unit => exact .unit
  | int => exact .int
  | borrow htargets =>
      rename_i mutable' target' lifetime'
      rcases htargets with ⟨ty₀, lf₀, hty₀, hle₀, hbase₀⟩
      rcases hcontained PartialTyContains.here with ⟨x, hcont⟩
      have hnoConflictTarget : ¬ target' ⋈ lv := by
        intro hconflict
        exact hnotWrite
          (WriteProhibited.of_contains_conflict hcont hconflict)
      exact .borrow ⟨ty₀, lf₀,
        LValTyping.move_of_no_conflicts hcbwf hmove hnotWrite
          hnoConflictTarget hty₀, hle₀,
        LValBaseOutlives.move hmove hbase₀⟩
  | box _ ih =>
      refine .box (ih ?_)
      intro mutable target hcontains
      exact hcontained (PartialTyContains.tyBox hcontains)

/-! ### The write-chain guard kernel

Partial types are unary spines, so a slot type contains at most one borrow
annotation (`PartialTyContains.borrow_unique`).  `ChainGuard` captures the
slots reachable from the written base through environment-contained mutable
annotations — exactly the write chain plus the grafted slot.  In a borrow-safe
environment, an annotation held OUTSIDE the chain can never target INTO it:
at the chain root that would write-prohibit the assigned lval in the result,
and at deeper links borrow safety forces the holder onto the chain.  This is
what lets strict typings transport across the write without any existence
recursion.
-/

theorem PartialTyContains.borrow_unique {pt : PartialTy} {mutable mutable' : Bool}
    {target target' : LVal} :
    PartialTyContains pt (.borrow mutable target) →
    PartialTyContains pt (.borrow mutable' target') →
    mutable = mutable' ∧ target = target' := by
  intro hleft
  generalize hβ : Ty.borrow mutable target = β at hleft
  induction hleft with
  | here =>
      intro hright
      cases hβ
      cases hright with
      | here => exact ⟨rfl, rfl⟩
  | tyBox _ ih =>
      intro hright
      cases hright with
      | tyBox hinner => exact ih hβ hinner
  | box _ ih =>
      intro hright
      cases hright with
      | box hinner => exact ih hβ hinner

/-- Slots reachable from `root` through environment-contained mutable borrow
annotations. -/
inductive ChainGuard (env : Env) (root : Name) : Name → Prop where
  | base : ChainGuard env root root
  | step {z y : Name} {g : LVal} :
      ChainGuard env root z →
      env ⊢ z ↝ (.borrow true g) →
      LVal.base g = y →
      ChainGuard env root y

/-- No annotation held outside the chain targets into the chain. -/
theorem chainGuard_contains_exclusion {env env₃ : Env} {lhs : LVal}
    (hsafe : BorrowSafeEnv env)
    (hunchanged : ∀ x, ¬ ChainGuard env (LVal.base lhs) x →
      env₃.slotAt x = env.slotAt x)
    (hnotWrite : ¬ WriteProhibited env₃ lhs) :
    ∀ {y : Name}, ChainGuard env (LVal.base lhs) y →
      ∀ {x : Name} {mutable : Bool} {u : LVal},
        ¬ ChainGuard env (LVal.base lhs) x →
        env ⊢ x ↝ (.borrow mutable u) →
        LVal.base u = y →
        False := by
  intro y hguard
  induction hguard with
  | base =>
      intro x mutable u hxOutside hcont hbase
      apply hnotWrite
      have hcont₃ : env₃ ⊢ x ↝ (.borrow mutable u) := by
        rcases hcont with ⟨slot, hslot, hcontainsTy⟩
        exact ⟨slot, (hunchanged x hxOutside) ▸ hslot, hcontainsTy⟩
      exact WriteProhibited.of_contains_conflict hcont₃ hbase
  | step hz hcontZ hbaseG ih =>
      intro x mutable u hxOutside hcont hbase
      rename_i z y' g
      have hconflict : g ⋈ u := by
        show LVal.base g = LVal.base u
        rw [hbaseG, hbase]
      have hxz : z = x := hsafe z x mutable g u hcontZ hcont hconflict
      exact hxOutside (hxz ▸ hz)

/-- A typing derivation rooted outside the chain stays outside the chain, so
it transports unchanged across the write.  The induction also threads that
every borrow annotation in the resulting type has an outside holder, which is
what keeps hop targets outside. -/
theorem LValTyping.transport_of_outside_chain {env env₃ : Env} {lhs : LVal}
    (hsafe : BorrowSafeEnv env)
    (hunchanged : ∀ x, ¬ ChainGuard env (LVal.base lhs) x →
      env₃.slotAt x = env.slotAt x)
    (hnotWrite : ¬ WriteProhibited env₃ lhs) :
    ∀ {t : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping env t pt lf →
      ¬ ChainGuard env (LVal.base lhs) (LVal.base t) →
      LValTyping env₃ t pt lf ∧
        (∀ {mutable : Bool} {u : LVal},
          PartialTyContains pt (.borrow mutable u) →
          ∃ z, ¬ ChainGuard env (LVal.base lhs) z ∧
            env ⊢ z ↝ (.borrow mutable u)) := by
  intro t pt lf htyping
  induction htyping with
  | var hslot =>
      rename_i y s
      intro houtside
      refine ⟨.var ((hunchanged _ houtside) ▸ hslot), ?_⟩
      intro mutable u hcontains
      exact ⟨y, houtside, ⟨s, hslot, hcontains⟩⟩
  | box _ ih =>
      intro houtside
      refine ⟨.box (ih houtside).1, ?_⟩
      intro mutable u hcontains
      exact (ih houtside).2 (PartialTyContains.box hcontains)
  | boxFull _ ih =>
      intro houtside
      refine ⟨.boxFull (ih houtside).1, ?_⟩
      intro mutable u hcontains
      exact (ih houtside).2 (PartialTyContains.tyBox hcontains)
  | borrow hw hu ihBorrow ihTarget =>
      intro houtside
      rename_i w u m blf tlf tty
      rcases (ihBorrow houtside).2 PartialTyContains.here with
        ⟨z, hzOutside, hcont⟩
      have hguardU : ¬ ChainGuard env (LVal.base lhs) (LVal.base u) := by
        intro hguard
        exact chainGuard_contains_exclusion hsafe hunchanged hnotWrite
          hguard hzOutside hcont rfl
      exact ⟨.borrow (ihBorrow houtside).1 (ihTarget hguardU).1,
        (ihTarget hguardU).2⟩

/-- Characterization of the strong-update write: either nothing changed
(cyclic chains clobber their own graft), or exactly one slot `b` changed, its
new type's borrows all come from the written type, the written lval's typing
lifetime bounds `b`'s slot lifetime, and `b` is chain-guarded from the
written base. -/
theorem EnvWrite.chain_guarded {env : Env}
    (hcbwf : ContainedBorrowsWellFormed env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime} :
    EnvWrite env lhs rhsTy env₃ →
    LValTyping env lhs oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    (∀ y, env₃.slotAt y = env.slotAt y) ∨
      ∃ b bslot graftTy,
        env.slotAt b = some bslot ∧
        (∀ y, y ≠ b → env₃.slotAt y = env.slotAt y) ∧
        env₃.slotAt b = some { bslot with ty := graftTy } ∧
        targetLifetime ≤ bslot.lifetime ∧
        (∀ {mutable : Bool} {u : LVal},
          PartialTyContains graftTy (.borrow mutable u) →
          PartialTyContains (.ty rhsTy) (.borrow mutable u)) ∧
        ShapeCompatible env bslot.ty graftTy ∧
        ChainGuard env (LVal.base lhs) b := by
  intro hwrite hlv hshape
  exact EnvWrite.rec
    (motive_1 := fun path old ty result updated _ =>
      ∀ {wcur : LVal} {pt : PartialTy} {lf lfc : Lifetime},
        LValTyping env wcur old lfc →
        LValTyping env (prependPath path wcur) pt lf →
        (∀ {mutable : Bool} {u : LVal},
          PartialTyContains old (.borrow mutable u) →
          env ⊢ (LVal.base wcur) ↝ (.borrow mutable u)) →
        ChainGuard env (LVal.base lhs) (LVal.base wcur) →
        ShapeCompatible env pt (.ty ty) →
        (updated = old ∧
          ((∀ y, result.slotAt y = env.slotAt y) ∨
            ∃ b bslot graftTy,
              env.slotAt b = some bslot ∧
              (∀ y, y ≠ b → result.slotAt y = env.slotAt y) ∧
              result.slotAt b = some { bslot with ty := graftTy } ∧
              lf ≤ bslot.lifetime ∧
              (∀ {mutable : Bool} {u : LVal},
                PartialTyContains graftTy (.borrow mutable u) →
                PartialTyContains (.ty ty) (.borrow mutable u)) ∧
              ShapeCompatible env bslot.ty graftTy ∧
              ChainGuard env (LVal.base lhs) b)) ∨
        (result = env ∧
          (∀ {mutable : Bool} {u : LVal},
            PartialTyContains updated (.borrow mutable u) →
            PartialTyContains (.ty ty) (.borrow mutable u)) ∧
          ShapeCompatible env old updated ∧
          (∀ T₀, old = .ty T₀ → ∃ T₁, updated = .ty T₁)))
    (motive_2 := fun lv ty result _ =>
      ∀ {pt : PartialTy} {lf : Lifetime},
        LValTyping env lv pt lf →
        ChainGuard env (LVal.base lhs) (LVal.base lv) →
        ShapeCompatible env pt (.ty ty) →
        (∀ y, result.slotAt y = env.slotAt y) ∨
          ∃ b bslot graftTy,
            env.slotAt b = some bslot ∧
            (∀ y, y ≠ b → result.slotAt y = env.slotAt y) ∧
            result.slotAt b = some { bslot with ty := graftTy } ∧
            lf ≤ bslot.lifetime ∧
            (∀ {mutable : Bool} {u : LVal},
              PartialTyContains graftTy (.borrow mutable u) →
              PartialTyContains (.ty ty) (.borrow mutable u)) ∧
            ShapeCompatible env bslot.ty graftTy ∧
            ChainGuard env (LVal.base lhs) b)
    (by
      -- strong: the graft happens here; the environment part is untouched.
      intro _old _ty wcur pt lf lfc hwcur hlhs _hcontainsW _hguard hshapePt
      have hdet := LValTyping.deterministic hwcur
        (by simpa [prependPath] using hlhs)
      refine Or.inr ⟨rfl, fun hcontains => hcontains, ?_, ?_⟩
      · exact hdet.1 ▸ hshapePt
      · intro T₀ _hold
        exact ⟨_ty, rfl⟩)
    (by
      -- box: the update stays inside the partial box.
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
        wcur pt lf lfc hwcur hlhs hcontainsW hguard hshapePt
      rcases ih (LValTyping.box hwcur)
          (by rw [prependPath_deref_comm]; exact hlhs)
          (by
            intro mutable u hcontains
            exact hcontainsW (PartialTyContains.box hcontains))
          hguard hshapePt with
        ⟨hupdEq, hprops⟩ | ⟨henvEq, hgraft, hshapeInner, _htyRoot⟩
      · exact Or.inl ⟨by rw [hupdEq], hprops⟩
      · refine Or.inr ⟨henvEq, ?_, ShapeCompatible.box hshapeInner, ?_⟩
        · intro mutable u hcontains
          cases hcontains with
          | box hinner' => exact hgraft hinner'
        · intro T₀ hold
          cases hold
    )
    (by
      -- boxFull: as box, through the rebox wrapper.
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
        wcur pt lf lfc hwcur hlhs hcontainsW hguard hshapePt
      rcases ih (LValTyping.boxFull hwcur)
          (by rw [prependPath_deref_comm]; exact hlhs)
          (by
            intro mutable u hcontains
            exact hcontainsW (PartialTyContains.tyBox hcontains))
          hguard hshapePt with
        ⟨hupdEq, hprops⟩ | ⟨henvEq, hgraft, hshapeInner, htyRoot⟩
      · exact Or.inl ⟨by rw [hupdEq, partialTyRebox], hprops⟩
      · rcases htyRoot _ rfl with ⟨T₁, hT₁⟩
        subst hT₁
        exact Or.inr ⟨henvEq,
          fun hcontains =>
            hgraft (PartialTyContains.partialTyRebox_borrow_inv hcontains),
          by
            rw [partialTyRebox]
            exact ShapeCompatible.tyBox hshapeInner,
          fun T₀ _hold => ⟨.box T₁, by rw [partialTyRebox]⟩⟩)
    (by
      -- mutBorrow: the local type is unchanged; the nested write carries the
      -- change, one guard step deeper.
      intro _env₂ path target _ty _hwrite ih
        wcur pt lf lfc hwcur hlhs hcontainsW hguard hshapePt
      refine Or.inl ⟨rfl, ?_⟩
      have hguardTarget : ChainGuard env (LVal.base lhs) (LVal.base target) :=
        ChainGuard.step hguard (hcontainsW PartialTyContains.here) rfl
      have hlhsRebased :
          LValTyping env (prependPath path target) pt lf :=
        LValTyping.rebase_hop hwcur path
          (by rw [prependPath_deref_comm]; exact hlhs)
      exact ih hlhsRebased (by simpa using hguardTarget) hshapePt)
    (by
      -- intro: assemble the per-slot characterization.
      intro _env₂ lv slot _ty updatedTy hslot hupdate ih pt lf hlv hguard
        hshapePt
      have hcontainsW :
          ∀ {mutable : Bool} {u : LVal},
            PartialTyContains slot.ty (.borrow mutable u) →
            env ⊢ (LVal.base lv) ↝ (.borrow mutable u) := by
        intro mutable u hcontains
        exact ⟨slot, hslot, hcontains⟩
      rcases ih (wcur := .var (LVal.base lv)) (LValTyping.var hslot)
          (by rw [prependPath_path_base]; exact hlv) hcontainsW hguard
          hshapePt with
        ⟨hupdEq, hprops⟩ | ⟨henvEq, hgraft, hshapeGraft, _htyRoot⟩
      · -- Chain slot: the update rewrites the slot to its own value.
        have hslotEta : { slot with ty := updatedTy } = slot := by
          rw [hupdEq]
        rcases hprops with hpointwise | ⟨b, bslot, graftTy, hb, hne, hbLook,
            hbound, hgraftContains, hshapeB, hguardB⟩
        · refine Or.inl ?_
          intro y
          by_cases hy : y = LVal.base lv
          · subst hy
            rw [hslotEta]
            simpa [Env.update] using hslot.symm
          · simpa [Env.update, hy] using hpointwise y
        · by_cases hbEq : b = LVal.base lv
          · -- The chain clobbers its own graft: nothing changes.
            refine Or.inl ?_
            intro y
            by_cases hy : y = LVal.base lv
            · subst hy
              rw [hslotEta]
              simpa [Env.update] using hslot.symm
            · have hyB : y ≠ b := fun h => hy (h.trans hbEq)
              simpa [Env.update, hy] using hne y hyB
          · refine Or.inr ⟨b, bslot, graftTy, hb, ?_, ?_, hbound,
              hgraftContains, hshapeB, hguardB⟩
            · intro y hy
              by_cases hyLv : y = LVal.base lv
              · subst hyLv
                rw [hslotEta]
                simpa [Env.update] using hslot.symm
              · simpa [Env.update, hyLv] using hne y hy
            · simpa [Env.update, hbEq] using hbLook
      · -- Graft slot: the written base receives the grafted type.
        refine Or.inr ⟨LVal.base lv, slot, updatedTy, hslot, ?_, ?_, ?_,
          hgraft, hshapeGraft, hguard⟩
        · intro y hy
          rw [show (_env₂.update (LVal.base lv)
              { slot with ty := updatedTy }).slotAt y = _env₂.slotAt y by
            simp [Env.update, hy]]
          rw [henvEq]
        · simp [Env.update]
        · exact LValTyping.lifetime_le_of_base_outlives hcbwf hlv
            ⟨slot, hslot, LifetimeOutlives.refl _⟩)
    hwrite hlv ChainGuard.base hshape

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

end LwRust.Paper.Soundness
