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

/-- Compatibility predicate kept for consumers from the stale-aware development.

Single-target borrow validity already records the selected target in the type,
so the old global coherence side-condition carries no additional data. -/
def CoherentWhenInitialized (_env : Env) : Prop := True

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

/-- Compatibility wrapper: the old coherence invariant is trivial in the
single-target system. -/
theorem typingPreservesCoherentWhenInitialized_of_sourceTerm
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    SourceTerm term →
    WellFormedEnvWhenInitialized env₁ lifetime →
    CoherentWhenInitialized env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    CoherentWhenInitialized env₂ := by
  intro _ _ _ _
  trivial

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

theorem EnvMove.preserves_linearizable {env moved : Env} {lv : LVal} :
    Linearizable env →
    EnvMove env lv moved →
    Linearizable moved := by
  rintro ⟨φ, hlinear⟩ hmove
  refine ⟨φ, ?_⟩
  intro x slot hslot v hv
  rcases hmove with ⟨sourceSlot, struck, hsourceSlot, hstrike, hmoved⟩
  subst hmoved
  by_cases hx : x = LVal.base lv
  · subst hx
    have hslotEq : slot = { sourceSlot with ty := struck } := by
      exact (Option.some.inj (by simpa [Env.update] using hslot)).symm
    subst hslotEq
    exact hlinear (LVal.base lv) sourceSlot hsourceSlot v
      (Strike.vars_subset hstrike v hv)
  · have hslotOld : env.slotAt x = some slot := by
      simpa [Env.update, hx] using hslot
    exact hlinear x slot hslotOld v hv

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

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

end LwRust.Paper.Soundness
