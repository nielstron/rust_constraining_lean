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

/-- One plus the maximum rank of a finite variable list. -/
def rankBound (φ : Name → Nat) : List Name → Nat
  | [] => 0
  | v :: vars => max (φ v + 1) (rankBound φ vars)

theorem rank_lt_rankBound_of_mem {φ : Name → Nat} :
    ∀ {vars : List Name} {v : Name},
      v ∈ vars → φ v < rankBound φ vars := by
  intro vars
  induction vars with
  | nil =>
      intro v hmem
      cases hmem
  | cons head tail ih =>
      intro v hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst hhead
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
          (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih htail) (Nat.le_max_right _ _)

/-- One plus the maximum rank of variables mentioned by slots in a support list. -/
def slotsRankBound (φ : Name → Nat) (env : Env) : List Name → Nat
  | [] => 0
  | x :: support =>
      max
        (match env.slotAt x with
        | none => 0
        | some slot => rankBound φ (PartialTy.vars slot.ty))
        (slotsRankBound φ env support)

theorem rank_lt_slotsRankBound_of_mem {φ : Name → Nat} {env : Env} :
    ∀ {support : List Name} {x : Name} {slot : EnvSlot} {v : Name},
      x ∈ support →
      env.slotAt x = some slot →
      v ∈ PartialTy.vars slot.ty →
      φ v < slotsRankBound φ env support := by
  intro support
  induction support with
  | nil =>
      intro x slot v hmem _hslot _hv
      cases hmem
  | cons head tail ih =>
      intro x slot v hmem hslot hv
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst hhead
        unfold slotsRankBound
        rw [hslot]
        exact Nat.lt_of_lt_of_le (rank_lt_rankBound_of_mem (φ := φ) hv)
          (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih htail hslot hv)
          (Nat.le_max_right _ _)

def writeRankBound (φ : Name → Nat) (env : Env) (rhsTy : Ty)
    (support : List Name) : Nat :=
  max (rankBound φ (Ty.vars rhsTy)) (slotsRankBound φ env support)

theorem rank_lt_writeRankBound_of_rhs {φ : Name → Nat} {env : Env}
    {rhsTy : Ty} {support : List Name} {v : Name} :
    v ∈ Ty.vars rhsTy →
    φ v < writeRankBound φ env rhsTy support := by
  intro hv
  exact Nat.lt_of_lt_of_le (rank_lt_rankBound_of_mem (φ := φ) hv)
    (Nat.le_max_left _ _)

theorem rank_lt_writeRankBound_of_slot {φ : Name → Nat} {env : Env}
    {rhsTy : Ty} {support : List Name} {x : Name} {slot : EnvSlot}
    {v : Name} :
    x ∈ support →
    env.slotAt x = some slot →
    v ∈ PartialTy.vars slot.ty →
    φ v < writeRankBound φ env rhsTy support := by
  intro hx hslot hv
  exact Nat.lt_of_lt_of_le
    (rank_lt_slotsRankBound_of_mem (φ := φ) hx hslot hv)
    (Nat.le_max_right _ _)

theorem LinearizedBy.empty (φ : Name → Nat) :
    LinearizedBy φ Env.empty := by
  intro x slot v hslot _hv
  simp [Env.empty] at hslot

theorem Linearizable.empty : Linearizable Env.empty :=
  ⟨fun _ => 0, LinearizedBy.empty _⟩

theorem LinearizedBy.update_same_rank {φ : Name → Nat} {env : Env}
    {x : Name} {slot : EnvSlot} :
    LinearizedBy φ env →
    (∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x) →
    LinearizedBy φ (env.update x slot) := by
  intro hφ hslotBelow y resultSlot v hresult hv
  by_cases hy : y = x
  · subst hy
    have hslotEq : resultSlot = slot := by
      simpa [Env.update] using hresult.symm
    subst hslotEq
    exact hslotBelow v hv
  · have hsource : env.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresult
    exact hφ y resultSlot v hsource hv

theorem LinearizedBy.update_fresh_above {φ : Name → Nat} {env : Env}
    {x : Name} {slot : EnvSlot} :
    LinearizedBy φ env →
    env.fresh x →
    (∀ y sourceSlot,
      env.slotAt y = some sourceSlot →
      x ∉ PartialTy.vars sourceSlot.ty) →
    x ∉ PartialTy.vars slot.ty →
    LinearizedBy
      (fun y => if y = x then rankBound φ (PartialTy.vars slot.ty) else φ y)
      (env.update x slot) := by
  intro hφ _hfresh hnotInSource hnotInSlot y resultSlot v hresult hv
  by_cases hy : y = x
  · have hslotEq : resultSlot = slot := by
      simpa [Env.update, hy] using hresult.symm
    subst hslotEq
    have hvx : v ≠ x := by
      intro hvx
      exact hnotInSlot (by simpa [hvx] using hv)
    simpa [hy, hvx] using rank_lt_rankBound_of_mem (φ := φ) hv
  · have hsource : env.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresult
    have hvx : v ≠ x := by
      intro hvx
      exact hnotInSource y resultSlot hsource (by simpa [hvx] using hv)
    simpa [hy, hvx] using hφ y resultSlot v hsource hv

theorem LinearizedBy.dropLifetime {φ : Name → Nat} {env : Env}
    {lifetime : Lifetime} :
    LinearizedBy φ env →
    LinearizedBy φ (env.dropLifetime lifetime) := by
  intro hφ x slot v hslot hv
  unfold Env.dropLifetime at hslot
  cases henv : env.slotAt x with
  | none =>
      simp [henv] at hslot
  | some sourceSlot =>
      by_cases hlife : sourceSlot.lifetime = lifetime
      · simp [henv, hlife] at hslot
      · have hslotEq : sourceSlot = slot := by
          simpa [henv, hlife] using hslot
        have hvSource : v ∈ PartialTy.vars sourceSlot.ty := by
          simpa [hslotEq] using hv
        exact hφ x sourceSlot v henv hvSource

theorem LinearizedBy.move {φ : Name → Nat} {env moved : Env} {lv : LVal} :
    LinearizedBy φ env →
    EnvMove env lv moved →
    LinearizedBy φ moved := by
  intro hφ hmove
  rcases hmove with ⟨slot, struck, hslot, hstrike, hmoved⟩
  rw [hmoved]
  exact LinearizedBy.update_same_rank hφ (fun v hv =>
    hφ (LVal.base lv) slot v hslot (Strike.vars_subset hstrike v hv))

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

theorem LValTyping.contained_of_partialTyContains {env : Env} :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {mutable : Bool} {target : LVal},
      LValTyping env lv partialTy lifetime →
      PartialTyContains partialTy (.borrow mutable target) →
      ∃ holder, env ⊢ holder ↝ (.borrow mutable target) := by
  exact LValTyping.contains_borrow

theorem LValTyping.ty_borrow_contained {env : Env} :
    ∀ {lv : LVal} {mutable : Bool} {target : LVal} {lifetime : Lifetime},
      LValTyping env lv (.ty (.borrow mutable target)) lifetime →
      ∃ holder, env ⊢ holder ↝ (.borrow mutable target) := by
  intro lv mutable target lifetime htyping
  exact LValTyping.contained_of_partialTyContains htyping PartialTyContains.here

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

/-- Partial types that still describe initialized storage, i.e. contain no
`undef` leaf.  Moving strikes exactly one leaf to `undef`, so an initialized
lvalue typing in the moved environment was already initialized in the source
environment. -/
def PartialTyDefined : PartialTy → Prop
  | .ty _ => True
  | .box inner => PartialTyDefined inner
  | .undef _ => False

theorem Strike.not_defined {path : Path} {source struck : PartialTy} :
    Strike path source struck →
    PartialTyDefined struck →
    False := by
  intro hstrike hdefined
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;>
        simp [Strike, PartialTyDefined] at hstrike hdefined
  | cons _ tail ih =>
      cases source with
      | ty sourceTy =>
          cases sourceTy <;> cases struck <;>
            simp [Strike, PartialTyDefined] at hstrike hdefined
          exact ih hstrike hdefined
      | box inner =>
          cases struck <;> simp [Strike, PartialTyDefined] at hstrike hdefined
          exact ih hstrike hdefined
      | undef shape =>
          cases struck <;> simp [Strike] at hstrike

theorem LValTyping.defined_of_envMove {env moved : Env} {movedLv : LVal} :
    EnvMove env movedLv moved →
    ∀ {target : LVal} {pt : PartialTy} {lf : Lifetime},
      PartialTyDefined pt →
      LValTyping moved target pt lf →
      LValTyping env target pt lf := by
  intro hmove target pt lf hdefined htyping
  induction htyping with
  | var hslot =>
      rename_i x slot
      rcases hmove with ⟨sourceSlot, struck, hsourceSlot, hstrike, hmoved⟩
      by_cases hx : x = LVal.base movedLv
      · subst hx
        have hslotEq : { sourceSlot with ty := struck } = slot :=
          Option.some.inj (by simpa [hmoved, Env.update] using hslot)
        have htyEq : struck = slot.ty := congrArg EnvSlot.ty hslotEq
        exact False.elim
          (Strike.not_defined hstrike (by simpa [← htyEq] using hdefined))
      · exact .var (by simpa [hmoved, Env.update, hx] using hslot)
  | box _ ih =>
      exact .box (ih (by simpa [PartialTyDefined] using hdefined))
  | boxFull _ ih =>
      exact .boxFull (ih (by simp [PartialTyDefined]))
  | borrow _ _ ihBorrow ihTarget =>
      exact .borrow (ihBorrow (by simp [PartialTyDefined]))
        (ihTarget (by simp [PartialTyDefined]))

theorem TargetInitialized.of_envMove {env moved : Env} {movedLv target : LVal} :
    EnvMove env movedLv moved →
    TargetInitialized moved target →
    TargetInitialized env target := by
  intro hmove htarget
  rcases htarget with ⟨targetTy, targetLifetime, htyping⟩
  exact ⟨targetTy, targetLifetime,
    LValTyping.defined_of_envMove hmove (by simp [PartialTyDefined]) htyping⟩

theorem ValidPartialValueWhenInitialized.move_env {env moved : Env}
    {store : ProgramStore} {movedLv : LVal} {value : PartialValue}
    {ty : PartialTy} :
    EnvMove env movedLv moved →
    ValidPartialValueWhenInitialized env store value ty →
    ValidPartialValueWhenInitialized moved store value ty := by
  intro hmove hvalid
  exact validPartialValueWhenInitialized_transport_env
    (fun htarget => TargetInitialized.of_envMove hmove htarget) hvalid

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

theorem validPartialValueWhenInitialized_update_of_not_live_reaches {env : Env}
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot} :
    ∀ {v : PartialValue} {ty : PartialTy},
      ValidPartialValueWhenInitialized env store v ty →
      (∀ location, ReachesWhenInitialized env store v ty location →
        location ≠ updated) →
      ValidPartialValueWhenInitialized env (store.update updated newSlot) v ty := by
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
        (RuntimeFrame.validPartialValueSkeleton_update_of_not_owner_reaches hinner
          (fun location howner =>
            hreach location
              (ReachesWhenInitialized.undefOf hinner hstrength howner)))
        hstrength
  | borrowLive hinitialized hloc =>
      intro hreach
      refine ValidPartialValueWhenInitialized.borrowLive hinitialized ?_
      refine RuntimeFrame.loc_update_of_not_locReads hloc ?_
      intro mid hmidReads
      exact hreach mid
        (ReachesWhenInitialized.borrow hinitialized hloc hmidReads)
  | borrowStale hstale =>
      intro _hreach
      exact ValidPartialValueWhenInitialized.borrowStale hstale
  | box hslot _hinner ih =>
      intro hreach
      rename_i location slot inner
      have hlocNe : location ≠ updated :=
        hreach location (ReachesWhenInitialized.boxHere hslot)
      refine ValidPartialValueWhenInitialized.box (location := location)
        (slot := slot) ?_ ?_
      · rw [RuntimeFrame.ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun reached hreached =>
          hreach reached (ReachesWhenInitialized.boxInner hslot hreached))
  | boxFull hslot _hinner ih =>
      intro hreach
      rename_i location slot ty
      have hlocNe : location ≠ updated :=
        hreach location (ReachesWhenInitialized.boxFullHere hslot)
      refine ValidPartialValueWhenInitialized.boxFull (location := location)
        (slot := slot) ?_ ?_
      · rw [RuntimeFrame.ProgramStore.slotAt_update_ne hlocNe]
        exact hslot
      · exact ih (fun reached hreached =>
          hreach reached (ReachesWhenInitialized.boxFullInner hslot hreached))

theorem lval_loc_var_conflict_or_writeProhibited_whenInitialized
    {store : ProgramStore} {env : Env} {x : Name} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
      store.loc lv = some (VariableProjection x) →
      lv ⋈ (.var x) ∨ WriteProhibited env (.var x) := by
  intro hsafe hheap lv partialTy lifetime htyping
  induction htyping generalizing x with
  | var hslot =>
      rename_i y slot
      intro hloc
      left
      change y = x
      simpa [ProgramStore.loc, VariableProjection] using hloc
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
          have hownedVar : ownedLocation = VariableProjection x := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc
          have howns : ProgramStore.Owns store ownedLocation :=
            ⟨sourceLocation, sourceLifetime, by
              simpa [owningRef] using hsourceSlot⟩
          rcases hheap ownedLocation howns with ⟨address, hheapLocation⟩
          rw [hownedVar] at hheapLocation
          cases hheapLocation
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
          have hownedVar : ownedLocation = VariableProjection x := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc
          have howns : ProgramStore.Owns store ownedLocation :=
            ⟨sourceLocation, sourceLifetime, by
              simpa [owningRef] using hsourceSlot⟩
          rcases hheap ownedLocation howns with ⟨address, hheapLocation⟩
          rw [hownedVar] at hheapLocation
          cases hheapLocation
  | @borrow source target mutable borrowLifetime targetLifetime targetTy
      hsource htarget ihSource ihTarget =>
      intro hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store _
            (.ty (.borrow _ _)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrowLive borrowedLocation mutable target hinitialized htargetLoc =>
          have hborrowedVar : borrowedLocation = VariableProjection x := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc
          have htargetVar : store.loc target = some (VariableProjection x) := by
            simpa [hborrowedVar] using htargetLoc
          rcases ihTarget htargetVar with htargetConflict | hwrite
          · right
            rcases LValTyping.contains_borrow hsource PartialTyContains.here with
              ⟨holder, hcontains⟩
            exact WriteProhibited.of_contains_conflict hcontains htargetConflict
          · exact Or.inr hwrite
      | @borrowStale borrowedLocation mutable target hstale =>
          exact False.elim (hstale ⟨_, _, htarget⟩)

theorem locReads_var_conflict_or_writeProhibited_whenInitialized
    {store : ProgramStore} {env : Env} {x : Name} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
      LocReads store lv (VariableProjection x) →
      lv ⋈ (.var x) ∨ WriteProhibited env (.var x) := by
  intro hsafe hheap lv partialTy lifetime htyping
  induction htyping generalizing x with
  | var hslot =>
      intro hreads
      cases hreads
  | box hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_var_conflict_or_writeProhibited_whenInitialized
              hsafe hheap hsource hloc with hconflict | hwrite
          · exact Or.inl hconflict
          · exact Or.inr hwrite
      | there hsourceReads =>
          rcases ih hsourceReads with hconflict | hwrite
          · exact Or.inl hconflict
          · exact Or.inr hwrite
  | boxFull hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_var_conflict_or_writeProhibited_whenInitialized
              hsafe hheap hsource hloc with hconflict | hwrite
          · exact Or.inl hconflict
          · exact Or.inr hwrite
      | there hsourceReads =>
          rcases ih hsourceReads with hconflict | hwrite
          · exact Or.inl hconflict
          · exact Or.inr hwrite
  | @borrow source target mutable borrowLifetime targetLifetime targetTy
      hsource htarget ihSource ihTarget =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_var_conflict_or_writeProhibited_whenInitialized
              hsafe hheap hsource hloc with hconflict | hwrite
          · exact Or.inl hconflict
          · exact Or.inr hwrite
      | there hsourceReads =>
          rcases ihSource hsourceReads with hconflict | hwrite
          · exact Or.inl hconflict
          · exact Or.inr hwrite

theorem borrowDependencyWhenInitialized_var_writeProhibited
    {env : Env} {store : ProgramStore} {x holder : Name} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    ∀ {value : PartialValue} {partialTy : PartialTy} {dependency : Location},
      (∀ {mutable : Bool} {target : LVal},
        PartialTyContains partialTy (.borrow mutable target) →
        env ⊢ holder ↝ (.borrow mutable target)) →
      BorrowDependencyWhenInitialized env store value partialTy dependency →
      dependency = VariableProjection x →
      WriteProhibited env (.var x) := by
  intro hsafe hheap value partialTy dependency hcontains hdependency
  induction hdependency generalizing holder x with
  | @borrow location dependency mutable target hinitialized hloc hreads =>
      intro hdependencyEq
      rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
      have hreadsVar : LocReads store target (VariableProjection x) := by
        simpa [hdependencyEq] using hreads
      rcases locReads_var_conflict_or_writeProhibited_whenInitialized
          hsafe hheap htargetTyping hreadsVar with hconflict | hwrite
      · exact WriteProhibited.of_contains_conflict
          (hcontains PartialTyContains.here) hconflict
      · exact hwrite
  | boxInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih (by
        intro mutable target hcontainsInner
        exact hcontains (PartialTyContains.box hcontainsInner))
        hdependencyEq
  | boxFullInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih (by
        intro mutable target hcontainsInner
        exact hcontains (PartialTyContains.tyBox hcontainsInner))
        hdependencyEq

theorem reachesWhenInitialized_var_ne_of_stored_not_writeProhibited
    {env : Env} {store : ProgramStore} {x holder : Name}
    {storage : Location} {value : PartialValue} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    store.slotAt storage = some { value := value, lifetime := lifetime } →
    ValidPartialValueWhenInitialized env store value partialTy →
    (∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      env ⊢ holder ↝ (.borrow mutable target)) →
    ¬ WriteProhibited env (.var x) →
    ∀ {location : Location},
      ReachesWhenInitialized env store value partialTy location →
      location ≠ VariableProjection x := by
  intro hsafe hheap hstored hvalid hcontains hnotWrite location hreach
  induction hreach generalizing storage holder lifetime with
  | undefOf hskel hstrength howner =>
      intro hlocation
      have howns :=
        RuntimeFrame.store_owns_of_ownerReaches_stored hstored
          (OwnerReaches.undefOf hskel hstrength howner)
      rcases hheap _ howns with ⟨address, hheapLocation⟩
      rw [hlocation] at hheapLocation
      cases hheapLocation
  | boxHere hslot =>
      intro hlocation
      rename_i ownedLocation ownedSlot inner
      have howns : ProgramStore.Owns store ownedLocation :=
        ⟨storage, lifetime, by
          simpa [owningRef] using hstored⟩
      rcases hheap ownedLocation howns with ⟨address, hheapLocation⟩
      rw [hlocation] at hheapLocation
      cases hheapLocation
  | boxInner hslot _hinner ih =>
      intro hlocation
      cases hvalid with
      | box hvalidSlot hinnerValid =>
          have hslotEq := Option.some.inj (hslot.symm.trans hvalidSlot)
          subst hslotEq
          exact ih hslot hinnerValid
            (by
              intro mutable target hcontainsInner
              exact hcontains (PartialTyContains.box hcontainsInner))
            hlocation
  | boxFullHere hslot =>
      intro hlocation
      rename_i ownedLocation ownedSlot ty
      have howns : ProgramStore.Owns store ownedLocation :=
        ⟨storage, lifetime, by
          simpa [owningRef] using hstored⟩
      rcases hheap ownedLocation howns with ⟨address, hheapLocation⟩
      rw [hlocation] at hheapLocation
      cases hheapLocation
  | boxFullInner hslot _hinner ih =>
      intro hlocation
      cases hvalid with
      | boxFull hvalidSlot hinnerValid =>
          have hslotEq := Option.some.inj (hslot.symm.trans hvalidSlot)
          subst hslotEq
          exact ih hslot hinnerValid
            (by
              intro mutable target hcontainsInner
              exact hcontains (PartialTyContains.tyBox hcontainsInner))
            hlocation
  | borrow hinitialized hloc hreads =>
      intro hlocation
      subst hlocation
      exact hnotWrite
        (borrowDependencyWhenInitialized_var_writeProhibited
          hsafe hheap hcontains
          (BorrowDependencyWhenInitialized.borrow hinitialized hloc hreads) rfl)

theorem locReads_var_writeProhibited_or_base_whenInitialized
    {store : ProgramStore} {env : Env} {x : Name} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
      LocReads store lv (VariableProjection x) →
      WriteProhibited env (.var x) ∨ LVal.base lv = x := by
  intro hsafe hheap lv partialTy lifetime htyping
  induction htyping with
  | var hslot =>
      intro hreads
      cases hreads
  | box hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_var_conflict_or_writeProhibited_whenInitialized
              hsafe hheap hsource hloc with hconflict | hwrite
          · exact Or.inr (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inl hwrite
      | there hsourceReads =>
          rcases ih hsourceReads with hwrite | hbase
          · exact Or.inl hwrite
          · exact Or.inr (by simpa [LVal.base] using hbase)
  | boxFull hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_var_conflict_or_writeProhibited_whenInitialized
              hsafe hheap hsource hloc with hconflict | hwrite
          · exact Or.inr (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inl hwrite
      | there hsourceReads =>
          rcases ih hsourceReads with hwrite | hbase
          · exact Or.inl hwrite
          · exact Or.inr (by simpa [LVal.base] using hbase)
  | borrow hsource htarget ihSource ihTarget =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_var_conflict_or_writeProhibited_whenInitialized
              hsafe hheap hsource hloc with hconflict | hwrite
          · exact Or.inr (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inl hwrite
      | there hsourceReads =>
          rcases ihSource hsourceReads with hwrite | hbase
          · exact Or.inl hwrite
          · exact Or.inr (by simpa [LVal.base] using hbase)

theorem ReachesWhenInitialized.owner_or_borrow {env : Env}
    {store : ProgramStore} :
    ∀ {value : PartialValue} {partialTy : PartialTy} {location : Location},
      ReachesWhenInitialized env store value partialTy location →
      OwnerReaches store value partialTy location ∨
        BorrowDependencyWhenInitialized env store value partialTy location := by
  intro value partialTy location hreach
  induction hreach with
  | undefOf hskel hstrength howner =>
      exact Or.inl (OwnerReaches.undefOf hskel hstrength howner)
  | boxHere hslot =>
      exact Or.inl (OwnerReaches.boxHere hslot)
  | boxInner hslot _hinner ih =>
      rcases ih with howner | hborrow
      · exact Or.inl (OwnerReaches.boxInner hslot howner)
      · exact Or.inr (BorrowDependencyWhenInitialized.boxInner hslot hborrow)
  | boxFullHere hslot =>
      exact Or.inl (OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _hinner ih =>
      rcases ih with howner | hborrow
      · exact Or.inl (OwnerReaches.boxFullInner hslot howner)
      · exact Or.inr (BorrowDependencyWhenInitialized.boxFullInner hslot hborrow)
  | borrow hinitialized hloc hreads =>
      exact Or.inr (BorrowDependencyWhenInitialized.borrow hinitialized hloc hreads)

theorem borrowDependencyWhenInitialized_var_writeProhibited_or_mem_vars
    {store : ProgramStore} {env : Env} {x : Name}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    BorrowDependencyWhenInitialized env store value partialTy dependency →
    dependency = VariableProjection x →
    WriteProhibited env (.var x) ∨ x ∈ PartialTy.vars partialTy := by
  intro hsafe hheap hdependency
  induction hdependency with
  | borrow hinitialized _hloc hreads =>
      intro hdependencyEq
      rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases locReads_var_writeProhibited_or_base_whenInitialized
          hsafe hheap htargetTyping (by simpa [hdependencyEq] using hreads) with
        hwrite | hbase
      · exact Or.inl hwrite
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars, hbase])
  | boxInner _hslot _hinner ih =>
      intro hdependencyEq
      rcases ih hdependencyEq with hwrite | hmem
      · exact Or.inl hwrite
      · exact Or.inr (by simpa [PartialTy.vars] using hmem)
  | boxFullInner _hslot _hinner ih =>
      intro hdependencyEq
      rcases ih hdependencyEq with hwrite | hmem
      · exact Or.inl hwrite
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars] using hmem)

theorem ownerReaches_ne_var_of_heap
    {store : ProgramStore} {value : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap value →
    OwnerReaches store value partialTy location →
    location ≠ VariableProjection x := by
  intro hheap hvalueHeap hreach
  induction hreach with
  | undefOf _hskel _hstrength _howner ih =>
      exact ih hvalueHeap
  | boxHere hslot =>
      intro hloc
      have hvalueHeapVar :
          PartialValueOwnerTargetsHeap
            (.value (.ref { location := VariableProjection x, owner := true })) := by
        simpa [hloc] using hvalueHeap
      have howned :
          VariableProjection x ∈ partialValueOwningLocations
            (.value (.ref { location := VariableProjection x, owner := true })) := by
        simpa using
          (mem_partialValueOwningLocations_ref_true
            (ref := { location := VariableProjection x, owner := true }) rfl)
      rcases hvalueHeapVar (VariableProjection x) howned with
        ⟨address, hheapLocation⟩
      cases hheapLocation
  | boxInner hslot _hinner ih =>
      exact ih (partialValueOwnerTargetsHeap_of_slot hheap hslot)
  | boxFullHere hslot =>
      intro hloc
      have hvalueHeapVar :
          PartialValueOwnerTargetsHeap
            (.value (.ref { location := VariableProjection x, owner := true })) := by
        simpa [hloc] using hvalueHeap
      have howned :
          VariableProjection x ∈ partialValueOwningLocations
            (.value (.ref { location := VariableProjection x, owner := true })) := by
        simpa using
          (mem_partialValueOwningLocations_ref_true
            (ref := { location := VariableProjection x, owner := true }) rfl)
      rcases hvalueHeapVar (VariableProjection x) howned with
        ⟨address, hheapLocation⟩
      cases hheapLocation
  | boxFullInner hslot _hinner ih =>
      exact ih (partialValueOwnerTargetsHeap_of_slot hheap hslot)

theorem reachesWhenInitialized_ne_var_of_varsProtectedIn
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    SafeAbstraction store sourceEnv →
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    (∀ y, y ∈ PartialTy.vars partialTy →
      WriteProhibited observerEnv (.var y)) →
    ¬ WriteProhibited sourceEnv (.var x) →
    ¬ WriteProhibited observerEnv (.var x) →
    RuntimeFrame.ReachesWhenInitialized sourceEnv store partialValue partialTy
      location →
    location ≠ VariableProjection x := by
  intro hsafe hheap hvalueHeap hvarsObserver hnotWriteSource hnotWriteObserver
    hreach hlocation
  subst hlocation
  rcases ReachesWhenInitialized.owner_or_borrow hreach with
    howner | hdependency
  · exact ownerReaches_ne_var_of_heap hheap hvalueHeap howner rfl
  · rcases borrowDependencyWhenInitialized_var_writeProhibited_or_mem_vars
        (x := x) hsafe hheap hdependency rfl with hwrite | hmem
    · exact hnotWriteSource hwrite
    · exact hnotWriteObserver (hvarsObserver x hmem)

theorem value_reachesWhenInitialized_ne_var_of_varsProtectedIn
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {value : Value} {ty : Ty} {location : Location} {x : Name} :
    SafeAbstraction store sourceEnv →
    StoreOwnerTargetsHeap store →
    ValueOwnerTargetsHeap value →
    (∀ y, y ∈ Ty.vars ty → WriteProhibited observerEnv (.var y)) →
    ¬ WriteProhibited sourceEnv (.var x) →
    ¬ WriteProhibited observerEnv (.var x) →
    RuntimeFrame.ReachesWhenInitialized sourceEnv store (.value value) (.ty ty)
      location →
    location ≠ VariableProjection x := by
  intro hsafe hheap hvalueHeap hvars hnotWriteSource hnotWriteObserver hreach
  exact reachesWhenInitialized_ne_var_of_varsProtectedIn
    hsafe hheap (ValueOwnerTargetsHeap.partial hvalueHeap)
    (by
      intro y hy
      exact hvars y (by simpa [PartialTy.vars] using hy))
    hnotWriteSource hnotWriteObserver hreach

theorem envWrite_var_rhs_vars_writeProhibited {env env' : Env}
    {x y : Name} {envSlot : EnvSlot} {rhsTy : Ty} :
    env.slotAt x = some envSlot →
    EnvWrite env (.var x) rhsTy env' →
    y ∈ Ty.vars rhsTy →
    WriteProhibited env' (.var y) := by
  intro henvX hwrite hmem
  have henv' :
      env' = env.update x { envSlot with ty := .ty rhsTy } :=
    envWrite_zero_var_eq henvX hwrite
  rcases ty_vars_mem_contains y hmem with
    ⟨mutable, target, hcontains, hbase⟩
  have hcontainsEnv' :
      env' ⊢ x ↝ (.borrow mutable target) := by
    refine ⟨{ envSlot with ty := .ty rhsTy }, ?_, hcontains⟩
    rw [henv']
    simp [Env.update]
  cases mutable
  · exact Or.inr ⟨x, target, hcontainsEnv', by
      simpa [PathConflicts, LVal.base] using hbase⟩
  · exact Or.inl ⟨x, target, hcontainsEnv', by
      simpa [PathConflicts, LVal.base] using hbase⟩

theorem envSlot_partialTy_vars_writeProhibited {env : Env}
    {holder y : Name} {slot : EnvSlot} :
    env.slotAt holder = some slot →
    y ∈ PartialTy.vars slot.ty →
    WriteProhibited env (.var y) := by
  intro hslot hmem
  rcases partialTy_vars_mem_contains y hmem with
    ⟨mutable, target, hcontains, hbase⟩
  have hcontainsEnv : env ⊢ holder ↝ (.borrow mutable target) :=
    ⟨slot, hslot, hcontains⟩
  cases mutable
  · exact Or.inr ⟨holder, target, hcontainsEnv, by
      simpa [PathConflicts, LVal.base] using hbase⟩
  · exact Or.inl ⟨holder, target, hcontainsEnv, by
      simpa [PathConflicts, LVal.base] using hbase⟩

theorem LValTyping.envWrite_var_to_source_of_no_conflicts
    {env env' : Env} {x : Name} {envSlot : EnvSlot} {rhsTy : Ty} :
    env.slotAt x = some envSlot →
    EnvWrite env (.var x) rhsTy env' →
    (∀ holder mutable target,
      env' ⊢ holder ↝ (.borrow mutable target) →
      ¬ target ⋈ (.var x)) →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      ¬ lv ⋈ (.var x) →
      LValTyping env' lv partialTy lifetime →
      LValTyping env lv partialTy lifetime := by
  intro henvX hwrite hnoConflicts lv partialTy lifetime hnotConflict htyping
  have henv' :
      env' = env.update x { envSlot with ty := .ty rhsTy } :=
    envWrite_zero_var_eq henvX hwrite
  induction htyping with
  | var hslot =>
      rename_i y slot
      have hyx : y ≠ x := by
        intro hyx
        exact hnotConflict (by simpa [PathConflicts, LVal.base, hyx])
      exact .var (by simpa [henv', Env.update, hyx] using hslot)
  | box _ ih =>
      exact .box (ih hnotConflict)
  | boxFull _ ih =>
      exact .boxFull (ih hnotConflict)
  | borrow hborrow htarget ihBorrow ihTarget =>
      rename_i source target mutable borrowLifetime targetLifetime targetTy
      have hborrowSource :
          LValTyping env source (.ty (.borrow mutable target))
            borrowLifetime :=
        ihBorrow hnotConflict
      rcases LValTyping.contains_borrow hborrow PartialTyContains.here with
        ⟨holder, hcontains⟩
      have htargetNoConflict : ¬ target ⋈ (.var x) :=
        hnoConflicts holder mutable target hcontains
      exact .borrow hborrowSource (ihTarget htargetNoConflict)

theorem validPartialValueWhenInitialized_envWrite_var_of_no_write
    {env env' : Env} {store : ProgramStore} {x : Name}
    {envSlot : EnvSlot} {rhsTy : Ty}
    {value : PartialValue} {partialTy : PartialTy} :
    env.slotAt x = some envSlot →
    EnvWrite env (.var x) rhsTy env' →
    ¬ WriteProhibited env' (.var x) →
    (∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      ∃ holder, env' ⊢ holder ↝ (.borrow mutable target)) →
    ValidPartialValueWhenInitialized env store value partialTy →
    ValidPartialValueWhenInitialized env' store value partialTy := by
  intro henvX hwrite hnotWrite hcontainsResult hvalid
  have hnoConflicts :
      ∀ holder mutable target,
        env' ⊢ holder ↝ (.borrow mutable target) →
        ¬ target ⋈ (.var x) := by
    intro holder mutable target hcontains hconflict
    exact hnotWrite (WriteProhibited.of_contains_conflict hcontains hconflict)
  induction hvalid with
  | unit =>
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      exact ValidPartialValueWhenInitialized.undefOf hinner hstrength
  | @borrowLive location mutable target _hinitialized hloc =>
      by_cases htarget : TargetInitialized env' target
      · exact ValidPartialValueWhenInitialized.borrowLive htarget hloc
      · exact ValidPartialValueWhenInitialized.borrowStale htarget
  | @borrowStale location mutable target hstale =>
      by_cases htarget : TargetInitialized env' target
      · rcases hcontainsResult PartialTyContains.here with
          ⟨holder, hcontains⟩
        rcases htarget with ⟨targetTy, targetLifetime, htargetTyping⟩
        have htargetNoConflict : ¬ target ⋈ (.var x) :=
          hnoConflicts holder mutable target hcontains
        exact False.elim
          (hstale ⟨targetTy, targetLifetime,
            LValTyping.envWrite_var_to_source_of_no_conflicts
              henvX hwrite hnoConflicts htargetNoConflict htargetTyping⟩)
      · exact ValidPartialValueWhenInitialized.borrowStale htarget
  | box hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.box hslot
        (ih (by
          intro mutable target hcontains
          exact hcontainsResult (PartialTyContains.box hcontains)))
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.boxFull hslot
        (ih (by
          intro mutable target hcontains
          exact hcontainsResult (PartialTyContains.tyBox hcontains)))

theorem lval_loc_var_conflict_or_writeProhibited_envWrite_var
    {store : ProgramStore} {env env' : Env} {x : Name}
    {envSlot : EnvSlot} {rhsTy : Ty} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    env.slotAt x = some envSlot →
    EnvWrite env (.var x) rhsTy env' →
    ¬ WriteProhibited env' (.var x) →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env' lv partialTy lifetime →
      store.loc lv = some (VariableProjection x) →
      lv ⋈ (.var x) ∨ WriteProhibited env' (.var x) := by
  intro hsafe hheap henvX hwrite hnotWrite lv partialTy lifetime htyping
  have hnoConflicts :
      ∀ holder mutable target,
        env' ⊢ holder ↝ (.borrow mutable target) →
        ¬ target ⋈ (.var x) := by
    intro holder mutable target hcontains hconflict
    exact hnotWrite (WriteProhibited.of_contains_conflict hcontains hconflict)
  induction htyping with
  | var hslot =>
      rename_i y slot
      intro hloc
      left
      change y = x
      simpa [ProgramStore.loc, VariableProjection] using hloc
  | box hsource ih =>
      rename_i source inner sourceLifetime
      intro hloc
      by_cases hbase : LVal.base source = x
      · left
        simpa [PathConflicts, LVal.base, hbase]
      · have hsourceEnv :
            LValTyping env source (.box inner) sourceLifetime :=
          LValTyping.envWrite_var_to_source_of_no_conflicts
            henvX hwrite hnoConflicts
            (by simpa [PathConflicts, LVal.base] using hbase) hsource
        have hsourceAbs :
            LValLocationAbstractionWhenInitialized env store source
              (.box inner) :=
          lvalTyping_defined_location_whenInitialized hsafe hsourceEnv
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
            hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @box ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
            have hownedVar : ownedLocation = VariableProjection x := by
              simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc
            have howns : ProgramStore.Owns store ownedLocation :=
              ⟨sourceLocation, sourceLifetime, by
                simpa [owningRef] using hsourceSlot⟩
            rcases hheap ownedLocation howns with ⟨address, hheapLocation⟩
            rw [hownedVar] at hheapLocation
            cases hheapLocation
  | boxFull hsource ih =>
      rename_i source inner sourceLifetime
      intro hloc
      by_cases hbase : LVal.base source = x
      · left
        simpa [PathConflicts, LVal.base, hbase]
      · have hsourceEnv :
            LValTyping env source (.ty (.box inner)) sourceLifetime :=
          LValTyping.envWrite_var_to_source_of_no_conflicts
            henvX hwrite hnoConflicts
            (by simpa [PathConflicts, LVal.base] using hbase) hsource
        have hsourceAbs :
            LValLocationAbstractionWhenInitialized env store source
              (.ty (.box inner)) :=
          lvalTyping_defined_location_whenInitialized hsafe hsourceEnv
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
            hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @boxFull ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
            have hownedVar : ownedLocation = VariableProjection x := by
              simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc
            have howns : ProgramStore.Owns store ownedLocation :=
              ⟨sourceLocation, sourceLifetime, by
                simpa [owningRef] using hsourceSlot⟩
            rcases hheap ownedLocation howns with ⟨address, hheapLocation⟩
            rw [hownedVar] at hheapLocation
            cases hheapLocation
  | @borrow source target mutable borrowLifetime targetLifetime targetTy
      hsource htarget ihSource ihTarget =>
      intro hloc
      by_cases hbase : LVal.base source = x
      · left
        simpa [PathConflicts, LVal.base, hbase]
      · have hsourceEnv :
            LValTyping env source (.ty (.borrow mutable target))
              borrowLifetime :=
          LValTyping.envWrite_var_to_source_of_no_conflicts
            henvX hwrite hnoConflicts
            (by simpa [PathConflicts, LVal.base] using hbase) hsource
        have hsourceAbs :
            LValLocationAbstractionWhenInitialized env store source
              (.ty (.borrow mutable target)) :=
          lvalTyping_defined_location_whenInitialized hsafe hsourceEnv
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
            hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @borrowLive borrowedLocation _mutable _target hinitialized htargetLoc =>
            have hborrowedVar : borrowedLocation = VariableProjection x := by
              simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc
            have htargetLocX :
                store.loc target = some (VariableProjection x) := by
              simpa [hborrowedVar] using htargetLoc
            rcases ihTarget htargetLocX with htargetConflict | hwrite'
            · right
              rcases LValTyping.contains_borrow hsource PartialTyContains.here with
                ⟨holder, hcontains⟩
              exact WriteProhibited.of_contains_conflict hcontains
                htargetConflict
            · exact Or.inr hwrite'
        | @borrowStale _borrowedLocation _mutable _target hstale =>
            by_cases htargetBase : LVal.base target = x
            · right
              rcases LValTyping.contains_borrow hsource PartialTyContains.here with
                ⟨holder, hcontains⟩
              exact WriteProhibited.of_contains_conflict hcontains
                (by simpa [PathConflicts, LVal.base, htargetBase])
            · have htargetEnv :
                  LValTyping env target (.ty targetTy) targetLifetime :=
                LValTyping.envWrite_var_to_source_of_no_conflicts
                  henvX hwrite hnoConflicts
                  (by simpa [PathConflicts, LVal.base] using htargetBase)
                  htarget
              exact False.elim (hstale ⟨targetTy, targetLifetime, htargetEnv⟩)

theorem locReads_var_conflict_or_writeProhibited_envWrite_var
    {store : ProgramStore} {env env' : Env} {x : Name}
    {envSlot : EnvSlot} {rhsTy : Ty} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    env.slotAt x = some envSlot →
    EnvWrite env (.var x) rhsTy env' →
    ¬ WriteProhibited env' (.var x) →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env' lv partialTy lifetime →
      LocReads store lv (VariableProjection x) →
      lv ⋈ (.var x) ∨ WriteProhibited env' (.var x) := by
  intro hsafe hheap henvX hwrite hnotWrite lv partialTy lifetime htyping
  induction htyping with
  | var hslot =>
      intro hreads
      cases hreads
  | box hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_var_conflict_or_writeProhibited_envWrite_var
              hsafe hheap henvX hwrite hnotWrite hsource hloc with
            hconflict | hwrite'
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite'
      | there hsourceReads =>
          rcases ih hsourceReads with hconflict | hwrite'
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite'
  | boxFull hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_var_conflict_or_writeProhibited_envWrite_var
              hsafe hheap henvX hwrite hnotWrite hsource hloc with
            hconflict | hwrite'
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite'
      | there hsourceReads =>
          rcases ih hsourceReads with hconflict | hwrite'
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite'
  | borrow hsource htarget ihSource ihTarget =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_var_conflict_or_writeProhibited_envWrite_var
              hsafe hheap henvX hwrite hnotWrite hsource hloc with
            hconflict | hwrite'
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite'
      | there hsourceReads =>
          rcases ihSource hsourceReads with hconflict | hwrite'
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite'

theorem borrowDependencyWhenInitialized_envWrite_var_writeProhibited
    {env env' : Env} {store : ProgramStore} {x holder : Name}
    {envSlot : EnvSlot} {rhsTy : Ty} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    env.slotAt x = some envSlot →
    EnvWrite env (.var x) rhsTy env' →
    ¬ WriteProhibited env' (.var x) →
    ∀ {value : PartialValue} {partialTy : PartialTy}
      {dependency : Location},
      (∀ {mutable : Bool} {target : LVal},
        PartialTyContains partialTy (.borrow mutable target) →
        env' ⊢ holder ↝ (.borrow mutable target)) →
      BorrowDependencyWhenInitialized env' store value partialTy dependency →
      dependency = VariableProjection x →
      WriteProhibited env' (.var x) := by
  intro hsafe hheap henvX hwrite hnotWrite value partialTy dependency
    hcontains hdependency
  induction hdependency generalizing holder x with
  | @borrow location dependency mutable target hinitialized hloc hreads =>
      intro hdependencyEq
      rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
      have hreadsVar : LocReads store target (VariableProjection x) := by
        simpa [hdependencyEq] using hreads
      rcases locReads_var_conflict_or_writeProhibited_envWrite_var
          hsafe hheap henvX hwrite hnotWrite htargetTyping hreadsVar with
        hconflict | hwrite'
      · exact WriteProhibited.of_contains_conflict
          (hcontains PartialTyContains.here) hconflict
      · exact hwrite'
  | boxInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih henvX hwrite hnotWrite (by
        intro mutable target hcontainsInner
        exact hcontains (PartialTyContains.box hcontainsInner))
        hdependencyEq
  | boxFullInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih henvX hwrite hnotWrite (by
        intro mutable target hcontainsInner
        exact hcontains (PartialTyContains.tyBox hcontainsInner))
        hdependencyEq

theorem reachesWhenInitialized_var_ne_of_envWrite_var_not_writeProhibited
    {env env' : Env} {store : ProgramStore} {x holder : Name}
    {envSlot : EnvSlot} {rhsTy : Ty}
    {value : PartialValue} {partialTy : PartialTy} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    env.slotAt x = some envSlot →
    EnvWrite env (.var x) rhsTy env' →
    ¬ WriteProhibited env' (.var x) →
    PartialValueOwnerTargetsHeap value →
    (∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      env' ⊢ holder ↝ (.borrow mutable target)) →
    ∀ {location : Location},
      ReachesWhenInitialized env' store value partialTy location →
      location ≠ VariableProjection x := by
  intro hsafe hheap henvX hwrite hnotWrite hvalueHeap hcontains location
    hreach hlocation
  rcases ReachesWhenInitialized.owner_or_borrow hreach with howner | hdependency
  · exact ownerReaches_ne_var_of_heap hheap hvalueHeap howner hlocation
  · exact hnotWrite
      (borrowDependencyWhenInitialized_envWrite_var_writeProhibited
        hsafe hheap henvX hwrite hnotWrite hcontains hdependency hlocation)

theorem preservation_move_var_multistep_runtime_whenInitialized_of_wellFormed
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {x : Name} {finalValue : Value} {ty : Ty} :
    WellFormedEnvWhenInitialized env₁ lifetime →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.move (.var x)) →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    TermTyping env₁ typing lifetime (.move (.var x)) ty env₂ →
    MultiStep store lifetime (.move (.var x)) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro _hwellFormed hsafe hvalidRuntime henvSlot hmove htyping hmulti
  have hnotWrite : ¬ WriteProhibited env₁ (.var x) := by
    cases htyping with
    | move _hLv hnotWrite _hmove => exact hnotWrite
  exact preservation_runtime_multistep_of_step_to_value_whenInitialized
    (env := env₂) (term := .move (.var x)) (ty := ty)
    (by intro hterminal; simp [Terminal] at hterminal)
    (by
      intro _store' _term' hstep
      cases hstep with
      | move _hread _hwrite =>
          exact ⟨_, rfl⟩)
    (by
      intro store' value hstep
      cases hstep with
      | move hread hwrite =>
          rcases hsafe.2 x { ty := .ty ty, lifetime := valueLifetime }
              henvSlot with
            ⟨sourceValue, hsourceSlot, hvalidSource⟩
          have hstoreXStep := by
            simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
          have hsourceSlotVar :
              store.slotAt (Location.var x) =
                some { value := sourceValue, lifetime := valueLifetime } := by
            simpa [VariableProjection] using hsourceSlot
          rw [hstoreXStep] at hsourceSlotVar
          injection hsourceSlotVar with hslotEq
          cases hslotEq
          have hstoreX :
              store.slotAt (VariableProjection x) =
                some { value := .value value, lifetime := valueLifetime } := by
            simpa [VariableProjection] using hstoreXStep
          have hstore' :
              store' =
                store.update (VariableProjection x)
                  { value := .undef, lifetime := valueLifetime } := by
            rcases write_eq_update_of_read hread hwrite with
              ⟨location, hloc, _hslot, hupdate⟩
            have hlocEq : location = VariableProjection x := by
              simpa [ProgramStore.loc, VariableProjection] using hloc.symm
            subst hlocEq
            simpa [VariableProjection] using hupdate
          have hvalidValueBefore :
              ValidPartialValueWhenInitialized env₁ store (.value value) (.ty ty) :=
            hvalidSource
          have hvalidValue :
              ValidPartialValueWhenInitialized env₂ store'
                (.value value) (.ty ty) := by
            rw [hstore']
            exact ValidPartialValueWhenInitialized.move_env hmove
              (validPartialValueWhenInitialized_update_of_not_live_reaches
                hvalidValueBefore
                (fun location hreach =>
                  reachesWhenInitialized_var_ne_of_stored_not_writeProhibited
                    hsafe
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hstoreX hvalidValueBefore
                    (by
                      intro mutable target hcontains
                      exact ⟨{ ty := .ty ty, lifetime := valueLifetime },
                        henvSlot, hcontains⟩)
                    hnotWrite hreach))
          have hpreserveOld :
              ∀ y envSlot oldValue,
                y ≠ x →
                env₁.slotAt y = some envSlot →
                store.slotAt (VariableProjection y) =
                  some { value := oldValue, lifetime := envSlot.lifetime } →
                ValidPartialValueWhenInitialized env₂ store'
                  oldValue envSlot.ty := by
            intro y envSlot oldValue hyx henvY hstoreY
            have hvalidOldBefore :
                ValidPartialValueWhenInitialized env₁ store oldValue envSlot.ty := by
              rcases hsafe.2 y envSlot henvY with
                ⟨safeValue, hsafeSlot, hvalidSafe⟩
              rw [hstoreY] at hsafeSlot
              injection hsafeSlot with hslotEq
              cases hslotEq
              exact hvalidSafe
            rw [hstore']
            exact ValidPartialValueWhenInitialized.move_env hmove
              (validPartialValueWhenInitialized_update_of_not_live_reaches
                hvalidOldBefore
                (fun location hreach =>
                  reachesWhenInitialized_var_ne_of_stored_not_writeProhibited
                    hsafe
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hstoreY hvalidOldBefore
                    (by
                      intro mutable target hcontains
                      exact ⟨envSlot, henvY, hcontains⟩)
                    hnotWrite hreach))
          exact preservation_move_var_step_runtime_whenInitialized_of_preserved
            hsafe hvalidRuntime henvSlot hmove htyping
            (Step.move (lifetime := lifetime) hread hwrite)
            hvalidValue hpreserveOld)
    hmulti

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

theorem dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized_of_frames
    {env : Env} {store store' : ProgramStore}
    {values : List PartialValue} {storage location : Location}
    {value : PartialValue} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    Drops store values store' →
    ValidStore store →
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
  intro hdrops hvalidStore hstored hvalid havoidStorage hownerDisjoint
    hdependencyFrame hreach
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

/--
Dropping values that have already been detached from the store preserves the
initialized abstraction.  This is the post-write assignment frame: the old lhs
value may recursively drop heap cells, but none of those owned cells is still
owned by the written store.
-/
theorem safeAbstractionWhenInitialized_drops_of_orphaned_values_early
    {store store' : ProgramStore} {env : Env} {current : Lifetime}
    {values : List PartialValue} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ dropValue, dropValue ∈ values →
      PartialValueOwnerTargetsHeap dropValue) →
    (∀ owned, owned ∈ partialValuesOwningLocations values →
      ¬ ProgramStore.Owns store owned) →
    Drops store values store' →
    SafeAbstraction store' env := by
  intro _hwell hsafe hvalidStore hheap hvaluesHeap hownersOrphaned hdrops
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
          DropsAvoids store values (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hvaluesHeap
      exact ⟨slot, dropsAvoids_slotAt_preserved hdrops havoidVar hslot⟩
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    have havoidVar :
        DropsAvoids store values (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hvaluesHeap
    have hstoreSlot' :
        store'.slotAt (VariableProjection x) =
          some { value := oldValue, lifetime := envSlot.lifetime } :=
      dropsAvoids_slotAt_preserved hdrops havoidVar hstoreSlot
    have hvalidOld' :
        ValidPartialValueWhenInitialized env store' oldValue envSlot.ty :=
      RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_live_reaches
        hdrops hvalidOld
        (by
          intro reached hreach
          exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized
            hdrops hsafe hvalidStore hheap hvaluesHeap hstoreSlot hvalidOld
            havoidVar
            (by
              intro reached' howner dropValue hmem howned
              have hownsReached :
                  ProgramStore.Owns store reached' :=
                RuntimeFrame.store_owns_of_reaches_stored_validPartialValueWhenInitialized
                  hstoreSlot hvalidOld howner
              exact
                hownersOrphaned reached'
                  (by
                    have hflat :
                        reached' ∈ values.flatMap partialValueOwningLocations :=
                      List.mem_flatMap.mpr ⟨dropValue, hmem, howned⟩
                    simpa [partialValuesOwningLocations] using hflat)
                  hownsReached)
            (by
              intro dependency hdependency
              exact
                RuntimeFrame.dropsAvoids_of_borrowDependencyWhenInitialized_unprotected_values
                  hdrops hsafe hvalidStore hheap hvaluesHeap
                  (by
                    intro dropValue hmem owned howned root hprotected
                    have hownedAll :
                        owned ∈ partialValuesOwningLocations values := by
                      have hflat :
                          owned ∈ values.flatMap partialValueOwningLocations :=
                        List.mem_flatMap.mpr ⟨dropValue, hmem, howned⟩
                      simpa [partialValuesOwningLocations] using hflat
                    cases hprotected with
                    | inl hroot =>
                        subst hroot
                        rcases hvaluesHeap dropValue hmem
                            (VariableProjection root) howned with
                          ⟨address, hheapLocation⟩
                        cases hheapLocation
                    | inr hpath =>
                        exact hownersOrphaned owned hownedAll
                          (ProgramStore.OwnsTransitively.to_owns hpath))
                  hdependency)
            hreach)
    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩

/-- Canonical components of an `R-Assign` step. -/
theorem assign_step_components {store store' : ProgramStore}
    {lifetime : Lifetime} {lhs : LVal} {value finalValue : Value} :
    Step store lifetime (.assign lhs (.val value)) store' (.val finalValue) →
    ∃ writtenStore oldSlot location,
      store.read lhs = some oldSlot ∧
      store.write lhs (.value value) = some writtenStore ∧
      Drops writtenStore [oldSlot.value] store' ∧
      store.loc lhs = some location ∧
      store.slotAt location = some oldSlot ∧
      writtenStore =
        store.update location { oldSlot with value := .value value } ∧
      finalValue = .unit := by
  intro hstep
  cases hstep with
  | assign hread hwrite hdrops =>
      rcases write_eq_update_of_read hread hwrite with
        ⟨location, hloc, hslot, hwriteEq⟩
      exact ⟨_, _, location, hread, hwrite, hdrops, hloc, hslot,
        hwriteEq, rfl⟩

/--
The owners contained in the overwritten lhs value are orphaned immediately
after the write.  Any remaining owner for such a location would either be the
just-overwritten lhs slot, contradicting store-term disjointness for the RHS
value, or a second owner of the old location, contradicting `ValidStore`.
-/
theorem droppedValueOwnersOrphaned_assign
    {store writtenStore : ProgramStore}
    {lhs : LVal} {lhsLocation : Location} {oldSlot : StoreSlot}
    {value : Value} :
    ValidRuntimeState store (.assign lhs (.val value)) →
    store.loc lhs = some lhsLocation →
    store.slotAt lhsLocation = some oldSlot →
    store.write lhs (.value value) = some writtenStore →
    ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
      ¬ ProgramStore.Owns writtenStore owned := by
  intro hvalidRuntime hlhsLoc hlhsSlot hwriteStore owned howned hownsWritten
  have hwriteEq :
      writtenStore =
        store.update lhsLocation { oldSlot with value := .value value } := by
    unfold ProgramStore.write at hwriteStore
    simp [hlhsLoc, hlhsSlot] at hwriteStore
    exact hwriteStore.symm
  have hownedOld : owned ∈ partialValueOwningLocations oldSlot.value := by
    simpa [partialValuesOwningLocations] using howned
  have hstoreOwnsOld : ProgramStore.OwnsAt store owned lhsLocation := by
    have holdValue :
        oldSlot.value = .value (owningRef owned) :=
      eq_owningRef_of_mem_partialValueOwningLocations hownedOld
    exact ⟨oldSlot.lifetime, by
      cases oldSlot with
      | mk oldValue oldLifetime =>
          cases holdValue
          simpa [owningRef] using hlhsSlot⟩
  rcases hownsWritten with ⟨storage, ownerLifetime, hownerSlotWritten⟩
  by_cases hstorage : storage = lhsLocation
  · subst storage
    rw [hwriteEq] at hownerSlotWritten
    have hnewOwnsOld :
        owned ∈ partialValueOwningLocations (.value value) := by
      have hnewValueEq :
          PartialValue.value value = .value (owningRef owned) := by
        have hslotEq :
            { oldSlot with value := PartialValue.value value } =
              StoreSlot.mk (PartialValue.value (owningRef owned))
                ownerLifetime := by
          simpa [ProgramStore.update] using hownerSlotWritten
        exact congrArg StoreSlot.value hslotEq
      exact mem_partialValueOwningLocations_of_eq_owningRef hnewValueEq
    exact
      (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
        (by
          simpa [termOwningLocations, termValues, partialValueOwningLocations]
            using hnewOwnsOld))
      ⟨lhsLocation, hstoreOwnsOld⟩
  · have hownerSlotStore :
        store.slotAt storage =
          some (StoreSlot.mk (.value (owningRef owned)) ownerLifetime) := by
      rw [hwriteEq] at hownerSlotWritten
      simpa [ProgramStore.update, hstorage] using hownerSlotWritten
    have hstorageEq :
        storage = lhsLocation :=
      (ValidRuntimeState.validStore hvalidRuntime)
        owned storage lhsLocation
        ⟨ownerLifetime, hownerSlotStore⟩ hstoreOwnsOld
    exact hstorage hstorageEq

theorem preservation_assign_var_step_runtime_whenInitialized_of_frames
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime}
    {x : Name} {oldTy : PartialTy} {value finalValue : Value}
    {rhsTy : Ty} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    LValTyping env (.var x) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTyWhenInitialized env rhsTy rhsWellLifetime →
    EnvWrite env (.var x) rhsTy env' →
    WellFormedEnvWhenInitialized env' lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign (.var x) (.val value)) store'
      (.val finalValue) →
    ValidPartialValueWhenInitialized env' store (.value value) (.ty rhsTy) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ValidPartialValueWhenInitialized env' store oldValue otherEnvSlot.ty) →
    (∀ location,
      RuntimeFrame.ReachesWhenInitialized env' store (.value value) (.ty rhsTy)
        location →
      location ≠ VariableProjection x) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.ReachesWhenInitialized env' store oldValue
          otherEnvSlot.ty location →
        location ≠ VariableProjection x) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro _hwell hsafe hvalidRuntime hlhs _hshape _hwellTy hwriteEnv
    hwellOut hvalidValue hstep hvalidValueEnv' hotherValidEnv' hvalueFrame
    hotherFrame
  rcases LValTyping.var_inv hlhs with
    ⟨envSlot, henvX, holdTyEq, htargetLifetimeEq⟩
  subst holdTyEq
  subst htargetLifetimeEq
  rcases assign_step_components hstep with
    ⟨writtenStore, oldSlot, lhsLocation, hread, hwriteStore, hdrops,
      hlhsLoc, hlhsSlot, hwriteStoreEq, hresult⟩
  cases hresult
  have hlhsLocationEq : lhsLocation = VariableProjection x := by
    simpa [ProgramStore.loc, VariableProjection] using hlhsLoc.symm
  subst hlhsLocationEq
  have hwriteEq :
      writtenStore =
        store.update (VariableProjection x)
          { oldSlot with value := .value value } := by
    simpa using hwriteStoreEq
  have henv' :
      env' = env.update x { envSlot with ty := .ty rhsTy } :=
    envWrite_zero_var_eq henvX hwriteEnv
  have hheap : StoreOwnerTargetsHeap store :=
    ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
  have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
    ValueOwnerTargetsHeap.partial
      (TermOwnerTargetsHeap.value
        (termOwnerTargetsHeap_assign_inner
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
  have hvalidValueWritten :
      ValidPartialValueWhenInitialized env' writtenStore (.value value)
        (.ty rhsTy) := by
    rw [hwriteEq]
    exact RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
      hvalidValueEnv' hvalueFrame
  have hstoreX :
      store.slotAt (VariableProjection x) = some oldSlot := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  have hlifetime : oldSlot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henvX with ⟨safeValue, hsafeSlot, _hvalid⟩
    rw [hstoreX] at hsafeSlot
    exact congrArg StoreSlot.lifetime (Option.some.inj hsafeSlot)
  have hstoreXAfter :
      writtenStore.slotAt (VariableProjection x) =
        some { value := .value value, lifetime := envSlot.lifetime } := by
    rw [hwriteEq]
    cases oldSlot with
    | mk oldValue oldLifetime =>
        cases hlifetime
        simp [ProgramStore.update]
  have hsafeWrite : SafeAbstraction writtenStore env' := by
    refine safeAbstractionWhenInitialized_update_var_partial_of_preserved
      henvX hstoreXAfter hvalidValueWritten henv' ?domain ?preserve
    · intro y hyx
      have hvarNe : VariableProjection y ≠ VariableProjection x := by
        intro hvar
        exact hyx (by simpa [VariableProjection] using hvar)
      constructor
      · intro hstoreDomain
        rcases hstoreDomain with ⟨slot, hslot⟩
        have hslotStore : store.slotAt (VariableProjection y) = some slot := by
          rw [hwriteEq] at hslot
          simpa [ProgramStore.update, hvarNe] using hslot
        exact (hsafe.1 y).mp ⟨slot, hslotStore⟩
      · intro henvDomain
        rcases (hsafe.1 y).mpr henvDomain with ⟨slot, hslot⟩
        exact ⟨slot, by
          rw [hwriteEq]
          simpa [ProgramStore.update, hvarNe] using hslot⟩
    · intro y otherEnvSlot hyx henvY
      rcases hsafe.2 y otherEnvSlot henvY with
        ⟨oldValue, hstoreY, hvalidOld⟩
      have hvalidOldEnv' :
          ValidPartialValueWhenInitialized env' store oldValue
            otherEnvSlot.ty :=
        hotherValidEnv' y otherEnvSlot oldValue hyx henvY hstoreY
      have hvarNe : VariableProjection y ≠ VariableProjection x := by
        intro hvar
        exact hyx (by simpa [VariableProjection] using hvar)
      have hstoreYWritten :
          writtenStore.slotAt (VariableProjection y) =
            some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
        rw [hwriteEq]
        simpa [ProgramStore.update, hvarNe] using hstoreY
      have hvalidOldWritten :
          ValidPartialValueWhenInitialized env' writtenStore oldValue
            otherEnvSlot.ty := by
        rw [hwriteEq]
        exact RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
          hvalidOldEnv'
          (fun location hreach =>
            hotherFrame y otherEnvSlot oldValue hyx henvY hstoreY
              location hreach)
      exact ⟨oldValue, hstoreYWritten, hvalidOldWritten⟩
  have hnewDisjoint :
      ∀ owned, owned ∈ partialValueOwningLocations (.value value) →
        ¬ ProgramStore.Owns store owned := by
    intro owned hmem howns
    exact
      (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
        (by
          simpa [termOwningLocations, termValues,
            partialValueOwningLocations] using hmem))
      howns
  have hwrittenValidStore : ValidStore writtenStore :=
    validStore_write_disjoint
      (ValidRuntimeState.validStore hvalidRuntime)
      hnewDisjoint hwriteStore
  have hwrittenHeap : StoreOwnerTargetsHeap writtenStore :=
    storeOwnerTargetsHeap_write hheap hvalueHeap hwriteStore
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [oldSlot.value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact partialValueOwnerTargetsHeap_of_slot hheap hlhsSlot
  have hdropOwnersOrphaned :
      ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
        ¬ ProgramStore.Owns writtenStore owned :=
    droppedValueOwnersOrphaned_assign hvalidRuntime hlhsLoc hlhsSlot
      hwriteStore
  have hallocatedWrite : StoreOwnersAllocated writtenStore :=
    storeOwnersAllocated_write_value_of_validValueWhenInitialized
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
      hwriteStore
  have hrootWrite : HeapSlotsRootLifetime writtenStore :=
    heapSlotsRootLifetime_write
      (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
  have hallocatedFinal : StoreOwnersAllocated store' :=
    drops_storeOwnersAllocated_of_disjoint hdrops hwrittenValidStore
      hallocatedWrite hdropOwnersOrphaned
  have hheapFinal : StoreOwnerTargetsHeap store' :=
    drops_storeOwnerTargetsHeap hdrops hwrittenHeap
  have hrootFinal : HeapSlotsRootLifetime store' :=
    drops_heapSlotsRootLifetime hdrops hrootWrite
  have hsafeFinal : SafeAbstraction store' env' :=
    safeAbstractionWhenInitialized_drops_of_orphaned_values_early
      hwellOut hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap
      hdropOwnersOrphaned hdrops
  exact ⟨validRuntimeState_assign_step_of_postWriteDrop_invariants
      (lifetime := lifetime)
      hvalidRuntime hallocatedFinal hheapFinal hrootFinal hread hwriteStore
      hdrops,
    hsafeFinal, ValidPartialValueWhenInitialized.unit⟩

theorem preservation_assign_var_step_runtime_whenInitialized_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime}
    {x : Name} {oldTy : PartialTy} {value finalValue : Value}
    {rhsTy : Ty} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    LValTyping env (.var x) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTyWhenInitialized env rhsTy rhsWellLifetime →
    EnvWrite env (.var x) rhsTy env' →
    ¬ WriteProhibited env' (.var x) →
    WellFormedEnvWhenInitialized env' lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign (.var x) (.val value)) store'
      (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwell hsafe hvalidRuntime hlhs hshape hwellTy hwriteEnv
    hnotWrite hwellOut hvalidValue hstep
  rcases LValTyping.var_inv hlhs with
    ⟨envSlot, henvX, holdTyEq, htargetLifetimeEq⟩
  subst holdTyEq
  subst htargetLifetimeEq
  have henv' :
      env' = env.update x { envSlot with ty := .ty rhsTy } :=
    envWrite_zero_var_eq henvX hwriteEnv
  have henvX' :
      env'.slotAt x = some { envSlot with ty := .ty rhsTy } := by
    rw [henv']
    simp [Env.update]
  have hheap : StoreOwnerTargetsHeap store :=
    ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
  have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
    ValueOwnerTargetsHeap.partial
      (TermOwnerTargetsHeap.value
        (termOwnerTargetsHeap_assign_inner
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
  exact
    preservation_assign_var_step_runtime_whenInitialized_of_frames
      hwell hsafe hvalidRuntime hlhs hshape hwellTy hwriteEnv hwellOut
      hvalidValue hstep
      (RuntimeFrame.validPartialValueWhenInitialized_envWrite_var_of_no_write
        henvX hwriteEnv hnotWrite
        (by
          intro mutable target hcontains
          exact ⟨x, { envSlot with ty := .ty rhsTy }, henvX', hcontains⟩)
        hvalidValue)
      (by
        intro y otherEnvSlot oldValue hyx henvY hstoreY
        rcases hsafe.2 y otherEnvSlot henvY with
          ⟨safeValue, hsafeStoreY, hvalidOld⟩
        have hvalueEq : safeValue = oldValue := by
          have hslotEq :=
            Option.some.inj (hsafeStoreY.symm.trans hstoreY)
          exact congrArg StoreSlot.value hslotEq
        subst hvalueEq
        have henvY' : env'.slotAt y = some otherEnvSlot := by
          rw [henv']
          simpa [Env.update, hyx] using henvY
        exact
          RuntimeFrame.validPartialValueWhenInitialized_envWrite_var_of_no_write
            henvX hwriteEnv hnotWrite
            (by
              intro mutable target hcontains
              exact ⟨y, otherEnvSlot, henvY', hcontains⟩)
            hvalidOld)
      (by
        intro location hreach
        exact
          RuntimeFrame.reachesWhenInitialized_var_ne_of_envWrite_var_not_writeProhibited
            hsafe hheap henvX hwriteEnv hnotWrite hvalueHeap
            (holder := x)
            (by
              intro mutable target hcontains
              exact ⟨{ envSlot with ty := .ty rhsTy }, henvX', hcontains⟩)
            hreach)
      (by
        intro y otherEnvSlot oldValue hyx henvY hstoreY location hreach
        have henvY' : env'.slotAt y = some otherEnvSlot := by
          rw [henv']
          simpa [Env.update, hyx] using henvY
        have holdHeap : PartialValueOwnerTargetsHeap oldValue :=
          partialValueOwnerTargetsHeap_of_slot hheap hstoreY
        exact
          RuntimeFrame.reachesWhenInitialized_var_ne_of_envWrite_var_not_writeProhibited
            hsafe hheap henvX hwriteEnv hnotWrite holdHeap
            (holder := y)
            (by
              intro mutable target hcontains
              exact ⟨otherEnvSlot, henvY', hcontains⟩)
            hreach)

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

/-- `WellFormedEnv` plus the post-write check is too weak for strict assignment
preservation when the source environment is not borrow-safe.  These premises
allow the environment write from `move z : &mut *q` into `*p`, where
`p : &mut q` and `q : &mut r`, and the resulting environment is not strictly
contained-borrow well formed.  This is a borrow-safety counterexample, not a
reason to reject ordinary borrow-authorized writes such as `*p = 1`. -/
theorem strict_assign_rule_result_counterexample :
    ∃ env₁ env₂ env₃ typing lifetime lhs rhs oldTy targetLifetime rhsTy,
      WellFormedEnv env₁ lifetime ∧
        SourceTerm (.assign lhs rhs) ∧
        TermTyping env₁ typing lifetime rhs rhsTy env₂ ∧
        LValTyping env₂ lhs oldTy targetLifetime ∧
        ShapeCompatible env₂ oldTy (.ty rhsTy) ∧
        WellFormedTy env₂ rhsTy targetLifetime ∧
        EnvWrite env₂ lhs rhsTy env₃ ∧
        ¬ WriteProhibited env₃ lhs ∧
        ¬ ContainedBorrowsWellFormed env₃ := by
  exact ⟨envWithZ, movedZ, resultMoved, StoreTyping.empty, l, .deref p,
    .move z, .ty (.borrow true r), l, rhsTy,
    envWithZ_wellFormed, source_assign_move_z, rhs_move_typing,
    moved_lhs_typing, moved_shape, moved_rhs_wellFormed, write_moved,
    resultMoved_not_writeProhibited, resultMoved_not_containedBorrowsWellFormed⟩

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

/-- Spine-mirroring shape relation: the two partial types share their
partial-box spine, and the cores are full (or undef-vs-full) with
shape-compatible types.  This is what the strong update actually produces,
and unlike bare `ShapeCompatible` it inverts deterministically. -/
inductive MirrorShape (env : Env) : PartialTy → PartialTy → Prop where
  | boxes {inner inner' : PartialTy} :
      MirrorShape env inner inner' →
      MirrorShape env (.box inner) (.box inner')
  | full {T T' : Ty} :
      ShapeCompatible env (.ty T) (.ty T') →
      MirrorShape env (.ty T) (.ty T')
  | undefFull {T T' : Ty} :
      ShapeCompatible env (.undef T) (.ty T') →
      MirrorShape env (.undef T) (.ty T')

theorem MirrorShape.of_compat_full_right {env : Env} {pt : PartialTy}
    {T' : Ty} :
    ShapeCompatible env pt (.ty T') →
    MirrorShape env pt (.ty T') := by
  intro hcompat
  cases pt with
  | ty T => exact .full hcompat
  | undef T => exact .undefFull hcompat
  | box inner =>
      cases hcompat

theorem MirrorShape.full_inv {env : Env} {T : Ty} {pt' : PartialTy} :
    MirrorShape env (.ty T) pt' →
    ∃ T', pt' = .ty T' ∧ ShapeCompatible env (.ty T) (.ty T') := by
  intro hmirror
  cases hmirror with
  | full hcompat => exact ⟨_, rfl, hcompat⟩

theorem MirrorShape.boxes_inv {env : Env} {inner : PartialTy}
    {pt' : PartialTy} :
    MirrorShape env (.box inner) pt' →
    ∃ inner', pt' = .box inner' ∧ MirrorShape env inner inner' := by
  intro hmirror
  cases hmirror with
  | boxes hinner => exact ⟨_, rfl, hinner⟩

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
        MirrorShape env bslot.ty graftTy ∧
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
              MirrorShape env bslot.ty graftTy ∧
              ChainGuard env (LVal.base lhs) b)) ∨
        (result = env ∧
          (∀ {mutable : Bool} {u : LVal},
            PartialTyContains updated (.borrow mutable u) →
            PartialTyContains (.ty ty) (.borrow mutable u)) ∧
          MirrorShape env old updated))
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
            MirrorShape env bslot.ty graftTy ∧
            ChainGuard env (LVal.base lhs) b)
    (by
      -- strong: the graft happens here; the environment part is untouched.
      intro _old _ty wcur pt lf lfc hwcur hlhs _hcontainsW _hguard hshapePt
      have hdet := LValTyping.deterministic hwcur
        (by simpa [prependPath] using hlhs)
      exact Or.inr ⟨rfl, fun hcontains => hcontains,
        MirrorShape.of_compat_full_right (hdet.1 ▸ hshapePt)⟩)
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
        ⟨hupdEq, hprops⟩ | ⟨henvEq, hgraft, hshapeInner⟩
      · exact Or.inl ⟨by rw [hupdEq], hprops⟩
      · refine Or.inr ⟨henvEq, ?_, MirrorShape.boxes hshapeInner⟩
        intro mutable u hcontains
        cases hcontains with
        | box hinner' => exact hgraft hinner'
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
        ⟨hupdEq, hprops⟩ | ⟨henvEq, hgraft, hshapeInner⟩
      · exact Or.inl ⟨by rw [hupdEq, partialTyRebox], hprops⟩
      · rcases MirrorShape.full_inv hshapeInner with ⟨T₁, hT₁, hcompat⟩
        subst hT₁
        exact Or.inr ⟨henvEq,
          fun hcontains =>
            hgraft (PartialTyContains.partialTyRebox_borrow_inv hcontains),
          by
            rw [partialTyRebox]
            exact MirrorShape.full (ShapeCompatible.tyBox hcompat)⟩)
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
        ⟨hupdEq, hprops⟩ | ⟨henvEq, hgraft, hshapeGraft⟩
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

/-- Borrows in the grafted type never target into the write chain: at the
chain root they would write-prohibit the assigned lval through the grafted
slot, and at deeper links they conflict with the chain's own mutable
annotation, contradicting the written type's borrow safety. -/
theorem graft_target_outside {env env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u)) :
    ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      ¬ ChainGuard env (LVal.base lhs) (LVal.base u) := by
  intro mutable u hcontains hguard
  generalize hroot : LVal.base u = y at hguard
  cases hguard with
  | base =>
      exact hnotWrite
        (WriteProhibited.of_contains_conflict
          ⟨{ bslot with ty := graftTy }, hbLook, hcontains⟩ hroot)
  | step hz hcontZ hbaseG =>
      exact htySafe.2 _ _ mutable u hcontZ (hgraftContains hcontains)
        (hbaseG.trans hroot.symm)

noncomputable def chainRaisedRank (φ : Name → Nat) (env : Env)
    (root : Name) (bound : Nat) : Name → Nat := by
  classical
  exact fun y => if ChainGuard env root y then bound + φ y else φ y

/-- Raising every variable on the guarded write chain preserves linearization
after replacing the final graft slot.

The follow-up paper's assignment invariant gives the modified chain variables
fresh high ranks.  Existing chain edges still descend because every chain rank
is shifted by the same bound; old outside-to-chain edges are excluded by
borrow-safety plus the result `¬ WriteProhibited` premise, and graft edges back
into the chain are excluded by `TyBorrowSafeAgainstEnv`. -/
theorem LinearizedBy.raise_chain_update {φ : Name → Nat} {env env₃ : Env}
    {lhs : LVal} {rhsTy : Ty} {b : Name} {bslot : EnvSlot}
    {graftTy : PartialTy} {bound : Nat}
    (hφ : LinearizedBy φ env)
    (hsafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b)
    (hboundEnv : ∀ y slot v,
      env.slotAt y = some slot →
      v ∈ PartialTy.vars slot.ty →
      φ v < bound)
    (hboundGraft : ∀ v,
      v ∈ PartialTy.vars graftTy →
      φ v < bound) :
    LinearizedBy (chainRaisedRank φ env (LVal.base lhs) bound) env₃ := by
  classical
  have hunchanged : ∀ x, ¬ ChainGuard env (LVal.base lhs) x →
      env₃.slotAt x = env.slotAt x := by
    intro x hxOut
    exact hne x (fun h => hxOut (h ▸ hguardB))
  intro y resultSlot v hresult hv
  by_cases hyb : y = b
  · subst y
    have hslotEq : resultSlot = { bslot with ty := graftTy } :=
      Option.some.inj (hresult.symm.trans hbLook)
    subst hslotEq
    by_cases hvGuard : ChainGuard env (LVal.base lhs) v
    · rcases partialTy_vars_mem_contains (pt := graftTy) v hv with
        ⟨mutable, target, hcontains, hbase⟩
      exact False.elim
        ((graft_target_outside htySafe hnotWrite hbLook hgraftContains
          hcontains) (by simpa [hbase] using hvGuard))
    · have hvLt : φ v < bound := hboundGraft v hv
      have hle : bound ≤ bound + φ b := Nat.le_add_right _ _
      simpa [chainRaisedRank, hguardB, hvGuard] using
        Nat.lt_of_lt_of_le hvLt hle
  · have hsource : env.slotAt y = some resultSlot := by
      simpa [hne y hyb] using hresult
    by_cases hyGuard : ChainGuard env (LVal.base lhs) y
    · by_cases hvGuard : ChainGuard env (LVal.base lhs) v
      · have hold : φ v < φ y := hφ y resultSlot v hsource hv
        simpa [chainRaisedRank, hyGuard, hvGuard] using
          Nat.add_lt_add_left hold bound
      · have hvLt : φ v < bound := hboundEnv y resultSlot v hsource hv
        have hle : bound ≤ bound + φ y := Nat.le_add_right _ _
        simpa [chainRaisedRank, hyGuard, hvGuard] using
          Nat.lt_of_lt_of_le hvLt hle
    · by_cases hvGuard : ChainGuard env (LVal.base lhs) v
      · rcases partialTy_vars_mem_contains (pt := resultSlot.ty) v hv with
          ⟨mutable, target, hcontains, hbase⟩
        have hentry : env ⊢ y ↝ (.borrow mutable target) :=
          ⟨resultSlot, hsource, hcontains⟩
        exact False.elim
          (chainGuard_contains_exclusion hsafe hunchanged hnotWrite
            hvGuard hyGuard hentry hbase)
      · have hold : φ v < φ y := hφ y resultSlot v hsource hv
        simpa [chainRaisedRank, hyGuard, hvGuard] using hold

theorem EnvWrite.preserves_linearizable {env env₃ : Env}
    {lhs : LVal} {rhsTy : Ty} {oldTy : PartialTy}
    {targetLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    Env.FiniteSupport env →
    EnvWrite env lhs rhsTy env₃ →
    LValTyping env lhs oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    ¬ WriteProhibited env₃ lhs →
    Linearizable env →
    Linearizable env₃ := by
  intro hcbwf hsafe htySafe hfinite hwrite hlv hshape hnotWrite hlinear
  rcases hlinear with ⟨φ, hφ⟩
  rcases EnvWrite.chain_guarded hcbwf hwrite hlv hshape with
    hpointwise | ⟨b, bslot, graftTy, hb, hne, hbLook, _hlifetime,
      hgraftContains, _hmirror, hguardB⟩
  · refine ⟨φ, ?_⟩
    intro x slot v hslot hv
    have hsource : env.slotAt x = some slot := by
      simpa [hpointwise x] using hslot
    exact hφ x slot v hsource hv
  · rcases hfinite with ⟨support, hsupport⟩
    let bound := writeRankBound φ env rhsTy support.toList
    have hboundEnv : ∀ y slot v,
        env.slotAt y = some slot →
        v ∈ PartialTy.vars slot.ty →
        φ v < bound := by
      intro y slot v hslot hv
      exact rank_lt_writeRankBound_of_slot
        (φ := φ) (env := env) (rhsTy := rhsTy)
        (support := support.toList)
        (by exact Finset.mem_toList.mpr (hsupport y slot hslot))
        hslot hv
    have hboundGraft : ∀ v,
        v ∈ PartialTy.vars graftTy →
        φ v < bound := by
      intro v hv
      rcases partialTy_vars_mem_contains (pt := graftTy) v hv with
        ⟨mutable, target, hcontains, hbase⟩
      have htargetMem :
          LVal.base target ∈ PartialTy.vars (.ty rhsTy) :=
        PartialTyContains.borrow_target_mem_vars
          (hgraftContains hcontains)
      have hvRhs : v ∈ Ty.vars rhsTy := by
        simpa [PartialTy.vars, hbase] using htargetMem
      exact rank_lt_writeRankBound_of_rhs
        (φ := φ) (env := env) (rhsTy := rhsTy)
        (support := support.toList) hvRhs
    exact ⟨_, LinearizedBy.raise_chain_update hφ hsafe htySafe hnotWrite
      hne hbLook hgraftContains hguardB hboundEnv hboundGraft⟩

/-- Post-write typing existence: every source typing either survives the
write verbatim, or re-types through the graft at a spine-mirrored type all of
whose borrows point outside the chain and are source-typed. -/
theorem LValTyping.exists_env3 {env env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    (hcbwf : ContainedBorrowsWellFormed env)
    (hsafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hrhsTyped : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains (.ty rhsTy) (.borrow mutable u) →
      ∃ T lf, LValTyping env u (.ty T) lf)
    (hb : env.slotAt b = some bslot)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hmirror : MirrorShape env bslot.ty graftTy)
    (hguardB : ChainGuard env (LVal.base lhs) b) :
    ∀ {t : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping env t pt lf →
      LValTyping env₃ t pt lf ∨
        ∃ pt' lf', LValTyping env₃ t pt' lf' ∧ MirrorShape env pt pt' ∧
          (∀ {mutable : Bool} {u : LVal},
            PartialTyContains pt' (.borrow mutable u) →
            ¬ ChainGuard env (LVal.base lhs) (LVal.base u) ∧
              ∃ T lf'', LValTyping env u (.ty T) lf'') := by
  have hunchanged : ∀ x, ¬ ChainGuard env (LVal.base lhs) x →
      env₃.slotAt x = env.slotAt x := by
    intro x hxOut
    exact hne x (fun h => hxOut (h ▸ hguardB))
  intro t pt lf htyping
  induction htyping with
  | var hslot =>
      rename_i y s
      by_cases hy : y = b
      · subst hy
        have hsEq : s = bslot := Option.some.inj (hslot.symm.trans hb)
        subst hsEq
        refine Or.inr ⟨graftTy, _, .var hbLook, hmirror, ?_⟩
        intro mutable u hcontains
        exact ⟨graft_target_outside htySafe hnotWrite hbLook
            hgraftContains hcontains,
          hrhsTyped (hgraftContains hcontains)⟩
      · exact Or.inl (.var ((hne y hy) ▸ hslot))
  | box _ ih =>
      rcases ih with hleft | ⟨pt', lf', hty', hmirror', houts⟩
      · exact Or.inl (.box hleft)
      · rcases MirrorShape.boxes_inv hmirror' with ⟨inner', hEq, hmirrorInner⟩
        subst hEq
        refine Or.inr ⟨inner', lf', .box hty', hmirrorInner, ?_⟩
        intro mutable u hcontains
        exact houts (PartialTyContains.box hcontains)
  | boxFull _ ih =>
      rcases ih with hleft | ⟨pt', lf', hty', hmirror', houts⟩
      · exact Or.inl (.boxFull hleft)
      · rcases MirrorShape.full_inv hmirror' with ⟨T'', hEq, hcompat⟩
        subst hEq
        cases hcompat with
        | tyBox hcompatInner =>
            refine Or.inr ⟨_, lf', .boxFull hty',
              MirrorShape.full hcompatInner, ?_⟩
            intro mutable u hcontains
            exact houts (PartialTyContains.tyBox hcontains)
  | borrow hw hu ihBorrow ihTarget =>
      rename_i w u m blf tlf targetTy
      rcases ihBorrow with hleftW | ⟨pt'w, blf', hty'w, hmirrorW, houtsW⟩
      · rcases ihTarget with hleftU | ⟨pt'u, lf'u, hty'u, hmirrorU, houtsU⟩
        · exact Or.inl (.borrow hleftW hleftU)
        · rcases MirrorShape.full_inv hmirrorU with ⟨T'u, hEq, hcompatU⟩
          subst hEq
          exact Or.inr ⟨_, lf'u, .borrow hleftW hty'u,
            MirrorShape.full hcompatU, houtsU⟩
      · rcases MirrorShape.full_inv hmirrorW with ⟨Tw', hEqW, hcompatW⟩
        subst hEqW
        cases hcompatW with
        | borrow hlu hru' hcompatTT =>
            rename_i u' leftTy rightTy
            rcases hlu with ⟨llf, hluTyping⟩
            have hdetU := LValTyping.deterministic hu hluTyping
            rcases houtsW PartialTyContains.here with
              ⟨hu'Outside, T₃, lf₃, hu'Env⟩
            rcases hru' with ⟨rlf, hru'Typing⟩
            rcases LValTyping.transport_of_outside_chain hsafe hunchanged
                hnotWrite hru'Typing hu'Outside with
              ⟨hty₃, houts₂⟩
            refine Or.inr ⟨.ty rightTy, rlf, .borrow hty'w hty₃,
              MirrorShape.full ?_, ?_⟩
            · have hTyEq : PartialTy.ty targetTy = .ty leftTy := hdetU.1
              rw [show targetTy = leftTy from by
                injection hTyEq]
              exact hcompatTT
            · intro mutable₂ u₂ hcontains₂
              rcases houts₂ hcontains₂ with ⟨z, hzOutside, hzContains⟩
              have hu₂Outside :
                  ¬ ChainGuard env (LVal.base lhs) (LVal.base u₂) := by
                intro hguard₂
                exact chainGuard_contains_exclusion hsafe hunchanged
                  hnotWrite hguard₂ hzOutside hzContains rfl
              rcases hzContains with ⟨zslot, hzslot, hzContainsTy⟩
              rcases hcbwf z zslot mutable₂ u₂ hzslot
                  ⟨zslot, hzslot, hzContainsTy⟩ with
                ⟨T₄, lf₄, hty₄, _hle₄, _hbase₄⟩
              exact ⟨hu₂Outside, T₄, lf₄, hty₄⟩

theorem LValTyping.transport_of_pointwise {env env₃ : Env}
    (heq : ∀ y, env₃.slotAt y = env.slotAt y) :
    ∀ {t : LVal} {pt : PartialTy} {lf : Lifetime},
      LValTyping env t pt lf →
      LValTyping env₃ t pt lf := by
  intro t pt lf htyping
  induction htyping with
  | var hslot => exact .var ((heq _) ▸ hslot)
  | box _ ih => exact .box ih
  | boxFull _ ih => exact .boxFull ih
  | borrow _ _ ihBorrow ihTarget => exact .borrow ihBorrow ihTarget

/-- **Definition 4.8(i) across T-Assign, strict.**  The borrow invariant is
preserved by the strong-update write from exactly the rule premises plus the
threaded borrow-safety facts (whose necessity the counterexamples above
establish). -/
theorem ContainedBorrowsWellFormed.envWrite {env : Env}
    (hcbwf : ContainedBorrowsWellFormed env)
    (hsafe : BorrowSafeEnv env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlv : LValTyping env lhs oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWrite : ¬ WriteProhibited env₃ lhs) :
    ContainedBorrowsWellFormed env₃ := by
  have hrhsTyped : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains (.ty rhsTy) (.borrow mutable u) →
      ∃ T lf, LValTyping env u (.ty T) lf := by
    intro mutable u hcontains
    rcases borrowTargetsWellFormed_of_wellFormedTy_contains hwellTy hcontains
      with ⟨T, lf, hty, _, _⟩
    exact ⟨T, lf, hty⟩
  rcases EnvWrite.chain_guarded hcbwf hwrite hlv hshape with
    hpointwise | ⟨b, bslot, graftTy, hb, hne, hbLook, _hbound,
      hgraftContains, hmirror, hguardB⟩
  · -- Nothing changed: the invariant transports pointwise.
    intro x slot₃ mutable t hslot₃ hcontains₃
    rcases hcontains₃ with ⟨cslot, hcslot, hcontainsTy⟩
    have hcslotEnv : env.slotAt x = some cslot := (hpointwise x) ▸ hcslot
    rcases hcbwf x cslot mutable t hcslotEnv
        ⟨cslot, hcslotEnv, hcontainsTy⟩ with
      ⟨T, lf, hty, hle, hbase⟩
    have hslotEq : slot₃ = cslot :=
      Option.some.inj (hslot₃.symm.trans hcslot)
    subst hslotEq
    refine ⟨T, lf, LValTyping.transport_of_pointwise hpointwise hty, hle, ?_⟩
    rcases hbase with ⟨bs, hbs, hbsle⟩
    exact ⟨bs, (hpointwise _) ▸ hbs, hbsle⟩
  · intro x slot₃ mutable t hslot₃ hcontains₃
    rcases hcontains₃ with ⟨cslot, hcslot, hcontainsTy⟩
    have hslotEq : cslot = slot₃ :=
      Option.some.inj (hcslot.symm.trans hslot₃)
    subst hslotEq
    -- The target is source-typed: from the source invariant off the graft,
    -- from the written type's well-formedness on it.
    have hsource : ∃ T lf, LValTyping env t (.ty T) lf := by
      by_cases hx : x = b
      · subst hx
        have hcslotEq : cslot = { bslot with ty := graftTy } :=
          Option.some.inj (hcslot.symm.trans hbLook)
        rw [hcslotEq] at hcontainsTy
        exact hrhsTyped (hgraftContains hcontainsTy)
      · have hcslotEnv : env.slotAt x = some cslot := (hne x hx) ▸ hcslot
        rcases hcbwf x cslot mutable t hcslotEnv
            ⟨cslot, hcslotEnv, hcontainsTy⟩ with
          ⟨T, lf, hty, _, _⟩
        exact ⟨T, lf, hty⟩
    -- Existence in the result, then the strict write bounds.
    rcases hsource with ⟨T, lf, hty⟩
    have hexists : ∃ T' lf', LValTyping env₃ t (.ty T') lf' := by
      rcases LValTyping.exists_env3 hcbwf hsafe htySafe hnotWrite
          hrhsTyped hb hne hbLook hgraftContains hmirror hguardB hty with
        hleft | ⟨pt', lf', hty', hmirror', _houts⟩
      · exact ⟨T, lf, hleft⟩
      · rcases MirrorShape.full_inv hmirror' with ⟨T', hEq, _⟩
        subst hEq
        exact ⟨T', lf', hty'⟩
    rcases hexists with ⟨T', lf', hty₃⟩
    have hbase₃ : LValBaseOutlives env₃ t cslot.lifetime :=
      envWrite_contains_baseOutlives_strict hcbwf hwrite hlv hwellTy
        hcslot hcontainsTy
    have hbound₃ :=
      (envWrite_typing_bound_strict hcbwf hwrite hlv hwellTy hty₃).1
        cslot.lifetime hbase₃
    
    exact ⟨T', lf', hty₃, hbound₃, hbase₃⟩

/-- Definition 4.13 across T-Assign: borrow safety is preserved because the
written slot's new borrows come from the written type, whose conflicts with
environment borrows are exactly what `TyBorrowSafeAgainstEnv` forbids. -/
theorem BorrowSafeEnv.envWrite {env : Env}
    (hcbwf : ContainedBorrowsWellFormed env)
    (hsafe : BorrowSafeEnv env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlv : LValTyping env lhs oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy)) :
    BorrowSafeEnv env₃ := by
  rcases EnvWrite.chain_guarded hcbwf hwrite hlv hshape with
    hpointwise | ⟨b, bslot, graftTy, hb, hne, hbLook, _hbound,
      hgraftContains, _hmirror, _hguardB⟩
  · intro x y mutable targetMutable targetOther hx hy hconf
    refine hsafe x y mutable targetMutable targetOther ?_ ?_ hconf
    · rcases hx with ⟨s, hs, hcontains⟩
      exact ⟨s, (hpointwise x) ▸ hs, hcontains⟩
    · rcases hy with ⟨s, hs, hcontains⟩
      exact ⟨s, (hpointwise y) ▸ hs, hcontains⟩
  · have hclassify : ∀ {z : Name} {mutable : Bool} {u : LVal},
        env₃ ⊢ z ↝ (.borrow mutable u) →
        (z ≠ b ∧ env ⊢ z ↝ (.borrow mutable u)) ∨
          (z = b ∧ PartialTyContains (.ty rhsTy) (.borrow mutable u)) := by
      intro z mutable u hz
      rcases hz with ⟨s, hs, hcontains⟩
      by_cases hzb : z = b
      · subst hzb
        have hsEq : s = { bslot with ty := graftTy } :=
          Option.some.inj (hs.symm.trans hbLook)
        subst hsEq
        exact Or.inr ⟨rfl, hgraftContains hcontains⟩
      · exact Or.inl ⟨hzb, ⟨s, (hne z hzb) ▸ hs, hcontains⟩⟩
    intro x y mutable targetMutable targetOther hx hy hconf
    rcases hclassify hx with ⟨hxb, hxEnv⟩ | ⟨hxb, hxRhs⟩
    · rcases hclassify hy with ⟨hyb, hyEnv⟩ | ⟨hyb, hyRhs⟩
      · exact hsafe x y mutable targetMutable targetOther hxEnv hyEnv hconf
      · exact absurd hconf
          (fun h => htySafe.2 x targetMutable mutable targetOther hxEnv
            hyRhs h)
    · rcases hclassify hy with ⟨hyb, hyEnv⟩ | ⟨hyb, hyRhs⟩
      · exact absurd hconf
          (fun h => htySafe.1 targetMutable mutable targetOther y hxRhs
            hyEnv h)
      · exact hxb.trans hyb.symm

/-- Initialized target typings transport forward across a strict write.  If the
write changes a graft slot, `LValTyping.exists_env3` either preserves the old
typing exactly or produces a full mirrored typing, which is enough for
`TargetInitialized`. -/
theorem TargetInitialized.envWrite {env env₃ : Env} {lhs target : LVal}
    {rhsTy : Ty} {oldTy : PartialTy} {targetLifetime : Lifetime}
    (hcbwf : ContainedBorrowsWellFormed env)
    (hsafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlv : LValTyping env lhs oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWrite : ¬ WriteProhibited env₃ lhs) :
    TargetInitialized env target →
    TargetInitialized env₃ target := by
  intro hinitialized
  rcases hinitialized with ⟨targetTy, targetLifetime', htyping⟩
  have hrhsTyped : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains (.ty rhsTy) (.borrow mutable u) →
      ∃ T lf, LValTyping env u (.ty T) lf := by
    intro mutable u hcontains
    rcases borrowTargetsWellFormed_of_wellFormedTy_contains hwellTy hcontains
      with ⟨T, lf, hty, _hle, _hbase⟩
    exact ⟨T, lf, hty⟩
  rcases EnvWrite.chain_guarded hcbwf hwrite hlv hshape with
    hpointwise | ⟨b, bslot, graftTy, hb, hne, hbLook, _hbound,
      hgraftContains, hmirror, hguardB⟩
  · exact ⟨targetTy, targetLifetime',
      LValTyping.transport_of_pointwise hpointwise htyping⟩
  · rcases LValTyping.exists_env3 hcbwf hsafe htySafe hnotWrite
        hrhsTyped hb hne hbLook hgraftContains hmirror hguardB htyping with
      htyping₃ | ⟨pt', lf', htyping₃, hmirror', _houts⟩
    · exact ⟨targetTy, targetLifetime', htyping₃⟩
    · rcases MirrorShape.full_inv hmirror' with ⟨targetTy', hEq, _hcompat⟩
      subst hEq
      exact ⟨targetTy', lf', htyping₃⟩

/-- Initialized value validity transports across a strict write when every
borrow annotation in the value's type has a holder in the result environment.
Live borrows use `TargetInitialized.envWrite`; stale borrows stay stale because
any result holder for the same annotation comes either from the RHS type (which
is strictly well formed in the source environment) or from an old source slot
(which is covered by `ContainedBorrowsWellFormed`). -/
theorem validPartialValueWhenInitialized_envWrite_of_result_contains
    {env env₃ : Env} {store : ProgramStore} {lhs : LVal}
    {rhsTy : Ty} {oldTy partialTy : PartialTy}
    {targetLifetime : Lifetime} {value : PartialValue}
    (hcbwf : ContainedBorrowsWellFormed env)
    (hsafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlv : LValTyping env lhs oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hcontainsResult : ∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      ∃ holder, env₃ ⊢ holder ↝ (.borrow mutable target)) :
    ValidPartialValueWhenInitialized env store value partialTy →
    ValidPartialValueWhenInitialized env₃ store value partialTy := by
  intro hvalid
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
      exact ValidPartialValueWhenInitialized.borrowLive
        (TargetInitialized.envWrite hcbwf hsafe htySafe hwrite hlv hshape
          hwellTy hnotWrite hinitialized)
        hloc
  | @borrowStale location mutable target hstale =>
      refine ValidPartialValueWhenInitialized.borrowStale ?_
      intro _htarget₃
      rcases hcontainsResult PartialTyContains.here with
        ⟨holder, hcontains₃⟩
      rcases EnvWrite.contains_borrow_source hwrite hcontains₃ with
        hcontainsRhs | hcontainsSource
      · rcases borrowTargetsWellFormed_of_wellFormedTy_contains
            hwellTy hcontainsRhs with
          ⟨sourceTy, sourceLifetime, hsourceTyping, _hle, _hbase⟩
        exact hstale ⟨sourceTy, sourceLifetime, hsourceTyping⟩
      · rcases hcontainsSource with ⟨slot, hslot, hcontainsTy⟩
        rcases hcbwf holder slot mutable target hslot
            ⟨slot, hslot, hcontainsTy⟩ with
          ⟨sourceTy, sourceLifetime, hsourceTyping, _hle, _hbase⟩
        exact hstale ⟨sourceTy, sourceLifetime, hsourceTyping⟩
  | box hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.box hslot
        (ih (by
          intro mutable target hcontains
          exact hcontainsResult (PartialTyContains.box hcontains)))
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.boxFull hslot
        (ih (by
          intro mutable target hcontains
          exact hcontainsResult (PartialTyContains.tyBox hcontains)))

/-- **Definition 4.8 across T-Assign, strict.** -/
theorem WellFormedEnv.envWrite {env : Env} {current : Lifetime}
    (hwell : WellFormedEnv env current)
    (hsafe : BorrowSafeEnv env)
    {env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwrite : EnvWrite env lhs rhsTy env₃)
    (hlv : LValTyping env lhs oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWrite : ¬ WriteProhibited env₃ lhs) :
    WellFormedEnv env₃ current :=
  ⟨ContainedBorrowsWellFormed.envWrite hwell.1 hsafe htySafe hwrite hlv
      hshape hwellTy hnotWrite,
    EnvSlotsOutlive.write hwrite hwell.2⟩

/-- The struck remainder of a move never contains a borrow: the spine above
the removed subtree is pure boxes, and the subtree itself became `undef`. -/
theorem Strike.struck_borrow_free :
    ∀ {path : Path} {source struck : PartialTy} {mutable : Bool}
      {target : LVal},
      Strike path source struck →
      ¬ PartialTyContains struck (.borrow mutable target) := by
  intro path
  induction path with
  | nil =>
      intro source struck mutable target hstrike hcontains
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains
  | cons head tail ih =>
      intro source struck mutable target hstrike hcontains
      cases source with
      | ty tySource =>
          cases tySource <;> cases struck <;> simp [Strike] at hstrike
          cases hcontains with
          | box hinner => exact ih hstrike hinner
      | box inner =>
          cases struck <;> simp [Strike] at hstrike
          cases hcontains with
          | box hinner => exact ih hstrike hinner
      | undef shape =>
          cases struck <;> simp [Strike] at hstrike

/-- A strike through a typed lvalue factors into the prefix selecting the
lvalue and the remaining suffix over the lvalue's own type. -/
theorem LValTyping.strike_suffix {env : Env} :
    ∀ {lv : LVal} {pt : PartialTy} {lf : Lifetime}
      {slot : EnvSlot} {suffix : Path} {struck : PartialTy},
      LValTyping env lv pt lf →
      env.slotAt (LVal.base lv) = some slot →
      Strike (LVal.path lv ++ suffix) slot.ty struck →
      ∃ localStruck, Strike suffix pt localStruck := by
  intro lv pt lf slot suffix struck htyping
  induction htyping generalizing slot suffix struck with
  | var hslot =>
      intro hbase hstrike
      have hslotEq : slot = _ := Option.some.inj (hbase.symm.trans hslot)
      subst hslotEq
      exact ⟨struck, by simpa [LVal.path] using hstrike⟩
  | box _ ih =>
      intro hbase hstrike
      rcases ih (by simpa only [LVal.base] using hbase)
          (by
            simpa only [LVal.path, List.append_assoc] using hstrike) with
        ⟨sourceStruck, hsourceStruck⟩
      cases sourceStruck with
      | ty tyStruck => simp [Strike] at hsourceStruck
      | box localStruck =>
          simp [Strike] at hsourceStruck
          exact ⟨localStruck, hsourceStruck⟩
      | undef tyStruck => simp [Strike] at hsourceStruck
  | boxFull _ ih =>
      intro hbase hstrike
      rcases ih (by simpa only [LVal.base] using hbase)
          (by
            simpa only [LVal.path, List.append_assoc] using hstrike) with
        ⟨sourceStruck, hsourceStruck⟩
      cases sourceStruck with
      | ty tyStruck => simp [Strike] at hsourceStruck
      | box localStruck =>
          simp [Strike] at hsourceStruck
          exact ⟨localStruck, hsourceStruck⟩
      | undef tyStruck => simp [Strike] at hsourceStruck
  | borrow _ _ ihBorrow _ihTarget =>
      intro hbase hstrike
      rcases ihBorrow (by simpa only [LVal.base] using hbase)
          (by
            simpa only [LVal.path, List.append_assoc] using hstrike) with
        ⟨sourceStruck, hsourceStruck⟩
      cases sourceStruck <;> simp [Strike] at hsourceStruck

/-- A movable lval's type is contained in its base slot: the strike premise
forces a hop-free descent. -/
theorem strike_typing_contains {env : Env} :
    ∀ {path : Path} {source struck : PartialTy},
      Strike path source struck →
      ∀ {wcur : LVal} {lfc : Lifetime} {ty : Ty} {vlf : Lifetime}
        {mutable : Bool} {target : LVal},
        LValTyping env wcur source lfc →
        LValTyping env (prependPath path wcur) (.ty ty) vlf →
        PartialTyContains (.ty ty) (.borrow mutable target) →
        PartialTyContains source (.borrow mutable target) := by
  intro path
  induction path with
  | nil =>
      intro source struck hstrike wcur lfc ty vlf mutable target hwcur hlhs
        hcontains
      have hdet := LValTyping.deterministic hwcur
        (by simpa [prependPath] using hlhs)
      rw [hdet.1]
      exact hcontains
  | cons head tail ih =>
      intro source struck hstrike wcur lfc ty vlf mutable target hwcur hlhs
        hcontains
      cases source with
      | ty tySource =>
          cases tySource <;> cases struck <;> simp [Strike] at hstrike
          exact PartialTyContains.tyBox
            (ih hstrike (LValTyping.boxFull hwcur)
              (by rw [prependPath_deref_comm]; exact hlhs) hcontains)
      | box inner =>
          cases struck <;> simp [Strike] at hstrike
          exact PartialTyContains.box
            (ih hstrike (LValTyping.box hwcur)
              (by rw [prependPath_deref_comm]; exact hlhs) hcontains)
      | undef shape =>
          cases struck <;> simp [Strike] at hstrike

/-- The moved-out type is borrow-safe against the post-move environment: its
unique annotation lived in the struck slot, so it no longer conflicts with
any surviving loan. -/
theorem tyBorrowSafeAgainstEnv_move {env moved : Env} {lv : LVal} {ty : Ty}
    {valueLifetime : Lifetime}
    (hsafe : BorrowSafeEnv env)
    (hLv : LValTyping env lv (.ty ty) valueLifetime)
    (hmove : EnvMove env lv moved) :
    TyBorrowSafeAgainstEnv moved ty := by
  rcases hmove with ⟨slot, struck, hslot, hstrike, hmoved⟩
  have hbaseContains : ∀ {mutable : Bool} {target : LVal},
      PartialTyContains (.ty ty) (.borrow mutable target) →
      env ⊢ (LVal.base lv) ↝ (.borrow mutable target) := by
    intro mutable target hcontains
    exact ⟨slot, hslot,
      strike_typing_contains hstrike (LValTyping.var hslot)
        (by rw [prependPath_path_base]; exact hLv) hcontains⟩
  have hmovedBaseFree : ∀ {mutable : Bool} {target : LVal},
      ¬ moved ⊢ (LVal.base lv) ↝ (.borrow mutable target) := by
    intro mutable target hcontains
    rcases hcontains with ⟨s, hs, hcontainsTy⟩
    rw [hmoved] at hs
    have hsEq : s = { slot with ty := struck } :=
      (Option.some.inj (by simpa [Env.update] using hs)).symm
    subst hsEq
    exact Strike.struck_borrow_free hstrike hcontainsTy
  have hmovedToEnv : ∀ {z : Name} {mutable : Bool} {target : LVal},
      moved ⊢ z ↝ (.borrow mutable target) →
      env ⊢ z ↝ (.borrow mutable target) := by
    intro z mutable target hcontains
    rcases hcontains with ⟨s, hs, hcontainsTy⟩
    exact EnvMove.contains_borrow_source ⟨slot, struck, hslot, hstrike, hmoved⟩
      hs ⟨s, hs, hcontainsTy⟩
  constructor
  · intro targetMutable mutable targetOther x hcontains hother hconflict
    have hzx := hsafe (LVal.base lv) x mutable targetMutable targetOther
      (hbaseContains hcontains) (hmovedToEnv hother) hconflict
    exact hmovedBaseFree (hzx ▸ hother)
  · intro x targetMutable mutable targetOther hcontainsMutable hcontains
      hconflict
    have hzx := hsafe x (LVal.base lv) mutable targetMutable targetOther
      (hmovedToEnv hcontainsMutable) (hbaseContains hcontains)
      (by exact hconflict)
    exact hmovedBaseFree (hzx ▸ hcontainsMutable)

/-- A copied type is borrow-safe against the environment: copyable types
contain at most an immutable borrow, whose unique environment occurrence
cannot conflict with a mutable loan by borrow safety and unarity. -/
theorem tyBorrowSafeAgainstEnv_copy {env : Env} {lv : LVal} {ty : Ty}
    {valueLifetime : Lifetime}
    (hsafe : BorrowSafeEnv env)
    (hLv : LValTyping env lv (.ty ty) valueLifetime)
    (hcopy : CopyTy ty) :
    TyBorrowSafeAgainstEnv env ty := by
  cases hcopy with
  | unit => exact tyBorrowSafeAgainstEnv_borrowFree (by
      intro mutable target hcontains
      cases hcontains)
  | int => exact tyBorrowSafeAgainstEnv_borrowFree (by
      intro mutable target hcontains
      cases hcontains)
  | immBorrow =>
      rename_i target
      constructor
      · intro targetMutable mutable targetOther x hcontains _hother _hconflict
        cases hcontains
      · intro x targetMutable mutable targetOther hcontainsMutable hcontains
          hconflict
        cases hcontains with
        | here =>
            rcases LValTyping.contains_borrow hLv PartialTyContains.here with
              ⟨z, hz⟩
            have hxz := hsafe x z false targetMutable target
              hcontainsMutable hz hconflict
            subst hxz
            rcases hcontainsMutable with ⟨sx, hsx, hcontainsX⟩
            rcases hz with ⟨sz, hsz, hcontainsZ⟩
            have hsEq : sx = sz := Option.some.inj (hsx.symm.trans hsz)
            subst hsEq
            rcases PartialTyContains.borrow_unique hcontainsX hcontainsZ with
              ⟨hm, _⟩
            cases hm

/-- **The strict invariant walk.**  Source-term typing preserves the paper's
Definition 4.8 and Definition 4.13 invariants and yields a result type that
is well formed and borrow-safe against the result environment — with no rule
obligations beyond the paper premises. -/
theorem typingPreservesWellFormed_of_sourceTerm
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    SourceTerm term →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ BorrowSafeEnv env₂ ∧
      WellFormedTy env₂ ty lifetime ∧ TyBorrowSafeAgainstEnv env₂ ty := by
  intro hsource hwellFormed hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env _typing lifetime term ty env₂ _ =>
      SourceTerm term →
      WellFormedEnv env lifetime →
      BorrowSafeEnv env →
      WellFormedEnv env₂ lifetime ∧ BorrowSafeEnv env₂ ∧
        WellFormedTy env₂ ty lifetime ∧ TyBorrowSafeAgainstEnv env₂ ty)
    (motive_2 := fun env _typing blockLifetime terms ty env₂ _ =>
      SourceTerm (.block blockLifetime terms) →
      WellFormedEnv env blockLifetime →
      BorrowSafeEnv env →
      WellFormedEnv env₂ blockLifetime ∧ BorrowSafeEnv env₂ ∧
        WellFormedTy env₂ ty blockLifetime ∧
        TyBorrowSafeAgainstEnv env₂ ty)
    (by
      -- T-Const: source values are unit or int.
      intro _env _typing _lifetime value ty hvalue hsource hwell hsafe
      have hsourceValue : SourceValue value :=
        hsource value (by simp [termValues])
      cases hvalue with
      | unit =>
          exact ⟨hwell, hsafe, .unit,
            tyBorrowSafeAgainstEnv_borrowFree
              (fun mutable target hcontains => by cases hcontains)⟩
      | int =>
          exact ⟨hwell, hsafe, .int,
            tyBorrowSafeAgainstEnv_borrowFree
              (fun mutable target hcontains => by cases hcontains)⟩
      | ref hlookup =>
          exact absurd hsourceValue (by simp [SourceValue]))
    (by
      -- T-Copy.
      intro _env _typing _lifetime _valueLifetime lv ty hLv hcopy _hnotRead
        _hsource hwell hsafe
      exact ⟨hwell, hsafe, LValTyping.wellFormedTy hwell hLv,
        tyBorrowSafeAgainstEnv_copy hsafe hLv hcopy⟩)
    (by
      -- T-Move.
      intro _env₁ _env₂ _typing _lifetime _valueLifetime lv ty hLv hnotWrite
        hmove _hsource hwell hsafe
      refine ⟨WellFormedEnv.move hwell hmove hnotWrite,
        BorrowSafeEnv.move hsafe hmove, ?_,
        tyBorrowSafeAgainstEnv_move hsafe hLv hmove⟩
      refine WellFormedTy.move hwell.1 hmove hnotWrite ?_
        (LValTyping.wellFormedTy hwell hLv)
      intro mutable target hcontains
      exact LValTyping.contains_borrow hLv hcontains)
    (by
      -- T-MutBorrow.
      intro _env _typing _lifetime _valueLifetime lv ty hLv _hmutable
        hnotWrite _hsource hwell hsafe
      rcases LValTyping.base_slot_exists hLv with ⟨slot, hslot⟩
      exact ⟨hwell, hsafe,
        .borrow ⟨ty, _, hLv, LValTyping.lifetime_outlives_one hwell.2 hLv,
          slot, hslot, hwell.2 _ slot hslot⟩,
        tyBorrowSafeAgainstEnv_mutBorrow hnotWrite⟩)
    (by
      -- T-ImmBorrow.
      intro _env _typing _lifetime _valueLifetime lv ty hLv hnotRead
        _hsource hwell hsafe
      rcases LValTyping.base_slot_exists hLv with ⟨slot, hslot⟩
      exact ⟨hwell, hsafe,
        .borrow ⟨ty, _, hLv, LValTyping.lifetime_outlives_one hwell.2 hLv,
          slot, hslot, hwell.2 _ slot hslot⟩,
        tyBorrowSafeAgainstEnv_immBorrow hnotRead⟩)
    (by
      -- T-Box.
      intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih hsource hwell
        hsafe
      rcases ih (SourceTerm.box_inner hsource) hwell hsafe with
        ⟨hwell₂, hsafe₂, hwellTy, htySafe⟩
      exact ⟨hwell₂, hsafe₂, .box hwellTy, TyBorrowSafeAgainstEnv.box htySafe⟩)
    (by
      -- T-Block.
      intro _env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty
        hchild _hterms hwellTy hdrop ih hsource hwell hsafe
      rcases ih hsource
          (WellFormedEnv.weaken hwell (LifetimeChild.outlives hchild))
          hsafe with
        ⟨hwellBody, hsafeBody, _hwellTyBody, htySafeBody⟩
      rcases block_preserves_wellFormed hchild hwellBody hwellTy hdrop with
        ⟨hwellOut, hwellTyOut⟩
      refine ⟨hwellOut, ?_, hwellTyOut, ?_⟩
      · rw [hdrop]
        exact borrowSafeEnv_dropLifetime hsafeBody
      · rw [hdrop]
        exact TyBorrowSafeAgainstEnv.dropLifetime htySafeBody)
    (by
      -- T-Declare.
      intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty _hfresh _hterm
        hfreshOut henv₃ ih hsource hwell hsafe
      rcases ih (SourceTerm.declare_inner hsource) hwell hsafe with
        ⟨hwell₂, hsafe₂, hwellTy₂, htySafe₂⟩
      refine ⟨?_, ?_, .unit,
        tyBorrowSafeAgainstEnv_borrowFree
          (fun mutable target hcontains => by cases hcontains)⟩
      · rw [henv₃]
        exact WellFormedEnv.update_fresh_ty hwell₂ hwellTy₂ hfreshOut
      · rw [henv₃]
        exact borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv hsafe₂ htySafe₂)
    (by
      -- T-Assign: the write kernel.
      intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy
        _rhs _rhsTy hRhs hLhsPost hshape hwellTy hwrite hnotWrite ih
        hsource hwell hsafe
      rcases ih (SourceTerm.assign_inner hsource) hwell hsafe with
        ⟨hwell₂, hsafe₂, _hwellTyRhs, htySafe₂⟩
      exact ⟨WellFormedEnv.envWrite hwell₂ hsafe₂ htySafe₂ hwrite hLhsPost
          hshape hwellTy hnotWrite,
        BorrowSafeEnv.envWrite hwell₂.1 hsafe₂ htySafe₂ hwrite hLhsPost
          hshape,
        .unit,
        tyBorrowSafeAgainstEnv_borrowFree
          (fun mutable target hcontains => by cases hcontains)⟩)
    (by
      -- T-Seq singleton.
      intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih hsource hwell
        hsafe
      exact ih (SourceTerm.block_head hsource) hwell hsafe)
    (by
      -- T-Seq cons.
      intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
        _hterm _hrest ihHead ihRest hsource hwell hsafe
      rcases ihHead (SourceTerm.block_head hsource) hwell hsafe with
        ⟨hwell₂, hsafe₂, _, _⟩
      exact ihRest (SourceTerm.block_tail hsource) hwell₂ hsafe₂)
    htyping hsource hwellFormed hsafe

/-- Source-term typing preserves the follow-up paper's linearization invariant.

The theorem is finite-context, matching the paper's context `κ`.  The assignment
case delegates to `EnvWrite.preserves_linearizable`, whose rank map raises the
whole guarded write chain above every non-chain variable mentioned by the finite
environment and the RHS type. -/
theorem typingPreservesLinearizable_of_sourceTerm
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    SourceTerm term →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    Env.FiniteSupport env₁ →
    Linearizable env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    Linearizable env₂ := by
  intro hsource hwellFormed hsafe hfinite hlinear htyping
  exact TermTyping.rec
    (motive_1 := fun env _typing lifetime term _ty env₂ _ =>
      SourceTerm term →
      WellFormedEnv env lifetime →
      BorrowSafeEnv env →
      Env.FiniteSupport env →
      Linearizable env →
      Linearizable env₂)
    (motive_2 := fun env _typing blockLifetime terms _ty env₂ _ =>
      SourceTerm (.block blockLifetime terms) →
      WellFormedEnv env blockLifetime →
      BorrowSafeEnv env →
      Env.FiniteSupport env →
      Linearizable env →
      Linearizable env₂)
    (by
      intro _env _typing _lifetime _value _ty _hvalue _hsource _hwell _hsafe
        _hfinite hlinear
      exact hlinear)
    (by
      intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hcopy
        _hnotRead _hsource _hwell _hsafe _hfinite hlinear
      exact hlinear)
    (by
      intro _env₁ _env₂ _typing _lifetime _valueLifetime lv _ty _hLv
        _hnotWrite hmove _hsource _hwell _hsafe _hfinite hlinear
      rcases hlinear with ⟨φ, hφ⟩
      exact ⟨φ, LinearizedBy.move hφ hmove⟩)
    (by
      intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hmutable
        _hnotWrite _hsource _hwell _hsafe _hfinite hlinear
      exact hlinear)
    (by
      intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hnotRead
        _hsource _hwell _hsafe _hfinite hlinear
      exact hlinear)
    (by
      intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih hsource hwell
        hsafe hfinite hlinear
      exact ih (SourceTerm.box_inner hsource) hwell hsafe hfinite hlinear)
    (by
      intro _env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty
        hchild _hterms _hwellTy hdrop ih hsource hwell hsafe hfinite hlinear
      have hbodyLinear : Linearizable _env₂ :=
        ih hsource
          (WellFormedEnv.weaken hwell (LifetimeChild.outlives hchild))
          hsafe hfinite hlinear
      rcases hbodyLinear with ⟨φ, hφ⟩
      rw [hdrop]
      exact ⟨φ, LinearizedBy.dropLifetime hφ⟩)
    (by
      intro _env₁ _env₂ _env₃ _typing _lifetime x _term _ty _hfresh hterm
        hfreshOut henv₃ ih hsource hwell hsafe hfinite hlinear
      have hlinear₂ : Linearizable _env₂ :=
        ih (SourceTerm.declare_inner hsource) hwell hsafe hfinite hlinear
      have hwellInner :=
        typingPreservesWellFormed_of_sourceTerm
          (SourceTerm.declare_inner hsource) hwell hsafe hterm
      rcases hwellInner with ⟨hwell₂, _hsafe₂, hwellTy₂, _htySafe₂⟩
      rcases hlinear₂ with ⟨φ, hφ⟩
      have hnotInSource : ∀ y sourceSlot,
          _env₂.slotAt y = some sourceSlot →
          x ∉ PartialTy.vars sourceSlot.ty := by
        intro y sourceSlot hslot hmem
        rcases containedBorrows_slot_vars_in_env hwell₂.1 hslot x hmem with
          ⟨slot, hslotX⟩
        rw [hfreshOut] at hslotX
        cases hslotX
      have hnotInSlot :
          x ∉ PartialTy.vars (PartialTy.ty _ty) := by
        intro hmem
        rcases wellFormedTy_vars_in_env hwellTy₂ x
            (by simpa [PartialTy.vars] using hmem) with
          ⟨slot, hslotX⟩
        rw [hfreshOut] at hslotX
        cases hslotX
      rw [henv₃]
      exact ⟨_, LinearizedBy.update_fresh_above hφ hfreshOut hnotInSource
        hnotInSlot⟩)
    (by
      intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime lhs oldTy
        _rhs rhsTy hRhs hLhsPost hshape _hwellTy hwrite hnotWrite ih
        hsource hwell hsafe hfinite hlinear
      have hlinear₂ : Linearizable _env₂ :=
        ih (SourceTerm.assign_inner hsource) hwell hsafe hfinite hlinear
      have hwellInner :=
        typingPreservesWellFormed_of_sourceTerm
          (SourceTerm.assign_inner hsource) hwell hsafe hRhs
      rcases hwellInner with ⟨hwell₂, hsafe₂, _hwellTyRhs, htySafe₂⟩
      have hfinite₂ : Env.FiniteSupport _env₂ :=
        TermTyping.finiteSupport hRhs hfinite
      exact EnvWrite.preserves_linearizable hwell₂.1 hsafe₂ htySafe₂
        hfinite₂ hwrite hLhsPost hshape hnotWrite hlinear₂)
    (by
      intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih hsource hwell
        hsafe hfinite hlinear
      exact ih (SourceTerm.block_head hsource) hwell hsafe hfinite hlinear)
    (by
      intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
        hterm _hrest ihHead ihRest hsource hwell hsafe hfinite hlinear
      have hlinear₂ : Linearizable _env₂ :=
        ihHead (SourceTerm.block_head hsource) hwell hsafe hfinite hlinear
      have hwellHead :=
        typingPreservesWellFormed_of_sourceTerm
          (SourceTerm.block_head hsource) hwell hsafe hterm
      have hfinite₂ : Env.FiniteSupport _env₂ :=
        TermTyping.finiteSupport hterm hfinite
      exact ihRest (SourceTerm.block_tail hsource)
        hwellHead.1 hwellHead.2.1 hfinite₂ hlinear₂)
    htyping hsource hwellFormed hsafe hfinite hlinear

/-- The static invariant package threaded by source typing and used by
preservation: Definition 4.8 well-formedness, Definition 4.13 borrow safety,
finite context support, and the follow-up paper's linearization/rank
invariant. -/
def StaticInvariantPackage (env : Env) (lifetime : Lifetime) : Prop :=
  WellFormedEnv env lifetime ∧ BorrowSafeEnv env ∧
    Env.FiniteSupport env ∧ Linearizable env

theorem StaticInvariantPackage.empty (lifetime : Lifetime) :
    StaticInvariantPackage Env.empty lifetime := by
  exact ⟨wellFormedEnv_empty lifetime, borrowSafeEnv_empty,
    Env.finiteSupport_empty, Linearizable.empty⟩

/-- Source typing preserves the whole static invariant package. -/
theorem StaticInvariantPackage.preserve_of_sourceTerm
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    SourceTerm term →
    StaticInvariantPackage env₁ lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    StaticInvariantPackage env₂ lifetime ∧
      WellFormedTy env₂ ty lifetime ∧
      TyBorrowSafeAgainstEnv env₂ ty := by
  intro hsource hinv htyping
  rcases hinv with ⟨hwell, hsafe, hfinite, hlinear⟩
  rcases typingPreservesWellFormed_of_sourceTerm hsource hwell hsafe htyping with
    ⟨hwell₂, hsafe₂, hwellTy₂, htySafe₂⟩
  have hfinite₂ : Env.FiniteSupport env₂ :=
    TermTyping.finiteSupport htyping hfinite
  have hlinear₂ : Linearizable env₂ :=
    typingPreservesLinearizable_of_sourceTerm hsource hwell hsafe hfinite
      hlinear htyping
  exact ⟨⟨hwell₂, hsafe₂, hfinite₂, hlinear₂⟩, hwellTy₂, htySafe₂⟩

theorem safeAbstractionWhenInitialized_dropLifetime_of_preserved
    {store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    (∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot) →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ lifetime →
      ∃ value,
        store'.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } ∧
        ValidPartialValueWhenInitialized (env.dropLifetime lifetime) store'
          value envSlot.ty) →
    SafeAbstraction store' (env.dropLifetime lifetime) := by
  intro hdomain hpreserve
  constructor
  · exact hdomain
  · intro x envSlot henvDropped
    rcases (Env.dropLifetime_slotAt_eq_some.mp henvDropped) with
      ⟨henv, hlifetime⟩
    exact hpreserve x envSlot henv hlifetime

theorem dropPreservation_lifetime_whenInitialized
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    SafeAbstraction store env →
    DropsLifetime store lifetime store' →
    (∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot) →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      envSlot.lifetime ≠ lifetime →
      ∃ value,
        store'.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } ∧
        ValidPartialValueWhenInitialized (env.dropLifetime lifetime) store'
          value envSlot.ty) →
    SafeAbstraction store' (env.dropLifetime lifetime) := by
  intro _hsafe _hdrops hdomain hpreserve
  exact safeAbstractionWhenInitialized_dropLifetime_of_preserved
    hdomain hpreserve

theorem dropLifetime_envDomain_of_storeSurvivor_whenInitialized
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime}
    {x : Name} :
    SafeAbstraction store env →
    DropsLifetime store lifetime store' →
    (∀ slot,
      store'.slotAt (VariableProjection x) = some slot →
      slot.lifetime ≠ lifetime) →
    (∃ slot, store'.slotAt (VariableProjection x) = some slot) →
    ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot := by
  intro hsafe hdrops hnotDropped hstoreDomain
  rcases hstoreDomain with ⟨slot, hslot'⟩
  have hslot : store.slotAt (VariableProjection x) = some slot :=
    dropsLifetime_slotAt_of_slotAt hdrops hslot'
  rcases (hsafe.1 x).mp ⟨slot, hslot⟩ with ⟨envSlot, henv⟩
  have henvLifetime : envSlot.lifetime = slot.lifetime := by
    rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
    rw [hslot] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact (congrArg StoreSlot.lifetime hslotEq).symm
  exact ⟨envSlot, Env.dropLifetime_slotAt_eq_some.mpr
    ⟨henv, by
      intro hdrop
      exact hnotDropped slot hslot' (by simpa [henvLifetime] using hdrop)⟩⟩

theorem dropLifetime_storeDomain_of_envSurvivor_of_ownerTargetsHeap_whenInitialized
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime}
    {x : Name} :
    SafeAbstraction store env →
    DropsLifetime store lifetime store' →
    StoreOwnerTargetsHeap store →
    (∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot) →
    ∃ slot, store'.slotAt (VariableProjection x) = some slot := by
  intro hsafe hdrops hheap henvDomain
  rcases henvDomain with ⟨envSlot, henvDropped⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp henvDropped with
    ⟨henv, hlifetime⟩
  rcases (hsafe.1 x).mpr ⟨envSlot, henv⟩ with ⟨slot, hslot⟩
  have hslotLifetime : slot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henv with ⟨value, hsafeSlot, _hvalid⟩
    rw [hslot] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact congrArg StoreSlot.lifetime hslotEq
  exact ⟨slot, dropsLifetime_preserves_var_slot_of_not_lifetime hdrops hheap
    hslot (by simpa [hslotLifetime] using hlifetime)⟩

theorem dropLifetime_domain_equiv_of_ownerTargetsHeap_whenInitialized
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    SafeAbstraction store env →
    DropsLifetime store lifetime store' →
    StoreOwnerTargetsHeap store →
    ∀ x,
      (∃ slot, store'.slotAt (VariableProjection x) = some slot) ↔
        ∃ envSlot, (env.dropLifetime lifetime).slotAt x = some envSlot := by
  intro hsafe hdrops hheap x
  constructor
  · exact dropLifetime_envDomain_of_storeSurvivor_whenInitialized
      hsafe hdrops (by
        intro slot hslot
        exact dropsLifetime_slot_not_dropped hdrops hslot)
  · exact dropLifetime_storeDomain_of_envSurvivor_of_ownerTargetsHeap_whenInitialized
      hsafe hdrops hheap

/--
Lifetime drops avoid every location protected by a variable whose abstract slot
outlives the parent lifetime.  The root variable is not in the lifetime drop
set because its slot lifetime cannot be the child lifetime; owner descendants
are not in the drop set by the heap-root lifetime disjointness condition.
-/
theorem dropsAvoids_of_protectedByBase_lifetime_whenInitialized
    {store store' : ProgramStore} {env : Env}
    {parent child : Lifetime} {dropSet : List PartialValue}
    {root : Name} {location : Location} :
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location slot,
        store.slotAt location = some slot ∧
        slot.lifetime = child ∧
        value = .value (.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeDropOwnersDisjoint store child →
    LifetimeChild parent child →
    (∃ rootSlot, env.slotAt root = some rootSlot ∧
      rootSlot.lifetime ≤ parent) →
    RuntimeFrame.ProtectedByBase store root location →
    DropsAvoids store dropSet location := by
  intro hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint hchild
    hrootLifetime hprotected
  rcases hrootLifetime with ⟨rootEnvSlot, hrootEnvSlot, hrootLe⟩
  rcases hsafe.2 root rootEnvSlot hrootEnvSlot with
    ⟨rootValue, hrootStoreSlot, _hrootValid⟩
  have hrootAvoid : DropsAvoids store dropSet (VariableProjection root) :=
    dropsAvoids_var_of_not_owning_var hdrops hheap (by
      intro dropValue hmem hownsRoot
      rcases (hdropSet dropValue).mp hmem with
        ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
      have hrootEq : (VariableProjection root : Location) = dropLocation :=
        eq_location_of_mem_lifetime_drop_value hdropValue hownsRoot
      subst hrootEq
      have hdropSlotLifetime : dropSlot.lifetime = rootEnvSlot.lifetime := by
        have hslotEq :
            dropSlot =
              { value := rootValue, lifetime := rootEnvSlot.lifetime } :=
          Option.some.inj (hdropSlot.symm.trans hrootStoreSlot)
        exact congrArg StoreSlot.lifetime hslotEq
      have hdropLe : dropSlot.lifetime ≤ parent := by
        simpa [hdropSlotLifetime] using hrootLe
      exact LifetimeChild.not_child_outlives_parent hchild
        (by simpa [hdropLifetime] using hdropLe))
  have hdisjointOwner :
      ∀ {owned storage : Location},
        ProgramStore.OwnsAt store owned storage →
        ∀ value, value ∈ dropSet →
          owned ∉ partialValueOwningLocations value := by
    intro owned storage howns value hmem howned
    rcases (hdropSet value).mp hmem with
      ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
    have hownedEq : owned = dropLocation :=
      eq_location_of_mem_lifetime_drop_value hdropValue howned
    subst hownedEq
    exact hdropDisjoint owned dropSlot hdropSlot hdropLifetime
      ⟨storage, howns⟩
  have hpathAvoid :
      ∀ {storage owned : Location},
        ProgramStore.OwnsTransitively store storage owned →
        DropsAvoids store dropSet storage →
        DropsAvoids store dropSet owned := by
    intro storage owned hpath
    induction hpath with
    | direct howns =>
        intro havoidStorage
        exact dropsAvoids_of_protected_owner hdrops hvalidStore howns
          havoidStorage (hdisjointOwner howns)
    | trans hfirst _htail ih =>
        intro havoidStorage
        have havoidMiddle : DropsAvoids store dropSet _ :=
          dropsAvoids_of_protected_owner hdrops hvalidStore hfirst
            havoidStorage (hdisjointOwner hfirst)
        exact ih havoidMiddle
  cases hprotected with
  | inl hroot =>
      simpa [hroot] using hrootAvoid
  | inr hpath =>
      exact hpathAvoid hpath hrootAvoid

/-- A location selected by an initialized lvalue whose base outlives the parent
lifetime is not erased by dropping the child block lifetime. -/
theorem lval_loc_dropsAvoids_lifetime_whenInitialized
    {store store' : ProgramStore} {env : Env}
    {parent child : Lifetime} {dropSet : List PartialValue} :
    ContainedBorrowsWellFormedWhenInitialized env →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location slot,
        store.slotAt location = some slot ∧
        slot.lifetime = child ∧
        value = .value (.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeDropOwnersDisjoint store child →
    LifetimeChild parent child →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env lv partialTy lifetime →
      LValBaseOutlives env lv parent →
      store.loc lv = some location →
      DropsAvoids store dropSet location := by
  intro hcbwf hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint hchild
  have hdropNoOwned :
      ∀ {owned storage : Location},
        ProgramStore.OwnsAt store owned storage →
        ∀ value, value ∈ dropSet →
          owned ∉ partialValueOwningLocations value := by
    intro owned storage howns value hmem howned
    rcases (hdropSet value).mp hmem with
      ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
    have hownedEq : owned = dropLocation :=
      eq_location_of_mem_lifetime_drop_value hdropValue howned
    subst hownedEq
    exact hdropDisjoint owned dropSlot hdropSlot hdropLifetime
      ⟨storage, howns⟩
  intro lv partialTy lifetime location htyping
  induction htyping generalizing location with
  | @var x slot hslot =>
      intro hbase hloc
      have hlocation : location = VariableProjection x := by
        simpa [ProgramStore.loc, VariableProjection] using hloc.symm
      subst hlocation
      exact dropsAvoids_of_protectedByBase_lifetime_whenInitialized
        hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint hchild
        hbase RuntimeFrame.ProtectedByBase.root
  | box hsource ih =>
      intro hbase hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store _ (.box _) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
          hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
          have hlocEq : location = ownedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          have havoidSource :
              DropsAvoids store dropSet sourceLocation :=
            ih hbase hsourceLoc
          have hownsAt :
              ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have havoidOwned :
              DropsAvoids store dropSet ownedLocation :=
            dropsAvoids_of_protected_owner hdrops hvalidStore hownsAt
              havoidSource (hdropNoOwned hownsAt)
          simpa [hlocEq] using havoidOwned
  | boxFull hsource ih =>
      intro hbase hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store _
            (.ty (.box _)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
          hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @boxFull ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
          have hlocEq : location = ownedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          have havoidSource :
              DropsAvoids store dropSet sourceLocation :=
            ih hbase hsourceLoc
          have hownsAt :
              ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have havoidOwned :
              DropsAvoids store dropSet ownedLocation :=
            dropsAvoids_of_protected_owner hdrops hvalidStore hownsAt
              havoidSource (hdropNoOwned hownsAt)
          simpa [hlocEq] using havoidOwned
  | borrow hsource htarget ihSource ihTarget =>
      rename_i source target mutable borrowLifetime targetLifetime targetTy
      intro hbase hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store _
            (.ty (.borrow _ _)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
          hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrowLive borrowedLocation _mutable _target _hinitialized htargetLoc =>
          have hlocEq : location = borrowedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          have hsourceLifetimeLe :
              _ ≤ parent :=
            LValTyping.lifetime_le_of_base_outlives_whenInitialized
              hcbwf hsource hbase
          have htargetBase : LValBaseOutlives env target parent := by
            have htargetWF :=
              LValTyping.partialTyBorrowsWellFormedInSlotWhenInitialized
                hcbwf hsource PartialTyContains.here
            rcases htargetWF.1 with ⟨targetBaseSlot, htargetBaseSlot,
              htargetLe⟩
            exact ⟨targetBaseSlot, htargetBaseSlot,
              LifetimeOutlives.trans htargetLe hsourceLifetimeLe⟩
          have havoidTarget :
              DropsAvoids store dropSet borrowedLocation :=
            ihTarget htargetBase (by simpa using htargetLoc)
          simpa [hlocEq] using havoidTarget
      | @borrowStale borrowedLocation mutable target hstale =>
          exact False.elim (hstale ⟨_, _, htarget⟩)

/-- Every runtime location read while resolving such an lvalue also survives
the child lifetime drop. -/
theorem locReads_dropsAvoids_lifetime_whenInitialized
    {store store' : ProgramStore} {env : Env}
    {parent child : Lifetime} {dropSet : List PartialValue} :
    ContainedBorrowsWellFormedWhenInitialized env →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location slot,
        store.slotAt location = some slot ∧
        slot.lifetime = child ∧
        value = .value (.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeDropOwnersDisjoint store child →
    LifetimeChild parent child →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env lv partialTy lifetime →
      LValBaseOutlives env lv parent →
      RuntimeFrame.LocReads store lv location →
      DropsAvoids store dropSet location := by
  intro hcbwf hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint hchild
    lv partialTy lifetime location htyping
  induction htyping with
  | var hslot =>
      intro _hbase hreads
      cases hreads
  | box hsource ih =>
      intro hbase hreads
      cases hreads with
      | here hloc =>
          exact lval_loc_dropsAvoids_lifetime_whenInitialized hcbwf hsafe
            hvalidStore hheap hdropSet hdrops hdropDisjoint hchild
            hsource hbase hloc
      | there hsourceReads =>
          exact ih hbase hsourceReads
  | boxFull hsource ih =>
      intro hbase hreads
      cases hreads with
      | here hloc =>
          exact lval_loc_dropsAvoids_lifetime_whenInitialized hcbwf hsafe
            hvalidStore hheap hdropSet hdrops hdropDisjoint hchild
            hsource hbase hloc
      | there hsourceReads =>
          exact ih hbase hsourceReads
  | borrow hsource htarget ihSource ihTarget =>
      intro hbase hreads
      cases hreads with
      | here hloc =>
          exact lval_loc_dropsAvoids_lifetime_whenInitialized hcbwf hsafe
            hvalidStore hheap hdropSet hdrops hdropDisjoint hchild
            hsource hbase hloc
      | there hsourceReads =>
          exact ihSource hbase hsourceReads

/-- Borrow dependencies of a value in an outer-live slot survive a child
lifetime drop. -/
theorem borrowDependencyWhenInitialized_dropsAvoids_lifetime
    {store store' : ProgramStore} {env : Env}
    {parent child slotLifetime : Lifetime} {dropSet : List PartialValue}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    ContainedBorrowsWellFormedWhenInitialized env →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location slot,
        store.slotAt location = some slot ∧
        slot.lifetime = child ∧
        value = .value (.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeDropOwnersDisjoint store child →
    LifetimeChild parent child →
    slotLifetime ≤ parent →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy
      dependency →
    DropsAvoids store dropSet dependency := by
  intro hcbwf hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint hchild
    hslotParent hborrows hdependency
  induction hdependency generalizing slotLifetime with
  | @borrow location dependency mutable target hinitialized _hloc hreads =>
      rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
      have htargetWF := hborrows PartialTyContains.here
      have htargetBase : LValBaseOutlives env target parent := by
        rcases htargetWF.1 with ⟨targetBaseSlot, htargetBaseSlot,
          htargetBaseLe⟩
        exact ⟨targetBaseSlot, htargetBaseSlot,
          LifetimeOutlives.trans htargetBaseLe hslotParent⟩
      exact locReads_dropsAvoids_lifetime_whenInitialized hcbwf hsafe
        hvalidStore hheap hdropSet hdrops hdropDisjoint hchild
        htargetTyping htargetBase hreads
  | boxInner _hslot _hinner ih =>
      exact ih hslotParent (by
        intro mutable target hcontains
        exact hborrows (PartialTyContains.box hcontains))
  | boxFullInner _hslot _hinner ih =>
      exact ih hslotParent (by
        intro mutable target hcontains
        exact hborrows (PartialTyContains.tyBox hcontains))

/-! ### Owner-chain acyclicity and the strike/write alignment

The runtime counterpart of `Strike`: a move through boxes updates the leaf of
an owner-reference chain, while the static environment strikes the box spine
of the base slot's type.  Under store validity the chain cannot revisit its
leaf, so every spine slot other than the leaf survives the write unchanged. -/

/-- Owner-edge chains between locations, measured by length. -/
inductive OwnsChain (store : ProgramStore) : Location → Nat → Location → Prop
    where
  | zero {location : Location} : OwnsChain store location 0 location
  | succ {root mid next : Location} {n : Nat} :
      OwnsChain store root n mid →
      ProgramStore.OwnsAt store next mid →
      OwnsChain store root (n + 1) next

/-- Owner chains compose. -/
theorem ownsChain_append {store : ProgramStore} {root mid : Location}
    {n : Nat} (hfirst : OwnsChain store root n mid) :
    ∀ {m : Nat} {target : Location},
      OwnsChain store mid m target →
      OwnsChain store root (n + m) target := by
  intro m
  induction m with
  | zero =>
      intro target hsecond
      cases hsecond
      exact hfirst
  | succ m ih =>
      intro target hsecond
      cases hsecond with
      | succ hchain howns =>
          exact OwnsChain.succ (ih hchain) howns

/-- Under owner uniqueness, chains from an unowned root to a fixed location
have a unique length: backward steps are deterministic. -/
theorem ownsChain_unique_length {store : ProgramStore} {root : Location}
    (hvalidStore : ValidStore store)
    (hrootUnowned : ¬ ProgramStore.Owns store root) :
    ∀ {n₁ n₂ : Nat} {target : Location},
      OwnsChain store root n₁ target →
      OwnsChain store root n₂ target →
      n₁ = n₂ := by
  intro n₁
  induction n₁ with
  | zero =>
      intro n₂ target h₁ h₂
      cases h₁
      cases h₂ with
      | zero => rfl
      | succ _ howns => exact absurd ⟨_, howns⟩ hrootUnowned
  | succ n ih =>
      intro n₂ target h₁ h₂
      cases h₁ with
      | succ hchain₁ howns₁ =>
          cases h₂ with
          | zero => exact absurd ⟨_, howns₁⟩ hrootUnowned
          | succ hchain₂ howns₂ =>
              have hmid := hvalidStore _ _ _ howns₁ howns₂
              subst hmid
              rw [ih hchain₁ hchain₂]

/-- Variable locations are never owned when owner targets live on the heap. -/
theorem var_not_owned {store : ProgramStore} {x : Name}
    (hheap : StoreOwnerTargetsHeap store) :
    ¬ ProgramStore.Owns store (.var x) := by
  intro howns
  rcases hheap _ howns with ⟨address, haddr⟩
  cases haddr

/-- The runtime owner chain below a value, following a strike path to the
written leaf. -/
inductive OwnerChainAt (store : ProgramStore) :
    PartialValue → Path → Location → Prop where
  | here {location : Location} :
      OwnerChainAt store
        (.value (.ref { location := location, owner := true }))
        [()] location
  | there {location leaf : Location} {slot : StoreSlot} {rest : Path} :
      store.slotAt location = some slot →
      OwnerChainAt store slot.value (() :: rest) leaf →
      OwnerChainAt store
        (.value (.ref { location := location, owner := true }))
        (() :: () :: rest) leaf

theorem OwnerChainAt.extend {store : ProgramStore}
    {value : PartialValue} {path : Path} {location next : Location}
    {slot : StoreSlot} :
    OwnerChainAt store value path location →
    store.slotAt location = some slot →
    slot.value = .value (.ref { location := next, owner := true }) →
    OwnerChainAt store value (path ++ [()]) next := by
  intro hchain hslot hvalue
  induction hchain with
  | here =>
      have htail : OwnerChainAt store slot.value [()] next := by
        rw [hvalue]
        exact OwnerChainAt.here
      simpa using OwnerChainAt.there hslot htail
  | there hslotHead _htail ih =>
      simpa [List.cons_append] using
        OwnerChainAt.there hslotHead (ih hslot)

theorem ownsChain_extend {store : ProgramStore} {root location next : Location}
    {n : Nat} {slot : StoreSlot} :
    OwnsChain store root n location →
    store.slotAt location = some slot →
    slot.value = .value (.ref { location := next, owner := true }) →
    OwnsChain store root (n + 1) next := by
  intro hchain hslot hvalue
  exact OwnsChain.succ hchain
    ⟨slot.lifetime, by
      cases slot with
      | mk slotValue slotLifetime =>
          simp at hvalue
          subst hvalue
          simpa [owningRef] using hslot⟩

def OwnerChainPrefix (store : ProgramStore) (root : Location)
    (rootValue : PartialValue) (path : Path) (leaf : Location) : Prop :=
  (path = [] ∧ leaf = root) ∨
    ∃ k,
      OwnerChainAt store rootValue path leaf ∧
      OwnsChain store root k leaf ∧
      k = path.length

theorem OwnerChainPrefix.ownsChain_length {store : ProgramStore}
    {root leaf : Location} {rootValue : PartialValue} {path : Path} :
    OwnerChainPrefix store root rootValue path leaf →
    ∃ k, OwnsChain store root k leaf ∧ k = path.length := by
  intro hprefix
  rcases hprefix with ⟨hpath, hleaf⟩ | ⟨k, _hchainAt, hchain, hlen⟩
  · subst hpath
    subst hleaf
    exact ⟨0, OwnsChain.zero, rfl⟩
  · exact ⟨k, hchain, hlen⟩

theorem OwnerChainPrefix.prepend_owner {store : ProgramStore}
    {root next leaf : Location} {rootSlot nextSlot : StoreSlot}
    {path : Path} :
    store.slotAt root = some rootSlot →
    rootSlot.value = .value (.ref { location := next, owner := true }) →
    store.slotAt next = some nextSlot →
    OwnerChainPrefix store next nextSlot.value path leaf →
    ∃ k,
      OwnerChainAt store rootSlot.value (() :: path) leaf ∧
      OwnsChain store root k leaf ∧
      k = (() :: path).length := by
  intro hrootSlot hrootOwner hnextSlot hprefix
  have hfirst : OwnsChain store root 1 next := by
    simpa using ownsChain_extend
      (OwnsChain.zero (store := store) (location := root))
      hrootSlot hrootOwner
  rcases hprefix with ⟨hpath, hleaf⟩ | ⟨k, hchain, howns, hlen⟩
  · subst hpath
    subst hleaf
    refine ⟨1, ?_, hfirst, by simp⟩
    rw [hrootOwner]
    exact OwnerChainAt.here
  · refine ⟨1 + k, ?_, ?_, ?_⟩
    · rw [hrootOwner]
      cases nextSlot with
      | mk nextValue nextLifetime =>
          cases hchain with
          | here =>
              exact OwnerChainAt.there hnextSlot OwnerChainAt.here
          | there hslot htail =>
              exact OwnerChainAt.there hnextSlot
                (OwnerChainAt.there hslot htail)
    · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        ownsChain_append hfirst howns
    · rw [hlen]
      exact Nat.add_comm 1 path.length

inductive PathSelect : Path → PartialTy → PartialTy → Prop where
  | here {ty : PartialTy} :
      PathSelect [] ty ty
  | box {path : Path} {inner leaf : PartialTy} :
      PathSelect path inner leaf →
      PathSelect (() :: path) (.box inner) leaf
  | boxFull {path : Path} {inner : Ty} {leaf : PartialTy} :
      PathSelect path (.ty inner) leaf →
      PathSelect (() :: path) (.ty (.box inner)) leaf

theorem PathSelect.contains_of_leaf :
    ∀ {path : Path} {root leafTy : PartialTy} {needle : Ty},
      PathSelect path root leafTy →
      PartialTyContains leafTy needle →
      PartialTyContains root needle := by
  intro path root leafTy needle hselect
  induction hselect with
  | here =>
      intro hcontains
      exact hcontains
  | box _hinner ih =>
      intro hcontains
      exact PartialTyContains.box (ih hcontains)
  | boxFull _hinner ih =>
      intro hcontains
      exact PartialTyContains.tyBox (ih hcontains)

theorem PartialTyContains.pathSelect :
    ∀ {root : PartialTy} {needle : Ty},
      PartialTyContains root needle →
      ∃ path, PathSelect path root (.ty needle) := by
  intro root needle hcontains
  induction hcontains with
  | here =>
      exact ⟨[], PathSelect.here⟩
  | tyBox _hinner ih =>
      rcases ih with ⟨path, hselect⟩
      exact ⟨() :: path, PathSelect.boxFull hselect⟩
  | box _hinner ih =>
      rcases ih with ⟨path, hselect⟩
      exact ⟨() :: path, PathSelect.box hselect⟩

theorem PathSelect.borrow_contains_to_leaf :
    ∀ {path : Path} {root leafTy : PartialTy} {mutable : Bool} {u : LVal},
      PathSelect path root leafTy →
      PartialTyContains root (.borrow mutable u) →
      PartialTyContains leafTy (.borrow mutable u) := by
  intro path root leafTy mutable u hselect
  induction hselect with
  | here =>
      intro hcontains
      exact hcontains
  | box _hinner ih =>
      intro hcontains
      cases hcontains with
      | box hinner =>
          exact ih hinner
  | boxFull _hinner ih =>
      intro hcontains
      cases hcontains with
      | tyBox hinner =>
          exact ih hinner

theorem PathSelect.append_inv :
    ∀ {p₁ p₂ : Path} {root leaf : PartialTy},
      PathSelect (p₁ ++ p₂) root leaf →
      ∃ mid, PathSelect p₁ root mid ∧ PathSelect p₂ mid leaf := by
  intro p₁
  induction p₁ with
  | nil =>
      intro p₂ root leaf hselect
      exact ⟨root, PathSelect.here, by simpa using hselect⟩
  | cons _ p ih =>
      intro p₂ root leaf hselect
      cases hselect with
      | box hinner =>
          rcases ih hinner with ⟨mid, hprefix, hsuffix⟩
          exact ⟨mid, PathSelect.box hprefix, hsuffix⟩
      | boxFull hinner =>
          rcases ih hinner with ⟨mid, hprefix, hsuffix⟩
          exact ⟨mid, PathSelect.boxFull hprefix, hsuffix⟩

/-- Pure selections are deterministic. -/
theorem PathSelect.deterministic :
    ∀ {path : Path} {root a b : PartialTy},
      PathSelect path root a → PathSelect path root b → a = b := by
  intro path root a b ha
  induction ha with
  | here =>
      intro hb
      cases hb
      rfl
  | box hinner ih =>
      intro hb
      cases hb with
      | box hinner' => exact ih hinner'
  | boxFull hinner ih =>
      intro hb
      cases hb with
      | boxFull hinner' => exact ih hinner'

/-- Unit paths are determined by their length. -/
theorem Path.eq_of_length_eq :
    ∀ {p₁ p₂ : Path}, p₁.length = p₂.length → p₁ = p₂ := by
  intro p₁
  induction p₁ with
  | nil =>
      intro p₂ hlen
      cases p₂ with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons _ p ih =>
      intro p₂ hlen
      cases p₂ with
      | nil => simp at hlen
      | cons _ p' =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [ih hlen]

theorem PathSelect.snoc_box :
    ∀ {path : Path} {root inner : PartialTy},
    PathSelect path root (.box inner) →
    PathSelect (path ++ [()]) root inner
  | [], root, inner, hselect => by
      cases hselect
      exact PathSelect.box PathSelect.here
  | () :: path, root, inner, hselect => by
      cases hselect with
      | box hinner =>
          simpa [List.cons_append] using
            PathSelect.box (PathSelect.snoc_box hinner)
      | boxFull hinner =>
          simpa [List.cons_append] using
            PathSelect.boxFull (PathSelect.snoc_box hinner)

theorem PathSelect.snoc_boxFull :
    ∀ {path : Path} {root : PartialTy} {inner : Ty},
    PathSelect path root (.ty (.box inner)) →
    PathSelect (path ++ [()]) root (.ty inner)
  | [], root, inner, hselect => by
      cases hselect
      exact PathSelect.boxFull PathSelect.here
  | () :: path, root, inner, hselect => by
      cases hselect with
      | box hinner =>
          simpa [List.cons_append] using
            PathSelect.box (PathSelect.snoc_boxFull hinner)
      | boxFull hinner =>
          simpa [List.cons_append] using
            PathSelect.boxFull (PathSelect.snoc_boxFull hinner)

theorem PathSelect.exists_strike_undef :
    ∀ {path : Path} {root : PartialTy} {leaf : Ty},
      PathSelect path root (.ty leaf) →
      ∃ struck, Strike path root struck
  | [], root, leaf, hselect => by
      cases hselect
      exact ⟨.undef leaf, rfl⟩
  | () :: path, root, leaf, hselect => by
      cases hselect with
      | box hinner =>
          rcases PathSelect.exists_strike_undef hinner with
            ⟨struck, hstrike⟩
          exact ⟨.box struck, hstrike⟩
      | boxFull hinner =>
          rcases PathSelect.exists_strike_undef hinner with
            ⟨struck, hstrike⟩
          exact ⟨.box struck, hstrike⟩

theorem PathSelect.update_env_eq {env env₂ : Env}
    {path : Path} {root selected updatedTy : PartialTy} {rhsTy : Ty} :
    PathSelect path root selected →
    UpdateAtPath env path root rhsTy env₂ updatedTy →
    env₂ = env := by
  intro hselect
  induction hselect generalizing env₂ updatedTy rhsTy with
  | here =>
      intro hupdate
      cases hupdate
      rfl
  | box hinner ih =>
      intro hupdate
      cases hupdate with
      | box hupdateInner =>
          exact ih hupdateInner
  | boxFull hinner ih =>
      intro hupdate
      cases hupdate with
      | boxFull hupdateInner =>
          exact ih hupdateInner

theorem PathSelect.update_contains_rhs {env env₂ : Env}
    {path : Path} {root selected updatedTy : PartialTy} {rhsTy : Ty}
    {needle : Ty} :
    PathSelect path root selected →
    UpdateAtPath env path root rhsTy env₂ updatedTy →
    PartialTyContains (.ty rhsTy) needle →
    PartialTyContains updatedTy needle := by
  intro hselect
  induction hselect generalizing env₂ updatedTy rhsTy with
  | here =>
      intro hupdate hcontains
      cases hupdate
      exact hcontains
  | box hinner ih =>
      intro hupdate hcontains
      cases hupdate with
      | box hupdateInner =>
          exact PartialTyContains.box (ih hupdateInner hcontains)
  | boxFull hinner ih =>
      intro hupdate hcontains
      cases hupdate with
      | boxFull hupdateInner =>
          have hinnerContains := ih hupdateInner hcontains
          cases hinnerContains with
          | here =>
              exact PartialTyContains.tyBox PartialTyContains.here
          | tyBox hinner =>
              exact PartialTyContains.tyBox (PartialTyContains.tyBox hinner)
          | box hinner =>
              exact PartialTyContains.box (PartialTyContains.box hinner)

theorem PathSelect.update_borrows {env env₂ : Env}
    {path : Path} {root selected updatedTy : PartialTy} {rhsTy : Ty}
    {mutable : Bool} {u : LVal} :
    PathSelect path root selected →
    UpdateAtPath env path root rhsTy env₂ updatedTy →
    PartialTyContains updatedTy (.borrow mutable u) →
    PartialTyContains (.ty rhsTy) (.borrow mutable u) := by
  intro hselect
  induction hselect generalizing env₂ updatedTy rhsTy with
  | here =>
      intro hupdate hcontains
      cases hupdate
      exact hcontains
  | box _hinner ih =>
      intro hupdate hcontains
      cases hupdate with
      | box hupdateInner =>
          cases hcontains with
          | box hinnerContains =>
              exact ih hupdateInner hinnerContains
  | boxFull _hinner ih =>
      intro hupdate hcontains
      cases hupdate with
      | boxFull hupdateInner =>
          exact ih hupdateInner
            (PartialTyContains.partialTyRebox_borrow_inv hcontains)

theorem EnvWrite.pathSelect_update_eq {env env' : Env} {lhs : LVal}
    {rhsTy : Ty} {leaf : PartialTy} {envSlot : EnvSlot} :
    env.slotAt (LVal.base lhs) = some envSlot →
    PathSelect (LVal.path lhs) envSlot.ty leaf →
    EnvWrite env lhs rhsTy env' →
    ∃ updatedTy,
      UpdateAtPath env (LVal.path lhs) envSlot.ty rhsTy env updatedTy ∧
        env' = env.update (LVal.base lhs) { envSlot with ty := updatedTy } := by
  intro hslot hselect hwrite
  cases hwrite with
  | @intro writeEnv _writeLv writeSlot _writeTy updatedTy hwriteSlot hupdate =>
      have hwriteSlotEq : writeSlot = envSlot := by
        have hslot' : env.slotAt (LVal.base lhs) = some writeSlot := by
          simpa using hwriteSlot
        exact Option.some.inj (hslot'.symm.trans hslot)
      subst hwriteSlotEq
      have henvEq : writeEnv = env :=
        PathSelect.update_env_eq hselect hupdate
      subst henvEq
      exact ⟨updatedTy, hupdate, rfl⟩

theorem EnvWrite.pathSelect_result_contains {env env' : Env} {lhs : LVal}
    {rhsTy : Ty} {leaf : PartialTy} {envSlot : EnvSlot} :
    env.slotAt (LVal.base lhs) = some envSlot →
    PathSelect (LVal.path lhs) envSlot.ty leaf →
    EnvWrite env lhs rhsTy env' →
    (∀ {mutable : Bool} {target : LVal},
      PartialTyContains (.ty rhsTy) (.borrow mutable target) →
      env' ⊢ (LVal.base lhs) ↝ (.borrow mutable target)) ∧
    (∀ y, y ≠ LVal.base lhs → env'.slotAt y = env.slotAt y) := by
  intro hslot hselect hwrite
  rcases EnvWrite.pathSelect_update_eq hslot hselect hwrite with
    ⟨updatedTy, hupdate, henv'⟩
  constructor
  · intro mutable target hcontains
    refine ⟨{ envSlot with ty := updatedTy }, ?_, ?_⟩
    · rw [henv']
      simp [Env.update]
    · exact PathSelect.update_contains_rhs hselect hupdate hcontains
  · intro y hy
    rw [henv']
    simp [Env.update, hy]

/-- Snoc decomposition of a pure selection: the last step descends either a
partial box or a full box from the second-to-last node. -/
theorem PathSelect.snoc_inv :
    ∀ {path : Path} {root leaf : PartialTy},
      PathSelect (path ++ [()]) root leaf →
      ∃ mid, PathSelect path root mid ∧
        (mid = .box leaf ∨ ∃ T, mid = .ty (.box T) ∧ leaf = .ty T) := by
  intro path
  induction path with
  | nil =>
      intro root leaf hselect
      cases hselect with
      | box hinner =>
          cases hinner
          exact ⟨_, PathSelect.here, Or.inl rfl⟩
      | boxFull hinner =>
          cases hinner
          exact ⟨_, PathSelect.here, Or.inr ⟨_, rfl, rfl⟩⟩
  | cons _ p ih =>
      intro root leaf hselect
      cases hselect with
      | box hinner =>
          rcases ih hinner with ⟨mid, hmid, hshape⟩
          exact ⟨mid, PathSelect.box hmid, hshape⟩
      | boxFull hinner =>
          rcases ih hinner with ⟨mid, hmid, hshape⟩
          exact ⟨mid, PathSelect.boxFull hmid, hshape⟩

theorem PathSelect.lvalTyping_prepend_var
    {env : Env} {x : Name} {slot : EnvSlot} :
    ∀ {path : Path} {root leaf : PartialTy},
      env.slotAt x = some slot →
      slot.ty = root →
      PathSelect path root leaf →
      LValTyping env (prependPath path (.var x)) leaf slot.lifetime := by
  intro path
  induction path with
  | nil =>
      intro root leaf hslot hroot hselect
      cases hselect
      simpa [prependPath, hroot] using LValTyping.var hslot
  | cons _ path ih =>
      intro root leaf hslot hroot hselect
      have hselectSnoc : PathSelect (path ++ [()]) root leaf := by
        simpa [List.Unit_append_singleton_typing] using hselect
      rcases PathSelect.snoc_inv hselectSnoc with
        ⟨mid, hmid, hshape⟩
      have hprefix :
          LValTyping env (prependPath path (.var x)) mid slot.lifetime :=
        ih hslot hroot hmid
      rcases hshape with hpartial | ⟨T, hfull, hleaf⟩
      · subst hpartial
        simpa [prependPath] using LValTyping.box hprefix
      · subst hfull
        subst hleaf
        simpa [prependPath] using LValTyping.boxFull hprefix

theorem EnvContains.borrow_pathSelect_lvalTyping
    {env : Env} {y : Name} {mutable : Bool} {target : LVal} :
    env ⊢ y ↝ (.borrow mutable target) →
    ∃ (slot : EnvSlot) (path : Path),
      env.slotAt y = some slot ∧
        PathSelect path slot.ty (.ty (.borrow mutable target)) ∧
        LValTyping env (prependPath path (.var y))
          (.ty (.borrow mutable target)) slot.lifetime := by
  intro hentry
  rcases hentry with ⟨slot, hslot, hcontains⟩
  rcases PartialTyContains.pathSelect hcontains with ⟨path, hselect⟩
  refine ⟨slot, path, hslot, hselect, ?_⟩
  exact PathSelect.lvalTyping_prepend_var hslot rfl hselect

/-- A typing derivation and a pure selection over the same lvalue path from
the same base slot compute the same partial type.  In particular a selectable
lvalue never types through a borrow hop. -/
theorem LValTyping.pathSelect_deterministic {env : Env} :
    ∀ {lv : LVal} {pt mid : PartialTy} {lf : Lifetime} {slot : EnvSlot},
      LValTyping env lv pt lf →
      env.slotAt (LVal.base lv) = some slot →
      PathSelect (LVal.path lv) slot.ty mid →
      pt = mid := by
  intro lv
  induction lv with
  | var x =>
      intro pt mid lf slot htyping hslot hselect
      rcases LValTyping.var_inv htyping with ⟨envSlot, henvSlot, htyEq, _⟩
      have hslotEq : slot = envSlot :=
        Option.some.inj
          ((by simpa [LVal.base] using hslot :
              env.slotAt x = some slot).symm.trans henvSlot)
      subst hslotEq
      have hmid : mid = slot.ty := by
        cases hselect
        rfl
      rw [htyEq, hmid]
  | deref source ih =>
      intro pt mid lf slot htyping hslot hselect
      have hselect' : PathSelect (LVal.path source ++ [()]) slot.ty mid := by
        simpa [LVal.path] using hselect
      rcases PathSelect.snoc_inv hselect' with ⟨midp, hmidp, hshape⟩
      cases htyping with
      | box hsource =>
          have hsourceEq : PartialTy.box pt = midp :=
            ih hsource (by simpa [LVal.base] using hslot) hmidp
          rcases hshape with hbox | ⟨T, htyBox, _hleaf⟩
          · rw [hbox] at hsourceEq
            cases hsourceEq
            rfl
          · rw [htyBox] at hsourceEq
            cases hsourceEq
      | boxFull hsource =>
          rename_i inner
          have hsourceEq : PartialTy.ty (.box inner) = midp :=
            ih hsource (by simpa [LVal.base] using hslot) hmidp
          rcases hshape with hbox | ⟨T, htyBox, hleaf⟩
          · rw [hbox] at hsourceEq
            cases hsourceEq
          · rw [htyBox] at hsourceEq
            cases hsourceEq
            rw [hleaf]
      | borrow hsource _htarget =>
          have hsourceEq :
              PartialTy.ty (.borrow _ _) = midp :=
            ih hsource (by simpa [LVal.base] using hslot) hmidp
          rcases hshape with hbox | ⟨T, htyBox, _hleaf⟩
          · rw [hbox] at hsourceEq
            cases hsourceEq
          · rw [htyBox] at hsourceEq
            cases hsourceEq

theorem WriteProhibited.transport_of_pointwise {env result : Env} {lv : LVal}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    WriteProhibited env lv → WriteProhibited result lv := by
  intro hwrite
  have hcontains :
      ∀ {x mutable target},
        env ⊢ x ↝ (.borrow mutable target) →
        result ⊢ x ↝ (.borrow mutable target) := by
    intro x mutable target henvContains
    rcases henvContains with ⟨slot, hslot, hcontainsTy⟩
    exact ⟨slot, (heq x).trans hslot, hcontainsTy⟩
  cases hwrite with
  | inl hread =>
      rcases hread with ⟨x, target, henvContains, hconflict⟩
      exact Or.inl ⟨x, target, hcontains henvContains, hconflict⟩
  | inr hwrite =>
      rcases hwrite with ⟨x, target, henvContains, hconflict⟩
      exact Or.inr ⟨x, target, hcontains henvContains, hconflict⟩

theorem not_writeProhibited_of_pointwise {env result : Env} {lv : LVal}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    ¬ WriteProhibited env lv → ¬ WriteProhibited result lv := by
  intro hnotWrite hwriteResult
  exact hnotWrite
    (WriteProhibited.transport_of_pointwise
      (env := result) (result := env) (fun y => (heq y).symm)
      hwriteResult)

theorem LValBaseOutlives.transport_of_pointwise {env result : Env}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    ∀ {target : LVal} {lifetime : Lifetime},
      LValBaseOutlives env target lifetime →
      LValBaseOutlives result target lifetime := by
  intro target lifetime hbase
  rcases hbase with ⟨baseSlot, hbaseSlot, hle⟩
  exact ⟨baseSlot, (heq (LVal.base target)).trans hbaseSlot, hle⟩

theorem WellFormedEnv.transport_of_pointwise
    {env result : Env} {lifetime : Lifetime}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    WellFormedEnv env lifetime →
    WellFormedEnv result lifetime := by
  intro hwell
  refine ⟨?contained, ?outlive⟩
  · intro x slot mutable target hslotResult hcontainsResult
    have hslotEnv : env.slotAt x = some slot :=
      (heq x).symm.trans hslotResult
    rcases hcontainsResult with
      ⟨containedSlot, hcontainedSlotResult, hcontainsTy⟩
    have hcontainedSlotEnv : env.slotAt x = some containedSlot :=
      (heq x).symm.trans hcontainedSlotResult
    rcases hwell.1 x slot mutable target hslotEnv
        ⟨containedSlot, hcontainedSlotEnv, hcontainsTy⟩ with
      ⟨targetTy, targetLifetime, htyping, hle, hbase⟩
    exact ⟨targetTy, targetLifetime,
      LValTyping.transport_of_pointwise heq htyping, hle,
      LValBaseOutlives.transport_of_pointwise heq hbase⟩
  · intro x slot hslotResult
    exact hwell.2 x slot ((heq x).symm.trans hslotResult)

theorem WellFormedEnvWhenInitialized.transport_of_pointwise
    {env result : Env} {lifetime : Lifetime}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    WellFormedEnvWhenInitialized env lifetime →
    WellFormedEnvWhenInitialized result lifetime := by
  intro hwell
  have hbaseForward :
      ∀ {target : LVal} {slotLifetime : Lifetime},
        LValBaseOutlives env target slotLifetime →
        LValBaseOutlives result target slotLifetime := by
    intro target slotLifetime hbase
    rcases hbase with ⟨baseSlot, hbaseSlot, hle⟩
    exact ⟨baseSlot, (heq (LVal.base target)).trans hbaseSlot, hle⟩
  refine ⟨?contained, ?outlive⟩
  · intro x slot mutable target hslotResult hcontainsResult
    have hslotEnv : env.slotAt x = some slot :=
      (heq x).symm.trans hslotResult
    rcases hcontainsResult with
      ⟨containedSlot, hcontainedSlotResult, hcontainsTy⟩
    have hcontainedSlotEnv : env.slotAt x = some containedSlot :=
      (heq x).symm.trans hcontainedSlotResult
    rcases hwell.1 x slot mutable target hslotEnv
        ⟨containedSlot, hcontainedSlotEnv, hcontainsTy⟩ with
      ⟨hbase, hwhenInitialized⟩
    refine ⟨hbaseForward hbase, ?_⟩
    intro htargetResult
    have htargetEnv : TargetInitialized env target := by
      rcases htargetResult with ⟨targetTy, targetLifetime, htyping⟩
      exact ⟨targetTy, targetLifetime,
        LValTyping.transport_of_pointwise
          (env := result) (env₃ := env) (fun y => (heq y).symm)
          htyping⟩
    rcases hwhenInitialized htargetEnv with
      ⟨targetTy, targetLifetime, htyping, hle, hbase'⟩
    exact ⟨targetTy, targetLifetime,
      LValTyping.transport_of_pointwise heq htyping, hle,
      hbaseForward hbase'⟩
  · intro x slot hslotResult
    exact hwell.2 x slot ((heq x).symm.trans hslotResult)

theorem PathSelect.ownerChainPrefix_whenInitialized {store : ProgramStore}
    {env : Env} {rootLoc : Location} {rootSlot : StoreSlot}
    {path : Path} {rootTy leafTy : PartialTy} :
    store.slotAt rootLoc = some rootSlot →
    ValidPartialValueWhenInitialized env store rootSlot.value rootTy →
    PathSelect path rootTy leafTy →
    ∃ leaf leafSlot,
      store.slotAt leaf = some leafSlot ∧
      ValidPartialValueWhenInitialized env store leafSlot.value leafTy ∧
      OwnerChainPrefix store rootLoc rootSlot.value path leaf := by
  intro hrootSlot hvalid hselect
  induction hselect generalizing rootLoc rootSlot with
  | here =>
      exact ⟨rootLoc, rootSlot, hrootSlot, hvalid, Or.inl ⟨rfl, rfl⟩⟩
  | box hinner ih =>
      cases rootSlot with
      | mk rootValue rootLifetime =>
      cases hvalid with
      | box hownedSlot hinnerValid =>
          rename_i ownerLocation ownerSlot
          rcases ih hownedSlot hinnerValid with
            ⟨leaf, leafSlot, hleafSlot, hleafValid, hprefix⟩
          refine ⟨leaf, leafSlot, hleafSlot, hleafValid, ?_⟩
          rcases OwnerChainPrefix.prepend_owner hrootSlot rfl hownedSlot
              hprefix with
            ⟨k, hchain, howns, hlen⟩
          exact Or.inr ⟨k, hchain, howns, hlen⟩
  | boxFull hinner ih =>
      cases rootSlot with
      | mk rootValue rootLifetime =>
      cases hvalid with
      | boxFull hownedSlot hinnerValid =>
          rename_i ownerLocation ownerSlot
          rcases ih hownedSlot hinnerValid with
            ⟨leaf, leafSlot, hleafSlot, hleafValid, hprefix⟩
          refine ⟨leaf, leafSlot, hleafSlot, hleafValid, ?_⟩
          rcases OwnerChainPrefix.prepend_owner hrootSlot rfl hownedSlot
              hprefix with
            ⟨k, hchain, howns, hlen⟩
          exact Or.inr ⟨k, hchain, howns, hlen⟩

theorem OwnerChainPrefix.extend {store : ProgramStore}
    {rootLoc location next : Location} {rootValue : PartialValue}
    {path : Path} {slot : StoreSlot} :
    OwnerChainPrefix store rootLoc rootValue path location →
    (path = [] → rootValue = slot.value) →
    store.slotAt location = some slot →
    slot.value = .value (.ref { location := next, owner := true }) →
    ∃ k,
      OwnerChainAt store rootValue (path ++ [()]) next ∧
      OwnsChain store rootLoc k next ∧
      k = (path ++ [()]).length := by
  intro hprefix hrootValue hslot hvalue
  rcases hprefix with ⟨hpath, hlocation⟩ | ⟨k, hchain, howns, hlen⟩
  · subst hpath
    have howner : OwnerChainAt store rootValue [()] next := by
      rw [hrootValue rfl, hvalue]
      exact OwnerChainAt.here
    refine ⟨1, by simpa using howner, ?_, by simp⟩
    have howns1 : OwnsChain store location 1 next := by
      simpa using ownsChain_extend
        (OwnsChain.zero (store := store) (location := location))
        hslot hvalue
    subst hlocation
    simpa using howns1
  · refine ⟨k + 1, ?_, ?_, ?_⟩
    · exact OwnerChainAt.extend hchain hslot hvalue
    · exact ownsChain_extend howns hslot hvalue
    · simp [List.length_append, hlen]

theorem ProgramStore.loc_eq_var_of_path_nil {store : ProgramStore}
    {lv : LVal} :
    LVal.path lv = [] →
    store.loc lv = some (VariableProjection (LVal.base lv)) := by
  intro hpath
  cases lv with
  | var x =>
      simp [ProgramStore.loc, VariableProjection, LVal.base]
  | deref source =>
      simp [LVal.path] at hpath

theorem ownsChain_loc_eq_of_length {store : ProgramStore} :
    ∀ {lv : LVal} {leaf : Location} {k : Nat},
      OwnsChain store (VariableProjection (LVal.base lv)) k leaf →
      k = (LVal.path lv).length →
      ∀ {location : Location},
        store.loc lv = some location →
        location = leaf := by
  intro lv
  induction lv with
  | var x =>
      intro leaf k hchain hlen location hloc
      simp [LVal.path] at hlen
      subst k
      cases hchain
      simpa [ProgramStore.loc, VariableProjection, LVal.base] using hloc.symm
  | deref source ih =>
      intro leaf k hchain hlen location hloc
      cases hsourceLoc : store.loc source with
      | none =>
          simp [ProgramStore.loc, hsourceLoc] at hloc
      | some sourceLocation =>
          cases hchain with
          | zero =>
              simp [LVal.path, List.length_append] at hlen
          | succ hprefix howns =>
              rename_i chainLocation n
              have hn : n = (LVal.path source).length := by
                simp [LVal.path, List.length_append] at hlen
                omega
              have hsourceEq : sourceLocation = chainLocation :=
                ih hprefix hn hsourceLoc
              subst hsourceEq
              rcases howns with ⟨ownLifetime, hslotOwn⟩
              simpa [ProgramStore.loc, hsourceLoc, hslotOwn, owningRef]
                using hloc.symm

theorem PathSelect.runtime_leaf_whenInitialized {store : ProgramStore}
    {env : Env} {lv : LVal} {rootSlot : EnvSlot} {leafTy : PartialTy} :
    SafeAbstraction store env →
    env.slotAt (LVal.base lv) = some rootSlot →
    PathSelect (LVal.path lv) rootSlot.ty leafTy →
    ∃ rootStore leaf leafSlot k,
      store.slotAt (VariableProjection (LVal.base lv)) = some rootStore ∧
      rootStore.lifetime = rootSlot.lifetime ∧
      ValidPartialValueWhenInitialized env store rootStore.value
        rootSlot.ty ∧
      store.slotAt leaf = some leafSlot ∧
      ValidPartialValueWhenInitialized env store leafSlot.value leafTy ∧
      OwnerChainPrefix store (VariableProjection (LVal.base lv))
        rootStore.value (LVal.path lv) leaf ∧
      OwnsChain store (VariableProjection (LVal.base lv)) k leaf ∧
      k = (LVal.path lv).length ∧
      ∀ {location : Location}, store.loc lv = some location →
        location = leaf := by
  intro hsafe henv hselect
  rcases hsafe.2 (LVal.base lv) rootSlot henv with
    ⟨rootValue, hrootStore, hrootValid⟩
  let rootStore : StoreSlot :=
    { value := rootValue, lifetime := rootSlot.lifetime }
  have hrootStore' :
      store.slotAt (VariableProjection (LVal.base lv)) =
        some rootStore := by
    simpa [rootStore] using hrootStore
  rcases
      PathSelect.ownerChainPrefix_whenInitialized hrootStore'
        (by simpa [rootStore] using hrootValid) hselect with
    ⟨leaf, leafSlot, hleafStore, hleafValid, hprefix⟩
  rcases OwnerChainPrefix.ownsChain_length hprefix with
    ⟨k, hchain, hlen⟩
  refine ⟨rootStore, leaf, leafSlot, k, hrootStore', rfl,
    by simpa [rootStore] using hrootValid, hleafStore, hleafValid,
    hprefix, hchain, hlen, ?_⟩
  intro location hloc
  exact ownsChain_loc_eq_of_length hchain hlen hloc

theorem locReads_ownsChain_of_ownsChain_length {store : ProgramStore} :
    ∀ {lv : LVal} {leaf : Location} {k : Nat},
      OwnsChain store (VariableProjection (LVal.base lv)) k leaf →
      k = (LVal.path lv).length →
      ∀ {mid : Location},
        RuntimeFrame.LocReads store lv mid →
        ∃ j, OwnsChain store (VariableProjection (LVal.base lv)) j mid ∧
          j < (LVal.path lv).length := by
  intro lv
  induction lv with
  | var x =>
      intro leaf k hchain hlen mid hreads
      cases hreads
  | deref source ih =>
      intro leaf k hchain hlen mid hreads
      cases hreads with
      | here hloc =>
          cases hchain with
          | zero =>
              simp [LVal.path, List.length_append] at hlen
          | succ hprefix howns =>
              rename_i chainLocation n
              have hn : n = (LVal.path source).length := by
                simp [LVal.path, List.length_append] at hlen
                omega
              have hmidEq : mid = chainLocation :=
                ownsChain_loc_eq_of_length (lv := source) hprefix hn hloc
              subst hmidEq
              refine ⟨n, ?_, ?_⟩
              · simpa [LVal.base] using hprefix
              · simp [LVal.path, List.length_append]
                omega
      | there hsourceReads =>
          cases hchain with
          | zero =>
              simp [LVal.path, List.length_append] at hlen
          | succ hprefix howns =>
              rename_i chainLocation n
              have hn : n = (LVal.path source).length := by
                simp [LVal.path, List.length_append] at hlen
                omega
              rcases ih hprefix hn hsourceReads with ⟨j, hchainMid, hlt⟩
              refine ⟨j, ?_, ?_⟩
              · simpa [LVal.base] using hchainMid
              · simp [LVal.path, List.length_append]
                omega

theorem OwnerChainPrefix.locReads_ownsChain {store : ProgramStore} :
    ∀ {lv : LVal} {rootValue : PartialValue} {leaf : Location},
      OwnerChainPrefix store (VariableProjection (LVal.base lv)) rootValue
        (LVal.path lv) leaf →
      ∀ {mid : Location},
        RuntimeFrame.LocReads store lv mid →
        ∃ j, OwnsChain store (VariableProjection (LVal.base lv)) j mid ∧
          j < (LVal.path lv).length := by
  intro lv rootValue leaf hprefix mid hreads
  rcases hprefix with ⟨hpath, _hleaf⟩ | ⟨k, _hchainAt, hchain, hlen⟩
  · cases lv with
    | var x =>
        cases hreads
    | deref source =>
        have hfalse : False := by
          simpa [LVal.path] using hpath
        exact False.elim hfalse
  · exact locReads_ownsChain_of_ownsChain_length hchain hlen hreads

theorem locReads_ne_ownsChain_leaf {store : ProgramStore} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ∀ {lv : LVal} {rootValue : PartialValue} {leaf : Location} {k : Nat},
      OwnerChainPrefix store (VariableProjection (LVal.base lv)) rootValue
        (LVal.path lv) leaf →
      OwnsChain store (VariableProjection (LVal.base lv)) k leaf →
      k = (LVal.path lv).length →
      ∀ {mid : Location},
        RuntimeFrame.LocReads store lv mid →
        mid ≠ leaf := by
  intro hvalidStore hheap lv rootValue leaf k hprefix hleafChain hlen mid hreads
    hmidEq
  rcases OwnerChainPrefix.locReads_ownsChain hprefix hreads with
    ⟨j, hmidChain, hlt⟩
  subst hmidEq
  have hjk : j = k :=
    ownsChain_unique_length hvalidStore (var_not_owned hheap)
      hmidChain hleafChain
  rw [← hlen, hjk] at hlt
  omega

theorem locReads_ne_of_ownsChain_length {store : ProgramStore}
    {lv : LVal} {leaf : Location} {k : Nat} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    OwnsChain store (VariableProjection (LVal.base lv)) k leaf →
    k = (LVal.path lv).length →
    ∀ {mid : Location},
      RuntimeFrame.LocReads store lv mid → mid ≠ leaf := by
  intro hvalidStore hheap hleafChain hlen mid hreads hmid
  rcases locReads_ownsChain_of_ownsChain_length hleafChain hlen hreads with
    ⟨j, hmidChain, hjLt⟩
  subst hmid
  have hjk : j = k :=
    ownsChain_unique_length hvalidStore (var_not_owned hheap)
      hmidChain hleafChain
  rw [hjk, hlen] at hjLt
  omega

theorem ProgramStore.loc_prependPath_eq_of_loc_eq
    {store : ProgramStore} {left right : LVal} :
    store.loc left = store.loc right →
    ∀ path : Path,
      store.loc (prependPath path left) =
        store.loc (prependPath path right) := by
  intro hloc path
  induction path with
  | nil =>
      simpa [prependPath] using hloc
  | cons head tail ih =>
      cases head
      simp [prependPath, ProgramStore.loc, ih]

theorem locReads_prependPath_of_locReads {store : ProgramStore} :
    ∀ (p : Path) {lv : LVal} {mid : Location},
      RuntimeFrame.LocReads store lv mid →
      RuntimeFrame.LocReads store (prependPath p lv) mid := by
  intro p
  induction p with
  | nil =>
      intro lv mid hread
      simpa [prependPath] using hread
  | cons _ p ih =>
      intro lv mid hread
      exact RuntimeFrame.LocReads.there (ih hread)

theorem locReads_prependPath_hop {store : ProgramStore} {s₀ target : LVal}
    (hloc : store.loc s₀.deref = store.loc target) :
    ∀ (p : Path) {mid : Location},
      RuntimeFrame.LocReads store (prependPath p s₀.deref) mid →
      RuntimeFrame.LocReads store s₀ mid ∨
        store.loc s₀ = some mid ∨
        RuntimeFrame.LocReads store (prependPath p target) mid := by
  intro p
  induction p with
  | nil =>
      intro mid hread
      simp [prependPath] at hread
      cases hread with
      | here hsource =>
          exact Or.inr (Or.inl hsource)
      | there hsource =>
          exact Or.inl hsource
  | cons _ p ih =>
      intro mid hread
      cases hread with
      | here hsource =>
          have hlocPath :
              store.loc (prependPath p s₀.deref) =
                store.loc (prependPath p target) :=
            ProgramStore.loc_prependPath_eq_of_loc_eq hloc p
          have htarget :
              store.loc (prependPath p target) = some mid := by
            rwa [hlocPath] at hsource
          exact Or.inr (Or.inr (RuntimeFrame.LocReads.here htarget))
      | there hsource =>
          rcases ih hsource with hbaseReads | hbaseLoc | htargetReads
          · exact Or.inl hbaseReads
          · exact Or.inr (Or.inl hbaseLoc)
          · exact Or.inr (Or.inr (RuntimeFrame.LocReads.there htargetReads))

theorem ProgramStore.read_eq_of_loc_eq
    {store : ProgramStore} {left right : LVal} :
    store.loc left = store.loc right →
    store.read left = store.read right := by
  intro hloc
  simp [ProgramStore.read, hloc]

theorem ProgramStore.write_eq_of_loc_eq
    {store : ProgramStore} {left right : LVal} {value : PartialValue} :
    store.loc left = store.loc right →
    store.write left value = store.write right value := by
  intro hloc
  simp [ProgramStore.write, hloc]

/-- Assignment redexes with the same concrete write location take the same
runtime step.  This packages the operational side of mutable-borrow
re-rooting: after the source borrow is known live, the step can be replayed at
the borrow target. -/
theorem assign_step_of_loc_eq
    {store store' : ProgramStore} {lifetime : Lifetime}
    {left right : LVal} {value finalValue : Value} :
    store.loc left = store.loc right →
    Step store lifetime (.assign left (.val value)) store' (.val finalValue) →
    Step store lifetime (.assign right (.val value)) store' (.val finalValue) := by
  intro hloc hstep
  cases hstep with
  | assign hread hwrite hdrops =>
      exact Step.assign
        (by simpa [ProgramStore.read, hloc] using hread)
        (by simpa [ProgramStore.write, hloc] using hwrite)
        hdrops

/-- Assignment runtime validity depends on the RHS value, not on the syntactic
left-hand side.  This is the validity companion to `assign_step_of_loc_eq`. -/
theorem validRuntimeState_assign_lhs_of_value
    {store : ProgramStore} {left right : LVal} {value : Value} :
    ValidRuntimeState store (.assign left (.val value)) →
    ValidRuntimeState store (.assign right (.val value)) := by
  intro hvalid
  exact validRuntimeState_assign_value_of_value
    (validRuntimeState_assign_inner hvalid)

/-- If a typed borrow source is dereferenced while its target is initialized,
the runtime lvalue computation re-roots at the target location. -/
theorem lvalTyping_deref_borrow_loc_eq_whenInitialized
    {store : ProgramStore} {env : Env}
    {source target : LVal} {mutable : Bool}
    {borrowLifetime targetLifetime : Lifetime} {targetTy : Ty} :
    SafeAbstraction store env →
    LValTyping env source (.ty (.borrow mutable target)) borrowLifetime →
    LValTyping env target (.ty targetTy) targetLifetime →
    store.loc source.deref = store.loc target := by
  intro hsafe hsource htarget
  rcases lvalTyping_defined_location_whenInitialized hsafe hsource with
    ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hsourceValid with
  | borrowLive _hinitialized htargetLoc =>
      simp [ProgramStore.loc, hsourceLoc, hsourceSlot, htargetLoc]
  | borrowStale hstale =>
      exact False.elim (hstale ⟨targetTy, targetLifetime, htarget⟩)

/-- Re-root an assignment step below a live borrow hop, preserving any
remaining dereference suffix. -/
theorem assign_step_prependPath_deref_borrow_whenInitialized
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime}
    {source target : LVal} {mutable : Bool}
    {borrowLifetime targetLifetime : Lifetime} {targetTy : Ty}
    {path : Path} {value finalValue : Value} :
    SafeAbstraction store env →
    LValTyping env source (.ty (.borrow mutable target)) borrowLifetime →
    LValTyping env target (.ty targetTy) targetLifetime →
    Step store lifetime (.assign (prependPath path source.deref) (.val value))
      store' (.val finalValue) →
    Step store lifetime (.assign (prependPath path target) (.val value))
      store' (.val finalValue) := by
  intro hsafe hsource htarget hstep
  have hloc :
      store.loc (prependPath path source.deref) =
        store.loc (prependPath path target) :=
    ProgramStore.loc_prependPath_eq_of_loc_eq
      (lvalTyping_deref_borrow_loc_eq_whenInitialized
        hsafe hsource htarget)
      path
  exact assign_step_of_loc_eq hloc hstep

theorem Env.update_same_pointwise {env : Env} {x : Name} {slot : EnvSlot} :
    env.slotAt x = some slot →
    ∀ y, (env.update x slot).slotAt y = env.slotAt y := by
  intro hslot y
  by_cases hy : y = x
  · subst hy
    simp [Env.update, hslot]
  · simp [Env.update, hy]

theorem EnvWrite.deref_borrow_var_inv
    {env env' : Env} {x : Name} {slot : EnvSlot} {target : LVal}
    {rhsTy : Ty} :
    env.slotAt x = some slot →
    slot.ty = .ty (.borrow true target) →
    EnvWrite env (.deref (.var x)) rhsTy env' →
    ∃ nested,
      EnvWrite env target rhsTy nested ∧
      env' = nested.update x { slot with ty := .ty (.borrow true target) } := by
  intro hslot hslotTy hwrite
  cases hwrite with
  | @intro writeEnv _writeLv writeSlot _writeTy updatedTy hwriteSlot hupdate =>
      have hwriteSlotEq : writeSlot = slot := by
        have hslot' : env.slotAt x = some writeSlot := by
          simpa [LVal.base] using hwriteSlot
        exact Option.some.inj (hslot'.symm.trans hslot)
      subst writeSlot
      rw [hslotTy] at hupdate
      cases hupdate with
      | mutBorrow hinner =>
          refine ⟨writeEnv, ?_, ?_⟩
          · simpa [prependPath] using hinner
          · simp [LVal.base]

/-- A pure `UpdateAtPath` walk either stays on an owner-only selected path, or
hits a mutable-borrow hop.  In the hop branch the local rebuilt type is exactly
the original type; the environment change is the nested write below the hop. -/
theorem UpdateAtPath.pathSelect_or_hop {env result : Env} :
    ∀ {path : Path} {old updated : PartialTy} {rhsTy : Ty},
      UpdateAtPath env path old rhsTy result updated →
      (∃ leaf, PathSelect path old leaf) ∨
        ∃ (path' : Path) (target : LVal) (nested : Env),
          EnvWrite env (prependPath path' target) rhsTy nested ∧
          result = nested ∧ updated = old := by
  intro path old updated rhsTy hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun path old rhsTy result updated _ =>
      (∃ leaf, PathSelect path old leaf) ∨
        ∃ (path' : Path) (target : LVal) (nested : Env),
          EnvWrite env (prependPath path' target) rhsTy nested ∧
          result = nested ∧ updated = old)
    (motive_2 := fun _lv _rhsTy _result _ => True)
    (by
      intro old ty
      left
      exact ⟨_, PathSelect.here⟩)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
      rcases ih with ⟨leaf, hselect⟩ |
        ⟨path', target, nestedEnv, hwrite, hresult, hupdated⟩
      · left
        exact ⟨leaf, PathSelect.box hselect⟩
      · right
        exact ⟨path', target, nestedEnv, hwrite, hresult, by
          rw [hupdated]⟩)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
      rcases ih with ⟨leaf, hselect⟩ |
        ⟨path', target, nestedEnv, hwrite, hresult, hupdated⟩
      · left
        exact ⟨leaf, PathSelect.boxFull hselect⟩
      · right
        exact ⟨path', target, nestedEnv, hwrite, hresult, by
          rw [hupdated]
          simp [partialTyRebox]⟩)
    (by
      intro _env₂ path target _ty hwrite _ih
      right
      exact ⟨path, target, _env₂, hwrite, rfl, rfl⟩)
    (by
      intro _env₂ _lv _slot _ty _updatedTy _hslot _hupdate _ih
      trivial)
    hupdate

/-- The corresponding pure split for a complete environment write.  The hop
branch intentionally records the final outer update as `nested.update ... slot`;
turning that into pointwise equality requires proving that the nested write did
not change the outer holder slot. -/
theorem EnvWrite.select_or_hop_update_same
    {env env' : Env} {lhs : LVal} {rhsTy : Ty} :
    EnvWrite env lhs rhsTy env' →
    (∃ slot leaf,
      env.slotAt (LVal.base lhs) = some slot ∧
      PathSelect (LVal.path lhs) slot.ty leaf) ∨
      ∃ slot path' target nested,
        env.slotAt (LVal.base lhs) = some slot ∧
        EnvWrite env (prependPath path' target) rhsTy nested ∧
        env' = nested.update (LVal.base lhs) slot := by
  intro hwrite
  cases hwrite with
  | @intro result _lv slot _ty updatedTy hslot hupdate =>
      rcases UpdateAtPath.pathSelect_or_hop hupdate with
        ⟨leaf, hselect⟩ |
        ⟨path', target, nestedEnv, hnested, hresult, hupdated⟩
      · left
        exact ⟨slot, leaf, hslot, hselect⟩
      · right
        exact ⟨slot, path', target, nestedEnv, hslot, hnested, by
          simpa [hresult, hupdated]⟩

/-- The pointwise form of `EnvWrite.select_or_hop_update_same`, parameterized
by the missing typed fact that the nested hop write preserves the outer holder
slot.  This is the exact extra ingredient needed to recover the Round 16
pointwise branch under preservation hypotheses. -/
theorem EnvWrite.select_or_hop_of_nested_slot
    {env env' : Env} {lhs : LVal} {rhsTy : Ty}
    (hpreserve :
      ∀ {slot : EnvSlot} {path' : Path} {target : LVal} {nested : Env},
        env.slotAt (LVal.base lhs) = some slot →
        EnvWrite env (prependPath path' target) rhsTy nested →
        nested.slotAt (LVal.base lhs) = some slot) :
    EnvWrite env lhs rhsTy env' →
    (∃ slot leaf,
      env.slotAt (LVal.base lhs) = some slot ∧
      PathSelect (LVal.path lhs) slot.ty leaf) ∨
      ∃ path' target nested,
        EnvWrite env (prependPath path' target) rhsTy nested ∧
        (∀ y, env'.slotAt y = nested.slotAt y) := by
  intro hwrite
  rcases EnvWrite.select_or_hop_update_same hwrite with
    hselect | ⟨slot, path', target, nested, hslot, hnested, henv'⟩
  · exact Or.inl hselect
  · right
    refine ⟨path', target, nested, hnested, ?_⟩
    intro y
    rw [henv']
    by_cases hy : y = LVal.base lhs
    · subst hy
      simpa [Env.update, hpreserve hslot hnested]
    · simpa [Env.update, hy]

/-- Typed form of `UpdateAtPath.pathSelect_or_hop`.  The hop branch carries the
rebased lvalue typing and the concrete runtime-location equality needed to
replay the assignment step at the hop target. -/
theorem UpdateAtPath.pathSelect_or_hop_typed
    {store : ProgramStore} {env result : Env}
    (hsafe : SafeAbstraction store env)
    (hcbwf : ContainedBorrowsWellFormed env) :
    ∀ {path : Path} {old updated : PartialTy} {rhsTy : Ty},
      UpdateAtPath env path old rhsTy result updated →
      ∀ {wcur : LVal} {pt : PartialTy} {lf lfc : Lifetime},
        LValTyping env wcur old lfc →
        LValTyping env (prependPath path wcur) pt lf →
        (∀ {mutable : Bool} {u : LVal},
          PartialTyContains old (.borrow mutable u) →
          env ⊢ (LVal.base wcur) ↝ (.borrow mutable u)) →
        (∃ leaf, PathSelect path old leaf) ∨
          ∃ (path' : Path) (target : LVal) (nested : Env),
            EnvWrite env (prependPath path' target) rhsTy nested ∧
            result = nested ∧
            updated = old ∧
            env ⊢ (LVal.base wcur) ↝ (.borrow true target) ∧
            LValTyping env (prependPath path' target) pt lf ∧
              store.loc (prependPath path wcur) =
                store.loc (prependPath path' target) := by
  intro path old updated rhsTy hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun path old rhsTy result updated _ =>
      ∀ {wcur : LVal} {pt : PartialTy} {lf lfc : Lifetime},
        LValTyping env wcur old lfc →
        LValTyping env (prependPath path wcur) pt lf →
        (∀ {mutable : Bool} {u : LVal},
          PartialTyContains old (.borrow mutable u) →
          env ⊢ (LVal.base wcur) ↝ (.borrow mutable u)) →
        (∃ leaf, PathSelect path old leaf) ∨
          ∃ (path' : Path) (target : LVal) (nested : Env),
            EnvWrite env (prependPath path' target) rhsTy nested ∧
            result = nested ∧
            updated = old ∧
            env ⊢ (LVal.base wcur) ↝ (.borrow true target) ∧
            LValTyping env (prependPath path' target) pt lf ∧
            store.loc (prependPath path wcur) =
              store.loc (prependPath path' target))
    (motive_2 := fun _lv _rhsTy _result _ => True)
    (by
      intro _old _ty wcur pt lf lfc _hwcur _hlhs _hcontainsW
      left
      exact ⟨_, PathSelect.here⟩)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
      intro wcur pt lf lfc hwcur hlhs hcontainsW
      have hpathEq :
          prependPath _path wcur.deref = prependPath (() :: _path) wcur := by
        simp [prependPath_deref_comm, prependPath]
      have hlhs' :
          LValTyping env (prependPath _path wcur.deref) pt lf := by
        simpa [hpathEq] using hlhs
      rcases ih (LValTyping.box hwcur) hlhs'
          (by
            intro mutable u hcontains
            exact hcontainsW (PartialTyContains.box hcontains)) with
        hselect | hhop
      · rcases hselect with ⟨leaf, hselect⟩
        left
        exact ⟨leaf, PathSelect.box hselect⟩
      · rcases hhop with
          ⟨path', target, nested, hwrite, hresult, hupdated, hann, htyping,
            hloc⟩
        right
        refine ⟨path', target, nested, hwrite, hresult, ?_, hann, htyping,
          ?_⟩
        · rw [hupdated]
        · simpa [hpathEq] using hloc)
    (by
      intro _env₂ _path _inner _updatedInner _ty _hinner ih
      intro wcur pt lf lfc hwcur hlhs hcontainsW
      have hpathEq :
          prependPath _path wcur.deref = prependPath (() :: _path) wcur := by
        simp [prependPath_deref_comm, prependPath]
      have hlhs' :
          LValTyping env (prependPath _path wcur.deref) pt lf := by
        simpa [hpathEq] using hlhs
      rcases ih (LValTyping.boxFull hwcur) hlhs'
          (by
            intro mutable u hcontains
            exact hcontainsW (PartialTyContains.tyBox hcontains)) with
        hselect | hhop
      · rcases hselect with ⟨leaf, hselect⟩
        left
        exact ⟨leaf, PathSelect.boxFull hselect⟩
      · rcases hhop with
          ⟨path', target, nested, hwrite, hresult, hupdated, hann, htyping,
            hloc⟩
        right
        refine ⟨path', target, nested, hwrite, hresult, ?_, hann, htyping,
          ?_⟩
        · rw [hupdated]
          simp [partialTyRebox]
        · simpa [hpathEq] using hloc)
    (by
      intro env₂ path target rhsTy hwrite _ih
      intro wcur pt lf lfc hwcur hlhs hcontainsW
      have hpathEq :
          prependPath path wcur.deref = prependPath (() :: path) wcur := by
        simp [prependPath_deref_comm, prependPath]
      have hlhs' :
          LValTyping env (prependPath path wcur.deref) pt lf := by
        simpa [hpathEq] using hlhs
      have hrebased :
          LValTyping env (prependPath path target) pt lf :=
        LValTyping.rebase_hop hwcur path hlhs'
      rcases LValTyping.partialTyBorrowsWellFormedInSlot hcbwf hwcur
          PartialTyContains.here with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      have hlocBase :
          store.loc wcur.deref = store.loc target :=
        lvalTyping_deref_borrow_loc_eq_whenInitialized hsafe hwcur
          htargetTyping
      have hloc :
          store.loc (prependPath path wcur.deref) =
            store.loc (prependPath path target) :=
        ProgramStore.loc_prependPath_eq_of_loc_eq hlocBase path
      right
      exact ⟨path, target, env₂, hwrite, rfl, rfl,
        hcontainsW PartialTyContains.here, hrebased,
        by simpa [hpathEq] using hloc⟩)
    (by
      intro _env₂ _lv _slot _ty _updatedTy _hslot _hupdate _ih
      trivial)
    hupdate

/-- Typed form of the write split.  In the hop branch, the nested write is over
the same runtime location as the original lhs, and the reduced lhs has the same
static type as the original write target. -/
theorem EnvWrite.select_or_hop_typed
    {store : ProgramStore} {env env' : Env}
    (hsafe : SafeAbstraction store env)
    (hcbwf : ContainedBorrowsWellFormed env)
    {lhs : LVal} {oldTy : PartialTy} {targetLifetime : Lifetime}
    {rhsTy : Ty} :
    EnvWrite env lhs rhsTy env' →
    LValTyping env lhs oldTy targetLifetime →
    (∃ slot leaf,
      env.slotAt (LVal.base lhs) = some slot ∧
      PathSelect (LVal.path lhs) slot.ty leaf) ∨
      ∃ slot path' target nested,
        env.slotAt (LVal.base lhs) = some slot ∧
        EnvWrite env (prependPath path' target) rhsTy nested ∧
        env' = nested.update (LVal.base lhs) slot ∧
        env ⊢ (LVal.base lhs) ↝ (.borrow true target) ∧
        LValTyping env (prependPath path' target) oldTy targetLifetime ∧
        store.loc lhs = store.loc (prependPath path' target) := by
  intro hwrite hlhs
  cases hwrite with
  | @intro result _lv slot _ty updatedTy hslot hupdate =>
      rcases
          UpdateAtPath.pathSelect_or_hop_typed hsafe hcbwf hupdate
            (wcur := .var (LVal.base lhs))
            (pt := oldTy) (lf := targetLifetime)
            (LValTyping.var (by simpa [LVal.base] using hslot))
            (by
              rw [prependPath_path_base]
              exact hlhs)
            (by
              intro mutable u hcontains
              exact ⟨slot, by simpa [LVal.base] using hslot, hcontains⟩) with
        hselect | hhop
      · rcases hselect with ⟨leaf, hselect⟩
        left
        exact ⟨slot, leaf, by simpa [LVal.base] using hslot, hselect⟩
      · rcases hhop with
          ⟨path', target, nested, hnested, hresult, hupdated, hann, htyping,
            hloc⟩
        right
        refine ⟨slot, path', target, nested, by simpa [LVal.base] using hslot,
          hnested, ?_, by simpa [LVal.base] using hann, htyping, ?_⟩
        · subst hresult
          subst hupdated
          simp [LVal.base]
        · simpa [prependPath_path_base] using hloc

theorem TargetInitialized.transport_of_pointwise {env result : Env}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    ∀ {target : LVal},
      TargetInitialized result target →
      TargetInitialized env target := by
  intro target htarget
  rcases htarget with ⟨targetTy, targetLifetime, htyping⟩
  exact ⟨targetTy, targetLifetime,
    LValTyping.transport_of_pointwise (fun y => (heq y).symm) htyping⟩

theorem safeAbstractionWhenInitialized_transport_pointwise
    {store : ProgramStore} {env result : Env}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    SafeAbstraction store env →
    SafeAbstraction store result := by
  intro hsafe
  refine ⟨?domain, ?slots⟩
  · intro x
    constructor
    · intro hstoreDomain
      rcases (hsafe.1 x).mp hstoreDomain with ⟨slot, hslot⟩
      exact ⟨slot, by simpa [heq x] using hslot⟩
    · intro hresultDomain
      rcases hresultDomain with ⟨slot, hslot⟩
      exact (hsafe.1 x).mpr ⟨slot, by simpa [heq x] using hslot⟩
  · intro x slot hslot
    have hslotEnv : env.slotAt x = some slot := by
      simpa [heq x] using hslot
    rcases hsafe.2 x slot hslotEnv with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    exact ⟨oldValue, hstoreSlot,
      validPartialValueWhenInitialized_transport_env
        (TargetInitialized.transport_of_pointwise heq) hvalidOld⟩

theorem TerminalStateSafe.transport_env_pointwise
    {store : ProgramStore} {value : Value} {env result : Env} {ty : Ty}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    TerminalStateSafe store value env ty →
    TerminalStateSafe store value result ty := by
  intro hterminal
  rcases hterminal with ⟨hvalidRuntime, hsafe, hvalidValue⟩
  exact ⟨hvalidRuntime,
    safeAbstractionWhenInitialized_transport_pointwise heq hsafe,
    validPartialValueWhenInitialized_transport_env
      (TargetInitialized.transport_of_pointwise heq) hvalidValue⟩

theorem lvalTyping_box_ownerChainPrefix_whenInitialized
    {store : ProgramStore} {env : Env}
    (hsafe : SafeAbstraction store env) :
    ∀ {lv : LVal} {inner : PartialTy} {lifetime : Lifetime},
      LValTyping env lv (.box inner) lifetime →
      ∃ envSlot rootSlot leaf leafSlot,
        env.slotAt (LVal.base lv) = some envSlot ∧
        store.slotAt (VariableProjection (LVal.base lv)) = some rootSlot ∧
        rootSlot.lifetime = envSlot.lifetime ∧
        store.loc lv = some leaf ∧
        store.slotAt leaf = some leafSlot ∧
        ValidPartialValueWhenInitialized env store rootSlot.value envSlot.ty ∧
        ValidPartialValueWhenInitialized env store leafSlot.value (.box inner) ∧
        OwnerChainPrefix store (VariableProjection (LVal.base lv))
          rootSlot.value (LVal.path lv) leaf := by
  intro lv
  induction lv with
  | var x =>
      intro inner lifetime htyping
      rcases LValTyping.var_inv htyping with
        ⟨envSlot, hslot, htyEq, _hlifetimeEq⟩
      rcases hsafe.2 x envSlot hslot with ⟨rootValue, hrootSlot, hrootValid⟩
      have hrootValidBox :
          ValidPartialValueWhenInitialized env store rootValue (.box inner) := by
        simpa [← htyEq] using hrootValid
      refine ⟨envSlot, { value := rootValue, lifetime := envSlot.lifetime },
        VariableProjection x, { value := rootValue, lifetime := envSlot.lifetime },
        hslot, hrootSlot, rfl, ?_, hrootSlot, ?_, ?_, ?_⟩
      · simp [ProgramStore.loc, VariableProjection]
      · simpa using hrootValid
      · simpa using hrootValidBox
      · exact Or.inl ⟨by simp [LVal.path], rfl⟩
  | deref source ih =>
      intro inner lifetime htyping
      cases htyping with
      | box hsource =>
      rcases ih hsource with
        ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
          hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
          hrootValid, hsourceValid, hprefix⟩
      rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
      cases hsourceValid with
      | box hownerSlot hinnerValid =>
          rename_i ownerLocation ownerSlot
          have hderefLoc :
              store.loc (.deref source) = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hsourceOwner :
              (StoreSlot.mk
                (.value (.ref { location := ownerLocation, owner := true }))
                sourceSlotLifetime).value =
              .value (.ref { location := ownerLocation, owner := true }) := rfl
          have hprefixExtended :
              ∃ k,
                OwnerChainAt store rootSlot.value (LVal.path source ++ [()])
                  ownerLocation ∧
                OwnsChain store (VariableProjection (LVal.base source)) k
                  ownerLocation ∧
                k = (LVal.path source ++ [()]).length :=
            OwnerChainPrefix.extend hprefix
              (by
                intro hpathNil
                have hlocRoot :=
                  ProgramStore.loc_eq_var_of_path_nil
                    (store := store) (lv := source) hpathNil
                have hlocEq :
                    sourceLocation = VariableProjection (LVal.base source) :=
                  Option.some.inj (hsourceLoc.symm.trans hlocRoot)
                subst hlocEq
                have hslotEq :
                    StoreSlot.mk
                        (.value (.ref { location := ownerLocation, owner := true }))
                        sourceSlotLifetime = rootSlot :=
                  Option.some.inj (hsourceSlot.symm.trans hrootSlot)
                exact congrArg StoreSlot.value hslotEq.symm)
              hsourceSlot hsourceOwner
          refine ⟨envSlot, rootSlot, ownerLocation, ownerSlot,
            by simpa [LVal.base] using henvBase,
            by simpa [LVal.base] using hrootSlot,
            hrootLifetime, hderefLoc, hownerSlot,
            hrootValid, hinnerValid, ?_⟩
          rcases hprefixExtended with ⟨k, hchain, howns, hlen⟩
          exact Or.inr ⟨k, by simpa [LVal.path] using hchain,
            by simpa [LVal.base] using howns,
            by simpa [LVal.path] using hlen⟩

theorem LValTyping.box_pathSelect {env : Env} :
    ∀ {lv : LVal} {inner : PartialTy} {lifetime : Lifetime}
      {slot : EnvSlot},
      LValTyping env lv (.box inner) lifetime →
      env.slotAt (LVal.base lv) = some slot →
      PathSelect (LVal.path lv) slot.ty (.box inner) := by
  intro lv
  induction lv with
  | var x =>
      intro inner lifetime slot htyping hslot
      rcases LValTyping.var_inv htyping with
        ⟨envSlot, henvSlot, htyEq, _hlifetimeEq⟩
      have hslotEq : slot = envSlot :=
        Option.some.inj (hslot.symm.trans henvSlot)
      subst hslotEq
      rw [← htyEq]
      exact PathSelect.here
  | deref source ih =>
      intro inner lifetime slot htyping hslot
      cases htyping with
      | box hsource =>
          have hsourceSelect :
              PathSelect (LVal.path source) slot.ty (.box (.box inner)) :=
            ih hsource (by simpa [LVal.base] using hslot)
          simpa [LVal.path] using PathSelect.snoc_box hsourceSelect

/-- A full-box lvalue is either reached through an owner-only selected path
from its base slot, or its first non-owner hop is an explicit mutable-borrow
descent.  This is the structural split needed by dereference assignment: the
left branch is handled by the pure `PathSelect` helper, while the right branch
is the remaining re-rooting case. -/
theorem LValTyping.tyBox_pathSelect_or_borrow {env : Env} :
    ∀ {lv : LVal} {inner : Ty} {lifetime : Lifetime}
      {slot : EnvSlot},
      LValTyping env lv (.ty (.box inner)) lifetime →
      env.slotAt (LVal.base lv) = some slot →
      PathSelect (LVal.path lv) slot.ty (.ty (.box inner)) ∨
        ∃ (pref : Path) (source target : LVal) (mutable : Bool)
          (borrowLifetime targetLifetime : Lifetime) (targetTy : Ty),
          lv = prependPath pref source.deref ∧
          LValTyping env source (.ty (.borrow mutable target))
            borrowLifetime ∧
          LValTyping env target (.ty targetTy) targetLifetime ∧
          LValTyping env (prependPath pref target) (.ty (.box inner))
            lifetime := by
  intro lv
  induction lv with
  | var x =>
      intro inner lifetime slot htyping hslot
      rcases LValTyping.var_inv htyping with
        ⟨envSlot, henvSlot, htyEq, _hlifetimeEq⟩
      have hslotEq : slot = envSlot :=
        Option.some.inj (hslot.symm.trans henvSlot)
      subst hslotEq
      left
      rw [← htyEq]
      exact PathSelect.here
  | deref source ih =>
      intro inner lifetime slot htyping hslot
      cases htyping with
      | box hsource =>
          have hsourceSelect :
              PathSelect (LVal.path source) slot.ty
                (.box (.ty (.box inner))) :=
            LValTyping.box_pathSelect hsource
              (by simpa [LVal.base] using hslot)
          left
          simpa [LVal.path] using PathSelect.snoc_box hsourceSelect
      | boxFull hsource =>
          rcases ih hsource (by simpa [LVal.base] using hslot) with
            hselect | hhop
          · left
            simpa [LVal.path] using PathSelect.snoc_boxFull hselect
          · rcases hhop with
              ⟨pref, hopSource, target, mutable, borrowLifetime,
                targetLifetime, targetTy, hsourceEq, hhopTyping,
                htargetTyping, hretypedTarget⟩
            right
            refine ⟨() :: pref, hopSource, target, mutable,
              borrowLifetime, targetLifetime, targetTy, ?_, hhopTyping,
              htargetTyping, ?_⟩
            · rw [hsourceEq]
              rfl
            · simpa [prependPath] using LValTyping.boxFull hretypedTarget
      | borrow hsource htarget =>
          right
          exact ⟨[], source, _, _, _, _, .box inner, rfl,
            hsource, htarget, by simpa [prependPath] using htarget⟩

theorem EnvWrite.deref_box_update_eq {env env' : Env} {source : LVal}
    {oldTy : PartialTy} {targetLifetime : Lifetime} {rhsTy : Ty} :
    LValTyping env source (.box oldTy) targetLifetime →
    EnvWrite env source.deref rhsTy env' →
    ∃ slot updatedTy,
      env.slotAt (LVal.base source) = some slot ∧
      UpdateAtPath env (LVal.path source.deref) slot.ty rhsTy env updatedTy ∧
      env' = env.update (LVal.base source) { slot with ty := updatedTy } := by
  intro hsource hwrite
  cases hwrite with
  | @intro writeEnv _writeLv writeSlot _writeTy updatedTy hslot hupdate =>
      have hslotBase : env.slotAt (LVal.base source) = some writeSlot := by
        simpa [LVal.base] using hslot
      have hselectSource :
          PathSelect (LVal.path source) writeSlot.ty (.box oldTy) :=
        LValTyping.box_pathSelect hsource hslotBase
      have hselectDeref :
          PathSelect (LVal.path source.deref) writeSlot.ty oldTy := by
        simpa [LVal.path] using PathSelect.snoc_box hselectSource
      have henvEq :
          writeEnv = env :=
        PathSelect.update_env_eq hselectDeref (by
          simpa [LVal.base] using hupdate)
      subst henvEq
      exact ⟨writeSlot, updatedTy, hslotBase, by simpa [LVal.base] using hupdate,
        by simp [LVal.base]⟩

theorem EnvWrite.deref_box_result_contains {env env' : Env} {source : LVal}
    {oldTy : PartialTy} {targetLifetime : Lifetime} {rhsTy : Ty} :
    LValTyping env source (.box oldTy) targetLifetime →
    EnvWrite env source.deref rhsTy env' →
    ∃ slot updatedTy,
      env.slotAt (LVal.base source) = some slot ∧
      UpdateAtPath env (LVal.path source.deref) slot.ty rhsTy env updatedTy ∧
      env' = env.update (LVal.base source) { slot with ty := updatedTy } ∧
      ∀ {mutable : Bool} {target : LVal},
        PartialTyContains (.ty rhsTy) (.borrow mutable target) →
        env' ⊢ (LVal.base source) ↝ (.borrow mutable target) := by
  intro hsource hwrite
  rcases EnvWrite.deref_box_update_eq hsource hwrite with
    ⟨slot, updatedTy, hslot, hupdate, henv'⟩
  have hselectSource :
      PathSelect (LVal.path source) slot.ty (.box oldTy) :=
    LValTyping.box_pathSelect hsource hslot
  have hselectDeref :
      PathSelect (LVal.path source.deref) slot.ty oldTy := by
    simpa [LVal.path] using PathSelect.snoc_box hselectSource
  refine ⟨slot, updatedTy, hslot, hupdate, henv', ?_⟩
  intro mutable target hcontains
  refine ⟨{ slot with ty := updatedTy }, ?_, ?_⟩
  · rw [henv']
    simp [Env.update]
  · exact PathSelect.update_contains_rhs hselectDeref hupdate hcontains

theorem EnvWrite.deref_boxFull_update_eq_of_select {env env' : Env}
    {source : LVal} {oldTy : Ty} {rhsTy : Ty} {slot : EnvSlot} :
    env.slotAt (LVal.base source) = some slot →
    PathSelect (LVal.path source) slot.ty (.ty (.box oldTy)) →
    EnvWrite env source.deref rhsTy env' →
    ∃ updatedTy,
      UpdateAtPath env (LVal.path source.deref) slot.ty rhsTy env updatedTy ∧
      env' = env.update (LVal.base source) { slot with ty := updatedTy } := by
  intro hslot hselectSource hwrite
  cases hwrite with
  | @intro writeEnv _writeLv writeSlot _writeTy updatedTy hwriteSlot hupdate =>
      have hslotBase : env.slotAt (LVal.base source) = some writeSlot := by
        simpa [LVal.base] using hwriteSlot
      have hwriteSlotEq : writeSlot = slot :=
        Option.some.inj (hslotBase.symm.trans hslot)
      subst writeSlot
      have hselectDeref :
          PathSelect (LVal.path source.deref) slot.ty (.ty oldTy) := by
        simpa [LVal.path] using PathSelect.snoc_boxFull hselectSource
      have henvEq :
          writeEnv = env :=
        PathSelect.update_env_eq hselectDeref (by
          simpa [LVal.base] using hupdate)
      subst henvEq
      exact ⟨updatedTy, by simpa [LVal.base] using hupdate,
        by simp [LVal.base]⟩

theorem EnvWrite.deref_boxFull_result_contains_of_select {env env' : Env}
    {source : LVal} {oldTy : Ty} {rhsTy : Ty} {slot : EnvSlot} :
    env.slotAt (LVal.base source) = some slot →
    PathSelect (LVal.path source) slot.ty (.ty (.box oldTy)) →
    EnvWrite env source.deref rhsTy env' →
    ∃ updatedTy,
      UpdateAtPath env (LVal.path source.deref) slot.ty rhsTy env updatedTy ∧
      env' = env.update (LVal.base source) { slot with ty := updatedTy } ∧
      ∀ {mutable : Bool} {target : LVal},
        PartialTyContains (.ty rhsTy) (.borrow mutable target) →
        env' ⊢ (LVal.base source) ↝ (.borrow mutable target) := by
  intro hslot hselectSource hwrite
  rcases EnvWrite.deref_boxFull_update_eq_of_select hslot hselectSource
      hwrite with
    ⟨updatedTy, hupdate, henv'⟩
  have hselectDeref :
      PathSelect (LVal.path source.deref) slot.ty (.ty oldTy) := by
    simpa [LVal.path] using PathSelect.snoc_boxFull hselectSource
  refine ⟨updatedTy, hupdate, henv', ?_⟩
  intro mutable target hcontains
  refine ⟨{ slot with ty := updatedTy }, ?_, ?_⟩
  · rw [henv']
    simp [Env.update]
  · exact PathSelect.update_contains_rhs hselectDeref hupdate hcontains

theorem lvalTyping_tyBox_ownerChainPrefix_whenInitialized_of_strike
    {store : ProgramStore} {env : Env}
    (hsafe : SafeAbstraction store env) :
    ∀ {lv : LVal} {inner : Ty} {lifetime : Lifetime}
      {slot : EnvSlot} {struck : PartialTy} {suffix : Path},
      LValTyping env lv (.ty (.box inner)) lifetime →
      env.slotAt (LVal.base lv) = some slot →
      Strike (LVal.path lv ++ (() :: suffix)) slot.ty struck →
      ∃ envSlot rootSlot leaf leafSlot,
        env.slotAt (LVal.base lv) = some envSlot ∧
        store.slotAt (VariableProjection (LVal.base lv)) = some rootSlot ∧
        rootSlot.lifetime = envSlot.lifetime ∧
        store.loc lv = some leaf ∧
        store.slotAt leaf = some leafSlot ∧
        ValidPartialValueWhenInitialized env store rootSlot.value envSlot.ty ∧
        ValidPartialValueWhenInitialized env store leafSlot.value
          (.ty (.box inner)) ∧
        OwnerChainPrefix store (VariableProjection (LVal.base lv))
          rootSlot.value (LVal.path lv) leaf := by
  intro lv
  induction lv with
  | var x =>
      intro inner lifetime slot struck suffix htyping hbase _hstrike
      rcases LValTyping.var_inv htyping with
        ⟨envSlot, hslot, htyEq, _hlifetimeEq⟩
      rcases hsafe.2 x envSlot hslot with ⟨rootValue, hrootSlot, hrootValid⟩
      have hrootValidBox :
          ValidPartialValueWhenInitialized env store rootValue (.ty (.box inner)) := by
        simpa [← htyEq] using hrootValid
      refine ⟨envSlot, { value := rootValue, lifetime := envSlot.lifetime },
        VariableProjection x, { value := rootValue, lifetime := envSlot.lifetime },
        hslot, hrootSlot, rfl, ?_, hrootSlot, ?_, ?_, ?_⟩
      · simp [ProgramStore.loc, VariableProjection]
      · simpa using hrootValid
      · simpa using hrootValidBox
      · exact Or.inl ⟨by simp [LVal.path], rfl⟩
  | deref source ih =>
      intro inner lifetime slot struck suffix htyping hbase hstrike
      cases htyping with
      | box hsourceBox =>
          rcases lvalTyping_box_ownerChainPrefix_whenInitialized hsafe
              hsourceBox with
            ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
              hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
              hrootValid, hsourceValid, hprefix⟩
          rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
          cases hsourceValid with
          | box hownerSlot hinnerValid =>
              rename_i ownerLocation ownerSlot
              have hderefLoc :
                  store.loc (.deref source) = some ownerLocation := by
                simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
              have hsourceOwner :
                  (StoreSlot.mk
                    (.value (.ref { location := ownerLocation, owner := true }))
                    sourceSlotLifetime).value =
                  .value (.ref { location := ownerLocation, owner := true }) := rfl
              have hprefixExtended :
                  ∃ k,
                    OwnerChainAt store rootSlot.value (LVal.path source ++ [()])
                      ownerLocation ∧
                    OwnsChain store (VariableProjection (LVal.base source)) k
                      ownerLocation ∧
                    k = (LVal.path source ++ [()]).length :=
                OwnerChainPrefix.extend hprefix
                  (by
                    intro hpathNil
                    have hlocRoot :=
                      ProgramStore.loc_eq_var_of_path_nil
                        (store := store) (lv := source) hpathNil
                    have hlocEq :
                        sourceLocation = VariableProjection (LVal.base source) :=
                      Option.some.inj (hsourceLoc.symm.trans hlocRoot)
                    subst hlocEq
                    have hslotEq :
                        StoreSlot.mk
                            (.value (.ref { location := ownerLocation, owner := true }))
                            sourceSlotLifetime = rootSlot :=
                      Option.some.inj (hsourceSlot.symm.trans hrootSlot)
                    exact congrArg StoreSlot.value hslotEq.symm)
                  hsourceSlot hsourceOwner
              refine ⟨envSlot, rootSlot, ownerLocation, ownerSlot,
                by simpa [LVal.base] using henvBase,
                by simpa [LVal.base] using hrootSlot,
                hrootLifetime, hderefLoc, hownerSlot,
                hrootValid, hinnerValid, ?_⟩
              rcases hprefixExtended with ⟨k, hchain, howns, hlen⟩
              exact Or.inr ⟨k, by simpa [LVal.path] using hchain,
                by simpa [LVal.base] using howns,
                by simpa [LVal.path] using hlen⟩
      | boxFull hsourceFull =>
          have hstrikeSource :
              Strike (LVal.path source ++ (() :: (() :: suffix))) slot.ty struck := by
            change Strike ((LVal.path source ++ [()]) ++ (() :: suffix))
              slot.ty struck at hstrike
            simpa [List.append_assoc] using hstrike
          rcases ih hsourceFull (by simpa [LVal.base] using hbase)
              hstrikeSource with
            ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
              hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
              hrootValid, hsourceValid, hprefix⟩
          rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
          cases hsourceValid with
          | boxFull hownerSlot hinnerValid =>
              rename_i ownerLocation ownerSlot
              have hderefLoc :
                  store.loc (.deref source) = some ownerLocation := by
                simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
              have hsourceOwner :
                  (StoreSlot.mk
                    (.value (.ref { location := ownerLocation, owner := true }))
                    sourceSlotLifetime).value =
                  .value (.ref { location := ownerLocation, owner := true }) := rfl
              have hprefixExtended :
                  ∃ k,
                    OwnerChainAt store rootSlot.value (LVal.path source ++ [()])
                      ownerLocation ∧
                    OwnsChain store (VariableProjection (LVal.base source)) k
                      ownerLocation ∧
                    k = (LVal.path source ++ [()]).length :=
                OwnerChainPrefix.extend hprefix
                  (by
                    intro hpathNil
                    have hlocRoot :=
                      ProgramStore.loc_eq_var_of_path_nil
                        (store := store) (lv := source) hpathNil
                    have hlocEq :
                        sourceLocation = VariableProjection (LVal.base source) :=
                      Option.some.inj (hsourceLoc.symm.trans hlocRoot)
                    subst hlocEq
                    have hslotEq :
                        StoreSlot.mk
                            (.value (.ref { location := ownerLocation, owner := true }))
                            sourceSlotLifetime = rootSlot :=
                      Option.some.inj (hsourceSlot.symm.trans hrootSlot)
                    exact congrArg StoreSlot.value hslotEq.symm)
                  hsourceSlot hsourceOwner
              refine ⟨envSlot, rootSlot, ownerLocation, ownerSlot,
                by simpa [LVal.base] using henvBase,
                by simpa [LVal.base] using hrootSlot,
                hrootLifetime, hderefLoc, hownerSlot,
                hrootValid, hinnerValid, ?_⟩
              rcases hprefixExtended with ⟨k, hchain, howns, hlen⟩
              exact Or.inr ⟨k, by simpa [LVal.path] using hchain,
                by simpa [LVal.base] using howns,
                by simpa [LVal.path] using hlen⟩
      | borrow hsourceBorrow htarget =>
          have hstrikeSource :
              Strike (LVal.path source ++ (() :: (() :: suffix))) slot.ty struck := by
            change Strike ((LVal.path source ++ [()]) ++ (() :: suffix))
              slot.ty struck at hstrike
            simpa [List.append_assoc] using hstrike
          rcases LValTyping.strike_suffix hsourceBorrow
              (by simpa [LVal.base] using hbase) hstrikeSource with
            ⟨badStruck, hbad⟩
          cases badStruck <;> simp [Strike] at hbad

/-- **Strike/write alignment.**  Updating the owner-chain leaf to `undef`
realizes the struck type: the box spine survives slot-for-slot (the chain
cannot revisit its leaf under store validity), and the struck subtree's
`undef` is witnessed by the written leaf.  The conclusion is stated against
an arbitrary result environment: the struck spine mentions no borrows. -/
theorem validPartialValueWhenInitialized_strike_write
    {env moved : Env} {store : ProgramStore} {rootLoc : Location}
    (hvalidStore : ValidStore store)
    (hrootUnowned : ¬ ProgramStore.Owns store rootLoc)
    {leafLoc : Location} {leafSlot : StoreSlot} {k : Nat}
    (hleafChain : OwnsChain store rootLoc k leafLoc)
    (hleafSlot : store.slotAt leafLoc = some leafSlot) :
    ∀ {path : Path} {source struck : PartialTy} {value : PartialValue}
      {cur : Location} {j : Nat},
      Strike path source struck →
      ValidPartialValueWhenInitialized env store value source →
      OwnerChainAt store value path leafLoc →
      (∃ lifetime, store.slotAt cur = some ⟨value, lifetime⟩) →
      OwnsChain store rootLoc j cur →
      k = j + path.length →
      ValidPartialValueWhenInitialized moved
        (store.update leafLoc { leafSlot with value := .undef })
        value struck := by
  intro path
  induction path with
  | nil =>
      intro source struck value cur j _hstrike _hvalid hchain
      cases hchain
  | cons head rest ih =>
      intro source struck value cur j hstrike hvalid hchain hcurSlot hcurChain
        hlen
      cases hchain with
      | here =>
          -- The write happens at this owner's target: the strike leaf.
          cases source with
          | ty tySource =>
              cases tySource <;> cases struck <;> simp [Strike] at hstrike
              rename_i T struckInner
              cases struckInner <;> simp [Strike] at hstrike
              subst hstrike
              cases hvalid with
              | boxFull hslot hinner =>
                  refine ValidPartialValueWhenInitialized.box
                    (slot := { leafSlot with value := .undef }) ?_
                    ValidPartialValueWhenInitialized.undef
                  simp [ProgramStore.update]
          | box innerTy =>
              cases struck <;> simp [Strike] at hstrike
              rename_i struckInner
              cases innerTy <;> cases struckInner <;>
                simp [Strike] at hstrike
              subst hstrike
              cases hvalid with
              | box hslot hinner =>
                  refine ValidPartialValueWhenInitialized.box
                    (slot := { leafSlot with value := .undef }) ?_
                    ValidPartialValueWhenInitialized.undef
                  simp [ProgramStore.update]
          | undef shape =>
              cases struck <;> simp [Strike] at hstrike
      | there hslotNext hchainNext =>
          rename_i location slot rest'
          -- This spine slot is strictly above the leaf and survives.
          rcases hcurSlot with ⟨curLifetime, hcurSlotEq⟩
          have hownsNext : ProgramStore.OwnsAt store location cur :=
            ⟨curLifetime, by simpa [owningRef] using hcurSlotEq⟩
          have hnextChain : OwnsChain store rootLoc (j + 1) location :=
            OwnsChain.succ hcurChain hownsNext
          have hne : location ≠ leafLoc := by
            intro hEq
            subst hEq
            have hlenEq :=
              ownsChain_unique_length hvalidStore hrootUnowned
                hleafChain hnextChain
            simp only [List.length_cons] at hlen
            omega
          have hslotNext' :
              (store.update leafLoc { leafSlot with value := .undef }).slotAt
                location = some slot := by
            simpa [ProgramStore.update, hne] using hslotNext
          have hnextCurSlot :
              ∃ lifetime, store.slotAt location = some ⟨slot.value, lifetime⟩ :=
            ⟨slot.lifetime, by simpa using hslotNext⟩
          have hnextLen : k = (j + 1) + (() :: rest').length := by
            simp only [List.length_cons] at hlen ⊢
            omega
          cases source with
          | ty tySource =>
              cases tySource <;> cases struck <;> simp [Strike] at hstrike
              cases hvalid with
              | boxFull hslot hinner =>
                  rename_i slotV
                  have hslotEq : slotV = slot :=
                    Option.some.inj (hslot.symm.trans hslotNext)
                  subst hslotEq
                  exact ValidPartialValueWhenInitialized.box hslotNext'
                    (ih hstrike hinner hchainNext hnextCurSlot hnextChain
                      hnextLen)
          | box innerTy =>
              cases struck <;> simp [Strike] at hstrike
              cases hvalid with
              | box hslot hinner =>
                  rename_i slotV
                  have hslotEq : slotV = slot :=
                    Option.some.inj (hslot.symm.trans hslotNext)
                  subst hslotEq
                  exact ValidPartialValueWhenInitialized.box hslotNext'
                    (ih hstrike hinner hchainNext hnextCurSlot hnextChain
                      hnextLen)
          | undef shape =>
              cases struck <;> simp [Strike] at hstrike

theorem validPartialValueWhenInitialized_updateAtPath_write
    {env resultEnv : Env} {store : ProgramStore} {rootLoc : Location}
    (hvalidStore : ValidStore store)
    (hrootUnowned : ¬ ProgramStore.Owns store rootLoc)
    {leafLoc : Location} {leafSlot : StoreSlot} {k : Nat}
    (hleafChain : OwnsChain store rootLoc k leafLoc)
    (hleafSlot : store.slotAt leafLoc = some leafSlot)
    {rhsTy : Ty} {rhsValue : Value} :
    ∀ {path : Path} {source updated : PartialTy} {value : PartialValue}
      {cur : Location} {j : Nat},
      UpdateAtPath env path source rhsTy env updated →
      ValidPartialValueWhenInitialized env store value source →
      OwnerChainAt store value path leafLoc →
      (∃ lifetime, store.slotAt cur = some ⟨value, lifetime⟩) →
      OwnsChain store rootLoc j cur →
      k = j + path.length →
      ValidPartialValueWhenInitialized resultEnv
        (store.update leafLoc { leafSlot with value := .value rhsValue })
        (.value rhsValue) (.ty rhsTy) →
      ValidPartialValueWhenInitialized resultEnv
        (store.update leafLoc { leafSlot with value := .value rhsValue })
        value updated := by
  intro path
  induction path with
  | nil =>
      intro source updated value cur j _hupdate _hvalid hchain
      cases hchain
  | cons head rest ih =>
      intro source updated value cur j hupdate hvalid hchain hcurSlot
        hcurChain hlen hvalidRhs
      cases hchain with
      | here =>
          cases source with
          | ty tySource =>
              cases tySource <;> cases hupdate
              case borrow.mutBorrow hwrite =>
                cases hvalid
              case box.boxFull hinnerUpdate =>
                cases hinnerUpdate
                cases hvalid with
                | boxFull hslot hinner =>
                    refine ValidPartialValueWhenInitialized.boxFull
                      (slot := { leafSlot with value := .value rhsValue }) ?_
                      hvalidRhs
                    simp [ProgramStore.update]
          | box innerTy =>
              cases hupdate
              case box hinnerUpdate =>
                cases hinnerUpdate
                cases hvalid with
                | box hslot hinner =>
                    refine ValidPartialValueWhenInitialized.box
                      (slot := { leafSlot with value := .value rhsValue }) ?_
                      hvalidRhs
                    simp [ProgramStore.update]
          | undef shape =>
              cases hupdate
      | there hslotNext hchainNext =>
          rename_i location slot rest'
          rcases hcurSlot with ⟨curLifetime, hcurSlotEq⟩
          have hownsNext : ProgramStore.OwnsAt store location cur :=
            ⟨curLifetime, by simpa [owningRef] using hcurSlotEq⟩
          have hnextChain : OwnsChain store rootLoc (j + 1) location :=
            OwnsChain.succ hcurChain hownsNext
          have hne : location ≠ leafLoc := by
            intro hEq
            subst hEq
            have hlenEq :=
              ownsChain_unique_length hvalidStore hrootUnowned
                hleafChain hnextChain
            simp only [List.length_cons] at hlen
            omega
          have hslotNext' :
              (store.update leafLoc { leafSlot with value := .value rhsValue }).slotAt
                location = some slot := by
            simpa [ProgramStore.update, hne] using hslotNext
          have hnextCurSlot :
              ∃ lifetime, store.slotAt location = some ⟨slot.value, lifetime⟩ :=
            ⟨slot.lifetime, by simpa using hslotNext⟩
          have hnextLen : k = (j + 1) + (() :: rest').length := by
            simp only [List.length_cons] at hlen ⊢
            omega
          cases source with
          | ty tySource =>
              cases tySource <;> cases hupdate
              case borrow.mutBorrow hwrite =>
                cases hvalid
              case box.boxFull hinnerUpdate =>
                rename_i innerTy updatedInner
                cases hvalid with
                | @boxFull ownerLocation ownerSlot ty hslotOwner hinner =>
                    have hslotEq : ownerSlot = slot :=
                      Option.some.inj (hslotOwner.symm.trans hslotNext)
                    subst ownerSlot
                    have hinnerFinal :
                        ValidPartialValueWhenInitialized resultEnv
                          (store.update leafLoc
                            { leafSlot with value := .value rhsValue })
                          slot.value updatedInner :=
                      ih hinnerUpdate hinner hchainNext hnextCurSlot
                        hnextChain hnextLen hvalidRhs
                    cases updatedInner with
                    | ty updatedTy =>
                        exact ValidPartialValueWhenInitialized.boxFull
                          hslotNext' hinnerFinal
                    | box updatedInner =>
                        exact ValidPartialValueWhenInitialized.box
                          hslotNext' hinnerFinal
                    | undef updatedTy =>
                        exact ValidPartialValueWhenInitialized.box
                          hslotNext' hinnerFinal
          | box innerTy =>
              cases hupdate
              case box.box hinnerUpdate =>
                cases hvalid with
                | box hslot hinner =>
                    rename_i slotV
                    have hslotEq : slotV = slot :=
                      Option.some.inj (hslot.symm.trans hslotNext)
                    subst hslotEq
                    exact ValidPartialValueWhenInitialized.box hslotNext'
                      (ih hinnerUpdate hinner hchainNext hnextCurSlot
                        hnextChain hnextLen hvalidRhs)
          | undef shape =>
              cases hupdate

/-- Chains from unowned roots to a common target agree on root and length:
backward owner steps are deterministic. -/
theorem ownsChain_unique {store : ProgramStore} {root₁ root₂ : Location}
    (hvalidStore : ValidStore store)
    (hroot₁ : ¬ ProgramStore.Owns store root₁)
    (hroot₂ : ¬ ProgramStore.Owns store root₂) :
    ∀ {n₁ n₂ : Nat} {target : Location},
      OwnsChain store root₁ n₁ target →
      OwnsChain store root₂ n₂ target →
      root₁ = root₂ ∧ n₁ = n₂ := by
  intro n₁
  induction n₁ with
  | zero =>
      intro n₂ target h₁ h₂
      cases h₁
      cases h₂ with
      | zero => exact ⟨rfl, rfl⟩
      | succ _ howns => exact absurd ⟨_, howns⟩ hroot₁
  | succ n ih =>
      intro n₂ target h₁ h₂
      cases h₁ with
      | succ hchain₁ howns₁ =>
          cases h₂ with
          | zero => exact absurd ⟨_, howns₁⟩ hroot₂
          | succ hchain₂ howns₂ =>
              have hmid := hvalidStore _ _ _ howns₁ howns₂
              subst hmid
              rcases ih hchain₁ hchain₂ with ⟨hroot, hlen⟩
              exact ⟨hroot, by rw [hlen]⟩

/-- An owner reach from a stored value is an owner chain from its storage. -/
theorem ownerReaches_ownsChain_stored {store : ProgramStore} :
    ∀ {value : PartialValue} {partialTy : PartialTy} {ℓ : Location}
      {storage : Location} {lifetime : Lifetime},
      store.slotAt storage = some ⟨value, lifetime⟩ →
      RuntimeFrame.OwnerReaches store value partialTy ℓ →
      ∃ n, OwnsChain store storage (n + 1) ℓ := by
  intro value partialTy ℓ storage lifetime hstored hreach
  induction hreach generalizing storage lifetime with
  | undefOf _hskel _hstrength _howner ih =>
      exact ih hstored
  | boxHere hslot =>
      exact ⟨0, OwnsChain.succ OwnsChain.zero
        ⟨lifetime, by simpa [owningRef] using hstored⟩⟩
  | boxInner hslot _hinner ih =>
      rename_i location slot inner ℓ'
      rcases ih (storage := location) (lifetime := slot.lifetime)
          (by simpa using hslot) with ⟨n, hchain⟩
      refine ⟨n + 1, ?_⟩
      have hfirst : OwnsChain store storage 1 location :=
        OwnsChain.succ OwnsChain.zero
          ⟨lifetime, by simpa [owningRef] using hstored⟩
      have := ownsChain_append hfirst hchain
      simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using this
  | boxFullHere hslot =>
      exact ⟨0, OwnsChain.succ OwnsChain.zero
        ⟨lifetime, by simpa [owningRef] using hstored⟩⟩
  | boxFullInner hslot _hinner ih =>
      rename_i location slot ty ℓ'
      rcases ih (storage := location) (lifetime := slot.lifetime)
          (by simpa using hslot) with ⟨n, hchain⟩
      refine ⟨n + 1, ?_⟩
      have hfirst : OwnsChain store storage 1 location :=
        OwnsChain.succ OwnsChain.zero
          ⟨lifetime, by simpa [owningRef] using hstored⟩
      have := ownsChain_append hfirst hchain
      simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using this

/-- Sibling exclusion: a value stored at a different unowned root never
owner-reaches the leaf of the moved chain. -/
theorem ownerReaches_stored_ne_chain_leaf {store : ProgramStore}
    {rootLoc storage : Location} {k : Nat} {leafLoc : Location}
    (hvalidStore : ValidStore store)
    (hrootUnowned : ¬ ProgramStore.Owns store rootLoc)
    (hstorageUnowned : ¬ ProgramStore.Owns store storage)
    (hne : storage ≠ rootLoc)
    (hleafChain : OwnsChain store rootLoc k leafLoc) :
    ∀ {value : PartialValue} {partialTy : PartialTy} {lifetime : Lifetime},
      store.slotAt storage = some ⟨value, lifetime⟩ →
      ¬ RuntimeFrame.OwnerReaches store value partialTy leafLoc := by
  intro value partialTy lifetime hstored hreach
  rcases ownerReaches_ownsChain_stored hstored hreach with ⟨n, hchain⟩
  rcases ownsChain_unique hvalidStore hstorageUnowned hrootUnowned
      hchain hleafChain with ⟨hroots, _⟩
  exact hne hroots

theorem ownsTransitively_of_ownsChain_succ {store : ProgramStore} :
    ∀ {n : Nat} {root target : Location},
      OwnsChain store root (n + 1) target →
      ProgramStore.OwnsTransitively store root target := by
  intro n
  induction n with
  | zero =>
      intro root target hchain
      cases hchain with
      | succ hprefix howns =>
          cases hprefix
          exact ProgramStore.OwnsTransitively.direct howns
  | succ n ih =>
      intro root target hchain
      cases hchain with
      | succ hprefix howns =>
          exact ProgramStore.OwnsTransitively.trans_right (ih hprefix) howns

theorem ownsChain_of_ownsTransitively {store : ProgramStore}
    {root target : Location} :
    ProgramStore.OwnsTransitively store root target →
    ∃ n, OwnsChain store root (n + 1) target := by
  intro hpath
  induction hpath with
  | direct howns =>
      exact ⟨0, OwnsChain.succ OwnsChain.zero howns⟩
  | trans howns _hpath ih =>
      rcases ih with ⟨n, hchain⟩
      refine ⟨n + 1, ?_⟩
      have hfirst : OwnsChain store _ 1 _ :=
        OwnsChain.succ OwnsChain.zero howns
      have hcomposed := ownsChain_append hfirst hchain
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcomposed

theorem ownsChain_of_protectedByBase {store : ProgramStore}
    {root : Name} {target : Location} :
    RuntimeFrame.ProtectedByBase store root target →
    ∃ n, OwnsChain store (VariableProjection root) n target := by
  intro hprotected
  cases hprotected with
  | inl hroot =>
      subst hroot
      exact ⟨0, OwnsChain.zero⟩
  | inr hpath =>
      rcases ownsChain_of_ownsTransitively hpath with ⟨n, hchain⟩
      exact ⟨n + 1, hchain⟩

theorem protectedByBase_chain_leaf_base_eq {store : ProgramStore}
    {moved : LVal} {leafLoc : Location} {k : Nat} {root : Name}
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hleafChain :
      OwnsChain store (VariableProjection (LVal.base moved)) k leafLoc)
    (hprotected : RuntimeFrame.ProtectedByBase store root leafLoc) :
    root = LVal.base moved := by
  rcases ownsChain_of_protectedByBase hprotected with ⟨n, hchain⟩
  rcases ownsChain_unique hvalidStore (var_not_owned hheap)
      (var_not_owned hheap) hchain hleafChain with ⟨hroot, _⟩
  simpa [VariableProjection] using hroot

theorem protectedByBase_of_ownsChain {store : ProgramStore}
    {root : Name} {target : Location} :
    ∀ {k : Nat},
      OwnsChain store (VariableProjection root) k target →
      RuntimeFrame.ProtectedByBase store root target := by
  intro k hchain
  induction hchain with
  | zero =>
      exact RuntimeFrame.ProtectedByBase.root
  | succ _ howns ih =>
      exact RuntimeFrame.ProtectedByBase.trans_owned ih howns

theorem protectedByBase_parent_of_ownsAt {store : ProgramStore}
    {root : Name} {owned storage : Location}
    (hvalidStore : ValidStore store)
    (hrootUnowned : ¬ ProgramStore.Owns store (VariableProjection root)) :
    RuntimeFrame.ProtectedByBase store root owned →
    ProgramStore.OwnsAt store owned storage →
    RuntimeFrame.ProtectedByBase store root storage := by
  intro hprotected howns
  cases hprotected with
  | inl hroot =>
      subst hroot
      exact False.elim (hrootUnowned ⟨storage, howns⟩)
  | inr hpath =>
      have hparent :
          ∀ {base owned storage : Location},
            ProgramStore.OwnsTransitively store base owned →
            ProgramStore.OwnsAt store owned storage →
            storage = base ∨
              ProgramStore.OwnsTransitively store base storage := by
        intro base owned storage hpath howns
        induction hpath generalizing storage with
        | @direct storage₀ owned₀ hdirect =>
            left
            exact hvalidStore owned₀ storage storage₀ howns hdirect
        | @trans storage₀ middle owned₀ hfirst _htail ih =>
            rcases ih howns with hstorage | hstorage
            · right
              subst hstorage
              exact ProgramStore.OwnsTransitively.direct hfirst
            · right
              exact ProgramStore.OwnsTransitively.trans hfirst hstorage
      rcases hparent hpath howns with hstorage | hstorage
      · subst hstorage
        exact RuntimeFrame.ProtectedByBase.root
      · exact Or.inr hstorage

/-- Linearized lvalue typings mention only variables below their syntactic base. -/
theorem lvalTyping_vars_rank_lt {φ : Name → Nat} {env : Env}
    (hφ : LinearizedBy φ env) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ v, v ∈ PartialTy.vars partialTy → φ v < φ (LVal.base lv) := by
  intro lv partialTy lifetime htyping
  induction htyping with
  | var hslot =>
      rename_i x slot
      intro v hv
      exact hφ x slot v hslot hv
  | box _ ih =>
      intro v hv
      exact ih v (by simpa [PartialTy.vars] using hv)
  | boxFull _ ih =>
      intro v hv
      exact ih v (by simpa [PartialTy.vars, Ty.vars] using hv)
  | borrow hsource htarget ihSource ihTarget =>
      rename_i source target mutable _borrowLifetime _targetLifetime _targetTy
      intro v hv
      have hvTarget : φ v < φ (LVal.base target) := ihTarget v hv
      have htargetMem :
          LVal.base target ∈
            PartialTy.vars (.ty (.borrow mutable target)) := by
        simp [PartialTy.vars, Ty.vars]
      have htargetLtSource :
          φ (LVal.base target) < φ (LVal.base source) :=
        ihSource (LVal.base target) htargetMem
      exact lt_trans hvTarget htargetLtSource

theorem lval_loc_protected_rank_le_base_whenInitialized
    {store : ProgramStore} {env : Env} {φ : Name → Nat} {root : Name}
    (hφ : LinearizedBy φ env)
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env lv partialTy lifetime →
      store.loc lv = some location →
      RuntimeFrame.ProtectedByBase store root location →
      φ root ≤ φ (LVal.base lv) := by
  intro lv partialTy lifetime location htyping
  induction htyping generalizing location root with
  | var hslot =>
      rename_i x slot
      intro hloc hprotected
      simp [ProgramStore.loc] at hloc
      subst hloc
      cases hprotected with
      | inl hroot =>
          have hrootEq : root = x := by
            simpa [VariableProjection] using hroot.symm
          subst hrootEq
          exact Nat.le_refl _
      | inr hpath =>
          rcases hheap _ (ProgramStore.OwnsTransitively.to_owns hpath) with
            ⟨address, hheapLocation⟩
          cases hheapLocation
  | box hsource ih =>
      intro hloc hprotected
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
          have hprotectedOwned :
              RuntimeFrame.ProtectedByBase store root ownedLocation := by
            simpa [hlocEq] using hprotected
          have hownsAt :
              ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              RuntimeFrame.ProtectedByBase store root sourceLocation :=
            protectedByBase_parent_of_ownsAt hvalidStore
              (var_not_owned hheap) hprotectedOwned hownsAt
          exact ih hsourceLoc hsourceProtected
  | boxFull hsource ih =>
      intro hloc hprotected
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
          have hprotectedOwned :
              RuntimeFrame.ProtectedByBase store root ownedLocation := by
            simpa [hlocEq] using hprotected
          have hownsAt :
              ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              RuntimeFrame.ProtectedByBase store root sourceLocation :=
            protectedByBase_parent_of_ownsAt hvalidStore
              (var_not_owned hheap) hprotectedOwned hownsAt
          exact ih hsourceLoc hsourceProtected
  | borrow hsource htarget ihSource ihTarget =>
      rename_i source target mutable _borrowLifetime _targetLifetime _targetTy
      intro hloc hprotected
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store _
            (.ty (.borrow mutable target)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrowLive borrowedLocation mutable target _hinitialized htargetLoc =>
          have hlocEq : location = borrowedLocation := by
            simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
          have hprotectedBorrowed :
              RuntimeFrame.ProtectedByBase store root borrowedLocation := by
            simpa [hlocEq] using hprotected
          have hrootLeTarget :
              φ root ≤ φ (LVal.base target) :=
            ihTarget htargetLoc hprotectedBorrowed
          have htargetMem :
              LVal.base target ∈
                PartialTy.vars (.ty (.borrow mutable target)) := by
            simp [PartialTy.vars, Ty.vars]
          have htargetLtSource :
              φ (LVal.base target) < φ (LVal.base source) :=
            lvalTyping_vars_rank_lt hφ hsource (LVal.base target) htargetMem
          exact le_trans hrootLeTarget (Nat.le_of_lt htargetLtSource)
      | @borrowStale _borrowedLocation _mutable _target hstale =>
          exact False.elim (hstale ⟨_, _, htarget⟩)

theorem locReads_protected_rank_le_base_whenInitialized
    {store : ProgramStore} {env : Env} {φ : Name → Nat} {root : Name}
    (hφ : LinearizedBy φ env)
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env lv partialTy lifetime →
      RuntimeFrame.LocReads store lv location →
      RuntimeFrame.ProtectedByBase store root location →
      φ root ≤ φ (LVal.base lv) := by
  intro lv partialTy lifetime location htyping
  induction htyping with
  | var _hslot =>
      intro hreads
      cases hreads
  | box hsource ih =>
      intro hreads hprotected
      cases hreads with
      | here hloc =>
          simpa [LVal.base] using
            lval_loc_protected_rank_le_base_whenInitialized
              hφ hsafe hvalidStore hheap hsource hloc hprotected
      | there hsourceReads =>
          exact ih hsourceReads hprotected
  | boxFull hsource ih =>
      intro hreads hprotected
      cases hreads with
      | here hloc =>
          simpa [LVal.base] using
            lval_loc_protected_rank_le_base_whenInitialized
              hφ hsafe hvalidStore hheap hsource hloc hprotected
      | there hsourceReads =>
          exact ih hsourceReads hprotected
  | borrow hsource _htarget ihSource _ihTarget =>
      intro hreads hprotected
      cases hreads with
      | here hloc =>
          simpa [LVal.base] using
            lval_loc_protected_rank_le_base_whenInitialized
              hφ hsafe hvalidStore hheap hsource hloc hprotected
      | there hsourceReads =>
          exact ihSource hsourceReads hprotected

theorem lval_loc_chain_leaf_conflict_or_writeProhibited_whenInitialized
    {env : Env} {store : ProgramStore} {moved : LVal} :
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env lv partialTy lifetime →
      store.loc lv = some location →
      RuntimeFrame.ProtectedByBase store (LVal.base moved) location →
      lv ⋈ moved ∨ WriteProhibited env moved := by
  intro hsafe hvalidStore hheap lv partialTy lifetime location htyping
  induction htyping generalizing location with
  | var hslot =>
      rename_i x slot
      intro hloc hprotected
      simp [ProgramStore.loc] at hloc
      subst hloc
      cases hprotected with
      | inl hroot =>
          left
          change x = LVal.base moved
          simpa [VariableProjection] using hroot
      | inr hpath =>
          rcases hheap _ (ProgramStore.OwnsTransitively.to_owns hpath) with
            ⟨address, hheapLocation⟩
          cases hheapLocation
  | box hsource ih =>
      intro hloc hprotected
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
          have hprotectedOwned :
              RuntimeFrame.ProtectedByBase store (LVal.base moved)
                ownedLocation := by
            simpa [hlocEq] using hprotected
          have hownsAt : ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              RuntimeFrame.ProtectedByBase store (LVal.base moved)
                sourceLocation :=
            protectedByBase_parent_of_ownsAt hvalidStore
              (var_not_owned hheap) hprotectedOwned hownsAt
          rcases ih hsourceLoc hsourceProtected with hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
  | boxFull hsource ih =>
      intro hloc hprotected
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
          have hprotectedOwned :
              RuntimeFrame.ProtectedByBase store (LVal.base moved)
                ownedLocation := by
            simpa [hlocEq] using hprotected
          have hownsAt : ProgramStore.OwnsAt store ownedLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              RuntimeFrame.ProtectedByBase store (LVal.base moved)
                sourceLocation :=
            protectedByBase_parent_of_ownsAt hvalidStore
              (var_not_owned hheap) hprotectedOwned hownsAt
          rcases ih hsourceLoc hsourceProtected with hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
  | borrow hsource htarget ihSource ihTarget =>
      intro hloc hprotected
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
          have hprotectedBorrowed :
              RuntimeFrame.ProtectedByBase store (LVal.base moved)
                borrowedLocation := by
            simpa [hlocEq] using hprotected
          rcases ihTarget htargetLoc hprotectedBorrowed with
            htargetConflict | hwrite
          · rcases LValTyping.contains_borrow hsource PartialTyContains.here with
              ⟨holder, hcontains⟩
            exact Or.inr
              (WriteProhibited.of_contains_conflict hcontains htargetConflict)
          · exact Or.inr hwrite
      | @borrowStale borrowedLocation mutable target hstale =>
          exact False.elim (hstale ⟨_, _, htarget⟩)

theorem locReads_chain_leaf_conflict_or_writeProhibited_whenInitialized
    {env : Env} {store : ProgramStore} {moved : LVal}
    {leafLoc : Location} {k : Nat} :
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    OwnsChain store (VariableProjection (LVal.base moved)) k leafLoc →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
      RuntimeFrame.LocReads store lv leafLoc →
      lv ⋈ moved ∨ WriteProhibited env moved := by
  intro hsafe hvalidStore hheap hleafChain lv partialTy lifetime htyping
  induction htyping with
  | var hslot =>
      intro hreads
      cases hreads
  | box hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_chain_leaf_conflict_or_writeProhibited_whenInitialized
              hsafe hvalidStore hheap hsource hloc
              (protectedByBase_of_ownsChain hleafChain) with
            hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
      | there hsourceReads =>
          rcases ih hsourceReads with hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
  | boxFull hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_chain_leaf_conflict_or_writeProhibited_whenInitialized
              hsafe hvalidStore hheap hsource hloc
              (protectedByBase_of_ownsChain hleafChain) with
            hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
      | there hsourceReads =>
          rcases ih hsourceReads with hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
  | borrow hsource htarget ihSource ihTarget =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases lval_loc_chain_leaf_conflict_or_writeProhibited_whenInitialized
              hsafe hvalidStore hheap hsource hloc
              (protectedByBase_of_ownsChain hleafChain) with
            hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
      | there hsourceReads =>
          rcases ihSource hsourceReads with hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite

theorem borrowDependencyWhenInitialized_chain_leaf_writeProhibited
    {env : Env} {store : ProgramStore} {moved : LVal}
    {leafLoc : Location} {k : Nat} :
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    OwnsChain store (VariableProjection (LVal.base moved)) k leafLoc →
    ∀ {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
      ,
      (∀ {mutable : Bool} {target : LVal},
        PartialTyContains partialTy (.borrow mutable target) →
        ∃ holder, env ⊢ holder ↝ (.borrow mutable target)) →
      RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy
        dependency →
      dependency = leafLoc →
      WriteProhibited env moved := by
  intro hsafe hvalidStore hheap hleafChain value partialTy dependency
    hcontains hdependency
  induction hdependency with
  | borrow hinitialized _hloc hreads =>
      intro hdependencyEq
      rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases locReads_chain_leaf_conflict_or_writeProhibited_whenInitialized
          hsafe hvalidStore hheap hleafChain htargetTyping
          (by simpa [hdependencyEq] using hreads) with
        hconflict | hwrite
      · rcases hcontains PartialTyContains.here with ⟨holder, hholder⟩
        exact WriteProhibited.of_contains_conflict hholder hconflict
      · exact hwrite
  | boxInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.box hcontainsInner))
        hdependencyEq
  | boxFullInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.tyBox hcontainsInner))
        hdependencyEq

theorem reachesWhenInitialized_chain_leaf_ne_of_no_ownerReaches
    {env : Env} {store : ProgramStore} {moved : LVal}
    {leafLoc : Location} {k : Nat}
    {value : PartialValue} {partialTy : PartialTy} :
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    OwnsChain store (VariableProjection (LVal.base moved)) k leafLoc →
    (∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      ∃ holder, env ⊢ holder ↝ (.borrow mutable target)) →
    ¬ WriteProhibited env moved →
    ¬ RuntimeFrame.OwnerReaches store value partialTy leafLoc →
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized env store value partialTy location →
      location ≠ leafLoc := by
  intro hsafe hvalidStore hheap hleafChain hcontains hnotWrite hownerNoReach
    location hreach
  induction hreach with
  | undefOf hskel hstrength howner =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using
          RuntimeFrame.OwnerReaches.undefOf hskel hstrength howner)
  | boxHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxHere hslot)
  | boxInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.box hcontainsInner))
        (by
          intro howner
          exact hownerNoReach (RuntimeFrame.OwnerReaches.boxInner hslot howner))
        hlocation
  | boxFullHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.tyBox hcontainsInner))
        (by
          intro howner
          exact hownerNoReach
            (RuntimeFrame.OwnerReaches.boxFullInner hslot howner))
        hlocation
  | borrow hinitialized hloc hreads =>
      intro hlocation
      exact hnotWrite
        (borrowDependencyWhenInitialized_chain_leaf_writeProhibited
          hsafe hvalidStore hheap hleafChain hcontains
          (RuntimeFrame.BorrowDependencyWhenInitialized.borrow
            hinitialized hloc hreads)
          hlocation)

theorem LValTyping.update_var_to_source_of_no_conflicts
    {env env' : Env} {x : Name} {updatedSlot : EnvSlot} :
    env' = env.update x updatedSlot →
    (∀ holder mutable target,
      env' ⊢ holder ↝ (.borrow mutable target) →
      ¬ target ⋈ (.var x)) →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      ¬ lv ⋈ (.var x) →
      LValTyping env' lv partialTy lifetime →
      LValTyping env lv partialTy lifetime := by
  intro henv' hnoConflicts lv partialTy lifetime hnotConflict htyping
  induction htyping with
  | var hslot =>
      rename_i y slot
      have hyx : y ≠ x := by
        intro hyx
        exact hnotConflict (by simpa [PathConflicts, LVal.base, hyx])
      exact .var (by
        rw [henv'] at hslot
        simpa [Env.update, hyx] using hslot)
  | box _ ih =>
      exact .box (ih hnotConflict)
  | boxFull _ ih =>
      exact .boxFull (ih hnotConflict)
  | borrow hborrow htarget ihBorrow ihTarget =>
      rename_i source target mutable borrowLifetime targetLifetime targetTy
      have hborrowSource :
          LValTyping env source (.ty (.borrow mutable target))
            borrowLifetime :=
        ihBorrow hnotConflict
      rcases LValTyping.contains_borrow hborrow PartialTyContains.here with
        ⟨holder, hcontains⟩
      have htargetNoConflict : ¬ target ⋈ (.var x) :=
        hnoConflicts holder mutable target hcontains
      exact .borrow hborrowSource (ihTarget htargetNoConflict)

theorem lval_loc_chain_leaf_conflict_or_writeProhibited_update_var_whenInitialized
    {env env' : Env} {store : ProgramStore} {moved : LVal}
    {updatedSlot : EnvSlot} {leafLoc location : Location} {k : Nat} :
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env' = env.update (LVal.base moved) updatedSlot →
    ¬ WriteProhibited env' moved →
    OwnsChain store (VariableProjection (LVal.base moved)) k leafLoc →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env' lv partialTy lifetime →
      store.loc lv = some location →
      RuntimeFrame.ProtectedByBase store (LVal.base moved) location →
      lv ⋈ moved ∨ WriteProhibited env' moved := by
  intro hsafe hvalidStore hheap henv' hnotWrite hleafChain
  have hnoConflicts :
      ∀ holder mutable target,
        env' ⊢ holder ↝ (.borrow mutable target) →
        ¬ target ⋈ (.var (LVal.base moved)) := by
    intro holder mutable target hcontains hconflict
    exact hnotWrite
      (WriteProhibited.of_contains_conflict hcontains
        (by simpa [PathConflicts, LVal.base] using hconflict))
  intro lv partialTy lifetime htyping
  induction htyping generalizing location with
  | var hslot =>
      rename_i x slot
      intro hloc hprotected
      simp [ProgramStore.loc] at hloc
      subst hloc
      cases hprotected with
      | inl hroot =>
          left
          change x = LVal.base moved
          simpa [VariableProjection] using hroot
      | inr hpath =>
          rcases hheap _ (ProgramStore.OwnsTransitively.to_owns hpath) with
            ⟨address, hheapLocation⟩
          cases hheapLocation
  | box hsource ih =>
      rename_i source inner sourceLifetime
      intro hloc hprotected
      by_cases hbase : LVal.base source = LVal.base moved
      · left
        simpa [PathConflicts, LVal.base, hbase]
      · have hsourceEnv :
            LValTyping env source (.box _) _ :=
          LValTyping.update_var_to_source_of_no_conflicts henv'
            hnoConflicts
            (by simpa [PathConflicts, LVal.base] using hbase) hsource
        have hsourceAbs :
            LValLocationAbstractionWhenInitialized env store _ (.box _) :=
          lvalTyping_defined_location_whenInitialized hsafe hsourceEnv
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
            hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @box ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
            have hlocEq : location = ownedLocation := by
              simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
            have hprotectedOwned :
                RuntimeFrame.ProtectedByBase store (LVal.base moved)
                  ownedLocation := by
              simpa [hlocEq] using hprotected
            have hownsAt :
                ProgramStore.OwnsAt store ownedLocation sourceLocation :=
              ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
            have hsourceProtected :
                RuntimeFrame.ProtectedByBase store (LVal.base moved)
                  sourceLocation :=
              protectedByBase_parent_of_ownsAt hvalidStore
                (var_not_owned hheap) hprotectedOwned hownsAt
            rcases ih hsourceLoc hsourceProtected with hconflict | hwrite
            · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
            · exact Or.inr hwrite
  | boxFull hsource ih =>
      rename_i source inner sourceLifetime
      intro hloc hprotected
      by_cases hbase : LVal.base source = LVal.base moved
      · left
        simpa [PathConflicts, LVal.base, hbase]
      · have hsourceEnv :
            LValTyping env source (.ty (.box _)) _ :=
          LValTyping.update_var_to_source_of_no_conflicts henv'
            hnoConflicts
            (by simpa [PathConflicts, LVal.base] using hbase) hsource
        have hsourceAbs :
            LValLocationAbstractionWhenInitialized env store _
              (.ty (.box _)) :=
          lvalTyping_defined_location_whenInitialized hsafe hsourceEnv
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
            hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @boxFull ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
            have hlocEq : location = ownedLocation := by
              simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
            have hprotectedOwned :
                RuntimeFrame.ProtectedByBase store (LVal.base moved)
                  ownedLocation := by
              simpa [hlocEq] using hprotected
            have hownsAt :
                ProgramStore.OwnsAt store ownedLocation sourceLocation :=
              ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
            have hsourceProtected :
                RuntimeFrame.ProtectedByBase store (LVal.base moved)
                  sourceLocation :=
              protectedByBase_parent_of_ownsAt hvalidStore
                (var_not_owned hheap) hprotectedOwned hownsAt
            rcases ih hsourceLoc hsourceProtected with hconflict | hwrite
            · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
            · exact Or.inr hwrite
  | borrow hsource htarget ihSource ihTarget =>
      rename_i source target mutable borrowLifetime targetLifetime targetTy
      intro hloc hprotected
      by_cases hbase : LVal.base source = LVal.base moved
      · left
        simpa [PathConflicts, LVal.base, hbase]
      · have hsourceEnv :
            LValTyping env source (.ty (.borrow _ _)) _ :=
          LValTyping.update_var_to_source_of_no_conflicts henv'
            hnoConflicts
            (by simpa [PathConflicts, LVal.base] using hbase) hsource
        have hsourceAbs :
            LValLocationAbstractionWhenInitialized env store _
              (.ty (.borrow _ _)) :=
          lvalTyping_defined_location_whenInitialized hsafe hsourceEnv
        rcases hsourceAbs with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
            hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @borrowLive borrowedLocation mutable target _hinitialized htargetLoc =>
            have hlocEq : location = borrowedLocation := by
              simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
            have hprotectedBorrowed :
                RuntimeFrame.ProtectedByBase store (LVal.base moved)
                  borrowedLocation := by
              simpa [hlocEq] using hprotected
            rcases ihTarget htargetLoc hprotectedBorrowed with
              htargetConflict | hwrite
            · rcases LValTyping.contains_borrow hsource PartialTyContains.here
                with ⟨holder, hcontains⟩
              exact Or.inr
                (WriteProhibited.of_contains_conflict hcontains
                  htargetConflict)
            · exact Or.inr hwrite
        | @borrowStale borrowedLocation mutable target hstale =>
            by_cases htargetBase : LVal.base target = LVal.base moved
            · right
              rcases LValTyping.contains_borrow hsource PartialTyContains.here
                with ⟨holder, hcontains⟩
              exact WriteProhibited.of_contains_conflict hcontains
                (by simpa [PathConflicts, LVal.base, htargetBase])
            · have htargetEnv :
                  LValTyping env target (.ty _) _ :=
                LValTyping.update_var_to_source_of_no_conflicts henv'
                  hnoConflicts
                  (by simpa [PathConflicts, LVal.base] using htargetBase)
                  htarget
              exact False.elim (hstale ⟨_, _, htargetEnv⟩)

theorem locReads_chain_leaf_conflict_or_writeProhibited_update_var_whenInitialized
    {env env' : Env} {store : ProgramStore} {moved : LVal}
    {updatedSlot : EnvSlot} {leafLoc : Location} {k : Nat} :
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env' = env.update (LVal.base moved) updatedSlot →
    ¬ WriteProhibited env' moved →
    OwnsChain store (VariableProjection (LVal.base moved)) k leafLoc →
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env' lv partialTy lifetime →
      RuntimeFrame.LocReads store lv leafLoc →
      lv ⋈ moved ∨ WriteProhibited env' moved := by
  intro hsafe hvalidStore hheap henv' hnotWrite hleafChain
    lv partialTy lifetime htyping
  induction htyping with
  | var hslot =>
      intro hreads
      cases hreads
  | box hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases
              lval_loc_chain_leaf_conflict_or_writeProhibited_update_var_whenInitialized
                hsafe hvalidStore hheap henv' hnotWrite hleafChain
                hsource hloc (protectedByBase_of_ownsChain hleafChain) with
            hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
      | there hsourceReads =>
          rcases ih hsourceReads with hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
  | boxFull hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases
              lval_loc_chain_leaf_conflict_or_writeProhibited_update_var_whenInitialized
                hsafe hvalidStore hheap henv' hnotWrite hleafChain
                hsource hloc (protectedByBase_of_ownsChain hleafChain) with
            hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
      | there hsourceReads =>
          rcases ih hsourceReads with hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
  | borrow hsource htarget ihSource ihTarget =>
      intro hreads
      cases hreads with
      | here hloc =>
          rcases
              lval_loc_chain_leaf_conflict_or_writeProhibited_update_var_whenInitialized
                hsafe hvalidStore hheap henv' hnotWrite hleafChain
                hsource hloc (protectedByBase_of_ownsChain hleafChain) with
            hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite
      | there hsourceReads =>
          rcases ihSource hsourceReads with hconflict | hwrite
          · exact Or.inl (by simpa [PathConflicts, LVal.base] using hconflict)
          · exact Or.inr hwrite

theorem borrowDependencyWhenInitialized_chain_leaf_update_var_writeProhibited
    {env env' : Env} {store : ProgramStore} {moved : LVal}
    {updatedSlot : EnvSlot} {leafLoc : Location} {k : Nat} :
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env' = env.update (LVal.base moved) updatedSlot →
    ¬ WriteProhibited env' moved →
    OwnsChain store (VariableProjection (LVal.base moved)) k leafLoc →
    ∀ {value : PartialValue} {partialTy : PartialTy}
      {dependency : Location},
      (∀ {mutable : Bool} {target : LVal},
        PartialTyContains partialTy (.borrow mutable target) →
        ∃ holder, env' ⊢ holder ↝ (.borrow mutable target)) →
      RuntimeFrame.BorrowDependencyWhenInitialized env' store value partialTy
        dependency →
      dependency = leafLoc →
      WriteProhibited env' moved := by
  intro hsafe hvalidStore hheap henv' hnotWrite hleafChain
    value partialTy dependency hcontains hdependency
  induction hdependency with
  | borrow hinitialized _hloc hreads =>
      intro hdependencyEq
      rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases
          locReads_chain_leaf_conflict_or_writeProhibited_update_var_whenInitialized
            hsafe hvalidStore hheap henv' hnotWrite hleafChain
            htargetTyping (by simpa [hdependencyEq] using hreads) with
        hconflict | hwrite
      · rcases hcontains PartialTyContains.here with ⟨holder, hholder⟩
        exact WriteProhibited.of_contains_conflict hholder hconflict
      · exact hwrite
  | boxInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.box hcontainsInner))
        hdependencyEq
  | boxFullInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.tyBox hcontainsInner))
        hdependencyEq

theorem reachesWhenInitialized_chain_leaf_ne_of_update_var_not_writeProhibited
    {env env' : Env} {store : ProgramStore} {moved : LVal}
    {updatedSlot : EnvSlot} {leafLoc : Location} {k : Nat}
    {value : PartialValue} {partialTy : PartialTy} :
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env' = env.update (LVal.base moved) updatedSlot →
    ¬ WriteProhibited env' moved →
    OwnsChain store (VariableProjection (LVal.base moved)) k leafLoc →
    (∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      ∃ holder, env' ⊢ holder ↝ (.borrow mutable target)) →
    ¬ RuntimeFrame.OwnerReaches store value partialTy leafLoc →
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized env' store value partialTy location →
      location ≠ leafLoc := by
  intro hsafe hvalidStore hheap henv' hnotWrite hleafChain hcontains
    hownerNoReach location hreach
  induction hreach with
  | undefOf hskel hstrength howner =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using
          RuntimeFrame.OwnerReaches.undefOf hskel hstrength howner)
  | boxHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxHere hslot)
  | boxInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.box hcontainsInner))
        (by
          intro howner
          exact hownerNoReach (RuntimeFrame.OwnerReaches.boxInner hslot howner))
        hlocation
  | boxFullHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.tyBox hcontainsInner))
        (by
          intro howner
          exact hownerNoReach
            (RuntimeFrame.OwnerReaches.boxFullInner hslot howner))
        hlocation
  | borrow hinitialized hloc hreads =>
      intro hlocation
      exact hnotWrite
        (borrowDependencyWhenInitialized_chain_leaf_update_var_writeProhibited
          hsafe hvalidStore hheap henv' hnotWrite hleafChain hcontains
          (RuntimeFrame.BorrowDependencyWhenInitialized.borrow
            hinitialized hloc hreads)
          hlocation)

theorem ownerReaches_leaf_ne_of_stored_leaf_valid
    {env : Env} {store : ProgramStore} {leafLoc : Location}
    {leafSlot : StoreSlot} {partialTy : PartialTy} :
    store.slotAt leafLoc = some leafSlot →
    ValidPartialValueWhenInitialized env store leafSlot.value partialTy →
    ¬ RuntimeFrame.OwnerReaches store leafSlot.value partialTy leafLoc := by
  intro hleafSlot hvalid hreach
  rcases ownerReaches_ownsChain_stored hleafSlot hreach with ⟨n, hchain⟩
  exact ValidPartialValueWhenInitialized.no_storage_ownership_cycle
    hleafSlot hvalid (ownsTransitively_of_ownsChain_succ hchain)

theorem ownerReaches_ownsChain_value {store : ProgramStore} :
    ∀ {value : Value} {partialTy : PartialTy} {ℓ : Location},
      RuntimeFrame.OwnerReaches store (.value value) partialTy ℓ →
      ∃ root n, root ∈ valueOwningLocations value ∧
        OwnsChain store root n ℓ := by
  intro value partialTy ℓ hreach
  generalize hpv : (.value value : PartialValue) = rootValue at hreach
  induction hreach generalizing value with
  | undefOf _hskel _hstrength _howner ih =>
      exact ih hpv
  | boxHere hslot =>
      cases hpv
      exact ⟨_, 0, by
        simp [valueOwningLocations, valueOwnedLocation?],
        OwnsChain.zero⟩
  | boxInner hslot hinner =>
      cases hpv
      rcases ownerReaches_ownsChain_stored hslot hinner with ⟨n, hchain⟩
      exact ⟨_, n + 1, by
        simp [valueOwningLocations, valueOwnedLocation?],
        hchain⟩
  | boxFullHere hslot =>
      cases hpv
      exact ⟨_, 0, by
        simp [valueOwningLocations, valueOwnedLocation?],
        OwnsChain.zero⟩
  | boxFullInner hslot hinner =>
      cases hpv
      rcases ownerReaches_ownsChain_stored hslot hinner with ⟨n, hchain⟩
      exact ⟨_, n + 1, by
        simp [valueOwningLocations, valueOwnedLocation?],
        hchain⟩

theorem dropsAvoids_of_ownerReaches_value_lifetime_whenInitialized
    {store store' : ProgramStore} {parent child : Lifetime}
    {dropSet : List PartialValue} {value : Value}
    {partialTy : PartialTy} {location : Location} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    HeapSlotsRootLifetime store →
    ValueOwnerTargetsHeap value →
    (∀ owned, owned ∈ valueOwningLocations value →
      ¬ ProgramStore.Owns store owned) →
    (∀ value, value ∈ dropSet ↔
      ∃ location slot,
        store.slotAt location = some slot ∧
        slot.lifetime = child ∧
        value = .value (.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeDropOwnersDisjoint store child →
    LifetimeChild parent child →
    RuntimeFrame.OwnerReaches store (.value value) partialTy location →
    DropsAvoids store dropSet location := by
  intro hvalidStore hheap hrootLifetime hvalueHeap hvalueUnowned hdropSet
    hdrops hdropDisjoint hchild howner
  have hdropNoOwned :
      ∀ {owned storage : Location},
        ProgramStore.OwnsAt store owned storage →
        ∀ value, value ∈ dropSet →
          owned ∉ partialValueOwningLocations value := by
    intro owned storage howns value hmem howned
    rcases (hdropSet value).mp hmem with
      ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
    have hownedEq : owned = dropLocation :=
      eq_location_of_mem_lifetime_drop_value hdropValue howned
    subst hownedEq
    exact hdropDisjoint owned dropSlot hdropSlot hdropLifetime
      ⟨storage, howns⟩
  have hpathAvoid :
      ∀ {storage owned : Location},
        ProgramStore.OwnsTransitively store storage owned →
        DropsAvoids store dropSet storage →
        DropsAvoids store dropSet owned := by
    intro storage owned hpath
    induction hpath with
    | direct howns =>
        intro havoidStorage
        exact dropsAvoids_of_protected_owner hdrops hvalidStore howns
          havoidStorage (hdropNoOwned howns)
    | trans hfirst _htail ih =>
        intro havoidStorage
        have havoidMiddle : DropsAvoids store dropSet _ :=
          dropsAvoids_of_protected_owner hdrops hvalidStore hfirst
            havoidStorage (hdropNoOwned hfirst)
        exact ih havoidMiddle
  rcases ownerReaches_ownsChain_value howner with
    ⟨root, n, hrootMem, hchain⟩
  have hrootNoMem :
      ∀ dropValue, dropValue ∈ dropSet →
        root ∉ partialValueOwningLocations dropValue := by
    intro dropValue hmem howned
    rcases (hdropSet dropValue).mp hmem with
      ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
    have hrootEq : root = dropLocation :=
      eq_location_of_mem_lifetime_drop_value hdropValue howned
    subst hrootEq
    rcases hvalueHeap root hrootMem with ⟨address, hheapLocation⟩
    subst hheapLocation
    have hrootSlot : dropSlot.lifetime = Lifetime.root :=
      hrootLifetime address dropSlot hdropSlot
    exact LifetimeChild.child_ne_root hchild (hdropLifetime ▸ hrootSlot)
  have havoidRoot : DropsAvoids store dropSet root :=
    dropsAvoids_of_not_owns_and_not_mem hdrops hrootNoMem
      (hvalueUnowned root hrootMem)
  cases n with
  | zero =>
      cases hchain
      exact havoidRoot
  | succ n =>
      exact hpathAvoid (ownsTransitively_of_ownsChain_succ hchain)
        havoidRoot

theorem preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop
    {store finalStore : ProgramStore} {env : Env}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value}
    {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    SafeAbstraction store env →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnvWhenInitialized env blockLifetime →
    WellFormedTy env ty lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue
      (env.dropLifetime blockLifetime) ty := by
  intro hvalidRuntime hsafe hchild hwellBody hwellTy hvalidValue hmulti
  have hinitDropBack :
      ∀ {target : LVal},
        TargetInitialized (env.dropLifetime blockLifetime) target →
        TargetInitialized env target := by
    intro target hinitialized
    rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
    exact ⟨targetTy, targetLifetime, LValTyping.of_dropLifetime htargetTyping⟩
  exact preservation_runtime_multistep_of_step_to_value_whenInitialized
    (term := .block blockLifetime [.val value])
    (env := env.dropLifetime blockLifetime)
    (ty := ty)
    (by simp [Terminal])
    (by
      intro _store' _term' hstep
      cases hstep with
      | blockA hvalueStep =>
          exact False.elim (value_no_step hvalueStep)
      | blockB _hdrops =>
          exact ⟨value, rfl⟩)
    (by
      intro store' steppedValue hstep
      cases hstep with
      | blockB hdropsLifetime =>
          have hdropDisjoint : LifetimeDropOwnersDisjoint store blockLifetime :=
            lifetimeDropOwnersDisjoint_of_heapRootLifetime
              (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
              (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime)
              hchild
          cases hdropsLifetime with
          | intro hdropSet hdropsRaw =>
              let hdropsLifetime' : DropsLifetime store blockLifetime store' :=
                ProgramStore.DropsLifetime.intro hdropSet hdropsRaw
              have hwellTyWhen :
                  WellFormedTyWhenInitialized env ty lifetime :=
                hwellTy.whenInitialized
              have hvalueHeap : ValueOwnerTargetsHeap value :=
                TermOwnerTargetsHeap.value
                  (termOwnerTargetsHeap_block_value
                    (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
              have hvalueUnowned :
                  ∀ owned, owned ∈ valueOwningLocations value →
                    ¬ ProgramStore.Owns store owned := by
                intro owned hmem
                exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
                  (by
                    simpa [termOwningLocations, termValues,
                      partialValueOwningLocations] using hmem)
              have hresultValueEnv :
                  ValidPartialValueWhenInitialized env store'
                    (.value value) (.ty ty) :=
                RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_live_reaches
                  hdropsRaw hvalidValue (by
                    intro location hreach
                    rcases RuntimeFrame.ReachesWhenInitialized.owner_or_borrow
                        hreach with howner | hdependency
                    · exact
                        dropsAvoids_of_ownerReaches_value_lifetime_whenInitialized
                          (ValidRuntimeState.validStore hvalidRuntime)
                          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                          (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime)
                          hvalueHeap hvalueUnowned hdropSet hdropsRaw
                          hdropDisjoint hchild howner
                    · exact
                        borrowDependencyWhenInitialized_dropsAvoids_lifetime
                          hwellBody.1 hsafe
                          (ValidRuntimeState.validStore hvalidRuntime)
                          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                          hdropSet hdropsRaw hdropDisjoint hchild
                          (LifetimeOutlives.refl lifetime)
                          (PartialTyBorrowsWellFormedInSlotWhenInitialized.of_wellFormedTy
                            hwellTyWhen)
                          hdependency)
              have hresultValue :
                  ValidPartialValueWhenInitialized
                    (env.dropLifetime blockLifetime) store'
                    (.value value) (.ty ty) :=
                validPartialValueWhenInitialized_transport_env
                  hinitDropBack hresultValueEnv
              have hpreserve :
                  ∀ x envSlot,
                    env.slotAt x = some envSlot →
                    envSlot.lifetime ≠ blockLifetime →
                    ∃ oldValue,
                      store'.slotAt (VariableProjection x) =
                        some ({ value := oldValue, lifetime := envSlot.lifetime } : StoreSlot) ∧
                      ValidPartialValueWhenInitialized
                        (env.dropLifetime blockLifetime) store'
                        oldValue envSlot.ty := by
                intro x envSlot henvSlot hsurvives
                rcases hsafe.2 x envSlot henvSlot with
                  ⟨oldValue, hstoreSlot, hvalidOld⟩
                have havoidVar :
                    DropsAvoids store _ (VariableProjection x) :=
                  dropsAvoids_var_of_not_owning_var hdropsRaw
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    (by
                      intro dropValue hmem hownsVar
                      rcases (hdropSet dropValue).mp hmem with
                        ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime,
                          hdropValue⟩
                      have howned :
                          (VariableProjection x : Location) = dropLocation :=
                        eq_location_of_mem_lifetime_drop_value hdropValue hownsVar
                      subst howned
                      have hdropSlotEq :
                          dropSlot =
                            { value := oldValue,
                              lifetime := envSlot.lifetime } := by
                        exact Option.some.inj
                          (hdropSlot.symm.trans hstoreSlot)
                      subst hdropSlotEq
                      exact hsurvives hdropLifetime)
                have hvalidOldEnv' :
                    ValidPartialValueWhenInitialized env store'
                      oldValue envSlot.ty := by
                  refine
                    RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_live_reaches
                      hdropsRaw hvalidOld ?_
                  intro reached hreach
                  exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized_of_frames
                    hdropsRaw
                    (ValidRuntimeState.validStore hvalidRuntime)
                    hstoreSlot hvalidOld havoidVar
                    (by
                      intro reached' howner dropValue hmem howned
                      rcases (hdropSet dropValue).mp hmem with
                        ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime,
                          hdropValue⟩
                      have hreachedEq : reached' = dropLocation :=
                        eq_location_of_mem_lifetime_drop_value hdropValue howned
                      have hownsReached :
                          ProgramStore.Owns store reached' :=
                        RuntimeFrame.store_owns_of_reaches_stored_validPartialValueWhenInitialized
                          hstoreSlot hvalidOld howner
                      exact hdropDisjoint dropLocation dropSlot hdropSlot
                        hdropLifetime (by simpa [hreachedEq] using hownsReached))
                    (by
                      intro dependency hdependency
                      have hslotParent : envSlot.lifetime ≤ lifetime :=
                        LifetimeChild.parent_of_outlives_child_ne hchild
                          (hwellBody.2 x envSlot henvSlot) hsurvives
                      have hborrows :
                          PartialTyBorrowsWellFormedInSlotWhenInitialized env
                            envSlot.lifetime envSlot.ty := by
                        intro mutable target hcontains
                        exact hwellBody.1 x envSlot mutable target henvSlot
                          ⟨envSlot, henvSlot, hcontains⟩
                      exact borrowDependencyWhenInitialized_dropsAvoids_lifetime
                        hwellBody.1 hsafe
                        (ValidRuntimeState.validStore hvalidRuntime)
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                        hdropSet hdropsRaw hdropDisjoint hchild
                        hslotParent hborrows hdependency)
                    hreach
                have hvalidOldDrop :
                    ValidPartialValueWhenInitialized
                      (env.dropLifetime blockLifetime) store'
                      oldValue envSlot.ty :=
                  validPartialValueWhenInitialized_transport_env
                    hinitDropBack hvalidOldEnv'
                have hstoreSlot' :
                    store'.slotAt (VariableProjection x) =
                      some ({ value := oldValue, lifetime := envSlot.lifetime } : StoreSlot) :=
                  dropsLifetime_preserves_var_slot_of_not_lifetime
                    hdropsLifetime'
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    (by simpa [VariableProjection] using hstoreSlot)
                    hsurvives
                exact ⟨oldValue, hstoreSlot', hvalidOldDrop⟩
              have hsafeDrop :
                  SafeAbstraction store'
                    (env.dropLifetime blockLifetime) :=
                dropPreservation_lifetime_whenInitialized hsafe
                  hdropsLifetime'
                  (dropLifetime_domain_equiv_of_ownerTargetsHeap_whenInitialized
                    hsafe hdropsLifetime'
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime))
                  hpreserve
              exact ⟨validRuntimeState_blockB_step_of_child hvalidRuntime
                  hchild (Step.blockB (lifetime := lifetime) hdropsLifetime'),
                hsafeDrop, hresultValue⟩)
    hmulti

theorem ownerReaches_value_ne_chain_leaf_of_unowned_root
    {store : ProgramStore} {root : Name} {k : Nat} {leafLoc : Location}
    {value : Value} {partialTy : PartialTy}
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hvalueHeap : ValueOwnerTargetsHeap value)
    (hvalueUnowned : ∀ owned, owned ∈ valueOwningLocations value →
      ¬ ProgramStore.Owns store owned)
    (hleafChain : OwnsChain store (VariableProjection root) k leafLoc) :
    ¬ RuntimeFrame.OwnerReaches store (.value value) partialTy leafLoc := by
  intro hreach
  rcases ownerReaches_ownsChain_value hreach with
    ⟨valueRoot, n, hvalueRootMem, hvalueChain⟩
  rcases ownsChain_unique hvalidStore
      (hvalueUnowned valueRoot hvalueRootMem) (var_not_owned hheap)
      hvalueChain hleafChain with
    ⟨hrootEq, _hlen⟩
  rcases hvalueHeap valueRoot hvalueRootMem with
    ⟨address, hheapLocation⟩
  rw [hrootEq] at hheapLocation
  cases hheapLocation

theorem preservation_move_deref_box_multistep_runtime_whenInitialized_of_wellFormed
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {source : LVal} {finalValue : Value} {ty : Ty} :
    WellFormedEnvWhenInitialized env₁ lifetime →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.move source.deref) →
    LValTyping env₁ source (.box (.ty ty)) valueLifetime →
    ¬ WriteProhibited env₁ source.deref →
    EnvMove env₁ source.deref env₂ →
    TermTyping env₁ typing lifetime (.move source.deref) ty env₂ →
    MultiStep store lifetime (.move source.deref) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro _hwellFormed hsafe hvalidRuntime hsourceBox hnotWrite hmove htyping
    hmulti
  exact preservation_runtime_multistep_of_step_to_value_whenInitialized
    (term := .move source.deref)
    (env := env₂)
    (ty := ty)
    (by simp [Terminal])
    (by
      intro _store' _term' hstep
      cases hstep with
      | move _hread _hwrite => exact ⟨_, rfl⟩)
    (by
      intro store' value hstep
      cases hstep with
      | move hread hwrite =>
          have hmoveOriginal : EnvMove env₁ source.deref env₂ := hmove
          rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv₂⟩
          have hmoveSlotBase :
              env₁.slotAt (LVal.base source) = some moveSlot := by
            simpa [LVal.base] using hmoveSlot
          rcases
              lvalTyping_box_ownerChainPrefix_whenInitialized hsafe
                hsourceBox with
            ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
              hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
              hrootValid, hsourceValid, hprefix⟩
          have hmoveSlotEq : moveSlot = envSlot :=
            Option.some.inj (hmoveSlotBase.symm.trans henvBase)
          subst hmoveSlotEq
          rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
          cases hsourceValid with
          | @box ownerLocation ownerSlot inner hownedSlot hinnerValid =>
              have hderefLoc :
                  store.loc source.deref = some ownerLocation := by
                simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
              have hreadConcrete :
                  store.read source.deref = some ownerSlot := by
                simp [ProgramStore.read, hderefLoc, hownedSlot]
              have hownerSlotValue : ownerSlot.value = .value value := by
                rw [hreadConcrete] at hread
                exact congrArg StoreSlot.value (Option.some.inj hread)
              have hstore' :
                  store' =
                    store.update ownerLocation
                      { ownerSlot with value := .undef } := by
                have hwriteConcrete :
                    store.write source.deref .undef =
                      some
                        (store.update ownerLocation
                          { ownerSlot with value := .undef }) := by
                  simp [ProgramStore.write, hderefLoc, hownedSlot]
                rw [hwriteConcrete] at hwrite
                exact (Option.some.inj hwrite).symm
              subst hstore'
              have hsourceOwner :
                  (StoreSlot.mk
                    (.value (.ref { location := ownerLocation, owner := true }))
                    sourceLifetime).value =
                  .value (.ref { location := ownerLocation, owner := true }) := rfl
              have hprefixExtended :
                  ∃ k,
                    OwnerChainAt store rootSlot.value
                      (LVal.path source ++ [()]) ownerLocation ∧
                    OwnsChain store (VariableProjection (LVal.base source)) k
                      ownerLocation ∧
                    k = (LVal.path source ++ [()]).length :=
                OwnerChainPrefix.extend hprefix
                  (by
                    intro hpathNil
                    have hlocRoot :=
                      ProgramStore.loc_eq_var_of_path_nil
                        (store := store) (lv := source) hpathNil
                    have hlocEq :
                        sourceLocation = VariableProjection (LVal.base source) :=
                      Option.some.inj (hsourceLoc.symm.trans hlocRoot)
                    subst hlocEq
                    have hslotEq :
                        StoreSlot.mk
                            (.value (.ref { location := ownerLocation, owner := true }))
                            sourceLifetime = rootSlot :=
                      Option.some.inj (hsourceSlot.symm.trans hrootSlot)
                    exact congrArg StoreSlot.value hslotEq.symm)
                  hsourceSlot hsourceOwner
              rcases hprefixExtended with
                ⟨k, hchainAt, hleafChain, hchainLen⟩
              have hvalidStore : ValidStore store :=
                ValidRuntimeState.validStore hvalidRuntime
              have hheap : StoreOwnerTargetsHeap store :=
                ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
              have hrootUnowned :
                  ¬ ProgramStore.Owns store
                    (VariableProjection (LVal.base source)) :=
                var_not_owned hheap
              have hrootSlotCur :
                  ∃ rootLifetime,
                    store.slotAt (VariableProjection (LVal.base source)) =
                      some ⟨rootSlot.value, rootLifetime⟩ :=
                ⟨rootSlot.lifetime, by simpa using hrootSlot⟩
              have hstrikePath :
                  Strike (LVal.path source.deref) moveSlot.ty struck := by
                simpa [LVal.path] using hstrike
              have hrootValidFinal :
                  ValidPartialValueWhenInitialized env₂
                    (store.update ownerLocation
                      { ownerSlot with value := .undef })
                    rootSlot.value struck := by
                have hlen :
                    k = 0 + (LVal.path source.deref).length := by
                  simpa [LVal.path] using hchainLen
                exact validPartialValueWhenInitialized_strike_write
                  (env := env₁) (moved := env₂)
                  (rootLoc := VariableProjection (LVal.base source))
                  hvalidStore hrootUnowned hleafChain hownedSlot
                  hstrikePath hrootValid
                  (by simpa [LVal.path] using hchainAt)
                  hrootSlotCur OwnsChain.zero hlen
              have hrootNeLeaf :
                  VariableProjection (LVal.base source) ≠ ownerLocation := by
                intro hEq
                subst hEq
                have hlenEq :=
                  ownsChain_unique_length hvalidStore hrootUnowned hleafChain
                    (OwnsChain.zero
                      (store := store)
                      (location := VariableProjection (LVal.base source)))
                have hpos : 0 < k := by
                  rw [hchainLen]
                  simp
                omega
              have hrootSlotFinal :
                  (store.update ownerLocation
                    { ownerSlot with value := .undef }).slotAt
                      (VariableProjection (LVal.base source)) =
                    some { value := rootSlot.value, lifetime := moveSlot.lifetime } := by
                have hrootSlotMoveLifetime :
                    store.slotAt (VariableProjection (LVal.base source)) =
                      some { value := rootSlot.value, lifetime := moveSlot.lifetime } := by
                  cases rootSlot with
                  | mk rootValue rootLifetime =>
                      have hrootLifetimeMove : rootLifetime = moveSlot.lifetime := by
                        simpa using hrootLifetime
                      cases hrootLifetimeMove
                      simpa using hrootSlot
                simpa [ProgramStore.update, hrootNeLeaf] using hrootSlotMoveLifetime
              have hvalidValueStore :
                  ValidPartialValueWhenInitialized env₁ store
                    (.value value) (.ty ty) := by
                rw [← hownerSlotValue]
                exact hinnerValid
              have hownerNoReach :
                  ¬ RuntimeFrame.OwnerReaches store (.value value) (.ty ty)
                    ownerLocation := by
                have hvalidOwnerSlot :
                    ValidPartialValueWhenInitialized env₁ store
                      ownerSlot.value (.ty ty) := hinnerValid
                have hno :=
                  ownerReaches_leaf_ne_of_stored_leaf_valid
                    hownedSlot hvalidOwnerSlot
                simpa [hownerSlotValue] using hno
              have hvalidValueFinal :
                  ValidPartialValueWhenInitialized env₂
                    (store.update ownerLocation
                      { ownerSlot with value := .undef })
                    (.value value) (.ty ty) := by
                exact ValidPartialValueWhenInitialized.move_env hmoveOriginal
                  (RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
                    hvalidValueStore
                    (fun reached hreach =>
                      reachesWhenInitialized_chain_leaf_ne_of_no_ownerReaches
                        hsafe hvalidStore hheap
                        (by simpa [LVal.base] using hleafChain)
                        (by
                          intro mutable target hcontains
                          exact LValTyping.contains_borrow hsourceBox
                            (PartialTyContains.box hcontains))
                        hnotWrite hownerNoReach hreach))
              have hleafHeap :
                  ∃ address, ownerLocation = Location.heap address := by
                have hownsLeaf : ProgramStore.Owns store ownerLocation :=
                  ⟨sourceLocation, sourceLifetime,
                    by simpa [owningRef] using hsourceSlot⟩
                exact hheap ownerLocation hownsLeaf
              have hsafeFinal :
                  SafeAbstraction
                    (store.update ownerLocation
                      { ownerSlot with value := .undef })
                    env₂ := by
                refine safeAbstractionWhenInitialized_update_var_partial_of_preserved
                  hmoveSlotBase hrootSlotFinal hrootValidFinal
                  (by simpa [LVal.base] using henv₂) ?domainMove
                  ?preserveMove
                · intro y hyBase
                  have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
                    intro hvarLeaf
                    rcases hleafHeap with ⟨address, hheapLocation⟩
                    rw [← hvarLeaf] at hheapLocation
                    cases hheapLocation
                  constructor
                  · intro hstoreDomain
                    rcases hstoreDomain with ⟨slotY, hslotY⟩
                    have hslotYStore :
                        store.slotAt (VariableProjection y) = some slotY := by
                      simpa [ProgramStore.update, hvarNeLeaf] using hslotY
                    exact (hsafe.1 y).mp ⟨slotY, hslotYStore⟩
                  · intro henvDomain
                    rcases (hsafe.1 y).mpr henvDomain with ⟨slotY, hslotY⟩
                    exact ⟨slotY, by
                      simpa [ProgramStore.update, hvarNeLeaf] using hslotY⟩
                · intro y otherEnvSlot hyBase henvY
                  rcases hsafe.2 y otherEnvSlot henvY with
                    ⟨oldValue, hslotY, hvalidOld⟩
                  have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
                    intro hvarLeaf
                    rcases hleafHeap with ⟨address, hheapLocation⟩
                    rw [← hvarLeaf] at hheapLocation
                    cases hheapLocation
                  have hslotYFinal :
                      (store.update ownerLocation
                        { ownerSlot with value := .undef }).slotAt
                        (VariableProjection y) =
                      some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
                    simpa [ProgramStore.update, hvarNeLeaf] using hslotY
                  have hstorageNeRoot :
                      VariableProjection y ≠
                        VariableProjection (LVal.base source) := by
                    intro hrootEq
                    exact hyBase (by simpa [VariableProjection] using hrootEq)
                  have hownerNoReachOld :
                      ¬ RuntimeFrame.OwnerReaches store oldValue
                        otherEnvSlot.ty ownerLocation :=
                    ownerReaches_stored_ne_chain_leaf hvalidStore
                      hrootUnowned (var_not_owned hheap) hstorageNeRoot
                      (by simpa [LVal.base] using hleafChain) hslotY
                  have hvalidOldFinal :
                      ValidPartialValueWhenInitialized env₂
                        (store.update ownerLocation
                          { ownerSlot with value := .undef })
                        oldValue otherEnvSlot.ty := by
                    exact ValidPartialValueWhenInitialized.move_env hmoveOriginal
                      (RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
                        hvalidOld
                        (fun reached hreach =>
                          reachesWhenInitialized_chain_leaf_ne_of_no_ownerReaches
                            hsafe hvalidStore hheap
                            (by simpa [LVal.base] using hleafChain)
                            (by
                              intro mutable target hcontains
                              exact ⟨y, otherEnvSlot, henvY, hcontains⟩)
                            hnotWrite hownerNoReachOld hreach))
                  exact ⟨oldValue, hslotYFinal, hvalidOldFinal⟩
              exact ⟨validRuntimeState_move_step hvalidRuntime
                  (Step.move (lifetime := lifetime) hread hwrite),
                hsafeFinal, hvalidValueFinal⟩)
    hmulti

theorem preservation_move_deref_boxFull_multistep_runtime_whenInitialized_of_wellFormed
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {source : LVal} {finalValue : Value} {ty : Ty} :
    WellFormedEnvWhenInitialized env₁ lifetime →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.move source.deref) →
    LValTyping env₁ source (.ty (.box ty)) valueLifetime →
    ¬ WriteProhibited env₁ source.deref →
    EnvMove env₁ source.deref env₂ →
    TermTyping env₁ typing lifetime (.move source.deref) ty env₂ →
    MultiStep store lifetime (.move source.deref) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro _hwellFormed hsafe hvalidRuntime hsourceFull hnotWrite hmove htyping
    hmulti
  exact preservation_runtime_multistep_of_step_to_value_whenInitialized
    (term := .move source.deref)
    (env := env₂)
    (ty := ty)
    (by simp [Terminal])
    (by
      intro _store' _term' hstep
      cases hstep with
      | move _hread _hwrite => exact ⟨_, rfl⟩)
    (by
      intro store' value hstep
      cases hstep with
      | move hread hwrite =>
          have hmoveOriginal : EnvMove env₁ source.deref env₂ := hmove
          rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv₂⟩
          have hmoveSlotBase :
              env₁.slotAt (LVal.base source) = some moveSlot := by
            simpa [LVal.base] using hmoveSlot
          have hstrikeSource :
              Strike (LVal.path source ++ [()]) moveSlot.ty struck := by
            simpa [LVal.path] using hstrike
          rcases
              lvalTyping_tyBox_ownerChainPrefix_whenInitialized_of_strike
                hsafe hsourceFull hmoveSlotBase hstrikeSource with
            ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
              hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
              hrootValid, hsourceValid, hprefix⟩
          have hmoveSlotEq : moveSlot = envSlot :=
            Option.some.inj (hmoveSlotBase.symm.trans henvBase)
          subst hmoveSlotEq
          rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
          cases hsourceValid with
          | @boxFull ownerLocation ownerSlot inner hownedSlot hinnerValid =>
              have hderefLoc :
                  store.loc source.deref = some ownerLocation := by
                simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
              have hreadConcrete :
                  store.read source.deref = some ownerSlot := by
                simp [ProgramStore.read, hderefLoc, hownedSlot]
              have hownerSlotValue : ownerSlot.value = .value value := by
                rw [hreadConcrete] at hread
                exact congrArg StoreSlot.value (Option.some.inj hread)
              have hstore' :
                  store' =
                    store.update ownerLocation
                      { ownerSlot with value := .undef } := by
                have hwriteConcrete :
                    store.write source.deref .undef =
                      some
                        (store.update ownerLocation
                          { ownerSlot with value := .undef }) := by
                  simp [ProgramStore.write, hderefLoc, hownedSlot]
                rw [hwriteConcrete] at hwrite
                exact (Option.some.inj hwrite).symm
              subst hstore'
              have hsourceOwner :
                  (StoreSlot.mk
                    (.value (.ref { location := ownerLocation, owner := true }))
                    sourceLifetime).value =
                  .value (.ref { location := ownerLocation, owner := true }) := rfl
              have hprefixExtended :
                  ∃ k,
                    OwnerChainAt store rootSlot.value
                      (LVal.path source ++ [()]) ownerLocation ∧
                    OwnsChain store (VariableProjection (LVal.base source)) k
                      ownerLocation ∧
                    k = (LVal.path source ++ [()]).length :=
                OwnerChainPrefix.extend hprefix
                  (by
                    intro hpathNil
                    have hlocRoot :=
                      ProgramStore.loc_eq_var_of_path_nil
                        (store := store) (lv := source) hpathNil
                    have hlocEq :
                        sourceLocation = VariableProjection (LVal.base source) :=
                      Option.some.inj (hsourceLoc.symm.trans hlocRoot)
                    subst hlocEq
                    have hslotEq :
                        StoreSlot.mk
                            (.value (.ref { location := ownerLocation, owner := true }))
                            sourceLifetime = rootSlot :=
                      Option.some.inj (hsourceSlot.symm.trans hrootSlot)
                    exact congrArg StoreSlot.value hslotEq.symm)
                  hsourceSlot hsourceOwner
              rcases hprefixExtended with
                ⟨k, hchainAt, hleafChain, hchainLen⟩
              have hvalidStore : ValidStore store :=
                ValidRuntimeState.validStore hvalidRuntime
              have hheap : StoreOwnerTargetsHeap store :=
                ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
              have hrootUnowned :
                  ¬ ProgramStore.Owns store
                    (VariableProjection (LVal.base source)) :=
                var_not_owned hheap
              have hrootSlotCur :
                  ∃ rootLifetime,
                    store.slotAt (VariableProjection (LVal.base source)) =
                      some ⟨rootSlot.value, rootLifetime⟩ :=
                ⟨rootSlot.lifetime, by simpa using hrootSlot⟩
              have hstrikePath :
                  Strike (LVal.path source.deref) moveSlot.ty struck := by
                simpa [LVal.path] using hstrike
              have hrootValidFinal :
                  ValidPartialValueWhenInitialized env₂
                    (store.update ownerLocation
                      { ownerSlot with value := .undef })
                    rootSlot.value struck := by
                have hlen :
                    k = 0 + (LVal.path source.deref).length := by
                  simpa [LVal.path] using hchainLen
                exact validPartialValueWhenInitialized_strike_write
                  (env := env₁) (moved := env₂)
                  (rootLoc := VariableProjection (LVal.base source))
                  hvalidStore hrootUnowned hleafChain hownedSlot
                  hstrikePath hrootValid
                  (by simpa [LVal.path] using hchainAt)
                  hrootSlotCur OwnsChain.zero hlen
              have hrootNeLeaf :
                  VariableProjection (LVal.base source) ≠ ownerLocation := by
                intro hEq
                subst hEq
                have hlenEq :=
                  ownsChain_unique_length hvalidStore hrootUnowned hleafChain
                    (OwnsChain.zero
                      (store := store)
                      (location := VariableProjection (LVal.base source)))
                have hpos : 0 < k := by
                  rw [hchainLen]
                  simp
                omega
              have hrootSlotFinal :
                  (store.update ownerLocation
                    { ownerSlot with value := .undef }).slotAt
                      (VariableProjection (LVal.base source)) =
                    some { value := rootSlot.value, lifetime := moveSlot.lifetime } := by
                have hrootSlotEnvLifetime :
                    store.slotAt (VariableProjection (LVal.base source)) =
                      some { value := rootSlot.value, lifetime := moveSlot.lifetime } := by
                  cases rootSlot with
                  | mk rootValue rootLifetime =>
                      have hrootLifetimeMove : rootLifetime = moveSlot.lifetime := by
                        simpa using hrootLifetime
                      cases hrootLifetimeMove
                      simpa using hrootSlot
                simpa [ProgramStore.update, hrootNeLeaf] using hrootSlotEnvLifetime
              have hvalidValueStore :
                  ValidPartialValueWhenInitialized env₁ store
                    (.value value) (.ty ty) := by
                rw [← hownerSlotValue]
                exact hinnerValid
              have hownerNoReach :
                  ¬ RuntimeFrame.OwnerReaches store (.value value) (.ty ty)
                    ownerLocation := by
                have hvalidOwnerSlot :
                    ValidPartialValueWhenInitialized env₁ store
                      ownerSlot.value (.ty ty) := hinnerValid
                have hno :=
                  ownerReaches_leaf_ne_of_stored_leaf_valid
                    hownedSlot hvalidOwnerSlot
                simpa [hownerSlotValue] using hno
              have hvalidValueFinal :
                  ValidPartialValueWhenInitialized env₂
                    (store.update ownerLocation
                      { ownerSlot with value := .undef })
                    (.value value) (.ty ty) := by
                exact ValidPartialValueWhenInitialized.move_env hmoveOriginal
                  (RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
                    hvalidValueStore
                    (fun reached hreach =>
                      reachesWhenInitialized_chain_leaf_ne_of_no_ownerReaches
                        hsafe hvalidStore hheap
                        (by simpa [LVal.base] using hleafChain)
                        (by
                          intro mutable target hcontains
                          exact LValTyping.contains_borrow hsourceFull
                            (PartialTyContains.tyBox hcontains))
                        hnotWrite hownerNoReach hreach))
              have hleafHeap :
                  ∃ address, ownerLocation = Location.heap address := by
                have hownsLeaf : ProgramStore.Owns store ownerLocation :=
                  ⟨sourceLocation, sourceLifetime,
                    by simpa [owningRef] using hsourceSlot⟩
                exact hheap ownerLocation hownsLeaf
              have hsafeFinal :
                  SafeAbstraction
                    (store.update ownerLocation
                      { ownerSlot with value := .undef })
                    env₂ := by
                refine safeAbstractionWhenInitialized_update_var_partial_of_preserved
                  hmoveSlotBase hrootSlotFinal hrootValidFinal
                  (by simpa [LVal.base] using henv₂) ?domainMove
                  ?preserveMove
                · intro y hyBase
                  have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
                    intro hvarLeaf
                    rcases hleafHeap with ⟨address, hheapLocation⟩
                    rw [← hvarLeaf] at hheapLocation
                    cases hheapLocation
                  constructor
                  · intro hstoreDomain
                    rcases hstoreDomain with ⟨slotY, hslotY⟩
                    have hslotYStore :
                        store.slotAt (VariableProjection y) = some slotY := by
                      simpa [ProgramStore.update, hvarNeLeaf] using hslotY
                    exact (hsafe.1 y).mp ⟨slotY, hslotYStore⟩
                  · intro henvDomain
                    rcases (hsafe.1 y).mpr henvDomain with ⟨slotY, hslotY⟩
                    exact ⟨slotY, by
                      simpa [ProgramStore.update, hvarNeLeaf] using hslotY⟩
                · intro y otherEnvSlot hyBase henvY
                  rcases hsafe.2 y otherEnvSlot henvY with
                    ⟨oldValue, hslotY, hvalidOld⟩
                  have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
                    intro hvarLeaf
                    rcases hleafHeap with ⟨address, hheapLocation⟩
                    rw [← hvarLeaf] at hheapLocation
                    cases hheapLocation
                  have hslotYFinal :
                      (store.update ownerLocation
                        { ownerSlot with value := .undef }).slotAt
                        (VariableProjection y) =
                      some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
                    simpa [ProgramStore.update, hvarNeLeaf] using hslotY
                  have hstorageNeRoot :
                      VariableProjection y ≠
                        VariableProjection (LVal.base source) := by
                    intro hrootEq
                    exact hyBase (by simpa [VariableProjection] using hrootEq)
                  have hownerNoReachOld :
                      ¬ RuntimeFrame.OwnerReaches store oldValue
                        otherEnvSlot.ty ownerLocation :=
                    ownerReaches_stored_ne_chain_leaf hvalidStore
                      hrootUnowned (var_not_owned hheap) hstorageNeRoot
                      (by simpa [LVal.base] using hleafChain) hslotY
                  have hvalidOldFinal :
                      ValidPartialValueWhenInitialized env₂
                        (store.update ownerLocation
                          { ownerSlot with value := .undef })
                        oldValue otherEnvSlot.ty := by
                    exact ValidPartialValueWhenInitialized.move_env hmoveOriginal
                      (RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
                        hvalidOld
                        (fun reached hreach =>
                          reachesWhenInitialized_chain_leaf_ne_of_no_ownerReaches
                            hsafe hvalidStore hheap
                            (by simpa [LVal.base] using hleafChain)
                            (by
                              intro mutable target hcontains
                              exact ⟨y, otherEnvSlot, henvY, hcontains⟩)
                            hnotWrite hownerNoReachOld hreach))
                  exact ⟨oldValue, hslotYFinal, hvalidOldFinal⟩
              exact ⟨validRuntimeState_move_step hvalidRuntime
                  (Step.move (lifetime := lifetime) hread hwrite),
                hsafeFinal, hvalidValueFinal⟩)
    hmulti

theorem preservation_assign_deref_box_step_runtime_whenInitialized_of_frames
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime : Lifetime} {source : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    ContainedBorrowsWellFormed env →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign source.deref (.val value)) →
    LValTyping env source (.box oldTy) targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite env source.deref rhsTy env' →
    WellFormedEnvWhenInitialized env' lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign source.deref (.val value)) store'
      (.val finalValue) →
    ValidPartialValueWhenInitialized env' store (.value value) (.ty rhsTy) →
    (∀ y otherEnvSlot oldValue,
      y ≠ LVal.base source →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ValidPartialValueWhenInitialized env' store oldValue otherEnvSlot.ty) →
    (∀ location,
      RuntimeFrame.ReachesWhenInitialized env' store (.value value) (.ty rhsTy)
        location →
      location ≠
        (match store.loc source.deref with
        | some location => location
        | none => VariableProjection (LVal.base source))) →
    (∀ y otherEnvSlot oldValue,
      y ≠ LVal.base source →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.ReachesWhenInitialized env' store oldValue
          otherEnvSlot.ty location →
        location ≠
          (match store.loc source.deref with
          | some location => location
          | none => VariableProjection (LVal.base source))) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hcbwf hborrowSafe htySafe hsafe hvalidRuntime hsourceBox hshape
    hwellTy hwriteEnv hwellOut hvalidValue hstep hvalidValueEnv'
    hotherValidEnv' hvalueFrame hotherFrame
  rcases assign_step_components hstep with
    ⟨writtenStore, oldSlot, lhsLocation, hread, hwriteStore, hdrops,
      hlhsLoc, hlhsSlot, hwriteStoreEq, hresult⟩
  cases hresult
  have hwriteEq :
      writtenStore =
        store.update lhsLocation { oldSlot with value := .value value } := by
    simpa using hwriteStoreEq
  rcases
      lvalTyping_box_ownerChainPrefix_whenInitialized hsafe hsourceBox with
    ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
      hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
      hrootValid, hsourceValid, hprefix⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hsourceValid with
  | @box ownerLocation ownerSlot inner hownedSlot hinnerValid =>
      have hderefLoc :
          store.loc source.deref = some ownerLocation := by
        simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
      have hlhsEq : lhsLocation = ownerLocation := by
        exact Option.some.inj (hlhsLoc.symm.trans hderefLoc)
      subst lhsLocation
      have hownerSlotEq : ownerSlot = oldSlot :=
        Option.some.inj (hownedSlot.symm.trans hlhsSlot)
      subst ownerSlot
      rcases EnvWrite.deref_box_result_contains hsourceBox hwriteEnv with
        ⟨writeSlot, updatedTy, hwriteBase, hupdatePath, henv',
          hcontainsRhsResult⟩
      have hwriteSlotEq : writeSlot = envSlot :=
        Option.some.inj (hwriteBase.symm.trans henvBase)
      subst writeSlot
      have hsourceOwner :
          (StoreSlot.mk
            (.value (.ref { location := ownerLocation, owner := true }))
            sourceLifetime).value =
          .value (.ref { location := ownerLocation, owner := true }) := rfl
      have hprefixExtended :
          ∃ k,
            OwnerChainAt store rootSlot.value
              (LVal.path source ++ [()]) ownerLocation ∧
            OwnsChain store (VariableProjection (LVal.base source)) k
              ownerLocation ∧
            k = (LVal.path source ++ [()]).length :=
        OwnerChainPrefix.extend hprefix
          (by
            intro hpathNil
            have hlocRoot :=
              ProgramStore.loc_eq_var_of_path_nil
                (store := store) (lv := source) hpathNil
            have hlocEq :
                sourceLocation = VariableProjection (LVal.base source) :=
              Option.some.inj (hsourceLoc.symm.trans hlocRoot)
            subst hlocEq
            have hslotEq :
                StoreSlot.mk
                    (.value (.ref { location := ownerLocation, owner := true }))
                    sourceLifetime = rootSlot :=
              Option.some.inj (hsourceSlot.symm.trans hrootSlot)
            exact congrArg StoreSlot.value hslotEq.symm)
          hsourceSlot hsourceOwner
      rcases hprefixExtended with ⟨k, hchainAt, hleafChain, hchainLen⟩
      have hvalidStore : ValidStore store :=
        ValidRuntimeState.validStore hvalidRuntime
      have hheap : StoreOwnerTargetsHeap store :=
        ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
      have hrootUnowned :
          ¬ ProgramStore.Owns store
            (VariableProjection (LVal.base source)) :=
        var_not_owned hheap
      have hrootSlotCur :
          ∃ rootLifetime,
            store.slotAt (VariableProjection (LVal.base source)) =
              some ⟨rootSlot.value, rootLifetime⟩ :=
        ⟨rootSlot.lifetime, by simpa using hrootSlot⟩
      have hvalidValueWritten :
          ValidPartialValueWhenInitialized env' writtenStore (.value value)
            (.ty rhsTy) := by
        rw [hwriteEq]
        exact RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
          hvalidValueEnv'
          (by
            intro location hreach
            have hframe := hvalueFrame location hreach
            simpa [hderefLoc] using hframe)
      have hrootValidFinal :
          ValidPartialValueWhenInitialized env' writtenStore rootSlot.value
            updatedTy := by
        rw [hwriteEq]
        have hlen :
            k = 0 + (LVal.path source.deref).length := by
          simpa [LVal.path] using hchainLen
        exact validPartialValueWhenInitialized_updateAtPath_write
          (env := env) (resultEnv := env')
          (rootLoc := VariableProjection (LVal.base source))
          hvalidStore hrootUnowned hleafChain hownedSlot hupdatePath
          hrootValid
          (by simpa [LVal.path] using hchainAt)
          hrootSlotCur OwnsChain.zero hlen
          (by simpa [hwriteEq] using hvalidValueWritten)
      have hrootNeLeaf :
          VariableProjection (LVal.base source) ≠ ownerLocation := by
        intro hEq
        subst hEq
        have hlenEq :=
          ownsChain_unique_length hvalidStore hrootUnowned hleafChain
            (OwnsChain.zero
              (store := store)
              (location := VariableProjection (LVal.base source)))
        have hpos : 0 < k := by
          rw [hchainLen]
          simp
        omega
      have hrootSlotFinal :
          writtenStore.slotAt (VariableProjection (LVal.base source)) =
            some { value := rootSlot.value, lifetime := envSlot.lifetime } := by
        rw [hwriteEq]
        cases rootSlot with
        | mk rootValue rootLifetime =>
            have hrootLifetimeEnv : rootLifetime = envSlot.lifetime := by
              simpa using hrootLifetime
            cases hrootLifetimeEnv
            simpa [ProgramStore.update, hrootNeLeaf] using hrootSlot
      have hleafHeap :
          ∃ address, ownerLocation = Location.heap address := by
        have hownsLeaf : ProgramStore.Owns store ownerLocation :=
          ⟨sourceLocation, sourceLifetime,
            by simpa [owningRef] using hsourceSlot⟩
        exact hheap ownerLocation hownsLeaf
      have hsafeWrite : SafeAbstraction writtenStore env' := by
        refine safeAbstractionWhenInitialized_update_var_partial_of_preserved
          henvBase hrootSlotFinal hrootValidFinal henv' ?domainWrite
          ?preserveWrite
        · intro y hyBase
          have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
            intro hvarLeaf
            rcases hleafHeap with ⟨address, hheapLocation⟩
            rw [← hvarLeaf] at hheapLocation
            cases hheapLocation
          constructor
          · intro hstoreDomain
            rcases hstoreDomain with ⟨slotY, hslotY⟩
            have hslotYStore :
                store.slotAt (VariableProjection y) = some slotY := by
              rw [hwriteEq] at hslotY
              simpa [ProgramStore.update, hvarNeLeaf] using hslotY
            exact (hsafe.1 y).mp ⟨slotY, hslotYStore⟩
          · intro henvDomain
            rcases (hsafe.1 y).mpr henvDomain with ⟨slotY, hslotY⟩
            exact ⟨slotY, by
              rw [hwriteEq]
              simpa [ProgramStore.update, hvarNeLeaf] using hslotY⟩
        · intro y otherEnvSlot hyBase henvY
          rcases hsafe.2 y otherEnvSlot henvY with
            ⟨oldValue, hstoreY, hvalidOld⟩
          have hvalidOldEnv' :
              ValidPartialValueWhenInitialized env' store oldValue
                otherEnvSlot.ty :=
            hotherValidEnv' y otherEnvSlot oldValue hyBase henvY hstoreY
          have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
            intro hvarLeaf
            rcases hleafHeap with ⟨address, hheapLocation⟩
            rw [← hvarLeaf] at hheapLocation
            cases hheapLocation
          have hstoreYWritten :
              writtenStore.slotAt (VariableProjection y) =
                some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
            rw [hwriteEq]
            simpa [ProgramStore.update, hvarNeLeaf] using hstoreY
          have hvalidOldWritten :
              ValidPartialValueWhenInitialized env' writtenStore oldValue
                otherEnvSlot.ty := by
            rw [hwriteEq]
            exact RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
              hvalidOldEnv'
              (by
                intro location hreach
                have hframe :=
                  hotherFrame y otherEnvSlot oldValue hyBase henvY hstoreY
                    location hreach
                simpa [hderefLoc] using hframe)
          exact ⟨oldValue, hstoreYWritten, hvalidOldWritten⟩
      have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
        ValueOwnerTargetsHeap.partial
          (TermOwnerTargetsHeap.value
            (termOwnerTargetsHeap_assign_inner
              (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
      have hnewDisjoint :
          ∀ owned, owned ∈ partialValueOwningLocations (.value value) →
            ¬ ProgramStore.Owns store owned := by
        intro owned hmem
        exact
          (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
            (by
              simpa [termOwningLocations, termValues,
                partialValueOwningLocations] using hmem))
      have hwrittenValidStore : ValidStore writtenStore :=
        validStore_write_disjoint hvalidStore hnewDisjoint hwriteStore
      have hwrittenHeap : StoreOwnerTargetsHeap writtenStore :=
        storeOwnerTargetsHeap_write hheap hvalueHeap hwriteStore
      have hdropValuesHeap :
          ∀ dropValue, dropValue ∈ [oldSlot.value] →
            PartialValueOwnerTargetsHeap dropValue := by
        intro dropValue hmem
        simp at hmem
        subst hmem
        exact partialValueOwnerTargetsHeap_of_slot hheap hlhsSlot
      have hdropOwnersOrphaned :
          ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
            ¬ ProgramStore.Owns writtenStore owned :=
        droppedValueOwnersOrphaned_assign hvalidRuntime hlhsLoc hlhsSlot
          hwriteStore
      have hallocatedWrite : StoreOwnersAllocated writtenStore :=
        storeOwnersAllocated_write_value_of_validValueWhenInitialized
          (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
          hwriteStore
      have hrootWrite : HeapSlotsRootLifetime writtenStore :=
        heapSlotsRootLifetime_write
          (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
      have hallocatedFinal : StoreOwnersAllocated store' :=
        drops_storeOwnersAllocated_of_disjoint hdrops hwrittenValidStore
          hallocatedWrite hdropOwnersOrphaned
      have hheapFinal : StoreOwnerTargetsHeap store' :=
        drops_storeOwnerTargetsHeap hdrops hwrittenHeap
      have hrootFinal : HeapSlotsRootLifetime store' :=
        drops_heapSlotsRootLifetime hdrops hrootWrite
      have hsafeFinal : SafeAbstraction store' env' :=
        safeAbstractionWhenInitialized_drops_of_orphaned_values_early
          hwellOut hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap
          hdropOwnersOrphaned hdrops
      exact ⟨validRuntimeState_assign_step_of_postWriteDrop_invariants
          (lifetime := lifetime)
          hvalidRuntime hallocatedFinal hheapFinal hrootFinal hread
          hwriteStore hdrops,
        hsafeFinal, ValidPartialValueWhenInitialized.unit⟩

theorem preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_frames
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime : Lifetime} {source : LVal}
    {oldTy : Ty} {value finalValue : Value} {rhsTy : Ty} :
    ContainedBorrowsWellFormed env →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign source.deref (.val value)) →
    LValTyping env source (.ty (.box oldTy)) targetLifetime →
    ShapeCompatible env (.ty oldTy) (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite env source.deref rhsTy env' →
    WellFormedEnvWhenInitialized env' lifetime →
    (∀ {slot : EnvSlot},
      env.slotAt (LVal.base source) = some slot →
      PathSelect (LVal.path source) slot.ty (.ty (.box oldTy))) →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign source.deref (.val value)) store'
      (.val finalValue) →
    ValidPartialValueWhenInitialized env' store (.value value) (.ty rhsTy) →
    (∀ y otherEnvSlot oldValue,
      y ≠ LVal.base source →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ValidPartialValueWhenInitialized env' store oldValue otherEnvSlot.ty) →
    (∀ location,
      RuntimeFrame.ReachesWhenInitialized env' store (.value value) (.ty rhsTy)
        location →
      location ≠
        (match store.loc source.deref with
        | some location => location
        | none => VariableProjection (LVal.base source))) →
    (∀ y otherEnvSlot oldValue,
      y ≠ LVal.base source →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.ReachesWhenInitialized env' store oldValue
          otherEnvSlot.ty location →
        location ≠
          (match store.loc source.deref with
          | some location => location
          | none => VariableProjection (LVal.base source))) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hcbwf hborrowSafe htySafe hsafe hvalidRuntime hsourceFull hshape
    hwellTy hwriteEnv hwellOut hselectSource hvalidValue hstep
    hvalidValueEnv' hotherValidEnv' hvalueFrame hotherFrame
  rcases assign_step_components hstep with
    ⟨writtenStore, oldSlot, lhsLocation, hread, hwriteStore, hdrops,
      hlhsLoc, hlhsSlot, hwriteStoreEq, hresult⟩
  cases hresult
  have hwriteEq :
      writtenStore =
        store.update lhsLocation { oldSlot with value := .value value } := by
    simpa using hwriteStoreEq
  rcases LValTyping.base_slot_exists hsourceFull with
    ⟨baseSlot, hbaseSlot⟩
  have hselectDeref :
      PathSelect (LVal.path source.deref) baseSlot.ty (.ty oldTy) := by
    simpa [LVal.path] using PathSelect.snoc_boxFull
      (hselectSource hbaseSlot)
  rcases PathSelect.exists_strike_undef hselectDeref with
    ⟨struck, hstrikeDeref⟩
  have hstrikeSource :
      Strike (LVal.path source ++ [()]) baseSlot.ty struck := by
    simpa [LVal.path] using hstrikeDeref
  rcases
      lvalTyping_tyBox_ownerChainPrefix_whenInitialized_of_strike
        hsafe hsourceFull hbaseSlot hstrikeSource with
    ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
      hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
      hrootValid, hsourceValid, hprefix⟩
  have hbaseSlotEq : baseSlot = envSlot :=
    Option.some.inj (hbaseSlot.symm.trans henvBase)
  subst hbaseSlotEq
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hsourceValid with
  | @boxFull ownerLocation ownerSlot inner hownedSlot hinnerValid =>
      have hderefLoc :
          store.loc source.deref = some ownerLocation := by
        simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
      have hlhsEq : lhsLocation = ownerLocation := by
        exact Option.some.inj (hlhsLoc.symm.trans hderefLoc)
      subst lhsLocation
      have hownerSlotEq : ownerSlot = oldSlot :=
        Option.some.inj (hownedSlot.symm.trans hlhsSlot)
      subst ownerSlot
      rcases EnvWrite.deref_boxFull_result_contains_of_select henvBase
          (hselectSource henvBase) hwriteEnv with
        ⟨updatedTy, hupdatePath, henv', hcontainsRhsResult⟩
      have hsourceOwner :
          (StoreSlot.mk
            (.value (.ref { location := ownerLocation, owner := true }))
            sourceLifetime).value =
          .value (.ref { location := ownerLocation, owner := true }) := rfl
      have hprefixExtended :
          ∃ k,
            OwnerChainAt store rootSlot.value
              (LVal.path source ++ [()]) ownerLocation ∧
            OwnsChain store (VariableProjection (LVal.base source)) k
              ownerLocation ∧
            k = (LVal.path source ++ [()]).length :=
        OwnerChainPrefix.extend hprefix
          (by
            intro hpathNil
            have hlocRoot :=
              ProgramStore.loc_eq_var_of_path_nil
                (store := store) (lv := source) hpathNil
            have hlocEq :
                sourceLocation = VariableProjection (LVal.base source) :=
              Option.some.inj (hsourceLoc.symm.trans hlocRoot)
            subst hlocEq
            have hslotEq :
                StoreSlot.mk
                    (.value (.ref { location := ownerLocation, owner := true }))
                    sourceLifetime = rootSlot :=
              Option.some.inj (hsourceSlot.symm.trans hrootSlot)
            exact congrArg StoreSlot.value hslotEq.symm)
          hsourceSlot hsourceOwner
      rcases hprefixExtended with ⟨k, hchainAt, hleafChain, hchainLen⟩
      have hvalidStore : ValidStore store :=
        ValidRuntimeState.validStore hvalidRuntime
      have hheap : StoreOwnerTargetsHeap store :=
        ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
      have hrootUnowned :
          ¬ ProgramStore.Owns store
            (VariableProjection (LVal.base source)) :=
        var_not_owned hheap
      have hrootSlotCur :
          ∃ rootLifetime,
            store.slotAt (VariableProjection (LVal.base source)) =
              some ⟨rootSlot.value, rootLifetime⟩ :=
        ⟨rootSlot.lifetime, by simpa using hrootSlot⟩
      have hvalidValueWritten :
          ValidPartialValueWhenInitialized env' writtenStore (.value value)
            (.ty rhsTy) := by
        rw [hwriteEq]
        exact RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
          hvalidValueEnv'
          (by
            intro location hreach
            have hframe := hvalueFrame location hreach
            simpa [hderefLoc] using hframe)
      have hrootValidFinal :
          ValidPartialValueWhenInitialized env' writtenStore rootSlot.value
            updatedTy := by
        rw [hwriteEq]
        have hlen :
            k = 0 + (LVal.path source.deref).length := by
          simpa [LVal.path] using hchainLen
        exact validPartialValueWhenInitialized_updateAtPath_write
          (env := env) (resultEnv := env')
          (rootLoc := VariableProjection (LVal.base source))
          hvalidStore hrootUnowned hleafChain hownedSlot hupdatePath
          hrootValid
          (by simpa [LVal.path] using hchainAt)
          hrootSlotCur OwnsChain.zero hlen
          (by simpa [hwriteEq] using hvalidValueWritten)
      have hrootNeLeaf :
          VariableProjection (LVal.base source) ≠ ownerLocation := by
        intro hEq
        subst hEq
        have hlenEq :=
          ownsChain_unique_length hvalidStore hrootUnowned hleafChain
            (OwnsChain.zero
              (store := store)
              (location := VariableProjection (LVal.base source)))
        have hpos : 0 < k := by
          rw [hchainLen]
          simp
        omega
      have hrootSlotFinal :
          writtenStore.slotAt (VariableProjection (LVal.base source)) =
            some { value := rootSlot.value, lifetime := baseSlot.lifetime } := by
        rw [hwriteEq]
        cases rootSlot with
        | mk rootValue rootLifetime =>
            have hrootLifetimeEnv : rootLifetime = baseSlot.lifetime := by
              simpa using hrootLifetime
            cases hrootLifetimeEnv
            simpa [ProgramStore.update, hrootNeLeaf] using hrootSlot
      have hleafHeap :
          ∃ address, ownerLocation = Location.heap address := by
        have hownsLeaf : ProgramStore.Owns store ownerLocation :=
          ⟨sourceLocation, sourceLifetime,
            by simpa [owningRef] using hsourceSlot⟩
        exact hheap ownerLocation hownsLeaf
      have hsafeWrite : SafeAbstraction writtenStore env' := by
        refine safeAbstractionWhenInitialized_update_var_partial_of_preserved
          henvBase hrootSlotFinal hrootValidFinal henv' ?domainWrite
          ?preserveWrite
        · intro y hyBase
          have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
            intro hvarLeaf
            rcases hleafHeap with ⟨address, hheapLocation⟩
            rw [← hvarLeaf] at hheapLocation
            cases hheapLocation
          constructor
          · intro hstoreDomain
            rcases hstoreDomain with ⟨slotY, hslotY⟩
            have hslotYStore :
                store.slotAt (VariableProjection y) = some slotY := by
              rw [hwriteEq] at hslotY
              simpa [ProgramStore.update, hvarNeLeaf] using hslotY
            exact (hsafe.1 y).mp ⟨slotY, hslotYStore⟩
          · intro henvDomain
            rcases (hsafe.1 y).mpr henvDomain with ⟨slotY, hslotY⟩
            exact ⟨slotY, by
              rw [hwriteEq]
              simpa [ProgramStore.update, hvarNeLeaf] using hslotY⟩
        · intro y otherEnvSlot hyBase henvY
          rcases hsafe.2 y otherEnvSlot henvY with
            ⟨oldValue, hstoreY, hvalidOld⟩
          have hvalidOldEnv' :
              ValidPartialValueWhenInitialized env' store oldValue
                otherEnvSlot.ty :=
            hotherValidEnv' y otherEnvSlot oldValue hyBase henvY hstoreY
          have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
            intro hvarLeaf
            rcases hleafHeap with ⟨address, hheapLocation⟩
            rw [← hvarLeaf] at hheapLocation
            cases hheapLocation
          have hstoreYWritten :
              writtenStore.slotAt (VariableProjection y) =
                some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
            rw [hwriteEq]
            simpa [ProgramStore.update, hvarNeLeaf] using hstoreY
          have hvalidOldWritten :
              ValidPartialValueWhenInitialized env' writtenStore oldValue
                otherEnvSlot.ty := by
            rw [hwriteEq]
            exact RuntimeFrame.validPartialValueWhenInitialized_update_of_not_live_reaches
              hvalidOldEnv'
              (by
                intro location hreach
                have hframe :=
                  hotherFrame y otherEnvSlot oldValue hyBase henvY hstoreY
                    location hreach
                simpa [hderefLoc] using hframe)
          exact ⟨oldValue, hstoreYWritten, hvalidOldWritten⟩
      have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
        ValueOwnerTargetsHeap.partial
          (TermOwnerTargetsHeap.value
            (termOwnerTargetsHeap_assign_inner
              (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)))
      have hnewDisjoint :
          ∀ owned, owned ∈ partialValueOwningLocations (.value value) →
            ¬ ProgramStore.Owns store owned := by
        intro owned hmem
        exact
          (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
            (by
              simpa [termOwningLocations, termValues,
                partialValueOwningLocations] using hmem))
      have hwrittenValidStore : ValidStore writtenStore :=
        validStore_write_disjoint hvalidStore hnewDisjoint hwriteStore
      have hwrittenHeap : StoreOwnerTargetsHeap writtenStore :=
        storeOwnerTargetsHeap_write hheap hvalueHeap hwriteStore
      have hdropValuesHeap :
          ∀ dropValue, dropValue ∈ [oldSlot.value] →
            PartialValueOwnerTargetsHeap dropValue := by
        intro dropValue hmem
        simp at hmem
        subst hmem
        exact partialValueOwnerTargetsHeap_of_slot hheap hlhsSlot
      have hdropOwnersOrphaned :
          ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
            ¬ ProgramStore.Owns writtenStore owned :=
        droppedValueOwnersOrphaned_assign hvalidRuntime hlhsLoc hlhsSlot
          hwriteStore
      have hallocatedWrite : StoreOwnersAllocated writtenStore :=
        storeOwnersAllocated_write_value_of_validValueWhenInitialized
          (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
          hwriteStore
      have hrootWrite : HeapSlotsRootLifetime writtenStore :=
        heapSlotsRootLifetime_write
          (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
      have hallocatedFinal : StoreOwnersAllocated store' :=
        drops_storeOwnersAllocated_of_disjoint hdrops hwrittenValidStore
          hallocatedWrite hdropOwnersOrphaned
      have hheapFinal : StoreOwnerTargetsHeap store' :=
        drops_storeOwnerTargetsHeap hdrops hwrittenHeap
      have hrootFinal : HeapSlotsRootLifetime store' :=
        drops_heapSlotsRootLifetime hdrops hrootWrite
      have hsafeFinal : SafeAbstraction store' env' :=
        safeAbstractionWhenInitialized_drops_of_orphaned_values_early
          hwellOut hsafeWrite hwrittenValidStore hwrittenHeap hdropValuesHeap
          hdropOwnersOrphaned hdrops
      exact ⟨validRuntimeState_assign_step_of_postWriteDrop_invariants
          (lifetime := lifetime)
          hvalidRuntime hallocatedFinal hheapFinal hrootFinal hread
          hwriteStore hdrops,
        hsafeFinal, ValidPartialValueWhenInitialized.unit⟩

theorem preservation_assign_deref_box_step_runtime_whenInitialized_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime : Lifetime} {source : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign source.deref (.val value)) →
    LValTyping env source (.box oldTy) targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite env source.deref rhsTy env' →
    ¬ WriteProhibited env' source.deref →
    WellFormedEnv env' lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign source.deref (.val value)) store'
      (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hsourceBox hshape
    hwellTy hwriteEnv hnotWrite hwellOut hvalidValue hstep
  rcases
      lvalTyping_box_ownerChainPrefix_whenInitialized hsafe hsourceBox with
    ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
      hrootSlot, _hrootLifetime, hsourceLoc, hsourceSlot,
      _hrootValid, hsourceValid, hprefix⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hsourceValid with
  | @box ownerLocation ownerSlot inner hownedSlot _hinnerValid =>
      have hderefLoc :
          store.loc source.deref = some ownerLocation := by
        simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
      have hsourceOwner :
          (StoreSlot.mk
            (.value (.ref { location := ownerLocation, owner := true }))
            sourceLifetime).value =
          .value (.ref { location := ownerLocation, owner := true }) := rfl
      have hprefixExtended :
          ∃ k,
            OwnerChainAt store rootSlot.value
              (LVal.path source ++ [()]) ownerLocation ∧
            OwnsChain store (VariableProjection (LVal.base source)) k
              ownerLocation ∧
            k = (LVal.path source ++ [()]).length :=
        OwnerChainPrefix.extend hprefix
          (by
            intro hpathNil
            have hlocRoot :=
              ProgramStore.loc_eq_var_of_path_nil
                (store := store) (lv := source) hpathNil
            have hlocEq :
                sourceLocation = VariableProjection (LVal.base source) :=
              Option.some.inj (hsourceLoc.symm.trans hlocRoot)
            subst hlocEq
            have hslotEq :
                StoreSlot.mk
                    (.value (.ref { location := ownerLocation, owner := true }))
                    sourceLifetime = rootSlot :=
              Option.some.inj (hsourceSlot.symm.trans hrootSlot)
            exact congrArg StoreSlot.value hslotEq.symm)
          hsourceSlot hsourceOwner
      rcases hprefixExtended with ⟨k, _hchainAt, hleafChain, _hchainLen⟩
      rcases EnvWrite.deref_box_result_contains hsourceBox hwriteEnv with
        ⟨writeSlot, updatedTy, hwriteBase, _hupdatePath, henv',
          hcontainsRhsResult⟩
      have hwriteSlotEq : writeSlot = envSlot :=
        Option.some.inj (hwriteBase.symm.trans henvBase)
      subst writeSlot
      have hvalidStore : ValidStore store :=
        ValidRuntimeState.validStore hvalidRuntime
      have hheap : StoreOwnerTargetsHeap store :=
        ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
      have hvalueHeap : ValueOwnerTargetsHeap value :=
        TermOwnerTargetsHeap.value
          (termOwnerTargetsHeap_assign_inner
            (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
      have hvalueUnowned :
          ∀ owned, owned ∈ valueOwningLocations value →
            ¬ ProgramStore.Owns store owned := by
        intro owned hmem
        exact
          (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
            (by
              simpa [termOwningLocations, termValues,
                partialValueOwningLocations] using hmem))
      have hvalueOwnerNoReach :
          ¬ RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy)
            ownerLocation :=
        ownerReaches_value_ne_chain_leaf_of_unowned_root
          hvalidStore hheap hvalueHeap hvalueUnowned
          (by simpa [LVal.base, VariableProjection] using hleafChain)
      have hvalidValueEnv' :
          ValidPartialValueWhenInitialized env' store (.value value)
            (.ty rhsTy) :=
        validPartialValueWhenInitialized_envWrite_of_result_contains
          hwell.1 hborrowSafe htySafe hwriteEnv (LValTyping.box hsourceBox)
          hshape hwellTy hnotWrite
          (by
            intro mutable target hcontains
            exact ⟨LVal.base source, hcontainsRhsResult hcontains⟩)
          hvalidValue
      exact
        preservation_assign_deref_box_step_runtime_whenInitialized_of_frames
          hwell.1 hborrowSafe htySafe hsafe hvalidRuntime hsourceBox hshape
          hwellTy hwriteEnv (WellFormedEnv.whenInitialized hwellOut)
          hvalidValue hstep hvalidValueEnv'
          (by
            intro y otherEnvSlot oldValue hyBase henvY hstoreY
            rcases hsafe.2 y otherEnvSlot henvY with
              ⟨safeValue, hsafeStoreY, hvalidOld⟩
            have hvalueEq : safeValue = oldValue := by
              have hslotEq :=
                Option.some.inj (hsafeStoreY.symm.trans hstoreY)
              exact congrArg StoreSlot.value hslotEq
            subst hvalueEq
            have henvY' : env'.slotAt y = some otherEnvSlot := by
              rw [henv']
              simpa [Env.update, hyBase] using henvY
            exact
              validPartialValueWhenInitialized_envWrite_of_result_contains
                hwell.1 hborrowSafe htySafe hwriteEnv
                (LValTyping.box hsourceBox) hshape hwellTy hnotWrite
                (by
                  intro mutable target hcontains
                  exact ⟨y, otherEnvSlot, henvY', hcontains⟩)
                hvalidOld)
          (by
            intro location hreach
            have hne :
                location ≠ ownerLocation :=
              reachesWhenInitialized_chain_leaf_ne_of_update_var_not_writeProhibited
                hsafe hvalidStore hheap
                (by simpa [LVal.base] using henv') hnotWrite
                (by simpa [LVal.base, VariableProjection] using hleafChain)
                (by
                  intro mutable target hcontains
                  exact ⟨LVal.base source, hcontainsRhsResult hcontains⟩)
                hvalueOwnerNoReach hreach
            simpa [hderefLoc] using hne)
          (by
            intro y otherEnvSlot oldValue hyBase henvY hstoreY location
              hreach
            have henvY' : env'.slotAt y = some otherEnvSlot := by
              rw [henv']
              simpa [Env.update, hyBase] using henvY
            have hstorageNeRoot :
                VariableProjection y ≠
                  VariableProjection (LVal.base source) := by
              intro hrootEq
              exact hyBase (by simpa [VariableProjection] using hrootEq)
            have hownerNoReachOld :
                ¬ RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty
                  ownerLocation :=
              ownerReaches_stored_ne_chain_leaf hvalidStore
                (var_not_owned hheap) (var_not_owned hheap) hstorageNeRoot
                (by simpa [LVal.base, VariableProjection] using hleafChain)
                hstoreY
            have hne :
                location ≠ ownerLocation :=
              reachesWhenInitialized_chain_leaf_ne_of_update_var_not_writeProhibited
                hsafe hvalidStore hheap
                (by simpa [LVal.base] using henv') hnotWrite
                (by simpa [LVal.base, VariableProjection] using hleafChain)
                (by
                  intro mutable target hcontains
                  exact ⟨y, otherEnvSlot, henvY', hcontains⟩)
                hownerNoReachOld hreach
            simpa [hderefLoc] using hne)

theorem preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_wellFormed_of_select
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime : Lifetime} {source : LVal}
    {oldTy : Ty} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign source.deref (.val value)) →
    LValTyping env source (.ty (.box oldTy)) targetLifetime →
    ShapeCompatible env (.ty oldTy) (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite env source.deref rhsTy env' →
    ¬ WriteProhibited env' source.deref →
    WellFormedEnv env' lifetime →
    (∀ {slot : EnvSlot},
      env.slotAt (LVal.base source) = some slot →
      PathSelect (LVal.path source) slot.ty (.ty (.box oldTy))) →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign source.deref (.val value)) store'
      (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hsourceFull hshape
    hwellTy hwriteEnv hnotWrite hwellOut hselectSource hvalidValue hstep
  rcases LValTyping.base_slot_exists hsourceFull with
    ⟨baseSlot, hbaseSlot⟩
  have hselectDeref :
      PathSelect (LVal.path source.deref) baseSlot.ty (.ty oldTy) := by
    simpa [LVal.path] using PathSelect.snoc_boxFull
      (hselectSource hbaseSlot)
  rcases PathSelect.exists_strike_undef hselectDeref with
    ⟨struck, hstrikeDeref⟩
  have hstrikeSource :
      Strike (LVal.path source ++ [()]) baseSlot.ty struck := by
    simpa [LVal.path] using hstrikeDeref
  rcases
      lvalTyping_tyBox_ownerChainPrefix_whenInitialized_of_strike
        hsafe hsourceFull hbaseSlot hstrikeSource with
    ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
      hrootSlot, _hrootLifetime, hsourceLoc, hsourceSlot,
      _hrootValid, hsourceValid, hprefix⟩
  have hbaseSlotEq : baseSlot = envSlot :=
    Option.some.inj (hbaseSlot.symm.trans henvBase)
  subst hbaseSlotEq
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hsourceValid with
  | @boxFull ownerLocation ownerSlot inner hownedSlot _hinnerValid =>
      have hderefLoc :
          store.loc source.deref = some ownerLocation := by
        simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
      have hsourceOwner :
          (StoreSlot.mk
            (.value (.ref { location := ownerLocation, owner := true }))
            sourceLifetime).value =
          .value (.ref { location := ownerLocation, owner := true }) := rfl
      have hprefixExtended :
          ∃ k,
            OwnerChainAt store rootSlot.value
              (LVal.path source ++ [()]) ownerLocation ∧
            OwnsChain store (VariableProjection (LVal.base source)) k
              ownerLocation ∧
            k = (LVal.path source ++ [()]).length :=
        OwnerChainPrefix.extend hprefix
          (by
            intro hpathNil
            have hlocRoot :=
              ProgramStore.loc_eq_var_of_path_nil
                (store := store) (lv := source) hpathNil
            have hlocEq :
                sourceLocation = VariableProjection (LVal.base source) :=
              Option.some.inj (hsourceLoc.symm.trans hlocRoot)
            subst hlocEq
            have hslotEq :
                StoreSlot.mk
                    (.value (.ref { location := ownerLocation, owner := true }))
                    sourceLifetime = rootSlot :=
              Option.some.inj (hsourceSlot.symm.trans hrootSlot)
            exact congrArg StoreSlot.value hslotEq.symm)
          hsourceSlot hsourceOwner
      rcases hprefixExtended with ⟨k, _hchainAt, hleafChain, _hchainLen⟩
      rcases EnvWrite.deref_boxFull_result_contains_of_select henvBase
          (hselectSource henvBase) hwriteEnv with
        ⟨_updatedTy, _hupdatePath, henv', hcontainsRhsResult⟩
      have hvalidStore : ValidStore store :=
        ValidRuntimeState.validStore hvalidRuntime
      have hheap : StoreOwnerTargetsHeap store :=
        ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
      have hvalueHeap : ValueOwnerTargetsHeap value :=
        TermOwnerTargetsHeap.value
          (termOwnerTargetsHeap_assign_inner
            (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
      have hvalueUnowned :
          ∀ owned, owned ∈ valueOwningLocations value →
            ¬ ProgramStore.Owns store owned := by
        intro owned hmem
        exact
          (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
            (by
              simpa [termOwningLocations, termValues,
                partialValueOwningLocations] using hmem))
      have hvalueOwnerNoReach :
          ¬ RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy)
            ownerLocation :=
        ownerReaches_value_ne_chain_leaf_of_unowned_root
          hvalidStore hheap hvalueHeap hvalueUnowned
          (by simpa [LVal.base, VariableProjection] using hleafChain)
      have hvalidValueEnv' :
          ValidPartialValueWhenInitialized env' store (.value value)
            (.ty rhsTy) :=
        validPartialValueWhenInitialized_envWrite_of_result_contains
          hwell.1 hborrowSafe htySafe hwriteEnv
          (LValTyping.boxFull hsourceFull) hshape hwellTy hnotWrite
          (by
            intro mutable target hcontains
            exact ⟨LVal.base source, hcontainsRhsResult hcontains⟩)
          hvalidValue
      exact
        preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_frames
          hwell.1 hborrowSafe htySafe hsafe hvalidRuntime hsourceFull hshape
          hwellTy hwriteEnv (WellFormedEnv.whenInitialized hwellOut)
          hselectSource hvalidValue hstep hvalidValueEnv'
          (by
            intro y otherEnvSlot oldValue hyBase henvY hstoreY
            rcases hsafe.2 y otherEnvSlot henvY with
              ⟨safeValue, hsafeStoreY, hvalidOld⟩
            have hvalueEq : safeValue = oldValue := by
              have hslotEq :=
                Option.some.inj (hsafeStoreY.symm.trans hstoreY)
              exact congrArg StoreSlot.value hslotEq
            subst hvalueEq
            have henvY' : env'.slotAt y = some otherEnvSlot := by
              rw [henv']
              simpa [Env.update, hyBase] using henvY
            exact
              validPartialValueWhenInitialized_envWrite_of_result_contains
                hwell.1 hborrowSafe htySafe hwriteEnv
                (LValTyping.boxFull hsourceFull) hshape hwellTy hnotWrite
                (by
                  intro mutable target hcontains
                  exact ⟨y, otherEnvSlot, henvY', hcontains⟩)
                hvalidOld)
          (by
            intro location hreach
            have hne :
                location ≠ ownerLocation :=
              reachesWhenInitialized_chain_leaf_ne_of_update_var_not_writeProhibited
                hsafe hvalidStore hheap
                (by simpa [LVal.base] using henv') hnotWrite
                (by simpa [LVal.base, VariableProjection] using hleafChain)
                (by
                  intro mutable target hcontains
                  exact ⟨LVal.base source, hcontainsRhsResult hcontains⟩)
                hvalueOwnerNoReach hreach
            simpa [hderefLoc] using hne)
          (by
            intro y otherEnvSlot oldValue hyBase henvY hstoreY location
              hreach
            have henvY' : env'.slotAt y = some otherEnvSlot := by
              rw [henv']
              simpa [Env.update, hyBase] using henvY
            have hstorageNeRoot :
                VariableProjection y ≠
                  VariableProjection (LVal.base source) := by
              intro hrootEq
              exact hyBase (by simpa [VariableProjection] using hrootEq)
            have hownerNoReachOld :
                ¬ RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty
                  ownerLocation :=
              ownerReaches_stored_ne_chain_leaf hvalidStore
                (var_not_owned hheap) (var_not_owned hheap) hstorageNeRoot
                (by simpa [LVal.base, VariableProjection] using hleafChain)
                hstoreY
            have hne :
                location ≠ ownerLocation :=
              reachesWhenInitialized_chain_leaf_ne_of_update_var_not_writeProhibited
                hsafe hvalidStore hheap
                (by simpa [LVal.base] using henv') hnotWrite
                (by simpa [LVal.base, VariableProjection] using hleafChain)
                (by
                  intro mutable target hcontains
                  exact ⟨y, otherEnvSlot, henvY', hcontains⟩)
                hownerNoReachOld hreach
            simpa [hderefLoc] using hne)

/-- Full-box dereference assignment on the owner-only branch of the lvalue
descent.  The only excluded case is the explicit mutable-borrow hop produced by
`LValTyping.tyBox_pathSelect_or_borrow`; that is the re-rooting branch still
needed for the fully general helper. -/
theorem preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_wellFormed_of_no_borrow_hop
    {store store' : ProgramStore} {env env' : Env}
    {lifetime sourceLifetime : Lifetime} {source : LVal}
    {oldTy : Ty} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign source.deref (.val value)) →
    LValTyping env source (.ty (.box oldTy)) sourceLifetime →
    ShapeCompatible env (.ty oldTy) (.ty rhsTy) →
    WellFormedTy env rhsTy sourceLifetime →
    EnvWrite env source.deref rhsTy env' →
    ¬ WriteProhibited env' source.deref →
    WellFormedEnv env' lifetime →
    (∀ {pref : Path} {hopSource target : LVal} {mutable : Bool}
      {borrowLifetime hopTargetLifetime : Lifetime} {hopTargetTy : Ty},
      source = prependPath pref hopSource.deref →
      LValTyping env hopSource (.ty (.borrow mutable target))
        borrowLifetime →
      LValTyping env target (.ty hopTargetTy) hopTargetLifetime →
      LValTyping env (prependPath pref target) (.ty (.box oldTy))
        sourceLifetime →
      False) →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign source.deref (.val value)) store'
      (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hsourceFull hshape
    hwellTy hwriteEnv hnotWrite hwellOut hnoBorrowHop hvalidValue hstep
  exact
    preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_wellFormed_of_select
      hwell hborrowSafe htySafe hsafe hvalidRuntime hsourceFull hshape
      hwellTy hwriteEnv hnotWrite hwellOut
      (by
        intro slot hslot
        rcases LValTyping.tyBox_pathSelect_or_borrow hsourceFull hslot with
          hselect | hhop
        · exact hselect
        · rcases hhop with
            ⟨pref, hopSource, target, mutable, borrowLifetime,
              hopTargetLifetime, hopTargetTy, hsourceEq, hhopTyping,
              htargetTyping, hretypedTarget⟩
          exact False.elim
            (hnoBorrowHop hsourceEq hhopTyping htargetTyping
              hretypedTarget))
      hvalidValue hstep

/-- Dispatch assignment preservation for a pure selected lvalue.  The caller
supplies the frame obligations against the selected runtime leaf; the theorem
then selects the appropriate existing var/box/full-box assignment frame helper.
The borrow-hop typing case is impossible because a pure `PathSelect` descent
cannot type through a borrow. -/
theorem preservation_assign_pathSelect_step_runtime_whenInitialized_of_frames
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime : Lifetime} {lhs : LVal}
    {oldTy leafTy : PartialTy} {rootSlot : EnvSlot}
    {leafLoc : Location} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign lhs (.val value)) →
    LValTyping env lhs oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite env lhs rhsTy env' →
    WellFormedEnv env' lifetime →
    env.slotAt (LVal.base lhs) = some rootSlot →
    PathSelect (LVal.path lhs) rootSlot.ty leafTy →
    store.loc lhs = some leafLoc →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign lhs (.val value)) store' (.val finalValue) →
    ValidPartialValueWhenInitialized env' store (.value value) (.ty rhsTy) →
    (∀ y otherEnvSlot oldValue,
      y ≠ LVal.base lhs →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ValidPartialValueWhenInitialized env' store oldValue otherEnvSlot.ty) →
    (∀ location,
      RuntimeFrame.ReachesWhenInitialized env' store (.value value) (.ty rhsTy)
        location →
      location ≠ leafLoc) →
    (∀ y otherEnvSlot oldValue,
      y ≠ LVal.base lhs →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.ReachesWhenInitialized env' store oldValue
          otherEnvSlot.ty location →
        location ≠ leafLoc) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hlhs hshape hwellTy
    hwriteEnv hwellOut henvRoot hselect hleafLoc hvalidValue hstep
    hvalidValueEnv' hotherValidEnv' hvalueFrame hotherFrame
  cases lhs with
  | var x =>
      have hleafEq : leafLoc = VariableProjection x := by
        exact (Option.some.inj
          ((by simpa [ProgramStore.loc, VariableProjection] using hleafLoc :
              some (VariableProjection x) = some leafLoc))).symm
      exact
        preservation_assign_var_step_runtime_whenInitialized_of_frames
          (WellFormedEnv.whenInitialized hwell) hsafe hvalidRuntime hlhs
          hshape hwellTy.whenInitialized hwriteEnv
          (WellFormedEnv.whenInitialized hwellOut) hvalidValue hstep
          hvalidValueEnv'
          (by
            intro y otherEnvSlot oldValue hyBase henvY hstoreY
            exact hotherValidEnv' y otherEnvSlot oldValue
              (by simpa [LVal.base] using hyBase) henvY hstoreY)
          (by
            intro location hreach hlocation
            exact hvalueFrame location hreach (by simpa [hleafEq] using hlocation))
          (by
            intro y otherEnvSlot oldValue hyBase henvY hstoreY location
              hreach hlocation
            exact hotherFrame y otherEnvSlot oldValue
              (by simpa [LVal.base] using hyBase) henvY hstoreY
              location hreach (by simpa [hleafEq] using hlocation))
  | deref source =>
      cases hlhs with
      | box hsourceBox =>
          exact
            preservation_assign_deref_box_step_runtime_whenInitialized_of_frames
              hwell.1 hborrowSafe htySafe hsafe hvalidRuntime hsourceBox
              hshape hwellTy hwriteEnv (WellFormedEnv.whenInitialized hwellOut)
              hvalidValue hstep hvalidValueEnv'
              (by
                intro y otherEnvSlot oldValue hyBase henvY hstoreY
                exact hotherValidEnv' y otherEnvSlot oldValue
                  (by simpa [LVal.base] using hyBase) henvY hstoreY)
              (by
                intro location hreach
                simpa [hleafLoc] using hvalueFrame location hreach)
              (by
                intro y otherEnvSlot oldValue hyBase henvY hstoreY location
                  hreach
                simpa [hleafLoc] using
                  hotherFrame y otherEnvSlot oldValue
                    (by simpa [LVal.base] using hyBase) henvY hstoreY
                    location hreach)
      | boxFull hsourceFull =>
          rename_i inner
          have hselectDeref :
              PathSelect (LVal.path source ++ [()]) rootSlot.ty leafTy := by
            simpa [LVal.path] using hselect
          rcases PathSelect.snoc_inv hselectDeref with
            ⟨mid, hselectSourceMid, hmidShape⟩
          have hmidEq :
              PartialTy.ty (.box inner) = mid :=
            LValTyping.pathSelect_deterministic hsourceFull
              (by simpa [LVal.base] using henvRoot) hselectSourceMid
          have hselectSource :
              ∀ {slot : EnvSlot},
                env.slotAt (LVal.base source) = some slot →
                PathSelect (LVal.path source) slot.ty
                  (PartialTy.ty (.box inner)) := by
            intro slot hslot
            have hslotEq : slot = rootSlot :=
              Option.some.inj (hslot.symm.trans
                (by simpa [LVal.base] using henvRoot))
            subst hslotEq
            simpa [hmidEq] using hselectSourceMid
          exact
            preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_frames
              hwell.1 hborrowSafe htySafe hsafe hvalidRuntime hsourceFull
              hshape hwellTy hwriteEnv (WellFormedEnv.whenInitialized hwellOut)
              hselectSource hvalidValue hstep hvalidValueEnv'
              (by
                intro y otherEnvSlot oldValue hyBase henvY hstoreY
                exact hotherValidEnv' y otherEnvSlot oldValue
                  (by simpa [LVal.base] using hyBase) henvY hstoreY)
              (by
                intro location hreach
                simpa [hleafLoc] using hvalueFrame location hreach)
              (by
                intro y otherEnvSlot oldValue hyBase henvY hstoreY location
                  hreach
                simpa [hleafLoc] using
                  hotherFrame y otherEnvSlot oldValue
                    (by simpa [LVal.base] using hyBase) henvY hstoreY
                    location hreach)
      | borrow hsourceBorrow _htarget =>
          have hselectDeref :
              PathSelect (LVal.path source ++ [()]) rootSlot.ty leafTy := by
            simpa [LVal.path] using hselect
          rcases PathSelect.snoc_inv hselectDeref with
            ⟨mid, hselectSourceMid, hmidShape⟩
          have hsourceEq :
              PartialTy.ty (.borrow _ _) = mid :=
            LValTyping.pathSelect_deterministic hsourceBorrow
              (by simpa [LVal.base] using henvRoot) hselectSourceMid
          rcases hmidShape with hbox | htyBox
          · rw [hbox] at hsourceEq
            cases hsourceEq
          · rcases htyBox with ⟨T, htyBox, _hleaf⟩
            rw [htyBox] at hsourceEq
            cases hsourceEq

/-- **Chain-entry forcing in the result environment.**  Any borrow annotation
of the post-write environment that targets into the write chain is a source
annotation held on the chain itself: the graft's borrows never target the
chain (`graft_target_outside`), and outside holders never target into it
(`chainGuard_contains_exclusion`).  With unarity this pins the annotation to
the chain's own hop at that slot. -/
theorem chain_entry_env3 {env env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    (hsafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b) :
    ∀ {x : Name} {mutable : Bool} {u : LVal},
      env₃ ⊢ x ↝ (.borrow mutable u) →
      ChainGuard env (LVal.base lhs) (LVal.base u) →
      env ⊢ x ↝ (.borrow mutable u) ∧ ChainGuard env (LVal.base lhs) x := by
  have hunchanged : ∀ x, ¬ ChainGuard env (LVal.base lhs) x →
      env₃.slotAt x = env.slotAt x := by
    intro x hxOut
    exact hne x (fun h => hxOut (h ▸ hguardB))
  intro x mutable u hx hguardU
  by_cases hxb : x = b
  · -- The graft slot: its borrows never target the chain.
    subst hxb
    rcases hx with ⟨s, hs, hcontains⟩
    have hsEq : s = { bslot with ty := graftTy } :=
      Option.some.inj (hs.symm.trans hbLook)
    subst hsEq
    exact absurd hguardU
      (graft_target_outside htySafe hnotWrite hbLook hgraftContains
        hcontains)
  · -- Unchanged slot: a source annotation; outside holders are excluded.
    have hxEnv : env ⊢ x ↝ (.borrow mutable u) := by
      rcases hx with ⟨s, hs, hcontains⟩
      exact ⟨s, (hne x hxb) ▸ hs, hcontains⟩
    refine ⟨hxEnv, ?_⟩
    by_contra hxOutside
    exact chainGuard_contains_exclusion hsafe hunchanged hnotWrite hguardU
      hxOutside hxEnv rfl

/-- On-chain holders carry exactly the chain's hop annotation: combining the
entry forcing with unarity.  The entering borrow at a chain slot is the
unique annotation of that slot. -/
theorem chain_entry_unique {env : Env}
    {x : Name} {mutable mutable' : Bool} {u u' : LVal}
    (hx : env ⊢ x ↝ (.borrow mutable u))
    (hx' : env ⊢ x ↝ (.borrow mutable' u')) :
    mutable = mutable' ∧ u = u' := by
  rcases hx with ⟨s, hs, hcontains⟩
  rcases hx' with ⟨s', hs', hcontains'⟩
  have hsEq : s' = s := Option.some.inj (hs'.symm.trans hs)
  subst hsEq
  exact PartialTyContains.borrow_unique hcontains hcontains'

theorem chainGuard_tail_of_step {env : Env} {z a w : Name} {g : LVal}
    (hedge : env ⊢ z ↝ (.borrow true g))
    (hbase : LVal.base g = a) :
    ChainGuard env z w →
    w = z ∨ ChainGuard env a w := by
  intro hguard
  induction hguard with
  | base =>
      exact Or.inl rfl
  | @step zPrev y gPrev hprev hcont hbasePrev ih =>
      rcases ih with hprevEq | htail
      · subst hprevEq
        rcases chain_entry_unique hedge hcont with ⟨_hmut, htarget⟩
        subst htarget
        right
        have hyEq : y = a := hbasePrev.symm.trans hbase
        subst hyEq
        exact ChainGuard.base
      · exact Or.inr (ChainGuard.step htail hcont hbasePrev)

theorem chainGuard_incoming_edge {env : Env} {root y : Name} :
    ChainGuard env root y →
    y ≠ root →
    ∃ z g,
      ChainGuard env root z ∧
        env ⊢ z ↝ (.borrow true g) ∧
        LVal.base g = y := by
  intro hguard hyRoot
  cases hguard with
  | base =>
      exact False.elim (hyRoot rfl)
  | step hprev hcont hbase =>
      exact ⟨_, _, hprev, hcont, hbase⟩

theorem chainGuard_linear {env : Env} {root a b : Name} :
    ChainGuard env root a →
    ChainGuard env root b →
    a = b ∨ ChainGuard env a b ∨ ChainGuard env b a := by
  intro ha
  induction ha generalizing b with
  | base =>
      intro hb
      exact Or.inr (Or.inl hb)
  | @step z a g hrootZ hedge hbase ih =>
      intro hb
      rcases ih hb with hzb | hcomp
      · subst hzb
        exact Or.inr (Or.inr
          (ChainGuard.step ChainGuard.base hedge hbase))
      · rcases hcomp with hzToB | hbToZ
        · rcases chainGuard_tail_of_step hedge hbase hzToB with hbEqZ | haToB
          · subst hbEqZ
            exact Or.inr (Or.inr
              (ChainGuard.step ChainGuard.base hedge hbase))
          · exact Or.inr (Or.inl haToB)
        · exact Or.inr (Or.inr (ChainGuard.step hbToZ hedge hbase))

theorem chainGuard_trans {env : Env} {root mid target : Name} :
    ChainGuard env root mid →
    ChainGuard env mid target →
    ChainGuard env root target := by
  intro hroot htail
  induction htail with
  | base => exact hroot
  | step hprev hcont hbase ih =>
      exact ChainGuard.step ih hcont hbase

theorem chainGuard_rank_le {env : Env} {φ : Name → Nat}
    (hφ : LinearizedBy φ env) :
    ∀ {root y : Name}, ChainGuard env root y → φ y ≤ φ root := by
  intro root y hguard
  induction hguard with
  | base =>
      exact Nat.le_refl _
  | @step z y g hprev hentry hbase ih =>
      have hlt : φ y < φ z := by
        simpa [hbase] using LinearizedBy.contains_rank_lt hφ hentry
      exact le_trans (Nat.le_of_lt hlt) ih

theorem chainGuard_rank_lt_of_ne {env : Env} {φ : Name → Nat}
    (hφ : LinearizedBy φ env) {root y : Name} :
    ChainGuard env root y →
    y ≠ root →
    φ y < φ root := by
  intro hguard hy
  cases hguard with
  | base =>
      exact False.elim (hy rfl)
  | @step z y g hprev hentry hbase =>
      have hlt : φ y < φ z := by
        simpa [hbase] using LinearizedBy.contains_rank_lt hφ hentry
      exact lt_of_lt_of_le hlt (chainGuard_rank_le hφ hprev)

theorem chainGuard_linear_ne {env : Env} {root final y : Name} :
    ChainGuard env root final →
    ChainGuard env root y →
    y ≠ final →
    ChainGuard env final y ∨ ChainGuard env y final := by
  intro hfinal hy hyFinal
  rcases chainGuard_linear hfinal hy with hEq | hcomp
  · exact False.elim (hyFinal hEq.symm)
  · exact hcomp

/-- Borrow-safety plus slot unarity pins a competing entry edge.  If a chain
edge `z ↝ &mut g` targets base `y`, then any borrow annotation whose target also
has base `y` is held at `z`; if it is held at `z`, unary containment forces it
to be the same mutable annotation. -/
theorem borrowSafe_same_target_unique_edge {env : Env}
    {z x y : Name} {g u : LVal} {mutable : Bool}
    (hsafe : BorrowSafeEnv env)
    (hchainEdge : env ⊢ z ↝ (.borrow true g))
    (hchainBase : LVal.base g = y)
    (hentry : env ⊢ x ↝ (.borrow mutable u))
    (hentryBase : LVal.base u = y) :
    x = z ∧ mutable = true ∧ u = g := by
  have hconflict : g ⋈ u := by
    show LVal.base g = LVal.base u
    rw [hchainBase, hentryBase]
  have hzx : z = x := hsafe z x mutable g u hchainEdge hentry hconflict
  have hxz : x = z := hzx.symm
  subst x
  rcases chain_entry_unique hchainEdge hentry with ⟨hmutable, htarget⟩
  exact ⟨rfl, hmutable.symm, htarget.symm⟩

theorem chainGuard_entry_to_nonroot_unique_edge {env : Env}
    {root y targetBase : Name} {target : LVal} {mutable : Bool}
    (hsafe : BorrowSafeEnv env)
    (hguardTarget : ChainGuard env root targetBase)
    (htargetNeRoot : targetBase ≠ root)
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (hentryBase : LVal.base target = targetBase) :
    ∃ pred g,
      ChainGuard env root pred ∧
        env ⊢ pred ↝ (.borrow true g) ∧
        LVal.base g = targetBase ∧
        y = pred ∧ mutable = true ∧ target = g := by
  rcases chainGuard_incoming_edge hguardTarget htargetNeRoot with
    ⟨pred, g, hguardPred, hedge, hedgeBase⟩
  rcases borrowSafe_same_target_unique_edge hsafe hedge hedgeBase
      hentry hentryBase with
    ⟨hyPred, hmutable, htarget⟩
  exact ⟨pred, g, hguardPred, hedge, hedgeBase, hyPred, hmutable, htarget⟩

/-- Head decomposition for a guarded borrow chain.  A guarded slot is either
the root itself, or it is reached by first following the root's own mutable
borrow annotation and then continuing the guard from that target base. -/
theorem chainGuard_head_inv {env : Env} {root y : Name} :
    ChainGuard env root y →
    y = root ∨
      ∃ g, env ⊢ root ↝ (.borrow true g) ∧
        ChainGuard env (LVal.base g) y := by
  intro hguard
  induction hguard with
  | base =>
      exact Or.inl rfl
  | @step z y g hguardZ hcontains hbaseG ih =>
      rcases ih with hroot | ⟨first, hrootContains, htail⟩
      · subst hroot
        exact Or.inr ⟨g, hcontains, by
          rw [← hbaseG]
          exact ChainGuard.base⟩
      · exact Or.inr ⟨first, hrootContains,
          ChainGuard.step htail hcontains hbaseG⟩

/-- In a borrow-safe environment, a guarded slot can carry a mutable self-edge
only at the guard root.  If a later chain slot `z` pointed a mutable borrow
back to a `z`-rooted target, that self-edge would conflict with the preceding
chain edge into `z`; `BorrowSafeEnv` forces the predecessor holder to be `z`,
and the shorter guard proof repeats the argument. -/
theorem chainGuard_self_edge_eq_root {env : Env} {root z : Name} {g : LVal}
    (hsafe : BorrowSafeEnv env) :
    ChainGuard env root z →
    env ⊢ z ↝ (.borrow true g) →
    LVal.base g = z →
    z = root := by
  intro hguard
  induction hguard with
  | base =>
      intro _hcontains _hbase
      rfl
  | @step zPrev z gPrev hguardPrev hcontainsPrev hbasePrev ih =>
      intro hcontainsSelf hbaseSelf
      have hconflict : gPrev ⋈ g := by
        show LVal.base gPrev = LVal.base g
        rw [hbasePrev, hbaseSelf]
      have hprevEq : zPrev = z :=
        hsafe zPrev z true gPrev g hcontainsPrev hcontainsSelf hconflict
      subst hprevEq
      exact ih hcontainsSelf hbaseSelf

/-- Source-environment version of `chain_entry_env3`: if a source annotation
targets into the guarded write chain, then its holder is on that chain. -/
theorem chain_entry_source {env env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    (hsafe : BorrowSafeEnv env)
    (_htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (_hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (_hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b) :
    ∀ {x : Name} {mutable : Bool} {u : LVal},
      env ⊢ x ↝ (.borrow mutable u) →
      ChainGuard env (LVal.base lhs) (LVal.base u) →
      ChainGuard env (LVal.base lhs) x := by
  have hunchanged : ∀ x, ¬ ChainGuard env (LVal.base lhs) x →
      env₃.slotAt x = env.slotAt x := by
    intro x hxOut
    exact hne x (fun h => hxOut (h ▸ hguardB))
  intro x mutable u hcontains hguardU
  by_contra hxOutside
  exact chainGuard_contains_exclusion hsafe hunchanged hnotWrite hguardU
    hxOutside hcontains rfl

/-- Root-entry exclusion for source annotations.  If a source mutable
annotation targets the top-level write root, then either its holder is the
single changed/graft slot or the annotation survives into the result
environment and immediately contradicts the rule's `¬ WriteProhibited`
premise. -/
theorem chainGuard_step_root_prohibited {env env₃ : Env} {lhs : LVal}
    {rhsTy : Ty} {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    (_hsafe : BorrowSafeEnv env)
    (_htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (_hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (_hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (_hguardB : ChainGuard env (LVal.base lhs) b) :
    ∀ {x : Name} {g : LVal},
      env ⊢ x ↝ (.borrow true g) →
      LVal.base g = LVal.base lhs →
      x = b := by
  intro x g hcontains hbase
  by_contra hxb
  have hcontains₃ : env₃ ⊢ x ↝ (.borrow true g) := by
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    exact ⟨slot, (hne x hxb) ▸ hslot, hcontainsTy⟩
  exact hnotWrite (WriteProhibited.of_contains_conflict hcontains₃ hbase)

/-- Degenerate no-reentry package: a mutable self-edge on the guarded top
write chain can only live at the final changed/graft slot.  Borrow safety first
collapses any guarded self-edge to the chain root; the root-entry exclusion
then says the holder must be the changed slot, since any other holder survives
into the result environment and write-prohibits the top lhs. -/
theorem chainGuard_self_edge_eq_changed_slot {env env₃ : Env} {lhs : LVal}
    {rhsTy : Ty} {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    (hsafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b) :
    ∀ {z : Name} {g : LVal},
      ChainGuard env (LVal.base lhs) z →
      env ⊢ z ↝ (.borrow true g) →
      LVal.base g = z →
      z = b := by
  intro z g hguardZ hcontains hbaseSelf
  have hzRoot : z = LVal.base lhs :=
    chainGuard_self_edge_eq_root hsafe hguardZ hcontains hbaseSelf
  exact chainGuard_step_root_prohibited hsafe htySafe hnotWrite hne
    hbLook hgraftContains hguardB hcontains (by simpa [hzRoot] using hbaseSelf)

/-- Cycle prohibition.  Suppose no source annotation may target the top root
`r₀` (in the intended use, because the whole result environment is pointwise
value-equal to the source, so any such annotation survives the write and
write-prohibits the top lvalue), and suppose a mutable edge held at `w₀`
closes a cycle back to `ρ` with `ChainGuard env ρ w₀`.  Then no slot is
reachable both from `r₀` and from `ρ`.  The induction walks the top chain
backwards: at each meeting node, borrow safety matches the top chain's
arriving edge with the cycle chain's arriving edge (they target the same
base), so the meeting point slides one step toward `r₀`, where the arriving
edge is killed outright. -/
theorem chainGuard_cycle_prohibited {env : Env} {r₀ ρ w₀ : Name} {t : LVal}
    (hsafe : BorrowSafeEnv env)
    (hkill : ∀ {z : Name} {g : LVal},
      env ⊢ z ↝ (.borrow true g) → LVal.base g = r₀ → False)
    (hedge : env ⊢ w₀ ↝ (.borrow true t))
    (hedgeBase : LVal.base t = ρ)
    (hC₀ : ChainGuard env ρ w₀) :
    ∀ {w : Name}, ChainGuard env r₀ w → ChainGuard env ρ w → False := by
  intro w hT
  induction hT with
  | base =>
      intro hC
      cases hC with
      | base => exact hkill hedge hedgeBase
      | step _ hz hbase => exact hkill hz hbase
  | @step zT wT gT hT' hzT hbaseT ih =>
      intro hC
      cases hC with
      | base =>
          rcases borrowSafe_same_target_unique_edge hsafe hedge hedgeBase
              hzT hbaseT with ⟨hzEq, _, _⟩
          exact ih (by rw [hzEq]; exact hC₀)
      | @step zC _ gC hC' hzC hbaseC =>
          rcases borrowSafe_same_target_unique_edge hsafe hzC hbaseC
              hzT hbaseT with ⟨hzEq, _, _⟩
          exact ih (by rw [hzEq]; exact hC')

/-- Cycle prohibition with an arbitrary back edge.  The top chain still consists
of mutable edges; the closing edge can be mutable or immutable because it is
used as the second argument to `BorrowSafeEnv` when matching an arriving top
edge. -/
theorem chainGuard_cycle_prohibited_any_back {env : Env}
    {r₀ ρ w₀ : Name} {t : LVal} {mutable : Bool}
    (hsafe : BorrowSafeEnv env)
    (hkill : ∀ {z : Name} {mutable : Bool} {g : LVal},
      env ⊢ z ↝ (.borrow mutable g) → LVal.base g = r₀ → False)
    (hedge : env ⊢ w₀ ↝ (.borrow mutable t))
    (hedgeBase : LVal.base t = ρ)
    (hC₀ : ChainGuard env ρ w₀) :
    ∀ {w : Name}, ChainGuard env r₀ w → ChainGuard env ρ w → False := by
  intro w hT
  induction hT with
  | base =>
      intro hC
      cases hC with
      | base => exact hkill hedge hedgeBase
      | step _ hz hbase => exact hkill hz hbase
  | @step zT wT gT hT' hzT hbaseT ih =>
      intro hC
      cases hC with
      | base =>
          have hconflict : gT ⋈ t := by
            show LVal.base gT = LVal.base t
            rw [hbaseT, hedgeBase]
          have hzEq : zT = w₀ :=
            hsafe zT w₀ mutable gT t hzT hedge hconflict
          exact ih (by rw [hzEq]; exact hC₀)
      | @step zC _ gC hC' hzC hbaseC =>
          rcases borrowSafe_same_target_unique_edge hsafe hzC hbaseC
              hzT hbaseT with ⟨hzEq, _, _⟩
          exact ih (by rw [hzEq]; exact hC')

theorem chainGuard_back_edge_to_guarded_root_prohibited {env : Env}
    {top root z : Name} {target : LVal} {mutable : Bool}
    (hsafe : BorrowSafeEnv env)
    (hkillTop : ∀ {w : Name} {mutable : Bool} {g : LVal},
      env ⊢ w ↝ (.borrow mutable g) → LVal.base g = top → False)
    (hguardRoot : ChainGuard env top root)
    (hback : env ⊢ z ↝ (.borrow mutable target))
    (hbackBase : LVal.base target = root)
    (hrootToZ : ChainGuard env root z) :
    False :=
  chainGuard_cycle_prohibited_any_back hsafe hkillTop hback hbackBase
    hrootToZ hguardRoot ChainGuard.base

theorem chainGuard_tail_back_edge_to_guarded_ancestor_prohibited {env : Env}
    {top ancestor tail z : Name} {target : LVal} {mutable : Bool}
    (hsafe : BorrowSafeEnv env)
    (hkillTop : ∀ {w : Name} {mutable : Bool} {g : LVal},
      env ⊢ w ↝ (.borrow mutable g) → LVal.base g = top → False)
    (hguardAncestor : ChainGuard env top ancestor)
    (hancestorToTail : ChainGuard env ancestor tail)
    (htailToZ : ChainGuard env tail z)
    (hback : env ⊢ z ↝ (.borrow mutable target))
    (hbackBase : LVal.base target = ancestor) :
    False :=
  chainGuard_back_edge_to_guarded_root_prohibited hsafe hkillTop hguardAncestor
    hback hbackBase (chainGuard_trans hancestorToTail htailToZ)

/-- The nested hop write preserves the outer holder slot.  Applying the write
characterization to the reduced write, the only dangerous case is the one
where the nested chain re-enters the outer holder base.  There the outer
identity-update restores the holder slot, so the whole result environment is
pointwise value-equal to the source; every source annotation survives, the
re-entry chain plus the hop annotation closes a mutable-borrow cycle through
the current holder, and `chainGuard_cycle_prohibited` converts it into
`WriteProhibited env₃ lhsTop`, contradicting the rule premise. -/
theorem EnvWrite.hop_nested_slot_preserved
    {env env₃ nested : Env} {lhsTop : LVal} {lhsCur : Name} {rhsTy : Ty}
    {slot : EnvSlot} {path' : Path} {target : LVal}
    {oldTy : PartialTy} {targetLifetime : Lifetime}
    (hcbwf : ContainedBorrowsWellFormed env)
    (hsafe : BorrowSafeEnv env)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (hguardTop : ChainGuard env (LVal.base lhsTop) lhsCur)
    (hpoint : ∀ y, env₃.slotAt y = (nested.update lhsCur slot).slotAt y)
    (hslot : env.slotAt lhsCur = some slot)
    (hhopAnn : env ⊢ lhsCur ↝ (.borrow true target))
    (hnested : EnvWrite env (prependPath path' target) rhsTy nested)
    (hreduced :
      LValTyping env (prependPath path' target) oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy)) :
    nested.slotAt lhsCur = some slot := by
  rcases EnvWrite.chain_guarded hcbwf hnested hreduced hshape with
    hpointwise | ⟨b, bslot, graftTy, _hbEnv, hne, _hbNested, _hlife,
      _hgraftContains, _hmirror, hguard⟩
  · rw [hpointwise lhsCur]
    exact hslot
  · by_cases hbb : b = lhsCur
    · -- Re-entry corner: derive a contradiction from the top premise.
      exfalso
      subst hbb
      have henvEq : ∀ y, env₃.slotAt y = env.slotAt y := by
        intro y
        rw [hpoint y]
        by_cases hy : y = b
        · subst hy
          simpa [Env.update] using hslot.symm
        · have hupd :
              (nested.update b slot).slotAt y = nested.slotAt y := by
            simp [Env.update, hy]
          rw [hupd]
          exact hne y hy
      have hkill : ∀ {z : Name} {g : LVal},
          env ⊢ z ↝ (.borrow true g) → LVal.base g = LVal.base lhsTop →
          False := by
        intro z g hzg hbase
        rcases hzg with ⟨s, hs, hcont⟩
        refine hnotWriteTop
          (WriteProhibited.of_contains_conflict
            (⟨s, (henvEq z).trans hs, hcont⟩ :
              env₃ ⊢ z ↝ (Ty.borrow true g)) ?_)
        show LVal.base g = LVal.base lhsTop
        exact hbase
      have hC : ChainGuard env (LVal.base target) b := by
        simpa using hguard
      exact chainGuard_cycle_prohibited hsafe hkill hhopAnn rfl hC
        hguardTop hC
    · rw [hne lhsCur (fun h => hbb h.symm)]
      exact hslot

/-- The traversed borrow-hop spine of an environment write: the written
lvalue reduces to the final pure lvalue through a sequence of mutable-borrow
hops.  Each hop records the hop-free descent prefix `s₀` (typed at the hop
annotation), the annotation's containment at the base slot, and the remaining
path that re-roots at the hop target. -/
inductive HopsTo (env env₃ : Env) : LVal → LVal → Prop where
  | refl {lv : LVal} : HopsTo env env₃ lv lv
  | hop {s₀ target final : LVal} {slotH : EnvSlot} {lf : Lifetime} {p : Path} :
      env.slotAt (LVal.base s₀) = some slotH →
      PathSelect (LVal.path s₀) slotH.ty (.ty (.borrow true target)) →
      LValTyping env s₀ (.ty (.borrow true target)) lf →
      env ⊢ (LVal.base s₀) ↝ (.borrow true target) →
      env₃.slotAt (LVal.base s₀) = env.slotAt (LVal.base s₀) →
      HopsTo env env₃ (prependPath p target) final →
      HopsTo env env₃ (prependPath p s₀.deref) final

theorem HopsTo.locReads_ne_of_links_clean
    {env env₃ : Env} {store : ProgramStore} {leaf : Location}
    (hsafe : SafeAbstraction store env)
    (hcbwf : ContainedBorrowsWellFormed env) :
    ∀ {lv final : LVal},
      HopsTo env env₃ lv final →
      (∀ {s₀ target : LVal} {slotH : EnvSlot} {lf : Lifetime},
        env.slotAt (LVal.base s₀) = some slotH →
        PathSelect (LVal.path s₀) slotH.ty (.ty (.borrow true target)) →
        LValTyping env s₀ (.ty (.borrow true target)) lf →
        env ⊢ (LVal.base s₀) ↝ (.borrow true target) →
        env₃.slotAt (LVal.base s₀) = env.slotAt (LVal.base s₀) →
        (∀ mid, RuntimeFrame.LocReads store s₀ mid → mid ≠ leaf) ∧
          store.loc s₀ ≠ some leaf) →
      (∀ mid, RuntimeFrame.LocReads store final mid → mid ≠ leaf) →
      ∀ mid, RuntimeFrame.LocReads store lv mid → mid ≠ leaf := by
  intro lv final hhops
  induction hhops with
  | refl =>
      intro _hlinks hfinal mid hread
      exact hfinal mid hread
  | hop henvH hsel htyping hcont henv₃ tail ih =>
      intro hlinks hfinal mid hread
      rcases LValTyping.partialTyBorrowsWellFormedInSlot hcbwf htyping
          PartialTyContains.here with
        ⟨targetTy, targetLifetime', htargetTyping, _houtlives, _hbase⟩
      have hloc :
          store.loc _ = store.loc _ :=
        lvalTyping_deref_borrow_loc_eq_whenInitialized hsafe htyping
          htargetTyping
      rcases locReads_prependPath_hop hloc _ hread with
        hsourceReads | hsourceLoc | htargetReads
      · exact (hlinks henvH hsel htyping hcont henv₃).1 mid hsourceReads
      · intro hmidEq
        exact (hlinks henvH hsel htyping hcont henv₃).2
          (by simpa [hmidEq] using hsourceLoc)
      · exact ih hlinks hfinal mid htargetReads

theorem final_edge_target_locReads_ne
    {env : Env} {store : ProgramStore} {finalLhs target target' : LVal}
    {holder y : Name} {path' : Path} {mutable : Bool} {leaf : Location}
    (hborrowSafe : BorrowSafeEnv env)
    (hfinalEdge : env ⊢ holder ↝ (.borrow true target'))
    (hfinalEq : finalLhs = prependPath path' target')
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (hentryBase : LVal.base target = LVal.base finalLhs)
    (hfinalReads : ∀ mid, RuntimeFrame.LocReads store finalLhs mid →
      mid ≠ leaf) :
    ∀ mid, RuntimeFrame.LocReads store target mid → mid ≠ leaf := by
  have htargetBase : LVal.base target' = LVal.base finalLhs := by
    rw [hfinalEq]
    simp [LVal.base_prependPath]
  rcases borrowSafe_same_target_unique_edge hborrowSafe hfinalEdge
      htargetBase hentry hentryBase with ⟨_holderEq, _mutableEq,
        htargetEq⟩
  subst htargetEq
  intro mid hread
  exact hfinalReads mid (by
    rw [hfinalEq]
    exact locReads_prependPath_of_locReads path' hread)

/-- A source entry targeting the selected final base is the selected incoming
edge itself. -/
theorem edge_into_final_base_eq
    {env : Env} {finalLhs target target' : LVal}
    {holder y : Name} {path' : Path} {mutable : Bool}
    (hborrowSafe : BorrowSafeEnv env)
    (hfinalEdge : env ⊢ holder ↝ (.borrow true target'))
    (hfinalEq : finalLhs = prependPath path' target')
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (hentryBase : LVal.base target = LVal.base finalLhs) :
    y = holder ∧ mutable = true ∧ target = target' := by
  have htargetBase : LVal.base target' = LVal.base finalLhs := by
    rw [hfinalEq]
    simp [LVal.base_prependPath]
  rcases borrowSafe_same_target_unique_edge hborrowSafe hfinalEdge
      htargetBase hentry hentryBase with
    ⟨hyHolder, hmutable, htarget⟩
  exact ⟨hyHolder, hmutable, htarget⟩

theorem HopsTo.tail_target_locReads_ne
    {env env₃ : Env} {store : ProgramStore} {leaf : Location}
    (hsafe : SafeAbstraction store env)
    (hcbwf : ContainedBorrowsWellFormed env)
    {target final : LVal} {path' : Path}
    (hhops : HopsTo env env₃ (prependPath path' target) final)
    (hlinks :
      ∀ {s₀ target : LVal} {slotH : EnvSlot} {lf : Lifetime},
        env.slotAt (LVal.base s₀) = some slotH →
        PathSelect (LVal.path s₀) slotH.ty (.ty (.borrow true target)) →
        LValTyping env s₀ (.ty (.borrow true target)) lf →
        env ⊢ (LVal.base s₀) ↝ (.borrow true target) →
        env₃.slotAt (LVal.base s₀) = env.slotAt (LVal.base s₀) →
        (∀ mid, RuntimeFrame.LocReads store s₀ mid → mid ≠ leaf) ∧
          store.loc s₀ ≠ some leaf)
    (hfinalReads : ∀ mid, RuntimeFrame.LocReads store final mid →
      mid ≠ leaf) :
    ∀ mid, RuntimeFrame.LocReads store target mid → mid ≠ leaf := by
  have htailReads :
      ∀ mid, RuntimeFrame.LocReads store (prependPath path' target) mid →
        mid ≠ leaf :=
    HopsTo.locReads_ne_of_links_clean hsafe hcbwf hhops hlinks hfinalReads
  intro mid hread
  exact htailReads mid (locReads_prependPath_of_locReads path' hread)

/-- A source annotation targeting the root of a hop-spine tail is the incoming
hop annotation itself, so the tail read-exclusion applies to its target. -/
theorem HopsTo.source_entry_tail_root_locReads_ne
    {env env₃ : Env} {store : ProgramStore} {leaf : Location}
    (hsafe : SafeAbstraction store env)
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    {tailRoot target final : LVal} {path' : Path}
    {holder y : Name} {mutable : Bool}
    (hincoming : env ⊢ holder ↝ (.borrow true tailRoot))
    (hhops : HopsTo env env₃ (prependPath path' tailRoot) final)
    (hlinks :
      ∀ {s₀ target : LVal} {slotH : EnvSlot} {lf : Lifetime},
        env.slotAt (LVal.base s₀) = some slotH →
        PathSelect (LVal.path s₀) slotH.ty (.ty (.borrow true target)) →
        LValTyping env s₀ (.ty (.borrow true target)) lf →
        env ⊢ (LVal.base s₀) ↝ (.borrow true target) →
        env₃.slotAt (LVal.base s₀) = env.slotAt (LVal.base s₀) →
        (∀ mid, RuntimeFrame.LocReads store s₀ mid → mid ≠ leaf) ∧
          store.loc s₀ ≠ some leaf)
    (hfinalReads : ∀ mid, RuntimeFrame.LocReads store final mid →
      mid ≠ leaf)
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (hentryBase : LVal.base target = LVal.base tailRoot) :
    ∀ mid, RuntimeFrame.LocReads store target mid → mid ≠ leaf := by
  have htailRootReads :
      ∀ mid, RuntimeFrame.LocReads store tailRoot mid → mid ≠ leaf :=
    HopsTo.tail_target_locReads_ne hsafe hcbwf hhops hlinks hfinalReads
  have htailRootBase : LVal.base tailRoot = LVal.base tailRoot := rfl
  rcases borrowSafe_same_target_unique_edge hborrowSafe hincoming
      htailRootBase hentry hentryBase with
    ⟨_holderEq, _mutableEq, htargetEq⟩
  subst htargetEq
  exact htailRootReads

theorem HopsTo.suffix_of_guard_prefix_or_cycle
    {env env₃ : Env} :
    ∀ {lv final target : LVal} {y : Name} {mutable : Bool},
      HopsTo env env₃ lv final →
      ChainGuard env (LVal.base lv) y →
      ChainGuard env y (LVal.base final) →
      y ≠ LVal.base final →
      env ⊢ y ↝ (.borrow mutable target) →
      (∃ path', HopsTo env env₃ (prependPath path' target) final) ∨
        (ChainGuard env (LVal.base final) y ∧
          ChainGuard env y (LVal.base final)) := by
  intro lv final target y mutable hhops
  induction hhops generalizing y target mutable with
  | refl =>
      intro hprefix hyFinal _hyNeFinal _hentry
      exact Or.inr ⟨by simpa using hprefix, hyFinal⟩
  | @hop s₀ hopTarget final slotH lf p henvH hsel htyping hcont henv₃H tail ih =>
      intro hprefix hyFinal hyNeFinal hentry
      have hprefixS₀ :
          ChainGuard env (LVal.base s₀) y := by
        simpa [LVal.base_prependPath, LVal.base] using hprefix
      rcases chainGuard_tail_of_step hcont rfl hprefixS₀ with hyRoot | htail
      · subst hyRoot
        rcases chain_entry_unique hcont hentry with ⟨_hmutable, htargetEq⟩
        subst htargetEq
        exact Or.inl ⟨p, tail⟩
      · have htail' :
            ChainGuard env (LVal.base (prependPath p hopTarget)) y := by
          simpa [LVal.base_prependPath] using htail
        exact ih htail' hyFinal hyNeFinal hentry

theorem HopsTo.suffix_of_guard_prefix
    {env env₃ : Env} :
    ∀ {lv final target : LVal} {y : Name} {mutable : Bool},
      HopsTo env env₃ lv final →
      ChainGuard env (LVal.base lv) y →
      ChainGuard env y (LVal.base final) →
      y ≠ LVal.base final →
      env ⊢ y ↝ (.borrow mutable target) →
      (ChainGuard env (LVal.base final) y →
        ChainGuard env y (LVal.base final) → False) →
      ∃ path', HopsTo env env₃ (prependPath path' target) final := by
  intro lv final target y mutable hhops hprefix hyFinal hyNeFinal hentry
    hnoCycle
  rcases HopsTo.suffix_of_guard_prefix_or_cycle hhops hprefix hyFinal
      hyNeFinal hentry with hsuffix | hcycle
  · exact hsuffix
  · exact False.elim (hnoCycle hcycle.1 hcycle.2)

theorem source_entry_final_base_locReads_ne
    {env nested : Env} {store : ProgramStore} {lhsTop finalLhs lv target : LVal}
    {rhsTy : Ty} {rootSlot : EnvSlot} {graftTy : PartialTy}
    {y : Name} {mutable : Bool} {leaf : Location}
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWriteNested : ¬ WriteProhibited nested lhsTop)
    (hne : ∀ z, z ≠ LVal.base finalLhs →
      nested.slotAt z = env.slotAt z)
    (hbLook : nested.slotAt (LVal.base finalLhs) =
      some { rootSlot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hlast :
      finalLhs = lv ∨
        ∃ (holder : Name) (path' : Path) (target' : LVal),
          env ⊢ holder ↝ (.borrow true target') ∧
          finalLhs = prependPath path' target')
    (hlvBase : LVal.base lv = LVal.base lhsTop)
    (hyFinal : y ≠ LVal.base finalLhs)
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (hentryBase : LVal.base target = LVal.base finalLhs)
    (hfinalReads : ∀ mid, RuntimeFrame.LocReads store finalLhs mid →
      mid ≠ leaf) :
    ∀ mid, RuntimeFrame.LocReads store target mid → mid ≠ leaf := by
  rcases hlast with hfinalEq | hhop
  · exfalso
    have htargetTop : LVal.base target = LVal.base lhsTop := by
      rw [hentryBase, hfinalEq, hlvBase]
    have hentryNested : nested ⊢ y ↝ (.borrow mutable target) := by
      rcases hentry with ⟨slot, hslot, hcontains⟩
      exact ⟨slot, (hne y hyFinal) ▸ hslot, hcontains⟩
    exact hnotWriteNested
      (WriteProhibited.of_contains_conflict hentryNested
        (by simpa [PathConflicts] using htargetTop))
  · rcases hhop with ⟨holder, path', target', hfinalEdge, hfinalEq⟩
    exact final_edge_target_locReads_ne hborrowSafe hfinalEdge hfinalEq
      hentry hentryBase hfinalReads

theorem source_entry_to_top_root_eq_final_base
    {env nested : Env} {lhsTop finalLhs target : LVal}
    {z : Name} {mutable : Bool}
    (hnotWriteNested : ¬ WriteProhibited nested lhsTop)
    (hne : ∀ y, y ≠ LVal.base finalLhs →
      nested.slotAt y = env.slotAt y)
    (hentry : env ⊢ z ↝ (.borrow mutable target))
    (hentryBase : LVal.base target = LVal.base lhsTop) :
    z = LVal.base finalLhs := by
  by_contra hzFinal
  rcases hentry with ⟨slot, hslot, hcontains⟩
  have hentryNested : nested ⊢ z ↝ (.borrow mutable target) :=
    ⟨slot, (hne z hzFinal) ▸ hslot, hcontains⟩
  exact hnotWriteNested
    (by
      cases mutable
      · exact Or.inr ⟨z, target, hentryNested, hentryBase⟩
      · exact Or.inl ⟨z, target, hentryNested, hentryBase⟩)

/-- The selected final write does not leave chain-targeting borrows in the
updated final slot.  Any borrow still contained in that result slot must come
from the RHS graft; `TyBorrowSafeAgainstEnv` then keeps its target outside the
guarded write chain. -/
theorem selected_final_result_no_chain_borrow
    {env env₃ nested : Env} {lhsTop finalLhs target : LVal}
    {rhsTy : Ty} {rootSlot : EnvSlot} {leafTy : PartialTy}
    {mutable : Bool}
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardTarget : ChainGuard env (LVal.base lhsTop)
      (LVal.base target)) :
    ¬ nested ⊢ (LVal.base finalLhs) ↝ (.borrow mutable target) := by
  intro hentryNested
  rcases EnvWrite.pathSelect_update_eq henvFinal hselectFinal hwriteFinal with
    ⟨updatedTy, hupdate, hnested⟩
  have hnotWriteNested :
      ¬ WriteProhibited nested lhsTop :=
    not_writeProhibited_of_pointwise
      (env := env₃) (result := nested) (fun z => (hpoint z).symm)
      hnotWriteTop
  have hbLook :
      nested.slotAt (LVal.base finalLhs) =
        some { rootSlot with ty := updatedTy } := by
    rw [hnested]
    simp [Env.update]
  have hgraftContains :
      ∀ {mutable : Bool} {u : LVal},
        PartialTyContains updatedTy (.borrow mutable u) →
        PartialTyContains (.ty rhsTy) (.borrow mutable u) := by
    intro mutable u hcontains
    exact PathSelect.update_borrows hselectFinal hupdate hcontains
  rcases hentryNested with ⟨slot, hslot, hcontains⟩
  have hslotEq : slot = { rootSlot with ty := updatedTy } :=
    Option.some.inj (hslot.symm.trans hbLook)
  subst hslotEq
  exact graft_target_outside htySafe hnotWriteNested hbLook hgraftContains
    hcontains hguardTarget

/-- Hop links of the guarded write never read or point at the guarded leaf.
Each hop's descent prefix is an owner path from its own base variable; if it
read or reached the leaf, backward owner-chain uniqueness would root the
prefix at the final write's base with the hop annotation contained at or
below the graft position.  The graft is then value-equal to the old slot (the
holder-slot preservation field), so the annotation survives into the result
environment as a graft borrow — whose targets the write keeps off the guarded
chain — contradicting that hop targets are chain nodes. -/
theorem clean_hop_link_of_guarded_leaf
    {env env₃ nested : Env} {store : ProgramStore} {lhs finalLhs : LVal}
    {rhsTy : Ty} {bslotG : EnvSlot} {graftTy leafTy : PartialTy}
    {leaf : Location} {k : Nat} {rootSlotF : EnvSlot}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited nested lhs)
    (hpoint : ∀ y, env₃.slotAt y = nested.slotAt y)
    (hbLook : nested.slotAt (LVal.base finalLhs) =
      some { bslotG with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) (LVal.base finalLhs))
    (henvRootF : env.slotAt (LVal.base finalLhs) = some rootSlotF)
    (hselF : PathSelect (LVal.path finalLhs) rootSlotF.ty leafTy)
    (hleafChain : OwnsChain store (VariableProjection (LVal.base finalLhs))
      k leaf)
    (hlenF : k = (LVal.path finalLhs).length) :
    ∀ {s₀ target : LVal} {slotH : EnvSlot} {lf : Lifetime},
      env.slotAt (LVal.base s₀) = some slotH →
      PathSelect (LVal.path s₀) slotH.ty (.ty (.borrow true target)) →
      LValTyping env s₀ (.ty (.borrow true target)) lf →
      env ⊢ (LVal.base s₀) ↝ (.borrow true target) →
      env₃.slotAt (LVal.base s₀) = env.slotAt (LVal.base s₀) →
      (∀ mid, RuntimeFrame.LocReads store s₀ mid → mid ≠ leaf) ∧
        store.loc s₀ ≠ some leaf := by
  intro s₀ target slotH lf henvH hsel htyping hcont henv₃H
  have hrefute : LVal.base s₀ = LVal.base finalLhs →
      (LVal.path finalLhs).length ≤ (LVal.path s₀).length → False := by
    intro hbase hlen
    have hslotEq : slotH = rootSlotF := by
      rw [hbase] at henvH
      exact Option.some.inj (henvH.symm.trans henvRootF)
    subst hslotEq
    have hsplit : LVal.path s₀ =
        (LVal.path s₀).take (LVal.path finalLhs).length ++
          (LVal.path s₀).drop (LVal.path finalLhs).length :=
      (List.take_append_drop _ _).symm
    rw [hsplit] at hsel
    rcases PathSelect.append_inv hsel with ⟨mid₁, hsel₁, hsel₂⟩
    have htake : (LVal.path s₀).take (LVal.path finalLhs).length =
        LVal.path finalLhs :=
      Path.eq_of_length_eq (by
        simp only [List.length_take]
        omega)
    rw [htake] at hsel₁
    have hmidEq : mid₁ = leafTy := PathSelect.deterministic hsel₁ hselF
    have hcontLeaf : PartialTyContains leafTy (.borrow true target) := by
      rw [← hmidEq]
      exact PathSelect.contains_of_leaf hsel₂ PartialTyContains.here
    have hcontRoot : PartialTyContains slotH.ty (.borrow true target) :=
      PathSelect.contains_of_leaf hselF hcontLeaf
    have henv₃F : env₃.slotAt (LVal.base finalLhs) = some slotH := by
      rw [← hbase, henv₃H, hbase]
      exact henvRootF
    have hnestedB : nested.slotAt (LVal.base finalLhs) = some slotH :=
      (hpoint (LVal.base finalLhs)).symm.trans henv₃F
    have hslotGEq : { bslotG with ty := graftTy } = slotH :=
      Option.some.inj (hbLook.symm.trans hnestedB)
    have hgraftEq : graftTy = slotH.ty := congrArg EnvSlot.ty hslotGEq
    have hcontGraft : PartialTyContains graftTy (.borrow true target) := by
      rw [hgraftEq]
      exact hcontRoot
    have hcontF : env ⊢ (LVal.base finalLhs) ↝ (.borrow true target) := by
      rw [← hbase]
      exact hcont
    exact graft_target_outside htySafe hnotWrite hbLook hgraftContains
      hcontGraft (ChainGuard.step hguardB hcontF rfl)
  rcases hsafe.2 (LVal.base s₀) slotH henvH with
    ⟨rootValue₀, hstore₀, hvalid₀⟩
  rcases PathSelect.ownerChainPrefix_whenInitialized hstore₀
      (by simpa using hvalid₀) hsel with
    ⟨sLeaf, sLeafSlot, _hsLeafSlot, _hsLeafValid, hprefix₀⟩
  constructor
  · intro mid hmid hmidEq
    subst hmidEq
    rcases OwnerChainPrefix.locReads_ownsChain hprefix₀ hmid with
      ⟨j, hjChain, hjLt⟩
    rcases ownsChain_unique hvalidStore (var_not_owned hheap)
        (var_not_owned hheap) hjChain hleafChain with ⟨hrootEq, hjk⟩
    have hbase : LVal.base s₀ = LVal.base finalLhs := by
      simpa [VariableProjection] using hrootEq
    exact hrefute hbase (by omega)
  · intro hlocEq
    rcases hprefix₀ with ⟨hpathNil, _hleafRoot⟩ | ⟨k₀, _hchainAt, hchain₀, hlen₀⟩
    · cases s₀ with
      | var x =>
          have hleafVar : leaf = VariableProjection x := by
            simpa [ProgramStore.loc, VariableProjection] using hlocEq.symm
          cases hleafChain with
          | zero =>
              have hbaseEq : LVal.base finalLhs = x := by
                simpa [VariableProjection] using hleafVar
              refine hrefute (by simpa [LVal.base] using hbaseEq.symm) ?_
              simp only [LVal.path]
              omega
          | succ hchain' howns =>
              have hOwns : ProgramStore.Owns store leaf := ⟨_, howns⟩
              rw [hleafVar] at hOwns
              exact var_not_owned hheap
                (by simpa [VariableProjection] using hOwns)
      | deref s' =>
          exact absurd hpathNil (by simp [LVal.path])
    · have hleafEq : leaf = sLeaf :=
        ownsChain_loc_eq_of_length hchain₀ hlen₀ hlocEq
      have hchainLeaf₀ :
          OwnsChain store (VariableProjection (LVal.base s₀)) k₀ leaf := by
        rw [hleafEq]
        exact hchain₀
      rcases ownsChain_unique hvalidStore (var_not_owned hheap)
          (var_not_owned hheap) hchainLeaf₀ hleafChain with ⟨hrootEq, hkk⟩
      have hbase : LVal.base s₀ = LVal.base finalLhs := by
        simpa [VariableProjection] using hrootEq
      exact hrefute hbase (by omega)

/-- The final pure write selected by iterating borrow-hop reduction.  Any
environment write under the top-level rule premises reduces to a pure
(`PathSelect`) write over the same runtime location whose result is pointwise
value-equal to the original result environment. -/
def SelectFinalPackage (store : ProgramStore) (env env₃ : Env)
    (lhsTop lv : LVal) (rhsTy : Ty) (oldTy : PartialTy)
    (targetLifetime : Lifetime) : Prop :=
  ∃ (finalLhs : LVal) (rootSlot : EnvSlot) (nested : Env) (leaf : PartialTy),
    env.slotAt (LVal.base finalLhs) = some rootSlot ∧
    PathSelect (LVal.path finalLhs) rootSlot.ty leaf ∧
    EnvWrite env finalLhs rhsTy nested ∧
    (∀ y, env₃.slotAt y = nested.slotAt y) ∧
    LValTyping env finalLhs oldTy targetLifetime ∧
    store.loc lv = store.loc finalLhs ∧
    ChainGuard env (LVal.base lhsTop) (LVal.base finalLhs) ∧
    ((finalLhs = lv ∨
      ∃ (holder : Name) (path' : Path) (target' : LVal),
        env ⊢ holder ↝ (.borrow true target') ∧
        finalLhs = prependPath path' target') ∧
      HopsTo env env₃ lv finalLhs)

theorem EnvWrite.select_final
    {store : ProgramStore} {env env₃ : Env} {lhsTop : LVal}
    {rhsTy : Ty} {oldTy : PartialTy} {targetLifetime : Lifetime}
    (hsafeStore : SafeAbstraction store env)
    (hcbwf : ContainedBorrowsWellFormed env)
    (hsafeB : BorrowSafeEnv env)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy)) :
    EnvWrite env lhsTop rhsTy env₃ →
    LValTyping env lhsTop oldTy targetLifetime →
    SelectFinalPackage store env env₃ lhsTop lhsTop rhsTy oldTy
      targetLifetime := by
  intro hwrite hlvTop
  refine EnvWrite.rec
    (motive_1 := fun path old ty result updated _ =>
      ∀ {wcur : LVal} {rootSlot : EnvSlot} {lfc : Lifetime},
        LValTyping env wcur old lfc →
        LValTyping env (prependPath path wcur) oldTy targetLifetime →
        (∀ {mutable : Bool} {u : LVal},
          PartialTyContains old (.borrow mutable u) →
          env ⊢ (LVal.base wcur) ↝ (.borrow mutable u)) →
        ChainGuard env (LVal.base lhsTop) (LVal.base wcur) →
        env.slotAt (LVal.base wcur) = some rootSlot →
        PathSelect (LVal.path wcur) rootSlot.ty old →
        ShapeCompatible env oldTy (.ty ty) →
        (∃ leaf, PathSelect path old leaf) ∨
          (updated = old ∧
            ((∀ y, env₃.slotAt y =
                (result.update (LVal.base wcur) rootSlot).slotAt y) →
              SelectFinalPackage store env env₃ lhsTop
                (prependPath path wcur) ty oldTy targetLifetime)))
    (motive_2 := fun lv ty result _ =>
      LValTyping env lv oldTy targetLifetime →
      ChainGuard env (LVal.base lhsTop) (LVal.base lv) →
      ShapeCompatible env oldTy (.ty ty) →
      (∀ y, env₃.slotAt y = result.slotAt y) →
      SelectFinalPackage store env env₃ lhsTop lv ty oldTy targetLifetime)
    ?strong ?box ?boxFull ?mutBorrow ?intro hwrite hlvTop ChainGuard.base
    hshape (fun _ => rfl)
  case strong =>
    intro _old _ty wcur rootSlot lfc _hwcur _hlhs _hcontainsW _hguard
      _henvRoot _hselw _hshapePt
    left
    exact ⟨_, PathSelect.here⟩
  case box =>
    intro _env₂ _path _inner _updatedInner _ty _hinner ih
      wcur rootSlot lfc hwcur hlhs hcontainsW hguard henvRoot hselw hshapePt
    have hpathEq :
        prependPath _path wcur.deref = prependPath (() :: _path) wcur := by
      simp [prependPath_deref_comm, prependPath]
    have hlhs' :
        LValTyping env (prependPath _path wcur.deref) oldTy
          targetLifetime := by
      simpa [hpathEq] using hlhs
    rcases ih (LValTyping.box hwcur) hlhs'
        (by
          intro mutable u hcontains
          exact hcontainsW (PartialTyContains.box hcontains))
        hguard henvRoot
        (by simpa [LVal.path] using PathSelect.snoc_box hselw)
        hshapePt with
      hselect | ⟨hupdEq, himpl⟩
    · rcases hselect with ⟨leaf, hselect⟩
      left
      exact ⟨leaf, PathSelect.box hselect⟩
    · refine Or.inr ⟨by rw [hupdEq], ?_⟩
      intro hp
      have hfinal := himpl hp
      rw [hpathEq] at hfinal
      exact hfinal
  case boxFull =>
    intro _env₂ _path _inner _updatedInner _ty _hinner ih
      wcur rootSlot lfc hwcur hlhs hcontainsW hguard henvRoot hselw hshapePt
    have hpathEq :
        prependPath _path wcur.deref = prependPath (() :: _path) wcur := by
      simp [prependPath_deref_comm, prependPath]
    have hlhs' :
        LValTyping env (prependPath _path wcur.deref) oldTy
          targetLifetime := by
      simpa [hpathEq] using hlhs
    rcases ih (LValTyping.boxFull hwcur) hlhs'
        (by
          intro mutable u hcontains
          exact hcontainsW (PartialTyContains.tyBox hcontains))
        hguard henvRoot
        (by simpa [LVal.path] using PathSelect.snoc_boxFull hselw)
        hshapePt with
      hselect | ⟨hupdEq, himpl⟩
    · rcases hselect with ⟨leaf, hselect⟩
      left
      exact ⟨leaf, PathSelect.boxFull hselect⟩
    · refine Or.inr ⟨by rw [hupdEq]; simp [partialTyRebox], ?_⟩
      intro hp
      have hfinal := himpl hp
      rw [hpathEq] at hfinal
      exact hfinal
  case mutBorrow =>
    intro _env₂ path target ty hwriteNested ihNested
      wcur rootSlot lfc hwcur hlhs hcontainsW hguard henvRoot hselw hshapePt
    refine Or.inr ⟨rfl, ?_⟩
    intro hp
    have hpathEq :
        prependPath path wcur.deref = prependPath (() :: path) wcur := by
      simp [prependPath_deref_comm, prependPath]
    have hlhs' :
        LValTyping env (prependPath path wcur.deref) oldTy targetLifetime := by
      simpa [hpathEq] using hlhs
    have hrebased :
        LValTyping env (prependPath path target) oldTy targetLifetime :=
      LValTyping.rebase_hop hwcur path hlhs'
    have hannBase :
        env ⊢ (LVal.base wcur) ↝ (.borrow true target) :=
      hcontainsW PartialTyContains.here
    have hpreserved :
        _env₂.slotAt (LVal.base wcur) = some rootSlot :=
      EnvWrite.hop_nested_slot_preserved hcbwf hsafeB hnotWriteTop hguard
        hp henvRoot hannBase hwriteNested hrebased hshapePt
    have henv₃nested : ∀ y, env₃.slotAt y = _env₂.slotAt y := by
      intro y
      exact (hp y).trans (Env.update_same_pointwise hpreserved y)
    rcases LValTyping.partialTyBorrowsWellFormedInSlot hcbwf hwcur
        PartialTyContains.here with
      ⟨targetTy, targetLifetime', htargetTyping, _houtlives, _hbase⟩
    have hlocBase :
        store.loc wcur.deref = store.loc target :=
      lvalTyping_deref_borrow_loc_eq_whenInitialized hsafeStore hwcur
        htargetTyping
    have hloc :
        store.loc (prependPath path wcur.deref) =
          store.loc (prependPath path target) :=
      ProgramStore.loc_prependPath_eq_of_loc_eq hlocBase path
    have hguardTarget :
        ChainGuard env (LVal.base lhsTop) (LVal.base target) :=
      ChainGuard.step hguard hannBase rfl
    have hfinal :=
      ihNested hrebased (by simpa using hguardTarget) hshapePt henv₃nested
    rcases hfinal with
      ⟨finalLhs, rootSlot', nestedEnv, leaf, henvFinal, hselectFinal,
        hwriteFinal, hpointFinal, htypingFinal, hlocFinal, hguardFinal,
        hlast, hhops⟩
    refine ⟨finalLhs, rootSlot', nestedEnv, leaf, henvFinal, hselectFinal,
      hwriteFinal, hpointFinal, htypingFinal, ?_, hguardFinal, ?_, ?_⟩
    · calc store.loc (prependPath (() :: path) wcur)
          = store.loc (prependPath path wcur.deref) := by rw [hpathEq]
        _ = store.loc (prependPath path target) := hloc
        _ = store.loc finalLhs := hlocFinal
    · rcases hlast with hEq | hHop
      · exact Or.inr ⟨LVal.base wcur, path, target, hannBase, hEq⟩
      · exact Or.inr hHop
    · rw [← hpathEq]
      exact HopsTo.hop henvRoot hselw hwcur hannBase
        ((henv₃nested (LVal.base wcur)).trans
          (hpreserved.trans henvRoot.symm)) hhops
  case intro =>
    intro _env₂ lv slot ty updatedTy hslot hupdate ih hlv hguard hshapePt
      hpoint
    rcases ih (wcur := .var (LVal.base lv)) (rootSlot := slot)
        (LValTyping.var (by simpa [LVal.base] using hslot))
        (by
          rw [prependPath_path_base]
          exact hlv)
        (by
          intro mutable u hcontains
          exact ⟨slot, by simpa [LVal.base] using hslot, hcontains⟩)
        (by simpa [LVal.base] using hguard)
        (by simpa [LVal.base] using hslot)
        (by simpa [LVal.path] using PathSelect.here)
        hshapePt with
      hselect | ⟨hupdEq, himpl⟩
    · rcases hselect with ⟨leaf, hselect⟩
      exact ⟨lv, slot, _env₂.update (LVal.base lv) { slot with ty := updatedTy },
        leaf, hslot, hselect, EnvWrite.intro hslot hupdate, hpoint, hlv,
        rfl, hguard, Or.inl rfl, HopsTo.refl⟩
    · have hslotEta : { slot with ty := updatedTy } = slot := by
        rw [hupdEq]
      have hp :
          ∀ y, env₃.slotAt y =
            (_env₂.update (LVal.base (LVal.var (LVal.base lv)))
              slot).slotAt y := by
        intro y
        simpa [LVal.base, hslotEta] using hpoint y
      have hfinal := himpl hp
      rw [prependPath_path_base] at hfinal
      exact hfinal

theorem validPartialValueWhenInitialized_select_final_rhs
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop finalLhs : LVal} {rhsTy : Ty} {oldTy leaf : PartialTy}
    {targetLifetime : Lifetime} {rootSlot : EnvSlot} {value : Value}
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwriteTop : EnvWrite env lhsTop rhsTy env₃)
    (hlvTop : LValTyping env lhsTop oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leaf)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ y, env₃.slotAt y = nested.slotAt y) :
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    ValidPartialValueWhenInitialized nested store (.value value)
      (.ty rhsTy) := by
  intro hvalidValue
  have hcontainsNested :
      ∀ {mutable : Bool} {target : LVal},
        PartialTyContains (.ty rhsTy) (.borrow mutable target) →
        nested ⊢ (LVal.base finalLhs) ↝ (.borrow mutable target) :=
    (EnvWrite.pathSelect_result_contains henvFinal hselectFinal
      hwriteFinal).1
  have hcontainsTop :
      ∀ {mutable : Bool} {target : LVal},
        PartialTyContains (.ty rhsTy) (.borrow mutable target) →
        ∃ holder, env₃ ⊢ holder ↝ (.borrow mutable target) := by
    intro mutable target hcontains
    rcases hcontainsNested hcontains with ⟨slot, hslot, hcontainsSlot⟩
    exact ⟨LVal.base finalLhs, slot,
      (hpoint (LVal.base finalLhs)).trans hslot, hcontainsSlot⟩
  have hvalidEnv₃ :
      ValidPartialValueWhenInitialized env₃ store (.value value)
        (.ty rhsTy) :=
    validPartialValueWhenInitialized_envWrite_of_result_contains
      hcbwf hborrowSafe htySafe hwriteTop hlvTop hshape hwellTy
      hnotWriteTop hcontainsTop hvalidValue
  exact validPartialValueWhenInitialized_transport_env
    (env := env₃) (result := nested)
    (fun htarget =>
      TargetInitialized.transport_of_pointwise
        (env := env₃) (result := nested)
        (fun y => (hpoint y).symm) htarget)
    hvalidEnv₃

theorem validPartialValueWhenInitialized_select_final_unchanged_slot
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop finalLhs : LVal} {rhsTy : Ty} {oldTy leaf : PartialTy}
    {targetLifetime : Lifetime} {rootSlot otherEnvSlot : EnvSlot}
    {oldValue : PartialValue} {y : Name}
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwriteTop : EnvWrite env lhsTop rhsTy env₃)
    (hlvTop : LValTyping env lhsTop oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leaf)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hyFinal : y ≠ LVal.base finalLhs)
    (henvY : env.slotAt y = some otherEnvSlot) :
    ValidPartialValueWhenInitialized env store oldValue otherEnvSlot.ty →
    ValidPartialValueWhenInitialized nested store oldValue otherEnvSlot.ty := by
  intro hvalidOld
  have hunchangedNested :
      nested.slotAt y = env.slotAt y :=
    (EnvWrite.pathSelect_result_contains henvFinal hselectFinal
      hwriteFinal).2 y hyFinal
  have henv₃Y : env₃.slotAt y = some otherEnvSlot := by
    rw [hpoint y, hunchangedNested, henvY]
  have hcontainsTop :
      ∀ {mutable : Bool} {target : LVal},
        PartialTyContains otherEnvSlot.ty (.borrow mutable target) →
        ∃ holder, env₃ ⊢ holder ↝ (.borrow mutable target) := by
    intro mutable target hcontains
    exact ⟨y, otherEnvSlot, henv₃Y, hcontains⟩
  have hvalidEnv₃ :
      ValidPartialValueWhenInitialized env₃ store oldValue otherEnvSlot.ty :=
    validPartialValueWhenInitialized_envWrite_of_result_contains
      hcbwf hborrowSafe htySafe hwriteTop hlvTop hshape hwellTy
      hnotWriteTop hcontainsTop hvalidOld
  exact validPartialValueWhenInitialized_transport_env
    (env := env₃) (result := nested)
    (fun htarget =>
      TargetInitialized.transport_of_pointwise
        (env := env₃) (result := nested)
        (fun z => (hpoint z).symm) htarget)
    hvalidEnv₃

/-- Reverse outside-chain transport for the result of a guarded write.  If a
post-write lvalue is rooted outside the source write chain, then its typing
reads only unchanged source slots.  The auxiliary containment result records
that any borrow annotation in the transported type is still held outside the
chain in the post-write environment; this is the fact needed for subsequent
borrow-hop exclusions. -/
theorem LValTyping.transport_into_source_of_outside_chain
    {env env₃ : Env} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    (hsafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b) :
    ∀ {t : LVal} {pt : PartialTy} {lf : Lifetime},
      ¬ ChainGuard env (LVal.base lhs) (LVal.base t) →
      LValTyping env₃ t pt lf →
      LValTyping env t pt lf ∧
        (∀ {mutable : Bool} {u : LVal},
          PartialTyContains pt (.borrow mutable u) →
          ∃ z, ¬ ChainGuard env (LVal.base lhs) z ∧
            env₃ ⊢ z ↝ (.borrow mutable u)) := by
  intro t pt lf houtside htyping
  induction htyping with
  | var hslot =>
      rename_i y s
      have hyb : y ≠ b := by
        intro hy
        exact houtside (by simpa [hy, LVal.base] using hguardB)
      refine ⟨.var ((hne y hyb) ▸ hslot), ?_⟩
      intro mutable u hcontains
      exact ⟨y, houtside, ⟨s, hslot, hcontains⟩⟩
  | box _ ih =>
      rcases ih houtside with ⟨hsource, hcontains⟩
      exact ⟨.box hsource, fun h => hcontains (PartialTyContains.box h)⟩
  | boxFull _ ih =>
      rcases ih houtside with ⟨hsource, hcontains⟩
      exact ⟨.boxFull hsource,
        fun h => hcontains (PartialTyContains.tyBox h)⟩
  | borrow hw hu ihBorrow ihTarget =>
      rename_i w u m blf tlf targetTy
      rcases ihBorrow houtside with ⟨hwSource, hborrowContains⟩
      rcases hborrowContains PartialTyContains.here with
        ⟨holder, hholderOutside, hholderContains⟩
      have huOutside :
          ¬ ChainGuard env (LVal.base lhs) (LVal.base u) := by
        intro hguardU
        exact hholderOutside
          (chain_entry_env3 hsafe htySafe hnotWrite hne hbLook
            hgraftContains hguardB hholderContains hguardU).2
      rcases ihTarget huOutside with ⟨huSource, htargetContains⟩
      exact ⟨.borrow hwSource huSource, htargetContains⟩

/-- If a post-write lvalue's runtime location is protected by the guarded
changed slot, then the lvalue's base is itself on the source write chain. -/
theorem lval_loc_chain_protected_base_on_chain
    {env env₃ : Env} {store : ProgramStore} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hsafeEnv : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime}
      {location : Location},
      LValTyping env₃ lv partialTy lifetime →
      store.loc lv = some location →
      RuntimeFrame.ProtectedByBase store b location →
      ChainGuard env (LVal.base lhs) (LVal.base lv) := by
  intro lv partialTy lifetime location htyping
  induction htyping generalizing location with
  | var hslot =>
      rename_i x slot
      intro hloc hprotected
      simp [ProgramStore.loc] at hloc
      subst hloc
      cases hprotected with
      | inl hroot =>
          have hxb : x = b := by
            simpa [VariableProjection] using hroot
          simpa [hxb, LVal.base] using hguardB
      | inr hpath =>
          rcases hheap _ (ProgramStore.OwnsTransitively.to_owns hpath) with
            ⟨address, hheapLocation⟩
          cases hheapLocation
  | box hsource ih =>
      rename_i source inner sourceLifetime
      intro hloc hprotected
      by_cases hchain :
          ChainGuard env (LVal.base lhs) (LVal.base source)
      · simpa [LVal.base] using hchain
      · rcases
          LValTyping.transport_into_source_of_outside_chain
            hsafeEnv htySafe hnotWrite hne hbLook hgraftContains hguardB
            hchain hsource with
          ⟨hsourceEnv, _hsourceContains⟩
        rcases lvalTyping_defined_location_whenInitialized hsafe hsourceEnv with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
            hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @box ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
            have hlocEq : location = ownedLocation := by
              simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
            have hprotectedOwned :
                RuntimeFrame.ProtectedByBase store b ownedLocation := by
              simpa [hlocEq] using hprotected
            have hownsAt :
                ProgramStore.OwnsAt store ownedLocation sourceLocation :=
              ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
            have hsourceProtected :
                RuntimeFrame.ProtectedByBase store b sourceLocation :=
              protectedByBase_parent_of_ownsAt hvalidStore
                (var_not_owned hheap) hprotectedOwned hownsAt
            exact ih hsourceLoc hsourceProtected
  | boxFull hsource ih =>
      rename_i source inner sourceLifetime
      intro hloc hprotected
      by_cases hchain :
          ChainGuard env (LVal.base lhs) (LVal.base source)
      · simpa [LVal.base] using hchain
      · rcases
          LValTyping.transport_into_source_of_outside_chain
            hsafeEnv htySafe hnotWrite hne hbLook hgraftContains hguardB
            hchain hsource with
          ⟨hsourceEnv, _hsourceContains⟩
        rcases lvalTyping_defined_location_whenInitialized hsafe hsourceEnv with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
            hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @boxFull ownedLocation ownedSlot inner hownedSlot _hinnerValid =>
            have hlocEq : location = ownedLocation := by
              simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
            have hprotectedOwned :
                RuntimeFrame.ProtectedByBase store b ownedLocation := by
              simpa [hlocEq] using hprotected
            have hownsAt :
                ProgramStore.OwnsAt store ownedLocation sourceLocation :=
              ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
            have hsourceProtected :
                RuntimeFrame.ProtectedByBase store b sourceLocation :=
              protectedByBase_parent_of_ownsAt hvalidStore
                (var_not_owned hheap) hprotectedOwned hownsAt
            exact ih hsourceLoc hsourceProtected
  | borrow hsource htarget ihSource ihTarget =>
      rename_i source target mutable borrowLifetime targetLifetime targetTy
      intro hloc hprotected
      by_cases hchain :
          ChainGuard env (LVal.base lhs) (LVal.base source)
      · simpa [LVal.base] using hchain
      · rcases
          LValTyping.transport_into_source_of_outside_chain
            hsafeEnv htySafe hnotWrite hne hbLook hgraftContains hguardB
            hchain hsource with
          ⟨hsourceEnv, hsourceContains⟩
        rcases hsourceContains PartialTyContains.here with
          ⟨holder, hholderOutside, hholderContains⟩
        rcases lvalTyping_defined_location_whenInitialized hsafe hsourceEnv with
          ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
            hsourceValid⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hsourceValid with
        | @borrowLive borrowedLocation mutable target _hinitialized htargetLoc =>
            have hlocEq : location = borrowedLocation := by
              simpa [ProgramStore.loc, hsourceLoc, hsourceSlot] using hloc.symm
            have hprotectedBorrowed :
                RuntimeFrame.ProtectedByBase store b borrowedLocation := by
              simpa [hlocEq] using hprotected
            have htargetChain := ihTarget htargetLoc hprotectedBorrowed
            exact False.elim
              (hholderOutside
                (chain_entry_env3 hsafeEnv htySafe hnotWrite hne hbLook
                  hgraftContains hguardB hholderContains htargetChain).2)
        | @borrowStale borrowedLocation mutable target hstale =>
            by_cases htargetChain :
                ChainGuard env (LVal.base lhs) (LVal.base target)
            · exact False.elim
                (hholderOutside
                  (chain_entry_env3 hsafeEnv htySafe hnotWrite hne hbLook
                    hgraftContains hguardB hholderContains htargetChain).2)
            · rcases
                LValTyping.transport_into_source_of_outside_chain
                  hsafeEnv htySafe hnotWrite hne hbLook hgraftContains hguardB
                  htargetChain htarget with
                ⟨htargetEnv, _⟩
              exact False.elim (hstale ⟨_, _, htargetEnv⟩)

/-- A value stored in an off-chain variable slot cannot owner-reach the leaf of
the guarded changed slot. -/
theorem ownerReaches_stored_ne_guarded_chain_leaf {env : Env}
    {store : ProgramStore} {lhs : LVal} {b y : Name}
    {k : Nat} {leafLoc : Location}
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hleafChain : OwnsChain store (VariableProjection b) k leafLoc)
    (hguardB : ChainGuard env (LVal.base lhs) b)
    (hyOutside : ¬ ChainGuard env (LVal.base lhs) y) :
    ∀ {value : PartialValue} {partialTy : PartialTy}
      {lifetime : Lifetime},
      store.slotAt (VariableProjection y) = some ⟨value, lifetime⟩ →
      ¬ RuntimeFrame.OwnerReaches store value partialTy leafLoc := by
  intro value partialTy lifetime hstored
  have hstorageNeRoot : VariableProjection y ≠ VariableProjection b := by
    intro hEq
    have hyb : y = b := by
      simpa [VariableProjection] using hEq
    exact hyOutside (hyb ▸ hguardB)
  exact ownerReaches_stored_ne_chain_leaf hvalidStore
    (var_not_owned hheap) (var_not_owned hheap) hstorageNeRoot
    hleafChain hstored

/-- Loc-read routes hitting the guarded leaf must be rooted on the source write
chain. -/
theorem locReads_chain_protected_base_on_chain
    {env env₃ : Env} {store : ProgramStore} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    {leafLoc : Location}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hsafeEnv : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b)
    (hleafProtected : RuntimeFrame.ProtectedByBase store b leafLoc) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env₃ lv partialTy lifetime →
      RuntimeFrame.LocReads store lv leafLoc →
      ChainGuard env (LVal.base lhs) (LVal.base lv) := by
  intro lv partialTy lifetime htyping
  induction htyping with
  | var hslot =>
      intro hreads
      cases hreads
  | box hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          exact by
            simpa [LVal.base] using
              lval_loc_chain_protected_base_on_chain
                hsafe hvalidStore hheap hsafeEnv htySafe hnotWrite hne
                hbLook hgraftContains hguardB hsource hloc hleafProtected
      | there hsourceReads =>
          exact ih hsourceReads
  | boxFull hsource ih =>
      intro hreads
      cases hreads with
      | here hloc =>
          exact by
            simpa [LVal.base] using
              lval_loc_chain_protected_base_on_chain
                hsafe hvalidStore hheap hsafeEnv htySafe hnotWrite hne
                hbLook hgraftContains hguardB hsource hloc hleafProtected
      | there hsourceReads =>
          exact ih hsourceReads
  | borrow hsource htarget ihSource ihTarget =>
      intro hreads
      cases hreads with
      | here hloc =>
          exact by
            simpa [LVal.base] using
              lval_loc_chain_protected_base_on_chain
                hsafe hvalidStore hheap hsafeEnv htySafe hnotWrite hne
                hbLook hgraftContains hguardB hsource hloc hleafProtected
      | there hsourceReads =>
          exact ihSource hsourceReads

/-- Borrow-dependency routes whose borrow targets are off the guarded source
chain cannot hit the guarded leaf. -/
theorem borrowDependencyWhenInitialized_chain_leaf_ne_of_target_outside
    {env env₃ : Env} {store : ProgramStore} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    {leafLoc : Location}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hsafeEnv : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b)
    (hleafProtected : RuntimeFrame.ProtectedByBase store b leafLoc) :
    ∀ {value : PartialValue} {partialTy : PartialTy}
      {dependency : Location},
      (∀ {mutable : Bool} {target : LVal},
        PartialTyContains partialTy (.borrow mutable target) →
        ¬ ChainGuard env (LVal.base lhs) (LVal.base target)) →
      RuntimeFrame.BorrowDependencyWhenInitialized env₃ store value
        partialTy dependency →
      dependency = leafLoc →
      False := by
  intro value partialTy dependency hcontains hdependency
  induction hdependency with
  | @borrow location dependency mutable target hinitialized _hloc hreads =>
      intro hdependencyEq
      rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
      have htargetGuard :
          ChainGuard env (LVal.base lhs) (LVal.base target) :=
        locReads_chain_protected_base_on_chain
          hsafe hvalidStore hheap hsafeEnv htySafe hnotWrite hne hbLook
          hgraftContains hguardB hleafProtected htargetTyping
          (by simpa [hdependencyEq] using hreads)
      exact (hcontains PartialTyContains.here) htargetGuard
  | boxInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.box hcontainsInner))
        hdependencyEq
  | boxFullInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.tyBox hcontainsInner))
        hdependencyEq

/-- If every contained borrow target avoids the leaf and the owner spine avoids
the leaf, then the initialized reach relation avoids that leaf. -/
theorem reachesWhenInitialized_ne_of_borrow_targets_locReads_ne
    {env : Env} {store : ProgramStore} {leafLoc : Location}
    {value : PartialValue} {partialTy : PartialTy}
    (hcontains : ∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      ∀ {location : Location},
        RuntimeFrame.LocReads store target location →
        location ≠ leafLoc)
    (hownerNoReach :
      ¬ RuntimeFrame.OwnerReaches store value partialTy leafLoc) :
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized env store value partialTy location →
      location ≠ leafLoc := by
  intro location hreach
  induction hreach with
  | undefOf hskel hstrength howner =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using
          RuntimeFrame.OwnerReaches.undefOf hskel hstrength howner)
  | boxHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxHere hslot)
  | boxInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.box hcontainsInner))
        (by
          intro howner
          exact hownerNoReach (RuntimeFrame.OwnerReaches.boxInner hslot howner))
        hlocation
  | boxFullHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.tyBox hcontainsInner))
        (by
          intro howner
          exact hownerNoReach
            (RuntimeFrame.OwnerReaches.boxFullInner hslot howner))
        hlocation
  | borrow _hinitialized _hloc hreads =>
      intro hlocation
      exact hcontains PartialTyContains.here hreads hlocation

/-- Live initialized reach only needs read-exclusion for initialized borrow
targets.  Stale annotations never contribute `ReachesWhenInitialized.borrow`,
so the caller may use the supplied `TargetInitialized` evidence to prove the
target is one of the live entries preserved by the write. -/
theorem reachesWhenInitialized_ne_of_live_borrow_targets_locReads_ne
    {env : Env} {store : ProgramStore} {leafLoc : Location}
    {value : PartialValue} {partialTy : PartialTy}
    (hcontains : ∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      TargetInitialized env target →
      ∀ {location : Location},
        RuntimeFrame.LocReads store target location →
        location ≠ leafLoc)
    (hownerNoReach :
      ¬ RuntimeFrame.OwnerReaches store value partialTy leafLoc) :
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized env store value partialTy location →
      location ≠ leafLoc := by
  intro location hreach
  induction hreach with
  | undefOf hskel hstrength howner =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using
          RuntimeFrame.OwnerReaches.undefOf hskel hstrength howner)
  | boxHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxHere hslot)
  | boxInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner hinitialized
          exact hcontains (PartialTyContains.box hcontainsInner)
            hinitialized)
        (by
          intro howner
          exact hownerNoReach (RuntimeFrame.OwnerReaches.boxInner hslot howner))
        hlocation
  | boxFullHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner hinitialized
          exact hcontains (PartialTyContains.tyBox hcontainsInner)
            hinitialized)
        (by
          intro howner
          exact hownerNoReach
            (RuntimeFrame.OwnerReaches.boxFullInner hslot howner))
        hlocation
  | borrow hinitialized _hloc hreads =>
      intro hlocation
      exact hcontains PartialTyContains.here hinitialized hreads hlocation

/-- Values whose contained borrow targets are off the guarded source chain cannot
reach the guarded leaf, assuming their owner roots also do not reach that leaf. -/
theorem reachesWhenInitialized_chain_leaf_ne_of_target_outside
    {env env₃ : Env} {store : ProgramStore} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    {leafLoc : Location} {value : PartialValue} {partialTy : PartialTy}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hsafeEnv : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b)
    (hleafProtected : RuntimeFrame.ProtectedByBase store b leafLoc)
    (hcontains : ∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      ¬ ChainGuard env (LVal.base lhs) (LVal.base target))
    (hownerNoReach :
      ¬ RuntimeFrame.OwnerReaches store value partialTy leafLoc) :
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized env₃ store value partialTy location →
      location ≠ leafLoc := by
  intro location hreach
  induction hreach with
  | undefOf hskel hstrength howner =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using
          RuntimeFrame.OwnerReaches.undefOf hskel hstrength howner)
  | boxHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxHere hslot)
  | boxInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.box hcontainsInner))
        (by
          intro howner
          exact hownerNoReach (RuntimeFrame.OwnerReaches.boxInner hslot howner))
        hlocation
  | boxFullHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.tyBox hcontainsInner))
        (by
          intro howner
          exact hownerNoReach
            (RuntimeFrame.OwnerReaches.boxFullInner hslot howner))
        hlocation
  | borrow hinitialized hloc hreads =>
      intro hlocation
      exact
        borrowDependencyWhenInitialized_chain_leaf_ne_of_target_outside
          hsafe hvalidStore hheap hsafeEnv htySafe hnotWrite hne hbLook
          hgraftContains hguardB hleafProtected hcontains
          (RuntimeFrame.BorrowDependencyWhenInitialized.borrow
            hinitialized hloc hreads)
          hlocation

/-- Borrow-dependency routes from an off-chain value cannot hit the guarded
leaf. -/
theorem borrowDependencyWhenInitialized_chain_leaf_ne_of_outside_chain
    {env env₃ : Env} {store : ProgramStore} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    {leafLoc : Location}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hsafeEnv : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b)
    (hleafProtected : RuntimeFrame.ProtectedByBase store b leafLoc) :
    ∀ {value : PartialValue} {partialTy : PartialTy}
      {dependency : Location},
      (∀ {mutable : Bool} {target : LVal},
        PartialTyContains partialTy (.borrow mutable target) →
        ∃ holder, ¬ ChainGuard env (LVal.base lhs) holder ∧
          env₃ ⊢ holder ↝ (.borrow mutable target)) →
      RuntimeFrame.BorrowDependencyWhenInitialized env₃ store value
        partialTy dependency →
      dependency = leafLoc →
      False := by
  intro value partialTy dependency hcontains hdependency
  induction hdependency with
  | @borrow location dependency mutable target hinitialized _hloc hreads =>
      intro hdependencyEq
      rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
      have htargetGuard :
          ChainGuard env (LVal.base lhs) (LVal.base target) :=
        locReads_chain_protected_base_on_chain
          hsafe hvalidStore hheap hsafeEnv htySafe hnotWrite hne hbLook
          hgraftContains hguardB hleafProtected htargetTyping
          (by simpa [hdependencyEq] using hreads)
      rcases hcontains PartialTyContains.here with
        ⟨holder, hholderOutside, hholderContains⟩
      exact hholderOutside
        (chain_entry_env3 hsafeEnv htySafe hnotWrite hne hbLook
          hgraftContains hguardB hholderContains htargetGuard).2
  | boxInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.box hcontainsInner))
        hdependencyEq
  | boxFullInner _hslot _hinner ih =>
      intro hdependencyEq
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.tyBox hcontainsInner))
        hdependencyEq

/-- Values whose contained borrows are held off the guarded chain cannot reach
the guarded leaf, assuming their owner roots also do not reach that leaf. -/
theorem reachesWhenInitialized_chain_leaf_ne_of_outside_chain
    {env env₃ : Env} {store : ProgramStore} {lhs : LVal} {rhsTy : Ty}
    {b : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    {leafLoc : Location} {value : PartialValue} {partialTy : PartialTy}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hsafeEnv : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ y, y ≠ b → env₃.slotAt y = env.slotAt y)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b)
    (hleafProtected : RuntimeFrame.ProtectedByBase store b leafLoc)
    (hcontains : ∀ {mutable : Bool} {target : LVal},
      PartialTyContains partialTy (.borrow mutable target) →
      ∃ holder, ¬ ChainGuard env (LVal.base lhs) holder ∧
        env₃ ⊢ holder ↝ (.borrow mutable target))
    (hownerNoReach :
      ¬ RuntimeFrame.OwnerReaches store value partialTy leafLoc) :
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized env₃ store value partialTy location →
      location ≠ leafLoc := by
  intro location hreach
  induction hreach with
  | undefOf hskel hstrength howner =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using
          RuntimeFrame.OwnerReaches.undefOf hskel hstrength howner)
  | boxHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxHere hslot)
  | boxInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.box hcontainsInner))
        (by
          intro howner
          exact hownerNoReach (RuntimeFrame.OwnerReaches.boxInner hslot howner))
        hlocation
  | boxFullHere hslot =>
      intro hlocation
      exact hownerNoReach
        (by simpa [hlocation] using RuntimeFrame.OwnerReaches.boxFullHere hslot)
  | boxFullInner hslot _hinner ih =>
      intro hlocation
      exact ih
        (by
          intro mutable target hcontainsInner
          exact hcontains (PartialTyContains.tyBox hcontainsInner))
        (by
          intro howner
          exact hownerNoReach
            (RuntimeFrame.OwnerReaches.boxFullInner hslot howner))
        hlocation
  | borrow hinitialized hloc hreads =>
      intro hlocation
      exact
        borrowDependencyWhenInitialized_chain_leaf_ne_of_outside_chain
          hsafe hvalidStore hheap hsafeEnv htySafe hnotWrite hne hbLook
          hgraftContains hguardB hleafProtected hcontains
          (RuntimeFrame.BorrowDependencyWhenInitialized.borrow
            hinitialized hloc hreads)
          hlocation

/-- Stored off-chain sibling slots do not reach the guarded chain leaf. -/
theorem reachesWhenInitialized_chain_leaf_ne_of_stored_outside_chain
    {env env₃ : Env} {store : ProgramStore} {lhs : LVal} {rhsTy : Ty}
    {b y : Name} {bslot : EnvSlot} {graftTy : PartialTy}
    {leafLoc : Location} {k : Nat}
    {otherEnvSlot : EnvSlot} {oldValue : PartialValue}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hsafeEnv : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWrite : ¬ WriteProhibited env₃ lhs)
    (hne : ∀ z, z ≠ b → env₃.slotAt z = env.slotAt z)
    (hbLook : env₃.slotAt b = some { bslot with ty := graftTy })
    (hgraftContains : ∀ {mutable : Bool} {u : LVal},
      PartialTyContains graftTy (.borrow mutable u) →
      PartialTyContains (.ty rhsTy) (.borrow mutable u))
    (hguardB : ChainGuard env (LVal.base lhs) b)
    (hleafChain : OwnsChain store (VariableProjection b) k leafLoc)
    (hyOutside : ¬ ChainGuard env (LVal.base lhs) y)
    (henvY : env.slotAt y = some otherEnvSlot)
    (hstoreY : store.slotAt (VariableProjection y) =
      some { value := oldValue, lifetime := otherEnvSlot.lifetime }) :
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized env₃ store oldValue
        otherEnvSlot.ty location →
      location ≠ leafLoc := by
  have hyb : y ≠ b := by
    intro hy
    exact hyOutside (hy ▸ hguardB)
  have henvY₃ : env₃.slotAt y = some otherEnvSlot := by
    rw [hne y hyb, henvY]
  intro location hreach
  exact reachesWhenInitialized_chain_leaf_ne_of_outside_chain
    hsafe hvalidStore hheap hsafeEnv htySafe hnotWrite hne hbLook
    hgraftContains hguardB (protectedByBase_of_ownsChain hleafChain)
    (by
      intro mutable target hcontains
      exact ⟨y, hyOutside, ⟨otherEnvSlot, henvY₃, hcontains⟩⟩)
    (ownerReaches_stored_ne_guarded_chain_leaf hvalidStore hheap hleafChain
      hguardB hyOutside hstoreY)
    hreach

/-- RHS values installed by the final pure write cannot reach the selected
runtime leaf in the pre-write store.  The pure write exposes the graft slot;
all graft borrows are RHS borrows, and `TyBorrowSafeAgainstEnv` keeps those
targets outside the guarded write chain. -/
theorem reachesWhenInitialized_select_final_rhs_ne_leaf
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop finalLhs : LVal} {rhsTy : Ty} {oldTy leafTy : PartialTy}
    {targetLifetime : Lifetime} {rootSlot : EnvSlot}
    {value : Value} {leafLoc : Location} {k : Nat}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwriteTop : EnvWrite env lhsTop rhsTy env₃)
    (hlvTop : LValTyping env lhsTop oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ y, env₃.slotAt y = nested.slotAt y)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hvalueHeap : ValueOwnerTargetsHeap value)
    (hvalueUnowned : ∀ owned, owned ∈ valueOwningLocations value →
      ¬ ProgramStore.Owns store owned) :
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized nested store (.value value)
        (.ty rhsTy) location →
      location ≠ leafLoc := by
  rcases EnvWrite.pathSelect_update_eq henvFinal hselectFinal hwriteFinal with
    ⟨updatedTy, hupdate, hnested⟩
  have hnotWriteNested :
      ¬ WriteProhibited nested lhsTop :=
    not_writeProhibited_of_pointwise
      (env := env₃) (result := nested) (fun y => (hpoint y).symm)
      hnotWriteTop
  have hne : ∀ y, y ≠ LVal.base finalLhs →
      nested.slotAt y = env.slotAt y := by
    intro y hy
    rw [hnested]
    simp [Env.update, hy]
  have hbLook :
      nested.slotAt (LVal.base finalLhs) =
        some { rootSlot with ty := updatedTy } := by
    rw [hnested]
    simp [Env.update]
  have hgraftContains :
      ∀ {mutable : Bool} {u : LVal},
        PartialTyContains updatedTy (.borrow mutable u) →
        PartialTyContains (.ty rhsTy) (.borrow mutable u) := by
    intro mutable u hcontains
    exact PathSelect.update_borrows hselectFinal hupdate hcontains
  intro location hreach
  exact reachesWhenInitialized_chain_leaf_ne_of_target_outside
    hsafe hvalidStore hheap hborrowSafe htySafe hnotWriteNested hne
    hbLook hgraftContains hguardFinal
    (protectedByBase_of_ownsChain hleafChain)
    (by
      intro mutable target hcontains htargetGuard
      exact graft_target_outside htySafe hnotWriteNested hbLook
        hgraftContains
        (PathSelect.update_contains_rhs hselectFinal hupdate hcontains)
        htargetGuard)
    (ownerReaches_value_ne_chain_leaf_of_unowned_root
      hvalidStore hheap hvalueHeap hvalueUnowned hleafChain)
    hreach

/-- Off-chain surviving source slots cannot reach the final selected leaf after
the pure final write. -/
theorem reachesWhenInitialized_select_final_stored_outside_ne_leaf
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop finalLhs : LVal} {rhsTy : Ty} {leafTy : PartialTy}
    {rootSlot otherEnvSlot : EnvSlot} {oldValue : PartialValue}
    {y : Name} {leafLoc : Location} {k : Nat}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hyOutside : ¬ ChainGuard env (LVal.base lhsTop) y)
    (henvY : env.slotAt y = some otherEnvSlot)
    (hstoreY : store.slotAt (VariableProjection y) =
      some { value := oldValue, lifetime := otherEnvSlot.lifetime }) :
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized nested store oldValue
        otherEnvSlot.ty location →
      location ≠ leafLoc := by
  rcases EnvWrite.pathSelect_update_eq henvFinal hselectFinal hwriteFinal with
    ⟨updatedTy, hupdate, hnested⟩
  have hnotWriteNested :
      ¬ WriteProhibited nested lhsTop :=
    not_writeProhibited_of_pointwise
      (env := env₃) (result := nested) (fun z => (hpoint z).symm)
      hnotWriteTop
  have hne : ∀ z, z ≠ LVal.base finalLhs →
      nested.slotAt z = env.slotAt z := by
    intro z hz
    rw [hnested]
    simp [Env.update, hz]
  have hbLook :
      nested.slotAt (LVal.base finalLhs) =
        some { rootSlot with ty := updatedTy } := by
    rw [hnested]
    simp [Env.update]
  have hgraftContains :
      ∀ {mutable : Bool} {u : LVal},
        PartialTyContains updatedTy (.borrow mutable u) →
        PartialTyContains (.ty rhsTy) (.borrow mutable u) := by
    intro mutable u hcontains
    exact PathSelect.update_borrows hselectFinal hupdate hcontains
  intro location hreach
  exact reachesWhenInitialized_chain_leaf_ne_of_stored_outside_chain
    hsafe hvalidStore hheap hborrowSafe htySafe hnotWriteNested hne
    hbLook hgraftContains hguardFinal hleafChain hyOutside henvY
    hstoreY hreach

/-- Stored source slots reduce to source-entry read exclusions.  Owner reaches
are ruled out by store uniqueness; initialized borrow reaches are exactly the
contained source annotations whose targets must not read the selected leaf. -/
theorem reachesWhenInitialized_select_final_stored_ne_leaf_of_source_entries
    {store : ProgramStore} {env nested : Env}
    {finalLhs : LVal} {otherEnvSlot : EnvSlot} {oldValue : PartialValue}
    {y : Name} {leafLoc : Location} {k : Nat}
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hyFinal : y ≠ LVal.base finalLhs)
    (henvY : env.slotAt y = some otherEnvSlot)
    (hstoreY : store.slotAt (VariableProjection y) =
      some { value := oldValue, lifetime := otherEnvSlot.lifetime })
    (hentryReads :
      ∀ {mutable : Bool} {target : LVal},
        env ⊢ y ↝ (.borrow mutable target) →
        ∀ {location : Location},
          RuntimeFrame.LocReads store target location →
          location ≠ leafLoc) :
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized nested store oldValue
        otherEnvSlot.ty location →
      location ≠ leafLoc := by
  have hstorageNeRoot :
      VariableProjection y ≠ VariableProjection (LVal.base finalLhs) := by
    intro hEq
    exact hyFinal (by simpa [VariableProjection] using hEq)
  have hownerNoReach :
      ¬ RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty leafLoc :=
    ownerReaches_stored_ne_chain_leaf hvalidStore
      (var_not_owned hheap) (var_not_owned hheap) hstorageNeRoot
      hleafChain hstoreY
  intro location hreach
  exact reachesWhenInitialized_ne_of_borrow_targets_locReads_ne
    (env := nested) (store := store) (leafLoc := leafLoc)
    (value := oldValue) (partialTy := otherEnvSlot.ty)
    (by
      intro mutable target hcontains location hreads
      exact hentryReads ⟨otherEnvSlot, henvY, hcontains⟩ hreads)
    hownerNoReach hreach

/-- Stored source slots reduce to read exclusions for live source entries.
This is the form needed by selected-final assignment: a borrow annotation only
has to be excluded when the target remains initialized in the final
environment and can therefore be reached at runtime. -/
theorem reachesWhenInitialized_select_final_stored_ne_leaf_of_live_source_entries
    {store : ProgramStore} {env nested : Env}
    {finalLhs : LVal} {otherEnvSlot : EnvSlot} {oldValue : PartialValue}
    {y : Name} {leafLoc : Location} {k : Nat}
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hyFinal : y ≠ LVal.base finalLhs)
    (henvY : env.slotAt y = some otherEnvSlot)
    (hstoreY : store.slotAt (VariableProjection y) =
      some { value := oldValue, lifetime := otherEnvSlot.lifetime })
    (hentryReads :
      ∀ {mutable : Bool} {target : LVal},
        env ⊢ y ↝ (.borrow mutable target) →
        TargetInitialized nested target →
        ∀ {location : Location},
          RuntimeFrame.LocReads store target location →
          location ≠ leafLoc) :
    ∀ {location : Location},
      RuntimeFrame.ReachesWhenInitialized nested store oldValue
        otherEnvSlot.ty location →
      location ≠ leafLoc := by
  have hstorageNeRoot :
      VariableProjection y ≠ VariableProjection (LVal.base finalLhs) := by
    intro hEq
    exact hyFinal (by simpa [VariableProjection] using hEq)
  have hownerNoReach :
      ¬ RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty leafLoc :=
    ownerReaches_stored_ne_chain_leaf hvalidStore
      (var_not_owned hheap) (var_not_owned hheap) hstorageNeRoot
      hleafChain hstoreY
  intro location hreach
  exact reachesWhenInitialized_ne_of_live_borrow_targets_locReads_ne
    (env := nested) (store := store) (leafLoc := leafLoc)
    (value := oldValue) (partialTy := otherEnvSlot.ty)
    (by
      intro mutable target hcontains hinitialized location hreads
      exact hentryReads ⟨otherEnvSlot, henvY, hcontains⟩
        hinitialized hreads)
    hownerNoReach hreach

/-- A source borrow annotation's target remains initialized in the selected
final environment.  The original write transports target initialization to
`env₃`; the selected-final package supplies a pointwise-equal nested result. -/
theorem targetInitialized_select_final_of_source_entry
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop target : LVal} {rhsTy : Ty} {oldTy : PartialTy}
    {targetLifetime : Lifetime} {mutable : Bool} {y : Name}
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwriteTop : EnvWrite env lhsTop rhsTy env₃)
    (hlvTop : LValTyping env lhsTop oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hentry : env ⊢ y ↝ (.borrow mutable target)) :
    TargetInitialized nested target := by
  rcases hentry with ⟨slotY, hslotY, hcontainsY⟩
  rcases hcbwf y slotY mutable target hslotY
      (⟨slotY, hslotY, hcontainsY⟩ :
        env ⊢ y ↝ (.borrow mutable target)) with
    ⟨targetTy, targetLifetime', htargetTyping, _hle, _hbase⟩
  rcases TargetInitialized.envWrite hcbwf hborrowSafe htySafe hwriteTop
      hlvTop hshape hwellTy hnotWriteTop
      (⟨targetTy, targetLifetime', htargetTyping⟩ :
        TargetInitialized env target) with
    ⟨targetTy₃, targetLifetime₃, htargetTyping₃⟩
  exact ⟨targetTy₃, targetLifetime₃,
    LValTyping.transport_of_pointwise (fun z => (hpoint z).symm)
      htargetTyping₃⟩

/-- If a source borrow annotation survives to the selected-final environment and
its target reads the selected leaf, then the target root is on the original
write chain. -/
theorem source_entry_target_guard_of_select_final_locReads
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop finalLhs target : LVal} {rhsTy : Ty}
    {oldTy leafTy : PartialTy} {targetLifetime : Lifetime}
    {rootSlot : EnvSlot} {leafLoc : Location} {k : Nat}
    {mutable : Bool} {y : Name}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwriteTop : EnvWrite env lhsTop rhsTy env₃)
    (hlvTop : LValTyping env lhsTop oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hentry : env ⊢ y ↝ (.borrow mutable target)) :
    RuntimeFrame.LocReads store target leafLoc →
      ChainGuard env (LVal.base lhsTop) (LVal.base target) := by
  intro hreads
  rcases EnvWrite.pathSelect_update_eq henvFinal hselectFinal hwriteFinal with
    ⟨updatedTy, hupdate, hnested⟩
  have hnotWriteNested :
      ¬ WriteProhibited nested lhsTop :=
    not_writeProhibited_of_pointwise
      (env := env₃) (result := nested) (fun z => (hpoint z).symm)
      hnotWriteTop
  have hne : ∀ z, z ≠ LVal.base finalLhs →
      nested.slotAt z = env.slotAt z := by
    intro z hz
    rw [hnested]
    simp [Env.update, hz]
  have hbLook :
      nested.slotAt (LVal.base finalLhs) =
        some { rootSlot with ty := updatedTy } := by
    rw [hnested]
    simp [Env.update]
  have hgraftContains :
      ∀ {mutable : Bool} {u : LVal},
        PartialTyContains updatedTy (.borrow mutable u) →
        PartialTyContains (.ty rhsTy) (.borrow mutable u) := by
    intro mutable u hcontains
    exact PathSelect.update_borrows hselectFinal hupdate hcontains
  rcases targetInitialized_select_final_of_source_entry (store := store)
      hcbwf hborrowSafe htySafe hwriteTop hlvTop hshape hwellTy
      hnotWriteTop hpoint hentry with
    ⟨targetTy, targetLifetime', htargetTyping⟩
  exact locReads_chain_protected_base_on_chain
    hsafe hvalidStore hheap hborrowSafe htySafe hnotWriteNested hne hbLook
    hgraftContains hguardFinal (protectedByBase_of_ownsChain hleafChain)
    htargetTyping hreads

/-- Source entries whose target is rooted at the selected final base cannot
read the selected leaf.  The root case would survive and write-prohibit the
top write; the hop-selected case is pinned to the final incoming edge by
borrow safety and reduces to the final lvalue's own read exclusion. -/
theorem source_entry_select_final_base_locReads_ne
    {env env₃ nested : Env} {store : ProgramStore}
    {lhsTop finalLhs lv target : LVal} {rhsTy : Ty}
    {rootSlot : EnvSlot} {leafTy : PartialTy}
    {y : Name} {mutable : Bool} {leafLoc : Location}
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hlast :
      finalLhs = lv ∨
        ∃ (holder : Name) (path' : Path) (target' : LVal),
          env ⊢ holder ↝ (.borrow true target') ∧
          finalLhs = prependPath path' target')
    (hlvBase : LVal.base lv = LVal.base lhsTop)
    (hyFinal : y ≠ LVal.base finalLhs)
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (hentryBase : LVal.base target = LVal.base finalLhs)
    (hfinalReads : ∀ mid,
      RuntimeFrame.LocReads store finalLhs mid → mid ≠ leafLoc) :
    ∀ {location : Location},
      RuntimeFrame.LocReads store target location →
      location ≠ leafLoc := by
  rcases EnvWrite.pathSelect_update_eq henvFinal hselectFinal hwriteFinal with
    ⟨updatedTy, hupdate, hnested⟩
  have hnotWriteNested :
      ¬ WriteProhibited nested lhsTop :=
    not_writeProhibited_of_pointwise
      (env := env₃) (result := nested) (fun z => (hpoint z).symm)
      hnotWriteTop
  have hne : ∀ z, z ≠ LVal.base finalLhs →
      nested.slotAt z = env.slotAt z := by
    intro z hz
    rw [hnested]
    simp [Env.update, hz]
  have hbLook :
      nested.slotAt (LVal.base finalLhs) =
        some { rootSlot with ty := updatedTy } := by
    rw [hnested]
    simp [Env.update]
  have hgraftContains :
      ∀ {mutable : Bool} {u : LVal},
        PartialTyContains updatedTy (.borrow mutable u) →
        PartialTyContains (.ty rhsTy) (.borrow mutable u) := by
    intro mutable u hcontains
    exact PathSelect.update_borrows hselectFinal hupdate hcontains
  exact source_entry_final_base_locReads_ne hborrowSafe htySafe
    hnotWriteNested hne hbLook hgraftContains hguardFinal hlast hlvBase
    hyFinal hentry hentryBase hfinalReads

/-- If a source entry's target is outside the original write chain, it cannot
read the selected final leaf. -/
theorem source_entry_select_final_outside_locReads_ne
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop finalLhs target : LVal} {rhsTy : Ty}
    {oldTy leafTy : PartialTy} {targetLifetime : Lifetime}
    {rootSlot : EnvSlot} {leafLoc : Location} {k : Nat}
    {mutable : Bool} {y : Name}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwriteTop : EnvWrite env lhsTop rhsTy env₃)
    (hlvTop : LValTyping env lhsTop oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (htargetOutside :
      ¬ ChainGuard env (LVal.base lhsTop) (LVal.base target)) :
    ∀ {location : Location},
      RuntimeFrame.LocReads store target location →
      location ≠ leafLoc := by
  intro location hreads hlocation
  exact htargetOutside
    (source_entry_target_guard_of_select_final_locReads
      hsafe hvalidStore hheap hcbwf hborrowSafe htySafe hwriteTop hlvTop
      hshape hwellTy hnotWriteTop henvFinal hselectFinal hwriteFinal
      hpoint hguardFinal hleafChain hentry
      (by simpa [hlocation] using hreads))

/-- A source-entry target that is the root of a remaining selected-hop suffix
cannot read the selected leaf. -/
theorem source_entry_select_final_hops_suffix_locReads_ne
    {env env₃ nested : Env} {store : ProgramStore}
    {lhsTop finalLhs target : LVal} {rhsTy : Ty}
    {rootSlot : EnvSlot} {leafTy : PartialTy}
    {leafLoc : Location} {k : Nat}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hcbwf : ContainedBorrowsWellFormed env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hlen : k = (LVal.path finalLhs).length)
    (hhopsTail : ∃ path',
      HopsTo env env₃ (prependPath path' target) finalLhs) :
    ∀ {location : Location},
      RuntimeFrame.LocReads store target location →
      location ≠ leafLoc := by
  rcases EnvWrite.pathSelect_update_eq henvFinal hselectFinal hwriteFinal with
    ⟨updatedTy, hupdate, hnested⟩
  have hnotWriteNested :
      ¬ WriteProhibited nested lhsTop :=
    not_writeProhibited_of_pointwise
      (env := env₃) (result := nested) (fun z => (hpoint z).symm)
      hnotWriteTop
  have hne : ∀ z, z ≠ LVal.base finalLhs →
      nested.slotAt z = env.slotAt z := by
    intro z hz
    rw [hnested]
    simp [Env.update, hz]
  have hbLook :
      nested.slotAt (LVal.base finalLhs) =
        some { rootSlot with ty := updatedTy } := by
    rw [hnested]
    simp [Env.update]
  have hgraftContains :
      ∀ {mutable : Bool} {u : LVal},
        PartialTyContains updatedTy (.borrow mutable u) →
        PartialTyContains (.ty rhsTy) (.borrow mutable u) := by
    intro mutable u hcontains
    exact PathSelect.update_borrows hselectFinal hupdate hcontains
  have hlinks :
      ∀ {s₀ target : LVal} {slotH : EnvSlot} {lf : Lifetime},
        env.slotAt (LVal.base s₀) = some slotH →
        PathSelect (LVal.path s₀) slotH.ty (.ty (.borrow true target)) →
        LValTyping env s₀ (.ty (.borrow true target)) lf →
        env ⊢ (LVal.base s₀) ↝ (.borrow true target) →
        env₃.slotAt (LVal.base s₀) = env.slotAt (LVal.base s₀) →
        (∀ mid, RuntimeFrame.LocReads store s₀ mid → mid ≠ leafLoc) ∧
          store.loc s₀ ≠ some leafLoc :=
    clean_hop_link_of_guarded_leaf hsafe hvalidStore hheap htySafe
      hnotWriteNested hpoint hbLook hgraftContains hguardFinal henvFinal
      hselectFinal hleafChain hlen
  have hfinalReads :
      ∀ mid, RuntimeFrame.LocReads store finalLhs mid → mid ≠ leafLoc := by
    intro mid hreads
    exact locReads_ne_of_ownsChain_length hvalidStore hheap hleafChain
      hlen hreads
  rcases hhopsTail with ⟨path', hhops⟩
  exact HopsTo.tail_target_locReads_ne hsafe hcbwf hhops hlinks
    hfinalReads

/-- Prefix-chain source entries are exactly selected-hop suffix roots, unless
they are also in the final tail.  The `hnotTail` premise selects the genuine
prefix case when a degenerate source cycle gives both orderings. -/
theorem source_entry_select_final_prefix_locReads_ne
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop finalLhs target : LVal} {rhsTy : Ty}
    {oldTy leafTy : PartialTy} {targetLifetime : Lifetime}
    {rootSlot : EnvSlot} {leafLoc : Location} {k : Nat}
    {mutable : Bool} {y : Name}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwriteTop : EnvWrite env lhsTop rhsTy env₃)
    (hlvTop : LValTyping env lhsTop oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hlen : k = (LVal.path finalLhs).length)
    (hhops : HopsTo env env₃ lhsTop finalLhs)
    (hguardY : ChainGuard env (LVal.base lhsTop) y)
    (hyFinal : ChainGuard env y (LVal.base finalLhs))
    (hyNeFinal : y ≠ LVal.base finalLhs)
    (hnotTail : ¬ ChainGuard env (LVal.base finalLhs) y)
    (hentry : env ⊢ y ↝ (.borrow mutable target)) :
    ∀ {location : Location},
      RuntimeFrame.LocReads store target location →
      location ≠ leafLoc := by
  have hsuffix :
      ∃ path', HopsTo env env₃ (prependPath path' target) finalLhs :=
    HopsTo.suffix_of_guard_prefix hhops hguardY hyFinal hyNeFinal hentry
      (by
        intro hfinalY _hyFinal
        exact hnotTail hfinalY)
  intro location hreads
  exact source_entry_select_final_hops_suffix_locReads_ne
    hsafe hvalidStore hheap hcbwf htySafe hnotWriteTop henvFinal
    hselectFinal hwriteFinal hpoint hguardFinal hleafChain hlen hsuffix
    hreads

theorem source_entry_select_final_live_of_not_writeProhibited_final_locReads_ne
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop lv finalLhs target : LVal} {rhsTy : Ty}
    {leafTy : PartialTy} {rootSlot : EnvSlot}
    {leafLoc : Location} {k : Nat} {mutable : Bool} {y : Name}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (hnotWriteFinal : ¬ WriteProhibited env finalLhs)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hlen : k = (LVal.path finalLhs).length)
    (hlast :
      finalLhs = lv ∨
        ∃ (holder : Name) (path' : Path) (target' : LVal),
          env ⊢ holder ↝ (.borrow true target') ∧
          finalLhs = prependPath path' target')
    (hlvBase : LVal.base lv = LVal.base lhsTop)
    (hyFinal : y ≠ LVal.base finalLhs)
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (_hinitialized : TargetInitialized nested target) :
    ∀ {location : Location},
      RuntimeFrame.LocReads store target location →
      location ≠ leafLoc := by
  rcases hentry with ⟨entrySlot, hentrySlot, hentryContains⟩
  have hentry' : env ⊢ y ↝ (.borrow mutable target) :=
    ⟨entrySlot, hentrySlot, hentryContains⟩
  rcases hcbwf y entrySlot mutable target hentrySlot hentry' with
    ⟨targetTy, targetLifetime, htargetTyping, _hle, _hbase⟩
  intro location hreads hlocation
  rcases locReads_chain_leaf_conflict_or_writeProhibited_whenInitialized
      hsafe hvalidStore hheap hleafChain htargetTyping
      (by simpa [hlocation] using hreads) with
    htargetFinal | hwriteFinal
  · have hfinalReads :
        ∀ mid, RuntimeFrame.LocReads store finalLhs mid → mid ≠ leafLoc := by
      intro mid hread
      exact locReads_ne_of_ownsChain_length hvalidStore hheap hleafChain
        hlen hread
    exact source_entry_select_final_base_locReads_ne hborrowSafe htySafe
      hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint hguardFinal
      hlast hlvBase hyFinal hentry' htargetFinal hfinalReads hreads
      hlocation
  · exact hnotWriteFinal hwriteFinal

/-- Post-update version of the selected-final write-prohibition bridge.

If the selected final lvalue is not write-prohibited in the pure selected
write result, then any live source entry rooted away from the selected final
slot cannot read the selected runtime leaf.  The proof runs the
post-update conflict lemma on the initialized target typing in `nested`; a
direct conflict reduces to the already-pinned "target is the final base" case,
and the write-prohibited branch contradicts the premise. -/
theorem source_entry_select_final_live_of_not_writeProhibited_nested_final_locReads_ne
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop lv finalLhs target : LVal} {rhsTy : Ty}
    {leafTy : PartialTy} {rootSlot : EnvSlot}
    {leafLoc : Location} {k : Nat} {mutable : Bool} {y : Name}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (hnotWriteFinal : ¬ WriteProhibited nested finalLhs)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hlen : k = (LVal.path finalLhs).length)
    (hlast :
      finalLhs = lv ∨
        ∃ (holder : Name) (path' : Path) (target' : LVal),
          env ⊢ holder ↝ (.borrow true target') ∧
          finalLhs = prependPath path' target')
    (hlvBase : LVal.base lv = LVal.base lhsTop)
    (hyFinal : y ≠ LVal.base finalLhs)
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (hinitialized : TargetInitialized nested target) :
    ∀ {location : Location},
      RuntimeFrame.LocReads store target location →
      location ≠ leafLoc := by
  rcases EnvWrite.pathSelect_update_eq henvFinal hselectFinal
      hwriteFinal with
    ⟨updatedTy, _hupdate, hnested⟩
  rcases hinitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
  intro location hreads hlocation
  rcases
      locReads_chain_leaf_conflict_or_writeProhibited_update_var_whenInitialized
        hsafe hvalidStore hheap hnested hnotWriteFinal hleafChain
        htargetTyping (by simpa [hlocation] using hreads) with
    hconflict | hwrite
  · have hentryBase : LVal.base target = LVal.base finalLhs := by
      simpa [PathConflicts] using hconflict
    have hfinalReads :
        ∀ mid, RuntimeFrame.LocReads store finalLhs mid → mid ≠ leafLoc := by
      intro mid hread
      exact locReads_ne_of_ownsChain_length hvalidStore hheap hleafChain
        hlen hread
    exact source_entry_select_final_base_locReads_ne hborrowSafe htySafe
      hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint hguardFinal
      hlast hlvBase hyFinal hentry hentryBase hfinalReads hreads
      hlocation
  · exact hnotWriteFinal hwrite

/-- Live source entries that are not in the final tail cannot read the selected
runtime leaf.  This consolidates the target-at-final and selected-prefix cases
used by the assignment wrapper; the remaining open case is exactly a holder in
the final tail. -/
theorem source_entry_select_final_live_not_tail_locReads_ne
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop lv finalLhs target : LVal} {rhsTy : Ty}
    {oldTy leafTy : PartialTy} {targetLifetime : Lifetime}
    {rootSlot : EnvSlot} {leafLoc : Location} {k : Nat}
    {mutable : Bool} {y : Name}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwriteTop : EnvWrite env lhsTop rhsTy env₃)
    (hlvTop : LValTyping env lhsTop oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hlen : k = (LVal.path finalLhs).length)
    (hlast :
      finalLhs = lv ∨
        ∃ (holder : Name) (path' : Path) (target' : LVal),
          env ⊢ holder ↝ (.borrow true target') ∧
          finalLhs = prependPath path' target')
    (hhops : HopsTo env env₃ lhsTop finalLhs)
    (hlvBase : LVal.base lv = LVal.base lhsTop)
    (hyFinal : y ≠ LVal.base finalLhs)
    (hnotTailY : ¬ ChainGuard env (LVal.base finalLhs) y)
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (_hinitialized : TargetInitialized nested target) :
    ∀ {location : Location},
      RuntimeFrame.LocReads store target location →
      location ≠ leafLoc := by
  intro location hreads hlocation
  have htargetGuard :
      ChainGuard env (LVal.base lhsTop) (LVal.base target) :=
    source_entry_target_guard_of_select_final_locReads
      hsafe hvalidStore hheap hcbwf hborrowSafe htySafe hwriteTop hlvTop
      hshape hwellTy hnotWriteTop henvFinal hselectFinal hwriteFinal
      hpoint hguardFinal hleafChain hentry
      (by simpa [hlocation] using hreads)
  by_cases htargetFinal : LVal.base target = LVal.base finalLhs
  · have hfinalReads :
        ∀ mid, RuntimeFrame.LocReads store finalLhs mid → mid ≠ leafLoc := by
      intro mid hread
      exact locReads_ne_of_ownsChain_length hvalidStore hheap hleafChain
        hlen hread
    exact source_entry_select_final_base_locReads_ne hborrowSafe htySafe
      hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint hguardFinal
      hlast hlvBase hyFinal hentry htargetFinal hfinalReads hreads hlocation
  have hguardY :
      ChainGuard env (LVal.base lhsTop) y := by
    rcases EnvWrite.pathSelect_update_eq henvFinal hselectFinal
        hwriteFinal with
      ⟨updatedTy, hupdate, hnested⟩
    have hnotWriteNested :
        ¬ WriteProhibited nested lhsTop :=
      not_writeProhibited_of_pointwise
        (env := env₃) (result := nested) (fun z => (hpoint z).symm)
        hnotWriteTop
    have hne : ∀ z, z ≠ LVal.base finalLhs →
        nested.slotAt z = env.slotAt z := by
      intro z hz
      rw [hnested]
      simp [Env.update, hz]
    have hbLook :
        nested.slotAt (LVal.base finalLhs) =
          some { rootSlot with ty := updatedTy } := by
      rw [hnested]
      simp [Env.update]
    have hgraftContains :
        ∀ {mutable : Bool} {u : LVal},
          PartialTyContains updatedTy (.borrow mutable u) →
          PartialTyContains (.ty rhsTy) (.borrow mutable u) := by
      intro mutable u hcontains
      exact PathSelect.update_borrows hselectFinal hupdate hcontains
    exact chain_entry_source hborrowSafe htySafe hnotWriteNested hne
      hbLook hgraftContains hguardFinal hentry htargetGuard
  rcases chainGuard_linear_ne hguardFinal hguardY hyFinal with htail | hprefix
  · exact False.elim (hnotTailY htail)
  · exact source_entry_select_final_prefix_locReads_ne
      hsafe hvalidStore hheap hcbwf hborrowSafe htySafe hwriteTop
      hlvTop hshape hwellTy hnotWriteTop henvFinal hselectFinal
      hwriteFinal hpoint hguardFinal hleafChain hlen hhops hguardY
      hprefix hyFinal hnotTailY hentry hreads hlocation

/-- Tail-factored version of the selected-final read exclusion.

All non-tail entries are discharged by the hop-spine lemmas above.  The caller
supplies exactly the remaining on-chain tail frame: live source entries held
strictly below the selected final base cannot read the selected runtime leaf. -/
theorem source_entry_select_final_live_of_tail_frame_locReads_ne
    {store : ProgramStore} {env env₃ nested : Env}
    {lhsTop lv finalLhs target : LVal} {rhsTy : Ty}
    {oldTy leafTy : PartialTy} {targetLifetime : Lifetime}
    {rootSlot : EnvSlot} {leafLoc : Location} {k : Nat}
    {mutable : Bool} {y : Name}
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hcbwf : ContainedBorrowsWellFormed env)
    (hborrowSafe : BorrowSafeEnv env)
    (htySafe : TyBorrowSafeAgainstEnv env rhsTy)
    (hwriteTop : EnvWrite env lhsTop rhsTy env₃)
    (hlvTop : LValTyping env lhsTop oldTy targetLifetime)
    (hshape : ShapeCompatible env oldTy (.ty rhsTy))
    (hwellTy : WellFormedTy env rhsTy targetLifetime)
    (hnotWriteTop : ¬ WriteProhibited env₃ lhsTop)
    (henvFinal : env.slotAt (LVal.base finalLhs) = some rootSlot)
    (hselectFinal : PathSelect (LVal.path finalLhs) rootSlot.ty leafTy)
    (hwriteFinal : EnvWrite env finalLhs rhsTy nested)
    (hpoint : ∀ z, env₃.slotAt z = nested.slotAt z)
    (hguardFinal : ChainGuard env (LVal.base lhsTop)
      (LVal.base finalLhs))
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hlen : k = (LVal.path finalLhs).length)
    (hlast :
      finalLhs = lv ∨
        ∃ (holder : Name) (path' : Path) (target' : LVal),
          env ⊢ holder ↝ (.borrow true target') ∧
          finalLhs = prependPath path' target')
    (hhops : HopsTo env env₃ lhsTop finalLhs)
    (hlvBase : LVal.base lv = LVal.base lhsTop)
    (hyFinal : y ≠ LVal.base finalLhs)
    (htailFrame :
      ∀ {mutable : Bool} {target : LVal} {y : Name},
        y ≠ LVal.base finalLhs →
        ChainGuard env (LVal.base finalLhs) y →
        env ⊢ y ↝ (.borrow mutable target) →
        TargetInitialized nested target →
        ∀ {location : Location},
          RuntimeFrame.LocReads store target location →
          location ≠ leafLoc)
    (hentry : env ⊢ y ↝ (.borrow mutable target))
    (hinitialized : TargetInitialized nested target) :
    ∀ {location : Location},
      RuntimeFrame.LocReads store target location →
      location ≠ leafLoc := by
  by_cases htailY : ChainGuard env (LVal.base finalLhs) y
  · exact htailFrame hyFinal htailY hentry hinitialized
  · exact source_entry_select_final_live_not_tail_locReads_ne
      hsafe hvalidStore hheap hcbwf hborrowSafe htySafe hwriteTop
      hlvTop hshape hwellTy hnotWriteTop henvFinal hselectFinal
      hwriteFinal hpoint hguardFinal hleafChain hlen hlast hhops
      hlvBase hyFinal htailY hentry hinitialized

/-- Paper-linearized tail frame.

If a live borrow holder is strictly below the selected-final base in the
borrow-chain guard, then a read of the selected-final runtime leaf would create a
rank cycle: the leaf protects the target read, the target is below its holder,
and the holder is below the selected-final base. -/
theorem source_entry_select_final_tail_linearized_locReads_ne
    {store : ProgramStore} {env : Env}
    {finalLhs target : LVal} {leafLoc : Location} {k : Nat}
    {mutable : Bool} {y : Name} {φ : Name → Nat}
    (hφ : LinearizedBy φ env)
    (hsafe : SafeAbstraction store env)
    (hvalidStore : ValidStore store)
    (hheap : StoreOwnerTargetsHeap store)
    (hcbwf : ContainedBorrowsWellFormed env)
    (hleafChain : OwnsChain store
      (VariableProjection (LVal.base finalLhs)) k leafLoc)
    (hyFinal : y ≠ LVal.base finalLhs)
    (htailY : ChainGuard env (LVal.base finalLhs) y)
    (hentry : env ⊢ y ↝ (.borrow mutable target)) :
    ∀ {location : Location},
      RuntimeFrame.LocReads store target location →
      location ≠ leafLoc := by
  rcases hentry with ⟨entrySlot, hentrySlot, hentryContains⟩
  have hentry' : env ⊢ y ↝ (.borrow mutable target) :=
    ⟨entrySlot, hentrySlot, hentryContains⟩
  rcases hcbwf y entrySlot mutable target hentrySlot hentry' with
    ⟨targetTy, targetLifetime, htargetTyping, _hle, _hbase⟩
  intro location hreads hlocation
  have hfinalLeTarget :
      φ (LVal.base finalLhs) ≤ φ (LVal.base target) :=
    locReads_protected_rank_le_base_whenInitialized
      hφ hsafe hvalidStore hheap htargetTyping
      (by simpa [hlocation] using hreads)
      (protectedByBase_of_ownsChain hleafChain)
  have htargetLtY :
      φ (LVal.base target) < φ y :=
    LinearizedBy.contains_rank_lt hφ hentry'
  have hyLtFinal :
      φ y < φ (LVal.base finalLhs) :=
    chainGuard_rank_lt_of_ne hφ htailY hyFinal
  have hfinalLtY : φ (LVal.base finalLhs) < φ y :=
    lt_of_le_of_lt hfinalLeTarget htargetLtY
  exact Nat.lt_irrefl _ (lt_trans hfinalLtY hyLtFinal)

/-- Selected-final assignment preservation.

`EnvWrite.select_final` reduces the original assignment to this situation.  The
helper discharges the source-entry read exclusions for entries outside the
final tail, entries targeting the final base, and entries in the final tail.
This legacy helper keeps the tail case as an explicit local side condition:
the selected final node itself must not be write-prohibited in the source
environment.  The main assignment typing rule does not require this condition;
borrow-authorized writes through mutable references are accepted. -/
theorem preservation_assign_selected_final_step_runtime
    {store store' : ProgramStore} {env env₃ nested : Env}
    {lifetime targetLifetime : Lifetime}
    {lhsTop lv finalLhs : LVal} {oldTy leafTy : PartialTy}
    {rootSlot : EnvSlot} {rhsTy : Ty}
    {value finalValue : Value} {leafLoc : Location} {k : Nat} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign lv (.val value)) →
    EnvWrite env lhsTop rhsTy env₃ →
    LValTyping env lhsTop oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    ¬ WriteProhibited env finalLhs →
    ¬ WriteProhibited env₃ lhsTop →
    env.slotAt (LVal.base finalLhs) = some rootSlot →
    PathSelect (LVal.path finalLhs) rootSlot.ty leafTy →
    EnvWrite env finalLhs rhsTy nested →
    (∀ y, env₃.slotAt y = nested.slotAt y) →
    LValTyping env finalLhs oldTy targetLifetime →
    store.loc lv = store.loc finalLhs →
    ChainGuard env (LVal.base lhsTop) (LVal.base finalLhs) →
    OwnsChain store (VariableProjection (LVal.base finalLhs)) k leafLoc →
    k = (LVal.path finalLhs).length →
    store.loc finalLhs = some leafLoc →
    (finalLhs = lhsTop ∨
      ∃ (holder : Name) (path' : Path) (target' : LVal),
        env ⊢ holder ↝ (.borrow true target') ∧
        finalLhs = prependPath path' target') →
    HopsTo env env₃ lhsTop finalLhs →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign lv (.val value)) store' (.val finalValue) →
    FullTerminalStateSafe store' finalValue nested .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hwriteTop hlvTop
    hshape hwellTy hnotWriteFinal hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint
    htypingFinal hlocFinal hguardFinal hleafChain hlen hleafLoc
    hlast hhops hvalidValue hstep
  have hvalidStore : ValidStore store :=
    ValidRuntimeState.validStore hvalidRuntime
  have hheap : StoreOwnerTargetsHeap store :=
    ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
  have hwellEnv₃ : WellFormedEnv env₃ lifetime :=
    WellFormedEnv.envWrite hwell hborrowSafe htySafe hwriteTop hlvTop
      hshape hwellTy hnotWriteTop
  have hwellNested : WellFormedEnv nested lifetime :=
    WellFormedEnv.transport_of_pointwise
      (env := env₃) (result := nested) (fun y => (hpoint y).symm)
      hwellEnv₃
  have hstepFinal :
      Step store lifetime (.assign finalLhs (.val value)) store'
        (.val finalValue) :=
    assign_step_of_loc_eq hlocFinal hstep
  have hvalidRuntimeFinal :
      ValidRuntimeState store (.assign finalLhs (.val value)) :=
    validRuntimeState_assign_lhs_of_value hvalidRuntime
  have hvalidValueNested :
      ValidPartialValueWhenInitialized nested store (.value value)
        (.ty rhsTy) :=
    validPartialValueWhenInitialized_select_final_rhs
      hwell.1 hborrowSafe htySafe hwriteTop hlvTop hshape hwellTy
      hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint hvalidValue
  have hotherValidNested :
      ∀ y otherEnvSlot oldValue,
        y ≠ LVal.base finalLhs →
        env.slotAt y = some otherEnvSlot →
        store.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
        ValidPartialValueWhenInitialized nested store oldValue
          otherEnvSlot.ty := by
    intro y otherEnvSlot oldValue hyFinal henvY hstoreY
    rcases hsafe.2 y otherEnvSlot henvY with
      ⟨safeValue, hsafeStoreY, hvalidOld⟩
    have hvalueEq : safeValue = oldValue := by
      have hslotEq :=
        Option.some.inj (hsafeStoreY.symm.trans hstoreY)
      exact congrArg StoreSlot.value hslotEq
    subst hvalueEq
    exact validPartialValueWhenInitialized_select_final_unchanged_slot
      hwell.1 hborrowSafe htySafe hwriteTop hlvTop hshape hwellTy
      hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint hyFinal
      henvY hvalidOld
  have hvalueHeap : ValueOwnerTargetsHeap value :=
    TermOwnerTargetsHeap.value
      (termOwnerTargetsHeap_assign_inner
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
  have hvalueUnowned :
      ∀ owned, owned ∈ valueOwningLocations value →
        ¬ ProgramStore.Owns store owned := by
    intro owned hmem
    exact
      (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
        (by
          simpa [termOwningLocations, termValues,
            partialValueOwningLocations] using hmem))
  have hvalueFrame :
      ∀ location,
        RuntimeFrame.ReachesWhenInitialized nested store (.value value)
          (.ty rhsTy) location →
        location ≠ leafLoc := by
    intro location hreach
    exact reachesWhenInitialized_select_final_rhs_ne_leaf
      hsafe hvalidStore hheap hborrowSafe htySafe hwriteTop hlvTop hshape
      hwellTy hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint
      hguardFinal hleafChain hvalueHeap hvalueUnowned hreach
  have hotherFrame :
      ∀ y otherEnvSlot oldValue,
        y ≠ LVal.base finalLhs →
        env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.ReachesWhenInitialized nested store oldValue
          otherEnvSlot.ty location →
      location ≠ leafLoc := by
    intro y otherEnvSlot oldValue hyFinal henvY hstoreY location hreach
    exact reachesWhenInitialized_select_final_stored_ne_leaf_of_live_source_entries
      hvalidStore hheap hleafChain hyFinal henvY hstoreY
      (by
        intro mutable target hentry hinitialized location hreads
        exact
          source_entry_select_final_live_of_not_writeProhibited_final_locReads_ne
            hsafe hvalidStore hheap hwell.1 hborrowSafe htySafe
            hnotWriteTop hnotWriteFinal henvFinal hselectFinal hwriteFinal
            hpoint hguardFinal hleafChain hlen hlast rfl hyFinal
            hentry hinitialized hreads)
      hreach
  have hterminal : TerminalStateSafe store' finalValue nested .unit :=
    preservation_assign_pathSelect_step_runtime_whenInitialized_of_frames
      hwell hborrowSafe htySafe hsafe hvalidRuntimeFinal htypingFinal hshape
      hwellTy hwriteFinal hwellNested henvFinal hselectFinal hleafLoc hvalidValue
      hstepFinal hvalidValueNested hotherValidNested hvalueFrame hotherFrame
  exact TerminalStateSafe.full_of_wellFormed hterminal hwellNested
    WellFormedTy.unit

/-- Selected-final assignment preservation with the remaining on-chain tail
frame exposed as the only local side condition.

This is the version needed by the general borrow-hop assignment wrapper:
`EnvWrite.select_final` supplies the selected pure write and the hop spine; the
caller still has to prove that live source entries strictly below the selected
final base do not read the selected runtime leaf. -/
theorem preservation_assign_selected_final_step_runtime_of_tail_frame
    {store store' : ProgramStore} {env env₃ nested : Env}
    {lifetime targetLifetime : Lifetime}
    {lhsTop lv finalLhs : LVal} {oldTy leafTy : PartialTy}
    {rootSlot : EnvSlot} {rhsTy : Ty}
    {value finalValue : Value} {leafLoc : Location} {k : Nat} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign lv (.val value)) →
    EnvWrite env lhsTop rhsTy env₃ →
    LValTyping env lhsTop oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    ¬ WriteProhibited env₃ lhsTop →
    env.slotAt (LVal.base finalLhs) = some rootSlot →
    PathSelect (LVal.path finalLhs) rootSlot.ty leafTy →
    EnvWrite env finalLhs rhsTy nested →
    (∀ y, env₃.slotAt y = nested.slotAt y) →
    LValTyping env finalLhs oldTy targetLifetime →
    store.loc lv = store.loc finalLhs →
    ChainGuard env (LVal.base lhsTop) (LVal.base finalLhs) →
    OwnsChain store (VariableProjection (LVal.base finalLhs)) k leafLoc →
    k = (LVal.path finalLhs).length →
    store.loc finalLhs = some leafLoc →
    (finalLhs = lhsTop ∨
      ∃ (holder : Name) (path' : Path) (target' : LVal),
        env ⊢ holder ↝ (.borrow true target') ∧
        finalLhs = prependPath path' target') →
    HopsTo env env₃ lhsTop finalLhs →
    (∀ {mutable : Bool} {target : LVal} {y : Name},
      y ≠ LVal.base finalLhs →
      ChainGuard env (LVal.base finalLhs) y →
      env ⊢ y ↝ (.borrow mutable target) →
      TargetInitialized nested target →
      ∀ {location : Location},
        RuntimeFrame.LocReads store target location →
        location ≠ leafLoc) →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign lv (.val value)) store' (.val finalValue) →
    FullTerminalStateSafe store' finalValue nested .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hwriteTop hlvTop
    hshape hwellTy hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint
    htypingFinal hlocFinal hguardFinal hleafChain hlen hleafLoc
    hlast hhops htailFrame hvalidValue hstep
  have hvalidStore : ValidStore store :=
    ValidRuntimeState.validStore hvalidRuntime
  have hheap : StoreOwnerTargetsHeap store :=
    ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
  have hwellEnv₃ : WellFormedEnv env₃ lifetime :=
    WellFormedEnv.envWrite hwell hborrowSafe htySafe hwriteTop hlvTop
      hshape hwellTy hnotWriteTop
  have hwellNested : WellFormedEnv nested lifetime :=
    WellFormedEnv.transport_of_pointwise
      (env := env₃) (result := nested) (fun y => (hpoint y).symm)
      hwellEnv₃
  have hstepFinal :
      Step store lifetime (.assign finalLhs (.val value)) store'
        (.val finalValue) :=
    assign_step_of_loc_eq hlocFinal hstep
  have hvalidRuntimeFinal :
      ValidRuntimeState store (.assign finalLhs (.val value)) :=
    validRuntimeState_assign_lhs_of_value hvalidRuntime
  have hvalidValueNested :
      ValidPartialValueWhenInitialized nested store (.value value)
        (.ty rhsTy) :=
    validPartialValueWhenInitialized_select_final_rhs
      hwell.1 hborrowSafe htySafe hwriteTop hlvTop hshape hwellTy
      hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint hvalidValue
  have hotherValidNested :
      ∀ y otherEnvSlot oldValue,
        y ≠ LVal.base finalLhs →
        env.slotAt y = some otherEnvSlot →
        store.slotAt (VariableProjection y) =
          some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
        ValidPartialValueWhenInitialized nested store oldValue
          otherEnvSlot.ty := by
    intro y otherEnvSlot oldValue hyFinal henvY hstoreY
    rcases hsafe.2 y otherEnvSlot henvY with
      ⟨safeValue, hsafeStoreY, hvalidOld⟩
    have hvalueEq : safeValue = oldValue := by
      have hslotEq :=
        Option.some.inj (hsafeStoreY.symm.trans hstoreY)
      exact congrArg StoreSlot.value hslotEq
    subst hvalueEq
    exact validPartialValueWhenInitialized_select_final_unchanged_slot
      hwell.1 hborrowSafe htySafe hwriteTop hlvTop hshape hwellTy
      hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint hyFinal
      henvY hvalidOld
  have hvalueHeap : ValueOwnerTargetsHeap value :=
    TermOwnerTargetsHeap.value
      (termOwnerTargetsHeap_assign_inner
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
  have hvalueUnowned :
      ∀ owned, owned ∈ valueOwningLocations value →
        ¬ ProgramStore.Owns store owned := by
    intro owned hmem
    exact
      (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
        (by
          simpa [termOwningLocations, termValues,
            partialValueOwningLocations] using hmem))
  have hvalueFrame :
      ∀ location,
        RuntimeFrame.ReachesWhenInitialized nested store (.value value)
          (.ty rhsTy) location →
        location ≠ leafLoc := by
    intro location hreach
    exact reachesWhenInitialized_select_final_rhs_ne_leaf
      hsafe hvalidStore hheap hborrowSafe htySafe hwriteTop hlvTop hshape
      hwellTy hnotWriteTop henvFinal hselectFinal hwriteFinal hpoint
      hguardFinal hleafChain hvalueHeap hvalueUnowned hreach
  have hotherFrame :
      ∀ y otherEnvSlot oldValue,
        y ≠ LVal.base finalLhs →
        env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.ReachesWhenInitialized nested store oldValue
          otherEnvSlot.ty location →
      location ≠ leafLoc := by
    intro y otherEnvSlot oldValue hyFinal henvY hstoreY location hreach
    exact reachesWhenInitialized_select_final_stored_ne_leaf_of_live_source_entries
      hvalidStore hheap hleafChain hyFinal henvY hstoreY
      (by
        intro mutable target hentry hinitialized location hreads
        exact
          source_entry_select_final_live_of_tail_frame_locReads_ne
            hsafe hvalidStore hheap hwell.1 hborrowSafe htySafe
            hwriteTop hlvTop hshape hwellTy hnotWriteTop henvFinal
            hselectFinal hwriteFinal hpoint hguardFinal hleafChain hlen
            hlast hhops rfl hyFinal htailFrame hentry hinitialized hreads)
      hreach
  have hterminal : TerminalStateSafe store' finalValue nested .unit :=
    preservation_assign_pathSelect_step_runtime_whenInitialized_of_frames
      hwell hborrowSafe htySafe hsafe hvalidRuntimeFinal htypingFinal hshape
      hwellTy hwriteFinal hwellNested henvFinal hselectFinal hleafLoc hvalidValue
      hstepFinal hvalidValueNested hotherValidNested hvalueFrame hotherFrame
  exact TerminalStateSafe.full_of_wellFormed hterminal hwellNested
    WellFormedTy.unit

/-- General assignment preservation reduced to the selected-final tail frame. -/
theorem preservation_assign_step_runtime_whenInitialized_of_tail_frame
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime : Lifetime} {lhs : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign lhs (.val value)) →
    LValTyping env lhs oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite env lhs rhsTy env' →
    ¬ WriteProhibited env' lhs →
    (∀ {finalLhs : LVal} {rootSlot : EnvSlot} {nested : Env}
      {leafTy : PartialTy} {leafLoc : Location} {k : Nat},
      env.slotAt (LVal.base finalLhs) = some rootSlot →
      PathSelect (LVal.path finalLhs) rootSlot.ty leafTy →
      EnvWrite env finalLhs rhsTy nested →
      (∀ y, env'.slotAt y = nested.slotAt y) →
      LValTyping env finalLhs oldTy targetLifetime →
      store.loc lhs = store.loc finalLhs →
      ChainGuard env (LVal.base lhs) (LVal.base finalLhs) →
      OwnsChain store (VariableProjection (LVal.base finalLhs)) k leafLoc →
      k = (LVal.path finalLhs).length →
      store.loc finalLhs = some leafLoc →
      (finalLhs = lhs ∨
        ∃ (holder : Name) (path' : Path) (target' : LVal),
          env ⊢ holder ↝ (.borrow true target') ∧
          finalLhs = prependPath path' target') →
      HopsTo env env' lhs finalLhs →
      ∀ {mutable : Bool} {target : LVal} {y : Name},
        y ≠ LVal.base finalLhs →
        ChainGuard env (LVal.base finalLhs) y →
        env ⊢ y ↝ (.borrow mutable target) →
        TargetInitialized nested target →
        ∀ {location : Location},
          RuntimeFrame.LocReads store target location →
          location ≠ leafLoc) →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign lhs (.val value)) store' (.val finalValue) →
    FullTerminalStateSafe store' finalValue env' .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hlhs hshape hwellTy
    hwrite hnotWrite htailFrame hvalidValue hstep
  rcases EnvWrite.select_final hsafe hwell.1 hborrowSafe hnotWrite hshape
      hwrite hlhs with
    ⟨finalLhs, rootSlot, nested, leafTy, henvFinal, hselectFinal,
      hwriteFinal, hpoint, htypingFinal, hlocFinal, hguardFinal,
      hlast, hhops⟩
  rcases PathSelect.runtime_leaf_whenInitialized hsafe henvFinal
      hselectFinal with
    ⟨_rootStore, leafLoc, _leafSlot, k, _hrootStore, _hrootLifetime,
      _hrootValid, _hleafStore, _hleafValid, _hprefix, hleafChain, hlen,
      hlocLeaf⟩
  have hfinalLocSome : ∃ finalLocation,
      store.loc finalLhs = some finalLocation := by
    cases hstep with
    | assign hread _hwrite _hdrops =>
        unfold ProgramStore.read at hread
        cases hloc : store.loc lhs with
        | none =>
            simp [hloc] at hread
        | some lhsLocation =>
            refine ⟨lhsLocation, ?_⟩
            have hloc' : store.loc lhs = some lhsLocation := hloc
            rw [hlocFinal] at hloc'
            exact hloc'
  rcases hfinalLocSome with ⟨finalLocation, hfinalLoc⟩
  have hfinalLocationEq : finalLocation = leafLoc :=
    hlocLeaf hfinalLoc
  have hleafLoc : store.loc finalLhs = some leafLoc := by
    simpa [hfinalLocationEq] using hfinalLoc
  have hterminalNested :
      FullTerminalStateSafe store' finalValue nested .unit :=
    preservation_assign_selected_final_step_runtime_of_tail_frame
      hwell hborrowSafe htySafe hsafe hvalidRuntime hwrite hlhs hshape
      hwellTy hnotWrite henvFinal hselectFinal hwriteFinal hpoint
      htypingFinal hlocFinal hguardFinal hleafChain hlen hleafLoc hlast
      hhops
      (htailFrame henvFinal hselectFinal hwriteFinal hpoint htypingFinal
        hlocFinal hguardFinal hleafChain hlen hleafLoc hlast hhops)
      hvalidValue hstep
  exact FullTerminalStateSafe.transport_env_pointwise
    (store := store') (value := finalValue) (env := nested) (result := env')
    hpoint hterminalNested

/-- Assignment preservation with the selected-final tail frame discharged by the
follow-up paper's linearization invariant. -/
theorem preservation_assign_step_runtime_whenInitialized_of_linearized
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime : Lifetime} {lhs : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign lhs (.val value)) →
    LValTyping env lhs oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite env lhs rhsTy env' →
    ¬ WriteProhibited env' lhs →
    Linearizable env →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign lhs (.val value)) store' (.val finalValue) →
    FullTerminalStateSafe store' finalValue env' .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hlhs hshape hwellTy
    hwrite hnotWrite hlinear hvalidValue hstep
  rcases hlinear with ⟨φ, hφ⟩
  have hvalidStore : ValidStore store := ValidRuntimeState.validStore hvalidRuntime
  have hheap : StoreOwnerTargetsHeap store :=
    ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime
  exact preservation_assign_step_runtime_whenInitialized_of_tail_frame
    hwell hborrowSafe htySafe hsafe hvalidRuntime hlhs hshape hwellTy hwrite
    hnotWrite
    (by
      intro finalLhs rootSlot nested leafTy leafLoc k henvFinal hselectFinal
        hwriteFinal hpoint htypingFinal hlocFinal hguardFinal hleafChain
        hlen hleafLoc hlast hhops mutable target y hyFinal htailY hentry
        _hinitialized location hreads
      exact source_entry_select_final_tail_linearized_locReads_ne
        hφ hsafe hvalidStore hheap hwell.1 hleafChain hyFinal htailY
        hentry hreads)
    hvalidValue hstep

/-- Strict assignment preservation facade.

The selected-final proof internally uses the stale-aware frame lemmas while it
tracks which source borrows remain live through the write.  This wrapper is the
paper-facing boundary: callers provide the strict safe abstraction and strict
RHS value validity, and the implementation immediately coerces those premises
to the stale-aware forms needed by the current reduction. -/
theorem preservation_assign_step_runtime_of_tail_frame
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime : Lifetime} {lhs : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    FullSafeAbstraction store env →
    ValidRuntimeState store (.assign lhs (.val value)) →
    LValTyping env lhs oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite env lhs rhsTy env' →
    ¬ WriteProhibited env' lhs →
    (∀ {finalLhs : LVal} {rootSlot : EnvSlot} {nested : Env}
      {leafTy : PartialTy} {leafLoc : Location} {k : Nat},
      env.slotAt (LVal.base finalLhs) = some rootSlot →
      PathSelect (LVal.path finalLhs) rootSlot.ty leafTy →
      EnvWrite env finalLhs rhsTy nested →
      (∀ y, env'.slotAt y = nested.slotAt y) →
      LValTyping env finalLhs oldTy targetLifetime →
      store.loc lhs = store.loc finalLhs →
      ChainGuard env (LVal.base lhs) (LVal.base finalLhs) →
      OwnsChain store (VariableProjection (LVal.base finalLhs)) k leafLoc →
      k = (LVal.path finalLhs).length →
      store.loc finalLhs = some leafLoc →
      (finalLhs = lhs ∨
        ∃ (holder : Name) (path' : Path) (target' : LVal),
          env ⊢ holder ↝ (.borrow true target') ∧
          finalLhs = prependPath path' target') →
      HopsTo env env' lhs finalLhs →
      ∀ {mutable : Bool} {target : LVal} {y : Name},
        y ≠ LVal.base finalLhs →
        ChainGuard env (LVal.base finalLhs) y →
        env ⊢ y ↝ (.borrow mutable target) →
        TargetInitialized nested target →
        ∀ {location : Location},
          RuntimeFrame.LocReads store target location →
          location ≠ leafLoc) →
    ValidValue store value rhsTy →
    Step store lifetime (.assign lhs (.val value)) store' (.val finalValue) →
    FullTerminalStateSafe store' finalValue env' .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hlhs hshape hwellTy
    hwrite hnotWrite htailFrame hvalidValue hstep
  exact preservation_assign_step_runtime_whenInitialized_of_tail_frame
    hwell hborrowSafe htySafe hsafe.whenInitialized hvalidRuntime hlhs hshape
    hwellTy hwrite hnotWrite htailFrame hvalidValue.whenInitialized hstep

/-- Strict assignment preservation facade using the follow-up paper's
linearization invariant to close the selected-final tail frame. -/
theorem preservation_assign_step_runtime_of_linearized
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime : Lifetime} {lhs : LVal}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    BorrowSafeEnv env →
    TyBorrowSafeAgainstEnv env rhsTy →
    FullSafeAbstraction store env →
    ValidRuntimeState store (.assign lhs (.val value)) →
    LValTyping env lhs oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite env lhs rhsTy env' →
    ¬ WriteProhibited env' lhs →
    Linearizable env →
    ValidValue store value rhsTy →
    Step store lifetime (.assign lhs (.val value)) store' (.val finalValue) →
    FullTerminalStateSafe store' finalValue env' .unit := by
  intro hwell hborrowSafe htySafe hsafe hvalidRuntime hlhs hshape hwellTy
    hwrite hnotWrite hlinear hvalidValue hstep
  exact preservation_assign_step_runtime_whenInitialized_of_linearized
    hwell hborrowSafe htySafe hsafe.whenInitialized hvalidRuntime hlhs hshape
    hwellTy hwrite hnotWrite hlinear hvalidValue.whenInitialized hstep

/--
Bounded preservation for source terms.

The recursion follows the paper's typing derivation.  Assignment uses the
follow-up paper's linearization invariant to rule out cyclic live-borrow tails
after the write.
-/
theorem preservation_bounded
    (fuel : Nat) {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    term.size ≤ fuel →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    Env.FiniteSupport env₁ →
    Linearizable env₁ →
    store ≈ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    FullTerminalStateSafe finalStore finalValue env₂ ty := by
  induction fuel generalizing store finalStore env₁ env₂ typing lifetime term ty
      finalValue with
  | zero =>
      intro hsize _hsource _hvalidRuntime _hvalidStoreTyping _hwellFormed
        _hborrowSafe _hfinite _hlinear _hsafe _htyping _hmulti
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
  intro hsize hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe
    hfinite hlinear hsafe htyping hmulti
  refine TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      term.size ≤ fuel.succ →
      SourceTerm term →
      ∀ (store finalStore : ProgramStore) (finalValue : Value),
        ValidRuntimeState store term →
        ValidStoreTyping store term currentTyping →
        WellFormedEnv env lifetime →
        BorrowSafeEnv env →
        Env.FiniteSupport env →
        Linearizable env →
        store ≈ₛ env →
        MultiStep store lifetime term finalStore (.val finalValue) →
        FullTerminalStateSafe finalStore finalValue env₂ ty)
    (motive_2 := fun env currentTyping blockLifetime terms ty env₂ _ =>
      Term.size (.block blockLifetime terms) ≤ fuel.succ →
      SourceTerm (.block blockLifetime terms) →
      ∀ (outerLifetime : Lifetime) (store finalStore : ProgramStore)
        (finalValue : Value),
        LifetimeChild outerLifetime blockLifetime →
        ValidRuntimeState store (.block blockLifetime terms) →
        ValidStoreTyping store (.block blockLifetime terms) currentTyping →
        WellFormedEnv env blockLifetime →
        BorrowSafeEnv env →
        Env.FiniteSupport env →
        Linearizable env →
        store ≈ₛ env →
        WellFormedTy env₂ ty outerLifetime →
        MultiStep store outerLifetime (.block blockLifetime terms)
          finalStore (.val finalValue) →
        FullTerminalStateSafe finalStore finalValue
          (env₂.dropLifetime blockLifetime) ty)
    ?const ?copy ?move ?mutBorrow ?immBorrow ?box ?block
    ?declare ?assign
    ?singleton ?cons htyping hsize hsource store finalStore finalValue
    hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hfinite hlinear
    hsafe hmulti
  case const =>
    intro _env _typing _lifetime value _ty hvalueTyping _hsize hsource
      store finalStore finalValue hvalidRuntime hvalidStoreTyping hwell
      hborrowSafe _hfinite _hlinear hsafe hmulti
    have htermTyping :
        TermTyping _env _typing _lifetime (.val value) _ty _env :=
      TermTyping.const hvalueTyping
    have hterminal : TerminalStateSafe finalStore finalValue _env _ty :=
      preservation_multistep_runtime_value_whenInitialized
        hvalidRuntime hvalidStoreTyping hsafe.whenInitialized
        htermTyping hmulti
    have hwellTy :
        WellFormedTy _env _ty _lifetime :=
      (typingPreservesWellFormed_of_sourceTerm hsource hwell hborrowSafe
        htermTyping).2.2.1
    exact TerminalStateSafe.full_of_wellFormed hterminal hwell hwellTy
  case copy =>
    intro _env _typing _lifetime _valueLifetime lv _ty hLv hcopy hnotRead
      _hsize hsource store finalStore finalValue hvalidRuntime
      hvalidStoreTyping hwell hborrowSafe _hfinite _hlinear hsafe hmulti
    have htermTyping :
        TermTyping _env _typing _lifetime (.copy lv) _ty _env :=
      TermTyping.copy hLv hcopy hnotRead
    have hterminal : TerminalStateSafe finalStore finalValue _env _ty := by
      exact preservation_runtime_multistep_of_step_to_value_whenInitialized
        (term := .copy lv)
        (env := _env)
        (ty := _ty)
        (by intro hterminal; simp [Terminal] at hterminal)
        (by
          intro _store' _term' hstep
          cases hstep with
          | copy _hread =>
              exact ⟨_, rfl⟩)
        (by
          intro store' value hstep
          cases hstep with
          | copy hread =>
              have hlocAbs :
                  LValLocationAbstractionWhenInitialized _env store lv (.ty _ty) := by
                simpa [LValDefinedLocationAbstractionWhenInitialized] using
                  (lvalTyping_defined_location_whenInitialized
                    hsafe.whenInitialized hLv)
              rcases hlocAbs with
                ⟨location, slot, hloc, hslot, hvalidSlot⟩
              have hreadConcrete : store.read lv = some slot := by
                simp [ProgramStore.read, hloc, hslot]
              have hslotValueEq : slot.value = PartialValue.value value :=
                congrArg StoreSlot.value
                  (Option.some.inj (hreadConcrete.symm.trans hread))
              cases slot with
              | mk slotValue slotLifetime =>
                  cases hslotValueEq
                  have hvalidValue :
                      ValidPartialValueWhenInitialized _env store
                        (.value value) (.ty _ty) := by
                    simpa using hvalidSlot
                  have hnonOwner : PartialValueNonOwner (.value value) :=
                    validPartialValueWhenInitialized_nonOwner_of_envShape hvalidValue
                      (by
                        cases hcopy with
                        | unit => exact Or.inl rfl
                        | int => exact Or.inr (Or.inl rfl)
                        | immBorrow =>
                            exact Or.inr (Or.inr ⟨false, _, rfl⟩))
                  have hvalueOwnedNone : valueOwnedLocation? value = none := by
                    cases value with
                    | unit => rfl
                    | int _ => rfl
                    | ref ref =>
                        cases ref with
                        | mk location owner =>
                            cases owner
                            · rfl
                            · exact False.elim
                                (not_partialValueNonOwner_owning_ref
                                  (ref := { location := location, owner := true })
                                  rfl hnonOwner)
                  have hvalidStateValue :
                      ValidState store (.val value) := by
                    rcases hvalidRuntime.1 with
                      ⟨hvalidStore, _hvalidTerm, _hdisjoint⟩
                    exact ⟨hvalidStore,
                      by
                        simp [ValidTerm, termOwningLocations, termValues,
                          valueOwningLocations, hvalueOwnedNone],
                      by
                        intro owned hmem howns
                        simp [termOwningLocations, termValues,
                          valueOwningLocations, hvalueOwnedNone] at hmem⟩
                  exact ⟨⟨hvalidStateValue,
                      storeOwnersAllocated_copy_step
                        (ValidRuntimeState.storeOwnersAllocated hvalidRuntime)
                        (Step.copy (lifetime := _lifetime) hread),
                      ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime,
                      ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime,
                      termOwnerTargetsHeap_value_nonOwner hvalueOwnedNone⟩,
                    hsafe.whenInitialized,
                    hvalidValue⟩)
        hmulti
    have hwellTy :
        WellFormedTy _env _ty _lifetime :=
      (typingPreservesWellFormed_of_sourceTerm hsource hwell hborrowSafe
        htermTyping).2.2.1
    exact TerminalStateSafe.full_of_wellFormed hterminal hwell hwellTy
  case move =>
    intro _env₁ _env₂ _typing _lifetime _valueLifetime lv _ty hLv hnotWrite
      hmove _hsize hsource store finalStore finalValue hvalidRuntime
      _hvalidStoreTyping hwell hborrowSafe _hfinite _hlinear hsafe hmulti
    have htermTyping :
        TermTyping _env₁ _typing _lifetime (.move lv) _ty _env₂ :=
      TermTyping.move hLv hnotWrite hmove
    have hstatic :=
      typingPreservesWellFormed_of_sourceTerm hsource hwell hborrowSafe
        htermTyping
    have hterminal : TerminalStateSafe finalStore finalValue _env₂ _ty := by
      cases lv with
      | var x =>
          rcases LValTyping.var_inv hLv with ⟨slot, hslot, htyEq, hlifetimeEq⟩
          cases slot with
          | mk slotTy slotLifetime =>
              cases htyEq
              cases hlifetimeEq
              exact RuntimeFrame.preservation_move_var_multistep_runtime_whenInitialized_of_wellFormed
                hwell.whenInitialized hsafe.whenInitialized hvalidRuntime hslot
                hmove htermTyping hmulti
      | deref source =>
          cases hLv with
          | box hsourceBox =>
              exact preservation_move_deref_box_multistep_runtime_whenInitialized_of_wellFormed
                hwell.whenInitialized hsafe.whenInitialized hvalidRuntime
                hsourceBox hnotWrite hmove htermTyping hmulti
          | boxFull hsourceFull =>
              exact preservation_move_deref_boxFull_multistep_runtime_whenInitialized_of_wellFormed
                hwell.whenInitialized hsafe.whenInitialized hvalidRuntime
                hsourceFull hnotWrite hmove htermTyping hmulti
          | borrow hsourceBorrow htargets =>
              exfalso
              rcases hmove with ⟨moveSlot, struck, hslot, hstrike, _henv₂⟩
              have hsourceSlot :
                  _env₁.slotAt (LVal.base source) = some moveSlot := by
                simpa [LVal.base] using hslot
              have hstrikeAtBorrow :
                  Strike (LVal.path source ++ [()]) moveSlot.ty struck := by
                simpa [LVal.path] using hstrike
              rcases LValTyping.strike_suffix hsourceBorrow
                  hsourceSlot hstrikeAtBorrow with
                ⟨borrowStruck, hborrowStruck⟩
              cases borrowStruck <;> simp [Strike] at hborrowStruck
    exact TerminalStateSafe.full_of_wellFormed hterminal hstatic.1
      hstatic.2.2.1
  case mutBorrow =>
    intro _env _typing _lifetime _valueLifetime lv _ty hLv hmutable hnotWrite
      _hsize hsource store finalStore finalValue hvalidRuntime
      _hvalidStoreTyping hwell hborrowSafe _hfinite _hlinear hsafe hmulti
    have htermTyping :
        TermTyping _env _typing _lifetime (.borrow true lv)
          (.borrow true lv) _env :=
      TermTyping.mutBorrow hLv hmutable hnotWrite
    have hterminal :
        TerminalStateSafe finalStore finalValue _env (.borrow true lv) := by
      exact preservation_runtime_multistep_of_step_to_value_whenInitialized
        (term := .borrow true lv)
        (env := _env)
        (ty := .borrow true lv)
        (by intro hterminal; simp [Terminal] at hterminal)
        (by
          intro _store' _term' hstep
          cases hstep with
          | borrow _hloc =>
              exact ⟨_, rfl⟩)
        (by
          intro store' value hstep
          cases hstep with
          | borrow hloc =>
              refine ⟨validRuntimeState_borrow_step hvalidRuntime
                  (Step.borrow (lifetime := _lifetime) hloc),
                hsafe.whenInitialized, ?_⟩
              have hinitialized : TargetInitialized _env lv :=
                ⟨_ty, _valueLifetime, hLv⟩
              exact ValidPartialValueWhenInitialized.borrowLive
                (mutable := true) hinitialized hloc)
        hmulti
    have hwellTy :
        WellFormedTy _env (.borrow true lv) _lifetime :=
      (typingPreservesWellFormed_of_sourceTerm hsource hwell hborrowSafe
        htermTyping).2.2.1
    exact TerminalStateSafe.full_of_wellFormed hterminal hwell hwellTy
  case immBorrow =>
    intro _env _typing _lifetime _valueLifetime lv _ty hLv hnotRead
      _hsize hsource store finalStore finalValue hvalidRuntime
      _hvalidStoreTyping hwell hborrowSafe _hfinite _hlinear hsafe hmulti
    have htermTyping :
        TermTyping _env _typing _lifetime (.borrow false lv)
          (.borrow false lv) _env :=
      TermTyping.immBorrow hLv hnotRead
    have hterminal :
        TerminalStateSafe finalStore finalValue _env (.borrow false lv) := by
      exact preservation_runtime_multistep_of_step_to_value_whenInitialized
        (term := .borrow false lv)
        (env := _env)
        (ty := .borrow false lv)
        (by intro hterminal; simp [Terminal] at hterminal)
        (by
          intro _store' _term' hstep
          cases hstep with
          | borrow _hloc =>
              exact ⟨_, rfl⟩)
        (by
          intro store' value hstep
          cases hstep with
          | borrow hloc =>
              refine ⟨validRuntimeState_borrow_step hvalidRuntime
                  (Step.borrow (lifetime := _lifetime) hloc),
                hsafe.whenInitialized, ?_⟩
              have hinitialized : TargetInitialized _env lv :=
                ⟨_ty, _valueLifetime, hLv⟩
              exact ValidPartialValueWhenInitialized.borrowLive
                (mutable := false) hinitialized hloc)
        hmulti
    have hwellTy :
        WellFormedTy _env (.borrow false lv) _lifetime :=
      (typingPreservesWellFormed_of_sourceTerm hsource hwell hborrowSafe
        htermTyping).2.2.1
    exact TerminalStateSafe.full_of_wellFormed hterminal hwell hwellTy
  case box =>
    intro _env₁ _env₂ _typing _lifetime inner _ty hinner ih hsize hsource
      store finalStore finalValue hvalidRuntime hvalidStoreTyping hwell
      hborrowSafe hfinite hlinear hsafe hmulti
    have htermTyping :
        TermTyping _env₁ _typing _lifetime (.box inner) (.box _ty) _env₂ :=
      TermTyping.box hinner
    have hstatic :=
      typingPreservesWellFormed_of_sourceTerm hsource hwell hborrowSafe
        htermTyping
    have hterminal : TerminalStateSafe finalStore finalValue _env₂ (.box _ty) :=
      preservation_box_context_terminal_multistep_runtime_whenInitialized
        (by
          intro midStore value hvalidInner hvalidStoreTypingInner _hsafeInner
            hinnerTyping hmultiInner
          exact (ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            (SourceTerm.box_inner hsource)
            store midStore value hvalidInner hvalidStoreTypingInner
            hwell hborrowSafe hfinite hlinear hsafe hmultiInner).whenInitialized)
        hvalidRuntime hvalidStoreTyping hsafe.whenInitialized
        htermTyping hmulti
    exact TerminalStateSafe.full_of_wellFormed hterminal hstatic.1
      hstatic.2.2.1
  case block =>
    intro _env₁ _env₂ _env₃ _typing _lifetime blockLifetime terms _ty hchild
      hterms hwellTy hdrop ih hsize hsource store finalStore finalValue
      hvalidRuntime hvalidStoreTyping hwell hborrowSafe hfinite hlinear hsafe
      hmulti
    subst hdrop
    exact ih hsize hsource _lifetime store finalStore finalValue hchild
      hvalidRuntime hvalidStoreTyping
      (WellFormedEnv.weaken hwell (LifetimeChild.outlives hchild))
      hborrowSafe hfinite hlinear hsafe hwellTy hmulti
  case declare =>
    intro _env₁ _env₂ _env₃ _typing _lifetime x inner _ty hfresh hinner
      hfreshOut henv₃ ih hsize hsource store finalStore finalValue
      hvalidRuntime hvalidStoreTyping hwell hborrowSafe hfinite hlinear hsafe
      hmulti
    have htermTyping :
        TermTyping _env₁ _typing _lifetime (.letMut x inner) .unit _env₃ :=
      TermTyping.declare hfresh hinner hfreshOut henv₃
    have hstatic :=
      typingPreservesWellFormed_of_sourceTerm hsource hwell hborrowSafe
        htermTyping
    have hinnerStatic :=
      typingPreservesWellFormed_of_sourceTerm
        (SourceTerm.declare_inner hsource) hwell hborrowSafe hinner
    have hterminalWeak : TerminalStateSafe finalStore finalValue _env₃ .unit :=
      preservation_declare_context_terminal_multistep_runtime_whenInitialized
        (by
          intro midStore value hvalidInner hvalidStoreTypingInner _hwellInner
            _hsafeInner hinnerTyping hmultiInner
          exact (ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            (SourceTerm.declare_inner hsource)
            store midStore value hvalidInner hvalidStoreTypingInner
            hwell hborrowSafe hfinite hlinear hsafe hmultiInner).whenInitialized)
        hvalidRuntime hvalidStoreTyping hwell.whenInitialized
        hinnerStatic.1.whenInitialized hsafe.whenInitialized
        hinnerStatic.2.2.1.whenInitialized hinner hfreshOut henv₃ hmulti
    exact TerminalStateSafe.full_of_wellFormed hterminalWeak hstatic.1
      hstatic.2.2.1
  case assign =>
    intro _env₁ _env₂ _env₃ _typing _lifetime targetLifetime lhs oldTy rhs
      rhsTy hRhs hLhsPost hshape hwellTy hwrite hnotWrite ih hsize hsource
      store finalStore finalValue hvalidRuntime hvalidStoreTyping hwell
      hborrowSafe hfinite hlinear hsafe hmulti
    rcases multistep_assign_to_value_inv hmulti with
      ⟨midStore, value, hinnerMulti, hassignStep⟩
    have hterminalInner :
        FullTerminalStateSafe midStore value _env₂ rhsTy :=
      ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        (SourceTerm.assign_inner hsource)
        store midStore value
        (validRuntimeState_assign_inner hvalidRuntime)
        (validStoreTyping_assign_inner hvalidStoreTyping)
        hwell hborrowSafe hfinite hlinear hsafe hinnerMulti
    have hinnerStatic :=
      typingPreservesWellFormed_of_sourceTerm
        (SourceTerm.assign_inner hsource) hwell hborrowSafe hRhs
    have hlinearInner : Linearizable _env₂ :=
      typingPreservesLinearizable_of_sourceTerm
        (SourceTerm.assign_inner hsource) hwell hborrowSafe hfinite hlinear hRhs
    exact preservation_assign_step_runtime_of_linearized
      hinnerStatic.1 hinnerStatic.2.1 hinnerStatic.2.2.2
      hterminalInner.2.1
      (validRuntimeState_assign_value_of_value hterminalInner.1)
      hLhsPost hshape hwellTy hwrite hnotWrite hlinearInner
      hterminalInner.2.2 hassignStep
  case singleton =>
    intro _env₁ _env₂ _typing blockLifetime inner _ty hinner ih hsize hsource
      outerLifetime store finalStore finalValue hchild hvalidRuntime
      hvalidStoreTyping hwell hborrowSafe hfinite hlinear hsafe hwellTy hmulti
    rcases multistep_block_head_to_value_inv hmulti with
      ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
    have hterminalInner :
        FullTerminalStateSafe midStore value _env₂ _ty :=
      ih (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
        (SourceTerm.block_head hsource)
        store midStore value
        (validRuntimeState_block_singleton_inner hvalidRuntime)
        (validStoreTyping_block_singleton_inner hvalidStoreTyping)
        hwell hborrowSafe hfinite hlinear hsafe hinnerMulti
    have hinnerStatic :=
      typingPreservesWellFormed_of_sourceTerm
        (SourceTerm.block_head hsource) hwell hborrowSafe hinner
    have hterminalWeak :
        TerminalStateSafe finalStore finalValue
          (_env₂.dropLifetime blockLifetime) _ty :=
      preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop
        (validRuntimeState_block_singleton_value_of_value hterminalInner.1)
        hterminalInner.2.1.whenInitialized hchild hinnerStatic.1.whenInitialized
        hwellTy hterminalInner.2.2.whenInitialized hblockValueMulti
    have hblockWell :=
      block_preserves_wellFormed hchild hinnerStatic.1 hwellTy rfl
    exact TerminalStateSafe.full_of_wellFormed hterminalWeak hblockWell.1
      hblockWell.2
  case cons =>
    intro _env₁ _env₂ _env₃ _typing blockLifetime head rest termTy finalTy
      hhead hrest ihHead ihRest hsize hsource outerLifetime store finalStore
      finalValue hchild hvalidRuntime hvalidStoreTyping hwell hborrowSafe
      hfinite hlinear hsafe hwellTy hmulti
    cases rest with
    | nil =>
        cases hrest
    | cons next restTail =>
        have hsourceHead : SourceTerm head :=
          SourceTerm.block_head hsource
        have hsourceTail : SourceTerm (.block blockLifetime (next :: restTail)) :=
          SourceTerm.block_tail hsource
        rcases multistep_block_head_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
        have hterminalHead :
            FullTerminalStateSafe midStore value _env₂ termTy :=
          ihHead (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            hsourceHead store midStore value
            (validRuntimeState_block_head hvalidRuntime)
            (validStoreTyping_block_head hvalidStoreTyping)
            hwell hborrowSafe hfinite hlinear hsafe hinnerMulti
        have hheadStatic :=
          typingPreservesWellFormed_of_sourceTerm hsourceHead hwell
            hborrowSafe hhead
        have hwellInner : WellFormedEnv _env₂ blockLifetime := hheadStatic.1
        have hborrowSafeInner : BorrowSafeEnv _env₂ := hheadStatic.2.1
        have hfiniteInner : Env.FiniteSupport _env₂ :=
          TermTyping.finiteSupport hhead hfinite
        have hlinearInner : Linearizable _env₂ :=
          typingPreservesLinearizable_of_sourceTerm hsourceHead hwell
            hborrowSafe hfinite hlinear hhead
        have hvalueBlockValid :
            ValidRuntimeState midStore
              (.block blockLifetime (.val value :: next :: restTail)) :=
          validRuntimeState_block_value_cons_of_value_source_tail
            hsourceTail hterminalHead.1
        have htailStoreTypingAtMid :
            ValidStoreTyping midStore (.block blockLifetime (next :: restTail))
              _typing :=
          validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
            (validStoreTyping_block_tail_of_cons hvalidStoreTyping)
        rcases multistep_block_to_value_first_step_inv hblockValueMulti with
          hseqCase | hblockACase | hblockBCase
        · rcases hseqCase with
            ⟨seqValue, seqNext, seqRest, storeAfterDrop, hterms, hdrops,
              htailMulti⟩
          cases hterms
          have hseqStep :
              Step midStore outerLifetime
                (.block blockLifetime (.val value :: next :: restTail))
                storeAfterDrop (.block blockLifetime (next :: restTail)) :=
            Step.seq hdrops
          have hvalidTailAfter :
              ValidRuntimeState storeAfterDrop
                (.block blockLifetime (next :: restTail)) :=
            validRuntimeState_seq_step hvalueBlockValid hseqStep
          have hsafeTailAfter :
              storeAfterDrop ≈ₛ _env₂ :=
            safeAbstraction_seq_value_drop hterminalHead.2.1
              hvalueBlockValid hwellInner hdrops
          have htailStoreTyping :
              ValidStoreTyping storeAfterDrop
                (.block blockLifetime (next :: restTail)) _typing :=
            validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
              htailStoreTypingAtMid
          exact ihRest
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            hsourceTail outerLifetime storeAfterDrop finalStore finalValue
            hchild hvalidTailAfter htailStoreTyping hwellInner
            hborrowSafeInner hfiniteInner hlinearInner hsafeTailAfter hwellTy
            htailMulti
        · rcases hblockACase with
            ⟨blockTerm, blockRest, storeAfter, termAfter, hterms, hstep,
              _htailMulti⟩
          cases hterms
          exact False.elim (value_no_step hstep)
        · rcases hblockBCase with
            ⟨blockValue, storeAfter, hterms, _hdrops, _htailMulti⟩
          cases hterms

/-- Lemma 4.11, Preservation. -/
theorem preservation
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    BorrowSafeEnv env₁ →
    Env.FiniteSupport env₁ →
    Linearizable env₁ →
    store ≈ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe
    hfinite hlinear hsafe htyping hmulti
  exact preservation_bounded term.size (Nat.le_refl _) hsource
    hvalidRuntime hvalidStoreTyping hwellFormed hborrowSafe hfinite hlinear
    hsafe htyping hmulti

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/- Paper-facing alias for Lemma 4.11. -/
theorem lemma_4_11_preservation
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value}
    (hsource : SourceTerm term)
    (hvalid : ValidRuntimeState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hborrowSafe : BorrowSafeEnv env₁)
    (hfinite : Env.FiniteSupport env₁)
    (hlinear : Linearizable env₁)
    (hsafe : store ≈ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hmulti : MultiStep store lifetime term finalStore (.val finalValue)) :
    FullTerminalStateSafe finalStore finalValue env₂ ty :=
  LwRust.Paper.preservation hsource hvalid hstoreTyping hwellFormed
    hborrowSafe hfinite hlinear hsafe htyping hmulti

end LwRust.Paper.Soundness
