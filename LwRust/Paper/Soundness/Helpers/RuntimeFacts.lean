import LwRust.Paper.Soundness.Helpers.Eqv

/-!
# Soundness helpers: RuntimeFacts

Runtime-invariant preservation facts (Linearizable / Coherent packaging).
-/

namespace LwRust
namespace Paper

open Core

/-! ### Runtime-invariant preservation facts

These package the two runtime invariants (`Linearizable`, `Coherent`) that
`lvalTyping_strengthen_transport` consumes, as preserved by the two state
operations that the Appendix 9.6 borrow-invariance argument performs: a single
`EnvWrite` and an `EnvJoin` (the write fan-out's branch merge).

`Linearizable` preservation is the `lw_rust_followup` contribution (Definition
11 plus its preservation proposition): a common rank function survives a write
under the rule-carried RHS-rank side condition, and survives branch joins when
both branches use the same rank function.

`Coherent` preservation is Section-4 content proved from explicit
root-transport/coherence side conditions carried by the strengthened write and
declaration rules. -/

structure EnvJoinCoherenceObligations (left right join : Env) : Prop where
  borrow_transport
    {lv : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime : Lifetime} :
    LValTyping join lv (.ty (.borrow mutable targets)) borrowLifetime →
      (∃ leftBorrowLifetime,
        LValTyping left lv (.ty (.borrow mutable targets)) leftBorrowLifetime ∧
          ∀ targetTy targetLifetime,
            LValTargetsTyping left targets (.ty targetTy) targetLifetime →
              ∃ joinTargetTy joinTargetLifetime,
                LValTargetsTyping join targets (.ty joinTargetTy) joinTargetLifetime)
      ∨
      (∃ rightBorrowLifetime,
        LValTyping right lv (.ty (.borrow mutable targets)) rightBorrowLifetime ∧
          ∀ targetTy targetLifetime,
            LValTargetsTyping right targets (.ty targetTy) targetLifetime →
              ∃ joinTargetTy joinTargetLifetime,
                LValTargetsTyping join targets (.ty joinTargetTy) joinTargetLifetime)

theorem EnvJoin.preserves_coherent_of_obligations {left right join : Env} :
    Coherent left →
    Coherent right →
    EnvJoinCoherenceObligations left right join →
    Coherent join := by
  intro hleftCoh hrightCoh hobligations lv mutable targets borrowLifetime htyping
  rcases hobligations.borrow_transport htyping with
    ⟨leftBorrowLifetime, hleftTyping, htargetsTransport⟩ |
    ⟨rightBorrowLifetime, hrightTyping, htargetsTransport⟩
  · rcases hleftCoh lv mutable targets leftBorrowLifetime hleftTyping with
      ⟨targetTy, targetLifetime, htargetsLeft⟩
    exact htargetsTransport targetTy targetLifetime htargetsLeft
  · rcases hrightCoh lv mutable targets rightBorrowLifetime hrightTyping with
      ⟨targetTy, targetLifetime, htargetsRight⟩
    exact htargetsTransport targetTy targetLifetime htargetsRight

theorem EnvWrite.preserves_coherent_of_obligations {env result : Env}
    {writeBase : Name} :
    Coherent env →
    EnvWriteCoherenceObligations env result writeBase →
    Coherent result := by
  intro hcoh hobligations lv mutable targets borrowLifetime htyping
  by_cases hbase : LVal.base lv = writeBase
  · exact hobligations.written_root_coherent hbase htyping
  · rcases hobligations.old_root_transport hbase htyping with
      ⟨⟨oldBorrowLifetime, htypingOld⟩, htargetsTransport⟩
    exact hcoh lv mutable targets oldBorrowLifetime htypingOld
      |>.elim (fun targetTy htarget =>
        htarget.elim (fun targetLifetime htargetsOld =>
          htargetsTransport targetTy targetLifetime htargetsOld))

/-- Under a *shape-preserving* strengthening the occurring variables only grow:
`a ⊑ b` and `a ≈shape b` give `vars a ⊆ vars b`.  (`sameShape` rules out the
`undef`-introducing strengthening cases, which would erase variables.) -/
theorem partialTy_vars_mono {a b : PartialTy} (hstr : PartialTyStrengthens a b) :
    PartialTy.sameShape a b → ∀ v, v ∈ PartialTy.vars a → v ∈ PartialTy.vars b := by
  induction hstr with
  | reflex => intro _ v hv; exact hv
  | @box aL bL _hsub ih =>
      intro hshape v hv
      simp only [PartialTy.vars] at hv ⊢
      exact ih (by simpa [PartialTy.sameShape] using hshape) v hv
  | @tyBox aT bT _hsub ih =>
      intro hshape v hv
      simp only [PartialTy.vars, Ty.vars] at hv ⊢
      exact ih (by simpa [PartialTy.sameShape, Ty.sameShape] using hshape) v hv
  | @borrow m L R hsub =>
      intro _ v hv
      simp only [PartialTy.vars, Ty.vars, List.mem_map] at hv ⊢
      obtain ⟨t, ht, rfl⟩ := hv
      exact ⟨t, hsub ht, rfl⟩
  | @undefLeft aT bT _h _ih => intro _ v hv; simp [PartialTy.vars] at hv
  | @intoUndef aT bT _h _ih => intro hshape v _; simp [PartialTy.sameShape] at hshape
  | @boxIntoUndef aL bT _h _ih => intro hshape v _; simp [PartialTy.sameShape] at hshape

theorem EnvJoin.slot_union {left right join : Env} {x : Name}
    {leftSlot rightSlot joinSlot : EnvSlot} :
    EnvJoin left right join →
    left.slotAt x = some leftSlot →
    right.slotAt x = some rightSlot →
    join.slotAt x = some joinSlot →
    leftSlot.lifetime = joinSlot.lifetime ∧
      rightSlot.lifetime = joinSlot.lifetime ∧
      PartialTyUnion leftSlot.ty rightSlot.ty joinSlot.ty := by
  intro hjoin hleftSlot hrightSlot hjoinSlot
  have hleftMem : left ∈ ({left, right} : Set Env) := by simp
  have hrightMem : right ∈ ({left, right} : Set Env) := by simp
  have hleftStrength := hjoin.1 hleftMem x
  have hrightStrength := hjoin.1 hrightMem x
  simp [hleftSlot, hrightSlot, hjoinSlot] at hleftStrength hrightStrength
  refine ⟨hleftStrength.1, hrightStrength.1, ?_⟩
  constructor
  · intro ty hty
    simp at hty
    rcases hty with hty | hty
    · subst hty
      exact hleftStrength.2
    · subst hty
      exact hrightStrength.2
  · intro candidate hcandidate
    let candidateEnv : Env :=
      join.update x { joinSlot with ty := candidate }
    have hupper : candidateEnv ∈ upperBounds ({left, right} : Set Env) := by
      intro env henv
      simp at henv
      rcases henv with henv | henv
      · subst henv
        intro y
        by_cases hy : y = x
        · subst hy
          simp [candidateEnv, Env.update, hleftSlot]
          exact ⟨hleftStrength.1, hcandidate (by simp)⟩
        · have hleftAtY := hjoin.1 hleftMem y
          simpa [candidateEnv, Env.update, hy] using hleftAtY
      · subst henv
        intro y
        by_cases hy : y = x
        · subst hy
          simp [candidateEnv, Env.update, hrightSlot]
          exact ⟨hrightStrength.1, hcandidate (by simp)⟩
        · have hrightAtY := hjoin.1 hrightMem y
          simpa [candidateEnv, Env.update, hy] using hrightAtY
    have hjoinStrength := hjoin.2 hupper x
    simp [candidateEnv, Env.update, hjoinSlot] at hjoinStrength
    exact hjoinStrength

theorem EnvWrite.shapePreserved {rank : Nat} {env result : Env} {lv : LVal}
    {ty : Ty} :
    0 < rank →
    EnvWrite rank env lv ty result →
    (∀ slot, env.slotAt (LVal.base lv) = some slot →
      WriteShapeCompat env (LVal.path lv) slot.ty ty) →
    EnvShapePreserved env result := by
  intro hrank hwrite hsc
  refine EnvWrite.rec
    (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
      0 < rank → WriteShapeCompat env₁ path oldTy ty →
        EnvShapePreserved env₁ env₂ ∧ PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun rank env path targets ty result _ =>
      0 < rank →
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteShapeCompat env (LVal.path (prependPath path t)) tslot.ty ty) →
        EnvShapePreserved env result)
    (motive_3 := fun rank env lv ty result _ =>
      0 < rank →
      (∀ slot, env.slotAt (LVal.base lv) = some slot →
        WriteShapeCompat env (LVal.path lv) slot.ty ty) →
        EnvShapePreserved env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite hrank hsc
  case strong =>
    intro env old ty hrank0 _hcompat
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty hshape hjoinTy _hrank _hcompat
    exact ⟨EnvShapePreserved.refl env, partialTyJoin_sameShape hshape hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank hcompat
    cases hcompat with
    | box hInner =>
        rcases ih hrank hInner with ⟨hpres, hshape⟩
        exact ⟨hpres, hshape⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank hcompat
    cases hcompat with
    | borrow hTargets =>
        exact ⟨ih (Nat.succ_pos rank) hTargets, PartialTy.sameShape_refl _⟩
  case nil =>
    intro rank env path ty _hrank _hprem
    exact EnvShapePreserved.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank hprem
    exact ih hrank (fun slot hslot => hprem target (by simp) slot hslot)
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites hrank hprem
    have hupd : EnvShapePreserved env updated :=
      ihWrite hrank (fun slot hslot => hprem target (by simp) slot hslot)
    have hrest : EnvShapePreserved env restEnv :=
      ihWrites hrank
        (fun t ht slot hslot => hprem t (List.mem_cons_of_mem _ ht) slot hslot)
    intro x rslot hrslot
    rcases EnvJoin.lifetimesPreserved_left hjoin x rslot hrslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x rslot hrslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hrslot with ⟨_, _, hunionSlot⟩
    rcases hupd x us hus with ⟨es, hes, hShapeUS⟩
    rcases hrest x rs hrs with ⟨es', hes', hShapeRS⟩
    have hesEq : es = es' := Option.some.inj (hes.symm.trans hes')
    subst hesEq
    have hUSRS : PartialTy.sameShape us.ty rs.ty :=
      PartialTy.sameShape_trans (PartialTy.sameShape_symm hShapeUS) hShapeRS
    have hUSc : PartialTy.sameShape us.ty rslot.ty :=
      partialTyUnion_sameShape_of_sameShape hunionSlot hUSRS
    exact ⟨es, hes, PartialTy.sameShape_trans hShapeUS hUSc⟩
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank hprem
    have hsc' : WriteShapeCompat env₁ (LVal.path lv) slot.ty ty := hprem slot hslot
    rcases ih hrank hsc' with ⟨hpres, hshape⟩
    exact EnvShapePreserved.update_from_source_slot hpres hslot hshape

/-- Fan-out shape stability: a positive-rank `WriteBorrowTargets` of `ty`
preserves the shape of every slot, given per-target leaf shape-compatibility.
This is the `motive_2` already established inside `EnvWrite.shapePreserved`,
extracted as a standalone lemma so the write-fan-out driver can derive the
branch-sameShape it needs for the join merge. -/
theorem WriteBorrowTargets.shapePreserved {rank : Nat} {env result : Env}
    {path : List Unit} {targets : List LVal} {ty : Ty} :
    0 < rank →
    WriteBorrowTargets rank env path targets ty result →
    (∀ t, t ∈ targets → ∀ tslot,
      env.slotAt (LVal.base (prependPath path t)) = some tslot →
      WriteShapeCompat env (LVal.path (prependPath path t)) tslot.ty ty) →
    EnvShapePreserved env result := by
  intro hrank hwrites hsc
  refine WriteBorrowTargets.rec
    (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
      0 < rank → WriteShapeCompat env₁ path oldTy ty →
        EnvShapePreserved env₁ env₂ ∧ PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun rank env path targets ty result _ =>
      0 < rank →
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteShapeCompat env (LVal.path (prependPath path t)) tslot.ty ty) →
        EnvShapePreserved env result)
    (motive_3 := fun rank env lv ty result _ =>
      0 < rank →
      (∀ slot, env.slotAt (LVal.base lv) = some slot →
        WriteShapeCompat env (LVal.path lv) slot.ty ty) →
        EnvShapePreserved env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites hrank hsc
  case strong =>
    intro env old ty hrank0 _hcompat
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty hshape hjoinTy _hrank _hcompat
    exact ⟨EnvShapePreserved.refl env, partialTyJoin_sameShape hshape hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank hcompat
    cases hcompat with
    | box hInner =>
        rcases ih hrank hInner with ⟨hpres, hshape⟩
        exact ⟨hpres, hshape⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank hcompat
    cases hcompat with
    | borrow hTargets =>
        exact ⟨ih (Nat.succ_pos rank) hTargets, PartialTy.sameShape_refl _⟩
  case nil =>
    intro rank env path ty _hrank _hprem
    exact EnvShapePreserved.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank hprem
    exact ih hrank (fun slot hslot => hprem target (by simp) slot hslot)
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites hrank hprem
    have hupd : EnvShapePreserved env updated :=
      ihWrite hrank (fun slot hslot => hprem target (by simp) slot hslot)
    have hrest : EnvShapePreserved env restEnv :=
      ihWrites hrank
        (fun t ht slot hslot => hprem t (List.mem_cons_of_mem _ ht) slot hslot)
    intro x rslot hrslot
    rcases EnvJoin.lifetimesPreserved_left hjoin x rslot hrslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x rslot hrslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hrslot with ⟨_, _, hunionSlot⟩
    rcases hupd x us hus with ⟨es, hes, hShapeUS⟩
    rcases hrest x rs hrs with ⟨es', hes', hShapeRS⟩
    have hesEq : es = es' := Option.some.inj (hes.symm.trans hes')
    subst hesEq
    have hUSRS : PartialTy.sameShape us.ty rs.ty :=
      PartialTy.sameShape_trans (PartialTy.sameShape_symm hShapeUS) hShapeRS
    have hUSc : PartialTy.sameShape us.ty rslot.ty :=
      partialTyUnion_sameShape_of_sameShape hunionSlot hUSRS
    exact ⟨es, hes, PartialTy.sameShape_trans hShapeUS hUSc⟩
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank hprem
    have hsc' : WriteShapeCompat env₁ (LVal.path lv) slot.ty ty := hprem slot hslot
    rcases ih hrank hsc' with ⟨hpres, hshape⟩
    exact EnvShapePreserved.update_from_source_slot hpres hslot hshape

/-- Structural witness that a Definition 3.23 write descends to *initialised*
(`.ty`, never `.undef`) leaves.  Mirrors `WriteShapeCompat` but its leaf premise
is merely "the old leaf type is defined" — no `ShapeCompatible` (hence no
recursive target-typing construction).  This is exactly the discriminant of the
shape-breaking case: a positive-rank `W-Weak` preserves shape iff its leaf is not
`.undef` (re-initialisation `.undef ⊔ ty = ty` is the sole shape change). -/
inductive WriteLeafTy (env : Env) : List Unit → PartialTy → Ty → Prop where
  | leaf {oldTy ty : Ty} :
      WriteLeafTy env [] (.ty oldTy) ty
  | box {path : List Unit} {inner : PartialTy} {ty : Ty} :
      WriteLeafTy env path inner ty →
      WriteLeafTy env (() :: path) (.box inner) ty
  | borrow {mutable : Bool} {path : List Unit} {targets : List LVal} {ty : Ty} :
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty) →
      WriteLeafTy env (() :: path) (.ty (.borrow mutable targets)) ty

/-- Shape stability from initialised leaves: a positive-rank `EnvWrite` whose
leaves are defined (`WriteLeafTy`) preserves every slot's shape.

The strengthened `W-Weak` rule carries the local `ShapeCompatible` premise
needed to preserve shape at the leaf.
-/
theorem EnvWrite.shapePreserved_init {rank : Nat} {env result : Env} {lv : LVal}
    {ty : Ty} :
    0 < rank →
    EnvWrite rank env lv ty result →
    (∀ slot, env.slotAt (LVal.base lv) = some slot →
      WriteLeafTy env (LVal.path lv) slot.ty ty) →
    EnvShapePreserved env result := by
  intro hrank hwrite hsc
  refine EnvWrite.rec
    (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
      0 < rank → WriteLeafTy env₁ path oldTy ty →
        EnvShapePreserved env₁ env₂ ∧ PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun rank env path targets ty result _ =>
      0 < rank →
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty) →
        EnvShapePreserved env result)
    (motive_3 := fun rank env lv ty result _ =>
      0 < rank →
      (∀ slot, env.slotAt (LVal.base lv) = some slot →
        WriteLeafTy env (LVal.path lv) slot.ty ty) →
        EnvShapePreserved env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite hrank hsc
  case strong =>
    intro env old ty hrank0 _hcompat
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty hshape hjoinTy _hrank _hcompat
    exact ⟨EnvShapePreserved.refl env, partialTyJoin_sameShape hshape hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank hcompat
    cases hcompat with
    | box hInner =>
        rcases ih hrank hInner with ⟨hpres, hshape⟩
        exact ⟨hpres, hshape⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank hcompat
    cases hcompat with
    | borrow hTargets =>
        exact ⟨ih (Nat.succ_pos rank) hTargets, PartialTy.sameShape_refl _⟩
  case nil =>
    intro rank env path ty _hrank _hprem
    exact EnvShapePreserved.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank hprem
    exact ih hrank (fun slot hslot => hprem target (by simp) slot hslot)
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites hrank hprem
    have hupd : EnvShapePreserved env updated :=
      ihWrite hrank (fun slot hslot => hprem target (by simp) slot hslot)
    have hrest : EnvShapePreserved env restEnv :=
      ihWrites hrank
        (fun t ht slot hslot => hprem t (List.mem_cons_of_mem _ ht) slot hslot)
    intro x rslot hrslot
    rcases EnvJoin.lifetimesPreserved_left hjoin x rslot hrslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x rslot hrslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hrslot with ⟨_, _, hunionSlot⟩
    rcases hupd x us hus with ⟨es, hes, hShapeUS⟩
    rcases hrest x rs hrs with ⟨es', hes', hShapeRS⟩
    have hesEq : es = es' := Option.some.inj (hes.symm.trans hes')
    subst hesEq
    have hUSRS : PartialTy.sameShape us.ty rs.ty :=
      PartialTy.sameShape_trans (PartialTy.sameShape_symm hShapeUS) hShapeRS
    have hUSc : PartialTy.sameShape us.ty rslot.ty :=
      partialTyUnion_sameShape_of_sameShape hunionSlot hUSRS
    exact ⟨es, hes, PartialTy.sameShape_trans hShapeUS hUSc⟩
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank hprem
    have hsc' : WriteLeafTy env₁ (LVal.path lv) slot.ty ty := hprem slot hslot
    rcases ih hrank hsc' with ⟨hpres, hshape⟩
    exact EnvShapePreserved.update_from_source_slot hpres hslot hshape

/-- Fan-out version of `EnvWrite.shapePreserved_init`: a positive-rank
`WriteBorrowTargets` with initialised leaves preserves every slot's shape. -/
theorem WriteBorrowTargets.shapePreserved_init {rank : Nat} {env result : Env}
    {path : List Unit} {targets : List LVal} {ty : Ty} :
    0 < rank →
    WriteBorrowTargets rank env path targets ty result →
    (∀ t, t ∈ targets → ∀ tslot,
      env.slotAt (LVal.base (prependPath path t)) = some tslot →
      WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty) →
    EnvShapePreserved env result := by
  intro hrank hwrites hsc
  refine WriteBorrowTargets.rec
    (motive_1 := fun rank env₁ path oldTy ty env₂ updatedTy _ =>
      0 < rank → WriteLeafTy env₁ path oldTy ty →
        EnvShapePreserved env₁ env₂ ∧ PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun rank env path targets ty result _ =>
      0 < rank →
      (∀ t, t ∈ targets → ∀ tslot,
        env.slotAt (LVal.base (prependPath path t)) = some tslot →
        WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty) →
        EnvShapePreserved env result)
    (motive_3 := fun rank env lv ty result _ =>
      0 < rank →
      (∀ slot, env.slotAt (LVal.base lv) = some slot →
        WriteLeafTy env (LVal.path lv) slot.ty ty) →
        EnvShapePreserved env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites hrank hsc
  case strong =>
    intro env old ty hrank0 _hcompat
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty hshape hjoinTy _hrank _hcompat
    exact ⟨EnvShapePreserved.refl env, partialTyJoin_sameShape hshape hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank hcompat
    cases hcompat with
    | box hInner =>
        rcases ih hrank hInner with ⟨hpres, hshape⟩
        exact ⟨hpres, hshape⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank hcompat
    cases hcompat with
    | borrow hTargets =>
        exact ⟨ih (Nat.succ_pos rank) hTargets, PartialTy.sameShape_refl _⟩
  case nil =>
    intro rank env path ty _hrank _hprem
    exact EnvShapePreserved.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank hprem
    exact ih hrank (fun slot hslot => hprem target (by simp) slot hslot)
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites hrank hprem
    have hupd : EnvShapePreserved env updated :=
      ihWrite hrank (fun slot hslot => hprem target (by simp) slot hslot)
    have hrest : EnvShapePreserved env restEnv :=
      ihWrites hrank
        (fun t ht slot hslot => hprem t (List.mem_cons_of_mem _ ht) slot hslot)
    intro x rslot hrslot
    rcases EnvJoin.lifetimesPreserved_left hjoin x rslot hrslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x rslot hrslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hrslot with ⟨_, _, hunionSlot⟩
    rcases hupd x us hus with ⟨es, hes, hShapeUS⟩
    rcases hrest x rs hrs with ⟨es', hes', hShapeRS⟩
    have hesEq : es = es' := Option.some.inj (hes.symm.trans hes')
    subst hesEq
    have hUSRS : PartialTy.sameShape us.ty rs.ty :=
      PartialTy.sameShape_trans (PartialTy.sameShape_symm hShapeUS) hShapeRS
    have hUSc : PartialTy.sameShape us.ty rslot.ty :=
      partialTyUnion_sameShape_of_sameShape hunionSlot hUSRS
    exact ⟨es, hes, PartialTy.sameShape_trans hShapeUS hUSc⟩
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank hprem
    have hsc' : WriteLeafTy env₁ (LVal.path lv) slot.ty ty := hprem slot hslot
    rcases ih hrank hsc' with ⟨hpres, hshape⟩
    exact EnvShapePreserved.update_from_source_slot hpres hslot hshape

theorem writeLeafTy_mono {env : Env} {q : List Unit} {a : PartialTy} {rhsTy : Ty}
    (h : WriteLeafTy env q a rhsTy) :
    ∀ {b : PartialTy}, PartialTyStrengthens b a → PartialTy.sameShape b a →
      WriteLeafTy env q b rhsTy := by
  induction h with
  | leaf =>
      intro b _hstr hshape
      cases b with
      | ty bt => exact WriteLeafTy.leaf
      | box _ => simp [PartialTy.sameShape] at hshape
      | undef _ => simp [PartialTy.sameShape] at hshape
  | box _hInner ih =>
      intro b hstr hshape
      cases b with
      | box innerB =>
          exact WriteLeafTy.box (ih (PartialTyStrengthens.box_inv hstr)
            (by simpa [PartialTy.sameShape] using hshape))
      | ty _ => simp [PartialTy.sameShape] at hshape
      | undef _ => simp [PartialTy.sameShape] at hshape
  | borrow hTargets _ih =>
      intro b hstr hshape
      cases b with
      | ty bt =>
          cases bt with
          | borrow mB targetsB =>
              rcases PartialTyStrengthens.from_borrow_inv hstr with ⟨_, heq, hsubset⟩
              cases heq
              exact WriteLeafTy.borrow (fun t ht tslot htslot =>
                hTargets t (hsubset ht) tslot htslot)
          | unit => simp [PartialTy.sameShape, Ty.sameShape] at hshape
          | int => simp [PartialTy.sameShape, Ty.sameShape] at hshape
          | box _ => simp [PartialTy.sameShape, Ty.sameShape] at hshape
          | bool => simp [PartialTy.sameShape, Ty.sameShape] at hshape
      | box _ => simp [PartialTy.sameShape] at hshape
      | undef _ => simp [PartialTy.sameShape] at hshape

/-- For a `List Unit`, appending a `()` at the end equals prepending it (all
elements are `()`, so the list is determined by its length). -/
theorem list_unit_snoc : ∀ (p : List Unit), p ++ [()] = () :: p
  | [] => rfl
  | () :: p => by rw [List.cons_append, list_unit_snoc p]

@[simp] theorem base_prependPath (path : List Unit) (t : LVal) :
    LVal.base (prependPath path t) = LVal.base t := by
  induction path with
  | nil => rfl
  | cons _ p ih => simp [prependPath, LVal.base, ih]

@[simp] theorem path_prependPath (path : List Unit) (t : LVal) :
    LVal.path (prependPath path t) = LVal.path t ++ path := by
  induction path with
  | nil => simp [prependPath]
  | cons u p ih =>
      simp only [prependPath, LVal.path, ih, List.append_assoc, list_unit_snoc]

/-- **Matching lemma (the shape-bridge core).**  If `lv` types to `pt` and its
base slot is `slot`, then descending `slot.ty` along `path lv ++ q` reaches
initialised leaves whenever the continuation `pt`-write does (`WriteLeafTy env q
pt`).  Proven by mutual induction on the `LValTyping`/`LValTargetsTyping`
derivation: `var` is the continuation verbatim; `box`/`borrow` push one more
selector (the `borrow` case turns the per-target typings into `WriteLeafTy.borrow`
obligations); the multi-target `cons` specialises the union continuation to each
member via `writeLeafTy_mono`.  Top-level use takes `q = []` with the trivial
`WriteLeafTy.leaf`, giving `WriteLeafTy env (path lv) slot.ty rhsTy` for any
`lv : .ty _`. -/
theorem writeLeafTy_of_lvalTyping {env : Env} {lv : LVal} {pt : PartialTy}
    {lt : Lifetime} (htyping : LValTyping env lv pt lt) :
    ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
    ∀ (q : List Unit) (rhsTy : Ty),
      WriteLeafTy env q pt rhsTy →
      WriteLeafTy env (LVal.path lv ++ q) slot.ty rhsTy := by
  refine LValTyping.rec
    (motive_1 := fun lv pt _lt _ =>
      ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
      ∀ (q : List Unit) (rhsTy : Ty),
        WriteLeafTy env q pt rhsTy →
        WriteLeafTy env (LVal.path lv ++ q) slot.ty rhsTy)
    (motive_2 := fun targets pt _lt _ =>
      ∀ (q : List Unit) (rhsTy : Ty),
        WriteLeafTy env q pt rhsTy →
        ∀ t, t ∈ targets → ∀ tslot,
          env.slotAt (LVal.base t) = some tslot →
          WriteLeafTy env (LVal.path t ++ q) tslot.ty rhsTy)
    ?var ?box ?borrow ?singleton ?cons htyping
  case var =>
    intro x slot hslot slot' hslot' q rhsTy hleaf
    simp only [LVal.base] at hslot'
    have hEq : slot = slot' := by rw [hslot] at hslot'; exact Option.some.inj hslot'
    subst hEq
    simpa [LVal.base, LVal.path] using hleaf
  case box =>
    intro lv inner lifetime _hlv ih slot hslot q rhsTy hleaf
    rw [LVal.path, List.append_assoc]
    exact ih hslot (() :: q) rhsTy (WriteLeafTy.box hleaf)
  case borrow =>
    intro lv mutable targets borrowLifetime targetLifetime targetTy
      _hborrow _htargets ihBorrow ihTargets slot hslot q rhsTy hleaf
    rw [LVal.path, List.append_assoc]
    refine ihBorrow hslot (() :: q) rhsTy ?_
    refine WriteLeafTy.borrow (fun t ht tslot htslot => ?_)
    have hbase : env.slotAt (LVal.base t) = some tslot := by
      simpa using htslot
    have := ihTargets q rhsTy hleaf t ht tslot hbase
    simpa using this
  case singleton =>
    intro target ty lifetime _htarget ihTarget q rhsTy hleaf t ht tslot htslot
    rw [List.mem_singleton] at ht
    subst ht
    exact ihTarget htslot q rhsTy hleaf
  case cons =>
    intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest hunion _hintersection ihHead ihRest q rhsTy hleaf t ht tslot htslot
    obtain ⟨restFull, hrestFull⟩ := LValTargetsTyping.output_full _hrest
    subst hrestFull
    obtain ⟨unionFull, hunionFull⟩ := PartialTyUnion.ty_ty_full hunion
    subst hunionFull
    have hmemberLeaf : WriteLeafTy env q (.ty headTy) rhsTy := by
      apply writeLeafTy_mono hleaf (PartialTyUnion.left_strengthens hunion)
      show PartialTy.sameShape (.ty headTy) (.ty unionFull)
      simp only [PartialTy.sameShape]
      exact Ty.sameShape_symm (partialTyUnion_ty_left_sameShape hunion)
    have hrestLeaf : WriteLeafTy env q (.ty restFull) rhsTy := by
      apply writeLeafTy_mono hleaf (PartialTyUnion.right_strengthens hunion)
      show PartialTy.sameShape (.ty restFull) (.ty unionFull)
      simp only [PartialTy.sameShape]
      exact Ty.sameShape_symm
        (partialTyUnion_ty_left_sameShape (PartialTyUnion.symm hunion))
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ihHead htslot q rhsTy hmemberLeaf
    · exact ihRest q rhsTy hrestLeaf t ht tslot htslot

theorem EnvStrengthens.trans {a b c : Env}
    (hab : EnvStrengthens a b) (hbc : EnvStrengthens b c) :
    EnvStrengthens a c := by
  intro x
  have h1 := hab x
  have h2 := hbc x
  cases hb : b.slotAt x with
  | none =>
      cases ha : a.slotAt x with
      | none =>
          cases hc : c.slotAt x with
          | none => trivial
          | some sc => rw [hb, hc] at h2; simp at h2
      | some sa => rw [ha, hb] at h1; simp at h1
  | some sb =>
      cases ha : a.slotAt x with
      | none => rw [ha, hb] at h1; simp at h1
      | some sa =>
          cases hc : c.slotAt x with
          | none => rw [hb, hc] at h2; simp at h2
          | some sc =>
              rw [ha, hb] at h1
              rw [hb, hc] at h2
              exact ⟨h1.1.trans h2.1, partialTyStrengthens_trans h1.2 h2.2⟩

theorem EnvStrengthens.update_from_source_slot {source middle : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvStrengthens source middle →
    source.slotAt x = some slot →
    PartialTyStrengthens slot.ty newTy →
    EnvStrengthens source (middle.update x { slot with ty := newTy }) := by
  intro hstr hslot hnew y
  by_cases hy : y = x
  · have hupd : (middle.update x { slot with ty := newTy }).slotAt y
        = some { slot with ty := newTy } := by rw [hy]; simp [Env.update]
    have hsy : source.slotAt y = some slot := by rw [hy]; exact hslot
    rw [hsy, hupd]
    exact ⟨rfl, hnew⟩
  · have hupd : (middle.update x { slot with ty := newTy }).slotAt y
        = middle.slotAt y := by simp [Env.update, hy]
    rw [hupd]
    exact hstr y

/-- A positive-rank `Definition 3.23` write only makes slots more defined:
`env ≤ result` (result strengthens env — borrow target lists only grow).  This is
the growth characterization complementing `EnvWrite.shapePreserved`. -/
theorem EnvWrite.envStrengthens {rank : Nat} {env result : Env} {lv : LVal}
    {ty : Ty} :
    0 < rank →
    EnvWrite rank env lv ty result →
    EnvStrengthens env result := by
  intro hrank hwrite
  refine EnvWrite.rec
    (motive_1 := fun rank env₁ _path oldTy _ty env₂ updatedTy _ =>
      0 < rank → EnvStrengthens env₁ env₂ ∧ PartialTyStrengthens oldTy updatedTy)
    (motive_2 := fun rank env _path _targets _ty result _ =>
      0 < rank → EnvStrengthens env result)
    (motive_3 := fun rank env _lv _ty result _ =>
      0 < rank → EnvStrengthens env result)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite hrank
  case strong =>
    intro env old ty hrank0
    exact absurd hrank0 (Nat.lt_irrefl 0)
  case weak =>
    intro env rank old joined ty _hshape hjoinTy _hrank
    exact ⟨EnvStrengthens.refl env, PartialTyUnion.left_strengthens hjoinTy⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupdate ih hrank
    rcases ih hrank with ⟨hpres, hinner⟩
    exact ⟨hpres, PartialTyStrengthens.box hinner⟩
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih _hrank
    exact ⟨ih (Nat.succ_pos rank), PartialTyStrengthens.reflex⟩
  case nil =>
    intro rank env path ty _hrank
    exact EnvStrengthens.refl env
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih hrank
    exact ih hrank
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite _ihWrites hrank
    have hupd : EnvStrengthens env updated := ihWrite hrank
    have hUpdResult : EnvStrengthens updated result := hjoin.1 (by simp)
    exact EnvStrengthens.trans hupd hUpdResult
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih hrank
    rcases ih hrank with ⟨hpres, hstr⟩
    exact EnvStrengthens.update_from_source_slot hpres hslot hstr

/-- Every borrow target appearing in a result slot originates either from the
same variable's slot in the source env, or from the right-hand type written.
This is the per-slot growth bound (piece (A) of the coherence closure): writes
only grow borrow target lists by the rhs's contained-borrow targets. -/
def BorrowTargetOrigin
    (env : Env) (rhsTy : Ty) (x : Name) (mutable : Bool) (t : LVal) : Prop :=
  (∃ slot T, env.slotAt x = some slot ∧
    PartialTyContains slot.ty (.borrow mutable T) ∧ t ∈ T) ∨
  (∃ T, PartialTyContains (.ty rhsTy) (.borrow mutable T) ∧ t ∈ T)

/-- Type-level analogue of `BorrowTargetOrigin` used for the `UpdateAtPath`
motive: a borrow target in the updated type comes from the old type or the rhs. -/
def TypeBorrowOrigin
    (oldTy : PartialTy) (rhsTy : Ty) (mutable : Bool) (t : LVal) : Prop :=
  (∃ T, PartialTyContains oldTy (.borrow mutable T) ∧ t ∈ T) ∨
  (∃ T, PartialTyContains (.ty rhsTy) (.borrow mutable T) ∧ t ∈ T)

theorem EnvWrite.borrowTargetOrigin_all {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} :
    EnvWrite rank env lv rhsTy result →
    ∀ x slot m T, result.slotAt x = some slot →
      PartialTyContains slot.ty (.borrow m T) →
      ∀ t, t ∈ T → BorrowTargetOrigin env rhsTy x m t := by
  intro hwrite
  refine EnvWrite.rec
    (motive_1 := fun _rank env₁ _path oldTy ty env₂ updatedTy _ =>
      (∀ m T, PartialTyContains updatedTy (.borrow m T) →
        ∀ t, t ∈ T → TypeBorrowOrigin oldTy ty m t) ∧
      (∀ x slot m T, env₂.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env₁ ty x m t))
    (motive_2 := fun _rank env _path _targets ty result _ =>
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x m t)
    (motive_3 := fun _rank env _lv ty result _ =>
      ∀ x slot m T, result.slotAt x = some slot →
        PartialTyContains slot.ty (.borrow m T) →
        ∀ t, t ∈ T → BorrowTargetOrigin env ty x m t)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrite
  case strong =>
    intro env old ty
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      exact Or.inr ⟨T, hcontains, ht⟩
    · intro x slot m T hslot hcontains t ht
      exact Or.inl ⟨slot, T, hslot, hcontains, ht⟩
  case weak =>
    intro env rank old joined ty _hshape hjoin
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      rcases PartialTyUnion.contained_borrow_member hjoin hcontains ht with
        ⟨Tl, hl, htl⟩ | ⟨Tr, hr, htr⟩
      · exact Or.inl ⟨Tl, hl, htl⟩
      · exact Or.inr ⟨Tr, hr, htr⟩
    · intro x slot m T hslot hcontains t ht
      exact Or.inl ⟨slot, T, hslot, hcontains, ht⟩
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hupd ih
    rcases ih with ⟨ihType, ihEnv⟩
    refine ⟨?_, ihEnv⟩
    intro m T hcontains t ht
    cases hcontains with
    | box hinner =>
        rcases ihType m T hinner t ht with ⟨T₀, hc₀, ht₀⟩ | hrhs
        · exact Or.inl ⟨T₀, PartialTyContains.box hc₀, ht₀⟩
        · exact Or.inr hrhs
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites ih
    refine ⟨?_, ?_⟩
    · intro m T hcontains t ht
      exact Or.inl ⟨T, hcontains, ht⟩
    · exact ih
  case nil =>
    intro rank env path ty x slot m T hslot hcontains t ht
    exact Or.inl ⟨slot, T, hslot, hcontains, ht⟩
  case singleton =>
    intro rank env updated path target ty _hwrite _htyped ih
    exact ih
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite _htyped _hwrites hjoin ihWrite ihWrites x slot m T hslot hcontains t ht
    rcases EnvJoin.lifetimesPreserved_left hjoin x slot hslot with ⟨us, hus, _⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x slot hslot with ⟨rs, hrs, _⟩
    rcases EnvJoin.slot_union hjoin hus hrs hslot with ⟨_, _, hunion⟩
    rcases PartialTyUnion.contained_borrow_member hunion hcontains ht with
      ⟨Tl, hl, htl⟩ | ⟨Tr, hr, htr⟩
    · exact ihWrite x us m Tl hus hl t htl
    · exact ihWrites x rs m Tr hrs hr t htr
  case intro =>
    intro rank env₁ env₂ lv slot ty updatedTy hslot _hupdate ih
      x rslot m T hrslot hcontains t ht
    rcases ih with ⟨ihType, ihEnv⟩
    by_cases hx : x = LVal.base lv
    · have hreq : rslot = { slot with ty := updatedTy } := by
        have hlk : (env₂.update (LVal.base lv) { slot with ty := updatedTy }).slotAt x
            = some { slot with ty := updatedTy } := by rw [hx]; simp [Env.update]
        rw [hlk] at hrslot; exact (Option.some.inj hrslot).symm
      rw [hreq] at hcontains
      rcases ihType m T hcontains t ht with ⟨T₀, hc₀, ht₀⟩ | hrhs
      · exact Or.inl ⟨slot, T₀, by rw [hx]; exact hslot, hc₀, ht₀⟩
      · exact Or.inr hrhs
    · have hru : (env₂.update (LVal.base lv) { slot with ty := updatedTy }).slotAt x
          = env₂.slotAt x := by simp [Env.update, hx]
      rw [hru] at hrslot
      exact ihEnv x rslot m T hrslot hcontains t ht

theorem EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all {rank : Nat}
    {env result : Env} {lv : LVal} {rhsTy : Ty} {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    LinearizedBy φ env →
    EnvWriteRhsBorrowTargetsBelow φ result rhsTy →
    LinearizedBy φ result := by
  intro hwrite hlin hbelow x slot hslot v hv
  rcases partialTy_vars_mem_contains v hv with
    ⟨mutable, targets, hcontains, target, htarget, hbase⟩
  rcases EnvWrite.borrowTargetOrigin_all hwrite x slot mutable targets
      hslot hcontains target htarget with
    hfromOld | hfromRhs
  · rcases hfromOld with
      ⟨oldSlot, oldTargets, holdSlot, holdContains, holdTarget⟩
    have hvOld : v ∈ PartialTy.vars oldSlot.ty := by
      exact mem_partialTy_vars_iff.mpr
        ⟨mutable, oldTargets, target, holdContains, holdTarget, hbase⟩
    exact hlin x oldSlot holdSlot v hvOld
  · have htargetBelow : φ (LVal.base target) < φ x :=
      hbelow.1 x slot mutable targets target hslot hcontains htarget
        (by
          rcases hfromRhs with ⟨rhsTargets, hrhsContains, hrhsTarget⟩
          exact ⟨mutable, rhsTargets, hrhsContains, hrhsTarget⟩)
    simpa [hbase] using htargetBelow

theorem EnvWrite.shapeMap {rank : Nat} {env result : Env} {lv : LVal} {ty : Ty}
    (hrank : 0 < rank) (hwrite : EnvWrite rank env lv ty result)
    (hsc : ∀ slot, env.slotAt (LVal.base lv) = some slot →
      WriteShapeCompat env (LVal.path lv) slot.ty ty) :
    ∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty := by
  intro x sE hsE
  have hstrength := EnvWrite.envStrengthens hrank hwrite x
  have hshapePres := EnvWrite.shapePreserved hrank hwrite hsc
  rw [hsE] at hstrength
  cases hresult : result.slotAt x with
  | none => rw [hresult] at hstrength; exact absurd hstrength (by simp)
  | some sR =>
      rw [hresult] at hstrength
      rcases hshapePres x sR hresult with ⟨sE', hsE', hshape⟩
      have hEq : sE' = sE := Option.some.inj (hsE'.symm.trans hsE)
      subst hEq
      exact ⟨sR, rfl, hshape, hstrength.2⟩

theorem EnvJoin.contained_borrow_member {left right join : Env} {x : Name}
    {joinSlot : EnvSlot} {mutable : Bool} {targets : List LVal}
    {target : LVal} :
    EnvJoin left right join →
    join.slotAt x = some joinSlot →
    PartialTyContains joinSlot.ty (.borrow mutable targets) →
    target ∈ targets →
    (∃ leftSlot leftTargets,
      left.slotAt x = some leftSlot ∧
      PartialTyContains leftSlot.ty (.borrow mutable leftTargets) ∧
      target ∈ leftTargets) ∨
    (∃ rightSlot rightTargets,
      right.slotAt x = some rightSlot ∧
      PartialTyContains rightSlot.ty (.borrow mutable rightTargets) ∧
      target ∈ rightTargets) := by
  intro hjoin hjoinSlot hcontains htarget
  rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
    ⟨leftSlot, hleftSlot, _hleftLifetime⟩
  rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
    ⟨rightSlot, hrightSlot, _hrightLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨_hleftLife, _hrightLife, hunion⟩
  rcases PartialTyUnion.contained_borrow_member hunion hcontains htarget with
    hleft | hright
  · rcases hleft with ⟨leftTargets, hcontainsLeft, htargetLeft⟩
    exact Or.inl ⟨leftSlot, leftTargets, hleftSlot, hcontainsLeft, htargetLeft⟩
  · rcases hright with ⟨rightTargets, hcontainsRight, htargetRight⟩
    exact Or.inr ⟨rightSlot, rightTargets, hrightSlot, hcontainsRight, htargetRight⟩

theorem BorrowTargetsWellFormedInSlot.of_partialTyUnion {env : Env}
    {left right union : PartialTy} {lifetime : Lifetime} :
    PartialTyUnion left right union →
    (∀ {mutable targets},
      PartialTyContains left (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot env lifetime targets) →
    (∀ {mutable targets},
      PartialTyContains right (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot env lifetime targets) →
    ∀ {mutable targets},
      PartialTyContains union (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot env lifetime targets := by
  -- With the borrow invariant stated per target (Definition 4.8(i)), the union
  -- case is immediate: rule W-Bor merges the target lists of `left` and `right`,
  -- so every target of the union's borrow is a target of `left`'s or `right`'s
  -- borrow, and that side's per-target well-formedness supplies its typing,
  -- lifetime bound and base-slot survival directly.  No joint target-list typing
  -- of the merged list is needed (it need not exist; see the note on
  -- `BorrowTargetsWellFormedInSlot`).
  intro hunion hleft hright mutable targets hcontains target htarget
  rcases PartialTyUnion.contained_borrow_member hunion hcontains htarget with
    hfromLeft | hfromRight
  · rcases hfromLeft with ⟨leftTargets, hcontainsLeft, htargetLeft⟩
    exact hleft hcontainsLeft target htargetLeft
  · rcases hfromRight with ⟨rightTargets, hcontainsRight, htargetRight⟩
    exact hright hcontainsRight target htargetRight

theorem PartialTyBorrowsWellFormedInSlot.of_partialTyUnion {env : Env}
    {left right union : PartialTy} {lifetime : Lifetime} :
    PartialTyUnion left right union →
    PartialTyBorrowsWellFormedInSlot env lifetime left →
    PartialTyBorrowsWellFormedInSlot env lifetime right →
    PartialTyBorrowsWellFormedInSlot env lifetime union := by
  intro hunion hleft hright mutable targets hcontains
  exact BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion hleft hright hcontains

/--
Join closure for contained borrows, factored through the actual target-transport
obligations.

`EnvJoin.contained_borrow_member` shows that every target in a joined borrow
comes from one of the branch borrows.  This lemma packages the remaining work:
transporting that branch target's per-slot well-formedness into the joined
environment and joined slot lifetime.
-/
theorem EnvJoin.preserves_containedBorrowsWellFormed_of_target_transport
    {left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    (∀ x joinSlot leftSlot mutable targets,
      join.slotAt x = some joinSlot →
      left.slotAt x = some leftSlot →
      PartialTyContains leftSlot.ty (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot left leftSlot.lifetime targets →
      BorrowTargetsWellFormedInSlot join joinSlot.lifetime targets) →
    (∀ x joinSlot rightSlot mutable targets,
      join.slotAt x = some joinSlot →
      right.slotAt x = some rightSlot →
      PartialTyContains rightSlot.ty (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot right rightSlot.lifetime targets →
      BorrowTargetsWellFormedInSlot join joinSlot.lifetime targets) →
    ContainedBorrowsWellFormed join := by
  intro hjoin hleft hright hleftTransport hrightTransport
    x joinSlot mutable targets hjoinSlot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq : containedSlot = joinSlot :=
    Option.some.inj (hcontainedSlot.symm.trans hjoinSlot)
  have hcontainsJoin : PartialTyContains joinSlot.ty (.borrow mutable targets) := by
    simpa [hcontainedSlotEq] using hcontainsTy
  intro target htarget
  rcases EnvJoin.contained_borrow_member hjoin hjoinSlot hcontainsJoin htarget with
    hfromLeft | hfromRight
  · rcases hfromLeft with
      ⟨leftSlot, leftTargets, hleftSlot, hcontainsLeft, htargetLeft⟩
    exact hleftTransport x joinSlot leftSlot mutable leftTargets
      hjoinSlot hleftSlot hcontainsLeft
      (hleft x leftSlot mutable leftTargets hleftSlot
        ⟨leftSlot, hleftSlot, hcontainsLeft⟩)
      target htargetLeft
  · rcases hfromRight with
      ⟨rightSlot, rightTargets, hrightSlot, hcontainsRight, htargetRight⟩
    exact hrightTransport x joinSlot rightSlot mutable rightTargets
      hjoinSlot hrightSlot hcontainsRight
      (hright x rightSlot mutable rightTargets hrightSlot
        ⟨rightSlot, hrightSlot, hcontainsRight⟩)
      target htargetRight

/--
Write closure for contained borrows, factored through old-slot and RHS target
transport.

`EnvWrite.borrowTargetOrigin_all` proves that every target in a result borrow
originates either in the same source slot or in the RHS type.  This theorem
turns those origins into contained-borrow well-formedness once callers supply
the two transport facts appropriate for the particular write rule.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_of_target_transport
    {rank : Nat} {env result : Env} {lv : LVal} {rhsTy : Ty} :
    EnvWrite rank env lv rhsTy result →
    ContainedBorrowsWellFormed env →
    (∀ x resultSlot sourceSlot mutable targets,
      result.slotAt x = some resultSlot →
      env.slotAt x = some sourceSlot →
      PartialTyContains sourceSlot.ty (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot env sourceSlot.lifetime targets →
      BorrowTargetsWellFormedInSlot result resultSlot.lifetime targets) →
    (∀ x resultSlot mutable targets,
      result.slotAt x = some resultSlot →
      PartialTyContains (.ty rhsTy) (.borrow mutable targets) →
      BorrowTargetsWellFormedInSlot result resultSlot.lifetime targets) →
    ContainedBorrowsWellFormed result := by
  intro hwrite hcontained holdTransport hrhsTransport
    x resultSlot mutable targets hresultSlot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq : containedSlot = resultSlot :=
    Option.some.inj (hcontainedSlot.symm.trans hresultSlot)
  have hcontainsResult :
      PartialTyContains resultSlot.ty (.borrow mutable targets) := by
    simpa [hcontainedSlotEq] using hcontainsTy
  intro target htarget
  rcases EnvWrite.borrowTargetOrigin_all hwrite x resultSlot mutable targets
      hresultSlot hcontainsResult target htarget with
    hfromOld | hfromRhs
  · rcases hfromOld with
      ⟨sourceSlot, sourceTargets, hsourceSlot, hcontainsSource, htargetSource⟩
    exact holdTransport x resultSlot sourceSlot mutable sourceTargets
      hresultSlot hsourceSlot hcontainsSource
      (hcontained x sourceSlot mutable sourceTargets hsourceSlot
        ⟨sourceSlot, hsourceSlot, hcontainsSource⟩)
      target htargetSource
  · rcases hfromRhs with ⟨rhsTargets, hcontainsRhs, htargetRhs⟩
    exact hrhsTransport x resultSlot mutable rhsTargets
      hresultSlot hcontainsRhs target htargetRhs

theorem safeStrengthening {store : ProgramStore} {env : Env}
    {lifetime : Lifetime} {left right : Ty} {value : Value} :
    WellFormedEnv env lifetime →
    store ∼ₛ env →
    PartialTyStrengthens (.ty left) (.ty right) →
    ValidValue store value left →
    ValidValue store value right := by
  intro _hwellFormed _hsafe hstrength hvalid
  exact validPartialValue_strengthen_sameShape hvalid hstrength
    (by simpa [PartialTy.sameShape] using ty_sameShape_of_strengthens hstrength)

/--
Lemma 9.7, Value Typing.

Typing a runtime value is exactly `T-Const`, so it leaves the environment
unchanged.
-/
theorem valueTyping_environment_eq {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    TermTyping env₁ typing lifetime (.val value) ty env₂ →
    env₁ = env₂ := by
  intro htyping
  cases htyping
  rfl

/-- Value typing is functional for a fixed store typing and runtime value. -/
theorem valueTyping_deterministic {typing : StoreTyping} {value : Value}
    {left right : Ty} :
    ValueTyping typing value left →
    ValueTyping typing value right →
    left = right := by
  intro hleft hright
  exact ValueTyping.deterministic hleft hright

/-- Lemma 9.7 lifted to singleton term lists. -/
theorem termListTyping_singleton_value_environment_eq {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    TermListTyping env₁ typing lifetime [.val value] ty env₂ →
    env₁ = env₂ := by
  intro htyping
  cases htyping with
  | singleton hterm =>
      exact valueTyping_environment_eq hterm
  | cons _hterm hrest =>
      cases hrest

/-- `T-Const` inversion for singleton value term lists. -/
theorem termListTyping_singleton_value_valueTyping {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    TermListTyping env₁ typing lifetime [.val value] ty env₂ →
    ValueTyping typing value ty := by
  intro htyping
  cases htyping with
  | singleton hterm =>
      cases hterm with
      | const hvalueTyping =>
          exact hvalueTyping
  | cons _hterm hrest =>
      cases hrest

/--
Block value typing consequence used by the `R-BlockB` preservation cases:
a singleton value block outputs exactly `drop(Γ, m)`.
-/
theorem blockValueTyping_output_eq {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value : Value} {ty : Ty} :
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    env' = env.dropLifetime blockLifetime := by
  intro htyping
  cases htyping with
  | block _hblockChild hterms _hwellFormed hdrop =>
      have henv₂ := termListTyping_singleton_value_environment_eq hterms
      rw [henv₂]
      exact hdrop

/-- `T-Const` inversion for singleton value blocks. -/
theorem blockValueTyping_valueTyping {env env' : Env} {typing : StoreTyping}
    {lifetime blockLifetime : Lifetime} {value : Value} {ty : Ty} :
    TermTyping env typing lifetime (.block blockLifetime [.val value]) ty env' →
    ValueTyping typing value ty := by
  intro htyping
  cases htyping with
  | block _hblockChild hterms _hwellFormed _hdrop =>
      exact termListTyping_singleton_value_valueTyping hterms

/--
Lemma 9.9 support: if the store typing is valid for a terminal value and the
same value has type `T` under `σ`, then the runtime value safely abstracts `T`.
-/
theorem validStoreTyping_value {store : ProgramStore} {typing : StoreTyping}
    {value : Value} {ty : Ty} :
    ValidStoreTyping store (.val value) typing →
    ValueTyping typing value ty →
    ValidValue store value ty := by
  intro hvalidStoreTyping hvalueTyping
  rcases hvalidStoreTyping value (by simp [termValues]) with
    ⟨storedTy, hstoredTyping, hvalidValue⟩
  have hty : storedTy = ty :=
    valueTyping_deterministic hstoredTyping hvalueTyping
  subst hty
  exact hvalidValue

/-- Lemma 9.9, value case. -/
theorem valuePreservation_value {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidStoreTyping store (.val value) typing →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidValue store value ty ∧ env₂ = env := by
  intro hvalidStoreTyping htyping
  cases htyping with
  | const hvalueTyping =>
      exact ⟨validStoreTyping_value hvalidStoreTyping hvalueTyping, rfl⟩

/--
Lemma 4.11, zero-step terminal preservation.

This is the base case of Preservation for an already terminal value.
-/
theorem preservation_refl_value {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidState store (.val value) ∧ store ∼ₛ env₂ ∧ ValidValue store value ty := by
  intro hvalidState hvalidStoreTyping hsafe htyping
  rcases valuePreservation_value hvalidStoreTyping htyping with
    ⟨hvalidValue, henv⟩
  subst henv
  exact ⟨hvalidState, hsafe, hvalidValue⟩

/--
Lemma 4.11, zero-step terminal preservation for the mechanised runtime package.
-/
theorem preservation_refl_runtime_value {store : ProgramStore} {env env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    ValidRuntimeState store (.val value) ∧ store ∼ₛ env₂ ∧
      ValidValue store value ty := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping
  rcases preservation_refl_value hvalidRuntime.1 hvalidStoreTyping hsafe htyping with
    ⟨hvalidState, hsafe₂, hvalidValue⟩
  exact ⟨⟨hvalidState,
      ValidRuntimeState.storeOwnersAllocated hvalidRuntime,
      ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime,
      ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime,
      ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime⟩,
    hsafe₂, hvalidValue⟩

/--
Lemma 4.11, multistep terminal preservation when the initial term is already a
value.  A value cannot step, so every such multistep derivation is reflexive.
-/
theorem preservation_multistep_runtime_value {store finalStore : ProgramStore}
    {env env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) →
    ValidStoreTyping store (.val value) typing →
    store ∼ₛ env →
    TermTyping env typing lifetime (.val value) ty env₂ →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hvalidRuntime hvalidStoreTyping hsafe htyping hmulti
  rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact preservation_refl_runtime_value hvalidRuntime hvalidStoreTyping hsafe htyping

/--
General value-tail composition for Lemma 4.11 proofs.

Once a proof has established preservation for a step whose result is already a
runtime value, any remaining multistep tail is necessarily reflexive.
-/
theorem preservation_value_tail_runtime {store finalStore : ProgramStore}
    {env : Env} {lifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.val value) ∧ store ∼ₛ env ∧ ValidValue store value ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env ∧
      ValidValue finalStore finalValue ty := by
  intro hpreserved hmulti
  rcases multistep_value_inv hmulti with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact hpreserved

/--
General one-redex-to-value multistep preservation pattern.

This factors the common proof shape for redexes such as `box v`, `let mut x = v`,
and `{v}ᵐ`: the initial term is not terminal, every first step from that redex
produces a value, and preservation for that first step composes with the
reflexive value tail.
-/
theorem preservation_multistep_of_step_to_value
    {store finalStore : ProgramStore} {lifetime : Lifetime}
    {term : Term} {finalValue : Value}
    {Result : ProgramStore → Value → Prop} :
    ¬ Terminal term →
    (∀ store' term',
      Step store lifetime term store' term' →
      ∃ value, term' = .val value) →
    (∀ store' value,
      Step store lifetime term store' (.val value) →
      Result store' value) →
    (∀ store' value finalStore finalValue,
      Result store' value →
      MultiStep store' lifetime (.val value) finalStore (.val finalValue) →
      Result finalStore finalValue) →
    MultiStep store lifetime term finalStore (.val finalValue) →
    Result finalStore finalValue := by
  intro hnotTerminal hstepValue hstepPreserve htail hmulti
  cases hmulti with
  | refl =>
      exact False.elim (hnotTerminal (value_terminal finalValue))
  | trans hstep hrest =>
      rcases hstepValue _ _ hstep with ⟨value, hterm⟩
      subst hterm
      exact htail _ _ _ _ (hstepPreserve _ _ hstep) hrest

/--
Specialized preservation combinator for redexes whose first step is already a
runtime value.

This is the common Lemma 4.11 shape after the rule-specific one-step
preservation argument has been factored out.
-/
theorem preservation_runtime_multistep_of_step_to_value
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {term : Term} {finalValue : Value} {ty : Ty} :
    ¬ Terminal term →
    (∀ store' term',
      Step store lifetime term store' term' →
      ∃ value, term' = .val value) →
    (∀ store' value,
      Step store lifetime term store' (.val value) →
      ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env ∧
        ValidValue store' value ty) →
    MultiStep store lifetime term finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env ∧
      ValidValue finalStore finalValue ty := by
  intro hnotTerminal hstepValue hstepPreserve hmulti
  exact preservation_multistep_of_step_to_value
    (Result := fun store' value =>
      ValidRuntimeState store' (.val value) ∧ store' ∼ₛ env ∧
        ValidValue store' value ty)
    hnotTerminal hstepValue hstepPreserve
    (by
      intro _store' _value _finalStore _finalValue hpreserved htail
      exact preservation_value_tail_runtime hpreserved htail)
    hmulti

/--
Lemma 9.3, Location, factored through the part used by progress and read
preservation: a well-typed lval denotes an allocated store slot whose runtime
contents are safely abstracted by the lval's partial type.

The paper additionally writes the reached slot with the same lifetime as the
typing judgment.  Our store keeps allocation lifetimes on runtime slots, while
box contents are represented only through the `Box` type in `Γ`; the progress
and preservation arguments need the allocated slot and value abstraction below.
-/
def LValLocationAbstraction
    (store : ProgramStore) (lv : LVal) (ty : PartialTy) : Prop :=
  ∃ location slot,
    store.loc lv = some location ∧
    store.slotAt location = some slot ∧
    ValidPartialValue store slot.value ty

/--
The readable part of Lemma 9.3.  Undefined shadow types record declared but
moved-out storage; the operational `read`/`copy` premises only need a concrete
location for full and boxed partial types.
-/
def LValDefinedLocationAbstraction
    (store : ProgramStore) (lv : LVal) : PartialTy → Prop
  | .undef _ => True
  | ty => LValLocationAbstraction store lv ty

/-- Lemma 9.3, variable case. -/
theorem location_var {store : ProgramStore} {env : Env}
    {x : Name} {slot : EnvSlot} :
    store ∼ₛ env →
    env.slotAt x = some slot →
    LValLocationAbstraction store (.var x) slot.ty := by
  intro hsafe henv
  rcases hsafe.2 x slot henv with ⟨value, hstore, hvalid⟩
  exact ⟨.var x, StoreSlot.mk value slot.lifetime, by
      simp [ProgramStore.loc],
    by
      simpa [VariableProjection] using hstore,
    hvalid⟩

/-- Lemma 9.3, owned-box dereference case. -/
theorem location_box {store : ProgramStore} {lv : LVal} {inner : PartialTy} :
    LValLocationAbstraction store lv (.box inner) →
    LValLocationAbstraction store (.deref lv) inner := by
  intro hlocation
  rcases hlocation with ⟨source, sourceSlot, hloc, hslot, hvalid⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hvalid with
  | box htarget hinner =>
      exact ⟨_, _, by
          simp [ProgramStore.loc, hloc, hslot],
        htarget,
        hinner⟩

theorem validPartialValue_full_value {store : ProgramStore}
    {partialValue : PartialValue} {ty : Ty} :
    ValidPartialValue store partialValue (.ty ty) →
    ∃ value, partialValue = .value value ∧ ValidValue store value ty := by
  intro hvalid
  cases hvalid with
  | unit =>
      exact ⟨.unit, rfl, ValidPartialValue.unit⟩
  | int =>
      exact ⟨.int _, rfl, ValidPartialValue.int⟩
  | bool =>
      exact ⟨.bool _, rfl, ValidPartialValue.bool⟩
  | borrow hmem hloc =>
      exact ⟨.ref { location := _, owner := false }, rfl,
        ValidPartialValue.borrow hmem hloc⟩
  | boxFull hslot hinner =>
      exact ⟨.ref { location := _, owner := true }, rfl,
        ValidPartialValue.boxFull hslot hinner⟩

/--
Lemma 9.3, Location.

This packages the variable, owned-box, and borrowed-reference cases into one
recursive theorem over `LValTyping`.  Undefined shadow types are intentionally
excluded from the concrete-location conclusion, since they are not readable
runtime values.
-/
theorem lvalTyping_defined_location {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv ty lifetime →
    LValDefinedLocationAbstraction store lv ty := by
  intro hwellFormed hsafe htyping
  refine LValTyping.rec
    (motive_1 := fun lv ty _ _ => LValDefinedLocationAbstraction store lv ty)
    (motive_2 := fun targets unionTy _ _ =>
      ∀ target,
        target ∈ targets →
        ∃ ty,
          LValLocationAbstraction store target (.ty ty) ∧
          PartialTyStrengthens (.ty ty) unionTy)
    ?var ?box ?borrow ?singleton ?cons htyping
  · intro x slot hslot
    rcases slot with ⟨slotTy, slotLifetime⟩
    cases slotTy <;> simp [LValDefinedLocationAbstraction]
    · exact location_var (store := store) (env := env) hsafe hslot
    · exact location_var (store := store) (env := env) hsafe hslot
  · intro _lv inner _lifetime _htyping ih
    cases inner <;> simp [LValDefinedLocationAbstraction]
    · exact location_box ih
    · exact location_box ih
  · intro lv mutable targets _borrowLifetime _targetLifetime targetTy
      _hborrow _htargets ihBorrow ihTargets
    cases targetTy with
    | ty finalTy =>
        simp [LValDefinedLocationAbstraction]
        rcases ihBorrow with
          ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hvalidBorrow with
        | borrow hmem htargetLocFromBorrow =>
            rcases ihTargets _ hmem with
              ⟨selectedTy, hselectedLocation, hstrength⟩
            rcases hselectedLocation with
              ⟨selectedLocation, selectedSlot, hselectedLoc,
                hselectedSlot, hselectedValid⟩
            rcases validPartialValue_full_value hselectedValid with
              ⟨selectedValue, hselectedValue, hvalidSelectedValue⟩
            exact ⟨selectedLocation, selectedSlot, by
                simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                simpa [hselectedLoc] using htargetLocFromBorrow.symm,
              hselectedSlot,
              by
                simpa [hselectedValue, ValidValue] using
                  safeStrengthening hwellFormed hsafe hstrength hvalidSelectedValue⟩
    | box _inner =>
        rcases ihBorrow with
          ⟨source, sourceSlot, _hsourceLoc, _hsourceSlot, hvalidBorrow⟩
        rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
        cases hvalidBorrow with
        | borrow hmem _htargetLocFromBorrow =>
            rcases ihTargets _ hmem with
              ⟨selectedTy, _hselectedLocation, hstrength⟩
            cases hstrength
    | undef _shape =>
        simp [LValDefinedLocationAbstraction]
  · intro target ty _lifetime _htarget ihTarget selected hmem
    simp at hmem
    subst hmem
    exact ⟨ty, ihTarget, PartialTyStrengthens.reflex⟩
  · intro target rest headTy _headLifetime _restLifetime _lifetime _restTy unionTy
      _hhead _hrest hunion _hintersection ihHead ihRest selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ⟨headTy, ihHead, PartialTyUnion.left_strengthens hunion⟩
    · rcases ihRest selected hselected with
        ⟨selectedTy, hlocation, hstrength⟩
      exact ⟨selectedTy, hlocation,
        partialTyStrengthens_trans hstrength
          (PartialTyUnion.right_strengthens hunion)⟩

/-- A well-typed lval denotes allocated storage, even when its type is undefined. -/
def LValAllocatedLocation (store : ProgramStore) (lv : LVal) : Prop :=
  ∃ location slot, store.loc lv = some location ∧ store.slotAt location = some slot

theorem lvalTyping_allocated_location {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv ty lifetime →
    LValAllocatedLocation store lv := by
  intro hwellFormed hsafe htyping
  refine LValTyping.rec
    (motive_1 := fun lv _ _ _ => LValAllocatedLocation store lv)
    (motive_2 := fun targets _ _ _ =>
      ∀ target, target ∈ targets → LValAllocatedLocation store target)
    ?var ?box ?borrow ?singleton ?cons htyping
  · intro x slot hslot
    rcases location_var (store := store) (env := env) hsafe hslot with
      ⟨location, runtimeSlot, hloc, hslotRuntime, _hvalid⟩
    exact ⟨location, runtimeSlot, hloc, hslotRuntime⟩
  · intro _lv _inner _lifetime hbox _ih
    rcases location_box (lvalTyping_defined_location hwellFormed hsafe hbox) with
      ⟨location, slot, hloc, hslot, _hvalid⟩
    exact ⟨location, slot, hloc, hslot⟩
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      hborrow _htargets _ihBorrow ihTargets
    rcases lvalTyping_defined_location hwellFormed hsafe hborrow with
      ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
    rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
    cases hvalidBorrow with
    | borrow hmem htargetLocFromBorrow =>
        rcases ihTargets _ hmem with
          ⟨targetLocation, targetSlot, htargetLoc, htargetSlot⟩
        exact ⟨targetLocation, targetSlot, by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            simpa [htargetLoc] using htargetLocFromBorrow.symm,
          htargetSlot⟩
  · intro _target _ty _lifetime _htarget ihTarget selected hmem
    simp at hmem
    subst hmem
    exact ihTarget
  · intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
      _hhead _hrest _hunion _hintersection ihHead ihRest selected hmem
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ihHead
    · exact ihRest selected hselected

/-- Lemma 9.3 operational corollary: locating an lval makes `write` defined. -/
theorem write_defined_of_location {store : ProgramStore} {lv : LVal}
    {ty : PartialTy} {value : PartialValue} :
    LValLocationAbstraction store lv ty →
    ∃ store', store.write lv value = some store' := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot, _hvalid⟩
  exact ⟨store.update location { slot with value := value }, by
    simp [ProgramStore.write, hloc, hslot]⟩

/-- A successful runtime write updates exactly the location selected by `loc`. -/
theorem write_eq_update_of_read {store store' : ProgramStore}
    {lv : LVal} {oldSlot : StoreSlot} {value : PartialValue} :
    store.read lv = some oldSlot →
    store.write lv value = some store' →
    ∃ location,
      store.loc lv = some location ∧
        store.slotAt location = some oldSlot ∧
        store' = store.update location { oldSlot with value := value } := by
  intro hread hwrite
  unfold ProgramStore.read at hread
  unfold ProgramStore.write at hwrite
  cases hloc : store.loc lv with
  | none =>
      simp [hloc] at hread
  | some location =>
      cases hslot : store.slotAt location with
      | none =>
          simp [hloc, hslot] at hread
      | some runtimeSlot =>
          have holdSlot : oldSlot = runtimeSlot := by
            simpa [hloc, hslot] using hread.symm
          have hstore' :
              store' =
                store.update location { runtimeSlot with value := value } := by
            simpa [hloc, hslot] using hwrite.symm
          subst holdSlot
          subst hstore'
          refine ⟨location, ?_, ?_, rfl⟩
          · rfl
          · exact hslot

theorem read_defined_of_allocated {store : ProgramStore} {lv : LVal} :
    LValAllocatedLocation store lv →
    ∃ slot, store.read lv = some slot := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot⟩
  exact ⟨slot, by simp [ProgramStore.read, hloc, hslot]⟩

/-- Corollary 9.4, Read Preservation, from an established location witness. -/
theorem readPreservation_of_location {store : ProgramStore} {lv : LVal} {ty : Ty} :
    LValLocationAbstraction store lv (.ty ty) →
    ∃ value slot,
      store.read lv = some slot ∧
      slot.value = .value value ∧
      ValidValue store value ty := by
  intro hlocation
  rcases hlocation with ⟨location, slot, hloc, hslot, hvalid⟩
  rcases validPartialValue_full_value hvalid with ⟨value, hvalue, hvalidValue⟩
  exact ⟨value, slot, by
      simp [ProgramStore.read, hloc, hslot],
    hvalue,
    hvalidValue⟩

/-- Corollary 9.4, Read Preservation. -/
theorem readPreservation {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env lv (.ty ty) lifetime →
    ∃ value slot,
      store.read lv = some slot ∧
      slot.value = .value value ∧
      ValidValue store value ty := by
  intro hwellFormed hsafe htyping
  exact readPreservation_of_location
    (lvalTyping_defined_location hwellFormed hsafe htyping)

end Paper
end LwRust
