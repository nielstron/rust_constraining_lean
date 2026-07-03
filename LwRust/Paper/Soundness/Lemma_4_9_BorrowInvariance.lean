import LwRust.Paper.Soundness.Lemma_4_10_Progress

/-!
# Lemma 4.9 (Borrow Invariance)

Paper statement (Section 4.3):

> Let `S₁ ▷ t` be a valid state; let `σ` be a store typing where `S₁ ▷ t ⊢ σ`;
> let `Γ₁` be a well-formed typing environment with respect to a lifetime `l`
> where `S₁ ∼ Γ₁` and `Γ₂` be an arbitrary typing environment; let `t` be a
> term; and let `T` be a type.  If `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂`, then `Γ₂[γ ↦ T^l]`
> is well-formed with respect to `l` for arbitrary `γ ∈ fresh`.

Status: the core output-environment statement is proved.  The mutable-borrow
fan-out facts needed by Definition 3.23 are carried by the strengthened write
rules and appendix helper lemmas, not by the named Lemma 4.9 wrapper.

The borrow invariant is now mechanised **faithfully per target** (Definition
4.8(i): each individual target lval `w` of a contained borrow is typable with
`m ≼ n`), as opposed to the earlier — and unsound — joint target-list typing
`Γ ⊢ ū : ⟨T⟩^m` (Definition 3.21, which belongs to the well-formed *type*
judgement established at borrow creation by `T-LvBor`, not to the runtime
invariant).  This was the root cause that blocked the environment-join case: rule
W-Bor merges the target *lists* of two joined borrows without joining their
target types, so the merged list has no joint typing in general, yet each target
keeps its own per-target typing.  With the per-target statement:

* the previously **false** obligation `partialTyUnion_preserves_borrows` is now a
  theorem (`PartialTyBorrowsWellFormedInSlot.of_partialTyUnion`);
* the borrow-target join transport uses the single-lval
  `FullLValTypingJoinTransport` (no joint cons-union landmark);
* the single-lval determinism keystone `lvalTyping_eqv`/`lvalTyping_sameShape`
  (from the linearizability rank φ) is fully proven and unconditional.

The old artificial final result-extension form is kept only in explicitly named
compatibility helpers; the paper-facing wrapper below states the core `Γ₂`
invariant directly.
-/

namespace LwRust
namespace Paper

open Core

/--
The terminal safety conclusion of Lemma 4.11 / Theorem 4.12: the terminal state
is valid, the final store safely abstracts the output environment, and the
terminal value abstracts the result type.
-/
def FullTerminalStateSafe (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) :
    Prop :=
  ValidRuntimeState store (.val value) ∧
    FullSafeAbstraction store env ∧
    ValidValue store value ty

/--
Terminal safety against the weakened runtime abstraction used for environments
with stale loan annotations.  Initialized result values still carry full
validity at initialized borrow nodes; stale borrow annotations are checked only
as shape/protection tokens.
-/
def TerminalStateSafe
    (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) : Prop :=
  ValidRuntimeState store (.val value) ∧
    store ∼ₛ env ∧
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty)

theorem FullTerminalStateSafe.whenInitialized {store : ProgramStore}
    {value : Value} {env : Env} {ty : Ty} :
    FullTerminalStateSafe store value env ty →
    TerminalStateSafe store value env ty := by
  intro hterminal
  exact ⟨hterminal.1, hterminal.2.1.whenInitialized,
    hterminal.2.2.whenInitialized⟩

def EnvSameShapeStrengthening (source result : Env) : Prop :=
  (∀ x resultSlot,
    result.slotAt x = some resultSlot →
    ∃ sourceSlot,
      source.slotAt x = some sourceSlot ∧
        sourceSlot.lifetime = resultSlot.lifetime ∧
        PartialTyStrengthens sourceSlot.ty resultSlot.ty ∧
        PartialTy.sameShape sourceSlot.ty resultSlot.ty) ∧
  (∀ x sourceSlot,
    source.slotAt x = some sourceSlot →
    ∃ resultSlot,
      result.slotAt x = some resultSlot ∧
        sourceSlot.lifetime = resultSlot.lifetime)

def FullCoherent (env : Env) : Prop :=
  ∀ lv mutable targets borrowLifetime,
    LValTyping env lv (.ty (.borrow mutable targets)) borrowLifetime →
    ∃ targetTy targetLifetime,
      LValTargetsTyping env targets (.ty targetTy) targetLifetime

theorem EnvSameShapeStrengthening.refl (env : Env) :
    EnvSameShapeStrengthening env env := by
  constructor
  · intro x resultSlot hslot
    exact ⟨resultSlot, hslot, rfl, PartialTyStrengthens.reflex,
      PartialTy.sameShape_refl _⟩
  · intro x sourceSlot hslot
    exact ⟨sourceSlot, hslot, rfl⟩

theorem EnvSameShapeStrengthening.trans {first second third : Env} :
    EnvSameShapeStrengthening first second →
    EnvSameShapeStrengthening second third →
    EnvSameShapeStrengthening first third := by
  intro hfirst hsecond
  constructor
  · intro x thirdSlot hthird
    rcases hsecond.1 x thirdSlot hthird with
      ⟨secondSlot, hsecondSlot, hlife₂, hstrength₂, hshape₂⟩
    rcases hfirst.1 x secondSlot hsecondSlot with
      ⟨firstSlot, hfirstSlot, hlife₁, hstrength₁, hshape₁⟩
    exact ⟨firstSlot, hfirstSlot, by rw [hlife₁, hlife₂],
      partialTyStrengthens_trans hstrength₁ hstrength₂,
      PartialTy.sameShape_trans hshape₁ hshape₂⟩
  · intro x firstSlot hfirstSlot
    rcases hfirst.2 x firstSlot hfirstSlot with
      ⟨secondSlot, hsecondSlot, hlife₁⟩
    rcases hsecond.2 x secondSlot hsecondSlot with
      ⟨thirdSlot, hthirdSlot, hlife₂⟩
    exact ⟨thirdSlot, hthirdSlot, by rw [hlife₁, hlife₂]⟩

theorem EnvSameShapeStrengthening.safe
    {store : ProgramStore} {source result : Env} :
    EnvSameShapeStrengthening source result →
    store ≈ₛ source →
    store ≈ₛ result := by
  intro hmap hsafe
  exact safeAbstraction_transport_sameShape hsafe hmap.1 hmap.2

theorem EnvSameShapeStrengthening.update_result_strengthening
    {source result : Env} {x : Name} {sourceSlot resultSlot : EnvSlot} :
    EnvSameShapeStrengthening source result →
    source.slotAt x = some sourceSlot →
    sourceSlot.lifetime = resultSlot.lifetime →
    PartialTyStrengthens sourceSlot.ty resultSlot.ty →
    PartialTy.sameShape sourceSlot.ty resultSlot.ty →
    EnvSameShapeStrengthening source (result.update x resultSlot) := by
  intro hmap hsourceSlot hlifetime hstrength hshape
  constructor
  · intro y slot hslot
    by_cases hy : y = x
    · subst hy
      have hslotEq : slot = resultSlot := by
        simpa [Env.update] using hslot.symm
      subst hslotEq
      exact ⟨sourceSlot, hsourceSlot, hlifetime, hstrength, hshape⟩
    · have hresultOld : result.slotAt y = some slot := by
        simpa [Env.update, hy] using hslot
      exact hmap.1 y slot hresultOld
  · intro y slot hslot
    by_cases hy : y = x
    · subst hy
      have hslotEq : slot = sourceSlot :=
        Option.some.inj (hslot.symm.trans hsourceSlot)
      subst hslotEq
      exact ⟨resultSlot, by simp [Env.update], hlifetime⟩
    · rcases hmap.2 y slot hslot with ⟨middleSlot, hmiddleSlot, hlife⟩
      exact ⟨middleSlot, by simpa [Env.update, hy] using hmiddleSlot, hlife⟩

theorem EnvSameShapeStrengthening.of_shapeMap {source result : Env} :
    (∀ x sourceSlot,
      source.slotAt x = some sourceSlot →
      ∃ resultSlot,
        result.slotAt x = some resultSlot ∧
          PartialTy.sameShape sourceSlot.ty resultSlot.ty ∧
          PartialTyStrengthens sourceSlot.ty resultSlot.ty) →
    EnvLifetimesPreserved source result →
    EnvLifetimesSurvive source result →
    EnvSameShapeStrengthening source result := by
  intro hshapeMap hpreserved hsurvive
  constructor
  · intro x resultSlot hresultSlot
    rcases hpreserved x resultSlot hresultSlot with
      ⟨sourceSlot, hsourceSlot, hlifetime⟩
    rcases hshapeMap x sourceSlot hsourceSlot with
      ⟨mappedSlot, hmappedSlot, hshape, hstrength⟩
    have hmappedEq : mappedSlot = resultSlot :=
      Option.some.inj (hmappedSlot.symm.trans hresultSlot)
    subst hmappedEq
    exact ⟨sourceSlot, hsourceSlot, hlifetime, hstrength, hshape⟩
  · exact hsurvive

theorem EnvWrite.positive_var_strong_to_result_map
    {rank : Nat} {env result : Env} {x : Name}
    {slot : EnvSlot} {oldTy rhsTy : Ty} :
    0 < rank →
    env.slotAt x = some slot →
    slot.ty = .ty oldTy →
    EnvWrite rank env (.var x) rhsTy result →
    EnvSameShapeStrengthening
      (env.update x { slot with ty := .ty rhsTy }) result := by
  intro hrank hslot hslotTy hwrite
  cases hwrite with
  | @intro _rank _env₁ env₂ lv writeSlot _ty updatedTy hwriteSlot hupdate =>
      simp [LVal.base] at hwriteSlot
      have hslotEq : writeSlot = slot := by
        have hsome : some writeSlot = some slot := by
          rw [← hwriteSlot, hslot]
        exact Option.some.inj hsome
      subst writeSlot
      simp [LVal.path] at hupdate
      rw [hslotTy] at hupdate
      cases hupdate with
      | strong =>
          exact False.elim (Nat.lt_irrefl 0 hrank)
      | weak hshape hjoin =>
          constructor
          · intro y resultSlot hresultSlot
            by_cases hy : y = x
            · subst hy
              have hresultSlotEq :
                  resultSlot = { slot with ty := updatedTy } := by
                simpa [Env.update, LVal.base] using hresultSlot.symm
              subst hresultSlotEq
              refine ⟨{ slot with ty := .ty rhsTy }, ?_, ?_, ?_, ?_⟩
              · simp [Env.update]
              · rfl
              · exact PartialTyUnion.right_strengthens hjoin
              · exact partialTyJoin_ty_left_sameShape
                  (PartialTyUnion.symm hjoin)
            · have hresultOld :
                  env.slotAt y = some resultSlot := by
                simpa [Env.update, LVal.base, hy] using hresultSlot
              refine ⟨resultSlot, ?_, rfl, PartialTyStrengthens.reflex,
                PartialTy.sameShape_refl _⟩
              simpa [Env.update, hy] using hresultOld
          · intro y sourceSlot hsourceSlot
            by_cases hy : y = x
            · subst hy
              have hsourceSlotEq :
                  sourceSlot = { slot with ty := .ty rhsTy } := by
                simpa [Env.update, LVal.base] using hsourceSlot.symm
              subst hsourceSlotEq
              refine ⟨{ slot with ty := updatedTy }, ?_, rfl⟩
              simp [Env.update, LVal.base]
            · have hsourceOld :
                  env.slotAt y = some sourceSlot := by
                simpa [Env.update, hy] using hsourceSlot
              refine ⟨sourceSlot, ?_, rfl⟩
              simpa [Env.update, LVal.base, hy] using hsourceOld

theorem EnvJoin.left_sameShapeStrengthening {left right join : Env} :
    EnvJoin left right join →
    (∀ x leftSlot rightSlot,
      left.slotAt x = some leftSlot →
      right.slotAt x = some rightSlot →
      PartialTy.sameShape leftSlot.ty rightSlot.ty) →
    EnvSameShapeStrengthening left join := by
  intro hjoin hbranch
  constructor
  · intro x joinSlot hjoinSlot
    rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
      ⟨leftSlot, hleftSlot, hlifetime⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
      ⟨rightSlot, hrightSlot, _hrightLifetime⟩
    rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
      ⟨_, _, hunion⟩
    exact ⟨leftSlot, hleftSlot, hlifetime,
      PartialTyUnion.left_strengthens hunion,
      partialTyUnion_sameShape_of_sameShape hunion
        (hbranch x leftSlot rightSlot hleftSlot hrightSlot)⟩
  · intro x leftSlot hleftSlot
    have hle := EnvJoin.le_left hjoin x
    rw [hleftSlot] at hle
    cases hjoinSlot : join.slotAt x with
    | none =>
        rw [hjoinSlot] at hle
        exact False.elim hle
    | some joinSlot =>
        rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
          ⟨leftSlot', hleftSlot', hlifetime⟩
        have hslotEq : leftSlot' = leftSlot :=
          Option.some.inj (hleftSlot'.symm.trans hleftSlot)
        subst hslotEq
        exact ⟨joinSlot, rfl, hlifetime⟩

theorem EnvJoin.right_sameShapeStrengthening {left right join : Env} :
    EnvJoin left right join →
    (∀ x leftSlot rightSlot,
      left.slotAt x = some leftSlot →
      right.slotAt x = some rightSlot →
      PartialTy.sameShape leftSlot.ty rightSlot.ty) →
    EnvSameShapeStrengthening right join := by
  intro hjoin hbranch
  constructor
  · intro x joinSlot hjoinSlot
    rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
      ⟨leftSlot, hleftSlot, _hleftLifetime⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
      ⟨rightSlot, hrightSlot, hlifetime⟩
    rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
      ⟨_, _, hunion⟩
    have hshapeLR :
        PartialTy.sameShape leftSlot.ty rightSlot.ty :=
      hbranch x leftSlot rightSlot hleftSlot hrightSlot
    have hshapeLJoin :
        PartialTy.sameShape leftSlot.ty joinSlot.ty :=
      partialTyUnion_sameShape_of_sameShape hunion hshapeLR
    exact ⟨rightSlot, hrightSlot, hlifetime,
      PartialTyUnion.right_strengthens hunion,
      PartialTy.sameShape_trans (PartialTy.sameShape_symm hshapeLR)
        hshapeLJoin⟩
  · intro x rightSlot hrightSlot
    have hle := EnvJoin.le_right hjoin x
    rw [hrightSlot] at hle
    cases hjoinSlot : join.slotAt x with
    | none =>
        rw [hjoinSlot] at hle
        exact False.elim hle
    | some joinSlot =>
        rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
          ⟨rightSlot', hrightSlot', hlifetime⟩
        have hslotEq : rightSlot' = rightSlot :=
          Option.some.inj (hrightSlot'.symm.trans hrightSlot)
        subst hslotEq
        exact ⟨joinSlot, rfl, hlifetime⟩

/-- Transport one branch's terminal state into the join environment: the
join is well-formed (its slots-outlive component comes from the branch via
lifetime preservation; the remaining components are the rule's join
obligations), safe abstraction transports along the same-shape strengthening
map, and the final value strengthens into the join type.  This packages the
per-branch conclusion of `T-IfJoin` in the preservation proof. -/
theorem FullTerminalStateSafe.strengthen_join {finalStore : ProgramStore}
    {finalValue : Value} {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : FullTerminalStateSafe finalStore finalValue branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      FullTerminalStateSafe finalStore finalValue joinEnv joinTy := by
  have hwellJoin : WellFormedEnv joinEnv lifetime :=
    ⟨hcontained,
      EnvSlotsOutlive.of_lifetimesPreserved hwellBranch.2 hpreserved⟩
  have hsafeJoin : finalStore ≈ₛ joinEnv := hmap.safe hterminal.2.1
  exact ⟨hwellJoin, hterminal.1, hsafeJoin,
    safeStrengthening hwellJoin hsafeJoin.whenInitialized
      hstrengthens hterminal.2.2⟩

theorem FullTerminalStateSafe.strengthen_join_whenInitialized {finalStore : ProgramStore}
    {finalValue : Value} {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormedWhenInitialized joinEnv)
    (hcoherent : CoherentWhenInitialized joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnvWhenInitialized branchEnv lifetime)
    (hterminal : FullTerminalStateSafe finalStore finalValue branchEnv branchTy) :
    WellFormedEnvWhenInitialized joinEnv lifetime ∧
      FullTerminalStateSafe finalStore finalValue joinEnv joinTy := by
  have hwellJoin : WellFormedEnvWhenInitialized joinEnv lifetime :=
    ⟨hcontained,
      EnvSlotsOutlive.of_lifetimesPreserved hwellBranch.2 hpreserved⟩
  have hsafeJoin : finalStore ≈ₛ joinEnv := hmap.safe hterminal.2.1
  exact ⟨hwellJoin, hterminal.1, hsafeJoin,
    safeStrengthening_of_strengthens hstrengthens hterminal.2.2⟩

theorem FullTerminalStateSafe.strengthen_join_strengthening_whenInitialized
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime} {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormedWhenInitialized joinEnv)
    (hcoherent : CoherentWhenInitialized joinEnv)
    (hlinear : Linearizable joinEnv)
    (henvStrengthens : EnvStrengthens branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnvWhenInitialized branchEnv lifetime)
    (hterminal : FullTerminalStateSafe finalStore finalValue branchEnv branchTy) :
    WellFormedEnvWhenInitialized joinEnv lifetime ∧
      FullTerminalStateSafe finalStore finalValue joinEnv joinTy := by
  have hwellJoin : WellFormedEnvWhenInitialized joinEnv lifetime :=
    ⟨hcontained,
      EnvSlotsOutlive.of_lifetimesPreserved hwellBranch.2
        (EnvStrengthens.lifetimesPreserved henvStrengthens)⟩
  have hsafeJoin : finalStore ≈ₛ joinEnv :=
    safeAbstraction_transport_strengthening hterminal.2.1 henvStrengthens
  exact ⟨hwellJoin, hterminal.1, hsafeJoin,
    safeStrengthening_of_strengthens hstrengthens hterminal.2.2⟩

theorem TerminalStateSafe.strengthen_join_strengthening
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime} {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormedWhenInitialized joinEnv)
    (hcoherent : CoherentWhenInitialized joinEnv)
    (hlinear : Linearizable joinEnv)
    (hinitBack : ∀ {targets : List LVal},
      BorrowTargetsInitialized joinEnv targets →
      BorrowTargetsInitialized branchEnv targets)
    (henvStrengthens : EnvStrengthens branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnvWhenInitialized branchEnv lifetime)
    (hterminal : TerminalStateSafe finalStore finalValue
      branchEnv branchTy) :
    WellFormedEnvWhenInitialized joinEnv lifetime ∧
      TerminalStateSafe finalStore finalValue joinEnv joinTy := by
  have hwellJoin : WellFormedEnvWhenInitialized joinEnv lifetime :=
    ⟨hcontained,
      EnvSlotsOutlive.of_lifetimesPreserved hwellBranch.2
        (EnvStrengthens.lifetimesPreserved henvStrengthens)⟩
  have hsafeJoin : SafeAbstraction finalStore joinEnv :=
    safeAbstractionWhenInitialized_transport_strengthening
      hinitBack hterminal.2.1 henvStrengthens
  have hvalidJoinEnv :
      ValidPartialValueWhenInitialized joinEnv finalStore
        (.value finalValue) (.ty branchTy) :=
    validPartialValueWhenInitialized_transport_env hinitBack hterminal.2.2
  exact ⟨hwellJoin, hterminal.1, hsafeJoin,
    validPartialValueWhenInitialized_strengthen hvalidJoinEnv
      hstrengthens⟩

theorem WriteBorrowTargets.initialized_leaves_of_typed
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} :
    WriteBorrowTargets rank env path targets rhsTy result →
    ∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy := by
  intro hwrites
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _rank env path targets rhsTy _result _ =>
      ∀ target, target ∈ targets → ∀ targetSlot,
        env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
        WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?boxFull ?mutBorrow ?nil ?singleton ?cons ?intro hwrites
  case strong | weak | box | boxFull | mutBorrow => intros; trivial
  case nil =>
    intro rank env path ty target htarget
    simp at htarget
  case singleton =>
    intro rank env updated path target ty _hwrite htyped _ih selected hselected slot hslot
    rw [List.mem_singleton] at hselected
    subst hselected
    rcases htyped with ⟨leafTy, leafLifetime, htyping⟩
    have hleaf :=
      writeLeafTy_of_lvalTyping htyping hslot [] ty WriteLeafTy.leaf
    simpa using hleaf
  case cons =>
    intro rank env updated restEnv result path target rest ty
      _hwrite htyped _hwrites _hjoin _ihWrite ihRest selected hselected slot hslot
    rcases List.mem_cons.mp hselected with hhead | htail
    · subst hhead
      rcases htyped with ⟨leafTy, leafLifetime, htyping⟩
      have hleaf :=
        writeLeafTy_of_lvalTyping htyping hslot [] ty WriteLeafTy.leaf
      simpa using hleaf
    · exact ihRest selected htail slot hslot
  case intro => intros; trivial

theorem WriteBorrowTargets.selected_var_strong_to_result_map
    {rank : Nat} {env result : Env}
    {targets : List LVal} {rhsTy : Ty}
    {selectedName : Name} {selectedSlot : EnvSlot} {selectedTy : Ty} :
    0 < rank →
    WriteBorrowTargets rank env [] targets rhsTy result →
    (.var selectedName) ∈ targets →
    env.slotAt selectedName = some selectedSlot →
    selectedSlot.ty = .ty selectedTy →
    EnvSameShapeStrengthening
      (env.update selectedName { selectedSlot with ty := .ty rhsTy })
      result := by
  intro hrank hwrites
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun rank env path targets rhsTy result hwrites =>
      path = [] →
      0 < rank →
      ∀ {selectedName : Name} {selectedSlot : EnvSlot} {selectedTy : Ty},
        (.var selectedName) ∈ targets →
        env.slotAt selectedName = some selectedSlot →
        selectedSlot.ty = .ty selectedTy →
        EnvSameShapeStrengthening
          (env.update selectedName { selectedSlot with ty := .ty rhsTy })
          result)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?boxFull ?mutBorrow ?nil ?singleton ?cons ?intro
    hwrites rfl hrank
  case strong | weak | box | boxFull | mutBorrow => intros; trivial
  case nil =>
    intro rank env path ty hpath _hrank selectedName selectedSlot selectedTy hmem
    simp at hmem
  case singleton =>
    intro rank env updated path target ty hwrite _htyped _ih hpath
      hrank selectedName selectedSlot selectedTy hmem hslot hslotTy
    subst hpath
    rw [List.mem_singleton] at hmem
    subst hmem
    exact EnvWrite.positive_var_strong_to_result_map
      hrank hslot hslotTy (by simpa [prependPath] using hwrite)
  case cons =>
    intro rank env updated restEnv result path target rest ty
      hwrite htyped hwrites hjoin _ihWrite ihWrites hpath
      hrank selectedName selectedSlot selectedTy hmem hslot hslotTy
    subst hpath
    have hallLeaves :
        ∀ t, t ∈ target :: rest → ∀ tslot,
          env.slotAt (LVal.base (prependPath [] t)) = some tslot →
          WriteLeafTy env (LVal.path (prependPath [] t)) tslot.ty ty :=
      WriteBorrowTargets.initialized_leaves_of_typed
        (WriteBorrowTargets.cons hwrite htyped hwrites hjoin)
    have hupdShape : EnvShapePreserved env updated :=
      EnvWrite.shapePreserved_init hrank hwrite
        (fun slot hslot =>
          by
            have hleaf := hallLeaves target (by simp) slot hslot
            simpa [prependPath] using hleaf)
    have hrestShape : EnvShapePreserved env restEnv :=
      WriteBorrowTargets.shapePreserved_init hrank hwrites
        (fun t ht slot hslot =>
          by
            have hleaf := hallLeaves t (List.mem_cons_of_mem target ht) slot hslot
            simpa [prependPath] using hleaf)
    have hbranch :
        ∀ x leftSlot rightSlot,
          updated.slotAt x = some leftSlot →
          restEnv.slotAt x = some rightSlot →
          PartialTy.sameShape leftSlot.ty rightSlot.ty :=
      EnvShapePreserved.branch_sameShape hupdShape hrestShape
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst hhead
      have hheadMap :
          EnvSameShapeStrengthening
            (env.update selectedName { selectedSlot with ty := .ty ty })
            updated :=
        EnvWrite.positive_var_strong_to_result_map
          hrank hslot hslotTy (by simpa [prependPath] using hwrite)
      exact EnvSameShapeStrengthening.trans hheadMap
        (EnvJoin.left_sameShapeStrengthening hjoin hbranch)
    · have hrestMap :
          EnvSameShapeStrengthening
            (env.update selectedName { selectedSlot with ty := .ty ty })
            restEnv :=
        ihWrites rfl hrank htail hslot hslotTy
      exact EnvSameShapeStrengthening.trans hrestMap
        (EnvJoin.right_sameShapeStrengthening hjoin hbranch)
  case intro => intros; trivial

theorem WriteBorrowTargets.selected_branch_to_result_map
    {rank : Nat} {env result selectedSource : Env}
    {path : List Unit} {targets : List LVal} {rhsTy : Ty}
    {selectedTarget : LVal} :
    0 < rank →
    WriteBorrowTargets rank env path targets rhsTy result →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    selectedTarget ∈ targets →
    (∀ branchResult,
      EnvWrite rank env (prependPath path selectedTarget) rhsTy branchResult →
      EnvSameShapeStrengthening selectedSource branchResult) →
    EnvSameShapeStrengthening selectedSource result := by
  intro hrank hwrites hleaves hmem hselectedBranch
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun rank env path targets rhsTy result hwrites =>
      0 < rank →
      (∀ target, target ∈ targets → ∀ targetSlot,
        env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
        WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
      ∀ {selectedSource : Env} {selectedTarget : LVal},
        selectedTarget ∈ targets →
        (∀ branchResult,
          EnvWrite rank env (prependPath path selectedTarget) rhsTy branchResult →
          EnvSameShapeStrengthening selectedSource branchResult) →
        EnvSameShapeStrengthening selectedSource result)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?boxFull ?mutBorrow ?nil ?singleton ?cons ?intro
    hwrites hrank hleaves hmem hselectedBranch
  case strong | weak | box | boxFull | mutBorrow => intros; trivial
  case nil =>
    intro rank env path ty _hrank _hleaves selectedSource selectedTarget hmem
    simp at hmem
  case singleton =>
    intro rank env updated path target ty hwrite _htyped _ih _hrank _hleaves
      selectedSource selectedTarget hmem hbranch
    rw [List.mem_singleton] at hmem
    subst hmem
    exact hbranch updated hwrite
  case cons =>
    intro rank env updated restEnv result path target rest ty
      hwrite _htyped hwrites hjoin _ihWrite ihWrites hrank hleaves
      selectedSource selectedTarget hmem hbranch
    have hallLeaves :
        ∀ t, t ∈ target :: rest → ∀ tslot,
          env.slotAt (LVal.base (prependPath path t)) = some tslot →
          WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty :=
      hleaves
    have hupdShape : EnvShapePreserved env updated :=
      EnvWrite.shapePreserved_init hrank hwrite
        (fun slot hslot => hallLeaves target (by simp) slot hslot)
    have hrestShape : EnvShapePreserved env restEnv :=
      WriteBorrowTargets.shapePreserved_init hrank hwrites
        (fun t ht slot hslot =>
          hallLeaves t (List.mem_cons_of_mem target ht) slot hslot)
    have hbranchShape :
        ∀ x leftSlot rightSlot,
          updated.slotAt x = some leftSlot →
          restEnv.slotAt x = some rightSlot →
          PartialTy.sameShape leftSlot.ty rightSlot.ty :=
      EnvShapePreserved.branch_sameShape hupdShape hrestShape
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst hhead
      exact EnvSameShapeStrengthening.trans
        (hbranch updated hwrite)
        (EnvJoin.left_sameShapeStrengthening hjoin hbranchShape)
    · have hrestMap :
          EnvSameShapeStrengthening selectedSource restEnv :=
        ihWrites hrank
          (fun t ht slot hslot =>
            hallLeaves t (List.mem_cons_of_mem target ht) slot hslot)
          htail hbranch
      exact EnvSameShapeStrengthening.trans hrestMap
        (EnvJoin.right_sameShapeStrengthening hjoin hbranchShape)
  case intro => intros; trivial

theorem WriteBorrowTargets.selected_branch_to_result_exists
    {rank : Nat} {env result : Env}
    {path : List Unit} {targets : List LVal} {rhsTy : Ty}
    {selectedTarget : LVal} :
    0 < rank →
    WriteBorrowTargets rank env path targets rhsTy result →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    selectedTarget ∈ targets →
    ∃ branchResult,
      EnvWrite rank env (prependPath path selectedTarget) rhsTy branchResult ∧
      EnvSameShapeStrengthening branchResult result := by
  intro hrank hwrites hleaves hmem
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun rank env path targets rhsTy result hwrites =>
      0 < rank →
      (∀ target, target ∈ targets → ∀ targetSlot,
        env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
        WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
      ∀ {selectedTarget : LVal}, selectedTarget ∈ targets →
        ∃ branchResult,
          EnvWrite rank env (prependPath path selectedTarget) rhsTy branchResult ∧
          EnvSameShapeStrengthening branchResult result)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?boxFull ?mutBorrow ?nil ?singleton ?cons ?intro
    hwrites hrank hleaves hmem
  case strong | weak | box | boxFull | mutBorrow => intros; trivial
  case nil =>
    intro rank env path ty _hrank _hleaves selectedTarget hmem
    simp at hmem
  case singleton =>
    intro rank env updated path target ty hwrite _htyped _ih _hrank _hleaves
      selectedTarget hmem
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ⟨updated, hwrite, EnvSameShapeStrengthening.refl updated⟩
  case cons =>
    intro rank env updated restEnv result path target rest ty
      hwrite _htyped hwrites hjoin _ihWrite ihWrites hrank hleaves
      selectedTarget hmem
    have hallLeaves :
        ∀ t, t ∈ target :: rest → ∀ tslot,
          env.slotAt (LVal.base (prependPath path t)) = some tslot →
          WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty :=
      hleaves
    have hupdShape : EnvShapePreserved env updated :=
      EnvWrite.shapePreserved_init hrank hwrite
        (fun slot hslot => hallLeaves target (by simp) slot hslot)
    have hrestShape : EnvShapePreserved env restEnv :=
      WriteBorrowTargets.shapePreserved_init hrank hwrites
        (fun t ht slot hslot =>
          hallLeaves t (List.mem_cons_of_mem target ht) slot hslot)
    have hbranchShape :
        ∀ x leftSlot rightSlot,
          updated.slotAt x = some leftSlot →
          restEnv.slotAt x = some rightSlot →
          PartialTy.sameShape leftSlot.ty rightSlot.ty :=
      EnvShapePreserved.branch_sameShape hupdShape hrestShape
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst hhead
      exact ⟨updated, hwrite,
        EnvJoin.left_sameShapeStrengthening hjoin hbranchShape⟩
    · rcases ihWrites hrank
        (fun t ht slot hslot =>
          hallLeaves t (List.mem_cons_of_mem target ht) slot hslot)
        htail with
        ⟨branchResult, hbranchWrite, hbranchMap⟩
      exact ⟨branchResult, hbranchWrite,
        EnvSameShapeStrengthening.trans hbranchMap
          (EnvJoin.right_sameShapeStrengthening hjoin hbranchShape)⟩
  case intro => intros; trivial

@[simp] theorem prependPath_deref (path : List Unit) (lv : LVal) :
    prependPath path (.deref lv) = prependPath (() :: path) lv := by
  induction path with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [prependPath, ih]

mutual
  /--
  Proof-side selector invariant for writes through a typed lvalue path.

  `PathSelected env pt path selectedName selectedSlot selectedTy` says that
  following `path` from partial type `pt` eventually dereferences a mutable
  borrow branch whose selected target is the variable `selectedName`.  The
  invariant is derived from `LValTyping`/`LValTargetsTyping`; it is not an
  additional typing-rule premise.
  -/
  inductive PathSelected (env : Env) :
      PartialTy → List Unit → Name → EnvSlot → Ty → Prop where
    | borrowHere {mutable : Bool} {targets : List LVal}
        {selectedName : Name} {selectedSlot : EnvSlot} {selectedTy : Ty} :
        (.var selectedName) ∈ targets →
        env.slotAt selectedName = some selectedSlot →
        selectedSlot.ty = .ty selectedTy →
        PathSelected env (.ty (.borrow mutable targets)) [()] selectedName
          selectedSlot selectedTy
    | box {inner : PartialTy} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedTy : Ty} :
        PathSelected env inner path selectedName selectedSlot selectedTy →
        PathSelected env (.box inner) (() :: path) selectedName selectedSlot
          selectedTy
    | borrowStep {mutable : Bool} {targets : List LVal} {path : List Unit}
        {selectedName : Name} {selectedSlot : EnvSlot} {selectedTy : Ty} :
        TargetsPathSelected env targets path selectedName selectedSlot selectedTy →
        PathSelected env (.ty (.borrow mutable targets)) (() :: path) selectedName
          selectedSlot selectedTy

  inductive TargetsPathSelected (env : Env) :
      List LVal → List Unit → Name → EnvSlot → Ty → Prop where
    | target {targets : List LVal} {target : LVal} {pt : PartialTy}
        {lifetime : Lifetime} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedTy : Ty} :
        target ∈ targets →
        LValTyping env target pt lifetime →
        PathSelected env pt path selectedName selectedSlot selectedTy →
        TargetsPathSelected env targets path selectedName selectedSlot selectedTy
end

mutual
  theorem PathSelected.rank_lt_of_lvalTyping {env : Env} {φ : Name → Nat}
      (hφ : LinearizedBy φ env) :
      ∀ {pt : PartialTy} {path : List Unit} {selectedName : Name}
        {selectedSlot : EnvSlot} {selectedTy : Ty},
        PathSelected env pt path selectedName selectedSlot selectedTy →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv pt lifetime →
          φ selectedName < φ (LVal.base lv)
    | .ty (.borrow mutable targets), [()], selectedName, selectedSlot, selectedTy,
      PathSelected.borrowHere hmem _hslot _hty, lv, lifetime, htyping => by
        have hselectedVarMem :
            selectedName ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
          have hmemMap :
              LVal.base (.var selectedName) ∈ targets.map LVal.base :=
            List.mem_map_of_mem hmem
          simpa [PartialTy.vars, Ty.vars, LVal.base] using hmemMap
        exact (lvalTyping_vars_rank_lt hφ).1 htyping selectedName hselectedVarMem
    | .box inner, () :: path, selectedName, selectedSlot, selectedTy,
      PathSelected.box hinner, lv, lifetime, htyping => by
        have hderef : LValTyping env (.deref lv) inner lifetime :=
          LValTyping.box htyping
        simpa [LVal.base] using
          PathSelected.rank_lt_of_lvalTyping hφ hinner hderef
    | .ty (.borrow mutable targets), () :: path, selectedName, selectedSlot,
      selectedTy, PathSelected.borrowStep htargets, lv, lifetime, htyping => by
        exact TargetsPathSelected.rank_lt_of_lvalTyping hφ htargets htyping

  theorem TargetsPathSelected.rank_lt_of_lvalTyping {env : Env} {φ : Name → Nat}
      (hφ : LinearizedBy φ env) :
      ∀ {mutable : Bool} {targets : List LVal} {path : List Unit}
        {selectedName : Name} {selectedSlot : EnvSlot} {selectedTy : Ty},
        TargetsPathSelected env targets path selectedName selectedSlot selectedTy →
        ∀ {lv : LVal} {lifetime : Lifetime},
          LValTyping env lv (.ty (.borrow mutable targets)) lifetime →
          φ selectedName < φ (LVal.base lv)
    | mutable, targets, path, selectedName, selectedSlot, selectedTy,
      TargetsPathSelected.target hmem htargetTyping hpath, lv, lifetime, htyping => by
        have hselectedLtTarget :
            φ selectedName < φ (LVal.base _) :=
          PathSelected.rank_lt_of_lvalTyping hφ hpath htargetTyping
        have htargetMem :
            LVal.base _ ∈ PartialTy.vars (.ty (.borrow mutable targets)) :=
          mem_partialTy_vars_iff.mpr
            ⟨mutable, targets, _, PartialTyContains.here, hmem, rfl⟩
        have htargetLtLv :
            φ (LVal.base _) < φ (LVal.base lv) :=
          (lvalTyping_vars_rank_lt hφ).1 htyping _ htargetMem
        exact lt_trans hselectedLtTarget htargetLtLv
end

theorem PathSelected.of_partialTyUnion {env : Env} {left right union : PartialTy}
    {path : List Unit} {selectedName : Name} {selectedSlot : EnvSlot}
    {selectedTy : Ty} :
    PartialTyUnion left right union →
    PathSelected env union path selectedName selectedSlot selectedTy →
    PathSelected env left path selectedName selectedSlot selectedTy ∨
      PathSelected env right path selectedName selectedSlot selectedTy := by
  intro hunion hselected
  refine PathSelected.rec
    (motive_1 := fun union path selectedName selectedSlot selectedTy _ =>
      ∀ left right,
        PartialTyUnion left right union →
        PathSelected env left path selectedName selectedSlot selectedTy ∨
          PathSelected env right path selectedName selectedSlot selectedTy)
    (motive_2 := fun _targets _path _selectedName _selectedSlot _selectedTy _ =>
      True)
    ?borrowHere ?box ?borrowStep ?target hselected left right hunion
  case borrowHere =>
    intro mutable targets selectedName selectedSlot selectedTy hmem hslot hty
      left right hunion
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.left_strengthens hunion) with
      ⟨leftTargets, hleftEq, _hleftSubset⟩
    rcases PartialTyStrengthens.to_borrow_right
        (PartialTyUnion.right_strengthens hunion) with
      ⟨rightTargets, hrightEq, _hrightSubset⟩
    subst hleftEq
    subst hrightEq
    rcases PartialTyUnion.borrow_member hunion hmem with hleft | hright
    · exact Or.inl (PathSelected.borrowHere hleft hslot hty)
    · exact Or.inr (PathSelected.borrowHere hright hslot hty)
  case box =>
    intro inner path selectedName selectedSlot selectedTy hinner ih left right hunion
    have hleftStrength := PartialTyUnion.left_strengthens hunion
    cases hleftStrength with
    | reflex =>
        exact Or.inl (PathSelected.box hinner)
    | box hleftInner =>
        have hrightStrength := PartialTyUnion.right_strengthens hunion
        cases hrightStrength with
        | reflex =>
            exact Or.inr (PathSelected.box hinner)
        | box hrightInner =>
            rcases ih _ _ (PartialTyUnion.box_inv hunion) with hleft | hright
            · exact Or.inl (PathSelected.box hleft)
            · exact Or.inr (PathSelected.box hright)
  case borrowStep =>
    intro mutable targets path selectedName selectedSlot selectedTy htargets _ih
      left right hunion
    cases htargets with
    | target hmem htargetTyping hpath =>
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.left_strengthens hunion) with
          ⟨leftTargets, hleftEq, _hleftSubset⟩
        rcases PartialTyStrengthens.to_borrow_right
            (PartialTyUnion.right_strengthens hunion) with
          ⟨rightTargets, hrightEq, _hrightSubset⟩
        subst hleftEq
        subst hrightEq
        rcases PartialTyUnion.borrow_member hunion hmem with hleft | hright
        · exact Or.inl (PathSelected.borrowStep
            (TargetsPathSelected.target hleft htargetTyping hpath))
        · exact Or.inr (PathSelected.borrowStep
            (TargetsPathSelected.target hright htargetTyping hpath))
  case target =>
    intros
    trivial

theorem TargetsPathSelected.of_lvalTargetsTyping {env : Env}
    {targets : List LVal} {pt : PartialTy} {lifetime : Lifetime}
    {path : List Unit} {selectedName : Name} {selectedSlot : EnvSlot}
    {selectedTy : Ty} :
    LValTargetsTyping env targets pt lifetime →
    PathSelected env pt path selectedName selectedSlot selectedTy →
    TargetsPathSelected env targets path selectedName selectedSlot selectedTy := by
  intro htargets hselected
  refine LValTargetsTyping.rec
    (motive_1 := fun _target _ty _lifetime _htyping => True)
    (motive_2 := fun targets pt lifetime _htyping =>
      ∀ {path : List Unit} {selectedName : Name} {selectedSlot : EnvSlot}
        {selectedTy : Ty},
        PathSelected env pt path selectedName selectedSlot selectedTy →
        TargetsPathSelected env targets path selectedName selectedSlot selectedTy)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htargets hselected
  case var | box | boxFull | borrow => intros; trivial
  case singleton =>
      intro target ty lifetime htarget _ih path selectedName selectedSlot selectedTy hselected
      exact TargetsPathSelected.target (by simp) htarget hselected
  case cons =>
      intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
        hhead _hrest hunion _hintersection _ihHead ihRest
        path selectedName selectedSlot selectedTy hselected
      rcases PathSelected.of_partialTyUnion hunion hselected with hheadSelected |
        hrestSelected
      · exact TargetsPathSelected.target (by simp) hhead hheadSelected
      · cases ihRest hrestSelected with
        | target hmem htargetTyping hpath =>
            exact TargetsPathSelected.target (List.mem_cons_of_mem _ hmem)
              htargetTyping hpath

theorem PathSelected.updateAtPath_map {env writeEnv : Env}
    {oldTy updatedTy : PartialTy} {path : List Unit} {rank : Nat}
    {rhsTy selectedTy : Ty} {selectedName : Name} {selectedSlot : EnvSlot}
    {φ : Name → Nat} {rootRank : Nat} :
    (∀ v, v ∈ PartialTy.vars oldTy → φ v < rootRank) →
    PathSelected env oldTy path selectedName selectedSlot selectedTy →
    UpdateAtPath rank env path oldTy rhsTy writeEnv updatedTy →
    (∀ {branchRank : Nat} {target : LVal} {pt : PartialTy}
      {lifetime : Lifetime} {branchPath : List Unit} {branchResult : Env},
      φ (LVal.base target) < rootRank →
      LValTyping env target pt lifetime →
      PathSelected env pt branchPath selectedName selectedSlot selectedTy →
      EnvWrite branchRank env (prependPath branchPath target) rhsTy branchResult →
      EnvSameShapeStrengthening
        (env.update selectedName { selectedSlot with ty := .ty rhsTy })
        branchResult) →
    EnvSameShapeStrengthening
        (env.update selectedName { selectedSlot with ty := .ty rhsTy })
        writeEnv ∧
      PartialTyStrengthens oldTy updatedTy ∧
      PartialTy.sameShape oldTy updatedTy := by
  intro hbelow hselected hupdate hbranch
  refine (PathSelected.rec
    (motive_1 := fun oldTy path selectedName selectedSlot selectedTy _hselected =>
      ∀ {rank : Nat} {updatedTy : PartialTy} {writeEnv : Env},
        (∀ v, v ∈ PartialTy.vars oldTy → φ v < rootRank) →
        UpdateAtPath rank env path oldTy rhsTy writeEnv updatedTy →
        (∀ {branchRank : Nat} {target : LVal} {pt : PartialTy}
          {lifetime : Lifetime} {branchPath : List Unit} {branchResult : Env},
          φ (LVal.base target) < rootRank →
          LValTyping env target pt lifetime →
          PathSelected env pt branchPath selectedName selectedSlot selectedTy →
          EnvWrite branchRank env (prependPath branchPath target) rhsTy branchResult →
          EnvSameShapeStrengthening
            (env.update selectedName { selectedSlot with ty := .ty rhsTy })
            branchResult) →
        EnvSameShapeStrengthening
            (env.update selectedName { selectedSlot with ty := .ty rhsTy })
            writeEnv ∧
          PartialTyStrengthens oldTy updatedTy ∧
          PartialTy.sameShape oldTy updatedTy)
    (motive_2 := fun _targets _path _selectedName _selectedSlot _selectedTy _ =>
      True)
    ?borrowHere ?box ?borrowStep ?target hselected) hbelow hupdate hbranch
  case borrowHere =>
      intro mutable targets selectedName selectedSlot selectedTy hmem hselectedSlot
        hselectedTyEq rank updatedTy writeEnv hbelow hupdate hbranch
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        cases hupdatedEq
        exact ⟨
          WriteBorrowTargets.selected_var_strong_to_result_map
            (Nat.succ_pos rank) hwrites hmem hselectedSlot hselectedTyEq,
          PartialTyStrengthens.reflex,
          PartialTy.sameShape_refl _⟩
  case box =>
      intro inner path selectedName selectedSlot selectedTy hinner ih
        rank updatedTy writeEnv hbelow hupdate hbranch
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, hupdatedEq, hinnerUpdate⟩
          cases htyEq
          cases hupdatedEq
          have hbelowInner :
              ∀ v, v ∈ PartialTy.vars inner → φ v < rootRank := by
            intro v hv
            exact hbelow v (by simpa [PartialTy.vars] using hv)
          rcases ih hbelowInner hinnerUpdate hbranch with
            ⟨hmap, hstrength, hshape⟩
          exact ⟨hmap, PartialTyStrengthens.box hstrength,
            by simpa [PartialTy.sameShape] using hshape⟩
        · rcases hboxFull with
            ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinnerUpdate⟩
          cases htyEq
      · rcases hborrow with ⟨targets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  case borrowStep =>
      intro mutable targets path selectedName selectedSlot selectedTy htargetsSelected _ih
        rank updatedTy writeEnv hbelow hupdate hbranch
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        cases hupdatedEq
        cases htargetsSelected with
        | target htargetMem htargetTyping htargetSelected =>
            rename_i branchTarget branchPt branchLifetime
            have htargetRank :
                φ (LVal.base branchTarget) < rootRank := by
              exact hbelow (LVal.base branchTarget)
                (mem_partialTy_vars_iff.mpr
                  ⟨true, _, branchTarget, PartialTyContains.here, htargetMem, rfl⟩)
            have hleaves :=
              WriteBorrowTargets.initialized_leaves_of_typed hwrites
            have hmap :
                EnvSameShapeStrengthening
                  (env.update selectedName
                    { selectedSlot with ty := .ty rhsTy })
                  writeEnv :=
              WriteBorrowTargets.selected_branch_to_result_map
                (Nat.succ_pos rank) hwrites hleaves htargetMem
                (fun branchResult hbranchWrite =>
                  hbranch htargetRank htargetTyping htargetSelected hbranchWrite)
            exact ⟨hmap, PartialTyStrengthens.reflex,
              PartialTy.sameShape_refl _⟩
  case target =>
      intros
      trivial

theorem EnvContains.update_same {env : Env} {x : Name} {slot : EnvSlot}
    {ty : Ty} :
    PartialTyContains slot.ty ty →
    (env.update x slot) ⊢ x ↝ ty := by
  intro hcontains
  exact ⟨slot, by simp [Env.update], hcontains⟩

theorem pathConflicts_of_base_eq {target left right : LVal} :
    LVal.base left = LVal.base right →
    target ⋈ left →
    target ⋈ right := by
  intro hbase hconflict
  exact hconflict.trans hbase

theorem readProhibited_congr_base {env : Env} {left right : LVal} :
    LVal.base left = LVal.base right →
    (ReadProhibited env left ↔ ReadProhibited env right) := fun hbase => by
  constructor
  · intro hread
    rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    exact ⟨x, targets, target, hcontains, htarget,
      pathConflicts_of_base_eq hbase hconflict⟩
  · intro hread
    rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    exact ⟨x, targets, target, hcontains, htarget,
      pathConflicts_of_base_eq hbase.symm hconflict⟩

theorem writeProhibited_congr_base {env : Env} {left right : LVal} :
    LVal.base left = LVal.base right →
    (WriteProhibited env left ↔ WriteProhibited env right) := fun hbase => by
  constructor
  · intro hwrite
    cases hwrite with
    | inl hread =>
        exact Or.inl ((readProhibited_congr_base hbase).mp hread)
    | inr himm =>
        rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
        exact Or.inr ⟨x, targets, target, hcontains, htarget,
          pathConflicts_of_base_eq hbase hconflict⟩
  · intro hwrite
    cases hwrite with
    | inl hread =>
        exact Or.inl ((readProhibited_congr_base hbase).mpr hread)
    | inr himm =>
        rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
        exact Or.inr ⟨x, targets, target, hcontains, htarget,
          pathConflicts_of_base_eq hbase.symm hconflict⟩

theorem not_writeProhibited_var_base {env : Env} {lv : LVal} :
    ¬ WriteProhibited env lv →
    ¬ WriteProhibited env (.var (LVal.base lv)) := by
  intro hnot hwrite
  exact hnot ((writeProhibited_congr_base
    (env := env) (left := lv) (right := .var (LVal.base lv))
    (by simp [LVal.base])).mpr hwrite)

/-- `WriteProhibited` with the witnessing environment slot made explicit. -/
def WriteProhibitedVia (env : Env) (y : Name) (lv : LVal) : Prop :=
  (∃ targets target,
    env ⊢ y ↝ (.borrow true targets) ∧
    target ∈ targets ∧
    target ⋈ lv) ∨
  ∃ targets target,
    env ⊢ y ↝ (.borrow false targets) ∧
    target ∈ targets ∧
    target ⋈ lv

theorem WriteProhibitedVia.writeProhibited {env : Env} {y : Name}
    {lv : LVal} :
    WriteProhibitedVia env y lv → WriteProhibited env lv := by
  intro hvia
  cases hvia with
  | inl hread =>
      rcases hread with ⟨targets, target, hcontains, htarget, hconflict⟩
      exact Or.inl ⟨y, targets, target, hcontains, htarget, hconflict⟩
  | inr hwrite =>
      rcases hwrite with ⟨targets, target, hcontains, htarget, hconflict⟩
      exact Or.inr ⟨y, targets, target, hcontains, htarget, hconflict⟩

theorem EnvContains.update_of_ne {env : Env} {x y : Name}
    {slot : EnvSlot} {ty : Ty} :
    y ≠ x →
    env ⊢ y ↝ ty →
    (env.update x slot) ⊢ y ↝ ty := by
  intro hy hcontains
  rcases hcontains with ⟨envSlot, hslot, hcontainsTy⟩
  exact ⟨envSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩

theorem WriteProhibitedVia.update_of_ne {env : Env} {x y : Name}
    {slot : EnvSlot} {lv : LVal} :
    y ≠ x →
    WriteProhibitedVia env y lv →
    WriteProhibitedVia (env.update x slot) y lv := by
  intro hy hvia
  cases hvia with
  | inl hread =>
      rcases hread with ⟨targets, target, hcontains, htarget, hconflict⟩
      exact Or.inl ⟨targets, target,
        EnvContains.update_of_ne hy hcontains, htarget, hconflict⟩
  | inr hwrite =>
      rcases hwrite with ⟨targets, target, hcontains, htarget, hconflict⟩
      exact Or.inr ⟨targets, target,
        EnvContains.update_of_ne hy hcontains, htarget, hconflict⟩

theorem not_writeProhibitedVia_of_update_self {env : Env} {x : Name}
    {slot : EnvSlot} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    ∀ y, y ≠ x → ¬ WriteProhibitedVia env y (.var x) := by
  intro hnotWrite y hy hvia
  exact hnotWrite
    ((WriteProhibitedVia.update_of_ne hy hvia).writeProhibited)

theorem EnvContains.dropLifetime_of_contains {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    (env.dropLifetime lifetime) ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _hlifetime⟩
  exact ⟨slot, henvSlot, hcontainsTy⟩

/-! ## Paper-Facing Section 4 Targets -/

/--
The exact well-formedness invariant needed for runtime references in `T-Const`.

`ValueTyping` for references only consults `σ`; it does not itself say that the
type stored in `σ` is well formed in the current environment.  This predicate
names that missing bridge explicitly.
-/
def StoreTypingRefsWellFormed
    (env : Env) (typing : StoreTyping) (lifetime : Lifetime) : Prop :=
  ∀ (ref : Reference) (ty : Ty),
    typing.tyOf ref.location = some ty →
    WellFormedTy env ty lifetime

/-- `T-Const` value well-formedness from an explicit reference-store invariant. -/
theorem valueTyping_result_wellFormed_of_refs {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreTypingRefsWellFormed env typing lifetime →
    ValueTyping typing value ty →
    WellFormedTy env ty lifetime := by
  intro hrefs htyping
  cases htyping with
  | unit | int => constructor
  | ref hlookup =>
      exact hrefs _ _ hlookup

@[simp] theorem storeTypingRefsWellFormed_empty (env : Env) (lifetime : Lifetime) :
    StoreTypingRefsWellFormed env StoreTyping.empty lifetime := by
  intro ref ty hlookup
  simp [StoreTyping.empty] at hlookup

/--
Source terms contain no reference values, so their typing derivations never
consult the store typing: any store typing types them identically.
-/
theorem TermTyping.retype_of_sourceTerm {env₁ env₂ : Env}
    {typing typing' : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    SourceTerm term →
    TermTyping env₁ typing lifetime term ty env₂ →
    TermTyping env₁ typing' lifetime term ty env₂ := by
  intro hsource htyping
  exact TermTyping.rec
    (motive_1 := fun env _t l term ty env₂ _ =>
      SourceTerm term → TermTyping env typing' l term ty env₂)
    (motive_2 := fun env _t blockLifetime terms ty env₂ _ =>
      SourceTerm (.block blockLifetime terms) →
      TermListTyping env typing' blockLifetime terms ty env₂)
    (fun {_env _typing _lifetime value _ty} hvalueTyping hsource => by
      have hsourceValue : SourceValue value :=
        hsource value (by simp [termValues])
      cases hvalueTyping with
      | unit | int => exact TermTyping.const (by constructor)
      | ref _hlookup => exact absurd hsourceValue (by simp [SourceValue]))
    (fun hLv hcopy hread _hsource =>
      TermTyping.copy hLv hcopy hread)
    (fun hLv hwrite hmove _hsource =>
      TermTyping.move hLv hwrite hmove)
    (fun hLv hmutable hwrite _hsource =>
      TermTyping.mutBorrow hLv hmutable hwrite)
    (fun hLv hread _hsource =>
      TermTyping.immBorrow hLv hread)
    (fun _hterm ih hsource =>
      TermTyping.box (ih (SourceTerm.box_inner hsource)))
    (fun hchild _hterms hwellTy hdrop ih hsource =>
      TermTyping.block hchild (ih hsource) hwellTy hdrop)
    (fun hfresh _hterm hfreshOut hcohObl henv ih hsource =>
      TermTyping.declare hfresh (ih (SourceTerm.declare_inner hsource))
        hfreshOut hcohObl henv)
    (fun _hRhs hLhsPost hshape hwf hwrite hnoStale hranked hcoh hrhsTargets
        hnotWrite ih hsource =>
      TermTyping.assign (ih (SourceTerm.assign_inner hsource)) hLhsPost
        hshape hwf hwrite hnoStale hranked hcoh hrhsTargets hnotWrite)
    (fun _hterm ih hsource =>
      TermListTyping.singleton (ih (SourceTerm.block_head hsource)))
    (fun _hterm _hrest ihHead ihRest hsource =>
      TermListTyping.cons (ihHead (SourceTerm.block_head hsource))
        (ihRest (SourceTerm.block_tail hsource)))
    htyping hsource

theorem LValTyping.containedBorrowTargetsWellFormed {env : Env} {lv : LVal}
    {partialTy : PartialTy} {mutable : Bool} {targets : List LVal}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed htyping hcontainsTop
  refine LValTyping.rec
    (motive_1 := fun _lv partialTy _ _ =>
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime)
    (motive_2 := fun _targetLvs unionTy _ _ =>
      ∀ {mutable targets},
        PartialTyContains unionTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime)
    (by
      intro x slot hslot mutable targets hcontains
      exact EnvContains.borrowTargetsWellFormed hwellFormed
        ⟨slot, hslot, hcontains⟩)
    (by
      intro _lv inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.tyBox hcontains))
    (by
      intro _lv _mutableBorrow _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets _ihBorrow ihTargets _mutable _targets
        hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
        _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
        _mutable _targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion
          (by
            intro mutable targets hcontainsHead
            exact BorrowTargetsWellFormed.inSlot (ihHead hcontainsHead))
          (by
            intro mutable targets hcontainsRest
            exact BorrowTargetsWellFormed.inSlot (ihRest hcontainsRest))
          hcontains)
        (LifetimeOutlives.refl lifetime))
    htyping
    hcontainsTop

theorem LValTyping.containedBorrowTargetsWellFormed_at_lifetime {env : Env}
    {lv : LVal} {partialTy : PartialTy} {valueLifetime : Lifetime}
    {mutable : Bool} {targets : List LVal} :
    ContainedBorrowsWellFormed env →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormed env targets valueLifetime := by
  intro hcontained htyping hcontainsTop
  refine LValTyping.rec
    (motive_1 := fun _lv partialTy valueLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets valueLifetime)
    (motive_2 := fun _targetLvs unionTy targetLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains unionTy (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets targetLifetime)
    (by
      intro x slot hslot mutable targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (hcontained x slot mutable targets hslot ⟨slot, hslot, hcontains⟩)
        (LifetimeOutlives.refl slot.lifetime))
    (by
      intro _lv _inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.tyBox hcontains))
    (by
      intro _lv _mutableBorrow _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets _ihBorrow ihTargets _mutable _targets
        hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
        _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
        _mutable _targets hcontains
      exact BorrowTargetsWellFormedInSlot.toBorrowTargetsWellFormed
        (BorrowTargetsWellFormedInSlot.of_partialTyUnion hunion
          (by
            intro mutable targets hcontainsHead
            exact BorrowTargetsWellFormedInSlot.weaken
              (BorrowTargetsWellFormed.inSlot (ihHead hcontainsHead))
              (LifetimeIntersection.left_le hintersection))
          (by
            intro mutable targets hcontainsRest
            exact BorrowTargetsWellFormedInSlot.weaken
              (BorrowTargetsWellFormed.inSlot (ihRest hcontainsRest))
              (LifetimeIntersection.right_le hintersection))
          hcontains)
        (LifetimeOutlives.refl _))
    htyping
    hcontainsTop

theorem LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
    {env : Env} {lv : LVal} {partialTy : PartialTy}
    {valueLifetime : Lifetime} {mutable : Bool} {targets : List LVal} :
    ContainedBorrowsWellFormedWhenInitialized env →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormedWhenInitialized env targets valueLifetime := by
  intro hcontained htyping hcontainsTop
  refine LValTyping.rec
    (motive_1 := fun _lv partialTy valueLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        BorrowTargetsWellFormedWhenInitialized env targets valueLifetime)
    (motive_2 := fun _targetLvs unionTy targetLifetime _ =>
      ∀ {mutable targets},
        PartialTyContains unionTy (.borrow mutable targets) →
        BorrowTargetsWellFormedWhenInitialized env targets targetLifetime)
    (by
      intro x slot hslot mutable targets hcontains
      exact hcontained x slot mutable targets hslot
        ⟨slot, hslot, hcontains⟩)
    (by
      intro _lv _inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.box hcontains))
    (by
      intro _lv _inner _valueLifetime _htyping ih mutable targets hcontains
      exact ih (PartialTyContains.tyBox hcontains))
    (by
      intro _lv _mutableBorrow _sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets _ihBorrow ihTargets _mutable _targets
        hcontains
      exact ihTargets hcontains)
    (by
      intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
        hcontains
      exact ihTarget hcontains)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
        _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
        _mutable _targets hcontains
      exact BorrowTargetsWellFormedInSlotWhenInitialized.of_partialTyUnion
        hunion
        (by
          intro mutable targets hcontainsHead
          exact BorrowTargetsWellFormedInSlotWhenInitialized.weaken
            (BorrowTargetsWellFormedWhenInitialized.inSlot
              (ihHead hcontainsHead))
            (LifetimeIntersection.left_le hintersection))
        (by
          intro mutable targets hcontainsRest
          exact BorrowTargetsWellFormedInSlotWhenInitialized.weaken
            (BorrowTargetsWellFormedWhenInitialized.inSlot
              (ihRest hcontainsRest))
            (LifetimeIntersection.right_le hintersection))
        hcontains)
    htyping
    hcontainsTop

theorem LValTyping.of_update_fresh_whenContainedInitialized {env : Env}
    {x : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.fresh x →
    (∀ {lv partialTy lifetime},
      LValTyping (env.update x slot) lv partialTy lifetime →
      LVal.base lv ≠ x →
      LValTyping env lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping (env.update x slot) targets partialTy lifetime →
      (∀ target, target ∈ targets → LVal.base target ≠ x) →
      LValTargetsTyping env targets partialTy lifetime) := by
  intro hcontained hfresh
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        LVal.base lv ≠ x →
        LValTyping env lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → LVal.base target ≠ x) →
        LValTargetsTyping env targets partialTy lifetime)
      (by
        intro y envSlot hslot hbaseNe
        have hy : y ≠ x := by
          intro h
          subst h
          exact hbaseNe rfl
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro source inner lifetime _hsource ih hbaseNe
        exact LValTyping.box (ih hbaseNe))
      (by
        intro source inner lifetime _hsource ih hbaseNe
        exact LValTyping.boxFull (ih hbaseNe))
      (by
        intro source mutable targets borrowLifetime targetLifetime targetTy
          _hborrow _htargets ihBorrow ihTargets hbaseNe
        have hborrowOld := ihBorrow hbaseNe
        have htargetBases : ∀ target, target ∈ targets → LVal.base target ≠ x := by
          intro target htarget hbaseEq
          have htargetsWeak :=
            LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
              hcontained hborrowOld PartialTyContains.here
          rcases (htargetsWeak target htarget).1 with
            ⟨baseSlot, hbaseSlot, _houtlives⟩
          rw [hbaseEq] at hbaseSlot
          rw [hfresh] at hbaseSlot
          cases hbaseSlot
        exact LValTyping.borrow hborrowOld (ihTargets htargetBases))
      (by
        intro target ty lifetime _htarget ihTarget htargetBases
        exact LValTargetsTyping.singleton (ihTarget (htargetBases target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest htargetBases
        exact LValTargetsTyping.cons
          (ihHead (htargetBases target (by simp)))
          (ihRest (by
            intro selected hselected
            exact htargetBases selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        LVal.base lv ≠ x →
        LValTyping env lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → LVal.base target ≠ x) →
        LValTargetsTyping env targets partialTy lifetime)
      (by
        intro y envSlot hslot hbaseNe
        have hy : y ≠ x := by
          intro h
          subst h
          exact hbaseNe rfl
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro source inner lifetime _hsource ih hbaseNe
        exact LValTyping.box (ih hbaseNe))
      (by
        intro source inner lifetime _hsource ih hbaseNe
        exact LValTyping.boxFull (ih hbaseNe))
      (by
        intro source mutable targets borrowLifetime targetLifetime targetTy
          _hborrow _htargets ihBorrow ihTargets hbaseNe
        have hborrowOld := ihBorrow hbaseNe
        have htargetBases : ∀ target, target ∈ targets → LVal.base target ≠ x := by
          intro target htarget hbaseEq
          have htargetsWeak :=
            LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
              hcontained hborrowOld PartialTyContains.here
          rcases (htargetsWeak target htarget).1 with
            ⟨baseSlot, hbaseSlot, _houtlives⟩
          rw [hbaseEq] at hbaseSlot
          rw [hfresh] at hbaseSlot
          cases hbaseSlot
        exact LValTyping.borrow hborrowOld (ihTargets htargetBases))
      (by
        intro target ty lifetime _htarget ihTarget htargetBases
        exact LValTargetsTyping.singleton (ihTarget (htargetBases target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest htargetBases
        exact LValTargetsTyping.cons
          (ihHead (htargetBases target (by simp)))
          (ihRest (by
            intro selected hselected
            exact htargetBases selected (by simp [hselected])))
          hunion hintersection)
        htyping

theorem BorrowTargetsInitialized.update_fresh {env : Env} {x : Name}
    {slot : EnvSlot} {targets : List LVal} :
    env.fresh x →
    BorrowTargetsInitialized env targets →
    BorrowTargetsInitialized (env.update x slot) targets := by
  intro hfresh hinitialized target htarget
  rcases hinitialized target htarget with
    ⟨targetTy, targetLifetime, htargetTyping⟩
  exact ⟨targetTy, targetLifetime,
    LValTyping.update_fresh_one (slot := slot) hfresh htargetTyping⟩

theorem BorrowTargetsInitialized.of_update_fresh_whenContainedInitialized
    {env : Env} {x : Name} {slot : EnvSlot} {targets : List LVal} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.fresh x →
    (∀ target, target ∈ targets → LVal.base target ≠ x) →
    BorrowTargetsInitialized (env.update x slot) targets →
    BorrowTargetsInitialized env targets := by
  intro hcontained hfresh htargetBases hinitialized target htarget
  rcases hinitialized target htarget with
    ⟨targetTy, targetLifetime, htargetTyping⟩
  exact ⟨targetTy, targetLifetime,
    (LValTyping.of_update_fresh_whenContainedInitialized hcontained hfresh).1
      htargetTyping (htargetBases target htarget)⟩

theorem ValidPartialValueWhenInitialized.update_fresh_env_of_vars_fresh
    {env : Env} {store : ProgramStore} {x : Name} {slot : EnvSlot}
    {value : PartialValue} {partialTy : PartialTy} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.fresh x →
    x ∉ PartialTy.vars partialTy →
    ValidPartialValueWhenInitialized env store value partialTy →
    ValidPartialValueWhenInitialized (env.update x slot) store value partialTy := by
  intro hcontained hfresh hvarsFresh hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      exact ValidPartialValueWhenInitialized.undefOf hinner hstrength
  | @borrowLive location mutable targets target hinitialized hmem hloc =>
      exact ValidPartialValueWhenInitialized.borrowLive
        (BorrowTargetsInitialized.update_fresh (slot := slot) hfresh hinitialized)
        hmem hloc
  | @borrowStale location mutable targets hstale =>
      have htargetBases : ∀ target, target ∈ targets → LVal.base target ≠ x := by
        intro target htarget hbase
        apply hvarsFresh
        have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
          List.mem_map.mpr ⟨target, htarget, rfl⟩
        have hxMem : x ∈ targets.map LVal.base := by
          simpa [hbase] using hbaseMem
        simpa [PartialTy.vars, Ty.vars] using hxMem
      exact ValidPartialValueWhenInitialized.borrowStale (by
        intro hinitialized
        exact hstale
          (BorrowTargetsInitialized.of_update_fresh_whenContainedInitialized
            hcontained hfresh htargetBases hinitialized))
  | @box location boxSlot inner hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.box hslot
        (ih (by
          intro hmem
          exact hvarsFresh (by simpa [PartialTy.vars] using hmem)))
  | @boxFull location boxSlot ty hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.boxFull hslot
        (ih (by
          intro hmem
          exact hvarsFresh (by simpa [PartialTy.vars, Ty.vars] using hmem)))

theorem BorrowTargetsWellFormedWhenInitialized.update_fresh
    {env : Env} {x : Name} {slot : EnvSlot} {targets : List LVal}
    {lifetime : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.fresh x →
    BorrowTargetsWellFormedWhenInitialized env targets lifetime →
    BorrowTargetsWellFormedWhenInitialized (env.update x slot) targets lifetime := by
  intro hcontained hfresh htargets target htarget
  rcases htargets target htarget with ⟨hbase, hinitialized⟩
  have hbaseNe : LVal.base target ≠ x := by
    intro hbaseEq
    rcases hbase with ⟨baseSlot, hbaseSlot, _houtlives⟩
    rw [hbaseEq] at hbaseSlot
    rw [hfresh] at hbaseSlot
    cases hbaseSlot
  have hbaseUpdated : LValBaseOutlives (env.update x slot) target lifetime := by
    rcases hbase with ⟨baseSlot, hbaseSlot, houtlives⟩
    exact ⟨baseSlot, by simpa [Env.update, hbaseNe] using hbaseSlot, houtlives⟩
  refine ⟨hbaseUpdated, ?_⟩
  intro htargetInitialized
  rcases htargetInitialized with ⟨targetTy, targetLifetime, htargetTyping⟩
  have htargetTypingOld :=
    (LValTyping.of_update_fresh_whenContainedInitialized hcontained hfresh).1
      htargetTyping hbaseNe
  rcases hinitialized ⟨targetTy, targetLifetime, htargetTypingOld⟩ with
    ⟨targetTyOld, targetLifetimeOld, htargetTypingOldSelected,
      htargetOutlives, _hbaseOld⟩
  exact ⟨targetTyOld, targetLifetimeOld,
    LValTyping.update_fresh_one (slot := slot) hfresh htargetTypingOldSelected,
    htargetOutlives, hbaseUpdated⟩

theorem BorrowTargetsWellFormedInSlotWhenInitialized.update_fresh
    {env : Env} {x : Name} {slot : EnvSlot} {targets : List LVal}
    {lifetime : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    env.fresh x →
    BorrowTargetsWellFormedInSlotWhenInitialized env lifetime targets →
    BorrowTargetsWellFormedInSlotWhenInitialized
      (env.update x slot) lifetime targets := by
  exact BorrowTargetsWellFormedWhenInitialized.update_fresh

theorem ContainedBorrowsWellFormedWhenInitialized.update_fresh_ty
    {env : Env} {x : Name} {ty : Ty} {lifetime : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    WellFormedTyWhenInitialized env ty lifetime →
    env.fresh x →
    ContainedBorrowsWellFormedWhenInitialized
      (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hcontained hwellTy hfresh y envSlot mutable targets hslot hcontains
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
      (borrowTargetsWellFormedInSlotWhenInitialized_of_wellFormedTy_contains
        hwellTy hcontainsTy)
  · have hslotOld : env.slotAt y = some envSlot := by
      simpa [Env.update, hy] using hslot
    have hcontainsOld : env ⊢ y ↝ Ty.borrow mutable targets := by
      rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
      have hcontainedOld : env.slotAt y = some containedSlot := by
        simpa [Env.update, hy] using hcontainedSlot
      exact ⟨containedSlot, hcontainedOld, hcontainsTy⟩
    exact BorrowTargetsWellFormedInSlotWhenInitialized.update_fresh
      hcontained hfresh
      (hcontained y envSlot mutable targets hslotOld hcontainsOld)

theorem CoherentWhenInitialized.update_fresh_ty {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    CoherentWhenInitialized env →
    env.fresh x →
    FreshUpdateCoherenceObligations env x ty lifetime →
    CoherentWhenInitialized
      (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hcontained hcoh hfresh hobligations lv mutable targets borrowLifetime
    htyping hinitialized
  by_cases hbase : LVal.base lv = x
  · rcases hobligations.fresh_root_coherent hbase htyping with
      ⟨targetTy, targetLifetime, htargets⟩
    exact ⟨.ty targetTy, targetLifetime, htargets.toMaybe⟩
  · rcases hobligations.old_root_transport hbase htyping with
      ⟨oldBorrowLifetime, htypingOld⟩
    have htargetsOldInitialized : BorrowTargetsInitialized env targets := by
      intro target htarget
      rcases hinitialized target htarget with
        ⟨targetTy, targetLifetime, htargetTyping⟩
      have htargetBaseNe : LVal.base target ≠ x := by
        intro htargetBase
        have htargetsWeak :=
          LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
            hcontained htypingOld PartialTyContains.here
        rcases (htargetsWeak target htarget).1 with
          ⟨baseSlot, hbaseSlot, _houtlives⟩
        rw [htargetBase] at hbaseSlot
        rw [hfresh] at hbaseSlot
        cases hbaseSlot
      exact ⟨targetTy, targetLifetime,
        (LValTyping.of_update_fresh_whenContainedInitialized hcontained hfresh).1
          htargetTyping htargetBaseNe⟩
    rcases hcoh lv mutable targets oldBorrowLifetime htypingOld
        htargetsOldInitialized with
      ⟨targetTy, targetLifetime, htargetsOld⟩
    exact ⟨targetTy, targetLifetime,
      LValTargetsMaybeTyping.update_fresh
        (slot := { ty := .ty ty, lifetime := lifetime }) hfresh htargetsOld⟩

theorem WellFormedEnvWhenInitialized.update_fresh_ty {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env lifetime →
    WellFormedTyWhenInitialized env ty lifetime →
    env.fresh x →
    WellFormedEnvWhenInitialized
      (env.update x { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro hwellEnv hwellTy hfresh
  refine ⟨?_, ?_⟩
  · exact ContainedBorrowsWellFormedWhenInitialized.update_fresh_ty
      hwellEnv.1 hwellTy hfresh
  · intro y envSlot hslot
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

theorem Linearizable.update_fresh_ty_whenInitialized {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env lifetime →
    WellFormedTyWhenInitialized env ty lifetime →
    env.fresh x →
    Linearizable env →
    Linearizable (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hwellEnv hwellTy hfresh hlinear
  obtain ⟨φ, hφ⟩ := hlinear
  have hfreshEq : env.slotAt x = none := hfresh
  have hxnotin : x ∉ Ty.vars ty := by
    intro hx
    obtain ⟨s, hs⟩ := wellFormedTyWhenInitialized_vars_in_env hwellTy x hx
    rw [hfreshEq] at hs
    exact absurd hs (by simp)
  refine ⟨fun n => if n = x then
    (Ty.vars ty).foldr (fun w acc => max (φ w + 1) acc) 0 else φ n, ?_⟩
  intro y slot hslot v hv
  by_cases hy : y = x
  · have hslotEq : slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      rw [hy] at hslot
      simpa [Env.update] using hslot.symm
    have hvty : v ∈ Ty.vars ty := by
      rw [hslotEq] at hv
      simpa [PartialTy.vars] using hv
    have hvx : v ≠ x := fun h => hxnotin (h ▸ hvty)
    simp only [if_neg hvx, if_pos hy]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (mem_foldr_max_succ hvty)
  · have hslotOld : env.slotAt y = some slot := by
      simpa [Env.update, hy] using hslot
    obtain ⟨s, hs⟩ :=
      containedBorrowsWhenInitialized_slot_vars_in_env hwellEnv.1 hslotOld v hv
    have hvx : v ≠ x := by
      intro h
      rw [h, hfreshEq] at hs
      exact absurd hs (by simp)
    simp only [if_neg hy, if_neg hvx]
    exact hφ y slot hslotOld v hv

theorem LValTyping.lifetime_outlives_of_base_outlives {env : Env}
    {current : Lifetime} :
    ContainedBorrowsWellFormed env →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      LValBaseOutlives env lv current →
      lifetime ≤ current) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → LValBaseOutlives env target current) →
      lifetime ≤ current) := by
  intro hcontained
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormed env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormed_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormed env targets current :=
          BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget⟩
          exact hbaseTarget))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormed env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormed_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormed env targets current :=
          BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget⟩
          exact hbaseTarget))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
          _hhead _hrest _hunion hintersection ihHead ihRest hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping

theorem LValTyping.lifetime_outlives_of_base_outlives_one {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    LValTyping env lv partialTy lifetime →
    LValBaseOutlives env lv current →
    lifetime ≤ current := by
  intro hcontained htyping hbase
  exact (LValTyping.lifetime_outlives_of_base_outlives
    (current := current) hcontained).1 htyping hbase

theorem LValTyping.lifetime_outlives_of_base_outlives_whenInitialized
    {env : Env} {current : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      LValBaseOutlives env lv current →
      lifetime ≤ current) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → LValBaseOutlives env target current) →
      lifetime ≤ current) := by
  intro hcontained
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormedWhenInitialized env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormedWhenInitialized env targets current :=
          BorrowTargetsWellFormedWhenInitialized.weaken
            hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          exact (hwellTargets target htarget).1))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime
          _restTy _unionTy _hhead _hrest _hunion hintersection ihHead ihRest
          hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv _partialTy lifetime _ =>
        LValBaseOutlives env lv current → lifetime ≤ current)
      (motive_2 := fun targets _partialTy lifetime _ =>
        (∀ target, target ∈ targets → LValBaseOutlives env target current) →
        lifetime ≤ current)
      (by
        intro x slot hslot hbase
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        have hbaseSlotX : env.slotAt x = some baseSlot := by
          simpa [LVal.base] using hbaseSlot
        have hslotEq : baseSlot = slot := by
          have hsomeEq : some baseSlot = some slot := by
            rw [← hbaseSlotX, hslot]
          exact Option.some.inj hsomeEq
        subst hslotEq
        exact hbaseOutlives)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _inner _lifetime _htyping ih hbase
        exact ih hbase)
      (by
        intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
          hborrow _htargets ihBorrow ihTargets hbase
        have hborrowLifetime : _borrowLifetime ≤ current :=
          ihBorrow hbase
        have hwellTargetsAtBorrow :
            BorrowTargetsWellFormedWhenInitialized env targets _borrowLifetime :=
          LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
            hcontained hborrow PartialTyContains.here
        have hwellTargets :
            BorrowTargetsWellFormedWhenInitialized env targets current :=
          BorrowTargetsWellFormedWhenInitialized.weaken
            hwellTargetsAtBorrow hborrowLifetime
        exact ihTargets (by
          intro target htarget
          exact (hwellTargets target htarget).1))
      (by
        intro target _ty _lifetime _htarget ihTarget hbaseTargets
        exact ihTarget (hbaseTargets target (by simp)))
      (by
        intro target rest _headTy _headLifetime _restLifetime _lifetime
          _restTy _unionTy _hhead _hrest _hunion hintersection ihHead ihRest
          hbaseTargets
        exact LifetimeIntersection.le_of_le hintersection
          (ihHead (hbaseTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hbaseTargets selected (by simp [hselected]))))
      htyping

theorem LValTyping.lifetime_outlives_of_base_outlives_one_whenInitialized
    {env : Env} {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    LValTyping env lv partialTy lifetime →
    LValBaseOutlives env lv current →
    lifetime ≤ current := by
  intro hcontained htyping hbase
  exact (LValTyping.lifetime_outlives_of_base_outlives_whenInitialized
    (current := current) hcontained).1 htyping hbase

theorem LValTyping.borrowTargetsWellFormed {env : Env} {lv : LVal}
    {mutable : Bool} {targets : List LVal}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty (.borrow mutable targets)) valueLifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed htyping
  exact LValTyping.containedBorrowTargetsWellFormed hwellFormed htyping
    PartialTyContains.here

theorem wellFormedTy_of_containedBorrowTargets {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      BorrowTargetsWellFormed env targets lifetime) →
    WellFormedTy env ty lifetime := by
  intro htargets
  exact Ty.rec
    (motive_1 := fun ty =>
      (∀ mutable targets,
        PartialTyContains (.ty ty) (.borrow mutable targets) →
        BorrowTargetsWellFormed env targets lifetime) →
      WellFormedTy env ty lifetime)
    (motive_2 := fun _partialTy => True)
    (by
      intro _htargets
      exact WellFormedTy.unit)
    (by
      intro _htargets
      exact WellFormedTy.int)
    (by
      intro mutable targets htargets
      exact WellFormedTy.borrow (htargets mutable targets PartialTyContains.here))
    (by
      intro inner ih htargets
      exact WellFormedTy.box (ih (by
        intro mutable targets hcontains
        exact htargets mutable targets (PartialTyContains.tyBox hcontains))))
    (by
      intro _ty _ih
      trivial)
    (by
      intro _partialTy _ih
      trivial)
    (by
      intro _shape _ih
      trivial)
    ty htargets

theorem wellFormedTyWhenInitialized_of_containedBorrowTargets {env : Env}
    {ty : Ty} {lifetime : Lifetime} :
    (∀ mutable targets,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      BorrowTargetsWellFormedWhenInitialized env targets lifetime) →
    WellFormedTyWhenInitialized env ty lifetime := by
  intro htargets
  exact Ty.rec
    (motive_1 := fun ty =>
      (∀ mutable targets,
        PartialTyContains (.ty ty) (.borrow mutable targets) →
        BorrowTargetsWellFormedWhenInitialized env targets lifetime) →
      WellFormedTyWhenInitialized env ty lifetime)
    (motive_2 := fun _partialTy => True)
    (by
      intro _htargets
      exact WellFormedTyWhenInitialized.unit)
    (by
      intro _htargets
      exact WellFormedTyWhenInitialized.int)
    (by
      intro mutable targets htargets
      exact WellFormedTyWhenInitialized.borrow
        (htargets mutable targets PartialTyContains.here))
    (by
      intro inner ih htargets
      exact WellFormedTyWhenInitialized.box (ih (by
        intro mutable targets hcontains
        exact htargets mutable targets (PartialTyContains.tyBox hcontains))))
    (by
      intro _ty _ih
      trivial)
    (by
      intro _partialTy _ih
      trivial)
    (by
      intro _shape _ih
      trivial)
    ty htargets

theorem LValTyping.fullTyWellFormed {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    WellFormedTy env ty lifetime := by
  intro hwellFormed htyping
  exact wellFormedTy_of_containedBorrowTargets (by
    intro mutable targets hcontains
    exact LValTyping.containedBorrowTargetsWellFormed hwellFormed htyping
      hcontains)

theorem LValTyping.fullTyWellFormedWhenInitialized {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    WellFormedTyWhenInitialized env ty lifetime := by
  intro hwellFormed htyping
  exact wellFormedTyWhenInitialized_of_containedBorrowTargets (by
    intro mutable targets hcontains
    exact BorrowTargetsWellFormedWhenInitialized.weaken
        (LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
          hwellFormed.1 htyping hcontains)
        (LValTyping.lifetime_outlives_one_of_slots hwellFormed.2 htyping))

/--
The `T-Copy` result type is well formed.

This is intentionally specialized by `copy(T)`: copyable types are only `int`
and immutable borrows, so we do not need a false theorem saying every full type
read from an lval is recursively well formed.
-/
theorem copyBorrowTargetsWellFormed {env : Env} {lv : LVal}
    {targets : List LVal} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty (.borrow false targets)) valueLifetime →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed hLv
  exact LValTyping.borrowTargetsWellFormed hwellFormed hLv

theorem copyTy_result_wellFormed {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    CopyTy ty →
    WellFormedTy env ty lifetime := by
  intro hwellFormed hLv hcopy
  cases hcopy with
  | unit | int => constructor
  | immBorrow =>
      rename_i targets
      have htargets : BorrowTargetsWellFormed env targets lifetime := by
        exact copyBorrowTargetsWellFormed hwellFormed hLv
      exact WellFormedTy.borrow htargets

theorem copyTy_result_wellFormedWhenInitialized {env : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    EnvSlotsOutlive env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    CopyTy ty →
    WellFormedTyWhenInitialized env ty lifetime := by
  intro hcontained houtlives hLv hcopy
  cases hcopy with
  | unit =>
      exact WellFormedTyWhenInitialized.unit
  | int =>
      exact WellFormedTyWhenInitialized.int
  | immBorrow =>
      rename_i targets
      have htargetsAtValueLifetime :
          BorrowTargetsWellFormedWhenInitialized env targets valueLifetime :=
        LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
          hcontained hLv PartialTyContains.here
      exact WellFormedTyWhenInitialized.borrow
        (BorrowTargetsWellFormedWhenInitialized.weaken htargetsAtValueLifetime
          (LValTyping.lifetime_outlives_one_of_slots houtlives hLv))

theorem PartialTyContains.of_strike {path : Path} {source struck : PartialTy}
    {needle : Ty} :
    Strike path source struck →
    PartialTyContains struck needle →
    PartialTyContains source needle := by
  intro hstrike hcontains
  induction path generalizing source struck with
  | nil =>
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains
  | cons _ path ih =>
      cases source with
      | ty sourceTy =>
          cases sourceTy <;> cases struck <;> simp [Strike] at hstrike
          cases hcontains with
          | box hinner =>
              exact PartialTyContains.tyBox (ih hstrike hinner)
      | undef sourceTy =>
          cases struck <;> simp [Strike] at hstrike
      | box inner =>
          cases struck with
          | ty struckTy | undef struckTy =>
              simp [Strike] at hstrike
          | box struckInner =>
              simp [Strike] at hstrike
              cases hcontains with
              | box hinner =>
                  exact PartialTyContains.box (ih hstrike hinner)

theorem WriteLeafTy.not_strike_deref_borrow {env : Env} {path : Path}
    {mutable : Bool} {targets : List LVal} {ty : Ty} {struck : PartialTy} :
    WriteLeafTy env path (.ty (.borrow mutable targets)) ty →
    Strike (path ++ [()]) (.ty (.borrow mutable targets)) struck →
    False := by
  intro hleaf
  cases hleaf with
  | leaf =>
      intro hstrike
      simp [Strike] at hstrike
  | borrow =>
      intro hstrike
      simp [Strike] at hstrike

theorem EnvContains.of_move {env env' : Env} {lv : LVal} {x : Name}
    {ty : Ty} :
    EnvMove env lv env' →
    env' ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hmove hcontains
  rcases hmove with ⟨slot, struck, hslot, hstrike, henv'⟩
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hcontainedSlotEq :
        containedSlot = { slot with ty := struck } := by
      have h :
          { slot with ty := struck } = containedSlot := by
        simpa [henv', Env.update] using hcontainedSlot
      exact h.symm
    subst hcontainedSlotEq
    exact ⟨slot, hslot, PartialTyContains.of_strike hstrike hcontainsTy⟩
  · have hslotOld : env.slotAt x = some containedSlot := by
      simpa [henv', Env.update, hx] using hcontainedSlot
    exact ⟨containedSlot, hslotOld, hcontainsTy⟩

theorem EnvMove.oldSlot_of_newSlot {env env' : Env} {lv : LVal}
    {x : Name} {newSlot : EnvSlot} :
    EnvMove env lv env' →
    env'.slotAt x = some newSlot →
    ∃ oldSlot,
      env.slotAt x = some oldSlot ∧
      oldSlot.lifetime = newSlot.lifetime := by
  intro hmove hnewSlot
  rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
  by_cases hx : x = LVal.base lv
  · subst hx
    have hnewSlotEq :
        newSlot = { moveSlot with ty := struck } := by
      have h :
          { moveSlot with ty := struck } = newSlot := by
        simpa [henv', Env.update] using hnewSlot
      exact h.symm
    subst hnewSlotEq
    exact ⟨moveSlot, hmoveSlot, rfl⟩
  · have holdSlot : env.slotAt x = some newSlot := by
      simpa [henv', Env.update, hx] using hnewSlot
    exact ⟨newSlot, holdSlot, rfl⟩

theorem not_pathConflicts_of_not_writeProhibited_contains {env : Env}
    {lv target : LVal} {x : Name} {mutable : Bool} {targets : List LVal} :
    ¬ WriteProhibited env lv →
    env ⊢ x ↝ Ty.borrow mutable targets →
    target ∈ targets →
    ¬ target ⋈ lv := by
  intro hnotWrite hcontains htarget hconflict
  cases mutable with
  | false =>
      exact hnotWrite (Or.inr ⟨x, targets, target, hcontains, htarget, hconflict⟩)
  | true =>
      exact hnotWrite (Or.inl ⟨x, targets, target, hcontains, htarget, hconflict⟩)

theorem LValTyping.no_writeProhibited_targets {env : Env} {moved : LVal} :
    ¬ WriteProhibited env moved →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        ∀ target,
          target ∈ targets →
          ¬ target ⋈ moved) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {mutable borrowTargets},
        PartialTyContains partialTy (.borrow mutable borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ target ⋈ moved) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.tyBox hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains target
          htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ moved)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains target
          htarget
        exact ih (PartialTyContains.tyBox hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains target
          htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping

theorem LValTyping.move_of_not_pathConflicts {env env' : Env} {moved : LVal} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ¬ lv ⋈ moved →
      LValTyping env' lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ moved) →
      LValTargetsTyping env' targets partialTy lifetime) := by
  intro hmove hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ moved →
        LValTyping env' lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ moved) →
        LValTargetsTyping env' targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
        have hx : x ≠ LVal.base moved := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by simpa [henv', Env.update, hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.boxFull
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ moved := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ moved := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ moved →
        LValTyping env' lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ moved) →
        LValTargetsTyping env' targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        rcases hmove with ⟨moveSlot, struck, hmoveSlot, _hstrike, henv'⟩
        have hx : x ≠ LVal.base moved := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by simpa [henv', Env.update, hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.boxFull
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ moved := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ moved := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

theorem LValTargetsMaybeTyping.move_of_not_pathConflicts {env env' : Env}
    {moved : LVal} {targets : List LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    LValTargetsMaybeTyping env targets partialTy lifetime →
    (∀ target, target ∈ targets → ¬ target ⋈ moved) →
    LValTargetsMaybeTyping env' targets partialTy lifetime := by
  intro hmove hnotWrite htyping hnotTargets
  induction htyping with
  | singleton htarget =>
      exact LValTargetsMaybeTyping.singleton
        ((LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
          htarget (hnotTargets _ (by simp)))
  | cons hhead _hrest hunion hintersection ihRest =>
      exact LValTargetsMaybeTyping.cons
        ((LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
          hhead (hnotTargets _ (by simp)))
        (ihRest (by
          intro target hmem
          exact hnotTargets target (List.mem_cons_of_mem _ hmem)))
        hunion hintersection

theorem LValTyping.update_of_not_pathConflicts {env : Env} {x : Name}
    {slot : EnvSlot} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ¬ lv ⋈ (.var x) →
      LValTyping (env.update x slot) lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
      LValTargetsTyping (env.update x slot) targets partialTy lifetime) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) →
        LValTyping (env.update x slot) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping (env.update x slot) targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.boxFull
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping (env.update x slot) lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow' PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) →
        LValTyping (env.update x slot) lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping (env.update x slot) targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.boxFull
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping (env.update x slot) lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow' PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

theorem LValTyping.of_update_of_not_pathConflicts {env : Env} {x : Name}
    {slot : EnvSlot} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    (∀ {lv partialTy lifetime},
      LValTyping (env.update x slot) lv partialTy lifetime →
      ¬ lv ⋈ (.var x) →
      LValTyping env lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping (env.update x slot) targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
      LValTargetsTyping env targets partialTy lifetime) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) → LValTyping env lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping env targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.boxFull
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping env lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ (.var x) → LValTyping env lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
        LValTargetsTyping env targets partialTy lifetime)
      (by
        intro y envSlot hslot hnotConflict
        have hy : y ≠ x := by
          intro hy
          exact hnotConflict hy
        exact LValTyping.var (by simpa [Env.update, hy] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.boxFull
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ (.var x) := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have hborrow' : LValTyping env lv
            (.ty (.borrow mutable targets)) borrowLifetime :=
          ihBorrow hnotBorrow
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
          intro target htarget
          exact (LValTyping.no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow hborrow'
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

theorem LValTyping.of_move_not_pathConflicts {env env' : Env} {moved : LVal} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    (∀ {lv partialTy lifetime},
      LValTyping env' lv partialTy lifetime →
      ¬ lv ⋈ moved →
      LValTyping env lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env' targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ moved) →
      LValTargetsTyping env targets partialTy lifetime) := by
  intro hmove hnotWrite
  rcases hmove with ⟨slot, struck, hslot, _hstrike, henv'⟩
  subst henv'
  have hrestore :
      (env.update (LVal.base moved) { slot with ty := struck }).update
          (LVal.base moved) slot = env := by
    obtain ⟨g⟩ := env
    simp only [Env.update]
    congr 1
    funext y
    by_cases hy : y = LVal.base moved
    · subst hy
      simpa using hslot.symm
    · simp [hy]
  have hnotWriteVarEnv : ¬ WriteProhibited env (.var (LVal.base moved)) :=
    not_writeProhibited_var_base hnotWrite
  have hnotWriteVar :
      ¬ WriteProhibited
        ((env.update (LVal.base moved) { slot with ty := struck }).update
          (LVal.base moved) slot)
        (.var (LVal.base moved)) := by
    rw [hrestore]
    exact hnotWriteVarEnv
  constructor
  · intro lv partialTy lifetime htyping hnotConflict
    have htypingRestore :
        LValTyping
          ((env.update (LVal.base moved) { slot with ty := struck }).update
            (LVal.base moved) slot)
          lv partialTy lifetime :=
      (LValTyping.update_of_not_pathConflicts hnotWriteVar).1 htyping
        (by simpa [PathConflicts, LVal.base] using hnotConflict)
    rwa [hrestore] at htypingRestore
  · intro targets partialTy lifetime htyping hnotTargets
    have htypingRestore :
        LValTargetsTyping
          ((env.update (LVal.base moved) { slot with ty := struck }).update
            (LVal.base moved) slot)
          targets partialTy lifetime :=
        (LValTyping.update_of_not_pathConflicts hnotWriteVar).2 htyping
      (by
        intro target htarget
        simpa [PathConflicts, LVal.base] using hnotTargets target htarget)
    rwa [hrestore] at htypingRestore

theorem BorrowTargetsInitialized.update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {targets : List LVal} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    BorrowTargetsInitialized env targets →
    (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    BorrowTargetsInitialized (env.update x slot) targets := by
  intro hnotWrite hinitialized hnotTargets target htarget
  rcases hinitialized target htarget with
    ⟨targetTy, targetLifetime, htargetTyping⟩
  exact ⟨targetTy, targetLifetime,
    (LValTyping.update_of_not_pathConflicts (slot := slot) hnotWrite).1
      htargetTyping (hnotTargets target htarget)⟩

theorem BorrowTargetsInitialized.of_update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {targets : List LVal} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    BorrowTargetsInitialized (env.update x slot) targets →
    (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    BorrowTargetsInitialized env targets := by
  intro hnotWrite hinitialized hnotTargets target htarget
  rcases hinitialized target htarget with
    ⟨targetTy, targetLifetime, htargetTyping⟩
  exact ⟨targetTy, targetLifetime,
    (LValTyping.of_update_of_not_pathConflicts (slot := slot) hnotWrite).1
      htargetTyping (hnotTargets target htarget)⟩

theorem ValidPartialValueWhenInitialized.update_env_of_not_pathConflicts
    {env : Env} {store : ProgramStore} {x : Name} {slot : EnvSlot}
    {value : PartialValue} {partialTy : PartialTy} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    x ∉ PartialTy.vars partialTy →
    ValidPartialValueWhenInitialized env store value partialTy →
    ValidPartialValueWhenInitialized (env.update x slot) store value partialTy := by
  intro hnotWriteUpdated hvarsFresh hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      exact ValidPartialValueWhenInitialized.undefOf hinner hstrength
  | @borrowLive location mutable targets target hinitialized hmem hloc =>
      have hnotTargets :
          ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
        intro selected hselected hconflict
        apply hvarsFresh
        have hbaseMem : LVal.base selected ∈ targets.map LVal.base :=
          List.mem_map_of_mem hselected
        have hbaseEq : LVal.base selected = x := by
          simpa [PathConflicts, LVal.base] using hconflict
        simpa [PartialTy.vars, Ty.vars, hbaseEq] using hbaseMem
      exact ValidPartialValueWhenInitialized.borrowLive
        (BorrowTargetsInitialized.update_of_not_pathConflicts
          hnotWriteUpdated hinitialized hnotTargets)
        hmem hloc
  | @borrowStale location mutable targets hstale =>
      have hnotTargets :
          ∀ target, target ∈ targets → ¬ target ⋈ (.var x) := by
        intro selected hselected hconflict
        apply hvarsFresh
        have hbaseMem : LVal.base selected ∈ targets.map LVal.base :=
          List.mem_map_of_mem hselected
        have hbaseEq : LVal.base selected = x := by
          simpa [PathConflicts, LVal.base] using hconflict
        simpa [PartialTy.vars, Ty.vars, hbaseEq] using hbaseMem
      exact ValidPartialValueWhenInitialized.borrowStale (by
        intro hinitialized
        exact hstale
          (BorrowTargetsInitialized.of_update_of_not_pathConflicts
            hnotWriteUpdated hinitialized hnotTargets))
  | @box location boxSlot inner hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.box hslot
        (ih (by
          intro hmem
          exact hvarsFresh (by simpa [PartialTy.vars] using hmem)))
  | @boxFull location boxSlot ty hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.boxFull hslot
        (ih (by
          intro hmem
          exact hvarsFresh (by simpa [PartialTy.vars, Ty.vars] using hmem)))

theorem BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {slotLifetime : Lifetime}
    {targets : List LVal} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    BorrowTargetsWellFormedInSlot (env.update x slot) slotLifetime targets := by
  intro hnotWrite htargets hnotTargets target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  refine ⟨targetTy, targetLifetime,
    (LValTyping.update_of_not_pathConflicts (slot := slot) hnotWrite).1
      htyping (hnotTargets target htarget),
    houtlives, ?_⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  have hbaseNe : LVal.base target ≠ x := by
    intro hbaseEq
    exact hnotTargets target htarget hbaseEq
  have hbaseSlot' :
      (env.update x slot).slotAt (LVal.base target) = some baseSlot := by
    simpa [Env.update, hbaseNe] using hbaseSlot
  exact ⟨baseSlot, hbaseSlot', hbaseOutlives⟩

theorem PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts {env : Env}
    {x : Name} {slot : EnvSlot} {slotLifetime : Lifetime}
    {partialTy : PartialTy} :
    ¬ WriteProhibited (env.update x slot) (.var x) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ {mutable targets},
      PartialTyContains partialTy (.borrow mutable targets) →
      ∀ target, target ∈ targets → ¬ target ⋈ (.var x)) →
    PartialTyBorrowsWellFormedInSlot
      (env.update x slot) slotLifetime partialTy := by
  intro hnotWrite hpartial hnotTargets mutable targets hcontains
  exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
    (slot := slot) hnotWrite (hpartial hcontains)
    (hnotTargets hcontains)

theorem ContainedBorrowsWellFormed.update_slot {env : Env} {x : Name}
    {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot (env.update x slot) slot.lifetime slot.ty →
    ¬ WriteProhibited (env.update x slot) (.var x) →
    ContainedBorrowsWellFormed (env.update x slot) := by
  intro hcontained hslotTargets hnotWrite y resultSlot mutable targets
    hresultSlot hcontains
  by_cases hy : y = x
  · subst hy
    rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hresultSlotEq : resultSlot = slot := by
      have h : slot = resultSlot := by
        simpa [Env.update] using hresultSlot
      exact h.symm
    have hcontainedSlotEq : containedSlot = slot := by
      have h : slot = containedSlot := by
        simpa [Env.update] using hcontainedSlot
      exact h.symm
    have hcontainsSlot : PartialTyContains slot.ty (.borrow mutable targets) := by
      simpa [hcontainedSlotEq] using hcontainsTy
    rw [hresultSlotEq]
    exact hslotTargets hcontainsSlot
  · rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
    have hresultSlotOld : env.slotAt y = some resultSlot := by
      simpa [Env.update, hy] using hresultSlot
    have hcontainedSlotOld : env.slotAt y = some containedSlot := by
      simpa [Env.update, hy] using hcontainedSlot
    have hcontainedSlotEq : containedSlot = resultSlot := by
      have hsomeEq : some containedSlot = some resultSlot := by
        rw [← hcontainedSlotOld, hresultSlotOld]
      exact Option.some.inj hsomeEq
    have htargetsOld :
        BorrowTargetsWellFormedInSlot env resultSlot.lifetime targets := by
      rw [← hcontainedSlotEq]
      exact hcontained y containedSlot mutable targets hcontainedSlotOld
        ⟨containedSlot, hcontainedSlotOld, hcontainsTy⟩
    exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
      (slot := slot) hnotWrite htargetsOld
      (by
        intro target htarget
        exact not_pathConflicts_of_not_writeProhibited_contains
          hnotWrite
          ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
          htarget)

theorem ContainedBorrowsWellFormed.move {env env' : Env} {lv : LVal}
    {lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    ContainedBorrowsWellFormed env' := by
  intro hwellFormed hnotWrite hmove x slot mutable targets hslot hcontains
  rcases EnvMove.oldSlot_of_newSlot hmove hslot with
    ⟨oldSlot, holdSlot, hlifetime⟩
  rcases EnvContains.of_move hmove hcontains with
    ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  have hcontainedOldSlotEq : containedOldSlot = oldSlot := by
    have hsomeEq : some oldSlot = some containedOldSlot := by
      rw [← holdSlot, hcontainedOldSlot]
    injection hsomeEq with heq
    exact heq.symm
  have hlifetimeContained : containedOldSlot.lifetime = slot.lifetime := by
    rw [hcontainedOldSlotEq, hlifetime]
  have htargetsOld :
      BorrowTargetsWellFormedInSlot env containedOldSlot.lifetime targets :=
    hwellFormed.1 x containedOldSlot mutable targets hcontainedOldSlot
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  rw [← hlifetimeContained]
  have hnotTargets : ∀ target, target ∈ targets → ¬ target ⋈ lv := by
    intro target htarget
    exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩ htarget
  intro target htarget
  rcases htargetsOld target htarget with
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
  exact ⟨targetTy, targetLifetime,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
      htyping (hnotTargets target htarget),
    houtlives,
    LValBaseOutlives.move_of_not_pathConflicts
      hmove (hnotTargets target htarget) hbase⟩

theorem BorrowTargetsWellFormed.move_of_no_pathConflicts {env env' : Env}
    {moved : LVal} {targets : List LVal} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    BorrowTargetsWellFormed env targets lifetime →
    (∀ target, target ∈ targets → ¬ target ⋈ moved) →
    BorrowTargetsWellFormed env' targets lifetime := by
  intro hmove hnotWrite htargets hnotTargets
  cases htargets with
  | intro hmembers =>
      refine BorrowTargetsWellFormed.intro ?_
      intro target htarget
      rcases hmembers target htarget with
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
      exact ⟨targetTy, targetLifetime,
        (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
          htyping (hnotTargets target htarget),
        houtlives,
        LValBaseOutlives.move_of_not_pathConflicts
          hmove (hnotTargets target htarget) hbase⟩

theorem WellFormedTy.move_of_no_pathConflicts {env env' : Env}
    {moved : LVal} {ty : Ty} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    WellFormedTy env ty lifetime →
    (∀ mutable targets target,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      target ∈ targets →
      ¬ target ⋈ moved) →
    WellFormedTy env' ty lifetime := by
  intro hmove hnotWrite hwellTy hnotConflicts
  induction hwellTy with
  | unit | int => constructor
  | borrow htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.move_of_no_pathConflicts
          hmove hnotWrite htargets
          (by
            intro target htarget
            exact hnotConflicts _ _ target PartialTyContains.here htarget))
  | box hinner ih =>
      exact WellFormedTy.box (ih (by
        intro mutable targets target hcontains htarget
        exact hnotConflicts mutable targets target
          (PartialTyContains.tyBox hcontains) htarget))

theorem WellFormedTy.move_result {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedTy env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  have hwellTy : WellFormedTy env ty lifetime :=
    LValTyping.fullTyWellFormed hwellFormed hLv
  exact WellFormedTy.move_of_no_pathConflicts hmove hnotWrite hwellTy
    (by
      intro mutable targets target hcontains htarget
      exact (LValTyping.no_writeProhibited_targets hnotWrite).1
        hLv hcontains target htarget)

/-- `Strike` only removes variables (it replaces a sub-value by `undef`). -/
theorem Strike.vars_subset :
    ∀ {path : Path} {ty struck : PartialTy}, Strike path ty struck →
      ∀ v, v ∈ PartialTy.vars struck → v ∈ PartialTy.vars ty := by
  intro path
  induction path with
  | nil =>
      intro ty struck h v hv
      cases ty with
      | ty t =>
          cases struck with
          | undef t' => simp [PartialTy.vars] at hv
          | ty _ | box _ => simp [Strike] at h
      | box _ | undef _ => simp [Strike] at h
    | cons _ rest ih =>
        intro ty struck h v hv
        cases ty with
        | box inner =>
            cases struck with
            | box struck' =>
                simp only [PartialTy.vars] at hv ⊢
                exact ih (show Strike rest inner struck' from h) v hv
            | ty _ | undef _ => simp [Strike] at h
        | ty sourceTy =>
            cases sourceTy with
            | box inner =>
                cases struck with
                | box struck' =>
                    have hv' : v ∈ PartialTy.vars (.ty inner) :=
                      ih (show Strike rest (.ty inner) struck' from h) v
                        (by simpa [PartialTy.vars] using hv)
                    simpa [PartialTy.vars, Ty.vars] using hv'
                | ty _ | undef _ => simp [Strike] at h
            | unit | int | borrow _ _ =>
                cases struck <;> simp [Strike] at h
        | undef _ => simp [Strike] at h

/-- `Linearizable` is preserved by a move (the same rank function works; the
moved slot's type loses variables via `Strike`). -/
theorem Linearizable.move {env env' : Env} {lv : LVal}
    (hmove : EnvMove env lv env') (h : Linearizable env) :
    Linearizable env' := by
  rcases hmove with ⟨slot, struck, hslot, hstrike, henv'⟩
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x s hs
  subst henv'
  by_cases hx : x = LVal.base lv
  · subst hx
    have hseq : s = { slot with ty := struck } := by
      have h := hs
      simpa [Env.update] using h.symm
    subst hseq
    intro v hv
    exact hφ (LVal.base lv) slot hslot v
      (Strike.vars_subset hstrike v (by simpa using hv))
  · have hsenv : env.slotAt x = some s := by
      simpa [Env.update, hx] using hs
    exact hφ x s hsenv

/-- A partial type with no defined `.ty` leaf reachable: every `Strike` result
is of this form, and an lval typing rooted at a struck slot stays in it (so it
can never be a defined borrow). -/
def IsBoxUndef : PartialTy → Prop
  | .ty _ => False
  | .box inner => IsBoxUndef inner
  | .undef _ => True

theorem Strike.isBoxUndef :
    ∀ {path : Path} {ty struck : PartialTy}, Strike path ty struck → IsBoxUndef struck := by
  intro path
  induction path with
  | nil =>
      intro ty struck h
      cases ty with
      | ty t => cases struck with
        | undef _ => trivial
        | ty _ | box _ => simp [Strike] at h
      | box _ | undef _ => simp [Strike] at h
    | cons _ rest ih =>
        intro ty struck h
        cases ty with
        | box inner => cases struck with
          | box struck' =>
              have h' : Strike rest inner struck' := h
              show IsBoxUndef struck'
              exact ih h'
          | ty _ | undef _ => simp [Strike] at h
        | ty sourceTy =>
            cases sourceTy with
            | box inner =>
                cases struck with
                | box struck' =>
                    have h' : Strike rest (.ty inner) struck' := h
                    show IsBoxUndef struck'
                    exact ih h'
                | ty _ | undef _ => simp [Strike] at h
            | unit | int | borrow _ _ =>
                cases struck <;> simp [Strike] at h
        | undef _ => simp [Strike] at h

/-- An lval typed in the moved environment whose base is the moved variable has a
`Strike`-shaped (box/undef) type — never a defined `.ty` (in particular never a
borrow). -/
theorem LValTyping.isBoxUndef_of_base_moved {env : Env} {lv : LVal}
    {slot : EnvSlot} {struck : PartialTy}
    (_hslot : env.slotAt (LVal.base lv) = some slot)
    (hstrike : Strike (LVal.path lv) slot.ty struck) :
    ∀ {lv' p lf},
      LValTyping (env.update (LVal.base lv) { slot with ty := struck }) lv' p lf →
      LVal.base lv' = LVal.base lv → IsBoxUndef p := by
  intro lv' p lf h
  refine LValTyping.rec
    (motive_1 := fun lv' p _ _ => LVal.base lv' = LVal.base lv → IsBoxUndef p)
    (motive_2 := fun _ _ _ _ => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons h
  · intro y ySlot hySlot hbase
    have hy : y = LVal.base lv := by simpa [LVal.base] using hbase
    subst hy
    have : ySlot = { slot with ty := struck } := by
      simpa [Env.update] using hySlot.symm
    subst this
    exact Strike.isBoxUndef hstrike
  · intro lv'' inner lifetime _htyping ih hbase
    have := ih (by simpa [LVal.base] using hbase)
    simpa [IsBoxUndef] using this
  · intro lv'' inner lifetime _htyping ih hbase
    have := ih (by simpa [LVal.base] using hbase)
    simp [IsBoxUndef] at this
  · intro lv'' mutable targets _bLf _tLf _tTy hborrow _htargets ihBorrow _ihTargets hbase
    have := ihBorrow (by simpa [LVal.base] using hbase)
    simp [IsBoxUndef] at this
  · intro _ _ _ _ _; trivial
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _; trivial

theorem BorrowTargetsInitialized.of_move {env env' : Env} {moved : LVal}
    {targets : List LVal} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    BorrowTargetsInitialized env' targets →
    BorrowTargetsInitialized env targets := by
  intro hmove hnotWrite htargets target htarget
  rcases htargets target htarget with ⟨targetTy, targetLifetime, htargetTyping⟩
  have hmoveCopy := hmove
  rcases hmoveCopy with ⟨slot, struck, hslot, hstrike, henv'⟩
  subst henv'
  by_cases hconflict : target ⋈ moved
  · have hboxUndef :=
      LValTyping.isBoxUndef_of_base_moved hslot hstrike htargetTyping
        (by simpa [PathConflicts, LVal.base] using hconflict)
    simp [IsBoxUndef] at hboxUndef
  · exact ⟨targetTy, targetLifetime,
      (LValTyping.of_move_not_pathConflicts
        (moved := moved) hmove hnotWrite).1 htargetTyping hconflict⟩

theorem ValidPartialValueWhenInitialized.move_env {env env' : Env}
    {store : ProgramStore} {moved : LVal} {value : PartialValue}
    {ty : PartialTy} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    ValidPartialValueWhenInitialized env store value ty →
    ValidPartialValueWhenInitialized env' store value ty := by
  intro hmove hnotWrite hvalid
  induction hvalid with
  | unit =>
      exact ValidPartialValueWhenInitialized.unit
  | int =>
      exact ValidPartialValueWhenInitialized.int
  | undef =>
      exact ValidPartialValueWhenInitialized.undef
  | undefOf hinner hstrength =>
      exact ValidPartialValueWhenInitialized.undefOf hinner hstrength
  | @borrowLive location mutable targets target hinitialized hmem hloc =>
      by_cases hpost : BorrowTargetsInitialized env' targets
      · exact ValidPartialValueWhenInitialized.borrowLive
          (location := location) (mutable := mutable) (targets := targets)
          (target := target) hpost hmem hloc
      · exact ValidPartialValueWhenInitialized.borrowStale
          (location := location) (mutable := mutable) (targets := targets) hpost
  | @borrowStale location mutable targets hstale =>
      have hpost : ¬ BorrowTargetsInitialized env' targets := by
        intro hinit
        exact hstale (BorrowTargetsInitialized.of_move hmove hnotWrite hinit)
      exact ValidPartialValueWhenInitialized.borrowStale
        (location := location) (mutable := mutable) (targets := targets) hpost
  | box hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.box hslot ih
  | boxFull hslot _hinner ih =>
      exact ValidPartialValueWhenInitialized.boxFull hslot ih

/--
Move Preservation for well-formed environments, used in Lemma 4.9.

This is the proof obligation described in the `T-Move` case of the paper:
`move(Γ, w)` replaces the moved component by `undef`, and the
`¬writeProhibited(Γ, w)` premise prevents this from invalidating any surviving
borrow target.
-/
theorem move_preserves_wellFormed {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedEnv env' lifetime ∧ WellFormedTy env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  refine ⟨⟨ContainedBorrowsWellFormed.move hwellFormed hnotWrite hmove,
      EnvSlotsOutlive.move hwellFormed.2 hmove⟩,
    WellFormedTy.move_result hwellFormed hLv hnotWrite hmove⟩

theorem BorrowTargetsWellFormedWhenInitialized.move_of_no_pathConflicts
    {env env' : Env} {moved : LVal} {targets : List LVal}
    {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    BorrowTargetsWellFormedWhenInitialized env targets lifetime →
    (∀ target, target ∈ targets → ¬ target ⋈ moved) →
    BorrowTargetsWellFormedWhenInitialized env' targets lifetime := by
  intro hmove hnotWrite htargets hnotTargets target htarget
  rcases htargets target htarget with ⟨hbase, hinitialized⟩
  have hnotTarget : ¬ target ⋈ moved := hnotTargets target htarget
  have hbase' : LValBaseOutlives env' target lifetime :=
    LValBaseOutlives.move_of_not_pathConflicts hmove hnotTarget hbase
  refine ⟨hbase', ?_⟩
  intro htargetInitialized'
  rcases htargetInitialized' with
    ⟨targetTy', targetLifetime', htargetTyping'⟩
  have htargetTypingOld :
      LValTyping env target (.ty targetTy') targetLifetime' :=
    (LValTyping.of_move_not_pathConflicts hmove hnotWrite).1
      htargetTyping' hnotTarget
  rcases hinitialized ⟨targetTy', targetLifetime', htargetTypingOld⟩ with
    ⟨targetTy, targetLifetime, htargetTyping, houtlives, htargetBase⟩
  exact ⟨targetTy, targetLifetime,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
      htargetTyping hnotTarget,
    houtlives,
    LValBaseOutlives.move_of_not_pathConflicts hmove hnotTarget htargetBase⟩

theorem BorrowTargetsWellFormedInSlotWhenInitialized.move_of_no_pathConflicts
    {env env' : Env} {moved : LVal} {targets : List LVal}
    {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    BorrowTargetsWellFormedInSlotWhenInitialized env lifetime targets →
    (∀ target, target ∈ targets → ¬ target ⋈ moved) →
    BorrowTargetsWellFormedInSlotWhenInitialized env' lifetime targets := by
  exact BorrowTargetsWellFormedWhenInitialized.move_of_no_pathConflicts

theorem ContainedBorrowsWellFormedWhenInitialized.move {env env' : Env}
    {lv : LVal} {lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env lifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    ContainedBorrowsWellFormedWhenInitialized env' := by
  intro hwellFormed hnotWrite hmove x slot mutable targets hslot hcontains
  rcases EnvMove.oldSlot_of_newSlot hmove hslot with
    ⟨oldSlot, holdSlot, hlifetime⟩
  rcases EnvContains.of_move hmove hcontains with
    ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  have hcontainedOldSlotEq : containedOldSlot = oldSlot := by
    have hsomeEq : some oldSlot = some containedOldSlot := by
      rw [← holdSlot, hcontainedOldSlot]
    injection hsomeEq with heq
    exact heq.symm
  have hlifetimeContained : containedOldSlot.lifetime = slot.lifetime := by
    rw [hcontainedOldSlotEq, hlifetime]
  have htargetsOld :
      BorrowTargetsWellFormedInSlotWhenInitialized
        env containedOldSlot.lifetime targets :=
    hwellFormed.1 x containedOldSlot mutable targets hcontainedOldSlot
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩
  rw [← hlifetimeContained]
  have hnotTargets : ∀ target, target ∈ targets → ¬ target ⋈ lv := by
    intro target htarget
    exact not_pathConflicts_of_not_writeProhibited_contains hnotWrite
      ⟨containedOldSlot, hcontainedOldSlot, hcontainsOldTy⟩ htarget
  exact BorrowTargetsWellFormedInSlotWhenInitialized.move_of_no_pathConflicts
    hmove hnotWrite htargetsOld hnotTargets

theorem WellFormedTyWhenInitialized.move_of_no_pathConflicts
    {env env' : Env} {moved : LVal} {ty : Ty} {lifetime : Lifetime} :
    EnvMove env moved env' →
    ¬ WriteProhibited env moved →
    WellFormedTyWhenInitialized env ty lifetime →
    (∀ mutable targets target,
      PartialTyContains (.ty ty) (.borrow mutable targets) →
      target ∈ targets →
      ¬ target ⋈ moved) →
    WellFormedTyWhenInitialized env' ty lifetime := by
  intro hmove hnotWrite hwellTy hnotConflicts
  induction hwellTy with
  | unit | int =>
      constructor
  | borrow htargets =>
      exact WellFormedTyWhenInitialized.borrow
        (BorrowTargetsWellFormedWhenInitialized.move_of_no_pathConflicts
          hmove hnotWrite htargets
          (by
            intro target htarget
            exact hnotConflicts _ _ target PartialTyContains.here htarget))
  | box _hinner ih =>
      exact WellFormedTyWhenInitialized.box (ih (by
        intro mutable targets target hcontains htarget
        exact hnotConflicts mutable targets target
          (PartialTyContains.tyBox hcontains) htarget))

theorem WellFormedTyWhenInitialized.move_result {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedTyWhenInitialized env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  have hwellTy : WellFormedTyWhenInitialized env ty lifetime :=
    LValTyping.fullTyWellFormedWhenInitialized hwellFormed hLv
  exact WellFormedTyWhenInitialized.move_of_no_pathConflicts
    hmove hnotWrite hwellTy
    (by
      intro mutable targets target hcontains htarget
      exact (LValTyping.no_writeProhibited_targets hnotWrite).1
        hLv hcontains target htarget)

theorem CoherentWhenInitialized.move {env env' : Env} {lv : LVal}
    {lifetime : Lifetime}
    (_hwellFormed : WellFormedEnvWhenInitialized env lifetime)
    (hnotWrite : ¬ WriteProhibited env lv)
    (hmove : EnvMove env lv env')
    (hcohEnv : CoherentWhenInitialized env) :
    CoherentWhenInitialized env' := by
  have hmoveCopy := hmove
  rcases hmoveCopy with ⟨slot, struck, hslot, hstrike, henv'⟩
  subst henv'
  intro lv' m T bLf hty' hinitialized'
  have hbaseNe : ¬ lv' ⋈ lv := by
    intro hbeq
    have hbu := LValTyping.isBoxUndef_of_base_moved hslot hstrike hty'
      (by simpa [PathConflicts, LVal.base] using hbeq)
    simp [IsBoxUndef] at hbu
  have htyEnv : LValTyping env lv' (.ty (.borrow m T)) bLf :=
    (LValTyping.of_move_not_pathConflicts hmove hnotWrite).1 hty' hbaseNe
  have hnotTargets : ∀ target, target ∈ T → ¬ target ⋈ lv := by
    intro target htarget
    exact (LValTyping.no_writeProhibited_targets hnotWrite).1 htyEnv
      PartialTyContains.here target htarget
  have hinitializedEnv : BorrowTargetsInitialized env T := by
    intro target htarget
    rcases hinitialized' target htarget with
      ⟨targetTy, targetLifetime, htargetTyping'⟩
    exact ⟨targetTy, targetLifetime,
      (LValTyping.of_move_not_pathConflicts hmove hnotWrite).1
        htargetTyping' (hnotTargets target htarget)⟩
  rcases hcohEnv lv' m T bLf htyEnv hinitializedEnv with
    ⟨ty, lt, htgtsEnv⟩
  exact ⟨ty, lt,
    LValTargetsMaybeTyping.move_of_not_pathConflicts
      hmove hnotWrite htgtsEnv hnotTargets⟩

theorem move_preserves_wellFormedWhenInitialized {env env' : Env} {lv : LVal}
    {ty : Ty} {valueLifetime lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedEnvWhenInitialized env' lifetime ∧
      WellFormedTyWhenInitialized env' ty lifetime := by
  intro hwellFormed hLv hnotWrite hmove
  refine ⟨⟨ContainedBorrowsWellFormedWhenInitialized.move
        hwellFormed hnotWrite hmove,
      EnvSlotsOutlive.move hwellFormed.2 hmove⟩,
    WellFormedTyWhenInitialized.move_result hwellFormed hLv hnotWrite hmove⟩

def BorrowTargetsTransport (source target : Env) : Prop :=
  ∀ {slotLifetime targets},
    BorrowTargetsWellFormedInSlot source slotLifetime targets →
    BorrowTargetsWellFormedInSlot target slotLifetime targets

@[refl] theorem BorrowTargetsTransport.refl (env : Env) :
    BorrowTargetsTransport env env := by
  intro slotLifetime targets htargets
  exact htargets

theorem BorrowTargetsTransport.trans {first second third : Env} :
    BorrowTargetsTransport first second →
    BorrowTargetsTransport second third →
    BorrowTargetsTransport first third := by
  intro hfirstSecond hsecondThird slotLifetime targets htargets
  exact hsecondThird (hfirstSecond htargets)

def DropFullLValTypingTransport (env : Env) (parent child : Lifetime) : Prop :=
  ∀ {lv targetTy targetLifetime},
    LValBaseOutlives env lv parent →
    LValTyping env lv (.ty targetTy) targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv (.ty targetTy) targetLifetime

/--
Appendix Lemma 9.5 target-stability fragment.

If an lval is typed in a well-formed block body, its base slot survives the
enclosing parent lifetime, and the reached location also lives at the parent
side, then dropping the immediate child lifetime preserves the lval typing.
-/
theorem LValTyping.dropLifetime_child_of_base_outlives {env : Env}
    {parent child : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    LValBaseOutlives env lv parent →
    LValTyping env lv partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv partialTy targetLifetime := by
  intro hchild hwellBody hbase htyping houtlives
  have htransport :
      (∀ {lv partialTy lifetime},
        LValTyping env lv partialTy lifetime →
        LValBaseOutlives env lv parent →
        lifetime ≤ parent →
        LValTyping (env.dropLifetime child) lv partialTy lifetime) ∧
      (∀ {targets partialTy lifetime},
        LValTargetsTyping env targets partialTy lifetime →
        (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
        lifetime ≤ parent →
        LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime) := by
    constructor
    · intro lv partialTy lifetime htyping
      exact LValTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
        (motive_2 := fun targets partialTy lifetime _ =>
          (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
          lifetime ≤ parent →
          LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
        (by
          intro x slot hslot _hbase houtlives
          exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
            ⟨hslot, by
              intro hslotLifetime
              subst hslotLifetime
              exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.box (ih hbase houtlives))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.boxFull (ih hbase houtlives))
        (by
          intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
            hborrow _htargets ihBorrow ihTargets hbase houtlives
          have hborrowLifetime : _borrowLifetime ≤ parent :=
            LValTyping.lifetime_outlives_of_base_outlives_one
              hwellBody.1 hborrow hbase
          have hwellTargetsAtBorrow :
              BorrowTargetsWellFormed env targets _borrowLifetime :=
            LValTyping.containedBorrowTargetsWellFormed_at_lifetime
              hwellBody.1 hborrow PartialTyContains.here
          have hwellTargets :
              BorrowTargetsWellFormed env targets parent :=
            BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
          exact LValTyping.borrow
            (ihBorrow hbase hborrowLifetime)
            (ihTargets
              (by
                intro target htarget
                rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
                exact hbaseTarget)
              houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
            _hhead _hrest hunion hintersection ihHead ihRest hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
    · intro targets partialTy lifetime htyping
      exact LValTargetsTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
        (motive_2 := fun targets partialTy lifetime _ =>
          (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
          lifetime ≤ parent →
          LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
        (by
          intro x slot hslot _hbase houtlives
          exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
            ⟨hslot, by
              intro hslotLifetime
              subst hslotLifetime
              exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.box (ih hbase houtlives))
        (by
          intro _lv _inner _lifetime _htyping ih hbase houtlives
          exact LValTyping.boxFull (ih hbase houtlives))
        (by
          intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
            hborrow _htargets ihBorrow ihTargets hbase houtlives
          have hborrowLifetime : _borrowLifetime ≤ parent :=
            LValTyping.lifetime_outlives_of_base_outlives_one
              hwellBody.1 hborrow hbase
          have hwellTargetsAtBorrow :
              BorrowTargetsWellFormed env targets _borrowLifetime :=
            LValTyping.containedBorrowTargetsWellFormed_at_lifetime
              hwellBody.1 hborrow PartialTyContains.here
          have hwellTargets :
              BorrowTargetsWellFormed env targets parent :=
            BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetime
          exact LValTyping.borrow
            (ihBorrow hbase hborrowLifetime)
            (ihTargets
              (by
                intro target htarget
                rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
                exact hbaseTarget)
              houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy _unionTy
            _hhead _hrest hunion hintersection ihHead ihRest hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
  exact htransport.1 htyping hbase houtlives

theorem LValTargetsTyping.dropLifetime_child_of_member_base_outlives {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hbaseTargets htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy targetLifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      targetLifetime ≤ parent →
      LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget hbaseTargets houtlives
    exact LValTargetsTyping.singleton
      (LValTyping.dropLifetime_child_of_base_outlives
        hchild hwellBody (hbaseTargets target (by simp)) htarget houtlives)
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest hbaseTargets houtlives
    exact LValTargetsTyping.cons
      (LValTyping.dropLifetime_child_of_base_outlives hchild hwellBody
        (hbaseTargets target (by simp)) hhead
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives))
      (ihRest
        (by
          intro selected hselected
          exact hbaseTargets selected (by simp [hselected]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives))
      hunion hintersection

theorem LValTargetsTyping.dropLifetime_child_of_wellFormedTargets {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    BorrowTargetsWellFormed env targets parent →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hwellTargets htyping houtlives
  exact LValTargetsTyping.dropLifetime_child_of_member_base_outlives
    hchild hwellBody
    (by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
        ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbase⟩
      exact hbase)
    htyping houtlives

theorem LValTargetsMaybeTyping.lifetime_outlives_of_base_outlives {env : Env}
    {current : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    LValTargetsMaybeTyping env targets partialTy targetLifetime →
    (∀ target, target ∈ targets → LValBaseOutlives env target current) →
    targetLifetime ≤ current := by
  intro hcontained htyping hbaseTargets
  induction htyping with
  | singleton htarget =>
      exact LValTyping.lifetime_outlives_of_base_outlives_one hcontained
        htarget (hbaseTargets _ (by simp))
  | cons hhead _hrest _hunion hintersection ihRest =>
      exact LifetimeIntersection.le_of_le hintersection
        (LValTyping.lifetime_outlives_of_base_outlives_one hcontained
          hhead (hbaseTargets _ (by simp)))
        (ihRest (by
          intro selected hselected
          exact hbaseTargets selected (List.mem_cons_of_mem _ hselected)))

theorem LValTargetsMaybeTyping.dropLifetime_child_of_member_base_outlives
    {env : Env} {parent child : Lifetime} {targets : List LVal}
    {partialTy : PartialTy} {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsMaybeTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsMaybeTyping (env.dropLifetime child) targets partialTy
      targetLifetime := by
  intro hchild hwellBody hbaseTargets htyping houtlives
  induction htyping with
  | singleton htarget =>
      exact LValTargetsMaybeTyping.singleton
        (LValTyping.dropLifetime_child_of_base_outlives
          hchild hwellBody (hbaseTargets _ (by simp)) htarget houtlives)
  | cons hhead _hrest hunion hintersection ihRest =>
      exact LValTargetsMaybeTyping.cons
        (LValTyping.dropLifetime_child_of_base_outlives
          hchild hwellBody (hbaseTargets _ (by simp)) hhead
          (LifetimeOutlives.trans
            (LifetimeIntersection.left_le hintersection) houtlives))
        (ihRest
          (by
            intro selected hselected
            exact hbaseTargets selected (List.mem_cons_of_mem _ hselected))
          (LifetimeOutlives.trans
            (LifetimeIntersection.right_le hintersection) houtlives))
        hunion hintersection

theorem LValTargetsMaybeTyping.dropLifetime_child_of_wellFormedTargets
    {env : Env} {parent child : Lifetime} {targets : List LVal}
    {partialTy : PartialTy} {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    BorrowTargetsWellFormed env targets parent →
    LValTargetsMaybeTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsMaybeTyping (env.dropLifetime child) targets partialTy
      targetLifetime := by
  intro hchild hwellBody hwellTargets htyping houtlives
  exact LValTargetsMaybeTyping.dropLifetime_child_of_member_base_outlives
    hchild hwellBody
    (by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellTargets target htarget with
        ⟨_targetTy, _selectedLifetime, _htargetTyping, _htargetOutlives, hbase⟩
      exact hbase)
    htyping houtlives

/-- Backward typing across a lifetime drop: `dropLifetime` only *removes* slots
(leaving the rest unchanged), so any typing in the dropped environment also holds
in the original. -/
theorem LValTyping.of_dropLifetime {env : Env} {child : Lifetime}
    {lv : LVal} {p : PartialTy} {lf : Lifetime}
    (h : LValTyping (env.dropLifetime child) lv p lf) : LValTyping env lv p lf := by
  refine LValTyping.rec
    (motive_1 := fun lv p lf _ => LValTyping env lv p lf)
    (motive_2 := fun targets p lf _ => LValTargetsTyping env targets p lf)
    ?var ?box ?boxFull ?borrow ?singleton ?cons h
  · intro x slot hslot
    rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _⟩
    exact LValTyping.var henvSlot
  · intro _lv _inner _lifetime _htyping ih
    exact LValTyping.box ih
  · intro _lv _inner _lifetime _htyping ih
    exact LValTyping.boxFull ih
  · intro _lv _mutable _targets _bLf _tLf _tTy _hborrow _htargets ihBorrow ihTargets
    exact LValTyping.borrow ihBorrow ihTargets
  · intro _target _ty _lifetime _htarget ih
    exact LValTargetsTyping.singleton ih
  · intro _target _rest _headTy _headLf _restLf _lf _restTy _unionTy
      _hhead _hrest hunion hint ihHead ihRest
    exact LValTargetsTyping.cons ihHead ihRest hunion hint

theorem LValTargetsTyping.dropLifetime_child_of_transport {env : Env}
    {parent child : Lifetime} {targets : List LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    DropFullLValTypingTransport env parent child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro htransport hbaseTargets htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy targetLifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      targetLifetime ≤ parent →
      LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget hbaseTargets houtlives
    exact LValTargetsTyping.singleton
      (htransport (hbaseTargets target (by simp)) htarget houtlives)
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest hbaseTargets houtlives
    exact LValTargetsTyping.cons
      (htransport (hbaseTargets target (by simp)) hhead
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives))
      (ihRest
        (by
          intro selected hselected
          exact hbaseTargets selected (by simp [hselected]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives))
      hunion hintersection

theorem BorrowTargetsWellFormedInSlot.dropLifetime_child_of_transport
    {env : Env} {parent child slotLifetime : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    slotLifetime ≤ parent →
    BorrowTargetsWellFormedInSlot (env.dropLifetime child) slotLifetime targets := by
  intro hchild htransport htargets hslotParent target htarget
  rcases htargets target htarget with
    ⟨targetTy, targetLifetime, htyping, htargetOutlivesSlot, hbase⟩
  have hbaseParent : LValBaseOutlives env target parent := by
    rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
    exact ⟨baseSlot, hbaseSlot,
      LifetimeOutlives.trans hbaseOutlives hslotParent⟩
  refine ⟨targetTy, targetLifetime,
    htransport hbaseParent htyping
      (LifetimeOutlives.trans htargetOutlivesSlot hslotParent),
    htargetOutlivesSlot, ?_⟩
  exact LValBaseOutlives.dropLifetime_child hchild hslotParent hbase

theorem BorrowTargetsWellFormed.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormed env targets parent →
    BorrowTargetsWellFormed (env.dropLifetime child) targets parent := by
  intro hchild htransport htargets
  cases htargets with
  | intro hmembers =>
      refine BorrowTargetsWellFormed.intro ?_
      intro target htarget
      rcases hmembers target htarget with
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
      have hbaseParent : LValBaseOutlives env target parent := by
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        exact ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
      refine ⟨targetTy, targetLifetime,
        htransport hbaseParent htyping houtlives, houtlives, ?_⟩
      exact
        LValBaseOutlives.dropLifetime_child hchild
          (LifetimeOutlives.refl parent) hbase

theorem WellFormedTy.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    DropFullLValTypingTransport env parent child →
    WellFormedTy env ty parent →
    WellFormedTy (env.dropLifetime child) ty parent := by
  intro hchild htransport hwellTy
  induction hwellTy with
  | unit | int => constructor
  | borrow htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.dropLifetime_child_of_transport
          hchild htransport htargets)
  | box _hinner ih =>
      exact WellFormedTy.box (ih hchild htransport)

theorem ContainedBorrowsWellFormed.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    DropFullLValTypingTransport env parent child →
    ContainedBorrowsWellFormed (env.dropLifetime child) := by
  intro hchild hwellBody htransport x slot mutable targets hslot hcontains
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨holdSlot, hslotNeChild⟩
  have holdContains : env ⊢ x ↝ Ty.borrow mutable targets :=
    EnvContains.dropLifetime_of_contains hcontains
  have hslotParent : slot.lifetime ≤ parent :=
      LifetimeChild.parent_of_outlives_child_ne hchild
        (hwellBody.2 x slot holdSlot) hslotNeChild
  exact BorrowTargetsWellFormedInSlot.dropLifetime_child_of_transport
    hchild
    htransport
    (hwellBody.1 x slot mutable targets holdSlot holdContains)
    hslotParent

/-- `Linearizable` is preserved by a lifetime drop (the same rank function works;
`dropLifetime` only removes slots). -/
theorem Linearizable.dropLifetime_child {env : Env} {child : Lifetime}
    (h : Linearizable env) : Linearizable (env.dropLifetime child) := by
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _⟩
  exact hφ x slot henvSlot

/--
Block drop preservation for well-formed environments, used in the `T-Block`
case of Lemma 4.9.

This is the environment side of Appendix Lemma 9.5 together with the
`Γ₂ ⊢ T ≽ l` premise from `T-Block`: dropping the block lifetime removes locals
without invalidating the result type at the enclosing lifetime.
-/
theorem Env.dropLifetime_preserves_wellFormed_child {env env' : Env}
    {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    WellFormedTy env ty parent →
    env' = env.dropLifetime child →
    WellFormedEnv env' parent ∧ WellFormedTy env' ty parent := by
  intro hchild hwellBody hwellTy hdrop
  subst hdrop
  have htransport : DropFullLValTypingTransport env parent child := by
    intro lv targetTy targetLifetime hbase htyping houtlives
    exact LValTyping.dropLifetime_child_of_base_outlives
      hchild hwellBody hbase htyping houtlives
  refine ⟨
      ⟨ContainedBorrowsWellFormed.dropLifetime_child_of_transport
          hchild hwellBody htransport,
        EnvSlotsOutlive.dropLifetime_child hchild hwellBody.2⟩,
      WellFormedTy.dropLifetime_child_of_transport hchild htransport hwellTy⟩

theorem block_preserves_wellFormed {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₂ blockLifetime →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnv env₃ lifetime ∧ WellFormedTy env₃ ty lifetime := by
  intro hchild hwellBody _hterms hwellTy hdrop
  exact Env.dropLifetime_preserves_wellFormed_child hchild hwellBody hwellTy hdrop

theorem LValTyping.dropLifetime_child_of_base_outlives_whenInitialized
    {env : Env} {parent child : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    LValBaseOutlives env lv parent →
    LValTyping env lv partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv partialTy targetLifetime := by
  intro hchild hwellBody hbase htyping houtlives
  have htransport :
      (∀ {lv partialTy lifetime},
        LValTyping env lv partialTy lifetime →
        LValBaseOutlives env lv parent →
        lifetime ≤ parent →
        LValTyping (env.dropLifetime child) lv partialTy lifetime) ∧
      (∀ {targets partialTy lifetime},
        LValTargetsTyping env targets partialTy lifetime →
        (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
        lifetime ≤ parent →
        LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime) := by
    constructor
    · intro lv partialTy lifetime htyping
      exact LValTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
          (motive_2 := fun targets partialTy lifetime _ =>
            (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
            lifetime ≤ parent →
            LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
          (by
            intro x slot hslot _hbase houtlives
            exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
              ⟨hslot, by
                intro hslotLifetime
                subst hslotLifetime
                exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
          (by
            intro _lv _inner _lifetime _htyping ih hbase houtlives
            exact LValTyping.box (ih hbase houtlives))
          (by
            intro _lv _inner _lifetime _htyping ih hbase houtlives
            exact LValTyping.boxFull (ih hbase houtlives))
          (by
            intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
              hborrow _htargets ihBorrow ihTargets hbase houtlives
            have hborrowLifetime : _borrowLifetime ≤ parent :=
              LValTyping.lifetime_outlives_of_base_outlives_one_whenInitialized
                hwellBody.1 hborrow hbase
            have hwellTargetsAtBorrow :
                BorrowTargetsWellFormedWhenInitialized env targets _borrowLifetime :=
              LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
                hwellBody.1 hborrow PartialTyContains.here
            have hwellTargets :
                BorrowTargetsWellFormedWhenInitialized env targets parent :=
              BorrowTargetsWellFormedWhenInitialized.weaken
                hwellTargetsAtBorrow hborrowLifetime
            exact LValTyping.borrow
              (ihBorrow hbase hborrowLifetime)
              (ihTargets
                (by
                  intro target htarget
                  exact (hwellTargets target htarget).1)
                houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime
            _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
            hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
    · intro targets partialTy lifetime htyping
      exact LValTargetsTyping.rec
        (motive_1 := fun lv partialTy lifetime _ =>
          LValBaseOutlives env lv parent →
          lifetime ≤ parent →
          LValTyping (env.dropLifetime child) lv partialTy lifetime)
          (motive_2 := fun targets partialTy lifetime _ =>
            (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
            lifetime ≤ parent →
            LValTargetsTyping (env.dropLifetime child) targets partialTy lifetime)
          (by
            intro x slot hslot _hbase houtlives
            exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
              ⟨hslot, by
                intro hslotLifetime
                subst hslotLifetime
                exact LifetimeChild.not_child_outlives_parent hchild houtlives⟩))
          (by
            intro _lv _inner _lifetime _htyping ih hbase houtlives
            exact LValTyping.box (ih hbase houtlives))
          (by
            intro _lv _inner _lifetime _htyping ih hbase houtlives
            exact LValTyping.boxFull (ih hbase houtlives))
          (by
            intro _lv _mutable targets _borrowLifetime _targetLifetime _targetTy
              hborrow _htargets ihBorrow ihTargets hbase houtlives
            have hborrowLifetime : _borrowLifetime ≤ parent :=
              LValTyping.lifetime_outlives_of_base_outlives_one_whenInitialized
                hwellBody.1 hborrow hbase
            have hwellTargetsAtBorrow :
                BorrowTargetsWellFormedWhenInitialized env targets _borrowLifetime :=
              LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
                hwellBody.1 hborrow PartialTyContains.here
            have hwellTargets :
                BorrowTargetsWellFormedWhenInitialized env targets parent :=
              BorrowTargetsWellFormedWhenInitialized.weaken
                hwellTargetsAtBorrow hborrowLifetime
            exact LValTyping.borrow
              (ihBorrow hbase hborrowLifetime)
              (ihTargets
                (by
                  intro target htarget
                  exact (hwellTargets target htarget).1)
                houtlives))
        (by
          intro target _ty _lifetime htarget ihTarget hbaseTargets houtlives
          exact LValTargetsTyping.singleton
            (ihTarget (hbaseTargets target (by simp)) houtlives))
        (by
          intro target rest _headTy _headLifetime _restLifetime _lifetime
            _restTy _unionTy _hhead _hrest hunion hintersection ihHead ihRest
            hbaseTargets houtlives
          exact LValTargetsTyping.cons
            (ihHead (hbaseTargets target (by simp))
              (LifetimeOutlives.trans
                (LifetimeIntersection.left_le hintersection) houtlives))
            (ihRest
              (by
                intro selected hselected
                exact hbaseTargets selected (by simp [hselected]))
              (LifetimeOutlives.trans
                (LifetimeIntersection.right_le hintersection) houtlives))
            hunion hintersection)
        htyping
  exact htransport.1 htyping hbase houtlives

theorem LValTargetsTyping.dropLifetime_child_of_member_base_outlives_whenInitialized
    {env : Env} {parent child : Lifetime} {targets : List LVal}
    {partialTy : PartialTy} {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hbaseTargets htyping houtlives
  refine LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy targetLifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      targetLifetime ≤ parent →
      LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _inner _lifetime _htyping _ih
    trivial
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow _ihTargets
    trivial
  · intro target ty lifetime htarget _ihTarget hbaseTargets houtlives
    exact LValTargetsTyping.singleton
      (LValTyping.dropLifetime_child_of_base_outlives_whenInitialized
        hchild hwellBody (hbaseTargets target (by simp)) htarget houtlives)
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead _hrest hunion hintersection _ihHead ihRest hbaseTargets houtlives
    exact LValTargetsTyping.cons
      (LValTyping.dropLifetime_child_of_base_outlives_whenInitialized
        hchild hwellBody (hbaseTargets target (by simp)) hhead
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) houtlives))
      (ihRest
        (by
          intro selected hselected
          exact hbaseTargets selected (by simp [hselected]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) houtlives))
      hunion hintersection

theorem LValTargetsTyping.dropLifetime_child_of_wellFormedTargetsWhenInitialized
    {env : Env} {parent child : Lifetime} {targets : List LVal}
    {partialTy : PartialTy} {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    BorrowTargetsWellFormedWhenInitialized env targets parent →
    LValTargetsTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsTyping (env.dropLifetime child) targets partialTy targetLifetime := by
  intro hchild hwellBody hwellTargets htyping houtlives
  exact LValTargetsTyping.dropLifetime_child_of_member_base_outlives_whenInitialized
    hchild hwellBody
    (by
      intro target htarget
      exact (hwellTargets target htarget).1)
    htyping houtlives

theorem LValTargetsMaybeTyping.lifetime_outlives_of_base_outlives_whenInitialized
    {env : Env} {current : Lifetime} {targets : List LVal}
    {partialTy : PartialTy} {targetLifetime : Lifetime} :
    ContainedBorrowsWellFormedWhenInitialized env →
    LValTargetsMaybeTyping env targets partialTy targetLifetime →
    (∀ target, target ∈ targets → LValBaseOutlives env target current) →
    targetLifetime ≤ current := by
  intro hcontained htyping hbaseTargets
  induction htyping with
  | singleton htarget =>
      exact LValTyping.lifetime_outlives_of_base_outlives_one_whenInitialized
        hcontained htarget (hbaseTargets _ (by simp))
  | cons hhead _hrest _hunion hintersection ihRest =>
      exact LifetimeIntersection.le_of_le hintersection
        (LValTyping.lifetime_outlives_of_base_outlives_one_whenInitialized
          hcontained hhead (hbaseTargets _ (by simp)))
        (ihRest (by
          intro selected hselected
          exact hbaseTargets selected (List.mem_cons_of_mem _ hselected)))

theorem LValTargetsMaybeTyping.dropLifetime_child_of_member_base_outlives_whenInitialized
    {env : Env} {parent child : Lifetime} {targets : List LVal}
    {partialTy : PartialTy} {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
    LValTargetsMaybeTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsMaybeTyping (env.dropLifetime child) targets partialTy
      targetLifetime := by
  intro hchild hwellBody hbaseTargets htyping houtlives
  induction htyping with
  | singleton htarget =>
      exact LValTargetsMaybeTyping.singleton
        (LValTyping.dropLifetime_child_of_base_outlives_whenInitialized
          hchild hwellBody (hbaseTargets _ (by simp)) htarget houtlives)
  | cons hhead _hrest hunion hintersection ihRest =>
      exact LValTargetsMaybeTyping.cons
        (LValTyping.dropLifetime_child_of_base_outlives_whenInitialized
          hchild hwellBody (hbaseTargets _ (by simp)) hhead
          (LifetimeOutlives.trans
            (LifetimeIntersection.left_le hintersection) houtlives))
        (ihRest
          (by
            intro selected hselected
            exact hbaseTargets selected (List.mem_cons_of_mem _ hselected))
          (LifetimeOutlives.trans
            (LifetimeIntersection.right_le hintersection) houtlives))
        hunion hintersection

theorem LValTargetsMaybeTyping.dropLifetime_child_of_wellFormedTargetsWhenInitialized
    {env : Env} {parent child : Lifetime} {targets : List LVal}
    {partialTy : PartialTy} {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    BorrowTargetsWellFormedWhenInitialized env targets parent →
    LValTargetsMaybeTyping env targets partialTy targetLifetime →
    targetLifetime ≤ parent →
    LValTargetsMaybeTyping (env.dropLifetime child) targets partialTy
      targetLifetime := by
  intro hchild hwellBody hwellTargets htyping houtlives
  exact LValTargetsMaybeTyping.dropLifetime_child_of_member_base_outlives_whenInitialized
    hchild hwellBody
    (by
      intro target htarget
      exact (hwellTargets target htarget).1)
    htyping houtlives

theorem BorrowTargetsWellFormedInSlotWhenInitialized.dropLifetime_child_of_transport
    {env : Env} {parent child slotLifetime : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormedInSlotWhenInitialized env slotLifetime targets →
    slotLifetime ≤ parent →
    BorrowTargetsWellFormedInSlotWhenInitialized
      (env.dropLifetime child) slotLifetime targets := by
  intro hchild hwellBody htransport htargets hslotParent target htarget
  rcases htargets target htarget with ⟨hbase, hinitialized⟩
  have hbaseParent : LValBaseOutlives env target parent := by
    rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
    exact ⟨baseSlot, hbaseSlot,
      LifetimeOutlives.trans hbaseOutlives hslotParent⟩
  have hbaseDropped : LValBaseOutlives (env.dropLifetime child) target slotLifetime :=
    LValBaseOutlives.dropLifetime_child hchild hslotParent hbase
  refine ⟨hbaseDropped, ?_⟩
  intro htargetInitializedDropped
  rcases htargetInitializedDropped with
    ⟨targetTyDropped, targetLifetimeDropped, htargetTypingDropped⟩
  have htargetTypingEnv :
      LValTyping env target (.ty targetTyDropped) targetLifetimeDropped :=
    LValTyping.of_dropLifetime htargetTypingDropped
  rcases hinitialized ⟨targetTyDropped, targetLifetimeDropped, htargetTypingEnv⟩ with
    ⟨targetTy, targetLifetime, htargetTyping, houtlives, _hbaseTarget⟩
  exact ⟨targetTy, targetLifetime,
    htransport hbaseParent htargetTyping
      (LifetimeOutlives.trans houtlives hslotParent),
    houtlives,
    hbaseDropped⟩

theorem BorrowTargetsWellFormedWhenInitialized.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {targets : List LVal} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    DropFullLValTypingTransport env parent child →
    BorrowTargetsWellFormedWhenInitialized env targets parent →
    BorrowTargetsWellFormedWhenInitialized (env.dropLifetime child) targets parent := by
  intro hchild hwellBody htransport htargets
  exact BorrowTargetsWellFormedInSlotWhenInitialized.dropLifetime_child_of_transport
    hchild hwellBody htransport htargets (LifetimeOutlives.refl parent)

theorem WellFormedTyWhenInitialized.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    DropFullLValTypingTransport env parent child →
    WellFormedTyWhenInitialized env ty parent →
    WellFormedTyWhenInitialized (env.dropLifetime child) ty parent := by
  intro hchild hwellBody htransport hwellTy
  induction hwellTy with
  | unit | int =>
      constructor
  | borrow htargets =>
      exact WellFormedTyWhenInitialized.borrow
        (BorrowTargetsWellFormedWhenInitialized.dropLifetime_child_of_transport
          hchild hwellBody htransport htargets)
  | box _hinner ih =>
      exact WellFormedTyWhenInitialized.box (ih hchild htransport)

theorem ContainedBorrowsWellFormedWhenInitialized.dropLifetime_child_of_transport
    {env : Env} {parent child : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    DropFullLValTypingTransport env parent child →
    ContainedBorrowsWellFormedWhenInitialized (env.dropLifetime child) := by
  intro hchild hwellBody htransport x slot mutable targets hslot hcontains
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨holdSlot, hslotNeChild⟩
  have holdContains : env ⊢ x ↝ Ty.borrow mutable targets :=
    EnvContains.dropLifetime_of_contains hcontains
  have hslotParent : slot.lifetime ≤ parent :=
      LifetimeChild.parent_of_outlives_child_ne hchild
        (hwellBody.2 x slot holdSlot) hslotNeChild
  exact BorrowTargetsWellFormedInSlotWhenInitialized.dropLifetime_child_of_transport
    hchild
    hwellBody
    htransport
    (hwellBody.1 x slot mutable targets holdSlot holdContains)
    hslotParent

theorem CoherentWhenInitialized.dropLifetime_child {env : Env}
    {parent child : Lifetime}
    (hchild : LifetimeChild parent child)
    (hwellBody : WellFormedEnvWhenInitialized env child)
    (hcohEnv : CoherentWhenInitialized env) :
    CoherentWhenInitialized (env.dropLifetime child) := by
  intro lv m T bLf hty hinitialized
  have htyEnv := LValTyping.of_dropLifetime hty
  have hinitializedEnv : BorrowTargetsInitialized env T := by
    intro target htarget
    rcases hinitialized target htarget with
      ⟨targetTy, targetLifetime, htargetTyping⟩
    exact ⟨targetTy, targetLifetime, LValTyping.of_dropLifetime htargetTyping⟩
  rcases hcohEnv lv m T bLf htyEnv hinitializedEnv with ⟨ty, lt, htgtsEnv⟩
  rcases LValTyping.base_slot_exists hty with ⟨dslot, hdslot⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hdslot with ⟨henvBase, hneChild⟩
  have hbaseParent : LValBaseOutlives env lv parent := by
    rcases LValTyping.base_outlives_one_of_slots hwellBody.2 htyEnv with
      ⟨bslot, hbslot, hble⟩
    have hEq : dslot = bslot := Option.some.inj (henvBase.symm.trans hbslot)
    exact ⟨bslot, hbslot,
      LifetimeChild.parent_of_outlives_child_ne hchild hble (hEq ▸ hneChild)⟩
  have hbLfParent : bLf ≤ parent :=
    LValTyping.lifetime_outlives_of_base_outlives_one_whenInitialized
      hwellBody.1 htyEnv hbaseParent
  have hwellT : BorrowTargetsWellFormedWhenInitialized env T parent :=
    BorrowTargetsWellFormedWhenInitialized.weaken
      (LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
        hwellBody.1 htyEnv PartialTyContains.here)
      hbLfParent
  have hltParent : lt ≤ parent :=
    LValTargetsMaybeTyping.lifetime_outlives_of_base_outlives_whenInitialized
      hwellBody.1 htgtsEnv (by
        intro target htarget
        exact (hwellT target htarget).1)
  exact ⟨ty, lt,
    LValTargetsMaybeTyping.dropLifetime_child_of_wellFormedTargetsWhenInitialized
      hchild hwellBody hwellT htgtsEnv hltParent⟩

theorem Env.dropLifetime_preserves_wellFormedWhenInitialized_child
    {env env' : Env} {parent child : Lifetime} {ty : Ty} :
    LifetimeChild parent child →
    WellFormedEnvWhenInitialized env child →
    WellFormedTyWhenInitialized env ty parent →
    env' = env.dropLifetime child →
    WellFormedEnvWhenInitialized env' parent ∧
      WellFormedTyWhenInitialized env' ty parent := by
  intro hchild hwellBody hwellTy hdrop
  subst hdrop
  have htransport : DropFullLValTypingTransport env parent child := by
    intro lv targetTy targetLifetime hbase htyping houtlives
    exact LValTyping.dropLifetime_child_of_base_outlives_whenInitialized
      hchild hwellBody hbase htyping houtlives
  refine ⟨
      ⟨ContainedBorrowsWellFormedWhenInitialized.dropLifetime_child_of_transport
          hchild hwellBody htransport,
        EnvSlotsOutlive.dropLifetime_child hchild hwellBody.2⟩,
      WellFormedTyWhenInitialized.dropLifetime_child_of_transport
        hchild hwellBody htransport hwellTy⟩

theorem block_preserves_wellFormedWhenInitialized {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnvWhenInitialized env₂ blockLifetime →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    WellFormedTyWhenInitialized env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnvWhenInitialized env₃ lifetime ∧
      WellFormedTyWhenInitialized env₃ ty lifetime := by
  intro hchild hwellBody _hterms hwellTy hdrop
  exact Env.dropLifetime_preserves_wellFormedWhenInitialized_child
    hchild hwellBody hwellTy hdrop

/-! ### CBWF-derivation keystone: single-lval typing determinism (up to `eqv`)
and target-union monotonicity.

These lemmas let us derive contained-borrow well-formedness of write and join
results from the concrete shape evidence available in each proof path.  The
current weak join theorem below avoids the old `EnvJoinSameShape` typing
premise for `T-If`; the full-strength compatibility lemma still accepts it
explicitly when callers need the older invariant. -/

/-- `eqv` of full types is at least as strong as the strengthening preorder. -/
theorem ty_eqv_imp_strengthens : ∀ {a b : Ty},
    Ty.eqv a b → PartialTyStrengthens (.ty a) (.ty b)
  | .unit, b, h => by
      cases b <;> first | exact PartialTyStrengthens.reflex | simp [Ty.eqv] at h
  | .int, b, h => by
      cases b <;> first | exact PartialTyStrengthens.reflex | simp [Ty.eqv] at h
  | .borrow m ta, b, h => by
      cases b with
      | borrow m' tb =>
          obtain ⟨rfl, hsub, _⟩ := h
          exact PartialTyStrengthens.borrow hsub
      | unit => simp [Ty.eqv] at h
      | int => simp [Ty.eqv] at h
      | box _ => simp [Ty.eqv] at h
  | .box a0, b, h => by
      cases b with
      | box b0 =>
          exact PartialTyStrengthens.tyBox
            (ty_eqv_imp_strengthens (a := a0) (b := b0) (by simpa [Ty.eqv] using h))
      | unit => simp [Ty.eqv] at h
      | int => simp [Ty.eqv] at h
      | borrow _ _ => simp [Ty.eqv] at h

/-- Antisymmetry of the strengthening preorder on full types, modulo `eqv`. -/
theorem ty_eqv_of_le_le : ∀ {a b : Ty},
    PartialTyStrengthens (.ty a) (.ty b) →
    PartialTyStrengthens (.ty b) (.ty a) → Ty.eqv a b
  | .unit, _, hab, _ => by cases hab; exact Ty.eqv_refl _
  | .int, _, hab, _ => by cases hab; exact Ty.eqv_refl _
  | .borrow m ta, _, hab, hba => by
      cases hab with
      | reflex => exact Ty.eqv_refl _
      | borrow hsub =>
          cases hba with
          | reflex => exact Ty.eqv_refl _
          | borrow hsub' => exact ⟨rfl, hsub, hsub'⟩
  | .box a0, _, hab, hba => by
      cases hab with
      | reflex => exact Ty.eqv_refl _
      | tyBox hinner =>
          cases hba with
          | reflex => exact Ty.eqv_refl _
          | tyBox hinner' => exact ty_eqv_of_le_le (a := a0) hinner hinner'

/-- `eqv` composes into strengthening on the left. -/
theorem ty_eqv_strengthens_trans {a τ b : Ty} :
    Ty.eqv a τ → PartialTyStrengthens (.ty τ) (.ty b) →
    PartialTyStrengthens (.ty a) (.ty b) :=
  fun heqv hstr => partialTyStrengthens_trans (ty_eqv_imp_strengthens heqv) hstr

/-- **Target-union monotonicity.**  If two borrow-target lists are jointly typed
in the same environment, the smaller list's joint output type strengthens to
the larger list's, provided each shared target is typed determinately (up to
`eqv`).  This is the "least" half of the union LUB, transported across `⊆`. -/
theorem lvalTargetsTyping_union_mono {env : Env} {W' : List LVal} {b : Ty}
    {lb : Lifetime}
    (h2 : LValTargetsTyping env W' (.ty b) lb)
    (hdet : ∀ t, t ∈ W' → ∀ {q1 m1 q2 m2 : _},
      LValTyping env t q1 m1 → LValTyping env t q2 m2 → PartialTy.eqv q1 q2)
    {W : List LVal} {pty : PartialTy} {la : Lifetime}
    (h1 : LValTargetsTyping env W pty la) :
    W ⊆ W' → ∀ a, pty = .ty a → PartialTyStrengthens (.ty a) (.ty b) := by
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun W pty _ _ =>
      W ⊆ W' → ∀ a, pty = .ty a → PartialTyStrengthens (.ty a) (.ty b))
      (by intro _ _ _; trivial)
      (by intro _ _ _ _ _; trivial)
      (by intro _ _ _ _ _; trivial)
      (by intro _ _ _ _ _ _ _ _ _ _; trivial)
    (by
      intro t ty lifetime htyping _ihTarget hsub a ha
      cases ha
      have htmem : t ∈ W' := hsub (by simp)
      rcases lvalTargetsTyping_member_strengthens h2 t htmem with
        ⟨τ, lτ, htτ, hstrτ⟩
      have heq : PartialTy.eqv (.ty ty) (.ty τ) := hdet t htmem htyping htτ
      exact ty_eqv_strengthens_trans (by simpa [PartialTy.eqv] using heq) hstrτ)
    (by
      intro t rest headTy headLife restLife lifetime restTy unionTy
        hhead hrest hunion _hinter _ihhead ihrest hsub a ha
      subst ha
      have htmem : t ∈ W' := hsub (by simp)
      rcases lvalTargetsTyping_member_strengthens h2 t htmem with
        ⟨τ, lτ, htτ, hstrτ⟩
      have heqHead : PartialTy.eqv (.ty headTy) (.ty τ) := hdet t htmem hhead htτ
      have hheadLe : PartialTyStrengthens (.ty headTy) (.ty b) :=
        ty_eqv_strengthens_trans (by simpa [PartialTy.eqv] using heqHead) hstrτ
      obtain ⟨restU, hrestU⟩ := LValTargetsTyping.output_full hrest
      have hrestLe : PartialTyStrengthens (.ty restU) (.ty b) :=
        ihrest (fun t ht => hsub (List.mem_cons_of_mem _ ht)) restU hrestU
      rw [hrestU] at hunion
      exact hunion.2 (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hheadLe
        · exact hrestLe))
    h1

/-- If every member typing of a target list strengthens some upper type, then
the target-list union also strengthens that upper type. -/
theorem lvalTargetsTyping_strengthens_of_all_members {env : Env}
    {targets : List LVal} {pty upper : PartialTy} {lifetime : Lifetime}
    (htargets : LValTargetsTyping env targets pty lifetime)
    (hmember : ∀ target, target ∈ targets → ∀ targetTy targetLifetime,
      LValTyping env target (.ty targetTy) targetLifetime →
        PartialTyStrengthens (.ty targetTy) upper) :
    PartialTyStrengthens pty upper := by
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun targets pty _ _ =>
      (∀ target, target ∈ targets → ∀ targetTy targetLifetime,
        LValTyping env target (.ty targetTy) targetLifetime →
          PartialTyStrengthens (.ty targetTy) upper) →
      PartialTyStrengthens pty upper)
      (by intro _ _ _; trivial)
      (by intro _ _ _ _ _; trivial)
      (by intro _ _ _ _ _; trivial)
      (by intro _ _ _ _ _ _ _ _ _ _; trivial)
    (by
      intro target targetTy targetLifetime htyping _ih hmember
      exact hmember target (by simp) targetTy targetLifetime htyping)
    (by
      intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
        hhead hrest hunion _hintersection _ihHead ihRest hmember
      have hheadLe : PartialTyStrengthens (.ty headTy) upper :=
        hmember target (by simp) headTy headLifetime hhead
      have hrestLe : PartialTyStrengthens restTy upper :=
        ihRest (by
          intro selected hselected selectedTy selectedLifetime hselectedTyping
          exact hmember selected (List.mem_cons_of_mem _ hselected)
            selectedTy selectedLifetime hselectedTyping)
      exact hunion.2 (by
        intro candidate hcandidate
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · cases hcandidate
          exact hheadLe
        · cases hcandidate
          exact hrestLe))
    htargets hmember

/-- **Single-lval typing determinism (up to `eqv`).**  In a linearizable
environment two typings of the same lvalue assign `eqv`-equivalent output types.
Proved by strong induction on the linearization rank of the lvalue's base (with a
structural inner induction for the box/borrow chain). -/
theorem lvalTyping_eqv_of_linearizedBy {env : Env} {φ : Name → Nat}
    (hφ : LinearizedBy φ env) :
    ∀ {lv : LVal} {p1 l1 p2 l2}, LValTyping env lv p1 l1 →
      LValTyping env lv p2 l2 → PartialTy.eqv p1 p2 := by
  have key : ∀ n, ∀ lv : LVal, φ (LVal.base lv) ≤ n →
      ∀ {p1 l1 p2 l2}, LValTyping env lv p1 l1 → LValTyping env lv p2 l2 →
        PartialTy.eqv p1 p2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IHn =>
      intro lv
      induction lv with
      | var x =>
          intro _hle p1 l1 p2 l2 h1 h2
          rcases LValTyping.var_inv h1 with ⟨s1, hs1, ht1, _hl1⟩
          rcases LValTyping.var_inv h2 with ⟨s2, hs2, ht2, _hl2⟩
          have hseq : s1 = s2 := Option.some.inj (hs1.symm.trans hs2)
          subst hseq
          subst ht1; subst ht2
          exact PartialTy.eqv_refl _
      | deref w IHw =>
          intro hle p1 l1 p2 l2 h1 h2
          have hbase : LVal.base w = LVal.base (.deref w) := rfl
          have hleW : φ (LVal.base w) ≤ n := hle
          cases h1 with
          | box hb1 =>
              cases h2 with
              | box hb2 =>
                  have hweq : PartialTy.eqv (.box p1) (.box p2) :=
                    IHw hleW hb1 hb2
                  simpa [PartialTy.eqv] using hweq
              | boxFull hb2 =>
                  have hweq := IHw hleW hb1 hb2
                  simp [PartialTy.eqv] at hweq
              | borrow hb2 _ht2 =>
                  have hweq := IHw hleW hb1 hb2
                  simp [PartialTy.eqv] at hweq
          | boxFull hb1 =>
              cases h2 with
              | box hb2 =>
                  have hweq := IHw hleW hb1 hb2
                  simp [PartialTy.eqv] at hweq
              | boxFull hb2 =>
                  rename_i inner1 inner2
                  have hweq := IHw hleW hb1 hb2
                  simpa [PartialTy.eqv, Ty.eqv] using hweq
              | borrow hb2 _ht2 =>
                  have hweq := IHw hleW hb1 hb2
                  simp [PartialTy.eqv, Ty.eqv] at hweq
          | borrow hb1 ht1 =>
              cases h2 with
              | box hb2 =>
                  have hweq := IHw hleW hb1 hb2
                  simp [PartialTy.eqv] at hweq
              | boxFull hb2 =>
                  have hweq := IHw hleW hb1 hb2
                  simp [PartialTy.eqv, Ty.eqv] at hweq
              | borrow hb2 ht2 =>
                  rename_i m1 W1 bl1 m2 W2 bl2
                  have hweq := IHw hleW hb1 hb2
                  obtain ⟨hm, hsub12, hsub21⟩ : m1 = m2 ∧ W1 ⊆ W2 ∧ W2 ⊆ W1 := by
                    simpa [PartialTy.eqv, Ty.eqv] using hweq
                  subst hm
                  obtain ⟨a, ha⟩ := LValTargetsTyping.output_full ht1
                  obtain ⟨c, hc⟩ := LValTargetsTyping.output_full ht2
                  subst ha; subst hc
                  -- determinism for each target (rank strictly below base w)
                  have hr1 : ∀ t, t ∈ W1 → φ (LVal.base t) < n := fun t ht =>
                    lt_of_lt_of_le
                      ((lvalTyping_vars_rank_lt hφ).1 hb1 (LVal.base t)
                        (mem_partialTy_vars_iff.mpr
                          ⟨m1, W1, t, PartialTyContains.here, ht, rfl⟩)) hleW
                  have hr2 : ∀ t, t ∈ W2 → φ (LVal.base t) < n := fun t ht =>
                    lt_of_lt_of_le
                      ((lvalTyping_vars_rank_lt hφ).1 hb2 (LVal.base t)
                        (mem_partialTy_vars_iff.mpr
                          ⟨m1, W2, t, PartialTyContains.here, ht, rfl⟩)) hleW
                  have hdet1 : ∀ t, t ∈ W1 → ∀ {q1 m1' q2 m2'},
                      LValTyping env t q1 m1' → LValTyping env t q2 m2' →
                      PartialTy.eqv q1 q2 := by
                    intro t ht q1 m1' q2 m2' hq1 hq2
                    exact IHn (φ (LVal.base t)) (hr1 t ht) t (le_refl _) hq1 hq2
                  have hdet2 : ∀ t, t ∈ W2 → ∀ {q1 m1' q2 m2'},
                      LValTyping env t q1 m1' → LValTyping env t q2 m2' →
                      PartialTy.eqv q1 q2 := by
                    intro t ht q1 m1' q2 m2' hq1 hq2
                    exact IHn (φ (LVal.base t)) (hr2 t ht) t (le_refl _) hq1 hq2
                  have hac : PartialTyStrengthens (.ty a) (.ty c) :=
                    lvalTargetsTyping_union_mono ht2 hdet2 ht1 hsub12 a rfl
                  have hca : PartialTyStrengthens (.ty c) (.ty a) :=
                    lvalTargetsTyping_union_mono ht1 hdet1 ht2 hsub21 c rfl
                  exact ty_eqv_of_le_le hac hca
  intro lv p1 l1 p2 l2 h1 h2
  exact key (φ (LVal.base lv)) lv (le_refl _) h1 h2

theorem LValTyping.partialTy_eq_ty_of_initialized_linearizedBy {env : Env}
    {φ : Name → Nat} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    LinearizedBy φ env →
    LValTyping env lv partialTy lifetime →
    (∃ ty targetLifetime, LValTyping env lv (.ty ty) targetLifetime) →
    ∃ ty, partialTy = .ty ty := by
  intro hφ htyping hinitialized
  rcases hinitialized with ⟨targetTy, targetLifetime, htarget⟩
  have heqv : PartialTy.eqv partialTy (.ty targetTy) :=
    lvalTyping_eqv_of_linearizedBy hφ htyping htarget
  cases partialTy with
  | ty ty => exact ⟨ty, rfl⟩
  | box _ => simp [PartialTy.eqv] at heqv
  | undef _ => simp [PartialTy.eqv] at heqv

theorem LValTargetsMaybeTyping.full_of_initialized_linearizedBy {env : Env}
    {φ : Name → Nat} {targets : List LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    LinearizedBy φ env →
    LValTargetsMaybeTyping env targets partialTy lifetime →
    BorrowTargetsInitialized env targets →
    ∃ ty, partialTy = .ty ty ∧
      LValTargetsTyping env targets (.ty ty) lifetime := by
  intro hφ htyping hinitialized
  induction htyping with
  | singleton htarget =>
      rcases LValTyping.partialTy_eq_ty_of_initialized_linearizedBy
          hφ htarget (hinitialized _ (by simp)) with
        ⟨targetTy, htargetTy⟩
      subst htargetTy
      exact ⟨targetTy, rfl, LValTargetsTyping.singleton htarget⟩
  | cons hhead _hrest hunion hintersection ihRest =>
      rcases LValTyping.partialTy_eq_ty_of_initialized_linearizedBy
          hφ hhead (hinitialized _ (by simp)) with
        ⟨headTyFull, hheadTy⟩
      subst hheadTy
      rcases ihRest (by
          intro target htarget
          exact hinitialized target (List.mem_cons_of_mem _ htarget)) with
        ⟨restTyFull, hrestTy, hrestFull⟩
      subst hrestTy
      rcases PartialTyUnion.ty_ty_full hunion with ⟨unionFull, hunionFull⟩
      subst hunionFull
      exact ⟨unionFull, rfl,
        LValTargetsTyping.cons hhead hrestFull hunion hintersection⟩

/-- Lvalue typings transport backwards through an environment strengthening when
the source environment is weakly coherent and linearizable.

The only non-structural step is dereferencing a borrow.  The source borrow may
have fewer targets than the strengthened result borrow; linearization gives a
strictly smaller rank for those source targets, so their initialized typings can
be transported recursively before `CoherentWhenInitialized` rebuilds the source
dereference. -/
theorem lvalTyping_back_of_envStrengthens {source result : Env}
    (hstrength : EnvStrengthens source result)
    (hcoh : CoherentWhenInitialized source)
    (hlin : Linearizable source) :
    ∀ {lv pty lifetime},
      LValTyping result lv pty lifetime →
        ∃ sourcePty sourceLifetime,
          LValTyping source lv sourcePty sourceLifetime ∧
            PartialTyStrengthens sourcePty pty := by
  rcases hlin with ⟨φ, hφ⟩
  have hdetSource : ∀ t, ∀ {q1 m1 q2 m2},
      LValTyping source t q1 m1 →
      LValTyping source t q2 m2 →
      PartialTy.eqv q1 q2 := by
    intro t q1 m1 q2 m2 hq1 hq2
    exact lvalTyping_eqv_of_linearizedBy hφ hq1 hq2
  have key : ∀ n, ∀ lv,
      φ (LVal.base lv) ≤ n →
      ∀ {pty lifetime},
        LValTyping result lv pty lifetime →
          ∃ sourcePty sourceLifetime,
            LValTyping source lv sourcePty sourceLifetime ∧
              PartialTyStrengthens sourcePty pty := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihRank =>
        intro lv hle
        induction lv with
        | var x =>
            intro pty lifetime htyping
            cases htyping with
            | var hslot =>
                have hx := hstrength x
                cases hsourceSlot : source.slotAt x with
                | none =>
                    simp [hsourceSlot, hslot] at hx
                | some sourceSlot =>
                    simp [hsourceSlot, hslot] at hx
                    exact ⟨sourceSlot.ty, sourceSlot.lifetime,
                      LValTyping.var hsourceSlot, hx.2⟩
        | deref inner ihInner =>
            intro pty lifetime htyping
            cases htyping with
            | box hinner =>
                rcases ihInner (by simpa [LVal.base] using hle) hinner with
                  ⟨sourcePty, sourceLifetime, hsourceInner, hsourceStrength⟩
                cases sourcePty with
                | box sourceInner =>
                    exact ⟨sourceInner, sourceLifetime,
                      LValTyping.box hsourceInner,
                      PartialTyStrengthens.box_inv hsourceStrength⟩
                | ty _ =>
                    exact False.elim
                      (PartialTyStrengthens.not_ty_to_box hsourceStrength)
                | undef _ =>
                    exact False.elim
                      (PartialTyStrengthens.not_undef_to_box hsourceStrength)
            | boxFull hinner =>
                rcases ihInner (by simpa [LVal.base] using hle) hinner with
                  ⟨sourcePty, sourceLifetime, hsourceInner, hsourceStrength⟩
                rcases PartialTyStrengthens.to_ty_right hsourceStrength with
                  ⟨sourceTy, hsourcePtyEq⟩
                subst hsourcePtyEq
                rcases PartialTyStrengthens.to_box_ty_inv hsourceStrength with
                  ⟨sourceInner, hsourceTyEq, hinnerStrength⟩
                cases hsourceTyEq
                exact ⟨.ty sourceInner, sourceLifetime,
                  LValTyping.boxFull hsourceInner, hinnerStrength⟩
            | @borrow _ mutable resultTargets borrowLifetime targetLifetime targetTy
                hborrow htargets =>
                rcases ihInner (by simpa [LVal.base] using hle) hborrow with
                  ⟨sourcePty, sourceBorrowLifetime, hsourceBorrowRaw,
                    hsourceBorrowStrength⟩
                rcases PartialTyStrengthens.to_borrow_right hsourceBorrowStrength with
                  ⟨sourceTargets, hsourcePtyEq, hsubset⟩
                subst hsourcePtyEq
                have htargetRank : ∀ target, target ∈ sourceTargets →
                    φ (LVal.base target) < n := by
                  intro target htarget
                  have htargetBelowBorrow :
                      φ (LVal.base target) < φ (LVal.base inner) := by
                    exact (lvalTyping_vars_rank_lt hφ).1 hsourceBorrowRaw
                      (LVal.base target)
                      (mem_partialTy_vars_iff.mpr
                        ⟨mutable, sourceTargets, target,
                          PartialTyContains.here, htarget, rfl⟩)
                  exact lt_of_lt_of_le htargetBelowBorrow
                    (by simpa [LVal.base] using hle)
                have hsourceInitialized :
                    BorrowTargetsInitialized source sourceTargets := by
                  intro target htarget
                  have htargetResult : target ∈ resultTargets := hsubset htarget
                  rcases lvalTargetsTyping_member_strengthens htargets target
                      htargetResult with
                    ⟨resultTargetTy, resultTargetLifetime, hresultTarget,
                      _hresultTargetStrength⟩
                  rcases ihRank (φ (LVal.base target))
                      (htargetRank target htarget) target (le_refl _)
                      hresultTarget with
                    ⟨sourceTargetPty, sourceTargetLifetime, hsourceTarget,
                      hsourceTargetStrength⟩
                  rcases PartialTyStrengthens.to_ty_right hsourceTargetStrength with
                    ⟨sourceTargetTy, hsourceTargetPtyEq⟩
                  subst hsourceTargetPtyEq
                  exact ⟨sourceTargetTy, sourceTargetLifetime, hsourceTarget⟩
                rcases hcoh inner mutable sourceTargets sourceBorrowLifetime
                    hsourceBorrowRaw hsourceInitialized with
                  ⟨sourceTargetPartialTy, sourceTargetLifetime,
                    hsourceTargetsMaybe⟩
                rcases LValTargetsMaybeTyping.full_of_initialized_linearizedBy
                    hφ hsourceTargetsMaybe hsourceInitialized with
                  ⟨sourceTargetTy, hsourceTargetTyEq, hsourceTargets⟩
                subst hsourceTargetTyEq
                have hsourceTargetStrength :
                    PartialTyStrengthens (.ty sourceTargetTy) pty := by
                  exact lvalTargetsTyping_strengthens_of_all_members
                    hsourceTargets (by
                      intro target htarget sourceMemberTy sourceMemberLifetime
                        hsourceMember
                      have htargetResult : target ∈ resultTargets := hsubset htarget
                      rcases lvalTargetsTyping_member_strengthens htargets target
                          htargetResult with
                        ⟨resultMemberTy, resultMemberLifetime, hresultMember,
                          hresultMemberStrength⟩
                      rcases ihRank (φ (LVal.base target))
                          (htargetRank target htarget) target (le_refl _)
                          hresultMember with
                        ⟨sourceMemberPty', sourceMemberLifetime',
                          hsourceMember', hsourceMemberStrength'⟩
                      rcases PartialTyStrengthens.to_ty_right hsourceMemberStrength' with
                        ⟨sourceMemberTy', hsourceMemberPtyEq⟩
                      subst hsourceMemberPtyEq
                      have heq :
                          PartialTy.eqv (.ty sourceMemberTy)
                            (.ty sourceMemberTy') :=
                        hdetSource target hsourceMember hsourceMember'
                      exact partialTyStrengthens_trans
                        (ty_eqv_imp_strengthens
                          (by simpa [PartialTy.eqv] using heq))
                        (partialTyStrengthens_trans hsourceMemberStrength'
                          hresultMemberStrength))
                exact ⟨.ty sourceTargetTy, sourceTargetLifetime,
                  LValTyping.borrow hsourceBorrowRaw hsourceTargets,
                  hsourceTargetStrength⟩
  intro lv pty lifetime htyping
  exact key (φ (LVal.base lv)) lv (le_refl _) htyping

theorem lvalTyping_initialized_back_of_envStrengthens {source result : Env}
    (hstrength : EnvStrengthens source result)
    (hcoh : CoherentWhenInitialized source)
    (hlin : Linearizable source)
    {lv : LVal} {ty : Ty} {lifetime : Lifetime} :
    LValTyping result lv (.ty ty) lifetime →
      ∃ sourceTy sourceLifetime,
        LValTyping source lv (.ty sourceTy) sourceLifetime := by
  intro htyping
  rcases lvalTyping_back_of_envStrengthens hstrength hcoh hlin htyping with
    ⟨sourcePty, sourceLifetime, hsource, hstrengthTy⟩
  rcases PartialTyStrengthens.to_ty_right hstrengthTy with
    ⟨sourceTy, hsourcePtyEq⟩
  subst hsourcePtyEq
  exact ⟨sourceTy, sourceLifetime, hsource⟩

theorem borrowTargetsInitialized_back_of_envStrengthens {source result : Env}
    (hstrength : EnvStrengthens source result)
    (hcoh : CoherentWhenInitialized source)
    (hlin : Linearizable source)
    {targets : List LVal} :
    BorrowTargetsInitialized result targets →
      BorrowTargetsInitialized source targets := by
  intro hinitialized target htarget
  rcases hinitialized target htarget with
    ⟨targetTy, targetLifetime, htargetTyping⟩
  exact lvalTyping_initialized_back_of_envStrengthens
    hstrength hcoh hlin htargetTyping

/-- **Base-slot lifetime bound.**  Given that every borrow contained in a slot of
`result` has its targets' bases outliving that slot (the base-outlives half of
`ContainedBorrowsWellFormed`, `hdecomp`), the output lifetime of any lvalue typing
is bounded by the lifetime of the lvalue's base slot, and every borrow contained
in the output type has its targets' bases outliving that slot too. -/
theorem lvalTyping_lifetime_le_baseSlot {result : Env}
    (hdecomp : ∀ z zslot m W, result.slotAt z = some zslot →
      PartialTyContains zslot.ty (.borrow m W) →
      ∀ w, w ∈ W → ∃ wbs, result.slotAt (LVal.base w) = some wbs ∧
        wbs.lifetime ≤ zslot.lifetime) :
    ∀ {lv pty lf}, LValTyping result lv pty lf →
      ∀ bs, result.slotAt (LVal.base lv) = some bs →
        lf ≤ bs.lifetime ∧
        (∀ m W, PartialTyContains pty (.borrow m W) → ∀ w, w ∈ W →
          ∃ wbs, result.slotAt (LVal.base w) = some wbs ∧
            wbs.lifetime ≤ bs.lifetime) := by
  intro lv pty lf htyping
  refine LValTyping.rec
    (motive_1 := fun lv pty lf _ =>
      ∀ bs, result.slotAt (LVal.base lv) = some bs →
        lf ≤ bs.lifetime ∧
        (∀ m W, PartialTyContains pty (.borrow m W) → ∀ w, w ∈ W →
          ∃ wbs, result.slotAt (LVal.base w) = some wbs ∧
            wbs.lifetime ≤ bs.lifetime))
    (motive_2 := fun targets pty lf _ =>
      ∀ bound,
        (∀ t, t ∈ targets → ∃ tbs, result.slotAt (LVal.base t) = some tbs ∧
          tbs.lifetime ≤ bound) →
        lf ≤ bound ∧
        (∀ m W, PartialTyContains pty (.borrow m W) → ∀ w, w ∈ W →
          ∃ wbs, result.slotAt (LVal.base w) = some wbs ∧
            wbs.lifetime ≤ bound))
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  case var =>
    intro x slot hslot bs hbs
    simp only [LVal.base] at hbs
    rw [hslot] at hbs
    have hbsEq : slot = bs := Option.some.inj hbs
    subst hbsEq
    refine ⟨LifetimeOutlives.refl _, ?_⟩
    intro m W hcontains w hw
    exact hdecomp x slot m W hslot hcontains w hw
  case box =>
    intro u inner lifetime _htyping ih bs hbs
    have hih := ih bs (by simpa [LVal.base] using hbs)
    refine ⟨hih.1, ?_⟩
    intro m W hcontains w hw
    exact hih.2 m W (PartialTyContains.box hcontains) w hw
  case boxFull =>
    intro u inner lifetime _htyping ih bs hbs
    have hih := ih bs (by simpa [LVal.base] using hbs)
    refine ⟨hih.1, ?_⟩
    intro m W hcontains w hw
    exact hih.2 m W (PartialTyContains.tyBox hcontains) w hw
  case borrow =>
    intro u mutable W0 borrowLf targetLf targetTy _hborrow _htargets ihBorrow ihTargets bs hbs
    have hihB := ihBorrow bs (by simpa [LVal.base] using hbs)
    have hbound : ∀ t, t ∈ W0 → ∃ tbs, result.slotAt (LVal.base t) = some tbs ∧
        tbs.lifetime ≤ bs.lifetime :=
      hihB.2 mutable W0 PartialTyContains.here
    have hres := ihTargets bs.lifetime hbound
    exact ⟨hres.1, hres.2⟩
  case singleton =>
    intro t ty lifetime _htyping ihTarget bound hbound
    obtain ⟨tbs, htbs, htle⟩ := hbound t (by simp)
    have hih := ihTarget tbs htbs
    refine ⟨LifetimeOutlives.trans hih.1 htle, ?_⟩
    intro m W hcontains w hw
    obtain ⟨wbs, hwbs, hwle⟩ := hih.2 m W hcontains w hw
    exact ⟨wbs, hwbs, LifetimeOutlives.trans hwle htle⟩
  case cons =>
    intro t rest headTy headLf restLf lifetime restTy unionTy _hhead _hrest hunion
      hinter ihHead ihRest bound hbound
    obtain ⟨tbs, htbs, htle⟩ := hbound t (by simp)
    have hihHead := ihHead tbs htbs
    have hboundRest : ∀ s, s ∈ rest → ∃ sbs, result.slotAt (LVal.base s) = some sbs ∧
        sbs.lifetime ≤ bound := fun s hs => hbound s (List.mem_cons_of_mem _ hs)
    have hihRest := ihRest bound hboundRest
    refine ⟨LifetimeIntersection.le_of_le hinter
      (LifetimeOutlives.trans hihHead.1 htle) hihRest.1, ?_⟩
    intro m W hcontains w hw
    rcases PartialTyUnion.contained_borrow_member hunion hcontains hw with
      ⟨Wh, hch, hwh⟩ | ⟨Wr, hcr, hwr⟩
    · obtain ⟨wbs, hwbs, hwle⟩ := hihHead.2 m Wh hch w hwh
      exact ⟨wbs, hwbs, LifetimeOutlives.trans hwle htle⟩
    · exact hihRest.2 m Wr hcr w hwr

/-- `eqv` of full types implies `sameShape`. -/
theorem ty_eqv_imp_sameShape {a b : Ty} (h : Ty.eqv a b) : Ty.sameShape a b :=
  ty_sameShape_of_strengthens (ty_eqv_imp_strengthens h)

/--
Base-lifetime decomposition for weak contained borrows across joins.

No shape equality is needed here: each target of a joined borrow comes from one
of the branch borrow target lists, and the weak branch invariant still records
that the target's base slot outlives the containing branch slot.  `EnvJoin`
preserves slot lifetimes componentwise.
-/
theorem containedBorrowsWellFormedWhenInitialized_join_base_decomp
    {left right join : Env}
    (hjoin : EnvJoin left right join)
    (hcbwfL : ContainedBorrowsWellFormedWhenInitialized left)
    (hcbwfR : ContainedBorrowsWellFormedWhenInitialized right) :
    ∀ z zslot m W,
      join.slotAt z = some zslot →
      PartialTyContains zslot.ty (.borrow m W) →
      ∀ w, w ∈ W →
        ∃ wbs, join.slotAt (LVal.base w) = some wbs ∧
          wbs.lifetime ≤ zslot.lifetime := by
  intro z zslot m W hz hcontains w hw
  rcases EnvJoin.contained_borrow_member hjoin hz hcontains hw with
    ⟨lslot, lW, hlslot, hlc, hlw⟩ |
    ⟨rslot, rW, hrslot, hrc, hrw⟩
  · obtain ⟨hbase, _hinitialized⟩ :=
      hcbwfL z lslot m lW hlslot ⟨lslot, hlslot, hlc⟩ w hlw
    rcases hbase with ⟨bs, hbs, hbsLe⟩
    rcases EnvStrengthens.slot_forward (EnvJoin.left_le hjoin) hbs with
      ⟨jbs, hjbs, hbsLife, _hstrength⟩
    rcases EnvJoin.lifetimesPreserved_left hjoin z zslot hz with
      ⟨lslot', hlslot', hslotLife⟩
    have hslotEq : lslot' = lslot := Option.some.inj (hlslot'.symm.trans hlslot)
    subst hslotEq
    refine ⟨jbs, hjbs, ?_⟩
    rw [← hbsLife, ← hslotLife]
    exact hbsLe
  · obtain ⟨hbase, _hinitialized⟩ :=
      hcbwfR z rslot m rW hrslot ⟨rslot, hrslot, hrc⟩ w hrw
    rcases hbase with ⟨bs, hbs, hbsLe⟩
    rcases EnvStrengthens.slot_forward (EnvJoin.right_le hjoin) hbs with
      ⟨jbs, hjbs, hbsLife, _hstrength⟩
    rcases EnvJoin.lifetimesPreserved_right hjoin z zslot hz with
      ⟨rslot', hrslot', hslotLife⟩
    have hslotEq : rslot' = rslot := Option.some.inj (hrslot'.symm.trans hrslot)
    subst hslotEq
    refine ⟨jbs, hjbs, ?_⟩
    rw [← hbsLife, ← hslotLife]
    exact hbsLe

/--
Weak contained-borrow well-formedness is closed under environment joins without
`EnvJoinSameShape`.

If a joined borrow target is stale, the invariant only records its live base
slot.  If it is initialized in the joined environment, its lifetime is bounded
directly in the joined environment using `lvalTyping_lifetime_le_baseSlot`.
-/
theorem containedBorrowsWellFormedWhenInitialized_join {left right join : Env}
    (hjoin : EnvJoin left right join)
    (hcbwfL : ContainedBorrowsWellFormedWhenInitialized left)
    (hcbwfR : ContainedBorrowsWellFormedWhenInitialized right) :
    ContainedBorrowsWellFormedWhenInitialized join := by
  have hdecomp :=
    containedBorrowsWellFormedWhenInitialized_join_base_decomp
      hjoin hcbwfL hcbwfR
  intro x joinSlot mutable targets hjoinSlot hcontains target htarget
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq : containedSlot = joinSlot :=
    Option.some.inj (hcontainedSlot.symm.trans hjoinSlot)
  have hcontainsJoin : PartialTyContains joinSlot.ty (.borrow mutable targets) := by
    simpa [hcontainedSlotEq] using hcontainsTy
  have hbase := hdecomp x joinSlot mutable targets hjoinSlot hcontainsJoin target htarget
  refine ⟨hbase, ?_⟩
  intro hinitialized
  rcases hinitialized with ⟨targetTy, targetLifetime, htyping⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  have htargetBound :=
    (lvalTyping_lifetime_le_baseSlot hdecomp htyping baseSlot hbaseSlot).1
  exact ⟨targetTy, targetLifetime, htyping,
    LifetimeOutlives.trans htargetBound hbaseOutlives,
    ⟨baseSlot, hbaseSlot, hbaseOutlives⟩⟩

theorem wellFormedEnvWhenInitialized_join_of_obligations {left right join : Env}
    {lifetime : Lifetime} :
    EnvJoin left right join →
    WellFormedEnvWhenInitialized left lifetime →
    WellFormedEnvWhenInitialized right lifetime →
    CoherentWhenInitialized join →
    Linearizable join →
    WellFormedEnvWhenInitialized join lifetime := by
  intro hjoin hleft hright hcoherent hlinear
  exact ⟨
      containedBorrowsWellFormedWhenInitialized_join hjoin hleft.1 hright.1,
      EnvSlotsOutlive.of_lifetimesPreserved hleft.2
        (EnvJoin.lifetimesPreserved_left hjoin)⟩

theorem wellFormedWhenInitialized_iteJoin_of_obligations
    {left right join : Env} {lifetime : Lifetime} {joinTy : Ty} :
    EnvJoin left right join →
    WellFormedEnvWhenInitialized left lifetime →
    WellFormedEnvWhenInitialized right lifetime →
    WellFormedTy join joinTy lifetime →
    CoherentWhenInitialized join →
    Linearizable join →
    WellFormedEnvWhenInitialized join lifetime ∧
      WellFormedTyWhenInitialized join joinTy lifetime := by
  intro hjoin hleft hright hwellTy hcoherent hlinear
  exact ⟨
    wellFormedEnvWhenInitialized_join_of_obligations
      hjoin hleft hright hcoherent hlinear,
    WellFormedTy.whenInitialized hwellTy⟩

/-- **LValue typing transport across a same-shape strengthening.**  If `result`
is a same-shape strengthening of `source`, is coherent and linearizable, then any
lvalue typing transports from `source` to `result`, with the result output type
both `eqv`-strengthening and `sameShape` to the source one. -/
theorem lvalTyping_transport_of_sameShapeStrengthening {source result : Env}
    (hmap : EnvSameShapeStrengthening source result)
    (hcoh : FullCoherent result) (hlin : Linearizable result) :
    ∀ {lv pty lf}, LValTyping source lv pty lf →
      ∃ pty' lf', LValTyping result lv pty' lf' ∧
        PartialTyStrengthens pty pty' ∧ PartialTy.sameShape pty pty' := by
  obtain ⟨φ, hφ⟩ := hlin
  have hdet : ∀ t, ∀ {q1 m1 q2 m2}, LValTyping result t q1 m1 →
      LValTyping result t q2 m2 → PartialTy.eqv q1 q2 := by
    intro t q1 m1 q2 m2 hq1 hq2
    exact lvalTyping_eqv_of_linearizedBy hφ hq1 hq2
  intro lv pty lf htyping
  refine LValTyping.rec
    (motive_1 := fun lv pty _ _ =>
      ∃ pty' lf', LValTyping result lv pty' lf' ∧
        PartialTyStrengthens pty pty' ∧ PartialTy.sameShape pty pty')
      (motive_2 := fun targets pty _ _ =>
        ∀ {W' tyJ lfJ}, targets ⊆ W' → LValTargetsTyping result W' (.ty tyJ) lfJ →
          ∀ tyS, pty = .ty tyS →
            PartialTyStrengthens (.ty tyS) (.ty tyJ) ∧
              PartialTy.sameShape (.ty tyS) (.ty tyJ))
      ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  case var =>
    intro x slot hslot
    rcases hmap.2 x slot hslot with ⟨rslot, hrslot, _hlife⟩
    rcases hmap.1 x rslot hrslot with ⟨slot', hslot', _hlife, hstr, hshape⟩
    have : slot' = slot := Option.some.inj (hslot'.symm.trans hslot)
    subst this
    exact ⟨rslot.ty, rslot.lifetime, LValTyping.var hrslot, hstr, hshape⟩
  case box =>
    intro u inner lifetime _htyping ih
    obtain ⟨pty', lf', htyp', hstr', hshape'⟩ := ih
    cases pty' with
    | box inner' =>
        exact ⟨inner', lf', LValTyping.box htyp',
          PartialTyStrengthens.box_inv hstr', by simpa [PartialTy.sameShape] using hshape'⟩
    | ty _ => simp [PartialTy.sameShape] at hshape'
    | undef _ => simp [PartialTy.sameShape] at hshape'
  case boxFull =>
    intro u inner lifetime _htyping ih
    obtain ⟨pty', lf', htyp', hstr', hshape'⟩ := ih
    cases pty' with
    | ty ty' =>
        rcases PartialTyStrengthens.from_box_ty_inv hstr' with
          ⟨inner', hty', hinnerStr⟩
        cases hty'
        exact ⟨.ty inner', lf', LValTyping.boxFull htyp',
          hinnerStr,
          by simpa [PartialTy.sameShape, Ty.sameShape] using hshape'⟩
    | box _ => simp [PartialTy.sameShape] at hshape'
    | undef _ => simp [PartialTy.sameShape] at hshape'
  case borrow =>
    intro u mutable W0 borrowLf targetLf targetTy _hborrow _htargets ihBorrow ihTargets
    obtain ⟨ptyU, lfU, htypU, hstrU, hshapeU⟩ := ihBorrow
    cases ptyU with
    | ty tyU =>
        cases tyU with
        | borrow mU WU =>
            have hmEq : mutable = mU := by
              cases hstrU with
              | reflex => rfl
              | borrow _ => rfl
            subst hmEq
            obtain ⟨tyJ, lfJ, htJ⟩ := hcoh u mutable WU lfU htypU
            obtain ⟨tyTsrc, hTsrc⟩ := LValTargetsTyping.output_full _htargets
            subst hTsrc
            have hsub : W0 ⊆ WU := PartialTyStrengthens.borrow_subset hstrU
            have hcmp := ihTargets hsub htJ tyTsrc rfl
            exact ⟨.ty tyJ, lfJ, LValTyping.borrow htypU htJ, hcmp.1, hcmp.2⟩
        | unit => cases hstrU
        | int => cases hstrU
        | box _ => cases hstrU
    | box _ => simp [PartialTy.sameShape] at hshapeU
    | undef _ => simp [PartialTy.sameShape] at hshapeU
  case singleton =>
    intro t ty lifetime _htyping ih W' tyJ lfJ hsub htJ tyS htyS
    injection htyS with htyEq; subst htyEq
    obtain ⟨pt', lf', htyp', hstr', hshape'⟩ := ih
    obtain ⟨ty', hty'⟩ : ∃ ty', pt' = .ty ty' := by
      cases pt' with
      | ty ty' => exact ⟨ty', rfl⟩
      | box _ => simp [PartialTy.sameShape] at hshape'
      | undef _ => simp [PartialTy.sameShape] at hshape'
    subst hty'
    have htmem : t ∈ W' := hsub (by simp)
    rcases lvalTargetsTyping_member_strengthens htJ t htmem with ⟨τ, lτ, htτ, hstrτ⟩
    have heq : PartialTy.eqv (.ty ty') (.ty τ) := hdet t htyp' htτ
    have hτJ : PartialTyStrengthens (.ty ty') (.ty tyJ) :=
      ty_eqv_strengthens_trans (by simpa [PartialTy.eqv] using heq) hstrτ
    refine ⟨partialTyStrengthens_trans hstr' hτJ, ?_⟩
    exact PartialTy.sameShape_trans hshape'
      (by simpa [PartialTy.sameShape] using ty_sameShape_of_strengthens hτJ)
  case cons =>
    intro t rest headTy headLf restLf lifetime restTy unionTy hhead hrest hunion
      _hinter ihHead ihRest W' tyJ lfJ hsub htJ tyS htyS
    obtain ⟨ph, lh, htypHead, hstrHead, hshapeHead⟩ := ihHead
    obtain ⟨headTy', hh⟩ : ∃ ty, ph = .ty ty := by
      cases ph with
      | ty ty => exact ⟨ty, rfl⟩
      | box _ => simp [PartialTy.sameShape] at hshapeHead
      | undef _ => simp [PartialTy.sameShape] at hshapeHead
    subst hh
    obtain ⟨restTyFull, hrf⟩ := LValTargetsTyping.output_full hrest
    subst hrf
    -- head ≤ tyJ
    have htmem : t ∈ W' := hsub (by simp)
    rcases lvalTargetsTyping_member_strengthens htJ t htmem with ⟨τ, lτ, htτ, hstrτ⟩
    have heqH : PartialTy.eqv (.ty headTy') (.ty τ) := hdet t htypHead htτ
    have hHeadJ : PartialTyStrengthens (.ty headTy) (.ty tyJ) :=
      partialTyStrengthens_trans hstrHead
        (ty_eqv_strengthens_trans (by simpa [PartialTy.eqv] using heqH) hstrτ)
    -- rest ≤ tyJ
    have hsubRest : rest ⊆ W' := fun s hs => hsub (List.mem_cons_of_mem _ hs)
    have hRestJ := ihRest hsubRest htJ restTyFull rfl
    -- union ≤ tyJ
    have hunionTyS : PartialTyUnion (.ty headTy) (.ty restTyFull) (.ty tyS) := by
      rwa [htyS] at hunion
    refine ⟨hunionTyS.2 (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hHeadJ
      · exact hRestJ.1), ?_⟩
    -- sameShape (.ty tyS) (.ty tyJ)
    have hS1 : Ty.sameShape tyS headTy :=
      partialTyUnion_ty_left_sameShape hunionTyS
    have hS2 : Ty.sameShape headTy tyJ := by
      have h2a : Ty.sameShape headTy headTy' := by
        simpa [PartialTy.sameShape] using hshapeHead
      have h2b : Ty.sameShape headTy' τ := ty_eqv_imp_sameShape
        (by simpa [PartialTy.eqv] using heqH)
      have h2c : Ty.sameShape τ tyJ := ty_sameShape_of_strengthens hstrτ
      exact Ty.sameShape_trans (Ty.sameShape_trans h2a h2b) h2c
    show PartialTy.sameShape (.ty tyS) (.ty tyJ)
    simpa [PartialTy.sameShape] using Ty.sameShape_trans hS1 hS2

/-- Per-target borrow well-formedness transports across a same-shape
strengthening whose result is coherent, linearizable, and has the base-outlives
half of CBWF (`hdecomp`), with the result slot lifetime equal to the source. -/
theorem borrowTargetWellFormed_transport {source result : Env} {T : LVal}
    {sourceSlotLife resultSlotLife : Lifetime}
    (hmap : EnvSameShapeStrengthening source result)
    (hcoh : FullCoherent result) (hlin : Linearizable result)
    (hdecomp : ∀ z zslot m W, result.slotAt z = some zslot →
      PartialTyContains zslot.ty (.borrow m W) →
      ∀ w, w ∈ W → ∃ wbs, result.slotAt (LVal.base w) = some wbs ∧
        wbs.lifetime ≤ zslot.lifetime)
    (hlifeEq : sourceSlotLife = resultSlotLife)
    (hsrc : ∃ tTy tLf, LValTyping source T (.ty tTy) tLf ∧
      tLf ≤ sourceSlotLife ∧ LValBaseOutlives source T sourceSlotLife) :
    ∃ tTy' tLf', LValTyping result T (.ty tTy') tLf' ∧
      tLf' ≤ resultSlotLife ∧ LValBaseOutlives result T resultSlotLife := by
  obtain ⟨tTy, tLf, htyp, _htLe, hbase⟩ := hsrc
  obtain ⟨pty', lf', htyp', _hstr', hshape'⟩ :=
    lvalTyping_transport_of_sameShapeStrengthening hmap hcoh hlin htyp
  obtain ⟨tTy', hpty'⟩ : ∃ tTy', pty' = .ty tTy' := by
    cases pty' with
    | ty t => exact ⟨t, rfl⟩
    | box _ => simp [PartialTy.sameShape] at hshape'
    | undef _ => simp [PartialTy.sameShape] at hshape'
  subst hpty'
  obtain ⟨bs, hbs, hbsLe⟩ := hbase
  rcases hmap.2 (LVal.base T) bs hbs with ⟨bs', hbs', hbsLife⟩
  have hbsLe' : bs'.lifetime ≤ resultSlotLife := by
    rw [← hbsLife, ← hlifeEq]; exact hbsLe
  have hbound := (lvalTyping_lifetime_le_baseSlot hdecomp htyp' bs' hbs').1
  exact ⟨tTy', lf', htyp', LifetimeOutlives.trans hbound hbsLe', bs', hbs', hbsLe'⟩

/-- The slot-local borrow invariant transports across a same-shape
strengthening, by transporting each target. -/
theorem borrowTargetsWellFormedInSlot_transport {source result : Env}
    {targets : List LVal} {sourceSlotLife resultSlotLife : Lifetime}
    (hmap : EnvSameShapeStrengthening source result)
    (hcoh : FullCoherent result) (hlin : Linearizable result)
    (hdecomp : ∀ z zslot m W, result.slotAt z = some zslot →
      PartialTyContains zslot.ty (.borrow m W) →
      ∀ w, w ∈ W → ∃ wbs, result.slotAt (LVal.base w) = some wbs ∧
        wbs.lifetime ≤ zslot.lifetime)
    (hlifeEq : sourceSlotLife = resultSlotLife)
    (hsrc : BorrowTargetsWellFormedInSlot source sourceSlotLife targets) :
    BorrowTargetsWellFormedInSlot result resultSlotLife targets := by
  intro T hT
  exact borrowTargetWellFormed_transport hmap hcoh hlin hdecomp hlifeEq (hsrc T hT)

/-- Full contained-borrow well-formedness for a join, under explicit legacy
same-shape-to-join evidence.  This is not a current `T-If` typing premise; the
main preservation path uses `containedBorrowsWellFormedWhenInitialized_join`,
which needs only `EnvJoin` and the weak branch invariants. -/
theorem containedBorrowsWellFormed_join {left right join : Env}
    (hjoin : EnvJoin left right join)
    (hssLeft : EnvJoinSameShape left join) (hssRight : EnvJoinSameShape right join)
    (hcbwfL : ContainedBorrowsWellFormed left)
    (hcbwfR : ContainedBorrowsWellFormed right)
    (hcoh : FullCoherent join) (hlin : Linearizable join) :
    ContainedBorrowsWellFormed join := by
  have hbranch := EnvJoin.branches_sameShape hjoin hssLeft hssRight
  have hmapL : EnvSameShapeStrengthening left join :=
    EnvJoin.left_sameShapeStrengthening hjoin hbranch
  have hmapR : EnvSameShapeStrengthening right join :=
    EnvJoin.right_sameShapeStrengthening hjoin hbranch
  have hdecomp : ∀ z zslot m W, join.slotAt z = some zslot →
      PartialTyContains zslot.ty (.borrow m W) →
      ∀ w, w ∈ W → ∃ wbs, join.slotAt (LVal.base w) = some wbs ∧
        wbs.lifetime ≤ zslot.lifetime := by
    intro z zslot m W hz hcontains w hw
    rcases EnvJoin.contained_borrow_member hjoin hz hcontains hw with
      ⟨lslot, lW, hlslot, hlc, hlw⟩ | ⟨rslot, rW, hrslot, hrc, hrw⟩
    · obtain ⟨_, _, _, _, hbase⟩ :=
        (hcbwfL z lslot m lW hlslot ⟨lslot, hlslot, hlc⟩) w hlw
      obtain ⟨bs, hbs, hbsLe⟩ := hbase
      rcases hmapL.2 (LVal.base w) bs hbs with ⟨bs', hbs', hbsLife⟩
      rcases hmapL.1 z zslot hz with ⟨ls0, hls0, hls0life, _, _⟩
      have hlsEq : ls0 = lslot := Option.some.inj (hls0.symm.trans hlslot)
      subst hlsEq
      refine ⟨bs', hbs', ?_⟩
      rw [← hbsLife, ← hls0life]; exact hbsLe
    · obtain ⟨_, _, _, _, hbase⟩ :=
        (hcbwfR z rslot m rW hrslot ⟨rslot, hrslot, hrc⟩) w hrw
      obtain ⟨bs, hbs, hbsLe⟩ := hbase
      rcases hmapR.2 (LVal.base w) bs hbs with ⟨bs', hbs', hbsLife⟩
      rcases hmapR.1 z zslot hz with ⟨rs0, hrs0, hrs0life, _, _⟩
      have hrsEq : rs0 = rslot := Option.some.inj (hrs0.symm.trans hrslot)
      subst hrsEq
      refine ⟨bs', hbs', ?_⟩
      rw [← hbsLife, ← hrs0life]; exact hbsLe
  refine EnvJoin.preserves_containedBorrowsWellFormed_of_target_transport
    hjoin hcbwfL hcbwfR ?_ ?_
  · intro x joinSlot leftSlot mutable targets hjs hls _hcontains hbtw
    have hlifeEq : leftSlot.lifetime = joinSlot.lifetime := by
      rcases hmapL.1 x joinSlot hjs with ⟨ls, hls', hlife, _, _⟩
      have : ls = leftSlot := Option.some.inj (hls'.symm.trans hls)
      subst this; exact hlife
    exact borrowTargetsWellFormedInSlot_transport hmapL hcoh hlin hdecomp hlifeEq hbtw
  · intro x joinSlot rightSlot mutable targets hjs hrs _hcontains hbtw
    have hlifeEq : rightSlot.lifetime = joinSlot.lifetime := by
      rcases hmapR.1 x joinSlot hjs with ⟨rs, hrs', hlife, _, _⟩
      have : rs = rightSlot := Option.some.inj (hrs'.symm.trans hrs)
      subst this; exact hlife
    exact borrowTargetsWellFormedInSlot_transport hmapR hcoh hlin hdecomp hlifeEq hbtw

/-! ### Write fan-out shape lemmas (relocated from Lemma_4_11 to break the
import cycle with the assign CBWF derivation below). -/

/--
Positive-rank writes over initialized leaves transport safe-abstraction slot
types by same-shape strengthening.

This is the `WriteLeafTy` analogue of `EnvWrite.shapeMap`: the existing
positive-rank strengthening theorem supplies `env ≤ result`, while
`EnvWrite.shapePreserved_init` supplies the shape equality needed to transport
`ValidPartialValue`.
-/
theorem EnvWrite.sameShapeStrengthening_init {rank : Nat}
    {env result : Env} {lv : LVal} {rhsTy : Ty} :
    0 < rank →
    EnvWrite rank env lv rhsTy result →
    (∀ slot, env.slotAt (LVal.base lv) = some slot →
      WriteLeafTy env (LVal.path lv) slot.ty rhsTy) →
    EnvSameShapeStrengthening env result := by
  intro hrank hwrite hleaf
  refine EnvSameShapeStrengthening.of_shapeMap ?shapeMap
    (EnvWrite.lifetimesPreserved hwrite)
    (EnvWrite.lifetimesSurvive hwrite)
  intro x sourceSlot hsourceSlot
  have hstrength := EnvWrite.envStrengthens hrank hwrite x
  have hshapePres := EnvWrite.shapePreserved_init hrank hwrite hleaf
  rw [hsourceSlot] at hstrength
  cases hresult : result.slotAt x with
  | none =>
      rw [hresult] at hstrength
      exact False.elim hstrength
  | some resultSlot =>
      rw [hresult] at hstrength
      rcases hshapePres x resultSlot hresult with
        ⟨sourceSlot', hsourceSlot', hshape⟩
      have hsourceSlotEq : sourceSlot' = sourceSlot :=
        Option.some.inj (hsourceSlot'.symm.trans hsourceSlot)
      subst hsourceSlotEq
      exact ⟨resultSlot, rfl, hshape, hstrength.2⟩

/--
Fan-out writes over initialized leaves transport the original environment to the
joined fan-out result by same-shape strengthening.
-/
theorem WriteBorrowTargets.sameShapeStrengthening_init {rank : Nat}
    {env result : Env} {path : List Unit} {targets : List LVal}
    {rhsTy : Ty} :
    0 < rank →
    WriteBorrowTargets rank env path targets rhsTy result →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    EnvSameShapeStrengthening env result := by
  intro hrank hwrites hleaf
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun rank env path targets rhsTy result _ =>
      0 < rank →
      (∀ target, target ∈ targets → ∀ targetSlot,
        env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
        WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
      EnvSameShapeStrengthening env result)
      (motive_3 := fun _ _ _ _ _ _ => True)
      ?strong ?weak ?box ?boxFull ?mutBorrow ?nil ?singleton ?cons ?intro
      hwrites hrank hleaf
  case strong | weak | box | boxFull | mutBorrow => intros; trivial
  case nil =>
    intro rank env path ty _hrank _hleaf
    exact EnvSameShapeStrengthening.refl env
  case singleton =>
    intro rank env updated path target ty hwrite _htyped _ih hrank hleaf
    exact EnvWrite.sameShapeStrengthening_init hrank hwrite
      (fun slot hslot => hleaf target (by simp) slot hslot)
  case cons =>
    intro rank env updated restEnv result path target rest ty hwrite _htyped
      hwrites hjoin _ihWrite _ihWrites hrank hleaf
    have hheadMap : EnvSameShapeStrengthening env updated :=
      EnvWrite.sameShapeStrengthening_init hrank hwrite
        (fun slot hslot => hleaf target (by simp) slot hslot)
    have hallLeaves :
        ∀ t, t ∈ target :: rest → ∀ tslot,
          env.slotAt (LVal.base (prependPath path t)) = some tslot →
          WriteLeafTy env (LVal.path (prependPath path t)) tslot.ty ty :=
      hleaf
    have hupdShape : EnvShapePreserved env updated :=
      EnvWrite.shapePreserved_init hrank hwrite
        (fun slot hslot => hallLeaves target (by simp) slot hslot)
    have hrestShape : EnvShapePreserved env restEnv :=
      WriteBorrowTargets.shapePreserved_init hrank hwrites
        (fun t ht slot hslot =>
          hallLeaves t (List.mem_cons_of_mem target ht) slot hslot)
    have hbranchShape :
        ∀ x leftSlot rightSlot,
          updated.slotAt x = some leftSlot →
          restEnv.slotAt x = some rightSlot →
          PartialTy.sameShape leftSlot.ty rightSlot.ty :=
      EnvShapePreserved.branch_sameShape hupdShape hrestShape
    exact EnvSameShapeStrengthening.trans hheadMap
      (EnvJoin.left_sameShapeStrengthening hjoin hbranchShape)
  case intro => intros; trivial

/--
A write path that crosses a (mutable) borrow node of the walked type before the
path is exhausted.

Writes along such paths never strong-replace a leaf of the walked slot: at the
borrow node the update fans out at positive rank (`W-MutBor`), where every leaf
update is a weak join.  This is the discriminant separating the deref-of-borrow
assignment from the rank-0 deref-of-box assignment (whose leaf is strongly
replaced).
-/
inductive PathThroughBorrow : PartialTy → List Unit → Prop where
  | borrowHere {mutable : Bool} {targets : List LVal} {path : List Unit} :
      PathThroughBorrow (.ty (.borrow mutable targets)) (() :: path)
  | box {inner : PartialTy} {path : List Unit} :
      PathThroughBorrow inner path →
      PathThroughBorrow (.box inner) (() :: path)
  | boxFull {inner : Ty} {path : List Unit} :
      PathThroughBorrow (.ty inner) path →
      PathThroughBorrow (.ty (.box inner)) (() :: path)

theorem List.Unit_append_cons (l s : List Unit) :
    l ++ () :: s = () :: (l ++ s) := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [ih]

/--
An update along a path that crosses a borrow node transports the whole
environment by same-shape strengthening, and weakens the walked type itself
by same-shape strengthening.

The borrow node turns the rest of the update into a positive-rank fan-out
(`WriteBorrowTargets`), whose initialized leaves are weak joins; the box prefix
above the borrow node is rebuilt unchanged.
-/
theorem UpdateAtPath.sameShapeStrengthening_of_throughBorrow {rank : Nat}
    {env writeEnv : Env} {path : List Unit} {pt updatedTy : PartialTy}
    {rhsTy : Ty} :
    PathThroughBorrow pt path →
    UpdateAtPath rank env path pt rhsTy writeEnv updatedTy →
    EnvSameShapeStrengthening env writeEnv ∧
      PartialTyStrengthens pt updatedTy ∧
      PartialTy.sameShape pt updatedTy := by
  intro hthrough hupdate
  induction hthrough generalizing rank writeEnv updatedTy with
  | borrowHere =>
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        cases hupdatedEq
        refine ⟨?_, PartialTyStrengthens.reflex, PartialTy.sameShape_refl _⟩
        exact WriteBorrowTargets.sameShapeStrengthening_init
          (Nat.succ_pos _) hwrites
          (WriteBorrowTargets.initialized_leaves_of_typed hwrites)
  | box _hinner ih =>
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, hupdatedEq, hinnerUpdate⟩
          cases htyEq
          cases hupdatedEq
          rcases ih hinnerUpdate with ⟨hmap, hstrength, hshape⟩
          exact ⟨hmap, PartialTyStrengthens.box hstrength,
            by simpa [PartialTy.sameShape] using hshape⟩
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinnerUpdate⟩
          cases htyEq
      · rcases hborrow with ⟨targets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  | boxFull _hinner ih =>
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinnerUpdate⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, hupdatedEq,
            hinnerUpdate⟩
          cases htyEq
          cases hupdatedEq
          rcases ih hinnerUpdate with ⟨hmap, hstrength, hshape⟩
          exact ⟨hmap, PartialTyStrengthens.tyBox_rebox hstrength hshape,
            by
              cases updatedInner <;>
                simp [partialTyRebox, PartialTy.sameShape, Ty.sameShape] at hshape ⊢
              exact hshape⟩
      · rcases hborrow with ⟨targets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq

/--
The slot type at the base of a borrow-typed lvalue crosses a borrow node along
the lvalue's path extended by any suffix: the lvalue's own derefs walk the slot
type through boxes and borrows, and the borrow type at the end is itself a
borrow node consuming the first suffix step.
-/
theorem LValTyping.pathThroughBorrow_append {env : Env} {lv : LVal}
    {pt : PartialTy} {lifetime : Lifetime}
    (htyping : LValTyping env lv pt lifetime) :
    ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
    ∀ (suffix : List Unit),
      PathThroughBorrow pt suffix →
      PathThroughBorrow slot.ty (LVal.path lv ++ suffix) := by
  refine LValTyping.rec
    (motive_1 := fun lv pt _lifetime _ =>
      ∀ {slot : EnvSlot}, env.slotAt (LVal.base lv) = some slot →
      ∀ (suffix : List Unit),
        PathThroughBorrow pt suffix →
        PathThroughBorrow slot.ty (LVal.path lv ++ suffix))
    (motive_2 := fun _targets _pt _lifetime _ => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  case var =>
    intro x slot hslot slot' hslot' suffix hsuffix
    simp only [LVal.base] at hslot'
    have hslotEq : slot = slot' := by
      rw [hslot] at hslot'
      exact Option.some.inj hslot'
    subst hslotEq
    simpa [LVal.path] using hsuffix
  case box =>
    intro source inner sourceLifetime _hsource ih slot hslot suffix hsuffix
    have hsource :=
      ih hslot (() :: suffix) (PathThroughBorrow.box hsuffix)
    simpa [LVal.path, List.append_assoc, List.Unit_append_cons] using hsource
  case boxFull =>
    intro source inner sourceLifetime _hsource ih slot hslot suffix hsuffix
    have hsource :=
      ih hslot (() :: suffix) (PathThroughBorrow.boxFull hsuffix)
    simpa [LVal.path, List.append_assoc, List.Unit_append_cons] using hsource
  case borrow =>
    intro source mutable' targets' borrowLifetime targetLifetime targetTy
      _hsource _htargets ihSource _ihTargets slot hslot suffix _hsuffix
    have hsource :=
      ihSource hslot (() :: suffix) PathThroughBorrow.borrowHere
    simpa [LVal.path, List.append_assoc, List.Unit_append_cons] using hsource
  case singleton =>
    intros
    trivial
  case cons =>
    intros
    trivial

/-- **Through-borrow dichotomy.**  A type-level update either crosses a borrow
node (then it transports the whole environment by same-shape strengthening and
leaves the walked type unchanged) or it terminates at a strong/weak leaf without
changing the environment. -/
theorem UpdateAtPath.throughBorrow_dichotomy {rank : Nat} {env env' : Env}
    {path : List Unit} {oldTy updatedTy : PartialTy} {ty : Ty}
    (hupdate : UpdateAtPath rank env path oldTy ty env' updatedTy) :
    (EnvSameShapeStrengthening env env' ∧ updatedTy = oldTy) ∨ env' = env := by
  refine UpdateAtPath.rec
    (motive_1 := fun _rank env _path oldTy _ty env' updatedTy _ =>
      (EnvSameShapeStrengthening env env' ∧ updatedTy = oldTy) ∨ env' = env)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
      ?strong ?weak ?box ?boxFull ?mutBorrow ?nil ?singleton ?cons ?intro hupdate
  case strong => intro env old ty; exact Or.inr rfl
  case weak => intro env rank old joined ty _hshape _hjoin; exact Or.inr rfl
  case box =>
    intro env₁ env₂ rank path inner updatedInner ty _hinner ih
    rcases ih with ⟨hess, hupd⟩ | henv
    · exact Or.inl ⟨hess, by rw [hupd]⟩
    · exact Or.inr henv
  case boxFull =>
    intro env₁ env₂ rank path inner updatedInner ty _hinner ih
    rcases ih with ⟨hess, hupd⟩ | henv
    · exact Or.inl ⟨hess, by rw [hupd]; rfl⟩
    · exact Or.inr henv
  case mutBorrow =>
    intro env₁ env₂ rank path targets ty hwrites _ih
    exact Or.inl ⟨WriteBorrowTargets.sameShapeStrengthening_init (Nat.succ_pos _)
      hwrites (WriteBorrowTargets.initialized_leaves_of_typed hwrites), rfl⟩
  case nil => intro _ _ _ _; trivial
  case singleton => intro _ _ _ _ _ _ _ _; trivial
  case cons => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _; trivial
  case intro => intro _ _ _ _ _ _ _ _ _ _; trivial

/-- An assignment write (rank 0) is either a whole-environment same-shape
strengthening (it crossed a borrow → positive-rank fan-out, leaving the base
slot's type unchanged) or a single-slot strong/weak update of the base slot. -/
theorem EnvWrite.sameShapeStrengthening_or_singleSlot {env result : Env}
    {lhs : LVal} {rhsTy : Ty} (hwrite : EnvWrite 0 env lhs rhsTy result) :
    EnvSameShapeStrengthening env result ∨
      (∃ slot updatedTy, env.slotAt (LVal.base lhs) = some slot ∧
        result = env.update (LVal.base lhs) { slot with ty := updatedTy }) := by
  cases hwrite with
  | intro hslot hupdate =>
    rename_i intermediate slot updatedTy
    rcases UpdateAtPath.throughBorrow_dichotomy hupdate with ⟨hess0, hupdEq⟩ | hinterEq
    · refine Or.inl (EnvSameShapeStrengthening.update_result_strengthening hess0 hslot rfl ?_ ?_)
      · rw [hupdEq]
      · rw [hupdEq]
    · exact Or.inr ⟨slot, updatedTy, hslot, by rw [hinterEq]⟩

/-- **CBWF of an assignment write result**, derived from `ContainedBorrowsWellFormed`
of the pre-write environment, the legacy full-coherence premise,
`Linearizable` of the result, `¬WriteProhibited`), and the *minimal* RHS-target
obligation `EnvWriteRhsTargetsWellFormed`.  The old-origin borrows transport via
the borrow-invariance keystone; the RHS-origin borrows are supplied by the
minimal obligation. -/
theorem containedBorrowsWellFormed_assign {env₂ env₃ : Env}
    {lhs : LVal} {rhsTy : Ty}
    (hcbwf₂ : ContainedBorrowsWellFormed env₂)
    (hcoh₃ : FullCoherent env₃) (hlin₃ : Linearizable env₃)
    (hrhsWF : EnvWriteRhsTargetsWellFormed env₃ rhsTy)
    (hwrite : EnvWrite 0 env₂ lhs rhsTy env₃)
    (hnotWrite : ¬ WriteProhibited env₃ lhs) :
    ContainedBorrowsWellFormed env₃ := by
  have hlifePres := EnvWrite.lifetimesPreserved hwrite
  rcases EnvWrite.sameShapeStrengthening_or_singleSlot hwrite with hess | ⟨wslot, updatedTy, hwslot, henv₃⟩
  · -- fan-out: env₃ is a same-shape strengthening of env₂
    have hdecomp : ∀ z zslot m W, env₃.slotAt z = some zslot →
        PartialTyContains zslot.ty (.borrow m W) →
        ∀ w, w ∈ W → ∃ wbs, env₃.slotAt (LVal.base w) = some wbs ∧
          wbs.lifetime ≤ zslot.lifetime := by
      intro z zslot m W hz hcontains w hw
      rcases EnvWrite.borrowTargetOrigin_all hwrite z zslot m W hz hcontains w hw with
        ⟨srcSlot, srcT, hsrcSlot, hcontainsSrc, hwSrc⟩ | ⟨rhsT, hcontainsRhs, hwRhs⟩
      · obtain ⟨_, _, _, _, bs, hbs, hble⟩ :=
          (hcbwf₂ z srcSlot m srcT hsrcSlot ⟨srcSlot, hsrcSlot, hcontainsSrc⟩) w hwSrc
        rcases hess.2 (LVal.base w) bs hbs with ⟨bs', hbs', hbsLife⟩
        rcases hess.1 z zslot hz with ⟨z₂, hz₂, hz₂Life, _, _⟩
        have hz₂Eq : z₂ = srcSlot := Option.some.inj (hz₂.symm.trans hsrcSlot)
        subst hz₂Eq
        exact ⟨bs', hbs', by rw [← hbsLife, ← hz₂Life]; exact hble⟩
      · obtain ⟨_, _, _, _, bs, hbs, hble⟩ :=
          hrhsWF z zslot m W w hz hcontains hw ⟨m, rhsT, hcontainsRhs, hwRhs⟩
        exact ⟨bs, hbs, hble⟩
    intro x rslot m T hrslot hcontainsX
    obtain ⟨s, hs, hcTy⟩ := hcontainsX
    have hsEq : rslot = s := Option.some.inj (hrslot.symm.trans hs)
    subst hsEq
    intro t ht
    rcases EnvWrite.borrowTargetOrigin_all hwrite x rslot m T hrslot hcTy t ht with
      ⟨srcSlot, srcT, hsrcSlot, hcontainsSrc, htSrc⟩ | ⟨rhsT, hcontainsRhs, htRhs⟩
    · have hlife : srcSlot.lifetime = rslot.lifetime := by
        rcases hlifePres x rslot hrslot with ⟨s₂, hs₂, hs₂Life⟩
        have : s₂ = srcSlot := Option.some.inj (hs₂.symm.trans hsrcSlot)
        subst this; exact hs₂Life
      exact borrowTargetWellFormed_transport hess hcoh₃ hlin₃ hdecomp hlife
        ((hcbwf₂ x srcSlot m srcT hsrcSlot ⟨srcSlot, hsrcSlot, hcontainsSrc⟩) t htSrc)
    · exact hrhsWF x rslot m T t hrslot hcTy ht ⟨m, rhsT, hcontainsRhs, htRhs⟩
  · -- single-slot update: env₃ = env₂.update (base lhs) {wslot with ty := updatedTy}
    have hnotWriteVar : ¬ WriteProhibited env₃ (.var (LVal.base lhs)) :=
      not_writeProhibited_var_base hnotWrite
    intro x rslot m T hrslot hcontainsX
    obtain ⟨s, hs, hcTy⟩ := hcontainsX
    have hsEq : rslot = s := Option.some.inj (hrslot.symm.trans hs)
    subst hsEq
    intro t ht
    have hnoconf : ¬ t ⋈ (.var (LVal.base lhs)) := by
      have := not_pathConflicts_of_not_writeProhibited_contains hnotWrite
        ⟨rslot, hrslot, hcTy⟩ ht
      simpa [PathConflicts, LVal.base] using this
    rcases EnvWrite.borrowTargetOrigin_all hwrite x rslot m T hrslot hcTy t ht with
      ⟨srcSlot, srcT, hsrcSlot, hcontainsSrc, htSrc⟩ | ⟨rhsT, hcontainsRhs, htRhs⟩
    · have hlife : srcSlot.lifetime = rslot.lifetime := by
        rcases hlifePres x rslot hrslot with ⟨s₂, hs₂, hs₂Life⟩
        have : s₂ = srcSlot := Option.some.inj (hs₂.symm.trans hsrcSlot)
        subst this; exact hs₂Life
      obtain ⟨tTy, tLf, htyp, hle, hbase⟩ :=
        (hcbwf₂ x srcSlot m srcT hsrcSlot ⟨srcSlot, hsrcSlot, hcontainsSrc⟩) t htSrc
      refine ⟨tTy, tLf, ?_, by rw [← hlife]; exact hle, ?_⟩
      · rw [henv₃]
        exact (LValTyping.update_of_not_pathConflicts
          (slot := { wslot with ty := updatedTy }) (by rw [← henv₃]; exact hnotWriteVar)).1
          htyp hnoconf
      · obtain ⟨bs, hbs, hble⟩ := hbase
        have hbaseNe : LVal.base t ≠ LVal.base lhs := by
          intro hbaseEq
          exact hnoconf (by simpa [PathConflicts, LVal.base] using hbaseEq)
        refine ⟨bs, ?_, by rw [← hlife]; exact hble⟩
        rw [henv₃]; simpa [Env.update, hbaseNe] using hbs
    · exact hrhsWF x rslot m T t hrslot hcTy ht ⟨m, rhsT, hcontainsRhs, htRhs⟩

/-- A common weakening of a full borrow type is itself a borrow of the same
mutability, possibly under `undef`, and its target list contains the original
targets. -/
theorem PartialTyStrengthens.ty_borrow_upper {mutable : Bool}
    {targets : List LVal} {upper : PartialTy} :
    PartialTyStrengthens (.ty (.borrow mutable targets)) upper →
    ∃ upperTargets,
      (upper = .ty (.borrow mutable upperTargets) ∨
        upper = .undef (.borrow mutable upperTargets)) ∧
      targets ⊆ upperTargets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨targets, Or.inl rfl, fun _ hmem => hmem⟩
  | borrow hsubset =>
      exact ⟨_, Or.inl rfl, hsubset⟩
  | intoUndef hinner =>
      cases hinner with
      | reflex =>
          exact ⟨targets, Or.inr rfl, fun _ hmem => hmem⟩
      | borrow hsubset =>
          exact ⟨_, Or.inr rfl, hsubset⟩

theorem PartialTyUnion.borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal} :
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable (leftTargets ++ rightTargets))) := by
  constructor
  · intro candidate hcandidate
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        exact List.mem_append_left rightTargets htarget)
    · subst hcandidate
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        exact List.mem_append_right leftTargets htarget)
  · intro upper hupper
    have hleft :
        PartialTyStrengthens (.ty (.borrow mutable leftTargets)) upper :=
      hupper (.ty (.borrow mutable leftTargets)) (by simp)
    have hright :
        PartialTyStrengthens (.ty (.borrow mutable rightTargets)) upper :=
      hupper (.ty (.borrow mutable rightTargets)) (by simp)
    rcases PartialTyStrengthens.ty_borrow_upper hleft with
      ⟨upperTargets, hupperShape, hleftSubset⟩
    have happendSubset : leftTargets ++ rightTargets ⊆ upperTargets := by
      intro target htarget
      rcases List.mem_append.mp htarget with htarget | htarget
      · exact hleftSubset htarget
      · rcases PartialTyStrengthens.ty_borrow_upper hright with
          ⟨rightUpperTargets, hrightShape, hrightSubset⟩
        rcases hupperShape with hupperEq | hupperEq <;>
          rcases hrightShape with hrightEq | hrightEq
        · subst upper
          have htargetsEq :
              rightUpperTargets = upperTargets := by
            cases hrightEq
            rfl
          subst htargetsEq
          exact hrightSubset htarget
        · subst upper
          cases hrightEq
        · subst upper
          cases hrightEq
        · subst upper
          have htargetsEq :
              rightUpperTargets = upperTargets := by
            cases hrightEq
            rfl
          subst htargetsEq
          exact hrightSubset htarget
    rcases hupperShape with hupperEq | hupperEq
    · subst upper
      exact PartialTyStrengthens.borrow happendSubset
    · subst upper
      exact PartialTyStrengthens.intoUndef
        (PartialTyStrengthens.borrow happendSubset)

theorem PartialTyUnion.ty_sameShape_exists {left right : Ty} :
    Ty.sameShape left right →
    ∃ union : Ty, PartialTyUnion (.ty left) (.ty right) (.ty union) := by
  exact Ty.rec
    (motive_1 := fun left =>
      ∀ right, Ty.sameShape left right →
        ∃ union : Ty, PartialTyUnion (.ty left) (.ty right) (.ty union))
    (motive_2 := fun _partial => True)
    (by
      intro right hshape
      cases right <;> simp [Ty.sameShape] at hshape
      exact ⟨.unit, by simp⟩)
    (by
      intro right hshape
      cases right <;> simp [Ty.sameShape] at hshape
      exact ⟨.int, by simp⟩)
    (by
      intro mutable leftTargets right hshape
      cases right <;> simp [Ty.sameShape] at hshape
      rename_i rightMutable rightTargets
      subst hshape
      exact ⟨.borrow mutable (leftTargets ++ rightTargets),
        PartialTyUnion.borrow_append⟩)
    (by
      intro leftInner ih right hshape
      cases right <;> simp [Ty.sameShape] at hshape
      rename_i rightInner
      rcases ih rightInner hshape with ⟨unionInner, hunionInner⟩
      exact ⟨.box unionInner, PartialTyUnion.tyBox hunionInner⟩)
    (by intro _ty _ih; trivial)
    (by intro _partial _ih; trivial)
    (by intro _ty _ih; trivial)
    left right

theorem LifetimeOutlives.comparable_of_common_bound {left right bound : Lifetime} :
    left ≤ bound →
    right ≤ bound →
    left ≤ right ∨ right ≤ left := by
  intro hleft hright
  have hleftPrefix : left.path <+: bound.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hleft
  have hrightPrefix : right.path <+: bound.path := by
    simpa [LifetimeOutlives, Core.Lifetime.contains] using hright
  by_cases hlen : left.path.length ≤ right.path.length
  · have hprefix : left.path <+: right.path :=
      List.prefix_of_prefix_length_le hleftPrefix hrightPrefix hlen
    exact Or.inl (by
      simpa [LifetimeOutlives, Core.Lifetime.contains] using hprefix)
  · have hlen' : right.path.length ≤ left.path.length := by
      exact Nat.le_of_lt (Nat.lt_of_not_ge hlen)
    have hprefix : right.path <+: left.path :=
      List.prefix_of_prefix_length_le hrightPrefix hleftPrefix hlen'
    exact Or.inr (by
      simpa [LifetimeOutlives, Core.Lifetime.contains] using hprefix)

theorem LifetimeIntersection.of_common_bound {left right bound : Lifetime} :
    left ≤ bound →
    right ≤ bound →
    ∃ intersection, LifetimeIntersection left right intersection := by
  intro hleft hright
  rcases LifetimeOutlives.comparable_of_common_bound hleft hright with
    hle | hle
  · exact ⟨right, LifetimeIntersection.left hle⟩
  · exact ⟨left, LifetimeIntersection.right hle⟩

theorem PartialTyUnion.of_side {left right union side : PartialTy} :
    PartialTyUnion left right union →
    side = left ∨ side = right →
    PartialTyUnion side union union := by
  intro hunion hside
  rcases hside with rfl | rfl
  · constructor
    · intro candidate hcandidate
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
      rcases hcandidate with hcandidate | hcandidate
      · subst hcandidate
        exact PartialTyUnion.left_strengthens hunion
      · subst hcandidate
        exact PartialTyStrengthens.reflex
    · intro upper hupper
      exact hupper union (by simp)
  · constructor
    · intro candidate hcandidate
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
      rcases hcandidate with hcandidate | hcandidate
      · subst hcandidate
        exact PartialTyUnion.right_strengthens hunion
      · subst hcandidate
        exact PartialTyStrengthens.reflex
    · intro upper hupper
      exact hupper union (by simp)

theorem PartialTyUnion.combine_side_kind {left right union side rest : PartialTy} :
    PartialTyUnion left right union →
    (side = left ∨ side = right) →
    (rest = left ∨ rest = right ∨ rest = union) →
    ∃ out,
      PartialTyUnion side rest out ∧
        (out = left ∨ out = right ∨ out = union) := by
  intro hunion hside hrest
  rcases hside with rfl | rfl
  · rcases hrest with rfl | hrest
    · exact ⟨_, PartialTyUnion.self _, Or.inl rfl⟩
    · rcases hrest with rfl | rfl
      · exact ⟨_, hunion, Or.inr (Or.inr rfl)⟩
      · exact ⟨_, PartialTyUnion.of_side hunion (Or.inl rfl),
          Or.inr (Or.inr rfl)⟩
  · rcases hrest with rfl | hrest
    · exact ⟨_, PartialTyUnion.symm hunion, Or.inr (Or.inr rfl)⟩
    · rcases hrest with rfl | rfl
      · exact ⟨_, PartialTyUnion.self _, Or.inr (Or.inl rfl)⟩
      · exact ⟨_, PartialTyUnion.of_side hunion (Or.inr rfl),
          Or.inr (Or.inr rfl)⟩

theorem LValTargetsMaybeTyping.of_forall_mem_two_sides {env : Env}
    {targets : List LVal} {left right union : PartialTy}
    {bound : Lifetime} :
    targets ≠ [] →
    PartialTyUnion left right union →
    (∀ target, target ∈ targets →
      ∃ side lifetime,
        LValTyping env target side lifetime ∧
          (side = left ∨ side = right) ∧
          lifetime ≤ bound) →
    ∃ partialTy lifetime,
      LValTargetsMaybeTyping env targets partialTy lifetime ∧
        (partialTy = left ∨ partialTy = right ∨ partialTy = union) ∧
        lifetime ≤ bound := by
  intro hnonempty hunion hmembers
  induction targets with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons head rest ih =>
      rcases hmembers head (by simp) with
        ⟨headSide, headLifetime, hheadTyping, hheadSide, hheadBound⟩
      cases rest with
      | nil =>
          refine ⟨headSide, headLifetime,
            LValTargetsMaybeTyping.singleton hheadTyping, ?_, hheadBound⟩
          rcases hheadSide with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
      | cons restHead restTail =>
          have hrestNonempty : restHead :: restTail ≠ [] := by simp
          rcases ih hrestNonempty (by
              intro target htarget
              exact hmembers target (List.mem_cons_of_mem head htarget)) with
            ⟨restTy, restLifetime, hrestTyping, hrestKind, hrestBound⟩
          rcases PartialTyUnion.combine_side_kind hunion hheadSide hrestKind with
            ⟨outTy, houtUnion, houtKind⟩
          rcases LifetimeIntersection.of_common_bound hheadBound hrestBound with
            ⟨lifetime, hintersection⟩
          exact ⟨outTy, lifetime,
            LValTargetsMaybeTyping.cons hheadTyping hrestTyping
              houtUnion hintersection,
            houtKind,
            LifetimeIntersection.le_of_le hintersection hheadBound hrestBound⟩

theorem containedBorrowsWellFormedWhenInitialized_assign {env₂ env₃ : Env}
    {lhs : LVal} {rhsTy : Ty}
    (hcbwf₂ : ContainedBorrowsWellFormedWhenInitialized env₂)
    (hrhsWF : EnvWriteRhsTargetsWellFormed env₃ rhsTy)
    (hwrite : EnvWrite 0 env₂ lhs rhsTy env₃)
    (hnotWrite : ¬ WriteProhibited env₃ lhs) :
    ContainedBorrowsWellFormedWhenInitialized env₃ := by
  have hlifePres := EnvWrite.lifetimesPreserved hwrite
  have hdecomp : ∀ z zslot m W, env₃.slotAt z = some zslot →
      PartialTyContains zslot.ty (.borrow m W) →
      ∀ w, w ∈ W → ∃ wbs, env₃.slotAt (LVal.base w) = some wbs ∧
        wbs.lifetime ≤ zslot.lifetime := by
    rcases EnvWrite.sameShapeStrengthening_or_singleSlot hwrite with hess |
      ⟨wslot, updatedTy, hwslot, henv₃⟩
    · intro z zslot m W hz hcontains w hw
      rcases EnvWrite.borrowTargetOrigin_all hwrite z zslot m W hz hcontains w hw with
        ⟨srcSlot, srcT, hsrcSlot, hcontainsSrc, hwSrc⟩ | ⟨rhsT, hcontainsRhs, hwRhs⟩
      · obtain ⟨hbase, _hinitialized⟩ :=
          hcbwf₂ z srcSlot m srcT hsrcSlot ⟨srcSlot, hsrcSlot, hcontainsSrc⟩
            w hwSrc
        obtain ⟨bs, hbs, hble⟩ := hbase
        rcases hess.2 (LVal.base w) bs hbs with ⟨bs', hbs', hbsLife⟩
        rcases hess.1 z zslot hz with ⟨z₂, hz₂, hz₂Life, _, _⟩
        have hz₂Eq : z₂ = srcSlot := Option.some.inj (hz₂.symm.trans hsrcSlot)
        subst hz₂Eq
        exact ⟨bs', hbs', by rw [← hbsLife, ← hz₂Life]; exact hble⟩
      · obtain ⟨_, _, _, _, hbase⟩ :=
          hrhsWF z zslot m W w hz hcontains hw ⟨m, rhsT, hcontainsRhs, hwRhs⟩
        exact hbase
    · intro z zslot m W hz hcontains w hw
      have hcontainsResult : env₃ ⊢ z ↝ Ty.borrow m W :=
        ⟨zslot, hz, hcontains⟩
      have hnoconf : ¬ w ⋈ (.var (LVal.base lhs)) := by
        have := not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          hcontainsResult hw
        simpa [PathConflicts, LVal.base] using this
      rcases EnvWrite.borrowTargetOrigin_all hwrite z zslot m W hz hcontains w hw with
        ⟨srcSlot, srcT, hsrcSlot, hcontainsSrc, hwSrc⟩ | ⟨rhsT, hcontainsRhs, hwRhs⟩
      · have hlife : srcSlot.lifetime = zslot.lifetime := by
          rcases hlifePres z zslot hz with ⟨s₂, hs₂, hs₂Life⟩
          have : s₂ = srcSlot := Option.some.inj (hs₂.symm.trans hsrcSlot)
          subst this
          exact hs₂Life
        obtain ⟨hbase, _hinitialized⟩ :=
          hcbwf₂ z srcSlot m srcT hsrcSlot ⟨srcSlot, hsrcSlot, hcontainsSrc⟩
            w hwSrc
        obtain ⟨bs, hbs, hble⟩ := hbase
        have hbaseNe : LVal.base w ≠ LVal.base lhs := by
          intro hbaseEq
          exact hnoconf (by simpa [PathConflicts, LVal.base] using hbaseEq)
        refine ⟨bs, ?_, by rw [← hlife]; exact hble⟩
        rw [henv₃]
        simpa [Env.update, hbaseNe] using hbs
      · obtain ⟨_, _, _, _, hbase⟩ :=
          hrhsWF z zslot m W w hz hcontains hw ⟨m, rhsT, hcontainsRhs, hwRhs⟩
        exact hbase
  intro x rslot m T hrslot hcontainsX target htarget
  obtain ⟨s, hs, hcTy⟩ := hcontainsX
  have hsEq : rslot = s := Option.some.inj (hrslot.symm.trans hs)
  subst hsEq
  have hbase := hdecomp x rslot m T hrslot hcTy target htarget
  refine ⟨hbase, ?_⟩
  intro htargetInitialized
  rcases htargetInitialized with ⟨targetTy, targetLifetime, htyping⟩
  rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
  have htargetBound :=
    (lvalTyping_lifetime_le_baseSlot hdecomp htyping baseSlot hbaseSlot).1
  exact ⟨targetTy, targetLifetime, htyping,
    LifetimeOutlives.trans htargetBound hbaseOutlives,
    ⟨baseSlot, hbaseSlot, hbaseOutlives⟩⟩

theorem typingPreservesWellFormed_of_ruleCarriedObligations_core_bounded
    (fuel : Nat) {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    term.size ≤ fuel →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    WellFormedEnvWhenInitialized env₁ lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime ∧
      WellFormedTyWhenInitialized env₂ ty lifetime := by
  induction fuel generalizing env₁ env₂ typing lifetime term ty with
  | zero =>
      intro hsize _hrefs _hwellFormed _htyping
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
      intro hsize hrefs hwellFormed htyping
      refine TermTyping.rec
        (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
          term.size ≤ fuel.succ →
          currentTyping = typing →
          WellFormedEnvWhenInitialized env lifetime →
          WellFormedEnvWhenInitialized env₂ lifetime ∧
            WellFormedTyWhenInitialized env₂ ty lifetime)
        (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
          Term.size (.block lifetime terms) ≤ fuel.succ →
          currentTyping = typing →
          WellFormedEnvWhenInitialized env lifetime →
          WellFormedEnvWhenInitialized env₂ lifetime ∧
            WellFormedTyWhenInitialized env₂ ty lifetime)
        (fun {_env _typing _lifetime _value _ty} hvalueTyping _hsize
            htypingEq hwellFormed =>
          by
            subst htypingEq
            exact ⟨hwellFormed,
              WellFormedTy.whenInitialized
                (valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping)⟩)
        (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
            _hsize _htypingEq hwellFormed =>
          ⟨hwellFormed,
            copyTy_result_wellFormedWhenInitialized
              hwellFormed.1 hwellFormed.2 hLv hcopy⟩)
        (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
            hLv hnotWrite hmove _hsize _htypingEq hwellFormed =>
          move_preserves_wellFormedWhenInitialized
            hwellFormed hLv hnotWrite hmove)
        (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable
            _hwrite _hsize _htypingEq hwellFormed =>
          ⟨hwellFormed,
            WellFormedTyWhenInitialized.borrow
              (BorrowTargetsWellFormed.whenInitialized
                (BorrowTargetsWellFormed.singleton hLv
                  (LValTyping.lifetime_outlives_one_of_slots
                    hwellFormed.2 hLv)
                  (LValTyping.base_outlives_one_of_slots
                    hwellFormed.2 hLv)))⟩)
        (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
            _hsize _htypingEq hwellFormed =>
          ⟨hwellFormed,
            WellFormedTyWhenInitialized.borrow
              (BorrowTargetsWellFormed.whenInitialized
                (BorrowTargetsWellFormed.singleton hLv
                  (LValTyping.lifetime_outlives_one_of_slots
                    hwellFormed.2 hLv)
                  (LValTyping.base_outlives_one_of_slots
                    hwellFormed.2 hLv)))⟩)
        (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih hsize
            htypingEq hwellFormed =>
          let result := ih
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq hwellFormed
          ⟨result.1, WellFormedTyWhenInitialized.box result.2⟩)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
            hblockChild hterms hwellTy hdrop ih hsize htypingEq hwellFormed =>
          let bodyResult :=
            ih hsize htypingEq
              (WellFormedEnvWhenInitialized.weaken hwellFormed
                (LifetimeChild.outlives hblockChild))
          block_preserves_wellFormedWhenInitialized
            hblockChild bodyResult.1 hterms
            (WellFormedTy.whenInitialized hwellTy) hdrop)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
            _hfresh _hterm hfreshOut _hcohObl henv₃ ih hsize htypingEq
            hwellFormed =>
          by
            let result := ih
              (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
              htypingEq hwellFormed
            refine ⟨?_, WellFormedTyWhenInitialized.unit⟩
            rw [henv₃]
            exact WellFormedEnvWhenInitialized.update_fresh_ty
              result.1 result.2 hfreshOut)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs
              _oldTy _rhs _rhsTy}
            hRhs _hLhsPost hshape hwellRhs hwrite _hnoStale _hranked
            _hcoh hrhsTargets hnotWrite ih hsize htypingEq
            hwellFormed =>
          by
            let result := ih
              (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
              htypingEq hwellFormed
            have hrhsWF : EnvWriteRhsTargetsWellFormed _env₃ _rhsTy := hrhsTargets
            have hcbwf3 :=
              containedBorrowsWellFormedWhenInitialized_assign
                result.1.1 hrhsWF hwrite hnotWrite
            exact ⟨⟨hcbwf3,
                EnvWrite.preserves_slotsOutlive result.1.2 hwrite⟩,
                WellFormedTyWhenInitialized.unit⟩)
        (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih hsize
            htypingEq hwellFormed =>
          ih
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq hwellFormed)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
            _hterm _hrest ihHead ihRest hsize htypingEq hwellFormed =>
          let headResult := ihHead
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq hwellFormed
          ihRest
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq headResult.1)
        htyping hsize rfl hwellFormed

theorem typingPreservesWellFormedWhenInitialized_of_ruleCarriedObligations_core_bounded
    (fuel : Nat) {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    term.size ≤ fuel →
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    WellFormedEnvWhenInitialized env₁ lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime ∧
      WellFormedTyWhenInitialized env₂ ty lifetime := by
  induction fuel generalizing env₁ env₂ typing lifetime term ty with
  | zero =>
      intro hsize _hrefs _hwellFormed _htyping
      cases term <;> simp [Term.size] at hsize
  | succ fuel ihFuel =>
      intro hsize hrefs hwellFormed htyping
      refine TermTyping.rec
        (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
          term.size ≤ fuel.succ →
          currentTyping = typing →
          WellFormedEnvWhenInitialized env lifetime →
          WellFormedEnvWhenInitialized env₂ lifetime ∧
            WellFormedTyWhenInitialized env₂ ty lifetime)
        (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
          Term.size (.block lifetime terms) ≤ fuel.succ →
          currentTyping = typing →
          WellFormedEnvWhenInitialized env lifetime →
          WellFormedEnvWhenInitialized env₂ lifetime ∧
            WellFormedTyWhenInitialized env₂ ty lifetime)
        (fun {_env _typing _lifetime _value _ty} hvalueTyping _hsize
            htypingEq hwellFormed =>
          by
            subst htypingEq
            exact ⟨hwellFormed,
              WellFormedTy.whenInitialized
                (valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping)⟩)
        (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
            _hsize _htypingEq hwellFormed =>
          ⟨hwellFormed,
            copyTy_result_wellFormedWhenInitialized
              hwellFormed.1 hwellFormed.2 hLv hcopy⟩)
        (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
            hLv hnotWrite hmove _hsize _htypingEq hwellFormed =>
          move_preserves_wellFormedWhenInitialized
            hwellFormed hLv hnotWrite hmove)
        (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable
            _hwrite _hsize _htypingEq hwellFormed =>
          ⟨hwellFormed,
            WellFormedTyWhenInitialized.borrow
              (BorrowTargetsWellFormed.whenInitialized
                (BorrowTargetsWellFormed.singleton hLv
                  (LValTyping.lifetime_outlives_one_of_slots
                    hwellFormed.2 hLv)
                  (LValTyping.base_outlives_one_of_slots
                    hwellFormed.2 hLv)))⟩)
        (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
            _hsize _htypingEq hwellFormed =>
          ⟨hwellFormed,
            WellFormedTyWhenInitialized.borrow
              (BorrowTargetsWellFormed.whenInitialized
                (BorrowTargetsWellFormed.singleton hLv
                  (LValTyping.lifetime_outlives_one_of_slots
                    hwellFormed.2 hLv)
                  (LValTyping.base_outlives_one_of_slots
                    hwellFormed.2 hLv)))⟩)
        (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih hsize
            htypingEq hwellFormed =>
          let result := ih
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq hwellFormed
          ⟨result.1, WellFormedTyWhenInitialized.box result.2⟩)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
            hblockChild hterms hwellTy hdrop ih hsize htypingEq hwellFormed =>
          let bodyResult :=
            ih hsize htypingEq
              (WellFormedEnvWhenInitialized.weaken hwellFormed
                (LifetimeChild.outlives hblockChild))
          block_preserves_wellFormedWhenInitialized
            hblockChild bodyResult.1 hterms
            (WellFormedTy.whenInitialized hwellTy) hdrop)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
            _hfresh _hterm hfreshOut _hcohObl henv₃ ih hsize htypingEq
            hwellFormed =>
          by
            let result := ih
              (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
              htypingEq hwellFormed
            refine ⟨?_, WellFormedTyWhenInitialized.unit⟩
            rw [henv₃]
            exact WellFormedEnvWhenInitialized.update_fresh_ty
              result.1 result.2 hfreshOut)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs
              _oldTy _rhs _rhsTy}
            hRhs _hLhsPost _hshape _hwellRhs hwrite _hnoStale _hranked
            _hcoh hrhsTargets hnotWrite ih hsize htypingEq
            hwellFormed =>
          by
            let result := ih
              (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
              htypingEq hwellFormed
            have hrhsWF : EnvWriteRhsTargetsWellFormed _env₃ _rhsTy := hrhsTargets
            have hcbwf3 :=
              containedBorrowsWellFormedWhenInitialized_assign
                result.1.1 hrhsWF hwrite hnotWrite
            exact ⟨⟨hcbwf3,
                EnvWrite.preserves_slotsOutlive result.1.2 hwrite⟩,
                WellFormedTyWhenInitialized.unit⟩)
        (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih hsize
            htypingEq hwellFormed =>
          ih
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq hwellFormed)
        (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
            _hterm _hrest ihHead ihRest hsize htypingEq hwellFormed =>
          let headResult := ihHead
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq hwellFormed
          ihRest
            (by simp [Term.size, Term.sizeList] at hsize ⊢; omega)
            htypingEq headResult.1)
        htyping hsize rfl hwellFormed

theorem typingPreservesWellFormedWhenInitialized_of_ruleCarriedObligations
    {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    WellFormedEnvWhenInitialized env₁ lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime ∧
      WellFormedTyWhenInitialized env₂ ty lifetime := by
  intro hrefs hwellFormed htyping
  exact typingPreservesWellFormedWhenInitialized_of_ruleCarriedObligations_core_bounded
    term.size (Nat.le_refl _) hrefs hwellFormed htyping

theorem typingPreservesWellFormedWhenInitialized_of_sourceTerm
    {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    SourceTerm term →
    WellFormedEnvWhenInitialized env₁ lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime ∧
      WellFormedTyWhenInitialized env₂ ty lifetime := by
  intro hsource hwellFormed htyping
  exact typingPreservesWellFormedWhenInitialized_of_ruleCarriedObligations
    (fun env lifetime => storeTypingRefsWellFormed_empty env lifetime)
    hwellFormed
    (TermTyping.retype_of_sourceTerm hsource htyping)

theorem typingPreservesCoherentWhenInitialized_of_sourceTerm
    {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    SourceTerm term →
    WellFormedEnvWhenInitialized env₁ lifetime →
    CoherentWhenInitialized env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    CoherentWhenInitialized env₂ := by
  intro hsource hwellFormed hcoh htyping
  exact (TermTyping.rec
    (motive_1 := fun env _typing lifetime term ty env₂ _ =>
      SourceTerm term →
      WellFormedEnvWhenInitialized env lifetime →
      CoherentWhenInitialized env →
      WellFormedEnvWhenInitialized env₂ lifetime ∧
        CoherentWhenInitialized env₂)
    (motive_2 := fun env _typing lifetime terms _ty env₂ _ =>
      SourceTerm (.block lifetime terms) →
      WellFormedEnvWhenInitialized env lifetime →
      CoherentWhenInitialized env →
      WellFormedEnvWhenInitialized env₂ lifetime ∧
        CoherentWhenInitialized env₂)
    (fun _hvalueTyping _hsource hwell hcoh =>
      ⟨hwell, hcoh⟩)
    (fun _hLv _hcopy _hnotRead _hsource hwell hcoh =>
      ⟨hwell, hcoh⟩)
    (fun hLv hnotWrite hmove _hsource hwell hcoh =>
      ⟨(move_preserves_wellFormedWhenInitialized hwell hLv hnotWrite hmove).1,
        CoherentWhenInitialized.move hwell hnotWrite hmove hcoh⟩)
    (fun _hLv _hmutable _hnotWrite _hsource hwell hcoh =>
      ⟨hwell, hcoh⟩)
    (fun _hLv _hnotRead _hsource hwell hcoh =>
      ⟨hwell, hcoh⟩)
    (fun _hterm ih hsource hwell hcoh =>
      ih (SourceTerm.box_inner hsource) hwell hcoh)
    (fun hchild hterms hwellTy hdrop ih hsource hwell hcoh => by
      have bodyResult :=
        ih hsource
          (WellFormedEnvWhenInitialized.weaken hwell
            (LifetimeChild.outlives hchild))
          hcoh
      refine ⟨(block_preserves_wellFormedWhenInitialized hchild bodyResult.1
          hterms (WellFormedTy.whenInitialized hwellTy) hdrop).1, ?_⟩
      rw [hdrop]
      exact CoherentWhenInitialized.dropLifetime_child hchild bodyResult.1
        bodyResult.2)
    (fun _hfresh hterm hfreshOut hcohObl henv ih hsource hwell hcoh => by
      have innerResult := ih (SourceTerm.declare_inner hsource) hwell hcoh
      have hwellTy :=
        (typingPreservesWellFormedWhenInitialized_of_sourceTerm
          (SourceTerm.declare_inner hsource) hwell hterm).2
      refine ⟨?_, ?_⟩
      · rw [henv]
        exact WellFormedEnvWhenInitialized.update_fresh_ty
          innerResult.1 hwellTy hfreshOut
      · rw [henv]
        exact CoherentWhenInitialized.update_fresh_ty innerResult.1.1
          innerResult.2 hfreshOut hcohObl)
    (fun hRhs hLhsPost hshape hwellTy hwrite hnoStale hranked hcohOut
        hrhsTargets hnotWrite ih hsource hwell hcoh => by
      have htermTyping :=
        TermTyping.assign hRhs hLhsPost hshape hwellTy hwrite hnoStale
          hranked hcohOut hrhsTargets hnotWrite
      exact ⟨(typingPreservesWellFormedWhenInitialized_of_sourceTerm
          hsource hwell htermTyping).1, hcohOut⟩)
    (fun _hterm ih hsource hwell hcoh =>
      ih (SourceTerm.block_head hsource) hwell hcoh)
    (fun _hterm _hrest ihHead ihRest hsource hwell hcoh =>
      let headResult := ihHead (SourceTerm.block_head hsource) hwell hcoh
      ihRest (SourceTerm.block_tail hsource) headResult.1 headResult.2)
    htyping hsource hwellFormed hcoh).2

theorem borrowInvarianceWhenInitialized_emptyStoreTyping
    {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    WellFormedEnvWhenInitialized env₁ lifetime →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime := by
  intro hwellFormed htyping
  exact (typingPreservesWellFormedWhenInitialized_of_ruleCarriedObligations
    (fun env lifetime => storeTypingRefsWellFormed_empty env lifetime)
    hwellFormed htyping).1

theorem borrowInvarianceWhenInitialized_from_emptyEnv
    {env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime := by
  intro htyping
  exact borrowInvarianceWhenInitialized_emptyStoreTyping
    (wellFormedEnvWhenInitialized_empty lifetime) htyping

theorem typingPreservesWellFormed_of_ruleCarriedObligations
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime ∧
      WellFormedTyWhenInitialized env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact typingPreservesWellFormed_of_ruleCarriedObligations_core_bounded
    term.size (Nat.le_refl _) hrefs (WellFormedEnv.whenInitialized hwellFormed)
    htyping

theorem borrowInvariance_emptyStoreTyping {store : ProgramStore}
    {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    ValidState store term →
    ValidStoreTyping store term StoreTyping.empty →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime := by
  intro hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
  ⟨hwellFormedOutput, hwellFormedTy⟩
  exact hwellFormedOutput

/--
Borrow invariance through the rule-carried route.

Assignment rank/write-coherence and declaration fresh-slot coherence are part of
the strengthened typing derivation.
-/
theorem borrowInvariance_of_ruleCarriedObligations
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime := by
  intro hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping
  rcases typingPreservesWellFormed_of_ruleCarriedObligations
      hrefs hvalidState hvalidStoreTyping hwellFormed hsafe htyping with
    ⟨hwellFormedOutput, hwellFormedTy⟩
  exact hwellFormedOutput

/-- Source terms have a valid empty store typing in any store: their values
are units and integers. -/
theorem sourceTerm_validStoreTyping_empty_any {store : ProgramStore}
    {term : Term} :
    SourceTerm term →
    ValidStoreTyping store term StoreTyping.empty := by
  intro hsource value hmem
  have hsourceValue := hsource value hmem
  cases value with
  | unit => exact ⟨.unit, ValueTyping.unit, ValidPartialValue.unit⟩
  | int n => exact ⟨.int, ValueTyping.int, ValidPartialValue.int⟩
  | ref r => exact absurd hsourceValue (by simp [SourceValue])

/--
Lemma 4.9 well-formedness induction for source terms.

Source terms contain no reference values, so the store-typing
reference-well-formedness premise of
`typingPreservesWellFormed_of_ruleCarriedObligations` is not needed: the
typing derivation factors through the empty store typing
(`TermTyping.retype_of_sourceTerm`), whose reference invariant is trivial.
-/
theorem typingPreservesWellFormed_of_sourceTerm
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    SourceTerm term →
    ValidState store term →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime ∧
      WellFormedTyWhenInitialized env₂ ty lifetime := by
  intro hsource hvalidState hwellFormed hsafe htyping
  exact typingPreservesWellFormed_of_ruleCarriedObligations
    (fun env lifetime => storeTypingRefsWellFormed_empty env lifetime)
    hvalidState (sourceTerm_validStoreTyping_empty_any hsource) hwellFormed
    hsafe (TermTyping.retype_of_sourceTerm hsource htyping)

/-- Lemma 4.9, Borrow Invariance, for source terms (no store-typing premise). -/
theorem borrowInvariance_of_sourceTerm
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    SourceTerm term →
    ValidState store term →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnvWhenInitialized env₂ lifetime := by
  intro hsource hvalidState hwellFormed hsafe htyping
  exact (typingPreservesWellFormed_of_sourceTerm hsource hvalidState
    hwellFormed hsafe htyping).1

theorem writeProhibited_of_lvalTyping_var_in_type_core {env : Env}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} {x : Name} :
    LValTyping env lv partialTy lifetime →
    x ∈ PartialTy.vars partialTy →
    WriteProhibited env (.var x) := by
  intro htyping
  refine LValTyping.rec
    (motive_1 := fun _lv partialTy _lifetime _ =>
      x ∈ PartialTy.vars partialTy → WriteProhibited env (.var x))
    (motive_2 := fun _targets partialTy _lifetime _ =>
      x ∈ PartialTy.vars partialTy → WriteProhibited env (.var x))
    ?_ ?_ ?_ ?_ ?_ ?_ htyping
  · intro y slot hslot hv
    rcases partialTy_vars_mem_contains x hv with
      ⟨mutable, targets, hcontains, target, htarget, hbase⟩
    cases mutable
    · right
      exact ⟨y, targets, target, ⟨slot, hslot, hcontains⟩, htarget,
        by simp [PathConflicts, LVal.base, hbase]⟩
    · left
      exact ⟨y, targets, target, ⟨slot, hslot, hcontains⟩, htarget,
        by simp [PathConflicts, LVal.base, hbase]⟩
  · intro _lv inner _lifetime _hinner ih hv
    exact ih (by simpa [PartialTy.vars] using hv)
  · intro _lv inner _lifetime _hinner ih hv
    exact ih (by simpa [PartialTy.vars, Ty.vars] using hv)
  · intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
      _hborrow _htargets _ihBorrow ihTargets hv
    exact ihTargets hv
  · intro _target _ty _lifetime _htarget ihTarget hv
    exact ihTarget (by simpa [PartialTy.vars] using hv)
  · intro _target _rest _headTy _headLifetime _restLifetime _lifetime _restTy
      _unionTy _hhead _hrest hunion _hintersection ihHead ihRest hv
    rcases partialTyUnion_vars_subset hunion hv with hvHead | hvRest
    · exact ihHead (by simpa [PartialTy.vars] using hvHead)
    · exact ihRest hvRest

theorem writeProhibitedVia_or_base_of_lvalTyping_var_in_type_core {env : Env}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} {x : Name} :
    LValTyping env lv partialTy lifetime →
    x ∈ PartialTy.vars partialTy →
      (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
        LVal.base lv = x := by
  intro htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _lifetime _ =>
      x ∈ PartialTy.vars partialTy →
        (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
          LVal.base lv = x)
    (motive_2 := fun targets partialTy _lifetime _ =>
      x ∈ PartialTy.vars partialTy →
        (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
          ∃ target, target ∈ targets ∧ LVal.base target = x)
    (by
      intro y slot hslot hv
      by_cases hy : y = x
      · right
        simpa [LVal.base, hy]
      · left
        rcases partialTy_vars_mem_contains x hv with
          ⟨mutable, targets, hcontains, target, htarget, hbase⟩
        refine ⟨y, hy, ?_⟩
        cases mutable
        · exact Or.inr ⟨targets, target,
            ⟨slot, hslot, hcontains⟩, htarget,
            by simp [PathConflicts, LVal.base, hbase]⟩
        · exact Or.inl ⟨targets, target,
            ⟨slot, hslot, hcontains⟩, htarget,
            by simp [PathConflicts, LVal.base, hbase]⟩)
    (by
      intro _lv inner _lifetime _hinner ih hv
      exact ih (by simpa [PartialTy.vars] using hv))
    (by
      intro _lv inner _lifetime _hinner ih hv
      exact ih (by simpa [PartialTy.vars, Ty.vars] using hv))
    (by
      intro source mutable targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets ihBorrow ihTargets hv
      rcases ihTargets hv with hvia | htargetBase
      · exact Or.inl hvia
      · rcases htargetBase with ⟨target, htarget, hbaseTarget⟩
        have hxVars :
            x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
          have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
            List.mem_map_of_mem htarget
          simpa [PartialTy.vars, Ty.vars, hbaseTarget] using hbaseMem
        rcases ihBorrow hxVars with hvia | hbaseSource
        · exact Or.inl hvia
        · exact Or.inr (by simpa [LVal.base] using hbaseSource))
    (by
      intro target _ty _lifetime _htarget ihTarget hv
      rcases ihTarget (by simpa [PartialTy.vars] using hv) with hvia | hbase
      · exact Or.inl hvia
      · exact Or.inr ⟨target, by simp, hbase⟩)
    (by
      intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy
        _unionTy _hhead _hrest hunion _hintersection ihHead ihRest hv
      rcases partialTyUnion_vars_subset hunion hv with hvHead | hvRest
      · rcases ihHead (by simpa [PartialTy.vars] using hvHead) with hvia | hbase
        · exact Or.inl hvia
        · exact Or.inr ⟨target, by simp, hbase⟩
      · rcases ihRest hvRest with hvia | htargetBase
        · exact Or.inl hvia
        · rcases htargetBase with ⟨selected, hselected, hbase⟩
          exact Or.inr ⟨selected, by simp [hselected], hbase⟩)
    htyping

theorem writeProhibited_of_lvalTyping_var_in_type {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} {x : Name} :
    WellFormedEnv env current →
    LValTyping env lv partialTy lifetime →
    x ∈ PartialTy.vars partialTy →
    WriteProhibited env (.var x) := by
  intro _hwellFormed htyping hmem
  exact writeProhibited_of_lvalTyping_var_in_type_core htyping hmem

/-- Premise-free form of `writeProhibited_of_lvalTyping_var_in_type`. -/
theorem writeProhibited_of_lvalTyping_var_in_type_of_typing {env : Env}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} {x : Name} :
    LValTyping env lv partialTy lifetime →
    x ∈ PartialTy.vars partialTy →
    WriteProhibited env (.var x) := by
  exact writeProhibited_of_lvalTyping_var_in_type_core

/-- Slot-local version of `writeProhibited_of_lvalTyping_var_in_type`. -/
theorem writeProhibited_of_envSlot_var_in_type {env : Env}
    {slotName x : Name} {slot : EnvSlot} {partialTy : PartialTy} :
    env.slotAt slotName = some slot →
    slot.ty = partialTy →
    x ∈ PartialTy.vars partialTy →
    WriteProhibited env (.var x) := by
  intro hslot hty hv
  rcases partialTy_vars_mem_contains x hv with
    ⟨mutable, targets, hcontains, target, htarget, hbase⟩
  cases mutable
  · right
    exact ⟨slotName, targets, target,
      ⟨slot, hslot, by simpa [hty] using hcontains⟩, htarget,
      by simp [PathConflicts, LVal.base, hbase]⟩
  · left
    exact ⟨slotName, targets, target,
      ⟨slot, hslot, by simpa [hty] using hcontains⟩, htarget,
      by simp [PathConflicts, LVal.base, hbase]⟩

theorem lval_loc_var_writeProhibited_or_base {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} {x : Name} :
    WellFormedEnv env current →
    store ≈ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    store.loc lv = some (VariableProjection x) →
    WriteProhibited env (.var x) ∨ LVal.base lv = x := by
  intro hwellFormed hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _partialTy _lifetime _ =>
      store.loc lv = some (VariableProjection x) →
      WriteProhibited env (.var x) ∨ LVal.base lv = x)
    (motive_2 := fun targets _partialTy _lifetime _ =>
      ∀ target, target ∈ targets →
        store.loc target = some (VariableProjection x) →
        WriteProhibited env (.var x) ∨ LVal.base target = x)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro y _slot _hslot hloc
    right
    simp [ProgramStore.loc, VariableProjection] at hloc
    exact hloc
  · intro source inner _sourceLifetime hsource _ih hloc
    have hsourceAbs : LValLocationAbstraction store source (.box inner) :=
      lvalTyping_defined_location hwellFormed hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @box ownerLocation _ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          refine ⟨sourceLocation, sourceSlotLifetime, ?_⟩
          simpa [owningRef] using hsourceSlot
        rcases hheap (VariableProjection x) howns with ⟨address, hheapLoc⟩
        cases hheapLoc
  · intro source inner _sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstraction store source (.ty (.box inner)) :=
      lvalTyping_defined_location hwellFormed hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation _ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          refine ⟨sourceLocation, sourceSlotLifetime, ?_⟩
          simpa [owningRef] using hsourceSlot
        rcases hheap (VariableProjection x) howns with ⟨address, hheapLoc⟩
        cases hheapLoc
  · intro source mutable targets _borrowLifetime _targetLifetime _targetTy
      hborrow _htargets _ihBorrow ihTargets hloc
    have hsourceAbs :
        LValLocationAbstraction store source (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location hwellFormed hsafe hborrow
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, _sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrow borrowedLocation _mutable _targets selected hmem hselectedLoc =>
        have hderefLoc : store.loc source.deref = some borrowedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hborrowedEq : borrowedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hborrowedEq
        rcases ihTargets selected hmem hselectedLoc with hwp | hbase
        · exact Or.inl hwp
        · have hxVars :
              x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
            have hbaseMem : LVal.base selected ∈ targets.map LVal.base :=
              List.mem_map_of_mem hmem
            simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
          exact Or.inl
            (writeProhibited_of_lvalTyping_var_in_type
              hwellFormed hborrow hxVars)
  · intro target _ty _targetLifetime _htarget ih target' hmem hloc
    simp at hmem
    subst hmem
    exact ih hloc
  · intro target _rest _headTy _headLifetime _restLifetime _targetLifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection ihHead ihRest
      selected hmem hloc
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ihHead hloc
    · exact ihRest selected hselected hloc

/--
If resolving a typed lvalue reads a variable location, then either that variable
is the lvalue's syntactic base or writing it is prohibited.
-/
theorem locReads_var_writeProhibited_or_base {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} {x : Name} :
    WellFormedEnv env current →
    store ≈ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    RuntimeFrame.LocReads store lv (VariableProjection x) →
    WriteProhibited env (.var x) ∨ LVal.base lv = x := by
  intro hwellFormed hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _partialTy _lifetime _ =>
      RuntimeFrame.LocReads store lv (VariableProjection x) →
      WriteProhibited env (.var x) ∨ LVal.base lv = x)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro _y _slot _hslot hreads
    cases hreads
  · intro source _inner _sourceLifetime hsource ih hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibited_or_base hwellFormed hsafe hheap
            hsource hloc with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ih hinnerReads with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source _inner _sourceLifetime hsource ih hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibited_or_base hwellFormed hsafe hheap
            hsource hloc with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ih hinnerReads with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source _mutable _targets _borrowLifetime _targetLifetime _targetTy
      hborrow _htargets ihBorrow _ihTargets hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibited_or_base hwellFormed hsafe hheap
            hborrow hloc with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ihBorrow hinnerReads with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
  · intros
    trivial
  · intros
    trivial

/-- Premise-free (`∼ₛ`-only) form of `lval_loc_var_writeProhibited_or_base`. -/
theorem lval_loc_var_writeProhibited_or_base_of_safe {store : ProgramStore} {env : Env}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} {x : Name} :
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    store.loc lv = some (VariableProjection x) →
    WriteProhibited env (.var x) ∨ LVal.base lv = x := by
  intro hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _partialTy _lifetime _ =>
      store.loc lv = some (VariableProjection x) →
      WriteProhibited env (.var x) ∨ LVal.base lv = x)
    (motive_2 := fun targets _partialTy _lifetime _ =>
      ∀ target, target ∈ targets →
        store.loc target = some (VariableProjection x) →
        WriteProhibited env (.var x) ∨ LVal.base target = x)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro y _slot _hslot hloc
    right
    simp [ProgramStore.loc, VariableProjection] at hloc
    exact hloc
  · intro source inner _sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source (.box inner) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @box ownerLocation _ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          refine ⟨sourceLocation, sourceSlotLifetime, ?_⟩
          simpa [owningRef] using hsourceSlot
        rcases hheap (VariableProjection x) howns with ⟨address, hheapLoc⟩
        cases hheapLoc
  · intro source inner _sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source (.ty (.box inner)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation _ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          refine ⟨sourceLocation, sourceSlotLifetime, ?_⟩
          simpa [owningRef] using hsourceSlot
        rcases hheap (VariableProjection x) howns with ⟨address, hheapLoc⟩
        cases hheapLoc
  · intro source mutable targets _borrowLifetime _targetLifetime _targetTy
      hborrow _htargets _ihBorrow ihTargets hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location_whenInitialized hsafe hborrow
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, _sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrowLive borrowedLocation _mutable _targets selected _hinitialized hmem hselectedLoc =>
        have hderefLoc : store.loc source.deref = some borrowedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hborrowedEq : borrowedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hborrowedEq
        rcases ihTargets selected hmem hselectedLoc with hwp | hbase
        · exact Or.inl hwp
        · have hxVars :
              x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
            have hbaseMem : LVal.base selected ∈ targets.map LVal.base :=
              List.mem_map_of_mem hmem
            simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
          exact Or.inl
            (writeProhibited_of_lvalTyping_var_in_type_of_typing hborrow hxVars)
    | @borrowStale borrowedLocation _mutable _targets hstale =>
        have hinitialized : BorrowTargetsInitialized env targets := by
          intro target hmem
          rcases lvalTargetsTyping_member_strengthens _htargets target hmem with
            ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
          exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
        exact False.elim (hstale hinitialized)
  · intro target _ty _targetLifetime _htarget ih target' hmem hloc
    simp at hmem
    subst hmem
    exact ih hloc
  · intro target _rest _headTy _headLifetime _restLifetime _targetLifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection ihHead ihRest
      selected hmem hloc
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ihHead hloc
    · exact ihRest selected hselected hloc

/-- Premise-free (`∼ₛ`-only) form of `locReads_var_writeProhibited_or_base`. -/
theorem locReads_var_writeProhibited_or_base_of_safe {store : ProgramStore} {env : Env}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} {x : Name} :
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    RuntimeFrame.LocReads store lv (VariableProjection x) →
    WriteProhibited env (.var x) ∨ LVal.base lv = x := by
  intro hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _partialTy _lifetime _ =>
      RuntimeFrame.LocReads store lv (VariableProjection x) →
      WriteProhibited env (.var x) ∨ LVal.base lv = x)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  · intro _y _slot _hslot hreads
    cases hreads
  · intro source _inner _sourceLifetime hsource ih hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibited_or_base_of_safe hsafe hheap
            hsource hloc with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ih hinnerReads with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source _inner _sourceLifetime hsource ih hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibited_or_base_of_safe hsafe hheap
            hsource hloc with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ih hinnerReads with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source _mutable _targets _borrowLifetime _targetLifetime _targetTy
      hborrow _htargets ihBorrow _ihTargets hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibited_or_base_of_safe hsafe hheap
            hborrow hloc with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ihBorrow hinnerReads with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
  · intros
    trivial
  · intros
    trivial

theorem lval_loc_var_writeProhibitedVia_or_base_of_safe
    {store : ProgramStore} {env : Env}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} {x : Name} :
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    store.loc lv = some (VariableProjection x) →
      (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
        LVal.base lv = x := by
  intro hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _partialTy _lifetime _ =>
      store.loc lv = some (VariableProjection x) →
        (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
          LVal.base lv = x)
    (motive_2 := fun targets _partialTy _lifetime _ =>
      ∀ target, target ∈ targets →
        store.loc target = some (VariableProjection x) →
          (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
            LVal.base target = x)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  case var =>
    intro y _slot _hslot hloc
    right
    simp [ProgramStore.loc, VariableProjection] at hloc
    exact hloc
  case box =>
    intro source inner _sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source (.box inner) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @box ownerLocation _ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          refine ⟨sourceLocation, sourceSlotLifetime, ?_⟩
          simpa [owningRef] using hsourceSlot
        rcases hheap (VariableProjection x) howns with ⟨address, hheapLoc⟩
        cases hheapLoc
  case boxFull =>
    intro source inner _sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.box inner)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation _ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          refine ⟨sourceLocation, sourceSlotLifetime, ?_⟩
          simpa [owningRef] using hsourceSlot
        rcases hheap (VariableProjection x) howns with ⟨address, hheapLoc⟩
        cases hheapLoc
  case borrow =>
    intro source mutable targets _borrowLifetime _targetLifetime _targetTy
      hborrow htargets _ihBorrow ihTargets hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location_whenInitialized hsafe hborrow
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, _sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrowLive borrowedLocation _mutable _targets selected _hinitialized
        hmem hselectedLoc =>
        have hderefLoc : store.loc source.deref = some borrowedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hborrowedEq : borrowedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hborrowedEq
        rcases ihTargets selected hmem hselectedLoc with hvia | hbase
        · exact Or.inl hvia
        · have hxVars :
              x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
            have hbaseMem : LVal.base selected ∈ targets.map LVal.base :=
              List.mem_map_of_mem hmem
            simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
          exact
            writeProhibitedVia_or_base_of_lvalTyping_var_in_type_core
              (lv := source) hborrow hxVars
    | @borrowStale _borrowedLocation _mutable _targets hstale =>
        have hinitialized : BorrowTargetsInitialized env targets := by
          intro target hmem
          rcases lvalTargetsTyping_member_strengthens htargets target hmem with
            ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
          exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
        exact False.elim (hstale hinitialized)
  case singleton =>
    intro target _ty _targetLifetime _htarget ih target' hmem hloc
    simp at hmem
    subst hmem
    exact ih hloc
  case cons =>
    intro target _rest _headTy _headLifetime _restLifetime _targetLifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection ihHead ihRest
      selected hmem hloc
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ihHead hloc
    · exact ihRest selected hselected hloc

theorem locReads_var_writeProhibitedVia_or_base_of_safe
    {store : ProgramStore} {env : Env}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} {x : Name} :
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    RuntimeFrame.LocReads store lv (VariableProjection x) →
      (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
        LVal.base lv = x := by
  intro hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _partialTy _lifetime _ =>
      RuntimeFrame.LocReads store lv (VariableProjection x) →
        (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
          LVal.base lv = x)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  case var =>
    intro _y _slot _hslot hreads
    cases hreads
  case box =>
    intro source _inner _sourceLifetime hsource ih hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibitedVia_or_base_of_safe hsafe hheap
            hsource hloc with hvia | hbase
        · exact Or.inl hvia
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ih hinnerReads with hvia | hbase
        · exact Or.inl hvia
        · exact Or.inr (by simpa [LVal.base] using hbase)
  case boxFull =>
    intro source _inner _sourceLifetime hsource ih hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibitedVia_or_base_of_safe hsafe hheap
            hsource hloc with hvia | hbase
        · exact Or.inl hvia
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ih hinnerReads with hvia | hbase
        · exact Or.inl hvia
        · exact Or.inr (by simpa [LVal.base] using hbase)
  case borrow =>
    intro source _mutable _targets _borrowLifetime _targetLifetime _targetTy
      hborrow _htargets ihBorrow _ihTargets hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibitedVia_or_base_of_safe hsafe hheap
            hborrow hloc with hvia | hbase
        · exact Or.inl hvia
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ihBorrow hinnerReads with hvia | hbase
        · exact Or.inl hvia
        · exact Or.inr (by simpa [LVal.base] using hbase)
  case singleton =>
    intros
    trivial
  case cons =>
    intros
    trivial

/-- A location is either the root variable `x` itself or owned below it. -/
def ProtectedByBase (store : ProgramStore) (x : Name) (location : Location) : Prop :=
  location = VariableProjection x ∨
    ProgramStore.OwnsTransitively store (VariableProjection x) location

theorem ProtectedByBase.trans_owned {store : ProgramStore} {x : Name}
    {storage owned : Location} :
    ProtectedByBase store x storage →
    ProgramStore.OwnsAt store owned storage →
    ProtectedByBase store x owned := by
  intro hprotected howns
  rcases hprotected with hroot | hpath
  · subst hroot
    right
    exact ProgramStore.OwnsTransitively.direct howns
  · right
    exact ProgramStore.OwnsTransitively.trans_right hpath howns

theorem ProgramStore.OwnsTransitively.predecessor_eq_or_owned
    {store : ProgramStore} {root storage owned : Location} :
    ValidStore store →
    ProgramStore.OwnsTransitively store root owned →
    ProgramStore.OwnsAt store owned storage →
    storage = root ∨ ProgramStore.OwnsTransitively store root storage := by
  intro hvalid hpath hownsStorage
  induction hpath generalizing storage with
  | @direct root owned hownsRoot =>
      left
      exact (hvalid owned root storage hownsRoot hownsStorage).symm
  | @trans root middle owned hownsMiddle htail ih =>
      rcases ih hownsStorage with hstorageMiddle | hrootOwnsStorage
      · right
        subst hstorageMiddle
        exact ProgramStore.OwnsTransitively.direct hownsMiddle
      · right
        exact ProgramStore.OwnsTransitively.trans hownsMiddle hrootOwnsStorage

theorem ProtectedByBase.pred_of_ownsAt {store : ProgramStore} {x : Name}
    {storage owned : Location} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ProtectedByBase store x owned →
    ProgramStore.OwnsAt store owned storage →
    ProtectedByBase store x storage := by
  intro hvalid hheap hprotected howns
  rcases hprotected with hroot | hpath
  · subst hroot
    have hownsVar : ProgramStore.Owns store (VariableProjection x) :=
      ⟨storage, howns⟩
    rcases hheap (VariableProjection x) hownsVar with ⟨address, hlocation⟩
    cases hlocation
  · rcases ProgramStore.OwnsTransitively.predecessor_eq_or_owned
        hvalid hpath howns with hstorageRoot | hstoragePath
    · left
      exact hstorageRoot
    · right
      exact hstoragePath

theorem ProgramStore.OwnsAt.erase_to_store {store : ProgramStore}
    {erased storage owned : Location} :
    ProgramStore.OwnsAt (store.erase erased) owned storage →
    ProgramStore.OwnsAt store owned storage := by
  intro howns
  rcases howns with ⟨lifetime, hslot⟩
  exact ⟨lifetime, RuntimeFrame.slotAt_of_erase_slotAt hslot⟩

theorem ProgramStore.OwnsTransitively.erase_to_store {store : ProgramStore}
    {erased storage owned : Location} :
    ProgramStore.OwnsTransitively (store.erase erased) storage owned →
    ProgramStore.OwnsTransitively store storage owned := by
  intro hpath
  induction hpath with
  | direct howns =>
      exact ProgramStore.OwnsTransitively.direct
        (ProgramStore.OwnsAt.erase_to_store howns)
  | trans howns _htail ih =>
      exact ProgramStore.OwnsTransitively.trans
        (ProgramStore.OwnsAt.erase_to_store howns) ih

theorem ProtectedByBase.erase_to_store {store : ProgramStore}
    {erased location : Location} {x : Name} :
    ProtectedByBase (store.erase erased) x location →
    ProtectedByBase store x location := by
  intro hprotected
  rcases hprotected with hroot | hpath
  · exact Or.inl hroot
  · exact Or.inr (ProgramStore.OwnsTransitively.erase_to_store hpath)

theorem ProgramStore.OwnsAt.erase_of_storage_ne {store : ProgramStore}
    {erased storage owned : Location} :
    storage ≠ erased →
    ProgramStore.OwnsAt store owned storage →
    ProgramStore.OwnsAt (store.erase erased) owned storage := by
  intro hne howns
  rcases howns with ⟨lifetime, hslot⟩
  exact ⟨lifetime, by simpa [ProgramStore.erase, hne] using hslot⟩

theorem ProgramStore.OwnsTransitively.erase_of_not_protected
    {store : ProgramStore} {x : Name} {erased storage owned : Location} :
    ProtectedByBase store x storage →
    ¬ ProtectedByBase store x erased →
    ProgramStore.OwnsTransitively store storage owned →
    ProgramStore.OwnsTransitively (store.erase erased) storage owned := by
  intro hstorageProtected herased hpath
  induction hpath generalizing x with
  | @direct pathStorage pathOwned howns =>
      have hstorageNe : pathStorage ≠ erased := by
        intro h
        exact herased (by simpa [h] using hstorageProtected)
      exact ProgramStore.OwnsTransitively.direct
        (ProgramStore.OwnsAt.erase_of_storage_ne hstorageNe howns)
  | @trans pathStorage middle pathOwned howns htail ih =>
      have hstorageNe : pathStorage ≠ erased := by
        intro h
        exact herased (by simpa [h] using hstorageProtected)
      have hmiddleProtected : ProtectedByBase store x middle :=
        ProtectedByBase.trans_owned hstorageProtected howns
      exact ProgramStore.OwnsTransitively.trans
        (ProgramStore.OwnsAt.erase_of_storage_ne hstorageNe howns)
        (ih hmiddleProtected herased)

theorem ProtectedByBase.erase_of_not_protected {store : ProgramStore}
    {x : Name} {erased location : Location} :
    ProtectedByBase store x location →
    ¬ ProtectedByBase store x erased →
    ProtectedByBase (store.erase erased) x location := by
  intro hprotected herased
  rcases hprotected with hroot | hpath
  · exact Or.inl hroot
  · exact Or.inr
      (ProgramStore.OwnsTransitively.erase_of_not_protected
        (by left; rfl) herased hpath)

theorem dropsAvoids_of_protectedByBase_unprotected_values
    {store store' : ProgramStore} {values : List PartialValue}
    {x : Name} {location : Location} :
    Drops store values store' →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    (∀ value, value ∈ values →
      ∀ owned, owned ∈ partialValueOwningLocations value →
        ¬ ProtectedByBase store x owned) →
    ProtectedByBase store x location →
    DropsAvoids store values location := by
  intro hdrops
  induction hdrops generalizing x location with
  | nil =>
      intro _hvalid _hheap _hvaluesHeap _hunprotected _hprotected
      exact DropsAvoids.nil
  | nonOwner hnonOwner _hdrops ih =>
      intro hvalid hheap hvaluesHeap hunprotected hprotected
      exact DropsAvoids.nonOwner hnonOwner
        (ih hvalid hheap
          (by
            intro value hmem
            exact hvaluesHeap value (by simp [hmem]))
          (by
            intro value hmem owned howned
            exact hunprotected value (by simp [hmem]) owned howned)
          hprotected)
  | ownerMissing howner hmissing _hdrops ih =>
      intro hvalid hheap hvaluesHeap hunprotected hprotected
      exact DropsAvoids.ownerMissing howner hmissing
        (ih hvalid hheap
          (by
            intro value hmem
            exact hvaluesHeap value (by simp [hmem]))
          (by
            intro value hmem owned howned
            exact hunprotected value (by simp [hmem]) owned howned)
          hprotected)
  | ownerPresent howner hpresent _hdrops ih =>
      intro hvalid hheap hvaluesHeap hunprotected hprotected
      rename_i storeBefore _storeAfter ref slot rest
      have hrefUnprotected :
          ¬ ProtectedByBase storeBefore x ref.location :=
        hunprotected (.value (.ref ref)) (by simp) ref.location
          (mem_partialValueOwningLocations_ref_true howner)
      have hrefNeLocation : ref.location ≠ location := by
        intro h
        exact hrefUnprotected (by simpa [h] using hprotected)
      have hslotHeap : PartialValueOwnerTargetsHeap slot.value :=
        partialValueOwnerTargetsHeap_of_slot hheap hpresent
      exact DropsAvoids.ownerPresent howner hpresent hrefNeLocation
        (ih (validStore_erase hvalid) (storeOwnerTargetsHeap_erase hheap)
          (by
            intro value hmem
            simp at hmem
            rcases hmem with hslotValue | hrest
            · subst hslotValue
              exact hslotHeap
            · exact hvaluesHeap value (by simp [hrest]))
          (by
            intro value hmem owned howned hprotectedErased
            have hprotectedStore :
                ProtectedByBase storeBefore x owned :=
              ProtectedByBase.erase_to_store hprotectedErased
            simp at hmem
            rcases hmem with hslotValue | hrest
            · subst hslotValue
              have hownsSlot :
                  ProgramStore.OwnsAt storeBefore owned ref.location := by
                have hslotValueEq :
                    slot.value = .value (owningRef owned) :=
                  eq_owningRef_of_mem_partialValueOwningLocations howned
                exact ⟨slot.lifetime, by
                  cases slot with
                  | mk slotValue slotLifetime =>
                      cases hslotValueEq
                      simpa [owningRef] using hpresent⟩
              exact hrefUnprotected
                (ProtectedByBase.pred_of_ownsAt hvalid hheap
                  hprotectedStore hownsSlot)
            · exact hunprotected value (by simp [hrest]) owned howned
                hprotectedStore)
            (ProtectedByBase.erase_of_not_protected hprotected hrefUnprotected))

/-- If every owning location in a drop set is no longer owned by the store, then
no owning location in the drop set is protected by any variable base. -/
theorem dropValues_unprotected_of_disjoint {store : ProgramStore}
    {values : List PartialValue} :
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    (∀ owned, owned ∈ partialValuesOwningLocations values →
      ¬ ProgramStore.Owns store owned) →
    ∀ value, value ∈ values →
      ∀ owned, owned ∈ partialValueOwningLocations value →
      ∀ base, ¬ ProtectedByBase store base owned := by
  intro hheap hvaluesHeap hnotOwned value hmem owned howned base hprotected
  rcases hprotected with hroot | hpath
  · subst hroot
    rcases hvaluesHeap value hmem (VariableProjection base) howned with
      ⟨address, hheapLocation⟩
    cases hheapLocation
  · exact
      (hnotOwned owned
        (by
          simp [partialValuesOwningLocations]
          exact ⟨value, hmem, howned⟩))
      (ProgramStore.OwnsTransitively.to_owns hpath)

theorem protectedByBase_not_var_owned {store : ProgramStore} {x y : Name} :
    StoreOwnerTargetsHeap store →
    ProtectedByBase store x (VariableProjection y) →
    y = x := by
  intro hheap hprotected
  rcases hprotected with hvar | howns
  · cases hvar
    rfl
  · have hownsVar : ProgramStore.Owns store (VariableProjection y) :=
      ProgramStore.OwnsTransitively.to_owns howns
    rcases hheap (VariableProjection y) hownsVar with ⟨address, hheapLoc⟩
    cases hheapLoc

/--
If a typed lvalue resolves to, or reads while resolving, a location protected by
the ownership tree rooted at `x`, then the lvalue is rooted at `x` or writing `x`
is statically prohibited.
-/
theorem lval_loc_or_reads_protected_writeProhibited_or_base
    {store : ProgramStore} {env : Env} {current : Lifetime} {x : Name}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    (∀ {location},
      store.loc lv = some location →
      ProtectedByBase store x location →
      WriteProhibited env (.var x) ∨ LVal.base lv = x) ∧
    (∀ {location},
      RuntimeFrame.LocReads store lv location →
      ProtectedByBase store x location →
      WriteProhibited env (.var x) ∨ LVal.base lv = x) := by
  intro hwellFormed hsafe hvalidStore hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      (∀ {location},
        store.loc lv = some location →
        ProtectedByBase store x location →
        WriteProhibited env (.var x) ∨ LVal.base lv = x) ∧
      (∀ {location},
        RuntimeFrame.LocReads store lv location →
        ProtectedByBase store x location →
        WriteProhibited env (.var x) ∨ LVal.base lv = x))
    (motive_2 := fun targets partialTy lifetime _ =>
      (∀ target, target ∈ targets →
        ∀ {location},
          store.loc target = some location →
          ProtectedByBase store x location →
          WriteProhibited env (.var x) ∨ LVal.base target = x) ∧
      (∀ target, target ∈ targets →
        ∀ {location},
          RuntimeFrame.LocReads store target location →
          ProtectedByBase store x location →
          WriteProhibited env (.var x) ∨ LVal.base target = x))
    ?_ ?_ ?_ ?_ ?_ ?_ htyping
  · intro y slot hslot
    constructor
    · intro location hloc hprotected
      have hlocation : location = VariableProjection y := by
        exact (Option.some.inj hloc).symm
      subst hlocation
      right
      exact protectedByBase_not_var_owned hheap hprotected
    · intro location hreads _hprotected
      cases hreads
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc hprotected
      have hsourceAbs :
          LValLocationAbstraction store source (.box inner) :=
        lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              ProtectedByBase store x sourceLocation := by
            rcases hprotected with hroot | hpath
            · subst hroot
              have hownsVar : ProgramStore.Owns store (VariableProjection x) :=
                ⟨sourceLocation, hownsSource⟩
              rcases hheap (VariableProjection x) hownsVar with
                ⟨address, hheapLoc⟩
              cases hheapLoc
            · rcases ProgramStore.OwnsTransitively.predecessor_eq_or_owned
                  hvalidStore hpath hownsSource with hsourceRoot | hsourcePath
              · left
                exact hsourceRoot
              · right
                exact hsourcePath
          rcases ihSource.1 hsourceLoc hsourceProtected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
    · intro location hreads hprotected
      cases hreads with
      | here hsourceLoc =>
          rcases ihSource.1 hsourceLoc hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
      | there hsourceReads =>
          rcases ihSource.2 hsourceReads hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc hprotected
      have hsourceAbs :
          LValLocationAbstraction store source (.ty (.box inner)) :=
        lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @boxFull ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              ProtectedByBase store x sourceLocation := by
            rcases hprotected with hroot | hpath
            · subst hroot
              have hownsVar : ProgramStore.Owns store (VariableProjection x) :=
                ⟨sourceLocation, hownsSource⟩
              rcases hheap (VariableProjection x) hownsVar with
                ⟨address, hheapLoc⟩
              cases hheapLoc
            · rcases ProgramStore.OwnsTransitively.predecessor_eq_or_owned
                  hvalidStore hpath hownsSource with hsourceRoot | hsourcePath
              · left
                exact hsourceRoot
              · right
                exact hsourcePath
          rcases ihSource.1 hsourceLoc hsourceProtected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
    · intro location hreads hprotected
      cases hreads with
      | here hsourceLoc =>
          rcases ihSource.1 hsourceLoc hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
      | there hsourceReads =>
          rcases ihSource.2 hsourceReads hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets ihSource ihTargets
    constructor
    · intro location hloc hprotected
      have hsourceAbs :
          LValLocationAbstraction store source (.ty (.borrow mutable targets)) :=
        lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrow selectedLocation _mutable _targets selected hmem hselectedLoc =>
          have hderefLoc :
              store.loc source.deref = some selectedLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = selectedLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          rcases ihTargets.1 selected hmem hselectedLoc hprotected with
            hwp | hbaseSelected
          · exact Or.inl hwp
          · have hxVars :
  x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
              have hbaseMem : LVal.base selected ∈ targets.map LVal.base :=
                List.mem_map_of_mem hmem
              simpa [PartialTy.vars, Ty.vars, hbaseSelected] using hbaseMem
            exact Or.inl
              (writeProhibited_of_lvalTyping_var_in_type
                hwellFormed hsource hxVars)
    · intro location hreads hprotected
      cases hreads with
      | here hsourceLoc =>
          rcases ihSource.1 hsourceLoc hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
      | there hsourceReads =>
          rcases ihSource.2 hsourceReads hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro target ty lifetime htarget ihTarget
    constructor
    · intro selected hmem location hloc hprotected
      simp at hmem
      subst hmem
      exact ihTarget.1 hloc hprotected
    · intro selected hmem location hreads hprotected
      simp at hmem
      subst hmem
      exact ihTarget.2 hreads hprotected
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead hrest _hunion _hintersection ihHead ihRest
    constructor
    · intro selected hmem location hloc hprotected
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.1 hloc hprotected
      · exact ihRest.1 selected hselected hloc hprotected
    · intro selected hmem location hreads hprotected
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.2 hreads hprotected
      · exact ihRest.2 selected hselected hreads hprotected

theorem lval_loc_or_reads_protected_writeProhibited_or_base_whenInitialized
    {store : ProgramStore} {env : Env} {current : Lifetime} {x : Name}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    (∀ {location},
      store.loc lv = some location →
      ProtectedByBase store x location →
      WriteProhibited env (.var x) ∨ LVal.base lv = x) ∧
    (∀ {location},
      RuntimeFrame.LocReads store lv location →
      ProtectedByBase store x location →
      WriteProhibited env (.var x) ∨ LVal.base lv = x) := by
  intro hwellFormed hsafe hvalidStore hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      (∀ {location},
        store.loc lv = some location →
        ProtectedByBase store x location →
        WriteProhibited env (.var x) ∨ LVal.base lv = x) ∧
      (∀ {location},
        RuntimeFrame.LocReads store lv location →
        ProtectedByBase store x location →
        WriteProhibited env (.var x) ∨ LVal.base lv = x))
    (motive_2 := fun targets partialTy lifetime _ =>
      (∀ target, target ∈ targets →
        ∀ {location},
          store.loc target = some location →
          ProtectedByBase store x location →
          WriteProhibited env (.var x) ∨ LVal.base target = x) ∧
      (∀ target, target ∈ targets →
        ∀ {location},
          RuntimeFrame.LocReads store target location →
          ProtectedByBase store x location →
          WriteProhibited env (.var x) ∨ LVal.base target = x))
    ?_ ?_ ?_ ?_ ?_ ?_ htyping
  · intro y slot hslot
    constructor
    · intro location hloc hprotected
      have hlocation : location = VariableProjection y := by
        exact (Option.some.inj hloc).symm
      subst hlocation
      right
      exact protectedByBase_not_var_owned hheap hprotected
    · intro location hreads _hprotected
      cases hreads
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc hprotected
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source (.box inner) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              ProtectedByBase store x sourceLocation := by
            rcases hprotected with hroot | hpath
            · subst hroot
              have hownsVar : ProgramStore.Owns store (VariableProjection x) :=
                ⟨sourceLocation, hownsSource⟩
              rcases hheap (VariableProjection x) hownsVar with
                ⟨address, hheapLoc⟩
              cases hheapLoc
            · rcases ProgramStore.OwnsTransitively.predecessor_eq_or_owned
                  hvalidStore hpath hownsSource with hsourceRoot | hsourcePath
              · left
                exact hsourceRoot
              · right
                exact hsourcePath
          rcases ihSource.1 hsourceLoc hsourceProtected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
    · intro location hreads hprotected
      cases hreads with
      | here hsourceLoc =>
          rcases ihSource.1 hsourceLoc hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
      | there hsourceReads =>
          rcases ihSource.2 hsourceReads hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc hprotected
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source (.ty (.box inner)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @boxFull ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              ProtectedByBase store x sourceLocation := by
            rcases hprotected with hroot | hpath
            · subst hroot
              have hownsVar : ProgramStore.Owns store (VariableProjection x) :=
                ⟨sourceLocation, hownsSource⟩
              rcases hheap (VariableProjection x) hownsVar with
                ⟨address, hheapLoc⟩
              cases hheapLoc
            · rcases ProgramStore.OwnsTransitively.predecessor_eq_or_owned
                  hvalidStore hpath hownsSource with hsourceRoot | hsourcePath
              · left
                exact hsourceRoot
              · right
                exact hsourcePath
          rcases ihSource.1 hsourceLoc hsourceProtected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
    · intro location hreads hprotected
      cases hreads with
      | here hsourceLoc =>
          rcases ihSource.1 hsourceLoc hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
      | there hsourceReads =>
          rcases ihSource.2 hsourceReads hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets ihSource ihTargets
    constructor
    · intro location hloc hprotected
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source
            (.ty (.borrow mutable targets)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrowLive selectedLocation _mutable _targets selected _hinitialized
          hmem hselectedLoc =>
          have hderefLoc :
              store.loc source.deref = some selectedLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = selectedLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          rcases ihTargets.1 selected hmem hselectedLoc hprotected with
            hwp | hbaseSelected
          · exact Or.inl hwp
          · have hxVars :
                x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
              have hbaseMem : LVal.base selected ∈ targets.map LVal.base :=
                List.mem_map_of_mem hmem
              simpa [PartialTy.vars, Ty.vars, hbaseSelected] using hbaseMem
            exact Or.inl (writeProhibited_of_lvalTyping_var_in_type_core hsource hxVars)
      | @borrowStale _location _mutable _targets hstale =>
          have hinitialized : BorrowTargetsInitialized env targets := by
            intro target hmem
            rcases lvalTargetsTyping_member_strengthens htargets target hmem with
              ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
            exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
          exact False.elim (hstale hinitialized)
    · intro location hreads hprotected
      cases hreads with
      | here hsourceLoc =>
          rcases ihSource.1 hsourceLoc hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
      | there hsourceReads =>
          rcases ihSource.2 hsourceReads hprotected with hwp | hbase
          · exact Or.inl hwp
          · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro target ty lifetime htarget ihTarget
    constructor
    · intro selected hmem location hloc hprotected
      simp at hmem
      subst hmem
      exact ihTarget.1 hloc hprotected
    · intro selected hmem location hreads hprotected
      simp at hmem
      subst hmem
      exact ihTarget.2 hreads hprotected
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead hrest _hunion _hintersection ihHead ihRest
    constructor
    · intro selected hmem location hloc hprotected
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.1 hloc hprotected
      · exact ihRest.1 selected hselected hloc hprotected
    · intro selected hmem location hreads hprotected
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.2 hreads hprotected
      · exact ihRest.2 selected hselected hreads hprotected

theorem lval_loc_or_reads_protected_writeProhibitedVia_or_base_whenInitialized
    {store : ProgramStore} {env : Env} {current : Lifetime} {x : Name}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    (∀ {location},
      store.loc lv = some location →
      ProtectedByBase store x location →
        (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
          LVal.base lv = x) ∧
    (∀ {location},
      RuntimeFrame.LocReads store lv location →
      ProtectedByBase store x location →
        (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
          LVal.base lv = x) := by
  intro hwellFormed hsafe hvalidStore hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      (∀ {location},
        store.loc lv = some location →
        ProtectedByBase store x location →
          (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
            LVal.base lv = x) ∧
      (∀ {location},
        RuntimeFrame.LocReads store lv location →
        ProtectedByBase store x location →
          (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
            LVal.base lv = x))
    (motive_2 := fun targets partialTy lifetime _ =>
      (∀ target, target ∈ targets →
        ∀ {location},
          store.loc target = some location →
          ProtectedByBase store x location →
            (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
              LVal.base target = x) ∧
      (∀ target, target ∈ targets →
        ∀ {location},
          RuntimeFrame.LocReads store target location →
          ProtectedByBase store x location →
            (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
              LVal.base target = x))
    ?_ ?_ ?_ ?_ ?_ ?_ htyping
  · intro y slot hslot
    constructor
    · intro location hloc hprotected
      have hlocation : location = VariableProjection y := by
        exact (Option.some.inj hloc).symm
      subst hlocation
      right
      exact protectedByBase_not_var_owned hheap hprotected
    · intro location hreads _hprotected
      cases hreads
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc hprotected
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source (.box inner) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              ProtectedByBase store x sourceLocation := by
            rcases hprotected with hroot | hpath
            · subst hroot
              have hownsVar : ProgramStore.Owns store (VariableProjection x) :=
                ⟨sourceLocation, hownsSource⟩
              rcases hheap (VariableProjection x) hownsVar with
                ⟨address, hheapLoc⟩
              cases hheapLoc
            · rcases ProgramStore.OwnsTransitively.predecessor_eq_or_owned
                  hvalidStore hpath hownsSource with hsourceRoot | hsourcePath
              · left
                exact hsourceRoot
              · right
                exact hsourcePath
          rcases ihSource.1 hsourceLoc hsourceProtected with hvia | hbase
          · exact Or.inl hvia
          · exact Or.inr (by simpa [LVal.base] using hbase)
    · intro location hreads hprotected
      cases hreads with
      | here hsourceLoc =>
          rcases ihSource.1 hsourceLoc hprotected with hvia | hbase
          · exact Or.inl hvia
          · exact Or.inr (by simpa [LVal.base] using hbase)
      | there hsourceReads =>
          rcases ihSource.2 hsourceReads hprotected with hvia | hbase
          · exact Or.inl hvia
          · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc hprotected
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source (.ty (.box inner)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @boxFull ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          have hsourceProtected :
              ProtectedByBase store x sourceLocation := by
            rcases hprotected with hroot | hpath
            · subst hroot
              have hownsVar : ProgramStore.Owns store (VariableProjection x) :=
                ⟨sourceLocation, hownsSource⟩
              rcases hheap (VariableProjection x) hownsVar with
                ⟨address, hheapLoc⟩
              cases hheapLoc
            · rcases ProgramStore.OwnsTransitively.predecessor_eq_or_owned
                  hvalidStore hpath hownsSource with hsourceRoot | hsourcePath
              · left
                exact hsourceRoot
              · right
                exact hsourcePath
          rcases ihSource.1 hsourceLoc hsourceProtected with hvia | hbase
          · exact Or.inl hvia
          · exact Or.inr (by simpa [LVal.base] using hbase)
    · intro location hreads hprotected
      cases hreads with
      | here hsourceLoc =>
          rcases ihSource.1 hsourceLoc hprotected with hvia | hbase
          · exact Or.inl hvia
          · exact Or.inr (by simpa [LVal.base] using hbase)
      | there hsourceReads =>
          rcases ihSource.2 hsourceReads hprotected with hvia | hbase
          · exact Or.inl hvia
          · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets ihSource ihTargets
    constructor
    · intro location hloc hprotected
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source
            (.ty (.borrow mutable targets)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrowLive selectedLocation _mutable _targets selected _hinitialized
          hmem hselectedLoc =>
          have hderefLoc :
              store.loc source.deref = some selectedLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = selectedLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          rcases ihTargets.1 selected hmem hselectedLoc hprotected with
            hvia | hbaseSelected
          · exact Or.inl hvia
          · have hxVars :
                x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
              have hbaseMem : LVal.base selected ∈ targets.map LVal.base :=
                List.mem_map_of_mem hmem
              simpa [PartialTy.vars, Ty.vars, hbaseSelected] using hbaseMem
            exact
              writeProhibitedVia_or_base_of_lvalTyping_var_in_type_core
                (lv := source) hsource hxVars
      | @borrowStale _location _mutable _targets hstale =>
          have hinitialized : BorrowTargetsInitialized env targets := by
            intro target hmem
            rcases lvalTargetsTyping_member_strengthens htargets target hmem with
              ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
            exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
          exact False.elim (hstale hinitialized)
    · intro location hreads hprotected
      cases hreads with
      | here hsourceLoc =>
          rcases ihSource.1 hsourceLoc hprotected with hvia | hbase
          · exact Or.inl hvia
          · exact Or.inr (by simpa [LVal.base] using hbase)
      | there hsourceReads =>
          rcases ihSource.2 hsourceReads hprotected with hvia | hbase
          · exact Or.inl hvia
          · exact Or.inr (by simpa [LVal.base] using hbase)
  · intro target ty lifetime htarget ihTarget
    constructor
    · intro selected hmem location hloc hprotected
      simp at hmem
      subst hmem
      exact ihTarget.1 hloc hprotected
    · intro selected hmem location hreads hprotected
      simp at hmem
      subst hmem
      exact ihTarget.2 hreads hprotected
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead hrest _hunion _hintersection ihHead ihRest
    constructor
    · intro selected hmem location hloc hprotected
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.1 hloc hprotected
      · exact ihRest.1 selected hselected hloc hprotected
    · intro selected hmem location hreads hprotected
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.2 hreads hprotected
      · exact ihRest.2 selected hselected hreads hprotected

/--
Every location inspected while resolving a typed lvalue is protected by some
variable base.  For borrowed dereferences the protecting base can come from the
selected borrow target, not from the syntactic base of the dereference.
-/
theorem lval_loc_or_reads_protectedBySomeBase
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    (∀ {location},
      store.loc lv = some location →
      ∃ x, ProtectedByBase store x location) ∧
    (∀ {location},
      RuntimeFrame.LocReads store lv location →
      ∃ x, ProtectedByBase store x location) := by
  intro hwellFormed hsafe hvalidStore hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      (∀ {location},
        store.loc lv = some location →
        ∃ x, ProtectedByBase store x location) ∧
      (∀ {location},
        RuntimeFrame.LocReads store lv location →
        ∃ x, ProtectedByBase store x location))
    (motive_2 := fun targets partialTy lifetime _ =>
      (∀ target, target ∈ targets →
        ∀ {location},
          store.loc target = some location →
          ∃ x, ProtectedByBase store x location) ∧
      (∀ target, target ∈ targets →
        ∀ {location},
          RuntimeFrame.LocReads store target location →
          ∃ x, ProtectedByBase store x location))
    ?_ ?_ ?_ ?_ ?_ ?_ htyping
  · intro y slot hslot
    constructor
    · intro location hloc
      have hlocation : location = VariableProjection y := by
        exact (Option.some.inj hloc).symm
      subst hlocation
      exact ⟨y, Or.inl rfl⟩
    · intro location hreads
      cases hreads
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstraction store source (.box inner) :=
        lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst hlocationEq
          rcases ihSource.1 hsourceLoc with ⟨x, hprotectedSource⟩
          have hownsSource :
              ProgramStore.OwnsAt store location sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact ⟨x, ProtectedByBase.trans_owned hprotectedSource hownsSource⟩
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact ihSource.1 hsourceLoc
      | there hsourceReads =>
          exact ihSource.2 hsourceReads
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstraction store source (.ty (.box inner)) :=
        lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @boxFull ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          rcases ihSource.1 hsourceLoc with ⟨x, hprotectedSource⟩
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact ⟨x, ProtectedByBase.trans_owned hprotectedSource hownsSource⟩
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact ihSource.1 hsourceLoc
      | there hsourceReads =>
          exact ihSource.2 hsourceReads
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets ihSource ihTargets
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstraction store source (.ty (.borrow mutable targets)) :=
        lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrow selectedLocation _mutable _targets selected hmem hselectedLoc =>
          have hderefLoc :
              store.loc source.deref = some selectedLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = selectedLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst hlocationEq
          exact ihTargets.1 selected hmem hselectedLoc
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact ihSource.1 hsourceLoc
      | there hsourceReads =>
          exact ihSource.2 hsourceReads
  · intro target ty lifetime htarget ihTarget
    constructor
    · intro selected hmem location hloc
      simp at hmem
      subst hmem
      exact ihTarget.1 hloc
    · intro selected hmem location hreads
      simp at hmem
      subst hmem
      exact ihTarget.2 hreads
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead hrest _hunion _hintersection ihHead ihRest
    constructor
    · intro selected hmem location hloc
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.1 hloc
      · exact ihRest.1 selected hselected hloc
    · intro selected hmem location hreads
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.2 hreads
      · exact ihRest.2 selected hselected hreads

/--
Stale-aware version of `lval_loc_or_reads_protectedBySomeBase`.  Borrowed
dereferences are only followed when the borrow target list is initialized; a
typed dereference supplies that initialization from its target typing evidence.
-/
theorem lval_loc_or_reads_protectedBySomeBase_whenInitialized
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    (∀ {location},
      store.loc lv = some location →
      ∃ x, ProtectedByBase store x location) ∧
    (∀ {location},
      RuntimeFrame.LocReads store lv location →
      ∃ x, ProtectedByBase store x location) := by
  intro hwellFormed hsafe hvalidStore hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      (∀ {location},
        store.loc lv = some location →
        ∃ x, ProtectedByBase store x location) ∧
      (∀ {location},
        RuntimeFrame.LocReads store lv location →
        ∃ x, ProtectedByBase store x location))
    (motive_2 := fun targets partialTy lifetime _ =>
      (∀ target, target ∈ targets →
        ∀ {location},
          store.loc target = some location →
          ∃ x, ProtectedByBase store x location) ∧
      (∀ target, target ∈ targets →
        ∀ {location},
          RuntimeFrame.LocReads store target location →
          ∃ x, ProtectedByBase store x location))
    ?_ ?_ ?_ ?_ ?_ ?_ htyping
  · intro y slot hslot
    constructor
    · intro location hloc
      have hlocation : location = VariableProjection y := by
        exact (Option.some.inj hloc).symm
      subst hlocation
      exact ⟨y, Or.inl rfl⟩
    · intro location hreads
      cases hreads
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source (.box inner) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst hlocationEq
          rcases ihSource.1 hsourceLoc with ⟨x, hprotectedSource⟩
          have hownsSource :
              ProgramStore.OwnsAt store location sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact ⟨x, ProtectedByBase.trans_owned hprotectedSource hownsSource⟩
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact ihSource.1 hsourceLoc
      | there hsourceReads =>
          exact ihSource.2 hsourceReads
  · intro source inner lifetime hsource ihSource
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source (.ty (.box inner)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @boxFull ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          rcases ihSource.1 hsourceLoc with ⟨x, hprotectedSource⟩
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact ⟨x, ProtectedByBase.trans_owned hprotectedSource hownsSource⟩
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact ihSource.1 hsourceLoc
      | there hsourceReads =>
          exact ihSource.2 hsourceReads
  · intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets ihSource ihTargets
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source
            (.ty (.borrow mutable targets)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @borrowLive selectedLocation _mutable _targets selected _hinitialized
          hmem hselectedLoc =>
          have hderefLoc :
              store.loc source.deref = some selectedLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = selectedLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst hlocationEq
          exact ihTargets.1 selected hmem hselectedLoc
      | @borrowStale _location _mutable _targets hstale =>
          have hinitialized : BorrowTargetsInitialized env targets := by
            intro target hmem
            rcases lvalTargetsTyping_member_strengthens htargets target hmem with
              ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
            exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
          exact False.elim (hstale hinitialized)
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact ihSource.1 hsourceLoc
      | there hsourceReads =>
          exact ihSource.2 hsourceReads
  · intro target ty lifetime htarget ihTarget
    constructor
    · intro selected hmem location hloc
      simp at hmem
      subst hmem
      exact ihTarget.1 hloc
    · intro selected hmem location hreads
      simp at hmem
      subst hmem
      exact ihTarget.2 hreads
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      hhead hrest _hunion _hintersection ihHead ihRest
    constructor
    · intro selected hmem location hloc
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.1 hloc
      · exact ihRest.1 selected hselected hloc
    · intro selected hmem location hreads
      simp at hmem
      rcases hmem with hselected | hselected
      · subst hselected
        exact ihHead.2 hreads
      · exact ihRest.2 selected hselected hreads

/-- A lifetime drop avoids a variable whose environment slot outlives the parent lifetime. -/
theorem dropsAvoids_var_of_base_outlives_lifetimeDrop
    {store store' : ProgramStore} {env : Env} {dropSet : List PartialValue}
    {parent child : Lifetime} {x : Name} {slot : EnvSlot} :
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location storeSlot,
        store.slotAt location = some storeSlot ∧
          storeSlot.lifetime = child ∧
          value = PartialValue.value
            (Value.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeChild parent child →
    env.slotAt x = some slot →
    slot.lifetime ≤ parent →
    DropsAvoids store dropSet (VariableProjection x) := by
  intro hsafe hheap hdropSet hdrops hchild henvSlot hslotParent
  rcases hsafe.2 x slot henvSlot with ⟨oldValue, hstoreSlot, _hvalid⟩
  exact dropsAvoids_var_of_not_owning_var hdrops hheap (by
    intro dropValue hmem hownsVar
    rcases (hdropSet dropValue).mp hmem with
      ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
    have howned : (VariableProjection x : Location) = dropLocation :=
      eq_location_of_mem_lifetime_drop_value hdropValue hownsVar
    subst howned
    have hdropSlotEq :
        dropSlot = { value := oldValue, lifetime := slot.lifetime } := by
      rw [hstoreSlot] at hdropSlot
      injection hdropSlot with hdropSlotEq
      exact hdropSlotEq.symm
    subst hdropSlotEq
    have hchildParent : child ≤ parent := by
      rw [← hdropLifetime]
      exact hslotParent
    exact LifetimeChild.not_child_outlives_parent hchild hchildParent)

theorem dropsAvoids_var_of_base_outlives_lifetimeDrop_whenInitialized
    {store store' : ProgramStore} {env : Env} {dropSet : List PartialValue}
    {parent child : Lifetime} {x : Name} {slot : EnvSlot} :
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location storeSlot,
        store.slotAt location = some storeSlot ∧
          storeSlot.lifetime = child ∧
          value = PartialValue.value
            (Value.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeChild parent child →
    env.slotAt x = some slot →
    slot.lifetime ≤ parent →
    DropsAvoids store dropSet (VariableProjection x) := by
  intro hsafe hheap hdropSet hdrops hchild henvSlot hslotParent
  rcases hsafe.2 x slot henvSlot with ⟨oldValue, hstoreSlot, _hvalid⟩
  exact dropsAvoids_var_of_not_owning_var hdrops hheap (by
    intro dropValue hmem hownsVar
    rcases (hdropSet dropValue).mp hmem with
      ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
    have howned : (VariableProjection x : Location) = dropLocation :=
      eq_location_of_mem_lifetime_drop_value hdropValue hownsVar
    subst howned
    have hdropSlotEq :
        dropSlot = { value := oldValue, lifetime := slot.lifetime } := by
      rw [hstoreSlot] at hdropSlot
      injection hdropSlot with hdropSlotEq
      exact hdropSlotEq.symm
    subst hdropSlotEq
    have hchildParent : child ≤ parent := by
      rw [← hdropLifetime]
      exact hslotParent
    exact LifetimeChild.not_child_outlives_parent hchild hchildParent)

/--
Lifetime drops avoid every location inspected while resolving a typed lvalue whose
base outlives the parent lifetime.  Borrowed dereferences use the selected target's
own borrow-target well-formedness witness.
-/
theorem lval_loc_or_reads_dropsAvoids_lifetime
    {store store' : ProgramStore} {env : Env} {dropSet : List PartialValue}
    {parent child : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    WellFormedEnv env child →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location storeSlot,
        store.slotAt location = some storeSlot ∧
          storeSlot.lifetime = child ∧
          value = PartialValue.value
            (Value.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeDropOwnersDisjoint store child →
    LifetimeChild parent child →
    LValBaseOutlives env lv parent →
    LValTyping env lv partialTy lifetime →
    lifetime ≤ parent →
      (∀ {location},
        store.loc lv = some location → DropsAvoids store dropSet location) ∧
      (∀ {location},
        RuntimeFrame.LocReads store lv location →
          DropsAvoids store dropSet location) := by
  intro hwellFormed hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint
    hchild hbase htyping houtlives
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      LValBaseOutlives env lv parent →
      lifetime ≤ parent →
        (∀ {location},
          store.loc lv = some location → DropsAvoids store dropSet location) ∧
        (∀ {location},
          RuntimeFrame.LocReads store lv location →
            DropsAvoids store dropSet location))
    (motive_2 := fun targets partialTy lifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      lifetime ≤ parent →
      ∀ target, target ∈ targets →
        (∀ {location},
          store.loc target = some location → DropsAvoids store dropSet location) ∧
        (∀ {location},
          RuntimeFrame.LocReads store target location →
            DropsAvoids store dropSet location))
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping hbase houtlives
  case var =>
    intro x slot hslot _hbase hslotParent
    constructor
    · intro location hloc
      have hlocation : location = VariableProjection x :=
        (Option.some.inj hloc).symm
      subst hlocation
      exact dropsAvoids_var_of_base_outlives_lifetimeDrop
        hsafe.whenInitialized hheap hdropSet hdrops hchild hslot hslotParent
    · intro location hreads
      cases hreads
  case box =>
    intro source inner sourceLifetime hsource ihSource hbaseSource
      hsourceLifetimeParent
    have hsourceAvoid := ihSource hbaseSource hsourceLifetimeParent
    constructor
    · intro location hloc
      have hsourceAbs : LValLocationAbstraction store source (.box inner) :=
        lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
      cases hsourceValid with
      | @box ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hsourceLocationAvoid : DropsAvoids store dropSet sourceLocation :=
            hsourceAvoid.1 hsourceLoc
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceSlotLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact dropsAvoids_of_protected_owner hdrops hvalidStore hownsSource
            hsourceLocationAvoid (by
              intro dropValue hmem howned
              rcases (hdropSet dropValue).mp hmem with
                ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
              have hdropEq : ownerLocation = dropLocation :=
                eq_location_of_mem_lifetime_drop_value hdropValue howned
              subst hdropEq
              exact hdropDisjoint ownerLocation dropSlot hdropSlot hdropLifetime
                ⟨sourceLocation, hownsSource⟩)
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact hsourceAvoid.1 hsourceLoc
      | there hsourceReads =>
          exact hsourceAvoid.2 hsourceReads
  case boxFull =>
    intro source inner sourceLifetime hsource ihSource hbaseSource
      hsourceLifetimeParent
    have hsourceAvoid := ihSource hbaseSource hsourceLifetimeParent
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstraction store source (.ty (.box inner)) :=
        lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
      cases hsourceValid with
      | @boxFull ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hsourceLocationAvoid : DropsAvoids store dropSet sourceLocation :=
            hsourceAvoid.1 hsourceLoc
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceSlotLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact dropsAvoids_of_protected_owner hdrops hvalidStore hownsSource
            hsourceLocationAvoid (by
              intro dropValue hmem howned
              rcases (hdropSet dropValue).mp hmem with
                ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
              have hdropEq : ownerLocation = dropLocation :=
                eq_location_of_mem_lifetime_drop_value hdropValue howned
              subst hdropEq
              exact hdropDisjoint ownerLocation dropSlot hdropSlot hdropLifetime
                ⟨sourceLocation, hownsSource⟩)
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact hsourceAvoid.1 hsourceLoc
      | there hsourceReads =>
          exact hsourceAvoid.2 hsourceReads
  case borrow =>
    intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets ihSource ihTargets hbaseSource htargetLifetimeParent
    have hborrowLifetimeParent : borrowLifetime ≤ parent :=
      LValTyping.lifetime_outlives_of_base_outlives_one
        hwellFormed.1 hsource hbaseSource
    have hsourceAvoid := ihSource hbaseSource hborrowLifetimeParent
    have hwellTargetsAtBorrow :
        BorrowTargetsWellFormed env targets borrowLifetime :=
      LValTyping.containedBorrowTargetsWellFormed_at_lifetime
        hwellFormed.1 hsource PartialTyContains.here
    have hwellTargetsParent : BorrowTargetsWellFormed env targets parent :=
      BorrowTargetsWellFormed.weaken hwellTargetsAtBorrow hborrowLifetimeParent
    have hbaseTargets :
        ∀ target, target ∈ targets → LValBaseOutlives env target parent := by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellTargetsParent target htarget with
        ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
      exact hbaseTarget
    have htargetsAvoid := ihTargets hbaseTargets htargetLifetimeParent
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstraction store source (.ty (.borrow mutable targets)) :=
        lvalTyping_defined_location hwellFormed hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
      cases hsourceValid with
      | @borrow selectedLocation _mutable _targets selected hmem hselectedLoc =>
          have hderefLoc :
              store.loc source.deref = some selectedLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = selectedLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          exact (htargetsAvoid selected hmem).1 hselectedLoc
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact hsourceAvoid.1 hsourceLoc
      | there hsourceReads =>
          exact hsourceAvoid.2 hsourceReads
  case singleton =>
    intro onlyTarget ty targetLifetime htarget ihTarget hbaseTargets
      htargetLifetimeParent queried hmem
    have hqueriedEq : queried = onlyTarget := by
      simpa using hmem
    subst queried
    exact ihTarget (hbaseTargets onlyTarget (by simp)) htargetLifetimeParent
  case cons =>
    intro headTarget rest headTy headLifetime restLifetime targetLifetime restTy
      unionTy hhead hrest hunion hintersection ihHead ihRest hbaseTargets
      htargetLifetimeParent queried hmem
    simp at hmem
    rcases hmem with hqueriedHead | hqueriedRest
    · subst queried
      exact ihHead (hbaseTargets headTarget (by simp))
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) htargetLifetimeParent)
    · exact ihRest
        (by
          intro target htarget
          exact hbaseTargets target (by simp [htarget]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) htargetLifetimeParent)
        queried hqueriedRest

/-- Stale-aware version of `lval_loc_or_reads_dropsAvoids_lifetime`. -/
theorem lval_loc_or_reads_dropsAvoids_lifetime_whenInitialized
    {store store' : ProgramStore} {env : Env} {dropSet : List PartialValue}
    {parent child : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    WellFormedEnvWhenInitialized env child →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location storeSlot,
        store.slotAt location = some storeSlot ∧
          storeSlot.lifetime = child ∧
          value = PartialValue.value
            (Value.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeDropOwnersDisjoint store child →
    LifetimeChild parent child →
    LValBaseOutlives env lv parent →
    LValTyping env lv partialTy lifetime →
    lifetime ≤ parent →
      (∀ {location},
        store.loc lv = some location → DropsAvoids store dropSet location) ∧
      (∀ {location},
        RuntimeFrame.LocReads store lv location →
          DropsAvoids store dropSet location) := by
  intro hwellFormed hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint
    hchild hbase htyping houtlives
  refine LValTyping.rec
    (motive_1 := fun lv partialTy lifetime _ =>
      LValBaseOutlives env lv parent →
      lifetime ≤ parent →
        (∀ {location},
          store.loc lv = some location → DropsAvoids store dropSet location) ∧
        (∀ {location},
          RuntimeFrame.LocReads store lv location →
            DropsAvoids store dropSet location))
    (motive_2 := fun targets partialTy lifetime _ =>
      (∀ target, target ∈ targets → LValBaseOutlives env target parent) →
      lifetime ≤ parent →
      ∀ target, target ∈ targets →
        (∀ {location},
          store.loc target = some location → DropsAvoids store dropSet location) ∧
        (∀ {location},
          RuntimeFrame.LocReads store target location →
            DropsAvoids store dropSet location))
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping hbase houtlives
  case var =>
    intro x slot hslot _hbase hslotParent
    constructor
    · intro location hloc
      have hlocation : location = VariableProjection x :=
        (Option.some.inj hloc).symm
      subst hlocation
      exact dropsAvoids_var_of_base_outlives_lifetimeDrop_whenInitialized
        hsafe hheap hdropSet hdrops hchild hslot hslotParent
    · intro location hreads
      cases hreads
  case box =>
    intro source inner sourceLifetime hsource ihSource hbaseSource
      hsourceLifetimeParent
    have hsourceAvoid := ihSource hbaseSource hsourceLifetimeParent
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source (.box inner) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
      cases hsourceValid with
      | @box ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hsourceLocationAvoid : DropsAvoids store dropSet sourceLocation :=
            hsourceAvoid.1 hsourceLoc
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceSlotLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact dropsAvoids_of_protected_owner hdrops hvalidStore hownsSource
            hsourceLocationAvoid (by
              intro dropValue hmem howned
              rcases (hdropSet dropValue).mp hmem with
                ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
              have hdropEq : ownerLocation = dropLocation :=
                eq_location_of_mem_lifetime_drop_value hdropValue howned
              subst hdropEq
              exact hdropDisjoint ownerLocation dropSlot hdropSlot hdropLifetime
                ⟨sourceLocation, hownsSource⟩)
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact hsourceAvoid.1 hsourceLoc
      | there hsourceReads =>
          exact hsourceAvoid.2 hsourceReads
  case boxFull =>
    intro source inner sourceLifetime hsource ihSource hbaseSource
      hsourceLifetimeParent
    have hsourceAvoid := ihSource hbaseSource hsourceLifetimeParent
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source (.ty (.box inner)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
      cases hsourceValid with
      | @boxFull ownerLocation ownerSlot _ hownedSlot _hinnerValid =>
          have hderefLoc :
              store.loc source.deref = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = ownerLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          have hsourceLocationAvoid : DropsAvoids store dropSet sourceLocation :=
            hsourceAvoid.1 hsourceLoc
          have hownsSource :
              ProgramStore.OwnsAt store ownerLocation sourceLocation :=
            ⟨sourceSlotLifetime, by simpa [owningRef] using hsourceSlot⟩
          exact dropsAvoids_of_protected_owner hdrops hvalidStore hownsSource
            hsourceLocationAvoid (by
              intro dropValue hmem howned
              rcases (hdropSet dropValue).mp hmem with
                ⟨dropLocation, dropSlot, hdropSlot, hdropLifetime, hdropValue⟩
              have hdropEq : ownerLocation = dropLocation :=
                eq_location_of_mem_lifetime_drop_value hdropValue howned
              subst hdropEq
              exact hdropDisjoint ownerLocation dropSlot hdropSlot hdropLifetime
                ⟨sourceLocation, hownsSource⟩)
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact hsourceAvoid.1 hsourceLoc
      | there hsourceReads =>
          exact hsourceAvoid.2 hsourceReads
  case borrow =>
    intro source mutable targets borrowLifetime targetLifetime targetTy
      hsource htargets ihSource ihTargets hbaseSource htargetLifetimeParent
    have hborrowLifetimeParent : borrowLifetime ≤ parent :=
      LValTyping.lifetime_outlives_of_base_outlives_one_whenInitialized
        hwellFormed.1 hsource hbaseSource
    have hsourceAvoid := ihSource hbaseSource hborrowLifetimeParent
    have hwellTargetsAtBorrow :
        BorrowTargetsWellFormedWhenInitialized env targets borrowLifetime :=
      LValTyping.containedBorrowTargetsWellFormedWhenInitialized_at_lifetime
        hwellFormed.1 hsource PartialTyContains.here
    have hwellTargetsParent :
        BorrowTargetsWellFormedWhenInitialized env targets parent :=
      BorrowTargetsWellFormedWhenInitialized.weaken
        hwellTargetsAtBorrow hborrowLifetimeParent
    have hbaseTargets :
        ∀ target, target ∈ targets → LValBaseOutlives env target parent := by
      intro target htarget
      exact (hwellTargetsParent target htarget).1
    have htargetsAvoid := ihTargets hbaseTargets htargetLifetimeParent
    constructor
    · intro location hloc
      have hsourceAbs :
          LValLocationAbstractionWhenInitialized env store source
            (.ty (.borrow mutable targets)) :=
        lvalTyping_defined_location_whenInitialized hsafe hsource
      rcases hsourceAbs with
        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
      rcases sourceSlot with ⟨sourceValue, sourceSlotLifetime⟩
      cases hsourceValid with
      | @borrowLive selectedLocation _mutable _targets selected _hinitialized
          hmem hselectedLoc =>
          have hderefLoc :
              store.loc source.deref = some selectedLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hlocationEq : location = selectedLocation := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst location
          exact (htargetsAvoid selected hmem).1 hselectedLoc
      | @borrowStale _location _mutable _targets hstale =>
          have hinitialized : BorrowTargetsInitialized env targets := by
            intro target hmem
            rcases lvalTargetsTyping_member_strengthens htargets target hmem with
              ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
            exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
          exact False.elim (hstale hinitialized)
    · intro location hreads
      cases hreads with
      | here hsourceLoc =>
          exact hsourceAvoid.1 hsourceLoc
      | there hsourceReads =>
          exact hsourceAvoid.2 hsourceReads
  case singleton =>
    intro onlyTarget ty targetLifetime htarget ihTarget hbaseTargets
      htargetLifetimeParent queried hmem
    have hqueriedEq : queried = onlyTarget := by
      simpa using hmem
    subst queried
    exact ihTarget (hbaseTargets onlyTarget (by simp)) htargetLifetimeParent
  case cons =>
    intro headTarget rest headTy headLifetime restLifetime targetLifetime restTy
      unionTy hhead hrest hunion hintersection ihHead ihRest hbaseTargets
      htargetLifetimeParent queried hmem
    simp at hmem
    rcases hmem with hqueriedHead | hqueriedRest
    · subst queried
      exact ihHead (hbaseTargets headTarget (by simp))
        (LifetimeOutlives.trans
          (LifetimeIntersection.left_le hintersection) htargetLifetimeParent)
    · exact ihRest
        (by
          intro target htarget
          exact hbaseTargets target (by simp [htarget]))
        (LifetimeOutlives.trans
          (LifetimeIntersection.right_le hintersection) htargetLifetimeParent)
        queried hqueriedRest

/-- Borrow dependencies inside a value whose type outlives a parent lifetime survive
the runtime drop of an immediate child lifetime. -/
theorem borrowDependency_dropsAvoids_lifetime
    {store store' : ProgramStore} {env : Env} {dropSet : List PartialValue}
    {parent child slotLifetime : Lifetime} {value : PartialValue}
    {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnv env child →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location storeSlot,
        store.slotAt location = some storeSlot ∧
          storeSlot.lifetime = child ∧
          value = PartialValue.value
            (Value.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeDropOwnersDisjoint store child →
    LifetimeChild parent child →
    slotLifetime ≤ parent →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    DropsAvoids store dropSet dependency := by
  intro hwellFormed hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint
    hchild hslotParent hborrows hdependency
  induction hdependency generalizing env slotLifetime parent with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨targetTy, targetLifetime, htargetTyping, htargetOutlives, hbaseTarget⟩
      have htargetParent : targetLifetime ≤ parent :=
        LifetimeOutlives.trans htargetOutlives hslotParent
      have hbaseParent : LValBaseOutlives env target parent := by
        rcases hbaseTarget with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        exact ⟨baseSlot, hbaseSlot,
          LifetimeOutlives.trans hbaseOutlives hslotParent⟩
      exact (lval_loc_or_reads_dropsAvoids_lifetime
        hwellFormed hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint
        hchild hbaseParent htargetTyping htargetParent).2 hreads
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      exact ih (env := env) (slotLifetime := slotLifetime) (parent := parent)
        hwellFormed hsafe hchild hslotParent hinnerBorrows
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      exact ih (env := env) (slotLifetime := slotLifetime) (parent := parent)
        hwellFormed hsafe hchild hslotParent hinnerBorrows

/-- Stale-aware version of `borrowDependency_dropsAvoids_lifetime`. -/
theorem borrowDependencyWhenInitialized_dropsAvoids_lifetime
    {store store' : ProgramStore} {env : Env} {dropSet : List PartialValue}
    {parent child slotLifetime : Lifetime} {value : PartialValue}
    {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnvWhenInitialized env child →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ value, value ∈ dropSet ↔
      ∃ location storeSlot,
        store.slotAt location = some storeSlot ∧
          storeSlot.lifetime = child ∧
          value = PartialValue.value
            (Value.ref { location := location, owner := true })) →
    Drops store dropSet store' →
    LifetimeDropOwnersDisjoint store child →
    LifetimeChild parent child →
    slotLifetime ≤ parent →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy dependency →
    DropsAvoids store dropSet dependency := by
  intro hwellFormed hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint
    hchild hslotParent hborrows hdependency
  induction hdependency generalizing slotLifetime parent with
  | @borrow location readLocation mutable targets target hinitialized hmem hloc hreads =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨hbaseTarget, htargetWhenInitialized⟩
      rcases hinitialized target hmem with
        ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases htargetWhenInitialized
          ⟨targetTy, targetLifetime, htargetTyping⟩ with
        ⟨selectedTy, selectedLifetime, hselectedTyping, htargetOutlives,
          hbaseTargetAtSlot⟩
      have htargetParent : selectedLifetime ≤ parent :=
        LifetimeOutlives.trans htargetOutlives hslotParent
      have hbaseParent : LValBaseOutlives env target parent := by
        rcases hbaseTargetAtSlot with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        exact ⟨baseSlot, hbaseSlot,
          LifetimeOutlives.trans hbaseOutlives hslotParent⟩
      exact (lval_loc_or_reads_dropsAvoids_lifetime_whenInitialized
        hwellFormed hsafe hvalidStore hheap hdropSet hdrops hdropDisjoint
        hchild hbaseParent hselectedTyping htargetParent).2 hreads
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      exact ih (slotLifetime := slotLifetime) (parent := parent)
        hchild hslotParent hinnerBorrows
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      exact ih (slotLifetime := slotLifetime) (parent := parent)
        hchild hslotParent hinnerBorrows

/--
Borrow-resolution dependencies are always locations protected by some variable
base from the corresponding borrow target.  This formulation intentionally does
not name that base: recursive borrows can redirect resolution through another
target's base.
-/
theorem borrowDependency_protectedBySomeBase
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ∃ x, ProtectedByBase store x dependency := by
  intro hwellFormed hsafe hvalidStore hheap hborrows hdependency
  induction hdependency generalizing env slotLifetime current with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      exact
        (lval_loc_or_reads_protectedBySomeBase
          hwellFormed hsafe hvalidStore hheap htargetTyping).2 hreads
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      exact ih (env := env) (current := current)
        (slotLifetime := slotLifetime) hwellFormed hsafe hinnerBorrows
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      exact ih (env := env) (current := current)
        (slotLifetime := slotLifetime) hwellFormed hsafe hinnerBorrows

/-- Stale-aware version of `borrowDependency_protectedBySomeBase`. -/
theorem borrowDependencyWhenInitialized_protectedBySomeBase
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy dependency →
    ∃ x, ProtectedByBase store x dependency := by
  intro hwellFormed hsafe hvalidStore hheap hborrows hdependency
  induction hdependency generalizing slotLifetime current with
  | @borrow location readLocation mutable targets target hinitialized hmem hloc hreads =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨_hbaseTarget, htargetWhenInitialized⟩
      rcases hinitialized target hmem with
        ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases htargetWhenInitialized
          ⟨targetTy, targetLifetime, htargetTyping⟩ with
        ⟨selectedTy, selectedLifetime, hselectedTyping, _houtlives,
          _hbaseTargetAtSlot⟩
      exact
        (lval_loc_or_reads_protectedBySomeBase_whenInitialized
          hwellFormed hsafe hvalidStore hheap hselectedTyping).2 hreads
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      exact ih (current := current) (slotLifetime := slotLifetime)
        hwellFormed hinnerBorrows
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      exact ih (current := current) (slotLifetime := slotLifetime)
        hwellFormed hinnerBorrows

/-- General dependency-drop frame lemma: once every dropped owner is outside all
protected bases, every borrow-resolution dependency is avoided by the drop. -/
theorem dropsAvoids_of_borrowDependency_unprotected_values
    {store store' : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {values : List PartialValue} {value : PartialValue} {partialTy : PartialTy}
    {dependency : Location} :
    Drops store values store' →
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ dropValue, dropValue ∈ values → PartialValueOwnerTargetsHeap dropValue) →
    (∀ dropValue, dropValue ∈ values →
      ∀ owned, owned ∈ partialValueOwningLocations dropValue →
      ∀ base, ¬ ProtectedByBase store base owned) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    DropsAvoids store values dependency := by
  intro hdrops hwellFormed hsafe hvalidStore hheap hvaluesHeap hunprotected
    hborrows hdependency
  rcases borrowDependency_protectedBySomeBase
      hwellFormed hsafe hvalidStore hheap hborrows hdependency with
    ⟨base, hprotected⟩
  exact dropsAvoids_of_protectedByBase_unprotected_values
    hdrops hvalidStore hheap hvaluesHeap
    (by
      intro dropValue hmem owned howned
      exact hunprotected dropValue hmem owned howned base)
    hprotected

/-- Stale-aware version of `dropsAvoids_of_borrowDependency_unprotected_values`. -/
theorem dropsAvoids_of_borrowDependencyWhenInitialized_unprotected_values
    {store store' : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {values : List PartialValue} {value : PartialValue} {partialTy : PartialTy}
    {dependency : Location} :
    Drops store values store' →
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ dropValue, dropValue ∈ values → PartialValueOwnerTargetsHeap dropValue) →
    (∀ dropValue, dropValue ∈ values →
      ∀ owned, owned ∈ partialValueOwningLocations dropValue →
      ∀ base, ¬ ProtectedByBase store base owned) →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy dependency →
    DropsAvoids store values dependency := by
  intro hdrops hwellFormed hsafe hvalidStore hheap hvaluesHeap hunprotected
    hborrows hdependency
  rcases borrowDependencyWhenInitialized_protectedBySomeBase
      hwellFormed hsafe hvalidStore hheap hborrows hdependency with
    ⟨base, hprotected⟩
  exact dropsAvoids_of_protectedByBase_unprotected_values
    hdrops hvalidStore hheap hvaluesHeap
    (by
      intro dropValue hmem owned howned
      exact hunprotected dropValue hmem owned howned base)
    hprotected

/--
If every variable occurring in a partial type is protected from writes, then a
borrow-resolution dependency inside a value of that partial type is also
protected when the dependency is a variable location.
-/
theorem borrowDependency_var_writeProhibited_of_varsProtected
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnv env current →
    store ≈ₛ env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ y, y ∈ PartialTy.vars partialTy → WriteProhibited env (.var y)) →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ∀ x, dependency = VariableProjection x → WriteProhibited env (.var x) := by
  intro hwellFormed hsafe hheap hborrows hvars hdependency
  induction hdependency generalizing env slotLifetime current with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      intro x hdependencyEq
      subst hdependencyEq
      have htargetWell := hborrows PartialTyContains.here target hmem
      rcases htargetWell with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      rcases locReads_var_writeProhibited_or_base hwellFormed hsafe hheap
          htargetTyping hreads with hwp | hbase
      · exact hwp
      · have hxVars : x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
          have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
            List.mem_map_of_mem hmem
          simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
        exact hvars x hxVars
  | @boxInner location slot inner dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      have hinnerVars :
          ∀ y, y ∈ PartialTy.vars inner → WriteProhibited env (.var y) := by
        intro y hy
        exact hvars y (by simpa [PartialTy.vars] using hy)
      exact ih hwellFormed hsafe hinnerBorrows hinnerVars x hdependencyEq
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      have hinnerVars :
          ∀ y, y ∈ PartialTy.vars (.ty ty) → WriteProhibited env (.var y) := by
        intro y hy
        exact hvars y (by simpa [PartialTy.vars, Ty.vars] using hy)
      exact ih hwellFormed hsafe hinnerBorrows hinnerVars x hdependencyEq

/-- Premise-free (`∼ₛ`-only) form of `borrowDependency_var_writeProhibited_of_varsProtected`. -/
theorem borrowDependency_var_writeProhibited_of_varsProtected_of_safe
    {store : ProgramStore} {env : Env} {slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ y, y ∈ PartialTy.vars partialTy → WriteProhibited env (.var y)) →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ∀ x, dependency = VariableProjection x → WriteProhibited env (.var x) := by
  intro hsafe hheap hborrows hvars hdependency
  induction hdependency generalizing env slotLifetime with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      intro x hdependencyEq
      subst hdependencyEq
      have htargetWell := hborrows PartialTyContains.here target hmem
      rcases htargetWell with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      rcases locReads_var_writeProhibited_or_base_of_safe hsafe hheap
          htargetTyping hreads with hwp | hbase
      · exact hwp
      · have hxVars : x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
          have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
            List.mem_map_of_mem hmem
          simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
        exact hvars x hxVars
  | @boxInner location slot inner dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      have hinnerVars :
          ∀ y, y ∈ PartialTy.vars inner → WriteProhibited env (.var y) := by
        intro y hy
        exact hvars y (by simpa [PartialTy.vars] using hy)
      exact ih hsafe hinnerBorrows hinnerVars x hdependencyEq
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      have hinnerVars :
          ∀ y, y ∈ PartialTy.vars (.ty ty) → WriteProhibited env (.var y) := by
        intro y hy
        exact hvars y (by simpa [PartialTy.vars, Ty.vars] using hy)
      exact ih hsafe hinnerBorrows hinnerVars x hdependencyEq

theorem borrowDependency_var_writeProhibitedVia_or_mem_vars_of_safe
    {store : ProgramStore} {env : Env} {slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    store ∼ₛ env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ∀ x, dependency = VariableProjection x →
      (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
        x ∈ PartialTy.vars partialTy := by
  intro hsafe hheap hborrows hdependency
  induction hdependency generalizing env slotLifetime with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      intro x hdependencyEq
      subst hdependencyEq
      rcases hborrows PartialTyContains.here target hmem with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      rcases locReads_var_writeProhibitedVia_or_base_of_safe hsafe hheap
          htargetTyping hreads with hvia | hbase
      · exact Or.inl hvia
      · right
        have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
          List.mem_map_of_mem hmem
        simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
  | @boxInner location slot inner dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hsafe hinnerBorrows x hdependencyEq with hvia | hmem
      · exact Or.inl hvia
      · exact Or.inr (by simpa [PartialTy.vars] using hmem)
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hsafe hinnerBorrows x hdependencyEq with hvia | hmem
      · exact Or.inl hvia
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars] using hmem)

theorem borrowDependency_protected_writeProhibited_or_mem_vars
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {x : Name} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ProtectedByBase store x dependency →
      WriteProhibited env (.var x) ∨ x ∈ PartialTy.vars partialTy := by
  intro hwellFormed hsafe hvalidStore hheap hborrows hdependency
    hprotected
  induction hdependency generalizing env slotLifetime current with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      have htargetWell := hborrows PartialTyContains.here target hmem
      rcases htargetWell with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      rcases
          (lval_loc_or_reads_protected_writeProhibited_or_base
            hwellFormed hsafe hvalidStore hheap htargetTyping).2
            hreads hprotected with hwp | hbase
      · exact Or.inl hwp
      · right
        have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
          List.mem_map_of_mem hmem
        simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hwellFormed hsafe hinnerBorrows hprotected with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars] using hmem)
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hwellFormed hsafe hinnerBorrows hprotected with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars] using hmem)

theorem borrowDependencyWhenInitialized_protected_writeProhibited_or_mem_vars
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {x : Name} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy dependency →
    ProtectedByBase store x dependency →
      WriteProhibited env (.var x) ∨ x ∈ PartialTy.vars partialTy := by
  intro hwellFormed hsafe hvalidStore hheap hborrows hdependency
    hprotected
  induction hdependency generalizing slotLifetime current with
  | @borrow location readLocation mutable targets target hinitialized hmem hloc hreads =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨_hbaseTarget, htargetWhenInitialized⟩
      rcases hinitialized target hmem with
        ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases htargetWhenInitialized
          ⟨targetTy, targetLifetime, htargetTyping⟩ with
        ⟨selectedTy, selectedLifetime, hselectedTyping, _houtlives,
          _hbaseTargetAtSlot⟩
      rcases
          (lval_loc_or_reads_protected_writeProhibited_or_base_whenInitialized
            hwellFormed hsafe hvalidStore hheap hselectedTyping).2
            hreads hprotected with hwp | hbase
      · exact Or.inl hwp
      · right
        have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
          List.mem_map_of_mem hmem
        simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hwellFormed hinnerBorrows hprotected with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars] using hmem)
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hwellFormed hinnerBorrows hprotected with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars] using hmem)

theorem borrowDependencyWhenInitialized_protected_writeProhibitedVia_or_mem_vars
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {x : Name} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy dependency →
    ProtectedByBase store x dependency →
      (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
        x ∈ PartialTy.vars partialTy := by
  intro hwellFormed hsafe hvalidStore hheap hborrows hdependency
    hprotected
  induction hdependency generalizing slotLifetime current with
  | @borrow location readLocation mutable targets target hinitialized hmem hloc hreads =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨_hbaseTarget, htargetWhenInitialized⟩
      rcases hinitialized target hmem with
        ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases htargetWhenInitialized
          ⟨targetTy, targetLifetime, htargetTyping⟩ with
        ⟨selectedTy, selectedLifetime, hselectedTyping, _houtlives,
          _hbaseTargetAtSlot⟩
      rcases
          (lval_loc_or_reads_protected_writeProhibitedVia_or_base_whenInitialized
            hwellFormed hsafe hvalidStore hheap hselectedTyping).2
            hreads hprotected with hvia | hbase
      · exact Or.inl hvia
      · right
        have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
          List.mem_map_of_mem hmem
        simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hwellFormed hinnerBorrows hprotected with hvia | hmem
      · exact Or.inl hvia
      · exact Or.inr (by simpa [PartialTy.vars] using hmem)
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hwellFormed hinnerBorrows hprotected with hvia | hmem
      · exact Or.inl hvia
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars] using hmem)

theorem borrowDependency_not_protectedByBase_of_varsProtectedIn
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {x : Name} :
    WellFormedEnv sourceEnv current →
    store ≈ₛ sourceEnv →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot sourceEnv slotLifetime partialTy →
    (∀ y, y ∈ PartialTy.vars partialTy →
      WriteProhibited observerEnv (.var y)) →
    ¬ WriteProhibited sourceEnv (.var x) →
    ¬ WriteProhibited observerEnv (.var x) →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ¬ ProtectedByBase store x dependency := by
  intro hwellFormed hsafe hvalidStore hheap hborrows hvarsObserver
    hnotWriteSource hnotWriteObserver hdependency hprotected
  rcases borrowDependency_protected_writeProhibited_or_mem_vars
      hwellFormed hsafe hvalidStore hheap hborrows hdependency hprotected with
    hwpSource | hmemVars
  · exact hnotWriteSource hwpSource
  · exact hnotWriteObserver (hvarsObserver x hmemVars)

theorem borrowDependency_var_writeProhibited_or_mem_vars
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnv env current →
    store ≈ₛ env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ∀ x, dependency = VariableProjection x →
      WriteProhibited env (.var x) ∨ x ∈ PartialTy.vars partialTy := by
  intro hwellFormed hsafe hheap hborrows hdependency
  induction hdependency generalizing env slotLifetime current with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      intro x hdependencyEq
      subst hdependencyEq
      have htargetWell := hborrows PartialTyContains.here target hmem
      rcases htargetWell with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      rcases locReads_var_writeProhibited_or_base hwellFormed hsafe hheap
          htargetTyping hreads with hwp | hbase
      · exact Or.inl hwp
      · right
        have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
          List.mem_map_of_mem hmem
        simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
  | @boxInner location slot inner dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hwellFormed hsafe hinnerBorrows x hdependencyEq with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars] using hmem)
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hwellFormed hsafe hinnerBorrows x hdependencyEq with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars] using hmem)

/--
Borrow dependencies inside the value being moved cannot read a location protected
by the moved lvalue's base.  Otherwise the dependency either directly
write-prohibits the moved base, or it comes from a borrow target whose base
conflicts with the moved lvalue; both contradict the `T-Move` no-write premise.
-/
theorem borrowDependency_not_protectedByMovedBase {store : ProgramStore}
    {env : Env} {current valueLifetime : Lifetime} {lv : LVal}
    {value : Value} {ty : Ty} {dependency : Location} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    RuntimeFrame.BorrowDependency store (.value value) (.ty ty) dependency →
    ¬ ProtectedByBase store (LVal.base lv) dependency := by
  intro hwellFormed hsafe hvalidStore hheap hLv hnotWrite hdependency hprotected
  have hborrows :
      PartialTyBorrowsWellFormedInSlot env current (.ty ty) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy
      (LValTyping.fullTyWellFormed hwellFormed hLv)
  rcases borrowDependency_protected_writeProhibited_or_mem_vars
      hwellFormed hsafe hvalidStore hheap hborrows hdependency
      hprotected with hwp | hmemVars
  · exact (not_writeProhibited_var_base hnotWrite) hwp
  · rcases mem_partialTy_vars_iff.mp hmemVars with
      ⟨mutable, targets, target, hcontains, htarget, hbase⟩
    have hnotConflict :
        ¬ target ⋈ lv :=
      (LValTyping.no_writeProhibited_targets hnotWrite).1
        hLv hcontains target htarget
    exact hnotConflict (by
      simpa [PathConflicts] using hbase)

theorem borrowDependencyWhenInitialized_not_protectedByMovedBase
    {store : ProgramStore} {env : Env} {current valueLifetime : Lifetime}
    {lv : LVal} {value : Value} {ty : Ty} {dependency : Location} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    RuntimeFrame.BorrowDependencyWhenInitialized env store (.value value) (.ty ty)
      dependency →
    ¬ ProtectedByBase store (LVal.base lv) dependency := by
  intro hwellFormed hsafe hvalidStore hheap hLv hnotWrite hdependency hprotected
  have hborrows :
      PartialTyBorrowsWellFormedInSlotWhenInitialized env current (.ty ty) :=
    PartialTyBorrowsWellFormedInSlotWhenInitialized.of_wellFormedTy
      (LValTyping.fullTyWellFormedWhenInitialized hwellFormed hLv)
  rcases borrowDependencyWhenInitialized_protected_writeProhibited_or_mem_vars
      hwellFormed hsafe hvalidStore hheap hborrows hdependency hprotected with
    hwp | hmemVars
  · exact (not_writeProhibited_var_base hnotWrite) hwp
  · rcases mem_partialTy_vars_iff.mp hmemVars with
      ⟨mutable, targets, target, hcontains, htarget, hbase⟩
    have hnotConflict :
        ¬ target ⋈ lv :=
      (LValTyping.no_writeProhibited_targets hnotWrite).1
        hLv hcontains target htarget
    exact hnotConflict (by
      simpa [PathConflicts] using hbase)

/-- Updating the moved leaf cannot invalidate the value just read from that leaf:
owner reachability would create an ownership cycle, and borrow dependencies are
ruled out by the `T-Move` no-write premise. -/
theorem movedValue_reaches_ne_protected_leaf {store : ProgramStore}
    {env : Env} {current valueLifetime leafLifetime : Lifetime}
    {lv : LVal} {leaf reached : Location} {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    store.slotAt leaf = some { value := .value value, lifetime := leafLifetime } →
    ProtectedByBase store (LVal.base lv) leaf →
    ValidValue store value ty →
    RuntimeFrame.Reaches store (.value value) (.ty ty) reached →
    reached ≠ leaf := by
  intro hwellFormed hsafe hvalidStore hheap hLv hnotWrite hleafSlot
    hleafProtected hvalidValue hreach hreached
  subst reached
  rcases RuntimeFrame.Reaches.owner_or_borrow hreach with howner | hdependency
  · have hcycle :
        ProgramStore.OwnsTransitively store leaf leaf :=
      RuntimeFrame.ownsTransitively_of_ownerReaches_stored
        hleafSlot howner
    exact ValidPartialValue.no_storage_ownership_cycle hleafSlot
      hvalidValue hcycle
  · exact (borrowDependency_not_protectedByMovedBase
      hwellFormed hsafe hvalidStore hheap hLv hnotWrite hdependency)
      hleafProtected

theorem movedValue_reaches_ne_protected_leaf_whenInitialized
    {store : ProgramStore} {env : Env} {current valueLifetime leafLifetime : Lifetime}
    {lv : LVal} {leaf reached : Location} {value : Value} {ty : Ty} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    store.slotAt leaf = some { value := .value value, lifetime := leafLifetime } →
    ProtectedByBase store (LVal.base lv) leaf →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    RuntimeFrame.ReachesWhenInitialized env store (.value value) (.ty ty) reached →
    reached ≠ leaf := by
  intro hwellFormed hsafe hvalidStore hheap hLv hnotWrite hleafSlot
    hleafProtected hvalidValue hreach hreached
  subst reached
  rcases RuntimeFrame.ReachesWhenInitialized.owner_or_borrow hreach with
    howner | hdependency
  · have hcycle :
        ProgramStore.OwnsTransitively store leaf leaf :=
      RuntimeFrame.ownsTransitively_of_ownerReaches_stored
        hleafSlot howner
    exact ValidPartialValueWhenInitialized.no_storage_ownership_cycle
      hleafSlot hvalidValue hcycle
  · exact (borrowDependencyWhenInitialized_not_protectedByMovedBase
      hwellFormed hsafe hvalidStore hheap hLv hnotWrite hdependency)
      hleafProtected

inductive RuntimeFrame.ReachesSlot (store : ProgramStore) :
    PartialValue → PartialTy → Location → StoreSlot → PartialTy → Prop where
  | boxHere {location : Location} {slot : StoreSlot} {inner : PartialTy} :
      store.slotAt location = some slot →
      ValidPartialValue store slot.value inner →
      RuntimeFrame.ReachesSlot store
        (.value (.ref { location := location, owner := true })) (.box inner)
        location slot inner
  | boxInner {location reached : Location} {slot reachedSlot : StoreSlot}
      {inner reachedTy : PartialTy} :
      store.slotAt location = some slot →
      RuntimeFrame.ReachesSlot store slot.value inner reached reachedSlot
        reachedTy →
      RuntimeFrame.ReachesSlot store
        (.value (.ref { location := location, owner := true })) (.box inner)
        reached reachedSlot reachedTy
  | boxFullHere {location : Location} {slot : StoreSlot} {ty : Ty} :
      store.slotAt location = some slot →
      ValidPartialValue store slot.value (.ty ty) →
      RuntimeFrame.ReachesSlot store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) location slot (.ty ty)
  | boxFullInner {location reached : Location} {slot reachedSlot : StoreSlot}
      {ty : Ty} {reachedTy : PartialTy} :
      store.slotAt location = some slot →
      RuntimeFrame.ReachesSlot store slot.value (.ty ty) reached reachedSlot
        reachedTy →
      RuntimeFrame.ReachesSlot store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) reached reachedSlot reachedTy

theorem RuntimeFrame.ReachesSlot.reaches {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location}
    {slot : StoreSlot} {slotTy : PartialTy} :
    RuntimeFrame.ReachesSlot store value ty location slot slotTy →
    RuntimeFrame.Reaches store value ty location := by
  intro hreach
  induction hreach with
  | boxHere hslot _hvalid =>
      exact RuntimeFrame.Reaches.boxHere hslot
  | boxInner hslot _hinner ih =>
      exact RuntimeFrame.Reaches.boxInner hslot ih
  | boxFullHere hslot _hvalid =>
      exact RuntimeFrame.Reaches.boxFullHere hslot
  | boxFullInner hslot _hinner ih =>
      exact RuntimeFrame.Reaches.boxFullInner hslot ih

theorem RuntimeFrame.ReachesSlot.valid {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location}
    {slot : StoreSlot} {slotTy : PartialTy} :
    RuntimeFrame.ReachesSlot store value ty location slot slotTy →
    ValidPartialValue store slot.value slotTy := by
  intro hreach
  induction hreach with
  | boxHere _hslot hvalid =>
      exact hvalid
  | boxInner _hslot _hinner ih =>
      exact ih
  | boxFullHere _hslot hvalid =>
      exact hvalid
  | boxFullInner _hslot _hinner ih =>
      exact ih

theorem RuntimeFrame.ReachesSlot.evidenceSelectedBorrow_lift
    {store : ProgramStore} :
    ∀ {value : PartialValue} {ty : PartialTy} {location : Location}
      {slot : StoreSlot} {slotTy : PartialTy},
      RuntimeFrame.ReachesSlot store value ty location slot slotTy →
      ∀ {mutable : Bool} {targets : List LVal} {target : LVal},
        (slotEvidence :
          RuntimeFrame.ValidPartialValueEvidence store slot.value slotTy) →
        RuntimeFrame.EvidenceSelectedBorrow store slotEvidence mutable targets
          target →
        ∃ rootEvidence :
          RuntimeFrame.ValidPartialValueEvidence store value ty,
          RuntimeFrame.EvidenceSelectedBorrow store rootEvidence mutable
            targets target := by
  intro value ty location slot slotTy hreach
  induction hreach with
  | boxHere hslot _hvalid =>
      intro mutable targets target slotEvidence hselected
      exact ⟨RuntimeFrame.ValidPartialValueEvidence.box hslot slotEvidence,
        RuntimeFrame.EvidenceSelectedBorrow.boxInner hselected⟩
  | boxInner hslot _hinner ih =>
      intro mutable targets target slotEvidence hselected
      rcases ih slotEvidence hselected with ⟨innerEvidence, hinnerSelected⟩
      exact ⟨RuntimeFrame.ValidPartialValueEvidence.box hslot innerEvidence,
        RuntimeFrame.EvidenceSelectedBorrow.boxInner hinnerSelected⟩
  | boxFullHere hslot _hvalid =>
      intro mutable targets target slotEvidence hselected
      exact ⟨RuntimeFrame.ValidPartialValueEvidence.boxFull hslot slotEvidence,
        RuntimeFrame.EvidenceSelectedBorrow.boxFullInner hselected⟩
  | boxFullInner hslot _hinner ih =>
      intro mutable targets target slotEvidence hselected
      rcases ih slotEvidence hselected with ⟨innerEvidence, hinnerSelected⟩
      exact ⟨RuntimeFrame.ValidPartialValueEvidence.boxFull hslot innerEvidence,
        RuntimeFrame.EvidenceSelectedBorrow.boxFullInner hinnerSelected⟩

theorem RuntimeFrame.ReachesSlot.evidence_at {store : ProgramStore} :
    ∀ {value : PartialValue} {ty : PartialTy} {location : Location}
      {slot : StoreSlot} {slotTy : PartialTy},
      RuntimeFrame.ReachesSlot store value ty location slot slotTy →
      (rootEvidence : RuntimeFrame.ValidPartialValueEvidence store value ty) →
      ∃ slotEvidence :
        RuntimeFrame.ValidPartialValueEvidence store slot.value slotTy,
        ∀ {mutable : Bool} {targets : List LVal} {target : LVal},
          RuntimeFrame.EvidenceSelectedBorrow store slotEvidence mutable
            targets target →
          RuntimeFrame.EvidenceSelectedBorrow store
            rootEvidence mutable targets target := by
  intro value ty location slot slotTy hreach rootEvidence
  induction hreach with
  | boxHere hslot _hvalid =>
      cases rootEvidence with
      | @box _ slot' _ hslot' hinner =>
          have hslotEq := Option.some.inj (hslot'.symm.trans hslot)
          subst hslotEq
          exact ⟨hinner, by
            intro mutable targets target hselected
            exact RuntimeFrame.EvidenceSelectedBorrow.boxInner hselected⟩
  | boxInner hslot _hinner ih =>
      cases rootEvidence with
      | @box _ slot' _ hslot' rootInner =>
          have hslotEq := Option.some.inj (hslot'.symm.trans hslot)
          subst hslotEq
          rcases ih rootInner with ⟨slotEvidence, hlift⟩
          exact ⟨slotEvidence, by
            intro mutable targets target hselected
            exact RuntimeFrame.EvidenceSelectedBorrow.boxInner
              (hlift hselected)⟩
  | boxFullHere hslot _hvalid =>
      cases rootEvidence with
      | @boxFull _ slot' _ hslot' hinner =>
          have hslotEq := Option.some.inj (hslot'.symm.trans hslot)
          subst hslotEq
          exact ⟨hinner, by
            intro mutable targets target hselected
            exact RuntimeFrame.EvidenceSelectedBorrow.boxFullInner
              hselected⟩
  | boxFullInner hslot _hinner ih =>
      cases rootEvidence with
      | @boxFull _ slot' _ hslot' rootInner =>
          have hslotEq := Option.some.inj (hslot'.symm.trans hslot)
          subst hslotEq
          rcases ih rootInner with ⟨slotEvidence, hlift⟩
          exact ⟨slotEvidence, by
            intro mutable targets target hselected
            exact RuntimeFrame.EvidenceSelectedBorrow.boxFullInner
              (hlift hselected)⟩

theorem ValidPartialValueSkeleton.ownerDerefOfUndefAux
    {store : ProgramStore} {value : PartialValue} {owned : Location}
    {oldTy : PartialTy} {outerTy : Ty} :
    value = (.value (.ref { location := owned, owner := true })) →
    ValidPartialValueSkeleton store value oldTy →
    PartialTyStrengthens oldTy (.undef outerTy) →
    ∃ innerTy ownedSlot,
      outerTy = .box innerTy ∧
      store.slotAt owned = some ownedSlot ∧
      ValidPartialValue store ownedSlot.value (.undef innerTy) := by
  intro hvalue hskel
  induction hskel generalizing owned outerTy with
  | unit | int | undef | borrow =>
      cases hvalue
  | @box location slot inner hslot hinner =>
      cases hvalue
      intro hstrength
      cases hstrength with
      | boxIntoUndef hinnerStrength =>
          exact ⟨_, slot, rfl, hslot,
            ValidPartialValue.undefOf hinner hinnerStrength⟩
  | @boxFull location slot ty hslot hinner =>
      cases hvalue
      intro hstrength
      cases hstrength with
      | intoUndef htyStrength =>
          cases htyStrength with
          | reflex =>
              exact ⟨ty, slot, rfl, hslot,
                ValidPartialValue.undefOf hinner
                  (PartialTyStrengthens.intoUndef
                    PartialTyStrengthens.reflex)⟩
          | tyBox hinnerStrength =>
              exact ⟨_, slot, rfl, hslot,
                ValidPartialValue.undefOf hinner
                  (PartialTyStrengthens.intoUndef hinnerStrength)⟩
  | undefOf hinner hinnerStrength ih =>
      intro hstrength
      exact ih hvalue (partialTyStrengthens_trans_safe hinnerStrength hstrength)

theorem ValidPartialValueSkeleton.ownerDerefOfUndef
    {store : ProgramStore} {owned : Location} {oldTy : PartialTy}
    {outerTy : Ty} :
    ValidPartialValueSkeleton store
      (.value (.ref { location := owned, owner := true })) oldTy →
    PartialTyStrengthens oldTy (.undef outerTy) →
    ∃ innerTy ownedSlot,
      outerTy = .box innerTy ∧
      store.slotAt owned = some ownedSlot ∧
      ValidPartialValue store ownedSlot.value (.undef innerTy) := by
  intro hskel hstrength
  exact ValidPartialValueSkeleton.ownerDerefOfUndefAux rfl hskel hstrength

/-- Owner reachability through heap-only owner targets never reaches a variable slot. -/
theorem RuntimeFrame.ownerReaches_ne_var_of_heap
    {store : ProgramStore}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    RuntimeFrame.OwnerReaches store partialValue partialTy location →
    location ≠ VariableProjection x := by
  intro hstoreHeap hvalueHeap hreach
  induction hreach with
  | undefOf _hskel _hstrength _hinner ih =>
      exact ih hvalueHeap
  | @boxHere owned slot inner hslot =>
      have hmem :
          owned ∈ partialValueOwningLocations
            (.value (.ref { location := owned, owner := true })) := by
        simpa using
          (mem_partialValueOwningLocations_ref_true
            (ref := { location := owned, owner := true }) rfl)
      have hheap : ∃ address, owned = .heap address :=
        hvalueHeap owned hmem
      rcases hheap with ⟨address, hlocation⟩
      subst hlocation
      simp [VariableProjection]
  | boxInner hslot _hinner ih =>
      exact ih
        (partialValueOwnerTargetsHeap_of_slot hstoreHeap hslot)
  | @boxFullHere owned slot ty hslot =>
      have hmem :
          owned ∈ partialValueOwningLocations
            (.value (.ref { location := owned, owner := true })) := by
        simpa using
          (mem_partialValueOwningLocations_ref_true
            (ref := { location := owned, owner := true }) rfl)
      have hheap : ∃ address, owned = .heap address :=
        hvalueHeap owned hmem
      rcases hheap with ⟨address, hlocation⟩
      subst hlocation
      simp [VariableProjection]
  | boxFullInner hslot _hinner ih =>
      exact ih
        (partialValueOwnerTargetsHeap_of_slot hstoreHeap hslot)

theorem RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
    {store : ProgramStore} {env : Env} {slotLifetime : Lifetime}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.OwnerReaches store partialValue partialTy location →
    location ≠ VariableProjection x := by
  intro hstoreHeap hvalueHeap _hborrows hreach
  exact RuntimeFrame.ownerReaches_ne_var_of_heap hstoreHeap hvalueHeap hreach

/-- Full-value specialization of `reaches_ne_var_of_wellFormed_borrows`. -/
theorem RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
    {store : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {location : Location} {x : Name} :
    StoreOwnerTargetsHeap store →
    ValueOwnerTargetsHeap value →
    WellFormedTy env ty lifetime →
    RuntimeFrame.OwnerReaches store (.value value) (.ty ty) location →
    location ≠ VariableProjection x := by
  intro hstoreHeap hvalueHeap hwellTy hreach
  exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows hstoreHeap
    (ValueOwnerTargetsHeap.partial hvalueHeap)
    (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)
    hreach

theorem RuntimeFrame.reaches_ne_var_of_varsProtected {store : ProgramStore}
    {env : Env} {current slotLifetime : Lifetime}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    WellFormedEnv env current →
    store ≈ₛ env →
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ y, y ∈ PartialTy.vars partialTy → WriteProhibited env (.var y)) →
    ¬ WriteProhibited env (.var x) →
    RuntimeFrame.Reaches store partialValue partialTy location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hborrows hvars hnotWrite hreach hlocEq
  rcases RuntimeFrame.Reaches.owner_or_borrow hreach with howner | hdependency
  · exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows (x := x) hheap
      hvalueHeap hborrows howner hlocEq
  · have hwp :=
      borrowDependency_var_writeProhibited_of_varsProtected
        (dependency := location)
        hwellFormed hsafe hheap hborrows hvars hdependency x hlocEq
    exact hnotWrite hwp

theorem RuntimeFrame.reaches_ne_var_of_varsProtectedIn {store : ProgramStore}
    {sourceEnv observerEnv : Env} {current slotLifetime : Lifetime}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    WellFormedEnv sourceEnv current →
    store ≈ₛ sourceEnv →
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    PartialTyBorrowsWellFormedInSlot sourceEnv slotLifetime partialTy →
    (∀ y, y ∈ PartialTy.vars partialTy →
      WriteProhibited observerEnv (.var y)) →
    (∀ y, y ≠ x → ¬ WriteProhibitedVia sourceEnv y (.var x)) →
    ¬ WriteProhibited observerEnv (.var x) →
    RuntimeFrame.Reaches store partialValue partialTy location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hborrows hvarsObserver
    hnoOther hnotWriteObserver hreach hlocEq
  rcases RuntimeFrame.Reaches.owner_or_borrow hreach with howner | hdependency
  · exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows (x := x) hheap
      hvalueHeap hborrows howner hlocEq
  · rcases borrowDependency_var_writeProhibitedVia_or_mem_vars_of_safe
        (dependency := location)
        (FullSafeAbstraction.whenInitialized hsafe) hheap hborrows hdependency
        x hlocEq with
      hvia | hmemVars
    · rcases hvia with ⟨y, hy, hvia⟩
      exact hnoOther y hy hvia
    · exact hnotWriteObserver (hvarsObserver x hmemVars)

/-- Full-value specialization of `RuntimeFrame.reaches_ne_var_of_varsProtected`. -/
theorem RuntimeFrame.value_reaches_ne_var_of_varsProtected
    {store : ProgramStore} {env : Env} {current lifetime : Lifetime}
    {value : Value} {ty : Ty} {location : Location} {x : Name} :
    WellFormedEnv env current →
    store ≈ₛ env →
    StoreOwnerTargetsHeap store →
    ValueOwnerTargetsHeap value →
    WellFormedTy env ty lifetime →
    (∀ y, y ∈ Ty.vars ty → WriteProhibited env (.var y)) →
    ¬ WriteProhibited env (.var x) →
    RuntimeFrame.Reaches store (.value value) (.ty ty) location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hwellTy hvars hnotWrite hreach
  exact RuntimeFrame.reaches_ne_var_of_varsProtected hwellFormed hsafe hheap
    (ValueOwnerTargetsHeap.partial hvalueHeap)
    (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)
    (by
      intro y hy
      exact hvars y (by simpa [PartialTy.vars] using hy))
    hnotWrite hreach

/-- Weak-runtime version of `lval_loc_var_writeProhibited_or_base`.
Stale borrow annotations cannot justify the dereference case because the target
typing premise makes the target list initialized. -/
theorem lval_loc_var_writeProhibited_or_base_whenInitialized
    {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} {x : Name} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    store.loc lv = some (VariableProjection x) →
    WriteProhibited env (.var x) ∨ LVal.base lv = x := by
  intro hwellFormed hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _partialTy _lifetime _ =>
      store.loc lv = some (VariableProjection x) →
      WriteProhibited env (.var x) ∨ LVal.base lv = x)
    (motive_2 := fun targets _partialTy _lifetime _ =>
      ∀ target, target ∈ targets →
        store.loc target = some (VariableProjection x) →
        WriteProhibited env (.var x) ∨ LVal.base target = x)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  case var =>
    intro y _slot _hslot hloc
    right
    simp [ProgramStore.loc, VariableProjection] at hloc
    exact hloc
  case box =>
    intro source inner _sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source (.box inner) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @box ownerLocation _ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          refine ⟨sourceLocation, sourceSlotLifetime, ?_⟩
          simpa [owningRef] using hsourceSlot
        rcases hheap (VariableProjection x) howns with ⟨address, hheapLoc⟩
        cases hheapLoc
  case boxFull =>
    intro source inner _sourceLifetime hsource _ih hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.box inner)) :=
      lvalTyping_defined_location_whenInitialized hsafe hsource
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, sourceSlotLifetime⟩
    cases hsourceValid with
    | @boxFull ownerLocation _ownerSlot _ hownerSlot _hinnerValid =>
        have hderefLoc : store.loc source.deref = some ownerLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hownerEq : ownerLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hownerEq
        have howns : ProgramStore.Owns store (VariableProjection x) := by
          refine ⟨sourceLocation, sourceSlotLifetime, ?_⟩
          simpa [owningRef] using hsourceSlot
        rcases hheap (VariableProjection x) howns with ⟨address, hheapLoc⟩
        cases hheapLoc
  case borrow =>
    intro source mutable targets _borrowLifetime _targetLifetime _targetTy
      hborrow htargets _ihBorrow ihTargets hloc
    have hsourceAbs :
        LValLocationAbstractionWhenInitialized env store source
          (.ty (.borrow mutable targets)) :=
      lvalTyping_defined_location_whenInitialized hsafe hborrow
    rcases hsourceAbs with
      ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot, hsourceValid⟩
    rcases sourceSlot with ⟨_sourceValue, _sourceSlotLifetime⟩
    cases hsourceValid with
    | @borrowLive borrowedLocation _mutable _targets selected _hinitialized
        hmem hselectedLoc =>
        have hderefLoc : store.loc source.deref = some borrowedLocation := by
          simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
        have hborrowedEq : borrowedLocation = VariableProjection x := by
          rw [hloc] at hderefLoc
          exact Option.some.inj hderefLoc.symm
        subst hborrowedEq
        rcases ihTargets selected hmem hselectedLoc with hwp | hbase
        · exact Or.inl hwp
        · have hxVars :
              x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
            have hbaseMem : LVal.base selected ∈ targets.map LVal.base :=
              List.mem_map_of_mem hmem
            simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
          exact Or.inl
            (writeProhibited_of_lvalTyping_var_in_type_core hborrow hxVars)
    | @borrowStale _location _mutable _targets hstale =>
        have hinitialized : BorrowTargetsInitialized env targets := by
          intro target hmem
          rcases lvalTargetsTyping_member_strengthens htargets target hmem with
            ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
          exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
        exact False.elim (hstale hinitialized)
  case singleton =>
    intro target _ty _targetLifetime _htarget ih target' hmem hloc
    simp at hmem
    subst hmem
    exact ih hloc
  case cons =>
    intro target _rest _headTy _headLifetime _restLifetime _targetLifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection ihHead ihRest
      selected hmem hloc
    simp at hmem
    rcases hmem with hselected | hselected
    · subst hselected
      exact ihHead hloc
    · exact ihRest selected hselected hloc

/-- Weak-runtime version of `locReads_var_writeProhibited_or_base`. -/
theorem locReads_var_writeProhibited_or_base_whenInitialized
    {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} {x : Name} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    LValTyping env lv partialTy lifetime →
    RuntimeFrame.LocReads store lv (VariableProjection x) →
    WriteProhibited env (.var x) ∨ LVal.base lv = x := by
  intro hwellFormed hsafe hheap htyping
  refine LValTyping.rec
    (motive_1 := fun lv _partialTy _lifetime _ =>
      RuntimeFrame.LocReads store lv (VariableProjection x) →
      WriteProhibited env (.var x) ∨ LVal.base lv = x)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping
  case var =>
    intro _y _slot _hslot hreads
    cases hreads
  case box =>
    intro source _inner _sourceLifetime hsource ih hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibited_or_base_whenInitialized
            hwellFormed hsafe hheap hsource hloc with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ih hinnerReads with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
  case boxFull =>
    intro source _inner _sourceLifetime hsource ih hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibited_or_base_whenInitialized
            hwellFormed hsafe hheap hsource hloc with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ih hinnerReads with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
  case borrow =>
    intro source _mutable _targets _borrowLifetime _targetLifetime _targetTy
      hborrow _htargets ihBorrow _ihTargets hreads
    cases hreads with
    | here hloc =>
        rcases lval_loc_var_writeProhibited_or_base_whenInitialized
            hwellFormed hsafe hheap hborrow hloc with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
    | there hinnerReads =>
        rcases ihBorrow hinnerReads with hwp | hbase
        · exact Or.inl hwp
        · exact Or.inr (by simpa [LVal.base] using hbase)
  case singleton =>
    intros
    trivial
  case cons =>
    intros
    trivial

theorem borrowDependency_var_writeProhibited_or_mem_vars_whenInitialized
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnv env current →
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ∀ x, dependency = VariableProjection x →
      WriteProhibited env (.var x) ∨ x ∈ PartialTy.vars partialTy := by
  intro hwellFormed hsafe hheap hborrows hdependency
  induction hdependency generalizing env slotLifetime current with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      intro x hdependencyEq
      subst hdependencyEq
      have htargetWell := hborrows PartialTyContains.here target hmem
      rcases htargetWell with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      rcases locReads_var_writeProhibited_or_base_whenInitialized
          (WellFormedEnv.whenInitialized hwellFormed) hsafe hheap
          htargetTyping hreads with hwp | hbase
      · exact Or.inl hwp
      · right
        have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
          List.mem_map_of_mem hmem
        simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
  | @boxInner location slot inner dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hwellFormed hsafe hinnerBorrows x hdependencyEq with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars] using hmem)
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hwellFormed hsafe hinnerBorrows x hdependencyEq with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars] using hmem)

theorem borrowDependencyWhenInitialized_var_writeProhibited_or_mem_vars
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy dependency →
    ∀ x, dependency = VariableProjection x →
      WriteProhibited env (.var x) ∨ x ∈ PartialTy.vars partialTy := by
  intro hwellFormed hsafe hheap hborrows hdependency
  induction hdependency generalizing slotLifetime current with
  | @borrow location readLocation mutable targets target hinitialized hmem hloc hreads =>
      intro x hdependencyEq
      subst hdependencyEq
      rcases hinitialized target hmem with
        ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases locReads_var_writeProhibited_or_base_whenInitialized
          hwellFormed hsafe hheap htargetTyping hreads with hwp | hbase
      · exact Or.inl hwp
      · right
        have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
          List.mem_map_of_mem hmem
        simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
  | @boxInner location slot inner dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hwellFormed hinnerBorrows x hdependencyEq with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars] using hmem)
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime
            (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hwellFormed hinnerBorrows x hdependencyEq with hwp | hmem
      · exact Or.inl hwp
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars] using hmem)

theorem borrowDependencyWhenInitialized_var_writeProhibitedVia_or_mem_vars
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime partialTy →
    RuntimeFrame.BorrowDependencyWhenInitialized env store value partialTy dependency →
    ∀ x, dependency = VariableProjection x →
      (∃ y, y ≠ x ∧ WriteProhibitedVia env y (.var x)) ∨
        x ∈ PartialTy.vars partialTy := by
  intro hwellFormed hsafe hheap hborrows hdependency
  induction hdependency generalizing slotLifetime current with
  | @borrow location readLocation mutable targets target hinitialized hmem hloc hreads =>
      intro x hdependencyEq
      subst hdependencyEq
      rcases hinitialized target hmem with
        ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases locReads_var_writeProhibitedVia_or_base_of_safe hsafe hheap
          htargetTyping hreads with hvia | hbase
      · exact Or.inl hvia
      · right
        have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
          List.mem_map_of_mem hmem
        simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
  | @boxInner location slot inner dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime inner := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.box hcontains)
      rcases ih hwellFormed hinnerBorrows x hdependencyEq with hvia | hmem
      · exact Or.inl hvia
      · exact Or.inr (by simpa [PartialTy.vars] using hmem)
  | @boxFullInner location slot ty dependency hslot hinner ih =>
      intro x hdependencyEq
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlotWhenInitialized env slotLifetime
            (.ty ty) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      rcases ih hwellFormed hinnerBorrows x hdependencyEq with hvia | hmem
      · exact Or.inl hvia
      · exact Or.inr (by simpa [PartialTy.vars, Ty.vars] using hmem)

theorem RuntimeFrame.reaches_ne_var_of_varsProtected_whenInitialized
    {store : ProgramStore}
    {env : Env} {current slotLifetime : Lifetime}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    WellFormedEnv env current →
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ y, y ∈ PartialTy.vars partialTy → WriteProhibited env (.var y)) →
    ¬ WriteProhibited env (.var x) →
    RuntimeFrame.Reaches store partialValue partialTy location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hborrows hvars hnotWrite hreach hlocEq
  rcases RuntimeFrame.Reaches.owner_or_borrow hreach with howner | hdependency
  · exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows (x := x) hheap
      hvalueHeap hborrows howner hlocEq
  · have hwp :=
      borrowDependency_var_writeProhibited_or_mem_vars_whenInitialized
        (dependency := location)
        hwellFormed hsafe hheap hborrows hdependency x hlocEq
    rcases hwp with hwp | hmem
    · exact hnotWrite hwp
    · exact hnotWrite (hvars x hmem)

/-- Full-value specialization of
`RuntimeFrame.reaches_ne_var_of_varsProtected_whenInitialized`. -/
theorem RuntimeFrame.value_reaches_ne_var_of_varsProtected_whenInitialized
    {store : ProgramStore} {env : Env} {current lifetime : Lifetime}
    {value : Value} {ty : Ty} {location : Location} {x : Name} :
    WellFormedEnv env current →
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    ValueOwnerTargetsHeap value →
    WellFormedTy env ty lifetime →
    (∀ y, y ∈ Ty.vars ty → WriteProhibited env (.var y)) →
    ¬ WriteProhibited env (.var x) →
    RuntimeFrame.Reaches store (.value value) (.ty ty) location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hwellTy hvars hnotWrite hreach
  exact RuntimeFrame.reaches_ne_var_of_varsProtected_whenInitialized
    hwellFormed hsafe hheap
    (ValueOwnerTargetsHeap.partial hvalueHeap)
    (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)
    (by
      intro y hy
      exact hvars y (by simpa [PartialTy.vars] using hy))
    hnotWrite hreach

theorem RuntimeFrame.reachesWhenInitialized_ne_var_of_varsProtected
    {store : ProgramStore}
    {env : Env} {current : Lifetime}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    (∀ y, y ∈ PartialTy.vars partialTy → WriteProhibited env (.var y)) →
    ¬ WriteProhibited env (.var x) →
    RuntimeFrame.ReachesWhenInitialized env store partialValue partialTy location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hvars hnotWrite hreach
  induction hreach generalizing x with
  | undefOf hinner hstrength howner =>
      intro hlocEq
      exact RuntimeFrame.ownerReaches_ne_var_of_heap hheap hvalueHeap howner hlocEq
  | @boxHere owner slot inner hslot =>
      intro hlocEq
      have hmem :
          owner ∈ partialValueOwningLocations
            (.value (.ref { location := owner, owner := true })) := by
        simpa using
          (mem_partialValueOwningLocations_ref_true
            (ref := { location := owner, owner := true }) rfl)
      have hheapLocation : ∃ address, owner = .heap address :=
        hvalueHeap owner hmem
      rcases hheapLocation with ⟨address, hownerHeap⟩
      rw [hlocEq] at hownerHeap
      cases hownerHeap
  | @boxInner location slot inner reached hslot _hreach ih =>
      exact ih
        (partialValueOwnerTargetsHeap_of_slot hheap hslot)
        (by
          intro y hy
          exact hvars y (by simpa [PartialTy.vars] using hy))
        hnotWrite
  | @boxFullHere owner slot ty hslot =>
      intro hlocEq
      have hmem :
          owner ∈ partialValueOwningLocations
            (.value (.ref { location := owner, owner := true })) := by
        simpa using
          (mem_partialValueOwningLocations_ref_true
            (ref := { location := owner, owner := true }) rfl)
      have hheapLocation : ∃ address, owner = .heap address :=
        hvalueHeap owner hmem
      rcases hheapLocation with ⟨address, hownerHeap⟩
      rw [hlocEq] at hownerHeap
      cases hownerHeap
  | @boxFullInner location slot ty reached hslot _hreach ih =>
      exact ih
        (partialValueOwnerTargetsHeap_of_slot hheap hslot)
        (by
          intro y hy
          exact hvars y (by simpa [PartialTy.vars, Ty.vars] using hy))
        hnotWrite
  | @borrow borrowedLocation readLocation mutable targets target hinitialized hmem
      hloc hreads =>
      intro hlocEq
      subst hlocEq
      rcases hinitialized target hmem with
        ⟨targetTy, targetLifetime, htargetTyping⟩
      rcases locReads_var_writeProhibited_or_base_whenInitialized
          hwellFormed hsafe hheap htargetTyping hreads with hwp | hbase
      · exact hnotWrite hwp
      · have hxVars :
            x ∈ PartialTy.vars (.ty (.borrow mutable targets)) := by
          have hbaseMem : LVal.base target ∈ targets.map LVal.base :=
            List.mem_map_of_mem hmem
          simpa [PartialTy.vars, Ty.vars, hbase] using hbaseMem
        exact hnotWrite (hvars x hxVars)

/-- Full-value specialization of
`RuntimeFrame.reachesWhenInitialized_ne_var_of_varsProtected`. -/
theorem RuntimeFrame.value_reachesWhenInitialized_ne_var_of_varsProtected
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {value : Value} {ty : Ty} {location : Location} {x : Name} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    StoreOwnerTargetsHeap store →
    ValueOwnerTargetsHeap value →
    (∀ y, y ∈ Ty.vars ty → WriteProhibited env (.var y)) →
    ¬ WriteProhibited env (.var x) →
    RuntimeFrame.ReachesWhenInitialized env store (.value value) (.ty ty) location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hvars hnotWrite hreach
  exact RuntimeFrame.reachesWhenInitialized_ne_var_of_varsProtected
    hwellFormed hsafe hheap
    (ValueOwnerTargetsHeap.partial hvalueHeap)
    (by
      intro y hy
      exact hvars y (by simpa [PartialTy.vars] using hy))
    hnotWrite hreach

theorem RuntimeFrame.reachesWhenInitialized_ne_var_of_varsProtectedIn
    {store : ProgramStore}
    {sourceEnv observerEnv : Env} {current slotLifetime : Lifetime}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    WellFormedEnvWhenInitialized sourceEnv current →
    SafeAbstraction store sourceEnv →
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    PartialTyBorrowsWellFormedInSlotWhenInitialized
      sourceEnv slotLifetime partialTy →
    (∀ y, y ∈ PartialTy.vars partialTy →
      WriteProhibited observerEnv (.var y)) →
    (∀ y, y ≠ x → ¬ WriteProhibitedVia sourceEnv y (.var x)) →
    ¬ WriteProhibited observerEnv (.var x) →
    RuntimeFrame.ReachesWhenInitialized sourceEnv store partialValue partialTy
      location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hborrows hvarsObserver
    hnoOther hnotWriteObserver hreach hlocEq
  rcases RuntimeFrame.ReachesWhenInitialized.owner_or_borrow hreach with
    howner | hdependency
  · exact RuntimeFrame.ownerReaches_ne_var_of_heap hheap hvalueHeap
      howner hlocEq
  · rcases borrowDependencyWhenInitialized_var_writeProhibitedVia_or_mem_vars
        hwellFormed hsafe hheap hborrows hdependency x hlocEq with
      hvia | hmemVars
    · rcases hvia with ⟨y, hy, hvia⟩
      exact hnoOther y hy hvia
    · exact hnotWriteObserver (hvarsObserver x hmemVars)

theorem RuntimeFrame.value_reachesWhenInitialized_ne_var_of_varsProtectedIn
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {current lifetime : Lifetime}
    {value : Value} {ty : Ty} {location : Location} {x : Name} :
    WellFormedEnvWhenInitialized sourceEnv current →
    SafeAbstraction store sourceEnv →
    StoreOwnerTargetsHeap store →
    ValueOwnerTargetsHeap value →
    WellFormedTyWhenInitialized sourceEnv ty lifetime →
    (∀ y, y ∈ Ty.vars ty → WriteProhibited observerEnv (.var y)) →
    (∀ y, y ≠ x → ¬ WriteProhibitedVia sourceEnv y (.var x)) →
    ¬ WriteProhibited observerEnv (.var x) →
    RuntimeFrame.ReachesWhenInitialized sourceEnv store (.value value) (.ty ty)
      location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hwellTy hvars hnoOther
    hnotWriteObserver hreach
  exact RuntimeFrame.reachesWhenInitialized_ne_var_of_varsProtectedIn
    hwellFormed hsafe hheap
    (ValueOwnerTargetsHeap.partial hvalueHeap)
    (PartialTyBorrowsWellFormedInSlotWhenInitialized.of_wellFormedTy hwellTy)
    (by
      intro y hy
      exact hvars y (by simpa [PartialTy.vars] using hy))
    hnoOther hnotWriteObserver hreach

/--
Runtime owner-spine selected by a static lvalue path.

`StoreOwnerSpine S root rootSlot rootTy path leaf leafSlot leafTy` says that
starting from `root`, whose slot is valid at `rootTy`, following the owned-box
selectors in `path` reaches `leaf`, whose slot is valid at `leafTy`.
-/
inductive StoreOwnerSpine (store : ProgramStore) :
    Location → StoreSlot → PartialTy → Path → Location → StoreSlot → PartialTy → Prop where
  | nil {storage : Location} {slot : StoreSlot} {ty : PartialTy} :
      store.slotAt storage = some slot →
      ValidPartialValue store slot.value ty →
      StoreOwnerSpine store storage slot ty [] storage slot ty
    | box {storage owned leaf : Location} {slot ownedSlot leafSlot : StoreSlot}
        {inner leafTy : PartialTy} {path : Path} :
        store.slotAt storage = some slot →
        slot.value = .value (owningRef owned) →
        StoreOwnerSpine store owned ownedSlot inner path leaf leafSlot leafTy →
        StoreOwnerSpine store storage slot (.box inner) (() :: path) leaf leafSlot leafTy
    | boxFull {storage owned leaf : Location} {slot ownedSlot leafSlot : StoreSlot}
        {inner : Ty} {leafTy : PartialTy} {path : Path} :
        store.slotAt storage = some slot →
        slot.value = .value (owningRef owned) →
        StoreOwnerSpine store owned ownedSlot (.ty inner) path leaf leafSlot leafTy →
        StoreOwnerSpine store storage slot (.ty (.box inner)) (() :: path) leaf leafSlot leafTy

namespace StoreOwnerSpine

theorem storage_slot {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    store.slotAt storage = some slot := by
  intro hspine
  cases hspine with
  | nil hslot _hvalid =>
      exact hslot
    | box hslot _howns _htail =>
        exact hslot
    | boxFull hslot _howns _htail =>
        exact hslot

theorem valid {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    ValidPartialValue store slot.value ty := by
  intro hspine
  induction hspine with
  | nil _hslot hvalid =>
      exact hvalid
    | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
        _htail ih =>
        have hbox : ValidPartialValue store (.value (owningRef owned)) (.box inner) :=
          ValidPartialValue.box
            (location := owned) (slot := ownedSlot)
            (StoreOwnerSpine.storage_slot _htail) ih
        simpa [howner] using hbox
    | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
        _htail ih =>
        have hbox : ValidPartialValue store (.value (owningRef owned)) (.ty (.box inner)) :=
          ValidPartialValue.boxFull
          (location := owned) (slot := ownedSlot)
          (StoreOwnerSpine.storage_slot _htail)
          ih
        simpa [howner] using hbox

theorem leaf_valid {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    ValidPartialValue store leafSlot.value leafTy := by
  intro hspine
  induction hspine with
  | nil _hslot hvalid =>
      exact hvalid
    | box _hslot _howner _htail ih =>
        exact ih
    | boxFull _hslot _howner _htail ih =>
        exact ih

theorem leaf_protected_of_root_protected {store : ProgramStore} {x : Name}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    ProtectedByBase store x root →
    ProtectedByBase store x leaf := by
  intro hspine hprotected
  induction hspine with
  | nil _hslot _hvalid =>
      exact hprotected
    | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
        howner htail ih =>
        have howns : ProgramStore.OwnsAt store owned storage := by
          refine ⟨slot.lifetime, ?_⟩
          cases slot with
          | mk slotValue slotLifetime =>
              cases howner
              simpa [owningRef] using hslot
        have hownedProtected : ProtectedByBase store x owned :=
          ProtectedByBase.trans_owned hprotected howns
        exact ih hownedProtected
    | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
        howner htail ih =>
        have howns : ProgramStore.OwnsAt store owned storage := by
          refine ⟨slot.lifetime, ?_⟩
          cases slot with
          | mk slotValue slotLifetime =>
              cases howner
              simpa [owningRef] using hslot
        have hownedProtected : ProtectedByBase store x owned :=
          ProtectedByBase.trans_owned hprotected howns
        exact ih hownedProtected

theorem leaf_protected_by_base {store : ProgramStore} {x : Name}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    root = VariableProjection x →
    ProtectedByBase store x leaf := by
  intro hspine hroot
  exact leaf_protected_of_root_protected hspine (by
    left
    exact hroot)

theorem ownsAt_of_box {store : ProgramStore} {storage owned leaf : Location}
    {slot ownedSlot leafSlot : StoreSlot} {inner leafTy : PartialTy}
    {path : Path} :
    store.slotAt storage = some slot →
    slot.value = .value (owningRef owned) →
    StoreOwnerSpine store owned ownedSlot inner path leaf leafSlot leafTy →
    ProgramStore.OwnsAt store owned storage := by
  intro hslot howner _htail
  refine ⟨slot.lifetime, ?_⟩
  cases slot with
  | mk slotValue slotLifetime =>
      cases howner
      simpa [owningRef] using hslot

theorem valid_rebox {store : ProgramStore} {location : Location}
    {slot : StoreSlot} {updated : PartialTy} :
    store.slotAt location = some slot →
    ValidPartialValue store slot.value updated →
    ValidPartialValue store (.value (owningRef location)) (partialTyRebox updated) := by
  intro hslot hvalid
  cases updated with
  | ty inner =>
      simpa [partialTyRebox, owningRef] using
        (ValidPartialValue.boxFull (location := location) (slot := slot)
          hslot hvalid)
  | box inner =>
      simpa [partialTyRebox, owningRef] using
        (ValidPartialValue.box (location := location) (slot := slot)
          hslot hvalid)
  | undef inner =>
      simpa [partialTyRebox, owningRef] using
        (ValidPartialValue.box (location := location) (slot := slot)
          hslot hvalid)

theorem ownsTransitively_of_nonempty {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    path ≠ [] →
    ProgramStore.OwnsTransitively store storage leaf := by
  intro hspine hnonempty
  induction hspine with
  | nil =>
      exact False.elim (hnonempty rfl)
    | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner htail ih =>
        have howns : ProgramStore.OwnsAt store owned storage :=
          ownsAt_of_box hslot howner htail
        cases htail with
        | nil _hownedSlot _hvalid =>
            exact ProgramStore.OwnsTransitively.direct howns
        | box _htailSlot _htailValue _htailTail =>
            exact ProgramStore.OwnsTransitively.trans howns (ih (by simp))
        | boxFull _htailSlot _htailValue _htailTail =>
            exact ProgramStore.OwnsTransitively.trans howns (ih (by simp))
    | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner htail ih =>
        have howns : ProgramStore.OwnsAt store owned storage :=
          ownsAt_of_box hslot howner htail
        cases htail with
        | nil _hownedSlot _hvalid =>
            exact ProgramStore.OwnsTransitively.direct howns
        | boxFull _htailSlot _htailValue _htailTail =>
            exact ProgramStore.OwnsTransitively.trans howns (ih (by simp))

theorem ownsTransitively_of_cons {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store storage slot ty (() :: path) leaf leafSlot leafTy →
    ProgramStore.OwnsTransitively store storage leaf := by
  intro hspine
  exact ownsTransitively_of_nonempty hspine (by simp)

theorem leaf_ne_storage_of_cons {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store storage slot ty (() :: path) leaf leafSlot leafTy →
    leaf ≠ storage := by
  intro hspine hleaf
  have hcycle : ProgramStore.OwnsTransitively store storage storage := by
    simpa [hleaf] using ownsTransitively_of_cons hspine
  exact ValidPartialValue.no_storage_ownership_cycle
    (StoreOwnerSpine.storage_slot hspine)
    (StoreOwnerSpine.valid hspine)
    hcycle

theorem snoc_box {store : ProgramStore} {root storage owned : Location}
    {rootSlot slot ownedSlot : StoreSlot} {rootTy leafTy inner : PartialTy}
    {path : Path} :
    StoreOwnerSpine store root rootSlot rootTy path storage slot leafTy →
    leafTy = .box inner →
    slot.value = .value (owningRef owned) →
    store.slotAt owned = some ownedSlot →
    ValidPartialValue store ownedSlot.value inner →
    StoreOwnerSpine store root rootSlot rootTy (() :: path) owned ownedSlot inner := by
  intro hspine hleafTy howner hownedSlot hinnerValid
  induction hspine generalizing inner owned ownedSlot with
  | nil hslot hvalid =>
      subst hleafTy
      exact StoreOwnerSpine.box hslot howner
        (StoreOwnerSpine.nil hownedSlot hinnerValid)
    | @box root first storage rootSlot firstSlot slot rootInner leafTy path hrootSlot
        hrootOwner htail ih =>
        subst hleafTy
        exact StoreOwnerSpine.box hrootSlot hrootOwner
          (ih rfl howner hownedSlot hinnerValid)
    | @boxFull root first storage rootSlot firstSlot slot rootInner leafTy path hrootSlot
        hrootOwner htail ih =>
        subst hleafTy
        exact StoreOwnerSpine.boxFull hrootSlot hrootOwner
          (ih rfl howner hownedSlot hinnerValid)

  theorem snoc_boxFull {store : ProgramStore} {root storage owned : Location}
      {rootSlot slot ownedSlot : StoreSlot} {rootTy leafTy : PartialTy}
      {inner : Ty} {path : Path} :
      StoreOwnerSpine store root rootSlot rootTy path storage slot leafTy →
      leafTy = .ty (.box inner) →
      slot.value = .value (owningRef owned) →
      store.slotAt owned = some ownedSlot →
      ValidPartialValue store ownedSlot.value (.ty inner) →
      StoreOwnerSpine store root rootSlot rootTy (() :: path) owned ownedSlot (.ty inner) := by
    intro hspine hleafTy howner hownedSlot hinnerValid
    induction hspine generalizing inner owned ownedSlot with
    | nil hslot hvalid =>
        subst hleafTy
        exact StoreOwnerSpine.boxFull hslot howner
          (StoreOwnerSpine.nil hownedSlot hinnerValid)
    | @box root first storage rootSlot firstSlot slot rootInner leafTy path hrootSlot
        hrootOwner htail ih =>
        subst hleafTy
        exact StoreOwnerSpine.box hrootSlot hrootOwner
          (ih rfl howner hownedSlot hinnerValid)
    | @boxFull root first storage rootSlot firstSlot slot rootInner leafTy path hrootSlot
        hrootOwner htail ih =>
        subst hleafTy
        exact StoreOwnerSpine.boxFull hrootSlot hrootOwner
          (ih rfl howner hownedSlot hinnerValid)

theorem of_lvalTyping_box {store : ProgramStore} {env : Env}
    {current : Lifetime} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ∀ {lv : LVal} {inner : PartialTy} {lifetime : Lifetime},
      LValTyping env lv (.box inner) lifetime →
      ∃ envSlot rootSlot leaf leafSlot,
        env.slotAt (LVal.base lv) = some envSlot ∧
        store.slotAt (VariableProjection (LVal.base lv)) = some rootSlot ∧
        rootSlot.lifetime = envSlot.lifetime ∧
        store.loc lv = some leaf ∧
        store.slotAt leaf = some leafSlot ∧
        StoreOwnerSpine store (VariableProjection (LVal.base lv)) rootSlot
          envSlot.ty (LVal.path lv) leaf leafSlot (.box inner) := by
  intro hwell hsafe lv
  induction lv with
  | var x =>
      intro inner lifetime htyping
      rcases LValTyping.var_inv htyping with ⟨envSlot, henv, hty, hlifetime⟩
      rcases hsafe.2 x envSlot henv with ⟨value, hstore, hvalid⟩
      have hvalidBox : ValidPartialValue store value (.box inner) := by
        simpa [hty] using hvalid
      refine ⟨envSlot, { value := value, lifetime := envSlot.lifetime },
        VariableProjection x, { value := value, lifetime := envSlot.lifetime },
        henv, hstore, rfl, ?_, hstore, ?_⟩
      · simp [ProgramStore.loc, VariableProjection]
      · simpa [LVal.base, LVal.path, hty] using
          (StoreOwnerSpine.nil hstore hvalidBox)
  | deref source ih =>
      intro inner lifetime htyping
      have hsourceTyping :
          LValTyping env source (.box (.box inner)) lifetime :=
        LValTyping.deref_box_inv htyping
      rcases ih hsourceTyping with
        ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henv, hrootSlot,
          hrootLifetime, hsourceLoc, hsourceSlot, hspine⟩
      have hsourceValid :
          ValidPartialValue store sourceSlot.value (.box (.box inner)) :=
        StoreOwnerSpine.leaf_valid hspine
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
          have hderefLoc :
              store.loc (.deref source) = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hspineDeref :
              StoreOwnerSpine store (VariableProjection (LVal.base source))
                rootSlot envSlot.ty (() :: LVal.path source) ownerLocation
                ownerSlot (.box inner) :=
            StoreOwnerSpine.snoc_box hspine rfl rfl hownedSlot hinnerValid
          refine ⟨envSlot, rootSlot, ownerLocation, ownerSlot, ?_, ?_,
            hrootLifetime, hderefLoc, hownedSlot, ?_⟩
          · simpa [LVal.base] using henv
          · simpa [LVal.base] using hrootSlot
          · simpa [LVal.base, LVal.path_deref_cons] using hspineDeref

theorem valid_after_updateAtPath_nonempty {store : ProgramStore} {env writeEnv : Env}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {path : Path}
    {rhsTy : Ty} {value : Value} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    path ≠ [] →
    UpdateAtPath 0 env path rootTy rhsTy writeEnv updatedTy →
    ValidPartialValue
      (store.update leaf { leafSlot with value := .value value })
      (.value value) (.ty rhsTy) →
    ValidPartialValue
      (store.update leaf { leafSlot with value := .value value })
      rootSlot.value updatedTy := by
  intro hspine hnonempty hupdate hnewLeafValid
  induction hspine generalizing env writeEnv updatedTy rhsTy value with
  | nil =>
      exact False.elim (hnonempty rfl)
  | @box storage owned leaf slot ownedSlot leafSlot spineInner leafTy path hslot howner
      htail ih =>
      cases hupdate with
      | @box _env₁ _env₂ _rank _path _inner updatedInner _ty hinnerUpdate =>
          cases htail with
          | nil hownedSlot _holdValid =>
              cases hinnerUpdate with
              | strong =>
                  have hownedSlotWrite :
                      (store.update owned { ownedSlot with value := .value value }).slotAt
                        owned =
                        some { value := .value value, lifetime := ownedSlot.lifetime } := by
                    simp [ProgramStore.update]
                  have hbox :
                      ValidPartialValue
                        (store.update owned { ownedSlot with value := .value value })
                        (.value (owningRef owned)) (.box (.ty rhsTy)) :=
                    ValidPartialValue.box hownedSlotWrite hnewLeafValid
                  simpa [howner] using hbox
          | box htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpine.box htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .value value })
                    ownedSlot.value updatedInner :=
                ih (by simp) hinnerUpdate hnewLeafValid
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf { leafSlot with value := .value value }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpine.storage_slot htailSpine)
              have hbox :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .value value })
                    (.value (owningRef owned)) (.box updatedInner) :=
                ValidPartialValue.box hownedSlotWrite htailValid
              simpa [howner] using hbox
          | boxFull htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpine.boxFull htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .value value })
                    ownedSlot.value updatedInner :=
                ih (by simp) hinnerUpdate hnewLeafValid
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf { leafSlot with value := .value value }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpine.storage_slot htailSpine)
              have hbox :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .value value })
                    (.value (owningRef owned)) (.box updatedInner) :=
                ValidPartialValue.box hownedSlotWrite htailValid
              simpa [howner] using hbox
  | @boxFull storage owned leaf slot ownedSlot leafSlot spineInner leafTy path
      hslot howner htail ih =>
      cases hupdate with
      | @boxFull _env₁ _env₂ _rank _path _inner updatedInner _ty hinnerUpdate =>
          cases htail with
          | nil hownedSlot _holdValid =>
              cases hinnerUpdate with
              | strong =>
                  have hownedSlotWrite :
                      (store.update owned { ownedSlot with value := .value value }).slotAt
                        owned =
                        some { value := .value value, lifetime := ownedSlot.lifetime } := by
                    simp [ProgramStore.update]
                  have hbox :
                      ValidPartialValue
                        (store.update owned { ownedSlot with value := .value value })
                        (.value (owningRef owned)) (partialTyRebox (.ty rhsTy)) :=
                    StoreOwnerSpine.valid_rebox hownedSlotWrite hnewLeafValid
                  simpa [howner] using hbox
          | boxFull htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpine.boxFull htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .value value })
                    ownedSlot.value updatedInner :=
                ih (by simp) hinnerUpdate hnewLeafValid
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf { leafSlot with value := .value value }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpine.storage_slot htailSpine)
              have hbox :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .value value })
                    (.value (owningRef owned)) (partialTyRebox updatedInner) :=
                StoreOwnerSpine.valid_rebox hownedSlotWrite htailValid
              simpa [howner] using hbox

theorem valid_after_strike_nonempty_aux {store : ProgramStore}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy struck leafTy : PartialTy} {path : Path} {ty : Ty} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    leafTy = .ty ty →
    path ≠ [] →
    Strike path rootTy struck →
    ValidPartialValue
      (store.update leaf { leafSlot with value := .undef })
      rootSlot.value struck := by
  intro hspine hleafTy hnonempty hstrike
  induction hspine generalizing struck ty with
  | nil =>
      exact False.elim (hnonempty rfl)
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      cases struck with
      | ty struckTy | undef struckTy =>
          simp [Strike] at hstrike
      | box struckInner =>
          have hinnerStrike : Strike path inner struckInner := by
            simpa [Strike] using hstrike
          cases htail with
          | nil hownedSlot hownedValid =>
              cases hleafTy
              cases struckInner with
              | ty movedTy =>
                  simp [Strike] at hinnerStrike
              | box movedInner =>
                  simp [Strike] at hinnerStrike
              | undef movedTy =>
                  have hownedSlotWrite :
                      (store.update owned { ownedSlot with value := .undef }).slotAt
                        owned =
                        some { value := .undef, lifetime := ownedSlot.lifetime } := by
                    simp [ProgramStore.update]
                  have hbox :
                      ValidPartialValue
                        (store.update owned { ownedSlot with value := .undef })
                        (.value (owningRef owned)) (.box (.undef movedTy)) :=
                    ValidPartialValue.box hownedSlotWrite
                      (ValidPartialValue.undef (ty := movedTy))
                  simpa [howner] using hbox
          | box htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpine.box htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .undef })
                    ownedSlot.value struckInner :=
                ih hleafTy (by simp) hinnerStrike
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf { leafSlot with value := .undef }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpine.storage_slot htailSpine)
              have hbox :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .undef })
                    (.value (owningRef owned)) (.box struckInner) :=
                ValidPartialValue.box hownedSlotWrite htailValid
              simpa [howner] using hbox
          | boxFull htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpine.boxFull htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .undef })
                    ownedSlot.value struckInner :=
                ih hleafTy (by simp) hinnerStrike
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf { leafSlot with value := .undef }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpine.storage_slot htailSpine)
              have hbox :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .undef })
                    (.value (owningRef owned)) (.box struckInner) :=
                ValidPartialValue.box hownedSlotWrite htailValid
              simpa [howner] using hbox
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases struck with
      | ty struckTy | undef struckTy =>
          simp [Strike] at hstrike
      | box struckInner =>
          have hinnerStrike : Strike path (.ty inner) struckInner := by
            simpa [Strike] using hstrike
          cases htail with
          | nil hownedSlot hownedValid =>
              cases hleafTy
              cases struckInner with
              | ty movedTy =>
                  simp [Strike] at hinnerStrike
              | box movedInner =>
                  simp [Strike] at hinnerStrike
              | undef movedTy =>
                  have hownedSlotWrite :
                      (store.update owned { ownedSlot with value := .undef }).slotAt
                        owned =
                        some { value := .undef, lifetime := ownedSlot.lifetime } := by
                    simp [ProgramStore.update]
                  have hbox :
                      ValidPartialValue
                        (store.update owned { ownedSlot with value := .undef })
                        (.value (owningRef owned)) (.box (.undef movedTy)) :=
                    ValidPartialValue.box hownedSlotWrite
                      (ValidPartialValue.undef (ty := movedTy))
                  simpa [howner] using hbox
          | boxFull htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpine.boxFull htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .undef })
                    ownedSlot.value struckInner :=
                ih hleafTy (by simp) hinnerStrike
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf { leafSlot with value := .undef }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpine.storage_slot htailSpine)
              have hbox :
                  ValidPartialValue
                    (store.update leaf { leafSlot with value := .undef })
                    (.value (owningRef owned)) (.box struckInner) :=
                ValidPartialValue.box hownedSlotWrite htailValid
              simpa [howner] using hbox

theorem valid_after_strike_nonempty {store : ProgramStore}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy struck : PartialTy} {path : Path} {ty : Ty} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot (.ty ty) →
    path ≠ [] →
    Strike path rootTy struck →
    ValidPartialValue
      (store.update leaf { leafSlot with value := .undef })
      rootSlot.value struck := by
  intro hspine hnonempty hstrike
  exact valid_after_strike_nonempty_aux hspine rfl hnonempty hstrike

theorem updateAtPath_rank_zero_env_eq {store : ProgramStore} {env writeEnv : Env}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {path : Path}
    {rhsTy : Ty} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    UpdateAtPath 0 env path rootTy rhsTy writeEnv updatedTy →
    writeEnv = env := by
  intro hspine hupdate
  induction hspine generalizing env writeEnv updatedTy rhsTy with
  | nil _hslot _hvalid =>
      cases hupdate with
      | strong =>
          rfl
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      cases hupdate with
      | box hinner =>
          exact ih hinner
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | boxFull hinner =>
          exact ih hinner

theorem updateAtPath_env_eq {store : ProgramStore} {env writeEnv : Env}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {path : Path}
    {rhsTy : Ty} {rank : Nat} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    UpdateAtPath rank env path rootTy rhsTy writeEnv updatedTy →
    writeEnv = env := by
  intro hspine hupdate
  induction hspine generalizing env writeEnv updatedTy rhsTy rank with
  | nil _hslot _hvalid =>
      cases hupdate with
      | strong | weak _hshape _hjoin => rfl
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      cases hupdate with
      | box hinner =>
          exact ih hinner
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | boxFull hinner =>
          exact ih hinner

theorem updateAtPath_rank_zero_rhs_vars_subset_updated
    {store : ProgramStore} {env writeEnv : Env}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {path : Path}
    {rhsTy : Ty} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    UpdateAtPath 0 env path rootTy rhsTy writeEnv updatedTy →
    ∀ v, v ∈ PartialTy.vars (.ty rhsTy) → v ∈ PartialTy.vars updatedTy := by
  intro hspine hupdate
  induction hspine generalizing env writeEnv updatedTy rhsTy with
  | nil _hslot _hvalid =>
      cases hupdate with
      | strong =>
          intro v hv
          simpa using hv
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | box hinner =>
          intro v hv
          exact ih hinner v hv
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | @boxFull _env₁ _env₂ _rank _path _inner updatedInner _ty hinner =>
          intro v hv
          have hres := ih hinner v hv
          cases updatedInner <;>
            simpa [partialTyRebox, PartialTy.vars, Ty.vars] using hres

theorem not_reaches_leaf_of_not_reaches_root_of_owner_disjoint
    {store : ProgramStore}
    {env : Env} {slotLifetime : Lifetime}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path}
    {value : Value} {rhsTy : Ty} :
    ValidStore store →
    (∀ owned, owned ∈ valueOwningLocations value →
      ¬ ProgramStore.Owns store owned) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    ValidValue store value rhsTy →
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    (∀ reached,
      RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
      reached ≠ root) →
    ∀ reached,
      RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
      reached ≠ leaf := by
  intro hvalidStore hownerDisjoint hborrows hvalidValue hspine
  induction hspine with
  | nil _hslot _hvalid =>
      intro hrootNoReach
      exact hrootNoReach
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      intro hstorageNoReach
      have howns : ProgramStore.OwnsAt store owned storage :=
        StoreOwnerSpine.ownsAt_of_box hslot howner htail
      have hownedNoReach :
          ∀ reached,
            RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
            reached ≠ owned := by
        intro reached hreach hreached
        subst reached
        rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
            hborrows hvalidValue hreach with hdirect | hsource
        · exact hownerDisjoint owned
            (by simpa [partialValueOwningLocations] using hdirect)
            ⟨storage, howns⟩
        · rcases hsource with ⟨sourceStorage, hsourceReach, hsourceOwns⟩
          have hstorageEq : sourceStorage = storage :=
            hvalidStore owned sourceStorage storage hsourceOwns howns
          exact hstorageNoReach sourceStorage hsourceReach hstorageEq
      exact ih hownedNoReach
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro hstorageNoReach
      have howns : ProgramStore.OwnsAt store owned storage :=
        StoreOwnerSpine.ownsAt_of_box hslot howner htail
      have hownedNoReach :
          ∀ reached,
            RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
            reached ≠ owned := by
        intro reached hreach hreached
        subst reached
        rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
            hborrows hvalidValue hreach with hdirect | hsource
        · exact hownerDisjoint owned
            (by simpa [partialValueOwningLocations] using hdirect)
            ⟨storage, howns⟩
        · rcases hsource with ⟨sourceStorage, hsourceReach, hsourceOwns⟩
          have hstorageEq : sourceStorage = storage :=
            hvalidStore owned sourceStorage storage hsourceOwns howns
          exact hstorageNoReach sourceStorage hsourceReach hstorageEq
      exact ih hownedNoReach

theorem not_reaches_leaf_of_not_reaches_root {store : ProgramStore}
    {env : Env} {slotLifetime : Lifetime}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path}
    {value : Value} {rhsTy : Ty} :
    ValidRuntimeState store (.val value) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    ValidValue store value rhsTy →
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    (∀ reached,
      RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
      reached ≠ root) →
    ∀ reached,
      RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
      reached ≠ leaf := by
  intro hvalidRuntime
  exact not_reaches_leaf_of_not_reaches_root_of_owner_disjoint
    (ValidRuntimeState.validStore hvalidRuntime)
    (by
      intro owned howned
      exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
        (by
          simpa [termOwningLocations, termValues] using howned))

theorem stored_var_not_reaches_leaf_of_not_reaches_root {store : ProgramStore}
    {env : Env} {slotLifetime storedLifetime : Lifetime}
    {storedName : Name} {storedValue : PartialValue} {storedTy : PartialTy}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    store.slotAt (VariableProjection storedName) =
      some { value := storedValue, lifetime := storedLifetime } →
    PartialTyBorrowsWellFormedInSlot env slotLifetime storedTy →
    ValidPartialValue store storedValue storedTy →
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    VariableProjection storedName ≠ root →
    (∀ reached,
      RuntimeFrame.OwnerReaches store storedValue storedTy reached →
      reached ≠ root) →
    ∀ reached,
      RuntimeFrame.OwnerReaches store storedValue storedTy reached →
      reached ≠ leaf := by
  intro hvalidStore hheap hstored hborrows hvalid hspine
  induction hspine with
  | nil _hslot _hvalidRoot =>
      intro _hstoredNeRoot hrootNoReach
      exact hrootNoReach
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      intro hstoredNeStorage hstorageNoReach
      have howns : ProgramStore.OwnsAt store owned storage :=
        StoreOwnerSpine.ownsAt_of_box hslot howner htail
      have hownedNoReach :
          ∀ reached,
            RuntimeFrame.OwnerReaches store storedValue storedTy reached →
            reached ≠ owned := by
        intro reached hreach hreached
        subst reached
        rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
            hborrows hvalid hreach with hdirect | hsource
        · have hstoredOwns :
              ProgramStore.OwnsAt store owned (VariableProjection storedName) := by
            have hstoredValue :
                storedValue = .value (owningRef owned) :=
              eq_owningRef_of_mem_partialValueOwningLocations hdirect
            exact ⟨storedLifetime, by
              cases hstoredValue
              simpa [owningRef] using hstored⟩
          have hstorageEq : VariableProjection storedName = storage :=
            hvalidStore owned (VariableProjection storedName) storage
              hstoredOwns howns
          exact hstoredNeStorage hstorageEq
        · rcases hsource with ⟨sourceStorage, hsourceReach, hsourceOwns⟩
          have hstorageEq : sourceStorage = storage :=
            hvalidStore owned sourceStorage storage hsourceOwns howns
          exact hstorageNoReach sourceStorage hsourceReach hstorageEq
      have hstoredNeOwned : VariableProjection storedName ≠ owned := by
        intro hstoredEq
        have hownedHeap : ∃ address, owned = .heap address :=
          hheap owned ⟨storage, howns⟩
        rcases hownedHeap with ⟨address, hownedHeap⟩
        rw [← hstoredEq] at hownedHeap
        cases hownedHeap
      exact ih hstoredNeOwned hownedNoReach
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro hstoredNeStorage hstorageNoReach
      have howns : ProgramStore.OwnsAt store owned storage :=
        StoreOwnerSpine.ownsAt_of_box hslot howner htail
      have hownedNoReach :
          ∀ reached,
            RuntimeFrame.OwnerReaches store storedValue storedTy reached →
            reached ≠ owned := by
        intro reached hreach hreached
        subst reached
        rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
            hborrows hvalid hreach with hdirect | hsource
        · have hstoredOwns :
              ProgramStore.OwnsAt store owned (VariableProjection storedName) := by
            have hstoredValue :
                storedValue = .value (owningRef owned) :=
              eq_owningRef_of_mem_partialValueOwningLocations hdirect
            exact ⟨storedLifetime, by
              cases hstoredValue
              simpa [owningRef] using hstored⟩
          have hstorageEq : VariableProjection storedName = storage :=
            hvalidStore owned (VariableProjection storedName) storage
              hstoredOwns howns
          exact hstoredNeStorage hstorageEq
        · rcases hsource with ⟨sourceStorage, hsourceReach, hsourceOwns⟩
          have hstorageEq : sourceStorage = storage :=
            hvalidStore owned sourceStorage storage hsourceOwns howns
          exact hstorageNoReach sourceStorage hsourceReach hstorageEq
      have hstoredNeOwned : VariableProjection storedName ≠ owned := by
        intro hstoredEq
        have hownedHeap : ∃ address, owned = .heap address :=
          hheap owned ⟨storage, howns⟩
        rcases hownedHeap with ⟨address, hownedHeap⟩
        rw [← hstoredEq] at hownedHeap
        cases hownedHeap
      exact ih hstoredNeOwned hownedNoReach

end StoreOwnerSpine

/--
Weak runtime owner-spine selected by a static lvalue path.

This is the stale-aware counterpart of `StoreOwnerSpine`: the concrete ownership
path is still present, but stored payloads are only required to satisfy
`ValidPartialValueWhenInitialized`.  In particular, a boxed stale borrow remains
admissible as a protection token.
-/
inductive StoreOwnerSpineWhenInitialized (env : Env) (store : ProgramStore) :
    Location → StoreSlot → PartialTy → Path → Location → StoreSlot → PartialTy → Prop where
  | nil {storage : Location} {slot : StoreSlot} {ty : PartialTy} :
      store.slotAt storage = some slot →
      ValidPartialValueWhenInitialized env store slot.value ty →
      StoreOwnerSpineWhenInitialized env store storage slot ty [] storage slot ty
  | box {storage owned leaf : Location} {slot ownedSlot leafSlot : StoreSlot}
      {inner leafTy : PartialTy} {path : Path} :
      store.slotAt storage = some slot →
      slot.value = .value (owningRef owned) →
      StoreOwnerSpineWhenInitialized env store owned ownedSlot inner path leaf leafSlot leafTy →
      StoreOwnerSpineWhenInitialized env store storage slot (.box inner) (() :: path)
        leaf leafSlot leafTy
  | boxFull {storage owned leaf : Location} {slot ownedSlot leafSlot : StoreSlot}
      {inner : Ty} {leafTy : PartialTy} {path : Path} :
      store.slotAt storage = some slot →
      slot.value = .value (owningRef owned) →
      StoreOwnerSpineWhenInitialized env store owned ownedSlot (.ty inner) path
        leaf leafSlot leafTy →
      StoreOwnerSpineWhenInitialized env store storage slot (.ty (.box inner))
        (() :: path) leaf leafSlot leafTy

namespace StoreOwnerSpineWhenInitialized

theorem storage_slot {env : Env} {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf leafSlot leafTy →
    store.slotAt storage = some slot := by
  intro hspine
  cases hspine with
  | nil hslot _hvalid =>
      exact hslot
  | box hslot _howns _htail =>
      exact hslot
  | boxFull hslot _howns _htail =>
      exact hslot

theorem valid {env : Env} {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf leafSlot leafTy →
    ValidPartialValueWhenInitialized env store slot.value ty := by
  intro hspine
  induction hspine with
  | nil _hslot hvalid =>
      exact hvalid
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      _htail ih =>
      have hbox :
          ValidPartialValueWhenInitialized env store
            (.value (owningRef owned)) (.box inner) :=
        ValidPartialValueWhenInitialized.box
          (location := owned) (slot := ownedSlot)
          (StoreOwnerSpineWhenInitialized.storage_slot _htail)
          ih
      simpa [howner] using hbox
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner _htail ih =>
      have hbox :
          ValidPartialValueWhenInitialized env store
            (.value (owningRef owned)) (.ty (.box inner)) :=
        ValidPartialValueWhenInitialized.boxFull
          (location := owned) (slot := ownedSlot)
          (StoreOwnerSpineWhenInitialized.storage_slot _htail)
          ih
      simpa [howner] using hbox

theorem leaf_valid {env : Env} {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf leafSlot leafTy →
    ValidPartialValueWhenInitialized env store leafSlot.value leafTy := by
  intro hspine
  induction hspine with
  | nil _hslot hvalid =>
      exact hvalid
  | box _hslot _howner _htail ih =>
      exact ih
  | boxFull _hslot _howner _htail ih =>
      exact ih

theorem leaf_protected_of_root_protected {env : Env} {store : ProgramStore}
    {x : Name} {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf leafSlot leafTy →
    ProtectedByBase store x root →
    ProtectedByBase store x leaf := by
  intro hspine hprotected
  induction hspine with
  | nil _hslot _hvalid =>
      exact hprotected
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      have howns : ProgramStore.OwnsAt store owned storage := by
        refine ⟨slot.lifetime, ?_⟩
        cases slot with
        | mk slotValue slotLifetime =>
            cases howner
            simpa [owningRef] using hslot
      exact ih (ProtectedByBase.trans_owned hprotected howns)
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      have howns : ProgramStore.OwnsAt store owned storage := by
        refine ⟨slot.lifetime, ?_⟩
        cases slot with
        | mk slotValue slotLifetime =>
            cases howner
            simpa [owningRef] using hslot
      exact ih (ProtectedByBase.trans_owned hprotected howns)

theorem leaf_protected_by_base {env : Env} {store : ProgramStore} {x : Name}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf leafSlot leafTy →
    root = VariableProjection x →
    ProtectedByBase store x leaf := by
  intro hspine hroot
  exact leaf_protected_of_root_protected hspine (by
    left
    exact hroot)

theorem ownsAt_of_box {env : Env} {store : ProgramStore} {storage owned leaf : Location}
    {slot ownedSlot leafSlot : StoreSlot} {inner leafTy : PartialTy}
    {path : Path} :
    store.slotAt storage = some slot →
    slot.value = .value (owningRef owned) →
    StoreOwnerSpineWhenInitialized env store owned ownedSlot inner path leaf leafSlot leafTy →
    ProgramStore.OwnsAt store owned storage := by
  intro hslot howner _htail
  refine ⟨slot.lifetime, ?_⟩
  cases slot with
  | mk slotValue slotLifetime =>
      cases howner
      simpa [owningRef] using hslot

theorem ownsTransitively_of_nonempty {env : Env} {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot} {ty leafTy : PartialTy}
    {path : Path} :
    StoreOwnerSpineWhenInitialized env store storage slot ty path leaf leafSlot leafTy →
    path ≠ [] →
    ProgramStore.OwnsTransitively store storage leaf := by
  intro hspine hnonempty
  induction hspine with
  | nil =>
      exact False.elim (hnonempty rfl)
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner htail ih =>
      have howns : ProgramStore.OwnsAt store owned storage :=
        ownsAt_of_box hslot howner htail
      cases htail with
      | nil _hownedSlot _hvalid =>
          exact ProgramStore.OwnsTransitively.direct howns
      | box _htailSlot _htailValue _htailTail =>
          exact ProgramStore.OwnsTransitively.trans howns (ih (by simp))
      | boxFull _htailSlot _htailValue _htailTail =>
          exact ProgramStore.OwnsTransitively.trans howns (ih (by simp))
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      have howns : ProgramStore.OwnsAt store owned storage :=
        ownsAt_of_box hslot howner htail
      cases htail with
      | nil _hownedSlot _hvalid =>
          exact ProgramStore.OwnsTransitively.direct howns
      | boxFull _htailSlot _htailValue _htailTail =>
          exact ProgramStore.OwnsTransitively.trans howns (ih (by simp))

theorem ownsTransitively_of_cons {env : Env} {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot} {ty leafTy : PartialTy}
    {path : Path} :
    StoreOwnerSpineWhenInitialized env store storage slot ty (() :: path) leaf leafSlot leafTy →
    ProgramStore.OwnsTransitively store storage leaf := by
  intro hspine
  exact ownsTransitively_of_nonempty hspine (by simp)

theorem leaf_ne_storage_of_cons {env : Env} {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot} {ty leafTy : PartialTy}
    {path : Path} :
    StoreOwnerSpineWhenInitialized env store storage slot ty (() :: path) leaf leafSlot leafTy →
    leaf ≠ storage := by
  intro hspine hleaf
  have hcycle : ProgramStore.OwnsTransitively store storage storage := by
    simpa [hleaf] using ownsTransitively_of_cons hspine
  have hslot := StoreOwnerSpineWhenInitialized.storage_slot hspine
  have hvalid := (StoreOwnerSpineWhenInitialized.valid hspine).skeleton
  cases hcycle with
  | direct howns =>
      rcases howns with ⟨ownerLifetime, hownerSlot⟩
      have hslotValue :
          slot.value = .value (owningRef storage) := by
        have hslotEq :
            slot =
              { value := .value (owningRef storage),
                lifetime := ownerLifetime } :=
          Option.some.inj (hslot.symm.trans hownerSlot)
        exact congrArg StoreSlot.value hslotEq
      have hmem :
          storage ∈ partialValueOwningLocations slot.value :=
        mem_partialValueOwningLocations_of_eq_owningRef hslotValue
      exact ValidPartialValueSkeleton.no_owned_path_to_storage
        hvalid hslot rfl hmem
        (ProgramStore.OwnsTransitively.direct ⟨ownerLifetime, hownerSlot⟩)
  | trans howns htail =>
      rename_i middle
      rcases howns with ⟨ownerLifetime, hownerSlot⟩
      have hslotValue :
          slot.value = .value (owningRef middle) := by
        have hslotEq :
            slot =
              { value := .value (owningRef middle),
                lifetime := ownerLifetime } :=
          Option.some.inj (hslot.symm.trans hownerSlot)
        exact congrArg StoreSlot.value hslotEq
      have hmem :
          middle ∈ partialValueOwningLocations slot.value :=
        mem_partialValueOwningLocations_of_eq_owningRef hslotValue
      exact ValidPartialValueSkeleton.no_owned_path_to_storage
        hvalid hslot rfl hmem htail

theorem snoc_box {env : Env} {store : ProgramStore} {root storage owned : Location}
    {rootSlot slot ownedSlot : StoreSlot} {rootTy leafTy inner : PartialTy}
    {path : Path} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path storage slot leafTy →
    leafTy = .box inner →
    slot.value = .value (owningRef owned) →
    store.slotAt owned = some ownedSlot →
    ValidPartialValueWhenInitialized env store ownedSlot.value inner →
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy (() :: path)
      owned ownedSlot inner := by
  intro hspine hleafTy howner hownedSlot hinnerValid
  induction hspine generalizing inner owned ownedSlot with
  | nil hslot hvalid =>
      subst hleafTy
      exact StoreOwnerSpineWhenInitialized.box hslot howner
        (StoreOwnerSpineWhenInitialized.nil hownedSlot hinnerValid)
  | @box root first storage rootSlot firstSlot slot rootInner leafTy path hrootSlot
      hrootOwner htail ih =>
      subst hleafTy
      exact StoreOwnerSpineWhenInitialized.box hrootSlot hrootOwner
        (ih rfl howner hownedSlot hinnerValid)
  | @boxFull root first storage rootSlot firstSlot slot rootInner leafTy path
      hrootSlot hrootOwner htail ih =>
      subst hleafTy
      exact StoreOwnerSpineWhenInitialized.boxFull hrootSlot hrootOwner
        (ih rfl howner hownedSlot hinnerValid)

theorem snoc_boxFull {env : Env} {store : ProgramStore}
    {root storage owned : Location}
    {rootSlot slot ownedSlot : StoreSlot} {rootTy leafTy : PartialTy}
    {inner : Ty} {path : Path} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path storage
      slot leafTy →
    leafTy = .ty (.box inner) →
    slot.value = .value (owningRef owned) →
    store.slotAt owned = some ownedSlot →
    ValidPartialValueWhenInitialized env store ownedSlot.value (.ty inner) →
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy (() :: path)
      owned ownedSlot (.ty inner) := by
  intro hspine hleafTy howner hownedSlot hinnerValid
  induction hspine generalizing inner owned ownedSlot with
  | nil hslot hvalid =>
      subst hleafTy
      exact StoreOwnerSpineWhenInitialized.boxFull hslot howner
        (StoreOwnerSpineWhenInitialized.nil hownedSlot hinnerValid)
  | @box root first storage rootSlot firstSlot slot rootInner leafTy path
      hrootSlot hrootOwner htail ih =>
      subst hleafTy
      exact StoreOwnerSpineWhenInitialized.box hrootSlot hrootOwner
        (ih rfl howner hownedSlot hinnerValid)
  | @boxFull root first storage rootSlot firstSlot slot rootInner leafTy path
      hrootSlot hrootOwner htail ih =>
      subst hleafTy
      exact StoreOwnerSpineWhenInitialized.boxFull hrootSlot hrootOwner
        (ih rfl howner hownedSlot hinnerValid)

theorem of_lvalTyping_box {store : ProgramStore} {env : Env}
    {current : Lifetime} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ∀ {lv : LVal} {inner : PartialTy} {lifetime : Lifetime},
      LValTyping env lv (.box inner) lifetime →
      ∃ envSlot rootSlot leaf leafSlot,
        env.slotAt (LVal.base lv) = some envSlot ∧
        store.slotAt (VariableProjection (LVal.base lv)) = some rootSlot ∧
        rootSlot.lifetime = envSlot.lifetime ∧
        store.loc lv = some leaf ∧
        store.slotAt leaf = some leafSlot ∧
        StoreOwnerSpineWhenInitialized env store (VariableProjection (LVal.base lv))
          rootSlot envSlot.ty (LVal.path lv) leaf leafSlot (.box inner) := by
  intro _hwell hsafe lv
  induction lv with
  | var x =>
      intro inner lifetime htyping
      rcases LValTyping.var_inv htyping with ⟨envSlot, henv, hty, _hlifetime⟩
      rcases hsafe.2 x envSlot henv with ⟨value, hstore, hvalid⟩
      have hvalidBox :
          ValidPartialValueWhenInitialized env store value (.box inner) := by
        simpa [hty] using hvalid
      refine ⟨envSlot, { value := value, lifetime := envSlot.lifetime },
        VariableProjection x, { value := value, lifetime := envSlot.lifetime },
        henv, hstore, rfl, ?_, hstore, ?_⟩
      · simp [ProgramStore.loc, VariableProjection]
      · simpa [LVal.base, LVal.path, hty] using
          (StoreOwnerSpineWhenInitialized.nil hstore hvalidBox)
  | deref source ih =>
      intro inner lifetime htyping
      have hsourceTyping :
          LValTyping env source (.box (.box inner)) lifetime :=
        LValTyping.deref_box_inv htyping
      rcases ih hsourceTyping with
        ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henv, hrootSlot,
          hrootLifetime, hsourceLoc, hsourceSlot, hspine⟩
      have hsourceValid :
          ValidPartialValueWhenInitialized env store sourceSlot.value (.box (.box inner)) :=
        StoreOwnerSpineWhenInitialized.leaf_valid hspine
      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
      cases hsourceValid with
      | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
          have hderefLoc :
              store.loc (.deref source) = some ownerLocation := by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
          have hspineDeref :
              StoreOwnerSpineWhenInitialized env store
                (VariableProjection (LVal.base source))
                rootSlot envSlot.ty (() :: LVal.path source) ownerLocation
                ownerSlot (.box inner) :=
            StoreOwnerSpineWhenInitialized.snoc_box hspine rfl rfl hownedSlot hinnerValid
          refine ⟨envSlot, rootSlot, ownerLocation, ownerSlot, ?_, ?_,
            hrootLifetime, hderefLoc, hownedSlot, ?_⟩
          · simpa [LVal.base] using henv
          · simpa [LVal.base] using hrootSlot
          · simpa [LVal.base, LVal.path_deref_cons] using hspineDeref

theorem valid_rebox {env : Env} {store : ProgramStore} {location : Location}
    {slot : StoreSlot} {updated : PartialTy} :
    store.slotAt location = some slot →
    ValidPartialValueWhenInitialized env store slot.value updated →
    ValidPartialValueWhenInitialized env store (.value (owningRef location))
      (partialTyRebox updated) := by
  intro hslot hvalid
  cases updated with
  | ty inner =>
      simpa [partialTyRebox, owningRef] using
        (ValidPartialValueWhenInitialized.boxFull (location := location)
          (slot := slot) hslot hvalid)
  | box inner =>
      simpa [partialTyRebox, owningRef] using
        (ValidPartialValueWhenInitialized.box (location := location)
          (slot := slot) hslot hvalid)
  | undef inner =>
      simpa [partialTyRebox, owningRef] using
        (ValidPartialValueWhenInitialized.box (location := location)
          (slot := slot) hslot hvalid)

theorem valid_after_strike_nonempty_aux {env : Env} {store : ProgramStore}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy struck leafTy : PartialTy} {path : Path} {ty : Ty} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf leafSlot leafTy →
    leafTy = .ty ty →
    path ≠ [] →
    Strike path rootTy struck →
    ValidPartialValueWhenInitialized env
      (store.update leaf { leafSlot with value := .undef })
      rootSlot.value struck := by
  intro hspine hleafTy hnonempty hstrike
  induction hspine generalizing struck ty with
  | nil =>
      exact False.elim (hnonempty rfl)
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      cases struck with
      | ty struckTy | undef struckTy =>
          simp [Strike] at hstrike
      | box struckInner =>
          have hinnerStrike : Strike path inner struckInner := by
            simpa [Strike] using hstrike
          cases htail with
          | nil hownedSlot _hownedValid =>
              cases hleafTy
              cases struckInner with
              | ty movedTy =>
                  simp [Strike] at hinnerStrike
              | box movedInner =>
                  simp [Strike] at hinnerStrike
              | undef movedTy =>
                  have hownedSlotWrite :
                      (store.update owned { ownedSlot with value := .undef }).slotAt
                        owned =
                        some { value := .undef, lifetime := ownedSlot.lifetime } := by
                    simp [ProgramStore.update]
                  have hbox :
                      ValidPartialValueWhenInitialized env
                        (store.update owned { ownedSlot with value := .undef })
                        (.value (owningRef owned)) (.box (.undef movedTy)) :=
                    ValidPartialValueWhenInitialized.box hownedSlotWrite
                      (ValidPartialValueWhenInitialized.undef (ty := movedTy))
                  simpa [howner] using hbox
          | box htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpineWhenInitialized.box htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf { leafSlot with value := .undef })
                    ownedSlot.value struckInner :=
                ih hleafTy (by simp) hinnerStrike
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf { leafSlot with value := .undef }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpineWhenInitialized.storage_slot htailSpine)
              have hbox :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf { leafSlot with value := .undef })
                    (.value (owningRef owned)) (.box struckInner) :=
                  ValidPartialValueWhenInitialized.box hownedSlotWrite htailValid
              simpa [howner] using hbox
          | boxFull htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpineWhenInitialized.boxFull htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf { leafSlot with value := .undef })
                    ownedSlot.value struckInner :=
                ih hleafTy (by simp) hinnerStrike
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf { leafSlot with value := .undef }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpineWhenInitialized.storage_slot htailSpine)
              have hbox :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf { leafSlot with value := .undef })
                    (.value (owningRef owned)) (.box struckInner) :=
                ValidPartialValueWhenInitialized.box hownedSlotWrite htailValid
              simpa [howner] using hbox
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases struck with
      | ty struckTy | undef struckTy =>
          simp [Strike] at hstrike
      | box struckInner =>
          have hinnerStrike : Strike path (.ty inner) struckInner := by
            simpa [Strike] using hstrike
          cases htail with
          | nil hownedSlot _hownedValid =>
              cases hleafTy
              cases struckInner with
              | ty movedTy =>
                  simp [Strike] at hinnerStrike
              | box movedInner =>
                  simp [Strike] at hinnerStrike
              | undef movedTy =>
                  have hownedSlotWrite :
                      (store.update owned { ownedSlot with value := .undef }).slotAt
                        owned =
                        some { value := .undef, lifetime := ownedSlot.lifetime } := by
                    simp [ProgramStore.update]
                  have hbox :
                      ValidPartialValueWhenInitialized env
                        (store.update owned { ownedSlot with value := .undef })
                        (.value (owningRef owned)) (.box (.undef movedTy)) :=
                    ValidPartialValueWhenInitialized.box hownedSlotWrite
                      (ValidPartialValueWhenInitialized.undef (ty := movedTy))
                  simpa [howner] using hbox
          | boxFull htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpineWhenInitialized.boxFull htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf { leafSlot with value := .undef })
                    ownedSlot.value struckInner :=
                ih hleafTy (by simp) hinnerStrike
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf { leafSlot with value := .undef }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpineWhenInitialized.storage_slot htailSpine)
              have hbox :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf { leafSlot with value := .undef })
                    (.value (owningRef owned)) (.box struckInner) :=
                ValidPartialValueWhenInitialized.box hownedSlotWrite htailValid
              simpa [howner] using hbox

theorem valid_after_strike_nonempty {env : Env} {store : ProgramStore}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy struck : PartialTy} {path : Path} {ty : Ty} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf leafSlot (.ty ty) →
    path ≠ [] →
    Strike path rootTy struck →
    ValidPartialValueWhenInitialized env
      (store.update leaf { leafSlot with value := .undef })
      rootSlot.value struck := by
  intro hspine hnonempty hstrike
  exact valid_after_strike_nonempty_aux hspine rfl hnonempty hstrike

theorem valid_after_updateAtPath_nonempty {env writeEnv : Env}
    {store : ProgramStore}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {path : Path}
    {rhsTy : Ty} {value : Value} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf
      leafSlot leafTy →
    path ≠ [] →
    UpdateAtPath 0 env path rootTy rhsTy writeEnv updatedTy →
    ValidPartialValueWhenInitialized env
      (store.update leaf { leafSlot with value := .value value })
      (.value value) (.ty rhsTy) →
    ValidPartialValueWhenInitialized env
      (store.update leaf { leafSlot with value := .value value })
      rootSlot.value updatedTy := by
  intro hspine hnonempty hupdate hnewLeafValid
  induction hspine generalizing writeEnv updatedTy rhsTy value with
  | nil =>
      exact False.elim (hnonempty rfl)
  | @box storage owned leaf slot ownedSlot leafSlot spineInner leafTy path hslot howner
      htail ih =>
      cases hupdate with
      | @box _env₁ _env₂ _rank _path _inner updatedInner _ty hinnerUpdate =>
          cases htail with
          | nil hownedSlot _holdValid =>
              cases hinnerUpdate with
              | strong =>
                  have hownedSlotWrite :
                      (store.update owned { ownedSlot with value := .value value }).slotAt
                        owned =
                        some { value := .value value, lifetime := ownedSlot.lifetime } := by
                    simp [ProgramStore.update]
                  have hbox :
                      ValidPartialValueWhenInitialized env
                        (store.update owned { ownedSlot with value := .value value })
                        (.value (owningRef owned)) (.box (.ty rhsTy)) :=
                    ValidPartialValueWhenInitialized.box hownedSlotWrite hnewLeafValid
                  simpa [howner] using hbox
          | box htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpineWhenInitialized.box htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf
                      { leafSlot with value := .value value })
                    ownedSlot.value updatedInner := by
                exact ih (by simp) hinnerUpdate hnewLeafValid
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf
                    { leafSlot with value := .value value }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpineWhenInitialized.storage_slot htailSpine)
              have hbox :
                  ValidPartialValueWhenInitialized env
                  (store.update leaf
                    { leafSlot with value := .value value })
                  (.value (owningRef owned)) (.box updatedInner) := by
                exact ValidPartialValueWhenInitialized.box hownedSlotWrite htailValid
              simpa [howner] using hbox
          | boxFull htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpineWhenInitialized.boxFull htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf
                      { leafSlot with value := .value value })
                    ownedSlot.value updatedInner := by
                exact ih (by simp) hinnerUpdate hnewLeafValid
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf
                    { leafSlot with value := .value value }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpineWhenInitialized.storage_slot htailSpine)
              have hbox :
                  ValidPartialValueWhenInitialized env
                  (store.update leaf
                    { leafSlot with value := .value value })
                  (.value (owningRef owned)) (.box updatedInner) := by
                exact ValidPartialValueWhenInitialized.box hownedSlotWrite htailValid
              simpa [howner] using hbox
  | @boxFull storage owned leaf slot ownedSlot leafSlot spineInner leafTy path
      hslot howner htail ih =>
      cases hupdate with
      | @boxFull _env₁ _env₂ _rank _path _inner updatedInner _ty hinnerUpdate =>
          cases htail with
          | nil hownedSlot _holdValid =>
              cases hinnerUpdate with
              | strong =>
                  have hownedSlotWrite :
                      (store.update owned { ownedSlot with value := .value value }).slotAt
                        owned =
                        some { value := .value value, lifetime := ownedSlot.lifetime } := by
                    simp [ProgramStore.update]
                  have hbox :
                      ValidPartialValueWhenInitialized env
                        (store.update owned { ownedSlot with value := .value value })
                        (.value (owningRef owned)) (partialTyRebox (.ty rhsTy)) :=
                    StoreOwnerSpineWhenInitialized.valid_rebox hownedSlotWrite hnewLeafValid
                  simpa [howner] using hbox
          | boxFull htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpineWhenInitialized.boxFull htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf
                      { leafSlot with value := .value value })
                    ownedSlot.value updatedInner := by
                exact ih (by simp) hinnerUpdate hnewLeafValid
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf
                    { leafSlot with value := .value value }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpineWhenInitialized.storage_slot htailSpine)
              have hbox :
                  ValidPartialValueWhenInitialized env
                    (store.update leaf
                      { leafSlot with value := .value value })
                    (.value (owningRef owned)) (partialTyRebox updatedInner) :=
                StoreOwnerSpineWhenInitialized.valid_rebox hownedSlotWrite htailValid
              simpa [howner] using hbox

theorem updateAtPath_rank_zero_env_eq {env writeEnv : Env}
    {store : ProgramStore}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {path : Path}
    {rhsTy : Ty} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf
      leafSlot leafTy →
    UpdateAtPath 0 env path rootTy rhsTy writeEnv updatedTy →
    writeEnv = env := by
  intro hspine hupdate
  induction hspine generalizing writeEnv updatedTy rhsTy with
  | nil _hslot _hvalid =>
      cases hupdate with
      | strong =>
          rfl
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      cases hupdate with
      | box hinner =>
          exact ih hinner
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | boxFull hinner =>
          exact ih hinner

theorem updateAtPath_rank_zero_rhs_vars_subset_updated {env writeEnv : Env}
    {store : ProgramStore}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {path : Path}
    {rhsTy : Ty} :
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf
      leafSlot leafTy →
    UpdateAtPath 0 env path rootTy rhsTy writeEnv updatedTy →
    ∀ v, v ∈ PartialTy.vars (.ty rhsTy) → v ∈ PartialTy.vars updatedTy := by
  intro hspine hupdate
  induction hspine generalizing writeEnv updatedTy rhsTy with
  | nil _hslot _hvalid =>
      cases hupdate with
      | strong =>
          intro v hv
          simpa using hv
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | @box _env₁ _env₂ _rank _path _inner updatedInner _ty hinner =>
          intro v hv
          exact ih hinner v hv
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | @boxFull _env₁ _env₂ _rank _path _inner updatedInner _ty hinner =>
          intro v hv
          have hres := ih hinner v hv
          cases updatedInner <;>
            simpa [partialTyRebox, PartialTy.vars, Ty.vars] using hres

theorem stored_var_not_reaches_leaf_of_not_reaches_root {env : Env}
    {store : ProgramStore} {storedLifetime : Lifetime}
    {storedName : Name} {storedValue : PartialValue} {storedTy : PartialTy}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    store.slotAt (VariableProjection storedName) =
      some { value := storedValue, lifetime := storedLifetime } →
    ValidPartialValueWhenInitialized env store storedValue storedTy →
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf leafSlot leafTy →
    VariableProjection storedName ≠ root →
    (∀ reached,
      RuntimeFrame.OwnerReaches store storedValue storedTy reached →
      reached ≠ root) →
    ∀ reached,
      RuntimeFrame.OwnerReaches store storedValue storedTy reached →
      reached ≠ leaf := by
  intro hvalidStore hheap hstored hvalid hspine
  induction hspine with
  | nil _hslot _hvalidRoot =>
      intro _hstoredNeRoot hrootNoReach
      exact hrootNoReach
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      intro hstoredNeStorage hstorageNoReach
      have howns : ProgramStore.OwnsAt store owned storage :=
        StoreOwnerSpineWhenInitialized.ownsAt_of_box hslot howner htail
      have hownedNoReach :
          ∀ reached,
            RuntimeFrame.OwnerReaches store storedValue storedTy reached →
            reached ≠ owned := by
        intro reached hreach hreached
        subst reached
        rcases RuntimeFrame.reaches_owner_source_of_validPartialValue_core
            hvalid.skeleton hreach with hdirect | hsource
        · have hstoredOwns :
              ProgramStore.OwnsAt store owned (VariableProjection storedName) := by
            have hstoredValue :
                storedValue = .value (owningRef owned) :=
              eq_owningRef_of_mem_partialValueOwningLocations hdirect
            exact ⟨storedLifetime, by
              cases hstoredValue
              simpa [owningRef] using hstored⟩
          have hstorageEq : VariableProjection storedName = storage :=
            hvalidStore owned (VariableProjection storedName) storage
              hstoredOwns howns
          exact hstoredNeStorage hstorageEq
        · rcases hsource with ⟨sourceStorage, hsourceReach, hsourceOwns⟩
          have hstorageEq : sourceStorage = storage :=
            hvalidStore owned sourceStorage storage hsourceOwns howns
          exact hstorageNoReach sourceStorage hsourceReach hstorageEq
      have hstoredNeOwned : VariableProjection storedName ≠ owned := by
        intro hstoredEq
        have hownedHeap : ∃ address, owned = .heap address :=
          hheap owned ⟨storage, howns⟩
        rcases hownedHeap with ⟨address, hownedHeap⟩
        rw [← hstoredEq] at hownedHeap
        cases hownedHeap
      exact ih hstoredNeOwned hownedNoReach
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro hstoredNeStorage hstorageNoReach
      have howns : ProgramStore.OwnsAt store owned storage :=
        StoreOwnerSpineWhenInitialized.ownsAt_of_box hslot howner htail
      have hownedNoReach :
          ∀ reached,
            RuntimeFrame.OwnerReaches store storedValue storedTy reached →
            reached ≠ owned := by
        intro reached hreach hreached
        subst reached
        rcases RuntimeFrame.reaches_owner_source_of_validPartialValue_core
            hvalid.skeleton hreach with hdirect | hsource
        · have hstoredOwns :
              ProgramStore.OwnsAt store owned (VariableProjection storedName) := by
            have hstoredValue :
                storedValue = .value (owningRef owned) :=
              eq_owningRef_of_mem_partialValueOwningLocations hdirect
            exact ⟨storedLifetime, by
              cases hstoredValue
              simpa [owningRef] using hstored⟩
          have hstorageEq : VariableProjection storedName = storage :=
            hvalidStore owned (VariableProjection storedName) storage
              hstoredOwns howns
          exact hstoredNeStorage hstorageEq
        · rcases hsource with ⟨sourceStorage, hsourceReach, hsourceOwns⟩
          have hstorageEq : sourceStorage = storage :=
            hvalidStore owned sourceStorage storage hsourceOwns howns
          exact hstorageNoReach sourceStorage hsourceReach hstorageEq
      have hstoredNeOwned : VariableProjection storedName ≠ owned := by
        intro hstoredEq
        have hownedHeap : ∃ address, owned = .heap address :=
          hheap owned ⟨storage, howns⟩
        rcases hownedHeap with ⟨address, hownedHeap⟩
        rw [← hstoredEq] at hownedHeap
        cases hownedHeap
      exact ih hstoredNeOwned hownedNoReach

theorem not_reaches_leaf_of_not_reaches_root_of_owner_disjoint
    {store : ProgramStore} {env : Env}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path}
    {value : Value} {rhsTy : Ty} :
    ValidStore store →
    (∀ owned, owned ∈ valueOwningLocations value →
      ¬ ProgramStore.Owns store owned) →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf leafSlot leafTy →
    (∀ reached,
      RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
      reached ≠ root) →
    ∀ reached,
      RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
      reached ≠ leaf := by
  intro hvalidStore hownerDisjoint hvalidValue hspine
  induction hspine with
  | nil _hslot _hvalid =>
      intro hrootNoReach
      exact hrootNoReach
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      intro hstorageNoReach
      have howns : ProgramStore.OwnsAt store owned storage :=
        StoreOwnerSpineWhenInitialized.ownsAt_of_box hslot howner htail
      have hownedNoReach :
          ∀ reached,
            RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
            reached ≠ owned := by
        intro reached hreach hreached
        subst reached
        rcases RuntimeFrame.reaches_owner_source_of_validPartialValue_core
            hvalidValue.skeleton hreach with hdirect | hsource
        · exact hownerDisjoint owned
            (by simpa [partialValueOwningLocations] using hdirect)
            ⟨storage, howns⟩
        · rcases hsource with ⟨sourceStorage, hsourceReach, hsourceOwns⟩
          have hstorageEq : sourceStorage = storage :=
            hvalidStore owned sourceStorage storage hsourceOwns howns
          exact hstorageNoReach sourceStorage hsourceReach hstorageEq
      exact ih hownedNoReach
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro hstorageNoReach
      have howns : ProgramStore.OwnsAt store owned storage :=
        StoreOwnerSpineWhenInitialized.ownsAt_of_box hslot howner htail
      have hownedNoReach :
          ∀ reached,
            RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
            reached ≠ owned := by
        intro reached hreach hreached
        subst reached
        rcases RuntimeFrame.reaches_owner_source_of_validPartialValue_core
            hvalidValue.skeleton hreach with hdirect | hsource
        · exact hownerDisjoint owned
            (by simpa [partialValueOwningLocations] using hdirect)
            ⟨storage, howns⟩
        · rcases hsource with ⟨sourceStorage, hsourceReach, hsourceOwns⟩
          have hstorageEq : sourceStorage = storage :=
            hvalidStore owned sourceStorage storage hsourceOwns howns
          exact hstorageNoReach sourceStorage hsourceReach hstorageEq
      exact ih hownedNoReach

theorem not_reaches_leaf_of_not_reaches_root {env : Env}
    {store : ProgramStore}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy : PartialTy} {path : Path}
    {value : Value} {rhsTy : Ty} :
    ValidRuntimeState store (.val value) →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    StoreOwnerSpineWhenInitialized env store root rootSlot rootTy path leaf leafSlot leafTy →
    (∀ reached,
      RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
      reached ≠ root) →
    ∀ reached,
      RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
      reached ≠ leaf := by
  intro hvalidRuntime hvalidValue
  exact not_reaches_leaf_of_not_reaches_root_of_owner_disjoint
    (ValidRuntimeState.validStore hvalidRuntime)
    (by
      intro owned howned
      exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
        (by
          simpa [termOwningLocations, termValues] using howned))
    hvalidValue

end StoreOwnerSpineWhenInitialized

/-- Weak safe-abstraction preservation for direct variable moves.

Moving `x` overwrites the runtime slot with `undef` and strikes the environment
slot to `undef`.  Other variables keep their concrete slots, but their
abstractions are checked against the post-move environment so stale borrow
annotations can remain as protection tokens. -/
theorem safeAbstractionWhenInitialized_move_var_update {store : ProgramStore}
    {env : Env} {x : Name} {slot : EnvSlot} {ty : Ty} :
    SafeAbstraction store env →
    env.slotAt x = some slot →
    slot.ty = .ty ty →
    (∀ y envSlot value,
      y ≠ x →
      env.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := value, lifetime := envSlot.lifetime } →
      ValidPartialValueWhenInitialized
        (env.update x { slot with ty := .undef ty })
        (store.update (VariableProjection x)
          { value := .undef, lifetime := slot.lifetime })
        value envSlot.ty) →
    SafeAbstraction
      (store.update (VariableProjection x)
        { value := .undef, lifetime := slot.lifetime })
      (env.update x { slot with ty := .undef ty }) := by
  intro hsafe henv hty hpreserveOld
  constructor
  · intro y
    constructor
    · intro hstoreDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ slot with ty := .undef ty }, by simp [Env.update]⟩
      · rcases hstoreDomain with ⟨runtimeSlot, hruntimeSlot⟩
        have holdStore : ∃ oldSlot, store.slotAt (VariableProjection y) = some oldSlot := by
          rcases runtimeSlot with ⟨slotValue, slotLifetime⟩
          exact ⟨{ value := slotValue, lifetime := slotLifetime }, by
            simpa [ProgramStore.update, VariableProjection, hyx] using hruntimeSlot⟩
        rcases (hsafe.1 y).mp holdStore with ⟨envSlot, henvSlot⟩
        exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
    · intro henvDomain
      by_cases hyx : y = x
      · subst hyx
        exact ⟨{ value := .undef, lifetime := slot.lifetime }, by
          simp [ProgramStore.update, VariableProjection]⟩
      · rcases henvDomain with ⟨envSlot, henvSlot⟩
        have holdEnv : ∃ envSlot, env.slotAt y = some envSlot := by
          exact ⟨envSlot, by simpa [Env.update, hyx] using henvSlot⟩
        rcases (hsafe.1 y).mpr holdEnv with ⟨runtimeSlot, hruntimeSlot⟩
        exact ⟨runtimeSlot, by
          simpa [ProgramStore.update, VariableProjection, hyx] using hruntimeSlot⟩
  · intro y envSlot henvUpdated
    by_cases hyx : y = x
    · subst hyx
      have henvSlot :
          envSlot = { slot with ty := .undef ty } := by
        simpa [Env.update] using henvUpdated.symm
      subst henvSlot
      exact ⟨.undef, by
          simp [ProgramStore.update, VariableProjection],
        by
          simpa [hty] using
            (ValidPartialValueWhenInitialized.undef
              (env := env.update y { slot with ty := .undef ty })
              (store := store.update (VariableProjection y)
                { value := .undef, lifetime := slot.lifetime })
              (ty := ty))⟩
    · have holdEnv : env.slotAt y = some envSlot := by
        simpa [Env.update, hyx] using henvUpdated
      rcases hsafe.2 y envSlot holdEnv with ⟨value, hstore, _hvalid⟩
      exact ⟨value, by
          simpa [ProgramStore.update, VariableProjection, hyx] using hstore,
        hpreserveOld y envSlot value hyx holdEnv hstore⟩

/-- Direct variable `move` one-step preservation for the weakened runtime
abstraction. -/
theorem preservation_move_var_step_runtime_whenInitialized_of_frames
    {store store' : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {current lifetime valueLifetime : Lifetime}
    {x : Name} {value : Value} {ty : Ty} :
    WellFormedEnvWhenInitialized env₁ current →
    SafeAbstraction store env₁ →
    ValidRuntimeState store (.move (.var x)) →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    ¬ WriteProhibited env₁ (.var x) →
    TermTyping env₁ typing lifetime (.move (.var x)) ty env₂ →
    Step store lifetime (.move (.var x)) store' (.val value) →
    (∀ ℓ, RuntimeFrame.ReachesWhenInitialized env₁ store (.value value) (.ty ty) ℓ →
      ℓ ≠ VariableProjection x) →
    (∀ y envSlot oldValue,
      y ≠ x →
      env₁.slotAt y = some envSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := envSlot.lifetime } →
      ∀ ℓ, RuntimeFrame.ReachesWhenInitialized env₁ store oldValue envSlot.ty ℓ →
        ℓ ≠ VariableProjection x) →
    ValidRuntimeState store' (.val value) ∧
      SafeAbstraction store' env₂ ∧
      ValidPartialValueWhenInitialized env₂ store' (.value value) (.ty ty) := by
  intro _hwellFormed hsafe hvalidRuntime henvSlot hmove hnotWrite _htyping hstep
    hvalueFrame hotherFrames
  rcases hsafe.2 x { ty := .ty ty, lifetime := valueLifetime } henvSlot with
    ⟨sourceValue, hsourceSlot, hsourceValid⟩
  have hsourceSlotVar :
      store.slotAt (.var x) =
        some { value := sourceValue, lifetime := valueLifetime } := by
    simpa [VariableProjection] using hsourceSlot
  have hsourceValueEq : sourceValue = .value value := by
    cases hstep with
    | move hread _hwrite =>
        have hreadSource :
            store.read (.var x) =
              some { value := sourceValue, lifetime := valueLifetime } := by
          simp [ProgramStore.read, ProgramStore.loc, hsourceSlotVar]
        rw [hreadSource] at hread
        injection hread with hslotEq
        exact congrArg StoreSlot.value hslotEq
  have hstore' :
      store' =
        store.update (VariableProjection x)
          { value := .undef, lifetime := valueLifetime } := by
    cases hstep with
    | move hread hwrite =>
        have hreadEq := hread
        rw [show store.read (.var x) =
            some { value := sourceValue, lifetime := valueLifetime } by
              simp [ProgramStore.read, ProgramStore.loc, hsourceSlotVar]] at hreadEq
        injection hreadEq with hslotEq
        cases hslotEq
        simp [ProgramStore.write, ProgramStore.loc, hsourceSlotVar] at hwrite
        exact hwrite.symm
  have hvalidStoreValue :
      ValidPartialValueWhenInitialized env₁ store (.value value) (.ty ty) := by
    simpa [hsourceValueEq] using hsourceValid
  have hvalidValue : ValidPartialValueWhenInitialized env₂ store' (.value value) (.ty ty) := by
    rw [hstore']
    exact ValidPartialValueWhenInitialized.move_env hmove hnotWrite
      (RuntimeFrame.validPartialValueWhenInitialized_update_of_not_reachesWhenInitialized
        hvalidStoreValue hvalueFrame)
  have hsafeFinal : SafeAbstraction store' env₂ := by
    rw [hstore']
    rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv₂⟩
    have hmoveSlotEq :
        moveSlot = { ty := .ty ty, lifetime := valueLifetime } := by
      simp [LVal.base] at hmoveSlot
      rw [henvSlot] at hmoveSlot
      injection hmoveSlot with hmoveSlotEq
      exact hmoveSlotEq.symm
    subst hmoveSlotEq
    cases struck with
    | ty struckTy =>
        simp [Strike, LVal.path] at hstrike
    | box struckInner =>
        simp [Strike, LVal.path] at hstrike
    | undef struckTy =>
        simp [Strike, LVal.path] at hstrike
        subst hstrike
        subst henv₂
        refine safeAbstractionWhenInitialized_move_var_update hsafe henvSlot rfl ?_
        intro y envSlot oldValue hyx henvY hstoreY
        exact ValidPartialValueWhenInitialized.move_env
          (⟨{ ty := .ty ty, lifetime := valueLifetime }, .undef ty,
            henvSlot, by simp [Strike, LVal.path], rfl⟩ :
            EnvMove env₁ (.var x)
              (env₁.update x
                { ty := .undef ty, lifetime := valueLifetime }))
          hnotWrite
          (RuntimeFrame.validPartialValueWhenInitialized_update_of_not_reachesWhenInitialized
            (by
              rcases hsafe.2 y envSlot henvY with ⟨safeValue, hsafeSlot, hvalidOld⟩
              rw [hstoreY] at hsafeSlot
              injection hsafeSlot with hslotEq
              cases hslotEq
              exact hvalidOld)
            (hotherFrames y envSlot oldValue hyx henvY hstoreY))
  exact ⟨validRuntimeState_move_step hvalidRuntime hstep, hsafeFinal, hvalidValue⟩

/-- Direct variable `move` multistep preservation for the weakened runtime
abstraction, with frame facts derived from well-formedness. -/
theorem preservation_move_var_multistep_runtime_whenInitialized_of_wellFormed
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {x : Name} {finalValue : Value} {ty : Ty} :
    WellFormedEnvWhenInitialized env₁ lifetime →
    SafeAbstraction store env₁ →
    ValidRuntimeState store (.move (.var x)) →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    TermTyping env₁ typing lifetime (.move (.var x)) ty env₂ →
    MultiStep store lifetime (.move (.var x)) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hwellFormed hsafe hvalidRuntime henvSlot hmove htyping hmulti
  cases htyping with
  | move hLv hnotWrite _hmoveTyping =>
      exact preservation_runtime_multistep_of_step_to_value_whenInitialized
        (term := .move (.var x))
        (env := env₂)
        (ty := ty)
        (by simp [Terminal])
        (by
          intro _store' _term' hstep
          cases hstep with
          | move _hread _hwrite =>
              exact ⟨_, rfl⟩)
        (by
          intro store' value hstep
          cases hstep with
          | move hread hwrite =>
              exact preservation_move_var_step_runtime_whenInitialized_of_frames
                (typing := typing)
                hwellFormed hsafe hvalidRuntime
                henvSlot hmove hnotWrite
                (TermTyping.move (typing := typing) hLv hnotWrite hmove)
                (Step.move (lifetime := lifetime) hread hwrite)
                (by
                  intro location hreach
                  have hvalueHeap : ValueOwnerTargetsHeap value :=
                    TermOwnerTargetsHeap.value
                      (termOwnerTargetsHeap_value_of_store_read
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hread)
                  exact RuntimeFrame.value_reachesWhenInitialized_ne_var_of_varsProtected
                    hwellFormed hsafe
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hvalueHeap
                    (by
                      intro y hy
                      exact writeProhibited_of_lvalTyping_var_in_type_core
                        hLv (by simpa [PartialTy.vars] using hy))
                    hnotWrite hreach)
                (by
                  intro y envSlot oldValue hyx henvY hstoreY location hreach
                  have hvalueHeap : PartialValueOwnerTargetsHeap oldValue :=
                    partialValueOwnerTargetsHeap_of_slot
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreY
                  exact RuntimeFrame.reachesWhenInitialized_ne_var_of_varsProtected
                    hwellFormed hsafe
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hvalueHeap
                    (by
                      intro z hz
                      exact writeProhibited_of_envSlot_var_in_type henvY rfl hz)
                    hnotWrite hreach))
        hmulti

/-- Direct variable `move` multistep preservation with the frame facts derived
from well-formedness rather than supplied as an obligation. -/
theorem preservation_move_var_multistep_runtime_of_wellFormed
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {x : Name} {finalValue : Value} {ty : Ty} :
    WellFormedEnv env₁ lifetime →
    store ≈ₛ env₁ →
    ValidRuntimeState store (.move (.var x)) →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    TermTyping env₁ typing lifetime (.move (.var x)) ty env₂ →
    MultiStep store lifetime (.move (.var x)) finalStore (.val finalValue) →
    FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro hwellFormed hsafe hvalidRuntime henvSlot hmove htyping hmulti
  cases htyping with
  | move hLv _hnotWrite _hmoveTyping =>
      exact preservation_runtime_multistep_of_step_to_value_full
        (term := .move (.var x))
        (env := env₂)
        (ty := ty)
        (by simp [Terminal])
        (by
          intro _store' _term' hstep
          cases hstep with
          | move _hread _hwrite =>
              exact ⟨_, rfl⟩)
        (by
          intro store' value hstep
          cases hstep with
          | move hread hwrite =>
              exact preservation_move_var_step_runtime_of_frames
                (typing := typing)
                (WellFormedEnv.whenInitialized hwellFormed) hsafe hvalidRuntime henvSlot hmove
                (TermTyping.move (typing := typing) hLv _hnotWrite hmove)
                (Step.move (lifetime := lifetime) hread hwrite)
                (by
                  intro location hreach
                  have hvalueHeap : ValueOwnerTargetsHeap value :=
                    TermOwnerTargetsHeap.value
                      (termOwnerTargetsHeap_value_of_store_read
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hread)
                  exact RuntimeFrame.value_reaches_ne_var_of_varsProtected
                    hwellFormed hsafe
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hvalueHeap
                    (LValTyping.fullTyWellFormed hwellFormed hLv)
                    (by
                      intro y hy
                      exact writeProhibited_of_lvalTyping_var_in_type
                        hwellFormed hLv (by simpa [PartialTy.vars] using hy))
                    _hnotWrite hreach)
                (by
                  intro y envSlot oldValue hyx henvY hstoreY location hreach
                  have hvalueHeap : PartialValueOwnerTargetsHeap oldValue :=
                    partialValueOwnerTargetsHeap_of_slot
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreY
                  have hborrows :
                      PartialTyBorrowsWellFormedInSlot env₁ envSlot.lifetime envSlot.ty := by
                    intro mutable targets hcontains
                    exact hwellFormed.1 y envSlot mutable targets henvY
                      ⟨envSlot, henvY, hcontains⟩
                  exact RuntimeFrame.reaches_ne_var_of_varsProtected
                    hwellFormed hsafe
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hvalueHeap hborrows
                    (by
                      intro z hz
                      exact writeProhibited_of_envSlot_var_in_type henvY rfl hz)
                    _hnotWrite hreach))
        hmulti

/-- Owned-dereference `move` multistep preservation.

This is the non-empty owner-spine case of the paper's `R-Move` preservation
argument.  The source lvalue denotes a box slot, so moving `*source` writes
`undef` to the owned leaf while the environment move strikes the same leaf in the
base variable's partial type.
-/
theorem preservation_move_deref_box_multistep_runtime_of_wellFormed
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {source : LVal} {finalValue : Value} {ty : Ty} :
    WellFormedEnv env₁ lifetime →
    store ≈ₛ env₁ →
    ValidRuntimeState store (.move source.deref) →
    LValTyping env₁ source (.box (.ty ty)) valueLifetime →
    ¬ WriteProhibited env₁ source.deref →
    EnvMove env₁ source.deref env₂ →
    TermTyping env₁ typing lifetime (.move source.deref) ty env₂ →
    MultiStep store lifetime (.move source.deref) finalStore (.val finalValue) →
    FullTerminalStateSafe finalStore finalValue env₂ ty := by
  intro hwellFormed hsafe hvalidRuntime hsourceBox hnotWrite hmove htyping hmulti
  exact preservation_runtime_multistep_of_step_to_value_full
    (term := .move source.deref)
    (env := env₂)
    (ty := ty)
    (by simp [Terminal])
    (by
      intro _store' _term' hstep
      cases hstep with
      | move _hread _hwrite =>
          exact ⟨_, rfl⟩)
    (by
      intro store' value hstep
      cases hstep with
      | move hread hwrite =>
          rcases StoreOwnerSpine.of_lvalTyping_box hwellFormed hsafe hsourceBox with
            ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase, hrootSlot,
              hrootLifetime, hsourceLoc, hsourceSlot, hsourceSpine⟩
          have hsourceValid :
              ValidPartialValue store sourceSlot.value (.box (.ty ty)) :=
            StoreOwnerSpine.leaf_valid hsourceSpine
          rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv₂⟩
          have hmoveSlotEq : moveSlot = envSlot := by
            rw [show LVal.base source.deref = LVal.base source by rfl] at hmoveSlot
            rw [henvBase] at hmoveSlot
            exact (Option.some.inj hmoveSlot).symm
          subst hmoveSlotEq
          rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
          cases hsourceValid with
          | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
              have hlvLoc : store.loc source.deref = some ownerLocation := by
                simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
              have hreadConcrete :
                  store.read source.deref = some ownerSlot := by
                simp [ProgramStore.read, hlvLoc, hownedSlot]
              have hownerSlotValue :
                  ownerSlot.value = .value value := by
                rw [hreadConcrete] at hread
                exact congrArg StoreSlot.value (Option.some.inj hread)
              have hownedSlotValue :
                  store.slotAt ownerLocation =
                    some { value := .value value, lifetime := ownerSlot.lifetime } := by
                cases ownerSlot with
                | mk ownerValue ownerLifetime =>
                    cases hownerSlotValue
                    simpa using hownedSlot
              have hstore' :
                  store' =
                    store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef } := by
                have hwriteConcrete :
                    store.write source.deref PartialValue.undef =
                      some
                        (store.update ownerLocation
                          { ownerSlot with value := PartialValue.undef }) := by
                  simp [ProgramStore.write, hlvLoc, hownedSlot]
                rw [hwriteConcrete] at hwrite
                exact (Option.some.inj hwrite).symm
              subst hstore'
              have hspine :
                  StoreOwnerSpine store
                    (VariableProjection (LVal.base source.deref)) rootSlot moveSlot.ty
                    (LVal.path source.deref) ownerLocation
                    ownerSlot (.ty ty) := by
                have hsnoc :
                    StoreOwnerSpine store
                      (VariableProjection (LVal.base source)) rootSlot moveSlot.ty
                      (() :: LVal.path source) ownerLocation ownerSlot
                      (.ty ty) :=
                  StoreOwnerSpine.snoc_box hsourceSpine rfl rfl hownedSlot hinnerValid
                simpa [LVal.base, LVal.path_deref_cons] using hsnoc
              have hspineCons :
                  StoreOwnerSpine store
                    (VariableProjection (LVal.base source.deref)) rootSlot moveSlot.ty
                    (() :: LVal.path source) ownerLocation ownerSlot
                    (.ty ty) := by
                simpa [LVal.path_deref_cons] using hspine
              have hleafNeRoot : ownerLocation ≠ VariableProjection (LVal.base source.deref) :=
                StoreOwnerSpine.leaf_ne_storage_of_cons hspineCons
              have hrootNeLeaf :
                  VariableProjection (LVal.base source.deref) ≠ ownerLocation := by
                intro h
                exact hleafNeRoot h.symm
              have hpathNonempty : LVal.path source.deref ≠ [] := by
                simp [LVal.path_deref_cons]
              have hstrike' : Strike (LVal.path source.deref) moveSlot.ty struck := by
                simpa [LVal.base] using hstrike
              have hrootValidFinal :
                  ValidPartialValue
                    (store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef })
                    rootSlot.value struck :=
                StoreOwnerSpine.valid_after_strike_nonempty hspine hpathNonempty hstrike'
              have hrootSlotFinal :
                  (store.update ownerLocation
                    { ownerSlot with value := PartialValue.undef }).slotAt
                    (VariableProjection (LVal.base source.deref)) =
                  some { value := rootSlot.value, lifetime := moveSlot.lifetime } := by
                have hrootNeLeaf' :
                    VariableProjection (LVal.base source) ≠ ownerLocation := by
                  simpa [LVal.base] using hrootNeLeaf
                have hrootSlotMoveLifetime :
                    store.slotAt (VariableProjection (LVal.base source)) =
                    some { value := rootSlot.value, lifetime := moveSlot.lifetime } := by
                  cases rootSlot with
                  | mk rootValue rootLifetime =>
                      cases hrootLifetime
                      simpa using hrootSlot
                cases rootSlot with
                | mk rootValue rootLifetime =>
                    simpa [ProgramStore.update, hrootNeLeaf', LVal.base] using
                      hrootSlotMoveLifetime
              have hleafProtected :
                  ProtectedByBase store (LVal.base source.deref) ownerLocation :=
                StoreOwnerSpine.leaf_protected_by_base hspine rfl
              have hvalidValueStore : ValidValue store value ty :=
                by
                  show ValidPartialValue store (.value value) (.ty ty)
                  rw [← hownerSlotValue]
                  exact hinnerValid
              have hvalidValueFinal :
                  ValidValue
                    (store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef })
                    value ty :=
                RuntimeFrame.validValue_update_of_not_reaches hvalidValueStore
                  (by
                    intro reached hreach
                    exact movedValue_reaches_ne_protected_leaf
                      hwellFormed hsafe
                      (ValidRuntimeState.validStore hvalidRuntime)
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                      (LValTyping.box hsourceBox) hnotWrite hownedSlotValue
                      hleafProtected hvalidValueStore hreach)
              have hownsLeaf : ProgramStore.Owns store ownerLocation :=
                ProgramStore.OwnsTransitively.to_owns
                  (StoreOwnerSpine.ownsTransitively_of_cons hspineCons)
              have hleafHeap :
                  ∃ address, ownerLocation = Location.heap address :=
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                  ownerLocation hownsLeaf
              have hsafeFinal :
                  store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef } ≈ₛ
                    env₂ := by
                subst henv₂
                have hfull :
                    store.update ownerLocation
                        { ownerSlot with value := PartialValue.undef } ≈ₛ
                      env₁.update (LVal.base source.deref)
                        { ty := struck, lifetime := moveSlot.lifetime } := by
                  refine safeAbstraction_update_var_partial_of_preserved
                    (by simpa [LVal.base] using henvBase)
                    hrootSlotFinal hrootValidFinal rfl ?domainMove ?preserveMove
                  · intro y hyBase
                    have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
                      intro hvarLeaf
                      rcases hleafHeap with ⟨address, hheap⟩
                      rw [← hvarLeaf] at hheap
                      cases hheap
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
                      rcases hleafHeap with ⟨address, hheap⟩
                      rw [← hvarLeaf] at hheap
                      cases hheap
                    have hslotYFinal :
                        (store.update ownerLocation
                          { ownerSlot with value := PartialValue.undef }).slotAt
                          (VariableProjection y) =
                        some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
                      simpa [ProgramStore.update, hvarNeLeaf] using hslotY
                    have hborrowsOld :
                        PartialTyBorrowsWellFormedInSlot env₁ otherEnvSlot.lifetime
                          otherEnvSlot.ty := by
                      intro mutable targets hcontains
                      exact hwellFormed.1 y otherEnvSlot mutable targets henvY
                        ⟨otherEnvSlot, henvY, hcontains⟩
                    have hvalueHeapOld : PartialValueOwnerTargetsHeap oldValue :=
                      partialValueOwnerTargetsHeap_of_slot
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hslotY
                    have hvarYNeRoot :
                        VariableProjection y ≠ VariableProjection (LVal.base source.deref) := by
                      intro hvarEq
                      exact hyBase (by cases hvarEq; rfl)
                    have hrootNoOwnerReachOld :
                        ∀ reached,
                          RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty reached →
                          reached ≠ VariableProjection (LVal.base source.deref) := by
                      intro reached hreach
                      exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                        hvalueHeapOld hborrowsOld hreach
                    have holdOwnerNoReachLeaf :
                        ∀ reached,
                          RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty reached →
                          reached ≠ ownerLocation :=
                      StoreOwnerSpine.stored_var_not_reaches_leaf_of_not_reaches_root
                        (ValidRuntimeState.validStore hvalidRuntime)
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                        hslotY hborrowsOld hvalidOld hspine hvarYNeRoot
                        hrootNoOwnerReachOld
                    have hnotWriteRoot :
                        ¬ WriteProhibited env₁ (.var (LVal.base source.deref)) :=
                      not_writeProhibited_var_base hnotWrite
                    have holdNoReachLeaf :
                        ∀ reached,
                          RuntimeFrame.Reaches store oldValue otherEnvSlot.ty reached →
                          reached ≠ ownerLocation := by
                      intro reached hreach hreached
                      rcases RuntimeFrame.Reaches.owner_or_borrow hreach with howner | hdependency
                      · exact holdOwnerNoReachLeaf reached howner hreached
                      · exact
                          (borrowDependency_not_protectedByBase_of_varsProtectedIn
                            hwellFormed hsafe
                            (ValidRuntimeState.validStore hvalidRuntime)
                            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                            hborrowsOld
                            (by
                              intro z hz
                              exact writeProhibited_of_envSlot_var_in_type
                                henvY rfl hz)
                            hnotWriteRoot hnotWriteRoot hdependency)
                          (by simpa [hreached] using hleafProtected)
                    exact ⟨oldValue, hslotYFinal,
                      RuntimeFrame.validPartialValue_update_of_not_reaches
                        hvalidOld holdNoReachLeaf⟩
                exact hfull
              exact ⟨validRuntimeState_move_step hvalidRuntime
                  (Step.move (lifetime := lifetime) hread hwrite),
                hsafeFinal, hvalidValueFinal⟩)
                hmulti

/-- Stale-aware owned-dereference `move` multistep preservation. -/
theorem preservation_move_deref_box_multistep_runtime_whenInitialized_of_wellFormed
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {source : LVal} {finalValue : Value} {ty : Ty} :
    WellFormedEnvWhenInitialized env₁ lifetime →
    SafeAbstraction store env₁ →
    ValidRuntimeState store (.move source.deref) →
    LValTyping env₁ source (.box (.ty ty)) valueLifetime →
    ¬ WriteProhibited env₁ source.deref →
    EnvMove env₁ source.deref env₂ →
    TermTyping env₁ typing lifetime (.move source.deref) ty env₂ →
    MultiStep store lifetime (.move source.deref) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hwellFormed hsafe hvalidRuntime hsourceBox hnotWrite hmove htyping hmulti
  exact preservation_runtime_multistep_of_step_to_value_whenInitialized
    (term := .move source.deref)
    (env := env₂)
    (ty := ty)
    (by simp [Terminal])
    (by
      intro _store' _term' hstep
      cases hstep with
      | move _hread _hwrite =>
          exact ⟨_, rfl⟩)
    (by
      intro store' value hstep
      cases hstep with
      | move hread hwrite =>
          rcases StoreOwnerSpineWhenInitialized.of_lvalTyping_box
              hwellFormed hsafe hsourceBox with
            ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase, hrootSlot,
              hrootLifetime, hsourceLoc, hsourceSlot, hsourceSpine⟩
          have hsourceValid :
              ValidPartialValueWhenInitialized env₁ store
                sourceSlot.value (.box (.ty ty)) :=
            StoreOwnerSpineWhenInitialized.leaf_valid hsourceSpine
          have hmoveOriginal : EnvMove env₁ source.deref env₂ := hmove
          rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv₂⟩
          have hmoveSlotEq : moveSlot = envSlot := by
            rw [show LVal.base source.deref = LVal.base source by rfl] at hmoveSlot
            rw [henvBase] at hmoveSlot
            exact (Option.some.inj hmoveSlot).symm
          subst hmoveSlotEq
          rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
          cases hsourceValid with
          | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
              have hlvLoc : store.loc source.deref = some ownerLocation := by
                simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
              have hreadConcrete :
                  store.read source.deref = some ownerSlot := by
                simp [ProgramStore.read, hlvLoc, hownedSlot]
              have hownerSlotValue :
                  ownerSlot.value = .value value := by
                rw [hreadConcrete] at hread
                exact congrArg StoreSlot.value (Option.some.inj hread)
              have hownedSlotValue :
                  store.slotAt ownerLocation =
                    some { value := .value value, lifetime := ownerSlot.lifetime } := by
                cases ownerSlot with
                | mk ownerValue ownerLifetime =>
                    cases hownerSlotValue
                    simpa using hownedSlot
              have hstore' :
                  store' =
                    store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef } := by
                have hwriteConcrete :
                    store.write source.deref PartialValue.undef =
                      some
                        (store.update ownerLocation
                          { ownerSlot with value := PartialValue.undef }) := by
                  simp [ProgramStore.write, hlvLoc, hownedSlot]
                rw [hwriteConcrete] at hwrite
                exact (Option.some.inj hwrite).symm
              subst hstore'
              have hspine :
                  StoreOwnerSpineWhenInitialized env₁ store
                    (VariableProjection (LVal.base source.deref)) rootSlot moveSlot.ty
                    (LVal.path source.deref) ownerLocation
                    ownerSlot (.ty ty) := by
                have hsnoc :
                    StoreOwnerSpineWhenInitialized env₁ store
                      (VariableProjection (LVal.base source)) rootSlot moveSlot.ty
                      (() :: LVal.path source) ownerLocation ownerSlot
                      (.ty ty) :=
                  StoreOwnerSpineWhenInitialized.snoc_box hsourceSpine rfl rfl
                    hownedSlot hinnerValid
                simpa [LVal.base, LVal.path_deref_cons] using hsnoc
              have hspineCons :
                  StoreOwnerSpineWhenInitialized env₁ store
                    (VariableProjection (LVal.base source.deref)) rootSlot moveSlot.ty
                    (() :: LVal.path source) ownerLocation ownerSlot
                    (.ty ty) := by
                simpa [LVal.path_deref_cons] using hspine
              have hleafNeRoot : ownerLocation ≠ VariableProjection (LVal.base source.deref) :=
                StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons hspineCons
              have hrootNeLeaf :
                  VariableProjection (LVal.base source.deref) ≠ ownerLocation := by
                intro h
                exact hleafNeRoot h.symm
              have hpathNonempty : LVal.path source.deref ≠ [] := by
                simp [LVal.path_deref_cons]
              have hstrike' : Strike (LVal.path source.deref) moveSlot.ty struck := by
                simpa [LVal.base] using hstrike
              have hrootValidFinalEnv₁ :
                  ValidPartialValueWhenInitialized env₁
                    (store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef })
                    rootSlot.value struck :=
                StoreOwnerSpineWhenInitialized.valid_after_strike_nonempty
                  hspine hpathNonempty hstrike'
              have hrootValidFinal :
                  ValidPartialValueWhenInitialized env₂
                    (store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef })
                    rootSlot.value struck :=
                ValidPartialValueWhenInitialized.move_env
                  hmoveOriginal hnotWrite hrootValidFinalEnv₁
              have hrootSlotFinal :
                  (store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef }).slotAt
                      (VariableProjection (LVal.base source.deref)) =
                    some { value := rootSlot.value, lifetime := moveSlot.lifetime } := by
                have hrootNeLeaf' :
                    VariableProjection (LVal.base source) ≠ ownerLocation := by
                  simpa [LVal.base] using hrootNeLeaf
                have hrootSlotMoveLifetime :
                    store.slotAt (VariableProjection (LVal.base source)) =
                    some { value := rootSlot.value, lifetime := moveSlot.lifetime } := by
                  cases rootSlot with
                  | mk rootValue rootLifetime =>
                      cases hrootLifetime
                      simpa using hrootSlot
                cases rootSlot with
                | mk rootValue rootLifetime =>
                    simpa [ProgramStore.update, hrootNeLeaf', LVal.base] using
                      hrootSlotMoveLifetime
              have hleafProtected :
                  ProtectedByBase store (LVal.base source.deref) ownerLocation :=
                StoreOwnerSpineWhenInitialized.leaf_protected_by_base hspine rfl
              have hvalidValueStore :
                  ValidPartialValueWhenInitialized env₁ store (.value value) (.ty ty) := by
                show ValidPartialValueWhenInitialized env₁ store (.value value) (.ty ty)
                rw [← hownerSlotValue]
                exact hinnerValid
              have hvalidValueFinal :
                  ValidPartialValueWhenInitialized env₂
                    (store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef })
                    (.value value) (.ty ty) :=
                ValidPartialValueWhenInitialized.move_env hmoveOriginal hnotWrite
                  (RuntimeFrame.validPartialValueWhenInitialized_update_of_not_reachesWhenInitialized
                    hvalidValueStore
                    (by
                      intro reached hreach
                      exact movedValue_reaches_ne_protected_leaf_whenInitialized
                        hwellFormed hsafe
                        (ValidRuntimeState.validStore hvalidRuntime)
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                        (LValTyping.box hsourceBox) hnotWrite hownedSlotValue
                        hleafProtected hvalidValueStore hreach))
              have hownsLeaf : ProgramStore.Owns store ownerLocation :=
                ProgramStore.OwnsTransitively.to_owns
                  (StoreOwnerSpineWhenInitialized.ownsTransitively_of_cons hspineCons)
              have hleafHeap :
                  ∃ address, ownerLocation = Location.heap address :=
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                  ownerLocation hownsLeaf
              have hsafeFinal :
                  SafeAbstraction
                    (store.update ownerLocation
                      { ownerSlot with value := PartialValue.undef })
                    env₂ := by
                subst henv₂
                refine safeAbstractionWhenInitialized_update_var_partial_of_preserved
                  henvBase hrootSlotFinal hrootValidFinal rfl ?domainMove ?preserveMove
                · intro y hyBase
                  have hvarNeLeaf : VariableProjection y ≠ ownerLocation := by
                    intro hvarLeaf
                    rcases hleafHeap with ⟨address, hheap⟩
                    rw [← hvarLeaf] at hheap
                    cases hheap
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
                    rcases hleafHeap with ⟨address, hheap⟩
                    rw [← hvarLeaf] at hheap
                    cases hheap
                  have hslotYFinal :
                      (store.update ownerLocation
                        { ownerSlot with value := PartialValue.undef }).slotAt
                        (VariableProjection y) =
                      some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
                    simpa [ProgramStore.update, hvarNeLeaf] using hslotY
                  have hvalueHeapOld : PartialValueOwnerTargetsHeap oldValue :=
                    partialValueOwnerTargetsHeap_of_slot
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hslotY
                  have hvarYNeRoot :
                      VariableProjection y ≠ VariableProjection (LVal.base source.deref) := by
                    intro hvarEq
                    exact hyBase (by cases hvarEq; rfl)
                  have hrootNoOwnerReachOld :
                      ∀ reached,
                        RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty reached →
                        reached ≠ VariableProjection (LVal.base source.deref) := by
                    intro reached hreach
                    exact RuntimeFrame.ownerReaches_ne_var_of_heap
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                      hvalueHeapOld hreach
                  have holdOwnerNoReachLeaf :
                      ∀ reached,
                        RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty reached →
                        reached ≠ ownerLocation :=
                    StoreOwnerSpineWhenInitialized.stored_var_not_reaches_leaf_of_not_reaches_root
                      (ValidRuntimeState.validStore hvalidRuntime)
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                      hslotY hvalidOld hspine hvarYNeRoot hrootNoOwnerReachOld
                  have hnotWriteRoot :
                      ¬ WriteProhibited env₁ (.var (LVal.base source.deref)) :=
                    not_writeProhibited_var_base hnotWrite
                  have hborrowsOld :
                      PartialTyBorrowsWellFormedInSlotWhenInitialized env₁
                        otherEnvSlot.lifetime otherEnvSlot.ty := by
                    intro mutable targets hcontains
                    exact hwellFormed.1 y otherEnvSlot mutable targets henvY
                      ⟨otherEnvSlot, henvY, hcontains⟩
                  have holdNoReachLeaf :
                      ∀ reached,
                        RuntimeFrame.ReachesWhenInitialized env₁ store oldValue
                          otherEnvSlot.ty reached →
                        reached ≠ ownerLocation := by
                    intro reached hreach hreached
                    rcases RuntimeFrame.ReachesWhenInitialized.owner_or_borrow hreach with
                      howner | hdependency
                    · exact holdOwnerNoReachLeaf reached howner hreached
                    · have hnotProtected :
                          ¬ ProtectedByBase store (LVal.base source.deref) reached := by
                        intro hprotected
                        rcases borrowDependencyWhenInitialized_protected_writeProhibited_or_mem_vars
                            hwellFormed hsafe
                            (ValidRuntimeState.validStore hvalidRuntime)
                            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                            hborrowsOld hdependency hprotected with hwp | hmem
                        · exact hnotWriteRoot hwp
                        · exact hnotWriteRoot
                            (writeProhibited_of_envSlot_var_in_type henvY rfl hmem)
                      exact hnotProtected
                        (by simpa [hreached] using hleafProtected)
                  exact ⟨oldValue, hslotYFinal,
                    ValidPartialValueWhenInitialized.move_env
                      hmoveOriginal hnotWrite
                      (RuntimeFrame.validPartialValueWhenInitialized_update_of_not_reachesWhenInitialized
                        hvalidOld holdNoReachLeaf)⟩
              exact ⟨validRuntimeState_move_step hvalidRuntime
                  (Step.move (lifetime := lifetime) hread hwrite),
                hsafeFinal, hvalidValueFinal⟩)
    hmulti

/--
Dropping values that are no longer owned by any store slot preserves the same
safe abstraction.

This version is placed before direct-variable assignment preservation because
the lhs value may be a stale owner hidden behind `undef`; after the write, those
old owners are orphaned and the recursive drop is the operation that restores the
store invariants.
-/
theorem safeAbstraction_drops_of_orphaned_values_early
    {store store' : ProgramStore} {env : Env} {current : Lifetime}
    {values : List PartialValue} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ dropValue, dropValue ∈ values → PartialValueOwnerTargetsHeap dropValue) →
    (∀ owned, owned ∈ partialValuesOwningLocations values →
      ¬ ProgramStore.Owns store owned) →
    Drops store values store' →
    store' ≈ₛ env := by
  intro hwellFormed hsafe hvalidStore hheap hdropValuesHeap
    hdropOwnersOrphaned hdrops
  have hdropValuesUnprotected :
      ∀ dropValue, dropValue ∈ values →
        ∀ owned, owned ∈ partialValueOwningLocations dropValue →
          ∀ base, ¬ ProtectedByBase store base owned :=
    dropValues_unprotected_of_disjoint hheap hdropValuesHeap hdropOwnersOrphaned
  constructor
  · intro x
    constructor
    · intro hstoreDomain
      rcases hstoreDomain with ⟨slot, hslot⟩
      have hslotOld : store.slotAt (VariableProjection x) = some slot :=
        drops_slotAt_of_slotAt hdrops hslot
      exact (hsafe.1 x).mp ⟨slot, hslotOld⟩
    · intro henvDomain
      rcases (hsafe.1 x).mpr henvDomain with ⟨slot, hslot⟩
      have havoidVar : DropsAvoids store values (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hdropValuesHeap
      exact ⟨slot, dropsAvoids_slotAt_preserved hdrops havoidVar hslot⟩
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    have havoidVar : DropsAvoids store values (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hdropValuesHeap
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
            hdrops hvalidStore hstoreSlot hborrows hvalidOld havoidVar
            (by
              intro reached' hownerReach dropValue hdropMem howned
              have hownsReached : ProgramStore.Owns store reached' :=
                RuntimeFrame.store_owns_of_reaches_stored_validPartialValue
                  hstoreSlot hborrows hvalidOld hownerReach
              exact hdropOwnersOrphaned reached'
                (by
                  simp [partialValuesOwningLocations]
                  exact ⟨dropValue, hdropMem, howned⟩)
                hownsReached)
            (by
              intro dependency hdependency
              exact dropsAvoids_of_borrowDependency_unprotected_values
                hdrops hwellFormed hsafe hvalidStore hheap hdropValuesHeap
                hdropValuesUnprotected hborrows hdependency)
            hreach)
    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩

theorem safeAbstractionWhenInitialized_drops_of_orphaned_values_early
    {store store' : ProgramStore} {env : Env} {current : Lifetime}
    {values : List PartialValue} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ dropValue, dropValue ∈ values → PartialValueOwnerTargetsHeap dropValue) →
    (∀ owned, owned ∈ partialValuesOwningLocations values →
      ¬ ProgramStore.Owns store owned) →
    Drops store values store' →
    SafeAbstraction store' env := by
  intro hwellFormed hsafe hvalidStore hheap hdropValuesHeap
    hdropOwnersOrphaned hdrops
  have hdropValuesUnprotected :
      ∀ dropValue, dropValue ∈ values →
        ∀ owned, owned ∈ partialValueOwningLocations dropValue →
          ∀ base, ¬ ProtectedByBase store base owned :=
    dropValues_unprotected_of_disjoint hheap hdropValuesHeap hdropOwnersOrphaned
  constructor
  · intro x
    constructor
    · intro hstoreDomain
      rcases hstoreDomain with ⟨slot, hslot⟩
      have hslotOld : store.slotAt (VariableProjection x) = some slot :=
        drops_slotAt_of_slotAt hdrops hslot
      exact (hsafe.1 x).mp ⟨slot, hslotOld⟩
    · intro henvDomain
      rcases (hsafe.1 x).mpr henvDomain with ⟨slot, hslot⟩
      have havoidVar : DropsAvoids store values (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hdropValuesHeap
      exact ⟨slot, dropsAvoids_slotAt_preserved hdrops havoidVar hslot⟩
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    have havoidVar : DropsAvoids store values (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hdropValuesHeap
    have hstoreSlot' :
        store'.slotAt (VariableProjection x) =
          some { value := oldValue, lifetime := envSlot.lifetime } :=
      dropsAvoids_slotAt_preserved hdrops havoidVar hstoreSlot
    have hborrows :
        PartialTyBorrowsWellFormedInSlotWhenInitialized env
          envSlot.lifetime envSlot.ty := by
      intro mutable targets hcontains
      exact hwellFormed.1 x envSlot mutable targets henvSlot
        ⟨envSlot, henvSlot, hcontains⟩
    have hvalidOld' :
        ValidPartialValueWhenInitialized env store' oldValue envSlot.ty :=
      RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_reachesWhenInitialized
        hdrops hvalidOld
        (by
          intro reached hreach
          exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized
            hdrops hvalidStore hstoreSlot hvalidOld havoidVar
            (by
              intro reached' hownerReach dropValue hdropMem howned
              have hownsReached : ProgramStore.Owns store reached' :=
                RuntimeFrame.store_owns_of_reaches_stored_validPartialValueWhenInitialized
                  hstoreSlot hvalidOld hownerReach
              exact hdropOwnersOrphaned reached'
                (by
                  simp [partialValuesOwningLocations]
                  exact ⟨dropValue, hdropMem, howned⟩)
                hownsReached)
            (by
              intro dependency hdependency
              exact dropsAvoids_of_borrowDependencyWhenInitialized_unprotected_values
                hdrops hwellFormed hsafe hvalidStore hheap hdropValuesHeap
                hdropValuesUnprotected hborrows hdependency)
            hreach)
    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩

/-- The overwritten variable value's owners are orphaned immediately after the
write, before the recursive drop removes them. -/
theorem droppedValueOwnersOrphaned_assign_var
    {store writtenStore : ProgramStore} {x : Name}
    {oldSlot : StoreSlot} {value : Value} :
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    store.read (.var x) = some oldSlot →
    store.write (.var x) (.value value) = some writtenStore →
    ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
      ¬ ProgramStore.Owns writtenStore owned := by
  intro hvalidRuntime hread hwriteStore owned howned hownsWritten
  have hstoreX : store.slotAt (VariableProjection x) = some oldSlot := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  have hwriteEq :
      writtenStore =
        store.update (VariableProjection x)
          { oldSlot with value := .value value } :=
    write_var_eq hstoreX hwriteStore
  have hownedOld : owned ∈ partialValueOwningLocations oldSlot.value := by
    simpa [partialValuesOwningLocations] using howned
  have hstoreOwnsOld :
      ProgramStore.OwnsAt store owned (VariableProjection x) := by
    have holdValue :
        oldSlot.value = .value (owningRef owned) :=
      eq_owningRef_of_mem_partialValueOwningLocations hownedOld
    exact ⟨oldSlot.lifetime, by
      cases oldSlot with
      | mk oldValue oldLifetime =>
          cases holdValue
          simpa [owningRef] using hstoreX⟩
  rcases hownsWritten with ⟨storage, ownerLifetime, hownerSlotWritten⟩
  by_cases hstorage : storage = VariableProjection x
  · subst hstorage
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
      ⟨VariableProjection x, hstoreOwnsOld⟩
  · have hownerSlotStore :
        store.slotAt storage =
          some (StoreSlot.mk (.value (owningRef owned)) ownerLifetime) := by
      rw [hwriteEq] at hownerSlotWritten
      simpa [ProgramStore.update, hstorage] using hownerSlotWritten
    have hstorageEq :
        storage = VariableProjection x :=
      (ValidRuntimeState.validStore hvalidRuntime)
        owned storage (VariableProjection x)
        ⟨ownerLifetime, hownerSlotStore⟩ hstoreOwnsOld
    exact hstorage hstorageEq

/-- Shape-independent direct-variable assignment preservation.  The old slot may
own heap cells, including through a stale `undef` abstraction; the write orphans
those owners and the following drop removes them. -/
theorem preservation_assign_var_step_runtime_of_frames
    {store writtenStore store' : ProgramStore} {env env' : Env}
    {lifetime : Lifetime} {x : Name} {oldSlot : StoreSlot}
    {envSlot : EnvSlot} {value : Value} {ty : Ty} :
    WellFormedEnv env' lifetime →
    store ≈ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    ValidValue store value ty →
    store.read (.var x) = some oldSlot →
    store.write (.var x) (.value value) = some writtenStore →
    Drops writtenStore [oldSlot.value] store' →
    (∀ ℓ, RuntimeFrame.Reaches store (.value value) (.ty ty) ℓ →
      ℓ ≠ VariableProjection x) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ ℓ, RuntimeFrame.Reaches store oldValue otherEnvSlot.ty ℓ →
        ℓ ≠ VariableProjection x) →
    ValidRuntimeState store' (.val .unit) ∧ store' ≈ₛ env' ∧
      ValidValue store' .unit .unit := by
  intro hwellOut hsafe hvalidRuntime henvX hwriteEnv hvalidValue hread
    hwriteStore hdrops hvalueFrame hotherFrames
  have hstoreX : store.slotAt (VariableProjection x) = some oldSlot := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  have hslotLifetime : oldSlot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henvX with ⟨safeValue, hsafeSlot, _hvalidSafe⟩
    rw [hstoreX] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact congrArg StoreSlot.lifetime hslotEq
  have hwriteEq :
      writtenStore =
        store.update (VariableProjection x)
          { oldSlot with value := .value value } :=
    write_var_eq hstoreX hwriteStore
  have henv' :
      env' = env.update x { envSlot with ty := .ty ty } :=
    envWrite_zero_var_eq henvX hwriteEnv
  have hnewValidWrite :
      ValidPartialValue writtenStore (.value value) (.ty ty) := by
    rw [hwriteEq]
    exact RuntimeFrame.validValue_update_of_not_reaches hvalidValue hvalueFrame
  have hslotXWrite :
      writtenStore.slotAt (VariableProjection x) =
        some { value := .value value, lifetime := envSlot.lifetime } := by
    rw [hwriteEq]
    cases oldSlot with
    | mk oldValue oldLifetime =>
        cases hslotLifetime
        simp [ProgramStore.update]
  have hsafeWrite : writtenStore ≈ₛ env' := by
    rw [henv']
    refine safeAbstraction_update_var_of_preserved henvX hslotXWrite
      hnewValidWrite rfl ?domain ?preserve
    · intro y hyx
      constructor
      · intro hdomainStore
        rcases hdomainStore with ⟨slotY, hslotYWrite⟩
        have hslotYStore : store.slotAt (VariableProjection y) = some slotY := by
          rw [hwriteEq] at hslotYWrite
          simpa [ProgramStore.update, VariableProjection, hyx] using hslotYWrite
        exact (hsafe.1 y).mp ⟨slotY, hslotYStore⟩
      · intro hdomainEnv
        rcases (hsafe.1 y).mpr hdomainEnv with ⟨slotY, hslotY⟩
        exact ⟨slotY, by
          rw [hwriteEq]
          simpa [ProgramStore.update, VariableProjection, hyx] using hslotY⟩
    · intro y otherEnvSlot hyx henvY
      rcases hsafe.2 y otherEnvSlot henvY with
        ⟨oldValue, hslotY, hvalidOld⟩
      have hslotYWrite :
          writtenStore.slotAt (VariableProjection y) =
            some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
        rw [hwriteEq]
        simpa [ProgramStore.update, VariableProjection, hyx] using hslotY
      have hvalidOldWrite :
          ValidPartialValue writtenStore oldValue otherEnvSlot.ty := by
        rw [hwriteEq]
        exact RuntimeFrame.validPartialValue_update_of_not_reaches hvalidOld
          (hotherFrames y otherEnvSlot oldValue hyx henvY hslotY)
      exact ⟨oldValue, hslotYWrite, hvalidOldWrite⟩
  have hvalueHeap : ValueOwnerTargetsHeap value :=
    TermOwnerTargetsHeap.value
      (termOwnerTargetsHeap_assign_inner
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
  have hwriteOwnerHeap : StoreOwnerTargetsHeap writtenStore :=
    storeOwnerTargetsHeap_write
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
      (ValueOwnerTargetsHeap.partial hvalueHeap) hwriteStore
  have hnewDisjoint :
      ∀ owned, owned ∈ partialValueOwningLocations (.value value) →
        ¬ ProgramStore.Owns store owned := by
    intro owned hmem howns
    exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
      (by
        simpa [termOwningLocations, termValues, partialValueOwningLocations]
          using hmem)
      howns
  have hwriteValidStore : ValidStore writtenStore :=
    validStore_write_disjoint
      (ValidRuntimeState.validStore hvalidRuntime) hnewDisjoint hwriteStore
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [oldSlot.value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact partialValueOwnerTargetsHeap_of_slot
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreX
  have hdropOwnersOrphaned :
      ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
        ¬ ProgramStore.Owns writtenStore owned :=
    droppedValueOwnersOrphaned_assign_var hvalidRuntime hread hwriteStore
  have hallocatedWrite : StoreOwnersAllocated writtenStore :=
    storeOwnersAllocated_write_value_of_validValue
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
      hwriteStore
  have hrootWrite : HeapSlotsRootLifetime writtenStore :=
    heapSlotsRootLifetime_write
      (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
  have hallocatedFinal : StoreOwnersAllocated store' :=
    drops_storeOwnersAllocated_of_disjoint hdrops hwriteValidStore
      hallocatedWrite hdropOwnersOrphaned
  have hheapFinal : StoreOwnerTargetsHeap store' :=
    drops_storeOwnerTargetsHeap hdrops hwriteOwnerHeap
  have hrootFinal : HeapSlotsRootLifetime store' :=
    drops_heapSlotsRootLifetime hdrops hrootWrite
  have hsafeFinal : store' ≈ₛ env' :=
    safeAbstraction_drops_of_orphaned_values_early hwellOut hsafeWrite
      hwriteValidStore hwriteOwnerHeap hdropValuesHeap hdropOwnersOrphaned
      hdrops
  exact ⟨validRuntimeState_assign_step_of_postWriteDrop_invariants
      (lifetime := lifetime)
      hvalidRuntime hallocatedFinal hheapFinal hrootFinal hread hwriteStore
      hdrops,
    hsafeFinal, ValidPartialValue.unit⟩

theorem preservation_assign_var_step_runtime_whenInitialized_of_frames
    {store writtenStore store' : ProgramStore} {env env' : Env}
    {lifetime : Lifetime} {x : Name} {oldSlot : StoreSlot}
    {envSlot : EnvSlot} {value : Value} {ty : Ty} :
    WellFormedEnvWhenInitialized env' lifetime →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    env.slotAt x = some envSlot →
    EnvWrite 0 env (.var x) ty env' →
    ¬ WriteProhibited env' (.var x) →
    ValidPartialValueWhenInitialized env store (.value value) (.ty ty) →
    store.read (.var x) = some oldSlot →
    store.write (.var x) (.value value) = some writtenStore →
    Drops writtenStore [oldSlot.value] store' →
    (∀ ℓ, RuntimeFrame.ReachesWhenInitialized env store
      (.value value) (.ty ty) ℓ → ℓ ≠ VariableProjection x) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ ℓ, RuntimeFrame.ReachesWhenInitialized env store oldValue
        otherEnvSlot.ty ℓ → ℓ ≠ VariableProjection x) →
    ValidRuntimeState store' (.val .unit) ∧
      SafeAbstraction store' env' ∧
      ValidPartialValueWhenInitialized env' store' (.value .unit) (.ty .unit) := by
  intro hwellOut hsafe hvalidRuntime henvX hwriteEnv hnotWriteOut hvalidValue
    hread hwriteStore hdrops hvalueFrame hotherFrames
  have hstoreX : store.slotAt (VariableProjection x) = some oldSlot := by
    simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
  have hslotLifetime : oldSlot.lifetime = envSlot.lifetime := by
    rcases hsafe.2 x envSlot henvX with ⟨safeValue, hsafeSlot, _hvalidSafe⟩
    rw [hstoreX] at hsafeSlot
    injection hsafeSlot with hslotEq
    exact congrArg StoreSlot.lifetime hslotEq
  have hwriteEq :
      writtenStore =
        store.update (VariableProjection x)
          { oldSlot with value := .value value } :=
    write_var_eq hstoreX hwriteStore
  have henv' :
      env' = env.update x { envSlot with ty := .ty ty } :=
    envWrite_zero_var_eq henvX hwriteEnv
  have hnotWriteUpdated :
      ¬ WriteProhibited (env.update x { envSlot with ty := .ty ty })
        (.var x) := by
    simpa [henv'] using hnotWriteOut
  have hnewValidWriteOldEnv :
      ValidPartialValueWhenInitialized env writtenStore (.value value)
        (.ty ty) := by
    rw [hwriteEq]
    exact RuntimeFrame.validPartialValueWhenInitialized_update_of_not_reachesWhenInitialized
      hvalidValue hvalueFrame
  have hslotXPostUpdate :
      (env.update x { envSlot with ty := .ty ty }).slotAt x =
        some { envSlot with ty := .ty ty } := by
    simp [Env.update]
  have hvarsTyFresh : x ∉ PartialTy.vars (.ty ty) := by
    intro hmem
    exact hnotWriteUpdated
      (writeProhibited_of_envSlot_var_in_type hslotXPostUpdate rfl hmem)
  have hnewValidWrite :
      ValidPartialValueWhenInitialized env' writtenStore (.value value)
        (.ty ty) := by
    rw [henv']
    exact ValidPartialValueWhenInitialized.update_env_of_not_pathConflicts
      hnotWriteUpdated hvarsTyFresh hnewValidWriteOldEnv
  have hslotXWrite :
      writtenStore.slotAt (VariableProjection x) =
        some { value := .value value, lifetime := envSlot.lifetime } := by
    rw [hwriteEq]
    cases oldSlot with
    | mk oldValue oldLifetime =>
        cases hslotLifetime
        simp [ProgramStore.update]
  have hsafeWrite : SafeAbstraction writtenStore env' := by
    rw [henv']
    refine safeAbstractionWhenInitialized_update_var_partial_of_preserved
      henvX hslotXWrite (by simpa [henv'] using hnewValidWrite) rfl
      ?domain ?preserve
    · intro y hyx
      constructor
      · intro hdomainStore
        rcases hdomainStore with ⟨slotY, hslotYWrite⟩
        have hslotYStore : store.slotAt (VariableProjection y) = some slotY := by
          rw [hwriteEq] at hslotYWrite
          simpa [ProgramStore.update, VariableProjection, hyx] using hslotYWrite
        exact (hsafe.1 y).mp ⟨slotY, hslotYStore⟩
      · intro hdomainEnv
        rcases (hsafe.1 y).mpr hdomainEnv with ⟨slotY, hslotY⟩
        exact ⟨slotY, by
          rw [hwriteEq]
          simpa [ProgramStore.update, VariableProjection, hyx] using hslotY⟩
    · intro y otherEnvSlot hyx henvY
      rcases hsafe.2 y otherEnvSlot henvY with
        ⟨oldValue, hslotY, hvalidOld⟩
      have hslotYWrite :
          writtenStore.slotAt (VariableProjection y) =
            some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
        rw [hwriteEq]
        simpa [ProgramStore.update, VariableProjection, hyx] using hslotY
      have hvalidOldWriteOldEnv :
          ValidPartialValueWhenInitialized env writtenStore oldValue
            otherEnvSlot.ty := by
        rw [hwriteEq]
        exact RuntimeFrame.validPartialValueWhenInitialized_update_of_not_reachesWhenInitialized
          hvalidOld (hotherFrames y otherEnvSlot oldValue hyx henvY hslotY)
      have henvYPostUpdate :
          (env.update x { envSlot with ty := .ty ty }).slotAt y =
            some otherEnvSlot := by
        simpa [Env.update, hyx] using henvY
      have hvarsOtherFresh : x ∉ PartialTy.vars otherEnvSlot.ty := by
        intro hmem
        exact hnotWriteUpdated
          (writeProhibited_of_envSlot_var_in_type henvYPostUpdate rfl hmem)
      have hvalidOldWrite :
          ValidPartialValueWhenInitialized
            (env.update x { envSlot with ty := .ty ty }) writtenStore
            oldValue otherEnvSlot.ty :=
        ValidPartialValueWhenInitialized.update_env_of_not_pathConflicts
          hnotWriteUpdated hvarsOtherFresh hvalidOldWriteOldEnv
      exact ⟨oldValue, hslotYWrite, hvalidOldWrite⟩
  have hvalueHeap : ValueOwnerTargetsHeap value :=
    TermOwnerTargetsHeap.value
      (termOwnerTargetsHeap_assign_inner
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
  have hwriteOwnerHeap : StoreOwnerTargetsHeap writtenStore :=
    storeOwnerTargetsHeap_write
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
      (ValueOwnerTargetsHeap.partial hvalueHeap) hwriteStore
  have hnewDisjoint :
      ∀ owned, owned ∈ partialValueOwningLocations (.value value) →
        ¬ ProgramStore.Owns store owned := by
    intro owned hmem howns
    exact ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
      (by
        simpa [termOwningLocations, termValues, partialValueOwningLocations]
          using hmem)
      howns
  have hwriteValidStore : ValidStore writtenStore :=
    validStore_write_disjoint
      (ValidRuntimeState.validStore hvalidRuntime) hnewDisjoint hwriteStore
  have hdropValuesHeap :
      ∀ dropValue, dropValue ∈ [oldSlot.value] →
        PartialValueOwnerTargetsHeap dropValue := by
    intro dropValue hmem
    simp at hmem
    subst hmem
    exact partialValueOwnerTargetsHeap_of_slot
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreX
  have hdropOwnersOrphaned :
      ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
        ¬ ProgramStore.Owns writtenStore owned :=
    droppedValueOwnersOrphaned_assign_var hvalidRuntime hread hwriteStore
  have hallocatedWrite : StoreOwnersAllocated writtenStore :=
    storeOwnersAllocated_write_value_of_validValueWhenInitialized
      (ValidRuntimeState.storeOwnersAllocated hvalidRuntime) hvalidValue
      hwriteStore
  have hrootWrite : HeapSlotsRootLifetime writtenStore :=
    heapSlotsRootLifetime_write
      (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime) hwriteStore
  have hallocatedFinal : StoreOwnersAllocated store' :=
    drops_storeOwnersAllocated_of_disjoint hdrops hwriteValidStore
      hallocatedWrite hdropOwnersOrphaned
  have hheapFinal : StoreOwnerTargetsHeap store' :=
    drops_storeOwnerTargetsHeap hdrops hwriteOwnerHeap
  have hrootFinal : HeapSlotsRootLifetime store' :=
    drops_heapSlotsRootLifetime hdrops hrootWrite
  have hsafeFinal : SafeAbstraction store' env' :=
    safeAbstractionWhenInitialized_drops_of_orphaned_values_early hwellOut
      hsafeWrite hwriteValidStore hwriteOwnerHeap hdropValuesHeap
      hdropOwnersOrphaned hdrops
  exact ⟨validRuntimeState_assign_step_of_postWriteDrop_invariants
      (lifetime := lifetime)
      hvalidRuntime hallocatedFinal hheapFinal hrootFinal hread hwriteStore
      hdrops,
    hsafeFinal, ValidPartialValueWhenInitialized.unit⟩

theorem preservation_assign_var_step_runtime_whenInitialized_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {x : Name}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnvWhenInitialized env lifetime →
    SafeAbstraction store env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    LValTyping env (.var x) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.var x) rhsTy env' →
    ¬ WriteProhibited env' (.var x) →
    WellFormedEnvWhenInitialized env' lifetime →
    ValidPartialValueWhenInitialized env store (.value value) (.ty rhsTy) →
    Step store lifetime (.assign (.var x) (.val value)) store' (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwellFormed hsafe hvalidRuntime hLhs _hshape hwellTy hwrite hnotWrite
    hwellOut hvalidValue hstep
  rcases LValTyping.var_inv hLhs with ⟨envSlot, henvSlot, _htyEq, _hlifetimeEq⟩
  cases hstep with
  | assign hread hwriteStoreWritten hdrops =>
      have henv'Eq : env' = env.update x { envSlot with ty := .ty rhsTy } :=
        envWrite_zero_var_eq henvSlot hwrite
      have hnotWriteUpdated :
          ¬ WriteProhibited (env.update x { envSlot with ty := .ty rhsTy })
            (.var x) := by
        rw [← henv'Eq]
        exact hnotWrite
      have hnoOther :
          ∀ y, y ≠ x → ¬ WriteProhibitedVia env y (.var x) :=
        not_writeProhibitedVia_of_update_self hnotWriteUpdated
      have hslotXPost :
          env'.slotAt x = some { envSlot with ty := .ty rhsTy } := by
        rw [henv'Eq]
        simp [Env.update]
      have hvalueHeap : ValueOwnerTargetsHeap value :=
        TermOwnerTargetsHeap.value
          (termOwnerTargetsHeap_assign_inner
            (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
      have hvalueNoReach :
          ∀ location,
            RuntimeFrame.ReachesWhenInitialized env store
              (.value value) (.ty rhsTy) location →
            location ≠ VariableProjection x := by
        intro location hreach
        exact RuntimeFrame.value_reachesWhenInitialized_ne_var_of_varsProtectedIn
          hwellFormed hsafe
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hvalueHeap hwellTy.whenInitialized
          (by
            intro y hy
            exact writeProhibited_of_envSlot_var_in_type hslotXPost rfl
              (by simpa [PartialTy.vars] using hy))
          hnoOther hnotWrite hreach
      have hotherNoReach :
          ∀ y otherEnvSlot oldValue,
            y ≠ x →
            env.slotAt y = some otherEnvSlot →
            store.slotAt (VariableProjection y) =
              some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
            ∀ location,
              RuntimeFrame.ReachesWhenInitialized env store oldValue
                otherEnvSlot.ty location →
              location ≠ VariableProjection x := by
        intro y otherEnvSlot oldValue hyx henvY hstoreY location hreach
        have hvalueHeapOld : PartialValueOwnerTargetsHeap oldValue :=
          partialValueOwnerTargetsHeap_of_slot
            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreY
        have hborrows :
            PartialTyBorrowsWellFormedInSlotWhenInitialized env
              otherEnvSlot.lifetime otherEnvSlot.ty := by
          intro mutable targets hcontains
          exact hwellFormed.1 y otherEnvSlot mutable targets henvY
            ⟨otherEnvSlot, henvY, hcontains⟩
        have henvYPost : env'.slotAt y = some otherEnvSlot := by
          rw [henv'Eq]
          simpa [Env.update, hyx] using henvY
        exact RuntimeFrame.reachesWhenInitialized_ne_var_of_varsProtectedIn
          hwellFormed hsafe
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hvalueHeapOld hborrows
          (by
            intro z hz
            exact writeProhibited_of_envSlot_var_in_type henvYPost rfl hz)
          hnoOther hnotWrite hreach
      exact preservation_assign_var_step_runtime_whenInitialized_of_frames
        (lifetime := lifetime)
        hwellOut hsafe hvalidRuntime henvSlot hwrite hnotWrite hvalidValue
        hread hwriteStoreWritten hdrops
        hvalueNoReach hotherNoReach

/-- Direct variable `assign` redex preservation with the frame facts derived from
well-formedness rather than supplied as an obligation. -/
theorem preservation_assign_var_step_runtime_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {x : Name}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    store ≈ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    LValTyping env (.var x) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.var x) rhsTy env' →
    ¬ WriteProhibited env' (.var x) →
    WellFormedEnv env' lifetime →
    ValidValue store value rhsTy →
    Step store lifetime (.assign (.var x) (.val value)) store' (.val finalValue) →
    FullTerminalStateSafe store' finalValue env' .unit := by
  intro hwellFormed hsafe hvalidRuntime hLhs _hshape hwellTy hwrite hnotWrite
    hwellOut hvalidValue hstep
  rcases LValTyping.var_inv hLhs with ⟨envSlot, henvSlot, htyEq, _hlifetimeEq⟩
  cases hstep with
  | assign hread hwriteStoreWritten hdrops =>
      have henv'Eq : env' = env.update x { envSlot with ty := .ty rhsTy } :=
        envWrite_zero_var_eq henvSlot hwrite
      have hnotWriteUpdated :
          ¬ WriteProhibited (env.update x { envSlot with ty := .ty rhsTy })
            (.var x) := by
        rw [← henv'Eq]
        exact hnotWrite
      have hnoOther :
          ∀ y, y ≠ x → ¬ WriteProhibitedVia env y (.var x) :=
        not_writeProhibitedVia_of_update_self hnotWriteUpdated
      have hslotXPost :
          env'.slotAt x = some { envSlot with ty := .ty rhsTy } := by
        rw [henv'Eq]
        simp [Env.update]
      have hvalueHeap : ValueOwnerTargetsHeap value :=
        TermOwnerTargetsHeap.value
          (termOwnerTargetsHeap_assign_inner
            (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
      have hvalueNoReach :
          ∀ location,
            RuntimeFrame.Reaches store (.value value) (.ty rhsTy) location →
            location ≠ VariableProjection x := by
        intro location hreach
        exact RuntimeFrame.reaches_ne_var_of_varsProtectedIn
          hwellFormed hsafe
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          (ValueOwnerTargetsHeap.partial hvalueHeap)
          (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)
          (by
            intro y hy
            exact writeProhibited_of_envSlot_var_in_type hslotXPost rfl
              (by simpa [PartialTy.vars] using hy))
          hnoOther hnotWrite hreach
      have hotherNoReach :
          ∀ y otherEnvSlot oldValue,
            y ≠ x →
            env.slotAt y = some otherEnvSlot →
            store.slotAt (VariableProjection y) =
              some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
            ∀ location,
              RuntimeFrame.Reaches store oldValue otherEnvSlot.ty location →
              location ≠ VariableProjection x := by
        intro y otherEnvSlot oldValue hyx henvY hstoreY location hreach
        have hvalueHeapOld : PartialValueOwnerTargetsHeap oldValue :=
          partialValueOwnerTargetsHeap_of_slot
            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreY
        have hborrows :
            PartialTyBorrowsWellFormedInSlot env otherEnvSlot.lifetime
              otherEnvSlot.ty := by
          intro mutable targets hcontains
          exact hwellFormed.1 y otherEnvSlot mutable targets henvY
            ⟨otherEnvSlot, henvY, hcontains⟩
        have henvYPost : env'.slotAt y = some otherEnvSlot := by
          rw [henv'Eq]
          simpa [Env.update, hyx] using henvY
        exact RuntimeFrame.reaches_ne_var_of_varsProtectedIn
          hwellFormed hsafe
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hvalueHeapOld hborrows
          (by
            intro z hz
            exact writeProhibited_of_envSlot_var_in_type henvYPost rfl hz)
          hnoOther hnotWrite hreach
      exact preservation_assign_var_step_runtime_of_frames
        (lifetime := lifetime)
        hwellOut hsafe hvalidRuntime henvSlot hwrite hvalidValue
        hread hwriteStoreWritten hdrops hvalueNoReach hotherNoReach

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
      exact ⟨_, _, location, hread, hwrite, hdrops, hloc, hslot, hwriteEq, rfl⟩

/--
Selected-target form of Lemma 9.3's borrowed-reference case.  The existing
`location_borrow_selected` lemma is enough for value validity; assignment
preservation also needs the concrete selected target branch.
-/
theorem location_borrow_selected_target {store : ProgramStore} {env : Env}
    {lv : LVal} {mutable : Bool} {targets : List LVal}
    {targetTy : PartialTy} {targetLifetime : Lifetime} :
    LValLocationAbstraction store lv (.ty (.borrow mutable targets)) →
    LValTargetsTyping env targets targetTy targetLifetime →
    (∀ target ty lifetime,
      LValTyping env target (.ty ty) lifetime →
      LValLocationAbstraction store target (.ty ty)) →
    ∃ target selectedTy selectedLifetime,
      target ∈ targets ∧
      LValTyping env target (.ty selectedTy) selectedLifetime ∧
      LValLocationAbstraction store (.deref lv) (.ty selectedTy) ∧
      PartialTyStrengthens (.ty selectedTy) targetTy := by
  intro hborrowLocation htargets hresolve
  rcases hborrowLocation with
    ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hvalidBorrow with
  | borrow hmem htargetLocFromBorrow =>
      rcases lvalTargetsTyping_member_strengthens htargets _ hmem with
        ⟨selectedTy, selectedLifetime, hselectedTyping,
          hselectedStrengthens⟩
      rcases hresolve _ selectedTy selectedLifetime hselectedTyping with
        ⟨selectedLocation, selectedSlot, hselectedLoc, hselectedSlot,
          hselectedValid⟩
      exact ⟨_, selectedTy, selectedLifetime, hmem, hselectedTyping,
        ⟨selectedLocation, selectedSlot, by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            simpa [hselectedLoc] using htargetLocFromBorrow.symm,
          hselectedSlot, hselectedValid⟩,
        hselectedStrengthens⟩

theorem location_borrow_selected_target_whenInitialized
    {store : ProgramStore} {env : Env}
    {lv : LVal} {mutable : Bool} {targets : List LVal}
    {targetTy : PartialTy} {targetLifetime : Lifetime} :
    LValLocationAbstractionWhenInitialized env store lv
      (.ty (.borrow mutable targets)) →
    LValTargetsTyping env targets targetTy targetLifetime →
    (∀ target ty lifetime,
      LValTyping env target (.ty ty) lifetime →
      LValLocationAbstractionWhenInitialized env store target (.ty ty)) →
    ∃ target selectedTy selectedLifetime,
      target ∈ targets ∧
      LValTyping env target (.ty selectedTy) selectedLifetime ∧
      LValLocationAbstractionWhenInitialized env store (.deref lv)
        (.ty selectedTy) ∧
      PartialTyStrengthens (.ty selectedTy) targetTy := by
  intro hborrowLocation htargets hresolve
  rcases hborrowLocation with
    ⟨source, sourceSlot, hsourceLoc, hsourceSlot, hvalidBorrow⟩
  rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
  cases hvalidBorrow with
  | borrowLive _hinitialized hmem htargetLocFromBorrow =>
      rcases lvalTargetsTyping_member_strengthens htargets _ hmem with
        ⟨selectedTy, selectedLifetime, hselectedTyping,
          hselectedStrengthens⟩
      rcases hresolve _ selectedTy selectedLifetime hselectedTyping with
        ⟨selectedLocation, selectedSlot, hselectedLoc, hselectedSlot,
          hselectedValid⟩
      exact ⟨_, selectedTy, selectedLifetime, hmem, hselectedTyping,
        ⟨selectedLocation, selectedSlot, by
            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
            simpa [hselectedLoc] using htargetLocFromBorrow.symm,
          hselectedSlot, hselectedValid⟩,
        hselectedStrengthens⟩
  | borrowStale hstale =>
      have hinitialized : BorrowTargetsInitialized env targets := by
        intro target hmem
        rcases lvalTargetsTyping_member_strengthens htargets target hmem with
          ⟨selectedTy, selectedLifetime, hselectedTyping, _hstrength⟩
        exact ⟨selectedTy, selectedLifetime, hselectedTyping⟩
      exact False.elim (hstale hinitialized)

/--
Dropping values that are not owned anywhere in the store preserves safe
abstraction for the same environment.

This is the post-write cleanup part of assignment preservation.  Domain
agreement is preserved because heap-only owner targets cannot delete variable
slots; value validity is preserved because every owner reached by an
environment value is disjoint from the dropped owners, and every borrow
dependency is protected from the orphaned drop set.
-/
theorem safeAbstraction_drops_of_orphaned_values
    {store store' : ProgramStore} {env : Env} {current : Lifetime}
    {values : List PartialValue} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ dropValue, dropValue ∈ values → PartialValueOwnerTargetsHeap dropValue) →
    (∀ owned, owned ∈ partialValuesOwningLocations values →
      ¬ ProgramStore.Owns store owned) →
    Drops store values store' →
    store' ≈ₛ env := by
  intro hwellFormed hsafe hvalidStore hheap hdropValuesHeap
    hdropOwnersOrphaned hdrops
  have hdropValuesUnprotected :
      ∀ dropValue, dropValue ∈ values →
        ∀ owned, owned ∈ partialValueOwningLocations dropValue →
          ∀ base, ¬ ProtectedByBase store base owned :=
    dropValues_unprotected_of_disjoint hheap hdropValuesHeap hdropOwnersOrphaned
  constructor
  · intro x
    constructor
    · intro hstoreDomain
      rcases hstoreDomain with ⟨slot, hslot⟩
      have hslotOld : store.slotAt (VariableProjection x) = some slot :=
        drops_slotAt_of_slotAt hdrops hslot
      exact (hsafe.1 x).mp ⟨slot, hslotOld⟩
    · intro henvDomain
      rcases (hsafe.1 x).mpr henvDomain with ⟨slot, hslot⟩
      have havoidVar : DropsAvoids store values (VariableProjection x) :=
        dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hdropValuesHeap
      exact ⟨slot, dropsAvoids_slotAt_preserved hdrops havoidVar hslot⟩
  · intro x envSlot henvSlot
    rcases hsafe.2 x envSlot henvSlot with
      ⟨oldValue, hstoreSlot, hvalidOld⟩
    have havoidVar : DropsAvoids store values (VariableProjection x) :=
      dropsAvoids_var_of_ownerTargetsHeap hdrops hheap hdropValuesHeap
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
            hdrops hvalidStore hstoreSlot hborrows hvalidOld havoidVar
            (by
              intro reached' hownerReach dropValue hdropMem howned
              have hownsReached : ProgramStore.Owns store reached' :=
                RuntimeFrame.store_owns_of_reaches_stored_validPartialValue
                  hstoreSlot hborrows hvalidOld hownerReach
              exact hdropOwnersOrphaned reached'
                (by
                  simp [partialValuesOwningLocations]
                  exact ⟨dropValue, hdropMem, howned⟩)
                hownsReached)
            (by
              intro dependency hdependency
              exact dropsAvoids_of_borrowDependency_unprotected_values
                hdrops hwellFormed hsafe hvalidStore hheap hdropValuesHeap
                hdropValuesUnprotected hborrows hdependency)
            hreach)
    exact ⟨oldValue, hstoreSlot', hvalidOld'⟩

/--
GRAPH LEMMA B — the overwritten value's owners are orphaned by the write.

After `value` is written through `*source`, the locations owned by the old
contents `oldSlot.value` are no longer owned by any slot of `writtenStore`: by
single-owner uniqueness (`ValidStore`) their unique owner *was* the slot at
`lhsLocation`, which the write has just overwritten.  This is the ownership-graph
fact that lets the subsequent `Drops` re-establish `StoreOwnersAllocated` via
`drops_storeOwnersAllocated_of_disjoint`.
-/
theorem droppedValueOwnersOrphaned_assign_deref
    {store writtenStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {source : LVal} {lhsLocation : Location} {oldSlot : StoreSlot}
    {oldTy : PartialTy} {value : Value} :
    WellFormedEnv env lifetime →
    store ≈ₛ env →
    ValidRuntimeState store (.assign (.deref source) (.val value)) →
    store.loc (.deref source) = some lhsLocation →
    store.slotAt lhsLocation = some oldSlot →
    ValidPartialValue store oldSlot.value oldTy →
    store.write (.deref source) (.value value) = some writtenStore →
    ∀ owned, owned ∈ partialValuesOwningLocations [oldSlot.value] →
      ¬ ProgramStore.Owns writtenStore owned := by
  intro _hwellFormed _hsafe hvalidRuntime hlhsLoc hlhsSlot _holdSlotValid
    hwriteStore owned howned hownsWritten
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

theorem safeAbstraction_update_owner_spine_of_frames
    {store store' : ProgramStore} {env writeEnv : Env}
    {current : Lifetime} {x : Name}
    {envSlot : EnvSlot} {rootSlot leafSlot : StoreSlot}
    {leaf : Location} {leafTy updatedTy : PartialTy}
    {path : Path} {rhsTy : Ty} {value : Value} :
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env.slotAt x = some envSlot →
    store.slotAt (VariableProjection x) = some rootSlot →
    rootSlot.lifetime = envSlot.lifetime →
    StoreOwnerSpine store (VariableProjection x) rootSlot envSlot.ty
      path leaf leafSlot leafTy →
    path ≠ [] →
    UpdateAtPath 0 env path envSlot.ty rhsTy writeEnv updatedTy →
    store' = store.update leaf { leafSlot with value := .value value } →
    ValidPartialValue store' (.value value) (.ty rhsTy) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.Reaches store oldValue otherEnvSlot.ty location →
        location ≠ leaf) →
    store' ≈ₛ
      (writeEnv.update x { envSlot with ty := updatedTy }) := by
  intro hwellFormed hsafe hvalidStore hheap henvSlot hrootSlot hrootLifetime
    hspine hpathNonempty hupdate hstore' hnewValid hotherNoReachLeaf
  have hwriteEnvEq : writeEnv = env :=
    StoreOwnerSpine.updateAtPath_rank_zero_env_eq hspine hupdate
  subst hwriteEnvEq
  subst hstore'
  have hrootValidFinal :
      ValidPartialValue
        (store.update leaf { leafSlot with value := .value value })
        rootSlot.value updatedTy :=
    StoreOwnerSpine.valid_after_updateAtPath_nonempty hspine hpathNonempty
      hupdate hnewValid
  have hpathCons : ∃ tail, path = () :: tail := by
    cases path with
    | nil => exact False.elim (hpathNonempty rfl)
    | cons head tail =>
        cases head
        exact ⟨tail, rfl⟩
  have hleafNeRoot : leaf ≠ VariableProjection x := by
    rcases hpathCons with ⟨tail, hpathEq⟩
    have hspineCons :
        StoreOwnerSpine store (VariableProjection x) rootSlot envSlot.ty
          (() :: tail) leaf leafSlot leafTy := by
      simpa [hpathEq] using hspine
    exact StoreOwnerSpine.leaf_ne_storage_of_cons hspineCons
  have hrootNeLeaf : VariableProjection x ≠ leaf := by
    intro h
    exact hleafNeRoot h.symm
  have hrootSlotFinal :
      (store.update leaf { leafSlot with value := .value value }).slotAt
        (VariableProjection x) =
      some { value := rootSlot.value, lifetime := envSlot.lifetime } := by
    cases rootSlot with
    | mk rootValue rootLifetime =>
        cases hrootLifetime
        simpa [ProgramStore.update, hrootNeLeaf] using hrootSlot
  have hleafHeap : ∃ address, leaf = .heap address := by
    rcases hpathCons with ⟨tail, hpathEq⟩
    have hspineCons :
        StoreOwnerSpine store (VariableProjection x) rootSlot envSlot.ty
          (() :: tail) leaf leafSlot leafTy := by
      simpa [hpathEq] using hspine
    have hownsLeaf : ProgramStore.Owns store leaf :=
      ProgramStore.OwnsTransitively.to_owns
        (StoreOwnerSpine.ownsTransitively_of_cons hspineCons)
    exact hheap leaf hownsLeaf
  refine safeAbstraction_update_var_partial_of_preserved
    henvSlot hrootSlotFinal hrootValidFinal rfl ?domainOther ?preserveOther
  · intro y hyx
    have hvarNeLeaf : VariableProjection y ≠ leaf := by
      intro hvarLeaf
      rcases hleafHeap with ⟨address, hheapLeaf⟩
      rw [← hvarLeaf] at hheapLeaf
      cases hheapLeaf
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
  · intro y otherEnvSlot hyx henvY
    rcases hsafe.2 y otherEnvSlot henvY with
      ⟨oldValue, hslotY, hvalidOld⟩
    have hvarNeLeaf : VariableProjection y ≠ leaf := by
      intro hvarLeaf
      rcases hleafHeap with ⟨address, hheapLeaf⟩
      rw [← hvarLeaf] at hheapLeaf
      cases hheapLeaf
    have hslotYFinal :
        (store.update leaf { leafSlot with value := .value value }).slotAt
          (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
      simpa [ProgramStore.update, hvarNeLeaf] using hslotY
    exact ⟨oldValue, hslotYFinal,
      RuntimeFrame.validPartialValue_update_of_not_reaches hvalidOld
        (hotherNoReachLeaf y otherEnvSlot oldValue hyx henvY hslotY)⟩

theorem safeAbstractionWhenInitialized_update_owner_spine_of_frames
    {store store' : ProgramStore} {env writeEnv : Env}
    {current : Lifetime} {x : Name}
    {envSlot : EnvSlot} {rootSlot leafSlot : StoreSlot}
    {leaf : Location} {leafTy updatedTy : PartialTy}
    {path : Path} {rhsTy : Ty} {value : Value} :
    WellFormedEnvWhenInitialized env current →
    SafeAbstraction store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env.slotAt x = some envSlot →
    store.slotAt (VariableProjection x) = some rootSlot →
    rootSlot.lifetime = envSlot.lifetime →
    StoreOwnerSpineWhenInitialized env store (VariableProjection x) rootSlot
      envSlot.ty path leaf leafSlot leafTy →
    path ≠ [] →
    UpdateAtPath 0 env path envSlot.ty rhsTy writeEnv updatedTy →
    ¬ WriteProhibited (env.update x { envSlot with ty := updatedTy }) (.var x) →
    store' = store.update leaf { leafSlot with value := .value value } →
    ValidPartialValueWhenInitialized env store' (.value value) (.ty rhsTy) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.ReachesWhenInitialized env store oldValue otherEnvSlot.ty
          location →
        location ≠ leaf) →
    SafeAbstraction store'
      (writeEnv.update x { envSlot with ty := updatedTy }) := by
  intro _hwellFormed hsafe hvalidStore hheap henvSlot hrootSlot hrootLifetime
    hspine hpathNonempty hupdate hnotWriteUpdated hstore'
    hnewValid hotherNoReachLeaf
  have hwriteEnvEq : writeEnv = env :=
    StoreOwnerSpineWhenInitialized.updateAtPath_rank_zero_env_eq hspine hupdate
  cases hwriteEnvEq
  subst hstore'
  have hrootValidFinal :
      ValidPartialValueWhenInitialized env
        (store.update leaf { leafSlot with value := .value value })
        rootSlot.value updatedTy :=
    StoreOwnerSpineWhenInitialized.valid_after_updateAtPath_nonempty
      hspine hpathNonempty hupdate hnewValid
  have hslotXPost :
      (env.update x { envSlot with ty := updatedTy }).slotAt x =
        some { envSlot with ty := updatedTy } := by
    simp [Env.update]
  have hrootVarsFresh : x ∉ PartialTy.vars updatedTy := by
    intro hmem
    exact hnotWriteUpdated
      (writeProhibited_of_envSlot_var_in_type hslotXPost rfl hmem)
  have hrootValidFinalUpdated :
      ValidPartialValueWhenInitialized
        (env.update x { envSlot with ty := updatedTy })
        (store.update leaf { leafSlot with value := .value value })
        rootSlot.value updatedTy :=
    ValidPartialValueWhenInitialized.update_env_of_not_pathConflicts
      hnotWriteUpdated hrootVarsFresh hrootValidFinal
  have hpathCons : ∃ tail, path = () :: tail := by
    cases path with
    | nil => exact False.elim (hpathNonempty rfl)
    | cons head tail =>
        cases head
        exact ⟨tail, rfl⟩
  have hleafNeRoot : leaf ≠ VariableProjection x := by
    rcases hpathCons with ⟨tail, hpathEq⟩
    have hspineCons :
        StoreOwnerSpineWhenInitialized env store (VariableProjection x) rootSlot
          envSlot.ty (() :: tail) leaf leafSlot leafTy := by
      simpa [hpathEq] using hspine
    exact StoreOwnerSpineWhenInitialized.leaf_ne_storage_of_cons hspineCons
  have hrootNeLeaf : VariableProjection x ≠ leaf := by
    intro h
    exact hleafNeRoot h.symm
  have hrootSlotFinal :
      (store.update leaf { leafSlot with value := .value value }).slotAt
        (VariableProjection x) =
      some { value := rootSlot.value, lifetime := envSlot.lifetime } := by
    cases rootSlot with
    | mk rootValue rootLifetime =>
        cases hrootLifetime
        simpa [ProgramStore.update, hrootNeLeaf] using hrootSlot
  have hleafHeap : ∃ address, leaf = .heap address := by
    rcases hpathCons with ⟨tail, hpathEq⟩
    have hspineCons :
        StoreOwnerSpineWhenInitialized env store (VariableProjection x) rootSlot
          envSlot.ty (() :: tail) leaf leafSlot leafTy := by
      simpa [hpathEq] using hspine
    have hownsLeaf : ProgramStore.Owns store leaf :=
      ProgramStore.OwnsTransitively.to_owns
        (StoreOwnerSpineWhenInitialized.ownsTransitively_of_cons hspineCons)
    exact hheap leaf hownsLeaf
  refine safeAbstractionWhenInitialized_update_var_partial_of_preserved
    henvSlot hrootSlotFinal hrootValidFinalUpdated rfl ?domainOther ?preserveOther
  · intro y hyx
    have hvarNeLeaf : VariableProjection y ≠ leaf := by
      intro hvarLeaf
      rcases hleafHeap with ⟨address, hheapLeaf⟩
      rw [← hvarLeaf] at hheapLeaf
      cases hheapLeaf
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
  · intro y otherEnvSlot hyx henvY
    rcases hsafe.2 y otherEnvSlot henvY with
      ⟨oldValue, hslotY, hvalidOld⟩
    have hvarNeLeaf : VariableProjection y ≠ leaf := by
      intro hvarLeaf
      rcases hleafHeap with ⟨address, hheapLeaf⟩
      rw [← hvarLeaf] at hheapLeaf
      cases hheapLeaf
    have hslotYFinal :
        (store.update leaf { leafSlot with value := .value value }).slotAt
          (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } := by
      simpa [ProgramStore.update, hvarNeLeaf] using hslotY
    have henvYPost :
        (env.update x { envSlot with ty := updatedTy }).slotAt y =
          some otherEnvSlot := by
      simpa [Env.update, hyx] using henvY
    have hvarsOtherFresh : x ∉ PartialTy.vars otherEnvSlot.ty := by
      intro hmem
      exact hnotWriteUpdated
        (writeProhibited_of_envSlot_var_in_type henvYPost rfl hmem)
    have hvalidOldStoreUpdated :
        ValidPartialValueWhenInitialized env
          (store.update leaf { leafSlot with value := .value value })
          oldValue otherEnvSlot.ty :=
      RuntimeFrame.validPartialValueWhenInitialized_update_of_not_reachesWhenInitialized
        hvalidOld
        (hotherNoReachLeaf y otherEnvSlot oldValue hyx henvY hslotY)
    have hvalidOldFinalEnv :
        ValidPartialValueWhenInitialized
          (env.update x { envSlot with ty := updatedTy })
          (store.update leaf { leafSlot with value := .value value })
          oldValue otherEnvSlot.ty :=
      ValidPartialValueWhenInitialized.update_env_of_not_pathConflicts
        hnotWriteUpdated hvarsOtherFresh hvalidOldStoreUpdated
    exact ⟨oldValue, hslotYFinal, hvalidOldFinalEnv⟩

theorem RuntimeFrame.validPartialValue_update_of_owner_and_borrow_dependency_frame
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot} :
    ∀ {value : PartialValue} {ty : PartialTy}
      (_hvalid : ValidPartialValue store value ty),
      (∀ location,
        RuntimeFrame.OwnerReaches store value ty location →
        location ≠ updated) →
      (∀ location,
        RuntimeFrame.BorrowDependency store value ty location →
        location ≠ updated) →
      ValidPartialValue (store.update updated newSlot) value ty := by
  intro value ty hvalid
  induction hvalid with
  | unit | int | undef =>
      intro _howners _hdeps
      constructor
  | undefOf hinner hstrength =>
      intro howners _hdeps
      exact ValidPartialValue.undefOf
        (RuntimeFrame.validPartialValueSkeleton_update_of_not_owner_reaches
          hinner
          (by
            intro reached hreach
            exact howners reached
              (RuntimeFrame.OwnerReaches.undefOf hinner hstrength hreach)))
        hstrength
  | @borrow location mutable targets target hmem hloc =>
      intro _howners hdeps
      refine ValidPartialValue.borrow hmem ?_
      exact RuntimeFrame.loc_update_of_not_locReads hloc (by
        intro mid hreads
        exact hdeps mid
          (RuntimeFrame.BorrowDependency.borrow hmem hloc hreads))
  | @box location slot inner hslot _hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (RuntimeFrame.OwnerReaches.boxHere hslot)
      refine ValidPartialValue.box (location := location) (slot := slot) ?_ ?_
      · rw [RuntimeFrame.ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached
              (RuntimeFrame.OwnerReaches.boxInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (RuntimeFrame.BorrowDependency.boxInner hslot hdependency))
  | @boxFull location slot innerTy hslot _hinner ih =>
      intro howners hdeps
      have hlocationNe : location ≠ updated :=
        howners location (RuntimeFrame.OwnerReaches.boxFullHere hslot)
      refine ValidPartialValue.boxFull (location := location) (slot := slot) ?_ ?_
      · rw [RuntimeFrame.ProgramStore.slotAt_update_ne hlocationNe]
        exact hslot
      · exact ih
          (by
            intro reached hreach
            exact howners reached
              (RuntimeFrame.OwnerReaches.boxFullInner hslot hreach))
          (by
            intro dependency hdependency
            exact hdeps dependency
              (RuntimeFrame.BorrowDependency.boxFullInner hslot hdependency))

theorem stored_var_reaches_ne_owner_spine_leaf_of_noWrite
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {current : Lifetime} {x y : Name}
    {rootSlot leafSlot : StoreSlot} {otherEnvSlot : EnvSlot}
    {oldValue : PartialValue} {leaf : Location}
    {rootTy leafTy : PartialTy} {path : Path} :
    WellFormedEnv sourceEnv current →
    store ≈ₛ sourceEnv →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    StoreOwnerSpine store (VariableProjection x) rootSlot rootTy
      path leaf leafSlot leafTy →
    y ≠ x →
    sourceEnv.slotAt y = some otherEnvSlot →
    store.slotAt (VariableProjection y) =
      some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
    ValidPartialValue store oldValue otherEnvSlot.ty →
    (∀ z, z ∈ PartialTy.vars otherEnvSlot.ty →
      WriteProhibited observerEnv (.var z)) →
    ¬ WriteProhibited sourceEnv (.var x) →
    ¬ WriteProhibited observerEnv (.var x) →
    ∀ location,
      RuntimeFrame.Reaches store oldValue otherEnvSlot.ty location →
      location ≠ leaf := by
  intro hwellFormed hsafe hvalidStore hheap hspine hyx henvY hslotY
    hvalidOld hvarsObserver hnotWriteSource hnotWriteObserver location hreach
    hlocation
  have hborrowsOld :
      PartialTyBorrowsWellFormedInSlot sourceEnv otherEnvSlot.lifetime
        otherEnvSlot.ty := by
    intro mutable targets hcontains
    exact hwellFormed.1 y otherEnvSlot mutable targets henvY
      ⟨otherEnvSlot, henvY, hcontains⟩
  have hvalueHeapOld : PartialValueOwnerTargetsHeap oldValue :=
    partialValueOwnerTargetsHeap_of_slot hheap hslotY
  have hvarYNeRoot :
      VariableProjection y ≠ VariableProjection x := by
    intro hvarEq
    exact hyx (by cases hvarEq; rfl)
  have hrootNoOwnerReachOld :
      ∀ reached,
        RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty reached →
        reached ≠ VariableProjection x := by
    intro reached hownerReach
    exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
      hheap hvalueHeapOld hborrowsOld hownerReach
  have holdOwnerNoReachLeaf :
      ∀ reached,
        RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty reached →
        reached ≠ leaf :=
    StoreOwnerSpine.stored_var_not_reaches_leaf_of_not_reaches_root
      hvalidStore hheap hslotY hborrowsOld hvalidOld hspine hvarYNeRoot
      hrootNoOwnerReachOld
  have hleafProtected : ProtectedByBase store x leaf :=
    StoreOwnerSpine.leaf_protected_by_base hspine rfl
  rcases RuntimeFrame.Reaches.owner_or_borrow hreach with howner | hdependency
  · exact holdOwnerNoReachLeaf location howner hlocation
  · exact
      (borrowDependency_not_protectedByBase_of_varsProtectedIn
        hwellFormed hsafe hvalidStore hheap hborrowsOld hvarsObserver
        hnotWriteSource hnotWriteObserver hdependency)
      (by simpa [hlocation] using hleafProtected)

theorem term_value_reaches_ne_owner_spine_leaf_of_noWrite
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {current rhsLifetime : Lifetime} {x : Name}
    {rootSlot leafSlot : StoreSlot}
    {value : Value} {rhsTy : Ty} {leaf : Location}
    {rootTy leafTy : PartialTy} {path : Path} :
    WellFormedEnv sourceEnv current →
    store ≈ₛ sourceEnv →
    ValidRuntimeState store (.val value) →
    WellFormedTy sourceEnv rhsTy rhsLifetime →
    ValidValue store value rhsTy →
    StoreOwnerSpine store (VariableProjection x) rootSlot rootTy
      path leaf leafSlot leafTy →
    (∀ z, z ∈ PartialTy.vars (.ty rhsTy) →
      WriteProhibited observerEnv (.var z)) →
    ¬ WriteProhibited sourceEnv (.var x) →
    ¬ WriteProhibited observerEnv (.var x) →
    ∀ location,
      RuntimeFrame.Reaches store (.value value) (.ty rhsTy) location →
      location ≠ leaf := by
  intro hwellFormed hsafe hvalidRuntimeValue hwellTy hvalidValue hspine
    hvarsObserver hnotWriteSource hnotWriteObserver location hreach hlocation
  have hborrows :
      PartialTyBorrowsWellFormedInSlot sourceEnv rhsLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy
  have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
    ValueOwnerTargetsHeap.partial
      (TermOwnerTargetsHeap.value
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntimeValue))
  have hrootNoOwnerReach :
      ∀ reached,
        RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
        reached ≠ VariableProjection x := by
    intro reached hownerReach
    exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntimeValue)
      hvalueHeap hborrows hownerReach
  have hownerNoReachLeaf :
      ∀ reached,
        RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
        reached ≠ leaf :=
    StoreOwnerSpine.not_reaches_leaf_of_not_reaches_root
      hvalidRuntimeValue hborrows hvalidValue hspine hrootNoOwnerReach
  have hleafProtected : ProtectedByBase store x leaf :=
    StoreOwnerSpine.leaf_protected_by_base hspine rfl
  rcases RuntimeFrame.Reaches.owner_or_borrow hreach with howner | hdependency
  · exact hownerNoReachLeaf location howner hlocation
  · exact
      (borrowDependency_not_protectedByBase_of_varsProtectedIn
        hwellFormed hsafe
        (ValidRuntimeState.validStore hvalidRuntimeValue)
        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntimeValue)
          hborrows hvarsObserver hnotWriteSource hnotWriteObserver hdependency)
        (by simpa [hlocation] using hleafProtected)

theorem stored_var_reachesWhenInitialized_ne_owner_spine_leaf_of_noWrite
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {current : Lifetime} {x y : Name}
    {rootSlot leafSlot : StoreSlot} {otherEnvSlot : EnvSlot}
    {oldValue : PartialValue} {leaf : Location}
    {rootTy leafTy : PartialTy} {path : Path} :
    WellFormedEnvWhenInitialized sourceEnv current →
    SafeAbstraction store sourceEnv →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    StoreOwnerSpineWhenInitialized sourceEnv store (VariableProjection x) rootSlot
      rootTy path leaf leafSlot leafTy →
    y ≠ x →
    sourceEnv.slotAt y = some otherEnvSlot →
    store.slotAt (VariableProjection y) =
      some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
    ValidPartialValueWhenInitialized sourceEnv store oldValue otherEnvSlot.ty →
    (∀ z, z ∈ PartialTy.vars otherEnvSlot.ty →
      WriteProhibited observerEnv (.var z)) →
    (∀ z, z ≠ x → ¬ WriteProhibitedVia sourceEnv z (.var x)) →
    ¬ WriteProhibited observerEnv (.var x) →
    ∀ location,
      RuntimeFrame.ReachesWhenInitialized sourceEnv store oldValue
        otherEnvSlot.ty location →
      location ≠ leaf := by
  intro hwellFormed hsafe hvalidStore hheap hspine hyx henvY hslotY
    hvalidOld hvarsObserver hnoOtherSource hnotWriteObserver location hreach
    hlocation
  have hborrowsOld :
      PartialTyBorrowsWellFormedInSlotWhenInitialized sourceEnv
        otherEnvSlot.lifetime otherEnvSlot.ty := by
    intro mutable targets hcontains
    exact hwellFormed.1 y otherEnvSlot mutable targets henvY
      ⟨otherEnvSlot, henvY, hcontains⟩
  have hvalueHeapOld : PartialValueOwnerTargetsHeap oldValue :=
    partialValueOwnerTargetsHeap_of_slot hheap hslotY
  have hvarYNeRoot :
      VariableProjection y ≠ VariableProjection x := by
    intro hvarEq
    exact hyx (by cases hvarEq; rfl)
  have hrootNoOwnerReachOld :
      ∀ reached,
        RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty reached →
        reached ≠ VariableProjection x := by
    intro reached hownerReach
    exact RuntimeFrame.ownerReaches_ne_var_of_heap
      hheap hvalueHeapOld hownerReach
  have holdOwnerNoReachLeaf :
      ∀ reached,
        RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty reached →
        reached ≠ leaf :=
    StoreOwnerSpineWhenInitialized.stored_var_not_reaches_leaf_of_not_reaches_root
      hvalidStore hheap hslotY hvalidOld hspine hvarYNeRoot
      hrootNoOwnerReachOld
  have hleafProtected : ProtectedByBase store x leaf :=
    StoreOwnerSpineWhenInitialized.leaf_protected_by_base hspine rfl
  rcases RuntimeFrame.ReachesWhenInitialized.owner_or_borrow hreach with
    howner | hdependency
  · exact holdOwnerNoReachLeaf location howner hlocation
  · have hnotProtected : ¬ ProtectedByBase store x location := by
      intro hprotected
      rcases borrowDependencyWhenInitialized_protected_writeProhibitedVia_or_mem_vars
          hwellFormed hsafe hvalidStore hheap hborrowsOld hdependency
          hprotected with hvia | hmem
      · rcases hvia with ⟨z, hz, hvia⟩
        exact hnoOtherSource z hz hvia
      · exact hnotWriteObserver (hvarsObserver x hmem)
    exact hnotProtected (by simpa [hlocation] using hleafProtected)

theorem term_value_reachesWhenInitialized_ne_owner_spine_leaf_of_noWrite
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {current rhsLifetime : Lifetime} {x : Name}
    {rootSlot leafSlot : StoreSlot}
    {value : Value} {rhsTy : Ty} {leaf : Location}
    {rootTy leafTy : PartialTy} {path : Path} :
    WellFormedEnvWhenInitialized sourceEnv current →
    SafeAbstraction store sourceEnv →
    ValidRuntimeState store (.val value) →
    WellFormedTyWhenInitialized sourceEnv rhsTy rhsLifetime →
    ValidPartialValueWhenInitialized sourceEnv store (.value value) (.ty rhsTy) →
    StoreOwnerSpineWhenInitialized sourceEnv store (VariableProjection x) rootSlot
      rootTy path leaf leafSlot leafTy →
    (∀ z, z ∈ PartialTy.vars (.ty rhsTy) →
      WriteProhibited observerEnv (.var z)) →
    (∀ z, z ≠ x → ¬ WriteProhibitedVia sourceEnv z (.var x)) →
    ¬ WriteProhibited observerEnv (.var x) →
    ∀ location,
      RuntimeFrame.ReachesWhenInitialized sourceEnv store (.value value)
        (.ty rhsTy) location →
      location ≠ leaf := by
  intro hwellFormed hsafe hvalidRuntimeValue hwellTy hvalidValue hspine
    hvarsObserver hnoOtherSource hnotWriteObserver location hreach hlocation
  have hborrows :
      PartialTyBorrowsWellFormedInSlotWhenInitialized sourceEnv rhsLifetime
        (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlotWhenInitialized.of_wellFormedTy hwellTy
  have hvalueHeap : PartialValueOwnerTargetsHeap (.value value) :=
    ValueOwnerTargetsHeap.partial
      (TermOwnerTargetsHeap.value
        (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntimeValue))
  have hrootNoOwnerReach :
      ∀ reached,
        RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
        reached ≠ VariableProjection x := by
    intro reached hownerReach
    exact RuntimeFrame.ownerReaches_ne_var_of_heap
      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntimeValue)
      hvalueHeap hownerReach
  have hownerNoReachLeaf :
      ∀ reached,
        RuntimeFrame.OwnerReaches store (.value value) (.ty rhsTy) reached →
        reached ≠ leaf :=
    StoreOwnerSpineWhenInitialized.not_reaches_leaf_of_not_reaches_root
      hvalidRuntimeValue hvalidValue hspine hrootNoOwnerReach
  have hleafProtected : ProtectedByBase store x leaf :=
    StoreOwnerSpineWhenInitialized.leaf_protected_by_base hspine rfl
  rcases RuntimeFrame.ReachesWhenInitialized.owner_or_borrow hreach with
    howner | hdependency
  · exact hownerNoReachLeaf location howner hlocation
  · have hnotProtected : ¬ ProtectedByBase store x location := by
      intro hprotected
      rcases borrowDependencyWhenInitialized_protected_writeProhibitedVia_or_mem_vars
          hwellFormed hsafe
          (ValidRuntimeState.validStore hvalidRuntimeValue)
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntimeValue)
          hborrows hdependency hprotected with hvia | hmem
      · rcases hvia with ⟨z, hz, hvia⟩
        exact hnoOtherSource z hz hvia
      · exact hnotWriteObserver (hvarsObserver x hmem)
    exact hnotProtected (by simpa [hlocation] using hleafProtected)

/-! ### Location order for borrow-resolution chains (Appendix 9.6 support)

Lval resolution follows stored references.  Owner edges stay inside one
single-owner tree, while a borrow jump moves to the resolution of a
runtime-selected borrow target whose base ranks strictly below the current
tree's root variable.  This induces a strict order on resolved locations: a
typed lval can never read the location it resolves to, and nothing resolves
through a location from "at or below" it.
-/

/-- Ownership paths compose. -/
theorem ProgramStore.OwnsTransitively.comp {store : ProgramStore}
    {first middle last : Location} :
    ProgramStore.OwnsTransitively store first middle →
    ProgramStore.OwnsTransitively store middle last →
    ProgramStore.OwnsTransitively store first last := by
  intro hfirst hsecond
  induction hfirst with
  | direct howns =>
      exact ProgramStore.OwnsTransitively.trans howns hsecond
  | trans howns _htail ih =>
      exact ProgramStore.OwnsTransitively.trans howns (ih hsecond)

/-- In a single-owner store, two ownership paths into the same location are
totally ordered. -/
theorem ProgramStore.OwnsTransitively.same_target_comparable
    {store : ProgramStore} {first second owned : Location} :
    ValidStore store →
    ProgramStore.OwnsTransitively store first owned →
    ProgramStore.OwnsTransitively store second owned →
    first = second ∨ ProgramStore.OwnsTransitively store first second ∨
      ProgramStore.OwnsTransitively store second first := by
  intro hvalid hfirst
  induction hfirst with
  | direct howns =>
      intro hsecond
      rcases ProgramStore.OwnsTransitively.predecessor_eq_or_owned hvalid
          hsecond howns with heq | hba
      · exact Or.inl heq
      · exact Or.inr (Or.inr hba)
  | @trans storage middle owned howns _htail ih =>
      intro hsecond
      rcases ih hsecond with heq | hmb | hbm
      · subst heq
        exact Or.inr (Or.inl (ProgramStore.OwnsTransitively.direct howns))
      · exact Or.inr (Or.inl (ProgramStore.OwnsTransitively.trans howns hmb))
      · rcases ProgramStore.OwnsTransitively.predecessor_eq_or_owned hvalid
            hbm howns with heq | hba
        · exact Or.inl heq
        · exact Or.inr (Or.inr hba)

/-- Owner trees form a forest: a location owned from two variable roots pins
the roots equal. -/
theorem ProgramStore.OwnsTransitively.var_root_unique {store : ProgramStore}
    {root root' : Name} {owned : Location} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ProgramStore.OwnsTransitively store (VariableProjection root) owned →
    ProgramStore.OwnsTransitively store (VariableProjection root') owned →
    root = root' := by
  intro hvalid hheap hfirst hsecond
  rcases ProgramStore.OwnsTransitively.same_target_comparable hvalid hfirst
      hsecond with heq | hab | hba
  · simpa [VariableProjection] using heq
  · exact absurd (ProgramStore.OwnsTransitively.to_owns hab)
      (not_owns_var_of_storeOwnerTargetsHeap hheap)
  · exact absurd (ProgramStore.OwnsTransitively.to_owns hba)
      (not_owns_var_of_storeOwnerTargetsHeap hheap)

/-- The protecting root variable of a location is unique. -/
theorem ProtectedByBase.root_unique {store : ProgramStore} {root root' : Name}
    {location : Location} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ProtectedByBase store root location →
    ProtectedByBase store root' location →
    root = root' := by
  intro hvalid hheap hfirst hsecond
  rcases hfirst with hvar | howns
  · rcases hsecond with hvar' | howns'
    · simpa [VariableProjection] using hvar.symm.trans hvar'
    · subst hvar
      exact absurd (ProgramStore.OwnsTransitively.to_owns howns')
        (not_owns_var_of_storeOwnerTargetsHeap hheap)
  · rcases hsecond with hvar' | howns'
    · subst hvar'
      exact absurd (ProgramStore.OwnsTransitively.to_owns howns)
        (not_owns_var_of_storeOwnerTargetsHeap hheap)
    · exact ProgramStore.OwnsTransitively.var_root_unique hvalid hheap howns
        howns'

/--
Strict location order induced by resolution chains: `lower` sits below `upper`
when `lower`'s tree root ranks strictly below `upper`'s, or both share a root
and `upper` transitively owns `lower`.
-/
def LocationBelow (store : ProgramStore) (φ : Name → Nat)
    (lower upper : Location) : Prop :=
  ∃ rootLower rootUpper,
    ProtectedByBase store rootLower lower ∧
    ProtectedByBase store rootUpper upper ∧
    (φ rootLower < φ rootUpper ∨
      (rootLower = rootUpper ∧ ProgramStore.OwnsTransitively store upper lower))

theorem LocationBelow.trans {store : ProgramStore} {φ : Name → Nat}
    {first second third : Location} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LocationBelow store φ first second →
    LocationBelow store φ second third →
    LocationBelow store φ first third := by
  intro hvalid hheap hab hbc
  rcases hab with ⟨ra, rb, hpa, hpb, hcaseab⟩
  rcases hbc with ⟨rb', rc, hpb', hpc, hcasebc⟩
  have hrbEq : rb = rb' := ProtectedByBase.root_unique hvalid hheap hpb hpb'
  subst hrbEq
  refine ⟨ra, rc, hpa, hpc, ?_⟩
  rcases hcaseab with hlt | ⟨heq, howns⟩
  · rcases hcasebc with hlt' | ⟨heq', _howns'⟩
    · exact Or.inl (lt_trans hlt hlt')
    · exact Or.inl (by rw [← heq']; exact hlt)
  · rcases hcasebc with hlt' | ⟨heq', howns'⟩
    · exact Or.inl (by rw [heq]; exact hlt')
    · exact Or.inr ⟨heq.trans heq',
        ProgramStore.OwnsTransitively.comp howns' howns⟩

theorem LocationBelow.irrefl {store : ProgramStore} {φ : Name → Nat}
    {location : Location} {slot : StoreSlot} {ty : PartialTy} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    store.slotAt location = some slot →
    ValidPartialValue store slot.value ty →
    ¬ LocationBelow store φ location location := by
  intro hvalid hheap hslot hvalidSlot hbelow
  rcases hbelow with ⟨r, r', hp, hp', hcase⟩
  have hrEq : r = r' := ProtectedByBase.root_unique hvalid hheap hp hp'
  subst hrEq
  rcases hcase with hlt | ⟨_heq, howns⟩
  · exact Nat.lt_irrefl _ hlt
  · exact ValidPartialValue.no_storage_ownership_cycle hslot hvalidSlot howns

/-- Extend a slot-typed reachability by one owning step into a partial box. -/
theorem RuntimeFrame.ReachesSlot.snoc_box {store : ProgramStore}
    {value : PartialValue} {ty slice : PartialTy} {reached owned : Location}
    {reachedSlot ownedSlot : StoreSlot} {innerView : PartialTy} :
    RuntimeFrame.ReachesSlot store value ty reached reachedSlot slice →
    slice = .box innerView →
    reachedSlot.value = .value (.ref { location := owned, owner := true }) →
    store.slotAt owned = some ownedSlot →
    ValidPartialValue store ownedSlot.value innerView →
    RuntimeFrame.ReachesSlot store value ty owned ownedSlot innerView := by
  intro hreach
  induction hreach with
  | @boxHere location slot inner hslot _hvalid =>
      intro hslice hvalue howned hvalid
      subst hslice
      refine RuntimeFrame.ReachesSlot.boxInner hslot ?_
      rw [hvalue]
      exact RuntimeFrame.ReachesSlot.boxHere howned hvalid
  | @boxFullHere location slot innerTy hslot _hvalid =>
      intro hslice _hvalue _howned _hvalid
      cases hslice
  | boxInner hslot _hinner ih =>
      intro hslice hvalue howned hvalid
      exact RuntimeFrame.ReachesSlot.boxInner hslot
        (ih hslice hvalue howned hvalid)
  | boxFullInner hslot _hinner ih =>
      intro hslice hvalue howned hvalid
      exact RuntimeFrame.ReachesSlot.boxFullInner hslot
        (ih hslice hvalue howned hvalid)

/-- Extend a slot-typed reachability by one owning step into a full box. -/
theorem RuntimeFrame.ReachesSlot.snoc_boxFull {store : ProgramStore}
    {value : PartialValue} {ty slice : PartialTy} {reached owned : Location}
    {reachedSlot ownedSlot : StoreSlot} {innerTy : Ty} :
    RuntimeFrame.ReachesSlot store value ty reached reachedSlot slice →
    slice = .ty (.box innerTy) →
    reachedSlot.value = .value (.ref { location := owned, owner := true }) →
    store.slotAt owned = some ownedSlot →
    ValidPartialValue store ownedSlot.value (.ty innerTy) →
    RuntimeFrame.ReachesSlot store value ty owned ownedSlot (.ty innerTy) := by
  intro hreach
  induction hreach with
  | @boxHere location slot inner hslot _hvalid =>
      intro hslice hvalue howned hvalid
      subst hslice
      refine RuntimeFrame.ReachesSlot.boxInner hslot ?_
      rw [hvalue]
      exact RuntimeFrame.ReachesSlot.boxFullHere howned hvalid
  | @boxFullHere location slot innerTy' hslot _hvalid =>
      intro hslice hvalue howned hvalid
      have hinnerEq : innerTy' = .box innerTy := by
        simpa using hslice
      subst hinnerEq
      refine RuntimeFrame.ReachesSlot.boxFullInner hslot ?_
      rw [hvalue]
      exact RuntimeFrame.ReachesSlot.boxFullHere howned hvalid
  | boxInner hslot _hinner ih =>
      intro hslice hvalue howned hvalid
      exact RuntimeFrame.ReachesSlot.boxInner hslot
        (ih hslice hvalue howned hvalid)
  | boxFullInner hslot _hinner ih =>
      intro hslice hvalue howned hvalid
      exact RuntimeFrame.ReachesSlot.boxFullInner hslot
        (ih hslice hvalue howned hvalid)

/-- A dependency of a value passes through any slot-typed reachability ending
at a borrow node: box spines are linear, so the descent and the dependency
follow the same owning references. -/
theorem RuntimeFrame.borrowDependency_through_reachesSlot {store : ProgramStore}
    {value : PartialValue} {ty slice : PartialTy} {reached : Location}
    {reachedSlot : StoreSlot} {mutable : Bool} {targets : List LVal}
    {dependency : Location} :
    RuntimeFrame.ReachesSlot store value ty reached reachedSlot slice →
    slice = .ty (.borrow mutable targets) →
    RuntimeFrame.BorrowDependency store value ty dependency →
    RuntimeFrame.BorrowDependency store reachedSlot.value
      (.ty (.borrow mutable targets)) dependency := by
  intro hreach
  induction hreach with
  | @boxHere location slot inner hslot _hvalid =>
      intro hslice hdep
      subst hslice
      cases hdep with
      | @boxInner _ slot₂ _ _ hslot₂ hinner =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          rw [hslotEq]
          exact hinner
  | @boxFullHere location slot innerTy' hslot _hvalid =>
      intro hslice hdep
      have hinnerEq : innerTy' = .borrow mutable targets := by
        simpa using hslice
      subst hinnerEq
      cases hdep with
      | @boxFullInner _ slot₂ _ _ hslot₂ hinner =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          rw [hslotEq]
          exact hinner
  | @boxInner location reached slot reachedSlot' inner reachedTy hslot _hinner
      ih =>
      intro hslice hdep
      cases hdep with
      | @boxInner _ slot₂ _ _ hslot₂ hinner =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          exact ih hslice (by rw [hslotEq]; exact hinner)
  | @boxFullInner location reached slot reachedSlot' innerTy reachedTy hslot
      _hinner ih =>
      intro hslice hdep
      cases hdep with
      | @boxFullInner _ slot₂ _ _ hslot₂ hinner =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          exact ih hslice (by rw [hslotEq]; exact hinner)

/--
Intrinsic root view of a resolved location: the location lies in the owner
tree of a root variable ranked at most the lval's base, and its slot carries a
valid typed view whose borrow-target variables rank strictly below that root.

The view follows the runtime resolution: owner edges descend within the root's
slot type, while every borrow jump re-enters at a target whose base ranks
strictly below the current root.
-/
theorem RuntimeFrame.loc_intrinsicRootView {store : ProgramStore} {env : Env}
    {current : Lifetime} {φ : Name → Nat} {lv : LVal} {pt : PartialTy}
    {lifetime : Lifetime} {location : Location} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    LValTyping env lv pt lifetime →
    store.loc lv = some location →
    ∃ root slotL viewTy slotLifetime,
      ProtectedByBase store root location ∧
      φ root ≤ φ (LVal.base lv) ∧
      store.slotAt location = some slotL ∧
      ValidPartialValue store slotL.value viewTy ∧
      PartialTyStrengthens viewTy pt ∧
      (∀ v, v ∈ PartialTy.vars viewTy → φ v < φ root) ∧
        PartialTyBorrowsWellFormedInSlot env slotLifetime viewTy ∧
        (∀ {mutable : Bool} {targets : List LVal},
          PartialTyContains viewTy (.borrow mutable targets) →
          env ⊢ root ↝ (.borrow mutable targets)) ∧
        ∃ rootEnvSlot rootValue,
          env.slotAt root = some rootEnvSlot ∧
          store.slotAt (VariableProjection root) =
            some { value := rootValue, lifetime := rootEnvSlot.lifetime } ∧
          ((location = VariableProjection root ∧ viewTy = rootEnvSlot.ty ∧
              slotL.value = rootValue) ∨
            RuntimeFrame.ReachesSlot store rootValue rootEnvSlot.ty location
              slotL viewTy) := by
  intro hφ hwellFormed hsafe htyping hloc
  exact go hφ hwellFormed hsafe htyping hloc
where
  go {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {lv : LVal} {pt : PartialTy} {lifetime : Lifetime} {location : Location}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ≈ₛ env) (htyping : LValTyping env lv pt lifetime)
      (hloc : store.loc lv = some location) :
      ∃ root slotL viewTy slotLifetime,
        ProtectedByBase store root location ∧
        φ root ≤ φ (LVal.base lv) ∧
        store.slotAt location = some slotL ∧
        ValidPartialValue store slotL.value viewTy ∧
        PartialTyStrengthens viewTy pt ∧
        (∀ v, v ∈ PartialTy.vars viewTy → φ v < φ root) ∧
          PartialTyBorrowsWellFormedInSlot env slotLifetime viewTy ∧
          (∀ {mutable : Bool} {targets : List LVal},
            PartialTyContains viewTy (.borrow mutable targets) →
            env ⊢ root ↝ (.borrow mutable targets)) ∧
          ∃ rootEnvSlot rootValue,
            env.slotAt root = some rootEnvSlot ∧
            store.slotAt (VariableProjection root) =
              some { value := rootValue, lifetime := rootEnvSlot.lifetime } ∧
            ((location = VariableProjection root ∧ viewTy = rootEnvSlot.ty ∧
                slotL.value = rootValue) ∨
              RuntimeFrame.ReachesSlot store rootValue rootEnvSlot.ty location
                slotL viewTy) := by
    cases lv with
    | var x =>
        cases htyping with
        | @var _ slot hslot =>
            have hlocEq : location = VariableProjection x := by
              simp [ProgramStore.loc] at hloc
              exact hloc.symm
            subst hlocEq
            rcases hsafe.2 x slot hslot with ⟨value, hstoreSlot, hvalid⟩
            refine ⟨x, _, slot.ty, slot.lifetime, Or.inl rfl, le_refl _,
              hstoreSlot, hvalid, PartialTyStrengthens.reflex,
              hφ x slot hslot, ?_, ?_,
              ⟨slot, value, hslot, hstoreSlot, Or.inl ⟨rfl, rfl, rfl⟩⟩⟩
            · intro mutable targets hcontains
              exact hwellFormed.1 x slot mutable targets hslot
                ⟨slot, hslot, hcontains⟩
            · intro mutable targets hcontains
              exact ⟨slot, hslot, hcontains⟩
    | deref u =>
        cases htyping with
        | box hsource =>
            have hsourceAbs :
                LValLocationAbstraction store u (.box _) :=
              lvalTyping_defined_location hwellFormed hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            rcases go hφ hwellFormed hsafe hsource hmiddleLoc with
              ⟨root, slotM, viewTyM, slotLt, hprotM, hrank, hslotM, hvalidM,
                hstrengthM, hbound, hborrowsM, hcontainsM, rootEnvSlot,
                rootValue, hrootEnvSlot, hrootValue, hdescent⟩
            have hslotMEq :
                slotM = ⟨middleValue, middleLifetime⟩ :=
              Option.some.inj (hslotM.symm.trans hmiddleSlot)
            subst hslotMEq
            cases hmiddleValid with
            | @box owned ownedSlot _ hownedSlot _hinnerValid =>
                have hderefLoc : store.loc (.deref u) = some owned := by
                  simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot]
                have hlocEq : location = owned := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                have hownsAt :
                    ProgramStore.OwnsAt store location middle :=
                  ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
                cases hvalidM with
                | @box owned₂ ownedSlot₂ innerView hownedSlot₂ hinnerView =>
                    refine ⟨root, ownedSlot₂, innerView, slotLt,
                      ProtectedByBase.trans_owned hprotM hownsAt,
                      hrank, hownedSlot₂, hinnerView, ?_, ?_, ?_, ?_,
                      rootEnvSlot, rootValue, hrootEnvSlot, hrootValue,
                      Or.inr ?_⟩
                    · cases hstrengthM with
                      | reflex => exact PartialTyStrengthens.reflex
                      | box hinnerStrength => exact hinnerStrength
                    · intro v hv
                      exact hbound v (by simpa [PartialTy.vars] using hv)
                    · intro mutable targets hcontains
                      exact hborrowsM (PartialTyContains.box hcontains)
                    · intro mutable targets hcontains
                      exact hcontainsM (PartialTyContains.box hcontains)
                    · rcases hdescent with ⟨_hMvar, hviewEq, hvalEq⟩ | hreach
                      · rw [← hvalEq, ← hviewEq]
                        exact RuntimeFrame.ReachesSlot.boxHere hownedSlot₂
                          hinnerView
                      · exact RuntimeFrame.ReachesSlot.snoc_box hreach rfl rfl
                          hownedSlot₂ hinnerView
                | @boxFull owned₂ ownedSlot₂ innerTy hownedSlot₂ hinnerView =>
                    cases hstrengthM
                | @undefOf _ _ hiddenOuter hskel hstrength =>
                    cases hstrengthM
        | boxFull hsource =>
            have hsourceAbs :
                LValLocationAbstraction store u (.ty (.box _)) :=
              lvalTyping_defined_location hwellFormed hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            rcases go hφ hwellFormed hsafe hsource hmiddleLoc with
              ⟨root, slotM, viewTyM, slotLt, hprotM, hrank, hslotM, hvalidM,
                hstrengthM, hbound, hborrowsM, hcontainsM, rootEnvSlot,
                rootValue, hrootEnvSlot, hrootValue, hdescent⟩
            have hslotMEq :
                slotM = ⟨middleValue, middleLifetime⟩ :=
              Option.some.inj (hslotM.symm.trans hmiddleSlot)
            subst hslotMEq
            cases hmiddleValid with
            | @boxFull owned ownedSlot _ hownedSlot _hinnerValid =>
                have hderefLoc : store.loc (.deref u) = some owned := by
                  simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot]
                have hlocEq : location = owned := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                have hownsAt :
                    ProgramStore.OwnsAt store location middle :=
                  ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
                cases hvalidM with
                | @box owned₂ ownedSlot₂ innerView hownedSlot₂ hinnerView =>
                    cases hstrengthM
                | @boxFull owned₂ ownedSlot₂ innerView hownedSlot₂ hinnerView =>
                    refine ⟨root, ownedSlot₂, .ty innerView, slotLt,
                      ProtectedByBase.trans_owned hprotM hownsAt,
                      hrank, hownedSlot₂, hinnerView, ?_, ?_, ?_, ?_,
                      rootEnvSlot, rootValue, hrootEnvSlot, hrootValue,
                      Or.inr ?_⟩
                    · cases hstrengthM with
                      | reflex => exact PartialTyStrengthens.reflex
                      | tyBox hinnerStrength => exact hinnerStrength
                    · intro v hv
                      exact hbound v (by simpa [PartialTy.vars, Ty.vars] using hv)
                    · intro mutable targets hcontains
                      exact hborrowsM (PartialTyContains.tyBox hcontains)
                    · intro mutable targets hcontains
                      exact hcontainsM (PartialTyContains.tyBox hcontains)
                    · rcases hdescent with ⟨_hMvar, hviewEq, hvalEq⟩ | hreach
                      · rw [← hvalEq, ← hviewEq]
                        exact RuntimeFrame.ReachesSlot.boxFullHere hownedSlot₂
                          hinnerView
                      · exact RuntimeFrame.ReachesSlot.snoc_boxFull hreach rfl rfl
                          hownedSlot₂ hinnerView
                | @undefOf _ _ hiddenOuter hskel hstrength =>
                    cases hstrengthM
        | @borrow _ mutable targets borrowLifetime targetLifetime targetTy
            hsource htargets =>
            have hsourceAbs :
                LValLocationAbstraction store u (.ty (.borrow mutable targets)) :=
              lvalTyping_defined_location hwellFormed hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            rcases go hφ hwellFormed hsafe hsource hmiddleLoc with
              ⟨root, slotM, viewTyM, slotLt, hprotM, hrank, hslotM, hvalidM,
                hstrengthM, hbound, hborrowsM, hcontainsM, _rootEnvSlot,
                _rootValue, _hrootEnvSlot, _hrootValue, _hdescent⟩
            have hslotMEq :
                slotM = ⟨middleValue, middleLifetime⟩ :=
              Option.some.inj (hslotM.symm.trans hmiddleSlot)
            subst hslotMEq
            cases hvalidM with
            | @borrow target₀Loc mutable' targets' target₀ hmem₀ htarget₀Loc =>
                have htargetMem : target₀ ∈ targets := by
                  cases hstrengthM with
                  | reflex => exact hmem₀
                  | borrow hsubset => exact hsubset hmem₀
                have hderefLoc : store.loc (.deref u) = some target₀Loc := by
                  simp [ProgramStore.loc, hmiddleLoc, hslotM]
                have hlocEq : location = target₀Loc := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                rcases lvalTargetsTyping_member_strengthens htargets target₀
                    htargetMem with
                  ⟨selectedTy, selectedLifetime, htargetTyping,
                    hselectedStrengthens⟩
                have htargetRank :
                    φ (LVal.base target₀) < φ (LVal.base u) := by
                  exact (lvalTyping_vars_rank_lt hφ).1 hsource
                    (LVal.base target₀)
                    (by
                      simpa [PartialTy.vars, Ty.vars] using
                        List.mem_map_of_mem htargetMem)
                rcases go hφ hwellFormed hsafe htargetTyping htarget₀Loc with
                  ⟨root₂, slotL, viewTy, slotLt₂, hprot₂, hrank₂, hslotL,
                    hvalidL, hstrengthL, hbound₂, hborrows₂, hcontains₂,
                    rootEnvSlot₂, rootValue₂, hrootEnvSlot₂, hrootValue₂,
                    hdescent₂⟩
                exact ⟨root₂, slotL, viewTy, slotLt₂, hprot₂,
                  le_of_lt (lt_of_le_of_lt hrank₂ htargetRank),
                  hslotL, hvalidL,
                  partialTyStrengthens_trans_safe hstrengthL
                    hselectedStrengthens,
                  hbound₂, hborrows₂, hcontains₂, rootEnvSlot₂, rootValue₂,
                  hrootEnvSlot₂, hrootValue₂, hdescent₂⟩
            | unit | int | undef =>
                cases hstrengthM
            | @box owned ownedSlot innerView hownedSlot hinnerView =>
                cases hstrengthM
            | @boxFull owned ownedSlot innerTy hownedSlot hinnerView =>
                cases hstrengthM
            | @undefOf _ _ hiddenOuter hskel hstrength =>
                cases hstrengthM
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)

/--
One dereference step moves strictly down the location order: an owner edge
descends within the current tree, and a borrow jump lands at a target whose
root ranks strictly below the current root.
-/
theorem RuntimeFrame.loc_deref_step_below {store : ProgramStore} {env : Env}
    {current : Lifetime} {φ : Name → Nat} {u : LVal} {pt : PartialTy}
    {lifetime : Lifetime} {middle result : Location} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    LValTyping env (.deref u) pt lifetime →
    store.loc u = some middle →
    store.loc (.deref u) = some result →
    LocationBelow store φ result middle := by
  intro hφ hwellFormed hsafe htyping hmiddleLoc hloc
  cases htyping with
  | box hsource =>
      rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe hsource
          hmiddleLoc with
        ⟨root, slotM, viewTyM, slotLt, hprotM, _hrank, hslotM, hvalidM,
          hstrengthM, _hbound, _hborrowsM, _hcontainsM, _rootEnvSlot,
          _rootValue, _hrootEnvSlot, _hrootValue, _hdescent⟩
      rcases slotM with ⟨middleValue, middleLifetime⟩
      cases hvalidM with
      | @box owned ownedSlot innerView hownedSlot _hinner =>
          have hderefLoc : store.loc (.deref u) = some owned := by
            simp [ProgramStore.loc, hmiddleLoc, hslotM]
          have hresEq : result = owned := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst hresEq
          have hownsAt : ProgramStore.OwnsAt store result middle :=
            ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
          exact ⟨root, root, ProtectedByBase.trans_owned hprotM hownsAt,
            hprotM,
            Or.inr ⟨rfl, ProgramStore.OwnsTransitively.direct hownsAt⟩⟩
      | unit | int | undef =>
          cases hstrengthM
      | @borrow target₀Loc mutable' targets' witness hmemW hlocW =>
          cases hstrengthM
      | @boxFull owned ownedSlot innerTy hownedSlot _hinner =>
          cases hstrengthM
      | @undefOf _ _ hiddenOuter hskel hstrength =>
          cases hstrengthM
  | boxFull hsource =>
      rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe hsource
          hmiddleLoc with
        ⟨root, slotM, viewTyM, slotLt, hprotM, _hrank, hslotM, hvalidM,
          hstrengthM, _hbound, _hborrowsM, _hcontainsM, _rootEnvSlot,
          _rootValue, _hrootEnvSlot, _hrootValue, _hdescent⟩
      rcases slotM with ⟨middleValue, middleLifetime⟩
      cases hvalidM with
      | @boxFull owned ownedSlot innerView hownedSlot _hinner =>
          have hderefLoc : store.loc (.deref u) = some owned := by
            simp [ProgramStore.loc, hmiddleLoc, hslotM]
          have hresEq : result = owned := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst hresEq
          have hownsAt : ProgramStore.OwnsAt store result middle :=
            ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
          exact ⟨root, root, ProtectedByBase.trans_owned hprotM hownsAt,
            hprotM,
            Or.inr ⟨rfl, ProgramStore.OwnsTransitively.direct hownsAt⟩⟩
      | unit | int | undef =>
          cases hstrengthM
      | @borrow target₀Loc mutable' targets' witness hmemW hlocW =>
          cases hstrengthM
      | @box owned ownedSlot innerView hownedSlot _hinner =>
          cases hstrengthM
      | @undefOf _ _ hiddenOuter hskel hstrength =>
          cases hstrengthM
  | borrow hsource htargets =>
      rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe hsource
          hmiddleLoc with
        ⟨root, slotM, viewTyM, slotLt, hprotM, _hrank, hslotM, hvalidM,
          hstrengthM, hbound, hborrowsM, _hcontainsM, _rootEnvSlot,
          _rootValue, _hrootEnvSlot, _hrootValue, _hdescent⟩
      rcases slotM with ⟨middleValue, middleLifetime⟩
      cases hvalidM with
      | @borrow target₀Loc mutable' targets' witness hmemW hlocW =>
          have hderefLoc : store.loc (.deref u) = some target₀Loc := by
            simp [ProgramStore.loc, hmiddleLoc, hslotM]
          have hresEq : result = target₀Loc := by
            rw [hloc] at hderefLoc
            exact Option.some.inj hderefLoc
          subst hresEq
          rcases hborrowsM PartialTyContains.here witness hmemW with
            ⟨witnessTy, witnessLifetime, hwitnessTyping, _houtlives, _hbase⟩
          have hwitnessRank : φ (LVal.base witness) < φ root := by
            refine hbound (LVal.base witness) ?_
            simpa [PartialTy.vars, Ty.vars] using List.mem_map_of_mem hmemW
          rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe
              hwitnessTyping hlocW with
            ⟨root₂, _, _, _, hprot₂, hrank₂, _, _, _, _, _, _, _, _, _, _, _⟩
          exact ⟨root₂, root, hprot₂, hprotM,
            Or.inl (lt_of_le_of_lt hrank₂ hwitnessRank)⟩
      | unit | int | undef =>
          cases hstrengthM
      | @box owned ownedSlot innerView hownedSlot _hinner =>
          cases hstrengthM
      | @boxFull owned ownedSlot innerTy hownedSlot _hinner =>
          cases hstrengthM
      | @undefOf _ _ hiddenOuter hskel hstrength =>
          cases hstrengthM

/--
A typed lval resolves strictly below every location its resolution reads.
This is the global acyclicity of resolution chains: chains descend the
location order, so in particular no typed lval reads its own resolution.
-/
theorem RuntimeFrame.locReads_below {store : ProgramStore} {env : Env}
    {current : Lifetime} {φ : Name → Nat} {lv : LVal} {pt : PartialTy}
    {lifetime : Lifetime} {readLocation result : Location} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv pt lifetime →
    RuntimeFrame.LocReads store lv readLocation →
    store.loc lv = some result →
    LocationBelow store φ result readLocation := by
  intro hφ hwellFormed hsafe hvalidStore hheap htyping hreads hloc
  induction hreads generalizing pt lifetime result with
  | @here u readLoc huLoc =>
      cases htyping with
      | box hsource =>
          exact RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe
            (LValTyping.box hsource) huLoc hloc
      | boxFull hsource =>
          exact RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe
            (LValTyping.boxFull hsource) huLoc hloc
      | borrow hsource htargets =>
          exact RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe
            (LValTyping.borrow hsource htargets) huLoc hloc
  | @there u readLoc hinner ih =>
      cases htyping with
      | box hsource =>
          rcases lvalTyping_defined_location hwellFormed hsafe hsource with
            ⟨middle, middleSlot, hmiddleLoc, _hmiddleSlot, _hmiddleValid⟩
          exact LocationBelow.trans hvalidStore hheap
            (RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe
              (LValTyping.box hsource) hmiddleLoc hloc)
            (ih hsource hmiddleLoc)
      | boxFull hsource =>
          rcases lvalTyping_defined_location hwellFormed hsafe hsource with
            ⟨middle, middleSlot, hmiddleLoc, _hmiddleSlot, _hmiddleValid⟩
          exact LocationBelow.trans hvalidStore hheap
            (RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe
              (LValTyping.boxFull hsource) hmiddleLoc hloc)
            (ih hsource hmiddleLoc)
      | borrow hsource htargets =>
          rcases lvalTyping_defined_location hwellFormed hsafe hsource with
            ⟨middle, middleSlot, hmiddleLoc, _hmiddleSlot, _hmiddleValid⟩
          exact LocationBelow.trans hvalidStore hheap
            (RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe
              (LValTyping.borrow hsource htargets) hmiddleLoc hloc)
            (ih hsource hmiddleLoc)

/-! ### Guarded-base chase

Resolving into (or reading from) a guard-protected owner tree forces the
resolving lvalue's base into the guard set, provided the guard set absorbs the
container of any borrow node that targets a guarded base.  At the assignment
use-site the guard set is the write's authority chain and absorption is exactly
borrow safety (`BorrowSafeEnv`) against the chain's mutable-borrow records.
-/

theorem RuntimeFrame.loc_protected_guarded_base {store : ProgramStore}
    {env : Env} {current : Lifetime} {φ : Name → Nat} {G : Name → Prop}
    {lv : LVal} {pt : PartialTy} {lifetime : Lifetime} {location : Location}
    {r : Name} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ container mutable ts t, env ⊢ container ↝ (.borrow mutable ts) →
      t ∈ ts → G (LVal.base t) → G container) →
    LValTyping env lv pt lifetime →
    store.loc lv = some location →
    ProtectedByBase store r location →
    G r →
    G (LVal.base lv) := by
  intro hφ hwellFormed hsafe hvalidStore hheap hcollapse htyping hloc hprot hG
  exact go hφ hwellFormed hsafe hvalidStore hheap hcollapse htyping hloc hprot
    hG
where
  go {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {G : Name → Prop} {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
      {location : Location} {r : Name}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ≈ₛ env) (hvalidStore : ValidStore store)
      (hheap : StoreOwnerTargetsHeap store)
      (hcollapse : ∀ container mutable ts t,
        env ⊢ container ↝ (.borrow mutable ts) →
        t ∈ ts → G (LVal.base t) → G container)
      (htyping : LValTyping env lv pt lifetime)
      (hloc : store.loc lv = some location)
      (hprot : ProtectedByBase store r location) (hG : G r) :
      G (LVal.base lv) := by
    cases lv with
    | var x =>
        have hlocEq : location = VariableProjection x := by
          simp [ProgramStore.loc] at hloc
          exact hloc.symm
        subst hlocEq
        have hxr : x = r := protectedByBase_not_var_owned hheap hprot
        simpa [LVal.base, hxr] using hG
    | deref u =>
        have hMlocEx : ∃ M, store.loc u = some M := by
          cases hM : store.loc u with
          | none => simp [ProgramStore.loc, hM] at hloc
          | some M => exact ⟨M, rfl⟩
        rcases hMlocEx with ⟨M, hMloc⟩
        cases htyping with
        | box hsource =>
            rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe
                hsource hMloc with
              ⟨rootM, slotM, viewTyM, slotLt, hprotM, hrankM, hslotM,
                hvalidM, hstrengthM, _hbound, _hborrowsM, _hcontainsM,
                _rootEnvSlot, _rootValue, _hrootEnvSlot, _hrootValue,
                _hdescent⟩
            rcases slotM with ⟨middleValue, middleLifetime⟩
            cases hvalidM with
            | @box owned ownedSlot innerView hownedSlot _hinner =>
                have hderefLoc : store.loc (.deref u) = some owned := by
                  simp [ProgramStore.loc, hMloc, hslotM]
                have hlocEq : location = owned := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                have hprotM' : ProtectedByBase store r M :=
                  ProtectedByBase.pred_of_ownsAt hvalidStore hheap hprot
                    ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
                have hres :=
                  go hφ hwellFormed hsafe hvalidStore hheap hcollapse hsource
                    hMloc hprotM' hG
                simpa [LVal.base] using hres
            | unit | int | undef =>
                cases hstrengthM
            | @borrow targetLoc mutable' targets' witness hmemW hlocW =>
                cases hstrengthM
            | @boxFull owned ownedSlot innerTy hownedSlot _hinner =>
                cases hstrengthM
            | @undefOf _ _ hiddenOuter hskel hstrength =>
                cases hstrengthM
        | boxFull hsource =>
            rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe
                hsource hMloc with
              ⟨rootM, slotM, viewTyM, slotLt, hprotM, hrankM, hslotM,
                hvalidM, hstrengthM, _hbound, _hborrowsM, _hcontainsM,
                _rootEnvSlot, _rootValue, _hrootEnvSlot, _hrootValue,
                _hdescent⟩
            rcases slotM with ⟨middleValue, middleLifetime⟩
            cases hvalidM with
            | @boxFull owned ownedSlot innerView hownedSlot _hinner =>
                have hderefLoc : store.loc (.deref u) = some owned := by
                  simp [ProgramStore.loc, hMloc, hslotM]
                have hlocEq : location = owned := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                have hprotM' : ProtectedByBase store r M :=
                  ProtectedByBase.pred_of_ownsAt hvalidStore hheap hprot
                    ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
                have hres :=
                  go hφ hwellFormed hsafe hvalidStore hheap hcollapse hsource
                    hMloc hprotM' hG
                simpa [LVal.base] using hres
            | unit | int | undef =>
                cases hstrengthM
            | @borrow targetLoc mutable' targets' witness hmemW hlocW =>
                cases hstrengthM
            | @box owned ownedSlot innerView hownedSlot _hinner =>
                cases hstrengthM
            | @undefOf _ _ hiddenOuter hskel hstrength =>
                cases hstrengthM
        | borrow hsource htargets =>
            rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe
                hsource hMloc with
              ⟨rootM, slotM, viewTyM, slotLt, hprotM, hrankM, hslotM,
                hvalidM, hstrengthM, hbound, hborrowsM, hcontainsM,
                _rootEnvSlot, _rootValue, _hrootEnvSlot, _hrootValue,
                _hdescent⟩
            rcases slotM with ⟨middleValue, middleLifetime⟩
            cases hvalidM with
            | @borrow targetLoc mutable' targets' witness hmemW hlocW =>
                have hderefLoc : store.loc (.deref u) = some targetLoc := by
                  simp [ProgramStore.loc, hMloc, hslotM]
                have hlocEq : location = targetLoc := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                rcases hborrowsM PartialTyContains.here witness hmemW with
                  ⟨witnessTy, witnessLifetime, hwitnessTyping, _houtlives,
                    _hbase⟩
                have hwitnessRank : φ (LVal.base witness) < φ rootM := by
                  refine hbound (LVal.base witness) ?_
                  simpa [PartialTy.vars, Ty.vars] using List.mem_map_of_mem hmemW
                have hcallRank :
                    φ (LVal.base witness) < φ (LVal.base u) :=
                  lt_of_lt_of_le hwitnessRank hrankM
                have hGwitness : G (LVal.base witness) :=
                  go hφ hwellFormed hsafe hvalidStore hheap hcollapse
                    hwitnessTyping hlocW hprot hG
                have hGrootM : G rootM :=
                  hcollapse rootM mutable' targets' witness
                    (hcontainsM PartialTyContains.here) hmemW hGwitness
                have hres :=
                  go hφ hwellFormed hsafe hvalidStore hheap hcollapse hsource
                    hMloc hprotM hGrootM
                simpa [LVal.base] using hres
            | unit | int | undef =>
                cases hstrengthM
            | @box owned ownedSlot innerView hownedSlot _hinner =>
                cases hstrengthM
            | @boxFull owned ownedSlot innerTy hownedSlot _hinner =>
                cases hstrengthM
            | @undefOf _ _ hiddenOuter hskel hstrength =>
                cases hstrengthM
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)

/-- Every read of a resolution chain is itself the resolution of a typed
prefix sharing the chain's base. -/
theorem RuntimeFrame.locReads_resolved_prefix {store : ProgramStore}
    {env : Env} {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {location : Location} :
    LValTyping env lv pt lifetime →
    RuntimeFrame.LocReads store lv location →
    ∃ w ptW ltW,
      LValTyping env w ptW ltW ∧
      LVal.base w = LVal.base lv ∧
      store.loc w = some location := by
  intro htyping hreads
  induction hreads generalizing pt lifetime with
  | @here u readLoc huLoc =>
      cases htyping with
      | box hsource => exact ⟨u, _, _, hsource, rfl, huLoc⟩
      | boxFull hsource => exact ⟨u, _, _, hsource, rfl, huLoc⟩
      | borrow hsource htargets => exact ⟨u, _, _, hsource, rfl, huLoc⟩
  | @there u readLoc hinner ih =>
      cases htyping with
      | box hsource =>
          rcases ih hsource with ⟨w, ptW, ltW, hw, hbase, hwLoc⟩
          exact ⟨w, ptW, ltW, hw, hbase, hwLoc⟩
      | boxFull hsource =>
          rcases ih hsource with ⟨w, ptW, ltW, hw, hbase, hwLoc⟩
          exact ⟨w, ptW, ltW, hw, hbase, hwLoc⟩
      | borrow hsource htargets =>
          rcases ih hsource with ⟨w, ptW, ltW, hw, hbase, hwLoc⟩
          exact ⟨w, ptW, ltW, hw, hbase, hwLoc⟩

/-- Reads version of the guarded-base chase. -/
theorem RuntimeFrame.locReads_protected_guarded_base {store : ProgramStore}
    {env : Env} {current : Lifetime} {φ : Name → Nat} {G : Name → Prop}
    {lv : LVal} {pt : PartialTy} {lifetime : Lifetime} {location : Location}
    {r : Name} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ container mutable ts t, env ⊢ container ↝ (.borrow mutable ts) →
      t ∈ ts → G (LVal.base t) → G container) →
    LValTyping env lv pt lifetime →
    RuntimeFrame.LocReads store lv location →
    ProtectedByBase store r location →
    G r →
    G (LVal.base lv) := by
  intro hφ hwellFormed hsafe hvalidStore hheap hcollapse htyping hreads hprot
    hG
  rcases RuntimeFrame.locReads_resolved_prefix htyping hreads with
    ⟨w, ptW, ltW, hw, hbase, hwLoc⟩
  have hres :=
    RuntimeFrame.loc_protected_guarded_base hφ hwellFormed hsafe hvalidStore
      hheap hcollapse hw hwLoc hprot hG
  rw [hbase] at hres
  exact hres

/-! ### The write's authority guard (Appendix 9.6 deref-assign support)

The deref-assignment's authority chain: starting from the written base, the
bases of the targets of guarded mutable-borrow nodes.  Memberships carry the
container's dependency kill, so borrow safety collapses any observer with a
dependency inside the written tree onto a member whose kill refutes it.
-/

/-- The slot variable's stored value has no borrow-resolution dependency on
the written location. -/
def SlotDepKill (store : ProgramStore) (env : Env) (leaf : Location)
    (z : Name) : Prop :=
  ∀ zslot value,
    env.slotAt z = some zslot →
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := zslot.lifetime } →
    ¬ RuntimeFrame.BorrowDependency store value zslot.ty leaf

/-- The write's guard set. -/
inductive WriteGuarded (store : ProgramStore) (env : Env) (leaf : Location)
    (base₀ : Name) : Name → Prop where
  | base :
      SlotDepKill store env leaf base₀ →
      WriteGuarded store env leaf base₀ base₀
  | step {container z : Name} {targets : List LVal} {t : LVal} :
      WriteGuarded store env leaf base₀ container →
      env ⊢ container ↝ (.borrow true targets) →
      t ∈ targets →
      LVal.base t = z →
      SlotDepKill store env leaf container →
      WriteGuarded store env leaf base₀ z

/-- Borrow safety collapses any borrow node targeting a guarded base onto a
guarded container carrying a dependency kill. -/
theorem WriteGuarded.collapse_kill {store : ProgramStore} {env : Env}
    {leaf : Location} {base₀ : Name}
    (hborrowSafe : BorrowSafeEnv env)
    (hnotWP : ¬ WriteProhibited env (.var base₀)) :
    ∀ {c : Name} {mutable : Bool} {ts : List LVal} {t : LVal},
      env ⊢ c ↝ (.borrow mutable ts) →
      t ∈ ts →
      WriteGuarded store env leaf base₀ (LVal.base t) →
      WriteGuarded store env leaf base₀ c ∧ SlotDepKill store env leaf c := by
  intro c mutable ts t hnode hmem hG
  generalize hz : LVal.base t = z at hG
  cases hG with
  | base _hkill =>
      exfalso
      apply hnotWP
      cases mutable with
      | true =>
          exact Or.inl ⟨c, ts, t, hnode, hmem,
            by simpa [PathConflicts, LVal.base] using hz⟩
      | false =>
          exact Or.inr ⟨c, ts, t, hnode, hmem,
            by simpa [PathConflicts, LVal.base] using hz⟩
  | @step container _z targets' t' hGc hnode' hmem' hbase' hkill' =>
      have hconflict : t' ⋈ t := by
        simpa [PathConflicts, hbase'] using hz.symm
      have hceq : container = c :=
        hborrowSafe container c mutable targets' ts t' t hnode' hnode hmem'
          hmem hconflict
      subst hceq
      exact ⟨hGc, hkill'⟩

/--
The runtime-selected write guard.

Unlike `WriteGuarded`, each step records the concrete evidence-selected mutable
borrow target that moved the guard.  This is the local invariant needed for
relaxed joins: collapse can compare selected runtime borrow nodes instead of
all static targets in the joined approximation.
-/
inductive RuntimeWriteGuarded (store : ProgramStore) (env : Env)
    (leaf : Location) (base₀ : Name) : Name → Prop where
  | base :
      SlotDepKill store env leaf base₀ →
      RuntimeWriteGuarded store env leaf base₀ base₀
  | step {container z : Name} {slot : EnvSlot} {value : PartialValue}
      {evidence : RuntimeFrame.ValidPartialValueEvidence store value slot.ty}
      {targets : List LVal} {t : LVal} :
      RuntimeWriteGuarded store env leaf base₀ container →
      env.slotAt container = some slot →
      store.slotAt (VariableProjection container) =
        some { value := value, lifetime := slot.lifetime } →
      RuntimeFrame.EvidenceSelectedBorrow store evidence true targets t →
      LVal.base t = z →
      SlotDepKill store env leaf container →
      RuntimeWriteGuarded store env leaf base₀ z

/--
Selected runtime borrow safety collapses a selected target guard back to its
container.

This is the non-global replacement for `WriteGuarded.collapse_kill`: the
mutable borrow that produced the guard and the borrow being collapsed must both
come from concrete runtime evidence.
-/
theorem RuntimeWriteGuarded.collapse_kill {store : ProgramStore} {env : Env}
    {leaf : Location} {base₀ : Name}
    (hselectedSafe : RuntimeFrame.RuntimeSelectedBorrowSafe store env)
    (hnotWP : ¬ WriteProhibited env (.var base₀)) :
    ∀ {c : Name} {slot : EnvSlot} {value : PartialValue}
      {evidence : RuntimeFrame.ValidPartialValueEvidence store value slot.ty}
      {mutable : Bool} {ts : List LVal} {t : LVal},
      env.slotAt c = some slot →
      store.slotAt (VariableProjection c) =
        some { value := value, lifetime := slot.lifetime } →
      RuntimeFrame.EvidenceSelectedBorrow store evidence mutable ts t →
      RuntimeWriteGuarded store env leaf base₀ (LVal.base t) →
      RuntimeWriteGuarded store env leaf base₀ c ∧
        SlotDepKill store env leaf c := by
  intro c slot value evidence mutable ts t hslot hstore hselected hG
  generalize hz : LVal.base t = z at hG
  cases hG with
  | base hkill =>
      exfalso
      rcases RuntimeFrame.EvidenceSelectedBorrow.contains hselected with
        ⟨hcontains, hmem⟩
      apply hnotWP
      cases mutable with
      | true =>
          exact Or.inl ⟨c, ts, t, ⟨slot, hslot, hcontains⟩, hmem,
            by simpa [PathConflicts, LVal.base] using hz⟩
      | false =>
          exact Or.inr ⟨c, ts, t, ⟨slot, hslot, hcontains⟩, hmem,
            by simpa [PathConflicts, LVal.base] using hz⟩
  | @step container _z stepSlot stepValue stepEvidence targets' t' hGc
      hstepSlot hstepStore hstepSelected hbase' hkill' =>
      have hconflict : t' ⋈ t := by
        simpa [PathConflicts, hbase'] using hz.symm
      have hceq : container = c :=
        hselectedSafe container c stepSlot slot stepValue value hstepSlot
          hslot hstepStore hstore stepEvidence evidence mutable targets' ts
          t' t hstepSelected hselected hconflict
      subst hceq
      exact ⟨hGc, hkill'⟩

/--
Provider-backed runtime write guard.

Each mutable-borrow step is recorded specifically through the chosen runtime
evidence provider, so collapse can consume `RuntimeSelectedBorrowSafeWith`
instead of the old all-evidence `RuntimeSelectedBorrowSafe`.
-/
inductive RuntimeWriteGuardedWith (store : ProgramStore) (env : Env)
    (evidenceOf : RuntimeFrame.RuntimeEvidenceProvider store env)
    (leaf : Location) (base₀ : Name) : Name → Prop where
  | base :
      SlotDepKill store env leaf base₀ →
      RuntimeWriteGuardedWith store env evidenceOf leaf base₀ base₀
  | step {container z : Name} {slot : EnvSlot} {value : PartialValue}
      {targets : List LVal} {t : LVal} :
      RuntimeWriteGuardedWith store env evidenceOf leaf base₀ container →
      (hslot : env.slotAt container = some slot) →
      (hstore : store.slotAt (VariableProjection container) =
        some { value := value, lifetime := slot.lifetime }) →
      RuntimeFrame.EvidenceSelectedBorrow store
        (evidenceOf container slot value hslot hstore) true targets t →
      LVal.base t = z →
      SlotDepKill store env leaf container →
      RuntimeWriteGuardedWith store env evidenceOf leaf base₀ z

theorem RuntimeWriteGuardedWith.forget {store : ProgramStore} {env : Env}
    {evidenceOf : RuntimeFrame.RuntimeEvidenceProvider store env}
    {leaf : Location} {base₀ r : Name} :
    RuntimeWriteGuardedWith store env evidenceOf leaf base₀ r →
    RuntimeWriteGuarded store env leaf base₀ r := by
  intro hguard
  induction hguard with
  | base hkill =>
      exact RuntimeWriteGuarded.base hkill
  | step hGc hslot hstore hselected hbase hkill ih =>
      exact RuntimeWriteGuarded.step ih hslot hstore hselected hbase hkill

theorem RuntimeWriteGuardedWith.collapse_kill {store : ProgramStore}
    {env : Env} {evidenceOf : RuntimeFrame.RuntimeEvidenceProvider store env}
    {leaf : Location} {base₀ : Name}
    (hselectedSafe :
      RuntimeFrame.RuntimeSelectedBorrowSafeWith store env evidenceOf)
    (hnotWP : ¬ WriteProhibited env (.var base₀)) :
    ∀ {c : Name} {slot : EnvSlot} {value : PartialValue}
      {mutable : Bool} {ts : List LVal} {t : LVal}
      (hslot : env.slotAt c = some slot)
      (hstore : store.slotAt (VariableProjection c) =
        some { value := value, lifetime := slot.lifetime }),
      RuntimeFrame.EvidenceSelectedBorrow store
        (evidenceOf c slot value hslot hstore) mutable ts t →
      RuntimeWriteGuardedWith store env evidenceOf leaf base₀ (LVal.base t) →
      RuntimeWriteGuardedWith store env evidenceOf leaf base₀ c ∧
        SlotDepKill store env leaf c := by
  intro c slot value mutable ts t hslot hstore hselected hG
  generalize hz : LVal.base t = z at hG
  cases hG with
  | base hkill =>
      exfalso
      rcases RuntimeFrame.EvidenceSelectedBorrow.contains hselected with
        ⟨hcontains, hmem⟩
      apply hnotWP
      cases mutable with
      | true =>
          exact Or.inl ⟨c, ts, t, ⟨slot, hslot, hcontains⟩, hmem,
            by simpa [PathConflicts, LVal.base] using hz⟩
      | false =>
          exact Or.inr ⟨c, ts, t, ⟨slot, hslot, hcontains⟩, hmem,
            by simpa [PathConflicts, LVal.base] using hz⟩
  | @step container _z stepSlot stepValue targets' t' hGc hstepSlot
      hstepStore hstepSelected hbase' hkill' =>
      have hconflict : t' ⋈ t := by
        simpa [PathConflicts, hbase'] using hz.symm
      have hceq : container = c :=
        hselectedSafe container c stepSlot slot stepValue value hstepSlot
          hslot hstepStore hstore mutable targets' ts t' t hstepSelected
          hselected hconflict
      subst hceq
      exact ⟨hGc, hkill'⟩

theorem RuntimeFrame.loc_protected_runtimeGuarded_base {store : ProgramStore}
    {env : Env} {current : Lifetime} {φ : Name → Nat}
    {leaf : Location} {base₀ : Name}
    {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {location : Location} {r : Name} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    RuntimeFrame.RuntimeSelectedBorrowSafe store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ¬ WriteProhibited env (.var base₀) →
    LValTyping env lv pt lifetime →
    store.loc lv = some location →
    ProtectedByBase store r location →
    RuntimeWriteGuarded store env leaf base₀ r →
    RuntimeWriteGuarded store env leaf base₀ (LVal.base lv) := by
  intro hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
    htyping hloc hprot hG
  exact go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
    htyping hloc hprot hG
where
  go {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {leaf : Location} {base₀ : Name}
      {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
      {location : Location} {r : Name}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ≈ₛ env)
      (hselectedSafe : RuntimeFrame.RuntimeSelectedBorrowSafe store env)
      (hvalidStore : ValidStore store) (hheap : StoreOwnerTargetsHeap store)
      (hnotWP : ¬ WriteProhibited env (.var base₀))
      (htyping : LValTyping env lv pt lifetime)
      (hloc : store.loc lv = some location)
      (hprot : ProtectedByBase store r location)
      (hG : RuntimeWriteGuarded store env leaf base₀ r) :
      RuntimeWriteGuarded store env leaf base₀ (LVal.base lv) := by
    cases lv with
    | var x =>
        have hlocEq : location = VariableProjection x := by
          simp [ProgramStore.loc] at hloc
          exact hloc.symm
        subst hlocEq
        have hxr : x = r := protectedByBase_not_var_owned hheap hprot
        simpa [LVal.base, hxr] using hG
    | deref u =>
        have hsourceTyped :
            ∃ ptu ltu, LValTyping env u ptu ltu ∧
              ((∃ inner, ptu = .box inner) ∨
                (∃ inner, ptu = .ty (.box inner)) ∨
                (∃ mutable targets, ptu = .ty (.borrow mutable targets))) := by
          cases htyping with
          | box hsource => exact ⟨_, _, hsource, Or.inl ⟨_, rfl⟩⟩
          | boxFull hsource => exact ⟨_, _, hsource, Or.inr (Or.inl ⟨_, rfl⟩)⟩
          | borrow hsource htargets =>
              exact ⟨_, _, hsource, Or.inr (Or.inr ⟨_, _, rfl⟩)⟩
        rcases hsourceTyped with ⟨ptu, ltu, hsource, hsourceShape⟩
        have hMlocEx : ∃ M, store.loc u = some M := by
          cases hM : store.loc u with
          | none => simp [ProgramStore.loc, hM] at hloc
          | some M => exact ⟨M, rfl⟩
        rcases hMlocEx with ⟨M, hMloc⟩
        rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe hsource
            hMloc with
          ⟨rootM, slotM, viewTyM, slotLt, hprotM, hrankM, hslotM,
            hvalidM, hstrengthM, hbound, hborrowsM, hcontainsM, rootEnvSlot,
            rootValue, hrootEnvSlot, hrootValue, hdescentM⟩
        rcases slotM with ⟨middleValue, middleLifetime⟩
        cases hvalidM with
        | unit | int | undef =>
            simp [ProgramStore.loc, hMloc, hslotM] at hloc
          | @undefOf _ _ hiddenOuter hskel hstrength =>
              rcases hsourceShape with ⟨inner, hshape⟩ | hsourceShape
              · rw [hshape] at hstrengthM
                exact False.elim
                  (PartialTyStrengthens.not_undef_to_box hstrengthM)
              rcases hsourceShape with ⟨inner, hshape⟩ |
                ⟨mutable, targets, hshape⟩
              · rw [hshape] at hstrengthM
                exact False.elim
                  (PartialTyStrengthens.not_undef_to_ty hstrengthM)
              · rw [hshape] at hstrengthM
                exact False.elim
                  (PartialTyStrengthens.not_undef_to_ty hstrengthM)
        | @box owned ownedSlot innerView hownedSlot _hinner =>
            have hderefLoc : store.loc (.deref u) = some owned := by
              simp [ProgramStore.loc, hMloc, hslotM]
            have hlocEq : location = owned := by
              rw [hloc] at hderefLoc
              exact Option.some.inj hderefLoc
            subst hlocEq
            have hprotM' : ProtectedByBase store r M :=
              ProtectedByBase.pred_of_ownsAt hvalidStore hheap hprot
                ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
            have hres :=
              go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
                hsource hMloc hprotM' hG
            simpa [LVal.base] using hres
        | @boxFull owned ownedSlot innerTy hownedSlot _hinner =>
            have hderefLoc : store.loc (.deref u) = some owned := by
              simp [ProgramStore.loc, hMloc, hslotM]
            have hlocEq : location = owned := by
              rw [hloc] at hderefLoc
              exact Option.some.inj hderefLoc
            subst hlocEq
            have hprotM' : ProtectedByBase store r M :=
              ProtectedByBase.pred_of_ownsAt hvalidStore hheap hprot
                ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
            have hres :=
              go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
                hsource hMloc hprotM' hG
            simpa [LVal.base] using hres
        | @borrow targetLoc mutable' targets' witness hmemW hlocW =>
            have hderefLoc : store.loc (.deref u) = some targetLoc := by
              simp [ProgramStore.loc, hMloc, hslotM]
            have hlocEq : location = targetLoc := by
              rw [hloc] at hderefLoc
              exact Option.some.inj hderefLoc
            subst hlocEq
            rcases hborrowsM PartialTyContains.here witness hmemW with
              ⟨witnessTy, witnessLifetime, hwitnessTyping, _houtlives, _hbase⟩
            have hwitnessRank : φ (LVal.base witness) < φ rootM := by
              refine hbound (LVal.base witness) ?_
              simpa [PartialTy.vars, Ty.vars] using List.mem_map_of_mem hmemW
            have hcallRank :
                φ (LVal.base witness) < φ (LVal.base u) :=
              lt_of_lt_of_le hwitnessRank hrankM
            have hGwitness :
                RuntimeWriteGuarded store env leaf base₀ (LVal.base witness) :=
              go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
                hwitnessTyping hlocW hprot hG
            let cellEvidence :
                RuntimeFrame.ValidPartialValueEvidence store
                  (.value (.ref { location := location, owner := false }))
                  (.ty (.borrow mutable' targets')) :=
              RuntimeFrame.ValidPartialValueEvidence.borrow witness hmemW hlocW
            have hcellSelected :
                RuntimeFrame.EvidenceSelectedBorrow store cellEvidence mutable'
                  targets' witness :=
              RuntimeFrame.EvidenceSelectedBorrow.borrow rfl
            have hrootSelected :
                ∃ rootEvidence :
                    RuntimeFrame.ValidPartialValueEvidence store rootValue
                      rootEnvSlot.ty,
                  RuntimeFrame.EvidenceSelectedBorrow store rootEvidence
                    mutable' targets' witness := by
              rcases hdescentM with hroot | hreach
              · rcases hroot with ⟨hlocationRoot, hviewRoot, hvalueRoot⟩
                rw [← hviewRoot, ← hvalueRoot]
                exact ⟨cellEvidence, hcellSelected⟩
              · exact RuntimeFrame.ReachesSlot.evidenceSelectedBorrow_lift
                  hreach cellEvidence hcellSelected
            rcases hrootSelected with ⟨rootEvidence, hrootSelected⟩
            have hGrootM :
                RuntimeWriteGuarded store env leaf base₀ rootM :=
              (RuntimeWriteGuarded.collapse_kill hselectedSafe hnotWP
                hrootEnvSlot hrootValue hrootSelected hGwitness).1
            have hres :=
              go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
                hsource hMloc hprotM hGrootM
            simpa [LVal.base] using hres
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)

theorem RuntimeFrame.loc_protected_runtimeGuardedWith_base
    {store : ProgramStore} {env : Env}
    {evidenceOf : RuntimeFrame.RuntimeEvidenceProvider store env}
    {current : Lifetime} {φ : Name → Nat}
    {leaf : Location} {base₀ : Name}
    {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {location : Location} {r : Name} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    RuntimeFrame.RuntimeSelectedBorrowSafeWith store env evidenceOf →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ¬ WriteProhibited env (.var base₀) →
    LValTyping env lv pt lifetime →
    store.loc lv = some location →
    ProtectedByBase store r location →
    RuntimeWriteGuardedWith store env evidenceOf leaf base₀ r →
    RuntimeWriteGuardedWith store env evidenceOf leaf base₀ (LVal.base lv) := by
  intro hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
    htyping hloc hprot hG
  exact go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
    htyping hloc hprot hG
where
  go {store : ProgramStore} {env : Env}
      {evidenceOf : RuntimeFrame.RuntimeEvidenceProvider store env}
      {current : Lifetime} {φ : Name → Nat}
      {leaf : Location} {base₀ : Name}
      {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
      {location : Location} {r : Name}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ≈ₛ env)
      (hselectedSafe :
        RuntimeFrame.RuntimeSelectedBorrowSafeWith store env evidenceOf)
      (hvalidStore : ValidStore store) (hheap : StoreOwnerTargetsHeap store)
      (hnotWP : ¬ WriteProhibited env (.var base₀))
      (htyping : LValTyping env lv pt lifetime)
      (hloc : store.loc lv = some location)
      (hprot : ProtectedByBase store r location)
      (hG : RuntimeWriteGuardedWith store env evidenceOf leaf base₀ r) :
      RuntimeWriteGuardedWith store env evidenceOf leaf base₀ (LVal.base lv) := by
    cases lv with
    | var x =>
        have hlocEq : location = VariableProjection x := by
          simp [ProgramStore.loc] at hloc
          exact hloc.symm
        subst hlocEq
        have hxr : x = r := protectedByBase_not_var_owned hheap hprot
        simpa [LVal.base, hxr] using hG
    | deref u =>
        have hsourceTyped :
            ∃ ptu ltu, LValTyping env u ptu ltu ∧
              ((∃ inner, ptu = .box inner) ∨
                (∃ inner, ptu = .ty (.box inner)) ∨
                (∃ mutable targets, ptu = .ty (.borrow mutable targets))) := by
          cases htyping with
          | box hsource => exact ⟨_, _, hsource, Or.inl ⟨_, rfl⟩⟩
          | boxFull hsource => exact ⟨_, _, hsource, Or.inr (Or.inl ⟨_, rfl⟩)⟩
          | borrow hsource htargets =>
              exact ⟨_, _, hsource, Or.inr (Or.inr ⟨_, _, rfl⟩)⟩
        rcases hsourceTyped with ⟨ptu, ltu, hsource, hsourceShape⟩
        have hMlocEx : ∃ M, store.loc u = some M := by
          cases hM : store.loc u with
          | none => simp [ProgramStore.loc, hM] at hloc
          | some M => exact ⟨M, rfl⟩
        rcases hMlocEx with ⟨M, hMloc⟩
        rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe hsource
            hMloc with
          ⟨rootM, slotM, viewTyM, slotLt, hprotM, hrankM, hslotM,
            hvalidM, hstrengthM, hbound, hborrowsM, hcontainsM, rootEnvSlot,
            rootValue, hrootEnvSlot, hrootValue, hdescentM⟩
        rcases slotM with ⟨middleValue, middleLifetime⟩
        cases hvalidM with
        | unit | int | undef =>
            simp [ProgramStore.loc, hMloc, hslotM] at hloc
          | @undefOf _ _ hiddenOuter hskel hstrength =>
              rcases hsourceShape with ⟨inner, hshape⟩ | hsourceShape
              · rw [hshape] at hstrengthM
                exact False.elim
                  (PartialTyStrengthens.not_undef_to_box hstrengthM)
              rcases hsourceShape with ⟨inner, hshape⟩ |
                ⟨mutable, targets, hshape⟩
              · rw [hshape] at hstrengthM
                exact False.elim
                  (PartialTyStrengthens.not_undef_to_ty hstrengthM)
              · rw [hshape] at hstrengthM
                exact False.elim
                  (PartialTyStrengthens.not_undef_to_ty hstrengthM)
        | @box owned ownedSlot innerView hownedSlot _hinner =>
            have hderefLoc : store.loc (.deref u) = some owned := by
              simp [ProgramStore.loc, hMloc, hslotM]
            have hlocEq : location = owned := by
              rw [hloc] at hderefLoc
              exact Option.some.inj hderefLoc
            subst hlocEq
            have hprotM' : ProtectedByBase store r M :=
              ProtectedByBase.pred_of_ownsAt hvalidStore hheap hprot
                ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
            have hres :=
              go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
                hsource hMloc hprotM' hG
            simpa [LVal.base] using hres
        | @boxFull owned ownedSlot innerTy hownedSlot _hinner =>
            have hderefLoc : store.loc (.deref u) = some owned := by
              simp [ProgramStore.loc, hMloc, hslotM]
            have hlocEq : location = owned := by
              rw [hloc] at hderefLoc
              exact Option.some.inj hderefLoc
            subst hlocEq
            have hprotM' : ProtectedByBase store r M :=
              ProtectedByBase.pred_of_ownsAt hvalidStore hheap hprot
                ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
            have hres :=
              go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
                hsource hMloc hprotM' hG
            simpa [LVal.base] using hres
        | @borrow targetLoc mutable' targets' _witness _hmemW _hlocW =>
            have hderefLoc : store.loc (.deref u) = some targetLoc := by
              simp [ProgramStore.loc, hMloc, hslotM]
            have hlocEq : location = targetLoc := by
              rw [hloc] at hderefLoc
              exact Option.some.inj hderefLoc
            subst hlocEq
            rcases rootEnvSlot with ⟨rootTy, rootLifetime⟩
            let rootEvidence :=
              evidenceOf rootM
                ({ ty := rootTy, lifetime := rootLifetime } : EnvSlot)
                rootValue hrootEnvSlot hrootValue
            have hproviderSelected :
                ∃ witness,
                  RuntimeFrame.EvidenceSelectedBorrow store rootEvidence
                    mutable' targets' witness ∧
              witness ∈ targets' ∧ store.loc witness = some location := by
              rcases hdescentM with hroot | hreach
              · rcases hroot with ⟨_hlocationRoot, hviewRoot, hvalueRoot⟩
                cases hvalueRoot
                cases hviewRoot
                rcases RuntimeFrame.ValidPartialValueEvidence.borrow_selected
                    rootEvidence with
                  ⟨witness, hselected, hmem, hlocWitness⟩
                exact ⟨witness, hselected, hmem, hlocWitness⟩
              · rcases RuntimeFrame.ReachesSlot.evidence_at hreach rootEvidence
                  with ⟨slotEvidence, hlift⟩
                rcases RuntimeFrame.ValidPartialValueEvidence.borrow_selected
                    slotEvidence with
                  ⟨witness, hselected, hmem, hlocWitness⟩
                exact ⟨witness, hlift hselected, hmem, hlocWitness⟩
            rcases hproviderSelected with
              ⟨witness, hrootSelected, hmemW, hlocW⟩
            rcases hborrowsM PartialTyContains.here witness hmemW with
              ⟨witnessTy, witnessLifetime, hwitnessTyping, _houtlives, _hbase⟩
            have hwitnessRank : φ (LVal.base witness) < φ rootM := by
              refine hbound (LVal.base witness) ?_
              simpa [PartialTy.vars, Ty.vars] using List.mem_map_of_mem hmemW
            have hcallRank :
                φ (LVal.base witness) < φ (LVal.base u) :=
              lt_of_lt_of_le hwitnessRank hrankM
            have hGwitness :
                RuntimeWriteGuardedWith store env evidenceOf leaf base₀
                  (LVal.base witness) :=
              go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
                hwitnessTyping hlocW hprot hG
            have hGrootM :
                RuntimeWriteGuardedWith store env evidenceOf leaf base₀ rootM :=
              (RuntimeWriteGuardedWith.collapse_kill hselectedSafe hnotWP
                hrootEnvSlot hrootValue hrootSelected hGwitness).1
            have hres :=
              go hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP
                hsource hMloc hprotM hGrootM
            simpa [LVal.base] using hres
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)

theorem RuntimeFrame.locReads_protected_runtimeGuarded_base
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {φ : Name → Nat} {leaf : Location} {base₀ : Name}
    {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {location : Location} {r : Name} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    RuntimeFrame.RuntimeSelectedBorrowSafe store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ¬ WriteProhibited env (.var base₀) →
    LValTyping env lv pt lifetime →
    RuntimeFrame.LocReads store lv location →
    ProtectedByBase store r location →
    RuntimeWriteGuarded store env leaf base₀ r →
    RuntimeWriteGuarded store env leaf base₀ (LVal.base lv) := by
  intro hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP htyping
    hreads hprot hG
  rcases RuntimeFrame.locReads_resolved_prefix htyping hreads with
    ⟨w, ptW, ltW, hw, hbase, hwLoc⟩
  have hres :=
    RuntimeFrame.loc_protected_runtimeGuarded_base hφ hwellFormed hsafe
      hselectedSafe hvalidStore hheap hnotWP hw hwLoc hprot hG
  rw [hbase] at hres
  exact hres

theorem RuntimeFrame.locReads_protected_runtimeGuardedWith_base
    {store : ProgramStore} {env : Env}
    {evidenceOf : RuntimeFrame.RuntimeEvidenceProvider store env}
    {current : Lifetime} {φ : Name → Nat}
    {leaf : Location} {base₀ : Name}
    {lv : LVal} {pt : PartialTy} {lifetime : Lifetime}
    {location : Location} {r : Name} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    RuntimeFrame.RuntimeSelectedBorrowSafeWith store env evidenceOf →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ¬ WriteProhibited env (.var base₀) →
    LValTyping env lv pt lifetime →
    RuntimeFrame.LocReads store lv location →
    ProtectedByBase store r location →
    RuntimeWriteGuardedWith store env evidenceOf leaf base₀ r →
    RuntimeWriteGuardedWith store env evidenceOf leaf base₀ (LVal.base lv) := by
  intro hφ hwellFormed hsafe hselectedSafe hvalidStore hheap hnotWP htyping
    hreads hprot hG
  rcases RuntimeFrame.locReads_resolved_prefix htyping hreads with
    ⟨w, ptW, ltW, hw, hbase, hwLoc⟩
  have hres :=
    RuntimeFrame.loc_protected_runtimeGuardedWith_base hφ hwellFormed hsafe
      hselectedSafe hvalidStore hheap hnotWP hw hwLoc hprot hG
  rw [hbase] at hres
  exact hres

/-- The spine's leaf type is box-contained in the spine's root type. -/
theorem StoreOwnerSpine.contains_leafTy {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} {path : Path} {mutable : Bool}
    {targets : List LVal} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    leafTy = .ty (.borrow mutable targets) →
    PartialTyContains ty (.borrow mutable targets) := by
  intro hspine
  induction hspine with
  | nil _ _ =>
      intro h
      subst h
      exact PartialTyContains.here
  | box _hslot _howner _htail ih =>
      intro h
      exact PartialTyContains.box (ih h)
  | boxFull _hslot _howner _htail ih =>
      intro h
      exact PartialTyContains.tyBox (ih h)

/-- A nonempty spine is a slot-typed value descent of its root value. -/
theorem StoreOwnerSpine.reachesSlot_of_spine {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    path ≠ [] →
    RuntimeFrame.ReachesSlot store slot.value ty leaf leafSlot leafTy := by
  intro hspine
  induction hspine with
  | nil _ _ =>
      intro h
      exact absurd rfl h
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro _hne
      rw [howner]
      cases htail with
      | nil hleafSlot hleafValid =>
          simpa [owningRef] using
            RuntimeFrame.ReachesSlot.boxHere hleafSlot hleafValid
      | box hslot₂ howner₂ htail₂ =>
          have hownedSlotAt :
              store.slotAt owned = some ownedSlot :=
            StoreOwnerSpine.storage_slot
              (StoreOwnerSpine.box hslot₂ howner₂ htail₂)
          simpa [owningRef] using
            RuntimeFrame.ReachesSlot.boxInner hownedSlotAt (ih (by simp))
      | boxFull hslot₂ howner₂ htail₂ =>
          have hownedSlotAt :
              store.slotAt owned = some ownedSlot :=
            StoreOwnerSpine.storage_slot
              (StoreOwnerSpine.boxFull hslot₂ howner₂ htail₂)
          simpa [owningRef] using
            RuntimeFrame.ReachesSlot.boxInner hownedSlotAt (ih (by simp))
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro _hne
      rw [howner]
      cases htail with
      | nil hleafSlot hleafValid =>
          simpa [owningRef] using
            RuntimeFrame.ReachesSlot.boxFullHere hleafSlot hleafValid
      | boxFull hslot₂ howner₂ htail₂ =>
          have hownedSlotAt :
              store.slotAt owned = some ownedSlot :=
            StoreOwnerSpine.storage_slot
              (StoreOwnerSpine.boxFull hslot₂ howner₂ htail₂)
          simpa [owningRef] using
            RuntimeFrame.ReachesSlot.boxFullInner hownedSlotAt (ih (by simp))

/-- A slot-typed value descent can be viewed as an owner spine from the storage
slot whose value starts the descent. -/
theorem StoreOwnerSpine.of_reachesSlot {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {value : PartialValue} {ty leafTy : PartialTy} :
    store.slotAt storage = some slot →
    slot.value = value →
    RuntimeFrame.ReachesSlot store value ty leaf leafSlot leafTy →
    ∃ path,
      StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy ∧
        path ≠ [] := by
  intro hslot hvalue hreach
  induction hreach generalizing storage slot with
  | @boxHere location leafSlot inner hleafSlot hleafValid =>
      refine ⟨[()], ?_, by simp⟩
      exact StoreOwnerSpine.box hslot (by simpa [owningRef] using hvalue)
        (StoreOwnerSpine.nil hleafSlot hleafValid)
  | @boxInner location reached firstSlot reachedSlot inner reachedTy hfirstSlot
      _hinner ih =>
      rcases ih hfirstSlot rfl with ⟨path, htail, _hnonempty⟩
      refine ⟨() :: path, ?_, by simp⟩
      exact StoreOwnerSpine.box hslot (by simpa [owningRef] using hvalue)
        htail
  | @boxFullHere location leafSlot innerTy hleafSlot hleafValid =>
      refine ⟨[()], ?_, by simp⟩
      exact StoreOwnerSpine.boxFull hslot (by simpa [owningRef] using hvalue)
        (StoreOwnerSpine.nil hleafSlot hleafValid)
  | @boxFullInner location reached firstSlot reachedSlot innerTy reachedTy
      hfirstSlot _hinner ih =>
      rcases ih hfirstSlot rfl with ⟨path, htail, _hnonempty⟩
      refine ⟨() :: path, ?_, by simp⟩
      exact StoreOwnerSpine.boxFull hslot (by simpa [owningRef] using hvalue)
        htail

/-- The write's walk crosses the spine's borrow node: the node is mutable and
the walk fans out over its targets. -/
theorem StoreOwnerSpine.updateAtPath_node_fanout {store : ProgramStore}
    {env writeEnv : Env} {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy updatedTy : PartialTy} {mutable : Bool} {targets : List LVal}
    {spinePath suffix : List Unit} {rank : Nat} {rhsTy : Ty} :
    StoreOwnerSpine store storage slot ty spinePath leaf leafSlot leafTy →
    leafTy = .ty (.borrow mutable targets) →
    UpdateAtPath rank env (spinePath ++ (() :: suffix)) ty rhsTy writeEnv
      updatedTy →
    mutable = true ∧
      ∃ env₂, WriteBorrowTargets (rank + 1) env suffix targets rhsTy env₂ := by
  intro hspine
  induction hspine generalizing rank writeEnv updatedTy with
  | nil _ _ =>
      intro hleafTy hupdate
      subst hleafTy
      rcases UpdateAtPath.cons_inv (by simpa using hupdate) with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, hwrites⟩
        cases htyEq
        exact ⟨rfl, _, hwrites⟩
  | box _hslot _howner _htail ih =>
      intro hleafTy hupdate
      rcases UpdateAtPath.cons_inv (by simpa using hupdate) with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, hinner⟩
          cases htyEq
          exact ih hleafTy hinner
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            _hinner⟩
          cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  | boxFull _hslot _howner _htail ih =>
      intro hleafTy hupdate
      rcases UpdateAtPath.cons_inv (by simpa using hupdate) with hbox | hborrow
      · rcases hbox with hbox | hboxFull
        · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
          cases htyEq
        · rcases hboxFull with ⟨inner, updatedInner, htyEq, _hupdatedEq,
            hinner⟩
          cases htyEq
          exact ih hleafTy hinner
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq

/-! ### Strong spine updates (Appendix 9.6 deref-assign support) -/

/-- Replace the leaf of a box spine after `path` dereferences by `.ty ty`. -/
def PartialTy.strongLeafUpdate : PartialTy → List Unit → Ty → PartialTy
  | _, [], ty => .ty ty
  | .box inner, _ :: path, ty => .box (PartialTy.strongLeafUpdate inner path ty)
  | .ty (.box inner), _ :: path, ty =>
      partialTyRebox (PartialTy.strongLeafUpdate (.ty inner) path ty)
  | pt, _ :: _, _ => pt

/-- Pointwise same-shape strengthening between two updates of the same slot. -/
theorem EnvSameShapeStrengthening.update_same {env : Env} {x : Name}
    {strong weak : EnvSlot} :
    strong.lifetime = weak.lifetime →
    PartialTyStrengthens strong.ty weak.ty →
    PartialTy.sameShape strong.ty weak.ty →
    EnvSameShapeStrengthening (env.update x strong) (env.update x weak) := by
  intro hlife hstr hshape
  constructor
  · intro y resultSlot hresultSlot
    by_cases hy : y = x
    · subst hy
      have hresultEq : resultSlot = weak := by
        simpa [Env.update] using hresultSlot.symm
      subst hresultEq
      exact ⟨strong, by simp [Env.update], hlife, hstr, hshape⟩
    · have hold : env.slotAt y = some resultSlot := by
        simpa [Env.update, hy] using hresultSlot
      exact ⟨resultSlot, by simpa [Env.update, hy] using hold, rfl,
        PartialTyStrengthens.reflex, PartialTy.sameShape_refl _⟩
  · intro y sourceSlot hsourceSlot
    by_cases hy : y = x
    · subst hy
      have hsourceEq : sourceSlot = strong := by
        simpa [Env.update] using hsourceSlot.symm
      subst hsourceEq
      exact ⟨weak, by simp [Env.update], hlife⟩
    · exact ⟨sourceSlot, by simpa [Env.update, hy] using hsourceSlot, rfl⟩

/-- Owner spines between the same endpoints have the same path: the descent is
deterministic because each slot stores one owning reference. -/
theorem StoreOwnerSpine.path_unique {store : ProgramStore}
    {storage leaf : Location} {slot₁ : StoreSlot} {ty₁ leafTy₁ : PartialTy}
    {leafSlot₁ : StoreSlot} {path₁ : Path} :
    StoreOwnerSpine store storage slot₁ ty₁ path₁ leaf leafSlot₁ leafTy₁ →
    ∀ {slot₂ : StoreSlot} {ty₂ leafTy₂ : PartialTy} {leafSlot₂ : StoreSlot}
      {path₂ : Path},
      StoreOwnerSpine store storage slot₂ ty₂ path₂ leaf leafSlot₂ leafTy₂ →
      path₁ = path₂ := by
  intro h₁
  induction h₁ with
  | nil hslot _hvalid =>
      intro slot₂ ty₂ leafTy₂ leafSlot₂ path₂ h₂
      cases h₂ with
      | nil _ _ => rfl
      | box hslot₂ howner₂ htail₂ =>
          exact absurd rfl
            (StoreOwnerSpine.leaf_ne_storage_of_cons
              (StoreOwnerSpine.box hslot₂ howner₂ htail₂))
      | boxFull hslot₂ howner₂ htail₂ =>
          exact absurd rfl
            (StoreOwnerSpine.leaf_ne_storage_of_cons
              (StoreOwnerSpine.boxFull hslot₂ howner₂ htail₂))
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro slot₂ ty₂ leafTy₂ leafSlot₂ path₂ h₂
      cases h₂ with
      | nil hslot₂ _ =>
          exact absurd rfl
            (StoreOwnerSpine.leaf_ne_storage_of_cons
              (StoreOwnerSpine.box hslot howner htail))
      | @box _ owned₂ _ _ ownedSlot₂ _ inner₂ _ path₂' hslot₂ howner₂
          htail₂ =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          have hownedEq : owned = owned₂ := by
            have hvalueEq :
                PartialValue.value (owningRef owned) =
                  PartialValue.value (owningRef owned₂) := by
              rw [← howner, hslotEq, howner₂]
            cases hvalueEq
            rfl
          subst hownedEq
          rw [ih htail₂]
      | @boxFull _ owned₂ _ _ ownedSlot₂ _ inner₂ _ path₂' hslot₂ howner₂
          htail₂ =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          have hownedEq : owned = owned₂ := by
            have hvalueEq :
                PartialValue.value (owningRef owned) =
                  PartialValue.value (owningRef owned₂) := by
              rw [← howner, hslotEq, howner₂]
            cases hvalueEq
            rfl
          subst hownedEq
          rw [ih htail₂]
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      intro slot₂ ty₂ leafTy₂ leafSlot₂ path₂ h₂
      cases h₂ with
      | nil hslot₂ _ =>
          exact absurd rfl
            (StoreOwnerSpine.leaf_ne_storage_of_cons
              (StoreOwnerSpine.boxFull hslot howner htail))
      | @box _ owned₂ _ _ ownedSlot₂ _ inner₂ _ path₂' hslot₂ howner₂
          htail₂ =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          have hownedEq : owned = owned₂ := by
            have hvalueEq :
                PartialValue.value (owningRef owned) =
                  PartialValue.value (owningRef owned₂) := by
              rw [← howner, hslotEq, howner₂]
            cases hvalueEq
            rfl
          subst hownedEq
          rw [ih htail₂]
      | @boxFull _ owned₂ _ _ ownedSlot₂ _ inner₂ _ path₂' hslot₂ howner₂
          htail₂ =>
          have hslotEq : slot = slot₂ :=
            Option.some.inj (hslot.symm.trans hslot₂)
          have hownedEq : owned = owned₂ := by
            have hvalueEq :
                PartialValue.value (owningRef owned) =
                  PartialValue.value (owningRef owned₂) := by
              rw [← howner, hslotEq, howner₂]
            cases hvalueEq
            rfl
          subst hownedEq
          rw [ih htail₂]

/-- Spine validity after strongly replacing the leaf contents. -/
theorem StoreOwnerSpine.valid_after_leaf_strong_update {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} {path : Path} {value : Value} {rhsTy : Ty}
    {newSlot : StoreSlot} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    path ≠ [] →
    newSlot.value = .value value →
    ValidPartialValue (store.update leaf newSlot) (.value value) (.ty rhsTy) →
    ValidPartialValue (store.update leaf newSlot) slot.value
      (PartialTy.strongLeafUpdate ty path rhsTy) := by
  intro hspine hpath hnewValue hnewValid
  induction hspine with
  | nil _hslot _hvalid =>
      exact absurd rfl hpath
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases htail with
      | nil hleafSlot _hleafValid =>
          rw [howner]
          have hnewSlotAt :
              (store.update owned newSlot).slotAt owned = some newSlot := by
            simp [ProgramStore.update]
          have hnewSlotValid :
              ValidPartialValue (store.update owned newSlot) newSlot.value
                (.ty rhsTy) := by
            rw [hnewValue]
            exact hnewValid
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            ValidPartialValue.box hnewSlotAt hnewSlotValid
      | box hslot₂ howner₂ htail₂ =>
          rw [howner]
          have htailSpine :
              StoreOwnerSpine store owned ownedSlot _ (() :: _) leaf leafSlot
                leafTy :=
            StoreOwnerSpine.box hslot₂ howner₂ htail₂
          have htailValid :=
            ih (by simp) hnewValid
          have hleafNeOwned : leaf ≠ owned :=
            StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
          have hownedNeLeaf : owned ≠ leaf := fun h => hleafNeOwned h.symm
          have hownedSlotAt :
              (store.update leaf newSlot).slotAt owned = some ownedSlot := by
            rw [RuntimeFrame.ProgramStore.slotAt_update_ne hownedNeLeaf]
            exact StoreOwnerSpine.storage_slot htailSpine
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            ValidPartialValue.box hownedSlotAt htailValid
      | boxFull hslot₂ howner₂ htail₂ =>
          rw [howner]
          have htailSpine :
              StoreOwnerSpine store owned ownedSlot _ (() :: _) leaf leafSlot
                leafTy :=
            StoreOwnerSpine.boxFull hslot₂ howner₂ htail₂
          have htailValid :=
            ih (by simp) hnewValid
          have hleafNeOwned : leaf ≠ owned :=
            StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
          have hownedNeLeaf : owned ≠ leaf := fun h => hleafNeOwned h.symm
          have hownedSlotAt :
              (store.update leaf newSlot).slotAt owned = some ownedSlot := by
            rw [RuntimeFrame.ProgramStore.slotAt_update_ne hownedNeLeaf]
            exact StoreOwnerSpine.storage_slot htailSpine
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            ValidPartialValue.box hownedSlotAt htailValid
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases htail with
      | nil hleafSlot _hleafValid =>
          rw [howner]
          have hnewSlotAt :
              (store.update owned newSlot).slotAt owned = some newSlot := by
            simp [ProgramStore.update]
          have hnewSlotValid :
              ValidPartialValue (store.update owned newSlot) newSlot.value
                (.ty rhsTy) := by
            rw [hnewValue]
            exact hnewValid
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            StoreOwnerSpine.valid_rebox hnewSlotAt hnewSlotValid
      | boxFull hslot₂ howner₂ htail₂ =>
          rw [howner]
          have htailSpine :
              StoreOwnerSpine store owned ownedSlot _ (() :: _) leaf leafSlot
                leafTy :=
            StoreOwnerSpine.boxFull hslot₂ howner₂ htail₂
          have htailValid :=
            ih (by simp) hnewValid
          have hleafNeOwned : leaf ≠ owned :=
            StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
          have hownedNeLeaf : owned ≠ leaf := fun h => hleafNeOwned h.symm
          have hownedSlotAt :
              (store.update leaf newSlot).slotAt owned = some ownedSlot := by
            rw [RuntimeFrame.ProgramStore.slotAt_update_ne hownedNeLeaf]
            exact StoreOwnerSpine.storage_slot htailSpine
          simpa [PartialTy.strongLeafUpdate, owningRef] using
            StoreOwnerSpine.valid_rebox hownedSlotAt htailValid

theorem PartialTyStrengthens.rebox {strong weak : PartialTy} :
    PartialTyStrengthens strong weak →
    PartialTy.sameShape strong weak →
    PartialTyStrengthens (partialTyRebox strong) (partialTyRebox weak) := by
  intro hstr hshape
  cases strong <;> cases weak <;>
    try simp [PartialTy.sameShape] at hshape
  · simpa [partialTyRebox] using PartialTyStrengthens.tyBox hstr
  · simpa [partialTyRebox] using PartialTyStrengthens.box hstr
  · simpa [partialTyRebox] using PartialTyStrengthens.box hstr

theorem PartialTy.sameShape_rebox {strong weak : PartialTy} :
    PartialTy.sameShape strong weak →
    PartialTy.sameShape (partialTyRebox strong) (partialTyRebox weak) := by
  intro hshape
  cases strong with
  | ty strongTy =>
      cases weak with
      | ty weakTy =>
          simpa [partialTyRebox, PartialTy.sameShape, Ty.sameShape] using hshape
      | box weakInner =>
          simp [PartialTy.sameShape] at hshape
      | undef weakTy =>
          simp [PartialTy.sameShape] at hshape
  | box strongInner =>
      cases weak with
      | ty weakTy =>
          simp [PartialTy.sameShape] at hshape
      | box weakInner =>
          simpa [partialTyRebox, PartialTy.sameShape] using hshape
      | undef weakTy =>
          simp [PartialTy.sameShape] at hshape
  | undef strongTy =>
      cases weak with
      | ty weakTy =>
          simp [PartialTy.sameShape] at hshape
      | box weakInner =>
          simp [PartialTy.sameShape] at hshape
      | undef weakTy =>
          simpa [partialTyRebox, PartialTy.sameShape, Ty.sameShape] using hshape

/-- The strong leaf replacement strengthens any actual leaf update along the
same owner spine, with the same shape.  The spine leaf must be initialized
(full), which the assignment branches guarantee via their carried typings. -/
theorem StoreOwnerSpine.strongLeafUpdate_strengthens_updateAtPath
    {store : ProgramStore} {env writeEnv : Env} {rank : Nat}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy updatedTy : PartialTy} {oldLeafTy rhsTy : Ty} {path : Path} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    leafTy = .ty oldLeafTy →
    UpdateAtPath rank env path ty rhsTy writeEnv updatedTy →
    PartialTyStrengthens (PartialTy.strongLeafUpdate ty path rhsTy)
      updatedTy ∧
      PartialTy.sameShape (PartialTy.strongLeafUpdate ty path rhsTy)
        updatedTy := by
  intro hspine hleafTy hupdate
  induction hspine generalizing rank writeEnv updatedTy oldLeafTy with
  | nil _hslot _hvalid =>
      subst hleafTy
      cases hupdate with
      | strong =>
          exact ⟨by
              simpa [PartialTy.strongLeafUpdate] using
                (PartialTyStrengthens.reflex (ty := PartialTy.ty rhsTy)),
            by
              simpa [PartialTy.strongLeafUpdate] using
                PartialTy.sameShape_refl (PartialTy.ty rhsTy)⟩
      | weak hshape hjoin =>
          constructor
          · simpa [PartialTy.strongLeafUpdate] using
              PartialTyUnion.right_strengthens hjoin
          · have hshapeOldJoined :
                PartialTy.sameShape (.ty oldLeafTy) updatedTy :=
              partialTyJoin_ty_left_sameShape hjoin
            have hshapeRhsOld :
                PartialTy.sameShape (.ty rhsTy) (.ty oldLeafTy) :=
              PartialTy.sameShape_symm
                (PartialTy.sameShape_of_shapeCompatible hshape)
            simpa [PartialTy.strongLeafUpdate] using
              PartialTy.sameShape_trans hshapeRhsOld hshapeOldJoined
  | @box storage owned leaf slot ownedSlot leafSlot spineInner leafTy path
      hslot howner htail ih =>
      cases hupdate with
      | @box _env₁ _env₂ _rank _path _inner updatedInner _ty hinnerUpdate =>
          rcases ih hleafTy hinnerUpdate with ⟨hstr, hshape⟩
          constructor
          · change
              PartialTyStrengthens
                (.box (PartialTy.strongLeafUpdate spineInner path rhsTy))
                (.box updatedInner)
            exact PartialTyStrengthens.box hstr
          · change
              PartialTy.sameShape
                (.box (PartialTy.strongLeafUpdate spineInner path rhsTy))
                (.box updatedInner)
            simpa [PartialTy.sameShape] using hshape
  | @boxFull storage owned leaf slot ownedSlot leafSlot spineInner leafTy path
      hslot howner htail ih =>
      cases hupdate with
      | @boxFull _env₁ _env₂ _rank _path _inner updatedInner _ty hinnerUpdate =>
          rcases ih hleafTy hinnerUpdate with ⟨hstr, hshape⟩
          constructor
          · change
              PartialTyStrengthens
                (partialTyRebox
                  (PartialTy.strongLeafUpdate (.ty spineInner) path rhsTy))
                (partialTyRebox updatedInner)
            exact PartialTyStrengthens.rebox hstr hshape
          · change
              PartialTy.sameShape
                (partialTyRebox
                  (PartialTy.strongLeafUpdate (.ty spineInner) path rhsTy))
                (partialTyRebox updatedInner)
            exact PartialTy.sameShape_rebox hshape

/-- Borrow-resolution dependencies decompose into a contained borrow node and
a target whose resolution reads the dependency. -/
theorem RuntimeFrame.borrowDependency_witness {store : ProgramStore}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ∃ mutable targets target,
      PartialTyContains partialTy (.borrow mutable targets) ∧
      target ∈ targets ∧
      RuntimeFrame.LocReads store target dependency := by
  intro hdep
  induction hdep with
  | @borrow location readLocation mutable targets target hmem _hloc hreads =>
      exact ⟨mutable, targets, target, PartialTyContains.here, hmem, hreads⟩
  | boxInner _hslot _hinner ih =>
      rcases ih with ⟨m, ts, t, hcontains, hmem, hreads⟩
      exact ⟨m, ts, t, PartialTyContains.box hcontains, hmem, hreads⟩
  | boxFullInner _hslot _hinner ih =>
      rcases ih with ⟨m, ts, t, hcontains, hmem, hreads⟩
      exact ⟨m, ts, t, PartialTyContains.tyBox hcontains, hmem, hreads⟩

/-- A contained borrow survives same-shape strengthening, with a grown target
list. -/
theorem PartialTyContains.mono_strengthens_sameShape
    {strong weak : PartialTy} {mutable : Bool} {targets : List LVal} :
    PartialTyContains strong (.borrow mutable targets) →
    PartialTyStrengthens strong weak →
    PartialTy.sameShape strong weak →
    ∃ targets',
      PartialTyContains weak (.borrow mutable targets') ∧
        targets ⊆ targets' := by
  intro hcontains hstrengthens
  induction hstrengthens generalizing targets with
  | reflex =>
      intro _hshape
      exact ⟨targets, hcontains, fun _ h => h⟩
  | @box left right _hinner ih =>
      intro hshape
      cases hcontains with
      | box hcontains' =>
          rcases ih hcontains'
              (by simpa [PartialTy.sameShape] using hshape) with
            ⟨ts', hcontains'', hsubset⟩
          exact ⟨ts', PartialTyContains.box hcontains'', hsubset⟩
  | @tyBox left right _hinner ih =>
      intro hshape
      cases hcontains with
      | tyBox hcontains' =>
          rcases ih hcontains'
              (by simpa [PartialTy.sameShape, Ty.sameShape] using hshape) with
            ⟨ts', hcontains'', hsubset⟩
          exact ⟨ts', PartialTyContains.tyBox hcontains'', hsubset⟩
  | @borrow mutable' leftTargets rightTargets hsubset =>
      intro _hshape
      cases hcontains with
      | here =>
          exact ⟨rightTargets, PartialTyContains.here, hsubset⟩
  | undefLeft _hinner _ih =>
      intro _hshape
      cases hcontains
  | intoUndef _hinner _ih =>
      intro hshape
      simp [PartialTy.sameShape] at hshape
  | boxIntoUndef _hinner _ih =>
      intro hshape
      simp [PartialTy.sameShape] at hshape

/-- A borrow contained in the written type is contained in the strongly
updated spine type. -/
theorem StoreOwnerSpine.strongLeafUpdate_contains {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} {path : Path} {rhsTy needle : Ty} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    PartialTyContains (.ty rhsTy) needle →
    PartialTyContains (PartialTy.strongLeafUpdate ty path rhsTy) needle := by
  intro hspine hcontains
  induction hspine with
  | nil _ _ =>
      simpa [PartialTy.strongLeafUpdate] using hcontains
  | box _hslot _howner _htail ih =>
      simpa [PartialTy.strongLeafUpdate] using PartialTyContains.box ih
  | @boxFull storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      have hinner :
          PartialTyContains (PartialTy.strongLeafUpdate (.ty inner) path rhsTy)
            needle :=
        ih
      generalize hupdated :
        PartialTy.strongLeafUpdate (.ty inner) path rhsTy = updated at hinner ⊢
      cases updated with
      | ty updatedInner =>
          simpa [PartialTy.strongLeafUpdate, hupdated, partialTyRebox] using
            PartialTyContains.tyBox hinner
      | box updatedInner =>
          simpa [PartialTy.strongLeafUpdate, hupdated, partialTyRebox] using
            PartialTyContains.box hinner
      | undef updatedInner =>
          cases hinner

/-- Write prohibitions on a variable transport forward through same-shape
strengthening maps: joins only grow borrow target lists. -/
theorem writeProhibited_var_transport {env env' : Env} {b : Name}
    {lv' : LVal} :
    EnvSameShapeStrengthening env env' →
    LVal.base lv' = b →
    WriteProhibited env (.var b) →
    WriteProhibited env' lv' := by
  intro hmap hbase hWP
  have transport :
      ∀ {c : Name} {mutable : Bool} {ts : List LVal} {t : LVal},
        env ⊢ c ↝ (.borrow mutable ts) → t ∈ ts → t ⋈ (.var b) →
        ∃ ts', env' ⊢ c ↝ (.borrow mutable ts') ∧ t ∈ ts' ∧ t ⋈ lv' := by
    intro c mutable ts t hnode hmem hconf
    rcases hnode with ⟨cslot, hcslot, hcontains⟩
    rcases hmap.2 c cslot hcslot with ⟨resultSlot, hresultSlot, _hlife⟩
    rcases hmap.1 c resultSlot hresultSlot with
      ⟨cslot', hcslot', _hlife', hstrengthens, hshape⟩
    have hcslotEq : cslot' = cslot :=
      Option.some.inj (hcslot'.symm.trans hcslot)
    subst hcslotEq
    rcases PartialTyContains.mono_strengthens_sameShape hcontains
        hstrengthens hshape with
      ⟨ts', hcontains', hsubset⟩
    refine ⟨ts', ⟨resultSlot, hresultSlot, hcontains'⟩, hsubset hmem, ?_⟩
    simpa [PathConflicts, LVal.base, hbase] using hconf
  rcases hWP with ⟨c, ts, t, hnode, hmem, hconf⟩ | ⟨c, ts, t, hnode, hmem,
      hconf⟩
  · rcases transport hnode hmem hconf with ⟨ts', hnode', hmem', hconf'⟩
    exact Or.inl ⟨c, ts', t, hnode', hmem', hconf'⟩
  · rcases transport hnode hmem hconf with ⟨ts', hnode', hmem', hconf'⟩
    exact Or.inr ⟨c, ts', t, hnode', hmem', hconf'⟩

/--
The owner-spine decomposition of a heap-resolved typed lvalue: the resolution
bottoms out in a pure box descent from a root variable whose typed owner spine
reaches the resolved heap cell.
-/
theorem heapLeaf_spine_of_loc {store : ProgramStore} {env : Env}
    {current : Lifetime} {φ : Name → Nat} {lv : LVal} {lvTy : Ty}
    {lifetime : Lifetime} {address : Nat} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ≈ₛ env →
    LValTyping env lv (.ty lvTy) lifetime →
    store.loc lv = some (.heap address) →
    ∃ xRoot envSlot rootSlot spinePath leafSlot leafTy,
      env.slotAt xRoot = some envSlot ∧
      store.slotAt (VariableProjection xRoot) = some rootSlot ∧
      rootSlot.lifetime = envSlot.lifetime ∧
      StoreOwnerSpine store (VariableProjection xRoot) rootSlot envSlot.ty
        spinePath (.heap address) leafSlot (.ty leafTy) ∧
      spinePath ≠ [] := by
  intro hφ hwellFormed hsafe htyping hloc
  exact go hφ hwellFormed hsafe htyping hloc
where
  go {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {lv : LVal} {lvTy : Ty} {lifetime : Lifetime} {address : Nat}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ≈ₛ env) (htyping : LValTyping env lv (.ty lvTy) lifetime)
      (hloc : store.loc lv = some (.heap address)) :
      ∃ xRoot envSlot rootSlot spinePath leafSlot leafTy,
        env.slotAt xRoot = some envSlot ∧
        store.slotAt (VariableProjection xRoot) = some rootSlot ∧
        rootSlot.lifetime = envSlot.lifetime ∧
        StoreOwnerSpine store (VariableProjection xRoot) rootSlot envSlot.ty
          spinePath (.heap address) leafSlot (.ty leafTy) ∧
        spinePath ≠ [] := by
    cases lv with
    | var x =>
        simp [ProgramStore.loc] at hloc
    | deref u =>
        cases htyping with
        | @box _ _ sourceLifetime hsource =>
            rcases StoreOwnerSpine.of_lvalTyping_box hwellFormed hsafe
                hsource with
              ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
                hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
                hsourceSpine⟩
            have hsourceValid :=
              StoreOwnerSpine.leaf_valid hsourceSpine
            rcases sourceSlot with ⟨sourceValue, sourceLifetime'⟩
            cases hsourceValid with
            | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
                have hderefLoc :
                    store.loc (.deref u) = some ownerLocation := by
                  simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                have hlocEq : Location.heap address = ownerLocation := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                have hsnoc :=
                  StoreOwnerSpine.snoc_box hsourceSpine rfl rfl hownedSlot
                    hinnerValid
                rw [← hlocEq] at hsnoc
                exact ⟨LVal.base u, envSlot, rootSlot, () :: LVal.path u,
                  ownerSlot, lvTy, henvBase, hrootSlot, hrootLifetime, hsnoc,
                  by simp⟩
          | @boxFull _ _ _ hsource =>
              have hsourceAbs :
                  LValLocationAbstraction store u (.ty (.box lvTy)) :=
                lvalTyping_defined_location hwellFormed hsafe hsource
              rcases hsourceAbs with
                ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, _hmiddleValid⟩
              rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe
                  hsource hmiddleLoc with
                ⟨root, slotM, viewTyM, slotLt, hprotM, hrankM, hslotM,
                  hvalidM, hstrengthM, hboundM, hborrowsM, hcontainsM,
                  rootEnvSlot, rootValue, hrootEnvSlot, hrootValue,
                  hdescent⟩
              rcases middleSlot with ⟨middleValue, middleLifetime⟩
              have hslotMEq :
                  slotM = ⟨middleValue, middleLifetime⟩ :=
                Option.some.inj (hslotM.symm.trans hmiddleSlot)
              subst hslotMEq
              cases hvalidM with
              | @boxFull ownerLocation ownerSlot innerView hownedSlot hinnerValid =>
                  have hderefLoc :
                      store.loc (.deref u) = some ownerLocation := by
                    simp [ProgramStore.loc, hmiddleLoc, hslotM]
                  have hlocEq : Location.heap address = ownerLocation := by
                    rw [hloc] at hderefLoc
                    exact Option.some.inj hderefLoc
                  rcases hdescent with hroot | hreach
                  · rcases hroot with ⟨hrootLocation, hviewRoot, hvalueRoot⟩
                    have hspine :
                        StoreOwnerSpine store (VariableProjection root)
                          { value := rootValue,
                            lifetime := rootEnvSlot.lifetime }
                          rootEnvSlot.ty [()] (.heap address) ownerSlot
                          (.ty innerView) := by
                      rw [← hviewRoot]
                      refine StoreOwnerSpine.boxFull
                        (owned := .heap address) (ownedSlot := ownerSlot)
                        hrootValue ?_ ?_
                      · have hownerValue :
                            rootValue = .value (owningRef ownerLocation) := by
                          rw [← hvalueRoot]
                          rfl
                        simpa [owningRef, hlocEq] using hownerValue
                      · exact StoreOwnerSpine.nil
                          (by simpa [hlocEq] using hownedSlot) hinnerValid
                    exact ⟨root, rootEnvSlot,
                      { value := rootValue, lifetime := rootEnvSlot.lifetime },
                      [()], ownerSlot, innerView, hrootEnvSlot, hrootValue, rfl,
                      hspine, by simp⟩
                  · rcases StoreOwnerSpine.of_reachesSlot hrootValue rfl hreach
                      with ⟨spinePath, hspineToMiddle, _hspineNonempty⟩
                    have hspine :
                        StoreOwnerSpine store (VariableProjection root)
                          { value := rootValue,
                            lifetime := rootEnvSlot.lifetime }
                          rootEnvSlot.ty (() :: spinePath) (.heap address)
                          ownerSlot (.ty innerView) := by
                      exact StoreOwnerSpine.snoc_boxFull hspineToMiddle rfl
                        (by simpa [owningRef, hlocEq])
                        (by simpa [hlocEq] using hownedSlot) hinnerValid
                    exact ⟨root, rootEnvSlot,
                      { value := rootValue, lifetime := rootEnvSlot.lifetime },
                      () :: spinePath, ownerSlot, innerView, hrootEnvSlot,
                      hrootValue, rfl, hspine, by simp⟩
              | unit | int | undef =>
                  cases hstrengthM
              | @borrow targetLoc mutable' targets' witness hmemW hlocW =>
                  cases hstrengthM
              | @box ownerLocation ownerSlot innerView hownedSlot hinnerValid =>
                  cases hstrengthM
              | @undefOf _ _ hiddenOuter hskel hstrength =>
                  cases hstrengthM
          | @borrow _ mutable targets borrowLifetime targetLifetime targetTy
              hsource htargets =>
            have hsourceAbs :
                LValLocationAbstraction store u
                  (.ty (.borrow mutable targets)) :=
              lvalTyping_defined_location hwellFormed hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            cases hmiddleValid with
            | @borrow targetLoc _mutable _targets witness hmemW hlocW =>
                have hderefLoc :
                    store.loc (.deref u) = some targetLoc := by
                  simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot]
                have hlocEq : Location.heap address = targetLoc := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                rcases lvalTargetsTyping_member_strengthens htargets _
                    hmemW with
                  ⟨witnessTy, witnessLifetime, hwitnessTyping, _hstrengthens⟩
                have hwitnessRank :
                    φ (LVal.base witness) < φ (LVal.base u) :=
                  (lvalTyping_vars_rank_lt hφ).1 hsource (LVal.base witness)
                    (mem_partialTy_vars_iff.mpr
                      ⟨mutable, targets, witness, PartialTyContains.here,
                        hmemW, rfl⟩)
                exact go hφ hwellFormed hsafe hwitnessTyping
                  (by rw [← hlocEq] at hlocW; exact hlocW)
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)

end Paper
end LwRust

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Lemma 4.9, Borrow Invariance. -/
theorem lemma_4_9_borrowInvariance
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hrefs : ∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime)
    (hvalid : ValidState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂) :
    WellFormedEnvWhenInitialized env₂ lifetime :=
  borrowInvariance_of_ruleCarriedObligations
    hrefs hvalid hstoreTyping hwellFormed hsafe htyping

end LwRust.Paper.Soundness
