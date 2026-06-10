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
pointee types, so the merged list has no joint typing in general, yet each target
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
def TerminalStateSafe (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) :
    Prop :=
  ValidRuntimeState store (.val value) ∧ store ∼ₛ env ∧ ValidValue store value ty

theorem TerminalStateSafe.transport_sameShape {store : ProgramStore}
    {value : Value} {source result : Env} {ty : Ty} :
    TerminalStateSafe store value source ty →
    (∀ x resultSlot,
      result.slotAt x = some resultSlot →
      ∃ sourceSlot,
        source.slotAt x = some sourceSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime ∧
          PartialTyStrengthens sourceSlot.ty resultSlot.ty ∧
          PartialTy.sameShape sourceSlot.ty resultSlot.ty) →
    (∀ x sourceSlot,
      source.slotAt x = some sourceSlot →
      ∃ resultSlot,
        result.slotAt x = some resultSlot ∧
          sourceSlot.lifetime = resultSlot.lifetime) →
    TerminalStateSafe store value result ty := by
  intro hterminal hback hfwd
  exact ⟨hterminal.1,
    safeAbstraction_transport_sameShape hterminal.2.1 hback hfwd,
    hterminal.2.2⟩

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
    store ∼ₛ source →
    store ∼ₛ result := by
  intro hmap hsafe
  exact safeAbstraction_transport_sameShape hsafe hmap.1 hmap.2

theorem EnvSameShapeStrengthening.update_result_existing_slot
    {source result : Env} {x : Name} {slot : EnvSlot} :
    EnvSameShapeStrengthening source result →
    source.slotAt x = some slot →
    EnvSameShapeStrengthening source (result.update x slot) := by
  intro hmap hsourceSlot
  constructor
  · intro y resultSlot hresultSlot
    by_cases hy : y = x
    · subst hy
      have hresultSlotEq : resultSlot = slot := by
        simpa [Env.update] using hresultSlot.symm
      exact ⟨slot, hsourceSlot,
        by rw [hresultSlotEq],
        by
          rw [hresultSlotEq],
        by
          rw [hresultSlotEq]⟩
    · have hresultOld : result.slotAt y = some resultSlot := by
        simpa [Env.update, hy] using hresultSlot
      exact hmap.1 y resultSlot hresultOld
  · intro y sourceSlot hslot
    by_cases hy : y = x
    · subst hy
      have hslotEq : sourceSlot = slot :=
        Option.some.inj (hslot.symm.trans hsourceSlot)
      exact ⟨slot, by simp [Env.update], by rw [hslotEq]⟩
    · rcases hmap.2 y sourceSlot hslot with
        ⟨resultSlot, hresultSlot, hlifetime⟩
      exact ⟨resultSlot, by simpa [Env.update, hy] using hresultSlot,
        hlifetime⟩

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
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
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
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites rfl hrank
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
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
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro
    hwrites hrank hleaves hmem hselectedBranch
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
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
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro
    hwrites hrank hleaves hmem
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
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
    ?var ?box ?borrow ?singleton ?cons htargets hselected
  case var => intros; trivial
  case box => intros; trivial
  case borrow => intros; trivial
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
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
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
      · rcases hborrow with ⟨targets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq
  case borrowStep =>
      intro mutable targets path selectedName selectedSlot selectedTy htargetsSelected _ih
        rank updatedTy writeEnv hbelow hupdate hbranch
      rcases UpdateAtPath.cons_inv hupdate with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
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

theorem EnvWrite.selected_path_map {rank : Nat} {env result : Env}
    {lv : LVal} {pt : PartialTy} {lifetime : Lifetime} {path : List Unit}
    {rhsTy selectedTy : Ty} {selectedName : Name} {selectedSlot : EnvSlot}
    {φ : Name → Nat} :
    LinearizedBy φ env →
    LValTyping env lv pt lifetime →
    PathSelected env pt path selectedName selectedSlot selectedTy →
    EnvWrite rank env (prependPath path lv) rhsTy result →
    EnvSameShapeStrengthening
      (env.update selectedName { selectedSlot with ty := .ty rhsTy })
      result := by
  intro hφ htyping₀ hselected₀ hwrite₀
  let rec go (lv : LVal) {pt : PartialTy} {lifetime : Lifetime}
      {path : List Unit} {rank : Nat} {result : Env} {rhsTy selectedTy : Ty}
      {selectedName : Name} {selectedSlot : EnvSlot}
      (htyping : LValTyping env lv pt lifetime)
      (hselected : PathSelected env pt path selectedName selectedSlot selectedTy)
      (hwrite : EnvWrite rank env (prependPath path lv) rhsTy result) :
      EnvSameShapeStrengthening
        (env.update selectedName { selectedSlot with ty := .ty rhsTy })
        result := by
    cases htyping with
    | var hslot =>
        rename_i x slot
        cases hwrite with
        | @intro _rank _env₁ writeEnv _writeLv writeSlot _writeTy updatedTy
            hwriteSlot hupdate =>
            simp [LVal.base] at hwriteSlot
            have hslotEq : writeSlot = slot := by
              have hsome : some writeSlot = some slot := by
                rw [← hwriteSlot, hslot]
              exact Option.some.inj hsome
            subst writeSlot
            have hupdatePath :
                UpdateAtPath rank env path slot.ty rhsTy writeEnv updatedTy := by
              simpa [path_prependPath, LVal.path] using hupdate
            rcases PathSelected.updateAtPath_map
                (φ := φ) (rootRank := φ x)
                (hφ x slot hslot) hselected hupdatePath
                (fun {branchRank target pt lifetime branchPath branchResult}
                    hrank hbranchTyping hbranchSelected hbranchWrite =>
                  go target (pt := pt) (lifetime := lifetime)
                    (path := branchPath) (rank := branchRank)
                    (result := branchResult) (rhsTy := rhsTy)
                    (selectedTy := selectedTy) (selectedName := selectedName)
                    (selectedSlot := selectedSlot)
                    hbranchTyping hbranchSelected hbranchWrite) with
              ⟨hmap, hstrength, hshape⟩
            have hselectedRankLt :
                φ selectedName < φ x :=
              PathSelected.rank_lt_of_lvalTyping hφ hselected
                (LValTyping.var hslot)
            have hselectedNeX : selectedName ≠ x := by
              intro hEq
              subst hEq
              exact Nat.lt_irrefl _ hselectedRankLt
            have hxNeSelected : x ≠ selectedName := by
              intro hEq
              exact hselectedNeX hEq.symm
            have hslotStrong :
                (env.update selectedName
                  { selectedSlot with ty := .ty rhsTy }).slotAt
                    (LVal.base (prependPath path (LVal.var x))) =
                  some slot := by
              simpa [Env.update, LVal.base, hxNeSelected] using hslot
            have hfinal :
                EnvSameShapeStrengthening
                  (env.update selectedName
                    { selectedSlot with ty := .ty rhsTy })
                  (writeEnv.update
                    (LVal.base (prependPath path (LVal.var x)))
                    { slot with ty := updatedTy }) :=
              EnvSameShapeStrengthening.update_result_strengthening
                hmap hslotStrong rfl hstrength hshape
            simpa [LVal.base] using hfinal
    | box hinner =>
        exact go _ (path := () :: path) (rank := rank) (result := result)
          (rhsTy := rhsTy) (selectedTy := selectedTy)
          (selectedName := selectedName) (selectedSlot := selectedSlot)
          hinner (PathSelected.box hselected)
          (by simpa [prependPath_deref] using hwrite)
    | borrow hborrow htargets =>
        have htargetSelected :=
          TargetsPathSelected.of_lvalTargetsTyping htargets hselected
        exact go _ (path := () :: path) (rank := rank)
          (result := result) (rhsTy := rhsTy) (selectedTy := selectedTy)
          (selectedName := selectedName) (selectedSlot := selectedSlot)
          hborrow (PathSelected.borrowStep htargetSelected)
          (by simpa [prependPath_deref] using hwrite)
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      try subst_vars
      simp [LVal.base]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)
  exact go lv htyping₀ hselected₀ hwrite₀

theorem EnvWrite.deref_var_borrow_selected_var_map_of_rank
    {rank : Nat} {env result : Env} {sourceName selectedName : Name}
    {sourceSlot selectedSlot : EnvSlot} {mutable : Bool} {targets : List LVal}
    {rhsTy selectedTy : Ty} {φ : Name → Nat} :
    LinearizedBy φ env →
    env.slotAt sourceName = some sourceSlot →
    sourceSlot.ty = .ty (.borrow mutable targets) →
    EnvWrite rank env (.deref (.var sourceName)) rhsTy result →
    (.var selectedName) ∈ targets →
    env.slotAt selectedName = some selectedSlot →
    selectedSlot.ty = .ty selectedTy →
    EnvSameShapeStrengthening
      (env.update selectedName { selectedSlot with ty := .ty rhsTy })
      result := by
  intro hφ hsourceSlot hsourceTy hwrite hmem hselectedSlot hselectedTy
  cases hwrite with
  | @intro _rank _env₁ writeEnv lv writeSlot _ty updatedTy hwriteSlot hupdate =>
      simp [LVal.base] at hwriteSlot
      have hslotEq : writeSlot = sourceSlot := by
        have hsome : some writeSlot = some sourceSlot := by
          rw [← hwriteSlot, hsourceSlot]
        exact Option.some.inj hsome
      subst writeSlot
      have hupdateCons :
          UpdateAtPath rank env [()] sourceSlot.ty rhsTy writeEnv updatedTy := by
        simpa [LVal.path, LVal.base] using hupdate
      rw [hsourceTy] at hupdateCons
      rcases UpdateAtPath.cons_inv hupdateCons with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
        cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        have hselectedRankLt : φ selectedName < φ sourceName := by
          have hselectedVarMem :
              selectedName ∈ PartialTy.vars sourceSlot.ty := by
            rw [hsourceTy]
            have hmemMap :
                LVal.base (.var selectedName) ∈ targets.map LVal.base :=
              List.mem_map_of_mem hmem
            simpa [PartialTy.vars, Ty.vars, LVal.base] using hmemMap
          exact hφ sourceName sourceSlot hsourceSlot selectedName hselectedVarMem
        have hselectedNeSource : selectedName ≠ sourceName := by
          intro hEq
          subst hEq
          exact Nat.lt_irrefl _ hselectedRankLt
        have hsourceNeSelected : sourceName ≠ selectedName := by
          intro hEq
          exact hselectedNeSource hEq.symm
        have hfanMap :
            EnvSameShapeStrengthening
              (env.update selectedName { selectedSlot with ty := .ty rhsTy })
              writeEnv :=
          WriteBorrowTargets.selected_var_strong_to_result_map
            (Nat.succ_pos rank) hwrites hmem hselectedSlot hselectedTy
        have hsourceRebuild :
            (env.update selectedName
              { selectedSlot with ty := .ty rhsTy }).slotAt sourceName =
              some { sourceSlot with ty := .ty (.borrow true targets) } := by
          have hsourceStrong :
              (env.update selectedName
                { selectedSlot with ty := .ty rhsTy }).slotAt sourceName =
                some sourceSlot := by
            simpa [Env.update, hsourceNeSelected] using hsourceSlot
          have hslotRebuild :
              { sourceSlot with ty := .ty (.borrow true targets) } = sourceSlot := by
            cases sourceSlot
            simp at hsourceTy ⊢
            exact hsourceTy.symm
          simpa [hslotRebuild] using hsourceStrong
        have hmapFinal :=
          EnvSameShapeStrengthening.update_result_existing_slot
            hfanMap hsourceRebuild
        simpa [LVal.base, hupdatedEq] using hmapFinal

theorem EnvWrite.deref_var_borrow_selected_var_map
    {rank : Nat} {env result : Env} {sourceName selectedName : Name}
    {sourceSlot selectedSlot : EnvSlot} {mutable : Bool} {targets : List LVal}
    {rhsTy selectedTy : Ty} :
    env.slotAt sourceName = some sourceSlot →
    sourceSlot.ty = .ty (.borrow mutable targets) →
    EnvWrite rank env (.deref (.var sourceName)) rhsTy result →
    ¬ WriteProhibited result (.deref (.var sourceName)) →
    (.var selectedName) ∈ targets →
    env.slotAt selectedName = some selectedSlot →
    selectedSlot.ty = .ty selectedTy →
    EnvSameShapeStrengthening
      (env.update selectedName { selectedSlot with ty := .ty rhsTy })
      result := by
  intro hsourceSlot hsourceTy hwrite hnotWrite hmem hselectedSlot hselectedTy
  cases hwrite with
  | @intro _rank _env₁ writeEnv lv writeSlot _ty updatedTy hwriteSlot hupdate =>
      simp [LVal.base] at hwriteSlot
      have hslotEq : writeSlot = sourceSlot := by
        have hsome : some writeSlot = some sourceSlot := by
          rw [← hwriteSlot, hsourceSlot]
        exact Option.some.inj hsome
      subst writeSlot
      have hupdateCons :
          UpdateAtPath rank env [()] sourceSlot.ty rhsTy writeEnv updatedTy := by
        simpa [LVal.path, LVal.base] using hupdate
      rw [hsourceTy] at hupdateCons
      rcases UpdateAtPath.cons_inv hupdateCons with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
        cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        have hselectedNeSource : selectedName ≠ sourceName := by
          intro hEq
          have hcontains :
              (writeEnv.update (LVal.base (LVal.var sourceName).deref)
                { sourceSlot with ty := updatedTy }) ⊢
                sourceName ↝ Ty.borrow true targets :=
            ⟨{ sourceSlot with ty := updatedTy },
              by simp [Env.update, LVal.base],
              by
                rw [hupdatedEq]
                exact PartialTyContains.here⟩
          have hmemSource : (.var sourceName) ∈ targets := by
            simpa [hEq] using hmem
          have hconflict :
              (.var sourceName) ⋈ (.deref (.var sourceName)) := by
            simp [PathConflicts, LVal.base]
          exact hnotWrite
            (Or.inl ⟨sourceName, targets, .var sourceName,
              hcontains, hmemSource, hconflict⟩)
        have hsourceNeSelected : sourceName ≠ selectedName := by
          intro hEq
          exact hselectedNeSource hEq.symm
        have hfanMap :
            EnvSameShapeStrengthening
              (env.update selectedName { selectedSlot with ty := .ty rhsTy })
              writeEnv :=
          WriteBorrowTargets.selected_var_strong_to_result_map
            (Nat.succ_pos rank) hwrites hmem hselectedSlot hselectedTy
        have hsourceRebuild :
            (env.update selectedName
              { selectedSlot with ty := .ty rhsTy }).slotAt sourceName =
              some { sourceSlot with ty := .ty (.borrow true targets) } := by
          have hsourceStrong :
              (env.update selectedName
                { selectedSlot with ty := .ty rhsTy }).slotAt sourceName =
                some sourceSlot := by
            simpa [Env.update, hsourceNeSelected] using hsourceSlot
          have hslotRebuild :
              { sourceSlot with ty := .ty (.borrow true targets) } = sourceSlot := by
            cases sourceSlot
            simp at hsourceTy ⊢
            exact hsourceTy.symm
          simpa [hslotRebuild] using hsourceStrong
        have hmapFinal :=
          EnvSameShapeStrengthening.update_result_existing_slot
            hfanMap hsourceRebuild
        simpa [LVal.base, hupdatedEq] using hmapFinal

theorem EnvWrite.deref_var_borrow_selected_var_map_of_ne
    {rank : Nat} {env result : Env} {sourceName selectedName : Name}
    {sourceSlot selectedSlot : EnvSlot} {mutable : Bool} {targets : List LVal}
    {rhsTy selectedTy : Ty} :
    selectedName ≠ sourceName →
    env.slotAt sourceName = some sourceSlot →
    sourceSlot.ty = .ty (.borrow mutable targets) →
    EnvWrite rank env (.deref (.var sourceName)) rhsTy result →
    (.var selectedName) ∈ targets →
    env.slotAt selectedName = some selectedSlot →
    selectedSlot.ty = .ty selectedTy →
    EnvSameShapeStrengthening
      (env.update selectedName { selectedSlot with ty := .ty rhsTy })
      result := by
  intro hselectedNeSource hsourceSlot hsourceTy hwrite hmem hselectedSlot
    hselectedTy
  cases hwrite with
  | @intro _rank _env₁ writeEnv lv writeSlot _ty updatedTy hwriteSlot hupdate =>
      simp [LVal.base] at hwriteSlot
      have hslotEq : writeSlot = sourceSlot := by
        have hsome : some writeSlot = some sourceSlot := by
          rw [← hwriteSlot, hsourceSlot]
        exact Option.some.inj hsome
      subst writeSlot
      have hupdateCons :
          UpdateAtPath rank env [()] sourceSlot.ty rhsTy writeEnv updatedTy := by
        simpa [LVal.path, LVal.base] using hupdate
      rw [hsourceTy] at hupdateCons
      rcases UpdateAtPath.cons_inv hupdateCons with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
        cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, hupdatedEq, hwrites⟩
        cases htyEq
        have hsourceNeSelected : sourceName ≠ selectedName := by
          intro hEq
          exact hselectedNeSource hEq.symm
        have hfanMap :
            EnvSameShapeStrengthening
              (env.update selectedName { selectedSlot with ty := .ty rhsTy })
              writeEnv :=
          WriteBorrowTargets.selected_var_strong_to_result_map
            (Nat.succ_pos rank) hwrites hmem hselectedSlot hselectedTy
        have hsourceRebuild :
            (env.update selectedName
              { selectedSlot with ty := .ty rhsTy }).slotAt sourceName =
              some { sourceSlot with ty := .ty (.borrow true targets) } := by
          have hsourceStrong :
              (env.update selectedName
                { selectedSlot with ty := .ty rhsTy }).slotAt sourceName =
                some sourceSlot := by
            simpa [Env.update, hsourceNeSelected] using hsourceSlot
          have hslotRebuild :
              { sourceSlot with ty := .ty (.borrow true targets) } = sourceSlot := by
            cases sourceSlot
            simp at hsourceTy ⊢
            exact hsourceTy.symm
          simpa [hslotRebuild] using hsourceStrong
        have hmapFinal :=
          EnvSameShapeStrengthening.update_result_existing_slot
            hfanMap hsourceRebuild
        simpa [LVal.base, hupdatedEq] using hmapFinal

theorem EnvContains.update_same {env : Env} {x : Name} {slot : EnvSlot}
    {ty : Ty} :
    PartialTyContains slot.ty ty →
    (env.update x slot) ⊢ x ↝ ty := by
  intro hcontains
  exact ⟨slot, by simp [Env.update], hcontains⟩

theorem EnvContains.update_fresh_of_old {env : Env} {x y : Name} {slot : EnvSlot}
    {ty : Ty} :
    env.fresh x →
    env ⊢ y ↝ ty →
    (env.update x slot) ⊢ y ↝ ty := by
  intro hfresh hcontains
  rcases hcontains with ⟨containedSlot, hslot, hcontainsTy⟩
  by_cases hy : y = x
  · subst hy
    rw [hfresh] at hslot
    cases hslot
  · exact ⟨containedSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩

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

theorem not_writeProhibited_var_of_update_self {env : Env} {x : Name}
    {slot : EnvSlot} :
    Linearizable env →
    ¬ WriteProhibited (env.update x slot) (.var x) →
    ¬ WriteProhibited env (.var x) := by
  intro hlinear hnotWrite hwrite
  rcases hlinear with ⟨φ, hφ⟩
  have notOldSelfBorrow :
      ∀ {oldSlot mutable targets target},
        env.slotAt x = some oldSlot →
        PartialTyContains oldSlot.ty (.borrow mutable targets) →
        target ∈ targets →
        target ⋈ (.var x) →
        False := by
    intro oldSlot mutable targets target hslot hcontains htarget hconflict
    have hxVar : x ∈ PartialTy.vars oldSlot.ty := by
      exact mem_partialTy_vars_iff.mpr
        ⟨mutable, targets, target, hcontains, htarget, hconflict⟩
    exact Nat.lt_irrefl (φ x) (hφ x oldSlot hslot x hxVar)
  cases hwrite with
  | inl hread =>
      rcases hread with ⟨y, targets, target, hcontains, htarget, hconflict⟩
      rcases hcontains with ⟨oldSlot, hslot, hcontainsTy⟩
      by_cases hy : y = x
      · subst hy
        exact False.elim
          (notOldSelfBorrow hslot hcontainsTy htarget hconflict)
      · have hcontains' :
            (env.update x slot) ⊢ y ↝ Ty.borrow true targets :=
          ⟨oldSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩
        exact hnotWrite (Or.inl
          ⟨y, targets, target, hcontains', htarget, hconflict⟩)
  | inr himm =>
      rcases himm with ⟨y, targets, target, hcontains, htarget, hconflict⟩
      rcases hcontains with ⟨oldSlot, hslot, hcontainsTy⟩
      by_cases hy : y = x
      · subst hy
        exact False.elim
          (notOldSelfBorrow hslot hcontainsTy htarget hconflict)
      · have hcontains' :
            (env.update x slot) ⊢ y ↝ Ty.borrow false targets :=
          ⟨oldSlot, by simpa [Env.update, hy] using hslot, hcontainsTy⟩
        exact hnotWrite (Or.inr
          ⟨y, targets, target, hcontains', htarget, hconflict⟩)

theorem EnvContains.dropLifetime_of_contains {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime} :
    (env.dropLifetime lifetime) ⊢ x ↝ ty →
    env ⊢ x ↝ ty := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _hlifetime⟩
  exact ⟨slot, henvSlot, hcontainsTy⟩

theorem LValTyping.var_dropLifetime_child {env : Env} {parent child : Lifetime}
    {x : Name} {slot : EnvSlot} :
    LifetimeChild parent child →
    env.slotAt x = some slot →
    slot.lifetime ≤ parent →
    LValTyping (env.dropLifetime child) (.var x) slot.ty slot.lifetime := by
  intro hchild hslot houtlivesParent
  exact LValTyping.var (Env.dropLifetime_slotAt_eq_some.mpr
    ⟨hslot, by
      intro hslotLifetime
      subst hslotLifetime
      exact LifetimeChild.not_child_outlives_parent hchild houtlivesParent⟩)

theorem Env.dropLifetime_update_ne {env : Env} {x : Name} {slot : EnvSlot}
    {dropped : Lifetime} :
    slot.lifetime ≠ dropped →
    (env.update x slot).dropLifetime dropped =
      (env.dropLifetime dropped).update x slot := by
  intro hslotLifetime
  cases env with
  | mk slotAt =>
      simp only [Env.dropLifetime, Env.update]
      congr
      funext y
      by_cases hy : y = x
      · subst hy
        simp [hslotLifetime]
      · simp [hy]

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
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
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
      | unit => exact TermTyping.const ValueTyping.unit
      | int => exact TermTyping.const ValueTyping.int
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
    (fun hfresh _hterm hfreshOut hcoh henv ih hsource =>
      TermTyping.declare hfresh (ih (SourceTerm.declare_inner hsource))
        hfreshOut hcoh henv)
    (fun hLhs _hRhs hLhsPost hshape hwf hwrite hranked hcoh hcontained
        hnotWrite ih hsource =>
      TermTyping.assign hLhs (ih (SourceTerm.assign_inner hsource)) hLhsPost
        hshape hwf hwrite hranked hcoh hcontained hnotWrite)
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

theorem TermTyping.target_lifetime_outlives_surviving_base_slot {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lv : LVal} {oldTy : PartialTy} {term : Term} {ty : Ty}
    {resultSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    LValTyping env₁ lv oldTy targetLifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    env₂.slotAt (LVal.base lv) = some resultSlot →
    targetLifetime ≤ resultSlot.lifetime := by
  intro hwellInitial hLv hterm hresultSlot
  rcases LValTyping.base_outlives_one hwellInitial hLv with
    ⟨sourceSlot, hsourceSlot, hsourceOutlivesCurrent⟩
  have hbaseSelf : LValBaseOutlives env₁ lv sourceSlot.lifetime :=
    ⟨sourceSlot, hsourceSlot, LifetimeOutlives.refl sourceSlot.lifetime⟩
  have htargetOutlivesSource :
      targetLifetime ≤ sourceSlot.lifetime :=
    LValTyping.lifetime_outlives_of_base_outlives_one
      hwellInitial.1 hLv hbaseSelf
  rcases (TermTyping.slot_lifetime_survives.1 hterm)
      hsourceOutlivesCurrent hsourceSlot with
    ⟨survivedSlot, hsurvivedSlot, hsurvivedLifetime⟩
  have hslotEq : survivedSlot = resultSlot := by
    have hsomeEq : some survivedSlot = some resultSlot := by
      rw [← hsurvivedSlot, hresultSlot]
    exact Option.some.inj hsomeEq
  rw [← hslotEq, ← hsurvivedLifetime]
  exact htargetOutlivesSource

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
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
  | immBorrow =>
      exact WellFormedTy.borrow
        (copyBorrowTargetsWellFormed hwellFormed hLv)

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
      cases source <;> cases struck <;> simp [Strike] at hstrike
      cases hcontains with
      | box hinner =>
          exact PartialTyContains.box (ih hstrike hinner)

theorem LVal.path_deref_append (lv : LVal) (suffix : Path) :
    LVal.path (.deref lv) ++ suffix = LVal.path lv ++ (() :: suffix) := by
  rw [LVal.path, List.append_assoc]
  rfl

/-- If a path selects an initialized leaf, `Strike` cannot consume one more
dereference beyond that path. -/
theorem WriteLeafTy.not_strike_deref {env : Env} {path : Path}
    {partialTy : PartialTy} {ty : Ty} {struck : PartialTy} :
    WriteLeafTy env path partialTy ty →
    Strike (path ++ [()]) partialTy struck →
    False := by
  intro hleaf
  induction hleaf generalizing struck with
  | leaf =>
      intro hstrike
      simp [Strike] at hstrike
  | box hinner ih =>
      intro hstrike
      cases struck with
      | ty struckTy =>
          simp [Strike] at hstrike
      | undef struckTy =>
          simp [Strike] at hstrike
      | box struckInner =>
          exact ih (struck := struckInner) (by
            simpa [Strike] using hstrike)
  | borrow _htargets =>
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

theorem ContainedBorrowsWellFormed.slot_partial {env : Env}
    {x : Name} {slot : EnvSlot} :
    ContainedBorrowsWellFormed env →
    env.slotAt x = some slot →
    PartialTyBorrowsWellFormedInSlot env slot.lifetime slot.ty := by
  intro hcontained hslot mutable targets hcontains
  exact hcontained x slot mutable targets hslot ⟨slot, hslot, hcontains⟩

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

theorem declare_preserves_wellFormed_output_fresh {env₂ env₃ : Env}
    {lifetime : Lifetime} {x : Name} {ty : Ty} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh x →
    FreshUpdateCoherenceObligations env₂ x ty lifetime →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    WellFormedEnv env₃ lifetime := by
  intro hwellFormed hwellTy hfresh hcoh henv₃
  rw [henv₃]
  exact WellFormedEnv.update_fresh_ty hwellFormed hwellTy hfresh hcoh

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
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
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
          | ty _ => simp [Strike] at h
          | box _ => simp [Strike] at h
      | box _ => simp [Strike] at h
      | undef _ => simp [Strike] at h
  | cons _ rest ih =>
      intro ty struck h v hv
      cases ty with
      | box inner =>
          cases struck with
          | box struck' =>
              simp only [PartialTy.vars] at hv ⊢
              exact ih (show Strike rest inner struck' from h) v hv
          | ty _ => simp [Strike] at h
          | undef _ => simp [Strike] at h
      | ty _ => simp [Strike] at h
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
  · have hsenv : env.slotAt x = some s := by simpa [Env.update, hx] using hs
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
        | ty _ => simp [Strike] at h
        | box _ => simp [Strike] at h
      | box _ => simp [Strike] at h
      | undef _ => simp [Strike] at h
  | cons _ rest ih =>
      intro ty struck h
      cases ty with
      | box inner => cases struck with
        | box struck' =>
            have h' : Strike rest inner struck' := h
            show IsBoxUndef struck'
            exact ih h'
        | ty _ => simp [Strike] at h
        | undef _ => simp [Strike] at h
      | ty _ => simp [Strike] at h
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
    ?var ?box ?borrow ?singleton ?cons h
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
  · intro lv'' mutable targets _bLf _tLf _tTy hborrow _htargets ihBorrow _ihTargets hbase
    have := ihBorrow (by simpa [LVal.base] using hbase)
    simp [IsBoxUndef] at this
  · intro _ _ _ _ _; trivial
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _; trivial

/-- `Coherent` is preserved by a move.  A defined borrow `lv':&T` in the moved
environment cannot be rooted at the (undef'd) moved variable
(`isBoxUndef_of_base_moved`), so it transports backward to the original
environment (restoring the moved slot is an update with no path conflict), where
`Coherent env` provides a joint typing of `T`; the joint typing then transports
forward across the move (the targets do not conflict with the moved value, by
`¬WriteProhibited`). -/
theorem Coherent.move {env env' : Env} {lv : LVal} {lifetime : Lifetime}
    (hwellFormed : WellFormedEnv env lifetime)
    (hnotWrite : ¬ WriteProhibited env lv)
    (hmove : EnvMove env lv env')
    (hcohEnv : Coherent env) : Coherent env' := by
  have hmoveCopy := hmove
  rcases hmoveCopy with ⟨slot, struck, hslot, hstrike, henv'⟩
  subst henv'
  intro lv' m T bLf hty'
  have hbaseNe : ¬ lv' ⋈ lv := by
    intro hbeq
    have hbu := LValTyping.isBoxUndef_of_base_moved hslot hstrike hty'
      (by simpa [PathConflicts, LVal.base] using hbeq)
    simp [IsBoxUndef] at hbu
  -- restoring the moved slot returns the original environment
  have hrestore :
      (env.update (LVal.base lv) { slot with ty := struck }).update (LVal.base lv) slot
        = env := by
    obtain ⟨g⟩ := env
    simp only [Env.update]
    congr 1
    funext y
    by_cases hy : y = LVal.base lv
    · subst hy; simpa using hslot.symm
    · simp [hy]
  have hnotWriteVarEnv : ¬ WriteProhibited env (.var (LVal.base lv)) :=
    not_writeProhibited_var_base hnotWrite
  have hnotWriteVar :
      ¬ WriteProhibited
        ((env.update (LVal.base lv) { slot with ty := struck }).update (LVal.base lv) slot)
        (.var (LVal.base lv)) := by rw [hrestore]; exact hnotWriteVarEnv
  -- backward typing: env' → env (restore update, no conflict)
  have htyEnvRestore :
      LValTyping ((env.update (LVal.base lv) { slot with ty := struck }).update
        (LVal.base lv) slot) lv' (.ty (.borrow m T)) bLf :=
    (LValTyping.update_of_not_pathConflicts hnotWriteVar).1 hty'
      (by simpa [PathConflicts, LVal.base] using hbaseNe)
  have htyEnv : LValTyping env lv' (.ty (.borrow m T)) bLf := by
    rwa [hrestore] at htyEnvRestore
  rcases hcohEnv lv' m T bLf htyEnv with ⟨ty, lt, htgtsEnv⟩
  -- targets do not conflict with the moved value
  have hnotTargets : ∀ target, target ∈ T → ¬ target ⋈ lv := by
    intro target htarget
    exact (LValTyping.no_writeProhibited_targets hnotWrite).1 htyEnv
      PartialTyContains.here target htarget
  -- forward transport of the joint typing across the move
  exact ⟨ty, lt,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).2 htgtsEnv hnotTargets⟩

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
      EnvSlotsOutlive.move hwellFormed.2.1 hmove, ?_, ?_⟩,
    WellFormedTy.move_result hwellFormed hLv hnotWrite hmove⟩
  · exact Coherent.move hwellFormed hnotWrite hmove hwellFormed.2.2.1
  · exact Linearizable.move hmove hwellFormed.2.2.2

theorem EnvWrite.preserves_containedBorrowsWellFormed_var {env result : Env}
    {lifetime targetLifetime : Lifetime} {x : Name}
    {oldTy : PartialTy} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    LValTyping env (.var x) oldTy targetLifetime →
    WellFormedTy env rhsTy targetLifetime →
    EnvWrite 0 env (.var x) rhsTy result →
    ¬ WriteProhibited result (.var x) →
    ContainedBorrowsWellFormed result := by
  intro hwellFormed hLhs hwellRhs hwrite hnotWrite
  rcases LValTyping.var_inv hLhs with
    ⟨lhsSlot, hlhsSlot, _holdTy, hlhsLifetime⟩
  cases hwrite with
  | intro hwriteSlot hupdate =>
      rename_i writeEnv writeSlot updatedTy
      simp [LVal.base, LVal.path] at hwriteSlot hupdate
      have hslotEq : writeSlot = lhsSlot := by
        have hsomeEq : some writeSlot = some lhsSlot := by
          rw [← hwriteSlot, hlhsSlot]
        exact Option.some.inj hsomeEq
      cases hupdate with
      | strong =>
          have hnotWrite' :
              ¬ WriteProhibited
                (env.update x { writeSlot with ty := PartialTy.ty rhsTy })
                (.var x) := by
            simpa [LVal.base] using hnotWrite
          have hslotTargets :
              PartialTyBorrowsWellFormedInSlot
                (env.update x { writeSlot with ty := PartialTy.ty rhsTy })
                writeSlot.lifetime
                ({ writeSlot with ty := PartialTy.ty rhsTy }).ty := by
            intro mutable targets hcontainsTy
            have htargetsEnv :
                BorrowTargetsWellFormedInSlot env targetLifetime targets :=
              borrowTargetsWellFormedInSlot_of_wellFormedTy_contains
                hwellRhs hcontainsTy
            have htargetsEnvAtSlot :
                BorrowTargetsWellFormedInSlot env writeSlot.lifetime targets := by
              rw [hslotEq, hlhsLifetime]
              exact htargetsEnv
            exact BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
              (x := x)
              (slot := { writeSlot with ty := PartialTy.ty rhsTy }) hnotWrite'
              htargetsEnvAtSlot
              (by
                intro target htarget
                have hcontainsUpdated :
                    (env.update x { writeSlot with ty := PartialTy.ty rhsTy }) ⊢
                      x ↝ Ty.borrow mutable targets :=
                  ⟨{ writeSlot with ty := PartialTy.ty rhsTy },
                    by simp [Env.update],
                    hcontainsTy⟩
                exact not_pathConflicts_of_not_writeProhibited_contains
                  hnotWrite'
                  hcontainsUpdated
                  htarget)
          simpa [LVal.base] using
            ContainedBorrowsWellFormed.update_slot
              hwellFormed.1 hslotTargets hnotWrite'

/-- Remaining update invariant needed by Lemma 4.9.

The `W-Weak` union case is no longer a caller obligation:
`PartialTyBorrowsWellFormedInSlot.of_partialTyUnion` proves it directly for the
per-target invariant.  The package now only records the non-local mutable-borrow
fan-out fact, where branch writes and joins must preserve observer target
well-formedness.
-/
structure UpdateBorrowInvariantObligations : Prop where
  writeBorrowTargets_preserves_containedBorrowsWellFormed
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets

/-- Initialized-leaf fact for Appendix 9.6 fan-out writes.

Documented rule strengthening: `WriteBorrowTargets.singleton/cons` now carry a
full typing for the concrete branch target `prependPath path target`.  Without
that premise, the bare fan-out syntax could write through arbitrary partial
paths, including reinitialising `undef` leaves, so branch shape would not be
derivable.  With it, the existing matching lemma
`writeLeafTy_of_lvalTyping` supplies exactly the initialized-leaf witness needed
by `EnvWrite.shapePreserved_init` and `WriteBorrowTargets.shapePreserved_init`. -/
theorem WriteBorrowTargets.initialized_leaves_appendix96
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    WriteBorrowTargets rank env path targets rhsTy result →
    ∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy := by
  intro _htargets hwrites
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _rank env path targets rhsTy _result _ =>
      ∀ target, target ∈ targets → ∀ targetSlot,
        env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
        WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
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

/--
`ContainedBorrowsWellFormedIn source observer` says that every borrow contained
in `source` has targets that are also well formed in `observer`, at the
containing slot's lifetime.

This is the cross-branch invariant needed by `writeBorrowTargets`: when two
branch environments are joined, contained borrows from one branch can be
validated in the joined environment only if their targets are available on the
other branch as well.
-/
def ContainedBorrowsWellFormedIn (source observer : Env) : Prop :=
  ∀ {x slot mutable targets},
    source.slotAt x = some slot →
    source ⊢ x ↝ Ty.borrow mutable targets →
    BorrowTargetsWellFormedInSlot observer slot.lifetime targets

/--
Join transport needed for Definition 4.8(i).

This is the lval-shaped part of the Appendix 9.6 join argument: if the same
borrow target is fully typed on both branches, and both typings live long
enough for the observer slot, then the joined environment also gives that
target a full type at a lifetime that still lives long enough.
-/
structure FullLValTypingJoinTransport : Prop where
  full
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftTy) leftLifetime →
    LValTyping right target (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join target (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure LValTargetsTypingJoinTransport : Prop where
  targets
    {left right join : Env} {targets : List LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTargetsTyping left targets (.ty leftTy) leftLifetime →
    LValTargetsTyping right targets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join targets (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure DerefLValTypingJoinTransport : Prop where
  deref
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.ty leftTy) leftLifetime →
    LValTyping right (.deref source) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

structure DerefLValTypingJoinTransportWithUnion : Prop where
  deref
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.ty leftTy) leftLifetime →
    LValTyping right (.deref source) (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
          joinLifetime ≤ current

structure FullLValTypingJoinTransportWithUnion : Prop where
  full
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftTy) leftLifetime →
    LValTyping right target (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      PartialTyUnion (.ty leftTy) (.ty rightTy) (.ty joinTy) ∧
        LValTyping join target (.ty joinTy) joinLifetime ∧
          joinLifetime ≤ current

structure BoxFullLValTypingJoinTransport : Prop where
  boxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join source (.box (.ty joinTy)) joinLifetime ∧
        joinLifetime ≤ current

structure DerefBoxFullLValTypingJoinTransport : Prop where
  derefBoxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left (.deref source) (.box (.ty leftTy)) leftLifetime →
    LValTyping right (.deref source) (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.box (.ty joinTy)) joinLifetime ∧
        joinLifetime ≤ current

structure BoxBoxFullLValTypingJoinTransport : Prop where
  boxBoxFull
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.box (.ty leftTy))) leftLifetime →
    LValTyping right source (.box (.box (.ty rightTy))) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join source (.box (.box (.ty joinTy))) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefBoxFullLValTypingJoinTransport.of_boxBoxFull
    (htransport : BoxBoxFullLValTypingJoinTransport) :
    DerefBoxFullLValTypingJoinTransport where
  derefBoxFull := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleft hright hleftOutlives hrightOutlives
    have hleftSource :
        LValTyping left source (.box (.box (.ty leftTy))) leftLifetime :=
      LValTyping.deref_box_full_inv hleft
    have hrightSource :
        LValTyping right source (.box (.box (.ty rightTy))) rightLifetime :=
      LValTyping.deref_box_full_inv hright
    rcases htransport.boxBoxFull hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftSource hrightSource
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, hjoinSource, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, LValTyping.box hjoinSource, hjoinOutlives⟩

theorem BoxFullLValTypingJoinTransport.of_derefBoxFull
    (hderef : DerefBoxFullLValTypingJoinTransport) :
    BoxFullLValTypingJoinTransport where
  boxFull := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleft hright hleftOutlives hrightOutlives
    cases source with
    | var x =>
        exact LValTyping.var_join_box_full_bounded hjoin hleft hright
          hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.derefBoxFull hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleft hright hleftOutlives hrightOutlives

structure DerefLValTypingJoinConstructorLandmarks : Prop where
  box_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  box_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {rightMutable : Bool} {rightTargets : List LVal}
    {leftLifetime rightBorrowLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftMutable : Bool} {leftTargets : List LVal}
    {leftBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty}
    {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal}
    {leftBorrowLifetime rightBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefLValTypingJoinConstructorLandmarks.box_box_of_boxFull
    (hbox : BoxFullLValTypingJoinTransport)
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright hleftOutlives hrightOutlives
  rcases hbox.boxFull hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hright hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, LValTyping.box hjoinTyping, hjoinOutlives⟩

theorem LValTyping.deref_borrow_from_aligned_targets
    {env : Env} {source : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime targetLifetime current : Lifetime} {targetTy : Ty} :
    LValTyping env source (.ty (.borrow mutable targets)) borrowLifetime →
    LValTargetsTyping env targets (.ty targetTy) targetLifetime →
    targetLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping env (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hborrow htargets houtlives
  exact ⟨targetTy, targetLifetime,
    LValTyping.borrow hborrow htargets,
    houtlives⟩

structure DerefLValTypingJoinConstructorSplitLandmarks : Prop where
  boxFull :
    BoxFullLValTypingJoinTransport
  box_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {rightMutable : Bool} {rightTargets : List LVal}
    {leftLifetime rightBorrowLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.box (.ty leftTy)) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_box
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty} {leftMutable : Bool} {leftTargets : List LVal}
    {leftBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.box (.ty rightTy)) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current
  borrow_borrow
    {left right join : Env} {source : LVal}
    {leftTy rightTy : Ty}
    {leftMutable rightMutable : Bool}
    {leftTargets rightTargets : List LVal}
    {leftBorrowLifetime rightBorrowLifetime leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left source (.ty (.borrow leftMutable leftTargets)) leftBorrowLifetime →
    LValTargetsTyping left leftTargets (.ty leftTy) leftLifetime →
    LValTyping right source (.ty (.borrow rightMutable rightTargets)) rightBorrowLifetime →
    LValTargetsTyping right rightTargets (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTyping join (.deref source) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem DerefLValTypingJoinConstructorLandmarks.of_split
    (hlandmarks : DerefLValTypingJoinConstructorSplitLandmarks) :
    DerefLValTypingJoinConstructorLandmarks where
  box_box := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft hleft hright
      hleftOutlives hrightOutlives
    exact DerefLValTypingJoinConstructorLandmarks.box_box_of_boxFull
      hlandmarks.boxFull hjoin hleftContained hrightContained hleftInRight
      hrightInLeft hleft hright hleftOutlives hrightOutlives
  box_borrow := by
    intro left right join source leftTy rightTy rightMutable rightTargets
      leftLifetime rightBorrowLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleft hright hrightTargets
      hleftOutlives hrightOutlives
    exact hlandmarks.box_borrow hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hright hrightTargets
      hleftOutlives hrightOutlives
  borrow_box := by
    intro left right join source leftTy rightTy leftMutable leftTargets
      leftBorrowLifetime leftLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleft hleftTargets hright
      hleftOutlives hrightOutlives
    exact hlandmarks.borrow_box hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hleftTargets hright
      hleftOutlives hrightOutlives
  borrow_borrow := by
    intro left right join source leftTy rightTy leftMutable rightMutable
      leftTargets rightTargets leftBorrowLifetime rightBorrowLifetime leftLifetime
      rightLifetime current hjoin hleftContained hrightContained hleftInRight
      hrightInLeft hleft hleftTargets hright hrightTargets hleftOutlives
      hrightOutlives
    exact hlandmarks.borrow_borrow hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleft hleftTargets hright hrightTargets
      hleftOutlives hrightOutlives

theorem DerefLValTypingJoinTransport.of_constructorLandmarks
    (hlandmarks : DerefLValTypingJoinConstructorLandmarks) :
    DerefLValTypingJoinTransport where
  deref := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases hleftTyping with
    | box hleftSource =>
        cases hrightTyping with
        | box hrightSource =>
            exact hlandmarks.box_box hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hrightSource
              hleftOutlives hrightOutlives
        | borrow hrightSource hrightTargets =>
            exact hlandmarks.box_borrow hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hrightSource hrightTargets
              hleftOutlives hrightOutlives
    | borrow hleftSource hleftTargets =>
        cases hrightTyping with
        | box hrightSource =>
            exact hlandmarks.borrow_box hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hleftTargets hrightSource
              hleftOutlives hrightOutlives
        | borrow hrightSource hrightTargets =>
            exact hlandmarks.borrow_borrow hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleftSource hleftTargets hrightSource hrightTargets
              hleftOutlives hrightOutlives

theorem FullLValTypingJoinTransport.of_deref
    (hderef : DerefLValTypingJoinTransport) :
    FullLValTypingJoinTransport where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases target with
    | var x =>
        exact LValTyping.var_join_full_bounded hjoin hleftTyping hrightTyping
          hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.deref hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleftTyping hrightTyping
          hleftOutlives hrightOutlives

theorem DerefLValTypingJoinTransportWithUnion.to_deref
    (htransport : DerefLValTypingJoinTransportWithUnion) :
    DerefLValTypingJoinTransport where
  deref := by
    intro left right join source leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    rcases htransport.deref hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftTyping hrightTyping
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, _hunion, hjoinTyping, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩

theorem FullLValTypingJoinTransportWithUnion.to_full
    (htransport : FullLValTypingJoinTransportWithUnion) :
    FullLValTypingJoinTransport where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    rcases htransport.full hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftTyping hrightTyping
        hleftOutlives hrightOutlives with
      ⟨joinTy, joinLifetime, _hunion, hjoinTyping, hjoinOutlives⟩
    exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩

theorem FullLValTypingJoinTransportWithUnion.of_deref
    (hderef : DerefLValTypingJoinTransportWithUnion) :
    FullLValTypingJoinTransportWithUnion where
  full := by
    intro left right join target leftTy rightTy leftLifetime rightLifetime current
      hjoin hleftContained hrightContained hleftInRight hrightInLeft
      hleftTyping hrightTyping hleftOutlives hrightOutlives
    cases target with
    | var x =>
        exact LValTyping.var_join_full_bounded_with_union hjoin
          hleftTyping hrightTyping hleftOutlives hrightOutlives
    | deref source =>
        exact hderef.deref hjoin hleftContained hrightContained
          hleftInRight hrightInLeft hleftTyping hrightTyping
          hleftOutlives hrightOutlives

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

/-- Observer-target transport across a join via the runtime invariants
(one-directional: `source → left → join`).  Here `ContainedBorrows join` is
already established (the bootstrap runs first), so each transported target's
lifetime is bounded by the *unbounded*-strength invariant — packaged through the
rank-bounded `fullJoinTransport` with the per-target bound `N := φ(base t)+1` and
`hcontN` derived from the full `hcontJoin`. -/
theorem BorrowTargetsTransport.join_viaInvariants_left
    {source left right join : Env}
    (hjoin : EnvJoin left right join)
    (hstrL : ∀ x sE, left.slotAt x = some sE →
      ∃ sE', join.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty)
    (hlinJoin : Linearizable join) (hcohJoin : Coherent join)
    (hcontJoin : ContainedBorrowsWellFormed join)
    (hsourceLeft : BorrowTargetsTransport source left) :
    BorrowTargetsTransport source join := by
  obtain ⟨φ, hφJoin⟩ := hlinJoin
  intro slotLifetime targets htargets
  have hleft := hsourceLeft htargets
  intro target htarget
  rcases hleft target htarget with
    ⟨leftTy, leftLf, hleftTyping, _hleftOutlives, hleftBase⟩
  have hjoinBase := LValBaseOutlives.join_left hjoin hleftBase
  rcases fullJoinTransport_viaInvariants (N := φ (LVal.base target) + 1)
      hstrL hφJoin hcohJoin
      (fun x' slot' m' T' _ hslot' hcont' => hcontJoin x' slot' m' T' hslot' hcont')
      (Nat.lt_succ_self _) hleftTyping hjoinBase
    with ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives, hjoinBase⟩

theorem ContainedBorrowsWellFormedIn.of_transport {source observer : Env} :
    ContainedBorrowsWellFormed source →
    BorrowTargetsTransport source observer →
    ContainedBorrowsWellFormedIn source observer := by
  intro hcontained htransport x slot mutable targets hslot hcontains
  exact htransport (hcontained x slot mutable targets hslot hcontains)

theorem ContainedBorrowsWellFormed.in_self {env : Env} :
    ContainedBorrowsWellFormed env →
    ContainedBorrowsWellFormedIn env env := by
  intro hcontained x slot mutable targets hslot hcontains
  exact hcontained x slot mutable targets hslot hcontains

theorem LValTargetsTyping.join_full_singleton_of_fullLValTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {target : LVal}
    {leftTy rightTy : Ty} {leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTargetsTyping left [target] (.ty leftTy) leftLifetime →
    LValTargetsTyping right [target] (.ty rightTy) rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join [target] (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleftTargets hrightTargets hleftOutlives hrightOutlives
  cases hleftTargets with
  | singleton hleft =>
      cases hrightTargets with
      | singleton hright =>
          rcases htransport.full hjoin hleftContained hrightContained
              hleftInRight hrightInLeft hleft hright
              hleftOutlives hrightOutlives with
            ⟨joinTy, joinLifetime, hjoinTarget, hjoinOutlives⟩
          exact ⟨joinTy, joinLifetime,
            LValTargetsTyping.singleton hjoinTarget, hjoinOutlives⟩
      | cons _hhead hrest _hunion _hintersection =>
          cases hrest
  | cons _hhead hrest _hunion _hintersection =>
      cases hrest

theorem LValTargetsTyping.join_full_cons_of_parts
    {join : Env} {target : LVal} {rest : List LVal}
    {headTy restTy unionTy : Ty}
    {headLifetime restLifetime lifetime current : Lifetime} :
    LValTyping join target (.ty headTy) headLifetime →
    LValTargetsTyping join rest (.ty restTy) restLifetime →
    PartialTyUnion (.ty headTy) (.ty restTy) (.ty unionTy) →
    LifetimeIntersection headLifetime restLifetime lifetime →
    lifetime ≤ current →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join (target :: rest) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current := by
  intro hhead hrest hunion hintersection houtlives
  exact ⟨unionTy, lifetime,
    LValTargetsTyping.cons hhead hrest hunion hintersection,
    houtlives⟩

structure LValTargetsTypingJoinConsTypeUnionLandmark : Prop where
  typeUnion
    {left right join : Env} {target : LVal} {rest : List LVal}
    {leftHeadTy rightHeadTy leftRestTy rightRestTy leftTy rightTy : Ty}
    {joinHeadTy joinRestTy : Ty}
    {leftHeadLifetime rightHeadLifetime leftRestLifetime rightRestLifetime
      leftLifetime rightLifetime joinHeadLifetime joinRestLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftHeadTy) leftHeadLifetime →
    LValTyping right target (.ty rightHeadTy) rightHeadLifetime →
    LValTargetsTyping left rest (.ty leftRestTy) leftRestLifetime →
    LValTargetsTyping right rest (.ty rightRestTy) rightRestLifetime →
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty rightHeadTy) (.ty rightRestTy) (.ty rightTy) →
    LifetimeIntersection leftHeadLifetime leftRestLifetime leftLifetime →
    LifetimeIntersection rightHeadLifetime rightRestLifetime rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    LValTyping join target (.ty joinHeadTy) joinHeadLifetime →
    LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime →
    joinHeadLifetime ≤ current →
    joinRestLifetime ≤ current →
    ∃ joinTy, PartialTyUnion (.ty joinHeadTy) (.ty joinRestTy) (.ty joinTy)

structure LValTargetsTypingJoinConsLandmark : Prop where
  cons
    {left right join : Env} {target : LVal} {rest : List LVal}
    {leftHeadTy rightHeadTy leftRestTy rightRestTy leftTy rightTy : Ty}
    {leftHeadLifetime rightHeadLifetime leftRestLifetime rightRestLifetime
      leftLifetime rightLifetime current : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    LValTyping left target (.ty leftHeadTy) leftHeadLifetime →
    LValTyping right target (.ty rightHeadTy) rightHeadLifetime →
    LValTargetsTyping left rest (.ty leftRestTy) leftRestLifetime →
    LValTargetsTyping right rest (.ty rightRestTy) rightRestLifetime →
    PartialTyUnion (.ty leftHeadTy) (.ty leftRestTy) (.ty leftTy) →
    PartialTyUnion (.ty rightHeadTy) (.ty rightRestTy) (.ty rightTy) →
    LifetimeIntersection leftHeadLifetime leftRestLifetime leftLifetime →
    LifetimeIntersection rightHeadLifetime rightRestLifetime rightLifetime →
    leftLifetime ≤ current →
    rightLifetime ≤ current →
    (∃ joinHeadTy joinHeadLifetime,
      LValTyping join target (.ty joinHeadTy) joinHeadLifetime ∧
        joinHeadLifetime ≤ current) →
    (∃ joinRestTy joinRestLifetime,
      LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime ∧
        joinRestLifetime ≤ current) →
    ∃ joinTy joinLifetime,
      LValTargetsTyping join (target :: rest) (.ty joinTy) joinLifetime ∧
        joinLifetime ≤ current

theorem LValTargetsTypingJoinConsLandmark.of_typeUnion
    (htypeUnion : LValTargetsTypingJoinConsTypeUnionLandmark) :
    LValTargetsTypingJoinConsLandmark where
  cons := by
    intro left right join target rest leftHeadTy rightHeadTy leftRestTy rightRestTy
      leftTy rightTy leftHeadLifetime rightHeadLifetime leftRestLifetime
      rightRestLifetime leftLifetime rightLifetime current hjoin hleftContained
      hrightContained hleftInRight hrightInLeft hleftHead hrightHead hleftRest
      hrightRest hleftUnion hrightUnion hleftIntersection hrightIntersection
      hleftOutlives hrightOutlives hjoinHead hjoinRest
    rcases hjoinHead with
      ⟨joinHeadTy, joinHeadLifetime, hjoinHeadTyping, hjoinHeadOutlives⟩
    rcases hjoinRest with
      ⟨joinRestTy, joinRestLifetime, hjoinRestTyping, hjoinRestOutlives⟩
    rcases htypeUnion.typeUnion hjoin hleftContained hrightContained
        hleftInRight hrightInLeft hleftHead hrightHead hleftRest hrightRest
        hleftUnion hrightUnion hleftIntersection hrightIntersection
        hleftOutlives hrightOutlives hjoinHeadTyping hjoinRestTyping
        hjoinHeadOutlives hjoinRestOutlives with
      ⟨joinTy, hjoinUnion⟩
    rcases LifetimeIntersection.exists_of_common_inner
        hjoinHeadOutlives hjoinRestOutlives with
      ⟨joinLifetime, hjoinIntersection⟩
    exact LValTargetsTyping.join_full_cons_of_parts
      hjoinHeadTyping hjoinRestTyping hjoinUnion hjoinIntersection
      (LifetimeIntersection.le_of_le hjoinIntersection
        hjoinHeadOutlives hjoinRestOutlives)

theorem LValTargetsTypingJoinTransport.of_full_and_cons
    (hfull : FullLValTypingJoinTransport)
    (hcons : LValTargetsTypingJoinConsLandmark) :
    LValTargetsTypingJoinTransport := by
  constructor
  intro left right join targets leftTy rightTy leftLifetime rightLifetime current
    hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleftTargets hrightTargets hleftOutlives hrightOutlives
  induction targets generalizing leftTy rightTy leftLifetime rightLifetime current with
  | nil =>
      cases hleftTargets
  | cons target rest ih =>
      by_cases hrestNil : rest = []
      · subst hrestNil
        cases hleftTargets with
        | singleton hleftTarget =>
            cases hrightTargets with
            | singleton hrightTarget =>
  rcases hfull.full hjoin hleftContained hrightContained
                    hleftInRight hrightInLeft hleftTarget hrightTarget
                    hleftOutlives hrightOutlives with
                  ⟨joinTy, joinLifetime, hjoinTarget, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime,
                  LValTargetsTyping.singleton hjoinTarget, hjoinOutlives⟩
            | cons _hrightHead hrightRest _hrightUnion _hrightIntersection =>
                cases hrightRest
        | cons _hleftHead hleftRest _hleftUnion _hleftIntersection =>
            cases hleftRest
      · rcases LValTargetsTyping.cons_full_inv hrestNil hleftTargets with
          ⟨leftHeadTy, leftHeadLifetime, leftRestTy, leftRestLifetime,
            hleftHead, hleftRest, hleftUnion, hleftIntersection⟩
        rcases LValTargetsTyping.cons_full_inv hrestNil hrightTargets with
          ⟨rightHeadTy, rightHeadLifetime, rightRestTy, rightRestLifetime,
            hrightHead, hrightRest, hrightUnion, hrightIntersection⟩
        have hleftHeadOutlives : leftHeadLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.left_le hleftIntersection) hleftOutlives
        have hrightHeadOutlives : rightHeadLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.left_le hrightIntersection) hrightOutlives
        have hleftRestOutlives : leftRestLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.right_le hleftIntersection) hleftOutlives
        have hrightRestOutlives : rightRestLifetime ≤ current :=
          LifetimeOutlives.trans
            (LifetimeIntersection.right_le hrightIntersection) hrightOutlives
        have hjoinHead :
            ∃ joinHeadTy joinHeadLifetime,
              LValTyping join target (.ty joinHeadTy) joinHeadLifetime ∧
                joinHeadLifetime ≤ current :=
          hfull.full hjoin hleftContained hrightContained hleftInRight
            hrightInLeft hleftHead hrightHead hleftHeadOutlives
            hrightHeadOutlives
        have hjoinRest :
            ∃ joinRestTy joinRestLifetime,
              LValTargetsTyping join rest (.ty joinRestTy) joinRestLifetime ∧
                joinRestLifetime ≤ current :=
          ih hleftRest hrightRest hleftRestOutlives hrightRestOutlives
        exact hcons.cons hjoin hleftContained hrightContained hleftInRight
          hrightInLeft hleftHead hrightHead hleftRest hrightRest
          hleftUnion hrightUnion hleftIntersection hrightIntersection
          hleftOutlives hrightOutlives hjoinHead hjoinRest

theorem BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {targets : List LVal}
    {slotLifetime : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright target htarget
  -- Per-target invariant: each target is typed in both branches; transport the
  -- single typing across the join via the single-lval full join transport.  No
  -- joint target-list typing of the merged list is needed, so the list-level
  -- cons-union landmark is no longer required here.
  rcases hleft target htarget with
    ⟨leftTy, leftLifetime, hleftTyping, hleftOutlives, hleftBase⟩
  rcases hright target htarget with
    ⟨rightTy, rightLifetime, hrightTyping, hrightOutlives, _hrightBase⟩
  rcases htransport.full hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleftTyping hrightTyping
      hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives,
    LValBaseOutlives.join_left hjoin hleftBase⟩

theorem EnvJoin.preserves_observerTargets_of_lvalTargetsTypingJoinTransport
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} {targets : List LVal}
    {slotLifetime : Lifetime} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets := by
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport

theorem BorrowTargetsTransport.join_observer
    (htransport : FullLValTypingJoinTransport)
    {source left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    BorrowTargetsTransport source left →
    BorrowTargetsTransport source right →
    BorrowTargetsTransport source join := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright slotLifetime targets htargets
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport hjoin hleftContained hrightContained hleftInRight hrightInLeft
    (hleft htargets) (hright htargets)

theorem ContainedBorrowsWellFormedIn.join_observer
    (htransport : FullLValTypingJoinTransport)
    {source left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    ContainedBorrowsWellFormedIn source left →
    ContainedBorrowsWellFormedIn source right →
    ContainedBorrowsWellFormedIn source join := by
  intro hjoin hleftContained hrightContained hleftInRight hrightInLeft
    hleft hright x slot mutable targets hslot hcontains
  exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
    htransport hjoin hleftContained hrightContained hleftInRight hrightInLeft
    (hleft hslot hcontains)
    (hright hslot hcontains)

theorem ContainedBorrowsWellFormedIn.join_source
    {left right join observer : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormedIn left observer →
    ContainedBorrowsWellFormedIn right observer →
    ContainedBorrowsWellFormedIn join observer := by
  intro hjoin hleft hright x joinSlot mutable targets hjoinSlot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedSlotEq : containedSlot = joinSlot := by
    have hsomeEq : some containedSlot = some joinSlot := by
      rw [← hcontainedSlot, hjoinSlot]
    exact Option.some.inj hsomeEq
  have hcontainsJoin : PartialTyContains joinSlot.ty (.borrow mutable targets) := by
    simpa [hcontainedSlotEq] using hcontainsTy
  rcases EnvJoin.lifetimesPreserved_left hjoin x joinSlot hjoinSlot with
    ⟨leftSlot, hleftSlot, _hleftLifetime⟩
  rcases EnvJoin.lifetimesPreserved_right hjoin x joinSlot hjoinSlot with
    ⟨rightSlot, hrightSlot, _hrightLifetime⟩
  rcases EnvJoin.slot_union hjoin hleftSlot hrightSlot hjoinSlot with
    ⟨hleftLife, hrightLife, hunion⟩
  exact BorrowTargetsWellFormedInSlot.of_partialTyUnion
    (env := observer) (lifetime := joinSlot.lifetime) hunion
    (by
      intro leftMutable leftTargets hcontainsLeft
      have htargets :
          BorrowTargetsWellFormedInSlot observer leftSlot.lifetime leftTargets :=
        hleft hleftSlot ⟨leftSlot, hleftSlot, hcontainsLeft⟩
      simpa [hleftLife] using htargets)
    (by
      intro rightMutable rightTargets hcontainsRight
      have htargets :
          BorrowTargetsWellFormedInSlot observer rightSlot.lifetime rightTargets :=
        hright hrightSlot ⟨rightSlot, hrightSlot, hcontainsRight⟩
      simpa [hrightLife] using htargets)
    hcontainsJoin

/--
Branch-specific contained-borrow join preservation.

The unconditional statement "contained borrows are preserved by every
environment join" is too strong for partial environments: a borrow introduced
on one branch may have targets that are not fully typable on the other branch.
The `writeBorrowTargets` cons case supplies precisely the missing cross-branch
premises via its observer-target induction hypotheses.
-/
theorem ContainedBorrowsWellFormed.join_of_crossBranchTargets
    (htransport : FullLValTypingJoinTransport)
    {left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormedIn left right →
    ContainedBorrowsWellFormedIn right left →
    ContainedBorrowsWellFormed join := by
  intro hjoin hleftContained hrightContained hleftTargetsRight hrightTargetsLeft
  exact ContainedBorrowsWellFormed.join_of_inSlot hjoin
    (by
      intro x slot mutable targets hslot hcontains
      exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
        htransport hjoin hleftContained hrightContained
        hleftTargetsRight hrightTargetsLeft
        (hleftContained x slot mutable targets hslot hcontains)
        (hleftTargetsRight hslot hcontains))
    (by
      intro x slot mutable targets hslot hcontains
      exact BorrowTargetsWellFormedInSlot.join_of_lvalTargetsTypingJoinTransport
        htransport hjoin hleftContained hrightContained
        hleftTargetsRight hrightTargetsLeft
        (hrightTargetsLeft hslot hcontains)
        (hrightContained x slot mutable targets hslot hcontains))

structure UpdateBorrowInvariantCrossLandmarks : Prop where
  envWrite_preserves_core
    {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env

/-- Rank side condition needed for preserving one common linearization witness
through a mutable-borrow fan-out.

For every concrete branch write, each *new borrow edge* whose target came from
the RHS type must point to a strictly lower-ranked base.  This is the local
acyclicity premise behind the old bare `EnvWrite.preserves_linearizedBy`
obligation. -/
def WriteBorrowTargetsRhsVarsBelowBranches (φ : Name → Nat) (rank : Nat)
    (env : Env) (path : Path) (writeTargets : List LVal) (rhsTy : Ty) : Prop :=
  ∀ target, target ∈ writeTargets → ∀ updated,
    EnvWrite rank env (prependPath path target) rhsTy updated →
    EnvWriteRhsBorrowTargetsBelow φ updated rhsTy

/-- Coherence obligations for every branch and branch join in a mutable-borrow
fan-out write.

This is the fan-out analogue of the strengthened assignment coherence premise.
Each concrete branch write must expose the write-coherence transport needed by
`EnvWrite.preserves_coherent_of_obligations`; each cons join must expose the
join-coherence transport needed by `EnvJoin.preserves_coherent_of_obligations`.
-/
structure WriteBorrowTargetsCoherenceObligations
    (rank : Nat) (env : Env) (path : Path) (writeTargets : List LVal)
    (rhsTy : Ty) : Prop where
  write
    (target : LVal) :
    target ∈ writeTargets →
    ∀ updated,
      EnvWrite rank env (prependPath path target) rhsTy updated →
      EnvWriteCoherenceObligations env updated (LVal.base (prependPath path target))
  join
    (target : LVal) (rest : List LVal) :
    target ∈ writeTargets →
    (∀ t, t ∈ rest → t ∈ writeTargets) →
    ∀ updated restEnv result,
      EnvWrite rank env (prependPath path target) rhsTy updated →
      WriteBorrowTargets rank env path rest rhsTy restEnv →
      EnvJoin updated restEnv result →
      EnvJoinCoherenceObligations updated restEnv result

/-- Constructive variant of `WriteBorrowTargets.preserves_core_of_crossLandmarks`
that does not rely on the bare `EnvWrite.preserves_linearizedBy` statement.

The extra `WriteBorrowTargetsRhsVarsBelowBranches` premise is the small
borrow-inference/rank side condition needed to keep the same linearization witness
across every fan-out branch. -/
theorem WriteBorrowTargets.preserves_core_of_crossLandmarks
    (hlandmarks : UpdateBorrowInvariantCrossLandmarks)
    {rank : Nat} {env result : Env} {path : Path}
    {writeTargets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime}
    {φ : Name → Nat} :
    0 < rank →
    Coherent env →
    LinearizedBy φ env →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    (∀ target, target ∈ writeTargets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    WriteBorrowTargetsRhsVarsBelowBranches φ rank env path writeTargets rhsTy →
    WriteBorrowTargetsCoherenceObligations rank env path writeTargets rhsTy →
    WriteBorrowTargets rank env path writeTargets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro hrank hcoh hφ hcontained hrhs hleaf hbelow hfanoutCoh hwrites
  exact (WriteBorrowTargets.rec
    (motive_1 := fun _rank _env _path _oldTy _rhsTy _result _updatedTy _ =>
      True)
    (motive_2 := fun _rank env _path _writeTargets constructorTy result _ =>
      0 < _rank → Coherent env → LinearizedBy φ env →
      ∀ {slotLifetime},
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        (∀ target, target ∈ _writeTargets → ∀ targetSlot,
          env.slotAt (LVal.base (prependPath _path target)) = some targetSlot →
          WriteLeafTy env (LVal.path (prependPath _path target))
            targetSlot.ty constructorTy) →
        WriteBorrowTargetsRhsVarsBelowBranches φ _rank env _path _writeTargets constructorTy →
        WriteBorrowTargetsCoherenceObligations _rank env _path _writeTargets constructorTy →
        (ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env) ∧
          Coherent result ∧ LinearizedBy φ result)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by intro env old ty; trivial)
    (by intro env rank old joined ty _hshape _hjoin; trivial)
    (by intro env₁ env₂ rank path inner updatedInner ty hupdate ih; trivial)
    (by intro env₁ env₂ rank path targets ty hwrites ih; trivial)
    (by
      intro rank env path ty _hrank hcoh hlinBy slotLifetime hcontained _hrhs _hleaf
        _hbelow _hfanoutCoh
      exact ⟨⟨hcontained, BorrowTargetsTransport.refl env,
        ContainedBorrowsWellFormed.in_self hcontained⟩, hcoh, hlinBy⟩)
    (by
      intro rank env updated path target ty hwrite _htyped _ih
        hrank hcoh hlinBy slotLifetime hcontained hrhs _hleaf hbelow hfanoutCoh
      have hlinEnv : Linearizable env := Linearizable.of_linearizedBy hlinBy
      have hlinUBy :=
        EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
          hwrite hlinBy (hbelow target (by simp) updated hwrite)
      have hlinU := Linearizable.of_linearizedBy hlinUBy
      have hcohU := EnvWrite.preserves_coherent_of_obligations hcoh
        (hfanoutCoh.write target (by simp) updated hwrite)
      exact ⟨hlandmarks.envWrite_preserves_core hrank hcontained hrhs hwrite,
        hcohU, hlinUBy⟩)
    (by
      intro rank env updated restEnv result path target rest ty
        hwrite _htyped hwrites hjoin _ihWrite ihWrites
        hrank hcoh hlinBy slotLifetime hcontained hrhs hleaf hbelow hfanoutCoh
      have hlinEnv : Linearizable env := Linearizable.of_linearizedBy hlinBy
      have hlinUBy :=
        EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
          hwrite hlinBy (hbelow target (by simp) updated hwrite)
      have hlinU := Linearizable.of_linearizedBy hlinUBy
      have hcohU := EnvWrite.preserves_coherent_of_obligations hcoh
        (hfanoutCoh.write target (by simp) updated hwrite)
      rcases hlandmarks.envWrite_preserves_core hrank hcontained hrhs hwrite with
        ⟨hupdatedContained, hupdatedTransport, hupdatedInEnv⟩
      have hleafRest :
          ∀ t, t ∈ rest → ∀ slot,
            env.slotAt (LVal.base (prependPath path t)) = some slot →
            WriteLeafTy env (LVal.path (prependPath path t)) slot.ty ty := by
        intro t ht slot hslot
        exact hleaf t (List.mem_cons_of_mem target ht) slot hslot
      have hbelowRest :
          WriteBorrowTargetsRhsVarsBelowBranches φ rank env path rest ty := by
        intro t ht branch hbranch
        exact hbelow t (List.mem_cons_of_mem target ht) branch hbranch
      have hfanoutCohRest :
          WriteBorrowTargetsCoherenceObligations rank env path rest ty := {
        write := by
          intro t ht branch hbranch
          exact hfanoutCoh.write t (List.mem_cons_of_mem target ht) branch hbranch
        join := by
          intro t later ht hlater branch laterEnv branchResult hbranch hlaterWrites hbranchJoin
          exact hfanoutCoh.join t later (List.mem_cons_of_mem target ht)
            (fun u hu => List.mem_cons_of_mem target (hlater u hu))
            branch laterEnv branchResult hbranch hlaterWrites hbranchJoin
      }
      rcases ihWrites hrank hcoh hlinBy hcontained hrhs hleafRest hbelowRest
          hfanoutCohRest with
        ⟨⟨hrestContained, _hrestTransport, hrestInEnv⟩, hcohRest, hlinRestBy⟩
      have hlinRest := Linearizable.of_linearizedBy hlinRestBy
      have hlinRBy := EnvJoin.preserves_linearizedBy hjoin hlinUBy hlinRestBy
      have hlinR := Linearizable.of_linearizedBy hlinRBy
      have hjoinCoh : EnvJoinCoherenceObligations updated restEnv result :=
        hfanoutCoh.join target rest (by simp)
          (fun t ht => List.mem_cons_of_mem target ht)
          updated restEnv result hwrite hwrites hjoin
      have hcohR := EnvJoin.preserves_coherent_of_obligations hcohU hcohRest hjoinCoh
      have hupdShape : EnvShapePreserved env updated :=
        EnvWrite.shapePreserved_init hrank hwrite
          (fun slot hslot => hleaf target (by simp) slot hslot)
      have hrestShape : EnvShapePreserved env restEnv :=
        WriteBorrowTargets.shapePreserved_init hrank hwrites
          (fun t ht slot hslot =>
            hleaf t (List.mem_cons_of_mem target ht) slot hslot)
      have hbranch : ∀ x sL sR, updated.slotAt x = some sL → restEnv.slotAt x = some sR →
          PartialTy.sameShape sL.ty sR.ty :=
        EnvShapePreserved.branch_sameShape hupdShape hrestShape
      have hstrL := EnvJoin.fanOutShapeMap_left hjoin hbranch
      have hstrR := EnvJoin.fanOutShapeMap_right hjoin hbranch
      have hcontJoin :=
        ContainedBorrowsWellFormed.join_viaInvariants hjoin hstrL hstrR hlinR hcohR
          hupdatedContained hrestContained
      refine ⟨⟨hcontJoin,
        BorrowTargetsTransport.join_viaInvariants_left hjoin hstrL hlinR hcohR
          hcontJoin hupdatedTransport,
        ContainedBorrowsWellFormedIn.join_source hjoin hupdatedInEnv hrestInEnv⟩,
        hcohR, hlinRBy⟩)
    (by intro rank env₁ env₂ lv slot ty updatedTy hslot hupdate ih; trivial)
    hwrites hrank hcoh hφ hcontained hrhs hleaf hbelow hfanoutCoh).1

theorem UpdateBorrowInvariantObligations.of_crossLandmarks
    (hlandmarks : UpdateBorrowInvariantCrossLandmarks)
    (hfanoutRanked :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty} {φ : Name → Nat},
        WriteBorrowTargetsRhsVarsBelowBranches φ rank env path targets rhsTy)
    (hfanoutCoherence :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty},
        WriteBorrowTargetsCoherenceObligations rank env path targets rhsTy) :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed := by
    intro rank env result path targets rhsTy slotLifetime
      hrank hcoh hlin hcontained htargets hleaf hrhs hwrites
    rcases hlin with ⟨φ, hφ⟩
    rcases WriteBorrowTargets.preserves_core_of_crossLandmarks
        hlandmarks hrank hcoh hφ hcontained hrhs hleaf
        (hfanoutRanked (rank := rank) (env := env) (path := path)
          (targets := targets) (rhsTy := rhsTy) (φ := φ))
        (hfanoutCoherence (rank := rank) (env := env) (path := path)
          (targets := targets) (rhsTy := rhsTy))
        hwrites with
      ⟨hresultContained, htransport, _hresultInEnv⟩
    exact ⟨hresultContained, htransport htargets⟩

-- The deref-of-borrow join transport landmark (`borrow_borrow`, formerly the
-- `FullLValTypingJoinTransport` chain) is no longer needed: the write fan-out
-- driver (`WriteBorrowTargets.preserves_core_of_crossLandmarks`) now establishes
-- borrow-target join preservation directly and one-directionally via the
-- transport keystone (`ContainedBorrowsWellFormed.join_viaInvariants` etc.),
-- supplied with the runtime invariants `Coherent`/`Linearizable`.  The old
-- symmetric `FullLValTypingJoinTransport` structure and its consumers remain in
-- the file as dead (proven) scaffolding.

/-- Old borrow-target transport for one write, derived from the transport keystone.

This is one of the constructive pieces behind the legacy single-write Appendix
9.6 claim below.  It deliberately exposes the runtime facts the keystone needs:
the write result must be shape-preserving/strengthening from the source, already
linearized, coherent, and contained-borrow well formed.
-/
theorem EnvWrite.borrowTargetsTransport_of_shapeMap
    {rank : Nat} {env result : Env} {lv : LVal} {rhsTy : Ty}
    {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    BorrowTargetsTransport env result := by
  intro hwrite hshapeMap hlinResult hcohResult hcontainedResult
    slotLifetime targets htargets target htarget
  rcases htargets target htarget with
    ⟨sourceTy, sourceLifetime, hsourceTyping, hsourceOutlives, hsourceBase⟩
  have hresultBase : LValBaseOutlives result target slotLifetime :=
    LValBaseOutlives.write hwrite hsourceBase
  rcases fullJoinTransport_viaInvariants
      (source := env) (join := result) (target := target)
      (sourceTy := sourceTy) (sourceLifetime := sourceLifetime)
      (current := slotLifetime) (φ := φ) (N := φ (LVal.base target) + 1)
      hshapeMap hlinResult hcohResult
      (fun x slot mutable targets _hrank hslot hcontains =>
        hcontainedResult x slot mutable targets hslot hcontains)
      (Nat.lt_succ_self _) hsourceTyping hresultBase with
    ⟨resultTy, resultLifetime, hresultTyping, hresultOutlives⟩
  exact ⟨resultTy, resultLifetime, hresultTyping, hresultOutlives, hresultBase⟩

/-- Constructive packaging of the parts of the legacy single-write core claim
once the result-side invariants have been established separately.

The nontrivial old-target transport component is proved by
`EnvWrite.borrowTargetsTransport_of_shapeMap`; the two contained-borrow facts are
kept explicit because those are structural update obligations, not consequences
of a bare `EnvWrite` plus RHS well-formedness alone.
-/
theorem EnvWrite.preserves_core_appendix96_of_result_invariants
    {rank : Nat} {env result : Env} {lv : LVal} {rhsTy : Ty}
    {φ : Name → Nat} :
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    ContainedBorrowsWellFormedIn result env →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro hwrite hshapeMap hlinResult hcohResult hcontainedResult hresultInEnv
  exact ⟨hcontainedResult,
    EnvWrite.borrowTargetsTransport_of_shapeMap
      hwrite hshapeMap hlinResult hcohResult hcontainedResult,
    hresultInEnv⟩

/-- Appendix 9.6 core preservation for one positive-rank write, with the
result-side invariants exposed.

This is the proved replacement for the old bare claim.  A single `EnvWrite` plus
RHS per-target well-formedness is not enough to derive old-target transport; the
caller must also provide the shape map and result-side linearization/coherence
and contained-borrow facts needed by the transport keystone. -/
theorem EnvWrite.preserves_core_appendix96
    {rank : Nat} {env result : Env} {lv : LVal}
    {rhsTy : Ty} {slotLifetime : Lifetime} {φ : Name → Nat} :
    0 < rank →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    (∀ x sE, env.slotAt x = some sE →
      ∃ sE', result.slotAt x = some sE' ∧
        PartialTy.sameShape sE.ty sE'.ty ∧ PartialTyStrengthens sE.ty sE'.ty) →
    LinearizedBy φ result →
    Coherent result →
    ContainedBorrowsWellFormed result →
    ContainedBorrowsWellFormedIn result env →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsTransport env result ∧
      ContainedBorrowsWellFormedIn result env := by
  intro _hrank _hcontained _hrhs hwrite hshape hlinResult hcohResult
    hcontainedResult hresultInEnv
  exact EnvWrite.preserves_core_appendix96_of_result_invariants
    hwrite hshape hlinResult hcohResult hcontainedResult hresultInEnv

/-- Legacy packaging of Appendix 9.6 cross-landmarks.

The broad single-write field is no longer hidden behind a proof package.  Older callers
that still want this package must provide that compatibility premise explicitly;
the proved replacement is `EnvWrite.preserves_core_appendix96`, whose statement
exposes the result-side invariants needed for old-target transport.
-/
theorem updateBorrowInvariantCrossLandmarks_appendix96
    (hwriteCore :
      ∀ {rank : Nat} {env result : Env} {lv : LVal}
        {rhsTy : Ty} {slotLifetime : Lifetime},
        0 < rank →
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
        EnvWrite rank env lv rhsTy result →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env) :
    UpdateBorrowInvariantCrossLandmarks where
  envWrite_preserves_core := by
    intro rank env result lv rhsTy slotLifetime hrank hcontained hrhs hwrite
    exact hwriteCore hrank hcontained hrhs hwrite

structure UpdateBorrowInvariantLandmarks : Prop where
  envWrite_preserves_observerTargets
    {rank : Nat} {env result : Env} {lv : LVal}
    {observerTargets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    EnvWrite rank env lv rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime observerTargets
  envJoin_preserves_containedBorrowsWellFormed
    {left right join : Env} :
    EnvJoin left right join →
    ContainedBorrowsWellFormed left →
    ContainedBorrowsWellFormed right →
    ContainedBorrowsWellFormed join
  envJoin_preserves_observerTargets
    {left right join : Env} {targets : List LVal} {slotLifetime : Lifetime} :
    EnvJoin left right join →
    BorrowTargetsWellFormedInSlot left slotLifetime targets →
    BorrowTargetsWellFormedInSlot right slotLifetime targets →
    BorrowTargetsWellFormedInSlot join slotLifetime targets

theorem WriteBorrowTargets.preserves_observerTargets_of_landmarks
    (hlandmarks : UpdateBorrowInvariantLandmarks)
    {rank : Nat} {env result : Env} {path : Path}
    {writeTargets observerTargets : List LVal} {rhsTy : Ty}
    {slotLifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path writeTargets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime observerTargets := by
  intro hcontained hobservers hrhs hwrites
  exact WriteBorrowTargets.rec
    (motive_1 := fun _rank _env _path _oldTy _rhsTy _result _updatedTy _ =>
      True)
    (motive_2 := fun _rank env _path _writeTargets constructorTy result _ =>
      ∀ {observerTargets slotLifetime},
        ContainedBorrowsWellFormed env →
        BorrowTargetsWellFormedInSlot env slotLifetime observerTargets →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsWellFormedInSlot result slotLifetime observerTargets)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by
      intro env old ty
      trivial)
    (by
      intro env rank old joined ty _hshape _hjoin
      trivial)
    (by
      intro env₁ env₂ rank path inner updatedInner ty hupdate ih
      trivial)
    (by
      intro env₁ env₂ rank path targets ty hwrites ih
      trivial)
    (by
      intro rank env path ty observerTargets slotLifetime hcontained hobservers _hrhs
      exact ⟨hcontained, hobservers⟩)
    (by
      intro rank env updated path target ty hwrite _htyped _ih
        observerTargets slotLifetime hcontained hobservers hrhs
      exact hlandmarks.envWrite_preserves_observerTargets
        hcontained hobservers hrhs hwrite)
    (by
      intro rank env updated restEnv result path target rest ty
        hwrite _htyped _hwrites hjoin _ihWrite ihWrites
        observerTargets slotLifetime hcontained hobservers hrhs
      rcases hlandmarks.envWrite_preserves_observerTargets
          hcontained hobservers hrhs hwrite with
        ⟨hupdatedContained, hupdatedObservers⟩
      rcases ihWrites hcontained hobservers hrhs with
        ⟨hrestContained, hrestObservers⟩
      exact ⟨
        hlandmarks.envJoin_preserves_containedBorrowsWellFormed
          hjoin hupdatedContained hrestContained,
        hlandmarks.envJoin_preserves_observerTargets hjoin
          hupdatedObservers hrestObservers⟩)
    (by
      intro rank env₁ env₂ lv slot ty updatedTy hslot hupdate ih
      trivial)
    hwrites hcontained hobservers hrhs

theorem UpdateBorrowInvariantObligations.of_landmarks
    (hlandmarks : UpdateBorrowInvariantLandmarks) :
    UpdateBorrowInvariantObligations where
  writeBorrowTargets_preserves_containedBorrowsWellFormed := by
    intro rank env result path targets rhsTy slotLifetime
      _hrank _hcoh _hlin hcontained htargets _hleaf hrhs hwrites
    exact WriteBorrowTargets.preserves_observerTargets_of_landmarks
      hlandmarks hcontained htargets hrhs hwrites

/--
Definition 3.23 `writeBorrowTargets` borrow-invariant obligation.

This is the remaining paper-level update invariant needed by Lemma 4.9.  The
legacy theorem `updateBorrowInvariantObligations_appendix96` below records the
old Appendix 9.6 target as explicit result-side rank/coherence premises rather
than hiding them as assumptions.
-/
theorem WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {rank : Nat} {env result : Env} {path : Path}
    {targets : List LVal} {rhsTy : Ty} {slotLifetime : Lifetime} :
    0 < rank →
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    BorrowTargetsWellFormedInSlot env slotLifetime targets →
    (∀ target, target ∈ targets → ∀ targetSlot,
      env.slotAt (LVal.base (prependPath path target)) = some targetSlot →
      WriteLeafTy env (LVal.path (prependPath path target)) targetSlot.ty rhsTy) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    WriteBorrowTargets rank env path targets rhsTy result →
    ContainedBorrowsWellFormed result ∧
      BorrowTargetsWellFormedInSlot result slotLifetime targets := by
  exact hobligations.writeBorrowTargets_preserves_containedBorrowsWellFormed

/-- Appendix Lemma 9.6 package for the borrow-target fan-out.

This is an obligation-parametric compatibility route: the broad write-core and
fan-out rank/coherence facts are explicit premises until the remaining
result-side update obligations are proved constructively.
-/
theorem updateBorrowInvariantObligations_appendix96
    (hwriteCore :
      ∀ {rank : Nat} {env result : Env} {lv : LVal}
        {rhsTy : Ty} {slotLifetime : Lifetime},
        0 < rank →
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
        EnvWrite rank env lv rhsTy result →
        ContainedBorrowsWellFormed result ∧
          BorrowTargetsTransport env result ∧
          ContainedBorrowsWellFormedIn result env)
    (hfanoutRanked :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty} {φ : Name → Nat},
        WriteBorrowTargetsRhsVarsBelowBranches φ rank env path targets rhsTy)
    (hfanoutCoherence :
      ∀ {rank : Nat} {env : Env} {path : Path} {targets : List LVal}
        {rhsTy : Ty},
        WriteBorrowTargetsCoherenceObligations rank env path targets rhsTy) :
    UpdateBorrowInvariantObligations := by
  exact UpdateBorrowInvariantObligations.of_crossLandmarks
    (updateBorrowInvariantCrossLandmarks_appendix96 hwriteCore)
    hfanoutRanked hfanoutCoherence

/--
Appendix Lemma 9.6 at the Definition 3.23 update-relation level.

The statement tracks both components needed by the enclosing `write` rule:
the intermediate environment remains contained-borrow well formed, and the
partial type returned by `update_k` has well-formed contained borrows at the
allocation lifetime of the slot being rebuilt.
-/
theorem UpdateAtPath.preserves_containedBorrowsWellFormed_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {rank : Nat} {env result : Env} {path : Path}
    {oldTy updatedTy : PartialTy} {rhsTy : Ty} {slotLifetime : Lifetime} :
    Coherent env →
    Linearizable env →
    ContainedBorrowsWellFormed env →
    PartialTyBorrowsWellFormedInSlot env slotLifetime oldTy →
    PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty rhsTy) →
    UpdateAtPath rank env path oldTy rhsTy result updatedTy →
    ContainedBorrowsWellFormed result ∧
      PartialTyBorrowsWellFormedInSlot result slotLifetime updatedTy := by
  intro hcoh hlin hcontained holdTy hrhsTy hupdate
  exact UpdateAtPath.rec
    (motive_1 := fun _rank env _path oldTy constructorTy result updatedTy _ =>
      Coherent env → Linearizable env →
      ∀ {slotLifetime},
        ContainedBorrowsWellFormed env →
        PartialTyBorrowsWellFormedInSlot env slotLifetime oldTy →
        PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty constructorTy) →
        ContainedBorrowsWellFormed result ∧
          PartialTyBorrowsWellFormedInSlot result slotLifetime updatedTy)
    (motive_2 := fun _rank _env _path _targets _rhsTy _result _ => True)
    (motive_3 := fun _rank _env _lv _rhsTy _result _ => True)
    (by
      intro env old ty hcoh hlin slotLifetime hcontained _holdTy hrhsTy
      exact ⟨hcontained, hrhsTy⟩)
    (by
      intro env rank old joined ty _hshape hjoin hcoh hlin slotLifetime hcontained holdTy hrhsTy
      exact ⟨hcontained,
        PartialTyBorrowsWellFormedInSlot.of_partialTyUnion
          (by simpa [PartialTyUnion] using hjoin) holdTy hrhsTy⟩)
    (by
      intro env₁ env₂ rank path inner updatedInner ty _hinner ih
        hcoh hlin slotLifetime hcontained holdTy hrhsTy
      rcases ih hcoh hlin hcontained
          (PartialTyBorrowsWellFormedInSlot.box_inv holdTy)
          hrhsTy with
        ⟨hcontainedResult, hupdatedInner⟩
      exact ⟨hcontainedResult, PartialTyBorrowsWellFormedInSlot.box hupdatedInner⟩)
    (by
      intro env₁ env₂ rank path targets ty hwrites _ih
        hcoh hlin slotLifetime hcontained holdTy hrhsTy
      have htargets :
          BorrowTargetsWellFormedInSlot env₁ slotLifetime targets :=
        holdTy PartialTyContains.here
      have htargetLeaves :
          ∀ target, target ∈ targets → ∀ targetSlot,
            env₁.slotAt (LVal.base (prependPath path target)) = some targetSlot →
            WriteLeafTy env₁ (LVal.path (prependPath path target)) targetSlot.ty ty :=
        WriteBorrowTargets.initialized_leaves_appendix96 htargets hwrites
      rcases WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
          hobligations (Nat.succ_pos rank) hcoh hlin hcontained htargets htargetLeaves
          hrhsTy hwrites with
        ⟨hcontainedResult, htargetsResult⟩
      exact ⟨hcontainedResult, by
        intro mutable selected hcontains
        cases hcontains
        exact htargetsResult⟩)
    (by
      intro rank env path ty
      trivial)
    (by
      intro rank env updated path target ty _hwrite _ih
      trivial)
    (by
      intro rank env updated restEnv result path target rest ty
        _hwrite _hwrites _hjoin _ihWrite _ihWrites
      trivial)
    (by
      intro rank env₁ env₂ lv slot ty updatedTy _hslot _hupdate _ih
      trivial)
    hupdate hcoh hlin hcontained holdTy hrhsTy

/--
Appendix Lemma 9.6, `W-Box` branch of Definition 3.23.

Updating through an owned box recursively updates the boxed partial type, then
replaces the original base slot with `.box updatedInner`.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_box_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ writeEnv env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {inner updatedInner oldTy : PartialTy}
    {rhs : Term} {rhsTy : Ty} {writeSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    env₂.slotAt (LVal.base lhs) = some writeSlot →
    writeSlot.ty = .box inner →
    UpdateAtPath 0 env₂ (LVal.path lhs) inner rhsTy writeEnv updatedInner →
    env₃ = writeEnv.update (LVal.base lhs)
      { writeSlot with ty := .box updatedInner } →
    ¬ WriteProhibited env₃ (.deref lhs) →
    ContainedBorrowsWellFormed env₃ := by
  intro hwellInitial hwellFormed hLhs _htargetLifetime hRhs _hshape hwellRhs
    hwriteSlot hwriteTy hinnerUpdate henv₃ hnotWrite
  subst henv₃
  have htargetOutlivesSlot :
      targetLifetime ≤ writeSlot.lifetime :=
    TermTyping.target_lifetime_outlives_surviving_base_slot
      hwellInitial hLhs hRhs (by simpa [LVal.base] using hwriteSlot)
  have hslotPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime writeSlot.ty :=
    ContainedBorrowsWellFormed.slot_partial hwellFormed.1 hwriteSlot
  have hinnerPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime inner := by
    rw [hwriteTy] at hslotPartial
    exact PartialTyBorrowsWellFormedInSlot.box_inv hslotPartial
  have hrhsPartialAtTarget :
      PartialTyBorrowsWellFormedInSlot env₂ targetLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellRhs
  have hrhsPartialAtSlot :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.weaken
      hrhsPartialAtTarget htargetOutlivesSlot
  rcases UpdateAtPath.preserves_containedBorrowsWellFormed_appendix96
      hobligations hwellFormed.2.2.1 hwellFormed.2.2.2 hwellFormed.1 hinnerPartial
      hrhsPartialAtSlot hinnerUpdate with
    ⟨hcontainedWriteEnv, hupdatedInnerPartial⟩
  have hnotWriteVar :
      ¬ WriteProhibited
        (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
        (.var (LVal.base lhs)) := by
    exact not_writeProhibited_var_base hnotWrite
  have hslotTargets :
      PartialTyBorrowsWellFormedInSlot
        (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
        writeSlot.lifetime
        ({ writeSlot with ty := .box updatedInner }).ty := by
    change PartialTyBorrowsWellFormedInSlot
      (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
      writeSlot.lifetime
      (.box updatedInner)
    have hboxedPartial :
        PartialTyBorrowsWellFormedInSlot writeEnv writeSlot.lifetime
          (.box updatedInner) :=
      PartialTyBorrowsWellFormedInSlot.box hupdatedInnerPartial
    intro mutable targets hcontains
    have htransported :
        PartialTyBorrowsWellFormedInSlot
          (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner })
          writeSlot.lifetime
          (.box updatedInner) :=
      PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts
        (x := LVal.base lhs)
        (slot := { writeSlot with ty := .box updatedInner })
        (partialTy := .box updatedInner)
        hnotWriteVar
        hboxedPartial
        (by
          intro mutable targets hcontains target htarget
          have hcontainsUpdated :
              (writeEnv.update (LVal.base lhs) { writeSlot with ty := .box updatedInner }) ⊢
                LVal.base lhs ↝ Ty.borrow mutable targets :=
            ⟨{ writeSlot with ty := .box updatedInner },
              by simp [Env.update],
              hcontains⟩
          exact not_pathConflicts_of_not_writeProhibited_contains
            hnotWriteVar hcontainsUpdated htarget)
    exact htransported hcontains
  exact ContainedBorrowsWellFormed.update_slot
    hcontainedWriteEnv hslotTargets hnotWriteVar

/--
Appendix Lemma 9.6, `W-MutB` branch of Definition 3.23.

Updating through a mutable borrow writes every possible borrowed target at
`rank + 1` and joins the resulting environments.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_mutBorrow_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {targets : List LVal} {oldTy : PartialTy}
    {rhs : Term} {rhsTy : Ty} {writeSlot : EnvSlot} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    env₂.slotAt (LVal.base lhs) = some writeSlot →
    writeSlot.ty = .ty (.borrow true targets) →
    WriteBorrowTargets 1 env₂ (LVal.path lhs) targets rhsTy env₃ →
    ¬ WriteProhibited
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
      (.deref lhs) →
    ContainedBorrowsWellFormed
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) }) := by
  intro hwellInitial hwellFormed hLhs _htargetLifetime hRhs _hshape hwellRhs
    hwriteSlot hwriteTy hwrites hnotWrite
  have htargetOutlivesSlot :
      targetLifetime ≤ writeSlot.lifetime :=
    TermTyping.target_lifetime_outlives_surviving_base_slot
      hwellInitial hLhs hRhs (by simpa [LVal.base] using hwriteSlot)
  have hslotPartial :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime writeSlot.ty :=
    ContainedBorrowsWellFormed.slot_partial hwellFormed.1 hwriteSlot
  have htargetsOld :
      BorrowTargetsWellFormedInSlot env₂ writeSlot.lifetime targets := by
    rw [hwriteTy] at hslotPartial
    exact hslotPartial PartialTyContains.here
  have hrhsPartialAtTarget :
      PartialTyBorrowsWellFormedInSlot env₂ targetLifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellRhs
  have hrhsPartialAtSlot :
      PartialTyBorrowsWellFormedInSlot env₂ writeSlot.lifetime (.ty rhsTy) :=
    PartialTyBorrowsWellFormedInSlot.weaken
      hrhsPartialAtTarget htargetOutlivesSlot
  have htargetLeaves :
      ∀ target, target ∈ targets → ∀ targetSlot,
        env₂.slotAt (LVal.base (prependPath (LVal.path lhs) target)) = some targetSlot →
        WriteLeafTy env₂ (LVal.path (prependPath (LVal.path lhs) target))
          targetSlot.ty rhsTy :=
    WriteBorrowTargets.initialized_leaves_appendix96 htargetsOld hwrites
  rcases WriteBorrowTargets.preserves_containedBorrowsWellFormed_appendix96
      hobligations (by decide : 0 < 1) hwellFormed.2.2.1 hwellFormed.2.2.2
        hwellFormed.1 htargetsOld htargetLeaves hrhsPartialAtSlot hwrites with
    ⟨hcontainedWriteEnv, htargetsResult⟩
  have hnotWriteVar :
      ¬ WriteProhibited
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        (.var (LVal.base lhs)) := by
    exact not_writeProhibited_var_base hnotWrite
  have htargetsFinal :
      BorrowTargetsWellFormedInSlot
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        writeSlot.lifetime targets :=
    BorrowTargetsWellFormedInSlot.update_of_not_pathConflicts
      (x := LVal.base lhs)
      (slot := { writeSlot with ty := .ty (.borrow true targets) })
      hnotWriteVar
      htargetsResult
      (by
        intro target htarget
        have hcontainsUpdated :
            (env₃.update (LVal.base lhs)
              { writeSlot with ty := .ty (.borrow true targets) }) ⊢
              LVal.base lhs ↝ Ty.borrow true targets :=
          ⟨{ writeSlot with ty := .ty (.borrow true targets) },
            by simp [Env.update],
            PartialTyContains.here⟩
        exact not_pathConflicts_of_not_writeProhibited_contains
          hnotWriteVar hcontainsUpdated htarget)
  have hslotTargets :
      PartialTyBorrowsWellFormedInSlot
        (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
        writeSlot.lifetime
        ({ writeSlot with ty := .ty (.borrow true targets) }).ty := by
    change PartialTyBorrowsWellFormedInSlot
      (env₃.update (LVal.base lhs) { writeSlot with ty := .ty (.borrow true targets) })
      writeSlot.lifetime
      (.ty (.borrow true targets))
    intro mutable selected hcontains
    cases hcontains
    exact htargetsFinal
  exact ContainedBorrowsWellFormed.update_slot
    hcontainedWriteEnv hslotTargets hnotWriteVar

/--
Appendix Lemma 9.6, dereference/update component.

This is the part that needs the mutual induction over Definition 3.23:
`W-Box` recurses into the path, while `W-MutB` switches to
`writeBorrowTargets` and uses the environment-join borrow invariant.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_deref_appendix96
    (hobligations : UpdateBorrowInvariantObligations)
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ (.deref lhs) oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ (.deref lhs) rhsTy env₃ →
    ¬ WriteProhibited env₃ (.deref lhs) →
    ContainedBorrowsWellFormed env₃ := by
  intro hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  cases hwrite with
  | intro hwriteSlot hupdate =>
      rename_i writeEnv writeSlot updatedTy
      simp [LVal.base] at hwriteSlot
      have hupdateCons :
          UpdateAtPath 0 env₂ (() :: LVal.path lhs) writeSlot.ty rhsTy
            writeEnv updatedTy := by
        simpa [LVal.path_deref_cons] using hupdate
      rcases UpdateAtPath.cons_inv hupdateCons with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, hwriteTy, hupdatedTy, hinnerUpdate⟩
        have hnotWriteBox :
            ¬ WriteProhibited
              (writeEnv.update (LVal.base lhs)
                { writeSlot with ty := .box updatedInner })
              (.deref lhs) := by
          simpa [LVal.base, hupdatedTy] using hnotWrite
        simpa [LVal.base, hupdatedTy] using
          EnvWrite.preserves_containedBorrowsWellFormed_deref_box_appendix96
            hobligations
            (lhs := lhs)
            hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
            hwriteSlot hwriteTy hinnerUpdate rfl hnotWriteBox
      · rcases hborrow with ⟨targets, hwriteTy, hupdatedTy, hwrites⟩
        have hwritesOne :
            WriteBorrowTargets 1 env₂ (LVal.path lhs) targets rhsTy writeEnv := by
          simpa using hwrites
        have hnotWriteBorrow :
            ¬ WriteProhibited
              (writeEnv.update (LVal.base lhs)
                { writeSlot with ty := .ty (.borrow true targets) })
              (.deref lhs) := by
          simpa [LVal.base, hupdatedTy] using hnotWrite
        simpa [LVal.base, hupdatedTy] using
          EnvWrite.preserves_containedBorrowsWellFormed_deref_mutBorrow_appendix96
            hobligations
            (lhs := lhs)
            hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
            hwriteSlot hwriteTy hwritesOne hnotWriteBorrow

/--
Appendix Lemma 9.6, borrow-target component.

The proof is the paper's induction over Definition 3.23:

* `W-Strong`/`W-Weak` reduce to replacing the base slot and checking the
  contained borrows of the updated partial type.
* `W-Box` is the recursive path case.
* `W-MutB` uses the corresponding induction over `writeBorrowTargets`, whose
  cons case is discharged by the environment-join borrow invariant.

The statement is deliberately at the assignment boundary rather than at a
syntactic variable case.  The right-hand side may change the environment from
`env₁` to `env₂`, and a write through `*w` may fan out through mutable-borrow
targets before joining the resulting environments.
-/
theorem EnvWrite.preserves_containedBorrowsWellFormed_appendix96
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ContainedBorrowsWellFormed env₃ := by
  intro hobligations hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
    hwrite hnotWrite
  cases lhs with
  | var x =>
      rcases LValTyping.var_inv hLhs with
        ⟨sourceSlot, hsourceSlot, _hsourceTy, hsourceLifetime⟩
      cases hwrite with
      | intro hwriteSlot hupdate =>
          rename_i writeEnv writeSlot updatedTy
          simp [LVal.base] at hwriteSlot
          rcases (TermTyping.slot_lifetime_survives.1 hRhs)
              (by simpa [hsourceLifetime] using htargetLifetime)
              hsourceSlot with
            ⟨rhsSlot, hrhsSlot, hrhsLifetime⟩
          have hwriteSlotEq : writeSlot = rhsSlot := by
            have hsomeEq : some writeSlot = some rhsSlot := by
              rw [← hwriteSlot, hrhsSlot]
            exact Option.some.inj hsomeEq
          have hwriteLifetime : writeSlot.lifetime = targetLifetime := by
            rw [hwriteSlotEq, ← hrhsLifetime, hsourceLifetime]
          have hLhs₂ : LValTyping env₂ (.var x) writeSlot.ty targetLifetime := by
            rw [← hwriteLifetime]
            exact LValTyping.var hwriteSlot
          exact EnvWrite.preserves_containedBorrowsWellFormed_var
            hwellFormed hLhs₂ hwellRhs
            (EnvWrite.intro hwriteSlot hupdate)
            hnotWrite
    | deref lhs =>
        exact EnvWrite.preserves_containedBorrowsWellFormed_deref_appendix96
          hobligations hwellInitial hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs
          hwrite hnotWrite

theorem EnvWrite.preserves_containedBorrowsWellFormed {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    ContainedBorrowsWellFormed env₃ := by
  exact EnvWrite.preserves_containedBorrowsWellFormed_appendix96

/-- Assignment/update well-formedness using the precise RHS-edge rank premise.

The caller supplies the linearization witness for the pre-write environment,
proves that every newly installed RHS borrow edge points to a lower-ranked base,
and provides the lvalue-coherence transport facts for the write result. -/
theorem EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  have hlin3By :=
    EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all hwrite hlinBy hbelow
  have hlin3 := Linearizable.of_linearizedBy hlin3By
  have hcoh3 := EnvWrite.preserves_coherent_of_obligations
    hwellFormed.2.2.1 hwriteCoh
  exact ⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations hwellInitial hwellFormed hLhs
      htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite,
    EnvWrite.preserves_slotsOutlive hwellFormed.2.1 hwrite, hcoh3, hlin3⟩

/-- Assignment-level write-coherence side condition.

This is the remaining coherence proof boundary for `T-Assign`: after the RHS is
typed, the ranked write is performed, and the RHS borrow edges are known to point
downward, the resulting environment must be coherent.  The old
`EnvWrite.preserves_coherent` shortcut tried to prove this from a per-target RHS
well-formedness premise, which is too weak.  This side condition is stated at the
assignment boundary where the needed typing/shape/rank facts are available.
-/
def AssignmentWritePreservesCoherent : Prop :=
  ∀ {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat},
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    Coherent env₃

/-- Assignment/update well-formedness using explicit rank and coherence premises. -/
theorem EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    AssignmentWritePreservesCoherent →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  have hlin3By :=
    EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all hwrite hlinBy hbelow
  have hlin3 := Linearizable.of_linearizedBy hlin3By
  have hcoh3 := hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact ⟨EnvWrite.preserves_containedBorrowsWellFormed hobligations hwellInitial
      hwellFormed hLhs htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite,
    EnvWrite.preserves_slotsOutlive hwellFormed.2.1 hwrite, hcoh3, hlin3⟩

/-- Assignment preservation variant with the explicit RHS-edge rank premise. -/
theorem assign_preserves_wellFormed_of_rhsBorrowTargetsBelow
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow hobligations
    hwellInitial hwellFormed hlinBy hbelow hwriteCoh hLhs htargetLifetime
    hRhs hshape hwellRhs hwrite hnotWrite

/-- Assignment preservation variant with explicit RHS-edge rank and coherence. -/
theorem assign_preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {φ : Name → Nat} :
    UpdateBorrowInvariantObligations →
    AssignmentWritePreservesCoherent →
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LinearizedBy φ env₂ →
    EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime := by
  intro hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite
  exact EnvWrite.preserves_wellFormed_of_rhsBorrowTargetsBelow_and_coherent
    hobligations hwriteCoherent hwellInitial hwellFormed hlinBy hbelow hLhs
    htargetLifetime hRhs hshape hwellRhs hwrite hnotWrite

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
    {parent child : Lifetime} {lv : LVal} {targetTy : Ty}
    {targetLifetime : Lifetime} :
    LifetimeChild parent child →
    WellFormedEnv env child →
    LValBaseOutlives env lv parent →
    LValTyping env lv (.ty targetTy) targetLifetime →
    targetLifetime ≤ parent →
    LValTyping (env.dropLifetime child) lv (.ty targetTy) targetLifetime := by
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
    ?var ?box ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
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

/-- Backward typing across a lifetime drop: `dropLifetime` only *removes* slots
(leaving the rest unchanged), so any typing in the dropped environment also holds
in the original. -/
theorem LValTyping.of_dropLifetime {env : Env} {child : Lifetime}
    {lv : LVal} {p : PartialTy} {lf : Lifetime}
    (h : LValTyping (env.dropLifetime child) lv p lf) : LValTyping env lv p lf := by
  refine LValTyping.rec
    (motive_1 := fun lv p lf _ => LValTyping env lv p lf)
    (motive_2 := fun targets p lf _ => LValTargetsTyping env targets p lf)
    ?var ?box ?borrow ?singleton ?cons h
  · intro x slot hslot
    rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨henvSlot, _⟩
    exact LValTyping.var henvSlot
  · intro _lv _inner _lifetime _htyping ih
    exact LValTyping.box ih
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
    ?var ?box ?borrow ?singleton ?cons htyping hbaseTargets houtlives
  · intro _x _slot _hslot
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
  | unit =>
      exact WellFormedTy.unit
  | int =>
      exact WellFormedTy.int
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
      (hwellBody.2.1 x slot holdSlot) hslotNeChild
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

/-- `Coherent` is preserved by a lifetime drop: a borrow typed in the dropped
environment also types in the original (`of_dropLifetime`), where `Coherent env`
gives its targets a joint typing, which then transports back across the drop
(`dropLifetime_child_of_wellFormedTargets`).  The targets are well formed at
`parent` because the surviving borrow's base outlives `parent`. -/
theorem Coherent.dropLifetime_child {env : Env} {parent child : Lifetime}
    (hchild : LifetimeChild parent child) (hwellBody : WellFormedEnv env child)
    (hcohEnv : Coherent env) : Coherent (env.dropLifetime child) := by
  intro lv m T bLf hty
  have htyEnv := LValTyping.of_dropLifetime hty
  rcases hcohEnv lv m T bLf htyEnv with ⟨ty, lt, htgtsEnv⟩
  rcases LValTyping.base_slot_exists hty with ⟨dslot, hdslot⟩
  rcases Env.dropLifetime_slotAt_eq_some.mp hdslot with ⟨henvBase, hneChild⟩
  have hbaseParent : LValBaseOutlives env lv parent := by
    rcases LValTyping.base_outlives_one hwellBody htyEnv with ⟨bslot, hbslot, hble⟩
    have hEq : dslot = bslot := Option.some.inj (henvBase.symm.trans hbslot)
    exact ⟨bslot, hbslot,
      LifetimeChild.parent_of_outlives_child_ne hchild hble (hEq ▸ hneChild)⟩
  have hbLfParent : bLf ≤ parent :=
    LValTyping.lifetime_outlives_of_base_outlives_one hwellBody.1 htyEnv hbaseParent
  have hwellT : BorrowTargetsWellFormed env T parent :=
    BorrowTargetsWellFormed.weaken
      (LValTyping.containedBorrowTargetsWellFormed_at_lifetime hwellBody.1 htyEnv
        PartialTyContains.here)
      hbLfParent
  have hltParent : lt ≤ parent :=
    (LValTyping.lifetime_outlives_of_base_outlives hwellBody.1).2 htgtsEnv (by
      intro target htarget
      rcases BorrowTargetsWellFormed.member hwellT target htarget with
        ⟨_, _, _, _, hb⟩
      exact hb)
  exact ⟨ty, lt, LValTargetsTyping.dropLifetime_child_of_wellFormedTargets
    hchild hwellBody hwellT htgtsEnv hltParent⟩

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
      EnvSlotsOutlive.dropLifetime_child hchild hwellBody.2.1,
      Coherent.dropLifetime_child hchild hwellBody hwellBody.2.2.1,
      Linearizable.dropLifetime_child hwellBody.2.2.2⟩,
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

theorem declare_preserves_wellFormed_of_output_fresh {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {x : Name}
    {term : Term} {ty : Ty} :
    WellFormedEnv env₂ lifetime →
    WellFormedTy env₂ ty lifetime →
    env₂.fresh x →
    TermTyping env₁ typing lifetime term ty env₂ →
    FreshUpdateCoherenceObligations env₂ x ty lifetime →
    env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
    WellFormedEnv env₃ lifetime := by
  intro hwellFormed hwellTy hfresh _hterm hcoh henv₃
  exact declare_preserves_wellFormed_output_fresh hwellFormed hwellTy hfresh hcoh henv₃

/--
Constructor landmarks for Lemma 4.9.

The term-typing induction is small once the update-sensitive constructors are
named at their paper granularity.  The final Lemma 4.9 route below uses the
rule-carried obligation induction instead of manufacturing this legacy landmark
package from broad write-preservation claims.
-/
structure TypingPreservesWellFormedObligations : Prop where
  block_preserves_wellFormed
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty} :
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv env₂ blockLifetime →
    TermListTyping env₁ typing blockLifetime terms ty env₂ →
    WellFormedTy env₂ ty lifetime →
    env₃ = env₂.dropLifetime blockLifetime →
    WellFormedEnv env₃ lifetime ∧ WellFormedTy env₃ ty lifetime
  copy_result_wellFormed
    {env : Env} {lv : LVal} {ty : Ty}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    CopyTy ty →
    WellFormedTy env ty lifetime
  move_preserves_wellFormed
    {env env' : Env} {lv : LVal} {ty : Ty}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv (.ty ty) valueLifetime →
    ¬ WriteProhibited env lv →
    EnvMove env lv env' →
    WellFormedEnv env' lifetime ∧ WellFormedTy env' ty lifetime
  assign_preserves_wellFormed
    {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
    WellFormedEnv env₁ lifetime →
    WellFormedEnv env₂ lifetime →
    LValTyping env₁ lhs oldTy targetLifetime →
    targetLifetime ≤ lifetime →
    TermTyping env₁ typing lifetime rhs rhsTy env₂ →
    ShapeCompatible env₂ oldTy (.ty rhsTy) →
    WellFormedTy env₂ rhsTy targetLifetime →
    EnvWrite 0 env₂ lhs rhsTy env₃ →
    ContainedBorrowsWellFormed env₃ →
    ¬ WriteProhibited env₃ lhs →
    WellFormedEnv env₃ lifetime

/--
Lemma 4.9 induction, parameterized by the appendix landmarks.

This is the proof we want to keep clean: each typing constructor is handled
once, while the reusable update/move/copy facts are proved separately.
-/
theorem typingPreservesWellFormed_of_landmarks
    (hlandmarks : TypingPreservesWellFormedObligations)
    {store : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : LwRust.Core.Lifetime}
    {term : LwRust.Core.Term} {ty : LwRust.Core.Ty} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    ValidState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        hlandmarks.copy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      hlandmarks.move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      hlandmarks.block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcoh henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcoh)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs _hLhsPost hshape hwellRhs hwrite _hranked _hwriteCoh
        hcontained hnotWrite ih htypingEq hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨hlandmarks.assign_preserves_wellFormed hwellFormed result.1 hLhs
          (LValTyping.lifetime_outlives_one hwellFormed hLhs)
          hRhs hshape hwellRhs hwrite hcontained hnotWrite,
        WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
      (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
          _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
        let headResult := ihHead htypingEq hwellFormed
        ihRest htypingEq headResult.1)
      htyping rfl hwellFormed

/-- Lemma 4.9 well-formedness induction using rule-carried obligations.

The assignment rank/write-coherence facts and declaration fresh-slot coherence
fact come from the strengthened `T-Assign` and `T-Declare` constructors. -/
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
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs _hvalidState _hvalidStoreTyping hwellFormed _hsafe htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_refs (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed, copyTy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv hnotWrite hmove
        _htypingEq hwellFormed =>
      move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed (LifetimeChild.outlives hblockChild))
      block_preserves_wellFormed
        hblockChild bodyResult.1 hterms hwellTy hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcohObligations henv₃ ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcohObligations)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs _hLhsPost hshape hwellRhs hwrite hranked hwriteCoh hcontained
        hnotWrite ih
        htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        rcases hranked with
          ⟨φ, hlinBy, hbelow⟩
        have hlin3By :=
          EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
            hwrite hlinBy hbelow
        have hcoh3 := EnvWrite.preserves_coherent_of_obligations
          result.1.2.2.1 hwriteCoh
        exact ⟨⟨hcontained,
            EnvWrite.preserves_slotsOutlive result.1.2.1 hwrite,
            hcoh3,
            Linearizable.of_linearizedBy hlin3By⟩,
          WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
      let headResult := ihHead htypingEq hwellFormed
      ihRest htypingEq headResult.1)
    htyping rfl hwellFormed

theorem borrowInvariance_emptyStoreTyping {store : ProgramStore}
    {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term}
    {ty : Ty} :
    ValidState store term →
    ValidStoreTyping store term StoreTyping.empty →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime := by
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
    WellFormedEnv env₂ lifetime := by
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
    WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
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
    WellFormedEnv env₂ lifetime := by
  intro hsource hvalidState hwellFormed hsafe htyping
  exact (typingPreservesWellFormed_of_sourceTerm hsource hvalidState
    hwellFormed hsafe htyping).1

/-- Variable lvalues read no store location while being resolved. -/
theorem RuntimeFrame.locReads_varTarget_false {store : ProgramStore}
    {lv : LVal} {location : Location} :
    LValIsVar lv →
    RuntimeFrame.LocReads store lv location →
    False := by
  intro hvar hreads
  cases lv with
  | var _ =>
      cases hreads
  | deref _ =>
      exact hvar

/--
If a variable occurs in the type computed for a typed lvalue, then writing that
variable is prohibited by a borrow contained in the environment.

This is the static half of the recursive-target frame argument: recursive
runtime target resolution can expose variables that are not the syntactic base
of the outer target, but those variables occur in the type of an intermediate
typed target and are therefore protected by some contained borrow.
-/
theorem writeProhibited_of_lvalTyping_var_in_type {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} {x : Name} :
    WellFormedEnv env current →
    LValTyping env lv partialTy lifetime →
    x ∈ PartialTy.vars partialTy →
    WriteProhibited env (.var x) := by
  intro _hwellFormed htyping
  refine LValTyping.rec
    (motive_1 := fun _lv partialTy _lifetime _ =>
      x ∈ PartialTy.vars partialTy → WriteProhibited env (.var x))
    (motive_2 := fun _targets partialTy _lifetime _ =>
      x ∈ PartialTy.vars partialTy → WriteProhibited env (.var x))
    ?_ ?_ ?_ ?_ ?_ htyping
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

theorem EnvSameShapeStrengthening.writeProhibited_var
    {source result : Env} {x : Name} :
    EnvSameShapeStrengthening source result →
    WriteProhibited source (.var x) →
    WriteProhibited result (.var x) := by
  intro hmap hwrite
  cases hwrite with
  | inl hread =>
      rcases hread with
        ⟨slotName, targets, target, hcontains, htarget, hconflict⟩
      rcases hcontains with ⟨sourceSlot, hsourceSlot, hcontainsTy⟩
      rcases hmap.2 slotName sourceSlot hsourceSlot with
        ⟨resultSlot, hresultSlot, _hlifetime⟩
      rcases hmap.1 slotName resultSlot hresultSlot with
        ⟨sourceSlot0, hsourceSlot0, _hlifetime', hstrength, hshape⟩
      have hsourceSlotEq : sourceSlot0 = sourceSlot := by
        rw [hsourceSlot] at hsourceSlot0
        exact (Option.some.inj hsourceSlot0).symm
      have hxSource0 : x ∈ PartialTy.vars sourceSlot.ty := by
        exact mem_partialTy_vars_iff.mpr
          ⟨true, targets, target, hcontainsTy, htarget,
            by simpa [PathConflicts, LVal.base] using hconflict⟩
      have hxSource : x ∈ PartialTy.vars sourceSlot0.ty := by
        simpa [hsourceSlotEq] using hxSource0
      have hxResult : x ∈ PartialTy.vars resultSlot.ty :=
        partialTy_vars_mono hstrength hshape x hxSource
      exact writeProhibited_of_envSlot_var_in_type hresultSlot rfl hxResult
  | inr himm =>
      rcases himm with
        ⟨slotName, targets, target, hcontains, htarget, hconflict⟩
      rcases hcontains with ⟨sourceSlot, hsourceSlot, hcontainsTy⟩
      rcases hmap.2 slotName sourceSlot hsourceSlot with
        ⟨resultSlot, hresultSlot, _hlifetime⟩
      rcases hmap.1 slotName resultSlot hresultSlot with
        ⟨sourceSlot0, hsourceSlot0, _hlifetime', hstrength, hshape⟩
      have hsourceSlotEq : sourceSlot0 = sourceSlot := by
        rw [hsourceSlot] at hsourceSlot0
        exact (Option.some.inj hsourceSlot0).symm
      have hxSource0 : x ∈ PartialTy.vars sourceSlot.ty := by
        exact mem_partialTy_vars_iff.mpr
          ⟨false, targets, target, hcontainsTy, htarget,
            by simpa [PathConflicts, LVal.base] using hconflict⟩
      have hxSource : x ∈ PartialTy.vars sourceSlot0.ty := by
        simpa [hsourceSlotEq] using hxSource0
      have hxResult : x ∈ PartialTy.vars resultSlot.ty :=
        partialTy_vars_mono hstrength hshape x hxSource
      exact writeProhibited_of_envSlot_var_in_type hresultSlot rfl hxResult

/--
If a typed lvalue resolves to a variable location, then either that variable is
the lvalue's syntactic base or writing the variable is prohibited.

The owned-box case is impossible for non-base variable results because valid
owned references point to heap locations.  The borrow case follows the selected
target from the runtime validity witness and uses
`writeProhibited_of_lvalTyping_var_in_type` when the selected target's base is
the resolved variable.
-/
theorem lval_loc_var_writeProhibited_or_base {store : ProgramStore} {env : Env}
    {current : Lifetime} {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} {x : Name} :
    WellFormedEnv env current →
    store ∼ₛ env →
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
    ?var ?box ?borrow ?singleton ?cons htyping
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
    store ∼ₛ env →
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
    ?var ?box ?borrow ?singleton ?cons htyping
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

theorem ProtectedByBase.pred_of_ownsTransitively {store : ProgramStore} {x : Name}
    {storage owned : Location} :
    ValidStore store →
    StoreOwnerTargetsHeap store →
    ProtectedByBase store x owned →
    ProgramStore.OwnsTransitively store storage owned →
    ProtectedByBase store x storage := by
  intro hvalid hheap hprotected hpath
  induction hpath generalizing x with
  | direct howns =>
      exact ProtectedByBase.pred_of_ownsAt hvalid hheap hprotected howns
  | trans hownsMiddle htail ih =>
      exact ProtectedByBase.pred_of_ownsAt hvalid hheap (ih hprotected)
        hownsMiddle

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

theorem dropsAvoids_of_not_protectedByBase
    {origin current final : ProgramStore} {values : List PartialValue}
    {x : Name} {location : Location} :
    Drops current values final →
    ValidStore origin →
    StoreOwnerTargetsHeap origin →
    (∀ storage slot,
      current.slotAt storage = some slot →
      storage ≠ VariableProjection x →
      origin.slotAt storage = some slot) →
    (∀ value, value ∈ values → PartialValueOwnerTargetsHeap value) →
    (∀ value, value ∈ values →
      ∀ owned, owned ∈ partialValueOwningLocations value →
        ProtectedByBase origin x owned) →
    ¬ ProtectedByBase origin x location →
    DropsAvoids current values location := by
  intro hdrops hvalidOrigin hheapOrigin hcurrentOrigin hvaluesHeap
    hvaluesProtected hnotProtected
  induction hdrops with
  | nil =>
      exact DropsAvoids.nil
  | nonOwner hnonOwner _hdrops ih =>
      exact DropsAvoids.nonOwner hnonOwner
        (ih (by
            intro storage slot hslot hne
            exact hcurrentOrigin storage slot hslot hne)
          (by
            intro value hmem
            exact hvaluesHeap value (by simp [hmem]))
          (by
            intro value hmem owned howned
            exact hvaluesProtected value (by simp [hmem]) owned howned))
  | ownerMissing howner hmissing _hdrops ih =>
      exact DropsAvoids.ownerMissing howner hmissing
        (ih (by
            intro storage slot hslot hne
            exact hcurrentOrigin storage slot hslot hne)
          (by
            intro value hmem
            exact hvaluesHeap value (by simp [hmem]))
          (by
            intro value hmem owned howned
            exact hvaluesProtected value (by simp [hmem]) owned howned))
  | ownerPresent howner hpresent _hdrops ih =>
      rename_i storeBefore _storeAfter ref slot rest
      have hrefProtected :
          ProtectedByBase origin x ref.location :=
        hvaluesProtected (.value (.ref ref)) (by simp) ref.location
          (mem_partialValueOwningLocations_ref_true howner)
      have hrefNeLocation : ref.location ≠ location := by
        intro hrefEq
        exact hnotProtected (by simpa [hrefEq] using hrefProtected)
      have hrefNeVar : ref.location ≠ VariableProjection x := by
        intro hrefEq
        have hheadHeap : PartialValueOwnerTargetsHeap (.value (.ref ref)) :=
          hvaluesHeap (.value (.ref ref)) (by simp)
        rcases hheadHeap ref.location
            (mem_partialValueOwningLocations_ref_true howner) with
          ⟨address, hheapLocation⟩
        rw [hrefEq] at hheapLocation
        cases hheapLocation
      have horiginSlot : origin.slotAt ref.location = some slot :=
        hcurrentOrigin ref.location slot hpresent hrefNeVar
      have hslotHeap : PartialValueOwnerTargetsHeap slot.value :=
        partialValueOwnerTargetsHeap_of_slot hheapOrigin horiginSlot
      exact DropsAvoids.ownerPresent howner hpresent hrefNeLocation
        (ih (by
            intro storage erasedSlot hslot hne
            have hslotBefore :
                storeBefore.slotAt storage = some erasedSlot :=
              RuntimeFrame.slotAt_of_erase_slotAt hslot
            exact hcurrentOrigin storage erasedSlot hslotBefore hne)
          (by
            intro value hmem
            simp at hmem
            rcases hmem with hslotValue | hrest
            · subst hslotValue
              exact hslotHeap
            · exact hvaluesHeap value (by simp [hrest]))
          (by
            intro value hmem owned howned
            simp at hmem
            rcases hmem with hslotValue | hrest
            · subst hslotValue
              have hownsOrigin : ProgramStore.OwnsAt origin owned ref.location :=
                ⟨slot.lifetime, by
                  have hslotValueEq :
                      slot.value = .value (owningRef owned) :=
                    eq_owningRef_of_mem_partialValueOwningLocations howned
                  cases slot with
                  | mk slotValue slotLifetime =>
                      cases hslotValueEq
                      simpa [owningRef] using horiginSlot⟩
              exact ProtectedByBase.trans_owned hrefProtected hownsOrigin
            · exact hvaluesProtected value (by simp [hrest]) owned howned)
          )

/--
Dual frame lemma for drops: if every owning root in the drop list is outside the
ownership tree protected by `x`, then the drop avoids every location inside that
tree.
-/
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
    store ∼ₛ env →
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
    ?_ ?_ ?_ ?_ ?_ htyping
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

/--
Every location inspected while resolving a typed lvalue is protected by some
variable base.  For borrowed dereferences the protecting base can come from the
selected borrow target, not from the syntactic base of the dereference.
-/
theorem lval_loc_or_reads_protectedBySomeBase
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
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
    ?_ ?_ ?_ ?_ ?_ htyping
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
    store ∼ₛ env →
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
    ?var ?box ?borrow ?singleton ?cons htyping hbase houtlives
  · intro x slot hslot _hbase hslotParent
    constructor
    · intro location hloc
      have hlocation : location = VariableProjection x :=
        (Option.some.inj hloc).symm
      subst hlocation
      exact dropsAvoids_var_of_base_outlives_lifetimeDrop
        hsafe hheap hdropSet hdrops hchild hslot hslotParent
    · intro location hreads
      cases hreads
  · intro source inner sourceLifetime hsource ihSource hbaseSource
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
  · intro source mutable targets borrowLifetime targetLifetime targetTy
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
  · intro onlyTarget ty targetLifetime htarget ihTarget hbaseTargets
      htargetLifetimeParent queried hmem
    have hqueriedEq : queried = onlyTarget := by
      simpa using hmem
    subst queried
    exact ihTarget (hbaseTargets onlyTarget (by simp)) htargetLifetimeParent
  · intro headTarget rest headTy headLifetime restLifetime targetLifetime restTy
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
    store ∼ₛ env →
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
    store ∼ₛ env →
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

/-- General dependency-drop frame lemma: once every dropped owner is outside all
protected bases, every borrow-resolution dependency is avoided by the drop. -/
theorem dropsAvoids_of_borrowDependency_unprotected_values
    {store store' : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {values : List PartialValue} {value : PartialValue} {partialTy : PartialTy}
    {dependency : Location} :
    Drops store values store' →
    WellFormedEnv env current →
    store ∼ₛ env →
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

/--
If every variable occurring in a partial type is protected from writes, then a
borrow-resolution dependency inside a value of that partial type is also
protected when the dependency is a variable location.
-/
theorem borrowDependency_var_writeProhibited_of_varsProtected
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location} :
    WellFormedEnv env current →
    store ∼ₛ env →
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

theorem borrowDependency_protected_writeProhibited_or_mem_vars
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {x : Name} :
    WellFormedEnv env current →
    store ∼ₛ env →
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

/--
Authority-aware form of `borrowDependency_protected_writeProhibited_or_mem_vars`.

When the protected base is the base of a known mutable-borrow target, the
`WriteProhibited (.var x)` branch is not just an opaque fact: borrow safety
forces every witness for that prohibition to live in the mutable-borrow
authority root.  The other branch is the genuine "the dependent value mentions
the selected base" case.
-/
theorem borrowDependency_protected_authority_or_mem_vars
    {store : ProgramStore} {env : Env} {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {authority x : Name} {targetsMutable : List LVal}
    {targetMutable : LVal} :
    WellFormedEnv env current →
    BorrowSafeEnv env →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    env ⊢ authority ↝ (&mut targetsMutable) →
    targetMutable ∈ targetsMutable →
    LVal.base targetMutable = x →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ProtectedByBase store x dependency →
      (∃ mutable targetsOther targetOther,
        env ⊢ authority ↝ (Ty.borrow mutable targetsOther) ∧
          targetOther ∈ targetsOther ∧ targetOther ⋈ (.var x)) ∨
        x ∈ PartialTy.vars partialTy := by
  intro hwellFormed hborrowSafe hsafe hvalidStore hheap hborrows hmut
    htargetMutable htargetBase hdependency hprotected
  rcases borrowDependency_protected_writeProhibited_or_mem_vars
      hwellFormed hsafe hvalidStore hheap hborrows hdependency hprotected with
    hwrite | hmem
  · left
    have hwriteTarget :
        WriteProhibited env (.var (LVal.base targetMutable)) := by
      simpa [htargetBase] using hwrite
    rcases BorrowSafeEnv.writeProhibited_var_of_mut_target_authority
        hborrowSafe hmut htargetMutable hwriteTarget with
      ⟨mutable, targetsOther, targetOther, hauthority, htargetOther,
        hconflict⟩
    exact ⟨mutable, targetsOther, targetOther, hauthority, htargetOther,
      by simpa [htargetBase] using hconflict⟩
  · exact Or.inr hmem

theorem borrowDependency_not_protectedByBase_of_varsProtectedIn
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {current slotLifetime : Lifetime}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {x : Name} :
    WellFormedEnv sourceEnv current →
    store ∼ₛ sourceEnv →
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
    store ∼ₛ env →
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
    store ∼ₛ env →
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

/-- Updating the moved leaf cannot invalidate the value just read from that leaf:
owner reachability would create an ownership cycle, and borrow dependencies are
ruled out by the `T-Move` no-write premise. -/
theorem movedValue_reaches_ne_protected_leaf {store : ProgramStore}
    {env : Env} {current valueLifetime leafLifetime : Lifetime}
    {lv : LVal} {leaf reached : Location} {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
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

/--
A finite value-abstraction derivation cannot validate a slot whose value is an
owning reference back to the slot's own location.  This is not an additional
runtime invariant: it is a structural consequence of `ValidPartialValue`.
-/
theorem ValidPartialValue.no_self_owning_ref {store : ProgramStore}
    {location : Location} {lifetime : Lifetime} {ty : PartialTy} :
    store.slotAt location =
      some { value := .value (owningRef location), lifetime := lifetime } →
    ¬ ValidPartialValue store (.value (owningRef location)) ty := by
  intro hslot hvalid
  have hno :
      ∀ {value ty},
        ValidPartialValue store value ty →
        ∀ {location lifetime},
          store.slotAt location =
            some { value := .value (owningRef location), lifetime := lifetime } →
          value = .value (owningRef location) →
          False := by
    intro value ty hvalid
    induction hvalid with
    | unit =>
        intro location lifetime _hslot hvalue
        simp [owningRef] at hvalue
    | int =>
        intro location lifetime _hslot hvalue
        simp [owningRef] at hvalue
    | undef =>
        intro location lifetime _hslot hvalue
        simp at hvalue
    | @borrow borrowedLocation mutable targets target hmem hloc =>
        intro location lifetime _hslot hvalue
        simp [owningRef] at hvalue
    | @box ownerLocation slot inner hownedSlot _hinner ih =>
        intro location lifetime hslot hvalue
        have hownerEq : ownerLocation = location := by
          simpa [owningRef] using hvalue
        subst location
        have hslotEq :
            slot =
              { value := .value (owningRef ownerLocation),
                lifetime := lifetime } :=
          Option.some.inj (hownedSlot.symm.trans hslot)
        subst hslotEq
        exact ih hslot rfl
    | @boxFull ownerLocation slot innerTy hownedSlot _hinner ih =>
        intro location lifetime hslot hvalue
        have hownerEq : ownerLocation = location := by
          simpa [owningRef] using hvalue
        subst location
        have hslotEq :
            slot =
              { value := .value (owningRef ownerLocation),
                lifetime := lifetime } :=
          Option.some.inj (hownedSlot.symm.trans hslot)
        subst hslotEq
        exact ih hslot rfl
  exact hno hvalid hslot rfl

/-- Any direct owner carried by a valid partial value is in its reachability set. -/
theorem RuntimeFrame.reaches_of_mem_partialValueOwningLocations
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy}
    {owned : Location} :
    ValidPartialValue store value ty →
    owned ∈ partialValueOwningLocations value →
    RuntimeFrame.Reaches store value ty owned := by
  intro hvalid hmem
  cases hvalid with
  | unit =>
      simp [partialValueOwningLocations, valueOwningLocations,
        valueOwnedLocation?] at hmem
  | int =>
      simp [partialValueOwningLocations, valueOwningLocations,
        valueOwnedLocation?] at hmem
  | undef =>
      simp [partialValueOwningLocations] at hmem
  | borrow htargetMem hloc =>
      simp [partialValueOwningLocations, valueOwningLocations,
        valueOwnedLocation?] at hmem
  | @box location slot inner hslot _hinner =>
      have hownedEq : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations,
          valueOwnedLocation?] using hmem
      subst hownedEq
      exact RuntimeFrame.Reaches.boxHere hslot
  | @boxFull location slot innerTy hslot _hinner =>
      have hownedEq : owned = location := by
        simpa [partialValueOwningLocations, valueOwningLocations,
          valueOwnedLocation?] using hmem
      subst hownedEq
      exact RuntimeFrame.Reaches.boxFullHere hslot

/--
Reachability with the reached slot's static partial type.  This is a proof-side
refinement of `RuntimeFrame.Reaches`: following an owning reference descends
into the type of the pointed-to slot.
-/
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

theorem RuntimeFrame.ReachesSlot.ty_size_lt {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {location : Location}
    {slot : StoreSlot} {slotTy : PartialTy} :
    RuntimeFrame.ReachesSlot store value ty location slot slotTy →
    sizeOf slotTy < sizeOf ty := by
  intro hreach
  induction hreach with
  | boxHere =>
      simp
  | boxInner _hslot _hinner ih =>
      exact lt_trans ih (by simp)
  | boxFullHere =>
      simp
  | boxFullInner _hslot _hinner ih =>
      exact lt_trans ih (by simp)

theorem RuntimeFrame.reachesSlot_of_ownerReaches {store : ProgramStore}
    {env : Env} {slotLifetime : Lifetime}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    PartialTyBorrowsWellFormedInSlot env slotLifetime ty →
    ValidPartialValue store value ty →
    RuntimeFrame.OwnerReaches store value ty location →
    ∃ slot slotTy,
      RuntimeFrame.ReachesSlot store value ty location slot slotTy := by
  intro hborrows hvalid hreach
  induction hvalid generalizing env slotLifetime location with
  | unit =>
      cases hreach
  | int =>
      cases hreach
  | undef =>
      cases hreach
  | @borrow borrowedLocation mutable targets target hmem hloc =>
      cases hreach
  | @box ownerLocation slot inner hslot hinner ih =>
      cases hreach with
      | @boxHere _ reachedSlot _ hreachSlot =>
          have hslotEq : slot = reachedSlot := by
            rw [hslot] at hreachSlot
            exact Option.some.inj hreachSlot
          subst hslotEq
          exact ⟨slot, inner, RuntimeFrame.ReachesSlot.boxHere hslot hinner⟩
      | @boxInner _ reachedSlot _ _ hreachSlot hinnerReach =>
          have hslotEq : reachedSlot = slot := by
            rw [hslot] at hreachSlot
            exact Option.some.inj hreachSlot.symm
          subst hslotEq
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.box hcontains)
          rcases ih hinnerBorrows hinnerReach with
            ⟨innerSlot, innerTy, hinnerSlot⟩
          exact ⟨innerSlot, innerTy,
            RuntimeFrame.ReachesSlot.boxInner hslot hinnerSlot⟩
  | @boxFull ownerLocation slot innerTy hslot hinner ih =>
      cases hreach with
      | @boxFullHere _ reachedSlot _ hreachSlot =>
          have hslotEq : slot = reachedSlot := by
            rw [hslot] at hreachSlot
            exact Option.some.inj hreachSlot
          subst hslotEq
          exact ⟨slot, .ty innerTy,
            RuntimeFrame.ReachesSlot.boxFullHere hslot hinner⟩
      | @boxFullInner _ reachedSlot _ _ hreachSlot hinnerReach =>
          have hslotEq : reachedSlot = slot := by
            rw [hslot] at hreachSlot
            exact Option.some.inj hreachSlot.symm
          subst hslotEq
          have hinnerBorrows :
              PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty innerTy) := by
            intro mutable targets hcontains
            exact hborrows (PartialTyContains.tyBox hcontains)
          rcases ih hinnerBorrows hinnerReach with
            ⟨innerSlot, innerTy, hinnerSlot⟩
          exact ⟨innerSlot, innerTy,
            RuntimeFrame.ReachesSlot.boxFullInner hslot hinnerSlot⟩

/-- Owner reachability through heap-only owner targets never reaches a variable slot. -/
theorem RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
    {store : ProgramStore} {env : Env} {slotLifetime : Lifetime}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.OwnerReaches store partialValue partialTy location →
    location ≠ VariableProjection x := by
  intro hstoreHeap hvalueHeap hborrows hreach
  induction hreach with
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
        (PartialTyBorrowsWellFormedInSlot.box_inv hborrows)
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
        (by
          intro mutable targets hcontains
          exact hborrows (PartialTyContains.tyBox hcontains))

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

theorem RuntimeFrame.ownerReaches_not_protectedByBase_of_term_value
    {store : ProgramStore} {value : Value} {ty : Ty}
    {location : Location} {x : Name} :
    ValidRuntimeState store (.val value) →
    ValidValue store value ty →
    RuntimeFrame.OwnerReaches store (.value value) (.ty ty) location →
    ¬ ProtectedByBase store x location := by
  intro hvalidRuntime _hvalidValue hreach hprotected
  cases hreach with
  | boxFullHere hslot =>
      rcases hprotected with hroot | hpath
      · have hheap :
            ∃ address, location = .heap address :=
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)
            location (by
              simp [termOwningLocations, termValues,
                valueOwningLocations, valueOwnedLocation?])
        subst hroot
        rcases hheap with ⟨address, hlocation⟩
        cases hlocation
      · exact
          (ValidRuntimeState.storeTermDisjoint hvalidRuntime location
            (by
              simp [termOwningLocations, termValues,
                valueOwningLocations, valueOwnedLocation?]))
          (ProgramStore.OwnsTransitively.to_owns hpath)
  | boxFullInner hslot hinnerReach =>
      rename_i ownerLocation ownerSlot innerTy
      have hownerPath :=
        RuntimeFrame.ownsTransitively_of_ownerReaches_stored hslot hinnerReach
      have hownerProtected :
          ProtectedByBase store x ownerLocation :=
        ProtectedByBase.pred_of_ownsTransitively
          (ValidRuntimeState.validStore hvalidRuntime)
          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
          hprotected hownerPath
      rcases hownerProtected with hroot | hpath
      · have hheap :
            ∃ address, ownerLocation = .heap address :=
          (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime)
            ownerLocation (by
              simp [termOwningLocations, termValues,
                valueOwningLocations, valueOwnedLocation?])
        subst hroot
        rcases hheap with ⟨address, hlocation⟩
        cases hlocation
      · exact
          (ValidRuntimeState.storeTermDisjoint hvalidRuntime ownerLocation
            (by
              simp [termOwningLocations, termValues,
                valueOwningLocations, valueOwnedLocation?]))
          (ProgramStore.OwnsTransitively.to_owns hpath)

/--
Full reachability cannot hit a variable protected by a no-write premise, provided
all variables syntactically occurring in the partial type are write-protected.
Owner reaches are ruled out by heap-only owner targets; borrow dependencies are
ruled out by `borrowDependency_var_writeProhibited_of_varsProtected`.
-/
theorem RuntimeFrame.reaches_ne_var_of_varsProtected {store : ProgramStore}
    {env : Env} {current slotLifetime : Lifetime}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    WellFormedEnv env current →
    store ∼ₛ env →
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
    store ∼ₛ sourceEnv →
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    PartialTyBorrowsWellFormedInSlot sourceEnv slotLifetime partialTy →
    (∀ y, y ∈ PartialTy.vars partialTy →
      WriteProhibited observerEnv (.var y)) →
    ¬ WriteProhibited sourceEnv (.var x) →
    ¬ WriteProhibited observerEnv (.var x) →
    RuntimeFrame.Reaches store partialValue partialTy location →
    location ≠ VariableProjection x := by
  intro hwellFormed hsafe hheap hvalueHeap hborrows hvarsObserver
    hnotWriteSource hnotWriteObserver hreach hlocEq
  rcases RuntimeFrame.Reaches.owner_or_borrow hreach with howner | hdependency
  · exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows (x := x) hheap
      hvalueHeap hborrows howner hlocEq
  · rcases borrowDependency_var_writeProhibited_or_mem_vars
        (dependency := location)
        hwellFormed hsafe hheap hborrows hdependency x hlocEq with
      hwpSource | hmemVars
    · exact hnotWriteSource hwpSource
    · exact hnotWriteObserver (hvarsObserver x hmemVars)

/-- Full-value specialization of `RuntimeFrame.reaches_ne_var_of_varsProtected`. -/
theorem RuntimeFrame.value_reaches_ne_var_of_varsProtected
    {store : ProgramStore} {env : Env} {current lifetime : Lifetime}
    {value : Value} {ty : Ty} {location : Location} {x : Name} :
    WellFormedEnv env current →
    store ∼ₛ env →
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
        (StoreOwnerSpine.storage_slot _htail)
        ih
      simpa [howner] using hbox

theorem leaf_slot {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    store.slotAt leaf = some leafSlot := by
  intro hspine
  induction hspine with
  | nil hslot _hvalid =>
      exact hslot
  | box _hslot _howner _htail ih =>
      exact ih

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

theorem of_lvalTyping_box {store : ProgramStore} {env : Env}
    {current : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
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
                    (store.update leaf
                      { leafSlot with value := .value value })
                    ownedSlot.value updatedInner := by
                exact ih (by simp) hinnerUpdate hnewLeafValid
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf
                    { leafSlot with value := .value value }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpine.storage_slot htailSpine)
              have hbox :
                  ValidPartialValue
                  (store.update leaf
                    { leafSlot with value := .value value })
                  (.value (owningRef owned)) (.box updatedInner) := by
                exact ValidPartialValue.box hownedSlotWrite htailValid
              simpa [howner] using hbox

theorem valid_after_updateAtPath_nonempty_full_aux
    {store : ProgramStore} {env writeEnv : Env}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {oldLeafTy rhsTy : Ty}
    {path : Path} {rank : Nat} {value : Value} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    leafTy = .ty oldLeafTy →
    path ≠ [] →
    UpdateAtPath rank env path rootTy rhsTy writeEnv updatedTy →
    ValidPartialValue
      (store.update leaf { leafSlot with value := .value value })
      (.value value) (.ty rhsTy) →
    ValidPartialValue
      (store.update leaf { leafSlot with value := .value value })
      rootSlot.value updatedTy := by
  intro hspine hleafTy hnonempty hupdate hnewLeafValid
  induction hspine generalizing env writeEnv updatedTy rhsTy value oldLeafTy with
  | nil =>
      exact False.elim (hnonempty rfl)
  | @box storage owned leaf slot ownedSlot leafSlot spineInner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | @box _env₁ _env₂ _rank _path _inner updatedInner _ty hinnerUpdate =>
          cases htail with
          | nil hownedSlot _holdValid =>
              have hinnerEq : spineInner = .ty oldLeafTy := hleafTy
              subst spineInner
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
              | weak hshape hjoin =>
                  have hjoinedShapeOld :
                      PartialTy.sameShape (.ty oldLeafTy) updatedInner :=
                    partialTyJoin_sameShape hshape hjoin
                  have holdShapeRhs :
                      PartialTy.sameShape (.ty oldLeafTy) (.ty rhsTy) :=
                    PartialTy.sameShape_of_shapeCompatible hshape
                  have hrhsShapeJoined :
                      PartialTy.sameShape (.ty rhsTy) updatedInner :=
                    PartialTy.sameShape_trans
                      (PartialTy.sameShape_symm holdShapeRhs) hjoinedShapeOld
                  have hnewJoined :
                      ValidPartialValue
                        (store.update owned { ownedSlot with value := .value value })
                        (.value value) updatedInner :=
                    validPartialValue_strengthen_sameShape hnewLeafValid
                      (PartialTyUnion.right_strengthens hjoin) hrhsShapeJoined
                  have hownedSlotWrite :
                      (store.update owned { ownedSlot with value := .value value }).slotAt
                        owned =
                        some { value := .value value, lifetime := ownedSlot.lifetime } := by
                    simp [ProgramStore.update]
                  have hbox :
                      ValidPartialValue
                        (store.update owned { ownedSlot with value := .value value })
                        (.value (owningRef owned)) (.box updatedInner) :=
                    ValidPartialValue.box hownedSlotWrite hnewJoined
                  simpa [howner] using hbox
          | box htailSlot htailOwner htailTail =>
              have htailSpine :=
                StoreOwnerSpine.box htailSlot htailOwner htailTail
              have htailValid :
                  ValidPartialValue
                    (store.update leaf
                      { leafSlot with value := .value value })
                    ownedSlot.value updatedInner := by
                exact ih hleafTy (by simp) hinnerUpdate hnewLeafValid
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpine.leaf_ne_storage_of_cons htailSpine
              have hownedSlotWrite :
                  (store.update leaf
                    { leafSlot with value := .value value }).slotAt owned =
                    some ownedSlot := by
                have hownedNeLeaf : owned ≠ leaf := by
                  intro h
                  exact hleafNeOwned h.symm
                simpa [ProgramStore.update, hownedNeLeaf] using
                  (StoreOwnerSpine.storage_slot htailSpine)
              have hbox :
                  ValidPartialValue
                    (store.update leaf
                      { leafSlot with value := .value value })
                    (.value (owningRef owned)) (.box updatedInner) := by
                exact ValidPartialValue.box hownedSlotWrite htailValid
              simpa [howner] using hbox

theorem valid_after_updateAtPath_nonempty_full
    {store : ProgramStore} {env writeEnv : Env}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy updatedTy : PartialTy} {oldLeafTy rhsTy : Ty}
    {path : Path} {rank : Nat} {value : Value} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot
      (.ty oldLeafTy) →
    path ≠ [] →
    UpdateAtPath rank env path rootTy rhsTy writeEnv updatedTy →
    ValidPartialValue
      (store.update leaf { leafSlot with value := .value value })
      (.value value) (.ty rhsTy) →
    ValidPartialValue
      (store.update leaf { leafSlot with value := .value value })
      rootSlot.value updatedTy := by
  intro hspine
  exact valid_after_updateAtPath_nonempty_full_aux hspine rfl

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
      | ty struckTy =>
          simp [Strike] at hstrike
      | undef struckTy =>
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
      | strong => rfl
      | weak _hshape _hjoin => rfl
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot howner
      htail ih =>
      cases hupdate with
      | box hinner =>
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

theorem updateAtPath_rhs_vars_subset_updated_full_aux
    {store : ProgramStore} {env writeEnv : Env}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy leafTy updatedTy : PartialTy} {oldLeafTy rhsTy : Ty}
    {path : Path} {rank : Nat} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot leafTy →
    leafTy = .ty oldLeafTy →
    UpdateAtPath rank env path rootTy rhsTy writeEnv updatedTy →
    ∀ v, v ∈ PartialTy.vars (.ty rhsTy) → v ∈ PartialTy.vars updatedTy := by
  intro hspine hleafTy hupdate
  induction hspine generalizing env writeEnv updatedTy rhsTy rank oldLeafTy with
  | nil _hslot _hvalid =>
      subst hleafTy
      cases hupdate with
      | strong =>
          intro v hv
          simpa using hv
      | weak hshape hjoin =>
          intro v hv
          have hjoinedShapeOld :
              PartialTy.sameShape (.ty oldLeafTy) updatedTy :=
            partialTyJoin_sameShape hshape hjoin
          have holdShapeRhs :
              PartialTy.sameShape (.ty oldLeafTy) (.ty rhsTy) :=
            PartialTy.sameShape_of_shapeCompatible hshape
          have hrhsShapeJoined :
              PartialTy.sameShape (.ty rhsTy) updatedTy :=
            PartialTy.sameShape_trans
              (PartialTy.sameShape_symm holdShapeRhs) hjoinedShapeOld
          exact partialTy_vars_mono
            (PartialTyUnion.right_strengthens hjoin) hrhsShapeJoined v hv
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      cases hupdate with
      | box hinner =>
          intro v hv
          exact ih hleafTy hinner v hv

theorem updateAtPath_rhs_vars_subset_updated_full
    {store : ProgramStore} {env writeEnv : Env}
    {root leaf : Location} {rootSlot leafSlot : StoreSlot}
    {rootTy updatedTy : PartialTy} {oldLeafTy rhsTy : Ty}
    {path : Path} {rank : Nat} :
    StoreOwnerSpine store root rootSlot rootTy path leaf leafSlot
      (.ty oldLeafTy) →
    UpdateAtPath rank env path rootTy rhsTy writeEnv updatedTy →
    ∀ v, v ∈ PartialTy.vars (.ty rhsTy) → v ∈ PartialTy.vars updatedTy := by
  intro hspine
  exact updateAtPath_rhs_vars_subset_updated_full_aux hspine rfl

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

end StoreOwnerSpine

/-- Direct variable `move` multistep preservation with the frame facts derived
from well-formedness rather than supplied as an obligation. -/
theorem preservation_move_var_multistep_runtime_of_wellFormed
    {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {x : Name} {finalValue : Value} {ty : Ty} :
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    ValidRuntimeState store (.move (.var x)) →
    env₁.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } →
    EnvMove env₁ (.var x) env₂ →
    TermTyping env₁ typing lifetime (.move (.var x)) ty env₂ →
    MultiStep store lifetime (.move (.var x)) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hwellFormed hsafe hvalidRuntime henvSlot hmove htyping hmulti
  cases htyping with
  | move hLv _hnotWrite _hmoveTyping =>
      exact preservation_runtime_multistep_of_step_to_value
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
                hwellFormed hsafe hvalidRuntime henvSlot hmove
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
    store ∼ₛ env₁ →
    ValidRuntimeState store (.move source.deref) →
    LValTyping env₁ source (.box (.ty ty)) valueLifetime →
    ¬ WriteProhibited env₁ source.deref →
    EnvMove env₁ source.deref env₂ →
    TermTyping env₁ typing lifetime (.move source.deref) ty env₂ →
    MultiStep store lifetime (.move source.deref) finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hwellFormed hsafe hvalidRuntime hsourceBox hnotWrite hmove htyping hmulti
  exact preservation_runtime_multistep_of_step_to_value
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
                      { ownerSlot with value := PartialValue.undef } ∼ₛ
                    env₂ := by
                subst henv₂
                refine safeAbstraction_update_var_partial_of_preserved
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
              exact ⟨validRuntimeState_move_step hvalidRuntime
                  (Step.move (lifetime := lifetime) hread hwrite),
                hsafeFinal, hvalidValueFinal⟩)
    hmulti

/-- Direct variable `assign` redex preservation with the frame facts derived from
well-formedness rather than supplied as an obligation. -/
theorem preservation_assign_var_step_runtime_of_wellFormed
    {store store' : ProgramStore} {env env' : Env}
    {lifetime targetLifetime rhsWellLifetime : Lifetime} {x : Name}
    {oldTy : PartialTy} {value finalValue : Value} {rhsTy : Ty} :
    WellFormedEnv env lifetime →
    store ∼ₛ env →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    LValTyping env (.var x) oldTy targetLifetime →
    ShapeCompatible env oldTy (.ty rhsTy) →
    WellFormedTy env rhsTy rhsWellLifetime →
    EnvWrite 0 env (.var x) rhsTy env' →
    ¬ WriteProhibited env' (.var x) →
    WellFormedEnv env' lifetime →
    ValidValue store value rhsTy →
    Step store lifetime (.assign (.var x) (.val value)) store' (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwellFormed hsafe hvalidRuntime hLhs hshape hwellTy hwrite hnotWrite
    hwellOut hvalidValue hstep
  rcases LValTyping.var_inv hLhs with ⟨envSlot, henvSlot, htyEq, _hlifetimeEq⟩
  cases hstep with
  | assign hread hwriteStoreWritten hdrops =>
      have henv'Eq : env' = env.update x { envSlot with ty := .ty rhsTy } :=
        envWrite_zero_var_eq henvSlot hwrite
      have hnotWriteSource : ¬ WriteProhibited env (.var x) := by
        exact not_writeProhibited_var_of_update_self hwellFormed.2.2.2 (by
          rw [henv'Eq] at hnotWrite
          exact hnotWrite)
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
          hnotWriteSource hnotWrite hreach
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
          hnotWriteSource hnotWrite hreach
      cases hshape with
      | unit =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
              (by left; exact htyEq)
              hvalidValue hread hwriteStoreWritten hdrops
              hvalueNoReach hotherNoReach
      | int =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
              (by right; left; exact htyEq)
              hvalidValue hread hwriteStoreWritten hdrops
              hvalueNoReach hotherNoReach
      | borrow hleft hright hinner =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
              (by right; right; right; exact ⟨_, _, htyEq⟩)
              hvalidValue hread hwriteStoreWritten hdrops
              hvalueNoReach hotherNoReach
      | undefLeft hinner =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
              (by right; right; left; exact ⟨_, htyEq⟩)
              hvalidValue hread hwriteStoreWritten hdrops
              hvalueNoReach hotherNoReach
      | tyBox hinnerShape =>
          rename_i postWriteStore oldStoreSlot leftInner rightInner
          cases hvalidValue with
          | @boxFull location slot _ hnewRootSlot hnewInnerValid =>
              have hstoreX : store.slotAt (VariableProjection x) = some oldStoreSlot := by
                simpa [ProgramStore.read, ProgramStore.loc, VariableProjection] using hread
              have hslotLifetime : oldStoreSlot.lifetime = envSlot.lifetime := by
                rcases hsafe.2 x envSlot henvSlot with
                  ⟨safeValue, hsafeSlot, _hvalidSafe⟩
                rw [hstoreX] at hsafeSlot
                injection hsafeSlot with hslotEq
                exact congrArg StoreSlot.lifetime hslotEq
              set writtenStore : ProgramStore :=
                store.update (VariableProjection x)
                  { oldStoreSlot with
                    value := .value
                      (.ref { location := location, owner := true }) } with hwrittenStore
              have hstoreAfterWrite : postWriteStore = writtenStore := by
                rw [hwrittenStore]
                exact write_var_eq hstoreX hwriteStoreWritten
              rw [hstoreAfterWrite] at hdrops
              have hwriteStoreConcrete :
                  store.write (.var x)
                    (.value (.ref { location := location, owner := true })) =
                      some writtenStore := by
                rw [← hstoreAfterWrite]
                exact hwriteStoreWritten
              have henv' :
                  env' = env.update x { envSlot with ty := .ty (.box rightInner) } :=
                envWrite_zero_var_eq henvSlot hwrite
              have hnewValueHeap :
                  ValueOwnerTargetsHeap
                    (.ref { location := location, owner := true }) :=
                TermOwnerTargetsHeap.value
                  (termOwnerTargetsHeap_assign_inner
                    (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
              have hnewRootHeap : ∃ address, location = .heap address :=
                hnewValueHeap location (by
                  simp [valueOwningLocations, valueOwnedLocation?])
              have hnewRootNeVar : location ≠ VariableProjection x := by
                intro hlocation
                rcases hnewRootHeap with ⟨address, hheap⟩
                rw [hlocation] at hheap
                cases hheap
              have hnewRootSlotWrite :
                  writtenStore.slotAt location = some slot := by
                rw [hwrittenStore]
                simpa [ProgramStore.update, hnewRootNeVar] using hnewRootSlot
              have hslotXWriteRuntime :
                  writtenStore.slotAt (VariableProjection x) =
                    some
                      { oldStoreSlot with
                        value := .value
                          (.ref { location := location, owner := true }) } := by
                rw [hwrittenStore]
                simp [ProgramStore.update]
              have hwellInner : WellFormedTy env rightInner rhsWellLifetime := by
                cases hwellTy with
                | box hinner => exact hinner
              have hnewInnerValidWrite :
                  ValidPartialValue writtenStore slot.value (.ty rightInner) := by
                rw [hwrittenStore]
                exact RuntimeFrame.validPartialValue_update_of_not_reaches
                  hnewInnerValid
                  (by
                    intro reached hreach
                    have hvalueHeap : PartialValueOwnerTargetsHeap slot.value :=
                      partialValueOwnerTargetsHeap_of_slot
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                        hnewRootSlot
                    exact RuntimeFrame.reaches_ne_var_of_varsProtectedIn
                      hwellFormed hsafe
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                      hvalueHeap
                      (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellInner)
                      (by
                        intro y hy
                        exact writeProhibited_of_envSlot_var_in_type hslotXPost rfl
                          (by simpa [PartialTy.vars, Ty.vars] using hy))
                      hnotWriteSource hnotWrite hreach)
              have hnewValidWrite :
                  ValidPartialValue writtenStore
                    (.value (.ref { location := location, owner := true }))
                    (.ty (.box rightInner)) :=
                ValidPartialValue.boxFull hnewRootSlotWrite hnewInnerValidWrite
              have hwriteValidStore : ValidStore writtenStore := by
                rw [hwrittenStore]
                exact validStore_update_disjoint
                  (updatedLocation := VariableProjection x)
                  (slot :=
                    { oldStoreSlot with
                      value := .value
                        (.ref { location := location, owner := true }) })
                  (ValidRuntimeState.validStore hvalidRuntime)
                    (by
                      intro owned hmem howns
                      have hownedEq : owned = location := by
                        simpa [partialValueOwningLocations, valueOwningLocations,
                          valueOwnedLocation?] using hmem
                      exact
                        (ValidRuntimeState.storeTermDisjoint hvalidRuntime location
                          (by
                            simp [termOwningLocations, termValues,
                              valueOwningLocations, valueOwnedLocation?]))
                          (by simpa [hownedEq] using howns))
              have hwriteOwnerHeap : StoreOwnerTargetsHeap writtenStore :=
                storeOwnerTargetsHeap_write
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                  (ValueOwnerTargetsHeap.partial hnewValueHeap) hwriteStoreConcrete
              have hdropValuesHeap :
                  ∀ dropValue, dropValue ∈ [oldStoreSlot.value] →
                    PartialValueOwnerTargetsHeap dropValue := by
                intro dropValue hmem
                simp at hmem
                subst hmem
                have holdHeap : PartialValueOwnerTargetsHeap oldStoreSlot.value :=
                  partialValueOwnerTargetsHeap_of_slot
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hstoreX
                exact holdHeap
              have havoidVarX :
                  DropsAvoids writtenStore [oldStoreSlot.value] (VariableProjection x) :=
                dropsAvoids_var_of_ownerTargetsHeap hdrops hwriteOwnerHeap hdropValuesHeap
              have hnewBorrows :
                  PartialTyBorrowsWellFormedInSlot env rhsWellLifetime
                    (.ty (.box rightInner)) :=
                PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy
              have hnewGraphDisjoint :
                  ∀ reached,
                    RuntimeFrame.OwnerReaches writtenStore
                      (.value (.ref { location := location, owner := true }))
                      (.ty (.box rightInner)) reached →
                    ∀ dropValue, dropValue ∈ [oldStoreSlot.value] →
                      reached ∉ partialValueOwningLocations dropValue := by
                intro reached hreach dropValue hmem howned
                simp at hmem
                subst hmem
                have holdOwns : ProgramStore.OwnsAt store reached (VariableProjection x) := by
                  have holdValue :
                      oldStoreSlot.value = .value (owningRef reached) :=
                    eq_owningRef_of_mem_partialValueOwningLocations howned
                  exact ⟨oldStoreSlot.lifetime, by
                    cases oldStoreSlot with
                    | mk oldValue oldLifetime =>
                        cases holdValue
                        simpa [owningRef] using hstoreX⟩
                rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
                    hnewBorrows hnewValidWrite hreach with hdirect | hsource
                · have hreachedEq : reached = location := by
                    simpa [partialValueOwningLocations, valueOwningLocations,
                      valueOwnedLocation?] using hdirect
                  have holdOwnsLocation :
                      ProgramStore.OwnsAt store location (VariableProjection x) := by
                    simpa [hreachedEq] using holdOwns
                  exact
                    (ValidRuntimeState.storeTermDisjoint hvalidRuntime location
                      (by
                        simp [termOwningLocations, termValues,
                          valueOwningLocations, valueOwnedLocation?]))
                      ⟨VariableProjection x, holdOwnsLocation⟩
                · rcases hsource with ⟨storage, hstorageReach, hownsWrite⟩
                  have hstorageNeVar :
                      storage ≠ VariableProjection x := by
                    have hstorageHeapOrNoVar :
                        storage ≠ VariableProjection x :=
                      RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                        hwriteOwnerHeap
                        (ValueOwnerTargetsHeap.partial hnewValueHeap)
                        hnewBorrows hstorageReach
                    exact hstorageHeapOrNoVar
                  rcases hownsWrite with ⟨ownerLifetime, hownerSlotWrite⟩
                  have hownerSlotStore :
                      store.slotAt storage =
                        some (StoreSlot.mk (.value (owningRef reached))
                          ownerLifetime) := by
                    rw [hwrittenStore] at hownerSlotWrite
                    simpa [ProgramStore.update, hstorageNeVar] using hownerSlotWrite
                  have hownsStore :
                      ProgramStore.OwnsAt store reached storage :=
                    ⟨ownerLifetime, hownerSlotStore⟩
                  have hstorageEq :
                      storage = VariableProjection x :=
                    (ValidRuntimeState.validStore hvalidRuntime)
                      reached storage (VariableProjection x) hownsStore holdOwns
                  exact hstorageNeVar hstorageEq
              have hsafeWrite : writtenStore ∼ₛ env' := by
                rw [henv']
                refine safeAbstraction_update_var_of_preserved henvSlot ?hstoreX
                  hnewValidWrite rfl ?domain ?preserve
                · simpa [hslotLifetime] using hslotXWriteRuntime
                · intro y hyx
                  constructor
                  · intro hdomainStore
                    rcases hdomainStore with ⟨slotY, hslotYWrite⟩
                    have hslotYStore :
                        store.slotAt (VariableProjection y) = some slotY := by
                      rw [hwrittenStore] at hslotYWrite
                      simpa [ProgramStore.update, VariableProjection, hyx] using
                        hslotYWrite
                    exact (hsafe.1 y).mp ⟨slotY, hslotYStore⟩
                  · intro hdomainEnv
                    rcases hdomainEnv with ⟨otherEnvSlot, henvY⟩
                    rcases hsafe.2 y otherEnvSlot henvY with
                      ⟨oldValue, hslotY, _hvalidOld⟩
                    exact ⟨StoreSlot.mk oldValue otherEnvSlot.lifetime, by
                      rw [hwrittenStore]
                      simpa [ProgramStore.update, VariableProjection, hyx] using
                        hslotY⟩
                · intro y otherEnvSlot hyx henvY
                  rcases hsafe.2 y otherEnvSlot henvY with
                    ⟨oldValue, hslotY, hvalidOld⟩
                  have hslotYWrite :
                      writtenStore.slotAt (VariableProjection y) =
                        some (StoreSlot.mk oldValue
                          otherEnvSlot.lifetime) := by
                    rw [hwrittenStore]
                    simpa [ProgramStore.update, VariableProjection, hyx] using hslotY
                  have hvalidOldWrite :
                      ValidPartialValue writtenStore oldValue otherEnvSlot.ty := by
                    rw [hwrittenStore]
                    exact RuntimeFrame.validPartialValue_update_of_not_reaches
                      hvalidOld
                      (by
                        intro reached hreach
                        exact hotherNoReach y otherEnvSlot oldValue hyx
                          henvY hslotY reached hreach)
                  exact ⟨oldValue, hslotYWrite, hvalidOldWrite⟩
              have hslotXPostBox :
                  env'.slotAt x =
                    some { envSlot with ty := .ty (.box rightInner) } := by
                simpa using hslotXPost
              have hnewBorrowsPost :
                  PartialTyBorrowsWellFormedInSlot env' rhsWellLifetime
                    (.ty (.box rightInner)) := by
                rw [henv']
                exact PartialTyBorrowsWellFormedInSlot.update_of_not_pathConflicts
                  (x := x)
                  (slot := { envSlot with ty := .ty (.box rightInner) })
                  (by simpa [henv'] using hnotWrite)
                  hnewBorrows
                  (by
                    intro mutable targets hcontains target htarget hconflict
                    have hxVars :
                        x ∈ PartialTy.vars (.ty (.box rightInner)) :=
                      mem_partialTy_vars_iff.mpr
                        ⟨mutable, targets, target, hcontains, htarget,
                          by simpa [PathConflicts, LVal.base] using hconflict⟩
                    exact hnotWrite
                      (writeProhibited_of_envSlot_var_in_type
                        hslotXPostBox rfl hxVars))
              have hdropDisjointForDeps :
                  ∀ owned,
                    owned ∈ partialValuesOwningLocations [oldStoreSlot.value] →
                      ¬ ProgramStore.Owns writtenStore owned := by
                intro owned hmem howns
                simp [partialValuesOwningLocations] at hmem
                have holdValue :
                    oldStoreSlot.value = .value (owningRef owned) :=
                  eq_owningRef_of_mem_partialValueOwningLocations hmem
                have holdOwnsStore :
                    ProgramStore.OwnsAt store owned (VariableProjection x) :=
                  ⟨oldStoreSlot.lifetime, by
                    cases oldStoreSlot with
                    | mk oldValue oldLifetime =>
                        cases holdValue
                        simpa [owningRef] using hstoreX⟩
                rw [hwrittenStore] at howns
                rcases howns with ⟨storage, ownerLifetime, hownerSlot⟩
                by_cases hstorageX : storage = VariableProjection x
                · subst hstorageX
                  have hnewOwnsOld : owned ∈
                      partialValueOwningLocations
                        (.value (.ref { location := location, owner := true })) := by
                    have hslotNew :
                        { oldStoreSlot with
                          value := .value
                            (.ref { location := location, owner := true }) } =
                          StoreSlot.mk (.value (owningRef owned))
                            ownerLifetime := by
                      simpa [ProgramStore.update] using hownerSlot
                    have hvalueEq :
                        PartialValue.value
                            (Value.ref { location := location, owner := true }) =
                          PartialValue.value (owningRef owned) := by
                      simpa using congrArg StoreSlot.value hslotNew
                    injection hvalueEq with hvalueEq'
                    exact mem_partialValueOwningLocations_of_eq_owningRef
                      (congrArg PartialValue.value hvalueEq')
                  have hownedEq : owned = location := by
                    simpa [partialValueOwningLocations, valueOwningLocations,
                      valueOwnedLocation?] using hnewOwnsOld
                  exact hnewGraphDisjoint location
                    (RuntimeFrame.OwnerReaches.boxFullHere hnewRootSlotWrite)
                    oldStoreSlot.value (by simp) (by simpa [hownedEq] using hmem)
                · have hownerOld :
                      ProgramStore.OwnsAt store owned storage :=
                    ⟨ownerLifetime, by
                      simpa [ProgramStore.update, hstorageX] using hownerSlot⟩
                  have hstorageEq :
                      storage = VariableProjection x :=
                    (ValidRuntimeState.validStore hvalidRuntime)
                      owned storage (VariableProjection x)
                      hownerOld holdOwnsStore
                  exact hstorageX hstorageEq
              have hdropValuesUnprotectedWrite :
                  ∀ dropValue, dropValue ∈ [oldStoreSlot.value] →
                    ∀ owned, owned ∈ partialValueOwningLocations dropValue →
                      ∀ base, ¬ ProtectedByBase writtenStore base owned := by
                exact dropValues_unprotected_of_disjoint
                  hwriteOwnerHeap hdropValuesHeap hdropDisjointForDeps
              have hnewDependencyAvoid :
                  ∀ dependency,
                    RuntimeFrame.BorrowDependency writtenStore
                      (.value (.ref { location := location, owner := true }))
                      (.ty (.box rightInner)) dependency →
                      DropsAvoids writtenStore [oldStoreSlot.value]
                        dependency := by
                intro dependency hdependency
                exact dropsAvoids_of_borrowDependency_unprotected_values
                  hdrops hwellOut hsafeWrite hwriteValidStore hwriteOwnerHeap
                  hdropValuesHeap hdropValuesUnprotectedWrite hnewBorrowsPost
                  hdependency
              have hnewValidFinal :
                  ValidPartialValue store'
                    (.value (.ref { location := location, owner := true }))
                    (.ty (.box rightInner)) :=
                RuntimeFrame.validPartialValue_drops_of_avoids_reaches
                  hdrops hnewValidWrite
                  (by
                    intro reached hreach
                    exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
                      hdrops hwriteValidStore hslotXWriteRuntime
                      hnewBorrows hnewValidWrite havoidVarX
                      hnewGraphDisjoint hnewDependencyAvoid hreach)
              have hallocatedWrite : StoreOwnersAllocated writtenStore :=
                storeOwnersAllocated_write_value_of_validValue
                  (ValidRuntimeState.storeOwnersAllocated hvalidRuntime)
                  (ValidPartialValue.boxFull hnewRootSlot hnewInnerValid)
                  hwriteStoreConcrete
              have hrootWrite : HeapSlotsRootLifetime writtenStore :=
                heapSlotsRootLifetime_write
                  (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime)
                  hwriteStoreConcrete
              have hdropDisjoint :
                  ∀ owned,
                    owned ∈ partialValuesOwningLocations [oldStoreSlot.value] →
                      ¬ ProgramStore.Owns writtenStore owned := by
                intro owned hmem howns
                simp [partialValuesOwningLocations] at hmem
                have holdValue :
                    oldStoreSlot.value = .value (owningRef owned) :=
                  eq_owningRef_of_mem_partialValueOwningLocations hmem
                have holdOwnsStore : ProgramStore.OwnsAt store owned (VariableProjection x) :=
                  ⟨oldStoreSlot.lifetime, by
                    cases oldStoreSlot with
                    | mk oldValue oldLifetime =>
                        cases holdValue
                        simpa [owningRef] using hstoreX⟩
                rw [hwrittenStore] at howns
                rcases howns with ⟨storage, ownerLifetime, hownerSlot⟩
                by_cases hstorageX : storage = VariableProjection x
                · subst hstorageX
                  have hnewOwnsOld : owned ∈
                      partialValueOwningLocations
                        (.value (.ref { location := location, owner := true })) := by
                    have hslotNew :
                        { oldStoreSlot with
                          value := .value
                            (.ref { location := location, owner := true }) } =
                          StoreSlot.mk (.value (owningRef owned))
                            ownerLifetime := by
                      simpa [ProgramStore.update] using hownerSlot
                    have hvalueEq :
                        PartialValue.value
                            (Value.ref { location := location, owner := true }) =
                          PartialValue.value (owningRef owned) := by
                      simpa using congrArg StoreSlot.value hslotNew
                    injection hvalueEq with hvalueEq'
                    exact mem_partialValueOwningLocations_of_eq_owningRef
                      (congrArg PartialValue.value hvalueEq')
                  have hownedEq : owned = location := by
                    simpa [partialValueOwningLocations, valueOwningLocations,
                      valueOwnedLocation?] using hnewOwnsOld
                  exact hnewGraphDisjoint location
                    (RuntimeFrame.OwnerReaches.boxFullHere hnewRootSlotWrite)
                    oldStoreSlot.value (by simp) (by simpa [hownedEq] using hmem)
                · have hownerOld :
                      ProgramStore.OwnsAt store owned storage := by
                    exact ⟨ownerLifetime, by
                      simpa [ProgramStore.update, hstorageX] using hownerSlot⟩
                  have hstorageEq :
                      storage = VariableProjection x :=
                    (ValidRuntimeState.validStore hvalidRuntime)
                      owned storage (VariableProjection x)
                      hownerOld holdOwnsStore
                  exact hstorageX hstorageEq
              have hallocatedFinal : StoreOwnersAllocated store' :=
                drops_storeOwnersAllocated_of_disjoint hdrops hwriteValidStore
                  hallocatedWrite hdropDisjoint
              have hheapFinal : StoreOwnerTargetsHeap store' :=
                drops_storeOwnerTargetsHeap hdrops hwriteOwnerHeap
              have hrootFinal : HeapSlotsRootLifetime store' :=
                drops_heapSlotsRootLifetime hdrops hrootWrite
              have hvalidRuntimeFinal : ValidRuntimeState store' (.val .unit) :=
                validRuntimeState_assign_step_of_postWriteDrop_invariants
                  (lifetime := lifetime)
                  hvalidRuntime hallocatedFinal hheapFinal hrootFinal hread
                  hwriteStoreConcrete hdrops
              have hsafeFinal : store' ∼ₛ env' := by
                rw [henv']
                refine safeAbstraction_update_var_of_preserved henvSlot ?hstoreXFinal
                  hnewValidFinal rfl ?domainFinal ?preserveFinal
                · have hslotFinal :=
                    dropsAvoids_slotAt_preserved hdrops havoidVarX
                      (by
                        simpa [hslotLifetime] using hslotXWriteRuntime)
                  simpa using hslotFinal
                · intro y hyx
                  constructor
                  · intro hdomainStore
                    rcases hdomainStore with ⟨slotY, hslotYFinal⟩
                    have hslotYWrite :
                        writtenStore.slotAt (VariableProjection y) = some slotY :=
                      drops_slotAt_of_slotAt hdrops hslotYFinal
                    have hslotYStore :
                        store.slotAt (VariableProjection y) = some slotY := by
                      rw [hwrittenStore] at hslotYWrite
                      simpa [ProgramStore.update, VariableProjection, hyx] using hslotYWrite
                    exact (hsafe.1 y).mp ⟨slotY, hslotYStore⟩
                  · intro hdomainEnv
                    rcases hdomainEnv with ⟨otherEnvSlot, henvY⟩
                    rcases hsafe.2 y otherEnvSlot henvY with
                      ⟨oldValue, hslotY, _hvalidOld⟩
                    have hslotYWrite :
                        writtenStore.slotAt (VariableProjection y) =
                          some (StoreSlot.mk oldValue
                            otherEnvSlot.lifetime) := by
                      rw [hwrittenStore]
                      simpa [ProgramStore.update, VariableProjection, hyx] using hslotY
                    have havoidY :
                        DropsAvoids writtenStore [oldStoreSlot.value]
                          (VariableProjection y) :=
                      dropsAvoids_var_of_ownerTargetsHeap hdrops hwriteOwnerHeap
                        hdropValuesHeap
                    exact ⟨_, dropsAvoids_slotAt_preserved hdrops havoidY hslotYWrite⟩
                · intro y otherEnvSlot hyx henvY
                  rcases hsafe.2 y otherEnvSlot henvY with
                    ⟨oldValue, hslotY, hvalidOld⟩
                  have hslotYWrite :
                      writtenStore.slotAt (VariableProjection y) =
                        some (StoreSlot.mk oldValue
                          otherEnvSlot.lifetime) := by
                    rw [hwrittenStore]
                    simpa [ProgramStore.update, VariableProjection, hyx] using hslotY
                  have havoidY :
                      DropsAvoids writtenStore [oldStoreSlot.value]
                        (VariableProjection y) :=
                    dropsAvoids_var_of_ownerTargetsHeap hdrops hwriteOwnerHeap
                      hdropValuesHeap
                  have hvalidOldWrite :
                      ValidPartialValue writtenStore oldValue otherEnvSlot.ty := by
                    rw [hwrittenStore]
                    exact RuntimeFrame.validPartialValue_update_of_not_reaches
                      hvalidOld
                      (by
                        intro reached hreach
                        exact hotherNoReach y otherEnvSlot oldValue hyx
                          henvY hslotY reached hreach)
                  have holdGraphDisjoint :
                      ∀ reached,
                        RuntimeFrame.OwnerReaches writtenStore oldValue
                          otherEnvSlot.ty reached →
                        ∀ dropValue, dropValue ∈ [oldStoreSlot.value] →
                          reached ∉ partialValueOwningLocations dropValue := by
                    intro reached hreach dropValue hmem howned
                    simp at hmem
                    subst hmem
                    have holdOwnsX :
                        ProgramStore.OwnsAt store reached (VariableProjection x) := by
                      have holdValue :
                          oldStoreSlot.value = .value (owningRef reached) :=
                        eq_owningRef_of_mem_partialValueOwningLocations howned
                      exact ⟨oldStoreSlot.lifetime, by
                        cases oldStoreSlot with
                        | mk oldValueX oldLifetimeX =>
                            cases holdValue
                            simpa [owningRef] using hstoreX⟩
                    have hborrows :
                        PartialTyBorrowsWellFormedInSlot env otherEnvSlot.lifetime
                          otherEnvSlot.ty := by
                      intro mutable targets hcontains
                      exact hwellFormed.1 y otherEnvSlot mutable targets henvY
                        ⟨otherEnvSlot, henvY, hcontains⟩
                    rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
                        hborrows hvalidOldWrite hreach with hdirect | hsource
                    · have holdValueOwns :
                          oldValue = .value (owningRef reached) :=
                        eq_owningRef_of_mem_partialValueOwningLocations hdirect
                      have hownsY : ProgramStore.OwnsAt store reached (VariableProjection y) :=
                        ⟨otherEnvSlot.lifetime, by
                          cases holdValueOwns
                          simpa [owningRef] using hslotY⟩
                      have hyxLoc :
                          VariableProjection y = VariableProjection x :=
                        (ValidRuntimeState.validStore hvalidRuntime)
                          reached (VariableProjection y) (VariableProjection x)
                          hownsY holdOwnsX
                      exact hyx (by
                        cases hyxLoc
                        rfl)
                    · rcases hsource with ⟨storage, hstorageReach, hownsWrite⟩
                      have hstorageNeX :
                          storage ≠ VariableProjection x := by
                        have hvalueHeap : PartialValueOwnerTargetsHeap oldValue :=
                          partialValueOwnerTargetsHeap_of_slot
                            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                            hslotY
                        exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                          hwriteOwnerHeap hvalueHeap hborrows hstorageReach
                      rcases hownsWrite with ⟨ownerLifetime, hownerSlotWrite⟩
                      have hownerStore :
                          ProgramStore.OwnsAt store reached storage := by
                        rw [hwrittenStore] at hownerSlotWrite
                        exact ⟨ownerLifetime, by
                          simpa [ProgramStore.update, hstorageNeX] using
                            hownerSlotWrite⟩
                      have hstorageEq :
                          storage = VariableProjection x :=
                        (ValidRuntimeState.validStore hvalidRuntime)
                          reached storage (VariableProjection x)
                          hownerStore holdOwnsX
                      exact hstorageNeX hstorageEq
                  have henvYPost :
                      env'.slotAt y = some otherEnvSlot := by
                    rw [henv']
                    simpa [Env.update, hyx] using henvY
                  have hborrowsOldPost :
                      PartialTyBorrowsWellFormedInSlot env'
                        otherEnvSlot.lifetime otherEnvSlot.ty := by
                    intro mutable targets hcontains
                    exact hwellOut.1 y otherEnvSlot mutable targets henvYPost
                      ⟨otherEnvSlot, henvYPost, hcontains⟩
                  have holdDependencyAvoid :
                      ∀ dependency,
                        RuntimeFrame.BorrowDependency writtenStore oldValue
                          otherEnvSlot.ty dependency →
                          DropsAvoids writtenStore [oldStoreSlot.value]
                            dependency := by
                    intro dependency hdependency
                    exact dropsAvoids_of_borrowDependency_unprotected_values
                      hdrops hwellOut hsafeWrite hwriteValidStore hwriteOwnerHeap
                      hdropValuesHeap hdropValuesUnprotectedWrite
                      hborrowsOldPost hdependency
                  have hvalidOldFinal :
                      ValidPartialValue store' oldValue otherEnvSlot.ty :=
                    RuntimeFrame.validPartialValue_drops_of_avoids_reaches
                      hdrops hvalidOldWrite
                      (by
                        intro reached hreach
                        exact RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
                          hdrops hwriteValidStore hslotYWrite
                          (by
                            intro mutable targets hcontains
                            exact hwellFormed.1 y otherEnvSlot mutable targets henvY
                              ⟨otherEnvSlot, henvY, hcontains⟩)
                          hvalidOldWrite havoidY holdGraphDisjoint
                          holdDependencyAvoid hreach)
                  exact ⟨oldValue,
                    dropsAvoids_slotAt_preserved hdrops havoidY hslotYWrite,
                    hvalidOldFinal⟩
              exact ⟨hvalidRuntimeFinal, hsafeFinal, ValidPartialValue.unit⟩

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
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ dropValue, dropValue ∈ values → PartialValueOwnerTargetsHeap dropValue) →
    (∀ owned, owned ∈ partialValuesOwningLocations values →
      ¬ ProgramStore.Owns store owned) →
    Drops store values store' →
    store' ∼ₛ env := by
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
    store ∼ₛ env →
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
    store ∼ₛ env →
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
    store' ∼ₛ
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

theorem safeAbstraction_update_owner_spine_full_of_frames
    {store store' : ProgramStore} {env writeEnv : Env}
    {current : Lifetime} {x : Name}
    {envSlot : EnvSlot} {rootSlot leafSlot : StoreSlot}
    {leaf : Location} {oldLeafTy rhsTy : Ty} {updatedTy : PartialTy}
    {path : Path} {rank : Nat} {value : Value} :
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env.slotAt x = some envSlot →
    store.slotAt (VariableProjection x) = some rootSlot →
    rootSlot.lifetime = envSlot.lifetime →
    StoreOwnerSpine store (VariableProjection x) rootSlot envSlot.ty
      path leaf leafSlot (.ty oldLeafTy) →
    path ≠ [] →
    UpdateAtPath rank env path envSlot.ty rhsTy writeEnv updatedTy →
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
    store' ∼ₛ
      (writeEnv.update x { envSlot with ty := updatedTy }) := by
  intro hwellFormed hsafe hvalidStore hheap henvSlot hrootSlot hrootLifetime
    hspine hpathNonempty hupdate hstore' hnewValid hotherNoReachLeaf
  have hwriteEnvEq : writeEnv = env :=
    StoreOwnerSpine.updateAtPath_env_eq hspine hupdate
  subst writeEnv
  subst hstore'
  have hrootValidFinal :
      ValidPartialValue
        (store.update leaf { leafSlot with value := .value value })
        rootSlot.value updatedTy :=
    StoreOwnerSpine.valid_after_updateAtPath_nonempty_full hspine
      hpathNonempty hupdate hnewValid
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
          (() :: tail) leaf leafSlot (.ty oldLeafTy) := by
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
          (() :: tail) leaf leafSlot (.ty oldLeafTy) := by
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
  | unit =>
      intro _howners _hdeps
      exact ValidPartialValue.unit
  | int =>
      intro _howners _hdeps
      exact ValidPartialValue.int
  | undef =>
      intro _howners _hdeps
      exact ValidPartialValue.undef
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

theorem safeAbstraction_update_owner_spine_full_of_split_frames
    {store store' : ProgramStore} {env writeEnv : Env}
    {current : Lifetime} {x : Name}
    {envSlot : EnvSlot} {rootSlot leafSlot : StoreSlot}
    {leaf : Location} {oldLeafTy rhsTy : Ty} {updatedTy : PartialTy}
    {path : Path} {rank : Nat} {value : Value} :
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    env.slotAt x = some envSlot →
    store.slotAt (VariableProjection x) = some rootSlot →
    rootSlot.lifetime = envSlot.lifetime →
    StoreOwnerSpine store (VariableProjection x) rootSlot envSlot.ty
      path leaf leafSlot (.ty oldLeafTy) →
    path ≠ [] →
    UpdateAtPath rank env path envSlot.ty rhsTy writeEnv updatedTy →
    store' = store.update leaf { leafSlot with value := .value value } →
    ValidPartialValue store' (.value value) (.ty rhsTy) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.OwnerReaches store oldValue otherEnvSlot.ty location →
        location ≠ leaf) →
    (∀ y otherEnvSlot oldValue,
      y ≠ x →
      env.slotAt y = some otherEnvSlot →
      store.slotAt (VariableProjection y) =
        some { value := oldValue, lifetime := otherEnvSlot.lifetime } →
      ∀ location,
        RuntimeFrame.BorrowDependency store oldValue otherEnvSlot.ty location →
        location ≠ leaf) →
    store' ∼ₛ
      (writeEnv.update x { envSlot with ty := updatedTy }) := by
  intro hwellFormed hsafe hvalidStore hheap henvSlot hrootSlot hrootLifetime
    hspine hpathNonempty hupdate hstore' hnewValid hotherOwnerNoReachLeaf
    hotherDependencyNoReachLeaf
  have hwriteEnvEq : writeEnv = env :=
    StoreOwnerSpine.updateAtPath_env_eq hspine hupdate
  subst writeEnv
  subst hstore'
  have hrootValidFinal :
      ValidPartialValue
        (store.update leaf { leafSlot with value := .value value })
        rootSlot.value updatedTy :=
    StoreOwnerSpine.valid_after_updateAtPath_nonempty_full hspine
      hpathNonempty hupdate hnewValid
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
          (() :: tail) leaf leafSlot (.ty oldLeafTy) := by
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
          (() :: tail) leaf leafSlot (.ty oldLeafTy) := by
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
      RuntimeFrame.validPartialValue_update_of_owner_and_borrow_dependency_frame
        hvalidOld
        (hotherOwnerNoReachLeaf y otherEnvSlot oldValue hyx henvY hslotY)
        (hotherDependencyNoReachLeaf y otherEnvSlot oldValue hyx henvY hslotY)⟩

theorem stored_var_reaches_ne_owner_spine_leaf_of_noWrite
    {store : ProgramStore} {sourceEnv observerEnv : Env}
    {current : Lifetime} {x y : Name}
    {rootSlot leafSlot : StoreSlot} {otherEnvSlot : EnvSlot}
    {oldValue : PartialValue} {leaf : Location}
    {rootTy leafTy : PartialTy} {path : Path} :
    WellFormedEnv sourceEnv current →
    store ∼ₛ sourceEnv →
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
    store ∼ₛ sourceEnv →
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
    store ∼ₛ env →
    LValTyping env lv pt lifetime →
    store.loc lv = some location →
    ∃ root slotL viewTy slotLifetime,
      ProtectedByBase store root location ∧
      φ root ≤ φ (LVal.base lv) ∧
      store.slotAt location = some slotL ∧
      ValidPartialValue store slotL.value viewTy ∧
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
      (hsafe : store ∼ₛ env) (htyping : LValTyping env lv pt lifetime)
      (hloc : store.loc lv = some location) :
      ∃ root slotL viewTy slotLifetime,
        ProtectedByBase store root location ∧
        φ root ≤ φ (LVal.base lv) ∧
        store.slotAt location = some slotL ∧
        ValidPartialValue store slotL.value viewTy ∧
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
              hstoreSlot, hvalid, hφ x slot hslot, ?_, ?_,
              ⟨slot, value, hslot, hstoreSlot, Or.inl ⟨rfl, rfl, rfl⟩⟩⟩
            · intro mutable targets hcontains
              exact hwellFormed.1 x slot mutable targets hslot
                ⟨slot, hslot, hcontains⟩
            · intro mutable targets hcontains
              exact ⟨slot, hslot, hcontains⟩
    | deref u =>
        cases htyping with
        | @box _ _ sourceLifetime hsource =>
            have hsourceAbs :
                LValLocationAbstraction store u (.box _) :=
              lvalTyping_defined_location hwellFormed hsafe hsource
            rcases hsourceAbs with
              ⟨middle, middleSlot, hmiddleLoc, hmiddleSlot, hmiddleValid⟩
            rcases middleSlot with ⟨middleValue, middleLifetime⟩
            rcases go hφ hwellFormed hsafe hsource hmiddleLoc with
              ⟨root, slotM, viewTyM, slotLt, hprotM, hrank, hslotM, hvalidM,
                hbound, hborrowsM, hcontainsM, rootEnvSlot, rootValue,
                hrootEnvSlot, hrootValue, hdescent⟩
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
                      hrank, hownedSlot₂, hinnerView, ?_, ?_, ?_,
                      rootEnvSlot, rootValue, hrootEnvSlot, hrootValue,
                      Or.inr ?_⟩
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
                    refine ⟨root, ownedSlot₂, .ty innerTy, slotLt,
                      ProtectedByBase.trans_owned hprotM hownsAt,
                      hrank, hownedSlot₂, hinnerView, ?_, ?_, ?_,
                      rootEnvSlot, rootValue, hrootEnvSlot, hrootValue,
                      Or.inr ?_⟩
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
                      · exact RuntimeFrame.ReachesSlot.snoc_boxFull hreach rfl
                          rfl hownedSlot₂ hinnerView
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
                hbound, hborrowsM, hcontainsM, rootEnvSlot, rootValue,
                hrootEnvSlot, hrootValue, hdescent⟩
            have hslotMEq :
                slotM = ⟨middleValue, middleLifetime⟩ :=
              Option.some.inj (hslotM.symm.trans hmiddleSlot)
            subst hslotMEq
            cases hmiddleValid with
            | @borrow target₀Loc _mutable _targets target₀ hmem₀ htarget₀Loc =>
                have hderefLoc : store.loc (.deref u) = some target₀Loc := by
                  simp [ProgramStore.loc, hmiddleLoc, hmiddleSlot]
                have hlocEq : location = target₀Loc := by
                  rw [hloc] at hderefLoc
                  exact Option.some.inj hderefLoc
                subst hlocEq
                cases hvalidM with
                | @borrow location' mutable' targets' witness hmemW hlocW =>
                    rcases hborrowsM PartialTyContains.here witness hmemW with
                      ⟨witnessTy, witnessLifetime, hwitnessTyping, _houtlives,
                        _hbase⟩
                    have hwitnessRank :
                        φ (LVal.base witness) < φ root := by
                      refine hbound (LVal.base witness) ?_
                      simpa [PartialTy.vars, Ty.vars] using
                        List.mem_map_of_mem hmemW
                    have hcallRank :
                        φ (LVal.base witness) < φ (LVal.base u) :=
                      lt_of_lt_of_le hwitnessRank hrank
                    rcases go hφ hwellFormed hsafe hwitnessTyping hlocW with
                      ⟨root₂, slotL, viewTy, slotLt₂, hprot₂, hrank₂, hslotL,
                        hvalidL, hbound₂, hborrows₂, hcontains₂, hdescent₂⟩
                    exact ⟨root₂, slotL, viewTy, slotLt₂, hprot₂,
                      le_of_lt (lt_of_le_of_lt hrank₂ hcallRank),
                      hslotL, hvalidL, hbound₂, hborrows₂, hcontains₂,
                      hdescent₂⟩
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
    store ∼ₛ env →
    LValTyping env u pt lifetime →
    store.loc u = some middle →
    store.loc (.deref u) = some result →
    LocationBelow store φ result middle := by
  intro hφ hwellFormed hsafe htyping hmiddleLoc hloc
  rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe htyping
      hmiddleLoc with
    ⟨root, slotM, viewTyM, slotLt, hprotM, _hrank, hslotM, hvalidM, hbound,
      hborrowsM, _hcontainsM, _hdescentM⟩
  rcases slotM with ⟨middleValue, middleLifetime⟩
  cases hvalidM with
  | unit =>
      simp [ProgramStore.loc, hmiddleLoc, hslotM] at hloc
  | int =>
      simp [ProgramStore.loc, hmiddleLoc, hslotM] at hloc
  | undef =>
      simp [ProgramStore.loc, hmiddleLoc, hslotM] at hloc
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
        ⟨root₂, _, _, _, hprot₂, hrank₂, _, _, _, _, _, _⟩
      exact ⟨root₂, root, hprot₂, hprotM,
        Or.inl (lt_of_le_of_lt hrank₂ hwitnessRank)⟩
  | @box owned ownedSlot innerView hownedSlot _hinner =>
      have hderefLoc : store.loc (.deref u) = some owned := by
        simp [ProgramStore.loc, hmiddleLoc, hslotM]
      have hresEq : result = owned := by
        rw [hloc] at hderefLoc
        exact Option.some.inj hderefLoc
      subst hresEq
      have hownsAt : ProgramStore.OwnsAt store result middle :=
        ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
      exact ⟨root, root, ProtectedByBase.trans_owned hprotM hownsAt, hprotM,
        Or.inr ⟨rfl, ProgramStore.OwnsTransitively.direct hownsAt⟩⟩
  | @boxFull owned ownedSlot innerTy hownedSlot _hinner =>
      have hderefLoc : store.loc (.deref u) = some owned := by
        simp [ProgramStore.loc, hmiddleLoc, hslotM]
      have hresEq : result = owned := by
        rw [hloc] at hderefLoc
        exact Option.some.inj hderefLoc
      subst hresEq
      have hownsAt : ProgramStore.OwnsAt store result middle :=
        ⟨middleLifetime, by simpa [owningRef] using hslotM⟩
      exact ⟨root, root, ProtectedByBase.trans_owned hprotM hownsAt, hprotM,
        Or.inr ⟨rfl, ProgramStore.OwnsTransitively.direct hownsAt⟩⟩

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
    store ∼ₛ env →
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
          exact RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe hsource
            huLoc hloc
      | borrow hsource htargets =>
          exact RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe hsource
            huLoc hloc
  | @there u readLoc hinner ih =>
      cases htyping with
      | box hsource =>
          rcases lvalTyping_defined_location hwellFormed hsafe hsource with
            ⟨middle, middleSlot, hmiddleLoc, _hmiddleSlot, _hmiddleValid⟩
          exact LocationBelow.trans hvalidStore hheap
            (RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe hsource
              hmiddleLoc hloc)
            (ih hsource hmiddleLoc)
      | borrow hsource htargets =>
          rcases lvalTyping_defined_location hwellFormed hsafe hsource with
            ⟨middle, middleSlot, hmiddleLoc, _hmiddleSlot, _hmiddleValid⟩
          exact LocationBelow.trans hvalidStore hheap
            (RuntimeFrame.loc_deref_step_below hφ hwellFormed hsafe hsource
              hmiddleLoc hloc)
            (ih hsource hmiddleLoc)

/-- No typed lval reads the location it resolves to. -/
theorem RuntimeFrame.loc_not_locReads_self {store : ProgramStore} {env : Env}
    {current : Lifetime} {φ : Name → Nat} {lv : LVal} {pt : PartialTy}
    {lifetime : Lifetime} {location : Location} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env lv pt lifetime →
    store.loc lv = some location →
    ¬ RuntimeFrame.LocReads store lv location := by
  intro hφ hwellFormed hsafe hvalidStore hheap htyping hloc hreads
  rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe htyping
      hloc with
    ⟨_root, slotL, viewTy, _slotLt, _hprot, _hrank, hslotL, hvalidL, _hbound,
      _hborrows, _hcontains, _hdescent⟩
  exact LocationBelow.irrefl hvalidStore hheap hslotL hvalidL
    (RuntimeFrame.locReads_below hφ hwellFormed hsafe hvalidStore hheap
      htyping hreads hloc)

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
    store ∼ₛ env →
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
      (hsafe : store ∼ₛ env) (hvalidStore : ValidStore store)
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
        have hsourceTyped : ∃ ptu ltu, LValTyping env u ptu ltu := by
          cases htyping with
          | box hsource => exact ⟨_, _, hsource⟩
          | borrow hsource htargets => exact ⟨_, _, hsource⟩
        rcases hsourceTyped with ⟨ptu, ltu, hsource⟩
        have hMlocEx : ∃ M, store.loc u = some M := by
          cases hM : store.loc u with
          | none => simp [ProgramStore.loc, hM] at hloc
          | some M => exact ⟨M, rfl⟩
        rcases hMlocEx with ⟨M, hMloc⟩
        rcases RuntimeFrame.loc_intrinsicRootView hφ hwellFormed hsafe hsource
            hMloc with
          ⟨rootM, slotM, viewTyM, slotLt, hprotM, hrankM, hslotM, hvalidM,
            hbound, hborrowsM, hcontainsM, _hdescentM⟩
        rcases slotM with ⟨middleValue, middleLifetime⟩
        cases hvalidM with
        | unit =>
            simp [ProgramStore.loc, hMloc, hslotM] at hloc
        | int =>
            simp [ProgramStore.loc, hMloc, hslotM] at hloc
        | undef =>
            simp [ProgramStore.loc, hMloc, hslotM] at hloc
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
              go hφ hwellFormed hsafe hvalidStore hheap hcollapse hsource
                hMloc hprotM' hG
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
      | borrow hsource htargets => exact ⟨u, _, _, hsource, rfl, huLoc⟩
  | @there u readLoc hinner ih =>
      cases htyping with
      | box hsource =>
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
    store ∼ₛ env →
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

/--
Borrow-dependency version of the guarded-base chase: if a slot value has a
borrow-resolution dependency inside a guard-protected owner tree, the slot
variable itself is absorbed into the guard set.
-/
theorem RuntimeFrame.borrowDependency_protected_guarded {store : ProgramStore}
    {env : Env} {current slotLifetime : Lifetime} {φ : Name → Nat}
    {G : Name → Prop} {value : PartialValue} {partialTy : PartialTy}
    {dependency : Location} {observer : Name} {r : Name} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    (∀ container mutable ts t, env ⊢ container ↝ (.borrow mutable ts) →
      t ∈ ts → G (LVal.base t) → G container) →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    (∀ {mutable : Bool} {targets : List LVal},
      PartialTyContains partialTy (.borrow mutable targets) →
      env ⊢ observer ↝ (.borrow mutable targets)) →
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    ProtectedByBase store r dependency →
    G r →
    G observer := by
  intro hφ hwellFormed hsafe hvalidStore hheap hcollapse hborrows hcontains
    hdependency hprot hG
  induction hdependency generalizing slotLifetime with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      have hGtarget : G (LVal.base target) :=
        RuntimeFrame.locReads_protected_guarded_base hφ hwellFormed hsafe
          hvalidStore hheap hcollapse htargetTyping hreads hprot hG
      exact hcollapse observer mutable targets target
        (hcontains PartialTyContains.here) hmem hGtarget
  | @boxInner location slot inner dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime inner := by
        intro mutable targets hcontains'
        exact hborrows (PartialTyContains.box hcontains')
      have hinnerContains :
          ∀ {mutable : Bool} {targets : List LVal},
            PartialTyContains inner (.borrow mutable targets) →
            env ⊢ observer ↝ (.borrow mutable targets) := by
        intro mutable targets hcontains'
        exact hcontains (PartialTyContains.box hcontains')
      exact ih hinnerBorrows hinnerContains hprot
  | @boxFullInner location slot innerTy dependency hslot hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env slotLifetime (.ty innerTy) := by
        intro mutable targets hcontains'
        exact hborrows (PartialTyContains.tyBox hcontains')
      have hinnerContains :
          ∀ {mutable : Bool} {targets : List LVal},
            PartialTyContains (.ty innerTy) (.borrow mutable targets) →
            env ⊢ observer ↝ (.borrow mutable targets) := by
        intro mutable targets hcontains'
        exact hcontains (PartialTyContains.tyBox hcontains')
      exact ih hinnerBorrows hinnerContains hprot

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
Dependency kill for the intrinsic root of a borrow-node cell on the
resolution: the node's stored reference resolves at or below the written
location, while a dependency on the written location resolves strictly below
it.
-/
theorem slotDepKill_of_intrinsic_node {store : ProgramStore} {env : Env}
    {current : Lifetime} {φ : Name → Nat} {leaf nodeCell nextLoc : Location}
    {rootM : Name} {slotM : StoreSlot} {mutable : Bool} {targets : List LVal}
    {slotLt : Lifetime} {rootEnvSlot : EnvSlot} {rootValue : PartialValue}
    {leafSlot nextSlot : StoreSlot} {leafView nextView : PartialTy} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    store.slotAt nodeCell = some slotM →
    slotM.value = .value (.ref { location := nextLoc, owner := false }) →
    PartialTyBorrowsWellFormedInSlot env slotLt
      (.ty (.borrow mutable targets)) →
    env.slotAt rootM = some rootEnvSlot →
    store.slotAt (VariableProjection rootM) =
      some { value := rootValue, lifetime := rootEnvSlot.lifetime } →
    ((nodeCell = VariableProjection rootM ∧
        (.ty (.borrow mutable targets) : PartialTy) = rootEnvSlot.ty ∧
        slotM.value = rootValue) ∨
      RuntimeFrame.ReachesSlot store rootValue rootEnvSlot.ty nodeCell slotM
        (.ty (.borrow mutable targets))) →
    (LocationBelow store φ leaf nextLoc ∨ leaf = nextLoc) →
    store.slotAt leaf = some leafSlot →
    ValidPartialValue store leafSlot.value leafView →
    store.slotAt nextLoc = some nextSlot →
    ValidPartialValue store nextSlot.value nextView →
    SlotDepKill store env leaf rootM := by
  intro hφ hwellFormed hsafe hvalidStore hheap hslotM hslotMValue hborrows
    hrootEnvSlot hrootStoreSlot hdescent hbelowNext hleafSlot hleafValid
    hnextSlot hnextValid
  intro zslot value hzslot hzstore hdep
  have hzslotEq : zslot = rootEnvSlot :=
    Option.some.inj (hzslot.symm.trans hrootEnvSlot)
  subst hzslotEq
  have hvalueEq : value = rootValue := by
    have := Option.some.inj (hzstore.symm.trans hrootStoreSlot)
    exact congrArg StoreSlot.value this
  subst hvalueEq
  have hnodeDep :
      RuntimeFrame.BorrowDependency store slotM.value
        (.ty (.borrow mutable targets)) leaf := by
    rcases hdescent with ⟨_hcellVar, hviewEq, hvalEq⟩ | hreach
    · rw [← hvalEq, ← hviewEq] at hdep
      exact hdep
    · exact RuntimeFrame.borrowDependency_through_reachesSlot hreach rfl hdep
  rw [hslotMValue] at hnodeDep
  cases hnodeDep with
  | @borrow _ _ _ _ target hmem _hloc hreads =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      have hbelow : LocationBelow store φ nextLoc leaf :=
        RuntimeFrame.locReads_below hφ hwellFormed hsafe hvalidStore hheap
          htargetTyping hreads _hloc
      rcases hbelowNext with hbelowLeaf | hleafEq
      · exact LocationBelow.irrefl hvalidStore hheap hnextSlot hnextValid
          (LocationBelow.trans hvalidStore hheap hbelow hbelowLeaf)
      · subst hleafEq
        exact LocationBelow.irrefl hvalidStore hheap hleafSlot hleafValid
          hbelow

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
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, _hinner⟩
        cases htyEq
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, hwrites⟩
        cases htyEq
        exact ⟨rfl, _, hwrites⟩
  | box _hslot _howner _htail ih =>
      intro hleafTy hupdate
      rcases UpdateAtPath.cons_inv (by simpa using hupdate) with hbox | hborrow
      · rcases hbox with ⟨inner, updatedInner, htyEq, _hupdatedEq, hinner⟩
        cases htyEq
        exact ih hleafTy hinner
      · rcases hborrow with ⟨writeTargets, htyEq, _hupdatedEq, _hwrites⟩
        cases htyEq

/--
The first borrow node crossed by a deref-of-borrow resolution: the node's cell
sits at the end of an all-box owner spine from the base variable, its stored
reference points at the continuation location `L`, and `L` is the resolution
result or read by it.  The syntactic decomposition pins the crossing deref.
-/
theorem firstNodePack {store : ProgramStore} {env : Env} {current : Lifetime}
    {source : LVal} {mutable : Bool} {targets : List LVal}
    {sourceLifetime : Lifetime} {res : Location} :
    WellFormedEnv env current →
    store ∼ₛ env →
    LValTyping env source (.ty (.borrow mutable targets)) sourceLifetime →
    store.loc (.deref source) = some res →
    ∃ envSlot rootValue cell cellSlot L m ts spinePath suffix u₀,
      env.slotAt (LVal.base source) = some envSlot ∧
      store.slotAt (VariableProjection (LVal.base source)) =
        some { value := rootValue, lifetime := envSlot.lifetime } ∧
      store.slotAt cell = some cellSlot ∧
      cellSlot.value = .value (.ref { location := L, owner := false }) ∧
      ValidPartialValue store cellSlot.value (.ty (.borrow m ts)) ∧
      StoreOwnerSpine store (VariableProjection (LVal.base source))
        { value := rootValue, lifetime := envSlot.lifetime } envSlot.ty
        spinePath cell cellSlot (.ty (.borrow m ts)) ∧
      LVal.deref source = prependPath suffix (.deref u₀) ∧
      store.loc (.deref u₀) = some L ∧
      LVal.path u₀ = spinePath ∧
      (res = L ∨ RuntimeFrame.LocReads store (.deref source) L) := by
  intro hwellFormed hsafe htyping hloc
  induction source generalizing mutable targets sourceLifetime res with
  | var b =>
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
      rcases hsafe.2 b slot hslot with ⟨rootValue, hstoreSlot, hvalid⟩
      have hvalidB := hvalid
      rw [hslotTy] at hvalidB
      cases hvalidB with
      | @borrow L _m _ts w hmemW hlocW =>
          have hlocDeref :
              store.loc (.deref (.var b)) = some L := by
            simp [ProgramStore.loc, VariableProjection] at hstoreSlot ⊢
            simp [hstoreSlot]
          have hresEq : res = L :=
            Option.some.inj (hloc.symm.trans hlocDeref)
          have hspine :
              StoreOwnerSpine store (VariableProjection b)
                { value :=
                    PartialValue.value
                      (Value.ref { location := L, owner := false }),
                  lifetime := slot.lifetime } slot.ty []
                (VariableProjection b)
                { value :=
                    PartialValue.value
                      (Value.ref { location := L, owner := false }),
                  lifetime := slot.lifetime }
                (.ty (.borrow mutable targets)) := by
            rw [← hslotTy]
            exact StoreOwnerSpine.nil hstoreSlot hvalid
          refine ⟨slot,
            PartialValue.value (Value.ref { location := L, owner := false }),
            VariableProjection b,
            { value :=
                PartialValue.value
                  (Value.ref { location := L, owner := false }),
              lifetime := slot.lifetime }, L, mutable,
            targets, [], [], .var b, hslot, hstoreSlot, hstoreSlot, rfl,
            ?_, hspine, rfl, hlocDeref, rfl, Or.inl hresEq⟩
          exact ValidPartialValue.borrow hmemW hlocW
  | deref u' ih =>
      cases htyping with
      | @box _ _ _ hsource' =>
          rcases StoreOwnerSpine.of_lvalTyping_box hwellFormed hsafe
              hsource' with
            ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
              hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot, hsourceSpine⟩
          have hsourceValid := StoreOwnerSpine.leaf_valid hsourceSpine
          rcases sourceSlot with ⟨sourceValue, sourceLifetime'⟩
          cases hsourceValid with
          | @box cell cellSlot _ hcellSlot hinnerValid =>
              have hinnerValid' := hinnerValid
              rcases cellSlot with ⟨cellValue, cellLifetime⟩
              cases hinnerValid with
              | @borrow L _m _ts w hmemW hlocW =>
                  have hsnoc :=
                    StoreOwnerSpine.snoc_box hsourceSpine rfl rfl hcellSlot
                      hinnerValid'
                  have hrootSlotEq :
                      rootSlot =
                        { value := rootSlot.value,
                          lifetime := envSlot.lifetime } := by
                    rw [← hrootLifetime]
                  rw [hrootSlotEq] at hsnoc hrootSlot
                  have hlocU :
                      store.loc (.deref u') = some cell := by
                    simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                  have hlocDeref :
                      store.loc (.deref (.deref u')) = some L := by
                    generalize hgen : LVal.deref u' = du at hlocU ⊢
                    simp [ProgramStore.loc, hlocU, hcellSlot]
                  have hresEq : res = L :=
                    Option.some.inj (hloc.symm.trans hlocDeref)
                  refine ⟨envSlot, rootSlot.value, cell,
                    { value :=
                        PartialValue.value
                          (Value.ref { location := L, owner := false }),
                      lifetime := cellLifetime }, L,
                    mutable, targets, () :: LVal.path u', [], .deref u',
                    henvBase, hrootSlot, hcellSlot, rfl, hinnerValid', ?_,
                    rfl, hlocDeref, by simp [LVal.path], Or.inl hresEq⟩
                  exact hsnoc
      | @borrow _ mutable' targets' borrowLifetime' targetLifetime' targetTy'
          hsource' htargets' =>
          have hM₀ : ∃ M₀, store.loc (.deref u') = some M₀ := by
            cases hM : store.loc (.deref u') with
            | none =>
                exfalso
                generalize hgen : LVal.deref u' = du at hM hloc
                simp [ProgramStore.loc, hM] at hloc
            | some M₀ => exact ⟨M₀, rfl⟩
          rcases hM₀ with ⟨M₀, hM₀loc⟩
          rcases ih hsource' hM₀loc with
            ⟨envSlot, rootValue, cell, cellSlot, L, m, ts, spinePath, suffix,
              u₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
          refine ⟨envSlot, rootValue, cell, cellSlot, L, m, ts, spinePath,
            () :: suffix, u₀, h1, h2, h3, h4, h5, h6, ?_, h8, h9, ?_⟩
          · show LVal.deref (LVal.deref u') = .deref (prependPath suffix
              (.deref u₀))
            rw [← h7]
          · right
            rcases h10 with hM₀eq | hreads
            · exact RuntimeFrame.LocReads.here (by rw [hM₀loc, hM₀eq])
            · exact RuntimeFrame.LocReads.there hreads

theorem StoreOwnerSpine.nil_inv {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} :
    StoreOwnerSpine store storage slot ty [] leaf leafSlot leafTy →
    storage = leaf ∧ slot = leafSlot ∧ ty = leafTy := by
  intro h
  cases h with
  | nil _ _ => exact ⟨rfl, rfl, rfl⟩

/--
Dependency kill for the base of a deref-of-borrow resolution: the first
crossed borrow node's stored reference resolves at-or-below the written
location, so a dependency of the base's value on the written location closes a
cycle in the location order.
-/
theorem slotDepKill_of_firstNode {store : ProgramStore} {env : Env}
    {current : Lifetime} {φ : Name → Nat} {source : LVal} {mutable : Bool}
    {targets : List LVal} {sourceLifetime : Lifetime} {derefTy : PartialTy}
    {derefLifetime : Lifetime} {leaf : Location} {leafSlot : StoreSlot}
    {leafView : PartialTy} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env source (.ty (.borrow mutable targets)) sourceLifetime →
    LValTyping env (.deref source) derefTy derefLifetime →
    store.loc (.deref source) = some leaf →
    store.slotAt leaf = some leafSlot →
    ValidPartialValue store leafSlot.value leafView →
    SlotDepKill store env leaf (LVal.base source) := by
  intro hφ hwellFormed hsafe hvalidStore hheap htyping hderefTyping hloc
    hleafSlot hleafValid
  rcases firstNodePack hwellFormed hsafe htyping hloc with
    ⟨envSlot, rootValue, cell, cellSlot, L, m, ts, spinePath, suffix, u₀,
      h1, h2, h3, h4, h5, h6, _h7, _h8, _h9, h10⟩
  intro zslot value hzslot hzstore hdep
  have hzslotEq : envSlot = zslot :=
    Option.some.inj (h1.symm.trans hzslot)
  subst hzslotEq
  have hvalueEq : rootValue = value := by
    have := Option.some.inj (h2.symm.trans hzstore)
    exact congrArg StoreSlot.value this
  subst hvalueEq
  have hnodeDep :
      RuntimeFrame.BorrowDependency store cellSlot.value
        (.ty (.borrow m ts)) leaf := by
    by_cases hpath : spinePath = []
    · subst hpath
      rcases StoreOwnerSpine.nil_inv h6 with ⟨_hcellEq, hcellSlotEq, htyEq⟩
      rw [htyEq] at hdep
      rw [← hcellSlotEq]
      exact hdep
    · have hreach :=
        StoreOwnerSpine.reachesSlot_of_spine h6 hpath
      exact RuntimeFrame.borrowDependency_through_reachesSlot hreach rfl hdep
  rw [h4] at hnodeDep
  cases hnodeDep with
  | @borrow _ _ _ _ target hmem' hloc' hreads' =>
      have hcontains : PartialTyContains envSlot.ty (.borrow m ts) :=
        StoreOwnerSpine.contains_leafTy h6 rfl
      rcases hwellFormed.1 (LVal.base source) envSlot m ts h1
          ⟨envSlot, h1, hcontains⟩ target hmem' with
        ⟨targetTy, targetLifetime, htargetTyping, _houtlives, _hbase⟩
      have hbelowDown : LocationBelow store φ L leaf :=
        RuntimeFrame.locReads_below hφ hwellFormed hsafe hvalidStore hheap
          htargetTyping hreads' hloc'
      rcases h10 with hleafEq | hreads
      · rw [← hleafEq] at hbelowDown
        exact LocationBelow.irrefl hvalidStore hheap hleafSlot hleafValid
          hbelowDown
      · have hbelowUp : LocationBelow store φ leaf L :=
          RuntimeFrame.locReads_below hφ hwellFormed hsafe hvalidStore hheap
          hderefTyping hreads hloc
        exact LocationBelow.irrefl hvalidStore hheap hleafSlot hleafValid
          (LocationBelow.trans hvalidStore hheap hbelowUp hbelowDown)

/-- Resolution only depends on the start location. -/
theorem ProgramStore.loc_congr_prependPath {store : ProgramStore}
    {a b : LVal} (h : store.loc a = store.loc b) :
    ∀ p : List Unit,
      store.loc (prependPath p a) = store.loc (prependPath p b) := by
  intro p
  induction p with
  | nil => exact h
  | cons head tail ih =>
      cases head
      show store.loc (.deref (prependPath tail a)) =
        store.loc (.deref (prependPath tail b))
      simp [ProgramStore.loc, ih]

/-- Every fan-out member is fully typed. -/
theorem WriteBorrowTargets.typed_of_mem {rank : Nat} {env result : Env}
    {path : Path} {targets : List LVal} {rhsTy : Ty} :
    WriteBorrowTargets rank env path targets rhsTy result →
    ∀ target, target ∈ targets →
      ∃ leafTy leafLifetime,
        LValTyping env (prependPath path target) (.ty leafTy) leafLifetime := by
  intro hwrites
  refine WriteBorrowTargets.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _rank env path targets rhsTy _result _ =>
      ∀ target, target ∈ targets →
        ∃ leafTy leafLifetime,
          LValTyping env (prependPath path target) (.ty leafTy) leafLifetime)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?strong ?weak ?box ?mutBorrow ?nil ?singleton ?cons ?intro hwrites
  case strong => intros; trivial
  case weak => intros; trivial
  case box => intros; trivial
  case mutBorrow => intros; trivial
  case nil =>
    intro _rank _env _path _ty target htarget
    simp at htarget
  case singleton =>
    intro _rank _env _updated _path target _ty _hwrite htyped _ih selected
      hselected
    rw [List.mem_singleton] at hselected
    subst hselected
    exact htyped
  case cons =>
    intro _rank _env _updated _restEnv _result _path target rest _ty _hwrite
      htyped _hwrites _hjoin _ihWrite ihRest selected hselected
    rcases List.mem_cons.mp hselected with hhead | htail
    · subst hhead
      exact htyped
    · exact ihRest selected htail
  case intro => intros; trivial

set_option maxRecDepth 4096 in
/--
The write's authority guard reaches a protector of the written location: the
resolution's chain of first-crossed mutable-borrow nodes steps the guard from
the written base down to the owner root (or the variable itself) of the
written cell.
-/
theorem writeGuarded_of_resolution {store : ProgramStore} {env : Env}
    {current : Lifetime} {φ : Name → Nat} {rhsTy : Ty} {base₀ : Name}
    {leaf : Location} {leafSlot : StoreSlot} {leafView : PartialTy}
    {lv : LVal} {lvTy : Ty} {lifetime : Lifetime} {rank : Nat}
    {result : Env} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    store.slotAt leaf = some leafSlot →
    ValidPartialValue store leafSlot.value leafView →
    LValTyping env lv (.ty lvTy) lifetime →
    store.loc lv = some leaf →
    EnvWrite rank env lv rhsTy result →
    WriteGuarded store env leaf base₀ (LVal.base lv) →
    ∃ r, ProtectedByBase store r leaf ∧ WriteGuarded store env leaf base₀ r := by
  intro hφ hwellFormed hsafe hvalidStore hheap hleafSlot hleafValid htyping
    hloc hwrite hGbase
  exact go hφ hwellFormed hsafe hvalidStore hheap hleafSlot hleafValid htyping
    hloc hwrite hGbase
where
  go {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
      {rhsTy : Ty} {base₀ : Name} {leaf : Location} {leafSlot : StoreSlot}
      {leafView : PartialTy} {lv : LVal} {lvTy : Ty} {lifetime : Lifetime}
      {rank : Nat} {result : Env}
      (hφ : LinearizedBy φ env) (hwellFormed : WellFormedEnv env current)
      (hsafe : store ∼ₛ env) (hvalidStore : ValidStore store)
      (hheap : StoreOwnerTargetsHeap store)
      (hleafSlot : store.slotAt leaf = some leafSlot)
      (hleafValid : ValidPartialValue store leafSlot.value leafView)
      (htyping : LValTyping env lv (.ty lvTy) lifetime)
      (hloc : store.loc lv = some leaf)
      (hwrite : EnvWrite rank env lv rhsTy result)
      (hGbase : WriteGuarded store env leaf base₀ (LVal.base lv)) :
      ∃ r, ProtectedByBase store r leaf ∧
        WriteGuarded store env leaf base₀ r := by
    cases lv with
    | var b =>
        have hleafEq : leaf = VariableProjection b := by
          simp [ProgramStore.loc] at hloc
          exact hloc.symm
        exact ⟨b, Or.inl hleafEq, hGbase⟩
    | deref u =>
        cases htyping with
        | @box _ _ sourceLifetime hsource =>
            rcases StoreOwnerSpine.of_lvalTyping_box hwellFormed hsafe
                hsource with
              ⟨envSlot, rootSlot, sourceLocation, sourceSlot, henvBase,
                hrootSlot, hrootLifetime, hsourceLoc, hsourceSlot,
                hsourceSpine⟩
            have hsourceValid := StoreOwnerSpine.leaf_valid hsourceSpine
            rcases sourceSlot with ⟨sourceValue, sourceLifetime'⟩
            cases hsourceValid with
            | @box owned ownedSlot _ hownedSlot hinnerValid =>
                have hderefLoc :
                    store.loc (.deref u) = some owned := by
                  simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                have hleafEq : leaf = owned :=
                  Option.some.inj (hloc.symm.trans hderefLoc)
                have hsnoc :=
                  StoreOwnerSpine.snoc_box hsourceSpine rfl rfl hownedSlot
                    hinnerValid
                rw [← hleafEq] at hsnoc
                exact ⟨LVal.base u,
                  Or.inr (StoreOwnerSpine.ownsTransitively_of_nonempty hsnoc
                    (by simp)),
                  hGbase⟩
        | @borrow _ mutable targets borrowLifetime targetLifetime targetTy
            hsource htargets =>
            have hkill : SlotDepKill store env leaf (LVal.base u) :=
              slotDepKill_of_firstNode hφ hwellFormed hsafe hvalidStore hheap
                hsource (LValTyping.borrow hsource htargets) hloc hleafSlot
                hleafValid
            rcases firstNodePack hwellFormed hsafe hsource hloc with
              ⟨envSlot, rootValue, cell, cellSlot, L, m, ts, spinePath,
                suffix, u₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
            cases hwrite with
            | @intro _rank _env₁ writeEnv _writeLv writeSlot _ty updatedTy
                hwriteSlot hupdate =>
                have hwriteSlotEq : writeSlot = envSlot := by
                  have hwriteSlotBase :
                      env.slotAt (LVal.base u) = some writeSlot := by
                    simpa [LVal.base] using hwriteSlot
                  exact Option.some.inj (hwriteSlotBase.symm.trans h1)
                have hpathEq :
                    LVal.path (.deref u) = spinePath ++ (() :: suffix) := by
                  rw [h7]
                  simp [path_prependPath, ← h9, LVal.path]
                have hupdate' :
                    UpdateAtPath rank env (spinePath ++ (() :: suffix))
                      envSlot.ty rhsTy writeEnv updatedTy := by
                  rw [← hpathEq, ← hwriteSlotEq]
                  exact hupdate
                rcases StoreOwnerSpine.updateAtPath_node_fanout h6 rfl
                    hupdate' with
                  ⟨hmut, env₂, hfanout⟩
                subst hmut
                have hvalidCell := h5
                rw [h4] at hvalidCell
                cases hvalidCell with
                | @borrow _ _ _ tSel hmemSel hlocSel =>
                    have hcontains : PartialTyContains envSlot.ty
                        (.borrow true ts) :=
                      StoreOwnerSpine.contains_leafTy h6 rfl
                    have hGtarget :
                        WriteGuarded store env leaf base₀ (LVal.base tSel) :=
                      WriteGuarded.step hGbase ⟨envSlot, h1, hcontains⟩
                        hmemSel rfl hkill
                    rcases WriteBorrowTargets.selected_branch_to_result_exists
                        (Nat.succ_pos rank) hfanout
                        (WriteBorrowTargets.initialized_leaves_of_typed
                          hfanout)
                        hmemSel with
                      ⟨branchResult, hbranchWrite, _hbranchMap⟩
                    rcases WriteBorrowTargets.typed_of_mem hfanout tSel
                        hmemSel with
                      ⟨branchTy, branchLifetime, hbranchTyping⟩
                    have hbranchLoc :
                        store.loc (prependPath suffix tSel) = some leaf := by
                      have hcongr :=
                        ProgramStore.loc_congr_prependPath
                          (hlocSel.trans h8.symm) suffix
                      rw [hcongr, ← h7]
                      exact hloc
                    have hcallRank :
                        φ (LVal.base tSel) < φ (LVal.base u) :=
                      hφ (LVal.base u) envSlot h1 (LVal.base tSel)
                        (mem_partialTy_vars_iff.mpr
                          ⟨true, ts, tSel, hcontains, hmemSel, rfl⟩)
                    have hres :=
                      go hφ hwellFormed hsafe hvalidStore hheap hleafSlot
                        hleafValid hbranchTyping hbranchLoc hbranchWrite
                        (by simpa [base_prependPath] using hGtarget)
                    exact hres
  termination_by (φ (LVal.base lv), sizeOf lv)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [LVal.base, base_prependPath]
      first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by assumption)

/-! ### Strong spine updates (Appendix 9.6 deref-assign support) -/

/-- Replace the leaf of a box spine after `path` dereferences by `.ty ty`. -/
def PartialTy.strongLeafUpdate : PartialTy → List Unit → Ty → PartialTy
  | _, [], ty => .ty ty
  | .box inner, _ :: path, ty => .box (PartialTy.strongLeafUpdate inner path ty)
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
            simpa [owningRef] using hvalueEq
          subst hownedEq
          rw [ih htail₂]

/-- Spine validity after strongly replacing the leaf contents: the rebuilt
`V-Box` chain types the root against the strongly updated spine type. -/
theorem StoreOwnerSpine.valid_after_leaf_strong_update_box
    {store : ProgramStore} {value : Value} {rhsTy : Ty} {newSlot : StoreSlot}
    (hnewValue : newSlot.value = .value value) :
    ∀ {path : Path} {storage leaf : Location} {slot leafSlot : StoreSlot}
      {inner leafTy : PartialTy},
      StoreOwnerSpine store storage slot (.box inner) (() :: path) leaf
        leafSlot leafTy →
      ValidPartialValue (store.update leaf newSlot) (.value value)
        (.ty rhsTy) →
      ValidPartialValue (store.update leaf newSlot) slot.value
        (.box (PartialTy.strongLeafUpdate inner path rhsTy)) := by
  intro path
  induction path with
  | nil =>
      intro storage leaf slot leafSlot inner leafTy hspine hnewValid
      cases hspine with
      | box hslot howner htail =>
          rename_i owned ownedSlot
          cases htail with
          | nil hleafSlot _hleafValid =>
              rw [howner]
              have hnewSlotAt :
                  (store.update leaf newSlot).slotAt leaf = some newSlot := by
                simp [ProgramStore.update]
              refine ValidPartialValue.box hnewSlotAt ?_
              rw [hnewValue]
              simpa [PartialTy.strongLeafUpdate] using hnewValid
  | cons head rest ih =>
      cases head
      intro storage leaf slot leafSlot inner leafTy hspine hnewValid
      cases hspine with
      | box hslot howner htail =>
          rename_i owned ownedSlot
          cases htail with
          | box hslot₂ howner₂ htail₂ =>
              rename_i owned₂ ownedSlot₂ inner₂
              rw [howner]
              have hinnerSpine :
                  StoreOwnerSpine store owned ownedSlot (.box inner₂)
                    (() :: rest) leaf leafSlot leafTy :=
                StoreOwnerSpine.box hslot₂ howner₂ htail₂
              have hleafNeOwned : leaf ≠ owned :=
                StoreOwnerSpine.leaf_ne_storage_of_cons hinnerSpine
              have hownedNeLeaf : owned ≠ leaf := fun h => hleafNeOwned h.symm
              have hownedSlotAt :
                  (store.update leaf newSlot).slotAt owned =
                    some ownedSlot := by
                rw [RuntimeFrame.ProgramStore.slotAt_update_ne hownedNeLeaf]
                exact hslot₂
              have hinnerValid := ih hinnerSpine hnewValid
              simpa [PartialTy.strongLeafUpdate, owningRef] using
                ValidPartialValue.box hownedSlotAt hinnerValid

/-- General-type wrapper for `valid_after_leaf_strong_update_box`. -/
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
  cases hspine with
  | nil _hslot _hvalid =>
      exact absurd rfl hpath
  | box hslot howner htail =>
      have hres :=
        StoreOwnerSpine.valid_after_leaf_strong_update_box hnewValue
          (StoreOwnerSpine.box hslot howner htail) hnewValid
      simpa [PartialTy.strongLeafUpdate] using hres

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
          · simpa [PartialTy.strongLeafUpdate] using
              PartialTyStrengthens.box hstr
          · simpa [PartialTy.strongLeafUpdate, PartialTy.sameShape] using
              hshape

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
    store ∼ₛ env →
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
      (hsafe : store ∼ₛ env) (htyping : LValTyping env lv (.ty lvTy) lifetime)
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
    WellFormedEnv env₂ lifetime :=
  borrowInvariance_of_ruleCarriedObligations
    hrefs hvalid hstoreTyping hwellFormed hsafe htyping

end LwRust.Paper.Soundness
