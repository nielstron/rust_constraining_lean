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

theorem LValTyping.containedBorrowTargetsWellFormed {env : Env} {lv : LVal}
    {partialTy : PartialTy} {mutable : Bool} {targets : List LVal}
    {valueLifetime lifetime : Lifetime} :
    WellFormedEnv env lifetime →
    LValTyping env lv partialTy valueLifetime →
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormed env targets lifetime := by
  intro hwellFormed htyping hcontainsTop
  exact LValTyping.rec
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
  exact LValTyping.rec
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
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget, _hvar⟩
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
            ⟨targetTy, targetLifetime, htargetTyping, houtlives, hbaseTarget, _hvar⟩
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
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase, hvar⟩
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
  exact ⟨⟨baseSlot, hbaseSlot', hbaseOutlives⟩, hvar⟩

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
    ⟨targetTy, targetLifetime, htyping, houtlives, hbase, hvar⟩
  exact ⟨targetTy, targetLifetime,
    (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
      htyping (hnotTargets target htarget),
    houtlives,
    LValBaseOutlives.move_of_not_pathConflicts
      hmove (hnotTargets target htarget) hbase,
    hvar⟩

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
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase, hvar⟩
      exact ⟨targetTy, targetLifetime,
        (LValTyping.move_of_not_pathConflicts hmove hnotWrite).1
          htyping (hnotTargets target htarget),
        houtlives,
        LValBaseOutlives.move_of_not_pathConflicts
          hmove (hnotTargets target htarget) hbase,
        hvar⟩

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
    ⟨leftTy, leftLf, hleftTyping, _hleftOutlives, hleftBase, hleftVar⟩
  have hjoinBase := LValBaseOutlives.join_left hjoin hleftBase
  rcases fullJoinTransport_viaInvariants (N := φ (LVal.base target) + 1)
      hstrL hφJoin hcohJoin
      (fun x' slot' m' T' _ hslot' hcont' => hcontJoin x' slot' m' T' hslot' hcont')
      (Nat.lt_succ_self _) hleftTyping hjoinBase
    with ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLf, hjoinTyping, hjoinOutlives, hjoinBase, hleftVar⟩

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
    ⟨leftTy, leftLifetime, hleftTyping, hleftOutlives, hleftBase, hleftVar⟩
  rcases hright target htarget with
    ⟨rightTy, rightLifetime, hrightTyping, hrightOutlives, _hrightBase, _hrightVar⟩
  rcases htransport.full hjoin hleftContained hrightContained
      hleftInRight hrightInLeft hleftTyping hrightTyping
      hleftOutlives hrightOutlives with
    ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives⟩
  exact ⟨joinTy, joinLifetime, hjoinTyping, hjoinOutlives,
    LValBaseOutlives.join_left hjoin hleftBase, hleftVar⟩

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
    ⟨sourceTy, sourceLifetime, hsourceTyping, hsourceOutlives, hsourceBase, hsourceVar⟩
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
  exact ⟨resultTy, resultLifetime, hresultTyping, hresultOutlives, hresultBase, hsourceVar⟩

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
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget, _hvar⟩
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
                  ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbaseTarget, _hvar⟩
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
        ⟨targetTy, selectedLifetime, htargetTyping, htargetOutlives, hbase, _hvar⟩
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
    ⟨targetTy, targetLifetime, htyping, htargetOutlivesSlot, hbase, hvar⟩
  have hbaseParent : LValBaseOutlives env target parent := by
    rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
    exact ⟨baseSlot, hbaseSlot,
      LifetimeOutlives.trans hbaseOutlives hslotParent⟩
  refine ⟨targetTy, targetLifetime,
    htransport hbaseParent htyping
      (LifetimeOutlives.trans htargetOutlivesSlot hslotParent),
    htargetOutlivesSlot, ?_⟩
  exact ⟨LValBaseOutlives.dropLifetime_child hchild hslotParent hbase, hvar⟩

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
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase, hvar⟩
      have hbaseParent : LValBaseOutlives env target parent := by
        rcases hbase with ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
        exact ⟨baseSlot, hbaseSlot, hbaseOutlives⟩
      refine ⟨targetTy, targetLifetime,
        htransport hbaseParent htyping houtlives, houtlives, ?_⟩
      exact ⟨
        LValBaseOutlives.dropLifetime_child hchild
          (LifetimeOutlives.refl parent) hbase,
        hvar⟩

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
        ⟨_, _, _, _, hb, _hvar⟩
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
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv _hvar hnotWrite hmove
        _htypingEq hwellFormed =>
      hlandmarks.move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv hvar _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv)
            hvar)⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv hvar _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv)
            hvar)⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy _hdropSafe hdrop ih htypingEq hwellFormed =>
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
          _hterm _hnonOwner _hrest ihHead ihRest htypingEq hwellFormed =>
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
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty} hLv _hvar hnotWrite hmove
        _htypingEq hwellFormed =>
      move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv hvar _hmutable _hwrite
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv)
            hvar)⟩)
    (fun {_env _typing _lifetime _valueLifetime lv _ty} hLv hvar _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv)
            hvar)⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy _hdropSafe hdrop ih htypingEq hwellFormed =>
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
        _hterm _hnonOwner _hrest ihHead ihRest htypingEq hwellFormed =>
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

theorem RuntimeFrame.reachesSlot_of_reaches {store : ProgramStore}
    {env : Env} {slotLifetime : Lifetime}
    {value : PartialValue} {ty : PartialTy} {location : Location} :
    PartialTyBorrowsWellFormedInSlot env slotLifetime ty →
    ValidPartialValue store value ty →
    RuntimeFrame.Reaches store value ty location →
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
      cases hreach with
      | @borrow _borrowedLocation readLocation _mutable _targets target' hmem' _hloc' hreads =>
          rcases hborrows PartialTyContains.here target' hmem' with
            ⟨_targetTy, _targetLifetime, _htyping, _houtlives, _hbase,
              hvar⟩
          exact False.elim (RuntimeFrame.locReads_varTarget_false hvar hreads)
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

/--
Well-formed borrow targets are variable lvalues, so a borrowed reference whose
type is well-formed never reaches a variable slot through target resolution.
Owning references may reach heap slots; those are also disjoint from variables.
-/
theorem RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
    {store : ProgramStore} {env : Env} {slotLifetime : Lifetime}
    {partialValue : PartialValue} {partialTy : PartialTy}
    {location : Location} {x : Name} :
    StoreOwnerTargetsHeap store →
    PartialValueOwnerTargetsHeap partialValue →
    PartialTyBorrowsWellFormedInSlot env slotLifetime partialTy →
    RuntimeFrame.Reaches store partialValue partialTy location →
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
  | @borrow borrowedLocation readLocation mutable targets target hmem _hloc hreads =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨_targetTy, _targetLifetime, _htyping, _houtlives, _hbase, hvar⟩
      exact False.elim (RuntimeFrame.locReads_varTarget_false hvar hreads)

/-- Full-value specialization of `reaches_ne_var_of_wellFormed_borrows`. -/
theorem RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
    {store : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value : Value} {ty : Ty} {location : Location} {x : Name} :
    StoreOwnerTargetsHeap store →
    ValueOwnerTargetsHeap value →
    WellFormedTy env ty lifetime →
    RuntimeFrame.Reaches store (.value value) (.ty ty) location →
    location ≠ VariableProjection x := by
  intro hstoreHeap hvalueHeap hwellTy hreach
  exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows hstoreHeap
    (ValueOwnerTargetsHeap.partial hvalueHeap)
    (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)
    hreach

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
                    (.value (owningRef owned)) (.box updatedInner) :=
                ValidPartialValue.box hownedSlotWrite htailValid
              simpa [howner] using hbox

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
      RuntimeFrame.Reaches store (.value value) (.ty rhsTy) reached →
      reached ≠ root) →
    ∀ reached,
      RuntimeFrame.Reaches store (.value value) (.ty rhsTy) reached →
      reached ≠ leaf := by
  intro hvalidRuntime hborrows hvalidValue hspine
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
            RuntimeFrame.Reaches store (.value value) (.ty rhsTy) reached →
            reached ≠ owned := by
        intro reached hreach hreached
        subst reached
        rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
            hborrows hvalidValue hreach with hdirect | hsource
        · exact
            (ValidRuntimeState.storeTermDisjoint hvalidRuntime owned
              (by
                simpa [termOwningLocations, termValues,
                  partialValueOwningLocations, valueOwningLocations,
                  valueOwnedLocation?] using hdirect))
              ⟨storage, howns⟩
        · rcases hsource with ⟨sourceStorage, hsourceReach, hsourceOwns⟩
          have hstorageEq : sourceStorage = storage :=
            (ValidRuntimeState.validStore hvalidRuntime) owned
              sourceStorage storage hsourceOwns howns
          exact hstorageNoReach sourceStorage hsourceReach hstorageEq
      exact ih hownedNoReach

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
      RuntimeFrame.Reaches store storedValue storedTy reached →
      reached ≠ root) →
    ∀ reached,
      RuntimeFrame.Reaches store storedValue storedTy reached →
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
            RuntimeFrame.Reaches store storedValue storedTy reached →
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
  | move hLv _hvar _hnotWrite _hmoveTyping =>
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
                (TermTyping.move (typing := typing) hLv (by trivial) _hnotWrite hmove)
                (Step.move (lifetime := lifetime) hread hwrite)
                (by
                  intro location hreach
                  have hvalueHeap : ValueOwnerTargetsHeap value :=
                    TermOwnerTargetsHeap.value
                      (termOwnerTargetsHeap_value_of_store_read
                        (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hread)
                  exact RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hvalueHeap
                    (LValTyping.fullTyWellFormed hwellFormed hLv)
                    hreach)
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
                  exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hvalueHeap hborrows hreach))
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
    ValidValue store value rhsTy →
    Step store lifetime (.assign (.var x) (.val value)) store' (.val finalValue) →
    TerminalStateSafe store' finalValue env' .unit := by
  intro hwellFormed hsafe hvalidRuntime hLhs hshape hwellTy hwrite hvalidValue hstep
  rcases LValTyping.var_inv hLhs with ⟨envSlot, henvSlot, htyEq, _hlifetimeEq⟩
  cases hstep with
  | assign hread hwriteStoreWritten hdrops =>
      cases hshape with
      | unit =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
            (by left; exact htyEq)
            hvalidValue hread hwriteStoreWritten hdrops
            (by
              intro location hreach
              have hvalueHeap : ValueOwnerTargetsHeap value :=
                TermOwnerTargetsHeap.value
                  (termOwnerTargetsHeap_assign_inner
                    (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
              exact RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hvalueHeap hwellTy hreach)
            (by
              intro y otherEnvSlot oldValue hyx henvY hstoreY location hreach
              have hvalueHeap : PartialValueOwnerTargetsHeap oldValue :=
                partialValueOwnerTargetsHeap_of_slot
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreY
              have hborrows :
                  PartialTyBorrowsWellFormedInSlot env otherEnvSlot.lifetime
                    otherEnvSlot.ty := by
                intro mutable targets hcontains
                exact hwellFormed.1 y otherEnvSlot mutable targets henvY
                  ⟨otherEnvSlot, henvY, hcontains⟩
              exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hvalueHeap hborrows hreach)
      | int =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
            (by right; left; exact htyEq)
            hvalidValue hread hwriteStoreWritten hdrops
            (by
              intro location hreach
              have hvalueHeap : ValueOwnerTargetsHeap value :=
                TermOwnerTargetsHeap.value
                  (termOwnerTargetsHeap_assign_inner
                    (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
              exact RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hvalueHeap hwellTy hreach)
            (by
              intro y otherEnvSlot oldValue hyx henvY hstoreY location hreach
              have hvalueHeap : PartialValueOwnerTargetsHeap oldValue :=
                partialValueOwnerTargetsHeap_of_slot
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreY
              have hborrows :
                  PartialTyBorrowsWellFormedInSlot env otherEnvSlot.lifetime
                    otherEnvSlot.ty := by
                intro mutable targets hcontains
                exact hwellFormed.1 y otherEnvSlot mutable targets henvY
                  ⟨otherEnvSlot, henvY, hcontains⟩
              exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hvalueHeap hborrows hreach)
      | borrow hleft hright hinner =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
            (by right; right; right; exact ⟨_, _, htyEq⟩)
            hvalidValue hread hwriteStoreWritten hdrops
            (by
              intro location hreach
              have hvalueHeap : ValueOwnerTargetsHeap value :=
                TermOwnerTargetsHeap.value
                  (termOwnerTargetsHeap_assign_inner
                    (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
              exact RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hvalueHeap hwellTy hreach)
            (by
              intro y otherEnvSlot oldValue hyx henvY hstoreY location hreach
              have hvalueHeap : PartialValueOwnerTargetsHeap oldValue :=
                partialValueOwnerTargetsHeap_of_slot
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreY
              have hborrows :
                  PartialTyBorrowsWellFormedInSlot env otherEnvSlot.lifetime
                    otherEnvSlot.ty := by
                intro mutable targets hcontains
                exact hwellFormed.1 y otherEnvSlot mutable targets henvY
                  ⟨otherEnvSlot, henvY, hcontains⟩
              exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hvalueHeap hborrows hreach)
      | undefLeft hinner =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
            (by right; right; left; exact ⟨_, htyEq⟩)
            hvalidValue hread hwriteStoreWritten hdrops
            (by
              intro location hreach
              have hvalueHeap : ValueOwnerTargetsHeap value :=
                TermOwnerTargetsHeap.value
                  (termOwnerTargetsHeap_assign_inner
                    (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
              exact RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hvalueHeap hwellTy hreach)
            (by
              intro y otherEnvSlot oldValue hyx henvY hstoreY location hreach
              have hvalueHeap : PartialValueOwnerTargetsHeap oldValue :=
                partialValueOwnerTargetsHeap_of_slot
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime) hstoreY
              have hborrows :
                  PartialTyBorrowsWellFormedInSlot env otherEnvSlot.lifetime
                    otherEnvSlot.ty := by
                intro mutable targets hcontains
                exact hwellFormed.1 y otherEnvSlot mutable targets henvY
                  ⟨otherEnvSlot, henvY, hcontains⟩
              exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                hvalueHeap hborrows hreach)
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
                    exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                      hvalueHeap
                      (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellInner)
                      hreach)
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
                    RuntimeFrame.Reaches writtenStore
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
                      hnewGraphDisjoint hreach)
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
                    (RuntimeFrame.Reaches.boxFullHere hnewRootSlotWrite)
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
                  hnewValidFinal rfl ?domain ?preserve
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
                        have hvalueHeap : PartialValueOwnerTargetsHeap oldValue :=
                          partialValueOwnerTargetsHeap_of_slot
                            (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                            hslotY
                        have hborrows :
                            PartialTyBorrowsWellFormedInSlot env
                              otherEnvSlot.lifetime otherEnvSlot.ty := by
                          intro mutable targets hcontains
                          exact hwellFormed.1 y otherEnvSlot mutable targets henvY
                            ⟨otherEnvSlot, henvY, hcontains⟩
                        exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                          (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                          hvalueHeap hborrows hreach)
                  have holdGraphDisjoint :
                      ∀ reached,
                        RuntimeFrame.Reaches writtenStore oldValue
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
                          hvalidOldWrite havoidY holdGraphDisjoint hreach)
                  exact ⟨oldValue,
                    dropsAvoids_slotAt_preserved hdrops havoidY hslotYWrite,
                    hvalidOldFinal⟩
              exact ⟨hvalidRuntimeFinal, hsafeFinal, ValidPartialValue.unit⟩

/--
Singleton value block preservation for `R-BlockB` under the mechanized
block-local drop-safety condition carried by `T-Block`.
-/
theorem preservation_blockB_value_multistep_runtime_of_envDropSafe
    {store finalStore : ProgramStore} {env : Env}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    store ∼ₛ env →
    LifetimeChild lifetime blockLifetime →
    EnvLifetimeDropSafe env blockLifetime →
    WellFormedEnv env blockLifetime →
    WellFormedTy env ty lifetime →
    ValidValue store value ty →
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue (env.dropLifetime blockLifetime) ty := by
  intro hvalidRuntime hsafe hchild hdropSafe hwellBody hwellTy hvalidValue hmulti
  exact preservation_runtime_multistep_of_step_to_value
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
      | blockB hdrops =>
          have hresultValue : ValidValue store' value ty :=
            validPartialValue_dropsLifetime_of_envDropSafe
              hsafe hdropSafe
              (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime)
              hchild hvalidValue
              (by
                intro location hreach x
                have hvalueHeap : ValueOwnerTargetsHeap value :=
                  TermOwnerTargetsHeap.value
                    (termOwnerTargetsHeap_block_value
                      (ValidRuntimeState.termOwnerTargetsHeap hvalidRuntime))
                exact RuntimeFrame.value_reaches_ne_var_of_wellFormedTy
                  (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                  hvalueHeap hwellTy hreach)
              hdrops
          have hpreserve :
              ∀ x envSlot,
                env.slotAt x = some envSlot →
                envSlot.lifetime ≠ blockLifetime →
                ∃ oldValue,
                  store'.slotAt (VariableProjection x) =
                    some { value := oldValue, lifetime := envSlot.lifetime } ∧
                  ValidPartialValue store' oldValue envSlot.ty := by
            intro x envSlot henvSlot hsurvives
            rcases hsafe.2 x envSlot henvSlot with
              ⟨oldValue, hstoreSlot, hvalidOld⟩
            have hvalidOld' : ValidPartialValue store' oldValue envSlot.ty :=
              validPartialValue_dropsLifetime_of_envDropSafe
                hsafe hdropSafe
                (ValidRuntimeState.heapSlotsRootLifetime hvalidRuntime)
                hchild hvalidOld
                (by
                  intro location hreach y
                  have hvalueHeap : PartialValueOwnerTargetsHeap oldValue :=
                    partialValueOwnerTargetsHeap_of_slot
                      (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                      hstoreSlot
                  have hborrows :
                      PartialTyBorrowsWellFormedInSlot env envSlot.lifetime
                        envSlot.ty := by
                    intro mutable targets hcontains
                    exact hwellBody.1 x envSlot mutable targets henvSlot
                      ⟨envSlot, henvSlot, hcontains⟩
                  exact RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                    (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                    hvalueHeap hborrows hreach)
                hdrops
            have hstoreSlot' :
                store'.slotAt (VariableProjection x) =
                  some { value := oldValue, lifetime := envSlot.lifetime } :=
              dropsLifetime_preserves_var_slot_of_not_lifetime hdrops
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime)
                (by simpa [VariableProjection] using hstoreSlot)
                hsurvives
            exact ⟨oldValue, hstoreSlot', hvalidOld'⟩
          have hsafeDrop : store' ∼ₛ env.dropLifetime blockLifetime :=
            dropPreservation_lifetime hsafe hdrops
              (dropLifetime_domain_equiv_of_ownerTargetsHeap hsafe hdrops
                (ValidRuntimeState.storeOwnerTargetsHeap hvalidRuntime))
              hpreserve
          exact ⟨validRuntimeState_blockB_step_of_child hvalidRuntime hchild
              (Step.blockB (lifetime := lifetime) hdrops),
            hsafeDrop, hresultValue⟩)
    hmulti

/--
Lemma 4.11, Preservation.

This is stated over `ValidRuntimeState`, the mechanised package that contains
Definition 4.3's valid-state condition plus the explicit owner-allocation
invariant needed by our concrete store model.
-/
theorem preservation {store finalStore : ProgramStore} {env₁ env₂ : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {ty : Ty} {finalValue : Value} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
    SourceTerm term →
    ValidRuntimeState store term →
    ValidStoreTyping store term typing →
    WellFormedEnv env₁ lifetime →
    store ∼ₛ env₁ →
    TermTyping env₁ typing lifetime term ty env₂ →
    MultiStep store lifetime term finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hrefs hsource hvalidRuntime hvalidStoreTyping hwellFormed hsafe htyping hmulti
  exact (TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      SourceTerm term →
      ∀ (store finalStore : ProgramStore) (finalValue : Value),
        ValidRuntimeState store term →
        ValidStoreTyping store term currentTyping →
        WellFormedEnv env lifetime →
        store ∼ₛ env →
        MultiStep store lifetime term finalStore (.val finalValue) →
        WellFormedEnv env₂ lifetime ∧
          TerminalStateSafe finalStore finalValue env₂ ty)
    (motive_2 := fun env currentTyping blockLifetime terms ty env₂ _ =>
      currentTyping = typing →
      SourceTerm (.block blockLifetime terms) →
      ∀ (outerLifetime : Lifetime) (store finalStore : ProgramStore)
        (finalValue : Value),
        LifetimeChild outerLifetime blockLifetime →
        ValidRuntimeState store (.block blockLifetime terms) →
        ValidStoreTyping store (.block blockLifetime terms) currentTyping →
        WellFormedEnv env blockLifetime →
        store ∼ₛ env →
        EnvLifetimeDropSafe env₂ blockLifetime →
        WellFormedTy env₂ ty outerLifetime →
        MultiStep store outerLifetime (.block blockLifetime terms)
          finalStore (.val finalValue) →
        TerminalStateSafe finalStore finalValue
          (env₂.dropLifetime blockLifetime) ty)
    (fun {_env _typing _lifetime _value _ty}
        (hvalueTyping : ValueTyping _typing _value _ty)
        (htypingEq : _typing = typing) (_hsource : SourceTerm (.val _value))
        (store finalStore : ProgramStore)
        (finalValue : Value)
        (hvalidRuntime : ValidRuntimeState store (.val _value))
        (hvalidStoreTyping : ValidStoreTyping store (.val _value) _typing)
        (hwellFormed : WellFormedEnv _env _lifetime)
        (hsafe : store ∼ₛ _env)
        (hmulti : MultiStep store _lifetime (.val _value) finalStore (.val finalValue)) =>
      show WellFormedEnv _env _lifetime ∧
          TerminalStateSafe finalStore finalValue _env _ty from by
      cases htypingEq
      have htermTyping : TermTyping _env typing _lifetime (.val _value) _ty _env :=
        TermTyping.const hvalueTyping
      have hterminal : TerminalStateSafe finalStore finalValue _env _ty :=
        preservation_multistep_runtime_value hvalidRuntime hvalidStoreTyping hsafe
          htermTyping hmulti
      exact And.intro hwellFormed hterminal)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty}
        (hLv : LValTyping _env _lv (.ty _ty) _valueLifetime)
        (hcopy : CopyTy _ty) (hnotRead : ¬ ReadProhibited _env _lv)
        (htypingEq : _typing = typing) (_hsource : SourceTerm (.copy _lv))
        (store finalStore : ProgramStore)
        (finalValue : Value)
        (hvalidRuntime : ValidRuntimeState store (.copy _lv))
        (hvalidStoreTyping : ValidStoreTyping store (.copy _lv) _typing)
        (hwellFormed : WellFormedEnv _env _lifetime)
        (hsafe : store ∼ₛ _env)
        (hmulti : MultiStep store _lifetime (.copy _lv) finalStore (.val finalValue)) =>
      show WellFormedEnv _env _lifetime ∧
          TerminalStateSafe finalStore finalValue _env _ty from by
      cases htypingEq
      have htermTyping : TermTyping _env typing _lifetime (.copy _lv) _ty _env :=
        TermTyping.copy hLv hcopy hnotRead
      have hterminal : TerminalStateSafe finalStore finalValue _env _ty :=
        preservation_copy_multistep_runtime hwellFormed hsafe hvalidRuntime
          htermTyping hmulti
      exact And.intro hwellFormed hterminal)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
        (hLv : LValTyping _env₁ _lv (.ty _ty) _valueLifetime)
        (hvar : LValIsVar _lv) (hnotWrite : ¬ WriteProhibited _env₁ _lv)
        (hmove : EnvMove _env₁ _lv _env₂)
        (htypingEq : _typing = typing) (_hsource : SourceTerm (.move _lv))
        (store finalStore : ProgramStore)
        (finalValue : Value)
        (hvalidRuntime : ValidRuntimeState store (.move _lv))
        (hvalidStoreTyping : ValidStoreTyping store (.move _lv) _typing)
        (hwellFormed : WellFormedEnv _env₁ _lifetime)
        (hsafe : store ∼ₛ _env₁)
        (hmulti : MultiStep store _lifetime (.move _lv) finalStore (.val finalValue)) =>
      show WellFormedEnv _env₂ _lifetime ∧
          TerminalStateSafe finalStore finalValue _env₂ _ty from by
      cases htypingEq
      have htermTyping : TermTyping _env₁ typing _lifetime (.move _lv) _ty _env₂ :=
        TermTyping.move hLv hvar hnotWrite hmove
      have hwellOut : WellFormedEnv _env₂ _lifetime :=
        (move_preserves_wellFormed hwellFormed hLv hnotWrite hmove).1
      have hterminal : TerminalStateSafe finalStore finalValue _env₂ _ty :=
        by
          cases _lv with
          | var x =>
              rcases LValTyping.var_inv hLv with ⟨slot, hslot, htyEq, hlifetimeEq⟩
              cases slot with
              | mk slotTy slotLifetime =>
                  cases htyEq
                  cases hlifetimeEq
                  exact preservation_move_var_multistep_runtime_of_wellFormed
                    hwellFormed hsafe hvalidRuntime hslot hmove htermTyping hmulti
          | deref lv =>
              exact False.elim hvar
      exact And.intro hwellOut hterminal)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty}
        (hLv : LValTyping _env _lv (.ty _ty) _valueLifetime)
        (hvar : LValIsVar _lv) (hmutable : Mutable _env _lv)
        (hnotWrite : ¬ WriteProhibited _env _lv)
        (htypingEq : _typing = typing) (_hsource : SourceTerm (.borrow true _lv))
        (store finalStore : ProgramStore)
        (finalValue : Value)
        (hvalidRuntime : ValidRuntimeState store (.borrow true _lv))
        (_hvalidStoreTyping : ValidStoreTyping store (.borrow true _lv) _typing)
        (_hwellFormed : WellFormedEnv _env _lifetime)
        (hsafe : store ∼ₛ _env)
        (hmulti : MultiStep store _lifetime (.borrow true _lv) finalStore (.val finalValue)) =>
      show WellFormedEnv _env _lifetime ∧
          TerminalStateSafe finalStore finalValue _env (.borrow true [_lv]) from by
      cases htypingEq
      have htermTyping :
          TermTyping _env typing _lifetime (.borrow true _lv) (.borrow true [_lv]) _env :=
        TermTyping.mutBorrow hLv hvar hmutable hnotWrite
      have hterminal : TerminalStateSafe finalStore finalValue _env (.borrow true [_lv]) :=
        preservation_borrow_multistep_runtime hsafe hvalidRuntime htermTyping hmulti
      exact And.intro _hwellFormed hterminal)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty}
        (hLv : LValTyping _env _lv (.ty _ty) _valueLifetime)
        (hvar : LValIsVar _lv) (hnotRead : ¬ ReadProhibited _env _lv)
        (htypingEq : _typing = typing) (_hsource : SourceTerm (.borrow false _lv))
        (store finalStore : ProgramStore)
        (finalValue : Value)
        (hvalidRuntime : ValidRuntimeState store (.borrow false _lv))
        (_hvalidStoreTyping : ValidStoreTyping store (.borrow false _lv) _typing)
        (_hwellFormed : WellFormedEnv _env _lifetime)
        (hsafe : store ∼ₛ _env)
        (hmulti : MultiStep store _lifetime (.borrow false _lv) finalStore (.val finalValue)) =>
      show WellFormedEnv _env _lifetime ∧
          TerminalStateSafe finalStore finalValue _env (.borrow false [_lv]) from by
      cases htypingEq
      have htermTyping :
          TermTyping _env typing _lifetime (.borrow false _lv) (.borrow false [_lv]) _env :=
        TermTyping.immBorrow hLv hvar hnotRead
      have hterminal : TerminalStateSafe finalStore finalValue _env (.borrow false [_lv]) :=
        preservation_borrow_multistep_runtime hsafe hvalidRuntime htermTyping hmulti
      exact And.intro _hwellFormed hterminal)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty}
        (hterm : TermTyping _env₁ _typing _lifetime _term _ty _env₂)
        (ih : _typing = typing →
          SourceTerm _term →
          ∀ (store finalStore : ProgramStore) (finalValue : Value),
            ValidRuntimeState store _term →
            ValidStoreTyping store _term _typing →
            WellFormedEnv _env₁ _lifetime →
            store ∼ₛ _env₁ →
            MultiStep store _lifetime _term finalStore (.val finalValue) →
            WellFormedEnv _env₂ _lifetime ∧
              TerminalStateSafe finalStore finalValue _env₂ _ty)
        (htypingEq : _typing = typing) (hsource : SourceTerm (.box _term))
        (store finalStore : ProgramStore)
        (finalValue : Value)
        (hvalidRuntime : ValidRuntimeState store (.box _term))
        (hvalidStoreTyping : ValidStoreTyping store (.box _term) _typing)
        (hwellFormed : WellFormedEnv _env₁ _lifetime)
        (hsafe : store ∼ₛ _env₁)
        (hmulti : MultiStep store _lifetime (.box _term) finalStore (.val finalValue)) =>
      show WellFormedEnv _env₂ _lifetime ∧
          TerminalStateSafe finalStore finalValue _env₂ (.box _ty) from by
      cases htypingEq
      have htermTyping : TermTyping _env₁ typing _lifetime (.box _term) (.box _ty) _env₂ :=
        TermTyping.box hterm
      have hterminal : TerminalStateSafe finalStore finalValue _env₂ (.box _ty) :=
        preservation_box_context_terminal_multistep_runtime
        (by
          intro midStore value hvalidInner hvalidStoreTypingInner hsafeInner
            _hinnerTyping hmultiInner
          exact (ih rfl (SourceTerm.box_inner hsource)
            store midStore value hvalidInner hvalidStoreTypingInner
            hwellFormed hsafeInner hmultiInner).2)
        hvalidRuntime hvalidStoreTyping hsafe htermTyping hmulti
      have hwellOut : WellFormedEnv _env₂ _lifetime :=
        (typingPreservesWellFormed_of_ruleCarriedObligations hrefs
          (ValidRuntimeState.validState hvalidRuntime)
          hvalidStoreTyping hwellFormed hsafe htermTyping).1
      exact And.intro hwellOut hterminal)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        (hblockChild : LifetimeChild _lifetime _blockLifetime)
        (hterms : TermListTyping _env₁ _typing _blockLifetime _terms _ty _env₂)
        (hwellTy : WellFormedTy _env₂ _ty _lifetime)
        (hdropSafe : EnvLifetimeDropSafe _env₂ _blockLifetime)
        (hdrop : _env₃ = _env₂.dropLifetime _blockLifetime)
        (ih : _typing = typing →
          SourceTerm (.block _blockLifetime _terms) →
          ∀ (outerLifetime : Lifetime) (store finalStore : ProgramStore)
            (finalValue : Value),
            LifetimeChild outerLifetime _blockLifetime →
            ValidRuntimeState store (.block _blockLifetime _terms) →
            ValidStoreTyping store (.block _blockLifetime _terms) _typing →
            WellFormedEnv _env₁ _blockLifetime →
            store ∼ₛ _env₁ →
            EnvLifetimeDropSafe _env₂ _blockLifetime →
            WellFormedTy _env₂ _ty outerLifetime →
            MultiStep store outerLifetime (.block _blockLifetime _terms)
              finalStore (.val finalValue) →
            TerminalStateSafe finalStore finalValue
              (_env₂.dropLifetime _blockLifetime) _ty)
        (htypingEq : _typing = typing)
        (hsource : SourceTerm (.block _blockLifetime _terms))
        (store finalStore : ProgramStore) (finalValue : Value)
        (hvalidRuntime : ValidRuntimeState store (.block _blockLifetime _terms))
        (hvalidStoreTyping : ValidStoreTyping store (.block _blockLifetime _terms) _typing)
        (hwellFormed : WellFormedEnv _env₁ _lifetime)
        (hsafe : store ∼ₛ _env₁)
        (hmulti : MultiStep store _lifetime (.block _blockLifetime _terms)
          finalStore (.val finalValue)) =>
      show WellFormedEnv _env₃ _lifetime ∧
          TerminalStateSafe finalStore finalValue _env₃ _ty from by
      cases htypingEq
      have htermTyping :
          TermTyping _env₁ typing _lifetime (.block _blockLifetime _terms) _ty _env₃ :=
        TermTyping.block hblockChild hterms hwellTy hdropSafe hdrop
      have hwellOut : WellFormedEnv _env₃ _lifetime :=
        (typingPreservesWellFormed_of_ruleCarriedObligations hrefs
          (ValidRuntimeState.validState hvalidRuntime)
          hvalidStoreTyping hwellFormed hsafe htermTyping).1
      have hterminal : TerminalStateSafe finalStore finalValue _env₃ _ty :=
        by
          subst hdrop
          exact ih rfl hsource _lifetime store finalStore finalValue hblockChild
            hvalidRuntime hvalidStoreTyping
            (WellFormedEnv.weaken hwellFormed
              (LifetimeChild.outlives hblockChild))
            hsafe hdropSafe hwellTy hmulti
      exact And.intro hwellOut hterminal)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        hfresh hterm hfreshOut _hcoh henv₃ ih
        (htypingEq : _typing = typing) (hsource : SourceTerm (.letMut _x _term))
        store finalStore finalValue hvalidRuntime
        hvalidStoreTyping hwellFormed hsafe hmulti =>
      by
        cases htypingEq
        rcases multistep_declare_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hdeclareStep⟩
        rcases ih rfl (SourceTerm.declare_inner hsource) store midStore value
            (validRuntimeState_declare_inner hvalidRuntime)
            (validStoreTyping_declare_inner hvalidStoreTyping)
            hwellFormed hsafe hinnerMulti with
          ⟨_hwellInner, hterminalInner⟩
        rcases hterminalInner with
          ⟨hvalidInner, hsafeInner, hvalidValue⟩
        cases hdeclareStep with
        | declare hstore =>
            have htermTyping := TermTyping.declare hfresh hterm hfreshOut _hcoh henv₃
            have hwellOut :=
              (typingPreservesWellFormed_of_ruleCarriedObligations hrefs
                (ValidRuntimeState.validState hvalidRuntime)
                hvalidStoreTyping hwellFormed hsafe htermTyping).1
            have hpreserved :=
              preservation_declare_redex_runtime_of_validValue hsafeInner
                hfreshOut
                (validRuntimeState_declare_value_of_value hvalidInner)
                hvalidValue
                (Step.declare (lifetime := _lifetime) hstore)
            have hterminal : TerminalStateSafe finalStore .unit _env₃ .unit := by
              rw [henv₃]
              exact hpreserved
            exact And.intro hwellOut hterminal)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy _rhs _rhsTy}
        hLhs hRhs hLhsPost hshape hwellTy hwrite hranked hcoh hcontained
        hnotWrite _ih
        (htypingEq : _typing = typing) (hsource : SourceTerm (.assign _lhs _rhs))
        store finalStore finalValue hvalidRuntime
        hvalidStoreTyping hwellFormed hsafe hmulti =>
      by
        cases htypingEq
        rcases multistep_assign_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hassignStep⟩
        rcases _ih rfl (SourceTerm.assign_inner hsource) store midStore value
            (validRuntimeState_assign_inner hvalidRuntime)
            (validStoreTyping_assign_inner hvalidStoreTyping)
            hwellFormed hsafe hinnerMulti with
          ⟨hwellInner, hterminalInner⟩
        rcases hterminalInner with
          ⟨hvalidInner, hsafeInner, hvalidValue⟩
        have htermTyping :=
          TermTyping.assign hLhs hRhs hLhsPost hshape hwellTy hwrite
            hranked hcoh hcontained hnotWrite
        have hwellOut :=
          (typingPreservesWellFormed_of_ruleCarriedObligations hrefs
            (ValidRuntimeState.validState hvalidRuntime)
            hvalidStoreTyping hwellFormed hsafe htermTyping).1
        have hterminal : TerminalStateSafe finalStore finalValue _env₃ .unit := by
          cases _lhs with
          | var x =>
              exact preservation_assign_var_step_runtime_of_wellFormed
                hwellInner hsafeInner
                (validRuntimeState_assign_value_of_value hvalidInner)
                hLhsPost hshape hwellTy hwrite hvalidValue hassignStep
          | deref lv =>
              cases hassignStep with
              | assign hread hwriteStore hdrops =>
                  rename_i writtenStore overwrittenSlot
                  rcases write_eq_update_of_read hread hwriteStore with
                    ⟨lhsLocation, hlhsLoc, hlhsSlot, hwriteStoreEq⟩
                  cases hLhsPost with
                  | box hsourceBox =>
                      cases hwrite with
                      | @intro _rank _writeEnv _writeMiddle _writeLv writeEnvSlot
                          _writeTy _updatedTy hbase hupdate =>
                          cases lv with
                          | var x =>
                              rcases LValTyping.var_inv hsourceBox with
                                ⟨sourceEnvSlot, henvX, hsourceTy, hsourceLifetime⟩
                              have hslotEq : writeEnvSlot = sourceEnvSlot := by
                                have hsome : some writeEnvSlot = some sourceEnvSlot := by
                                  rw [← hbase]
                                  simpa [LVal.base] using henvX
                                exact Option.some.inj hsome
                              subst hslotEq
                              rw [hsourceTy] at hupdate
                              cases hupdate with
                              | box hinnerUpdate =>
                                  cases hinnerUpdate with
                                  | strong =>
                                      rcases hsafeInner.2 x writeEnvSlot henvX with
                                        ⟨sourceValue, hstoreX, hvalidSource⟩
                                      rw [hsourceTy] at hvalidSource
                                      cases hvalidSource with
                                      | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
                                          have hstoreXVar :
                                              midStore.slotAt (Location.var x) =
                                                some
                                                  { value := PartialValue.value
                                                      (Value.ref
                                                        { location := ownerLocation,
                                                          owner := true }),
                                                    lifetime := writeEnvSlot.lifetime } := by
                                            simpa [VariableProjection] using hstoreX
                                          have hlhsLocFromX :
                                              midStore.loc (LVal.var x).deref =
                                                some ownerLocation := by
                                            simp [ProgramStore.loc, hstoreXVar]
                                          have hlocationEq : ownerLocation = lhsLocation := by
                                            rw [hlhsLoc] at hlhsLocFromX
                                            exact (Option.some.inj hlhsLocFromX).symm
                                          subst hlocationEq
                                          have hslotEqOld : ownerSlot = overwrittenSlot := by
                                            rw [hlhsSlot] at hownedSlot
                                            exact (Option.some.inj hownedSlot).symm
                                          subst hslotEqOld
                                          have hvalidAssign :
                                              ValidRuntimeState midStore
                                                (.assign (LVal.var x).deref
                                                  (.val value)) :=
                                            validRuntimeState_assign_value_of_value hvalidInner
                                          rw [hwriteStoreEq] at hdrops
                                          have hownsLhsByX :
                                              ProgramStore.OwnsAt midStore ownerLocation
                                                (VariableProjection x) :=
                                            ⟨writeEnvSlot.lifetime, hstoreX⟩
                                          have hownerHeap :
                                              ∃ address, ownerLocation = .heap address :=
                                            (ValidRuntimeState.storeOwnerTargetsHeap
                                              hvalidInner) ownerLocation
                                              ⟨VariableProjection x, hownsLhsByX⟩
                                          have hownerNeVarX :
                                              ownerLocation ≠ VariableProjection x := by
                                            intro hlocation
                                            rcases hownerHeap with ⟨address, hheap⟩
                                            rw [hlocation] at hheap
                                            cases hheap
                                          have hvalueHeap :
                                              ValueOwnerTargetsHeap value :=
                                            TermOwnerTargetsHeap.value
                                              (ValidRuntimeState.termOwnerTargetsHeap
                                                hvalidInner)
                                          have hvaluePartialHeap :
                                              PartialValueOwnerTargetsHeap
                                                (.value value) :=
                                            ValueOwnerTargetsHeap.partial hvalueHeap
                                          have hborrowsRhs :
                                              PartialTyBorrowsWellFormedInSlot _env₂
                                                _targetLifetime (.ty _rhsTy) :=
                                            PartialTyBorrowsWellFormedInSlot.of_wellFormedTy
                                              hwellTy
                                          have hvalueNoReachOwner :
                                              ∀ reached,
                                                RuntimeFrame.Reaches midStore
                                                  (.value value) (.ty _rhsTy) reached →
                                                reached ≠ ownerLocation := by
                                            intro reached hreach hreached
                                            subst reached
                                            rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
                                                hborrowsRhs hvalidValue hreach with
                                              hdirect | hsource
                                            · exact
                                                (ValidRuntimeState.storeTermDisjoint
                                                  hvalidInner ownerLocation
                                                  (by
                                                    simpa [termOwningLocations,
                                                      termValues,
                                                      partialValueOwningLocations,
                                                      valueOwningLocations,
                                                      valueOwnedLocation?] using
                                                      hdirect))
                                                ⟨VariableProjection x, hownsLhsByX⟩
                                            · rcases hsource with
                                                ⟨storage, hstorageReach, hownsStorage⟩
                                              have hstorageNeVar :
                                                  storage ≠ VariableProjection x :=
                                                RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                                                  (ValidRuntimeState.storeOwnerTargetsHeap
                                                    hvalidInner)
                                                  hvaluePartialHeap hborrowsRhs
                                                  hstorageReach
                                              have hstorageEq :
                                                  storage = VariableProjection x :=
                                                (ValidRuntimeState.validStore
                                                  hvalidInner) ownerLocation
                                                  storage (VariableProjection x)
                                                  hownsStorage hownsLhsByX
                                              exact hstorageNeVar hstorageEq
                                          have hnewValueValidWrite :
                                              ValidValue
                                                (midStore.update ownerLocation
                                                  { ownerSlot with
                                                    value := .value value })
                                                value _rhsTy :=
                                            RuntimeFrame.validValue_update_of_not_reaches
                                              hvalidValue hvalueNoReachOwner
                                          have hnewSlotWrite :
                                              (midStore.update ownerLocation
                                                { ownerSlot with value := .value value }).slotAt
                                                ownerLocation =
                                                some
                                                  { value := .value value,
                                                    lifetime := ownerSlot.lifetime } := by
                                            simp [ProgramStore.update]
                                          have hstoreXWrite :
                                              (midStore.update ownerLocation
                                                { ownerSlot with value := .value value }).slotAt
                                                (VariableProjection x) =
                                                some
                                                  { value := PartialValue.value
                                                      (Value.ref
                                                        { location := ownerLocation,
                                                          owner := true }),
                                                    lifetime := writeEnvSlot.lifetime } := by
                                            have hvarXNeOwner :
                                                VariableProjection x ≠ ownerLocation := by
                                              intro hvarX
                                              exact hownerNeVarX hvarX.symm
                                            simpa [ProgramStore.update, hvarXNeOwner]
                                              using hstoreX
                                          have hnewBaseValidWrite :
                                              ValidPartialValue
                                                (midStore.update ownerLocation
                                                  { ownerSlot with
                                                    value := .value value })
                                                (.value
                                                  (.ref
                                                    { location := ownerLocation,
                                                      owner := true }))
                                                (.box (.ty _rhsTy)) :=
                                            ValidPartialValue.box hnewSlotWrite
                                              hnewValueValidWrite
                                          have hwriteValidStore :
                                              ValidStore
                                                (midStore.update ownerLocation
                                                  { ownerSlot with
                                                    value := .value value }) := by
                                            exact validStore_update_disjoint
                                              (updatedLocation := ownerLocation)
                                              (slot :=
                                                { ownerSlot with
                                                  value := .value value })
                                              (ValidRuntimeState.validStore
                                                hvalidInner)
                                              (by
                                                intro owned hmem howns
                                                exact
                                                  (ValidRuntimeState.storeTermDisjoint
                                                    hvalidInner owned
                                                    (by
                                                      simpa [termOwningLocations,
                                                        termValues,
                                                        partialValueOwningLocations]
                                                        using hmem))
                                                  howns)
                                          have hwriteStoreConcrete :
                                              midStore.write (LVal.var x).deref
                                                (.value value) =
                                                some
                                                  (midStore.update ownerLocation
                                                    { ownerSlot with
                                                      value := .value value }) := by
                                            simpa [hwriteStoreEq] using hwriteStore
                                          have hwriteOwnerHeap :
                                              StoreOwnerTargetsHeap
                                                (midStore.update ownerLocation
                                                  { ownerSlot with
                                                    value := .value value }) :=
                                            storeOwnerTargetsHeap_write
                                              (ValidRuntimeState.storeOwnerTargetsHeap
                                                hvalidInner)
                                              hvaluePartialHeap hwriteStoreConcrete
                                          have hdropValuesHeap :
                                              ∀ dropValue,
                                                dropValue ∈ [ownerSlot.value] →
                                                PartialValueOwnerTargetsHeap dropValue := by
                                            intro dropValue hmem
                                            simp at hmem
                                            subst hmem
                                            exact partialValueOwnerTargetsHeap_of_slot
                                              (ValidRuntimeState.storeOwnerTargetsHeap
                                                hvalidInner) hownedSlot
                                          have havoidVarX :
                                              DropsAvoids
                                                (midStore.update ownerLocation
                                                  { ownerSlot with
                                                    value := .value value })
                                                [ownerSlot.value]
                                                (VariableProjection x) :=
                                            dropsAvoids_var_of_ownerTargetsHeap
                                              hdrops hwriteOwnerHeap hdropValuesHeap
                                          have holdDoesNotOwnLhs :
                                              ∀ dropValue,
                                                dropValue ∈ [ownerSlot.value] →
                                                ownerLocation ∉
                                                  partialValueOwningLocations
                                                    dropValue := by
                                            intro dropValue hmem howned
                                            simp at hmem
                                            subst hmem
                                            have holdValue :
                                                ownerSlot.value =
                                                  .value
                                                    (owningRef
                                                      ownerLocation) :=
                                              eq_owningRef_of_mem_partialValueOwningLocations
                                                howned
                                            have hselfSlot :
                                                midStore.slotAt ownerLocation =
                                                  some
                                                    { value := .value
                                                        (owningRef
                                                          ownerLocation),
                                                      lifetime :=
                                                        ownerSlot.lifetime } := by
                                              cases ownerSlot with
                                              | mk oldValue oldLifetime =>
                                                  cases holdValue
                                                  simpa [owningRef] using
                                                    hownedSlot
                                            exact
                                              (ValidPartialValue.no_self_owning_ref
                                                hselfSlot)
                                                (by simpa [holdValue] using
                                                  hinnerValid)
                                          have havoidOwnerLocation :
                                              DropsAvoids
                                                (midStore.update ownerLocation
                                                  { ownerSlot with
                                                    value := .value value })
                                                [ownerSlot.value] ownerLocation :=
                                            dropsAvoids_of_protected_owner
                                              hdrops hwriteValidStore
                                              ⟨writeEnvSlot.lifetime,
                                                hstoreXWrite⟩
                                              havoidVarX holdDoesNotOwnLhs
                                          have hnewBorrows :
                                              PartialTyBorrowsWellFormedInSlot _env₂
                                                writeEnvSlot.lifetime
                                                (.box (.ty _rhsTy)) := by
                                            rw [hsourceLifetime]
                                            exact PartialTyBorrowsWellFormedInSlot.box
                                              hborrowsRhs
                                          have hnewGraphDisjoint :
                                              ∀ reached,
                                                RuntimeFrame.Reaches
                                                  (midStore.update ownerLocation
                                                    { ownerSlot with
                                                      value := .value value })
                                                  (.value
                                                    (.ref
                                                      { location := ownerLocation,
                                                        owner := true }))
                                                  (.box (.ty _rhsTy)) reached →
                                                ∀ dropValue,
                                                  dropValue ∈ [ownerSlot.value] →
                                                  reached ∉
                                                    partialValueOwningLocations
                                                      dropValue := by
                                            intro reached hreach dropValue hmem howned
                                            simp at hmem
                                            subst hmem
                                            rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
                                                hnewBorrows hnewBaseValidWrite
                                                hreach with hdirect | hsource
                                            · have hreachedEq : reached = ownerLocation := by
                                                simpa [partialValueOwningLocations,
                                                  valueOwningLocations,
                                                  valueOwnedLocation?] using hdirect
                                              subst hreachedEq
                                              exact holdDoesNotOwnLhs ownerSlot.value
                                                (by simp) howned
                                            · rcases hsource with
                                                ⟨storage, hstorageReach,
                                                  hownsWrite⟩
                                              by_cases hstorageOwner :
                                                  storage = ownerLocation
                                              · subst storage
                                                rcases hownsWrite with
                                                  ⟨ownerLifetime, hownerSlotWrite⟩
                                                have hnewOwnsReached :
                                                    PartialValue.value value =
                                                      PartialValue.value
                                                        (owningRef reached) := by
                                                  have hslotEq :
                                                      { ownerSlot with
                                                        value := PartialValue.value value } =
                                                        StoreSlot.mk
                                                          (PartialValue.value
                                                            (owningRef reached))
                                                          ownerLifetime := by
                                                    simpa [ProgramStore.update]
                                                      using hownerSlotWrite
                                                  exact congrArg StoreSlot.value
                                                    hslotEq
                                                have htermOwns :
                                                    reached ∈
                                                      termOwningLocations
                                                        (.val value) := by
                                                  simpa [termOwningLocations,
                                                    termValues,
                                                    valueOwningLocations,
                                                    partialValueOwningLocations]
                                                    using
                                                      mem_partialValueOwningLocations_of_eq_owningRef
                                                        hnewOwnsReached
                                                have holdOwns :
                                                    ProgramStore.OwnsAt midStore
                                                      reached ownerLocation := by
                                                  have holdValue :
                                                      ownerSlot.value =
                                                        .value
                                                          (owningRef reached) :=
                                                    eq_owningRef_of_mem_partialValueOwningLocations
                                                      howned
                                                  exact ⟨ownerSlot.lifetime, by
                                                    cases ownerSlot with
                                                    | mk oldValue oldLifetime =>
                                                        cases holdValue
                                                        simpa [owningRef] using
                                                          hownedSlot⟩
                                                exact
                                                  (ValidRuntimeState.storeTermDisjoint
                                                    hvalidInner reached
                                                    htermOwns)
                                                  ⟨ownerLocation, holdOwns⟩
                                              · have hstorageNeUpdated :
                                                    storage ≠ ownerLocation :=
                                                  hstorageOwner
                                                rcases hownsWrite with
                                                  ⟨ownerLifetime, hownerSlotWrite⟩
                                                have hownsStore :
                                                    ProgramStore.OwnsAt midStore
                                                      reached storage :=
                                                  ⟨ownerLifetime, by
                                                    simpa [ProgramStore.update,
                                                      hstorageNeUpdated] using
                                                      hownerSlotWrite⟩
                                                have holdOwns :
                                                    ProgramStore.OwnsAt midStore
                                                      reached ownerLocation := by
                                                  have holdValue :
                                                      ownerSlot.value =
                                                        .value
                                                          (owningRef reached) :=
                                                    eq_owningRef_of_mem_partialValueOwningLocations
                                                      howned
                                                  exact ⟨ownerSlot.lifetime, by
                                                    cases ownerSlot with
                                                    | mk oldValue oldLifetime =>
                                                        cases holdValue
                                                        simpa [owningRef] using
                                                          hownedSlot⟩
                                                have hstorageEq :
                                                    storage = ownerLocation :=
                                                  (ValidRuntimeState.validStore
                                                    hvalidInner) reached
                                                    storage ownerLocation
                                                    hownsStore holdOwns
                                                exact hstorageNeUpdated hstorageEq
                                          have hnewBaseValidFinal :
                                              ValidPartialValue finalStore
                                                (.value
                                                  (.ref
                                                    { location := ownerLocation,
                                                      owner := true }))
                                                (.box (.ty _rhsTy)) :=
                                            RuntimeFrame.validPartialValue_drops_of_avoids_reaches
                                              hdrops hnewBaseValidWrite
                                              (by
                                                intro reached hreach
                                                exact
                                                  RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
                                                    hdrops hwriteValidStore
                                                    hstoreXWrite hnewBorrows
                                                    hnewBaseValidWrite
                                                    havoidVarX
                                                    hnewGraphDisjoint hreach)
                                          have hallocatedWrite :
                                              StoreOwnersAllocated
                                                (midStore.update ownerLocation
                                                  { ownerSlot with
                                                    value := .value value }) :=
                                            storeOwnersAllocated_write_value_of_validValue
                                              (ValidRuntimeState.storeOwnersAllocated
                                                hvalidInner)
                                              hvalidValue hwriteStoreConcrete
                                          have hrootWrite :
                                              HeapSlotsRootLifetime
                                                (midStore.update ownerLocation
                                                  { ownerSlot with
                                                    value := .value value }) :=
                                            heapSlotsRootLifetime_write
                                              (ValidRuntimeState.heapSlotsRootLifetime
                                                hvalidInner)
                                              hwriteStoreConcrete
                                          have hdropDisjoint :
                                              ∀ owned,
                                                owned ∈
                                                  partialValuesOwningLocations
                                                    [ownerSlot.value] →
                                                ¬ ProgramStore.Owns
                                                  (midStore.update ownerLocation
                                                    { ownerSlot with
                                                      value := .value value })
                                                  owned := by
                                            intro owned hmem howns
                                            simp [partialValuesOwningLocations] at hmem
                                            have holdOwns :
                                                ProgramStore.OwnsAt midStore
                                                  owned ownerLocation := by
                                              have holdValue :
                                                  ownerSlot.value =
                                                    .value (owningRef owned) :=
                                                eq_owningRef_of_mem_partialValueOwningLocations
                                                  hmem
                                              exact ⟨ownerSlot.lifetime, by
                                                cases ownerSlot with
                                                | mk oldValue oldLifetime =>
                                                    cases holdValue
                                                    simpa [owningRef] using
                                                      hownedSlot⟩
                                            rw [ProgramStore.Owns] at howns
                                            rcases howns with
                                              ⟨storage, ownerLifetime,
                                                hownerSlotWrite⟩
                                            by_cases hstorageOwner :
                                                storage = ownerLocation
                                            · subst storage
                                              have hnewOwnsOld :
                                                  owned ∈
                                                    partialValueOwningLocations
                                                      (.value value) := by
                                                have hslotEq :
                                                    { ownerSlot with
                                                      value := PartialValue.value value } =
                                                      StoreSlot.mk
                                                        (PartialValue.value
                                                          (owningRef owned))
                                                        ownerLifetime := by
                                                  simpa [ProgramStore.update]
                                                    using hownerSlotWrite
                                                exact
                                                  mem_partialValueOwningLocations_of_eq_owningRef
                                                    (congrArg StoreSlot.value
                                                      hslotEq)
                                              exact
                                                (ValidRuntimeState.storeTermDisjoint
                                                  hvalidInner owned
                                                  (by
                                                    simpa [termOwningLocations,
                                                      termValues,
                                                      partialValueOwningLocations]
                                                      using hnewOwnsOld))
                                                ⟨ownerLocation, holdOwns⟩
                                            · have hownerOld :
                                                  ProgramStore.OwnsAt midStore
                                                    owned storage :=
                                                ⟨ownerLifetime, by
                                                  simpa [ProgramStore.update,
                                                    hstorageOwner] using
                                                    hownerSlotWrite⟩
                                              have hstorageEq :
                                                  storage = ownerLocation :=
                                                (ValidRuntimeState.validStore
                                                  hvalidInner) owned storage
                                                  ownerLocation hownerOld
                                                  holdOwns
                                              exact hstorageOwner hstorageEq
                                          have hallocatedFinal :
                                              StoreOwnersAllocated finalStore :=
                                            drops_storeOwnersAllocated_of_disjoint
                                              hdrops hwriteValidStore
                                              hallocatedWrite hdropDisjoint
                                          have hheapFinal :
                                              StoreOwnerTargetsHeap finalStore :=
                                            drops_storeOwnerTargetsHeap hdrops
                                              hwriteOwnerHeap
                                          have hrootFinal :
                                              HeapSlotsRootLifetime finalStore :=
                                            drops_heapSlotsRootLifetime hdrops
                                              hrootWrite
                                          have hvalidRuntimeFinal :
                                              ValidRuntimeState finalStore
                                                (.val .unit) :=
                                            validRuntimeState_assign_step_of_postWriteDrop_invariants
                                              (lifetime := _lifetime)
                                              hvalidAssign hallocatedFinal
                                              hheapFinal hrootFinal hread
                                              hwriteStoreConcrete hdrops
                                          have hsafeFinal :
                                              finalStore ∼ₛ
                                                (_env₂.update x
                                                  { writeEnvSlot with
                                                    ty := .box (.ty _rhsTy) }) := by
                                            refine safeAbstraction_update_var_partial_of_preserved
                                              henvX ?hstoreXFinal
                                              hnewBaseValidFinal rfl ?domain
                                              ?preserve
                                            · exact dropsAvoids_slotAt_preserved
                                                hdrops havoidVarX hstoreXWrite
                                            · intro y hyx
                                              constructor
                                              · intro hdomainStore
                                                rcases hdomainStore with
                                                  ⟨slotY, hslotYFinal⟩
                                                have hslotYWrite :
                                                    (midStore.update
                                                      ownerLocation
                                                      { ownerSlot with
                                                        value := .value value }).slotAt
                                                        (VariableProjection y) =
                                                      some slotY :=
                                                  drops_slotAt_of_slotAt
                                                    hdrops hslotYFinal
                                                have hslotYStore :
                                                    midStore.slotAt
                                                      (VariableProjection y) =
                                                      some slotY := by
                                                  by_cases hyOwner :
                                                      VariableProjection y =
                                                        ownerLocation
                                                  · subst hyOwner
                                                    have hvarYHeap :
                                                        ∃ address,
                                                          VariableProjection y =
                                                            .heap address :=
                                                      hownerHeap
                                                    rcases hvarYHeap with
                                                      ⟨address, hheap⟩
                                                    cases hheap
                                                  · simpa [ProgramStore.update,
                                                      hyOwner] using hslotYWrite
                                                exact (hsafeInner.1 y).mp
                                                  ⟨slotY, hslotYStore⟩
                                              · intro hdomainEnv
                                                rcases hdomainEnv with
                                                  ⟨otherEnvSlot, henvY⟩
                                                rcases hsafeInner.2 y otherEnvSlot
                                                    henvY with
                                                  ⟨oldValue, hslotY,
                                                    _hvalidOld⟩
                                                have hslotYWrite :
                                                    (midStore.update
                                                      ownerLocation
                                                      { ownerSlot with
                                                        value := .value value }).slotAt
                                                        (VariableProjection y) =
                                                      some
                                                        { value := oldValue,
                                                          lifetime :=
                                                            otherEnvSlot.lifetime } := by
                                                  have hyOwner :
                                                      VariableProjection y ≠
                                                        ownerLocation := by
                                                    intro hyOwner
                                                    have hownerEq :
                                                        ownerLocation =
                                                          VariableProjection y :=
                                                      hyOwner.symm
                                                    have hvarYHeap :
                                                        ∃ address,
                                                          ownerLocation =
                                                            .heap address :=
                                                      hownerHeap
                                                    rcases hvarYHeap with
                                                      ⟨address, hheap⟩
                                                    rw [hownerEq] at hheap
                                                    cases hheap
                                                  simpa [ProgramStore.update,
                                                    hyOwner] using hslotY
                                                have havoidY :
                                                    DropsAvoids
                                                      (midStore.update
                                                        ownerLocation
                                                        { ownerSlot with
                                                          value := .value value })
                                                      [ownerSlot.value]
                                                      (VariableProjection y) :=
                                                  dropsAvoids_var_of_ownerTargetsHeap
                                                    hdrops hwriteOwnerHeap
                                                    hdropValuesHeap
                                                exact ⟨_,
                                                  dropsAvoids_slotAt_preserved
                                                    hdrops havoidY
                                                    hslotYWrite⟩
                                            · intro y otherEnvSlot hyx henvY
                                              rcases hsafeInner.2 y
                                                  otherEnvSlot henvY with
                                                ⟨oldValue, hslotY, hvalidOld⟩
                                              have hyOwner :
                                                  VariableProjection y ≠
                                                    ownerLocation := by
                                                intro hyOwner
                                                have hownerEq :
                                                    ownerLocation =
                                                      VariableProjection y :=
                                                  hyOwner.symm
                                                rcases hownerHeap with
                                                  ⟨address, hheap⟩
                                                rw [hownerEq] at hheap
                                                cases hheap
                                              have hslotYWrite :
                                                  (midStore.update ownerLocation
                                                    { ownerSlot with
                                                      value := .value value }).slotAt
                                                      (VariableProjection y) =
                                                    some
                                                      { value := oldValue,
                                                        lifetime :=
                                                          otherEnvSlot.lifetime } := by
                                                simpa [ProgramStore.update,
                                                  hyOwner] using hslotY
                                              have havoidY :
                                                  DropsAvoids
                                                    (midStore.update ownerLocation
                                                      { ownerSlot with
                                                        value := .value value })
                                                    [ownerSlot.value]
                                                    (VariableProjection y) :=
                                                dropsAvoids_var_of_ownerTargetsHeap
                                                  hdrops hwriteOwnerHeap
                                                  hdropValuesHeap
                                              have hborrowsOld :
                                                  PartialTyBorrowsWellFormedInSlot
                                                    _env₂
                                                    otherEnvSlot.lifetime
                                                    otherEnvSlot.ty := by
                                                intro mutable targets hcontains
                                                exact hwellInner.1 y
                                                  otherEnvSlot mutable targets
                                                  henvY
                                                  ⟨otherEnvSlot, henvY,
                                                    hcontains⟩
                                              have hvalidOldWrite :
                                                  ValidPartialValue
                                                    (midStore.update
                                                      ownerLocation
                                                      { ownerSlot with
                                                        value := .value value })
                                                    oldValue otherEnvSlot.ty :=
                                                RuntimeFrame.validPartialValue_update_of_not_reaches
                                                  hvalidOld
                                                  (by
                                                    intro reached hreach hreached
                                                    subst reached
                                                    have hvalueHeapOld :
                                                        PartialValueOwnerTargetsHeap
                                                          oldValue :=
                                                      partialValueOwnerTargetsHeap_of_slot
                                                        (ValidRuntimeState.storeOwnerTargetsHeap
                                                          hvalidInner) hslotY
                                                    rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
                                                        hborrowsOld hvalidOld
                                                        hreach with
                                                      hdirect | hsource
                                                    · have holdValueOwns :
                                                          oldValue =
                                                            .value
                                                              (owningRef
                                                                ownerLocation) :=
                                                        eq_owningRef_of_mem_partialValueOwningLocations
                                                          hdirect
                                                      have hownsY :
                                                          ProgramStore.OwnsAt
                                                            midStore
                                                            ownerLocation
                                                            (VariableProjection y) :=
                                                        ⟨otherEnvSlot.lifetime, by
                                                          cases holdValueOwns
                                                          simpa [owningRef] using
                                                            hslotY⟩
                                                      have hvarEq :
                                                          VariableProjection y =
                                                            VariableProjection x :=
                                                        (ValidRuntimeState.validStore
                                                          hvalidInner)
                                                          ownerLocation
                                                          (VariableProjection y)
                                                          (VariableProjection x)
                                                          hownsY hownsLhsByX
                                                      exact hyx (by
                                                        cases hvarEq
                                                        rfl)
                                                    · rcases hsource with
                                                        ⟨storage,
                                                          hstorageReach,
                                                          hownsStorage⟩
                                                      have hstorageNeVar :
                                                          storage ≠
                                                            VariableProjection x :=
                                                        RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                                                          (ValidRuntimeState.storeOwnerTargetsHeap
                                                            hvalidInner)
                                                          hvalueHeapOld
                                                          hborrowsOld
                                                          hstorageReach
                                                      have hstorageEq :
                                                          storage =
                                                            VariableProjection x :=
                                                        (ValidRuntimeState.validStore
                                                          hvalidInner)
                                                          ownerLocation storage
                                                          (VariableProjection x)
                                                          hownsStorage
                                                          hownsLhsByX
                                                      exact hstorageNeVar
                                                        hstorageEq)
                                              have holdGraphDisjoint :
                                                  ∀ reached,
                                                    RuntimeFrame.Reaches
                                                      (midStore.update
                                                        ownerLocation
                                                        { ownerSlot with
                                                          value := .value value })
                                                      oldValue otherEnvSlot.ty
                                                      reached →
                                                    ∀ dropValue,
                                                      dropValue ∈
                                                        [ownerSlot.value] →
                                                      reached ∉
                                                        partialValueOwningLocations
                                                          dropValue := by
                                                intro reached hreach dropValue
                                                  hmem howned
                                                simp at hmem
                                                subst hmem
                                                have holdOwns :
                                                    ProgramStore.OwnsAt midStore
                                                      reached ownerLocation := by
                                                  have holdValue :
                                                      ownerSlot.value =
                                                        .value
                                                          (owningRef reached) :=
                                                    eq_owningRef_of_mem_partialValueOwningLocations
                                                      howned
                                                  exact ⟨ownerSlot.lifetime, by
                                                    cases ownerSlot with
                                                    | mk oldValueX oldLifetimeX =>
                                                        cases holdValue
                                                        simpa [owningRef] using
                                                          hownedSlot⟩
                                                rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
                                                    hborrowsOld hvalidOldWrite
                                                    hreach with hdirect | hsource
                                                · have holdValueOwns :
                                                      oldValue =
                                                        .value
                                                          (owningRef reached) :=
                                                    eq_owningRef_of_mem_partialValueOwningLocations
                                                      hdirect
                                                  have hownsY :
                                                      ProgramStore.OwnsAt midStore
                                                        reached
                                                        (VariableProjection y) :=
                                                    ⟨otherEnvSlot.lifetime, by
                                                      cases holdValueOwns
                                                      simpa [owningRef] using
                                                        hslotY⟩
                                                  have hstorageEq :
                                                      VariableProjection y =
                                                        ownerLocation :=
                                                    (ValidRuntimeState.validStore
                                                      hvalidInner) reached
                                                      (VariableProjection y)
                                                      ownerLocation hownsY
                                                      holdOwns
                                                  exact hyOwner hstorageEq
                                                · rcases hsource with
                                                    ⟨storage, hstorageReach,
                                                      hownsWrite⟩
                                                  rcases hownsWrite with
                                                    ⟨ownerLifetime,
                                                      hownerSlotWrite⟩
                                                  by_cases hstorageOwner :
                                                      storage = ownerLocation
                                                  · subst storage
                                                    have hnewOwnsReached :
                                                        PartialValue.value value =
                                                          PartialValue.value
                                                            (owningRef
                                                              reached) := by
                                                      have hslotEq :
                                                          { ownerSlot with
                                                            value :=
                                                              PartialValue.value
                                                                value } =
                                                            StoreSlot.mk
                                                              (PartialValue.value
                                                                (owningRef
                                                                  reached))
                                                              ownerLifetime := by
                                                        simpa [ProgramStore.update]
                                                          using hownerSlotWrite
                                                      exact congrArg
                                                        StoreSlot.value hslotEq
                                                    have htermOwns :
                                                        reached ∈
                                                          termOwningLocations
                                                            (.val value) := by
                                                      simpa [termOwningLocations,
                                                        termValues,
                                                        valueOwningLocations,
                                                        partialValueOwningLocations]
                                                        using
                                                          mem_partialValueOwningLocations_of_eq_owningRef
                                                            hnewOwnsReached
                                                    exact
                                                      (ValidRuntimeState.storeTermDisjoint
                                                        hvalidInner reached
                                                        htermOwns)
                                                      ⟨ownerLocation, holdOwns⟩
                                                  · have hownerStore :
                                                        ProgramStore.OwnsAt
                                                          midStore reached
                                                          storage :=
                                                      ⟨ownerLifetime, by
                                                        simpa [ProgramStore.update,
                                                          hstorageOwner] using
                                                          hownerSlotWrite⟩
                                                    have hstorageEq :
                                                        storage = ownerLocation :=
                                                      (ValidRuntimeState.validStore
                                                        hvalidInner) reached
                                                        storage ownerLocation
                                                        hownerStore holdOwns
                                                    exact hstorageOwner
                                                      hstorageEq
                                              have hvalidOldFinal :
                                                  ValidPartialValue finalStore
                                                    oldValue otherEnvSlot.ty :=
                                                RuntimeFrame.validPartialValue_drops_of_avoids_reaches
                                                  hdrops hvalidOldWrite
                                                  (by
                                                    intro reached hreach
                                                    exact
                                                      RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
                                                        hdrops hwriteValidStore
                                                        hslotYWrite
                                                        hborrowsOld
                                                        hvalidOldWrite havoidY
                                                        holdGraphDisjoint
                                                        hreach)
                                              exact ⟨oldValue,
                                                dropsAvoids_slotAt_preserved
                                                  hdrops havoidY hslotYWrite,
                                                hvalidOldFinal⟩
                                          exact ⟨hvalidRuntimeFinal, hsafeFinal,
                                            ValidPartialValue.unit⟩
                          | deref source =>
                              have hownerSpine :
                                  ∃ baseEnvSlot rootSlot,
                                    _env₂.slotAt
                                        (LVal.base source.deref.deref) =
                                      some baseEnvSlot ∧
                                    midStore.slotAt
                                        (VariableProjection
                                          (LVal.base source.deref.deref)) =
                                      some rootSlot ∧
                                    rootSlot.lifetime = baseEnvSlot.lifetime ∧
                                    StoreOwnerSpine midStore
                                      (VariableProjection
                                        (LVal.base source.deref.deref))
                                      rootSlot baseEnvSlot.ty
                                      (LVal.path source.deref.deref)
                                      lhsLocation overwrittenSlot _oldTy := by
                                rcases StoreOwnerSpine.of_lvalTyping_box
                                    hwellInner hsafeInner hsourceBox with
                                  ⟨baseEnvSlot, rootSlot, sourceLocation,
                                    sourceSlot, henvBase, hrootSlot,
                                    hrootLifetime, hsourceLoc, hsourceSlot,
                                    hsourceSpine⟩
                                have hsourceValid :
                                    ValidPartialValue midStore sourceSlot.value
                                      (.box _oldTy) :=
                                  StoreOwnerSpine.leaf_valid hsourceSpine
                                rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
                                cases hsourceValid with
                                | @box ownerLocation ownerSlot _ hownedSlot hinnerValid =>
                                    have hlhsLocFromSource :
                                        midStore.loc source.deref.deref =
                                          some ownerLocation := by
                                      change
                                        ((midStore.loc source.deref).bind
                                          (fun location =>
                                            (midStore.slotAt location).bind
                                              (fun slot =>
                                                match slot.value with
                                                | .value (.ref ref) =>
                                                    some ref.location
                                                | .value _ => none
                                                | .undef => none))) =
                                          some ownerLocation
                                      simp [hsourceLoc, hsourceSlot]
                                    have hownerEq : ownerLocation = lhsLocation := by
                                      rw [hlhsLoc] at hlhsLocFromSource
                                      exact (Option.some.inj hlhsLocFromSource).symm
                                    subst hownerEq
                                    have hslotEqOld : ownerSlot = overwrittenSlot := by
                                      rw [hlhsSlot] at hownedSlot
                                      exact (Option.some.inj hownedSlot).symm
                                    subst hslotEqOld
                                    have hspineFull :
                                        StoreOwnerSpine midStore
                                          (VariableProjection
                                            (LVal.base source.deref))
                                          rootSlot baseEnvSlot.ty
                                          (() :: LVal.path source.deref)
                                          ownerLocation ownerSlot _oldTy :=
                                      StoreOwnerSpine.snoc_box hsourceSpine rfl rfl
                                        hownedSlot hinnerValid
                                    exact ⟨baseEnvSlot, rootSlot,
                                      by simpa [LVal.base] using henvBase,
                                      by simpa [LVal.base] using hrootSlot,
                                      hrootLifetime,
                                      by
                                        simpa [LVal.base, LVal.path_deref_cons]
                                          using hspineFull⟩
                              rw [hwriteStoreEq] at hdrops
                              rcases hownerSpine with
                                ⟨baseEnvSlot, rootSlot, henvBase,
                                  hrootSlot, hrootLifetime, hspine⟩
                              have hwriteEnvSlotEq :
                                  writeEnvSlot = baseEnvSlot := by
                                rw [hbase] at henvBase
                                exact Option.some.inj henvBase
                              cases hwriteEnvSlotEq
                              have hwriteMiddleEq : _env₂ = _writeMiddle :=
                                (StoreOwnerSpine.updateAtPath_rank_zero_env_eq
                                  hspine hupdate).symm
                              cases hwriteMiddleEq
                              have hpathNonempty :
                                  LVal.path source.deref.deref ≠ [] := by
                                simp [LVal.path_deref_cons]
                              have hspineCons :
                                  StoreOwnerSpine midStore
                                    (VariableProjection
                                      (LVal.base source.deref))
                                    rootSlot writeEnvSlot.ty
                                    (() :: LVal.path source.deref)
                                    lhsLocation overwrittenSlot _oldTy := by
                                simpa [LVal.base, LVal.path_deref_cons] using
                                  hspine
                              have hleafNeRoot :
                                  lhsLocation ≠
                                    VariableProjection
                                      (LVal.base source.deref.deref) := by
                                have hne :=
                                  StoreOwnerSpine.leaf_ne_storage_of_cons
                                    hspineCons
                                simpa [LVal.base] using hne
                              have hleafOwned :
                                  ProgramStore.Owns midStore lhsLocation :=
                                ProgramStore.OwnsTransitively.to_owns
                                  (StoreOwnerSpine.ownsTransitively_of_nonempty
                                    hspine hpathNonempty)
                              have hlhsHeap :
                                  ∃ address, lhsLocation = .heap address :=
                                (ValidRuntimeState.storeOwnerTargetsHeap
                                  hvalidInner) lhsLocation hleafOwned
                              have hvalidAssign :
                                  ValidRuntimeState midStore
                                    (.assign source.deref.deref (.val value)) :=
                                validRuntimeState_assign_value_of_value
                                  hvalidInner
                              have hvalueHeap :
                                  ValueOwnerTargetsHeap value :=
                                TermOwnerTargetsHeap.value
                                  (ValidRuntimeState.termOwnerTargetsHeap
                                    hvalidInner)
                              have hvaluePartialHeap :
                                  PartialValueOwnerTargetsHeap (.value value) :=
                                ValueOwnerTargetsHeap.partial hvalueHeap
                              have hborrowsRhs :
                                  PartialTyBorrowsWellFormedInSlot _env₂
                                    _targetLifetime (.ty _rhsTy) :=
                                PartialTyBorrowsWellFormedInSlot.of_wellFormedTy
                                  hwellTy
                              have hrootNoReach :
                                  ∀ reached,
                                    RuntimeFrame.Reaches midStore
                                      (.value value) (.ty _rhsTy) reached →
                                    reached ≠
                                      VariableProjection
                                        (LVal.base source.deref.deref) := by
                                intro reached hreach
                                exact
                                  RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                                    (ValidRuntimeState.storeOwnerTargetsHeap
                                      hvalidInner)
                                    hvaluePartialHeap hborrowsRhs hreach
                              have hvalueNoReachLhs :
                                  ∀ reached,
                                    RuntimeFrame.Reaches midStore
                                      (.value value) (.ty _rhsTy) reached →
                                    reached ≠ lhsLocation :=
                                StoreOwnerSpine.not_reaches_leaf_of_not_reaches_root
                                  hvalidInner hborrowsRhs hvalidValue hspine
                                  hrootNoReach
                              have hnewValueValidWrite :
                                  ValidValue
                                    (midStore.update lhsLocation
                                      { overwrittenSlot with
                                        value := .value value })
                                    value _rhsTy :=
                                RuntimeFrame.validValue_update_of_not_reaches
                                  hvalidValue hvalueNoReachLhs
                              have hnewLeafSlotWrite :
                                  (midStore.update lhsLocation
                                    { overwrittenSlot with
                                      value := .value value }).slotAt
                                    lhsLocation =
                                    some
                                      { value := .value value,
                                        lifetime := overwrittenSlot.lifetime } := by
                                simp [ProgramStore.update]
                              have hnewRootValidWrite :
                                  ValidPartialValue
                                    (midStore.update lhsLocation
                                      { overwrittenSlot with
                                        value := .value value })
                                    rootSlot.value _updatedTy :=
                                StoreOwnerSpine.valid_after_updateAtPath_nonempty
                                  hspine hpathNonempty hupdate
                                  hnewValueValidWrite
                              have hrootNeLeaf :
                                  VariableProjection
                                      (LVal.base source.deref.deref) ≠
                                    lhsLocation := by
                                intro hrootEq
                                exact hleafNeRoot hrootEq.symm
                              have hrootSlotWrite :
                                  (midStore.update lhsLocation
                                    { overwrittenSlot with
                                      value := .value value }).slotAt
                                    (VariableProjection
                                      (LVal.base source.deref.deref)) =
                                    some rootSlot := by
                                simpa [ProgramStore.update, hrootNeLeaf] using
                                  hrootSlot
                              have hrootSlotWriteEnv :
                                  (midStore.update lhsLocation
                                    { overwrittenSlot with
                                      value := .value value }).slotAt
                                    (VariableProjection
                                      (LVal.base source.deref.deref)) =
                                    some
                                      { value := rootSlot.value,
                                        lifetime := writeEnvSlot.lifetime } := by
                                rw [← hrootLifetime]
                                simpa using hrootSlotWrite
                              have hwriteValidStore :
                                  ValidStore
                                    (midStore.update lhsLocation
                                      { overwrittenSlot with
                                        value := .value value }) := by
                                exact validStore_update_disjoint
                                  (updatedLocation := lhsLocation)
                                  (slot :=
                                    { overwrittenSlot with
                                      value := .value value })
                                  (ValidRuntimeState.validStore hvalidInner)
                                  (by
                                    intro owned hmem howns
                                    exact
                                      (ValidRuntimeState.storeTermDisjoint
                                        hvalidInner owned
                                        (by
                                          simpa [termOwningLocations,
                                            termValues,
                                            partialValueOwningLocations]
                                            using hmem))
                                      howns)
                              have hwriteStoreConcrete :
                                  midStore.write source.deref.deref
                                    (.value value) =
                                    some
                                      (midStore.update lhsLocation
                                        { overwrittenSlot with
                                          value := .value value }) := by
                                simpa [hwriteStoreEq] using hwriteStore
                              have hwriteOwnerHeap :
                                  StoreOwnerTargetsHeap
                                    (midStore.update lhsLocation
                                      { overwrittenSlot with
                                        value := .value value }) :=
                                storeOwnerTargetsHeap_write
                                  (ValidRuntimeState.storeOwnerTargetsHeap
                                    hvalidInner)
                                  hvaluePartialHeap hwriteStoreConcrete
                              have hdropValuesHeap :
                                  ∀ dropValue,
                                    dropValue ∈ [overwrittenSlot.value] →
                                    PartialValueOwnerTargetsHeap dropValue := by
                                intro dropValue hmem
                                simp at hmem
                                subst hmem
                                exact partialValueOwnerTargetsHeap_of_slot
                                  (ValidRuntimeState.storeOwnerTargetsHeap
                                    hvalidInner) hlhsSlot
                              have havoidRoot :
                                  DropsAvoids
                                    (midStore.update lhsLocation
                                      { overwrittenSlot with
                                        value := .value value })
                                    [overwrittenSlot.value]
                                    (VariableProjection
                                      (LVal.base source.deref.deref)) :=
                                dropsAvoids_var_of_ownerTargetsHeap
                                  hdrops hwriteOwnerHeap hdropValuesHeap
                              have hrootUpdatedEnvSlot :
                                  (_env₂.update
                                    (LVal.base source.deref.deref)
                                    { ty := _updatedTy,
                                      lifetime := writeEnvSlot.lifetime }).slotAt
                                      (LVal.base source.deref.deref) =
                                    some
                                      { ty := _updatedTy,
                                        lifetime := writeEnvSlot.lifetime } := by
                                simp [Env.update]
                              have hnewBorrowsRoot :
                                  PartialTyBorrowsWellFormedInSlot
                                    (_env₂.update
                                      (LVal.base source.deref.deref)
                                      { ty := _updatedTy,
                                        lifetime := writeEnvSlot.lifetime })
                                    writeEnvSlot.lifetime _updatedTy := by
                                intro mutable targets hcontains
                                exact hwellOut.1
                                  (LVal.base source.deref.deref)
                                  { ty := _updatedTy,
                                    lifetime := writeEnvSlot.lifetime }
                                  mutable targets hrootUpdatedEnvSlot
                                  ⟨{ ty := _updatedTy,
                                      lifetime := writeEnvSlot.lifetime },
                                    hrootUpdatedEnvSlot, hcontains⟩
                              have hnewGraphDisjoint :
                                  ∀ reached,
                                    RuntimeFrame.Reaches
                                      (midStore.update lhsLocation
                                        { overwrittenSlot with
                                          value := .value value })
                                      rootSlot.value _updatedTy reached →
                                    ∀ dropValue,
                                      dropValue ∈ [overwrittenSlot.value] →
                                      reached ∉
                                        partialValueOwningLocations
                                          dropValue := by
                                intro reached hreach dropValue hmem howned
                                simp at hmem
                                subst hmem
                                have holdOwns :
                                    ProgramStore.OwnsAt midStore reached
                                      lhsLocation := by
                                  have holdValue :
                                      overwrittenSlot.value =
                                        .value (owningRef reached) :=
                                    eq_owningRef_of_mem_partialValueOwningLocations
                                      howned
                                  exact ⟨overwrittenSlot.lifetime, by
                                    cases overwrittenSlot with
                                    | mk oldValue oldLifetime =>
                                        cases holdValue
                                        simpa [owningRef] using hlhsSlot⟩
                                rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
                                    hnewBorrowsRoot hnewRootValidWrite
                                    hreach with hdirect | hsource
                                · have hrootValueOwns :
                                      rootSlot.value =
                                        .value (owningRef reached) :=
                                    eq_owningRef_of_mem_partialValueOwningLocations
                                      hdirect
                                  have hrootOwns :
                                      ProgramStore.OwnsAt midStore reached
                                        (VariableProjection
                                          (LVal.base source.deref.deref)) :=
                                    ⟨rootSlot.lifetime, by
                                      cases rootSlot with
                                      | mk rootValue rootLifetime =>
                                          cases hrootValueOwns
                                          simpa [owningRef] using
                                            hrootSlot⟩
                                  have hstorageEq :
                                      VariableProjection
                                          (LVal.base source.deref.deref) =
                                        lhsLocation :=
                                    (ValidRuntimeState.validStore hvalidInner)
                                      reached
                                      (VariableProjection
                                        (LVal.base source.deref.deref))
                                      lhsLocation hrootOwns holdOwns
                                  exact hleafNeRoot hstorageEq.symm
                                · rcases hsource with
                                    ⟨storage, _hstorageReach, hownsWrite⟩
                                  rcases hownsWrite with
                                    ⟨ownerLifetime, hownerSlotWrite⟩
                                  by_cases hstorageLeaf :
                                      storage = lhsLocation
                                  · subst storage
                                    have hnewOwnsReached :
                                        PartialValue.value value =
                                          PartialValue.value
                                            (owningRef reached) := by
                                      have hslotEq :
                                          { overwrittenSlot with
                                            value := PartialValue.value value } =
                                            StoreSlot.mk
                                              (PartialValue.value
                                                (owningRef reached))
                                              ownerLifetime := by
                                        simpa [ProgramStore.update] using
                                          hownerSlotWrite
                                      exact congrArg StoreSlot.value hslotEq
                                    have htermOwns :
                                        reached ∈
                                          termOwningLocations (.val value) := by
                                      simpa [termOwningLocations, termValues,
                                        valueOwningLocations,
                                        partialValueOwningLocations]
                                        using
                                          mem_partialValueOwningLocations_of_eq_owningRef
                                            hnewOwnsReached
                                    exact
                                      (ValidRuntimeState.storeTermDisjoint
                                        hvalidInner reached htermOwns)
                                      ⟨lhsLocation, holdOwns⟩
                                  · have hownerStore :
                                        ProgramStore.OwnsAt midStore reached
                                          storage :=
                                      ⟨ownerLifetime, by
                                        simpa [ProgramStore.update,
                                          hstorageLeaf] using
                                          hownerSlotWrite⟩
                                    have hstorageEq :
                                        storage = lhsLocation :=
                                      (ValidRuntimeState.validStore
                                        hvalidInner) reached storage
                                        lhsLocation hownerStore holdOwns
                                    exact hstorageLeaf hstorageEq
                              have hnewRootValidFinal :
                                  ValidPartialValue finalStore
                                    rootSlot.value _updatedTy :=
                                RuntimeFrame.validPartialValue_drops_of_avoids_reaches
                                  hdrops hnewRootValidWrite
                                  (by
                                    intro reached hreach
                                    exact
                                      RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
                                        hdrops hwriteValidStore
                                        hrootSlotWriteEnv hnewBorrowsRoot
                                        hnewRootValidWrite havoidRoot
                                        hnewGraphDisjoint hreach)
                              have hallocatedWrite :
                                  StoreOwnersAllocated
                                    (midStore.update lhsLocation
                                      { overwrittenSlot with
                                        value := .value value }) :=
                                storeOwnersAllocated_write_value_of_validValue
                                  (ValidRuntimeState.storeOwnersAllocated
                                    hvalidInner)
                                  hvalidValue hwriteStoreConcrete
                              have hrootWrite :
                                  HeapSlotsRootLifetime
                                    (midStore.update lhsLocation
                                      { overwrittenSlot with
                                        value := .value value }) :=
                                heapSlotsRootLifetime_write
                                  (ValidRuntimeState.heapSlotsRootLifetime
                                    hvalidInner)
                                  hwriteStoreConcrete
                              have hdropDisjoint :
                                  ∀ owned,
                                    owned ∈
                                      partialValuesOwningLocations
                                        [overwrittenSlot.value] →
                                    ¬ ProgramStore.Owns
                                      (midStore.update lhsLocation
                                        { overwrittenSlot with
                                          value := .value value })
                                      owned := by
                                intro owned hmem howns
                                simp [partialValuesOwningLocations] at hmem
                                have holdOwns :
                                    ProgramStore.OwnsAt midStore owned
                                      lhsLocation := by
                                  have holdValue :
                                      overwrittenSlot.value =
                                        .value (owningRef owned) :=
                                    eq_owningRef_of_mem_partialValueOwningLocations
                                      hmem
                                  exact ⟨overwrittenSlot.lifetime, by
                                    cases overwrittenSlot with
                                    | mk oldValue oldLifetime =>
                                        cases holdValue
                                        simpa [owningRef] using hlhsSlot⟩
                                rw [ProgramStore.Owns] at howns
                                rcases howns with
                                  ⟨storage, ownerLifetime,
                                    hownerSlotWrite⟩
                                by_cases hstorageLeaf :
                                    storage = lhsLocation
                                · subst storage
                                  have hnewOwnsOld :
                                      owned ∈
                                        partialValueOwningLocations
                                          (.value value) := by
                                    have hslotEq :
                                        { overwrittenSlot with
                                          value := PartialValue.value value } =
                                          StoreSlot.mk
                                            (PartialValue.value
                                              (owningRef owned))
                                            ownerLifetime := by
                                      simpa [ProgramStore.update] using
                                        hownerSlotWrite
                                    exact
                                      mem_partialValueOwningLocations_of_eq_owningRef
                                        (congrArg StoreSlot.value hslotEq)
                                  exact
                                    (ValidRuntimeState.storeTermDisjoint
                                      hvalidInner owned
                                      (by
                                        simpa [termOwningLocations,
                                          termValues,
                                          partialValueOwningLocations]
                                          using hnewOwnsOld))
                                    ⟨lhsLocation, holdOwns⟩
                                · have hownerOld :
                                      ProgramStore.OwnsAt midStore owned
                                        storage :=
                                    ⟨ownerLifetime, by
                                      simpa [ProgramStore.update,
                                        hstorageLeaf] using
                                        hownerSlotWrite⟩
                                  have hstorageEq :
                                      storage = lhsLocation :=
                                    (ValidRuntimeState.validStore hvalidInner)
                                      owned storage lhsLocation hownerOld
                                      holdOwns
                                  exact hstorageLeaf hstorageEq
                              have hallocatedFinal :
                                  StoreOwnersAllocated finalStore :=
                                drops_storeOwnersAllocated_of_disjoint
                                  hdrops hwriteValidStore hallocatedWrite
                                  hdropDisjoint
                              have hheapFinal :
                                  StoreOwnerTargetsHeap finalStore :=
                                drops_storeOwnerTargetsHeap hdrops
                                  hwriteOwnerHeap
                              have hrootFinal :
                                  HeapSlotsRootLifetime finalStore :=
                                drops_heapSlotsRootLifetime hdrops
                                  hrootWrite
                              have hvalidRuntimeFinal :
                                  ValidRuntimeState finalStore (.val .unit) :=
                                validRuntimeState_assign_step_of_postWriteDrop_invariants
                                  (lifetime := _lifetime)
                                  hvalidAssign hallocatedFinal hheapFinal
                                  hrootFinal hread hwriteStoreConcrete hdrops
                              have hrootSlotFinal :
                                  finalStore.slotAt
                                    (VariableProjection
                                      (LVal.base source.deref.deref)) =
                                    some
                                      { value := rootSlot.value,
                                        lifetime := writeEnvSlot.lifetime } :=
                                dropsAvoids_slotAt_preserved hdrops
                                  havoidRoot hrootSlotWriteEnv
                              have hsafeFinal :
                                  finalStore ∼ₛ
                                    (_env₂.update
                                      (LVal.base source.deref.deref)
                                      { ty := _updatedTy,
                                        lifetime := writeEnvSlot.lifetime }) := by
                                refine safeAbstraction_update_var_partial_of_preserved
                                  hbase hrootSlotFinal hnewRootValidFinal rfl
                                  ?domainNested ?preserveNested
                                · intro y hyBase
                                  constructor
                                  · intro hdomainStore
                                    rcases hdomainStore with
                                      ⟨slotY, hslotYFinal⟩
                                    have hslotYWrite :
                                        (midStore.update lhsLocation
                                          { overwrittenSlot with
                                            value := .value value }).slotAt
                                          (VariableProjection y) =
                                          some slotY :=
                                      drops_slotAt_of_slotAt hdrops
                                        hslotYFinal
                                    have hyLeaf :
                                        VariableProjection y ≠
                                          lhsLocation := by
                                      intro hyLeaf
                                      rcases hlhsHeap with
                                        ⟨address, hheap⟩
                                      rw [← hyLeaf] at hheap
                                      cases hheap
                                    have hslotYStore :
                                        midStore.slotAt
                                          (VariableProjection y) =
                                          some slotY := by
                                      simpa [ProgramStore.update, hyLeaf] using
                                        hslotYWrite
                                    exact (hsafeInner.1 y).mp
                                      ⟨slotY, hslotYStore⟩
                                  · intro hdomainEnv
                                    rcases hdomainEnv with
                                      ⟨otherEnvSlot, henvY⟩
                                    rcases hsafeInner.2 y otherEnvSlot
                                        henvY with
                                      ⟨oldValue, hslotY, _hvalidOld⟩
                                    have hyLeaf :
                                        VariableProjection y ≠
                                          lhsLocation := by
                                      intro hyLeaf
                                      rcases hlhsHeap with
                                        ⟨address, hheap⟩
                                      rw [← hyLeaf] at hheap
                                      cases hheap
                                    have hslotYWrite :
                                        (midStore.update lhsLocation
                                          { overwrittenSlot with
                                            value := .value value }).slotAt
                                          (VariableProjection y) =
                                          some
                                            { value := oldValue,
                                              lifetime :=
                                                otherEnvSlot.lifetime } := by
                                      simpa [ProgramStore.update, hyLeaf] using
                                        hslotY
                                    have havoidY :
                                        DropsAvoids
                                          (midStore.update lhsLocation
                                            { overwrittenSlot with
                                              value := .value value })
                                          [overwrittenSlot.value]
                                          (VariableProjection y) :=
                                      dropsAvoids_var_of_ownerTargetsHeap
                                        hdrops hwriteOwnerHeap
                                        hdropValuesHeap
                                    exact ⟨_,
                                      dropsAvoids_slotAt_preserved hdrops
                                        havoidY hslotYWrite⟩
                                · intro y otherEnvSlot hyBase henvY
                                  rcases hsafeInner.2 y otherEnvSlot henvY
                                    with ⟨oldValue, hslotY, hvalidOld⟩
                                  have hyLeaf :
                                      VariableProjection y ≠ lhsLocation := by
                                    intro hyLeaf
                                    rcases hlhsHeap with ⟨address, hheap⟩
                                    rw [← hyLeaf] at hheap
                                    cases hheap
                                  have hslotYWrite :
                                      (midStore.update lhsLocation
                                        { overwrittenSlot with
                                          value := .value value }).slotAt
                                        (VariableProjection y) =
                                        some
                                          { value := oldValue,
                                            lifetime :=
                                              otherEnvSlot.lifetime } := by
                                    simpa [ProgramStore.update, hyLeaf] using
                                      hslotY
                                  have havoidY :
                                      DropsAvoids
                                        (midStore.update lhsLocation
                                          { overwrittenSlot with
                                            value := .value value })
                                        [overwrittenSlot.value]
                                        (VariableProjection y) :=
                                    dropsAvoids_var_of_ownerTargetsHeap
                                      hdrops hwriteOwnerHeap hdropValuesHeap
                                  have hborrowsOld :
                                      PartialTyBorrowsWellFormedInSlot _env₂
                                        otherEnvSlot.lifetime
                                        otherEnvSlot.ty := by
                                    intro mutable targets hcontains
                                    exact hwellInner.1 y otherEnvSlot
                                      mutable targets henvY
                                      ⟨otherEnvSlot, henvY, hcontains⟩
                                  have hvalueHeapOld :
                                      PartialValueOwnerTargetsHeap oldValue :=
                                    partialValueOwnerTargetsHeap_of_slot
                                      (ValidRuntimeState.storeOwnerTargetsHeap
                                        hvalidInner) hslotY
                                  have hvarYNeRoot :
                                      VariableProjection y ≠
                                        VariableProjection
                                          (LVal.base source.deref.deref) := by
                                    intro hvarEq
                                    exact hyBase (by cases hvarEq; rfl)
                                  have hrootNoReachOld :
                                      ∀ reached,
                                        RuntimeFrame.Reaches midStore
                                          oldValue otherEnvSlot.ty reached →
                                        reached ≠
                                          VariableProjection
                                            (LVal.base source.deref.deref) := by
                                    intro reached hreach
                                    exact
                                      RuntimeFrame.reaches_ne_var_of_wellFormed_borrows
                                        (ValidRuntimeState.storeOwnerTargetsHeap
                                          hvalidInner)
                                        hvalueHeapOld hborrowsOld hreach
                                  have holdNoReachLeaf :
                                      ∀ reached,
                                        RuntimeFrame.Reaches midStore
                                          oldValue otherEnvSlot.ty reached →
                                        reached ≠ lhsLocation :=
                                    StoreOwnerSpine.stored_var_not_reaches_leaf_of_not_reaches_root
                                      (ValidRuntimeState.validStore hvalidInner)
                                      (ValidRuntimeState.storeOwnerTargetsHeap
                                        hvalidInner)
                                      hslotY hborrowsOld hvalidOld hspine
                                      hvarYNeRoot hrootNoReachOld
                                  have hvalidOldWrite :
                                      ValidPartialValue
                                        (midStore.update lhsLocation
                                          { overwrittenSlot with
                                            value := .value value })
                                        oldValue otherEnvSlot.ty :=
                                    RuntimeFrame.validPartialValue_update_of_not_reaches
                                      hvalidOld holdNoReachLeaf
                                  have holdGraphDisjoint :
                                      ∀ reached,
                                        RuntimeFrame.Reaches
                                          (midStore.update lhsLocation
                                            { overwrittenSlot with
                                              value := .value value })
                                          oldValue otherEnvSlot.ty reached →
                                        ∀ dropValue,
                                          dropValue ∈ [overwrittenSlot.value] →
                                          reached ∉
                                            partialValueOwningLocations
                                              dropValue := by
                                    intro reached hreach dropValue hmem
                                      howned
                                    simp at hmem
                                    subst hmem
                                    have holdOwns :
                                        ProgramStore.OwnsAt midStore
                                          reached lhsLocation := by
                                      have holdValue :
                                          overwrittenSlot.value =
                                            .value (owningRef reached) :=
                                        eq_owningRef_of_mem_partialValueOwningLocations
                                          howned
                                      exact ⟨overwrittenSlot.lifetime, by
                                        cases overwrittenSlot with
                                        | mk oldValueX oldLifetimeX =>
                                            cases holdValue
                                            simpa [owningRef] using
                                              hlhsSlot⟩
                                    rcases RuntimeFrame.reaches_owner_source_of_validPartialValue
                                        hborrowsOld hvalidOldWrite
                                        hreach with hdirect | hsource
                                    · have holdValueOwns :
                                          oldValue =
                                            .value (owningRef reached) :=
                                        eq_owningRef_of_mem_partialValueOwningLocations
                                          hdirect
                                      have hownsY :
                                          ProgramStore.OwnsAt midStore
                                            reached
                                            (VariableProjection y) :=
                                        ⟨otherEnvSlot.lifetime, by
                                          cases holdValueOwns
                                          simpa [owningRef] using
                                            hslotY⟩
                                      have hstorageEq :
                                          VariableProjection y =
                                            lhsLocation :=
                                        (ValidRuntimeState.validStore
                                          hvalidInner) reached
                                          (VariableProjection y)
                                          lhsLocation hownsY holdOwns
                                      exact hyLeaf hstorageEq
                                    · rcases hsource with
                                        ⟨storage, _hstorageReach,
                                          hownsWrite⟩
                                      rcases hownsWrite with
                                        ⟨ownerLifetime,
                                          hownerSlotWrite⟩
                                      by_cases hstorageLeaf :
                                          storage = lhsLocation
                                      · subst storage
                                        have hnewOwnsReached :
                                            PartialValue.value value =
                                              PartialValue.value
                                                (owningRef reached) := by
                                          have hslotEq :
                                              { overwrittenSlot with
                                                value :=
                                                  PartialValue.value value } =
                                                StoreSlot.mk
                                                  (PartialValue.value
                                                    (owningRef reached))
                                                  ownerLifetime := by
                                            simpa [ProgramStore.update] using
                                              hownerSlotWrite
                                          exact congrArg StoreSlot.value
                                            hslotEq
                                        have htermOwns :
                                            reached ∈
                                              termOwningLocations
                                                (.val value) := by
                                          simpa [termOwningLocations,
                                            termValues, valueOwningLocations,
                                            partialValueOwningLocations]
                                            using
                                              mem_partialValueOwningLocations_of_eq_owningRef
                                                hnewOwnsReached
                                        exact
                                          (ValidRuntimeState.storeTermDisjoint
                                            hvalidInner reached htermOwns)
                                          ⟨lhsLocation, holdOwns⟩
                                      · have hownerStore :
                                            ProgramStore.OwnsAt midStore
                                              reached storage :=
                                          ⟨ownerLifetime, by
                                            simpa [ProgramStore.update,
                                              hstorageLeaf] using
                                              hownerSlotWrite⟩
                                        have hstorageEq :
                                            storage = lhsLocation :=
                                          (ValidRuntimeState.validStore
                                            hvalidInner) reached storage
                                            lhsLocation hownerStore holdOwns
                                        exact hstorageLeaf hstorageEq
                                  have hvalidOldFinal :
                                      ValidPartialValue finalStore oldValue
                                        otherEnvSlot.ty :=
                                    RuntimeFrame.validPartialValue_drops_of_avoids_reaches
                                      hdrops hvalidOldWrite
                                      (by
                                        intro reached hreach
                                        exact
                                          RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValue
                                            hdrops hwriteValidStore
                                            hslotYWrite hborrowsOld
                                            hvalidOldWrite havoidY
                                            holdGraphDisjoint hreach)
                                  exact ⟨oldValue,
                                    dropsAvoids_slotAt_preserved hdrops
                                      havoidY hslotYWrite,
                                    hvalidOldFinal⟩
                              exact ⟨hvalidRuntimeFinal, hsafeFinal,
                                ValidPartialValue.unit⟩
                  | borrow hsourceBorrow htargets =>
                      rename_i mutable targets borrowLifetime
                      have hsourceLocation :
                          LValLocationAbstraction midStore lv
                            (.ty (.borrow mutable targets)) :=
                        lvalTyping_defined_location hwellInner hsafeInner hsourceBorrow
                      rcases hsourceLocation with
                        ⟨sourceLocation, sourceSlot, hsourceLoc, hsourceSlot,
                          hvalidBorrowSlot⟩
                      rcases sourceSlot with ⟨sourceValue, sourceLifetime⟩
                      cases hvalidBorrowSlot with
                      | @borrow selectedLocation _mutable _targets selectedTarget
                          htargetMem htargetLocFromBorrow =>
                          have hlhsLocFromBorrow :
                              midStore.loc lv.deref = some selectedLocation := by
                            simp [ProgramStore.loc, hsourceLoc, hsourceSlot]
                          have hselectedLocationEq : selectedLocation = lhsLocation := by
                            rw [hlhsLoc] at hlhsLocFromBorrow
                            exact (Option.some.inj hlhsLocFromBorrow).symm
                          subst hselectedLocationEq
                          have hsourceWellTy :
                              WellFormedTy _env₂ (.borrow mutable targets) _lifetime :=
                            LValTyping.fullTyWellFormed hwellInner hsourceBorrow
                          cases hsourceWellTy with
                          | borrow hborrowTargets =>
                              cases hborrowTargets with
                              | intro hborrowTargets =>
                              rcases hborrowTargets selectedTarget htargetMem with
                                ⟨selectedTy, selectedLifetime, htargetTyping,
                                  _htargetOutlives, _htargetBase, htargetVar⟩
                              cases selectedTarget with
                              | var selectedName =>
                                  have hselectedRead :
                                      midStore.read (.var selectedName) =
                                        some overwrittenSlot := by
                                    have hselectedLoc :
                                        midStore.loc (.var selectedName) =
                                          some selectedLocation := by
                                      simpa using htargetLocFromBorrow
                                    simp [ProgramStore.read, hselectedLoc, hlhsSlot]
                                  have hselectedWrite :
                                      midStore.write (.var selectedName)
                                          (.value value) =
                                        some
                                          (midStore.update selectedLocation
                                            { overwrittenSlot with value := .value value }) := by
                                    have hselectedLoc :
                                        midStore.loc (.var selectedName) =
                                          some selectedLocation := by
                                      simpa using htargetLocFromBorrow
                                    simp [ProgramStore.write, hselectedLoc, hlhsSlot]
                                  rcases lvalTargetsTyping_member_strengthens
                                      htargets (.var selectedName) htargetMem with
                                    ⟨memberTy, memberLifetime, hmemberTyping,
                                      hmemberStrength⟩
                                  rcases LValTyping.var_inv hmemberTyping with
                                    ⟨selectedEnvSlot, hselectedEnvSlot,
                                      _hselectedTyEq, _hselectedLifetimeEq⟩
                                  let selectedStrongEnv :=
                                    _env₂.update selectedName
                                      { selectedEnvSlot with ty := .ty _rhsTy }
                                  have hselectedStrongWrite :
                                      EnvWrite 0 _env₂ (.var selectedName)
                                        _rhsTy selectedStrongEnv := by
                                    dsimp [selectedStrongEnv]
                                    exact EnvWrite.intro hselectedEnvSlot
                                      UpdateAtPath.strong
                                  have hselectedShape :
                                      ShapeCompatible _env₂
                                        (.ty memberTy) (.ty _rhsTy) :=
                                    ShapeCompatible.ty_left_of_strengthens
                                      hmemberStrength hshape
                                  have hdropsSelected :
                                      Drops
                                        (midStore.update selectedLocation
                                          { overwrittenSlot with value := .value value })
                                        [overwrittenSlot.value] finalStore := by
                                    rwa [hwriteStoreEq] at hdrops
                                  have hselectedStep :
                                      Step midStore _lifetime
                                        (Term.assign (.var selectedName) (.val value))
                                        finalStore (.val .unit) :=
                                    Step.assign hselectedRead hselectedWrite hdropsSelected
                                  have hselectedTerminal :
                                      TerminalStateSafe finalStore .unit
                                        selectedStrongEnv .unit :=
                                    preservation_assign_var_step_runtime_of_wellFormed
                                      hwellInner hsafeInner
                                      (validRuntimeState_assign_value_of_value
                                        (lhs := .var selectedName) hvalidInner)
                                      hmemberTyping hselectedShape hwellTy
                                      hselectedStrongWrite hvalidValue
                                      hselectedStep
                                  have hpathSelected :
                                      PathSelected _env₂
                                        (.ty (.borrow mutable targets)) [()]
                                        selectedName selectedEnvSlot memberTy :=
                                    PathSelected.borrowHere htargetMem
                                      hselectedEnvSlot _hselectedTyEq
                                  rcases hwellInner.2.2.2 with ⟨φ, hφ⟩
                                  have hmap :
                                      EnvSameShapeStrengthening
                                        selectedStrongEnv _env₃ := by
                                    dsimp [selectedStrongEnv]
                                    exact
                                      EnvWrite.selected_path_map
                                        (φ := φ) hφ hsourceBorrow
                                        hpathSelected
                                        (by simpa [prependPath] using hwrite)
                                  exact TerminalStateSafe.transport_sameShape
                                    hselectedTerminal hmap.1 hmap.2
                              | deref selectedSource =>
                                  cases htargetVar
        exact ⟨hwellOut, hterminal⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm _ih
        htypingEq hsource outerLifetime store finalStore finalValue hchild hvalidRuntime
        hvalidStoreTyping hwellFormed hsafe hdropSafe hwellTy hmulti =>
      by
        cases htypingEq
        rcases multistep_block_head_to_value_inv hmulti with
          ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
        rcases _ih rfl (SourceTerm.block_head hsource) store midStore value
            (validRuntimeState_block_singleton_inner hvalidRuntime)
            (validStoreTyping_block_singleton_inner hvalidStoreTyping)
            hwellFormed hsafe hinnerMulti with
          ⟨hwellInner, hterminalInner⟩
        exact preservation_blockB_value_multistep_runtime_of_envDropSafe
          (validRuntimeState_block_singleton_value_of_value hterminalInner.1)
          hterminalInner.2.1 hchild hdropSafe hwellInner hwellTy
          hterminalInner.2.2 hblockValueMulti)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm hnonOwner hrest _ihHead _ihRest
        htypingEq hsource outerLifetime store finalStore finalValue hchild
        hvalidRuntime hvalidStoreTyping hwellFormed hsafe hdropSafe hwellTy hmulti =>
      by
        cases htypingEq
        cases _rest with
        | nil =>
            cases hrest
        | cons next restTail =>
            have hsourceHead : SourceTerm _term :=
              SourceTerm.block_head hsource
            have hsourceTail : SourceTerm (.block _lifetime (next :: restTail)) :=
              SourceTerm.block_tail hsource
            rcases multistep_block_head_to_value_inv hmulti with
              ⟨midStore, value, hinnerMulti, hblockValueMulti⟩
            rcases _ihHead rfl hsourceHead store midStore value
                (validRuntimeState_block_head hvalidRuntime)
                (validStoreTyping_block_head hvalidStoreTyping)
                hwellFormed hsafe hinnerMulti with
              ⟨hwellInner, hterminalInner⟩
            have hvalueNonOwner : valueOwnedLocation? value = none :=
              validValue_nonOwner_of_nonOwnerTy hnonOwner hterminalInner.2.2
            have hvalueBlockValid :
                ValidRuntimeState midStore
                  (.block _lifetime (.val value :: next :: restTail)) :=
              validRuntimeState_block_value_cons_of_value_source_tail
                hsourceTail hterminalInner.1
            have htailStoreTypingAtMid :
                ValidStoreTyping midStore (.block _lifetime (next :: restTail)) typing :=
              validStoreTyping_sourceTerm_of_validStoreTyping hsourceTail
                (validStoreTyping_block_tail_of_cons hvalidStoreTyping)
            exact preservation_block_terminal_multistep_runtime_of_first_step
              (env' := _env₃.dropLifetime _lifetime) (ty := _finalTy)
              (by
                intro seqValue seqNext seqRest storeAfter hterms hdrops htailMulti
                cases hterms
                have hseqStep :
                    Step midStore outerLifetime
                      (.block _lifetime (.val value :: next :: restTail))
                      storeAfter (.block _lifetime (next :: restTail)) :=
                  Step.seq hdrops
                rcases preservation_seq_nonOwner_step_runtime hvalueNonOwner
                    hterminalInner.2.1 hvalueBlockValid hseqStep with
                  ⟨hvalidTailAfter, hsafeTailAfter⟩
                have hstoreAfter : storeAfter = midStore :=
                  drops_value_nonOwner_eq hvalueNonOwner hdrops
                have htailStoreTyping :
                    ValidStoreTyping storeAfter (.block _lifetime (next :: restTail)) typing := by
                  rw [hstoreAfter]
                  exact htailStoreTypingAtMid
                exact _ihRest rfl hsourceTail outerLifetime storeAfter finalStore
                  finalValue hchild hvalidTailAfter htailStoreTyping hwellInner
                  hsafeTailAfter hdropSafe hwellTy htailMulti)
              (by
                intro blockTerm blockRest storeAfter termAfter hterms hstep _htailMulti
                cases hterms
                exact False.elim (value_no_step hstep))
              (by
                intro blockValue storeAfter hterms _hdrops _htailMulti
                cases hterms)
              hblockValueMulti)
    htyping rfl hsource store finalStore finalValue hvalidRuntime hvalidStoreTyping hwellFormed
    hsafe hmulti).2

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
