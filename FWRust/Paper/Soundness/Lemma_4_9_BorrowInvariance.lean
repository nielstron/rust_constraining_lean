import FWRust.Paper.Soundness.Lemma_4_10_Progress

/-!
# Lemma 4.9 (Borrow Invariance)

Single-target Phase D1 support.  The obsolete target-list join and fan-out
machinery has been removed from this file.
-/

namespace FWRust
namespace Paper

open Core

def FullTerminalStateSafe (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) :
    Prop :=
  ValidRuntimeState store (.val value) ∧
    FullSafeAbstraction store env ∧
    ValidValue store value ty

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

theorem TerminalStateSafe.full_of_wellFormed {store : ProgramStore}
    {value : Value} {env : Env} {ty : Ty} {lifetime : Lifetime} :
    TerminalStateSafe store value env ty →
    WellFormedEnv env lifetime →
    WellFormedTy env ty lifetime →
    FullTerminalStateSafe store value env ty := by
  intro hterminal hwell hwellTy
  exact ⟨hterminal.1,
    SafeAbstraction.full_of_containedBorrowsWellFormed hwell.1
      hterminal.2.1,
    hterminal.2.2.toFull_of_borrowsWellFormed
      (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)⟩

theorem FullTerminalStateSafe.transport_env_pointwise
    {store : ProgramStore} {value : Value} {env result : Env} {ty : Ty}
    (heq : ∀ y, result.slotAt y = env.slotAt y) :
    FullTerminalStateSafe store value env ty →
    FullTerminalStateSafe store value result ty := by
  intro hterminal
  exact ⟨hterminal.1,
    FullSafeAbstraction.transport_pointwise heq hterminal.2.1,
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
    · have hresult : result.slotAt y = some slot := by
        simpa [Env.update, hy] using hslot
      exact hmap.1 y slot hresult
  · intro y slot hslot
    rcases hmap.2 y slot hslot with ⟨resultSlot', hresultSlot', hlife⟩
    by_cases hy : y = x
    · subst hy
      have hslotEq : slot = sourceSlot := by
        exact Option.some.inj (hslot.symm.trans hsourceSlot)
      subst hslotEq
      exact ⟨resultSlot, by simp [Env.update], hlifetime⟩
    · exact ⟨resultSlot', by simpa [Env.update, hy] using hresultSlot', hlife⟩

theorem EnvSameShapeStrengthening.update_same {source result : Env}
    {x : Name} {slot : EnvSlot} {newTy : PartialTy} :
    EnvSameShapeStrengthening source result →
    result.slotAt x = some slot →
    PartialTyStrengthens slot.ty newTy →
    PartialTy.sameShape slot.ty newTy →
    EnvSameShapeStrengthening source (result.update x { slot with ty := newTy }) := by
  intro hmap hslot hstrength hshape
  rcases hmap.1 x slot hslot with
    ⟨sourceSlot, hsourceSlot, hlife, hsourceStrength, hsourceShape⟩
  exact EnvSameShapeStrengthening.update_result_strengthening hmap hsourceSlot hlife
    (partialTyStrengthens_trans hsourceStrength hstrength)
    (PartialTy.sameShape_trans hsourceShape hshape)

def StoreTypingRefsWellFormed
    (env : Env) (typing : StoreTyping) (lifetime : Lifetime) : Prop :=
  ∀ (ref : Reference) (ty : Ty),
    typing.tyOf ref.location = some ty →
    WellFormedTy env ty lifetime

theorem valueTyping_result_wellFormed_of_refs {env : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty} :
    StoreTypingRefsWellFormed env typing lifetime →
    ValueTyping typing value ty →
    WellFormedTy env ty lifetime := by
  intro hrefs htyping
  cases htyping with
  | unit | int => constructor
  | ref hlookup => exact hrefs _ _ hlookup

@[simp] theorem storeTypingRefsWellFormed_empty (env : Env) (lifetime : Lifetime) :
    StoreTypingRefsWellFormed env StoreTyping.empty lifetime := by
  intro ref ty hlookup
  simp [StoreTyping.empty, StoreTyping.tyOf] at hlookup

end Paper
end FWRust
