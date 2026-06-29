import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
# Coherence rejection examples

Small examples around the coherence invariant that do not depend on the main
soundness wrapper.  These are useful while the source-level coherence theorem is
being rebuilt: they show which plausible counterexamples are rejected by the
existing typing premises.
-/

namespace LwRust
namespace Paper

open Core

def nestedIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def nestedBoolSlot : EnvSlot :=
  { ty := .ty .bool, lifetime := Lifetime.root }

def nestedBxSlot : EnvSlot :=
  { ty := .ty (.borrow false [.var "x"]), lifetime := Lifetime.root }

def nestedBySlot : EnvSlot :=
  { ty := .ty (.borrow false [.var "y"]), lifetime := Lifetime.root }

def nestedZSlot : EnvSlot :=
  { ty := .ty (.borrow false [.var "bx", .var "by"]),
    lifetime := Lifetime.root }

def nestedBorrowEnv : Env :=
  (((Env.empty.update "x" nestedIntSlot).update "y" nestedBoolSlot).update
    "bx" nestedBxSlot).update "by" nestedBySlot

def nestedBorrowEnvZ : Env :=
  nestedBorrowEnv.update "z" nestedZSlot

theorem nestedBorrowEnvZ_x_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping nestedBorrowEnvZ (.var "x") (.ty ty) lifetime →
    ty = .int := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hslotEq : slot = nestedIntSlot := by
    have hx : nestedBorrowEnvZ.slotAt "x" = some nestedIntSlot := by
      simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot, nestedBoolSlot,
        nestedBxSlot, nestedBySlot, nestedZSlot, Env.update]
    exact Option.some.inj (hslot.symm.trans hx)
  subst hslotEq
  simpa [nestedIntSlot] using hslotTy.symm

theorem nestedBorrowEnvZ_y_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping nestedBorrowEnvZ (.var "y") (.ty ty) lifetime →
    ty = .bool := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hslotEq : slot = nestedBoolSlot := by
    have hy : nestedBorrowEnvZ.slotAt "y" = some nestedBoolSlot := by
      simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot, nestedBoolSlot,
        nestedBxSlot, nestedBySlot, nestedZSlot, Env.update]
    exact Option.some.inj (hslot.symm.trans hy)
  subst hslotEq
  simpa [nestedBoolSlot] using hslotTy.symm

theorem nestedBorrowEnvZ_bx_typing :
    LValTyping nestedBorrowEnvZ (.var "bx")
      (.ty (.borrow false [.var "x"])) Lifetime.root := by
  exact LValTyping.var (env := nestedBorrowEnvZ) (x := "bx")
    (slot := nestedBxSlot) (by
      simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot, nestedBoolSlot,
        nestedBxSlot, nestedBySlot, nestedZSlot, Env.update])

theorem nestedBorrowEnvZ_by_typing :
    LValTyping nestedBorrowEnvZ (.var "by")
      (.ty (.borrow false [.var "y"])) Lifetime.root := by
  exact LValTyping.var (env := nestedBorrowEnvZ) (x := "by")
    (slot := nestedBySlot) (by
      simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot, nestedBoolSlot,
        nestedBxSlot, nestedBySlot, nestedZSlot, Env.update])

theorem nestedBorrowEnvZ_z_typing :
    LValTyping nestedBorrowEnvZ (.var "z")
      (.ty (.borrow false [.var "bx", .var "by"])) Lifetime.root := by
  exact LValTyping.var (env := nestedBorrowEnvZ) (x := "z")
    (slot := nestedZSlot) (by
      simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedZSlot, Env.update])

theorem nested_borrow_pair_join :
    PartialTyJoin (.ty (.borrow false [.var "x"]))
      (.ty (.borrow false [.var "y"]))
      (.ty (.borrow false [.var "x", .var "y"])) := by
  constructor
  · intro candidate hcandidate
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact PartialTyStrengthens.borrow (by
        intro target htarget
        have htargetEq : target = .var "x" := by simpa using htarget
        subst htargetEq
        simp)
    · exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget
        subst htarget
        simp)
  · intro upper hupper
    have hx :
        PartialTyStrengthens (.ty (.borrow false [.var "x"])) upper :=
      hupper (.ty (.borrow false [.var "x"])) (by simp)
    have hy :
        PartialTyStrengthens (.ty (.borrow false [.var "y"])) upper :=
      hupper (.ty (.borrow false [.var "y"])) (by simp)
    cases upper with
    | ty upperTy =>
        rcases PartialTyStrengthens.from_borrow_inv hx with
          ⟨upperTargets, hupperEq, hxSubset⟩
        subst hupperEq
        rcases PartialTyStrengthens.from_borrow_inv hy with
          ⟨rightTargets, hrightEq, hySubset⟩
        injection hrightEq with _hmut htargets
        subst htargets
        exact PartialTyStrengthens.borrow (by
          intro target htarget
          simp at htarget
          rcases htarget with rfl | htarget
          · exact hxSubset (by simp)
          · subst htarget
            exact hySubset (by simp))
    | undef upperTy =>
        have hxTy :
            PartialTyStrengthens (.ty (.borrow false [.var "x"]))
              (.ty upperTy) :=
          PartialTyStrengthens.ty_to_undef_inv hx
        have hyTy :
            PartialTyStrengthens (.ty (.borrow false [.var "y"]))
              (.ty upperTy) :=
          PartialTyStrengthens.ty_to_undef_inv hy
        rcases PartialTyStrengthens.from_borrow_inv hxTy with
          ⟨upperTargets, hupperEq, hxSubset⟩
        subst hupperEq
        rcases PartialTyStrengthens.from_borrow_inv hyTy with
          ⟨rightTargets, hrightEq, hySubset⟩
        injection hrightEq with _hmut htargets
        subst htargets
        exact PartialTyStrengthens.intoUndef
          (PartialTyStrengthens.borrow (by
            intro target htarget
            simp at htarget
            rcases htarget with rfl | htarget
            · exact hxSubset (by simp)
            · subst htarget
              exact hySubset (by simp)))
    | box _ =>
        exact False.elim (PartialTyStrengthens.not_ty_to_box hx)

theorem nestedBorrowEnvZ_bx_by_targets_typing :
    LValTargetsTyping nestedBorrowEnvZ [.var "bx", .var "by"]
      (.ty (.borrow false [.var "x", .var "y"])) Lifetime.root := by
  exact LValTargetsTyping.cons nestedBorrowEnvZ_bx_typing
    (LValTargetsTyping.singleton nestedBorrowEnvZ_by_typing)
    nested_borrow_pair_join
    (LifetimeIntersection.self Lifetime.root)

theorem nestedBorrowEnvZ_deref_z_typing :
    LValTyping nestedBorrowEnvZ (.deref (.var "z"))
      (.ty (.borrow false [.var "x", .var "y"])) Lifetime.root := by
  exact LValTyping.borrow nestedBorrowEnvZ_z_typing
    nestedBorrowEnvZ_bx_by_targets_typing

theorem nestedBorrowEnvZ_xy_not_targets_typing :
    ¬ ∃ ty lifetime,
      LValTargetsTyping nestedBorrowEnvZ [.var "x", .var "y"]
        (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htargets⟩
  rcases lvalTargetsTyping_member_strengthens htargets (.var "x") (by simp) with
    ⟨xTy, xLifetime, hxTyping, hxStrength⟩
  rcases lvalTargetsTyping_member_strengthens htargets (.var "y") (by simp) with
    ⟨yTy, yLifetime, hyTyping, hyStrength⟩
  have hxTy : xTy = .int := nestedBorrowEnvZ_x_typing_inv hxTyping
  have hyTy : yTy = .bool := nestedBorrowEnvZ_y_typing_inv hyTyping
  subst hxTy
  subst hyTy
  cases hxStrength with
  | reflex =>
      cases hyStrength

theorem nestedBorrowEnvZ_not_coherent :
    ¬ Coherent nestedBorrowEnvZ := by
  intro hcoherent
  rcases hcoherent (.deref (.var "z")) false [.var "x", .var "y"]
      Lifetime.root nestedBorrowEnvZ_deref_z_typing with
    ⟨ty, lifetime, htargets⟩
  exact nestedBorrowEnvZ_xy_not_targets_typing ⟨ty, lifetime, htargets⟩

/--
Slot-local coherence is not enough.  The `z` slot is coherent in the weak
`EnvTypesCoherent` sense because `[bx, by]` is jointly typed as
`&[x, y]`; the environment still fails lvalue-facing `Coherent` when that output
borrow is dereferenced.
-/
theorem nestedBorrowEnvZ_envTypesCoherent :
    EnvTypesCoherent nestedBorrowEnvZ := by
  intro name slot hslot mutable targets hcontains
  by_cases hz : name = "z"
  · subst hz
    have hslotExpected :
        nestedBorrowEnvZ.slotAt "z" = some nestedZSlot := by
      simp [nestedBorrowEnvZ, nestedZSlot, Env.update]
    have hslotEq : slot = nestedZSlot :=
      Option.some.inj (hslot.symm.trans hslotExpected)
    subst hslotEq
    cases hcontains with
    | here =>
        exact ⟨.borrow false [.var "x", .var "y"], Lifetime.root,
          nestedBorrowEnvZ_bx_by_targets_typing⟩
  · by_cases hby : name = "by"
    · subst hby
      have hslotExpected :
          nestedBorrowEnvZ.slotAt "by" = some nestedBySlot := by
        simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedBySlot, nestedZSlot,
          Env.update]
      have hslotEq : slot = nestedBySlot :=
        Option.some.inj (hslot.symm.trans hslotExpected)
      subst hslotEq
      cases hcontains with
      | here =>
          exact ⟨.bool, Lifetime.root,
            LValTargetsTyping.singleton
              (LValTyping.var (env := nestedBorrowEnvZ) (x := "y")
                (slot := nestedBoolSlot) (by
                  simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot,
                    nestedBoolSlot, nestedBxSlot, nestedBySlot, nestedZSlot,
                    Env.update]))⟩
    · by_cases hbx : name = "bx"
      · subst hbx
        have hslotExpected :
            nestedBorrowEnvZ.slotAt "bx" = some nestedBxSlot := by
          simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedBxSlot, nestedBySlot,
            nestedZSlot, Env.update]
        have hslotEq : slot = nestedBxSlot :=
          Option.some.inj (hslot.symm.trans hslotExpected)
        subst hslotEq
        cases hcontains with
        | here =>
            exact ⟨.int, Lifetime.root,
              LValTargetsTyping.singleton
                (LValTyping.var (env := nestedBorrowEnvZ) (x := "x")
                  (slot := nestedIntSlot) (by
                    simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot,
                      nestedBoolSlot, nestedBxSlot, nestedBySlot, nestedZSlot,
                      Env.update]))⟩
      · by_cases hy : name = "y"
        · subst hy
          have hslotExpected :
              nestedBorrowEnvZ.slotAt "y" = some nestedBoolSlot := by
            simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot,
              nestedBoolSlot, nestedBxSlot, nestedBySlot, nestedZSlot,
              Env.update]
          have hslotEq : slot = nestedBoolSlot :=
            Option.some.inj (hslot.symm.trans hslotExpected)
          subst hslotEq
          cases hcontains
        · by_cases hx : name = "x"
          · subst hx
            have hslotExpected :
                nestedBorrowEnvZ.slotAt "x" = some nestedIntSlot := by
              simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot,
                nestedBoolSlot, nestedBxSlot, nestedBySlot, nestedZSlot,
                Env.update]
            have hslotEq : slot = nestedIntSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst hslotEq
            cases hcontains
          · have hnone : nestedBorrowEnvZ.slotAt name = none := by
              simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot,
                nestedBoolSlot, nestedBxSlot, nestedBySlot, nestedZSlot,
                Env.update, Env.empty, hz, hby, hbx, hy, hx]
            rw [hnone] at hslot
            cases hslot

def nestedBorrowRank (name : Name) : Nat :=
  if name = "z" then 2 else if name = "bx" ∨ name = "by" then 1 else 0

theorem nestedBorrowEnvZ_linearizedBy :
    LinearizedBy nestedBorrowRank nestedBorrowEnvZ := by
  intro name slot hslot v hv
  by_cases hz : name = "z"
  · subst hz
    have hslotExpected :
        nestedBorrowEnvZ.slotAt "z" = some nestedZSlot := by
      simp [nestedBorrowEnvZ, nestedZSlot, Env.update]
    have hslotEq : slot = nestedZSlot :=
      Option.some.inj (hslot.symm.trans hslotExpected)
    subst hslotEq
    simp [nestedBorrowRank, nestedZSlot, PartialTy.vars, Ty.vars] at hv ⊢
    rcases hv with hv | hv
    · subst hv
      decide
    · subst hv
      decide
  · by_cases hby : name = "by"
    · subst hby
      have hslotExpected :
          nestedBorrowEnvZ.slotAt "by" = some nestedBySlot := by
        simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedBySlot, nestedZSlot,
          Env.update]
      have hslotEq : slot = nestedBySlot :=
        Option.some.inj (hslot.symm.trans hslotExpected)
      subst hslotEq
      simp [nestedBorrowRank, nestedBySlot, PartialTy.vars, Ty.vars]
        at hv ⊢
      subst hv
      decide
    · by_cases hbx : name = "bx"
      · subst hbx
        have hslotExpected :
            nestedBorrowEnvZ.slotAt "bx" = some nestedBxSlot := by
          simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedBxSlot, nestedBySlot,
            nestedZSlot, Env.update]
        have hslotEq : slot = nestedBxSlot :=
          Option.some.inj (hslot.symm.trans hslotExpected)
        subst hslotEq
        simp [nestedBorrowRank, nestedBxSlot, PartialTy.vars, Ty.vars]
          at hv ⊢
        subst hv
        decide
      · by_cases hy : name = "y"
        · subst hy
          have hslotExpected :
              nestedBorrowEnvZ.slotAt "y" = some nestedBoolSlot := by
            simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot,
              nestedBoolSlot, nestedBxSlot, nestedBySlot, nestedZSlot,
              Env.update]
          have hslotEq : slot = nestedBoolSlot :=
            Option.some.inj (hslot.symm.trans hslotExpected)
          subst hslotEq
          simp [nestedBoolSlot, PartialTy.vars, Ty.vars] at hv
        · by_cases hx : name = "x"
          · subst hx
            have hslotExpected :
                nestedBorrowEnvZ.slotAt "x" = some nestedIntSlot := by
              simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot,
                nestedBoolSlot, nestedBxSlot, nestedBySlot, nestedZSlot,
                Env.update]
            have hslotEq : slot = nestedIntSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst hslotEq
            simp [nestedIntSlot, PartialTy.vars, Ty.vars] at hv
          · have hnone : nestedBorrowEnvZ.slotAt name = none := by
              simp [nestedBorrowEnvZ, nestedBorrowEnv, nestedIntSlot,
                nestedBoolSlot, nestedBxSlot, nestedBySlot, nestedZSlot,
                Env.update, Env.empty, hz, hby, hbx, hy, hx]
            rw [hnone] at hslot
            cases hslot

theorem nestedBorrowEnvZ_linearizable_and_slotCoherent_not_coherent :
    Linearizable nestedBorrowEnvZ ∧ EnvTypesCoherent nestedBorrowEnvZ ∧
      ¬ Coherent nestedBorrowEnvZ := by
  exact ⟨⟨nestedBorrowRank, nestedBorrowEnvZ_linearizedBy⟩,
    nestedBorrowEnvZ_envTypesCoherent, nestedBorrowEnvZ_not_coherent⟩

/-! ### Same-shape growth is not a coherence source. -/

def shapeOnlyBSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "x"]), lifetime := Lifetime.root }

def shapeOnlyBXYSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "x", .var "y"]),
    lifetime := Lifetime.root }

def shapeOnlyBaseEnv : Env :=
  (Env.empty.update "x" nestedIntSlot).update "y" nestedBoolSlot

def shapeOnlySourceEnv : Env :=
  shapeOnlyBaseEnv.update "b" shapeOnlyBSlot

def shapeOnlyResultEnv : Env :=
  shapeOnlyBaseEnv.update "b" shapeOnlyBXYSlot

theorem shapeOnly_source_x_typing :
    LValTyping shapeOnlySourceEnv (.var "x") (.ty .int) Lifetime.root := by
  exact LValTyping.var (env := shapeOnlySourceEnv) (x := "x")
    (slot := nestedIntSlot) (by
      simp [shapeOnlySourceEnv, shapeOnlyBaseEnv, shapeOnlyBSlot,
        nestedIntSlot, nestedBoolSlot, Env.update])

theorem shapeOnly_source_x_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping shapeOnlySourceEnv (.var "x") (.ty ty) lifetime →
    ty = .int := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hslotEq : slot = nestedIntSlot := by
    have hx : shapeOnlySourceEnv.slotAt "x" = some nestedIntSlot := by
      simp [shapeOnlySourceEnv, shapeOnlyBaseEnv, shapeOnlyBSlot,
        nestedIntSlot, nestedBoolSlot, Env.update]
    exact Option.some.inj (hslot.symm.trans hx)
  subst hslotEq
  simpa [nestedIntSlot] using hslotTy.symm

theorem shapeOnly_source_y_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping shapeOnlySourceEnv (.var "y") (.ty ty) lifetime →
    ty = .bool := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hslotEq : slot = nestedBoolSlot := by
    have hy : shapeOnlySourceEnv.slotAt "y" = some nestedBoolSlot := by
      simp [shapeOnlySourceEnv, shapeOnlyBaseEnv, shapeOnlyBSlot,
        nestedIntSlot, nestedBoolSlot, Env.update]
    exact Option.some.inj (hslot.symm.trans hy)
  subst hslotEq
  simpa [nestedBoolSlot] using hslotTy.symm

theorem shapeOnly_result_x_typing :
    LValTyping shapeOnlyResultEnv (.var "x") (.ty .int) Lifetime.root := by
  exact LValTyping.var (env := shapeOnlyResultEnv) (x := "x")
    (slot := nestedIntSlot) (by
      simp [shapeOnlyResultEnv, shapeOnlyBaseEnv, shapeOnlyBXYSlot,
        nestedIntSlot, nestedBoolSlot, Env.update])

theorem shapeOnly_result_y_typing :
    LValTyping shapeOnlyResultEnv (.var "y") (.ty .bool) Lifetime.root := by
  exact LValTyping.var (env := shapeOnlyResultEnv) (x := "y")
    (slot := nestedBoolSlot) (by
      simp [shapeOnlyResultEnv, shapeOnlyBaseEnv, shapeOnlyBXYSlot,
        nestedIntSlot, nestedBoolSlot, Env.update])

theorem shapeOnly_result_b_typing :
    LValTyping shapeOnlyResultEnv (.var "b")
      (.ty (.borrow true [.var "x", .var "y"])) Lifetime.root := by
  exact LValTyping.var (env := shapeOnlyResultEnv) (x := "b")
    (slot := shapeOnlyBXYSlot) (by
      simp [shapeOnlyResultEnv, shapeOnlyBXYSlot, Env.update])

theorem shapeOnly_source_typing_cases {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    LValTyping shapeOnlySourceEnv lv partialTy lifetime →
      (lv = .var "x" ∧ partialTy = .ty .int) ∨
      (lv = .var "y" ∧ partialTy = .ty .bool) ∨
      (lv = .var "b" ∧ partialTy = .ty (.borrow true [.var "x"])) ∨
      (lv = .deref (.var "b") ∧ partialTy = .ty .int) := by
  intro htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _lifetime _ =>
      (lv = .var "x" ∧ partialTy = .ty .int) ∨
      (lv = .var "y" ∧ partialTy = .ty .bool) ∨
      (lv = .var "b" ∧ partialTy = .ty (.borrow true [.var "x"])) ∨
      (lv = .deref (.var "b") ∧ partialTy = .ty .int))
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping
  case var =>
      intro name slot hslot
      by_cases hb : name = "b"
      · subst hb
        have hslotExpected :
            shapeOnlySourceEnv.slotAt "b" = some shapeOnlyBSlot := by
          simp [shapeOnlySourceEnv, shapeOnlyBSlot, Env.update]
        have hslotEq : slot = shapeOnlyBSlot :=
          Option.some.inj (hslot.symm.trans hslotExpected)
        subst hslotEq
        right; right; left
        exact ⟨rfl, rfl⟩
      · by_cases hx : name = "x"
        · subst hx
          have hslotExpected :
              shapeOnlySourceEnv.slotAt "x" = some nestedIntSlot := by
            simp [shapeOnlySourceEnv, shapeOnlyBaseEnv, shapeOnlyBSlot,
              nestedIntSlot, nestedBoolSlot, Env.update]
          have hslotEq : slot = nestedIntSlot :=
            Option.some.inj (hslot.symm.trans hslotExpected)
          subst hslotEq
          left
          exact ⟨rfl, rfl⟩
        · by_cases hy : name = "y"
          · subst hy
            have hslotExpected :
                shapeOnlySourceEnv.slotAt "y" = some nestedBoolSlot := by
              simp [shapeOnlySourceEnv, shapeOnlyBaseEnv, shapeOnlyBSlot,
                nestedIntSlot, nestedBoolSlot, Env.update]
            have hslotEq : slot = nestedBoolSlot :=
              Option.some.inj (hslot.symm.trans hslotExpected)
            subst hslotEq
            right; left
            exact ⟨rfl, rfl⟩
          · have hnone : shapeOnlySourceEnv.slotAt name = none := by
              simp [shapeOnlySourceEnv, shapeOnlyBaseEnv, shapeOnlyBSlot,
                nestedIntSlot, nestedBoolSlot, Env.update, Env.empty, hb, hx, hy]
            rw [hnone] at hslot
            cases hslot
  case box =>
      intro _source _inner _lifetime _hsource ih
      rcases ih with
        ⟨_hlv, hpartialTy⟩ |
        ⟨_hlv, hpartialTy⟩ |
        ⟨_hlv, hpartialTy⟩ |
        ⟨_hlv, hpartialTy⟩ <;> cases hpartialTy
  case borrow =>
      intro _source _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hsource htargets ihSource _ihTargets
      rcases ihSource with
        ⟨_hlv, hpartialTy⟩ |
        ⟨_hlv, hpartialTy⟩ |
        ⟨hlv, hpartialTy⟩ |
        ⟨_hlv, hpartialTy⟩
      · cases hpartialTy
      · cases hpartialTy
      · cases hpartialTy
        subst hlv
        rcases LValTargetsTyping.output_full htargets with
          ⟨outTy, houtTy⟩
        subst houtTy
        rcases lvalTargetsTyping_member_strengthens htargets
            (.var "x") (by simp) with
          ⟨targetTy, _targetLifetime, htargetTyping, hstrength⟩
        rcases LValTyping.var_inv htargetTyping with
          ⟨slot, hslot, hslotTy, _htargetLifetime⟩
        have hslotExpected :
            shapeOnlySourceEnv.slotAt "x" = some nestedIntSlot := by
          simp [shapeOnlySourceEnv, shapeOnlyBaseEnv, shapeOnlyBSlot,
            nestedIntSlot, nestedBoolSlot, Env.update]
        have hslotEq : slot = nestedIntSlot :=
          Option.some.inj (hslot.symm.trans hslotExpected)
        subst hslotEq
        have htargetTy : targetTy = .int := by
          simpa [nestedIntSlot] using hslotTy.symm
        subst htargetTy
        have htargetPartial : outTy = .int :=
          PartialTyStrengthens.from_int_inv hstrength
        subst htargetPartial
        right; right; right
        exact ⟨rfl, rfl⟩
      · cases hpartialTy
  case singleton =>
      intros
      trivial
  case cons =>
      intros
      trivial

theorem shapeOnlySourceEnv_coherent : Coherent shapeOnlySourceEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases shapeOnly_source_typing_cases htyping with
    ⟨_hlv, hpartialTy⟩ |
    ⟨_hlv, hpartialTy⟩ |
    ⟨_hlv, hpartialTy⟩ |
    ⟨_hlv, hpartialTy⟩
  · cases hpartialTy
  · cases hpartialTy
  · injection hpartialTy with hborrow
    injection hborrow with hmutable htargets
    subst hmutable
    subst htargets
    exact ⟨.int, Lifetime.root,
      LValTargetsTyping.singleton shapeOnly_source_x_typing⟩
  · cases hpartialTy

theorem shapeOnlySourceEnv_xy_not_targets_typing :
    ¬ ∃ ty lifetime,
      LValTargetsTyping shapeOnlySourceEnv [.var "x", .var "y"]
        (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htargets⟩
  rcases lvalTargetsTyping_member_strengthens htargets (.var "x") (by simp) with
    ⟨xTy, _xLifetime, hxTyping, hxStrength⟩
  rcases lvalTargetsTyping_member_strengthens htargets (.var "y") (by simp) with
    ⟨yTy, _yLifetime, hyTyping, hyStrength⟩
  have hxTy : xTy = .int := shapeOnly_source_x_typing_inv hxTyping
  have hyTy : yTy = .bool := shapeOnly_source_y_typing_inv hyTyping
  subst hxTy
  subst hyTy
  cases hxStrength with
  | reflex =>
      cases hyStrength

theorem shapeOnly_bad_growth_raw_lub :
    PartialTyUnion
      (.ty (.borrow true [.var "x"]))
      (.ty (.borrow true [.var "y"]))
      (.ty (.borrow true [.var "x", .var "y"])) := by
  simpa using
    (PartialTyUnion.borrow_append
      (mutable := true)
      (leftTargets := [.var "x"])
      (rightTargets := [.var "y"]))

theorem shapeOnly_bad_growth_raw_lub_not_coherent :
    ¬ PartialTyCoherent shapeOnlySourceEnv
      (.ty (.borrow true [.var "x", .var "y"])) := by
  intro hcoherent
  rcases hcoherent true [.var "x", .var "y"] PartialTyContains.here with
    ⟨ty, lifetime, htargets⟩
  exact shapeOnlySourceEnv_xy_not_targets_typing ⟨ty, lifetime, htargets⟩

theorem shapeOnlyResultEnv_xy_not_targets_typing :
    ¬ ∃ ty lifetime,
      LValTargetsTyping shapeOnlyResultEnv [.var "x", .var "y"]
        (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htargets⟩
  rcases lvalTargetsTyping_member_strengthens htargets (.var "x") (by simp) with
    ⟨xTy, _xLifetime, hxTyping, hxStrength⟩
  rcases lvalTargetsTyping_member_strengthens htargets (.var "y") (by simp) with
    ⟨yTy, _yLifetime, hyTyping, hyStrength⟩
  rcases LValTyping.var_inv hxTyping with ⟨xSlot, hxSlot, hxTy, _⟩
  rcases LValTyping.var_inv hyTyping with ⟨ySlot, hySlot, hyTy, _⟩
  have hxSlotExpected :
      shapeOnlyResultEnv.slotAt "x" = some nestedIntSlot := by
    simp [shapeOnlyResultEnv, shapeOnlyBaseEnv, shapeOnlyBXYSlot,
      nestedIntSlot, nestedBoolSlot, Env.update]
  have hySlotExpected :
      shapeOnlyResultEnv.slotAt "y" = some nestedBoolSlot := by
    simp [shapeOnlyResultEnv, shapeOnlyBaseEnv, shapeOnlyBXYSlot,
      nestedIntSlot, nestedBoolSlot, Env.update]
  have hxSlotEq : xSlot = nestedIntSlot :=
    Option.some.inj (hxSlot.symm.trans hxSlotExpected)
  have hySlotEq : ySlot = nestedBoolSlot :=
    Option.some.inj (hySlot.symm.trans hySlotExpected)
  subst hxSlotEq
  subst hySlotEq
  have hxTyEq : xTy = .int := by simpa [nestedIntSlot] using hxTy.symm
  have hyTyEq : yTy = .bool := by simpa [nestedBoolSlot] using hyTy.symm
  subst hxTyEq
  subst hyTyEq
  cases hxStrength with
  | reflex =>
      cases hyStrength

theorem shapeOnlyResultEnv_not_coherent :
    ¬ Coherent shapeOnlyResultEnv := by
  intro hcoherent
  rcases hcoherent (.var "b") true [.var "x", .var "y"] Lifetime.root
      shapeOnly_result_b_typing with
    ⟨ty, lifetime, htargets⟩
  exact shapeOnlyResultEnv_xy_not_targets_typing ⟨ty, lifetime, htargets⟩

theorem sameShapeStrengthening_not_coherence_source :
    Coherent shapeOnlySourceEnv ∧
      EnvSameShapeStrengthening shapeOnlySourceEnv shapeOnlyResultEnv ∧
      ¬ Coherent shapeOnlyResultEnv := by
  refine ⟨shapeOnlySourceEnv_coherent, ?_, shapeOnlyResultEnv_not_coherent⟩
  simpa [shapeOnlySourceEnv, shapeOnlyResultEnv] using
    (EnvSameShapeStrengthening.update_same
      (env := shapeOnlyBaseEnv) (x := "b")
      (strong := shapeOnlyBSlot) (weak := shapeOnlyBXYSlot)
      (by rfl)
      (PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget
        subst target
        simp))
        (by simp [shapeOnlyBSlot, shapeOnlyBXYSlot, PartialTy.sameShape,
          Ty.sameShape]))

theorem shapeOnly_heterogeneous_rhs_not_shapeCompatible :
    ¬ ShapeCompatible shapeOnlySourceEnv
      (.ty (.borrow true [.var "x"])) (.ty (.borrow true [.var "y"])) := by
  intro hshape
  cases hshape with
  | borrow hleft hright hinner =>
      rcases hleft (.var "x") (by simp) with ⟨xLifetime, hxTyping⟩
      rcases hright (.var "y") (by simp) with ⟨yLifetime, hyTyping⟩
      have hxTy := shapeOnly_source_x_typing_inv hxTyping
      have hyTy := shapeOnly_source_y_typing_inv hyTyping
      subst hxTy
      subst hyTy
      cases hinner

theorem shapeOnly_bad_growth_not_assignment_leaf {result : Env} :
    ¬ EnvWrite 1 shapeOnlySourceEnv (.var "b") (.borrow true [.var "y"])
      result := by
  intro hwrite
  have hb :
      shapeOnlySourceEnv.slotAt "b" = some shapeOnlyBSlot := by
    simp [shapeOnlySourceEnv, shapeOnlyBSlot, Env.update]
  have hshape :=
    EnvWrite.positive_var_leaf_shapeCompatible
      (rank := 0) (env := shapeOnlySourceEnv) (result := result)
      (x := "b") (slot := shapeOnlyBSlot)
      (rhsTy := .borrow true [.var "y"]) hb hwrite
  exact shapeOnly_heterogeneous_rhs_not_shapeCompatible
    (by simpa [shapeOnlyBSlot] using hshape)

/-- The same rejection happens through a mutable-borrow fan-out: the selected
target branch is a positive-rank assignment leaf, whose `ShapeCompatible` premise
rules out the heterogeneous `b := &mut y` growth. -/
theorem shapeOnly_bad_growth_not_mut_borrow_fanout {result : Env}
    {updatedTy : PartialTy} :
    ¬ UpdateAtPath 0 shapeOnlySourceEnv [()]
      (.ty (.borrow true [.var "b"])) (.borrow true [.var "y"]) result
      updatedTy := by
  intro hupdate
  have hb :
      shapeOnlySourceEnv.slotAt "b" = some shapeOnlyBSlot := by
    simp [shapeOnlySourceEnv, shapeOnlyBSlot, Env.update]
  have hshape :=
    UpdateAtPath.mutBorrow_selected_var_leaf_shapeCompatible
      (rank := 0) (env := shapeOnlySourceEnv) (result := result)
      (targets := [.var "b"]) (rhsTy := .borrow true [.var "y"])
      (updatedTy := updatedTy) (x := "b") (slot := shapeOnlyBSlot)
      hupdate (by simp) hb
  exact shapeOnly_heterogeneous_rhs_not_shapeCompatible
    (by simpa [shapeOnlyBSlot] using hshape)

def shapeOnlyBadGrowthTerm : Term :=
  .assign (.var "b") (.borrow true (.var "y"))

theorem shapeOnly_bad_growth_assignment_rejected :
    ¬ ∃ result,
      TermTyping shapeOnlySourceEnv StoreTyping.empty Lifetime.root
        shapeOnlyBadGrowthTerm .unit result := by
  rintro ⟨result, htyping⟩
  unfold shapeOnlyBadGrowthTerm at htyping
  cases htyping with
  | assign hRhs hLhs hshape _hwellRhs _hwrite _hranked _hrhsWF _hnotWrite =>
      cases hRhs with
      | mutBorrow _hY _hmutableY _hnotWriteY =>
          rcases LValTyping.var_inv hLhs with
            ⟨slot, hslot, hslotTy, _hlife⟩
          have hb :
              shapeOnlySourceEnv.slotAt "b" = some shapeOnlyBSlot := by
            simp [shapeOnlySourceEnv, shapeOnlyBSlot, Env.update]
          have hslotEq : slot = shapeOnlyBSlot :=
            Option.some.inj (hslot.symm.trans hb)
          subst hslotEq
          cases hslotTy
          exact shapeOnly_heterogeneous_rhs_not_shapeCompatible
            (by simpa [shapeOnlyBSlot] using hshape)

def immutableShapeOnlyBSlot : EnvSlot :=
  { ty := .ty (.borrow false [.var "x"]), lifetime := Lifetime.root }

def immutableShapeOnlyEnv : Env :=
  shapeOnlyBaseEnv.update "b" immutableShapeOnlyBSlot

/-- Assignment through a borrow node is not a same-shape permission: the write
rule only has a through-borrow constructor for mutable borrows. -/
theorem immutable_borrow_crossing_write_rejected {result : Env} :
    ¬ EnvWrite 0 immutableShapeOnlyEnv
      (.deref (.var "b")) .int result := by
  intro hwrite
  have hb :
      immutableShapeOnlyEnv.slotAt "b" = some immutableShapeOnlyBSlot := by
    simp [immutableShapeOnlyEnv, immutableShapeOnlyBSlot, Env.update]
  have hthrough :
      PathThroughBorrow (.ty (.borrow false [.var "x"]))
        (LVal.path (.deref (.var "b"))) := by
    simpa [LVal.path] using
      (PathThroughBorrow.borrowHere (mutable := false)
        (targets := [.var "x"]) (path := []))
  have hmut :
      PathThroughMutBorrow (.ty (.borrow false [.var "x"]))
        (LVal.path (.deref (.var "b"))) :=
    EnvWrite.pathThroughBorrow_implies_pathThroughMutBorrow
      (env := shapeOnlyBaseEnv.update "b"
        { ty := .ty (.borrow false [.var "x"]), lifetime := Lifetime.root })
      (result := result)
      (lhs := .deref (.var "b"))
      (rhsTy := .int)
      (slot := immutableShapeOnlyBSlot)
      hb hthrough hwrite
  have himpossible :
      PathThroughMutBorrow (.ty (.borrow false [.var "x"])) [()] := by
    simpa [LVal.path] using hmut
  cases himpossible

/-! ### Reborrow-chain assignment updates the observed target type. -/

def reborrowBSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "x"]), lifetime := Lifetime.root }

def reborrowASlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "b"]), lifetime := Lifetime.root }

def reborrowEnv : Env :=
  (((Env.empty.update "x" nestedIntSlot).update "c" nestedIntSlot).update
    "b" reborrowBSlot).update "a" reborrowASlot

def reborrowBUpdatedSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "x", .var "c"]),
    lifetime := Lifetime.root }

def reborrowResultEnv : Env :=
  (reborrowEnv.update "b" reborrowBUpdatedSlot).update "a" reborrowASlot

theorem reborrowEnv_x_typing :
    LValTyping reborrowEnv (.var "x") (.ty .int) Lifetime.root := by
  exact LValTyping.var (env := reborrowEnv) (x := "x")
    (slot := nestedIntSlot) (by
      simp [reborrowEnv, reborrowASlot, reborrowBSlot, nestedIntSlot,
        Env.update])

theorem reborrowEnv_c_typing :
    LValTyping reborrowEnv (.var "c") (.ty .int) Lifetime.root := by
  exact LValTyping.var (env := reborrowEnv) (x := "c")
    (slot := nestedIntSlot) (by
      simp [reborrowEnv, reborrowASlot, reborrowBSlot, nestedIntSlot,
        Env.update])

theorem reborrowEnv_b_typing :
    LValTyping reborrowEnv (.var "b")
      (.ty (.borrow true [.var "x"])) Lifetime.root := by
  exact LValTyping.var (env := reborrowEnv) (x := "b")
    (slot := reborrowBSlot) (by
      simp [reborrowEnv, reborrowBSlot, reborrowASlot, Env.update])

theorem reborrowEnv_a_typing :
    LValTyping reborrowEnv (.var "a")
      (.ty (.borrow true [.var "b"])) Lifetime.root := by
  exact LValTyping.var (env := reborrowEnv) (x := "a")
    (slot := reborrowASlot) (by
      simp [reborrowEnv, reborrowASlot, Env.update])

theorem reborrow_leaf_shapeCompatible :
    ShapeCompatible reborrowEnv
      (.ty (.borrow true [.var "x"]))
      (.ty (.borrow true [.var "c"])) := by
  refine ShapeCompatible.borrow ?left ?right ShapeCompatible.int
  · intro target htarget
    have htargetEq : target = .var "x" := by simpa using htarget
    subst htargetEq
    exact ⟨Lifetime.root, reborrowEnv_x_typing⟩
  · intro target htarget
    have htargetEq : target = .var "c" := by simpa using htarget
    subst htargetEq
    exact ⟨Lifetime.root, reborrowEnv_c_typing⟩

theorem reborrow_leaf_join :
    PartialTyUnion
      (.ty (.borrow true [.var "x"]))
      (.ty (.borrow true [.var "c"]))
      (.ty (.borrow true [.var "x", .var "c"])) := by
  simpa using
    (PartialTyUnion.borrow_append
      (mutable := true)
      (leftTargets := [.var "x"])
      (rightTargets := [.var "c"]))

theorem reborrow_write_b :
    EnvWrite 1 reborrowEnv (.var "b") (.borrow true [.var "c"])
      (reborrowEnv.update "b" reborrowBUpdatedSlot) := by
  exact EnvWrite.intro
    (env₁ := reborrowEnv)
    (env₂ := reborrowEnv)
    (lv := .var "b")
    (slot := reborrowBSlot)
    (ty := .borrow true [.var "c"])
    (updatedTy := .ty (.borrow true [.var "x", .var "c"]))
    (by simp [reborrowEnv, reborrowBSlot, reborrowASlot, Env.update,
      LVal.base])
    (by
      simpa [reborrowBSlot, reborrowBUpdatedSlot, LVal.path] using
        (UpdateAtPath.weak
          (rank := 0)
          (env := reborrowEnv)
          (old := .ty (.borrow true [.var "x"]))
          (joined := .ty (.borrow true [.var "x", .var "c"]))
          (ty := .borrow true [.var "c"])
          reborrow_leaf_shapeCompatible
          reborrow_leaf_join))

theorem reborrow_write_targets :
    WriteBorrowTargets 1 reborrowEnv [] [.var "b"]
      (.borrow true [.var "c"])
      (reborrowEnv.update "b" reborrowBUpdatedSlot) := by
  exact WriteBorrowTargets.singleton reborrow_write_b
    ⟨.borrow true [.var "x"], Lifetime.root, reborrowEnv_b_typing⟩

theorem reborrow_write_deref_a :
    EnvWrite 0 reborrowEnv (.deref (.var "a")) (.borrow true [.var "c"])
      reborrowResultEnv := by
  exact EnvWrite.intro
    (env₁ := reborrowEnv)
    (env₂ := reborrowEnv.update "b" reborrowBUpdatedSlot)
    (lv := .deref (.var "a"))
    (slot := reborrowASlot)
    (ty := .borrow true [.var "c"])
    (updatedTy := .ty (.borrow true [.var "b"]))
    (by simp [reborrowEnv, reborrowASlot, Env.update, LVal.base])
    (by
      simpa [reborrowASlot, reborrowResultEnv, LVal.path] using
        (UpdateAtPath.mutBorrow
          (rank := 0)
          (env₁ := reborrowEnv)
          (env₂ := reborrowEnv.update "b" reborrowBUpdatedSlot)
          (path := [])
          (targets := [.var "b"])
          (ty := .borrow true [.var "c"])
          reborrow_write_targets))

theorem reborrowResultEnv_b_typing :
    LValTyping reborrowResultEnv (.var "b")
      (.ty (.borrow true [.var "x", .var "c"])) Lifetime.root := by
  exact LValTyping.var (env := reborrowResultEnv) (x := "b")
    (slot := reborrowBUpdatedSlot) (by
      simp [reborrowResultEnv, reborrowBUpdatedSlot, reborrowASlot,
        Env.update])

theorem reborrowResultEnv_a_typing :
    LValTyping reborrowResultEnv (.var "a")
      (.ty (.borrow true [.var "b"])) Lifetime.root := by
  exact LValTyping.var (env := reborrowResultEnv) (x := "a")
    (slot := reborrowASlot) (by
      simp [reborrowResultEnv, reborrowASlot, Env.update])

theorem reborrowResultEnv_deref_a_typing :
    LValTyping reborrowResultEnv (.deref (.var "a"))
      (.ty (.borrow true [.var "x", .var "c"])) Lifetime.root := by
  exact LValTyping.borrow reborrowResultEnv_a_typing
    (LValTargetsTyping.singleton reborrowResultEnv_b_typing)

theorem reborrow_assignment_updates_observed_deref_type :
    ∃ result,
      EnvWrite 0 reborrowEnv (.deref (.var "a")) (.borrow true [.var "c"])
        result ∧
      LValTyping result (.deref (.var "a"))
        (.ty (.borrow true [.var "x", .var "c"])) Lifetime.root := by
  exact ⟨reborrowResultEnv, reborrow_write_deref_a,
    reborrowResultEnv_deref_a_typing⟩

theorem nestedBorrowEnv_fresh_z_rejected :
    ¬ FreshUpdateCoherenceObligations nestedBorrowEnv "z"
      (.borrow false [.var "bx", .var "by"]) Lifetime.root := by
  intro hobligations
  have htyping : LValTyping
      (nestedBorrowEnv.update "z"
        { ty := .ty (.borrow false [.var "bx", .var "by"]),
          lifetime := Lifetime.root })
      (.deref (.var "z")) (.ty (.borrow false [.var "x", .var "y"]))
      Lifetime.root := by
    simpa [nestedBorrowEnvZ, nestedZSlot] using nestedBorrowEnvZ_deref_z_typing
  rcases hobligations.fresh_root_coherent (by rfl) htyping with
    ⟨ty, lifetime, htargets⟩
  have htargetsZ :
      LValTargetsTyping nestedBorrowEnvZ [.var "x", .var "y"] (.ty ty)
        lifetime := by
    simpa [nestedBorrowEnvZ, nestedZSlot] using htargets
  exact nestedBorrowEnvZ_xy_not_targets_typing ⟨ty, lifetime, htargetsZ⟩

/-! ### Environment coherence does not imply boxed result-type coherence. -/

def boxedHiddenSlot : EnvSlot :=
  { ty := .ty (.box (.borrow false [.var "x", .var "y"])),
    lifetime := Lifetime.root }

def boxedHiddenEnv : Env :=
  ((Env.empty.update "x" nestedIntSlot).update "y" nestedBoolSlot).update
    "boxed" boxedHiddenSlot

theorem boxedHiddenEnv_x_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping boxedHiddenEnv (.var "x") (.ty ty) lifetime →
    ty = .int := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hx : boxedHiddenEnv.slotAt "x" = some nestedIntSlot := by
    simp [boxedHiddenEnv, nestedIntSlot, nestedBoolSlot, boxedHiddenSlot,
      Env.update]
  have hslotEq : slot = nestedIntSlot := Option.some.inj (hslot.symm.trans hx)
  subst hslotEq
  simpa [nestedIntSlot] using hslotTy.symm

theorem boxedHiddenEnv_y_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping boxedHiddenEnv (.var "y") (.ty ty) lifetime →
    ty = .bool := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hy : boxedHiddenEnv.slotAt "y" = some nestedBoolSlot := by
    simp [boxedHiddenEnv, nestedIntSlot, nestedBoolSlot, boxedHiddenSlot,
      Env.update]
  have hslotEq : slot = nestedBoolSlot := Option.some.inj (hslot.symm.trans hy)
  subst hslotEq
  simpa [nestedBoolSlot] using hslotTy.symm

theorem boxedHiddenEnv_xy_not_targets_typing :
    ¬ ∃ ty lifetime,
      LValTargetsTyping boxedHiddenEnv [.var "x", .var "y"]
        (.ty ty) lifetime := by
  rintro ⟨ty, lifetime, htargets⟩
  rcases lvalTargetsTyping_member_strengthens htargets (.var "x") (by simp) with
    ⟨xTy, _xLifetime, hxTyping, hxStrength⟩
  rcases lvalTargetsTyping_member_strengthens htargets (.var "y") (by simp) with
    ⟨yTy, _yLifetime, hyTyping, hyStrength⟩
  have hxTy : xTy = .int := boxedHiddenEnv_x_typing_inv hxTyping
  have hyTy : yTy = .bool := boxedHiddenEnv_y_typing_inv hyTyping
  subst hxTy
  subst hyTy
  cases hxStrength with
  | reflex =>
      cases hyStrength

theorem boxedHiddenEnv_no_borrow_typing {lv : LVal} {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTyping boxedHiddenEnv lv (.ty (.borrow mutable targets)) lifetime := by
  intro htyping
  refine LValTyping.rec
    (motive_1 := fun _lv partialTy _lifetime _ =>
      (∀ {mutable targets},
        partialTy = .ty (.borrow mutable targets) → False) ∧
      (∀ {inner}, partialTy = .box inner → False))
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    (by
      intro x slot hslot
      constructor
      · intro mutable targets hpartial
        cases slot with
        | mk slotTy slotLifetime =>
            simp at hpartial
            subst hpartial
            simp [boxedHiddenEnv, nestedIntSlot, nestedBoolSlot, boxedHiddenSlot,
              Env.update] at hslot
            by_cases hboxed : x = "boxed"
            · subst hboxed
              simp at hslot
            · by_cases hy : x = "y"
              · subst hy
                simp [hboxed] at hslot
              · by_cases hx : x = "x"
                · subst hx
                  simp [hboxed, hy] at hslot
                · simp [hboxed, hy, hx, Env.empty] at hslot
      · intro inner hpartial
        cases slot with
        | mk slotTy slotLifetime =>
            simp at hpartial
            subst hpartial
            simp [boxedHiddenEnv, nestedIntSlot, nestedBoolSlot, boxedHiddenSlot,
              Env.update] at hslot
            by_cases hboxed : x = "boxed"
            · subst hboxed
              simp at hslot
            · by_cases hy : x = "y"
              · subst hy
                simp [hboxed] at hslot
              · by_cases hx : x = "x"
                · subst hx
                  simp [hboxed, hy] at hslot
                · simp [hboxed, hy, hx, Env.empty] at hslot)
    (by
      intro _lv inner _lifetime _htyping ih
      exact ⟨
        (by
          intro _mutable _targets _hpartial
          exact ih.2 (inner := inner) rfl),
        (by
          intro _boxedInner _hpartial
          exact ih.2 (inner := inner) rfl)⟩)
    (by
      intro _lv sourceMutable sourceTargets _borrowLifetime _targetLifetime
        _targetTy _hborrow _htargets ihBorrow _ihTargets
      have hsourceFalse : False :=
        ihBorrow.1 (mutable := sourceMutable) (targets := sourceTargets) rfl
      exact False.elim hsourceFalse)
    (by
      intro _target _ty _lifetime _htyping _ih
      trivial)
    (by
      intro _target _rest _headTy _headLifetime _restLifetime _lifetime
        _restTy _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
      trivial)
    htyping |>.1 rfl

theorem boxedHiddenEnv_coherent : Coherent boxedHiddenEnv := by
  intro lv mutable targets borrowLifetime htyping
  exact False.elim (boxedHiddenEnv_no_borrow_typing htyping)

theorem coherent_env_lval_boxed_type_not_tyCoherent :
    Coherent boxedHiddenEnv ∧
      LValTyping boxedHiddenEnv (.var "boxed")
        (.ty (.box (.borrow false [.var "x", .var "y"]))) Lifetime.root ∧
      ¬ TyCoherent boxedHiddenEnv (.box (.borrow false [.var "x", .var "y"])) := by
  refine ⟨boxedHiddenEnv_coherent, ?_, ?_⟩
  · exact LValTyping.var (env := boxedHiddenEnv) (x := "boxed")
      (slot := boxedHiddenSlot) (by
        simp [boxedHiddenEnv, boxedHiddenSlot, Env.update])
  · intro htyCoherent
    rcases htyCoherent false [.var "x", .var "y"]
        (PartialTyContains.tyBox PartialTyContains.here) with
      ⟨ty, lifetime, htargets⟩
    exact boxedHiddenEnv_xy_not_targets_typing ⟨ty, lifetime, htargets⟩

/-! ### Assignment compatibility rejects heterogeneous nested targets. -/

def assignCompatXSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def assignCompatYSlot : EnvSlot :=
  { ty := .ty .bool, lifetime := Lifetime.root }

def assignCompatBxSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "x"]), lifetime := Lifetime.root }

def assignCompatBySlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "y"]), lifetime := Lifetime.root }

def assignCompatPSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "bx"]), lifetime := Lifetime.root }

def assignCompatEnv : Env :=
  ((((Env.empty.update "x" assignCompatXSlot).update "y"
    assignCompatYSlot).update "bx" assignCompatBxSlot).update "by"
    assignCompatBySlot).update "p" assignCompatPSlot

theorem assignCompat_x_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping assignCompatEnv (.var "x") (.ty ty) lifetime →
    ty = .int := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hx : assignCompatEnv.slotAt "x" = some assignCompatXSlot := by
    simp [assignCompatEnv, assignCompatXSlot, assignCompatYSlot,
      assignCompatBxSlot, assignCompatBySlot, assignCompatPSlot, Env.update]
  have hslotEq : slot = assignCompatXSlot :=
    Option.some.inj (hslot.symm.trans hx)
  subst hslotEq
  simpa [assignCompatXSlot] using hslotTy.symm

theorem assignCompat_y_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping assignCompatEnv (.var "y") (.ty ty) lifetime →
    ty = .bool := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hy : assignCompatEnv.slotAt "y" = some assignCompatYSlot := by
    simp [assignCompatEnv, assignCompatXSlot, assignCompatYSlot,
      assignCompatBxSlot, assignCompatBySlot, assignCompatPSlot, Env.update]
  have hslotEq : slot = assignCompatYSlot :=
    Option.some.inj (hslot.symm.trans hy)
  subst hslotEq
  simpa [assignCompatYSlot] using hslotTy.symm

theorem assignCompat_bx_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping assignCompatEnv (.var "bx") (.ty ty) lifetime →
    ty = .borrow true [.var "x"] := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hbx : assignCompatEnv.slotAt "bx" = some assignCompatBxSlot := by
    simp [assignCompatEnv, assignCompatBxSlot, assignCompatBySlot,
      assignCompatPSlot, Env.update]
  have hslotEq : slot = assignCompatBxSlot :=
    Option.some.inj (hslot.symm.trans hbx)
  subst hslotEq
  simpa [assignCompatBxSlot] using hslotTy.symm

theorem assignCompat_by_typing_inv {ty : Ty} {lifetime : Lifetime} :
    LValTyping assignCompatEnv (.var "by") (.ty ty) lifetime →
    ty = .borrow true [.var "y"] := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, _hlife⟩
  have hby : assignCompatEnv.slotAt "by" = some assignCompatBySlot := by
    simp [assignCompatEnv, assignCompatBySlot, assignCompatPSlot, Env.update]
  have hslotEq : slot = assignCompatBySlot :=
    Option.some.inj (hslot.symm.trans hby)
  subst hslotEq
  simpa [assignCompatBySlot] using hslotTy.symm

theorem assignCompat_bx_by_shape_rejected :
    ¬ ShapeCompatible assignCompatEnv
      (.ty (.borrow true [.var "bx"]))
      (.ty (.borrow true [.var "by"])) := by
  intro hshape
  cases hshape with
  | borrow hleft hright hinner =>
      rcases hleft (.var "bx") (by simp) with ⟨_leftLifetime, hbx⟩
      rcases hright (.var "by") (by simp) with ⟨_rightLifetime, hby⟩
      have hleftTy := assignCompat_bx_typing_inv hbx
      have hrightTy := assignCompat_by_typing_inv hby
      subst hleftTy
      subst hrightTy
      cases hinner with
      | borrow hleftInner hrightInner hinnerShape =>
          rcases hleftInner (.var "x") (by simp) with
            ⟨_xLifetime, hx⟩
          rcases hrightInner (.var "y") (by simp) with
            ⟨_yLifetime, hy⟩
          have hxTy := assignCompat_x_typing_inv hx
          have hyTy := assignCompat_y_typing_inv hy
          subst hxTy
          subst hyTy
          cases hinnerShape

def assignCompatHeterogeneousTerm : Term :=
  .assign (.var "p") (.borrow true (.var "by"))

theorem assignCompat_heterogeneous_assignment_rejected :
    ¬ ∃ result,
      TermTyping assignCompatEnv StoreTyping.empty Lifetime.root
        assignCompatHeterogeneousTerm .unit result := by
  rintro ⟨result, htyping⟩
  unfold assignCompatHeterogeneousTerm at htyping
  cases htyping with
  | assign hRhs hLhs hshape _hwellRhs _hwrite _hranked _hrhsWF _hnotWrite =>
      cases hRhs with
      | mutBorrow _hBy _hmutableBy _hnotWriteBy =>
          rcases LValTyping.var_inv hLhs with ⟨slot, hslot, hslotTy, _hlife⟩
          have hp : assignCompatEnv.slotAt "p" = some assignCompatPSlot := by
            simp [assignCompatEnv, assignCompatPSlot, Env.update]
          have hslotEq : slot = assignCompatPSlot :=
            Option.some.inj (hslot.symm.trans hp)
          subst hslotEq
          cases hslotTy
          exact assignCompat_bx_by_shape_rejected
            (by simpa [assignCompatPSlot] using hshape)

end Paper
end LwRust
