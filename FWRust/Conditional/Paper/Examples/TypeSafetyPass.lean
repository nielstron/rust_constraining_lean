import FWRust.Conditional.Paper.Soundness.InitialStates

/-!
Build-checked accepted paper-style examples.

Each `*_typeSafety` theorem invokes the empty-initial form of Theorem 4.12:
from a typing derivation and syntactic exclusion of generated `.missing`, the
program reduces to a terminal value whose final state is safe at initialized
places.
-/

namespace FWRust.Conditional
namespace Paper

open Core

/--
Accepted scalar comparison example: two copyable integer values can be compared,
and Theorem 4.12 gives terminal-state safety.
-/
def scalarCopyComparison : Term :=
  .eq (.val (.int 1)) (.val (.int 1))

theorem scalarCopyComparison_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root
      scalarCopyComparison .bool Env.empty := by
  unfold scalarCopyComparison
  refine TermTyping.eq_finite
    (TermTyping.const ValueTyping.int)
    Env.finiteSupport_empty
    StoreTyping.finiteSupport_empty
    ?_
    CopyTy.int
    CopyTy.int
    ShapeCompatible.int
  intro ghost hfresh _htypeFresh _htyFresh _hstoreFresh _hnotMention
  exact ⟨_,
    TermTyping.const ValueTyping.int,
    (Env.erase_update_fresh Env.empty ghost
      { ty := .ty Ty.int, lifetime := Lifetime.root } hfresh).symm⟩

theorem scalarCopyComparison_terminates :
    TerminatesAsValue ProgramStore.empty Lifetime.root scalarCopyComparison := by
  unfold scalarCopyComparison
  exact ⟨ProgramStore.empty, .bool true,
    MultiStep.trans Step.eqTrue MultiStep.refl⟩

theorem scalarCopyComparison_missingFree :
    scalarCopyComparison.MissingFree := by
  unfold scalarCopyComparison
  simp [Term.MissingFree]

theorem scalarCopyComparison_loopFree :
    scalarCopyComparison.LoopFree := by
  unfold scalarCopyComparison
  simp [Term.LoopFree]

theorem scalarCopyComparison_typeSafety :
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty Lifetime.root scalarCopyComparison finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue Env.empty .bool :=
  emptyInitial_typeAndBorrowSafety_total scalarCopyComparison_typing
    scalarCopyComparison_missingFree scalarCopyComparison_loopFree

/--
Accepted `if/else` example for the control-flow extension: both branches return
the same borrow-free type, and the joined environment is empty.
-/
def ifThenElseInt : Term :=
  .ite (.val (.bool true)) (.val (.int 1)) (.val (.int 2))

theorem ifThenElseInt_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root
      ifThenElseInt .int Env.empty := by
  unfold ifThenElseInt
  refine TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    (TermTyping.const ValueTyping.int)
    (TermTyping.const ValueTyping.int)
    (PartialTyJoin.self (.ty .int))
    ?join
  · simp [EnvJoin]

theorem ifThenElseInt_terminates :
    TerminatesAsValue ProgramStore.empty Lifetime.root ifThenElseInt := by
  unfold ifThenElseInt
  exact ⟨ProgramStore.empty, .int 1,
    MultiStep.trans Step.iteTrue MultiStep.refl⟩

theorem ifThenElseInt_missingFree :
    ifThenElseInt.MissingFree := by
  unfold ifThenElseInt
  simp [Term.MissingFree]

theorem ifThenElseInt_loopFree :
    ifThenElseInt.LoopFree := by
  unfold ifThenElseInt
  simp [Term.LoopFree]

theorem ifThenElseInt_typeSafety :
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty Lifetime.root ifThenElseInt finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue Env.empty .int :=
  emptyInitial_typeAndBorrowSafety_total ifThenElseInt_typing
    ifThenElseInt_missingFree ifThenElseInt_loopFree

/--
Accepted `if/else` example with a nontrivial boolean guard.  The conditional
still joins to the empty environment.
-/
def ifEqThenElseInt : Term :=
  .ite scalarCopyComparison (.val (.int 1)) (.val (.int 2))

theorem ifEqThenElseInt_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root
      ifEqThenElseInt .int Env.empty := by
  unfold ifEqThenElseInt
  refine TermTyping.ite
    scalarCopyComparison_typing
    (TermTyping.const ValueTyping.int)
    (TermTyping.const ValueTyping.int)
    (PartialTyJoin.self (.ty .int))
    ?join
  · simp [EnvJoin]

theorem ifEqThenElseInt_terminates :
    TerminatesAsValue ProgramStore.empty Lifetime.root ifEqThenElseInt := by
  unfold ifEqThenElseInt scalarCopyComparison
  exact ⟨ProgramStore.empty, .int 1,
    MultiStep.trans (Step.subIte Step.eqTrue)
      (MultiStep.trans Step.iteTrue MultiStep.refl)⟩

theorem ifEqThenElseInt_missingFree :
    ifEqThenElseInt.MissingFree := by
  unfold ifEqThenElseInt scalarCopyComparison
  simp [Term.MissingFree]

theorem ifEqThenElseInt_loopFree :
    ifEqThenElseInt.LoopFree := by
  unfold ifEqThenElseInt scalarCopyComparison
  simp [Term.LoopFree]

theorem ifEqThenElseInt_typeSafety :
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty Lifetime.root ifEqThenElseInt finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue Env.empty .int :=
  emptyInitial_typeAndBorrowSafety_total ifEqThenElseInt_typing
    ifEqThenElseInt_missingFree ifEqThenElseInt_loopFree

/--
Regression outline for the relaxed `T-If` join.

Rust-like code, starting from an empty environment:

```rust
let mut c = 0;
let mut d = 0;
let mut e = 0;
let mut sth = true;
let mut a = &mut c;

if sth {
    a = &mut d;
} else {
    a = &mut e;
}
*a = 0;
```

The intended typing-environment trace is:

```text
Env0 = empty
Env1 = Env0, c  : int
Env2 = Env1, d  : int
Env3 = Env2, e  : int
Env4 = Env3, sth : bool
Env5 = Env4, a : &mut [c]

true branch  Env6T = Env5[a := &mut [d]]
false branch Env6F = Env5[a := &mut [e]]
join         Env7  = Env5[a := &mut [d, e]]

after *a = 0, the type environment is still Env7.
```

The key point is that `Env7` is a static control-flow approximation: the joined
type of `a` remembers both branch targets, but at runtime only the selected
branch's reference exists before the final `*a = 0` write.
-/
def retargetAfterIfIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def retargetAfterIfBoolSlot : EnvSlot :=
  { ty := .ty .bool, lifetime := Lifetime.root }

def retargetAfterIfACSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "c"]), lifetime := Lifetime.root }

def retargetAfterIfADSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "d"]), lifetime := Lifetime.root }

def retargetAfterIfAESlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "e"]), lifetime := Lifetime.root }

def retargetAfterIfAJoinSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "d", .var "e"]), lifetime := Lifetime.root }

def retargetAfterIfEnv0 : Env :=
  Env.empty

def retargetAfterIfEnv1 : Env :=
  retargetAfterIfEnv0.update "c" retargetAfterIfIntSlot

def retargetAfterIfEnv2 : Env :=
  retargetAfterIfEnv1.update "d" retargetAfterIfIntSlot

def retargetAfterIfEnv3 : Env :=
  retargetAfterIfEnv2.update "e" retargetAfterIfIntSlot

def retargetAfterIfEnv4 : Env :=
  retargetAfterIfEnv3.update "sth" retargetAfterIfBoolSlot

def retargetAfterIfEnv5 : Env :=
  retargetAfterIfEnv4.update "a" retargetAfterIfACSlot

def retargetAfterIfTrueEnv : Env :=
  retargetAfterIfEnv5.update "a" retargetAfterIfADSlot

def retargetAfterIfFalseEnv : Env :=
  retargetAfterIfEnv5.update "a" retargetAfterIfAESlot

def retargetAfterIfJoinEnv : Env :=
  retargetAfterIfEnv5.update "a" retargetAfterIfAJoinSlot

def retargetAfterIfTerms : List Term :=
  [.letMut "c" (.val (.int 0)),
   .letMut "d" (.val (.int 0)),
   .letMut "e" (.val (.int 0)),
   .letMut "sth" (.val (.bool true)),
   .letMut "a" (.borrow true (.var "c")),
   .ite (.copy (.var "sth"))
     (.assign (.var "a") (.borrow true (.var "d")))
     (.assign (.var "a") (.borrow true (.var "e"))),
   .assign (.deref (.var "a")) (.val (.int 0))]

theorem lval_not_box_of_scalar_slots {env : Env}
    (hscalar : ∀ {x slot}, env.slotAt x = some slot →
      slot.ty = .ty .int ∨ slot.ty = .ty .bool) :
    ∀ (lv : LVal) {inner lifetime},
      ¬ LValTyping env lv (.box inner) lifetime
  | .var _x, _inner, _lifetime => by
      intro htyping
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hl⟩
      rcases hscalar hslot with hslotTy | hslotTy <;>
        rw [hslotTy] at hty <;> cases hty
  | .deref lv, _inner, _lifetime => by
      intro htyping
      cases htyping with
      | box hinner =>
          exact lval_not_box_of_scalar_slots hscalar lv hinner
      | borrow _hborrow htargets =>
          exact LValTargetsTyping.not_box htargets

theorem lval_full_type_scalar_slots {env : Env}
    (hscalar : ∀ {x slot}, env.slotAt x = some slot →
      slot.ty = .ty .int ∨ slot.ty = .ty .bool) :
    ∀ (lv : LVal) {ty lifetime},
      LValTyping env lv (.ty ty) lifetime → ty = .int ∨ ty = .bool
  | .var _x, _ty, _lifetime => by
      intro htyping
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hl⟩
      rcases hscalar hslot with hslotTy | hslotTy
      · rw [hslotTy] at hty
        cases hty
        exact Or.inl rfl
      · rw [hslotTy] at hty
        cases hty
        exact Or.inr rfl
  | .deref lv, _ty, _lifetime => by
      intro htyping
      cases htyping with
      | box hinner =>
          exact False.elim (lval_not_box_of_scalar_slots hscalar lv hinner)
      | boxFull hinner =>
          rcases lval_full_type_scalar_slots hscalar lv hinner with hbox | hbox <;>
            cases hbox
      | borrow hinner _htargets =>
          rcases lval_full_type_scalar_slots hscalar lv hinner with hborrow | hborrow <;>
            cases hborrow

theorem lval_not_borrow_of_scalar_slots {env : Env}
    (hscalar : ∀ {x slot}, env.slotAt x = some slot →
      slot.ty = .ty .int ∨ slot.ty = .ty .bool) :
    ∀ (lv : LVal) {mutable targets lifetime},
      ¬ LValTyping env lv (.ty (.borrow mutable targets)) lifetime := by
  intro lv mutable targets lifetime htyping
  rcases lval_full_type_scalar_slots hscalar lv htyping with hty | hty <;>
    cases hty

theorem freshUpdateCoherence_no_borrow {env : Env} {x : Name}
    {ty : Ty} {lifetime : Lifetime}
    (hnoBorrow : ∀ lv mutable targets borrowLifetime,
      ¬ LValTyping (env.update x { ty := .ty ty, lifetime := lifetime }) lv
        (.ty (.borrow mutable targets)) borrowLifetime) :
    FreshUpdateCoherenceObligations env x ty lifetime := by
  constructor
  · intro lv mutable targets borrowLifetime _hbase htyping
    exact False.elim (hnoBorrow lv mutable targets borrowLifetime htyping)
  · intro lv mutable targets borrowLifetime _hbase htyping
    exact False.elim (hnoBorrow lv mutable targets borrowLifetime htyping)
theorem env_not_contains_borrow_of_scalar_slots {env : Env}
    (hscalar : ∀ {x slot}, env.slotAt x = some slot →
      slot.ty = .ty .int ∨ slot.ty = .ty .bool) :
    ∀ {x mutable targets}, ¬ env ⊢ x ↝ (.borrow mutable targets) := by
  intro x mutable targets hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  rcases hscalar hslot with hslotTy | hslotTy <;>
    rw [hslotTy] at hcontainsTy <;> cases hcontainsTy

theorem not_readProhibited_of_no_borrows {env : Env}
    (hnoBorrow : ∀ {x mutable targets}, ¬ env ⊢ x ↝ (.borrow mutable targets))
    (lv : LVal) :
    ¬ ReadProhibited env lv := by
  intro hread
  rcases hread with ⟨x, _targets, _target, hcontains, _htarget,
    _hconflict⟩
  exact hnoBorrow hcontains

theorem not_writeProhibited_of_no_borrows {env : Env}
    (hnoBorrow : ∀ {x mutable targets}, ¬ env ⊢ x ↝ (.borrow mutable targets))
    (lv : LVal) :
    ¬ WriteProhibited env lv := by
  intro hwrite
  rcases hwrite with hread | himm
  · exact not_readProhibited_of_no_borrows hnoBorrow lv hread
  · rcases himm with ⟨x, _targets, _target, hcontains, _htarget,
      _hconflict⟩
    exact hnoBorrow hcontains

theorem not_readProhibited_of_oneBorrowSlot_disjoint {env : Env}
    {slotTargets : List LVal} {lv : LVal}
    (hinv : ∀ {x mutable targets}, env ⊢ x ↝ (.borrow mutable targets) →
      x = "a" ∧ mutable = true ∧ targets = slotTargets)
    (hdisjoint : ∀ target, target ∈ slotTargets →
      LVal.base target ≠ LVal.base lv) :
    ¬ ReadProhibited env lv := by
  intro hread
  rcases hread with ⟨_x, _targets, target, hcontains, htarget,
    hconflict⟩
  rcases hinv hcontains with ⟨_hx, _hmutable, htargets⟩
  subst htargets
  exact hdisjoint target htarget hconflict

theorem not_writeProhibited_of_oneBorrowSlot_disjoint {env : Env}
    {slotTargets : List LVal} {lv : LVal}
    (hinv : ∀ {x mutable targets}, env ⊢ x ↝ (.borrow mutable targets) →
      x = "a" ∧ mutable = true ∧ targets = slotTargets)
    (hdisjoint : ∀ target, target ∈ slotTargets →
      LVal.base target ≠ LVal.base lv) :
    ¬ WriteProhibited env lv := by
  intro hwrite
  rcases hwrite with hread | himm
  · exact not_readProhibited_of_oneBorrowSlot_disjoint hinv hdisjoint hread
  · rcases himm with ⟨_x, _targets, _target, hcontains, _htarget,
      _hconflict⟩
    rcases hinv hcontains with ⟨_hx, hmutable, _htargets⟩
    cases hmutable

theorem oneBorrowSlot_no_box_lval {env : Env} {aSlot : EnvSlot}
    {targets : List LVal}
    (hslotA : env.slotAt "a" = some aSlot)
    (haTy : aSlot.ty = .ty (.borrow true targets))
    (hrest : ∀ {x slot}, x ≠ "a" → env.slotAt x = some slot →
      slot.ty = .ty .int ∨ slot.ty = .ty .bool) :
    ∀ (lv : LVal) {inner lifetime},
      ¬ LValTyping env lv (.box inner) lifetime
  | .var x, _inner, _lifetime => by
      intro htyping
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hl⟩
      by_cases ha : x = "a"
      · subst ha
        have hslotEq : slot = aSlot :=
          Option.some.inj (hslot.symm.trans hslotA)
        subst hslotEq
        rw [haTy] at hty
        cases hty
      · rcases hrest ha hslot with hslotTy | hslotTy <;>
          rw [hslotTy] at hty <;> cases hty
  | .deref lv, _inner, _lifetime => by
      intro htyping
      cases htyping with
      | box hinner =>
          exact oneBorrowSlot_no_box_lval hslotA haTy hrest lv hinner
      | borrow _hborrow htargets =>
          exact LValTargetsTyping.not_box htargets

theorem oneBorrowSlot_no_full_box_lval {env : Env} {aSlot : EnvSlot}
    {targets : List LVal}
    (hslotA : env.slotAt "a" = some aSlot)
    (haTy : aSlot.ty = .ty (.borrow true targets))
    (hrest : ∀ {x slot}, x ≠ "a" → env.slotAt x = some slot →
      slot.ty = .ty .int ∨ slot.ty = .ty .bool) :
    ∀ (lv : LVal) {inner lifetime},
      ¬ LValTyping env lv (.ty (.box inner)) lifetime := by
  intro lv inner lifetime htyping
  refine LValTyping.rec
    (motive_1 := fun _lv partialTy _lifetime _ =>
      ∀ {inner : Ty}, partialTy = .ty (.box inner) → False)
    (motive_2 := fun _targets partialTy _lifetime _ =>
      ∀ {inner : Ty}, partialTy = .ty (.box inner) → False)
    ?var ?box ?boxFull ?borrow ?singleton ?cons htyping rfl
  · intro x slot hslot inner hty
    by_cases ha : x = "a"
    · subst ha
      have hslotEq : slot = aSlot :=
        Option.some.inj (hslot.symm.trans hslotA)
      subst hslotEq
      rw [haTy] at hty
      cases hty
    · rcases hrest ha hslot with hslotTy | hslotTy <;>
        rw [hslotTy] at hty <;> cases hty
  · intro source innerPartial sourceLifetime hsource _ih inner hty
    cases hty
    exact oneBorrowSlot_no_box_lval hslotA haTy hrest source hsource
  · intro source innerTy sourceLifetime _hsource ih inner hty
    cases hty
    exact ih rfl
  · intro source mutable borrowTargets borrowLifetime targetLifetime targetTy
      _hsource htargets _ihSource ihTargets inner hty
    exact ihTargets hty
  · intro target targetTy targetLifetime _htarget ihTarget inner hty
    exact ihTarget hty
  · intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
      _hhead _hrest hunion _hintersection ihHead _ihRest inner hty
    have hleft : PartialTyStrengthens (.ty headTy) (.ty (.box inner)) := by
      have hleft' := PartialTyUnion.left_strengthens hunion
      rwa [hty] at hleft'
    rcases PartialTyStrengthens.to_box_ty_inv hleft with
      ⟨sourceInner, hheadEq, _hinner⟩
    subst hheadEq
    exact ihHead rfl

theorem oneBorrowSlot_borrow_lval_inv {env : Env} {aSlot : EnvSlot}
    {slotTargets : List LVal}
    (hslotA : env.slotAt "a" = some aSlot)
    (haTy : aSlot.ty = .ty (.borrow true slotTargets))
    (haLife : aSlot.lifetime = Lifetime.root)
    (hrest : ∀ {x slot}, x ≠ "a" → env.slotAt x = some slot →
      slot.ty = .ty .int ∨ slot.ty = .ty .bool)
    (htargetsNoBorrow : ∀ {mutable targets lifetime},
      ¬ LValTargetsTyping env slotTargets (.ty (.borrow mutable targets))
        lifetime) :
    ∀ (lv : LVal) {mutable targets lifetime},
      LValTyping env lv (.ty (.borrow mutable targets)) lifetime →
      lv = .var "a" ∧ mutable = true ∧ targets = slotTargets ∧
        lifetime = Lifetime.root := by
  intro lv mutable targets lifetime htyping
  induction lv generalizing mutable targets lifetime with
  | var x =>
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hl⟩
      by_cases ha : x = "a"
      · subst ha
        have hslotEq : slot = aSlot :=
          Option.some.inj (hslot.symm.trans hslotA)
        subst hslotEq
        rw [haTy] at hty
        cases hty
        exact ⟨rfl, rfl, rfl, hl.symm.trans haLife⟩
      · rcases hrest ha hslot with hslotTy | hslotTy <;>
          rw [hslotTy] at hty <;> cases hty
  | deref source ih =>
      cases htyping with
      | box hsource =>
          exact False.elim
            (oneBorrowSlot_no_box_lval hslotA haTy hrest source hsource)
      | boxFull hsource =>
          exact False.elim
            (oneBorrowSlot_no_full_box_lval hslotA haTy hrest source hsource)
      | borrow hsource htargets =>
          rcases ih hsource with ⟨hsourceEq, _hmutable, htargetsEq, _hlife⟩
          subst hsourceEq
          subst htargetsEq
          exact False.elim (htargetsNoBorrow htargets)

theorem oneBorrowSlot_contains_inv {env : Env} {aSlot : EnvSlot}
    {slotTargets : List LVal}
    (hslotA : env.slotAt "a" = some aSlot)
    (haTy : aSlot.ty = .ty (.borrow true slotTargets))
    (hrest : ∀ {x slot}, x ≠ "a" → env.slotAt x = some slot →
      slot.ty = .ty .int ∨ slot.ty = .ty .bool) :
    ∀ {x mutable targets},
      env ⊢ x ↝ (.borrow mutable targets) →
      x = "a" ∧ mutable = true ∧ targets = slotTargets := by
  intro x mutable targets hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases ha : x = "a"
  · subst ha
    have hslotEq : slot = aSlot :=
      Option.some.inj (hslot.symm.trans hslotA)
    subst hslotEq
    rw [haTy] at hcontainsTy
    cases hcontainsTy
    exact ⟨rfl, rfl, rfl⟩
  · rcases hrest ha hslot with hslotTy | hslotTy <;>
      rw [hslotTy] at hcontainsTy <;> cases hcontainsTy

theorem retargetAfterIfEnv1_scalar_slot {x : Name} {slot : EnvSlot} :
    retargetAfterIfEnv1.slotAt x = some slot →
    slot.ty = .ty .int ∨ slot.ty = .ty .bool := by
  intro hslot
  by_cases hc : x = "c"
  · subst hc
    have hslotTy : slot.ty = .ty .int := by
      simpa [retargetAfterIfEnv1, retargetAfterIfEnv0,
        retargetAfterIfIntSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    exact Or.inl hslotTy
  · have hnone : retargetAfterIfEnv1.slotAt x = none := by
      simp [retargetAfterIfEnv1, retargetAfterIfEnv0,
        retargetAfterIfIntSlot, Env.update, Env.empty, hc]
    rw [hslot] at hnone
    cases hnone

theorem retargetAfterIfEnv2_scalar_slot {x : Name} {slot : EnvSlot} :
    retargetAfterIfEnv2.slotAt x = some slot →
    slot.ty = .ty .int ∨ slot.ty = .ty .bool := by
  intro hslot
  by_cases hd : x = "d"
  · subst hd
    have hslotTy : slot.ty = .ty .int := by
      simpa [retargetAfterIfEnv2, retargetAfterIfIntSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    exact Or.inl hslotTy
  · by_cases hc : x = "c"
    · subst hc
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetAfterIfEnv2, retargetAfterIfEnv1,
          retargetAfterIfEnv0, retargetAfterIfIntSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      exact Or.inl hslotTy
    · have hnone : retargetAfterIfEnv2.slotAt x = none := by
        simp [retargetAfterIfEnv2, retargetAfterIfEnv1,
          retargetAfterIfEnv0, retargetAfterIfIntSlot, Env.update,
          Env.empty, hd, hc]
      rw [hslot] at hnone
      cases hnone

theorem retargetAfterIfEnv3_scalar_slot {x : Name} {slot : EnvSlot} :
    retargetAfterIfEnv3.slotAt x = some slot →
    slot.ty = .ty .int ∨ slot.ty = .ty .bool := by
  intro hslot
  by_cases he : x = "e"
  · subst he
    have hslotTy : slot.ty = .ty .int := by
      simpa [retargetAfterIfEnv3, retargetAfterIfIntSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    exact Or.inl hslotTy
  · by_cases hd : x = "d"
    · subst hd
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfIntSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      exact Or.inl hslotTy
    · by_cases hc : x = "c"
      · subst hc
        have hslotTy : slot.ty = .ty .int := by
          simpa [retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        exact Or.inl hslotTy
      · have hnone : retargetAfterIfEnv3.slotAt x = none := by
          simp [retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            Env.update, Env.empty, he, hd, hc]
        rw [hslot] at hnone
        cases hnone

theorem retargetAfterIfEnv4_scalar_slot {x : Name} {slot : EnvSlot} :
    retargetAfterIfEnv4.slotAt x = some slot →
    slot.ty = .ty .int ∨ slot.ty = .ty .bool := by
  intro hslot
  by_cases hsth : x = "sth"
  · subst hsth
    have hslotTy : slot.ty = .ty .bool := by
      simpa [retargetAfterIfEnv4, retargetAfterIfBoolSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    exact Or.inr hslotTy
  · by_cases he : x = "e"
    · subst he
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetAfterIfEnv4, retargetAfterIfEnv3,
          retargetAfterIfIntSlot, retargetAfterIfBoolSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      exact Or.inl hslotTy
    · by_cases hd : x = "d"
      · subst hd
        have hslotTy : slot.ty = .ty .int := by
          simpa [retargetAfterIfEnv4, retargetAfterIfEnv3,
            retargetAfterIfEnv2, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        exact Or.inl hslotTy
      · by_cases hc : x = "c"
        · subst hc
          have hslotTy : slot.ty = .ty .int := by
            simpa [retargetAfterIfEnv4, retargetAfterIfEnv3,
              retargetAfterIfEnv2, retargetAfterIfEnv1,
              retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                hslot).symm
          exact Or.inl hslotTy
        · have hnone : retargetAfterIfEnv4.slotAt x = none := by
            simp [retargetAfterIfEnv4, retargetAfterIfEnv3,
              retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
              retargetAfterIfIntSlot, retargetAfterIfBoolSlot, Env.update,
              Env.empty, hsth, he, hd, hc]
          rw [hslot] at hnone
          cases hnone

theorem retargetAfterIfEnv1_not_borrow_lval :
    ∀ (lv : LVal) {mutable targets lifetime},
      ¬ LValTyping retargetAfterIfEnv1 lv
        (.ty (.borrow mutable targets)) lifetime :=
  lval_not_borrow_of_scalar_slots retargetAfterIfEnv1_scalar_slot

theorem retargetAfterIfEnv2_not_borrow_lval :
    ∀ (lv : LVal) {mutable targets lifetime},
      ¬ LValTyping retargetAfterIfEnv2 lv
        (.ty (.borrow mutable targets)) lifetime :=
  lval_not_borrow_of_scalar_slots retargetAfterIfEnv2_scalar_slot

theorem retargetAfterIfEnv3_not_borrow_lval :
    ∀ (lv : LVal) {mutable targets lifetime},
      ¬ LValTyping retargetAfterIfEnv3 lv
        (.ty (.borrow mutable targets)) lifetime :=
  lval_not_borrow_of_scalar_slots retargetAfterIfEnv3_scalar_slot

theorem retargetAfterIfEnv4_not_borrow_lval :
    ∀ (lv : LVal) {mutable targets lifetime},
      ¬ LValTyping retargetAfterIfEnv4 lv
        (.ty (.borrow mutable targets)) lifetime :=
  lval_not_borrow_of_scalar_slots retargetAfterIfEnv4_scalar_slot

theorem retargetAfterIf_c_declare_coherent :
    FreshUpdateCoherenceObligations retargetAfterIfEnv0 "c" .int
      Lifetime.root := by
  exact freshUpdateCoherence_no_borrow (fun lv mutable targets borrowLifetime =>
    by
      intro htyping
      exact retargetAfterIfEnv1_not_borrow_lval lv (by
        simpa [retargetAfterIfEnv1, retargetAfterIfIntSlot] using htyping))

theorem retargetAfterIf_d_declare_coherent :
    FreshUpdateCoherenceObligations retargetAfterIfEnv1 "d" .int
      Lifetime.root := by
  exact freshUpdateCoherence_no_borrow (fun lv mutable targets borrowLifetime =>
    by
      intro htyping
      exact retargetAfterIfEnv2_not_borrow_lval lv (by
        simpa [retargetAfterIfEnv2, retargetAfterIfIntSlot] using htyping))

theorem retargetAfterIf_e_declare_coherent :
    FreshUpdateCoherenceObligations retargetAfterIfEnv2 "e" .int
      Lifetime.root := by
  exact freshUpdateCoherence_no_borrow (fun lv mutable targets borrowLifetime =>
    by
      intro htyping
      exact retargetAfterIfEnv3_not_borrow_lval lv (by
        simpa [retargetAfterIfEnv3, retargetAfterIfIntSlot] using htyping))

theorem retargetAfterIf_sth_declare_coherent :
    FreshUpdateCoherenceObligations retargetAfterIfEnv3 "sth" .bool
      Lifetime.root := by
  exact freshUpdateCoherence_no_borrow (fun lv mutable targets borrowLifetime =>
    by
      intro htyping
      exact retargetAfterIfEnv4_not_borrow_lval lv (by
        simpa [retargetAfterIfEnv4, retargetAfterIfBoolSlot] using htyping))

theorem retargetAfterIfEnv4_c_typing :
    LValTyping retargetAfterIfEnv4 (.var "c") (.ty .int) Lifetime.root := by
  exact @LValTyping.var retargetAfterIfEnv4 "c" retargetAfterIfIntSlot (by
    simp [retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
      retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
      retargetAfterIfBoolSlot, Env.update])

theorem retargetAfterIfEnv5_c_typing :
    LValTyping retargetAfterIfEnv5 (.var "c") (.ty .int) Lifetime.root := by
  exact @LValTyping.var retargetAfterIfEnv5 "c" retargetAfterIfIntSlot (by
    simp [retargetAfterIfEnv5, retargetAfterIfEnv4, retargetAfterIfEnv3,
      retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
      retargetAfterIfIntSlot, retargetAfterIfBoolSlot, retargetAfterIfACSlot,
      Env.update])

theorem retargetAfterIfEnv5_no_box_lval :
    ∀ (lv : LVal) {inner lifetime},
      ¬ LValTyping retargetAfterIfEnv5 lv (.box inner) lifetime
  | .var x, _inner, _lifetime => by
      intro htyping
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hl⟩
      by_cases ha : x = "a"
      · subst ha
        have hslotTy : slot.ty = .ty (.borrow true [.var "c"]) := by
          simpa [retargetAfterIfEnv5, retargetAfterIfACSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hty
        cases hty
      · rcases retargetAfterIfEnv4_scalar_slot (by
            simpa [retargetAfterIfEnv5, Env.update, ha] using hslot) with
          hslotTy | hslotTy <;> rw [hslotTy] at hty <;> cases hty
  | .deref lv, _inner, _lifetime => by
      intro htyping
      cases htyping with
      | box hinner =>
          exact retargetAfterIfEnv5_no_box_lval lv hinner
      | borrow _hborrow htargets =>
          exact LValTargetsTyping.not_box htargets

theorem retargetAfterIfEnv5_borrow_lval_inv :
    ∀ (lv : LVal) {mutable targets lifetime},
      LValTyping retargetAfterIfEnv5 lv (.ty (.borrow mutable targets))
        lifetime →
      lv = .var "a" ∧ mutable = true ∧ targets = [.var "c"] ∧
        lifetime = Lifetime.root := by
  exact oneBorrowSlot_borrow_lval_inv
    (env := retargetAfterIfEnv5) (aSlot := retargetAfterIfACSlot)
    (slotTargets := [.var "c"])
    (by simp [retargetAfterIfEnv5, retargetAfterIfACSlot, Env.update])
    rfl rfl
    (by
      intro x slot hne hslot
      exact retargetAfterIfEnv4_scalar_slot
        (by simpa [retargetAfterIfEnv5, Env.update, hne] using hslot))
    (by
      intro mutable targets lifetime htargets
      cases htargets with
      | singleton htarget =>
          rcases LValTyping.var_inv htarget with ⟨slot, hslot, hty, _hlife⟩
          have hslotTy : slot.ty = .ty .int := by
            simpa [retargetAfterIfEnv5, retargetAfterIfEnv4, retargetAfterIfEnv3,
              retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
              retargetAfterIfACSlot, retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hty
          cases hty
      | cons _hhead hrest _hunion _hintersection =>
          cases hrest)

theorem retargetAfterIf_a_declare_coherent :
    FreshUpdateCoherenceObligations retargetAfterIfEnv4 "a"
      (.borrow true [.var "c"]) Lifetime.root := by
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    rcases retargetAfterIfEnv5_borrow_lval_inv lv (by
        simpa [retargetAfterIfEnv5, retargetAfterIfACSlot] using htyping) with
      ⟨hlv, _hmutable, _htargets, _hlife⟩
    subst hlv
    exact False.elim (hbase rfl)
  · intro lv mutable targets borrowLifetime _hbase htyping
    rcases retargetAfterIfEnv5_borrow_lval_inv lv (by
        simpa [retargetAfterIfEnv5, retargetAfterIfACSlot] using htyping) with
      ⟨_hlv, _hmutable, htargets, _hlife⟩
    subst htargets
    exact ⟨Ty.int, Lifetime.root,
      LValTargetsTyping.singleton retargetAfterIfEnv5_c_typing⟩

theorem retargetAfterIf_declare_c_typing :
    TermTyping retargetAfterIfEnv0 StoreTyping.empty Lifetime.root
      (.letMut "c" (.val (.int 0))) .unit retargetAfterIfEnv1 := by
  exact TermTyping.declare
    (by simp [retargetAfterIfEnv0, Env.fresh, Env.empty])
    (TermTyping.const ValueTyping.int)
    (by simp [retargetAfterIfEnv0, Env.fresh, Env.empty])
    retargetAfterIf_c_declare_coherent
    (by simp [retargetAfterIfEnv1, retargetAfterIfIntSlot])

theorem retargetAfterIf_declare_d_typing :
    TermTyping retargetAfterIfEnv1 StoreTyping.empty Lifetime.root
      (.letMut "d" (.val (.int 0))) .unit retargetAfterIfEnv2 := by
  exact TermTyping.declare
    (by simp [retargetAfterIfEnv1, retargetAfterIfEnv0, Env.fresh,
      Env.update, Env.empty])
    (TermTyping.const ValueTyping.int)
    (by simp [retargetAfterIfEnv1, retargetAfterIfEnv0, Env.fresh,
      Env.update, Env.empty])
    retargetAfterIf_d_declare_coherent
    (by simp [retargetAfterIfEnv2, retargetAfterIfIntSlot])

theorem retargetAfterIf_declare_e_typing :
    TermTyping retargetAfterIfEnv2 StoreTyping.empty Lifetime.root
      (.letMut "e" (.val (.int 0))) .unit retargetAfterIfEnv3 := by
  exact TermTyping.declare
    (by simp [retargetAfterIfEnv2, retargetAfterIfEnv1,
      retargetAfterIfEnv0, Env.fresh, Env.update, Env.empty])
    (TermTyping.const ValueTyping.int)
    (by simp [retargetAfterIfEnv2, retargetAfterIfEnv1,
      retargetAfterIfEnv0, Env.fresh, Env.update, Env.empty])
    retargetAfterIf_e_declare_coherent
    (by simp [retargetAfterIfEnv3, retargetAfterIfIntSlot])

theorem retargetAfterIf_declare_sth_typing :
    TermTyping retargetAfterIfEnv3 StoreTyping.empty Lifetime.root
      (.letMut "sth" (.val (.bool true))) .unit retargetAfterIfEnv4 := by
  exact TermTyping.declare
    (by simp [retargetAfterIfEnv3, retargetAfterIfEnv2,
      retargetAfterIfEnv1, retargetAfterIfEnv0, Env.fresh, Env.update,
      Env.empty])
    (TermTyping.const ValueTyping.bool)
    (by simp [retargetAfterIfEnv3, retargetAfterIfEnv2,
      retargetAfterIfEnv1, retargetAfterIfEnv0, Env.fresh, Env.update,
      Env.empty])
    retargetAfterIf_sth_declare_coherent
    (by simp [retargetAfterIfEnv4, retargetAfterIfBoolSlot])

theorem retargetAfterIf_declare_a_typing :
    TermTyping retargetAfterIfEnv4 StoreTyping.empty Lifetime.root
      (.letMut "a" (.borrow true (.var "c"))) .unit retargetAfterIfEnv5 := by
  exact TermTyping.declare
    (by simp [retargetAfterIfEnv4, retargetAfterIfEnv3,
      retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
      Env.fresh, Env.update, Env.empty])
    (TermTyping.mutBorrow retargetAfterIfEnv4_c_typing
      (Mutable.var (by
        show retargetAfterIfEnv4.slotAt "c" = some retargetAfterIfIntSlot
        simp [retargetAfterIfEnv4, retargetAfterIfEnv3,
          retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
          retargetAfterIfIntSlot, retargetAfterIfBoolSlot, Env.update]))
      (not_writeProhibited_of_no_borrows
        (env_not_contains_borrow_of_scalar_slots
          retargetAfterIfEnv4_scalar_slot)
        (.var "c")))
    (by simp [retargetAfterIfEnv4, retargetAfterIfEnv3,
      retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
      Env.fresh, Env.update, Env.empty])
    retargetAfterIf_a_declare_coherent
    (by simp [retargetAfterIfEnv5, retargetAfterIfACSlot])

theorem retargetAfterIf_declarations_typing :
    TermListTyping retargetAfterIfEnv0 StoreTyping.empty Lifetime.root
      [.letMut "c" (.val (.int 0)),
       .letMut "d" (.val (.int 0)),
       .letMut "e" (.val (.int 0)),
       .letMut "sth" (.val (.bool true)),
       .letMut "a" (.borrow true (.var "c"))]
      .unit retargetAfterIfEnv5 := by
  exact TermListTyping.cons retargetAfterIf_declare_c_typing
    (TermListTyping.cons retargetAfterIf_declare_d_typing
      (TermListTyping.cons retargetAfterIf_declare_e_typing
        (TermListTyping.cons retargetAfterIf_declare_sth_typing
          (TermListTyping.singleton retargetAfterIf_declare_a_typing))))

/--
Accepted `if/else` with nontrivial pointer effects in the branches.

The starting environment contains `x : int`, `y : int`, and `p : &mut x`.
The guard compares through the pointer with `*p == 1`.  The true branch
retargets the pointer with `p = &mut y`; the false branch writes through the
pointer with `*p = 1`.  Since `x` and `y` have compatible shape, the branch
environments join to `p : &mut [y, x]`.
-/
def pointerIfXSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def pointerIfYSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def pointerIfPXSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "x"]), lifetime := Lifetime.root }

def pointerIfPYSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "y"]), lifetime := Lifetime.root }

def pointerIfJoinPSlot : EnvSlot :=
  { ty := .ty (.borrow true [.var "y", .var "x"]), lifetime := Lifetime.root }

def pointerIfEnv : Env :=
  ((Env.empty.update "x" pointerIfXSlot).update "y" pointerIfYSlot).update
    "p" pointerIfPXSlot

def pointerIfRetargetEnv : Env :=
  pointerIfEnv.update "p" pointerIfPYSlot

def pointerIfWriteEnv : Env :=
  (pointerIfEnv.update "x" pointerIfXSlot).update "p" pointerIfPXSlot

def pointerIfJoinEnv : Env :=
  ((Env.empty.update "x" pointerIfXSlot).update "y" pointerIfYSlot).update
    "p" pointerIfJoinPSlot

def pointerRetargetBranch : Term :=
  .assign (.var "p") (.borrow true (.var "y"))

def pointerWriteBranch : Term :=
  .assign (.deref (.var "p")) (.val (.int 1))

def ifPointerAssignment : Term :=
  .ite (.eq (.copy (.deref (.var "p"))) (.val (.int 1)))
    pointerRetargetBranch pointerWriteBranch

theorem pointerIf_x_typing :
    LValTyping pointerIfEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfEnv "x" pointerIfXSlot (by
    simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
      Env.update])

theorem pointerIf_y_typing :
    LValTyping pointerIfEnv (.var "y") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfEnv "y" pointerIfYSlot (by
    simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update])

theorem pointerIf_p_typing :
    LValTyping pointerIfEnv (.var "p")
      (.ty (.borrow true [.var "x"])) Lifetime.root := by
  exact @LValTyping.var pointerIfEnv "p" pointerIfPXSlot (by
    simp [pointerIfEnv, pointerIfPXSlot, Env.update])

theorem pointerIf_deref_p_typing :
    LValTyping pointerIfEnv (.deref (.var "p")) (.ty .int) Lifetime.root := by
  exact LValTyping.borrow pointerIf_p_typing
    (LValTargetsTyping.singleton pointerIf_x_typing)

theorem pointerIf_not_readProhibited_deref_p :
    ¬ ReadProhibited pointerIfEnv (.deref (.var "p")) := by
  intro hread
  rcases hread with ⟨root, targets, target, hcontains, htarget,
    hconflict⟩
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hroot : root = "p"
  · subst hroot
    have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
      simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hcontainsTy
    cases hcontainsTy with
    | here =>
        simp at htarget
        subst htarget
        simp [PathConflicts, LVal.base] at hconflict
  · by_cases hrootY : root = "y"
    · subst hrootY
      have hslotTy : slot.ty = .ty .int := by
        simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hrootX : root = "x"
      · subst hrootX
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · have hnone : pointerIfEnv.slotAt root = none := by
          simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update, Env.empty, hroot, hrootY, hrootX]
        rw [hslot] at hnone
        cases hnone

theorem pointerIfCondition_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      (.eq (.copy (.deref (.var "p"))) (.val (.int 1))) .bool pointerIfEnv := by
  refine TermTyping.eq_finite
    (TermTyping.copy pointerIf_deref_p_typing CopyTy.int
      pointerIf_not_readProhibited_deref_p)
    (((Env.finiteSupport_empty.update).update).update)
    StoreTyping.finiteSupport_empty
    ?_
    CopyTy.int
    CopyTy.int
    ShapeCompatible.int
  intro ghost hfresh _htypeFresh _htyFresh _hstoreFresh _hnotMention
  exact ⟨_,
    TermTyping.const ValueTyping.int,
    (Env.erase_update_fresh pointerIfEnv ghost
      { ty := .ty Ty.int, lifetime := Lifetime.root } hfresh).symm⟩

theorem pointerIf_not_writeProhibited_y :
    ¬ WriteProhibited pointerIfEnv (.var "y") := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨root, targets, target, hcontains, htarget,
      hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
        simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy with
      | here =>
          simp at htarget
          subst htarget
          simp [PathConflicts, LVal.base] at hconflict
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfEnv.slotAt root = none := by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone
  · rcases himm with ⟨root, targets, target, hcontains, htarget,
      hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
        simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfEnv.slotAt root = none := by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone

theorem pointerIf_y_mutable : Mutable pointerIfEnv (.var "y") :=
  @Mutable.var pointerIfEnv "y" pointerIfYSlot
    (by simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update])

theorem pointerIfRetarget_y_typing :
    LValTyping pointerIfRetargetEnv (.var "y") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfRetargetEnv "y" pointerIfYSlot (by
    simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot, pointerIfPYSlot,
      Env.update])

theorem pointerIfRetarget_p_typing :
    LValTyping pointerIfRetargetEnv (.var "p")
      (.ty (.borrow true [.var "y"])) Lifetime.root := by
  exact @LValTyping.var pointerIfRetargetEnv "p" pointerIfPYSlot (by
    simp [pointerIfRetargetEnv, pointerIfPYSlot, Env.update])

theorem pointerIf_borrow_y_wellFormed :
    WellFormedTy pointerIfEnv (.borrow true [.var "y"]) Lifetime.root := by
  exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
    intro target htarget
    simp at htarget
    subst htarget
    exact ⟨.int, Lifetime.root, pointerIf_y_typing,
      LifetimeOutlives.refl Lifetime.root,
      ⟨pointerIfYSlot, by
        simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update,
          LVal.base],
        LifetimeOutlives.refl Lifetime.root⟩⟩))

theorem pointerIf_shape_px_py :
    ShapeCompatible pointerIfEnv
      (.ty (.borrow true [.var "x"])) (.ty (.borrow true [.var "y"])) := by
  exact ShapeCompatible.borrow
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, pointerIf_x_typing⟩)
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, pointerIf_y_typing⟩)
    ShapeCompatible.int

theorem pointerIf_retarget_write :
    EnvWrite 0 pointerIfEnv (.var "p") (.borrow true [.var "y"])
      pointerIfRetargetEnv := by
  simpa [pointerIfRetargetEnv, pointerIfPYSlot, pointerIfPXSlot, LVal.base] using
    (@EnvWrite.intro 0 pointerIfEnv pointerIfEnv (.var "p")
      pointerIfPXSlot (.borrow true [.var "y"]) (.ty (.borrow true [.var "y"]))
      (by
        show pointerIfEnv.slotAt "p" = some pointerIfPXSlot
        simp [pointerIfEnv, pointerIfPXSlot, Env.update])
      UpdateAtPath.strong)

theorem pointerIf_retarget_effective_write_written {result : Env}
    {written : LVal} :
    EnvWriteEffectiveWrite 0 pointerIfEnv (.var "p")
      (.borrow true [.var "y"]) result written →
    written = .var "p" := by
  intro hwrite
  cases hwrite with
  | intro _hslot hupdate =>
      cases hupdate with
      | strong => rfl

theorem pointerIf_retarget_noStale :
    EnvWriteNoStaleBorrowTargets 0 pointerIfEnv (.var "p")
      (.borrow true [.var "y"]) pointerIfRetargetEnv := by
  intro written x slot mutable targets target hwrite hslot hcontains htarget
    hprefix
  have hwritten := pointerIf_retarget_effective_write_written hwrite
  subst written
  rcases hcontains with ⟨containsSlot, hcontainsSlot, hcontainsTy⟩
  have hcontainsSlotEq : containsSlot = slot :=
    Option.some.inj (hcontainsSlot.symm.trans hslot)
  subst containsSlot
  by_cases hp : x = "p"
  · subst hp
    have hslotTy : slot.ty = .ty (.borrow true [.var "y"]) := by
      simpa [pointerIfRetargetEnv, pointerIfPYSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hcontainsTy
    cases hcontainsTy with
    | here =>
        simp at htarget
        subst htarget
        cases hprefix with
        | direct hprefix =>
            simp [LVal.StrictPrefixOf, StrictPathPrefix, LVal.base,
              LVal.path] at hprefix
  · by_cases hx : x = "x"
    · subst hx
      have hslotTy : slot.ty = .ty .int := by
        simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
          pointerIfYSlot, pointerIfPYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hy : x = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPYSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · have hnone : pointerIfRetargetEnv.slotAt x = none := by
          simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
            pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty, hp, hx,
            hy]
        rw [hslot] at hnone
        cases hnone

theorem pointerIf_retarget_ranked :
    ∃ φ, LinearizedBy φ pointerIfEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ pointerIfRetargetEnv (.borrow true [.var "y"]) := by
  let φ : Name → Nat := fun name => if name = "p" then 1 else 0
  refine ⟨φ, ?linearized, ?below⟩
  · intro root slot hslot v hv
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
        simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
      subst v
      simp [φ, LVal.base]
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars] at hv
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hv
          simp [PartialTy.vars, Ty.vars] at hv
        · have hnone : pointerIfEnv.slotAt root = none := by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone
  · intro root slot mutable targets target hslot hcontains htarget hrhs
    rcases hrhs with ⟨rhsMutable, rhsTargets, hrhsContains, hrhsTarget⟩
    cases hrhsContains with
    | here =>
        by_cases hp : root = "p"
        · subst hp
          have hslotTy : slot.ty = .ty (.borrow true [.var "y"]) := by
            simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfPYSlot,
              Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontains
          cases hcontains with
          | here =>
              simp at htarget
              subst htarget
              simp [φ, LVal.base]
        · by_cases hy : root = "y"
          · subst hy
            have hslotTy : slot.ty = .ty .int := by
              simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
                pointerIfPYSlot, Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
            rw [hslotTy] at hcontains
            cases hcontains
          · by_cases hx : root = "x"
            · subst hx
              have hslotTy : slot.ty = .ty .int := by
                simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                  pointerIfYSlot, pointerIfPYSlot, Env.update] using
                  (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
              rw [hslotTy] at hcontains
              cases hcontains
            · have hnone : pointerIfRetargetEnv.slotAt root = none := by
                simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                  pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty, hp, hy, hx]
              rw [hslot] at hnone
              cases hnone

theorem pointerIfRetarget_not_writeProhibited_p :
    ¬ WriteProhibited pointerIfRetargetEnv (.var "p") := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨root, targets, target, hcontains, htarget,
      hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "y"]) := by
        simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfPYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy with
      | here =>
          simp at htarget
          subst htarget
          simp [PathConflicts, LVal.base] at hconflict
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPYSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfRetargetEnv.slotAt root = none := by
            simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone
  · rcases himm with ⟨root, targets, target, hcontains, htarget,
      hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "y"]) := by
        simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfPYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPYSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfRetargetEnv.slotAt root = none := by
            simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone

theorem pointerIfEnv_contained :
    ContainedBorrowsWellFormed pointerIfEnv := by
  intro root slot mutable targets hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hp : root = "p"
  · subst hp
    have hcontainedTy : containedSlot.ty = .ty (.borrow true [.var "x"]) := by
      simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
          hcontainedSlot).symm
    rw [hcontainedTy] at hcontainsTy
    cases hcontainsTy with
    | here =>
        intro target htarget
        simp at htarget
        subst htarget
        exact ⟨.int, Lifetime.root, pointerIf_x_typing,
          LifetimeOutlives.refl Lifetime.root,
          ⟨pointerIfXSlot, by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, LVal.base],
            LifetimeOutlives.refl Lifetime.root⟩⟩
  · by_cases hy : root = "y"
    · subst hy
      have hcontainedTy : containedSlot.ty = .ty .int := by
        simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
            hcontainedSlot).symm
      rw [hcontainedTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hx : root = "x"
      · subst hx
        have hcontainedTy : containedSlot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hcontainedSlot).symm
        rw [hcontainedTy] at hcontainsTy
        cases hcontainsTy
      · have hnone : pointerIfEnv.slotAt root = none := by
          simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update, Env.empty, hp, hy, hx]
        rw [hslot] at hnone
        cases hnone

theorem pointerIfRetarget_slot_borrows_wellFormed :
    PartialTyBorrowsWellFormedInSlot pointerIfRetargetEnv
      pointerIfPYSlot.lifetime pointerIfPYSlot.ty := by
  intro mutable targets hcontains
  cases hcontains with
  | here =>
      intro target htarget
      simp at htarget
      subst htarget
      exact ⟨.int, Lifetime.root, pointerIfRetarget_y_typing,
        LifetimeOutlives.refl Lifetime.root,
        ⟨pointerIfYSlot, by
          simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPYSlot, Env.update, LVal.base],
          LifetimeOutlives.refl Lifetime.root⟩⟩

theorem pointerIfRetarget_contained :
    ContainedBorrowsWellFormed pointerIfRetargetEnv := by
  simpa [pointerIfRetargetEnv] using
    (ContainedBorrowsWellFormed.update_slot
      (env := pointerIfEnv) (x := "p") (slot := pointerIfPYSlot)
      pointerIfEnv_contained pointerIfRetarget_slot_borrows_wellFormed
      pointerIfRetarget_not_writeProhibited_p)

theorem pointerLike_old_root_int {env : Env}
    (hx : env.slotAt "x" = some pointerIfXSlot)
    (hy : env.slotAt "y" = some pointerIfYSlot)
    (hnone : ∀ {name : Name}, name ≠ "x" → name ≠ "y" → name ≠ "p" →
      env.slotAt name = none) :
    ∀ {lv partialTy lifetime},
      LVal.base lv ≠ "p" →
      LValTyping env lv partialTy lifetime →
      (lv = .var "x" ∨ lv = .var "y") ∧
        partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  intro lv
  induction lv with
  | var name =>
      intro partialTy lifetime hbase htyping
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlife⟩
      by_cases hnameX : name = "x"
      · subst hnameX
        have hslotEq : slot = pointerIfXSlot :=
          Option.some.inj (hslot.symm.trans hx)
        subst hslotEq
        exact ⟨Or.inl rfl,
          by simpa [pointerIfXSlot] using hty.symm,
          by simpa [pointerIfXSlot] using hlife.symm⟩
      · by_cases hnameY : name = "y"
        · subst hnameY
          have hslotEq : slot = pointerIfYSlot :=
            Option.some.inj (hslot.symm.trans hy)
          subst hslotEq
          exact ⟨Or.inr rfl,
            by simpa [pointerIfYSlot] using hty.symm,
            by simpa [pointerIfYSlot] using hlife.symm⟩
        · by_cases hnameP : name = "p"
          · subst hnameP
            exact False.elim (hbase rfl)
          · have hnoneSlot : env.slotAt name = none :=
              hnone hnameX hnameY hnameP
            rw [hslot] at hnoneSlot
            cases hnoneSlot
  | deref source ih =>
      intro partialTy lifetime hbase htyping
      cases htyping with
      | box hsource =>
          rcases ih (by simpa [LVal.base] using hbase) hsource with
            ⟨_hlv, hpartialTy, _hlife⟩
          cases hpartialTy
      | boxFull hsource =>
          rcases ih (by simpa [LVal.base] using hbase) hsource with
            ⟨_hlv, hpartialTy, _hlife⟩
          cases hpartialTy
      | borrow hsource _htargets =>
          rcases ih (by simpa [LVal.base] using hbase) hsource with
            ⟨_hlv, hpartialTy, _hlife⟩
          cases hpartialTy

theorem pointerLike_p_root_facts_full {env : Env} {pSlot : EnvSlot}
    {rootTargets : List LVal}
    (hp : env.slotAt "p" = some pSlot)
    (hpTy : pSlot.ty = .ty (.borrow true rootTargets))
    (hpLife : pSlot.lifetime = Lifetime.root)
    (htargetsNoBorrow : ∀ {mutable targets lifetime},
      ¬ LValTargetsTyping env rootTargets (.ty (.borrow mutable targets))
        lifetime)
    (htargetsNoBox : ∀ {inner lifetime},
      ¬ LValTargetsTyping env rootTargets (.box inner) lifetime)
    (htargetsNoFullBox : ∀ {inner lifetime},
      ¬ LValTargetsTyping env rootTargets (.ty (.box inner)) lifetime) :
    ∀ {lv},
      LVal.base lv = "p" →
      (∀ {inner lifetime}, ¬ LValTyping env lv (.box inner) lifetime) ∧
      (∀ {inner lifetime}, ¬ LValTyping env lv (.ty (.box inner)) lifetime) ∧
      (∀ {mutable targets lifetime},
        LValTyping env lv (.ty (.borrow mutable targets)) lifetime →
        lv = .var "p" ∧ mutable = true ∧ targets = rootTargets ∧
          lifetime = Lifetime.root) := by
  intro lv
  induction lv with
  | var name =>
      intro hbase
      simp [LVal.base] at hbase
      subst hbase
      constructor
      · intro inner lifetime htyping
        rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hlife⟩
        have hslotEq : slot = pSlot :=
          Option.some.inj (hslot.symm.trans hp)
        subst hslotEq
        rw [hpTy] at hty
        cases hty
      constructor
      · intro inner lifetime htyping
        rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hlife⟩
        have hslotEq : slot = pSlot :=
          Option.some.inj (hslot.symm.trans hp)
        subst hslotEq
        rw [hpTy] at hty
        cases hty
      · intro mutable targets lifetime htyping
        rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, hlife⟩
        have hslotEq : slot = pSlot :=
          Option.some.inj (hslot.symm.trans hp)
        subst hslotEq
        rw [hpTy] at hty
        cases hty
        exact ⟨rfl, rfl, rfl, hlife.symm.trans hpLife⟩
  | deref source ih =>
      intro hbase
      rcases ih (by simpa [LVal.base] using hbase) with
        ⟨hsourceNoBox, hsourceNoFullBox, hsourceBorrowInv⟩
      constructor
      · intro inner lifetime htyping
        cases htyping with
        | box hsource =>
            exact hsourceNoBox hsource
        | borrow hsource htargets =>
            rcases hsourceBorrowInv hsource with
              ⟨hsourceEq, _hmutable, htargetsEq, _hlife⟩
            subst hsourceEq
            subst htargetsEq
            exact False.elim (htargetsNoBox htargets)
      constructor
      · intro inner lifetime htyping
        cases htyping with
        | box hsource =>
            exact hsourceNoBox hsource
        | boxFull hsource =>
            exact hsourceNoFullBox hsource
        | borrow hsource htargets =>
            rcases hsourceBorrowInv hsource with
              ⟨hsourceEq, _hmutable, htargetsEq, _hlife⟩
            subst hsourceEq
            subst htargetsEq
            exact False.elim (htargetsNoFullBox htargets)
      · intro mutable targets lifetime htyping
        cases htyping with
        | box hsource =>
            exact False.elim (hsourceNoBox hsource)
        | boxFull hsource =>
            exact False.elim (hsourceNoFullBox hsource)
        | borrow hsource htargets =>
            rcases hsourceBorrowInv hsource with
              ⟨hsourceEq, _hmutable, htargetsEq, _hlife⟩
            subst hsourceEq
            subst htargetsEq
            exact False.elim (htargetsNoBorrow htargets)

theorem pointerIfRetarget_old_root_int : ∀ {lv partialTy lifetime},
    LVal.base lv ≠ "p" →
    LValTyping pointerIfRetargetEnv lv partialTy lifetime →
    (lv = .var "x" ∨ lv = .var "y") ∧
      partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  exact pointerLike_old_root_int
    (env := pointerIfRetargetEnv)
    (by simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot, pointerIfYSlot,
      pointerIfPYSlot, Env.update])
    (by simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot, pointerIfPYSlot,
      Env.update])
    (by
      intro name hnameX hnameY hnameP
      simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot, pointerIfYSlot,
        pointerIfPYSlot, Env.update, Env.empty, hnameX, hnameY, hnameP])

theorem pointerIfRetarget_no_y_targets_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping pointerIfRetargetEnv [.var "y"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htyping
  generalize hpartialTy :
      (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIfRetarget_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      rcases pointerIfRetarget_old_root_int (by simp [LVal.base]) _hhead with
        ⟨_, hheadTy, _⟩
      injection hheadTy with hheadTy
      subst hheadTy
      have hupper : PartialTyStrengthens (.ty .int) partialTy :=
        _hunion.1 (by simp)
      rw [← hpartialTy] at hupper
      cases PartialTyStrengthens.from_int_inv hupper

theorem pointerIfRetarget_no_y_targets_box {inner lifetime} :
    ¬ LValTargetsTyping pointerIfRetargetEnv [.var "y"] (.box inner)
      lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIfRetarget_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      rcases pointerIfRetarget_old_root_int (by simp [LVal.base]) _hhead with
        ⟨_, hheadTy, _⟩
      injection hheadTy with hheadTy
      subst hheadTy
      have hupper : PartialTyStrengthens (.ty .int) partialTy :=
        _hunion.1 (by simp)
      rw [← hpartialTy] at hupper
      cases hupper

theorem pointerIfRetarget_no_y_targets_full_box {inner lifetime} :
    ¬ LValTargetsTyping pointerIfRetargetEnv [.var "y"] (.ty (.box inner))
      lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.ty (Ty.box inner)) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIfRetarget_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      cases hrest

theorem pointerIfRetarget_p_root_facts : ∀ {lv},
    LVal.base lv = "p" →
    (∀ {inner lifetime},
      ¬ LValTyping pointerIfRetargetEnv lv (.box inner) lifetime) ∧
    (∀ {mutable targets lifetime},
      LValTyping pointerIfRetargetEnv lv
        (.ty (.borrow mutable targets)) lifetime →
      lv = .var "p" ∧ mutable = true ∧ targets = [.var "y"] ∧
        lifetime = Lifetime.root) := by
  intro lv hbase
  have hfacts := pointerLike_p_root_facts_full
    (env := pointerIfRetargetEnv) (pSlot := pointerIfPYSlot)
    (rootTargets := [.var "y"])
    (by simp [pointerIfRetargetEnv, pointerIfPYSlot, Env.update])
    rfl rfl
    pointerIfRetarget_no_y_targets_borrow
    pointerIfRetarget_no_y_targets_box
    pointerIfRetarget_no_y_targets_full_box
    hbase
  exact ⟨hfacts.1, hfacts.2.2⟩

theorem pointerIfRetarget_coherent : Coherent pointerIfRetargetEnv := by
  intro lv mutable targets borrowLifetime htyping
  by_cases hbase : LVal.base lv = "p"
  · rcases (pointerIfRetarget_p_root_facts hbase).2 htyping with
      ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨.ty Ty.int, Lifetime.root,
      LValTargetsMaybeTyping.singleton pointerIfRetarget_y_typing⟩
  · rcases pointerIfRetarget_old_root_int hbase htyping with
      ⟨_, hpartialTy, _⟩
    cases hpartialTy

theorem pointerRetargetBranch_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      pointerRetargetBranch .unit pointerIfRetargetEnv := by
  unfold pointerRetargetBranch
  exact TermTyping.assign
    (TermTyping.mutBorrow pointerIf_y_typing pointerIf_y_mutable
      pointerIf_not_writeProhibited_y)
    pointerIf_p_typing
    pointerIf_shape_px_py
    pointerIf_borrow_y_wellFormed
    pointerIf_retarget_write
    pointerIf_retarget_noStale
    pointerIf_retarget_ranked
    (Coherent.whenInitialized pointerIfRetarget_coherent)
    (EnvWriteRhsTargetsWellFormed.of_containedBorrowsWellFormed pointerIfRetarget_contained)
    pointerIfRetarget_not_writeProhibited_p

theorem pointerIf_write_x :
    EnvWrite 1 pointerIfEnv (.var "x") .int
      (pointerIfEnv.update "x" pointerIfXSlot) := by
  simpa [pointerIfXSlot, LVal.base] using
    (@EnvWrite.intro 1 pointerIfEnv pointerIfEnv (.var "x")
      pointerIfXSlot .int (.ty .int)
      (by
        show pointerIfEnv.slotAt "x" = some pointerIfXSlot
        simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
          Env.update])
      (UpdateAtPath.weak ShapeCompatible.int (PartialTyJoin.self (.ty .int))))

theorem pointerIf_write_deref_p :
    EnvWrite 0 pointerIfEnv (.deref (.var "p")) .int pointerIfWriteEnv := by
  have htargets : WriteBorrowTargets 1 pointerIfEnv [] [.var "x"] .int
      (pointerIfEnv.update "x" pointerIfXSlot) := by
    exact WriteBorrowTargets.singleton pointerIf_write_x
      ⟨.int, Lifetime.root, pointerIf_x_typing⟩
  simpa [pointerIfWriteEnv, pointerIfPXSlot, pointerIfXSlot, LVal.base,
      LVal.path] using
    (@EnvWrite.intro 0 pointerIfEnv (pointerIfEnv.update "x" pointerIfXSlot)
      (.deref (.var "p")) pointerIfPXSlot .int
      (.ty (.borrow true [.var "x"]))
      (by
        show pointerIfEnv.slotAt "p" = some pointerIfPXSlot
        simp [pointerIfEnv, pointerIfPXSlot, Env.update])
      (@UpdateAtPath.mutBorrow pointerIfEnv
        (pointerIfEnv.update "x" pointerIfXSlot) 0 [] [.var "x"] .int
        htargets))

theorem pointerIf_write_effective_write_written {result : Env}
    {written : LVal} :
    EnvWriteEffectiveWrite 0 pointerIfEnv (.deref (.var "p")) .int result
      written →
    written = .var "x" := by
  intro hwrite
  cases hwrite with
  | @intro _rank _env₁ _env₂ _lv _written sourceSlot _ty _updatedTy
      hslot hupdate =>
      have hslotEq : sourceSlot = pointerIfPXSlot := by
        simpa [pointerIfEnv, pointerIfPXSlot, Env.update, LVal.base] using
          hslot.symm
      subst sourceSlot
      cases hupdate with
      | mutBorrow htargets =>
          cases htargets with
          | singleton htargetWrite =>
              cases htargetWrite with
              | intro _htargetSlot htargetUpdate =>
                  cases htargetUpdate with
                  | weak _hshape _hjoin => rfl
          | consHead htargetWrite _hrest _hjoin =>
              cases htargetWrite with
              | intro _htargetSlot htargetUpdate =>
                  cases htargetUpdate with
                  | weak _hshape _hjoin => rfl
          | consTail _htargetWrite hrest _hjoin =>
              cases hrest

/-- Regression for reborrow-chain writes after removing borrow target annotations:
the outer borrow target list is preserved while the write is fanned out through
the selected target. -/
theorem reborrowChain_updateAtPath_preserves_outer_targets {env result : Env}
    (hwrites : WriteBorrowTargets 1 env [] [.var "b"]
      (.borrow true [.var "c"]) result) :
    UpdateAtPath 0 env [()]
      (.ty (.borrow true [.var "b"]))
      (.borrow true [.var "c"])
      result
      (.ty (.borrow true [.var "b"])) := by
  exact UpdateAtPath.mutBorrow hwrites

theorem pointerIf_write_ranked :
    ∃ φ, LinearizedBy φ pointerIfEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ pointerIfWriteEnv .int := by
  refine ⟨pointerIf_retarget_ranked.choose,
    pointerIf_retarget_ranked.choose_spec.1, ?below⟩
  · intro root slot mutable targets target hslot hcontains _htarget hrhs
    rcases hrhs with ⟨rhsMutable, rhsTargets, hrhsContains, _hrhsTarget⟩
    cases hrhsContains

theorem pointerIf_old_root_int : ∀ {lv partialTy lifetime},
    LVal.base lv ≠ "p" →
    LValTyping pointerIfEnv lv partialTy lifetime →
    (lv = .var "x" ∨ lv = .var "y") ∧
      partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  exact pointerLike_old_root_int
    (env := pointerIfEnv)
    (by simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
      Env.update])
    (by simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update])
    (by
      intro name hnameX hnameY hnameP
      simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
        Env.update, Env.empty, hnameX, hnameY, hnameP])

theorem pointerIf_no_x_targets_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping pointerIfEnv [.var "x"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htyping
  generalize hpartialTy :
      (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIf_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      rcases pointerIf_old_root_int (by simp [LVal.base]) _hhead with
        ⟨_, hheadTy, _⟩
      injection hheadTy with hheadTy
      subst hheadTy
      have hupper : PartialTyStrengthens (.ty .int) partialTy :=
        _hunion.1 (by simp)
      rw [← hpartialTy] at hupper
      cases PartialTyStrengthens.from_int_inv hupper

theorem pointerIf_no_x_targets_box {inner lifetime} :
    ¬ LValTargetsTyping pointerIfEnv [.var "x"] (.box inner) lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIf_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      rcases pointerIf_old_root_int (by simp [LVal.base]) _hhead with
        ⟨_, hheadTy, _⟩
      injection hheadTy with hheadTy
      subst hheadTy
      have hupper : PartialTyStrengthens (.ty .int) partialTy :=
        _hunion.1 (by simp)
      rw [← hpartialTy] at hupper
      cases hupper

theorem pointerIf_no_x_targets_full_box {inner lifetime} :
    ¬ LValTargetsTyping pointerIfEnv [.var "x"] (.ty (.box inner)) lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.ty (Ty.box inner)) = partialTy at htyping
  cases htyping with
  | singleton htarget =>
      rcases pointerIf_old_root_int (by simp [LVal.base]) htarget with
        ⟨_, htargetTy, _⟩
      rw [← hpartialTy] at htargetTy
      cases htargetTy
  | cons _hhead hrest _hunion _hlifetime =>
      cases hrest

theorem pointerIf_p_root_facts : ∀ {lv},
    LVal.base lv = "p" →
    (∀ {inner lifetime}, ¬ LValTyping pointerIfEnv lv (.box inner) lifetime) ∧
    (∀ {mutable targets lifetime},
      LValTyping pointerIfEnv lv (.ty (.borrow mutable targets)) lifetime →
      lv = .var "p" ∧ mutable = true ∧ targets = [.var "x"] ∧
        lifetime = Lifetime.root) := by
  intro lv hbase
  have hfacts := pointerLike_p_root_facts_full
    (env := pointerIfEnv) (pSlot := pointerIfPXSlot)
    (rootTargets := [.var "x"])
    (by simp [pointerIfEnv, pointerIfPXSlot, Env.update])
    rfl rfl
    pointerIf_no_x_targets_borrow
    pointerIf_no_x_targets_box
    pointerIf_no_x_targets_full_box
    hbase
  exact ⟨hfacts.1, hfacts.2.2⟩

theorem pointerIf_coherent : Coherent pointerIfEnv := by
  intro lv mutable targets borrowLifetime htyping
  by_cases hbase : LVal.base lv = "p"
  · rcases (pointerIf_p_root_facts hbase).2 htyping with
      ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨.ty Ty.int, Lifetime.root,
      LValTargetsMaybeTyping.singleton pointerIf_x_typing⟩
  · rcases pointerIf_old_root_int hbase htyping with ⟨_, hpartialTy, _⟩
    cases hpartialTy

theorem env_ext_local (left right : Env)
    (h : ∀ x, left.slotAt x = right.slotAt x) : left = right := by
  cases left with
  | mk leftSlotAt =>
      cases right with
      | mk rightSlotAt =>
          have hfun : leftSlotAt = rightSlotAt := funext h
          subst hfun
          rfl

theorem pointerIfWriteEnv_eq : pointerIfWriteEnv = pointerIfEnv := by
  apply env_ext_local
  intro name
  by_cases hp : name = "p" <;> by_cases hx : name = "x" <;>
    by_cases hy : name = "y" <;>
    simp [pointerIfWriteEnv, pointerIfEnv, pointerIfXSlot, pointerIfYSlot,
      pointerIfPXSlot, Env.update, Env.empty, hp, hx, hy]

theorem pointerIf_write_coherent : Coherent pointerIfWriteEnv := by
  rw [pointerIfWriteEnv_eq]
  exact pointerIf_coherent

theorem pointerIf_not_writeProhibited_deref_p :
    ¬ WriteProhibited pointerIfWriteEnv (.deref (.var "p")) := by
  rw [pointerIfWriteEnv_eq]
  intro hwrite
  rcases hwrite with hread | himm
  · exact pointerIf_not_readProhibited_deref_p (by
      simpa using hread)
  · rcases himm with ⟨root, targets, target, hcontains, htarget,
      hconflict⟩
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · subst hp
      have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
        simpa [pointerIfWriteEnv, pointerIfEnv, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfWriteEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPXSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfWriteEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPXSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfEnv.slotAt root = none := by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
              Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone

theorem pointerIf_write_noStale :
    EnvWriteNoStaleBorrowTargets 0 pointerIfEnv (.deref (.var "p"))
      .int pointerIfWriteEnv := by
  intro written x slot mutable targets target hwrite hslot hcontains htarget
    hprefix
  have hwritten := pointerIf_write_effective_write_written hwrite
  subst written
  rw [pointerIfWriteEnv_eq] at hslot hcontains
  rcases hcontains with ⟨containsSlot, hcontainsSlot, hcontainsTy⟩
  have hcontainsSlotEq : containsSlot = slot :=
    Option.some.inj (hcontainsSlot.symm.trans hslot)
  subst containsSlot
  by_cases hp : x = "p"
  · subst hp
    have hslotTy : slot.ty = .ty (.borrow true [.var "x"]) := by
      simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hcontainsTy
    cases hcontainsTy with
    | here =>
        simp at htarget
        subst htarget
        cases hprefix with
        | direct hprefix =>
            simp [LVal.StrictPrefixOf, StrictPathPrefix, LVal.base,
              LVal.path] at hprefix
  · by_cases hx : x = "x"
    · subst hx
      have hslotTy : slot.ty = .ty .int := by
        simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hy : x = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · have hnone : pointerIfEnv.slotAt x = none := by
          simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update, Env.empty, hp, hx, hy]
        rw [hslot] at hnone
        cases hnone

theorem pointerWriteBranch_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      pointerWriteBranch .unit pointerIfWriteEnv := by
  unfold pointerWriteBranch
  exact TermTyping.assign
    (TermTyping.const ValueTyping.int)
    pointerIf_deref_p_typing
    ShapeCompatible.int
    WellFormedTy.int
    pointerIf_write_deref_p
    pointerIf_write_noStale
    pointerIf_write_ranked
    (Coherent.whenInitialized pointerIf_write_coherent)
    (EnvWriteRhsTargetsWellFormed.of_containedBorrowsWellFormed
      (by simpa [pointerIfWriteEnv_eq] using pointerIfEnv_contained))
    pointerIf_not_writeProhibited_deref_p

/-- Two borrow types strengthening into the same partial type can be merged:
the appended target list still strengthens into it.  This is the least-upper-
bound argument for the `p` slot of the branch join. -/
theorem partialTyStrengthens_borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal}
    {joined : PartialTy}
    (hleft : PartialTyStrengthens (.ty (.borrow mutable leftTargets)) joined)
    (hright : PartialTyStrengthens (.ty (.borrow mutable rightTargets)) joined) :
    PartialTyStrengthens (.ty (.borrow mutable (leftTargets ++ rightTargets)))
      joined := by
  cases hleft with
  | reflex =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hmem
        · exact hsubRight hmem) (by
        intro hleftNonempty happendEmpty
        exact hleftNonempty
          ((_root_.List.eq_nil_of_append_eq_nil happendEmpty).1))
  | borrow hsubLeft hleftNonempty =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem) (by
        intro htargetNonempty happendEmpty
        exact hleftNonempty htargetNonempty
          ((_root_.List.eq_nil_of_append_eq_nil happendEmpty).1))
  | intoUndef hinner =>
      rcases PartialTyStrengthens.from_borrow_inv hinner with
        ⟨targetTargets, htargetEq, hsubLeft⟩
      cases htargetEq
      have hsubRight : rightTargets ⊆ targetTargets := by
        cases hright with
        | intoUndef hinner' => exact PartialTyStrengthens.borrow_subset hinner'
      exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem) (by
        intro htargetNonempty happendEmpty
        exact (PartialTyStrengthens.borrow_nonempty hinner htargetNonempty)
          ((_root_.List.eq_nil_of_append_eq_nil happendEmpty).1)))

theorem pointerIfJoin_x_typing :
    LValTyping pointerIfJoinEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfJoinEnv "x" pointerIfXSlot (by
    simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot, pointerIfJoinPSlot,
      Env.update])

theorem pointerIfJoin_y_typing :
    LValTyping pointerIfJoinEnv (.var "y") (.ty .int) Lifetime.root := by
  exact @LValTyping.var pointerIfJoinEnv "y" pointerIfYSlot (by
    simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot, Env.update])

theorem pointerIfJoin_old_root_int : ∀ {lv partialTy lifetime},
    LVal.base lv ≠ "p" →
    LValTyping pointerIfJoinEnv lv partialTy lifetime →
    (lv = .var "x" ∨ lv = .var "y") ∧
      partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  exact pointerLike_old_root_int
    (env := pointerIfJoinEnv)
    (by simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
      pointerIfJoinPSlot, Env.update])
    (by simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot, Env.update])
    (by
      intro name hnameX hnameY hnameP
      simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot, pointerIfJoinPSlot,
        Env.update, Env.empty, hnameX, hnameY, hnameP])

theorem pointerIfJoin_no_targets_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping pointerIfJoinEnv [.var "y", .var "x"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htyping
  generalize hpartialTy :
      (PartialTy.ty (Ty.borrow mutable targets)) = partialTy at htyping
  cases htyping with
  | cons hhead _hrest hunion _hlifetime =>
      rcases pointerIfJoin_old_root_int (by simp [LVal.base]) hhead with
        ⟨_, hheadTy, _⟩
      injection hheadTy with hheadTy
      subst hheadTy
      have hupper : PartialTyStrengthens (.ty .int) partialTy :=
        hunion.1 (by simp)
      rw [← hpartialTy] at hupper
      cases PartialTyStrengthens.from_int_inv hupper

theorem pointerIfJoin_no_targets_box {inner lifetime} :
    ¬ LValTargetsTyping pointerIfJoinEnv [.var "y", .var "x"] (.box inner)
      lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.box inner) = partialTy at htyping
  cases htyping with
  | cons hhead _hrest hunion _hlifetime =>
      rcases pointerIfJoin_old_root_int (by simp [LVal.base]) hhead with
        ⟨_, hheadTy, _⟩
      injection hheadTy with hheadTy
      subst hheadTy
      have hupper : PartialTyStrengthens (.ty .int) partialTy :=
        hunion.1 (by simp)
      rw [← hpartialTy] at hupper
      cases hupper

theorem pointerIfJoin_no_targets_full_box {inner lifetime} :
    ¬ LValTargetsTyping pointerIfJoinEnv [.var "y", .var "x"]
      (.ty (.box inner)) lifetime := by
  intro htyping
  generalize hpartialTy : (PartialTy.ty (Ty.box inner)) = partialTy at htyping
  cases htyping with
  | cons hhead _hrest hunion _hlifetime =>
      rcases pointerIfJoin_old_root_int (by simp [LVal.base]) hhead with
        ⟨_, hheadTy, _⟩
      injection hheadTy with hheadTy
      subst hheadTy
      have hupper : PartialTyStrengthens (.ty .int) partialTy :=
        hunion.1 (by simp)
      rw [← hpartialTy] at hupper
      cases PartialTyStrengthens.from_int_inv hupper

theorem pointerIfJoin_p_root_facts : ∀ {lv},
    LVal.base lv = "p" →
    (∀ {inner lifetime},
      ¬ LValTyping pointerIfJoinEnv lv (.box inner) lifetime) ∧
    (∀ {mutable targets lifetime},
      LValTyping pointerIfJoinEnv lv
        (.ty (.borrow mutable targets)) lifetime →
      lv = .var "p" ∧ mutable = true ∧ targets = [.var "y", .var "x"] ∧
        lifetime = Lifetime.root) := by
  intro lv hbase
  have hfacts := pointerLike_p_root_facts_full
    (env := pointerIfJoinEnv) (pSlot := pointerIfJoinPSlot)
    (rootTargets := [.var "y", .var "x"])
    (by simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update])
    rfl rfl
    pointerIfJoin_no_targets_borrow
    pointerIfJoin_no_targets_box
    pointerIfJoin_no_targets_full_box
    hbase
  exact ⟨hfacts.1, hfacts.2.2⟩

theorem pointerIfJoin_coherent : Coherent pointerIfJoinEnv := by
  intro lv mutable targets borrowLifetime htyping
  by_cases hbase : LVal.base lv = "p"
  · rcases (pointerIfJoin_p_root_facts hbase).2 htyping with
      ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨.ty Ty.int, Lifetime.root,
      LValTargetsMaybeTyping.cons pointerIfJoin_y_typing
        (LValTargetsMaybeTyping.singleton pointerIfJoin_x_typing)
        (PartialTyUnion.self (.ty .int))
        (LifetimeIntersection.self Lifetime.root)⟩
  · rcases pointerIfJoin_old_root_int hbase htyping with ⟨_, hpartialTy, _⟩
    cases hpartialTy

theorem pointerIfJoin_contained :
    ContainedBorrowsWellFormed pointerIfJoinEnv := by
  intro root slot mutable targets hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hp : root = "p"
  · subst hp
    have hslotExpected :
        pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot := by
      simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update]
    have hslotEq : slot = pointerIfJoinPSlot :=
      Option.some.inj (hslot.symm.trans hslotExpected)
    subst slot
    have hcontainedTy :
        containedSlot.ty = .ty (.borrow true [.var "y", .var "x"]) := by
      simpa [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
          hcontainedSlot).symm
    rw [hcontainedTy] at hcontainsTy
    cases hcontainsTy with
    | here =>
        intro target htarget
        simp at htarget
        rcases htarget with rfl | rfl
        · exact ⟨.int, Lifetime.root, pointerIfJoin_y_typing,
            LifetimeOutlives.refl Lifetime.root,
            ⟨pointerIfYSlot, by
              simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
                Env.update, LVal.base],
              LifetimeOutlives.refl Lifetime.root⟩⟩
        · exact ⟨.int, Lifetime.root, pointerIfJoin_x_typing,
            LifetimeOutlives.refl Lifetime.root,
            ⟨pointerIfXSlot, by
              simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
                pointerIfJoinPSlot, Env.update, LVal.base],
              LifetimeOutlives.refl Lifetime.root⟩⟩
  · by_cases hy : root = "y"
    · subst hy
      have hcontainedTy : containedSlot.ty = .ty .int := by
        simpa [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
            hcontainedSlot).symm
      rw [hcontainedTy] at hcontainsTy
      cases hcontainsTy
    · by_cases hx : root = "x"
      · subst hx
        have hcontainedTy : containedSlot.ty = .ty .int := by
          simpa [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
            pointerIfJoinPSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hcontainedSlot).symm
        rw [hcontainedTy] at hcontainsTy
        cases hcontainsTy
      · have hnone : pointerIfJoinEnv.slotAt root = none := by
          simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]
        rw [hslot] at hnone
        cases hnone

theorem pointerIfJoin_linearizable : Linearizable pointerIfJoinEnv := by
  refine ⟨fun name => if name = "p" then 1 else 0, ?_⟩
  intro root slot hslot v hv
  by_cases hp : root = "p"
  · subst hp
    have hslotTy : slot.ty = .ty (.borrow true [.var "y", .var "x"]) := by
      simpa [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hv
    simp [PartialTy.vars, Ty.vars, LVal.base] at hv
    rcases hv with rfl | rfl <;> simp
  · by_cases hy : root = "y"
    · subst hy
      have hslotTy : slot.ty = .ty .int := by
        simpa [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · by_cases hx : root = "x"
      · subst hx
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
            pointerIfJoinPSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars] at hv
      · have hnone : pointerIfJoinEnv.slotAt root = none := by
          simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]
        rw [hslot] at hnone
        cases hnone

theorem pointerIfJoin_borrowSafe : BorrowSafeEnv pointerIfJoinEnv := by
  have hroot : ∀ root mutable targets,
      (pointerIfJoinEnv ⊢ root ↝ (Ty.borrow mutable targets)) →
      root = "p" := by
    intro root mutable targets hcontains
    rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
    by_cases hp : root = "p"
    · exact hp
    · exfalso
      by_cases hy : root = "y"
      · subst hy
        have hslotTy : slot.ty = .ty .int := by
          simpa [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hcontainsTy
        cases hcontainsTy
      · by_cases hx : root = "x"
        · subst hx
          have hslotTy : slot.ty = .ty .int := by
            simpa [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
              pointerIfJoinPSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                hslot).symm
          rw [hslotTy] at hcontainsTy
          cases hcontainsTy
        · have hnone : pointerIfJoinEnv.slotAt root = none := by
            simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]
          rw [hslot] at hnone
          cases hnone
  intro x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable hcontainsOther _htargetMutable _htargetOther _hconflict
  rw [hroot x true targetsMutable hcontainsMutable,
    hroot y mutable targetsOther hcontainsOther]

theorem pointerIfRetarget_le_join :
    EnvStrengthens pointerIfRetargetEnv pointerIfJoinEnv := by
  intro name
  by_cases hp : name = "p"
  · subst hp
    rw [show pointerIfRetargetEnv.slotAt "p" = some pointerIfPYSlot by
        simp [pointerIfRetargetEnv, pointerIfPYSlot, Env.update],
      show pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot by
        simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update]]
    have hsub : List.Subset [LVal.var "y"] [LVal.var "y", LVal.var "x"] := by
      intro target htarget
      simp at htarget
      subst htarget
      simp
    exact ⟨rfl, PartialTyStrengthens.borrow hsub (by
      intro _ hnil
      simp at hnil)⟩
  · by_cases hy : name = "y"
    · subst hy
      rw [show pointerIfRetargetEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
            pointerIfPYSlot, Env.update],
        show pointerIfJoinEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
            Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hx : name = "x"
      · subst hx
        rw [show pointerIfRetargetEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
              pointerIfYSlot, pointerIfPYSlot, Env.update],
          show pointerIfJoinEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
              pointerIfJoinPSlot, Env.update]]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · rw [show pointerIfRetargetEnv.slotAt name = none by
            simp [pointerIfRetargetEnv, pointerIfEnv, Env.update, Env.empty,
              hp, hy, hx],
          show pointerIfJoinEnv.slotAt name = none by
            simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]]
        trivial

theorem pointerIfWrite_le_join :
    EnvStrengthens pointerIfWriteEnv pointerIfJoinEnv := by
  rw [pointerIfWriteEnv_eq]
  intro name
  by_cases hp : name = "p"
  · subst hp
    rw [show pointerIfEnv.slotAt "p" = some pointerIfPXSlot by
        simp [pointerIfEnv, pointerIfPXSlot, Env.update],
      show pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot by
        simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update]]
    have hsub : List.Subset [LVal.var "x"] [LVal.var "y", LVal.var "x"] := by
      intro target htarget
      simp at htarget
      subst htarget
      simp
    exact ⟨rfl, PartialTyStrengthens.borrow hsub (by
      intro _ hnil
      simp at hnil)⟩
  · by_cases hy : name = "y"
    · subst hy
      rw [show pointerIfEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update],
        show pointerIfJoinEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
            Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hx : name = "x"
      · subst hx
        rw [show pointerIfEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfEnv, pointerIfXSlot, pointerIfYSlot,
              pointerIfPXSlot, Env.update],
          show pointerIfJoinEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
              pointerIfJoinPSlot, Env.update]]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · rw [show pointerIfEnv.slotAt name = none by
            simp [pointerIfEnv, Env.update, Env.empty, hp, hy, hx],
          show pointerIfJoinEnv.slotAt name = none by
            simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]]
        trivial

theorem pointerIfJoin_least {env' : Env}
    (hret : EnvStrengthens pointerIfRetargetEnv env')
    (hwrite : EnvStrengthens pointerIfWriteEnv env') :
    EnvStrengthens pointerIfJoinEnv env' := by
  rw [pointerIfWriteEnv_eq] at hwrite
  intro name
  by_cases hp : name = "p"
  · subst hp
    rcases EnvStrengthens.slot_forward hret (show
        pointerIfRetargetEnv.slotAt "p" = some pointerIfPYSlot by
          simp [pointerIfRetargetEnv, pointerIfPYSlot, Env.update]) with
      ⟨slotY, hslotY, hlife, hstrY⟩
    rcases EnvStrengthens.slot_forward hwrite (show
        pointerIfEnv.slotAt "p" = some pointerIfPXSlot by
          simp [pointerIfEnv, pointerIfPXSlot, Env.update]) with
      ⟨slotX, hslotX, _hlifeX, hstrX⟩
    have hslotEq : slotX = slotY := Option.some.inj (hslotX.symm.trans hslotY)
    subst hslotEq
    rw [show pointerIfJoinEnv.slotAt "p" = some pointerIfJoinPSlot by
        simp [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update], hslotX]
    have hY : PartialTyStrengthens (.ty (.borrow true [.var "y"])) slotX.ty :=
      hstrY
    have hX : PartialTyStrengthens (.ty (.borrow true [.var "x"])) slotX.ty :=
      hstrX
    have hYX : PartialTyStrengthens
        (.ty (.borrow true ([.var "y"] ++ [.var "x"]))) slotX.ty :=
      partialTyStrengthens_borrow_append hY hX
    exact ⟨hlife, by simpa [pointerIfJoinPSlot] using hYX⟩
  · by_cases hy : name = "y"
    · subst hy
      rcases EnvStrengthens.slot_forward hret (show
          pointerIfRetargetEnv.slotAt "y" = some pointerIfYSlot by
            simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
              pointerIfPYSlot, Env.update]) with
        ⟨slot', hslot', hlife, hstr⟩
      rw [show pointerIfJoinEnv.slotAt "y" = some pointerIfYSlot by
          simp [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
            Env.update], hslot']
      exact ⟨hlife, hstr⟩
    · by_cases hx : name = "x"
      · subst hx
        rcases EnvStrengthens.slot_forward hret (show
            pointerIfRetargetEnv.slotAt "x" = some pointerIfXSlot by
              simp [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
                pointerIfYSlot, pointerIfPYSlot, Env.update]) with
          ⟨slot', hslot', hlife, hstr⟩
        rw [show pointerIfJoinEnv.slotAt "x" = some pointerIfXSlot by
            simp [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
              pointerIfJoinPSlot, Env.update], hslot']
        exact ⟨hlife, hstr⟩
      · have hretNone : pointerIfRetargetEnv.slotAt name = none := by
          simp [pointerIfRetargetEnv, pointerIfEnv, Env.update, Env.empty,
            hp, hy, hx]
        have hjoinNone : pointerIfJoinEnv.slotAt name = none := by
          simp [pointerIfJoinEnv, Env.update, Env.empty, hp, hy, hx]
        have h := hret name
        rw [hretNone] at h
        rw [hjoinNone]
        cases henvSlot : env'.slotAt name with
        | none =>
            trivial
        | some envSlot =>
            rw [henvSlot] at h
            cases h

theorem pointerIf_envJoin :
    EnvJoin pointerIfRetargetEnv pointerIfWriteEnv pointerIfJoinEnv := by
  constructor
  · intro env henv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at henv
    rcases henv with rfl | rfl
    · exact pointerIfRetarget_le_join
    · exact pointerIfWrite_le_join
  · intro env' henv'
    exact pointerIfJoin_least
      (henv' pointerIfRetargetEnv (by simp))
      (henv' pointerIfWriteEnv (by simp))

theorem pointerIfRetarget_join_sameShape :
    EnvJoinSameShape pointerIfRetargetEnv pointerIfJoinEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  by_cases hp : name = "p"
  · subst hp
    have hbranchTy : branchSlot.ty = .ty (.borrow true [.var "y"]) := by
      simpa [pointerIfRetargetEnv, pointerIfPYSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
    have hjoinTy : joinSlot.ty = .ty (.borrow true [.var "y", .var "x"]) := by
      simpa [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
    simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
  · by_cases hy : name = "y"
    · subst hy
      have hbranchTy : branchSlot.ty = .ty .int := by
        simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfYSlot,
          pointerIfPYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
      have hjoinTy : joinSlot.ty = .ty .int := by
        simpa [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
      simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
    · by_cases hx : name = "x"
      · subst hx
        have hbranchTy : branchSlot.ty = .ty .int := by
          simpa [pointerIfRetargetEnv, pointerIfEnv, pointerIfXSlot,
            pointerIfYSlot, pointerIfPYSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hbranch).symm
        have hjoinTy : joinSlot.ty = .ty .int := by
          simpa [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
            pointerIfJoinPSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hjoin).symm
        simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
      · have hnone : pointerIfRetargetEnv.slotAt name = none := by
          simp [pointerIfRetargetEnv, pointerIfEnv, Env.update, Env.empty,
            hp, hy, hx]
        rw [hbranch] at hnone
        cases hnone

theorem pointerIfWrite_join_sameShape :
    EnvJoinSameShape pointerIfWriteEnv pointerIfJoinEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  rw [pointerIfWriteEnv_eq] at hbranch
  by_cases hp : name = "p"
  · subst hp
    have hbranchTy : branchSlot.ty = .ty (.borrow true [.var "x"]) := by
      simpa [pointerIfEnv, pointerIfPXSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
    have hjoinTy : joinSlot.ty = .ty (.borrow true [.var "y", .var "x"]) := by
      simpa [pointerIfJoinEnv, pointerIfJoinPSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
    simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
  · by_cases hy : name = "y"
    · subst hy
      have hbranchTy : branchSlot.ty = .ty .int := by
        simpa [pointerIfEnv, pointerIfYSlot, pointerIfPXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
      have hjoinTy : joinSlot.ty = .ty .int := by
        simpa [pointerIfJoinEnv, pointerIfYSlot, pointerIfJoinPSlot,
          Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
      simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
    · by_cases hx : name = "x"
      · subst hx
        have hbranchTy : branchSlot.ty = .ty .int := by
          simpa [pointerIfEnv, pointerIfXSlot, pointerIfYSlot, pointerIfPXSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hbranch).symm
        have hjoinTy : joinSlot.ty = .ty .int := by
          simpa [pointerIfJoinEnv, pointerIfXSlot, pointerIfYSlot,
            pointerIfJoinPSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
              hjoin).symm
        simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
      · have hnone : pointerIfEnv.slotAt name = none := by
          simp [pointerIfEnv, Env.update, Env.empty, hp, hy, hx]
        rw [hbranch] at hnone
        cases hnone

theorem ifPointerAssignment_join_obligations :
    EnvJoin pointerIfRetargetEnv pointerIfWriteEnv pointerIfJoinEnv ∧
    EnvJoinSameShape pointerIfRetargetEnv pointerIfJoinEnv ∧
    EnvJoinSameShape pointerIfWriteEnv pointerIfJoinEnv ∧
    ContainedBorrowsWellFormed pointerIfJoinEnv ∧
    Coherent pointerIfJoinEnv ∧
    Linearizable pointerIfJoinEnv ∧
    BorrowSafeEnv pointerIfJoinEnv :=
  ⟨pointerIf_envJoin, pointerIfRetarget_join_sameShape,
    pointerIfWrite_join_sameShape, pointerIfJoin_contained,
    pointerIfJoin_coherent, pointerIfJoin_linearizable,
    pointerIfJoin_borrowSafe⟩

theorem ifPointerAssignment_typing :
    TermTyping pointerIfEnv StoreTyping.empty Lifetime.root
      ifPointerAssignment .unit pointerIfJoinEnv := by
  unfold ifPointerAssignment
  exact TermTyping.ite
    pointerIfCondition_typing
    pointerRetargetBranch_typing
    pointerWriteBranch_typing
    (PartialTyJoin.self (.ty .unit))
    ifPointerAssignment_join_obligations.1

/-! ### Checked relaxed-`T-If` retargeting example -/

theorem retargetAfterIfEnv5_contains_inv {x mutable targets} :
    retargetAfterIfEnv5 ⊢ x ↝ (.borrow mutable targets) →
    x = "a" ∧ mutable = true ∧ targets = [.var "c"] :=
  oneBorrowSlot_contains_inv
    (env := retargetAfterIfEnv5) (aSlot := retargetAfterIfACSlot)
    (slotTargets := [.var "c"])
    (by simp [retargetAfterIfEnv5, retargetAfterIfACSlot, Env.update])
    (by simp [retargetAfterIfACSlot])
    (by
      intro x slot ha hslot
      exact retargetAfterIfEnv4_scalar_slot (by
        simpa [retargetAfterIfEnv5, Env.update, ha] using hslot))

theorem retargetAfterIfEnv5_d_typing :
    LValTyping retargetAfterIfEnv5 (.var "d") (.ty .int) Lifetime.root := by
  exact @LValTyping.var retargetAfterIfEnv5 "d" retargetAfterIfIntSlot (by
    simp [retargetAfterIfEnv5, retargetAfterIfEnv4, retargetAfterIfEnv3,
      retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
      retargetAfterIfIntSlot, retargetAfterIfBoolSlot, retargetAfterIfACSlot,
      Env.update])

theorem retargetAfterIfEnv5_e_typing :
    LValTyping retargetAfterIfEnv5 (.var "e") (.ty .int) Lifetime.root := by
  exact @LValTyping.var retargetAfterIfEnv5 "e" retargetAfterIfIntSlot (by
    simp [retargetAfterIfEnv5, retargetAfterIfEnv4, retargetAfterIfEnv3,
      retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
      retargetAfterIfIntSlot, retargetAfterIfBoolSlot, retargetAfterIfACSlot,
      Env.update])

theorem retargetAfterIfEnv5_sth_typing :
    LValTyping retargetAfterIfEnv5 (.var "sth") (.ty .bool)
      Lifetime.root := by
  exact @LValTyping.var retargetAfterIfEnv5 "sth" retargetAfterIfBoolSlot (by
    simp [retargetAfterIfEnv5, retargetAfterIfEnv4, retargetAfterIfEnv3,
      retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
      retargetAfterIfIntSlot, retargetAfterIfBoolSlot, retargetAfterIfACSlot,
      Env.update])

theorem retargetAfterIfEnv5_a_typing :
    LValTyping retargetAfterIfEnv5 (.var "a")
      (.ty (.borrow true [.var "c"])) Lifetime.root := by
  exact @LValTyping.var retargetAfterIfEnv5 "a" retargetAfterIfACSlot (by
    simp [retargetAfterIfEnv5, retargetAfterIfACSlot, Env.update])

theorem retargetAfterIfEnv5_not_readProhibited_sth :
    ¬ ReadProhibited retargetAfterIfEnv5 (.var "sth") := by
  exact not_readProhibited_of_oneBorrowSlot_disjoint
    retargetAfterIfEnv5_contains_inv
    (by
      intro target htarget
      simp at htarget
      subst htarget
      simp [LVal.base])

theorem retargetAfterIfCondition_typing :
    TermTyping retargetAfterIfEnv5 StoreTyping.empty Lifetime.root
      (.copy (.var "sth")) .bool retargetAfterIfEnv5 :=
  TermTyping.copy retargetAfterIfEnv5_sth_typing CopyTy.bool
    retargetAfterIfEnv5_not_readProhibited_sth

theorem retargetAfterIfEnv5_not_writeProhibited_d :
    ¬ WriteProhibited retargetAfterIfEnv5 (.var "d") := by
  exact not_writeProhibited_of_oneBorrowSlot_disjoint
    retargetAfterIfEnv5_contains_inv
    (by
      intro target htarget
      simp at htarget
      subst htarget
      simp [LVal.base])

theorem retargetAfterIfEnv5_not_writeProhibited_e :
    ¬ WriteProhibited retargetAfterIfEnv5 (.var "e") := by
  exact not_writeProhibited_of_oneBorrowSlot_disjoint
    retargetAfterIfEnv5_contains_inv
    (by
      intro target htarget
      simp at htarget
      subst htarget
      simp [LVal.base])

theorem retargetAfterIfEnv5_d_mutable :
    Mutable retargetAfterIfEnv5 (.var "d") :=
  @Mutable.var retargetAfterIfEnv5 "d" retargetAfterIfIntSlot (by
    simp [retargetAfterIfEnv5, retargetAfterIfEnv4, retargetAfterIfEnv3,
      retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
      retargetAfterIfIntSlot, retargetAfterIfBoolSlot, retargetAfterIfACSlot,
      Env.update])

theorem retargetAfterIfEnv5_e_mutable :
    Mutable retargetAfterIfEnv5 (.var "e") :=
  @Mutable.var retargetAfterIfEnv5 "e" retargetAfterIfIntSlot (by
    simp [retargetAfterIfEnv5, retargetAfterIfEnv4, retargetAfterIfEnv3,
      retargetAfterIfEnv2, retargetAfterIfEnv1, retargetAfterIfEnv0,
      retargetAfterIfIntSlot, retargetAfterIfBoolSlot, retargetAfterIfACSlot,
      Env.update])

theorem retargetAfterIf_shape_ac_ad :
    ShapeCompatible retargetAfterIfEnv5
      (.ty (.borrow true [.var "c"])) (.ty (.borrow true [.var "d"])) := by
  exact ShapeCompatible.borrow
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, retargetAfterIfEnv5_c_typing⟩)
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, retargetAfterIfEnv5_d_typing⟩)
    ShapeCompatible.int

theorem retargetAfterIf_shape_ac_ae :
    ShapeCompatible retargetAfterIfEnv5
      (.ty (.borrow true [.var "c"])) (.ty (.borrow true [.var "e"])) := by
  exact ShapeCompatible.borrow
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, retargetAfterIfEnv5_c_typing⟩)
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, retargetAfterIfEnv5_e_typing⟩)
    ShapeCompatible.int

theorem retargetAfterIf_borrow_d_wellFormed :
    WellFormedTy retargetAfterIfEnv5 (.borrow true [.var "d"])
      Lifetime.root := by
  exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
    intro target htarget
    simp at htarget
    subst htarget
    exact ⟨.int, Lifetime.root, retargetAfterIfEnv5_d_typing,
      LifetimeOutlives.refl Lifetime.root,
      ⟨retargetAfterIfIntSlot, by
        simp [retargetAfterIfEnv5, retargetAfterIfEnv4,
          retargetAfterIfEnv3, retargetAfterIfEnv2, retargetAfterIfEnv1,
          retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfACSlot, Env.update,
          LVal.base],
        LifetimeOutlives.refl Lifetime.root⟩⟩))

theorem retargetAfterIf_borrow_e_wellFormed :
    WellFormedTy retargetAfterIfEnv5 (.borrow true [.var "e"])
      Lifetime.root := by
  exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
    intro target htarget
    simp at htarget
    subst htarget
    exact ⟨.int, Lifetime.root, retargetAfterIfEnv5_e_typing,
      LifetimeOutlives.refl Lifetime.root,
      ⟨retargetAfterIfIntSlot, by
        simp [retargetAfterIfEnv5, retargetAfterIfEnv4,
          retargetAfterIfEnv3, retargetAfterIfEnv2, retargetAfterIfEnv1,
          retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfACSlot, Env.update,
          LVal.base],
        LifetimeOutlives.refl Lifetime.root⟩⟩))

theorem retargetAfterIf_write_a_d :
    EnvWrite 0 retargetAfterIfEnv5 (.var "a") (.borrow true [.var "d"])
      retargetAfterIfTrueEnv := by
  simpa [retargetAfterIfTrueEnv, retargetAfterIfADSlot,
      retargetAfterIfACSlot, LVal.base] using
    (@EnvWrite.intro 0 retargetAfterIfEnv5 retargetAfterIfEnv5 (.var "a")
      retargetAfterIfACSlot (.borrow true [.var "d"])
      (.ty (.borrow true [.var "d"]))
      (by
        show retargetAfterIfEnv5.slotAt "a" = some retargetAfterIfACSlot
        simp [retargetAfterIfEnv5, retargetAfterIfACSlot, Env.update])
      UpdateAtPath.strong)

theorem retargetAfterIf_write_a_e :
    EnvWrite 0 retargetAfterIfEnv5 (.var "a") (.borrow true [.var "e"])
      retargetAfterIfFalseEnv := by
  simpa [retargetAfterIfFalseEnv, retargetAfterIfAESlot,
      retargetAfterIfACSlot, LVal.base] using
    (@EnvWrite.intro 0 retargetAfterIfEnv5 retargetAfterIfEnv5 (.var "a")
      retargetAfterIfACSlot (.borrow true [.var "e"])
      (.ty (.borrow true [.var "e"]))
      (by
        show retargetAfterIfEnv5.slotAt "a" = some retargetAfterIfACSlot
        simp [retargetAfterIfEnv5, retargetAfterIfACSlot, Env.update])
      UpdateAtPath.strong)

theorem retargetAfterIf_write_a_d_effective {result : Env} {written : LVal} :
    EnvWriteEffectiveWrite 0 retargetAfterIfEnv5 (.var "a")
      (.borrow true [.var "d"]) result written →
    written = .var "a" := by
  intro hwrite
  cases hwrite with
  | intro _hslot hupdate =>
      cases hupdate with
      | strong => rfl

theorem retargetAfterIf_write_a_e_effective {result : Env} {written : LVal} :
    EnvWriteEffectiveWrite 0 retargetAfterIfEnv5 (.var "a")
      (.borrow true [.var "e"]) result written →
    written = .var "a" := by
  intro hwrite
  cases hwrite with
  | intro _hslot hupdate =>
      cases hupdate with
      | strong => rfl

theorem retargetAfterIfTrue_rest_scalar {x : Name} {slot : EnvSlot} :
    x ≠ "a" → retargetAfterIfTrueEnv.slotAt x = some slot →
    slot.ty = .ty .int ∨ slot.ty = .ty .bool := by
  intro ha hslot
  exact retargetAfterIfEnv4_scalar_slot (by
    simpa [retargetAfterIfTrueEnv, retargetAfterIfEnv5, Env.update, ha] using
      hslot)

theorem retargetAfterIfTrue_d_typing :
    LValTyping retargetAfterIfTrueEnv (.var "d") (.ty .int)
      Lifetime.root := by
  exact @LValTyping.var retargetAfterIfTrueEnv "d" retargetAfterIfIntSlot (by
    simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5, retargetAfterIfEnv4,
      retargetAfterIfEnv3, retargetAfterIfEnv2, retargetAfterIfEnv1,
      retargetAfterIfEnv0, retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
      retargetAfterIfADSlot, Env.update])

theorem retargetAfterIfTrue_targets_d_no_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping retargetAfterIfTrueEnv [.var "d"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      rcases LValTyping.var_inv htarget with ⟨slot, hslot, hty, _hl⟩
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
          retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hty
      cases hty
  | cons _hhead hrest _hunion _hintersection =>
      cases hrest

theorem retargetAfterIfTrue_borrow_lval_inv :
    ∀ (lv : LVal) {mutable targets lifetime},
      LValTyping retargetAfterIfTrueEnv lv (.ty (.borrow mutable targets))
        lifetime →
      lv = .var "a" ∧ mutable = true ∧ targets = [.var "d"] ∧
        lifetime = Lifetime.root :=
  oneBorrowSlot_borrow_lval_inv
    (env := retargetAfterIfTrueEnv) (aSlot := retargetAfterIfADSlot)
    (slotTargets := [.var "d"])
    (by simp [retargetAfterIfTrueEnv, retargetAfterIfADSlot, Env.update])
    (by simp [retargetAfterIfADSlot])
    (by simp [retargetAfterIfADSlot])
    retargetAfterIfTrue_rest_scalar
    retargetAfterIfTrue_targets_d_no_borrow

theorem retargetAfterIfTrue_contains_inv {x mutable targets} :
    retargetAfterIfTrueEnv ⊢ x ↝ (.borrow mutable targets) →
    x = "a" ∧ mutable = true ∧ targets = [.var "d"] :=
  oneBorrowSlot_contains_inv
    (env := retargetAfterIfTrueEnv) (aSlot := retargetAfterIfADSlot)
    (slotTargets := [.var "d"])
    (by simp [retargetAfterIfTrueEnv, retargetAfterIfADSlot, Env.update])
    (by simp [retargetAfterIfADSlot])
    retargetAfterIfTrue_rest_scalar

theorem retargetAfterIfTrue_coherent : Coherent retargetAfterIfTrueEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases retargetAfterIfTrue_borrow_lval_inv lv htyping with
    ⟨hlv, hmutable, htargets, _hl⟩
  subst hlv
  subst hmutable
  subst htargets
  exact ⟨.ty Ty.int, Lifetime.root,
    LValTargetsMaybeTyping.singleton retargetAfterIfTrue_d_typing⟩

theorem retargetAfterIfTrue_contained :
    ContainedBorrowsWellFormed retargetAfterIfTrueEnv := by
  intro x slot mutable targets hslot hcontains
  rcases retargetAfterIfTrue_contains_inv hcontains with ⟨rfl, rfl, rfl⟩
  have hslotEq : slot = retargetAfterIfADSlot := by
    have hslotExpected :
        retargetAfterIfTrueEnv.slotAt "a" = some retargetAfterIfADSlot := by
      simp [retargetAfterIfTrueEnv, retargetAfterIfADSlot, Env.update]
    exact Option.some.inj (hslot.symm.trans hslotExpected)
  subst slot
  intro target htarget
  simp at htarget
  subst htarget
  exact ⟨.int, Lifetime.root, retargetAfterIfTrue_d_typing,
    LifetimeOutlives.refl Lifetime.root,
    ⟨retargetAfterIfIntSlot, by
      simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
        retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
        retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
        retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update,
        LVal.base],
      LifetimeOutlives.refl Lifetime.root⟩⟩

theorem retargetAfterIfTrue_not_writeProhibited_a :
    ¬ WriteProhibited retargetAfterIfTrueEnv (.var "a") := by
  exact not_writeProhibited_of_oneBorrowSlot_disjoint
    retargetAfterIfTrue_contains_inv
    (by
      intro target htarget
      simp at htarget
      subst htarget
      simp [LVal.base])

theorem retargetAfterIfFalse_rest_scalar {x : Name} {slot : EnvSlot} :
    x ≠ "a" → retargetAfterIfFalseEnv.slotAt x = some slot →
    slot.ty = .ty .int ∨ slot.ty = .ty .bool := by
  intro ha hslot
  exact retargetAfterIfEnv4_scalar_slot (by
    simpa [retargetAfterIfFalseEnv, retargetAfterIfEnv5, Env.update, ha] using
      hslot)

theorem retargetAfterIfFalse_e_typing :
    LValTyping retargetAfterIfFalseEnv (.var "e") (.ty .int)
      Lifetime.root := by
  exact @LValTyping.var retargetAfterIfFalseEnv "e" retargetAfterIfIntSlot (by
    simp [retargetAfterIfFalseEnv, retargetAfterIfEnv5, retargetAfterIfEnv4,
      retargetAfterIfEnv3, retargetAfterIfEnv2, retargetAfterIfEnv1,
      retargetAfterIfEnv0, retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
      retargetAfterIfAESlot, Env.update])

theorem retargetAfterIfFalse_targets_e_no_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping retargetAfterIfFalseEnv [.var "e"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      rcases LValTyping.var_inv htarget with ⟨slot, hslot, hty, _hl⟩
      have hslotTy : slot.ty = .ty .int := by
        simpa [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
          retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hty
      cases hty
  | cons _hhead hrest _hunion _hintersection =>
      cases hrest

theorem retargetAfterIfFalse_borrow_lval_inv :
    ∀ (lv : LVal) {mutable targets lifetime},
      LValTyping retargetAfterIfFalseEnv lv (.ty (.borrow mutable targets))
        lifetime →
      lv = .var "a" ∧ mutable = true ∧ targets = [.var "e"] ∧
        lifetime = Lifetime.root :=
  oneBorrowSlot_borrow_lval_inv
    (env := retargetAfterIfFalseEnv) (aSlot := retargetAfterIfAESlot)
    (slotTargets := [.var "e"])
    (by simp [retargetAfterIfFalseEnv, retargetAfterIfAESlot, Env.update])
    (by simp [retargetAfterIfAESlot])
    (by simp [retargetAfterIfAESlot])
    retargetAfterIfFalse_rest_scalar
    retargetAfterIfFalse_targets_e_no_borrow

theorem retargetAfterIfFalse_contains_inv {x mutable targets} :
    retargetAfterIfFalseEnv ⊢ x ↝ (.borrow mutable targets) →
    x = "a" ∧ mutable = true ∧ targets = [.var "e"] :=
  oneBorrowSlot_contains_inv
    (env := retargetAfterIfFalseEnv) (aSlot := retargetAfterIfAESlot)
    (slotTargets := [.var "e"])
    (by simp [retargetAfterIfFalseEnv, retargetAfterIfAESlot, Env.update])
    (by simp [retargetAfterIfAESlot])
    retargetAfterIfFalse_rest_scalar

theorem retargetAfterIfFalse_coherent : Coherent retargetAfterIfFalseEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases retargetAfterIfFalse_borrow_lval_inv lv htyping with
    ⟨hlv, hmutable, htargets, _hl⟩
  subst hlv
  subst hmutable
  subst htargets
  exact ⟨.ty Ty.int, Lifetime.root,
    LValTargetsMaybeTyping.singleton retargetAfterIfFalse_e_typing⟩

theorem retargetAfterIfFalse_contained :
    ContainedBorrowsWellFormed retargetAfterIfFalseEnv := by
  intro x slot mutable targets hslot hcontains
  rcases retargetAfterIfFalse_contains_inv hcontains with ⟨rfl, rfl, rfl⟩
  have hslotEq : slot = retargetAfterIfAESlot := by
    have hslotExpected :
        retargetAfterIfFalseEnv.slotAt "a" = some retargetAfterIfAESlot := by
      simp [retargetAfterIfFalseEnv, retargetAfterIfAESlot, Env.update]
    exact Option.some.inj (hslot.symm.trans hslotExpected)
  subst slot
  intro target htarget
  simp at htarget
  subst htarget
  exact ⟨.int, Lifetime.root, retargetAfterIfFalse_e_typing,
    LifetimeOutlives.refl Lifetime.root,
    ⟨retargetAfterIfIntSlot, by
      simp [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
        retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
        retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
        retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update,
        LVal.base],
      LifetimeOutlives.refl Lifetime.root⟩⟩

theorem retargetAfterIfFalse_not_writeProhibited_a :
    ¬ WriteProhibited retargetAfterIfFalseEnv (.var "a") := by
  exact not_writeProhibited_of_oneBorrowSlot_disjoint
    retargetAfterIfFalse_contains_inv
    (by
      intro target htarget
      simp at htarget
      subst htarget
      simp [LVal.base])

theorem retargetAfterIf_retarget_d_noStale :
    EnvWriteNoStaleBorrowTargets 0 retargetAfterIfEnv5 (.var "a")
      (.borrow true [.var "d"]) retargetAfterIfTrueEnv := by
  intro written x slot mutable targets target hwrite hslot hcontains htarget
    hmayRead
  have hwritten := retargetAfterIf_write_a_d_effective hwrite
  subst written
  rcases retargetAfterIfTrue_contains_inv hcontains with ⟨rfl, rfl, rfl⟩
  simp at htarget
  subst htarget
  cases hmayRead with
  | direct hprefix =>
      simp [LVal.StrictPrefixOf, StrictPathPrefix, LVal.base, LVal.path] at hprefix

theorem retargetAfterIf_retarget_e_noStale :
    EnvWriteNoStaleBorrowTargets 0 retargetAfterIfEnv5 (.var "a")
      (.borrow true [.var "e"]) retargetAfterIfFalseEnv := by
  intro written x slot mutable targets target hwrite hslot hcontains htarget
    hmayRead
  have hwritten := retargetAfterIf_write_a_e_effective hwrite
  subst written
  rcases retargetAfterIfFalse_contains_inv hcontains with ⟨rfl, rfl, rfl⟩
  simp at htarget
  subst htarget
  cases hmayRead with
  | direct hprefix =>
      simp [LVal.StrictPrefixOf, StrictPathPrefix, LVal.base, LVal.path] at hprefix

theorem retargetAfterIf_retarget_d_ranked :
    ∃ φ, LinearizedBy φ retargetAfterIfEnv5 ∧
      EnvWriteRhsBorrowTargetsBelow φ retargetAfterIfTrueEnv
        (.borrow true [.var "d"]) := by
  let φ : Name → Nat := fun name => if name = "a" then 1 else 0
  refine ⟨φ, ?linearized, ?below⟩
  · intro root slot hslot v hv
    by_cases ha : root = "a"
    · subst ha
      have hslotTy : slot.ty = .ty (.borrow true [.var "c"]) := by
        simpa [retargetAfterIfEnv5, retargetAfterIfACSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
      subst v
      simp [φ, LVal.base]
    · rcases retargetAfterIfEnv4_scalar_slot (by
          simpa [retargetAfterIfEnv5, Env.update, ha] using hslot) with
        hslotTy | hslotTy <;> rw [hslotTy] at hv <;>
        simp [PartialTy.vars, Ty.vars] at hv
  · intro root slot mutable targets target hslot hcontains htarget hrhs
    rcases hrhs with ⟨_rhsMutable, _rhsTargets, hrhsContains,
      hrhsTarget⟩
    cases hrhsContains with
    | here =>
        rcases retargetAfterIfTrue_contains_inv
            ⟨slot, hslot, hcontains⟩ with
          ⟨hroot, hmutable, htargets⟩
        subst hroot
        subst hmutable
        subst htargets
        simp at htarget hrhsTarget
        subst htarget
        simp [φ, LVal.base]

theorem retargetAfterIf_retarget_e_ranked :
    ∃ φ, LinearizedBy φ retargetAfterIfEnv5 ∧
      EnvWriteRhsBorrowTargetsBelow φ retargetAfterIfFalseEnv
        (.borrow true [.var "e"]) := by
  let φ : Name → Nat := fun name => if name = "a" then 1 else 0
  refine ⟨φ, ?linearized, ?below⟩
  · intro root slot hslot v hv
    by_cases ha : root = "a"
    · subst ha
      have hslotTy : slot.ty = .ty (.borrow true [.var "c"]) := by
        simpa [retargetAfterIfEnv5, retargetAfterIfACSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
      subst v
      simp [φ, LVal.base]
    · rcases retargetAfterIfEnv4_scalar_slot (by
          simpa [retargetAfterIfEnv5, Env.update, ha] using hslot) with
        hslotTy | hslotTy <;> rw [hslotTy] at hv <;>
        simp [PartialTy.vars, Ty.vars] at hv
  · intro root slot mutable targets target hslot hcontains htarget hrhs
    rcases hrhs with ⟨_rhsMutable, _rhsTargets, hrhsContains,
      hrhsTarget⟩
    cases hrhsContains with
    | here =>
        rcases retargetAfterIfFalse_contains_inv
            ⟨slot, hslot, hcontains⟩ with
          ⟨hroot, hmutable, htargets⟩
        subst hroot
        subst hmutable
        subst htargets
        simp at htarget hrhsTarget
        subst htarget
        simp [φ, LVal.base]

theorem retargetAfterIf_trueBranch_typing :
    TermTyping retargetAfterIfEnv5 StoreTyping.empty Lifetime.root
      (.assign (.var "a") (.borrow true (.var "d"))) .unit
      retargetAfterIfTrueEnv := by
  exact TermTyping.assign
    (TermTyping.mutBorrow retargetAfterIfEnv5_d_typing
      retargetAfterIfEnv5_d_mutable
      retargetAfterIfEnv5_not_writeProhibited_d)
    retargetAfterIfEnv5_a_typing
    retargetAfterIf_shape_ac_ad
    retargetAfterIf_borrow_d_wellFormed
    retargetAfterIf_write_a_d
    retargetAfterIf_retarget_d_noStale
    retargetAfterIf_retarget_d_ranked
    (Coherent.whenInitialized retargetAfterIfTrue_coherent)
    (EnvWriteRhsTargetsWellFormed.of_containedBorrowsWellFormed
      retargetAfterIfTrue_contained)
    retargetAfterIfTrue_not_writeProhibited_a

theorem retargetAfterIf_falseBranch_typing :
    TermTyping retargetAfterIfEnv5 StoreTyping.empty Lifetime.root
      (.assign (.var "a") (.borrow true (.var "e"))) .unit
      retargetAfterIfFalseEnv := by
  exact TermTyping.assign
    (TermTyping.mutBorrow retargetAfterIfEnv5_e_typing
      retargetAfterIfEnv5_e_mutable
      retargetAfterIfEnv5_not_writeProhibited_e)
    retargetAfterIfEnv5_a_typing
    retargetAfterIf_shape_ac_ae
    retargetAfterIf_borrow_e_wellFormed
    retargetAfterIf_write_a_e
    retargetAfterIf_retarget_e_noStale
    retargetAfterIf_retarget_e_ranked
    (Coherent.whenInitialized retargetAfterIfFalse_coherent)
    (EnvWriteRhsTargetsWellFormed.of_containedBorrowsWellFormed
      retargetAfterIfFalse_contained)
    retargetAfterIfFalse_not_writeProhibited_a

theorem retargetAfterIfJoin_rest_scalar {x : Name} {slot : EnvSlot} :
    x ≠ "a" → retargetAfterIfJoinEnv.slotAt x = some slot →
    slot.ty = .ty .int ∨ slot.ty = .ty .bool := by
  intro ha hslot
  exact retargetAfterIfEnv4_scalar_slot (by
    simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5, Env.update, ha] using
      hslot)

theorem retargetAfterIfJoin_d_typing :
    LValTyping retargetAfterIfJoinEnv (.var "d") (.ty .int)
      Lifetime.root := by
  exact @LValTyping.var retargetAfterIfJoinEnv "d" retargetAfterIfIntSlot (by
    simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5, retargetAfterIfEnv4,
      retargetAfterIfEnv3, retargetAfterIfEnv2, retargetAfterIfEnv1,
      retargetAfterIfEnv0, retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
      retargetAfterIfAJoinSlot, Env.update])

theorem retargetAfterIfJoin_e_typing :
    LValTyping retargetAfterIfJoinEnv (.var "e") (.ty .int)
      Lifetime.root := by
  exact @LValTyping.var retargetAfterIfJoinEnv "e" retargetAfterIfIntSlot (by
    simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5, retargetAfterIfEnv4,
      retargetAfterIfEnv3, retargetAfterIfEnv2, retargetAfterIfEnv1,
      retargetAfterIfEnv0, retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
      retargetAfterIfAJoinSlot, Env.update])

theorem retargetAfterIfJoin_a_typing :
    LValTyping retargetAfterIfJoinEnv (.var "a")
      (.ty (.borrow true [.var "d", .var "e"])) Lifetime.root := by
  exact @LValTyping.var retargetAfterIfJoinEnv "a" retargetAfterIfAJoinSlot (by
    simp [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update])

theorem retargetAfterIfJoin_targets_de_no_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping retargetAfterIfJoinEnv [.var "d", .var "e"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  cases htargets with
  | cons hhead hrest hunion _hintersection =>
      rcases LValTyping.var_inv hhead with ⟨slotD, hslotD, htyD, _⟩
      have hslotDTy : slotD.ty = .ty .int := by
        simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
          retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslotD).symm
      rw [hslotDTy] at htyD
      cases htyD
      cases hrest with
      | singleton htail =>
          rcases LValTyping.var_inv htail with ⟨slotE, hslotE, htyE, _⟩
          have hslotETy : slotE.ty = .ty .int := by
            simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslotE).symm
          rw [hslotETy] at htyE
          cases htyE
          have hleft := PartialTyUnion.left_strengthens hunion
          cases hleft
      | cons _hhead2 hrest2 _hunion2 _hintersection2 =>
          cases hrest2

theorem retargetAfterIfJoin_borrow_lval_inv :
    ∀ (lv : LVal) {mutable targets lifetime},
      LValTyping retargetAfterIfJoinEnv lv (.ty (.borrow mutable targets))
        lifetime →
      lv = .var "a" ∧ mutable = true ∧ targets = [.var "d", .var "e"] ∧
        lifetime = Lifetime.root :=
  oneBorrowSlot_borrow_lval_inv
    (env := retargetAfterIfJoinEnv) (aSlot := retargetAfterIfAJoinSlot)
    (slotTargets := [.var "d", .var "e"])
    (by simp [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update])
    (by simp [retargetAfterIfAJoinSlot])
    (by simp [retargetAfterIfAJoinSlot])
    retargetAfterIfJoin_rest_scalar
    retargetAfterIfJoin_targets_de_no_borrow

theorem retargetAfterIfJoin_contains_inv {x mutable targets} :
    retargetAfterIfJoinEnv ⊢ x ↝ (.borrow mutable targets) →
    x = "a" ∧ mutable = true ∧ targets = [.var "d", .var "e"] :=
  oneBorrowSlot_contains_inv
    (env := retargetAfterIfJoinEnv) (aSlot := retargetAfterIfAJoinSlot)
    (slotTargets := [.var "d", .var "e"])
    (by simp [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update])
    (by simp [retargetAfterIfAJoinSlot])
    retargetAfterIfJoin_rest_scalar

theorem retargetAfterIfJoin_coherent : Coherent retargetAfterIfJoinEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases retargetAfterIfJoin_borrow_lval_inv lv htyping with
    ⟨hlv, hmutable, htargets, _hl⟩
  subst hlv
  subst hmutable
  subst htargets
  exact ⟨.ty Ty.int, Lifetime.root,
    LValTargetsMaybeTyping.cons retargetAfterIfJoin_d_typing
      (LValTargetsMaybeTyping.singleton retargetAfterIfJoin_e_typing)
      (PartialTyUnion.self (.ty .int))
      (LifetimeIntersection.self Lifetime.root)⟩

theorem retargetAfterIfJoin_contained :
    ContainedBorrowsWellFormed retargetAfterIfJoinEnv := by
  intro x slot mutable targets hslot hcontains
  rcases retargetAfterIfJoin_contains_inv hcontains with ⟨rfl, rfl, rfl⟩
  have hslotEq : slot = retargetAfterIfAJoinSlot := by
    have hslotExpected :
        retargetAfterIfJoinEnv.slotAt "a" = some retargetAfterIfAJoinSlot := by
      simp [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update]
    exact Option.some.inj (hslot.symm.trans hslotExpected)
  subst slot
  intro target htarget
  simp at htarget
  rcases htarget with rfl | rfl
  · exact ⟨.int, Lifetime.root, retargetAfterIfJoin_d_typing,
      LifetimeOutlives.refl Lifetime.root,
      ⟨retargetAfterIfIntSlot, by
        simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
          retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update,
          LVal.base],
        LifetimeOutlives.refl Lifetime.root⟩⟩
  · exact ⟨.int, Lifetime.root, retargetAfterIfJoin_e_typing,
      LifetimeOutlives.refl Lifetime.root,
      ⟨retargetAfterIfIntSlot, by
        simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
          retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update,
          LVal.base],
        LifetimeOutlives.refl Lifetime.root⟩⟩

theorem retargetAfterIfJoin_linearizable : Linearizable retargetAfterIfJoinEnv := by
  refine ⟨fun name => if name = "a" then 1 else 0, ?_⟩
  intro root slot hslot v hv
  by_cases ha : root = "a"
  · subst ha
    have hslotTy : slot.ty = .ty (.borrow true [.var "d", .var "e"]) := by
      simpa [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hv
    simp [PartialTy.vars, Ty.vars, LVal.base] at hv
    rcases hv with rfl | rfl <;> simp
  · rcases retargetAfterIfJoin_rest_scalar ha hslot with hslotTy | hslotTy <;>
      rw [hslotTy] at hv <;> simp [PartialTy.vars, Ty.vars] at hv

theorem retargetAfterIfTrue_le_join :
    EnvStrengthens retargetAfterIfTrueEnv retargetAfterIfJoinEnv := by
  intro name
  by_cases ha : name = "a"
  · subst ha
    rw [show retargetAfterIfTrueEnv.slotAt "a" =
          some retargetAfterIfADSlot by
        simp [retargetAfterIfTrueEnv, retargetAfterIfADSlot, Env.update],
      show retargetAfterIfJoinEnv.slotAt "a" =
          some retargetAfterIfAJoinSlot by
        simp [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update]]
    have hsub : List.Subset [LVal.var "d"] [LVal.var "d", LVal.var "e"] := by
      intro target htarget
      simp at htarget
      subst htarget
      simp
    exact ⟨rfl, PartialTyStrengthens.borrow hsub (by
      intro _ hnil
      simp at hnil)⟩
  · by_cases hsth : name = "sth"
    · subst hsth
      rw [show retargetAfterIfTrueEnv.slotAt "sth" =
            some retargetAfterIfBoolSlot by
          simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update],
        show retargetAfterIfJoinEnv.slotAt "sth" =
            some retargetAfterIfBoolSlot by
          simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases he : name = "e"
      · subst he
        rw [show retargetAfterIfTrueEnv.slotAt "e" =
              some retargetAfterIfIntSlot by
            simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update],
          show retargetAfterIfJoinEnv.slotAt "e" =
              some retargetAfterIfIntSlot by
            simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update]]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · by_cases hd : name = "d"
        · subst hd
          rw [show retargetAfterIfTrueEnv.slotAt "d" =
                some retargetAfterIfIntSlot by
              simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update],
            show retargetAfterIfJoinEnv.slotAt "d" =
                some retargetAfterIfIntSlot by
              simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update]]
          exact ⟨rfl, PartialTyStrengthens.reflex⟩
        · by_cases hc : name = "c"
          · subst hc
            rw [show retargetAfterIfTrueEnv.slotAt "c" =
                  some retargetAfterIfIntSlot by
                simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                  retargetAfterIfEnv1, retargetAfterIfEnv0,
                  retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                  retargetAfterIfADSlot, Env.update],
              show retargetAfterIfJoinEnv.slotAt "c" =
                  some retargetAfterIfIntSlot by
                simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                  retargetAfterIfEnv1, retargetAfterIfEnv0,
                  retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                  retargetAfterIfAJoinSlot, Env.update]]
            exact ⟨rfl, PartialTyStrengthens.reflex⟩
          · rw [show retargetAfterIfTrueEnv.slotAt name = none by
                simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                  retargetAfterIfEnv1, retargetAfterIfEnv0,
                  retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                  retargetAfterIfADSlot, Env.update, Env.empty, ha, hsth, he,
                  hd, hc],
              show retargetAfterIfJoinEnv.slotAt name = none by
                simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                  retargetAfterIfEnv1, retargetAfterIfEnv0,
                  retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                  retargetAfterIfAJoinSlot, Env.update, Env.empty, ha, hsth,
                  he, hd, hc]]
            trivial

theorem retargetAfterIfFalse_le_join :
    EnvStrengthens retargetAfterIfFalseEnv retargetAfterIfJoinEnv := by
  intro name
  by_cases ha : name = "a"
  · subst ha
    rw [show retargetAfterIfFalseEnv.slotAt "a" =
          some retargetAfterIfAESlot by
        simp [retargetAfterIfFalseEnv, retargetAfterIfAESlot, Env.update],
      show retargetAfterIfJoinEnv.slotAt "a" =
          some retargetAfterIfAJoinSlot by
        simp [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update]]
    have hsub : List.Subset [LVal.var "e"] [LVal.var "d", LVal.var "e"] := by
      intro target htarget
      simp at htarget
      subst htarget
      simp
    exact ⟨rfl, PartialTyStrengthens.borrow hsub (by
      intro _ hnil
      simp at hnil)⟩
  · by_cases hsth : name = "sth"
    · subst hsth
      rw [show retargetAfterIfFalseEnv.slotAt "sth" =
            some retargetAfterIfBoolSlot by
          simp [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update],
        show retargetAfterIfJoinEnv.slotAt "sth" =
            some retargetAfterIfBoolSlot by
          simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases he : name = "e"
      · subst he
        rw [show retargetAfterIfFalseEnv.slotAt "e" =
              some retargetAfterIfIntSlot by
            simp [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update],
          show retargetAfterIfJoinEnv.slotAt "e" =
              some retargetAfterIfIntSlot by
            simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update]]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · by_cases hd : name = "d"
        · subst hd
          rw [show retargetAfterIfFalseEnv.slotAt "d" =
                some retargetAfterIfIntSlot by
              simp [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update],
            show retargetAfterIfJoinEnv.slotAt "d" =
                some retargetAfterIfIntSlot by
              simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update]]
          exact ⟨rfl, PartialTyStrengthens.reflex⟩
        · by_cases hc : name = "c"
          · subst hc
            rw [show retargetAfterIfFalseEnv.slotAt "c" =
                  some retargetAfterIfIntSlot by
                simp [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                  retargetAfterIfEnv1, retargetAfterIfEnv0,
                  retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                  retargetAfterIfAESlot, Env.update],
              show retargetAfterIfJoinEnv.slotAt "c" =
                  some retargetAfterIfIntSlot by
                simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                  retargetAfterIfEnv1, retargetAfterIfEnv0,
                  retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                  retargetAfterIfAJoinSlot, Env.update]]
            exact ⟨rfl, PartialTyStrengthens.reflex⟩
          · rw [show retargetAfterIfFalseEnv.slotAt name = none by
                simp [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                  retargetAfterIfEnv1, retargetAfterIfEnv0,
                  retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                  retargetAfterIfAESlot, Env.update, Env.empty, ha, hsth, he,
                  hd, hc],
              show retargetAfterIfJoinEnv.slotAt name = none by
                simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                  retargetAfterIfEnv1, retargetAfterIfEnv0,
                  retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                  retargetAfterIfAJoinSlot, Env.update, Env.empty, ha, hsth,
                  he, hd, hc]]
            trivial

theorem retargetAfterIfJoin_least {env' : Env}
    (htrue : EnvStrengthens retargetAfterIfTrueEnv env')
    (hfalse : EnvStrengthens retargetAfterIfFalseEnv env') :
    EnvStrengthens retargetAfterIfJoinEnv env' := by
  intro name
  by_cases ha : name = "a"
  · subst ha
    rcases EnvStrengthens.slot_forward htrue (show
        retargetAfterIfTrueEnv.slotAt "a" = some retargetAfterIfADSlot by
          simp [retargetAfterIfTrueEnv, retargetAfterIfADSlot, Env.update]) with
      ⟨slotD, hslotD, hlifeD, hstrD⟩
    rcases EnvStrengthens.slot_forward hfalse (show
        retargetAfterIfFalseEnv.slotAt "a" = some retargetAfterIfAESlot by
          simp [retargetAfterIfFalseEnv, retargetAfterIfAESlot, Env.update]) with
      ⟨slotE, hslotE, _hlifeE, hstrE⟩
    have hslotEq : slotE = slotD := Option.some.inj (hslotE.symm.trans hslotD)
    subst hslotEq
    rw [show retargetAfterIfJoinEnv.slotAt "a" =
          some retargetAfterIfAJoinSlot by
        simp [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update],
      hslotE]
    have hD : PartialTyStrengthens (.ty (.borrow true [.var "d"])) slotE.ty :=
      hstrD
    have hE : PartialTyStrengthens (.ty (.borrow true [.var "e"])) slotE.ty :=
      hstrE
    have hDE : PartialTyStrengthens
        (.ty (.borrow true ([.var "d"] ++ [.var "e"]))) slotE.ty :=
      partialTyStrengthens_borrow_append hD hE
    exact ⟨hlifeD, by simpa [retargetAfterIfAJoinSlot] using hDE⟩
  · by_cases hsth : name = "sth"
    · subst hsth
      rcases EnvStrengthens.slot_forward htrue (show
          retargetAfterIfTrueEnv.slotAt "sth" =
            some retargetAfterIfBoolSlot by
            simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0,
              retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
              retargetAfterIfADSlot, Env.update]) with
        ⟨slot', hslot', hlife, hstr⟩
      rw [show retargetAfterIfJoinEnv.slotAt "sth" =
            some retargetAfterIfBoolSlot by
          simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update],
        hslot']
      exact ⟨hlife, hstr⟩
    · by_cases he : name = "e"
      · subst he
        rcases EnvStrengthens.slot_forward htrue (show
            retargetAfterIfTrueEnv.slotAt "e" =
              some retargetAfterIfIntSlot by
              simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0,
                retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                retargetAfterIfADSlot, Env.update]) with
          ⟨slot', hslot', hlife, hstr⟩
        rw [show retargetAfterIfJoinEnv.slotAt "e" =
              some retargetAfterIfIntSlot by
            simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0,
              retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
              retargetAfterIfAJoinSlot, Env.update],
          hslot']
        exact ⟨hlife, hstr⟩
      · by_cases hd : name = "d"
        · subst hd
          rcases EnvStrengthens.slot_forward htrue (show
              retargetAfterIfTrueEnv.slotAt "d" =
                some retargetAfterIfIntSlot by
                simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3,
                  retargetAfterIfEnv2, retargetAfterIfEnv1,
                  retargetAfterIfEnv0, retargetAfterIfIntSlot,
                  retargetAfterIfBoolSlot, retargetAfterIfADSlot,
                  Env.update]) with
            ⟨slot', hslot', hlife, hstr⟩
          rw [show retargetAfterIfJoinEnv.slotAt "d" =
                some retargetAfterIfIntSlot by
              simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0,
                retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                retargetAfterIfAJoinSlot, Env.update],
            hslot']
          exact ⟨hlife, hstr⟩
        · by_cases hc : name = "c"
          · subst hc
            rcases EnvStrengthens.slot_forward htrue (show
                retargetAfterIfTrueEnv.slotAt "c" =
                  some retargetAfterIfIntSlot by
                  simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
                    retargetAfterIfEnv4, retargetAfterIfEnv3,
                    retargetAfterIfEnv2, retargetAfterIfEnv1,
                    retargetAfterIfEnv0, retargetAfterIfIntSlot,
                    retargetAfterIfBoolSlot, retargetAfterIfADSlot,
                    Env.update]) with
              ⟨slot', hslot', hlife, hstr⟩
            rw [show retargetAfterIfJoinEnv.slotAt "c" =
                  some retargetAfterIfIntSlot by
                simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                  retargetAfterIfEnv4, retargetAfterIfEnv3,
                  retargetAfterIfEnv2, retargetAfterIfEnv1,
                  retargetAfterIfEnv0, retargetAfterIfIntSlot,
                  retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot,
                  Env.update],
              hslot']
            exact ⟨hlife, hstr⟩
          · have htrueNone : retargetAfterIfTrueEnv.slotAt name = none := by
              simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0,
                retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                retargetAfterIfADSlot, Env.update, Env.empty, ha, hsth, he,
                hd, hc]
            have hjoinNone : retargetAfterIfJoinEnv.slotAt name = none := by
              simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0,
                retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
                retargetAfterIfAJoinSlot, Env.update, Env.empty, ha, hsth, he,
                hd, hc]
            have h := htrue name
            rw [htrueNone] at h
            rw [hjoinNone]
            cases henvSlot : env'.slotAt name with
            | none => trivial
            | some envSlot =>
                rw [henvSlot] at h
                cases h

theorem retargetAfterIf_envJoin :
    EnvJoin retargetAfterIfTrueEnv retargetAfterIfFalseEnv
      retargetAfterIfJoinEnv := by
  constructor
  · intro env henv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at henv
    rcases henv with rfl | rfl
    · exact retargetAfterIfTrue_le_join
    · exact retargetAfterIfFalse_le_join
  · intro env' henv'
    exact retargetAfterIfJoin_least
      (henv' retargetAfterIfTrueEnv (by simp))
      (henv' retargetAfterIfFalseEnv (by simp))

theorem retargetAfterIfTrue_join_sameShape :
    EnvJoinSameShape retargetAfterIfTrueEnv retargetAfterIfJoinEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  by_cases ha : name = "a"
  · subst ha
    have hbranchTy : branchSlot.ty = .ty (.borrow true [.var "d"]) := by
      simpa [retargetAfterIfTrueEnv, retargetAfterIfADSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
    have hjoinTy :
        joinSlot.ty = .ty (.borrow true [.var "d", .var "e"]) := by
      simpa [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
    simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
  · by_cases hsth : name = "sth"
    · subst hsth
      have hbranchTy : branchSlot.ty = .ty .bool := by
        simpa [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
          retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
      have hjoinTy : joinSlot.ty = .ty .bool := by
        simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
          retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
      simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
    · by_cases he : name = "e"
      · subst he
        have hbranchTy : branchSlot.ty = .ty .int := by
          simpa [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
        have hjoinTy : joinSlot.ty = .ty .int := by
          simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
        simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
      · by_cases hd : name = "d"
        · subst hd
          have hbranchTy : branchSlot.ty = .ty .int := by
            simpa [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
          have hjoinTy : joinSlot.ty = .ty .int := by
            simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
          simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
        · by_cases hc : name = "c"
          · subst hc
            have hbranchTy : branchSlot.ty = .ty .int := by
              simpa [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
            have hjoinTy : joinSlot.ty = .ty .int := by
              simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
            simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
          · have hnone : retargetAfterIfTrueEnv.slotAt name = none := by
              simp [retargetAfterIfTrueEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfADSlot, Env.update,
                Env.empty, ha, hsth, he, hd, hc]
            rw [hbranch] at hnone
            cases hnone

theorem retargetAfterIfFalse_join_sameShape :
    EnvJoinSameShape retargetAfterIfFalseEnv retargetAfterIfJoinEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  by_cases ha : name = "a"
  · subst ha
    have hbranchTy : branchSlot.ty = .ty (.borrow true [.var "e"]) := by
      simpa [retargetAfterIfFalseEnv, retargetAfterIfAESlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
    have hjoinTy :
        joinSlot.ty = .ty (.borrow true [.var "d", .var "e"]) := by
      simpa [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
    simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
  · by_cases hsth : name = "sth"
    · subst hsth
      have hbranchTy : branchSlot.ty = .ty .bool := by
        simpa [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
          retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
      have hjoinTy : joinSlot.ty = .ty .bool := by
        simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
          retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
          retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
          retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
      simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
    · by_cases he : name = "e"
      · subst he
        have hbranchTy : branchSlot.ty = .ty .int := by
          simpa [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
        have hjoinTy : joinSlot.ty = .ty .int := by
          simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
        simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
      · by_cases hd : name = "d"
        · subst hd
          have hbranchTy : branchSlot.ty = .ty .int := by
            simpa [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
          have hjoinTy : joinSlot.ty = .ty .int := by
            simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
              retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
              retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
              retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
              (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
          simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
        · by_cases hc : name = "c"
          · subst hc
            have hbranchTy : branchSlot.ty = .ty .int := by
              simpa [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
            have hjoinTy : joinSlot.ty = .ty .int := by
              simpa [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update] using
                (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
            simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
          · have hnone : retargetAfterIfFalseEnv.slotAt name = none := by
              simp [retargetAfterIfFalseEnv, retargetAfterIfEnv5,
                retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
                retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
                retargetAfterIfBoolSlot, retargetAfterIfAESlot, Env.update,
                Env.empty, ha, hsth, he, hd, hc]
            rw [hbranch] at hnone
            cases hnone

theorem retargetAfterIf_if_typing :
    TermTyping retargetAfterIfEnv5 StoreTyping.empty Lifetime.root
      (.ite (.copy (.var "sth"))
        (.assign (.var "a") (.borrow true (.var "d")))
        (.assign (.var "a") (.borrow true (.var "e"))))
      .unit retargetAfterIfJoinEnv := by
  exact TermTyping.ite
    retargetAfterIfCondition_typing
    retargetAfterIf_trueBranch_typing
    retargetAfterIf_falseBranch_typing
    (PartialTyJoin.self (.ty .unit))
    retargetAfterIf_envJoin

theorem retargetAfterIfJoin_deref_a_typing :
    LValTyping retargetAfterIfJoinEnv (.deref (.var "a")) (.ty .int)
      Lifetime.root := by
  exact LValTyping.borrow retargetAfterIfJoin_a_typing
    (LValTargetsTyping.cons retargetAfterIfJoin_d_typing
      (LValTargetsTyping.singleton retargetAfterIfJoin_e_typing)
      (PartialTyUnion.self (.ty .int))
      (LifetimeIntersection.self Lifetime.root))

theorem retargetAfterIfJoin_not_writeProhibited_deref_a :
    ¬ WriteProhibited retargetAfterIfJoinEnv (.deref (.var "a")) := by
  exact not_writeProhibited_of_oneBorrowSlot_disjoint
    retargetAfterIfJoin_contains_inv
    (by
      intro target htarget
      simp at htarget
      rcases htarget with rfl | rfl <;> simp [LVal.base])

theorem retargetAfterIfJoin_update_d_eq :
    retargetAfterIfJoinEnv.update "d" retargetAfterIfIntSlot =
      retargetAfterIfJoinEnv := by
  apply env_ext_local
  intro name
  by_cases ha : name = "a" <;> by_cases hsth : name = "sth" <;>
    by_cases he : name = "e" <;> by_cases hd : name = "d" <;>
    by_cases hc : name = "c" <;>
    simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5, retargetAfterIfEnv4,
      retargetAfterIfEnv3, retargetAfterIfEnv2, retargetAfterIfEnv1,
      retargetAfterIfEnv0, retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
      retargetAfterIfAJoinSlot, Env.update, Env.empty, ha, hsth, he, hd, hc]

theorem retargetAfterIfJoin_update_e_eq :
    retargetAfterIfJoinEnv.update "e" retargetAfterIfIntSlot =
      retargetAfterIfJoinEnv := by
  apply env_ext_local
  intro name
  by_cases ha : name = "a" <;> by_cases hsth : name = "sth" <;>
    by_cases he : name = "e" <;> by_cases hd : name = "d" <;>
    by_cases hc : name = "c" <;>
    simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5, retargetAfterIfEnv4,
      retargetAfterIfEnv3, retargetAfterIfEnv2, retargetAfterIfEnv1,
      retargetAfterIfEnv0, retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
      retargetAfterIfAJoinSlot, Env.update, Env.empty, ha, hsth, he, hd, hc]

theorem retargetAfterIfJoin_update_a_eq :
    retargetAfterIfJoinEnv.update "a" retargetAfterIfAJoinSlot =
      retargetAfterIfJoinEnv := by
  apply env_ext_local
  intro name
  by_cases ha : name = "a" <;> by_cases hsth : name = "sth" <;>
    by_cases he : name = "e" <;> by_cases hd : name = "d" <;>
    by_cases hc : name = "c" <;>
    simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5, retargetAfterIfEnv4,
      retargetAfterIfEnv3, retargetAfterIfEnv2, retargetAfterIfEnv1,
      retargetAfterIfEnv0, retargetAfterIfIntSlot, retargetAfterIfBoolSlot,
      retargetAfterIfAJoinSlot, Env.update, Env.empty, ha, hsth, he, hd, hc]

theorem retargetAfterIf_write_d :
    EnvWrite 1 retargetAfterIfJoinEnv (.var "d") .int
      retargetAfterIfJoinEnv := by
  have hwrite : EnvWrite 1 retargetAfterIfJoinEnv (.var "d") .int
      (retargetAfterIfJoinEnv.update "d" retargetAfterIfIntSlot) := by
    simpa [retargetAfterIfIntSlot, LVal.base] using
      (@EnvWrite.intro 1 retargetAfterIfJoinEnv retargetAfterIfJoinEnv
        (.var "d") retargetAfterIfIntSlot .int (.ty .int)
        (by
          show retargetAfterIfJoinEnv.slotAt "d" =
            some retargetAfterIfIntSlot
          simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update])
        (UpdateAtPath.weak ShapeCompatible.int
          (PartialTyJoin.self (.ty .int))))
  simpa [retargetAfterIfJoin_update_d_eq] using hwrite

theorem retargetAfterIf_write_e :
    EnvWrite 1 retargetAfterIfJoinEnv (.var "e") .int
      retargetAfterIfJoinEnv := by
  have hwrite : EnvWrite 1 retargetAfterIfJoinEnv (.var "e") .int
      (retargetAfterIfJoinEnv.update "e" retargetAfterIfIntSlot) := by
    simpa [retargetAfterIfIntSlot, LVal.base] using
      (@EnvWrite.intro 1 retargetAfterIfJoinEnv retargetAfterIfJoinEnv
        (.var "e") retargetAfterIfIntSlot .int (.ty .int)
        (by
          show retargetAfterIfJoinEnv.slotAt "e" =
            some retargetAfterIfIntSlot
          simp [retargetAfterIfJoinEnv, retargetAfterIfEnv5,
            retargetAfterIfEnv4, retargetAfterIfEnv3, retargetAfterIfEnv2,
            retargetAfterIfEnv1, retargetAfterIfEnv0, retargetAfterIfIntSlot,
            retargetAfterIfBoolSlot, retargetAfterIfAJoinSlot, Env.update])
        (UpdateAtPath.weak ShapeCompatible.int
          (PartialTyJoin.self (.ty .int))))
  simpa [retargetAfterIfJoin_update_e_eq] using hwrite

theorem retargetAfterIfJoin_envJoin_self :
    EnvJoin retargetAfterIfJoinEnv retargetAfterIfJoinEnv
      retargetAfterIfJoinEnv := by
  simp [EnvJoin]

theorem retargetAfterIf_write_deref_a :
    EnvWrite 0 retargetAfterIfJoinEnv (.deref (.var "a")) .int
      retargetAfterIfJoinEnv := by
  have htargets : WriteBorrowTargets 1 retargetAfterIfJoinEnv []
      [.var "d", .var "e"] .int retargetAfterIfJoinEnv := by
    exact WriteBorrowTargets.cons retargetAfterIf_write_d
      ⟨.int, Lifetime.root, retargetAfterIfJoin_d_typing⟩
      (WriteBorrowTargets.singleton retargetAfterIf_write_e
        ⟨.int, Lifetime.root, retargetAfterIfJoin_e_typing⟩)
      retargetAfterIfJoin_envJoin_self
  have hwrite : EnvWrite 0 retargetAfterIfJoinEnv (.deref (.var "a")) .int
      (retargetAfterIfJoinEnv.update "a" retargetAfterIfAJoinSlot) := by
    simpa [retargetAfterIfAJoinSlot, LVal.base, LVal.path] using
      (@EnvWrite.intro 0 retargetAfterIfJoinEnv retargetAfterIfJoinEnv
        (.deref (.var "a")) retargetAfterIfAJoinSlot .int
        (.ty (.borrow true [.var "d", .var "e"]))
        (by
          show retargetAfterIfJoinEnv.slotAt "a" =
            some retargetAfterIfAJoinSlot
          simp [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update])
        (@UpdateAtPath.mutBorrow retargetAfterIfJoinEnv
          retargetAfterIfJoinEnv 0 [] [.var "d", .var "e"] .int htargets))
  simpa [retargetAfterIfJoin_update_a_eq] using hwrite

theorem retargetAfterIf_write_deref_a_effective {result : Env}
    {written : LVal} :
    EnvWriteEffectiveWrite 0 retargetAfterIfJoinEnv (.deref (.var "a"))
      .int result written →
    written = .var "d" ∨ written = .var "e" := by
  intro hwrite
  cases hwrite with
  | @intro _rank _env₁ _env₂ _lv _written sourceSlot _ty _updatedTy
      hslot hupdate =>
      have hslotEq : sourceSlot = retargetAfterIfAJoinSlot := by
        simpa [retargetAfterIfJoinEnv, retargetAfterIfAJoinSlot, Env.update,
          LVal.base] using hslot.symm
      subst sourceSlot
      cases hupdate with
      | mutBorrow htargets =>
          cases htargets with
          | consHead htargetWrite _hrest _hjoin =>
              cases htargetWrite with
              | intro _htargetSlot htargetUpdate =>
                  cases htargetUpdate with
                  | weak _hshape _hjoin => exact Or.inl rfl
          | consTail _htargetWrite hrest _hjoin =>
              cases hrest with
              | singleton htargetWrite =>
                  cases htargetWrite with
                  | intro _htargetSlot htargetUpdate =>
                      cases htargetUpdate with
                      | weak _hshape _hjoin => exact Or.inr rfl
              | consHead htargetWrite _hrest _hjoin =>
                  cases htargetWrite with
                  | intro _htargetSlot htargetUpdate =>
                      cases htargetUpdate with
                      | weak _hshape _hjoin => exact Or.inr rfl
              | consTail _htargetWrite hrest _hjoin =>
                  cases hrest

theorem retargetAfterIf_write_deref_a_noStale :
    EnvWriteNoStaleBorrowTargets 0 retargetAfterIfJoinEnv
      (.deref (.var "a")) .int retargetAfterIfJoinEnv := by
  intro written x slot mutable targets target hwrite hslot hcontains htarget
    hmayRead
  rcases retargetAfterIf_write_deref_a_effective hwrite with
    hwritten | hwritten
  · subst hwritten
    rcases retargetAfterIfJoin_contains_inv hcontains with ⟨rfl, rfl, rfl⟩
    simp at htarget
    rcases htarget with rfl | rfl
    · cases hmayRead with
      | direct hprefix =>
          simp [LVal.StrictPrefixOf, StrictPathPrefix, LVal.base, LVal.path] at hprefix
    · cases hmayRead with
      | direct hprefix =>
          simp [LVal.StrictPrefixOf, StrictPathPrefix, LVal.base, LVal.path] at hprefix
  · subst hwritten
    rcases retargetAfterIfJoin_contains_inv hcontains with ⟨rfl, rfl, rfl⟩
    simp at htarget
    rcases htarget with rfl | rfl
    · cases hmayRead with
      | direct hprefix =>
          simp [LVal.StrictPrefixOf, StrictPathPrefix, LVal.base, LVal.path] at hprefix
    · cases hmayRead with
      | direct hprefix =>
          simp [LVal.StrictPrefixOf, StrictPathPrefix, LVal.base, LVal.path] at hprefix

theorem retargetAfterIf_write_int_ranked :
    ∃ φ, LinearizedBy φ retargetAfterIfJoinEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ retargetAfterIfJoinEnv .int := by
  rcases retargetAfterIfJoin_linearizable with ⟨φ, hlinearized⟩
  refine ⟨φ, hlinearized, ?_⟩
  intro _root _slot _mutable _targets _target _hslot _hcontains _htarget
    hrhs
  rcases hrhs with ⟨_rhsMutable, _rhsTargets, hrhsContains, _hrhsTarget⟩
  cases hrhsContains

theorem retargetAfterIf_final_write_typing :
    TermTyping retargetAfterIfJoinEnv StoreTyping.empty Lifetime.root
      (.assign (.deref (.var "a")) (.val (.int 0))) .unit
      retargetAfterIfJoinEnv := by
  exact TermTyping.assign
    (TermTyping.const ValueTyping.int)
    retargetAfterIfJoin_deref_a_typing
    ShapeCompatible.int
    WellFormedTy.int
    retargetAfterIf_write_deref_a
    retargetAfterIf_write_deref_a_noStale
    retargetAfterIf_write_int_ranked
    (Coherent.whenInitialized retargetAfterIfJoin_coherent)
    (EnvWriteRhsTargetsWellFormed.of_containedBorrowsWellFormed
      retargetAfterIfJoin_contained)
    retargetAfterIfJoin_not_writeProhibited_deref_a

theorem retargetAfterIf_terms_typing :
    TermListTyping retargetAfterIfEnv0 StoreTyping.empty Lifetime.root
      retargetAfterIfTerms .unit retargetAfterIfJoinEnv := by
  unfold retargetAfterIfTerms
  exact TermListTyping.cons retargetAfterIf_declare_c_typing
    (TermListTyping.cons retargetAfterIf_declare_d_typing
      (TermListTyping.cons retargetAfterIf_declare_e_typing
        (TermListTyping.cons retargetAfterIf_declare_sth_typing
          (TermListTyping.cons retargetAfterIf_declare_a_typing
            (TermListTyping.cons retargetAfterIf_if_typing
              (TermListTyping.singleton
                retargetAfterIf_final_write_typing))))))

end Paper
end FWRust.Conditional
