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

/-- A borrow contained in the finer (source) type of a shape-preserving
strengthening is also contained in the coarser (result) type, with a *superset*
of targets.  This is the structural core of "preserve writeProhibited":
strengthening only grows borrow target lists (W-Bor), and `sameShape` rules out
the contained borrow being struck to `undef`. -/
theorem partialTyContains_borrow_transport_strengthens
    {sourceTy resultTy : PartialTy} {mutable : Bool} {targets : List LVal} :
    PartialTyContains sourceTy (.borrow mutable targets) →
    PartialTyStrengthens sourceTy resultTy →
    PartialTy.sameShape sourceTy resultTy →
    ∃ targets',
      PartialTyContains resultTy (.borrow mutable targets') ∧
        targets.Subset targets' := by
  intro hcontains hstrength
  induction hstrength with
  | @reflex ty =>
      intro _hshape
      exact ⟨targets, hcontains, fun _ h => h⟩
  | @box left right _hsub ih =>
      intro hshape
      cases hcontains with
      | box hinner =>
          have hshape' : PartialTy.sameShape left right := by
            simpa [PartialTy.sameShape] using hshape
          rcases ih hinner hshape' with ⟨targets', hc, hsub⟩
          exact ⟨targets', PartialTyContains.box hc, hsub⟩
  | @tyBox left right _hsub ih =>
      intro hshape
      cases hcontains with
      | tyBox hinner =>
          have hshape' : PartialTy.sameShape (.ty left) (.ty right) := by
            simpa [PartialTy.sameShape, Ty.sameShape] using hshape
          rcases ih hinner hshape' with ⟨targets', hc, hsub⟩
          exact ⟨targets', PartialTyContains.tyBox hc, hsub⟩
  | @borrow m leftTargets rightTargets hsubset =>
      intro _hshape
      cases hcontains with
      | here => exact ⟨rightTargets, PartialTyContains.here, hsubset⟩
  | @undefLeft left right _hsub _ih =>
      intro _hshape
      cases hcontains
  | @intoUndef left right _hsub _ih =>
      intro hshape
      simp [PartialTy.sameShape] at hshape
  | @boxIntoUndef left right _hsub _ih =>
      intro hshape
      simp [PartialTy.sameShape] at hshape

/-- A borrow contained in the coarser side of a same-shape strengthening
originates from a borrow with the same mutability in the finer side.

The target list may be smaller on the fine side.  This is the structural reason
join widening cannot invent a new borrow kind; it can only add static target
alternatives to an existing borrow node. -/
theorem partialTyContains_borrow_pullback_strengthens
    {sourceTy resultTy : PartialTy} {mutable : Bool} {targets : List LVal} :
    PartialTyStrengthens sourceTy resultTy →
    PartialTy.sameShape sourceTy resultTy →
    PartialTyContains resultTy (.borrow mutable targets) →
    ∃ sourceTargets,
      PartialTyContains sourceTy (.borrow mutable sourceTargets) ∧
        sourceTargets.Subset targets := by
  intro hstrength
  induction hstrength generalizing targets with
  | @reflex ty =>
      intro _hshape hcontains
      exact ⟨targets, hcontains, fun _ h => h⟩
  | @box left right _hsub ih =>
      intro hshape hcontains
      cases hcontains with
      | box hinner =>
          have hshape' : PartialTy.sameShape left right := by
            simpa [PartialTy.sameShape] using hshape
          rcases ih hshape' hinner with ⟨sourceTargets, hcontains',
            hsubset⟩
          exact ⟨sourceTargets, PartialTyContains.box hcontains', hsubset⟩
  | @tyBox left right _hsub ih =>
      intro hshape hcontains
      cases hcontains with
      | tyBox hinner =>
          have hshape' : PartialTy.sameShape (.ty left) (.ty right) := by
            simpa [PartialTy.sameShape, Ty.sameShape] using hshape
          rcases ih hshape' hinner with ⟨sourceTargets, hcontains',
            hsubset⟩
          exact ⟨sourceTargets, PartialTyContains.tyBox hcontains',
            hsubset⟩
  | @borrow m leftTargets rightTargets hsubset =>
      intro _hshape hcontains
      cases hcontains with
      | here =>
          exact ⟨leftTargets, PartialTyContains.here, hsubset⟩
  | @undefLeft left right _hsub _ih =>
      intro _hshape hcontains
      cases hcontains
  | @intoUndef left right _hsub _ih =>
      intro hshape _hcontains
      simp [PartialTy.sameShape] at hshape
  | @boxIntoUndef left right _hsub _ih =>
      intro hshape _hcontains
      simp [PartialTy.sameShape] at hshape

/-- "Preserve writeProhibited": a write that is not prohibited in the coarser
(result) environment is not prohibited in any finer same-shape strengthening
environment.  Strengthening only grows borrow target lists, so the finer
environment has *fewer* conflicting borrows.  This is the mechanised form of the
T-If insight — every write that type-checks against the merged join env is
automatically safe against each branch env. -/
theorem not_writeProhibited_of_sameShapeStrengthening
    {envFine envCoarse : Env} {w : LVal} :
    EnvSameShapeStrengthening envFine envCoarse →
    ¬ WriteProhibited envCoarse w →
    ¬ WriteProhibited envFine w := by
  intro hstr hnot hfine
  have htransport :
      ∀ x mutable targets target,
        envFine ⊢ x ↝ (.borrow mutable targets) →
        target ∈ targets →
        ∃ targets', envCoarse ⊢ x ↝ (.borrow mutable targets') ∧ target ∈ targets' := by
    intro x mutable targets target hcontains hmem
    rcases hcontains with ⟨fineSlot, hfineSlot, hcont⟩
    rcases hstr.2 x fineSlot hfineSlot with ⟨coarseSlot, hcoarseSlot, _hlife⟩
    rcases hstr.1 x coarseSlot hcoarseSlot with
      ⟨fineSlot', hfineSlot', _hlife', hstrength, hshape⟩
    have heq : fineSlot = fineSlot' :=
      Option.some.inj (hfineSlot.symm.trans hfineSlot')
    subst heq
    rcases partialTyContains_borrow_transport_strengthens hcont hstrength hshape with
      ⟨targets', hcontR, hsub⟩
    exact ⟨targets', ⟨coarseSlot, hcoarseSlot, hcontR⟩, hsub hmem⟩
  apply hnot
  unfold WriteProhibited ReadProhibited at hfine ⊢
  rcases hfine with ⟨x, targets, target, hcont, hmem, hconf⟩ |
      ⟨x, targets, target, hcont, hmem, hconf⟩
  · rcases htransport x true targets target hcont hmem with ⟨targets', hcontR, hmemR⟩
    exact Or.inl ⟨x, targets', target, hcontR, hmemR, hconf⟩
  · rcases htransport x false targets target hcont hmem with ⟨targets', hcontR, hmemR⟩
    exact Or.inr ⟨x, targets', target, hcontR, hmemR, hconf⟩

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

/-- Same-shape strengthening commutes with `dropLifetime`: both environments
drop exactly the slots at the given lifetime (strengthening preserves slot
lifetimes), and the survivors keep their strengthening relationship. -/
theorem EnvSameShapeStrengthening.dropLifetime {source result : Env}
    {lifetime : Lifetime} :
    EnvSameShapeStrengthening source result →
    EnvSameShapeStrengthening (source.dropLifetime lifetime)
      (result.dropLifetime lifetime) := by
  intro hmap
  constructor
  · intro x resultSlot hresult
    simp only [Env.dropLifetime] at hresult
    cases hr : result.slotAt x with
    | none => rw [hr] at hresult; simp at hresult
    | some slot =>
        rw [hr] at hresult
        by_cases hlt : slot.lifetime = lifetime
        · simp [hlt] at hresult
        · simp [hlt] at hresult
          subst hresult
          rcases hmap.1 x slot hr with ⟨sourceSlot, hsource, hlife, hstr, hshape⟩
          refine ⟨sourceSlot, ?_, hlife, hstr, hshape⟩
          simp only [Env.dropLifetime, hsource]
          have hne : sourceSlot.lifetime ≠ lifetime := by rw [hlife]; exact hlt
          simp [hne]
  · intro x sourceSlot hsource
    simp only [Env.dropLifetime] at hsource
    cases hs : source.slotAt x with
    | none => rw [hs] at hsource; simp at hsource
    | some slot =>
        rw [hs] at hsource
        by_cases hlt : slot.lifetime = lifetime
        · simp [hlt] at hsource
        · simp [hlt] at hsource
          subst hsource
          rcases hmap.2 x slot hs with ⟨resultSlot, hresult, hlife⟩
          refine ⟨resultSlot, ?_, hlife⟩
          simp only [Env.dropLifetime, hresult]
          have hne : resultSlot.lifetime ≠ lifetime := by rw [← hlife]; exact hlt
          simp [hne]

/-- `t` is the live target a stored borrow value actually points to: some store
cell holds a (non-owning) reference to a location that `t` resolves to.  Unlike
mere resolvability, a *stale* merged-join target — one no current borrow points
to — does not satisfy this, so the live-target witness env can drop it and stay
borrow safe. -/
def TargetPointedTo (store : ProgramStore) (t : LVal) : Prop :=
  ∃ cell cellSlot loc,
    store.slotAt cell = some cellSlot ∧
      cellSlot.value = .value (.ref { location := loc, owner := false }) ∧
      store.loc t = some loc

/-- `t` is the live target selected by root `x`'s OWN borrow: `x`'s value reaches
(via ownership) a cell holding a reference to a location that `t` resolves to.
Unlike `TargetPointedTo` (which allows *any* root's borrow), this ties the live
target to `x`.  Across joins this gives a runtime fact about the concrete
location, not necessarily about the same syntactic target lvalue: a joined
target may resolve to the same store location as the executed branch's target
without being textually the same lvalue.  (`ProtectedByBase` inlined to keep
this before the witness definition.) -/
def SelectedTarget (store : ProgramStore) (x : Name) (t : LVal) : Prop :=
  ∃ cell cellSlot loc,
    (cell = VariableProjection x ∨
        ProgramStore.OwnsTransitively store (VariableProjection x) cell) ∧
      store.slotAt cell = some cellSlot ∧
      cellSlot.value = .value (.ref { location := loc, owner := false }) ∧
      store.loc t = some loc

/-- A selected target is in particular pointed to (forgetting the root). -/
theorem SelectedTarget.targetPointedTo {store : ProgramStore} {x : Name}
    {t : LVal} : SelectedTarget store x t → TargetPointedTo store t := by
  rintro ⟨cell, cellSlot, loc, _hprot, hslot, hval, hloc⟩
  exact ⟨cell, cellSlot, loc, hslot, hval, hloc⟩

/-- Inversion: the storage of a valid `value` owns (directly) `owned` iff
`value` is a `box`/`boxFull` whose pointee is exactly `owned`.  For non-box
valid values there is no owning edge. -/
theorem ownsAt_storage_inv {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {storage owned : Location}
    {stoLt : Lifetime} :
    ValidPartialValue store value ty →
    store.slotAt storage = some { value := value, lifetime := stoLt } →
    ProgramStore.OwnsAt store owned storage →
    (∃ inner, ty = .box inner ∧
        value = .value (.ref { location := owned, owner := true })) ∨
    (∃ innerTy, ty = .ty (.box innerTy) ∧
        value = .value (.ref { location := owned, owner := true })) := by
  intro hvalid hsto howns
  rcases howns with ⟨lt, hslot⟩
  rw [hsto] at hslot
  have hval : value = .value (owningRef owned) := by
    have := Option.some.inj hslot
    simpa using congrArg StoreSlot.value this
  cases hvalid with
  | unit => simp [owningRef] at hval
  | int => simp [owningRef] at hval
  | bool => simp [owningRef] at hval
  | undef => simp [owningRef] at hval
  | @borrow location mutable targets target hmem hloc =>
      simp [owningRef] at hval
  | @box ownerLocation ownerSlot inner hownerSlot hinnerValid =>
      left
      refine ⟨inner, rfl, ?_⟩
      have : ownerLocation = owned := by
        simpa [owningRef] using hval
      subst this
      simp [owningRef] at hval ⊢
  | @boxFull ownerLocation ownerSlot innerTy hownerSlot hinnerValid =>
      right
      refine ⟨innerTy, rfl, ?_⟩
      have : ownerLocation = owned := by
        simpa [owningRef] using hval
      subst this
      simp [owningRef] at hval ⊢

/-- Reverse-descent.  `value` valid at `ty` is stored at `storage`; `storage`
owns (directly or transitively) `cell`, which holds a *borrow* (non-owning)
reference to `loc`.  Then `ty` contains a borrow type one of whose static
targets resolves (`store.loc`) to `loc`.  This is the structural inverse of the
forward `Reaches`/`BorrowDependency` chases: instead of walking a value down to
a dependency, it climbs an ownership chain back up to the env borrow node whose
realization explains the cell. -/
theorem borrowContains_of_owned_borrowCell {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {storage cell loc : Location}
    {cellSlot : StoreSlot} {stoLt : Lifetime} :
    ValidPartialValue store value ty →
    store.slotAt storage = some { value := value, lifetime := stoLt } →
    ProgramStore.OwnsTransitively store storage cell →
    store.slotAt cell = some cellSlot →
    cellSlot.value = .value (.ref { location := loc, owner := false }) →
    ∃ mutable targets target,
      PartialTyContains ty (.borrow mutable targets) ∧
      target ∈ targets ∧ store.loc target = some loc := by
  intro hvalid hsto howns
  induction howns generalizing value ty stoLt with
  | @direct storage owned hownsEdge =>
      intro hcell hcellval
      rcases ownsAt_storage_inv hvalid hsto hownsEdge with
        ⟨inner, htyEq, hvalEq⟩ | ⟨innerTy, htyEq, hvalEq⟩
      · subst htyEq
        cases hvalid with
        | @box ol os _ hos hinner =>
            have holEq : ol = owned := by simpa using hvalEq
            subst holEq
            have hosEq : os = cellSlot := Option.some.inj (hos.symm.trans hcell)
            subst hosEq
            rw [hcellval] at hinner
            cases hinner with
            | @borrow location mutable targets target hmem hloc =>
                exact ⟨mutable, targets, target,
                  PartialTyContains.box PartialTyContains.here, hmem, hloc⟩
      · subst htyEq
        cases hvalid with
        | @boxFull ol os _ hos hinner =>
            have holEq : ol = owned := by simpa using hvalEq
            subst holEq
            have hosEq : os = cellSlot := Option.some.inj (hos.symm.trans hcell)
            subst hosEq
            rw [hcellval] at hinner
            cases hinner with
            | @borrow location mutable targets target hmem hloc =>
                exact ⟨mutable, targets, target,
                  PartialTyContains.tyBox PartialTyContains.here, hmem, hloc⟩
  | @trans storage middle owned hownsEdge htail ih =>
      intro hcell hcellval
      rcases ownsAt_storage_inv hvalid hsto hownsEdge with
        ⟨inner, htyEq, hvalEq⟩ | ⟨innerTy, htyEq, hvalEq⟩
      · subst htyEq
        cases hvalid with
        | @box ol os _ hos hinner =>
            have holEq : ol = middle := by simpa using hvalEq
            subst holEq
            rcases ih hinner hos hcell hcellval with ⟨m, ts, t, hcontains, hmem, hloc⟩
            exact ⟨m, ts, t, PartialTyContains.box hcontains, hmem, hloc⟩
      · subst htyEq
        cases hvalid with
        | @boxFull ol os _ hos hinner =>
            have holEq : ol = middle := by simpa using hvalEq
            subst holEq
            rcases ih hinner hos hcell hcellval with ⟨m, ts, t, hcontains, hmem, hloc⟩
            exact ⟨m, ts, t, PartialTyContains.tyBox hcontains, hmem, hloc⟩

/-- A value that is a *borrow* (non-owning) reference, valid at `ty`, forces `ty`
to be a plain borrow type whose static targets contain one resolving to the
pointee. -/
theorem borrowContains_of_valid_borrowRef {store : ProgramStore}
    {ty : PartialTy} {loc : Location} :
    ValidPartialValue store (.value (.ref { location := loc, owner := false })) ty →
    ∃ mutable targets target,
      ty = .ty (.borrow mutable targets) ∧
      target ∈ targets ∧ store.loc target = some loc := by
  intro hvalid
  cases hvalid with
  | @borrow location mutable targets target hmem hloc =>
      exact ⟨mutable, targets, target, rfl, hmem, hloc⟩

/-- From a `SelectedTarget store x s` (a cell owned by `x` holding a borrow ref
to `loc`, with `store.loc s = some loc`) and a store that realizes `env`,
recover the genuine `env` borrow node at `x` together with a *realized* env
target `t₃` (`store.loc t₃ = some loc`).  `t₃` is in particular itself a
selected target of `x`, co-located with the original cell.  This is the
realization bridge from a runtime selected target to a static branch borrow
node. -/
theorem envBorrow_of_selectedTarget {store : ProgramStore} {env : Env}
    {x : Name} {s : LVal} :
    store ∼ₛ env →
    SelectedTarget store x s →
    ∃ mutable targets t₃,
      env ⊢ x ↝ (.borrow mutable targets) ∧ t₃ ∈ targets ∧
      SelectedTarget store x t₃ ∧ store.loc t₃ = store.loc s := by
  intro hrealize hsel
  rcases hsel with ⟨cell, cellSlot, loc, hprot, hcellSlot, hcellval, hsloc⟩
  obtain ⟨xEnvSlot, hxEnvSlot⟩ : ∃ es, env.slotAt x = some es := by
    have hdom := (hrealize.1 x).1
    have hxStore : ∃ slot, store.slotAt (VariableProjection x) = some slot := by
      rcases hprot with hvar | howns
      · exact ⟨cellSlot, by rw [← hvar]; exact hcellSlot⟩
      · cases howns with
        | direct hedge => rcases hedge with ⟨lt, hslot⟩; exact ⟨_, hslot⟩
        | trans hedge _ => rcases hedge with ⟨lt, hslot⟩; exact ⟨_, hslot⟩
    exact hdom hxStore
  rcases hrealize.2 x xEnvSlot hxEnvSlot with ⟨xValue, hxStoreSlot, hxValid⟩
  rcases hprot with hvar | howns
  · subst hvar
    have hvalEq : xValue = .value (.ref { location := loc, owner := false }) := by
      have heq : some (StoreSlot.mk xValue xEnvSlot.lifetime) = some cellSlot :=
        hxStoreSlot.symm.trans hcellSlot
      have hvv := congrArg StoreSlot.value (Option.some.inj heq)
      simpa [hcellval] using hvv
    rw [hvalEq] at hxValid
    rcases borrowContains_of_valid_borrowRef hxValid with
      ⟨mutable, targets, target, htyEq, hmem, hloc⟩
    refine ⟨mutable, targets, target, ⟨xEnvSlot, hxEnvSlot,
      htyEq ▸ PartialTyContains.here⟩, hmem,
      ⟨VariableProjection x, cellSlot, loc, Or.inl rfl, hcellSlot,
        hcellval, hloc⟩, ?_⟩
    rw [hloc, hsloc]
  · rcases borrowContains_of_owned_borrowCell hxValid hxStoreSlot howns
        hcellSlot hcellval with ⟨mutable, targets, target, hcontains, hmem, hloc⟩
    refine ⟨mutable, targets, target,
      ⟨xEnvSlot, hxEnvSlot, hcontains⟩, hmem,
      ⟨cell, cellSlot, loc, Or.inr howns, hcellSlot, hcellval, hloc⟩, ?_⟩
    rw [hloc, hsloc]

/-- Safe abstraction recovers a branch-environment borrow node at the concrete
location selected by a runtime target.

The recovered target need not be syntactically the same lvalue as the queried
target; it is the target actually justified by the branch environment and it
resolves to the same concrete location. -/
theorem envBorrow_locationWitness_of_selectedTarget {store : ProgramStore}
    {env : Env} {x : Name} {target : LVal} {leaf : Location} :
    store ∼ₛ env →
    SelectedTarget store x target →
    store.loc target = some leaf →
    ∃ mutable targets branchTarget,
      env ⊢ x ↝ (.borrow mutable targets) ∧
        branchTarget ∈ targets ∧
        SelectedTarget store x branchTarget ∧
        store.loc branchTarget = some leaf := by
  intro hsafe hselected hloc
  rcases envBorrow_of_selectedTarget hsafe hselected with
    ⟨mutable, targets, branchTarget, hcontains, hmem, hselectedBranch,
      hlocEq⟩
  exact ⟨mutable, targets, branchTarget, hcontains, hmem, hselectedBranch,
    hlocEq.trans hloc⟩

/-- The `&mut` *location-exclusivity* invariant of the executed-branch store
across a `T-If` join (`store ∼ₛ env₃`, `env₅ = env₃ ⊔ env₄`).

Read off the realized env₃ store: whenever an env₅ borrow node at root `x`
*selects* (`SelectedTarget store x s`) a target `s` reaching some location, and
the realized branch env₃ *also* selects, at the same root `x`, a target `t₃`
reaching the *same* location (`store.loc t₃ = store.loc s`), then the two borrow
nodes carry the same mutability bit.

This is the honest store-level invariant the §4.5.1 ite-join deviation needs:
at most one *live* `&mut` borrow reaches any given location, so a runtime cell
that co-resolves an env₄-only join target `s` and an env₃ target `t₃` cannot
disagree on `&mut`-ness — the mutability reaching a location is a function of the
location, not of which branch's target names it.  Crucially it is purely a
property of the realized store plus which targets are `&mut` (read off env₃ and
the join), so it is *invariant under the type-level ite join*: the join never
touches the store, and W-Bor preserves the mutable bit. -/
def LocMutExcl (store : ProgramStore) (env₃ env₅ : Env) : Prop :=
  ∀ x mutable targets s,
    env₅ ⊢ x ↝ (.borrow mutable targets) → s ∈ targets → SelectedTarget store x s →
    ∀ mutable₃ targets₃ t₃,
      env₃ ⊢ x ↝ (.borrow mutable₃ targets₃) → t₃ ∈ targets₃ →
      SelectedTarget store x t₃ →
      store.loc t₃ = store.loc s →
      mutable₃ = mutable

/-- `BorrowDependency` is monotone along a same-shape strengthening of the type:
strengthening only grows borrow target lists (W-Bor), so any borrow-resolution
dependency present at the finer type persists at the coarser type.  Equivalently,
`SlotDepKill` over the coarse (join) type implies it over each finer branch type
— the bridge for transporting the deref-write frame between `env₅` and the
witness `env₃`. -/
theorem borrowDependency_mono_sameShape {store : ProgramStore}
    {value : PartialValue} {tyFine tyCoarse : PartialTy} {dep : Location} :
    RuntimeFrame.BorrowDependency store value tyFine dep →
    PartialTyStrengthens tyFine tyCoarse →
    PartialTy.sameShape tyFine tyCoarse →
    RuntimeFrame.BorrowDependency store value tyCoarse dep := by
  intro hdep
  induction hdep generalizing tyCoarse with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      intro hstr hshape
      cases hstr with
      | reflex => exact RuntimeFrame.BorrowDependency.borrow hmem hloc hreads
      | borrow hsub =>
          exact RuntimeFrame.BorrowDependency.borrow (hsub hmem) hloc hreads
      | intoUndef _ => simp [PartialTy.sameShape] at hshape
  | @boxInner location slot inner dependency hslot _hinner ih =>
      intro hstr hshape
      cases hstr with
      | reflex => exact RuntimeFrame.BorrowDependency.boxInner hslot _hinner
      | @box _innerL innerC hsubInner =>
          have hshapeInner : PartialTy.sameShape inner innerC := by
            simpa [PartialTy.sameShape] using hshape
          exact RuntimeFrame.BorrowDependency.boxInner hslot
            (ih hsubInner hshapeInner)
      | boxIntoUndef _ => simp [PartialTy.sameShape] at hshape
  | @boxFullInner location slot ty dependency hslot _hinner ih =>
      intro hstr hshape
      cases hstr with
      | reflex => exact RuntimeFrame.BorrowDependency.boxFullInner hslot _hinner
      | @tyBox _innerL innerC hsubInner =>
          have hshapeInner : PartialTy.sameShape (.ty ty) (.ty innerC) := by
            simpa [PartialTy.sameShape, Ty.sameShape] using hshape
          exact RuntimeFrame.BorrowDependency.boxFullInner hslot
            (ih hsubInner hshapeInner)
      | intoUndef _ => simp [PartialTy.sameShape] at hshape

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
theorem TerminalStateSafe.strengthen_join {finalStore : ProgramStore}
    {finalValue : Value} {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafe finalStore finalValue branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafe finalStore finalValue joinEnv joinTy := by
  have hwellJoin : WellFormedEnv joinEnv lifetime :=
    ⟨hcontained,
      EnvSlotsOutlive.of_lifetimesPreserved hwellBranch.2.1 hpreserved,
      hcoherent, hlinear⟩
  have hsafeJoin : finalStore ∼ₛ joinEnv := hmap.safe hterminal.2.1
  exact ⟨hwellJoin, hterminal.1, hsafeJoin,
    safeStrengthening hwellJoin hsafeJoin hstrengthens hterminal.2.2⟩

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
  case strong | weak | box | mutBorrow => intros; trivial
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
  case strong | weak | box | mutBorrow => intros; trivial
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
  case strong | weak | box | mutBorrow => intros; trivial
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
  case strong | weak | box | mutBorrow => intros; trivial
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
  case var | box | borrow => intros; trivial
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
  | unit | int | bool => constructor
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
      | unit | int | bool => exact TermTyping.const (by constructor)
      | ref _hlookup => exact absurd hsourceValue (by simp [SourceValue]))
    (fun hwellTy hloanFree _hsource =>
      TermTyping.missing hwellTy hloanFree)
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
    (fun _hLhs hfresh _hghostRhs _hRhs hcopyL hcopyR hshape ihL ihGhost ihR
        hsource =>
      TermTyping.eq (ihL (SourceTerm.eq_lhs hsource)) hfresh
        (ihGhost (SourceTerm.eq_rhs hsource))
        (ihR (SourceTerm.eq_rhs hsource)) hcopyL hcopyR hshape)
    (fun _hcondition _htrue _hfalse hjoin henvJoin hsameLeft hsameRight hwellJoin
        hcontained hcoherent hlinear ihCondition ihTrue ihFalse hsource =>
      TermTyping.ite (ihCondition (SourceTerm.ite_condition hsource))
        (ihTrue (SourceTerm.ite_trueBranch hsource))
        (ihFalse (SourceTerm.ite_falseBranch hsource))
        hjoin henvJoin hsameLeft hsameRight hwellJoin hcontained hcoherent hlinear)
    (fun _hcondition _htrue _hfalse hdiverges ihCondition ihTrue ihFalse
        hsource =>
      TermTyping.iteDiverging (ihCondition (SourceTerm.ite_condition hsource))
        (ihTrue (SourceTerm.ite_trueBranch hsource))
        (ihFalse (SourceTerm.ite_falseBranch hsource))
        hdiverges)
    (fun hchild _hcond _hbody hwellTy hdrop ihCond ihBody hsource =>
      TermTyping.whileLoop hchild
        (ihCond (SourceTerm.while_condition hsource))
        (ihBody (SourceTerm.while_body hsource))
        hwellTy hdrop)
    (fun hchild _hcond _hbody hdiverges ihCond ihBody hsource =>
      TermTyping.whileLoopDiverging hchild
        (ihCond (SourceTerm.while_condition hsource))
        (ihBody (SourceTerm.while_body hsource))
        hdiverges)
    (fun hchild hjoin hss1 hss2 hcbwf hcoh hlin _hcondInv _hbodyInv
        hwellTy hdrop _hcondEntry _hbodyEntry
        ihCondInv ihBodyInv ihCondEntry ihBodyEntry hsource =>
      TermTyping.whileLoopJoin hchild hjoin hss1 hss2 hcbwf hcoh hlin
        (ihCondInv (SourceTerm.while_condition hsource))
        (ihBodyInv (SourceTerm.while_body hsource))
        hwellTy hdrop
        (ihCondEntry (SourceTerm.while_condition hsource))
        (ihBodyEntry (SourceTerm.while_body hsource)))
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
      intro _htargets
      exact WellFormedTy.bool)
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
  | unit | int | bool => constructor
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
      | ty struckTy | undef struckTy =>
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
  | unit | int | bool => constructor
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
      | ty _ | undef _ => simp [Strike] at h

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
      | ty _ | undef _ => simp [Strike] at h

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
  | unit | int | bool => constructor
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
    (fun {_env _typing _lifetime _ty} hwellTy _hloanFree _htypingEq hwellFormed =>
      ⟨hwellFormed, hwellTy⟩)
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
    (fun {_env₁ _env₂ _env₃ _envGhost _ghost _typing _lifetime _lhs _rhs
          _lhsTy _rhsTy _ghostRhsTy}
        _hLhs _hfresh _hghostRhs _hRhs _hcopyL _hcopyR _hshape
        ihL _ihGhost ihR htypingEq hwellFormed =>
      let leftResult := ihL htypingEq hwellFormed
      let rightResult := ihR htypingEq leftResult.1
      ⟨rightResult.1, WellFormedTy.bool⟩)
    (fun {_env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition _trueBranch
          _falseBranch _trueTy _falseTy _joinTy}
        _hcondition _htrue _hfalse _hjoin _henvJoin _hsameLeft _hsameRight hwellJoin
        hcontained hcoherent hlinear ihCondition ihTrue ihFalse
        htypingEq hwellFormed =>
      let conditionResult := ihCondition htypingEq hwellFormed
      let trueResult := ihTrue htypingEq conditionResult.1
      let falseResult := ihFalse htypingEq conditionResult.1
      ⟨⟨hcontained, by
          exact EnvSlotsOutlive.of_lifetimesPreserved trueResult.1.2.1
            (EnvJoin.lifetimesPreserved_left _henvJoin),
        hcoherent, hlinear⟩, hwellJoin⟩)
    (fun {_env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition _trueBranch
          _falseBranch _trueTy _falseTy}
        _hcondition _htrue _hfalse _hdiverges ihCondition ihTrue _ihFalse
        htypingEq hwellFormed =>
      let conditionResult := ihCondition htypingEq hwellFormed
      ihTrue htypingEq conditionResult.1)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition _body
          _bodyTy}
        _hchild _hcond _hbody _hwellTy _hdrop ihCond _ihBody
        htypingEq hwellFormed =>
      let conditionResult := ihCond htypingEq hwellFormed
      ⟨conditionResult.1, WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition _body
          _bodyTy}
        _hchild _hcond _hbody _hdiverges ihCond _ihBody
        htypingEq hwellFormed =>
      let conditionResult := ihCond htypingEq hwellFormed
      ⟨conditionResult.1, WellFormedTy.unit⟩)
    (fun {_env₁ _envBack _envInv _env₂ _envEntry₂ _env₃ _envEntry₃ _typing
          _lifetime _bodyLifetime _condition _body _bodyTy _bodyEntryTy}
        _hchild hjoin _hss1 _hss2 hcbwf hcoh hlin _hcondInv _hbodyInv
        _hwellTy _hdrop _hcondEntry _hbodyEntry
        ihCondInv _ihBodyInv _ihCondEntry _ihBodyEntry
        htypingEq hwellFormed =>
      let invWellFormed : WellFormedEnv _envInv _lifetime :=
        ⟨hcbwf,
          EnvSlotsOutlive.of_lifetimesPreserved hwellFormed.2.1
            (EnvJoin.lifetimesPreserved_left hjoin),
          hcoh, hlin⟩
      let conditionResult := ihCondInv htypingEq invWellFormed
      ⟨conditionResult.1, WellFormedTy.unit⟩)
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
  | bool b => exact ⟨.bool, ValueTyping.bool, ValidPartialValue.bool⟩
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

theorem ProtectedByBase.trans_ownsTransitively {store : ProgramStore}
    {x : Name} {storage owned : Location} :
    ProtectedByBase store x storage →
    ProgramStore.OwnsTransitively store storage owned →
    ProtectedByBase store x owned := by
  intro hprotected howns
  induction howns with
  | direct hedge =>
      exact ProtectedByBase.trans_owned hprotected hedge
  | trans hedge _htail ih =>
      exact ih (ProtectedByBase.trans_owned hprotected hedge)

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

/-- An ownership spine from a variable's projection protects its leaf: the leaf
is the variable itself (empty spine) or transitively owned by it.  This connects
`firstNodePack`'s spine to `ProtectedByBase`, the root component of a borrow's
*selected* target. -/
theorem protectedByBase {store : ProgramStore} {storage leaf : Location}
    {slot leafSlot : StoreSlot} {ty leafTy : PartialTy} {path : Path}
    {x : Name} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    storage = VariableProjection x →
    ProtectedByBase store x leaf := by
  intro hspine hstorage
  cases hspine with
  | nil _hslot _hvalid => exact Or.inl hstorage
  | box hslot howner htail =>
      subst hstorage
      exact Or.inr (ownsTransitively_of_cons
        (StoreOwnerSpine.box hslot howner htail))

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
      | strong | weak _hshape _hjoin => rfl
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
      | bool =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
              (by right; right; left; exact htyEq)
              hvalidValue hread hwriteStoreWritten hdrops
              hvalueNoReach hotherNoReach
      | borrow hleft hright hinner =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
              (by right; right; right; right; exact ⟨_, _, htyEq⟩)
              hvalidValue hread hwriteStoreWritten hdrops
              hvalueNoReach hotherNoReach
      | undefLeft hinner =>
          exact preservation_assign_var_envShape_step_runtime_of_frames
            (lifetime := lifetime)
            hsafe hvalidRuntime henvSlot hwrite
              (by right; right; right; left; exact ⟨_, htyEq⟩)
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

/-- Canonical components of an `R-Borrow` step.

The produced runtime reference contains the concrete location selected by
`store.loc`; it does not contain, or point back to, the static lvalue expression
or its target list. -/
theorem borrow_step_components {store store' : ProgramStore}
    {lifetime : Lifetime} {mutable : Bool} {lv : LVal}
    {finalValue : Value} :
    Step store lifetime (.borrow mutable lv) store' (.val finalValue) →
    ∃ location,
      store.loc lv = some location ∧
        store' = store ∧
        finalValue = .ref { location := location, owner := false } := by
  intro hstep
  cases hstep with
  | borrow hloc =>
      exact ⟨_, hloc, rfl, rfl⟩

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
  | unit | int | bool | undef =>
      intro _howners _hdeps
      constructor
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
  | unit | int | bool | undef =>
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

/-! ### Guarded-base chase

Resolving into (or reading from) a guard-protected owner tree forces the
resolving lvalue's base into the guard set, provided the guard set absorbs the
container of any borrow node that targets a guarded base.  At the assignment
use-site the guard set is the write's authority chain and absorption is supplied
by assignment-local `BorrowSafeRoot` obligations.
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
      t ∈ ts → SelectedTarget store container t → G (LVal.base t) → G container) →
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
        t ∈ ts → SelectedTarget store container t → G (LVal.base t) → G container)
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
        | unit | int | bool | undef =>
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
                (hcontainsM PartialTyContains.here) hmemW
                ⟨M, _, location, hprotM, hslotM, rfl, hlocW⟩ hGwitness
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
      t ∈ ts → SelectedTarget store container t → G (LVal.base t) → G container) →
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

/-- **Location-based `&mut` leaf exclusivity.**

The honest store-level runtime invariant that discharges the deref-write frame's
cross-variable kill obligation *pointwise*.

`MutLeafExclusive store env owner leaf` says: `leaf` is the runtime location a
live `&mut` (held by the lval `owner`) currently points to, and *no other*
variable's stored borrow resolves through it.  Concretely, for every variable
`z` distinct from `owner`'s base, `z`'s stored value carries **no** borrow
dependency reading `leaf` (`SlotDepKill store env leaf z`) — `z`'s borrow
back-edges never resolve through the written `&mut` leaf.

This is exactly the missing fact pinned down by "angle C": the `LocationBelow`
cycle in the deref-assign kill closes its DOWN direction for any borrow target
(`locReads_below`) but its UP direction only for `owner` itself (the firstNode,
whose deref chain *is* the write chain).  For a cross-variable `z` the UP
direction is unavailable, and the only contradiction is that `z` must not read
the written `&mut` leaf at all — i.e. `SlotDepKill` for that `z`.

`BorrowDependency` (hence `SlotDepKill`) is defined through `LocReads` and
`store.loc`, so this is a genuinely location-based store/env-level invariant —
keyed on actual store locations and realized pointees, never on a syntactic
merged target list — and the `T-If` join therefore preserves it for free.  The
owner's *own* dependency through `leaf` is handled separately by location
well-foundedness (`slotDepKill_of_firstNode`), so `MutLeafExclusive` only
constrains the genuinely cross-variable aliases. -/
def MutLeafExclusive (store : ProgramStore) (env : Env) (owner : LVal)
    (leaf : Location) : Prop :=
  ∀ z, z ≠ LVal.base owner → SlotDepKill store env leaf z

/-- **The general store/env-level `&mut`-exclusivity invariant.**

`MutBorrowsExclusive store env` is the write-agnostic invariant threaded through
preservation that discharges the deref-write frame's `MutLeafExclusive`
obligation.  It says: every live mutable borrow's runtime pointee location is
*exclusive* — no other variable's stored borrow resolves through it.

Concretely, for every lval `source` whose env type is `&mut targets` and whose
dereference resolves at runtime to a leaf location `leaf`
(`store.loc (.deref source) = some leaf`), the leaf is `MutLeafExclusive`: no
cross-variable borrow back-edge carries a `BorrowDependency` reading `leaf`.

This is a genuinely store-level / location-based invariant (keyed on
`store.loc` and `BorrowDependency`, never on a syntactic merged target list), so
the `T-If` *join* preserves it for free — the post-`ite` store is the executed
branch's store and `&mut`-ness is store-keyed.  Its real preservation crux is
straight-line borrow creation (`x = &mut y`), discharged by the borrow rule's
write-prohibition check. -/
def MutBorrowsExclusive (store : ProgramStore) (env : Env) : Prop :=
  ∀ (source : LVal) (targets : List LVal) (bl : Lifetime) (leaf : Location),
    LValTyping env source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    MutLeafExclusive store env source leaf

/-- The general invariant instantiates to the deref-write frame's
`MutLeafExclusive` obligation for any `&mut`-typed `source` whose deref resolves
to `leaf`. -/
theorem MutBorrowsExclusive.mutLeafExclusive {store : ProgramStore} {env : Env}
    {source : LVal} {targets : List LVal} {bl : Lifetime} {leaf : Location}
    (hexcl : MutBorrowsExclusive store env)
    (hsource : LValTyping env source (.ty (.borrow true targets)) bl)
    (hleaf : store.loc (.deref source) = some leaf) :
    MutLeafExclusive store env source leaf :=
  hexcl source targets bl leaf hsource hleaf

/-! ### Realized-witness `&mut` leaf exclusivity (join-trivial reformulation)

The `MutLeafExclusive`/`SlotDepKill` family above is keyed on
`RuntimeFrame.BorrowDependency store value zslot.ty leaf`, which reads `zslot.ty`
(the env type) — so it is ANTI-MONOTONE under the W-Bor target-list union and the
`T-If` join coarsens it, making establishment at the join impossible (the
§4.5.1 deviation, verified in Lean over many runs).

`RuntimeFrame.RealizedBorrowReads` (Frame.lean) is the TYPE-FREE realization: it
follows only the borrow target that resolves to the stored reference's OWN pointee
location, never a static target-list member.  Keying the kill on it removes the
env-type from the conclusion entirely, so the invariant below is invariant under
any env coarsening and the `T-If` join preserves it for free (the post-join store
is the executed branch's store). -/

/-- Type-free, store-realized version of `SlotDepKill`: variable `z`'s stored
value carries no *realized* borrow read of `leaf`.  Reads `env` only for the slot
lifetime (a store-realized quantity); the stored value's TYPE is never inspected,
so this predicate is unchanged by any env-type coarsening. -/
def RealizedSlotKill (store : ProgramStore) (env : Env) (leaf : Location)
    (z : Name) : Prop :=
  ∀ zslot value,
    env.slotAt z = some zslot →
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := zslot.lifetime } →
    ¬ RuntimeFrame.RealizedBorrowReads store value leaf

/-- A `RealizedSlotKill` discharges the `SlotDepKill` obligation: any
`BorrowDependency` is in particular a `RealizedBorrowReads`. -/
theorem RealizedSlotKill.slotDepKill {store : ProgramStore} {env : Env}
    {leaf : Location} {z : Name}
    (h : RealizedSlotKill store env leaf z) :
    SlotDepKill store env leaf z := by
  intro zslot value henv hstore hdep
  exact h zslot value henv hstore hdep.realizedBorrowReads

/-- Type-free version of `MutLeafExclusive`. -/
def RealizedLeafExclusive (store : ProgramStore) (env : Env) (owner : LVal)
    (leaf : Location) : Prop :=
  ∀ z, z ≠ LVal.base owner → RealizedSlotKill store env leaf z

/-- A `RealizedLeafExclusive` discharges the `MutLeafExclusive` obligation. -/
theorem RealizedLeafExclusive.mutLeafExclusive {store : ProgramStore} {env : Env}
    {owner : LVal} {leaf : Location}
    (h : RealizedLeafExclusive store env owner leaf) :
    MutLeafExclusive store env owner leaf :=
  fun z hz => (h z hz).slotDepKill

/-- **The join-trivial store-realized `&mut`-exclusivity invariant.**

Identical in shape to `MutBorrowsExclusive`, but its conclusion is the type-free
`RealizedLeafExclusive`.  The only env-dependence is the gate (`source` is
`&mut`-typed; `leaf` is its runtime pointee) — both store-realized facts that the
`T-If` join preserves — while the conclusion never reads any stored value's type.
This is what makes the join preserve it for free. -/
def RealizedMutBorrowsExclusive (store : ProgramStore) (env : Env) : Prop :=
  ∀ (source : LVal) (targets : List LVal) (bl : Lifetime) (leaf : Location),
    LValTyping env source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    RealizedLeafExclusive store env source leaf

/-- The realized invariant instantiates to the deref-write frame's
`MutLeafExclusive` obligation. -/
theorem RealizedMutBorrowsExclusive.mutLeafExclusive {store : ProgramStore}
    {env : Env} {source : LVal} {targets : List LVal} {bl : Lifetime}
    {leaf : Location}
    (hexcl : RealizedMutBorrowsExclusive store env)
    (hsource : LValTyping env source (.ty (.borrow true targets)) bl)
    (hleaf : store.loc (.deref source) = some leaf) :
    MutLeafExclusive store env source leaf :=
  (hexcl source targets bl leaf hsource hleaf).mutLeafExclusive

/-- **Conclusion-transfer (the join-trivial core).**  `RealizedSlotKill` transfers
along *any* env relation that preserves the slot lifetime of `z`, because its
conclusion (`¬ RealizedBorrowReads store value leaf`) is entirely store-keyed and
never inspects the slot type.  In particular it transfers from a finer env to its
same-shape strengthening (`EnvSameShapeStrengthening fine coarse`), which is what
makes the `T-If` join preserve the realized invariant for free — the prior
type-keyed `SlotDepKill` was anti-monotone here. -/
theorem RealizedSlotKill.transfer_lifetime {store : ProgramStore}
    {envFine envCoarse : Env} {leaf : Location} {z : Name}
    (hfine : RealizedSlotKill store envFine leaf z)
    (hlife : ∀ coarseSlot, envCoarse.slotAt z = some coarseSlot →
      ∃ fineSlot, envFine.slotAt z = some fineSlot ∧
        fineSlot.lifetime = coarseSlot.lifetime) :
    RealizedSlotKill store envCoarse leaf z := by
  intro coarseSlot value hcoarse hstore hreads
  rcases hlife coarseSlot hcoarse with ⟨fineSlot, hfineSlot, hlifeEq⟩
  refine hfine fineSlot value hfineSlot ?_ hreads
  rw [hlifeEq]; exact hstore

/-- **`RealizedLeafExclusive` transfers from a finer env to its same-shape
strengthening.**  The `owner` base is unchanged; for every other variable, the
conclusion transfers by `RealizedSlotKill.transfer_lifetime` using the lifetime
agreement built into `EnvSameShapeStrengthening`. -/
theorem RealizedLeafExclusive.of_strengthening {store : ProgramStore}
    {envFine envCoarse : Env} {owner : LVal} {leaf : Location}
    (hstr : EnvSameShapeStrengthening envFine envCoarse)
    (hfine : RealizedLeafExclusive store envFine owner leaf) :
    RealizedLeafExclusive store envCoarse owner leaf := by
  intro z hz
  refine (hfine z hz).transfer_lifetime ?_
  intro coarseSlot hcoarse
  rcases hstr.1 z coarseSlot hcoarse with
    ⟨fineSlot, hfineSlot, hlifeEq, _hstrength, _hshape⟩
  exact ⟨fineSlot, hfineSlot, hlifeEq⟩

/-- Inversion for successful runtime dereference resolution.

The store never carries a target list at runtime: `store.loc (.deref source)`
can succeed only because `source` resolves to an allocated slot whose value is a
single concrete reference. -/
theorem ProgramStore.loc_deref_some_inv {store : ProgramStore}
    {source : LVal} {leaf : Location} :
    store.loc (.deref source) = some leaf →
      ∃ sourceLocation ref sourceLifetime,
        store.loc source = some sourceLocation ∧
          store.slotAt sourceLocation =
            some { value := .value (.ref ref), lifetime := sourceLifetime } ∧
          ref.location = leaf := by
  intro hloc
  unfold ProgramStore.loc at hloc
  cases hsource : ProgramStore.loc store source with
  | none =>
      simp [hsource] at hloc
  | some sourceLocation =>
      cases hslot : store.slotAt sourceLocation with
      | none =>
          simp [hsource, hslot] at hloc
      | some sourceSlot =>
          cases sourceSlot with
          | mk sourceValue sourceLifetime =>
              cases sourceValue with
              | undef =>
                  simp [hsource, hslot] at hloc
              | value sourceValue =>
                  cases sourceValue with
                  | unit =>
                      simp [hsource, hslot] at hloc
                  | int value =>
                      simp [hsource, hslot] at hloc
                  | bool value =>
                      simp [hsource, hslot] at hloc
                  | ref ref =>
                      have hrefLocation : ref.location = leaf := by
                        simpa [hsource, hslot] using hloc
                      exact ⟨sourceLocation, ref, sourceLifetime,
                        by simpa only using hsource, by simpa using hslot,
                        hrefLocation⟩

/-- Runtime-realized `&mut` gate pullback.

A store-free pullback from the coarser join environment to the executed branch is
false: joins can grow target lists, and a dereference through an empty branch
target list may be typable only after the join.  Preservation only needs the
runtime-realized case, namely a coarse `&mut` source whose dereference actually
resolves to a concrete leaf in the current store.  That concrete resolution is
the bridge back to the executed branch's provenance registry. -/
def RuntimeLValMutGatePullback (store : ProgramStore)
    (envFine envCoarse : Env) : Prop :=
  ∀ source targets bl leaf,
    LValTyping envCoarse source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    ∃ targetsFine blFine,
      LValTyping envFine source (.ty (.borrow true targetsFine)) blFine

/-- The runtime mutable-borrow gate is reflexive. -/
theorem RuntimeLValMutGatePullback.refl (store : ProgramStore) (env : Env) :
    RuntimeLValMutGatePullback store env env := by
  intro source targets bl _leaf hsource _hleaf
  exact ⟨targets, bl, hsource⟩

/-- Runtime mutable-borrow gates compose. -/
theorem RuntimeLValMutGatePullback.trans {store : ProgramStore}
    {envFine envMiddle envCoarse : Env}
    (hleft : RuntimeLValMutGatePullback store envFine envMiddle)
    (hright : RuntimeLValMutGatePullback store envMiddle envCoarse) :
    RuntimeLValMutGatePullback store envFine envCoarse := by
  intro source targets bl leaf hsource hleaf
  rcases hright source targets bl leaf hsource hleaf with
    ⟨targetsMiddle, blMiddle, hmiddle⟩
  exact hleft source targetsMiddle blMiddle leaf hmiddle hleaf

/-- The **variable case** of borrow gate pullback is discharged outright by
`EnvSameShapeStrengthening`: a borrow-typed variable slot in the coarse (join)
env corresponds to a slot in the finer env whose type strengthens into it, and
same-shape forces that finer type to also be a borrow with the same mutability
bit (over a subset target list, hence the same `.var` base).

The full runtime gate needs this for both `&mut` sources and outer immutable
borrow sources such as `p : &&mut T`, where `*p` is the mutable-borrow source
that a later write consumes. -/
theorem lvalBorrowVar_pullback_of_strengthening {envFine envCoarse : Env}
    {x : Name} {mutable : Bool} {targets : List LVal} {bl : Lifetime}
    (hstr : EnvSameShapeStrengthening envFine envCoarse)
    (hcoarseSlot :
      envCoarse.slotAt x = some ⟨.ty (.borrow mutable targets), bl⟩) :
    ∃ targetsFine blFine,
      LValTyping envFine (.var x)
        (.ty (.borrow mutable targetsFine)) blFine := by
  rcases hstr.1 x ⟨.ty (.borrow mutable targets), bl⟩ hcoarseSlot with
    ⟨fineSlot, hfineSlot, _hlife, hstrength, hshape⟩
  cases fineSlot with
  | mk fty flt =>
    simp only at hstrength hshape
    cases hstrength with
    | reflex => exact ⟨targets, flt, LValTyping.var hfineSlot⟩
    | borrow _hsub => exact ⟨_, flt, LValTyping.var hfineSlot⟩

/-- Mutable-borrow specialization of `lvalBorrowVar_pullback_of_strengthening`. -/
theorem lvalMutVar_pullback_of_strengthening {envFine envCoarse : Env}
    {x : Name} {targets : List LVal} {bl : Lifetime}
    (hstr : EnvSameShapeStrengthening envFine envCoarse)
    (hcoarseSlot : envCoarse.slotAt x = some ⟨.ty (.borrow true targets), bl⟩) :
    ∃ targetsFine blFine,
      LValTyping envFine (.var x) (.ty (.borrow true targetsFine)) blFine := by
  exact lvalBorrowVar_pullback_of_strengthening hstr hcoarseSlot

/-- A binary type union is the least upper bound: it strengthens into any common
upper bound of its two inputs. -/
theorem PartialTyUnion.least {a b u ub : PartialTy}
    (hunion : PartialTyUnion a b u)
    (ha : PartialTyStrengthens a ub) (hb : PartialTyStrengthens b ub) :
    PartialTyStrengthens u ub := by
  have hupper : ub ∈ upperBounds ({a, b} : Set PartialTy) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  exact hunion.2 hupper

/-- A target-list union strengthens into any partial type `ub` that every member
target's type strengthens into.  This is the list-level least-upper-bound fact,
proved by structural recursion over the target list with `PartialTyUnion.least`
for the cons join. -/
theorem lvalTargetsTyping_union_le_of_forall_member_le {env : Env}
    {targets : List LVal} {unionTy ub : PartialTy} {lifetime : Lifetime}
    (htargets : LValTargetsTyping env targets unionTy lifetime)
    (hmem : ∀ t, t ∈ targets → ∀ tty tlt,
      LValTyping env t (.ty tty) tlt → PartialTyStrengthens (.ty tty) ub) :
    PartialTyStrengthens unionTy ub := by
  refine LValTargetsTyping.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun targets unionTy _ _ =>
      (∀ t, t ∈ targets → ∀ tty tlt,
        LValTyping env t (.ty tty) tlt → PartialTyStrengthens (.ty tty) ub) →
        PartialTyStrengthens unionTy ub)
    ?var ?box ?borrow ?singleton ?cons htargets hmem
  · intro _x _slot _hslot; trivial
  · intro _lv _inner _lifetime _htyping _ih; trivial
  · intro _lv _mutable _targets _bl _tl _tty _htyping _htargets _ih1 _ih2; trivial
  · intro target ty targetLifetime htyping _ihTyping hmem'
    exact hmem' target (by simp) _ _ htyping
  · intro target rest headTy headLifetime _restLifetime _lifetime restTy unionTy
      hhead _hrest hunion _hintersection _ihHead ihRest hmem'
    have hheadLe : PartialTyStrengthens (.ty headTy) ub :=
      hmem' target (by simp) _ _ hhead
    have hrestLe : PartialTyStrengthens restTy ub :=
      ihRest (fun t ht tty tlt htt =>
        hmem' t (List.mem_cons_of_mem _ ht) tty tlt htt)
    exact PartialTyUnion.least hunion hheadLe hrestLe

/-- **General lval typing pullback under same-shape strengthening (rank form).**

If `envFine` same-shape-strengthens into `envCoarse` and `envFine` is well-formed,
then any lvalue typing in the coarse env has a corresponding typing in the fine
env whose type has the *same shape* and *strengthens into* the coarse type.

This is store-free: `WellFormedEnv envFine` already forbids empty borrow-target
lists (via `Coherent`), so a dereference that types in the coarse env also types
in the fine env.  The variable case uses same-shape strengthening directly; the
box case recurses structurally; the borrow case rebuilds the fine target-list
typing from `Coherent envFine`, then pins the union to the coarse union via the
least-upper-bound fact, recursing on the strictly lower-ranked borrow targets
(linearization rank) and using fine-env determinism to reconcile the target
typing chosen by `Coherent` with the one produced by the recursion. -/
theorem lvalTyping_pullback_of_strengthening_rank
    {envFine envCoarse : Env} {φ : Name → Nat} {current : Lifetime}
    (hwellFine : WellFormedEnv envFine current)
    (hφF : LinearizedBy φ envFine)
    (hstr : EnvSameShapeStrengthening envFine envCoarse) :
    ∀ (rankBound sizeBound : Nat) {lv : LVal} {tyC : PartialTy} {lC : Lifetime},
      φ (LVal.base lv) < rankBound →
      sizeOf lv < sizeBound →
      LValTyping envCoarse lv tyC lC →
      ∃ tyF lF,
        LValTyping envFine lv tyF lF ∧
          PartialTy.sameShape tyF tyC ∧
          PartialTyStrengthens tyF tyC := by
  intro rankBound
  induction rankBound with
  | zero =>
      intro _sizeBound lv tyC lC hrank _hsize _htyping
      exact absurd hrank (Nat.not_lt_zero _)
  | succ rankBound ihRank =>
      intro sizeBound
      induction sizeBound with
      | zero =>
          intro lv tyC lC _hrank hsize _htyping
          exact absurd hsize (Nat.not_lt_zero _)
      | succ sizeBound ihSize =>
          intro lv tyC lC hrank hsize htyping
          cases htyping with
          | var hslot =>
              rename_i x slot
              rcases hstr.1 x slot hslot with
                ⟨fineSlot, hfineSlot, _hlife, hstrength, hshape⟩
              exact ⟨fineSlot.ty, fineSlot.lifetime,
                LValTyping.var hfineSlot, hshape, hstrength⟩
          | box hsource =>
              rename_i u
              rcases ihSize (lv := u) (by simpa [LVal.base] using hrank)
                  (by simp at hsize ⊢; omega) hsource with
                ⟨tyFU, lFU, hufine, hushape, hustrength⟩
              cases tyFU with
              | box innerF =>
                  refine ⟨innerF, lFU, LValTyping.box hufine, ?_, ?_⟩
                  · simpa [PartialTy.sameShape] using hushape
                  · cases hustrength with
                    | reflex => exact PartialTyStrengthens.reflex
                    | box h => exact h
              | ty t => simp [PartialTy.sameShape] at hushape
              | undef t => simp [PartialTy.sameShape] at hushape
          | borrow hsource htargets =>
              rename_i u mutable uTargets borrowLifetime
              rcases LValTargetsTyping.output_full htargets with ⟨tyCunion, rfl⟩
              rcases ihSize (lv := u) (by simpa [LVal.base] using hrank)
                  (by simp at hsize ⊢; omega) hsource with
                ⟨tyFU, lFU, hufine, hushape, hustrength⟩
              cases tyFU with
              | ty tF =>
                  cases tF with
                  | borrow mF uTargetsF =>
                      have hsubset : uTargetsF.Subset uTargets := by
                        cases hustrength with
                        | reflex => exact fun _ h => h
                        | borrow hsub => exact hsub
                      rcases hwellFine.2.2.1 u mF uTargetsF lFU hufine with
                        ⟨tyFunion, lFunion, htargetsFine⟩
                      have hUnionStrength :
                          PartialTyStrengthens (.ty tyFunion) (.ty tyCunion) := by
                        refine lvalTargetsTyping_union_le_of_forall_member_le
                          htargetsFine ?_
                        intro t ht tty tlt htfine
                        have htmem : t ∈ uTargets := hsubset ht
                        rcases lvalTargetsTyping_member_strengthens htargets t htmem
                          with ⟨ttyC, ttlC, htcoarse, htcStrength⟩
                        have htrank : φ (LVal.base t) < rankBound := by
                          have hlt := (lvalTyping_vars_rank_lt hφF).1 hufine
                            (LVal.base t)
                            (by
                              simp only [PartialTy.vars, Ty.vars, List.mem_map]
                              exact ⟨t, ht, rfl⟩)
                          have hu : φ (LVal.base u) < rankBound + 1 := by
                            simpa [LVal.base] using hrank
                          omega
                        rcases ihRank (sizeOf t + 1) htrank (Nat.lt_succ_self _)
                          htcoarse with
                          ⟨ttyF2, ttlF2, htfine2, _htshape2, htstrength2⟩
                        have heqv :=
                          lvalTyping_eqv_of_linearizedBy hφF htfine htfine2
                        have h1 : PartialTyStrengthens (.ty tty) ttyF2 :=
                          PartialTy.eqv_strengthens heqv
                        exact partialTyStrengthens_trans h1
                          (partialTyStrengthens_trans htstrength2 htcStrength)
                      refine ⟨.ty tyFunion, lFunion,
                        LValTyping.borrow hufine htargetsFine, ?_, hUnionStrength⟩
                      simpa [PartialTy.sameShape] using
                        ty_sameShape_of_strengthens hUnionStrength
                  | unit => simp [PartialTy.sameShape, Ty.sameShape] at hushape
                  | int => simp [PartialTy.sameShape, Ty.sameShape] at hushape
                  | bool => simp [PartialTy.sameShape, Ty.sameShape] at hushape
                  | box t' => simp [PartialTy.sameShape, Ty.sameShape] at hushape
              | box p => simp [PartialTy.sameShape] at hushape
              | undef t => simp [PartialTy.sameShape] at hushape

/-- The runtime-realized `&mut`-gate pullback follows from same-shape
strengthening alone: every coarse mutable-borrow source is a mutable-borrow
source in the fine env as well.  This is the join discharge that needs no
separate borrow-safety assumption.  (The store/safe-abstraction argument is kept
in the signature for call-site uniformity but is unused: `WellFormedEnv envFine`
already supplies everything via `Coherent`/`Linearizable`.) -/
theorem RuntimeLValMutGatePullback.of_sameShapeStrengthening
    {store : ProgramStore} {envFine envCoarse : Env} {current : Lifetime}
    (hwellFine : WellFormedEnv envFine current)
    (_hsafeFine : store ∼ₛ envFine)
    (hstr : EnvSameShapeStrengthening envFine envCoarse) :
    RuntimeLValMutGatePullback store envFine envCoarse := by
  intro source targets bl leaf hsource _hleaf
  rcases hwellFine.2.2.2 with ⟨φ, hφF⟩
  rcases lvalTyping_pullback_of_strengthening_rank hwellFine hφF hstr
      (φ (LVal.base source) + 1) (sizeOf source + 1)
      (Nat.lt_succ_self _) (Nat.lt_succ_self _) hsource with
    ⟨ptyFine, blFine, hfine, hshape, _hstrength⟩
  cases ptyFine with
  | ty t =>
      cases t with
      | borrow m ts =>
          have hm : m = true := by
            simpa [PartialTy.sameShape, Ty.sameShape] using hshape
          subst hm
          exact ⟨ts, blFine, hfine⟩
      | unit => simp [PartialTy.sameShape, Ty.sameShape] at hshape
      | int => simp [PartialTy.sameShape, Ty.sameShape] at hshape
      | bool => simp [PartialTy.sameShape, Ty.sameShape] at hshape
      | box t' => simp [PartialTy.sameShape, Ty.sameShape] at hshape
  | box p => simp [PartialTy.sameShape] at hshape
  | undef t => simp [PartialTy.sameShape] at hshape

/-- **The join-trivial monotonicity of the realized `&mut`-exclusivity invariant.**

Given the `&mut`-gate pullback, `RealizedMutBorrowsExclusive` transports from the
finer branch env `env₃` to its same-shape strengthening `env₅` (the `T-If` join).
The conclusion side is fully store-keyed and transports for free
(`RealizedLeafExclusive.of_strengthening`); the only env-type-sensitive ingredient
is the runtime-realized gate.  This is the join establishment that was
*impossible* for the type-keyed `MutBorrowsExclusive` (whose conclusion read the
join-coarsened slot type and was anti-monotone). -/
theorem realizedMutBorrowsExclusive_of_strengthening {store : ProgramStore}
    {envFine envCoarse : Env}
    (hstr : EnvSameShapeStrengthening envFine envCoarse)
    (hgate : RuntimeLValMutGatePullback store envFine envCoarse)
    (hfine : RealizedMutBorrowsExclusive store envFine) :
    RealizedMutBorrowsExclusive store envCoarse := by
  intro source targets bl leaf hsource hleaf
  rcases hgate source targets bl leaf hsource hleaf with
    ⟨targetsFine, blFine, hsourceFine⟩
  exact RealizedLeafExclusive.of_strengthening hstr
    (hfine source targetsFine blFine leaf hsourceFine hleaf)

/-! ### The live-`&mut` registry (trilemma-escape: env-type-free provenance)

The realized-witness analysis pinned a TRILEMMA (memory `soundness-current-sorries`,
Update 2026-06-16): the exclusivity predicate the deref-write kill needs must be
either (a) type-FREE — `RealizedBorrowReads` — which is join-trivial but
*unestablishable* at borrow creation (no typed target handle to invoke the borrow
rule), or (b) all-targets-typed — `BorrowDependency` — which is establishable but
*anti-monotone* (the W-Bor join coarsens the target list and the kill reads it).
Every prior design re-derived exclusivity from a *program point's* `(store, env)`,
so it was caught on one horn or the other.

The **escape** is to stop re-deriving exclusivity from the env at each program
point, and instead thread it as an INDEPENDENT invariant that carries its own
provenance: a *registry* `R : List (Location × Name)` recording, per live `&mut`
borrow, its runtime pointee `Location` together with the owning variable.  The
exclusivity invariant `MutRegistryExclusive store R` references ONLY the store and
`R` — never any env target list — so:

* the `T-If` join is a genuine pass-through (`MutRegistryExclusive.ite_passthrough`):
  the join leaves the store and `R` untouched and creates no borrows, so there is
  literally nothing to re-derive (CORNER B — the make-or-break corner);
* the registry is populated AT `&mut` creation, where the type/mut-bit IS known
  (so the unestablishability horn is also avoided, CORNER C);
* and it discharges the env-keyed `MutLeafExclusive` the deref-frame consumes via
  the existing store-realized `RealizedBorrowReads` frame (CORNER A).

The kill is keyed STORE-ONLY (`StoreRealizedSlotKill`): it quantifies over the
store's variable slots directly and never reads the env, not even for a lifetime.
That is what makes the invariant a function of `(store, R)` alone. -/

/-- **Store-only realized slot kill.**  Variable `z`'s stored value carries no
*realized* borrow read of `leaf`.  Unlike `RealizedSlotKill`, this reads NO env at
all (it quantifies over the store slot's value directly, for any lifetime), so it
is a function of the store alone.  It is strictly stronger than `RealizedSlotKill
store env leaf z` for every `env` (`StoreRealizedSlotKill.realizedSlotKill`). -/
def StoreRealizedSlotKill (store : ProgramStore) (leaf : Location)
    (z : Name) : Prop :=
  ∀ value lifetime,
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := lifetime } →
    ¬ RuntimeFrame.RealizedBorrowReads store value leaf

/-- A store-only kill discharges the env-keyed `RealizedSlotKill` for ANY env: it
already constrains the store slot under every lifetime, so in particular under the
one `env` assigns to `z`. -/
theorem StoreRealizedSlotKill.realizedSlotKill {store : ProgramStore} {env : Env}
    {leaf : Location} {z : Name}
    (h : StoreRealizedSlotKill store leaf z) :
    RealizedSlotKill store env leaf z := by
  intro zslot value _henv hstore hreads
  exact h value zslot.lifetime hstore hreads

/-- Erasing a store slot preserves store-realized kills: any realized read still
observable after the erase was already observable before it. -/
theorem StoreRealizedSlotKill.erase {store : ProgramStore}
    {leaf erased : Location} {z : Name}
    (h : StoreRealizedSlotKill store leaf z) :
    StoreRealizedSlotKill (store.erase erased) leaf z := by
  intro value lifetime hslot hreads
  exact h value lifetime (RuntimeFrame.slotAt_of_erase_slotAt hslot)
    (RuntimeFrame.RealizedBorrowReads.erase_to_store hreads)

/-- Updating one store slot to `undef` preserves store-realized kills: deleting
a value cannot create a new realized borrow read of the protected leaf. -/
theorem StoreRealizedSlotKill.update_undef {store : ProgramStore}
    {leaf updated : Location} {z : Name} {updatedLifetime : Lifetime}
    (h : StoreRealizedSlotKill store leaf z) :
    StoreRealizedSlotKill
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      leaf z := by
  intro value lifetime hslot hreads
  by_cases hz : VariableProjection z = updated
  · subst hz
    simp [ProgramStore.update] at hslot
    cases hslot
    cases hreads <;> simp at *
  · have hslotOld :
        store.slotAt (VariableProjection z) =
          some { value := value, lifetime := lifetime } := by
      simpa [ProgramStore.update, hz] using hslot
    exact h value lifetime hslotOld
      (RuntimeFrame.RealizedBorrowReads.update_undef_to_store hreads)

/-- **The live-`&mut` registry exclusivity invariant — a function of `(store, R)`
alone.**

`R : List (Location × Name)` lists, per live `&mut` borrow, its runtime pointee
`leaf` and owning variable `owner`.  The invariant says: for every registered
`(leaf, owner)`, the leaf is *exclusively* borrowed — no cross-variable (`z ≠
owner`) stored value carries a realized borrow read of `leaf`.

Crucially this references ONLY the store and `R`; it never reads any env target
list (it is keyed on `StoreRealizedSlotKill`, which is store-only).  That is what
makes the `T-If` join a genuine pass-through (CORNER B). -/
def MutRegistryExclusive (store : ProgramStore)
    (R : List (Location × Name)) : Prop :=
  ∀ leaf owner, (leaf, owner) ∈ R →
    ∀ z, z ≠ owner → StoreRealizedSlotKill store leaf z

/-! #### CORNER A — consumption

The registry discharges the env-keyed `MutLeafExclusive` premise that the existing
deref-write frame (`safeAbstraction_assign_deref_drop_of_wellFormed`,
`validPartialValue_update_of_owner_and_realized_reads_frame`) consumes, provided
the deref-write's `source` is registered at its pointee `leaf` (i.e. `(leaf,
base source) ∈ R`).  No env target list is touched: the store-only kill is lifted
to `RealizedSlotKill` (any env), then to `SlotDepKill`, then to
`MutLeafExclusive`. -/

/-- **CORNER A (consumption).**  If `source`'s pointee `leaf` is registered under
owner `base source`, the registry yields the env-keyed `MutLeafExclusive store env
source leaf` the deref-frame needs — for ANY `env`.  This is the connection from
the env-free registry to the existing consumption site. -/
theorem MutRegistryExclusive.mutLeafExclusive {store : ProgramStore} {env : Env}
    {R : List (Location × Name)} {source : LVal} {leaf : Location}
    (hexcl : MutRegistryExclusive store R)
    (hreg : (leaf, LVal.base source) ∈ R) :
    MutLeafExclusive store env source leaf := by
  intro z hz
  exact ((hexcl leaf (LVal.base source) hreg z hz).realizedSlotKill).slotDepKill

/-- Erasing a store slot preserves registry exclusivity. -/
theorem MutRegistryExclusive.erase {store : ProgramStore}
    {R : List (Location × Name)} {erased : Location}
    (hexcl : MutRegistryExclusive store R) :
    MutRegistryExclusive (store.erase erased) R := by
  intro leaf owner hmem z hz
  exact (hexcl leaf owner hmem z hz).erase

/-- Updating one store slot to `undef` preserves registry exclusivity. -/
theorem MutRegistryExclusive.update_undef {store : ProgramStore}
    {R : List (Location × Name)} {updated : Location}
    {updatedLifetime : Lifetime}
    (hexcl : MutRegistryExclusive store R) :
    MutRegistryExclusive
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      R := by
  intro leaf owner hmem z hz
  exact (hexcl leaf owner hmem z hz).update_undef

/-- Filtering registry entries preserves exclusivity.  This is useful for moves:
after the source slot is set to `undef`, entries owned by the moved root are no
longer needed for coverage, and dropping them prevents stale owners from
constraining a later destination that receives the moved borrow value. -/
theorem MutRegistryExclusive.filter {store : ProgramStore}
    {R : List (Location × Name)} (p : Location × Name → Bool)
    (hexcl : MutRegistryExclusive store R) :
    MutRegistryExclusive store (R.filter p) := by
  intro leaf owner hmem z hz
  exact hexcl leaf owner (List.mem_of_mem_filter hmem) z hz

/-- Appending two exclusive registries preserves exclusivity.  The hard
creation/update facts are local to each side; this lemma is only the registry
algebra. -/
theorem MutRegistryExclusive.append {store : ProgramStore}
    {left right : List (Location × Name)}
    (hleft : MutRegistryExclusive store left)
    (hright : MutRegistryExclusive store right) :
    MutRegistryExclusive store (left ++ right) := by
  intro leaf owner hmem z hz
  rcases List.mem_append.mp hmem with hleftMem | hrightMem
  · exact hleft leaf owner hleftMem z hz
  · exact hright leaf owner hrightMem z hz

/-! #### CORNER B — join pass-through (the make-or-break corner)

`MutRegistryExclusive store R` is a function of `(store, R)` alone, so a `T-If`
join — which leaves the store and the registry untouched, and creates no borrows —
preserves it *definitionally* with the SAME `store` and SAME `R`.  There is no env
target list to re-derive, which is exactly the horn every prior design impaled
itself on.  Stated as both an explicit pass-through and an env-independence lemma. -/

/-- **CORNER B (join pass-through).**  Across a `T-If` join the store and registry
are unchanged, so the registry invariant passes through with the SAME `store` and
SAME `R` — there is *nothing to re-derive*.  The proof is `id`: the invariant does
not mention any env, so neither the executed-branch env `env₃` nor the merged join
env `env₅` appears.  THIS is the corner all prior (env-keyed) designs failed. -/
theorem MutRegistryExclusive.ite_passthrough {store : ProgramStore}
    {R : List (Location × Name)}
    (h : MutRegistryExclusive store R) :
    MutRegistryExclusive store R :=
  h

/-- The registry invariant is **independent of the env** entirely: it transports
across *any* pair of envs with the SAME `store` and `R`.  This is the formal
content of "the join is a genuine pass-through" — quantifying over the two join
envs `envFine` (branch `env₃`) and `envCoarse` (join `env₅`) shows neither can
appear in the conclusion, so the W-Bor target-list coarsening cannot break it.
Contrast `realizedMutBorrowsExclusive_of_strengthening`, which still needed the
runtime-realized env-type ingredient; the registry needs none. -/
theorem MutRegistryExclusive.env_independent {store : ProgramStore}
    {R : List (Location × Name)} (_envFine _envCoarse : Env)
    (h : MutRegistryExclusive store R) :
    MutRegistryExclusive store R :=
  h

/-! #### CORNER C — creation establishment

A straight-line `&mut`-creation step `x = &mut y` extends `R` with `(loc_y, x)`.
Establishing `MutRegistryExclusive` for the extended registry splits on the new
entry vs. the old ones:

* old entries `(leaf, owner) ∈ R` keep their kill — provided the creation does not
  introduce a new realized read of an old `leaf` (the frame side condition, which
  the borrow rule's write/read-prohibition supplies);
* the new entry `(loc_y, x)` requires that no cross-variable `z ≠ x` reads `loc_y`
  — which is exactly the `&mut`-exclusivity at the pointee `loc_y` that the borrow
  rule's `¬ WriteProhibited` premise guarantees at creation (where the TYPE is
  known).

Below: the registry-extension *algebra* (the cons split), proved green, reducing
CORNER C to (i) old-entry stability under the creation update and (ii) the new
entry's pointee-exclusivity — the two facts the borrow rule supplies.  Full
threading through the creation step is later preservation engineering. -/

/-- **CORNER C (creation — the registry-extension algebra).**  Extending the
registry with a fresh entry `(newLeaf, x)` preserves `MutRegistryExclusive`,
given (i) the pre-existing invariant still holds at the (possibly updated) store,
and (ii) the new entry's pointee `newLeaf` is exclusively borrowed by `x` — i.e.
every cross-variable `z ≠ x` has a `StoreRealizedSlotKill store newLeaf z`.  This
isolates exactly the two obligations the borrow rule discharges at `x = &mut y`:
old-entry stability and new-pointee exclusivity. -/
theorem MutRegistryExclusive.cons {store : ProgramStore}
    {R : List (Location × Name)} {newLeaf : Location} {x : Name}
    (hold : MutRegistryExclusive store R)
    (hnew : ∀ z, z ≠ x → StoreRealizedSlotKill store newLeaf z) :
    MutRegistryExclusive store ((newLeaf, x) :: R) := by
  intro leaf owner hmem z hz
  rcases List.mem_cons.mp hmem with heq | htail
  · -- the new entry
    cases heq
    exact hnew z hz
  · -- an old entry
    exact hold leaf owner htail z hz

/-! #### Value-scoped provenance

Before a terminal RHS value is stored in an environment root, its mutable-borrow
provenance is not yet env coverage.  The following predicate records the
concrete `&mut` pointees carried by a value; declaration/assignment installation
will transfer these entries to the destination owner. -/

/-! #### Concrete runtime borrow footprint

The registry below records mutable borrow leaves, but the *kill* side should not
be phrased in terms of a lvalue expression that once produced a reference.  At
runtime a non-owning reference stores one concrete location.  A write to `leaf`
can invalidate such a reference only when that concrete location is exactly
`leaf`, or when it is owned below `leaf` and will be recursively dropped by the
write.  In particular, after `x = &a; y = &*x`, the store value of `y` points to
`a`; it is not a runtime reference to the expression `*x`.

This footprint is intentionally independent of environment target lists, so a
join can widen static targets without manufacturing new runtime aliases. -/

/-- Concrete non-owning references carried by a runtime partial value.  This
relation follows owned boxes in the store, but for a borrow it records only the
stored reference location. -/
inductive RuntimeValueBorrow (store : ProgramStore) :
    PartialValue → Location → Prop where
  | borrow {leaf : Location} :
      RuntimeValueBorrow store
        (.value (.ref { location := leaf, owner := false })) leaf
  | box {location : Location} {slot : StoreSlot} {leaf : Location} :
      store.slotAt location = some slot →
      RuntimeValueBorrow store slot.value leaf →
      RuntimeValueBorrow store
        (.value (.ref { location := location, owner := true })) leaf

/-- A pure owner spine ending in a non-owning borrow cell has exactly that
borrow as the concrete non-owning borrow footprint of its root value.

There are no product/sibling values in the core calculus: following a root value
through owned boxes is a single chain.  Thus, once the selected spine reaches
the first borrow cell, any concrete runtime borrow reachable from the root value
is the location stored in that cell. -/
theorem StoreOwnerSpine.runtimeValueBorrow_leaf_eq {store : ProgramStore}
    {storage leaf : Location} {slot leafSlot : StoreSlot}
    {ty leafTy : PartialTy} {path : Path} {borrowed observed : Location} :
    StoreOwnerSpine store storage slot ty path leaf leafSlot leafTy →
    leafSlot.value =
      .value (.ref { location := borrowed, owner := false }) →
    RuntimeValueBorrow store slot.value observed →
      observed = borrowed := by
  intro hspine hleafValue hborrow
  induction hspine with
  | nil _hslot _hvalid =>
      rw [hleafValue] at hborrow
      cases hborrow
      rfl
  | @box storage owned leaf slot ownedSlot leafSlot inner leafTy path hslot
      howner htail ih =>
      rw [howner] at hborrow
      cases hborrow with
      | box hownedSlot hinnerBorrow =>
          have hownedSlot' : store.slotAt owned = some ownedSlot :=
            StoreOwnerSpine.storage_slot htail
          have hslotEq : ownedSlot = _ :=
            Option.some.inj (hownedSlot'.symm.trans hownedSlot)
          subst hslotEq
          exact ih hleafValue hinnerBorrow

/-- Concrete runtime well-formedness for stored values, independent of static
borrow target lists.  A non-owning reference is well formed when its concrete
pointee is allocated; an owning reference follows the owned slot recursively.

This is the runtime shape needed for the join-friendly safety statement: a join
may widen target lists, but it cannot change the concrete location stored in a
reference. -/
inductive ConcreteRuntimeValueSafe (store : ProgramStore) :
    PartialValue → Prop where
  | unit :
      ConcreteRuntimeValueSafe store (.value .unit)
  | int {value : Int} :
      ConcreteRuntimeValueSafe store (.value (.int value))
  | bool {value : Bool} :
      ConcreteRuntimeValueSafe store (.value (.bool value))
  | undef :
      ConcreteRuntimeValueSafe store .undef
  | borrow {location : Location} {slot : StoreSlot} :
      store.slotAt location = some slot →
      ConcreteRuntimeValueSafe store
        (.value (.ref { location := location, owner := false }))
  | box {location : Location} {slot : StoreSlot} :
      store.slotAt location = some slot →
      ConcreteRuntimeValueSafe store slot.value →
      ConcreteRuntimeValueSafe store
        (.value (.ref { location := location, owner := true }))

/-- Type-free concrete reachability through a runtime value.

This is the concrete counterpart of `RuntimeFrame.Reaches`: it follows owning
references through the store and records non-owning reference pointees, but it
does not inspect a static type or a borrow target list. -/
inductive ConcreteRuntimeValueReaches (store : ProgramStore) :
    PartialValue → Location → Prop where
  | borrow {location : Location} :
      ConcreteRuntimeValueReaches store
        (.value (.ref { location := location, owner := false })) location
  | boxHere {location : Location} {slot : StoreSlot} :
      store.slotAt location = some slot →
      ConcreteRuntimeValueReaches store
        (.value (.ref { location := location, owner := true })) location
  | boxInner {location : Location} {slot : StoreSlot} {reached : Location} :
      store.slotAt location = some slot →
      ConcreteRuntimeValueReaches store slot.value reached →
      ConcreteRuntimeValueReaches store
        (.value (.ref { location := location, owner := true })) reached

/-- Concrete reachability splits into non-owning borrow reachability or owned
reachability from an owner carried by the value itself.  This is the type-free
runtime graph decomposition used by drop-safety arguments. -/
theorem ConcreteRuntimeValueReaches.borrow_or_owned {store : ProgramStore}
    {value : PartialValue} {reached : Location} :
    ConcreteRuntimeValueReaches store value reached →
      RuntimeValueBorrow store value reached ∨
        ∃ owner,
          owner ∈ partialValueOwningLocations value ∧
            (owner = reached ∨
              ProgramStore.OwnsTransitively store owner reached) := by
  intro hreach
  induction hreach with
  | borrow =>
      exact Or.inl RuntimeValueBorrow.borrow
  | @boxHere location slot hslot =>
      exact Or.inr ⟨location,
        mem_partialValueOwningLocations_ref_true (ref := { location := location, owner := true }) rfl,
        Or.inl rfl⟩
  | @boxInner location slot reached hslot _hinner ih =>
      rcases ih with hborrow | howned
      · exact Or.inl (RuntimeValueBorrow.box hslot hborrow)
      · rcases howned with ⟨owner, hownerMem, hownerRel⟩
        have hownsOwner : ProgramStore.OwnsAt store owner location := by
          have hslotValue : slot.value = .value (owningRef owner) :=
            eq_owningRef_of_mem_partialValueOwningLocations hownerMem
          exact ⟨slot.lifetime, by
            cases slot with
            | mk slotValue slotLifetime =>
                cases hslotValue
                simpa [owningRef] using hslot⟩
        have hlocationReaches :
            ProgramStore.OwnsTransitively store location reached := by
          rcases hownerRel with hownerEq | hpath
          · subst hownerEq
            exact ProgramStore.OwnsTransitively.direct hownsOwner
          · exact ProgramStore.OwnsTransitively.trans hownsOwner hpath
        exact Or.inr ⟨location,
          mem_partialValueOwningLocations_ref_true
            (ref := { location := location, owner := true }) rfl,
          Or.inr hlocationReaches⟩

/-- Erasing a slot cannot create a concrete runtime reachability witness. -/
theorem ConcreteRuntimeValueReaches.erase_to_store {store : ProgramStore}
    {erased : Location} {value : PartialValue} {reached : Location} :
    ConcreteRuntimeValueReaches (store.erase erased) value reached →
    ConcreteRuntimeValueReaches store value reached := by
  intro hreach
  induction hreach with
  | borrow =>
      exact ConcreteRuntimeValueReaches.borrow
  | boxHere hslot =>
      exact ConcreteRuntimeValueReaches.boxHere
        (RuntimeFrame.slotAt_of_erase_slotAt hslot)
  | boxInner hslot _hinner ih =>
      exact ConcreteRuntimeValueReaches.boxInner
        (RuntimeFrame.slotAt_of_erase_slotAt hslot) ih

/-- Erasing an unreached location preserves concrete runtime value safety. -/
theorem ConcreteRuntimeValueSafe.erase_of_not_reaches {store : ProgramStore}
    {erased : Location} {value : PartialValue} :
    ConcreteRuntimeValueSafe store value →
    (∀ reached, ConcreteRuntimeValueReaches store value reached →
      reached ≠ erased) →
    ConcreteRuntimeValueSafe (store.erase erased) value := by
  intro hsafe hnotReached
  induction hsafe with
  | unit =>
      exact ConcreteRuntimeValueSafe.unit
  | int =>
      exact ConcreteRuntimeValueSafe.int
  | bool =>
      exact ConcreteRuntimeValueSafe.bool
  | undef =>
      exact ConcreteRuntimeValueSafe.undef
  | @borrow location slot hslot =>
      have hne : location ≠ erased :=
        hnotReached location ConcreteRuntimeValueReaches.borrow
      exact ConcreteRuntimeValueSafe.borrow
        (by simpa [ProgramStore.erase, hne] using hslot)
  | @box location slot hslot _hinner ih =>
      have hne : location ≠ erased :=
        hnotReached location (ConcreteRuntimeValueReaches.boxHere hslot)
      have hslotErased :
          (store.erase erased).slotAt location = some slot := by
        simpa [ProgramStore.erase, hne] using hslot
      exact ConcreteRuntimeValueSafe.box hslotErased
        (ih (by
          intro reached hreach
          exact hnotReached reached
            (ConcreteRuntimeValueReaches.boxInner hslot hreach)))

/-- Recursive drops preserve concrete runtime value safety when every concrete
location reached by the value is avoided by the drop. -/
theorem ConcreteRuntimeValueSafe.drops_of_avoids_reaches
    {store store' : ProgramStore} {values : List PartialValue}
    {value : PartialValue} :
    Drops store values store' →
    ConcreteRuntimeValueSafe store value →
    (∀ reached, ConcreteRuntimeValueReaches store value reached →
      DropsAvoids store values reached) →
    ConcreteRuntimeValueSafe store' value := by
  intro hdrops hsafe havoids
  induction hdrops generalizing value with
  | nil =>
      exact hsafe
  | nonOwner hnonOwner _hdrops ih =>
      exact ih hsafe (by
        intro reached hreach
        have havoid := havoids reached hreach
        cases havoid with
        | nonOwner _ hrest => exact hrest
        | ownerMissing howner _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerPresent howner _ _ _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner))
  | ownerMissing howner hmissing _hdrops ih =>
      exact ih hsafe (by
        intro reached hreach
        have havoid := havoids reached hreach
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
          ∀ reached,
            ConcreteRuntimeValueReaches storeBefore value reached →
              reached ≠ ref.location := by
        intro reached hreach hreached
        have havoid := havoids reached hreach
        cases havoid with
        | nonOwner hnonOwner _ =>
            exact False.elim
              (not_partialValueNonOwner_owning_ref howner hnonOwner)
        | ownerMissing _ hmissing _ =>
            rw [hpresent] at hmissing
            cases hmissing
        | ownerPresent _ _ hne _ =>
            exact hne hreached.symm
      have hsafeErased :
          ConcreteRuntimeValueSafe (storeBefore.erase ref.location) value :=
        ConcreteRuntimeValueSafe.erase_of_not_reaches hsafe hnotErased
      exact ih hsafeErased (by
        intro reached hreachErased
        have hreachStore :
            ConcreteRuntimeValueReaches storeBefore value reached :=
          ConcreteRuntimeValueReaches.erase_to_store hreachErased
        have havoid := havoids reached hreachStore
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

/-- Every concrete borrow footprint inside a concrete-safe value points at an
allocated location. -/
theorem ConcreteRuntimeValueSafe.borrow_allocated {store : ProgramStore}
    {value : PartialValue} {leaf : Location} :
    ConcreteRuntimeValueSafe store value →
    RuntimeValueBorrow store value leaf →
    ∃ slot, store.slotAt leaf = some slot := by
  intro hsafe hborrow
  induction hsafe generalizing leaf with
  | unit =>
      cases hborrow
  | int =>
      cases hborrow
  | bool =>
      cases hborrow
  | undef =>
      cases hborrow
  | @borrow location slot hslot =>
      cases hborrow
      exact ⟨slot, hslot⟩
  | @box location slot hslot _hsafe ih =>
      cases hborrow with
      | box hslot' hinner =>
          have hslotEq : slot = _ := Option.some.inj (hslot.symm.trans hslot')
          subst hslotEq
          exact ih hinner

/-- A concrete borrow footprint inside a statically valid value came from one
of that value's static borrow targets.  The target list may be a join
over-approximation, but the witness target is the one whose `store.loc`
actually produced the stored runtime location. -/
theorem RuntimeValueBorrow.static_witness_of_validPartialValue
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy}
    {leaf : Location} :
    ValidPartialValue store value ty →
    RuntimeValueBorrow store value leaf →
      ∃ mutable targets target,
        PartialTyContains ty (.borrow mutable targets) ∧
          target ∈ targets ∧
            store.loc target = some leaf := by
  intro hvalid hborrow
  induction hvalid generalizing leaf with
  | unit =>
      cases hborrow
  | int =>
      cases hborrow
  | bool =>
      cases hborrow
  | undef =>
      cases hborrow
  | @borrow location mutable targets target hmem hloc =>
      cases hborrow
      exact ⟨mutable, targets, target, PartialTyContains.here, hmem, hloc⟩
  | @box location slot inner hslot _hinner ih =>
      cases hborrow with
      | box hslot' hinnerBorrow =>
          have hslotEq : slot = _ := Option.some.inj (hslot.symm.trans hslot')
          subst hslotEq
          rcases ih hinnerBorrow with
            ⟨mutable, targets, target, hcontains, hmem, hloc⟩
          exact ⟨mutable, targets, target, PartialTyContains.box hcontains,
            hmem, hloc⟩
  | @boxFull location slot innerTy hslot _hinner ih =>
      cases hborrow with
      | box hslot' hinnerBorrow =>
          have hslotEq : slot = _ := Option.some.inj (hslot.symm.trans hslot')
          subst hslotEq
          rcases ih hinnerBorrow with
            ⟨mutable, targets, target, hcontains, hmem, hloc⟩
          exact ⟨mutable, targets, target, PartialTyContains.tyBox hcontains,
            hmem, hloc⟩

/-- Full-value wrapper for
`RuntimeValueBorrow.static_witness_of_validPartialValue`. -/
theorem RuntimeValueBorrow.static_witness_of_validValue
    {store : ProgramStore} {value : Value} {ty : Ty}
    {leaf : Location} :
    ValidValue store value ty →
    RuntimeValueBorrow store (.value value) leaf →
      ∃ mutable targets target,
        PartialTyContains (.ty ty) (.borrow mutable targets) ∧
          target ∈ targets ∧
            store.loc target = some leaf :=
  RuntimeValueBorrow.static_witness_of_validPartialValue

/-- Static value validity implies concrete runtime value safety when every
runtime location selected by a borrow-validity witness is allocated.  The
allocation premise is deliberately about the concrete resolved location, not the
static target expression. -/
theorem ConcreteRuntimeValueSafe.of_validPartialValue {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy}
    (hallocated :
      ∀ {target : LVal} {location : Location},
        store.loc target = some location →
          ∃ slot, store.slotAt location = some slot) :
    ValidPartialValue store value ty →
      ConcreteRuntimeValueSafe store value := by
  intro hvalid
  induction hvalid with
  | unit =>
      exact ConcreteRuntimeValueSafe.unit
  | int =>
      exact ConcreteRuntimeValueSafe.int
  | bool =>
      exact ConcreteRuntimeValueSafe.bool
  | undef =>
      exact ConcreteRuntimeValueSafe.undef
  | borrow _hmem hloc =>
      rcases hallocated hloc with ⟨slot, hslot⟩
      exact ConcreteRuntimeValueSafe.borrow hslot
  | box hslot _hinner ih =>
      exact ConcreteRuntimeValueSafe.box hslot ih
  | boxFull hslot _hinner ih =>
      exact ConcreteRuntimeValueSafe.box hslot ih

/-- A static valid partial value whose contained borrow targets satisfy the
well-formed-environment invariant is concrete-runtime safe.  In the borrow case
we use only the target selected by the validity proof, then forget the target
expression and keep the allocated concrete location. -/
theorem ConcreteRuntimeValueSafe.of_validPartialValue_borrowsWellFormed
    {store : ProgramStore} {env : Env} {current valueLifetime : Lifetime}
    {value : PartialValue} {ty : PartialTy} :
    WellFormedEnv env current →
    store ∼ₛ env →
    PartialTyBorrowsWellFormedInSlot env valueLifetime ty →
    ValidPartialValue store value ty →
      ConcreteRuntimeValueSafe store value := by
  intro hwellEnv hsafe hborrows hvalid
  induction hvalid generalizing valueLifetime with
  | unit =>
      exact ConcreteRuntimeValueSafe.unit
  | int =>
      exact ConcreteRuntimeValueSafe.int
  | bool =>
      exact ConcreteRuntimeValueSafe.bool
  | undef =>
      exact ConcreteRuntimeValueSafe.undef
  | @borrow location mutable targets target hmem hloc =>
      rcases hborrows PartialTyContains.here target hmem with
        ⟨targetTy, targetLifetime, htarget, _houtlives, _hbase⟩
      have htargetAbs :
          LValLocationAbstraction store target (.ty targetTy) :=
        lvalTyping_defined_location hwellEnv hsafe htarget
      rcases htargetAbs with
        ⟨targetLocation, targetSlot, htargetLoc, htargetSlot, _htargetValid⟩
      have hlocationEq : location = targetLocation :=
        Option.some.inj (hloc.symm.trans htargetLoc)
      subst hlocationEq
      exact ConcreteRuntimeValueSafe.borrow htargetSlot
  | box hslot _hinner ih =>
      exact ConcreteRuntimeValueSafe.box hslot
        (ih (PartialTyBorrowsWellFormedInSlot.box_inv hborrows))
  | @boxFull location slot innerTy hslot _hinner ih =>
      have hinnerBorrows :
          PartialTyBorrowsWellFormedInSlot env valueLifetime (.ty innerTy) := by
        intro mutable targets hcontains
        exact hborrows (PartialTyContains.tyBox hcontains)
      exact ConcreteRuntimeValueSafe.box hslot (ih hinnerBorrows)

/-- Full-value wrapper for
`ConcreteRuntimeValueSafe.of_validPartialValue_borrowsWellFormed`. -/
theorem ConcreteRuntimeValueSafe.of_validValue_wellFormed
    {store : ProgramStore} {env : Env} {current valueLifetime : Lifetime}
    {value : Value} {ty : Ty} :
    WellFormedEnv env current →
    store ∼ₛ env →
    WellFormedTy env ty valueLifetime →
    ValidValue store value ty →
      ConcreteRuntimeValueSafe store (.value value) := by
  intro hwellEnv hsafe hwellTy hvalid
  exact ConcreteRuntimeValueSafe.of_validPartialValue_borrowsWellFormed
    hwellEnv hsafe
    (PartialTyBorrowsWellFormedInSlot.of_wellFormedTy hwellTy)
    hvalid

/-- Concrete value safety for every allocated store slot. -/
def ConcreteRuntimeStoreSafe (store : ProgramStore) : Prop :=
  ∀ location slot,
    store.slotAt location = some slot →
      ConcreteRuntimeValueSafe store slot.value

/-- Concrete safety for the live roots described by an environment.

This is deliberately root-reachable rather than all-slot: `S ∼ Γ` abstracts
variable roots and `ConcreteRuntimeValueSafe` recursively follows owned boxes
from those roots.  It does not make claims about unreachable abstract heap
cells, which the paper's safe-abstraction relation intentionally ignores. -/
def ConcreteRuntimeRootsSafe (store : ProgramStore) (env : Env) : Prop :=
  ∀ x envSlot,
    env.slotAt x = some envSlot →
      ∃ value,
        store.slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } ∧
        ConcreteRuntimeValueSafe store value

/-- Safe abstraction plus the slot-local borrow invariant gives concrete
runtime safety for every live root.  The proof forgets static target-list
alternatives after using well-formedness to show the selected concrete target is
allocated. -/
theorem ConcreteRuntimeRootsSafe.of_safeAbstraction_wellFormed
    {store : ProgramStore} {env : Env} {current : Lifetime} :
    WellFormedEnv env current →
    store ∼ₛ env →
      ConcreteRuntimeRootsSafe store env := by
  intro hwellEnv hsafe x envSlot hslot
  rcases hsafe.2 x envSlot hslot with ⟨value, hstore, hvalid⟩
  have hborrows :
      PartialTyBorrowsWellFormedInSlot env envSlot.lifetime envSlot.ty := by
    intro mutable targets hcontains
    exact hwellEnv.1 x envSlot mutable targets hslot
      ⟨envSlot, hslot, hcontains⟩
  exact ⟨value, hstore,
    ConcreteRuntimeValueSafe.of_validPartialValue_borrowsWellFormed
      hwellEnv hsafe hborrows hvalid⟩

/-- Root-reachable concrete runtime safety transports across a same-shape
environment strengthening.  The conclusion is type-list independent: only root
lifetimes are needed to look up the same store value.  This is the concrete
runtime reason joins cannot create dangling references. -/
theorem ConcreteRuntimeRootsSafe.of_sameShapeStrengthening
    {store : ProgramStore} {envFine envCoarse : Env}
    (hmap : EnvSameShapeStrengthening envFine envCoarse)
    (hroots : ConcreteRuntimeRootsSafe store envFine) :
      ConcreteRuntimeRootsSafe store envCoarse := by
  intro x coarseSlot hcoarse
  rcases hmap.1 x coarseSlot hcoarse with
    ⟨fineSlot, hfine, hlifetime, _hstrength, _hshape⟩
  rcases hroots x fineSlot hfine with ⟨value, hstore, hsafeValue⟩
  exact ⟨value, by simpa [hlifetime] using hstore, hsafeValue⟩

/-- Root-reachable concrete runtime safety only depends on which variable roots
exist and on their lifetimes.  The static type component of a slot can be
rewritten, joined, or widened without changing the concrete safety claim. -/
theorem ConcreteRuntimeRootsSafe.of_lifetimesPreservedSurvive
    {store : ProgramStore} {env result : Env}
    (hpreserved : EnvLifetimesPreserved env result)
    (_hsurvive : EnvLifetimesSurvive env result)
    (hroots : ConcreteRuntimeRootsSafe store env) :
      ConcreteRuntimeRootsSafe store result := by
  intro x resultSlot hresult
  rcases hpreserved x resultSlot hresult with
    ⟨sourceSlot, hsource, hlifetime⟩
  rcases hroots x sourceSlot hsource with ⟨value, hstore, hsafeValue⟩
  exact ⟨value, by simpa [hlifetime] using hstore, hsafeValue⟩

/-- Type-level environment writes do not affect concrete runtime root safety
when the store is unchanged.  `EnvWrite` may rewrite slot types or widen joined
borrow target lists, but it preserves the variable root set and lifetimes. -/
theorem ConcreteRuntimeRootsSafe.of_envWrite
    {store : ProgramStore} {env result : Env}
    {rank : Nat} {lv : LVal} {rhsTy : Ty}
    (hwrite : EnvWrite rank env lv rhsTy result)
    (hroots : ConcreteRuntimeRootsSafe store env) :
      ConcreteRuntimeRootsSafe store result :=
  ConcreteRuntimeRootsSafe.of_lifetimesPreservedSurvive
    (EnvWrite.lifetimesPreserved hwrite)
    (EnvWrite.lifetimesSurvive hwrite)
    hroots

/-- Recursive drops preserve concrete safety for all live roots when they avoid
each root slot and every concrete location reached from the root value. -/
theorem ConcreteRuntimeRootsSafe.drops_of_avoids_reaches
    {store store' : ProgramStore} {env : Env} {values : List PartialValue} :
    Drops store values store' →
    ConcreteRuntimeRootsSafe store env →
    (∀ x envSlot value,
      env.slotAt x = some envSlot →
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } →
      DropsAvoids store values (VariableProjection x) ∧
        ∀ reached,
          ConcreteRuntimeValueReaches store value reached →
            DropsAvoids store values reached) →
      ConcreteRuntimeRootsSafe store' env := by
  intro hdrops hroots havoids x envSlot henvSlot
  rcases hroots x envSlot henvSlot with ⟨value, hstoreSlot, hsafeValue⟩
  rcases havoids x envSlot value henvSlot hstoreSlot with
    ⟨havoidRoot, havoidReached⟩
  exact ⟨value,
    dropsAvoids_slotAt_preserved hdrops havoidRoot hstoreSlot,
    ConcreteRuntimeValueSafe.drops_of_avoids_reaches
      hdrops hsafeValue havoidReached⟩

/-- Declaring a fresh variable preserves concrete safety of an existing value:
old concrete references still point at the same allocated locations, and old
owned boxes still recurse through the same slots. -/
theorem ConcreteRuntimeValueSafe.declare {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {newValue : Value} {value : PartialValue} :
    store.fresh (.var x) →
    ConcreteRuntimeValueSafe store value →
      ConcreteRuntimeValueSafe (store.declare x lifetime newValue) value := by
  intro hfresh hsafe
  induction hsafe with
  | unit =>
      exact ConcreteRuntimeValueSafe.unit
  | int =>
      exact ConcreteRuntimeValueSafe.int
  | bool =>
      exact ConcreteRuntimeValueSafe.bool
  | undef =>
      exact ConcreteRuntimeValueSafe.undef
  | borrow hslot =>
      exact ConcreteRuntimeValueSafe.borrow (slotAt_declare_of_slotAt hfresh hslot)
  | box hslot _hsafe ih =>
      exact ConcreteRuntimeValueSafe.box (slotAt_declare_of_slotAt hfresh hslot) ih

/-- Concrete store safety is preserved by declaring a fresh root, provided the
newly installed value is concrete-safe in the post-declare store. -/
theorem ConcreteRuntimeStoreSafe.declare {store : ProgramStore} {x : Name}
    {lifetime : Lifetime} {value : Value} :
    store.fresh (.var x) →
    ConcreteRuntimeStoreSafe store →
    ConcreteRuntimeValueSafe (store.declare x lifetime value) (.value value) →
      ConcreteRuntimeStoreSafe (store.declare x lifetime value) := by
  intro hfresh hstoreSafe hvalueSafe location slot hslot
  by_cases hlocation : location = .var x
  · subst hlocation
    have hslotEq :
        slot = { value := .value value, lifetime := lifetime } := by
      simpa [ProgramStore.declare, ProgramStore.update] using hslot.symm
    subst hslotEq
    exact hvalueSafe
  · have hslotOld : store.slotAt location = some slot := by
      simpa [ProgramStore.declare, ProgramStore.update, hlocation] using hslot
    exact ConcreteRuntimeValueSafe.declare hfresh (hstoreSafe location slot hslotOld)

/-- Declaration preserves concrete store safety when the RHS value is statically
valid at a well-formed result type.  This is the concrete-runtime counterpart of
the existing `safeAbstraction_declare` frame. -/
theorem ConcreteRuntimeStoreSafe.declare_of_validValue_wellFormed
    {store : ProgramStore} {env : Env} {current valueLifetime lifetime : Lifetime}
    {x : Name} {value : Value} {ty : Ty} :
    store.fresh (.var x) →
    ConcreteRuntimeStoreSafe store →
    WellFormedEnv env current →
    store ∼ₛ env →
    WellFormedTy env ty valueLifetime →
    ValidValue store value ty →
      ConcreteRuntimeStoreSafe (store.declare x lifetime value) := by
  intro hfresh hstoreSafe hwellEnv hsafe hwellTy hvalidValue
  have hvalueSafe :
      ConcreteRuntimeValueSafe (store.declare x lifetime value) (.value value) :=
    ConcreteRuntimeValueSafe.declare hfresh
      (ConcreteRuntimeValueSafe.of_validValue_wellFormed
        hwellEnv hsafe hwellTy hvalidValue)
  exact ConcreteRuntimeStoreSafe.declare hfresh hstoreSafe hvalueSafe

/-- Declaring a fresh root preserves concrete runtime safety for every live
environment root and installs the new value at the declared variable. -/
theorem ConcreteRuntimeRootsSafe.declare {store : ProgramStore} {env : Env}
    {x : Name} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    store.fresh (.var x) →
    ConcreteRuntimeRootsSafe store env →
    ConcreteRuntimeValueSafe (store.declare x lifetime value) (.value value) →
      ConcreteRuntimeRootsSafe (store.declare x lifetime value)
        (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hfresh hroots hnewSafe y envSlot hslot
  by_cases hyx : y = x
  · subst hyx
    have henvSlot :
        envSlot = { ty := .ty ty, lifetime := lifetime } := by
      simpa [Env.update] using hslot.symm
    subst henvSlot
    exact ⟨.value value, by
        simp [ProgramStore.declare, ProgramStore.update, VariableProjection],
      hnewSafe⟩
  · have holdSlot : env.slotAt y = some envSlot := by
      simpa [Env.update, hyx] using hslot
    rcases hroots y envSlot holdSlot with ⟨oldValue, hstoreSlot, holdSafe⟩
    exact ⟨oldValue, slotAt_declare_of_slotAt hfresh hstoreSlot,
      ConcreteRuntimeValueSafe.declare hfresh holdSafe⟩

/-- Declaration preserves root-reachable concrete safety when the RHS value is
statically valid at a well-formed type. -/
theorem ConcreteRuntimeRootsSafe.declare_of_validValue_wellFormed
    {store : ProgramStore} {env : Env} {current valueLifetime lifetime : Lifetime}
    {x : Name} {value : Value} {ty : Ty} :
    store.fresh (.var x) →
    ConcreteRuntimeRootsSafe store env →
    WellFormedEnv env current →
    store ∼ₛ env →
    WellFormedTy env ty valueLifetime →
    ValidValue store value ty →
      ConcreteRuntimeRootsSafe (store.declare x lifetime value)
        (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  intro hfresh hroots hwellEnv hsafe hwellTy hvalidValue
  have hvalueSafe :
      ConcreteRuntimeValueSafe (store.declare x lifetime value) (.value value) :=
    ConcreteRuntimeValueSafe.declare hfresh
      (ConcreteRuntimeValueSafe.of_validValue_wellFormed
        hwellEnv hsafe hwellTy hvalidValue)
  exact ConcreteRuntimeRootsSafe.declare hfresh hroots hvalueSafe

/-- Concrete terminal runtime safety, stated without inspecting static borrow
target expressions.  This is intentionally weaker than `TerminalStateSafe`'s
`ValidValue` component and is the target shape for proving safety through joins. -/
def ConcreteTerminalRuntimeSafe (store : ProgramStore) (value : Value) : Prop :=
  ValidRuntimeState store (.val value) ∧
    ConcreteRuntimeStoreSafe store ∧
      ConcreteRuntimeValueSafe store (.value value)

/-- Concrete terminal safety for the live root set of a terminal environment,
plus the terminal value.  Unlike `TerminalStateSafe`, this does not validate
stored references by re-reading static target expressions. -/
def ConcreteTerminalRuntimeRootsSafe (store : ProgramStore)
    (value : Value) (env : Env) : Prop :=
  ValidRuntimeState store (.val value) ∧
    ConcreteRuntimeRootsSafe store env ∧
      ConcreteRuntimeValueSafe store (.value value)

/-- Static terminal safety entails concrete root-reachable runtime safety when
the terminal value type is well formed. -/
theorem TerminalStateSafe.concreteRuntimeRoots
    {store : ProgramStore} {value : Value} {env : Env} {ty : Ty}
    {current valueLifetime : Lifetime} :
    WellFormedEnv env current →
    WellFormedTy env ty valueLifetime →
    TerminalStateSafe store value env ty →
      ConcreteTerminalRuntimeRootsSafe store value env := by
  intro hwellEnv hwellTy hterminal
  rcases hterminal with ⟨hvalidRuntime, hsafe, hvalidValue⟩
  exact ⟨hvalidRuntime,
    ConcreteRuntimeRootsSafe.of_safeAbstraction_wellFormed hwellEnv hsafe,
    ConcreteRuntimeValueSafe.of_validValue_wellFormed
      hwellEnv hsafe hwellTy hvalidValue⟩

/-- Concrete terminal root safety is join-stable under same-shape
strengthening.  The store and final value are unchanged; only the root-domain
view is transported through lifetime-preserving slot correspondence. -/
theorem ConcreteTerminalRuntimeRootsSafe.of_sameShapeStrengthening
    {store : ProgramStore} {value : Value}
    {envFine envCoarse : Env}
    (hmap : EnvSameShapeStrengthening envFine envCoarse)
    (hterminal : ConcreteTerminalRuntimeRootsSafe store value envFine) :
      ConcreteTerminalRuntimeRootsSafe store value envCoarse := by
  rcases hterminal with ⟨hvalidRuntime, hroots, hvalue⟩
  exact ⟨hvalidRuntime,
    ConcreteRuntimeRootsSafe.of_sameShapeStrengthening hmap hroots,
    hvalue⟩

/-- Concrete terminal root safety transports across an environment rewrite that
preserves the result roots and their lifetimes.  The terminal value and store
are unchanged, and static slot types are ignored by the concrete claim. -/
theorem ConcreteTerminalRuntimeRootsSafe.of_lifetimesPreservedSurvive
    {store : ProgramStore} {value : Value}
    {env result : Env}
    (hpreserved : EnvLifetimesPreserved env result)
    (hsurvive : EnvLifetimesSurvive env result)
    (hterminal : ConcreteTerminalRuntimeRootsSafe store value env) :
      ConcreteTerminalRuntimeRootsSafe store value result := by
  rcases hterminal with ⟨hvalidRuntime, hroots, hvalue⟩
  exact ⟨hvalidRuntime,
    ConcreteRuntimeRootsSafe.of_lifetimesPreservedSurvive
      hpreserved hsurvive hroots,
    hvalue⟩

/-- Concrete terminal runtime safety is invariant under an `EnvWrite` when the
store and terminal value are unchanged. -/
theorem ConcreteTerminalRuntimeRootsSafe.of_envWrite
    {store : ProgramStore} {value : Value}
    {env result : Env} {rank : Nat} {lv : LVal} {rhsTy : Ty}
    (hwrite : EnvWrite rank env lv rhsTy result)
    (hterminal : ConcreteTerminalRuntimeRootsSafe store value env) :
      ConcreteTerminalRuntimeRootsSafe store value result := by
  rcases hterminal with ⟨hvalidRuntime, hroots, hvalue⟩
  exact ⟨hvalidRuntime,
    ConcreteRuntimeRootsSafe.of_envWrite hwrite hroots,
    hvalue⟩

/-- Concrete terminal root safety transports through a type-level join without
any runtime target-list obligation.

The join can widen static borrow target lists, but the store and terminal value
are unchanged.  Concrete root safety only follows variable roots and the
locations stored in runtime references, so same-shape/lifetime correspondence is
the only join fact it needs. -/
theorem ConcreteTerminalRuntimeRootsSafe.strengthen_join
    {store : ProgramStore} {value : Value}
    {branchEnv joinEnv : Env}
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hterminal : ConcreteTerminalRuntimeRootsSafe store value branchEnv) :
      ConcreteTerminalRuntimeRootsSafe store value joinEnv :=
  ConcreteTerminalRuntimeRootsSafe.of_sameShapeStrengthening hmap hterminal

/-- Concrete terminal root safety is unchanged by a value-tail multistep. -/
theorem ConcreteTerminalRuntimeRootsSafe.value_tail
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value finalValue : Value} :
    ConcreteTerminalRuntimeRootsSafe store value env →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
      ConcreteTerminalRuntimeRootsSafe finalStore finalValue env := by
  intro hterminal htail
  rcases multistep_value_inv htail with ⟨hstore, hterm⟩
  injection hterm with hvalue
  subst hstore
  subst hvalue
  exact hterminal

/-- Terminal safety packaged with concrete root-reachable runtime safety.

This is the target shape for preservation facts that must survive joins without
revalidating widened static borrow target lists.  The first component keeps the
paper-facing terminal facts; the second component records the concrete runtime
claim that every live environment root and the terminal value are safe by
following actual stored references only. -/
def TerminalStateSafeWithConcreteRoots (store : ProgramStore)
    (value : Value) (env : Env) (ty : Ty) : Prop :=
  TerminalStateSafe store value env ty ∧
    ConcreteTerminalRuntimeRootsSafe store value env

/-- Value-tail composition for terminal safety with concrete roots. -/
theorem TerminalStateSafeWithConcreteRoots.value_tail
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    TerminalStateSafeWithConcreteRoots store value env ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
      TerminalStateSafeWithConcreteRoots finalStore finalValue env ty := by
  intro hterminal htail
  exact ⟨preservation_value_tail_runtime hterminal.1 htail,
    hterminal.2.value_tail htail⟩

/-- Terminal safety with concrete roots transports through a join.  The static
terminal component uses the existing same-shape strengthening proof; the
concrete roots component only needs the same root/lifetime map and is independent
of joined target-list alternatives. -/
theorem TerminalStateSafeWithConcreteRoots.strengthen_join
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithConcreteRoots finalStore finalValue
      branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithConcreteRoots finalStore finalValue joinEnv joinTy := by
  rcases hterminal with ⟨hterminalSafe, hconcreteRoots⟩
  rcases TerminalStateSafe.strengthen_join hcontained hcoherent hlinear
      hpreserved hmap hstrengthens hwellBranch hterminalSafe with
    ⟨hwellJoin, hsafeJoin⟩
  exact ⟨hwellJoin, hsafeJoin,
    ConcreteTerminalRuntimeRootsSafe.of_sameShapeStrengthening hmap hconcreteRoots⟩

/-- Concrete store safety is independent of the typing environment; this is the
formal reason target-list joins cannot manufacture runtime dangling references. -/
theorem ConcreteRuntimeStoreSafe.env_independent {store : ProgramStore}
    (_envFine _envCoarse : Env) :
    ConcreteRuntimeStoreSafe store →
      ConcreteRuntimeStoreSafe store :=
  id

/-- A stored value carries a concrete borrow that would be invalidated by
rewriting `root`: either the borrow points directly at `root`, or it points into
the ownership subtree rooted at `root`. -/
def RuntimeValueBorrowInvalidatedBy (store : ProgramStore)
    (value : PartialValue) (root : Location) : Prop :=
  ∃ leaf,
    RuntimeValueBorrow store value leaf ∧
      (leaf = root ∨ ProgramStore.OwnsTransitively store root leaf)

/-- A stored value carries a concrete borrow into the ownership subtree rooted at
`root`.  This is the concrete danger for replacing an owning value and then
dropping the old contents: references to `root` itself remain allocated after the
write, while references below `root` may be erased by the old-value drop. -/
def RuntimeValueBorrowInvalidatedBelow (store : ProgramStore)
    (value : PartialValue) (root : Location) : Prop :=
  ∃ leaf,
    RuntimeValueBorrow store value leaf ∧
      ProgramStore.OwnsTransitively store root leaf

/-- If a concrete value has no borrow into the subtree below `root`, then any
location it reaches below `root` must be reached through ownership carried by
the value itself. -/
theorem ConcreteRuntimeValueReaches.owned_of_below_not_invalidated
    {store : ProgramStore} {value : PartialValue} {root reached : Location} :
    ¬ RuntimeValueBorrowInvalidatedBelow store value root →
    ConcreteRuntimeValueReaches store value reached →
    ProgramStore.OwnsTransitively store root reached →
      ∃ owner,
        owner ∈ partialValueOwningLocations value ∧
          (owner = reached ∨
            ProgramStore.OwnsTransitively store owner reached) := by
  intro hnotInvalidated hreach hbelow
  rcases ConcreteRuntimeValueReaches.borrow_or_owned hreach with hborrow | howned
  · exact False.elim (hnotInvalidated ⟨reached, hborrow, hbelow⟩)
  · exact howned

/-- In a valid ownership forest, a concrete reach below `root` from a value
with no below-root borrow must come from an owner carried by the value whose
ownership path overlaps `root`. -/
theorem ConcreteRuntimeValueReaches.owner_overlaps_of_below_not_invalidated
    {store : ProgramStore} {value : PartialValue} {root reached : Location} :
    ValidStore store →
    ¬ RuntimeValueBorrowInvalidatedBelow store value root →
    ConcreteRuntimeValueReaches store value reached →
    ProgramStore.OwnsTransitively store root reached →
      ∃ owner,
        owner ∈ partialValueOwningLocations value ∧
          (root = owner ∨
            ProgramStore.OwnsTransitively store root owner ∨
              ProgramStore.OwnsTransitively store owner root) := by
  intro hvalid hnotInvalidated hreach hbelow
  rcases ConcreteRuntimeValueReaches.owned_of_below_not_invalidated
      hnotInvalidated hreach hbelow with
    ⟨owner, hownerMem, hownerRel⟩
  refine ⟨owner, hownerMem, ?_⟩
  rcases hownerRel with hownerEq | hownerPath
  · subst hownerEq
    exact Or.inr (Or.inl hbelow)
  · rcases ProgramStore.OwnsTransitively.same_target_comparable
      hvalid hbelow hownerPath with hrootEq | hpaths
    · exact Or.inl hrootEq
    · exact Or.inr hpaths

/-- A concrete invalidation footprint in a statically valid value is witnessed
by one of the value's static borrow targets, plus the concrete relation that
would make rewriting `root` unsafe. -/
theorem RuntimeValueBorrowInvalidatedBy.static_witness_of_validPartialValue
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy}
    {root : Location} :
    ValidPartialValue store value ty →
    RuntimeValueBorrowInvalidatedBy store value root →
      ∃ mutable targets target leaf,
        PartialTyContains ty (.borrow mutable targets) ∧
          target ∈ targets ∧
            store.loc target = some leaf ∧
              (leaf = root ∨ ProgramStore.OwnsTransitively store root leaf) := by
  intro hvalid hinvalid
  rcases hinvalid with ⟨leaf, hborrow, hrel⟩
  rcases RuntimeValueBorrow.static_witness_of_validPartialValue
      hvalid hborrow with
    ⟨mutable, targets, target, hcontains, hmem, hloc⟩
  exact ⟨mutable, targets, target, leaf, hcontains, hmem, hloc, hrel⟩

/-- Full-value wrapper for
`RuntimeValueBorrowInvalidatedBy.static_witness_of_validPartialValue`. -/
theorem RuntimeValueBorrowInvalidatedBy.static_witness_of_validValue
    {store : ProgramStore} {value : Value} {ty : Ty} {root : Location} :
    ValidValue store value ty →
    RuntimeValueBorrowInvalidatedBy store (.value value) root →
      ∃ mutable targets target leaf,
        PartialTyContains (.ty ty) (.borrow mutable targets) ∧
          target ∈ targets ∧
            store.loc target = some leaf ∧
              (leaf = root ∨ ProgramStore.OwnsTransitively store root leaf) :=
  RuntimeValueBorrowInvalidatedBy.static_witness_of_validPartialValue

/-- A concrete below-root invalidation footprint in a statically valid value is
witnessed by one of the value's static borrow targets. -/
theorem RuntimeValueBorrowInvalidatedBelow.static_witness_of_validPartialValue
    {store : ProgramStore} {value : PartialValue} {ty : PartialTy}
    {root : Location} :
    ValidPartialValue store value ty →
    RuntimeValueBorrowInvalidatedBelow store value root →
      ∃ mutable targets target leaf,
        PartialTyContains ty (.borrow mutable targets) ∧
          target ∈ targets ∧
            store.loc target = some leaf ∧
              ProgramStore.OwnsTransitively store root leaf := by
  intro hvalid hinvalid
  rcases hinvalid with ⟨leaf, hborrow, hrel⟩
  rcases RuntimeValueBorrow.static_witness_of_validPartialValue
      hvalid hborrow with
    ⟨mutable, targets, target, hcontains, hmem, hloc⟩
  exact ⟨mutable, targets, target, leaf, hcontains, hmem, hloc, hrel⟩

/-- Full-value wrapper for
`RuntimeValueBorrowInvalidatedBelow.static_witness_of_validPartialValue`. -/
theorem RuntimeValueBorrowInvalidatedBelow.static_witness_of_validValue
    {store : ProgramStore} {value : Value} {ty : Ty} {root : Location} :
    ValidValue store value ty →
    RuntimeValueBorrowInvalidatedBelow store (.value value) root →
      ∃ mutable targets target leaf,
        PartialTyContains (.ty ty) (.borrow mutable targets) ∧
          target ∈ targets ∧
            store.loc target = some leaf ∧
              ProgramStore.OwnsTransitively store root leaf :=
  RuntimeValueBorrowInvalidatedBelow.static_witness_of_validPartialValue

/-- Concrete store-only kill: variable `z`'s stored value contains no runtime
borrow into the ownership subtree below `leaf`.

A direct non-owning reference to `leaf` remains allocated after rewriting
`leaf`; only references below `leaf` can dangle when the old owned contents are
dropped.  This predicate never asks whether some unrelated lvalue expression can
be made to resolve through `leaf`. -/
def StoreConcreteBorrowKill (store : ProgramStore) (leaf : Location)
    (z : Name) : Prop :=
  ∀ value lifetime,
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := lifetime } →
    ¬ RuntimeValueBorrowInvalidatedBelow store value leaf

/-- Erasing a store slot cannot create a concrete runtime borrow footprint. -/
theorem RuntimeValueBorrow.erase_to_store {store : ProgramStore}
    {erased : Location} {value : PartialValue} {leaf : Location} :
    RuntimeValueBorrow (store.erase erased) value leaf →
    RuntimeValueBorrow store value leaf := by
  intro hborrow
  induction hborrow with
  | borrow =>
      exact RuntimeValueBorrow.borrow
  | box hslot _hinner ih =>
      exact RuntimeValueBorrow.box (RuntimeFrame.slotAt_of_erase_slotAt hslot) ih

/-- Updating a slot to `undef` cannot create a concrete runtime borrow
footprint inside an existing value. -/
theorem RuntimeValueBorrow.update_undef_to_store {store : ProgramStore}
    {updated : Location} {updatedLifetime : Lifetime}
    {value : PartialValue} {leaf : Location} :
    RuntimeValueBorrow
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      value leaf →
    RuntimeValueBorrow store value leaf := by
  intro hborrow
  induction hborrow with
  | borrow =>
      exact RuntimeValueBorrow.borrow
  | @box location slot leaf hslot _hinner ih =>
      by_cases hlocation : location = updated
      · subst hlocation
        simp [ProgramStore.update] at hslot
        cases hslot
        cases _hinner
      · exact RuntimeValueBorrow.box
          (by
            rw [← RuntimeFrame.ProgramStore.slotAt_update_ne hlocation]
            exact hslot)
          ih

/-- An ownership edge observed after an update either comes from the old store or
starts at the updated slot. -/
theorem ProgramStore.OwnsAt.update_to_store_or_updated {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} {owned storage : Location} :
    ProgramStore.OwnsAt (store.update updated newSlot) owned storage →
    storage = updated ∨ ProgramStore.OwnsAt store owned storage := by
  intro howns
  by_cases hstorage : storage = updated
  · exact Or.inl hstorage
  · rcases howns with ⟨lifetime, hslot⟩
    exact Or.inr ⟨lifetime, by
      rw [← RuntimeFrame.ProgramStore.slotAt_update_ne hstorage]
      exact hslot⟩

/-- A transitive ownership path observed after an update either already existed
or the old store could reach the updated location. -/
theorem ProgramStore.OwnsTransitively.update_to_store_or_updated
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot}
    {root owned : Location} :
    root ≠ updated →
    ProgramStore.OwnsTransitively (store.update updated newSlot) root owned →
    ProgramStore.OwnsTransitively store root owned ∨
      ProgramStore.OwnsTransitively store root updated := by
  intro hroot hpath
  induction hpath with
  | direct howns =>
      rcases ProgramStore.OwnsAt.update_to_store_or_updated howns with
        hstorage | hownsOld
      · exact False.elim (hroot hstorage)
      · exact Or.inl (ProgramStore.OwnsTransitively.direct hownsOld)
  | @trans storage middle owned howns _htail ih =>
      rcases ProgramStore.OwnsAt.update_to_store_or_updated howns with
        hstorage | hownsOld
      · exact False.elim (hroot hstorage)
      · by_cases hmiddle : middle = updated
        · subst hmiddle
          exact Or.inr (ProgramStore.OwnsTransitively.direct hownsOld)
        · rcases ih hmiddle with htailOld | hmiddleUpdated
          · exact Or.inl (ProgramStore.OwnsTransitively.trans hownsOld htailOld)
          · exact Or.inr
              (ProgramStore.OwnsTransitively.trans hownsOld hmiddleUpdated)

/-- Updating a fresh location cannot create a transitive ownership path from an
old root distinct from the updated location. -/
theorem ProgramStore.OwnsTransitively.update_fresh_to_store
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot}
    {root owned : Location}
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh updated)
    (hroot : root ≠ updated) :
    ProgramStore.OwnsTransitively (store.update updated newSlot) root owned →
    ProgramStore.OwnsTransitively store root owned := by
  intro hpath
  rcases ProgramStore.OwnsTransitively.update_to_store_or_updated
      hroot hpath with hstored | hupdated
  · exact hstored
  · exact False.elim
      ((not_owns_of_fresh_of_storeOwnersAllocated hallocated hfresh)
        (ProgramStore.OwnsTransitively.to_owns hupdated))

/-- Updating a fresh location cannot create a concrete borrow footprint inside a
value already stored in an old slot. -/
theorem RuntimeValueBorrow.update_fresh_slot_to_store {store : ProgramStore}
    {updated : Location} {newSlot : StoreSlot} {slotLocation : Location}
    {value : PartialValue} {lifetime : Lifetime} {leaf : Location}
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh updated)
    (hslot :
      store.slotAt slotLocation = some { value := value, lifetime := lifetime }) :
    RuntimeValueBorrow (store.update updated newSlot) value leaf →
    RuntimeValueBorrow store value leaf := by
  intro hborrow
  induction hborrow generalizing slotLocation lifetime with
  | borrow =>
      exact RuntimeValueBorrow.borrow
  | @box location slot leaf hslotUpdated _hinner ih =>
      by_cases hlocation : location = updated
      · subst location
        have howns : ProgramStore.Owns store updated := by
          exact ⟨slotLocation, lifetime, by simpa [owningRef] using hslot⟩
        exact False.elim
          ((not_owns_of_fresh_of_storeOwnersAllocated hallocated hfresh)
            howns)
      · have hslotOld : store.slotAt location = some slot := by
          rw [← RuntimeFrame.ProgramStore.slotAt_update_ne hlocation]
          exact hslotUpdated
        exact RuntimeValueBorrow.box hslotOld (ih hslotOld)

/-- If a root owns a cell containing a non-owning reference, that reference is a
concrete runtime borrow carried by the root's stored value. -/
theorem RuntimeValueBorrow.of_ownsTransitively_borrowCell
    {store : ProgramStore} {root cell loc : Location}
    {rootSlot cellSlot : StoreSlot}
    (hallocated : StoreOwnersAllocated store)
    (hrootSlot : store.slotAt root = some rootSlot)
    (hpath : ProgramStore.OwnsTransitively store root cell)
    (hcellSlot : store.slotAt cell = some cellSlot)
    (hcellValue :
      cellSlot.value = .value (.ref { location := loc, owner := false })) :
    RuntimeValueBorrow store rootSlot.value loc := by
  induction hpath generalizing rootSlot with
  | @direct storage owned howns =>
      rcases howns with ⟨ownerLifetime, hownerSlot⟩
      have hrootValue :
          rootSlot.value = .value (owningRef owned) := by
        have hslotEq :
            rootSlot =
              { value := .value (owningRef owned), lifetime := ownerLifetime } :=
          Option.some.inj (hrootSlot.symm.trans hownerSlot)
        exact congrArg StoreSlot.value hslotEq
      rw [hrootValue]
      exact RuntimeValueBorrow.box hcellSlot (by
        rw [hcellValue]
        exact RuntimeValueBorrow.borrow)
  | @trans storage middle owned howns _htail ih =>
      rcases howns with ⟨ownerLifetime, hownerSlot⟩
      have hrootValue :
          rootSlot.value = .value (owningRef middle) := by
        have hslotEq :
            rootSlot =
              { value := .value (owningRef middle),
                lifetime := ownerLifetime } :=
          Option.some.inj (hrootSlot.symm.trans hownerSlot)
        exact congrArg StoreSlot.value hslotEq
      rcases hallocated middle ⟨storage, ownerLifetime, hownerSlot⟩ with
        ⟨middleSlot, hmiddleSlot⟩
      rw [hrootValue]
      exact RuntimeValueBorrow.box hmiddleSlot
        (ih hmiddleSlot hcellSlot)

/-- A selected target is a concrete borrow footprint of its selecting root's
stored value. -/
theorem RuntimeValueBorrow.of_selectedTarget {store : ProgramStore}
    {x : Name} {target : LVal} {rootSlot : StoreSlot}
    (hallocated : StoreOwnersAllocated store)
    (hrootSlot : store.slotAt (VariableProjection x) = some rootSlot)
    (hselected : SelectedTarget store x target) :
    ∃ loc,
      store.loc target = some loc ∧
        RuntimeValueBorrow store rootSlot.value loc := by
  rcases hselected with
    ⟨cell, cellSlot, loc, hprotected, hcellSlot, hcellValue, htargetLoc⟩
  refine ⟨loc, htargetLoc, ?_⟩
  rcases hprotected with hcellRoot | hpath
  · subst hcellRoot
    have hrootValue :
        rootSlot.value =
          .value (.ref { location := loc, owner := false }) := by
      have hslotEq : rootSlot = cellSlot :=
        Option.some.inj (hrootSlot.symm.trans hcellSlot)
      rw [hslotEq]
      exact hcellValue
    rw [hrootValue]
    exact RuntimeValueBorrow.borrow
  · exact RuntimeValueBorrow.of_ownsTransitively_borrowCell
      hallocated hrootSlot hpath hcellSlot hcellValue

/-- If a root's stored value carries a concrete borrow and a target lval
resolves to that borrow's concrete location, then the target is selected by that
root.  This is the converse direction needed to consume runtime-selected borrow
safety from a concrete invalidation witness. -/
theorem SelectedTarget.of_runtimeValueBorrowAt {store : ProgramStore}
    {root : Location} {rootValue : PartialValue} {rootLifetime : Lifetime}
    {target : LVal} {leaf : Location} :
    store.slotAt root =
      some { value := rootValue, lifetime := rootLifetime } →
    RuntimeValueBorrow store rootValue leaf →
    store.loc target = some leaf →
      ∃ cell cellSlot loc,
        (cell = root ∨ ProgramStore.OwnsTransitively store root cell) ∧
          store.slotAt cell = some cellSlot ∧
          cellSlot.value = .value (.ref { location := loc, owner := false }) ∧
          store.loc target = some loc := by
  intro hrootSlot hborrow htargetLoc
  revert root rootLifetime target hrootSlot htargetLoc
  induction hborrow with
  | borrow =>
      intro root rootLifetime target hrootSlot htargetLoc
      exact ⟨root, _, _, Or.inl rfl, hrootSlot, rfl, htargetLoc⟩
  | @box location slot leaf hslot hinner ih =>
      intro root rootLifetime target hrootSlot htargetLoc
      cases slot with
      | mk slotValue slotLifetime =>
          rcases ih hslot htargetLoc with
            ⟨cell, cellSlot, loc, hprotected, hcellSlot, hcellValue,
              htargetLoc'⟩
          have hownsAt : ProgramStore.OwnsAt store location root := by
            exact ⟨rootLifetime, by simpa [owningRef] using hrootSlot⟩
          have hrootOwnsLocation :
              ProgramStore.OwnsTransitively store root location :=
            ProgramStore.OwnsTransitively.direct hownsAt
          have hprotectedRoot :
              cell = root ∨ ProgramStore.OwnsTransitively store root cell := by
            rcases hprotected with hcellLocation | hpath
            · subst hcellLocation
              exact Or.inr hrootOwnsLocation
            · exact Or.inr
                (ProgramStore.OwnsTransitively.trans hownsAt hpath)
          exact ⟨cell, cellSlot, loc, hprotectedRoot, hcellSlot, hcellValue,
            htargetLoc'⟩

/-- Root-variable specialization of
`SelectedTarget.of_runtimeValueBorrowAt`. -/
theorem SelectedTarget.of_runtimeValueBorrow {store : ProgramStore}
    {x : Name} {rootSlot : StoreSlot} {target : LVal} {leaf : Location} :
    store.slotAt (VariableProjection x) = some rootSlot →
    RuntimeValueBorrow store rootSlot.value leaf →
    store.loc target = some leaf →
      SelectedTarget store x target := by
  intro hrootSlot hborrow htargetLoc
  cases rootSlot with
  | mk rootValue rootLifetime =>
      exact SelectedTarget.of_runtimeValueBorrowAt hrootSlot hborrow htargetLoc

/-- A concrete invalidation footprint in a valid root slot yields a static
borrow contained in that slot whose witnessed target is selected by the root at
runtime.  This converts the concrete runtime danger back into the
runtime-selected vocabulary used by the assignment frame. -/
theorem RuntimeValueBorrowInvalidatedBy.selectedTarget_of_validRoot
    {store : ProgramStore} {z : Name} {value : PartialValue}
    {lifetime : Lifetime} {ty : PartialTy} {root : Location} :
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := lifetime } →
    ValidPartialValue store value ty →
    RuntimeValueBorrowInvalidatedBy store value root →
      ∃ mutable targets target leaf,
        PartialTyContains ty (.borrow mutable targets) ∧
          target ∈ targets ∧
            SelectedTarget store z target ∧
              store.loc target = some leaf ∧
                (leaf = root ∨
                  ProgramStore.OwnsTransitively store root leaf) := by
  intro hslot hvalid hinvalid
  rcases hinvalid with ⟨leaf, hborrow, hrel⟩
  rcases RuntimeValueBorrow.static_witness_of_validPartialValue
      hvalid hborrow with
    ⟨mutable, targets, target, hcontains, hmem, hloc⟩
  have hselected : SelectedTarget store z target :=
    SelectedTarget.of_runtimeValueBorrow hslot hborrow hloc
  exact ⟨mutable, targets, target, leaf, hcontains, hmem, hselected,
    hloc, hrel⟩

/-- Below-root specialization of
`RuntimeValueBorrowInvalidatedBy.selectedTarget_of_validRoot`.

This is the concrete assignment/drop witness: if a root slot contains a runtime
borrow into the old ownership subtree of the written location, then that borrow
comes from a selected static target of the root. -/
theorem RuntimeValueBorrowInvalidatedBelow.selectedTarget_of_validRoot
    {store : ProgramStore} {z : Name} {value : PartialValue}
    {lifetime : Lifetime} {ty : PartialTy} {root : Location} :
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := lifetime } →
    ValidPartialValue store value ty →
    RuntimeValueBorrowInvalidatedBelow store value root →
      ∃ mutable targets target leaf,
        PartialTyContains ty (.borrow mutable targets) ∧
          target ∈ targets ∧
            SelectedTarget store z target ∧
              store.loc target = some leaf ∧
                ProgramStore.OwnsTransitively store root leaf := by
  intro hslot hvalid hinvalid
  rcases hinvalid with ⟨leaf, hborrow, hrel⟩
  rcases RuntimeValueBorrow.static_witness_of_validPartialValue
      hvalid hborrow with
    ⟨mutable, targets, target, hcontains, hmem, hloc⟩
  have hselected : SelectedTarget store z target :=
    SelectedTarget.of_runtimeValueBorrow hslot hborrow hloc
  exact ⟨mutable, targets, target, leaf, hcontains, hmem, hselected,
    hloc, hrel⟩

/-- Updating a slot to `undef` cannot create ownership paths. -/
theorem ProgramStore.OwnsTransitively.update_undef_to_store
    {store : ProgramStore} {updated : Location} {updatedLifetime : Lifetime}
    {storage owned : Location} :
    ProgramStore.OwnsTransitively
        (store.update updated { value := .undef, lifetime := updatedLifetime })
        storage owned →
    ProgramStore.OwnsTransitively store storage owned := by
  intro howns
  induction howns with
  | direct hownsAt =>
      exact ProgramStore.OwnsTransitively.direct
        (ownsAt_update_undef hownsAt).2
  | trans hownsAt _htail ih =>
      exact ProgramStore.OwnsTransitively.trans
        (ownsAt_update_undef hownsAt).2 ih

/-- Erasing a store slot cannot create a concrete invalidation footprint. -/
theorem RuntimeValueBorrowInvalidatedBy.erase_to_store {store : ProgramStore}
    {erased : Location} {value : PartialValue} {root : Location} :
    RuntimeValueBorrowInvalidatedBy (store.erase erased) value root →
    RuntimeValueBorrowInvalidatedBy store value root := by
  intro hinvalid
  rcases hinvalid with ⟨leaf, hborrow, hrel⟩
  refine ⟨leaf, hborrow.erase_to_store, ?_⟩
  rcases hrel with hleaf | howns
  · exact Or.inl hleaf
  · exact Or.inr (ProgramStore.OwnsTransitively.erase_to_store howns)

/-- Updating a slot to `undef` cannot create a concrete invalidation footprint. -/
theorem RuntimeValueBorrowInvalidatedBy.update_undef_to_store
    {store : ProgramStore} {updated : Location} {updatedLifetime : Lifetime}
    {value : PartialValue} {root : Location} :
    RuntimeValueBorrowInvalidatedBy
        (store.update updated { value := .undef, lifetime := updatedLifetime })
        value root →
    RuntimeValueBorrowInvalidatedBy store value root := by
  intro hinvalid
  rcases hinvalid with ⟨leaf, hborrow, hrel⟩
  refine ⟨leaf, hborrow.update_undef_to_store, ?_⟩
  rcases hrel with hleaf | howns
  · exact Or.inl hleaf
  · exact Or.inr
      (ProgramStore.OwnsTransitively.update_undef_to_store howns)

/-- Erasing a store slot cannot create a selected runtime target. -/
theorem SelectedTarget.erase_to_store {store : ProgramStore}
    {erased : Location} {x : Name} {target : LVal} :
    SelectedTarget (store.erase erased) x target →
    SelectedTarget store x target := by
  intro hselected
  rcases hselected with
    ⟨cell, cellSlot, loc, hprotected, hcellSlot, hcellValue, htargetLoc⟩
  refine ⟨cell, cellSlot, loc, ?_, ?_, hcellValue, ?_⟩
  · rcases hprotected with hroot | hpath
    · exact Or.inl hroot
    · exact Or.inr (ProgramStore.OwnsTransitively.erase_to_store hpath)
  · exact RuntimeFrame.slotAt_of_erase_slotAt hcellSlot
  · exact RuntimeFrame.loc_erase_some_to_store htargetLoc

/-- Updating a slot to `undef` cannot create a selected runtime target. -/
theorem SelectedTarget.update_undef_to_store {store : ProgramStore}
    {updated : Location} {updatedLifetime : Lifetime}
    {x : Name} {target : LVal} :
    SelectedTarget
        (store.update updated { value := .undef, lifetime := updatedLifetime })
        x target →
    SelectedTarget store x target := by
  intro hselected
  rcases hselected with
    ⟨cell, cellSlot, loc, hprotected, hcellSlot, hcellValue, htargetLoc⟩
  have hcellNe : cell ≠ updated := by
    intro hcellEq
    subst hcellEq
    simp [ProgramStore.update] at hcellSlot
    cases hcellSlot
    simp at hcellValue
  have hcellSlotOld : store.slotAt cell = some cellSlot := by
    rw [← RuntimeFrame.ProgramStore.slotAt_update_ne hcellNe]
    exact hcellSlot
  refine ⟨cell, cellSlot, loc, ?_, hcellSlotOld, hcellValue, ?_⟩
  · rcases hprotected with hroot | hpath
    · exact Or.inl hroot
    · exact Or.inr (ProgramStore.OwnsTransitively.update_undef_to_store hpath)
  · exact RuntimeFrame.loc_update_undef_some_to_store htargetLoc

/-- Updating a fresh location cannot create a concrete invalidation footprint
inside a value stored in an old slot, for an old root distinct from the fresh
location. -/
theorem RuntimeValueBorrowInvalidatedBy.update_fresh_slot_to_store
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot}
    {slotLocation : Location} {value : PartialValue} {lifetime : Lifetime}
    {root : Location}
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh updated)
    (hroot : root ≠ updated)
    (hslot :
      store.slotAt slotLocation = some { value := value, lifetime := lifetime }) :
    RuntimeValueBorrowInvalidatedBy (store.update updated newSlot) value root →
    RuntimeValueBorrowInvalidatedBy store value root := by
  intro hinvalid
  rcases hinvalid with ⟨leaf, hborrow, hrel⟩
  refine ⟨leaf,
    RuntimeValueBorrow.update_fresh_slot_to_store hallocated hfresh hslot hborrow,
    ?_⟩
  rcases hrel with hleaf | howns
  · exact Or.inl hleaf
  · exact Or.inr
      (ProgramStore.OwnsTransitively.update_fresh_to_store
        hallocated hfresh hroot howns)

/-- Erasing a store slot cannot create a below-root concrete invalidation
footprint. -/
theorem RuntimeValueBorrowInvalidatedBelow.erase_to_store {store : ProgramStore}
    {erased : Location} {value : PartialValue} {root : Location} :
    RuntimeValueBorrowInvalidatedBelow (store.erase erased) value root →
    RuntimeValueBorrowInvalidatedBelow store value root := by
  intro hinvalid
  rcases hinvalid with ⟨leaf, hborrow, howns⟩
  exact ⟨leaf, hborrow.erase_to_store,
    ProgramStore.OwnsTransitively.erase_to_store howns⟩

/-- Updating a slot to `undef` cannot create a below-root concrete invalidation
footprint. -/
theorem RuntimeValueBorrowInvalidatedBelow.update_undef_to_store
    {store : ProgramStore} {updated : Location} {updatedLifetime : Lifetime}
    {value : PartialValue} {root : Location} :
    RuntimeValueBorrowInvalidatedBelow
        (store.update updated { value := .undef, lifetime := updatedLifetime })
        value root →
    RuntimeValueBorrowInvalidatedBelow store value root := by
  intro hinvalid
  rcases hinvalid with ⟨leaf, hborrow, howns⟩
  exact ⟨leaf, hborrow.update_undef_to_store,
    ProgramStore.OwnsTransitively.update_undef_to_store howns⟩

/-- Updating a fresh location cannot create a below-root concrete invalidation
footprint inside a value stored in an old slot, for an old root distinct from
the fresh location. -/
theorem RuntimeValueBorrowInvalidatedBelow.update_fresh_slot_to_store
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot}
    {slotLocation : Location} {value : PartialValue} {lifetime : Lifetime}
    {root : Location}
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh updated)
    (hroot : root ≠ updated)
    (hslot :
      store.slotAt slotLocation = some { value := value, lifetime := lifetime }) :
    RuntimeValueBorrowInvalidatedBelow (store.update updated newSlot) value root →
    RuntimeValueBorrowInvalidatedBelow store value root := by
  intro hinvalid
  rcases hinvalid with ⟨leaf, hborrow, howns⟩
  exact ⟨leaf,
    RuntimeValueBorrow.update_fresh_slot_to_store hallocated hfresh hslot hborrow,
    ProgramStore.OwnsTransitively.update_fresh_to_store
      hallocated hfresh hroot howns⟩

/-- For a bare non-owning reference, concrete invalidation depends only on the
stored reference location.  The lvalue expression that originally produced the
reference is not part of the runtime footprint. -/
theorem RuntimeValueBorrowInvalidatedBy.borrow_iff {store : ProgramStore}
    {borrowed root : Location} :
    RuntimeValueBorrowInvalidatedBy store
        (.value (.ref { location := borrowed, owner := false })) root ↔
      borrowed = root ∨ ProgramStore.OwnsTransitively store root borrowed := by
  constructor
  · intro hinvalid
    rcases hinvalid with ⟨leaf, hborrow, hrel⟩
    cases hborrow
    exact hrel
  · intro hrel
    exact ⟨borrowed, RuntimeValueBorrow.borrow, hrel⟩

/-- For a bare non-owning reference, below-root invalidation depends only on the
stored reference location being strictly inside the root's ownership subtree. -/
theorem RuntimeValueBorrowInvalidatedBelow.borrow_iff {store : ProgramStore}
    {borrowed root : Location} :
    RuntimeValueBorrowInvalidatedBelow store
        (.value (.ref { location := borrowed, owner := false })) root ↔
      ProgramStore.OwnsTransitively store root borrowed := by
  constructor
  · intro hinvalid
    rcases hinvalid with ⟨leaf, hborrow, hrel⟩
    cases hborrow
    exact hrel
  · intro hrel
    exact ⟨borrowed, RuntimeValueBorrow.borrow, hrel⟩

/-- Concrete value-safety frame for a raw store update.  The old value remains
runtime-safe after the update when none of its concrete runtime borrows is
invalidated by rewriting `updated`; if an owned reference points exactly at the
updated location, it follows the new slot and therefore needs the new slot to be
concrete-safe. -/
theorem ConcreteRuntimeValueSafe.update_of_not_invalidated
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot}
    {value : PartialValue} :
    ConcreteRuntimeValueSafe store value →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    ¬ RuntimeValueBorrowInvalidatedBy store value updated →
      ConcreteRuntimeValueSafe (store.update updated newSlot) value := by
  intro hsafe hnewSafe hnotInvalidated
  induction hsafe with
  | unit =>
      exact ConcreteRuntimeValueSafe.unit
  | int =>
      exact ConcreteRuntimeValueSafe.int
  | bool =>
      exact ConcreteRuntimeValueSafe.bool
  | undef =>
      exact ConcreteRuntimeValueSafe.undef
  | @borrow location slot hslot =>
      by_cases hlocation : location = updated
      · subst hlocation
        exact False.elim
          (hnotInvalidated
            ((RuntimeValueBorrowInvalidatedBy.borrow_iff).2 (Or.inl rfl)))
      · exact ConcreteRuntimeValueSafe.borrow (by
          simpa [ProgramStore.update, hlocation] using hslot)
  | @box location slot hslot _hinner ih =>
      by_cases hlocation : location = updated
      · subst hlocation
        exact ConcreteRuntimeValueSafe.box
          (by simp [ProgramStore.update]) hnewSafe
      · have hslotUpdate :
            (store.update updated newSlot).slotAt location = some slot := by
          simpa [ProgramStore.update, hlocation] using hslot
        have hinnerNotInvalidated :
            ¬ RuntimeValueBorrowInvalidatedBy store slot.value updated := by
          intro hinvalid
          rcases hinvalid with ⟨leaf, hborrow, hrel⟩
          exact hnotInvalidated
            ⟨leaf, RuntimeValueBorrow.box hslot hborrow, hrel⟩
        exact ConcreteRuntimeValueSafe.box hslotUpdate
          (ih hinnerNotInvalidated)

/-- Concrete value-safety frame for a raw store update with the precise
below-root danger.  Non-owning references directly to the updated slot remain
safe because the slot is still allocated after the update; only references into
the old owned subtree rooted at the updated slot need to be ruled out before a
subsequent drop of the old contents. -/
theorem ConcreteRuntimeValueSafe.update_of_not_below_invalidated
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot}
    {value : PartialValue} :
    ConcreteRuntimeValueSafe store value →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    ¬ RuntimeValueBorrowInvalidatedBelow store value updated →
      ConcreteRuntimeValueSafe (store.update updated newSlot) value := by
  intro hsafe hnewSafe hnotInvalidated
  induction hsafe with
  | unit =>
      exact ConcreteRuntimeValueSafe.unit
  | int =>
      exact ConcreteRuntimeValueSafe.int
  | bool =>
      exact ConcreteRuntimeValueSafe.bool
  | undef =>
      exact ConcreteRuntimeValueSafe.undef
  | @borrow location slot hslot =>
      by_cases hlocation : location = updated
      · subst hlocation
        exact ConcreteRuntimeValueSafe.borrow (slot := newSlot)
          (by simp [ProgramStore.update])
      · exact ConcreteRuntimeValueSafe.borrow (by
          simpa [ProgramStore.update, hlocation] using hslot)
  | @box location slot hslot _hinner ih =>
      by_cases hlocation : location = updated
      · subst hlocation
        exact ConcreteRuntimeValueSafe.box
          (by simp [ProgramStore.update]) hnewSafe
      · have hslotUpdate :
            (store.update updated newSlot).slotAt location = some slot := by
          simpa [ProgramStore.update, hlocation] using hslot
        have hinnerNotInvalidated :
            ¬ RuntimeValueBorrowInvalidatedBelow store slot.value updated := by
          intro hinvalid
          rcases hinvalid with ⟨leaf, hborrow, hrel⟩
          exact hnotInvalidated
            ⟨leaf, RuntimeValueBorrow.box hslot hborrow, hrel⟩
        exact ConcreteRuntimeValueSafe.box hslotUpdate
          (ih hinnerNotInvalidated)

/-- No old slot contains a concrete borrow invalidated by rewriting `updated`.
This is the store-level frame condition consumed by concrete assignment/update
safety. -/
def StoreConcreteUpdateKill (store : ProgramStore) (updated : Location) :
    Prop :=
  ∀ location slot,
    location ≠ updated →
    store.slotAt location = some slot →
      ¬ RuntimeValueBorrowInvalidatedBy store slot.value updated

/-- Concrete store-safety frame for a raw store update.  The updated slot is
checked directly; every other old slot is preserved by
`ConcreteRuntimeValueSafe.update_of_not_invalidated`. -/
theorem ConcreteRuntimeStoreSafe.update_of_not_invalidated
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot} :
    ConcreteRuntimeStoreSafe store →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    StoreConcreteUpdateKill store updated →
      ConcreteRuntimeStoreSafe (store.update updated newSlot) := by
  intro hstoreSafe hnewSafe hkill location slot hslot
  by_cases hlocation : location = updated
  · subst hlocation
    have hslotEq : slot = newSlot := by
      simpa [ProgramStore.update] using hslot.symm
    subst hslotEq
    exact hnewSafe
  · have hslotOld : store.slotAt location = some slot := by
      simpa [ProgramStore.update, hlocation] using hslot
    exact ConcreteRuntimeValueSafe.update_of_not_invalidated
      (hstoreSafe location slot hslotOld) hnewSafe
      (hkill location slot hlocation hslotOld)

/-- No old slot contains a concrete borrow into the ownership subtree rooted at
`updated`.  This is the precise store-level frame condition for a write followed
by dropping the old owned contents. -/
def StoreConcreteUpdateBelowKill (store : ProgramStore) (updated : Location) :
    Prop :=
  ∀ location slot,
    location ≠ updated →
    store.slotAt location = some slot →
      ¬ RuntimeValueBorrowInvalidatedBelow store slot.value updated

/-- Concrete store-safety frame for a raw store update using the precise
below-root invalidation condition. -/
theorem ConcreteRuntimeStoreSafe.update_of_not_below_invalidated
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot} :
    ConcreteRuntimeStoreSafe store →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    StoreConcreteUpdateBelowKill store updated →
      ConcreteRuntimeStoreSafe (store.update updated newSlot) := by
  intro hstoreSafe hnewSafe hkill location slot hslot
  by_cases hlocation : location = updated
  · subst hlocation
    have hslotEq : slot = newSlot := by
      simpa [ProgramStore.update] using hslot.symm
    subst hslotEq
    exact hnewSafe
  · have hslotOld : store.slotAt location = some slot := by
      simpa [ProgramStore.update, hlocation] using hslot
    exact ConcreteRuntimeValueSafe.update_of_not_below_invalidated
      (hstoreSafe location slot hslotOld) hnewSafe
      (hkill location slot hlocation hslotOld)

/-- Root-reachable concrete safety frame for a raw store update.  The updated
root, if any, is checked directly; every other live root is preserved by ruling
out below-root concrete invalidation in its old value. -/
theorem ConcreteRuntimeRootsSafe.update_of_not_below_invalidated
    {store : ProgramStore} {env : Env} {updated : Location}
    {newSlot : StoreSlot} :
    ConcreteRuntimeRootsSafe store env →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      VariableProjection x = updated →
        newSlot.lifetime = envSlot.lifetime) →
    (∀ x envSlot value,
      env.slotAt x = some envSlot →
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } →
      VariableProjection x ≠ updated →
        ¬ RuntimeValueBorrowInvalidatedBelow store value updated) →
      ConcreteRuntimeRootsSafe (store.update updated newSlot) env := by
  intro hroots hnewSafe hlifetime hkill x envSlot henvSlot
  by_cases hx : VariableProjection x = updated
  · subst updated
    cases newSlot with
    | mk newValue newLifetime =>
        have hlife : newLifetime = envSlot.lifetime :=
          hlifetime x envSlot henvSlot rfl
        exact ⟨newValue, by simp [ProgramStore.update, hlife], hnewSafe⟩
  · rcases hroots x envSlot henvSlot with ⟨value, hstoreSlot, hsafeValue⟩
    have hslotUpdated :
        (store.update updated newSlot).slotAt (VariableProjection x) =
          some { value := value, lifetime := envSlot.lifetime } := by
      simpa [ProgramStore.update, hx] using hstoreSlot
    exact ⟨value, hslotUpdated,
      ConcreteRuntimeValueSafe.update_of_not_below_invalidated hsafeValue
        hnewSafe (hkill x envSlot value henvSlot hstoreSlot hx)⟩

/-- Erasing a store slot preserves concrete borrow kills. -/
theorem StoreConcreteBorrowKill.erase {store : ProgramStore}
    {leaf erased : Location} {z : Name}
    (h : StoreConcreteBorrowKill store leaf z) :
    StoreConcreteBorrowKill (store.erase erased) leaf z := by
  intro value lifetime hslot hinvalid
  exact h value lifetime (RuntimeFrame.slotAt_of_erase_slotAt hslot)
    (RuntimeValueBorrowInvalidatedBelow.erase_to_store hinvalid)

/-- Updating a store slot to `undef` preserves concrete borrow kills. -/
theorem StoreConcreteBorrowKill.update_undef {store : ProgramStore}
    {leaf updated : Location} {z : Name} {updatedLifetime : Lifetime}
    (h : StoreConcreteBorrowKill store leaf z) :
    StoreConcreteBorrowKill
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      leaf z := by
  intro value lifetime hslot hinvalid
  by_cases hz : VariableProjection z = updated
  · subst hz
    simp [ProgramStore.update] at hslot
    cases hslot
    subst value
    subst lifetime
    rcases hinvalid with ⟨borrowed, hborrow, _hrel⟩
    cases hborrow
  · have hslotOld :
        store.slotAt (VariableProjection z) =
          some { value := value, lifetime := lifetime } := by
      rw [← RuntimeFrame.ProgramStore.slotAt_update_ne hz]
      exact hslot
    exact h value lifetime hslotOld
      (RuntimeValueBorrowInvalidatedBelow.update_undef_to_store hinvalid)

/-- Updating a fresh heap location preserves concrete borrow kills for every old
registered leaf distinct from that heap location. -/
theorem StoreConcreteBorrowKill.update_fresh_heap {store : ProgramStore}
    {leaf : Location} {address : Nat} {newSlot : StoreSlot} {z : Name}
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.heap address))
    (hleaf : leaf ≠ .heap address)
    (h : StoreConcreteBorrowKill store leaf z) :
    StoreConcreteBorrowKill (store.update (.heap address) newSlot) leaf z := by
  intro value lifetime hslot hinvalid
  have hvarNe : VariableProjection z ≠ .heap address := by
    intro hvar
    cases hvar
  have hslotOld :
      store.slotAt (VariableProjection z) =
        some { value := value, lifetime := lifetime } := by
    rw [← RuntimeFrame.ProgramStore.slotAt_update_ne hvarNe]
    exact hslot
  exact h value lifetime hslotOld
    (RuntimeValueBorrowInvalidatedBelow.update_fresh_slot_to_store
      hallocated hfresh hleaf hslotOld hinvalid)

/-- Updating a fresh variable preserves a concrete borrow kill for old slots,
provided the freshly-installed slot itself does not contain a below-root borrow
into the protected leaf.  This is the declaration frame for old registry entries:
the new variable is the only genuinely new root that must be checked. -/
theorem StoreConcreteBorrowKill.update_fresh_var {store : ProgramStore}
    {leaf : Location} {x z : Name} {newSlot : StoreSlot}
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.var x))
    (hleaf : leaf ≠ .var x)
    (h : StoreConcreteBorrowKill store leaf z)
    (hnew :
      z = x →
        ¬ RuntimeValueBorrowInvalidatedBelow
          (store.update (.var x) newSlot) newSlot.value leaf) :
    StoreConcreteBorrowKill (store.update (.var x) newSlot) leaf z := by
  intro value lifetime hslot hinvalid
  by_cases hz : z = x
  · subst hz
    have hslotEq : newSlot = { value := value, lifetime := lifetime } := by
      simpa [ProgramStore.update, VariableProjection] using hslot
    subst hslotEq
    exact hnew rfl hinvalid
  · have hvarNe : VariableProjection z ≠ .var x := by
      simpa [VariableProjection] using hz
    have hslotOld :
        store.slotAt (VariableProjection z) =
          some { value := value, lifetime := lifetime } := by
      rw [← RuntimeFrame.ProgramStore.slotAt_update_ne hvarNe]
      exact hslot
    exact h value lifetime hslotOld
      (RuntimeValueBorrowInvalidatedBelow.update_fresh_slot_to_store
        hallocated hfresh hleaf hslotOld hinvalid)

/-- A concrete kill rules out any selected target whose stored reference points
inside the ownership subtree rooted at that leaf. -/
theorem StoreConcreteBorrowKill.not_selectedTarget {store : ProgramStore}
    {leaf selectedLoc : Location} {z : Name} {target : LVal}
    {zSlot : StoreSlot}
    (hallocated : StoreOwnersAllocated store)
    (hkill : StoreConcreteBorrowKill store leaf z)
    (hzSlot : store.slotAt (VariableProjection z) = some zSlot)
    (hselected : SelectedTarget store z target)
    (htargetLoc : store.loc target = some selectedLoc)
    (hrel : ProgramStore.OwnsTransitively store leaf selectedLoc) :
    False := by
  rcases RuntimeValueBorrow.of_selectedTarget
      hallocated hzSlot hselected with ⟨loc, hloc, hborrow⟩
  have hlocEq : loc = selectedLoc :=
    Option.some.inj (hloc.symm.trans htargetLoc)
  have hrelLoc : ProgramStore.OwnsTransitively store leaf loc := by
    simpa [hlocEq] using hrel
  exact hkill zSlot.value zSlot.lifetime hzSlot
    ⟨loc, hborrow, hrelLoc⟩

/-- Concrete version of the live-`&mut` registry exclusivity invariant.  This is
the intended replacement for the `RealizedBorrowReads`-based registry: it records
that no cross-variable runtime reference points into the ownership subtree that
would be dropped by rewriting the registered leaf. -/
def ConcreteMutRegistryExclusive (store : ProgramStore)
    (R : List (Location × Name)) : Prop :=
  ∀ leaf owner, (leaf, owner) ∈ R →
    ∀ z, z ≠ owner → StoreConcreteBorrowKill store leaf z

/-- Erasing a store slot preserves concrete registry exclusivity. -/
theorem ConcreteMutRegistryExclusive.erase {store : ProgramStore}
    {R : List (Location × Name)} {erased : Location}
    (hexcl : ConcreteMutRegistryExclusive store R) :
    ConcreteMutRegistryExclusive (store.erase erased) R := by
  intro leaf owner hmem z hz
  exact (hexcl leaf owner hmem z hz).erase

/-- Updating a store slot to `undef` preserves concrete registry exclusivity. -/
theorem ConcreteMutRegistryExclusive.update_undef {store : ProgramStore}
    {R : List (Location × Name)} {updated : Location}
    {updatedLifetime : Lifetime}
    (hexcl : ConcreteMutRegistryExclusive store R) :
    ConcreteMutRegistryExclusive
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      R := by
  intro leaf owner hmem z hz
  exact (hexcl leaf owner hmem z hz).update_undef

/-- Updating a fresh heap location preserves concrete registry exclusivity for
all old entries whose registered leaf is not that fresh heap location. -/
theorem ConcreteMutRegistryExclusive.update_fresh_heap_filter
    {store : ProgramStore} {R : List (Location × Name)}
    {address : Nat} {newSlot : StoreSlot}
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.heap address))
    (hexcl : ConcreteMutRegistryExclusive store R) :
    ConcreteMutRegistryExclusive
      (store.update (.heap address) newSlot)
      (R.filter (fun entry => decide (entry.1 ≠ .heap address))) := by
  intro leaf owner hmem z hz
  have hmemOld : (leaf, owner) ∈ R :=
    List.mem_of_mem_filter hmem
  have hpred : decide ((leaf, owner).1 ≠ .heap address) = true :=
    (List.mem_filter.mp hmem).2
  have hleaf : leaf ≠ .heap address := by
    intro hleafEq
    subst hleafEq
    exact (of_decide_eq_true hpred) rfl
  exact (hexcl leaf owner hmemOld z hz).update_fresh_heap
    hallocated hfresh hleaf

/-- Updating a fresh variable preserves old concrete registry entries after
filtering out an impossible registered leaf at that variable, provided the new
slot is concrete-safe against every surviving old registered leaf owned by a
different variable. -/
theorem ConcreteMutRegistryExclusive.update_fresh_var_filter
    {store : ProgramStore} {R : List (Location × Name)}
    {x : Name} {newSlot : StoreSlot}
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.var x))
    (hexcl : ConcreteMutRegistryExclusive store R)
    (hnew :
      ∀ leaf owner,
        (leaf, owner) ∈ R →
        leaf ≠ .var x →
        x ≠ owner →
          ¬ RuntimeValueBorrowInvalidatedBelow
            (store.update (.var x) newSlot) newSlot.value leaf) :
    ConcreteMutRegistryExclusive
      (store.update (.var x) newSlot)
      (R.filter (fun entry => decide (entry.1 ≠ .var x))) := by
  intro leaf owner hmem z hz
  have hmemOld : (leaf, owner) ∈ R :=
    List.mem_of_mem_filter hmem
  have hpred : decide ((leaf, owner).1 ≠ .var x) = true :=
    (List.mem_filter.mp hmem).2
  have hleaf : leaf ≠ .var x := by
    intro hleafEq
    subst hleafEq
    exact (of_decide_eq_true hpred) rfl
  exact (hexcl leaf owner hmemOld z hz).update_fresh_var
    hallocated hfresh hleaf
    (by
      intro hzEq
      subst hzEq
      exact hnew leaf owner hmemOld hleaf hz)

/-- Filtering concrete registry entries preserves exclusivity. -/
theorem ConcreteMutRegistryExclusive.filter {store : ProgramStore}
    {R : List (Location × Name)} (p : Location × Name → Bool)
    (hexcl : ConcreteMutRegistryExclusive store R) :
    ConcreteMutRegistryExclusive store (R.filter p) := by
  intro leaf owner hmem z hz
  exact hexcl leaf owner (List.mem_of_mem_filter hmem) z hz

/-- Appending two concrete exclusive registries preserves exclusivity. -/
theorem ConcreteMutRegistryExclusive.append {store : ProgramStore}
    {left right : List (Location × Name)}
    (hleft : ConcreteMutRegistryExclusive store left)
    (hright : ConcreteMutRegistryExclusive store right) :
    ConcreteMutRegistryExclusive store (left ++ right) := by
  intro leaf owner hmem z hz
  rcases List.mem_append.mp hmem with hleftMem | hrightMem
  · exact hleft leaf owner hleftMem z hz
  · exact hright leaf owner hrightMem z hz

/-- Extending a concrete registry preserves exclusivity when the new leaf is
concretely exclusive for the new owner. -/
theorem ConcreteMutRegistryExclusive.cons {store : ProgramStore}
    {R : List (Location × Name)} {newLeaf : Location} {x : Name}
    (hold : ConcreteMutRegistryExclusive store R)
    (hnew : ∀ z, z ≠ x → StoreConcreteBorrowKill store newLeaf z) :
    ConcreteMutRegistryExclusive store ((newLeaf, x) :: R) := by
  intro leaf owner hmem z hz
  rcases List.mem_cons.mp hmem with heq | htail
  · cases heq
    exact hnew z hz
  · exact hold leaf owner htail z hz

/-- A concrete exclusive registry rules out cross-owner selected targets whose
concrete location is below a registered mutable-borrow leaf. -/
theorem ConcreteMutRegistryExclusive.not_selectedTarget
    {store : ProgramStore} {R : List (Location × Name)}
    {leaf selectedLoc : Location} {owner z : Name} {target : LVal}
    {zSlot : StoreSlot}
    (hexcl : ConcreteMutRegistryExclusive store R)
    (hallocated : StoreOwnersAllocated store)
    (hmem : (leaf, owner) ∈ R)
    (hz : z ≠ owner)
    (hzSlot : store.slotAt (VariableProjection z) = some zSlot)
    (hselected : SelectedTarget store z target)
    (htargetLoc : store.loc target = some selectedLoc)
    (hrel : ProgramStore.OwnsTransitively store leaf selectedLoc) :
    False :=
  (hexcl leaf owner hmem z hz).not_selectedTarget
    hallocated hzSlot hselected htargetLoc hrel

/-- Concrete mutable-borrow leaves carried by a runtime value viewed at a partial
type.  This follows owned boxes in the store and records only mutable non-owning
references.  It is intentionally store/runtime based: the leaf is the reference's
actual pointee location, not a static target-list approximation. -/
inductive RuntimeValueMutBorrow (store : ProgramStore) :
    PartialValue → PartialTy → Location → Prop where
  | borrow {leaf : Location} {targets : List LVal} :
      RuntimeValueMutBorrow store
        (.value (.ref { location := leaf, owner := false }))
        (.ty (.borrow true targets)) leaf
  | box {location : Location} {slot : StoreSlot} {inner : PartialTy}
      {leaf : Location} :
      store.slotAt location = some slot →
      RuntimeValueMutBorrow store slot.value inner leaf →
      RuntimeValueMutBorrow store
        (.value (.ref { location := location, owner := true }))
        (.box inner) leaf
  | boxFull {location : Location} {slot : StoreSlot} {ty : Ty}
      {leaf : Location} :
      store.slotAt location = some slot →
      RuntimeValueMutBorrow store slot.value (.ty ty) leaf →
      RuntimeValueMutBorrow store
        (.value (.ref { location := location, owner := true }))
        (.ty (.box ty)) leaf

/-- A mutable-borrow footprint is, in particular, a concrete runtime borrow
footprint.  This forgets only the mutability/type evidence; the concrete leaf is
unchanged. -/
theorem RuntimeValueMutBorrow.toBorrow {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {leaf : Location} :
    RuntimeValueMutBorrow store value ty leaf →
      RuntimeValueBorrow store value leaf := by
  intro hborrow
  induction hborrow with
  | borrow =>
      exact RuntimeValueBorrow.borrow
  | box hslot _hinner ih =>
      exact RuntimeValueBorrow.box hslot ih
  | boxFull hslot _hinner ih =>
      exact RuntimeValueBorrow.box hslot ih

/-- A mutable-borrow footprint below `root` is exactly the concrete assignment
drop hazard recorded by `RuntimeValueBorrowInvalidatedBelow`. -/
theorem RuntimeValueMutBorrow.invalidatedBelow {store : ProgramStore}
    {value : PartialValue} {ty : PartialTy} {root leaf : Location} :
    RuntimeValueMutBorrow store value ty leaf →
    ProgramStore.OwnsTransitively store root leaf →
      RuntimeValueBorrowInvalidatedBelow store value root := by
  intro hborrow hbelow
  exact ⟨leaf, hborrow.toBorrow, hbelow⟩

/-- A registry covers all concrete mutable-borrow leaves carried by one runtime
value once that value is installed under `owner`. -/
def ValueMutRegistryCovers (store : ProgramStore) (owner : Name)
    (value : PartialValue) (ty : PartialTy)
    (R : List (Location × Name)) : Prop :=
  ∀ leaf, RuntimeValueMutBorrow store value ty leaf → (leaf, owner) ∈ R

/-- A value registry has no unrelated entries: every entry belongs to `owner`
and corresponds to a concrete mutable borrow carried by the value. -/
def ValueMutRegistrySound (store : ProgramStore) (owner : Name)
    (value : PartialValue) (ty : PartialTy)
    (R : List (Location × Name)) : Prop :=
  ∀ leaf entryOwner, (leaf, entryOwner) ∈ R →
    entryOwner = owner ∧ RuntimeValueMutBorrow store value ty leaf

/-- Exact value-scoped registry: complete for the value's concrete mutable
borrows and containing no unrelated entries. -/
def ValueMutRegistryExact (store : ProgramStore) (owner : Name)
    (value : PartialValue) (ty : PartialTy)
    (R : List (Location × Name)) : Prop :=
  ValueMutRegistryCovers store owner value ty R ∧
    ValueMutRegistrySound store owner value ty R

/-- Coverage for a value is monotone under appending extra registry entries on
the right. -/
theorem ValueMutRegistryCovers.append_right {store : ProgramStore}
    {owner : Name} {value : PartialValue} {ty : PartialTy}
    {left right : List (Location × Name)}
    (hcover : ValueMutRegistryCovers store owner value ty left) :
    ValueMutRegistryCovers store owner value ty (left ++ right) := by
  intro leaf hleaf
  exact List.mem_append.mpr (Or.inl (hcover leaf hleaf))

/-- Coverage for a value is monotone under appending extra registry entries on
the left. -/
theorem ValueMutRegistryCovers.append_left {store : ProgramStore}
    {owner : Name} {value : PartialValue} {ty : PartialTy}
    {left right : List (Location × Name)}
    (hcover : ValueMutRegistryCovers store owner value ty right) :
    ValueMutRegistryCovers store owner value ty (left ++ right) := by
  intro leaf hleaf
  exact List.mem_append.mpr (Or.inr (hcover leaf hleaf))

/-- A singleton registry covers a top-level mutable borrow value under the chosen
owner. -/
theorem ValueMutRegistryCovers.singleton_borrow {store : ProgramStore}
    {owner : Name} {leaf : Location} {targets : List LVal} :
    ValueMutRegistryCovers store owner
      (.value (.ref { location := leaf, owner := false }))
      (.ty (.borrow true targets)) [(leaf, owner)] := by
  intro observed hborrow
  cases hborrow with
  | borrow =>
      simp

/-- The singleton registry is exact for a top-level mutable borrow value. -/
theorem ValueMutRegistryExact.singleton_borrow {store : ProgramStore}
    {owner : Name} {leaf : Location} {targets : List LVal} :
    ValueMutRegistryExact store owner
      (.value (.ref { location := leaf, owner := false }))
      (.ty (.borrow true targets)) [(leaf, owner)] := by
  constructor
  · exact ValueMutRegistryCovers.singleton_borrow
  · intro observed entryOwner hmem
    have hpair : (observed, entryOwner) = (leaf, owner) :=
      List.mem_singleton.mp hmem
    cases hpair
    exact ⟨rfl, RuntimeValueMutBorrow.borrow⟩

/-- Value-scoped coverage through an owned box slot. -/
theorem ValueMutRegistryCovers.box {store : ProgramStore}
    {owner : Name} {location : Location} {slot : StoreSlot}
    {inner : PartialTy} {R : List (Location × Name)} :
    store.slotAt location = some slot →
    ValueMutRegistryCovers store owner slot.value inner R →
    ValueMutRegistryCovers store owner
      (.value (.ref { location := location, owner := true }))
      (.box inner) R := by
  intro hslot hcover leaf hborrow
  cases hborrow with
  | box hslot' hinner =>
      have hslotEq : slot = _ := Option.some.inj (hslot.symm.trans hslot')
      subst hslotEq
      exact hcover leaf hinner

/-- Exact value-scoped registries transport through an owned box slot. -/
theorem ValueMutRegistryExact.box {store : ProgramStore}
    {owner : Name} {location : Location} {slot : StoreSlot}
    {inner : PartialTy} {R : List (Location × Name)} :
    store.slotAt location = some slot →
    ValueMutRegistryExact store owner slot.value inner R →
    ValueMutRegistryExact store owner
      (.value (.ref { location := location, owner := true }))
      (.box inner) R := by
  intro hslot hexact
  constructor
  · exact ValueMutRegistryCovers.box hslot hexact.1
  · intro leaf entryOwner hmem
    rcases hexact.2 leaf entryOwner hmem with ⟨howner, hborrow⟩
    exact ⟨howner, RuntimeValueMutBorrow.box hslot hborrow⟩

/-- Value-scoped coverage through a full boxed type. -/
theorem ValueMutRegistryCovers.boxFull {store : ProgramStore}
    {owner : Name} {location : Location} {slot : StoreSlot}
    {ty : Ty} {R : List (Location × Name)} :
    store.slotAt location = some slot →
    ValueMutRegistryCovers store owner slot.value (.ty ty) R →
    ValueMutRegistryCovers store owner
      (.value (.ref { location := location, owner := true }))
      (.ty (.box ty)) R := by
  intro hslot hcover leaf hborrow
  cases hborrow with
  | boxFull hslot' hinner =>
      have hslotEq : slot = _ := Option.some.inj (hslot.symm.trans hslot')
      subst hslotEq
      exact hcover leaf hinner

/-- Exact value-scoped registries transport through a full boxed type. -/
theorem ValueMutRegistryExact.boxFull {store : ProgramStore}
    {owner : Name} {location : Location} {slot : StoreSlot}
    {ty : Ty} {R : List (Location × Name)} :
    store.slotAt location = some slot →
    ValueMutRegistryExact store owner slot.value (.ty ty) R →
    ValueMutRegistryExact store owner
      (.value (.ref { location := location, owner := true }))
      (.ty (.box ty)) R := by
  intro hslot hexact
  constructor
  · exact ValueMutRegistryCovers.boxFull hslot hexact.1
  · intro leaf entryOwner hmem
    rcases hexact.2 leaf entryOwner hmem with ⟨howner, hborrow⟩
    exact ⟨howner, RuntimeValueMutBorrow.boxFull hslot hborrow⟩

/-- An exact value registry is exclusive once each carried mutable-borrow leaf is
known exclusive for the destination owner. -/
theorem ValueMutRegistryExact.exclusive {store : ProgramStore}
    {owner : Name} {value : PartialValue} {ty : PartialTy}
    {R : List (Location × Name)}
    (hexact : ValueMutRegistryExact store owner value ty R)
    (hleaves :
      ∀ leaf, RuntimeValueMutBorrow store value ty leaf →
        ∀ z, z ≠ owner → StoreRealizedSlotKill store leaf z) :
    MutRegistryExclusive store R := by
  intro leaf entryOwner hmem z hz
  rcases hexact.2 leaf entryOwner hmem with ⟨howner, hborrow⟩
  subst howner
  exact hleaves leaf hborrow z hz

/-- Concrete variant of `ValueMutRegistryExact.exclusive`: exact value
provenance is exclusive once each carried mutable-borrow leaf is concretely
exclusive for the destination owner. -/
theorem ValueMutRegistryExact.concreteExclusive {store : ProgramStore}
    {owner : Name} {value : PartialValue} {ty : PartialTy}
    {R : List (Location × Name)}
    (hexact : ValueMutRegistryExact store owner value ty R)
    (hleaves :
      ∀ leaf, RuntimeValueMutBorrow store value ty leaf →
        ∀ z, z ≠ owner → StoreConcreteBorrowKill store leaf z) :
    ConcreteMutRegistryExclusive store R := by
  intro leaf entryOwner hmem z hz
  rcases hexact.2 leaf entryOwner hmem with ⟨howner, hborrow⟩
  subst howner
  exact hleaves leaf hborrow z hz

/-- Every valid partial value admits a finite exact registry of the concrete
mutable borrow leaves it carries.  This registry is scoped to a future owner; it
does not claim the value has already been installed in the environment. -/
theorem ValueMutRegistryExact.exists_of_valid {store : ProgramStore}
    {owner : Name} {value : PartialValue} {ty : PartialTy} :
    ValidPartialValue store value ty →
    ∃ R, ValueMutRegistryExact store owner value ty R := by
  intro hvalid
  induction hvalid with
  | unit =>
      refine ⟨[], ?_, ?_⟩
      · intro leaf hborrow
        cases hborrow
      · intro leaf entryOwner hmem
        simp at hmem
  | int =>
      refine ⟨[], ?_, ?_⟩
      · intro leaf hborrow
        cases hborrow
      · intro leaf entryOwner hmem
        simp at hmem
  | bool =>
      refine ⟨[], ?_, ?_⟩
      · intro leaf hborrow
        cases hborrow
      · intro leaf entryOwner hmem
        simp at hmem
  | undef =>
      refine ⟨[], ?_, ?_⟩
      · intro leaf hborrow
        cases hborrow
      · intro leaf entryOwner hmem
        simp at hmem
  | borrow hmem hloc =>
      rename_i leaf mutable targets target
      cases mutable
      · refine ⟨[], ?_, ?_⟩
        · intro observed hborrow
          cases hborrow
        · intro observed entryOwner hmem
          simp at hmem
      · exact ⟨[(leaf, owner)], ValueMutRegistryExact.singleton_borrow⟩
  | box hslot _hinner ih =>
      rcases ih with ⟨R, hexact⟩
      exact ⟨R, ValueMutRegistryExact.box hslot hexact⟩
  | boxFull hslot _hinner ih =>
      rcases ih with ⟨R, hexact⟩
      exact ⟨R, ValueMutRegistryExact.boxFull hslot hexact⟩

/-- Convenience wrapper for full values. -/
theorem ValueMutRegistryExact.exists_of_validValue {store : ProgramStore}
    {owner : Name} {value : Value} {ty : Ty} :
    ValidValue store value ty →
    ∃ R, ValueMutRegistryExact store owner (.value value) (.ty ty) R :=
  ValueMutRegistryExact.exists_of_valid

/-- A value registry covers the mutable-borrow lvalues exposed once the value is
installed as a fresh root in `env`.

This is the coverage side that declaration preservation needs.  It is stated
separately from `ValueMutRegistryExact`: exactness talks about concrete mutable
borrow leaves carried by the value, while this predicate connects those leaves
to the lvalue typings exposed by the destination environment slot. -/
def InstalledFreshValueMutRegistryCovers (store : ProgramStore) (env : Env)
    (owner : Name) (ty : Ty) (lifetime : Lifetime)
    (R : List (Location × Name)) : Prop :=
  ∀ source targets bl leaf,
    LVal.base source = owner →
    LValTyping (env.update owner { ty := .ty ty, lifetime := lifetime })
      source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    (leaf, owner) ∈ R

/-- Concrete mutable-borrow provenance carried by a value for installation as a
fresh root.

The future owner matters: concrete exclusivity does not constrain the owner
itself, only other roots.  Declaration/assignment preservation will obtain this
package from the RHS evaluation and then append it to the environment
provenance registry. -/
def ConcreteRuntimeValueInstallProvenance (store : ProgramStore) (env : Env)
    (owner : Name) (value : Value) (ty : Ty) (lifetime : Lifetime) : Prop :=
  ∃ R,
    ValueMutRegistryExact store owner (.value value) (.ty ty) R ∧
      ConcreteMutRegistryExclusive store R ∧
      InstalledFreshValueMutRegistryCovers store env owner ty lifetime R

/-- If a fresh root is installed with unit type, no lvalue rooted at that
variable can expose a mutable-borrow type. -/
theorem LValTyping.update_unit_base_ty_eq {env : Env} {x : Name}
    {lifetime bl : Lifetime} {lv : LVal} {pt : PartialTy} :
    LVal.base lv = x →
    LValTyping (env.update x { ty := .ty .unit, lifetime := lifetime })
      lv pt bl →
    pt = .ty .unit := by
  intro hbase htyping
  induction lv generalizing pt bl with
  | var y =>
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hlife⟩
      simp [LVal.base] at hbase
      subst hbase
      simp [Env.update] at hslot
      cases hslot
      exact hty.symm
  | deref u ih =>
      cases htyping with
      | box hsource =>
          have h := ih (by simpa [LVal.base] using hbase) hsource
          cases h
      | borrow hsource _htargets =>
          have h := ih (by simpa [LVal.base] using hbase) hsource
          cases h

theorem LValTyping.update_int_base_ty_eq {env : Env} {x : Name}
    {lifetime bl : Lifetime} {lv : LVal} {pt : PartialTy} :
    LVal.base lv = x →
    LValTyping (env.update x { ty := .ty .int, lifetime := lifetime })
      lv pt bl →
    pt = .ty .int := by
  intro hbase htyping
  induction lv generalizing pt bl with
  | var y =>
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hlife⟩
      simp [LVal.base] at hbase
      subst hbase
      simp [Env.update] at hslot
      cases hslot
      exact hty.symm
  | deref u ih =>
      cases htyping with
      | box hsource =>
          have h := ih (by simpa [LVal.base] using hbase) hsource
          cases h
      | borrow hsource _htargets =>
          have h := ih (by simpa [LVal.base] using hbase) hsource
          cases h

theorem LValTyping.update_bool_base_ty_eq {env : Env} {x : Name}
    {lifetime bl : Lifetime} {lv : LVal} {pt : PartialTy} :
    LVal.base lv = x →
    LValTyping (env.update x { ty := .ty .bool, lifetime := lifetime })
      lv pt bl →
    pt = .ty .bool := by
  intro hbase htyping
  induction lv generalizing pt bl with
  | var y =>
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hlife⟩
      simp [LVal.base] at hbase
      subst hbase
      simp [Env.update] at hslot
      cases hslot
      exact hty.symm
  | deref u ih =>
      cases htyping with
      | box hsource =>
          have h := ih (by simpa [LVal.base] using hbase) hsource
          cases h
      | borrow hsource _htargets =>
          have h := ih (by simpa [LVal.base] using hbase) hsource
          cases h

/-- Installing `unit` as a fresh root contributes no mutable-borrow registry
entries. -/
theorem ConcreteRuntimeValueInstallProvenance.unit {store : ProgramStore}
    {env : Env} {owner : Name} {lifetime : Lifetime} :
    ConcreteRuntimeValueInstallProvenance store env owner .unit .unit lifetime := by
  refine ⟨[], ?_, ?_, ?_⟩
  · constructor
    · intro leaf hborrow
      cases hborrow
    · intro leaf entryOwner hmem
      simp at hmem
  · intro leaf entryOwner hmem _z _hz
    simp at hmem
  · intro source targets bl leaf hbase htyping _hloc
    have hty := LValTyping.update_unit_base_ty_eq hbase htyping
    cases hty

theorem ConcreteRuntimeValueInstallProvenance.int {store : ProgramStore}
    {env : Env} {owner : Name} {lifetime : Lifetime} {value : Int} :
    ConcreteRuntimeValueInstallProvenance store env owner (.int value) .int
      lifetime := by
  refine ⟨[], ?_, ?_, ?_⟩
  · constructor
    · intro leaf hborrow
      cases hborrow
    · intro leaf entryOwner hmem
      simp at hmem
  · intro leaf entryOwner hmem _z _hz
    simp at hmem
  · intro source targets bl leaf hbase htyping _hloc
    have hty := LValTyping.update_int_base_ty_eq hbase htyping
    cases hty

theorem ConcreteRuntimeValueInstallProvenance.bool {store : ProgramStore}
    {env : Env} {owner : Name} {lifetime : Lifetime} {value : Bool} :
    ConcreteRuntimeValueInstallProvenance store env owner (.bool value) .bool
      lifetime := by
  refine ⟨[], ?_, ?_, ?_⟩
  · constructor
    · intro leaf hborrow
      cases hborrow
    · intro leaf entryOwner hmem
      simp at hmem
  · intro leaf entryOwner hmem _z _hz
    simp at hmem
  · intro source targets bl leaf hbase htyping _hloc
    have hty := LValTyping.update_bool_base_ty_eq hbase htyping
    cases hty

/-- If an installed root slot stores a valid top-level mutable borrow value, the
value's exact registry covers the concrete pointee of `*x`.  This is the direct
`x = &mut y` bridge; nested boxes/reborrows need the recursive generalization. -/
theorem ValueMutRegistryExact.covers_valid_installed_var_mut_borrow
    {store : ProgramStore} {x : Name} {value : Value} {lifetime : Lifetime}
    {targets : List LVal} {R : List (Location × Name)} {leaf : Location} :
    store.slotAt (VariableProjection x) =
      some { value := .value value, lifetime := lifetime } →
    ValidValue store value (.borrow true targets) →
    ValueMutRegistryExact store x (.value value) (.ty (.borrow true targets)) R →
    store.loc (.deref (.var x)) = some leaf →
    (leaf, x) ∈ R := by
  intro hslot hvalid hexact hleaf
  cases hvalid with
  | borrow hmem htargetLoc =>
      rename_i storedLeaf selected
      have hslotVar :
          store.slotAt (.var x) =
            some
              { value := .value (.ref { location := storedLeaf, owner := false }),
                lifetime := lifetime } := by
        simpa [VariableProjection] using hslot
      have hleafEq : leaf = storedLeaf := by
        simp [ProgramStore.loc, hslotVar] at hleaf
        exact hleaf.symm
      rw [hleafEq]
      exact hexact.1 storedLeaf RuntimeValueMutBorrow.borrow

/--
The registry covers the currently live mutable borrows described by an
environment: every `&mut`-typed source whose dereference resolves to `leaf` has
an entry `(leaf, base source)` in the registry.

This is deliberately separated from `MutRegistryExclusive`.  Coverage is the
provenance side that must be maintained when new borrow values are installed;
exclusivity is the store-only side that survives joins without reading widened
target lists.
-/
def MutRegistryCovers (store : ProgramStore) (env : Env)
    (R : List (Location × Name)) : Prop :=
  ∀ (source : LVal) (targets : List LVal) (bl : Lifetime) (leaf : Location),
    LValTyping env source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    (leaf, LVal.base source) ∈ R

/-- Existing environment coverage remains valid after appending extra registry
entries on the right. -/
theorem MutRegistryCovers.append_right {store : ProgramStore} {env : Env}
    {left right : List (Location × Name)}
    (hcover : MutRegistryCovers store env left) :
    MutRegistryCovers store env (left ++ right) := by
  intro source targets bl leaf hsource hleaf
  exact List.mem_append.mpr (Or.inl (hcover source targets bl leaf hsource hleaf))

/-- Existing environment coverage remains valid after appending extra registry
entries on the left. -/
theorem MutRegistryCovers.append_left {store : ProgramStore} {env : Env}
    {left right : List (Location × Name)}
    (hcover : MutRegistryCovers store env right) :
    MutRegistryCovers store env (left ++ right) := by
  intro source targets bl leaf hsource hleaf
  exact List.mem_append.mpr (Or.inr (hcover source targets bl leaf hsource hleaf))

/--
The runtime provenance invariant needed by dereference-assignment preservation.

`RuntimeBorrowProvenance store env` says there is a live-`&mut` registry that
covers every concrete mutable borrow exposed by `env`, and whose registered
leaves are exclusive in the store-realized sense.  The existential hides the
registry from the paper-facing typing judgement while keeping the invariant
strong enough to instantiate `MutLeafExclusive` at a write through a concrete
borrow.
-/
def RuntimeBorrowProvenance (store : ProgramStore) (env : Env) : Prop :=
  ∃ R, MutRegistryCovers store env R ∧ MutRegistryExclusive store R

/-- Concrete-runtime version of borrow provenance.  It has the same coverage
side as `RuntimeBorrowProvenance`, but its exclusivity side talks only about
stored reference locations and ownership subtrees, not arbitrary lvalue
expressions or joined target-list alternatives. -/
def ConcreteRuntimeBorrowProvenance (store : ProgramStore) (env : Env) : Prop :=
  ∃ R, MutRegistryCovers store env R ∧ ConcreteMutRegistryExclusive store R

/--
Runtime-selected writable mutable-borrow gate for assignment through `*source`.

This is narrower than "every syntactic lvalue whose type is `&mut ...`": it also
requires the type-level write relation for the actual assignment lvalue
`.deref source`.  It deliberately does not include the current
`¬ WriteProhibited` check: a genuine mutable reference may be temporarily
blocked by a shorter-lived borrow and become writable again after that borrow is
dropped.  In particular, an immutable reborrow of a mutable reference can make
`*p` statically have mutable-borrow type, while still failing the structural
write gate for `**p`.
-/
def RuntimeWritableMutGate (store : ProgramStore) (env : Env)
    (source : LVal) (leaf : Location) : Prop :=
  ∃ targets bl rhsTy result,
    LValTyping env source (.ty (.borrow true targets)) bl ∧
      store.loc (.deref source) = some leaf ∧
      EnvWrite 0 env (.deref source) rhsTy result

/--
Coverage restricted to runtime-writable mutable gates.

This is the migration target for the provenance side of preservation.  The old
`MutRegistryCovers` quantifies over every syntactic lvalue typed `&mut`, which is
too broad for immutable reborrows such as `p = &x`: `*p` may be statically typed
as `&mut ...`, but assignment through `**p` is not an `EnvWrite` gate.  This
predicate records only gates that the assignment proof can actually consume.
-/
def WritableMutRegistryCovers (store : ProgramStore) (env : Env)
    (R : List (Location × Name)) : Prop :=
  ∀ source leaf,
    RuntimeWritableMutGate store env source leaf →
    (leaf, LVal.base source) ∈ R

/-- Writable-gate coverage for a value installed as a fresh root.

This is the value-scoped counterpart of
`InstalledFreshValueMutRegistryCovers`, but it only covers gates that assignment
preservation can actually consume.  Immutable reborrows may expose a syntactic
`&mut` view through dereference, but if the corresponding `EnvWrite` gate does
not exist then no registry entry is required. -/
def InstalledFreshValueWritableMutRegistryCovers
    (store : ProgramStore) (env : Env) (owner : Name)
    (ty : Ty) (lifetime : Lifetime) (R : List (Location × Name)) : Prop :=
  ∀ source leaf,
    LVal.base source = owner →
    RuntimeWritableMutGate store
      (env.update owner { ty := .ty ty, lifetime := lifetime }) source leaf →
    (leaf, owner) ∈ R

/-- Concrete writable-gate provenance carried by a value for installation as a
fresh root.

Unlike `ConcreteRuntimeValueInstallProvenance`, the coverage side is restricted
to runtime-writable gates.  This is the install package compatible with
immutable reborrows and joined target-list over-approximations. -/
def ConcreteRuntimeValueWritableInstallProvenance
    (store : ProgramStore) (env : Env) (owner : Name)
    (value : Value) (ty : Ty) (lifetime : Lifetime) : Prop :=
  ∃ R,
    ValueMutRegistryExact store owner (.value value) (.ty ty) R ∧
      ConcreteMutRegistryExclusive store R ∧
      InstalledFreshValueWritableMutRegistryCovers store env owner ty
        lifetime R

/-- Store-realized writable-gate provenance carried by a value for installation
as a fresh or rewritten root.

This is the assignment-frame counterpart of
`ConcreteRuntimeValueWritableInstallProvenance`: the coverage side is still
restricted to writable gates, but the exclusivity side is the store-realized
`MutRegistryExclusive` consumed by ordinary safe-abstraction preservation. -/
def RuntimeValueWritableInstallProvenance
    (store : ProgramStore) (env : Env) (owner : Name)
    (value : Value) (ty : Ty) (lifetime : Lifetime) : Prop :=
  ∃ R,
    ValueMutRegistryExact store owner (.value value) (.ty ty) R ∧
      MutRegistryExclusive store R ∧
      InstalledFreshValueWritableMutRegistryCovers store env owner ty
        lifetime R

/-- The old all-syntactic-target install package implies the writable-gate
install package. -/
theorem ConcreteRuntimeValueInstallProvenance.writable
    {store : ProgramStore} {env : Env} {owner : Name}
    {value : Value} {ty : Ty} {lifetime : Lifetime} :
    ConcreteRuntimeValueInstallProvenance store env owner value ty lifetime →
    ConcreteRuntimeValueWritableInstallProvenance store env owner value ty
      lifetime := by
  intro hprov
  rcases hprov with ⟨R, hexact, hexcl, hcover⟩
  refine ⟨R, hexact, hexcl, ?_⟩
  intro source leaf hbase hgate
  rcases hgate with ⟨targets, bl, _rhsTy, _result, hsource, hleaf, _hwrite⟩
  exact hcover source targets bl leaf hbase hsource hleaf

theorem ConcreteRuntimeValueWritableInstallProvenance.unit {store : ProgramStore}
    {env : Env} {owner : Name} {lifetime : Lifetime} :
    ConcreteRuntimeValueWritableInstallProvenance store env owner .unit .unit
      lifetime :=
  ConcreteRuntimeValueInstallProvenance.writable
    (ConcreteRuntimeValueInstallProvenance.unit (store := store)
      (env := env) (owner := owner) (lifetime := lifetime))

theorem ConcreteRuntimeValueWritableInstallProvenance.int {store : ProgramStore}
    {env : Env} {owner : Name} {lifetime : Lifetime} {value : Int} :
    ConcreteRuntimeValueWritableInstallProvenance store env owner (.int value)
      .int lifetime :=
  ConcreteRuntimeValueInstallProvenance.writable
    (ConcreteRuntimeValueInstallProvenance.int (store := store)
      (env := env) (owner := owner) (lifetime := lifetime) (value := value))

theorem ConcreteRuntimeValueWritableInstallProvenance.bool {store : ProgramStore}
    {env : Env} {owner : Name} {lifetime : Lifetime} {value : Bool} :
    ConcreteRuntimeValueWritableInstallProvenance store env owner (.bool value)
      .bool lifetime :=
  ConcreteRuntimeValueInstallProvenance.writable
    (ConcreteRuntimeValueInstallProvenance.bool (store := store)
      (env := env) (owner := owner) (lifetime := lifetime) (value := value))

theorem RuntimeValueWritableInstallProvenance.unit {store : ProgramStore}
    {env : Env} {owner : Name} {lifetime : Lifetime} :
    RuntimeValueWritableInstallProvenance store env owner .unit .unit
      lifetime := by
  refine ⟨[], ?_, ?_, ?_⟩
  · constructor
    · intro leaf hborrow
      cases hborrow
    · intro leaf entryOwner hmem
      simp at hmem
  · intro leaf entryOwner hmem _z _hz
    simp at hmem
  · intro source leaf hbase hgate
    rcases hgate with ⟨targets, bl, _rhsTy, _result, hsource, _hleaf,
      _hwrite⟩
    have hty := LValTyping.update_unit_base_ty_eq hbase hsource
    cases hty

theorem RuntimeValueWritableInstallProvenance.int {store : ProgramStore}
    {env : Env} {owner : Name} {lifetime : Lifetime} {value : Int} :
    RuntimeValueWritableInstallProvenance store env owner (.int value) .int
      lifetime := by
  refine ⟨[], ?_, ?_, ?_⟩
  · constructor
    · intro leaf hborrow
      cases hborrow
    · intro leaf entryOwner hmem
      simp at hmem
  · intro leaf entryOwner hmem _z _hz
    simp at hmem
  · intro source leaf hbase hgate
    rcases hgate with ⟨targets, bl, _rhsTy, _result, hsource, _hleaf,
      _hwrite⟩
    have hty := LValTyping.update_int_base_ty_eq hbase hsource
    cases hty

theorem RuntimeValueWritableInstallProvenance.bool {store : ProgramStore}
    {env : Env} {owner : Name} {lifetime : Lifetime} {value : Bool} :
    RuntimeValueWritableInstallProvenance store env owner (.bool value) .bool
      lifetime := by
  refine ⟨[], ?_, ?_, ?_⟩
  · constructor
    · intro leaf hborrow
      cases hborrow
    · intro leaf entryOwner hmem
      simp at hmem
  · intro leaf entryOwner hmem _z _hz
    simp at hmem
  · intro source leaf hbase hgate
    rcases hgate with ⟨targets, bl, _rhsTy, _result, hsource, _hleaf,
      _hwrite⟩
    have hty := LValTyping.update_bool_base_ty_eq hbase hsource
    cases hty

/-- Broad syntactic coverage implies writable-gate coverage. -/
theorem MutRegistryCovers.writable {store : ProgramStore} {env : Env}
    {R : List (Location × Name)}
    (hcover : MutRegistryCovers store env R) :
    WritableMutRegistryCovers store env R := by
  intro source leaf hgate
  rcases hgate with ⟨targets, bl, _rhsTy, _result, hsource, hleaf,
    _hwrite⟩
  exact hcover source targets bl leaf hsource hleaf

/-- Writable-gate coverage is monotone under appending extra entries on the
right. -/
theorem WritableMutRegistryCovers.append_right {store : ProgramStore}
    {env : Env} {left right : List (Location × Name)}
    (hcover : WritableMutRegistryCovers store env left) :
    WritableMutRegistryCovers store env (left ++ right) := by
  intro source leaf hgate
  exact List.mem_append.mpr (Or.inl (hcover source leaf hgate))

/-- Writable-gate coverage is monotone under appending extra entries on the
left. -/
theorem WritableMutRegistryCovers.append_left {store : ProgramStore}
    {env : Env} {left right : List (Location × Name)}
    (hcover : WritableMutRegistryCovers store env right) :
    WritableMutRegistryCovers store env (left ++ right) := by
  intro source leaf hgate
  exact List.mem_append.mpr (Or.inr (hcover source leaf hgate))

/-- Pull back only writable mutable gates from a coarser environment to a finer
one.  This is the join migration relation needed by writable-gate provenance:
unlike `RuntimeLValMutGatePullback`, it does not ask about every syntactic
`&mut` view, only about assignment-consumable gates. -/
def RuntimeWritableMutGatePullback (store : ProgramStore)
    (envFine envCoarse : Env) : Prop :=
  ∀ source leaf,
    RuntimeWritableMutGate store envCoarse source leaf →
    RuntimeWritableMutGate store envFine source leaf

/-- Writable-gate pullback is reflexive. -/
theorem RuntimeWritableMutGatePullback.refl
    (store : ProgramStore) (env : Env) :
    RuntimeWritableMutGatePullback store env env := by
  intro source leaf hgate
  exact hgate

/-- Writable-gate pullbacks compose. -/
theorem RuntimeWritableMutGatePullback.trans {store : ProgramStore}
    {envFine envMiddle envCoarse : Env}
    (hleft : RuntimeWritableMutGatePullback store envFine envMiddle)
    (hright : RuntimeWritableMutGatePullback store envMiddle envCoarse) :
    RuntimeWritableMutGatePullback store envFine envCoarse := by
  intro source leaf hgate
  exact hleft source leaf (hright source leaf hgate)

/-- Writable-gate coverage transports through a writable-gate pullback. -/
theorem WritableMutRegistryCovers.of_writableGatePullback
    {store : ProgramStore} {envFine envCoarse : Env}
    {R : List (Location × Name)}
    (hgate : RuntimeWritableMutGatePullback store envFine envCoarse)
    (hcover : WritableMutRegistryCovers store envFine R) :
    WritableMutRegistryCovers store envCoarse R := by
  intro source leaf hcoarse
  exact hcover source leaf (hgate source leaf hcoarse)

/-- Erasing a store slot preserves writable-gate coverage: any writable gate
whose dereference still resolves after the erase resolved before the erase. -/
theorem WritableMutRegistryCovers.erase {store : ProgramStore} {env : Env}
    {R : List (Location × Name)} {erased : Location}
    (hcover : WritableMutRegistryCovers store env R) :
    WritableMutRegistryCovers (store.erase erased) env R := by
  intro source leaf hgate
  rcases hgate with ⟨targets, bl, rhsTy, result, hsource, hleaf, hwrite⟩
  exact hcover source leaf
    ⟨targets, bl, rhsTy, result, hsource,
      RuntimeFrame.loc_erase_some_to_store hleaf, hwrite⟩

/-- Updating a store slot to `undef` preserves writable-gate coverage against an
unchanged environment. -/
theorem WritableMutRegistryCovers.update_undef {store : ProgramStore}
    {env : Env} {R : List (Location × Name)} {updated : Location}
    {updatedLifetime : Lifetime}
    (hcover : WritableMutRegistryCovers store env R) :
    WritableMutRegistryCovers
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env R := by
  intro source leaf hgate
  rcases hgate with ⟨targets, bl, rhsTy, result, hsource, hleaf, hwrite⟩
  exact hcover source leaf
    ⟨targets, bl, rhsTy, result, hsource,
      RuntimeFrame.loc_update_undef_some_to_store hleaf, hwrite⟩

/-- Fresh-update coverage with the fresh location filtered out of the writable
registry.

The proof is the writable-gate analogue of
`MutRegistryCovers.update_fresh_filter_of_wellFormed`: a writable gate observed
after a fresh update already resolved to an allocated old target before the
update, while the `EnvWrite` witness is unchanged because the environment is
unchanged. -/
theorem WritableMutRegistryCovers.update_fresh_filter_of_wellFormed
    {store : ProgramStore} {env : Env} {R : List (Location × Name)}
    {updated : Location} {newSlot : StoreSlot} {current : Lifetime}
    (hwell : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (hfresh : store.fresh updated)
    (hcover : WritableMutRegistryCovers store env R) :
    WritableMutRegistryCovers (store.update updated newSlot) env
      (R.filter (fun entry => decide (entry.1 ≠ updated))) := by
  intro source leaf hgate
  rcases hgate with ⟨targets, bl, rhsTy, result, hsource, hleaf, hwrite⟩
  rcases hwell.2.2.1 source true targets bl hsource with
    ⟨targetTy, targetLifetime, htargets⟩
  have hsourceAbs :
      LValLocationAbstraction store source (.ty (.borrow true targets)) :=
    lvalTyping_defined_location hwell hsafe hsource
  have htargetsAbs :
      ∀ target ty lifetime,
        LValTyping env target (.ty ty) lifetime →
        LValLocationAbstraction store target (.ty ty) := by
    intro target ty lifetime htarget
    exact lvalTyping_defined_location hwell hsafe htarget
  rcases location_borrow_selected_target hsourceAbs htargets htargetsAbs with
    ⟨selected, selectedTy, selectedLifetime, _hselectedMem, _hselectedTyping,
      hselectedAbs, _hstrengthens⟩
  rcases hselectedAbs with
    ⟨oldLeaf, oldLeafSlot, hlocOld, hslotOld, _hvalidOld⟩
  have hlocUpdated :
      (store.update updated newSlot).loc (.deref source) = some oldLeaf :=
    loc_update_of_loc hfresh hlocOld
  have hleafEq : leaf = oldLeaf :=
    Option.some.inj (hleaf.symm.trans hlocUpdated)
  have hmemOld : (oldLeaf, LVal.base source) ∈ R :=
    hcover source oldLeaf
      ⟨targets, bl, rhsTy, result, hsource, hlocOld, hwrite⟩
  have holdNe : oldLeaf ≠ updated := by
    intro holdEq
    subst holdEq
    rw [ProgramStore.fresh] at hfresh
    rw [hfresh] at hslotOld
    cases hslotOld
  have hmemFiltered :
      (oldLeaf, LVal.base source) ∈
        R.filter (fun entry => decide (entry.1 ≠ updated)) := by
    rw [List.mem_filter]
    exact ⟨hmemOld, decide_eq_true holdNe⟩
  simpa [hleafEq] using hmemFiltered

/-- Runtime borrow provenance keyed only by writable mutable gates. -/
def RuntimeWritableBorrowProvenance (store : ProgramStore) (env : Env) : Prop :=
  ∃ R, WritableMutRegistryCovers store env R ∧ MutRegistryExclusive store R

/-- The broad store-realized provenance package implies writable-gate
provenance. -/
theorem RuntimeBorrowProvenance.writable {store : ProgramStore} {env : Env} :
    RuntimeBorrowProvenance store env →
    RuntimeWritableBorrowProvenance store env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.writable, hexcl⟩

/-- Writable-gate provenance supplies the dereference-write frame invariant for
the concrete writable gate being consumed. -/
theorem RuntimeWritableBorrowProvenance.mutLeafExclusive
    {store : ProgramStore} {env : Env} {source : LVal} {leaf : Location} :
    RuntimeWritableBorrowProvenance store env →
    RuntimeWritableMutGate store env source leaf →
    MutLeafExclusive store env source leaf := by
  intro hprov hgate
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact hexcl.mutLeafExclusive (hcover source leaf hgate)

/-- Empty environments have writable-gate provenance. -/
theorem RuntimeWritableBorrowProvenance.empty {store : ProgramStore} :
    RuntimeWritableBorrowProvenance store Env.empty := by
  refine ⟨[], ?_, ?_⟩
  · intro source leaf hgate
    rcases hgate with ⟨targets, bl, _rhsTy, _result, hsource, _hleaf,
      _hwrite⟩
    exact False.elim (lvalTyping_empty_false hsource)
  · intro leaf owner hmem _z _hz
    simp at hmem

/-- Writable-gate provenance is unchanged by a value-tail multistep. -/
theorem RuntimeWritableBorrowProvenance.value_tail
    {store finalStore : ProgramStore} {env : Env}
    {lifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    RuntimeWritableBorrowProvenance store env →
    RuntimeWritableBorrowProvenance finalStore env := by
  intro hmulti hprov
  rcases multistep_value_inv hmulti with ⟨hstore, _hterm⟩
  simpa [hstore] using hprov

/-- Writable-gate provenance transports through a writable-gate pullback. -/
theorem RuntimeWritableBorrowProvenance.of_writableGatePullback
    {store : ProgramStore} {envFine envCoarse : Env}
    (hgate : RuntimeWritableMutGatePullback store envFine envCoarse)
    (hprov : RuntimeWritableBorrowProvenance store envFine) :
    RuntimeWritableBorrowProvenance store envCoarse := by
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.of_writableGatePullback hgate, hexcl⟩

/-- Writable-gate provenance survives erasing one store slot. -/
theorem RuntimeWritableBorrowProvenance.erase {store : ProgramStore}
    {env : Env} {erased : Location} :
    RuntimeWritableBorrowProvenance store env →
    RuntimeWritableBorrowProvenance (store.erase erased) env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.erase, hexcl.erase⟩

/-- Writable-gate provenance survives updating one store slot to `undef` when
the environment is unchanged. -/
theorem RuntimeWritableBorrowProvenance.update_undef
    {store : ProgramStore} {env : Env} {updated : Location}
    {updatedLifetime : Lifetime} :
    RuntimeWritableBorrowProvenance store env →
    RuntimeWritableBorrowProvenance
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.update_undef, hexcl.update_undef⟩

/-- Writable-gate provenance is preserved by dropping values when the
environment is unchanged. -/
theorem RuntimeWritableBorrowProvenance.drops
    {store store' : ProgramStore} {env : Env} {values : List PartialValue} :
    Drops store values store' →
    RuntimeWritableBorrowProvenance store env →
    RuntimeWritableBorrowProvenance store' env := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro hprov
      exact hprov
  | nonOwner _hnonOwner _hdrops ih =>
      intro hprov
      exact ih hprov
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hprov
      exact ih hprov
  | ownerPresent _howner _hslot _hdrops ih =>
      intro hprov
      exact ih hprov.erase

/-- Writable-gate provenance can be extended with an independently exclusive
registry without changing environment coverage. -/
theorem RuntimeWritableBorrowProvenance.append_exclusive
    {store : ProgramStore} {env : Env} {extra : List (Location × Name)}
    (hprov : RuntimeWritableBorrowProvenance store env)
    (hextra : MutRegistryExclusive store extra) :
    RuntimeWritableBorrowProvenance store env := by
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R ++ extra, hcover.append_right, hexcl.append hextra⟩

/--
Generic writable-gate provenance installation across an environment change.

The old broad install lemmas transported every syntactic `&mut` view.  For the
writable-gate registry, preservation should instead prove exactly two local
facts for the environment-changing rule:

* every old-root structural write gate in the result pulls back to an old gate;
* every gate rooted at the written/fresh owner is covered by the newly installed
  value registry.

This isolates the remaining declaration/write work without reintroducing
all-target static coverage.
-/
theorem RuntimeWritableBorrowProvenance.install_root
    {store : ProgramStore} {oldEnv newEnv : Env} {owner : Name}
    {extra : List (Location × Name)}
    (hpostOld : RuntimeWritableBorrowProvenance store oldEnv)
    (hextra : MutRegistryExclusive store extra)
    (holdPullback :
      ∀ source leaf,
        LVal.base source ≠ owner →
        RuntimeWritableMutGate store newEnv source leaf →
        RuntimeWritableMutGate store oldEnv source leaf)
    (hnewCover :
      ∀ source leaf,
        LVal.base source = owner →
        RuntimeWritableMutGate store newEnv source leaf →
        (leaf, owner) ∈ extra) :
    RuntimeWritableBorrowProvenance store newEnv := by
  rcases hpostOld with ⟨R, hcover, hexcl⟩
  refine ⟨R ++ extra, ?_, hexcl.append hextra⟩
  intro source leaf hgate
  by_cases hbase : LVal.base source = owner
  · exact List.mem_append.mpr
      (Or.inr (by simpa [hbase] using hnewCover source leaf hbase hgate))
  · exact List.mem_append.mpr
      (Or.inl (hcover source leaf (holdPullback source leaf hbase hgate)))

/-- Install a freshly declared or rewritten root using the value-scoped
store-realized writable provenance package. -/
theorem RuntimeWritableBorrowProvenance.install_fresh_root_of_valueWritableProvenance
    {store : ProgramStore} {env : Env} {owner : Name}
    {value : Value} {ty : Ty} {lifetime : Lifetime}
    (hpostOld : RuntimeWritableBorrowProvenance store env)
    (holdPullback :
      ∀ source leaf,
        LVal.base source ≠ owner →
        RuntimeWritableMutGate store
          (env.update owner { ty := .ty ty, lifetime := lifetime })
          source leaf →
        RuntimeWritableMutGate store env source leaf)
    (hvalueProv :
      RuntimeValueWritableInstallProvenance store env owner value ty
        lifetime) :
    RuntimeWritableBorrowProvenance store
      (env.update owner { ty := .ty ty, lifetime := lifetime }) := by
  rcases hvalueProv with ⟨R, _hexact, hexcl, hcover⟩
  exact RuntimeWritableBorrowProvenance.install_root
    hpostOld hexcl holdPullback
    (by
      intro source leaf hbase hgate
      exact hcover source leaf hbase hgate)

/-- Concrete runtime borrow provenance keyed only by writable mutable gates. -/
def ConcreteRuntimeWritableBorrowProvenance
    (store : ProgramStore) (env : Env) : Prop :=
  ∃ R, WritableMutRegistryCovers store env R ∧
    ConcreteMutRegistryExclusive store R

/-- The current broad concrete provenance package implies the writable-gate
package.  This is a one-way migration bridge: new proofs should target
`ConcreteRuntimeWritableBorrowProvenance`, while existing broad-provenance users
can still be projected into it. -/
theorem ConcreteRuntimeBorrowProvenance.writable {store : ProgramStore}
    {env : Env} :
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeWritableBorrowProvenance store env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.writable, hexcl⟩

/-- Empty environments have concrete writable-gate provenance. -/
theorem ConcreteRuntimeWritableBorrowProvenance.empty {store : ProgramStore} :
    ConcreteRuntimeWritableBorrowProvenance store Env.empty := by
  refine ⟨[], ?_, ?_⟩
  · intro source leaf hgate
    rcases hgate with ⟨targets, bl, _rhsTy, _result, hsource, _hleaf,
      _hwrite⟩
    exact False.elim (lvalTyping_empty_false hsource)
  · intro leaf owner hmem _z _hz
    simp at hmem

/-- Concrete writable-gate provenance is unchanged by a value-tail multistep. -/
theorem ConcreteRuntimeWritableBorrowProvenance.value_tail
    {store finalStore : ProgramStore} {env : Env}
    {lifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ConcreteRuntimeWritableBorrowProvenance store env →
    ConcreteRuntimeWritableBorrowProvenance finalStore env := by
  intro hmulti hprov
  rcases multistep_value_inv hmulti with ⟨hstore, _hterm⟩
  simpa [hstore] using hprov

/-- Concrete writable-gate provenance transports through a writable-gate
pullback with the same store and registry. -/
theorem ConcreteRuntimeWritableBorrowProvenance.of_writableGatePullback
    {store : ProgramStore} {envFine envCoarse : Env}
    (hgate : RuntimeWritableMutGatePullback store envFine envCoarse)
    (hprov : ConcreteRuntimeWritableBorrowProvenance store envFine) :
    ConcreteRuntimeWritableBorrowProvenance store envCoarse := by
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.of_writableGatePullback hgate, hexcl⟩

/-- Concrete writable-gate provenance survives erasing one store slot. -/
theorem ConcreteRuntimeWritableBorrowProvenance.erase {store : ProgramStore}
    {env : Env} {erased : Location} :
    ConcreteRuntimeWritableBorrowProvenance store env →
    ConcreteRuntimeWritableBorrowProvenance (store.erase erased) env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.erase, hexcl.erase⟩

/-- Concrete writable-gate provenance survives updating one slot to `undef`
when the environment is unchanged. -/
theorem ConcreteRuntimeWritableBorrowProvenance.update_undef
    {store : ProgramStore} {env : Env} {updated : Location}
    {updatedLifetime : Lifetime} :
    ConcreteRuntimeWritableBorrowProvenance store env →
    ConcreteRuntimeWritableBorrowProvenance
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.update_undef, hexcl.update_undef⟩

/-- Concrete writable provenance for old roots survives installing a fresh
variable when the installed value is concrete-safe against every surviving old
registered mutable-borrow leaf.

This is the writable-gate counterpart of
`ConcreteRuntimeBorrowProvenance.update_fresh_var_filter_of_wellFormed`. -/
theorem ConcreteRuntimeWritableBorrowProvenance.update_fresh_var_filter_of_wellFormed
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {x : Name} {newSlot : StoreSlot}
    (hwell : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.var x))
    (hnew :
      ∀ leaf owner,
        leaf ≠ .var x →
        x ≠ owner →
          ¬ RuntimeValueBorrowInvalidatedBelow
            (store.update (.var x) newSlot) newSlot.value leaf) :
    ConcreteRuntimeWritableBorrowProvenance store env →
      ConcreteRuntimeWritableBorrowProvenance
        (store.update (.var x) newSlot) env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R.filter (fun entry => decide (entry.1 ≠ .var x)),
    WritableMutRegistryCovers.update_fresh_filter_of_wellFormed
      hwell hsafe hfresh hcover,
    ConcreteMutRegistryExclusive.update_fresh_var_filter
      hallocated hfresh hexcl
      (fun leaf owner _hmem hleaf howner =>
        hnew leaf owner hleaf howner)⟩

/-- Declaration form of
`ConcreteRuntimeWritableBorrowProvenance.update_fresh_var_filter_of_wellFormed`.

This preserves the old-root writable registry while the fresh root's slot is
allocated; adding the fresh root's own writable entries is handled separately by
`install_fresh_root_of_valueWritableProvenance`. -/
theorem ConcreteRuntimeWritableBorrowProvenance.declare_old_roots_of_not_below_invalidated
    {store : ProgramStore} {env : Env} {current lifetime : Lifetime}
    {x : Name} {value : Value}
    (hwell : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.var x))
    (hnew :
      ∀ leaf owner,
        leaf ≠ .var x →
        x ≠ owner →
          ¬ RuntimeValueBorrowInvalidatedBelow
            (store.declare x lifetime value) (.value value) leaf) :
    ConcreteRuntimeWritableBorrowProvenance store env →
      ConcreteRuntimeWritableBorrowProvenance
        (store.declare x lifetime value) env := by
  intro hprov
  simpa [ProgramStore.declare] using
    ConcreteRuntimeWritableBorrowProvenance.update_fresh_var_filter_of_wellFormed
      (store := store) (env := env) (current := current)
      (x := x) (newSlot := { value := .value value, lifetime := lifetime })
      hwell hsafe hallocated hfresh
      (by
        intro leaf owner hleaf howner
        simpa [ProgramStore.declare] using hnew leaf owner hleaf howner)
      hprov

/-- Concrete writable-gate provenance is preserved by dropping values when the
environment is unchanged. -/
theorem ConcreteRuntimeWritableBorrowProvenance.drops
    {store store' : ProgramStore} {env : Env} {values : List PartialValue} :
    Drops store values store' →
    ConcreteRuntimeWritableBorrowProvenance store env →
    ConcreteRuntimeWritableBorrowProvenance store' env := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro hprov
      exact hprov
  | nonOwner _hnonOwner _hdrops ih =>
      intro hprov
      exact ih hprov
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hprov
      exact ih hprov
  | ownerPresent _howner _hslot _hdrops ih =>
      intro hprov
      exact ih hprov.erase

/-- Concrete writable-gate provenance survives allocating a fresh heap box.
Coverage keeps only old registered leaves; the fresh heap leaf cannot be needed
for an unchanged environment. -/
theorem ConcreteRuntimeWritableBorrowProvenance.boxAt {store : ProgramStore}
    {env : Env} {current : Lifetime} {address : Nat} {value : Value}
    (hwell : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.heap address)) :
    ConcreteRuntimeWritableBorrowProvenance store env →
    ConcreteRuntimeWritableBorrowProvenance (store.boxAt address value).1
      env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  refine ⟨R.filter (fun entry => decide (entry.1 ≠ .heap address)), ?_, ?_⟩
  · simpa [ProgramStore.boxAt] using
      WritableMutRegistryCovers.update_fresh_filter_of_wellFormed
        hwell hsafe hfresh hcover
  · simpa [ProgramStore.boxAt] using
      ConcreteMutRegistryExclusive.update_fresh_heap_filter
        hallocated hfresh hexcl

/-- Concrete writable-gate provenance can be extended with an independently
exclusive registry without changing environment coverage. -/
theorem ConcreteRuntimeWritableBorrowProvenance.append_exclusive
    {store : ProgramStore} {env : Env} {extra : List (Location × Name)}
    (hprov : ConcreteRuntimeWritableBorrowProvenance store env)
    (hextra : ConcreteMutRegistryExclusive store extra) :
    ConcreteRuntimeWritableBorrowProvenance store env := by
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R ++ extra, hcover.append_right, hexcl.append hextra⟩

/-- Concrete variant of `RuntimeWritableBorrowProvenance.install_root`. -/
theorem ConcreteRuntimeWritableBorrowProvenance.install_root
    {store : ProgramStore} {oldEnv newEnv : Env} {owner : Name}
    {extra : List (Location × Name)}
    (hpostOld : ConcreteRuntimeWritableBorrowProvenance store oldEnv)
    (hextra : ConcreteMutRegistryExclusive store extra)
    (holdPullback :
      ∀ source leaf,
        LVal.base source ≠ owner →
        RuntimeWritableMutGate store newEnv source leaf →
        RuntimeWritableMutGate store oldEnv source leaf)
    (hnewCover :
      ∀ source leaf,
        LVal.base source = owner →
        RuntimeWritableMutGate store newEnv source leaf →
        (leaf, owner) ∈ extra) :
    ConcreteRuntimeWritableBorrowProvenance store newEnv := by
  rcases hpostOld with ⟨R, hcover, hexcl⟩
  refine ⟨R ++ extra, ?_, hexcl.append hextra⟩
  intro source leaf hgate
  by_cases hbase : LVal.base source = owner
  · exact List.mem_append.mpr
      (Or.inr (by simpa [hbase] using hnewCover source leaf hbase hgate))
  · exact List.mem_append.mpr
      (Or.inl (hcover source leaf (holdPullback source leaf hbase hgate)))

/-- Install a freshly declared root using the value-scoped writable provenance
package.

The rule-specific proof still supplies the old-root pullback, because that
depends on how the environment changed.  The installed value package supplies
the concrete exclusive registry and covers every writable gate rooted at the new
owner. -/
theorem ConcreteRuntimeWritableBorrowProvenance.install_fresh_root_of_valueWritableProvenance
    {store : ProgramStore} {env : Env} {owner : Name}
    {value : Value} {ty : Ty} {lifetime : Lifetime}
    (hpostOld : ConcreteRuntimeWritableBorrowProvenance store env)
    (holdPullback :
      ∀ source leaf,
        LVal.base source ≠ owner →
        RuntimeWritableMutGate store
          (env.update owner { ty := .ty ty, lifetime := lifetime })
          source leaf →
        RuntimeWritableMutGate store env source leaf)
    (hvalueProv :
      ConcreteRuntimeValueWritableInstallProvenance store env owner value ty
        lifetime) :
    ConcreteRuntimeWritableBorrowProvenance store
      (env.update owner { ty := .ty ty, lifetime := lifetime }) := by
  rcases hvalueProv with ⟨R, _hexact, hexcl, hcover⟩
  exact ConcreteRuntimeWritableBorrowProvenance.install_root
    hpostOld hexcl holdPullback
    (by
      intro source leaf hbase hgate
      exact hcover source leaf hbase hgate)

/-- Writable-gate provenance gives the concrete below-root assignment frame for
any other root. -/
theorem ConcreteRuntimeWritableBorrowProvenance.not_below_invalidated_of_writableGate
    {store : ProgramStore} {env : Env} {source : LVal}
    {leaf : Location} {z : Name} {lifetime : Lifetime} {value : PartialValue} :
    ConcreteRuntimeWritableBorrowProvenance store env →
    RuntimeWritableMutGate store env source leaf →
    z ≠ LVal.base source →
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := lifetime } →
      ¬ RuntimeValueBorrowInvalidatedBelow store value leaf := by
  intro hprov hgate hz hslot
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact (hexcl leaf (LVal.base source) (hcover source leaf hgate)
    z hz) value lifetime hslot

/-- Writable-gate provenance rules out a cross-root selected target below the
registered writable leaf. -/
theorem ConcreteRuntimeWritableBorrowProvenance.not_selectedTarget_of_writableGate
    {store : ProgramStore} {env : Env} {source : LVal}
    {leaf selectedLoc : Location} {z : Name} {target : LVal}
    {zSlot : StoreSlot} :
    ConcreteRuntimeWritableBorrowProvenance store env →
    StoreOwnersAllocated store →
    RuntimeWritableMutGate store env source leaf →
    z ≠ LVal.base source →
    store.slotAt (VariableProjection z) = some zSlot →
    SelectedTarget store z target →
    store.loc target = some selectedLoc →
    ProgramStore.OwnsTransitively store leaf selectedLoc →
    False := by
  intro hprov hallocated hgate hz hzSlot hselected htargetLoc hbelow
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ConcreteMutRegistryExclusive.not_selectedTarget hexcl hallocated
    (hcover source leaf hgate) hz hzSlot hselected htargetLoc hbelow

/-- Concrete provenance rules out a cross-owner selected runtime target at, or
below, a registered mutable-borrow leaf.

This is the concrete consumption bridge needed by assignment preservation: the
registered source contributes the `(leaf, base source)` entry, and the concrete
exclusive side rules out any other root whose actual stored reference would be
invalidated by writing that leaf.  Static target-list alternatives introduced by
joins are irrelevant unless they are selected by the runtime store. -/
theorem ConcreteRuntimeBorrowProvenance.not_cross_selectedTarget
    {store : ProgramStore} {env : Env} {source : LVal}
    {targets : List LVal} {bl : Lifetime} {leaf : Location}
    {z : Name} {mutable : Bool} {targetsOther : List LVal}
    {target : LVal} {selectedLoc : Location} :
    ConcreteRuntimeBorrowProvenance store env →
    StoreOwnersAllocated store →
    store ∼ₛ env →
    LValTyping env source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    env ⊢ z ↝ Ty.borrow mutable targetsOther →
    SelectedTarget store z target →
    store.loc target = some selectedLoc →
    ProgramStore.OwnsTransitively store leaf selectedLoc →
    z ≠ LVal.base source →
    False := by
  intro hprov hallocated hsafe hsource hleaf hz hselected htargetLoc hrel hne
  rcases hprov with ⟨R, hcover, hexcl⟩
  rcases hz with ⟨zEnvSlot, hzEnvSlot, _hcontains⟩
  rcases hsafe.2 z zEnvSlot hzEnvSlot with ⟨zValue, hzStore, _hzValid⟩
  let zSlot : StoreSlot := { value := zValue, lifetime := zEnvSlot.lifetime }
  have hzSlot :
      store.slotAt (VariableProjection z) = some zSlot := hzStore
  exact ConcreteMutRegistryExclusive.not_selectedTarget hexcl hallocated
    (hcover source targets bl leaf hsource hleaf) hne hzSlot hselected
    htargetLoc hrel

/-- Concrete provenance rules out the actual runtime drop hazard for a
cross-root value.

If `source` is a live `&mut` whose dereference resolves to `leaf`, then no
other root can contain a concrete runtime borrow into the ownership subtree below
`leaf`.  This is the concrete assignment frame we need for `*source := value`:
rewriting `leaf` may drop the old owned subtree, but joined-in static target-list
members are irrelevant unless some stored reference actually points below
`leaf`.
-/
theorem ConcreteRuntimeBorrowProvenance.not_below_invalidated_of_validRoot
    {store : ProgramStore} {env : Env} {source : LVal}
    {targets : List LVal} {bl : Lifetime} {leaf : Location}
    {z : Name} {zSlot : EnvSlot} {value : PartialValue} :
    ConcreteRuntimeBorrowProvenance store env →
    StoreOwnersAllocated store →
    store ∼ₛ env →
    LValTyping env source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    z ≠ LVal.base source →
    env.slotAt z = some zSlot →
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := zSlot.lifetime } →
    ValidPartialValue store value zSlot.ty →
      ¬ RuntimeValueBorrowInvalidatedBelow store value leaf := by
  intro hprov hallocated hsafe hsource hleaf hzNe hzSlot hstoreSlot hvalid hinvalid
  rcases RuntimeValueBorrowInvalidatedBelow.selectedTarget_of_validRoot
      hstoreSlot hvalid hinvalid with
    ⟨mutable, targetsOther, target, selectedLoc, hcontains, hmem,
      hselected, htargetLoc, hbelow⟩
  exact hprov.not_cross_selectedTarget hallocated hsafe hsource hleaf
    ⟨zSlot, hzSlot, hcontains⟩ hselected htargetLoc hbelow hzNe

/-- Variable-source variant for a same-shape join.

If the joined environment exposes `x` as a mutable-borrow source and the runtime
dereference of `*x` resolves to `leaf`, then concrete provenance from the
executed branch still rules out any other root carrying an actual runtime borrow
below `leaf`.  The only join-sensitive step is pulling the variable's `&mut`
typing back through the same-shape map; the concrete registry entry itself is
store-keyed. -/
theorem ConcreteRuntimeBorrowProvenance.not_below_invalidated_of_validRoot_var_join
    {store : ProgramStore} {envFine envCoarse : Env}
    {x z : Name} {targets : List LVal} {bl : Lifetime}
    {leaf : Location} {zSlot : EnvSlot} {value : PartialValue} :
    EnvSameShapeStrengthening envFine envCoarse →
    ConcreteRuntimeBorrowProvenance store envFine →
    StoreOwnersAllocated store →
    LValTyping envCoarse (.var x) (.ty (.borrow true targets)) bl →
    store.loc (.deref (.var x)) = some leaf →
    z ≠ x →
    envCoarse.slotAt z = some zSlot →
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := zSlot.lifetime } →
    ValidPartialValue store value zSlot.ty →
      ¬ RuntimeValueBorrowInvalidatedBelow store value leaf := by
  intro hmap hprov hallocated hsource hleaf hzNe _hzSlot hstoreSlot hvalid
    hinvalid
  rcases RuntimeValueBorrowInvalidatedBelow.selectedTarget_of_validRoot
      hstoreSlot hvalid hinvalid with
    ⟨mutable, targetsOther, target, selectedLoc, _hcontains, _hmem,
      hselected, htargetLoc, hbelow⟩
  rcases hprov with ⟨R, hcover, hexcl⟩
  rcases LValTyping.var_inv hsource with
    ⟨sourceSlot, hsourceSlot, hsourceTy, hsourceLifetime⟩
  cases sourceSlot with
  | mk sourceTy sourceLifetime =>
      cases hsourceTy
      cases hsourceLifetime
      rcases lvalMutVar_pullback_of_strengthening hmap hsourceSlot with
        ⟨targetsFine, blFine, hsourceFine⟩
      exact ConcreteMutRegistryExclusive.not_selectedTarget hexcl hallocated
        (hcover (.var x) targetsFine blFine leaf hsourceFine hleaf)
        hzNe hstoreSlot hselected htargetLoc hbelow

/-- Concrete provenance rules out cross-root below-invalidation through a
runtime mutable-borrow gate pullback.

The coarse environment may have joined or widened the source's target list.  The
only static fact needed from that coarse environment is the gate saying the
source is `&mut`-typed; the actual registry entry is recovered from the finer
environment using the concrete dereference `store.loc (*source) = leaf`. -/
theorem ConcreteRuntimeBorrowProvenance.not_below_invalidated_of_validRoot_join
    {store : ProgramStore} {envFine envCoarse : Env}
    {source : LVal} {z : Name} {targets : List LVal} {bl : Lifetime}
    {leaf : Location} {zSlot : EnvSlot} {value : PartialValue} :
    RuntimeLValMutGatePullback store envFine envCoarse →
    ConcreteRuntimeBorrowProvenance store envFine →
    StoreOwnersAllocated store →
    LValTyping envCoarse source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    z ≠ LVal.base source →
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := zSlot.lifetime } →
    ValidPartialValue store value zSlot.ty →
      ¬ RuntimeValueBorrowInvalidatedBelow store value leaf := by
  intro hgate hprov hallocated hsource hleaf hzNe hstoreSlot hvalid
    hinvalid
  rcases RuntimeValueBorrowInvalidatedBelow.selectedTarget_of_validRoot
      hstoreSlot hvalid hinvalid with
    ⟨mutable, targetsOther, target, selectedLoc, _hcontains, _hmem,
      hselected, htargetLoc, hbelow⟩
  rcases hprov with ⟨R, hcover, hexcl⟩
  rcases hgate source targets bl leaf hsource hleaf with
    ⟨targetsFine, blFine, hsourceFine⟩
  exact ConcreteMutRegistryExclusive.not_selectedTarget hexcl hallocated
    (hcover source targetsFine blFine leaf hsourceFine hleaf)
    hzNe hstoreSlot hselected htargetLoc hbelow

/-- Concrete-only variable-source variant for a same-shape join.

This is the callback shape needed by concrete root update frames: for every root
other than the owner of the live `&mut` variable source, the branch provenance
registry gives a direct `StoreConcreteBorrowKill`, so no static
`ValidPartialValue` witness for the other root is needed. -/
theorem ConcreteRuntimeBorrowProvenance.not_below_invalidated_of_var_join
    {store : ProgramStore} {envFine envCoarse : Env}
    {x z : Name} {targets : List LVal} {bl lifetime : Lifetime}
    {leaf : Location} {value : PartialValue} :
    EnvSameShapeStrengthening envFine envCoarse →
    ConcreteRuntimeBorrowProvenance store envFine →
    LValTyping envCoarse (.var x) (.ty (.borrow true targets)) bl →
    store.loc (.deref (.var x)) = some leaf →
    z ≠ x →
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := lifetime } →
      ¬ RuntimeValueBorrowInvalidatedBelow store value leaf := by
  intro hmap hprov hsource hleaf hzNe hstoreSlot
  rcases hprov with ⟨R, hcover, hexcl⟩
  rcases LValTyping.var_inv hsource with
    ⟨sourceSlot, hsourceSlot, hsourceTy, hsourceLifetime⟩
  cases sourceSlot with
  | mk sourceTy sourceLifetime =>
      cases hsourceTy
      cases hsourceLifetime
      rcases lvalMutVar_pullback_of_strengthening hmap hsourceSlot with
        ⟨targetsFine, blFine, hsourceFine⟩
      exact (hexcl leaf x
        (hcover (.var x) targetsFine blFine leaf hsourceFine hleaf)
        z hzNe) value lifetime hstoreSlot

/-- Concrete-only mutable-gate variant for a same-store join.

This is the direct store-level form used by concrete root update frames: once a
coarse mutable-borrow source is pulled back to the executed fine environment,
the concrete registry gives a `StoreConcreteBorrowKill` for every other root. -/
theorem ConcreteRuntimeBorrowProvenance.not_below_invalidated_of_join
    {store : ProgramStore} {envFine envCoarse : Env}
    {source : LVal} {z : Name} {targets : List LVal} {bl lifetime : Lifetime}
    {leaf : Location} {value : PartialValue} :
    RuntimeLValMutGatePullback store envFine envCoarse →
    ConcreteRuntimeBorrowProvenance store envFine →
    LValTyping envCoarse source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    z ≠ LVal.base source →
    store.slotAt (VariableProjection z) =
      some { value := value, lifetime := lifetime } →
      ¬ RuntimeValueBorrowInvalidatedBelow store value leaf := by
  intro hgate hprov hsource hleaf hzNe hstoreSlot
  rcases hprov with ⟨R, hcover, hexcl⟩
  rcases hgate source targets bl leaf hsource hleaf with
    ⟨targetsFine, blFine, hsourceFine⟩
  exact (hexcl leaf (LVal.base source)
    (hcover source targetsFine blFine leaf hsourceFine hleaf)
    z hzNe) value lifetime hstoreSlot

/-- Concrete root update frame for assignment through a variable-held mutable
borrow after a same-shape join.

The joined environment may widen `x`'s static target list, but the store still
contains one concrete pointee for `x`.  Branch provenance supplies the
cross-root frame for that concrete pointee; the owner-root case is discharged by
the fact that a bare non-owning reference to `updated` is not a borrow below
`updated` unless the updated storage owns itself. -/
theorem ConcreteRuntimeRootsSafe.update_of_var_mut_borrow_provenance_join
    {store : ProgramStore} {envFine envCoarse : Env}
    {x : Name} {targets : List LVal} {bl : Lifetime}
    {updated : Location} {updatedSlot newSlot : StoreSlot}
    {updatedTy : PartialTy} :
    EnvSameShapeStrengthening envFine envCoarse →
    ConcreteRuntimeRootsSafe store envCoarse →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    ConcreteRuntimeBorrowProvenance store envFine →
    store ∼ₛ envCoarse →
    LValTyping envCoarse (.var x) (.ty (.borrow true targets)) bl →
    store.loc (.deref (.var x)) = some updated →
    store.slotAt updated = some updatedSlot →
    ValidPartialValue store updatedSlot.value updatedTy →
    (∀ y envSlot,
      envCoarse.slotAt y = some envSlot →
      VariableProjection y = updated →
        newSlot.lifetime = envSlot.lifetime) →
      ConcreteRuntimeRootsSafe (store.update updated newSlot) envCoarse := by
  intro hmap hroots hnewSafe hprov hsafe hsource hupdated hupdatedSlot
    hupdatedValid hlifetime
  refine ConcreteRuntimeRootsSafe.update_of_not_below_invalidated
    hroots hnewSafe hlifetime ?_
  intro y envSlot value henvSlot hstoreSlot hyUpdated
  by_cases hyx : y = x
  · subst hyx
    intro hinvalid
    rcases LValTyping.var_inv hsource with
      ⟨sourceSlot, hsourceSlot, hsourceTy, hsourceLifetime⟩
    have henvSlotEq : envSlot = sourceSlot :=
      Option.some.inj (henvSlot.symm.trans hsourceSlot)
    subst envSlot
    rcases hsafe.2 y sourceSlot hsourceSlot with
      ⟨sourceValue, hsourceStore, hsourceValid⟩
    cases sourceSlot with
    | mk sourceTy sourceLifetime =>
    cases hsourceTy
    cases hsourceLifetime
    cases hsourceValid with
    | @borrow borrowedLocation _mutable _targets selected hmem hselectedLoc =>
    have hvalueEq :
        value =
          .value (.ref { location := borrowedLocation, owner := false }) := by
      exact (congrArg StoreSlot.value
        (Option.some.inj (hsourceStore.symm.trans hstoreSlot))).symm
    have hsourceStore' :
        store.slotAt (Location.var y) =
          some {
            value := .value (.ref
              { location := borrowedLocation, owner := false }),
            lifetime := sourceLifetime } := by
      simpa [VariableProjection] using hsourceStore
    have hborrowedEq : borrowedLocation = updated := by
      simpa [ProgramStore.loc, VariableProjection, hsourceStore'] using
        hupdated
    have hinvalidBorrow :
        RuntimeValueBorrowInvalidatedBelow store
          (.value (.ref { location := borrowedLocation, owner := false }))
          updated := by
      simpa [hvalueEq] using hinvalid
    have hinvalidUpdated :
        RuntimeValueBorrowInvalidatedBelow store
          (.value (.ref { location := updated, owner := false }))
          updated := by
      simpa [hborrowedEq] using hinvalidBorrow
    have hbelow :
        ProgramStore.OwnsTransitively store updated updated :=
      (RuntimeValueBorrowInvalidatedBelow.borrow_iff).mp hinvalidUpdated
    exact ValidPartialValue.no_storage_ownership_cycle hupdatedSlot
      hupdatedValid hbelow
  · exact hprov.not_below_invalidated_of_var_join hmap hsource hupdated
      hyx hstoreSlot

/-- Safe-abstraction wrapper for
`ConcreteRuntimeBorrowProvenance.not_below_invalidated_of_validRoot`.

For any live root distinct from the owner of the `&mut` source, the concrete
provenance registry rules out the below-root borrow footprint that an assignment
drop would invalidate.
-/
theorem ConcreteRuntimeBorrowProvenance.not_below_invalidated_of_envRoot
    {store : ProgramStore} {env : Env} {source : LVal}
    {targets : List LVal} {bl : Lifetime} {leaf : Location} :
    ConcreteRuntimeBorrowProvenance store env →
    StoreOwnersAllocated store →
    store ∼ₛ env →
    LValTyping env source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    ∀ z zSlot value,
      z ≠ LVal.base source →
      env.slotAt z = some zSlot →
      store.slotAt (VariableProjection z) =
        some { value := value, lifetime := zSlot.lifetime } →
        ¬ RuntimeValueBorrowInvalidatedBelow store value leaf := by
  intro hprov hallocated hsafe hsource hleaf z zSlot value hzNe hzSlot hstoreSlot
  rcases hsafe.2 z zSlot hzSlot with ⟨safeValue, hsafeSlot, hvalid⟩
  have hvalueEq : safeValue = value := by
    have hslotEq :
        StoreSlot.mk safeValue zSlot.lifetime =
          StoreSlot.mk value zSlot.lifetime :=
      Option.some.inj (hsafeSlot.symm.trans hstoreSlot)
    exact congrArg StoreSlot.value hslotEq
  subst hvalueEq
  exact hprov.not_below_invalidated_of_validRoot hallocated hsafe hsource
    hleaf hzNe hzSlot hstoreSlot hvalid

/-- Concrete provenance supplies the cross-root frame for updating the concrete
pointee of a live `&mut`.

The remaining caller-supplied premise is the owner-root case
`x = LVal.base source`: provenance deliberately does not constrain the owner of
the mutable borrow itself.  All other live roots are discharged by the concrete
registry, which rules out actual runtime references into the old subtree below
the written leaf. -/
theorem ConcreteRuntimeRootsSafe.update_of_mut_borrow_provenance
    {store : ProgramStore} {env : Env} {source : LVal}
    {targets : List LVal} {bl : Lifetime}
    {updated : Location} {newSlot : StoreSlot} :
    ConcreteRuntimeRootsSafe store env →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    ConcreteRuntimeBorrowProvenance store env →
    StoreOwnersAllocated store →
    store ∼ₛ env →
    LValTyping env source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some updated →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      VariableProjection x = updated →
        newSlot.lifetime = envSlot.lifetime) →
    (∀ x envSlot value,
      x = LVal.base source →
      env.slotAt x = some envSlot →
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } →
      VariableProjection x ≠ updated →
        ¬ RuntimeValueBorrowInvalidatedBelow store value updated) →
      ConcreteRuntimeRootsSafe (store.update updated newSlot) env := by
  intro hroots hnewSafe hprov hallocated hsafe hsource hupdated
    hlifetime howner
  refine ConcreteRuntimeRootsSafe.update_of_not_below_invalidated
    hroots hnewSafe hlifetime ?_
  intro x envSlot value henvSlot hstoreSlot hxUpdated
  by_cases hxOwner : x = LVal.base source
  · exact howner x envSlot value hxOwner henvSlot hstoreSlot hxUpdated
  · exact hprov.not_below_invalidated_of_envRoot hallocated hsafe hsource
      hupdated x envSlot value hxOwner henvSlot hstoreSlot

/-- Concrete provenance restricted to writable gates supplies the cross-root
frame for updating the concrete pointee of the writable mutable-borrow source.

The remaining caller-supplied premise is the owner-root case
`x = LVal.base source`: provenance deliberately does not constrain the owner of
the mutable borrow itself. -/
theorem ConcreteRuntimeRootsSafe.update_of_mut_borrow_writableProvenance
    {store : ProgramStore} {env : Env} {source : LVal}
    {updated : Location} {newSlot : StoreSlot} :
    ConcreteRuntimeRootsSafe store env →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    ConcreteRuntimeWritableBorrowProvenance store env →
    RuntimeWritableMutGate store env source updated →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      VariableProjection x = updated →
        newSlot.lifetime = envSlot.lifetime) →
    (∀ x envSlot value,
      x = LVal.base source →
      env.slotAt x = some envSlot →
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } →
      VariableProjection x ≠ updated →
        ¬ RuntimeValueBorrowInvalidatedBelow store value updated) →
      ConcreteRuntimeRootsSafe (store.update updated newSlot) env := by
  intro hroots hnewSafe hprov hgate hlifetime howner
  refine ConcreteRuntimeRootsSafe.update_of_not_below_invalidated
    hroots hnewSafe hlifetime ?_
  intro x envSlot value henvSlot hstoreSlot hxUpdated
  by_cases hxOwner : x = LVal.base source
  · exact howner x envSlot value hxOwner henvSlot hstoreSlot hxUpdated
  · exact hprov.not_below_invalidated_of_writableGate hgate hxOwner
      hstoreSlot

/-- Concrete root update frame for assignment through a live `&mut` whose
typing gate is observed in a joined/coarser environment.

Cross-root below-invalidation is discharged by the branch/fine provenance
registry after pulling the concrete mutable-borrow gate back through
`hgate`.  The owner-root case remains caller-supplied, as in
`ConcreteRuntimeRootsSafe.update_of_mut_borrow_provenance`, because provenance
does not constrain the mutable borrow's own owner. -/
theorem ConcreteRuntimeRootsSafe.update_of_mut_borrow_provenance_gate
    {store : ProgramStore} {envFine envCoarse : Env} {source : LVal}
    {targets : List LVal} {bl : Lifetime}
    {updated : Location} {newSlot : StoreSlot} :
    RuntimeLValMutGatePullback store envFine envCoarse →
    ConcreteRuntimeRootsSafe store envCoarse →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    ConcreteRuntimeBorrowProvenance store envFine →
    LValTyping envCoarse source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some updated →
    (∀ x envSlot,
      envCoarse.slotAt x = some envSlot →
      VariableProjection x = updated →
        newSlot.lifetime = envSlot.lifetime) →
    (∀ x envSlot value,
      x = LVal.base source →
      envCoarse.slotAt x = some envSlot →
      store.slotAt (VariableProjection x) =
        some { value := value, lifetime := envSlot.lifetime } →
      VariableProjection x ≠ updated →
        ¬ RuntimeValueBorrowInvalidatedBelow store value updated) →
      ConcreteRuntimeRootsSafe (store.update updated newSlot) envCoarse := by
  intro hgate hroots hnewSafe hprov hsource hupdated hlifetime howner
  refine ConcreteRuntimeRootsSafe.update_of_not_below_invalidated
    hroots hnewSafe hlifetime ?_
  intro x envSlot value henvSlot hstoreSlot hxUpdated
  by_cases hxOwner : x = LVal.base source
  · exact howner x envSlot value hxOwner henvSlot hstoreSlot hxUpdated
  · exact hprov.not_below_invalidated_of_join hgate hsource hupdated
      hxOwner hstoreSlot

/-- Runtime provenance can be extended with an independently exclusive registry
without changing the environment coverage it already had. -/
theorem RuntimeBorrowProvenance.append_exclusive {store : ProgramStore}
    {env : Env} {extra : List (Location × Name)}
    (hprov : RuntimeBorrowProvenance store env)
    (hextra : MutRegistryExclusive store extra) :
    RuntimeBorrowProvenance store env := by
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R ++ extra, hcover.append_right, hexcl.append hextra⟩

/-- Install provenance for a freshly-added root.  Old-root mutable-borrow
coverage is transported back through the declaration coherence obligation; all
new-root coverage is supplied by the caller, typically from the RHS value's
exact registry. -/
theorem RuntimeBorrowProvenance.install_fresh_root
    {store : ProgramStore} {env : Env} {x : Name} {ty : Ty}
    {lifetime : Lifetime} {extra : List (Location × Name)}
    (hpostOld : RuntimeBorrowProvenance store env)
    (hcoh : FreshUpdateCoherenceObligations env x ty lifetime)
    (hextra : MutRegistryExclusive store extra)
    (hnewCover :
      ∀ source targets bl leaf,
        LVal.base source = x →
        LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
          source (.ty (.borrow true targets)) bl →
        store.loc (.deref source) = some leaf →
        (leaf, x) ∈ extra) :
    RuntimeBorrowProvenance store
      (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  rcases hpostOld with ⟨R, hcover, hexcl⟩
  refine ⟨R ++ extra, ?_, hexcl.append hextra⟩
  intro source targets bl leaf hsource hleaf
  by_cases hbase : LVal.base source = x
  · exact List.mem_append.mpr
      (Or.inr (by simpa [hbase] using hnewCover source targets bl leaf hbase hsource hleaf))
  · rcases hcoh.old_root_transport hbase hsource with
      ⟨oldBl, hsourceOld⟩
    exact List.mem_append.mpr
      (Or.inl (hcover source targets oldBl leaf hsourceOld hleaf))

/-- Install provenance for an assignment/write result environment.  Old-root
coverage is transported through the rule-carried write coherence obligation;
written-root coverage is supplied separately by the RHS value installation
argument. -/
theorem RuntimeBorrowProvenance.install_write_root
    {store : ProgramStore} {env result : Env} {writeBase : Name}
    {extra : List (Location × Name)}
    (hpostOld : RuntimeBorrowProvenance store env)
    (hcoh : EnvWriteCoherenceObligations env result writeBase)
    (hextra : MutRegistryExclusive store extra)
    (hnewCover :
      ∀ source targets bl leaf,
        LVal.base source = writeBase →
        LValTyping result source (.ty (.borrow true targets)) bl →
        store.loc (.deref source) = some leaf →
        (leaf, writeBase) ∈ extra) :
    RuntimeBorrowProvenance store result := by
  rcases hpostOld with ⟨R, hcover, hexcl⟩
  refine ⟨R ++ extra, ?_, hexcl.append hextra⟩
  intro source targets bl leaf hsource hleaf
  by_cases hbase : LVal.base source = writeBase
  · exact List.mem_append.mpr
      (Or.inr (by simpa [hbase] using hnewCover source targets bl leaf hbase hsource hleaf))
  · rcases (hcoh.old_root_transport hbase hsource).1 with
      ⟨oldBl, hsourceOld⟩
    exact List.mem_append.mpr
      (Or.inl (hcover source targets oldBl leaf hsourceOld hleaf))

/-- A covered, exclusive registry supplies the deref-write frame invariant. -/
theorem MutRegistryCovers.mutLeafExclusive {store : ProgramStore} {env : Env}
    {R : List (Location × Name)} {source : LVal} {targets : List LVal}
    {bl : Lifetime} {leaf : Location} :
    MutRegistryCovers store env R →
    MutRegistryExclusive store R →
    LValTyping env source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    MutLeafExclusive store env source leaf := by
  intro hcover hexcl hsource hleaf
  exact hexcl.mutLeafExclusive (hcover source targets bl leaf hsource hleaf)

/-- Registry coverage transports from a branch env to a coarser/join env once
the `&mut` typing gate is pulled back.  The registry entry itself is runtime
data `(leaf, base source)`: it does not mention the widened static target list. -/
theorem MutRegistryCovers.of_mutGatePullback {store : ProgramStore}
    {envFine envCoarse : Env} {R : List (Location × Name)}
    (hgate : RuntimeLValMutGatePullback store envFine envCoarse)
    (hcover : MutRegistryCovers store envFine R) :
    MutRegistryCovers store envCoarse R := by
  intro source targets bl leaf hsource hleaf
  rcases hgate source targets bl leaf hsource hleaf with
    ⟨targetsFine, blFine, hsourceFine⟩
  exact hcover source targetsFine blFine leaf hsourceFine hleaf

/-- Erasing a store slot preserves registry coverage: any mutable borrow whose
dereference still resolves after the erase resolved to the same leaf before the
erase, so the old registry entry still covers it. -/
theorem MutRegistryCovers.erase {store : ProgramStore} {env : Env}
    {R : List (Location × Name)} {erased : Location}
    (hcover : MutRegistryCovers store env R) :
    MutRegistryCovers (store.erase erased) env R := by
  intro source targets bl leaf hsource hleaf
  exact hcover source targets bl leaf hsource
    (RuntimeFrame.loc_erase_some_to_store hleaf)

/-- Updating a fresh location preserves registry coverage for an unchanged
environment, assuming the old store safely realizes the well-formed environment.

The runtime dereference of a typed mutable-borrow source already resolved before
the update: coherence gives a target-list typing for the source borrow, and
`lvalTyping_defined_location` gives allocated storage for the selected concrete
target.  A fresh update therefore cannot be the newly observed dereference
location, and the old registry entry still covers it. -/
theorem MutRegistryCovers.update_fresh_of_wellFormed {store : ProgramStore}
    {env : Env} {R : List (Location × Name)} {updated : Location}
    {newSlot : StoreSlot} {current : Lifetime}
    (hwell : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (hfresh : store.fresh updated)
    (hcover : MutRegistryCovers store env R) :
    MutRegistryCovers (store.update updated newSlot) env R := by
  intro source targets bl leaf hsource hleaf
  rcases hwell.2.2.1 source true targets bl hsource with
    ⟨targetTy, targetLifetime, htargets⟩
  have hsourceAbs :
      LValLocationAbstraction store source (.ty (.borrow true targets)) :=
    lvalTyping_defined_location hwell hsafe hsource
  have htargetsAbs :
      ∀ target ty lifetime,
        LValTyping env target (.ty ty) lifetime →
        LValLocationAbstraction store target (.ty ty) := by
    intro target ty lifetime htarget
    exact lvalTyping_defined_location hwell hsafe htarget
  rcases location_borrow_selected_target hsourceAbs htargets htargetsAbs with
    ⟨selected, selectedTy, selectedLifetime, _hselectedMem, _hselectedTyping,
      hselectedAbs, _hstrengthens⟩
  rcases hselectedAbs with
    ⟨oldLeaf, oldLeafSlot, hlocOld, _hslotOld, _hvalidOld⟩
  have hlocUpdated :
      (store.update updated newSlot).loc (.deref source) = some oldLeaf :=
    loc_update_of_loc hfresh hlocOld
  have hleafEq : leaf = oldLeaf :=
    Option.some.inj (hleaf.symm.trans hlocUpdated)
  simpa [hleafEq] using hcover source targets bl oldLeaf hsource hlocOld

/-- Fresh-update coverage with the fresh location filtered out of the registry.
The filter is harmless: any typed mutable-borrow dereference observed after the
fresh update already resolved to an allocated old location before the update. -/
theorem MutRegistryCovers.update_fresh_filter_of_wellFormed
    {store : ProgramStore} {env : Env} {R : List (Location × Name)}
    {updated : Location} {newSlot : StoreSlot} {current : Lifetime}
    (hwell : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (hfresh : store.fresh updated)
    (hcover : MutRegistryCovers store env R) :
    MutRegistryCovers (store.update updated newSlot) env
      (R.filter (fun entry => decide (entry.1 ≠ updated))) := by
  intro source targets bl leaf hsource hleaf
  rcases hwell.2.2.1 source true targets bl hsource with
    ⟨targetTy, targetLifetime, htargets⟩
  have hsourceAbs :
      LValLocationAbstraction store source (.ty (.borrow true targets)) :=
    lvalTyping_defined_location hwell hsafe hsource
  have htargetsAbs :
      ∀ target ty lifetime,
        LValTyping env target (.ty ty) lifetime →
        LValLocationAbstraction store target (.ty ty) := by
    intro target ty lifetime htarget
    exact lvalTyping_defined_location hwell hsafe htarget
  rcases location_borrow_selected_target hsourceAbs htargets htargetsAbs with
    ⟨selected, selectedTy, selectedLifetime, _hselectedMem, _hselectedTyping,
      hselectedAbs, _hstrengthens⟩
  rcases hselectedAbs with
    ⟨oldLeaf, oldLeafSlot, hlocOld, hslotOld, _hvalidOld⟩
  have hlocUpdated :
      (store.update updated newSlot).loc (.deref source) = some oldLeaf :=
    loc_update_of_loc hfresh hlocOld
  have hleafEq : leaf = oldLeaf :=
    Option.some.inj (hleaf.symm.trans hlocUpdated)
  have hmemOld : (oldLeaf, LVal.base source) ∈ R :=
    hcover source targets bl oldLeaf hsource hlocOld
  have holdNe : oldLeaf ≠ updated := by
    intro holdEq
    subst holdEq
    rw [ProgramStore.fresh] at hfresh
    rw [hfresh] at hslotOld
    cases hslotOld
  have hmemFiltered :
      (oldLeaf, LVal.base source) ∈
        R.filter (fun entry => decide (entry.1 ≠ updated)) := by
    rw [List.mem_filter]
    exact ⟨hmemOld, decide_eq_true holdNe⟩
  simpa [hleafEq] using hmemFiltered

/-- Updating one store slot to `undef` preserves registry coverage against the
same environment: a successful mutable-borrow dereference after the update
already succeeded before the update. -/
theorem MutRegistryCovers.update_undef {store : ProgramStore} {env : Env}
    {R : List (Location × Name)} {updated : Location}
    {updatedLifetime : Lifetime}
    (hcover : MutRegistryCovers store env R) :
    MutRegistryCovers
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env R := by
  intro source targets bl leaf hsource hleaf
  exact hcover source targets bl leaf hsource
    (RuntimeFrame.loc_update_undef_some_to_store hleaf)

/-- Registry coverage survives a move paired with the concrete runtime update
that writes `undef`.  Any surviving mutable-borrow typing in the moved
environment transports back to the pre-move environment; a typing rooted at the
struck variable would have an `undef`/box-`undef` shape and therefore cannot be a
defined borrow. -/
theorem MutRegistryCovers.move_update_undef {store : ProgramStore}
    {env env' : Env} {R : List (Location × Name)} {moved : LVal}
    {updated : Location} {updatedLifetime : Lifetime}
    (hcover : MutRegistryCovers store env R)
    (hmove : EnvMove env moved env')
    (hnotWrite : ¬ WriteProhibited env moved) :
    MutRegistryCovers
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env' (R.filter (fun entry => entry.2 != LVal.base moved)) := by
  rcases hmove with ⟨moveSlot, struck, hmoveSlot, hstrike, henv'⟩
  subst henv'
  intro source targets bl leaf hsource hleaf
  have hsourceEnv :
      LValTyping env source (.ty (.borrow true targets)) bl := by
    by_cases hconflict : source ⋈ moved
    · have hshape :=
        LValTyping.isBoxUndef_of_base_moved hmoveSlot hstrike hsource
          (by simpa [PathConflicts] using hconflict)
      simp [IsBoxUndef] at hshape
    · have hrestore :
          (env.update (LVal.base moved) { moveSlot with ty := struck }).update
              (LVal.base moved) moveSlot = env := by
        obtain ⟨g⟩ := env
        simp only [Env.update]
        congr 1
        funext y
        by_cases hy : y = LVal.base moved
        · subst hy
          simpa using hmoveSlot.symm
        · simp [hy]
      have hnotWriteVarEnv : ¬ WriteProhibited env (.var (LVal.base moved)) :=
        not_writeProhibited_var_base hnotWrite
      have hnotWriteVar :
          ¬ WriteProhibited
            ((env.update (LVal.base moved) { moveSlot with ty := struck }).update
              (LVal.base moved) moveSlot)
            (.var (LVal.base moved)) := by
        rw [hrestore]
        exact hnotWriteVarEnv
      have hsourceRestore :
          LValTyping
            ((env.update (LVal.base moved) { moveSlot with ty := struck }).update
              (LVal.base moved) moveSlot)
            source (.ty (.borrow true targets)) bl :=
        (LValTyping.update_of_not_pathConflicts hnotWriteVar).1 hsource
          (by simpa [PathConflicts, LVal.base] using hconflict)
      rwa [hrestore] at hsourceRestore
  have hsourceMem :
      (leaf, LVal.base source) ∈ R :=
    hcover source targets bl leaf hsourceEnv
      (RuntimeFrame.loc_update_undef_some_to_store hleaf)
  have hbaseNe : LVal.base source ≠ LVal.base moved := by
    intro hbase
    have hconflict : source ⋈ moved := by
      simpa [PathConflicts] using hbase
    have hshape :=
      LValTyping.isBoxUndef_of_base_moved hmoveSlot hstrike hsource
        (by simpa [PathConflicts] using hconflict)
    simp [IsBoxUndef] at hshape
  exact List.mem_filter.mpr ⟨hsourceMem, by simp [hbaseNe]⟩

/-- Existential registry provenance supplies the deref-write frame invariant. -/
theorem RuntimeBorrowProvenance.mutLeafExclusive {store : ProgramStore}
    {env : Env} {source : LVal} {targets : List LVal} {bl : Lifetime}
    {leaf : Location} :
    RuntimeBorrowProvenance store env →
    LValTyping env source (.ty (.borrow true targets)) bl →
    store.loc (.deref source) = some leaf →
    MutLeafExclusive store env source leaf := by
  intro hprov hsource hleaf
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact hcover.mutLeafExclusive hexcl hsource hleaf

/-- Runtime provenance survives erasing one store slot.  Erasure can only remove
runtime reads/resolutions, never create new mutable-borrow coverage or
exclusivity obligations. -/
theorem RuntimeBorrowProvenance.erase {store : ProgramStore} {env : Env}
    {erased : Location} :
    RuntimeBorrowProvenance store env →
    RuntimeBorrowProvenance (store.erase erased) env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.erase, hexcl.erase⟩

/-- Runtime provenance survives updating one store slot to `undef` when the
typing environment is unchanged. -/
theorem RuntimeBorrowProvenance.update_undef {store : ProgramStore}
    {env : Env} {updated : Location} {updatedLifetime : Lifetime} :
    RuntimeBorrowProvenance store env →
    RuntimeBorrowProvenance
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.update_undef, hexcl.update_undef⟩

/-- Runtime provenance survives a move when the runtime write is the matching
concrete `undef` update. -/
theorem RuntimeBorrowProvenance.move_update_undef {store : ProgramStore}
    {env env' : Env} {moved : LVal} {updated : Location}
    {updatedLifetime : Lifetime}
    (hmove : EnvMove env moved env')
    (hnotWrite : ¬ WriteProhibited env moved) :
    RuntimeBorrowProvenance store env →
    RuntimeBorrowProvenance
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env' := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R.filter (fun entry => entry.2 != LVal.base moved),
    hcover.move_update_undef hmove hnotWrite,
    (hexcl.update_undef).filter _⟩

/-- Runtime provenance is preserved by dropping values.  Dropping either leaves
the store unchanged or erases owner locations; erasure cannot create new
realized borrow reads or new mutable-borrow resolutions. -/
theorem RuntimeBorrowProvenance.drops {store store' : ProgramStore}
    {env : Env} {values : List PartialValue} :
    Drops store values store' →
    RuntimeBorrowProvenance store env →
    RuntimeBorrowProvenance store' env := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro hprov
      exact hprov
  | nonOwner _hnonOwner _hdrops ih =>
      intro hprov
      exact ih hprov
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hprov
      exact ih hprov
  | ownerPresent _howner _hslot _hdrops ih =>
      intro hprov
      exact ih hprov.erase

/-- Runtime provenance survives a lifetime drop paired with the matching
environment lifetime drop. -/
theorem RuntimeBorrowProvenance.dropsLifetime {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    DropsLifetime store lifetime store' →
    RuntimeBorrowProvenance store env →
    RuntimeBorrowProvenance store' (env.dropLifetime lifetime) := by
  intro hdrops hprov
  cases hdrops with
  | intro _hdropSet hdrops =>
      rcases RuntimeBorrowProvenance.drops hdrops hprov with
        ⟨R, hcover, hexcl⟩
      refine ⟨R, ?_, hexcl⟩
      intro source targets bl leaf hsource hleaf
      exact hcover source targets bl leaf
        (LValTyping.of_dropLifetime hsource) hleaf

/-- Runtime provenance follows the single `R-BlockB` drop hidden inside a
singleton-value block multistep. -/
theorem RuntimeBorrowProvenance.blockBValueMultiStep
    {store finalStore : ProgramStore} {env : Env}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    RuntimeBorrowProvenance store env →
    RuntimeBorrowProvenance finalStore (env.dropLifetime blockLifetime) := by
  intro hmulti hprov
  cases hmulti with
  | trans hstep hrest =>
      cases hstep with
      | blockA hvalueStep =>
          exact False.elim (value_no_step hvalueStep)
      | blockB hdrops =>
          rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
          subst hstore
          cases hterm
          exact RuntimeBorrowProvenance.dropsLifetime hdrops hprov

/-- Runtime borrow provenance transports through a join/coarsening with the same
store and registry.  Only coverage needs the `&mut` gate pullback; exclusivity is
store-only and therefore unchanged by target-list widening. -/
theorem RuntimeBorrowProvenance.of_mutGatePullback {store : ProgramStore}
    {envFine envCoarse : Env}
    (hgate : RuntimeLValMutGatePullback store envFine envCoarse)
    (hprov : RuntimeBorrowProvenance store envFine) :
    RuntimeBorrowProvenance store envCoarse := by
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.of_mutGatePullback hgate, hexcl⟩

/-- Variable-held mutable borrows consume branch provenance after a join without
inspecting the join-widened target list.  The coarse variable typing is pulled
back to the fine env only to recover the same concrete registry entry
`(leaf, x)`; the exclusive kill is store/registry-only and is then valid for the
coarse env as well. -/
theorem RuntimeBorrowProvenance.var_mutLeafExclusive_of_strengthening
    {store : ProgramStore} {envFine envCoarse : Env} {x : Name}
    {targets : List LVal} {bl : Lifetime} {leaf : Location}
    (hstr : EnvSameShapeStrengthening envFine envCoarse)
    (hprov : RuntimeBorrowProvenance store envFine)
    (hcoarse : LValTyping envCoarse (.var x) (.ty (.borrow true targets)) bl)
    (hleaf : store.loc (.deref (.var x)) = some leaf) :
    MutLeafExclusive store envCoarse (.var x) leaf := by
  rcases hprov with ⟨R, hcover, hexcl⟩
  rcases LValTyping.var_inv hcoarse with ⟨slot, hcoarseSlot, hslotTy, hslotLife⟩
  cases slot with
  | mk slotTy slotLifetime =>
      cases hslotTy
      cases hslotLife
      rcases lvalMutVar_pullback_of_strengthening hstr hcoarseSlot with
        ⟨targetsFine, blFine, hfine⟩
      exact hexcl.mutLeafExclusive
        (hcover (.var x) targetsFine blFine leaf hfine hleaf)

/-- Registry coverage is monotone under lifetime dropping: any mutable borrow
still typeable after `dropLifetime` was already typeable before the drop, so the
same concrete registry entry covers it. -/
theorem MutRegistryCovers.dropLifetime {store : ProgramStore} {env : Env}
    {R : List (Location × Name)} {lifetime : Lifetime}
    (hcover : MutRegistryCovers store env R) :
    MutRegistryCovers store (env.dropLifetime lifetime) R := by
  intro source targets bl leaf hsource hleaf
  exact hcover source targets bl leaf (LValTyping.of_dropLifetime hsource)
    hleaf

/-- Concrete runtime provenance can be extended with an independently exclusive
registry without changing environment coverage. -/
theorem ConcreteRuntimeBorrowProvenance.append_exclusive {store : ProgramStore}
    {env : Env} {extra : List (Location × Name)}
    (hprov : ConcreteRuntimeBorrowProvenance store env)
    (hextra : ConcreteMutRegistryExclusive store extra) :
    ConcreteRuntimeBorrowProvenance store env := by
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R ++ extra, hcover.append_right, hexcl.append hextra⟩

/-- Concrete provenance survives erasing one store slot. -/
theorem ConcreteRuntimeBorrowProvenance.erase {store : ProgramStore} {env : Env}
    {erased : Location} :
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeBorrowProvenance (store.erase erased) env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.erase, hexcl.erase⟩

/-- Concrete provenance survives updating one store slot to `undef` when the
typing environment is unchanged. -/
theorem ConcreteRuntimeBorrowProvenance.update_undef {store : ProgramStore}
    {env : Env} {updated : Location} {updatedLifetime : Lifetime} :
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeBorrowProvenance
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.update_undef, hexcl.update_undef⟩

/-- Concrete provenance for old roots survives installing a fresh variable when
the installed value is concrete-safe against every surviving old registered
mutable-borrow leaf.  The side condition is intentionally store/runtime-only:
it talks about concrete below-root invalidation, not joined target-list
alternatives. -/
theorem ConcreteRuntimeBorrowProvenance.update_fresh_var_filter_of_wellFormed
    {store : ProgramStore} {env : Env} {current : Lifetime}
    {x : Name} {newSlot : StoreSlot}
    (hwell : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.var x))
    (hnew :
      ∀ leaf owner,
        leaf ≠ .var x →
        x ≠ owner →
          ¬ RuntimeValueBorrowInvalidatedBelow
            (store.update (.var x) newSlot) newSlot.value leaf) :
    ConcreteRuntimeBorrowProvenance store env →
      ConcreteRuntimeBorrowProvenance (store.update (.var x) newSlot) env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R.filter (fun entry => decide (entry.1 ≠ .var x)),
    MutRegistryCovers.update_fresh_filter_of_wellFormed hwell hsafe hfresh hcover,
    ConcreteMutRegistryExclusive.update_fresh_var_filter
      hallocated hfresh hexcl
      (fun leaf owner _hmem hleaf howner =>
        hnew leaf owner hleaf howner)⟩

/-- Declaration form of
`ConcreteRuntimeBorrowProvenance.update_fresh_var_filter_of_wellFormed`. -/
theorem ConcreteRuntimeBorrowProvenance.declare_old_roots_of_not_below_invalidated
    {store : ProgramStore} {env : Env} {current lifetime : Lifetime}
    {x : Name} {value : Value}
    (hwell : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.var x))
    (hnew :
      ∀ leaf owner,
        leaf ≠ .var x →
        x ≠ owner →
          ¬ RuntimeValueBorrowInvalidatedBelow
            (store.declare x lifetime value) (.value value) leaf) :
    ConcreteRuntimeBorrowProvenance store env →
      ConcreteRuntimeBorrowProvenance (store.declare x lifetime value) env := by
  intro hprov
  simpa [ProgramStore.declare] using
    ConcreteRuntimeBorrowProvenance.update_fresh_var_filter_of_wellFormed
      (store := store) (env := env) (current := current)
      (x := x) (newSlot := { value := .value value, lifetime := lifetime })
      hwell hsafe hallocated hfresh
      (by
        intro leaf owner hleaf howner
        simpa [ProgramStore.declare] using hnew leaf owner hleaf howner)
      hprov

/-- Concrete provenance survives a move when the runtime write is the matching
concrete `undef` update. -/
theorem ConcreteRuntimeBorrowProvenance.move_update_undef {store : ProgramStore}
    {env env' : Env} {moved : LVal} {updated : Location}
    {updatedLifetime : Lifetime}
    (hmove : EnvMove env moved env')
    (hnotWrite : ¬ WriteProhibited env moved) :
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeBorrowProvenance
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env' := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R.filter (fun entry => entry.2 != LVal.base moved),
    hcover.move_update_undef hmove hnotWrite,
    (hexcl.update_undef).filter _⟩

/-- Install concrete provenance for a freshly-added root.  Old-root mutable
borrow coverage is transported back through the declaration coherence
obligation; all new-root coverage is supplied by the caller from the installed
value's registry. -/
theorem ConcreteRuntimeBorrowProvenance.install_fresh_root
    {store : ProgramStore} {env : Env} {x : Name} {ty : Ty}
    {lifetime : Lifetime} {extra : List (Location × Name)}
    (hpostOld : ConcreteRuntimeBorrowProvenance store env)
    (hcoh : FreshUpdateCoherenceObligations env x ty lifetime)
    (hextra : ConcreteMutRegistryExclusive store extra)
    (hnewCover :
      ∀ source targets bl leaf,
        LVal.base source = x →
        LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
          source (.ty (.borrow true targets)) bl →
        store.loc (.deref source) = some leaf →
        (leaf, x) ∈ extra) :
    ConcreteRuntimeBorrowProvenance store
      (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  rcases hpostOld with ⟨R, hcover, hexcl⟩
  refine ⟨R ++ extra, ?_, hexcl.append hextra⟩
  intro source targets bl leaf hsource hleaf
  by_cases hbase : LVal.base source = x
  · exact List.mem_append.mpr
      (Or.inr
        (by simpa [hbase] using hnewCover source targets bl leaf hbase hsource hleaf))
  · rcases hcoh.old_root_transport hbase hsource with
      ⟨oldBl, hsourceOld⟩
    exact List.mem_append.mpr
      (Or.inl (hcover source targets oldBl leaf hsourceOld hleaf))

/-- Install concrete provenance for a fresh root from the value-scoped
installation package.  This wrapper keeps the declaration case honest: the RHS
value must supply its own concrete mutable-borrow registry before it can become
an environment root. -/
theorem ConcreteRuntimeBorrowProvenance.install_fresh_root_of_valueProvenance
    {store : ProgramStore} {env : Env} {x : Name} {value : Value}
    {ty : Ty} {lifetime : Lifetime}
    (hpostOld : ConcreteRuntimeBorrowProvenance store env)
    (hcoh : FreshUpdateCoherenceObligations env x ty lifetime)
    (hvalueProv :
      ConcreteRuntimeValueInstallProvenance store env x value ty lifetime) :
    ConcreteRuntimeBorrowProvenance store
      (env.update x { ty := .ty ty, lifetime := lifetime }) := by
  rcases hvalueProv with ⟨R, _hexact, hexcl, hcover⟩
  exact ConcreteRuntimeBorrowProvenance.install_fresh_root
    hpostOld hcoh hexcl hcover

/-- Install concrete provenance for an assignment/write result environment.
Old-root coverage is transported through the rule-carried write coherence
obligation; written-root coverage is supplied separately by the RHS value
installation argument. -/
theorem ConcreteRuntimeBorrowProvenance.install_write_root
    {store : ProgramStore} {env result : Env} {writeBase : Name}
    {extra : List (Location × Name)}
    (hpostOld : ConcreteRuntimeBorrowProvenance store env)
    (hcoh : EnvWriteCoherenceObligations env result writeBase)
    (hextra : ConcreteMutRegistryExclusive store extra)
    (hnewCover :
      ∀ source targets bl leaf,
        LVal.base source = writeBase →
        LValTyping result source (.ty (.borrow true targets)) bl →
        store.loc (.deref source) = some leaf →
        (leaf, writeBase) ∈ extra) :
    ConcreteRuntimeBorrowProvenance store result := by
  rcases hpostOld with ⟨R, hcover, hexcl⟩
  refine ⟨R ++ extra, ?_, hexcl.append hextra⟩
  intro source targets bl leaf hsource hleaf
  by_cases hbase : LVal.base source = writeBase
  · exact List.mem_append.mpr
      (Or.inr
        (by simpa [hbase] using hnewCover source targets bl leaf hbase hsource hleaf))
  · rcases (hcoh.old_root_transport hbase hsource).1 with
      ⟨oldBl, hsourceOld⟩
    exact List.mem_append.mpr
      (Or.inl (hcover source targets oldBl leaf hsourceOld hleaf))

/-- Concrete provenance is preserved by dropping values. -/
theorem ConcreteRuntimeBorrowProvenance.drops {store store' : ProgramStore}
    {env : Env} {values : List PartialValue} :
    Drops store values store' →
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeBorrowProvenance store' env := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro hprov
      exact hprov
  | nonOwner _hnonOwner _hdrops ih =>
      intro hprov
      exact ih hprov
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hprov
      exact ih hprov
  | ownerPresent _howner _hslot _hdrops ih =>
      intro hprov
      exact ih hprov.erase

/-- Concrete provenance survives a lifetime drop paired with the matching
environment lifetime drop. -/
theorem ConcreteRuntimeBorrowProvenance.dropsLifetime
    {store store' : ProgramStore} {env : Env} {lifetime : Lifetime} :
    DropsLifetime store lifetime store' →
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeBorrowProvenance store' (env.dropLifetime lifetime) := by
  intro hdrops hprov
  cases hdrops with
  | intro _hdropSet hdrops =>
      rcases ConcreteRuntimeBorrowProvenance.drops hdrops hprov with
        ⟨R, hcover, hexcl⟩
      refine ⟨R, ?_, hexcl⟩
      intro source targets bl leaf hsource hleaf
      exact hcover source targets bl leaf
        (LValTyping.of_dropLifetime hsource) hleaf

/-- Concrete provenance follows the single `R-BlockB` drop hidden inside a
singleton-value block multistep. -/
theorem ConcreteRuntimeBorrowProvenance.blockBValueMultiStep
    {store finalStore : ProgramStore} {env : Env}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeBorrowProvenance finalStore
      (env.dropLifetime blockLifetime) := by
  intro hmulti hprov
  cases hmulti with
  | trans hstep hrest =>
      cases hstep with
      | blockA hvalueStep =>
          exact False.elim (value_no_step hvalueStep)
      | blockB hdrops =>
          rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
          subst hstore
          cases hterm
          exact ConcreteRuntimeBorrowProvenance.dropsLifetime hdrops hprov

/-- Concrete provenance transports through a join/coarsening with the same store
and registry. -/
theorem ConcreteRuntimeBorrowProvenance.of_mutGatePullback
    {store : ProgramStore} {envFine envCoarse : Env}
    (hgate : RuntimeLValMutGatePullback store envFine envCoarse)
    (hprov : ConcreteRuntimeBorrowProvenance store envFine) :
    ConcreteRuntimeBorrowProvenance store envCoarse := by
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.of_mutGatePullback hgate, hexcl⟩

/-- Concrete provenance is monotone under lifetime dropping. -/
theorem ConcreteRuntimeBorrowProvenance.dropLifetime {store : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeBorrowProvenance store (env.dropLifetime lifetime) := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.dropLifetime, hexcl⟩

/-- Concrete runtime provenance is unchanged by a value-tail multistep. -/
theorem ConcreteRuntimeBorrowProvenance.value_tail
    {store finalStore : ProgramStore}
    {env : Env} {lifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeBorrowProvenance finalStore env := by
  intro hmulti hprov
  rcases multistep_value_inv hmulti with ⟨hstore, _hterm⟩
  simpa [hstore] using hprov

/-- Concrete runtime provenance survives allocating a fresh heap box.  Coverage
keeps only old registered leaves; the fresh heap leaf cannot be needed for an
unchanged environment. -/
theorem ConcreteRuntimeBorrowProvenance.boxAt {store : ProgramStore}
    {env : Env} {current : Lifetime} {address : Nat} {value : Value}
    (hwell : WellFormedEnv env current)
    (hsafe : store ∼ₛ env)
    (hallocated : StoreOwnersAllocated store)
    (hfresh : store.fresh (.heap address)) :
    ConcreteRuntimeBorrowProvenance store env →
    ConcreteRuntimeBorrowProvenance (store.boxAt address value).1 env := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  refine ⟨R.filter (fun entry => decide (entry.1 ≠ .heap address)), ?_, ?_⟩
  · simpa [ProgramStore.boxAt] using
      MutRegistryCovers.update_fresh_filter_of_wellFormed
        hwell hsafe hfresh hcover
  · simpa [ProgramStore.boxAt] using
      ConcreteMutRegistryExclusive.update_fresh_heap_filter
        hallocated hfresh hexcl

/-- The empty environment has concrete runtime borrow provenance. -/
theorem ConcreteRuntimeBorrowProvenance.empty {store : ProgramStore} :
    ConcreteRuntimeBorrowProvenance store Env.empty := by
  refine ⟨[], ?_, ?_⟩
  · intro source targets bl leaf hsource _hleaf
    exact False.elim (lvalTyping_empty_false hsource)
  · intro leaf owner hmem _z _hz
    simp at hmem

/-- Terminal safety packaged with concrete runtime borrow provenance.

This is the join-friendly preservation package for the runtime-safety proof:
ordinary terminal safety keeps the usual validity/safe-abstraction/value facts,
while concrete provenance records only live `&mut` pointee locations and their
owners.  The provenance component is intentionally independent of joined target
list alternatives. -/
def TerminalStateSafeWithConcreteProvenance (store : ProgramStore)
    (value : Value) (env : Env) (ty : Ty) : Prop :=
  TerminalStateSafe store value env ty ∧
    ConcreteRuntimeBorrowProvenance store env

/-- Terminal safety with the concrete runtime-root claim plus the concrete
mutable-borrow provenance needed to continue through later writes.

The root component is the join-stable runtime-safety statement.  The provenance
component is deliberately kept separate: it is a write-frame invariant, not the
final safety claim. -/
def TerminalStateSafeWithConcreteRootsAndProvenance (store : ProgramStore)
    (value : Value) (env : Env) (ty : Ty) : Prop :=
  TerminalStateSafeWithConcreteRoots store value env ty ∧
    ConcreteRuntimeBorrowProvenance store env

/-- Forget the write-frame provenance and keep the concrete runtime roots. -/
theorem TerminalStateSafeWithConcreteRootsAndProvenance.toConcreteRoots
    {store : ProgramStore} {value : Value} {env : Env} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndProvenance store value env ty →
      TerminalStateSafeWithConcreteRoots store value env ty :=
  And.left

/-- Forget concrete root safety but keep the ordinary terminal facts and the
concrete mutable-borrow provenance. -/
theorem TerminalStateSafeWithConcreteRootsAndProvenance.toConcreteProvenance
    {store : ProgramStore} {value : Value} {env : Env} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndProvenance store value env ty →
      TerminalStateSafeWithConcreteProvenance store value env ty := by
  intro hterminal
  exact ⟨hterminal.1.1, hterminal.2⟩

/-- Value-tail composition for terminal concrete roots plus provenance. -/
theorem TerminalStateSafeWithConcreteRootsAndProvenance.value_tail
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndProvenance store value env ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    TerminalStateSafeWithConcreteRootsAndProvenance finalStore finalValue env ty := by
  intro hterminal htail
  exact ⟨hterminal.1.value_tail htail,
    ConcreteRuntimeBorrowProvenance.value_tail htail hterminal.2⟩

/-- Terminal concrete roots plus provenance transport through a join.

The root component is same-shape only: joined target-list alternatives do not
change the store locations held by runtime references.  The provenance component
uses the runtime mutable-gate pullback, so coverage is recovered only for
mutable-borrow gates that the concrete store can actually dereference. -/
theorem TerminalStateSafeWithConcreteRootsAndProvenance.strengthen_join
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hgate : RuntimeLValMutGatePullback finalStore branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithConcreteRootsAndProvenance
      finalStore finalValue branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithConcreteRootsAndProvenance
        finalStore finalValue joinEnv joinTy := by
  rcases hterminal with ⟨hterminalRoots, hprov⟩
  rcases TerminalStateSafeWithConcreteRoots.strengthen_join
      hcontained hcoherent hlinear hpreserved hmap hstrengthens
      hwellBranch hterminalRoots with
    ⟨hwellJoin, hterminalJoin⟩
  exact ⟨hwellJoin, hterminalJoin,
    ConcreteRuntimeBorrowProvenance.of_mutGatePullback hgate hprov⟩

/-- Forget concrete mutable-borrow provenance down to concrete root safety.

The provenance registry is stronger than what runtime safety through joins
needs.  This projection is the migration bridge: existing preservation branches
that still establish provenance can be consumed by the join-stable concrete-root
package instead. -/
theorem TerminalStateSafeWithConcreteProvenance.toConcreteRoots
    {store : ProgramStore} {value : Value} {env : Env} {ty : Ty}
    {current valueLifetime : Lifetime} :
    WellFormedEnv env current →
    WellFormedTy env ty valueLifetime →
    TerminalStateSafeWithConcreteProvenance store value env ty →
      TerminalStateSafeWithConcreteRoots store value env ty := by
  intro hwellEnv hwellTy hterminal
  exact ⟨hterminal.1, hterminal.1.concreteRuntimeRoots hwellEnv hwellTy⟩

/-- Value-tail composition for the concrete terminal package. -/
theorem TerminalStateSafeWithConcreteProvenance.value_tail
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    TerminalStateSafeWithConcreteProvenance store value env ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    TerminalStateSafeWithConcreteProvenance finalStore finalValue env ty := by
  intro hterminal htail
  exact ⟨preservation_value_tail_runtime hterminal.1 htail,
    ConcreteRuntimeBorrowProvenance.value_tail htail hterminal.2⟩

/-- The concrete terminal conclusion transports through a join.  The terminal
state facts use the existing same-shape strengthening proof; concrete provenance
uses only the runtime-realized mutable gate, so joined-in stale target-list
members do not create new obligations. -/
theorem TerminalStateSafeWithConcreteProvenance.strengthen_join
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hgate : RuntimeLValMutGatePullback finalStore branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithConcreteProvenance finalStore finalValue
      branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithConcreteProvenance finalStore finalValue joinEnv joinTy := by
  rcases hterminal with ⟨hterminalSafe, hprov⟩
  rcases TerminalStateSafe.strengthen_join hcontained hcoherent hlinear
      hpreserved hmap hstrengthens hwellBranch hterminalSafe with
    ⟨hwellJoin, hsafeJoin⟩
  exact ⟨hwellJoin, hsafeJoin, hprov.of_mutGatePullback hgate⟩

/-- Runtime provenance survives block-lifetime drops with the same registry.
Dropping static slots removes gates; it does not allocate references or widen
runtime targets. -/
theorem RuntimeBorrowProvenance.dropLifetime {store : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    RuntimeBorrowProvenance store env →
    RuntimeBorrowProvenance store (env.dropLifetime lifetime) := by
  intro hprov
  rcases hprov with ⟨R, hcover, hexcl⟩
  exact ⟨R, hcover.dropLifetime, hexcl⟩

/-- Terminal safety packaged with runtime borrow provenance.  This is the
preservation conclusion needed by dereference assignment: ordinary terminal
safety gives validity/safe abstraction/value typing, while provenance supplies
the concrete `&mut` registry consumed by the write frame. -/
def TerminalStateSafeWithProvenance (store : ProgramStore) (value : Value)
    (env : Env) (ty : Ty) : Prop :=
  TerminalStateSafe store value env ty ∧ RuntimeBorrowProvenance store env

/-- Runtime provenance is unchanged by a value-tail multistep: values do not
step, so the final store is definitionally the starting store. -/
theorem RuntimeBorrowProvenance.value_tail {store finalStore : ProgramStore}
    {env : Env} {lifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    RuntimeBorrowProvenance store env →
    RuntimeBorrowProvenance finalStore env := by
  intro hmulti hprov
  rcases multistep_value_inv hmulti with ⟨hstore, _hterm⟩
  simpa [hstore] using hprov

/-- The strengthened terminal conclusion transports through a join: ordinary
terminal safety uses the existing same-shape strengthening proof, while runtime
provenance uses the join-friendly registry transport. -/
theorem TerminalStateSafeWithProvenance.strengthen_join
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hgate : RuntimeLValMutGatePullback finalStore branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithProvenance finalStore finalValue
      branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithProvenance finalStore finalValue joinEnv joinTy := by
  rcases hterminal with ⟨hterminalSafe, hprov⟩
  rcases TerminalStateSafe.strengthen_join hcontained hcoherent hlinear
      hpreserved hmap hstrengthens hwellBranch hterminalSafe with
    ⟨hwellJoin, hsafeJoin⟩
  exact ⟨hwellJoin, hsafeJoin, hprov.of_mutGatePullback hgate⟩

/-- Terminal concrete roots plus writable-gate runtime provenance.

This is the non-concrete writable package needed by preservation.  The concrete
root component is the public runtime-safety statement.  The writable provenance
component keeps the store-realized `MutRegistryExclusive` frame that
dereference-assignment preservation consumes, but its coverage is restricted to
actual writable gates rather than every syntactic `&mut` lvalue. -/
def TerminalStateSafeWithConcreteRootsAndWritableProvenance
    (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) : Prop :=
  TerminalStateSafeWithConcreteRoots store value env ty ∧
    RuntimeWritableBorrowProvenance store env

/-- Terminal concrete roots plus both writable-gate write frames.

The store-realized frame is consumed by ordinary assignment preservation; the
concrete frame preserves the public root-safety claim across the concrete store
update.  Both coverage predicates range only over assignment-consumable gates,
so joined target-list alternatives do not become runtime obligations. -/
def TerminalStateSafeWithConcreteRootsAndWritableFrames
    (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) : Prop :=
  TerminalStateSafeWithConcreteRoots store value env ty ∧
    RuntimeWritableBorrowProvenance store env ∧
      ConcreteRuntimeWritableBorrowProvenance store env

/-- Forget writable-gate provenance and keep concrete roots. -/
theorem TerminalStateSafeWithConcreteRootsAndWritableProvenance.toConcreteRoots
    {store : ProgramStore} {value : Value} {env : Env} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndWritableProvenance store value env ty →
      TerminalStateSafeWithConcreteRoots store value env ty :=
  And.left

/-- Forget writable frames and keep concrete roots. -/
theorem TerminalStateSafeWithConcreteRootsAndWritableFrames.toConcreteRoots
    {store : ProgramStore} {value : Value} {env : Env} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndWritableFrames store value env ty →
      TerminalStateSafeWithConcreteRoots store value env ty :=
  And.left

/-- Value-tail composition for concrete roots plus writable-gate provenance. -/
theorem TerminalStateSafeWithConcreteRootsAndWritableProvenance.value_tail
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndWritableProvenance store value env ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    TerminalStateSafeWithConcreteRootsAndWritableProvenance
      finalStore finalValue env ty := by
  intro hterminal htail
  exact ⟨hterminal.1.value_tail htail,
    RuntimeWritableBorrowProvenance.value_tail htail hterminal.2⟩

/-- Value-tail composition for concrete roots plus both writable frames. -/
theorem TerminalStateSafeWithConcreteRootsAndWritableFrames.value_tail
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndWritableFrames store value env ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    TerminalStateSafeWithConcreteRootsAndWritableFrames
      finalStore finalValue env ty := by
  intro hterminal htail
  exact ⟨hterminal.1.value_tail htail,
    RuntimeWritableBorrowProvenance.value_tail htail hterminal.2.1,
    ConcreteRuntimeWritableBorrowProvenance.value_tail htail hterminal.2.2⟩

/-- Terminal concrete roots plus writable-gate provenance transport through a
join.

The join may widen static target lists, but writable provenance only asks about
assignment-consumable gates.  Those gates are transported through the explicit
runtime-writable pullback; the store-realized registry itself is unchanged. -/
theorem TerminalStateSafeWithConcreteRootsAndWritableProvenance.strengthen_join
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hgate : RuntimeWritableMutGatePullback finalStore branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithConcreteRootsAndWritableProvenance
      finalStore finalValue branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithConcreteRootsAndWritableProvenance
        finalStore finalValue joinEnv joinTy := by
  rcases hterminal with ⟨hterminalRoots, hprov⟩
  rcases TerminalStateSafeWithConcreteRoots.strengthen_join
      hcontained hcoherent hlinear hpreserved hmap hstrengthens
      hwellBranch hterminalRoots with
    ⟨hwellJoin, hterminalJoin⟩
  exact ⟨hwellJoin, hterminalJoin,
    RuntimeWritableBorrowProvenance.of_writableGatePullback hgate hprov⟩

/-- Terminal concrete roots plus both writable frames transport through a join.

The concrete-root component follows the same-shape/lifetime map.  The two
private write frames use the same runtime-writable gate pullback and otherwise
keep the same store-realized registries. -/
theorem TerminalStateSafeWithConcreteRootsAndWritableFrames.strengthen_join
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hgate : RuntimeWritableMutGatePullback finalStore branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithConcreteRootsAndWritableFrames
      finalStore finalValue branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithConcreteRootsAndWritableFrames
        finalStore finalValue joinEnv joinTy := by
  rcases hterminal with ⟨hterminalRoots, hprov, hconcreteProv⟩
  rcases TerminalStateSafeWithConcreteRoots.strengthen_join
      hcontained hcoherent hlinear hpreserved hmap hstrengthens
      hwellBranch hterminalRoots with
    ⟨hwellJoin, hterminalJoin⟩
  exact ⟨hwellJoin, hterminalJoin,
    RuntimeWritableBorrowProvenance.of_writableGatePullback hgate hprov,
    ConcreteRuntimeWritableBorrowProvenance.of_writableGatePullback
      hgate hconcreteProv⟩

/-- No lvalue is typeable in the empty environment. -/
theorem LValTyping.not_empty {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    LValTyping Env.empty lv partialTy lifetime → False := by
  exact lvalTyping_empty_false

/-- Empty environments have empty runtime borrow provenance. -/
theorem RuntimeBorrowProvenance.empty {store : ProgramStore} :
    RuntimeBorrowProvenance store Env.empty := by
  refine ⟨[], ?_, ?_⟩
  · intro source targets bl leaf hsource _hleaf
    exact False.elim (LValTyping.not_empty hsource)
  · intro leaf owner hmem _z _hz
    simp at hmem

/-- Runtime-selected borrow safety for one mutable-borrow root.

This is the join-friendly counterpart of `BorrowSafeRoot`: conflicts are only
considered when both conflicting targets are selected by live runtime borrow
cells.  Joined-in stale targets therefore do not force a false conflict, while a
real simultaneous conflict with a selected mutable target still collapses to the
same owner root. -/
def RuntimeBorrowSafeRoot (store : ProgramStore) (env : Env)
    (root : Name) : Prop :=
  ∀ y mutable targetsMutable targetsOther targetMutable targetOther,
    env ⊢ root ↝ (&mut targetsMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    SelectedTarget store root targetMutable →
    SelectedTarget store y targetOther →
    targetMutable ⋈ targetOther →
    root = y

/-- Runtime-selected borrow safety for every mutable-borrow root in an
environment.

This is weaker than requiring every static target-list conflict to collapse: it
only talks about targets selected by the concrete runtime store.  It still
compares the selected lvalues syntactically via `PathConflicts`; joins whose
executed branch realizes the same location through a different lvalue need an
additional location- or write-gate argument. -/
def RuntimeBorrowSafety (store : ProgramStore) (env : Env) : Prop :=
  ∀ root, RuntimeBorrowSafeRoot store env root

/-- Location-level no-overlap check for one mutable-borrow root.

Unlike `RuntimeBorrowSafeRoot`, this does not use syntactic `PathConflicts`.
Two selected targets conflict exactly when they resolve to the same concrete
location.  This is useful for isolating the join issue, because widened target
lists do not create runtime references.  It is not the final global runtime
safety invariant: accepted reborrows can keep two roots whose references resolve
to the same concrete location while later writes remain guarded. -/
def RuntimeLocationBorrowSafeRoot (store : ProgramStore) (env : Env)
    (root : Name) : Prop :=
  ∀ y mutable targetsMutable targetsOther targetMutable targetOther leaf,
    env ⊢ root ↝ (&mut targetsMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    SelectedTarget store root targetMutable →
    SelectedTarget store y targetOther →
    store.loc targetMutable = some leaf →
    store.loc targetOther = some leaf →
    root = y

/-- Location-level no-overlap check for an environment.  This is diagnostic and
too strong for ordinary accepted mutable reborrows. -/
def RuntimeLocationBorrowSafety (store : ProgramStore) (env : Env) : Prop :=
  ∀ root, RuntimeLocationBorrowSafeRoot store env root

/-- Empty environments are location-level runtime borrow-safe. -/
theorem RuntimeLocationBorrowSafety.empty {store : ProgramStore} :
    RuntimeLocationBorrowSafety store Env.empty := by
  intro root y mutable targetsMutable targetsOther targetMutable targetOther
    leaf hroot _hy _hmemMutable _hmemOther _hselectedMutable _hselectedOther
    _hlocMutable _hlocOther
  rcases hroot with ⟨slot, hslot, _hcontains⟩
  simp [Env.empty] at hslot

/-- Runtime-selected target-list membership pullback.

This is the join-side condition that rules out treating every joined target-list
member as a runtime edge.  A coarse target only has to come from the executed
fine branch when the concrete store actually selects it. -/
def RuntimeSelectedTargetMembershipPullback
    (store : ProgramStore) (envFine envCoarse : Env) : Prop :=
  ∀ root mutable targets target,
    envCoarse ⊢ root ↝ (Ty.borrow mutable targets) →
    target ∈ targets →
    SelectedTarget store root target →
    ∃ fineTargets,
      envFine ⊢ root ↝ (Ty.borrow mutable fineTargets) ∧
        target ∈ fineTargets

/-- Location-level selected-target pullback.

For runtime safety through joins, the same syntactic target need not be present
in the executed branch target list.  What matters is the concrete selected
location.  This pullback recovers a fine-branch target selected by the same root
and resolving to the same concrete location. -/
def RuntimeSelectedTargetLocationPullback
    (store : ProgramStore) (envFine envCoarse : Env) : Prop :=
  ∀ root mutable targets target leaf,
    envCoarse ⊢ root ↝ (Ty.borrow mutable targets) →
    target ∈ targets →
    SelectedTarget store root target →
    store.loc target = some leaf →
    ∃ fineTargets fineTarget,
      envFine ⊢ root ↝ (Ty.borrow mutable fineTargets) ∧
        fineTarget ∈ fineTargets ∧
        SelectedTarget store root fineTarget ∧
        store.loc fineTarget = some leaf

/-- The location-level selected-target pullback is reflexive. -/
theorem RuntimeSelectedTargetLocationPullback.refl
    (store : ProgramStore) (env : Env) :
    RuntimeSelectedTargetLocationPullback store env env := by
  intro root mutable targets target leaf hcontains hmem hselected hloc
  exact ⟨targets, target, hcontains, hmem, hselected, hloc⟩

/-- Same-target membership pullback implies the weaker location-level pullback. -/
theorem RuntimeSelectedTargetMembershipPullback.location
    {store : ProgramStore} {envFine envCoarse : Env} :
    RuntimeSelectedTargetMembershipPullback store envFine envCoarse →
    RuntimeSelectedTargetLocationPullback store envFine envCoarse := by
  intro hpull root mutable targets target leaf hcontains hmem hselected hloc
  rcases hpull root mutable targets target hcontains hmem hselected with
    ⟨fineTargets, hfine, hmemFine⟩
  exact ⟨fineTargets, target, hfine, hmemFine, hselected, hloc⟩

/-- Safe abstraction plus concrete-location mutability agreement gives the
join-safe selected-target pullback.

The target recovered in the executed branch need not be the same syntactic lval
as the joined target-list member.  It is enough that both are selected by the
same runtime root and resolve to the same concrete location; `LocMutExcl` pins
the mutability bit to that concrete location. -/
theorem RuntimeSelectedTargetLocationPullback.of_safeAbstraction_locMutExcl
    {store : ProgramStore} {envFine envCoarse : Env}
    (hsafe : store ∼ₛ envFine)
    (hmut : LocMutExcl store envFine envCoarse) :
    RuntimeSelectedTargetLocationPullback store envFine envCoarse := by
  intro root mutable targets target leaf hcontains hmem hselected hloc
  rcases envBorrow_locationWitness_of_selectedTarget hsafe hselected hloc with
    ⟨mutableFine, fineTargets, fineTarget, hfine, hmemFine, hselectedFine,
      hlocFine⟩
  have hsameLoc : store.loc fineTarget = store.loc target := by
    rw [hlocFine, hloc]
  have hmutableEq : mutableFine = mutable :=
    hmut root mutable targets target hcontains hmem hselected
      mutableFine fineTargets fineTarget hfine hmemFine hselectedFine hsameLoc
  cases hmutableEq
  exact ⟨fineTargets, fineTarget, hfine, hmemFine, hselectedFine, hlocFine⟩

/-- Static root borrow safety implies the runtime-selected version. -/
theorem BorrowSafeRoot.runtime {store : ProgramStore} {env : Env} {root : Name} :
    BorrowSafeRoot env root →
    RuntimeBorrowSafeRoot store env root := by
  intro hsafe y mutable targetsMutable targetsOther targetMutable targetOther
    hroot hy hmemMutable hmemOther _hselectedMutable _hselectedOther hconflict
  exact hsafe y mutable targetsMutable targetsOther targetMutable targetOther
    hroot hy hmemMutable hmemOther hconflict

/-- An environment whose roots are statically borrow-safe is runtime borrow-safe. -/
theorem RuntimeBorrowSafety.of_static {store : ProgramStore} {env : Env} :
    (∀ root, BorrowSafeRoot env root) →
    RuntimeBorrowSafety store env := by
  intro hsafe root
  exact (hsafe root).runtime

/-- The empty environment is runtime borrow-safe for any store. -/
theorem RuntimeBorrowSafety.empty {store : ProgramStore} :
    RuntimeBorrowSafety store Env.empty := by
  intro root y mutable targetsMutable targetsOther targetMutable targetOther
    hroot _hy _hmemMutable _hmemOther _hselectedMutable _hselectedOther _hconflict
  rcases hroot with ⟨slot, hslot, _hcontains⟩
  simp [Env.empty] at hslot

/-- A target lvalue is one of the concrete runtime borrow targets carried by a
value: the value contains a runtime reference to the same location that the
target resolves to.  This is value-scoped, so it can be used before the value is
installed as an environment root. -/
def RuntimeValueSelectsTarget (store : ProgramStore) (value : Value)
    (target : LVal) : Prop :=
  ∃ leaf,
    RuntimeValueBorrow store (.value value) leaf ∧
      store.loc target = some leaf

/-- A selected target of an installed root is a value-scoped selected target of
the value stored in that root. -/
theorem RuntimeValueSelectsTarget.of_selectedRoot
    {store : ProgramStore} {owner : Name} {value : Value}
    {lifetime : Lifetime} {target : LVal} :
    StoreOwnersAllocated store →
    store.slotAt (VariableProjection owner) =
      some { value := .value value, lifetime := lifetime } →
    SelectedTarget store owner target →
      RuntimeValueSelectsTarget store value target := by
  intro hallocated hslot hselected
  rcases RuntimeValueBorrow.of_selectedTarget
      hallocated hslot hselected with
    ⟨leaf, htargetLoc, hborrow⟩
  exact ⟨leaf, hborrow, htargetLoc⟩

/-- Concrete selected-borrow compatibility between an evaluated value and an
environment into which that value may be installed.

This is the runtime counterpart of `TyBorrowSafeAgainstEnv`: it only considers
targets whose lvalues resolve to concrete borrow locations actually carried by
the value, and selected targets actually carried by roots in the environment. -/
def RuntimeValueBorrowSafeAgainstEnv
    (store : ProgramStore) (env : Env) (value : Value) (ty : Ty) : Prop :=
  (∀ targetsMutable mutable targetsOther y targetMutable targetOther,
    PartialTyContains (.ty ty) (.borrow true targetsMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    RuntimeValueSelectsTarget store value targetMutable →
    SelectedTarget store y targetOther →
    targetMutable ⋈ targetOther →
    False) ∧
  (∀ x targetsMutable mutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ (.borrow true targetsMutable) →
    PartialTyContains (.ty ty) (.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    SelectedTarget store x targetMutable →
    RuntimeValueSelectsTarget store value targetOther →
    targetMutable ⋈ targetOther →
    False)

/-- The old static install-safety predicate implies the concrete runtime
version.  This is only a bridge for existing proofs; the runtime predicate is
strictly weaker because it ignores unselected joined targets. -/
theorem RuntimeValueBorrowSafeAgainstEnv.of_static
    {store : ProgramStore} {env : Env} {value : Value} {ty : Ty} :
    TyBorrowSafeAgainstEnv env ty →
    RuntimeValueBorrowSafeAgainstEnv store env value ty := by
  intro hsafe
  rcases hsafe with ⟨hsafeLeft, hsafeRight⟩
  constructor
  · intro targetsMutable mutable targetsOther y targetMutable targetOther
      hcontains henv hmemMutable hmemOther _hvalueSelected _hselectedOther
      hconflict
    exact hsafeLeft targetsMutable mutable targetsOther y targetMutable
      targetOther hcontains henv hmemMutable hmemOther hconflict
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      henv hcontains hmemMutable hmemOther _hselectedMutable _hvalueSelected
      hconflict
    exact hsafeRight x targetsMutable mutable targetsOther targetMutable
      targetOther henv hcontains hmemMutable hmemOther hconflict

/-- Runtime-selected borrow safety transports through explicit pullbacks of
contained borrow typings and selected runtime targets. -/
theorem RuntimeBorrowSafety.of_pullback
    {oldStore newStore : ProgramStore} {oldEnv newEnv : Env} :
    (∀ root mutable targets,
      newEnv ⊢ root ↝ (Ty.borrow mutable targets) →
      oldEnv ⊢ root ↝ (Ty.borrow mutable targets)) →
    (∀ root target,
      SelectedTarget newStore root target →
      SelectedTarget oldStore root target) →
    RuntimeBorrowSafety oldStore oldEnv →
    RuntimeBorrowSafety newStore newEnv := by
  intro hcontains hselected hsafe root y mutable targetsMutable targetsOther
    targetMutable targetOther hroot hy hmemMutable hmemOther hselectedMutable
    hselectedOther hconflict
  exact hsafe root y mutable targetsMutable targetsOther targetMutable
    targetOther
    (hcontains root true targetsMutable hroot)
    (hcontains y mutable targetsOther hy)
    hmemMutable hmemOther
    (hselected root targetMutable hselectedMutable)
    (hselected y targetOther hselectedOther)
    hconflict

/-- Runtime-selected borrow safety transports through target-list growth when
every selected target in the grown environment is known to come from a target
list in the original environment.

This is the proof obligation needed at joins: the type-level target lists may
grow, but a grown-in target is harmless unless it is selected by the concrete
store. -/
theorem RuntimeBorrowSafety.of_selectedTargetMembershipPullback
    {store : ProgramStore} {oldEnv newEnv : Env} :
    (∀ root mutable targets target,
      newEnv ⊢ root ↝ (Ty.borrow mutable targets) →
      target ∈ targets →
      SelectedTarget store root target →
      ∃ oldTargets,
        oldEnv ⊢ root ↝ (Ty.borrow mutable oldTargets) ∧
          target ∈ oldTargets) →
    RuntimeBorrowSafety store oldEnv →
    RuntimeBorrowSafety store newEnv := by
  intro hpull hsafe root y mutable targetsMutable targetsOther targetMutable
    targetOther hroot hy hmemMutable hmemOther hselectedMutable
    hselectedOther hconflict
  rcases hpull root true targetsMutable targetMutable hroot hmemMutable
      hselectedMutable with
    ⟨oldTargetsMutable, hrootOld, hmemMutableOld⟩
  rcases hpull y mutable targetsOther targetOther hy hmemOther
      hselectedOther with
    ⟨oldTargetsOther, hyOld, hmemOtherOld⟩
  exact hsafe root y mutable oldTargetsMutable oldTargetsOther targetMutable
    targetOther hrootOld hyOld hmemMutableOld hmemOtherOld hselectedMutable
    hselectedOther hconflict

/-- Runtime borrow safety transports through an explicit selected-target
membership pullback. -/
theorem RuntimeBorrowSafety.of_runtimeSelectedTargetMembershipPullback
    {store : ProgramStore} {envFine envCoarse : Env}
    (hpull : RuntimeSelectedTargetMembershipPullback store envFine envCoarse)
    (hsafe : RuntimeBorrowSafety store envFine) :
    RuntimeBorrowSafety store envCoarse := by
  exact RuntimeBorrowSafety.of_selectedTargetMembershipPullback hpull hsafe

/-- Location-level runtime borrow safety transports through a location-level
selected-target pullback. -/
theorem RuntimeLocationBorrowSafety.of_locationPullback
    {store : ProgramStore} {envFine envCoarse : Env}
    (hpull : RuntimeSelectedTargetLocationPullback store envFine envCoarse)
    (hsafe : RuntimeLocationBorrowSafety store envFine) :
    RuntimeLocationBorrowSafety store envCoarse := by
  intro root y mutable targetsMutable targetsOther targetMutable targetOther
    leaf hroot hy hmemMutable hmemOther hselectedMutable hselectedOther
    hlocMutable hlocOther
  rcases hpull root true targetsMutable targetMutable leaf
      hroot hmemMutable hselectedMutable hlocMutable with
    ⟨fineTargetsMutable, fineTargetMutable, hrootFine, hmemMutableFine,
      hselectedMutableFine, hlocMutableFine⟩
  rcases hpull y mutable targetsOther targetOther leaf
      hy hmemOther hselectedOther hlocOther with
    ⟨fineTargetsOther, fineTargetOther, hyFine, hmemOtherFine,
      hselectedOtherFine, hlocOtherFine⟩
  exact hsafe root y mutable fineTargetsMutable fineTargetsOther
    fineTargetMutable fineTargetOther leaf hrootFine hyFine hmemMutableFine
    hmemOtherFine hselectedMutableFine hselectedOtherFine hlocMutableFine
    hlocOtherFine

/-- Updating a slot to `undef` cannot create a location-level runtime
borrow-safety violation in an unchanged environment. -/
theorem RuntimeLocationBorrowSafety.update_undef {store : ProgramStore}
    {env : Env} {updated : Location} {updatedLifetime : Lifetime} :
    RuntimeLocationBorrowSafety store env →
    RuntimeLocationBorrowSafety
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env := by
  intro hsafe root y mutable targetsMutable targetsOther targetMutable
    targetOther leaf hroot hy hmemMutable hmemOther hselectedMutable
    hselectedOther hlocMutable hlocOther
  exact hsafe root y mutable targetsMutable targetsOther targetMutable
    targetOther leaf hroot hy hmemMutable hmemOther
    (SelectedTarget.update_undef_to_store hselectedMutable)
    (SelectedTarget.update_undef_to_store hselectedOther)
    (RuntimeFrame.loc_update_undef_some_to_store hlocMutable)
    (RuntimeFrame.loc_update_undef_some_to_store hlocOther)

namespace RuntimeFrame

/-- A successful lvalue resolution after a drop already resolved before the
drop. -/
theorem loc_drops_some_to_store {store store' : ProgramStore}
    {values : List PartialValue} :
    Drops store values store' →
    ∀ {lv : LVal} {location : Location},
      store'.loc lv = some location →
      store.loc lv = some location := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro lv location hloc
      exact hloc
  | nonOwner _hnonOwner _hdrops ih =>
      intro lv location hloc
      exact ih hloc
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro lv location hloc
      exact ih hloc
  | ownerPresent _howner _hslot _hdrops ih =>
      intro lv location hloc
      exact RuntimeFrame.loc_erase_some_to_store (ih hloc)

end RuntimeFrame

/-- Runtime location borrow safety is unchanged by a value-tail multistep. -/
theorem RuntimeLocationBorrowSafety.value_tail
    {store finalStore : ProgramStore} {env : Env}
    {lifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    RuntimeLocationBorrowSafety store env →
    RuntimeLocationBorrowSafety finalStore env := by
  intro hmulti hsafe
  rcases multistep_value_inv hmulti with ⟨hstore, _hterm⟩
  simpa [hstore] using hsafe

/-- Installing a value as a fresh root preserves runtime-selected borrow safety
when the value's concrete borrow footprint is compatible with the old
environment. -/
theorem RuntimeBorrowSafety.install_fresh_root
    {store : ProgramStore} {env : Env} {owner : Name}
    {value : Value} {ty : Ty} {lifetime : Lifetime} :
    RuntimeBorrowSafety store env →
    StoreOwnersAllocated store →
    store.slotAt (VariableProjection owner) =
      some { value := .value value, lifetime := lifetime } →
    RuntimeValueBorrowSafeAgainstEnv store env value ty →
    RuntimeBorrowSafety store
      (env.update owner { ty := .ty ty, lifetime := lifetime }) := by
  intro hsafe hallocated hrootSlot hvalueSafe root y mutable targetsMutable
    targetsOther targetMutable targetOther hroot hy hmemMutable hmemOther
    hselectedMutable hselectedOther hconflict
  by_cases hrootOwner : root = owner
  · subst root
    by_cases hyOwner : y = owner
    · exact hyOwner.symm
    · have hrootContains :
          PartialTyContains (.ty ty) (.borrow true targetsMutable) := by
        rcases hroot with ⟨slot, hslot, hcontains⟩
        have hslotEq : slot = { ty := .ty ty, lifetime := lifetime } := by
          simpa [Env.update] using hslot.symm
        subst hslotEq
        exact hcontains
      have hyOld : env ⊢ y ↝ (Ty.borrow mutable targetsOther) := by
        rcases hy with ⟨slot, hslot, hcontains⟩
        exact ⟨slot, by simpa [Env.update, hyOwner] using hslot, hcontains⟩
      have hvalueSelected :
          RuntimeValueSelectsTarget store value targetMutable :=
        RuntimeValueSelectsTarget.of_selectedRoot
          hallocated hrootSlot hselectedMutable
      exact False.elim
        (hvalueSafe.1 targetsMutable mutable targetsOther y targetMutable
          targetOther hrootContains hyOld hmemMutable hmemOther hvalueSelected
          hselectedOther hconflict)
  · have hrootOld : env ⊢ root ↝ (&mut targetsMutable) := by
      rcases hroot with ⟨slot, hslot, hcontains⟩
      exact ⟨slot, by simpa [Env.update, hrootOwner] using hslot, hcontains⟩
    by_cases hyOwner : y = owner
    · subst y
      have hyContains :
          PartialTyContains (.ty ty) (.borrow mutable targetsOther) := by
        rcases hy with ⟨slot, hslot, hcontains⟩
        have hslotEq : slot = { ty := .ty ty, lifetime := lifetime } := by
          simpa [Env.update] using hslot.symm
        subst hslotEq
        exact hcontains
      have hvalueSelected :
          RuntimeValueSelectsTarget store value targetOther :=
        RuntimeValueSelectsTarget.of_selectedRoot
          hallocated hrootSlot hselectedOther
      exact False.elim
        (hvalueSafe.2 root targetsMutable mutable targetsOther targetMutable
          targetOther hrootOld hyContains hmemMutable hmemOther
          hselectedMutable hvalueSelected hconflict)
    · have hyOld : env ⊢ y ↝ (Ty.borrow mutable targetsOther) := by
        rcases hy with ⟨slot, hslot, hcontains⟩
        exact ⟨slot, by simpa [Env.update, hyOwner] using hslot, hcontains⟩
      exact hsafe root y mutable targetsMutable targetsOther targetMutable
        targetOther hrootOld hyOld hmemMutable hmemOther hselectedMutable
        hselectedOther hconflict

/-- Updating a slot to `undef` cannot create a runtime-selected borrow-safety
violation in an unchanged environment. -/
theorem RuntimeBorrowSafeRoot.update_undef {store : ProgramStore}
    {env : Env} {root : Name} {updated : Location}
    {updatedLifetime : Lifetime} :
    RuntimeBorrowSafeRoot store env root →
    RuntimeBorrowSafeRoot
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env root := by
  intro hsafe y mutable targetsMutable targetsOther targetMutable targetOther
    hroot hy hmemMutable hmemOther hselectedMutable hselectedOther hconflict
  exact hsafe y mutable targetsMutable targetsOther targetMutable targetOther
    hroot hy hmemMutable hmemOther
    (SelectedTarget.update_undef_to_store hselectedMutable)
    (SelectedTarget.update_undef_to_store hselectedOther)
    hconflict

/-- Updating a slot to `undef` preserves runtime-selected borrow safety. -/
theorem RuntimeBorrowSafety.update_undef {store : ProgramStore}
    {env : Env} {updated : Location} {updatedLifetime : Lifetime} :
    RuntimeBorrowSafety store env →
    RuntimeBorrowSafety
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env := by
  intro hsafe root
  exact (hsafe root).update_undef

/-- A move paired with the concrete runtime `undef` update preserves
runtime-selected borrow safety.

The environment-side move can only remove borrow nodes (via `Strike`), and the
store update cannot create a newly selected runtime target.  Therefore every
post-move selected conflict pulls back to a pre-move selected conflict. -/
theorem RuntimeBorrowSafety.move_update_undef {store : ProgramStore}
    {env env' : Env} {moved : LVal} {updated : Location}
    {updatedLifetime : Lifetime} :
    EnvMove env moved env' →
    RuntimeBorrowSafety store env →
    RuntimeBorrowSafety
      (store.update updated { value := .undef, lifetime := updatedLifetime })
      env' := by
  intro hmove hsafe root y mutable targetsMutable targetsOther
    targetMutable targetOther hroot hy hmemMutable hmemOther
    hselectedMutable hselectedOther hconflict
  exact hsafe root y mutable targetsMutable targetsOther targetMutable
    targetOther
    (EnvContains.of_move hmove hroot)
    (EnvContains.of_move hmove hy)
    hmemMutable hmemOther
    (SelectedTarget.update_undef_to_store hselectedMutable)
    (SelectedTarget.update_undef_to_store hselectedOther)
    hconflict

/-- Dropping values cannot create a selected target in the resulting store. -/
theorem SelectedTarget.drops_to_store {store store' : ProgramStore}
    {values : List PartialValue} {x : Name} {target : LVal} :
    Drops store values store' →
    SelectedTarget store' x target →
    SelectedTarget store x target := by
  intro hdrops
  induction hdrops with
  | nil =>
      intro hselected
      exact hselected
  | nonOwner _hnonOwner _hdrops ih =>
      intro hselected
      exact ih hselected
  | ownerMissing _howner _hmissing _hdrops ih =>
      intro hselected
      exact ih hselected
  | ownerPresent _howner _hslot _hdrops ih =>
      intro hselected
      exact SelectedTarget.erase_to_store (ih hselected)

/-- Dropping values preserves location-level runtime borrow safety in an
unchanged environment. -/
theorem RuntimeLocationBorrowSafety.drops {store store' : ProgramStore}
    {env : Env} {values : List PartialValue} :
    Drops store values store' →
    RuntimeLocationBorrowSafety store env →
    RuntimeLocationBorrowSafety store' env := by
  intro hdrops hsafe root y mutable targetsMutable targetsOther targetMutable
    targetOther leaf hroot hy hmemMutable hmemOther hselectedMutable
    hselectedOther hlocMutable hlocOther
  exact hsafe root y mutable targetsMutable targetsOther targetMutable
    targetOther leaf hroot hy hmemMutable hmemOther
    (SelectedTarget.drops_to_store hdrops hselectedMutable)
    (SelectedTarget.drops_to_store hdrops hselectedOther)
    (RuntimeFrame.loc_drops_some_to_store hdrops hlocMutable)
    (RuntimeFrame.loc_drops_some_to_store hdrops hlocOther)

/-- Dropping a lifetime preserves location-level runtime borrow safety for the
dropped environment. -/
theorem RuntimeLocationBorrowSafety.dropsLifetime {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    DropsLifetime store lifetime store' →
    RuntimeLocationBorrowSafety store env →
    RuntimeLocationBorrowSafety store' (env.dropLifetime lifetime) := by
  intro hdrops hsafe
  cases hdrops with
  | intro _hdropSet hdrops =>
      have hsafeStore' : RuntimeLocationBorrowSafety store' env :=
        RuntimeLocationBorrowSafety.drops hdrops hsafe
      intro root y mutable targetsMutable targetsOther targetMutable
        targetOther leaf hroot hy hmemMutable hmemOther hselectedMutable
        hselectedOther hlocMutable hlocOther
      exact hsafeStore' root y mutable targetsMutable targetsOther targetMutable
        targetOther leaf
        (EnvContains.dropLifetime_of_contains hroot)
        (EnvContains.dropLifetime_of_contains hy)
        hmemMutable hmemOther hselectedMutable hselectedOther hlocMutable
        hlocOther

/-- Location-level runtime borrow safety follows the lifetime drop hidden inside
a singleton-value block multistep. -/
theorem RuntimeLocationBorrowSafety.blockBValueMultiStep
    {store finalStore : ProgramStore} {env : Env}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    RuntimeLocationBorrowSafety store env →
    RuntimeLocationBorrowSafety finalStore (env.dropLifetime blockLifetime) := by
  intro hmulti hsafe
  cases hmulti with
  | trans hstep hrest =>
      cases hstep with
      | blockA hvalueStep =>
          exact False.elim (value_no_step hvalueStep)
      | blockB hdrops =>
          rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
          subst hstore
          cases hterm
          exact RuntimeLocationBorrowSafety.dropsLifetime hdrops hsafe

/-- Dropping values preserves runtime-selected borrow safety in an unchanged
environment. -/
theorem RuntimeBorrowSafeRoot.drops {store store' : ProgramStore}
    {env : Env} {root : Name} {values : List PartialValue} :
    Drops store values store' →
    RuntimeBorrowSafeRoot store env root →
    RuntimeBorrowSafeRoot store' env root := by
  intro hdrops hsafe y mutable targetsMutable targetsOther targetMutable targetOther
    hroot hy hmemMutable hmemOther hselectedMutable hselectedOther hconflict
  exact hsafe y mutable targetsMutable targetsOther targetMutable targetOther
    hroot hy hmemMutable hmemOther
    (SelectedTarget.drops_to_store hdrops hselectedMutable)
    (SelectedTarget.drops_to_store hdrops hselectedOther)
    hconflict

/-- Dropping values preserves runtime-selected borrow safety. -/
theorem RuntimeBorrowSafety.drops {store store' : ProgramStore}
    {env : Env} {values : List PartialValue} :
    Drops store values store' →
    RuntimeBorrowSafety store env →
    RuntimeBorrowSafety store' env := by
  intro hdrops hsafe root
  exact (hsafe root).drops hdrops

/-- Dropping a lifetime preserves runtime-selected borrow safety for the dropped
environment: every surviving borrow node was already present before the drop,
and every selected target in the dropped store was selected before the drop. -/
theorem RuntimeBorrowSafety.dropsLifetime {store store' : ProgramStore}
    {env : Env} {lifetime : Lifetime} :
    DropsLifetime store lifetime store' →
    RuntimeBorrowSafety store env →
    RuntimeBorrowSafety store' (env.dropLifetime lifetime) := by
  intro hdrops hsafe
  cases hdrops with
  | intro _hdropSet hdrops =>
      have hsafeStore' : RuntimeBorrowSafety store' env :=
        RuntimeBorrowSafety.drops hdrops hsafe
      intro root y mutable targetsMutable targetsOther targetMutable targetOther
        hroot hy hmemMutable hmemOther hselectedMutable hselectedOther hconflict
      exact hsafeStore' root y mutable targetsMutable targetsOther targetMutable
        targetOther
        (EnvContains.dropLifetime_of_contains hroot)
        (EnvContains.dropLifetime_of_contains hy)
        hmemMutable hmemOther hselectedMutable hselectedOther hconflict

/-- Runtime-selected borrow safety is unchanged by a value-tail multistep. -/
theorem RuntimeBorrowSafety.value_tail {store finalStore : ProgramStore}
    {env : Env} {lifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    RuntimeBorrowSafety store env →
    RuntimeBorrowSafety finalStore env := by
  intro hmulti hsafe
  rcases multistep_value_inv hmulti with ⟨hstore, _hterm⟩
  simpa [hstore] using hsafe

/-- Runtime-selected borrow safety follows the lifetime drop hidden inside a
singleton-value block multistep. -/
theorem RuntimeBorrowSafety.blockBValueMultiStep
    {store finalStore : ProgramStore} {env : Env}
    {lifetime blockLifetime : Lifetime} {value finalValue : Value} :
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    RuntimeBorrowSafety store env →
    RuntimeBorrowSafety finalStore (env.dropLifetime blockLifetime) := by
  intro hmulti hsafe
  cases hmulti with
  | trans hstep hrest =>
      cases hstep with
      | blockA hvalueStep =>
          exact False.elim (value_no_step hvalueStep)
      | blockB hdrops =>
          rcases multistep_value_inv hrest with ⟨hstore, hterm⟩
          subst hstore
          cases hterm
          exact RuntimeBorrowSafety.dropsLifetime hdrops hsafe

/-- Terminal concrete roots plus runtime-selected borrow safety.

This is the preservation package that avoids assignment-local static borrow
safety: ordinary terminal facts and concrete root safety describe runtime value
validity, while `RuntimeBorrowSafety` is the selected-target invariant consumed
by later dereference assignments. -/
def TerminalStateSafeWithConcreteRootsAndRuntimeSafety (store : ProgramStore)
    (value : Value) (env : Env) (ty : Ty) : Prop :=
  TerminalStateSafeWithConcreteRoots store value env ty ∧
    RuntimeBorrowSafety store env

/-- Terminal concrete roots plus the diagnostic location-level no-overlap check.

This package is useful for proving that joins themselves do not manufacture
runtime references.  It is too strong as a global preservation target for the
full language, because mutable reborrows may overlap at the concrete-location
level while access remains protected by the write rules. -/
def TerminalStateSafeWithConcreteRootsAndLocationSafety
    (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) : Prop :=
  TerminalStateSafeWithConcreteRoots store value env ty ∧
    RuntimeLocationBorrowSafety store env

/-- Forget runtime-selected borrow safety and keep concrete roots. -/
theorem TerminalStateSafeWithConcreteRootsAndRuntimeSafety.toConcreteRoots
    {store : ProgramStore} {value : Value} {env : Env} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndRuntimeSafety store value env ty →
      TerminalStateSafeWithConcreteRoots store value env ty :=
  And.left

/-- Forget location-level runtime borrow safety and keep concrete roots. -/
theorem TerminalStateSafeWithConcreteRootsAndLocationSafety.toConcreteRoots
    {store : ProgramStore} {value : Value} {env : Env} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndLocationSafety store value env ty →
      TerminalStateSafeWithConcreteRoots store value env ty :=
  And.left

/-- Value-tail composition for concrete roots plus runtime-selected borrow
safety. -/
theorem TerminalStateSafeWithConcreteRootsAndRuntimeSafety.value_tail
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndRuntimeSafety store value env ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    TerminalStateSafeWithConcreteRootsAndRuntimeSafety finalStore finalValue env ty := by
  intro hterminal htail
  exact ⟨hterminal.1.value_tail htail,
    RuntimeBorrowSafety.value_tail htail hterminal.2⟩

/-- Value-tail composition for concrete roots plus location-level runtime
borrow safety. -/
theorem TerminalStateSafeWithConcreteRootsAndLocationSafety.value_tail
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    TerminalStateSafeWithConcreteRootsAndLocationSafety store value env ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    TerminalStateSafeWithConcreteRootsAndLocationSafety
      finalStore finalValue env ty := by
  intro hterminal htail
  exact ⟨hterminal.1.value_tail htail,
    RuntimeLocationBorrowSafety.value_tail htail hterminal.2⟩

/-- Terminal concrete roots plus location-level runtime safety transport
through a join. -/
theorem TerminalStateSafeWithConcreteRootsAndLocationSafety.strengthen_join
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hlocation :
      RuntimeSelectedTargetLocationPullback finalStore branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithConcreteRootsAndLocationSafety
      finalStore finalValue branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithConcreteRootsAndLocationSafety
        finalStore finalValue joinEnv joinTy := by
  rcases hterminal with ⟨hterminalRoots, hlocationSafe⟩
  rcases TerminalStateSafeWithConcreteRoots.strengthen_join
      hcontained hcoherent hlinear hpreserved hmap hstrengthens
      hwellBranch hterminalRoots with
    ⟨hwellJoin, hterminalJoin⟩
  exact ⟨hwellJoin, hterminalJoin,
    RuntimeLocationBorrowSafety.of_locationPullback hlocation
      hlocationSafe⟩

/-- Terminal concrete roots plus location-level runtime safety transport
through a join, using the concrete store invariant for joined target lists. -/
theorem TerminalStateSafeWithConcreteRootsAndLocationSafety.strengthen_join_of_safeAbstraction_locMutExcl
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hsafeBranch : finalStore ∼ₛ branchEnv)
    (hmut : LocMutExcl finalStore branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithConcreteRootsAndLocationSafety
      finalStore finalValue branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithConcreteRootsAndLocationSafety
        finalStore finalValue joinEnv joinTy := by
  exact
    TerminalStateSafeWithConcreteRootsAndLocationSafety.strengthen_join
      hcontained hcoherent hlinear hpreserved hmap
      (RuntimeSelectedTargetLocationPullback.of_safeAbstraction_locMutExcl
        hsafeBranch hmut)
      hstrengthens hwellBranch hterminal

/-- Concrete roots, runtime-selected borrow safety, and writable-gate concrete
provenance bundled together.

This is the intended replacement package for the current broad
`TerminalStateSafeWithConcreteRootsAndProvenance`: the safety component is
selected-target based, and the registry component ranges only over writable
mutable gates. -/
def TerminalStateSafeWithRuntimeSafetyAndWritableProvenance
    (store : ProgramStore) (value : Value) (env : Env) (ty : Ty) : Prop :=
  TerminalStateSafeWithConcreteRoots store value env ty ∧
    RuntimeBorrowSafety store env ∧
      ConcreteRuntimeWritableBorrowProvenance store env

/-- Forget the writable provenance and keep concrete roots plus runtime safety. -/
theorem TerminalStateSafeWithRuntimeSafetyAndWritableProvenance.toRuntimeSafety
    {store : ProgramStore} {value : Value} {env : Env} {ty : Ty} :
    TerminalStateSafeWithRuntimeSafetyAndWritableProvenance store value env ty →
      TerminalStateSafeWithConcreteRootsAndRuntimeSafety store value env ty := by
  intro hterminal
  exact ⟨hterminal.1, hterminal.2.1⟩

/-- Value-tail composition for concrete roots, runtime-selected borrow safety,
and writable-gate concrete provenance. -/
theorem TerminalStateSafeWithRuntimeSafetyAndWritableProvenance.value_tail
    {store finalStore : ProgramStore} {env : Env} {lifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} :
    TerminalStateSafeWithRuntimeSafetyAndWritableProvenance store value env ty →
    MultiStep store lifetime (.val value) finalStore (.val finalValue) →
    TerminalStateSafeWithRuntimeSafetyAndWritableProvenance
      finalStore finalValue env ty := by
  intro hterminal htail
  exact ⟨hterminal.1.value_tail htail,
    RuntimeBorrowSafety.value_tail htail hterminal.2.1,
    ConcreteRuntimeWritableBorrowProvenance.value_tail htail hterminal.2.2⟩

/-- Terminal concrete roots, runtime-selected safety, and writable provenance
transport through a join.

The join may widen static target lists.  The concrete-root component strengthens
by same shape; runtime borrow safety is carried as the selected-target invariant
for the joined environment; writable provenance transports only for concrete
assignment gates. -/
theorem TerminalStateSafeWithRuntimeSafetyAndWritableProvenance.strengthen_join
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hruntime : RuntimeBorrowSafety finalStore joinEnv)
    (hgate : RuntimeWritableMutGatePullback finalStore branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithRuntimeSafetyAndWritableProvenance
      finalStore finalValue branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithRuntimeSafetyAndWritableProvenance
        finalStore finalValue joinEnv joinTy := by
  rcases hterminal with ⟨hterminalRoots, _hruntimeBranch, hprov⟩
  rcases TerminalStateSafeWithConcreteRoots.strengthen_join
      hcontained hcoherent hlinear hpreserved hmap hstrengthens
      hwellBranch hterminalRoots with
    ⟨hwellJoin, hterminalJoin⟩
  exact ⟨hwellJoin, hterminalJoin, hruntime,
    ConcreteRuntimeWritableBorrowProvenance.of_writableGatePullback
      hgate hprov⟩

/-- Terminal concrete roots, runtime-selected safety, and writable provenance
transport through a join from the two runtime pullbacks.

The selected-target pullback says widened target-list members are ignored unless
they are the concrete member selected by the store; the writable-gate pullback
does the same narrowing for later assignment frames. -/
theorem TerminalStateSafeWithRuntimeSafetyAndWritableProvenance.strengthen_join_of_pullbacks
    {finalStore : ProgramStore} {finalValue : Value}
    {branchEnv joinEnv : Env} {lifetime : Lifetime}
    {branchTy joinTy : Ty}
    (hcontained : ContainedBorrowsWellFormed joinEnv)
    (hcoherent : Coherent joinEnv)
    (hlinear : Linearizable joinEnv)
    (hpreserved : EnvLifetimesPreserved branchEnv joinEnv)
    (hmap : EnvSameShapeStrengthening branchEnv joinEnv)
    (hselected :
      RuntimeSelectedTargetMembershipPullback finalStore branchEnv joinEnv)
    (hgate : RuntimeWritableMutGatePullback finalStore branchEnv joinEnv)
    (hstrengthens : PartialTyStrengthens (.ty branchTy) (.ty joinTy))
    (hwellBranch : WellFormedEnv branchEnv lifetime)
    (hterminal : TerminalStateSafeWithRuntimeSafetyAndWritableProvenance
      finalStore finalValue branchEnv branchTy) :
    WellFormedEnv joinEnv lifetime ∧
      TerminalStateSafeWithRuntimeSafetyAndWritableProvenance
        finalStore finalValue joinEnv joinTy := by
  exact
    TerminalStateSafeWithRuntimeSafetyAndWritableProvenance.strengthen_join
      hcontained hcoherent hlinear hpreserved hmap
      (RuntimeBorrowSafety.of_runtimeSelectedTargetMembershipPullback hselected
        hterminal.2.1)
      hgate hstrengthens hwellBranch hterminal


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
      SelectedTarget store container t →
      WriteGuarded store env leaf base₀ z

/-- Runtime write guards are contained in the static authority closure. -/
theorem WriteGuarded.authorityGuard {store : ProgramStore} {env : Env}
    {leaf : Location} {base₀ root : Name} :
    WriteGuarded store env leaf base₀ root →
    BorrowAuthorityGuard env base₀ root := by
  intro hguard
  induction hguard with
  | base _hkill =>
      exact BorrowAuthorityGuard.base
  | step hcontainer hnode hmem _hbase _hkill _hlive ih =>
      simpa [_hbase] using BorrowAuthorityGuard.step ih hnode hmem

/--
Only roots in the write's authority closure need to be borrow-safe against the
rest of the environment.  Unrelated conflicts elsewhere in a joined environment
are irrelevant to this collapse.
-/
theorem WriteGuarded.collapse_kill_authority {store : ProgramStore} {env : Env}
    {leaf : Location} {base₀ : Name}
    (hsafeRoot :
      ∀ root, BorrowAuthorityGuard env base₀ root → BorrowSafeRoot env root)
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
  | @step container _z targets' t' hGc hnode' hmem' hbase' hkill' _hlive' =>
      have hconflict : t' ⋈ t := by
        simpa [PathConflicts, hbase'] using hz.symm
      have hcontainerSafe : BorrowSafeRoot env container :=
        hsafeRoot container hGc.authorityGuard
      have hceq : container = c :=
        hcontainerSafe c mutable targets' ts t' t hnode' hnode hmem'
          hmem hconflict
      subst hceq
      exact ⟨hGc, hkill'⟩

/--
Selected-target variant of `collapse_kill_authority`.

The static version uses `BorrowSafeRoot`, which is too strong after joins
because it ranges over every target in a widened type list.  This version only
collapses through conflicts between runtime-selected targets.  It is the guard
lemma needed by deref-assignment preservation once the reachable-state
provenance invariant is threaded. -/
theorem WriteGuarded.collapse_kill_selected_authority
    {store : ProgramStore} {env : Env} {leaf : Location} {base₀ : Name}
    (hsafeRoot :
      ∀ root,
        BorrowAuthorityGuard env base₀ root →
          RuntimeBorrowSafeRoot store env root)
    (hnotWP : ¬ WriteProhibited env (.var base₀)) :
    ∀ {c : Name} {mutable : Bool} {ts : List LVal} {t : LVal},
      env ⊢ c ↝ (.borrow mutable ts) →
      t ∈ ts →
      SelectedTarget store c t →
      WriteGuarded store env leaf base₀ (LVal.base t) →
      WriteGuarded store env leaf base₀ c ∧ SlotDepKill store env leaf c := by
  intro c mutable ts t hnode hmem hselected hG
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
  | @step container _z targets' t' hGc hnode' hmem' hbase' hkill' hlive' =>
      have hconflict : t' ⋈ t := by
        simpa [PathConflicts, hbase'] using hz.symm
      have hcontainerSafe : RuntimeBorrowSafeRoot store env container :=
        hsafeRoot container hGc.authorityGuard
      have hceq : container = c :=
        hcontainerSafe c mutable targets' ts t' t hnode' hnode hmem'
          hmem hlive' hselected hconflict
      subst hceq
      exact ⟨hGc, hkill'⟩

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

/-- Owner-root case for concrete dereference assignment.

When `source` is a live borrow rooted at `x`, provenance deliberately does not
constrain `x` itself.  The missing fact is structural: the root value reaches
the first non-owning borrow cell by a pure owner spine, so any concrete runtime
borrow carried by that root value is the first borrow cell's pointee.  That
pointee cannot be strictly below the write result without forming a resolution
cycle. -/
theorem not_below_invalidated_owner_root_of_firstNode
    {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
    {source : LVal} {mutable : Bool} {targets : List LVal}
    {sourceLifetime derefLifetime : Lifetime}
    {derefTy updatedTy : PartialTy}
    {updated : Location} {updatedSlot : StoreSlot}
    {x : Name} {envSlot : EnvSlot} {value : PartialValue} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    store ∼ₛ env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    LValTyping env source (.ty (.borrow mutable targets)) sourceLifetime →
    LValTyping env (.deref source) derefTy derefLifetime →
    store.loc (.deref source) = some updated →
    store.slotAt updated = some updatedSlot →
    ValidPartialValue store updatedSlot.value updatedTy →
    x = LVal.base source →
    env.slotAt x = some envSlot →
    store.slotAt (VariableProjection x) =
      some { value := value, lifetime := envSlot.lifetime } →
    VariableProjection x ≠ updated →
      ¬ RuntimeValueBorrowInvalidatedBelow store value updated := by
  intro hφ hwellFormed hsafe hvalidStore hheap hsource hderef hloc
    hupdatedSlot hupdatedValid hx henvSlot hrootSlot _hrootNe hinvalid
  rcases firstNodePack hwellFormed hsafe hsource hloc with
    ⟨packSlot, rootValue, cell, cellSlot, firstLeaf, m, ts, spinePath,
      suffix, u₀, hpackEnv, hpackRoot, hcellSlot, hcellValue, _hcellValid,
      hspine, _hderefShape, _hfirstLoc, _hpath, hres⟩
  subst hx
  have hpackSlotEq : packSlot = envSlot :=
    Option.some.inj (hpackEnv.symm.trans henvSlot)
  subst hpackSlotEq
  have hrootValueEq : rootValue = value := by
    have hslotEq :
        StoreSlot.mk rootValue packSlot.lifetime =
          StoreSlot.mk value packSlot.lifetime :=
      Option.some.inj (hpackRoot.symm.trans hrootSlot)
    exact congrArg StoreSlot.value hslotEq
  subst rootValue
  rcases hinvalid with ⟨borrowLeaf, hborrow, hbelow⟩
  have hborrowLeafEq : borrowLeaf = firstLeaf :=
    StoreOwnerSpine.runtimeValueBorrow_leaf_eq hspine hcellValue hborrow
  subst borrowLeaf
  rcases hres with hupdatedEq | hreadsFirst
  · subst hupdatedEq
    exact ValidPartialValue.no_storage_ownership_cycle hupdatedSlot
      hupdatedValid hbelow
  · have hbelowUp : LocationBelow store φ updated firstLeaf :=
      RuntimeFrame.locReads_below hφ hwellFormed hsafe hvalidStore hheap
        hderef hreadsFirst hloc
    rcases (lval_loc_or_reads_protectedBySomeBase hwellFormed hsafe
        hvalidStore hheap hderef).1 hloc with ⟨root, hprotectedUpdated⟩
    have hprotectedFirst : ProtectedByBase store root firstLeaf :=
      ProtectedByBase.trans_ownsTransitively hprotectedUpdated hbelow
    have hbelowDown : LocationBelow store φ firstLeaf updated :=
      ⟨root, root, hprotectedFirst, hprotectedUpdated,
        Or.inr ⟨rfl, hbelow⟩⟩
    exact LocationBelow.irrefl hvalidStore hheap hupdatedSlot hupdatedValid
      (LocationBelow.trans hvalidStore hheap hbelowUp hbelowDown)

/-- Concrete root update frame for dereference assignment through a live
mutable borrow.

This discharges the owner-root case of
`ConcreteRuntimeRootsSafe.update_of_mut_borrow_provenance` using the first-node
spine decomposition of the runtime dereference.  Cross-root invalidation is
still ruled out by the concrete provenance registry. -/
theorem ConcreteRuntimeRootsSafe.update_of_mut_borrow_provenance_firstNode
    {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
    {source : LVal} {targets : List LVal} {bl derefLifetime : Lifetime}
    {derefTy updatedTy : PartialTy}
    {updated : Location} {updatedSlot newSlot : StoreSlot} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    ConcreteRuntimeRootsSafe store env →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    ConcreteRuntimeBorrowProvenance store env →
    StoreOwnersAllocated store →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    store ∼ₛ env →
    LValTyping env source (.ty (.borrow true targets)) bl →
    LValTyping env (.deref source) derefTy derefLifetime →
    store.loc (.deref source) = some updated →
    store.slotAt updated = some updatedSlot →
    ValidPartialValue store updatedSlot.value updatedTy →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      VariableProjection x = updated →
        newSlot.lifetime = envSlot.lifetime) →
      ConcreteRuntimeRootsSafe (store.update updated newSlot) env := by
  intro hφ hwellFormed hroots hnewSafe hprov hallocated hvalidStore hheap
    hsafe hsource hderef hupdated hupdatedSlot hupdatedValid hlifetime
  exact ConcreteRuntimeRootsSafe.update_of_mut_borrow_provenance hroots
    hnewSafe hprov hallocated hsafe hsource hupdated hlifetime
    (by
      intro x envSlot value hx henvSlot hstoreSlot hrootNe
      exact not_below_invalidated_owner_root_of_firstNode hφ hwellFormed
        hsafe hvalidStore hheap hsource hderef hupdated hupdatedSlot
        hupdatedValid hx henvSlot hstoreSlot hrootNe)

/-- Concrete root update frame for dereference assignment through a live
writable `&mut`, consuming only writable-gate concrete provenance.

The writable gate supplies the cross-root concrete frame; the owner-root case is
the same first-node runtime argument used by the broad provenance variant. -/
theorem ConcreteRuntimeRootsSafe.update_of_mut_borrow_writableProvenance_firstNode
    {store : ProgramStore} {env : Env} {current : Lifetime} {φ : Name → Nat}
    {source : LVal} {targets : List LVal} {bl derefLifetime : Lifetime}
    {derefTy updatedTy : PartialTy}
    {updated : Location} {updatedSlot newSlot : StoreSlot}
    {rhsTy : Ty} {result : Env} :
    LinearizedBy φ env →
    WellFormedEnv env current →
    ConcreteRuntimeRootsSafe store env →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    ConcreteRuntimeWritableBorrowProvenance store env →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    store ∼ₛ env →
    LValTyping env source (.ty (.borrow true targets)) bl →
    LValTyping env (.deref source) derefTy derefLifetime →
    store.loc (.deref source) = some updated →
    store.slotAt updated = some updatedSlot →
    ValidPartialValue store updatedSlot.value updatedTy →
    EnvWrite 0 env (.deref source) rhsTy result →
    (∀ x envSlot,
      env.slotAt x = some envSlot →
      VariableProjection x = updated →
        newSlot.lifetime = envSlot.lifetime) →
      ConcreteRuntimeRootsSafe (store.update updated newSlot) env := by
  intro hφ hwellFormed hroots hnewSafe hprov hvalidStore hheap hsafe
    hsource hderef hupdated hupdatedSlot hupdatedValid hwrite hlifetime
  have hgate : RuntimeWritableMutGate store env source updated :=
    ⟨targets, bl, rhsTy, result, hsource, hupdated, hwrite⟩
  exact ConcreteRuntimeRootsSafe.update_of_mut_borrow_writableProvenance
    hroots hnewSafe hprov hgate hlifetime
    (by
      intro x envSlot value hx henvSlot hstoreSlot hrootNe
      exact not_below_invalidated_owner_root_of_firstNode hφ hwellFormed
        hsafe hvalidStore hheap hsource hderef hupdated hupdatedSlot
        hupdatedValid hx henvSlot hstoreSlot hrootNe)

/-- Join-aware concrete root update frame for dereference assignment through a
live mutable borrow.

This is the same first-node owner-root argument as
`ConcreteRuntimeRootsSafe.update_of_mut_borrow_provenance_firstNode`, but the
cross-root frame may come from a finer executed branch environment and is
transported through an explicit runtime mutable-gate pullback. -/
theorem ConcreteRuntimeRootsSafe.update_of_mut_borrow_provenance_gate_firstNode
    {store : ProgramStore} {envFine envCoarse : Env}
    {current : Lifetime} {φ : Name → Nat}
    {source : LVal} {targets : List LVal} {bl derefLifetime : Lifetime}
    {derefTy updatedTy : PartialTy}
    {updated : Location} {updatedSlot newSlot : StoreSlot} :
    RuntimeLValMutGatePullback store envFine envCoarse →
    LinearizedBy φ envCoarse →
    WellFormedEnv envCoarse current →
    ConcreteRuntimeRootsSafe store envCoarse →
    ConcreteRuntimeValueSafe (store.update updated newSlot) newSlot.value →
    ConcreteRuntimeBorrowProvenance store envFine →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    store ∼ₛ envCoarse →
    LValTyping envCoarse source (.ty (.borrow true targets)) bl →
    LValTyping envCoarse (.deref source) derefTy derefLifetime →
    store.loc (.deref source) = some updated →
    store.slotAt updated = some updatedSlot →
    ValidPartialValue store updatedSlot.value updatedTy →
    (∀ x envSlot,
      envCoarse.slotAt x = some envSlot →
      VariableProjection x = updated →
        newSlot.lifetime = envSlot.lifetime) →
      ConcreteRuntimeRootsSafe (store.update updated newSlot) envCoarse := by
  intro hgate hφ hwellFormed hroots hnewSafe hprov hvalidStore hheap
    hsafe hsource hderef hupdated hupdatedSlot hupdatedValid hlifetime
  exact ConcreteRuntimeRootsSafe.update_of_mut_borrow_provenance_gate
    hgate hroots hnewSafe hprov hsource hupdated hlifetime
    (by
      intro x envSlot value hx henvSlot hstoreSlot hrootNe
      exact not_below_invalidated_owner_root_of_firstNode hφ hwellFormed
        hsafe hvalidStore hheap hsource hderef hupdated hupdatedSlot
        hupdatedValid hx henvSlot hstoreSlot hrootNe)

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
  case strong | weak | box | mutBorrow => intros; trivial
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
                    have hcellProt : ProtectedByBase store (LVal.base u) cell :=
                      StoreOwnerSpine.protectedByBase h6 rfl
                    have hGtarget :
                        WriteGuarded store env leaf base₀ (LVal.base tSel) :=
                      WriteGuarded.step hGbase ⟨envSlot, h1, hcontains⟩
                        hmemSel rfl hkill
                        ⟨cell, cellSlot, L, hcellProt, h3, h4, hlocSel⟩
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

/-- The borrow-resolution dependency's target is a *live* target: the leaf borrow
value (reached through any owning boxes from a cell holding `value`) is a
reference to the location that `target` resolves to.  So `TargetPointedTo` holds
for the dependency target. -/
theorem RuntimeFrame.borrowDependency_targetPointedTo {store : ProgramStore}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {cell : Location} {cellSlot : StoreSlot} :
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    store.slotAt cell = some cellSlot →
    cellSlot.value = value →
    ∃ mutable targets target,
      PartialTyContains partialTy (.borrow mutable targets) ∧
      target ∈ targets ∧
      RuntimeFrame.LocReads store target dependency ∧
      TargetPointedTo store target := by
  intro hdep
  induction hdep generalizing cell cellSlot with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      intro hcell hval
      exact ⟨mutable, targets, target, PartialTyContains.here, hmem, hreads,
        ⟨cell, cellSlot, location, hcell, hval, hloc⟩⟩
  | @boxInner location slot inner dep hslot _hinner ih =>
      intro _hcell _hval
      rcases ih hslot rfl with ⟨m, ts, t, hcontains, hmem, hreads, htpt⟩
      exact ⟨m, ts, t, PartialTyContains.box hcontains, hmem, hreads, htpt⟩
  | @boxFullInner location slot innerTy dep hslot _hinner ih =>
      intro _hcell _hval
      rcases ih hslot rfl with ⟨m, ts, t, hcontains, hmem, hreads, htpt⟩
      exact ⟨m, ts, t, PartialTyContains.tyBox hcontains, hmem, hreads, htpt⟩

/-- The same as `borrowDependency_targetPointedTo`, but the dependency's target is
*selected* by the root variable `x` that owns the dependency-bearing cell: every
cell crossed by the borrow-resolution descent is owned by `x` (the descent only
follows owning boxes), so the leaf borrow cell holding the reference to the
target's location is `ProtectedByBase store x`.  This is exactly the
`SelectedTarget` used by selected-target frame lemmas. -/
theorem RuntimeFrame.borrowDependency_selectedTarget {store : ProgramStore}
    {value : PartialValue} {partialTy : PartialTy} {dependency : Location}
    {cell : Location} {cellSlot : StoreSlot} {x : Name} :
    RuntimeFrame.BorrowDependency store value partialTy dependency →
    store.slotAt cell = some cellSlot →
    cellSlot.value = value →
    ProtectedByBase store x cell →
    ∃ mutable targets target,
      PartialTyContains partialTy (.borrow mutable targets) ∧
      target ∈ targets ∧
      RuntimeFrame.LocReads store target dependency ∧
      SelectedTarget store x target := by
  intro hdep
  induction hdep generalizing cell cellSlot with
  | @borrow location readLocation mutable targets target hmem hloc hreads =>
      intro hcell hval hprot
      exact ⟨mutable, targets, target, PartialTyContains.here, hmem, hreads,
        ⟨cell, cellSlot, location, hprot, hcell, hval, hloc⟩⟩
  | @boxInner location slot inner dep hslot _hinner ih =>
      intro hcell hval hprot
      have howns : ProgramStore.OwnsAt store location cell :=
        ⟨cellSlot.lifetime, by
          rw [hcell]; cases cellSlot; simp [owningRef] at hval ⊢; exact hval⟩
      have hprotInner : ProtectedByBase store x location :=
        ProtectedByBase.trans_owned hprot howns
      rcases ih hslot rfl hprotInner with ⟨m, ts, t, hcontains, hmem, hreads, hsel⟩
      exact ⟨m, ts, t, PartialTyContains.box hcontains, hmem, hreads, hsel⟩
  | @boxFullInner location slot innerTy dep hslot _hinner ih =>
      intro hcell hval hprot
      have howns : ProgramStore.OwnsAt store location cell :=
        ⟨cellSlot.lifetime, by
          rw [hcell]; cases cellSlot; simp [owningRef] at hval ⊢; exact hval⟩
      have hprotInner : ProtectedByBase store x location :=
        ProtectedByBase.trans_owned hprot howns
      rcases ih hslot rfl hprotInner with ⟨m, ts, t, hcontains, hmem, hreads, hsel⟩
      exact ⟨m, ts, t, PartialTyContains.tyBox hcontains, hmem, hreads, hsel⟩

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
