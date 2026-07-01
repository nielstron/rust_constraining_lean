import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Bounds.Basic
import LwRust.Paper.Runtime

/-!
Typing and borrow-checking judgments for the core FR calculus in Section 3.4.

The paper presents the auxiliary operations as mathematical partial functions.
Here they are deliberately relational when determinism is not needed by the
semantics or later metatheory.
-/

namespace LwRust
namespace Paper

open Core

/-- A typing-environment slot `⟨T̃⟩^m`. -/
structure EnvSlot where
  ty : PartialTy
  lifetime : Lifetime
  deriving BEq, Repr

/-- Paper typing environment `Γ`, as a finite partial map abstracted by lookup. -/
structure Env where
  slotAt : Name → Option EnvSlot

namespace Env

def empty : Env :=
  { slotAt := fun _ => none }

def fresh (env : Env) (x : Name) : Prop :=
  env.slotAt x = none

def update (env : Env) (x : Name) (slot : EnvSlot) : Env :=
  { slotAt := fun y => if y = x then some slot else env.slotAt y }

def erase (env : Env) (x : Name) : Env :=
  { slotAt := fun y => if y = x then none else env.slotAt y }

def eraseMany (env : Env) : List Name → Env
  | [] => env
  | erased :: rest => (env.erase erased).eraseMany rest

@[simp] theorem update_slotAt_same (env : Env) (x : Name) (slot : EnvSlot) :
    (env.update x slot).slotAt x = some slot := by
  simp [update]

@[simp] theorem update_slotAt_ne (env : Env) {x y : Name} (slot : EnvSlot) :
    y ≠ x →
    (env.update x slot).slotAt y = env.slotAt y := by
  intro hne
  simp [update, hne]

@[simp] theorem erase_slotAt_same (env : Env) (x : Name) :
    (env.erase x).slotAt x = none := by
  simp [erase]

@[simp] theorem erase_slotAt_ne (env : Env) {x y : Name} :
    y ≠ x →
    (env.erase x).slotAt y = env.slotAt y := by
  intro hne
  simp [erase, hne]

@[simp] theorem erase_update_fresh (env : Env) (x : Name) (slot : EnvSlot) :
    env.fresh x →
    (env.update x slot).erase x = env := by
  intro hfresh
  cases env with
  | mk slotAt =>
      simp [erase, update, fresh] at hfresh ⊢
      funext y
      by_cases hy : y = x
      · subst hy
        simpa using hfresh.symm
      · simp [hy]

/-- The abstract environment has only finitely many defined variable slots. -/
def FiniteSupport (env : Env) : Prop :=
  ∃ support : Finset Name,
    ∀ x slot, env.slotAt x = some slot → x ∈ support

theorem finiteSupport_empty : FiniteSupport Env.empty :=
  ⟨∅, by intro x slot hslot; simp [Env.empty] at hslot⟩

theorem FiniteSupport.update {env : Env} {x : Name} {slot : EnvSlot} :
    FiniteSupport env → FiniteSupport (env.update x slot) := by
  rintro ⟨support, hsupport⟩
  refine ⟨insert x support, ?_⟩
  intro y slot' hslot'
  by_cases hy : y = x
  · subst hy
    exact Finset.mem_insert_self _ _
  · rw [Env.update_slotAt_ne _ _ hy] at hslot'
    exact Finset.mem_insert_of_mem (hsupport y slot' hslot')

theorem FiniteSupport.erase {env : Env} {x : Name} :
    FiniteSupport env → FiniteSupport (env.erase x) := by
  rintro ⟨support, hsupport⟩
  refine ⟨support, ?_⟩
  intro y slot hslot
  by_cases hy : y = x
  · subst hy
    simp at hslot
  · rw [Env.erase_slotAt_ne _ hy] at hslot
    exact hsupport y slot hslot

end Env

/--
Store typing `σ` for locations in flight during reduction, as discussed in
Section 3.3 and used by T-Const.
-/
structure StoreTyping where
  tyOf : Location → Option Ty

namespace StoreTyping

def empty : StoreTyping :=
  { tyOf := fun _ => none }

def update (typing : StoreTyping) (location : Location) (ty : Ty) : StoreTyping :=
  { tyOf := fun candidate =>
      if candidate = location then some ty else typing.tyOf candidate }

/-- The abstract store typing has only finitely many typed locations. -/
def FiniteSupport (typing : StoreTyping) : Prop :=
  ∃ support : Finset Location,
    ∀ location ty, typing.tyOf location = some ty → location ∈ support

theorem finiteSupport_empty : FiniteSupport StoreTyping.empty :=
  ⟨∅, by intro location ty hlookup; simp [StoreTyping.empty] at hlookup⟩

theorem FiniteSupport.update {typing : StoreTyping}
    {location : Location} {ty : Ty} :
    FiniteSupport typing → FiniteSupport (typing.update location ty) := by
  rintro ⟨support, hsupport⟩
  refine ⟨insert location support, ?_⟩
  intro candidate ty' hlookup
  by_cases hsame : candidate = location
  · subst hsame
    exact Finset.mem_insert_self _ _
  · simp [StoreTyping.update, hsame] at hlookup
    exact Finset.mem_insert_of_mem (hsupport candidate ty' hlookup)

end StoreTyping

/-- Definition 3.6, `copy(T)`, extended with `bool` (Section 6.1). -/
inductive CopyTy : Ty → Prop where
  | unit :
      CopyTy .unit
  | int :
      CopyTy .int
  | bool :
      CopyTy .bool
  | immBorrow {targets : List LVal} :
      CopyTy (.borrow false targets)

/-- Definition 3.7, type strengthening `T̃₁ ⊑ T̃₂`. -/
inductive PartialTyStrengthens : PartialTy → PartialTy → Prop where
  /-- W-Reflex. -/
  | reflex {ty : PartialTy} :
      PartialTyStrengthens ty ty
  /-- W-Box. -/
  | box {left right : PartialTy} :
      PartialTyStrengthens left right →
      PartialTyStrengthens (.box left) (.box right)
  /-- W-Box for fully initialized owner types. -/
  | tyBox {left right : Ty} :
      PartialTyStrengthens (.ty left) (.ty right) →
      PartialTyStrengthens (.ty (.box left)) (.ty (.box right))
  /-- W-Bor. -/
  | borrow {mutable : Bool} {leftTargets rightTargets : List LVal} :
      leftTargets.Subset rightTargets →
      PartialTyStrengthens (.ty (.borrow mutable leftTargets))
        (.ty (.borrow mutable rightTargets))
  /-- W-UndefA. -/
  | undefLeft {left right : Ty} :
      PartialTyStrengthens (.ty left) (.ty right) →
      PartialTyStrengthens (.undef left) (.undef right)
  /-- W-UndefB. -/
  | intoUndef {left right : Ty} :
      PartialTyStrengthens (.ty left) (.ty right) →
      PartialTyStrengthens (.ty left) (.undef right)
  /-- W-UndefC. -/
  | boxIntoUndef {left : PartialTy} {right : Ty} :
      PartialTyStrengthens left (.undef right) →
      PartialTyStrengthens (.box left) (.undef (.box right))

instance : LE PartialTy where
  le := PartialTyStrengthens

@[simp] theorem partialTy_le_iff (left right : PartialTy) :
    left ≤ right ↔ PartialTyStrengthens left right :=
  Iff.rfl

@[refl, simp] theorem PartialTyStrengthens.refl (ty : PartialTy) :
    PartialTyStrengthens ty ty :=
  PartialTyStrengthens.reflex

@[refl, simp] theorem partialTy_le_refl (ty : PartialTy) :
    ty ≤ ty :=
  PartialTyStrengthens.reflex

/--
Definition 3.8, type join `T̃₁ ⊔ T̃₂`.

The paper defines this as a partial function returning the strongest
`T̃₃` such that both inputs strengthen `T̃₃`.  We keep it relational, but spell
out that paper definition directly: `join` must be a common weakening of the
two inputs, and every other common weakening must be weaker than `join`.

In the `T-LvBor` rule, the paper writes the same operation over a finite target
list as `⋃ᵢ Tᵢ`; this is a join/union of static type information, not a set
union of runtime locations.
-/
def PartialTyJoin (left right join : PartialTy) : Prop :=
  (∀ {candidate},
      candidate ∈ ({left, right} : Set PartialTy) →
        PartialTyStrengthens candidate join) ∧
    ∀ {upper},
      (∀ candidate,
        candidate ∈ ({left, right} : Set PartialTy) →
          PartialTyStrengthens candidate upper) →
        PartialTyStrengthens join upper

@[simp] theorem PartialTyJoin.self (ty : PartialTy) :
    PartialTyJoin ty ty ty := by
  simp [PartialTyJoin]

theorem PartialTyJoin.isLUB {left right join : PartialTy} :
    PartialTyJoin left right join →
    IsLUB ({left, right} : Set PartialTy) join := by
  intro hjoin
  simpa [PartialTyJoin, IsLUB, IsLeast, upperBounds, lowerBounds,
    partialTy_le_iff] using hjoin

theorem PartialTyJoin.of_isLUB {left right join : PartialTy} :
    IsLUB ({left, right} : Set PartialTy) join →
    PartialTyJoin left right join := by
  intro hjoin
  simpa [PartialTyJoin, IsLUB, IsLeast, upperBounds, lowerBounds,
    partialTy_le_iff] using hjoin

theorem partialTyJoin_iff_isLUB (left right join : PartialTy) :
    PartialTyJoin left right join ↔
      IsLUB ({left, right} : Set PartialTy) join :=
  ⟨PartialTyJoin.isLUB, PartialTyJoin.of_isLUB⟩

/-- Paper-facing name for the type union used in `T-LvBor`. -/
def PartialTyUnion (left right union : PartialTy) : Prop :=
  PartialTyJoin left right union

@[simp] theorem partialTyUnion_iff_join (left right union : PartialTy) :
    PartialTyUnion left right union ↔ PartialTyJoin left right union :=
  Iff.rfl

@[simp] theorem PartialTyUnion.self (ty : PartialTy) :
    PartialTyUnion ty ty ty := by
  simp [PartialTyUnion]

/-- Definition 3.9, environment strengthening `Γ₁ ⊑ Γ₂`. -/
def EnvStrengthens (left right : Env) : Prop :=
  ∀ x,
    match left.slotAt x, right.slotAt x with
    | none, none => True
    | some leftSlot, some rightSlot =>
        leftSlot.lifetime = rightSlot.lifetime ∧
        PartialTyStrengthens leftSlot.ty rightSlot.ty
    | _, _ => False

instance : LE Env where
  le := EnvStrengthens

@[simp] theorem env_le_iff (left right : Env) :
    left ≤ right ↔ EnvStrengthens left right :=
  Iff.rfl

@[refl, simp] theorem EnvStrengthens.refl (env : Env) :
    EnvStrengthens env env := by
  intro x
  cases env.slotAt x <;> simp

@[refl, simp] theorem env_le_refl (env : Env) :
    env ≤ env :=
  EnvStrengthens.refl env

/--
Definition 3.10, environment join `Γ₁ ⊔ Γ₂`.

As for Definition 3.8, the paper presents this as a partial function returning
the strongest environment strengthened by both inputs.  The relational encoding
below is that definition: `join` is a common weakening, and it strengthens every
other common weakening.
-/
def EnvJoin (left right join : Env) : Prop :=
  (∀ {candidate},
      candidate ∈ ({left, right} : Set Env) →
        EnvStrengthens candidate join) ∧
    ∀ {upper},
      (∀ candidate,
        candidate ∈ ({left, right} : Set Env) →
          EnvStrengthens candidate upper) →
        EnvStrengthens join upper

theorem EnvJoin.isLUB {left right join : Env} :
    EnvJoin left right join →
    IsLUB ({left, right} : Set Env) join := by
  intro hjoin
  simpa [EnvJoin, IsLUB, IsLeast, upperBounds, lowerBounds, env_le_iff] using hjoin

theorem EnvJoin.of_isLUB {left right join : Env} :
    IsLUB ({left, right} : Set Env) join →
    EnvJoin left right join := by
  intro hjoin
  simpa [EnvJoin, IsLUB, IsLeast, upperBounds, lowerBounds, env_le_iff] using hjoin

theorem envJoin_iff_isLUB (left right join : Env) :
    EnvJoin left right join ↔ IsLUB ({left, right} : Set Env) join :=
  ⟨EnvJoin.isLUB, EnvJoin.of_isLUB⟩

def LifetimeOutlives (outer inner : Lifetime) : Prop :=
  outer.contains inner

instance : LE Lifetime where
  le := LifetimeOutlives

@[simp] theorem lifetime_le_iff_outlives (outer inner : Lifetime) :
    outer ≤ inner ↔ LifetimeOutlives outer inner :=
  Iff.rfl

@[simp] theorem lifetimeOutlives_iff_contains (outer inner : Lifetime) :
    LifetimeOutlives outer inner ↔ outer.contains inner :=
  Iff.rfl

/-- Paper `l ≺ m`: `m` is the immediate nested block lifetime below `l`. -/
def LifetimeChild (parent child : Lifetime) : Prop :=
  ∃ label, child.path = parent.path ++ [label]

@[refl, simp] theorem LifetimeOutlives.refl (lifetime : Lifetime) :
    LifetimeOutlives lifetime lifetime := by
  simp [LifetimeOutlives, Core.Lifetime.contains]

example : (([0] : Lifetime) ≤ ([0, 0] : Lifetime)) := by
  simp [LifetimeOutlives, Core.Lifetime.contains]

example : ¬ (([0] : Lifetime) ≤ ([1] : Lifetime)) := by
  simp [LifetimeOutlives, Core.Lifetime.contains]

/--
Paper `⋂` for lifetimes: the common/innermost lifetime of two active
lifetimes.

Because our order is `outer ≤ inner` meaning "`outer` outlives `inner`", this
paper intersection is an order-theoretic least upper bound.  For example,
`[0] ≤ [0, 0]`, and the common lifetime of `[0]` and `[0, 0]` is `[0, 0]`.
-/
def LifetimeIntersection (left right intersection : Lifetime) : Prop :=
  IsLUB ({left, right} : Set Lifetime) intersection

theorem LifetimeIntersection.left {outer inner : Lifetime} :
    outer ≤ inner →
    LifetimeIntersection outer inner inner := by
  intro h
  constructor
  · intro lifetime hmem
    simp at hmem
    rcases hmem with houter | hinner
    · simpa [houter] using h
    · simpa [hinner] using LifetimeOutlives.refl inner
  · intro lifetime hupper
    exact hupper (by simp)

theorem LifetimeIntersection.right {outer inner : Lifetime} :
    inner ≤ outer →
    LifetimeIntersection outer inner outer := by
  intro h
  constructor
  · intro lifetime hmem
    simp at hmem
    rcases hmem with houter | hinner
    · simpa [houter] using LifetimeOutlives.refl outer
    · simpa [hinner] using h
  · intro lifetime hupper
    exact hupper (by simp)

@[simp] theorem LifetimeIntersection.self (lifetime : Lifetime) :
    LifetimeIntersection lifetime lifetime lifetime :=
  LifetimeIntersection.left (LifetimeOutlives.refl lifetime)

/--
Paper-facing alias for `LifetimeIntersection`.  With our `≤`, this is a LUB
rather than a GLB; the name is kept because the paper writes `⋂ᵢ mᵢ`.
-/
def LifetimeMeet (left right meet : Lifetime) : Prop :=
  LifetimeIntersection left right meet

@[simp] theorem lifetimeMeet_iff_intersection (left right meet : Lifetime) :
    LifetimeMeet left right meet ↔ LifetimeIntersection left right meet :=
  Iff.rfl

@[simp] theorem LifetimeMeet.self (lifetime : Lifetime) :
    LifetimeMeet lifetime lifetime lifetime := by
  simp [LifetimeMeet]

/-- Base variable of an lvalue. -/
def LVal.base : LVal → Name
  | .var x => x
  | .deref lv => LVal.base lv

/-- Variables occurring in live loans of a full type.

For borrow types, the target list contributes the live loan variables.
-/
def Ty.vars : Ty → List Name
  | .unit => []
  | .int => []
  | .bool => []
  | .borrow _ targets => targets.map LVal.base
  | .box inner => Ty.vars inner

/-- Variables occurring anywhere in full-type annotations. -/
def Ty.allVars : Ty → List Name
  | .unit => []
  | .int => []
  | .bool => []
  | .borrow _ targets => targets.map LVal.base
  | .box inner => Ty.allVars inner

mutual
  /-- Definition 3.11, lval typing `Γ ⊢ w : ⟨T̃⟩^m`. -/
  inductive LValTyping : Env → LVal → PartialTy → Lifetime → Prop where
    /-- T-LvVar. -/
    | var {env : Env} {x : Name} {slot : EnvSlot} :
        env.slotAt x = some slot →
        LValTyping env (.var x) slot.ty slot.lifetime
    /-- T-LvBox. -/
    | box {env : Env} {lv : LVal} {inner : PartialTy} {lifetime : Lifetime} :
        LValTyping env lv (.box inner) lifetime →
        LValTyping env (.deref lv) inner lifetime
    /-- T-LvBox for fully initialized owner types. -/
    | boxFull {env : Env} {lv : LVal} {inner : Ty} {lifetime : Lifetime} :
        LValTyping env lv (.ty (.box inner)) lifetime →
        LValTyping env (.deref lv) (.ty inner) lifetime
    /--
    T-LvBor.  If `w` has borrow type over target list `u`, then `*w` has the
    finite union of the target types and the intersection/meet of their
    lifetimes.
    -/
    | borrow {env : Env} {lv : LVal} {mutable : Bool} {targets : List LVal}
        {borrowLifetime targetLifetime : Lifetime} {targetTy : PartialTy} :
        LValTyping env lv (.ty (.borrow mutable targets)) borrowLifetime →
        LValTargetsTyping env targets targetTy targetLifetime →
        LValTyping env (.deref lv) targetTy targetLifetime

  /--
  The paper premise `Γ ⊢ u : ⟨⋃ᵢ Tᵢ⟩^(⋂ᵢ mᵢ)` for a finite, non-empty list
  of borrowed lvals.
  -/
  inductive LValTargetsTyping : Env → List LVal → PartialTy → Lifetime → Prop where
    | singleton {env : Env} {target : LVal} {ty : Ty} {lifetime : Lifetime} :
        LValTyping env target (.ty ty) lifetime →
        LValTargetsTyping env [target] (.ty ty) lifetime
    | cons {env : Env} {target : LVal} {rest : List LVal}
        {headTy : Ty} {headLifetime restLifetime lifetime : Lifetime}
        {restTy unionTy : PartialTy} :
        LValTyping env target (.ty headTy) headLifetime →
        LValTargetsTyping env rest restTy restLifetime →
        PartialTyUnion (.ty headTy) restTy unionTy →
        LifetimeIntersection headLifetime restLifetime lifetime →
        LValTargetsTyping env (target :: rest) unionTy lifetime
end

/--
Stale-aware target-list typing used by coherence invariants.

Unlike `LValTargetsTyping`, this allows a target to contribute an `undef`
partial type.  It records that the static target list still has a least common
partial type, without making the corresponding borrow dereference readable:
`T-LvBor` continues to use `LValTargetsTyping`, whose singleton targets must be
fully initialized.
-/
inductive LValTargetsMaybeTyping :
    Env → List LVal → PartialTy → Lifetime → Prop where
  | singleton {env : Env} {target : LVal} {partialTy : PartialTy}
      {lifetime : Lifetime} :
      LValTyping env target partialTy lifetime →
      LValTargetsMaybeTyping env [target] partialTy lifetime
  | cons {env : Env} {target : LVal} {rest : List LVal}
      {headTy : PartialTy} {headLifetime restLifetime lifetime : Lifetime}
      {restTy unionTy : PartialTy} :
      LValTyping env target headTy headLifetime →
      LValTargetsMaybeTyping env rest restTy restLifetime →
      PartialTyUnion headTy restTy unionTy →
      LifetimeIntersection headLifetime restLifetime lifetime →
      LValTargetsMaybeTyping env (target :: rest) unionTy lifetime

theorem LValTargetsTyping.toMaybe {env : Env} {targets : List LVal}
    {partialTy : PartialTy} {lifetime : Lifetime} :
    LValTargetsTyping env targets partialTy lifetime →
    LValTargetsMaybeTyping env targets partialTy lifetime := by
  intro htyping
  exact LValTargetsTyping.rec
    (motive_1 := fun _lv _partialTy _lifetime _ => True)
    (motive_2 := fun targets partialTy lifetime _ =>
      LValTargetsMaybeTyping env targets partialTy lifetime)
    (by intro _x _slot _hslot; trivial)
    (by intro _lv _inner _lifetime _htyping _ih; trivial)
    (by intro _lv _inner _lifetime _htyping _ih; trivial)
    (by
      intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
        _hborrow _htargets _ihBorrow _ihTargets
      trivial)
    (by
      intro target _ty _lifetime htarget _ihTarget
      exact LValTargetsMaybeTyping.singleton htarget)
    (by
      intro target rest _headTy _headLifetime _restLifetime _lifetime _restTy
        _unionTy hhead _hrest hunion hintersection _ihHead ihRest
      exact LValTargetsMaybeTyping.cons hhead ihRest hunion hintersection)
    htyping

/-- Definitions 3.12 and 3.13 collapse to a list of dereference selectors. -/
abbrev Path := List Unit

def LVal.path : LVal → Path
  | .var _ => []
  | .deref lv => LVal.path lv ++ [()]

/--
Strict prefix on dereference paths.  `[]` is a strict prefix of any non-empty
path, and prefix comparison proceeds structurally through matching derefs.
-/
def StrictPathPrefix : Path → Path → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | _ :: left, _ :: right => StrictPathPrefix left right

/--
The written lvalue is a strict resolution prefix of the target lvalue.

If `written ≺ target`, then overwriting the location denoted by `written` can
change the later dereference steps used to resolve `target`.  For example,
`p ≺ *p` and `*p ≺ **p`, but `p` is not a strict prefix of `p`.
-/
def LVal.StrictPrefixOf (written target : LVal) : Prop :=
  LVal.base written = LVal.base target ∧
    StrictPathPrefix (LVal.path written) (LVal.path target)

theorem StrictPathPrefix.self_append_singleton :
    ∀ path : Path, StrictPathPrefix path (path ++ [()])
  | [] => by simp [StrictPathPrefix]
  | _ :: tail => by
      simpa [StrictPathPrefix] using
        StrictPathPrefix.self_append_singleton tail

theorem StrictPathPrefix.append_right_singleton :
    ∀ {left right : Path}, StrictPathPrefix left right →
      StrictPathPrefix left (right ++ [()])
  | [], [], hprefix => by cases hprefix
  | [], _ :: _, _ => by simp [StrictPathPrefix]
  | _ :: _, [], hprefix => by cases hprefix
  | _ :: left, _ :: right, hprefix => by
      simpa [StrictPathPrefix] using
        StrictPathPrefix.append_right_singleton
          (left := left) (right := right) hprefix

theorem StrictPathPrefix.exists_suffix :
    ∀ {left right : Path}, StrictPathPrefix left right →
      ∃ suffix : Path, suffix ≠ [] ∧ right = left ++ suffix := by
  intro left
  induction left with
  | nil =>
      intro right hprefix
      cases right with
      | nil => cases hprefix
      | cons head tail =>
          cases head
          exact ⟨() :: tail, by simp, rfl⟩
  | cons head left ih =>
      intro right hprefix
      cases head
      cases right with
      | nil => cases hprefix
      | cons headRight right =>
          cases headRight
          rcases ih hprefix with ⟨suffix, hnonempty, hright⟩
          exact ⟨suffix, hnonempty, by simp [hright]⟩

theorem LVal.StrictPrefixOf.self_deref (lv : LVal) :
    LVal.StrictPrefixOf lv (.deref lv) := by
  constructor
  · simp [LVal.base]
  · simpa [LVal.path] using
      StrictPathPrefix.self_append_singleton (LVal.path lv)

theorem LVal.StrictPrefixOf.deref_right {written target : LVal} :
    LVal.StrictPrefixOf written target →
    LVal.StrictPrefixOf written (.deref target) := by
  intro hprefix
  rcases hprefix with ⟨hbase, hpath⟩
  constructor
  · simpa [LVal.base] using hbase
  · simpa [LVal.path] using
      StrictPathPrefix.append_right_singleton hpath

theorem LVal.eq_of_base_path :
    ∀ {left right : LVal},
      LVal.base left = LVal.base right →
      LVal.path left = LVal.path right →
      left = right
  | .var x, .var y, hbase, _hpath => by
      simp [LVal.base] at hbase
      simp [hbase]
  | .var _x, .deref _right, _hbase, hpath => by
      simp [LVal.path] at hpath
  | .deref _left, .var _y, _hbase, hpath => by
      simp [LVal.path] at hpath
  | .deref left, .deref right, hbase, hpath => by
      have hpath' : LVal.path left = LVal.path right := by
        simpa [LVal.path, List.append_cancel_right_eq] using hpath
      exact congrArg LVal.deref (LVal.eq_of_base_path hbase hpath')

/-- Syntactic occurrence of a variable name in an lvalue. -/
def LVal.Mentions (x : Name) : LVal → Prop
  | .var y => y = x
  | .deref lv => LVal.Mentions x lv

/-- The finite set of variable names syntactically mentioned by an lvalue. -/
def LVal.names : LVal → Finset Name
  | .var x => {x}
  | .deref lv => LVal.names lv

mutual
  /-- Syntactic occurrence of a variable name in a term. -/
  def Term.Mentions (x : Name) : Term → Prop
    | .block _ terms => TermList.Mentions x terms
    | .letMut y initialiser => y = x ∨ Term.Mentions x initialiser
    | .assign lhs rhs => LVal.Mentions x lhs ∨ Term.Mentions x rhs
    | .box operand => Term.Mentions x operand
    | .borrow _ operand => LVal.Mentions x operand
    | .move operand => LVal.Mentions x operand
    | .copy operand => LVal.Mentions x operand
    | .val _ => False
    | .missing => False
    | .eq lhs rhs => Term.Mentions x lhs ∨ Term.Mentions x rhs
    | .ite condition trueBranch falseBranch =>
        Term.Mentions x condition ∨ Term.Mentions x trueBranch ∨
          Term.Mentions x falseBranch

  /-- Syntactic occurrence of a variable name in a term list. -/
  def TermList.Mentions (x : Name) : List Term → Prop
    | [] => False
    | term :: rest => Term.Mentions x term ∨ TermList.Mentions x rest
end

/- The finite set of variable names syntactically mentioned by a term. -/
mutual
  def Term.names : Term → Finset Name
    | .block _ terms => TermList.names terms
    | .letMut x initialiser => {x} ∪ Term.names initialiser
    | .assign lhs rhs => LVal.names lhs ∪ Term.names rhs
    | .box operand => Term.names operand
    | .borrow _ operand => LVal.names operand
    | .move operand => LVal.names operand
    | .copy operand => LVal.names operand
    | .val _ => ∅
    | .missing => ∅
    | .eq lhs rhs => Term.names lhs ∪ Term.names rhs
    | .ite condition trueBranch falseBranch =>
        Term.names condition ∪ Term.names trueBranch ∪ Term.names falseBranch

  def TermList.names : List Term → Finset Name
    | [] => ∅
    | term :: rest => Term.names term ∪ TermList.names rest
end

theorem LVal.mentions_mem_names {x : Name} :
    ∀ {lv : LVal}, LVal.Mentions x lv → x ∈ LVal.names lv
  | .var y, hmentions => by
      simp [LVal.Mentions, LVal.names] at hmentions ⊢
      exact hmentions.symm
  | .deref lv, hmentions => by
      induction lv with
      | var y =>
          simp [LVal.Mentions, LVal.names] at hmentions ⊢
          exact hmentions.symm
      | deref lv ih =>
          exact ih hmentions

theorem Term.mentions_mem_names {x : Name} {term : Term}
    (hmentions : Term.Mentions x term) : x ∈ Term.names term := by
  revert hmentions
  refine Term.rec
    (motive_1 := fun term => Term.Mentions x term → x ∈ Term.names term)
    (motive_2 := fun terms => TermList.Mentions x terms → x ∈ TermList.names terms)
    ?block ?letMut ?assign ?box ?borrow ?move ?copy ?val ?missing ?eq ?ite
    ?nil ?cons term
  case block =>
    intro _lifetime _terms ih hmentions
    exact ih hmentions
  case letMut =>
    intro y _initialiser ih hmentions
    rcases hmentions with hdecl | hinitialiser
    · exact Finset.mem_union.mpr (Or.inl (by simp [hdecl]))
    · exact Finset.mem_union.mpr (Or.inr (ih hinitialiser))
  case assign =>
    intro _lhs _rhs ih hmentions
    rcases hmentions with hlhs | hrhs
    · exact Finset.mem_union.mpr (Or.inl (LVal.mentions_mem_names hlhs))
    · exact Finset.mem_union.mpr (Or.inr (ih hrhs))
  case box =>
    intro _operand ih hmentions
    exact ih hmentions
  case borrow =>
    intro _mutable _operand hmentions
    exact LVal.mentions_mem_names hmentions
  case move =>
    intro _operand hmentions
    exact LVal.mentions_mem_names hmentions
  case copy =>
    intro _operand hmentions
    exact LVal.mentions_mem_names hmentions
  case val =>
    intro _value hmentions
    cases hmentions
  case missing =>
    intro hmentions
    cases hmentions
  case eq =>
    intro _lhs _rhs ihLhs ihRhs hmentions
    rcases hmentions with hlhs | hrhs
    · exact Finset.mem_union.mpr (Or.inl (ihLhs hlhs))
    · exact Finset.mem_union.mpr (Or.inr (ihRhs hrhs))
  case ite =>
    intro _condition _trueBranch _falseBranch ihCondition ihTrue ihFalse
      hmentions
    rcases hmentions with hcondition | htrue | hfalse
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl (ihCondition hcondition))))
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inr (ihTrue htrue))))
    · exact Finset.mem_union.mpr (Or.inr (ihFalse hfalse))
  case nil =>
    intro hmentions
    cases hmentions
  case cons =>
    intro _head _tail ihHead ihTail hmentions
    rcases hmentions with hhead | htail
    · exact Finset.mem_union.mpr (Or.inl (ihHead hhead))
    · exact Finset.mem_union.mpr (Or.inr (ihTail htail))

theorem TermList.mentions_mem_names {x : Name} :
    ∀ {terms : List Term}, TermList.Mentions x terms → x ∈ TermList.names terms
  | [], hmentions => by
      cases hmentions
  | term :: rest, hmentions => by
      rcases hmentions with hterm | hrest
      · exact Finset.mem_union.mpr
          (Or.inl (Term.mentions_mem_names hterm))
      · exact Finset.mem_union.mpr
          (Or.inr (TermList.mentions_mem_names hrest))

theorem Term.not_mentions_of_not_mem_names {x : Name} {term : Term} :
    x ∉ Term.names term → ¬ Term.Mentions x term := by
  intro hnot hmentions
  exact hnot (Term.mentions_mem_names hmentions)

/-- Variables occurring (in live borrows) in a partial type.

`undef` shadows are moved-out and carry no live borrow, mirroring
`PartialTyContains`, which does not descend into `undef`. -/
def PartialTy.vars : PartialTy → List Name
  | .ty t => Ty.vars t
  | .box inner => PartialTy.vars inner
  | .undef _ => []

/-- Variables occurring anywhere in a partial type, including dead `undef` shadows.

`PartialTy.vars` deliberately ignores `undef` for live-borrow invariants.  Ghost
erasure also has to preserve shape checks, and those can inspect the type carried
under `undef`, so freshness for anonymous equality slots uses this stronger
view. -/
def PartialTy.allVars : PartialTy → List Name
  | .ty t => Ty.allVars t
  | .box inner => PartialTy.allVars inner
  | .undef t => Ty.allVars t

mutual
  theorem Ty.vars_subset_allVars {ty : Ty} {v : Name} :
      v ∈ Ty.vars ty → v ∈ Ty.allVars ty := by
    cases ty with
    | unit => intro h; simpa [Ty.vars] using h
    | int => intro h; simpa [Ty.vars] using h
    | bool => intro h; simpa [Ty.vars] using h
    | borrow mutable targets =>
        intro h
        simpa [Ty.vars, Ty.allVars] using h
    | box inner =>
        intro h
        exact Ty.vars_subset_allVars (ty := inner) (by simpa [Ty.vars] using h)

  theorem PartialTy.vars_subset_allVars {partialTy : PartialTy} {v : Name} :
      v ∈ PartialTy.vars partialTy → v ∈ PartialTy.allVars partialTy := by
    cases partialTy with
    | ty ty =>
        intro h
        exact Ty.vars_subset_allVars (by simpa [PartialTy.vars] using h)
    | box inner =>
        intro h
        exact PartialTy.vars_subset_allVars (partialTy := inner)
          (by simpa [PartialTy.vars] using h)
    | undef ty =>
        intro h
        simpa [PartialTy.vars] using h
end

/-- A name does not occur in any borrow target inside an environment type,
including the type shadows carried below `undef`. -/
def Env.TypeNameFresh (env : Env) (x : Name) : Prop :=
  ∀ y slot, env.slotAt y = some slot → x ∉ PartialTy.allVars slot.ty

namespace StoreTyping

/-- A name does not occur in any live borrow target inside store-typed values. -/
def TypeNameFresh (typing : StoreTyping) (x : Name) : Prop :=
  ∀ location ty, typing.tyOf location = some ty → x ∉ Ty.allVars ty

@[simp] theorem empty_typeNameFresh (x : Name) :
    TypeNameFresh StoreTyping.empty x := by
  intro location ty hlookup
  simp [StoreTyping.empty] at hlookup

end StoreTyping

/-- Finite environment domains mention only finitely many names inside slot types. -/
theorem Env.FiniteSupport.typeNameSupport {env : Env} :
    Env.FiniteSupport env →
    ∃ support : Finset Name,
      ∀ y slot x,
        env.slotAt y = some slot →
        x ∈ PartialTy.allVars slot.ty →
        x ∈ support := by
  rintro ⟨domain, hdomain⟩
  let support : Finset Name :=
    domain.biUnion (fun y =>
      match env.slotAt y with
      | some slot => (PartialTy.allVars slot.ty).toFinset
      | none => ∅)
  refine ⟨support, ?_⟩
  intro y slot x hslot hmem
  dsimp [support]
  exact Finset.mem_biUnion.mpr ⟨y, hdomain y slot hslot, by
    simp [hslot, hmem]⟩

/-- Finite store-typing domains mention only finitely many variable names in types. -/
theorem StoreTyping.FiniteSupport.typeNameSupport {typing : StoreTyping} :
    StoreTyping.FiniteSupport typing →
    ∃ support : Finset Name,
      ∀ location ty x,
        typing.tyOf location = some ty →
        x ∈ Ty.allVars ty →
        x ∈ support := by
  rintro ⟨domain, hdomain⟩
  let support : Finset Name :=
    domain.biUnion (fun location =>
      match typing.tyOf location with
      | some ty => (Ty.allVars ty).toFinset
      | none => ∅)
  refine ⟨support, ?_⟩
  intro location ty x hlookup hmem
  dsimp [support]
  exact Finset.mem_biUnion.mpr ⟨location, hdomain location ty hlookup, by
    simp [hlookup, hmem]⟩

/--
Finite environment/store typing support gives a genuinely fresh equality ghost.

The chosen name is fresh as an environment slot, absent from all names stored in
environment/store types, absent from the left type, and absent from the right
operand syntax.
-/
theorem exists_fresh_eq_ghost {env : Env} {typing : StoreTyping}
    {lhsTy : Ty} {rhs : Term} :
    Env.FiniteSupport env →
    StoreTyping.FiniteSupport typing →
    ∃ ghost,
      env.fresh ghost ∧
      Env.TypeNameFresh env ghost ∧
      ghost ∉ Ty.allVars lhsTy ∧
      StoreTyping.TypeNameFresh typing ghost ∧
      ¬ Term.Mentions ghost rhs := by
  rintro ⟨envDomain, henvDomain⟩ ⟨typingDomain, htypingDomain⟩
  let envTypeNames : Finset Name :=
    envDomain.biUnion (fun y =>
      match env.slotAt y with
      | some slot => (PartialTy.allVars slot.ty).toFinset
      | none => ∅)
  let storeTypeNames : Finset Name :=
    typingDomain.biUnion (fun location =>
      match typing.tyOf location with
      | some ty => (Ty.allVars ty).toFinset
      | none => ∅)
  let forbidden : Finset Name :=
    envDomain ∪ envTypeNames ∪ storeTypeNames ∪
      (Ty.allVars lhsTy).toFinset ∪ Term.names rhs
  rcases Finset.exists_notMem forbidden with ⟨ghost, hghost⟩
  have hnotEnvDomain : ghost ∉ envDomain := by
    intro hmem
    exact hghost (by simp [forbidden, hmem])
  have hnotEnvTypeNames : ghost ∉ envTypeNames := by
    intro hmem
    exact hghost (by simp [forbidden, hmem])
  have hnotStoreTypeNames : ghost ∉ storeTypeNames := by
    intro hmem
    exact hghost (by simp [forbidden, hmem])
  have hnotLhsVarsFinset : ghost ∉ (Ty.allVars lhsTy).toFinset := by
    intro hmem
    exact hghost (by simp [forbidden, hmem])
  have hnotRhsNames : ghost ∉ Term.names rhs := by
    intro hmem
    exact hghost (by simp [forbidden, hmem])
  have henvFresh : env.fresh ghost := by
    unfold Env.fresh
    cases hslot : env.slotAt ghost with
    | none => rfl
    | some slot =>
        exact False.elim (hnotEnvDomain (henvDomain ghost slot hslot))
  have henvTypeFresh : Env.TypeNameFresh env ghost := by
    intro y slot hslot hmem
    exact hnotEnvTypeNames (by
      dsimp [envTypeNames]
      exact Finset.mem_biUnion.mpr ⟨y, henvDomain y slot hslot, by
        simp [hslot, hmem]⟩)
  have hnotLhsVars : ghost ∉ Ty.allVars lhsTy := by
    intro hmem
    exact hnotLhsVarsFinset (List.mem_toFinset.mpr hmem)
  have hstoreTypeFresh : StoreTyping.TypeNameFresh typing ghost := by
    intro location ty hlookup hmem
    exact hnotStoreTypeNames (by
      dsimp [storeTypeNames]
      exact Finset.mem_biUnion.mpr
        ⟨location, htypingDomain location ty hlookup, by
          simp [hlookup, hmem]⟩)
  exact ⟨ghost, henvFresh, henvTypeFresh, hnotLhsVars, hstoreTypeFresh,
    Term.not_mentions_of_not_mem_names hnotRhsNames⟩

/-- A fixed rank function witnessing linearizability of an environment. -/
def LinearizedBy (φ : Name → Nat) (env : Env) : Prop :=
  ∀ x slot, env.slotAt x = some slot →
    ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x

/--
Definition 11 of `lw_rust_followup`, Linearizable typing.

An environment is linearizable when there is a rank function `φ` on variables
such that every variable strictly outranks all live borrow-target variables
occurring in its slot type.  This forbids cyclic borrow references and is the
well-foundedness condition that makes the `LValTyping` recursion terminate.
-/
def Linearizable (env : Env) : Prop :=
  ∃ φ : Name → Nat, LinearizedBy φ env

/-- Structural shape equality of full types, ignoring borrow *target lists* but
keeping the `mutable` flag. -/
def Ty.sameShape : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .bool, .bool => True
  | .borrow m₁ _, .borrow m₂ _ => m₁ = m₂
  | .box t₁, .box t₂ => Ty.sameShape t₁ t₂
  | _, _ => False

/-- Structural shape equality of partial types. -/
def PartialTy.sameShape : PartialTy → PartialTy → Prop
  | .ty t₁, .ty t₂ => Ty.sameShape t₁ t₂
  | .box p₁, .box p₂ => PartialTy.sameShape p₁ p₂
  | .undef t₁, .undef t₂ => Ty.sameShape t₁ t₂
  | _, _ => False

/-- Finer type equivalence than `sameShape`: structural, and borrow target
lists must be subset-equivalent (same set). -/
def Ty.eqv : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .bool, .bool => True
  | .borrow m₁ t₁, .borrow m₂ t₂ =>
      m₁ = m₂ ∧ t₁ ⊆ t₂ ∧ t₂ ⊆ t₁
  | .box t₁, .box t₂ => Ty.eqv t₁ t₂
  | _, _ => False

/-- Partial-type version of `Ty.eqv`. -/
def PartialTy.eqv : PartialTy → PartialTy → Prop
  | .ty t₁, .ty t₂ => Ty.eqv t₁ t₂
  | .box p₁, .box p₂ => PartialTy.eqv p₁ p₂
  | .undef t₁, .undef t₂ => Ty.eqv t₁ t₂
  | _, _ => False

/-- Definition 3.14, path conflict `u ⋈ w`. -/
def PathConflicts (left right : LVal) : Prop :=
  LVal.base left = LVal.base right

infix:50 " ⋈ " => PathConflicts

notation:max "&mut " targets:max => Ty.borrow true targets
notation:max "&" targets:max => Ty.borrow false targets

/-- Definition 3.15, type containment inside a variable slot. -/
inductive PartialTyContains : PartialTy → Ty → Prop where
  | here {ty : Ty} :
      PartialTyContains (.ty ty) ty
  | tyBox {inner needle : Ty} :
      PartialTyContains (.ty inner) needle →
      PartialTyContains (.ty (.box inner)) needle
  | box {inner : PartialTy} {needle : Ty} :
      PartialTyContains inner needle →
      PartialTyContains (.box inner) needle

theorem PartialTyContains.borrow_target_mem_allVars
    {partialTy : PartialTy} {mutable : Bool} {targets : List LVal}
    {target : LVal} :
    PartialTyContains partialTy (.borrow mutable targets) →
    target ∈ targets →
    LVal.base target ∈ PartialTy.allVars partialTy := by
  intro hcontains htarget
  suffices hgeneral :
      ∀ {partialTy : PartialTy} {needle : Ty},
        PartialTyContains partialTy needle →
        ∀ {mutable : Bool} {targets : List LVal} {target : LVal},
          needle = .borrow mutable targets →
          target ∈ targets →
          LVal.base target ∈ PartialTy.allVars partialTy by
    exact hgeneral hcontains rfl htarget
  intro partialTy needle hcontains
  induction hcontains with
  | here =>
      intro mutable targets target hneedle htarget
      subst hneedle
      simp [PartialTy.allVars, Ty.allVars, List.mem_map]
      exact ⟨target, htarget, rfl⟩
  | tyBox _hinner ih =>
      intro mutable targets target hneedle htarget
      simpa [PartialTy.allVars, Ty.allVars] using
        ih hneedle htarget
  | box _hinner ih =>
      intro mutable targets target hneedle htarget
      simpa [PartialTy.allVars] using ih hneedle htarget

def EnvContains (env : Env) (x : Name) (ty : Ty) : Prop :=
  ∃ slot, env.slotAt x = some slot ∧ PartialTyContains slot.ty ty

notation:50 env:51 " ⊢ " x:51 " ↝ " ty:51 => EnvContains env x ty

/--
Coherence obligations for adding a fresh full-typed slot.

This is deliberately carried by the declaration/result rules rather than
derived from `WellFormedTy`: a declared borrow type must be lvalue-coherent,
meaning its target list is jointly typeable.
-/
structure FreshUpdateCoherenceObligations
    (env : Env) (x : Name) (ty : Ty) (lifetime : Lifetime) : Prop where
  old_root_transport
    {lv : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime : Lifetime} :
    LVal.base lv ≠ x →
    LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
      lv (.ty (.borrow mutable targets)) borrowLifetime →
    ∃ oldBorrowLifetime,
      LValTyping env lv (.ty (.borrow mutable targets)) oldBorrowLifetime
  fresh_root_coherent
    {lv : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime : Lifetime} :
    LVal.base lv = x →
    LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
      lv (.ty (.borrow mutable targets)) borrowLifetime →
    ∃ targetTy targetLifetime,
      LValTargetsTyping
        (env.update x { ty := .ty ty, lifetime := lifetime })
        targets (.ty targetTy) targetLifetime

/--
Rank obligation for assignment writes.

Every borrow edge installed from the RHS type must point to a lower-ranked base
in the pre-write environment.
-/
def EnvWriteRhsBorrowTargetsBelow (φ : Name → Nat) (result : Env) (rhsTy : Ty) : Prop :=
  ∀ x slot mutable targets target,
      result.slotAt x = some slot →
      PartialTyContains slot.ty (.borrow mutable targets) →
      target ∈ targets →
      (∃ rhsMutable rhsTargets,
        PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets) ∧
          target ∈ rhsTargets) →
      φ (LVal.base target) < φ x

/-- Definition 3.16, `readProhibited(Γ, w)`. -/
def ReadProhibited (env : Env) (lv : LVal) : Prop :=
  ∃ x targets target,
    env ⊢ x ↝ (.borrow true targets) ∧
    target ∈ targets ∧
    target ⋈ lv

/-- Definition 3.17, `writeProhibited(Γ, w)`. -/
def WriteProhibited (env : Env) (lv : LVal) : Prop :=
  ReadProhibited env lv ∨
  ∃ x targets target,
    env ⊢ x ↝ (.borrow false targets) ∧
    target ∈ targets ∧
    target ⋈ lv

def Strike : Path → PartialTy → PartialTy → Prop
  | [], .ty sourceTy, .undef targetTy => sourceTy = targetTy
  | _ :: path, .box inner, .box struck => Strike path inner struck
  | _ :: path, .ty (.box inner), .box struck => Strike path (.ty inner) struck
  | _, _, _ => False

/-- Definition 3.18, `move(Γ, w)`. -/
def EnvMove (env : Env) (lv : LVal) (moved : Env) : Prop :=
  ∃ slot struck,
    env.slotAt (LVal.base lv) = some slot ∧
    Strike (LVal.path lv) slot.ty struck ∧
    moved = env.update (LVal.base lv) { slot with ty := struck }

theorem EnvMove.finiteSupport {env moved : Env} {lv : LVal} :
    EnvMove env lv moved →
    Env.FiniteSupport env →
    Env.FiniteSupport moved := by
  rintro ⟨slot, struck, _hslot, _hstrike, hmoved⟩ hfinite
  subst hmoved
  exact hfinite.update

/-- Definition 3.19, `mut(Γ, w)`. -/
inductive Mutable : Env → LVal → Prop where
  | var {env : Env} {x : Name} {slot : EnvSlot} :
      env.slotAt x = some slot →
      Mutable env (.var x)
  | box {env : Env} {lv : LVal} {inner : PartialTy} {lifetime : Lifetime} :
      LValTyping env lv (.box inner) lifetime →
      Mutable env lv →
      Mutable env (.deref lv)
  | boxFull {env : Env} {lv : LVal} {inner : Ty} {lifetime : Lifetime} :
      LValTyping env lv (.ty (.box inner)) lifetime →
      Mutable env lv →
      Mutable env (.deref lv)
  | borrow {env : Env} {lv : LVal} {targets : List LVal} {lifetime : Lifetime} :
      LValTyping env lv (.ty (.borrow true targets)) lifetime →
      (∀ target, target ∈ targets → Mutable env target) →
      Mutable env (.deref lv)

namespace Env

/-- Definition 3.20, environment drop `drop(Γ, m)`. -/
def dropLifetime (env : Env) (lifetime : Lifetime) : Env :=
  { slotAt := fun x =>
      match env.slotAt x with
      | some slot => if slot.lifetime = lifetime then none else some slot
      | none => none }

theorem FiniteSupport.dropLifetime {env : Env} {lifetime : Lifetime} :
    FiniteSupport env → FiniteSupport (env.dropLifetime lifetime) := by
  rintro ⟨support, hsupport⟩
  refine ⟨support, ?_⟩
  intro x slot hslot
  cases horig : env.slotAt x with
  | none =>
      change (match env.slotAt x with
        | some slot => if slot.lifetime = lifetime then none else some slot
        | none => none) = some slot at hslot
      rw [horig] at hslot
      cases hslot
  | some origSlot =>
      exact hsupport x origSlot horig

end Env

/-- The variable slot at the base of an lval survives for the requested lifetime. -/
def LValBaseOutlives (env : Env) (lv : LVal) (lifetime : Lifetime) : Prop :=
  ∃ slot, env.slotAt (LVal.base lv) = some slot ∧ slot.lifetime ≤ lifetime

/--
All borrow targets are well formed for the requested lifetime.

This is the borrow invariant of Definition 4.8(i), stated faithfully **per
target**: each individual target lval `w` is typable (`Γ ⊢ w : T^m`) with its
own target type `T` and lifetime `m ≼ l`, plus the mechanisation's slot-survival
component used by drop/update preservation.

Note the deliberate separation from Definition 3.21 (`WellFormedTy`, the
well-formed *type* judgement): the paper's `L-Borrow` premise `Γ ⊢ u : ⟨T⟩^m`
types the whole target set *jointly* (one shared target type `T`).  That joint
typing is what the typing rules establish when a borrow is **created** (T-LvBor
produces an `LValTargetsTyping`).  The well-formedness invariant that must be
**preserved** through execution, however, is only the per-target statement of
Definition 4.8(i).  Conflating the two — carrying the joint typing as the runtime
invariant — is unsound at environment joins: rule W-Bor merges the target lists
of two borrows (`&u₁ ⊔ &u₂ = &(u₁ ⊔ u₂)`) without requiring their target types
to join, so the merged list has no joint typing in general, yet each target
retains its own per-target typing.  Keeping this predicate per-target is exactly
what makes borrow invariance provable across joins. -/
inductive BorrowTargetsWellFormed : Env → List LVal → Lifetime → Prop where
  | intro {env : Env} {targets : List LVal} {lifetime : Lifetime} :
      (∀ target, target ∈ targets →
        ∃ targetTy targetLifetime,
          LValTyping env target (.ty targetTy) targetLifetime ∧
          LifetimeOutlives targetLifetime lifetime ∧
          LValBaseOutlives env target lifetime) →
      BorrowTargetsWellFormed env targets lifetime

/--
Definition 4.8(i), the borrow invariant, stated per target for borrows contained
in one slot.
-/
def BorrowTargetsWellFormedInSlot
    (env : Env) (slotLifetime : Lifetime) (targets : List LVal) : Prop :=
  ∀ target, target ∈ targets →
    ∃ targetTy targetLifetime,
      LValTyping env target (.ty targetTy) targetLifetime ∧
        targetLifetime ≤ slotLifetime ∧
        LValBaseOutlives env target slotLifetime

/--
Weaker borrow-target invariant for stale loan annotations.

A target list carried by a type can be a conservative protection token after a
path-insensitive join: the annotation still blocks writes through
`ReadProhibited`/`WriteProhibited`, but a moved-out target is not currently
dereferenceable.  The target's base slot must still survive for the containing
loan, but the full target typing needed to dereference the borrow is conditional
on the target being initialized.
-/
def BorrowTargetsWellFormedWhenInitialized
    (env : Env) (targets : List LVal) (lifetime : Lifetime) : Prop :=
  ∀ target, target ∈ targets →
    LValBaseOutlives env target lifetime ∧
      ((∃ targetTy targetLifetime,
        LValTyping env target (.ty targetTy) targetLifetime) →
      ∃ targetTy targetLifetime,
        LValTyping env target (.ty targetTy) targetLifetime ∧
          targetLifetime ≤ lifetime ∧
          LValBaseOutlives env target lifetime)

/-- Slot-local version of `BorrowTargetsWellFormedWhenInitialized`. -/
def BorrowTargetsWellFormedInSlotWhenInitialized
    (env : Env) (slotLifetime : Lifetime) (targets : List LVal) : Prop :=
  BorrowTargetsWellFormedWhenInitialized env targets slotLifetime

/-- Slot-local borrow invariant for a partial type. -/
def PartialTyBorrowsWellFormedInSlot
    (env : Env) (slotLifetime : Lifetime) (partialTy : PartialTy) : Prop :=
  ∀ {mutable targets},
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormedInSlot env slotLifetime targets

/-- Slot-local weak borrow invariant for a partial type. -/
def PartialTyBorrowsWellFormedInSlotWhenInitialized
    (env : Env) (slotLifetime : Lifetime) (partialTy : PartialTy) : Prop :=
  ∀ {mutable targets},
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormedInSlotWhenInitialized env slotLifetime targets

/-- Weak borrow invariant for a full type. -/
def TyBorrowsWellFormedWhenInitialized
    (env : Env) (ty : Ty) (lifetime : Lifetime) : Prop :=
  ∀ {mutable targets},
    PartialTyContains (.ty ty) (.borrow mutable targets) →
    BorrowTargetsWellFormedWhenInitialized env targets lifetime

/--
Minimal lifetime obligation for assignment writes.

This is the strictly-weaker replacement for carrying the broad
`ContainedBorrowsWellFormed` of the write result on `T-Assign`: only the borrow
edges *installed from the RHS type* must be well formed against the slot they are
injected into.  Each RHS-origin borrow target appearing in a result slot must
outlive *that slot* (its target typeable with a lifetime `≤` the slot lifetime,
plus the base-slot survival of Definition 4.8(i)).

This is exactly what the broad result CBWF demands of the RHS-origin borrows; the
old-origin borrows are *derived* from `ContainedBorrowsWellFormed` of the
pre-write environment via the borrow-invariance keystone.  It is genuinely needed
(and not derivable from `WellFormedTy env₂ rhsTy targetLifetime`): a write through
a multi-target borrow `&mut[x,z]` whose targets have different lifetimes fans the
RHS into both slots, but `targetLifetime` is only the *intersection* of the
targets' lifetimes, so it cannot bound the RHS by the longer-lived slot's
lifetime — see the deviation note in the README and the `example` below the rule.
This mirrors `EnvWriteRhsBorrowTargetsBelow`, with a lifetime
conclusion in place of the rank one. -/
def EnvWriteRhsTargetsWellFormed (result : Env) (rhsTy : Ty) : Prop :=
  ∀ x slot mutable targets target,
    result.slotAt x = some slot →
    PartialTyContains slot.ty (.borrow mutable targets) →
    target ∈ targets →
    (∃ rhsMutable rhsTargets,
      PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets) ∧
        target ∈ rhsTargets) →
    ∃ targetTy targetLifetime,
      LValTyping result target (.ty targetTy) targetLifetime ∧
        targetLifetime ≤ slot.lifetime ∧
        LValBaseOutlives result target slot.lifetime

/-- Every borrow contained in every environment slot has well-formed targets. -/
def ContainedBorrowsWellFormed (env : Env) : Prop :=
  ∀ x slot mutable targets,
    env.slotAt x = some slot →
    env ⊢ x ↝ (Ty.borrow mutable targets) →
    BorrowTargetsWellFormedInSlot env slot.lifetime targets

/--
Every borrow contained in every environment slot has well-formed targets when
those targets are currently initialized.
-/
def ContainedBorrowsWellFormedWhenInitialized (env : Env) : Prop :=
  ∀ x slot mutable targets,
    env.slotAt x = some slot →
    env ⊢ x ↝ (Ty.borrow mutable targets) →
    BorrowTargetsWellFormedInSlotWhenInitialized env slot.lifetime targets

/-- The minimal RHS-target obligation is (much) weaker than the broad result
CBWF: any environment that is fully `ContainedBorrowsWellFormed` satisfies it for
every `rhsTy`.  Used to discharge the obligation in examples that already prove
the stronger fact. -/
theorem EnvWriteRhsTargetsWellFormed.of_containedBorrowsWellFormed
    {result : Env} {rhsTy : Ty} :
    ContainedBorrowsWellFormed result → EnvWriteRhsTargetsWellFormed result rhsTy := by
  intro hcbwf x slot mutable targets target hslot hcontains htarget _hrhs
  exact (hcbwf x slot mutable targets hslot ⟨slot, hslot, hcontains⟩) target htarget

/-- Definition 4.8(ii). Every environment slot lives at least as long as `lifetime`. -/
def EnvSlotsOutlive (env : Env) (lifetime : Lifetime) : Prop :=
  ∀ x slot,
    env.slotAt x = some slot →
    slot.lifetime ≤ lifetime

/--
Coherence of contained borrows: every borrow-typed lvalue has jointly typeable
targets, which is what `T-LvBor` needs for reborrows.
-/
def Coherent (env : Env) : Prop :=
  ∀ lv mutable targets borrowLifetime,
    LValTyping env lv (.ty (.borrow mutable targets)) borrowLifetime →
    ∃ partialTy lifetime, LValTargetsMaybeTyping env targets partialTy lifetime

/-- A target list whose every target is currently initialized. -/
def BorrowTargetsInitialized (env : Env) (targets : List LVal) : Prop :=
  ∀ target, target ∈ targets →
    ∃ targetTy targetLifetime,
      LValTyping env target (.ty targetTy) targetLifetime

/--
Weaker coherence for stale loan annotations: a borrow-typed lvalue must have
jointly typeable targets only when all of those targets are currently
initialized.  If some target has been moved out, the borrow annotation remains a
protection token but cannot be dereferenced through `T-LvBor`.
-/
def CoherentWhenInitialized (env : Env) : Prop :=
  ∀ lv mutable targets borrowLifetime,
    LValTyping env lv (.ty (.borrow mutable targets)) borrowLifetime →
    BorrowTargetsInitialized env targets →
    ∃ partialTy lifetime, LValTargetsMaybeTyping env targets partialTy lifetime

theorem Linearizable.of_linearizedBy {φ : Name → Nat} {env : Env} :
    LinearizedBy φ env → Linearizable env := by
  intro hφ
  exact ⟨φ, hφ⟩

/--
Weaker environment invariant that permits stale loan annotations while keeping
their base slots live as conservative protection tokens.
-/
def WellFormedEnvWhenInitialized (env : Env) (lifetime : Lifetime) : Prop :=
  ContainedBorrowsWellFormedWhenInitialized env ∧
    EnvSlotsOutlive env lifetime ∧
    CoherentWhenInitialized env ∧ Linearizable env

/-- Definition 4.8, well-formed environment, with the maintained invariants. -/
def WellFormedEnv (env : Env) (lifetime : Lifetime) : Prop :=
  ContainedBorrowsWellFormed env ∧ EnvSlotsOutlive env lifetime ∧
    Coherent env ∧ Linearizable env

/--
Definition 4.13, borrow-safe environment.

The paper phrases this over variables in `dom(Γ)` and borrowed lvalues inside
contained borrow types.  The containment premises already imply the relevant
variables are present in the environment.

This lives here (rather than with the Section 4.3 helpers) because assignment
and preservation helpers need the predicate near the typing relation.  It is
not required by the relaxed `T-If` join: joined environments may be static
approximations that are not globally borrow-safe.
-/
def BorrowSafeEnv (env : Env) : Prop :=
  ∀ x y mutable targetsMutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ (.borrow true targetsMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    x = y

/-- A result type is borrow-safe against an environment when installing it as a
new root would introduce no borrow-target conflict with any existing root. -/
def TyBorrowSafeAgainstEnv (env : Env) (ty : Ty) : Prop :=
  (∀ targetsMutable mutable targetsOther x targetMutable targetOther,
    PartialTyContains (.ty ty) (.borrow true targetsMutable) →
    env ⊢ x ↝ Ty.borrow mutable targetsOther →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False) ∧
  (∀ x targetsMutable mutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ Ty.borrow true targetsMutable →
    PartialTyContains (.ty ty) (.borrow mutable targetsOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False)

/-- A type that contains no borrow type anywhere. -/
def TyBorrowFree (ty : Ty) : Prop :=
  ∀ mutable targets, ¬ PartialTyContains (.ty ty) (.borrow mutable targets)

def PartialTyBorrowFree (ty : PartialTy) : Prop :=
  ∀ mutable targets, ¬ PartialTyContains ty (.borrow mutable targets)

/-- A type whose contained borrows claim no loans.  With empty target lists
disallowed, this is exactly borrow-freedom. -/
def TyLoanFree (ty : Ty) : Prop :=
  TyBorrowFree ty

def PartialTyLoanFree (ty : PartialTy) : Prop :=
  PartialTyBorrowFree ty

def EnvJoinSameShape (branch join : Env) : Prop :=
  ∀ x branchSlot joinSlot,
    branch.slotAt x = some branchSlot →
    join.slotAt x = some joinSlot →
    PartialTy.sameShape branchSlot.ty joinSlot.ty

def LoopInvariantNameFresh (entry inv : Env) (condition body : Term) : Prop :=
  ∀ erased checked,
    Env.TypeNameFresh (entry.eraseMany erased) checked →
    ¬ Term.Mentions checked condition →
    ¬ Term.Mentions checked body →
    Env.TypeNameFresh (inv.eraseMany erased) checked

/-- A join is an upper bound of its left component. -/
theorem EnvJoin.left_le {left right join : Env} :
  EnvJoin left right join →
    EnvStrengthens left join := by
  intro hjoin
  exact hjoin.1 (by simp)

/-- A join is an upper bound of its right component. -/
theorem EnvJoin.right_le {left right join : Env} :
  EnvJoin left right join →
    EnvStrengthens right join := by
  intro hjoin
  exact hjoin.1 (by simp)

theorem EnvJoin.finiteSupport_left {left right join : Env} :
    EnvJoin left right join →
    Env.FiniteSupport left →
    Env.FiniteSupport join := by
  intro hjoin hfinite
  rcases hfinite with ⟨support, hsupport⟩
  refine ⟨support, ?_⟩
  intro x joinSlot hjoinSlot
  have hstrength := EnvJoin.left_le hjoin x
  cases hleft : left.slotAt x with
  | none =>
      rw [hleft, hjoinSlot] at hstrength
      exact False.elim hstrength
  | some leftSlot =>
      exact hsupport x leftSlot hleft

theorem EnvJoin.finiteSupport_right {left right join : Env} :
    EnvJoin left right join →
    Env.FiniteSupport right →
    Env.FiniteSupport join := by
  intro hjoin hfinite
  rcases hfinite with ⟨support, hsupport⟩
  refine ⟨support, ?_⟩
  intro x joinSlot hjoinSlot
  have hstrength := EnvJoin.right_le hjoin x
  cases hright : right.slotAt x with
  | none =>
      rw [hright, hjoinSlot] at hstrength
      exact False.elim hstrength
  | some rightSlot =>
      exact hsupport x rightSlot hright

/-- `EnvStrengthens` componentwise view: slots of the weaker environment are
matched by slots of the stronger one with equal lifetimes. -/
theorem EnvStrengthens.slot_forward {left right : Env} {x : Name}
    {leftSlot : EnvSlot} :
    EnvStrengthens left right →
    left.slotAt x = some leftSlot →
    ∃ rightSlot,
      right.slotAt x = some rightSlot ∧
      leftSlot.lifetime = rightSlot.lifetime ∧
      PartialTyStrengthens leftSlot.ty rightSlot.ty := by
  intro hstrengthens hleft
  have h := hstrengthens x
  rw [hleft] at h
  cases hright : right.slotAt x with
  | none =>
      rw [hright] at h
      exact False.elim h
  | some rightSlot =>
      rw [hright] at h
      exact ⟨rightSlot, rfl, h.1, h.2⟩

/-- Definition 3.21, well-formed type `Γ ⊢ T ≽ l`. -/
inductive WellFormedTy : Env → Ty → Lifetime → Prop where
  /-- L-Unit, the unit case implicit in the paper's use of `ϵ`. -/
  | unit {env : Env} {lifetime : Lifetime} :
      WellFormedTy env .unit lifetime
  /-- L-Int. -/
  | int {env : Env} {lifetime : Lifetime} :
      WellFormedTy env .int lifetime
  /-- L-Bool, Section 6.1. -/
  | bool {env : Env} {lifetime : Lifetime} :
      WellFormedTy env .bool lifetime
  /-- L-Borrow. -/
  | borrow {env : Env} {mutable : Bool} {targets : List LVal}
      {lifetime : Lifetime} :
      BorrowTargetsWellFormed env targets lifetime →
      WellFormedTy env (.borrow mutable targets) lifetime
  /-- L-Box. -/
  | box {env : Env} {ty : Ty} {lifetime : Lifetime} :
      WellFormedTy env ty lifetime →
      WellFormedTy env (.box ty) lifetime

/--
Weak type well-formedness for stale loan annotations.

This mirrors `WellFormedTy`, but borrow targets only need to be well formed
when initialized.  A type may therefore carry a conservative borrow target list
whose base slot is still live but whose full lvalue is currently moved out.
-/
inductive WellFormedTyWhenInitialized : Env → Ty → Lifetime → Prop where
  | unit {env : Env} {lifetime : Lifetime} :
      WellFormedTyWhenInitialized env .unit lifetime
  | int {env : Env} {lifetime : Lifetime} :
      WellFormedTyWhenInitialized env .int lifetime
  | bool {env : Env} {lifetime : Lifetime} :
      WellFormedTyWhenInitialized env .bool lifetime
  | borrow {env : Env} {mutable : Bool} {targets : List LVal}
      {lifetime : Lifetime} :
      BorrowTargetsWellFormedWhenInitialized env targets lifetime →
      WellFormedTyWhenInitialized env (.borrow mutable targets) lifetime
  | box {env : Env} {ty : Ty} {lifetime : Lifetime} :
      WellFormedTyWhenInitialized env ty lifetime →
      WellFormedTyWhenInitialized env (.box ty) lifetime

/-- Definition 3.22, compatible shape `Γ ⊢ T̃₁ ≈ T̃₂`. -/
inductive ShapeCompatible : Env → PartialTy → PartialTy → Prop where
  /-- S-Unit, the unit case implicit in the paper's statement type. -/
  | unit {env : Env} :
      ShapeCompatible env (.ty .unit) (.ty .unit)
  /-- S-Int. -/
  | int {env : Env} :
      ShapeCompatible env (.ty .int) (.ty .int)
  /-- S-Bool, Section 6.1. -/
  | bool {env : Env} :
      ShapeCompatible env (.ty .bool) (.ty .bool)
  /-- S-Box for fully initialized owner types. -/
  | tyBox {env : Env} {left right : Ty} :
      ShapeCompatible env (.ty left) (.ty right) →
      ShapeCompatible env (.ty (.box left)) (.ty (.box right))
  /-- S-Box. -/
  | box {env : Env} {left right : PartialTy} :
      ShapeCompatible env left right →
      ShapeCompatible env (.box left) (.box right)
  /-- S-Bor.  Borrow shapes are compatible when their target-list output types
  are shape-compatible in the current environment. -/
  | borrow {env : Env} {mutable : Bool} {leftTargets rightTargets : List LVal}
      {leftTy rightTy : Ty} :
      (∀ leftTarget, leftTarget ∈ leftTargets →
        ∃ leftLifetime, LValTyping env leftTarget (.ty leftTy) leftLifetime) →
      (∀ rightTarget, rightTarget ∈ rightTargets →
        ∃ rightLifetime, LValTyping env rightTarget (.ty rightTy) rightLifetime) →
      ShapeCompatible env (.ty leftTy) (.ty rightTy) →
      ShapeCompatible env (.ty (.borrow mutable leftTargets))
        (.ty (.borrow mutable rightTargets))
  /-- S-UndefL. -/
  | undefLeft {env : Env} {left : Ty} {right : PartialTy} :
      ShapeCompatible env (.ty left) right →
      ShapeCompatible env (.undef left) right
  /-- S-UndefR. -/
  | undefRight {env : Env} {left : PartialTy} {right : Ty} :
      ShapeCompatible env left (.ty right) →
      ShapeCompatible env left (.undef right)

/-- Path composition used by Definition 3.23's borrow case. -/
def prependPath : List Unit → LVal → LVal
  | [], lv => lv
  | _ :: path, lv => .deref (prependPath path lv)

theorem List.Unit_append_singleton_typing :
    ∀ (path : List Unit), path ++ [()] = () :: path
  | [] => rfl
  | () :: path => by
      rw [List.cons_append, List.Unit_append_singleton_typing path]

@[simp] theorem LVal.base_prependPath (path : List Unit) (target : LVal) :
    LVal.base (prependPath path target) = LVal.base target := by
  induction path with
  | nil => rfl
  | cons _ tail ih => simp [prependPath, LVal.base, ih]

@[simp] theorem LVal.path_prependPath (path : List Unit) (target : LVal) :
    LVal.path (prependPath path target) = LVal.path target ++ path := by
  induction path with
  | nil => simp [prependPath]
  | cons _ tail ih =>
      simp only [prependPath, LVal.path, ih, List.append_assoc,
        List.Unit_append_singleton_typing]

/--
Static approximation of lvalue-resolution dependencies.

`EnvMayReadThrough env written target` means that resolving `target` may inspect
the location denoted by `written` before reaching `target`'s final location.
The direct case is the ordinary same-base strict-prefix dependency.  The borrow
case accounts for aliases introduced by borrow targets: after one dereference
of `source`, resolution may continue from any statically listed target.
-/
inductive EnvMayReadThrough (env : Env) (written : LVal) : LVal → Prop where
  | direct {target : LVal} :
      LVal.StrictPrefixOf written target →
      EnvMayReadThrough env written target
  | borrow {source selected : LVal} {suffix : List Unit}
      {mutable : Bool} {targets : List LVal} {lifetime : Lifetime} :
      LValTyping env source (.ty (.borrow mutable targets)) lifetime →
      selected ∈ targets →
      EnvMayReadThrough env written (prependPath suffix selected) →
      EnvMayReadThrough env written (prependPath (() :: suffix) source)

theorem EnvMayReadThrough.borrowTarget_deref_deref {env : Env}
    {written source : LVal} {mutable : Bool} {targets : List LVal}
    {lifetime : Lifetime} :
    LValTyping env source (.ty (.borrow mutable targets)) lifetime →
    written ∈ targets →
    EnvMayReadThrough env written (.deref (.deref source)) := by
  intro htyping hmem
  exact EnvMayReadThrough.borrow (suffix := [()]) htyping hmem
    (EnvMayReadThrough.direct (LVal.StrictPrefixOf.self_deref written))

theorem EnvMayReadThrough.deref_right {env : Env} {written target : LVal} :
    EnvMayReadThrough env written target →
    EnvMayReadThrough env written (.deref target) := by
  intro hread
  induction hread with
  | direct hprefix =>
      exact EnvMayReadThrough.direct
        (LVal.StrictPrefixOf.deref_right hprefix)
  | @borrow source selected suffix mutable targets lifetime htyping hmem _ ih =>
      simpa [prependPath] using
        EnvMayReadThrough.borrow (source := source) (selected := selected)
          (suffix := () :: suffix) htyping hmem ih

theorem EnvMayReadThrough.prependPath_right {env : Env} {written target : LVal} :
    ∀ suffix : List Unit,
      EnvMayReadThrough env written target →
      EnvMayReadThrough env written (prependPath suffix target)
  | [], hread => hread
  | _ :: suffix, hread =>
      EnvMayReadThrough.deref_right
        (EnvMayReadThrough.prependPath_right suffix hread)

theorem EnvMayReadThrough.direct_prependPath_self_deref {env : Env}
    {written : LVal} :
    ∀ suffix : List Unit,
      EnvMayReadThrough env written (prependPath (() :: suffix) written)
  | [] =>
      EnvMayReadThrough.direct (LVal.StrictPrefixOf.self_deref written)
  | _ :: suffix =>
      EnvMayReadThrough.deref_right
        (EnvMayReadThrough.direct_prependPath_self_deref suffix)

theorem EnvMayReadThrough.borrowTarget_deref_prepend {env : Env}
    {written source : LVal} {mutable : Bool} {targets : List LVal}
    {lifetime : Lifetime} :
    LValTyping env source (.ty (.borrow mutable targets)) lifetime →
    written ∈ targets →
    ∀ suffix : List Unit,
      EnvMayReadThrough env written
        (prependPath (() :: (() :: suffix)) source) := by
  intro htyping hmem suffix
  exact EnvMayReadThrough.borrow (suffix := () :: suffix) htyping hmem
    (EnvMayReadThrough.direct_prependPath_self_deref suffix)

theorem EnvMayReadThrough.borrow_deref_step {env : Env}
    {written source selected : LVal} {mutable : Bool} {targets : List LVal}
    {lifetime : Lifetime} :
    LValTyping env source (.ty (.borrow mutable targets)) lifetime →
    selected ∈ targets →
    EnvMayReadThrough env written (.deref selected) →
    EnvMayReadThrough env written (.deref (.deref source)) := by
  intro htyping hmem hread
  exact EnvMayReadThrough.borrow (suffix := [()]) htyping hmem hread

theorem LVal.StrictPrefixOf.eq_prependPath
    {pref target : LVal} :
    LVal.StrictPrefixOf pref target →
    ∃ suffix : Path, suffix ≠ [] ∧ target = prependPath suffix pref := by
  intro hprefix
  rcases hprefix with ⟨hbase, hpath⟩
  rcases StrictPathPrefix.exists_suffix hpath with
    ⟨suffix, hnonempty, hpathEq⟩
  refine ⟨suffix, hnonempty, ?_⟩
  apply LVal.eq_of_base_path
  · simpa [LVal.base_prependPath] using hbase.symm
  · simpa [LVal.path_prependPath, hpathEq]

theorem EnvMayReadThrough.strictPrefix_right {env : Env}
    {written middle target : LVal} :
    EnvMayReadThrough env written middle →
    LVal.StrictPrefixOf middle target →
    EnvMayReadThrough env written target := by
  intro hread hprefix
  rcases LVal.StrictPrefixOf.eq_prependPath hprefix with
    ⟨suffix, _hnonempty, htarget⟩
  rw [htarget]
  exact EnvMayReadThrough.prependPath_right suffix hread

theorem EnvMayReadThrough.trans {env : Env}
    {written middle target : LVal} :
    EnvMayReadThrough env written middle →
    EnvMayReadThrough env middle target →
    EnvMayReadThrough env written target := by
  intro hleft hright
  induction hright generalizing written with
  | direct hprefix =>
      exact EnvMayReadThrough.strictPrefix_right hleft hprefix
  | @borrow source selected suffix mutable targets lifetime htyping hmem
      _hinner ih =>
      exact EnvMayReadThrough.borrow htyping hmem (ih hleft)

/-- Re-wrap an updated box element, preserving full-box shape when possible. -/
def partialTyRebox : PartialTy → PartialTy
  | .ty inner => .ty (.box inner)
  | inner => .box inner

mutual
  /-- Definition 3.23, `update_k(Γ, π | T̃, T)`. -/
  inductive UpdateAtPath : Nat → Env → List Unit → PartialTy → Ty → Env → PartialTy → Prop where
    | strong {env : Env} {old : PartialTy} {ty : Ty} :
        UpdateAtPath 0 env [] old ty env (.ty ty)
    | weak {env : Env} {rank : Nat} {old joined : PartialTy} {ty : Ty} :
        ShapeCompatible env old (.ty ty) →
        PartialTyJoin old (.ty ty) joined →
        UpdateAtPath (rank + 1) env [] old ty env joined
    | box {env₁ env₂ : Env} {rank : Nat} {path : List Unit}
        {inner updatedInner : PartialTy} {ty : Ty} :
        UpdateAtPath rank env₁ path inner ty env₂ updatedInner →
        UpdateAtPath rank env₁ (() :: path) (.box inner) ty env₂ (.box updatedInner)
    | boxFull {env₁ env₂ : Env} {rank : Nat} {path : List Unit}
        {inner : Ty} {updatedInner : PartialTy} {ty : Ty} :
        UpdateAtPath rank env₁ path (.ty inner) ty env₂ updatedInner →
        UpdateAtPath rank env₁ (() :: path) (.ty (.box inner)) ty env₂
          (partialTyRebox updatedInner)
    | mutBorrow {env₁ env₂ : Env} {rank : Nat} {path : List Unit}
        {targets : List LVal} {ty : Ty} :
        WriteBorrowTargets (rank + 1) env₁ path targets ty env₂ →
        UpdateAtPath rank env₁ (() :: path) (.ty (.borrow true targets)) ty
          env₂ (.ty (.borrow true targets))

  /-- The joined environment from updating each possible target of a borrow.

  Documented strengthening for the mechanization: each non-empty branch carries
  a full typing for the concrete written lvalue `prependPath path target`.  The
  bare syntax of `EnvWrite` can reinitialize an `undef` leaf, which would make
  the two fan-out branches fail to have the same shape.  The assignment rule
  should only fan out through initialized borrowed targets; carrying this witness
  here makes that invariant explicit and lets Appendix 9.6 derive branch shape
  constructively instead of assuming it. -/
  inductive WriteBorrowTargets :
      Nat → Env → List Unit → List LVal → Ty → Env → Prop where
    | nil {rank : Nat} {env : Env} {path : List Unit} {ty : Ty} :
        WriteBorrowTargets rank env path [] ty env
    | singleton {rank : Nat} {env updated : Env} {path : List Unit}
        {target : LVal} {ty : Ty} :
        EnvWrite rank env (prependPath path target) ty updated →
        (∃ leafTy leafLifetime,
          LValTyping env (prependPath path target) (.ty leafTy) leafLifetime) →
        WriteBorrowTargets rank env path [target] ty updated
    | cons {rank : Nat} {env updated restEnv result : Env} {path : List Unit}
        {target : LVal} {rest : List LVal} {ty : Ty} :
        EnvWrite rank env (prependPath path target) ty updated →
        (∃ leafTy leafLifetime,
          LValTyping env (prependPath path target) (.ty leafTy) leafLifetime) →
        WriteBorrowTargets rank env path rest ty restEnv →
        EnvJoin updated restEnv result →
        WriteBorrowTargets rank env path (target :: rest) ty result

  /-- Definition 3.23, `write_k(Γ, w, T)`. -/
  inductive EnvWrite : Nat → Env → LVal → Ty → Env → Prop where
    | intro {rank : Nat} {env₁ env₂ : Env} {lv : LVal} {slot : EnvSlot}
        {ty : Ty} {updatedTy : PartialTy} :
        env₁.slotAt (LVal.base lv) = some slot →
        UpdateAtPath rank env₁ (LVal.path lv) slot.ty ty env₂ updatedTy →
        EnvWrite rank env₁ lv ty
          (env₂.update (LVal.base lv) { slot with ty := updatedTy })
end

mutual
  /--
  Effective lvalues overwritten by an `UpdateAtPath`.

  This mirrors `UpdateAtPath` but records the concrete static lvalue whose
  stored value is replaced after following box paths or mutable-borrow fan-out.
  In the mutable-borrow case the effective writes are the borrow targets, not
  the source borrow slot.
  -/
  inductive UpdateAtPathEffectiveWrite :
      Nat → Env → Name → List Unit → PartialTy → Ty → Env → PartialTy →
        LVal → Prop where
    | strong {env : Env} {base : Name} {old : PartialTy} {ty : Ty} :
        UpdateAtPathEffectiveWrite 0 env base [] old ty env (.ty ty)
          (.var base)
    | weak {env : Env} {base : Name} {rank : Nat}
        {old joined : PartialTy} {ty : Ty} :
        ShapeCompatible env old (.ty ty) →
        PartialTyJoin old (.ty ty) joined →
        UpdateAtPathEffectiveWrite (rank + 1) env base [] old ty env joined
          (.var base)
    | box {env₁ env₂ : Env} {base : Name} {rank : Nat}
        {path : List Unit} {inner updatedInner : PartialTy} {ty : Ty}
        {written : LVal} :
        UpdateAtPathEffectiveWrite rank env₁ base path inner ty env₂
          updatedInner written →
        UpdateAtPathEffectiveWrite rank env₁ base (() :: path) (.box inner) ty
          env₂ (.box updatedInner) (.deref written)
    | boxPassthrough {env₁ env₂ : Env} {base : Name} {rank : Nat}
        {path : List Unit} {inner updatedInner : PartialTy} {ty : Ty}
        {written : LVal} :
        UpdateAtPathEffectiveWrite rank env₁ base path inner ty env₂
          updatedInner written →
        UpdateAtPathEffectiveWrite rank env₁ base (() :: path) (.box inner) ty
          env₂ (.box updatedInner) written
    | boxFull {env₁ env₂ : Env} {base : Name} {rank : Nat}
        {path : List Unit} {inner : Ty} {updatedInner : PartialTy} {ty : Ty}
        {written : LVal} :
        UpdateAtPathEffectiveWrite rank env₁ base path (.ty inner) ty env₂
          updatedInner written →
        UpdateAtPathEffectiveWrite rank env₁ base (() :: path) (.ty (.box inner))
          ty env₂ (partialTyRebox updatedInner) (.deref written)
    | boxFullPassthrough {env₁ env₂ : Env} {base : Name} {rank : Nat}
        {path : List Unit} {inner : Ty} {updatedInner : PartialTy} {ty : Ty}
        {written : LVal} :
        UpdateAtPathEffectiveWrite rank env₁ base path (.ty inner) ty env₂
          updatedInner written →
        UpdateAtPathEffectiveWrite rank env₁ base (() :: path) (.ty (.box inner))
          ty env₂ (partialTyRebox updatedInner) written
    | mutBorrow {env₁ env₂ : Env} {base : Name} {rank : Nat}
        {path : List Unit} {targets : List LVal} {ty : Ty}
        {written : LVal} :
        WriteBorrowTargetsEffectiveWrite (rank + 1) env₁ path targets ty env₂
          written →
        UpdateAtPathEffectiveWrite rank env₁ base (() :: path)
          (.ty (.borrow true targets)) ty env₂
          (.ty (.borrow true targets)) written

  /-- Effective writes performed by a borrow-target fan-out. -/
  inductive WriteBorrowTargetsEffectiveWrite :
      Nat → Env → List Unit → List LVal → Ty → Env → LVal → Prop where
    | singleton {rank : Nat} {env updated : Env} {path : List Unit}
        {target : LVal} {ty : Ty} {written : LVal} :
        EnvWriteEffectiveWrite rank env (prependPath path target) ty updated
          written →
        WriteBorrowTargetsEffectiveWrite rank env path [target] ty updated
          written
    | consHead {rank : Nat} {env updated restEnv result : Env}
        {path : List Unit} {target : LVal} {rest : List LVal} {ty : Ty}
        {written : LVal} :
        EnvWriteEffectiveWrite rank env (prependPath path target) ty updated
          written →
        WriteBorrowTargets rank env path rest ty restEnv →
        EnvJoin updated restEnv result →
        WriteBorrowTargetsEffectiveWrite rank env path (target :: rest) ty
          result written
    | consTail {rank : Nat} {env updated restEnv result : Env}
        {path : List Unit} {target : LVal} {rest : List LVal} {ty : Ty}
        {written : LVal} :
        EnvWrite rank env (prependPath path target) ty updated →
        WriteBorrowTargetsEffectiveWrite rank env path rest ty restEnv
          written →
        EnvJoin updated restEnv result →
        WriteBorrowTargetsEffectiveWrite rank env path (target :: rest) ty
          result written

  /-- Effective writes performed by an environment write. -/
  inductive EnvWriteEffectiveWrite :
      Nat → Env → LVal → Ty → Env → LVal → Prop where
    | intro {rank : Nat} {env₁ env₂ : Env} {lv written : LVal}
        {slot : EnvSlot} {ty : Ty} {updatedTy : PartialTy} :
        env₁.slotAt (LVal.base lv) = some slot →
        UpdateAtPathEffectiveWrite rank env₁ (LVal.base lv) (LVal.path lv)
          slot.ty ty env₂ updatedTy written →
        EnvWriteEffectiveWrite rank env₁ lv ty
          (env₂.update (LVal.base lv) { slot with ty := updatedTy }) written
end

/--
No surviving borrow target may dereference through an effective write in the
pre-write environment.

This is a local assignment-side obligation, weaker than global `BorrowSafeEnv`:
it only talks about old or newly surviving borrow targets in the write result,
and only forbids the stale-resolution shape where an effective write is a
strict prefix of a live borrow target as resolved before the write.
-/
def EnvWriteNoStaleBorrowTargets
    (rank : Nat) (env : Env) (lv : LVal) (rhsTy : Ty) (result : Env) : Prop :=
  ∀ written x slot mutable targets target,
    EnvWriteEffectiveWrite rank env lv rhsTy result written →
    result.slotAt x = some slot →
    result ⊢ x ↝ (.borrow mutable targets) →
    target ∈ targets →
    EnvMayReadThrough env written target →
    False

theorem EnvWrite.finiteSupport {rank : Nat} {env result : Env}
    {lv : LVal} {ty : Ty} :
    EnvWrite rank env lv ty result →
    Env.FiniteSupport env →
    Env.FiniteSupport result := by
  intro hwrite
  exact EnvWrite.rec
    (motive_1 := fun _ env _ _ _ result _ _ =>
      Env.FiniteSupport env → Env.FiniteSupport result)
    (motive_2 := fun _ env _ _ _ result _ =>
      Env.FiniteSupport env → Env.FiniteSupport result)
    (motive_3 := fun _ env _ _ result _ =>
      Env.FiniteSupport env → Env.FiniteSupport result)
    (fun {env old ty} hfinite => hfinite)
    (fun {env rank old joined ty} _hshape _hjoin hfinite => hfinite)
    (fun {env₁ env₂ rank path inner updatedInner ty} _hupdate ih hfinite =>
      ih hfinite)
    (fun {env₁ env₂ rank path inner updatedInner ty} _hupdate ih hfinite =>
      ih hfinite)
    (fun {env₁ env₂ rank path targets ty} _htargets ih hfinite =>
      ih hfinite)
    (fun {rank env path ty} hfinite => hfinite)
    (fun {rank env updated path target ty} _hwrite _hleafTyping ih hfinite =>
      ih hfinite)
    (fun {rank env updated restEnv result path target rest ty} _hwrite
        _hleafTyping _hrest hjoin ihWrite _ihRest hfinite =>
      EnvJoin.finiteSupport_left hjoin (ihWrite hfinite))
    (fun {rank env₁ env₂ lv slot ty updatedTy} _hslot _hupdate ih hfinite =>
      (ih hfinite).update)
    hwrite

/-- Value typing premise `σ ⊢ v : T` from T-Const. -/
inductive ValueTyping : StoreTyping → Value → Ty → Prop where
  | unit {typing : StoreTyping} :
      ValueTyping typing .unit .unit
  | int {typing : StoreTyping} {value : Int} :
      ValueTyping typing (.int value) .int
  | bool {typing : StoreTyping} {value : Bool} :
      ValueTyping typing (.bool value) .bool
  | ref {typing : StoreTyping} {ref : Reference} {ty : Ty} :
      typing.tyOf ref.location = some ty →
      ValueTyping typing (.ref ref) ty

theorem ValueTyping.deterministic {typing : StoreTyping} {value : Value}
    {left right : Ty} :
    ValueTyping typing value left →
    ValueTyping typing value right →
    left = right := by
  intro hleft hright
  cases hleft <;> cases hright
  · rfl
  · rfl
  · rfl
  · rename_i hleftLookup hrightLookup
    rw [hleftLookup] at hrightLookup
    exact Option.some.inj hrightLookup

mutual
  /-- Section 3.4 term typing `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂`. -/
  inductive TermTyping : Env → StoreTyping → Lifetime → Term → Ty → Env → Prop where
    /-- T-Const. -/
    | const {env : Env} {typing : StoreTyping} {lifetime : Lifetime}
        {value : Value} {ty : Ty} :
        ValueTyping typing value ty →
        TermTyping env typing lifetime (.val value) ty env
    /-- T-Missing: synthetic extractor placeholder.  The loan-freedom premise
    keeps the placeholder from claiming a borrow of an existing place, which
    would break borrow safety of the result environment. -/
    | missing {env : Env} {typing : StoreTyping} {lifetime : Lifetime}
        {ty : Ty} :
        WellFormedTy env ty lifetime →
        TyLoanFree ty →
        TermTyping env typing lifetime .missing ty env
    /-- T-Copy. -/
    | copy {env : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
        {lv : LVal} {ty : Ty} :
        LValTyping env lv (.ty ty) valueLifetime →
        CopyTy ty →
        ¬ ReadProhibited env lv →
        TermTyping env typing lifetime (.copy lv) ty env
    /-- T-Move. -/
    | move {env₁ env₂ : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
        {lv : LVal} {ty : Ty} :
        LValTyping env₁ lv (.ty ty) valueLifetime →
        ¬ WriteProhibited env₁ lv →
        EnvMove env₁ lv env₂ →
        TermTyping env₁ typing lifetime (.move lv) ty env₂
    /-- T-MutBorrow. -/
    | mutBorrow {env : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
        {lv : LVal} {ty : Ty} :
        LValTyping env lv (.ty ty) valueLifetime →
        Mutable env lv →
        ¬ WriteProhibited env lv →
        TermTyping env typing lifetime (.borrow true lv) (.borrow true [lv]) env
    /-- T-ImmBorrow. -/
    | immBorrow {env : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
        {lv : LVal} {ty : Ty} :
        LValTyping env lv (.ty ty) valueLifetime →
        ¬ ReadProhibited env lv →
        TermTyping env typing lifetime (.borrow false lv) (.borrow false [lv]) env
    /-- T-Box. -/
    | box {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
        {term : Term} {ty : Ty} :
        TermTyping env₁ typing lifetime term ty env₂ →
        TermTyping env₁ typing lifetime (.box term) (.box ty) env₂
    /-- T-Block. -/
    | block {env₁ env₂ env₃ : Env} {typing : StoreTyping}
        {lifetime blockLifetime : Lifetime} {terms : List Term} {ty : Ty} :
        LifetimeChild lifetime blockLifetime →
        TermListTyping env₁ typing blockLifetime terms ty env₂ →
        WellFormedTy env₂ ty lifetime →
        env₃ = env₂.dropLifetime blockLifetime →
        TermTyping env₁ typing lifetime (.block blockLifetime terms) ty env₃
    /-- T-Declare. -/
    | declare {env₁ env₂ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
        {x : Name} {term : Term} {ty : Ty} :
        env₁.fresh x →
        TermTyping env₁ typing lifetime term ty env₂ →
        env₂.fresh x →
        FreshUpdateCoherenceObligations env₂ x ty lifetime →
        env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
        TermTyping env₁ typing lifetime (.letMut x term) .unit env₃
    /-- T-Assign. -/
    | assign {env₁ env₂ env₃ : Env} {typing : StoreTyping}
        {lifetime targetLifetime : Lifetime} {lhs : LVal}
        {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
        TermTyping env₁ typing lifetime rhs rhsTy env₂ →
        LValTyping env₂ lhs oldTy targetLifetime →
        ShapeCompatible env₂ oldTy (.ty rhsTy) →
        WellFormedTy env₂ rhsTy targetLifetime →
        EnvWrite 0 env₂ lhs rhsTy env₃ →
        EnvWriteNoStaleBorrowTargets 0 env₂ lhs rhsTy env₃ →
        (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
        Coherent env₃ →
        EnvWriteRhsTargetsWellFormed env₃ rhsTy →
        ¬ WriteProhibited env₃ lhs →
        TermTyping env₁ typing lifetime (.assign lhs rhs) .unit env₃
    /-- T-Eqal, Section 6.1.2, with the paper's ghost-slot check.

    The right operand is typed only in `Γ₂[γ ↦ ⟨T₁⟩^l]`, where `γ` is a fresh
    anonymous slot representing the left operand value that remains live while
    the right operand is evaluated.  The result environment erases `γ` again.

    The explicit non-occurrence premise records that the anonymous slot is not
    source-addressable syntax.  It is what lets the metatheory thin the ghost
    slot back out after it has done its borrow-conflict filtering job. -/
    | eq {env₁ env₂ env₃ envGhost : Env} {ghost : Name}
        {typing : StoreTyping} {lifetime : Lifetime}
        {lhs rhs : Term} {lhsTy rhsTy : Ty} :
        TermTyping env₁ typing lifetime lhs lhsTy env₂ →
        env₂.fresh ghost →
        Env.TypeNameFresh env₂ ghost →
        ghost ∉ Ty.allVars lhsTy →
        StoreTyping.TypeNameFresh typing ghost →
        TermTyping
          (env₂.update ghost { ty := .ty lhsTy, lifetime := lifetime })
          typing lifetime rhs rhsTy envGhost →
        ¬ Term.Mentions ghost rhs →
        env₃ = envGhost.erase ghost →
        CopyTy lhsTy →
        CopyTy rhsTy →
        ShapeCompatible env₃ (.ty lhsTy) (.ty rhsTy) →
        TermTyping env₁ typing lifetime (.eq lhs rhs) .bool env₃
    /-- T-If, Section 6.1.2.

    The condition types as `bool`, both branches are typed in the
    post-condition environment, and the resulting type/environment are the
    joins (Definitions 3.8 and 3.10) of the branch results.

    Legacy mechanisation obligations on the joined result, following the
    repo's earlier convention of rule-carried obligations (cf. `T-Assign`).
    `EnvJoinSameShape` is no longer a premise: join shape facts used by the
    metatheory are derived internally from the weak initialized invariant and
    the concrete join construction.

    * `Coherent`, `Linearizable` — the result invariants needed to type
      dereferences through joined borrow target lists.  The per-target
      `ContainedBorrowsWellFormed` invariant is derived in the preservation
      proof from the branch invariants plus these result obligations. -/
    | ite {env₁ env₂ env₃ env₄ env₅ : Env} {typing : StoreTyping}
        {lifetime : Lifetime} {condition trueBranch falseBranch : Term}
        {trueTy falseTy joinTy : Ty} :
        TermTyping env₁ typing lifetime condition .bool env₂ →
        TermTyping env₂ typing lifetime trueBranch trueTy env₃ →
        TermTyping env₂ typing lifetime falseBranch falseTy env₄ →
        PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy) →
        EnvJoin env₃ env₄ env₅ →
        WellFormedTy env₅ joinTy lifetime →
        Coherent env₅ →
        Linearizable env₅ →
        TermTyping env₁ typing lifetime (.ite condition trueBranch falseBranch)
          joinTy env₅
    /-- T-IfDiv: divergence-aware conditional merge.

    Rust accepts `if c { t } else { …; panic!() }` even when the truncated
    else-branch and the live branch disagree on moves or types: the
    `panic!()`-terminated branch has the never type `!`, so control never
    flows from it to the merge point and it contributes nothing to the
    borrow-state join.  `Term.Diverges` is the syntactic counterpart of that
    `!`-propagation.

    The diverging branch is still fully type- and borrow-checked (premise
    three) — this is what lets the extractor keep a truncated branch's
    constraints — but the result type and environment are exactly the live
    branch's, and none of `T-If`'s join obligations are needed because no
    join happens. -/
    | iteDiverging {env₁ env₂ env₃ env₄ : Env} {typing : StoreTyping}
        {lifetime : Lifetime} {condition trueBranch falseBranch : Term}
        {trueTy falseTy : Ty} :
        TermTyping env₁ typing lifetime condition .bool env₂ →
        TermTyping env₂ typing lifetime trueBranch trueTy env₃ →
        TermTyping env₂ typing lifetime falseBranch falseTy env₄ →
        falseBranch.Diverges →
        TermTyping env₁ typing lifetime
          (.ite condition trueBranch falseBranch) trueTy env₃
    /-- T-IfDivT: mirror image of `T-IfDiv` for a diverging true branch.

    This models Rust's statement-level `if c { ...; panic!() }`: when the
    true branch diverges, only the false branch can reach the merge point. -/
    | iteTrueDiverging {env₁ env₂ env₃ env₄ : Env} {typing : StoreTyping}
        {lifetime : Lifetime} {condition trueBranch falseBranch : Term}
        {trueTy falseTy : Ty} :
        TermTyping env₁ typing lifetime condition .bool env₂ →
        TermTyping env₂ typing lifetime trueBranch trueTy env₃ →
        TermTyping env₂ typing lifetime falseBranch falseTy env₄ →
        trueBranch.Diverges →
        TermTyping env₁ typing lifetime
          (.ite condition trueBranch falseBranch) falseTy env₄
  inductive TermListTyping : Env → StoreTyping → Lifetime → List Term → Ty → Env → Prop where
    /-- T-Seq, singleton sequence. -/
    | singleton {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
        {term : Term} {ty : Ty} :
        TermTyping env₁ typing lifetime term ty env₂ →
        TermListTyping env₁ typing lifetime [term] ty env₂
    /-- T-Seq, environment threading through `t₁; ...; tₙ`. -/
    | cons {env₁ env₂ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
        {term : Term} {rest : List Term} {termTy finalTy : Ty} :
        TermTyping env₁ typing lifetime term termTy env₂ →
        TermListTyping env₂ typing lifetime rest finalTy env₃ →
        TermListTyping env₁ typing lifetime (term :: rest) finalTy env₃
end

theorem TermTyping.finiteSupport {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping env₁ typing lifetime term ty env₂ →
    Env.FiniteSupport env₁ →
    Env.FiniteSupport env₂ := by
  intro htyping
  exact TermTyping.rec
    (motive_1 := fun env _typing _lifetime _term _ty result _ =>
      Env.FiniteSupport env → Env.FiniteSupport result)
    (motive_2 := fun env _typing _lifetime _terms _ty result _ =>
      Env.FiniteSupport env → Env.FiniteSupport result)
    (fun _hvalue hfinite => hfinite)
    (fun _hwellTy _hloanFree hfinite => hfinite)
    (fun _hlv _hcopy _hnotRead hfinite => hfinite)
    (fun _hlv _hnotWrite hmove hfinite =>
      EnvMove.finiteSupport hmove hfinite)
    (fun _hlv _hmutable _hnotWrite hfinite => hfinite)
    (fun _hlv _hnotRead hfinite => hfinite)
    (fun _hterm ih hfinite => ih hfinite)
    (fun _hchild _hterms _hwellTy henvEq ih hfinite => by
      rw [henvEq]
      exact (ih hfinite).dropLifetime)
    (fun _hfresh _hterm _hfreshResult _hcoherence henvEq ih hfinite => by
      rw [henvEq]
      exact (ih hfinite).update)
    (fun _hrhs _hlhs _hshape _hwellTy hwrite _hnoStale _hrank _hcoherence
        _hcontained _hnotWrite ih hfinite =>
      EnvWrite.finiteSupport hwrite (ih hfinite))
    (fun _hlhs _hfresh _htypeFresh _hnotTy _hstoreFresh _hrhs
        _hnotMentions henvEq _hcopyL _hcopyR _hshape ihLhs ihRhs hfinite => by
      rw [henvEq]
      exact (ihRhs (ihLhs hfinite).update).erase)
    (fun _hcondition _htrue _hfalse _htyJoin henvJoin
        _hwellTy _hcoherent _hlinear
        ihCondition ihTrue _ihFalse hfinite =>
      EnvJoin.finiteSupport_left henvJoin (ihTrue (ihCondition hfinite)))
    (fun _hcondition _htrue _hfalse _hdiverges ihCondition ihTrue
        _ihFalse hfinite =>
      ihTrue (ihCondition hfinite))
    (fun _hcondition _htrue _hfalse _hdiverges ihCondition _ihTrue
        ihFalse hfinite =>
      ihFalse (ihCondition hfinite))
    (fun _hterm ih hfinite => ih hfinite)
    (fun _hterm _hrest ihTerm ihRest hfinite =>
      ihRest (ihTerm hfinite))
    htyping

/--
Derived equality typing rule that chooses the anonymous equality slot from
finite support instead of requiring callers to name it and prove freshness.

The RHS is still checked in the ghost-extended environment.  The continuation
must work for the fresh ghost chosen by `exists_fresh_eq_ghost`.
-/
theorem TermTyping.eq_finite {env₁ env₂ env₃ : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {lhs rhs : Term} {lhsTy rhsTy : Ty} :
    TermTyping env₁ typing lifetime lhs lhsTy env₂ →
    Env.FiniteSupport env₁ →
    StoreTyping.FiniteSupport typing →
    (∀ ghost,
      env₂.fresh ghost →
      Env.TypeNameFresh env₂ ghost →
      ghost ∉ Ty.allVars lhsTy →
      StoreTyping.TypeNameFresh typing ghost →
      ¬ Term.Mentions ghost rhs →
      ∃ envGhost,
        TermTyping
          (env₂.update ghost { ty := .ty lhsTy, lifetime := lifetime })
          typing lifetime rhs rhsTy envGhost ∧
        env₃ = envGhost.erase ghost) →
    CopyTy lhsTy →
    CopyTy rhsTy →
    ShapeCompatible env₃ (.ty lhsTy) (.ty rhsTy) →
    TermTyping env₁ typing lifetime (.eq lhs rhs) .bool env₃ := by
  intro hLhs hfiniteEnv hfiniteTyping hRhs hcopyL hcopyR hshape
  have hfiniteEnv₂ : Env.FiniteSupport env₂ :=
    hLhs.finiteSupport hfiniteEnv
  rcases exists_fresh_eq_ghost (env := env₂) (typing := typing)
      (lhsTy := lhsTy) (rhs := rhs) hfiniteEnv₂ hfiniteTyping with
    ⟨ghost, hfresh, htypeFresh, htyFresh, hstoreFresh, hnotMention⟩
  rcases hRhs ghost hfresh htypeFresh htyFresh hstoreFresh hnotMention with
    ⟨envGhost, hRhsGhost, henvEq⟩
  exact TermTyping.eq hLhs hfresh htypeFresh htyFresh hstoreFresh
    hRhsGhost hnotMention henvEq hcopyL hcopyR hshape

theorem BorrowSafeEnv.erase {env : Env} {ghost : Name} :
    BorrowSafeEnv env →
    BorrowSafeEnv (env.erase ghost) := by
  intro hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    hx hy htargetMutable htargetOther hconflict
  rcases hx with ⟨xSlot, hxSlot, hxContains⟩
  rcases hy with ⟨ySlot, hySlot, hyContains⟩
  have hxOrig : env ⊢ x ↝ (.borrow true targetsMutable) := by
    by_cases hxGhost : x = ghost
    · subst hxGhost
      simp [Env.erase] at hxSlot
    · exact ⟨xSlot, by simpa [Env.erase, hxGhost] using hxSlot, hxContains⟩
  have hyOrig : env ⊢ y ↝ (Ty.borrow mutable targetsOther) := by
    by_cases hyGhost : y = ghost
    · subst hyGhost
      simp [Env.erase] at hySlot
    · exact ⟨ySlot, by simpa [Env.erase, hyGhost] using hySlot, hyContains⟩
  exact hsafe x y mutable targetsMutable targetsOther targetMutable targetOther
    hxOrig hyOrig htargetMutable htargetOther hconflict

end Paper
end LwRust
