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


@[simp] theorem update_slotAt_same (env : Env) (x : Name) (slot : EnvSlot) :
    (env.update x slot).slotAt x = some slot := by
  simp [update]

@[simp] theorem update_slotAt_ne (env : Env) {x y : Name} (slot : EnvSlot) :
    y ≠ x →
    (env.update x slot).slotAt y = env.slotAt y := by
  intro hne
  simp [update, hne]

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

end StoreTyping

/-- Definition 3.6, `copy(T)`. -/
inductive CopyTy : Ty → Prop where
  | int :
      CopyTy .int
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

This is the least upper bound for the strengthening preorder from Definition
3.7.  In the `T-LvBor` rule, the paper writes the same operation over a finite
target list as `⋃ᵢ Tᵢ`; this is a join/union of static type information, not a
set union of runtime locations.
-/
def PartialTyJoin (left right join : PartialTy) : Prop :=
  IsLUB ({left, right} : Set PartialTy) join

@[simp] theorem PartialTyJoin.self (ty : PartialTy) :
    PartialTyJoin ty ty ty := by
  simp [PartialTyJoin, IsLUB, IsLeast, upperBounds, lowerBounds]

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

/-- Definition 3.10, environment join `Γ₁ ⊔ Γ₂`. -/
def EnvJoin (left right join : Env) : Prop :=
  IsLUB ({left, right} : Set Env) join

/-- A finite join of environments, used by the write-through-borrow case. -/
inductive EnvJoinMany : List Env → Env → Prop where
  | nil {env : Env} :
      EnvJoinMany [] env
  | singleton {env : Env} :
      EnvJoinMany [env] env
  | cons {first second join final : Env} {rest : List Env} :
      EnvJoin first second join →
      EnvJoinMany (join :: rest) final →
      EnvJoinMany (first :: second :: rest) final

/--
Lifetime order used in the paper: `outer` outlives `inner` when `outer` is a
prefix of `inner`.

The full set of lifetimes is tree-shaped, but the active lifetimes at one
program point form a chain.  On that chain we get semilattice-style min/max
operations.  This is not a ring or a monad.
-/
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

/-- Definitions 3.12 and 3.13 collapse to a list of dereference selectors. -/
abbrev Path := List Unit

def LVal.path : LVal → Path
  | .var _ => []
  | .deref lv => LVal.path lv ++ [()]

def LVal.base : LVal → Name
  | .var x => x
  | .deref lv => LVal.base lv

/-- Number of dereferences in an lval (length of its path). -/
def LVal.derefCount : LVal → Nat
  | .var _ => 0
  | .deref lv => LVal.derefCount lv + 1

/-- Variables occurring in a full type (the base names of all borrow targets). -/
def Ty.vars : Ty → List Name
  | .unit => []
  | .int => []
  | .borrow _ targets => targets.map LVal.base
  | .box inner => Ty.vars inner

/-- Variables occurring (in live borrows) in a partial type.

`undef` shadows are moved-out and carry no live borrow, mirroring
`PartialTyContains`, which does not descend into `undef`. -/
def PartialTy.vars : PartialTy → List Name
  | .ty t => Ty.vars t
  | .box inner => PartialTy.vars inner
  | .undef _ => []

/--
Definition 11 of `lw_rust_followup`, Linearizable typing.

An environment is linearizable when there is a rank function `φ` on variables
such that every variable strictly outranks all variables occurring in its slot
type.  This forbids cyclic borrow references and is the well-foundedness
condition that makes the `LValTyping` recursion (and hence shape-determinism of
borrow-target unions) terminate.
-/
def Linearizable (env : Env) : Prop :=
  ∃ φ : Name → Nat,
    ∀ x slot, env.slotAt x = some slot →
      ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x

/-- Structural shape equality of full types, ignoring borrow *target lists* (but
keeping the `mutable` flag).  Box types are rigid in the strengthening order, so
two box shapes count as equal only when their contents are literally equal —
which is all that arises, because box-typed lvals have a unique type. -/
def Ty.sameShape : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
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
lists must be subset-equivalent (same set).  This is what `LValTyping`
determinism actually establishes (target lists are unique up to set), and the
extra subset-equivalence is what lets reborrow chains be related. -/
def Ty.eqv : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .borrow m₁ t₁, .borrow m₂ t₂ => m₁ = m₂ ∧ t₁ ⊆ t₂ ∧ t₂ ⊆ t₁
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

def EnvContains (env : Env) (x : Name) (ty : Ty) : Prop :=
  ∃ slot, env.slotAt x = some slot ∧ PartialTyContains slot.ty ty

notation:50 env:51 " ⊢ " x:51 " ↝ " ty:51 => EnvContains env x ty

/-- Definition 3.16, `readProhibited(Γ, w)`. -/
def ReadProhibited (env : Env) (lv : LVal) : Prop :=
  ∃ x targets target,
    env ⊢ x ↝ (&mut targets) ∧
    target ∈ targets ∧
    target ⋈ lv

/-- Definition 3.17, `writeProhibited(Γ, w)`. -/
def WriteProhibited (env : Env) (lv : LVal) : Prop :=
  ReadProhibited env lv ∨
  ∃ x targets target,
    env ⊢ x ↝ (&targets) ∧
    target ∈ targets ∧
    target ⋈ lv

def Strike : Path → PartialTy → PartialTy → Prop
  | [], .ty sourceTy, .undef targetTy => sourceTy = targetTy
  | _ :: path, .box inner, .box struck => Strike path inner struck
  | _, _, _ => False

/-- Definition 3.18, `move(Γ, w)`. -/
def EnvMove (env : Env) (lv : LVal) (moved : Env) : Prop :=
  ∃ slot struck,
    env.slotAt (LVal.base lv) = some slot ∧
    Strike (LVal.path lv) slot.ty struck ∧
    moved = env.update (LVal.base lv) { slot with ty := struck }

/-- Definition 3.19, `mut(Γ, w)`. -/
inductive Mutable : Env → LVal → Prop where
  | var {env : Env} {x : Name} {slot : EnvSlot} :
      env.slotAt x = some slot →
      Mutable env (.var x)
  | box {env : Env} {lv : LVal} {inner : PartialTy} {lifetime : Lifetime} :
      LValTyping env lv (.box inner) lifetime →
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

end Env

/-- The variable slot at the base of an lval survives for the requested lifetime. -/
def LValBaseOutlives (env : Env) (lv : LVal) (lifetime : Lifetime) : Prop :=
  ∃ slot, env.slotAt (LVal.base lv) = some slot ∧ slot.lifetime ≤ lifetime

/--
All borrow targets are well formed for the requested lifetime.

This is the borrow invariant of Definition 4.8(i), stated faithfully **per
target**: each individual target lval `w` is typable (`Γ ⊢ w : T^m`) with its
own pointee type `T` and lifetime `m ≼ l`, plus the mechanisation's slot-survival
component used by drop/update preservation.

Note the deliberate separation from Definition 3.21 (`WellFormedTy`, the
well-formed *type* judgement): the paper's `L-Borrow` premise `Γ ⊢ u : ⟨T⟩^m`
types the whole target set *jointly* (one shared pointee type `T`).  That joint
typing is what the typing rules establish when a borrow is **created** (T-LvBor
produces an `LValTargetsTyping`).  The well-formedness invariant that must be
**preserved** through execution, however, is only the per-target statement of
Definition 4.8(i).  Conflating the two — carrying the joint typing as the runtime
invariant — is unsound at environment joins: rule W-Bor merges the target lists
of two borrows (`&u₁ ⊔ &u₂ = &(u₁ ⊔ u₂)`) without requiring their pointee types
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

/-- Definition 3.21, well-formed type `Γ ⊢ T ≽ l`. -/
inductive WellFormedTy : Env → Ty → Lifetime → Prop where
  /-- L-Unit, the unit case implicit in the paper's use of `ϵ`. -/
  | unit {env : Env} {lifetime : Lifetime} :
      WellFormedTy env .unit lifetime
  /-- L-Int. -/
  | int {env : Env} {lifetime : Lifetime} :
      WellFormedTy env .int lifetime
  /-- L-Borrow. -/
  | borrow {env : Env} {mutable : Bool} {targets : List LVal}
      {lifetime : Lifetime} :
      BorrowTargetsWellFormed env targets lifetime →
      WellFormedTy env (.borrow mutable targets) lifetime
  /-- L-Box. -/
  | box {env : Env} {ty : Ty} {lifetime : Lifetime} :
      WellFormedTy env ty lifetime →
      WellFormedTy env (.box ty) lifetime

/-- Definition 3.22, compatible shape `Γ ⊢ T̃₁ ≈ T̃₂`. -/
inductive ShapeCompatible : Env → PartialTy → PartialTy → Prop where
  /-- S-Unit, the unit case implicit in the paper's statement type. -/
  | unit {env : Env} :
      ShapeCompatible env (.ty .unit) (.ty .unit)
  /-- S-Int. -/
  | int {env : Env} :
      ShapeCompatible env (.ty .int) (.ty .int)
  /-- S-Box. -/
  | box {env : Env} {left right : PartialTy} :
      ShapeCompatible env left right →
      ShapeCompatible env (.box left) (.box right)
  /-- S-Bor.

  Definition 3.22 requires the borrow *pointee* types to be shape compatible,
  not merely that each target is individually typeable.  Concretely all left
  targets share a pointee type `leftTy`, all right targets share `rightTy`, and
  `leftTy ≈ rightTy`.  Dropping the `ShapeCompatible env (.ty leftTy) (.ty
  rightTy)` premise (as an earlier version did) makes `T-Assign` accept e.g.
  `&mut &c ≈ &mut int`, after which a write-through-borrow weak update can build
  the ill-formed type `&mut[a,b]` with non-joinable pointees — breaking
  Borrow Invariance (Lemma 4.9). -/
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

mutual
  /-- Definition 3.23, `update_k(Γ, π | T̃, T)`. -/
  inductive UpdateAtPath : Nat → Env → List Unit → PartialTy → Ty → Env → PartialTy → Prop where
    | strong {env : Env} {old : PartialTy} {ty : Ty} :
        UpdateAtPath 0 env [] old ty env (.ty ty)
    | weak {env : Env} {rank : Nat} {old joined : PartialTy} {ty : Ty} :
        PartialTyJoin old (.ty ty) joined →
        UpdateAtPath (rank + 1) env [] old ty env joined
    | box {env₁ env₂ : Env} {rank : Nat} {path : List Unit}
        {inner updatedInner : PartialTy} {ty : Ty} :
        UpdateAtPath rank env₁ path inner ty env₂ updatedInner →
        UpdateAtPath rank env₁ (() :: path) (.box inner) ty env₂ (.box updatedInner)
    | mutBorrow {env₁ env₂ : Env} {rank : Nat} {path : List Unit}
        {targets : List LVal} {ty : Ty} :
        WriteBorrowTargets (rank + 1) env₁ path targets ty env₂ →
        UpdateAtPath rank env₁ (() :: path) (.ty (.borrow true targets)) ty
          env₂ (.ty (.borrow true targets))

  /-- The joined environment from updating each possible target of a borrow. -/
  inductive WriteBorrowTargets :
      Nat → Env → List Unit → List LVal → Ty → Env → Prop where
    | nil {rank : Nat} {env : Env} {path : List Unit} {ty : Ty} :
        WriteBorrowTargets rank env path [] ty env
    | singleton {rank : Nat} {env updated : Env} {path : List Unit}
        {target : LVal} {ty : Ty} :
        EnvWrite rank env (prependPath path target) ty updated →
        WriteBorrowTargets rank env path [target] ty updated
    | cons {rank : Nat} {env updated restEnv result : Env} {path : List Unit}
        {target : LVal} {rest : List LVal} {ty : Ty} :
        EnvWrite rank env (prependPath path target) ty updated →
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

/-- Value typing premise `σ ⊢ v : T` from T-Const. -/
inductive ValueTyping : StoreTyping → Value → Ty → Prop where
  | unit {typing : StoreTyping} :
      ValueTyping typing .unit .unit
  | int {typing : StoreTyping} {value : Int} :
      ValueTyping typing (.int value) .int
  | ref {typing : StoreTyping} {ref : Reference} {ty : Ty} :
      typing.tyOf ref.location = some ty →
      ValueTyping typing (.ref ref) ty

mutual
  /-- Section 3.4 term typing `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂`. -/
  inductive TermTyping : Env → StoreTyping → Lifetime → Term → Ty → Env → Prop where
    /-- T-Const. -/
    | const {env : Env} {typing : StoreTyping} {lifetime : Lifetime}
        {value : Value} {ty : Ty} :
        ValueTyping typing value ty →
        TermTyping env typing lifetime (.val value) ty env
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
        env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
        TermTyping env₁ typing lifetime (.letMut x term) .unit env₃
    /-- T-Assign. -/
    | assign {env₁ env₂ env₃ : Env} {typing : StoreTyping}
        {lifetime targetLifetime : Lifetime} {lhs : LVal}
        {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
        LValTyping env₁ lhs oldTy targetLifetime →
        TermTyping env₁ typing lifetime rhs rhsTy env₂ →
        ShapeCompatible env₂ oldTy (.ty rhsTy) →
        WellFormedTy env₂ rhsTy targetLifetime →
        EnvWrite 0 env₂ lhs rhsTy env₃ →
        ¬ WriteProhibited env₃ lhs →
        TermTyping env₁ typing lifetime (.assign lhs rhs) .unit env₃

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

end Paper
end LwRust
