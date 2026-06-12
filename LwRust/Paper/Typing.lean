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

/-- Variables occurring in a full type (the base names of all borrow targets). -/
def Ty.vars : Ty → List Name
  | .unit => []
  | .int => []
  | .bool => []
  | .borrow _ targets => targets.map LVal.base
  | .box inner => Ty.vars inner

/-- Variables occurring (in live borrows) in a partial type.

`undef` shadows are moved-out and carry no live borrow, mirroring
`PartialTyContains`, which does not descend into `undef`. -/
def PartialTy.vars : PartialTy → List Name
  | .ty t => Ty.vars t
  | .box inner => PartialTy.vars inner
  | .undef _ => []

/-- A fixed rank function witnessing linearizability of an environment. -/
def LinearizedBy (φ : Name → Nat) (env : Env) : Prop :=
  ∀ x slot, env.slotAt x = some slot →
    ∀ v, v ∈ PartialTy.vars slot.ty → φ v < φ x

/--
Definition 11 of `lw_rust_followup`, Linearizable typing.

An environment is linearizable when there is a rank function `φ` on variables
such that every variable strictly outranks all variables occurring in its slot
type.  This forbids cyclic borrow references and is the well-foundedness
condition that makes the `LValTyping` recursion (and hence shape-determinism of
borrow-target unions) terminate.
-/
def Linearizable (env : Env) : Prop :=
  ∃ φ : Name → Nat, LinearizedBy φ env

/-- Structural shape equality of full types, ignoring borrow *target lists* (but
keeping the `mutable` flag). -/
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
lists must be subset-equivalent (same set).  This is what `LValTyping`
determinism actually establishes (target lists are unique up to set), and the
extra subset-equivalence is what lets reborrow chains be related. -/
def Ty.eqv : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .bool, .bool => True
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

/--
Coherence obligations for adding a fresh full-typed slot.

This is deliberately carried by the declaration/result rules rather than
derived from `WellFormedTy`: a declared borrow type such as `&[]` is syntactically
well formed in the paper's target-well-formedness premise, but it is not
lvalue-coherent because empty target lists are not jointly typeable.
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
Rank and RHS-fan-out safety obligation for assignment writes.

Every borrow edge installed from the RHS type must point to a lower-ranked base
in the pre-write environment.  Additionally, if a write fan-out duplicates RHS
borrow targets into two result roots, any resulting mutable-borrow conflict must
be within one root.  This is the explicit rule-side replacement for assuming
that all environment writes preserve linearizability and borrow safety.
-/
def EnvWriteRhsBorrowTargetsBelow (φ : Name → Nat) (result : Env) (rhsTy : Ty) : Prop :=
  (∀ x slot mutable targets target,
      result.slotAt x = some slot →
      PartialTyContains slot.ty (.borrow mutable targets) →
      target ∈ targets →
      (∃ rhsMutable rhsTargets,
        PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets) ∧
          target ∈ rhsTargets) →
      φ (LVal.base target) < φ x) ∧
  (∀ x y mutable targetsMutable targetsOther targetMutable targetOther,
      result ⊢ x ↝ (.borrow true targetsMutable) →
      result ⊢ y ↝ (.borrow mutable targetsOther) →
      targetMutable ∈ targetsMutable →
      targetOther ∈ targetsOther →
      targetMutable ⋈ targetOther →
      (∃ rhsMutable rhsTargets,
        PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets) ∧
          targetMutable ∈ rhsTargets) →
      (∃ rhsMutable rhsTargets,
        PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets) ∧
          targetOther ∈ rhsTargets) →
      x = y)

/--
Coherence obligations for assignment writes.

For old roots, borrow typings in the result must transport back to the pre-write
environment, and coherent target lists from that environment must transport
forward.  For the written root, the updated path must directly provide the
joint target-list typing required by coherence.
-/
structure EnvWriteCoherenceObligations
    (env result : Env) (writeBase : Name) : Prop where
  old_root_transport
    {lv : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime : Lifetime} :
    LVal.base lv ≠ writeBase →
    LValTyping result lv (.ty (.borrow mutable targets)) borrowLifetime →
    (∃ oldBorrowLifetime,
      LValTyping env lv (.ty (.borrow mutable targets)) oldBorrowLifetime) ∧
      (∀ targetTy targetLifetime,
        LValTargetsTyping env targets (.ty targetTy) targetLifetime →
        ∃ resultTargetTy resultTargetLifetime,
          LValTargetsTyping result targets (.ty resultTargetTy) resultTargetLifetime)
  written_root_coherent
    {lv : LVal} {mutable : Bool} {targets : List LVal}
    {borrowLifetime : Lifetime} :
    LVal.base lv = writeBase →
    LValTyping result lv (.ty (.borrow mutable targets)) borrowLifetime →
    ∃ targetTy targetLifetime,
      LValTargetsTyping result targets (.ty targetTy) targetLifetime

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

/-- Slot-local borrow invariant for a partial type. -/
def PartialTyBorrowsWellFormedInSlot
    (env : Env) (slotLifetime : Lifetime) (partialTy : PartialTy) : Prop :=
  ∀ {mutable targets},
    PartialTyContains partialTy (.borrow mutable targets) →
    BorrowTargetsWellFormedInSlot env slotLifetime targets

/-- Every borrow contained in every environment slot has well-formed targets. -/
def ContainedBorrowsWellFormed (env : Env) : Prop :=
  ∀ x slot mutable targets,
    env.slotAt x = some slot →
    env ⊢ x ↝ (Ty.borrow mutable targets) →
    BorrowTargetsWellFormedInSlot env slot.lifetime targets

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
    ∃ ty lifetime, LValTargetsTyping env targets (.ty ty) lifetime

theorem Linearizable.of_linearizedBy {φ : Name → Nat} {env : Env} :
    LinearizedBy φ env → Linearizable env := by
  intro hφ
  exact ⟨φ, hφ⟩

/-- Definition 4.8, well-formed environment, with the maintained invariants. -/
def WellFormedEnv (env : Env) (lifetime : Lifetime) : Prop :=
  ContainedBorrowsWellFormed env ∧ EnvSlotsOutlive env lifetime ∧
    Coherent env ∧ Linearizable env

/--
Definition 4.13, borrow-safe environment.

The paper phrases this over variables in `dom(Γ)` and borrowed lvalues inside
contained borrow types.  The containment premises already imply the relevant
variables are present in the environment.

This lives here (rather than with the Section 4.3 helpers) because the
control-flow extension's `T-If` rule carries it as an obligation for the
joined result environment; see `TermTyping.ite`.
-/
def BorrowSafeEnv (env : Env) : Prop :=
  ∀ x y mutable targetsMutable targetsOther targetMutable targetOther,
    env ⊢ x ↝ (&mut targetsMutable) →
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

/-- A type whose contained borrows all have empty target lists.  Carried by
`T-Missing`: a placeholder typed at `&mut []` claims no loan on any existing
place, so installing it cannot create a borrow conflict.  This is the static
analogue of `ast_copier`'s `__missing__<T>() -> T` returning a reference with
a fresh region and no outstanding loans. -/
def TyLoanFree (ty : Ty) : Prop :=
  ∀ mutable targets,
    PartialTyContains (.ty ty) (.borrow mutable targets) → targets = []

def PartialTyLoanFree (ty : PartialTy) : Prop :=
  ∀ mutable targets,
    PartialTyContains ty (.borrow mutable targets) → targets = []

def EnvJoinSameShape (branch join : Env) : Prop :=
  ∀ x branchSlot joinSlot,
    branch.slotAt x = some branchSlot →
    join.slotAt x = some joinSlot →
    PartialTy.sameShape branchSlot.ty joinSlot.ty

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
        ShapeCompatible env old (.ty ty) →
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
    would break borrow safety of the result environment (Corollary 4.14);
    borrow shapes themselves are allowed via empty target lists. -/
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
        LValTyping env₁ lhs oldTy targetLifetime →
        TermTyping env₁ typing lifetime rhs rhsTy env₂ →
        LValTyping env₂ lhs oldTy targetLifetime →
        ShapeCompatible env₂ oldTy (.ty rhsTy) →
        WellFormedTy env₂ rhsTy targetLifetime →
        EnvWrite 0 env₂ lhs rhsTy env₃ →
        (∃ φ, LinearizedBy φ env₂ ∧ EnvWriteRhsBorrowTargetsBelow φ env₃ rhsTy) →
        EnvWriteCoherenceObligations env₂ env₃ (LVal.base lhs) →
        ContainedBorrowsWellFormed env₃ →
        ¬ WriteProhibited env₃ lhs →
        TermTyping env₁ typing lifetime (.assign lhs rhs) .unit env₃
    /-- T-Eqal, Section 6.1.2, with the paper's ghost-slot check.

    The paper types the right operand in `Γ₂[γ ↦ ⟨T₁⟩^l]` for an anonymous
    fresh `γ` and erases `γ` afterwards, so that borrows inside `T₁` keep
    prohibiting conflicting uses while the right operand is typed.  The
    third premise is exactly that check.  The ghost slot has no runtime
    counterpart, so its derivation cannot be threaded through preservation
    (safe abstraction `S ∼ Γ` demands two-way domain agreement), and
    eliminating it afterwards would need the fresh-slot thinning
    metatheorem, which the paper does not provide.  Following the
    rule-carried-obligation convention (cf. `T-WhileJoin`), the rule
    therefore *also* carries the eliminated form (fourth premise) — in the
    paper's system it is implied by the ghost form, and it is what the
    metatheory threads.  The ghost premise is a pure filter restoring the
    paper's strictness: a right operand that conflicts with borrows in the
    left operand's result type is rejected. -/
    | eq {env₁ env₂ env₃ envGhost : Env} {ghost : Name}
        {typing : StoreTyping} {lifetime : Lifetime}
        {lhs rhs : Term} {lhsTy rhsTy ghostRhsTy : Ty} :
        TermTyping env₁ typing lifetime lhs lhsTy env₂ →
        env₂.fresh ghost →
        TermTyping
          (env₂.update ghost { ty := .ty lhsTy, lifetime := lifetime })
          typing lifetime rhs ghostRhsTy envGhost →
        TermTyping env₂ typing lifetime rhs rhsTy env₃ →
        CopyTy lhsTy →
        CopyTy rhsTy →
        ShapeCompatible env₃ (.ty lhsTy) (.ty rhsTy) →
        TermTyping env₁ typing lifetime (.eq lhs rhs) .bool env₃
    /-- T-If, Section 6.1.2.

    The condition types as `bool`, both branches are typed in the
    post-condition environment, and the resulting type/environment are the
    joins (Definitions 3.8 and 3.10) of the branch results.

    Mechanisation obligations on the joined result, following the repo
    convention of rule-carried obligations (cf. `T-Assign`):

    * `EnvJoinSameShape` for both branches — branches must agree on each
      variable's initialisation state (see that definition for why the
      paper's more liberal join is unsound against Definition 4.4 as
      printed);
    * `ContainedBorrowsWellFormed`, `Coherent`, `Linearizable` — the
      well-formed-environment invariants for the join.  Joins merge borrow
      target lists, so these do not follow from the branch invariants by a
      local argument; they are carried, as the corresponding `T-Assign`
      obligations are;
    * `BorrowSafeEnv` — joins can merge mutable borrows of *different*
      variables into one target list, in which case the joined environment
      is genuinely not borrow safe even though each branch is (the paper
      concedes the corresponding weakening of Corollary 4.14 for this
      extension in Section 4.5.1).  The preservation architecture threads
      borrow safety through sequencing, so the mechanised rule only accepts
      conditionals whose join remains borrow safe;
    * `TyBorrowSafeAgainstEnv` for the result type — this is the
      root-independent result-extension invariant used by Corollary 4.14.
      It does not follow from branch-local result safety because the joined
      result can be installed in the joined environment. -/
    | ite {env₁ env₂ env₃ env₄ env₅ : Env} {typing : StoreTyping}
        {lifetime : Lifetime} {condition trueBranch falseBranch : Term}
        {trueTy falseTy joinTy : Ty} :
        TermTyping env₁ typing lifetime condition .bool env₂ →
        TermTyping env₂ typing lifetime trueBranch trueTy env₃ →
        TermTyping env₂ typing lifetime falseBranch falseTy env₄ →
        PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy) →
        EnvJoin env₃ env₄ env₅ →
        EnvJoinSameShape env₃ env₅ →
        EnvJoinSameShape env₄ env₅ →
        WellFormedTy env₅ joinTy lifetime →
        ContainedBorrowsWellFormed env₅ →
        Coherent env₅ →
        Linearizable env₅ →
        BorrowSafeEnv env₅ →
        TyBorrowSafeAgainstEnv env₅ joinTy →
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
    join happens.  The mirror-image rule (diverging *true* branch) is
    omitted: place the diverging branch in `else` position. -/
    | iteDiverging {env₁ env₂ env₃ env₄ : Env} {typing : StoreTyping}
        {lifetime : Lifetime} {condition trueBranch falseBranch : Term}
        {trueTy falseTy : Ty} :
        TermTyping env₁ typing lifetime condition .bool env₂ →
        TermTyping env₂ typing lifetime trueBranch trueTy env₃ →
        TermTyping env₂ typing lifetime falseBranch falseTy env₄ →
        falseBranch.Diverges →
        TermTyping env₁ typing lifetime
          (.ite condition trueBranch falseBranch) trueTy env₃
    /-- T-While (beyond the paper, which is loop-free): strict-invariant
    while loop.

    The body is scoped under `bodyLifetime` like a block and must restore
    the loop-entry environment exactly (`env₃.dropLifetime bodyLifetime =
    env₁`): the back edge then re-enters the same derivation verbatim, so no
    environment join or fixpoint is needed.  This deliberately
    under-approximates rustc, whose NLL fixpoint can widen borrow sets
    around the back edge (e.g. a body reassigning an outer `&mut` to a
    different target); such loops are rejected here.  The loop exits when
    the condition evaluates to `false`, so the result environment is the
    post-condition environment and the result type is `unit`. -/
    | whileLoop {env₁ env₂ env₃ : Env} {typing : StoreTyping}
        {lifetime bodyLifetime : Lifetime} {condition body : Term}
        {bodyTy : Ty} :
        LifetimeChild lifetime bodyLifetime →
        TermTyping env₁ typing lifetime condition .bool env₂ →
        TermTyping env₂ typing bodyLifetime body bodyTy env₃ →
        WellFormedTy env₃ bodyTy lifetime →
        env₃.dropLifetime bodyLifetime = env₁ →
        TermTyping env₁ typing lifetime
          (.whileLoop bodyLifetime condition body) .unit env₂
    /-- T-WhileDiv: while loop with a diverging body — the loop-body
    counterpart of `T-IfDiv`.  A body ending in `panic!()` never reaches the
    back edge, so no re-entry invariant is required; the body is still fully
    type- and borrow-checked.  This is what `ast_copier` relies on when it
    rebuilds a truncated loop body as `while c { …; panic!() }`. -/
    | whileLoopDiverging {env₁ env₂ env₃ : Env} {typing : StoreTyping}
        {lifetime bodyLifetime : Lifetime} {condition body : Term}
        {bodyTy : Ty} :
        LifetimeChild lifetime bodyLifetime →
        TermTyping env₁ typing lifetime condition .bool env₂ →
        TermTyping env₂ typing bodyLifetime body bodyTy env₃ →
        body.Diverges →
        TermTyping env₁ typing lifetime
          (.whileLoop bodyLifetime condition body) .unit env₂
    /-- T-WhileJoin: NLL-style loop invariant.

    The loop is checked against an invariant environment `envInv` solving the
    fixpoint equation `envInv = env₁ ⊔ envBack`: the condition is typed from
    the invariant, and the back edge (post-body, after the body-scope drop)
    must be exactly the `envBack` that closes the join.  This accepts loops
    that widen borrow target lists across iterations (e.g. re-pointing an
    outer `&mut` inside the body), which the strict rule `T-While` rejects.

    Obligations follow the `T-If` convention: joins merge borrow target
    lists, so shape agreement and the well-formedness/borrow-safety kit for
    the join are rule-carried.  Runtime entry/back-edge states transport
    into the invariant via `EnvSameShapeStrengthening.safe`, exactly as in
    the `T-If` preservation argument.

    The final two premises re-type the condition and body from the
    *entry-side* environments.  In real Rust this is implied: per-code
    borrow checking is monotone under removing loans, so anything that
    checks at the widened loop-head state also checks at the entry state.
    In this calculus that implication is genuinely unprovable — borrow
    types carry their pointee information in the target lists, so
    shrinking a target list can make a dereference typeless rather than
    merely less constrained (`Examples/ThinningFalse.lean`) — so the
    monotonicity fact is carried as rule premises instead.  The
    conservative extractor's transport relies on them: a truncated loop
    re-rooted at the loop's position reuses the entry-side derivations
    verbatim. -/
    | whileLoopJoin {env₁ envBack envInv env₂ envEntry₂ env₃ envEntry₃ : Env}
        {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
        {condition body : Term} {bodyTy bodyEntryTy : Ty} :
        LifetimeChild lifetime bodyLifetime →
        EnvJoin env₁ envBack envInv →
        EnvJoinSameShape env₁ envInv →
        EnvJoinSameShape envBack envInv →
        ContainedBorrowsWellFormed envInv →
        Coherent envInv →
        Linearizable envInv →
        BorrowSafeEnv envInv →
        TermTyping envInv typing lifetime condition .bool env₂ →
        TermTyping env₂ typing bodyLifetime body bodyTy env₃ →
        WellFormedTy env₃ bodyTy lifetime →
        env₃.dropLifetime bodyLifetime = envBack →
        TermTyping env₁ typing lifetime condition .bool envEntry₂ →
        TermTyping envEntry₂ typing bodyLifetime body bodyEntryTy envEntry₃ →
        TermTyping env₁ typing lifetime
          (.whileLoop bodyLifetime condition body) .unit env₂

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
