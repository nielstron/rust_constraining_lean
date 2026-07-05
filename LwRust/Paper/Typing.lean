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

/-- Definition 3.6, `copy(T)`. -/
inductive CopyTy : Ty → Prop where
  | unit :
      CopyTy .unit
  | int :
      CopyTy .int
  | immBorrow {target : LVal} :
      CopyTy (.borrow false target)

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

/-- Base variable of an lvalue. -/
def LVal.base : LVal → Name
  | .var x => x
  | .deref lv => LVal.base lv

/-- Variables occurring in live loans of a full type. -/
def Ty.vars : Ty → List Name
  | .unit => []
  | .int => []
  | .borrow _ target => [LVal.base target]
  | .box inner => Ty.vars inner

/-- Variables occurring anywhere in full-type annotations. -/
def Ty.allVars : Ty → List Name
  | .unit => []
  | .int => []
  | .borrow _ target => [LVal.base target]
  | .box inner => Ty.allVars inner

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
  /-- T-LvBor for single-target borrows. -/
  | borrow {env : Env} {lv target : LVal} {mutable : Bool}
      {borrowLifetime targetLifetime : Lifetime} {targetTy : Ty} :
      LValTyping env lv (.ty (.borrow mutable target)) borrowLifetime →
      LValTyping env target (.ty targetTy) targetLifetime →
      LValTyping env (.deref lv) (.ty targetTy) targetLifetime

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

/-- Structural shape equality of full types, ignoring borrow *target lists* but
keeping the `mutable` flag. -/
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

/-- Finer type equivalence than `sameShape`: structural, and borrow targets
must be equal. -/
def Ty.eqv : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .borrow m₁ t₁, .borrow m₂ t₂ =>
      m₁ = m₂ ∧ t₁ = t₂
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
    {partialTy : PartialTy} {mutable : Bool} {target : LVal} :
    PartialTyContains partialTy (.borrow mutable target) →
    LVal.base target ∈ PartialTy.allVars partialTy := by
  intro hcontains
  suffices hgeneral :
      ∀ {partialTy : PartialTy} {needle : Ty},
        PartialTyContains partialTy needle →
        ∀ {mutable : Bool} {target : LVal},
          needle = .borrow mutable target →
          LVal.base target ∈ PartialTy.allVars partialTy by
    exact hgeneral hcontains rfl
  intro partialTy needle hcontains
  induction hcontains with
  | here =>
      intro mutable target hneedle
      subst hneedle
      simp [PartialTy.allVars, Ty.allVars]
  | tyBox _hinner ih =>
      intro mutable target hneedle
      simpa [PartialTy.allVars, Ty.allVars] using
        ih hneedle
  | box _hinner ih =>
      intro mutable target hneedle
      simpa [PartialTy.allVars] using ih hneedle

def EnvContains (env : Env) (x : Name) (ty : Ty) : Prop :=
  ∃ slot, env.slotAt x = some slot ∧ PartialTyContains slot.ty ty

notation:50 env:51 " ⊢ " x:51 " ↝ " ty:51 => EnvContains env x ty

/-- Definition 3.16, `readProhibited(Γ, w)`. -/
def ReadProhibited (env : Env) (lv : LVal) : Prop :=
  ∃ x target,
    env ⊢ x ↝ (.borrow true target) ∧
    target ⋈ lv

/-- Definition 3.17, `writeProhibited(Γ, w)`. -/
def WriteProhibited (env : Env) (lv : LVal) : Prop :=
  ReadProhibited env lv ∨
  ∃ x target,
    env ⊢ x ↝ (.borrow false target) ∧
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
  | borrow {env : Env} {lv target : LVal} {lifetime : Lifetime} :
      LValTyping env lv (.ty (.borrow true target)) lifetime →
      Mutable env target →
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

/-- All borrow targets are well formed for the requested lifetime. -/
inductive BorrowTargetsWellFormed : Env → LVal → Lifetime → Prop where
  | intro {env : Env} {target : LVal} {lifetime : Lifetime} :
      (∃ targetTy targetLifetime,
        LValTyping env target (.ty targetTy) targetLifetime ∧
          LifetimeOutlives targetLifetime lifetime ∧
          LValBaseOutlives env target lifetime) →
      BorrowTargetsWellFormed env target lifetime

/-- Definition 4.8(i), the borrow invariant for a borrow contained in one slot. -/
def BorrowTargetsWellFormedInSlot
    (env : Env) (slotLifetime : Lifetime) (target : LVal) : Prop :=
  ∃ targetTy targetLifetime,
    LValTyping env target (.ty targetTy) targetLifetime ∧
      targetLifetime ≤ slotLifetime ∧
      LValBaseOutlives env target slotLifetime

/--
Weaker borrow-target invariant for stale loan annotations.

A target carried by a type can be a conservative protection token after a move:
the annotation still blocks writes through `ReadProhibited`/`WriteProhibited`,
but a moved-out target is not currently dereferenceable.  The target's base slot
must still survive for the containing loan, but the full target typing needed to
dereference the borrow is conditional on the target being initialized.
-/
def BorrowTargetsWellFormedWhenInitialized
    (env : Env) (target : LVal) (lifetime : Lifetime) : Prop :=
  LValBaseOutlives env target lifetime ∧
    ((∃ targetTy targetLifetime,
      LValTyping env target (.ty targetTy) targetLifetime) →
    ∃ targetTy targetLifetime,
      LValTyping env target (.ty targetTy) targetLifetime ∧
        targetLifetime ≤ lifetime ∧
        LValBaseOutlives env target lifetime)

/-- Slot-local version of `BorrowTargetsWellFormedWhenInitialized`. -/
def BorrowTargetsWellFormedInSlotWhenInitialized
    (env : Env) (slotLifetime : Lifetime) (target : LVal) : Prop :=
  BorrowTargetsWellFormedWhenInitialized env target slotLifetime

/-- Slot-local borrow invariant for a partial type. -/
def PartialTyBorrowsWellFormedInSlot
    (env : Env) (slotLifetime : Lifetime) (partialTy : PartialTy) : Prop :=
  ∀ {mutable target},
    PartialTyContains partialTy (.borrow mutable target) →
    BorrowTargetsWellFormedInSlot env slotLifetime target

/-- Slot-local weak borrow invariant for a partial type. -/
def PartialTyBorrowsWellFormedInSlotWhenInitialized
    (env : Env) (slotLifetime : Lifetime) (partialTy : PartialTy) : Prop :=
  ∀ {mutable target},
    PartialTyContains partialTy (.borrow mutable target) →
    BorrowTargetsWellFormedInSlotWhenInitialized env slotLifetime target

/-- Weak borrow invariant for a full type. -/
def TyBorrowsWellFormedWhenInitialized
    (env : Env) (ty : Ty) (lifetime : Lifetime) : Prop :=
  ∀ {mutable target},
    PartialTyContains (.ty ty) (.borrow mutable target) →
    BorrowTargetsWellFormedWhenInitialized env target lifetime

/-- Every borrow contained in every environment slot has well-formed targets. -/
def ContainedBorrowsWellFormed (env : Env) : Prop :=
  ∀ x slot mutable target,
    env.slotAt x = some slot →
    env ⊢ x ↝ (Ty.borrow mutable target) →
    BorrowTargetsWellFormedInSlot env slot.lifetime target

/--
Every borrow contained in every environment slot has well-formed targets when
those targets are currently initialized.
-/
def ContainedBorrowsWellFormedWhenInitialized (env : Env) : Prop :=
  ∀ x slot mutable target,
    env.slotAt x = some slot →
    env ⊢ x ↝ (Ty.borrow mutable target) →
    BorrowTargetsWellFormedInSlotWhenInitialized env slot.lifetime target

/-- Definition 4.8(ii). Every environment slot lives at least as long as `lifetime`. -/
def EnvSlotsOutlive (env : Env) (lifetime : Lifetime) : Prop :=
  ∀ x slot,
    env.slotAt x = some slot →
    slot.lifetime ≤ lifetime

/--
Weaker environment invariant that permits stale loan annotations while keeping
their base slots live as conservative protection tokens.
-/
def WellFormedEnvWhenInitialized (env : Env) (lifetime : Lifetime) : Prop :=
  ContainedBorrowsWellFormedWhenInitialized env ∧
    EnvSlotsOutlive env lifetime

/-- Definition 4.8, well-formed environment. -/
def WellFormedEnv (env : Env) (lifetime : Lifetime) : Prop :=
  ContainedBorrowsWellFormed env ∧ EnvSlotsOutlive env lifetime

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
  ∀ x y mutable targetMutable targetOther,
    env ⊢ x ↝ (.borrow true targetMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetOther) →
    targetMutable ⋈ targetOther →
    x = y

/-- Slots reachable from `root` through environment-contained mutable borrow
annotations. -/
inductive ChainGuard (env : Env) (root : Name) : Name → Prop where
  | base : ChainGuard env root root
  | step {z y : Name} {g : LVal} :
      ChainGuard env root z →
      env ⊢ z ↝ (.borrow true g) →
      LVal.base g = y →
      ChainGuard env root y

/-- A result type is borrow-safe against an environment when installing it as a
new root would introduce no borrow-target conflict with any existing root. -/
def TyBorrowSafeAgainstEnv (env : Env) (ty : Ty) : Prop :=
  (∀ targetMutable mutable targetOther x,
    PartialTyContains (.ty ty) (.borrow true targetMutable) →
    env ⊢ x ↝ Ty.borrow mutable targetOther →
    targetMutable ⋈ targetOther →
    False) ∧
  (∀ x targetMutable mutable targetOther,
    env ⊢ x ↝ Ty.borrow true targetMutable →
    PartialTyContains (.ty ty) (.borrow mutable targetOther) →
    targetMutable ⋈ targetOther →
    False)

/-- A type that contains no borrow type anywhere. -/
def TyBorrowFree (ty : Ty) : Prop :=
  ∀ mutable target, ¬ PartialTyContains (.ty ty) (.borrow mutable target)

def PartialTyBorrowFree (ty : PartialTy) : Prop :=
  ∀ mutable target, ¬ PartialTyContains ty (.borrow mutable target)

/-- A type whose contained borrows claim no loans. -/
def TyLoanFree (ty : Ty) : Prop :=
  TyBorrowFree ty

def PartialTyLoanFree (ty : PartialTy) : Prop :=
  PartialTyBorrowFree ty

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
  /-- L-Borrow. -/
  | borrow {env : Env} {mutable : Bool} {target : LVal}
      {lifetime : Lifetime} :
      BorrowTargetsWellFormed env target lifetime →
      WellFormedTy env (.borrow mutable target) lifetime
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
  | borrow {env : Env} {mutable : Bool} {target : LVal}
      {lifetime : Lifetime} :
      BorrowTargetsWellFormedWhenInitialized env target lifetime →
      WellFormedTyWhenInitialized env (.borrow mutable target) lifetime
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
  /-- S-Box for fully initialized owner types. -/
  | tyBox {env : Env} {left right : Ty} :
      ShapeCompatible env (.ty left) (.ty right) →
      ShapeCompatible env (.ty (.box left)) (.ty (.box right))
  /-- S-Box. -/
  | box {env : Env} {left right : PartialTy} :
      ShapeCompatible env left right →
      ShapeCompatible env (.box left) (.box right)
  /-- S-Bor.  Borrow shapes are compatible when their target output types
  are shape-compatible in the current environment. -/
  | borrow {env : Env} {mutable : Bool} {leftTarget rightTarget : LVal}
      {leftTy rightTy : Ty} :
      (∃ leftLifetime, LValTyping env leftTarget (.ty leftTy) leftLifetime) →
      (∃ rightLifetime, LValTyping env rightTarget (.ty rightTy) rightLifetime) →
      ShapeCompatible env (.ty leftTy) (.ty rightTy) →
      ShapeCompatible env (.ty (.borrow mutable leftTarget))
        (.ty (.borrow mutable rightTarget))
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

/-- Re-wrap an updated box element, preserving full-box shape when possible. -/
def partialTyRebox : PartialTy → PartialTy
  | .ty inner => .ty (.box inner)
  | inner => .box inner

mutual
  /-- Definition 3.23, strong update along an lvalue path. -/
  inductive UpdateAtPath : Env → List Unit → PartialTy → Ty → Env → PartialTy → Prop where
    | strong {env : Env} {old : PartialTy} {ty : Ty} :
        UpdateAtPath env [] old ty env (.ty ty)
    | box {env₁ env₂ : Env} {path : List Unit}
        {inner updatedInner : PartialTy} {ty : Ty} :
        UpdateAtPath env₁ path inner ty env₂ updatedInner →
        UpdateAtPath env₁ (() :: path) (.box inner) ty env₂ (.box updatedInner)
    | boxFull {env₁ env₂ : Env} {path : List Unit}
        {inner : Ty} {updatedInner : PartialTy} {ty : Ty} :
        UpdateAtPath env₁ path (.ty inner) ty env₂ updatedInner →
        UpdateAtPath env₁ (() :: path) (.ty (.box inner)) ty env₂
          (partialTyRebox updatedInner)
    | mutBorrow {env₁ env₂ : Env} {path : List Unit}
        {target : LVal} {ty : Ty} :
        EnvWrite env₁ (prependPath path target) ty env₂ →
        UpdateAtPath env₁ (() :: path) (.ty (.borrow true target)) ty env₂
          (.ty (.borrow true target))

  /-- Definition 3.23, strong environment write. -/
  inductive EnvWrite : Env → LVal → Ty → Env → Prop where
    | intro {env₁ env₂ : Env} {lv : LVal} {slot : EnvSlot}
        {ty : Ty} {updatedTy : PartialTy} :
        env₁.slotAt (LVal.base lv) = some slot →
        UpdateAtPath env₁ (LVal.path lv) slot.ty ty env₂ updatedTy →
        EnvWrite env₁ lv ty
          (env₂.update (LVal.base lv) { slot with ty := updatedTy })
end

theorem EnvWrite.finiteSupport {env result : Env}
    {lv : LVal} {ty : Ty} :
    EnvWrite env lv ty result →
    Env.FiniteSupport env →
    Env.FiniteSupport result := by
  intro hwrite hfinite
  exact EnvWrite.rec
    (motive_1 := fun _path _old _ty result _updated _ =>
      Env.FiniteSupport result)
    (motive_2 := fun _lv _ty result _ =>
      Env.FiniteSupport result)
    (fun {old ty} => hfinite)
    (fun {env₂ path inner updatedInner ty} _hupdate ih => ih)
    (fun {env₂ path inner updatedInner ty} _hupdate ih => ih)
    (fun {env₂ path target ty} _hwrite ih => ih)
    (fun {env₂ lv slot ty updatedTy} _hslot _hupdate ih => ih.update)
    hwrite

/-- Value typing premise `σ ⊢ v : T` from T-Const. -/
inductive ValueTyping : StoreTyping → Value → Ty → Prop where
  | unit {typing : StoreTyping} :
      ValueTyping typing .unit .unit
  | int {typing : StoreTyping} {value : Int} :
      ValueTyping typing (.int value) .int
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
        TermTyping env typing lifetime (.borrow true lv) (.borrow true lv) env
    /-- T-ImmBorrow. -/
    | immBorrow {env : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
        {lv : LVal} {ty : Ty} :
        LValTyping env lv (.ty ty) valueLifetime →
        ¬ ReadProhibited env lv →
        TermTyping env typing lifetime (.borrow false lv) (.borrow false lv) env
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
    /-- T-Declare.

    The paper rule requires `x ∉ dom(Γ₁)`.  The extra `env₂.fresh x` premise
    mechanizes the paper's no-redeclaration intent (Section 5.2 explicitly
    treats redeclaration as not permitted): the literal rule would allow the
    shadow chain `let mut x = (let mut x = t)`, where `x` re-enters the
    environment through the initializer itself.

    The follow-up's T-Block explicitly assumes no redeclaration; `env₂.fresh x`
    is the mechanized form of that premise for initializers that may themselves
    evaluate declarations. -/
    | declare {env₁ env₂ env₃ : Env} {typing : StoreTyping} {lifetime : Lifetime}
        {x : Name} {term : Term} {ty : Ty} :
        env₁.fresh x →
        TermTyping env₁ typing lifetime term ty env₂ →
        env₂.fresh x →
        env₃ = env₂.update x { ty := .ty ty, lifetime := lifetime } →
        TermTyping env₁ typing lifetime (.letMut x term) .unit env₃
    /-- T-Assign.

    The rule checks the final post-write environment at the syntactic
    left-hand side.  Writes through mutable-borrow chains such as `*p = v`
    are intentionally accepted when the post-write environment is not
    write-prohibited at the original left-hand side. -/
    | assign {env₁ env₂ env₃ : Env} {typing : StoreTyping}
        {lifetime targetLifetime : Lifetime} {lhs : LVal}
        {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty} :
        TermTyping env₁ typing lifetime rhs rhsTy env₂ →
        LValTyping env₂ lhs oldTy targetLifetime →
        ShapeCompatible env₂ oldTy (.ty rhsTy) →
        WellFormedTy env₂ rhsTy targetLifetime →
        EnvWrite env₂ lhs rhsTy env₃ →
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
    (fun _hlv _hcopy _hnotRead hfinite => hfinite)
    (fun _hlv _hnotWrite hmove hfinite =>
      EnvMove.finiteSupport hmove hfinite)
    (fun _hlv _hmutable _hnotWrite hfinite => hfinite)
    (fun _hlv _hnotRead hfinite => hfinite)
    (fun _hterm ih hfinite => ih hfinite)
    (fun _hchild _hterms _hwellTy henvEq ih hfinite => by
      rw [henvEq]
      exact (ih hfinite).dropLifetime)
    (fun _hfresh _hterm _hfreshOut henvEq ih hfinite => by
      rw [henvEq]
      exact (ih hfinite).update)
    (fun _hrhs _hlhs _hshape _hwellTy hwrite _hnotWrite ih hfinite =>
      EnvWrite.finiteSupport hwrite (ih hfinite))
    (fun _hterm ih hfinite => ih hfinite)
    (fun _hterm _hrest ihTerm ihRest hfinite =>
      ihRest (ihTerm hfinite))
    htyping

end Paper
end LwRust
