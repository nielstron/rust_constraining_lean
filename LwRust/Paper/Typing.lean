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
  | immBorrow {targets : List LVal} {pointee : Ty} :
      CopyTy (.borrow false targets pointee)

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
  | borrow {mutable : Bool} {pointee : Ty}
      {leftTargets rightTargets : List LVal} :
      leftTargets.Subset rightTargets →
      PartialTyStrengthens (.ty (.borrow mutable leftTargets pointee))
        (.ty (.borrow mutable rightTargets pointee))
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

/-- Base variable of an lvalue. -/
def LVal.base : LVal → Name
  | .var x => x
  | .deref lv => LVal.base lv

/-- Variables occurring in live loans of a full type.

For borrow types, only the target list contributes live loan variables.  The
carried pointee type is an annotation used for dereference typing, not another
owned value contained by the reference.
-/
def Ty.vars : Ty → List Name
  | .unit => []
  | .int => []
  | .bool => []
  | .borrow _ targets _pointee => targets.map LVal.base
  | .box inner => Ty.vars inner

/-- Variables occurring anywhere in full-type annotations, including borrow
pointee annotations. -/
def Ty.allVars : Ty → List Name
  | .unit => []
  | .int => []
  | .bool => []
  | .borrow _ targets pointee => targets.map LVal.base ++ Ty.allVars pointee
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
    /--
    T-LvBor.  The borrow type carries the pointee shape explicitly, while the
    target list still provides the typing/lifetime evidence for reachable
    dereferences.
    -/
    | borrow {env : Env} {lv : LVal} {mutable : Bool} {targets : List LVal}
        {pointee : Ty} {borrowLifetime targetLifetime : Lifetime} :
        LValTyping env lv (.ty (.borrow mutable targets pointee)) borrowLifetime →
        LValTargetsTyping env targets (.ty pointee) targetLifetime →
        LValTyping env (.deref lv) (.ty pointee) targetLifetime

  /--
  The paper premise `Γ ⊢ u : ⟨⋃ᵢ Tᵢ⟩^(⋂ᵢ mᵢ)` for a finite, non-empty list
  of borrowed lvals.
  -/
  inductive LValTargetsTyping : Env → List LVal → PartialTy → Lifetime → Prop where
    /--
    Empty target sets are only useful for pointee types whose annotations mention
    no program variables.  They model unreachable borrows such as `&mut[int] []`
    without letting `&mut[&y] []` fabricate access to `y`.
    -/
    | empty {env : Env} {ty : Ty} :
        Ty.allVars ty = [] →
        LValTargetsTyping env [] (.ty ty) Lifetime.root
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
    | .whileLoop _ condition body =>
        Term.Mentions x condition ∨ Term.Mentions x body
    | .whileCond _ conditionInFlight condition body =>
        Term.Mentions x conditionInFlight ∨ Term.Mentions x condition ∨
          Term.Mentions x body
    | .whileBody _ bodyInFlight condition body =>
        Term.Mentions x bodyInFlight ∨ Term.Mentions x condition ∨
          Term.Mentions x body

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
    | .whileLoop _ condition body =>
        Term.names condition ∪ Term.names body
    | .whileCond _ conditionInFlight condition body =>
        Term.names conditionInFlight ∪ Term.names condition ∪ Term.names body
    | .whileBody _ bodyInFlight condition body =>
        Term.names bodyInFlight ∪ Term.names condition ∪ Term.names body

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
    ?whileLoop ?whileCond ?whileBody ?nil ?cons term
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
  case whileLoop =>
    intro _bodyLifetime _condition _body ihCondition ihBody hmentions
    rcases hmentions with hcondition | hbody
    · exact Finset.mem_union.mpr (Or.inl (ihCondition hcondition))
    · exact Finset.mem_union.mpr (Or.inr (ihBody hbody))
  case whileCond =>
    intro _bodyLifetime _conditionInFlight _condition _body ihInFlight
      ihCondition ihBody hmentions
    rcases hmentions with hinFlight | hcondition | hbody
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl (ihInFlight hinFlight))))
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inr (ihCondition hcondition))))
    · exact Finset.mem_union.mpr (Or.inr (ihBody hbody))
  case whileBody =>
    intro _bodyLifetime _bodyInFlight _condition _body ihInFlight
      ihCondition ihBody hmentions
    rcases hmentions with hinFlight | hcondition | hbody
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl (ihInFlight hinFlight))))
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inr (ihCondition hcondition))))
    · exact Finset.mem_union.mpr (Or.inr (ihBody hbody))
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
    | borrow mutable targets pointee =>
        intro h
        exact List.mem_append_left _ h
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
keeping the `mutable` flag and carried pointee shape. -/
def Ty.sameShape : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .bool, .bool => True
  | .borrow m₁ _ p₁, .borrow m₂ _ p₂ => m₁ = m₂ ∧ Ty.sameShape p₁ p₂
  | .box t₁, .box t₂ => Ty.sameShape t₁ t₂
  | _, _ => False

/-- Structural shape equality of partial types. -/
def PartialTy.sameShape : PartialTy → PartialTy → Prop
  | .ty t₁, .ty t₂ => Ty.sameShape t₁ t₂
  | .box p₁, .box p₂ => PartialTy.sameShape p₁ p₂
  | .undef t₁, .undef t₂ => Ty.sameShape t₁ t₂
  | _, _ => False

/-- Finer type equivalence than `sameShape`: structural, and borrow target
lists must be subset-equivalent (same set).  The carried borrow pointee
annotation is syntactic in this equivalence, matching `W-Bor`: the target list
may grow/shrink extensionally, but the dereference annotation is not rewritten
inside the borrow constructor. -/
def Ty.eqv : Ty → Ty → Prop
  | .unit, .unit => True
  | .int, .int => True
  | .bool, .bool => True
  | .borrow m₁ t₁ p₁, .borrow m₂ t₂ p₂ =>
      m₁ = m₂ ∧ t₁ ⊆ t₂ ∧ t₂ ⊆ t₁ ∧ p₁ = p₂
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

notation:max "&mut[" pointee "] " targets:max => Ty.borrow true targets pointee
notation:max "&[" pointee "] " targets:max => Ty.borrow false targets pointee

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
    {pointee : Ty} {target : LVal} :
    PartialTyContains partialTy (.borrow mutable targets pointee) →
    target ∈ targets →
    LVal.base target ∈ PartialTy.allVars partialTy := by
  intro hcontains htarget
  suffices hgeneral :
      ∀ {partialTy : PartialTy} {needle : Ty},
        PartialTyContains partialTy needle →
        ∀ {mutable : Bool} {targets : List LVal} {pointee : Ty}
          {target : LVal},
          needle = .borrow mutable targets pointee →
          target ∈ targets →
          LVal.base target ∈ PartialTy.allVars partialTy by
    exact hgeneral hcontains rfl htarget
  intro partialTy needle hcontains
  induction hcontains with
  | here =>
      intro mutable targets pointee target hneedle htarget
      subst hneedle
      simp [PartialTy.allVars, Ty.allVars, List.mem_map]
      exact Or.inl ⟨target, htarget, rfl⟩
  | tyBox _hinner ih =>
      intro mutable targets pointee target hneedle htarget
      simpa [PartialTy.allVars, Ty.allVars] using
        ih hneedle htarget
  | box _hinner ih =>
      intro mutable targets pointee target hneedle htarget
      simpa [PartialTy.allVars] using ih hneedle htarget

def EnvContains (env : Env) (x : Name) (ty : Ty) : Prop :=
  ∃ slot, env.slotAt x = some slot ∧ PartialTyContains slot.ty ty

notation:50 env:51 " ⊢ " x:51 " ↝ " ty:51 => EnvContains env x ty

/--
Coherence obligations for adding a fresh full-typed slot.

This is currently carried by the declaration/result rules for the parts of the
metatheory that still reason through target-list typings.  The refactored
borrow type carries a pointee annotation separately, so these obligations should
become candidates for removal as those proofs are simplified.
-/
structure FreshUpdateCoherenceObligations
    (env : Env) (x : Name) (ty : Ty) (lifetime : Lifetime) : Prop where
  old_root_transport
    {lv : LVal} {mutable : Bool} {targets : List LVal} {pointee : Ty}
    {borrowLifetime : Lifetime} :
    LVal.base lv ≠ x →
    LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
      lv (.ty (.borrow mutable targets pointee)) borrowLifetime →
    ∃ oldBorrowLifetime,
      LValTyping env lv (.ty (.borrow mutable targets pointee)) oldBorrowLifetime
  fresh_root_coherent
    {lv : LVal} {mutable : Bool} {targets : List LVal} {pointee : Ty}
    {borrowLifetime : Lifetime} :
    LVal.base lv = x →
    LValTyping (env.update x { ty := .ty ty, lifetime := lifetime })
      lv (.ty (.borrow mutable targets pointee)) borrowLifetime →
    ∃ targetLifetime,
      LValTargetsTyping
        (env.update x { ty := .ty ty, lifetime := lifetime })
        targets (.ty pointee) targetLifetime

/--
Rank and RHS-fan-out safety obligation for assignment writes.

Every borrow edge installed from the RHS type must point to a lower-ranked base
in the pre-write environment.  Additionally, if a write fan-out duplicates RHS
borrow targets into two result roots, any resulting mutable-borrow conflict must
be within one root.  This is the explicit rule-side replacement for assuming
that all environment writes preserve linearizability and borrow safety.
-/
def EnvWriteRhsBorrowTargetsBelow (φ : Name → Nat) (result : Env) (rhsTy : Ty) : Prop :=
  (∀ x slot mutable targets pointee target,
      result.slotAt x = some slot →
      PartialTyContains slot.ty (.borrow mutable targets pointee) →
      target ∈ targets →
      (∃ rhsMutable rhsTargets rhsPointee,
        PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets rhsPointee) ∧
          target ∈ rhsTargets) →
      φ (LVal.base target) < φ x) ∧
  (∀ x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther,
      result ⊢ x ↝ (.borrow true targetsMutable pointeeMutable) →
      result ⊢ y ↝ (.borrow mutable targetsOther pointeeOther) →
      targetMutable ∈ targetsMutable →
      targetOther ∈ targetsOther →
      targetMutable ⋈ targetOther →
      (∃ rhsMutable rhsTargets rhsPointee,
        PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets rhsPointee) ∧
          targetMutable ∈ rhsTargets) →
      (∃ rhsMutable rhsTargets rhsPointee,
        PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets rhsPointee) ∧
          targetOther ∈ rhsTargets) →
      x = y)

/-- Definition 3.16, `readProhibited(Γ, w)`. -/
def ReadProhibited (env : Env) (lv : LVal) : Prop :=
  ∃ x targets pointee target,
    env ⊢ x ↝ (.borrow true targets pointee) ∧
    target ∈ targets ∧
    target ⋈ lv

/-- Definition 3.17, `writeProhibited(Γ, w)`. -/
def WriteProhibited (env : Env) (lv : LVal) : Prop :=
  ReadProhibited env lv ∨
  ∃ x targets pointee target,
    env ⊢ x ↝ (.borrow false targets pointee) ∧
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
  | borrow {env : Env} {lv : LVal} {targets : List LVal} {pointee : Ty}
      {lifetime : Lifetime} :
      LValTyping env lv (.ty (.borrow true targets pointee)) lifetime →
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
  ∀ {mutable targets pointee},
    PartialTyContains partialTy (.borrow mutable targets pointee) →
    BorrowTargetsWellFormedInSlot env slotLifetime targets

/--
Minimal lifetime obligation for assignment writes.

This is the strictly-weaker replacement for carrying the broad
`ContainedBorrowsWellFormed` of the write result on `T-Assign`: only the borrow
edges *installed from the RHS type* must be well formed against the slot they are
injected into.  Each RHS-origin borrow target appearing in a result slot must
outlive *that slot* (its pointee typeable with a lifetime `≤` the slot lifetime,
plus the base-slot survival of Definition 4.8(i)).

This is exactly what the broad result CBWF demands of the RHS-origin borrows; the
old-origin borrows are *derived* from `ContainedBorrowsWellFormed` of the
pre-write environment via the borrow-invariance keystone.  It is genuinely needed
(and not derivable from `WellFormedTy env₂ rhsTy targetLifetime`): a write through
a multi-target borrow `&mut[x,z]` whose targets have different lifetimes fans the
RHS into both slots, but `targetLifetime` is only the *intersection* of the
targets' lifetimes, so it cannot bound the RHS by the longer-lived slot's
lifetime — see the deviation note in the README and the `example` below the rule.
This mirrors `EnvWriteRhsBorrowTargetsBelow`'s first conjunct, with a lifetime
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
  ∀ x slot mutable targets pointee,
    env.slotAt x = some slot →
    env ⊢ x ↝ (Ty.borrow mutable targets pointee) →
    BorrowTargetsWellFormedInSlot env slot.lifetime targets

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
  ∀ lv mutable targets pointee borrowLifetime,
    LValTyping env lv (.ty (.borrow mutable targets pointee)) borrowLifetime →
    ∃ lifetime, LValTargetsTyping env targets (.ty pointee) lifetime

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
  ∀ x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther,
    env ⊢ x ↝ (.borrow true targetsMutable pointeeMutable) →
    env ⊢ y ↝ (Ty.borrow mutable targetsOther pointeeOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    x = y

/-- A result type is borrow-safe against an environment when installing it as a
new root would introduce no borrow-target conflict with any existing root. -/
def TyBorrowSafeAgainstEnv (env : Env) (ty : Ty) : Prop :=
  (∀ targetsMutable mutable targetsOther pointeeMutable pointeeOther x
      targetMutable targetOther,
    PartialTyContains (.ty ty) (.borrow true targetsMutable pointeeMutable) →
    env ⊢ x ↝ Ty.borrow mutable targetsOther pointeeOther →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False) ∧
  (∀ x targetsMutable mutable targetsOther pointeeMutable pointeeOther
      targetMutable targetOther,
    env ⊢ x ↝ Ty.borrow true targetsMutable pointeeMutable →
    PartialTyContains (.ty ty) (.borrow mutable targetsOther pointeeOther) →
    targetMutable ∈ targetsMutable →
    targetOther ∈ targetsOther →
    targetMutable ⋈ targetOther →
    False)

/-- A type that contains no borrow type anywhere. -/
def TyBorrowFree (ty : Ty) : Prop :=
  ∀ mutable targets pointee,
    ¬ PartialTyContains (.ty ty) (.borrow mutable targets pointee)

def PartialTyBorrowFree (ty : PartialTy) : Prop :=
  ∀ mutable targets pointee,
    ¬ PartialTyContains ty (.borrow mutable targets pointee)

/-- A type whose contained borrows claim no variable names anywhere in their
target annotations.  Carried by `T-Missing`: a placeholder typed at `&mut[int]
[]` claims no loan on any existing place, while `&mut[&[int] [x]] []` is not
loan-free because the unreachable annotation would still mention `x`. -/
def TyLoanFree (ty : Ty) : Prop :=
  Ty.allVars ty = []

def PartialTyLoanFree (ty : PartialTy) : Prop :=
  PartialTy.allVars ty = []

theorem PartialTyLoanFree.empty_targets {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} {pointee : Ty} :
    PartialTyLoanFree partialTy →
    PartialTyContains partialTy (.borrow mutable targets pointee) →
    targets = [] := by
  intro hfree hcontains
  cases targets with
  | nil => rfl
  | cons target rest =>
      have hmem : LVal.base target ∈ PartialTy.allVars partialTy :=
        PartialTyContains.borrow_target_mem_allVars hcontains (by simp)
      rw [hfree] at hmem
      cases hmem

theorem TyLoanFree.empty_targets {ty : Ty}
    {mutable : Bool} {targets : List LVal} {pointee : Ty} :
    TyLoanFree ty →
    PartialTyContains (.ty ty) (.borrow mutable targets pointee) →
    targets = [] := by
  intro hfree hcontains
  exact PartialTyLoanFree.empty_targets
    (partialTy := .ty ty)
    (by simpa [TyLoanFree, PartialTyLoanFree, PartialTy.allVars] using hfree)
    hcontains

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
      {pointee : Ty} {lifetime : Lifetime} :
      BorrowTargetsWellFormed env targets lifetime →
      WellFormedTy env (.borrow mutable targets pointee) lifetime
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
      {leftPointee rightPointee : Ty} :
      ShapeCompatible env (.ty leftPointee) (.ty rightPointee) →
      ShapeCompatible env (.ty (.borrow mutable leftTargets leftPointee))
        (.ty (.borrow mutable rightTargets rightPointee))
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
        {targets : List LVal} {oldPointee ty : Ty} :
        WriteBorrowTargets (rank + 1) env₁ path targets ty env₂ →
        UpdateAtPath rank env₁ (() :: path) (.ty (.borrow true targets oldPointee)) ty
          env₂ (.ty (.borrow true targets oldPointee))

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
    (fun {env₁ env₂ rank path targets oldPointee ty} _htargets ih hfinite =>
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
        TermTyping env typing lifetime (.borrow true lv) (.borrow true [lv] ty) env
    /-- T-ImmBorrow. -/
    | immBorrow {env : Env} {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
        {lv : LVal} {ty : Ty} :
        LValTyping env lv (.ty ty) valueLifetime →
        ¬ ReadProhibited env lv →
        TermTyping env typing lifetime (.borrow false lv) (.borrow false [lv] ty) env
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
    /-- T-While: NLL-style loop invariant.

    The loop is checked against an invariant environment `envInv` solving the
    fixpoint equation `envInv = env₁ ⊔ envBack`: the condition is typed from
    the invariant, and the back edge (post-body, after the body-scope drop)
    must be exactly the `envBack` that closes the join.  This accepts loops
    that widen borrow target lists across iterations (e.g. re-pointing an
    outer `&mut` inside the body).

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
    | whileLoop {env₁ envBack envInv env₂ envEntry₂ env₃ envEntry₃ : Env}
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
        LoopInvariantNameFresh env₁ envInv condition body →
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
    (fun _hrhs _hlhs _hshape _hwellTy hwrite _hrank _hcoherence
        _hcontained _hnotWrite ih hfinite =>
      EnvWrite.finiteSupport hwrite (ih hfinite))
    (fun _hlhs _hfresh _htypeFresh _hnotTy _hstoreFresh _hrhs
        _hnotMentions henvEq _hcopyL _hcopyR _hshape ihLhs ihRhs hfinite => by
      rw [henvEq]
      exact (ihRhs (ihLhs hfinite).update).erase)
    (fun _hcondition _htrue _hfalse _htyJoin henvJoin _hsameLeft
        _hsameRight _hwellTy _hcoherent _hlinear _hborrowSafe _htySafe
        ihCondition ihTrue _ihFalse hfinite =>
      EnvJoin.finiteSupport_left henvJoin (ihTrue (ihCondition hfinite)))
    (fun _hcondition _htrue _hfalse _hdiverges ihCondition ihTrue
        _ihFalse hfinite =>
      ihTrue (ihCondition hfinite))
    (fun _hchild _hcondition _hbody _hdiverges ihCondition _ihBody hfinite =>
      ihCondition hfinite)
    (fun _hchild hjoin _hsameEntry _hsameBack _hcontained _hcoherent
        _hlinear _hborrowSafe _hnameFresh _hcondition _hbody _hwellTy
        _hback _hentryCondition _hentryBody ihCondition _ihBody
        _ihEntryCondition _ihEntryBody hfinite =>
      ihCondition (EnvJoin.finiteSupport_left hjoin hfinite))
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
  intro hsafe x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
    targetMutable targetOther hx hy htargetMutable htargetOther hconflict
  rcases hx with ⟨xSlot, hxSlot, hxContains⟩
  rcases hy with ⟨ySlot, hySlot, hyContains⟩
  have hxOrig : env ⊢ x ↝ (.borrow true targetsMutable pointeeMutable) := by
    by_cases hxGhost : x = ghost
    · subst hxGhost
      simp [Env.erase] at hxSlot
    · exact ⟨xSlot, by simpa [Env.erase, hxGhost] using hxSlot, hxContains⟩
  have hyOrig : env ⊢ y ↝ (Ty.borrow mutable targetsOther pointeeOther) := by
    by_cases hyGhost : y = ghost
    · subst hyGhost
      simp [Env.erase] at hySlot
    · exact ⟨ySlot, by simpa [Env.erase, hyGhost] using hySlot, hyContains⟩
  exact hsafe x y mutable targetsMutable targetsOther pointeeMutable pointeeOther
    targetMutable targetOther
    hxOrig hyOrig htargetMutable htargetOther hconflict

end Paper
end LwRust
