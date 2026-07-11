import Std

/-!
Syntax for the core FR calculus in Figure 1 of `lw_rust.pdf`.
-/

namespace FWRust
namespace Core

abbrev Name := String

/--
Reference lifetime names are paths in the lexical lifetime tree.

This is intentionally a wrapper rather than an abbreviation for `List Nat`, so
we can give lifetimes their own order without changing Lean's existing list
order.
-/
structure Lifetime where
  path : List Nat
  deriving BEq, DecidableEq, Repr

instance : Coe (List Nat) Lifetime where
  coe path := { path := path }

inductive LVal where
  | var (name : Name)
  | deref (operand : LVal)
  deriving BEq, DecidableEq, Repr

/--
Paper Section 2.2's abstract location: a chunk of allocated storage.  The core
semantics names stack-allocated variable locations by variable name and heap
locations by a fresh natural.
-/
inductive Location where
  | var (name : Name)
  | heap (address : Nat)
  deriving BEq, DecidableEq, Repr

mutual
  inductive Ty where
    | unit
    | int
    | borrow (mutable : Bool) (targets : List LVal)
    | box (element : Ty)
    /-- Section 6.1 control-flow extension (Figure 5): Boolean type. -/
    | bool
    deriving BEq, Repr

  inductive PartialTy where
    | ty (type : Ty)
    | box (element : PartialTy)
    | undef (shape : Ty)
    deriving BEq, Repr
end

instance : Coe Ty PartialTy where
  coe := PartialTy.ty

structure Reference where
  location : Location
  owner : Bool
  deriving BEq, DecidableEq, Repr

def Reference.borrowed (ref : Reference) : Reference :=
  { ref with owner := false }

inductive Value where
  | unit
  | int (value : Int)
  | ref (location : Reference)
  /-- Section 6.1 control-flow extension (Figure 5): `true` / `false`. -/
  | bool (value : Bool)
  deriving BEq, DecidableEq, Repr

inductive PartialValue where
  | value (value : Value)
  | undef
  deriving BEq, DecidableEq, Repr

def Lifetime.root : Lifetime := { path := [] }

def Lifetime.contains (outer inner : Lifetime) : Bool :=
  outer.path.isPrefixOf inner.path

inductive Term where
  | block (lifetime : Lifetime) (terms : List Term)
  | letMut (name : Name) (initialiser : Term)
  | assign (lhs : LVal) (rhs : Term)
  | box (operand : Term)
  | borrow (mutable : Bool) (operand : LVal)
  | move (operand : LVal)
  | copy (operand : LVal)
  | val (value : Value)
  /-- Synthetic extractor placeholder, analogous to `ast_copier`'s polymorphic
  `__missing__<T>() -> T`. It is source-like generated syntax and diverges at
  runtime, so it also plays the role of Rust's `panic!()`: a diverging
  expression usable at any (loan-free) type. -/
  | missing
  /-- Section 6.1 control-flow extension (Figure 5): equality comparator and conditional -/
  | eq (lhs rhs : Term)
  | ite (condition trueBranch falseBranch : Term)
  /-- Source while loop.  The body is evaluated in `bodyLifetime`; the two
  constructors below are runtime-only phases that retain pristine copies of
  the condition and body for the next iteration. -/
  | whileLoop (bodyLifetime : Lifetime) (condition body : Term)
  /-- Runtime form while the current condition copy is being evaluated. -/
  | whileCond (bodyLifetime : Lifetime)
      (conditionInFlight condition body : Term)
  /-- Runtime form while the current scoped body copy is being evaluated. -/
  | whileBody (bodyLifetime : Lifetime) (bodyInFlight condition body : Term)
  deriving BEq, Repr

mutual
  /-- Structural size of a term.  This is still useful for the original core
  calculus, but generated `.missing` terms self-loop and therefore do not
  strictly decrease. -/
  def Term.size : Term → Nat
    | .block _ terms => 1 + Term.sizeList terms
    | .letMut _ initialiser => 1 + initialiser.size
    | .assign _ rhs => 1 + rhs.size
    | .box operand => 1 + operand.size
    | .borrow _ _ => 2
    | .move _ => 2
    | .copy _ => 2
    | .val _ => 1
    | .missing => 1
    | .eq lhs rhs => 1 + lhs.size + rhs.size
    | .ite condition trueBranch falseBranch =>
        1 + condition.size + trueBranch.size + falseBranch.size
    | .whileLoop _ condition body => 1 + condition.size + body.size
    | .whileCond _ conditionInFlight condition body =>
        1 + conditionInFlight.size + condition.size + body.size
    | .whileBody _ bodyInFlight condition body =>
        1 + bodyInFlight.size + condition.size + body.size

  def Term.sizeList : List Term → Nat
    | [] => 0
    | term :: rest => term.size + Term.sizeList rest
end

inductive Term.Diverges : Term → Prop where
  | missing : Term.Diverges .missing
  | block {lifetime : Lifetime} {terms : List Term} {term : Term} :
      term ∈ terms →
      Term.Diverges term →
      Term.Diverges (.block lifetime terms)

mutual
  /-- Syntactic exclusion of the generated diverging `missing` placeholder. -/
  def Term.MissingFree : Term → Prop
    | .block _ terms => Term.MissingFreeList terms
    | .letMut _ initialiser => initialiser.MissingFree
    | .assign _ rhs => rhs.MissingFree
    | .box operand => operand.MissingFree
    | .borrow _ _ => True
    | .move _ => True
    | .copy _ => True
    | .val _ => True
    | .missing => False
    | .eq lhs rhs => lhs.MissingFree ∧ rhs.MissingFree
    | .ite condition trueBranch falseBranch =>
        condition.MissingFree ∧ trueBranch.MissingFree ∧ falseBranch.MissingFree
    | .whileLoop _ condition body =>
        condition.MissingFree ∧ body.MissingFree
    | .whileCond _ conditionInFlight condition body =>
        conditionInFlight.MissingFree ∧ condition.MissingFree ∧ body.MissingFree
    | .whileBody _ bodyInFlight condition body =>
        bodyInFlight.MissingFree ∧ condition.MissingFree ∧ body.MissingFree

  def Term.MissingFreeList : List Term → Prop
    | [] => True
    | term :: rest => term.MissingFree ∧ Term.MissingFreeList rest
end

mutual
  /-- Syntactic exclusion of while loops and their runtime-only phases.

  Unlike `MissingFree`, this predicate says only that no loop occurs.  The
  terminating fragment of the extended calculus therefore requires both
  predicates rather than overloading either one. -/
  def Term.LoopFree : Term → Prop
    | .block _ terms => Term.LoopFreeList terms
    | .letMut _ initialiser => initialiser.LoopFree
    | .assign _ rhs => rhs.LoopFree
    | .box operand => operand.LoopFree
    | .borrow _ _ => True
    | .move _ => True
    | .copy _ => True
    | .val _ => True
    | .missing => True
    | .eq lhs rhs => lhs.LoopFree ∧ rhs.LoopFree
    | .ite condition trueBranch falseBranch =>
        condition.LoopFree ∧ trueBranch.LoopFree ∧ falseBranch.LoopFree
    | .whileLoop _ _ _ => False
    | .whileCond _ _ _ _ => False
    | .whileBody _ _ _ _ => False

  def Term.LoopFreeList : List Term → Prop
    | [] => True
    | term :: rest => term.LoopFree ∧ Term.LoopFreeList rest
end

theorem Term.MissingFreeList.of_mem {terms : List Term} {term : Term} :
    Term.MissingFreeList terms →
    term ∈ terms →
    term.MissingFree := by
  intro hfree hmem
  induction terms with
  | nil =>
      cases hmem
  | cons head tail ih =>
      rcases hfree with ⟨hhead, htail⟩
      rcases List.mem_cons.mp hmem with hterm | hmem
      · subst hterm
        exact hhead
      · exact ih htail hmem

theorem Term.MissingFreeList.tail {term : Term} {rest : List Term} :
    Term.MissingFreeList (term :: rest) →
    Term.MissingFreeList rest :=
  fun hfree => hfree.2

theorem Term.MissingFree.block_head {lifetime : Lifetime} {term : Term}
    {rest : List Term} :
    Term.MissingFree (.block lifetime (term :: rest)) →
    term.MissingFree :=
  fun hfree => hfree.1

theorem Term.MissingFree.block_tail {lifetime : Lifetime} {term next : Term}
    {rest : List Term} :
    Term.MissingFree (.block lifetime (term :: next :: rest)) →
    Term.MissingFree (.block lifetime (next :: rest)) :=
  fun hfree => hfree.2

theorem Term.MissingFree.box_inner {term : Term} :
    Term.MissingFree (.box term) → term.MissingFree :=
  fun hfree => hfree

theorem Term.MissingFree.declare_inner {x : Name} {term : Term} :
    Term.MissingFree (.letMut x term) → term.MissingFree :=
  fun hfree => hfree

theorem Term.MissingFree.assign_inner {lhs : LVal} {rhs : Term} :
    Term.MissingFree (.assign lhs rhs) → rhs.MissingFree :=
  fun hfree => hfree

theorem Term.MissingFree.eq_lhs {lhs rhs : Term} :
    Term.MissingFree (.eq lhs rhs) → lhs.MissingFree :=
  fun hfree => hfree.1

theorem Term.MissingFree.eq_rhs {lhs rhs : Term} :
    Term.MissingFree (.eq lhs rhs) → rhs.MissingFree :=
  fun hfree => hfree.2

theorem Term.MissingFree.ite_condition {condition trueBranch falseBranch : Term} :
    Term.MissingFree (.ite condition trueBranch falseBranch) →
    condition.MissingFree :=
  fun hfree => hfree.1

theorem Term.MissingFree.ite_trueBranch {condition trueBranch falseBranch : Term} :
    Term.MissingFree (.ite condition trueBranch falseBranch) →
    trueBranch.MissingFree :=
  fun hfree => hfree.2.1

theorem Term.MissingFree.ite_falseBranch {condition trueBranch falseBranch : Term} :
    Term.MissingFree (.ite condition trueBranch falseBranch) →
    falseBranch.MissingFree :=
  fun hfree => hfree.2.2

theorem Term.MissingFree.while_condition {bodyLifetime : Lifetime}
    {condition body : Term} :
    Term.MissingFree (.whileLoop bodyLifetime condition body) →
    condition.MissingFree :=
  fun hfree => hfree.1

theorem Term.MissingFree.while_body {bodyLifetime : Lifetime}
    {condition body : Term} :
    Term.MissingFree (.whileLoop bodyLifetime condition body) →
    body.MissingFree :=
  fun hfree => hfree.2

theorem Term.MissingFree.whileCond_inFlight {bodyLifetime : Lifetime}
    {conditionInFlight condition body : Term} :
    Term.MissingFree
      (.whileCond bodyLifetime conditionInFlight condition body) →
    conditionInFlight.MissingFree :=
  fun hfree => hfree.1

theorem Term.MissingFree.whileCond_condition {bodyLifetime : Lifetime}
    {conditionInFlight condition body : Term} :
    Term.MissingFree
      (.whileCond bodyLifetime conditionInFlight condition body) →
    condition.MissingFree :=
  fun hfree => hfree.2.1

theorem Term.MissingFree.whileCond_body {bodyLifetime : Lifetime}
    {conditionInFlight condition body : Term} :
    Term.MissingFree
      (.whileCond bodyLifetime conditionInFlight condition body) →
    body.MissingFree :=
  fun hfree => hfree.2.2

theorem Term.MissingFree.whileBody_inFlight {bodyLifetime : Lifetime}
    {bodyInFlight condition body : Term} :
    Term.MissingFree (.whileBody bodyLifetime bodyInFlight condition body) →
    bodyInFlight.MissingFree :=
  fun hfree => hfree.1

theorem Term.MissingFree.whileBody_condition {bodyLifetime : Lifetime}
    {bodyInFlight condition body : Term} :
    Term.MissingFree (.whileBody bodyLifetime bodyInFlight condition body) →
    condition.MissingFree :=
  fun hfree => hfree.2.1

theorem Term.MissingFree.whileBody_body {bodyLifetime : Lifetime}
    {bodyInFlight condition body : Term} :
    Term.MissingFree (.whileBody bodyLifetime bodyInFlight condition body) →
    body.MissingFree :=
  fun hfree => hfree.2.2

theorem Term.MissingFree.not_diverges {term : Term} :
    term.MissingFree →
    ¬ term.Diverges := by
  intro hfree hdiv
  induction hdiv with
  | missing =>
      exact hfree
  | block hmem _hinner ih =>
      exact ih (Term.MissingFreeList.of_mem hfree hmem)

theorem Term.LoopFreeList.of_mem {terms : List Term} {term : Term} :
    Term.LoopFreeList terms →
    term ∈ terms →
    term.LoopFree := by
  intro hfree hmem
  induction terms with
  | nil =>
      cases hmem
  | cons head tail ih =>
      rcases hfree with ⟨hhead, htail⟩
      rcases List.mem_cons.mp hmem with hterm | hmem
      · subst hterm
        exact hhead
      · exact ih htail hmem

theorem Term.LoopFreeList.tail {term : Term} {rest : List Term} :
    Term.LoopFreeList (term :: rest) →
    Term.LoopFreeList rest :=
  fun hfree => hfree.2

theorem Term.LoopFree.block_head {lifetime : Lifetime} {term : Term}
    {rest : List Term} :
    Term.LoopFree (.block lifetime (term :: rest)) →
    term.LoopFree :=
  fun hfree => hfree.1

theorem Term.LoopFree.block_tail {lifetime : Lifetime} {term next : Term}
    {rest : List Term} :
    Term.LoopFree (.block lifetime (term :: next :: rest)) →
    Term.LoopFree (.block lifetime (next :: rest)) :=
  fun hfree => hfree.2

theorem Term.LoopFree.box_inner {term : Term} :
    Term.LoopFree (.box term) → term.LoopFree :=
  fun hfree => hfree

theorem Term.LoopFree.declare_inner {x : Name} {term : Term} :
    Term.LoopFree (.letMut x term) → term.LoopFree :=
  fun hfree => hfree

theorem Term.LoopFree.assign_inner {lhs : LVal} {rhs : Term} :
    Term.LoopFree (.assign lhs rhs) → rhs.LoopFree :=
  fun hfree => hfree

theorem Term.LoopFree.eq_lhs {lhs rhs : Term} :
    Term.LoopFree (.eq lhs rhs) → lhs.LoopFree :=
  fun hfree => hfree.1

theorem Term.LoopFree.eq_rhs {lhs rhs : Term} :
    Term.LoopFree (.eq lhs rhs) → rhs.LoopFree :=
  fun hfree => hfree.2

theorem Term.LoopFree.ite_condition {condition trueBranch falseBranch : Term} :
    Term.LoopFree (.ite condition trueBranch falseBranch) →
    condition.LoopFree :=
  fun hfree => hfree.1

theorem Term.LoopFree.ite_trueBranch
    {condition trueBranch falseBranch : Term} :
    Term.LoopFree (.ite condition trueBranch falseBranch) →
    trueBranch.LoopFree :=
  fun hfree => hfree.2.1

theorem Term.LoopFree.ite_falseBranch
    {condition trueBranch falseBranch : Term} :
    Term.LoopFree (.ite condition trueBranch falseBranch) →
    falseBranch.LoopFree :=
  fun hfree => hfree.2.2

end Core
end FWRust
