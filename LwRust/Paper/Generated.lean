import LwRust.Paper.Typing

/-!
# Generated environment operations

This module starts separating *computed* typing-environment operations from the
paper-facing relational judgments in `Typing.lean`.

The existing rules use relations such as `EnvJoin left right join`, where
`join` is supplied by the derivation.  That shape forces typing rules to carry
extra invariants (`Coherent`, `Linearizable`, `BorrowSafeEnv`, ...), because a
badly chosen output environment can otherwise be smuggled into the derivation.

The definitions below are deliberately algorithm-shaped:

* `Generated.joinTy?` / `Generated.joinPartialTy?` choose a concrete type join.
* `Generated.Env.pointwiseJoin` chooses a concrete environment join candidate.
* `Generated.Ty.rebuildBorrowPointees?` is the hook for the coherence repair
  pass: after a slot such as `b` grows, borrows targeting `b` must have their
  carried pointee annotations rebuilt from the current target type.

The typing rules should eventually consume generated operations from this module
instead of accepting arbitrary output environments plus invariant premises.
-/

namespace LwRust
namespace Paper

open Core

namespace Generated

/-- Deterministic target-list union used by generated borrow joins. -/
def unionTargets (left right : List LVal) : List LVal :=
  left ++ right.filter (fun target => !left.contains target)

mutual
  /-- Deterministic join for full types, choosing one representative when the
  strengthening preorder admits equivalent target-list orderings. -/
  def joinTy? : Ty → Ty → Option Ty
    | .unit, .unit => some .unit
    | .int, .int => some .int
    | .bool, .bool => some .bool
    | .box left, .box right => do
        let joined ← joinTy? left right
        some (.box joined)
    | .borrow leftMutable leftTargets leftPointee,
        .borrow rightMutable rightTargets rightPointee => do
        if _hmutable : leftMutable = rightMutable then
          let joinedPointee ← joinTy? leftPointee rightPointee
          some (.borrow leftMutable (unionTargets leftTargets rightTargets)
            joinedPointee)
        else
          none
    | _, _ => none

  /-- Deterministic join for partial types.  This includes the paper's
  initialized/undefined weakening shape: `T ⊔ undef(T') = undef(T ⊔ T')`. -/
  def joinPartialTy? : PartialTy → PartialTy → Option PartialTy
    | .ty left, .ty right => do
        let joined ← joinTy? left right
        some (.ty joined)
    | .box left, .box right => do
        let joined ← joinPartialTy? left right
        some (.box joined)
    | .undef left, .undef right => do
        let joined ← joinTy? left right
        some (.undef joined)
    | .ty left, .undef right => do
        let joined ← joinTy? left right
        some (.undef joined)
    | .undef left, .ty right => do
        let joined ← joinTy? left right
        some (.undef joined)
    | _, _ => none
end

def joinSlot? (left right : EnvSlot) : Option EnvSlot := do
  if _hlifetime : left.lifetime = right.lifetime then
    let joinedTy ← joinPartialTy? left.ty right.ty
    some { ty := joinedTy, lifetime := left.lifetime }
  else
    none

/-- Generated full-type join: the result is selected by `joinTy?`. -/
def TyJoinGenerated (left right join : Ty) : Prop :=
  joinTy? left right = some join

/-- Generated partial-type join: the result is selected by `joinPartialTy?`. -/
def PartialTyJoinGenerated (left right join : PartialTy) : Prop :=
  joinPartialTy? left right = some join

namespace Env

/-- Pointwise generated environment-join candidate.

This function is total because `Env` is an abstract lookup function.  Failed
pointwise joins are represented by `none` at that slot; callers should pair this
with `pointwiseJoinComplete` when they need a successful generated join. -/
def pointwiseJoin (left right : Paper.Env) : Paper.Env :=
  { slotAt := fun x =>
      match left.slotAt x, right.slotAt x with
      | none, none => none
      | some leftSlot, some rightSlot => joinSlot? leftSlot rightSlot
      | _, _ => none }

/-- All slots needed for `pointwiseJoin` were present on both sides and joined
successfully. -/
def pointwiseJoinComplete (left right : Paper.Env) : Prop :=
  ∀ x,
    match left.slotAt x, right.slotAt x with
    | none, none => True
    | some leftSlot, some rightSlot =>
        leftSlot.lifetime = rightSlot.lifetime ∧
        ∃ joinedTy, joinPartialTy? leftSlot.ty rightSlot.ty = some joinedTy
    | _, _ => False

/-- Generated join: the output is fixed by `pointwiseJoin`, not supplied
arbitrarily by a typing derivation. -/
def GeneratedJoin (left right join : Paper.Env) : Prop :=
  join = pointwiseJoin left right ∧ pointwiseJoinComplete left right

/-- Root-only target type lookup used by the first coherence-repair hook.

Full normalization should use the algorithmic lvalue-typing operation; this
root lookup is enough to state the essential repair pass without changing the
existing `LValTyping` relation yet. -/
def rootTargetTy? (env : Paper.Env) : LVal → Option Ty
  | .var x =>
      match env.slotAt x with
      | some { ty := .ty ty, .. } => some ty
      | _ => none
  | .deref _ => none

end Env

mutual
  /-- Join the current types of a non-empty target list. -/
  def joinTargetTypes? (targetTy? : LVal → Option Ty) :
      List LVal → Ty → Option Ty
    | [], acc => some acc
    | target :: rest, acc => do
        let targetTy ← targetTy? target
        let joined ← joinTy? acc targetTy
        joinTargetTypes? targetTy? rest joined

  /-- Rebuild borrow pointee annotations from the current target types.

For a borrow `&[targets] pointee`, non-empty `targets` are authoritative: the
carried `pointee` is recomputed from the generated types of those targets.  This
is the pass needed for chains such as `a : &mut[b] (&mut[x] int)` when `b` grows
to `&mut[x,c] int`.
  -/
  def Ty.rebuildBorrowPointees? (targetTy? : LVal → Option Ty) : Ty → Option Ty
    | .unit => some .unit
    | .int => some .int
    | .bool => some .bool
    | .box inner => do
        let inner' ← Ty.rebuildBorrowPointees? targetTy? inner
        some (.box inner')
    | .borrow mutable targets pointee => do
        match targets with
        | [] =>
            let pointee' ← Ty.rebuildBorrowPointees? targetTy? pointee
            some (.borrow mutable [] pointee')
        | target :: rest =>
            let headTy ← targetTy? target
            let joinedTargetsTy ← joinTargetTypes? targetTy? rest headTy
            some (.borrow mutable targets joinedTargetsTy)

  def PartialTy.rebuildBorrowPointees? (targetTy? : LVal → Option Ty) :
      PartialTy → Option PartialTy
    | .ty ty => do
        let ty' ← Ty.rebuildBorrowPointees? targetTy? ty
        some (.ty ty')
    | .box inner => do
        let inner' ← PartialTy.rebuildBorrowPointees? targetTy? inner
        some (.box inner')
    | .undef ty => do
        let ty' ← Ty.rebuildBorrowPointees? targetTy? ty
        some (.undef ty')
end

namespace Env

/-- One pass of borrow-pointee rebuilding over an environment.  The result is
again pointwise generated: every slot is either rebuilt by the algorithm or
discarded on failure.  Later typing rules should use a successful/generated
variant rather than this raw total candidate. -/
def rebuildRootBorrowPointees (env : Paper.Env) : Paper.Env :=
  { slotAt := fun x =>
      match env.slotAt x with
      | none => none
      | some slot =>
          match Generated.PartialTy.rebuildBorrowPointees? (rootTargetTy? env) slot.ty with
          | some ty => some { slot with ty := ty }
          | none => none }

def rebuildRootBorrowPointeesComplete (env : Paper.Env) : Prop :=
  ∀ x slot,
    env.slotAt x = some slot →
      ∃ rebuiltTy,
        Generated.PartialTy.rebuildBorrowPointees? (rootTargetTy? env) slot.ty =
          some rebuiltTy

/-- Generated coherent-join candidate: first choose the pointwise join, then
rebuild borrow pointee annotations from the joined target types. -/
def coherentJoin (left right : Paper.Env) : Paper.Env :=
  rebuildRootBorrowPointees (pointwiseJoin left right)

def CoherentJoinGenerated (left right join : Paper.Env) : Prop :=
  join = coherentJoin left right ∧
    pointwiseJoinComplete left right ∧
    rebuildRootBorrowPointeesComplete (pointwiseJoin left right)

end Env

/-! ## Generated control-flow joins

These definitions model the route we want the typing rules to take: branch and
loop merge environments are produced by the generated operations above.  The
relations still refer to the existing `TermTyping` judgment for checking the
subterms, but they do not let a typing derivation supply an arbitrary merge
environment or attach coherence as a premise of that merge.
-/

/-- Generated conditional merge.  Both the result type and the result
environment are fixed by generated operations. -/
structure IfMergeGenerated
    (trueTy falseTy joinTy : Ty) (trueEnv falseEnv joinEnv : Paper.Env) :
    Prop where
  tyJoin : TyJoinGenerated trueTy falseTy joinTy
  envJoin : Paper.Generated.Env.CoherentJoinGenerated trueEnv falseEnv joinEnv

/-- Generated typing shape for `if`: subterms are checked by the existing
typing relation, while the merge type and merge environment are fixed by
generated operations.

This is the conditional counterpart of `WhileLoopTypingGenerated` below and is
the migration target for replacing the legacy `TermTyping.ite` constructor's
caller-supplied join and coherence premises. -/
def IfTypingGenerated
    (entry : Paper.Env) (typing : StoreTyping) (lifetime : Lifetime)
    (condition trueBranch falseBranch : Term) (joinTy : Ty)
    (joinEnv : Paper.Env) : Prop :=
  ∃ conditionEnv trueEnv falseEnv trueTy falseTy,
    TermTyping entry typing lifetime condition .bool conditionEnv ∧
    TermTyping conditionEnv typing lifetime trueBranch trueTy trueEnv ∧
    TermTyping conditionEnv typing lifetime falseBranch falseTy falseEnv ∧
    IfMergeGenerated trueTy falseTy joinTy trueEnv falseEnv joinEnv

/-- One generated loop-invariant iteration.

Starting from `current`, check the condition and body once, drop the body
lifetime to obtain the back-edge environment, then compute the next invariant
candidate as the generated coherent join of `entry` and that back edge. -/
inductive LoopIterationGenerated
    (entry : Paper.Env) (typing : StoreTyping)
    (lifetime bodyLifetime : Lifetime) (condition body : Term) :
    Paper.Env → Paper.Env → Prop where
  | step {current conditionEnv bodyEnv backEnv next : Paper.Env}
      {bodyTy : Ty} :
      TermTyping current typing lifetime condition .bool conditionEnv →
      TermTyping conditionEnv typing bodyLifetime body bodyTy bodyEnv →
      WellFormedTy bodyEnv bodyTy lifetime →
      bodyEnv.dropLifetime bodyLifetime = backEnv →
      Paper.Generated.Env.CoherentJoinGenerated entry backEnv next →
      LoopIterationGenerated entry typing lifetime bodyLifetime condition body
        current next

/-- Finite generated fixed-point iteration for a loop invariant.

`LoopFixpointGenerated entry ... fuel current invariant exitEnv` means that
starting from `current`, at most `fuel + 1` generated iterations reach a stable
`invariant`.  The `exitEnv` is the post-condition environment produced by
typing the condition from that stable invariant. -/
inductive LoopFixpointGenerated
    (entry : Paper.Env) (typing : StoreTyping)
    (lifetime bodyLifetime : Lifetime) (condition body : Term) :
    Nat → Paper.Env → Paper.Env → Paper.Env → Prop where
  | done {current conditionEnv bodyEnv backEnv : Paper.Env} {bodyTy : Ty} :
      TermTyping current typing lifetime condition .bool conditionEnv →
      TermTyping conditionEnv typing bodyLifetime body bodyTy bodyEnv →
      WellFormedTy bodyEnv bodyTy lifetime →
      bodyEnv.dropLifetime bodyLifetime = backEnv →
      Paper.Generated.Env.CoherentJoinGenerated entry backEnv current →
      LoopFixpointGenerated entry typing lifetime bodyLifetime condition body
        0 current current conditionEnv
  | step {fuel : Nat} {current next invariant exitEnv : Paper.Env} :
      LoopIterationGenerated entry typing lifetime bodyLifetime condition body
        current next →
      current ≠ next →
      LoopFixpointGenerated entry typing lifetime bodyLifetime condition body
        fuel next invariant exitEnv →
      LoopFixpointGenerated entry typing lifetime bodyLifetime condition body
        (fuel + 1) current invariant exitEnv

/-- Generated loop invariant obtained by iterating from the entry environment. -/
def LoopInvariantGenerated
    (entry : Paper.Env) (typing : StoreTyping)
    (lifetime bodyLifetime : Lifetime) (condition body : Term)
    (invariant exitEnv : Paper.Env) : Prop :=
  ∃ fuel,
    LoopFixpointGenerated entry typing lifetime bodyLifetime condition body
      fuel entry invariant exitEnv

/-- Generated typing shape for `while`: the invariant and exit environment come
from generated fixed-point iteration, not from caller-supplied join witnesses.

This is not yet wired into `TermTyping`; it is the migration target for replacing
the legacy `TermTyping.whileLoop` constructor. -/
def WhileLoopTypingGenerated
    (entry : Paper.Env) (typing : StoreTyping)
    (lifetime bodyLifetime : Lifetime) (condition body : Term)
    (exitEnv : Paper.Env) : Prop :=
  LifetimeChild lifetime bodyLifetime ∧
    ∃ invariant,
      LoopInvariantGenerated entry typing lifetime bodyLifetime condition body
        invariant exitEnv

/-! ## Sanity check: rebuilding a reborrow chain

The environment below models the problematic shape:

* `b : &mut[x,c] int`
* `a : &mut[b] (&mut[x] int)`

The rebuild pass makes `a`'s carried pointee agree with the current type of
`b`, producing `a : &mut[b] (&mut[x,c] int)`.
-/

def reborrowChainBeforeRepair : Paper.Env :=
  { slotAt := fun name =>
      if name = "x" then
        some { ty := .ty .int, lifetime := Lifetime.root }
      else if name = "c" then
        some { ty := .ty .int, lifetime := Lifetime.root }
      else if name = "b" then
        some {
          ty := .ty (.borrow true [.var "x", .var "c"] .int),
          lifetime := Lifetime.root
        }
      else if name = "a" then
        some {
          ty := .ty (.borrow true [.var "b"]
            (.borrow true [.var "x"] .int)),
          lifetime := Lifetime.root
        }
      else
        none }

example :
    (Env.rebuildRootBorrowPointees reborrowChainBeforeRepair).slotAt "a" =
      some {
        ty := .ty (.borrow true [.var "b"]
          (.borrow true [.var "x", .var "c"] .int)),
        lifetime := Lifetime.root
      } := by
  simp [Env.rebuildRootBorrowPointees, Env.rootTargetTy?,
    reborrowChainBeforeRepair, PartialTy.rebuildBorrowPointees?,
    Ty.rebuildBorrowPointees?, joinTargetTypes?]

end Generated

end Paper
end LwRust
