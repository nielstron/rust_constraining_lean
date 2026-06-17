import LwRust.Paper.Soundness.Helpers.AppendixPrelim

/-!
Executable borrow/type checker for the finite fragment used by examples.

The declarative rules in `Typing.lean` are propositions over abstract
function-valued environments and existential rank functions.  This module gives
an executable counterpart over finite environments.  It computes the ordinary
typing/borrow checks, environment joins, assignment-local borrow authority, and
the maintained environment invariants (`ContainedBorrowsWellFormed`,
`Coherent`, and `Linearizable`) as booleans/`Except` results.

The raw checker is an executable search layer.  The public proof-carrying layer
below packages a successful run together with the matching declarative
`TermTyping` derivation; its final boolean is just whether such a certificate
was found.
-/

namespace LwRust
namespace Paper

open Core

structure FiniteEnv where
  entries : List (Name × EnvSlot)
  deriving BEq, DecidableEq, Repr

namespace FiniteEnv

def empty : FiniteEnv :=
  { entries := [] }

def lookupEntries : List (Name × EnvSlot) → Name → Option EnvSlot
  | [], _ => none
  | (name, slot) :: rest, needle =>
      if needle = name then some slot else lookupEntries rest needle

def lookup (env : FiniteEnv) (name : Name) : Option EnvSlot :=
  lookupEntries env.entries name

def fresh (env : FiniteEnv) (name : Name) : Bool :=
  env.lookup name == none

def update (env : FiniteEnv) (name : Name) (slot : EnvSlot) : FiniteEnv :=
  { entries := (name, slot) :: env.entries.filter (fun entry => entry.1 != name) }

def erase (env : FiniteEnv) (name : Name) : FiniteEnv :=
  { entries := env.entries.filter (fun entry => entry.1 != name) }

private theorem lookupEntries_filter_update_ne
    (entries : List (Name × EnvSlot)) {name needle : Name}
    (hne : needle ≠ name) :
    lookupEntries (entries.filter (fun entry => entry.1 != name)) needle =
      lookupEntries entries needle := by
  induction entries with
  | nil =>
      simp [lookupEntries]
  | cons entry rest ih =>
      rcases entry with ⟨entryName, entrySlot⟩
      by_cases hentry : entryName = name
      · have hneedle : ¬ needle = entryName := by
          intro h
          exact hne (h.trans hentry)
        simp [lookupEntries, hentry, hne, ih]
      · by_cases hneedle : needle = entryName
        · subst hneedle
          simp [lookupEntries, hentry]
        · simp [lookupEntries, hentry, hneedle, ih]

def support (env : FiniteEnv) : List Name :=
  env.entries.foldl
    (fun names entry => if names.contains entry.1 then names else names ++ [entry.1])
    []

def toEnv (env : FiniteEnv) : Env :=
  { slotAt := env.lookup }

@[simp] theorem toEnv_empty :
    (FiniteEnv.empty).toEnv = Env.empty := by
  apply congrArg Env.mk
  funext _name
  rfl

@[simp] theorem toEnv_update (env : FiniteEnv) (name : Name)
    (slot : EnvSlot) :
    (env.update name slot).toEnv = env.toEnv.update name slot := by
  cases env with
  | mk entries =>
      apply congrArg Env.mk
      funext needle
      by_cases hneedle : needle = name
      · subst hneedle
        simp [lookup, update, lookupEntries]
      · simp [toEnv, lookup, update, lookupEntries, hneedle,
          lookupEntries_filter_update_ne entries hneedle]

def dropLifetime (env : FiniteEnv) (lifetime : Lifetime) : FiniteEnv :=
  { entries := env.entries.filter (fun entry => entry.2.lifetime != lifetime) }

end FiniteEnv

structure CheckResult where
  ty : Ty
  env : FiniteEnv
  deriving BEq, DecidableEq, Repr

private def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def fromOption (message : String) : Option α → Except String α
  | some value => .ok value
  | none => .error message

private def insertName (names : List Name) (name : Name) : List Name :=
  if names.contains name then names else names ++ [name]

private def unionNames (left right : List Name) : List Name :=
  right.foldl insertName left

namespace FiniteEnv

def sameBindings (left right : FiniteEnv) : Bool :=
  let names := unionNames left.support right.support
  names.all (fun name => left.lookup name == right.lookup name)

end FiniteEnv

private def insertLVal (targets : List LVal) (target : LVal) : List LVal :=
  if targets.contains target then targets else targets ++ [target]

private def unionLVals (left right : List LVal) : List LVal :=
  left ++ right

private def lvalNames : LVal → List Name
  | .var name => [name]
  | .deref lv => lvalNames lv

mutual
  private def tyNames : Ty → List Name
    | .unit => []
    | .int => []
    | .bool => []
    | .borrow _ targets =>
        targets.foldl (fun names target => unionNames names (lvalNames target)) []
    | .box ty => tyNames ty

  private def partialTyNames : PartialTy → List Name
    | .ty ty => tyNames ty
    | .box ty => partialTyNames ty
    | .undef _ => []
end

private def termNames : Term → List Name
  | .block _ terms =>
      terms.foldl (fun names term => unionNames names (termNames term)) []
  | .letMut name initialiser => insertName (termNames initialiser) name
  | .assign lhs rhs => unionNames (lvalNames lhs) (termNames rhs)
  | .box operand => termNames operand
  | .borrow _ operand => lvalNames operand
  | .move operand => lvalNames operand
  | .copy operand => lvalNames operand
  | .val _ => []
  | .missing => []
  | .eq lhs rhs => unionNames (termNames lhs) (termNames rhs)
  | .ite condition trueBranch falseBranch =>
      unionNames (termNames condition)
        (unionNames (termNames trueBranch) (termNames falseBranch))
  | .whileLoop _ condition body => unionNames (termNames condition) (termNames body)
  | .whileCond _ conditionInFlight condition body =>
      unionNames (termNames conditionInFlight)
        (unionNames (termNames condition) (termNames body))
  | .whileBody _ bodyInFlight condition body =>
      unionNames (termNames bodyInFlight)
        (unionNames (termNames condition) (termNames body))

private def envNames (env : FiniteEnv) : List Name :=
  env.entries.foldl
    (fun names entry => unionNames (insertName names entry.1) (partialTyNames entry.2.ty))
    []

private def envEqOnSupport (left right : FiniteEnv) : Bool :=
  left.sameBindings right

private partial def freshNameFrom (used : List Name) (fuel : Nat) : Name :=
  let candidate := "_γ" ++ toString fuel
  if used.contains candidate then freshNameFrom used (fuel + 1) else candidate

private def freshGhostName (env : FiniteEnv) (term : Term) : Name :=
  freshNameFrom (unionNames (envNames env) (termNames term)) 0

private def copyTy : Ty → Bool
  | .unit => true
  | .int => true
  | .bool => true
  | .borrow false _ => true
  | _ => false

mutual
  private def tyLoanFree : Ty → Bool
    | .unit => true
    | .int => true
    | .bool => true
    | .borrow _ targets => targets.isEmpty
    | .box ty => tyLoanFree ty

  private def partialTyLoanFree : PartialTy → Bool
    | .ty ty => tyLoanFree ty
    | .box ty => partialTyLoanFree ty
    | .undef _ => true
end

mutual
  private def tyBorrows : Ty → List (Bool × List LVal)
    | .unit => []
    | .int => []
    | .bool => []
    | .borrow mutable targets => [(mutable, targets)]
    | .box ty => tyBorrows ty

  private def partialTyBorrows : PartialTy → List (Bool × List LVal)
    | .ty ty => tyBorrows ty
    | .box ty => partialTyBorrows ty
    | .undef _ => []
end

private def partialTyContainsBorrow
    (partialTy : PartialTy) (mutable : Bool) (targets : List LVal) : Bool :=
  (partialTyBorrows partialTy).any
    (fun borrow => borrow.1 == mutable && borrow.2 == targets)

private def pathConflicts (left right : LVal) : Bool :=
  LVal.base left == LVal.base right

private def envBorrowEdges (env : FiniteEnv) : List (Name × Bool × List LVal) :=
  env.entries.foldr
    (fun entry edges =>
      (partialTyBorrows entry.2.ty).map
          (fun borrow => (entry.1, borrow.1, borrow.2)) ++ edges)
    []

private def readProhibited (env : FiniteEnv) (lv : LVal) : Bool :=
  (envBorrowEdges env).any (fun edge =>
    edge.2.1 &&
      edge.2.2.any (fun target => pathConflicts target lv))

private def writeProhibited (env : FiniteEnv) (lv : LVal) : Bool :=
  readProhibited env lv ||
    (envBorrowEdges env).any (fun edge =>
      edge.2.2.any (fun target => pathConflicts target lv))

mutual
  private def tyJoin? : Ty → Ty → Option Ty
    | .unit, .unit => some .unit
    | .int, .int => some .int
    | .bool, .bool => some .bool
    | .borrow mutable₁ targets₁, .borrow mutable₂ targets₂ =>
        if mutable₁ == mutable₂ then
          some (.borrow mutable₁ (unionLVals targets₁ targets₂))
        else
          none
    | .box left, .box right => do
        some (.box (← tyJoin? left right))
    | _, _ => none

  private def partialTyJoin? : PartialTy → PartialTy → Option PartialTy
    | .ty left, .ty right => do
        some (.ty (← tyJoin? left right))
    | .box left, .box right => do
        some (.box (← partialTyJoin? left right))
    | .undef left, .undef right => do
        some (.undef (← tyJoin? left right))
    | .ty left, .undef right => do
        some (.undef (← tyJoin? left right))
    | .undef left, .ty right => do
        some (.undef (← tyJoin? left right))
    | _, _ => none
end

mutual
  private def tySameShape : Ty → Ty → Bool
    | .unit, .unit => true
    | .int, .int => true
    | .bool, .bool => true
    | .borrow mutable₁ _, .borrow mutable₂ _ => mutable₁ == mutable₂
    | .box left, .box right => tySameShape left right
    | _, _ => false

  private def partialTySameShape : PartialTy → PartialTy → Bool
    | .ty left, .ty right => tySameShape left right
    | .box left, .box right => partialTySameShape left right
    | .undef left, .undef right => tySameShape left right
    | _, _ => false
end

private def lifetimeIntersection? (left right : Lifetime) : Option Lifetime :=
  if left.contains right then some right
  else if right.contains left then some left
  else none

private def lifetimeOutlives (outer inner : Lifetime) : Bool :=
  outer.contains inner

mutual
  private def lvalType? : Nat → FiniteEnv → LVal → Option (PartialTy × Lifetime)
    | 0, _, _ => none
    | _fuel + 1, env, .var name => do
        let slot ← env.lookup name
        some (slot.ty, slot.lifetime)
    | fuel + 1, env, .deref lv => do
        match ← lvalType? fuel env lv with
        | (.box inner, lifetime) => some (inner, lifetime)
        | (.ty (.borrow _ targets), _) => lvalTargetsType? fuel env targets
        | _ => none

  private def lvalTargetsType? :
      Nat → FiniteEnv → List LVal → Option (PartialTy × Lifetime)
    | _, _, [] => none
    | fuel, env, [target] => do
        match ← lvalType? fuel env target with
        | (.ty ty, lifetime) => some (.ty ty, lifetime)
        | _ => none
    | fuel, env, target :: rest => do
        let (headTy, headLifetime) ←
          match ← lvalType? fuel env target with
          | (.ty ty, lifetime) => some (.ty ty, lifetime)
          | _ => none
        let (restTy, restLifetime) ← lvalTargetsType? fuel env rest
        let unionTy ← partialTyJoin? headTy restTy
        let lifetime ← lifetimeIntersection? headLifetime restLifetime
        some (unionTy, lifetime)
end

private def lvalBaseOutlives (env : FiniteEnv) (lv : LVal)
    (lifetime : Lifetime) : Bool :=
  match env.lookup (LVal.base lv) with
  | some slot => lifetimeOutlives slot.lifetime lifetime
  | none => false

private def borrowTargetsWellFormed
    (fuel : Nat) (env : FiniteEnv) (targets : List LVal)
    (lifetime : Lifetime) : Bool :=
  targets.all (fun target =>
    match lvalType? fuel env target with
    | some (.ty _, targetLifetime) =>
        lifetimeOutlives targetLifetime lifetime &&
          lvalBaseOutlives env target lifetime
    | _ => false)

private def wellFormedTy (fuel : Nat) (env : FiniteEnv)
    (ty : Ty) (lifetime : Lifetime) : Bool :=
  match ty with
  | .unit => true
  | .int => true
  | .bool => true
  | .borrow _ targets => borrowTargetsWellFormed fuel env targets lifetime
  | .box inner => wellFormedTy fuel env inner lifetime

private def targetListPartialTy? (fuel : Nat) (env : FiniteEnv)
    (targets : List LVal) : Option (Option PartialTy) :=
  match targets with
  | [] => some none
  | _ => do
      let (ty, _) ← lvalTargetsType? fuel env targets
      some (some ty)

mutual
  private partial def shapeCompatibleTy
      (fuel : Nat) (env : FiniteEnv) : Ty → Ty → Bool
    | .unit, .unit => true
    | .int, .int => true
    | .bool, .bool => true
    | .box left, .box right => shapeCompatibleTy fuel env left right
    | .borrow mutable₁ leftTargets, .borrow mutable₂ rightTargets =>
        mutable₁ == mutable₂ &&
          match targetListPartialTy? fuel env leftTargets,
              targetListPartialTy? fuel env rightTargets with
          | some none, some none => true
          | some none, some (some _) => true
          | some (some _), some none => true
          | some (some leftTy), some (some rightTy) =>
              shapeCompatiblePartialTy fuel env leftTy rightTy
          | _, _ => false
    | _, _ => false

  private partial def shapeCompatiblePartialTy
      (fuel : Nat) (env : FiniteEnv) : PartialTy → PartialTy → Bool
    | .ty left, .ty right => shapeCompatibleTy fuel env left right
    | .box left, .box right => shapeCompatiblePartialTy fuel env left right
    | .undef left, right => shapeCompatiblePartialTy fuel env (.ty left) right
    | left, .undef right => shapeCompatiblePartialTy fuel env left (.ty right)
    | _, _ => false
end

mutual
  private def mutableLVal (fuel : Nat) (env : FiniteEnv) : LVal → Bool
    | .var name => (env.lookup name).isSome
    | .deref lv =>
        match fuel with
        | 0 => false
        | fuel + 1 =>
            match lvalType? fuel env lv with
            | some (.box _, _) => mutableLVal fuel env lv
            | some (.ty (.borrow true targets), _) =>
                targets.all (fun target => mutableLVal fuel env target)
            | _ => false
end

private def strike? : Path → PartialTy → Option PartialTy
  | [], .ty ty => some (.undef ty)
  | _ :: path, .box inner => do
      some (.box (← strike? path inner))
  | _, _ => none

private def envMove? (env : FiniteEnv) (lv : LVal) : Option FiniteEnv := do
  let slot ← env.lookup (LVal.base lv)
  let struck ← strike? (LVal.path lv) slot.ty
  some (env.update (LVal.base lv) { slot with ty := struck })

private def valueTy? (typing : StoreTyping) : Value → Option Ty
  | .unit => some .unit
  | .int _ => some .int
  | .bool _ => some .bool
  | .ref ref => typing.tyOf ref.location

private def containedBorrowsWellFormed (fuel : Nat) (env : FiniteEnv) : Bool :=
  env.entries.all (fun entry =>
    (partialTyBorrows entry.2.ty).all (fun borrow =>
      borrowTargetsWellFormed fuel env borrow.2 entry.2.lifetime))

private def coherent (fuel : Nat) (env : FiniteEnv) : Bool :=
  env.entries.all (fun entry =>
    (partialTyBorrows entry.2.ty).all (fun borrow =>
      match lvalTargetsType? fuel env borrow.2 with
      | some (.ty _, _) => true
      | _ => false))

private def rankOf? : Nat → FiniteEnv → Name → Option Nat
  | 0, _, _ => none
  | fuel + 1, env, name =>
      match env.lookup name with
      | none => some 0
      | some slot =>
          let deps := PartialTy.vars slot.ty
          let ranks := deps.map (rankOf? fuel env)
          if ranks.any Option.isNone then
            none
          else
            some (1 + ranks.foldl (fun maxRank rank =>
              Nat.max maxRank (rank.getD 0)) 0)

private def linearizable (env : FiniteEnv) : Bool :=
  let fuel := (envNames env).length + 1
  env.entries.all (fun entry =>
    match rankOf? fuel env entry.1 with
    | none => false
    | some rootRank =>
        (PartialTy.vars entry.2.ty).all (fun dep =>
          match rankOf? fuel env dep with
          | some depRank => depRank < rootRank
          | none => false))

private def wellFormedKit (fuel : Nat) (env : FiniteEnv) : Bool :=
  containedBorrowsWellFormed fuel env && coherent fuel env && linearizable env

private def envJoin? (left right : FiniteEnv) : Option FiniteEnv :=
  let names := unionNames left.support right.support
  names.foldlM (init := FiniteEnv.empty) (fun result name => do
    match left.lookup name, right.lookup name with
    | some leftSlot, some rightSlot =>
        if leftSlot.lifetime == rightSlot.lifetime then
          let ty ← partialTyJoin? leftSlot.ty rightSlot.ty
          pure (result.update name { ty := ty, lifetime := leftSlot.lifetime })
        else
          none
    | none, none => pure result
    | _, _ => none)

private def envJoinSameShape (branch join : FiniteEnv) : Bool :=
  branch.support.all (fun name =>
    match branch.lookup name, join.lookup name with
    | some branchSlot, some joinSlot => partialTySameShape branchSlot.ty joinSlot.ty
    | _, _ => false)

private def tyBorrowSafeAgainstEnv (env : FiniteEnv) (ty : Ty) : Bool :=
  let tyBorrows := tyBorrows ty
  let envBorrows := envBorrowEdges env
  let leftSafe :=
    tyBorrows.all (fun tyBorrow =>
      if tyBorrow.1 then
        envBorrows.all (fun envBorrow =>
          tyBorrow.2.all (fun targetMutable =>
            envBorrow.2.2.all (fun targetOther =>
              !pathConflicts targetMutable targetOther)))
      else
        true)
  let rightSafe :=
    envBorrows.all (fun envBorrow =>
      if envBorrow.2.1 then
        tyBorrows.all (fun tyBorrow =>
          envBorrow.2.2.all (fun targetMutable =>
            tyBorrow.2.all (fun targetOther =>
              !pathConflicts targetMutable targetOther)))
      else
        true)
  leftSafe && rightSafe

private def borrowSafeRoot (env : FiniteEnv) (root : Name) : Bool :=
  let rootMutableBorrows :=
    (envBorrowEdges env).filter (fun edge => edge.1 == root && edge.2.1)
  let allBorrows := envBorrowEdges env
  rootMutableBorrows.all (fun rootBorrow =>
    allBorrows.all (fun otherBorrow =>
      rootBorrow.2.2.all (fun targetMutable =>
        otherBorrow.2.2.all (fun targetOther =>
          !pathConflicts targetMutable targetOther || root == otherBorrow.1))))

private def mutableBorrowTargetsOfRoot (env : FiniteEnv) (root : Name) :
    List LVal :=
  (envBorrowEdges env).foldl
    (fun targets edge =>
      if edge.1 == root && edge.2.1 then unionLVals targets edge.2.2 else targets)
    []

private def guardClosure (env : FiniteEnv) : Nat → List Name → List Name → List Name
  | 0, seen, _ => seen
  | _fuel + 1, seen, [] => seen
  | fuel + 1, seen, root :: rest =>
      if seen.contains root then
        guardClosure env fuel seen rest
      else
        let next := (mutableBorrowTargetsOfRoot env root).map LVal.base
        guardClosure env fuel (seen ++ [root]) (unionNames rest next)

private def assignmentBorrowSafety (env : FiniteEnv) : LVal → Bool
  | .var _ => true
  | .deref source =>
      let roots := guardClosure env ((envNames env).length + 1) [] [LVal.base source]
      roots.all (borrowSafeRoot env)

mutual
  private def updateAtPath? (fuel rank : Nat) (env : FiniteEnv)
      (path : Path) (oldTy : PartialTy) (rhsTy : Ty) :
      Option (FiniteEnv × PartialTy) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match path with
        | [] =>
            if rank == 0 then
              some (env, .ty rhsTy)
            else if shapeCompatiblePartialTy fuel env oldTy (.ty rhsTy) then
              match partialTyJoin? oldTy (.ty rhsTy) with
              | some joined => some (env, joined)
              | none => none
            else
              none
        | _ :: rest =>
            match oldTy with
            | .box inner => do
                let (env₂, updatedInner) ← updateAtPath? fuel rank env rest inner rhsTy
                some (env₂, .box updatedInner)
            | .ty (.borrow true targets) => do
                let env₂ ← writeBorrowTargets? fuel (rank + 1) env rest targets rhsTy
                some (env₂, oldTy)
            | _ => none

  private def writeBorrowTargets? (fuel rank : Nat) (env : FiniteEnv)
      (path : Path) (targets : List LVal) (rhsTy : Ty) : Option FiniteEnv :=
    match targets with
    | [] => some env
    | [target] => envWrite? fuel rank env (prependPath path target) rhsTy
    | target :: rest => do
        let updated ← envWrite? fuel rank env (prependPath path target) rhsTy
        let restUpdated ← writeBorrowTargets? fuel rank env path rest rhsTy
        envJoin? updated restUpdated

  private def envWrite? (fuel rank : Nat) (env : FiniteEnv)
      (lv : LVal) (rhsTy : Ty) : Option FiniteEnv := do
    let slot ← env.lookup (LVal.base lv)
    let (env₂, updatedTy) ← updateAtPath? fuel rank env (LVal.path lv) slot.ty rhsTy
    some (env₂.update (LVal.base lv) { slot with ty := updatedTy })
end

private def targetInBorrowTargets (target : LVal) (borrows : List (Bool × List LVal)) :
    Bool :=
  borrows.any (fun borrow => borrow.2.contains target)

private def rhsBorrowTargetsBelow (envBefore result : FiniteEnv) (rhsTy : Ty) :
    Bool :=
  let fuel := (envNames envBefore).length + (envNames result).length + 1
  let rhsBorrows := tyBorrows rhsTy
  let resultBorrows := envBorrowEdges result
  let rankBelow :=
    result.entries.all (fun entry =>
      (partialTyBorrows entry.2.ty).all (fun borrow =>
        borrow.2.all (fun target =>
          if targetInBorrowTargets target rhsBorrows then
            match rankOf? fuel result (LVal.base target),
                rankOf? fuel result entry.1 with
            | some targetRank, some rootRank => targetRank < rootRank
            | _, _ => false
          else
            true)))
  let fanoutSafe :=
    resultBorrows.all (fun left =>
      resultBorrows.all (fun right =>
        left.2.2.all (fun leftTarget =>
          right.2.2.all (fun rightTarget =>
            if left.2.1 && pathConflicts leftTarget rightTarget &&
                targetInBorrowTargets leftTarget rhsBorrows &&
                targetInBorrowTargets rightTarget rhsBorrows then
              left.1 == right.1
            else
              true))))
  rankBelow && fanoutSafe

private def isLifetimeChild (parent child : Lifetime) : Bool :=
  match child.path.drop parent.path.length with
  | [_] => parent.path.isPrefixOf child.path
  | _ => false

private partial def termDiverges : Term → Bool
  | .missing => true
  | .block _ terms => terms.any termDiverges
  | _ => false

mutual
  def checkTerm? (fuel : Nat) (env : FiniteEnv) (typing : StoreTyping)
      (lifetime : Lifetime) (term : Term) : Except String CheckResult :=
    match fuel with
    | 0 => .error "borrow checker fuel exhausted"
    | fuel + 1 =>
        match term with
        | .val value => do
            let ty ← fromOption "value has no store type" (valueTy? typing value)
            pure ⟨ty, env⟩
        | .missing =>
            .error "cannot infer type for missing; use checkTermAs?"
        | .copy lv => do
            let (partialTy, _) ←
              fromOption "copy operand is not typeable" (lvalType? fuel env lv)
            let ty ←
              match partialTy with
              | PartialTy.ty ty => pure ty
              | _ => .error "copy operand is not fully initialized"
            ensure (copyTy ty) "copy operand is not copyable"
            ensure (!readProhibited env lv) "copy is read-prohibited"
            pure ⟨ty, env⟩
        | .move lv => do
            let (partialTy, _) ←
              fromOption "move operand is not typeable" (lvalType? fuel env lv)
            let ty ←
              match partialTy with
              | PartialTy.ty ty => pure ty
              | _ => .error "move operand is not fully initialized"
            ensure (!writeProhibited env lv) "move is write-prohibited"
            let moved ← fromOption "move cannot strike operand" (envMove? env lv)
            pure ⟨ty, moved⟩
        | .borrow mutable lv => do
            let (partialTy, _) ←
              fromOption "borrow operand is not typeable" (lvalType? fuel env lv)
            match partialTy with
            | PartialTy.ty _ =>
                if mutable then
                  ensure (mutableLVal fuel env lv) "mutable borrow operand is immutable"
                  ensure (!writeProhibited env lv) "mutable borrow is write-prohibited"
                  pure ⟨.borrow true [lv], env⟩
                else
                  ensure (!readProhibited env lv) "immutable borrow is read-prohibited"
                  pure ⟨.borrow false [lv], env⟩
            | _ => .error "borrow operand is not fully initialized"
        | .box operand => do
            let result ← checkTerm? fuel env typing lifetime operand
            pure ⟨.box result.ty, result.env⟩
        | .block blockLifetime terms => do
            ensure (isLifetimeChild lifetime blockLifetime)
              "block lifetime is not a child of current lifetime"
            let result ← checkTermList? fuel env typing blockLifetime terms
            ensure (wellFormedTy fuel result.env result.ty lifetime)
              "block result type is not well-formed"
            pure ⟨result.ty, result.env.dropLifetime blockLifetime⟩
        | .letMut name initialiser => do
            ensure (env.fresh name) "declaration is not fresh in input environment"
            let result ← checkTerm? fuel env typing lifetime initialiser
            ensure (result.env.fresh name)
              "declaration is not fresh in post-initializer environment"
            let env' := result.env.update name { ty := .ty result.ty, lifetime := lifetime }
            ensure (wellFormedKit fuel env') "declaration result environment is not well formed"
            pure ⟨.unit, env'⟩
        | .assign lhs rhs => do
            let (oldTy, targetLifetime) ←
              fromOption "assignment lhs is not typeable" (lvalType? fuel env lhs)
            let rhsResult ← checkTerm? fuel env typing lifetime rhs
            ensure (assignmentBorrowSafety rhsResult.env lhs)
              "assignment-local borrow authority failed"
            let (oldTyAfter, targetLifetimeAfter) ←
              fromOption "assignment lhs is not typeable after rhs"
                (lvalType? fuel rhsResult.env lhs)
            ensure (oldTyAfter == oldTy && targetLifetimeAfter == targetLifetime)
              "assignment lhs type changed while checking rhs"
            ensure (shapeCompatiblePartialTy fuel rhsResult.env oldTy (.ty rhsResult.ty))
              "assignment rhs shape is incompatible with lhs"
            ensure (wellFormedTy fuel rhsResult.env rhsResult.ty targetLifetime)
              "assignment rhs type is not well-formed at target lifetime"
            let written ←
              fromOption "assignment environment write failed"
                (envWrite? fuel 0 rhsResult.env lhs rhsResult.ty)
            ensure (rhsBorrowTargetsBelow rhsResult.env written rhsResult.ty)
              "assignment rhs borrow targets are not below written roots"
            ensure (containedBorrowsWellFormed fuel written && linearizable written)
              "assignment result environment violates containment or linearization"
            ensure (!writeProhibited written lhs)
              "assignment result leaves lhs write-prohibited"
            pure ⟨.unit, written⟩
        | .eq lhs rhs => do
            let lhsResult ← checkTerm? fuel env typing lifetime lhs
            ensure (copyTy lhsResult.ty) "equality lhs is not copyable"
            let ghost := freshGhostName lhsResult.env rhs
            ensure (lhsResult.env.fresh ghost) "generated ghost name is not fresh"
            let ghostEnv :=
              lhsResult.env.update ghost { ty := .ty lhsResult.ty, lifetime := lifetime }
            discard <| checkTerm? fuel ghostEnv typing lifetime rhs
            let rhsResult ← checkTerm? fuel lhsResult.env typing lifetime rhs
            ensure (copyTy rhsResult.ty) "equality rhs is not copyable"
            ensure (shapeCompatiblePartialTy fuel rhsResult.env
              (.ty lhsResult.ty) (.ty rhsResult.ty))
              "equality operand shapes are incompatible"
            pure ⟨.bool, rhsResult.env⟩
        | .ite condition trueBranch falseBranch => do
            let conditionResult ← checkTerm? fuel env typing lifetime condition
            ensure (conditionResult.ty == .bool) "if condition is not bool"
            let trueResult ← checkTerm? fuel conditionResult.env typing lifetime trueBranch
            let falseResult ← checkTerm? fuel conditionResult.env typing lifetime falseBranch
            match partialTyJoin? (.ty trueResult.ty) (.ty falseResult.ty),
                envJoin? trueResult.env falseResult.env with
            | some (.ty joinTy), some joinEnv =>
                ensure (envJoinSameShape trueResult.env joinEnv)
                  "if true branch shape does not match join"
                ensure (envJoinSameShape falseResult.env joinEnv)
                  "if false branch shape does not match join"
                ensure (wellFormedTy fuel joinEnv joinTy lifetime)
                  "if result type is not well-formed"
                ensure (wellFormedKit fuel joinEnv)
                  "if joined environment is not well formed"
                ensure (tyBorrowSafeAgainstEnv joinEnv joinTy)
                  "if result type is not borrow-safe against join"
                pure ⟨joinTy, joinEnv⟩
            | _, _ =>
                if termDiverges falseBranch then
                  pure trueResult
                else
                  .error "if branch types/environments do not join"
        | .whileLoop bodyLifetime condition body =>
            checkWhile? fuel env typing lifetime bodyLifetime condition body
        | .whileCond .. =>
            .error "runtime whileCond form is not source-checkable"
        | .whileBody .. =>
            .error "runtime whileBody form is not source-checkable"

  def checkTermAs? (fuel : Nat) (env : FiniteEnv) (typing : StoreTyping)
      (lifetime : Lifetime) (term : Term) (expected : Ty) :
      Except String CheckResult :=
    match fuel with
    | 0 => .error "borrow checker fuel exhausted"
    | fuel + 1 =>
        match term with
        | .missing => do
            ensure (wellFormedTy fuel env expected lifetime)
              "missing expected type is not well-formed"
            ensure (tyLoanFree expected) "missing expected type is not loan-free"
            pure ⟨expected, env⟩
        | _ => do
            let result ← checkTerm? fuel env typing lifetime term
            ensure (result.ty == expected) "term inferred type differs from expected type"
            pure result

  def checkTermList? (fuel : Nat) (env : FiniteEnv) (typing : StoreTyping)
      (lifetime : Lifetime) : List Term → Except String CheckResult
    | [] => .error "empty block has no type"
    | [term] => checkTerm? fuel env typing lifetime term
    | term :: rest => do
        let head ← checkTerm? fuel env typing lifetime term
        checkTermList? fuel head.env typing lifetime rest

  private def checkStrictWhile? (fuel : Nat) (env : FiniteEnv)
      (typing : StoreTyping) (lifetime bodyLifetime : Lifetime)
      (condition body : Term) : Except String CheckResult := do
    ensure (isLifetimeChild lifetime bodyLifetime)
      "while body lifetime is not a child of current lifetime"
    let conditionResult ← checkTerm? fuel env typing lifetime condition
    ensure (conditionResult.ty == .bool) "while condition is not bool"
    let bodyResult ← checkTerm? fuel conditionResult.env typing bodyLifetime body
    ensure (wellFormedTy fuel bodyResult.env bodyResult.ty lifetime)
      "while body result type is not well-formed"
    ensure (envEqOnSupport (bodyResult.env.dropLifetime bodyLifetime) env)
      "strict while body does not restore entry environment"
    pure ⟨.unit, conditionResult.env⟩

  private def checkWhileJoinLoop? (iterations fuel : Nat) (entry inv : FiniteEnv)
      (typing : StoreTyping) (lifetime bodyLifetime : Lifetime)
      (condition body : Term) : Except String CheckResult :=
    match iterations with
    | 0 => .error "while-join invariant iteration did not converge"
    | iterations + 1 => do
        let conditionResult ← checkTerm? fuel inv typing lifetime condition
        ensure (conditionResult.ty == .bool) "while-join condition is not bool"
        let bodyResult ← checkTerm? fuel conditionResult.env typing bodyLifetime body
        ensure (wellFormedTy fuel bodyResult.env bodyResult.ty lifetime)
          "while-join body result type is not well-formed"
        let back := bodyResult.env.dropLifetime bodyLifetime
        let nextInv ←
          fromOption "while-join entry/back environments do not join"
            (envJoin? entry back)
        ensure (envJoinSameShape entry nextInv)
          "while-join entry shape does not match invariant"
        ensure (envJoinSameShape back nextInv)
          "while-join back-edge shape does not match invariant"
        ensure (wellFormedKit fuel nextInv)
          "while-join invariant environment is not well formed"
        if envEqOnSupport nextInv inv then
          let entryCondition ← checkTerm? fuel entry typing lifetime condition
          ensure (entryCondition.ty == .bool) "entry-side while condition is not bool"
          discard <| checkTerm? fuel entryCondition.env typing bodyLifetime body
          pure ⟨.unit, conditionResult.env⟩
        else
          checkWhileJoinLoop? iterations fuel entry nextInv typing lifetime
            bodyLifetime condition body

  private def checkWhileJoin? (fuel : Nat) (env : FiniteEnv)
      (typing : StoreTyping) (lifetime bodyLifetime : Lifetime)
      (condition body : Term) : Except String CheckResult := do
    ensure (isLifetimeChild lifetime bodyLifetime)
      "while body lifetime is not a child of current lifetime"
    checkWhileJoinLoop? fuel fuel env env typing lifetime bodyLifetime condition body

  private def checkWhile? (fuel : Nat) (env : FiniteEnv)
      (typing : StoreTyping) (lifetime bodyLifetime : Lifetime)
      (condition body : Term) : Except String CheckResult :=
    match checkStrictWhile? fuel env typing lifetime bodyLifetime condition body with
    | .ok result => .ok result
    | .error _ =>
        if termDiverges body then
          .error "diverging while bodies require an expected body type in this checker"
        else
          checkWhileJoin? fuel env typing lifetime bodyLifetime condition body
end

def checkProgram? (fuel : Nat) (term : Term) : Except String CheckResult :=
  checkTerm? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term

def CheckResult.matches (result : CheckResult) (expectedTy : Ty)
    (expectedEnv : FiniteEnv) : Bool :=
  result.ty == expectedTy && result.env.sameBindings expectedEnv

def checkTermMatches? (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term)
    (expectedTy : Ty) (expectedEnv : FiniteEnv) : Bool :=
  match checkTerm? fuel env typing lifetime term with
  | .ok result => result.matches expectedTy expectedEnv
  | .error _ => false

def checkTermListMatches? (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (terms : List Term)
    (expectedTy : Ty) (expectedEnv : FiniteEnv) : Bool :=
  match checkTermList? fuel env typing lifetime terms with
  | .ok result => result.matches expectedTy expectedEnv
  | .error _ => false

def checkTermRejects? (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term) : Bool :=
  !(checkTerm? fuel env typing lifetime term).isOk

def checkAssignmentBorrowSafety? (env : FiniteEnv) (lhs : LVal) : Bool :=
  assignmentBorrowSafety env lhs

/--
Proof-facing bridge for a particular checker run: the executable checker
computes the expected type and finite output environment, and the same input
and output environments support the declarative `TermTyping` judgment consumed
by progress and preservation.
-/
def CheckedTermTypingWitness (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term)
    (expectedTy : Ty) (expectedEnv : FiniteEnv) : Prop :=
  checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv = true ∧
    TermTyping env.toEnv typing lifetime term expectedTy expectedEnv.toEnv

namespace CheckedTermTypingWitness

theorem checked {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv} :
    CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv →
      checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv = true :=
  And.left

theorem typing {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv} :
    CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv →
      TermTyping env.toEnv typing lifetime term expectedTy expectedEnv.toEnv :=
  And.right

theorem typable {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv} :
    CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv →
      ∃ env₂ ty, TermTyping env.toEnv typing lifetime term ty env₂ := by
  intro h
  exact ⟨expectedEnv.toEnv, expectedTy, h.typing⟩

end CheckedTermTypingWitness

/--
Type-level certificate form of `CheckedTermTypingWitness`.

Unlike the proposition above, this can be returned under `Option`: the executable
boolean at that boundary is simply whether a certified witness was constructed.
-/
structure CertifiedTermCheck (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term)
    (expectedTy : Ty) (expectedEnv : FiniteEnv) : Type where
  checked :
    checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv = true
  typing :
    TermTyping env.toEnv typing lifetime term expectedTy expectedEnv.toEnv

namespace CertifiedTermCheck

def ofWitness {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (witness :
      CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv) :
    CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv :=
  { checked := witness.checked
    typing := witness.typing }

def toWitness {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv) :
    CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv :=
  ⟨certificate.checked, certificate.typing⟩

def found? {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate? :
      Option (CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv)) :
    Bool :=
  certificate?.isSome

theorem sound {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv) :
    TermTyping env.toEnv typing lifetime term expectedTy expectedEnv.toEnv :=
  certificate.typing

theorem check_matches {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv) :
    checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv = true :=
  certificate.checked

theorem typable {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv) :
    ∃ env₂ ty, TermTyping env.toEnv typing lifetime term ty env₂ := by
  exact ⟨expectedEnv.toEnv, expectedTy, certificate.typing⟩

def const {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.val value) ty env = true)
    (valueTyping : ValueTyping typing value ty) :
    CertifiedTermCheck fuel env typing lifetime (.val value) ty env :=
  { checked := checked
    typing := TermTyping.const valueTyping }

def copy {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.copy lv) ty env = true)
    (lvalTyping : LValTyping env.toEnv lv (.ty ty) valueLifetime)
    (copyTy : CopyTy ty)
    (notReadProhibited : ¬ ReadProhibited env.toEnv lv) :
    CertifiedTermCheck fuel env typing lifetime (.copy lv) ty env :=
  { checked := checked
    typing := TermTyping.copy lvalTyping copyTy notReadProhibited }

def mutBorrow {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.borrow true lv)
        (.borrow true [lv]) env = true)
    (lvalTyping : LValTyping env.toEnv lv (.ty ty) valueLifetime)
    (mutable : Mutable env.toEnv lv)
    (notWriteProhibited : ¬ WriteProhibited env.toEnv lv) :
    CertifiedTermCheck fuel env typing lifetime (.borrow true lv)
      (.borrow true [lv]) env :=
  { checked := checked
    typing := TermTyping.mutBorrow lvalTyping mutable notWriteProhibited }

def immBorrow {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.borrow false lv)
        (.borrow false [lv]) env = true)
    (lvalTyping : LValTyping env.toEnv lv (.ty ty) valueLifetime)
    (notReadProhibited : ¬ ReadProhibited env.toEnv lv) :
    CertifiedTermCheck fuel env typing lifetime (.borrow false lv)
      (.borrow false [lv]) env :=
  { checked := checked
    typing := TermTyping.immBorrow lvalTyping notReadProhibited }

def assign {fuel : Nat} {env rhsEnv outEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.assign lhs rhs) .unit
        outEnv = true)
    (lhsBefore : LValTyping env.toEnv lhs oldTy targetLifetime)
    (rhsCert : CertifiedTermCheck fuel env typing lifetime rhs rhsTy rhsEnv)
    (assignmentSafe : AssignmentBorrowSafety rhsEnv.toEnv lhs)
    (lhsAfter : LValTyping rhsEnv.toEnv lhs oldTy targetLifetime)
    (shape : ShapeCompatible rhsEnv.toEnv oldTy (.ty rhsTy))
    (wellFormed : WellFormedTy rhsEnv.toEnv rhsTy targetLifetime)
    (write : EnvWrite 0 rhsEnv.toEnv lhs rhsTy outEnv.toEnv)
    (below :
      ∃ φ, LinearizedBy φ rhsEnv.toEnv ∧
        EnvWriteRhsBorrowTargetsBelow φ outEnv.toEnv rhsTy)
    (coherence :
      EnvWriteCoherenceObligations rhsEnv.toEnv outEnv.toEnv (LVal.base lhs))
    (contained : ContainedBorrowsWellFormed outEnv.toEnv)
    (notWriteProhibited : ¬ WriteProhibited outEnv.toEnv lhs) :
    CertifiedTermCheck fuel env typing lifetime (.assign lhs rhs) .unit outEnv :=
  { checked := checked
    typing :=
      TermTyping.assign lhsBefore rhsCert.typing assignmentSafe lhsAfter shape
        wellFormed write below coherence contained notWriteProhibited }

def equal {fuel : Nat} {env lhsEnv rhsEnv ghostEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {lhs rhs : Term}
    {lhsTy rhsTy ghostRhsTy : Ty} {ghost : Name}
    (checked :
      checkTermMatches? fuel env typing lifetime (.eq lhs rhs) .bool
        rhsEnv = true)
    (lhsCert : CertifiedTermCheck fuel env typing lifetime lhs lhsTy lhsEnv)
    (freshGhost : lhsEnv.toEnv.fresh ghost)
    (ghostCert :
      CertifiedTermCheck fuel
        (lhsEnv.update ghost { ty := .ty lhsTy, lifetime := lifetime })
        typing lifetime rhs ghostRhsTy ghostEnv)
    (rhsCert : CertifiedTermCheck fuel lhsEnv typing lifetime rhs rhsTy rhsEnv)
    (lhsCopy : CopyTy lhsTy)
    (rhsCopy : CopyTy rhsTy)
    (shape : ShapeCompatible rhsEnv.toEnv (.ty lhsTy) (.ty rhsTy)) :
    CertifiedTermCheck fuel env typing lifetime (.eq lhs rhs) .bool rhsEnv :=
  { checked := checked
    typing :=
      TermTyping.eq (ghost := ghost) lhsCert.typing freshGhost
        (by simpa [FiniteEnv.toEnv_update] using ghostCert.typing)
        rhsCert.typing lhsCopy rhsCopy shape }

def ite {fuel : Nat} {env conditionEnv trueEnv falseEnv joinEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term} {trueTy falseTy joinTy : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime
        (.ite condition trueBranch falseBranch) joinTy joinEnv = true)
    (conditionCert :
      CertifiedTermCheck fuel env typing lifetime condition .bool conditionEnv)
    (trueCert :
      CertifiedTermCheck fuel conditionEnv typing lifetime trueBranch trueTy
        trueEnv)
    (falseCert :
      CertifiedTermCheck fuel conditionEnv typing lifetime falseBranch falseTy
        falseEnv)
    (typeJoin : PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy))
    (envJoin : EnvJoin trueEnv.toEnv falseEnv.toEnv joinEnv.toEnv)
    (trueSameShape : EnvJoinSameShape trueEnv.toEnv joinEnv.toEnv)
    (falseSameShape : EnvJoinSameShape falseEnv.toEnv joinEnv.toEnv)
    (wellFormed : WellFormedTy joinEnv.toEnv joinTy lifetime)
    (contained : ContainedBorrowsWellFormed joinEnv.toEnv)
    (coherent : Coherent joinEnv.toEnv)
    (linearizable : Linearizable joinEnv.toEnv)
    (typeBorrowSafe : TyBorrowSafeAgainstEnv joinEnv.toEnv joinTy) :
    CertifiedTermCheck fuel env typing lifetime
      (.ite condition trueBranch falseBranch) joinTy joinEnv :=
  { checked := checked
    typing :=
      TermTyping.ite conditionCert.typing trueCert.typing falseCert.typing
        typeJoin envJoin trueSameShape falseSameShape wellFormed contained
        coherent linearizable typeBorrowSafe }

end CertifiedTermCheck

/--
Proof-carrying rejection certificate.

This is intentionally separate from `checkTermRejects?`: the boolean says the
executable search found no witness, while `notyping` is the logical
non-typability proof.  A failed checker run alone is not used as a completeness
theorem.
-/
structure CertifiedTermReject (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term) : Type where
  checked : checkTermRejects? fuel env typing lifetime term = true
  notyping :
    ¬ ∃ ty outEnv, TermTyping env.toEnv typing lifetime term ty outEnv

namespace CertifiedTermReject

def found? {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
    (certificate? :
      Option (CertifiedTermReject fuel env typing lifetime term)) : Bool :=
  certificate?.isSome

theorem rejected {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
    (certificate : CertifiedTermReject fuel env typing lifetime term) :
    checkTermRejects? fuel env typing lifetime term = true :=
  certificate.checked

theorem sound {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
    (certificate : CertifiedTermReject fuel env typing lifetime term) :
    ¬ ∃ ty outEnv, TermTyping env.toEnv typing lifetime term ty outEnv :=
  certificate.notyping

end CertifiedTermReject

/-- Proof-carrying counterpart of `checkTermList?` for block bodies. -/
structure CertifiedTermListCheck (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (terms : List Term)
    (expectedTy : Ty) (expectedEnv : FiniteEnv) : Type where
  checked :
    checkTermListMatches? fuel env typing lifetime terms expectedTy expectedEnv =
      true
  typing :
    TermListTyping env.toEnv typing lifetime terms expectedTy expectedEnv.toEnv

namespace CertifiedTermListCheck

def singleton {fuel : Nat} {env outEnv : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (checked :
      checkTermListMatches? fuel env typing lifetime [term] ty outEnv = true)
    (termCert : CertifiedTermCheck fuel env typing lifetime term ty outEnv) :
    CertifiedTermListCheck fuel env typing lifetime [term] ty outEnv :=
  { checked := checked
    typing := TermListTyping.singleton termCert.typing }

def cons {fuel : Nat} {env midEnv outEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {rest : List Term} {termTy finalTy : Ty}
    (checked :
      checkTermListMatches? fuel env typing lifetime (term :: rest) finalTy
        outEnv = true)
    (headCert : CertifiedTermCheck fuel env typing lifetime term termTy midEnv)
    (restCert :
      CertifiedTermListCheck fuel midEnv typing lifetime rest finalTy outEnv) :
    CertifiedTermListCheck fuel env typing lifetime (term :: rest) finalTy
      outEnv :=
  { checked := checked
    typing := TermListTyping.cons headCert.typing restCert.typing }

theorem sound {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {terms : List Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermListCheck fuel env typing lifetime terms expectedTy
        expectedEnv) :
    TermListTyping env.toEnv typing lifetime terms expectedTy
      expectedEnv.toEnv :=
  certificate.typing

end CertifiedTermListCheck

namespace CertifiedTermCheck

def block {fuel : Nat} {env bodyEnv outEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.block blockLifetime terms)
        ty outEnv = true)
    (child : LifetimeChild lifetime blockLifetime)
    (bodyCert :
      CertifiedTermListCheck fuel env typing blockLifetime terms ty bodyEnv)
    (wellFormed : WellFormedTy bodyEnv.toEnv ty lifetime)
    (dropEq : outEnv.toEnv = bodyEnv.toEnv.dropLifetime blockLifetime) :
    CertifiedTermCheck fuel env typing lifetime (.block blockLifetime terms) ty
      outEnv :=
  { checked := checked
    typing := TermTyping.block child bodyCert.typing wellFormed dropEq }

end CertifiedTermCheck

/--
Run the executable checker on decidable computation goals.

This tactic is deliberately narrow: it does not search for declarative typing
side conditions or project from proof-carrying certificates.  It is the tactic
to use when the goal is the checker verdict itself, for example
`checkTermMatches? ... = true` or `borrowReject? ... = true`.
-/
syntax (name := borrow_run_tactic) "borrow_run" : tactic

macro_rules
  | `(tactic| borrow_run) => `(tactic| native_decide)

/--
Project facts from a proof-carrying borrow-checking certificate.

Bare `borrow_check` is kept as a compatibility alias for `borrow_run`.
`borrow_check using cert` is not a reflection theorem from a boolean checker
result; it only exposes the proof stored in `cert`.
-/
syntax (name := borrow_check_tactic) "borrow_check" (" using " term)? : tactic

macro_rules
  | `(tactic| borrow_check using $certificate) =>
      `(tactic|
        first
        | exact CertifiedTermCheck.sound $certificate
        | exact CertifiedTermCheck.toWitness $certificate
        | exact CertifiedTermCheck.check_matches $certificate
        | exact CertifiedTermCheck.typable $certificate
        | exact CertifiedTermListCheck.sound $certificate
        | exact CertifiedTermReject.sound $certificate
        | exact CertifiedTermReject.rejected $certificate
        | exact $certificate)
  | `(tactic| borrow_check) => `(tactic| borrow_run)

def borrowCheck? (fuel : Nat) (term : Term) : Bool :=
  (checkProgram? fuel term).isOk

def borrowReject? (fuel : Nat) (term : Term) : Bool :=
  !(checkProgram? fuel term).isOk

def checkProgramAs? (fuel : Nat) (term : Term) (expected : Ty) :
    Except String CheckResult :=
  checkTermAs? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term expected

/-! ## Reflection lemmas for checker soundness -/

private theorem valueTy?_sound {typing : StoreTyping} {value : Value} {ty : Ty} :
    valueTy? typing value = some ty → ValueTyping typing value ty := by
  intro h
  cases value with
  | unit =>
      simp [valueTy?] at h
      subst h
      exact ValueTyping.unit
  | int _ =>
      simp [valueTy?] at h
      subst h
      exact ValueTyping.int
  | bool _ =>
      simp [valueTy?] at h
      subst h
      exact ValueTyping.bool
  | ref ref =>
      exact ValueTyping.ref h

private theorem copyTy_sound {ty : Ty} :
    copyTy ty = true → CopyTy ty := by
  intro h
  cases ty with
  | unit => exact CopyTy.unit
  | int => exact CopyTy.int
  | bool => exact CopyTy.bool
  | borrow mutable targets =>
      cases mutable <;> simp [copyTy] at h
      exact CopyTy.immBorrow
  | box inner =>
      simp [copyTy] at h

private theorem tyLoanFree_sound : ∀ {ty : Ty},
    tyLoanFree ty = true → TyLoanFree ty
  | .unit, _ => by
      intro mutable targets hcontains
      cases hcontains
  | .int, _ => by
      intro mutable targets hcontains
      cases hcontains
  | .bool, _ => by
      intro mutable targets hcontains
      cases hcontains
  | .borrow borrowMutable borrowTargets, h => by
      intro mutable targets hcontains
      simp [tyLoanFree] at h
      cases hcontains with
      | here =>
          exact h
  | .box inner, h => by
      intro mutable targets hcontains
      simp [tyLoanFree] at h
      cases hcontains with
      | tyBox hinner =>
          exact tyLoanFree_sound h mutable targets hinner

private theorem lifetimeIntersection?_sound {left right intersection : Lifetime} :
    lifetimeIntersection? left right = some intersection →
      LifetimeIntersection left right intersection := by
  intro h
  unfold lifetimeIntersection? at h
  by_cases hleft : left.contains right
  · simp [hleft] at h
    subst h
    exact LifetimeIntersection.left (by simpa [LifetimeOutlives] using hleft)
  · by_cases hright : right.contains left
    · simp [hleft, hright] at h
      subst h
      exact LifetimeIntersection.right (by simpa [LifetimeOutlives] using hright)
    · simp [hleft, hright] at h

private theorem isLifetimeChild_sound {parent child : Lifetime} :
    isLifetimeChild parent child = true → LifetimeChild parent child := by
  intro h
  unfold isLifetimeChild at h
  generalize hdrop : child.path.drop parent.path.length = suffix at h
  cases suffix with
  | nil =>
      simp at h
  | cons label rest =>
      cases rest with
      | cons _ _ =>
          simp at h
      | nil =>
          simp at h
          refine ⟨label, ?_⟩
          have hprefix : parent.path <+: child.path := h
          have happ :
              parent.path ++ child.path.drop parent.path.length = child.path :=
            (List.prefix_iff_eq_append.mp hprefix)
          rw [hdrop] at happ
          exact happ.symm

private theorem partialTyStrengthens_borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal}
    {joined : PartialTy}
    (hleft : PartialTyStrengthens (.ty (.borrow mutable leftTargets)) joined)
    (hright : PartialTyStrengthens (.ty (.borrow mutable rightTargets)) joined) :
    PartialTyStrengthens
      (.ty (.borrow mutable (leftTargets ++ rightTargets))) joined := by
  cases hleft with
  | reflex =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hmem
        · exact hsubRight hmem)
  | borrow hsubLeft =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem)
  | intoUndef hinner =>
      rcases PartialTyStrengthens.from_borrow_inv hinner with
        ⟨targetTargets, rfl, hsubLeft⟩
      have hsubRight : rightTargets ⊆ targetTargets := by
        cases hright with
        | intoUndef hinner' =>
            exact PartialTyStrengthens.borrow_subset hinner'
      exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem))

mutual
  private theorem tyJoin?_sound :
      ∀ {left right join : Ty},
        tyJoin? left right = some join →
          PartialTyJoin (.ty left) (.ty right) (.ty join) := by
    intro left
    cases left with
    | unit =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        subst h
        exact PartialTyJoin.self (.ty .unit)
    | int =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        subst h
        exact PartialTyJoin.self (.ty .int)
    | bool =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        subst h
        exact PartialTyJoin.self (.ty .bool)
    | borrow mutable leftTargets =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        next mutable' rightTargets =>
          by_cases hmutable : mutable = mutable'
          · subst hmutable
            simp at h
            cases h
            constructor
            · intro candidate hcandidate
              simp at hcandidate
              rcases hcandidate with hcandidate | hcandidate
              · subst hcandidate
                exact PartialTyStrengthens.borrow
                  (by intro target htarget; exact List.mem_append_left _ htarget)
              · subst hcandidate
                exact PartialTyStrengthens.borrow
                  (by intro target htarget; exact List.mem_append_right _ htarget)
            · intro upper hupper
              exact partialTyStrengthens_borrow_append
                (hupper (by simp)) (hupper (by simp))
          · simp [hmutable] at h
    | box leftInner =>
        intro right join h
        cases right <;> simp [tyJoin?] at h
        next rightInner =>
          cases hinner : tyJoin? leftInner rightInner with
          | none =>
              simp [hinner] at h
          | some inner =>
              simp [hinner] at h
              cases h
              exact PartialTyUnion.tyBox (tyJoin?_sound hinner)

end

mutual
  private theorem lvalType?_sound :
      ∀ {fuel : Nat} {env : FiniteEnv} {lv : LVal}
        {partialTy : PartialTy} {lifetime : Lifetime},
        lvalType? fuel env lv = some (partialTy, lifetime) →
          LValTyping env.toEnv lv partialTy lifetime := by
    intro fuel
    cases fuel with
    | zero =>
        intro env lv partialTy lifetime h
        cases lv <;> simp [lvalType?] at h
    | succ fuel =>
        intro env lv partialTy lifetime h
        cases lv with
        | var name =>
            simp [lvalType?] at h
            cases hlookup : env.lookup name with
            | none =>
                simp [hlookup] at h
            | some slot =>
                simp [hlookup] at h
                rcases h with ⟨rfl, rfl⟩
                exact LValTyping.var (show env.toEnv.slotAt name = some slot from hlookup)
        | deref inner =>
            cases hinner : lvalType? fuel env inner with
            | none =>
                simp [lvalType?, hinner] at h
            | some result =>
                rcases result with ⟨innerTy, innerLifetime⟩
                cases innerTy with
                | ty ty =>
                    cases ty with
                    | borrow mutable targets =>
                        simp [lvalType?, hinner] at h
                        exact LValTyping.borrow
                          (lvalType?_sound hinner)
                          (lvalTargetsType?_sound h)
                    | unit =>
                        simp [lvalType?, hinner] at h
                    | int =>
                        simp [lvalType?, hinner] at h
                    | bool =>
                        simp [lvalType?, hinner] at h
                    | box _ =>
                        simp [lvalType?, hinner] at h
                | box innerPartial =>
                    simp [lvalType?, hinner] at h
                    rcases h with ⟨rfl, rfl⟩
                    exact LValTyping.box
                      (lvalType?_sound
                        (partialTy := .box innerPartial)
                        (lifetime := innerLifetime) hinner)
                | undef _ =>
                    simp [lvalType?, hinner] at h

  private theorem lvalTargetsType?_sound :
      ∀ {fuel : Nat} {env : FiniteEnv} {targets : List LVal}
        {partialTy : PartialTy} {lifetime : Lifetime},
        lvalTargetsType? fuel env targets = some (partialTy, lifetime) →
          LValTargetsTyping env.toEnv targets partialTy lifetime := by
    intro fuel env targets
    cases targets with
    | nil =>
        intro partialTy lifetime h
        simp [lvalTargetsType?] at h
    | cons target rest =>
        cases rest with
        | nil =>
            intro partialTy lifetime h
            cases htarget : lvalType? fuel env target with
            | none =>
                simp [lvalTargetsType?, htarget] at h
            | some result =>
                rcases result with ⟨targetTy, targetLifetime⟩
                cases targetTy with
                | ty ty =>
                    simp [lvalTargetsType?, htarget] at h
                    rcases h with ⟨rfl, rfl⟩
                    exact LValTargetsTyping.singleton
                      (lvalType?_sound
                        (partialTy := .ty ty)
                        (lifetime := targetLifetime) htarget)
                | box _ =>
                    simp [lvalTargetsType?, htarget] at h
                | undef _ =>
                    simp [lvalTargetsType?, htarget] at h
        | cons restHead restTail =>
            intro partialTy lifetime h
            cases htarget : lvalType? fuel env target with
            | none =>
                simp [lvalTargetsType?, htarget] at h
            | some targetResult =>
                rcases targetResult with ⟨targetTy, targetLifetime⟩
                cases targetTy with
                | ty headTy =>
                    cases hrest :
                        lvalTargetsType? fuel env (restHead :: restTail) with
                    | none =>
                        simp [lvalTargetsType?, htarget, hrest] at h
                    | some restResult =>
                        rcases restResult with ⟨restTy, restLifetime⟩
                        have restTyping :
                            LValTargetsTyping env.toEnv (restHead :: restTail)
                              restTy restLifetime :=
                          lvalTargetsType?_sound hrest
                        rcases LValTargetsTyping.output_full restTyping with
                          ⟨restFullTy, hrestFull⟩
                        subst hrestFull
                        cases hjoin : tyJoin? headTy restFullTy with
                        | none =>
                            simp [lvalTargetsType?, htarget, hrest,
                              partialTyJoin?, hjoin] at h
                        | some joinTy =>
                            cases hlifetime :
                                lifetimeIntersection? targetLifetime
                                  restLifetime with
                            | none =>
                                simp [lvalTargetsType?, htarget, hrest,
                                  partialTyJoin?, hjoin, hlifetime] at h
                            | some lifetime' =>
                                simp [lvalTargetsType?, htarget, hrest,
                                  partialTyJoin?, hjoin, hlifetime] at h
                                rcases h with ⟨rfl, rfl⟩
                                exact LValTargetsTyping.cons
                                  (lvalType?_sound htarget)
                                  restTyping
                                  (tyJoin?_sound hjoin)
                                  (lifetimeIntersection?_sound hlifetime)
                | box _ =>
                    simp [lvalTargetsType?, htarget] at h
                | undef _ =>
                    simp [lvalTargetsType?, htarget] at h
end

private theorem lookupEntries_mem {entries : List (Name × EnvSlot)}
    {name : Name} {slot : EnvSlot} :
    FiniteEnv.lookupEntries entries name = some slot →
      (name, slot) ∈ entries := by
  induction entries with
  | nil =>
      intro h
      simp [FiniteEnv.lookupEntries] at h
  | cons entry rest ih =>
      intro h
      rcases entry with ⟨entryName, entrySlot⟩
      by_cases hname : name = entryName
      · subst hname
        simp [FiniteEnv.lookupEntries] at h
        cases h
        exact List.mem_cons_self
      · simp [FiniteEnv.lookupEntries, hname] at h
        exact List.mem_cons_of_mem _ (ih h)

private theorem partialTyContainsBorrow_mem_aux {partialTy : PartialTy}
    {needle : Ty}
    (hcontains : PartialTyContains partialTy needle) :
    ∀ {mutable : Bool} {targets : List LVal},
      needle = .borrow mutable targets →
        (mutable, targets) ∈ partialTyBorrows partialTy := by
  induction hcontains with
  | here =>
      intro mutable targets hneedle
      cases hneedle
      simp [partialTyBorrows, tyBorrows]
  | tyBox _ ih =>
      intro mutable targets hneedle
      simpa [partialTyBorrows, tyBorrows] using ih hneedle
  | box _ ih =>
      intro mutable targets hneedle
      simpa [partialTyBorrows] using ih hneedle

private theorem partialTyContainsBorrow_mem {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyContains partialTy (.borrow mutable targets) →
      (mutable, targets) ∈ partialTyBorrows partialTy := by
  intro hcontains
  exact partialTyContainsBorrow_mem_aux hcontains rfl

private theorem envBorrowEdges_mem_of_entry {entries : List (Name × EnvSlot)}
    {entry : Name × EnvSlot} {borrow : Bool × List LVal} :
    entry ∈ entries →
      borrow ∈ partialTyBorrows entry.2.ty →
        (entry.1, borrow.1, borrow.2) ∈
          entries.foldr
            (fun entry edges =>
              (partialTyBorrows entry.2.ty).map
                  (fun borrow => (entry.1, borrow.1, borrow.2)) ++ edges)
            [] := by
  intro hentry hborrow
  induction entries with
  | nil =>
      cases hentry
  | cons head rest ih =>
      cases hentry with
      | head =>
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨borrow, hborrow, rfl⟩
      | tail _ hrest =>
          exact List.mem_append_right _ (ih hrest)

private theorem envBorrowEdges_of_contains {env : FiniteEnv}
    {root : Name} {mutable : Bool} {targets : List LVal} :
    env.toEnv ⊢ root ↝ Ty.borrow mutable targets →
      (root, mutable, targets) ∈ envBorrowEdges env := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  cases env with
  | mk entries =>
      have hentry : (root, slot) ∈ entries :=
        lookupEntries_mem hslot
      exact envBorrowEdges_mem_of_entry hentry
        (partialTyContainsBorrow_mem hcontainsTy)

private theorem readProhibited_false_sound {env : FiniteEnv} {lv : LVal} :
    readProhibited env lv = false →
      ¬ ReadProhibited env.toEnv lv := by
  intro hfalse hread
  rcases hread with ⟨root, targets, target, hcontains, htarget, hconflict⟩
  have hedge :
      (root, true, targets) ∈ envBorrowEdges env :=
    envBorrowEdges_of_contains hcontains
  have htargetConflict : pathConflicts target lv = true := by
    simpa [pathConflicts, PathConflicts] using hconflict
  have hany : readProhibited env lv = true := by
    rw [readProhibited, List.any_eq_true]
    refine ⟨(root, true, targets), hedge, ?_⟩
    simp [List.any_eq_true]
    exact ⟨target, htarget, htargetConflict⟩
  rw [hfalse] at hany
  cases hany

private theorem writeProhibited_false_sound {env : FiniteEnv} {lv : LVal} :
    writeProhibited env lv = false →
      ¬ WriteProhibited env.toEnv lv := by
  intro hfalse hwrite
  simp [writeProhibited] at hfalse
  rcases hfalse with ⟨hreadFalse, himmFalse⟩
  cases hwrite with
  | inl hread =>
      exact readProhibited_false_sound hreadFalse hread
  | inr himm =>
      rcases himm with
        ⟨root, targets, target, hcontains, htarget, hconflict⟩
      have hedge :
          (root, false, targets) ∈ envBorrowEdges env :=
        envBorrowEdges_of_contains hcontains
      have htargetConflict : pathConflicts target lv = true := by
        simpa [pathConflicts, PathConflicts] using hconflict
      have htargetFalse :=
        (himmFalse root).1 targets hedge target htarget
      rw [htargetConflict] at htargetFalse
      cases htargetFalse

mutual
  private theorem mutableLVal_sound :
      ∀ {fuel : Nat} {env : FiniteEnv} {lv : LVal},
        mutableLVal fuel env lv = true →
          Mutable env.toEnv lv := by
    intro fuel env lv
    cases lv with
    | var name =>
        intro h
        simp [mutableLVal] at h
        cases hlookup : env.lookup name with
        | none =>
            simp [hlookup] at h
        | some slot =>
            exact Mutable.var
              (show env.toEnv.slotAt name = some slot from hlookup)
    | deref inner =>
        intro h
        cases fuel with
        | zero =>
            simp [mutableLVal] at h
        | succ fuel =>
            cases htype : lvalType? fuel env inner with
            | none =>
                simp [mutableLVal, htype] at h
            | some result =>
                rcases result with ⟨partialTy, lifetime⟩
                cases partialTy with
                | box innerTy =>
                    simp [mutableLVal, htype] at h
                    exact Mutable.box
                      (lvalType?_sound htype)
                      (mutableLVal_sound h)
                | ty ty =>
                    cases ty with
                    | borrow mutable targets =>
                        cases mutable <;> simp [mutableLVal, htype] at h
                        exact Mutable.borrow
                          (lvalType?_sound htype)
                          (by
                            intro target htarget
                            exact mutableLVal_sound
                              (h target htarget))
                    | unit =>
                        simp [mutableLVal, htype] at h
                    | int =>
                        simp [mutableLVal, htype] at h
                    | bool =>
                        simp [mutableLVal, htype] at h
                    | box _ =>
                        simp [mutableLVal, htype] at h
                | undef _ =>
                    simp [mutableLVal, htype] at h
end

structure CertifiedLValFullType (fuel : Nat) (env : FiniteEnv)
    (lv : LVal) : Type where
  ty : Ty
  lifetime : Lifetime
  checked : lvalType? fuel env lv = some (.ty ty, lifetime)

namespace CertifiedLValFullType

theorem typing {fuel : Nat} {env : FiniteEnv} {lv : LVal}
    (certificate : CertifiedLValFullType fuel env lv) :
    LValTyping env.toEnv lv (.ty certificate.ty) certificate.lifetime :=
  lvalType?_sound certificate.checked

end CertifiedLValFullType

def certifyLValFullType? (fuel : Nat) (env : FiniteEnv) (lv : LVal) :
    Option (CertifiedLValFullType fuel env lv) :=
  match h : lvalType? fuel env lv with
  | some (.ty ty, lifetime) =>
      some { ty := ty, lifetime := lifetime, checked := h }
  | _ => none

namespace CertifiedTermCheck

def copyFromChecker {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    (lvalCert : CertifiedLValFullType fuel env lv)
    (checked :
      checkTermMatches? fuel env typing lifetime (.copy lv)
        lvalCert.ty env = true)
    (copyChecked : copyTy lvalCert.ty = true)
    (notReadChecked : readProhibited env lv = false) :
    CertifiedTermCheck fuel env typing lifetime (.copy lv) lvalCert.ty env :=
  { checked := by
      simpa using checked
    typing :=
      TermTyping.copy lvalCert.typing (copyTy_sound copyChecked)
        (readProhibited_false_sound notReadChecked) }

def copyFromCheckerAs {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {expectedTy : Ty}
    (lvalCert : CertifiedLValFullType fuel env lv)
    (typeEq : lvalCert.ty = expectedTy)
    (checked :
      checkTermMatches? fuel env typing lifetime (.copy lv) expectedTy env =
        true)
    (copyChecked : copyTy expectedTy = true)
    (notReadChecked : readProhibited env lv = false) :
    CertifiedTermCheck fuel env typing lifetime (.copy lv) expectedTy env := by
  subst typeEq
  exact copyFromChecker lvalCert checked copyChecked notReadChecked

def mutBorrowFromChecker {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    (lvalCert : CertifiedLValFullType fuel env lv)
    (checked :
      checkTermMatches? fuel env typing lifetime (.borrow true lv)
        (.borrow true [lv]) env = true)
    (mutableChecked : mutableLVal fuel env lv = true)
    (notWriteChecked : writeProhibited env lv = false) :
    CertifiedTermCheck fuel env typing lifetime (.borrow true lv)
      (.borrow true [lv]) env :=
  { checked := checked
    typing :=
      TermTyping.mutBorrow lvalCert.typing
        (mutableLVal_sound mutableChecked)
        (writeProhibited_false_sound notWriteChecked) }

end CertifiedTermCheck

syntax (name := borrow_cert_tactic) "borrow_cert" : tactic

macro_rules
  | `(tactic| borrow_cert) =>
      `(tactic|
        first
        | exact CertifiedTermCheck.mutBorrowFromChecker
            ((certifyLValFullType? _ _ _).get (by native_decide))
            (by borrow_run)
            (by native_decide)
            (by native_decide)
        | exact CertifiedTermCheck.copyFromCheckerAs
            ((certifyLValFullType? _ _ _).get (by native_decide))
            (by native_decide)
            (by borrow_run)
            (by native_decide)
            (by native_decide))

end Paper
end LwRust
