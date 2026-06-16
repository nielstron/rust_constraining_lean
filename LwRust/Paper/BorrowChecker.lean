import LwRust.Paper.Typing

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
  deriving BEq, Repr

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

def support (env : FiniteEnv) : List Name :=
  env.entries.foldl
    (fun names entry => if names.contains entry.1 then names else names ++ [entry.1])
    []

def toEnv (env : FiniteEnv) : Env :=
  { slotAt := env.lookup }

def dropLifetime (env : FiniteEnv) (lifetime : Lifetime) : FiniteEnv :=
  { entries := env.entries.filter (fun entry => entry.2.lifetime != lifetime) }

end FiniteEnv

structure CheckResult where
  ty : Ty
  env : FiniteEnv
  deriving BEq, Repr

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
  right.foldl insertLVal left

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

end CertifiedTermCheck

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

end Paper
end LwRust
