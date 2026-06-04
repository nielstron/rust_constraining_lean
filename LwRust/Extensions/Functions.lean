import LwRust.Core.BorrowChecker
import LwRust.Core.OperationalSemantics

/-!
Function extension.

Java source: `FeatherweightRust/src/featherweightrust/extensions/Functions.java`.

This module provides a function-aware checker/evaluator layered over the core
translation.  It covers first-order declarations, ordinary argument passing,
box signatures, direct borrow-typed parameters and direct return lifting (e.g.
identity functions returning a parameter), plus conservative side-effect lifting
for writes through mutable borrow parameters.

TODO: The Java implementation's declaration subtyping details are still only
approximated here.  Declaration result checking tracks the abstract outlives
relation induced by lowered signatures; call checking now enumerates candidate
abstract-lifetime bindings like `Functions.java`; and call return lifting uses
the subtype-driven borrow-hole search from the Java implementation.
-/

namespace LwRust
namespace Extensions
namespace Functions

open Core

inductive Signature where
  | unit
  | int
  | borrow (mutable : Bool) (lifetimeName : String) (sig : Signature)
  | box (sig : Signature)
  | tuple (fields : List Signature)
  deriving BEq, Repr

structure FunctionDeclaration where
  name : Name
  params : List (Name × Signature)
  ret : Signature
  body : Term
  deriving BEq, Repr

def invoke := Core.invoke

abbrev CheckM := Except String
abbrev EvalM := Except String

def fail {α : Type} (msg : String) : Except String α :=
  Except.error msg

def expectSome {α : Type} (msg : String) : Option α → Except String α
  | some x => Except.ok x
  | none => fail msg

namespace Signature

abbrev LifetimeBinding := List (String × Lifetime × Bool)

def LifetimeBinding.get (binding : LifetimeBinding) (name : String) : Option (Lifetime × Bool) :=
  match binding with
  | [] => none
  | (n, lifetime, locked) :: rest => if n == name then some (lifetime, locked) else get rest name

def LifetimeBinding.put (binding : LifetimeBinding) (name : String) (lifetime : Lifetime) (locked : Bool) :
    LifetimeBinding :=
  (name, lifetime, locked) :: binding.filter (fun entry => entry.fst != name)

def LifetimeBinding.constrainSubtype (binding : LifetimeBinding) (name : String) (lifetime : Lifetime)
    (invariant : Bool) : Option LifetimeBinding :=
  match binding.get name with
  | none => some (binding.put name lifetime invariant)
  | some (old, locked) =>
      if invariant then
        if old == lifetime then some (binding.put name old true) else none
      else if locked then
        if lifetime.contains old then some binding else none
      else if old.contains lifetime then
        some (binding.put name lifetime false)
      else if lifetime.contains old then
        some binding
      else
        none

def LifetimeBinding.constrainSupertype (binding : LifetimeBinding) (name : String) (lifetime : Lifetime)
    (invariant : Bool) : Option LifetimeBinding :=
  match binding.get name with
  | none => some (binding.put name lifetime invariant)
  | some (old, locked) =>
      if invariant then
        if old == lifetime then some (binding.put name old true) else none
      else if locked then
        if old.contains lifetime then some binding else none
      else if lifetime.contains old then
        some (binding.put name lifetime false)
      else if old.contains lifetime then
        some binding
      else
        none

def LifetimeBinding.constrainExact (binding : LifetimeBinding) (name : String) (lifetime : Lifetime) :
    Option LifetimeBinding :=
  match binding.get name with
  | none => some (binding.put name lifetime true)
  | some (old, _) =>
      if old == lifetime then some (binding.put name old true) else none

def LifetimeBinding.lock (binding : LifetimeBinding) (name : String) : LifetimeBinding :=
  match binding.get name with
  | none => binding
  | some (lifetime, _) => binding.put name lifetime true

structure LowerState where
  binding : LifetimeBinding := []
  targets : List (Name × String) := []
  outlives : List (String × String) := []
  next : Nat := 0
  deriving BEq, Repr

structure DeclBinding where
  lifetimes : LifetimeBinding := []
  targets : List (Name × String) := []
  outlives : List (String × String) := []
  deriving BEq, Repr

namespace LowerState

def fresh (state : LowerState) : Name × LowerState :=
  ("?sig" ++ toString state.next, { state with next := state.next + 1 })

def instantiate (state : LowerState) (name : String) (lifetime : Lifetime) :
    Lifetime × LowerState :=
  match state.binding.get name with
  | some (target, locked) => (target, { state with binding := state.binding.put name target locked })
  | none =>
      let target := lifetime.dropLast
      (target, { state with binding := state.binding.put name target false })

def addTarget (state : LowerState) (target : Name) (lifetimeName : String) : LowerState :=
  { state with targets := (target, lifetimeName) :: state.targets }

def addOutlives (state : LowerState) (outer inner : String) : LowerState :=
  if state.outlives.contains (outer, inner) then state else { state with outlives := (outer, inner) :: state.outlives }

def toDeclBinding (state : LowerState) : DeclBinding :=
  { lifetimes := state.binding, targets := state.targets, outlives := state.outlives }

end LowerState

namespace DeclBinding

def lifetimeOfTarget? (binding : DeclBinding) (target : Name) : Option String :=
  match binding.targets.find? (fun entry => entry.fst == target) with
  | some entry => some entry.snd
  | none => none

def abstractContainsFuel (binding : DeclBinding) : Nat → String → String → Bool
  | 0, outer, inner => outer == inner
  | fuel + 1, outer, inner =>
      outer == inner ||
        binding.outlives.any (fun edge => edge.fst == outer && abstractContainsFuel binding fuel edge.snd inner)

def abstractContains (binding : DeclBinding) (outer inner : String) : Bool :=
  abstractContainsFuel binding (binding.outlives.length + 1) outer inner

def concreteContains (binding : DeclBinding) (outer : Lifetime) (innerName : String) : Bool :=
  match binding.lifetimes.get innerName with
  | some (inner, _) => outer.contains inner
  | none => false

def containsTarget (binding : DeclBinding) (env : Env) (lv : LVal) (innerName : String) :
    CheckM Bool := do
  match binding.lifetimeOfTarget? lv.name with
  | some outerName => return binding.abstractContains outerName innerName
  | none =>
      let (_, outer) ← Core.BorrowChecker.typeOf env lv
      return binding.concreteContains outer innerName

end DeclBinding

partial def lockLifetimes (sig : Signature) (binding : LifetimeBinding) : LifetimeBinding :=
  match sig with
  | .unit => binding
  | .int => binding
  | .box operand => lockLifetimes operand binding
  | .tuple fields => fields.foldl (fun binding sig => lockLifetimes sig binding) binding
  | .borrow _ lifetimeName operand =>
      lockLifetimes operand (binding.lock lifetimeName)

partial def lowerWithState (sig : Signature) (env : Env) (lifetime : Lifetime) (state : LowerState)
    (current : Option String := none) :
    CheckM (Env × Ty × LowerState) := do
  match sig with
  | .unit => return (env, .unit, state)
  | .int => return (env, .int, state)
  | .box operand =>
      let (env, ty, state) ← lowerWithState operand env lifetime state current
      return (env, .box ty, state)
  | .tuple fields =>
      let (env, fields, state) ← lowerFields fields env lifetime state current
      return (env, .tuple fields, state)
  | .borrow mutable lifetimeName operand =>
      let (targetLifetime, state) := state.instantiate lifetimeName lifetime
      let state :=
        match current with
        | some currentName => state.addOutlives lifetimeName currentName
        | none => state
      let (env, operandTy, state) ← lowerWithState operand env targetLifetime state (some lifetimeName)
      let (targetName, state) := state.fresh
      let state := state.addTarget targetName lifetimeName
      let env := Env.put env targetName { ty := operandTy, lifetime := targetLifetime }
      return (env, .borrow mutable [LVal.var targetName], state)
where
  lowerFields : List Signature → Env → Lifetime → LowerState → Option String → CheckM (Env × List Ty × LowerState)
    | [], env, _, state, _ => return (env, [], state)
    | sig :: rest, env, lifetime, state, current => do
        let (env, ty, state) ← lowerWithState sig env lifetime state current
        let (env, tys, state) ← lowerFields rest env lifetime state current
        return (env, ty :: tys, state)

def lower (sig : Signature) (env : Env) (lifetime : Lifetime) : CheckM (Env × Ty) := do
  let (env, ty, _) ← lowerWithState sig env lifetime {}
  return (env, ty)

partial def matchesSig (env : Env) (sig : Signature) (ty : Ty) : CheckM Bool := do
  match sig, ty with
  | .unit, .unit => return true
  | .int, .int => return true
  | .box s, .box t => matchesSig env s t
  | .tuple ss, .tuple ts =>
      if ss.length == ts.length then
        (ss.zip ts).allM (fun pair => matchesSig env pair.fst pair.snd)
      else
        return false
  | .borrow mutable _ s, .borrow actualMutable lvals =>
      if mutable != actualMutable then
        return false
      else
        lvals.allM (fun lv => do
          let (targetTy, _) ← Core.BorrowChecker.typeOf env lv
          matchesSig env s targetTy)
  | _, _ => return false

mutual
  partial def matchSubtypeWithBinding (env : Env) (sig : Signature) (ty : Ty) (binding : LifetimeBinding) :
      CheckM (Option LifetimeBinding) := do
    match sig, ty with
    | .unit, .unit => return some binding
    | .int, .int => return some binding
    | .box s, .box t => matchSubtypeWithBinding env s t binding
    | .tuple ss, .tuple ts =>
        if ss.length == ts.length then
          (ss.zip ts).foldlM
            (fun acc pair => do
              match acc with
              | none => return none
              | some binding => matchSubtypeWithBinding env pair.fst pair.snd binding)
            (some binding)
        else
          return none
    | .borrow mutable lifetimeName s, .borrow actualMutable lvals =>
        if mutable != actualMutable then
          return none
        else
          lvals.foldlM
            (fun acc lv => do
              match acc with
              | none => return none
              | some binding => do
                  let (targetTy, targetLifetime) ← Core.BorrowChecker.typeOf env lv
                  let constrained :=
                    if mutable then
                      LifetimeBinding.constrainExact binding lifetimeName targetLifetime
                    else
                      LifetimeBinding.constrainSubtype binding lifetimeName targetLifetime false
                  match constrained with
                  | none => return none
                  | some binding => do
                      match ← matchSubtypeWithBinding env s targetTy binding with
                      | none => return none
                      | some binding =>
                          if mutable then
                            match ← matchSupertypeWithBinding env s targetTy binding with
                            | none => return none
                            | some binding => return some (lockLifetimes s binding)
                          else
                            return some binding)
            (some binding)
    | _, _ => return none

  partial def matchSupertypeWithBinding (env : Env) (sig : Signature) (ty : Ty) (binding : LifetimeBinding) :
      CheckM (Option LifetimeBinding) := do
    match sig, ty with
    | .unit, .unit => return some binding
    | .int, .int => return some binding
    | .box s, .box t => matchSupertypeWithBinding env s t binding
    | .tuple ss, .tuple ts =>
        if ss.length == ts.length then
          (ss.zip ts).foldlM
            (fun acc pair => do
              match acc with
              | none => return none
              | some binding => matchSupertypeWithBinding env pair.fst pair.snd binding)
            (some binding)
        else
          return none
    | .borrow mutable lifetimeName s, .borrow actualMutable lvals =>
        if mutable != actualMutable then
          return none
        else
          lvals.foldlM
            (fun acc lv => do
              match acc with
              | none => return none
              | some binding => do
                  let (targetTy, targetLifetime) ← Core.BorrowChecker.typeOf env lv
                  let constrained :=
                    if mutable then
                      LifetimeBinding.constrainExact binding lifetimeName targetLifetime
                    else
                      LifetimeBinding.constrainSupertype binding lifetimeName targetLifetime false
                  match constrained with
                  | none => return none
                  | some binding => do
                      match ← matchSupertypeWithBinding env s targetTy binding with
                      | none => return none
                      | some binding =>
                          if mutable then
                            match ← matchSubtypeWithBinding env s targetTy binding with
                            | none => return none
                            | some binding => return some (lockLifetimes s binding)
                          else
                            return some binding)
            (some binding)
    | _, _ => return none
end

mutual
  partial def fixedSubtype (env : Env) (sig : Signature) (ty : Ty) (binding : DeclBinding) :
      CheckM Bool := do
    match sig, ty with
    | .unit, .unit => return true
    | .int, .int => return true
    | .box s, .box t => fixedSubtype env s t binding
    | .tuple ss, .tuple ts =>
        if ss.length == ts.length then
          (ss.zip ts).allM (fun pair => fixedSubtype env pair.fst pair.snd binding)
        else
          return false
    | .borrow mutable lifetimeName s, .borrow actualMutable lvals =>
        if mutable != actualMutable then
          return false
        else
          match binding.lifetimes.get lifetimeName with
          | none => return false
          | some _ =>
              lvals.allM (fun lv => do
                let (targetTy, targetLifetime) ← Core.BorrowChecker.typeOf env lv
                if !(← binding.containsTarget env lv lifetimeName) then
                  return false
                else if !(← fixedSubtype env s targetTy binding) then
                  return false
                else if mutable then
                  let reverseContains :=
                    match binding.lifetimeOfTarget? lv.name with
                    | some outerName => binding.abstractContains lifetimeName outerName
                    | none => binding.concreteContains targetLifetime lifetimeName
                  if !reverseContains then
                    return false
                  else
                    fixedSupertype env s targetTy binding
                else
                  return true)
    | _, _ => return false

  partial def fixedSupertype (env : Env) (sig : Signature) (ty : Ty) (binding : DeclBinding) :
      CheckM Bool := do
    match sig, ty with
    | .unit, .unit => return true
    | .int, .int => return true
    | .box s, .box t => fixedSupertype env s t binding
    | .tuple ss, .tuple ts =>
        if ss.length == ts.length then
          (ss.zip ts).allM (fun pair => fixedSupertype env pair.fst pair.snd binding)
        else
          return false
    | .borrow mutable lifetimeName s, .borrow actualMutable lvals =>
        if mutable != actualMutable then
          return false
        else
          match binding.lifetimes.get lifetimeName with
          | none => return false
          | some _ =>
              lvals.allM (fun lv => do
                let (targetTy, targetLifetime) ← Core.BorrowChecker.typeOf env lv
                let targetContains :=
                  match binding.lifetimeOfTarget? lv.name with
                  | some outerName => binding.abstractContains lifetimeName outerName
                  | none => binding.concreteContains targetLifetime lifetimeName
                if !targetContains then
                  return false
                else if !(← fixedSupertype env s targetTy binding) then
                  return false
                else if mutable then
                  if !(← binding.containsTarget env lv lifetimeName) then
                    return false
                  else
                    fixedSubtype env s targetTy binding
                else
                  return true)
    | _, _ => return false
end

partial def sigSubtype (binding : DeclBinding) (lhs rhs : Signature) : Bool :=
  match lhs, rhs with
  | .unit, .unit => true
  | .int, .int => true
  | .box lhs, .box rhs => sigSubtype binding lhs rhs
  | .tuple lhs, .tuple rhs =>
      lhs.length == rhs.length && (lhs.zip rhs).all (fun pair => sigSubtype binding pair.fst pair.snd)
  | .borrow lhsMut lhsLifetime lhsOperand, .borrow rhsMut rhsLifetime rhsOperand =>
      if lhsMut && rhsMut then
        binding.abstractContains rhsLifetime lhsLifetime &&
          binding.abstractContains lhsLifetime rhsLifetime &&
          sigSubtype binding lhsOperand rhsOperand &&
          sigSubtype binding rhsOperand lhsOperand
      else if !lhsMut && !rhsMut then
        binding.abstractContains rhsLifetime lhsLifetime && sigSubtype binding lhsOperand rhsOperand
      else
        false
  | _, _ => false

def pushUnique [BEq α] (xs : List α) (x : α) : List α :=
  if xs.contains x then xs else xs ++ [x]

partial def abstractLifetimes : Signature → List String
  | .unit => []
  | .int => []
  | .box operand => abstractLifetimes operand
  | .tuple fields => fields.foldl (fun acc sig => (abstractLifetimes sig).foldl pushUnique acc) []
  | .borrow _ lifetimeName operand => (abstractLifetimes operand).foldl pushUnique [lifetimeName]

def abstractParamLifetimes (params : List (Name × Signature)) : List String :=
  params.foldl (fun acc param => (abstractLifetimes param.snd).foldl pushUnique acc) []

partial def concreteLifetimesFromTy (env : Env) : Ty → CheckM (List Lifetime)
  | .unit => return []
  | .int => return []
  | .undef shape => concreteLifetimesFromTy env shape
  | .box operand => concreteLifetimesFromTy env operand
  | .tuple fields =>
      fields.foldlM
        (fun acc ty => do
          let lifetimes ← concreteLifetimesFromTy env ty
          return lifetimes.foldl pushUnique acc)
        []
  | .borrow _ lvals =>
      lvals.foldlM
        (fun acc lv => do
          let (targetTy, targetLifetime) ← Core.BorrowChecker.typeOf env lv
          let nested ← concreteLifetimesFromTy env targetTy
          return nested.foldl pushUnique (pushUnique acc targetLifetime))
        []

def concreteArgLifetimes (env : Env) (argTys : List Ty) : CheckM (List Lifetime) :=
  argTys.foldlM
    (fun acc ty => do
      let lifetimes ← concreteLifetimesFromTy env ty
      return lifetimes.foldl pushUnique acc)
    []

def generateBindings (abstracts : List String) (concretes : List Lifetime) : List LifetimeBinding :=
  match abstracts with
  | [] => [[]]
  | lifetimeName :: rest =>
      if concretes.isEmpty then
        []
      else
        (generateBindings rest concretes).flatMap (fun binding =>
          concretes.map (fun concrete => LifetimeBinding.put binding lifetimeName concrete true))

def matchArgsWithCandidate (env : Env) (params : List (Name × Signature)) (argTys : List Ty)
    (binding : LifetimeBinding) :
    CheckM Bool := do
  let result ← (params.zip argTys).foldlM
    (fun acc pair => do
      match acc with
      | none => return none
      | some binding => matchSubtypeWithBinding env pair.fst.snd pair.snd binding)
    (some binding)
  return result.isSome

def matchArgsWithBinding (env : Env) (params : List (Name × Signature)) (argTys : List Ty) :
    CheckM Bool := do
  let abstracts := abstractParamLifetimes params
  let concretes ← concreteArgLifetimes env argTys
  (generateBindings abstracts concretes).anyM (matchArgsWithCandidate env params argTys)

partial def matchesLoweredSig (env : Env) (sig : Signature) (ty : Ty) : CheckM Bool := do
  match sig, ty with
  | .unit, .unit => return true
  | .int, .int => return true
  | .box s, .box t => matchesLoweredSig env s t
  | .tuple ss, .tuple ts =>
      if ss.length == ts.length then
        (ss.zip ts).allM (fun pair => matchesLoweredSig env pair.fst pair.snd)
      else
        return false
  | .borrow mutable lifetimeName s, .borrow actualMutable lvals =>
      if mutable != actualMutable then
        return false
      else
        let target := LVal.var ("?" ++ lifetimeName)
        if !(lvals.all (fun lv => lv == target)) then
          return false
        else
          lvals.allM (fun lv => do
            let (targetTy, _) ← Core.BorrowChecker.typeOf env lv
            matchesLoweredSig env s targetTy)
  | _, _ => return false

def abstractTy (sig : Signature) : Ty :=
  match sig with
  | .unit => .unit
  | .int => .int
  | .box operand => .box (abstractTy operand)
  | .tuple fields => .tuple (fields.map abstractTy)
  | .borrow mutable lifetimeName _ =>
      .borrow mutable [LVal.var ("?" ++ lifetimeName)]

end Signature

def lookupDecl (decls : List FunctionDeclaration) (name : Name) : Option FunctionDeclaration :=
  decls.find? (fun decl => decl.name == name)

def lowerParamEnvWithBindingAt (params : List (Name × Signature)) (lowerLifetime slotLifetime : Lifetime) :
    CheckM (Env × Signature.DeclBinding) := do
  let (env, state) ← params.foldlM
    (fun (env, state) param => do
      let (env, ty, state) ← param.snd.lowerWithState env lowerLifetime state
      return (Env.put env param.fst { ty := ty, lifetime := slotLifetime }, state))
    (Env.empty, ({} : Signature.LowerState))
  return (env, state.toDeclBinding)

def lowerParamEnvWithBinding (params : List (Name × Signature)) (lifetime : Lifetime) :
    CheckM (Env × Signature.DeclBinding) :=
  lowerParamEnvWithBindingAt params lifetime lifetime

def lowerParamEnv (params : List (Name × Signature)) (lifetime : Lifetime) : CheckM Env := do
  let (env, _) ← lowerParamEnvWithBinding params lifetime
  return env

def constructLiftBinding (params : List (Name × Signature)) (lifetime : Lifetime) :
    CheckM Signature.DeclBinding := do
  let (_, binding) ← lowerParamEnvWithBinding params (lifetime ++ [0])
  return binding

def mergeLift (lhs rhs : Option Ty) : CheckM (Option Ty) := do
  match lhs, rhs with
  | none, none => return none
  | some ty, none => return some ty
  | none, some ty => return some ty
  | some lhs, some rhs => return some (← Core.BorrowChecker.Ty.union lhs rhs)

partial def liftCandidate (env : Env) (binding : Signature.DeclBinding) (target param : Signature) (argTy : Ty) :
    CheckM (Option Ty) := do
  if Signature.sigSubtype binding target param then
    return some argTy
  else
    match param, argTy with
    | .box paramOperand, .box argOperand =>
        liftCandidate env binding target paramOperand argOperand
    | .tuple paramFields, .tuple argFields =>
        if paramFields.length == argFields.length then
          (paramFields.zip argFields).foldlM
            (fun acc pair => do
              let lifted ← liftCandidate env binding target pair.fst pair.snd
              mergeLift acc lifted)
            none
        else
          return none
    | .borrow _ _ paramOperand, .borrow _ lvals =>
        lvals.foldlM
          (fun acc lv => do
            let (targetTy, _) ← Core.BorrowChecker.typeOf env lv
            let lifted ← liftCandidate env binding target paramOperand targetTy
            mergeLift acc lifted)
          none
    | _, _ => return none

def liftSignature (env : Env) (binding : Signature.DeclBinding) (target : Signature)
    (params : List (Name × Signature)) (argTys : List Ty) :
    CheckM Ty := do
  let lifted ← (params.zip argTys).foldlM
    (fun acc pair => do
      let candidate ← liftCandidate env binding target pair.fst.snd pair.snd
      mergeLift acc candidate)
    none
  match lifted with
  | some ty => return ty
  | none => return Signature.abstractTy target

def liftReturn (env : Env) (binding : Signature.DeclBinding) (decl : FunctionDeclaration) (argTys : List Ty) :
    CheckM Ty :=
  liftSignature env binding decl.ret decl.params argTys

partial def collectMutableEffects (env : Env) (param : Signature) (argTy : Ty) :
    CheckM (List (Signature × List LVal)) := do
  match param, argTy with
  | .box paramOperand, .box argOperand =>
      collectMutableEffects env paramOperand argOperand
  | .tuple paramFields, .tuple argFields =>
      if paramFields.length == argFields.length then
        (paramFields.zip argFields).foldlM
          (fun acc pair => do
            let effects ← collectMutableEffects env pair.fst pair.snd
            return acc ++ effects)
          []
      else
        return []
  | .borrow true _ operand, .borrow true lvals =>
      let nested ← lvals.foldlM
        (fun acc lv => do
          let (targetTy, _) ← Core.BorrowChecker.typeOf env lv
          let effects ← collectMutableEffects env operand targetTy
          return acc ++ effects)
        []
      return nested ++ [(operand, lvals)]
  | _, _ => return []

def liftSideEffects (env : Env) (binding : Signature.DeclBinding) (decl : FunctionDeclaration) (argTys : List Ty) :
    CheckM Env := do
  let effects ← (decl.params.zip argTys).foldlM
    (fun acc pair => do
      let effects ← collectMutableEffects env pair.fst.snd pair.snd
      return acc ++ effects)
    []
  effects.foldlM
    (fun env effect => do
      let effectTy ← liftSignature env binding effect.fst decl.params argTys
      effect.snd.foldlM (fun env lv => Core.BorrowChecker.write env lv effectTy false) env)
    env

partial def checkTerm (decls : List FunctionDeclaration) (env : Env) (lifetime : Lifetime) (term : Term) :
    CheckM (Env × Ty) := do
  match term with
  | .val .unit => return (env, .unit)
  | .val (.int _) => return (env, .int)
  | .val (.ref _) => fail "locations are not source-level syntax"
  | .val .moved => fail "moved values are not source-level syntax"
  | .val (.tuple fields) =>
      return (env, .tuple (fields.map (fun _ => Ty.unit)))
  | .access kind lv => do
      let (ty, _) ← Core.BorrowChecker.typeOf env lv
      if !(Core.BorrowChecker.Ty.defined ty) then
        fail "use of moved lval or attempt to move out of lval"
      else if kind == AccessKind.copy || kind == AccessKind.temp then
        if kind == AccessKind.copy && !(Core.BorrowChecker.Ty.copyable ty) then
          fail "lval's type cannot be copied"
        else if Core.BorrowChecker.readProhibited env lv then
          fail "lval cannot be read (e.g. is moved in part or whole)"
        else
          return (env, ty)
      else
        if Core.BorrowChecker.writeProhibited env lv then
          fail "lval cannot be written (e.g. is moved in part or whole)"
        else
          return (← Core.BorrowChecker.move env lv, ty)
  | .borrow mutableBorrow lv => do
      let (ty, _) ← Core.BorrowChecker.typeOf env lv
      if !(Core.BorrowChecker.Ty.defined ty) then
        fail "use of moved lval or attempt to move out of lval"
      else if mutableBorrow then
        if Core.BorrowChecker.writeProhibited env lv then
          fail "lval cannot be written (e.g. is moved in part or whole)"
        else if !(← Core.BorrowChecker.mutLVal env lv) then
          fail "lval borrowed in part or whole"
        else
          return (env, .borrow true [lv])
      else if Core.BorrowChecker.readProhibited env lv then
        fail "lval cannot be read (e.g. is moved in part or whole)"
      else
        return (env, .borrow false [lv])
  | .box operand => do
      let (env, ty) ← checkTerm decls env lifetime operand
      return (env, .box ty)
  | .letMut x initialiser => do
      if (Env.get env x).isSome then
        fail "variable already declared"
      else
        let (env, ty) ← checkTerm decls env lifetime initialiser
        return (Env.put env x { ty := ty, lifetime := lifetime }, .unit)
  | .assign lhs rhs => do
      let (lhsTy, targetLifetime) ← Core.BorrowChecker.typeOf env lhs
      let (env, rhsTy) ← checkTerm decls env lifetime rhs
      if !(← Core.BorrowChecker.compatible env lhsTy rhsTy) then
        fail "incompatible type"
      else if !(← Core.BorrowChecker.Ty.within env targetLifetime rhsTy) then
        fail "lifetime not within"
      else
        let env ← Core.BorrowChecker.write env lhs rhsTy true
        if Core.BorrowChecker.writeProhibited env lhs then
          fail "lval borrowed in part or whole"
        else
          return (env, .unit)
  | .block blockLifetime terms => do
      let (env, ty) ← checkSeq env blockLifetime terms
      if !(← Core.BorrowChecker.Ty.within env lifetime ty) then
        fail "lifetime not within"
      else if !(← Core.BorrowChecker.scopedAfterDrop env blockLifetime) then
        fail "lifetime not within"
      else
        return (Env.dropLifetime env blockLifetime, ty)
  | .tuple terms => do
      let (env, tys, temps) ← carry env lifetime terms 0
      return (Env.removeMany env temps, .tuple tys)
  | .ifElse _ lhs rhs trueBlock falseBlock => do
      let fresh := "?" ++ toString env.length
      let (env, lhsTy) ← checkTerm decls env lifetime lhs
      let (env, rhsTy) ← checkTerm decls (Env.put env fresh { ty := lhsTy, lifetime := Lifetime.root }) lifetime rhs
      let env := Env.erase env fresh
      if !(← Core.BorrowChecker.compatible env lhsTy rhsTy) then
        fail "incompatible type"
      else if !(Core.BorrowChecker.Ty.copyable lhsTy) || !(Core.BorrowChecker.Ty.copyable rhsTy) then
        fail "lval's type cannot be copied"
      else
        let (trueEnv, trueTy) ← checkTerm decls env lifetime trueBlock
        let (falseEnv, falseTy) ← checkTerm decls env lifetime falseBlock
        let env ← Core.BorrowChecker.joinEnv trueEnv falseEnv
        if !(← Core.BorrowChecker.compatible env trueTy falseTy) then
          fail "incompatible type"
        else
          return (env, ← Core.BorrowChecker.Ty.union trueTy falseTy)
  | .invoke name args => do
      let decl ← expectSome "unknown function" (lookupDecl decls name)
      if args.length < decl.params.length then
        fail "insufficient arguments"
      else if args.length > decl.params.length then
        fail "too many arguments"
      else
        let (env, argTys, temps) ← carry env lifetime args 0
        let ok ← Signature.matchArgsWithBinding env decl.params argTys
        if !ok then
          fail "incompatible argument(s)"
        else
          let binding ← constructLiftBinding decl.params lifetime
          let retTy ← liftReturn env binding decl argTys
          let env ← liftSideEffects env binding decl argTys
          return (Env.removeMany env temps, retTy)
where
  checkSeq (env : Env) (lifetime : Lifetime) : List Term → CheckM (Env × Ty)
    | [] => return (env, .unit)
    | t :: rest => do
        let (env, ty) ← checkTerm decls env lifetime t
        match rest with
        | [] => return (env, ty)
        | _ => checkSeq env lifetime rest

  carry (env : Env) (lifetime : Lifetime) : List Term → Nat → CheckM (Env × List Ty × List Name)
    | [], _ => return (env, [], [])
    | t :: rest, n => do
        let (env, ty) ← checkTerm decls env lifetime t
        let fresh := "?" ++ toString n
        let env := Env.put env fresh { ty := ty, lifetime := Lifetime.root }
        let (env, tys, names) ← carry env lifetime rest (n + 1)
        return (env, ty :: tys, fresh :: names)

def checkDecl (decls : List FunctionDeclaration) (decl : FunctionDeclaration) : CheckM Unit := do
  let lifetime := [1]
  let (env, binding) ← lowerParamEnvWithBinding decl.params lifetime
  let (_, bodyTy) ← checkTerm decls env lifetime decl.body
  if !(← Signature.fixedSubtype env decl.ret bodyTy binding) then
    fail "incompatible type"

def checkProgram (decls : List FunctionDeclaration) (term : Term) : CheckM Ty := do
  decls.forM (checkDecl decls)
  let (_, ty) ← checkTerm decls Env.empty Lifetime.root term
  return ty

partial def eval (decls : List FunctionDeclaration) (state : Core.OperationalSemantics.State) (lifetime : Lifetime) (term : Term) :
    EvalM (Core.OperationalSemantics.State × Value) := do
  match term with
  | .val v => return (state, v)
  | .access kind lv => do
      let value ← Core.OperationalSemantics.State.readLVal state lv
      if kind == AccessKind.move then
        return (← Core.OperationalSemantics.State.writeLVal state lv none, value)
      else
        return (state, value)
  | .borrow _ lv => do
      let ref ← Core.OperationalSemantics.locate state lv
      return (state, .ref (Reference.borrowed ref))
  | .box operand => do
      let (state, value) ← eval decls state lifetime operand
      let (state, ref) := Core.OperationalSemantics.State.allocate state Lifetime.root value
      return (state, .ref ref)
  | .letMut x initialiser => do
      let (state, value) ← eval decls state lifetime initialiser
      let (state, ref) := Core.OperationalSemantics.State.allocate state lifetime value
      return (Core.OperationalSemantics.State.putVar state x ref, .unit)
  | .assign lhs rhs => do
      let (state, value) ← eval decls state lifetime rhs
      return (← Core.OperationalSemantics.State.writeLVal state lhs (some value), .unit)
  | .block blockLifetime terms =>
      let (state, value) ← evalSeq state blockLifetime terms
      return (Core.OperationalSemantics.State.dropLifetime state blockLifetime, value)
  | .tuple terms => do
      let (state, values) ← evalTerms state lifetime terms
      return (state, .tuple values)
  | .ifElse eq lhs rhs trueBlock falseBlock => do
      let (state, lhsValue) ← eval decls state lifetime lhs
      let (state, rhsValue) ← eval decls state lifetime rhs
      if (lhsValue == rhsValue) == eq then
        eval decls state lifetime trueBlock
      else
        eval decls state lifetime falseBlock
  | .invoke name args => do
      let decl ← expectSome "unknown function" (lookupDecl decls name)
      let (state, values) ← evalTerms state lifetime args
      let callLifetime :=
        match decl.body with
        | .block blockLifetime _ => blockLifetime
        | _ => lifetime ++ [decl.params.length]
      let callerVars := state.vars
      let state ← bindParams state callLifetime decl.params values
      let (state, value) ← eval decls state callLifetime decl.body
      return ({ state with vars := callerVars }, value)
where
  evalSeq (state : Core.OperationalSemantics.State) (lifetime : Lifetime) : List Term → EvalM (Core.OperationalSemantics.State × Value)
    | [] => return (state, .unit)
    | t :: rest => do
        let (state, value) ← eval decls state lifetime t
        match rest with
        | [] => return (state, value)
        | _ => evalSeq state lifetime rest

  evalTerms (state : Core.OperationalSemantics.State) (lifetime : Lifetime) : List Term → EvalM (Core.OperationalSemantics.State × List Value)
    | [] => return (state, [])
    | t :: rest => do
        let (state, value) ← eval decls state lifetime t
        let (state, values) ← evalTerms state lifetime rest
        return (state, value :: values)

  bindParams (state : Core.OperationalSemantics.State) (lifetime : Lifetime) :
      List (Name × Signature) → List Value → EvalM Core.OperationalSemantics.State
    | [], [] => return state
    | param :: params, value :: values => do
        let (state, ref) := Core.OperationalSemantics.State.allocate state lifetime value
        bindParams (Core.OperationalSemantics.State.putVar state param.fst ref) lifetime params values
    | _, _ => fail "argument arity mismatch"

def execute (decls : List FunctionDeclaration) (term : Term) : EvalM Value := do
  discard <| checkProgram decls term
  let (_, value) ← eval decls Core.OperationalSemantics.State.empty Lifetime.root term
  return value

end Functions
end Extensions
end LwRust
