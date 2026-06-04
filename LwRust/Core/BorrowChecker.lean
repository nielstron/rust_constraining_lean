import LwRust.Core.Syntax

namespace LwRust
namespace Core
namespace BorrowChecker

abbrev CheckM := Except String

def fail {α : Type} (msg : String) : CheckM α :=
  Except.error msg

def expectSome {α : Type} (msg : String) : Option α → CheckM α
  | some x => Except.ok x
  | none => fail msg

def Ty.undefine : Ty → Ty
  | .undef t => .undef t
  | t => .undef t

partial def Ty.union : Ty → Ty → CheckM Ty
  | .undef lhs, .undef rhs => return .undef (← Ty.union lhs rhs)
  | .undef lhs, rhs => return .undef (← Ty.union lhs rhs)
  | lhs, .undef rhs => return .undef (← Ty.union lhs rhs)
  | .unit, .unit => return .unit
  | .int, .int => return .int
  | .box lhs, .box rhs => return .box (← Ty.union lhs rhs)
  | .tuple lhs, .tuple rhs =>
      if lhs.length == rhs.length then
        return .tuple (← unionLists lhs rhs)
      else
        fail "invalid tuple union"
  | .borrow lm lhs, .borrow rm rhs =>
      if lm == rm then
        return .borrow lm (lhs.foldl (fun acc lv => if acc.contains lv then acc else acc ++ [lv]) rhs)
      else
        fail "invalid borrow union"
  | _, _ => fail "invalid type union"
where
  unionLists : List Ty → List Ty → CheckM (List Ty)
    | [], [] => return []
    | l :: ls, r :: rs => return (← Ty.union l r) :: (← unionLists ls rs)
    | _, _ => fail "invalid tuple union"

partial def Ty.defined : Ty → Bool
  | .undef _ => false
  | .box t => Ty.defined t
  | .tuple ts => ts.all Ty.defined
  | _ => true

partial def Ty.copyable : Ty → Bool
  | .unit => true
  | .int => true
  | .borrow mutable _ => !mutable
  | .box _ => false
  | .tuple ts => ts.all Ty.copyable
  | .undef _ => false

partial def Ty.concretize : Ty → Ty
  | .undef t => Ty.concretize t
  | .box t => .box (Ty.concretize t)
  | .tuple ts => .tuple (ts.map Ty.concretize)
  | t => t

partial def Ty.prohibitsWriting (ty : Ty) (lv : LVal) : Bool :=
  match ty with
  | .borrow _ lvals => lvals.any (fun other => lv.conflicts other)
  | .box t => Ty.prohibitsWriting t lv
  | .tuple ts => ts.any (fun t => Ty.prohibitsWriting t lv)
  | _ => false

partial def Ty.prohibitsReading (ty : Ty) (lv : LVal) : Bool :=
  match ty with
  | .borrow true lvals => lvals.any (fun other => lv.conflicts other)
  | .box t => Ty.prohibitsReading t lv
  | .tuple ts => ts.any (fun t => Ty.prohibitsReading t lv)
  | _ => false

partial def readProhibited (env : Env) (lv : LVal) : Bool :=
  env.any (fun entry => Ty.prohibitsReading entry.snd.ty lv)

partial def writeProhibited (env : Env) (lv : LVal) : Bool :=
  env.any (fun entry => Ty.prohibitsWriting entry.snd.ty lv)

partial def typeOf (env : Env) (lv : LVal) : CheckM (Ty × Lifetime) := do
  let slot ← expectSome "variable undeclared" (Env.get env lv.name)
  applyPath env slot.ty slot.lifetime lv.path
where
  applyPath (env : Env) (ty : Ty) (lifetime : Lifetime) : Path → CheckM (Ty × Lifetime)
    | [] => return (ty, lifetime)
    | .deref :: rest =>
        match ty with
        | .box element => applyPath env element lifetime rest
        | .borrow _ lvals => do
            let (ty, lifetime) ← derefBorrow env lvals
            applyPath env ty lifetime rest
        | _ => fail "lval is invalid (e.g. incorrectly typed)"
    | .index i :: rest =>
        match ty with
        | .tuple fields => do
            let field ← expectSome "invalid tuple accessor" fields[i]?
            applyPath env field lifetime rest
        | _ => fail "expected tuple type"

  derefBorrow (env : Env) : List LVal → CheckM (Ty × Lifetime)
    | [] => fail "empty borrow type"
    | lv :: rest => do
        let first ← typeOf env lv
        rest.foldlM
          (fun (accTy, accLifetime) lv => do
            let (ty, lifetime) ← typeOf env lv
            let minLifetime ← expectSome "ambiguous lifetimes" (Lifetime.min? accLifetime lifetime)
            return (← Ty.union accTy ty, minLifetime))
          first

partial def Ty.within (env : Env) (lifetime : Lifetime) : Ty → CheckM Bool
  | .unit => return true
  | .int => return true
  | .box t => Ty.within env lifetime t
  | .tuple ts => ts.allM (Ty.within env lifetime)
  | .borrow _ lvals =>
      lvals.allM (fun lv => do
        let slot ← expectSome "variable undeclared" (Env.get env lv.name)
        return slot.lifetime.contains lifetime)
  | .undef _ => fail "undefined type cannot be assigned"

partial def strike (ty : Ty) (path : Path) (i : Nat := 0) : CheckM Ty :=
  if i == path.length then
    return Ty.undefine ty
  else
    match path[i]? with
    | none => fail "invalid path"
    | some PathElem.deref =>
        match ty with
        | .box element => return .box (← strike element path (i + 1))
        | .borrow _ _ => fail "cannot move out through borrow"
        | _ => fail "lval is invalid (e.g. incorrectly typed)"
    | some (.index n) =>
        match ty with
        | .tuple fields => do
            let field ← expectSome "invalid tuple accessor" fields[n]?
            let updated ← strike field path (i + 1)
            return .tuple (fields.set n updated)
        | _ => fail "expected tuple type"

def move (env : Env) (lv : LVal) : CheckM Env := do
  let slot ← expectSome "variable undeclared" (Env.get env lv.name)
  let ty ← strike slot.ty lv.path
  return Env.put env lv.name { slot with ty := ty }

partial def compatible (env : Env) : Ty → Ty → CheckM Bool
  | .undef lhs, .undef rhs => compatible env lhs rhs
  | .undef lhs, rhs => compatible env lhs rhs
  | lhs, .undef rhs => compatible env lhs rhs
  | .unit, .unit => return true
  | .int, .int => return true
  | .box lhs, .box rhs => compatible env lhs rhs
  | .tuple lhs, .tuple rhs =>
      if lhs.length == rhs.length then
        lhs.zip rhs |>.allM (fun pair => compatible env pair.fst pair.snd)
      else
        return false
  | .borrow lm lhs, .borrow rm rhs =>
      if lm == rm then
        match lhs, rhs with
        | l :: _, r :: _ => do
            let (lt, _) ← typeOf env l
            let (rt, _) ← typeOf env r
            compatible env lt rt
        | _, _ => return false
      else
        return false
  | _, _ => return false

partial def mutable (env : Env) (ty : Ty) (path : Path) (i : Nat := 0) : CheckM Bool :=
  if i == path.length then
    return true
  else
    match path[i]? with
    | some PathElem.deref =>
        match ty with
        | .box element => mutable env element path (i + 1)
        | .borrow isMut lvals =>
            if !isMut then
              return false
            else
              match lvals with
              | first :: _ => do
                  let (targetTy, _) ← typeOf env first
                  mutable env targetTy path (i + 1)
              | [] => return false
        | _ => return false
    | some (.index n) =>
        match ty with
        | .tuple fields =>
            match fields[n]? with
            | some field => mutable env field path (i + 1)
            | none => fail "invalid tuple accessor"
        | _ => fail "expected tuple type"
    | none => fail "invalid path"

def mutLVal (env : Env) (lv : LVal) : CheckM Bool := do
  let slot ← expectSome "variable undeclared" (Env.get env lv.name)
  mutable env slot.ty lv.path

partial def update (env : Env) (ty : Ty) (path : Path) (i : Nat) (newTy : Ty) (strong : Bool) : CheckM (Env × Ty) :=
  if i == path.length then
    if strong then
      return (env, newTy)
    else
      return (env, ← Ty.union ty newTy)
  else
    match path[i]? with
    | some PathElem.deref =>
        match ty with
        | .box element => do
            let (env, element) ← update env element path (i + 1) newTy true
            return (env, .box element)
        | .borrow isMutable lvals =>
            if !isMutable then
              fail "lval borrowed in part or whole"
            else do
              let env ← lvals.foldlM
                (fun env target => write env (target.traverse path (i + 1)) newTy false)
                env
              return (env, ty)
        | _ => fail "lval is invalid (e.g. incorrectly typed)"
    | some (.index n) =>
        match ty with
        | .tuple fields => do
            let field ← expectSome "invalid tuple accessor" fields[n]?
            let (env, updated) ← update env field path (i + 1) newTy strong
            return (env, .tuple (fields.set n updated))
        | _ => fail "expected tuple type"
    | none => fail "invalid path"
where
  write (env : Env) (lv : LVal) (newTy : Ty) (strong : Bool) : CheckM Env := do
    let slot ← expectSome "variable undeclared" (Env.get env lv.name)
    let (env, ty) ← update env slot.ty lv.path 0 newTy strong
    return Env.put env lv.name { slot with ty := ty }

partial def write (env : Env) (lv : LVal) (newTy : Ty) (strong : Bool := true) : CheckM Env := do
  let slot ← expectSome "variable undeclared" (Env.get env lv.name)
  let (env, ty) ← update env slot.ty lv.path 0 newTy strong
  return Env.put env lv.name { slot with ty := ty }

def joinEnv (lhs rhs : Env) : CheckM Env := do
  let lhsNames := lhs.names
  let rhsNames := rhs.names
  if !((lhsNames.all (fun x => rhsNames.contains x)) && (rhsNames.all (fun x => lhsNames.contains x))) then
    fail "invalid environment keys"
  else
    lhs.foldlM
      (fun acc entry => do
        let rhsSlot ← expectSome "invalid environment keys" (Env.get rhs entry.fst)
        if entry.snd.lifetime != rhsSlot.lifetime then
          fail "invalid environment cells (lifetime)"
        else
          let ty ← Ty.union entry.snd.ty rhsSlot.ty
          return Env.put acc entry.fst { entry.snd with ty := ty })
      ([] : Env)

partial def checkTerm (env : Env) (lifetime : Lifetime) (term : Term) : CheckM (Env × Ty) := do
  match term with
  | .val .unit => return (env, .unit)
  | .val (.int _) => return (env, .int)
  | .val (.ref _) => fail "locations are not source-level syntax"
  | .val (.tuple fields) =>
      -- Runtime tuple values only arise after evaluation. Source tuples use `Term.tuple`.
      return (env, .tuple (fields.map (fun _ => Ty.unit)))
  | .access kind lv => do
      let (ty, _) ← typeOf env lv
      if !(Ty.defined ty) then
        fail "use of moved lval or attempt to move out of lval"
      else if kind == .copy || kind == .temp then
        if kind == .copy && !(Ty.copyable ty) then
          fail "lval's type cannot be copied"
        else if readProhibited env lv then
          fail "lval cannot be read (e.g. is moved in part or whole)"
        else
          return (env, ty)
      else
        if writeProhibited env lv then
          fail "lval cannot be written (e.g. is moved in part or whole)"
        else
          return (← move env lv, ty)
  | .borrow mutableBorrow lv => do
      let (ty, _) ← typeOf env lv
      if !(Ty.defined ty) then
        fail "use of moved lval or attempt to move out of lval"
      else if mutableBorrow then
        if writeProhibited env lv then
          fail "lval cannot be written (e.g. is moved in part or whole)"
        else if !(← mutLVal env lv) then
          fail "lval borrowed in part or whole"
        else
          return (env, .borrow true [lv])
      else if readProhibited env lv then
        fail "lval cannot be read (e.g. is moved in part or whole)"
      else
        return (env, .borrow false [lv])
  | .box operand => do
      let (env, ty) ← checkTerm env lifetime operand
      return (env, .box ty)
  | .letMut x initialiser => do
      if (Env.get env x).isSome then
        fail "variable already declared"
      else
        let (env, ty) ← checkTerm env lifetime initialiser
        return (Env.put env x { ty := ty, lifetime := lifetime }, .unit)
  | .assign lhs rhs => do
      let (lhsTy, targetLifetime) ← typeOf env lhs
      let (env, rhsTy) ← checkTerm env lifetime rhs
      if !(← compatible env lhsTy rhsTy) then
        fail "incompatible type"
      else if !(← Ty.within env targetLifetime rhsTy) then
        fail "lifetime not within"
      else
        let env ← write env lhs rhsTy true
        if writeProhibited env lhs then
          fail "lval borrowed in part or whole"
        else
          return (env, .unit)
  | .block blockLifetime terms => do
      let (env, ty) ← checkSeq env blockLifetime terms
      if !(← Ty.within env lifetime ty) then
        fail "lifetime not within"
      else
        return (Env.dropLifetime env blockLifetime, ty)
  | .tuple terms => do
      let (env, tys, temps) ← carry env lifetime terms 0
      return (Env.removeMany env temps, .tuple tys)
  | .ifElse _ lhs rhs trueBlock falseBlock => do
      let fresh := "?" ++ toString env.length
      let (env, lhsTy) ← checkTerm env lifetime lhs
      let (env, rhsTy) ← checkTerm (Env.put env fresh { ty := lhsTy, lifetime := Lifetime.root }) lifetime rhs
      let env := Env.erase env fresh
      if !(← compatible env lhsTy rhsTy) then
        fail "incompatible type"
      else if !(Ty.copyable lhsTy) || !(Ty.copyable rhsTy) then
        fail "lval's type cannot be copied"
      else
        let (trueEnv, trueTy) ← checkTerm env lifetime trueBlock
        let (falseEnv, falseTy) ← checkTerm env lifetime falseBlock
        let env ← joinEnv trueEnv falseEnv
        if !(← compatible env trueTy falseTy) then
          fail "incompatible type"
        else
          return (env, ← Ty.union trueTy falseTy)
  | .invoke _ _ =>
      fail "TODO functions extension typing is not adequately translated yet"
where
  checkSeq (env : Env) (lifetime : Lifetime) : List Term → CheckM (Env × Ty)
    | [] => return (env, .unit)
    | t :: rest => do
        let (env, ty) ← checkTerm env lifetime t
        match rest with
        | [] => return (env, ty)
        | _ => checkSeq env lifetime rest

  carry (env : Env) (lifetime : Lifetime) : List Term → Nat → CheckM (Env × List Ty × List Name)
    | [], _ => return (env, [], [])
    | t :: rest, n => do
        let (env, ty) ← checkTerm env lifetime t
        let fresh := "?" ++ toString n
        let env := Env.put env fresh { ty := ty, lifetime := Lifetime.root }
        let (env, tys, names) ← carry env lifetime rest (n + 1)
        return (env, ty :: tys, fresh :: names)

def checkProgram (term : Term) : CheckM Ty := do
  let (_, ty) ← checkTerm Env.empty Lifetime.root term
  return ty

def isValid (term : Term) : Bool :=
  match checkProgram term with
  | .ok _ => true
  | .error _ => false

end BorrowChecker
end Core
end LwRust
