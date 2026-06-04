import LwRust.Core.BorrowChecker

namespace LwRust
namespace Core
namespace OperationalSemantics

abbrev EvalM := Except String

structure Cell where
  lifetime : Lifetime
  value : Option Value
  deriving BEq, Repr

structure State where
  nextAddress : Nat := 0
  heap : List (Nat × Cell) := []
  vars : List (Name × Reference) := []
  deriving BEq, Repr

namespace State

def empty : State := {}

def lookupVar (x : Name) : List (Name × Reference) → Option Reference
  | [] => none
  | (y, r) :: rest => if x == y then some r else lookupVar x rest

def getVar (state : State) (x : Name) : Option Reference :=
  lookupVar x state.vars

def putVar (state : State) (x : Name) (r : Reference) : State :=
  { state with vars := (x, r) :: state.vars.filter (fun entry => entry.fst != x) }

def dropLifetime (state : State) (lifetime : Lifetime) : State :=
  { state with
    vars := state.vars.filter (fun entry =>
      match entry.snd with
      | _ => true),
    heap := state.heap.map (fun entry =>
      if entry.snd.lifetime == lifetime then (entry.fst, { entry.snd with value := none }) else entry) }

def lookupCell (address : Nat) : List (Nat × Cell) → Option Cell
  | [] => none
  | (a, c) :: rest => if a == address then some c else lookupCell address rest

def getCell (state : State) (address : Nat) : Option Cell :=
  lookupCell address state.heap

def putCell (state : State) (address : Nat) (cell : Cell) : State :=
  { state with heap := (address, cell) :: state.heap.filter (fun entry => entry.fst != address) }

def allocate (state : State) (lifetime : Lifetime) (value : Value) : State × Reference :=
  let address := state.nextAddress
  let ref := { address := address, path := [], owner := true }
  ({ state with
      nextAddress := address + 1,
      heap := (address, { lifetime := lifetime, value := some value }) :: state.heap },
    ref)

end State

def fail {α : Type} (msg : String) : EvalM α :=
  Except.error msg

def expectSome {α : Type} (msg : String) : Option α → EvalM α
  | some x => Except.ok x
  | none => fail msg

partial def Value.readPath (value : Value) : List Nat → EvalM Value
  | [] =>
      match value with
      | .moved => fail "use of moved value"
      | _ => return value
  | i :: rest =>
      match value with
      | .tuple fields => do
          let field ← expectSome "invalid tuple accessor" fields[i]?
          Value.readPath field rest
      | .moved => fail "use of moved value"
      | _ => fail "cannot select field from non-tuple value"

partial def Value.writePath (value : Value) (path : List Nat) (newValue : Value) : EvalM Value :=
  match path with
  | [] => return newValue
  | i :: rest =>
      match value with
      | .tuple fields => do
          let field ← expectSome "invalid tuple accessor" fields[i]?
          let updated ← Value.writePath field rest newValue
          return .tuple (fields.set i updated)
      | .moved => fail "use of moved value"
      | _ => fail "cannot select field from non-tuple value"

def State.readRef (state : State) (ref : Reference) : EvalM Value := do
  let cell ← expectSome "invalid location" (state.getCell ref.address)
  let value ← expectSome "use of moved value" cell.value
  Value.readPath value ref.path

def State.writeRef (state : State) (ref : Reference) (value : Option Value) : EvalM State := do
  let cell ← expectSome "invalid location" (state.getCell ref.address)
  match value with
  | none =>
      if ref.path.isEmpty then
        return state.putCell ref.address { cell with value := none }
      else
        let old ← expectSome "use of moved value" cell.value
        let updated ← Value.writePath old ref.path .moved
        return state.putCell ref.address { cell with value := some updated }
  | some value =>
      if ref.path.isEmpty then
        return state.putCell ref.address { cell with value := some value }
      else
        let old ← expectSome "use of moved value" cell.value
        let updated ← Value.writePath old ref.path value
        return state.putCell ref.address { cell with value := some updated }

partial def locate (state : State) (lv : LVal) : EvalM Reference := do
  let root ← expectSome "variable undeclared" (state.getVar lv.name)
  applyPath state root lv.path
where
  applyPath (state : State) (ref : Reference) : Path → EvalM Reference
    | [] => return ref
    | .deref :: rest => do
        match (← state.readRef ref) with
        | .ref r => applyPath state r rest
        | _ => fail "expected reference value"
    | .index i :: rest =>
        applyPath state (ref.atIndex i) rest

def State.readLVal (state : State) (lv : LVal) : EvalM Value := do
  state.readRef (← locate state lv)

def State.writeLVal (state : State) (lv : LVal) (value : Option Value) : EvalM State := do
  state.writeRef (← locate state lv) value

partial def eval (state : State) (lifetime : Lifetime) (term : Term) : EvalM (State × Value) := do
  match term with
  | .val v => return (state, v)
  | .access kind lv => do
      let value ← state.readLVal lv
      if kind == .move then
        return (← state.writeLVal lv none, value)
      else
        return (state, value)
  | .borrow _ lv => do
      let ref ← locate state lv
      return (state, .ref ref.borrowed)
  | .box operand => do
      let (state, value) ← eval state lifetime operand
      let (state, ref) := state.allocate Lifetime.root value
      return (state, .ref ref)
  | .letMut x initialiser => do
      let (state, value) ← eval state lifetime initialiser
      let (state, ref) := state.allocate lifetime value
      return (state.putVar x ref, .unit)
  | .assign lhs rhs => do
      let (state, value) ← eval state lifetime rhs
      return (← state.writeLVal lhs (some value), .unit)
  | .block blockLifetime terms =>
      let (state, value) ← evalSeq state blockLifetime terms
      return (state.dropLifetime blockLifetime, value)
  | .tuple terms => do
      let (state, values) ← evalTerms state lifetime terms
      return (state, .tuple values)
  | .ifElse eq lhs rhs trueBlock falseBlock => do
      let (state, lhsValue) ← eval state lifetime lhs
      let (state, rhsValue) ← eval state lifetime rhs
      if (lhsValue == rhsValue) == eq then
        eval state lifetime trueBlock
      else
        eval state lifetime falseBlock
  | .invoke _ _ =>
      fail "TODO functions extension semantics is not adequately translated yet"
where
  evalSeq (state : State) (lifetime : Lifetime) : List Term → EvalM (State × Value)
    | [] => return (state, .unit)
    | t :: rest => do
        let (state, value) ← eval state lifetime t
        match rest with
        | [] => return (state, value)
        | _ => evalSeq state lifetime rest

  evalTerms (state : State) (lifetime : Lifetime) : List Term → EvalM (State × List Value)
    | [] => return (state, [])
    | t :: rest => do
        let (state, value) ← eval state lifetime t
        let (state, values) ← evalTerms state lifetime rest
        return (state, value :: values)

def execute (term : Term) : EvalM Value := do
  discard <| BorrowChecker.checkProgram term
  let (_, value) ← eval State.empty Lifetime.root term
  return value

end OperationalSemantics
end Core
end LwRust
