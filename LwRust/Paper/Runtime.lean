import LwRust.Core.Syntax

/-!
Runtime structures and primitive actions for the paper formalization.
-/

namespace LwRust
namespace Paper

open Core

abbrev EvalM := Except String

/--
Paper Section 3 store cell.
-/
structure Cell where
  lifetime : Lifetime
  value : Option Value
  deriving BEq, Repr

/--
Paper Section 3 runtime state.
-/
structure State where
  nextAddress : Nat := 0
  heap : List (Nat × Cell) := []
  vars : List (Name × Reference) := []
  deriving BEq, Repr

def fail {α : Type} (msg : String) : EvalM α :=
  Except.error msg

def expectSome {α : Type} (msg : String) : Option α → EvalM α
  | some x => Except.ok x
  | none => fail msg

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
    vars := state.vars,
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

def readValuePath : Value → List Nat → EvalM Value
  | value, [] =>
      match value with
      | .moved => fail "use of moved value"
      | _ => return value
  | .tuple fields, i :: rest => do
      let field ← expectSome "invalid tuple accessor" fields[i]?
      readValuePath field rest
  | .moved, _ :: _ => fail "use of moved value"
  | _, _ :: _ => fail "cannot select field from non-tuple value"

def writeValuePath : Value → List Nat → Value → EvalM Value
  | _, [], newValue => return newValue
  | .tuple fields, i :: rest, newValue => do
      let field ← expectSome "invalid tuple accessor" fields[i]?
      let updated ← writeValuePath field rest newValue
      return .tuple (fields.set i updated)
  | .moved, _ :: _, _ => fail "use of moved value"
  | _, _ :: _, _ => fail "cannot select field from non-tuple value"

namespace State

def readRef (state : State) (ref : Reference) : EvalM Value := do
  let cell ← expectSome "invalid location" (state.getCell ref.address)
  let value ← expectSome "use of moved value" cell.value
  readValuePath value ref.path

def writeRef (state : State) (ref : Reference) (value : Option Value) : EvalM State := do
  let cell ← expectSome "invalid location" (state.getCell ref.address)
  match value with
  | none =>
      if ref.path.isEmpty then
        return state.putCell ref.address { cell with value := none }
      else
        let old ← expectSome "use of moved value" cell.value
        let updated ← writeValuePath old ref.path .moved
        return state.putCell ref.address { cell with value := some updated }
  | some value =>
      if ref.path.isEmpty then
        return state.putCell ref.address { cell with value := some value }
      else
        let old ← expectSome "use of moved value" cell.value
        let updated ← writeValuePath old ref.path value
        return state.putCell ref.address { cell with value := some updated }

def locatePath (state : State) (ref : Reference) : Path → EvalM Reference
  | [] => return ref
  | .deref :: rest => do
      match (← state.readRef ref) with
      | .ref r => locatePath state r rest
      | _ => fail "expected reference value"
  | .index i :: rest =>
      locatePath state (ref.atIndex i) rest

def locate (state : State) (lv : LVal) : EvalM Reference := do
  let root ← expectSome "variable undeclared" (state.getVar lv.name)
  locatePath state root lv.path

def readLVal (state : State) (lv : LVal) : EvalM Value := do
  state.readRef (← state.locate lv)

def writeLVal (state : State) (lv : LVal) (value : Option Value) : EvalM State := do
  state.writeRef (← state.locate lv) value

end State

def locate (state : State) (lv : LVal) : EvalM Reference :=
  state.locate lv

end Paper
end LwRust
