import LwRust.Core.Syntax

/-!
Finite program-space generation.

Java source: `FeatherweightRust/src/featherweightrust/core/ProgramSpace.java`.

The Java implementation uses `jmodelgen` `Domain` and `Walker` objects for lazy
enumeration and exact cardinality accounting.  This Lean translation keeps the
same bounded-program intent, but materializes finite `List`s instead.

TODO: Reproduce the exact `jmodelgen` cursor ordering, `BigInteger`-backed API,
and efficient lazy walking interface if those experiments are ported. The
finite list model matches the Java runtime cardinalities covered by tests. Note
that the Java source comment lists `P{1,1,2,2}_def(3)` as `21432`, but running
`ProgramSpace.definedVariableWalker` returns `8436`, which is the Lean count.
-/

namespace LwRust
namespace Core
namespace ProgramSpace

def variableNames : List Name :=
  ["x", "y", "z", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
    "n", "o", "p", "q", "r", "s", "t", "u", "v", "w"]

structure Config where
  intCount : Nat
  maxVariables : Nat
  maxBlockDepth : Nat
  maxBlockWidth : Nat
  deriving BEq, Repr

def Config.render (cfg : Config) : String :=
  "P{" ++ toString cfg.intCount ++ "," ++ toString cfg.maxVariables ++ "," ++
    toString cfg.maxBlockDepth ++ "," ++ toString cfg.maxBlockWidth ++ "}"

def intTerms (count : Nat) : List Term :=
  (List.range count).map (fun n => int (Int.ofNat n))

def declaredNames (cfg : Config) : List Name :=
  variableNames.take cfg.maxVariables

def lvals (names : List Name) : List LVal :=
  names.flatMap (fun x =>
    let root := var x
    [root, deref root])

def boxDepth (depth : Nat) (term : Term) : Term :=
  match depth with
  | 0 => box term
  | n + 1 => boxDepth n (box term)

def expressions (cfg : Config) (names : List Name) : List Term :=
  let atoms := intTerms cfg.intCount
  let accesses := (lvals names).flatMap (fun lv => [move lv, copy lv])
  let borrows := (lvals names).flatMap (fun lv => [borrow lv, borrowMut lv])
  let terminals := atoms ++ accesses ++ borrows
  let boxes :=
    (List.range 1).flatMap (fun depth =>
      terminals.map (boxDepth depth))
  terminals ++ boxes

def assignments (cfg : Config) (names : List Name) : List Term :=
  (lvals names).flatMap (fun lv => (expressions cfg names).map (assign lv))

def lets (cfg : Config) (declared : List Name) : List Term :=
  match variableNames[declared.length]? with
  | some x =>
      if declared.length < cfg.maxVariables then
        (expressions cfg declared).map (letMut x)
      else
        []
  | none => []

partial def listsOfLength (length : Nat) (stmts : List Term) : List (List Term) :=
  match length with
  | 0 => [[]]
  | n + 1 => stmts.flatMap (fun stmt => (listsOfLength n stmts).map (fun tail => stmt :: tail))

def statementLists (width : Nat) (stmts : List Term) : List (List Term) :=
  (List.range (width + 1)).flatMap (fun n => listsOfLength n stmts)

partial def unconstrainedTerms (cfg : Config) (depth : Nat) (lifetime : Lifetime) : List Term :=
  let names := declaredNames cfg
  let units := (declaredNames cfg).flatMap (fun x => (expressions cfg names).map (letMut x)) ++
    assignments cfg names
  if depth == 0 then
    units
  else
    let nestedTerms := unconstrainedTerms cfg (depth - 1) (lifetime ++ [0])
    let blocks := (statementLists cfg.maxBlockWidth nestedTerms).filter (fun ts => !ts.isEmpty) |>.map
      (fun terms => block (lifetime ++ [0]) terms)
    units ++ blocks

def domain (cfg : Config) : List Term :=
  let lifetime := [0]
  let terms := unconstrainedTerms cfg (cfg.maxBlockDepth - 1) lifetime
  (statementLists cfg.maxBlockWidth terms).filter (fun ts => !ts.isEmpty) |>.map (block lifetime)

def containsVar (x : Name) : Term → Bool
  | .letMut y _ => x == y
  | _ => false

def updateDeclared (cfg : Config) (declared : List Name) (term : Term) : List Name :=
  match term with
  | .letMut x _ =>
      if declared.contains x then declared
      else (declared ++ [x]).take cfg.maxVariables
  | _ => declared

partial def blockCount : Term → Nat
  | .block _ terms => 1 + terms.foldl (fun acc term => acc + blockCount term) 0
  | _ => 0

def updateBlocks (blocks : Nat) (term : Term) : Nat :=
  blocks - blockCount term

mutual
  partial def definedTerms (cfg : Config) (depth blocks : Nat) (lifetime : Lifetime) (declared : List Name) :
      List Term :=
    let units := lets cfg declared ++ assignments cfg declared
    if depth == 0 || blocks == 0 then
      units
    else
      let childLifetime := lifetime ++ [declared.length]
      let childBlocks := (definedSequences cfg (depth - 1) (blocks - 1) cfg.maxBlockWidth childLifetime declared)
        |>.filter (fun ts => !ts.isEmpty)
        |>.map (block childLifetime)
      units ++ childBlocks

partial def definedSequences (cfg : Config) (depth blocks width : Nat) (lifetime : Lifetime) (declared : List Name) :
    List (List Term) :=
  match width with
  | 0 => [[]]
  | n + 1 =>
      let stop := [[]]
      let stmts := definedTerms cfg depth blocks lifetime declared
      let extend := stmts.flatMap (fun stmt =>
        let declared' := updateDeclared cfg declared stmt
        let blocks' := updateBlocks blocks stmt
        (definedSequences cfg depth blocks' n lifetime declared').map (fun tail => stmt :: tail))
      stop ++ extend
end

def definedVariablePrograms (cfg : Config) (maxBlocks : Nat) : List Term :=
  let lifetime := [0]
  let depth := cfg.maxBlockDepth - 1
  let blocks := maxBlocks - 1
  (definedSequences cfg depth blocks cfg.maxBlockWidth lifetime []).filter (fun ts => !ts.isEmpty) |>.map
    (block lifetime)

end ProgramSpace
end Core
end LwRust
