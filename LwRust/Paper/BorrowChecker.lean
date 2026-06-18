import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

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
  match env.lookup name with
  | none => true
  | some _ => false

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

theorem fresh_sound {env : FiniteEnv} {name : Name} :
    env.fresh name = true → env.toEnv.fresh name := by
  intro h
  cases hlookup : env.lookup name with
  | none =>
      simp [Env.fresh, toEnv, hlookup]
  | some slot =>
      simp [fresh, hlookup] at h

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
  { entries := env.entries.filter (fun entry =>
      match env.lookup entry.1 with
      | some slot =>
          decide (slot = entry.2) && !decide (slot.lifetime = lifetime)
      | none => false) }

private theorem lookupEntries_filter_congr_for_name
    {entries : List (Name × EnvSlot)} {p q : Name × EnvSlot → Bool}
    {needle : Name}
    (h : ∀ entry, entry ∈ entries → entry.1 = needle → p entry = q entry) :
    lookupEntries (entries.filter p) needle =
      lookupEntries (entries.filter q) needle := by
  induction entries with
  | nil =>
      simp [lookupEntries]
  | cons entry rest ih =>
      have hrest : ∀ e, e ∈ rest → e.1 = needle → p e = q e := by
        intro e he hname
        exact h e (List.mem_cons_of_mem _ he) hname
      rcases entry with ⟨entryName, entrySlot⟩
      by_cases hname : entryName = needle
      · subst entryName
        have hpq := h (needle, entrySlot) List.mem_cons_self rfl
        cases hp : p (needle, entrySlot) <;>
          cases hq : q (needle, entrySlot) <;>
          simp [List.filter, hp, hq, lookupEntries, ih hrest] at hpq ⊢
      · have hnameNeedle : ¬ needle = entryName :=
          fun hne => hname hne.symm
        cases hp : p (entryName, entrySlot) <;>
          cases hq : q (entryName, entrySlot) <;>
          simp [List.filter, hp, hq, lookupEntries, hnameNeedle, ih hrest]

private theorem lookupEntries_filter_none_of_name_false
    {entries : List (Name × EnvSlot)} {p : Name × EnvSlot → Bool}
    {needle : Name}
    (h : ∀ entry, entry ∈ entries → entry.1 = needle → p entry = false) :
    lookupEntries (entries.filter p) needle = none := by
  induction entries with
  | nil =>
      simp [lookupEntries]
  | cons entry rest ih =>
      have hrest : ∀ e, e ∈ rest → e.1 = needle → p e = false := by
        intro e he hname
        exact h e (List.mem_cons_of_mem _ he) hname
      rcases entry with ⟨entryName, entrySlot⟩
      by_cases hname : entryName = needle
      · subst entryName
        have hp := h (needle, entrySlot) List.mem_cons_self rfl
        simp [List.filter, hp, ih hrest]
      · have hnameNeedle : ¬ needle = entryName :=
          fun hne => hname hne.symm
        cases hp : p (entryName, entrySlot) <;>
          simp [List.filter, hp, lookupEntries, hnameNeedle, ih hrest]

private theorem lookupEntries_dropLifetime_filter
    (entries : List (Name × EnvSlot)) (lifetime : Lifetime) (needle : Name) :
    lookupEntries
        (entries.filter (fun entry =>
          match lookupEntries entries entry.1 with
          | some slot =>
              decide (slot = entry.2) && !decide (slot.lifetime = lifetime)
          | none => false)) needle =
      match lookupEntries entries needle with
      | some slot => if slot.lifetime = lifetime then none else some slot
      | none => none := by
  induction entries with
  | nil =>
      simp [lookupEntries]
  | cons entry rest ih =>
      rcases entry with ⟨entryName, entrySlot⟩
      by_cases hneedle : needle = entryName
      · subst needle
        by_cases hlife : entrySlot.lifetime = lifetime
        · have hnone :
            lookupEntries
              (rest.filter (fun entry =>
                match (if entry.1 = entryName then some entrySlot
                  else lookupEntries rest entry.1) with
                | some slot =>
                    decide (slot = entry.2) &&
                      !decide (slot.lifetime = lifetime)
                | none => false)) entryName = none := by
              apply lookupEntries_filter_none_of_name_false
              intro e _he hename
              subst hename
              by_cases hslot : entrySlot = e.2
              · subst entrySlot
                simp [hlife]
              · simp [hslot]
          simp [List.filter, lookupEntries, hlife, hnone]
        · simp [List.filter, lookupEntries, hlife]
      · have hcongr :
          lookupEntries
              (rest.filter (fun entry =>
                match (if entry.1 = entryName then some entrySlot
                  else lookupEntries rest entry.1) with
                | some slot =>
                    decide (slot = entry.2) &&
                      !decide (slot.lifetime = lifetime)
                | none => false)) needle =
            lookupEntries
              (rest.filter (fun entry =>
                match lookupEntries rest entry.1 with
                | some slot =>
                    decide (slot = entry.2) &&
                      !decide (slot.lifetime = lifetime)
                | none => false)) needle := by
            apply lookupEntries_filter_congr_for_name
            intro e _he hename
            have hne : e.1 ≠ entryName := by
              intro heq
              exact hneedle (hename.symm.trans heq)
            simp [hne]
        cases hkeep : (!decide (entrySlot.lifetime = lifetime)) <;>
          simp [List.filter, lookupEntries, hneedle, hkeep]
        · rw [hcongr, ih]
        · rw [hcongr, ih]

@[simp] theorem toEnv_dropLifetime (env : FiniteEnv) (lifetime : Lifetime) :
    (env.dropLifetime lifetime).toEnv = env.toEnv.dropLifetime lifetime := by
  cases env with
  | mk entries =>
      apply congrArg Env.mk
      funext needle
      change
        lookupEntries
          (entries.filter (fun entry =>
            match lookupEntries entries entry.1 with
            | some slot =>
                decide (slot = entry.2) &&
                  !decide (slot.lifetime = lifetime)
            | none => false)) needle =
          match lookupEntries entries needle with
          | some slot =>
              if slot.lifetime = lifetime then none else some slot
          | none => none
      exact lookupEntries_dropLifetime_filter entries lifetime needle

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
  names.all (fun name =>
    if left.lookup name = right.lookup name then true else false)

theorem sameBindings_self (env : FiniteEnv) :
    env.sameBindings env = true := by
  unfold sameBindings
  exact List.all_eq_true.mpr (by
    intro name _hmem
    simp)

end FiniteEnv

private def lvalMem (target : LVal) : List LVal → Bool
  | [] => false
  | head :: rest =>
      if target = head then true else lvalMem target rest

private theorem lvalMem_true_iff {target : LVal} {targets : List LVal} :
    lvalMem target targets = true ↔ target ∈ targets := by
  induction targets with
  | nil =>
      simp [lvalMem]
  | cons head rest ih =>
      by_cases heq : target = head
      · subst heq
        simp [lvalMem]
      · simp [lvalMem, heq, ih]

private def insertLVal (targets : List LVal) (target : LVal) : List LVal :=
  if lvalMem target targets then targets else targets ++ [target]

private def unionLVals (left right : List LVal) : List LVal :=
  right.foldl insertLVal left

private theorem mem_insertLVal {candidate target : LVal}
    {targets : List LVal} :
    candidate ∈ insertLVal targets target ↔
      candidate ∈ targets ∨ candidate = target := by
  unfold insertLVal
  cases hcheck : lvalMem target targets
  · simpa [hcheck] using
      (List.mem_append :
        candidate ∈ targets ++ [target] ↔
          candidate ∈ targets ∨ candidate ∈ [target])
  · have htarget : target ∈ targets :=
      lvalMem_true_iff.mp hcheck
    simp [hcheck]
    intro h
    subst h
    exact htarget

private theorem mem_unionLVals {candidate : LVal}
    {left right : List LVal} :
    candidate ∈ unionLVals left right ↔
      candidate ∈ left ∨ candidate ∈ right := by
  unfold unionLVals
  induction right generalizing left with
  | nil =>
      simp
  | cons target rest ih =>
      rw [List.foldl_cons, ih, mem_insertLVal]
      constructor
      · intro hmem
        rcases hmem with hmem | hmem
        · rcases hmem with hmem | hmem
          · exact Or.inl hmem
          · subst hmem
            exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
      · intro hmem
        rcases hmem with hmem | hmem
        · exact Or.inl (Or.inl hmem)
        · cases hmem with
          | head =>
            exact Or.inl (Or.inr rfl)
          | tail _ htail =>
            exact Or.inr htail

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

private def envEqOutside (left right : FiniteEnv) (exceptName : Name) : Bool :=
  let names := unionNames left.support right.support
  names.all (fun name =>
    if name = exceptName then true
    else if left.lookup name = right.lookup name then true else false)

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

private def targetsAllHaveTy? (fuel : Nat) (env : FiniteEnv)
    (ty : Ty) : List LVal → Bool
  | [] => true
  | target :: rest =>
      match lvalType? fuel env target with
      | some (.ty targetTy, _) =>
          if targetTy = ty then targetsAllHaveTy? fuel env ty rest else false
      | _ => false

private def targetListCommonTy? (fuel : Nat) (env : FiniteEnv)
    (targets : List LVal) : Option (Option Ty) :=
  match targets with
  | [] => some none
  | target :: rest =>
      match lvalType? fuel env target with
      | some (.ty ty, _) =>
          if targetsAllHaveTy? fuel env ty rest then some (some ty) else none
      | _ => none

mutual
  private def shapeCompatibleTy
      : Nat → FiniteEnv → Ty → Ty → Bool
    | 0, _, _, _ => false
    | _ + 1, _, .unit, .unit => true
    | _ + 1, _, .int, .int => true
    | _ + 1, _, .bool, .bool => true
    | fuel + 1, env, .box left, .box right =>
        shapeCompatibleTy fuel env left right
    | fuel + 1, env, .borrow mutable₁ leftTargets,
        .borrow mutable₂ rightTargets =>
        mutable₁ == mutable₂ &&
          match targetListCommonTy? fuel env leftTargets,
              targetListCommonTy? fuel env rightTargets with
          | some none, some none => true
          | some none, some (some rightTy) =>
              shapeCompatibleTy fuel env rightTy rightTy
          | some (some leftTy), some none =>
              shapeCompatibleTy fuel env leftTy leftTy
          | some (some leftTy), some (some rightTy) =>
              shapeCompatibleTy fuel env leftTy rightTy
          | _, _ => false
    | _ + 1, _, _, _ => false

  private def shapeCompatiblePartialTy
      : Nat → FiniteEnv → PartialTy → PartialTy → Bool
    | 0, _, _, _ => false
    | fuel + 1, env, .ty left, .ty right =>
        shapeCompatibleTy fuel env left right
    | fuel + 1, env, .box left, .box right =>
        shapeCompatiblePartialTy fuel env left right
    | fuel + 1, env, .undef left, right =>
        shapeCompatiblePartialTy fuel env (.ty left) right
    | fuel + 1, env, left, .undef right =>
        shapeCompatiblePartialTy fuel env left (.ty right)
    | _ + 1, _, _, _ => false
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

mutual
  private def tyCoherent : Nat → FiniteEnv → Ty → Bool
    | _, _, .unit => true
    | _, _, .int => true
    | _, _, .bool => true
    | 0, _, .box _ => false
    | fuel + 1, env, .box inner => tyCoherent fuel env inner
    | 0, _, .borrow _ _ => false
    | fuel + 1, env, .borrow _ targets =>
        match lvalTargetsType? fuel env targets with
        | some (.ty targetTy, _) => tyCoherent fuel env targetTy
        | _ => false

  private def partialTyCoherent : Nat → FiniteEnv → PartialTy → Bool
    | fuel, env, .ty ty => tyCoherent fuel env ty
    | 0, _, .box _ => false
    | fuel + 1, env, .box inner => partialTyCoherent fuel env inner
    | _, _, .undef _ => true
end

private def coherent (fuel : Nat) (env : FiniteEnv) : Bool :=
  env.entries.all (fun entry => partialTyCoherent fuel env entry.2.ty)

mutual
  private def tyCoherentNonempty : Nat → FiniteEnv → Ty → Bool
    | _, _, .unit => true
    | _, _, .int => true
    | _, _, .bool => true
    | 0, _, .box _ => false
    | fuel + 1, env, .box inner => tyCoherentNonempty fuel env inner
    | 0, _, .borrow _ targets => targets == []
    | fuel + 1, env, .borrow _ targets =>
        if targets = [] then
          true
        else
          match lvalTargetsType? fuel env targets with
          | some (.ty targetTy, _) => tyCoherentNonempty fuel env targetTy
          | _ => false

  private def partialTyCoherentNonempty : Nat → FiniteEnv → PartialTy → Bool
    | fuel, env, .ty ty => tyCoherentNonempty fuel env ty
    | 0, _, .box _ => false
    | fuel + 1, env, .box inner => partialTyCoherentNonempty fuel env inner
    | _, _, .undef _ => true
end

private def coherentNonempty (fuel : Nat) (env : FiniteEnv) : Bool :=
  env.entries.all (fun entry => partialTyCoherentNonempty fuel env entry.2.ty)

private def rootCoherent (fuel : Nat) (env : FiniteEnv) (root : Name) : Bool :=
  match env.lookup root with
  | some slot => partialTyCoherent fuel env slot.ty
  | none => false

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

private def envJoinStep? (left right result : FiniteEnv)
    (name : Name) : Option FiniteEnv :=
  match left.lookup name, right.lookup name with
  | some leftSlot, some rightSlot =>
      if leftSlot.lifetime = rightSlot.lifetime then do
        let ty ← partialTyJoin? leftSlot.ty rightSlot.ty
        some (result.update name { ty := ty, lifetime := leftSlot.lifetime })
      else
        none
  | none, none => some result
  | _, _ => none

private def envJoinNames? (left right : FiniteEnv) :
    List Name → FiniteEnv → Option FiniteEnv
  | [], result => some result
  | name :: names, result => do
      let result' ← envJoinStep? left right result name
      envJoinNames? left right names result'

private def envJoin? (left right : FiniteEnv) : Option FiniteEnv :=
  envJoinNames? left right (unionNames left.support right.support)
    FiniteEnv.empty

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

private def guardedRoots (env : FiniteEnv) (source : LVal) : List Name :=
  guardClosure env ((envNames env).length + 1) [] [LVal.base source]

private def guardClosed (env : FiniteEnv) (roots : List Name) : Bool :=
  roots.all (fun root =>
    (mutableBorrowTargetsOfRoot env root).all (fun target =>
      roots.contains (LVal.base target)))

private def assignmentBorrowSafety (env : FiniteEnv) : LVal → Bool
  | .var _ => true
  | .deref source =>
      let roots := guardedRoots env source
      roots.contains (LVal.base source) &&
        guardClosed env roots &&
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
    | [target] => do
        match lvalType? fuel env (prependPath path target) with
        | some (.ty _, _) =>
            envWrite? fuel rank env (prependPath path target) rhsTy
        | _ => none
    | target :: rest => do
        match lvalType? fuel env (prependPath path target) with
        | some (.ty _, _) => pure ()
        | _ => none
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
  borrows.any (fun borrow => lvalMem target borrow.2)

private def linearizedByRanks? (fuel : Nat) (rankSource env : FiniteEnv) :
    Bool :=
  env.entries.all (fun entry =>
    match rankOf? fuel rankSource entry.1 with
    | none => false
    | some rootRank =>
        (PartialTy.vars entry.2.ty).all (fun dep =>
          match rankOf? fuel rankSource dep with
          | some depRank => depRank < rootRank
          | none => false))

private def rhsBorrowTargetsBelow (envBefore result : FiniteEnv) (rhsTy : Ty) :
    Bool :=
  let fuel := (envNames envBefore).length + (envNames result).length + 1
  let rhsBorrows := tyBorrows rhsTy
  let resultBorrows := envBorrowEdges result
  let preLinear := linearizedByRanks? fuel result envBefore
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
  preLinear && rankBelow && fanoutSafe

private def isLifetimeChild (parent child : Lifetime) : Bool :=
  match child.path.drop parent.path.length with
  | [_] => parent.path.isPrefixOf child.path
  | _ => false

mutual
  private def termDiverges : Term → Bool
    | .missing => true
    | .block _ terms => termListDiverges terms
    | _ => false

  private def termListDiverges : List Term → Bool
    | [] => false
    | term :: rest => termDiverges term || termListDiverges rest
end

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
            ensure (decide (oldTyAfter = oldTy) &&
                decide (targetLifetimeAfter = targetLifetime))
              "assignment lhs type changed while checking rhs"
            ensure (shapeCompatiblePartialTy fuel rhsResult.env oldTy (.ty rhsResult.ty))
              "assignment rhs shape is incompatible with lhs"
            ensure (wellFormedTy fuel rhsResult.env rhsResult.ty targetLifetime)
              "assignment rhs type is not well-formed at target lifetime"
            let written ←
              fromOption "assignment environment write failed"
                (envWrite? fuel 0 rhsResult.env lhs rhsResult.ty)
            ensure (envEqOutside rhsResult.env written (LVal.base lhs))
              "assignment write changes roots outside its coherence frame"
            ensure (rhsBorrowTargetsBelow rhsResult.env written rhsResult.ty)
              "assignment rhs borrow targets are not below written roots"
            ensure (containedBorrowsWellFormed fuel written && linearizable written)
              "assignment result environment violates containment or linearization"
            ensure (coherentNonempty fuel written)
              "assignment result nonempty borrows are not coherent"
            ensure (rootCoherent fuel written (LVal.base lhs))
              "assignment written root is not coherent"
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
            ensure (wellFormedKit fuel ghostEnv)
              "equality ghost environment is not well formed"
            discard <| checkTerm? fuel ghostEnv typing lifetime rhs
            let rhsResult ← checkTerm? fuel lhsResult.env typing lifetime rhs
            ensure (copyTy rhsResult.ty) "equality rhs is not copyable"
            ensure (shapeCompatiblePartialTy fuel rhsResult.env
              (.ty lhsResult.ty) (.ty rhsResult.ty))
              "equality operand shapes are incompatible"
            pure ⟨.bool, rhsResult.env⟩
        | .ite condition trueBranch falseBranch => do
            let conditionResult ← checkTerm? fuel env typing lifetime condition
            ensure (decide (conditionResult.ty = .bool)) "if condition is not bool"
            let thenResult ← checkTerm? fuel conditionResult.env typing lifetime trueBranch
            let falseResult ← checkTerm? fuel conditionResult.env typing lifetime falseBranch
            match partialTyJoin? (.ty thenResult.ty) (.ty falseResult.ty),
                envJoin? thenResult.env falseResult.env with
            | some (.ty joinTy), some joinEnv =>
                ensure (envJoinSameShape thenResult.env joinEnv)
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
                  pure thenResult
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
            ensure (decide (result.ty = expected))
              "term inferred type differs from expected type"
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
    ensure (decide (conditionResult.ty = .bool)) "while condition is not bool"
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
        ensure (decide (conditionResult.ty = .bool))
          "while-join condition is not bool"
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
          ensure (decide (entryCondition.ty = .bool))
            "entry-side while condition is not bool"
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
  (if result.ty = expectedTy then true else false) &&
    result.env.sameBindings expectedEnv

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

def checkerErrorUnknown? (message : String) : Bool :=
  message = "borrow checker fuel exhausted" ||
    message = "while-join invariant iteration did not converge" ||
    message = "cannot infer type for missing; use checkTermAs?" ||
    message = "diverging while bodies require an expected body type in this checker" ||
    message = "copy operand is not typeable" ||
    message = "move operand is not typeable" ||
    message = "borrow operand is not typeable" ||
    message = "assignment lhs is not typeable" ||
    message = "assignment lhs is not typeable after rhs" ||
    message = "equality operand shapes are incompatible" ||
    message = "assignment rhs shape is incompatible with lhs" ||
    message = "assignment environment write failed"

def checkTermFails? (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term) : Bool :=
  match checkTerm? fuel env typing lifetime term with
  | .ok _ => false
  | .error message => !checkerErrorUnknown? message

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

def declare {fuel : Nat} {env initEnv outEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {name : Name}
    {initialiser : Term} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.letMut name initialiser)
        .unit outEnv = true)
    (freshIn : env.toEnv.fresh name)
    (initialiserCert :
      CertifiedTermCheck fuel env typing lifetime initialiser ty initEnv)
    (freshOut : initEnv.toEnv.fresh name)
    (coherence :
      FreshUpdateCoherenceObligations initEnv.toEnv name ty lifetime)
    (outEq :
      outEnv.toEnv =
        initEnv.toEnv.update name { ty := .ty ty, lifetime := lifetime }) :
    CertifiedTermCheck fuel env typing lifetime (.letMut name initialiser)
      .unit outEnv :=
  { checked := checked
    typing :=
      TermTyping.declare freshIn initialiserCert.typing freshOut coherence
        outEq }

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

This is intentionally separate from `checkTermFails?`: the boolean says the
executable checker produced a finite rule-premise failure rather than an
unknown result, while `notyping` is the logical non-typability proof.  A failed
checker run alone is not used as a completeness theorem.
-/
structure CertifiedTermReject (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term) : Type where
  checked : checkTermFails? fuel env typing lifetime term = true
  notyping :
    ¬ ∃ ty outEnv, TermTyping env.toEnv typing lifetime term ty outEnv

namespace CertifiedTermReject

def found? {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
    (certificate? :
      Option (CertifiedTermReject fuel env typing lifetime term)) : Bool :=
  certificate?.isSome

theorem checkedFailure {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
    (certificate : CertifiedTermReject fuel env typing lifetime term) :
    checkTermFails? fuel env typing lifetime term = true :=
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
`checkTermMatches? ... = true`, `borrowCheckFailed? ... = true`, or
`borrowUnknown? ... = true`.
-/
syntax (name := borrow_run_tactic) "borrow_run" : tactic

macro_rules
  | `(tactic| borrow_run) => `(tactic| native_decide)

/--
Project facts from a proof-carrying borrow-checking certificate.

Bare `borrow_check` proves closed `borrowCheck` goals by running the executable
checker with the default public-example fuel and applying its soundness bridge.
It also proves proof-carrying accepted, failed, and unknown witness goals from
the corresponding executable booleans.  `borrow_check[n]` uses explicit fuel.
`borrow_check[n, result]` proves exact closed `TermTyping` goals from a
computed `CheckResult`.  `borrow_check[n, inEnv, outEnv]` proves exact
term-level `TermTyping` or `TermListTyping` goals by running
`checkTermMatches?` or `checkTermListMatches?` from the finite input
environment to the finite output environment, for empty store typings and
goals whose environments are written as `inEnv.toEnv` and `outEnv.toEnv`.
`borrow_check using cert` exposes the proof stored in a proof-carrying
certificate.
-/
syntax (name := borrow_check_tactic) "borrow_check" (" using " term)? : tactic
syntax (name := borrow_check_fuel_tactic) "borrow_check" "[" term "]" : tactic
syntax (name := borrow_check_result_tactic)
  "borrow_check" "[" term ", " term "]" : tactic
syntax (name := borrow_check_term_result_tactic)
  "borrow_check" "[" term ", " term ", " term "]" : tactic

inductive BorrowCheckVerdict where
  | accepted
  | failed
  | unknown
  deriving DecidableEq, Repr

def borrowCheckVerdict? (fuel : Nat) (term : Term) : BorrowCheckVerdict :=
  match checkProgram? fuel term with
  | .ok _ => .accepted
  | .error message =>
      if checkerErrorUnknown? message then .unknown else .failed

def borrowCheck? (fuel : Nat) (term : Term) : Bool :=
  match borrowCheckVerdict? fuel term with
  | .accepted => true
  | .failed => false
  | .unknown => false

/--
The executable checker found a rule-premise failure in the given finite run,
rather than accepting or reporting an unknown result.  This is not the same
thing as logical rejection; use `borrowReject`, `CertifiedTermReject`, or a
closed `CertifiedBorrowReject` when a non-typability proof is required.
-/
def borrowCheckFailed? (fuel : Nat) (term : Term) : Bool :=
  match borrowCheckVerdict? fuel term with
  | .accepted => false
  | .failed => true
  | .unknown => false

def borrowUnknown? (fuel : Nat) (term : Term) : Bool :=
  match borrowCheckVerdict? fuel term with
  | .accepted => false
  | .failed => false
  | .unknown => true

/--
Proof-carrying finite checker failure.

This records only the executable failure classification: the program checker
returned a non-unknown error message.  It deliberately does not contain a
non-typability proof; use `CertifiedBorrowReject` for logical rejection.
-/
structure CertifiedBorrowFailure (fuel : Nat) (term : Term) : Type where
  checked : borrowCheckFailed? fuel term = true

namespace CertifiedBorrowFailure

def found? {fuel : Nat} {term : Term}
    (certificate? : Option (CertifiedBorrowFailure fuel term)) : Bool :=
  certificate?.isSome

theorem checkedFailure {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowFailure fuel term) :
    borrowCheckFailed? fuel term = true :=
  certificate.checked

theorem checkerError {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowFailure fuel term) :
    ∃ message,
      checkProgram? fuel term = .error message ∧
        checkerErrorUnknown? message = false := by
  have h := certificate.checked
  unfold borrowCheckFailed? borrowCheckVerdict? at h
  cases hcheck : checkProgram? fuel term with
  | ok result =>
      simp [hcheck] at h
  | error message =>
      cases hunknown : checkerErrorUnknown? message
      · exact ⟨message, rfl, hunknown⟩
      · simp [hcheck, hunknown] at h

theorem checkedFailure_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowFailure fuel term)} :
    found? certificate? = true → borrowCheckFailed? fuel term = true := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.checkedFailure

end CertifiedBorrowFailure

/--
Proof-carrying unknown checker result.

This records that the executable checker returned an error classified as
unknown, such as fuel exhaustion or an inference limitation.
-/
structure CertifiedBorrowUnknown (fuel : Nat) (term : Term) : Type where
  checked : borrowUnknown? fuel term = true

namespace CertifiedBorrowUnknown

def found? {fuel : Nat} {term : Term}
    (certificate? : Option (CertifiedBorrowUnknown fuel term)) : Bool :=
  certificate?.isSome

theorem checkedUnknown {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowUnknown fuel term) :
    borrowUnknown? fuel term = true :=
  certificate.checked

theorem checkerError {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowUnknown fuel term) :
    ∃ message,
      checkProgram? fuel term = .error message ∧
        checkerErrorUnknown? message = true := by
  have h := certificate.checked
  unfold borrowUnknown? borrowCheckVerdict? at h
  cases hcheck : checkProgram? fuel term with
  | ok result =>
      simp [hcheck] at h
  | error message =>
      cases hunknown : checkerErrorUnknown? message
      · simp [hcheck, hunknown] at h
      · exact ⟨message, rfl, hunknown⟩

theorem checkedUnknown_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowUnknown fuel term)} :
    found? certificate? = true → borrowUnknown? fuel term = true := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.checkedUnknown

end CertifiedBorrowUnknown

def certifyBorrowFailure? (fuel : Nat) (term : Term) :
    Option (CertifiedBorrowFailure fuel term) :=
  if hchecked : borrowCheckFailed? fuel term = true then
    some { checked := hchecked }
  else
    none

theorem certifyBorrowFailure?_found_iff {fuel : Nat} {term : Term} :
    CertifiedBorrowFailure.found? (certifyBorrowFailure? fuel term) = true ↔
      borrowCheckFailed? fuel term = true := by
  unfold CertifiedBorrowFailure.found? certifyBorrowFailure?
  by_cases hchecked : borrowCheckFailed? fuel term = true <;> simp [hchecked]

/--
Proof-level reflection target for finite checker failures.

This is the failed-verdict analogue of `borrowCheckWitness`: it says the
checker produced a non-unknown failure witness, not that the program is
logically untypable.
-/
def borrowCheckFailureWitness (fuel : Nat) (term : Term) : Prop :=
  Nonempty (CertifiedBorrowFailure fuel term)

theorem borrowCheckFailed?_eq_true_iff_witness {fuel : Nat} {term : Term} :
    borrowCheckFailed? fuel term = true ↔
      borrowCheckFailureWitness fuel term := by
  constructor
  · intro hfailed
    exact ⟨{ checked := hfailed }⟩
  · intro hwitness
    rcases hwitness with ⟨certificate⟩
    exact certificate.checkedFailure

theorem borrowCheckFailureWitness_checked {fuel : Nat} {term : Term} :
    borrowCheckFailureWitness fuel term →
      borrowCheckFailed? fuel term = true := by
  intro hwitness
  exact (borrowCheckFailed?_eq_true_iff_witness).2 hwitness

theorem borrowCheckFailureWitness_of_certifyBorrowFailure?
    {fuel : Nat} {term : Term} :
    CertifiedBorrowFailure.found? (certifyBorrowFailure? fuel term) = true →
      borrowCheckFailureWitness fuel term := by
  intro hfound
  exact (borrowCheckFailed?_eq_true_iff_witness).1
    ((certifyBorrowFailure?_found_iff).1 hfound)

def certifyBorrowUnknown? (fuel : Nat) (term : Term) :
    Option (CertifiedBorrowUnknown fuel term) :=
  if hchecked : borrowUnknown? fuel term = true then
    some { checked := hchecked }
  else
    none

theorem certifyBorrowUnknown?_found_iff {fuel : Nat} {term : Term} :
    CertifiedBorrowUnknown.found? (certifyBorrowUnknown? fuel term) = true ↔
      borrowUnknown? fuel term = true := by
  unfold CertifiedBorrowUnknown.found? certifyBorrowUnknown?
  by_cases hchecked : borrowUnknown? fuel term = true <;> simp [hchecked]

/--
Proof-level reflection target for unknown checker results.
-/
def borrowUnknownWitness (fuel : Nat) (term : Term) : Prop :=
  Nonempty (CertifiedBorrowUnknown fuel term)

theorem borrowUnknown?_eq_true_iff_witness {fuel : Nat} {term : Term} :
    borrowUnknown? fuel term = true ↔ borrowUnknownWitness fuel term := by
  constructor
  · intro hunknown
    exact ⟨{ checked := hunknown }⟩
  · intro hwitness
    rcases hwitness with ⟨certificate⟩
    exact certificate.checkedUnknown

theorem borrowUnknownWitness_checked {fuel : Nat} {term : Term} :
    borrowUnknownWitness fuel term → borrowUnknown? fuel term = true := by
  intro hwitness
  exact (borrowUnknown?_eq_true_iff_witness).2 hwitness

theorem borrowUnknownWitness_of_certifyBorrowUnknown?
    {fuel : Nat} {term : Term} :
    CertifiedBorrowUnknown.found? (certifyBorrowUnknown? fuel term) = true →
      borrowUnknownWitness fuel term := by
  intro hfound
  exact (borrowUnknown?_eq_true_iff_witness).1
    ((certifyBorrowUnknown?_found_iff).1 hfound)

/--
Proof-facing closed-program borrow/type check.

This is the inductive property that a closed source term has some declarative
typing derivation from the empty environment and empty store typing.  The
executable boolean is `borrowCheck?`; `borrowCheck?_sound` bridges
from `borrowCheck? fuel term = true` to `borrowCheck term`.
-/
def borrowCheck (term : Term) : Prop :=
  ∃ ty env, TermTyping Env.empty StoreTyping.empty Lifetime.root term ty env

/--
Proof-facing closed-program rejection.

This is deliberately stronger than `borrowCheckFailed? fuel term = true`: an
executable rule failure is not yet a completeness theorem for non-typability.
Logical rejection is therefore exposed through proof-carrying rejection
certificates, with `CertifiedBorrowReject` packaging the closed-program case.
-/
def borrowReject (term : Term) : Prop :=
  ¬ borrowCheck term

theorem borrowCheck_of_typing {term : Term} {ty : Ty} {env : Env}
    (typing : TermTyping Env.empty StoreTyping.empty Lifetime.root term ty env) :
    borrowCheck term :=
  ⟨ty, env, typing⟩

theorem borrowReject_of_no_typing {term : Term}
    (notyping :
      ¬ ∃ ty env, TermTyping Env.empty StoreTyping.empty Lifetime.root term ty env) :
    borrowReject term := by
  intro hcheck
  exact notyping hcheck

namespace CertifiedTermReject

theorem borrowReject {fuel : Nat} {term : Term}
    (certificate :
      CertifiedTermReject fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
        term) :
    LwRust.Paper.borrowReject term :=
  borrowReject_of_no_typing certificate.notyping

end CertifiedTermReject

/--
Closed proof-carrying rejection result.

This is the rejection-shaped counterpart of `CertifiedBorrowCheck`: a value of
this type records both a finite executable checker failure and a proof that the
closed source term has no declarative typing derivation.
-/
structure CertifiedBorrowReject (fuel : Nat) (term : Term) : Type where
  certificate :
    CertifiedTermReject fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
      term

namespace CertifiedBorrowReject

def ofTermReject {fuel : Nat} {term : Term}
    (certificate :
      CertifiedTermReject fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
        term) : CertifiedBorrowReject fuel term :=
  { certificate := certificate }

def found? {fuel : Nat} {term : Term}
    (certificate? : Option (CertifiedBorrowReject fuel term)) : Bool :=
  certificate?.isSome

theorem checkedFailure {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowReject fuel term) :
    borrowCheckFailed? fuel term = true := by
  have hchecked := certificate.certificate.checked
  unfold borrowCheckFailed? borrowCheckVerdict? checkProgram?
  unfold checkTermFails? at hchecked
  cases hcheck :
      checkTerm? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term with
  | ok result =>
      simp [hcheck] at hchecked
  | error message =>
      cases hunknown : checkerErrorUnknown? message
      · simp [hunknown]
      · simp [hcheck, hunknown] at hchecked

theorem borrowReject {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowReject fuel term) :
    LwRust.Paper.borrowReject term :=
  CertifiedTermReject.borrowReject certificate.certificate

theorem checkedFailure_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowReject fuel term)} :
    found? certificate? = true → borrowCheckFailed? fuel term = true := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.checkedFailure

theorem borrowReject_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowReject fuel term)} :
    found? certificate? = true → LwRust.Paper.borrowReject term := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.borrowReject

end CertifiedBorrowReject

theorem borrowUnknown?_zero_on_typable_unit :
    borrowUnknown? 0 (.val .unit) = true ∧ borrowCheck (.val .unit) := by
  constructor
  · native_decide
  · exact borrowCheck_of_typing (TermTyping.const ValueTyping.unit)

theorem checkTermFails?_checker_error {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} :
    checkTermFails? fuel env typing lifetime term = true →
      ∃ message,
        checkTerm? fuel env typing lifetime term = .error message ∧
          checkerErrorUnknown? message = false := by
  intro h
  unfold checkTermFails? at h
  cases hcheck : checkTerm? fuel env typing lifetime term with
  | ok result =>
      simp [hcheck] at h
  | error message =>
      cases hunknown : checkerErrorUnknown? message
      · exact ⟨message, rfl, hunknown⟩
      · simp [hcheck, hunknown] at h

theorem checkTermFails?_eq_true_iff {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term} :
    checkTermFails? fuel env typing lifetime term = true ↔
      ∃ message,
        checkTerm? fuel env typing lifetime term = .error message ∧
          checkerErrorUnknown? message = false := by
  constructor
  · exact checkTermFails?_checker_error
  · rintro ⟨message, hcheck, hunknown⟩
    unfold checkTermFails?
    simp [hcheck, hunknown]

theorem borrowCheckVerdict?_accepted_iff {fuel : Nat} {term : Term} :
    borrowCheckVerdict? fuel term = .accepted ↔
      ∃ result, checkProgram? fuel term = .ok result := by
  constructor
  · intro h
    unfold borrowCheckVerdict? at h
    cases hcheck : checkProgram? fuel term with
    | ok result =>
        exact ⟨result, rfl⟩
    | error message =>
        cases hunknown : checkerErrorUnknown? message <;>
          simp [hcheck, hunknown] at h
  · rintro ⟨result, hcheck⟩
    unfold borrowCheckVerdict?
    simp [hcheck]

theorem borrowCheckVerdict?_failed_iff {fuel : Nat} {term : Term} :
    borrowCheckVerdict? fuel term = .failed ↔
      ∃ message,
        checkProgram? fuel term = .error message ∧
          checkerErrorUnknown? message = false := by
  constructor
  · intro h
    unfold borrowCheckVerdict? at h
    cases hcheck : checkProgram? fuel term with
    | ok result =>
        simp [hcheck] at h
    | error message =>
        cases hunknown : checkerErrorUnknown? message
        · exact ⟨message, rfl, hunknown⟩
        · simp [hcheck, hunknown] at h
  · rintro ⟨message, hcheck, hunknown⟩
    unfold borrowCheckVerdict?
    simp [hcheck, hunknown]

theorem borrowCheckVerdict?_unknown_iff {fuel : Nat} {term : Term} :
    borrowCheckVerdict? fuel term = .unknown ↔
      ∃ message,
        checkProgram? fuel term = .error message ∧
          checkerErrorUnknown? message = true := by
  constructor
  · intro h
    unfold borrowCheckVerdict? at h
    cases hcheck : checkProgram? fuel term with
    | ok result =>
        simp [hcheck] at h
    | error message =>
        cases hunknown : checkerErrorUnknown? message
        · simp [hcheck, hunknown] at h
        · exact ⟨message, rfl, hunknown⟩
  · rintro ⟨message, hcheck, hunknown⟩
    unfold borrowCheckVerdict?
    simp [hcheck, hunknown]

theorem borrowCheckFailed?_checker_error {fuel : Nat} {term : Term} :
    borrowCheckFailed? fuel term = true →
      ∃ message,
        checkProgram? fuel term = .error message ∧
          checkerErrorUnknown? message = false := by
  intro h
  unfold borrowCheckFailed? borrowCheckVerdict? at h
  cases hcheck : checkProgram? fuel term with
  | ok result =>
      simp [hcheck] at h
  | error message =>
      cases hunknown : checkerErrorUnknown? message
      · exact ⟨message, rfl, hunknown⟩
      · simp [hcheck, hunknown] at h

theorem borrowCheckFailed?_eq_true_iff {fuel : Nat} {term : Term} :
    borrowCheckFailed? fuel term = true ↔
      ∃ message,
        checkProgram? fuel term = .error message ∧
          checkerErrorUnknown? message = false := by
  constructor
  · exact borrowCheckFailed?_checker_error
  · rintro ⟨message, hcheck, hunknown⟩
    unfold borrowCheckFailed? borrowCheckVerdict?
    simp [hcheck, hunknown]

theorem borrowUnknown?_checker_error {fuel : Nat} {term : Term} :
    borrowUnknown? fuel term = true →
      ∃ message,
        checkProgram? fuel term = .error message ∧
          checkerErrorUnknown? message = true := by
  intro h
  unfold borrowUnknown? borrowCheckVerdict? at h
  cases hcheck : checkProgram? fuel term with
  | ok result =>
      simp [hcheck] at h
  | error message =>
      cases hunknown : checkerErrorUnknown? message
      · simp [hcheck, hunknown] at h
      · exact ⟨message, rfl, hunknown⟩

theorem borrowUnknown?_eq_true_iff {fuel : Nat} {term : Term} :
    borrowUnknown? fuel term = true ↔
      ∃ message,
        checkProgram? fuel term = .error message ∧
          checkerErrorUnknown? message = true := by
  constructor
  · exact borrowUnknown?_checker_error
  · rintro ⟨message, hcheck, hunknown⟩
    unfold borrowUnknown? borrowCheckVerdict?
    simp [hcheck, hunknown]

theorem borrowCheck?_ok {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true →
      ∃ result, checkProgram? fuel term = .ok result := by
  intro h
  unfold borrowCheck? borrowCheckVerdict? at h
  cases hcheck : checkProgram? fuel term with
  | ok result =>
      exact ⟨result, rfl⟩
  | error message =>
      cases hunknown : checkerErrorUnknown? message <;>
        simp [hcheck, hunknown] at h

theorem borrowCheck?_eq_true_iff {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true ↔
      ∃ result, checkProgram? fuel term = .ok result := by
  constructor
  · exact borrowCheck?_ok
  · rintro ⟨result, hcheck⟩
    unfold borrowCheck? borrowCheckVerdict?
    simp [hcheck]

theorem borrowCheck?_false_of_borrowCheckFailed? {fuel : Nat} {term : Term} :
    borrowCheckFailed? fuel term = true → borrowCheck? fuel term = false := by
  unfold borrowCheckFailed? borrowCheck?
  cases borrowCheckVerdict? fuel term <;> simp

theorem borrowCheck?_false_of_borrowUnknown? {fuel : Nat} {term : Term} :
    borrowUnknown? fuel term = true → borrowCheck? fuel term = false := by
  unfold borrowUnknown? borrowCheck?
  cases borrowCheckVerdict? fuel term <;> simp

/--
Fixed-fuel `borrowCheck? = false` is not a sound logical rejection criterion:
fuel exhaustion can make a typable program unknown, and `borrowCheck?` maps
unknown to false.
-/
theorem borrowCheck?_false_not_rejection_complete :
    ¬ (∀ fuel term, borrowCheck? fuel term = false → borrowReject term) := by
  intro hreject
  rcases borrowUnknown?_zero_on_typable_unit with ⟨hunknown, htyped⟩
  exact hreject 0 (.val .unit)
    (borrowCheck?_false_of_borrowUnknown? hunknown) htyped

theorem borrowCheckFailed?_false_of_borrowCheck? {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true → borrowCheckFailed? fuel term = false := by
  unfold borrowCheck? borrowCheckFailed?
  cases borrowCheckVerdict? fuel term <;> simp

theorem borrowUnknown?_false_of_borrowCheck? {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true → borrowUnknown? fuel term = false := by
  unfold borrowCheck? borrowUnknown?
  cases borrowCheckVerdict? fuel term <;> simp

theorem borrowCheck_of_checkProgram?_sound {fuel : Nat} {term : Term}
    (sound :
      ∀ result,
        checkProgram? fuel term = .ok result →
          TermTyping Env.empty StoreTyping.empty Lifetime.root term
            result.ty result.env.toEnv) :
    borrowCheck? fuel term = true → borrowCheck term := by
  intro h
  rcases borrowCheck?_ok h with ⟨result, hresult⟩
  exact borrowCheck_of_typing (sound result hresult)

namespace CheckedTermTypingWitness

theorem borrowCheck {fuel : Nat} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (witness :
      CheckedTermTypingWitness fuel FiniteEnv.empty StoreTyping.empty
        Lifetime.root term expectedTy expectedEnv) :
    LwRust.Paper.borrowCheck term :=
  ⟨expectedTy, expectedEnv.toEnv, witness.typing⟩

end CheckedTermTypingWitness

namespace CertifiedTermCheck

theorem borrowCheck {fuel : Nat} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
        term expectedTy expectedEnv) :
    LwRust.Paper.borrowCheck term :=
  ⟨expectedTy, expectedEnv.toEnv, certificate.typing⟩

end CertifiedTermCheck

/--
Closed proof-carrying checker result.

This is the certificate-shaped counterpart of `borrowCheck? fuel term`: a value
of this type records the executable successful run and the corresponding
declarative typing derivation from the empty environment.
-/
structure CertifiedBorrowCheck (fuel : Nat) (term : Term) : Type where
  ty : Ty
  env : FiniteEnv
  certificate :
    CertifiedTermCheck fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
      term ty env

namespace CertifiedBorrowCheck

def ofTermCheck {fuel : Nat} {term : Term} {ty : Ty} {env : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
        term ty env) : CertifiedBorrowCheck fuel term :=
  { ty := ty
    env := env
    certificate := certificate }

def found? {fuel : Nat} {term : Term}
    (certificate? : Option (CertifiedBorrowCheck fuel term)) : Bool :=
  certificate?.isSome

theorem checked {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowCheck fuel term) :
    borrowCheck? fuel term = true := by
  rcases certificate with ⟨ty, env, termCertificate⟩
  have hmatches := termCertificate.checked
  unfold borrowCheck? borrowCheckVerdict? checkProgram?
  unfold checkTermMatches? at hmatches
  cases hcheck :
      checkTerm? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term with
  | error message =>
      simp [hcheck] at hmatches
  | ok result =>
      simp

theorem borrowCheck {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowCheck fuel term) :
    LwRust.Paper.borrowCheck term :=
  ⟨certificate.ty, certificate.env.toEnv, certificate.certificate.typing⟩

theorem borrowCheck_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowCheck fuel term)} :
    found? certificate? = true → LwRust.Paper.borrowCheck term := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.borrowCheck

theorem checked_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowCheck fuel term)} :
    found? certificate? = true → borrowCheck? fuel term = true := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.checked

end CertifiedBorrowCheck

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

private theorem tySameShape_sound_aux (left : Ty) :
    ∀ right, tySameShape left right = true → Ty.sameShape left right := by
  refine Ty.rec
    (motive_1 := fun left =>
      ∀ right, tySameShape left right = true → Ty.sameShape left right)
    (motive_2 := fun _ => True)
    ?unit ?int ?borrow ?box ?bool ?partialTy ?partialBox ?partialUndef left
  · intro right h
    cases right <;> simp [tySameShape, Ty.sameShape] at h ⊢
  · intro right h
    cases right <;> simp [tySameShape, Ty.sameShape] at h ⊢
  · intro mutable targets right h
    cases right <;> simp [tySameShape, Ty.sameShape] at h ⊢
    exact h
  · intro inner ih right h
    cases right <;> simp [tySameShape, Ty.sameShape] at h ⊢
    exact ih _ h
  · intro right h
    cases right <;> simp [tySameShape, Ty.sameShape] at h ⊢
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial

private theorem tySameShape_sound {left right : Ty} :
    tySameShape left right = true → Ty.sameShape left right :=
  tySameShape_sound_aux left right

private theorem partialTySameShape_sound_aux (left : PartialTy) :
    ∀ right,
      partialTySameShape left right = true → PartialTy.sameShape left right := by
  refine PartialTy.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun left =>
      ∀ right,
        partialTySameShape left right = true → PartialTy.sameShape left right)
    ?unit ?int ?borrow ?boxTy ?bool ?ty ?box ?undef left
  · trivial
  · trivial
  · intro _ _; trivial
  · intro _ _; trivial
  · trivial
  · intro ty _ right h
    cases right <;> simp [partialTySameShape, PartialTy.sameShape] at h ⊢
    exact tySameShape_sound h
  · intro inner ih right h
    cases right <;> simp [partialTySameShape, PartialTy.sameShape] at h ⊢
    exact ih _ h
  · intro ty _ right h
    cases right <;> simp [partialTySameShape, PartialTy.sameShape] at h ⊢
    exact tySameShape_sound h

private theorem partialTySameShape_sound {left right : PartialTy} :
    partialTySameShape left right = true → PartialTy.sameShape left right :=
  partialTySameShape_sound_aux left right

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

private theorem partialTyStrengthens_undef_to_undef_inv {left right : Ty} :
    PartialTyStrengthens (.undef left) (.undef right) →
      PartialTyStrengthens (.ty left) (.ty right) := by
  intro h
  cases h with
  | reflex =>
      exact PartialTyStrengthens.reflex
  | undefLeft hinner =>
      exact hinner

private theorem partialTyJoin_ty_undef {left right join : Ty} :
    PartialTyJoin (.ty left) (.ty right) (.ty join) →
      PartialTyJoin (.ty left) (.undef right) (.undef join) := by
  intro hjoin
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.intoUndef
        (PartialTyUnion.left_strengthens hjoin)
    · subst hcandidate
      exact PartialTyStrengthens.undefLeft
        (PartialTyUnion.right_strengthens hjoin)
  · intro upper hupper
    have hleftUpper : PartialTyStrengthens (.ty left) upper :=
      hupper (by simp)
    have hrightUpper : PartialTyStrengthens (.undef right) upper :=
      hupper (by simp)
    cases upper with
    | ty upperTy =>
        exact False.elim (PartialTyStrengthens.not_undef_to_ty hrightUpper)
    | box upperInner =>
        exact False.elim (PartialTyStrengthens.not_undef_to_box hrightUpper)
    | undef upperTy =>
        exact PartialTyStrengthens.undefLeft
          (hjoin.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact PartialTyStrengthens.ty_to_undef_inv hleftUpper
            · subst hcandidate
              exact partialTyStrengthens_undef_to_undef_inv hrightUpper))

private theorem partialTyJoin_undef_ty {left right join : Ty} :
    PartialTyJoin (.ty left) (.ty right) (.ty join) →
      PartialTyJoin (.undef left) (.ty right) (.undef join) := by
  intro hjoin
  exact PartialTyUnion.symm
    (partialTyJoin_ty_undef (PartialTyUnion.symm hjoin))

private theorem partialTyJoin_undef_undef {left right join : Ty} :
    PartialTyJoin (.ty left) (.ty right) (.ty join) →
      PartialTyJoin (.undef left) (.undef right) (.undef join) := by
  intro hjoin
  constructor
  · intro candidate hcandidate
    simp at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact PartialTyStrengthens.undefLeft
        (PartialTyUnion.left_strengthens hjoin)
    · subst hcandidate
      exact PartialTyStrengthens.undefLeft
        (PartialTyUnion.right_strengthens hjoin)
  · intro upper hupper
    have hleftUpper : PartialTyStrengthens (.undef left) upper :=
      hupper (by simp)
    have hrightUpper : PartialTyStrengthens (.undef right) upper :=
      hupper (by simp)
    cases upper with
    | ty upperTy =>
        exact False.elim (PartialTyStrengthens.not_undef_to_ty hleftUpper)
    | box upperInner =>
        exact False.elim (PartialTyStrengthens.not_undef_to_box hleftUpper)
    | undef upperTy =>
        exact PartialTyStrengthens.undefLeft
          (hjoin.2 (by
            intro candidate hcandidate
            simp at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact partialTyStrengthens_undef_to_undef_inv hleftUpper
            · subst hcandidate
              exact partialTyStrengthens_undef_to_undef_inv hrightUpper))

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
                  (by
                    intro target htarget
                    exact mem_unionLVals.mpr (Or.inl htarget))
              · subst hcandidate
                exact PartialTyStrengthens.borrow
                  (by
                    intro target htarget
                    exact mem_unionLVals.mpr (Or.inr htarget))
            · intro upper hupper
              have hleftUpper :
                  PartialTyStrengthens
                    (.ty (.borrow mutable leftTargets)) upper :=
                hupper (by simp)
              have hrightUpper :
                  PartialTyStrengthens
                    (.ty (.borrow mutable rightTargets)) upper :=
                hupper (by simp)
              cases hleftUpper with
              | reflex =>
                  have hsubRight :=
                    PartialTyStrengthens.borrow_subset hrightUpper
                  exact PartialTyStrengthens.borrow (by
                    intro target htarget
                    rcases mem_unionLVals.mp htarget with hmem | hmem
                    · exact hmem
                    · exact hsubRight hmem)
              | borrow hsubLeft =>
                  have hsubRight :=
                    PartialTyStrengthens.borrow_subset hrightUpper
                  exact PartialTyStrengthens.borrow (by
                    intro target htarget
                    rcases mem_unionLVals.mp htarget with hmem | hmem
                    · exact hsubLeft hmem
                    · exact hsubRight hmem)
              | intoUndef hinner =>
                  rcases PartialTyStrengthens.from_borrow_inv hinner with
                    ⟨targetTargets, rfl, hsubLeft⟩
                  have hsubRight : rightTargets ⊆ targetTargets := by
                    cases hrightUpper with
                    | intoUndef hinner' =>
                        exact PartialTyStrengthens.borrow_subset hinner'
                  exact PartialTyStrengthens.intoUndef
                    (PartialTyStrengthens.borrow (by
                      intro target htarget
                      rcases mem_unionLVals.mp htarget with hmem | hmem
                      · exact hsubLeft hmem
                      · exact hsubRight hmem))
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

private theorem partialTyJoin?_sound :
    ∀ {left right join : PartialTy},
      partialTyJoin? left right = some join →
        PartialTyJoin left right join
  | .ty left, .ty right, join, h => by
      cases hty : tyJoin? left right with
      | none =>
          simp [partialTyJoin?, hty] at h
      | some ty =>
          simp [partialTyJoin?, hty] at h
          cases h
          exact tyJoin?_sound hty
  | .ty left, .box right, join, h => by
      simp [partialTyJoin?] at h
  | .ty left, .undef right, join, h => by
      cases hty : tyJoin? left right with
      | none =>
          simp [partialTyJoin?, hty] at h
      | some ty =>
          simp [partialTyJoin?, hty] at h
          cases h
          exact partialTyJoin_ty_undef (tyJoin?_sound hty)
  | .box left, .ty right, join, h => by
      simp [partialTyJoin?] at h
  | .box left, .box right, join, h => by
      cases hinner : partialTyJoin? left right with
      | none =>
          simp [partialTyJoin?, hinner] at h
      | some inner =>
          simp [partialTyJoin?, hinner] at h
          cases h
          exact PartialTyUnion.box (partialTyJoin?_sound hinner)
  | .box left, .undef right, join, h => by
      simp [partialTyJoin?] at h
  | .undef left, .ty right, join, h => by
      cases hty : tyJoin? left right with
      | none =>
          simp [partialTyJoin?, hty] at h
      | some ty =>
          simp [partialTyJoin?, hty] at h
          cases h
          exact partialTyJoin_undef_ty (tyJoin?_sound hty)
  | .undef left, .box right, join, h => by
      simp [partialTyJoin?] at h
  | .undef left, .undef right, join, h => by
      cases hty : tyJoin? left right with
      | none =>
          simp [partialTyJoin?, hty] at h
      | some ty =>
          simp [partialTyJoin?, hty] at h
          cases h
          exact partialTyJoin_undef_undef (tyJoin?_sound hty)

private theorem partialTyUnion_borrow_mem_iff {mutable : Bool}
    {leftTargets rightTargets unionTargets : List LVal} {target : LVal} :
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable unionTargets)) →
        (target ∈ unionTargets ↔
          target ∈ leftTargets ∨ target ∈ rightTargets) := by
  intro hunion
  constructor
  · intro htarget
    exact PartialTyUnion.borrow_member hunion htarget
  · intro htarget
    rcases htarget with hleft | hright
    · exact PartialTyStrengthens.borrow_subset
        (PartialTyUnion.left_strengthens hunion) hleft
    · exact PartialTyStrengthens.borrow_subset
        (PartialTyUnion.right_strengthens hunion) hright


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

mutual
  private def TyCoherentWitness : Nat → Env → Ty → Prop
    | _, _, .unit => True
    | _, _, .int => True
    | _, _, .bool => True
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner => TyCoherentWitness fuel env inner
    | 0, _, .borrow _ _ => False
    | fuel + 1, env, .borrow _ targets =>
        ∃ targetTy targetLifetime,
          LValTargetsTyping env targets (.ty targetTy) targetLifetime ∧
            TyCoherentWitness fuel env targetTy

  private def PartialTyCoherentWitness : Nat → Env → PartialTy → Prop
    | fuel, env, .ty ty => TyCoherentWitness fuel env ty
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner =>
        PartialTyCoherentWitness fuel env inner
    | _, _, .undef _ => True
end

mutual
  private def TyCoherentNonemptyWitness : Nat → Env → Ty → Prop
    | _, _, .unit => True
    | _, _, .int => True
    | _, _, .bool => True
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner => TyCoherentNonemptyWitness fuel env inner
    | 0, _, .borrow _ targets => targets = []
    | fuel + 1, env, .borrow _ targets =>
        targets = [] ∨
          ∃ targetTy targetLifetime,
            LValTargetsTyping env targets (.ty targetTy) targetLifetime ∧
              TyCoherentNonemptyWitness fuel env targetTy

  private def PartialTyCoherentNonemptyWitness : Nat → Env → PartialTy → Prop
    | fuel, env, .ty ty => TyCoherentNonemptyWitness fuel env ty
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner =>
        PartialTyCoherentNonemptyWitness fuel env inner
    | _, _, .undef _ => True
end

private theorem coherentWitness_sound (fuel : Nat) :
    (∀ {env : FiniteEnv} {ty : Ty},
      tyCoherent fuel env ty = true →
        TyCoherentWitness fuel env.toEnv ty) ∧
    (∀ {env : FiniteEnv} {partialTy : PartialTy},
      partialTyCoherent fuel env partialTy = true →
        PartialTyCoherentWitness fuel env.toEnv partialTy) := by
  induction fuel with
  | zero =>
      have hty :
          ∀ {env : FiniteEnv} {ty : Ty},
            tyCoherent 0 env ty = true →
              TyCoherentWitness 0 env.toEnv ty := by
        intro env ty h
        cases ty <;> simp [tyCoherent, TyCoherentWitness] at h ⊢
      constructor
      · exact hty
      · intro env partialTy h
        cases partialTy with
        | ty ty =>
            exact hty h
        | box inner =>
            simp [partialTyCoherent] at h
        | undef ty =>
            trivial
  | succ fuel ih =>
      have hty :
          ∀ {env : FiniteEnv} {ty : Ty},
            tyCoherent (fuel + 1) env ty = true →
              TyCoherentWitness (fuel + 1) env.toEnv ty := by
        intro env ty h
        cases ty with
        | unit =>
            trivial
        | int =>
            trivial
        | bool =>
            trivial
        | box inner =>
            exact ih.1 (by simpa [tyCoherent] using h)
        | borrow mutable targets =>
            cases htargets : lvalTargetsType? fuel env targets with
            | none =>
                simp [tyCoherent, htargets] at h
            | some result =>
                rcases result with ⟨partialTy, targetLifetime⟩
                cases partialTy with
                | ty targetTy =>
                    have htargetCoherent :
                        tyCoherent fuel env targetTy = true := by
                      simpa [tyCoherent, htargets] using h
                    exact ⟨targetTy, targetLifetime,
                      lvalTargetsType?_sound htargets,
                      ih.1 htargetCoherent⟩
                | box _ =>
                    simp [tyCoherent, htargets] at h
                | undef _ =>
                    simp [tyCoherent, htargets] at h
      constructor
      · exact hty
      · intro env partialTy h
        cases partialTy with
        | ty ty =>
            exact hty h
        | box inner =>
            exact ih.2 (by simpa [partialTyCoherent] using h)
        | undef ty =>
            trivial

private theorem coherentNonemptyWitness_sound (fuel : Nat) :
    (∀ {env : FiniteEnv} {ty : Ty},
      tyCoherentNonempty fuel env ty = true →
        TyCoherentNonemptyWitness fuel env.toEnv ty) ∧
    (∀ {env : FiniteEnv} {partialTy : PartialTy},
      partialTyCoherentNonempty fuel env partialTy = true →
        PartialTyCoherentNonemptyWitness fuel env.toEnv partialTy) := by
  induction fuel with
  | zero =>
      have hty :
          ∀ {env : FiniteEnv} {ty : Ty},
            tyCoherentNonempty 0 env ty = true →
              TyCoherentNonemptyWitness 0 env.toEnv ty := by
        intro env ty h
        cases ty with
        | unit => trivial
        | int => trivial
        | bool => trivial
        | box inner =>
            simp [tyCoherentNonempty, TyCoherentNonemptyWitness] at h
        | borrow mutable targets =>
            simpa [tyCoherentNonempty, TyCoherentNonemptyWitness] using h
      constructor
      · exact hty
      · intro env partialTy h
        cases partialTy with
        | ty ty =>
            exact hty h
        | box inner =>
            simp [partialTyCoherentNonempty,
              PartialTyCoherentNonemptyWitness] at h
        | undef ty =>
            trivial
  | succ fuel ih =>
      have hty :
          ∀ {env : FiniteEnv} {ty : Ty},
            tyCoherentNonempty (fuel + 1) env ty = true →
              TyCoherentNonemptyWitness (fuel + 1) env.toEnv ty := by
        intro env ty h
        cases ty with
        | unit => trivial
        | int => trivial
        | bool => trivial
        | box inner =>
            exact ih.1 (by simpa [tyCoherentNonempty] using h)
        | borrow mutable targets =>
            by_cases htargets : targets = []
            · exact Or.inl htargets
            · cases htargetType : lvalTargetsType? fuel env targets with
              | none =>
                  simp [tyCoherentNonempty, htargets, htargetType] at h
              | some result =>
                  rcases result with ⟨partialTy, targetLifetime⟩
                  cases partialTy with
                  | ty targetTy =>
                      have htargetCoherent :
                          tyCoherentNonempty fuel env targetTy = true := by
                        simpa [tyCoherentNonempty, htargets, htargetType] using h
                      exact Or.inr ⟨targetTy, targetLifetime,
                        lvalTargetsType?_sound htargetType,
                        ih.1 htargetCoherent⟩
                  | box _ =>
                      simp [tyCoherentNonempty, htargets, htargetType] at h
                  | undef _ =>
                      simp [tyCoherentNonempty, htargets, htargetType] at h
      constructor
      · exact hty
      · intro env partialTy h
        cases partialTy with
        | ty ty =>
            exact hty h
        | box inner =>
            exact ih.2 (by simpa [partialTyCoherentNonempty] using h)
        | undef ty =>
            trivial

private def CoherentWitness (fuel : Nat) (env : Env) : Prop :=
  ∀ {name : Name} {slot : EnvSlot},
    env.slotAt name = some slot →
      PartialTyCoherentWitness fuel env slot.ty

private theorem tyCoherent_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {mutable : Bool} {targets : List LVal} :
    tyCoherent fuel env (.borrow mutable targets) = true →
      ∃ targetTy targetLifetime,
        LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro h
  cases fuel with
  | zero =>
      simp [tyCoherent] at h
  | succ fuel =>
      cases htargets : lvalTargetsType? fuel env targets with
      | none =>
          simp [tyCoherent, htargets] at h
      | some result =>
          rcases result with ⟨partialTy, targetLifetime⟩
          cases partialTy with
          | ty targetTy =>
              exact ⟨targetTy, targetLifetime, lvalTargetsType?_sound htargets⟩
          | box _ =>
              simp [tyCoherent, htargets] at h
          | undef _ =>
              simp [tyCoherent, htargets] at h

private theorem partialTyCoherent_contains_borrow_targets_sound
    {fuel : Nat} {env : FiniteEnv} {partialTy : PartialTy}
    {needle : Ty} :
    partialTyCoherent fuel env partialTy = true →
      PartialTyContains partialTy needle →
        ∀ {mutable : Bool} {targets : List LVal},
          needle = .borrow mutable targets →
            ∃ targetTy targetLifetime,
              LValTargetsTyping env.toEnv targets (.ty targetTy)
                targetLifetime := by
  intro hcoherent hcontains
  induction hcontains generalizing fuel with
  | here =>
      intro mutable targets hneedle
      cases hneedle
      exact tyCoherent_borrow_targets_sound
        (by simpa [partialTyCoherent] using hcoherent)
  | tyBox _hinner ih =>
      intro mutable targets hneedle
      cases fuel with
      | zero =>
          simp [partialTyCoherent, tyCoherent] at hcoherent
      | succ fuel =>
        exact ih (fuel := fuel)
          (by simpa [partialTyCoherent, tyCoherent] using hcoherent)
          hneedle
  | box _hinner ih =>
      intro mutable targets hneedle
      cases fuel with
      | zero =>
          simp [partialTyCoherent] at hcoherent
      | succ fuel =>
        exact ih (fuel := fuel)
          (by simpa [partialTyCoherent] using hcoherent)
          hneedle

private theorem targetsAllHaveTy?_sound {fuel : Nat} {env : FiniteEnv}
    {ty : Ty} {targets : List LVal} :
    targetsAllHaveTy? fuel env ty targets = true →
      ∀ target, target ∈ targets →
        ∃ lifetime, LValTyping env.toEnv target (.ty ty) lifetime := by
  induction targets with
  | nil =>
      intro _ target htarget
      cases htarget
  | cons head rest ih =>
      intro h target htarget
      cases hhead : lvalType? fuel env head with
      | none =>
          simp [targetsAllHaveTy?, hhead] at h
      | some result =>
          rcases result with ⟨headPartialTy, headLifetime⟩
          cases headPartialTy with
          | ty headTy =>
              by_cases hty : headTy = ty
              · subst headTy
                have hrest : targetsAllHaveTy? fuel env ty rest = true := by
                  simpa [targetsAllHaveTy?, hhead] using h
                cases htarget with
                | head =>
                    exact ⟨headLifetime, lvalType?_sound hhead⟩
                | tail _ htail =>
                    exact ih hrest target htail
              · simp [targetsAllHaveTy?, hhead, hty] at h
          | box _ =>
              simp [targetsAllHaveTy?, hhead] at h
          | undef _ =>
              simp [targetsAllHaveTy?, hhead] at h

private theorem targetListCommonTy?_none_sound {fuel : Nat} {env : FiniteEnv}
    {targets : List LVal} :
    targetListCommonTy? fuel env targets = some none → targets = [] := by
  cases targets with
  | nil =>
      intro _h
      rfl
  | cons head rest =>
      intro h
      cases hhead : lvalType? fuel env head with
      | none =>
          simp [targetListCommonTy?, hhead] at h
      | some result =>
          rcases result with ⟨headPartialTy, headLifetime⟩
          cases headPartialTy with
          | ty ty =>
              cases hall : targetsAllHaveTy? fuel env ty rest <;>
                simp [targetListCommonTy?, hhead, hall] at h
          | box _ =>
              simp [targetListCommonTy?, hhead] at h
          | undef _ =>
              simp [targetListCommonTy?, hhead] at h

private theorem targetListCommonTy?_some_sound {fuel : Nat} {env : FiniteEnv}
    {targets : List LVal} {ty : Ty} :
    targetListCommonTy? fuel env targets = some (some ty) →
      ∀ target, target ∈ targets →
        ∃ lifetime, LValTyping env.toEnv target (.ty ty) lifetime := by
  cases targets with
  | nil =>
      intro h
      simp [targetListCommonTy?] at h
  | cons head rest =>
      intro h target htarget
      cases hhead : lvalType? fuel env head with
      | none =>
          simp [targetListCommonTy?, hhead] at h
      | some result =>
          rcases result with ⟨headPartialTy, headLifetime⟩
          cases headPartialTy with
          | ty headTy =>
              cases hall : targetsAllHaveTy? fuel env headTy rest
              · simp [targetListCommonTy?, hhead, hall] at h
              · simp [targetListCommonTy?, hhead, hall] at h
                subst h
                cases htarget with
                | head =>
                    exact ⟨headLifetime, lvalType?_sound hhead⟩
                | tail _ htail =>
                    exact targetsAllHaveTy?_sound hall target htail
          | box _ =>
              simp [targetListCommonTy?, hhead] at h
          | undef _ =>
              simp [targetListCommonTy?, hhead] at h

private theorem shapeCompatible_sound (fuel : Nat) :
    (∀ {env : FiniteEnv} {left right : Ty},
      shapeCompatibleTy fuel env left right = true →
        ShapeCompatible env.toEnv (.ty left) (.ty right)) ∧
    (∀ {env : FiniteEnv} {left right : PartialTy},
      shapeCompatiblePartialTy fuel env left right = true →
        ShapeCompatible env.toEnv left right) := by
  induction fuel with
  | zero =>
      constructor
      · intro env left right h
        simp [shapeCompatibleTy] at h
      · intro env left right h
        simp [shapeCompatiblePartialTy] at h
  | succ fuel ih =>
      constructor
      · intro env left right h
        cases left with
        | unit =>
            cases right <;> simp [shapeCompatibleTy] at h
            exact ShapeCompatible.unit
        | int =>
            cases right <;> simp [shapeCompatibleTy] at h
            exact ShapeCompatible.int
        | bool =>
            cases right <;> simp [shapeCompatibleTy] at h
            exact ShapeCompatible.bool
        | box left =>
            cases right <;> simp [shapeCompatibleTy] at h
            next right =>
              exact ShapeCompatible.tyBox (ih.1 h)
        | borrow mutable₁ leftTargets =>
            cases right <;> simp [shapeCompatibleTy] at h
            next mutable₂ rightTargets =>
              by_cases hmutable : mutable₁ = mutable₂
              · subst mutable₂
                simp at h
                cases hleft :
                    targetListCommonTy? fuel env leftTargets with
                | none =>
                    simp [hleft] at h
                | some leftCommon =>
                    cases hright :
                        targetListCommonTy? fuel env rightTargets with
                    | none =>
                        simp [hleft, hright] at h
                    | some rightCommon =>
                        cases leftCommon with
                        | none =>
                            have hleftEmpty :
                                leftTargets = [] :=
                              targetListCommonTy?_none_sound hleft
                            cases rightCommon with
                            | none =>
                                have hrightEmpty :
                                    rightTargets = [] :=
                                  targetListCommonTy?_none_sound hright
                                subst leftTargets
                                subst rightTargets
                                refine ShapeCompatible.borrow ?_ ?_
                                  ShapeCompatible.unit
                                · intro target htarget
                                  cases htarget
                                · intro target htarget
                                  cases htarget
                            | some rightTy =>
                                simp [hleft, hright] at h
                                subst leftTargets
                                refine ShapeCompatible.borrow ?_ ?_ (ih.1 h)
                                · intro target htarget
                                  cases htarget
                                · exact targetListCommonTy?_some_sound hright
                        | some leftTy =>
                            cases rightCommon with
                            | none =>
                                simp [hleft, hright] at h
                                have hrightEmpty :
                                    rightTargets = [] :=
                                  targetListCommonTy?_none_sound hright
                                subst rightTargets
                                refine ShapeCompatible.borrow ?_ ?_ (ih.1 h)
                                · exact targetListCommonTy?_some_sound hleft
                                · intro target htarget
                                  cases htarget
                            | some rightTy =>
                                simp [hleft, hright] at h
                                refine ShapeCompatible.borrow ?_ ?_ (ih.1 h)
                                · exact targetListCommonTy?_some_sound hleft
                                · exact targetListCommonTy?_some_sound hright
              · simp [hmutable] at h
      · intro env left right h
        cases left with
        | ty leftTy =>
            cases right <;> simp [shapeCompatiblePartialTy] at h
            · exact ih.1 h
            · exact ShapeCompatible.undefRight (ih.2 h)
        | box leftInner =>
            cases right <;> simp [shapeCompatiblePartialTy] at h
            · exact ShapeCompatible.box (ih.2 h)
            · exact ShapeCompatible.undefRight (ih.2 h)
        | undef leftTy =>
            simp [shapeCompatiblePartialTy] at h
            exact ShapeCompatible.undefLeft (ih.2 h)

private theorem shapeCompatibleTy_sound {fuel : Nat} {env : FiniteEnv}
    {left right : Ty} :
    shapeCompatibleTy fuel env left right = true →
      ShapeCompatible env.toEnv (.ty left) (.ty right) :=
  (shapeCompatible_sound fuel).1

private theorem shapeCompatiblePartialTy_sound {fuel : Nat} {env : FiniteEnv}
    {left right : PartialTy} :
    shapeCompatiblePartialTy fuel env left right = true →
      ShapeCompatible env.toEnv left right :=
  (shapeCompatible_sound fuel).2

private theorem lifetimeOutlives_sound {outer inner : Lifetime} :
    lifetimeOutlives outer inner = true → LifetimeOutlives outer inner := by
  intro h
  simpa [lifetimeOutlives, LifetimeOutlives] using h

private theorem lvalBaseOutlives_sound {env : FiniteEnv} {lv : LVal}
    {lifetime : Lifetime} :
    lvalBaseOutlives env lv lifetime = true →
      LValBaseOutlives env.toEnv lv lifetime := by
  intro h
  unfold lvalBaseOutlives at h
  cases hlookup : env.lookup (LVal.base lv) with
  | none =>
      simp [hlookup] at h
  | some slot =>
      exact ⟨slot, hlookup, lifetimeOutlives_sound (by
        simpa [hlookup] using h)⟩

private theorem borrowTargetsWellFormed_sound {fuel : Nat} {env : FiniteEnv}
    {targets : List LVal} {lifetime : Lifetime} :
    borrowTargetsWellFormed fuel env targets lifetime = true →
      BorrowTargetsWellFormed env.toEnv targets lifetime := by
  intro h
  refine BorrowTargetsWellFormed.intro ?_
  intro target htarget
  unfold borrowTargetsWellFormed at h
  have htargetCheck := (List.all_eq_true.mp h) target htarget
  cases htype : lvalType? fuel env target with
  | none =>
      simp [htype] at htargetCheck
  | some result =>
      rcases result with ⟨partialTy, targetLifetime⟩
      cases partialTy with
      | ty targetTy =>
          simp [htype] at htargetCheck
          exact ⟨targetTy, targetLifetime, lvalType?_sound htype,
            lifetimeOutlives_sound htargetCheck.1,
            lvalBaseOutlives_sound htargetCheck.2⟩
      | box _ =>
          simp [htype] at htargetCheck
      | undef _ =>
          simp [htype] at htargetCheck

private theorem wellFormedTy_sound :
    ∀ {fuel : Nat} {env : FiniteEnv} {ty : Ty} {lifetime : Lifetime},
      wellFormedTy fuel env ty lifetime = true →
        WellFormedTy env.toEnv ty lifetime
  | _fuel, _env, .unit, _lifetime, _h => WellFormedTy.unit
  | _fuel, _env, .int, _lifetime, _h => WellFormedTy.int
  | _fuel, _env, .bool, _lifetime, _h => WellFormedTy.bool
  | _fuel, _env, .borrow _ _, _lifetime, h =>
      WellFormedTy.borrow (borrowTargetsWellFormed_sound h)
  | _fuel, _env, .box _, _lifetime, h =>
      WellFormedTy.box (wellFormedTy_sound h)

private theorem strike?_sound {path : Path} {source struck : PartialTy} :
    strike? path source = some struck → Strike path source struck := by
  intro h
  induction path generalizing source struck with
  | nil =>
      cases source <;> simp [strike?] at h
      next ty =>
        cases h
        rfl
  | cons _ rest ih =>
      cases source <;> simp [strike?] at h
      next inner =>
        cases hinner : strike? rest inner with
        | none =>
            simp [hinner] at h
        | some innerStruck =>
            simp [hinner] at h
            cases h
            exact ih hinner

private theorem envMove?_sound {env moved : FiniteEnv} {lv : LVal} :
    envMove? env lv = some moved → EnvMove env.toEnv lv moved.toEnv := by
  intro h
  unfold envMove? at h
  cases hslot : env.lookup (LVal.base lv) with
  | none =>
      simp [hslot] at h
  | some slot =>
      cases hstrike : strike? (LVal.path lv) slot.ty with
      | none =>
          simp [hslot, hstrike] at h
      | some struck =>
          simp [hslot, hstrike] at h
          cases h
          refine ⟨slot, struck, hslot, strike?_sound hstrike, ?_⟩
          simp [FiniteEnv.toEnv_update]

private theorem termDiverges_sound {term : Term} :
    termDiverges term = true → Term.Diverges term := by
  exact
    Term.rec
      (motive_1 := fun term => termDiverges term = true → Term.Diverges term)
      (motive_2 := fun terms =>
        termListDiverges terms = true →
          ∃ term, term ∈ terms ∧ Term.Diverges term)
      (by
        intro lifetime terms ih h
        simp [termDiverges] at h
        rcases ih h with ⟨term, hmem, hdiv⟩
        exact Term.Diverges.block hmem hdiv)
      (by intro _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ h; unfold termDiverges at h; simp at h)
      (by intro _ h; unfold termDiverges at h; simp at h)
      (by intro _ h; unfold termDiverges at h; simp at h)
      (by intro _; exact Term.Diverges.missing)
      (by intro _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro h; simp [termListDiverges] at h)
      (by
        intro head tail ihHead ihTail h
        simp [termListDiverges] at h
        rcases h with h | h
        · exact ⟨head, by simp, ihHead h⟩
        · rcases ihTail h with ⟨term, hmem, hdiv⟩
          exact ⟨term, List.mem_cons_of_mem _ hmem, hdiv⟩)
      term

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

private theorem coherent_witness_sound {fuel : Nat} {env : FiniteEnv} :
    coherent fuel env = true →
      CoherentWitness fuel env.toEnv := by
  intro hcoherent name slot hslot
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherent at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  exact (coherentWitness_sound fuel).2 hentryCheck

private theorem rootCoherent_witness_sound {fuel : Nat} {env : FiniteEnv}
    {root : Name} :
    rootCoherent fuel env root = true →
    ∀ {slot : EnvSlot},
      env.lookup root = some slot →
        PartialTyCoherentWitness fuel env.toEnv slot.ty := by
  intro hroot slot hslot
  have hslotCoherent : partialTyCoherent fuel env slot.ty = true := by
    simpa [rootCoherent, hslot] using hroot
  exact (coherentWitness_sound fuel).2 hslotCoherent

private theorem tyCoherentNonempty_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {mutable : Bool} {targets : List LVal} :
    tyCoherentNonempty fuel env (.borrow mutable targets) = true →
    targets ≠ [] →
      ∃ targetTy targetLifetime,
        LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro h hnonempty
  cases fuel with
  | zero =>
      simp [tyCoherentNonempty] at h
      exact False.elim (hnonempty h)
  | succ fuel =>
      by_cases htargets : targets = []
      · exact False.elim (hnonempty htargets)
      · cases htargetType : lvalTargetsType? fuel env targets with
        | none =>
            simp [tyCoherentNonempty, htargets, htargetType] at h
        | some result =>
            rcases result with ⟨partialTy, targetLifetime⟩
            cases partialTy with
            | ty targetTy =>
                exact ⟨targetTy, targetLifetime,
                  lvalTargetsType?_sound htargetType⟩
            | box _ =>
                simp [tyCoherentNonempty, htargets, htargetType] at h
            | undef _ =>
                simp [tyCoherentNonempty, htargets, htargetType] at h

private theorem partialTyCoherentNonempty_contains_borrow_targets_sound_aux
    {fuel : Nat} {env : FiniteEnv} {partialTy : PartialTy}
    {needle : Ty} :
    partialTyCoherentNonempty fuel env partialTy = true →
    PartialTyContains partialTy needle →
      ∀ {mutable : Bool} {targets : List LVal},
        needle = .borrow mutable targets →
        targets ≠ [] →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env.toEnv targets (.ty targetTy)
              targetLifetime := by
  intro hcoherent hcontains
  induction hcontains generalizing fuel with
  | here =>
      intro mutable targets hneedle hnonempty
      cases hneedle
      exact tyCoherentNonempty_borrow_targets_sound
        (by simpa [partialTyCoherentNonempty] using hcoherent)
        hnonempty
  | tyBox _hinner ih =>
      intro mutable targets hneedle hnonempty
      cases fuel with
      | zero =>
          simp [partialTyCoherentNonempty, tyCoherentNonempty] at hcoherent
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [partialTyCoherentNonempty, tyCoherentNonempty] using
              hcoherent)
            hneedle hnonempty
  | box _hinner ih =>
      intro mutable targets hneedle hnonempty
      cases fuel with
      | zero =>
          simp [partialTyCoherentNonempty] at hcoherent
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [partialTyCoherentNonempty] using hcoherent)
            hneedle hnonempty

private theorem partialTyCoherentNonempty_contains_borrow_targets_sound
    {fuel : Nat} {env : FiniteEnv} {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    partialTyCoherentNonempty fuel env partialTy = true →
    PartialTyContains partialTy (.borrow mutable targets) →
    targets ≠ [] →
      ∃ targetTy targetLifetime,
        LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro hcoherent hcontains hnonempty
  exact partialTyCoherentNonempty_contains_borrow_targets_sound_aux
    hcoherent hcontains rfl hnonempty

private theorem coherentNonempty_slot_contains_borrow_targets_sound
    {fuel : Nat} {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    coherentNonempty fuel env = true →
    env.lookup name = some slot →
    PartialTyContains slot.ty (.borrow mutable targets) →
    targets ≠ [] →
      ∃ targetTy targetLifetime,
        LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro hcoherent hslot hcontains hnonempty
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherentNonempty at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  exact partialTyCoherentNonempty_contains_borrow_targets_sound
    hentryCheck hcontains hnonempty

private theorem partialTyCoherentWitness_contains_borrow_targets_aux
    {fuel : Nat} {env : Env} {partialTy : PartialTy} {needle : Ty} :
    PartialTyCoherentWitness fuel env partialTy →
      PartialTyContains partialTy needle →
        ∀ {mutable : Bool} {targets : List LVal},
          needle = .borrow mutable targets →
            ∃ targetTy targetLifetime,
              LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hcontains
  induction hcontains generalizing fuel with
  | here =>
      intro mutable targets hneedle
      cases hneedle
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          rcases hwitness with ⟨targetTy, targetLifetime, htargets, _⟩
          exact ⟨targetTy, targetLifetime, htargets⟩
  | tyBox _hinner ih =>
      intro mutable targets hneedle
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [PartialTyCoherentWitness, TyCoherentWitness] using
              hwitness)
            hneedle
  | box _hinner ih =>
      intro mutable targets hneedle
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [PartialTyCoherentWitness] using hwitness)
            hneedle

private theorem partialTyCoherentWitness_contains_borrow_targets
    {fuel : Nat} {env : Env} {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyCoherentWitness fuel env partialTy →
      PartialTyContains partialTy (.borrow mutable targets) →
        ∃ targetTy targetLifetime,
          LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hcontains
  exact partialTyCoherentWitness_contains_borrow_targets_aux
    hwitness hcontains rfl

private theorem partialTyCoherentWitness_borrow_targets_nonempty
    {fuel : Nat} {env : Env} {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyCoherentWitness fuel env partialTy →
      PartialTyContains partialTy (.borrow mutable targets) →
        targets ≠ [] := by
  intro hwitness hcontains hnil
  rcases partialTyCoherentWitness_contains_borrow_targets
      hwitness hcontains with
    ⟨targetTy, targetLifetime, htargets⟩
  subst hnil
  exact LValTargetsTyping.nil_false htargets

private theorem tyCoherentWitness_of_eqv (fuel : Nat) {env : Env}
    (hlinear : Linearizable env) :
    (∀ {left right : Ty},
      Ty.eqv left right →
      TyCoherentWitness fuel env left →
        TyCoherentWitness fuel env right) ∧
    (∀ {left right : PartialTy},
      PartialTy.eqv left right →
      PartialTyCoherentWitness fuel env left →
        PartialTyCoherentWitness fuel env right) := by
  induction fuel with
  | zero =>
      have hty :
          ∀ {left right : Ty},
            Ty.eqv left right →
            TyCoherentWitness 0 env left →
              TyCoherentWitness 0 env right := by
        intro left right heqv hwitness
        cases left <;> cases right <;>
          simp [Ty.eqv, TyCoherentWitness] at heqv hwitness ⊢
      have hpartial :
          ∀ {left right : PartialTy},
            PartialTy.eqv left right →
            PartialTyCoherentWitness 0 env left →
              PartialTyCoherentWitness 0 env right := by
        intro left right heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                exact hty heqv hwitness
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right <;>
              simp [PartialTy.eqv, PartialTyCoherentWitness] at heqv hwitness ⊢
        | undef leftTy =>
            cases right <;>
              simp [PartialTy.eqv, PartialTyCoherentWitness] at heqv hwitness ⊢
      constructor
      · exact hty
      · exact hpartial
  | succ fuel ih =>
      have hty :
          ∀ {left right : Ty},
            Ty.eqv left right →
            TyCoherentWitness (fuel + 1) env left →
              TyCoherentWitness (fuel + 1) env right := by
        intro left right heqv hwitness
        cases left with
        | unit =>
            cases right <;>
              simp [Ty.eqv, TyCoherentWitness] at heqv hwitness ⊢
        | int =>
            cases right <;>
              simp [Ty.eqv, TyCoherentWitness] at heqv hwitness ⊢
        | bool =>
            cases right <;>
              simp [Ty.eqv, TyCoherentWitness] at heqv hwitness ⊢
        | box leftInner =>
            cases right with
            | box rightInner =>
                change TyCoherentWitness fuel env leftInner at hwitness
                change TyCoherentWitness fuel env rightInner
                exact ih.1 (by simpa [Ty.eqv] using heqv) hwitness
            | unit =>
                simp [Ty.eqv] at heqv
            | int =>
                simp [Ty.eqv] at heqv
            | borrow _ _ =>
                simp [Ty.eqv] at heqv
            | bool =>
                simp [Ty.eqv] at heqv
        | borrow leftMutable leftTargets =>
            cases right with
            | borrow rightMutable rightTargets =>
                simp [Ty.eqv] at heqv
                change ∃ targetTy targetLifetime,
                  LValTargetsTyping env leftTargets (.ty targetTy)
                    targetLifetime ∧
                    TyCoherentWitness fuel env targetTy at hwitness
                change ∃ targetTy targetLifetime,
                  LValTargetsTyping env rightTargets (.ty targetTy)
                    targetLifetime ∧
                    TyCoherentWitness fuel env targetTy
                rcases heqv with ⟨hmutable, hleftRight, hrightLeft⟩
                subst rightMutable
                rcases hwitness with
                  ⟨targetTy, targetLifetime, htargets, htargetWitness⟩
                have htargetsNonempty : rightTargets ≠ [] := by
                  intro hnil
                  subst hnil
                  cases leftTargets with
                  | nil =>
                      exact LValTargetsTyping.nil_false htargets
                  | cons head tail =>
                      have hmem : head ∈ ([] : List LVal) :=
                        hleftRight (by simp)
                      cases hmem
                rcases lvalTargetsTyping_of_nonempty_subset htargets
                    htargetsNonempty hrightLeft with
                  ⟨rightTargetTy, rightTargetLifetime, hrightTargets,
                    _hrightStrengthens, _hrightLifetime⟩
                rcases hlinear with ⟨φ, hφ⟩
                have heqvTargets :
                    PartialTy.eqv (.ty targetTy) (.ty rightTargetTy) :=
                  lvalTargetsTyping_eqv_of_subset_of_lval_eqv
                    (env := env)
                    (leftTargets := leftTargets) (rightTargets := rightTargets)
                    (leftTy := .ty targetTy)
                    (rightTy := .ty rightTargetTy)
                    (leftLifetime := targetLifetime)
                    (rightLifetime := rightTargetLifetime)
                    (fun hleft hright =>
                      lvalTyping_eqv_of_linearizedBy hφ hleft hright)
                    htargets hrightTargets hleftRight hrightLeft
                exact ⟨rightTargetTy, rightTargetLifetime, hrightTargets,
                  ih.1 heqvTargets htargetWitness⟩
            | unit =>
                simp [Ty.eqv] at heqv
            | int =>
                simp [Ty.eqv] at heqv
            | box _ =>
                simp [Ty.eqv] at heqv
            | bool =>
                simp [Ty.eqv] at heqv
      have hpartial :
          ∀ {left right : PartialTy},
            PartialTy.eqv left right →
            PartialTyCoherentWitness (fuel + 1) env left →
              PartialTyCoherentWitness (fuel + 1) env right := by
        intro left right heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                exact hty heqv hwitness
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right with
            | box rightInner =>
                exact ih.2 (by simpa [PartialTy.eqv] using heqv)
                  (by simpa [PartialTyCoherentWitness] using hwitness)
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | undef leftTy =>
            cases right with
            | undef rightTy =>
                trivial
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | box _ =>
                simp [PartialTy.eqv] at heqv
      constructor
      · exact hty
      · exact hpartial

private theorem partialTyCoherentWitness_of_eqv {fuel : Nat} {env : Env}
    (hlinear : Linearizable env) {left right : PartialTy} :
    PartialTy.eqv left right →
    PartialTyCoherentWitness fuel env left →
      PartialTyCoherentWitness fuel env right :=
  (tyCoherentWitness_of_eqv fuel hlinear).2

private theorem tyCoherentNonemptyWitness_of_eqv (fuel : Nat) {env : Env}
    (hlinear : Linearizable env) :
    (∀ {left right : Ty},
      Ty.eqv left right →
      TyCoherentNonemptyWitness fuel env left →
        TyCoherentNonemptyWitness fuel env right) ∧
    (∀ {left right : PartialTy},
      PartialTy.eqv left right →
      PartialTyCoherentNonemptyWitness fuel env left →
        PartialTyCoherentNonemptyWitness fuel env right) := by
  induction fuel with
  | zero =>
      have hty :
          ∀ {left right : Ty},
            Ty.eqv left right →
            TyCoherentNonemptyWitness 0 env left →
              TyCoherentNonemptyWitness 0 env right := by
        intro left right heqv hwitness
        cases left with
        | unit =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | int =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | bool =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | box _ =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | borrow leftMutable leftTargets =>
            cases right with
            | borrow rightMutable rightTargets =>
                simp [Ty.eqv] at heqv
                rcases heqv with ⟨hmutable, _hleftRight, hrightLeft⟩
                subst rightMutable
                cases rightTargets with
                | nil => rfl
                | cons head tail =>
                    have hmem : head ∈ leftTargets :=
                      hrightLeft (by simp)
                    rw [hwitness] at hmem
                    cases hmem
            | unit | int | box _ | bool =>
                simp [Ty.eqv] at heqv
      have hpartial :
          ∀ {left right : PartialTy},
            PartialTy.eqv left right →
            PartialTyCoherentNonemptyWitness 0 env left →
              PartialTyCoherentNonemptyWitness 0 env right := by
        intro left right heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                exact hty heqv hwitness
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right <;>
              simp [PartialTy.eqv, PartialTyCoherentNonemptyWitness] at heqv hwitness ⊢
        | undef leftTy =>
            cases right <;>
              simp [PartialTy.eqv, PartialTyCoherentNonemptyWitness] at heqv hwitness ⊢
      constructor
      · exact hty
      · exact hpartial
  | succ fuel ih =>
      have hty :
          ∀ {left right : Ty},
            Ty.eqv left right →
            TyCoherentNonemptyWitness (fuel + 1) env left →
              TyCoherentNonemptyWitness (fuel + 1) env right := by
        intro left right heqv hwitness
        cases left with
        | unit =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | int =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | bool =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | box leftInner =>
            cases right with
            | box rightInner =>
                change TyCoherentNonemptyWitness fuel env leftInner at hwitness
                change TyCoherentNonemptyWitness fuel env rightInner
                exact ih.1 (by simpa [Ty.eqv] using heqv) hwitness
            | unit | int | borrow _ _ | bool =>
                simp [Ty.eqv] at heqv
        | borrow leftMutable leftTargets =>
            cases right with
            | borrow rightMutable rightTargets =>
                simp [Ty.eqv] at heqv
                rcases heqv with ⟨hmutable, hleftRight, hrightLeft⟩
                subst rightMutable
                cases hwitness with
                | inl hleftEmpty =>
                    left
                    cases rightTargets with
                    | nil => rfl
                    | cons head tail =>
                        have hmem : head ∈ leftTargets :=
                          hrightLeft (by simp)
                        rw [hleftEmpty] at hmem
                        cases hmem
                | inr hwitnessNonempty =>
                    rcases hwitnessNonempty with
                      ⟨targetTy, targetLifetime, htargets, htargetWitness⟩
                    by_cases hrightEmpty : rightTargets = []
                    · exact Or.inl hrightEmpty
                    · rcases lvalTargetsTyping_of_nonempty_subset htargets
                        hrightEmpty hrightLeft with
                      ⟨rightTargetTy, rightTargetLifetime, hrightTargets,
                        _hrightStrengthens, _hrightLifetime⟩
                      rcases hlinear with ⟨φ, hφ⟩
                      have heqvTargets :
                          PartialTy.eqv (.ty targetTy) (.ty rightTargetTy) :=
                        lvalTargetsTyping_eqv_of_subset_of_lval_eqv
                          (env := env)
                          (leftTargets := leftTargets)
                          (rightTargets := rightTargets)
                          (leftTy := .ty targetTy)
                          (rightTy := .ty rightTargetTy)
                          (leftLifetime := targetLifetime)
                          (rightLifetime := rightTargetLifetime)
                          (fun hleft hright =>
                            lvalTyping_eqv_of_linearizedBy hφ hleft hright)
                          htargets hrightTargets hleftRight hrightLeft
                      exact Or.inr ⟨rightTargetTy, rightTargetLifetime,
                        hrightTargets, ih.1 heqvTargets htargetWitness⟩
            | unit | int | box _ | bool =>
                simp [Ty.eqv] at heqv
      have hpartial :
          ∀ {left right : PartialTy},
            PartialTy.eqv left right →
            PartialTyCoherentNonemptyWitness (fuel + 1) env left →
              PartialTyCoherentNonemptyWitness (fuel + 1) env right := by
        intro left right heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                exact hty heqv hwitness
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right with
            | box rightInner =>
                exact ih.2 (by simpa [PartialTy.eqv] using heqv)
                  (by simpa [PartialTyCoherentNonemptyWitness] using hwitness)
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | undef leftTy =>
            cases right with
            | undef rightTy =>
                trivial
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | box _ =>
                simp [PartialTy.eqv] at heqv
      constructor
      · exact hty
      · exact hpartial

private theorem partialTyCoherentNonemptyWitness_of_eqv {fuel : Nat}
    {env : Env} (hlinear : Linearizable env) {left right : PartialTy} :
    PartialTy.eqv left right →
    PartialTyCoherentNonemptyWitness fuel env left →
      PartialTyCoherentNonemptyWitness fuel env right :=
  (tyCoherentNonemptyWitness_of_eqv fuel hlinear).2

private theorem partialTyCoherentNonemptyWitness_contains_borrow_targets_aux
    {fuel : Nat} {env : Env} {partialTy : PartialTy} {needle : Ty} :
    PartialTyCoherentNonemptyWitness fuel env partialTy →
      PartialTyContains partialTy needle →
        ∀ {mutable : Bool} {targets : List LVal},
          needle = .borrow mutable targets →
          targets ≠ [] →
            ∃ targetTy targetLifetime,
              LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hcontains
  induction hcontains generalizing fuel with
  | here =>
      intro mutable targets hneedle hnonempty
      cases hneedle
      cases fuel with
      | zero =>
          exact False.elim (hnonempty hwitness)
      | succ fuel =>
          cases hwitness with
          | inl hempty =>
              exact False.elim (hnonempty hempty)
          | inr hwitnessNonempty =>
              rcases hwitnessNonempty with
                ⟨targetTy, targetLifetime, htargets, _htargetWitness⟩
              exact ⟨targetTy, targetLifetime, htargets⟩
  | tyBox _hinner ih =>
      intro mutable targets hneedle hnonempty
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [PartialTyCoherentNonemptyWitness,
              TyCoherentNonemptyWitness] using hwitness)
            hneedle hnonempty
  | box _hinner ih =>
      intro mutable targets hneedle hnonempty
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [PartialTyCoherentNonemptyWitness] using hwitness)
            hneedle hnonempty

private theorem partialTyCoherentNonemptyWitness_contains_borrow_targets
    {fuel : Nat} {env : Env} {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyCoherentNonemptyWitness fuel env partialTy →
      PartialTyContains partialTy (.borrow mutable targets) →
      targets ≠ [] →
        ∃ targetTy targetLifetime,
          LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hcontains hnonempty
  exact partialTyCoherentNonemptyWitness_contains_borrow_targets_aux
    hwitness hcontains rfl hnonempty

private theorem coherentWitness_lvalTyping_witness {fuel : Nat}
    {env : Env}
    (hwitness : CoherentWitness fuel env)
    (hlinear : Linearizable env) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
        ∃ witnessFuel,
          witnessFuel ≤ fuel ∧
            PartialTyCoherentWitness witnessFuel env partialTy := by
  intro lv partialTy lifetime htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _lifetime _ =>
      ∃ witnessFuel,
        witnessFuel ≤ fuel ∧
          PartialTyCoherentWitness witnessFuel env partialTy)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping
  · intro _x _slot hslot
    exact ⟨fuel, Nat.le_refl fuel, hwitness hslot⟩
  · intro _lv inner _lifetime _htyping ih
    rcases ih with ⟨witnessFuel, hwitnessFuelLe, hinnerBox⟩
    cases witnessFuel with
    | zero =>
        exact False.elim hinnerBox
    | succ witnessFuel =>
        exact ⟨witnessFuel, Nat.le_trans (Nat.le_succ _)
          hwitnessFuelLe, by
          simpa [PartialTyCoherentWitness] using hinnerBox⟩
  · intro _lv mutable targets _borrowLifetime _targetLifetime targetTy
      _hborrow htargets ihBorrow _ihTargets
    rcases ihBorrow with
      ⟨borrowWitnessFuel, hborrowWitnessFuelLe, hborrowWitness⟩
    cases borrowWitnessFuel with
    | zero =>
        exact False.elim hborrowWitness
    | succ borrowWitnessFuel =>
        rcases hborrowWitness with
          ⟨witnessTargetTy, witnessTargetLifetime, hwitnessTargets,
            hwitnessTargetTy⟩
        rcases LValTargetsTyping.output_full htargets with
          ⟨actualTargetTy, htargetTyEq⟩
        subst htargetTyEq
        have hlinearForRanks := hlinear
        rcases hlinearForRanks with ⟨φ, hφ⟩
        have heqvTargets :
            PartialTy.eqv (.ty witnessTargetTy) (.ty actualTargetTy) :=
          lvalTargetsTyping_eqv_of_subset_of_lval_eqv
            (env := env)
            (leftTargets := targets) (rightTargets := targets)
            (leftTy := .ty witnessTargetTy) (rightTy := .ty actualTargetTy)
            (leftLifetime := witnessTargetLifetime)
            (rightLifetime := _targetLifetime)
            (fun hleft hright =>
              lvalTyping_eqv_of_linearizedBy hφ hleft hright)
            hwitnessTargets htargets
            (by intro target htarget; exact htarget)
            (by intro target htarget; exact htarget)
        exact ⟨borrowWitnessFuel,
          Nat.le_trans (Nat.le_succ _) hborrowWitnessFuelLe,
          partialTyCoherentWitness_of_eqv hlinear heqvTargets
            (by
              simpa [PartialTyCoherentWitness] using hwitnessTargetTy)⟩
  · intro _target _ty _targetLifetime _htyping _ihTyping
    trivial
  · intro _target _rest _headTy _headLifetime _restLifetime _lifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

private def CoherentNonemptyWitness (fuel : Nat) (env : Env) : Prop :=
  ∀ {name : Name} {slot : EnvSlot},
    env.slotAt name = some slot →
      PartialTyCoherentNonemptyWitness fuel env slot.ty

private theorem coherentNonempty_witness_sound {fuel : Nat} {env : FiniteEnv} :
    coherentNonempty fuel env = true →
      CoherentNonemptyWitness fuel env.toEnv := by
  intro hcoherent name slot hslot
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherentNonempty at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  exact (coherentNonemptyWitness_sound fuel).2 hentryCheck

private theorem coherentNonemptyWitness_lvalTyping_witness {fuel : Nat}
    {env : Env}
    (hwitness : CoherentNonemptyWitness fuel env)
    (hlinear : Linearizable env) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
        ∃ witnessFuel,
          witnessFuel ≤ fuel ∧
            PartialTyCoherentNonemptyWitness witnessFuel env partialTy := by
  intro lv partialTy lifetime htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _lifetime _ =>
      ∃ witnessFuel,
        witnessFuel ≤ fuel ∧
          PartialTyCoherentNonemptyWitness witnessFuel env partialTy)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping
  · intro _x _slot hslot
    exact ⟨fuel, Nat.le_refl fuel, hwitness hslot⟩
  · intro _lv inner _lifetime _htyping ih
    rcases ih with ⟨witnessFuel, hwitnessFuelLe, hinnerBox⟩
    cases witnessFuel with
    | zero =>
        exact False.elim hinnerBox
    | succ witnessFuel =>
        exact ⟨witnessFuel, Nat.le_trans (Nat.le_succ _)
          hwitnessFuelLe, by
          simpa [PartialTyCoherentNonemptyWitness] using hinnerBox⟩
  · intro _lv mutable targets _borrowLifetime targetLifetime targetTy
      _hborrow htargets ihBorrow _ihTargets
    rcases ihBorrow with
      ⟨borrowWitnessFuel, hborrowWitnessFuelLe, hborrowWitness⟩
    cases borrowWitnessFuel with
    | zero =>
        have htargetsEmpty : targets = [] := hborrowWitness
        subst htargetsEmpty
        exact False.elim (LValTargetsTyping.nil_false htargets)
    | succ borrowWitnessFuel =>
        cases hborrowWitness with
        | inl htargetsEmpty =>
            subst htargetsEmpty
            exact False.elim (LValTargetsTyping.nil_false htargets)
        | inr hborrowWitnessNonempty =>
            rcases hborrowWitnessNonempty with
              ⟨witnessTargetTy, witnessTargetLifetime, hwitnessTargets,
                hwitnessTargetTy⟩
            rcases LValTargetsTyping.output_full htargets with
              ⟨actualTargetTy, htargetTyEq⟩
            subst htargetTyEq
            have hlinearForRanks := hlinear
            rcases hlinearForRanks with ⟨φ, hφ⟩
            have heqvTargets :
                PartialTy.eqv (.ty witnessTargetTy) (.ty actualTargetTy) :=
              lvalTargetsTyping_eqv_of_subset_of_lval_eqv
                (env := env)
                (leftTargets := targets) (rightTargets := targets)
                (leftTy := .ty witnessTargetTy) (rightTy := .ty actualTargetTy)
                (leftLifetime := witnessTargetLifetime)
                (rightLifetime := targetLifetime)
                (fun hleft hright =>
                  lvalTyping_eqv_of_linearizedBy hφ hleft hright)
                hwitnessTargets htargets
                (by intro target htarget; exact htarget)
                (by intro target htarget; exact htarget)
            exact ⟨borrowWitnessFuel,
              Nat.le_trans (Nat.le_succ _) hborrowWitnessFuelLe,
              partialTyCoherentNonemptyWitness_of_eqv hlinear heqvTargets
                (by
                  simpa [PartialTyCoherentNonemptyWitness] using
                    hwitnessTargetTy)⟩
  · intro _target _ty _targetLifetime _htyping _ihTyping
    trivial
  · intro _target _rest _headTy _headLifetime _restLifetime _lifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

private theorem coherentNonempty_lvalTyping_sound {fuel : Nat}
    {env : FiniteEnv} :
    coherentNonempty fuel env = true →
    Linearizable env.toEnv →
    ∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LValTyping env.toEnv lv (.ty (.borrow mutable targets)) borrowLifetime →
      targets ≠ [] →
        ∃ targetTy targetLifetime,
          LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro hcoherent hlinear lv mutable targets borrowLifetime htyping hnonempty
  rcases coherentNonemptyWitness_lvalTyping_witness
      (coherentNonempty_witness_sound hcoherent) hlinear htyping with
    ⟨witnessFuel, _hle, hpartialWitness⟩
  exact partialTyCoherentNonemptyWitness_contains_borrow_targets
    hpartialWitness PartialTyContains.here hnonempty

private theorem rootCoherent_lvalTyping_witness {fuel : Nat}
    {env : Env} {root : Name}
    (hrootWitness :
      ∀ {slot : EnvSlot},
        env.slotAt root = some slot →
          PartialTyCoherentWitness fuel env slot.ty)
    (hlinear : Linearizable env) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LVal.base lv = root →
      LValTyping env lv partialTy lifetime →
        ∃ witnessFuel,
          witnessFuel ≤ fuel ∧
            PartialTyCoherentWitness witnessFuel env partialTy := by
  intro lv partialTy lifetime hbase htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _lifetime _ =>
      LVal.base lv = root →
        ∃ witnessFuel,
          witnessFuel ≤ fuel ∧
            PartialTyCoherentWitness witnessFuel env partialTy)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping hbase
  · intro x slot hslot hbase
    have hx : x = root := by
      simpa [LVal.base] using hbase
    subst hx
    exact ⟨fuel, Nat.le_refl fuel, hrootWitness hslot⟩
  · intro lv inner _lifetime _htyping ih hbase
    have hsourceBase : LVal.base lv = root := by
      simpa [LVal.base] using hbase
    rcases ih hsourceBase with ⟨witnessFuel, hwitnessFuelLe, hinnerBox⟩
    cases witnessFuel with
    | zero =>
        exact False.elim hinnerBox
    | succ witnessFuel =>
        exact ⟨witnessFuel, Nat.le_trans (Nat.le_succ _)
          hwitnessFuelLe, by
          simpa [PartialTyCoherentWitness] using hinnerBox⟩
  · intro lv mutable targets _borrowLifetime targetLifetime targetTy
      _hborrow htargets ihBorrow _ihTargets hbase
    have hsourceBase : LVal.base lv = root := by
      simpa [LVal.base] using hbase
    rcases ihBorrow hsourceBase with
      ⟨borrowWitnessFuel, hborrowWitnessFuelLe, hborrowWitness⟩
    cases borrowWitnessFuel with
    | zero =>
        exact False.elim hborrowWitness
    | succ borrowWitnessFuel =>
        rcases hborrowWitness with
          ⟨witnessTargetTy, witnessTargetLifetime, hwitnessTargets,
            hwitnessTargetTy⟩
        rcases LValTargetsTyping.output_full htargets with
          ⟨actualTargetTy, htargetTyEq⟩
        subst htargetTyEq
        have hlinearForRanks := hlinear
        rcases hlinearForRanks with ⟨φ, hφ⟩
        have heqvTargets :
            PartialTy.eqv (.ty witnessTargetTy) (.ty actualTargetTy) :=
          lvalTargetsTyping_eqv_of_subset_of_lval_eqv
            (env := env)
            (leftTargets := targets) (rightTargets := targets)
            (leftTy := .ty witnessTargetTy) (rightTy := .ty actualTargetTy)
            (leftLifetime := witnessTargetLifetime)
            (rightLifetime := targetLifetime)
            (fun hleft hright =>
              lvalTyping_eqv_of_linearizedBy hφ hleft hright)
            hwitnessTargets htargets
            (by intro target htarget; exact htarget)
            (by intro target htarget; exact htarget)
        exact ⟨borrowWitnessFuel,
          Nat.le_trans (Nat.le_succ _) hborrowWitnessFuelLe,
          partialTyCoherentWitness_of_eqv hlinear heqvTargets
            (by
              simpa [PartialTyCoherentWitness] using hwitnessTargetTy)⟩
  · intro _target _ty _targetLifetime _htyping _ihTyping
    trivial
  · intro _target _rest _headTy _headLifetime _restLifetime _lifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

private theorem rootCoherent_written_root_sound {fuel : Nat}
    {env : FiniteEnv} {root : Name} :
    rootCoherent fuel env root = true →
    Linearizable env.toEnv →
    ∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LVal.base lv = root →
      LValTyping env.toEnv lv (.ty (.borrow mutable targets)) borrowLifetime →
        ∃ targetTy targetLifetime,
          LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro hroot hlinear lv mutable targets borrowLifetime hbase htyping
  rcases rootCoherent_lvalTyping_witness
      (env := env.toEnv) (root := root)
      (by
        intro slot hslot
        exact rootCoherent_witness_sound hroot hslot)
      hlinear hbase htyping with
    ⟨witnessFuel, _hle, hpartialWitness⟩
  exact partialTyCoherentWitness_contains_borrow_targets
    hpartialWitness PartialTyContains.here

private theorem coherentWitness_sound_coherent {fuel : Nat} {env : Env} :
    CoherentWitness fuel env →
    Linearizable env →
      Coherent env := by
  intro hwitness hlinear lv mutable targets borrowLifetime htyping
  rcases coherentWitness_lvalTyping_witness hwitness hlinear htyping with
    ⟨witnessFuel, _hle, hpartialWitness⟩
  exact partialTyCoherentWitness_contains_borrow_targets
    hpartialWitness PartialTyContains.here

private theorem coherentWitness_slot_contains_borrow_targets
    {fuel : Nat} {env : Env} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    CoherentWitness fuel env →
      env.slotAt name = some slot →
        PartialTyContains slot.ty (.borrow mutable targets) →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hslot hcontains
  exact partialTyCoherentWitness_contains_borrow_targets
    (hwitness hslot) hcontains

private theorem support_foldl_preserves {entries : List (Name × EnvSlot)}
    {acc : List Name} {name : Name} :
    name ∈ acc →
      name ∈ entries.foldl
        (fun names entry =>
          if names.contains entry.1 then names else names ++ [entry.1])
        acc := by
  induction entries generalizing acc with
  | nil =>
      intro h
      exact h
  | cons entry rest ih =>
      intro h
      apply ih
      by_cases hcontains : acc.contains entry.1
      · have hentryMem : entry.1 ∈ acc := by
          simpa using hcontains
        simpa [hentryMem] using h
      · have hentryNotMem : entry.1 ∉ acc := by
          simpa using hcontains
        simpa [hentryNotMem] using List.mem_append_left [entry.1] h

private theorem support_foldl_contains_entry
    {entries : List (Name × EnvSlot)} {acc : List Name}
    {entry : Name × EnvSlot} :
    entry ∈ entries →
      entry.1 ∈ entries.foldl
        (fun names entry =>
          if names.contains entry.1 then names else names ++ [entry.1])
        acc := by
  induction entries generalizing acc with
  | nil =>
      intro h
      cases h
  | cons first rest ih =>
      intro h
      cases h with
      | head =>
        apply support_foldl_preserves (entries := rest)
          (acc := if acc.contains entry.1 then acc else acc ++ [entry.1])
        by_cases hmem : entry.1 ∈ acc
        · simp [hmem]
        · simp [hmem]
      | tail _ hrest =>
        exact ih (acc :=
          if acc.contains first.1 then acc else acc ++ [first.1]) hrest

private theorem lookup_mem_support {env : FiniteEnv} {name : Name}
    {slot : EnvSlot} :
    env.lookup name = some slot → name ∈ env.support := by
  intro hlookup
  cases env with
  | mk entries =>
      change FiniteEnv.lookupEntries entries name = some slot at hlookup
      change name ∈
        entries.foldl
          (fun names entry =>
            if names.contains entry.1 then names else names ++ [entry.1])
          []
      exact support_foldl_contains_entry (lookupEntries_mem hlookup)

private theorem lookup_update_eq (env : FiniteEnv) (name : Name)
    (slot : EnvSlot) :
    (env.update name slot).lookup name = some slot := by
  have h := congrArg (fun env => env.slotAt name)
    (FiniteEnv.toEnv_update env name slot)
  simpa [FiniteEnv.toEnv, Env.update] using h

private theorem lookup_update_ne (env : FiniteEnv) {updated name : Name}
    (slot : EnvSlot) (hne : name ≠ updated) :
    (env.update updated slot).lookup name = env.lookup name := by
  have h := congrArg (fun env => env.slotAt name)
    (FiniteEnv.toEnv_update env updated slot)
  simpa [FiniteEnv.toEnv, Env.update, hne] using h

private theorem support_foldl_mem_iff
    {entries : List (Name × EnvSlot)} {acc : List Name} {name : Name} :
    name ∈ entries.foldl
        (fun names entry =>
          if names.contains entry.1 then names else names ++ [entry.1])
        acc ↔
      name ∈ acc ∨ ∃ slot, (name, slot) ∈ entries := by
  induction entries generalizing acc with
  | nil =>
      simp
  | cons entry rest ih =>
      rcases entry with ⟨entryName, entrySlot⟩
      have hstep :
          name ∈
              (if acc.contains entryName then acc else acc ++ [entryName]) ↔
            name ∈ acc ∨ name = entryName := by
        by_cases hentryMem : entryName ∈ acc
        · have hif :
            (if acc.contains entryName then acc else acc ++ [entryName]) =
              acc := by
              simp [hentryMem]
          rw [hif]
          constructor
          · intro hmem
            exact Or.inl hmem
          · intro hmem
            rcases hmem with hmem | hmem
            · exact hmem
            · subst hmem
              exact hentryMem
        · have hif :
            (if acc.contains entryName then acc else acc ++ [entryName]) =
              acc ++ [entryName] := by
              simp [hentryMem]
          rw [hif]
          constructor
          · intro hmem
            rcases List.mem_append.mp hmem with hmemAcc | hmemSingle
            · exact Or.inl hmemAcc
            · simp at hmemSingle
              exact Or.inr hmemSingle
          · intro hmem
            rcases hmem with hmem | hmem
            · exact List.mem_append_left [entryName] hmem
            · subst hmem
              exact List.mem_append_right acc (by simp)
      change name ∈
          rest.foldl
            (fun names entry =>
              if names.contains entry.1 then names else names ++ [entry.1])
            (if acc.contains entryName then acc else acc ++ [entryName]) ↔
        name ∈ acc ∨ ∃ slot, (name, slot) ∈ (entryName, entrySlot) :: rest
      rw [ih]
      constructor
      · intro hmem
        rcases hmem with hmem | hmem
        · rcases hstep.mp hmem with hmemAcc | hname
          · exact Or.inl hmemAcc
          · subst hname
            exact Or.inr ⟨entrySlot, List.mem_cons_self⟩
        · rcases hmem with ⟨slot, hslot⟩
          exact Or.inr ⟨slot, List.mem_cons_of_mem _ hslot⟩
      · intro hmem
        rcases hmem with hmemAcc | hentry
        · exact Or.inl (hstep.mpr (Or.inl hmemAcc))
        · rcases hentry with ⟨slot, hslot⟩
          cases hslot with
          | head =>
              exact Or.inl (hstep.mpr (Or.inr rfl))
          | tail _ htail =>
              exact Or.inr ⟨slot, htail⟩

private theorem lookupEntries_isSome_of_entry_name
    {entries : List (Name × EnvSlot)} {name : Name} {slot : EnvSlot} :
    (name, slot) ∈ entries →
      ∃ found, FiniteEnv.lookupEntries entries name = some found := by
  intro hmem
  induction entries with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      rcases entry with ⟨entryName, entrySlot⟩
      cases hmem with
      | head =>
          simp [FiniteEnv.lookupEntries]
      | tail _ htail =>
          by_cases hname : name = entryName
          · subst hname
            exact ⟨entrySlot, by simp [FiniteEnv.lookupEntries]⟩
          · rcases ih htail with ⟨found, hfound⟩
            exact ⟨found, by simpa [FiniteEnv.lookupEntries, hname] using hfound⟩

private theorem mem_support_iff_lookup_isSome {env : FiniteEnv}
    {name : Name} :
    name ∈ env.support ↔ ∃ slot, env.lookup name = some slot := by
  constructor
  · intro hmem
    cases env with
    | mk entries =>
        change name ∈
          entries.foldl
            (fun names entry =>
              if names.contains entry.1 then names else names ++ [entry.1])
            [] at hmem
        rcases (support_foldl_mem_iff.mp hmem) with hnil | hentry
        · cases hnil
        · rcases hentry with ⟨slot, hentry⟩
          exact lookupEntries_isSome_of_entry_name hentry
  · intro hlookup
    rcases hlookup with ⟨slot, hslot⟩
    exact lookup_mem_support hslot

private theorem lookup_none_of_not_mem_support {env : FiniteEnv}
    {name : Name} :
    name ∉ env.support → env.lookup name = none := by
  intro hnot
  cases hlookup : env.lookup name with
  | none => rfl
  | some slot =>
      exact False.elim (hnot (lookup_mem_support hlookup))

private theorem mem_insertName {names : List Name} {candidate name : Name} :
    candidate ∈ insertName names name ↔ candidate ∈ names ∨ candidate = name := by
  unfold insertName
  by_cases hnameMem : name ∈ names
  · have hif : (if names.contains name then names else names ++ [name]) =
        names := by
      simp [hnameMem]
    rw [hif]
    constructor
    · intro hmem
      exact Or.inl hmem
    · intro hmem
      rcases hmem with hmem | hmem
      · exact hmem
      · subst hmem
        exact hnameMem
  · constructor
    · intro hmem
      have hif : (if names.contains name then names else names ++ [name]) =
          names ++ [name] := by
        simp [hnameMem]
      rw [hif] at hmem
      rcases List.mem_append.mp hmem with hmemNames | hmemSingle
      · exact Or.inl hmemNames
      · simp at hmemSingle
        exact Or.inr hmemSingle
    · intro hmem
      have hif : (if names.contains name then names else names ++ [name]) =
          names ++ [name] := by
        simp [hnameMem]
      rw [hif]
      rcases hmem with hmem | hmem
      · exact List.mem_append_left [name] hmem
      · subst hmem
        exact List.mem_append_right names (by simp)

private theorem mem_unionNames {left right : List Name} {candidate : Name} :
    candidate ∈ unionNames left right ↔
      candidate ∈ left ∨ candidate ∈ right := by
  unfold unionNames
  induction right generalizing left with
  | nil =>
      simp
  | cons name rest ih =>
      rw [List.foldl_cons, ih]
      rw [mem_insertName]
      by_cases hleft : candidate ∈ left <;>
        by_cases hname : candidate = name <;>
          by_cases hrest : candidate ∈ rest <;>
            simp [List.mem_cons, hleft, hname, hrest]

private theorem sameBindings_lookup_eq {left right : FiniteEnv} :
    left.sameBindings right = true →
      ∀ name, left.lookup name = right.lookup name := by
  intro h name
  unfold FiniteEnv.sameBindings at h
  let names := unionNames left.support right.support
  by_cases hmem : name ∈ names
  · have hcheck := (List.all_eq_true.mp h) name hmem
    by_cases heq : left.lookup name = right.lookup name
    · exact heq
    · simp [heq] at hcheck
  · have hnotLeft : name ∉ left.support := by
      intro hleft
      exact hmem ((mem_unionNames).mpr (Or.inl hleft))
    have hnotRight : name ∉ right.support := by
      intro hright
      exact hmem ((mem_unionNames).mpr (Or.inr hright))
    rw [lookup_none_of_not_mem_support hnotLeft,
      lookup_none_of_not_mem_support hnotRight]

private theorem envEqOutside_lookup_eq {left right : FiniteEnv}
    {exceptName : Name} :
    envEqOutside left right exceptName = true →
      ∀ name, name ≠ exceptName → left.lookup name = right.lookup name := by
  intro h name hne
  unfold envEqOutside at h
  let names := unionNames left.support right.support
  by_cases hmem : name ∈ names
  · have hcheck := (List.all_eq_true.mp h) name hmem
    have hnotExcept : ¬ name = exceptName := hne
    simp [hnotExcept] at hcheck
    by_cases heq : left.lookup name = right.lookup name
    · exact heq
    · simp [heq] at hcheck
  · have hnotLeft : name ∉ left.support := by
      intro hleft
      exact hmem ((mem_unionNames).mpr (Or.inl hleft))
    have hnotRight : name ∉ right.support := by
      intro hright
      exact hmem ((mem_unionNames).mpr (Or.inr hright))
    rw [lookup_none_of_not_mem_support hnotLeft,
      lookup_none_of_not_mem_support hnotRight]

private theorem sameBindings_toEnv_eq {left right : FiniteEnv} :
    left.sameBindings right = true → left.toEnv = right.toEnv := by
  intro h
  change ({ slotAt := left.lookup } : Env) = { slotAt := right.lookup }
  have hslot : left.lookup = right.lookup := by
    funext name
    exact sameBindings_lookup_eq h name
  rw [hslot]

private theorem checkResult_matches_sound {result : CheckResult}
    {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    result.matches expectedTy expectedEnv = true →
      result.ty = expectedTy ∧ result.env.toEnv = expectedEnv.toEnv := by
  intro h
  unfold CheckResult.matches at h
  by_cases hty : result.ty = expectedTy
  · simp [hty] at h
    exact ⟨hty, sameBindings_toEnv_eq h⟩
  · simp [hty] at h

private def EnvJoinSlotSpec
    (left right join : Option EnvSlot) : Prop :=
  match left, right, join with
  | none, none, none => True
  | some leftSlot, some rightSlot, some joinSlot =>
      leftSlot.lifetime = rightSlot.lifetime ∧
        joinSlot.lifetime = leftSlot.lifetime ∧
          PartialTyJoin leftSlot.ty rightSlot.ty joinSlot.ty
  | _, _, _ => False

private theorem envJoinStep?_lookup_eq_of_ne {left right result result' : FiniteEnv}
    {stepName name : Name} :
    envJoinStep? left right result stepName = some result' →
      name ≠ stepName →
        result'.lookup name = result.lookup name := by
  intro hstep hne
  unfold envJoinStep? at hstep
  cases hleft : left.lookup stepName <;>
    cases hright : right.lookup stepName <;> simp [hleft, hright] at hstep
  · cases hstep
    rfl
  · rename_i leftSlot rightSlot
    by_cases hlife : leftSlot.lifetime = rightSlot.lifetime
    · cases hjoin : partialTyJoin? leftSlot.ty rightSlot.ty with
      | none =>
          simp [hlife, hjoin] at hstep
      | some joinedTy =>
          simp [hlife, hjoin] at hstep
          have hstepEq :
              result.update stepName
                  { ty := joinedTy, lifetime := rightSlot.lifetime } =
                result' :=
            hstep
          rw [← hstepEq]
          exact lookup_update_ne result
            { ty := joinedTy, lifetime := rightSlot.lifetime } hne
    · simp [hlife] at hstep

private theorem envJoinNames?_lookup_eq_of_not_mem
    {left right result out : FiniteEnv} {names : List Name} {name : Name} :
    envJoinNames? left right names result = some out →
      name ∉ names →
        out.lookup name = result.lookup name := by
  induction names generalizing result with
  | nil =>
      intro hrun _hnot
      simp [envJoinNames?] at hrun
      cases hrun
      rfl
  | cons head rest ih =>
      intro hrun hnot
      simp [envJoinNames?] at hrun
      cases hstep : envJoinStep? left right result head with
      | none =>
          simp [hstep] at hrun
      | some result' =>
          simp [hstep] at hrun
          have hne : name ≠ head := by
            intro h
            apply hnot
            simp [h]
          have hnotRest : name ∉ rest := by
            intro hmem
            apply hnot
            exact List.mem_cons_of_mem _ hmem
          rw [ih hrun hnotRest]
          exact envJoinStep?_lookup_eq_of_ne hstep hne

private theorem envJoinNames?_impossible_of_left_only
    {left right result out : FiniteEnv} {names : List Name}
    {name : Name} {leftSlot : EnvSlot} :
    name ∈ names →
      left.lookup name = some leftSlot →
        right.lookup name = none →
          envJoinNames? left right names result = some out →
            False := by
  induction names generalizing result with
  | nil =>
      intro hmem _ _ _
      cases hmem
  | cons head rest ih =>
      intro hmem hleft hright hrun
      simp [envJoinNames?] at hrun
      cases hmem with
      | head =>
          simp [envJoinStep?, hleft, hright] at hrun
      | tail _ htail =>
          cases hstep : envJoinStep? left right result head with
          | none =>
              simp [hstep] at hrun
          | some result' =>
              simp [hstep] at hrun
              exact ih htail hleft hright hrun

private theorem envJoinNames?_impossible_of_right_only
    {left right result out : FiniteEnv} {names : List Name}
    {name : Name} {rightSlot : EnvSlot} :
    name ∈ names →
      left.lookup name = none →
        right.lookup name = some rightSlot →
          envJoinNames? left right names result = some out →
            False := by
  induction names generalizing result with
  | nil =>
      intro hmem _ _ _
      cases hmem
  | cons head rest ih =>
      intro hmem hleft hright hrun
      simp [envJoinNames?] at hrun
      cases hmem with
      | head =>
          simp [envJoinStep?, hleft, hright] at hrun
      | tail _ htail =>
          cases hstep : envJoinStep? left right result head with
          | none =>
              simp [hstep] at hrun
          | some result' =>
              simp [hstep] at hrun
              exact ih htail hleft hright hrun

private theorem envJoinNames?_lookup_join_of_mem
    {left right result out : FiniteEnv} {names : List Name}
    {name : Name} {leftSlot rightSlot : EnvSlot} :
    name ∈ names →
      left.lookup name = some leftSlot →
        right.lookup name = some rightSlot →
          envJoinNames? left right names result = some out →
            ∃ joinTy,
              leftSlot.lifetime = rightSlot.lifetime ∧
                partialTyJoin? leftSlot.ty rightSlot.ty = some joinTy ∧
                  out.lookup name =
                    some { ty := joinTy, lifetime := leftSlot.lifetime } := by
  induction names generalizing result with
  | nil =>
      intro hmem _ _ _
      cases hmem
  | cons head rest ih =>
      intro hmem hleft hright hrun
      simp [envJoinNames?] at hrun
      cases hstep : envJoinStep? left right result head with
      | none =>
          simp [hstep] at hrun
      | some result' =>
          simp [hstep] at hrun
          cases hmem with
          | head =>
              unfold envJoinStep? at hstep
              simp [hleft, hright] at hstep
              by_cases hlife : leftSlot.lifetime = rightSlot.lifetime
              · cases hjoin : partialTyJoin? leftSlot.ty rightSlot.ty with
                | none =>
                    simp [hlife, hjoin] at hstep
                | some joinTy =>
                    simp [hlife, hjoin] at hstep
                    have hstepEq :
                        result' =
                          result.update name
                            { ty := joinTy, lifetime := rightSlot.lifetime } :=
                      hstep.symm
                    by_cases hmemRest : name ∈ rest
                    · rcases ih hmemRest hleft hright hrun with
                        ⟨joinTy', hlife', hjoin', hlookup'⟩
                      have hjoinEq : joinTy' = joinTy :=
                        Option.some.inj (hjoin'.symm.trans hjoin)
                      subst joinTy'
                      refine ⟨joinTy, hlife, ?_, hlookup'⟩
                      simpa [hjoin]
                    · have hpreserve :=
                        envJoinNames?_lookup_eq_of_not_mem hrun hmemRest
                      rw [hpreserve, hstepEq]
                      refine ⟨joinTy, hlife, ?_, ?_⟩
                      · simpa [hjoin]
                      · simpa [hlife] using
                          (lookup_update_eq result name
                            { ty := joinTy, lifetime := rightSlot.lifetime })
              · simp [hlife] at hstep
          | tail _ htail =>
              exact ih htail hleft hright hrun

private theorem envJoin?_slotSpec {left right join : FiniteEnv} :
    envJoin? left right = some join →
      ∀ name,
        EnvJoinSlotSpec (left.lookup name) (right.lookup name)
          (join.lookup name) := by
  intro hjoin name
  unfold envJoin? at hjoin
  let names := unionNames left.support right.support
  cases hleft : left.lookup name with
  | none =>
      cases hright : right.lookup name with
      | none =>
          have hnot : name ∉ names := by
            intro hmem
            rcases (mem_unionNames.mp hmem) with hmemLeft | hmemRight
            · rcases (mem_support_iff_lookup_isSome.mp hmemLeft) with
                ⟨slot, hslot⟩
              rw [hleft] at hslot
              cases hslot
            · rcases (mem_support_iff_lookup_isSome.mp hmemRight) with
                ⟨slot, hslot⟩
              rw [hright] at hslot
              cases hslot
          have hlookup :
              join.lookup name = (FiniteEnv.empty).lookup name :=
            envJoinNames?_lookup_eq_of_not_mem (left := left) (right := right)
              (result := FiniteEnv.empty) hjoin hnot
          rw [hlookup]
          simp [EnvJoinSlotSpec, hleft, hright, FiniteEnv.empty,
            FiniteEnv.lookup, FiniteEnv.lookupEntries]
      | some rightSlot =>
          have hmemNames : name ∈ names := by
            apply mem_unionNames.mpr
            exact Or.inr (lookup_mem_support hright)
          exact False.elim
            (envJoinNames?_impossible_of_right_only hmemNames hleft hright
              hjoin)
  | some leftSlot =>
      cases hright : right.lookup name with
      | none =>
          have hmemNames : name ∈ names := by
            apply mem_unionNames.mpr
            exact Or.inl (lookup_mem_support hleft)
          exact False.elim
            (envJoinNames?_impossible_of_left_only hmemNames hleft hright
              hjoin)
      | some rightSlot =>
          have hmemNames : name ∈ names := by
            apply mem_unionNames.mpr
            exact Or.inl (lookup_mem_support hleft)
          rcases envJoinNames?_lookup_join_of_mem hmemNames hleft hright
              hjoin with
            ⟨joinTy, hlife, htyJoin, hlookup⟩
          simp [hleft, hright, EnvJoinSlotSpec]
          rw [hlookup]
          exact ⟨hlife, rfl, partialTyJoin?_sound htyJoin⟩

private theorem envJoinSlotSpec_sound {left right join : FiniteEnv}
    (hspec :
      ∀ name,
        EnvJoinSlotSpec (left.lookup name) (right.lookup name)
          (join.lookup name)) :
    EnvJoin left.toEnv right.toEnv join.toEnv := by
  constructor
  · intro candidate hcandidate name
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with hcandidate | hcandidate <;> subst hcandidate
    · specialize hspec name
      cases hleft : left.lookup name <;>
        cases hright : right.lookup name <;>
        cases hjoin : join.lookup name <;>
        simp [EnvJoinSlotSpec, FiniteEnv.toEnv, hleft, hright, hjoin] at hspec ⊢
      rename_i leftSlot rightSlot joinSlot
      rcases hspec with ⟨_hlifeRight, hlifeJoin, htyJoin⟩
      exact ⟨hlifeJoin.symm, PartialTyUnion.left_strengthens htyJoin⟩
    · specialize hspec name
      cases hleft : left.lookup name <;>
        cases hright : right.lookup name <;>
        cases hjoin : join.lookup name <;>
        simp [EnvJoinSlotSpec, FiniteEnv.toEnv, hleft, hright, hjoin] at hspec ⊢
      rename_i leftSlot rightSlot joinSlot
      rcases hspec with ⟨hlifeRight, hlifeJoin, htyJoin⟩
      exact ⟨hlifeRight.symm.trans hlifeJoin.symm,
        PartialTyUnion.right_strengthens htyJoin⟩
  · intro upper hupper name
    have hleftUpper : left.toEnv ≤ upper :=
      hupper (by simp)
    have hrightUpper : right.toEnv ≤ upper :=
      hupper (by simp)
    specialize hspec name
    cases hleft : left.lookup name <;>
      cases hright : right.lookup name <;>
      cases hjoin : join.lookup name <;>
      simp [EnvJoinSlotSpec, FiniteEnv.toEnv, hleft, hright, hjoin] at hspec ⊢
    · cases hupperSlot : upper.slotAt name with
      | none =>
          simp [FiniteEnv.toEnv, hjoin, hupperSlot]
      | some upperSlot =>
          have hleftAt := hleftUpper name
          simp [FiniteEnv.toEnv, hleft, hupperSlot] at hleftAt
    · rcases hspec with ⟨hlifeRight, hlifeJoin, htyJoin⟩
      cases hupperSlot : upper.slotAt name with
      | none =>
          have hleftAt := hleftUpper name
          simp [FiniteEnv.toEnv, hleft, hupperSlot] at hleftAt
      | some upperSlot =>
          have hleftAt := hleftUpper name
          have hrightAt := hrightUpper name
          simp [FiniteEnv.toEnv, hleft, hright, hupperSlot] at hleftAt hrightAt
          rcases hleftAt with ⟨hlifeLeftUpper, hleftLeUpper⟩
          rcases hrightAt with ⟨_hlifeRightUpper, hrightLeUpper⟩
          exact ⟨hlifeJoin.trans hlifeLeftUpper, htyJoin.2 (by
            intro candidate hcandidate
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · subst hcandidate
              exact hleftLeUpper
            · subst hcandidate
              exact hrightLeUpper)⟩

private theorem envJoin?_sound {left right join : FiniteEnv} :
    envJoin? left right = some join →
      EnvJoin left.toEnv right.toEnv join.toEnv := by
  intro h
  exact envJoinSlotSpec_sound (envJoin?_slotSpec h)

mutual
  private theorem updateAtPath?_sound :
      ∀ {fuel rank : Nat} {env : FiniteEnv} {path : Path}
        {oldTy : PartialTy} {rhsTy : Ty} {out : FiniteEnv}
        {updatedTy : PartialTy},
        updateAtPath? fuel rank env path oldTy rhsTy =
          some (out, updatedTy) →
          UpdateAtPath rank env.toEnv path oldTy rhsTy out.toEnv updatedTy := by
    intro fuel rank env path oldTy rhsTy out updatedTy h
    cases fuel with
    | zero =>
        simp [updateAtPath?] at h
    | succ fuel =>
        cases path with
        | nil =>
            cases rank with
            | zero =>
                simp [updateAtPath?] at h
                rcases h with ⟨rfl, rfl⟩
                exact UpdateAtPath.strong
            | succ rank =>
                cases hshape :
                    shapeCompatiblePartialTy fuel env oldTy (.ty rhsTy) with
                | false =>
                    simp [updateAtPath?, hshape] at h
                | true =>
                    cases hjoin : partialTyJoin? oldTy (.ty rhsTy) with
                    | none =>
                        simp [updateAtPath?, hshape, hjoin] at h
                    | some joined =>
                        simp [updateAtPath?, hshape, hjoin] at h
                        rcases h with ⟨rfl, rfl⟩
                        exact UpdateAtPath.weak
                          (shapeCompatiblePartialTy_sound hshape)
                          (partialTyJoin?_sound hjoin)
        | cons head rest =>
            cases head
            cases oldTy with
            | ty ty =>
                cases ty with
                | borrow mutable targets =>
                    cases mutable with
                    | false =>
                        simp [updateAtPath?] at h
                    | true =>
                        cases hwrite :
                            writeBorrowTargets? fuel (rank + 1) env rest targets
                              rhsTy with
                        | none =>
                            simp [updateAtPath?, hwrite] at h
                        | some writeEnv =>
                            simp [updateAtPath?, hwrite] at h
                            rcases h with ⟨rfl, rfl⟩
                            simpa using UpdateAtPath.mutBorrow
                              (writeBorrowTargets?_sound hwrite)
                | unit =>
                    simp [updateAtPath?] at h
                | int =>
                    simp [updateAtPath?] at h
                | box inner =>
                    simp [updateAtPath?] at h
                | bool =>
                    simp [updateAtPath?] at h
            | box inner =>
                cases hinner :
                    updateAtPath? fuel rank env rest inner rhsTy with
                | none =>
                    simp [updateAtPath?, hinner] at h
                | some result =>
                    rcases result with ⟨innerEnv, updatedInner⟩
                    simp [updateAtPath?, hinner] at h
                    rcases h with ⟨rfl, rfl⟩
                    simpa using UpdateAtPath.box (updateAtPath?_sound hinner)
            | undef ty =>
                simp [updateAtPath?] at h
  termination_by fuel rank env path oldTy rhsTy out updatedTy h => (fuel, 0, 0)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      first
      | omega
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))

  private theorem writeBorrowTargets?_sound :
      ∀ {fuel rank : Nat} {env : FiniteEnv} {path : Path}
        {targets : List LVal} {rhsTy : Ty} {out : FiniteEnv},
        writeBorrowTargets? fuel rank env path targets rhsTy = some out →
          WriteBorrowTargets rank env.toEnv path targets rhsTy out.toEnv := by
    intro fuel rank env path targets rhsTy out h
    cases targets with
    | nil =>
        simp [writeBorrowTargets?] at h
        cases h
        exact WriteBorrowTargets.nil
    | cons target rest =>
        cases rest with
        | nil =>
            cases htype : lvalType? fuel env (prependPath path target) with
            | none =>
                simp [writeBorrowTargets?, htype] at h
            | some typed =>
                rcases typed with ⟨partialTy, leafLifetime⟩
                cases partialTy with
                | ty leafTy =>
                    cases hwrite :
                        envWrite? fuel rank env (prependPath path target)
                          rhsTy with
                    | none =>
                        simp [writeBorrowTargets?, htype, hwrite] at h
                    | some updated =>
                        simp [writeBorrowTargets?, htype, hwrite] at h
                        cases h
                        exact WriteBorrowTargets.singleton
                          (envWrite?_sound hwrite)
                          ⟨leafTy, leafLifetime, lvalType?_sound htype⟩
                | box inner =>
                    simp [writeBorrowTargets?, htype] at h
                | undef ty =>
                    simp [writeBorrowTargets?, htype] at h
        | cons restHead restTail =>
            cases htype : lvalType? fuel env (prependPath path target) with
            | none =>
                simp [writeBorrowTargets?, htype] at h
            | some typed =>
                rcases typed with ⟨partialTy, leafLifetime⟩
                cases partialTy with
                | ty leafTy =>
                    cases hwrite :
                        envWrite? fuel rank env (prependPath path target)
                          rhsTy with
                    | none =>
                        simp [writeBorrowTargets?, htype, hwrite] at h
                    | some updated =>
                        cases hrest :
                            writeBorrowTargets? fuel rank env path
                              (restHead :: restTail) rhsTy with
                        | none =>
                            simp [writeBorrowTargets?, htype, hwrite, hrest] at h
                        | some restUpdated =>
                            cases hjoin : envJoin? updated restUpdated with
                            | none =>
                                simp [writeBorrowTargets?, htype, hwrite, hrest,
                                  hjoin] at h
                            | some joined =>
                                simp [writeBorrowTargets?, htype, hwrite, hrest,
                                  hjoin] at h
                                cases h
                                exact WriteBorrowTargets.cons
                                  (envWrite?_sound hwrite)
                                  ⟨leafTy, leafLifetime, lvalType?_sound htype⟩
                                  (writeBorrowTargets?_sound hrest)
                                  (envJoin?_sound hjoin)
                | box inner =>
                    simp [writeBorrowTargets?, htype] at h
                | undef ty =>
                    simp [writeBorrowTargets?, htype] at h
  termination_by fuel rank env path targets rhsTy out h => (fuel, 2, targets.length)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      first
      | omega
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))

  private theorem envWrite?_sound :
      ∀ {fuel rank : Nat} {env : FiniteEnv} {lv : LVal}
        {rhsTy : Ty} {out : FiniteEnv},
        envWrite? fuel rank env lv rhsTy = some out →
          EnvWrite rank env.toEnv lv rhsTy out.toEnv := by
    intro fuel rank env lv rhsTy out h
    unfold envWrite? at h
    cases hslot : env.lookup (LVal.base lv) with
    | none =>
        simp [hslot] at h
    | some slot =>
        cases hupdate :
            updateAtPath? fuel rank env (LVal.path lv) slot.ty rhsTy with
        | none =>
            simp [hslot, hupdate] at h
        | some result =>
            rcases result with ⟨writeEnv, updatedTy⟩
            simp [hslot, hupdate] at h
            cases h
            have hwrite :
                EnvWrite rank env.toEnv lv rhsTy
                  (writeEnv.toEnv.update (LVal.base lv)
                    { slot with ty := updatedTy }) :=
              EnvWrite.intro
                (show env.toEnv.slotAt (LVal.base lv) = some slot from hslot)
                (updateAtPath?_sound hupdate)
            simpa [FiniteEnv.toEnv_update] using hwrite
  termination_by fuel rank env lv rhsTy out h => (fuel, 1, 0)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      first
      | omega
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))
end

private theorem envJoinSameShape_sound {branch join : FiniteEnv} :
    envJoinSameShape branch join = true →
      EnvJoinSameShape branch.toEnv join.toEnv := by
  intro h x branchSlot joinSlot hbranch hjoin
  unfold envJoinSameShape at h
  change branch.lookup x = some branchSlot at hbranch
  change join.lookup x = some joinSlot at hjoin
  have hmem : x ∈ branch.support := lookup_mem_support hbranch
  have hcheck := (List.all_eq_true.mp h) x hmem
  simp [hbranch, hjoin] at hcheck
  exact partialTySameShape_sound hcheck

private theorem linearizable_rankOf_sound {env : FiniteEnv} :
    linearizable env = true →
      LinearizedBy
        (fun name => (rankOf? ((envNames env).length + 1) env name).getD 0)
        env.toEnv := by
  intro h
  let fuel := (envNames env).length + 1
  intro x slot hslot v hv
  unfold linearizable at h
  have hentry : (x, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  have hentryCheck := (List.all_eq_true.mp h) (x, slot) hentry
  change
    (match rankOf? fuel env x with
    | none => false
    | some rootRank =>
        (PartialTy.vars slot.ty).all (fun dep =>
          match rankOf? fuel env dep with
          | some depRank => depRank < rootRank
          | none => false)) = true at hentryCheck
  cases hroot : rankOf? fuel env x with
  | none =>
      simp [hroot] at hentryCheck
  | some rootRank =>
      simp [hroot] at hentryCheck
      have hdepCheck := hentryCheck v hv
      cases hdep : rankOf? fuel env v with
      | none =>
          simp [hdep] at hdepCheck
        | some depRank =>
            simp [hdep] at hdepCheck
            simpa [fuel, hroot, hdep]
              using hdepCheck

private theorem linearizable_sound {env : FiniteEnv} :
    linearizable env = true → Linearizable env.toEnv := by
  intro h
  exact ⟨fun name => (rankOf? ((envNames env).length + 1) env name).getD 0,
    linearizable_rankOf_sound h⟩

private theorem linearizedByRanks?_sound {fuel : Nat}
    {rankSource env : FiniteEnv} :
    linearizedByRanks? fuel rankSource env = true →
      LinearizedBy
        (fun name => (rankOf? fuel rankSource name).getD 0)
        env.toEnv := by
  intro h x slot hslot v hv
  unfold linearizedByRanks? at h
  have hentry : (x, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  have hentryCheck := (List.all_eq_true.mp h) (x, slot) hentry
  change
    (match rankOf? fuel rankSource x with
    | none => false
    | some rootRank =>
        (PartialTy.vars slot.ty).all (fun dep =>
          match rankOf? fuel rankSource dep with
          | some depRank => depRank < rootRank
          | none => false)) = true at hentryCheck
  cases hroot : rankOf? fuel rankSource x with
  | none =>
      simp [hroot] at hentryCheck
  | some rootRank =>
      simp [hroot] at hentryCheck
      have hdepCheck := hentryCheck v hv
      cases hdep : rankOf? fuel rankSource v with
      | none =>
          simp [hdep] at hdepCheck
      | some depRank =>
          simp [hdep] at hdepCheck
          simpa [hroot, hdep] using hdepCheck

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

private theorem lvalMem_true_of_mem {target : LVal} :
    ∀ {targets : List LVal}, target ∈ targets → lvalMem target targets = true
  | [], h => by cases h
  | head :: rest, h => by
      cases h with
      | head =>
          simp [lvalMem]
      | tail _ htail =>
          by_cases heq : target = head
          · simp [lvalMem, heq]
          · simp [lvalMem, heq, lvalMem_true_of_mem htail]

private theorem targetInBorrowTargets_true {target : LVal} {rhsTy : Ty} :
    (∃ rhsMutable rhsTargets,
      PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets) ∧
        target ∈ rhsTargets) →
      targetInBorrowTargets target (tyBorrows rhsTy) = true := by
  rintro ⟨rhsMutable, rhsTargets, hcontains, htarget⟩
  unfold targetInBorrowTargets
  rw [List.any_eq_true]
  refine ⟨(rhsMutable, rhsTargets), ?_, ?_⟩
  · simpa [partialTyBorrows] using partialTyContainsBorrow_mem hcontains
  · exact lvalMem_true_of_mem htarget

private theorem containedBorrowsWellFormed_sound {fuel : Nat}
    {env : FiniteEnv} :
    containedBorrowsWellFormed fuel env = true →
      ContainedBorrowsWellFormed env.toEnv := by
  intro h x slot mutable targets hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedEq : containedSlot = slot :=
    Option.some.inj (hcontainedSlot.symm.trans hslot)
  subst containedSlot
  cases env with
  | mk entries =>
      have hentry : (x, slot) ∈ entries :=
        lookupEntries_mem hslot
      unfold containedBorrowsWellFormed at h
      have hentryCheck := (List.all_eq_true.mp h) (x, slot) hentry
      have hborrowMem :
          (mutable, targets) ∈ partialTyBorrows slot.ty :=
        partialTyContainsBorrow_mem hcontainsTy
      have htargetsCheck :=
        (List.all_eq_true.mp hentryCheck) (mutable, targets) hborrowMem
      exact BorrowTargetsWellFormed.inSlot
        (borrowTargetsWellFormed_sound htargetsCheck)

private theorem coherent_slot_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    coherent fuel env = true →
      env.lookup name = some slot →
        slot.ty = .ty (.borrow mutable targets) →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env.toEnv targets (.ty targetTy)
              targetLifetime := by
  intro hcoherent hslot hslotTy
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherent at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  rw [hslotTy] at hentryCheck
  exact tyCoherent_borrow_targets_sound
    (by simpa [partialTyCoherent] using hentryCheck)

private theorem coherent_slot_contains_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    coherent fuel env = true →
      env.lookup name = some slot →
        PartialTyContains slot.ty (.borrow mutable targets) →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env.toEnv targets (.ty targetTy)
              targetLifetime := by
  intro hcoherent hslot hcontains
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherent at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  exact partialTyCoherent_contains_borrow_targets_sound hentryCheck hcontains rfl

private theorem wellFormedKit_sound {fuel : Nat} {env : FiniteEnv} :
    wellFormedKit fuel env = true →
      ContainedBorrowsWellFormed env.toEnv ∧
        coherent fuel env = true ∧
          Linearizable env.toEnv := by
  intro h
  unfold wellFormedKit at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hcontainedAndCoherent, hlinear⟩
  rcases Bool.and_eq_true_iff.mp hcontainedAndCoherent with
    ⟨hcontained, hcoherent⟩
  exact ⟨containedBorrowsWellFormed_sound hcontained, hcoherent,
    linearizable_sound hlinear⟩

private def CheckerInvariant (env : FiniteEnv) : Prop :=
  ContainedBorrowsWellFormed env.toEnv ∧
    Coherent env.toEnv ∧
      Linearizable env.toEnv

private theorem CheckerInvariant.empty :
    CheckerInvariant FiniteEnv.empty := by
  simp [CheckerInvariant, containedBorrowsWellFormed_empty, coherent_empty,
    linearizable_empty]

private theorem CheckerInvariant.of_wellFormedKit {fuel : Nat}
    {env : FiniteEnv} :
    wellFormedKit fuel env = true →
      CheckerInvariant env := by
  intro hkit
  have hsound := wellFormedKit_sound hkit
  exact ⟨hsound.1,
    coherentWitness_sound_coherent
      (coherent_witness_sound hsound.2.1) hsound.2.2,
    hsound.2.2⟩

private theorem wellFormedKit_coherent_witness_sound {fuel : Nat}
    {env : FiniteEnv} :
    wellFormedKit fuel env = true →
      CoherentWitness fuel env.toEnv := by
  intro hkit
  exact coherent_witness_sound (wellFormedKit_sound hkit).2.1

private theorem wellFormedKit_coherent_sound {fuel : Nat}
    {env : FiniteEnv} :
    wellFormedKit fuel env = true →
      Coherent env.toEnv := by
  intro hkit
  exact coherentWitness_sound_coherent
    (wellFormedKit_coherent_witness_sound hkit)
    (wellFormedKit_sound hkit).2.2

private theorem wellFormedKit_slot_contains_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    wellFormedKit fuel env = true →
      env.lookup name = some slot →
        PartialTyContains slot.ty (.borrow mutable targets) →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env.toEnv targets (.ty targetTy)
              targetLifetime := by
  intro hkit hslot hcontains
  exact coherent_slot_contains_borrow_targets_sound
    (wellFormedKit_sound hkit).2.1 hslot hcontains

private theorem assignmentResultInvariants_sound {fuel : Nat}
    {env : FiniteEnv} :
    (containedBorrowsWellFormed fuel env && linearizable env) = true →
      ContainedBorrowsWellFormed env.toEnv ∧ Linearizable env.toEnv := by
  intro h
  rcases Bool.and_eq_true_iff.mp h with ⟨hcontained, hlinear⟩
  exact ⟨containedBorrowsWellFormed_sound hcontained,
    linearizable_sound hlinear⟩

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

private theorem rhsBorrowTargetsBelow_sound {envBefore result : FiniteEnv}
    {rhsTy : Ty} :
    rhsBorrowTargetsBelow envBefore result rhsTy = true →
      ∃ φ, LinearizedBy φ envBefore.toEnv ∧
        EnvWriteRhsBorrowTargetsBelow φ result.toEnv rhsTy := by
  intro h
  let fuel := (envNames envBefore).length + (envNames result).length + 1
  let φ : Name → Nat :=
    fun name => (rankOf? fuel result name).getD 0
  unfold rhsBorrowTargetsBelow at h
  change
    (linearizedByRanks? fuel result envBefore &&
      result.entries.all (fun entry =>
        (partialTyBorrows entry.2.ty).all (fun borrow =>
          borrow.2.all (fun target =>
            if targetInBorrowTargets target (tyBorrows rhsTy) then
              match rankOf? fuel result (LVal.base target),
                  rankOf? fuel result entry.1 with
              | some targetRank, some rootRank => targetRank < rootRank
              | _, _ => false
            else
              true))) &&
      (envBorrowEdges result).all (fun left =>
        (envBorrowEdges result).all (fun right =>
          left.2.2.all (fun leftTarget =>
            right.2.2.all (fun rightTarget =>
              if left.2.1 && pathConflicts leftTarget rightTarget &&
                  targetInBorrowTargets leftTarget (tyBorrows rhsTy) &&
                  targetInBorrowTargets rightTarget (tyBorrows rhsTy) then
                left.1 == right.1
              else
                true))))) = true at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hpreAndRank, hfanout⟩
  rcases Bool.and_eq_true_iff.mp hpreAndRank with ⟨hpre, hrank⟩
  refine ⟨φ, linearizedByRanks?_sound hpre, ?_⟩
  constructor
  · intro x slot mutable targets target hslot hcontains htarget hrhs
    change result.lookup x = some slot at hslot
    have hentry : (x, slot) ∈ result.entries :=
      lookupEntries_mem hslot
    have hborrowMem :
        (mutable, targets) ∈ partialTyBorrows slot.ty :=
      partialTyContainsBorrow_mem hcontains
    have hentryCheck :=
      (List.all_eq_true.mp hrank) (x, slot) hentry
    have hborrowCheck :=
      (List.all_eq_true.mp hentryCheck) (mutable, targets) hborrowMem
    have htargetCheck :=
      (List.all_eq_true.mp hborrowCheck) target htarget
    have htargetIn :
        targetInBorrowTargets target (tyBorrows rhsTy) = true :=
      targetInBorrowTargets_true hrhs
    simp [htargetIn] at htargetCheck
    cases htargetRank : rankOf? fuel result (LVal.base target) with
    | none =>
        simp [htargetRank] at htargetCheck
    | some targetRank =>
        cases hrootRank : rankOf? fuel result x with
        | none =>
            simp [htargetRank, hrootRank] at htargetCheck
        | some rootRank =>
            simp [htargetRank, hrootRank] at htargetCheck
            simpa [φ, htargetRank, hrootRank] using htargetCheck
  · intro x y mutable targetsMutable targetsOther targetMutable targetOther
      hleftContains hrightContains htargetMutable htargetOther hconflict
      hrhsMutable hrhsOther
    have hleftEdge :
        (x, true, targetsMutable) ∈ envBorrowEdges result :=
      envBorrowEdges_of_contains hleftContains
    have hrightEdge :
        (y, mutable, targetsOther) ∈ envBorrowEdges result :=
      envBorrowEdges_of_contains hrightContains
    have hleftCheck :=
      (List.all_eq_true.mp hfanout) (x, true, targetsMutable) hleftEdge
    have hrightCheck :=
      (List.all_eq_true.mp hleftCheck) (y, mutable, targetsOther) hrightEdge
    have htargetMutableCheck :=
      (List.all_eq_true.mp hrightCheck) targetMutable htargetMutable
    have htargetOtherCheck :=
      (List.all_eq_true.mp htargetMutableCheck) targetOther htargetOther
    have hconflictBool :
        pathConflicts targetMutable targetOther = true := by
      simpa [pathConflicts, PathConflicts] using hconflict
    have htargetMutableIn :
        targetInBorrowTargets targetMutable (tyBorrows rhsTy) = true :=
      targetInBorrowTargets_true hrhsMutable
    have htargetOtherIn :
        targetInBorrowTargets targetOther (tyBorrows rhsTy) = true :=
      targetInBorrowTargets_true hrhsOther
    simp [hconflictBool, htargetMutableIn, htargetOtherIn] at htargetOtherCheck
    simpa using htargetOtherCheck

private theorem tyBorrowSafeAgainstEnv_sound {env : FiniteEnv} {ty : Ty} :
    tyBorrowSafeAgainstEnv env ty = true →
      TyBorrowSafeAgainstEnv env.toEnv ty := by
  intro h
  unfold tyBorrowSafeAgainstEnv at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hleftSafe, hrightSafe⟩
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther
      htyContains henvContains htargetMutable htargetOther hconflict
    have htyMem :
        (true, targetsMutable) ∈ tyBorrows ty :=
      partialTyContainsBorrow_mem
        (partialTy := .ty ty) htyContains
    have hedge :
        (x, mutable, targetsOther) ∈ envBorrowEdges env :=
      envBorrowEdges_of_contains henvContains
    have htyCheck :=
      (List.all_eq_true.mp hleftSafe) (true, targetsMutable) htyMem
    simp at htyCheck
    have htargetOtherCheck :
        pathConflicts targetMutable targetOther = false := by
      cases mutable
      · exact (htyCheck x).1 targetsOther hedge
          targetMutable htargetMutable targetOther htargetOther
      · exact (htyCheck x).2 targetsOther hedge
          targetMutable htargetMutable targetOther htargetOther
    have hconflictBool : pathConflicts targetMutable targetOther = true := by
      simpa [pathConflicts, PathConflicts] using hconflict
    rw [hconflictBool] at htargetOtherCheck
    simp at htargetOtherCheck
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      henvContains htyContains htargetMutable htargetOther hconflict
    have hedge :
        (x, true, targetsMutable) ∈ envBorrowEdges env :=
      envBorrowEdges_of_contains henvContains
    have htyMem :
        (mutable, targetsOther) ∈ tyBorrows ty :=
      partialTyContainsBorrow_mem
        (partialTy := .ty ty) htyContains
    have hedgeCheck :=
      (List.all_eq_true.mp hrightSafe) (x, true, targetsMutable) hedge
    simp at hedgeCheck
    have htargetOtherCheck :
        pathConflicts targetMutable targetOther = false := by
      cases mutable
      · exact hedgeCheck.1 targetsOther htyMem
          targetMutable htargetMutable targetOther htargetOther
      · exact hedgeCheck.2 targetsOther htyMem
          targetMutable htargetMutable targetOther htargetOther
    have hconflictBool : pathConflicts targetMutable targetOther = true := by
      simpa [pathConflicts, PathConflicts] using hconflict
    rw [hconflictBool] at htargetOtherCheck
    simp at htargetOtherCheck

private theorem borrowSafeRoot_sound {env : FiniteEnv} {root : Name} :
    borrowSafeRoot env root = true → BorrowSafeRoot env.toEnv root := by
  intro h y mutable targetsMutable targetsOther targetMutable targetOther
    hrootContains hotherContains htargetMutable htargetOther hconflict
  unfold borrowSafeRoot at h
  have hrootEdge :
      (root, true, targetsMutable) ∈ envBorrowEdges env :=
    envBorrowEdges_of_contains hrootContains
  have hrootFiltered :
      (root, true, targetsMutable) ∈
        (envBorrowEdges env).filter
          (fun edge => edge.1 == root && edge.2.1) := by
    apply List.mem_filter.mpr
    constructor
    · exact hrootEdge
    · simp
  have hotherEdge :
      (y, mutable, targetsOther) ∈ envBorrowEdges env :=
    envBorrowEdges_of_contains hotherContains
  have hrootCheck :=
    (List.all_eq_true.mp h) (root, true, targetsMutable) hrootFiltered
  have hotherCheck :=
    (List.all_eq_true.mp hrootCheck) (y, mutable, targetsOther) hotherEdge
  have htargetMutableCheck :=
    (List.all_eq_true.mp hotherCheck) targetMutable htargetMutable
  have htargetOtherCheck :=
    (List.all_eq_true.mp htargetMutableCheck) targetOther htargetOther
  have hconflictBool : pathConflicts targetMutable targetOther = true := by
    simpa [pathConflicts, PathConflicts] using hconflict
  simp [hconflictBool] at htargetOtherCheck
  simpa using htargetOtherCheck

private theorem mutableBorrowTargetsOfRoot_foldl_preserves
    {edges : List (Name × Bool × List LVal)} {root : Name}
    {target : LVal} {acc : List LVal} :
    target ∈ acc →
      target ∈ edges.foldl
        (fun targets edge =>
          if edge.1 == root && edge.2.1 then unionLVals targets edge.2.2
          else targets)
        acc := by
  induction edges generalizing acc with
  | nil =>
      intro h
      exact h
  | cons edge rest ih =>
      intro h
      apply ih
      by_cases hcheck : edge.1 == root && edge.2.1
      · simp [hcheck]
        exact mem_unionLVals.mpr (Or.inl h)
      · simpa [hcheck] using h

private theorem mutableBorrowTargetsOfRoot_foldl_of_edge
    {edges : List (Name × Bool × List LVal)} {acc : List LVal}
    {root : Name} {targets : List LVal} {target : LVal} :
    (root, true, targets) ∈ edges →
      target ∈ targets →
        target ∈ edges.foldl
          (fun targets edge =>
            if edge.1 == root && edge.2.1 then unionLVals targets edge.2.2
            else targets)
          acc := by
  intro hedge htarget
  induction hedge generalizing acc with
  | head =>
      simp only [List.foldl]
      simp only [beq_self_eq_true, Bool.true_and, if_true]
      change target ∈
        List.foldl
          (fun (targets : List LVal) (edge : Name × Bool × List LVal) =>
            if edge.1 == root && edge.2.1 then unionLVals targets edge.2.2
            else targets)
          (unionLVals acc targets) _
      apply mutableBorrowTargetsOfRoot_foldl_preserves
      exact mem_unionLVals.mpr (Or.inr htarget)
  | tail edge _ ih =>
      exact ih (acc :=
        if edge.1 == root && edge.2.1 then unionLVals acc edge.2.2
        else acc)

private theorem mutableBorrowTargetsOfRoot_mem {env : FiniteEnv}
    {root : Name} {targets : List LVal} {target : LVal} :
    (root, true, targets) ∈ envBorrowEdges env →
      target ∈ targets →
        target ∈ mutableBorrowTargetsOfRoot env root := by
  intro hedge htarget
  unfold mutableBorrowTargetsOfRoot
  exact mutableBorrowTargetsOfRoot_foldl_of_edge hedge htarget

private theorem guardClosed_sound {env : FiniteEnv} {roots : List Name} :
    guardClosed env roots = true →
      ∀ {root targets target},
        root ∈ roots →
          env.toEnv ⊢ root ↝ (&mut targets) →
            target ∈ targets →
              LVal.base target ∈ roots := by
  intro hclosed root targets target hroot hcontains htarget
  unfold guardClosed at hclosed
  have hrootCheck :=
    (List.all_eq_true.mp hclosed) root hroot
  have htargetMem :
      target ∈ mutableBorrowTargetsOfRoot env root :=
    mutableBorrowTargetsOfRoot_mem (envBorrowEdges_of_contains hcontains)
      htarget
  have htargetCheck :=
    (List.all_eq_true.mp hrootCheck) target htargetMem
  simpa using htargetCheck

private theorem assignmentBorrowSafety_sound {env : FiniteEnv} {lhs : LVal} :
    assignmentBorrowSafety env lhs = true →
      AssignmentBorrowSafety env.toEnv lhs := by
  cases lhs with
  | var name =>
      intro _h
      trivial
  | deref source =>
      intro h
      unfold assignmentBorrowSafety at h
      let roots := guardedRoots env source
      have hsplit :
          (LVal.base source ∈ roots ∧ guardClosed env roots = true) ∧
            ∀ root, root ∈ roots → borrowSafeRoot env root = true := by
        simpa [roots, Bool.and_assoc] using
          (Bool.and_eq_true_iff.mp h)
      rcases hsplit with ⟨⟨hbase, hclosed⟩, hallSafe⟩
      intro root hguard
      have hrootMem : root ∈ roots := by
        induction hguard with
        | base =>
            exact hbase
        | step hcontainer hcontains htarget ih =>
            exact guardClosed_sound hclosed ih hcontains htarget
      exact borrowSafeRoot_sound (hallSafe root hrootMem)

theorem checkAssignmentBorrowSafety?_sound {env : FiniteEnv} {lhs : LVal} :
    checkAssignmentBorrowSafety? env lhs = true →
      AssignmentBorrowSafety env.toEnv lhs :=
  assignmentBorrowSafety_sound

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

private theorem checker_not_pathConflicts_of_not_writeProhibited_contains
    {env : Env} {lv target : LVal} {x : Name}
    {mutable : Bool} {targets : List LVal} :
    ¬ WriteProhibited env lv →
    env ⊢ x ↝ Ty.borrow mutable targets →
    target ∈ targets →
      ¬ target ⋈ lv := by
  intro hnotWrite hcontains htarget hconflict
  cases mutable with
  | false =>
      exact hnotWrite
        (Or.inr ⟨x, targets, target, hcontains, htarget, hconflict⟩)
  | true =>
      exact hnotWrite
        (Or.inl ⟨x, targets, target, hcontains, htarget, hconflict⟩)

private theorem lvalTyping_no_writeProhibited_targets {env : Env}
    {written : LVal} :
    ¬ WriteProhibited env written →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        ∀ target,
          target ∈ targets →
          ¬ target ⋈ written) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {mutable borrowTargets},
        PartialTyContains partialTy (.borrow mutable borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ target ⋈ written) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ written)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ written)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact checker_not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains
          target htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains
          target htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains
            hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with
            ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with
            ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ written)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ written)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact checker_not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains
          target htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains
          target htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains
            hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with
            ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with
            ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping

private theorem lvalTyping_transport_of_lookup_eq_notWrite
    {source target : FiniteEnv} {written : LVal}
    (hlookup :
      ∀ name, name ≠ LVal.base written →
        source.lookup name = target.lookup name)
    (hnotWrite : ¬ WriteProhibited source.toEnv written) :
    (∀ {lv partialTy lifetime},
      LValTyping source.toEnv lv partialTy lifetime →
      ¬ lv ⋈ written →
        LValTyping target.toEnv lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping source.toEnv targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ written) →
        LValTargetsTyping target.toEnv targets partialTy lifetime) := by
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ written →
          LValTyping target.toEnv lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ written) →
          LValTargetsTyping target.toEnv targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        have hx : x ≠ LVal.base written := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by
          simpa [FiniteEnv.toEnv, hlookup x hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ written := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ written := by
          intro target htarget
          exact (lvalTyping_no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ written →
          LValTyping target.toEnv lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ written) →
          LValTargetsTyping target.toEnv targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        have hx : x ≠ LVal.base written := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by
          simpa [FiniteEnv.toEnv, hlookup x hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ written := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ written := by
          intro target htarget
          exact (lvalTyping_no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

private theorem envWriteCoherenceObligations_of_checker {fuel : Nat}
    {before result : FiniteEnv} {lhs : LVal} :
    envEqOutside before result (LVal.base lhs) = true →
    coherentNonempty fuel result = true →
    rootCoherent fuel result (LVal.base lhs) = true →
    Linearizable result.toEnv →
    ¬ WriteProhibited result.toEnv lhs →
      EnvWriteCoherenceObligations before.toEnv result.toEnv (LVal.base lhs) := by
  intro houtside hcoherentNonempty hrootCoherent hlinear hnotWrite
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    have hlookup :
        ∀ name, name ≠ LVal.base lhs →
          result.lookup name = before.lookup name := by
      intro name hne
      exact (envEqOutside_lookup_eq houtside name hne).symm
    have hnotConflict : ¬ lv ⋈ lhs := by
      intro hconflict
      exact hbase hconflict
    have htypingBefore :
        LValTyping before.toEnv lv (.ty (.borrow mutable targets))
          borrowLifetime :=
      (lvalTyping_transport_of_lookup_eq_notWrite
          (source := result) (target := before) (written := lhs)
          hlookup hnotWrite).1 htyping hnotConflict
    refine ⟨⟨borrowLifetime, htypingBefore⟩, ?_⟩
    intro targetTy targetLifetime htargetsBefore
    have htargetsNonempty : targets ≠ [] := by
      intro hnil
      subst hnil
      exact LValTargetsTyping.nil_false htargetsBefore
    exact coherentNonempty_lvalTyping_sound
      hcoherentNonempty hlinear htyping htargetsNonempty
  · intro lv mutable targets borrowLifetime hbase htyping
    exact rootCoherent_written_root_sound
      hrootCoherent hlinear hbase htyping

private theorem writeProhibited_update_fresh_false_of_contained
    {env : Env} {name : Name} {ty : Ty} {lifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    WellFormedTy env ty lifetime →
    env.fresh name →
      ¬ WriteProhibited
        (env.update name { ty := .ty ty, lifetime := lifetime }) (.var name) := by
  intro hcontained hwellTy hfresh hwrite
  have htargetFresh :
      ∀ {root slot mutable targets target},
        (env.update name { ty := .ty ty, lifetime := lifetime }).slotAt root =
          some slot →
        PartialTyContains slot.ty (.borrow mutable targets) →
        target ∈ targets →
          LVal.base target ≠ name := by
    intro root slot mutable targets target hslot hcontains htarget hbase
    by_cases hroot : root = name
    · subst hroot
      have hslotEq :
          slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have htargets :=
        borrowTargetsWellFormedInSlot_of_wellFormedTy_contains
          hwellTy hcontains target htarget
      rcases htargets with ⟨targetTy, targetLifetime, htyping, _houtlives, _hbase⟩
      rcases LValTyping.base_slot_exists htyping with ⟨targetSlot, htargetSlot⟩
      rw [hbase, hfresh] at htargetSlot
      cases htargetSlot
    · have hslotOld : env.slotAt root = some slot := by
        simpa [Env.update, hroot] using hslot
      have hcontainsOld :
          env ⊢ root ↝ Ty.borrow mutable targets :=
        ⟨slot, hslotOld, hcontains⟩
      have htargets :=
        hcontained root slot mutable targets hslotOld hcontainsOld target
          htarget
      rcases htargets with ⟨targetTy, targetLifetime, htyping, _houtlives, _hbase⟩
      rcases LValTyping.base_slot_exists htyping with ⟨targetSlot, htargetSlot⟩
      rw [hbase, hfresh] at htargetSlot
      cases htargetSlot
  cases hwrite with
  | inl hread =>
      rcases hread with ⟨root, targets, target, hcontains, htarget, hconflict⟩
      rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
      have hbase : LVal.base target = name := by
        simpa [PathConflicts, LVal.base] using hconflict
      exact (htargetFresh hslot hcontainsTy htarget) hbase
  | inr himm =>
      rcases himm with ⟨root, targets, target, hcontains, htarget, hconflict⟩
      rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
      have hbase : LVal.base target = name := by
        simpa [PathConflicts, LVal.base] using hconflict
      exact (htargetFresh hslot hcontainsTy htarget) hbase

private theorem freshUpdateCoherenceObligations_of_checker {fuel : Nat}
    {env updated : FiniteEnv} {name : Name} {ty : Ty}
    {lifetime : Lifetime} :
    updated = env.update name { ty := .ty ty, lifetime := lifetime } →
    ContainedBorrowsWellFormed env.toEnv →
    WellFormedTy env.toEnv ty lifetime →
    env.toEnv.fresh name →
    wellFormedKit fuel updated = true →
      FreshUpdateCoherenceObligations env.toEnv name ty lifetime := by
  intro hupdated hcontained hwellTy hfresh hkit
  subst hupdated
  let slot : EnvSlot := { ty := .ty ty, lifetime := lifetime }
  have hnotWrite :
      ¬ WriteProhibited (env.update name slot).toEnv (.var name) := by
    simpa [slot, FiniteEnv.toEnv_update] using
      writeProhibited_update_fresh_false_of_contained
        hcontained hwellTy hfresh
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    have hlookup :
        ∀ root, root ≠ name →
          (env.update name slot).lookup root = env.lookup root := by
      intro root hne
      exact lookup_update_ne env slot hne
    have hnotConflict : ¬ lv ⋈ (.var name) := by
      intro hconflict
      exact hbase hconflict
    have htypingUpdated :
        LValTyping (env.update name slot).toEnv lv
          (.ty (.borrow mutable targets)) borrowLifetime := by
      simpa [slot, FiniteEnv.toEnv_update] using htyping
    exact ⟨borrowLifetime,
      (lvalTyping_transport_of_lookup_eq_notWrite
          (source := env.update name slot) (target := env)
          (written := .var name) hlookup hnotWrite).1
        htypingUpdated hnotConflict⟩
  · intro lv mutable targets borrowLifetime hbase htyping
    have hcoherent : Coherent (env.update name slot).toEnv :=
      wellFormedKit_coherent_sound hkit
    have htypingUpdated :
        LValTyping (env.update name slot).toEnv lv
          (.ty (.borrow mutable targets)) borrowLifetime := by
      simpa [slot, FiniteEnv.toEnv_update] using htyping
    rcases hcoherent lv mutable targets borrowLifetime htypingUpdated with
      ⟨targetTy, targetLifetime, htargets⟩
    exact ⟨targetTy, targetLifetime, by
      simpa [slot, FiniteEnv.toEnv_update] using htargets⟩

private theorem envSlotsOutlive_update_fresh_current
    {env : Env} {name : Name} {ty : Ty} {lifetime : Lifetime} :
    EnvSlotsOutlive env lifetime →
    env.fresh name →
      EnvSlotsOutlive
        (env.update name { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro houtlives hfresh candidate slot hslot
  by_cases hname : candidate = name
  · subst candidate
    have hslotEq :
        slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      exact (Option.some.inj (by simpa [Env.update] using hslot)).symm
    subst hslotEq
    exact LifetimeOutlives.refl lifetime
  · have hold : env.slotAt candidate = some slot := by
      simpa [Env.update, hname] using hslot
    exact houtlives candidate slot hold

private def CheckerStoreTypingRefsWellFormed
    (env : Env) (typing : StoreTyping) (lifetime : Lifetime) : Prop :=
  ∀ (ref : Reference) (ty : Ty),
    typing.tyOf ref.location = some ty →
    WellFormedTy env ty lifetime

private def CheckTermSoundAt (fuel : Nat) : Prop :=
  ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {result : CheckResult},
    (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
    WellFormedEnv env.toEnv lifetime →
    checkTerm? fuel env typing lifetime term = .ok result →
      TermTyping env.toEnv typing lifetime term result.ty result.env.toEnv ∧
        WellFormedEnv result.env.toEnv lifetime ∧
          WellFormedTy result.env.toEnv result.ty lifetime

private theorem valueTyping_result_wellFormed_of_checkerRefs {env : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    CheckerStoreTypingRefsWellFormed env typing lifetime →
    ValueTyping typing value ty →
    WellFormedTy env ty lifetime := by
  intro hrefs htyping
  cases htyping with
  | unit | int | bool => constructor
  | ref hlookup =>
      exact hrefs _ _ hlookup

private theorem checkTermList?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
      {terms : List Term} {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
      checkTermList? fuel env typing lifetime terms = .ok result →
        TermListTyping env.toEnv typing lifetime terms result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro env typing lifetime terms
  induction terms generalizing env with
  | nil =>
      intro result hrefs hwell hcheck
      simp [checkTermList?] at hcheck
  | cons term rest ih =>
      intro result hrefs hwell hcheck
      cases rest with
      | nil =>
          simp [checkTermList?] at hcheck
          have hterm := termSound hrefs hwell hcheck
          exact ⟨TermListTyping.singleton hterm.1, hterm.2⟩
      | cons restHead restTail =>
          cases hhead : checkTerm? fuel env typing lifetime term with
          | error message =>
              simp [checkTermList?, hhead, Bind.bind, Except.bind] at hcheck
          | ok headResult =>
              simp [checkTermList?, hhead, Except.bind] at hcheck
              have hheadSound := termSound hrefs hwell hhead
              have hrestSound := ih hrefs hheadSound.2.1 hcheck
              exact ⟨TermListTyping.cons hheadSound.1 hrestSound.1,
                hrestSound.2⟩

private def CheckTermTypingSoundAt (fuel : Nat) : Prop :=
  ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {result : CheckResult},
    checkTerm? fuel env typing lifetime term = .ok result →
      TermTyping env.toEnv typing lifetime term result.ty result.env.toEnv

private theorem checkTermList?_typing_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermTypingSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
      {terms : List Term} {result : CheckResult},
      checkTermList? fuel env typing lifetime terms = .ok result →
        TermListTyping env.toEnv typing lifetime terms result.ty
          result.env.toEnv := by
  intro env typing lifetime terms
  induction terms generalizing env with
  | nil =>
      intro result hcheck
      simp [checkTermList?] at hcheck
  | cons term rest ih =>
      intro result hcheck
      cases rest with
      | nil =>
          simp [checkTermList?] at hcheck
          exact TermListTyping.singleton (termSound hcheck)
      | cons restHead restTail =>
          cases hhead : checkTerm? fuel env typing lifetime term with
          | error message =>
              simp [checkTermList?, hhead, Bind.bind, Except.bind] at hcheck
          | ok headResult =>
              simp [checkTermList?, hhead, Except.bind] at hcheck
              exact TermListTyping.cons (termSound hhead) (ih hcheck)

private theorem termTyping_preserves_wellFormed_for_checker
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
    WellFormedEnv env₁ lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs hwell htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
        WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
        WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_checkerRefs
            (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _ty} hwellTy _hloanFree _htypingEq
        hwellFormed =>
      ⟨hwellFormed, hwellTy⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed, copyTy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
        hLv hnotWrite hmove _htypingEq hwellFormed =>
      move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty}
        hLv _hmutable _hwrite _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty}
        hLv _hread _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed
            (LifetimeChild.outlives hblockChild))
      block_preserves_wellFormed hblockChild bodyResult.1 hterms hwellTy
        hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcohObligations henv₃ ih htypingEq
        hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcohObligations)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy
          _rhs _rhsTy}
        hLhs hRhs _hRhsSafe _hLhsPost _hshape _hwellRhs hwrite hranked
        hwriteCoh hcontained hnotWrite ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        rcases hranked with ⟨φ, hlinBy, hbelow⟩
        have hlin3By :=
          EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
            hwrite hlinBy hbelow
        have hcoh3 := EnvWrite.preserves_coherent_of_obligations
          result.1.2.2.1 hwriteCoh
        exact ⟨⟨hcontained,
            EnvWrite.preserves_slotsOutlive result.1.2.1 hwrite,
            hcoh3,
            Linearizable.of_linearizedBy hlin3By⟩,
          WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _env₃ _envGhost _ghost _typing _lifetime _lhs _rhs
          _lhsTy _rhsTy _ghostRhsTy}
        _hLhs _hfresh _hghostRhs _hRhs _hcopyL _hcopyR _hshape
        ihL _ihGhost ihR htypingEq hwellFormed =>
      let leftResult := ihL htypingEq hwellFormed
      let rightResult := ihR htypingEq leftResult.1
      ⟨rightResult.1, WellFormedTy.bool⟩)
    (fun {_env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
          _trueBranch _falseBranch _trueTy _falseTy _joinTy}
        _hcondition _htrue _hfalse _hjoin henvJoin _hsameLeft _hsameRight
        hwellJoin hcontained hcoherent hlinear _hresultSafe ihCondition
        ihTrue _ihFalse htypingEq hwellFormed =>
      let conditionResult := ihCondition htypingEq hwellFormed
      let thenResult := ihTrue htypingEq conditionResult.1
      ⟨⟨hcontained,
          EnvSlotsOutlive.of_lifetimesPreserved thenResult.1.2.1
            (EnvJoin.lifetimesPreserved_left henvJoin),
          hcoherent, hlinear⟩,
        hwellJoin⟩)
    (fun {_env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition
          _trueBranch _falseBranch _trueTy _falseTy}
        _hcondition _htrue _hfalse _hdiverges ihCondition ihTrue _ihFalse
        htypingEq hwellFormed =>
      let conditionResult := ihCondition htypingEq hwellFormed
      ihTrue htypingEq conditionResult.1)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition
          _body _bodyTy}
        _hchild _hcond _hbody _hwellTy _hdrop ihCond _ihBody htypingEq
        hwellFormed =>
      let conditionResult := ihCond htypingEq hwellFormed
      ⟨conditionResult.1, WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition
          _body _bodyTy}
        _hchild _hcond _hbody _hdiverges ihCond _ihBody htypingEq
        hwellFormed =>
      let conditionResult := ihCond htypingEq hwellFormed
      ⟨conditionResult.1, WellFormedTy.unit⟩)
    (fun {_env₁ _envBack _envInv _env₂ _envEntry₂ _env₃ _envEntry₃ _typing
          _lifetime _bodyLifetime _condition _body _bodyTy _bodyEntryTy}
        _hchild hjoin _hss1 _hss2 hcbwf hcoh hlin _hcondInv _hbodyInv
        _hwellTy _hdrop _hcondEntry _hbodyEntry ihCondInv _ihBodyInv
        _ihCondEntry _ihBodyEntry htypingEq hwellFormed =>
      let invWellFormed : WellFormedEnv _envInv _lifetime :=
        ⟨hcbwf,
          EnvSlotsOutlive.of_lifetimesPreserved hwellFormed.2.1
            (EnvJoin.lifetimesPreserved_left hjoin),
          hcoh, hlin⟩
      let conditionResult := ihCondInv htypingEq invWellFormed
      ⟨conditionResult.1, WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
      let headResult := ihHead htypingEq hwellFormed
      ihRest htypingEq headResult.1)
    htyping rfl hwell

private theorem checkTermSound_of_typing
    {env resultEnv : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hrefs :
      ∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime)
    (hwell : WellFormedEnv env.toEnv lifetime)
    (htyping : TermTyping env.toEnv typing lifetime term ty resultEnv.toEnv) :
    TermTyping env.toEnv typing lifetime term ty resultEnv.toEnv ∧
      WellFormedEnv resultEnv.toEnv lifetime ∧
        WellFormedTy resultEnv.toEnv ty lifetime := by
  exact ⟨htyping,
    termTyping_preserves_wellFormed_for_checker hrefs hwell htyping⟩

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

private theorem checkStrictWhile?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
      {condition body : Term} {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
      checkStrictWhile? fuel env typing lifetime bodyLifetime condition body =
        .ok result →
        TermTyping env.toEnv typing lifetime
          (.whileLoop bodyLifetime condition body) result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro env typing lifetime bodyLifetime condition body result hrefs hwell hcheck
  unfold checkStrictWhile? at hcheck
  cases hchildCheck : isLifetimeChild lifetime bodyLifetime
  · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
  · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
    have hchild := isLifetimeChild_sound hchildCheck
    cases hcondition :
        checkTerm? fuel env typing lifetime condition with
    | error message =>
        simp [hcondition, Bind.bind, Except.bind] at hcheck
    | ok conditionResult =>
        simp [hcondition, Bind.bind, Except.bind] at hcheck
        by_cases hconditionTy : conditionResult.ty = .bool
        · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck
          have hconditionSound := termSound hrefs hwell hcondition
          have hbodyWell : WellFormedEnv conditionResult.env.toEnv bodyLifetime :=
            WellFormedEnv.of_outlives hconditionSound.2.1
              (LifetimeChild.outlives hchild)
          cases hbody :
              checkTerm? fuel conditionResult.env typing bodyLifetime body with
          | error message =>
              simp [hbody, Bind.bind, Except.bind] at hcheck
          | ok bodyResult =>
              simp [hbody, Bind.bind, Except.bind] at hcheck
              cases hbodyTyCheck :
                  wellFormedTy fuel bodyResult.env bodyResult.ty lifetime
              · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
              · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                cases hrestore :
                    envEqOnSupport
                      (bodyResult.env.dropLifetime bodyLifetime) env
                · simp [ensure, hrestore, Bind.bind, Except.bind] at hcheck
                · simp [ensure, hrestore, Bind.bind, Except.bind] at hcheck
                  have hbodySound := termSound hrefs hbodyWell hbody
                  have hdrop :
                      bodyResult.env.toEnv.dropLifetime bodyLifetime = env.toEnv := by
                    have hsame :
                        (bodyResult.env.dropLifetime bodyLifetime).toEnv =
                          env.toEnv := by
                      exact sameBindings_toEnv_eq hrestore
                    simpa [FiniteEnv.toEnv_dropLifetime] using hsame
                  cases hcheck
                  have htyping :
                      TermTyping env.toEnv typing lifetime
                        (.whileLoop bodyLifetime condition body) .unit
                        conditionResult.env.toEnv :=
                    TermTyping.whileLoop hchild
                      (by simpa [hconditionTy] using hconditionSound.1)
                      hbodySound.1
                      (wellFormedTy_sound hbodyTyCheck)
                      hdrop
                  exact checkTermSound_of_typing hrefs hwell htyping
        · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck

private theorem checkWhileJoinLoop?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {iterations : Nat} {entry inv : FiniteEnv} {typing : StoreTyping}
      {lifetime bodyLifetime : Lifetime} {condition body : Term}
      {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      LifetimeChild lifetime bodyLifetime →
      WellFormedEnv entry.toEnv lifetime →
      WellFormedEnv inv.toEnv lifetime →
      checkWhileJoinLoop? iterations fuel entry inv typing lifetime
        bodyLifetime condition body = .ok result →
        TermTyping entry.toEnv typing lifetime
          (.whileLoop bodyLifetime condition body) result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro iterations
  induction iterations with
  | zero =>
      intro entry inv typing lifetime bodyLifetime condition body result
        hrefs hchild hentryWell hinvWell hcheck
      simp [checkWhileJoinLoop?] at hcheck
  | succ iterations ih =>
      intro entry inv typing lifetime bodyLifetime condition body result
        hrefs hchild hentryWell hinvWell hcheck
      simp [checkWhileJoinLoop?] at hcheck
      cases hcondition :
          checkTerm? fuel inv typing lifetime condition with
      | error message =>
          simp [hcondition, Bind.bind, Except.bind] at hcheck
      | ok conditionResult =>
        simp [hcondition, Bind.bind, Except.bind] at hcheck
        by_cases hconditionTy : conditionResult.ty = .bool
        · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck
          have hconditionSound := termSound hrefs hinvWell hcondition
          have hbodyWell :
              WellFormedEnv conditionResult.env.toEnv bodyLifetime :=
            WellFormedEnv.of_outlives hconditionSound.2.1
              (LifetimeChild.outlives hchild)
          cases hbody :
              checkTerm? fuel conditionResult.env typing bodyLifetime body with
            | error message =>
                simp [hbody, Bind.bind, Except.bind] at hcheck
            | ok bodyResult =>
                simp [hbody, Bind.bind, Except.bind] at hcheck
                cases hbodyTyCheck :
                    wellFormedTy fuel bodyResult.env bodyResult.ty lifetime
                · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                  let back := bodyResult.env.dropLifetime bodyLifetime
                  cases hjoin : envJoin? entry back with
                  | none =>
                      simp [back, fromOption, hjoin, Bind.bind, Except.bind] at hcheck
                  | some nextInv =>
                      simp [back, fromOption, hjoin, Bind.bind, Except.bind] at hcheck
                      cases hentryShape : envJoinSameShape entry nextInv
                      · simp [ensure, hentryShape, Bind.bind, Except.bind] at hcheck
                      · simp [ensure, hentryShape, Bind.bind, Except.bind] at hcheck
                        cases hbackShape : envJoinSameShape back nextInv
                        · simp [back, ensure, hbackShape, Bind.bind, Except.bind] at hcheck
                        · simp [back, ensure, hbackShape, Bind.bind, Except.bind] at hcheck
                          cases hkit : wellFormedKit fuel nextInv
                          · simp [ensure, hkit, Bind.bind, Except.bind] at hcheck
                          · simp [ensure, hkit, Bind.bind, Except.bind] at hcheck
                            have hbodySound := termSound hrefs hbodyWell hbody
                            have hjoinSound : EnvJoin entry.toEnv back.toEnv nextInv.toEnv :=
                              envJoin?_sound hjoin
                            have hkitSound := wellFormedKit_sound hkit
                            have hnextWell : WellFormedEnv nextInv.toEnv lifetime :=
                              ⟨hkitSound.1,
                                EnvSlotsOutlive.of_lifetimesPreserved
                                  hentryWell.2.1
                                  (EnvJoin.lifetimesPreserved_left hjoinSound),
                                wellFormedKit_coherent_sound hkit,
                                hkitSound.2.2⟩
                            cases hfixed : envEqOnSupport nextInv inv
                            · simp [hfixed, Bind.bind, Except.bind] at hcheck
                              exact ih hrefs hchild hentryWell hnextWell hcheck
                            · simp [hfixed, Bind.bind, Except.bind] at hcheck
                              cases hentryCondition :
                                  checkTerm? fuel entry typing lifetime condition with
                              | error message =>
                                  simp [hentryCondition, Bind.bind, Except.bind] at hcheck
                              | ok entryCondition =>
                                  simp [hentryCondition, Bind.bind, Except.bind] at hcheck
                                  by_cases hentryConditionTy :
                                      entryCondition.ty = .bool
                                  · simp [ensure, hentryConditionTy,
                                      Bind.bind, Except.bind] at hcheck
                                    have hentryConditionSound :=
                                      termSound hrefs hentryWell hentryCondition
                                    have hentryBodyWell :
                                        WellFormedEnv entryCondition.env.toEnv
                                          bodyLifetime :=
                                      WellFormedEnv.of_outlives
                                        hentryConditionSound.2.1
                                        (LifetimeChild.outlives hchild)
                                    cases hentryBody :
                                        checkTerm? fuel entryCondition.env typing
                                          bodyLifetime body with
                                    | error message =>
                                        simp [hentryBody, Bind.bind, Except.bind,
                                          discard, Functor.mapConst, Except.map]
                                          at hcheck
                                    | ok entryBody =>
                                        simp [hentryBody, Bind.bind, Except.bind]
                                          at hcheck
                                        cases hcheck
                                        have hsame :
                                            nextInv.toEnv = inv.toEnv :=
                                          sameBindings_toEnv_eq hfixed
                                        have hjoinInv :
                                            EnvJoin entry.toEnv back.toEnv inv.toEnv := by
                                          simpa [hsame] using hjoinSound
                                        have hentryShapeInv :
                                            EnvJoinSameShape entry.toEnv inv.toEnv := by
                                          simpa [hsame] using
                                            envJoinSameShape_sound hentryShape
                                        have hbackShapeInv :
                                            EnvJoinSameShape back.toEnv inv.toEnv := by
                                          simpa [hsame] using
                                            envJoinSameShape_sound hbackShape
                                        have hcontainedInv :
                                            ContainedBorrowsWellFormed inv.toEnv := by
                                          simpa [hsame] using hkitSound.1
                                        have hcoherentInv : Coherent inv.toEnv := by
                                          simpa [hsame] using
                                            wellFormedKit_coherent_sound hkit
                                        have hlinearInv : Linearizable inv.toEnv := by
                                          simpa [hsame] using hkitSound.2.2
                                        have hdrop :
                                            bodyResult.env.toEnv.dropLifetime
                                              bodyLifetime = back.toEnv := by
                                          simp [back, FiniteEnv.toEnv_dropLifetime]
                                        have hentryBodySound :=
                                          termSound hrefs hentryBodyWell hentryBody
                                        have htyping :
                                            TermTyping entry.toEnv typing lifetime
                                              (.whileLoop bodyLifetime condition body)
                                              .unit conditionResult.env.toEnv :=
                                          TermTyping.whileLoopJoin hchild
                                            hjoinInv hentryShapeInv hbackShapeInv
                                            hcontainedInv hcoherentInv hlinearInv
                                            (by simpa [hconditionTy] using
                                              hconditionSound.1)
                                            hbodySound.1
                                            (wellFormedTy_sound hbodyTyCheck)
                                            hdrop
                                            (by simpa [hentryConditionTy] using
                                              hentryConditionSound.1)
                                            hentryBodySound.1
                                        exact checkTermSound_of_typing hrefs
                                          hentryWell htyping
                                  · simp [ensure, hentryConditionTy,
                                      Bind.bind, Except.bind] at hcheck
        · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck

private theorem checkWhileJoin?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
      {condition body : Term} {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
      checkWhileJoin? fuel env typing lifetime bodyLifetime condition body =
        .ok result →
        TermTyping env.toEnv typing lifetime
          (.whileLoop bodyLifetime condition body) result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro env typing lifetime bodyLifetime condition body result hrefs hwell hcheck
  unfold checkWhileJoin? at hcheck
  cases hchildCheck : isLifetimeChild lifetime bodyLifetime
  · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
  · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
    exact checkWhileJoinLoop?_sound_of_termSound termSound
      hrefs (isLifetimeChild_sound hchildCheck) hwell hwell hcheck

private theorem checkWhile?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
      {condition body : Term} {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
      checkWhile? fuel env typing lifetime bodyLifetime condition body =
        .ok result →
        TermTyping env.toEnv typing lifetime
          (.whileLoop bodyLifetime condition body) result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro env typing lifetime bodyLifetime condition body result hrefs hwell hcheck
  unfold checkWhile? at hcheck
  cases hstrict :
      checkStrictWhile? fuel env typing lifetime bodyLifetime condition body with
  | ok strictResult =>
      simp [hstrict] at hcheck
      cases hcheck
      exact checkStrictWhile?_sound_of_termSound termSound hrefs hwell hstrict
  | error message =>
      simp [hstrict] at hcheck
      cases hdiv : termDiverges body
      · simp [hdiv] at hcheck
        exact checkWhileJoin?_sound_of_termSound termSound hrefs hwell hcheck
      · simp [hdiv] at hcheck

private theorem checkTerm?_sound_at : ∀ fuel, CheckTermSoundAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro env typing lifetime term result _hrefs _hwell hcheck
      cases term <;> simp [checkTerm?] at hcheck
  | succ fuel ih =>
      intro env typing lifetime term result hrefs hwell hcheck
      cases term with
      | val value =>
          simp [checkTerm?] at hcheck
          cases hty : valueTy? typing value with
          | none =>
              simp [hty, fromOption, Bind.bind, Except.bind] at hcheck
          | some ty =>
              simp [hty, fromOption, Bind.bind, Except.bind] at hcheck
              cases hcheck
              exact checkTermSound_of_typing hrefs hwell
                (TermTyping.const (valueTy?_sound hty))
      | missing =>
          simp [checkTerm?] at hcheck
      | copy lv =>
          simp [checkTerm?] at hcheck
          cases hlv : lvalType? fuel env lv with
          | none =>
              simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
          | some typed =>
              rcases typed with ⟨partialTy, valueLifetime⟩
              cases partialTy with
              | ty ty =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
                  cases hcopy : copyTy ty
                  · simp [ensure, hcopy, Bind.bind, Except.bind] at hcheck
                  · simp [ensure, hcopy, Bind.bind, Except.bind] at hcheck
                    cases hread : readProhibited env lv
                    · simp [ensure, hread, Bind.bind, Except.bind] at hcheck
                      cases hcheck
                      exact checkTermSound_of_typing hrefs hwell
                        (TermTyping.copy (lvalType?_sound hlv)
                          (copyTy_sound hcopy)
                          (readProhibited_false_sound hread))
                    · simp [ensure, hread, Bind.bind, Except.bind] at hcheck
              | box _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
              | undef _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
      | move lv =>
          simp [checkTerm?] at hcheck
          cases hlv : lvalType? fuel env lv with
          | none =>
              simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
          | some typed =>
              rcases typed with ⟨partialTy, valueLifetime⟩
              cases partialTy with
              | ty ty =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
                  cases hwriteProhibited : writeProhibited env lv
                  · simp [ensure, hwriteProhibited, Bind.bind, Except.bind]
                      at hcheck
                    cases hmoved : envMove? env lv with
                    | none =>
                        simp [hmoved, fromOption, Bind.bind, Except.bind]
                          at hcheck
                    | some moved =>
                        simp [hmoved, fromOption, Bind.bind, Except.bind]
                          at hcheck
                        cases hcheck
                        exact checkTermSound_of_typing hrefs hwell
                          (TermTyping.move (lvalType?_sound hlv)
                            (writeProhibited_false_sound hwriteProhibited)
                            (envMove?_sound hmoved))
                  · simp [ensure, hwriteProhibited, Bind.bind, Except.bind]
                      at hcheck
              | box _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
              | undef _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
      | borrow mutable lv =>
          simp [checkTerm?] at hcheck
          cases hlv : lvalType? fuel env lv with
          | none =>
              simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
          | some typed =>
              rcases typed with ⟨partialTy, valueLifetime⟩
              cases partialTy with
              | ty ty =>
                  cases mutable with
                  | false =>
                      simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
                      cases hread : readProhibited env lv
                      · simp [ensure, hread, Bind.bind, Except.bind] at hcheck
                        cases hcheck
                        exact checkTermSound_of_typing hrefs hwell
                          (TermTyping.immBorrow (lvalType?_sound hlv)
                            (readProhibited_false_sound hread))
                      · simp [ensure, hread, Bind.bind, Except.bind] at hcheck
                  | true =>
                      simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
                      cases hmutable : mutableLVal fuel env lv
                      · simp [ensure, hmutable, Bind.bind, Except.bind]
                          at hcheck
                      · simp [ensure, hmutable, Bind.bind, Except.bind]
                          at hcheck
                        cases hwrite : writeProhibited env lv
                        · simp [ensure, hwrite, Bind.bind, Except.bind]
                            at hcheck
                          cases hcheck
                          exact checkTermSound_of_typing hrefs hwell
                            (TermTyping.mutBorrow (lvalType?_sound hlv)
                              (mutableLVal_sound hmutable)
                              (writeProhibited_false_sound hwrite))
                        · simp [ensure, hwrite, Bind.bind, Except.bind]
                            at hcheck
              | box _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
              | undef _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
      | box operand =>
          simp [checkTerm?] at hcheck
          cases hoperand : checkTerm? fuel env typing lifetime operand with
          | error message =>
              simp [hoperand, Bind.bind, Except.bind] at hcheck
          | ok operandResult =>
              simp [hoperand, Bind.bind, Except.bind] at hcheck
              cases hcheck
              have hoperandSound := ih hrefs hwell hoperand
              exact checkTermSound_of_typing hrefs hwell
                (TermTyping.box hoperandSound.1)
      | block blockLifetime terms =>
          simp [checkTerm?] at hcheck
          cases hchildCheck : isLifetimeChild lifetime blockLifetime
          · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
          · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
            have hchild := isLifetimeChild_sound hchildCheck
            have hbodyWell : WellFormedEnv env.toEnv blockLifetime :=
              WellFormedEnv.weaken hwell (LifetimeChild.outlives hchild)
            cases hbody :
                checkTermList? fuel env typing blockLifetime terms with
            | error message =>
                simp [hbody, Bind.bind, Except.bind] at hcheck
            | ok bodyResult =>
                simp [hbody, Bind.bind, Except.bind] at hcheck
                cases hbodyTyCheck :
                    wellFormedTy fuel bodyResult.env bodyResult.ty lifetime
                · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                  cases hcheck
                  have hbodySound :=
                    checkTermList?_sound_of_termSound ih hrefs hbodyWell hbody
                  have htyping :
                      TermTyping env.toEnv typing lifetime
                        (.block blockLifetime terms) bodyResult.ty
                        (bodyResult.env.dropLifetime blockLifetime).toEnv :=
                    TermTyping.block hchild hbodySound.1
                      (wellFormedTy_sound hbodyTyCheck)
                      (by simp [FiniteEnv.toEnv_dropLifetime])
                  exact checkTermSound_of_typing hrefs hwell htyping
      | letMut name initialiser =>
          simp [checkTerm?] at hcheck
          cases hfreshIn : env.fresh name
          · simp [ensure, hfreshIn, Bind.bind, Except.bind] at hcheck
          · simp [ensure, hfreshIn, Bind.bind, Except.bind] at hcheck
            cases hinitialiser :
                checkTerm? fuel env typing lifetime initialiser with
            | error message =>
                simp [hinitialiser, Bind.bind, Except.bind] at hcheck
            | ok initResult =>
                simp [hinitialiser, Bind.bind, Except.bind] at hcheck
                have hinitSound := ih hrefs hwell hinitialiser
                cases hfreshOut : initResult.env.fresh name
                · simp [ensure, hfreshOut, Bind.bind, Except.bind] at hcheck
                · simp [ensure, hfreshOut, Bind.bind, Except.bind] at hcheck
                  let updated :=
                    initResult.env.update name
                      { ty := .ty initResult.ty, lifetime := lifetime }
                  cases hkit : wellFormedKit fuel updated
                  · simp [updated, ensure, hkit, Bind.bind, Except.bind]
                      at hcheck
                  · simp [updated, ensure, hkit, Bind.bind, Except.bind]
                      at hcheck
                    cases hcheck
                    have hcoherence :
                        FreshUpdateCoherenceObligations initResult.env.toEnv
                          name initResult.ty lifetime :=
                      freshUpdateCoherenceObligations_of_checker
                        (env := initResult.env) (updated := updated)
                        (name := name) (ty := initResult.ty)
                        (lifetime := lifetime) rfl
                        hinitSound.2.1.1 hinitSound.2.2
                        (FiniteEnv.fresh_sound hfreshOut) hkit
                    have htyping :
                        TermTyping env.toEnv typing lifetime
                          (.letMut name initialiser) .unit updated.toEnv :=
                      TermTyping.declare (FiniteEnv.fresh_sound hfreshIn)
                        hinitSound.1 (FiniteEnv.fresh_sound hfreshOut) hcoherence
                        (by simp [updated, FiniteEnv.toEnv_update])
                    exact checkTermSound_of_typing hrefs hwell htyping
      | assign lhs rhs =>
          simp [checkTerm?] at hcheck
          cases hlhsBefore : lvalType? fuel env lhs with
          | none =>
              simp [hlhsBefore, fromOption, Bind.bind, Except.bind] at hcheck
          | some lhsBefore =>
              rcases lhsBefore with ⟨oldTy, targetLifetime⟩
              simp [hlhsBefore, fromOption, Bind.bind, Except.bind] at hcheck
              cases hrhs : checkTerm? fuel env typing lifetime rhs with
              | error message =>
                  simp [hrhs, Bind.bind, Except.bind] at hcheck
              | ok rhsResult =>
                  simp [hrhs, Bind.bind, Except.bind] at hcheck
                  have hrhsSound := ih hrefs hwell hrhs
                  cases hassignSafe : assignmentBorrowSafety rhsResult.env lhs
                  · simp [ensure, hassignSafe, Bind.bind, Except.bind] at hcheck
                  · simp [ensure, hassignSafe, Bind.bind, Except.bind] at hcheck
                    cases hlhsAfter :
                        lvalType? fuel rhsResult.env lhs with
                    | none =>
                        simp [hlhsAfter, fromOption, Bind.bind, Except.bind]
                          at hcheck
                    | some lhsAfter =>
                        rcases lhsAfter with ⟨oldTyAfter, targetLifetimeAfter⟩
                        simp [hlhsAfter, fromOption, Bind.bind, Except.bind]
                          at hcheck
                        by_cases hOldEq : oldTyAfter = oldTy
                        · by_cases hLifetimeEq :
                              targetLifetimeAfter = targetLifetime
                          · simp [ensure, hOldEq, hLifetimeEq, Bind.bind,
                              Except.bind] at hcheck
                            subst oldTyAfter
                            subst targetLifetimeAfter
                            cases hshape :
                                shapeCompatiblePartialTy fuel rhsResult.env
                                  oldTy (.ty rhsResult.ty)
                            · simp [ensure, hshape, Bind.bind, Except.bind]
                                at hcheck
                            · simp [ensure, hshape, Bind.bind, Except.bind]
                                at hcheck
                              cases hwellRhs :
                                  wellFormedTy fuel rhsResult.env
                                    rhsResult.ty targetLifetime
                              · simp [ensure, hwellRhs, Bind.bind,
                                  Except.bind] at hcheck
                              · simp [ensure, hwellRhs, Bind.bind,
                                  Except.bind] at hcheck
                                cases hwrite :
                                    envWrite? fuel 0 rhsResult.env lhs
                                      rhsResult.ty with
                                | none =>
                                    simp [hwrite, fromOption, Bind.bind,
                                      Except.bind] at hcheck
                                | some written =>
                                    simp [hwrite, fromOption, Bind.bind,
                                      Except.bind] at hcheck
                                    cases houtside :
                                        envEqOutside rhsResult.env written
                                          (LVal.base lhs)
                                    · simp [ensure, houtside, Bind.bind,
                                        Except.bind] at hcheck
                                    · simp [ensure, houtside, Bind.bind,
                                        Except.bind] at hcheck
                                      cases hbelow :
                                          rhsBorrowTargetsBelow rhsResult.env
                                            written rhsResult.ty
                                      · simp [ensure, hbelow, Bind.bind,
                                          Except.bind] at hcheck
                                      · simp [ensure, hbelow, Bind.bind,
                                          Except.bind] at hcheck
                                        by_cases hcontained :
                                            containedBorrowsWellFormed fuel
                                              written = true
                                        · by_cases hlinear :
                                              linearizable written = true
                                          · have hinvariants :
                                              (containedBorrowsWellFormed fuel
                                                  written &&
                                                linearizable written) = true := by
                                              simp [hcontained, hlinear]
                                            simp [ensure, hcontained, hlinear,
                                              Bind.bind, Except.bind] at hcheck
                                            cases hcoherentNonempty :
                                                coherentNonempty fuel written
                                            · simp [ensure, hcoherentNonempty,
                                                Bind.bind, Except.bind] at hcheck
                                            · simp [ensure, hcoherentNonempty,
                                                Bind.bind, Except.bind] at hcheck
                                              cases hrootCoherent :
                                                  rootCoherent fuel written
                                                    (LVal.base lhs)
                                              · simp [ensure, hrootCoherent,
                                                  Bind.bind, Except.bind]
                                                  at hcheck
                                              · simp [ensure, hrootCoherent,
                                                  Bind.bind, Except.bind]
                                                  at hcheck
                                                cases hnotWrite :
                                                    writeProhibited written lhs
                                                · simp [ensure, hnotWrite,
                                                    Bind.bind, Except.bind]
                                                    at hcheck
                                                  cases hcheck
                                                  have hinv :=
                                                    assignmentResultInvariants_sound
                                                      hinvariants
                                                  have hnotWriteProp :=
                                                    writeProhibited_false_sound
                                                      hnotWrite
                                                  have htyping :
                                                      TermTyping env.toEnv typing
                                                        lifetime (.assign lhs rhs)
                                                        .unit written.toEnv :=
                                                    TermTyping.assign
                                                      (lvalType?_sound
                                                        hlhsBefore)
                                                      hrhsSound.1
                                                      (assignmentBorrowSafety_sound
                                                        hassignSafe)
                                                      (lvalType?_sound hlhsAfter)
                                                      (shapeCompatiblePartialTy_sound
                                                        hshape)
                                                      (wellFormedTy_sound
                                                        hwellRhs)
                                                      (envWrite?_sound hwrite)
                                                      (rhsBorrowTargetsBelow_sound
                                                        hbelow)
                                                      (envWriteCoherenceObligations_of_checker
                                                        houtside
                                                        hcoherentNonempty
                                                        hrootCoherent hinv.2
                                                        hnotWriteProp)
                                                      hinv.1 hnotWriteProp
                                                  exact checkTermSound_of_typing
                                                    hrefs hwell htyping
                                                · simp [ensure, hnotWrite,
                                                    Bind.bind, Except.bind]
                                                    at hcheck
                                          · simp [ensure, hcontained, hlinear,
                                              Bind.bind, Except.bind] at hcheck
                                        · simp [ensure, hcontained, Bind.bind,
                                            Except.bind] at hcheck
                          · simp [ensure, hOldEq, hLifetimeEq, Bind.bind,
                              Except.bind] at hcheck
                        · simp [ensure, hOldEq, Bind.bind, Except.bind] at hcheck
      | eq lhs rhs =>
          simp [checkTerm?] at hcheck
          cases hlhs : checkTerm? fuel env typing lifetime lhs with
          | error message =>
              simp [hlhs, Bind.bind, Except.bind] at hcheck
          | ok lhsResult =>
              simp [hlhs, Bind.bind, Except.bind] at hcheck
              have hlhsSound := ih hrefs hwell hlhs
              cases hlhsCopy : copyTy lhsResult.ty
              · simp [ensure, hlhsCopy, Bind.bind, Except.bind] at hcheck
              · simp [ensure, hlhsCopy, Bind.bind, Except.bind] at hcheck
                let ghost := freshGhostName lhsResult.env rhs
                cases hghostFresh : lhsResult.env.fresh ghost
                · simp [ghost, ensure, hghostFresh, Bind.bind, Except.bind]
                    at hcheck
                · simp [ghost, ensure, hghostFresh, Bind.bind, Except.bind]
                    at hcheck
                  let ghostEnv :=
                    lhsResult.env.update ghost
                      { ty := .ty lhsResult.ty, lifetime := lifetime }
                  cases hghostKit : wellFormedKit fuel ghostEnv
                  · simp [ghost, ghostEnv, ensure, hghostKit, Bind.bind,
                      Except.bind] at hcheck
                  · simp [ghost, ghostEnv, ensure, hghostKit, Bind.bind,
                      Except.bind] at hcheck
                    have hghostKitSound := wellFormedKit_sound hghostKit
                    have hghostWell : WellFormedEnv ghostEnv.toEnv lifetime :=
                      ⟨hghostKitSound.1,
                        by
                          simpa [ghostEnv, FiniteEnv.toEnv_update] using
                            envSlotsOutlive_update_fresh_current
                              hlhsSound.2.1.2.1
                              (FiniteEnv.fresh_sound hghostFresh),
                        wellFormedKit_coherent_sound hghostKit,
                        hghostKitSound.2.2⟩
                    cases hghost :
                        checkTerm? fuel ghostEnv typing lifetime rhs with
                    | error message =>
                        have hfalse : False := by
                          simpa [ghost, ghostEnv, hghost, Bind.bind,
                            Except.bind, discard, Functor.mapConst,
                            Except.map] using hcheck
                        exact False.elim hfalse
                    | ok ghostResult =>
                        simp [hghost, Bind.bind, Except.bind, discard,
                          Functor.mapConst, Except.map] at hcheck
                        have hghostSound := ih hrefs hghostWell hghost
                        cases hrhs :
                            checkTerm? fuel lhsResult.env typing lifetime rhs with
                        | error message =>
                            have hfalse : False := by
                              simpa [ghost, ghostEnv, hghost, hrhs,
                                Bind.bind, Except.bind, discard,
                                Functor.mapConst, Except.map] using hcheck
                            exact False.elim hfalse
                        | ok rhsResult =>
                            simp [hrhs, Bind.bind, Except.bind] at hcheck
                            have hrhsSound := ih hrefs hlhsSound.2.1 hrhs
                            cases hrhsCopy : copyTy rhsResult.ty
                            · have hfalse : False := by
                                simpa [ghost, ghostEnv, hghost, hrhs,
                                  hrhsCopy, ensure, Bind.bind, Except.bind,
                                  discard, Functor.mapConst, Except.map]
                                  using hcheck
                              exact False.elim hfalse
                            · simp [ensure, hrhsCopy, Bind.bind, Except.bind]
                                at hcheck
                              cases hshape :
                                    shapeCompatiblePartialTy fuel rhsResult.env
                                    (.ty lhsResult.ty) (.ty rhsResult.ty)
                              · have hfalse : False := by
                                  simpa [ghost, ghostEnv, hghost, hrhs,
                                    hrhsCopy, hshape, ensure, Bind.bind,
                                    Except.bind, discard, Functor.mapConst,
                                    Except.map] using hcheck
                                exact False.elim hfalse
                              · simp [ensure, hshape, Bind.bind, Except.bind]
                                  at hcheck
                                have hresultOk :
                                    (Except.ok
                                        { ty := Ty.bool, env := rhsResult.env } :
                                      Except String CheckResult) =
                                      Except.ok result := by
                                  simpa [ghost, ghostEnv, hghost, hrhs,
                                    hrhsCopy, hshape, ensure, Bind.bind,
                                    Except.bind, discard, Functor.mapConst,
                                    Except.map] using hcheck
                                have hresult :
                                    result =
                                      { ty := Ty.bool, env := rhsResult.env } :=
                                  (Except.ok.inj hresultOk).symm
                                cases hresult
                                have htyping :
                                    TermTyping env.toEnv typing lifetime
                                      (.eq lhs rhs) .bool rhsResult.env.toEnv :=
                                  TermTyping.eq (ghost := ghost) hlhsSound.1
                                    (FiniteEnv.fresh_sound hghostFresh)
                                    (by
                                      simpa [ghostEnv, FiniteEnv.toEnv_update]
                                        using hghostSound.1)
                                    hrhsSound.1 (copyTy_sound hlhsCopy)
                                    (copyTy_sound hrhsCopy)
                                    (shapeCompatiblePartialTy_sound hshape)
                                exact checkTermSound_of_typing hrefs hwell
                                  htyping
      | ite condition trueBranch falseBranch =>
          simp [checkTerm?] at hcheck
          cases hcondition :
              checkTerm? fuel env typing lifetime condition with
          | error message =>
              simp [hcondition, Bind.bind, Except.bind] at hcheck
          | ok conditionResult =>
              simp [hcondition, Bind.bind, Except.bind] at hcheck
              have hconditionSound := ih hrefs hwell hcondition
              by_cases hconditionTy : conditionResult.ty = .bool
              · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck
                cases htrue :
                    checkTerm? fuel conditionResult.env typing lifetime
                      trueBranch with
                | error message =>
                    simp [htrue, Bind.bind, Except.bind] at hcheck
                | ok thenResult =>
                    simp [htrue, Bind.bind, Except.bind] at hcheck
                    have hthenSound := ih hrefs hconditionSound.2.1 htrue
                    cases hfalse :
                        checkTerm? fuel conditionResult.env typing lifetime
                          falseBranch with
                    | error message =>
                        simp [hfalse, Bind.bind, Except.bind] at hcheck
                    | ok falseResult =>
                        simp [hfalse, Bind.bind, Except.bind] at hcheck
                        have hfalseSound := ih hrefs hconditionSound.2.1 hfalse
                        cases hjoinTy :
                            partialTyJoin? (.ty (CheckResult.ty thenResult))
                              (.ty falseResult.ty) with
                        | none =>
                            simp [hjoinTy] at hcheck
                            cases hdiv : termDiverges falseBranch
                            · simp [hdiv] at hcheck
                            · simp [hdiv] at hcheck
                              have htyping :
                                  TermTyping env.toEnv typing lifetime
                                    (.ite condition trueBranch falseBranch)
                                    (CheckResult.ty thenResult)
                                    (CheckResult.env thenResult).toEnv :=
                                TermTyping.iteDiverging
                                  (by simpa [hconditionTy] using
                                    hconditionSound.1)
                                  hthenSound.1 hfalseSound.1
                                  (termDiverges_sound hdiv)
                              cases hcheck
                              exact checkTermSound_of_typing hrefs hwell
                                htyping
                        | some joinPartial =>
                            cases joinPartial with
                            | ty joinTy =>
                                cases hjoinEnv :
                                    envJoin? (CheckResult.env thenResult)
                                      falseResult.env with
                                | none =>
                                    simp [hjoinTy, hjoinEnv] at hcheck
                                    cases hdiv : termDiverges falseBranch
                                    · simp [hdiv] at hcheck
                                    · simp [hdiv] at hcheck
                                      have htyping :
                                          TermTyping env.toEnv typing lifetime
                                            (.ite condition trueBranch
                                              falseBranch)
                                            (CheckResult.ty thenResult)
                                            (CheckResult.env thenResult).toEnv :=
                                        TermTyping.iteDiverging
                                          (by simpa [hconditionTy] using
                                            hconditionSound.1)
                                          hthenSound.1 hfalseSound.1
                                          (termDiverges_sound hdiv)
                                      cases hcheck
                                      exact checkTermSound_of_typing hrefs
                                        hwell htyping
                                | some joinEnv =>
                                    simp [hjoinTy, hjoinEnv] at hcheck
                                    cases hthenShape :
                                        envJoinSameShape
                                          (CheckResult.env thenResult) joinEnv
                                    · simp [ensure, hthenShape, Bind.bind,
                                        Except.bind] at hcheck
                                    · simp [ensure, hthenShape, Bind.bind,
                                        Except.bind] at hcheck
                                      cases hfalseShape :
                                          envJoinSameShape falseResult.env
                                            joinEnv
                                      · simp [ensure, hfalseShape, Bind.bind,
                                          Except.bind] at hcheck
                                      · simp [ensure, hfalseShape, Bind.bind,
                                          Except.bind] at hcheck
                                        cases hwellJoin :
                                            wellFormedTy fuel joinEnv joinTy
                                              lifetime
                                        · simp [ensure, hwellJoin, Bind.bind,
                                            Except.bind] at hcheck
                                        · simp [ensure, hwellJoin, Bind.bind,
                                            Except.bind] at hcheck
                                          cases hkit :
                                              wellFormedKit fuel joinEnv
                                          · simp [ensure, hkit, Bind.bind,
                                              Except.bind] at hcheck
                                          · simp [ensure, hkit, Bind.bind,
                                              Except.bind] at hcheck
                                            cases htySafe :
                                                tyBorrowSafeAgainstEnv joinEnv
                                                  joinTy
                                            · simp [htySafe] at hcheck
                                            · simp [htySafe] at hcheck
                                              cases hcheck
                                              have hkitSound :=
                                                wellFormedKit_sound hkit
                                              have htyping :
                                                  TermTyping env.toEnv typing
                                                    lifetime
                                                    (.ite condition trueBranch
                                                      falseBranch)
                                                    joinTy joinEnv.toEnv :=
                                                TermTyping.ite
                                                  (by simpa [hconditionTy]
                                                    using hconditionSound.1)
                                                  hthenSound.1 hfalseSound.1
                                                  (partialTyJoin?_sound
                                                    hjoinTy)
                                                  (envJoin?_sound hjoinEnv)
                                                  (envJoinSameShape_sound
                                                    hthenShape)
                                                  (envJoinSameShape_sound
                                                    hfalseShape)
                                                  (wellFormedTy_sound
                                                    hwellJoin)
                                                  hkitSound.1
                                                  (wellFormedKit_coherent_sound
                                                    hkit)
                                                  hkitSound.2.2
                                                  (tyBorrowSafeAgainstEnv_sound
                                                    htySafe)
                                              exact checkTermSound_of_typing
                                                hrefs hwell htyping
                            | box _ =>
                                simp [hjoinTy] at hcheck
                                cases hdiv : termDiverges falseBranch
                                · simp [hdiv] at hcheck
                                · simp [hdiv] at hcheck
                                  have htyping :
                                      TermTyping env.toEnv typing lifetime
                                        (.ite condition trueBranch falseBranch)
                                        (CheckResult.ty thenResult)
                                        (CheckResult.env thenResult).toEnv :=
                                    TermTyping.iteDiverging
                                      (by simpa [hconditionTy] using
                                        hconditionSound.1)
                                      hthenSound.1 hfalseSound.1
                                      (termDiverges_sound hdiv)
                                  cases hcheck
                                  exact checkTermSound_of_typing hrefs hwell
                                    htyping
                            | undef _ =>
                                simp [hjoinTy] at hcheck
                                cases hdiv : termDiverges falseBranch
                                · simp [hdiv] at hcheck
                                · simp [hdiv] at hcheck
                                  have htyping :
                                      TermTyping env.toEnv typing lifetime
                                        (.ite condition trueBranch falseBranch)
                                        (CheckResult.ty thenResult)
                                        (CheckResult.env thenResult).toEnv :=
                                    TermTyping.iteDiverging
                                      (by simpa [hconditionTy] using
                                        hconditionSound.1)
                                      hthenSound.1 hfalseSound.1
                                      (termDiverges_sound hdiv)
                                  cases hcheck
                                  exact checkTermSound_of_typing hrefs hwell
                                    htyping
              · simp [ensure, hconditionTy] at hcheck
      | whileLoop bodyLifetime condition body =>
          have hwhile :
              checkWhile? fuel env typing lifetime bodyLifetime condition body =
                .ok result := by
            simpa [checkTerm?] using hcheck
          exact checkWhile?_sound_of_termSound ih hrefs hwell hwhile
      | whileCond bodyLifetime conditionInFlight condition body =>
          simp [checkTerm?] at hcheck
      | whileBody bodyLifetime bodyInFlight condition body =>
          simp [checkTerm?] at hcheck

theorem checkTerm?_sound {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {result : CheckResult} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTerm? fuel env typing lifetime term = .ok result →
          TermTyping env.toEnv typing lifetime term result.ty
            result.env.toEnv := by
  intro hrefs hwell hcheck
  have hrefsChecker :
      ∀ env lifetime,
        CheckerStoreTypingRefsWellFormed env typing lifetime := by
    intro env lifetime ref ty hlookup
    exact hrefs env lifetime ref ty hlookup
  exact (checkTerm?_sound_at fuel hrefsChecker hwell hcheck).1

theorem checkTermList?_sound {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {terms : List Term}
    {result : CheckResult} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermList? fuel env typing lifetime terms = .ok result →
          TermListTyping env.toEnv typing lifetime terms result.ty
            result.env.toEnv := by
  intro hrefs hwell hcheck
  have hrefsChecker :
      ∀ env lifetime,
        CheckerStoreTypingRefsWellFormed env typing lifetime := by
    intro env lifetime ref ty hlookup
    exact hrefs env lifetime ref ty hlookup
  exact (checkTermList?_sound_of_termSound (checkTerm?_sound_at fuel)
    hrefsChecker hwell hcheck).1

theorem termTyping_of_checkTermMatches? {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv =
          true →
          TermTyping env.toEnv typing lifetime term expectedTy
            expectedEnv.toEnv := by
  intro hrefs hwell hmatches
  unfold checkTermMatches? at hmatches
  cases hcheck : checkTerm? fuel env typing lifetime term with
  | error message =>
      simp [hcheck] at hmatches
  | ok result =>
      simp [hcheck] at hmatches
      have htyping := checkTerm?_sound hrefs hwell hcheck
      have hmatch := checkResult_matches_sound hmatches
      rw [hmatch.1, hmatch.2] at htyping
      exact htyping

theorem termListTyping_of_checkTermListMatches? {fuel : Nat}
    {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {terms : List Term} {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermListMatches? fuel env typing lifetime terms expectedTy
          expectedEnv = true →
          TermListTyping env.toEnv typing lifetime terms expectedTy
            expectedEnv.toEnv := by
  intro hrefs hwell hmatches
  unfold checkTermListMatches? at hmatches
  cases hcheck : checkTermList? fuel env typing lifetime terms with
  | error message =>
      simp [hcheck] at hmatches
  | ok result =>
      simp [hcheck] at hmatches
      have htyping := checkTermList?_sound hrefs hwell hcheck
      have hmatch := checkResult_matches_sound hmatches
      rw [hmatch.1, hmatch.2] at htyping
      exact htyping

theorem checkedTermTypingWitness_of_checkTermMatches? {fuel : Nat}
    {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv =
          true →
          CheckedTermTypingWitness fuel env typing lifetime term expectedTy
            expectedEnv := by
  intro hrefs hwell hmatches
  exact ⟨hmatches, termTyping_of_checkTermMatches? hrefs hwell hmatches⟩

theorem certifiedTermCheck_of_checkTermMatches? {fuel : Nat}
    {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv =
          true →
          Nonempty
            (CertifiedTermCheck fuel env typing lifetime term expectedTy
              expectedEnv) := by
  intro hrefs hwell hmatches
  exact ⟨
    { checked := hmatches
      typing := termTyping_of_checkTermMatches? hrefs hwell hmatches }⟩

theorem checkProgram?_sound {fuel : Nat} {term : Term} {result : CheckResult} :
    checkProgram? fuel term = .ok result →
      TermTyping Env.empty StoreTyping.empty Lifetime.root term result.ty
        result.env.toEnv := by
  intro hcheck
  have hrefs :
      ∀ env lifetime,
        StoreTypingRefsWellFormed env StoreTyping.empty lifetime := by
    intro env lifetime
    exact storeTypingRefsWellFormed_empty env lifetime
  exact checkTerm?_sound
      (env := FiniteEnv.empty) (typing := StoreTyping.empty)
      (lifetime := Lifetime.root) (term := term) (result := result)
      hrefs
      (by
        simp [FiniteEnv.toEnv_empty, wellFormedEnv_empty])
      (by simpa [checkProgram?] using hcheck)

theorem termTyping_of_checkProgram?_matches {fuel : Nat} {term : Term}
    {result : CheckResult} {ty : Ty} {env : Env} :
    checkProgram? fuel term = .ok result →
      result.ty = ty →
        result.env.toEnv = env →
          TermTyping Env.empty StoreTyping.empty Lifetime.root term ty env := by
  intro hcheck hty henv
  have htyping := checkProgram?_sound hcheck
  rw [hty, henv] at htyping
  exact htyping

/--
Executable proof-carrying accepted checker.

When `checkProgram?` accepts, this returns the successful checker run packaged
with the corresponding declarative typing derivation.  When the checker returns
`.failed` or `.unknown`, no accepted-run certificate is produced.
-/
def certifyBorrowCheck? (fuel : Nat) (term : Term) :
    Option (CertifiedBorrowCheck fuel term) :=
  match hcheck : checkProgram? fuel term with
  | .ok result =>
      some
        { ty := result.ty
          env := result.env
          certificate :=
            { checked := by
                have hterm :
                    checkTerm? fuel FiniteEnv.empty StoreTyping.empty
                      Lifetime.root term = .ok result := by
                  simpa [checkProgram?] using hcheck
                unfold checkTermMatches? CheckResult.matches
                rw [hterm]
                simp [FiniteEnv.sameBindings_self]
              typing := by
                simpa [FiniteEnv.toEnv_empty] using checkProgram?_sound hcheck } }
  | .error _ => none

theorem certifyBorrowCheck?_found_iff {fuel : Nat} {term : Term} :
    CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = true ↔
      borrowCheck? fuel term = true := by
  unfold CertifiedBorrowCheck.found? certifyBorrowCheck? borrowCheck?
    borrowCheckVerdict?
  split
  · rename_i result hcheck
    simp [hcheck]
  · rename_i message hcheck
    cases hunknown : checkerErrorUnknown? message <;>
      simp [hcheck, hunknown]

/--
Proof-level reflection target for the executable accepted checker.

`borrowCheckWitness fuel term` means that the successful executable run has
been reified as a `CertifiedBorrowCheck`, i.e. as both a checker trace and the
corresponding inductive typing derivation.
-/
def borrowCheckWitness (fuel : Nat) (term : Term) : Prop :=
  Nonempty (CertifiedBorrowCheck fuel term)

theorem borrowCheck?_eq_true_iff_witness {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true ↔ borrowCheckWitness fuel term := by
  constructor
  · intro hcheck
    have hfound :
        CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = true :=
      (certifyBorrowCheck?_found_iff).2 hcheck
    unfold CertifiedBorrowCheck.found? at hfound
    cases hcert : certifyBorrowCheck? fuel term with
    | none =>
        simp [hcert] at hfound
    | some certificate =>
        exact ⟨certificate⟩
  · intro hwitness
    rcases hwitness with ⟨certificate⟩
    exact certificate.checked

theorem borrowCheck?_eq_false_iff_no_witness {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = false ↔ ¬ borrowCheckWitness fuel term := by
  constructor
  · intro hfalse hwitness
    have htrue := (borrowCheck?_eq_true_iff_witness).2 hwitness
    rw [hfalse] at htrue
    cases htrue
  · intro hnoWitness
    cases hcheck : borrowCheck? fuel term
    · rfl
    · exact False.elim
        (hnoWitness ((borrowCheck?_eq_true_iff_witness).1 hcheck))

theorem borrowCheckWitness_sound {fuel : Nat} {term : Term} :
    borrowCheckWitness fuel term → borrowCheck term := by
  intro hwitness
  rcases hwitness with ⟨certificate⟩
  exact certificate.borrowCheck

theorem borrowReject_no_borrowCheckWitness {fuel : Nat} {term : Term} :
    borrowReject term → ¬ borrowCheckWitness fuel term := by
  intro hreject hwitness
  exact hreject (borrowCheckWitness_sound hwitness)

theorem borrowReject_no_borrowCheckWitness_anyFuel {term : Term} :
    borrowReject term → ∀ fuel, ¬ borrowCheckWitness fuel term := by
  intro hreject fuel
  exact borrowReject_no_borrowCheckWitness (fuel := fuel) hreject

theorem borrowCheck?_eq_false_of_borrowReject {fuel : Nat} {term : Term} :
    borrowReject term → borrowCheck? fuel term = false := by
  intro hreject
  exact (borrowCheck?_eq_false_iff_no_witness).2
    (borrowReject_no_borrowCheckWitness (fuel := fuel) hreject)

theorem borrowCheckWitness_checked {fuel : Nat} {term : Term} :
    borrowCheckWitness fuel term → borrowCheck? fuel term = true := by
  intro hwitness
  exact (borrowCheck?_eq_true_iff_witness).2 hwitness

theorem borrowCheckFailureWitness_no_borrowCheckWitness
    {fuel : Nat} {term : Term} :
    borrowCheckFailureWitness fuel term →
      ¬ borrowCheckWitness fuel term := by
  intro hfailure haccepted
  have hfailed := borrowCheckFailureWitness_checked hfailure
  have hcheck := borrowCheckWitness_checked haccepted
  have hnotFailed := borrowCheckFailed?_false_of_borrowCheck? hcheck
  rw [hfailed] at hnotFailed
  cases hnotFailed

theorem borrowUnknownWitness_no_borrowCheckWitness
    {fuel : Nat} {term : Term} :
    borrowUnknownWitness fuel term →
      ¬ borrowCheckWitness fuel term := by
  intro hunknown haccepted
  have hunknownChecked := borrowUnknownWitness_checked hunknown
  have hcheck := borrowCheckWitness_checked haccepted
  have hnotUnknown := borrowUnknown?_false_of_borrowCheck? hcheck
  rw [hunknownChecked] at hnotUnknown
  cases hnotUnknown

theorem borrowCheck_of_certifyBorrowCheck? {fuel : Nat} {term : Term} :
    CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = true →
      borrowCheck term := by
  exact CertifiedBorrowCheck.borrowCheck_of_found?
    (certificate? := certifyBorrowCheck? fuel term)

theorem borrowCheck_of_borrowCheck? {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true → borrowCheck term := by
  exact borrowCheck_of_checkProgram?_sound
    (fun result hresult => checkProgram?_sound hresult)

theorem borrowCheck?_sound {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true → borrowCheck term :=
  borrowCheck_of_borrowCheck?

theorem borrowCheck_of_borrowCheckVerdict?_accepted {fuel : Nat} {term : Term} :
    borrowCheckVerdict? fuel term = .accepted → borrowCheck term := by
  intro hverdict
  apply borrowCheck?_sound
  simpa [borrowCheck?] using congrArg
    (fun verdict =>
      match verdict with
      | BorrowCheckVerdict.accepted => true
      | BorrowCheckVerdict.failed => false
      | BorrowCheckVerdict.unknown => false)
    hverdict

/--
Proof-carrying closed-program checker outcome.

An `accepted` outcome carries the executable successful run and its inductive
typing proof.  A `rejected` outcome carries both an executable failure and an
inductive no-typing proof.  Plain `.failed` checker verdicts are intentionally
not promoted to this type: they need a `CertifiedBorrowReject` witness first.
-/
inductive CertifiedBorrowOutcome (fuel : Nat) (term : Term) : Type where
  | accepted (certificate : CertifiedBorrowCheck fuel term)
  | rejected (certificate : CertifiedBorrowReject fuel term)

namespace CertifiedBorrowOutcome

def found? {fuel : Nat} {term : Term}
    (outcome? : Option (CertifiedBorrowOutcome fuel term)) : Bool :=
  outcome?.isSome

def certifyBorrowOutcome? (fuel : Nat) (term : Term)
    (rejection? : Option (CertifiedBorrowReject fuel term) := none) :
    Option (CertifiedBorrowOutcome fuel term) :=
  match certifyBorrowCheck? fuel term with
  | some certificate => some (.accepted certificate)
  | none =>
      match rejection? with
      | some certificate => some (.rejected certificate)
      | none => none

theorem sound {fuel : Nat} {term : Term}
    (outcome : CertifiedBorrowOutcome fuel term) :
    borrowCheck term ∨ borrowReject term := by
  cases outcome with
  | accepted certificate =>
      exact Or.inl certificate.borrowCheck
  | rejected certificate =>
      exact Or.inr certificate.borrowReject

theorem checked {fuel : Nat} {term : Term}
    (outcome : CertifiedBorrowOutcome fuel term) :
    borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true := by
  cases outcome with
  | accepted certificate =>
      exact Or.inl certificate.checked
  | rejected certificate =>
      exact Or.inr certificate.checkedFailure

theorem sound_of_found? {fuel : Nat} {term : Term}
    {outcome? : Option (CertifiedBorrowOutcome fuel term)} :
    found? outcome? = true → borrowCheck term ∨ borrowReject term := by
  cases outcome? with
  | none =>
      simp [found?]
  | some outcome =>
      intro _h
      exact outcome.sound

theorem checked_of_found? {fuel : Nat} {term : Term}
    {outcome? : Option (CertifiedBorrowOutcome fuel term)} :
    found? outcome? = true →
      borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true := by
  cases outcome? with
  | none =>
      simp [found?]
  | some outcome =>
      intro _h
      exact outcome.checked

theorem found_of_borrowCheck? {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowCheck? fuel term = true →
      found? (certifyBorrowOutcome? fuel term rejection?) = true := by
  intro hcheck
  have hcert :
      CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = true :=
    (certifyBorrowCheck?_found_iff).2 hcheck
  unfold found? certifyBorrowOutcome?
  cases hcertificate : certifyBorrowCheck? fuel term with
  | none =>
      have hnotFound :
          CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = false := by
        simp [CertifiedBorrowCheck.found?, hcertificate]
      rw [hnotFound] at hcert
      cases hcert
  | some certificate =>
      simp

theorem sound_of_certifyBorrowOutcome? {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    found? (certifyBorrowOutcome? fuel term rejection?) = true →
      borrowCheck term ∨ borrowReject term :=
  sound_of_found?

theorem checked_of_certifyBorrowOutcome? {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    found? (certifyBorrowOutcome? fuel term rejection?) = true →
      borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true :=
  checked_of_found?

end CertifiedBorrowOutcome

/--
Executable found/not-found bit for proof-carrying borrow-checking outcomes.

With no rejection certificate, this is the accepted-checker witness bit.  With a
`CertifiedBorrowReject`, it can also return true for a proof-carrying rejection.
Either way, `borrowOutcome?_sound` turns a true bit into an inductive fact.
-/
def borrowOutcome? (fuel : Nat) (term : Term)
    (rejection? : Option (CertifiedBorrowReject fuel term) := none) : Bool :=
  CertifiedBorrowOutcome.found?
    (CertifiedBorrowOutcome.certifyBorrowOutcome? fuel term rejection?)

/--
Proof-level reflection target for `borrowOutcome?`.

Unlike `CertifiedBorrowOutcome` by itself, this records that the executable
outcome function actually returned the witness, using the optional rejection
certificate supplied by the caller.
-/
def borrowOutcomeWitness (fuel : Nat) (term : Term)
    (rejection? : Option (CertifiedBorrowReject fuel term) := none) : Prop :=
  ∃ outcome,
    CertifiedBorrowOutcome.certifyBorrowOutcome? fuel term rejection? =
      some outcome

theorem borrowOutcome?_eq_true_iff_witness {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcome? fuel term rejection? = true ↔
      borrowOutcomeWitness fuel term rejection? := by
  unfold borrowOutcome? borrowOutcomeWitness CertifiedBorrowOutcome.found?
  cases hcert :
      CertifiedBorrowOutcome.certifyBorrowOutcome? fuel term rejection? with
  | none =>
      simp
  | some outcome =>
      simp

theorem borrowOutcome?_eq_false_iff_no_witness {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcome? fuel term rejection? = false ↔
      ¬ borrowOutcomeWitness fuel term rejection? := by
  constructor
  · intro hfalse hwitness
    have htrue := (borrowOutcome?_eq_true_iff_witness).2 hwitness
    rw [hfalse] at htrue
    cases htrue
  · intro hnoWitness
    cases hcheck : borrowOutcome? fuel term rejection?
    · rfl
    · exact False.elim
        (hnoWitness ((borrowOutcome?_eq_true_iff_witness).1 hcheck))

theorem borrowOutcomeWitness_sound {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcomeWitness fuel term rejection? →
      borrowCheck term ∨ borrowReject term := by
  rintro ⟨outcome, _houtcome⟩
  exact outcome.sound

theorem borrowOutcomeWitness_checked {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcomeWitness fuel term rejection? →
      borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true := by
  rintro ⟨outcome, _houtcome⟩
  exact outcome.checked

theorem borrowOutcome?_sound {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcome? fuel term rejection? = true →
      borrowCheck term ∨ borrowReject term := by
  intro hfound
  exact CertifiedBorrowOutcome.sound_of_certifyBorrowOutcome?
    (rejection? := rejection?) (by simpa [borrowOutcome?] using hfound)

theorem borrowOutcome?_checked {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcome? fuel term rejection? = true →
      borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true := by
  intro hfound
  exact CertifiedBorrowOutcome.checked_of_certifyBorrowOutcome?
    (rejection? := rejection?) (by simpa [borrowOutcome?] using hfound)

theorem borrowOutcome?_of_borrowCheck? {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowCheck? fuel term = true → borrowOutcome? fuel term rejection? = true := by
  intro hcheck
  exact CertifiedBorrowOutcome.found_of_borrowCheck?
    (rejection? := rejection?) hcheck

theorem borrowOutcome?_of_certifiedCheck {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)}
    (certificate : CertifiedBorrowCheck fuel term) :
    borrowOutcome? fuel term rejection? = true :=
  borrowOutcome?_of_borrowCheck? certificate.checked

theorem borrowOutcome?_of_certifiedReject {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowReject fuel term) :
    borrowOutcome? fuel term (some certificate) = true := by
  unfold borrowOutcome? CertifiedBorrowOutcome.found?
    CertifiedBorrowOutcome.certifyBorrowOutcome?
  cases certifyBorrowCheck? fuel term <;> simp

theorem borrowOutcome?_none_eq_true_iff {fuel : Nat} {term : Term} :
    borrowOutcome? fuel term = true ↔ borrowCheck? fuel term = true := by
  constructor
  · intro hfound
    unfold borrowOutcome? CertifiedBorrowOutcome.found?
      CertifiedBorrowOutcome.certifyBorrowOutcome? at hfound
    cases hcert : certifyBorrowCheck? fuel term with
    | none =>
        simp [hcert] at hfound
    | some certificate =>
        exact certificate.checked
  · exact borrowOutcome?_of_borrowCheck?

theorem borrowCheck_of_borrowOutcome? {fuel : Nat} {term : Term} :
    borrowOutcome? fuel term = true → borrowCheck term := by
  intro hfound
  exact borrowCheck?_sound ((borrowOutcome?_none_eq_true_iff).1 hfound)

theorem borrowCheck_of_borrowOutcomeWitness {fuel : Nat} {term : Term} :
    borrowOutcomeWitness fuel term → borrowCheck term := by
  intro hwitness
  exact borrowCheck_of_borrowOutcome?
    ((borrowOutcome?_eq_true_iff_witness).2 hwitness)

macro_rules
  | `(tactic| borrow_check using $certificate) =>
      `(tactic|
        first
        | exact LwRust.Paper.borrowOutcome?_of_certifiedCheck $certificate
        | exact LwRust.Paper.borrowOutcome?_of_certifiedReject $certificate
        | exact (LwRust.Paper.borrowCheck?_eq_true_iff_witness).1
            (LwRust.Paper.CertifiedBorrowCheck.checked $certificate)
        | exact (LwRust.Paper.borrowOutcome?_eq_true_iff_witness).1
            (LwRust.Paper.borrowOutcome?_of_certifiedCheck $certificate)
        | exact (LwRust.Paper.borrowOutcome?_eq_true_iff_witness).1
            (LwRust.Paper.borrowOutcome?_of_certifiedReject $certificate)
        | exact LwRust.Paper.CertifiedBorrowCheck.borrowCheck $certificate
        | exact LwRust.Paper.CertifiedBorrowCheck.checked $certificate
        | exact LwRust.Paper.CertifiedBorrowCheck.borrowCheck_of_found?
            (certificate? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowCheck.checked_of_found?
            (certificate? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowReject.borrowReject $certificate
        | exact LwRust.Paper.CertifiedBorrowReject.checkedFailure $certificate
        | exact LwRust.Paper.CertifiedBorrowReject.borrowReject_of_found?
            (certificate? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowReject.checkedFailure_of_found?
            (certificate? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowOutcome.sound $certificate
        | exact LwRust.Paper.CertifiedBorrowOutcome.checked $certificate
        | exact LwRust.Paper.CertifiedBorrowOutcome.sound_of_found?
            (outcome? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowOutcome.checked_of_found?
            (outcome? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedTermCheck.sound $certificate
        | exact LwRust.Paper.CertifiedTermCheck.toWitness $certificate
        | exact LwRust.Paper.CertifiedTermCheck.check_matches $certificate
        | exact LwRust.Paper.CertifiedTermCheck.typable $certificate
        | exact LwRust.Paper.CertifiedTermListCheck.sound $certificate
        | exact LwRust.Paper.CertifiedTermReject.sound $certificate
        | exact LwRust.Paper.CertifiedTermReject.checkedFailure $certificate
        | exact $certificate)

macro_rules
  | `(tactic| borrow_check[$fuel, $env, $expectedEnv]) =>
      `(tactic|
        first
        | exact LwRust.Paper.termTyping_of_checkTermMatches?
            (fuel := $fuel) (env := $env) (expectedEnv := $expectedEnv)
            (fun env lifetime =>
              LwRust.Paper.storeTypingRefsWellFormed_empty env lifetime)
            (by
              first
              | simp [LwRust.Paper.FiniteEnv.toEnv_empty,
                  LwRust.Paper.wellFormedEnv_empty]
              | native_decide)
            (by native_decide)
        | exact LwRust.Paper.termListTyping_of_checkTermListMatches?
            (fuel := $fuel) (env := $env) (expectedEnv := $expectedEnv)
            (fun env lifetime =>
              LwRust.Paper.storeTypingRefsWellFormed_empty env lifetime)
            (by
              first
              | simp [LwRust.Paper.FiniteEnv.toEnv_empty,
                  LwRust.Paper.wellFormedEnv_empty]
              | native_decide)
            (by native_decide))

macro_rules
  | `(tactic| borrow_check[$fuel, $result]) =>
      `(tactic|
        first
        | exact LwRust.Paper.termTyping_of_checkProgram?_matches
            (fuel := $fuel) (result := $result)
            (by native_decide) (by native_decide)
            (by simp [LwRust.Paper.FiniteEnv.toEnv_empty])
        | borrow_check[$fuel])

macro_rules
  | `(tactic| borrow_check[$fuel]) =>
      `(tactic|
        first
        | exact LwRust.Paper.borrowCheck_of_certifyBorrowCheck?
            (fuel := $fuel) (by native_decide)
        | exact LwRust.Paper.borrowCheck?_sound
            (fuel := $fuel) (by native_decide)
        | exact (LwRust.Paper.borrowCheck?_eq_true_iff_witness
            (fuel := $fuel)).1 (by native_decide)
        | exact (LwRust.Paper.borrowOutcome?_eq_true_iff_witness
            (fuel := $fuel)).1 (by native_decide)
        | exact LwRust.Paper.borrowCheckFailureWitness_of_certifyBorrowFailure?
            (fuel := $fuel) (by native_decide)
        | exact LwRust.Paper.borrowUnknownWitness_of_certifyBorrowUnknown?
            (fuel := $fuel) (by native_decide)
        | exact LwRust.Paper.borrowCheckFailureWitness_no_borrowCheckWitness
            ((LwRust.Paper.borrowCheckFailed?_eq_true_iff_witness
              (fuel := $fuel)).1 (by native_decide))
        | exact LwRust.Paper.borrowUnknownWitness_no_borrowCheckWitness
            ((LwRust.Paper.borrowUnknown?_eq_true_iff_witness
              (fuel := $fuel)).1 (by native_decide))
        | exact (LwRust.Paper.borrowCheck?_eq_false_iff_no_witness
            (fuel := $fuel)).1 (by native_decide)
        | exact (LwRust.Paper.borrowOutcome?_eq_false_iff_no_witness
            (fuel := $fuel)).1 (by native_decide)
        | borrow_run)

macro_rules
  | `(tactic| borrow_check) =>
      `(tactic|
        first
        | exact LwRust.Paper.borrowCheck_of_certifyBorrowCheck?
            (fuel := 256) (by native_decide)
        | exact LwRust.Paper.borrowCheck?_sound
            (fuel := 256) (by native_decide)
        | exact (LwRust.Paper.borrowCheck?_eq_true_iff_witness
            (fuel := 256)).1 (by native_decide)
        | exact (LwRust.Paper.borrowOutcome?_eq_true_iff_witness
            (fuel := 256)).1 (by native_decide)
        | exact LwRust.Paper.borrowCheckFailureWitness_of_certifyBorrowFailure?
            (fuel := 256) (by native_decide)
        | exact LwRust.Paper.borrowUnknownWitness_of_certifyBorrowUnknown?
            (fuel := 256) (by native_decide)
        | exact LwRust.Paper.borrowCheckFailureWitness_no_borrowCheckWitness
            ((LwRust.Paper.borrowCheckFailed?_eq_true_iff_witness
              (fuel := 256)).1 (by native_decide))
        | exact LwRust.Paper.borrowUnknownWitness_no_borrowCheckWitness
            ((LwRust.Paper.borrowUnknown?_eq_true_iff_witness
              (fuel := 256)).1 (by native_decide))
        | exact (LwRust.Paper.borrowCheck?_eq_false_iff_no_witness
            (fuel := 256)).1 (by native_decide)
        | exact (LwRust.Paper.borrowOutcome?_eq_false_iff_no_witness
            (fuel := 256)).1 (by native_decide)
        | borrow_run)

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
