import LwRust.Paper.BorrowChecker.Inductive

/-!
Executable borrow/type checker for the finite fragment used by examples.
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

theorem lookupEntries_filter_update_ne
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

theorem lookupEntries_filter_congr_for_name
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

theorem lookupEntries_filter_none_of_name_false
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

theorem lookupEntries_dropLifetime_filter
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

def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def fromOption (message : String) : Option α → Except String α
  | some value => .ok value
  | none => .error message

def insertName (names : List Name) (name : Name) : List Name :=
  if names.contains name then names else names ++ [name]

def unionNames (left right : List Name) : List Name :=
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

def lvalMem (target : LVal) : List LVal → Bool
  | [] => false
  | head :: rest =>
      if target = head then true else lvalMem target rest

theorem lvalMem_true_iff {target : LVal} {targets : List LVal} :
    lvalMem target targets = true ↔ target ∈ targets := by
  induction targets with
  | nil =>
      simp [lvalMem]
  | cons head rest ih =>
      by_cases heq : target = head
      · subst heq
        simp [lvalMem]
      · simp [lvalMem, heq, ih]

def insertLVal (targets : List LVal) (target : LVal) : List LVal :=
  if lvalMem target targets then targets else targets ++ [target]

def unionLVals (left right : List LVal) : List LVal :=
  right.foldl insertLVal left

theorem mem_insertLVal {candidate target : LVal}
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

theorem mem_unionLVals {candidate : LVal}
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

def lvalNames : LVal → List Name
  | .var name => [name]
  | .deref lv => lvalNames lv

mutual
  def tyNames : Ty → List Name
    | .unit => []
    | .int => []
    | .bool => []
    | .borrow _ targets =>
        targets.foldl (fun names target => unionNames names (lvalNames target)) []
    | .box ty => tyNames ty

  def partialTyNames : PartialTy → List Name
    | .ty ty => tyNames ty
    | .box ty => partialTyNames ty
    | .undef _ => []
end

def termNames : Term → List Name
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

def envNames (env : FiniteEnv) : List Name :=
  env.entries.foldl
    (fun names entry => unionNames (insertName names entry.1) (partialTyNames entry.2.ty))
    []

def envEqOnSupport (left right : FiniteEnv) : Bool :=
  left.sameBindings right

def envEqOutside (left right : FiniteEnv) (exceptName : Name) : Bool :=
  let names := unionNames left.support right.support
  names.all (fun name =>
    if name = exceptName then true
    else if left.lookup name = right.lookup name then true else false)

private partial def freshNameFrom (used : List Name) (fuel : Nat) : Name :=
  let candidate := "_γ" ++ toString fuel
  if used.contains candidate then freshNameFrom used (fuel + 1) else candidate

def freshGhostName (env : FiniteEnv) (term : Term) : Name :=
  freshNameFrom (unionNames (envNames env) (termNames term)) 0

def copyTy : Ty → Bool
  | .unit => true
  | .int => true
  | .bool => true
  | .borrow false _ => true
  | _ => false

mutual
  def tyLoanFree : Ty → Bool
    | .unit => true
    | .int => true
    | .bool => true
    | .borrow _ targets => targets.isEmpty
    | .box ty => tyLoanFree ty

  def partialTyLoanFree : PartialTy → Bool
    | .ty ty => tyLoanFree ty
    | .box ty => partialTyLoanFree ty
    | .undef _ => true
end

mutual
  def tyBorrows : Ty → List (Bool × List LVal)
    | .unit => []
    | .int => []
    | .bool => []
    | .borrow mutable targets => [(mutable, targets)]
    | .box ty => tyBorrows ty

  def partialTyBorrows : PartialTy → List (Bool × List LVal)
    | .ty ty => tyBorrows ty
    | .box ty => partialTyBorrows ty
    | .undef _ => []
end

def partialTyContainsBorrow
    (partialTy : PartialTy) (mutable : Bool) (targets : List LVal) : Bool :=
  (partialTyBorrows partialTy).any
    (fun borrow => borrow.1 == mutable && borrow.2 == targets)

def pathConflicts (left right : LVal) : Bool :=
  LVal.base left == LVal.base right

def envBorrowEdges (env : FiniteEnv) : List (Name × Bool × List LVal) :=
  env.entries.foldr
    (fun entry edges =>
      (partialTyBorrows entry.2.ty).map
          (fun borrow => (entry.1, borrow.1, borrow.2)) ++ edges)
    []

def readProhibited (env : FiniteEnv) (lv : LVal) : Bool :=
  (envBorrowEdges env).any (fun edge =>
    edge.2.1 &&
      edge.2.2.any (fun target => pathConflicts target lv))

def writeProhibited (env : FiniteEnv) (lv : LVal) : Bool :=
  readProhibited env lv ||
    (envBorrowEdges env).any (fun edge =>
      edge.2.2.any (fun target => pathConflicts target lv))

mutual
  def tyJoin? : Ty → Ty → Option Ty
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

  def partialTyJoin? : PartialTy → PartialTy → Option PartialTy
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
  def tySameShape : Ty → Ty → Bool
    | .unit, .unit => true
    | .int, .int => true
    | .bool, .bool => true
    | .borrow mutable₁ _, .borrow mutable₂ _ => mutable₁ == mutable₂
    | .box left, .box right => tySameShape left right
    | _, _ => false

  def partialTySameShape : PartialTy → PartialTy → Bool
    | .ty left, .ty right => tySameShape left right
    | .box left, .box right => partialTySameShape left right
    | .undef left, .undef right => tySameShape left right
    | _, _ => false
end

def lifetimeIntersection? (left right : Lifetime) : Option Lifetime :=
  if left.contains right then some right
  else if right.contains left then some left
  else none

def lifetimeOutlives (outer inner : Lifetime) : Bool :=
  outer.contains inner

mutual
  def lvalType? : Nat → FiniteEnv → LVal → Option (PartialTy × Lifetime)
    | 0, _, _ => none
    | _fuel + 1, env, .var name => do
        let slot ← env.lookup name
        some (slot.ty, slot.lifetime)
    | fuel + 1, env, .deref lv => do
        match ← lvalType? fuel env lv with
        | (.box inner, lifetime) => some (inner, lifetime)
        | (.ty (.borrow _ targets), _) => lvalTargetsType? fuel env targets
        | _ => none

  def lvalTargetsType? :
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

def lvalBaseOutlives (env : FiniteEnv) (lv : LVal)
    (lifetime : Lifetime) : Bool :=
  match env.lookup (LVal.base lv) with
  | some slot => lifetimeOutlives slot.lifetime lifetime
  | none => false

def borrowTargetsWellFormed
    (fuel : Nat) (env : FiniteEnv) (targets : List LVal)
    (lifetime : Lifetime) : Bool :=
  targets.all (fun target =>
    match lvalType? fuel env target with
    | some (.ty _, targetLifetime) =>
        lifetimeOutlives targetLifetime lifetime &&
          lvalBaseOutlives env target lifetime
    | _ => false)

def wellFormedTy (fuel : Nat) (env : FiniteEnv)
    (ty : Ty) (lifetime : Lifetime) : Bool :=
  match ty with
  | .unit => true
  | .int => true
  | .bool => true
  | .borrow _ targets => borrowTargetsWellFormed fuel env targets lifetime
  | .box inner => wellFormedTy fuel env inner lifetime

def targetListPartialTy? (fuel : Nat) (env : FiniteEnv)
    (targets : List LVal) : Option (Option PartialTy) :=
  match targets with
  | [] => some none
  | _ => do
      let (ty, _) ← lvalTargetsType? fuel env targets
      some (some ty)

def targetsAllHaveTy? (fuel : Nat) (env : FiniteEnv)
    (ty : Ty) : List LVal → Bool
  | [] => true
  | target :: rest =>
      match lvalType? fuel env target with
      | some (.ty targetTy, _) =>
          if targetTy = ty then targetsAllHaveTy? fuel env ty rest else false
      | _ => false

def targetListCommonTy? (fuel : Nat) (env : FiniteEnv)
    (targets : List LVal) : Option (Option Ty) :=
  match targets with
  | [] => some none
  | target :: rest =>
      match lvalType? fuel env target with
      | some (.ty ty, _) =>
          if targetsAllHaveTy? fuel env ty rest then some (some ty) else none
      | _ => none

mutual
  def shapeCompatibleTy
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

  def shapeCompatiblePartialTy
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
  def mutableLVal (fuel : Nat) (env : FiniteEnv) : LVal → Bool
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

def strike? : Path → PartialTy → Option PartialTy
  | [], .ty ty => some (.undef ty)
  | _ :: path, .box inner => do
      some (.box (← strike? path inner))
  | _, _ => none

def envMove? (env : FiniteEnv) (lv : LVal) : Option FiniteEnv := do
  let slot ← env.lookup (LVal.base lv)
  let struck ← strike? (LVal.path lv) slot.ty
  some (env.update (LVal.base lv) { slot with ty := struck })

def valueTy? (typing : StoreTyping) : Value → Option Ty
  | .unit => some .unit
  | .int _ => some .int
  | .bool _ => some .bool
  | .ref ref => typing.tyOf ref.location

def containedBorrowsWellFormed (fuel : Nat) (env : FiniteEnv) : Bool :=
  env.entries.all (fun entry =>
    (partialTyBorrows entry.2.ty).all (fun borrow =>
      borrowTargetsWellFormed fuel env borrow.2 entry.2.lifetime))

mutual
  def tyCoherent : Nat → FiniteEnv → Ty → Bool
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

  def partialTyCoherent : Nat → FiniteEnv → PartialTy → Bool
    | fuel, env, .ty ty => tyCoherent fuel env ty
    | 0, _, .box _ => false
    | fuel + 1, env, .box inner => partialTyCoherent fuel env inner
    | _, _, .undef _ => true
end

def coherent (fuel : Nat) (env : FiniteEnv) : Bool :=
  env.entries.all (fun entry => partialTyCoherent fuel env entry.2.ty)

mutual
  def tyCoherentNonempty : Nat → FiniteEnv → Ty → Bool
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

  def partialTyCoherentNonempty : Nat → FiniteEnv → PartialTy → Bool
    | fuel, env, .ty ty => tyCoherentNonempty fuel env ty
    | 0, _, .box _ => false
    | fuel + 1, env, .box inner => partialTyCoherentNonempty fuel env inner
    | _, _, .undef _ => true
end

def coherentNonempty (fuel : Nat) (env : FiniteEnv) : Bool :=
  env.entries.all (fun entry => partialTyCoherentNonempty fuel env entry.2.ty)

def rootCoherent (fuel : Nat) (env : FiniteEnv) (root : Name) : Bool :=
  match env.lookup root with
  | some slot => partialTyCoherent fuel env slot.ty
  | none => false

def rankOf? : Nat → FiniteEnv → Name → Option Nat
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

def linearizable (env : FiniteEnv) : Bool :=
  let fuel := (envNames env).length + 1
  env.entries.all (fun entry =>
    match rankOf? fuel env entry.1 with
    | none => false
    | some rootRank =>
        (PartialTy.vars entry.2.ty).all (fun dep =>
          match rankOf? fuel env dep with
          | some depRank => depRank < rootRank
          | none => false))

def wellFormedKit (fuel : Nat) (env : FiniteEnv) : Bool :=
  containedBorrowsWellFormed fuel env && coherent fuel env && linearizable env

def envJoinStep? (left right result : FiniteEnv)
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

def envJoinNames? (left right : FiniteEnv) :
    List Name → FiniteEnv → Option FiniteEnv
  | [], result => some result
  | name :: names, result => do
      let result' ← envJoinStep? left right result name
      envJoinNames? left right names result'

def envJoin? (left right : FiniteEnv) : Option FiniteEnv :=
  envJoinNames? left right (unionNames left.support right.support)
    FiniteEnv.empty

def envJoinSameShape (branch join : FiniteEnv) : Bool :=
  branch.support.all (fun name =>
    match branch.lookup name, join.lookup name with
    | some branchSlot, some joinSlot => partialTySameShape branchSlot.ty joinSlot.ty
    | _, _ => false)

def tyBorrowSafeAgainstEnv (env : FiniteEnv) (ty : Ty) : Bool :=
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

def borrowSafeRoot (env : FiniteEnv) (root : Name) : Bool :=
  let rootMutableBorrows :=
    (envBorrowEdges env).filter (fun edge => edge.1 == root && edge.2.1)
  let allBorrows := envBorrowEdges env
  rootMutableBorrows.all (fun rootBorrow =>
    allBorrows.all (fun otherBorrow =>
      rootBorrow.2.2.all (fun targetMutable =>
        otherBorrow.2.2.all (fun targetOther =>
          !pathConflicts targetMutable targetOther || root == otherBorrow.1))))

def mutableBorrowTargetsOfRoot (env : FiniteEnv) (root : Name) :
    List LVal :=
  (envBorrowEdges env).foldl
    (fun targets edge =>
      if edge.1 == root && edge.2.1 then unionLVals targets edge.2.2 else targets)
    []

def guardClosure (env : FiniteEnv) : Nat → List Name → List Name → List Name
  | 0, seen, _ => seen
  | _fuel + 1, seen, [] => seen
  | fuel + 1, seen, root :: rest =>
      if seen.contains root then
        guardClosure env fuel seen rest
      else
        let next := (mutableBorrowTargetsOfRoot env root).map LVal.base
        guardClosure env fuel (seen ++ [root]) (unionNames rest next)

def guardedRoots (env : FiniteEnv) (source : LVal) : List Name :=
  guardClosure env ((envNames env).length + 1) [] [LVal.base source]

def guardClosed (env : FiniteEnv) (roots : List Name) : Bool :=
  roots.all (fun root =>
    (mutableBorrowTargetsOfRoot env root).all (fun target =>
      roots.contains (LVal.base target)))

def assignmentBorrowSafety (env : FiniteEnv) : LVal → Bool
  | .var _ => true
  | .deref source =>
      let roots := guardedRoots env source
      roots.contains (LVal.base source) &&
        guardClosed env roots &&
          roots.all (borrowSafeRoot env)

mutual
  def updateAtPath? (fuel rank : Nat) (env : FiniteEnv)
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

  def writeBorrowTargets? (fuel rank : Nat) (env : FiniteEnv)
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

  def envWrite? (fuel rank : Nat) (env : FiniteEnv)
      (lv : LVal) (rhsTy : Ty) : Option FiniteEnv := do
    let slot ← env.lookup (LVal.base lv)
    let (env₂, updatedTy) ← updateAtPath? fuel rank env (LVal.path lv) slot.ty rhsTy
    some (env₂.update (LVal.base lv) { slot with ty := updatedTy })
end

def targetInBorrowTargets (target : LVal) (borrows : List (Bool × List LVal)) :
    Bool :=
  borrows.any (fun borrow => lvalMem target borrow.2)

def linearizedByRanks? (fuel : Nat) (rankSource env : FiniteEnv) :
    Bool :=
  env.entries.all (fun entry =>
    match rankOf? fuel rankSource entry.1 with
    | none => false
    | some rootRank =>
        (PartialTy.vars entry.2.ty).all (fun dep =>
          match rankOf? fuel rankSource dep with
          | some depRank => depRank < rootRank
          | none => false))

def rhsBorrowTargetsBelow (envBefore result : FiniteEnv) (rhsTy : Ty) :
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

def isLifetimeChild (parent child : Lifetime) : Bool :=
  match child.path.drop parent.path.length with
  | [_] => parent.path.isPrefixOf child.path
  | _ => false

mutual
  def termDiverges : Term → Bool
    | .missing => true
    | .block _ terms => termListDiverges terms
    | _ => false

  def termListDiverges : List Term → Bool
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

  def checkStrictWhile? (fuel : Nat) (env : FiniteEnv)
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

  def checkWhileJoinLoop? (iterations fuel : Nat) (entry inv : FiniteEnv)
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

  def checkWhileJoin? (fuel : Nat) (env : FiniteEnv)
      (typing : StoreTyping) (lifetime bodyLifetime : Lifetime)
      (condition body : Term) : Except String CheckResult := do
    ensure (isLifetimeChild lifetime bodyLifetime)
      "while body lifetime is not a child of current lifetime"
    checkWhileJoinLoop? fuel fuel env env typing lifetime bodyLifetime condition body

  def checkWhile? (fuel : Nat) (env : FiniteEnv)
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

def lvalCheckerFuelBound : LVal → Nat
  | .var _ => 1
  | .deref lv => lvalCheckerFuelBound lv + 1

mutual
  def termContainsMissing? : Term → Bool
    | .block _ terms => termListContainsMissing? terms
    | .letMut _ initialiser => termContainsMissing? initialiser
    | .assign _ rhs => termContainsMissing? rhs
    | .box operand => termContainsMissing? operand
    | .borrow _ _ => false
    | .move _ => false
    | .copy _ => false
    | .val _ => false
    | .missing => true
    | .eq lhs rhs => termContainsMissing? lhs || termContainsMissing? rhs
    | .ite condition trueBranch falseBranch =>
        termContainsMissing? condition ||
          termContainsMissing? trueBranch ||
            termContainsMissing? falseBranch
    | .whileLoop _ condition body =>
        termContainsMissing? condition || termContainsMissing? body
    | .whileCond _ conditionInFlight condition body =>
        termContainsMissing? conditionInFlight ||
          termContainsMissing? condition ||
            termContainsMissing? body
    | .whileBody _ bodyInFlight condition body =>
        termContainsMissing? bodyInFlight ||
          termContainsMissing? condition ||
            termContainsMissing? body

  def termListContainsMissing? : List Term → Bool
    | [] => false
    | term :: rest => termContainsMissing? term || termListContainsMissing? rest
end

mutual
  def termContainsWhile? : Term → Bool
    | .block _ terms => termListContainsWhile? terms
    | .letMut _ initialiser => termContainsWhile? initialiser
    | .assign _ rhs => termContainsWhile? rhs
    | .box operand => termContainsWhile? operand
    | .borrow _ _ => false
    | .move _ => false
    | .copy _ => false
    | .val _ => false
    | .missing => false
    | .eq lhs rhs => termContainsWhile? lhs || termContainsWhile? rhs
    | .ite condition trueBranch falseBranch =>
        termContainsWhile? condition ||
          termContainsWhile? trueBranch ||
            termContainsWhile? falseBranch
    | .whileLoop _ _ _ => true
    | .whileCond _ _ _ _ => true
    | .whileBody _ _ _ _ => true

  def termListContainsWhile? : List Term → Bool
    | [] => false
    | term :: rest => termContainsWhile? term || termListContainsWhile? rest
end

theorem termContainsMissing?_false_of_mem {terms : List Term} {term : Term} :
    termListContainsMissing? terms = false →
      term ∈ terms →
        termContainsMissing? term = false := by
  induction terms with
  | nil =>
      intro _h hmem
      cases hmem
  | cons head rest ih =>
      intro hmissing hmem
      simp [termListContainsMissing?] at hmissing
      rcases hmissing with ⟨hhead, hrest⟩
      cases hmem with
      | head =>
          exact hhead
      | tail _ htail =>
          exact ih hrest htail

theorem termContainsWhile?_false_of_mem {terms : List Term} {term : Term} :
    termListContainsWhile? terms = false →
      term ∈ terms →
        termContainsWhile? term = false := by
  induction terms with
  | nil =>
      intro _h hmem
      cases hmem
  | cons head rest ih =>
      intro hwhile hmem
      simp [termListContainsWhile?] at hwhile
      rcases hwhile with ⟨hhead, hrest⟩
      cases hmem with
      | head =>
          exact hhead
      | tail _ htail =>
          exact ih hrest htail

theorem not_termDiverges_of_termContainsMissing?_false {term : Term} :
    termContainsMissing? term = false →
      ¬ Term.Diverges term := by
  intro hmissing hdiverges
  induction hdiverges with
  | missing =>
      simp [termContainsMissing?] at hmissing
  | block hmem _hdiverges ih =>
      simp [termContainsMissing?] at hmissing
      exact ih (termContainsMissing?_false_of_mem hmissing hmem)

mutual
  def termCheckerFuelBound : Term → Nat
    | .block _ terms => termListCheckerFuelBound terms + 2
    | .letMut _ initialiser => termCheckerFuelBound initialiser + 2
    | .assign lhs rhs =>
        lvalCheckerFuelBound lhs + termCheckerFuelBound rhs + 2
    | .box operand => termCheckerFuelBound operand + 2
    | .borrow _ lv => lvalCheckerFuelBound lv + 2
    | .move lv => lvalCheckerFuelBound lv + 2
    | .copy lv => lvalCheckerFuelBound lv + 2
    | .val _ => 2
    | .missing => 2
    | .eq lhs rhs => termCheckerFuelBound lhs + termCheckerFuelBound rhs + 2
    | .ite condition trueBranch falseBranch =>
        termCheckerFuelBound condition +
          termCheckerFuelBound trueBranch +
            termCheckerFuelBound falseBranch + 2
    | .whileLoop _ condition body =>
        termCheckerFuelBound condition + termCheckerFuelBound body + 2
    | .whileCond _ conditionInFlight condition body =>
        termCheckerFuelBound conditionInFlight +
          termCheckerFuelBound condition +
            termCheckerFuelBound body + 2
    | .whileBody _ bodyInFlight condition body =>
        termCheckerFuelBound bodyInFlight +
          termCheckerFuelBound condition +
            termCheckerFuelBound body + 2

  def termListCheckerFuelBound : List Term → Nat
    | [] => 1
    | term :: rest =>
        termCheckerFuelBound term + termListCheckerFuelBound rest + 1
end

mutual
  theorem termCheckerFuelBound_pos (term : Term) :
      0 < termCheckerFuelBound term := by
    cases term <;> simp [termCheckerFuelBound,
      termCheckerFuelBound_pos, termListCheckerFuelBound_pos]

  theorem termListCheckerFuelBound_pos (terms : List Term) :
      0 < termListCheckerFuelBound terms := by
    cases terms <;> simp [termListCheckerFuelBound]
end

theorem lvalCheckerFuelBound_pos (lv : LVal) :
    0 < lvalCheckerFuelBound lv := by
  induction lv with
  | var _ =>
      simp [lvalCheckerFuelBound]
  | deref inner ih =>
      simp [lvalCheckerFuelBound]

mutual
  def tyBorrowTargetsFuelBounded (fuel : Nat) : Ty → Prop
    | .unit => True
    | .int => True
    | .bool => True
    | .borrow _ targets =>
        ∀ target, target ∈ targets → lvalCheckerFuelBound target < fuel
    | .box inner => tyBorrowTargetsFuelBounded fuel inner

  def partialTyBorrowTargetsFuelBounded
      (fuel : Nat) : PartialTy → Prop
    | .ty ty => tyBorrowTargetsFuelBounded fuel ty
    | .box inner => partialTyBorrowTargetsFuelBounded fuel inner
    | .undef ty => tyBorrowTargetsFuelBounded fuel ty
end

def envBorrowTargetsFuelBounded (fuel : Nat)
    (env : FiniteEnv) : Prop :=
  ∀ {name slot},
    env.lookup name = some slot →
      partialTyBorrowTargetsFuelBounded fuel slot.ty

theorem partialTyBorrowTargetsFuelBounded_contains
    {fuel : Nat} {partialTy : PartialTy} {needle : Ty} :
    partialTyBorrowTargetsFuelBounded fuel partialTy →
      PartialTyContains partialTy needle →
        ∀ {mutable targets},
          needle = .borrow mutable targets →
            ∀ target, target ∈ targets → lvalCheckerFuelBound target < fuel := by
  intro hbounded hcontains
  induction hcontains with
  | here =>
      intro mutable targets hneedle
      cases hneedle
      simpa [partialTyBorrowTargetsFuelBounded,
        tyBorrowTargetsFuelBounded] using hbounded
  | tyBox _hinner ih =>
      intro mutable targets hneedle
      exact ih
        (by
          simpa [partialTyBorrowTargetsFuelBounded,
            tyBorrowTargetsFuelBounded] using hbounded)
        hneedle
  | box _hinner ih =>
      intro mutable targets hneedle
      exact ih
        (by
          simpa [partialTyBorrowTargetsFuelBounded] using hbounded)
        hneedle

mutual
  theorem tyBorrowTargetsFuelBounded_of_eqv {fuel : Nat}
      {left right : Ty} :
      Ty.eqv left right →
        tyBorrowTargetsFuelBounded fuel left →
          tyBorrowTargetsFuelBounded fuel right := by
    intro heqv hbounded
    cases left <;> cases right <;> simp [Ty.eqv,
      tyBorrowTargetsFuelBounded] at heqv hbounded ⊢
    · rcases heqv with ⟨_hmutable, _hleftRight, hrightLeft⟩
      intro target htarget
      exact hbounded target (hrightLeft htarget)
    · exact tyBorrowTargetsFuelBounded_of_eqv heqv hbounded

  theorem partialTyBorrowTargetsFuelBounded_of_eqv {fuel : Nat}
      {left right : PartialTy} :
      PartialTy.eqv left right →
        partialTyBorrowTargetsFuelBounded fuel left →
          partialTyBorrowTargetsFuelBounded fuel right := by
    intro heqv hbounded
    cases left <;> cases right <;> simp [PartialTy.eqv,
      partialTyBorrowTargetsFuelBounded] at heqv hbounded ⊢
    · exact tyBorrowTargetsFuelBounded_of_eqv heqv hbounded
    · exact partialTyBorrowTargetsFuelBounded_of_eqv heqv hbounded
    · exact tyBorrowTargetsFuelBounded_of_eqv heqv hbounded
end

theorem lvalCheckerFuelBound_le_termFuel_of_copy {fuel : Nat}
    {lv : LVal} :
    termCheckerFuelBound (.copy lv) ≤ fuel + 1 →
      lvalCheckerFuelBound lv ≤ fuel := by
  intro h
  simp [termCheckerFuelBound] at h
  omega

theorem lvalCheckerFuelBound_le_termFuel_of_move {fuel : Nat}
    {lv : LVal} :
    termCheckerFuelBound (.move lv) ≤ fuel + 1 →
      lvalCheckerFuelBound lv ≤ fuel := by
  intro h
  simp [termCheckerFuelBound] at h
  omega

theorem lvalCheckerFuelBound_le_termFuel_of_borrow {fuel : Nat}
    {mutable : Bool} {lv : LVal} :
    termCheckerFuelBound (.borrow mutable lv) ≤ fuel + 1 →
      lvalCheckerFuelBound lv ≤ fuel := by
  intro h
  simp [termCheckerFuelBound] at h
  omega

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

end Paper
end LwRust
