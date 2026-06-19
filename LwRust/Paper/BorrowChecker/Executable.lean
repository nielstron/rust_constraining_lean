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

theorem lookup_update_eq (env : FiniteEnv) (name : Name)
    (slot : EnvSlot) :
    (env.update name slot).lookup name = some slot := by
  have h := congrArg (fun env => env.slotAt name)
    (FiniteEnv.toEnv_update env name slot)
  simpa [FiniteEnv.toEnv, Env.update] using h

theorem lookup_update_ne (env : FiniteEnv) {updated name : Name}
    (slot : EnvSlot) (hne : name ≠ updated) :
    (env.update updated slot).lookup name = env.lookup name := by
  have h := congrArg (fun env => env.slotAt name)
    (FiniteEnv.toEnv_update env updated slot)
  simpa [FiniteEnv.toEnv, Env.update, hne] using h

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

/--
Every concrete entry stored in `entries` agrees with the finite lookup map.

The executable keeps older shadowed entries out of environments it constructs,
but many executable predicates scan `entries` directly while the declarative
environment view uses `lookup`.  Completeness proofs use this invariant to
move between the two views.
-/
def EntriesReflectLookup (env : FiniteEnv) : Prop :=
  ∀ {name : Name} {slot : EnvSlot},
    (name, slot) ∈ env.entries → env.lookup name = some slot

theorem entriesReflectLookup_empty :
    EntriesReflectLookup FiniteEnv.empty := by
  intro name slot hmem
  cases hmem

theorem entriesReflectLookup_update {env : FiniteEnv}
    {name : Name} {slot : EnvSlot} :
    EntriesReflectLookup env →
      EntriesReflectLookup (env.update name slot) := by
  intro hreflect needle candidate hmem
  unfold FiniteEnv.update at hmem
  simp only [List.mem_cons, List.mem_filter] at hmem
  rcases hmem with hhead | htail
  · cases hhead
    exact lookup_update_eq env name slot
  · rcases htail with ⟨horiginal, hkeep⟩
    have hne : needle ≠ name := by
      intro heq
      subst heq
      simp at hkeep
    rw [lookup_update_ne env slot hne]
    exact hreflect horiginal

theorem entriesReflectLookup_erase {env : FiniteEnv}
    {erased : Name} :
    EntriesReflectLookup env →
      EntriesReflectLookup (env.erase erased) := by
  intro hreflect needle candidate hmem
  cases env with
  | mk entries =>
      change (needle, candidate) ∈
        entries.filter (fun entry => entry.1 != erased) at hmem
      change
        FiniteEnv.lookupEntries
          (entries.filter (fun entry => entry.1 != erased)) needle =
            some candidate
      simp only [List.mem_filter] at hmem
      rcases hmem with ⟨horiginal, hkeep⟩
      have hne : needle ≠ erased := by
        intro heq
        subst heq
        simp at hkeep
      rw [FiniteEnv.lookupEntries_filter_update_ne entries hne]
      exact hreflect horiginal

theorem entriesReflectLookup_dropLifetime {env : FiniteEnv}
    {lifetime : Lifetime} :
    EntriesReflectLookup env →
      EntriesReflectLookup (env.dropLifetime lifetime) := by
  intro _hreflect name slot hmem
  unfold FiniteEnv.dropLifetime at hmem
  simp only [List.mem_filter] at hmem
  rcases hmem with ⟨_horiginal, hkeep⟩
  cases hlookup : env.lookup name with
  | none =>
      simp [hlookup] at hkeep
  | some candidate =>
      simp [hlookup] at hkeep
      rcases hkeep with ⟨hslot, hlifetime⟩
      subst hslot
      have hdrop := congrArg (fun env => env.slotAt name)
        (FiniteEnv.toEnv_dropLifetime env lifetime)
      change
        (env.dropLifetime lifetime).lookup name =
          (env.toEnv.dropLifetime lifetime).slotAt name at hdrop
      simpa [FiniteEnv.toEnv, Env.dropLifetime, hlookup, hlifetime] using hdrop

theorem lookupEntries_mem {entries : List (Name × EnvSlot)}
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

theorem support_foldl_preserves
    {entries : List (Name × EnvSlot)}
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

theorem support_foldl_contains_entry
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
          exact ih
            (acc := if acc.contains first.1 then acc else acc ++ [first.1])
            hrest

theorem lookup_mem_support {env : FiniteEnv} {name : Name}
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

theorem support_foldl_mem_iff
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

theorem lookupEntries_isSome_of_entry_name
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
            exact ⟨found, by
              simpa [FiniteEnv.lookupEntries, hname] using hfound⟩

theorem mem_support_iff_lookup_isSome {env : FiniteEnv}
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

theorem lookup_none_of_not_mem_support {env : FiniteEnv}
    {name : Name} :
    name ∉ env.support → env.lookup name = none := by
  intro hnot
  cases hlookup : env.lookup name with
  | none => rfl
  | some slot =>
      exact False.elim (hnot (lookup_mem_support hlookup))

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

theorem mem_insertName {names : List Name} {candidate name : Name} :
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

theorem mem_unionNames {left right : List Name} {candidate : Name} :
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

theorem sameBindings_lookup_eq {left right : FiniteEnv} :
    left.sameBindings right = true →
      ∀ name, left.lookup name = right.lookup name := by
  intro h name
  unfold sameBindings at h
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

theorem sameBindings_toEnv_eq {left right : FiniteEnv} :
    left.sameBindings right = true → left.toEnv = right.toEnv := by
  intro h
  change ({ slotAt := left.lookup } : Env) = { slotAt := right.lookup }
  have hslot : left.lookup = right.lookup := by
    funext name
    exact sameBindings_lookup_eq h name
  rw [hslot]

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

theorem tySameShape_sound_aux (left : Ty) :
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

theorem tySameShape_sound {left right : Ty} :
    tySameShape left right = true → Ty.sameShape left right :=
  tySameShape_sound_aux left right

theorem partialTySameShape_sound_aux (left : PartialTy) :
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

theorem partialTySameShape_sound {left right : PartialTy} :
    partialTySameShape left right = true → PartialTy.sameShape left right :=
  partialTySameShape_sound_aux left right

theorem tySameShape_complete_aux (left : Ty) :
    ∀ right, Ty.sameShape left right → tySameShape left right = true := by
  refine Ty.rec
    (motive_1 := fun left =>
      ∀ right, Ty.sameShape left right → tySameShape left right = true)
    (motive_2 := fun _ => True)
    ?unit ?int ?borrow ?box ?bool ?partialTy ?partialBox ?partialUndef left
  · intro right h
    cases right <;> simp [Ty.sameShape, tySameShape] at h ⊢
  · intro right h
    cases right <;> simp [Ty.sameShape, tySameShape] at h ⊢
  · intro mutable targets right h
    cases right <;> simp [Ty.sameShape, tySameShape] at h ⊢
    exact h
  · intro inner ih right h
    cases right <;> simp [Ty.sameShape, tySameShape] at h ⊢
    exact ih _ h
  · intro right h
    cases right <;> simp [Ty.sameShape, tySameShape] at h ⊢
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _; trivial

theorem tySameShape_complete {left right : Ty} :
    Ty.sameShape left right → tySameShape left right = true :=
  tySameShape_complete_aux left right

theorem partialTySameShape_complete_aux (left : PartialTy) :
    ∀ right,
      PartialTy.sameShape left right → partialTySameShape left right = true := by
  refine PartialTy.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun left =>
      ∀ right,
        PartialTy.sameShape left right → partialTySameShape left right = true)
    ?unit ?int ?borrow ?boxTy ?bool ?ty ?box ?undef left
  · trivial
  · trivial
  · intro _ _; trivial
  · intro _ _; trivial
  · trivial
  · intro ty _ right h
    cases right <;> simp [PartialTy.sameShape, partialTySameShape] at h ⊢
    exact tySameShape_complete h
  · intro inner ih right h
    cases right <;> simp [PartialTy.sameShape, partialTySameShape] at h ⊢
    exact ih _ h
  · intro ty _ right h
    cases right <;> simp [PartialTy.sameShape, partialTySameShape] at h ⊢
    exact tySameShape_complete h

theorem partialTySameShape_complete {left right : PartialTy} :
    PartialTy.sameShape left right → partialTySameShape left right = true :=
  partialTySameShape_complete_aux left right

theorem partialTyStrengthens_undef_to_undef_inv {left right : Ty} :
    PartialTyStrengthens (.undef left) (.undef right) →
      PartialTyStrengthens (.ty left) (.ty right) := by
  intro h
  cases h with
  | reflex =>
      exact PartialTyStrengthens.reflex
  | undefLeft hinner =>
      exact hinner

theorem partialTyJoin_ty_undef {left right join : Ty} :
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

theorem partialTyJoin_undef_ty {left right join : Ty} :
    PartialTyJoin (.ty left) (.ty right) (.ty join) →
      PartialTyJoin (.undef left) (.ty right) (.undef join) := by
  intro hjoin
  exact PartialTyUnion.symm
    (partialTyJoin_ty_undef (PartialTyUnion.symm hjoin))

theorem partialTyJoin_undef_undef {left right join : Ty} :
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
  theorem tyJoin?_sound :
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

theorem partialTyJoin?_sound :
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

def lvalFitsFuel : Nat → LVal → Bool
  | 0, _ => false
  | _fuel + 1, .var _ => true
  | fuel + 1, .deref lv => lvalFitsFuel fuel lv

def lvalTypeOrError? (fuel : Nat) (env : FiniteEnv)
    (lv : LVal) (message : String) : Except String (PartialTy × Lifetime) :=
  match lvalType? fuel env lv with
  | some result => .ok result
  | none =>
      if lvalFitsFuel fuel lv then .error message
      else .error "borrow checker fuel exhausted"

@[simp] theorem lvalTypeOrError?_some {fuel : Nat} {env : FiniteEnv}
    {lv : LVal} {message : String} {result : PartialTy × Lifetime} :
    lvalType? fuel env lv = some result →
      lvalTypeOrError? fuel env lv message = .ok result := by
  intro h
  simp [lvalTypeOrError?, h]

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

def EnvJoinSlotSpec
    (left right join : Option EnvSlot) : Prop :=
  match left, right, join with
  | none, none, none => True
  | some leftSlot, some rightSlot, some joinSlot =>
      leftSlot.lifetime = rightSlot.lifetime ∧
        joinSlot.lifetime = leftSlot.lifetime ∧
          PartialTyJoin leftSlot.ty rightSlot.ty joinSlot.ty
  | _, _, _ => False

theorem envJoinStep?_lookup_eq_of_ne {left right result result' : FiniteEnv}
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
          exact FiniteEnv.lookup_update_ne result
            { ty := joinedTy, lifetime := rightSlot.lifetime } hne
    · simp [hlife] at hstep

theorem envJoinNames?_lookup_eq_of_not_mem
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

theorem envJoinNames?_impossible_of_left_only
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

theorem envJoinNames?_impossible_of_right_only
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

theorem envJoinNames?_lookup_join_of_mem
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
                          (FiniteEnv.lookup_update_eq result name
                            { ty := joinTy, lifetime := rightSlot.lifetime })
              · simp [hlife] at hstep
          | tail _ htail =>
              exact ih htail hleft hright hrun

theorem envJoin?_slotSpec {left right join : FiniteEnv} :
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
            · rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hmemLeft) with
                ⟨slot, hslot⟩
              rw [hleft] at hslot
              cases hslot
            · rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hmemRight) with
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
            exact Or.inr (FiniteEnv.lookup_mem_support hright)
          exact False.elim
            (envJoinNames?_impossible_of_right_only hmemNames hleft hright
              hjoin)
  | some leftSlot =>
      cases hright : right.lookup name with
      | none =>
          have hmemNames : name ∈ names := by
            apply mem_unionNames.mpr
            exact Or.inl (FiniteEnv.lookup_mem_support hleft)
          exact False.elim
            (envJoinNames?_impossible_of_left_only hmemNames hleft hright
              hjoin)
      | some rightSlot =>
          have hmemNames : name ∈ names := by
            apply mem_unionNames.mpr
            exact Or.inl (FiniteEnv.lookup_mem_support hleft)
          rcases envJoinNames?_lookup_join_of_mem hmemNames hleft hright
              hjoin with
            ⟨joinTy, hlife, htyJoin, hlookup⟩
          simp [hleft, hright, EnvJoinSlotSpec]
          rw [hlookup]
          exact ⟨hlife, rfl, partialTyJoin?_sound htyJoin⟩

theorem envJoinSlotSpec_sound {left right join : FiniteEnv}
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

theorem envJoin?_sound {left right join : FiniteEnv} :
    envJoin? left right = some join →
      EnvJoin left.toEnv right.toEnv join.toEnv := by
  intro h
  exact envJoinSlotSpec_sound (envJoin?_slotSpec h)

theorem envJoinSameShape_sound {branch join : FiniteEnv} :
    envJoinSameShape branch join = true →
      EnvJoinSameShape branch.toEnv join.toEnv := by
  intro h x branchSlot joinSlot hbranch hjoin
  unfold envJoinSameShape at h
  change branch.lookup x = some branchSlot at hbranch
  change join.lookup x = some joinSlot at hjoin
  have hmem : x ∈ branch.support := FiniteEnv.lookup_mem_support hbranch
  have hcheck := (List.all_eq_true.mp h) x hmem
  simp [hbranch, hjoin] at hcheck
  exact partialTySameShape_sound hcheck

theorem envJoinSameShape_left_complete_of_envJoin?
    {left right join : FiniteEnv} :
    envJoin? left right = some join →
      (∀ name leftSlot rightSlot,
        left.lookup name = some leftSlot →
          right.lookup name = some rightSlot →
            PartialTy.sameShape leftSlot.ty rightSlot.ty) →
        envJoinSameShape left join = true := by
  intro hjoin hbranches
  unfold envJoinSameShape
  exact List.all_eq_true.mpr (by
    intro name hmem
    rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hmem) with
      ⟨leftSlot, hleft⟩
    have hspec := envJoin?_slotSpec hjoin name
    cases hright : right.lookup name with
    | none =>
        simp [EnvJoinSlotSpec, hleft, hright] at hspec
    | some rightSlot =>
        cases hjoinSlot : join.lookup name with
        | none =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinSlot] at hspec
        | some joinSlot =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinSlot] at hspec
            rcases hspec with ⟨_hlifeRight, _hlifeJoin, htyJoin⟩
            have hshape :
                PartialTy.sameShape leftSlot.ty joinSlot.ty :=
              partialTyUnion_sameShape_of_sameShape htyJoin
                (hbranches name leftSlot rightSlot hleft hright)
            simp [hleft, partialTySameShape_complete hshape])

theorem envJoinSameShape_right_complete_of_envJoin?
    {left right join : FiniteEnv} :
    envJoin? left right = some join →
      (∀ name leftSlot rightSlot,
        left.lookup name = some leftSlot →
          right.lookup name = some rightSlot →
            PartialTy.sameShape leftSlot.ty rightSlot.ty) →
        envJoinSameShape right join = true := by
  intro hjoin hbranches
  unfold envJoinSameShape
  exact List.all_eq_true.mpr (by
    intro name hmem
    rcases (FiniteEnv.mem_support_iff_lookup_isSome.mp hmem) with
      ⟨rightSlot, hright⟩
    have hspec := envJoin?_slotSpec hjoin name
    cases hleft : left.lookup name with
    | none =>
        simp [EnvJoinSlotSpec, hleft, hright] at hspec
    | some leftSlot =>
        cases hjoinSlot : join.lookup name with
        | none =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinSlot] at hspec
        | some joinSlot =>
            simp [EnvJoinSlotSpec, hleft, hright, hjoinSlot] at hspec
            rcases hspec with ⟨_hlifeRight, _hlifeJoin, htyJoin⟩
            have hshape :
                PartialTy.sameShape rightSlot.ty joinSlot.ty :=
              partialTyUnion_sameShape_of_sameShape
                (PartialTyUnion.symm htyJoin)
                (PartialTy.sameShape_symm
                  (hbranches name leftSlot rightSlot hleft hright))
            simp [hright, partialTySameShape_complete hshape])

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
              lvalTypeOrError? fuel env lv "copy operand is not typeable"
            let ty ←
              match partialTy with
              | PartialTy.ty ty => pure ty
              | _ => .error "copy operand is not fully initialized"
            ensure (copyTy ty) "copy operand is not copyable"
            ensure (!readProhibited env lv) "copy is read-prohibited"
            pure ⟨ty, env⟩
        | .move lv => do
            let (partialTy, _) ←
              lvalTypeOrError? fuel env lv "move operand is not typeable"
            let ty ←
              match partialTy with
              | PartialTy.ty ty => pure ty
              | _ => .error "move operand is not fully initialized"
            ensure (!writeProhibited env lv) "move is write-prohibited"
            let moved ← fromOption "move cannot strike operand" (envMove? env lv)
            pure ⟨ty, moved⟩
        | .borrow mutable lv => do
            let (partialTy, _) ←
              lvalTypeOrError? fuel env lv "borrow operand is not typeable"
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
              lvalTypeOrError? fuel env lhs "assignment lhs is not typeable"
            let rhsResult ← checkTerm? fuel env typing lifetime rhs
            let (oldTyAfter, targetLifetimeAfter) ←
              lvalTypeOrError? fuel rhsResult.env lhs
                "assignment lhs is not typeable after rhs"
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

theorem lvalFitsFuel_of_lvalCheckerFuelBound_lt {fuel : Nat} {lv : LVal} :
    lvalCheckerFuelBound lv < fuel → lvalFitsFuel fuel lv = true := by
  induction lv generalizing fuel with
  | var _ =>
      cases fuel <;> simp [lvalCheckerFuelBound, lvalFitsFuel]
  | deref inner ih =>
      cases fuel with
      | zero =>
          simp [lvalCheckerFuelBound]
      | succ fuel =>
          intro h
          simp [lvalCheckerFuelBound] at h
          exact ih h

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

theorem envBorrowTargetsFuelBounded_empty (fuel : Nat) :
    envBorrowTargetsFuelBounded fuel FiniteEnv.empty := by
  intro name slot hlookup
  simp [FiniteEnv.empty, FiniteEnv.lookup, FiniteEnv.lookupEntries] at hlookup

theorem envBorrowTargetsFuelBounded_update {fuel : Nat}
    {env : FiniteEnv} {name : Name} {slot : EnvSlot} :
    envBorrowTargetsFuelBounded fuel env →
      partialTyBorrowTargetsFuelBounded fuel slot.ty →
        envBorrowTargetsFuelBounded fuel (env.update name slot) := by
  intro henv hslot candidate candidateSlot hlookup
  by_cases hcandidate : candidate = name
  · subst hcandidate
    rw [FiniteEnv.lookup_update_eq] at hlookup
    cases hlookup
    exact hslot
  · rw [FiniteEnv.lookup_update_ne env slot hcandidate] at hlookup
    exact henv hlookup

theorem tyBorrowTargetsFuelBounded_mono {fuel fuel' : Nat}
    {ty : Ty} :
    fuel ≤ fuel' →
      tyBorrowTargetsFuelBounded fuel ty →
        tyBorrowTargetsFuelBounded fuel' ty := by
  intro hle hbounded
  refine Ty.rec
    (motive_1 := fun ty =>
      tyBorrowTargetsFuelBounded fuel ty →
        tyBorrowTargetsFuelBounded fuel' ty)
    (motive_2 := fun _partialTy => True)
    ?unit ?int ?borrow ?box ?bool ?partialTy ?partialBox ?partialUndef ty
    hbounded
  · intro _hbounded
    trivial
  · intro _hbounded
    trivial
  · intro _mutable _targets hbounded target htarget
    exact lt_of_lt_of_le (hbounded target htarget) hle
  · intro _inner ih hbounded
    exact ih hbounded
  · intro _hbounded
    trivial
  · intro _ty _ih
    trivial
  · intro _inner _ih
    trivial
  · intro _ty _ih
    trivial

theorem partialTyBorrowTargetsFuelBounded_mono {fuel fuel' : Nat}
    {partialTy : PartialTy} :
    fuel ≤ fuel' →
      partialTyBorrowTargetsFuelBounded fuel partialTy →
        partialTyBorrowTargetsFuelBounded fuel' partialTy := by
  intro hle hbounded
  refine PartialTy.rec
    (motive_1 := fun ty =>
      tyBorrowTargetsFuelBounded fuel ty →
        tyBorrowTargetsFuelBounded fuel' ty)
    (motive_2 := fun partialTy =>
      partialTyBorrowTargetsFuelBounded fuel partialTy →
        partialTyBorrowTargetsFuelBounded fuel' partialTy)
    ?unit ?int ?borrow ?box ?bool ?partialTy ?partialBox ?partialUndef
    partialTy hbounded
  · intro _hbounded
    trivial
  · intro _hbounded
    trivial
  · intro _mutable _targets hbounded target htarget
    exact lt_of_lt_of_le (hbounded target htarget) hle
  · intro _inner ih hbounded
    exact ih hbounded
  · intro _hbounded
    trivial
  · intro _ty ih hbounded
    exact ih hbounded
  · intro _inner ih hbounded
    exact ih hbounded
  · intro _ty ih hbounded
    exact ih hbounded

theorem envBorrowTargetsFuelBounded_mono {fuel fuel' : Nat}
    {env : FiniteEnv} :
    fuel ≤ fuel' →
      envBorrowTargetsFuelBounded fuel env →
        envBorrowTargetsFuelBounded fuel' env := by
  intro hle henv name slot hlookup
  exact partialTyBorrowTargetsFuelBounded_mono hle (henv hlookup)

theorem envBorrowTargetsFuelBounded_contains {fuel : Nat}
    {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    envBorrowTargetsFuelBounded fuel env →
      env.lookup name = some slot →
        PartialTyContains slot.ty (.borrow mutable targets) →
          ∀ target, target ∈ targets → lvalCheckerFuelBound target < fuel := by
  intro henv hslot hcontains
  exact partialTyBorrowTargetsFuelBounded_contains
    (henv hslot) hcontains rfl

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
    message = "diverging while bodies require an expected body type in this checker"

def checkTermFails? (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term) : Bool :=
  match checkTerm? fuel env typing lifetime term with
  | .ok _ => false
  | .error message => !checkerErrorUnknown? message

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

theorem borrowCheckFailed?_false_of_borrowCheck? {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true → borrowCheckFailed? fuel term = false := by
  unfold borrowCheck? borrowCheckFailed?
  cases borrowCheckVerdict? fuel term <;> simp

theorem borrowUnknown?_false_of_borrowCheck? {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true → borrowUnknown? fuel term = false := by
  unfold borrowCheck? borrowUnknown?
  cases borrowCheckVerdict? fuel term <;> simp

def checkProgramAs? (fuel : Nat) (term : Term) (expected : Ty) :
    Except String CheckResult :=
  checkTermAs? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term expected

end Paper
end LwRust
