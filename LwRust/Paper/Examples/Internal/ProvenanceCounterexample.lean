import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
Counterexample to the current value-install provenance invariant.

The state is the accepted prefix:

```
let mut a = 0;
let mut x = &mut a;
let mut p = &x;
```

After installing `p`, the lvalue `*p` is statically typed as `&mut a`, but the
value stored in `p` is an immutable reference.  Therefore the value-scoped
mutable registry for `p` cannot cover the concrete leaf reached by `**p`.

This pinpoints why `MutRegistryCovers` is too broad for preservation: it covers
every syntactic lvalue typed `&mut`, including `*p`, rather than only runtime
write-authority gates.
-/

namespace LwRust
namespace Paper

open Core

namespace ProvenanceCounterexample

def l : Lifetime := [0]

def a : LVal := .var "a"
def x : LVal := .var "x"
def p : LVal := .var "p"

def envBeforeP : Env :=
  (Env.empty.update "a" { ty := .ty .int, lifetime := l }).update "x"
    { ty := .ty (.borrow true [a]), lifetime := l }

def envAfterP : Env :=
  envBeforeP.update "p" { ty := .ty (.borrow false [x]), lifetime := l }

def storeBeforeP : ProgramStore :=
  (ProgramStore.empty.declare "a" l (.int 0)).declare "x" l
    (.ref { location := .var "a", owner := false })

def pValue : Value :=
  .ref { location := .var "x", owner := false }

def storeAfterP : ProgramStore :=
  storeBeforeP.declare "p" l pValue

theorem derefP_typed_mut :
    LValTyping envAfterP (.deref p) (.ty (.borrow true [a])) l := by
  exact LValTyping.borrow
      (LValTyping.var
        (slot := { ty := .ty (.borrow false [x]), lifetime := l })
      (by simp [envAfterP, envBeforeP, l]))
    (LValTargetsTyping.singleton
      (LValTyping.var
        (slot := { ty := .ty (.borrow true [a]), lifetime := l })
        (by simp [envAfterP, envBeforeP, x, l])))

theorem derefDerefP_loc :
    storeAfterP.loc (.deref (.deref p)) = some (.var "a") := by
  simp [storeAfterP, storeBeforeP, pValue, p, l, ProgramStore.declare,
    ProgramStore.update, ProgramStore.loc]

theorem no_updateAtPath_immutableBorrow_deref
    {rank : Nat} {env result : Env} {path : List Unit}
    {targets : List LVal} {rhsTy : Ty} {updatedTy : PartialTy} :
    ¬ UpdateAtPath rank env (() :: path) (.ty (.borrow false targets))
      rhsTy result updatedTy := by
  intro h
  cases h

theorem derefP_not_writable_mut_gate :
    ¬ RuntimeWritableMutGate storeAfterP envAfterP (.deref p) (.var "a") := by
  rintro ⟨targets, bl, rhsTy, result, _htyped, _hloc, hwrite⟩
  cases hwrite with
  | @intro _rank _env₁ env₂ lv slot _ty updatedTy hslot hupdate =>
      have hslotEq :
          slot = { ty := .ty (.borrow false [x]), lifetime := l } := by
        simpa [envAfterP, envBeforeP, p, LVal.base, l] using hslot.symm
      subst hslotEq
      exact no_updateAtPath_immutableBorrow_deref
        (path := [()]) (by
          simpa [p, LVal.path] using hupdate)

theorem no_writable_mut_gate_rooted_p {source : LVal} {leaf : Location} :
    LVal.base source = "p" →
    ¬ RuntimeWritableMutGate storeAfterP envAfterP source leaf := by
  intro hbase
  rintro ⟨targets, bl, rhsTy, result, _htyped, _hloc, hwrite⟩
  cases hwrite with
  | @intro _rank _env₁ env₂ lv slot _ty updatedTy hslot hupdate =>
      have hslotEq :
          slot = { ty := .ty (.borrow false [x]), lifetime := l } := by
        simpa [envAfterP, envBeforeP, LVal.base, hbase, p, l] using
          hslot.symm
      subst hslotEq
      exact no_updateAtPath_immutableBorrow_deref
        (path := LVal.path source) (by
          simpa [LVal.path_deref_cons] using hupdate)

theorem no_valueInstallProvenance_for_immutable_reborrow :
    ¬ ConcreteRuntimeValueInstallProvenance storeAfterP envBeforeP "p" pValue
      (.borrow false [x]) l := by
  intro hprov
  rcases hprov with ⟨R, hexact, _hexcl, hcover⟩
  have hmem : (.var "a", "p") ∈ R :=
    hcover (.deref p) [a] l (.var "a")
      (by simp [p, LVal.base])
      (by simpa [envAfterP, p, x, a, l] using derefP_typed_mut)
      (by simpa [p, a] using derefDerefP_loc)
  rcases hexact.2 (.var "a") "p" hmem with ⟨_howner, hborrow⟩
  cases hborrow

theorem valueWritableInstallProvenance_for_immutable_reborrow :
    ConcreteRuntimeValueWritableInstallProvenance storeAfterP envBeforeP "p"
      pValue (.borrow false [x]) l := by
  simpa [pValue] using
    (ConcreteRuntimeValueWritableInstallProvenance.immBorrow
      (store := storeAfterP) (env := envBeforeP) (owner := "p")
      (lifetime := l) (location := .var "x") (targets := [x]))

/-!
The writable install package is still too narrow for mutable borrows.  If
`q = &mut m` and `m : &mut b`, then the value stored in `q` physically carries
only the reference to `m`, but the freshly installed root exposes a writable gate
through `**q` to `b`.

That is the type-threaded navigation bridge the preservation migration still
needs: writable authority rooted at a newly installed mutable borrow can reach
mutable-borrow leaves already stored in the selected target.
-/

def b : LVal := .var "b"
def m : LVal := .var "m"
def q : LVal := .var "q"

def nestedMutableEnvBeforeQ : Env :=
  (Env.empty.update "b" { ty := .ty .int, lifetime := l }).update "m"
    { ty := .ty (.borrow true [b]), lifetime := l }

def nestedMutableEnvAfterQ : Env :=
  nestedMutableEnvBeforeQ.update "q"
    { ty := .ty (.borrow true [m]), lifetime := l }

def qValue : Value :=
  .ref { location := .var "m", owner := false }

def nestedMutableStoreAfterQ : ProgramStore :=
  ((ProgramStore.empty.declare "b" l (.int 0)).declare "m" l
      (.ref { location := .var "b", owner := false })).declare "q" l qValue

def nestedMutableWriteBResult : Env :=
  nestedMutableEnvAfterQ.update "b" { ty := .ty .int, lifetime := l }

def nestedMutableWriteDerefMResult : Env :=
  nestedMutableWriteBResult.update "m"
    { ty := .ty (.borrow true [b]), lifetime := l }

def nestedMutableWriteDerefDerefQResult : Env :=
  nestedMutableWriteDerefMResult.update "q"
    { ty := .ty (.borrow true [m]), lifetime := l }

theorem nested_derefQ_typed_mut :
    LValTyping nestedMutableEnvAfterQ (.deref q)
      (.ty (.borrow true [b])) l := by
  exact LValTyping.borrow
    (LValTyping.var
      (slot := { ty := .ty (.borrow true [m]), lifetime := l })
      (by simp [nestedMutableEnvAfterQ, nestedMutableEnvBeforeQ, l]))
    (LValTargetsTyping.singleton
      (LValTyping.var
        (slot := { ty := .ty (.borrow true [b]), lifetime := l })
        (by simp [nestedMutableEnvAfterQ, nestedMutableEnvBeforeQ, m, l])))

theorem nested_derefM_typed_int :
    LValTyping nestedMutableEnvAfterQ (.deref m) (.ty .int) l := by
  exact LValTyping.borrow
    (LValTyping.var
      (slot := { ty := .ty (.borrow true [b]), lifetime := l })
      (by simp [nestedMutableEnvAfterQ, nestedMutableEnvBeforeQ, m, l]))
    (LValTargetsTyping.singleton
      (LValTyping.var
        (slot := { ty := .ty .int, lifetime := l })
        (by simp [nestedMutableEnvAfterQ, nestedMutableEnvBeforeQ, b, l])))

theorem nested_derefDerefQ_loc :
    nestedMutableStoreAfterQ.loc (.deref (.deref q)) = some (.var "b") := by
  simp [nestedMutableStoreAfterQ, qValue, q, l, ProgramStore.declare,
    ProgramStore.update, ProgramStore.loc]

theorem nested_write_b :
    EnvWrite 2 nestedMutableEnvAfterQ b .int nestedMutableWriteBResult := by
  exact EnvWrite.intro
    (slot := { ty := .ty .int, lifetime := l })
    (by simp [nestedMutableEnvAfterQ, nestedMutableEnvBeforeQ, b, LVal.base, l])
    (UpdateAtPath.weak ShapeCompatible.int (PartialTyUnion.self (.ty .int)))

theorem nested_write_deref_m :
    EnvWrite 1 nestedMutableEnvAfterQ (.deref m) .int
      nestedMutableWriteDerefMResult := by
  exact EnvWrite.intro
    (env₂ := nestedMutableWriteBResult)
    (updatedTy := .ty (.borrow true [b]))
    (slot := { ty := .ty (.borrow true [b]), lifetime := l })
    (by simp [nestedMutableEnvAfterQ, nestedMutableEnvBeforeQ, m, LVal.base, l])
    (UpdateAtPath.mutBorrow
      (WriteBorrowTargets.singleton nested_write_b
        ⟨.int, l,
          by
            simpa [prependPath, b] using
              (LValTyping.var
                (slot := { ty := .ty .int, lifetime := l })
                (by
                  simp [nestedMutableEnvAfterQ, nestedMutableEnvBeforeQ, b,
                    l]))⟩))

theorem nested_write_deref_deref_q :
    EnvWrite 0 nestedMutableEnvAfterQ (.deref (.deref q)) .int
      nestedMutableWriteDerefDerefQResult := by
  exact EnvWrite.intro
    (env₂ := nestedMutableWriteDerefMResult)
    (updatedTy := .ty (.borrow true [m]))
    (slot := { ty := .ty (.borrow true [m]), lifetime := l })
    (by simp [nestedMutableEnvAfterQ, nestedMutableEnvBeforeQ, q, LVal.base, l])
    (UpdateAtPath.mutBorrow
      (WriteBorrowTargets.singleton nested_write_deref_m
        ⟨.int, l,
          by
            simpa [prependPath, m] using nested_derefM_typed_int⟩))

theorem nested_runtimeWritableGate_derefQ_to_b :
    RuntimeWritableMutGate nestedMutableStoreAfterQ nestedMutableEnvAfterQ
      (.deref q) (.var "b") := by
  exact ⟨[b], l, .int, nestedMutableWriteDerefDerefQResult,
    nested_derefQ_typed_mut,
    by simpa [q, b] using nested_derefDerefQ_loc,
    nested_write_deref_deref_q⟩

theorem top_ref_runtimeValueMutBorrow_leaf_eq {store : ProgramStore}
    {location leaf : Location} {targets : List LVal} :
    RuntimeValueMutBorrow store
      (.value (.ref { location := location, owner := false }))
      (.ty (.borrow true targets)) leaf →
    leaf = location := by
  intro hborrow
  cases hborrow
  rfl

theorem nested_qValue_no_mut_borrow_b :
    ¬ RuntimeValueMutBorrow nestedMutableStoreAfterQ (.value qValue)
      (.ty (.borrow true [m])) (.var "b") := by
  intro hborrow
  have hleaf :
      (.var "b" : Location) = .var "m" := by
    exact top_ref_runtimeValueMutBorrow_leaf_eq
      (store := nestedMutableStoreAfterQ) (location := .var "m")
      (leaf := .var "b") (targets := [.var "m"])
      (by simpa [qValue, m] using hborrow)
  simp at hleaf

theorem no_valueWritableInstallProvenance_for_nested_mutable_borrow :
    ¬ ConcreteRuntimeValueWritableInstallProvenance nestedMutableStoreAfterQ
      nestedMutableEnvBeforeQ "q" qValue (.borrow true [m]) l := by
  intro hprov
  rcases hprov with ⟨R, hexact, _hexcl, hcover⟩
  have hmem : (.var "b", "q") ∈ R :=
    hcover (.deref q) (.var "b") (by simp [q, LVal.base])
      (by
        simpa [nestedMutableEnvAfterQ, q, m, b, l] using
          nested_runtimeWritableGate_derefQ_to_b)
  rcases hexact.2 (.var "b") "q" hmem with ⟨_howner, hborrow⟩
  exact nested_qValue_no_mut_borrow_b hborrow

theorem nestedMutableStoreAfterQ_no_ownsAt
    {owned storage : Location} :
    ¬ ProgramStore.OwnsAt nestedMutableStoreAfterQ owned storage := by
  rintro ⟨ownedLifetime, hslot⟩
  cases storage with
  | var name =>
      by_cases hq : name = "q"
      · subst hq
        simp [nestedMutableStoreAfterQ, qValue, ProgramStore.declare,
          ProgramStore.update, owningRef] at hslot
      · by_cases hm : name = "m"
        · subst hm
          simp [nestedMutableStoreAfterQ, qValue, ProgramStore.declare,
            ProgramStore.update, owningRef] at hslot
        · by_cases hb : name = "b"
          · subst hb
            simp [nestedMutableStoreAfterQ, qValue, ProgramStore.declare,
              ProgramStore.update, owningRef] at hslot
          · simp [nestedMutableStoreAfterQ, qValue, ProgramStore.declare,
              ProgramStore.update, owningRef, hq, hm, hb] at hslot
  | heap address =>
      simp [nestedMutableStoreAfterQ, qValue, ProgramStore.declare,
        ProgramStore.update, owningRef] at hslot

theorem nestedMutableStoreAfterQ_no_ownsTransitively
    {root owned : Location} :
    ¬ ProgramStore.OwnsTransitively nestedMutableStoreAfterQ root owned := by
  intro howns
  induction howns with
  | direct hownsAt =>
      exact nestedMutableStoreAfterQ_no_ownsAt hownsAt
  | trans hownsAt _tail _ih =>
      exact nestedMutableStoreAfterQ_no_ownsAt hownsAt

theorem nestedMutableStoreAfterQ_kill
    {leaf : Location} {z : Name} :
    StoreConcreteBorrowKill nestedMutableStoreAfterQ leaf z := by
  intro value lifetime _hslot hinvalid
  rcases hinvalid with ⟨borrowed, _hborrow, hbelow⟩
  exact nestedMutableStoreAfterQ_no_ownsTransitively hbelow

theorem nestedMutableStoreAfterQ_deref_rooted_q_loc
    {source : LVal} {leaf : Location} :
    LVal.base source = "q" →
    nestedMutableStoreAfterQ.loc (.deref source) = some leaf →
      leaf = .var "m" ∨ leaf = .var "b" := by
  intro hbase hloc
  induction source generalizing leaf with
  | var name =>
      simp [LVal.base] at hbase
      subst hbase
      simp [nestedMutableStoreAfterQ, qValue, ProgramStore.declare,
        ProgramStore.update, ProgramStore.loc] at hloc
      exact Or.inl hloc.symm
  | deref inner ih =>
      change ((nestedMutableStoreAfterQ.loc (.deref inner)).bind
        (fun location =>
          (nestedMutableStoreAfterQ.slotAt location).bind
            (fun slot =>
              match slot.value with
              | .value (.ref ref) => some ref.location
              | .value _ => none
              | .undef => none))) = some leaf at hloc
      cases hinner : nestedMutableStoreAfterQ.loc (.deref inner) with
      | none =>
          rw [hinner] at hloc
          cases hloc
      | some middle =>
          rw [hinner] at hloc
          rcases ih (by simpa [LVal.base] using hbase) hinner with
            hmiddle | hmiddle
          · subst hmiddle
            simp [nestedMutableStoreAfterQ, qValue, ProgramStore.declare,
              ProgramStore.update] at hloc
            exact Or.inr hloc.symm
          · subst hmiddle
            simp [nestedMutableStoreAfterQ, qValue, ProgramStore.declare,
              ProgramStore.update] at hloc

theorem valueWritableAuthorityInstallProvenance_for_nested_mutable_borrow :
    ConcreteRuntimeValueWritableAuthorityInstallProvenance
      nestedMutableStoreAfterQ nestedMutableEnvBeforeQ "q" qValue
      (.borrow true [m]) l := by
  refine ⟨[(.var "m", "q"), (.var "b", "q")], ?_, ?_⟩
  · intro leaf owner hmem z _hz
    rcases List.mem_cons.mp hmem with hhead | htail
    · cases hhead
      exact nestedMutableStoreAfterQ_kill
    · have hpair : (leaf, owner) = (.var "b", "q") :=
        List.mem_singleton.mp htail
      cases hpair
      exact nestedMutableStoreAfterQ_kill
  · intro source leaf hbase hgate
    rcases hgate with ⟨_targets, _bl, _rhsTy, _result, _hsourceTyping, hloc,
      _hwrite⟩
    rcases nestedMutableStoreAfterQ_deref_rooted_q_loc hbase hloc with
      hleaf | hleaf
    · subst hleaf
      simp
    · subst hleaf
      simp

end ProvenanceCounterexample

end Paper
end LwRust
