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
  refine ⟨[], ?_, ?_, ?_⟩
  · constructor
    · intro leaf hborrow
      cases hborrow
    · intro leaf entryOwner hmem
      simp at hmem
  · intro leaf entryOwner hmem _z _hz
    simp at hmem
  · intro source leaf hbase hgate
    exact False.elim (no_writable_mut_gate_rooted_p hbase hgate)

end ProvenanceCounterexample

end Paper
end LwRust
