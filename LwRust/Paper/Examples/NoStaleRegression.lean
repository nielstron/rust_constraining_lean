import LwRust.Paper.Typing

/-!
Regression examples for the assignment-side no-stale side condition.

This module is intentionally typing-only: it imports `Typing`, not the soundness
development, so these examples remain checkable while preservation is being
adapted.
-/

namespace LwRust
namespace Paper

open Core

/-!
Rust accepts this program:

```rust
let mut a = 0;
let mut b = 0;
let c = 0;
let mut d = 0;
let sth = true;

let mut p = &mut a;
let mut q = &mut d;
let mut y = &c;
let mut s = &mut q;

if sth {
    y = &*p;
} else {
    y = &c;
    s = &mut p;
}

*s = &mut b;
let _ = y;
```

The important joined static shape after the `if` is:

```text
p : &mut [a]
q : &mut [d]
y : &[ *p, c ]
s : &mut [ q, p ]
```

The final `*s = &mut b` may statically write `p`, but at runtime that only
happens on the else branch, where `y` is `&c` rather than `&*p`.  The old
`EnvWriteNoStaleBorrowTargets` side condition rejects this joined static shape
because it does not remember that branch correlation.
-/

def noStaleIfA : Name := "a"
def noStaleIfB : Name := "b"
def noStaleIfC : Name := "c"
def noStaleIfD : Name := "d"
def noStaleIfSth : Name := "sth"
def noStaleIfP : Name := "p"
def noStaleIfQ : Name := "q"
def noStaleIfY : Name := "y"
def noStaleIfS : Name := "s"

def noStaleIfALVal : LVal := .var noStaleIfA
def noStaleIfBLVal : LVal := .var noStaleIfB
def noStaleIfCLVal : LVal := .var noStaleIfC
def noStaleIfDLVal : LVal := .var noStaleIfD
def noStaleIfPLVal : LVal := .var noStaleIfP
def noStaleIfQLVal : LVal := .var noStaleIfQ
def noStaleIfYLVal : LVal := .var noStaleIfY
def noStaleIfSLVal : LVal := .var noStaleIfS
def noStaleIfDerefP : LVal := .deref noStaleIfPLVal

def noStaleIfIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def noStaleIfBoolSlot : EnvSlot :=
  { ty := .ty .bool, lifetime := Lifetime.root }

def noStaleIfPSlot : EnvSlot :=
  { ty := .ty (.borrow true [noStaleIfALVal]),
    lifetime := Lifetime.root }

def noStaleIfQSlot : EnvSlot :=
  { ty := .ty (.borrow true [noStaleIfDLVal]),
    lifetime := Lifetime.root }

def noStaleIfYCSlot : EnvSlot :=
  { ty := .ty (.borrow false [noStaleIfCLVal]),
    lifetime := Lifetime.root }

def noStaleIfYDerefPSlot : EnvSlot :=
  { ty := .ty (.borrow false [noStaleIfDerefP]),
    lifetime := Lifetime.root }

def noStaleIfYJoinSlot : EnvSlot :=
  { ty := .ty (.borrow false [noStaleIfDerefP, noStaleIfCLVal]),
    lifetime := Lifetime.root }

def noStaleIfSSlotQ : EnvSlot :=
  { ty := .ty (.borrow true [noStaleIfQLVal]),
    lifetime := Lifetime.root }

def noStaleIfSSlotP : EnvSlot :=
  { ty := .ty (.borrow true [noStaleIfPLVal]),
    lifetime := Lifetime.root }

def noStaleIfSJoinSlot : EnvSlot :=
  { ty := .ty (.borrow true [noStaleIfQLVal, noStaleIfPLVal]),
    lifetime := Lifetime.root }

def noStaleIfPAfterWriteSlot : EnvSlot :=
  { ty := .ty (.borrow true [noStaleIfALVal, noStaleIfBLVal]),
    lifetime := Lifetime.root }

def noStaleIfQAfterWriteSlot : EnvSlot :=
  { ty := .ty (.borrow true [noStaleIfDLVal, noStaleIfBLVal]),
    lifetime := Lifetime.root }

def noStaleIfEnv0 : Env :=
  Env.empty

def noStaleIfEnv1 : Env :=
  noStaleIfEnv0.update noStaleIfA noStaleIfIntSlot

def noStaleIfEnv2 : Env :=
  noStaleIfEnv1.update noStaleIfB noStaleIfIntSlot

def noStaleIfEnv3 : Env :=
  noStaleIfEnv2.update noStaleIfC noStaleIfIntSlot

def noStaleIfEnv4 : Env :=
  noStaleIfEnv3.update noStaleIfD noStaleIfIntSlot

def noStaleIfEnv5 : Env :=
  noStaleIfEnv4.update noStaleIfSth noStaleIfBoolSlot

def noStaleIfEnv6 : Env :=
  noStaleIfEnv5.update noStaleIfP noStaleIfPSlot

def noStaleIfEnv7 : Env :=
  noStaleIfEnv6.update noStaleIfQ noStaleIfQSlot

def noStaleIfEnv8 : Env :=
  noStaleIfEnv7.update noStaleIfY noStaleIfYCSlot

def noStaleIfEnv9 : Env :=
  noStaleIfEnv8.update noStaleIfS noStaleIfSSlotQ

def noStaleIfTrueEnv : Env :=
  noStaleIfEnv9.update noStaleIfY noStaleIfYDerefPSlot

def noStaleIfFalseEnv : Env :=
  noStaleIfEnv9.update noStaleIfS noStaleIfSSlotP

def noStaleIfJoinEnv : Env :=
  (noStaleIfEnv9.update noStaleIfY noStaleIfYJoinSlot).update
    noStaleIfS noStaleIfSJoinSlot

def noStaleIfAfterWriteEnv : Env :=
  ((noStaleIfJoinEnv.update noStaleIfP noStaleIfPAfterWriteSlot).update
    noStaleIfQ noStaleIfQAfterWriteSlot)

def noStaleIfTerms : List Term :=
  [.letMut noStaleIfA (.val (.int 0)),
   .letMut noStaleIfB (.val (.int 0)),
   .letMut noStaleIfC (.val (.int 0)),
   .letMut noStaleIfD (.val (.int 0)),
   .letMut noStaleIfSth (.val (.bool true)),
   .letMut noStaleIfP (.borrow true noStaleIfALVal),
   .letMut noStaleIfQ (.borrow true noStaleIfDLVal),
   .letMut noStaleIfY (.borrow false noStaleIfCLVal),
   .letMut noStaleIfS (.borrow true noStaleIfQLVal),
   .ite (.copy (.var noStaleIfSth))
     (.assign noStaleIfYLVal (.borrow false noStaleIfDerefP))
     (.block Lifetime.root
       [.assign noStaleIfYLVal (.borrow false noStaleIfCLVal),
        .assign noStaleIfSLVal (.borrow true noStaleIfPLVal)]),
   .assign (.deref noStaleIfSLVal) (.borrow true noStaleIfBLVal)]

theorem noStaleIf_afterWrite_y_slot :
    noStaleIfAfterWriteEnv.slotAt noStaleIfY =
      some noStaleIfYJoinSlot := by
  simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv, noStaleIfEnv9,
    noStaleIfEnv8, noStaleIfEnv7, noStaleIfEnv6, noStaleIfEnv5,
    noStaleIfEnv4, noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
    noStaleIfEnv0, noStaleIfA, noStaleIfB, noStaleIfC, noStaleIfD,
    noStaleIfSth, noStaleIfP, noStaleIfQ, noStaleIfY, noStaleIfS,
    Env.update]

theorem noStaleIf_afterWrite_y_contains :
    noStaleIfAfterWriteEnv ⊢ noStaleIfY ↝
      (.borrow false [noStaleIfDerefP, noStaleIfCLVal]) :=
  ⟨noStaleIfYJoinSlot, noStaleIf_afterWrite_y_slot, PartialTyContains.here⟩

theorem noStaleIf_p_may_read_through_deref_p :
    EnvMayReadThrough noStaleIfAfterWriteEnv noStaleIfPLVal
      noStaleIfDerefP :=
  EnvMayReadThrough.direct (LVal.StrictPrefixOf.self_deref noStaleIfPLVal)

theorem noStaleIf_final_write_rejected_by_noStale
    (hwriteP :
      EnvWriteEffectiveWrite 0 noStaleIfJoinEnv (.deref noStaleIfSLVal)
        (.borrow true [noStaleIfBLVal]) noStaleIfAfterWriteEnv
        noStaleIfPLVal) :
    ¬ EnvWriteNoStaleBorrowTargets 0 noStaleIfJoinEnv
      (.deref noStaleIfSLVal) (.borrow true [noStaleIfBLVal])
      noStaleIfAfterWriteEnv := by
  intro hnoStale
  exact hnoStale noStaleIfPLVal noStaleIfY noStaleIfYJoinSlot false
    [noStaleIfDerefP, noStaleIfCLVal] noStaleIfDerefP hwriteP
    noStaleIf_afterWrite_y_slot noStaleIf_afterWrite_y_contains
    (by simp [noStaleIfDerefP]) noStaleIf_p_may_read_through_deref_p

end Paper
end LwRust
