import LwRust.Paper.Soundness.Helpers.AppendixPrelim

/-!
Regression examples for the assignment-side no-stale side condition.

This module stays independent of preservation and the final soundness theorem.
It imports the preliminary inversion helpers only to keep the finite typing
proofs readable.
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

@[simp] theorem noStaleIfJoin_slot_a :
    noStaleIfJoinEnv.slotAt noStaleIfA = some noStaleIfIntSlot := by
  simp [noStaleIfJoinEnv, noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
    noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
    noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0, noStaleIfA,
    noStaleIfB, noStaleIfC, noStaleIfD, noStaleIfSth, noStaleIfP,
    noStaleIfQ, noStaleIfY, noStaleIfS, Env.update]

@[simp] theorem noStaleIfJoin_slot_b :
    noStaleIfJoinEnv.slotAt noStaleIfB = some noStaleIfIntSlot := by
  simp [noStaleIfJoinEnv, noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
    noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
    noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0, noStaleIfA,
    noStaleIfB, noStaleIfC, noStaleIfD, noStaleIfSth, noStaleIfP,
    noStaleIfQ, noStaleIfY, noStaleIfS, Env.update]

@[simp] theorem noStaleIfJoin_slot_c :
    noStaleIfJoinEnv.slotAt noStaleIfC = some noStaleIfIntSlot := by
  simp [noStaleIfJoinEnv, noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
    noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
    noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0, noStaleIfA,
    noStaleIfB, noStaleIfC, noStaleIfD, noStaleIfSth, noStaleIfP,
    noStaleIfQ, noStaleIfY, noStaleIfS, Env.update]

@[simp] theorem noStaleIfJoin_slot_d :
    noStaleIfJoinEnv.slotAt noStaleIfD = some noStaleIfIntSlot := by
  simp [noStaleIfJoinEnv, noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
    noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
    noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0, noStaleIfA,
    noStaleIfB, noStaleIfC, noStaleIfD, noStaleIfSth, noStaleIfP,
    noStaleIfQ, noStaleIfY, noStaleIfS, Env.update]

@[simp] theorem noStaleIfJoin_slot_p :
    noStaleIfJoinEnv.slotAt noStaleIfP = some noStaleIfPSlot := by
  simp [noStaleIfJoinEnv, noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
    noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
    noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0, noStaleIfA,
    noStaleIfB, noStaleIfC, noStaleIfD, noStaleIfSth, noStaleIfP,
    noStaleIfQ, noStaleIfY, noStaleIfS, Env.update]

@[simp] theorem noStaleIfJoin_slot_q :
    noStaleIfJoinEnv.slotAt noStaleIfQ = some noStaleIfQSlot := by
  simp [noStaleIfJoinEnv, noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
    noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
    noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0, noStaleIfA,
    noStaleIfB, noStaleIfC, noStaleIfD, noStaleIfSth, noStaleIfP,
    noStaleIfQ, noStaleIfY, noStaleIfS, Env.update]

@[simp] theorem noStaleIfJoin_slot_y :
    noStaleIfJoinEnv.slotAt noStaleIfY = some noStaleIfYJoinSlot := by
  simp [noStaleIfJoinEnv, noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
    noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
    noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0, noStaleIfA,
    noStaleIfB, noStaleIfC, noStaleIfD, noStaleIfSth, noStaleIfP,
    noStaleIfQ, noStaleIfY, noStaleIfS, Env.update]

@[simp] theorem noStaleIfJoin_slot_s :
    noStaleIfJoinEnv.slotAt noStaleIfS = some noStaleIfSJoinSlot := by
  simp [noStaleIfJoinEnv, Env.update]

@[simp] theorem noStaleIfAfterWrite_slot_a :
    noStaleIfAfterWriteEnv.slotAt noStaleIfA = some noStaleIfIntSlot := by
  simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv, noStaleIfEnv9,
    noStaleIfEnv8, noStaleIfEnv7, noStaleIfEnv6, noStaleIfEnv5,
    noStaleIfEnv4, noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
    noStaleIfEnv0, noStaleIfA, noStaleIfB, noStaleIfC, noStaleIfD,
    noStaleIfSth, noStaleIfP, noStaleIfQ, noStaleIfY, noStaleIfS,
    Env.update]

@[simp] theorem noStaleIfAfterWrite_slot_b :
    noStaleIfAfterWriteEnv.slotAt noStaleIfB = some noStaleIfIntSlot := by
  simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv, noStaleIfEnv9,
    noStaleIfEnv8, noStaleIfEnv7, noStaleIfEnv6, noStaleIfEnv5,
    noStaleIfEnv4, noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
    noStaleIfEnv0, noStaleIfA, noStaleIfB, noStaleIfC, noStaleIfD,
    noStaleIfSth, noStaleIfP, noStaleIfQ, noStaleIfY, noStaleIfS,
    Env.update]

@[simp] theorem noStaleIfAfterWrite_slot_c :
    noStaleIfAfterWriteEnv.slotAt noStaleIfC = some noStaleIfIntSlot := by
  simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv, noStaleIfEnv9,
    noStaleIfEnv8, noStaleIfEnv7, noStaleIfEnv6, noStaleIfEnv5,
    noStaleIfEnv4, noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
    noStaleIfEnv0, noStaleIfA, noStaleIfB, noStaleIfC, noStaleIfD,
    noStaleIfSth, noStaleIfP, noStaleIfQ, noStaleIfY, noStaleIfS,
    Env.update]

@[simp] theorem noStaleIfAfterWrite_slot_d :
    noStaleIfAfterWriteEnv.slotAt noStaleIfD = some noStaleIfIntSlot := by
  simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv, noStaleIfEnv9,
    noStaleIfEnv8, noStaleIfEnv7, noStaleIfEnv6, noStaleIfEnv5,
    noStaleIfEnv4, noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
    noStaleIfEnv0, noStaleIfA, noStaleIfB, noStaleIfC, noStaleIfD,
    noStaleIfSth, noStaleIfP, noStaleIfQ, noStaleIfY, noStaleIfS,
    Env.update]

@[simp] theorem noStaleIfAfterWrite_slot_p :
    noStaleIfAfterWriteEnv.slotAt noStaleIfP =
      some noStaleIfPAfterWriteSlot := by
  simp [noStaleIfAfterWriteEnv, noStaleIfP, noStaleIfQ, Env.update]

@[simp] theorem noStaleIfAfterWrite_slot_q :
    noStaleIfAfterWriteEnv.slotAt noStaleIfQ =
      some noStaleIfQAfterWriteSlot := by
  simp [noStaleIfAfterWriteEnv, noStaleIfP, noStaleIfQ, Env.update]

@[simp] theorem noStaleIfAfterWrite_slot_s :
    noStaleIfAfterWriteEnv.slotAt noStaleIfS = some noStaleIfSJoinSlot := by
  simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv, noStaleIfP, noStaleIfQ,
    noStaleIfS, Env.update]

theorem noStaleIfJoin_a_typing :
    LValTyping noStaleIfJoinEnv noStaleIfALVal (.ty .int) Lifetime.root :=
  LValTyping.var noStaleIfJoin_slot_a

theorem noStaleIfJoin_b_typing :
    LValTyping noStaleIfJoinEnv noStaleIfBLVal (.ty .int) Lifetime.root :=
  LValTyping.var noStaleIfJoin_slot_b

theorem noStaleIfJoin_c_typing :
    LValTyping noStaleIfJoinEnv noStaleIfCLVal (.ty .int) Lifetime.root :=
  LValTyping.var noStaleIfJoin_slot_c

theorem noStaleIfJoin_d_typing :
    LValTyping noStaleIfJoinEnv noStaleIfDLVal (.ty .int) Lifetime.root :=
  LValTyping.var noStaleIfJoin_slot_d

theorem noStaleIfJoin_p_typing :
    LValTyping noStaleIfJoinEnv noStaleIfPLVal
      (.ty (.borrow true [noStaleIfALVal])) Lifetime.root :=
  LValTyping.var noStaleIfJoin_slot_p

theorem noStaleIfJoin_q_typing :
    LValTyping noStaleIfJoinEnv noStaleIfQLVal
      (.ty (.borrow true [noStaleIfDLVal])) Lifetime.root :=
  LValTyping.var noStaleIfJoin_slot_q

theorem noStaleIfJoin_y_typing :
    LValTyping noStaleIfJoinEnv noStaleIfYLVal
      (.ty (.borrow false [noStaleIfDerefP, noStaleIfCLVal]))
      Lifetime.root :=
  LValTyping.var noStaleIfJoin_slot_y

theorem noStaleIfJoin_s_typing :
    LValTyping noStaleIfJoinEnv noStaleIfSLVal
      (.ty (.borrow true [noStaleIfQLVal, noStaleIfPLVal]))
      Lifetime.root :=
  LValTyping.var noStaleIfJoin_slot_s

theorem noStaleIfAfterWrite_a_typing :
    LValTyping noStaleIfAfterWriteEnv noStaleIfALVal (.ty .int)
      Lifetime.root :=
  LValTyping.var noStaleIfAfterWrite_slot_a

theorem noStaleIfAfterWrite_b_typing :
    LValTyping noStaleIfAfterWriteEnv noStaleIfBLVal (.ty .int)
      Lifetime.root :=
  LValTyping.var noStaleIfAfterWrite_slot_b

theorem noStaleIfAfterWrite_c_typing :
    LValTyping noStaleIfAfterWriteEnv noStaleIfCLVal (.ty .int)
      Lifetime.root :=
  LValTyping.var noStaleIfAfterWrite_slot_c

theorem noStaleIfAfterWrite_d_typing :
    LValTyping noStaleIfAfterWriteEnv noStaleIfDLVal (.ty .int)
      Lifetime.root :=
  LValTyping.var noStaleIfAfterWrite_slot_d

theorem noStaleIfAfterWrite_p_typing :
    LValTyping noStaleIfAfterWriteEnv noStaleIfPLVal
      (.ty (.borrow true [noStaleIfALVal, noStaleIfBLVal]))
      Lifetime.root :=
  LValTyping.var noStaleIfAfterWrite_slot_p

theorem noStaleIfAfterWrite_q_typing :
    LValTyping noStaleIfAfterWriteEnv noStaleIfQLVal
      (.ty (.borrow true [noStaleIfDLVal, noStaleIfBLVal]))
      Lifetime.root :=
  LValTyping.var noStaleIfAfterWrite_slot_q

theorem noStaleIfAfterWrite_s_typing :
    LValTyping noStaleIfAfterWriteEnv noStaleIfSLVal
      (.ty (.borrow true [noStaleIfQLVal, noStaleIfPLVal]))
      Lifetime.root :=
  LValTyping.var noStaleIfAfterWrite_slot_s

theorem noStaleIf_env_ext (left right : Env)
    (h : ∀ x, left.slotAt x = right.slotAt x) : left = right := by
  cases left with
  | mk leftSlotAt =>
      cases right with
      | mk rightSlotAt =>
          have hfun : leftSlotAt = rightSlotAt := funext h
          subst hfun
          rfl

theorem noStaleIfAfterWrite_update_s_eq :
    noStaleIfAfterWriteEnv.update noStaleIfS noStaleIfSJoinSlot =
      noStaleIfAfterWriteEnv := by
  apply noStaleIf_env_ext
  intro name
  by_cases hs : name = noStaleIfS
  · subst hs
    simp [Env.update, noStaleIfAfterWrite_slot_s]
  · simp [Env.update, hs]

theorem noStaleIf_partialTyStrengthens_borrow_subset {mutable : Bool}
    {leftTargets rightTargets : List LVal} :
    PartialTyStrengthens (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets)) →
    leftTargets.Subset rightTargets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      intro target hmem
      exact hmem
  | borrow hsubset =>
      exact hsubset

theorem noStaleIf_partialTyStrengthens_from_borrow_inv {mutable : Bool}
    {sourceTargets : List LVal} {targetTy : Ty} :
    PartialTyStrengthens (.ty (.borrow mutable sourceTargets)) (.ty targetTy) →
    ∃ targetTargets,
      targetTy = .borrow mutable targetTargets ∧
        sourceTargets.Subset targetTargets := by
  intro hstrength
  cases hstrength with
  | reflex =>
      exact ⟨sourceTargets, rfl, by intro target hmem; exact hmem⟩
  | borrow hsubset =>
      exact ⟨_, rfl, hsubset⟩

theorem noStaleIf_partialTyStrengthens_borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal} {joined : PartialTy}
    (hleft : PartialTyStrengthens (.ty (.borrow mutable leftTargets)) joined)
    (hright : PartialTyStrengthens (.ty (.borrow mutable rightTargets)) joined) :
    PartialTyStrengthens (.ty (.borrow mutable (leftTargets ++ rightTargets)))
      joined := by
  cases hleft with
  | reflex =>
      have hsubRight := noStaleIf_partialTyStrengthens_borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hmem
        · exact hsubRight hmem)
  | borrow hsubLeft =>
      have hsubRight := noStaleIf_partialTyStrengthens_borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem)
  | intoUndef hinner =>
      rcases noStaleIf_partialTyStrengthens_from_borrow_inv hinner with
        ⟨targetTargets, htargetEq, hsubLeft⟩
      cases htargetEq
      have hsubRight : rightTargets ⊆ targetTargets := by
        cases hright with
        | intoUndef hinner' =>
            exact noStaleIf_partialTyStrengthens_borrow_subset hinner'
      exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem))

theorem noStaleIf_borrow_union_da :
    PartialTyUnion
      (.ty (.borrow true [noStaleIfDLVal]))
      (.ty (.borrow true [noStaleIfALVal]))
      (.ty (.borrow true [noStaleIfDLVal, noStaleIfALVal])) := by
  constructor
  · intro candidate hcandidate
    rcases hcandidate with hleft | hright
    · subst hleft
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inl htarget)
    · subst hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inr htarget)
  · intro upper hupper
    have hleft :
        PartialTyStrengthens (.ty (.borrow true [noStaleIfDLVal])) upper :=
      hupper _ (by simp)
    have hright :
        PartialTyStrengthens (.ty (.borrow true [noStaleIfALVal])) upper :=
      hupper _ (by simp)
    simpa using
      (noStaleIf_partialTyStrengthens_borrow_append hleft hright)

theorem noStaleIf_borrow_union_ab :
    PartialTyUnion
      (.ty (.borrow true [noStaleIfALVal]))
      (.ty (.borrow true [noStaleIfBLVal]))
      (.ty (.borrow true [noStaleIfALVal, noStaleIfBLVal])) := by
  constructor
  · intro candidate hcandidate
    rcases hcandidate with hleft | hright
    · subst hleft
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inl htarget)
    · subst hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inr htarget)
  · intro upper hupper
    have hleft :
        PartialTyStrengthens (.ty (.borrow true [noStaleIfALVal])) upper :=
      hupper _ (by simp)
    have hright :
        PartialTyStrengthens (.ty (.borrow true [noStaleIfBLVal])) upper :=
      hupper _ (by simp)
    simpa using
      (noStaleIf_partialTyStrengthens_borrow_append hleft hright)

theorem noStaleIf_borrow_union_db :
    PartialTyUnion
      (.ty (.borrow true [noStaleIfDLVal]))
      (.ty (.borrow true [noStaleIfBLVal]))
      (.ty (.borrow true [noStaleIfDLVal, noStaleIfBLVal])) := by
  constructor
  · intro candidate hcandidate
    rcases hcandidate with hleft | hright
    · subst hleft
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inl htarget)
    · subst hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        exact Or.inr htarget)
  · intro upper hupper
    have hleft :
        PartialTyStrengthens (.ty (.borrow true [noStaleIfDLVal])) upper :=
      hupper _ (by simp)
    have hright :
        PartialTyStrengthens (.ty (.borrow true [noStaleIfBLVal])) upper :=
      hupper _ (by simp)
    simpa using
      (noStaleIf_partialTyStrengthens_borrow_append hleft hright)

theorem noStaleIf_borrow_union_db_ab :
    PartialTyUnion
      (.ty (.borrow true [noStaleIfDLVal, noStaleIfBLVal]))
      (.ty (.borrow true [noStaleIfALVal, noStaleIfBLVal]))
      (.ty (.borrow true
        [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal, noStaleIfBLVal])) := by
  constructor
  · intro candidate hcandidate
    rcases hcandidate with hleft | hright
    · subst hleft
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        rcases htarget with htarget | htarget
        · exact Or.inl htarget
        · exact Or.inr (Or.inl htarget))
    · subst hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        simp at htarget ⊢
        rcases htarget with htarget | htarget
        · exact Or.inr (Or.inr (Or.inl htarget))
        · exact Or.inr (Or.inl htarget))
  · intro upper hupper
    have hleft :
        PartialTyStrengthens
          (.ty (.borrow true [noStaleIfDLVal, noStaleIfBLVal])) upper :=
      hupper _ (by simp)
    have hright :
        PartialTyStrengthens
          (.ty (.borrow true [noStaleIfALVal, noStaleIfBLVal])) upper :=
      hupper _ (by simp)
    simpa using
      (noStaleIf_partialTyStrengthens_borrow_append hleft hright)

theorem noStaleIfJoin_qp_targets_typing :
    LValTargetsTyping noStaleIfJoinEnv [noStaleIfQLVal, noStaleIfPLVal]
      (.ty (.borrow true [noStaleIfDLVal, noStaleIfALVal]))
      Lifetime.root :=
  LValTargetsTyping.cons noStaleIfJoin_q_typing
    (LValTargetsTyping.singleton noStaleIfJoin_p_typing)
    noStaleIf_borrow_union_da
    (LifetimeIntersection.self Lifetime.root)

theorem noStaleIfJoin_deref_s_typing :
    LValTyping noStaleIfJoinEnv (.deref noStaleIfSLVal)
      (.ty (.borrow true [noStaleIfDLVal, noStaleIfALVal]))
      Lifetime.root :=
  LValTyping.borrow noStaleIfJoin_s_typing noStaleIfJoin_qp_targets_typing

theorem noStaleIfAfterWrite_ab_targets_typing :
    LValTargetsTyping noStaleIfAfterWriteEnv
      [noStaleIfALVal, noStaleIfBLVal] (.ty .int) Lifetime.root :=
  LValTargetsTyping.cons noStaleIfAfterWrite_a_typing
    (LValTargetsTyping.singleton noStaleIfAfterWrite_b_typing)
    (PartialTyUnion.self (.ty .int))
    (LifetimeIntersection.self Lifetime.root)

theorem noStaleIfAfterWrite_db_targets_typing :
    LValTargetsTyping noStaleIfAfterWriteEnv
      [noStaleIfDLVal, noStaleIfBLVal] (.ty .int) Lifetime.root :=
  LValTargetsTyping.cons noStaleIfAfterWrite_d_typing
    (LValTargetsTyping.singleton noStaleIfAfterWrite_b_typing)
    (PartialTyUnion.self (.ty .int))
    (LifetimeIntersection.self Lifetime.root)

theorem noStaleIfAfterWrite_dbab_targets_typing :
    LValTargetsTyping noStaleIfAfterWriteEnv
      [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal, noStaleIfBLVal]
      (.ty .int) Lifetime.root :=
  LValTargetsTyping.cons noStaleIfAfterWrite_d_typing
    (LValTargetsTyping.cons noStaleIfAfterWrite_b_typing
      (LValTargetsTyping.cons noStaleIfAfterWrite_a_typing
        (LValTargetsTyping.singleton noStaleIfAfterWrite_b_typing)
        (PartialTyUnion.self (.ty .int))
        (LifetimeIntersection.self Lifetime.root))
      (PartialTyUnion.self (.ty .int))
      (LifetimeIntersection.self Lifetime.root))
    (PartialTyUnion.self (.ty .int))
    (LifetimeIntersection.self Lifetime.root)

theorem noStaleIfAfterWrite_qp_targets_typing :
    LValTargetsTyping noStaleIfAfterWriteEnv [noStaleIfQLVal, noStaleIfPLVal]
      (.ty (.borrow true
        [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal, noStaleIfBLVal]))
      Lifetime.root :=
  LValTargetsTyping.cons noStaleIfAfterWrite_q_typing
    (LValTargetsTyping.singleton noStaleIfAfterWrite_p_typing)
    noStaleIf_borrow_union_db_ab
    (LifetimeIntersection.self Lifetime.root)

theorem noStaleIfAfterWrite_deref_p_typing :
    LValTyping noStaleIfAfterWriteEnv (.deref noStaleIfPLVal) (.ty .int)
      Lifetime.root :=
  LValTyping.borrow noStaleIfAfterWrite_p_typing
    noStaleIfAfterWrite_ab_targets_typing

theorem noStaleIfAfterWrite_deref_p_c_targets_typing :
    LValTargetsTyping noStaleIfAfterWriteEnv
      [noStaleIfDerefP, noStaleIfCLVal] (.ty .int) Lifetime.root :=
  LValTargetsTyping.cons noStaleIfAfterWrite_deref_p_typing
    (LValTargetsTyping.singleton noStaleIfAfterWrite_c_typing)
    (PartialTyUnion.self (.ty .int))
    (LifetimeIntersection.self Lifetime.root)

theorem noStaleIfAfterWrite_deref_s_typing :
    LValTyping noStaleIfAfterWriteEnv (.deref noStaleIfSLVal)
      (.ty (.borrow true
        [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal, noStaleIfBLVal]))
      Lifetime.root :=
  LValTyping.borrow noStaleIfAfterWrite_s_typing
    noStaleIfAfterWrite_qp_targets_typing

theorem noStaleIf_shape_deref_s_rhs :
    ShapeCompatible noStaleIfJoinEnv
      (.ty (.borrow true [noStaleIfDLVal, noStaleIfALVal]))
      (.ty (.borrow true [noStaleIfBLVal])) := by
  exact ShapeCompatible.borrow
    (fun target htarget => by
      simp at htarget
      rcases htarget with htarget | htarget
      · subst htarget
        exact ⟨Lifetime.root, noStaleIfJoin_d_typing⟩
      · subst htarget
        exact ⟨Lifetime.root, noStaleIfJoin_a_typing⟩)
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, noStaleIfJoin_b_typing⟩)
    ShapeCompatible.int

theorem noStaleIf_borrow_b_wellFormed :
    WellFormedTy noStaleIfJoinEnv (.borrow true [noStaleIfBLVal])
      Lifetime.root := by
  exact WellFormedTy.borrow (BorrowTargetsWellFormed.intro (by
    intro target htarget
    simp at htarget
    subst htarget
    exact ⟨.int, Lifetime.root, noStaleIfJoin_b_typing,
      LifetimeOutlives.refl Lifetime.root,
      ⟨noStaleIfIntSlot, by simpa [noStaleIfBLVal, LVal.base],
        LifetimeOutlives.refl Lifetime.root⟩⟩))

theorem noStaleIf_shape_p_rhs :
    ShapeCompatible noStaleIfJoinEnv
      (.ty (.borrow true [noStaleIfALVal]))
      (.ty (.borrow true [noStaleIfBLVal])) := by
  exact ShapeCompatible.borrow
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, noStaleIfJoin_a_typing⟩)
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, noStaleIfJoin_b_typing⟩)
    ShapeCompatible.int

theorem noStaleIf_shape_q_rhs :
    ShapeCompatible noStaleIfJoinEnv
      (.ty (.borrow true [noStaleIfDLVal]))
      (.ty (.borrow true [noStaleIfBLVal])) := by
  exact ShapeCompatible.borrow
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, noStaleIfJoin_d_typing⟩)
    (fun target htarget => by
      simp at htarget
      subst htarget
      exact ⟨Lifetime.root, noStaleIfJoin_b_typing⟩)
    ShapeCompatible.int

theorem noStaleIf_write_p :
    EnvWrite 1 noStaleIfJoinEnv noStaleIfPLVal
      (.borrow true [noStaleIfBLVal])
      (noStaleIfJoinEnv.update noStaleIfP noStaleIfPAfterWriteSlot) := by
  simpa [noStaleIfPLVal, noStaleIfPSlot, noStaleIfPAfterWriteSlot, LVal.base] using
    (@EnvWrite.intro 1 noStaleIfJoinEnv noStaleIfJoinEnv noStaleIfPLVal
      noStaleIfPSlot (.borrow true [noStaleIfBLVal])
      (.ty (.borrow true [noStaleIfALVal, noStaleIfBLVal]))
      noStaleIfJoin_slot_p
      (UpdateAtPath.weak noStaleIf_shape_p_rhs noStaleIf_borrow_union_ab))

theorem noStaleIf_write_q :
    EnvWrite 1 noStaleIfJoinEnv noStaleIfQLVal
      (.borrow true [noStaleIfBLVal])
      (noStaleIfJoinEnv.update noStaleIfQ noStaleIfQAfterWriteSlot) := by
  simpa [noStaleIfQLVal, noStaleIfQSlot, noStaleIfQAfterWriteSlot, LVal.base] using
    (@EnvWrite.intro 1 noStaleIfJoinEnv noStaleIfJoinEnv noStaleIfQLVal
      noStaleIfQSlot (.borrow true [noStaleIfBLVal])
      (.ty (.borrow true [noStaleIfDLVal, noStaleIfBLVal]))
      noStaleIfJoin_slot_q
      (UpdateAtPath.weak noStaleIf_shape_q_rhs noStaleIf_borrow_union_db))

theorem noStaleIf_write_qp_join :
    EnvJoin
      (noStaleIfJoinEnv.update noStaleIfQ noStaleIfQAfterWriteSlot)
      (noStaleIfJoinEnv.update noStaleIfP noStaleIfPAfterWriteSlot)
      noStaleIfAfterWriteEnv := by
  constructor
  · intro candidate hcandidate
    rcases hcandidate with hleft | hright
    · subst hleft
      intro name
      by_cases hp : name = noStaleIfP
      · subst hp
        have hslotP : noStaleIfJoinEnv.slotAt "p" = some noStaleIfPSlot := by
          simpa [noStaleIfP] using noStaleIfJoin_slot_p
        simp [noStaleIfAfterWriteEnv, Env.update, noStaleIfP, noStaleIfQ,
          hslotP]
        simpa [noStaleIfPSlot, noStaleIfPAfterWriteSlot] using
          (PartialTyStrengthens.borrow (by
            intro target htarget
            simp at htarget ⊢
            exact Or.inl htarget) :
            PartialTyStrengthens
              (.ty (.borrow true [noStaleIfALVal]))
              (.ty (.borrow true [noStaleIfALVal, noStaleIfBLVal])))
      · by_cases hq : name = noStaleIfQ
        · subst hq
          simp [EnvStrengthens, noStaleIfAfterWriteEnv, Env.update,
            noStaleIfP, noStaleIfQ]
        · cases hslot : noStaleIfJoinEnv.slotAt name <;>
            simp [EnvStrengthens, noStaleIfAfterWriteEnv, Env.update, hp, hq,
              hslot]
    · subst hright
      intro name
      by_cases hp : name = noStaleIfP
      · subst hp
        simp [EnvStrengthens, noStaleIfAfterWriteEnv, Env.update,
          noStaleIfP, noStaleIfQ]
      · by_cases hq : name = noStaleIfQ
        · subst hq
          have hslotQ : noStaleIfJoinEnv.slotAt "q" = some noStaleIfQSlot := by
            simpa [noStaleIfQ] using noStaleIfJoin_slot_q
          simp [noStaleIfAfterWriteEnv, Env.update, noStaleIfP, noStaleIfQ,
            hslotQ]
          simpa [noStaleIfQSlot, noStaleIfQAfterWriteSlot] using
            (PartialTyStrengthens.borrow (by
              intro target htarget
              simp at htarget ⊢
              exact Or.inl htarget) :
              PartialTyStrengthens
                (.ty (.borrow true [noStaleIfDLVal]))
                (.ty (.borrow true [noStaleIfDLVal, noStaleIfBLVal])))
        · cases hslot : noStaleIfJoinEnv.slotAt name <;>
            simp [EnvStrengthens, noStaleIfAfterWriteEnv, Env.update, hp, hq,
              hslot]
  · intro upper hupper name
    by_cases hp : name = noStaleIfP
    · subst hp
      have h :=
        hupper (noStaleIfJoinEnv.update noStaleIfP noStaleIfPAfterWriteSlot)
          (by simp) noStaleIfP
      simpa [noStaleIfAfterWriteEnv, Env.update, noStaleIfP, noStaleIfQ]
        using h
    · by_cases hq : name = noStaleIfQ
      · subst hq
        have h :=
          hupper (noStaleIfJoinEnv.update noStaleIfQ noStaleIfQAfterWriteSlot)
            (by simp) noStaleIfQ
        simpa [noStaleIfAfterWriteEnv, Env.update, noStaleIfP, noStaleIfQ]
          using h
      · have h :=
          hupper (noStaleIfJoinEnv.update noStaleIfQ noStaleIfQAfterWriteSlot)
            (by simp) name
        simpa [noStaleIfAfterWriteEnv, Env.update, hp, hq] using h

theorem noStaleIf_write_qp_targets :
    WriteBorrowTargets 1 noStaleIfJoinEnv []
      [noStaleIfQLVal, noStaleIfPLVal] (.borrow true [noStaleIfBLVal])
      noStaleIfAfterWriteEnv := by
  exact WriteBorrowTargets.cons noStaleIf_write_q
    ⟨.borrow true [noStaleIfDLVal], Lifetime.root, noStaleIfJoin_q_typing⟩
    (WriteBorrowTargets.singleton noStaleIf_write_p
      ⟨.borrow true [noStaleIfALVal], Lifetime.root, noStaleIfJoin_p_typing⟩)
    noStaleIf_write_qp_join

theorem noStaleIf_write_deref_s :
    EnvWrite 0 noStaleIfJoinEnv (.deref noStaleIfSLVal)
      (.borrow true [noStaleIfBLVal]) noStaleIfAfterWriteEnv := by
  have hwrite :
      EnvWrite 0 noStaleIfJoinEnv (.deref noStaleIfSLVal)
        (.borrow true [noStaleIfBLVal])
        (noStaleIfAfterWriteEnv.update noStaleIfS noStaleIfSJoinSlot) := by
    simpa [noStaleIfSLVal, noStaleIfSJoinSlot, LVal.base, LVal.path] using
      (@EnvWrite.intro 0 noStaleIfJoinEnv noStaleIfAfterWriteEnv
        (.deref noStaleIfSLVal) noStaleIfSJoinSlot
        (.borrow true [noStaleIfBLVal])
        (.ty (.borrow true [noStaleIfQLVal, noStaleIfPLVal]))
        noStaleIfJoin_slot_s
        (@UpdateAtPath.mutBorrow noStaleIfJoinEnv noStaleIfAfterWriteEnv
          0 [] [noStaleIfQLVal, noStaleIfPLVal]
          (.borrow true [noStaleIfBLVal]) noStaleIf_write_qp_targets))
  simpa [noStaleIfAfterWrite_update_s_eq] using hwrite

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

theorem noStaleIfJoin_contains_inv {x mutable targets} :
    noStaleIfJoinEnv ⊢ x ↝ (.borrow mutable targets) →
      (x = noStaleIfP ∧ mutable = true ∧
        targets = [noStaleIfALVal]) ∨
      (x = noStaleIfQ ∧ mutable = true ∧
        targets = [noStaleIfDLVal]) ∨
      (x = noStaleIfY ∧ mutable = false ∧
        targets = [noStaleIfDerefP, noStaleIfCLVal]) ∨
      (x = noStaleIfS ∧ mutable = true ∧
        targets = [noStaleIfQLVal, noStaleIfPLVal]) := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hp : x = noStaleIfP
  · subst hp
    have hslotEq : slot = noStaleIfPSlot :=
      Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_p)
    subst hslotEq
    simp [noStaleIfPSlot] at hcontainsTy
    cases hcontainsTy
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · by_cases hq : x = noStaleIfQ
    · subst hq
      have hslotEq : slot = noStaleIfQSlot :=
        Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_q)
      subst hslotEq
      simp [noStaleIfQSlot] at hcontainsTy
      cases hcontainsTy
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · by_cases hy : x = noStaleIfY
      · subst hy
        have hslotEq : slot = noStaleIfYJoinSlot :=
          Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_y)
        subst hslotEq
        simp [noStaleIfYJoinSlot] at hcontainsTy
        cases hcontainsTy
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      · by_cases hs : x = noStaleIfS
        · subst hs
          have hslotEq : slot = noStaleIfSJoinSlot :=
            Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_s)
          subst hslotEq
          simp [noStaleIfSJoinSlot] at hcontainsTy
          cases hcontainsTy
          exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
        · by_cases ha : x = noStaleIfA
          · subst ha
            have hslotEq : slot = noStaleIfIntSlot :=
              Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_a)
            subst hslotEq
            cases hcontainsTy
          · by_cases hb : x = noStaleIfB
            · subst hb
              have hslotEq : slot = noStaleIfIntSlot :=
                Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_b)
              subst hslotEq
              cases hcontainsTy
            · by_cases hc : x = noStaleIfC
              · subst hc
                have hslotEq : slot = noStaleIfIntSlot :=
                  Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_c)
                subst hslotEq
                cases hcontainsTy
              · by_cases hd : x = noStaleIfD
                · subst hd
                  have hslotEq : slot = noStaleIfIntSlot :=
                    Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_d)
                  subst hslotEq
                  cases hcontainsTy
                · by_cases hsth : x = noStaleIfSth
                  · subst hsth
                    have hslotTy : slot.ty = .ty .bool := by
                      simpa [noStaleIfJoinEnv, noStaleIfEnv9,
                        noStaleIfEnv8, noStaleIfEnv7, noStaleIfEnv6,
                        noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
                        noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0,
                        noStaleIfA, noStaleIfB, noStaleIfC, noStaleIfD,
                        noStaleIfSth, noStaleIfP, noStaleIfQ, noStaleIfY,
                        noStaleIfS, noStaleIfBoolSlot, Env.update] using
                        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                          hslot).symm
                    rw [hslotTy] at hcontainsTy
                    cases hcontainsTy
                  · have hnone : noStaleIfJoinEnv.slotAt x = none := by
                      have hp' : x ≠ "p" := by simpa [noStaleIfP] using hp
                      have hq' : x ≠ "q" := by simpa [noStaleIfQ] using hq
                      have hy' : x ≠ "y" := by simpa [noStaleIfY] using hy
                      have hs' : x ≠ "s" := by simpa [noStaleIfS] using hs
                      have ha' : x ≠ "a" := by simpa [noStaleIfA] using ha
                      have hb' : x ≠ "b" := by simpa [noStaleIfB] using hb
                      have hc' : x ≠ "c" := by simpa [noStaleIfC] using hc
                      have hd' : x ≠ "d" := by simpa [noStaleIfD] using hd
                      have hsth' : x ≠ "sth" := by
                        simpa [noStaleIfSth] using hsth
                      simp [noStaleIfJoinEnv, noStaleIfEnv9, noStaleIfEnv8,
                        noStaleIfEnv7, noStaleIfEnv6, noStaleIfEnv5,
                        noStaleIfEnv4, noStaleIfEnv3, noStaleIfEnv2,
                        noStaleIfEnv1, noStaleIfEnv0, Env.update,
                        Env.empty, hp, hq, hy, hs, ha, hb, hc, hd, hsth]
                    rw [hslot] at hnone
                    cases hnone

theorem noStaleIfAfterWrite_contains_inv {x mutable targets} :
    noStaleIfAfterWriteEnv ⊢ x ↝ (.borrow mutable targets) →
      (x = noStaleIfP ∧ mutable = true ∧
        targets = [noStaleIfALVal, noStaleIfBLVal]) ∨
      (x = noStaleIfQ ∧ mutable = true ∧
        targets = [noStaleIfDLVal, noStaleIfBLVal]) ∨
      (x = noStaleIfY ∧ mutable = false ∧
        targets = [noStaleIfDerefP, noStaleIfCLVal]) ∨
      (x = noStaleIfS ∧ mutable = true ∧
        targets = [noStaleIfQLVal, noStaleIfPLVal]) := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hp : x = noStaleIfP
  · subst hp
    have hslotEq : slot = noStaleIfPAfterWriteSlot :=
      Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_p)
    subst hslotEq
    simp [noStaleIfPAfterWriteSlot] at hcontainsTy
    cases hcontainsTy
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · by_cases hq : x = noStaleIfQ
    · subst hq
      have hslotEq : slot = noStaleIfQAfterWriteSlot :=
        Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_q)
      subst hslotEq
      simp [noStaleIfQAfterWriteSlot] at hcontainsTy
      cases hcontainsTy
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · by_cases hy : x = noStaleIfY
      · subst hy
        have hslotEq : slot = noStaleIfYJoinSlot :=
          Option.some.inj (hslot.symm.trans noStaleIf_afterWrite_y_slot)
        subst hslotEq
        simp [noStaleIfYJoinSlot] at hcontainsTy
        cases hcontainsTy
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      · by_cases hs : x = noStaleIfS
        · subst hs
          have hslotEq : slot = noStaleIfSJoinSlot :=
            Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_s)
          subst hslotEq
          simp [noStaleIfSJoinSlot] at hcontainsTy
          cases hcontainsTy
          exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
        · by_cases ha : x = noStaleIfA
          · subst ha
            have hslotEq : slot = noStaleIfIntSlot :=
              Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_a)
            subst hslotEq
            cases hcontainsTy
          · by_cases hb : x = noStaleIfB
            · subst hb
              have hslotEq : slot = noStaleIfIntSlot :=
                Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_b)
              subst hslotEq
              cases hcontainsTy
            · by_cases hc : x = noStaleIfC
              · subst hc
                have hslotEq : slot = noStaleIfIntSlot :=
                  Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_c)
                subst hslotEq
                cases hcontainsTy
              · by_cases hd : x = noStaleIfD
                · subst hd
                  have hslotEq : slot = noStaleIfIntSlot :=
                    Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_d)
                  subst hslotEq
                  cases hcontainsTy
                · by_cases hsth : x = noStaleIfSth
                  · subst hsth
                    have hslotTy : slot.ty = .ty .bool := by
                      simpa [noStaleIfAfterWriteEnv, noStaleIfJoinEnv,
                        noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
                        noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4,
                        noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
                        noStaleIfEnv0, noStaleIfA, noStaleIfB,
                        noStaleIfC, noStaleIfD, noStaleIfSth, noStaleIfP,
                        noStaleIfQ, noStaleIfY, noStaleIfS,
                        noStaleIfBoolSlot, Env.update]
                        using
                        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                          hslot).symm
                    rw [hslotTy] at hcontainsTy
                    cases hcontainsTy
                  · have hnone : noStaleIfAfterWriteEnv.slotAt x = none := by
                      have hp' : x ≠ "p" := by simpa [noStaleIfP] using hp
                      have hq' : x ≠ "q" := by simpa [noStaleIfQ] using hq
                      have hy' : x ≠ "y" := by simpa [noStaleIfY] using hy
                      have hs' : x ≠ "s" := by simpa [noStaleIfS] using hs
                      have ha' : x ≠ "a" := by simpa [noStaleIfA] using ha
                      have hb' : x ≠ "b" := by simpa [noStaleIfB] using hb
                      have hc' : x ≠ "c" := by simpa [noStaleIfC] using hc
                      have hd' : x ≠ "d" := by simpa [noStaleIfD] using hd
                      have hsth' : x ≠ "sth" := by
                        simpa [noStaleIfSth] using hsth
                      simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv,
                        noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
                        noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4,
                        noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
                        noStaleIfEnv0, Env.update, Env.empty, hp, hq, hy,
                        hs, ha, hb, hc, hd, hsth]
                    rw [hslot] at hnone
                    cases hnone

theorem noStaleIfJoin_not_writeProhibited_b :
    ¬ WriteProhibited noStaleIfJoinEnv noStaleIfBLVal := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    rcases noStaleIfJoin_contains_inv hcontains with
      hp | hq | hy | hs
    · rcases hp with ⟨rfl, _hmut, rfl⟩
      simp at htarget
      subst htarget
      simp [noStaleIfALVal, noStaleIfBLVal, noStaleIfA, noStaleIfB,
        PathConflicts, LVal.base] at hconflict
    · rcases hq with ⟨rfl, _hmut, rfl⟩
      simp at htarget
      subst htarget
      simp [noStaleIfDLVal, noStaleIfBLVal, noStaleIfD, noStaleIfB,
        PathConflicts, LVal.base] at hconflict
    · rcases hy with ⟨rfl, hmut, _htargets⟩
      cases hmut
    · rcases hs with ⟨rfl, _hmut, rfl⟩
      simp at htarget
      rcases htarget with htarget | htarget <;> subst htarget <;>
        simp [noStaleIfQLVal, noStaleIfPLVal, noStaleIfBLVal,
          noStaleIfQ, noStaleIfP, noStaleIfB, PathConflicts, LVal.base] at hconflict
  · rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    rcases noStaleIfJoin_contains_inv hcontains with
      hp | hq | hy | hs
    · rcases hp with ⟨rfl, hmut, _htargets⟩
      cases hmut
    · rcases hq with ⟨rfl, hmut, _htargets⟩
      cases hmut
    · rcases hy with ⟨rfl, _hmut, rfl⟩
      simp at htarget
      rcases htarget with htarget | htarget <;> subst htarget <;>
        simp [noStaleIfDerefP, noStaleIfPLVal, noStaleIfCLVal,
          noStaleIfBLVal, noStaleIfP, noStaleIfC, noStaleIfB,
          PathConflicts, LVal.base] at hconflict
    · rcases hs with ⟨rfl, hmut, _htargets⟩
      cases hmut

theorem noStaleIfAfterWrite_not_writeProhibited_deref_s :
    ¬ WriteProhibited noStaleIfAfterWriteEnv (.deref noStaleIfSLVal) := by
  intro hwrite
  rcases hwrite with hread | himm
  · rcases hread with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    rcases noStaleIfAfterWrite_contains_inv hcontains with
      hp | hq | hy | hs
    · rcases hp with ⟨rfl, _hmut, rfl⟩
      simp at htarget
      rcases htarget with htarget | htarget <;> subst htarget <;>
        simp [noStaleIfALVal, noStaleIfBLVal, noStaleIfSLVal,
          noStaleIfA, noStaleIfB, noStaleIfS, PathConflicts, LVal.base] at hconflict
    · rcases hq with ⟨rfl, _hmut, rfl⟩
      simp at htarget
      rcases htarget with htarget | htarget <;> subst htarget <;>
        simp [noStaleIfDLVal, noStaleIfBLVal, noStaleIfSLVal,
          noStaleIfD, noStaleIfB, noStaleIfS, PathConflicts, LVal.base] at hconflict
    · rcases hy with ⟨rfl, hmut, _htargets⟩
      cases hmut
    · rcases hs with ⟨rfl, _hmut, rfl⟩
      simp at htarget
      rcases htarget with htarget | htarget <;> subst htarget <;>
        simp [noStaleIfQLVal, noStaleIfPLVal, noStaleIfSLVal,
          noStaleIfQ, noStaleIfP, noStaleIfS, PathConflicts, LVal.base] at hconflict
  · rcases himm with ⟨x, targets, target, hcontains, htarget, hconflict⟩
    rcases noStaleIfAfterWrite_contains_inv hcontains with
      hp | hq | hy | hs
    · rcases hp with ⟨rfl, hmut, _htargets⟩
      cases hmut
    · rcases hq with ⟨rfl, hmut, _htargets⟩
      cases hmut
    · rcases hy with ⟨rfl, _hmut, rfl⟩
      simp at htarget
      rcases htarget with htarget | htarget <;> subst htarget <;>
        simp [noStaleIfDerefP, noStaleIfPLVal, noStaleIfCLVal,
          noStaleIfSLVal, noStaleIfP, noStaleIfC, noStaleIfS,
          PathConflicts, LVal.base] at hconflict
    · rcases hs with ⟨rfl, hmut, _htargets⟩
      cases hmut

def noStaleIfRank (name : Name) : Nat :=
  if name = noStaleIfY then 2
  else if name = noStaleIfS then 2
  else if name = noStaleIfP then 1
  else if name = noStaleIfQ then 1
  else 0

theorem noStaleIf_final_write_ranked :
    ∃ φ, LinearizedBy φ noStaleIfJoinEnv ∧
      EnvWriteRhsBorrowTargetsBelow φ noStaleIfAfterWriteEnv
        (.borrow true [noStaleIfBLVal]) := by
  refine ⟨noStaleIfRank, ?linearized, ?below⟩
  · intro x slot hslot v hv
    by_cases hp : x = noStaleIfP
    · subst hp
      have hslotEq : slot = noStaleIfPSlot :=
        Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_p)
      subst hslotEq
      simp [noStaleIfPSlot, PartialTy.vars, Ty.vars, LVal.base] at hv
      rcases hv with rfl
      simp [noStaleIfRank, noStaleIfALVal, noStaleIfA, noStaleIfP,
        noStaleIfY, noStaleIfS, noStaleIfQ, LVal.base]
    · by_cases hq : x = noStaleIfQ
      · subst hq
        have hslotEq : slot = noStaleIfQSlot :=
          Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_q)
        subst hslotEq
        simp [noStaleIfQSlot, PartialTy.vars, Ty.vars, LVal.base] at hv
        rcases hv with rfl
        simp [noStaleIfRank, noStaleIfDLVal, noStaleIfD, noStaleIfQ,
          noStaleIfY, noStaleIfS, noStaleIfP, LVal.base]
      · by_cases hy : x = noStaleIfY
        · subst hy
          have hslotEq : slot = noStaleIfYJoinSlot :=
            Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_y)
          subst hslotEq
          simp [noStaleIfYJoinSlot, PartialTy.vars, Ty.vars,
            noStaleIfDerefP, noStaleIfPLVal, noStaleIfCLVal, LVal.base] at hv
          rcases hv with rfl | rfl
          · simp [noStaleIfRank, noStaleIfP, noStaleIfY, noStaleIfS,
              noStaleIfQ]
          · simp [noStaleIfRank, noStaleIfC, noStaleIfY, noStaleIfS,
              noStaleIfP, noStaleIfQ]
        · by_cases hs : x = noStaleIfS
          · subst hs
            have hslotEq : slot = noStaleIfSJoinSlot :=
              Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_s)
            subst hslotEq
            simp [noStaleIfSJoinSlot, PartialTy.vars, Ty.vars,
              noStaleIfQLVal, noStaleIfPLVal, LVal.base] at hv
            rcases hv with rfl | rfl
            · simp [noStaleIfRank, noStaleIfQ, noStaleIfS, noStaleIfY,
                noStaleIfP]
            · simp [noStaleIfRank, noStaleIfP, noStaleIfS, noStaleIfY,
                noStaleIfQ]
          · by_cases ha : x = noStaleIfA
            · subst ha
              have hslotEq : slot = noStaleIfIntSlot :=
                Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_a)
              subst hslotEq
              cases hv
            · by_cases hb : x = noStaleIfB
              · subst hb
                have hslotEq : slot = noStaleIfIntSlot :=
                  Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_b)
                subst hslotEq
                cases hv
              · by_cases hc : x = noStaleIfC
                · subst hc
                  have hslotEq : slot = noStaleIfIntSlot :=
                    Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_c)
                  subst hslotEq
                  cases hv
                · by_cases hd : x = noStaleIfD
                  · subst hd
                    have hslotEq : slot = noStaleIfIntSlot :=
                      Option.some.inj (hslot.symm.trans noStaleIfJoin_slot_d)
                    subst hslotEq
                    cases hv
                  · by_cases hsth : x = noStaleIfSth
                    · subst hsth
                      have hslotTy : slot.ty = .ty .bool := by
                        simpa [noStaleIfJoinEnv, noStaleIfEnv9,
                          noStaleIfEnv8, noStaleIfEnv7, noStaleIfEnv6,
                          noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
                          noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0,
                          noStaleIfA, noStaleIfB, noStaleIfC, noStaleIfD,
                          noStaleIfSth, noStaleIfP, noStaleIfQ, noStaleIfY,
                          noStaleIfS, noStaleIfBoolSlot, Env.update] using
                          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                            hslot).symm
                      rw [hslotTy] at hv
                      cases hv
                    · have hnone : noStaleIfJoinEnv.slotAt x = none := by
                        simp [noStaleIfJoinEnv, noStaleIfEnv9,
                          noStaleIfEnv8, noStaleIfEnv7, noStaleIfEnv6,
                          noStaleIfEnv5, noStaleIfEnv4, noStaleIfEnv3,
                          noStaleIfEnv2, noStaleIfEnv1, noStaleIfEnv0,
                          Env.update, Env.empty, hp, hq, hy, hs, ha, hb,
                          hc, hd, hsth]
                      rw [hslot] at hnone
                      cases hnone
  · intro x slot mutable targets target hslot hcontains htarget hrhs
    rcases hrhs with ⟨rhsMutable, rhsTargets, hrhsContains, hrhsTarget⟩
    cases hrhsContains with
    | here =>
        simp at hrhsTarget
        subst target
        rcases noStaleIfAfterWrite_contains_inv ⟨slot, hslot, hcontains⟩ with
          hp | hq | hy | hs
        · rcases hp with ⟨rfl, _hmut, rfl⟩
          simp [noStaleIfALVal, noStaleIfBLVal, noStaleIfA, noStaleIfB] at htarget
          simp [noStaleIfRank, noStaleIfBLVal, noStaleIfB, noStaleIfP,
            noStaleIfY, noStaleIfS, noStaleIfQ, LVal.base]
        · rcases hq with ⟨rfl, _hmut, rfl⟩
          simp [noStaleIfDLVal, noStaleIfBLVal, noStaleIfD, noStaleIfB] at htarget
          simp [noStaleIfRank, noStaleIfBLVal, noStaleIfB, noStaleIfQ,
            noStaleIfY, noStaleIfS, noStaleIfP, LVal.base]
        · rcases hy with ⟨rfl, _hmut, rfl⟩
          simp [noStaleIfDerefP, noStaleIfCLVal, noStaleIfBLVal,
            noStaleIfPLVal, noStaleIfP, noStaleIfC, noStaleIfB] at htarget
        · rcases hs with ⟨rfl, _hmut, rfl⟩
          simp [noStaleIfQLVal, noStaleIfPLVal, noStaleIfBLVal,
            noStaleIfQ, noStaleIfP, noStaleIfB] at htarget

theorem noStaleIfAfterWrite_no_box_lval :
    ∀ lv {inner lifetime},
      ¬ LValTyping noStaleIfAfterWriteEnv lv (.box inner) lifetime := by
  intro lv
  induction lv with
  | var x =>
      intro inner lifetime htyping
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hlife⟩
      by_cases hp : x = noStaleIfP
      · subst hp
        have hslotEq : slot = noStaleIfPAfterWriteSlot :=
          Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_p)
        subst hslotEq
        simp [noStaleIfPAfterWriteSlot] at hty
      · by_cases hq : x = noStaleIfQ
        · subst hq
          have hslotEq : slot = noStaleIfQAfterWriteSlot :=
            Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_q)
          subst hslotEq
          simp [noStaleIfQAfterWriteSlot] at hty
        · by_cases hy : x = noStaleIfY
          · subst hy
            have hslotEq : slot = noStaleIfYJoinSlot :=
              Option.some.inj (hslot.symm.trans noStaleIf_afterWrite_y_slot)
            subst hslotEq
            simp [noStaleIfYJoinSlot] at hty
          · by_cases hs : x = noStaleIfS
            · subst hs
              have hslotEq : slot = noStaleIfSJoinSlot :=
                Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_s)
              subst hslotEq
              simp [noStaleIfSJoinSlot] at hty
            · by_cases ha : x = noStaleIfA
              · subst ha
                have hslotEq : slot = noStaleIfIntSlot :=
                  Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_a)
                subst hslotEq
                simp [noStaleIfIntSlot] at hty
              · by_cases hb : x = noStaleIfB
                · subst hb
                  have hslotEq : slot = noStaleIfIntSlot :=
                    Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_b)
                  subst hslotEq
                  simp [noStaleIfIntSlot] at hty
                · by_cases hc : x = noStaleIfC
                  · subst hc
                    have hslotEq : slot = noStaleIfIntSlot :=
                      Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_c)
                    subst hslotEq
                    simp [noStaleIfIntSlot] at hty
                  · by_cases hd : x = noStaleIfD
                    · subst hd
                      have hslotEq : slot = noStaleIfIntSlot :=
                        Option.some.inj
                          (hslot.symm.trans noStaleIfAfterWrite_slot_d)
                      subst hslotEq
                      simp [noStaleIfIntSlot] at hty
                    · by_cases hsth : x = noStaleIfSth
                      · subst hsth
                        have hslotTy : slot.ty = .ty .bool := by
                          simpa [noStaleIfAfterWriteEnv, noStaleIfJoinEnv,
                            noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
                            noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4,
                            noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
                            noStaleIfEnv0, noStaleIfA, noStaleIfB,
                            noStaleIfC, noStaleIfD, noStaleIfSth,
                            noStaleIfP, noStaleIfQ, noStaleIfY, noStaleIfS,
                            noStaleIfBoolSlot, Env.update]
                            using
                            (congrArg (fun slotOpt =>
                              Option.map EnvSlot.ty slotOpt) hslot).symm
                        rw [hslotTy] at hty
                        cases hty
                      · have hnone : noStaleIfAfterWriteEnv.slotAt x = none := by
                          simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv,
                            noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
                            noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4,
                            noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
                            noStaleIfEnv0, Env.update, Env.empty, hp, hq,
                            hy, hs, ha, hb, hc, hd, hsth]
                        rw [hslot] at hnone
                        cases hnone
  | deref lv ih =>
      intro inner lifetime htyping
      cases htyping with
      | box hinner =>
          exact ih hinner
      | borrow _hinner htargets =>
          exact LValTargetsTyping.not_box htargets

theorem noStaleIfAfterWrite_no_full_box :
    (∀ {lv partialTy lifetime},
      LValTyping noStaleIfAfterWriteEnv lv partialTy lifetime →
        ∀ inner, partialTy = .ty (.box inner) → False) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping noStaleIfAfterWriteEnv targets partialTy lifetime →
        ∀ inner, partialTy = .ty (.box inner) → False) := by
  have hvar :
      ∀ {x slot inner},
        noStaleIfAfterWriteEnv.slotAt x = some slot →
        slot.ty = .ty (.box inner) →
        False := by
    intro x slot inner hslot hty
    by_cases hp : x = noStaleIfP
    · subst hp
      have hslotEq : slot = noStaleIfPAfterWriteSlot :=
        Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_p)
      subst hslotEq
      simp [noStaleIfPAfterWriteSlot] at hty
    · by_cases hq : x = noStaleIfQ
      · subst hq
        have hslotEq : slot = noStaleIfQAfterWriteSlot :=
          Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_q)
        subst hslotEq
        simp [noStaleIfQAfterWriteSlot] at hty
      · by_cases hy : x = noStaleIfY
        · subst hy
          have hslotEq : slot = noStaleIfYJoinSlot :=
            Option.some.inj (hslot.symm.trans noStaleIf_afterWrite_y_slot)
          subst hslotEq
          simp [noStaleIfYJoinSlot] at hty
        · by_cases hs : x = noStaleIfS
          · subst hs
            have hslotEq : slot = noStaleIfSJoinSlot :=
              Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_s)
            subst hslotEq
            simp [noStaleIfSJoinSlot] at hty
          · by_cases ha : x = noStaleIfA
            · subst ha
              have hslotEq : slot = noStaleIfIntSlot :=
                Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_a)
              subst hslotEq
              simp [noStaleIfIntSlot] at hty
            · by_cases hb : x = noStaleIfB
              · subst hb
                have hslotEq : slot = noStaleIfIntSlot :=
                  Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_b)
                subst hslotEq
                simp [noStaleIfIntSlot] at hty
              · by_cases hc : x = noStaleIfC
                · subst hc
                  have hslotEq : slot = noStaleIfIntSlot :=
                    Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_c)
                  subst hslotEq
                  simp [noStaleIfIntSlot] at hty
                · by_cases hd : x = noStaleIfD
                  · subst hd
                    have hslotEq : slot = noStaleIfIntSlot :=
                      Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_d)
                    subst hslotEq
                    simp [noStaleIfIntSlot] at hty
                  · by_cases hsth : x = noStaleIfSth
                    · subst hsth
                      have hslotTy : slot.ty = .ty .bool := by
                        simpa [noStaleIfAfterWriteEnv, noStaleIfJoinEnv,
                          noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
                          noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4,
                          noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
                          noStaleIfEnv0, noStaleIfA, noStaleIfB,
                          noStaleIfC, noStaleIfD, noStaleIfSth, noStaleIfP,
                          noStaleIfQ, noStaleIfY, noStaleIfS,
                          noStaleIfBoolSlot, Env.update]
                          using
                          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt)
                            hslot).symm
                      rw [hslotTy] at hty
                      cases hty
                    · have hnone : noStaleIfAfterWriteEnv.slotAt x = none := by
                        simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv,
                          noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
                          noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4,
                          noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
                          noStaleIfEnv0, Env.update, Env.empty, hp, hq, hy,
                          hs, ha, hb, hc, hd, hsth]
                      rw [hslot] at hnone
                      cases hnone
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun _lv partialTy _lifetime _ =>
        ∀ inner, partialTy = .ty (.box inner) → False)
      (motive_2 := fun _targets partialTy _lifetime _ =>
        ∀ inner, partialTy = .ty (.box inner) → False)
      (by
        intro _x slot hslot inner hty
        exact hvar hslot hty)
      (by
        intro lv inner lifetime hbox _ih fullInner hfull
        cases hfull
        exact noStaleIfAfterWrite_no_box_lval lv hbox)
      (by
        intro _lv _inner _lifetime _hbox ih fullInner hfull
        cases hfull
        exact ih _ rfl)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets inner hfull
        exact ihTargets inner hfull)
      (by
        intro _target ty _lifetime _htarget ihTarget inner hfull
        exact ihTarget inner hfull)
      (by
        intro _target _rest headTy _headLifetime _restLifetime _lifetime _restTy
          _unionTy _hhead _hrest hunion _hintersection ihHead _ihRest inner hfull
        cases hfull
        have hstrength :
            PartialTyStrengthens (.ty headTy) (.ty (.box inner)) :=
          PartialTyUnion.left_strengthens hunion
        rcases PartialTyStrengthens.to_box_ty_inv hstrength with
          ⟨headInner, hheadEq, _hinnerStrength⟩
        cases hheadEq
        exact ihHead headInner rfl)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv partialTy _lifetime _ =>
        ∀ inner, partialTy = .ty (.box inner) → False)
      (motive_2 := fun _targets partialTy _lifetime _ =>
        ∀ inner, partialTy = .ty (.box inner) → False)
      (by
        intro _x slot hslot inner hty
        exact hvar hslot hty)
      (by
        intro lv inner lifetime hbox _ih fullInner hfull
        cases hfull
        exact noStaleIfAfterWrite_no_box_lval lv hbox)
      (by
        intro _lv _inner _lifetime _hbox ih fullInner hfull
        cases hfull
        exact ih _ rfl)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets inner hfull
        exact ihTargets inner hfull)
      (by
        intro _target ty _lifetime _htarget ihTarget inner hfull
        exact ihTarget inner hfull)
      (by
        intro _target _rest headTy _headLifetime _restLifetime _lifetime _restTy
          _unionTy _hhead _hrest hunion _hintersection ihHead _ihRest inner hfull
        cases hfull
        have hstrength :
            PartialTyStrengthens (.ty headTy) (.ty (.box inner)) :=
          PartialTyUnion.left_strengthens hunion
        rcases PartialTyStrengthens.to_box_ty_inv hstrength with
          ⟨headInner, hheadEq, _hinnerStrength⟩
        cases hheadEq
        exact ihHead headInner rfl)
      htyping

theorem noStaleIfAfterWrite_no_full_box_lval {lv inner lifetime} :
    ¬ LValTyping noStaleIfAfterWriteEnv lv (.ty (.box inner)) lifetime := by
  intro htyping
  exact noStaleIfAfterWrite_no_full_box.1 htyping inner rfl

theorem noStaleIfAfterWrite_var_int_full {x ty lifetime}
    (hx : x = noStaleIfA ∨ x = noStaleIfB ∨ x = noStaleIfC ∨
      x = noStaleIfD) :
    LValTyping noStaleIfAfterWriteEnv (.var x) (.ty ty) lifetime →
      ty = .int := by
  intro htyping
  rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hlife⟩
  rcases hx with rfl | rfl | rfl | rfl
  · have hslotEq : slot = noStaleIfIntSlot :=
      Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_a)
    subst hslotEq
    simpa [noStaleIfIntSlot] using hty.symm
  · have hslotEq : slot = noStaleIfIntSlot :=
      Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_b)
    subst hslotEq
    simpa [noStaleIfIntSlot] using hty.symm
  · have hslotEq : slot = noStaleIfIntSlot :=
      Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_c)
    subst hslotEq
    simpa [noStaleIfIntSlot] using hty.symm
  · have hslotEq : slot = noStaleIfIntSlot :=
      Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_d)
    subst hslotEq
    simpa [noStaleIfIntSlot] using hty.symm

theorem noStaleIf_targets_output_int_of_head_int
    {head : LVal} {rest : List LVal} {ty : Ty} {lifetime : Lifetime}
    (hheadInt :
      ∀ {headTy headLifetime},
        LValTyping noStaleIfAfterWriteEnv head (.ty headTy) headLifetime →
          headTy = .int) :
    LValTargetsTyping noStaleIfAfterWriteEnv (head :: rest) (.ty ty)
      lifetime →
      ty = .int := by
  intro htargets
  cases htargets with
  | singleton hhead =>
      exact hheadInt hhead
  | @cons target rest' headTy headLifetime restLifetime lifetime'
      restTy unionTy hhead _hrest hunion _hintersection =>
      have hheadTy : headTy = Ty.int := hheadInt hhead
      have hstrength :
          PartialTyStrengthens (.ty Ty.int) (.ty ty) := by
        simpa [hheadTy] using PartialTyUnion.left_strengthens hunion
      exact PartialTyStrengthens.from_int_inv hstrength

theorem noStaleIfAfterWrite_deref_p_full_int {ty lifetime} :
    LValTyping noStaleIfAfterWriteEnv noStaleIfDerefP (.ty ty) lifetime →
      ty = .int := by
  intro htyping
  cases htyping with
  | box hinner =>
      exact False.elim (noStaleIfAfterWrite_no_box_lval noStaleIfPLVal hinner)
  | boxFull hinner =>
      exact False.elim (noStaleIfAfterWrite_no_full_box_lval hinner)
  | borrow hinner htargets =>
      rcases LValTyping.var_inv
          (by simpa [noStaleIfPLVal] using hinner) with
        ⟨slot, hslot, hty, _hlife⟩
      have hslotEq : slot = noStaleIfPAfterWriteSlot :=
        Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_p)
      subst hslotEq
      simp [noStaleIfPAfterWriteSlot] at hty
      rcases hty with ⟨rfl, rfl⟩
      exact noStaleIf_targets_output_int_of_head_int
        (head := noStaleIfALVal) (rest := [noStaleIfBLVal])
        (by
          intro headTy headLifetime hhead
          have hhead' :
              LValTyping noStaleIfAfterWriteEnv (.var noStaleIfA)
                (.ty headTy) headLifetime := by
            simpa [noStaleIfALVal] using hhead
          exact noStaleIfAfterWrite_var_int_full
            (Or.inl rfl) hhead') htargets

theorem noStaleIf_targets_not_borrow_of_head_int
    {head : LVal} {rest : List LVal} {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime}
    (hheadInt :
      ∀ {headTy headLifetime},
        LValTyping noStaleIfAfterWriteEnv head (.ty headTy) headLifetime →
          headTy = .int) :
    ¬ LValTargetsTyping noStaleIfAfterWriteEnv (head :: rest)
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  have hty := noStaleIf_targets_output_int_of_head_int hheadInt htargets
  cases hty

theorem noStaleIfAfterWrite_ab_targets_not_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping noStaleIfAfterWriteEnv
      [noStaleIfALVal, noStaleIfBLVal] (.ty (.borrow mutable targets))
      lifetime :=
  noStaleIf_targets_not_borrow_of_head_int
    (head := noStaleIfALVal) (rest := [noStaleIfBLVal])
    (by
      intro headTy headLifetime hhead
      have hhead' :
          LValTyping noStaleIfAfterWriteEnv (.var noStaleIfA)
            (.ty headTy) headLifetime := by
        simpa [noStaleIfALVal] using hhead
      exact noStaleIfAfterWrite_var_int_full (Or.inl rfl) hhead')

theorem noStaleIfAfterWrite_db_targets_not_borrow {mutable targets lifetime} :
    ¬ LValTargetsTyping noStaleIfAfterWriteEnv
      [noStaleIfDLVal, noStaleIfBLVal] (.ty (.borrow mutable targets))
      lifetime :=
  noStaleIf_targets_not_borrow_of_head_int
    (head := noStaleIfDLVal) (rest := [noStaleIfBLVal])
    (by
      intro headTy headLifetime hhead
      have hhead' :
          LValTyping noStaleIfAfterWriteEnv (.var noStaleIfD)
            (.ty headTy) headLifetime := by
        simpa [noStaleIfDLVal] using hhead
      exact noStaleIfAfterWrite_var_int_full (Or.inr (Or.inr (Or.inr rfl)))
        hhead')

theorem noStaleIfAfterWrite_deref_p_c_targets_not_borrow
    {mutable targets lifetime} :
    ¬ LValTargetsTyping noStaleIfAfterWriteEnv
      [noStaleIfDerefP, noStaleIfCLVal] (.ty (.borrow mutable targets))
      lifetime :=
  noStaleIf_targets_not_borrow_of_head_int
    (head := noStaleIfDerefP) (rest := [noStaleIfCLVal])
    (by
      intro headTy headLifetime hhead
      exact noStaleIfAfterWrite_deref_p_full_int hhead)

theorem noStaleIfAfterWrite_dbab_target_int {target ty lifetime}
    (hmem : target ∈
      [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal, noStaleIfBLVal]) :
    LValTyping noStaleIfAfterWriteEnv target (.ty ty) lifetime →
      ty = .int := by
  intro htyping
  simp at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · have htyping' :
        LValTyping noStaleIfAfterWriteEnv (.var noStaleIfD)
          (.ty ty) lifetime := by
      simpa [noStaleIfDLVal] using htyping
    exact noStaleIfAfterWrite_var_int_full
      (Or.inr (Or.inr (Or.inr rfl))) htyping'
  · have htyping' :
        LValTyping noStaleIfAfterWriteEnv (.var noStaleIfB)
          (.ty ty) lifetime := by
      simpa [noStaleIfBLVal] using htyping
    exact noStaleIfAfterWrite_var_int_full (Or.inr (Or.inl rfl)) htyping'
  · have htyping' :
        LValTyping noStaleIfAfterWriteEnv (.var noStaleIfA)
          (.ty ty) lifetime := by
      simpa [noStaleIfALVal] using htyping
    exact noStaleIfAfterWrite_var_int_full (Or.inl rfl) htyping'
  · have htyping' :
        LValTyping noStaleIfAfterWriteEnv (.var noStaleIfB)
          (.ty ty) lifetime := by
      simpa [noStaleIfBLVal] using htyping
    exact noStaleIfAfterWrite_var_int_full (Or.inr (Or.inl rfl)) htyping'

theorem noStaleIfAfterWrite_dbab_target_typing {target}
    (hmem : target ∈
      [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal, noStaleIfBLVal]) :
    LValTyping noStaleIfAfterWriteEnv target (.ty .int) Lifetime.root := by
  simp at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact noStaleIfAfterWrite_d_typing
  · exact noStaleIfAfterWrite_b_typing
  · exact noStaleIfAfterWrite_a_typing
  · exact noStaleIfAfterWrite_b_typing

theorem noStaleIfAfterWrite_targets_int_typing :
    ∀ targets : List LVal,
      targets ≠ [] →
      (∀ target, target ∈ targets →
        target ∈
          [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal, noStaleIfBLVal]) →
      LValTargetsTyping noStaleIfAfterWriteEnv targets (.ty .int)
        Lifetime.root := by
  intro targets
  induction targets with
  | nil =>
      intro hnonempty _hmem
      exact False.elim (hnonempty rfl)
  | cons head tail ih =>
      intro _hnonempty hmem
      cases tail with
      | nil =>
          exact LValTargetsTyping.singleton
            (noStaleIfAfterWrite_dbab_target_typing (hmem head (by simp)))
      | cons next rest =>
          exact LValTargetsTyping.cons
            (noStaleIfAfterWrite_dbab_target_typing (hmem head (by simp)))
            (ih (by simp) (by
              intro target htarget
              exact hmem target (List.mem_cons_of_mem head htarget)))
            (PartialTyUnion.self (.ty .int))
            (LifetimeIntersection.self Lifetime.root)

theorem noStaleIfAfterWrite_int_targets_not_borrow
    {sourceTargets : List LVal} {mutable : Bool} {targets : List LVal}
    {lifetime : Lifetime}
    (hnonempty : sourceTargets ≠ [])
    (hmem :
      ∀ target, target ∈ sourceTargets →
        target ∈
          [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal, noStaleIfBLVal]) :
    ¬ LValTargetsTyping noStaleIfAfterWriteEnv sourceTargets
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  cases sourceTargets with
  | nil =>
      exact hnonempty rfl
  | cons head rest =>
      exact noStaleIf_targets_not_borrow_of_head_int
        (head := head) (rest := rest)
        (by
          intro headTy headLifetime hhead
          exact noStaleIfAfterWrite_dbab_target_int
            (hmem head (by simp)) hhead)
        htargets

theorem noStaleIfAfterWrite_qp_borrow_targets_shape {mutable targets lifetime} :
    LValTargetsTyping noStaleIfAfterWriteEnv [noStaleIfQLVal, noStaleIfPLVal]
      (.ty (.borrow mutable targets)) lifetime →
      targets ≠ [] ∧
        ∀ target, target ∈ targets →
          target ∈
            [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal,
              noStaleIfBLVal] := by
  intro htargets
  cases htargets with
  | @cons target rest headTy headLifetime restLifetime lifetime'
      restTy unionTy hq hpTargets hunion _hintersection =>
      cases hpTargets with
      | @singleton targetP tailTy tailLifetime hp =>
          rcases LValTyping.var_inv
              (by simpa [noStaleIfQLVal] using hq) with
            ⟨qSlot, hqSlot, hqTy, _hqLife⟩
          have hqSlotEq : qSlot = noStaleIfQAfterWriteSlot :=
            Option.some.inj (hqSlot.symm.trans noStaleIfAfterWrite_slot_q)
          subst hqSlotEq
          have hqTyEq :
              headTy = Ty.borrow true [noStaleIfDLVal, noStaleIfBLVal] := by
            simpa [noStaleIfQAfterWriteSlot] using hqTy.symm
          rcases LValTyping.var_inv
              (by simpa [noStaleIfPLVal] using hp) with
            ⟨pSlot, hpSlot, hpTy, _hpLife⟩
          have hpSlotEq : pSlot = noStaleIfPAfterWriteSlot :=
            Option.some.inj (hpSlot.symm.trans noStaleIfAfterWrite_slot_p)
          subst hpSlotEq
          have hpTyEq :
              tailTy = Ty.borrow true [noStaleIfALVal, noStaleIfBLVal] := by
            simpa [noStaleIfPAfterWriteSlot] using hpTy.symm
          have hleft :
              PartialTyStrengthens
                (.ty (.borrow true [noStaleIfDLVal, noStaleIfBLVal]))
                (.ty (.borrow mutable targets)) := by
            simpa [hqTyEq, hpTyEq] using PartialTyUnion.left_strengthens hunion
          rcases PartialTyStrengthens.to_borrow_right hleft with
            ⟨leftTargets, hleftEq, hleftSubset⟩
          cases hleftEq
          have hnonempty : targets ≠ [] := by
            intro hnil
            have hd : noStaleIfDLVal ∈ targets := hleftSubset (by simp)
            simp [hnil] at hd
          refine ⟨hnonempty, ?_⟩
          intro target htarget
          have hmember :
              target ∈ [noStaleIfDLVal, noStaleIfBLVal] ∨
                target ∈ [noStaleIfALVal, noStaleIfBLVal] := by
            exact PartialTyUnion.borrow_member
              (by simpa [hqTyEq, hpTyEq] using hunion) htarget
          simp at hmember ⊢
          rcases hmember with hleftMem | hrightMem
          · rcases hleftMem with htarget | htarget
            · exact Or.inl htarget
            · exact Or.inr (Or.inl htarget)
          · rcases hrightMem with htarget | htarget
            · exact Or.inr (Or.inr (Or.inl htarget))
            · exact Or.inr (Or.inl htarget)
      | cons _ hrest _hunion _hintersection =>
          cases hrest

theorem noStaleIfAfterWrite_qp_borrow_targets_coherent
    {mutable targets lifetime} :
    LValTargetsTyping noStaleIfAfterWriteEnv [noStaleIfQLVal, noStaleIfPLVal]
      (.ty (.borrow mutable targets)) lifetime →
      ∃ ty targetLifetime,
        LValTargetsTyping noStaleIfAfterWriteEnv targets (.ty ty)
          targetLifetime := by
  intro htargets
  rcases noStaleIfAfterWrite_qp_borrow_targets_shape htargets with
    ⟨hnonempty, hmem⟩
  exact ⟨.int, Lifetime.root,
    noStaleIfAfterWrite_targets_int_typing targets hnonempty hmem⟩

theorem noStaleIfAfterWrite_borrow_lval_inv :
    ∀ lv {mutable targets lifetime},
      LValTyping noStaleIfAfterWriteEnv lv
        (.ty (.borrow mutable targets)) lifetime →
      (lv = noStaleIfPLVal ∧
        targets = [noStaleIfALVal, noStaleIfBLVal]) ∨
      (lv = noStaleIfQLVal ∧
        targets = [noStaleIfDLVal, noStaleIfBLVal]) ∨
      (lv = noStaleIfYLVal ∧
        targets = [noStaleIfDerefP, noStaleIfCLVal]) ∨
      (lv = noStaleIfSLVal ∧
        targets = [noStaleIfQLVal, noStaleIfPLVal]) ∨
      (lv = .deref noStaleIfSLVal ∧
        targets ≠ [] ∧
        ∀ target, target ∈ targets →
          target ∈
            [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal,
              noStaleIfBLVal]) := by
  intro lv
  induction lv with
  | var x =>
      intro mutable targets lifetime htyping
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hty, _hlife⟩
      by_cases hp : x = noStaleIfP
      · subst hp
        have hslotEq : slot = noStaleIfPAfterWriteSlot :=
          Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_p)
        subst hslotEq
        simp [noStaleIfPAfterWriteSlot] at hty
        rcases hty with ⟨_hmutable, htargets⟩
        exact Or.inl ⟨rfl, htargets.symm⟩
      · by_cases hq : x = noStaleIfQ
        · subst hq
          have hslotEq : slot = noStaleIfQAfterWriteSlot :=
            Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_q)
          subst hslotEq
          simp [noStaleIfQAfterWriteSlot] at hty
          rcases hty with ⟨_hmutable, htargets⟩
          exact Or.inr (Or.inl ⟨rfl, htargets.symm⟩)
        · by_cases hy : x = noStaleIfY
          · subst hy
            have hslotEq : slot = noStaleIfYJoinSlot :=
              Option.some.inj (hslot.symm.trans noStaleIf_afterWrite_y_slot)
            subst hslotEq
            simp [noStaleIfYJoinSlot] at hty
            rcases hty with ⟨_hmutable, htargets⟩
            exact Or.inr (Or.inr (Or.inl ⟨rfl, htargets.symm⟩))
          · by_cases hs : x = noStaleIfS
            · subst hs
              have hslotEq : slot = noStaleIfSJoinSlot :=
                Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_s)
              subst hslotEq
              simp [noStaleIfSJoinSlot] at hty
              rcases hty with ⟨_hmutable, htargets⟩
              exact Or.inr (Or.inr (Or.inr (Or.inl
                ⟨rfl, htargets.symm⟩)))
            · by_cases ha : x = noStaleIfA
              · subst ha
                have hslotEq : slot = noStaleIfIntSlot :=
                  Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_a)
                subst hslotEq
                simp [noStaleIfIntSlot] at hty
              · by_cases hb : x = noStaleIfB
                · subst hb
                  have hslotEq : slot = noStaleIfIntSlot :=
                    Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_b)
                  subst hslotEq
                  simp [noStaleIfIntSlot] at hty
                · by_cases hc : x = noStaleIfC
                  · subst hc
                    have hslotEq : slot = noStaleIfIntSlot :=
                      Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_c)
                    subst hslotEq
                    simp [noStaleIfIntSlot] at hty
                  · by_cases hd : x = noStaleIfD
                    · subst hd
                      have hslotEq : slot = noStaleIfIntSlot :=
                        Option.some.inj
                          (hslot.symm.trans noStaleIfAfterWrite_slot_d)
                      subst hslotEq
                      simp [noStaleIfIntSlot] at hty
                    · by_cases hsth : x = noStaleIfSth
                      · subst hsth
                        have hslotTy : slot.ty = .ty .bool := by
                          simpa [noStaleIfAfterWriteEnv, noStaleIfJoinEnv,
                            noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
                            noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4,
                            noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
                            noStaleIfEnv0, noStaleIfA, noStaleIfB,
                            noStaleIfC, noStaleIfD, noStaleIfSth,
                            noStaleIfP, noStaleIfQ, noStaleIfY, noStaleIfS,
                            noStaleIfBoolSlot, Env.update]
                            using
                            (congrArg (fun slotOpt =>
                              Option.map EnvSlot.ty slotOpt) hslot).symm
                        rw [hslotTy] at hty
                        cases hty
                      · have hnone : noStaleIfAfterWriteEnv.slotAt x = none := by
                          simp [noStaleIfAfterWriteEnv, noStaleIfJoinEnv,
                            noStaleIfEnv9, noStaleIfEnv8, noStaleIfEnv7,
                            noStaleIfEnv6, noStaleIfEnv5, noStaleIfEnv4,
                            noStaleIfEnv3, noStaleIfEnv2, noStaleIfEnv1,
                            noStaleIfEnv0, Env.update, Env.empty, hp, hq,
                            hy, hs, ha, hb, hc, hd, hsth]
                        rw [hslot] at hnone
                        cases hnone
  | deref lv ih =>
      intro mutable targets lifetime htyping
      cases htyping with
      | box hinner =>
          exact False.elim (noStaleIfAfterWrite_no_box_lval lv hinner)
      | boxFull hinner =>
          exact False.elim (noStaleIfAfterWrite_no_full_box_lval hinner)
      | borrow hinner htargets =>
          rcases ih hinner with hp | hq | hy | hs | hds
          · rcases hp with ⟨hlv, htargetsEq⟩
            subst hlv
            subst htargetsEq
            exact False.elim (noStaleIfAfterWrite_ab_targets_not_borrow htargets)
          · rcases hq with ⟨hlv, htargetsEq⟩
            subst hlv
            subst htargetsEq
            exact False.elim (noStaleIfAfterWrite_db_targets_not_borrow htargets)
          · rcases hy with ⟨hlv, htargetsEq⟩
            subst hlv
            subst htargetsEq
            exact False.elim
              (noStaleIfAfterWrite_deref_p_c_targets_not_borrow htargets)
          · rcases hs with ⟨hlv, htargetsEq⟩
            subst hlv
            subst htargetsEq
            rcases noStaleIfAfterWrite_qp_borrow_targets_shape htargets with
              ⟨hnonempty, hmem⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨rfl, hnonempty, hmem⟩)))
          · rcases hds with ⟨hlv, hnonempty, hmem⟩
            subst hlv
            exact False.elim
              (noStaleIfAfterWrite_int_targets_not_borrow hnonempty hmem
                htargets)

theorem noStaleIfAfterWrite_coherent :
    Coherent noStaleIfAfterWriteEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases noStaleIfAfterWrite_borrow_lval_inv lv htyping with
    hp | hq | hy | hs | hds
  · rcases hp with ⟨_hlv, htargets⟩
    subst htargets
    exact ⟨.ty .int, Lifetime.root,
      LValTargetsTyping.toMaybe noStaleIfAfterWrite_ab_targets_typing⟩
  · rcases hq with ⟨_hlv, htargets⟩
    subst htargets
    exact ⟨.ty .int, Lifetime.root,
      LValTargetsTyping.toMaybe noStaleIfAfterWrite_db_targets_typing⟩
  · rcases hy with ⟨_hlv, htargets⟩
    subst htargets
    exact ⟨.ty .int, Lifetime.root,
      LValTargetsTyping.toMaybe noStaleIfAfterWrite_deref_p_c_targets_typing⟩
  · rcases hs with ⟨_hlv, htargets⟩
    subst htargets
    exact ⟨.ty (.borrow true
        [noStaleIfDLVal, noStaleIfBLVal, noStaleIfALVal, noStaleIfBLVal]),
      Lifetime.root, LValTargetsTyping.toMaybe
        noStaleIfAfterWrite_qp_targets_typing⟩
  · rcases hds with ⟨_hlv, hnonempty, hmem⟩
    exact ⟨.ty .int, Lifetime.root,
      LValTargetsTyping.toMaybe
        (noStaleIfAfterWrite_targets_int_typing targets hnonempty hmem)⟩

theorem noStaleIf_final_write_rhs_targets_wellFormed :
    EnvWriteRhsTargetsWellFormed noStaleIfAfterWriteEnv
      (.borrow true [noStaleIfBLVal]) := by
  intro x slot mutable targets target hslot hcontains _htarget hrhs
  rcases hrhs with ⟨rhsMutable, rhsTargets, hrhsContains, hrhsTarget⟩
  cases hrhsContains
  simp at hrhsTarget
  subst target
  have hslotLifetime : slot.lifetime = Lifetime.root := by
    rcases noStaleIfAfterWrite_contains_inv ⟨slot, hslot, hcontains⟩ with
      hp | hq | hy | hs
    · rcases hp with ⟨rfl, _hmut, _htargets⟩
      have hslotEq : slot = noStaleIfPAfterWriteSlot :=
        Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_p)
      subst hslotEq
      rfl
    · rcases hq with ⟨rfl, _hmut, _htargets⟩
      have hslotEq : slot = noStaleIfQAfterWriteSlot :=
        Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_q)
      subst hslotEq
      rfl
    · rcases hy with ⟨rfl, _hmut, _htargets⟩
      have hslotEq : slot = noStaleIfYJoinSlot :=
        Option.some.inj (hslot.symm.trans noStaleIf_afterWrite_y_slot)
      subst hslotEq
      rfl
    · rcases hs with ⟨rfl, _hmut, _htargets⟩
      have hslotEq : slot = noStaleIfSJoinSlot :=
        Option.some.inj (hslot.symm.trans noStaleIfAfterWrite_slot_s)
      subst hslotEq
      rfl
  refine ⟨.int, Lifetime.root, noStaleIfAfterWrite_b_typing, ?_, ?_⟩
  · rw [hslotLifetime]
    exact LifetimeOutlives.refl Lifetime.root
  · exact ⟨noStaleIfIntSlot, by simpa [noStaleIfBLVal, LVal.base],
      by
        rw [hslotLifetime]
        exact LifetimeOutlives.refl Lifetime.root⟩

theorem noStaleIf_p_may_read_through_deref_p :
    EnvMayReadThrough noStaleIfJoinEnv noStaleIfPLVal
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
