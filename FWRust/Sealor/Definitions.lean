/-
Abstract definitions and the main sealor theorem.

This file contains no language-specific syntax.  `Partial` is the type of
prefixes/partial outputs, `Complete` is the type checked by the complete
checker, and `Completes p c` says that `c` is one possible completion of `p`.
-/

namespace ConservativeSealor

variable {Partial Complete : Type}

def Completable
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (p : Partial) : Prop :=
  ∃ c, Completes p c ∧ L c

def Conservative
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (sealFn : Partial → Complete) : Prop :=
  ∀ p, ¬ L (sealFn p) → ∀ c, Completes p c → ¬ L c

def CheckerComplete
    (L : Complete → Prop)
    (checker : Complete → Prop) : Prop :=
  ∀ c, L c → checker c

def PrefixCheckerComplete
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (prefixChecker : Partial → Prop) : Prop :=
  ∀ p, Completable L Completes p → prefixChecker p

def SealorPrefixChecker
    (checker : Complete → Prop)
    (sealFn : Partial → Complete)
    (p : Partial) : Prop :=
  checker (sealFn p)

theorem conservative_sealors_give_complete_prefix_checkers
    {L : Complete → Prop}
    {Completes : Partial → Complete → Prop}
    {sealFn : Partial → Complete}
    {checker : Complete → Prop}
    (hSeal : Conservative L Completes sealFn)
    (hChecker : CheckerComplete L checker) :
    PrefixCheckerComplete L Completes
      (SealorPrefixChecker checker sealFn) := by
  intro p hp
  rcases hp with ⟨c, hCompletes, hValid⟩
  apply hChecker
  exact Classical.byContradiction (fun hSealInvalid =>
    hSeal p hSealInvalid c hCompletes hValid)

theorem conservative_accepts_all_completable_sealings
    {L : Complete → Prop}
    {Completes : Partial → Complete → Prop}
    {sealFn : Partial → Complete}
    (hSeal : Conservative L Completes sealFn) :
    ∀ p, Completable L Completes p → L (sealFn p) := by
  intro p hp
  rcases hp with ⟨c, hCompletes, hValid⟩
  exact Classical.byContradiction (fun hSealInvalid =>
    hSeal p hSealInvalid c hCompletes hValid)

end ConservativeSealor
