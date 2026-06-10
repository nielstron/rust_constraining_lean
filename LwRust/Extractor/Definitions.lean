/-
Abstract definitions and the main extractor theorem.

This file contains no language-specific syntax.  `Partial` is the type of
prefixes/partial outputs, `Complete` is the type checked by the complete
checker, and `Completes p c` says that `c` is one possible completion of `p`.
-/

namespace ConservativeExtractor

variable {Partial Complete : Type}

def Completable
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (p : Partial) : Prop :=
  ∃ c, Completes p c ∧ L c

def Conservative
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (extract : Partial → Complete) : Prop :=
  ∀ p, ¬ L (extract p) → ∀ c, Completes p c → ¬ L c

def CheckerComplete
    (L : Complete → Prop)
    (checker : Complete → Prop) : Prop :=
  ∀ c, L c → checker c

def PrefixCheckerComplete
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (prefixChecker : Partial → Prop) : Prop :=
  ∀ p, Completable L Completes p → prefixChecker p

def ExtractorPrefixChecker
    (checker : Complete → Prop)
    (extract : Partial → Complete)
    (p : Partial) : Prop :=
  checker (extract p)

theorem conservative_extractors_give_complete_prefix_checkers
    {L : Complete → Prop}
    {Completes : Partial → Complete → Prop}
    {extract : Partial → Complete}
    {checker : Complete → Prop}
    (hExt : Conservative L Completes extract)
    (hChecker : CheckerComplete L checker) :
    PrefixCheckerComplete L Completes
      (ExtractorPrefixChecker checker extract) := by
  intro p hp
  rcases hp with ⟨c, hCompletes, hValid⟩
  apply hChecker
  exact Classical.byContradiction (fun hExtractInvalid =>
    hExt p hExtractInvalid c hCompletes hValid)

theorem conservative_accepts_all_completable_extractions
    {L : Complete → Prop}
    {Completes : Partial → Complete → Prop}
    {extract : Partial → Complete}
    (hExt : Conservative L Completes extract) :
    ∀ p, Completable L Completes p → L (extract p) := by
  intro p hp
  rcases hp with ⟨c, hCompletes, hValid⟩
  exact Classical.byContradiction (fun hExtractInvalid =>
    hExt p hExtractInvalid c hCompletes hValid)

end ConservativeExtractor
