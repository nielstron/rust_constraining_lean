/-
Abstract definitions and the main extractor theorem.

This file contains no language-specific syntax.  It captures the logical shape
of the paper's extractor argument:

  * a complete output checker recognizes a language `L`;
  * an extractor maps a partial output to a complete candidate;
  * conservativeness says that extraction is allowed to reject only prefixes
    that really have no valid completion;
  * therefore the checker-after-extractor prefix checker is complete.
-/

namespace LwRust

/-!
`Partial` and `Complete` are kept separate.  For Rust they would both usually be
represented by text, but separating them makes the interfaces explicit:

  * `Completes p c` means that `c` is one possible complete output obtained by
    finishing partial output `p`;
  * `extract p` is the complete candidate sent to the ordinary checker.

The paper writes the language predicate as membership in `𝓛`; here it is just a
predicate `L : Complete → Prop`.
-/

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

/-!
Proof strategy, in words:

Assume a partial output `p` has a valid completion `x`.  If the extraction were
invalid, conservativeness would say that every completion of `p` is invalid.
That contradicts the concrete valid completion `x`.  Hence the extraction is
valid.  Since the ordinary checker is complete for complete outputs, it accepts
the extraction, so the derived prefix checker accepts `p`.
-/
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

/-!
The contrapositive form below is often the most convenient proof obligation for
a designed extractor: when the partial output is completable, extraction must
produce a valid complete output.  This is equivalent to conservativeness in
classical logic, but the paper's direction is the operationally meaningful one:
an invalid extraction is only allowed when no completion exists.
-/
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

end LwRust
