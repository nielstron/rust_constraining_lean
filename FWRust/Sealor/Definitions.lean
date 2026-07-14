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

/-- A complete-program checker is sound when acceptance implies membership in
the target language. Together with `CheckerComplete`, this is the paper's
assumption that the underlying compiler is exact. -/
def CheckerSound
    (L : Complete → Prop)
    (checker : Complete → Prop) : Prop :=
  ∀ c, checker c → L c

/-- A prefix checker is complete on `Class` when every completable partial input
in that class is accepted. -/
def PrefixCheckerCompleteOn
    (Class : Partial → Prop)
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (prefixChecker : Partial → Prop) : Prop :=
  ∀ p, Class p → Completable L Completes p → prefixChecker p

/-- A prefix checker is sound on `Class` when every accepted partial input in
that class has a valid completion. -/
def PrefixCheckerSoundOn
    (Class : Partial → Prop)
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (prefixChecker : Partial → Prop) : Prop :=
  ∀ p, Class p → prefixChecker p → Completable L Completes p

/-- A prefix checker is globally complete when it is complete on all partial
inputs. -/
def PrefixCheckerComplete
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (prefixChecker : Partial → Prop) : Prop :=
  PrefixCheckerCompleteOn (fun _ => True) L Completes prefixChecker

/-- A prefix checker is globally sound when it is sound on all partial inputs. -/
def PrefixCheckerSound
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (prefixChecker : Partial → Prop) : Prop :=
  PrefixCheckerSoundOn (fun _ => True) L Completes prefixChecker

/-- A sealor is sound on `Class` when a valid sealed program witnesses that
the original partial input has a valid completion. -/
def SealorSoundOn
    (Class : Partial → Prop)
    (L : Complete → Prop)
    (Completes : Partial → Complete → Prop)
    (sealFn : Partial → Complete) : Prop :=
  ∀ p, Class p → L (sealFn p) → Completable L Completes p

/-- A complete syntax tree extends a string when parsing the string with some
appended suffix produces that tree. -/
def StringExtensionCompletes
    (parse : String → Option Complete)
    (rawPrefix : String) (complete : Complete) : Prop :=
  ∃ suffix, parse (rawPrefix ++ suffix) = some complete

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
  intro p _ hp
  rcases hp with ⟨c, hCompletes, hValid⟩
  apply hChecker
  exact Classical.byContradiction (fun hSealInvalid =>
    hSeal p hSealInvalid c hCompletes hValid)

/-- The soundness direction of Theorem 3.2: sealor soundness and compiler
soundness imply soundness of the induced generative compiler. -/
theorem sealor_soundness_lifts_to_prefix_checkers
    {Class : Partial → Prop}
    {L : Complete → Prop}
    {Completes : Partial → Complete → Prop}
    {sealFn : Partial → Complete}
    {checker : Complete → Prop}
    (hSeal : SealorSoundOn Class L Completes sealFn)
    (hChecker : CheckerSound L checker) :
    PrefixCheckerSoundOn Class L Completes
      (SealorPrefixChecker checker sealFn) := by
  intro p hClass hAccepted
  exact hSeal p hClass (hChecker (sealFn p) hAccepted)

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

/-- The partial-syntax completeness theorem lifts to arbitrary strings once a
decoder maps every string with a valid extension to a completable partial tree.
This isolates the parser bridge used by the paper's string-level argument. -/
theorem partialSyntax_completeness_lifts_to_strings
    {L : Complete → Prop}
    {Completes : Partial → Complete → Prop}
    {prefixChecker : Partial → Prop}
    (parse : String → Option Complete)
    (decode : String → Partial)
    (hPartial : PrefixCheckerComplete L Completes prefixChecker)
    (hDecode : ∀ rawPrefix,
      Completable L (StringExtensionCompletes parse) rawPrefix →
      Completable L Completes (decode rawPrefix)) :
    PrefixCheckerComplete L (StringExtensionCompletes parse)
      (fun rawPrefix => prefixChecker (decode rawPrefix)) := by
  intro rawPrefix _ hCompletable
  exact hPartial (decode rawPrefix) trivial
    (hDecode rawPrefix hCompletable)

/-- Partial-syntax soundness on a class lifts to strings when decoding preserves
the class and every partial completion is realized by a string extension. -/
theorem partialSyntax_soundness_lifts_to_strings
    {L : Complete → Prop}
    {Completes : Partial → Complete → Prop}
    {prefixChecker : Partial → Prop}
    {Class : Partial → Prop}
    (parse : String → Option Complete)
    (decode : String → Partial)
    (StringClass : String → Prop)
    (hPartial : PrefixCheckerSoundOn Class L Completes prefixChecker)
    (hClass : ∀ rawPrefix,
      StringClass rawPrefix → Class (decode rawPrefix))
    (hRealizes : ∀ rawPrefix complete,
      Completes (decode rawPrefix) complete →
      StringExtensionCompletes parse rawPrefix complete) :
    PrefixCheckerSoundOn StringClass L (StringExtensionCompletes parse)
      (fun rawPrefix => prefixChecker (decode rawPrefix)) := by
  intro rawPrefix hStringClass hAccepted
  rcases hPartial (decode rawPrefix) (hClass rawPrefix hStringClass)
      hAccepted with
    ⟨complete, hCompletes, hValid⟩
  exact ⟨complete, hRealizes rawPrefix complete hCompletes, hValid⟩

end ConservativeSealor
