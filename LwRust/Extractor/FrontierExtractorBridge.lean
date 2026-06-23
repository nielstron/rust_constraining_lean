import LwRust.Extractor.Generated.FrontierLower
import LwRust.Extractor.FrontierSourceCompletion
import LwRust.Extractor.Extractors.NestedBlocks

/-!
Bridge from token-prefix completions to the existing extractor theorem.

The parser/frontier development makes "partial code" a token prefix with a
grammar-derived completion relation.  The existing extractor still consumes
`Generated.PartialProgram`.  This file isolates the single proof obligation
needed to reuse the extractor: a generated lowering from token prefixes to old
partial programs must over-approximate all grammar/AST completions of that
prefix.
-/

namespace ConservativeExtractor
namespace GrammarFrontier
namespace FwRust

abbrev CodeCompletesProgram : List Tok → Program → Prop :=
  CodeCompletesTerm

def LowersCodePrefix (lower : List Tok → PartialProgram) : Prop :=
  ∀ pref full,
    CodeCompletesProgram pref full →
    CompletesProgram (lower pref) full

def codePrefixExtractor (lower : List Tok → PartialProgram)
    (pref : List Tok) : Program :=
  extractProgram (lower pref)

theorem codePrefixExtractor_wellTyped_of_completion
    {lower : List Tok → PartialProgram}
    (hlower : LowersCodePrefix lower)
    {pref : List Tok} {full : Program}
    (hCompletion : CodeCompletesProgram pref full)
    (hFull : ProgramWellTyped full) :
    ProgramWellTyped (codePrefixExtractor lower pref) := by
  exact extractProgram_wellTyped_of_completion
    (hlower pref full hCompletion) hFull

theorem codePrefixExtractor_conservative
    {lower : List Tok → PartialProgram}
    (hlower : LowersCodePrefix lower) :
    Conservative ProgramWellTyped CodeCompletesProgram
      (codePrefixExtractor lower) := by
  intro pref hInvalid full hCompletion hFull
  exact hInvalid
    (codePrefixExtractor_wellTyped_of_completion hlower hCompletion hFull)

theorem codePrefixExtractor_prefixChecker_complete
    {lower : List Tok → PartialProgram}
    (hlower : LowersCodePrefix lower) :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (ExtractorPrefixChecker programWellTyped (codePrefixExtractor lower)) := by
  exact conservative_extractors_give_complete_prefix_checkers
    (codePrefixExtractor_conservative hlower)
    programWellTyped_complete

/--
Relational lowering from token prefixes to old partial-program frontiers.

This is the shape a generated parser/frontier should expose.  A single token
prefix may lower to several old partial states: for example, `move x` can be
the whole term or the left side of `move x == ...`.
-/
def RelLowersCodePrefix
    (lowers : List Tok → PartialProgram → Prop) : Prop :=
  ∀ pref full,
    CodeCompletesProgram pref full →
    ∃ frontier,
      lowers pref frontier ∧ CompletesProgram frontier full

def relationalCodePrefixChecker
    (lowers : List Tok → PartialProgram → Prop) (pref : List Tok) : Prop :=
  ∃ frontier,
    lowers pref frontier ∧ programWellTyped (extractProgram frontier)

theorem relationalCodePrefixChecker_complete
    {lowers : List Tok → PartialProgram → Prop}
    (hlower : RelLowersCodePrefix lowers) :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (relationalCodePrefixChecker lowers) := by
  intro pref hcompletable
  obtain ⟨full, hcompletion, hwellTyped⟩ := hcompletable
  obtain ⟨frontier, hlowered, hfrontierCompletion⟩ :=
    hlower pref full hcompletion
  exact ⟨frontier, hlowered,
    extractProgram_wellTyped_of_completion hfrontierCompletion hwellTyped⟩

structure LoweredTermCompletion (pref : List Tok) where
  completion : ValidTermCompletion pref
  frontier : PartialProgram
  lowered : CompletesProgram frontier completion.term

namespace LoweredTermCompletion

def completedTokens {pref : List Tok}
    (completion : LoweredTermCompletion pref) : List Tok :=
  completion.completion.completedTokens

theorem codeCompletes {pref : List Tok}
    (completion : LoweredTermCompletion pref) :
    CodeCompletesProgram pref completion.completion.term :=
  completion.completion.codeCompletes

end LoweredTermCompletion

/--
Exact specification lowering: every grammar/AST completion can be lowered to
the old partial program `.done full`.

This is not an implementation strategy for an incremental checker; it is the
smallest correctness target for any executable parser/lowering pair.  A real
generated lowering can be proved complete against `CodeCompletesProgram` by
showing it covers the same completions with more informative partial states.
-/
inductive completionLower : List Tok → PartialProgram → Prop where
  | done {pref : List Tok} {full : Program} :
      CodeCompletesProgram pref full →
      completionLower pref (.done full)

theorem completionLower_lowers :
    RelLowersCodePrefix completionLower := by
  intro pref full hcompletion
  exact ⟨.done full, completionLower.done hcompletion,
    ConservativeExtractor.Generated.CompletesTerm.done⟩

theorem completionLower_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (relationalCodePrefixChecker completionLower) := by
  exact relationalCodePrefixChecker_complete completionLower_lowers

/--
Parser-backed specification lowering.

This keeps the old `.done full` lowering target, but it is no longer detached
from the generated parser: every lowered full program must come with a checked
frontier state found by the generated fuel enumerator for the same token
prefix.  This is the bridge theorem an executable, more precise lowering can
refine later by replacing `.done full` with the old partial state represented
by that frontier.

`parserActualCompletionLower` below is the stronger exact version: it also
records that the checked state completes the same parse tree that denotes
`full`.
-/
inductive parserBackedCompletionLower :
    List Tok → PartialProgram → Prop where
  | done {pref : List Tok} {full : Program} {fuel : Nat}
      {parsed : CheckableGrammar.ParsedFrontierState
        checkableGrammar .cterm pref} :
      CodeCompletesProgram pref full →
      parsed ∈ ctermFrontierStatesFuel fuel pref →
      parserBackedCompletionLower pref (.done full)

theorem parserBackedCompletionLower_lowers :
    RelLowersCodePrefix parserBackedCompletionLower := by
  intro pref full hcompletion
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes hcompletion
  obtain ⟨parsed, hparsed⟩ := hfound minFuel (Nat.le_refl _)
  exact ⟨.done full,
    parserBackedCompletionLower.done hcompletion hparsed,
    ConservativeExtractor.Generated.CompletesTerm.done⟩

theorem parserBackedCompletionLower_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (relationalCodePrefixChecker parserBackedCompletionLower) := by
  exact relationalCodePrefixChecker_complete parserBackedCompletionLower_lowers

/--
Exact parser-backed lowering for the current prefix.

This is the complete, low-trust correctness path: a lowered `.done full`
program is allowed only when the executable frontier enumerator has found a
checked parser frontier for the same prefix, that frontier is proved to
complete the actual parse tree, and that tree denotes `full`.

Unlike `parserPreciseFrontierLower_lowers`, this theorem does not use the
generated `.fallback`/`.cutoff` old-frontier case.  It is intentionally exact:
it proves the parser/completion story independently of how much of the older
partial-program representation has been generated precisely.
-/
inductive parserActualCompletionLower :
    List Tok → PartialProgram → Prop where
  | done {pref : List Tok} {full : Program} {fuel : Nat}
      {parsed : CheckableGrammar.ParsedFrontierState
        checkableGrammar .cterm pref} {tree : Tree Tok} :
      parsed ∈ ctermFrontierStatesFuel fuel pref →
      CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
        parsed.state tree →
      DenotesTerm tree full →
      parserActualCompletionLower pref (.done full)

theorem parserActualCompletionLower_lowers :
    RelLowersCodePrefix parserActualCompletionLower := by
  intro pref full hcompletion
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes_with_completion
      hcompletion
  obtain ⟨parsed, tree, hparsed, hstateCompletes, hdenotes⟩ :=
    hfound minFuel (Nat.le_refl _)
  exact ⟨.done full,
    parserActualCompletionLower.done hparsed hstateCompletes hdenotes,
    ConservativeExtractor.Generated.CompletesTerm.done⟩

theorem parserActualCompletionLower_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (relationalCodePrefixChecker parserActualCompletionLower) := by
  exact relationalCodePrefixChecker_complete
    parserActualCompletionLower_lowers

def parserActualCodePrefixChecker (pref : List Tok) : Prop :=
  relationalCodePrefixChecker parserActualCompletionLower pref

theorem parserActualCodePrefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      parserActualCodePrefixChecker := by
  exact parserActualCompletionLower_prefixChecker_complete

/--
Extractor-backed checker for token prefixes using the exact parser frontier
certificate.

This is the main low-trust bridge from partial code to the existing extractor
theorem.  A positive witness contains an old partial program accepted by
`extractProgram`, but the only complete totality branch of
`parserActualCompletionLower` is `.done full` accompanied by:

* a generated parser frontier state for the same token prefix,
* a proof that the state completes the actual parse tree, and
* a proof that the tree denotes the full program.
-/
def parserActualExtractorPrefixChecker (pref : List Tok) : Prop :=
  ∃ frontier,
    parserActualCompletionLower pref frontier ∧
    programWellTyped (extractProgram frontier)

theorem parserActualExtractorPrefixChecker_eq :
    parserActualExtractorPrefixChecker =
      relationalCodePrefixChecker parserActualCompletionLower := by
  rfl

theorem parserActualExtractorPrefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      parserActualExtractorPrefixChecker := by
  exact parserActualCodePrefixChecker_complete

theorem parserActualCompletionLower_of_codeCompletes
    {pref : List Tok} {full : Program}
    (hcompletion : CodeCompletesProgram pref full) :
    parserActualCompletionLower pref (.done full) := by
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes_with_completion
      hcompletion
  obtain ⟨parsed, tree, hparsed, hstateCompletes, hdenotes⟩ :=
    hfound minFuel (Nat.le_refl _)
  exact parserActualCompletionLower.done hparsed hstateCompletes hdenotes

theorem decodedTermSourceCompletion_parserActualLower
    {pref : List Tok}
    (completion : ValidDecodedTermSourceCompletion pref) :
    parserActualCompletionLower pref (.done completion.term) := by
  exact parserActualCompletionLower_of_codeCompletes
    completion.codeCompletes

theorem decodedTermSourceCompletion_parserActualExtractorPrefixChecker
    {pref : List Tok}
    (completion : ValidDecodedTermSourceCompletion pref)
    (hwellTyped : ProgramWellTyped completion.term) :
    parserActualExtractorPrefixChecker pref := by
  refine ⟨.done completion.term,
    decodedTermSourceCompletion_parserActualLower completion, ?_⟩
  exact extractProgram_wellTyped_of_completion
    ConservativeExtractor.Generated.CompletesTerm.done hwellTyped

theorem decodedTermSourceParser_completion_lowers_of_some
    {fuel : Nat} {pref : List Tok} {source : String}
    (hsource : decodedTermSourceParser.complete fuel pref = some source) :
    ∃ completion : ValidDecodedTermSourceCompletion pref,
      completion.source = source ∧
      parserActualCompletionLower pref (.done completion.term) := by
  obtain ⟨completion, hcompletionSource⟩ :=
    decodedTermSourceParser_sound_of_some hsource
  exact ⟨completion, hcompletionSource,
    decodedTermSourceCompletion_parserActualLower completion⟩

/--
Ambiguity is represented by the completion relation, not by choosing a
single parser state.  If the same token prefix can complete to two different
programs, the exact parser-backed lowering completes the same prefix to both.
-/
theorem parserActualCompletionLower_same_prefix_for_completions
    {pref : List Tok} {left right : Program}
    (hleft : CodeCompletesProgram pref left)
    (hright : CodeCompletesProgram pref right) :
    parserActualCompletionLower pref (.done left) ∧
      parserActualCompletionLower pref (.done right) :=
  ⟨parserActualCompletionLower_of_codeCompletes hleft,
    parserActualCompletionLower_of_codeCompletes hright⟩

theorem parserActualCompletionLower_has_both_moveX_completions :
    parserActualCompletionLower moveXPrefix (.done moveXTerm) ∧
      parserActualCompletionLower moveXPrefix (.done moveXEqMoveXTerm) :=
  parserActualCompletionLower_same_prefix_for_completions
    moveXPrefix_codeCompletes_as_move
    moveXPrefix_codeCompletes_as_eq

theorem parserActualCompletionLower_has_x_assignment_completion :
    parserActualCompletionLower xPrefix (.done assignXMoveXTerm) :=
  parserActualCompletionLower_of_codeCompletes
    xPrefix_codeCompletes_as_assignment

def generatedPartialMoveX : PartialProgram :=
  .moveOperand (.done xLVal)

def generatedPartialMoveXAsEqLhs : PartialProgram :=
  .termPrefix (.done moveXTerm)

def generatedPartialXAsAssignmentLhs : PartialProgram :=
  .assignLhs (.done xLVal)

def generatedPartialX : PartialLVal :=
  .varX (.done "x")

def clvalXDoneItem : Item Cat Terminal :=
  { rule := clvalVarRule, dot := 1 }

def clvalXDoneFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .clval :=
  CheckableGrammar.CheckedFrontierState.boundary clvalXDoneItem
    (by native_decide) [.token xTok] (by native_decide)

theorem clvalXDoneFrontierState_completes_clvalXTree :
    CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
      clvalXDoneFrontierState clvalXTree := by
  simp [clvalXDoneFrontierState, clvalXDoneItem,
    CheckableGrammar.CheckedFrontierStateCompletes, clvalXTree,
    clvalVarRule]
  exact ⟨[], by
    simpa [clvalXDoneItem, clvalVarRule, Item.after] using
      (DerivesSeq.nil :
        DerivesSeq checkableGrammar.toGrammar [] [] [])⟩

theorem generatedPartialX_completes_actual_lval :
    CompletesLVal generatedPartialX xLVal := by
  simpa [generatedPartialX] using
    (GeneratedFrontierLower.checkedLValFrontierLower_completes_of_stateCompletes
      (GeneratedFrontierLower.CheckedLValFrontierLower.clvalVar_varX_boundary)
      clvalXDoneFrontierState_completes_clvalXTree
      clvalX_denotes)

theorem moveXDoneFrontierState_completes_moveXTree :
    CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
      moveXDoneFrontierState moveXTree := by
  simp [moveXDoneFrontierState, moveXDoneItem,
    CheckableGrammar.CheckedFrontierStateCompletes, moveXTree,
    ctermMoveRule]
  exact ⟨[], by
    simpa [moveXDoneItem, ctermMoveRule, Item.after] using
      (DerivesSeq.nil :
        DerivesSeq checkableGrammar.toGrammar [] [] [])⟩

theorem moveXEqAfterLhsFrontierState_completes_moveXEqMoveXTree :
    CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
      moveXEqAfterLhsFrontierState moveXEqMoveXTree := by
  simp [moveXEqAfterLhsFrontierState, moveXEqAfterLhsItem,
    CheckableGrammar.CheckedFrontierStateCompletes, moveXEqMoveXTree,
    ctermEqRule]
  exact ⟨[Tok.eqEq] ++ moveXPrefix, by
    simpa [moveXEqAfterLhsItem, ctermEqRule, Item.after] using
      (DerivesSeq.token (G := checkableGrammar.toGrammar)
        (by simp [checkableGrammar, grammar, accepts])
        (DerivesSeq.cat moveX_derives DerivesSeq.nil))⟩

theorem xAssignAfterLhsFrontierState_completes_assignXMoveXTree :
    CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
      xAssignAfterLhsFrontierState assignXMoveXTree := by
  simp [xAssignAfterLhsFrontierState, xAssignAfterLhsItem,
    CheckableGrammar.CheckedFrontierStateCompletes, assignXMoveXTree,
    ctermAssignRule]
  exact ⟨[Tok.assign] ++ moveXPrefix, by
    simpa [xAssignAfterLhsItem, ctermAssignRule, Item.after] using
      (DerivesSeq.token (G := checkableGrammar.toGrammar)
        (by simp [checkableGrammar, grammar, accepts])
        (DerivesSeq.cat moveX_derives DerivesSeq.nil))⟩

theorem generatedPartialMoveX_lowered_from_done_frontier :
    GeneratedFrontierLower.CheckedTermFrontierLower
      moveXDoneFrontierState generatedPartialMoveX := by
  simpa [generatedPartialMoveX, moveXDoneFrontierState, moveXDoneItem,
    clvalXTree, xLVal] using
    (GeneratedFrontierLower.CheckedTermFrontierLower.ctermMove_moveOperand_boundary
      (by simp [denoteLVal?, xTok]))

theorem generatedPartialMoveXAsEqLhs_lowered_from_lhs_frontier :
    GeneratedFrontierLower.CheckedTermFrontierLower
      moveXEqAfterLhsFrontierState generatedPartialMoveXAsEqLhs := by
  simpa [generatedPartialMoveXAsEqLhs, moveXEqAfterLhsFrontierState,
    moveXEqAfterLhsItem, moveXTree, moveXTerm] using
    (GeneratedFrontierLower.CheckedTermFrontierLower.ctermEq_termPrefix_boundary
      (by simp [denoteTerm?, denoteLVal?, clvalXTree, xLVal, xTok]))

theorem generatedPartialXAsAssignmentLhs_lowered_from_lhs_frontier :
    GeneratedFrontierLower.CheckedTermFrontierLower
      xAssignAfterLhsFrontierState generatedPartialXAsAssignmentLhs := by
  simpa [generatedPartialXAsAssignmentLhs, xAssignAfterLhsFrontierState,
    xAssignAfterLhsItem, clvalXTree, xLVal] using
    (GeneratedFrontierLower.CheckedTermFrontierLower.ctermAssign_assignLhs_boundary
      (by simp [denoteLVal?, xTok]))

theorem generatedPartialMoveX_frontier_sound :
    GeneratedFrontierLower.CheckedTermFrontierLower
      moveXDoneFrontierState generatedPartialMoveX ∧
    CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
      moveXDoneFrontierState moveXTree ∧
    DenotesTerm moveXTree moveXTerm ∧
    CompletesProgram generatedPartialMoveX moveXTerm := by
  exact ⟨generatedPartialMoveX_lowered_from_done_frontier,
    moveXDoneFrontierState_completes_moveXTree,
    moveX_denotes,
    GeneratedFrontierLower.checkedTermFrontierLower_completes_of_stateCompletes
      generatedPartialMoveX_lowered_from_done_frontier
      moveXDoneFrontierState_completes_moveXTree
      moveX_denotes⟩

theorem generatedPartialMoveXAsEqLhs_frontier_sound :
    GeneratedFrontierLower.CheckedTermFrontierLower
      moveXEqAfterLhsFrontierState generatedPartialMoveXAsEqLhs ∧
    CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
      moveXEqAfterLhsFrontierState moveXEqMoveXTree ∧
    DenotesTerm moveXEqMoveXTree moveXEqMoveXTerm ∧
    CompletesProgram generatedPartialMoveXAsEqLhs moveXEqMoveXTerm := by
  exact ⟨generatedPartialMoveXAsEqLhs_lowered_from_lhs_frontier,
    moveXEqAfterLhsFrontierState_completes_moveXEqMoveXTree,
    moveXEqMoveX_denotes,
    GeneratedFrontierLower.checkedTermFrontierLower_completes_of_stateCompletes
      generatedPartialMoveXAsEqLhs_lowered_from_lhs_frontier
      moveXEqAfterLhsFrontierState_completes_moveXEqMoveXTree
      moveXEqMoveX_denotes⟩

theorem generatedPartialXAsAssignmentLhs_frontier_sound :
    GeneratedFrontierLower.CheckedTermFrontierLower
      xAssignAfterLhsFrontierState generatedPartialXAsAssignmentLhs ∧
    CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
      xAssignAfterLhsFrontierState assignXMoveXTree ∧
    DenotesTerm assignXMoveXTree assignXMoveXTerm ∧
    CompletesProgram generatedPartialXAsAssignmentLhs assignXMoveXTerm := by
  exact ⟨generatedPartialXAsAssignmentLhs_lowered_from_lhs_frontier,
    xAssignAfterLhsFrontierState_completes_assignXMoveXTree,
    assignXMoveX_denotes,
    GeneratedFrontierLower.checkedTermFrontierLower_completes_of_stateCompletes
      generatedPartialXAsAssignmentLhs_lowered_from_lhs_frontier
      xAssignAfterLhsFrontierState_completes_assignXMoveXTree
      assignXMoveX_denotes⟩

def defaultName : Name :=
  "__fw_default"

def defaultLVal : LVal :=
  SyntaxCtor.clvalVar_ctor defaultName

def derefDefaultLVal : LVal :=
  SyntaxCtor.clvalDeref_ctor defaultLVal

def moveDerefDefaultTerm : Term :=
  SyntaxCtor.ctermMove_ctor derefDefaultLVal

def boxMoveStarPrefix : List Tok :=
  [.box] ++ moveStarPrefix

def boxMoveDerefDefaultTerm : Term :=
  SyntaxCtor.ctermBox_ctor moveDerefDefaultTerm

def rootLifetime : Lifetime :=
  LwRust.Core.Lifetime.root

def blockEmptyPrefix : List Tok :=
  [.block, .lifetime rootLifetime, .lbrace]

def blockEmptyTerm : Term :=
  SyntaxCtor.ctermBlock_ctor rootLifetime []

def boxUnitPrefix : List Tok :=
  [.box, .unit]

def boxUnitTerm : Term :=
  SyntaxCtor.ctermBox_ctor SyntaxCtor.ctermUnit_ctor

def generatedPartialMoveStar : PartialProgram :=
  .moveOperand .derefStart

def generatedPartialBoxMoveStar : PartialProgram :=
  .boxOperand generatedPartialMoveStar

def generatedPartialBlockEmptyTerms : PartialProgram :=
  .blockTerms rootLifetime (.done [])

def generatedPartialBlockOpenTerms : PartialProgram :=
  .blockTerms rootLifetime .cutoff

def generatedPartialBoxUnit : PartialProgram :=
  .boxOperand (.done SyntaxCtor.ctermUnit_ctor)

def clvalDerefStartItem : Item Cat Terminal :=
  { rule := clvalDerefRule, dot := 1 }

def clvalDerefStartFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .clval :=
  CheckableGrammar.CheckedFrontierState.boundary clvalDerefStartItem
    (by native_decide) [.token .star] (by native_decide)

theorem clvalDerefStartFrontierState_pref :
    clvalDerefStartFrontierState.pref = [.star] := by
  native_decide

def moveStarDescendFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm :=
  CheckableGrammar.CheckedFrontierState.descend
    ({ rule := ctermMoveRule, dot := 1 } : Item Cat Terminal)
    (by native_decide) .clval [] (by native_decide)
    [.token .moveKw] (by native_decide) clvalDerefStartFrontierState

theorem moveStarDescendFrontierState_pref :
    moveStarDescendFrontierState.pref = moveStarPrefix := by
  native_decide

def boxMoveStarDescendFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm :=
  CheckableGrammar.CheckedFrontierState.descend
    ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal)
    (by native_decide) .cterm [] (by native_decide)
    [.token .box] (by native_decide) moveStarDescendFrontierState

theorem boxMoveStarDescendFrontierState_pref :
    boxMoveStarDescendFrontierState.pref = boxMoveStarPrefix := by
  native_decide

def ctermsEmptyItem : Item Cat Terminal :=
  { rule := ctermsEmptyRule, dot := 0 }

def ctermsEmptyFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterms :=
  CheckableGrammar.CheckedFrontierState.boundary ctermsEmptyItem
    (by native_decide) [] (by native_decide)

theorem ctermsEmptyFrontierState_pref :
    ctermsEmptyFrontierState.pref = [] := by
  native_decide

def blockEmptyTermsDescendFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm :=
  CheckableGrammar.CheckedFrontierState.descend
    ({ rule := ctermBlockRule, dot := 3 } : Item Cat Terminal)
    (by native_decide) .cterms [.token .rbrace] (by native_decide)
    [.token .block, .token (.lifetime rootLifetime), .token .lbrace]
    (by native_decide) ctermsEmptyFrontierState

theorem blockEmptyTermsDescendFrontierState_pref :
    blockEmptyTermsDescendFrontierState.pref = blockEmptyPrefix := by
  native_decide

def blockOpenBoundaryItem : Item Cat Terminal :=
  { rule := ctermBlockRule, dot := 3 }

def blockOpenBoundaryFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm :=
  CheckableGrammar.CheckedFrontierState.boundary blockOpenBoundaryItem
    (by native_decide)
    [.token .block, .token (.lifetime rootLifetime), .token .lbrace]
    (by native_decide)

theorem blockOpenBoundaryFrontierState_pref :
    blockOpenBoundaryFrontierState.pref = blockEmptyPrefix := by
  native_decide

def ctermUnitDoneItem : Item Cat Terminal :=
  { rule := ctermUnitRule, dot := 1 }

def ctermUnitDoneFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm :=
  CheckableGrammar.CheckedFrontierState.boundary ctermUnitDoneItem
    (by native_decide) [.token .unit] (by native_decide)

theorem ctermUnitDoneFrontierState_pref :
    ctermUnitDoneFrontierState.pref = [.unit] := by
  native_decide

def boxUnitDescendFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm :=
  CheckableGrammar.CheckedFrontierState.descend
    ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal)
    (by native_decide) .cterm [] (by native_decide)
    [.token .box] (by native_decide) ctermUnitDoneFrontierState

theorem boxUnitDescendFrontierState_pref :
    boxUnitDescendFrontierState.pref = boxUnitPrefix := by
  native_decide

def parserPreciseFrontierLower
    (pref : List Tok) (frontier : PartialProgram) : Prop :=
  ∃ fuel parsed,
    parsed ∈ ctermFrontierStatesFuel fuel pref ∧
    GeneratedFrontierLower.CheckedTermFrontierLower parsed.state frontier

/--
The generated parser-frontier bridge exposed under its total-correctness name.

The relation contains the precise syntax-derived lowerings below and the
generated `CheckedTermFrontierLower.fallback` case to old `.cutoff`, so every
checked parser frontier has at least one old partial-program representative.
-/
abbrev parserGeneratedFrontierLower :
    List Tok → PartialProgram → Prop :=
  parserPreciseFrontierLower

theorem parserPreciseFrontierLower_moveX_done :
    parserPreciseFrontierLower moveXPrefix generatedPartialMoveX := by
  rw [← moveXDoneFrontierState_pref]
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_checked_exact
      moveXDoneFrontierState
  obtain ⟨parsed, hstate, hmem⟩ :=
    hfound minFuel (Nat.le_refl _)
  refine ⟨minFuel, parsed, hmem, ?_⟩
  · rw [hstate]
    simpa [generatedPartialMoveX, moveXDoneFrontierState, moveXDoneItem,
      clvalXTree, xLVal] using
      (GeneratedFrontierLower.CheckedTermFrontierLower.ctermMove_moveOperand_boundary
        (by simp [denoteLVal?, xTok]))

theorem parserPreciseFrontierLower_moveX_eq_lhs :
    parserPreciseFrontierLower moveXPrefix generatedPartialMoveXAsEqLhs := by
  rw [← moveXEqAfterLhsFrontierState_pref]
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_checked_exact
      moveXEqAfterLhsFrontierState
  obtain ⟨parsed, hstate, hmem⟩ :=
    hfound minFuel (Nat.le_refl _)
  refine ⟨minFuel, parsed, hmem, ?_⟩
  · rw [hstate]
    simpa [generatedPartialMoveXAsEqLhs, moveXEqAfterLhsFrontierState,
      moveXEqAfterLhsItem, moveXTree, moveXTerm] using
      (GeneratedFrontierLower.CheckedTermFrontierLower.ctermEq_termPrefix_boundary
        (by simp [denoteTerm?, denoteLVal?, clvalXTree, xLVal, xTok]))

theorem parserPreciseFrontierLower_x_assignment_lhs :
    parserPreciseFrontierLower xPrefix generatedPartialXAsAssignmentLhs := by
  rw [← xAssignAfterLhsFrontierState_pref]
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_checked_exact
      xAssignAfterLhsFrontierState
  obtain ⟨parsed, hstate, hmem⟩ :=
    hfound minFuel (Nat.le_refl _)
  refine ⟨minFuel, parsed, hmem, ?_⟩
  · rw [hstate]
    simpa [generatedPartialXAsAssignmentLhs, xAssignAfterLhsFrontierState,
      xAssignAfterLhsItem, clvalXTree, xLVal] using
      (GeneratedFrontierLower.CheckedTermFrontierLower.ctermAssign_assignLhs_boundary
        (by simp [denoteLVal?, xTok]))

theorem parserPreciseFrontierLower_moveStar_descend :
    parserPreciseFrontierLower moveStarPrefix generatedPartialMoveStar := by
  rw [← moveStarDescendFrontierState_pref]
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_checked_exact
      moveStarDescendFrontierState
  obtain ⟨parsed, hstate, hmem⟩ :=
    hfound minFuel (Nat.le_refl _)
  refine ⟨minFuel, parsed, hmem, ?_⟩
  · rw [hstate]
    simpa [generatedPartialMoveStar, moveStarDescendFrontierState,
      clvalDerefStartFrontierState, clvalDerefStartItem] using
      (GeneratedFrontierLower.CheckedTermFrontierLower.ctermMove_moveOperand_descend
        GeneratedFrontierLower.CheckedLValFrontierLower.clvalDeref_derefStart_boundary)

theorem parserPreciseFrontierLower_boxMoveStar_descend :
    parserPreciseFrontierLower boxMoveStarPrefix
      generatedPartialBoxMoveStar := by
  rw [← boxMoveStarDescendFrontierState_pref]
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_checked_exact
      boxMoveStarDescendFrontierState
  obtain ⟨parsed, hstate, hmem⟩ :=
    hfound minFuel (Nat.le_refl _)
  refine ⟨minFuel, parsed, hmem, ?_⟩
  · rw [hstate]
    simpa [generatedPartialBoxMoveStar, generatedPartialMoveStar,
      boxMoveStarDescendFrontierState, moveStarDescendFrontierState,
      clvalDerefStartFrontierState, clvalDerefStartItem] using
      (GeneratedFrontierLower.CheckedTermFrontierLower.ctermBox_boxOperand_descend
        (GeneratedFrontierLower.CheckedTermFrontierLower.ctermMove_moveOperand_descend
          GeneratedFrontierLower.CheckedLValFrontierLower.clvalDeref_derefStart_boundary))

theorem parserPreciseFrontierLower_blockEmptyTerms_descend :
    parserPreciseFrontierLower blockEmptyPrefix
      generatedPartialBlockEmptyTerms := by
  rw [← blockEmptyTermsDescendFrontierState_pref]
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_checked_exact
      blockEmptyTermsDescendFrontierState
  obtain ⟨parsed, hstate, hmem⟩ :=
    hfound minFuel (Nat.le_refl _)
  refine ⟨minFuel, parsed, hmem, ?_⟩
  · rw [hstate]
    simpa [generatedPartialBlockEmptyTerms,
      blockEmptyTermsDescendFrontierState, ctermsEmptyFrontierState,
      ctermsEmptyItem, rootLifetime] using
      (GeneratedFrontierLower.CheckedTermFrontierLower.ctermBlock_blockTerms_descend
        GeneratedFrontierLower.CheckedTermsFrontierLower.ctermsEmpty_done_boundary)

theorem parserPreciseFrontierLower_blockOpen_boundary :
    parserPreciseFrontierLower blockEmptyPrefix
      generatedPartialBlockOpenTerms := by
  rw [← blockOpenBoundaryFrontierState_pref]
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_checked_exact
      blockOpenBoundaryFrontierState
  obtain ⟨parsed, hstate, hmem⟩ :=
    hfound minFuel (Nat.le_refl _)
  refine ⟨minFuel, parsed, hmem, ?_⟩
  · rw [hstate]
    simpa [generatedPartialBlockOpenTerms,
      blockOpenBoundaryFrontierState, blockOpenBoundaryItem,
      rootLifetime] using
      GeneratedFrontierLower.CheckedTermFrontierLower.ctermBlock_dot3_boundary

theorem parserPreciseFrontierLower_boxUnit_descend :
    parserPreciseFrontierLower boxUnitPrefix
      generatedPartialBoxUnit := by
  rw [← boxUnitDescendFrontierState_pref]
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_checked_exact
      boxUnitDescendFrontierState
  obtain ⟨parsed, hstate, hmem⟩ :=
    hfound minFuel (Nat.le_refl _)
  refine ⟨minFuel, parsed, hmem, ?_⟩
  · rw [hstate]
    simpa [generatedPartialBoxUnit, boxUnitDescendFrontierState,
      ctermUnitDoneFrontierState, ctermUnitDoneItem] using
      (GeneratedFrontierLower.CheckedTermFrontierLower.ctermBox_boxOperand_descend
        GeneratedFrontierLower.CheckedTermFrontierLower.ctermUnit_done_boundary)

theorem parserPreciseFrontierLower_has_both_moveX_frontiers :
    parserPreciseFrontierLower moveXPrefix generatedPartialMoveX ∧
    parserPreciseFrontierLower moveXPrefix generatedPartialMoveXAsEqLhs :=
  ⟨parserPreciseFrontierLower_moveX_done,
    parserPreciseFrontierLower_moveX_eq_lhs⟩

theorem parserPreciseFrontierLower_lowers :
    RelLowersCodePrefix parserPreciseFrontierLower := by
  intro pref full hcompletion
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes_with_completion
      hcompletion
  obtain ⟨parsed, tree, hparsed, hstateCompletes, hdenotes⟩ :=
    hfound minFuel (Nat.le_refl _)
  obtain ⟨frontier, hlower⟩ :=
    GeneratedFrontierLower.checkedTermFrontierLower_exists parsed.state
  exact ⟨frontier,
    ⟨minFuel, parsed, hparsed, hlower⟩,
    GeneratedFrontierLower.checkedTermFrontierLower_completes_of_stateCompletes
      hlower hstateCompletes hdenotes⟩

theorem parserPreciseFrontierLower_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (relationalCodePrefixChecker parserPreciseFrontierLower) := by
  exact relationalCodePrefixChecker_complete
    parserPreciseFrontierLower_lowers

theorem parserGeneratedFrontierLower_lowers :
    RelLowersCodePrefix parserGeneratedFrontierLower :=
  parserPreciseFrontierLower_lowers

theorem parserGeneratedFrontierLower_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (relationalCodePrefixChecker parserGeneratedFrontierLower) :=
  parserPreciseFrontierLower_prefixChecker_complete

def parserPreciseCodePrefixChecker (pref : List Tok) : Prop :=
  relationalCodePrefixChecker parserPreciseFrontierLower pref

theorem parserPreciseCodePrefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      parserPreciseCodePrefixChecker := by
  exact parserPreciseFrontierLower_prefixChecker_complete

def parserGeneratedCodePrefixChecker (pref : List Tok) : Prop :=
  relationalCodePrefixChecker parserGeneratedFrontierLower pref

theorem parserGeneratedCodePrefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      parserGeneratedCodePrefixChecker := by
  exact parserGeneratedFrontierLower_prefixChecker_complete

theorem parserPreciseFrontierLower_has_cutoff_moveX :
    parserPreciseFrontierLower moveXPrefix .cutoff := by
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes
      moveXPrefix_codeCompletes_as_move
  obtain ⟨parsed, hparsed⟩ := hfound minFuel (Nat.le_refl _)
  exact ⟨minFuel, parsed, hparsed,
    GeneratedFrontierLower.CheckedTermFrontierLower.fallback⟩

theorem generatedCutoff_completes_moveX_ambiguity :
    parserPreciseFrontierLower moveXPrefix .cutoff ∧
    CompletesProgram .cutoff moveXTerm ∧
    CompletesProgram .cutoff moveXEqMoveXTerm := by
  exact ⟨parserPreciseFrontierLower_has_cutoff_moveX,
    _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff,
    _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff⟩

theorem parserGeneratedFrontierLower_same_cutoff_for_completions
    {pref : List Tok} {left right : Program}
    (hleft : CodeCompletesProgram pref left)
    (_hright : CodeCompletesProgram pref right) :
    parserGeneratedFrontierLower pref .cutoff ∧
    CompletesProgram .cutoff left ∧
    CompletesProgram .cutoff right := by
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes hleft
  obtain ⟨parsed, hparsed⟩ := hfound minFuel (Nat.le_refl _)
  exact ⟨
    ⟨minFuel, parsed, hparsed,
      GeneratedFrontierLower.CheckedTermFrontierLower.fallback⟩,
    _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff,
    _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff⟩

theorem generatedPartialMoveX_completes :
    CompletesProgram generatedPartialMoveX moveXTerm := by
  simpa [generatedPartialMoveX, moveXTerm] using
    (GeneratedFrontierLower.ctermMove_moveOperand_boundary_completes
      (operand := xLVal))

theorem generatedPartialMoveXAsEqLhs_completes :
    CompletesProgram generatedPartialMoveXAsEqLhs moveXEqMoveXTerm := by
  simpa [generatedPartialMoveXAsEqLhs, moveXTerm,
    moveXEqMoveXTerm] using
    (GeneratedFrontierLower.ctermEq_termPrefix_boundary_completes
      (lhs := moveXTerm) (rhs := moveXTerm))

theorem generatedPartialXAsAssignmentLhs_completes :
    CompletesProgram generatedPartialXAsAssignmentLhs assignXMoveXTerm := by
  simpa [generatedPartialXAsAssignmentLhs, assignXMoveXTerm] using
    (GeneratedFrontierLower.ctermAssign_assignLhs_boundary_completes
      (lhs := xLVal) (rhs := moveXTerm))

theorem generatedPartialMoveStar_completes :
    CompletesProgram generatedPartialMoveStar moveDerefDefaultTerm := by
  simpa [generatedPartialMoveStar, moveDerefDefaultTerm,
    derefDefaultLVal] using
    (GeneratedFrontierLower.ctermMove_moveOperand_descend_completes
      (operand := _root_.ConservativeExtractor.Generated.PartialLVal.derefStart)
      (operand' := derefDefaultLVal)
      (GeneratedFrontierLower.clvalDeref_derefStart_boundary_completes
        (operand := defaultLVal)))

theorem generatedPartialBoxMoveStar_completes :
    CompletesProgram generatedPartialBoxMoveStar
      boxMoveDerefDefaultTerm := by
  simpa [generatedPartialBoxMoveStar, boxMoveDerefDefaultTerm] using
    (GeneratedFrontierLower.ctermBox_boxOperand_descend_completes
      (operand := generatedPartialMoveStar)
      (operand' := moveDerefDefaultTerm)
      generatedPartialMoveStar_completes)

theorem generatedPartialBlockEmptyTerms_completes :
    CompletesProgram generatedPartialBlockEmptyTerms blockEmptyTerm := by
  simpa [generatedPartialBlockEmptyTerms, blockEmptyTerm] using
    (GeneratedFrontierLower.ctermBlock_blockTerms_descend_completes
      (lifetime := rootLifetime)
      (terms := _root_.ConservativeExtractor.Generated.PartialTerms.done [])
      (terms' := [])
      _root_.ConservativeExtractor.Generated.CompletesTerms.done)

theorem generatedPartialBlockOpenTerms_completes :
    CompletesProgram generatedPartialBlockOpenTerms blockEmptyTerm := by
  simpa [generatedPartialBlockOpenTerms, blockEmptyTerm] using
    (GeneratedFrontierLower.ctermBlock_dot3_boundary_completes
      (lifetime := rootLifetime) (terms := []))

theorem generatedPartialBoxUnit_completes :
    CompletesProgram generatedPartialBoxUnit boxUnitTerm := by
  simpa [generatedPartialBoxUnit, boxUnitTerm] using
    (GeneratedFrontierLower.ctermBox_boxOperand_descend_completes
      (operand :=
        _root_.ConservativeExtractor.Generated.PartialTerm.done
          SyntaxCtor.ctermUnit_ctor)
      (operand' := SyntaxCtor.ctermUnit_ctor)
      GeneratedFrontierLower.ctermUnit_done_boundary_completes)

/--
Complete parser-backed relation that keeps precise generated frontiers when
available and also retains the exact checked-parser `.done full` certificate.

The `.precise` branch demonstrates that generated frontiers can distinguish
grammar contexts such as `move x` as a complete move term, equality lhs, or
assignment lhs.  Its totality proof now uses parser-state completion evidence
and `checkedTermFrontierLower_completes_of_stateCompletes`, so it does not rely
on default raw completions.  The `.parserDone` branch keeps the exact
`.done full` certificate available as a small specification fallback.
-/
inductive parserCertifiedFrontierLower : List Tok → PartialProgram → Prop where
  | precise {pref : List Tok} {frontier : PartialProgram} :
      parserPreciseFrontierLower pref frontier →
      parserCertifiedFrontierLower pref frontier
  | parserDone {pref : List Tok} {frontier : PartialProgram} :
      parserActualCompletionLower pref frontier →
      parserCertifiedFrontierLower pref frontier

theorem parserCertifiedFrontierLower_lowers :
    RelLowersCodePrefix parserCertifiedFrontierLower := by
  intro pref full hcompletion
  obtain ⟨frontier, hlower, hcomplete⟩ :=
    parserPreciseFrontierLower_lowers pref full hcompletion
  exact ⟨frontier, .precise hlower, hcomplete⟩

theorem parserCertifiedFrontierLower_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (relationalCodePrefixChecker parserCertifiedFrontierLower) := by
  exact relationalCodePrefixChecker_complete
    parserCertifiedFrontierLower_lowers

def parserCertifiedCodePrefixChecker (pref : List Tok) : Prop :=
  relationalCodePrefixChecker parserCertifiedFrontierLower pref

theorem parserCertifiedCodePrefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      parserCertifiedCodePrefixChecker := by
  exact parserCertifiedFrontierLower_prefixChecker_complete

theorem parserCertifiedFrontierLower_has_precise_moveX_frontiers :
    parserCertifiedFrontierLower moveXPrefix generatedPartialMoveX ∧
    parserCertifiedFrontierLower moveXPrefix
      generatedPartialMoveXAsEqLhs :=
  ⟨.precise parserPreciseFrontierLower_moveX_done,
    .precise parserPreciseFrontierLower_moveX_eq_lhs⟩

theorem parserCertifiedFrontierLower_has_precise_x_assignment_lhs :
    parserCertifiedFrontierLower xPrefix generatedPartialXAsAssignmentLhs :=
  .precise parserPreciseFrontierLower_x_assignment_lhs

theorem parserCertifiedFrontierLower_has_precise_moveStar_descend :
    parserCertifiedFrontierLower moveStarPrefix generatedPartialMoveStar :=
  .precise parserPreciseFrontierLower_moveStar_descend

theorem parserCertifiedFrontierLower_has_precise_boxMoveStar_descend :
    parserCertifiedFrontierLower boxMoveStarPrefix
      generatedPartialBoxMoveStar :=
  .precise parserPreciseFrontierLower_boxMoveStar_descend

theorem parserCertifiedFrontierLower_has_precise_blockEmptyTerms_descend :
    parserCertifiedFrontierLower blockEmptyPrefix
      generatedPartialBlockEmptyTerms :=
  .precise parserPreciseFrontierLower_blockEmptyTerms_descend

theorem parserCertifiedFrontierLower_has_precise_blockOpen_boundary :
    parserCertifiedFrontierLower blockEmptyPrefix
      generatedPartialBlockOpenTerms :=
  .precise parserPreciseFrontierLower_blockOpen_boundary

theorem parserCertifiedFrontierLower_has_precise_boxUnit_descend :
    parserCertifiedFrontierLower boxUnitPrefix generatedPartialBoxUnit :=
  .precise parserPreciseFrontierLower_boxUnit_descend

/--
Legacy cutoff bridge kept as a comparison point.

`parserCertifiedFrontierLower` above is the preferred complete parser-backed
bridge: it uses precise generated frontiers when available and `.done full`
for the remaining parser-certified completions.  This relation is still useful
for demonstrating that a category-wide cutoff is sufficient for conservation,
but it is no longer the target shape for the generated lowering.
-/
inductive hybridFrontierLower : List Tok → PartialProgram → Prop where
  | precise {pref : List Tok} {frontier : PartialProgram} :
      parserPreciseFrontierLower pref frontier →
      hybridFrontierLower pref frontier
  | parserCutoff {pref : List Tok} {fuel : Nat}
      {parsed : CheckableGrammar.ParsedFrontierState
        checkableGrammar .cterm pref} :
      parsed ∈ ctermFrontierStatesFuel fuel pref →
      hybridFrontierLower pref .cutoff

theorem hybridFrontierLower_lowers :
    RelLowersCodePrefix hybridFrontierLower := by
  intro pref full hcompletion
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes hcompletion
  obtain ⟨parsed, hparsed⟩ := hfound minFuel (Nat.le_refl _)
  exact ⟨.cutoff,
    hybridFrontierLower.parserCutoff hparsed,
    ConservativeExtractor.Generated.CompletesTerm.cutoff⟩

theorem hybridFrontierLower_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (relationalCodePrefixChecker hybridFrontierLower) := by
  exact relationalCodePrefixChecker_complete hybridFrontierLower_lowers

theorem hybridFrontierLower_has_precise_moveX_frontiers :
    hybridFrontierLower moveXPrefix generatedPartialMoveX ∧
    hybridFrontierLower moveXPrefix generatedPartialMoveXAsEqLhs :=
  ⟨.precise parserPreciseFrontierLower_moveX_done,
    .precise parserPreciseFrontierLower_moveX_eq_lhs⟩

theorem hybridFrontierLower_has_precise_x_assignment_lhs :
    hybridFrontierLower xPrefix generatedPartialXAsAssignmentLhs :=
  .precise parserPreciseFrontierLower_x_assignment_lhs

theorem hybridFrontierLower_has_precise_moveStar_descend :
    hybridFrontierLower moveStarPrefix generatedPartialMoveStar :=
  .precise parserPreciseFrontierLower_moveStar_descend

theorem hybridFrontierLower_has_precise_boxMoveStar_descend :
    hybridFrontierLower boxMoveStarPrefix generatedPartialBoxMoveStar :=
  .precise parserPreciseFrontierLower_boxMoveStar_descend

theorem hybridFrontierLower_has_precise_blockEmptyTerms_descend :
    hybridFrontierLower blockEmptyPrefix generatedPartialBlockEmptyTerms :=
  .precise parserPreciseFrontierLower_blockEmptyTerms_descend

theorem hybridFrontierLower_has_precise_blockOpen_boundary :
    hybridFrontierLower blockEmptyPrefix generatedPartialBlockOpenTerms :=
  .precise parserPreciseFrontierLower_blockOpen_boundary

theorem hybridFrontierLower_has_precise_boxUnit_descend :
    hybridFrontierLower boxUnitPrefix generatedPartialBoxUnit :=
  .precise parserPreciseFrontierLower_boxUnit_descend

def generatedLoweredMoveXEqMoveX :
    LoweredTermCompletion moveXPrefix :=
  { completion := moveXEqMoveXTermCompletion
    frontier := generatedPartialMoveXAsEqLhs
    lowered := generatedPartialMoveXAsEqLhs_completes }

def generatedLoweredAssignXMoveX :
    LoweredTermCompletion xPrefix :=
  { completion := assignXMoveXTermCompletion
    frontier := generatedPartialXAsAssignmentLhs
    lowered := generatedPartialXAsAssignmentLhs_completes }

def doneLoweredTermCompletion {pref : List Tok}
    (completion : ValidTermCompletion pref) :
    LoweredTermCompletion pref :=
  { completion := completion
    frontier := .done completion.term
    lowered := ConservativeExtractor.Generated.CompletesTerm.done }

/--
Baseline lowering used only to show the bridge is inhabited.

The real generated lowering should be more precise than this; it should use
the parser frontier to construct old partial states such as block/list tails.
-/
def cutoffLower (_pref : List Tok) : PartialProgram :=
  .cutoff

theorem cutoffLower_lowers :
    LowersCodePrefix cutoffLower := by
  intro _pref _full _hCompletion
  exact ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem cutoffCodePrefixExtractor_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (ExtractorPrefixChecker programWellTyped
        (codePrefixExtractor cutoffLower)) := by
  exact codePrefixExtractor_prefixChecker_complete cutoffLower_lowers

inductive exampleFrontierLower : List Tok → PartialProgram → Prop where
  | moveXDone :
      exampleFrontierLower moveXPrefix oldPartialMoveX
  | moveXEqLhs :
      exampleFrontierLower moveXPrefix oldPartialMoveXAsEqLhs
  | xAssignLhs :
      exampleFrontierLower xPrefix oldPartialXAsAssignmentLhs
  | cutoff {pref : List Tok} :
      exampleFrontierLower pref .cutoff

theorem exampleFrontierLower_has_both_moveX_frontiers :
    exampleFrontierLower moveXPrefix oldPartialMoveX ∧
    exampleFrontierLower moveXPrefix oldPartialMoveXAsEqLhs :=
  ⟨.moveXDone, .moveXEqLhs⟩

def loweredMoveXEqMoveX :
    LoweredTermCompletion moveXPrefix :=
  { completion := moveXEqMoveXTermCompletion
    frontier := oldPartialMoveXAsEqLhs
    lowered := oldPartialMoveXAsEqLhs_completes }

def loweredAssignXMoveX :
    LoweredTermCompletion xPrefix :=
  { completion := assignXMoveXTermCompletion
    frontier := oldPartialXAsAssignmentLhs
    lowered := oldPartialXAsAssignmentLhs_completes }

theorem exampleFrontierLower_lowers_moveX_eq :
    ∃ frontier,
      exampleFrontierLower moveXPrefix frontier ∧
      CompletesProgram frontier moveXEqMoveXTerm :=
  ⟨oldPartialMoveXAsEqLhs, .moveXEqLhs,
    oldPartialMoveXAsEqLhs_completes⟩

theorem exampleFrontierLower_lowers_x_assignment :
    ∃ frontier,
      exampleFrontierLower xPrefix frontier ∧
      CompletesProgram frontier assignXMoveXTerm :=
  ⟨oldPartialXAsAssignmentLhs, .xAssignLhs,
    oldPartialXAsAssignmentLhs_completes⟩

theorem exampleFrontierLower_lowers :
    RelLowersCodePrefix exampleFrontierLower := by
  intro pref full _hcompletion
  exact ⟨.cutoff, .cutoff, ConservativeExtractor.Generated.CompletesTerm.cutoff⟩

theorem exampleFrontierLower_prefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      (relationalCodePrefixChecker exampleFrontierLower) := by
  exact relationalCodePrefixChecker_complete exampleFrontierLower_lowers

end FwRust
end GrammarFrontier
end ConservativeExtractor
