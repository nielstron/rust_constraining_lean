import LwRust.Extractor.FrontierSourceCompletion
import LwRust.Extractor.Checkers
import LwRust.Extractor.Generated.FrontierLower
import LwRust.Extractor.Extractors.NestedBlocks
import LwRust.Extractor.RelaxedMergeCompleteness

/-!
Direct parser-frontier prefix checking.

Partial code is represented by the token prefix plus a checked parser frontier
state for that prefix.  The basic completeness theorem is proved directly from
the generated parser frontier and the semantic interpretation of completed
parse trees.

The nested-block extractor wrappers below keep the parser frontier as the
external partial program.  The remaining generated lowering certificate is an
internal bridge to the already-proved nested-block extractor.
-/

namespace ConservativeExtractor
namespace GrammarFrontier
namespace FwRust

abbrev CodeCompletesProgram : List Tok → Program → Prop :=
  CodeCompletesTerm

structure ParsedTermFrontier (pref : List Tok) where
  fuel : Nat
  parsed : CheckableGrammar.ParsedFrontierState checkableGrammar .cterm pref
  found : parsed ∈ ctermFrontierStatesFuel fuel pref

namespace ParsedTermFrontier

def Completes {pref : List Tok}
    (frontier : ParsedTermFrontier pref) (program : Program) : Prop :=
  ∃ tree,
    CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
      frontier.parsed.state tree ∧
    DenotesTerm tree program

end ParsedTermFrontier

def parserFrontierPrefixChecker (pref : List Tok) : Prop :=
  ∃ frontier : ParsedTermFrontier pref,
    ∃ program : Program,
      frontier.Completes program ∧ ProgramWellTyped program

theorem parserFrontier_complete_of_codeCompletes
    {pref : List Tok} {program : Program}
    (hcompletion : CodeCompletesProgram pref program) :
    ∃ frontier : ParsedTermFrontier pref,
      frontier.Completes program := by
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes_with_completion
      hcompletion
  obtain ⟨parsed, tree, hparsed, hstateCompletes, hdenotes⟩ :=
    hfound minFuel (Nat.le_refl _)
  refine ⟨{
    fuel := minFuel
    parsed := parsed
    found := hparsed
  }, ?_⟩
  exact ⟨tree, hstateCompletes, hdenotes⟩

theorem parserFrontierPrefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      parserFrontierPrefixChecker := by
  intro pref hcompletable
  obtain ⟨program, hcompletion, hwellTyped⟩ := hcompletable
  obtain ⟨frontier, hfrontierCompletes⟩ :=
    parserFrontier_complete_of_codeCompletes hcompletion
  exact ⟨frontier, program, hfrontierCompletes, hwellTyped⟩

theorem decodedTermSourceCompletion_parserFrontierPrefixChecker
    {pref : List Tok}
    (completion : ValidDecodedTermSourceCompletion pref)
    (hwellTyped : ProgramWellTyped completion.term) :
    parserFrontierPrefixChecker pref := by
  exact parserFrontierPrefixChecker_complete pref
    ⟨completion.term, completion.codeCompletes, hwellTyped⟩

theorem decodedTermSourceParser_completion_frontier_of_some
    {fuel : Nat} {pref : List Tok} {source : String}
    (hsource : decodedTermSourceParser.complete fuel pref = some source) :
    ∃ completion : ValidDecodedTermSourceCompletion pref,
      completion.source = source ∧
      ∃ frontier : ParsedTermFrontier pref,
        frontier.Completes completion.term := by
  obtain ⟨completion, hcompletionSource⟩ :=
    decodedTermSourceParser_sound_of_some hsource
  obtain ⟨frontier, hfrontierCompletes⟩ :=
    parserFrontier_complete_of_codeCompletes completion.codeCompletes
  exact ⟨completion, hcompletionSource, frontier, hfrontierCompletes⟩

/--
Ambiguity is represented by multiple parser-frontier completions for the same
token prefix, not by forcing a single partial AST.
-/
theorem parserFrontier_same_prefix_for_completions
    {pref : List Tok} {left right : Program}
    (hleft : CodeCompletesProgram pref left)
    (hright : CodeCompletesProgram pref right) :
    (∃ frontier : ParsedTermFrontier pref, frontier.Completes left) ∧
      (∃ frontier : ParsedTermFrontier pref, frontier.Completes right) := by
  exact ⟨parserFrontier_complete_of_codeCompletes hleft,
    parserFrontier_complete_of_codeCompletes hright⟩

namespace NestedBlocks

open GeneratedFrontierLower

structure ExtractedTermFrontier (pref : List Tok) where
  parsed : ParsedTermFrontier pref
  frontierTerm : PartialTerm
  lower : CheckedTermFrontierLower parsed.parsed.state frontierTerm

namespace ExtractedTermFrontier

def extract {pref : List Tok} (frontier : ExtractedTermFrontier pref) :
    Program :=
  ConservativeExtractor.extractProgram frontier.frontierTerm

end ExtractedTermFrontier

def parserFrontierNestedBlocksPrefixChecker (pref : List Tok) : Prop :=
  ∃ frontier : ExtractedTermFrontier pref,
    ProgramWellTyped frontier.extract

theorem parserFrontierNestedBlocks_complete_of_codeCompletes
    {pref : List Tok} {program : Program}
    (hcompletion : CodeCompletesProgram pref program)
    (hwellTyped : ProgramWellTyped program) :
    ∃ frontier : ExtractedTermFrontier pref,
      ProgramWellTyped frontier.extract := by
  obtain ⟨frontier, hfrontierCompletes⟩ :=
    parserFrontier_complete_of_codeCompletes hcompletion
  obtain ⟨tree, hstateCompletes, hdenotes⟩ := hfrontierCompletes
  obtain ⟨frontierTerm, hlower⟩ :=
    checkedTermFrontierLower_exists frontier.parsed.state
  refine ⟨{
    parsed := frontier
    frontierTerm := frontierTerm
    lower := hlower
  }, ?_⟩
  exact extractProgram_wellTyped_of_completion
    (checkedTermFrontierLower_completes_of_stateCompletes
      hlower hstateCompletes hdenotes)
    hwellTyped

theorem parserFrontierNestedBlocksPrefixChecker_complete :
    PrefixCheckerComplete ProgramWellTyped CodeCompletesProgram
      parserFrontierNestedBlocksPrefixChecker := by
  intro pref hcompletable
  obtain ⟨program, hcompletion, hwellTyped⟩ := hcompletable
  exact parserFrontierNestedBlocks_complete_of_codeCompletes
    hcompletion hwellTyped

def parserFrontierNestedBlocksRelaxedPrefixChecker
    (pref : List Tok) : Prop :=
  ∃ frontier : ExtractedTermFrontier pref,
    ProgramRelaxedWellTyped frontier.extract

theorem parserFrontierNestedBlocks_relaxedComplete_of_codeCompletes
    {pref : List Tok} {program : Program}
    (hcompletion : CodeCompletesProgram pref program)
    (hwellTyped : ProgramRelaxedWellTyped program) :
    ∃ frontier : ExtractedTermFrontier pref,
      ProgramRelaxedWellTyped frontier.extract := by
  obtain ⟨frontier, hfrontierCompletes⟩ :=
    parserFrontier_complete_of_codeCompletes hcompletion
  obtain ⟨tree, hstateCompletes, hdenotes⟩ := hfrontierCompletes
  obtain ⟨frontierTerm, hlower⟩ :=
    checkedTermFrontierLower_exists frontier.parsed.state
  refine ⟨{
    parsed := frontier
    frontierTerm := frontierTerm
    lower := hlower
  }, ?_⟩
  exact extractProgram_relaxedWellTyped_of_completion
    (checkedTermFrontierLower_completes_of_stateCompletes
      hlower hstateCompletes hdenotes)
    hwellTyped

theorem parserFrontierNestedBlocksRelaxedPrefixChecker_complete :
    PrefixCheckerComplete ProgramRelaxedWellTyped CodeCompletesProgram
      parserFrontierNestedBlocksRelaxedPrefixChecker := by
  intro pref hcompletable
  obtain ⟨program, hcompletion, hwellTyped⟩ := hcompletable
  exact parserFrontierNestedBlocks_relaxedComplete_of_codeCompletes
    hcompletion hwellTyped

end NestedBlocks

theorem parserFrontier_has_both_moveX_completions :
    (∃ frontier : ParsedTermFrontier moveXPrefix,
      frontier.Completes moveXTerm) ∧
    (∃ frontier : ParsedTermFrontier moveXPrefix,
      frontier.Completes moveXEqMoveXTerm) :=
  parserFrontier_same_prefix_for_completions
    moveXPrefix_codeCompletes_as_move
    moveXPrefix_codeCompletes_as_eq

theorem parserFrontier_has_x_assignment_completion :
    ∃ frontier : ParsedTermFrontier xPrefix,
      frontier.Completes assignXMoveXTerm :=
  parserFrontier_complete_of_codeCompletes
    xPrefix_codeCompletes_as_assignment

theorem parserFrontier_has_amp_borrow_ambiguity :
    (∃ frontier : ParsedTermFrontier ampPrefix,
      frontier.Completes borrowSharedXTerm) ∧
    (∃ frontier : ParsedTermFrontier ampPrefix,
      frontier.Completes borrowMutXTerm) :=
  parserFrontier_same_prefix_for_completions
    ampPrefix_codeCompletes_as_shared_borrow
    ampPrefix_codeCompletes_as_mut_borrow

end FwRust
end GrammarFrontier
end ConservativeExtractor
