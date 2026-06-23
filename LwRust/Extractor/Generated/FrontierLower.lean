import LwRust.Extractor.FrontierSemantics

/-!
Generated lowering hooks from checked FW parser frontiers to the
existing generated partial-program frontiers.

This file is generated from the syntax declarations and checked
`SyntaxCtor` annotations in `LwRust.Extractor.CompleteProgram`.
Re-generate it with `scripts/generate_frontier_lower_from_syntax.py`.
-/

namespace ConservativeExtractor
namespace GrammarFrontier
namespace FwRust
namespace GeneratedFrontierLower

inductive CheckedLValsFrontierLower :
    CheckableGrammar.CheckedFrontierState checkableGrammar .clvals →
    PartialLVals → Prop where
  | fallback
      {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clvals} :
      CheckedLValsFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | clvalsEmpty_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsEmptyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedLValsFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalsEmptyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVals.done [])

  | clvalsCons_start_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedLValsFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalsConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsCons_head_boundary
      {headTree : Tree Tok}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 1 } : Item Cat Terminal).before [headTree] = Bool.true} :
      CheckedLValsFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalsConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) [headTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsCons_done_boundary
      {headTree tailTree : Tree Tok}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 2 } : Item Cat Terminal).before [headTree, tailTree] = Bool.true} :
      CheckedLValsFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalsConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) [headTree, tailTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsCons_head_descend
      {headState : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedLValsFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := clvalsConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) .clval [.cat .clvalsTail] (by native_decide) [] checkedBefore headState)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsCons_tail_descend
      {headTree : Tree Tok}
      {tailState : CheckableGrammar.CheckedFrontierState checkableGrammar .clvalsTail}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 1 } : Item Cat Terminal).before [headTree] = Bool.true} :
      CheckedLValsFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := clvalsConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clvalsTail [] (by native_decide) [headTree] checkedBefore tailState)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

inductive CheckedLValsTailFrontierLower :
    CheckableGrammar.CheckedFrontierState checkableGrammar .clvalsTail →
    PartialLVals → Prop where
  | fallback
      {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clvalsTail} :
      CheckedLValsTailFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | clvalsTailEmpty_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailEmptyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedLValsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalsTailEmptyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVals.done [])

  | clvalsTailCons_start_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedLValsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalsTailConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_comma_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 1 } : Item Cat Terminal).before [.token .comma] = Bool.true} :
      CheckedLValsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalsTailConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .comma] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_head_boundary
      {headTree : Tree Tok}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 2 } : Item Cat Terminal).before [.token .comma, headTree] = Bool.true} :
      CheckedLValsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalsTailConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .comma, headTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_done_boundary
      {headTree tailTree : Tree Tok}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 3 } : Item Cat Terminal).before [.token .comma, headTree, tailTree] = Bool.true} :
      CheckedLValsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalsTailConsRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .comma, headTree, tailTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_head_descend
      {headState : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 1 } : Item Cat Terminal).before [.token .comma] = Bool.true} :
      CheckedLValsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := clvalsTailConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [.cat .clvalsTail] (by native_decide) [.token .comma] checkedBefore headState)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_tail_descend
      {headTree : Tree Tok}
      {tailState : CheckableGrammar.CheckedFrontierState checkableGrammar .clvalsTail}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 2 } : Item Cat Terminal).before [.token .comma, headTree] = Bool.true} :
      CheckedLValsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := clvalsTailConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) .clvalsTail [] (by native_decide) [.token .comma, headTree] checkedBefore tailState)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

inductive CheckedTermsFrontierLower :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterms →
    PartialTerms → Prop where
  | fallback
      {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterms} :
      CheckedTermsFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialTerms.cutoff)

  | ctermsEmpty_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsEmptyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermsFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermsEmptyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerms.done [])

  | ctermsCons_start_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermsFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermsConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsCons_head_boundary
      {headTree : Tree Tok}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 1 } : Item Cat Terminal).before [headTree] = Bool.true} :
      CheckedTermsFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermsConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) [headTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsCons_done_boundary
      {headTree tailTree : Tree Tok}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 2 } : Item Cat Terminal).before [headTree, tailTree] = Bool.true} :
      CheckedTermsFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermsConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) [headTree, tailTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsCons_head_descend
      {headState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermsFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermsConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) .cterm [.cat .ctermsTail] (by native_decide) [] checkedBefore headState)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsCons_tail_descend
      {headTree : Tree Tok}
      {tailState : CheckableGrammar.CheckedFrontierState checkableGrammar .ctermsTail}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 1 } : Item Cat Terminal).before [headTree] = Bool.true} :
      CheckedTermsFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermsConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) .ctermsTail [] (by native_decide) [headTree] checkedBefore tailState)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

inductive CheckedTermsTailFrontierLower :
    CheckableGrammar.CheckedFrontierState checkableGrammar .ctermsTail →
    PartialTerms → Prop where
  | fallback
      {state : CheckableGrammar.CheckedFrontierState checkableGrammar .ctermsTail} :
      CheckedTermsTailFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialTerms.cutoff)

  | ctermsTailEmpty_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailEmptyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermsTailEmptyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerms.done [])

  | ctermsTailCons_start_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermsTailConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_comma_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 1 } : Item Cat Terminal).before [.token .comma] = Bool.true} :
      CheckedTermsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermsTailConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .comma] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_head_boundary
      {headTree : Tree Tok}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 2 } : Item Cat Terminal).before [.token .comma, headTree] = Bool.true} :
      CheckedTermsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermsTailConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .comma, headTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_done_boundary
      {headTree tailTree : Tree Tok}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 3 } : Item Cat Terminal).before [.token .comma, headTree, tailTree] = Bool.true} :
      CheckedTermsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermsTailConsRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .comma, headTree, tailTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_head_descend
      {headState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 1 } : Item Cat Terminal).before [.token .comma] = Bool.true} :
      CheckedTermsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermsTailConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) .cterm [.cat .ctermsTail] (by native_decide) [.token .comma] checkedBefore headState)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_tail_descend
      {headTree : Tree Tok}
      {tailState : CheckableGrammar.CheckedFrontierState checkableGrammar .ctermsTail}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 2 } : Item Cat Terminal).before [.token .comma, headTree] = Bool.true} :
      CheckedTermsTailFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermsTailConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) .ctermsTail [] (by native_decide) [.token .comma, headTree] checkedBefore tailState)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

inductive CheckedTyFrontierLower :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cty →
    PartialTy → Prop where
  | fallback
      {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cty} :
      CheckedTyFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyUnit_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyUnitRule, dot := 1 } : Item Cat Terminal).before [.token .ctyUnit] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyUnitRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ctyUnit] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxCtor.ctyUnit_ctor))

  | ctyInt_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyIntRule, dot := 1 } : Item Cat Terminal).before [.token .ctyInt] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyIntRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ctyInt] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxCtor.ctyInt_ctor))

  | ctyBool_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoolRule, dot := 1 } : Item Cat Terminal).before [.token .ctyBool] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBoolRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ctyBool] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxCtor.ctyBool_ctor))

  | ctyUnit_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyUnitRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyUnitRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyInt_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyIntRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyIntRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyBool_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoolRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBoolRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyBorrowShared_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | ctyBorrowShared_dot2_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 2 } : Item Cat Terminal).before [.token .amp, .token .lbrack] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .lbrack] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | ctyBorrowShared_dot4_boundary
      {targetsTree : Tree Tok} {targets : List LVal}
      (targets_denotes : denoteLVals? targetsTree = some targets)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 4 } : Item Cat Terminal).before [.token .amp, .token .lbrack, targetsTree, .token .rbrack] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .lbrack, targetsTree, .token .rbrack] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))

  | ctyBorrowMut_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | ctyBorrowMut_dot2_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 2 } : Item Cat Terminal).before [.token .ampMut, .token .lbrack] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .ampMut, .token .lbrack] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | ctyBorrowMut_dot4_boundary
      {targetsTree : Tree Tok} {targets : List LVal}
      (targets_denotes : denoteLVals? targetsTree = some targets)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 4 } : Item Cat Terminal).before [.token .ampMut, .token .lbrack, targetsTree, .token .rbrack] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .ampMut, .token .lbrack, targetsTree, .token .rbrack] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))

  | ctyBox_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoxRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBoxRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.boxElement _root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyBorrowShared_borrowSharedTargets_boundary
      {targetsTree : Tree Tok} {targets : List LVal}
      (targets_denotes : denoteLVals? targetsTree = some targets)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 3 } : Item Cat Terminal).before [.token .amp, .token .lbrack, targetsTree] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .lbrack, targetsTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))

  | ctyBorrowMut_borrowMutTargets_boundary
      {targetsTree : Tree Tok} {targets : List LVal}
      (targets_denotes : denoteLVals? targetsTree = some targets)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 3 } : Item Cat Terminal).before [.token .ampMut, .token .lbrack, targetsTree] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .ampMut, .token .lbrack, targetsTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))

  | ctyBox_boxElement_boundary
      {elementTree : Tree Tok} {element : Ty}
      (element_denotes : denoteTy? elementTree = some element)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoxRule, dot := 2 } : Item Cat Terminal).before [.token .box, elementTree] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBoxRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .box, elementTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.boxElement (_root_.ConservativeExtractor.Generated.PartialTy.done element))

  | ctyBorrowShared_tokenAmpStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 1 } : Item Cat Terminal).before [.token .amp] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .amp] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.tokenAmpStart)

  | ctyBorrowMut_tokenAmpStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 1 } : Item Cat Terminal).before [.token .ampMut] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ampMut] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.tokenAmpStart)

  | ctyBorrowMut_borrowMutStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 1 } : Item Cat Terminal).before [.token .ampMut] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ampMut] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutStart)

  | ctyBox_boxStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoxRule, dot := 1 } : Item Cat Terminal).before [.token .box] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctyBoxRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .box] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.boxStart)

  | ctyBorrowShared_borrowSharedTargets_descend
      {targetsState : CheckableGrammar.CheckedFrontierState checkableGrammar .clvals}
      {targets : PartialLVals}
      (targets_lower : CheckedLValsFrontierLower targetsState targets)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 2 } : Item Cat Terminal).before [.token .amp, .token .lbrack] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctyBorrowSharedRule, dot := 2 } : Item Cat Terminal) (by native_decide) .clvals [.token .rbrack] (by native_decide) [.token .amp, .token .lbrack] checkedBefore targetsState)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets targets)

  | ctyBorrowMut_borrowMutTargets_descend
      {targetsState : CheckableGrammar.CheckedFrontierState checkableGrammar .clvals}
      {targets : PartialLVals}
      (targets_lower : CheckedLValsFrontierLower targetsState targets)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 2 } : Item Cat Terminal).before [.token .ampMut, .token .lbrack] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctyBorrowMutRule, dot := 2 } : Item Cat Terminal) (by native_decide) .clvals [.token .rbrack] (by native_decide) [.token .ampMut, .token .lbrack] checkedBefore targetsState)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets targets)

  | ctyBox_boxElement_descend
      {elementState : CheckableGrammar.CheckedFrontierState checkableGrammar .cty}
      {element : PartialTy}
      (element_lower : CheckedTyFrontierLower elementState element)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoxRule, dot := 1 } : Item Cat Terminal).before [.token .box] = Bool.true} :
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctyBoxRule, dot := 1 } : Item Cat Terminal) (by native_decide) .cty [] (by native_decide) [.token .box] checkedBefore elementState)
        (_root_.ConservativeExtractor.Generated.PartialTy.boxElement element)

inductive CheckedLValFrontierLower :
    CheckableGrammar.CheckedFrontierState checkableGrammar .clval →
    PartialLVal → Prop where
  | fallback
      {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clval} :
      CheckedLValFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | clvalVar_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalVarRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedLValFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalVarRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVal.varX _root_.ConservativeExtractor.Generated.PartialName.cutoff)

  | clvalDeref_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalDerefRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedLValFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalDerefRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | clvalVar_varX_boundary
      {x : Name}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalVarRule, dot := 1 } : Item Cat Terminal).before [.token (.ident x)] = Bool.true} :
      CheckedLValFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalVarRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token (.ident x)] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVal.varX (_root_.ConservativeExtractor.Generated.PartialName.done x))

  | clvalDeref_derefOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalDerefRule, dot := 2 } : Item Cat Terminal).before [.token .star, operandTree] = Bool.true} :
      CheckedLValFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalDerefRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .star, operandTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | clvalDeref_derefStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalDerefRule, dot := 1 } : Item Cat Terminal).before [.token .star] = Bool.true} :
      CheckedLValFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := clvalDerefRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .star] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialLVal.derefStart)

  | clvalDeref_derefOperand_descend
      {operandState : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : CheckedLValFrontierLower operandState operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalDerefRule, dot := 1 } : Item Cat Terminal).before [.token .star] = Bool.true} :
      CheckedLValFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := clvalDerefRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [.token .star] checkedBefore operandState)
        (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand operand)

inductive CheckedTermFrontierLower :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm →
    PartialTerm → Prop where
  | fallback
      {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm} :
      CheckedTermFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermUnit_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermUnitRule, dot := 1 } : Item Cat Terminal).before [.token .unit] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermUnitRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .unit] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxCtor.ctermUnit_ctor))

  | ctermTrue_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermTrueRule, dot := 1 } : Item Cat Terminal).before [.token .trueLit] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermTrueRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .trueLit] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxCtor.ctermTrue_ctor))

  | ctermFalse_done_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermFalseRule, dot := 1 } : Item Cat Terminal).before [.token .falseLit] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermFalseRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .falseLit] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxCtor.ctermFalse_ctor))

  | ctermUnit_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermUnitRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermUnitRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermInt_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIntRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermIntRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermTrue_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermTrueRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermTrueRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermFalse_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermFalseRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermFalseRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermBlock_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBlockRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockStart)

  | ctermBlock_dot2_boundary
      {lifetime : Lifetime}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 2 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime)] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBlockRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .block, .token (.lifetime lifetime)] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime _root_.ConservativeExtractor.Generated.PartialTerms.cutoff)

  | ctermBlock_dot3_boundary
      {lifetime : Lifetime}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 3 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime), .token .lbrace] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBlockRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .block, .token (.lifetime lifetime), .token .lbrace] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime _root_.ConservativeExtractor.Generated.PartialTerms.cutoff)

  | ctermBlock_dot5_boundary
      {lifetime : Lifetime}
      {termsTree : Tree Tok} {terms : List Term}
      (terms_denotes : denoteTerms? termsTree = some terms)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 5 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime), .token .lbrace, termsTree, .token .rbrace] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBlockRule, dot := 5 } : Item Cat Terminal) (by native_decide) [.token .block, .token (.lifetime lifetime), .token .lbrace, termsTree, .token .rbrace] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime (_root_.ConservativeExtractor.Generated.PartialTerms.done terms))

  | ctermLetMut_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermLetMutRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName _root_.ConservativeExtractor.Generated.PartialName.cutoff)

  | ctermLetMut_dot2_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 2 } : Item Cat Terminal).before [.token .letKw, .token .mutKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermLetMutRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .letKw, .token .mutKw] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName _root_.ConservativeExtractor.Generated.PartialName.cutoff)

  | ctermLetMut_dot4_boundary
      {name : Name}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 4 } : Item Cat Terminal).before [.token .letKw, .token .mutKw, .token (.ident name), .token .assign] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermLetMutRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .letKw, .token .mutKw, .token (.ident name), .token .assign] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermAssign_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermAssignRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermAssign_dot2_boundary
      {lhsTree : Tree Tok} {lhs : LVal}
      (lhs_denotes : denoteLVal? lhsTree = some lhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 2 } : Item Cat Terminal).before [lhsTree, .token .assign] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermAssignRule, dot := 2 } : Item Cat Terminal) (by native_decide) [lhsTree, .token .assign] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermBox_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBoxRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBoxRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermBorrowShared_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowSharedRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBorrowSharedRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermBorrowMut_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBorrowMutRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermMove_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermMoveRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermMoveRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermCopy_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermCopyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermCopyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermEq_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermEqRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermEq_dot2_boundary
      {lhsTree : Tree Tok} {lhs : Term}
      (lhs_denotes : denoteTerm? lhsTree = some lhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 2 } : Item Cat Terminal).before [lhsTree, .token .eqEq] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermEqRule, dot := 2 } : Item Cat Terminal) (by native_decide) [lhsTree, .token .eqEq] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermIte_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermIteRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermIte_dot4_boundary
      {conditionTree : Tree Tok} {condition : Term}
      {trueBranchTree : Tree Tok} {trueBranch : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (trueBranch_denotes : denoteTerm? trueBranchTree = some trueBranch)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 4 } : Item Cat Terminal).before [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermIteRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermWhile_dot0_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermWhileRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileStart)

  | ctermWhile_dot2_boundary
      {bodyLifetime : Lifetime}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 2 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime)] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermWhileRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime)] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermInt_intN_boundary
      {n : Int}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIntRule, dot := 1 } : Item Cat Terminal).before [.token (.num n)] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermIntRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token (.num n)] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.intN n)

  | ctermBlock_blockTerms_boundary
      {lifetime : Lifetime}
      {termsTree : Tree Tok} {terms : List Term}
      (terms_denotes : denoteTerms? termsTree = some terms)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 4 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime), .token .lbrace, termsTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBlockRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .block, .token (.lifetime lifetime), .token .lbrace, termsTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime (_root_.ConservativeExtractor.Generated.PartialTerms.done terms))

  | ctermLetMut_letMutName_boundary
      {name : Name}
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 3 } : Item Cat Terminal).before [.token .letKw, .token .mutKw, .token (.ident name)] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermLetMutRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .letKw, .token .mutKw, .token (.ident name)] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName (_root_.ConservativeExtractor.Generated.PartialName.done name))

  | ctermLetMut_letMutInitialiser_boundary
      {name : Name}
      {initialiserTree : Tree Tok} {initialiser : Term}
      (initialiser_denotes : denoteTerm? initialiserTree = some initialiser)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 5 } : Item Cat Terminal).before [.token .letKw, .token .mutKw, .token (.ident name), .token .assign, initialiserTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermLetMutRule, dot := 5 } : Item Cat Terminal) (by native_decide) [.token .letKw, .token .mutKw, .token (.ident name), .token .assign, initialiserTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name (_root_.ConservativeExtractor.Generated.PartialTerm.done initialiser))

  | ctermAssign_assignLhs_boundary
      {lhsTree : Tree Tok} {lhs : LVal}
      (lhs_denotes : denoteLVal? lhsTree = some lhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 1 } : Item Cat Terminal).before [lhsTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermAssignRule, dot := 1 } : Item Cat Terminal) (by native_decide) [lhsTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs (_root_.ConservativeExtractor.Generated.PartialLVal.done lhs))

  | ctermAssign_assignRhs_boundary
      {lhsTree : Tree Tok} {lhs : LVal}
      {rhsTree : Tree Tok} {rhs : Term}
      (lhs_denotes : denoteLVal? lhsTree = some lhs)
      (rhs_denotes : denoteTerm? rhsTree = some rhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 3 } : Item Cat Terminal).before [lhsTree, .token .assign, rhsTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermAssignRule, dot := 3 } : Item Cat Terminal) (by native_decide) [lhsTree, .token .assign, rhsTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs (_root_.ConservativeExtractor.Generated.PartialTerm.done rhs))

  | ctermBox_boxOperand_boundary
      {operandTree : Tree Tok} {operand : Term}
      (operand_denotes : denoteTerm? operandTree = some operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBoxRule, dot := 2 } : Item Cat Terminal).before [.token .box, operandTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBoxRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .box, operandTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand (_root_.ConservativeExtractor.Generated.PartialTerm.done operand))

  | ctermBorrowShared_borrowSharedOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowSharedRule, dot := 2 } : Item Cat Terminal).before [.token .amp, operandTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBorrowSharedRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .amp, operandTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | ctermBorrowMut_borrowMutOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 2 } : Item Cat Terminal).before [.token .ampMut, operandTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBorrowMutRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .ampMut, operandTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | ctermMove_moveOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermMoveRule, dot := 2 } : Item Cat Terminal).before [.token .moveKw, operandTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermMoveRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .moveKw, operandTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | ctermCopy_copyOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermCopyRule, dot := 2 } : Item Cat Terminal).before [.token .copyKw, operandTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermCopyRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .copyKw, operandTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | ctermEq_termPrefix_boundary
      {lhsTree : Tree Tok} {lhs : Term}
      (lhs_denotes : denoteTerm? lhsTree = some lhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 1 } : Item Cat Terminal).before [lhsTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermEqRule, dot := 1 } : Item Cat Terminal) (by native_decide) [lhsTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix (_root_.ConservativeExtractor.Generated.PartialTerm.done lhs))

  | ctermEq_eqRhs_boundary
      {lhsTree : Tree Tok} {lhs : Term}
      {rhsTree : Tree Tok} {rhs : Term}
      (lhs_denotes : denoteTerm? lhsTree = some lhs)
      (rhs_denotes : denoteTerm? rhsTree = some rhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 3 } : Item Cat Terminal).before [lhsTree, .token .eqEq, rhsTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermEqRule, dot := 3 } : Item Cat Terminal) (by native_decide) [lhsTree, .token .eqEq, rhsTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs (_root_.ConservativeExtractor.Generated.PartialTerm.done rhs))

  | ctermIte_iteCondition_boundary
      {conditionTree : Tree Tok} {condition : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 2 } : Item Cat Terminal).before [.token .ifKw, conditionTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermIteRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .ifKw, conditionTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition (_root_.ConservativeExtractor.Generated.PartialTerm.done condition))

  | ctermIte_iteTrueBranch_boundary
      {conditionTree : Tree Tok} {condition : Term}
      {trueBranchTree : Tree Tok} {trueBranch : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (trueBranch_denotes : denoteTerm? trueBranchTree = some trueBranch)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 3 } : Item Cat Terminal).before [.token .ifKw, conditionTree, trueBranchTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermIteRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .ifKw, conditionTree, trueBranchTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteTrueBranch condition (_root_.ConservativeExtractor.Generated.PartialTerm.done trueBranch))

  | ctermIte_iteFalseBranch_boundary
      {conditionTree : Tree Tok} {condition : Term}
      {trueBranchTree : Tree Tok} {trueBranch : Term}
      {falseBranchTree : Tree Tok} {falseBranch : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (trueBranch_denotes : denoteTerm? trueBranchTree = some trueBranch)
      (falseBranch_denotes : denoteTerm? falseBranchTree = some falseBranch)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 5 } : Item Cat Terminal).before [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw, falseBranchTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermIteRule, dot := 5 } : Item Cat Terminal) (by native_decide) [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw, falseBranchTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch (_root_.ConservativeExtractor.Generated.PartialTerm.done falseBranch))

  | ctermWhile_whileCondition_boundary
      {bodyLifetime : Lifetime}
      {conditionTree : Tree Tok} {condition : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 3 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermWhileRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime (_root_.ConservativeExtractor.Generated.PartialTerm.done condition))

  | ctermWhile_whileBody_boundary
      {bodyLifetime : Lifetime}
      {conditionTree : Tree Tok} {condition : Term}
      {bodyTree : Tree Tok} {body : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (body_denotes : denoteTerm? bodyTree = some body)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 4 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree, bodyTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermWhileRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree, bodyTree] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileBody bodyLifetime condition (_root_.ConservativeExtractor.Generated.PartialTerm.done body))

  | ctermBlock_blockStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 1 } : Item Cat Terminal).before [.token .block] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBlockRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .block] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockStart)

  | ctermLetMut_letMutStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 1 } : Item Cat Terminal).before [.token .letKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermLetMutRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .letKw] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutStart)

  | ctermBox_boxStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal).before [.token .box] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .box] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.boxStart)

  | ctermBorrowShared_tokenAmpStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowSharedRule, dot := 1 } : Item Cat Terminal).before [.token .amp] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBorrowSharedRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .amp] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.tokenAmpStart)

  | ctermBorrowMut_tokenAmpStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 1 } : Item Cat Terminal).before [.token .ampMut] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBorrowMutRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ampMut] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.tokenAmpStart)

  | ctermBorrowMut_borrowMutStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 1 } : Item Cat Terminal).before [.token .ampMut] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermBorrowMutRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ampMut] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutStart)

  | ctermMove_moveStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermMoveRule, dot := 1 } : Item Cat Terminal).before [.token .moveKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermMoveRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .moveKw] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.moveStart)

  | ctermCopy_copyStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermCopyRule, dot := 1 } : Item Cat Terminal).before [.token .copyKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermCopyRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .copyKw] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.copyStart)

  | ctermIte_iteStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 1 } : Item Cat Terminal).before [.token .ifKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermIteRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ifKw] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteStart)

  | ctermWhile_whileStart_boundary
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 1 } : Item Cat Terminal).before [.token .whileKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary ({ rule := ctermWhileRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .whileKw] checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileStart)

  | ctermBlock_blockTerms_descend
      {lifetime : Lifetime}
      {termsState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterms}
      {terms : PartialTerms}
      (terms_lower : CheckedTermsFrontierLower termsState terms)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 3 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime), .token .lbrace] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermBlockRule, dot := 3 } : Item Cat Terminal) (by native_decide) .cterms [.token .rbrace] (by native_decide) [.token .block, .token (.lifetime lifetime), .token .lbrace] checkedBefore termsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime terms)

  | ctermLetMut_letMutInitialiser_descend
      {name : Name}
      {initialiserState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {initialiser : PartialTerm}
      (initialiser_lower : CheckedTermFrontierLower initialiserState initialiser)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 4 } : Item Cat Terminal).before [.token .letKw, .token .mutKw, .token (.ident name), .token .assign] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermLetMutRule, dot := 4 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [.token .letKw, .token .mutKw, .token (.ident name), .token .assign] checkedBefore initialiserState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name initialiser)

  | ctermAssign_assignLhs_descend
      {lhsState : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
      {lhs : PartialLVal}
      (lhs_lower : CheckedLValFrontierLower lhsState lhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermAssignRule, dot := 0 } : Item Cat Terminal) (by native_decide) .clval [.token .assign, .cat .cterm] (by native_decide) [] checkedBefore lhsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs lhs)

  | ctermAssign_assignRhs_descend
      {lhsTree : Tree Tok} {lhs : LVal}
      (lhs_denotes : denoteLVal? lhsTree = some lhs)
      {rhsState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {rhs : PartialTerm}
      (rhs_lower : CheckedTermFrontierLower rhsState rhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 2 } : Item Cat Terminal).before [lhsTree, .token .assign] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermAssignRule, dot := 2 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [lhsTree, .token .assign] checkedBefore rhsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs rhs)

  | ctermBox_boxOperand_descend
      {operandState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {operand : PartialTerm}
      (operand_lower : CheckedTermFrontierLower operandState operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal).before [.token .box] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [.token .box] checkedBefore operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand operand)

  | ctermBorrowShared_borrowSharedOperand_descend
      {operandState : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : CheckedLValFrontierLower operandState operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowSharedRule, dot := 1 } : Item Cat Terminal).before [.token .amp] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermBorrowSharedRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [.token .amp] checkedBefore operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand operand)

  | ctermBorrowMut_borrowMutOperand_descend
      {operandState : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : CheckedLValFrontierLower operandState operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 1 } : Item Cat Terminal).before [.token .ampMut] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermBorrowMutRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [.token .ampMut] checkedBefore operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand operand)

  | ctermMove_moveOperand_descend
      {operandState : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : CheckedLValFrontierLower operandState operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermMoveRule, dot := 1 } : Item Cat Terminal).before [.token .moveKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermMoveRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [.token .moveKw] checkedBefore operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand operand)

  | ctermCopy_copyOperand_descend
      {operandState : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : CheckedLValFrontierLower operandState operand)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermCopyRule, dot := 1 } : Item Cat Terminal).before [.token .copyKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermCopyRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [.token .copyKw] checkedBefore operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand operand)

  | ctermEq_termPrefix_descend
      {lhsState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {lhs : PartialTerm}
      (lhs_lower : CheckedTermFrontierLower lhsState lhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermEqRule, dot := 0 } : Item Cat Terminal) (by native_decide) .cterm [.token .eqEq, .cat .cterm] (by native_decide) [] checkedBefore lhsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix lhs)

  | ctermEq_eqRhs_descend
      {lhsTree : Tree Tok} {lhs : Term}
      (lhs_denotes : denoteTerm? lhsTree = some lhs)
      {rhsState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {rhs : PartialTerm}
      (rhs_lower : CheckedTermFrontierLower rhsState rhs)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 2 } : Item Cat Terminal).before [lhsTree, .token .eqEq] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermEqRule, dot := 2 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [lhsTree, .token .eqEq] checkedBefore rhsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs rhs)

  | ctermIte_iteCondition_descend
      {conditionState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {condition : PartialTerm}
      (condition_lower : CheckedTermFrontierLower conditionState condition)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 1 } : Item Cat Terminal).before [.token .ifKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermIteRule, dot := 1 } : Item Cat Terminal) (by native_decide) .cterm [.cat .cterm, .token .elseKw, .cat .cterm] (by native_decide) [.token .ifKw] checkedBefore conditionState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition condition)

  | ctermIte_iteTrueBranch_descend
      {conditionTree : Tree Tok} {condition : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      {trueBranchState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {trueBranch : PartialTerm}
      (trueBranch_lower : CheckedTermFrontierLower trueBranchState trueBranch)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 2 } : Item Cat Terminal).before [.token .ifKw, conditionTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermIteRule, dot := 2 } : Item Cat Terminal) (by native_decide) .cterm [.token .elseKw, .cat .cterm] (by native_decide) [.token .ifKw, conditionTree] checkedBefore trueBranchState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteTrueBranch condition trueBranch)

  | ctermIte_iteFalseBranch_descend
      {conditionTree : Tree Tok} {condition : Term}
      {trueBranchTree : Tree Tok} {trueBranch : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (trueBranch_denotes : denoteTerm? trueBranchTree = some trueBranch)
      {falseBranchState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {falseBranch : PartialTerm}
      (falseBranch_lower : CheckedTermFrontierLower falseBranchState falseBranch)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 4 } : Item Cat Terminal).before [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermIteRule, dot := 4 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw] checkedBefore falseBranchState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch falseBranch)

  | ctermWhile_whileCondition_descend
      {bodyLifetime : Lifetime}
      {conditionState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {condition : PartialTerm}
      (condition_lower : CheckedTermFrontierLower conditionState condition)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 2 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime)] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermWhileRule, dot := 2 } : Item Cat Terminal) (by native_decide) .cterm [.cat .cterm] (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime)] checkedBefore conditionState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime condition)

  | ctermWhile_whileBody_descend
      {bodyLifetime : Lifetime}
      {conditionTree : Tree Tok} {condition : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      {bodyState : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
      {body : PartialTerm}
      (body_lower : CheckedTermFrontierLower bodyState body)
      {checkedBefore : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 3 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree] = Bool.true} :
      CheckedTermFrontierLower
        (CheckableGrammar.CheckedFrontierState.descend ({ rule := ctermWhileRule, dot := 3 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree] checkedBefore bodyState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileBody bodyLifetime condition body)


set_option linter.unusedSimpArgs false in
theorem checkedLValsFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clvals}
    {frontier : PartialLVals} {completed : List LVal}
    (hlower : CheckedLValsFrontierLower state frontier)
    (hdenotes :
      denoteLVals? (state.rawCompletion defaults).tree = some completed) :
    CompletesLVals frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | clvalsEmpty_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalsEmptyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | clvalsCons_start_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsCons_head_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsCons_done_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsCons_head_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsCons_tail_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone

set_option linter.unusedSimpArgs false in
theorem checkedLValsTailFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clvalsTail}
    {frontier : PartialLVals} {completed : List LVal}
    (hlower : CheckedLValsTailFrontierLower state frontier)
    (hdenotes :
      denoteLValsTail? (state.rawCompletion defaults).tree = some completed) :
    CompletesLVals frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | clvalsTailEmpty_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalsTailEmptyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | clvalsTailCons_start_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_comma_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_head_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_done_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_head_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_tail_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone

set_option linter.unusedSimpArgs false in
theorem checkedTermsFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterms}
    {frontier : PartialTerms} {completed : List Term}
    (hlower : CheckedTermsFrontierLower state frontier)
    (hdenotes :
      denoteTerms? (state.rawCompletion defaults).tree = some completed) :
    CompletesTerms frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermsEmpty_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermsEmptyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermsCons_start_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsCons_head_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsCons_done_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsCons_head_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsCons_tail_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone

set_option linter.unusedSimpArgs false in
theorem checkedTermsTailFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .ctermsTail}
    {frontier : PartialTerms} {completed : List Term}
    (hlower : CheckedTermsTailFrontierLower state frontier)
    (hdenotes :
      denoteTermsTail? (state.rawCompletion defaults).tree = some completed) :
    CompletesTerms frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermsTailEmpty_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermsTailEmptyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermsTailCons_start_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_comma_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_head_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_done_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_head_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_tail_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone

set_option linter.unusedSimpArgs false in
theorem checkedLValsFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clvals}
    {frontier : PartialLVals} {tree : Tree Tok} {completed : List LVal}
    (hlower : CheckedLValsFrontierLower state frontier)
    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesLVals tree completed) :
    CompletesLVals frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | clvalsEmpty_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalsEmpty =>
          exact _root_.ConservativeExtractor.Generated.CompletesLVals.done
      | clvalsCons hhead htail =>
          simp [clvalsEmptyRule] at htree
  | clvalsCons_start_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsCons_head_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsCons_done_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsCons_head_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsCons_tail_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone

set_option linter.unusedSimpArgs false in
theorem checkedLValsTailFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clvalsTail}
    {frontier : PartialLVals} {tree : Tree Tok} {completed : List LVal}
    (hlower : CheckedLValsTailFrontierLower state frontier)
    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesLValsTail tree completed) :
    CompletesLVals frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | clvalsTailEmpty_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalsTailEmpty =>
          exact _root_.ConservativeExtractor.Generated.CompletesLVals.done
      | clvalsTailCons hhead htail =>
          simp [clvalsTailEmptyRule] at htree
  | clvalsTailCons_start_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_comma_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_head_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_done_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_head_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone
  | clvalsTailCons_tail_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.elemsDone

set_option linter.unusedSimpArgs false in
theorem checkedTermsFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterms}
    {frontier : PartialTerms} {tree : Tree Tok} {completed : List Term}
    (hlower : CheckedTermsFrontierLower state frontier)
    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesTerms tree completed) :
    CompletesTerms frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermsEmpty_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | ctermsEmpty =>
          exact _root_.ConservativeExtractor.Generated.CompletesTerms.done
      | ctermsCons hhead htail =>
          simp [ctermsEmptyRule] at htree
  | ctermsCons_start_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsCons_head_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsCons_done_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsCons_head_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsCons_tail_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone

set_option linter.unusedSimpArgs false in
theorem checkedTermsTailFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .ctermsTail}
    {frontier : PartialTerms} {tree : Tree Tok} {completed : List Term}
    (hlower : CheckedTermsTailFrontierLower state frontier)
    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesTermsTail tree completed) :
    CompletesTerms frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermsTailEmpty_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | ctermsTailEmpty =>
          exact _root_.ConservativeExtractor.Generated.CompletesTerms.done
      | ctermsTailCons hhead htail =>
          simp [ctermsTailEmptyRule] at htree
  | ctermsTailCons_start_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_comma_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_head_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_done_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_head_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone
  | ctermsTailCons_tail_descend =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.elemsDone

set_option linter.unusedSimpArgs false in
theorem checkedTyFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cty}
    {frontier : PartialTy} {completed : Ty}
    (hlower : CheckedTyFrontierLower state frontier)
    (hdenotes :
      denoteTy? (state.rawCompletion defaults).tree = some completed) :
    CompletesTy frontier completed := by
  induction hlower generalizing completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyUnit_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyUnitRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyInt_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyIntRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyBool_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoolRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyUnit_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyUnitRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyInt_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyIntRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBool_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoolRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBorrowShared_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowShared_dot2_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowShared_dot4_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBorrowMut_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot2_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot4_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBox_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBorrowShared_borrowSharedTargets_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBorrowMut_borrowMutTargets_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBox_boxElement_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyBorrowShared_tokenAmpStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_tokenAmpStart
  | ctyBorrowMut_tokenAmpStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_tokenAmpStart
  | ctyBorrowMut_borrowMutStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutStart
  | ctyBox_boxStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxStart
  | ctyBorrowShared_borrowSharedTargets_descend targets_lower =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨targetsCompleted, targets_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets (checkedLValsFrontierLower_completes_of_rawDenotes targets_lower targets_denotes)
  | ctyBorrowMut_borrowMutTargets_descend targets_lower =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨targetsCompleted, targets_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets (checkedLValsFrontierLower_completes_of_rawDenotes targets_lower targets_denotes)
  | ctyBox_boxElement_descend element_lower element_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨elementCompleted, element_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement (element_ih element_denotes)

set_option linter.unusedSimpArgs false in
theorem checkedLValFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
    {frontier : PartialLVal} {completed : LVal}
    (hlower : CheckedLValFrontierLower state frontier)
    (hdenotes :
      denoteLVal? (state.rawCompletion defaults).tree = some completed) :
    CompletesLVal frontier completed := by
  induction hlower generalizing completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | clvalVar_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalVarRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | clvalDeref_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalDerefRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | clvalVar_varX_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalVarRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX _root_.ConservativeExtractor.Generated.CompletesName.done
  | clvalDeref_derefOperand_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalDerefRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | clvalDeref_derefStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalDerefRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefStart
  | clvalDeref_derefOperand_descend operand_lower operand_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalDerefRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand (operand_ih operand_denotes)

set_option linter.unusedSimpArgs false in
theorem checkedTermFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
    {frontier : PartialTerm} {completed : Term}
    (hlower : CheckedTermFrontierLower state frontier)
    (hdenotes :
      denoteTerm? (state.rawCompletion defaults).tree = some completed) :
    CompletesTerm frontier completed := by
  induction hlower generalizing completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermUnit_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermUnitRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermTrue_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermTrueRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermFalse_done_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermFalseRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermUnit_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermUnitRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermInt_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIntRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermTrue_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermTrueRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermFalse_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermFalseRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBlock_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermBlock_dot2_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot3_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot5_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermLetMut_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot2_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot4_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermAssign_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermAssign_dot2_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBox_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBorrowShared_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermBorrowMut_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermMove_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermMoveRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermCopy_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermCopyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermEq_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermEq_dot2_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot4_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermWhile_dot0_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermWhile_dot2_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermInt_intN_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIntRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermInt_intN
  | ctermBlock_blockTerms_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermLetMut_letMutName_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.done
  | ctermLetMut_letMutInitialiser_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermAssign_assignLhs_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermAssign_assignRhs_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBox_boxOperand_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBorrowShared_borrowSharedOperand_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermBorrowMut_borrowMutOperand_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermMove_moveOperand_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermMoveRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermCopy_copyOperand_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermCopyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermEq_termPrefix_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermEq_eqRhs_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteCondition_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteTrueBranch_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteFalseBranch_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermWhile_whileCondition_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermWhile_whileBody_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBlock_blockStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermLetMut_letMutStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutStart
  | ctermBox_boxStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxStart
  | ctermBorrowShared_tokenAmpStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_tokenAmpStart
  | ctermBorrowMut_tokenAmpStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_tokenAmpStart
  | ctermBorrowMut_borrowMutStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutStart
  | ctermMove_moveStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermMoveRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveStart
  | ctermCopy_copyStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermCopyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyStart
  | ctermIte_iteStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteStart
  | ctermWhile_whileStart_boundary =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermBlock_blockTerms_descend terms_lower =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨termsCompleted, terms_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms (checkedTermsFrontierLower_completes_of_rawDenotes terms_lower terms_denotes)
  | ctermLetMut_letMutInitialiser_descend initialiser_lower initialiser_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨initialiserCompleted, initialiser_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser (initialiser_ih initialiser_denotes)
  | ctermAssign_assignLhs_descend lhs_lower =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨lhsCompleted, lhs_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs (checkedLValFrontierLower_completes_of_rawDenotes lhs_lower lhs_denotes)
  | ctermAssign_assignRhs_descend lhs_denotes rhs_lower rhs_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨rhsCompleted, rhs_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs (rhs_ih rhs_denotes)
  | ctermBox_boxOperand_descend operand_lower operand_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand (operand_ih operand_denotes)
  | ctermBorrowShared_borrowSharedOperand_descend operand_lower =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand (checkedLValFrontierLower_completes_of_rawDenotes operand_lower operand_denotes)
  | ctermBorrowMut_borrowMutOperand_descend operand_lower =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand (checkedLValFrontierLower_completes_of_rawDenotes operand_lower operand_denotes)
  | ctermMove_moveOperand_descend operand_lower =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermMoveRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand (checkedLValFrontierLower_completes_of_rawDenotes operand_lower operand_denotes)
  | ctermCopy_copyOperand_descend operand_lower =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermCopyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand (checkedLValFrontierLower_completes_of_rawDenotes operand_lower operand_denotes)
  | ctermEq_termPrefix_descend lhs_lower lhs_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨lhsCompleted, lhs_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix (lhs_ih lhs_denotes)
  | ctermEq_eqRhs_descend lhs_denotes rhs_lower rhs_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨rhsCompleted, rhs_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs (rhs_ih rhs_denotes)
  | ctermIte_iteCondition_descend condition_lower condition_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨conditionCompleted, condition_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition (condition_ih condition_denotes)
  | ctermIte_iteTrueBranch_descend condition_denotes trueBranch_lower trueBranch_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨trueBranchCompleted, trueBranch_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch (trueBranch_ih trueBranch_denotes)
  | ctermIte_iteFalseBranch_descend condition_denotes trueBranch_denotes falseBranch_lower falseBranch_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨falseBranchCompleted, falseBranch_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch (falseBranch_ih falseBranch_denotes)
  | ctermWhile_whileCondition_descend condition_lower condition_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨conditionCompleted, condition_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition (condition_ih condition_denotes)
  | ctermWhile_whileBody_descend condition_denotes body_lower body_ih =>
      simp_all [CheckableGrammar.CheckedFrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨bodyCompleted, body_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody (body_ih body_denotes)

set_option linter.unusedSimpArgs false in
theorem checkedTyFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cty}
    {frontier : PartialTy} {tree : Tree Tok} {completed : Ty}
    (hlower : CheckedTyFrontierLower state frontier)
    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesTy tree completed) :
    CompletesTy frontier completed := by
  induction hlower generalizing tree completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyUnit_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyUnitRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyInt_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyIntRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyBool_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBoolRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyUnit_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyInt_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBool_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBorrowShared_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowShared_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowShared_dot4_boundary targets_denotes =>
      rename_i stateTargetsTree stateTargets checkedBefore
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      rename_i actualTargetsTree actualTargets htargets
      rcases htree with ⟨hTreeEq, _⟩
      have hactual : denoteLVals? actualTargetsTree = some actualTargets :=
        denoteLVals?_complete_of_denotes htargets
      rw [hTreeEq] at hactual
      rw [targets_denotes] at hactual
      simp at hactual
      subst actualTargets
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBorrowMut_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot4_boundary targets_denotes =>
      rename_i stateTargetsTree stateTargets checkedBefore
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      rename_i actualTargetsTree actualTargets htargets
      rcases htree with ⟨hTreeEq, _⟩
      have hactual : denoteLVals? actualTargetsTree = some actualTargets :=
        denoteLVals?_complete_of_denotes htargets
      rw [hTreeEq] at hactual
      rw [targets_denotes] at hactual
      simp at hactual
      subst actualTargets
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBox_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement
        _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBorrowShared_borrowSharedTargets_boundary targets_denotes =>
      rename_i stateTargetsTree stateTargets checkedBefore
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      rename_i actualTargetsTree actualTargets htargets
      rcases htree with ⟨hTreeEq, _⟩
      have hactual : denoteLVals? actualTargetsTree = some actualTargets :=
        denoteLVals?_complete_of_denotes htargets
      rw [hTreeEq] at hactual
      rw [targets_denotes] at hactual
      simp at hactual
      subst actualTargets
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBorrowMut_borrowMutTargets_boundary targets_denotes =>
      rename_i stateTargetsTree stateTargets checkedBefore
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      rename_i actualTargetsTree actualTargets htargets
      rcases htree with ⟨hTreeEq, _⟩
      have hactual : denoteLVals? actualTargetsTree = some actualTargets :=
        denoteLVals?_complete_of_denotes htargets
      rw [hTreeEq] at hactual
      rw [targets_denotes] at hactual
      simp at hactual
      subst actualTargets
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBox_boxElement_boundary element_denotes =>
      rename_i stateElementTree stateElement checkedBefore
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBoxRule] at htree
      rename_i actualElementTree actualElement helement
      rcases htree with ⟨hTreeEq, _⟩
      have hactual : denoteTy? actualElementTree = some actualElement :=
        denoteTy?_complete_of_denotes helement
      rw [hTreeEq] at hactual
      rw [element_denotes] at hactual
      simp at hactual
      subst actualElement
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement
        _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyBorrowShared_tokenAmpStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_tokenAmpStart
  | ctyBorrowMut_tokenAmpStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_tokenAmpStart
  | ctyBorrowMut_borrowMutStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutStart
  | ctyBox_boxStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxStart
  | ctyBorrowShared_borrowSharedTargets_descend targets_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      rename_i actualTargetsTree actualTargets htargets
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets
        (checkedLValsFrontierLower_completes_of_stateCompletes
          targets_lower hchild htargets)
  | ctyBorrowMut_borrowMutTargets_descend targets_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      rename_i actualTargetsTree actualTargets htargets
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets
        (checkedLValsFrontierLower_completes_of_stateCompletes
          targets_lower hchild htargets)
  | ctyBox_boxElement_descend element_lower element_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctyBoxRule] at htree
      rename_i actualElementTree actualElement helement
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement
        (element_ih hchild helement)

set_option linter.unusedSimpArgs false in
theorem checkedLValFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}
    {frontier : PartialLVal} {tree : Tree Tok} {completed : LVal}
    (hlower : CheckedLValFrontierLower state frontier)
    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesLVal tree completed) :
    CompletesLVal frontier completed := by
  induction hlower generalizing tree completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | clvalVar_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalVar =>
          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX
            _root_.ConservativeExtractor.Generated.CompletesName.cutoff
      | clvalDeref hoperand =>
          simp [clvalVarRule] at htree
  | clvalDeref_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalVar =>
          simp [clvalDerefRule] at htree
      | clvalDeref hoperand =>
          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand
            _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | clvalVar_varX_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalVar =>
          simp [clvalVarRule] at htree
          rcases htree with ⟨hname, _⟩
          rw [hname]
          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX
            _root_.ConservativeExtractor.Generated.CompletesName.done
      | clvalDeref hoperand =>
          simp [clvalVarRule] at htree
  | clvalDeref_derefOperand_boundary operand_denotes =>
      rename_i stateOperandTree stateOperand checkedBefore
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalVar =>
          simp [clvalDerefRule] at htree
      | clvalDeref hoperand =>
          rename_i actualOperandTree actualOperand
          simp [clvalDerefRule] at htree
          rcases htree with ⟨hTreeEq, _⟩
          have hactual : denoteLVal? actualOperandTree = some actualOperand :=
            denoteLVal?_complete_of_denotes hoperand
          rw [hTreeEq] at hactual
          rw [operand_denotes] at hactual
          simp at hactual
          subst actualOperand
          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand
            _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | clvalDeref_derefStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalVar =>
          simp [clvalDerefRule] at htree
      | clvalDeref hoperand =>
          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefStart
  | clvalDeref_derefOperand_descend operand_lower operand_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes with
      | clvalVar =>
          simp [clvalDerefRule] at htree
      | clvalDeref hoperand =>
          rename_i actualOperandTree actualOperand
          simp [clvalDerefRule] at htree
          rcases htree with ⟨hchildEq, _⟩
          rw [← hchildEq] at hchild
          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand
            (operand_ih hchild hoperand)
private theorem term_eq_of_denote_eq {stateTree actualTree : Tree Tok}
    {stateTerm actualTerm : Term}
    (hstate : denoteTerm? stateTree = some stateTerm)
    (hactual : DenotesTerm actualTree actualTerm)
    (htree : actualTree = stateTree) :
    stateTerm = actualTerm := by
  subst actualTree
  have hactual' : denoteTerm? stateTree = some actualTerm :=
    denoteTerm?_complete_of_denotes hactual
  rw [hstate] at hactual'
  simpa using hactual'

private theorem lval_eq_of_denote_eq {stateTree actualTree : Tree Tok}
    {stateLVal actualLVal : LVal}
    (hstate : denoteLVal? stateTree = some stateLVal)
    (hactual : DenotesLVal actualTree actualLVal)
    (htree : actualTree = stateTree) :
    stateLVal = actualLVal := by
  subst actualTree
  have hactual' : denoteLVal? stateTree = some actualLVal :=
    denoteLVal?_complete_of_denotes hactual
  rw [hstate] at hactual'
  simpa using hactual'

private theorem terms_eq_of_denote_eq {stateTree actualTree : Tree Tok}
    {stateTerms actualTerms : List Term}
    (hstate : denoteTerms? stateTree = some stateTerms)
    (hactual : DenotesTerms actualTree actualTerms)
    (htree : actualTree = stateTree) :
    stateTerms = actualTerms := by
  subst actualTree
  have hactual' : denoteTerms? stateTree = some actualTerms :=
    denoteTerms?_complete_of_denotes hactual
  rw [hstate] at hactual'
  simpa using hactual'

set_option linter.unusedSimpArgs false in
theorem checkedTermFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
    {frontier : PartialTerm} {tree : Tree Tok} {completed : Term}
    (hlower : CheckedTermFrontierLower state frontier)
    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesTerm tree completed) :
    CompletesTerm frontier completed := by
  induction hlower generalizing tree completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermUnit_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermUnitRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermTrue_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermTrueRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermFalse_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermFalseRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermUnit_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermInt_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermTrue_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermFalse_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBlock_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermBlock_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, _⟩
      subst actualLifetime
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot3_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, _⟩
      subst actualLifetime
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot5_boundary terms_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, htermsTreeEq, _⟩
      subst actualLifetime
      have htermsEq := terms_eq_of_denote_eq terms_denotes hterms htermsTreeEq
      subst actualTerms
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermLetMut_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName
        _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName
        _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot4_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, _⟩
      subst actualName
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermAssign_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermAssign_dot2_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBox_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBorrowShared_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermBorrowMut_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermMove_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermCopy_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermEq_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermEq_dot2_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot4_boundary condition_denotes trueBranch_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, htrueTreeEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have htrueEq :=
        term_eq_of_denote_eq trueBranch_denotes htrue htrueTreeEq
      subst actualCondition
      subst actualTrue
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermWhile_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermWhile_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, _⟩
      subst actualBodyLifetime
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermInt_intN_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIntRule] at htree
      rename_i actualN
      rcases htree with ⟨hnEq, _⟩
      subst actualN
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermInt_intN
  | ctermBlock_blockTerms_boundary terms_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, htermsTreeEq, _⟩
      subst actualLifetime
      have htermsEq := terms_eq_of_denote_eq terms_denotes hterms htermsTreeEq
      subst actualTerms
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermLetMut_letMutName_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, _⟩
      subst actualName
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName
        _root_.ConservativeExtractor.Generated.CompletesName.done
  | ctermLetMut_letMutInitialiser_boundary initialiser_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, hinitialiserTreeEq, _⟩
      subst actualName
      have hinitialiserEq :=
        term_eq_of_denote_eq initialiser_denotes hinitialiser hinitialiserTreeEq
      subst actualInitialiser
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermAssign_assignLhs_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermAssign_assignRhs_boundary lhs_denotes rhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, hrhsTreeEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      have hrhsEq := term_eq_of_denote_eq rhs_denotes hrhs hrhsTreeEq
      subst actualLhs
      subst actualRhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBox_boxOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := term_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBorrowShared_borrowSharedOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermBorrowMut_borrowMutOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermMove_moveOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermCopy_copyOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermEq_termPrefix_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermEq_eqRhs_boundary lhs_denotes rhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, hrhsTreeEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      have hrhsEq := term_eq_of_denote_eq rhs_denotes hrhs hrhsTreeEq
      subst actualLhs
      subst actualRhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteCondition_boundary condition_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      subst actualCondition
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteTrueBranch_boundary condition_denotes trueBranch_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, htrueTreeEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have htrueEq :=
        term_eq_of_denote_eq trueBranch_denotes htrue htrueTreeEq
      subst actualCondition
      subst actualTrue
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteFalseBranch_boundary condition_denotes trueBranch_denotes falseBranch_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, htrueTreeEq, hfalseTreeEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have htrueEq :=
        term_eq_of_denote_eq trueBranch_denotes htrue htrueTreeEq
      have hfalseEq :=
        term_eq_of_denote_eq falseBranch_denotes hfalse hfalseTreeEq
      subst actualCondition
      subst actualTrue
      subst actualFalse
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermWhile_whileCondition_boundary condition_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, hconditionTreeEq, _⟩
      subst actualBodyLifetime
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      subst actualCondition
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermWhile_whileBody_boundary condition_denotes body_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, hconditionTreeEq, hbodyTreeEq, _⟩
      subst actualBodyLifetime
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have hbodyEq := term_eq_of_denote_eq body_denotes hbody hbodyTreeEq
      subst actualCondition
      subst actualBody
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBlock_blockStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermLetMut_letMutStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutStart
  | ctermBox_boxStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxStart
  | ctermBorrowShared_tokenAmpStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_tokenAmpStart
  | ctermBorrowMut_tokenAmpStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_tokenAmpStart
  | ctermBorrowMut_borrowMutStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutStart
  | ctermMove_moveStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveStart
  | ctermCopy_copyStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyStart
  | ctermIte_iteStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteStart
  | ctermWhile_whileStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermBlock_blockTerms_descend terms_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, hchildEq, _⟩
      subst actualLifetime
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        (checkedTermsFrontierLower_completes_of_stateCompletes
          terms_lower hchild hterms)
  | ctermLetMut_letMutInitialiser_descend initialiser_lower initialiser_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, hchildEq, _⟩
      subst actualName
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser
        (initialiser_ih hchild hinitialiser)
  | ctermAssign_assignLhs_descend lhs_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
        (checkedLValFrontierLower_completes_of_stateCompletes
          lhs_lower hchild hlhs)
  | ctermAssign_assignRhs_descend lhs_denotes rhs_lower rhs_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, hchildEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs
        (rhs_ih hchild hrhs)
  | ctermBox_boxOperand_descend operand_lower operand_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand
        (operand_ih hchild hoperand)
  | ctermBorrowShared_borrowSharedOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand
        (checkedLValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermBorrowMut_borrowMutOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        (checkedLValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermMove_moveOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
        (checkedLValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermCopy_copyOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand
        (checkedLValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermEq_termPrefix_descend lhs_lower lhs_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
        (lhs_ih hchild hlhs)
  | ctermEq_eqRhs_descend lhs_denotes rhs_lower rhs_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, hchildEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs
        (rhs_ih hchild hrhs)
  | ctermIte_iteCondition_descend condition_lower condition_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition
        (condition_ih hchild hcondition)
  | ctermIte_iteTrueBranch_descend condition_denotes trueBranch_lower trueBranch_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, hchildEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      subst actualCondition
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch
        (trueBranch_ih hchild htrue)
  | ctermIte_iteFalseBranch_descend condition_denotes trueBranch_denotes falseBranch_lower falseBranch_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, htrueTreeEq, hchildEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have htrueEq :=
        term_eq_of_denote_eq trueBranch_denotes htrue htrueTreeEq
      subst actualCondition
      subst actualTrue
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch
        (falseBranch_ih hchild hfalse)
  | ctermWhile_whileCondition_descend condition_lower condition_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, hchildEq, _⟩
      subst actualBodyLifetime
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition
        (condition_ih hchild hcondition)
  | ctermWhile_whileBody_descend condition_denotes body_lower body_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, hconditionTreeEq, hchildEq, _⟩
      subst actualBodyLifetime
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      subst actualCondition
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody
        (body_ih hchild hbody)

theorem checkedLValsFrontierLower_exists
    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .clvals) :
    ∃ frontier : PartialLVals, CheckedLValsFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialLVals.cutoff,
    CheckedLValsFrontierLower.fallback⟩

theorem checkedLValsTailFrontierLower_exists
    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .clvalsTail) :
    ∃ frontier : PartialLVals, CheckedLValsTailFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialLVals.cutoff,
    CheckedLValsTailFrontierLower.fallback⟩

theorem checkedTermsFrontierLower_exists
    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterms) :
    ∃ frontier : PartialTerms, CheckedTermsFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialTerms.cutoff,
    CheckedTermsFrontierLower.fallback⟩

theorem checkedTermsTailFrontierLower_exists
    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .ctermsTail) :
    ∃ frontier : PartialTerms, CheckedTermsTailFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialTerms.cutoff,
    CheckedTermsTailFrontierLower.fallback⟩

theorem checkedTyFrontierLower_exists
    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .cty) :
    ∃ frontier : PartialTy, CheckedTyFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialTy.cutoff,
    CheckedTyFrontierLower.fallback⟩

theorem checkedLValFrontierLower_exists
    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .clval) :
    ∃ frontier : PartialLVal, CheckedLValFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialLVal.cutoff,
    CheckedLValFrontierLower.fallback⟩

theorem checkedTermFrontierLower_exists
    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm) :
    ∃ frontier : PartialTerm, CheckedTermFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialTerm.cutoff,
    CheckedTermFrontierLower.fallback⟩

set_option linter.unusedSimpArgs false in
theorem checkedTyFrontierLower_ctyBorrowSharedTargets_boundary_exists
    {targetsTree : Tree Tok}
    {checkedBefore :
      CheckableGrammar.checkSeq checkableGrammar
        ({ rule := ctyBorrowSharedRule, dot := 3 } : Item Cat Terminal).before
        [.token .amp, .token .lbrack, targetsTree] = Bool.true} :
    ∃ targets : List LVal,
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary
          ({ rule := ctyBorrowSharedRule, dot := 3 } : Item Cat Terminal)
          (by native_decide) [.token .amp, .token .lbrack, targetsTree]
          checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets
          (_root_.ConservativeExtractor.Generated.PartialLVals.done targets)) := by
  have htargets :
      CheckableGrammar.checkTree checkableGrammar .clvals targetsTree =
        Bool.true := by
    have h := checkedBefore
    simp [ctyBorrowSharedRule, Item.before, CheckableGrammar.checkSeq,
      acceptsBool] at h
    exact h.2.2
  obtain ⟨targets, htargetsDenote⟩ :=
    checkedLValsTree_denote_exists htargets
  exact ⟨targets,
    CheckedTyFrontierLower.ctyBorrowShared_borrowSharedTargets_boundary
      htargetsDenote⟩

set_option linter.unusedSimpArgs false in
theorem checkedTyFrontierLower_ctyBorrowMutTargets_boundary_exists
    {targetsTree : Tree Tok}
    {checkedBefore :
      CheckableGrammar.checkSeq checkableGrammar
        ({ rule := ctyBorrowMutRule, dot := 3 } : Item Cat Terminal).before
        [.token .ampMut, .token .lbrack, targetsTree] = Bool.true} :
    ∃ targets : List LVal,
      CheckedTyFrontierLower
        (CheckableGrammar.CheckedFrontierState.boundary
          ({ rule := ctyBorrowMutRule, dot := 3 } : Item Cat Terminal)
          (by native_decide) [.token .ampMut, .token .lbrack, targetsTree]
          checkedBefore)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets
          (_root_.ConservativeExtractor.Generated.PartialLVals.done targets)) := by
  have htargets :
      CheckableGrammar.checkTree checkableGrammar .clvals targetsTree =
        Bool.true := by
    have h := checkedBefore
    simp [ctyBorrowMutRule, Item.before, CheckableGrammar.checkSeq,
      acceptsBool] at h
    exact h.2.2
  obtain ⟨targets, htargetsDenote⟩ :=
    checkedLValsTree_denote_exists htargets
  exact ⟨targets,
    CheckedTyFrontierLower.ctyBorrowMut_borrowMutTargets_boundary
      htargetsDenote⟩

theorem ctyUnit_done_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxCtor.ctyUnit_ctor))
      (SyntaxCtor.ctyUnit_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.done

theorem ctyInt_done_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxCtor.ctyInt_ctor))
      (SyntaxCtor.ctyInt_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.done

theorem ctyBool_done_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxCtor.ctyBool_ctor))
      (SyntaxCtor.ctyBool_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.done

theorem ctyUnit_dot0_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)
      (SyntaxCtor.ctyUnit_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff

theorem ctyInt_dot0_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)
      (SyntaxCtor.ctyInt_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff

theorem ctyBool_dot0_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)
      (SyntaxCtor.ctyBool_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff

theorem ctyBorrowShared_dot0_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)
      (SyntaxCtor.ctyBorrowShared_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff

theorem ctyBorrowShared_dot2_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)
      (SyntaxCtor.ctyBorrowShared_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff

theorem ctyBorrowShared_dot4_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))
      (SyntaxCtor.ctyBorrowShared_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done

theorem ctyBorrowMut_dot0_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)
      (SyntaxCtor.ctyBorrowMut_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff

theorem ctyBorrowMut_dot2_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)
      (SyntaxCtor.ctyBorrowMut_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff

theorem ctyBorrowMut_dot4_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))
      (SyntaxCtor.ctyBorrowMut_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done

theorem ctyBox_dot0_boundary_completes {element : Ty} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.boxElement _root_.ConservativeExtractor.Generated.PartialTy.cutoff)
      (SyntaxCtor.ctyBox_ctor element) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement _root_.ConservativeExtractor.Generated.CompletesTy.cutoff

theorem ctyBorrowShared_borrowSharedTargets_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))
      (SyntaxCtor.ctyBorrowShared_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done

theorem ctyBorrowMut_borrowMutTargets_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))
      (SyntaxCtor.ctyBorrowMut_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done

theorem ctyBox_boxElement_boundary_completes {element : Ty} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.boxElement (_root_.ConservativeExtractor.Generated.PartialTy.done element))
      (SyntaxCtor.ctyBox_ctor element) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement _root_.ConservativeExtractor.Generated.CompletesTy.done

theorem ctyBorrowShared_tokenAmpStart_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.tokenAmpStart)
      (SyntaxCtor.ctyBorrowShared_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_tokenAmpStart

theorem ctyBorrowMut_tokenAmpStart_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.tokenAmpStart)
      (SyntaxCtor.ctyBorrowMut_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_tokenAmpStart

theorem ctyBorrowMut_borrowMutStart_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutStart)
      (SyntaxCtor.ctyBorrowMut_ctor targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutStart

theorem ctyBox_boxStart_boundary_completes {element : Ty} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.boxStart)
      (SyntaxCtor.ctyBox_ctor element) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxStart

theorem ctyBorrowShared_borrowSharedTargets_descend_completes {targets : PartialLVals} {targets' : List LVal}
    (targets_completes : _root_.ConservativeExtractor.Generated.CompletesLVals targets targets') :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets targets)
      (SyntaxCtor.ctyBorrowShared_ctor targets') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets targets_completes

theorem ctyBorrowMut_borrowMutTargets_descend_completes {targets : PartialLVals} {targets' : List LVal}
    (targets_completes : _root_.ConservativeExtractor.Generated.CompletesLVals targets targets') :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets targets)
      (SyntaxCtor.ctyBorrowMut_ctor targets') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets targets_completes

theorem ctyBox_boxElement_descend_completes {element : PartialTy} {element' : Ty}
    (element_completes : _root_.ConservativeExtractor.Generated.CompletesTy element element') :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.boxElement element)
      (SyntaxCtor.ctyBox_ctor element') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement element_completes

theorem clvalVar_dot0_boundary_completes {x : Name} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.varX _root_.ConservativeExtractor.Generated.PartialName.cutoff)
      (SyntaxCtor.clvalVar_ctor x) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX _root_.ConservativeExtractor.Generated.CompletesName.cutoff

theorem clvalDeref_dot0_boundary_completes {operand : LVal} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxCtor.clvalDeref_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem clvalVar_varX_boundary_completes {x : Name} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.varX (_root_.ConservativeExtractor.Generated.PartialName.done x))
      (SyntaxCtor.clvalVar_ctor x) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX _root_.ConservativeExtractor.Generated.CompletesName.done

theorem clvalDeref_derefOperand_boundary_completes {operand : LVal} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxCtor.clvalDeref_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem clvalDeref_derefStart_boundary_completes {operand : LVal} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.derefStart)
      (SyntaxCtor.clvalDeref_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefStart

theorem clvalDeref_derefOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand operand)
      (SyntaxCtor.clvalDeref_ctor operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand operand_completes

theorem ctermUnit_done_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxCtor.ctermUnit_ctor))
      (SyntaxCtor.ctermUnit_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermTrue_done_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxCtor.ctermTrue_ctor))
      (SyntaxCtor.ctermTrue_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermFalse_done_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxCtor.ctermFalse_ctor))
      (SyntaxCtor.ctermFalse_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermUnit_dot0_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermUnit_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermInt_dot0_boundary_completes {n : Int} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermInt_ctor n) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermTrue_dot0_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermTrue_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermFalse_dot0_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermFalse_ctor) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermBlock_dot0_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockStart)
      (SyntaxCtor.ctermBlock_ctor lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart

theorem ctermBlock_dot2_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime _root_.ConservativeExtractor.Generated.PartialTerms.cutoff)
      (SyntaxCtor.ctermBlock_ctor lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff

theorem ctermBlock_dot3_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime _root_.ConservativeExtractor.Generated.PartialTerms.cutoff)
      (SyntaxCtor.ctermBlock_ctor lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff

theorem ctermBlock_dot5_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime (_root_.ConservativeExtractor.Generated.PartialTerms.done terms))
      (SyntaxCtor.ctermBlock_ctor lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.done

theorem ctermLetMut_dot0_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName _root_.ConservativeExtractor.Generated.PartialName.cutoff)
      (SyntaxCtor.ctermLetMut_ctor name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.cutoff

theorem ctermLetMut_dot2_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName _root_.ConservativeExtractor.Generated.PartialName.cutoff)
      (SyntaxCtor.ctermLetMut_ctor name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.cutoff

theorem ctermLetMut_dot4_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermLetMut_ctor name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermAssign_dot0_boundary_completes {lhs : LVal} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxCtor.ctermAssign_ctor lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermAssign_dot2_boundary_completes {lhs : LVal} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermAssign_ctor lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermBox_dot0_boundary_completes {operand : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermBox_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermBorrowShared_dot0_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxCtor.ctermBorrowShared_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermBorrowMut_dot0_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxCtor.ctermBorrowMut_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermMove_dot0_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxCtor.ctermMove_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermCopy_dot0_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxCtor.ctermCopy_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermEq_dot0_boundary_completes {lhs : Term} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermEq_ctor lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermEq_dot2_boundary_completes {lhs : Term} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermEq_ctor lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermIte_dot0_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermIte_dot4_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermWhile_dot0_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileStart)
      (SyntaxCtor.ctermWhile_ctor bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart

theorem ctermWhile_dot2_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxCtor.ctermWhile_ctor bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermInt_intN_boundary_completes {n : Int} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.intN n)
      (SyntaxCtor.ctermInt_ctor n) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermInt_intN

theorem ctermBlock_blockTerms_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime (_root_.ConservativeExtractor.Generated.PartialTerms.done terms))
      (SyntaxCtor.ctermBlock_ctor lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.done

theorem ctermLetMut_letMutName_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName (_root_.ConservativeExtractor.Generated.PartialName.done name))
      (SyntaxCtor.ctermLetMut_ctor name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.done

theorem ctermLetMut_letMutInitialiser_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name (_root_.ConservativeExtractor.Generated.PartialTerm.done initialiser))
      (SyntaxCtor.ctermLetMut_ctor name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermAssign_assignLhs_boundary_completes {lhs : LVal} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs (_root_.ConservativeExtractor.Generated.PartialLVal.done lhs))
      (SyntaxCtor.ctermAssign_ctor lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermAssign_assignRhs_boundary_completes {lhs : LVal} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs (_root_.ConservativeExtractor.Generated.PartialTerm.done rhs))
      (SyntaxCtor.ctermAssign_ctor lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermBox_boxOperand_boundary_completes {operand : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand (_root_.ConservativeExtractor.Generated.PartialTerm.done operand))
      (SyntaxCtor.ctermBox_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermBorrowShared_borrowSharedOperand_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxCtor.ctermBorrowShared_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermBorrowMut_borrowMutOperand_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxCtor.ctermBorrowMut_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermMove_moveOperand_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxCtor.ctermMove_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermCopy_copyOperand_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxCtor.ctermCopy_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermEq_termPrefix_boundary_completes {lhs : Term} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix (_root_.ConservativeExtractor.Generated.PartialTerm.done lhs))
      (SyntaxCtor.ctermEq_ctor lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermEq_eqRhs_boundary_completes {lhs : Term} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs (_root_.ConservativeExtractor.Generated.PartialTerm.done rhs))
      (SyntaxCtor.ctermEq_ctor lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermIte_iteCondition_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition (_root_.ConservativeExtractor.Generated.PartialTerm.done condition))
      (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermIte_iteTrueBranch_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteTrueBranch condition (_root_.ConservativeExtractor.Generated.PartialTerm.done trueBranch))
      (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermIte_iteFalseBranch_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch (_root_.ConservativeExtractor.Generated.PartialTerm.done falseBranch))
      (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermWhile_whileCondition_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime (_root_.ConservativeExtractor.Generated.PartialTerm.done condition))
      (SyntaxCtor.ctermWhile_ctor bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermWhile_whileBody_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileBody bodyLifetime condition (_root_.ConservativeExtractor.Generated.PartialTerm.done body))
      (SyntaxCtor.ctermWhile_ctor bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermBlock_blockStart_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockStart)
      (SyntaxCtor.ctermBlock_ctor lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart

theorem ctermLetMut_letMutStart_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutStart)
      (SyntaxCtor.ctermLetMut_ctor name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutStart

theorem ctermBox_boxStart_boundary_completes {operand : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.boxStart)
      (SyntaxCtor.ctermBox_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxStart

theorem ctermBorrowShared_tokenAmpStart_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.tokenAmpStart)
      (SyntaxCtor.ctermBorrowShared_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_tokenAmpStart

theorem ctermBorrowMut_tokenAmpStart_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.tokenAmpStart)
      (SyntaxCtor.ctermBorrowMut_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_tokenAmpStart

theorem ctermBorrowMut_borrowMutStart_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutStart)
      (SyntaxCtor.ctermBorrowMut_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutStart

theorem ctermMove_moveStart_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.moveStart)
      (SyntaxCtor.ctermMove_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveStart

theorem ctermCopy_copyStart_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.copyStart)
      (SyntaxCtor.ctermCopy_ctor operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyStart

theorem ctermIte_iteStart_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteStart)
      (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteStart

theorem ctermWhile_whileStart_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileStart)
      (SyntaxCtor.ctermWhile_ctor bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart

theorem ctermBlock_blockTerms_descend_completes {lifetime : Lifetime} {terms : PartialTerms} {terms' : List Term}
    (terms_completes : _root_.ConservativeExtractor.Generated.CompletesTerms terms terms') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime terms)
      (SyntaxCtor.ctermBlock_ctor lifetime terms') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms terms_completes

theorem ctermLetMut_letMutInitialiser_descend_completes {name : Name} {initialiser : PartialTerm} {initialiser' : Term}
    (initialiser_completes : _root_.ConservativeExtractor.Generated.CompletesTerm initialiser initialiser') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name initialiser)
      (SyntaxCtor.ctermLetMut_ctor name initialiser') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser initialiser_completes

theorem ctermAssign_assignLhs_descend_completes {lhs : PartialLVal} {lhs' : LVal} {rhs : Term}
    (lhs_completes : _root_.ConservativeExtractor.Generated.CompletesLVal lhs lhs') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs lhs)
      (SyntaxCtor.ctermAssign_ctor lhs' rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs lhs_completes

theorem ctermAssign_assignRhs_descend_completes {lhs : LVal} {rhs : PartialTerm} {rhs' : Term}
    (rhs_completes : _root_.ConservativeExtractor.Generated.CompletesTerm rhs rhs') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs rhs)
      (SyntaxCtor.ctermAssign_ctor lhs rhs') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs rhs_completes

theorem ctermBox_boxOperand_descend_completes {operand : PartialTerm} {operand' : Term}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesTerm operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand operand)
      (SyntaxCtor.ctermBox_ctor operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand operand_completes

theorem ctermBorrowShared_borrowSharedOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand operand)
      (SyntaxCtor.ctermBorrowShared_ctor operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand operand_completes

theorem ctermBorrowMut_borrowMutOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand operand)
      (SyntaxCtor.ctermBorrowMut_ctor operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand operand_completes

theorem ctermMove_moveOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand operand)
      (SyntaxCtor.ctermMove_ctor operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand operand_completes

theorem ctermCopy_copyOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand operand)
      (SyntaxCtor.ctermCopy_ctor operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand operand_completes

theorem ctermEq_termPrefix_descend_completes {lhs : PartialTerm} {lhs' : Term} {rhs : Term}
    (lhs_completes : _root_.ConservativeExtractor.Generated.CompletesTerm lhs lhs') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix lhs)
      (SyntaxCtor.ctermEq_ctor lhs' rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix lhs_completes

theorem ctermEq_eqRhs_descend_completes {lhs : Term} {rhs : PartialTerm} {rhs' : Term}
    (rhs_completes : _root_.ConservativeExtractor.Generated.CompletesTerm rhs rhs') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs rhs)
      (SyntaxCtor.ctermEq_ctor lhs rhs') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs rhs_completes

theorem ctermIte_iteCondition_descend_completes {condition : PartialTerm} {condition' : Term} {trueBranch : Term} {falseBranch : Term}
    (condition_completes : _root_.ConservativeExtractor.Generated.CompletesTerm condition condition') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition condition)
      (SyntaxCtor.ctermIte_ctor condition' trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition condition_completes

theorem ctermIte_iteTrueBranch_descend_completes {condition : Term} {trueBranch : PartialTerm} {trueBranch' : Term} {falseBranch : Term}
    (trueBranch_completes : _root_.ConservativeExtractor.Generated.CompletesTerm trueBranch trueBranch') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteTrueBranch condition trueBranch)
      (SyntaxCtor.ctermIte_ctor condition trueBranch' falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch trueBranch_completes

theorem ctermIte_iteFalseBranch_descend_completes {condition : Term} {trueBranch : Term} {falseBranch : PartialTerm} {falseBranch' : Term}
    (falseBranch_completes : _root_.ConservativeExtractor.Generated.CompletesTerm falseBranch falseBranch') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch falseBranch)
      (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch falseBranch_completes

theorem ctermWhile_whileCondition_descend_completes {bodyLifetime : Lifetime} {condition : PartialTerm} {condition' : Term} {body : Term}
    (condition_completes : _root_.ConservativeExtractor.Generated.CompletesTerm condition condition') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime condition)
      (SyntaxCtor.ctermWhile_ctor bodyLifetime condition' body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition condition_completes

theorem ctermWhile_whileBody_descend_completes {bodyLifetime : Lifetime} {condition : Term} {body : PartialTerm} {body' : Term}
    (body_completes : _root_.ConservativeExtractor.Generated.CompletesTerm body body') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileBody bodyLifetime condition body)
      (SyntaxCtor.ctermWhile_ctor bodyLifetime condition body') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody body_completes

end GeneratedFrontierLower
end FwRust
end GrammarFrontier
end ConservativeExtractor
