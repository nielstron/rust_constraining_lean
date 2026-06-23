import LwRust.Extractor.FrontierSemantics
import LwRust.Extractor.PartialProgram

/-!
Generated lowering hooks from grammar-validated FW parser frontiers to the
existing generated partial-program frontiers.

This file is generated from the syntax declarations and
`SyntaxSemantics` annotations in `LwRust.Extractor.CompleteProgram`.
Re-generate it with `scripts/generate_frontier_lower_from_syntax.py`.
-/

namespace ConservativeExtractor
namespace GrammarFrontier
namespace FwRust
namespace GeneratedFrontierLower

inductive LValsFrontierLower :
    CheckableGrammar.FrontierState checkableGrammar .clvals →
    PartialLVals → Prop where
  | fallback
      {state : CheckableGrammar.FrontierState checkableGrammar .clvals} :
      LValsFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | clvalsEmpty_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsEmptyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      LValsFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalsEmptyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVals.done [])

  | clvalsCons_start_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      LValsFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalsConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsCons_head_boundary
      {headTree : Tree Tok}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 1 } : Item Cat Terminal).before [headTree] = Bool.true} :
      LValsFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalsConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) [headTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsCons_done_boundary
      {headTree tailTree : Tree Tok}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 2 } : Item Cat Terminal).before [headTree, tailTree] = Bool.true} :
      LValsFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalsConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) [headTree, tailTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsCons_head_descend
      {headState : CheckableGrammar.FrontierState checkableGrammar .clval}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      LValsFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := clvalsConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) .clval [.cat .clvalsTail] (by native_decide) [] before_ok headState)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsCons_tail_descend
      {headTree : Tree Tok}
      {tailState : CheckableGrammar.FrontierState checkableGrammar .clvalsTail}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsConsRule, dot := 1 } : Item Cat Terminal).before [headTree] = Bool.true} :
      LValsFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := clvalsConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clvalsTail [] (by native_decide) [headTree] before_ok tailState)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

inductive LValsTailFrontierLower :
    CheckableGrammar.FrontierState checkableGrammar .clvalsTail →
    PartialLVals → Prop where
  | fallback
      {state : CheckableGrammar.FrontierState checkableGrammar .clvalsTail} :
      LValsTailFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | clvalsTailEmpty_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailEmptyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      LValsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalsTailEmptyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVals.done [])

  | clvalsTailCons_start_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      LValsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalsTailConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_comma_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 1 } : Item Cat Terminal).before [.token .comma] = Bool.true} :
      LValsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalsTailConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .comma] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_head_boundary
      {headTree : Tree Tok}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 2 } : Item Cat Terminal).before [.token .comma, headTree] = Bool.true} :
      LValsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalsTailConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .comma, headTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_done_boundary
      {headTree tailTree : Tree Tok}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 3 } : Item Cat Terminal).before [.token .comma, headTree, tailTree] = Bool.true} :
      LValsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalsTailConsRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .comma, headTree, tailTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_head_descend
      {headState : CheckableGrammar.FrontierState checkableGrammar .clval}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 1 } : Item Cat Terminal).before [.token .comma] = Bool.true} :
      LValsTailFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := clvalsTailConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [.cat .clvalsTail] (by native_decide) [.token .comma] before_ok headState)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

  | clvalsTailCons_tail_descend
      {headTree : Tree Tok}
      {tailState : CheckableGrammar.FrontierState checkableGrammar .clvalsTail}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalsTailConsRule, dot := 2 } : Item Cat Terminal).before [.token .comma, headTree] = Bool.true} :
      LValsTailFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := clvalsTailConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) .clvalsTail [] (by native_decide) [.token .comma, headTree] before_ok tailState)
        (_root_.ConservativeExtractor.Generated.PartialLVals.elems [] none)

inductive TermsFrontierLower :
    CheckableGrammar.FrontierState checkableGrammar .cterms →
    PartialTerms → Prop where
  | fallback
      {state : CheckableGrammar.FrontierState checkableGrammar .cterms} :
      TermsFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialTerms.cutoff)

  | ctermsEmpty_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsEmptyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermsFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermsEmptyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerms.done [])

  | ctermsCons_start_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermsFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermsConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsCons_head_boundary
      {headTree : Tree Tok}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 1 } : Item Cat Terminal).before [headTree] = Bool.true} :
      TermsFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermsConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) [headTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsCons_done_boundary
      {headTree tailTree : Tree Tok}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 2 } : Item Cat Terminal).before [headTree, tailTree] = Bool.true} :
      TermsFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermsConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) [headTree, tailTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsCons_head_descend
      {headState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermsFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermsConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) .cterm [.cat .ctermsTail] (by native_decide) [] before_ok headState)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsCons_tail_descend
      {headTree : Tree Tok}
      {tailState : CheckableGrammar.FrontierState checkableGrammar .ctermsTail}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsConsRule, dot := 1 } : Item Cat Terminal).before [headTree] = Bool.true} :
      TermsFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermsConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) .ctermsTail [] (by native_decide) [headTree] before_ok tailState)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

inductive TermsTailFrontierLower :
    CheckableGrammar.FrontierState checkableGrammar .ctermsTail →
    PartialTerms → Prop where
  | fallback
      {state : CheckableGrammar.FrontierState checkableGrammar .ctermsTail} :
      TermsTailFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialTerms.cutoff)

  | ctermsTailEmpty_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailEmptyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermsTailEmptyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerms.done [])

  | ctermsTailCons_start_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermsTailConsRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_comma_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 1 } : Item Cat Terminal).before [.token .comma] = Bool.true} :
      TermsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermsTailConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .comma] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_head_boundary
      {headTree : Tree Tok}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 2 } : Item Cat Terminal).before [.token .comma, headTree] = Bool.true} :
      TermsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermsTailConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .comma, headTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_done_boundary
      {headTree tailTree : Tree Tok}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 3 } : Item Cat Terminal).before [.token .comma, headTree, tailTree] = Bool.true} :
      TermsTailFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermsTailConsRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .comma, headTree, tailTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_head_descend
      {headState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 1 } : Item Cat Terminal).before [.token .comma] = Bool.true} :
      TermsTailFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermsTailConsRule, dot := 1 } : Item Cat Terminal) (by native_decide) .cterm [.cat .ctermsTail] (by native_decide) [.token .comma] before_ok headState)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

  | ctermsTailCons_tail_descend
      {headTree : Tree Tok}
      {tailState : CheckableGrammar.FrontierState checkableGrammar .ctermsTail}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermsTailConsRule, dot := 2 } : Item Cat Terminal).before [.token .comma, headTree] = Bool.true} :
      TermsTailFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermsTailConsRule, dot := 2 } : Item Cat Terminal) (by native_decide) .ctermsTail [] (by native_decide) [.token .comma, headTree] before_ok tailState)
        (_root_.ConservativeExtractor.Generated.PartialTerms.elems [] none)

inductive TyFrontierLower :
    CheckableGrammar.FrontierState checkableGrammar .cty →
    PartialTy → Prop where
  | fallback
      {state : CheckableGrammar.FrontierState checkableGrammar .cty} :
      TyFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyUnit_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyUnitRule, dot := 1 } : Item Cat Terminal).before [.token .ctyUnit] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyUnitRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ctyUnit] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxSemantics.ctyUnit))

  | ctyInt_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyIntRule, dot := 1 } : Item Cat Terminal).before [.token .ctyInt] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyIntRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ctyInt] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxSemantics.ctyInt))

  | ctyBool_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoolRule, dot := 1 } : Item Cat Terminal).before [.token .ctyBool] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBoolRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ctyBool] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxSemantics.ctyBool))

  | ctyUnit_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyUnitRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyUnitRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyInt_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyIntRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyIntRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyBool_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoolRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBoolRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyBorrowShared_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | ctyBorrowShared_dot2_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 2 } : Item Cat Terminal).before [.token .amp, .token .lbrack] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .lbrack] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | ctyBorrowShared_dot4_boundary
      {targetsTree : Tree Tok} {targets : List LVal}
      (targets_denotes : denoteLVals? targetsTree = some targets)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 4 } : Item Cat Terminal).before [.token .amp, .token .lbrack, targetsTree, .token .rbrack] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .lbrack, targetsTree, .token .rbrack] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))

  | ctyBorrowMut_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | ctyBorrowMut_dot2_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 2 } : Item Cat Terminal).before [.token .amp, .token .mutKw] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .mutKw] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | ctyBorrowMut_dot3_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 3 } : Item Cat Terminal).before [.token .amp, .token .mutKw, .token .lbrack] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .mutKw, .token .lbrack] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)

  | ctyBorrowMut_dot5_boundary
      {targetsTree : Tree Tok} {targets : List LVal}
      (targets_denotes : denoteLVals? targetsTree = some targets)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 5 } : Item Cat Terminal).before [.token .amp, .token .mutKw, .token .lbrack, targetsTree, .token .rbrack] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 5 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .mutKw, .token .lbrack, targetsTree, .token .rbrack] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))

  | ctyBox_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoxRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBoxRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.boxElement _root_.ConservativeExtractor.Generated.PartialTy.cutoff)

  | ctyBorrowShared_borrowSharedTargets_boundary
      {targetsTree : Tree Tok} {targets : List LVal}
      (targets_denotes : denoteLVals? targetsTree = some targets)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 3 } : Item Cat Terminal).before [.token .amp, .token .lbrack, targetsTree] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .lbrack, targetsTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))

  | ctyBorrowMut_borrowMutTargets_boundary
      {targetsTree : Tree Tok} {targets : List LVal}
      (targets_denotes : denoteLVals? targetsTree = some targets)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 4 } : Item Cat Terminal).before [.token .amp, .token .mutKw, .token .lbrack, targetsTree] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .mutKw, .token .lbrack, targetsTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))

  | ctyBox_boxElement_boundary
      {elementTree : Tree Tok} {element : Ty}
      (element_denotes : denoteTy? elementTree = some element)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoxRule, dot := 2 } : Item Cat Terminal).before [.token .box, elementTree] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBoxRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .box, elementTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.boxElement (_root_.ConservativeExtractor.Generated.PartialTy.done element))

  | ctyBorrowShared_borrowSharedStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 1 } : Item Cat Terminal).before [.token .amp] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowSharedRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .amp] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedStart)

  | ctyBorrowMut_borrowSharedStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 1 } : Item Cat Terminal).before [.token .amp] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBorrowMutRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .amp] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedStart)

  | ctyBox_boxStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoxRule, dot := 1 } : Item Cat Terminal).before [.token .box] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctyBoxRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .box] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.boxStart)

  | ctyBorrowShared_borrowSharedTargets_descend
      {targetsState : CheckableGrammar.FrontierState checkableGrammar .clvals}
      {targets : PartialLVals}
      (targets_lower : LValsFrontierLower targetsState targets)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowSharedRule, dot := 2 } : Item Cat Terminal).before [.token .amp, .token .lbrack] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctyBorrowSharedRule, dot := 2 } : Item Cat Terminal) (by native_decide) .clvals [.token .rbrack] (by native_decide) [.token .amp, .token .lbrack] before_ok targetsState)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets targets)

  | ctyBorrowMut_borrowMutTargets_descend
      {targetsState : CheckableGrammar.FrontierState checkableGrammar .clvals}
      {targets : PartialLVals}
      (targets_lower : LValsFrontierLower targetsState targets)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBorrowMutRule, dot := 3 } : Item Cat Terminal).before [.token .amp, .token .mutKw, .token .lbrack] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctyBorrowMutRule, dot := 3 } : Item Cat Terminal) (by native_decide) .clvals [.token .rbrack] (by native_decide) [.token .amp, .token .mutKw, .token .lbrack] before_ok targetsState)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets targets)

  | ctyBox_boxElement_descend
      {elementState : CheckableGrammar.FrontierState checkableGrammar .cty}
      {element : PartialTy}
      (element_lower : TyFrontierLower elementState element)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctyBoxRule, dot := 1 } : Item Cat Terminal).before [.token .box] = Bool.true} :
      TyFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctyBoxRule, dot := 1 } : Item Cat Terminal) (by native_decide) .cty [] (by native_decide) [.token .box] before_ok elementState)
        (_root_.ConservativeExtractor.Generated.PartialTy.boxElement element)

inductive LValFrontierLower :
    CheckableGrammar.FrontierState checkableGrammar .clval →
    PartialLVal → Prop where
  | fallback
      {state : CheckableGrammar.FrontierState checkableGrammar .clval} :
      LValFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | clvalVar_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalVarRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      LValFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalVarRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVal.varX _root_.ConservativeExtractor.Generated.PartialName.cutoff)

  | clvalDeref_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalDerefRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      LValFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalDerefRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | clvalVar_varX_boundary
      {x : Name}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalVarRule, dot := 1 } : Item Cat Terminal).before [.token (.ident x)] = Bool.true} :
      LValFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalVarRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token (.ident x)] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVal.varX (_root_.ConservativeExtractor.Generated.PartialName.done x))

  | clvalDeref_derefOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalDerefRule, dot := 2 } : Item Cat Terminal).before [.token .star, operandTree] = Bool.true} :
      LValFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalDerefRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .star, operandTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | clvalDeref_derefStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalDerefRule, dot := 1 } : Item Cat Terminal).before [.token .star] = Bool.true} :
      LValFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := clvalDerefRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .star] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialLVal.derefStart)

  | clvalDeref_derefOperand_descend
      {operandState : CheckableGrammar.FrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : LValFrontierLower operandState operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := clvalDerefRule, dot := 1 } : Item Cat Terminal).before [.token .star] = Bool.true} :
      LValFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := clvalDerefRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [.token .star] before_ok operandState)
        (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand operand)

inductive TermFrontierLower :
    CheckableGrammar.FrontierState checkableGrammar .cterm →
    PartialTerm → Prop where
  | fallback
      {state : CheckableGrammar.FrontierState checkableGrammar .cterm} :
      TermFrontierLower
        state
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermUnit_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermUnitRule, dot := 1 } : Item Cat Terminal).before [.token .unit] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermUnitRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .unit] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxSemantics.ctermUnit))

  | ctermTrue_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermTrueRule, dot := 1 } : Item Cat Terminal).before [.token .trueLit] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermTrueRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .trueLit] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxSemantics.ctermTrue))

  | ctermFalse_done_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermFalseRule, dot := 1 } : Item Cat Terminal).before [.token .falseLit] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermFalseRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .falseLit] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxSemantics.ctermFalse))

  | ctermUnit_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermUnitRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermUnitRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermInt_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIntRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermIntRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermTrue_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermTrueRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermTrueRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermFalse_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermFalseRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermFalseRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermBlock_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBlockRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockStart)

  | ctermBlock_dot2_boundary
      {lifetime : Lifetime}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 2 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime)] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBlockRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .block, .token (.lifetime lifetime)] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime _root_.ConservativeExtractor.Generated.PartialTerms.cutoff)

  | ctermBlock_dot3_boundary
      {lifetime : Lifetime}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 3 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime), .token .lbrace] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBlockRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .block, .token (.lifetime lifetime), .token .lbrace] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime _root_.ConservativeExtractor.Generated.PartialTerms.cutoff)

  | ctermBlock_dot5_boundary
      {lifetime : Lifetime}
      {termsTree : Tree Tok} {terms : List Term}
      (terms_denotes : denoteTerms? termsTree = some terms)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 5 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime), .token .lbrace, termsTree, .token .rbrace] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBlockRule, dot := 5 } : Item Cat Terminal) (by native_decide) [.token .block, .token (.lifetime lifetime), .token .lbrace, termsTree, .token .rbrace] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime (_root_.ConservativeExtractor.Generated.PartialTerms.done terms))

  | ctermLetMut_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermLetMutRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName _root_.ConservativeExtractor.Generated.PartialName.cutoff)

  | ctermLetMut_dot2_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 2 } : Item Cat Terminal).before [.token .letKw, .token .mutKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermLetMutRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .letKw, .token .mutKw] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName _root_.ConservativeExtractor.Generated.PartialName.cutoff)

  | ctermLetMut_dot4_boundary
      {name : Name}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 4 } : Item Cat Terminal).before [.token .letKw, .token .mutKw, .token (.ident name), .token .assign] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermLetMutRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .letKw, .token .mutKw, .token (.ident name), .token .assign] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermAssign_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermAssignRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermAssign_dot2_boundary
      {lhsTree : Tree Tok} {lhs : LVal}
      (lhs_denotes : denoteLVal? lhsTree = some lhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 2 } : Item Cat Terminal).before [lhsTree, .token .assign] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermAssignRule, dot := 2 } : Item Cat Terminal) (by native_decide) [lhsTree, .token .assign] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermBox_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBoxRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBoxRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermBorrowShared_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowSharedRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBorrowSharedRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermBorrowMut_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBorrowMutRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermBorrowMut_dot2_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 2 } : Item Cat Terminal).before [.token .amp, .token .mutKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBorrowMutRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .mutKw] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermMove_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermMoveRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermMoveRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermCopy_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermCopyRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermCopyRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)

  | ctermEq_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermEqRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermEq_dot2_boundary
      {lhsTree : Tree Tok} {lhs : Term}
      (lhs_denotes : denoteTerm? lhsTree = some lhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 2 } : Item Cat Terminal).before [lhsTree, .token .eqEq] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermEqRule, dot := 2 } : Item Cat Terminal) (by native_decide) [lhsTree, .token .eqEq] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermIte_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermIteRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermIte_dot4_boundary
      {conditionTree : Tree Tok} {condition : Term}
      {trueBranchTree : Tree Tok} {trueBranch : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (trueBranch_denotes : denoteTerm? trueBranchTree = some trueBranch)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 4 } : Item Cat Terminal).before [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermIteRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermWhile_dot0_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermWhileRule, dot := 0 } : Item Cat Terminal) (by native_decide) [] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileStart)

  | ctermWhile_dot2_boundary
      {bodyLifetime : Lifetime}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 2 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime)] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermWhileRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime)] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)

  | ctermInt_intN_boundary
      {n : Int}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIntRule, dot := 1 } : Item Cat Terminal).before [.token (.num n)] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermIntRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token (.num n)] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.intN n)

  | ctermBlock_blockTerms_boundary
      {lifetime : Lifetime}
      {termsTree : Tree Tok} {terms : List Term}
      (terms_denotes : denoteTerms? termsTree = some terms)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 4 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime), .token .lbrace, termsTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBlockRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .block, .token (.lifetime lifetime), .token .lbrace, termsTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime (_root_.ConservativeExtractor.Generated.PartialTerms.done terms))

  | ctermLetMut_letMutName_boundary
      {name : Name}
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 3 } : Item Cat Terminal).before [.token .letKw, .token .mutKw, .token (.ident name)] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermLetMutRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .letKw, .token .mutKw, .token (.ident name)] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName (_root_.ConservativeExtractor.Generated.PartialName.done name))

  | ctermLetMut_letMutInitialiser_boundary
      {name : Name}
      {initialiserTree : Tree Tok} {initialiser : Term}
      (initialiser_denotes : denoteTerm? initialiserTree = some initialiser)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 5 } : Item Cat Terminal).before [.token .letKw, .token .mutKw, .token (.ident name), .token .assign, initialiserTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermLetMutRule, dot := 5 } : Item Cat Terminal) (by native_decide) [.token .letKw, .token .mutKw, .token (.ident name), .token .assign, initialiserTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name (_root_.ConservativeExtractor.Generated.PartialTerm.done initialiser))

  | ctermAssign_assignLhs_boundary
      {lhsTree : Tree Tok} {lhs : LVal}
      (lhs_denotes : denoteLVal? lhsTree = some lhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 1 } : Item Cat Terminal).before [lhsTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermAssignRule, dot := 1 } : Item Cat Terminal) (by native_decide) [lhsTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs (_root_.ConservativeExtractor.Generated.PartialLVal.done lhs))

  | ctermAssign_assignRhs_boundary
      {lhsTree : Tree Tok} {lhs : LVal}
      {rhsTree : Tree Tok} {rhs : Term}
      (lhs_denotes : denoteLVal? lhsTree = some lhs)
      (rhs_denotes : denoteTerm? rhsTree = some rhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 3 } : Item Cat Terminal).before [lhsTree, .token .assign, rhsTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermAssignRule, dot := 3 } : Item Cat Terminal) (by native_decide) [lhsTree, .token .assign, rhsTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs (_root_.ConservativeExtractor.Generated.PartialTerm.done rhs))

  | ctermBox_boxOperand_boundary
      {operandTree : Tree Tok} {operand : Term}
      (operand_denotes : denoteTerm? operandTree = some operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBoxRule, dot := 2 } : Item Cat Terminal).before [.token .box, operandTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBoxRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .box, operandTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand (_root_.ConservativeExtractor.Generated.PartialTerm.done operand))

  | ctermBorrowShared_borrowSharedOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowSharedRule, dot := 2 } : Item Cat Terminal).before [.token .amp, operandTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBorrowSharedRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .amp, operandTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | ctermBorrowMut_borrowMutOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 3 } : Item Cat Terminal).before [.token .amp, .token .mutKw, operandTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBorrowMutRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .amp, .token .mutKw, operandTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | ctermMove_moveOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermMoveRule, dot := 1 } : Item Cat Terminal).before [operandTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermMoveRule, dot := 1 } : Item Cat Terminal) (by native_decide) [operandTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | ctermCopy_copyOperand_boundary
      {operandTree : Tree Tok} {operand : LVal}
      (operand_denotes : denoteLVal? operandTree = some operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermCopyRule, dot := 2 } : Item Cat Terminal).before [.token .copyKw, operandTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermCopyRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .copyKw, operandTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))

  | ctermEq_termPrefix_boundary
      {lhsTree : Tree Tok} {lhs : Term}
      (lhs_denotes : denoteTerm? lhsTree = some lhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 1 } : Item Cat Terminal).before [lhsTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermEqRule, dot := 1 } : Item Cat Terminal) (by native_decide) [lhsTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix (_root_.ConservativeExtractor.Generated.PartialTerm.done lhs))

  | ctermEq_eqRhs_boundary
      {lhsTree : Tree Tok} {lhs : Term}
      {rhsTree : Tree Tok} {rhs : Term}
      (lhs_denotes : denoteTerm? lhsTree = some lhs)
      (rhs_denotes : denoteTerm? rhsTree = some rhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 3 } : Item Cat Terminal).before [lhsTree, .token .eqEq, rhsTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermEqRule, dot := 3 } : Item Cat Terminal) (by native_decide) [lhsTree, .token .eqEq, rhsTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs (_root_.ConservativeExtractor.Generated.PartialTerm.done rhs))

  | ctermIte_iteCondition_boundary
      {conditionTree : Tree Tok} {condition : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 2 } : Item Cat Terminal).before [.token .ifKw, conditionTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermIteRule, dot := 2 } : Item Cat Terminal) (by native_decide) [.token .ifKw, conditionTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition (_root_.ConservativeExtractor.Generated.PartialTerm.done condition))

  | ctermIte_iteTrueBranch_boundary
      {conditionTree : Tree Tok} {condition : Term}
      {trueBranchTree : Tree Tok} {trueBranch : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (trueBranch_denotes : denoteTerm? trueBranchTree = some trueBranch)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 3 } : Item Cat Terminal).before [.token .ifKw, conditionTree, trueBranchTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermIteRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .ifKw, conditionTree, trueBranchTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteTrueBranch condition (_root_.ConservativeExtractor.Generated.PartialTerm.done trueBranch))

  | ctermIte_iteFalseBranch_boundary
      {conditionTree : Tree Tok} {condition : Term}
      {trueBranchTree : Tree Tok} {trueBranch : Term}
      {falseBranchTree : Tree Tok} {falseBranch : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (trueBranch_denotes : denoteTerm? trueBranchTree = some trueBranch)
      (falseBranch_denotes : denoteTerm? falseBranchTree = some falseBranch)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 5 } : Item Cat Terminal).before [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw, falseBranchTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermIteRule, dot := 5 } : Item Cat Terminal) (by native_decide) [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw, falseBranchTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch (_root_.ConservativeExtractor.Generated.PartialTerm.done falseBranch))

  | ctermWhile_whileCondition_boundary
      {bodyLifetime : Lifetime}
      {conditionTree : Tree Tok} {condition : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 3 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermWhileRule, dot := 3 } : Item Cat Terminal) (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime (_root_.ConservativeExtractor.Generated.PartialTerm.done condition))

  | ctermWhile_whileBody_boundary
      {bodyLifetime : Lifetime}
      {conditionTree : Tree Tok} {condition : Term}
      {bodyTree : Tree Tok} {body : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (body_denotes : denoteTerm? bodyTree = some body)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 4 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree, bodyTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermWhileRule, dot := 4 } : Item Cat Terminal) (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree, bodyTree] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileBody bodyLifetime condition (_root_.ConservativeExtractor.Generated.PartialTerm.done body))

  | ctermBlock_blockStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 1 } : Item Cat Terminal).before [.token .block] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBlockRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .block] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockStart)

  | ctermLetMut_letMutStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 1 } : Item Cat Terminal).before [.token .letKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermLetMutRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .letKw] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutStart)

  | ctermBox_boxStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal).before [.token .box] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .box] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.boxStart)

  | ctermBorrowShared_borrowSharedStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowSharedRule, dot := 1 } : Item Cat Terminal).before [.token .amp] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBorrowSharedRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .amp] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedStart)

  | ctermBorrowMut_borrowSharedStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 1 } : Item Cat Terminal).before [.token .amp] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermBorrowMutRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .amp] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedStart)

  | ctermCopy_copyStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermCopyRule, dot := 1 } : Item Cat Terminal).before [.token .copyKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermCopyRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .copyKw] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.copyStart)

  | ctermIte_iteStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 1 } : Item Cat Terminal).before [.token .ifKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermIteRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .ifKw] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteStart)

  | ctermWhile_whileStart_boundary
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 1 } : Item Cat Terminal).before [.token .whileKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.boundary ({ rule := ctermWhileRule, dot := 1 } : Item Cat Terminal) (by native_decide) [.token .whileKw] before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileStart)

  | ctermBlock_blockTerms_descend
      {lifetime : Lifetime}
      {termsState : CheckableGrammar.FrontierState checkableGrammar .cterms}
      {terms : PartialTerms}
      (terms_lower : TermsFrontierLower termsState terms)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBlockRule, dot := 3 } : Item Cat Terminal).before [.token .block, .token (.lifetime lifetime), .token .lbrace] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermBlockRule, dot := 3 } : Item Cat Terminal) (by native_decide) .cterms [.token .rbrace] (by native_decide) [.token .block, .token (.lifetime lifetime), .token .lbrace] before_ok termsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime terms)

  | ctermLetMut_letMutInitialiser_descend
      {name : Name}
      {initialiserState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {initialiser : PartialTerm}
      (initialiser_lower : TermFrontierLower initialiserState initialiser)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermLetMutRule, dot := 4 } : Item Cat Terminal).before [.token .letKw, .token .mutKw, .token (.ident name), .token .assign] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermLetMutRule, dot := 4 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [.token .letKw, .token .mutKw, .token (.ident name), .token .assign] before_ok initialiserState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name initialiser)

  | ctermAssign_assignLhs_descend
      {lhsState : CheckableGrammar.FrontierState checkableGrammar .clval}
      {lhs : PartialLVal}
      (lhs_lower : LValFrontierLower lhsState lhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermAssignRule, dot := 0 } : Item Cat Terminal) (by native_decide) .clval [.token .assign, .cat .cterm] (by native_decide) [] before_ok lhsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs lhs)

  | ctermAssign_assignRhs_descend
      {lhsTree : Tree Tok} {lhs : LVal}
      (lhs_denotes : denoteLVal? lhsTree = some lhs)
      {rhsState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {rhs : PartialTerm}
      (rhs_lower : TermFrontierLower rhsState rhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermAssignRule, dot := 2 } : Item Cat Terminal).before [lhsTree, .token .assign] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermAssignRule, dot := 2 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [lhsTree, .token .assign] before_ok rhsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs rhs)

  | ctermBox_boxOperand_descend
      {operandState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {operand : PartialTerm}
      (operand_lower : TermFrontierLower operandState operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal).before [.token .box] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermBoxRule, dot := 1 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [.token .box] before_ok operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand operand)

  | ctermBorrowShared_borrowSharedOperand_descend
      {operandState : CheckableGrammar.FrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : LValFrontierLower operandState operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowSharedRule, dot := 1 } : Item Cat Terminal).before [.token .amp] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermBorrowSharedRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [.token .amp] before_ok operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand operand)

  | ctermBorrowMut_borrowMutOperand_descend
      {operandState : CheckableGrammar.FrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : LValFrontierLower operandState operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermBorrowMutRule, dot := 2 } : Item Cat Terminal).before [.token .amp, .token .mutKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermBorrowMutRule, dot := 2 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [.token .amp, .token .mutKw] before_ok operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand operand)

  | ctermMove_moveOperand_descend
      {operandState : CheckableGrammar.FrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : LValFrontierLower operandState operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermMoveRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermMoveRule, dot := 0 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [] before_ok operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand operand)

  | ctermCopy_copyOperand_descend
      {operandState : CheckableGrammar.FrontierState checkableGrammar .clval}
      {operand : PartialLVal}
      (operand_lower : LValFrontierLower operandState operand)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermCopyRule, dot := 1 } : Item Cat Terminal).before [.token .copyKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermCopyRule, dot := 1 } : Item Cat Terminal) (by native_decide) .clval [] (by native_decide) [.token .copyKw] before_ok operandState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand operand)

  | ctermEq_termPrefix_descend
      {lhsState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {lhs : PartialTerm}
      (lhs_lower : TermFrontierLower lhsState lhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 0 } : Item Cat Terminal).before [] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermEqRule, dot := 0 } : Item Cat Terminal) (by native_decide) .cterm [.token .eqEq, .cat .cterm] (by native_decide) [] before_ok lhsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix lhs)

  | ctermEq_eqRhs_descend
      {lhsTree : Tree Tok} {lhs : Term}
      (lhs_denotes : denoteTerm? lhsTree = some lhs)
      {rhsState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {rhs : PartialTerm}
      (rhs_lower : TermFrontierLower rhsState rhs)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermEqRule, dot := 2 } : Item Cat Terminal).before [lhsTree, .token .eqEq] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermEqRule, dot := 2 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [lhsTree, .token .eqEq] before_ok rhsState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs rhs)

  | ctermIte_iteCondition_descend
      {conditionState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {condition : PartialTerm}
      (condition_lower : TermFrontierLower conditionState condition)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 1 } : Item Cat Terminal).before [.token .ifKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermIteRule, dot := 1 } : Item Cat Terminal) (by native_decide) .cterm [.cat .cterm, .token .elseKw, .cat .cterm] (by native_decide) [.token .ifKw] before_ok conditionState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition condition)

  | ctermIte_iteTrueBranch_descend
      {conditionTree : Tree Tok} {condition : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      {trueBranchState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {trueBranch : PartialTerm}
      (trueBranch_lower : TermFrontierLower trueBranchState trueBranch)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 2 } : Item Cat Terminal).before [.token .ifKw, conditionTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermIteRule, dot := 2 } : Item Cat Terminal) (by native_decide) .cterm [.token .elseKw, .cat .cterm] (by native_decide) [.token .ifKw, conditionTree] before_ok trueBranchState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteTrueBranch condition trueBranch)

  | ctermIte_iteFalseBranch_descend
      {conditionTree : Tree Tok} {condition : Term}
      {trueBranchTree : Tree Tok} {trueBranch : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      (trueBranch_denotes : denoteTerm? trueBranchTree = some trueBranch)
      {falseBranchState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {falseBranch : PartialTerm}
      (falseBranch_lower : TermFrontierLower falseBranchState falseBranch)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermIteRule, dot := 4 } : Item Cat Terminal).before [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermIteRule, dot := 4 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw] before_ok falseBranchState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch falseBranch)

  | ctermWhile_whileCondition_descend
      {bodyLifetime : Lifetime}
      {conditionState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {condition : PartialTerm}
      (condition_lower : TermFrontierLower conditionState condition)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 2 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime)] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermWhileRule, dot := 2 } : Item Cat Terminal) (by native_decide) .cterm [.cat .cterm] (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime)] before_ok conditionState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime condition)

  | ctermWhile_whileBody_descend
      {bodyLifetime : Lifetime}
      {conditionTree : Tree Tok} {condition : Term}
      (condition_denotes : denoteTerm? conditionTree = some condition)
      {bodyState : CheckableGrammar.FrontierState checkableGrammar .cterm}
      {body : PartialTerm}
      (body_lower : TermFrontierLower bodyState body)
      {before_ok : CheckableGrammar.checkSeq checkableGrammar ({ rule := ctermWhileRule, dot := 3 } : Item Cat Terminal).before [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree] = Bool.true} :
      TermFrontierLower
        (CheckableGrammar.FrontierState.descend ({ rule := ctermWhileRule, dot := 3 } : Item Cat Terminal) (by native_decide) .cterm [] (by native_decide) [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree] before_ok bodyState)
        (_root_.ConservativeExtractor.Generated.PartialTerm.whileBody bodyLifetime condition body)


set_option linter.unusedSimpArgs false in
theorem lValsFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.FrontierState checkableGrammar .clvals}
    {frontier : PartialLVals} {completed : List LVal}
    (hlower : LValsFrontierLower state frontier)
    (hdenotes :
      denoteLVals? (state.rawCompletion defaults).tree = some completed) :
    CompletesLVals frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | clvalsEmpty_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalsEmptyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
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
theorem lValsTailFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.FrontierState checkableGrammar .clvalsTail}
    {frontier : PartialLVals} {completed : List LVal}
    (hlower : LValsTailFrontierLower state frontier)
    (hdenotes :
      denoteLValsTail? (state.rawCompletion defaults).tree = some completed) :
    CompletesLVals frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | clvalsTailEmpty_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalsTailEmptyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
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
theorem termsFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.FrontierState checkableGrammar .cterms}
    {frontier : PartialTerms} {completed : List Term}
    (hlower : TermsFrontierLower state frontier)
    (hdenotes :
      denoteTerms? (state.rawCompletion defaults).tree = some completed) :
    CompletesTerms frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermsEmpty_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermsEmptyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
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
theorem termsTailFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.FrontierState checkableGrammar .ctermsTail}
    {frontier : PartialTerms} {completed : List Term}
    (hlower : TermsTailFrontierLower state frontier)
    (hdenotes :
      denoteTermsTail? (state.rawCompletion defaults).tree = some completed) :
    CompletesTerms frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermsTailEmpty_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermsTailEmptyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
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
theorem lValsFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.FrontierState checkableGrammar .clvals}
    {frontier : PartialLVals} {tree : Tree Tok} {completed : List LVal}
    (hlower : LValsFrontierLower state frontier)
    (hcomplete : CheckableGrammar.FrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesLVals tree completed) :
    CompletesLVals frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | clvalsEmpty_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
theorem lValsTailFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.FrontierState checkableGrammar .clvalsTail}
    {frontier : PartialLVals} {tree : Tree Tok} {completed : List LVal}
    (hlower : LValsTailFrontierLower state frontier)
    (hcomplete : CheckableGrammar.FrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesLValsTail tree completed) :
    CompletesLVals frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | clvalsTailEmpty_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
theorem termsFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.FrontierState checkableGrammar .cterms}
    {frontier : PartialTerms} {tree : Tree Tok} {completed : List Term}
    (hlower : TermsFrontierLower state frontier)
    (hcomplete : CheckableGrammar.FrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesTerms tree completed) :
    CompletesTerms frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermsEmpty_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
theorem termsTailFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.FrontierState checkableGrammar .ctermsTail}
    {frontier : PartialTerms} {tree : Tree Tok} {completed : List Term}
    (hlower : TermsTailFrontierLower state frontier)
    (hcomplete : CheckableGrammar.FrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesTermsTail tree completed) :
    CompletesTerms frontier completed := by
  cases hlower with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermsTailEmpty_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
theorem tyFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.FrontierState checkableGrammar .cty}
    {frontier : PartialTy} {completed : Ty}
    (hlower : TyFrontierLower state frontier)
    (hdenotes :
      denoteTy? (state.rawCompletion defaults).tree = some completed) :
    CompletesTy frontier completed := by
  induction hlower generalizing completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyUnit_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyUnitRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyInt_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyIntRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyBool_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoolRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyUnit_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyUnitRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyInt_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyIntRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBool_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoolRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBorrowShared_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowShared_dot2_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowShared_dot4_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBorrowMut_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot2_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot3_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot5_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBox_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBorrowShared_borrowSharedTargets_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBorrowMut_borrowMutTargets_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done
  | ctyBox_boxElement_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyBorrowShared_borrowSharedStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedStart
  | ctyBorrowMut_borrowSharedStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowSharedStart
  | ctyBox_boxStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxStart
  | ctyBorrowShared_borrowSharedTargets_descend targets_lower =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨targetsCompleted, targets_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets (lValsFrontierLower_completes_of_rawDenotes targets_lower targets_denotes)
  | ctyBorrowMut_borrowMutTargets_descend targets_lower =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨targetsCompleted, targets_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets (lValsFrontierLower_completes_of_rawDenotes targets_lower targets_denotes)
  | ctyBox_boxElement_descend element_lower element_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctyBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨elementCompleted, element_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement (element_ih element_denotes)

set_option linter.unusedSimpArgs false in
theorem lValFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.FrontierState checkableGrammar .clval}
    {frontier : PartialLVal} {completed : LVal}
    (hlower : LValFrontierLower state frontier)
    (hdenotes :
      denoteLVal? (state.rawCompletion defaults).tree = some completed) :
    CompletesLVal frontier completed := by
  induction hlower generalizing completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | clvalVar_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalVarRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | clvalDeref_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalDerefRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | clvalVar_varX_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalVarRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX _root_.ConservativeExtractor.Generated.CompletesName.done
  | clvalDeref_derefOperand_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalDerefRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | clvalDeref_derefStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalDerefRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefStart
  | clvalDeref_derefOperand_descend operand_lower operand_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, clvalDerefRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand (operand_ih operand_denotes)

set_option linter.unusedSimpArgs false in
theorem termFrontierLower_completes_of_rawDenotes
    {state : CheckableGrammar.FrontierState checkableGrammar .cterm}
    {frontier : PartialTerm} {completed : Term}
    (hlower : TermFrontierLower state frontier)
    (hdenotes :
      denoteTerm? (state.rawCompletion defaults).tree = some completed) :
    CompletesTerm frontier completed := by
  induction hlower generalizing completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermUnit_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermUnitRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermTrue_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermTrueRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermFalse_done_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermFalseRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermUnit_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermUnitRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermInt_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIntRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermTrue_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermTrueRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermFalse_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermFalseRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBlock_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermBlock_dot2_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot3_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot5_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermLetMut_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot2_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot4_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermAssign_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermAssign_dot2_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBox_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBorrowShared_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermBorrowMut_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermBorrowMut_dot2_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermMove_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermMoveRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermCopy_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermCopyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermEq_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermEq_dot2_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot4_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermWhile_dot0_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermWhile_dot2_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermInt_intN_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIntRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermInt_intN
  | ctermBlock_blockTerms_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermLetMut_letMutName_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.done
  | ctermLetMut_letMutInitialiser_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermAssign_assignLhs_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermAssign_assignRhs_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBox_boxOperand_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBorrowShared_borrowSharedOperand_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermBorrowMut_borrowMutOperand_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermMove_moveOperand_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermMoveRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermCopy_copyOperand_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermCopyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermEq_termPrefix_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermEq_eqRhs_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteCondition_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteTrueBranch_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteFalseBranch_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermWhile_whileCondition_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermWhile_whileBody_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBlock_blockStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermLetMut_letMutStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutStart
  | ctermBox_boxStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxStart
  | ctermBorrowShared_borrowSharedStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedStart
  | ctermBorrowMut_borrowSharedStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowSharedStart
  | ctermCopy_copyStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermCopyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyStart
  | ctermIte_iteStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteStart
  | ctermWhile_whileStart_boundary =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermBlock_blockTerms_descend terms_lower =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBlockRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨termsCompleted, terms_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms (termsFrontierLower_completes_of_rawDenotes terms_lower terms_denotes)
  | ctermLetMut_letMutInitialiser_descend initialiser_lower initialiser_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermLetMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨initialiserCompleted, initialiser_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser (initialiser_ih initialiser_denotes)
  | ctermAssign_assignLhs_descend lhs_lower =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨lhsCompleted, lhs_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs (lValFrontierLower_completes_of_rawDenotes lhs_lower lhs_denotes)
  | ctermAssign_assignRhs_descend lhs_denotes rhs_lower rhs_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermAssignRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨rhsCompleted, rhs_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs (rhs_ih rhs_denotes)
  | ctermBox_boxOperand_descend operand_lower operand_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBoxRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand (operand_ih operand_denotes)
  | ctermBorrowShared_borrowSharedOperand_descend operand_lower =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowSharedRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand (lValFrontierLower_completes_of_rawDenotes operand_lower operand_denotes)
  | ctermBorrowMut_borrowMutOperand_descend operand_lower =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermBorrowMutRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand (lValFrontierLower_completes_of_rawDenotes operand_lower operand_denotes)
  | ctermMove_moveOperand_descend operand_lower =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermMoveRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand (lValFrontierLower_completes_of_rawDenotes operand_lower operand_denotes)
  | ctermCopy_copyOperand_descend operand_lower =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermCopyRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨operandCompleted, operand_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand (lValFrontierLower_completes_of_rawDenotes operand_lower operand_denotes)
  | ctermEq_termPrefix_descend lhs_lower lhs_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨lhsCompleted, lhs_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix (lhs_ih lhs_denotes)
  | ctermEq_eqRhs_descend lhs_denotes rhs_lower rhs_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermEqRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨rhsCompleted, rhs_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs (rhs_ih rhs_denotes)
  | ctermIte_iteCondition_descend condition_lower condition_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨conditionCompleted, condition_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition (condition_ih condition_denotes)
  | ctermIte_iteTrueBranch_descend condition_denotes trueBranch_lower trueBranch_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨trueBranchCompleted, trueBranch_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch (trueBranch_ih trueBranch_denotes)
  | ctermIte_iteFalseBranch_descend condition_denotes trueBranch_denotes falseBranch_lower falseBranch_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermIteRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨falseBranchCompleted, falseBranch_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch (falseBranch_ih falseBranch_denotes)
  | ctermWhile_whileCondition_descend condition_lower condition_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨conditionCompleted, condition_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition (condition_ih condition_denotes)
  | ctermWhile_whileBody_descend condition_denotes body_lower body_ih =>
      simp_all [CheckableGrammar.FrontierState.rawCompletion, CheckableGrammar.Defaults.completeBoundaryRaw, defaults, ctermWhileRule, Item.after, CheckableGrammar.Defaults.defaultSeq, CheckableGrammar.Defaults.defaultSymTree, defaultTree, defaultToken, denoteTerm?, denoteLVal?, denoteTerms?, denoteTermsTail?, denoteLVals?, denoteLValsTail?, denoteTy?]
      simp only [Option.bind_eq_some_iff] at hdenotes
      obtain ⟨bodyCompleted, body_denotes, hcompleted⟩ := hdenotes
      simp at hcompleted
      subst completed
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody (body_ih body_denotes)

set_option linter.unusedSimpArgs false in
theorem tyFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.FrontierState checkableGrammar .cty}
    {frontier : PartialTy} {tree : Tree Tok} {completed : Ty}
    (hlower : TyFrontierLower state frontier)
    (hcomplete : CheckableGrammar.FrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesTy tree completed) :
    CompletesTy frontier completed := by
  induction hlower generalizing tree completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyUnit_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyUnitRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyInt_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyIntRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.done
  | ctyBool_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowShared_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowShared_dot4_boundary targets_denotes =>
      rename_i stateTargetsTree stateTargets before_ok
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot3_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets
        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff
  | ctyBorrowMut_dot5_boundary targets_denotes =>
      rename_i stateTargetsTree stateTargets before_ok
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement
        _root_.ConservativeExtractor.Generated.CompletesTy.cutoff
  | ctyBorrowShared_borrowSharedTargets_boundary targets_denotes =>
      rename_i stateTargetsTree stateTargets before_ok
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
      rename_i stateTargetsTree stateTargets before_ok
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
      rename_i stateElementTree stateElement before_ok
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
  | ctyBorrowShared_borrowSharedStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedStart
  | ctyBorrowMut_borrowSharedStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowSharedStart
  | ctyBox_boxStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctyBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxStart
  | ctyBorrowShared_borrowSharedTargets_descend targets_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree
      rename_i actualTargetsTree actualTargets htargets
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets
        (lValsFrontierLower_completes_of_stateCompletes
          targets_lower hchild htargets)
  | ctyBorrowMut_borrowMutTargets_descend targets_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctyBorrowMutRule] at htree
      rename_i actualTargetsTree actualTargets htargets
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets
        (lValsFrontierLower_completes_of_stateCompletes
          targets_lower hchild htargets)
  | ctyBox_boxElement_descend element_lower element_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctyBoxRule] at htree
      rename_i actualElementTree actualElement helement
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement
        (element_ih hchild helement)

set_option linter.unusedSimpArgs false in
theorem lValFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.FrontierState checkableGrammar .clval}
    {frontier : PartialLVal} {tree : Tree Tok} {completed : LVal}
    (hlower : LValFrontierLower state frontier)
    (hcomplete : CheckableGrammar.FrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesLVal tree completed) :
    CompletesLVal frontier completed := by
  induction hlower generalizing tree completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | clvalVar_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalVar =>
          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX
            _root_.ConservativeExtractor.Generated.CompletesName.cutoff
      | clvalDeref hoperand =>
          simp [clvalVarRule] at htree
  | clvalDeref_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalVar =>
          simp [clvalDerefRule] at htree
      | clvalDeref hoperand =>
          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand
            _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | clvalVar_varX_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
      rename_i stateOperandTree stateOperand before_ok
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes with
      | clvalVar =>
          simp [clvalDerefRule] at htree
      | clvalDeref hoperand =>
          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefStart
  | clvalDeref_derefOperand_descend operand_lower operand_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
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
theorem termFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.FrontierState checkableGrammar .cterm}
    {frontier : PartialTerm} {tree : Tree Tok} {completed : Term}
    (hlower : TermFrontierLower state frontier)
    (hcomplete : CheckableGrammar.FrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesTerm tree completed) :
    CompletesTerm frontier completed := by
  induction hlower generalizing tree completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermUnit_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermUnitRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermTrue_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermTrueRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermFalse_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermBlock_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, _⟩
      subst actualLifetime
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot3_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, _⟩
      subst actualLifetime
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot5_boundary terms_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName
        _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName
        _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot4_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, _⟩
      subst actualName
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermAssign_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermAssign_dot2_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBox_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBorrowShared_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermBorrowMut_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermBorrowMut_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermMove_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermCopy_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermEq_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermEq_dot2_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot4_boundary condition_denotes trueBranch_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermWhile_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, _⟩
      subst actualBodyLifetime
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermInt_intN_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIntRule] at htree
      rename_i actualN
      rcases htree with ⟨hnEq, _⟩
      subst actualN
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermInt_intN
  | ctermBlock_blockTerms_boundary terms_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, _⟩
      subst actualName
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName
        _root_.ConservativeExtractor.Generated.CompletesName.done
  | ctermLetMut_letMutInitialiser_boundary initialiser_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermAssign_assignRhs_boundary lhs_denotes rhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := term_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBorrowShared_borrowSharedOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermBorrowMut_borrowMutOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermMove_moveOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermCopy_copyOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermEq_termPrefix_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermEq_eqRhs_boundary lhs_denotes rhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermLetMut_letMutStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutStart
  | ctermBox_boxStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxStart
  | ctermBorrowShared_borrowSharedStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedStart
  | ctermBorrowMut_borrowSharedStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowSharedStart
  | ctermCopy_copyStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyStart
  | ctermIte_iteStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteStart
  | ctermWhile_whileStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermBlock_blockTerms_descend terms_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, hchildEq, _⟩
      subst actualLifetime
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        (termsFrontierLower_completes_of_stateCompletes
          terms_lower hchild hterms)
  | ctermLetMut_letMutInitialiser_descend initialiser_lower initialiser_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, hchildEq, _⟩
      subst actualName
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser
        (initialiser_ih hchild hinitialiser)
  | ctermAssign_assignLhs_descend lhs_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
        (lValFrontierLower_completes_of_stateCompletes
          lhs_lower hchild hlhs)
  | ctermAssign_assignRhs_descend lhs_denotes rhs_lower rhs_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand
        (operand_ih hchild hoperand)
  | ctermBorrowShared_borrowSharedOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand
        (lValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermBorrowMut_borrowMutOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        (lValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermMove_moveOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
        (lValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermCopy_copyOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand
        (lValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermEq_termPrefix_descend lhs_lower lhs_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
        (lhs_ih hchild hlhs)
  | ctermEq_eqRhs_descend lhs_denotes rhs_lower rhs_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition
        (condition_ih hchild hcondition)
  | ctermIte_iteTrueBranch_descend condition_denotes trueBranch_lower trueBranch_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
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
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, hchildEq, _⟩
      subst actualBodyLifetime
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition
        (condition_ih hchild hcondition)
  | ctermWhile_whileBody_descend condition_denotes body_lower body_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.FrontierStateCompletes.descend_inv hcomplete
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

theorem lValsFrontierLower_exists
    (state : CheckableGrammar.FrontierState checkableGrammar .clvals) :
    ∃ frontier : PartialLVals, LValsFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialLVals.cutoff,
    LValsFrontierLower.fallback⟩

theorem lValsTailFrontierLower_exists
    (state : CheckableGrammar.FrontierState checkableGrammar .clvalsTail) :
    ∃ frontier : PartialLVals, LValsTailFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialLVals.cutoff,
    LValsTailFrontierLower.fallback⟩

theorem termsFrontierLower_exists
    (state : CheckableGrammar.FrontierState checkableGrammar .cterms) :
    ∃ frontier : PartialTerms, TermsFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialTerms.cutoff,
    TermsFrontierLower.fallback⟩

theorem termsTailFrontierLower_exists
    (state : CheckableGrammar.FrontierState checkableGrammar .ctermsTail) :
    ∃ frontier : PartialTerms, TermsTailFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialTerms.cutoff,
    TermsTailFrontierLower.fallback⟩

theorem tyFrontierLower_exists
    (state : CheckableGrammar.FrontierState checkableGrammar .cty) :
    ∃ frontier : PartialTy, TyFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialTy.cutoff,
    TyFrontierLower.fallback⟩

theorem lValFrontierLower_exists
    (state : CheckableGrammar.FrontierState checkableGrammar .clval) :
    ∃ frontier : PartialLVal, LValFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialLVal.cutoff,
    LValFrontierLower.fallback⟩

theorem termFrontierLower_exists
    (state : CheckableGrammar.FrontierState checkableGrammar .cterm) :
    ∃ frontier : PartialTerm, TermFrontierLower state frontier := by
  exact ⟨_root_.ConservativeExtractor.Generated.PartialTerm.cutoff,
    TermFrontierLower.fallback⟩

set_option linter.unusedSimpArgs false in
theorem tyFrontierLower_ctyBorrowSharedTargets_boundary_exists
    {targetsTree : Tree Tok}
    {before_ok :
      CheckableGrammar.checkSeq checkableGrammar
        ({ rule := ctyBorrowSharedRule, dot := 3 } : Item Cat Terminal).before
        [.token .amp, .token .lbrack, targetsTree] = Bool.true} :
    ∃ targets : List LVal,
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary
          ({ rule := ctyBorrowSharedRule, dot := 3 } : Item Cat Terminal)
          (by native_decide) [.token .amp, .token .lbrack, targetsTree]
          before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets
          (_root_.ConservativeExtractor.Generated.PartialLVals.done targets)) := by
  have htargets :
      CheckableGrammar.checkTree checkableGrammar .clvals targetsTree =
        Bool.true := by
    simpa [ctyBorrowSharedRule, Item.before, CheckableGrammar.checkSeq,
      checkableGrammar, acceptsBool] using before_ok
  obtain ⟨targets, htargetsDenote⟩ :=
    checkedLValsTree_denote_exists htargets
  exact ⟨targets,
    TyFrontierLower.ctyBorrowShared_borrowSharedTargets_boundary
      htargetsDenote⟩

set_option linter.unusedSimpArgs false in
theorem tyFrontierLower_ctyBorrowMutTargets_boundary_exists
    {targetsTree : Tree Tok}
    {before_ok :
      CheckableGrammar.checkSeq checkableGrammar
        ({ rule := ctyBorrowMutRule, dot := 4 } : Item Cat Terminal).before
        [.token .amp, .token .mutKw, .token .lbrack, targetsTree] = Bool.true} :
    ∃ targets : List LVal,
      TyFrontierLower
        (CheckableGrammar.FrontierState.boundary
          ({ rule := ctyBorrowMutRule, dot := 4 } : Item Cat Terminal)
          (by native_decide) [.token .amp, .token .mutKw, .token .lbrack, targetsTree]
          before_ok)
        (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets
          (_root_.ConservativeExtractor.Generated.PartialLVals.done targets)) := by
  have htargets :
      CheckableGrammar.checkTree checkableGrammar .clvals targetsTree =
        Bool.true := by
    simpa [ctyBorrowMutRule, Item.before, CheckableGrammar.checkSeq,
      checkableGrammar, acceptsBool] using before_ok
  obtain ⟨targets, htargetsDenote⟩ :=
    checkedLValsTree_denote_exists htargets
  exact ⟨targets,
    TyFrontierLower.ctyBorrowMut_borrowMutTargets_boundary
      htargetsDenote⟩

theorem ctyUnit_done_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxSemantics.ctyUnit))
      (SyntaxSemantics.ctyUnit) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.done

theorem ctyInt_done_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxSemantics.ctyInt))
      (SyntaxSemantics.ctyInt) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.done

theorem ctyBool_done_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.done (SyntaxSemantics.ctyBool))
      (SyntaxSemantics.ctyBool) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.done

theorem ctyUnit_dot0_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)
      (SyntaxSemantics.ctyUnit) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff

theorem ctyInt_dot0_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)
      (SyntaxSemantics.ctyInt) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff

theorem ctyBool_dot0_boundary_completes :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.cutoff)
      (SyntaxSemantics.ctyBool) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff

theorem ctyBorrowShared_dot0_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)
      (SyntaxSemantics.ctyBorrowShared targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff

theorem ctyBorrowShared_dot2_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)
      (SyntaxSemantics.ctyBorrowShared targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff

theorem ctyBorrowShared_dot4_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))
      (SyntaxSemantics.ctyBorrowShared targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done

theorem ctyBorrowMut_dot0_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)
      (SyntaxSemantics.ctyBorrowMut targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff

theorem ctyBorrowMut_dot2_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)
      (SyntaxSemantics.ctyBorrowMut targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff

theorem ctyBorrowMut_dot3_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets _root_.ConservativeExtractor.Generated.PartialLVals.cutoff)
      (SyntaxSemantics.ctyBorrowMut targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff

theorem ctyBorrowMut_dot5_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))
      (SyntaxSemantics.ctyBorrowMut targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done

theorem ctyBox_dot0_boundary_completes {element : Ty} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.boxElement _root_.ConservativeExtractor.Generated.PartialTy.cutoff)
      (SyntaxSemantics.ctyBox element) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement _root_.ConservativeExtractor.Generated.CompletesTy.cutoff

theorem ctyBorrowShared_borrowSharedTargets_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))
      (SyntaxSemantics.ctyBorrowShared targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done

theorem ctyBorrowMut_borrowMutTargets_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets (_root_.ConservativeExtractor.Generated.PartialLVals.done targets))
      (SyntaxSemantics.ctyBorrowMut targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets _root_.ConservativeExtractor.Generated.CompletesLVals.done

theorem ctyBox_boxElement_boundary_completes {element : Ty} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.boxElement (_root_.ConservativeExtractor.Generated.PartialTy.done element))
      (SyntaxSemantics.ctyBox element) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement _root_.ConservativeExtractor.Generated.CompletesTy.done

theorem ctyBorrowShared_borrowSharedStart_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedStart)
      (SyntaxSemantics.ctyBorrowShared targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedStart

theorem ctyBorrowMut_borrowSharedStart_boundary_completes {targets : List LVal} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedStart)
      (SyntaxSemantics.ctyBorrowMut targets) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowSharedStart

theorem ctyBox_boxStart_boundary_completes {element : Ty} :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.boxStart)
      (SyntaxSemantics.ctyBox element) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxStart

theorem ctyBorrowShared_borrowSharedTargets_descend_completes {targets : PartialLVals} {targets' : List LVal}
    (targets_completes : _root_.ConservativeExtractor.Generated.CompletesLVals targets targets') :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowSharedTargets targets)
      (SyntaxSemantics.ctyBorrowShared targets') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets targets_completes

theorem ctyBorrowMut_borrowMutTargets_descend_completes {targets : PartialLVals} {targets' : List LVal}
    (targets_completes : _root_.ConservativeExtractor.Generated.CompletesLVals targets targets') :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.borrowMutTargets targets)
      (SyntaxSemantics.ctyBorrowMut targets') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets targets_completes

theorem ctyBox_boxElement_descend_completes {element : PartialTy} {element' : Ty}
    (element_completes : _root_.ConservativeExtractor.Generated.CompletesTy element element') :
    CompletesTy (_root_.ConservativeExtractor.Generated.PartialTy.boxElement element)
      (SyntaxSemantics.ctyBox element') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement element_completes

theorem clvalVar_dot0_boundary_completes {x : Name} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.varX _root_.ConservativeExtractor.Generated.PartialName.cutoff)
      (SyntaxSemantics.clvalVar x) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX _root_.ConservativeExtractor.Generated.CompletesName.cutoff

theorem clvalDeref_dot0_boundary_completes {operand : LVal} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxSemantics.clvalDeref operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem clvalVar_varX_boundary_completes {x : Name} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.varX (_root_.ConservativeExtractor.Generated.PartialName.done x))
      (SyntaxSemantics.clvalVar x) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX _root_.ConservativeExtractor.Generated.CompletesName.done

theorem clvalDeref_derefOperand_boundary_completes {operand : LVal} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxSemantics.clvalDeref operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem clvalDeref_derefStart_boundary_completes {operand : LVal} :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.derefStart)
      (SyntaxSemantics.clvalDeref operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefStart

theorem clvalDeref_derefOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesLVal (_root_.ConservativeExtractor.Generated.PartialLVal.derefOperand operand)
      (SyntaxSemantics.clvalDeref operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand operand_completes

theorem ctermUnit_done_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxSemantics.ctermUnit))
      (SyntaxSemantics.ctermUnit) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermTrue_done_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxSemantics.ctermTrue))
      (SyntaxSemantics.ctermTrue) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermFalse_done_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.done (SyntaxSemantics.ctermFalse))
      (SyntaxSemantics.ctermFalse) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermUnit_dot0_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermUnit) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermInt_dot0_boundary_completes {n : Int} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermInt n) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermTrue_dot0_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermTrue) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermFalse_dot0_boundary_completes :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermFalse) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermBlock_dot0_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockStart)
      (SyntaxSemantics.ctermBlock lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart

theorem ctermBlock_dot2_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime _root_.ConservativeExtractor.Generated.PartialTerms.cutoff)
      (SyntaxSemantics.ctermBlock lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff

theorem ctermBlock_dot3_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime _root_.ConservativeExtractor.Generated.PartialTerms.cutoff)
      (SyntaxSemantics.ctermBlock lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff

theorem ctermBlock_dot5_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime (_root_.ConservativeExtractor.Generated.PartialTerms.done terms))
      (SyntaxSemantics.ctermBlock lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.done

theorem ctermLetMut_dot0_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName _root_.ConservativeExtractor.Generated.PartialName.cutoff)
      (SyntaxSemantics.ctermLetMut name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.cutoff

theorem ctermLetMut_dot2_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName _root_.ConservativeExtractor.Generated.PartialName.cutoff)
      (SyntaxSemantics.ctermLetMut name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.cutoff

theorem ctermLetMut_dot4_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermLetMut name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermAssign_dot0_boundary_completes {lhs : LVal} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxSemantics.ctermAssign lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermAssign_dot2_boundary_completes {lhs : LVal} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermAssign lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermBox_dot0_boundary_completes {operand : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermBox operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermBorrowShared_dot0_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxSemantics.ctermBorrowShared operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermBorrowMut_dot0_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxSemantics.ctermBorrowMut operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermBorrowMut_dot2_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxSemantics.ctermBorrowMut operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermMove_dot0_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxSemantics.ctermMove operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermCopy_dot0_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand _root_.ConservativeExtractor.Generated.PartialLVal.cutoff)
      (SyntaxSemantics.ctermCopy operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff

theorem ctermEq_dot0_boundary_completes {lhs : Term} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermEq lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermEq_dot2_boundary_completes {lhs : Term} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermEq lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermIte_dot0_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermIte condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermIte_dot4_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermIte condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermWhile_dot0_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileStart)
      (SyntaxSemantics.ctermWhile bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart

theorem ctermWhile_dot2_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime _root_.ConservativeExtractor.Generated.PartialTerm.cutoff)
      (SyntaxSemantics.ctermWhile bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff

theorem ctermInt_intN_boundary_completes {n : Int} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.intN n)
      (SyntaxSemantics.ctermInt n) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermInt_intN

theorem ctermBlock_blockTerms_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime (_root_.ConservativeExtractor.Generated.PartialTerms.done terms))
      (SyntaxSemantics.ctermBlock lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms _root_.ConservativeExtractor.Generated.CompletesTerms.done

theorem ctermLetMut_letMutName_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutName (_root_.ConservativeExtractor.Generated.PartialName.done name))
      (SyntaxSemantics.ctermLetMut name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName _root_.ConservativeExtractor.Generated.CompletesName.done

theorem ctermLetMut_letMutInitialiser_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name (_root_.ConservativeExtractor.Generated.PartialTerm.done initialiser))
      (SyntaxSemantics.ctermLetMut name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermAssign_assignLhs_boundary_completes {lhs : LVal} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs (_root_.ConservativeExtractor.Generated.PartialLVal.done lhs))
      (SyntaxSemantics.ctermAssign lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermAssign_assignRhs_boundary_completes {lhs : LVal} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs (_root_.ConservativeExtractor.Generated.PartialTerm.done rhs))
      (SyntaxSemantics.ctermAssign lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermBox_boxOperand_boundary_completes {operand : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand (_root_.ConservativeExtractor.Generated.PartialTerm.done operand))
      (SyntaxSemantics.ctermBox operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermBorrowShared_borrowSharedOperand_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxSemantics.ctermBorrowShared operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermBorrowMut_borrowMutOperand_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxSemantics.ctermBorrowMut operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermMove_moveOperand_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxSemantics.ctermMove operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermCopy_copyOperand_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand (_root_.ConservativeExtractor.Generated.PartialLVal.done operand))
      (SyntaxSemantics.ctermCopy operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand _root_.ConservativeExtractor.Generated.CompletesLVal.done

theorem ctermEq_termPrefix_boundary_completes {lhs : Term} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix (_root_.ConservativeExtractor.Generated.PartialTerm.done lhs))
      (SyntaxSemantics.ctermEq lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermEq_eqRhs_boundary_completes {lhs : Term} {rhs : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs (_root_.ConservativeExtractor.Generated.PartialTerm.done rhs))
      (SyntaxSemantics.ctermEq lhs rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermIte_iteCondition_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition (_root_.ConservativeExtractor.Generated.PartialTerm.done condition))
      (SyntaxSemantics.ctermIte condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermIte_iteTrueBranch_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteTrueBranch condition (_root_.ConservativeExtractor.Generated.PartialTerm.done trueBranch))
      (SyntaxSemantics.ctermIte condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermIte_iteFalseBranch_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch (_root_.ConservativeExtractor.Generated.PartialTerm.done falseBranch))
      (SyntaxSemantics.ctermIte condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermWhile_whileCondition_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime (_root_.ConservativeExtractor.Generated.PartialTerm.done condition))
      (SyntaxSemantics.ctermWhile bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermWhile_whileBody_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileBody bodyLifetime condition (_root_.ConservativeExtractor.Generated.PartialTerm.done body))
      (SyntaxSemantics.ctermWhile bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody _root_.ConservativeExtractor.Generated.CompletesTerm.done

theorem ctermBlock_blockStart_boundary_completes {lifetime : Lifetime} {terms : List Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockStart)
      (SyntaxSemantics.ctermBlock lifetime terms) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart

theorem ctermLetMut_letMutStart_boundary_completes {name : Name} {initialiser : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutStart)
      (SyntaxSemantics.ctermLetMut name initialiser) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutStart

theorem ctermBox_boxStart_boundary_completes {operand : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.boxStart)
      (SyntaxSemantics.ctermBox operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxStart

theorem ctermBorrowShared_borrowSharedStart_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedStart)
      (SyntaxSemantics.ctermBorrowShared operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedStart

theorem ctermBorrowMut_borrowSharedStart_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedStart)
      (SyntaxSemantics.ctermBorrowMut operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowSharedStart

theorem ctermCopy_copyStart_boundary_completes {operand : LVal} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.copyStart)
      (SyntaxSemantics.ctermCopy operand) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyStart

theorem ctermIte_iteStart_boundary_completes {condition : Term} {trueBranch : Term} {falseBranch : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteStart)
      (SyntaxSemantics.ctermIte condition trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteStart

theorem ctermWhile_whileStart_boundary_completes {bodyLifetime : Lifetime} {condition : Term} {body : Term} :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileStart)
      (SyntaxSemantics.ctermWhile bodyLifetime condition body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart

theorem ctermBlock_blockTerms_descend_completes {lifetime : Lifetime} {terms : PartialTerms} {terms' : List Term}
    (terms_completes : _root_.ConservativeExtractor.Generated.CompletesTerms terms terms') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.blockTerms lifetime terms)
      (SyntaxSemantics.ctermBlock lifetime terms') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms terms_completes

theorem ctermLetMut_letMutInitialiser_descend_completes {name : Name} {initialiser : PartialTerm} {initialiser' : Term}
    (initialiser_completes : _root_.ConservativeExtractor.Generated.CompletesTerm initialiser initialiser') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.letMutInitialiser name initialiser)
      (SyntaxSemantics.ctermLetMut name initialiser') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser initialiser_completes

theorem ctermAssign_assignLhs_descend_completes {lhs : PartialLVal} {lhs' : LVal} {rhs : Term}
    (lhs_completes : _root_.ConservativeExtractor.Generated.CompletesLVal lhs lhs') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignLhs lhs)
      (SyntaxSemantics.ctermAssign lhs' rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs lhs_completes

theorem ctermAssign_assignRhs_descend_completes {lhs : LVal} {rhs : PartialTerm} {rhs' : Term}
    (rhs_completes : _root_.ConservativeExtractor.Generated.CompletesTerm rhs rhs') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.assignRhs lhs rhs)
      (SyntaxSemantics.ctermAssign lhs rhs') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs rhs_completes

theorem ctermBox_boxOperand_descend_completes {operand : PartialTerm} {operand' : Term}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesTerm operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.boxOperand operand)
      (SyntaxSemantics.ctermBox operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand operand_completes

theorem ctermBorrowShared_borrowSharedOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowSharedOperand operand)
      (SyntaxSemantics.ctermBorrowShared operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand operand_completes

theorem ctermBorrowMut_borrowMutOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.borrowMutOperand operand)
      (SyntaxSemantics.ctermBorrowMut operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand operand_completes

theorem ctermMove_moveOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.moveOperand operand)
      (SyntaxSemantics.ctermMove operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand operand_completes

theorem ctermCopy_copyOperand_descend_completes {operand : PartialLVal} {operand' : LVal}
    (operand_completes : _root_.ConservativeExtractor.Generated.CompletesLVal operand operand') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.copyOperand operand)
      (SyntaxSemantics.ctermCopy operand') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand operand_completes

theorem ctermEq_termPrefix_descend_completes {lhs : PartialTerm} {lhs' : Term} {rhs : Term}
    (lhs_completes : _root_.ConservativeExtractor.Generated.CompletesTerm lhs lhs') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.termPrefix lhs)
      (SyntaxSemantics.ctermEq lhs' rhs) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix lhs_completes

theorem ctermEq_eqRhs_descend_completes {lhs : Term} {rhs : PartialTerm} {rhs' : Term}
    (rhs_completes : _root_.ConservativeExtractor.Generated.CompletesTerm rhs rhs') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.eqRhs lhs rhs)
      (SyntaxSemantics.ctermEq lhs rhs') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs rhs_completes

theorem ctermIte_iteCondition_descend_completes {condition : PartialTerm} {condition' : Term} {trueBranch : Term} {falseBranch : Term}
    (condition_completes : _root_.ConservativeExtractor.Generated.CompletesTerm condition condition') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteCondition condition)
      (SyntaxSemantics.ctermIte condition' trueBranch falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition condition_completes

theorem ctermIte_iteTrueBranch_descend_completes {condition : Term} {trueBranch : PartialTerm} {trueBranch' : Term} {falseBranch : Term}
    (trueBranch_completes : _root_.ConservativeExtractor.Generated.CompletesTerm trueBranch trueBranch') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteTrueBranch condition trueBranch)
      (SyntaxSemantics.ctermIte condition trueBranch' falseBranch) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch trueBranch_completes

theorem ctermIte_iteFalseBranch_descend_completes {condition : Term} {trueBranch : Term} {falseBranch : PartialTerm} {falseBranch' : Term}
    (falseBranch_completes : _root_.ConservativeExtractor.Generated.CompletesTerm falseBranch falseBranch') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.iteFalseBranch condition trueBranch falseBranch)
      (SyntaxSemantics.ctermIte condition trueBranch falseBranch') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch falseBranch_completes

theorem ctermWhile_whileCondition_descend_completes {bodyLifetime : Lifetime} {condition : PartialTerm} {condition' : Term} {body : Term}
    (condition_completes : _root_.ConservativeExtractor.Generated.CompletesTerm condition condition') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileCondition bodyLifetime condition)
      (SyntaxSemantics.ctermWhile bodyLifetime condition' body) := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition condition_completes

theorem ctermWhile_whileBody_descend_completes {bodyLifetime : Lifetime} {condition : Term} {body : PartialTerm} {body' : Term}
    (body_completes : _root_.ConservativeExtractor.Generated.CompletesTerm body body') :
    CompletesTerm (_root_.ConservativeExtractor.Generated.PartialTerm.whileBody bodyLifetime condition body)
      (SyntaxSemantics.ctermWhile bodyLifetime condition body') := by
  exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody body_completes

end GeneratedFrontierLower
end FwRust
end GrammarFrontier
end ConservativeExtractor
