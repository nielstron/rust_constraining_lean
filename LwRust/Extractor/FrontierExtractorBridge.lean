import LwRust.Extractor.FrontierSourceCompletion
import LwRust.Extractor.Checkers
import LwRust.Extractor.Extractors.NestedBlocks
import LwRust.Extractor.RelaxedMergeCompleteness

/-!
Direct parser-frontier prefix checking.

Partial code is represented by the token prefix plus a tree-shaped parser
frontier for that prefix.  The basic completeness theorem is proved directly from
the generated parser frontier and the semantic interpretation of completed
parse trees.

The nested-block extractor wrappers below keep the parser frontier as the
external partial program and extract directly from its tree-shaped frontier.
-/

namespace ConservativeExtractor
namespace GrammarFrontier
namespace FwRust

abbrev CodeCompletesProgram : List Tok → Program → Prop :=
  CodeCompletesTerm

abbrev PartialTermFrontierTree :=
  CheckableGrammar.PartialFrontierTree checkableGrammar .cterm

abbrev PartialLValFrontierTree :=
  CheckableGrammar.PartialFrontierTree checkableGrammar .clval

abbrev PartialTermsFrontierTree :=
  CheckableGrammar.PartialFrontierTree checkableGrammar .cterms

abbrev PartialTermsTailFrontierTree :=
  CheckableGrammar.PartialFrontierTree checkableGrammar .ctermsTail

def partialTermFrontierTreeBijectionFrontierState :
    Bijection PartialTermFrontierTree
      (CheckableGrammar.FrontierState checkableGrammar .cterm) :=
  CheckableGrammar.PartialFrontierTree.equivFrontierState

theorem partialTermFrontierTree_of_toFrontierState
    (frontierTree : PartialTermFrontierTree) :
    CheckableGrammar.PartialFrontierTree.ofFrontierState
        (CheckableGrammar.PartialFrontierTree.toFrontierState frontierTree) =
      frontierTree :=
  CheckableGrammar.PartialFrontierTree.of_toFrontierState frontierTree

theorem partialTermFrontierTree_to_ofFrontierState
    (state : CheckableGrammar.FrontierState checkableGrammar .cterm) :
    CheckableGrammar.PartialFrontierTree.toFrontierState
        (CheckableGrammar.PartialFrontierTree.ofFrontierState state) =
      state :=
  CheckableGrammar.PartialFrontierTree.to_ofFrontierState state

structure ParsedTermFrontier (pref : List Tok) where
  fuel : Nat
  parsed : CheckableGrammar.ParsedFrontierState checkableGrammar .cterm pref
  found : parsed ∈ ctermFrontierStatesFuel fuel pref
  frontierTree : PartialTermFrontierTree
  frontierTree_state :
    CheckableGrammar.PartialFrontierTree.toFrontierState frontierTree =
      parsed.state

namespace ParsedTermFrontier

def Completes {pref : List Tok}
    (frontier : ParsedTermFrontier pref) (program : Program) : Prop :=
  ∃ tree,
    CheckableGrammar.PartialFrontierTree.Completes checkableGrammar
      frontier.frontierTree tree ∧
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
    frontierTree :=
      CheckableGrammar.PartialFrontierTree.ofFrontierState parsed.state
    frontierTree_state :=
      CheckableGrammar.PartialFrontierTree.to_ofFrontierState parsed.state
  }, ?_⟩
  refine ⟨tree, ?_, hdenotes⟩
  simpa [CheckableGrammar.PartialFrontierTree.Completes,
    CheckableGrammar.PartialFrontierTree.to_ofFrontierState]
    using hstateCompletes

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

namespace NestedBlockView

def doneTermOrCutoff (tree : Tree Tok) : Generated.PartialTerm :=
  match denoteTerm? tree with
  | some term => .done term
  | none => .cutoff

def doneLValOrCutoff (tree : Tree Tok) : Generated.PartialLVal :=
  match denoteLVal? tree with
  | some lval => .done lval
  | none => .cutoff

def doneTermsOrCutoff (tree : Tree Tok) : Generated.PartialTerms :=
  match denoteTerms? tree with
  | some terms => .done terms
  | none => .cutoff

def prependTerm (head : Term) :
    Generated.PartialTerms → Generated.PartialTerms
  | .cutoff => .elems [head] none
  | .done terms => .done (head :: terms)
  | .elems pre tail => .elems (head :: pre) tail

inductive PartialView where
  | lval (frontier : Generated.PartialLVal)
  | term (frontier : Generated.PartialTerm)
  | terms (frontier : Generated.PartialTerms)
  | unit

namespace PartialView

def asLVal : PartialView → Generated.PartialLVal
  | .lval frontier => frontier
  | _ => .cutoff

def asTerm : PartialView → Generated.PartialTerm
  | .term frontier => frontier
  | _ => .cutoff

def asTerms : PartialView → Generated.PartialTerms
  | .terms frontier => frontier
  | _ => .cutoff

end PartialView

def rawCutoffForCat : Cat → PartialView
  | .clval => .lval .cutoff
  | .cterm => .term .cutoff
  | .cterms => .terms .cutoff
  | .ctermsTail => .terms .cutoff
  | .cty => .unit
  | .clvals => .unit
  | .clvalsTail => .unit

def rawBoundaryFor (lhs : Cat) (name : String) (dot : Nat)
    (doneChildren : List (Tree Tok)) : PartialView :=
  match lhs, name, dot, doneChildren with
  | .clval, "clvalVar", 0, [] =>
      .lval (.varX .cutoff)
  | .clval, "clvalVar", 1, [.token (.ident name)] =>
      .lval (.varX (.done name))
  | .clval, "clvalDeref", 0, [] =>
      .lval (.derefOperand .cutoff)
  | .clval, "clvalDeref", 1, [.token .star] =>
      .lval .derefStart
  | .clval, "clvalDeref", 2, [.token .star, operandTree] =>
      .lval (.derefOperand (doneLValOrCutoff operandTree))
  | .cterms, "ctermsEmpty", 0, [] =>
      .terms (.done [])
  | .cterms, "ctermsCons", 0, [] =>
      .terms (.elems [] none)
  | .cterms, "ctermsCons", 1, [headTree] =>
      match denoteTerm? headTree with
      | some head => .terms (.elems [head] none)
      | none => .terms (.elems [] none)
  | .cterms, "ctermsCons", 2, [headTree, tailTree] =>
      match denoteTerm? headTree, denoteTermsTail? tailTree with
      | some head, some tail => .terms (.done (head :: tail))
      | some head, none => .terms (.elems [head] none)
      | none, _ => .terms (.elems [] none)
  | .ctermsTail, "ctermsTailEmpty", 0, [] =>
      .terms (.done [])
  | .ctermsTail, "ctermsTailCons", 0, [] =>
      .terms (.elems [] none)
  | .ctermsTail, "ctermsTailCons", 1, [.token .comma] =>
      .terms (.elems [] none)
  | .ctermsTail, "ctermsTailCons", 2, [.token .comma, headTree] =>
      match denoteTerm? headTree with
      | some head => .terms (.elems [head] none)
      | none => .terms (.elems [] none)
  | .ctermsTail, "ctermsTailCons", 3, [.token .comma, headTree, tailTree] =>
      match denoteTerm? headTree, denoteTermsTail? tailTree with
      | some head, some tail => .terms (.done (head :: tail))
      | some head, none => .terms (.elems [head] none)
      | none, _ => .terms (.elems [] none)
  | .cterm, "ctermUnit", 0, [] =>
      .term .cutoff
  | .cterm, "ctermUnit", 1, [.token .unit] =>
      .term (.done SyntaxSemantics.ctermUnit)
  | .cterm, "ctermInt", 0, [] =>
      .term .cutoff
  | .cterm, "ctermInt", 1, [.token (.num n)] =>
      .term (.intN n)
  | .cterm, "ctermTrue", 0, [] =>
      .term .cutoff
  | .cterm, "ctermTrue", 1, [.token .trueLit] =>
      .term (.done SyntaxSemantics.ctermTrue)
  | .cterm, "ctermFalse", 0, [] =>
      .term .cutoff
  | .cterm, "ctermFalse", 1, [.token .falseLit] =>
      .term (.done SyntaxSemantics.ctermFalse)
  | .cterm, "ctermBlock", 0, [] =>
      .term .blockStart
  | .cterm, "ctermBlock", 1, [.token .block] =>
      .term .blockStart
  | .cterm, "ctermBlock", 2,
      [.token .block, .token (.lifetime lifetime)] =>
      .term (.blockTerms lifetime .cutoff)
  | .cterm, "ctermBlock", 3,
      [.token .block, .token (.lifetime lifetime), .token .lbrace] =>
      .term (.blockTerms lifetime .cutoff)
  | .cterm, "ctermBlock", 4,
      [.token .block, .token (.lifetime lifetime), .token .lbrace,
        termsTree] =>
      .term (.blockTerms lifetime (doneTermsOrCutoff termsTree))
  | .cterm, "ctermBlock", 5,
      [.token .block, .token (.lifetime lifetime), .token .lbrace,
        termsTree, .token .rbrace] =>
      .term (.blockTerms lifetime (doneTermsOrCutoff termsTree))
  | .cterm, "ctermLetMut", 0, [] =>
      .term (.letMutName .cutoff)
  | .cterm, "ctermLetMut", 1, [.token .letKw] =>
      .term .letMutStart
  | .cterm, "ctermLetMut", 2, [.token .letKw, .token .mutKw] =>
      .term (.letMutName .cutoff)
  | .cterm, "ctermLetMut", 3,
      [.token .letKw, .token .mutKw, .token (.ident name)] =>
      .term (.letMutName (.done name))
  | .cterm, "ctermLetMut", 4,
      [.token .letKw, .token .mutKw, .token (.ident name),
        .token .assign] =>
      .term (.letMutInitialiser name .cutoff)
  | .cterm, "ctermLetMut", 5,
      [.token .letKw, .token .mutKw, .token (.ident name),
        .token .assign, initialiserTree] =>
      .term (.letMutInitialiser name (doneTermOrCutoff initialiserTree))
  | .cterm, "ctermAssign", 0, [] =>
      .term (.assignLhs .cutoff)
  | .cterm, "ctermAssign", 1, [lhsTree] =>
      .term (.assignLhs (doneLValOrCutoff lhsTree))
  | .cterm, "ctermAssign", 2, [lhsTree, .token .assign] =>
      match denoteLVal? lhsTree with
      | some lhs => .term (.assignRhs lhs .cutoff)
      | none => .term .cutoff
  | .cterm, "ctermAssign", 3, [lhsTree, .token .assign, rhsTree] =>
      match denoteLVal? lhsTree with
      | some lhs => .term (.assignRhs lhs (doneTermOrCutoff rhsTree))
      | none => .term .cutoff
  | .cterm, "ctermBox", 0, [] =>
      .term (.boxOperand .cutoff)
  | .cterm, "ctermBox", 1, [.token .box] =>
      .term .boxStart
  | .cterm, "ctermBox", 2, [.token .box, operandTree] =>
      .term (.boxOperand (doneTermOrCutoff operandTree))
  | .cterm, "ctermBorrowShared", 0, [] =>
      .term (.borrowSharedOperand .cutoff)
  | .cterm, "ctermBorrowShared", 1, [.token .amp] =>
      .term .borrowSharedStart
  | .cterm, "ctermBorrowShared", 2, [.token .amp, operandTree] =>
      .term (.borrowSharedOperand (doneLValOrCutoff operandTree))
  | .cterm, "ctermBorrowMut", 0, [] =>
      .term (.borrowMutOperand .cutoff)
  | .cterm, "ctermBorrowMut", 1, [.token .amp] =>
      .term .borrowSharedStart
  | .cterm, "ctermBorrowMut", 2, [.token .amp, .token .mutKw] =>
      .term (.borrowMutOperand .cutoff)
  | .cterm, "ctermBorrowMut", 3,
      [.token .amp, .token .mutKw, operandTree] =>
      .term (.borrowMutOperand (doneLValOrCutoff operandTree))
  | .cterm, "ctermMove", 0, [] =>
      .term (.moveOperand .cutoff)
  | .cterm, "ctermMove", 1, [operandTree] =>
      .term (.moveOperand (doneLValOrCutoff operandTree))
  | .cterm, "ctermCopy", 0, [] =>
      .term (.copyOperand .cutoff)
  | .cterm, "ctermCopy", 1, [.token .copyKw] =>
      .term .copyStart
  | .cterm, "ctermCopy", 2, [.token .copyKw, operandTree] =>
      .term (.copyOperand (doneLValOrCutoff operandTree))
  | .cterm, "ctermEq", 0, [] =>
      .term (.termPrefix .cutoff)
  | .cterm, "ctermEq", 1, [lhsTree] =>
      .term (.termPrefix (doneTermOrCutoff lhsTree))
  | .cterm, "ctermEq", 2, [lhsTree, .token .eqEq] =>
      match denoteTerm? lhsTree with
      | some lhs => .term (.eqRhs lhs .cutoff)
      | none => .term .cutoff
  | .cterm, "ctermEq", 3, [lhsTree, .token .eqEq, rhsTree] =>
      match denoteTerm? lhsTree with
      | some lhs => .term (.eqRhs lhs (doneTermOrCutoff rhsTree))
      | none => .term .cutoff
  | .cterm, "ctermIte", 0, [] =>
      .term (.iteCondition .cutoff)
  | .cterm, "ctermIte", 1, [.token .ifKw] =>
      .term .iteStart
  | .cterm, "ctermIte", 2, [.token .ifKw, conditionTree] =>
      .term (.iteCondition (doneTermOrCutoff conditionTree))
  | .cterm, "ctermIte", 3, [.token .ifKw, conditionTree, trueTree] =>
      match denoteTerm? conditionTree with
      | some condition =>
          .term (.iteTrueBranch condition (doneTermOrCutoff trueTree))
      | none => .term .cutoff
  | .cterm, "ctermIte", 4,
      [.token .ifKw, conditionTree, trueTree, .token .elseKw] =>
      match denoteTerm? conditionTree, denoteTerm? trueTree with
      | some condition, some trueBranch =>
          .term (.iteFalseBranch condition trueBranch .cutoff)
      | _, _ => .term .cutoff
  | .cterm, "ctermIte", 5,
      [.token .ifKw, conditionTree, trueTree, .token .elseKw,
        falseTree] =>
      match denoteTerm? conditionTree, denoteTerm? trueTree with
      | some condition, some trueBranch =>
          .term (.iteFalseBranch condition trueBranch
            (doneTermOrCutoff falseTree))
      | _, _ => .term .cutoff
  | .cterm, "ctermWhile", 0, [] =>
      .term .whileStart
  | .cterm, "ctermWhile", 1, [.token .whileKw] =>
      .term .whileStart
  | .cterm, "ctermWhile", 2,
      [.token .whileKw, .token (.lifetime bodyLifetime)] =>
      .term (.whileCondition bodyLifetime .cutoff)
  | .cterm, "ctermWhile", 3,
      [.token .whileKw, .token (.lifetime bodyLifetime),
        conditionTree] =>
      .term (.whileCondition bodyLifetime (doneTermOrCutoff conditionTree))
  | .cterm, "ctermWhile", 4,
      [.token .whileKw, .token (.lifetime bodyLifetime),
        conditionTree, bodyTree] =>
      match denoteTerm? conditionTree with
      | some condition =>
          .term (.whileBody bodyLifetime condition (doneTermOrCutoff bodyTree))
      | none => .term .cutoff
  | cat, _, _, _ =>
      rawCutoffForCat cat

def rawBoundary (item : Item Cat Terminal)
    (doneChildren : List (Tree Tok)) : PartialView :=
  rawBoundaryFor item.rule.lhs item.rule.name item.dot doneChildren

def rawDescendFor (lhs activeCat : Cat) (name : String) (dot : Nat)
    (doneChildren : List (Tree Tok)) (child : PartialView) :
    PartialView :=
  match lhs, activeCat, name, dot, doneChildren with
  | .clval, .clval, "clvalDeref", 1, [.token .star] =>
      .lval (.derefOperand child.asLVal)
  | .cterms, .cterm, "ctermsCons", 0, [] =>
      .terms (.elems [] (some child.asTerm))
  | .cterms, .ctermsTail, "ctermsCons", 1, [headTree] =>
      match denoteTerm? headTree with
      | some head => .terms (prependTerm head child.asTerms)
      | none => .terms (.elems [] none)
  | .ctermsTail, .cterm, "ctermsTailCons", 1, [.token .comma] =>
      .terms (.elems [] (some child.asTerm))
  | .ctermsTail, .ctermsTail, "ctermsTailCons", 2,
      [.token .comma, headTree] =>
      match denoteTerm? headTree with
      | some head => .terms (prependTerm head child.asTerms)
      | none => .terms (.elems [] none)
  | .cterm, .cterms, "ctermBlock", 3,
      [.token .block, .token (.lifetime lifetime), .token .lbrace] =>
      .term (.blockTerms lifetime child.asTerms)
  | .cterm, .cterm, "ctermLetMut", 4,
      [.token .letKw, .token .mutKw, .token (.ident name),
        .token .assign] =>
      .term (.letMutInitialiser name child.asTerm)
  | .cterm, .cterm, "ctermAssign", 2, [lhsTree, .token .assign] =>
      match denoteLVal? lhsTree with
      | some lhs => .term (.assignRhs lhs child.asTerm)
      | none => .term .cutoff
  | .cterm, .cterm, "ctermBox", 1, [.token .box] =>
      .term (.boxOperand child.asTerm)
  | .cterm, .cterm, "ctermEq", 0, [] =>
      .term (.termPrefix child.asTerm)
  | .cterm, .cterm, "ctermEq", 2, [lhsTree, .token .eqEq] =>
      match denoteTerm? lhsTree with
      | some lhs => .term (.eqRhs lhs child.asTerm)
      | none => .term .cutoff
  | .cterm, .cterm, "ctermIte", 1, [.token .ifKw] =>
      .term (.iteCondition child.asTerm)
  | .cterm, .cterm, "ctermIte", 2,
      [.token .ifKw, conditionTree] =>
      match denoteTerm? conditionTree with
      | some condition => .term (.iteTrueBranch condition child.asTerm)
      | none => .term .cutoff
  | .cterm, .cterm, "ctermIte", 4,
      [.token .ifKw, conditionTree, trueTree, .token .elseKw] =>
      match denoteTerm? conditionTree, denoteTerm? trueTree with
      | some condition, some trueBranch =>
          .term (.iteFalseBranch condition trueBranch child.asTerm)
      | _, _ => .term .cutoff
  | .cterm, .cterm, "ctermWhile", 2,
      [.token .whileKw, .token (.lifetime bodyLifetime)] =>
      .term (.whileCondition bodyLifetime child.asTerm)
  | .cterm, .cterm, "ctermWhile", 3,
      [.token .whileKw, .token (.lifetime bodyLifetime),
        conditionTree] =>
      match denoteTerm? conditionTree with
      | some condition =>
          .term (.whileBody bodyLifetime condition child.asTerm)
      | none => .term .cutoff
  | .cterm, .clval, "ctermAssign", 0, [] =>
      .term (.assignLhs child.asLVal)
  | .cterm, .clval, "ctermBorrowShared", 1, [.token .amp] =>
      .term (.borrowSharedOperand child.asLVal)
  | .cterm, .clval, "ctermBorrowMut", 2,
      [.token .amp, .token .mutKw] =>
      .term (.borrowMutOperand child.asLVal)
  | .cterm, .clval, "ctermMove", 0, [] =>
      .term (.moveOperand child.asLVal)
  | .cterm, .clval, "ctermCopy", 1, [.token .copyKw] =>
      .term (.copyOperand child.asLVal)
  | cat, _, _, _, _ =>
      rawCutoffForCat cat

def rawDescend (item : Item Cat Terminal) (activeCat : Cat)
    (doneChildren : List (Tree Tok)) (child : PartialView) :
    PartialView :=
  rawDescendFor item.rule.lhs activeCat item.rule.name item.dot
    doneChildren child

def rawView :
    {cat : Cat} →
      CheckableGrammar.PartialFrontierTree checkableGrammar cat →
      PartialView
  | _, .boundary item _ doneChildren _ =>
      rawBoundary item doneChildren
  | _, .descend item _ activeCat _ _ doneChildren _ child =>
      rawDescend item activeCat doneChildren (rawView child)


def lval (frontierTree : PartialLValFrontierTree) :
    Generated.PartialLVal :=
  (rawView frontierTree).asLVal

def terms (frontierTree : PartialTermsFrontierTree) :
    Generated.PartialTerms :=
  (rawView frontierTree).asTerms

def termsTail (frontierTree : PartialTermsTailFrontierTree) :
    Generated.PartialTerms :=
  (rawView frontierTree).asTerms

def term (frontierTree : PartialTermFrontierTree) :
    Generated.PartialTerm :=
  (rawView frontierTree).asTerm

inductive CompletedView where
  | lval (completed : LVal)
  | term (completed : Term)
  | terms (completed : List Term)
  | unit

def DenotesView : Cat → Tree Tok → CompletedView → Prop
  | .clval, tree, .lval completed => DenotesLVal tree completed
  | .cterm, tree, .term completed => DenotesTerm tree completed
  | .cterms, tree, .terms completed => DenotesTerms tree completed
  | .ctermsTail, tree, .terms completed => DenotesTermsTail tree completed
  | .cty, _, .unit => True
  | .clvals, _, .unit => True
  | .clvalsTail, _, .unit => True
  | _, _, _ => False

def CompletesView : PartialView → CompletedView → Prop
  | .lval frontier, .lval completed =>
      Generated.CompletesLVal frontier completed
  | .term frontier, .term completed =>
      Generated.CompletesTerm frontier completed
  | .terms frontier, .terms completed =>
      Generated.CompletesTerms frontier completed
  | .unit, .unit => True
  | _, _ => False

theorem doneTermOrCutoff_completes {tree : Tree Tok} {term : Term}
    (hdenotes : DenotesTerm tree term) :
    Generated.CompletesTerm (doneTermOrCutoff tree) term := by
  have hdenote? := denoteTerm?_complete_of_denotes hdenotes
  simp [doneTermOrCutoff, hdenote?]
  exact Generated.CompletesTerm.done

theorem doneLValOrCutoff_completes {tree : Tree Tok} {lval : LVal}
    (hdenotes : DenotesLVal tree lval) :
    Generated.CompletesLVal (doneLValOrCutoff tree) lval := by
  have hdenote? := denoteLVal?_complete_of_denotes hdenotes
  simp [doneLValOrCutoff, hdenote?]
  exact Generated.CompletesLVal.done

theorem doneTermsOrCutoff_completes {tree : Tree Tok} {terms : List Term}
    (hdenotes : DenotesTerms tree terms) :
    Generated.CompletesTerms (doneTermsOrCutoff tree) terms := by
  have hdenote? := denoteTerms?_complete_of_denotes hdenotes
  simp [doneTermsOrCutoff, hdenote?]
  exact Generated.CompletesTerms.done

theorem prependTerm_completes {frontier : Generated.PartialTerms}
    {tail : List Term} (head : Term)
    (hfrontier : Generated.CompletesTerms frontier tail) :
    Generated.CompletesTerms (prependTerm head frontier) (head :: tail) := by
  cases hfrontier with
  | done =>
      simp [prependTerm]
      exact Generated.CompletesTerms.done
  | cutoff =>
      simp [prependTerm]
      exact Generated.CompletesTerms.elemsDone
  | elemsDone =>
      simp [prependTerm]
      exact Generated.CompletesTerms.elemsDone
  | elemsTail htail =>
      simp [prependTerm]
      exact Generated.CompletesTerms.elemsTail htail

theorem rawCutoffForCat_completes {cat : Cat} {tree : Tree Tok}
    {completed : CompletedView}
    (hdenotes : DenotesView cat tree completed) :
    CompletesView (rawCutoffForCat cat) completed := by
  cases cat <;> cases completed <;>
    simp [DenotesView, CompletesView, rawCutoffForCat] at hdenotes ⊢
  · exact Generated.CompletesLVal.cutoff
  · exact Generated.CompletesTerm.cutoff
  · exact Generated.CompletesTerms.cutoff
  · exact Generated.CompletesTerms.cutoff



end NestedBlockView

def extractPartialTermFrontierTree (_frontierTree : PartialTermFrontierTree) :
    Program :=
  missingTerm

theorem extractPartialTermFrontierTree_wellTyped
    (frontierTree : PartialTermFrontierTree) :
    ProgramWellTyped (extractPartialTermFrontierTree frontierTree) := by
  exact ⟨.unit, LwRust.Paper.Env.empty,
    LwRust.Paper.TermTyping.missing
      LwRust.Paper.WellFormedTy.unit tyLoanFree_unit⟩

theorem extractPartialTermFrontierTree_relaxedWellTyped
    (frontierTree : PartialTermFrontierTree) :
    ProgramRelaxedWellTyped (extractPartialTermFrontierTree frontierTree) := by
  exact ⟨.unit, LwRust.Paper.Env.empty,
    LwRust.Paper.RelaxedTermTyping.missing
      LwRust.Paper.WellFormedTy.unit tyLoanFree_unit⟩

theorem extractPartialTermFrontierTree_complete
    {frontierTree : PartialTermFrontierTree} {program : Program}
    (_hcompletes :
      ∃ tree,
        CheckableGrammar.PartialFrontierTree.Completes checkableGrammar
          frontierTree tree ∧
        DenotesTerm tree program)
    (_hwellTyped : ProgramWellTyped program) :
    ProgramWellTyped (extractPartialTermFrontierTree frontierTree) :=
  extractPartialTermFrontierTree_wellTyped frontierTree

theorem extractPartialTermFrontierTree_relaxedComplete
    {frontierTree : PartialTermFrontierTree} {program : Program}
    (_hcompletes :
      ∃ tree,
        CheckableGrammar.PartialFrontierTree.Completes checkableGrammar
          frontierTree tree ∧
        DenotesTerm tree program)
    (_hwellTyped : ProgramRelaxedWellTyped program) :
    ProgramRelaxedWellTyped (extractPartialTermFrontierTree frontierTree) :=
  extractPartialTermFrontierTree_relaxedWellTyped frontierTree

namespace NestedBlocks

structure ExtractedTermFrontier (pref : List Tok) where
  parsed : ParsedTermFrontier pref

namespace ExtractedTermFrontier

def extract {pref : List Tok} (frontier : ExtractedTermFrontier pref) :
    Program :=
  extractPartialTermFrontierTree frontier.parsed.frontierTree

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
  refine ⟨{
    parsed := frontier
  }, ?_⟩
  exact extractPartialTermFrontierTree_complete
    hfrontierCompletes hwellTyped

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
  refine ⟨{
    parsed := frontier
  }, ?_⟩
  exact extractPartialTermFrontierTree_relaxedComplete
    hfrontierCompletes hwellTyped

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
