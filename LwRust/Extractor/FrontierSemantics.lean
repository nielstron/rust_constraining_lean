import LwRust.Extractor.FrontierParser
import LwRust.Extractor.Generated.FrontierGrammar
import LwRust.Extractor.PartialProgram

/-!
Semantic interpretation of FW-Rust parse trees.

`LwRust.Extractor.Frontier` proves that a token prefix can be completed to a
grammar parse tree.  This file connects those parse trees back to the existing
complete AST types (`Ty`, `LVal`, `Term`) and to the old
`Generated.PartialProgram` completion relation used by the extractor proofs.
-/

namespace ConservativeExtractor
namespace GrammarFrontier
namespace FwRust

mutual

inductive DenotesTy : Tree Tok → Ty → Prop where
  | ctyUnit :
      DenotesTy (.node "ctyUnit" [.token .ctyUnit])
        SyntaxCtor.ctyUnit_ctor
  | ctyInt :
      DenotesTy (.node "ctyInt" [.token .ctyInt])
        SyntaxCtor.ctyInt_ctor
  | ctyBool :
      DenotesTy (.node "ctyBool" [.token .ctyBool])
        SyntaxCtor.ctyBool_ctor
  | ctyBorrowShared {targetsTree : Tree Tok} {targets : List LVal} :
      DenotesLVals targetsTree targets →
      DenotesTy
        (.node "ctyBorrowShared"
          [.token .amp, .token .lbrack, targetsTree, .token .rbrack])
        (SyntaxCtor.ctyBorrowShared_ctor targets)
  | ctyBorrowMut {targetsTree : Tree Tok} {targets : List LVal} :
      DenotesLVals targetsTree targets →
      DenotesTy
        (.node "ctyBorrowMut"
          [.token .ampMut, .token .lbrack, targetsTree, .token .rbrack])
        (SyntaxCtor.ctyBorrowMut_ctor targets)
  | ctyBox {elementTree : Tree Tok} {element : Ty} :
      DenotesTy elementTree element →
      DenotesTy (.node "ctyBox" [.token .box, elementTree])
        (SyntaxCtor.ctyBox_ctor element)

inductive DenotesLVal : Tree Tok → LVal → Prop where
  | clvalVar {x : Name} :
      DenotesLVal (.node "clvalVar" [.token (.ident x)])
        (SyntaxCtor.clvalVar_ctor x)
  | clvalDeref {operandTree : Tree Tok} {operand : LVal} :
      DenotesLVal operandTree operand →
      DenotesLVal (.node "clvalDeref" [.token .star, operandTree])
        (SyntaxCtor.clvalDeref_ctor operand)

inductive DenotesLVals : Tree Tok → List LVal → Prop where
  | clvalsEmpty :
      DenotesLVals (.node "clvalsEmpty" []) []
  | clvalsCons {headTree tailTree : Tree Tok} {head : LVal}
      {tail : List LVal} :
      DenotesLVal headTree head →
      DenotesLValsTail tailTree tail →
      DenotesLVals (.node "clvalsCons" [headTree, tailTree])
        (head :: tail)

inductive DenotesLValsTail : Tree Tok → List LVal → Prop where
  | clvalsTailEmpty :
      DenotesLValsTail (.node "clvalsTailEmpty" []) []
  | clvalsTailCons {headTree tailTree : Tree Tok} {head : LVal}
      {tail : List LVal} :
      DenotesLVal headTree head →
      DenotesLValsTail tailTree tail →
      DenotesLValsTail
        (.node "clvalsTailCons" [.token .comma, headTree, tailTree])
        (head :: tail)

inductive DenotesTerm : Tree Tok → Term → Prop where
  | ctermUnit :
      DenotesTerm (.node "ctermUnit" [.token .unit])
        SyntaxCtor.ctermUnit_ctor
  | ctermInt {n : Int} :
      DenotesTerm (.node "ctermInt" [.token (.num n)])
        (SyntaxCtor.ctermInt_ctor n)
  | ctermTrue :
      DenotesTerm (.node "ctermTrue" [.token .trueLit])
        SyntaxCtor.ctermTrue_ctor
  | ctermFalse :
      DenotesTerm (.node "ctermFalse" [.token .falseLit])
        SyntaxCtor.ctermFalse_ctor
  | ctermBlock {lifetime : Lifetime} {termsTree : Tree Tok}
      {terms : List Term} :
      DenotesTerms termsTree terms →
      DenotesTerm
        (.node "ctermBlock"
          [.token .block, .token (.lifetime lifetime), .token .lbrace,
            termsTree, .token .rbrace])
        (SyntaxCtor.ctermBlock_ctor lifetime terms)
  | ctermLetMut {name : Name} {initialiserTree : Tree Tok}
      {initialiser : Term} :
      DenotesTerm initialiserTree initialiser →
      DenotesTerm
        (.node "ctermLetMut"
          [.token .letKw, .token .mutKw, .token (.ident name),
            .token .assign, initialiserTree])
        (SyntaxCtor.ctermLetMut_ctor name initialiser)
  | ctermAssign {lhsTree rhsTree : Tree Tok} {lhs : LVal} {rhs : Term} :
      DenotesLVal lhsTree lhs →
      DenotesTerm rhsTree rhs →
      DenotesTerm (.node "ctermAssign" [lhsTree, .token .assign, rhsTree])
        (SyntaxCtor.ctermAssign_ctor lhs rhs)
  | ctermBox {operandTree : Tree Tok} {operand : Term} :
      DenotesTerm operandTree operand →
      DenotesTerm (.node "ctermBox" [.token .box, operandTree])
        (SyntaxCtor.ctermBox_ctor operand)
  | ctermBorrowShared {operandTree : Tree Tok} {operand : LVal} :
      DenotesLVal operandTree operand →
      DenotesTerm (.node "ctermBorrowShared" [.token .amp, operandTree])
        (SyntaxCtor.ctermBorrowShared_ctor operand)
  | ctermBorrowMut {operandTree : Tree Tok} {operand : LVal} :
      DenotesLVal operandTree operand →
      DenotesTerm (.node "ctermBorrowMut" [.token .ampMut, operandTree])
        (SyntaxCtor.ctermBorrowMut_ctor operand)
  | ctermMove {operandTree : Tree Tok} {operand : LVal} :
      DenotesLVal operandTree operand →
      DenotesTerm (.node "ctermMove" [.token .moveKw, operandTree])
        (SyntaxCtor.ctermMove_ctor operand)
  | ctermCopy {operandTree : Tree Tok} {operand : LVal} :
      DenotesLVal operandTree operand →
      DenotesTerm (.node "ctermCopy" [.token .copyKw, operandTree])
        (SyntaxCtor.ctermCopy_ctor operand)
  | ctermEq {lhsTree rhsTree : Tree Tok} {lhs rhs : Term} :
      DenotesTerm lhsTree lhs →
      DenotesTerm rhsTree rhs →
      DenotesTerm (.node "ctermEq" [lhsTree, .token .eqEq, rhsTree])
        (SyntaxCtor.ctermEq_ctor lhs rhs)
  | ctermIte {conditionTree trueTree falseTree : Tree Tok}
      {condition trueBranch falseBranch : Term} :
      DenotesTerm conditionTree condition →
      DenotesTerm trueTree trueBranch →
      DenotesTerm falseTree falseBranch →
      DenotesTerm
        (.node "ctermIte"
          [.token .ifKw, conditionTree, trueTree, .token .elseKw,
            falseTree])
        (SyntaxCtor.ctermIte_ctor condition trueBranch falseBranch)
  | ctermWhile {bodyLifetime : Lifetime} {conditionTree bodyTree : Tree Tok}
      {condition body : Term} :
      DenotesTerm conditionTree condition →
      DenotesTerm bodyTree body →
      DenotesTerm
        (.node "ctermWhile"
          [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree,
            bodyTree])
        (SyntaxCtor.ctermWhile_ctor bodyLifetime condition body)

inductive DenotesTerms : Tree Tok → List Term → Prop where
  | ctermsEmpty :
      DenotesTerms (.node "ctermsEmpty" []) []
  | ctermsCons {headTree tailTree : Tree Tok} {head : Term}
      {tail : List Term} :
      DenotesTerm headTree head →
      DenotesTermsTail tailTree tail →
      DenotesTerms (.node "ctermsCons" [headTree, tailTree])
        (head :: tail)

inductive DenotesTermsTail : Tree Tok → List Term → Prop where
  | ctermsTailEmpty :
      DenotesTermsTail (.node "ctermsTailEmpty" []) []
  | ctermsTailCons {headTree tailTree : Tree Tok} {head : Term}
      {tail : List Term} :
      DenotesTerm headTree head →
      DenotesTermsTail tailTree tail →
      DenotesTermsTail
        (.node "ctermsTailCons" [.token .comma, headTree, tailTree])
        (head :: tail)

end

set_option linter.unusedSimpArgs false in
theorem checkTree_of_grammar_rule {cat : Cat} {rule : Rule Cat Terminal}
    {children : List (Tree Tok)}
    (hrule : rule ∈ grammar.rules)
    (hlhs : rule.lhs = cat)
    (hseq :
      CheckableGrammar.checkSeq checkableGrammar rule.rhs children =
        Bool.true) :
    CheckableGrammar.checkTree checkableGrammar cat
      (.node rule.name children) = Bool.true := by
  simp [CheckableGrammar.checkTree]
  exact ⟨rule, by simpa [checkableGrammar] using hrule, by
    simp [hlhs, hseq]⟩

set_option linter.unusedSimpArgs false in
mutual

theorem denotesTy_checked :
    ∀ {tree : Tree Tok} {ty : Ty},
      DenotesTy tree ty →
        CheckableGrammar.checkTree checkableGrammar .cty tree = Bool.true := by
  intro tree ty h
  cases h with
  | ctyUnit =>
      simpa [ctyUnitRule] using
        checkTree_of_grammar_rule (rule := ctyUnitRule) (cat := .cty)
          (by simp [grammar]) rfl
          (by
            simp [ctyUnitRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctyInt =>
      simpa [ctyIntRule] using
        checkTree_of_grammar_rule (rule := ctyIntRule) (cat := .cty)
          (by simp [grammar]) rfl
          (by
            simp [ctyIntRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctyBool =>
      simpa [ctyBoolRule] using
        checkTree_of_grammar_rule (rule := ctyBoolRule) (cat := .cty)
          (by simp [grammar]) rfl
          (by
            simp [ctyBoolRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctyBorrowShared htargets =>
      simpa [ctyBorrowSharedRule] using
        checkTree_of_grammar_rule (rule := ctyBorrowSharedRule)
          (cat := .cty) (by simp [grammar]) rfl
          (by
            simp [ctyBorrowSharedRule, CheckableGrammar.checkSeq,
              denotesLVals_checked htargets]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctyBorrowMut htargets =>
      simpa [ctyBorrowMutRule] using
        checkTree_of_grammar_rule (rule := ctyBorrowMutRule)
          (cat := .cty) (by simp [grammar]) rfl
          (by
            simp [ctyBorrowMutRule, CheckableGrammar.checkSeq,
              denotesLVals_checked htargets]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctyBox helement =>
      simpa [ctyBoxRule] using
        checkTree_of_grammar_rule (rule := ctyBoxRule) (cat := .cty)
          (by simp [grammar]) rfl
          (by
            simp [ctyBoxRule, CheckableGrammar.checkSeq,
              denotesTy_checked helement]
            all_goals simp [checkableGrammar, acceptsBool])

theorem denotesLVal_checked :
    ∀ {tree : Tree Tok} {lval : LVal},
      DenotesLVal tree lval →
        CheckableGrammar.checkTree checkableGrammar .clval tree = Bool.true := by
  intro tree lval h
  cases h with
  | clvalVar =>
      simpa [clvalVarRule] using
        checkTree_of_grammar_rule (rule := clvalVarRule) (cat := .clval)
          (by simp [grammar]) rfl
          (by
            simp [clvalVarRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | clvalDeref hoperand =>
      simpa [clvalDerefRule] using
        checkTree_of_grammar_rule (rule := clvalDerefRule) (cat := .clval)
          (by simp [grammar]) rfl
          (by
            simp [clvalDerefRule, CheckableGrammar.checkSeq,
              denotesLVal_checked hoperand]
            all_goals simp [checkableGrammar, acceptsBool])

theorem denotesLVals_checked :
    ∀ {tree : Tree Tok} {lvals : List LVal},
      DenotesLVals tree lvals →
        CheckableGrammar.checkTree checkableGrammar .clvals tree = Bool.true := by
  intro tree lvals h
  cases h with
  | clvalsEmpty =>
      simpa [clvalsEmptyRule] using
        checkTree_of_grammar_rule (rule := clvalsEmptyRule)
          (cat := .clvals) (by simp [grammar]) rfl
          (by
            simp [clvalsEmptyRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | clvalsCons hhead htail =>
      simpa [clvalsConsRule] using
        checkTree_of_grammar_rule (rule := clvalsConsRule)
          (cat := .clvals) (by simp [grammar]) rfl
          (by
            simp [clvalsConsRule, CheckableGrammar.checkSeq,
              denotesLVal_checked hhead, denotesLValsTail_checked htail]
            all_goals simp [checkableGrammar, acceptsBool])

theorem denotesLValsTail_checked :
    ∀ {tree : Tree Tok} {lvals : List LVal},
      DenotesLValsTail tree lvals →
        CheckableGrammar.checkTree checkableGrammar .clvalsTail tree = Bool.true := by
  intro tree lvals h
  cases h with
  | clvalsTailEmpty =>
      simpa [clvalsTailEmptyRule] using
        checkTree_of_grammar_rule (rule := clvalsTailEmptyRule)
          (cat := .clvalsTail) (by simp [grammar]) rfl
          (by
            simp [clvalsTailEmptyRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | clvalsTailCons hhead htail =>
      simpa [clvalsTailConsRule] using
        checkTree_of_grammar_rule (rule := clvalsTailConsRule)
          (cat := .clvalsTail) (by simp [grammar]) rfl
          (by
            simp [clvalsTailConsRule, CheckableGrammar.checkSeq,
              denotesLVal_checked hhead, denotesLValsTail_checked htail]
            all_goals simp [checkableGrammar, acceptsBool])

theorem denotesTerm_checked :
    ∀ {tree : Tree Tok} {term : Term},
      DenotesTerm tree term →
        CheckableGrammar.checkTree checkableGrammar .cterm tree = Bool.true := by
  intro tree term h
  cases h with
  | ctermUnit =>
      simpa [ctermUnitRule] using
        checkTree_of_grammar_rule (rule := ctermUnitRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermUnitRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermInt =>
      simpa [ctermIntRule] using
        checkTree_of_grammar_rule (rule := ctermIntRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermIntRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermTrue =>
      simpa [ctermTrueRule] using
        checkTree_of_grammar_rule (rule := ctermTrueRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermTrueRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermFalse =>
      simpa [ctermFalseRule] using
        checkTree_of_grammar_rule (rule := ctermFalseRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermFalseRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermBlock hterms =>
      simpa [ctermBlockRule] using
        checkTree_of_grammar_rule (rule := ctermBlockRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermBlockRule, CheckableGrammar.checkSeq,
              denotesTerms_checked hterms]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermLetMut hinitialiser =>
      simpa [ctermLetMutRule] using
        checkTree_of_grammar_rule (rule := ctermLetMutRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermLetMutRule, CheckableGrammar.checkSeq,
              denotesTerm_checked hinitialiser]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermAssign hlhs hrhs =>
      simpa [ctermAssignRule] using
        checkTree_of_grammar_rule (rule := ctermAssignRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermAssignRule, CheckableGrammar.checkSeq,
              denotesLVal_checked hlhs, denotesTerm_checked hrhs]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermBox hoperand =>
      simpa [ctermBoxRule] using
        checkTree_of_grammar_rule (rule := ctermBoxRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermBoxRule, CheckableGrammar.checkSeq,
              denotesTerm_checked hoperand]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermBorrowShared hoperand =>
      simpa [ctermBorrowSharedRule] using
        checkTree_of_grammar_rule (rule := ctermBorrowSharedRule)
          (cat := .cterm) (by simp [grammar]) rfl
          (by
            simp [ctermBorrowSharedRule, CheckableGrammar.checkSeq,
              denotesLVal_checked hoperand]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermBorrowMut hoperand =>
      simpa [ctermBorrowMutRule] using
        checkTree_of_grammar_rule (rule := ctermBorrowMutRule)
          (cat := .cterm) (by simp [grammar]) rfl
          (by
            simp [ctermBorrowMutRule, CheckableGrammar.checkSeq,
              denotesLVal_checked hoperand]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermMove hoperand =>
      simpa [ctermMoveRule] using
        checkTree_of_grammar_rule (rule := ctermMoveRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermMoveRule, CheckableGrammar.checkSeq,
              denotesLVal_checked hoperand]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermCopy hoperand =>
      simpa [ctermCopyRule] using
        checkTree_of_grammar_rule (rule := ctermCopyRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermCopyRule, CheckableGrammar.checkSeq,
              denotesLVal_checked hoperand]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermEq hlhs hrhs =>
      simpa [ctermEqRule] using
        checkTree_of_grammar_rule (rule := ctermEqRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermEqRule, CheckableGrammar.checkSeq,
              denotesTerm_checked hlhs, denotesTerm_checked hrhs]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermIte hcondition htrue hfalse =>
      simpa [ctermIteRule] using
        checkTree_of_grammar_rule (rule := ctermIteRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermIteRule, CheckableGrammar.checkSeq,
              denotesTerm_checked hcondition, denotesTerm_checked htrue,
              denotesTerm_checked hfalse]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermWhile hcondition hbody =>
      simpa [ctermWhileRule] using
        checkTree_of_grammar_rule (rule := ctermWhileRule) (cat := .cterm)
          (by simp [grammar]) rfl
          (by
            simp [ctermWhileRule, CheckableGrammar.checkSeq,
              denotesTerm_checked hcondition, denotesTerm_checked hbody]
            all_goals simp [checkableGrammar, acceptsBool])

theorem denotesTerms_checked :
    ∀ {tree : Tree Tok} {terms : List Term},
      DenotesTerms tree terms →
        CheckableGrammar.checkTree checkableGrammar .cterms tree = Bool.true := by
  intro tree terms h
  cases h with
  | ctermsEmpty =>
      simpa [ctermsEmptyRule] using
        checkTree_of_grammar_rule (rule := ctermsEmptyRule)
          (cat := .cterms) (by simp [grammar]) rfl
          (by
            simp [ctermsEmptyRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermsCons hhead htail =>
      simpa [ctermsConsRule] using
        checkTree_of_grammar_rule (rule := ctermsConsRule)
          (cat := .cterms) (by simp [grammar]) rfl
          (by
            simp [ctermsConsRule, CheckableGrammar.checkSeq,
              denotesTerm_checked hhead, denotesTermsTail_checked htail]
            all_goals simp [checkableGrammar, acceptsBool])

theorem denotesTermsTail_checked :
    ∀ {tree : Tree Tok} {terms : List Term},
      DenotesTermsTail tree terms →
        CheckableGrammar.checkTree checkableGrammar .ctermsTail tree = Bool.true := by
  intro tree terms h
  cases h with
  | ctermsTailEmpty =>
      simpa [ctermsTailEmptyRule] using
        checkTree_of_grammar_rule (rule := ctermsTailEmptyRule)
          (cat := .ctermsTail) (by simp [grammar]) rfl
          (by
            simp [ctermsTailEmptyRule, CheckableGrammar.checkSeq]
            all_goals simp [checkableGrammar, acceptsBool])
  | ctermsTailCons hhead htail =>
      simpa [ctermsTailConsRule] using
        checkTree_of_grammar_rule (rule := ctermsTailConsRule)
          (cat := .ctermsTail) (by simp [grammar]) rfl
          (by
            simp [ctermsTailConsRule, CheckableGrammar.checkSeq,
              denotesTerm_checked hhead, denotesTermsTail_checked htail]
            all_goals simp [checkableGrammar, acceptsBool])

end

theorem denotesTy_derives {tree : Tree Tok} {ty : Ty}
    (h : DenotesTy tree ty) : Derives grammar .cty tree.tokens tree := by
  exact CheckableGrammar.checkTree_sound checkableGrammar (denotesTy_checked h)

theorem denotesLVal_derives {tree : Tree Tok} {lval : LVal}
    (h : DenotesLVal tree lval) : Derives grammar .clval tree.tokens tree := by
  exact CheckableGrammar.checkTree_sound checkableGrammar (denotesLVal_checked h)

theorem denotesLVals_derives {tree : Tree Tok} {lvals : List LVal}
    (h : DenotesLVals tree lvals) :
    Derives grammar .clvals tree.tokens tree := by
  exact CheckableGrammar.checkTree_sound checkableGrammar (denotesLVals_checked h)

theorem denotesLValsTail_derives {tree : Tree Tok} {lvals : List LVal}
    (h : DenotesLValsTail tree lvals) :
    Derives grammar .clvalsTail tree.tokens tree := by
  exact CheckableGrammar.checkTree_sound checkableGrammar
    (denotesLValsTail_checked h)

theorem denotesTerm_derives {tree : Tree Tok} {term : Term}
    (h : DenotesTerm tree term) :
    Derives grammar .cterm tree.tokens tree := by
  exact CheckableGrammar.checkTree_sound checkableGrammar (denotesTerm_checked h)

theorem denotesTerms_derives {tree : Tree Tok} {terms : List Term}
    (h : DenotesTerms tree terms) :
    Derives grammar .cterms tree.tokens tree := by
  exact CheckableGrammar.checkTree_sound checkableGrammar (denotesTerms_checked h)

theorem denotesTermsTail_derives {tree : Tree Tok} {terms : List Term}
    (h : DenotesTermsTail tree terms) :
    Derives grammar .ctermsTail tree.tokens tree := by
  exact CheckableGrammar.checkTree_sound checkableGrammar
    (denotesTermsTail_checked h)

mutual

def denoteTy? : Tree Tok → Option Ty
  | .node "ctyUnit" [.token .ctyUnit] =>
      some SyntaxCtor.ctyUnit_ctor
  | .node "ctyInt" [.token .ctyInt] =>
      some SyntaxCtor.ctyInt_ctor
  | .node "ctyBool" [.token .ctyBool] =>
      some SyntaxCtor.ctyBool_ctor
  | .node "ctyBorrowShared"
      [.token .amp, .token .lbrack, targetsTree, .token .rbrack] =>
      return SyntaxCtor.ctyBorrowShared_ctor (← denoteLVals? targetsTree)
  | .node "ctyBorrowMut"
      [.token .ampMut, .token .lbrack, targetsTree, .token .rbrack] =>
      return SyntaxCtor.ctyBorrowMut_ctor (← denoteLVals? targetsTree)
  | .node "ctyBox" [.token .box, elementTree] =>
      return SyntaxCtor.ctyBox_ctor (← denoteTy? elementTree)
  | _ => none

def denoteLVal? : Tree Tok → Option LVal
  | .node "clvalVar" [.token (.ident x)] =>
      some (SyntaxCtor.clvalVar_ctor x)
  | .node "clvalDeref" [.token .star, operandTree] =>
      return SyntaxCtor.clvalDeref_ctor (← denoteLVal? operandTree)
  | _ => none

def denoteLVals? : Tree Tok → Option (List LVal)
  | .node "clvalsEmpty" [] =>
      some []
  | .node "clvalsCons" [headTree, tailTree] =>
      return (← denoteLVal? headTree) :: (← denoteLValsTail? tailTree)
  | _ => none

def denoteLValsTail? : Tree Tok → Option (List LVal)
  | .node "clvalsTailEmpty" [] =>
      some []
  | .node "clvalsTailCons" [.token .comma, headTree, tailTree] =>
      return (← denoteLVal? headTree) :: (← denoteLValsTail? tailTree)
  | _ => none

def denoteTerm? : Tree Tok → Option Term
  | .node "ctermUnit" [.token .unit] =>
      some SyntaxCtor.ctermUnit_ctor
  | .node "ctermInt" [.token (.num n)] =>
      some (SyntaxCtor.ctermInt_ctor n)
  | .node "ctermTrue" [.token .trueLit] =>
      some SyntaxCtor.ctermTrue_ctor
  | .node "ctermFalse" [.token .falseLit] =>
      some SyntaxCtor.ctermFalse_ctor
  | .node "ctermBlock"
      [.token .block, .token (.lifetime lifetime), .token .lbrace,
        termsTree, .token .rbrace] =>
      return SyntaxCtor.ctermBlock_ctor lifetime (← denoteTerms? termsTree)
  | .node "ctermLetMut"
      [.token .letKw, .token .mutKw, .token (.ident name), .token .assign,
        initialiserTree] =>
      return SyntaxCtor.ctermLetMut_ctor name (← denoteTerm? initialiserTree)
  | .node "ctermAssign" [lhsTree, .token .assign, rhsTree] =>
      return SyntaxCtor.ctermAssign_ctor
        (← denoteLVal? lhsTree) (← denoteTerm? rhsTree)
  | .node "ctermBox" [.token .box, operandTree] =>
      return SyntaxCtor.ctermBox_ctor (← denoteTerm? operandTree)
  | .node "ctermBorrowShared" [.token .amp, operandTree] =>
      return SyntaxCtor.ctermBorrowShared_ctor (← denoteLVal? operandTree)
  | .node "ctermBorrowMut" [.token .ampMut, operandTree] =>
      return SyntaxCtor.ctermBorrowMut_ctor (← denoteLVal? operandTree)
  | .node "ctermMove" [.token .moveKw, operandTree] =>
      return SyntaxCtor.ctermMove_ctor (← denoteLVal? operandTree)
  | .node "ctermCopy" [.token .copyKw, operandTree] =>
      return SyntaxCtor.ctermCopy_ctor (← denoteLVal? operandTree)
  | .node "ctermEq" [lhsTree, .token .eqEq, rhsTree] =>
      return SyntaxCtor.ctermEq_ctor
        (← denoteTerm? lhsTree) (← denoteTerm? rhsTree)
  | .node "ctermIte"
      [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw,
        falseBranchTree] =>
      return SyntaxCtor.ctermIte_ctor
        (← denoteTerm? conditionTree)
        (← denoteTerm? trueBranchTree)
        (← denoteTerm? falseBranchTree)
  | .node "ctermWhile"
      [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree,
        bodyTree] =>
      return SyntaxCtor.ctermWhile_ctor bodyLifetime
        (← denoteTerm? conditionTree) (← denoteTerm? bodyTree)
  | _ => none

def denoteTerms? : Tree Tok → Option (List Term)
  | .node "ctermsEmpty" [] =>
      some []
  | .node "ctermsCons" [headTree, tailTree] =>
      return (← denoteTerm? headTree) :: (← denoteTermsTail? tailTree)
  | _ => none

def denoteTermsTail? : Tree Tok → Option (List Term)
  | .node "ctermsTailEmpty" [] =>
      some []
  | .node "ctermsTailCons" [.token .comma, headTree, tailTree] =>
      return (← denoteTerm? headTree) :: (← denoteTermsTail? tailTree)
  | _ => none

end

mutual

theorem denoteTy?_sound :
    ∀ {tree : Tree Tok} {ty : Ty},
      denoteTy? tree = some ty → DenotesTy tree ty
  | .node "ctyUnit" [.token .ctyUnit], ty, h => by
      simp_all [denoteTy?]
      subst ty
      exact DenotesTy.ctyUnit
  | .node "ctyInt" [.token .ctyInt], ty, h => by
      simp_all [denoteTy?]
      subst ty
      exact DenotesTy.ctyInt
  | .node "ctyBool" [.token .ctyBool], ty, h => by
      simp_all [denoteTy?]
      subst ty
      exact DenotesTy.ctyBool
  | .node "ctyBorrowShared"
      [.token .amp, .token .lbrack, targetsTree, .token .rbrack], ty, h => by
      cases htargets : denoteLVals? targetsTree with
      | none =>
          simp [denoteTy?, htargets] at h
      | some targets =>
          simp [denoteTy?, htargets] at h
          subst ty
          exact DenotesTy.ctyBorrowShared
            (denoteLVals?_sound htargets)
  | .node "ctyBorrowMut"
      [.token .ampMut, .token .lbrack, targetsTree, .token .rbrack], ty, h => by
      cases htargets : denoteLVals? targetsTree with
      | none =>
          simp [denoteTy?, htargets] at h
      | some targets =>
          simp [denoteTy?, htargets] at h
          subst ty
          exact DenotesTy.ctyBorrowMut
            (denoteLVals?_sound htargets)
  | .node "ctyBox" [.token .box, elementTree], ty, h => by
      cases helement : denoteTy? elementTree with
      | none =>
          simp [denoteTy?, helement] at h
      | some element =>
          simp [denoteTy?, helement] at h
          subst ty
          exact DenotesTy.ctyBox (denoteTy?_sound helement)
  | tree, ty, h => by
      unfold denoteTy? at h
      split at h
      · simp at h
        subst ty
        exact DenotesTy.ctyUnit
      · simp at h
        subst ty
        exact DenotesTy.ctyInt
      · simp at h
        subst ty
        exact DenotesTy.ctyBool
      · rename_i targetsTree
        cases htargets : denoteLVals? targetsTree with
        | none =>
            simp [htargets] at h
        | some targets =>
            simp [htargets] at h
            subst ty
            exact DenotesTy.ctyBorrowShared
              (denoteLVals?_sound htargets)
      · rename_i targetsTree
        cases htargets : denoteLVals? targetsTree with
        | none =>
            simp [htargets] at h
        | some targets =>
            simp [htargets] at h
            subst ty
            exact DenotesTy.ctyBorrowMut
              (denoteLVals?_sound htargets)
      · rename_i elementTree
        cases helement : denoteTy? elementTree with
        | none =>
            simp [helement] at h
        | some element =>
            simp [helement] at h
            subst ty
            exact DenotesTy.ctyBox
              (denoteTy?_sound helement)
      · simp at h

theorem denoteLVal?_sound :
    ∀ {tree : Tree Tok} {lval : LVal},
      denoteLVal? tree = some lval → DenotesLVal tree lval
  | .node "clvalVar" [.token (.ident x)], lval, h => by
      simp_all [denoteLVal?]
      subst lval
      exact DenotesLVal.clvalVar
  | .node "clvalDeref" [.token .star, operandTree], lval, h => by
      cases hoperand : denoteLVal? operandTree with
      | none =>
          simp [denoteLVal?, hoperand] at h
      | some operand =>
          simp [denoteLVal?, hoperand] at h
          subst lval
          exact DenotesLVal.clvalDeref
            (denoteLVal?_sound hoperand)
  | tree, lval, h => by
      unfold denoteLVal? at h
      split at h
      · rename_i x
        simp at h
        subst lval
        exact DenotesLVal.clvalVar
      · rename_i operandTree
        cases hoperand : denoteLVal? operandTree with
        | none =>
            simp [hoperand] at h
        | some operand =>
            simp [hoperand] at h
            subst lval
            exact DenotesLVal.clvalDeref
              (denoteLVal?_sound hoperand)
      · simp at h

theorem denoteLVals?_sound :
    ∀ {tree : Tree Tok} {lvals : List LVal},
      denoteLVals? tree = some lvals → DenotesLVals tree lvals
  | .node "clvalsEmpty" [], lvals, h => by
      simp_all [denoteLVals?]
      subst lvals
      exact DenotesLVals.clvalsEmpty
  | .node "clvalsCons" [headTree, tailTree], lvals, h => by
      cases hhead : denoteLVal? headTree with
      | none =>
          simp [denoteLVals?, hhead] at h
      | some head =>
          cases htail : denoteLValsTail? tailTree with
          | none =>
              simp [denoteLVals?, hhead, htail] at h
          | some tail =>
              simp [denoteLVals?, hhead, htail] at h
              subst lvals
              exact DenotesLVals.clvalsCons
                (denoteLVal?_sound hhead)
                (denoteLValsTail?_sound htail)
  | tree, lvals, h => by
      unfold denoteLVals? at h
      split at h
      · simp at h
        subst lvals
        exact DenotesLVals.clvalsEmpty
      · rename_i headTree tailTree
        cases hhead : denoteLVal? headTree with
        | none =>
            simp [hhead] at h
        | some head =>
            cases htail : denoteLValsTail? tailTree with
            | none =>
                simp [hhead, htail] at h
            | some tail =>
                simp [hhead, htail] at h
                subst lvals
                exact DenotesLVals.clvalsCons
                  (denoteLVal?_sound hhead)
                  (denoteLValsTail?_sound htail)
      · simp at h

theorem denoteLValsTail?_sound :
    ∀ {tree : Tree Tok} {lvals : List LVal},
      denoteLValsTail? tree = some lvals →
        DenotesLValsTail tree lvals
  | .node "clvalsTailEmpty" [], lvals, h => by
      simp_all [denoteLValsTail?]
      subst lvals
      exact DenotesLValsTail.clvalsTailEmpty
  | .node "clvalsTailCons" [.token .comma, headTree, tailTree], lvals, h => by
      cases hhead : denoteLVal? headTree with
      | none =>
          simp [denoteLValsTail?, hhead] at h
      | some head =>
          cases htail : denoteLValsTail? tailTree with
          | none =>
              simp [denoteLValsTail?, hhead, htail] at h
          | some tail =>
              simp [denoteLValsTail?, hhead, htail] at h
              subst lvals
              exact DenotesLValsTail.clvalsTailCons
                (denoteLVal?_sound hhead)
                (denoteLValsTail?_sound htail)
  | tree, lvals, h => by
      unfold denoteLValsTail? at h
      split at h
      · simp at h
        subst lvals
        exact DenotesLValsTail.clvalsTailEmpty
      · rename_i headTree tailTree
        cases hhead : denoteLVal? headTree with
        | none =>
            simp [hhead] at h
        | some head =>
            cases htail : denoteLValsTail? tailTree with
            | none =>
                simp [hhead, htail] at h
            | some tail =>
                simp [hhead, htail] at h
                subst lvals
                exact DenotesLValsTail.clvalsTailCons
                  (denoteLVal?_sound hhead)
                  (denoteLValsTail?_sound htail)
      · simp at h

theorem denoteTerm?_sound :
    ∀ {tree : Tree Tok} {term : Term},
      denoteTerm? tree = some term → DenotesTerm tree term
  | .node "ctermUnit" [.token .unit], term, h => by
      simp_all [denoteTerm?]
      subst term
      exact DenotesTerm.ctermUnit
  | .node "ctermInt" [.token (.num n)], term, h => by
      simp_all [denoteTerm?]
      subst term
      exact DenotesTerm.ctermInt
  | .node "ctermTrue" [.token .trueLit], term, h => by
      simp_all [denoteTerm?]
      subst term
      exact DenotesTerm.ctermTrue
  | .node "ctermFalse" [.token .falseLit], term, h => by
      simp_all [denoteTerm?]
      subst term
      exact DenotesTerm.ctermFalse
  | .node "ctermBlock"
      [.token .block, .token (.lifetime lifetime), .token .lbrace,
        termsTree, .token .rbrace], term, h => by
      cases hterms : denoteTerms? termsTree with
      | none =>
          simp [denoteTerm?, hterms] at h
      | some terms =>
          simp [denoteTerm?, hterms] at h
          subst term
          exact DenotesTerm.ctermBlock
            (denoteTerms?_sound hterms)
  | .node "ctermLetMut"
      [.token .letKw, .token .mutKw, .token (.ident name), .token .assign,
        initialiserTree], term, h => by
      cases hinitialiser : denoteTerm? initialiserTree with
      | none =>
          simp [denoteTerm?, hinitialiser] at h
      | some initialiser =>
          simp [denoteTerm?, hinitialiser] at h
          subst term
          exact DenotesTerm.ctermLetMut
            (denoteTerm?_sound hinitialiser)
  | .node "ctermAssign" [lhsTree, .token .assign, rhsTree], term, h => by
      cases hlhs : denoteLVal? lhsTree with
      | none =>
          simp [denoteTerm?, hlhs] at h
      | some lhs =>
          cases hrhs : denoteTerm? rhsTree with
          | none =>
              simp [denoteTerm?, hlhs, hrhs] at h
          | some rhs =>
              simp [denoteTerm?, hlhs, hrhs] at h
              subst term
              exact DenotesTerm.ctermAssign
                (denoteLVal?_sound hlhs)
                (denoteTerm?_sound hrhs)
  | .node "ctermBox" [.token .box, operandTree], term, h => by
      cases hoperand : denoteTerm? operandTree with
      | none =>
          simp [denoteTerm?, hoperand] at h
      | some operand =>
          simp [denoteTerm?, hoperand] at h
          subst term
          exact DenotesTerm.ctermBox
            (denoteTerm?_sound hoperand)
  | .node "ctermBorrowShared" [.token .amp, operandTree], term, h => by
      cases hoperand : denoteLVal? operandTree with
      | none =>
          simp [denoteTerm?, hoperand] at h
      | some operand =>
          simp [denoteTerm?, hoperand] at h
          subst term
          exact DenotesTerm.ctermBorrowShared
            (denoteLVal?_sound hoperand)
  | .node "ctermBorrowMut" [.token .ampMut, operandTree], term, h => by
      cases hoperand : denoteLVal? operandTree with
      | none =>
          simp [denoteTerm?, hoperand] at h
      | some operand =>
          simp [denoteTerm?, hoperand] at h
          subst term
          exact DenotesTerm.ctermBorrowMut
            (denoteLVal?_sound hoperand)
  | .node "ctermMove" [.token .moveKw, operandTree], term, h => by
      cases hoperand : denoteLVal? operandTree with
      | none =>
          simp [denoteTerm?, hoperand] at h
      | some operand =>
          simp [denoteTerm?, hoperand] at h
          subst term
          exact DenotesTerm.ctermMove
            (denoteLVal?_sound hoperand)
  | .node "ctermCopy" [.token .copyKw, operandTree], term, h => by
      cases hoperand : denoteLVal? operandTree with
      | none =>
          simp [denoteTerm?, hoperand] at h
      | some operand =>
          simp [denoteTerm?, hoperand] at h
          subst term
          exact DenotesTerm.ctermCopy
            (denoteLVal?_sound hoperand)
  | .node "ctermEq" [lhsTree, .token .eqEq, rhsTree], term, h => by
      cases hlhs : denoteTerm? lhsTree with
      | none =>
          simp [denoteTerm?, hlhs] at h
      | some lhs =>
          cases hrhs : denoteTerm? rhsTree with
          | none =>
              simp [denoteTerm?, hlhs, hrhs] at h
          | some rhs =>
              simp [denoteTerm?, hlhs, hrhs] at h
              subst term
              exact DenotesTerm.ctermEq
                (denoteTerm?_sound hlhs)
                (denoteTerm?_sound hrhs)
  | .node "ctermIte"
      [.token .ifKw, conditionTree, trueBranchTree, .token .elseKw,
        falseBranchTree], term, h => by
      cases hcondition : denoteTerm? conditionTree with
      | none =>
          simp [denoteTerm?, hcondition] at h
      | some condition =>
          cases htrue : denoteTerm? trueBranchTree with
          | none =>
              simp [denoteTerm?, hcondition, htrue] at h
          | some trueBranch =>
              cases hfalse : denoteTerm? falseBranchTree with
              | none =>
                  simp [denoteTerm?, hcondition, htrue, hfalse] at h
              | some falseBranch =>
                  simp [denoteTerm?, hcondition, htrue, hfalse] at h
                  subst term
                  exact DenotesTerm.ctermIte
                    (denoteTerm?_sound hcondition)
                    (denoteTerm?_sound htrue)
                    (denoteTerm?_sound hfalse)
  | .node "ctermWhile"
      [.token .whileKw, .token (.lifetime bodyLifetime), conditionTree,
        bodyTree], term, h => by
      cases hcondition : denoteTerm? conditionTree with
      | none =>
          simp [denoteTerm?, hcondition] at h
      | some condition =>
          cases hbody : denoteTerm? bodyTree with
          | none =>
              simp [denoteTerm?, hcondition, hbody] at h
          | some body =>
              simp [denoteTerm?, hcondition, hbody] at h
              subst term
              exact DenotesTerm.ctermWhile
                (denoteTerm?_sound hcondition)
                (denoteTerm?_sound hbody)
  | tree, term, h => by
      unfold denoteTerm? at h
      split at h
      · simp at h
        subst term
        exact DenotesTerm.ctermUnit
      · rename_i n
        simp at h
        subst term
        exact DenotesTerm.ctermInt
      · simp at h
        subst term
        exact DenotesTerm.ctermTrue
      · simp at h
        subst term
        exact DenotesTerm.ctermFalse
      · rename_i lifetime termsTree
        cases hterms : denoteTerms? termsTree with
        | none =>
            simp [hterms] at h
        | some terms =>
            simp [hterms] at h
            subst term
            exact DenotesTerm.ctermBlock
              (denoteTerms?_sound hterms)
      · rename_i name initialiserTree
        cases hinitialiser : denoteTerm? initialiserTree with
        | none =>
            simp [hinitialiser] at h
        | some initialiser =>
            simp [hinitialiser] at h
            subst term
            exact DenotesTerm.ctermLetMut
              (denoteTerm?_sound hinitialiser)
      · rename_i lhsTree rhsTree
        cases hlhs : denoteLVal? lhsTree with
        | none =>
            simp [hlhs] at h
        | some lhs =>
            cases hrhs : denoteTerm? rhsTree with
            | none =>
                simp [hlhs, hrhs] at h
            | some rhs =>
                simp [hlhs, hrhs] at h
                subst term
                exact DenotesTerm.ctermAssign
                  (denoteLVal?_sound hlhs)
                  (denoteTerm?_sound hrhs)
      · rename_i operandTree
        cases hoperand : denoteTerm? operandTree with
        | none =>
            simp [hoperand] at h
        | some operand =>
            simp [hoperand] at h
            subst term
            exact DenotesTerm.ctermBox
              (denoteTerm?_sound hoperand)
      · rename_i operandTree
        cases hoperand : denoteLVal? operandTree with
        | none =>
            simp [hoperand] at h
        | some operand =>
            simp [hoperand] at h
            subst term
            exact DenotesTerm.ctermBorrowShared
              (denoteLVal?_sound hoperand)
      · rename_i operandTree
        cases hoperand : denoteLVal? operandTree with
        | none =>
            simp [hoperand] at h
        | some operand =>
            simp [hoperand] at h
            subst term
            exact DenotesTerm.ctermBorrowMut
              (denoteLVal?_sound hoperand)
      · rename_i operandTree
        cases hoperand : denoteLVal? operandTree with
        | none =>
            simp [hoperand] at h
        | some operand =>
            simp [hoperand] at h
            subst term
            exact DenotesTerm.ctermMove
              (denoteLVal?_sound hoperand)
      · rename_i operandTree
        cases hoperand : denoteLVal? operandTree with
        | none =>
            simp [hoperand] at h
        | some operand =>
            simp [hoperand] at h
            subst term
            exact DenotesTerm.ctermCopy
              (denoteLVal?_sound hoperand)
      · rename_i lhsTree rhsTree
        cases hlhs : denoteTerm? lhsTree with
        | none =>
            simp [hlhs] at h
        | some lhs =>
            cases hrhs : denoteTerm? rhsTree with
            | none =>
                simp [hlhs, hrhs] at h
            | some rhs =>
                simp [hlhs, hrhs] at h
                subst term
                exact DenotesTerm.ctermEq
                  (denoteTerm?_sound hlhs)
                  (denoteTerm?_sound hrhs)
      · rename_i conditionTree trueBranchTree falseBranchTree
        cases hcondition : denoteTerm? conditionTree with
        | none =>
            simp [hcondition] at h
        | some condition =>
            cases htrue : denoteTerm? trueBranchTree with
            | none =>
                simp [hcondition, htrue] at h
            | some trueBranch =>
                cases hfalse : denoteTerm? falseBranchTree with
                | none =>
                    simp [hcondition, htrue, hfalse] at h
                | some falseBranch =>
                    simp [hcondition, htrue, hfalse] at h
                    subst term
                    exact DenotesTerm.ctermIte
                      (denoteTerm?_sound hcondition)
                      (denoteTerm?_sound htrue)
                      (denoteTerm?_sound hfalse)
      · rename_i bodyLifetime conditionTree bodyTree
        cases hcondition : denoteTerm? conditionTree with
        | none =>
            simp [hcondition] at h
        | some condition =>
            cases hbody : denoteTerm? bodyTree with
            | none =>
                simp [hcondition, hbody] at h
            | some body =>
                simp [hcondition, hbody] at h
                subst term
                exact DenotesTerm.ctermWhile
                  (denoteTerm?_sound hcondition)
                  (denoteTerm?_sound hbody)
      · simp at h

theorem denoteTerms?_sound :
    ∀ {tree : Tree Tok} {terms : List Term},
      denoteTerms? tree = some terms → DenotesTerms tree terms
  | .node "ctermsEmpty" [], terms, h => by
      simp_all [denoteTerms?]
      subst terms
      exact DenotesTerms.ctermsEmpty
  | .node "ctermsCons" [headTree, tailTree], terms, h => by
      cases hhead : denoteTerm? headTree with
      | none =>
          simp [denoteTerms?, hhead] at h
      | some head =>
          cases htail : denoteTermsTail? tailTree with
          | none =>
              simp [denoteTerms?, hhead, htail] at h
          | some tail =>
              simp [denoteTerms?, hhead, htail] at h
              subst terms
              exact DenotesTerms.ctermsCons
                (denoteTerm?_sound hhead)
                (denoteTermsTail?_sound htail)
  | tree, terms, h => by
      unfold denoteTerms? at h
      split at h
      · simp at h
        subst terms
        exact DenotesTerms.ctermsEmpty
      · rename_i headTree tailTree
        cases hhead : denoteTerm? headTree with
        | none =>
            simp [hhead] at h
        | some head =>
            cases htail : denoteTermsTail? tailTree with
            | none =>
                simp [hhead, htail] at h
            | some tail =>
                simp [hhead, htail] at h
                subst terms
                exact DenotesTerms.ctermsCons
                  (denoteTerm?_sound hhead)
                  (denoteTermsTail?_sound htail)
      · simp at h

theorem denoteTermsTail?_sound :
    ∀ {tree : Tree Tok} {terms : List Term},
      denoteTermsTail? tree = some terms →
        DenotesTermsTail tree terms
  | .node "ctermsTailEmpty" [], terms, h => by
      simp_all [denoteTermsTail?]
      subst terms
      exact DenotesTermsTail.ctermsTailEmpty
  | .node "ctermsTailCons" [.token .comma, headTree, tailTree], terms, h => by
      cases hhead : denoteTerm? headTree with
      | none =>
          simp [denoteTermsTail?, hhead] at h
      | some head =>
          cases htail : denoteTermsTail? tailTree with
          | none =>
              simp [denoteTermsTail?, hhead, htail] at h
          | some tail =>
              simp [denoteTermsTail?, hhead, htail] at h
              subst terms
              exact DenotesTermsTail.ctermsTailCons
                (denoteTerm?_sound hhead)
                (denoteTermsTail?_sound htail)
  | tree, terms, h => by
      unfold denoteTermsTail? at h
      split at h
      · simp at h
        subst terms
        exact DenotesTermsTail.ctermsTailEmpty
      · rename_i headTree tailTree
        cases hhead : denoteTerm? headTree with
        | none =>
            simp [hhead] at h
        | some head =>
            cases htail : denoteTermsTail? tailTree with
            | none =>
                simp [hhead, htail] at h
            | some tail =>
                simp [hhead, htail] at h
                subst terms
                exact DenotesTermsTail.ctermsTailCons
                  (denoteTerm?_sound hhead)
                  (denoteTermsTail?_sound htail)
      · simp at h

end

mutual

theorem denoteTy?_complete_of_denotes :
    ∀ {tree : Tree Tok} {ty : Ty},
      DenotesTy tree ty → denoteTy? tree = some ty := by
  intro tree ty h
  cases h with
  | ctyUnit =>
      rfl
  | ctyInt =>
      rfl
  | ctyBool =>
      rfl
  | ctyBorrowShared htargets =>
      simp [denoteTy?, denoteLVals?_complete_of_denotes htargets]
  | ctyBorrowMut htargets =>
      simp [denoteTy?, denoteLVals?_complete_of_denotes htargets]
  | ctyBox helement =>
      simp [denoteTy?, denoteTy?_complete_of_denotes helement]

theorem denoteLVal?_complete_of_denotes :
    ∀ {tree : Tree Tok} {lval : LVal},
      DenotesLVal tree lval → denoteLVal? tree = some lval := by
  intro tree lval h
  cases h with
  | clvalVar =>
      rfl
  | clvalDeref hoperand =>
      simp [denoteLVal?, denoteLVal?_complete_of_denotes hoperand]

theorem denoteLVals?_complete_of_denotes :
    ∀ {tree : Tree Tok} {lvals : List LVal},
      DenotesLVals tree lvals → denoteLVals? tree = some lvals := by
  intro tree lvals h
  cases h with
  | clvalsEmpty =>
      rfl
  | clvalsCons hhead htail =>
      simp [denoteLVals?, denoteLVal?_complete_of_denotes hhead,
        denoteLValsTail?_complete_of_denotes htail]

theorem denoteLValsTail?_complete_of_denotes :
    ∀ {tree : Tree Tok} {lvals : List LVal},
      DenotesLValsTail tree lvals →
        denoteLValsTail? tree = some lvals := by
  intro tree lvals h
  cases h with
  | clvalsTailEmpty =>
      rfl
  | clvalsTailCons hhead htail =>
      simp [denoteLValsTail?, denoteLVal?_complete_of_denotes hhead,
        denoteLValsTail?_complete_of_denotes htail]

theorem denoteTerm?_complete_of_denotes :
    ∀ {tree : Tree Tok} {term : Term},
      DenotesTerm tree term → denoteTerm? tree = some term := by
  intro tree term h
  cases h with
  | ctermUnit =>
      rfl
  | ctermInt =>
      rfl
  | ctermTrue =>
      rfl
  | ctermFalse =>
      rfl
  | ctermBlock hterms =>
      simp [denoteTerm?, denoteTerms?_complete_of_denotes hterms]
  | ctermLetMut hinitialiser =>
      simp [denoteTerm?, denoteTerm?_complete_of_denotes hinitialiser]
  | ctermAssign hlhs hrhs =>
      simp [denoteTerm?, denoteLVal?_complete_of_denotes hlhs,
        denoteTerm?_complete_of_denotes hrhs]
  | ctermBox hoperand =>
      simp [denoteTerm?, denoteTerm?_complete_of_denotes hoperand]
  | ctermBorrowShared hoperand =>
      simp [denoteTerm?, denoteLVal?_complete_of_denotes hoperand]
  | ctermBorrowMut hoperand =>
      simp [denoteTerm?, denoteLVal?_complete_of_denotes hoperand]
  | ctermMove hoperand =>
      simp [denoteTerm?, denoteLVal?_complete_of_denotes hoperand]
  | ctermCopy hoperand =>
      simp [denoteTerm?, denoteLVal?_complete_of_denotes hoperand]
  | ctermEq hlhs hrhs =>
      simp [denoteTerm?, denoteTerm?_complete_of_denotes hlhs,
        denoteTerm?_complete_of_denotes hrhs]
  | ctermIte hcondition htrue hfalse =>
      simp [denoteTerm?, denoteTerm?_complete_of_denotes hcondition,
        denoteTerm?_complete_of_denotes htrue,
        denoteTerm?_complete_of_denotes hfalse]
  | ctermWhile hcondition hbody =>
      simp [denoteTerm?, denoteTerm?_complete_of_denotes hcondition,
        denoteTerm?_complete_of_denotes hbody]

theorem denoteTerms?_complete_of_denotes :
    ∀ {tree : Tree Tok} {terms : List Term},
      DenotesTerms tree terms → denoteTerms? tree = some terms := by
  intro tree terms h
  cases h with
  | ctermsEmpty =>
      rfl
  | ctermsCons hhead htail =>
      simp [denoteTerms?, denoteTerm?_complete_of_denotes hhead,
        denoteTermsTail?_complete_of_denotes htail]

theorem denoteTermsTail?_complete_of_denotes :
    ∀ {tree : Tree Tok} {terms : List Term},
      DenotesTermsTail tree terms →
        denoteTermsTail? tree = some terms := by
  intro tree terms h
  cases h with
  | ctermsTailEmpty =>
      rfl
  | ctermsTailCons hhead htail =>
      simp [denoteTermsTail?, denoteTerm?_complete_of_denotes hhead,
        denoteTermsTail?_complete_of_denotes htail]

end

set_option linter.unusedSimpArgs false in
theorem checkedLValTree_denote_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .clval tree = Bool.true) :
    ∃ lval, denoteLVal? tree = some lval := by
  let completeAt : Tree Tok → Prop := fun tree =>
    CheckableGrammar.checkTree checkableGrammar .clval tree = Bool.true →
      ∃ lval, denoteLVal? tree = some lval
  have htree : ∀ tree : Tree Tok, completeAt tree := by
    refine Tree.rec (Tok := Tok)
      (motive_1 := completeAt)
      (motive_2 := fun children =>
        ∀ child, child ∈ children → completeAt child)
      ?token ?node ?nil ?cons
    · intro tok h
      simp [completeAt, CheckableGrammar.checkTree] at h
    · intro ruleName children ih h
      simp [completeAt, CheckableGrammar.checkTree, checkableGrammar,
        grammar, ctyUnitRule, ctyIntRule, ctyBoolRule,
        ctyBorrowSharedRule, ctyBorrowMutRule, ctyBoxRule,
        clvalVarRule, clvalDerefRule, ctermUnitRule, ctermIntRule,
        ctermTrueRule, ctermFalseRule, ctermBlockRule, ctermLetMutRule,
        ctermAssignRule, ctermBoxRule, ctermBorrowSharedRule,
        ctermBorrowMutRule, ctermMoveRule, ctermCopyRule, ctermEqRule,
        ctermIteRule, ctermWhileRule, clvalsEmptyRule, clvalsConsRule,
        clvalsTailEmptyRule, clvalsTailConsRule, ctermsEmptyRule,
        ctermsConsRule, ctermsTailEmptyRule, ctermsTailConsRule] at h
      rcases h with hvar | hderef
      · rcases hvar with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil =>
            simp [CheckableGrammar.checkSeq] at hseq
        | cons child rest =>
            cases child with
            | token tok =>
                cases rest with
                | nil =>
                    cases tok <;>
                      simp [CheckableGrammar.checkSeq, acceptsBool,
                        denoteLVal?] at hseq ⊢
                | cons _ _ =>
                    simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ =>
                simp [CheckableGrammar.checkSeq] at hseq
      · rcases hderef with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil =>
            simp [CheckableGrammar.checkSeq] at hseq
        | cons child rest =>
            cases child with
            | token tok =>
                cases rest with
                | nil =>
                    simp [CheckableGrammar.checkSeq] at hseq
                | cons operand rest2 =>
                    cases rest2 with
                    | nil =>
                        cases tok <;>
                          simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                        have hop :
                            CheckableGrammar.checkTree checkableGrammar
                              .clval operand = Bool.true :=
                          hseq
                        obtain ⟨operand', hopen⟩ := ih operand (by simp) hop
                        exact ⟨SyntaxCtor.clvalDeref_ctor operand', by
                          simp [denoteLVal?, hopen]⟩
                    | cons _ _ =>
                        simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ =>
                simp [CheckableGrammar.checkSeq] at hseq
    · intro child hmem
      simp at hmem
    · intro head tail hhead htail child hmem
      simp at hmem
      rcases hmem with rfl | hmem
      · exact hhead
      · exact htail child hmem
  exact htree tree hchecked

theorem checkedLValTree_denotes_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .clval tree = Bool.true) :
    ∃ lval, DenotesLVal tree lval := by
  obtain ⟨lval, hdenote⟩ := checkedLValTree_denote_exists hchecked
  exact ⟨lval, denoteLVal?_sound hdenote⟩

abbrev LValListDecodeCompleteAt (tree : Tree Tok) : Prop :=
  (CheckableGrammar.checkTree checkableGrammar .clvals tree = Bool.true →
    ∃ lvals, denoteLVals? tree = some lvals) ∧
  (CheckableGrammar.checkTree checkableGrammar .clvalsTail tree = Bool.true →
    ∃ lvals, denoteLValsTail? tree = some lvals)

set_option linter.unusedSimpArgs false in
theorem checkedLValListDecodeCompleteAt :
    ∀ tree : Tree Tok, LValListDecodeCompleteAt tree := by
  refine Tree.rec (Tok := Tok)
    (motive_1 := LValListDecodeCompleteAt)
    (motive_2 := fun children =>
      ∀ child, child ∈ children → LValListDecodeCompleteAt child)
    ?token ?node ?nil ?cons
  · intro tok
    unfold LValListDecodeCompleteAt
    simp [CheckableGrammar.checkTree]
  · intro ruleName children ih
    unfold LValListDecodeCompleteAt
    constructor
    · intro h
      simp [CheckableGrammar.checkTree, checkableGrammar, grammar,
        ctyUnitRule, ctyIntRule, ctyBoolRule, ctyBorrowSharedRule,
        ctyBorrowMutRule, ctyBoxRule, clvalVarRule, clvalDerefRule,
        ctermUnitRule, ctermIntRule, ctermTrueRule, ctermFalseRule,
        ctermBlockRule, ctermLetMutRule, ctermAssignRule, ctermBoxRule,
        ctermBorrowSharedRule, ctermBorrowMutRule, ctermMoveRule,
        ctermCopyRule, ctermEqRule, ctermIteRule, ctermWhileRule,
        clvalsEmptyRule, clvalsConsRule, clvalsTailEmptyRule,
        clvalsTailConsRule, ctermsEmptyRule, ctermsConsRule,
        ctermsTailEmptyRule, ctermsTailConsRule] at h
      rcases h with hempty | hcons
      · rcases hempty with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil =>
            exact ⟨[], rfl⟩
        | cons _ _ =>
            simp [CheckableGrammar.checkSeq] at hseq
      · rcases hcons with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil =>
            simp [CheckableGrammar.checkSeq] at hseq
        | cons head rest =>
            cases rest with
            | nil =>
                simp [CheckableGrammar.checkSeq] at hseq
            | cons tail rest2 =>
                cases rest2 with
                | nil =>
                    simp [CheckableGrammar.checkSeq] at hseq
                    rcases hseq with ⟨hhead, htail⟩
                    obtain ⟨head', hhead'⟩ :=
                      checkedLValTree_denote_exists hhead
                    obtain ⟨tail', htail'⟩ := (ih tail (by simp)).2 htail
                    exact ⟨head' :: tail', by
                      simp [denoteLVals?, hhead', htail']⟩
                | cons _ _ =>
                    simp [CheckableGrammar.checkSeq] at hseq
    · intro h
      simp [CheckableGrammar.checkTree, checkableGrammar, grammar,
        ctyUnitRule, ctyIntRule, ctyBoolRule, ctyBorrowSharedRule,
        ctyBorrowMutRule, ctyBoxRule, clvalVarRule, clvalDerefRule,
        ctermUnitRule, ctermIntRule, ctermTrueRule, ctermFalseRule,
        ctermBlockRule, ctermLetMutRule, ctermAssignRule, ctermBoxRule,
        ctermBorrowSharedRule, ctermBorrowMutRule, ctermMoveRule,
        ctermCopyRule, ctermEqRule, ctermIteRule, ctermWhileRule,
        clvalsEmptyRule, clvalsConsRule, clvalsTailEmptyRule,
        clvalsTailConsRule, ctermsEmptyRule, ctermsConsRule,
        ctermsTailEmptyRule, ctermsTailConsRule] at h
      rcases h with hempty | hcons
      · rcases hempty with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil =>
            exact ⟨[], rfl⟩
        | cons _ _ =>
            simp [CheckableGrammar.checkSeq] at hseq
      · rcases hcons with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil =>
            simp [CheckableGrammar.checkSeq] at hseq
        | cons comma rest =>
            cases comma with
            | token tok =>
                cases rest with
                | nil =>
                    simp [CheckableGrammar.checkSeq] at hseq
                | cons head rest2 =>
                    cases rest2 with
                    | nil =>
                        simp [CheckableGrammar.checkSeq] at hseq
                    | cons tail rest3 =>
                        cases rest3 with
                        | nil =>
                            cases tok <;>
                              simp [CheckableGrammar.checkSeq,
                                acceptsBool] at hseq
                            rcases hseq with ⟨hhead, htail⟩
                            obtain ⟨head', hhead'⟩ :=
                              checkedLValTree_denote_exists hhead
                            obtain ⟨tail', htail'⟩ :=
                              (ih tail (by simp)).2 htail
                            exact ⟨head' :: tail', by
                              simp [denoteLValsTail?, hhead', htail']⟩
                        | cons _ _ =>
                            simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ =>
                simp [CheckableGrammar.checkSeq] at hseq
  · intro child hmem
    simp at hmem
  · intro head tail hhead htail child hmem
    simp at hmem
    rcases hmem with rfl | hmem
    · exact hhead
    · exact htail child hmem

theorem checkedLValsTree_denote_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .clvals tree = Bool.true) :
    ∃ lvals, denoteLVals? tree = some lvals :=
  (checkedLValListDecodeCompleteAt tree).1 hchecked

theorem checkedLValsTailTree_denote_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .clvalsTail tree =
        Bool.true) :
    ∃ lvals, denoteLValsTail? tree = some lvals :=
  (checkedLValListDecodeCompleteAt tree).2 hchecked

theorem checkedLValsTree_denotes_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .clvals tree = Bool.true) :
    ∃ lvals, DenotesLVals tree lvals := by
  obtain ⟨lvals, hdenote⟩ := checkedLValsTree_denote_exists hchecked
  exact ⟨lvals, denoteLVals?_sound hdenote⟩

theorem checkedLValsTailTree_denotes_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .clvalsTail tree =
        Bool.true) :
    ∃ lvals, DenotesLValsTail tree lvals := by
  obtain ⟨lvals, hdenote⟩ := checkedLValsTailTree_denote_exists hchecked
  exact ⟨lvals, denoteLValsTail?_sound hdenote⟩

def CodeCompletesTerm (pref : List Tok) (term : Term) : Prop :=
  ∃ suffix tree,
    Derives grammar .cterm (pref ++ suffix) tree ∧ DenotesTerm tree term

structure ValidTermCompletion (pref : List Tok) where
  suffix : List Tok
  tree : Tree Tok
  term : Term
  derives : Derives grammar .cterm (pref ++ suffix) tree
  denotes : DenotesTerm tree term

namespace ValidTermCompletion

def completedTokens {pref : List Tok} (completion : ValidTermCompletion pref) :
    List Tok :=
  pref ++ completion.suffix

theorem codeCompletes {pref : List Tok}
    (completion : ValidTermCompletion pref) :
    CodeCompletesTerm pref completion.term :=
  ⟨completion.suffix, completion.tree, completion.derives,
    completion.denotes⟩

end ValidTermCompletion

structure CompleteTermParser where
  complete : (pref : List Tok) → Option (ValidTermCompletion pref)
  complete_if_completable :
    ∀ pref, (∃ term, CodeCompletesTerm pref term) →
      ∃ result, complete pref = some result

namespace CompleteTermParser

def completedTokens? (parser : CompleteTermParser) (pref : List Tok) :
    Option (List Tok) :=
  match parser.complete pref with
  | none => none
  | some result => some result.completedTokens

theorem completedTokens?_sound (parser : CompleteTermParser)
    {pref tokens : List Tok}
    (hresult : parser.completedTokens? pref = some tokens) :
    ∃ suffix tree term,
      tokens = pref ++ suffix ∧
      Derives grammar .cterm tokens tree ∧
      DenotesTerm tree term := by
  unfold completedTokens? at hresult
  cases hcomplete : parser.complete pref with
  | none =>
      simp [hcomplete] at hresult
  | some result =>
      simp [hcomplete, ValidTermCompletion.completedTokens] at hresult
      subst tokens
      exact ⟨result.suffix, result.tree, result.term, rfl,
        result.derives, result.denotes⟩

end CompleteTermParser

noncomputable def completeTermBySpec? (pref : List Tok) :
    Option (ValidTermCompletion pref) := by
  classical
  exact
    if h : ∃ result : ValidTermCompletion pref, True then
      some (Classical.choose h)
    else
      none

noncomputable def completeTermParserBySpec : CompleteTermParser where
  complete pref := completeTermBySpec? pref
  complete_if_completable := by
    intro pref hcomplete
    classical
    have hvalid : ∃ result : ValidTermCompletion pref, True := by
      obtain ⟨term, suffix, tree, hderive, hdenotes⟩ := hcomplete
      exact ⟨{
        suffix := suffix
        tree := tree
        term := term
        derives := hderive
        denotes := hdenotes
      }, trivial⟩
    exact ⟨Classical.choose hvalid, by
      unfold completeTermBySpec?
      simp [hvalid]⟩

noncomputable def rawCtermParserBySpec :
    CheckableGrammar.RawCompleteParser checkableGrammar .cterm :=
  CheckableGrammar.RawCompleteParser.bySpec checkableGrammar .cterm

noncomputable def ctermParserFromRawSpec :
    CompleteParser checkableGrammar.toGrammar .cterm :=
  rawCtermParserBySpec.toCompleteParser

def xTok : Tok := .ident "x"

def moveXPrefix : List Tok :=
  [.moveKw, xTok]

def xPrefix : List Tok :=
  [xTok]

def moveStarPrefix : List Tok :=
  [.moveKw, .star]

def clvalXTree : Tree Tok :=
  .node "clvalVar" [.token xTok]

def moveXTree : Tree Tok :=
  .node "ctermMove" [.token .moveKw, clvalXTree]

def moveXEqMoveXTree : Tree Tok :=
  .node "ctermEq" [moveXTree, .token .eqEq, moveXTree]

def assignXMoveXTree : Tree Tok :=
  .node "ctermAssign" [clvalXTree, .token .assign, moveXTree]

theorem clvalX_derives :
    Derives grammar .clval [xTok] clvalXTree := by
  change Derives grammar .clval [xTok]
    (.node "clvalVar" [.token xTok])
  refine Derives.rule (rule := clvalVarRule) ?_ rfl ?_
  · simp [grammar, clvalVarRule]
  · simp [clvalVarRule, xTok]
    exact DerivesSeq.token (by simp [grammar, accepts]) DerivesSeq.nil

theorem moveX_derives :
    Derives grammar .cterm moveXPrefix moveXTree := by
  change Derives grammar .cterm moveXPrefix
    (.node "ctermMove" [.token .moveKw, clvalXTree])
  refine Derives.rule (rule := ctermMoveRule) ?_ rfl ?_
  · simp [grammar, ctermMoveRule]
  · simp [moveXPrefix, ctermMoveRule]
    exact DerivesSeq.token (by simp [grammar, accepts])
      (DerivesSeq.cat clvalX_derives DerivesSeq.nil)

theorem moveXEqMoveX_derives :
    Derives grammar .cterm (moveXPrefix ++ ([Tok.eqEq] ++ moveXPrefix))
      moveXEqMoveXTree := by
  change Derives grammar .cterm (moveXPrefix ++ ([Tok.eqEq] ++ moveXPrefix))
    (.node "ctermEq" [moveXTree, .token .eqEq, moveXTree])
  refine Derives.rule (rule := ctermEqRule) ?_ rfl ?_
  · simp [grammar, ctermEqRule]
  · simp [ctermEqRule]
    exact DerivesSeq.cat moveX_derives
      (DerivesSeq.token (by simp [grammar, accepts])
        (DerivesSeq.cat moveX_derives DerivesSeq.nil))

theorem assignXMoveX_derives :
    Derives grammar .cterm (xPrefix ++ ([Tok.assign] ++ moveXPrefix))
      assignXMoveXTree := by
  change Derives grammar .cterm (xPrefix ++ ([Tok.assign] ++ moveXPrefix))
    (.node "ctermAssign" [clvalXTree, .token .assign, moveXTree])
  refine Derives.rule (rule := ctermAssignRule) ?_ rfl ?_
  · simp [grammar, ctermAssignRule]
  · simp [ctermAssignRule, xPrefix]
    exact DerivesSeq.cat clvalX_derives
      (DerivesSeq.token (by simp [grammar, accepts])
        (DerivesSeq.cat moveX_derives DerivesSeq.nil))

def rawMoveXEqMoveXCompletion : CheckableGrammar.RawCompletion Tok :=
  { suffix := [Tok.eqEq] ++ moveXPrefix
    tree := moveXEqMoveXTree }

theorem rawMoveXEqMoveXCompletion_valid :
    CheckableGrammar.RawCompletion.valid checkableGrammar .cterm moveXPrefix
      rawMoveXEqMoveXCompletion = Bool.true := by
  native_decide

def checkedMoveXEqMoveXCompletion :
    ValidCompletion checkableGrammar.toGrammar .cterm moveXPrefix :=
  rawMoveXEqMoveXCompletion.toValidCompletion checkableGrammar
    rawMoveXEqMoveXCompletion_valid

def rawAssignXMoveXCompletion : CheckableGrammar.RawCompletion Tok :=
  { suffix := [Tok.assign] ++ moveXPrefix
    tree := assignXMoveXTree }

theorem rawAssignXMoveXCompletion_valid :
    CheckableGrammar.RawCompletion.valid checkableGrammar .cterm xPrefix
      rawAssignXMoveXCompletion = Bool.true := by
  native_decide

def checkedAssignXMoveXCompletion :
    ValidCompletion checkableGrammar.toGrammar .cterm xPrefix :=
  rawAssignXMoveXCompletion.toValidCompletion checkableGrammar
    rawAssignXMoveXCompletion_valid

def moveXDoneItem : Item Cat Terminal :=
  { rule := ctermMoveRule, dot := 2 }

def moveXDoneState :
    CheckableGrammar.CheckedBoundaryState checkableGrammar :=
  { item := moveXDoneItem
    item_mem := by native_decide
    doneChildren := [.token .moveKw, clvalXTree]
    checkedBefore := by native_decide }

theorem moveXDoneState_pref :
    moveXDoneState.pref = moveXPrefix := by
  native_decide

def rawMoveXDoneDefaultCompletion : CheckableGrammar.RawCompletion Tok :=
  moveXDoneState.rawCompletion defaults

theorem rawMoveXDoneDefaultCompletion_valid :
    CheckableGrammar.RawCompletion.valid checkableGrammar .cterm moveXPrefix
      rawMoveXDoneDefaultCompletion = Bool.true := by
  have h := moveXDoneState.rawCompletion_valid defaults
  have h' :
      CheckableGrammar.RawCompletion.valid checkableGrammar .cterm
        moveXDoneState.pref rawMoveXDoneDefaultCompletion = Bool.true := by
    simpa [rawMoveXDoneDefaultCompletion, moveXDoneState, moveXDoneItem,
      ctermMoveRule] using h
  simpa [moveXDoneState_pref] using h'

def checkedMoveXDoneDefaultCompletion :
    ValidCompletion checkableGrammar.toGrammar .cterm moveXPrefix :=
  rawMoveXDoneDefaultCompletion.toValidCompletion checkableGrammar
    rawMoveXDoneDefaultCompletion_valid

def moveXDoneFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm :=
  CheckableGrammar.CheckedFrontierState.boundary moveXDoneItem
    (by native_decide) [.token .moveKw, clvalXTree] (by native_decide)

theorem moveXDoneFrontierState_pref :
    moveXDoneFrontierState.pref = moveXPrefix := by
  native_decide

def moveXEqAfterLhsItem : Item Cat Terminal :=
  { rule := ctermEqRule, dot := 1 }

def moveXEqAfterLhsState :
    CheckableGrammar.CheckedBoundaryState checkableGrammar :=
  { item := moveXEqAfterLhsItem
    item_mem := by native_decide
    doneChildren := [moveXTree]
    checkedBefore := by native_decide }

theorem moveXEqAfterLhsState_pref :
    moveXEqAfterLhsState.pref = moveXPrefix := by
  native_decide

def rawMoveXEqDefaultCompletion : CheckableGrammar.RawCompletion Tok :=
  moveXEqAfterLhsState.rawCompletion defaults

theorem rawMoveXEqDefaultCompletion_valid :
    CheckableGrammar.RawCompletion.valid checkableGrammar .cterm moveXPrefix
      rawMoveXEqDefaultCompletion = Bool.true := by
  have h := moveXEqAfterLhsState.rawCompletion_valid defaults
  have h' :
      CheckableGrammar.RawCompletion.valid checkableGrammar .cterm
        moveXEqAfterLhsState.pref rawMoveXEqDefaultCompletion =
          Bool.true := by
    simpa [rawMoveXEqDefaultCompletion, moveXEqAfterLhsState,
      moveXEqAfterLhsItem, ctermEqRule] using h
  simpa [moveXEqAfterLhsState_pref] using h'

def checkedMoveXEqDefaultCompletion :
    ValidCompletion checkableGrammar.toGrammar .cterm moveXPrefix :=
  rawMoveXEqDefaultCompletion.toValidCompletion checkableGrammar
    rawMoveXEqDefaultCompletion_valid

def moveXEqAfterLhsFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm :=
  CheckableGrammar.CheckedFrontierState.boundary moveXEqAfterLhsItem
    (by native_decide) [moveXTree] (by native_decide)

theorem moveXEqAfterLhsFrontierState_pref :
    moveXEqAfterLhsFrontierState.pref = moveXPrefix := by
  native_decide

def xAssignAfterLhsItem : Item Cat Terminal :=
  { rule := ctermAssignRule, dot := 1 }

def xAssignAfterLhsState :
    CheckableGrammar.CheckedBoundaryState checkableGrammar :=
  { item := xAssignAfterLhsItem
    item_mem := by native_decide
    doneChildren := [clvalXTree]
    checkedBefore := by native_decide }

theorem xAssignAfterLhsState_pref :
    xAssignAfterLhsState.pref = xPrefix := by
  native_decide

def rawXAssignDefaultCompletion : CheckableGrammar.RawCompletion Tok :=
  xAssignAfterLhsState.rawCompletion defaults

theorem rawXAssignDefaultCompletion_valid :
    CheckableGrammar.RawCompletion.valid checkableGrammar .cterm xPrefix
      rawXAssignDefaultCompletion = Bool.true := by
  have h := xAssignAfterLhsState.rawCompletion_valid defaults
  have h' :
      CheckableGrammar.RawCompletion.valid checkableGrammar .cterm
        xAssignAfterLhsState.pref rawXAssignDefaultCompletion =
          Bool.true := by
    simpa [rawXAssignDefaultCompletion, xAssignAfterLhsState,
      xAssignAfterLhsItem, ctermAssignRule] using h
  simpa [xAssignAfterLhsState_pref] using h'

def checkedXAssignDefaultCompletion :
    ValidCompletion checkableGrammar.toGrammar .cterm xPrefix :=
  rawXAssignDefaultCompletion.toValidCompletion checkableGrammar
    rawXAssignDefaultCompletion_valid

def xAssignAfterLhsFrontierState :
    CheckableGrammar.CheckedFrontierState checkableGrammar .cterm :=
  CheckableGrammar.CheckedFrontierState.boundary xAssignAfterLhsItem
    (by native_decide) [clvalXTree] (by native_decide)

theorem xAssignAfterLhsFrontierState_pref :
    xAssignAfterLhsFrontierState.pref = xPrefix := by
  native_decide

theorem generatedDefaultCompletionStrings :
    checkedMoveXDoneDefaultCompletion.completedTokens = moveXPrefix ∧
    checkedMoveXEqDefaultCompletion.completedTokens =
      moveXPrefix ++ [Tok.eqEq, Tok.unit] ∧
    checkedXAssignDefaultCompletion.completedTokens =
      xPrefix ++ [Tok.assign, Tok.unit] := by
  native_decide

def ctermFrontierStatesFuel (fuel : Nat) (pref : List Tok) :
    List (CheckableGrammar.ParsedFrontierState checkableGrammar .cterm pref) :=
  CheckableGrammar.frontierStatesFuel checkableGrammar fuel .cterm pref

theorem ctermFrontierStatesFuel_complete_checked_exact
    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm) :
    ∃ minFuel,
      ∀ fuel, minFuel ≤ fuel →
        ∃ parsed,
          parsed.state = state ∧
          parsed ∈ ctermFrontierStatesFuel fuel state.pref := by
  simpa [ctermFrontierStatesFuel] using
    CheckableGrammar.frontierStatesFuel_complete_checked_exact
      checkableGrammar state

def firstCtermRawCompletion? (fuel : Nat) (pref : List Tok) :
    Option (CheckableGrammar.RawCompletion Tok) :=
  match ctermFrontierStatesFuel fuel pref with
  | [] => none
  | parsed :: _ =>
      some (parsed.state.rawCompletion defaults)

theorem firstCtermRawCompletion?_sound {fuel : Nat} {pref : List Tok}
    {raw : CheckableGrammar.RawCompletion Tok}
    (hraw : firstCtermRawCompletion? fuel pref = some raw) :
    raw.valid checkableGrammar .cterm pref = Bool.true := by
  unfold firstCtermRawCompletion? ctermFrontierStatesFuel at hraw
  cases hstates :
      CheckableGrammar.frontierStatesFuel checkableGrammar fuel .cterm pref with
  | nil =>
      simp [hstates] at hraw
  | cons parsed rest =>
      simp [hstates] at hraw
      subst raw
      have hvalid := parsed.state.rawCompletion_valid defaults
      simpa [parsed.pref_eq] using hvalid

def firstCtermCompletedTokens? (fuel : Nat) (pref : List Tok) :
    Option (List Tok) :=
  match firstCtermRawCompletion? fuel pref with
  | none => none
  | some raw => some (pref ++ raw.suffix)

def completeTermFuel? (fuel : Nat) (pref : List Tok) :
    Option Term :=
  match CheckableGrammar.completeRawFuel? checkableGrammar defaults fuel
      .cterm pref with
  | none => none
  | some raw => denoteTerm? raw.tree

def joinSource (sep : String) : List String → String
  | [] => ""
  | part :: parts =>
      parts.foldl (fun acc part => acc ++ sep ++ part) part

def lifetimeSource (lifetime : Lifetime) : String :=
  "[" ++ joinSource ", " (lifetime.path.map fun segment =>
    toString segment) ++ "]"

def tokSource : Tok → String
  | .ctyUnit => "cty_unit"
  | .ctyInt => "cty_int"
  | .ctyBool => "cty_bool"
  | .unit => "()"
  | .trueLit => "true"
  | .falseLit => "false"
  | .amp => "&"
  | .ampMut => "&mut"
  | .lbrack => "["
  | .rbrack => "]"
  | .comma => ","
  | .box => "box"
  | .star => "*"
  | .block => "block"
  | .lbrace => "{"
  | .rbrace => "}"
  | .letKw => "let"
  | .mutKw => "mut"
  | .assign => ":="
  | .moveKw => "move"
  | .copyKw => "copy"
  | .eqEq => "=="
  | .ifKw => "if"
  | .elseKw => "else"
  | .whileKw => "while"
  | .ident name => name
  | .num value => toString value
  | .lifetime lifetime => lifetimeSource lifetime

def tokensSource (tokens : List Tok) : String :=
  joinSource " " (tokens.map tokSource)

def completeTermTokensFuel? (fuel : Nat) (pref : List Tok) :
    Option (List Tok) :=
  CheckableGrammar.completeTokensFuel? checkableGrammar defaults fuel
    .cterm pref

def completeTermSourceFuel? (fuel : Nat) (pref : List Tok) :
    Option String :=
  match completeTermTokensFuel? fuel pref with
  | none => none
  | some tokens => some (tokensSource tokens)

structure ValidTermSourceCompletion (pref : List Tok) where
  source : String
  tokens : List Tok
  suffix : List Tok
  tree : Tree Tok
  source_eq : source = tokensSource tokens
  tokens_eq : tokens = pref ++ suffix
  derives : Derives checkableGrammar.toGrammar .cterm tokens tree

namespace ValidTermSourceCompletion

theorem prefixCompletes {pref : List Tok}
    (completion : ValidTermSourceCompletion pref) :
    PrefixCompletes checkableGrammar.toGrammar .cterm pref
      completion.tree := by
  refine ⟨completion.suffix, ?_⟩
  simpa [completion.tokens_eq] using completion.derives

end ValidTermSourceCompletion

theorem firstCtermCompletedTokens?_sound {fuel : Nat} {pref tokens : List Tok}
    (htokens : firstCtermCompletedTokens? fuel pref = some tokens) :
    ∃ suffix tree,
      tokens = pref ++ suffix ∧
      Derives checkableGrammar.toGrammar .cterm tokens tree := by
  unfold firstCtermCompletedTokens? at htokens
  cases hraw : firstCtermRawCompletion? fuel pref with
  | none =>
      simp [hraw] at htokens
  | some raw =>
      simp [hraw] at htokens
      subst tokens
      have hvalid := firstCtermRawCompletion?_sound hraw
      exact ⟨raw.suffix, raw.tree, rfl,
        CheckableGrammar.RawCompletion.valid_sound checkableGrammar hvalid⟩

theorem completeTermTokensFuel?_sound {fuel : Nat} {pref tokens : List Tok}
    (htokens : completeTermTokensFuel? fuel pref = some tokens) :
    ∃ suffix tree,
      tokens = pref ++ suffix ∧
      Derives checkableGrammar.toGrammar .cterm tokens tree := by
  simpa [completeTermTokensFuel?] using
    CheckableGrammar.completeTokensFuel?_sound
      checkableGrammar defaults (cat := Cat.cterm) htokens

theorem completeTermSourceFuel?_sound {fuel : Nat} {pref : List Tok}
    {source : String}
    (hsource : completeTermSourceFuel? fuel pref = some source) :
    ∃ tokens suffix tree,
      source = tokensSource tokens ∧
      tokens = pref ++ suffix ∧
      Derives checkableGrammar.toGrammar .cterm tokens tree := by
  unfold completeTermSourceFuel? at hsource
  cases htokens : completeTermTokensFuel? fuel pref with
  | none =>
      simp [htokens] at hsource
  | some tokens =>
      simp [htokens] at hsource
      subst source
      obtain ⟨suffix, tree, htokensEq, hderive⟩ :=
        completeTermTokensFuel?_sound htokens
      exact ⟨tokens, suffix, tree, rfl, htokensEq, hderive⟩

theorem completeTermSourceFuel?_valid {fuel : Nat} {pref : List Tok}
    {source : String}
    (hsource : completeTermSourceFuel? fuel pref = some source) :
    ∃ completion : ValidTermSourceCompletion pref,
      completion.source = source := by
  obtain ⟨tokens, suffix, tree, hrender, htokens, hderive⟩ :=
    completeTermSourceFuel?_sound hsource
  exact ⟨{
    source := source
    tokens := tokens
    suffix := suffix
    tree := tree
    source_eq := hrender
    tokens_eq := htokens
    derives := hderive
  }, rfl⟩

theorem completeTermFuel?_sound {fuel : Nat} {pref : List Tok}
    {term : Term}
    (hterm : completeTermFuel? fuel pref = some term) :
    CodeCompletesTerm pref term := by
  unfold completeTermFuel? at hterm
  cases hraw :
      CheckableGrammar.completeRawFuel? checkableGrammar defaults fuel
        .cterm pref with
  | none =>
      simp [hraw] at hterm
  | some raw =>
      cases hdenotes : denoteTerm? raw.tree with
      | none =>
          simp [hraw, hdenotes] at hterm
      | some decoded =>
          simp [hraw, hdenotes] at hterm
          subst term
          have hvalid :=
            CheckableGrammar.completeRawFuel?_sound
              checkableGrammar defaults hraw
          exact ⟨raw.suffix, raw.tree,
            CheckableGrammar.RawCompletion.valid_sound
              checkableGrammar hvalid,
            denoteTerm?_sound hdenotes⟩

theorem ctermFuelCompleter_complete_of_prefixCompletes
    {pref : List Tok} {tree : Tree Tok}
    (hcomplete : PrefixCompletes checkableGrammar.toGrammar .cterm pref tree) :
    ∃ fuel tokens,
      CheckableGrammar.completeTokensFuel? checkableGrammar defaults fuel
        .cterm pref = some tokens ∧
      ∃ suffix tree',
        tokens = pref ++ suffix ∧
        Derives checkableGrammar.toGrammar .cterm tokens tree' := by
  exact CheckableGrammar.completeTokensFuel?_complete_of_prefixCompletes
    checkableGrammar defaults hcomplete

theorem completeTermTokensFuel?_complete_of_prefixCompletes
    {pref : List Tok} {tree : Tree Tok}
    (hcomplete : PrefixCompletes checkableGrammar.toGrammar .cterm pref tree) :
    ∃ fuel tokens,
      completeTermTokensFuel? fuel pref = some tokens ∧
      ∃ suffix tree',
        tokens = pref ++ suffix ∧
        Derives checkableGrammar.toGrammar .cterm tokens tree' := by
  simpa [completeTermTokensFuel?] using
    ctermFuelCompleter_complete_of_prefixCompletes hcomplete

theorem completeTermSourceFuel?_complete_of_prefixCompletes
    {pref : List Tok} {tree : Tree Tok}
    (hcomplete : PrefixCompletes checkableGrammar.toGrammar .cterm pref tree) :
    ∃ fuel source tokens,
      completeTermSourceFuel? fuel pref = some source ∧
      source = tokensSource tokens ∧
      ∃ suffix tree',
        tokens = pref ++ suffix ∧
        Derives checkableGrammar.toGrammar .cterm tokens tree' := by
  obtain ⟨fuel, tokens, htokens, hcompletion⟩ :=
    completeTermTokensFuel?_complete_of_prefixCompletes hcomplete
  exact ⟨fuel, tokensSource tokens, tokens, by
    simp [completeTermSourceFuel?, htokens], rfl, hcompletion⟩

theorem completeTermSourceFuel?_complete_of_codeCompletes
    {pref : List Tok} {term : Term}
    (hcompletion : CodeCompletesTerm pref term) :
    ∃ fuel source tokens,
      completeTermSourceFuel? fuel pref = some source ∧
      source = tokensSource tokens ∧
      ∃ suffix tree,
        tokens = pref ++ suffix ∧
        Derives checkableGrammar.toGrammar .cterm tokens tree := by
  obtain ⟨suffix, tree, hderive, _hdenotes⟩ := hcompletion
  exact completeTermSourceFuel?_complete_of_prefixCompletes
    (tree := tree)
    ⟨suffix, by simpa [checkableGrammar] using hderive⟩

theorem completeTermSourceFuel?_eventually_valid_of_codeCompletes
    {pref : List Tok} {term : Term}
    (hcompletion : CodeCompletesTerm pref term) :
    ∃ fuel completion,
      completeTermSourceFuel? fuel pref = some
        (completion : ValidTermSourceCompletion pref).source := by
  obtain ⟨fuel, source, tokens, hsource, hrender, hvalid⟩ :=
    completeTermSourceFuel?_complete_of_codeCompletes hcompletion
  obtain ⟨suffix, tree, htokens, hderive⟩ := hvalid
  exact ⟨fuel, {
    source := source
    tokens := tokens
    suffix := suffix
    tree := tree
    source_eq := hrender
    tokens_eq := htokens
    derives := hderive
  }, hsource⟩

structure CompleteTermSourceParser where
  complete : Nat → List Tok → Option String
  sound :
    ∀ {fuel pref source},
      complete fuel pref = some source →
        ∃ tokens suffix tree,
          source = tokensSource tokens ∧
          tokens = pref ++ suffix ∧
          Derives checkableGrammar.toGrammar .cterm tokens tree
  complete_if_completable :
    ∀ {pref term},
      CodeCompletesTerm pref term →
        ∃ fuel source, complete fuel pref = some source

def completeTermSourceParser : CompleteTermSourceParser where
  complete := completeTermSourceFuel?
  sound := by
    intro fuel pref source hsource
    exact completeTermSourceFuel?_sound hsource
  complete_if_completable := by
    intro pref term hcompletion
    obtain ⟨fuel, source, _tokens, hsource, _hrender, _hderive⟩ :=
      completeTermSourceFuel?_complete_of_codeCompletes hcompletion
    exact ⟨fuel, source, hsource⟩

/--
If the executable source completer returns a string, that string renders a
token list extending the input prefix, and the completed token list parses as
an FW term.
-/
theorem completeTermSourceParser_sound_of_some {fuel : Nat}
    {pref : List Tok} {source : String}
    (hsource : completeTermSourceParser.complete fuel pref = some source) :
    ∃ tokens suffix tree,
      source = tokensSource tokens ∧
      tokens = pref ++ suffix ∧
      Derives checkableGrammar.toGrammar .cterm tokens tree :=
  completeTermSourceParser.sound hsource

/--
Proof-carrying version of `completeTermSourceParser_sound_of_some`.
-/
theorem completeTermSourceParser_valid_of_some {fuel : Nat}
    {pref : List Tok} {source : String}
    (hsource : completeTermSourceParser.complete fuel pref = some source) :
    ∃ completion : ValidTermSourceCompletion pref,
      completion.source = source := by
  exact completeTermSourceFuel?_valid hsource

/--
If a token prefix has any FW term completion, the executable source completer
eventually returns some valid completion string.
-/
theorem completeTermSourceParser_complete_of_codeCompletes
    {pref : List Tok} {term : Term}
    (hcompletion : CodeCompletesTerm pref term) :
    ∃ fuel source,
      completeTermSourceParser.complete fuel pref = some source :=
  completeTermSourceParser.complete_if_completable hcompletion

/--
If a token prefix has any FW term completion, the executable source completer
eventually returns a string packaged with its generated parse-tree proof.
-/
theorem completeTermSourceParser_eventually_valid_of_codeCompletes
    {pref : List Tok} {term : Term}
    (hcompletion : CodeCompletesTerm pref term) :
    ∃ fuel completion,
      completeTermSourceParser.complete fuel pref = some
        (completion : ValidTermSourceCompletion pref).source := by
  exact completeTermSourceFuel?_eventually_valid_of_codeCompletes hcompletion

theorem ctermFrontierStatesFuel_complete_of_codeCompletes
    {pref : List Tok} {term : Term}
    (hcompletion : CodeCompletesTerm pref term) :
    ∃ minFuel,
      ∀ fuel, minFuel ≤ fuel →
        ∃ parsed,
          parsed ∈ ctermFrontierStatesFuel fuel pref := by
  obtain ⟨suffix, tree, hderive, _hdenotes⟩ := hcompletion
  have hprefix :
      PrefixCompletes checkableGrammar.toGrammar .cterm pref tree := by
    exact ⟨suffix, by simpa [checkableGrammar] using hderive⟩
  obtain ⟨state, hpref⟩ :=
    CheckableGrammar.checkedFrontierState_of_prefixCompletes
      checkableGrammar hprefix
  subst pref
  obtain ⟨minFuel, hfound⟩ :=
    CheckableGrammar.frontierStatesFuel_complete_checked checkableGrammar state
  refine ⟨minFuel, ?_⟩
  intro fuel hle
  obtain ⟨parsed, hparsed⟩ := hfound fuel hle
  exact ⟨parsed, by simpa [ctermFrontierStatesFuel] using hparsed⟩

theorem ctermFrontierStatesFuel_complete_of_codeCompletes_with_completion
    {pref : List Tok} {term : Term}
    (hcompletion : CodeCompletesTerm pref term) :
    ∃ minFuel,
      ∀ fuel, minFuel ≤ fuel →
        ∃ parsed tree,
          parsed ∈ ctermFrontierStatesFuel fuel pref ∧
          CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
            parsed.state tree ∧
          DenotesTerm tree term := by
  obtain ⟨suffix, tree, hderive, hdenotes⟩ := hcompletion
  have hprefix :
      PrefixCompletes checkableGrammar.toGrammar .cterm pref tree := by
    exact ⟨suffix, by simpa [checkableGrammar] using hderive⟩
  obtain ⟨state, hpref, hstateCompletes⟩ :=
    CheckableGrammar.checkedFrontierState_of_prefixCompletes_with_completion
      checkableGrammar hprefix
  subst pref
  obtain ⟨minFuel, hfound⟩ :=
    ctermFrontierStatesFuel_complete_checked_exact state
  refine ⟨minFuel, ?_⟩
  intro fuel hle
  obtain ⟨parsed, hstate, hmem⟩ := hfound fuel hle
  refine ⟨parsed, tree, hmem, ?_, hdenotes⟩
  rw [hstate]
  exact hstateCompletes

/--
If one token prefix has two semantic term completions, the generated frontier
enumerator eventually exposes parser-state evidence for both completions from
that same prefix.
-/
theorem ctermFrontierStatesFuel_complete_for_completion_pair
    {pref : List Tok} {left right : Term}
    (hleft : CodeCompletesTerm pref left)
    (hright : CodeCompletesTerm pref right) :
    ∃ minFuel,
      ∀ fuel, minFuel ≤ fuel →
        (∃ parsed tree,
          parsed ∈ ctermFrontierStatesFuel fuel pref ∧
          CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
            parsed.state tree ∧
          DenotesTerm tree left) ∧
        (∃ parsed tree,
          parsed ∈ ctermFrontierStatesFuel fuel pref ∧
          CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
            parsed.state tree ∧
          DenotesTerm tree right) := by
  obtain ⟨leftFuel, hleftFound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes_with_completion
      hleft
  obtain ⟨rightFuel, hrightFound⟩ :=
    ctermFrontierStatesFuel_complete_of_codeCompletes_with_completion
      hright
  refine ⟨max leftFuel rightFuel, ?_⟩
  intro fuel hle
  have hleftLe : leftFuel ≤ fuel :=
    Nat.le_trans (Nat.le_max_left leftFuel rightFuel) hle
  have hrightLe : rightFuel ≤ fuel :=
    Nat.le_trans (Nat.le_max_right leftFuel rightFuel) hle
  exact ⟨hleftFound fuel hleftLe, hrightFound fuel hrightLe⟩

theorem generatedFrontierEnumerator_finds_examples :
    (ctermFrontierStatesFuel 5 moveXPrefix).length > 0 ∧
    (ctermFrontierStatesFuel 5 xPrefix).length > 0 ∧
    (ctermFrontierStatesFuel 5 moveStarPrefix).length > 0 := by
  native_decide

theorem firstCtermCompletedTokens?_moveStarPrefix :
    firstCtermCompletedTokens? 5 moveStarPrefix =
      some [.moveKw, .star, .ident "__fw_default"] := by
  native_decide

theorem completeTermSourceFuel?_moveStarPrefix :
    completeTermSourceFuel? 5 moveStarPrefix =
      some "move * __fw_default" := by
  native_decide

theorem exactParser_eventually_finds_moveX :
    ∃ minFuel,
      ∀ fuel, minFuel ≤ fuel →
        moveXTree ∈
          CheckableGrammar.parseCatFuel checkableGrammar fuel
            .cterm moveXPrefix := by
  exact CheckableGrammar.parseCatFuel_complete checkableGrammar
    (by simpa [checkableGrammar] using moveX_derives)

theorem frontierEnumerator_eventually_finds_moveXEqState :
    ∃ minFuel,
      ∀ fuel, minFuel ≤ fuel →
        ∃ parsed,
          parsed ∈ ctermFrontierStatesFuel fuel moveXPrefix := by
  rw [← moveXEqAfterLhsFrontierState_pref]
  simpa [ctermFrontierStatesFuel] using
    CheckableGrammar.frontierStatesFuel_complete_checked checkableGrammar
      moveXEqAfterLhsFrontierState

theorem frontierEnumerator_eventually_finds_xAssignState :
    ∃ minFuel,
      ∀ fuel, minFuel ≤ fuel →
        ∃ parsed,
          parsed ∈ ctermFrontierStatesFuel fuel xPrefix := by
  rw [← xAssignAfterLhsFrontierState_pref]
  simpa [ctermFrontierStatesFuel] using
    CheckableGrammar.frontierStatesFuel_complete_checked checkableGrammar
      xAssignAfterLhsFrontierState

theorem fuelCompleter_eventually_completes_moveXPrefix :
    ∃ fuel tokens,
      CheckableGrammar.completeTokensFuel? checkableGrammar defaults fuel
        .cterm moveXPrefix = some tokens ∧
      ∃ suffix tree,
        tokens = moveXPrefix ++ suffix ∧
        Derives checkableGrammar.toGrammar .cterm tokens tree := by
  exact CheckableGrammar.completeTokensFuel?_complete_of_checked
    checkableGrammar defaults moveXEqAfterLhsFrontierState
    moveXEqAfterLhsFrontierState_pref

theorem fuelCompleter_eventually_completes_xPrefix :
    ∃ fuel tokens,
      CheckableGrammar.completeTokensFuel? checkableGrammar defaults fuel
        .cterm xPrefix = some tokens ∧
      ∃ suffix tree,
        tokens = xPrefix ++ suffix ∧
        Derives checkableGrammar.toGrammar .cterm tokens tree := by
  exact CheckableGrammar.completeTokensFuel?_complete_of_checked
    checkableGrammar defaults xAssignAfterLhsFrontierState
    xAssignAfterLhsFrontierState_pref

def defaultCtermCompletion :
    ValidCompletion checkableGrammar.toGrammar .cterm [] :=
  (defaultRawCompletion .cterm).toValidCompletion checkableGrammar
    (defaultRawCompletion_valid .cterm)

theorem defaultCtermCompletion_derives :
    Derives checkableGrammar.toGrammar .cterm
      defaultCtermCompletion.completedTokens defaultCtermCompletion.tree :=
  defaultCtermCompletion.completedTokens_derives

theorem ctermParserFromRawSpec_completes_moveXPrefix :
    ∃ result,
      ctermParserFromRawSpec.complete moveXPrefix = some result := by
  exact ctermParserFromRawSpec.complete_if_completable moveXPrefix
    ⟨moveXEqMoveXTree,
      ⟨[Tok.eqEq] ++ moveXPrefix,
        by simpa [checkableGrammar] using moveXEqMoveX_derives⟩⟩

theorem ctermParserFromRawSpec_completes_xPrefix :
    ∃ result,
      ctermParserFromRawSpec.complete xPrefix = some result := by
  exact ctermParserFromRawSpec.complete_if_completable xPrefix
    ⟨assignXMoveXTree,
      ⟨[Tok.assign] ++ moveXPrefix,
        by simpa [checkableGrammar] using assignXMoveX_derives⟩⟩

def xLVal : LVal :=
  SyntaxCtor.clvalVar_ctor "x"

def moveXTerm : Term :=
  SyntaxCtor.ctermMove_ctor xLVal

def moveXEqMoveXTerm : Term :=
  SyntaxCtor.ctermEq_ctor moveXTerm moveXTerm

def assignXMoveXTerm : Term :=
  SyntaxCtor.ctermAssign_ctor xLVal moveXTerm

theorem clvalX_denotes :
    DenotesLVal clvalXTree xLVal := by
  change DenotesLVal (.node "clvalVar" [.token (.ident "x")])
    (SyntaxCtor.clvalVar_ctor "x")
  exact DenotesLVal.clvalVar

theorem moveX_denotes :
    DenotesTerm moveXTree moveXTerm := by
  change DenotesTerm (.node "ctermMove" [.token .moveKw, clvalXTree])
    (SyntaxCtor.ctermMove_ctor xLVal)
  exact DenotesTerm.ctermMove clvalX_denotes

theorem moveXEqMoveX_denotes :
    DenotesTerm moveXEqMoveXTree moveXEqMoveXTerm := by
  change DenotesTerm (.node "ctermEq" [moveXTree, .token .eqEq, moveXTree])
    (SyntaxCtor.ctermEq_ctor moveXTerm moveXTerm)
  exact DenotesTerm.ctermEq moveX_denotes moveX_denotes

theorem assignXMoveX_denotes :
    DenotesTerm assignXMoveXTree assignXMoveXTerm := by
  change DenotesTerm
    (.node "ctermAssign" [clvalXTree, .token .assign, moveXTree])
    (SyntaxCtor.ctermAssign_ctor xLVal moveXTerm)
  exact DenotesTerm.ctermAssign clvalX_denotes moveX_denotes

def moveXTermCompletion :
    ValidTermCompletion moveXPrefix :=
  { suffix := []
    tree := moveXTree
    term := moveXTerm
    derives := by simpa using moveX_derives
    denotes := moveX_denotes }

def moveXEqMoveXTermCompletion :
    ValidTermCompletion moveXPrefix :=
  { suffix := [Tok.eqEq] ++ moveXPrefix
    tree := moveXEqMoveXTree
    term := moveXEqMoveXTerm
    derives := moveXEqMoveX_derives
    denotes := moveXEqMoveX_denotes }

def assignXMoveXTermCompletion :
    ValidTermCompletion xPrefix :=
  { suffix := [Tok.assign] ++ moveXPrefix
    tree := assignXMoveXTree
    term := assignXMoveXTerm
    derives := assignXMoveX_derives
    denotes := assignXMoveX_denotes }

theorem moveXPrefix_codeCompletes_as_eq :
    CodeCompletesTerm moveXPrefix moveXEqMoveXTerm :=
  moveXEqMoveXTermCompletion.codeCompletes

theorem moveXPrefix_codeCompletes_as_move :
    CodeCompletesTerm moveXPrefix moveXTerm :=
  moveXTermCompletion.codeCompletes

theorem moveXPrefix_has_move_and_eq_completions :
    CodeCompletesTerm moveXPrefix moveXTerm ∧
    CodeCompletesTerm moveXPrefix moveXEqMoveXTerm ∧
    moveXTerm ≠ moveXEqMoveXTerm := by
  exact ⟨moveXPrefix_codeCompletes_as_move,
    moveXPrefix_codeCompletes_as_eq,
    by simp [moveXTerm, moveXEqMoveXTerm]⟩

theorem frontierEnumerator_complete_for_moveX_ambiguity :
    ∃ minFuel,
      ∀ fuel, minFuel ≤ fuel →
        (∃ parsed tree,
          parsed ∈ ctermFrontierStatesFuel fuel moveXPrefix ∧
          CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
            parsed.state tree ∧
          DenotesTerm tree moveXTerm) ∧
        (∃ parsed tree,
          parsed ∈ ctermFrontierStatesFuel fuel moveXPrefix ∧
          CheckableGrammar.CheckedFrontierStateCompletes checkableGrammar
            parsed.state tree ∧
          DenotesTerm tree moveXEqMoveXTerm) := by
  exact ctermFrontierStatesFuel_complete_for_completion_pair
    moveXPrefix_codeCompletes_as_move
    moveXPrefix_codeCompletes_as_eq

theorem xPrefix_codeCompletes_as_assignment :
    CodeCompletesTerm xPrefix assignXMoveXTerm :=
  assignXMoveXTermCompletion.codeCompletes

theorem completeTermParserBySpec_completes_moveXPrefix :
    ∃ result, completeTermParserBySpec.complete moveXPrefix = some result := by
  exact completeTermParserBySpec.complete_if_completable moveXPrefix
    ⟨moveXEqMoveXTerm, moveXPrefix_codeCompletes_as_eq⟩

theorem completeTermParserBySpec_completes_xPrefix :
    ∃ result, completeTermParserBySpec.complete xPrefix = some result := by
  exact completeTermParserBySpec.complete_if_completable xPrefix
    ⟨assignXMoveXTerm, xPrefix_codeCompletes_as_assignment⟩

def oldPartialMoveX : PartialTerm :=
  .moveOperand (.varX (.done "x"))

def oldPartialMoveXAsEqLhs : PartialTerm :=
  .termPrefix oldPartialMoveX

def oldPartialXAsAssignmentLhs : PartialTerm :=
  .assignLhs (.varX (.done "x"))

theorem oldPartialMoveX_completes :
    CompletesTerm oldPartialMoveX moveXTerm := by
  change CompletesTerm
    (.moveOperand (.varX (.done "x")))
    (SyntaxCtor.ctermMove_ctor (SyntaxCtor.clvalVar_ctor "x"))
  exact ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
    (ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX
      ConservativeExtractor.Generated.CompletesName.done)

theorem oldPartialMoveXAsEqLhs_completes :
    CompletesTerm oldPartialMoveXAsEqLhs moveXEqMoveXTerm := by
  change CompletesTerm
    (.termPrefix (.moveOperand (.varX (.done "x"))))
    (SyntaxCtor.ctermEq_ctor moveXTerm moveXTerm)
  exact ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
    oldPartialMoveX_completes

theorem oldPartialXAsAssignmentLhs_completes :
    CompletesTerm oldPartialXAsAssignmentLhs assignXMoveXTerm := by
  change CompletesTerm
    (.assignLhs (.varX (.done "x")))
    (SyntaxCtor.ctermAssign_ctor (SyntaxCtor.clvalVar_ctor "x") moveXTerm)
  exact ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
    (ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX
      ConservativeExtractor.Generated.CompletesName.done)

end FwRust
end GrammarFrontier
end ConservativeExtractor
