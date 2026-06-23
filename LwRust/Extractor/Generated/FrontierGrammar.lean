import LwRust.Extractor.Frontier

/-!
Generated FW-Rust grammar for parser frontiers.

This file is generated from the syntax declarations and checked
`SyntaxCtor` annotations in `LwRust.Extractor.CompleteProgram`.
Re-generate it with `scripts/generate_frontier_grammar_from_syntax.py`.
-/

namespace ConservativeExtractor
namespace GrammarFrontier
namespace FwRust

inductive Cat where
  | cty
  | clval
  | cterm
  | clvals
  | clvalsTail
  | cterms
  | ctermsTail
  deriving Repr, DecidableEq

inductive Terminal where
  | ctyUnit
  | ctyInt
  | ctyBool
  | unit
  | trueLit
  | falseLit
  | amp
  | ampMut
  | lbrack
  | rbrack
  | comma
  | box
  | star
  | block
  | lbrace
  | rbrace
  | letKw
  | mutKw
  | assign
  | moveKw
  | copyKw
  | eqEq
  | ifKw
  | elseKw
  | whileKw
  | ident
  | num
  | lifetime
  deriving Repr, DecidableEq

inductive Tok where
  | ctyUnit
  | ctyInt
  | ctyBool
  | unit
  | trueLit
  | falseLit
  | amp
  | ampMut
  | lbrack
  | rbrack
  | comma
  | box
  | star
  | block
  | lbrace
  | rbrace
  | letKw
  | mutKw
  | assign
  | moveKw
  | copyKw
  | eqEq
  | ifKw
  | elseKw
  | whileKw
  | ident (name : Name)
  | num (value : Int)
  | lifetime (lifetime : Lifetime)
  deriving Repr, DecidableEq

def accepts : Terminal → Tok → Prop
  | .ctyUnit, .ctyUnit => True
  | .ctyInt, .ctyInt => True
  | .ctyBool, .ctyBool => True
  | .unit, .unit => True
  | .trueLit, .trueLit => True
  | .falseLit, .falseLit => True
  | .amp, .amp => True
  | .ampMut, .ampMut => True
  | .lbrack, .lbrack => True
  | .rbrack, .rbrack => True
  | .comma, .comma => True
  | .box, .box => True
  | .star, .star => True
  | .block, .block => True
  | .lbrace, .lbrace => True
  | .rbrace, .rbrace => True
  | .letKw, .letKw => True
  | .mutKw, .mutKw => True
  | .assign, .assign => True
  | .moveKw, .moveKw => True
  | .copyKw, .copyKw => True
  | .eqEq, .eqEq => True
  | .ifKw, .ifKw => True
  | .elseKw, .elseKw => True
  | .whileKw, .whileKw => True
  | .ident, .ident _ => True
  | .num, .num _ => True
  | .lifetime, .lifetime _ => True
  | _, _ => False

def acceptsBool : Terminal → Tok → Bool
  | .ctyUnit, .ctyUnit => Bool.true
  | .ctyInt, .ctyInt => Bool.true
  | .ctyBool, .ctyBool => Bool.true
  | .unit, .unit => Bool.true
  | .trueLit, .trueLit => Bool.true
  | .falseLit, .falseLit => Bool.true
  | .amp, .amp => Bool.true
  | .ampMut, .ampMut => Bool.true
  | .lbrack, .lbrack => Bool.true
  | .rbrack, .rbrack => Bool.true
  | .comma, .comma => Bool.true
  | .box, .box => Bool.true
  | .star, .star => Bool.true
  | .block, .block => Bool.true
  | .lbrace, .lbrace => Bool.true
  | .rbrace, .rbrace => Bool.true
  | .letKw, .letKw => Bool.true
  | .mutKw, .mutKw => Bool.true
  | .assign, .assign => Bool.true
  | .moveKw, .moveKw => Bool.true
  | .copyKw, .copyKw => Bool.true
  | .eqEq, .eqEq => Bool.true
  | .ifKw, .ifKw => Bool.true
  | .elseKw, .elseKw => Bool.true
  | .whileKw, .whileKw => Bool.true
  | .ident, .ident _ => Bool.true
  | .num, .num _ => Bool.true
  | .lifetime, .lifetime _ => Bool.true
  | _, _ => Bool.false

theorem acceptsBool_sound {terminal : Terminal} {tok : Tok}
    (h : acceptsBool terminal tok = Bool.true) :
    accepts terminal tok := by
  cases terminal <;> cases tok <;>
    simp [acceptsBool, accepts] at h ⊢

theorem acceptsBool_complete {terminal : Terminal} {tok : Tok}
    (h : accepts terminal tok) :
    acceptsBool terminal tok = Bool.true := by
  cases terminal <;> cases tok <;>
    simp [acceptsBool, accepts] at h ⊢

open Sym

def ctyUnitRule : Rule Cat Terminal :=
  { name := "ctyUnit", lhs := .cty, rhs := [.token .ctyUnit] }

def ctyIntRule : Rule Cat Terminal :=
  { name := "ctyInt", lhs := .cty, rhs := [.token .ctyInt] }

def ctyBoolRule : Rule Cat Terminal :=
  { name := "ctyBool", lhs := .cty, rhs := [.token .ctyBool] }

def ctyBorrowSharedRule : Rule Cat Terminal :=
  { name := "ctyBorrowShared", lhs := .cty, rhs := [.token .amp, .token .lbrack, .cat .clvals, .token .rbrack] }

def ctyBorrowMutRule : Rule Cat Terminal :=
  { name := "ctyBorrowMut", lhs := .cty, rhs := [.token .ampMut, .token .lbrack, .cat .clvals, .token .rbrack] }

def ctyBoxRule : Rule Cat Terminal :=
  { name := "ctyBox", lhs := .cty, rhs := [.token .box, .cat .cty] }

def clvalVarRule : Rule Cat Terminal :=
  { name := "clvalVar", lhs := .clval, rhs := [.token .ident] }

def clvalDerefRule : Rule Cat Terminal :=
  { name := "clvalDeref", lhs := .clval, rhs := [.token .star, .cat .clval] }

def ctermUnitRule : Rule Cat Terminal :=
  { name := "ctermUnit", lhs := .cterm, rhs := [.token .unit] }

def ctermIntRule : Rule Cat Terminal :=
  { name := "ctermInt", lhs := .cterm, rhs := [.token .num] }

def ctermTrueRule : Rule Cat Terminal :=
  { name := "ctermTrue", lhs := .cterm, rhs := [.token .trueLit] }

def ctermFalseRule : Rule Cat Terminal :=
  { name := "ctermFalse", lhs := .cterm, rhs := [.token .falseLit] }

def ctermBlockRule : Rule Cat Terminal :=
  { name := "ctermBlock", lhs := .cterm, rhs := [.token .block, .token .lifetime, .token .lbrace, .cat .cterms, .token .rbrace] }

def ctermLetMutRule : Rule Cat Terminal :=
  { name := "ctermLetMut", lhs := .cterm, rhs := [.token .letKw, .token .mutKw, .token .ident, .token .assign, .cat .cterm] }

def ctermAssignRule : Rule Cat Terminal :=
  { name := "ctermAssign", lhs := .cterm, rhs := [.cat .clval, .token .assign, .cat .cterm] }

def ctermBoxRule : Rule Cat Terminal :=
  { name := "ctermBox", lhs := .cterm, rhs := [.token .box, .cat .cterm] }

def ctermBorrowSharedRule : Rule Cat Terminal :=
  { name := "ctermBorrowShared", lhs := .cterm, rhs := [.token .amp, .cat .clval] }

def ctermBorrowMutRule : Rule Cat Terminal :=
  { name := "ctermBorrowMut", lhs := .cterm, rhs := [.token .ampMut, .cat .clval] }

def ctermMoveRule : Rule Cat Terminal :=
  { name := "ctermMove", lhs := .cterm, rhs := [.token .moveKw, .cat .clval] }

def ctermCopyRule : Rule Cat Terminal :=
  { name := "ctermCopy", lhs := .cterm, rhs := [.token .copyKw, .cat .clval] }

def ctermEqRule : Rule Cat Terminal :=
  { name := "ctermEq", lhs := .cterm, rhs := [.cat .cterm, .token .eqEq, .cat .cterm] }

def ctermIteRule : Rule Cat Terminal :=
  { name := "ctermIte", lhs := .cterm, rhs := [.token .ifKw, .cat .cterm, .cat .cterm, .token .elseKw, .cat .cterm] }

def ctermWhileRule : Rule Cat Terminal :=
  { name := "ctermWhile", lhs := .cterm, rhs := [.token .whileKw, .token .lifetime, .cat .cterm, .cat .cterm] }

def clvalsEmptyRule : Rule Cat Terminal :=
  { name := "clvalsEmpty", lhs := .clvals, rhs := [] }

def clvalsConsRule : Rule Cat Terminal :=
  { name := "clvalsCons", lhs := .clvals, rhs := [.cat .clval, .cat .clvalsTail] }

def clvalsTailEmptyRule : Rule Cat Terminal :=
  { name := "clvalsTailEmpty", lhs := .clvalsTail, rhs := [] }

def clvalsTailConsRule : Rule Cat Terminal :=
  { name := "clvalsTailCons", lhs := .clvalsTail, rhs := [.token .comma, .cat .clval, .cat .clvalsTail] }

def ctermsEmptyRule : Rule Cat Terminal :=
  { name := "ctermsEmpty", lhs := .cterms, rhs := [] }

def ctermsConsRule : Rule Cat Terminal :=
  { name := "ctermsCons", lhs := .cterms, rhs := [.cat .cterm, .cat .ctermsTail] }

def ctermsTailEmptyRule : Rule Cat Terminal :=
  { name := "ctermsTailEmpty", lhs := .ctermsTail, rhs := [] }

def ctermsTailConsRule : Rule Cat Terminal :=
  { name := "ctermsTailCons", lhs := .ctermsTail, rhs := [.token .comma, .cat .cterm, .cat .ctermsTail] }

def grammar : Grammar Cat Terminal Tok :=
  { rules := [
      ctyUnitRule,
      ctyIntRule,
      ctyBoolRule,
      ctyBorrowSharedRule,
      ctyBorrowMutRule,
      ctyBoxRule,
      clvalVarRule,
      clvalDerefRule,
      ctermUnitRule,
      ctermIntRule,
      ctermTrueRule,
      ctermFalseRule,
      ctermBlockRule,
      ctermLetMutRule,
      ctermAssignRule,
      ctermBoxRule,
      ctermBorrowSharedRule,
      ctermBorrowMutRule,
      ctermMoveRule,
      ctermCopyRule,
      ctermEqRule,
      ctermIteRule,
      ctermWhileRule,
      clvalsEmptyRule,
      clvalsConsRule,
      clvalsTailEmptyRule,
      clvalsTailConsRule,
      ctermsEmptyRule,
      ctermsConsRule,
      ctermsTailEmptyRule,
      ctermsTailConsRule
    ]
    accepts := accepts }

def checkableGrammar : CheckableGrammar Cat Terminal Tok :=
  { grammar with
    acceptsBool := acceptsBool
    acceptsBool_sound := by
      intro terminal tok h
      exact acceptsBool_sound h
    acceptsBool_complete := by
      intro terminal tok h
      exact acceptsBool_complete h }

def defaultToken : Terminal → Tok
  | .ctyUnit => .ctyUnit
  | .ctyInt => .ctyInt
  | .ctyBool => .ctyBool
  | .unit => .unit
  | .trueLit => .trueLit
  | .falseLit => .falseLit
  | .amp => .amp
  | .ampMut => .ampMut
  | .lbrack => .lbrack
  | .rbrack => .rbrack
  | .comma => .comma
  | .box => .box
  | .star => .star
  | .block => .block
  | .lbrace => .lbrace
  | .rbrace => .rbrace
  | .letKw => .letKw
  | .mutKw => .mutKw
  | .assign => .assign
  | .moveKw => .moveKw
  | .copyKw => .copyKw
  | .eqEq => .eqEq
  | .ifKw => .ifKw
  | .elseKw => .elseKw
  | .whileKw => .whileKw
  | .ident => .ident "__fw_default"
  | .num => .num 0
  | .lifetime => .lifetime LwRust.Core.Lifetime.root

theorem defaultToken_valid (terminal : Terminal) :
    acceptsBool terminal (defaultToken terminal) = Bool.true := by
  cases terminal <;> native_decide

def defaultTree : Cat → Tree Tok
  | .cty => .node "ctyUnit" [.token (Tok.ctyUnit)]
  | .clval => .node "clvalVar" [.token (.ident "__fw_default")]
  | .cterm => .node "ctermUnit" [.token (Tok.unit)]
  | .clvals => .node "clvalsEmpty" []
  | .clvalsTail => .node "clvalsTailEmpty" []
  | .cterms => .node "ctermsEmpty" []
  | .ctermsTail => .node "ctermsTailEmpty" []

theorem defaultTree_valid (cat : Cat) :
    CheckableGrammar.checkTree checkableGrammar cat
      (defaultTree cat) = Bool.true := by
  cases cat <;> native_decide

def defaultRawCompletion (cat : Cat) : CheckableGrammar.RawCompletion Tok :=
  { suffix := (defaultTree cat).tokens
    tree := defaultTree cat }

theorem defaultRawCompletion_valid (cat : Cat) :
    (defaultRawCompletion cat).valid checkableGrammar cat [] =
      Bool.true := by
  cases cat <;> native_decide

def defaults : CheckableGrammar.Defaults checkableGrammar :=
  { defaultToken := defaultToken
    defaultToken_valid := by
      intro terminal
      exact defaultToken_valid terminal
    defaultTree := defaultTree
    defaultTree_valid := by
      intro cat
      exact defaultTree_valid cat }

end FwRust
end GrammarFrontier
end ConservativeExtractor
