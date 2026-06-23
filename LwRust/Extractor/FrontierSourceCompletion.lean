import LwRust.Extractor.FrontierSemantics

/-!
Proof-carrying source completions for FW-Rust token prefixes.

`FrontierSemantics` proves that the fuel-based completer returns token lists
that parse as `cterm`s.  This file adds the decoder side of that certificate:
the returned parse tree also denotes a complete FW term.
-/

namespace ConservativeExtractor
namespace GrammarFrontier
namespace FwRust

abbrev TermDecodeCompleteAt (tree : Tree Tok) : Prop :=
  (CheckableGrammar.checkTree checkableGrammar .cterm tree = Bool.true →
    ∃ term, denoteTerm? tree = some term) ∧
  (CheckableGrammar.checkTree checkableGrammar .cterms tree = Bool.true →
    ∃ terms, denoteTerms? tree = some terms) ∧
  (CheckableGrammar.checkTree checkableGrammar .ctermsTail tree =
      Bool.true →
    ∃ terms, denoteTermsTail? tree = some terms)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem checkedTermDecodeCompleteAt :
    ∀ tree : Tree Tok, TermDecodeCompleteAt tree := by
  refine Tree.rec (Tok := Tok)
    (motive_1 := TermDecodeCompleteAt)
    (motive_2 := fun children =>
      ∀ child, child ∈ children → TermDecodeCompleteAt child)
    ?token ?node ?nil ?cons
  · intro tok
    unfold TermDecodeCompleteAt
    simp [CheckableGrammar.checkTree]
  · intro ruleName children ih
    unfold TermDecodeCompleteAt
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
      rcases h with hunit | hint | htrue | hfalse | hblock | hlet |
        hassign | hbox | hborrowShared | hborrowMut | hmove | hcopy |
        heq | hite | hwhile
      · rcases hunit with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons child rest =>
            cases child with
            | token tok =>
                cases rest with
                | nil =>
                    cases tok <;>
                      simp [CheckableGrammar.checkSeq, acceptsBool,
                        denoteTerm?] at hseq ⊢
                | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hint with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons child rest =>
            cases child with
            | token tok =>
                cases rest with
                | nil =>
                    cases tok <;>
                      simp [CheckableGrammar.checkSeq, acceptsBool,
                        denoteTerm?] at hseq ⊢
                | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases htrue with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons child rest =>
            cases child with
            | token tok =>
                cases rest with
                | nil =>
                    cases tok <;>
                      simp [CheckableGrammar.checkSeq, acceptsBool,
                        denoteTerm?] at hseq ⊢
                | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hfalse with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons child rest =>
            cases child with
            | token tok =>
                cases rest with
                | nil =>
                    cases tok <;>
                      simp [CheckableGrammar.checkSeq, acceptsBool,
                        denoteTerm?] at hseq ⊢
                | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hblock with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons blockTok rest1 =>
            cases blockTok with
            | token tok1 =>
                cases rest1 with
                | nil => simp [CheckableGrammar.checkSeq] at hseq
                | cons lifetimeTok rest2 =>
                    cases lifetimeTok with
                    | token tok2 =>
                        cases rest2 with
                        | nil => simp [CheckableGrammar.checkSeq] at hseq
                        | cons lbraceTok rest3 =>
                            cases lbraceTok with
                            | token tok3 =>
                                cases rest3 with
                                | nil => simp [CheckableGrammar.checkSeq] at hseq
                                | cons termsTree rest4 =>
                                    cases rest4 with
                                    | nil => simp [CheckableGrammar.checkSeq] at hseq
                                    | cons rbraceTok rest5 =>
                                        cases rbraceTok with
                                        | token tok5 =>
                                            cases rest5 with
                                            | nil =>
                                                cases tok1 <;>
                                                  simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                                cases tok2 <;>
                                                  simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                                rename_i lifetime
                                                cases tok3 <;>
                                                  simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                                cases tok5 <;>
                                                  simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                                obtain ⟨terms, hterms⟩ :=
                                                  (ih termsTree (by simp)).2.1 hseq
                                                exact ⟨SyntaxSemantics.ctermBlock lifetime terms, by
                                                  simp [denoteTerm?, hterms]⟩
                                            | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
                                        | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
                            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
                    | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hlet with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons letTok rest1 =>
            cases letTok with
            | token tok1 =>
                cases rest1 with
                | nil => simp [CheckableGrammar.checkSeq] at hseq
                | cons mutTok rest2 =>
                    cases mutTok with
                    | token tok2 =>
                        cases rest2 with
                        | nil => simp [CheckableGrammar.checkSeq] at hseq
                        | cons identTok rest3 =>
                            cases identTok with
                            | token tok3 =>
                                cases rest3 with
                                | nil => simp [CheckableGrammar.checkSeq] at hseq
                                | cons assignTok rest4 =>
                                    cases assignTok with
                                    | token tok4 =>
                                        cases rest4 with
                                        | nil => simp [CheckableGrammar.checkSeq] at hseq
                                        | cons initTree rest5 =>
                                            cases rest5 with
                                            | nil =>
                                                cases tok1 <;>
                                                  simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                                cases tok2 <;>
                                                  simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                                cases tok3 <;>
                                                  simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                                rename_i name
                                                cases tok4 <;>
                                                  simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                                obtain ⟨init, hinit⟩ :=
                                                  (ih initTree (by simp)).1 hseq
                                                exact ⟨SyntaxSemantics.ctermLetMut name init, by
                                                  simp [denoteTerm?, hinit]⟩
                                            | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
                                    | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
                            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
                    | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hassign with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons lhsTree rest1 =>
            cases rest1 with
            | nil => simp [CheckableGrammar.checkSeq] at hseq
            | cons assignTok rest2 =>
                cases assignTok with
                | token tok =>
                    cases rest2 with
                    | nil => simp [CheckableGrammar.checkSeq] at hseq
                    | cons rhsTree rest3 =>
                        cases rest3 with
                        | nil =>
                            cases tok <;> simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                            rcases hseq with ⟨hlhs, hrhs⟩
                            obtain ⟨lhs, hlhs'⟩ := checkedLValTree_denote_exists hlhs
                            obtain ⟨rhs, hrhs'⟩ := (ih rhsTree (by simp)).1 hrhs
                            exact ⟨SyntaxSemantics.ctermAssign lhs rhs, by
                              simp [denoteTerm?, hlhs', hrhs']⟩
                        | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
                | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hbox with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons boxTok rest1 =>
            cases boxTok with
            | token tok =>
                cases rest1 with
                | nil => simp [CheckableGrammar.checkSeq] at hseq
                | cons operandTree rest2 =>
                    cases rest2 with
                    | nil =>
                        cases tok <;> simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                        obtain ⟨operand, hoperand⟩ := (ih operandTree (by simp)).1 hseq
                        exact ⟨SyntaxSemantics.ctermBox operand, by
                          simp [denoteTerm?, hoperand]⟩
                    | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hborrowShared with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons ampTok rest1 =>
            cases ampTok with
            | token tok =>
                cases rest1 with
                | nil => simp [CheckableGrammar.checkSeq] at hseq
                | cons operandTree rest2 =>
                    cases rest2 with
                    | nil =>
                        cases tok <;> simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                        obtain ⟨operand, hoperand⟩ := checkedLValTree_denote_exists hseq
                        exact ⟨SyntaxSemantics.ctermBorrowShared operand, by
                          simp [denoteTerm?, hoperand]⟩
                    | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hborrowMut with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons ampTok rest1 =>
            cases ampTok with
            | token tok =>
                cases rest1 with
                | nil => simp [CheckableGrammar.checkSeq] at hseq
                | cons mutTok rest2 =>
                    cases mutTok with
                    | token mutTok =>
                        cases rest2 with
                        | nil => simp [CheckableGrammar.checkSeq] at hseq
                        | cons operandTree rest3 =>
                            cases rest3 with
                            | nil =>
                                cases tok <;> cases mutTok <;>
                                  simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                obtain ⟨operand, hoperand⟩ :=
                                  checkedLValTree_denote_exists hseq
                                exact ⟨SyntaxSemantics.ctermBorrowMut operand, by
                                  simp [denoteTerm?, hoperand]⟩
                            | cons _ _ =>
                                simp [CheckableGrammar.checkSeq] at hseq
                    | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hmove with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons operandTree rest1 =>
            cases rest1 with
            | nil =>
                have hoperandTree :
                    checkableGrammar.checkTree .clval operandTree = Bool.true := by
                  simpa [checkableGrammar, grammar, CheckableGrammar.checkSeq,
                    ctyUnitRule, ctyIntRule, ctyBoolRule, ctyBorrowSharedRule,
                    ctyBorrowMutRule, ctyBoxRule, clvalVarRule,
                    clvalDerefRule, ctermUnitRule, ctermIntRule,
                    ctermTrueRule, ctermFalseRule, ctermBlockRule,
                    ctermLetMutRule, ctermAssignRule, ctermBoxRule,
                    ctermBorrowSharedRule, ctermBorrowMutRule, ctermMoveRule,
                    ctermCopyRule, ctermEqRule, ctermIteRule,
                    ctermWhileRule, clvalsEmptyRule, clvalsConsRule,
                    clvalsTailEmptyRule, clvalsTailConsRule, ctermsEmptyRule,
                    ctermsConsRule, ctermsTailEmptyRule, ctermsTailConsRule]
                    using hseq
                obtain ⟨operand, hoperand⟩ :=
                  checkedLValTree_denote_exists hoperandTree
                exact ⟨SyntaxSemantics.ctermMove operand, by
                  simp [denoteTerm?, hoperand]⟩
            | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hcopy with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons copyTok rest1 =>
            cases copyTok with
            | token tok =>
                cases rest1 with
                | nil => simp [CheckableGrammar.checkSeq] at hseq
                | cons operandTree rest2 =>
                    cases rest2 with
                    | nil =>
                        cases tok <;> simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                        obtain ⟨operand, hoperand⟩ := checkedLValTree_denote_exists hseq
                        exact ⟨SyntaxSemantics.ctermCopy operand, by
                          simp [denoteTerm?, hoperand]⟩
                    | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases heq with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons lhsTree rest1 =>
            cases rest1 with
            | nil => simp [CheckableGrammar.checkSeq] at hseq
            | cons eqTok rest2 =>
                cases eqTok with
                | token tok =>
                    cases rest2 with
                    | nil => simp [CheckableGrammar.checkSeq] at hseq
                    | cons rhsTree rest3 =>
                        cases rest3 with
                        | nil =>
                            cases tok <;> simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                            rcases hseq with ⟨hlhs, hrhs⟩
                            obtain ⟨lhs, hlhs'⟩ := (ih lhsTree (by simp)).1 hlhs
                            obtain ⟨rhs, hrhs'⟩ := (ih rhsTree (by simp)).1 hrhs
                            exact ⟨SyntaxSemantics.ctermEq lhs rhs, by
                              simp [denoteTerm?, hlhs', hrhs']⟩
                        | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
                | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hite with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons ifTok rest1 =>
            cases ifTok with
            | token tok1 =>
                cases rest1 with
                | nil => simp [CheckableGrammar.checkSeq] at hseq
                | cons conditionTree rest2 =>
                    cases rest2 with
                    | nil => simp [CheckableGrammar.checkSeq] at hseq
                    | cons trueTree rest3 =>
                        cases rest3 with
                        | nil => simp [CheckableGrammar.checkSeq] at hseq
                        | cons elseTok rest4 =>
                            cases elseTok with
                            | token tok4 =>
                                cases rest4 with
                                | nil => simp [CheckableGrammar.checkSeq] at hseq
                                | cons falseTree rest5 =>
                                    cases rest5 with
                                    | nil =>
                                        cases tok1 <;>
                                          simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                        cases tok4 <;>
                                          simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                        rcases hseq with ⟨hcondition, htrue, hfalse⟩
                                        obtain ⟨condition, hcondition'⟩ :=
                                          (ih conditionTree (by simp)).1 hcondition
                                        obtain ⟨trueBranch, htrue'⟩ :=
                                          (ih trueTree (by simp)).1 htrue
                                        obtain ⟨falseBranch, hfalse'⟩ :=
                                          (ih falseTree (by simp)).1 hfalse
                                        exact ⟨SyntaxSemantics.ctermIte
                                          condition trueBranch falseBranch, by
                                          simp [denoteTerm?, hcondition',
                                            htrue', hfalse']⟩
                                    | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
                            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
      · rcases hwhile with ⟨hrule, hseq⟩
        subst ruleName
        cases children with
        | nil => simp [CheckableGrammar.checkSeq] at hseq
        | cons whileTok rest1 =>
            cases whileTok with
            | token tok1 =>
                cases rest1 with
                | nil => simp [CheckableGrammar.checkSeq] at hseq
                | cons lifetimeTok rest2 =>
                    cases lifetimeTok with
                    | token tok2 =>
                        cases rest2 with
                        | nil => simp [CheckableGrammar.checkSeq] at hseq
                        | cons conditionTree rest3 =>
                            cases rest3 with
                            | nil => simp [CheckableGrammar.checkSeq] at hseq
                            | cons bodyTree rest4 =>
                                cases rest4 with
                                | nil =>
                                    cases tok1 <;>
                                      simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                    cases tok2 <;>
                                      simp [CheckableGrammar.checkSeq, acceptsBool] at hseq
                                    rename_i lifetime
                                    rcases hseq with ⟨hcondition, hbody⟩
                                    obtain ⟨condition, hcondition'⟩ :=
                                      (ih conditionTree (by simp)).1 hcondition
                                    obtain ⟨body, hbody'⟩ :=
                                      (ih bodyTree (by simp)).1 hbody
                                    exact ⟨SyntaxSemantics.ctermWhile
                                      lifetime condition body, by
                                      simp [denoteTerm?, hcondition',
                                        hbody']⟩
                                | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
                    | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
            | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
    · constructor
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
          | nil => exact ⟨[], rfl⟩
          | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
        · rcases hcons with ⟨hrule, hseq⟩
          subst ruleName
          cases children with
          | nil => simp [CheckableGrammar.checkSeq] at hseq
          | cons head rest =>
              cases rest with
              | nil => simp [CheckableGrammar.checkSeq] at hseq
              | cons tail rest2 =>
                  cases rest2 with
                  | nil =>
                      simp [CheckableGrammar.checkSeq] at hseq
                      rcases hseq with ⟨hhead, htail⟩
                      obtain ⟨head', hhead'⟩ :=
                        (ih head (by simp)).1 hhead
                      obtain ⟨tail', htail'⟩ :=
                        (ih tail (by simp)).2.2 htail
                      exact ⟨head' :: tail', by
                        simp [denoteTerms?, hhead', htail']⟩
                  | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
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
          | nil => exact ⟨[], rfl⟩
          | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
        · rcases hcons with ⟨hrule, hseq⟩
          subst ruleName
          cases children with
          | nil => simp [CheckableGrammar.checkSeq] at hseq
          | cons comma rest =>
              cases comma with
              | token tok =>
                  cases rest with
                  | nil => simp [CheckableGrammar.checkSeq] at hseq
                  | cons head rest2 =>
                      cases rest2 with
                      | nil => simp [CheckableGrammar.checkSeq] at hseq
                      | cons tail rest3 =>
                          cases rest3 with
                          | nil =>
                              cases tok <;>
                                simp [CheckableGrammar.checkSeq,
                                  acceptsBool] at hseq
                              rcases hseq with ⟨hhead, htail⟩
                              obtain ⟨head', hhead'⟩ :=
                                (ih head (by simp)).1 hhead
                              obtain ⟨tail', htail'⟩ :=
                                (ih tail (by simp)).2.2 htail
                              exact ⟨head' :: tail', by
                                simp [denoteTermsTail?, hhead', htail']⟩
                          | cons _ _ => simp [CheckableGrammar.checkSeq] at hseq
              | node _ _ => simp [CheckableGrammar.checkSeq] at hseq
  · intro child hmem
    simp at hmem
  · intro head tail hhead htail child hmem
    simp at hmem
    rcases hmem with rfl | hmem
    · exact hhead
    · exact htail child hmem

theorem checkedTermTree_denote_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .cterm tree = Bool.true) :
    ∃ term, denoteTerm? tree = some term :=
  (checkedTermDecodeCompleteAt tree).1 hchecked

theorem checkedTermsTree_denote_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .cterms tree = Bool.true) :
    ∃ terms, denoteTerms? tree = some terms :=
  (checkedTermDecodeCompleteAt tree).2.1 hchecked

theorem checkedTermsTailTree_denote_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .ctermsTail tree =
        Bool.true) :
    ∃ terms, denoteTermsTail? tree = some terms :=
  (checkedTermDecodeCompleteAt tree).2.2 hchecked

theorem checkedTermTree_denotes_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .cterm tree = Bool.true) :
    ∃ term, DenotesTerm tree term := by
  obtain ⟨term, hdenote⟩ := checkedTermTree_denote_exists hchecked
  exact ⟨term, denoteTerm?_sound hdenote⟩

theorem checkedTermsTree_denotes_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .cterms tree = Bool.true) :
    ∃ terms, DenotesTerms tree terms := by
  obtain ⟨terms, hdenote⟩ := checkedTermsTree_denote_exists hchecked
  exact ⟨terms, denoteTerms?_sound hdenote⟩

theorem checkedTermsTailTree_denotes_exists {tree : Tree Tok}
    (hchecked :
      CheckableGrammar.checkTree checkableGrammar .ctermsTail tree =
        Bool.true) :
    ∃ terms, DenotesTermsTail tree terms := by
  obtain ⟨terms, hdenote⟩ := checkedTermsTailTree_denote_exists hchecked
  exact ⟨terms, denoteTermsTail?_sound hdenote⟩

structure ValidDecodedTermSourceCompletion (pref : List Tok) where
  source : String
  tokens : List Tok
  suffix : List Tok
  tree : Tree Tok
  term : Term
  source_eq : source = tokensSource tokens
  tokens_eq : tokens = pref ++ suffix
  derives : Derives checkableGrammar.toGrammar .cterm tokens tree
  denotes : DenotesTerm tree term

namespace ValidDecodedTermSourceCompletion

theorem codeCompletes {pref : List Tok}
    (completion : ValidDecodedTermSourceCompletion pref) :
    CodeCompletesTerm pref completion.term := by
  refine ⟨completion.suffix, completion.tree, ?_, completion.denotes⟩
  simpa [checkableGrammar, completion.tokens_eq] using completion.derives

end ValidDecodedTermSourceCompletion

theorem completeTermSourceFuel?_decoded_valid {fuel : Nat}
    {pref : List Tok} {source : String}
    (hsource : completeTermSourceFuel? fuel pref = some source) :
    ∃ completion : ValidDecodedTermSourceCompletion pref,
      completion.source = source := by
  unfold completeTermSourceFuel? completeTermTokensFuel? at hsource
  cases hraw :
      CheckableGrammar.completeRawFuel? checkableGrammar defaults fuel
        .cterm pref with
  | none =>
      simp [CheckableGrammar.completeTokensFuel?, hraw] at hsource
  | some raw =>
      simp [CheckableGrammar.completeTokensFuel?, hraw] at hsource
      subst source
      have hvalid :=
        CheckableGrammar.completeRawFuel?_sound
          checkableGrammar defaults hraw
      have hvalidParts := hvalid
      simp [CheckableGrammar.RawCompletion.valid] at hvalidParts
      obtain ⟨_htokens, hchecked⟩ := hvalidParts
      obtain ⟨term, hdenote⟩ := checkedTermTree_denote_exists hchecked
      exact ⟨{
        source := tokensSource (pref ++ raw.suffix)
        tokens := pref ++ raw.suffix
        suffix := raw.suffix
        tree := raw.tree
        term := term
        source_eq := rfl
        tokens_eq := rfl
        derives :=
          CheckableGrammar.RawCompletion.valid_sound checkableGrammar hvalid
        denotes := denoteTerm?_sound hdenote
      }, rfl⟩

theorem completeTermSourceParser_decoded_valid_of_some {fuel : Nat}
    {pref : List Tok} {source : String}
    (hsource : completeTermSourceParser.complete fuel pref = some source) :
    ∃ completion : ValidDecodedTermSourceCompletion pref,
      completion.source = source := by
  exact completeTermSourceFuel?_decoded_valid hsource

theorem completeTermSourceParser_eventually_decoded_valid_of_codeCompletes
    {pref : List Tok} {term : Term}
    (hcompletion : CodeCompletesTerm pref term) :
    ∃ fuel completion,
      completeTermSourceParser.complete fuel pref = some
        (completion : ValidDecodedTermSourceCompletion pref).source := by
  obtain ⟨fuel, source, hsource⟩ :=
    completeTermSourceParser_complete_of_codeCompletes hcompletion
  obtain ⟨completion, hcompletionSource⟩ :=
    completeTermSourceParser_decoded_valid_of_some hsource
  subst source
  exact ⟨fuel, completion, hsource⟩

structure DecodedTermSourceParser where
  complete : Nat → List Tok → Option String
  sound :
    ∀ {fuel pref source},
      complete fuel pref = some source →
        ∃ completion : ValidDecodedTermSourceCompletion pref,
          completion.source = source
  complete_if_completable :
    ∀ {pref term},
      CodeCompletesTerm pref term →
        ∃ fuel completion,
          complete fuel pref = some
            (completion : ValidDecodedTermSourceCompletion pref).source

def decodedTermSourceParser : DecodedTermSourceParser where
  complete := completeTermSourceFuel?
  sound := by
    intro fuel pref source hsource
    exact completeTermSourceFuel?_decoded_valid hsource
  complete_if_completable := by
    intro pref term hcompletion
    obtain ⟨fuel, completion, hsource⟩ :=
      completeTermSourceParser_eventually_decoded_valid_of_codeCompletes
        hcompletion
    exact ⟨fuel, completion, hsource⟩

theorem decodedTermSourceParser_sound_of_some {fuel : Nat}
    {pref : List Tok} {source : String}
    (hsource : decodedTermSourceParser.complete fuel pref = some source) :
    ∃ completion : ValidDecodedTermSourceCompletion pref,
      completion.source = source := by
  exact decodedTermSourceParser.sound hsource

theorem decodedTermSourceParser_complete_of_codeCompletes
    {pref : List Tok} {term : Term}
    (hcompletion : CodeCompletesTerm pref term) :
    ∃ fuel completion,
      decodedTermSourceParser.complete fuel pref = some
        (completion : ValidDecodedTermSourceCompletion pref).source := by
  exact decodedTermSourceParser.complete_if_completable hcompletion

theorem decodedTermSourceParser_codeCompletes_of_some {fuel : Nat}
    {pref : List Tok} {source : String}
    (hsource : decodedTermSourceParser.complete fuel pref = some source) :
    ∃ completion : ValidDecodedTermSourceCompletion pref,
      completion.source = source ∧
      CodeCompletesTerm pref completion.term := by
  obtain ⟨completion, hcompletionSource⟩ :=
    decodedTermSourceParser_sound_of_some hsource
  exact ⟨completion, hcompletionSource,
    completion.codeCompletes⟩

end FwRust
end GrammarFrontier
end ConservativeExtractor
