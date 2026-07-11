import FWRust.Conditional.Paper.Syntax

/-!
# Partial conditional programs

A small, isolated frontier grammar for the conditional extension.  The
reduced `FWRust.Sealor` grammar remains unchanged: this grammar uses the
extended `FWRust.Conditional.Core.Term`, including `eq`, `ite`, and `missing`.

The constructors correspond to parser frontiers rather than arbitrary holes.
In particular, `iteTrueBranch` represents an `if` whose condition is complete
and whose then branch is in flight; `iteFalseBranch` additionally records the
completed then branch.  Since a partial branch is itself a `PartialTerm`, a
frontier in an `else if` chain is represented recursively.
-/

namespace FWRust.Conditional.Sealor

open FWRust.Conditional.Core

abbrev Program := Term

mutual

inductive PartialTerms where
  | cutoff
  | done (terms : List Term)
  | elems (pre : List Term) (frontier : Option PartialTerm)
  deriving Repr

inductive PartialTerm where
  | cutoff
  | done (term : Term)
  | blockStart
  | blockTerms (lifetime : Lifetime) (terms : PartialTerms)
  | eqLhs (lhs : PartialTerm)
  | eqRhs (lhs : Term) (rhs : PartialTerm)
  | iteStart
  | iteCondition (condition : PartialTerm)
  | iteTrueBranch (condition : Term) (trueBranch : PartialTerm)
  | iteFalseBranch (condition trueBranch : Term)
      (falseBranch : PartialTerm)
  deriving Repr

end

abbrev PartialProgram := PartialTerm

mutual

/-- A complete statement list realizes a partial block-body frontier. -/
inductive CompletesTerms : PartialTerms → List Term → Prop where
  | done {terms : List Term} :
      CompletesTerms (.done terms) terms
  | cutoff {terms : List Term} :
      CompletesTerms .cutoff terms
  | elemsDone {pre suffix : List Term} :
      CompletesTerms (.elems pre none) (pre ++ suffix)
  | elemsFrontier {pre suffix : List Term} {frontier : PartialTerm}
      {completion : Term} :
      CompletesTerm frontier completion →
      CompletesTerms (.elems pre (some frontier))
        (pre ++ completion :: suffix)

/-- Realization of a parser frontier by a complete conditional-language term. -/
inductive CompletesTerm : PartialTerm → Term → Prop where
  | done {term : Term} :
      CompletesTerm (.done term) term
  | cutoff {term : Term} :
      CompletesTerm .cutoff term
  | blockStart {lifetime : Lifetime} {terms : List Term} :
      CompletesTerm .blockStart (.block lifetime terms)
  | blockTerms {lifetime : Lifetime} {terms : PartialTerms}
      {completion : List Term} :
      CompletesTerms terms completion →
      CompletesTerm (.blockTerms lifetime terms) (.block lifetime completion)
  | eqLhs {lhs : PartialTerm} {lhsCompletion rhs : Term} :
      CompletesTerm lhs lhsCompletion →
      CompletesTerm (.eqLhs lhs) (.eq lhsCompletion rhs)
  | eqRhs {lhs : Term} {rhs : PartialTerm} {rhsCompletion : Term} :
      CompletesTerm rhs rhsCompletion →
      CompletesTerm (.eqRhs lhs rhs) (.eq lhs rhsCompletion)
  | iteStart {condition trueBranch falseBranch : Term} :
      CompletesTerm .iteStart (.ite condition trueBranch falseBranch)
  | iteCondition {condition : PartialTerm} {conditionCompletion trueBranch
      falseBranch : Term} :
      CompletesTerm condition conditionCompletion →
      CompletesTerm (.iteCondition condition)
        (.ite conditionCompletion trueBranch falseBranch)
  | iteTrueBranch {condition : Term} {trueBranch : PartialTerm}
      {trueCompletion falseBranch : Term} :
      CompletesTerm trueBranch trueCompletion →
      CompletesTerm (.iteTrueBranch condition trueBranch)
        (.ite condition trueCompletion falseBranch)
  | iteFalseBranch {condition trueBranch : Term}
      {falseBranch : PartialTerm} {falseCompletion : Term} :
      CompletesTerm falseBranch falseCompletion →
      CompletesTerm (.iteFalseBranch condition trueBranch falseBranch)
        (.ite condition trueBranch falseCompletion)

end

abbrev CompletesProgram : PartialProgram → Program → Prop :=
  CompletesTerm

end FWRust.Conditional.Sealor
