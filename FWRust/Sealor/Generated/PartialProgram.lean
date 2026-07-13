import FWRust.Sealor.CompleteProgram

/-!
Template for grammar-derived partial syntax.

The generator replaces the marker below with declarations derived from the
complete FWRust syntax facade in `FWRust.Sealor.CompleteProgram`.
-/

namespace ConservativeSealor
namespace Generated

/-- The already-decoded lexical prefix of an integer literal. -/
abbrev PartialInt := String

inductive PartialName where
  | cutoff
  | done (x : Name)
  | prefix (x : Name)
  deriving Repr

mutual

inductive PartialTerms where
  | cutoff
  | done (xs : List Term)
  | elems (pre : List Term) (tail : Option PartialTerm)
  deriving Repr

inductive PartialTy where
  | cutoff
  | done (x : Ty)
  -- partial syntax: `& lval ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  | borrowSharedTargets (target : PartialLVal)
  -- partial syntax: `& mut lval ...`
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | borrowMutTargets (target : PartialLVal)
  -- partial syntax: `box ty ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | boxElement (element : PartialTy)
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | tokenAmpStart
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | boxStart
  deriving Repr

inductive PartialLVal where
  | cutoff
  | done (x : LVal)
  -- partial syntax: `name ...`
  -- derived from: SyntaxCtor.clvalVar_ctor {x}
  | varX (x : PartialName)
  -- partial syntax: `* lval ...`
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | derefOperand (operand : PartialLVal)
  -- partial syntax: `* ...`
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | derefStart
  deriving Repr

inductive PartialTerm where
  | cutoff
  | done (x : Term)
  -- partial syntax: `num ...`
  -- derived from: SyntaxCtor.ctermInt_ctor {n}
  | intN (n : PartialInt)
  -- partial syntax: `block lifetime { term,* ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | blockTerms (lifetime : Lifetime) (terms : PartialTerms)
  -- partial syntax: `let mut name ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutName (name : PartialName)
  -- partial syntax: `let mut name := term ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutRhs (name : Name) (term : PartialTerm)
  -- partial syntax: `lval ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  -- derived from: SyntaxCtor.ctermMove_ctor {operand}
  | lvalStart (lval : PartialLVal)
  -- partial syntax: `lval := term ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | assignRhs (lhs : LVal) (rhs : PartialTerm)
  -- partial syntax: `box term ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | boxOperand (operand : PartialTerm)
  -- partial syntax: `& lval ...`
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | borrowSharedOperand (operand : PartialLVal)
  -- partial syntax: `& mut lval ...`
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | borrowMutOperand (operand : PartialLVal)
  -- partial syntax: `copy lval ...`
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | copyOperand (operand : PartialLVal)
  -- partial syntax: `block ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | blockStart
  -- partial syntax: `let ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | letMutStart
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | boxStart
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | tokenAmpStart
  -- partial syntax: `copy ...`
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | copyStart
  deriving Repr

end

abbrev PartialProgram := PartialTerm

/-- The digit language accepted after a numeral base prefix.
Underscores may separate digits but cannot finish a complete token. -/
private def numTokenDigits (isDigit : Char → Bool)
    (chars : List Char) : Bool :=
  chars.all (fun c => isDigit c || c == '_') &&
    match chars.getLast? with
    | some last => isDigit last
    | none => false

private def asciiHexDigit (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') ||
    ('A' ≤ c && c ≤ 'F')

/-- Surface spellings accepted by the complete facade's Lean `num` atom. -/
private def validNumToken (spelling : String) : Bool :=
  match spelling.toList with
  | '0' :: 'x' :: rest | '0' :: 'X' :: rest =>
      numTokenDigits asciiHexDigit rest
  | '0' :: 'b' :: rest | '0' :: 'B' :: rest =>
      numTokenDigits (fun c => c == '0' || c == '1') rest
  | '0' :: 'o' :: rest | '0' :: 'O' :: rest =>
      numTokenDigits (fun c => '0' ≤ c && c ≤ '7') rest
  | chars@(first :: _) =>
      first.isDigit && numTokenDigits (fun c => c.isDigit) chars
  | [] => false

/-- Decode exactly the valid token spellings above.  Lean's stock
decoder omits the lexer's decimal `0_...` edge, so decimal
underscores are normalized before calling `String.toNat?`. -/
private def decodeNumToken? (spelling : String) : Option Nat :=
  match spelling.toList with
  | '0' :: 'x' :: _ | '0' :: 'X' :: _
  | '0' :: 'b' :: _ | '0' :: 'B' :: _
  | '0' :: 'o' :: _ | '0' :: 'O' :: _ =>
      Lean.Syntax.decodeNatLitVal? spelling
  | chars =>
      (String.ofList (chars.filter (fun c => c != '_'))).toNat?

/-- An integer literal realizes a `num`-token prefix when appending
some suffix forms a valid Lean numeral, embedded into `Int`. -/
def CompletesInt (decoded : PartialInt) (value : Int) : Prop :=
  ∃ suffix completed,
    validNumToken (decoded ++ suffix) = true ∧
      decodeNumToken? (decoded ++ suffix) = some completed ∧
      value = Int.ofNat completed

inductive CompletesName : PartialName → Name → Prop where
  | done {x} :
      CompletesName (PartialName.done x) x
  | cutoff {x} :
      CompletesName PartialName.cutoff x
  | prefix {x y} :
      x.isPrefixOf y = true →
      CompletesName (PartialName.prefix x) y

mutual

inductive CompletesTerms : PartialTerms → List Term → Prop where
  | done {xs} :
      CompletesTerms (PartialTerms.done xs) xs
  | cutoff {frontierCompletion : Term} {suffix : List Term} :
      CompletesTerms PartialTerms.cutoff (frontierCompletion :: suffix)
  | elemsDone {pre suffix : List Term} {frontierCompletion : Term} :
      CompletesTerms (PartialTerms.elems pre none)
        (pre ++ frontierCompletion :: suffix)
  | elemsTail {pre suffix : List Term} {frontier : PartialTerm}
      {frontierCompletion : Term} :
      CompletesTerm frontier frontierCompletion →
      CompletesTerms (PartialTerms.elems pre (some frontier))
        (pre ++ frontierCompletion :: suffix)

inductive CompletesTy : PartialTy → Ty → Prop where
  | done {x} :
      CompletesTy (PartialTy.done x) x
  | cutoff {x} :
      CompletesTy PartialTy.cutoff x
  -- partial syntax: `& lval ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  | ctyBorrowShared_borrowSharedTargets {target : PartialLVal} {target' : LVal} :
      CompletesLVal target target' →
      CompletesTy (PartialTy.borrowSharedTargets target) (SyntaxCtor.ctyBorrowShared_ctor target')
  -- partial syntax: `& mut lval ...`
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | ctyBorrowMut_borrowMutTargets {target : PartialLVal} {target' : LVal} :
      CompletesLVal target target' →
      CompletesTy (PartialTy.borrowMutTargets target) (SyntaxCtor.ctyBorrowMut_ctor target')
  -- partial syntax: `box ty ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | ctyBox_boxElement {element : PartialTy} {element' : Ty} :
      CompletesTy element element' →
      CompletesTy (PartialTy.boxElement element) (SyntaxCtor.ctyBox_ctor element')
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctyBorrowShared_ctor {target}
  | ctyBorrowShared_tokenAmpStart {target : LVal} :
      CompletesTy (PartialTy.tokenAmpStart) (SyntaxCtor.ctyBorrowShared_ctor target)
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctyBorrowMut_ctor {target}
  | ctyBorrowMut_tokenAmpStart {target : LVal} :
      CompletesTy (PartialTy.tokenAmpStart) (SyntaxCtor.ctyBorrowMut_ctor target)
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctyBox_ctor {element}
  | ctyBox_boxStart {element : Ty} :
      CompletesTy (PartialTy.boxStart) (SyntaxCtor.ctyBox_ctor element)

inductive CompletesLVal : PartialLVal → LVal → Prop where
  | done {x} :
      CompletesLVal (PartialLVal.done x) x
  | cutoff {x} :
      CompletesLVal PartialLVal.cutoff x
  -- partial syntax: `name ...`
  -- derived from: SyntaxCtor.clvalVar_ctor {x}
  | clvalVar_varX {x : PartialName} {x' : Name} :
      CompletesName x x' →
      CompletesLVal (PartialLVal.varX x) (SyntaxCtor.clvalVar_ctor x')
  -- partial syntax: `* lval ...`
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | clvalDeref_derefOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesLVal (PartialLVal.derefOperand operand) (SyntaxCtor.clvalDeref_ctor operand')
  -- partial syntax: `* ...`
  -- derived from: SyntaxCtor.clvalDeref_ctor {operand}
  | clvalDeref_derefStart {operand : LVal} :
      CompletesLVal (PartialLVal.derefStart) (SyntaxCtor.clvalDeref_ctor operand)

inductive CompletesTerm : PartialTerm → Term → Prop where
  | done {x} :
      CompletesTerm (PartialTerm.done x) x
  | cutoff {x} :
      CompletesTerm PartialTerm.cutoff x
  -- partial syntax: `num ...`
  -- derived from: SyntaxCtor.ctermInt_ctor {n}
  | ctermInt_intN {n : PartialInt} {n' : Int} :
      CompletesInt n n' →
      CompletesTerm (PartialTerm.intN n) (SyntaxCtor.ctermInt_ctor n')
  -- partial syntax: `block lifetime { term,* ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | ctermBlock_blockTerms {lifetime : Lifetime} {terms : PartialTerms} {terms' : List Term} :
      CompletesTerms terms terms' →
      CompletesTerm (PartialTerm.blockTerms lifetime terms) (SyntaxCtor.ctermBlock_ctor lifetime terms')
  -- partial syntax: `let mut name ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutName {name : PartialName} {name' : Name} {initialiser : Term} :
      CompletesName name name' →
      CompletesTerm (PartialTerm.letMutName name) (SyntaxCtor.ctermLetMut_ctor name' initialiser)
  -- partial syntax: `let mut name := term ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutRhs {name : Name} {term : PartialTerm} {term' : Term} :
      CompletesTerm term term' →
      CompletesTerm (PartialTerm.letMutRhs name term) (SyntaxCtor.ctermLetMut_ctor name term')
  -- partial syntax: `lval ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | ctermAssign_lvalStart {lval : PartialLVal} {lval' : LVal} {rhs : Term} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval) (SyntaxCtor.ctermAssign_ctor lval' rhs)
  -- partial syntax: `lval := term ...`
  -- derived from: SyntaxCtor.ctermAssign_ctor {lhs} {rhs}
  | ctermAssign_assignRhs {lhs : LVal} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.assignRhs lhs rhs) (SyntaxCtor.ctermAssign_ctor lhs rhs')
  -- partial syntax: `box term ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | ctermBox_boxOperand {operand : PartialTerm} {operand' : Term} :
      CompletesTerm operand operand' →
      CompletesTerm (PartialTerm.boxOperand operand) (SyntaxCtor.ctermBox_ctor operand')
  -- partial syntax: `& lval ...`
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | ctermBorrowShared_borrowSharedOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowSharedOperand operand) (SyntaxCtor.ctermBorrowShared_ctor operand')
  -- partial syntax: `& mut lval ...`
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | ctermBorrowMut_borrowMutOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowMutOperand operand) (SyntaxCtor.ctermBorrowMut_ctor operand')
  -- partial syntax: `lval ...`
  -- derived from: SyntaxCtor.ctermMove_ctor {operand}
  | ctermMove_lvalStart {lval : PartialLVal} {lval' : LVal} :
      CompletesLVal lval lval' →
      CompletesTerm (PartialTerm.lvalStart lval) (SyntaxCtor.ctermMove_ctor lval')
  -- partial syntax: `copy lval ...`
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | ctermCopy_copyOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.copyOperand operand) (SyntaxCtor.ctermCopy_ctor operand')
  -- partial syntax: `block ...`
  -- derived from: SyntaxCtor.ctermBlock_ctor {lifetime} {terms}
  | ctermBlock_blockStart {completion : Term} :
      CompletesTerm (PartialTerm.blockStart) completion
  -- partial syntax: `let ...`
  -- derived from: SyntaxCtor.ctermLetMut_ctor {name} {initialiser}
  | ctermLetMut_letMutStart {completion : Term} :
      CompletesTerm (PartialTerm.letMutStart) completion
  -- partial syntax: `box ...`
  -- derived from: SyntaxCtor.ctermBox_ctor {operand}
  | ctermBox_boxStart {completion : Term} :
      CompletesTerm (PartialTerm.boxStart) completion
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctermBorrowShared_ctor {operand}
  | ctermBorrowShared_tokenAmpStart {completion : Term} :
      CompletesTerm (PartialTerm.tokenAmpStart) completion
  -- partial syntax: `& ...`
  -- derived from: SyntaxCtor.ctermBorrowMut_ctor {operand}
  | ctermBorrowMut_tokenAmpStart {completion : Term} :
      CompletesTerm (PartialTerm.tokenAmpStart) completion
  -- partial syntax: `copy ...`
  -- derived from: SyntaxCtor.ctermCopy_ctor {operand}
  | ctermCopy_copyStart {completion : Term} :
      CompletesTerm (PartialTerm.copyStart) completion

end


end Generated
end ConservativeSealor
