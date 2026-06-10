from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "LwRust" / "Extractor" / "CompleteProgram.lean"
TEMPLATE = ROOT / "LwRust" / "Extractor" / "Template" / "PartialProgram.lean"
OUTPUT = ROOT / "LwRust" / "Extractor" / "Generated" / "PartialProgram.lean"
MARKER = "/-- INSERT GRAMMAR HERE --/"


GENERATED = """\
inductive PartialName where
  | cutoff
  | done (x : Name)
  | prefix (x : Name)
  deriving Repr

mutual

inductive PartialLVals where
  | cutoff
  | done (xs : List LVal)
  | elems (pre : List LVal) (tail : Option PartialLVal)
  deriving Repr

inductive PartialTerms where
  | cutoff
  | done (xs : List Term)
  | elems (pre : List Term) (tail : Option PartialTerm)
  deriving Repr

inductive PartialTy where
  | cutoff
  | done (x : Ty)
  | borrowTargets (mutable : Bool) (targets : PartialLVals)
  | boxElement (element : PartialTy)
  deriving Repr

inductive PartialLVal where
  | cutoff
  | done (x : LVal)
  | varName (x : PartialName)
  | derefOperand (operand : PartialLVal)
  deriving Repr

inductive PartialValue where
  | cutoff
  | done (x : Value)
  | intValue (n : Int)
  | boolValue (b : Bool)
  deriving Repr

inductive PartialTerm where
  | cutoff
  | done (x : Term)
  | blockTerms (lifetime : Lifetime) (terms : PartialTerms)
  | letMutName (name : PartialName)
  | letMutInitialiser (name : Name) (initialiser : PartialTerm)
  | assignLhs (lhs : PartialLVal)
  | assignRhs (lhs : LVal) (rhs : PartialTerm)
  | boxOperand (operand : PartialTerm)
  | borrowOperand (mutable : Bool) (operand : PartialLVal)
  | moveOperand (operand : PartialLVal)
  | copyOperand (operand : PartialLVal)
  | valValue (value : PartialValue)
  | eqLhs (lhs : PartialTerm)
  | eqRhs (lhs : Term) (rhs : PartialTerm)
  | iteCondition (condition : PartialTerm)
  | iteTrueBranch (condition : Term) (trueBranch : PartialTerm)
  | iteFalseBranch (condition trueBranch : Term) (falseBranch : PartialTerm)
  deriving Repr

end

abbrev PartialProgram := PartialTerm

inductive CompletesName : PartialName → Name → Prop where
  | done {x} :
      CompletesName (PartialName.done x) x
  | cutoff {x} :
      CompletesName PartialName.cutoff x
  | prefix {x y} :
      CompletesName (PartialName.prefix x) y

mutual

inductive CompletesLVals : PartialLVals → List LVal → Prop where
  | done {xs} :
      CompletesLVals (PartialLVals.done xs) xs
  | cutoff {xs} :
      CompletesLVals PartialLVals.cutoff xs
  | elemsDone {pre suffix : List LVal} :
      CompletesLVals (PartialLVals.elems pre none) (pre ++ suffix)
  | elemsTail {pre suffix : List LVal} {frontier : PartialLVal}
      {frontierCompletion : LVal} :
      CompletesLVal frontier frontierCompletion →
      CompletesLVals (PartialLVals.elems pre (some frontier))
        (pre ++ frontierCompletion :: suffix)

inductive CompletesTerms : PartialTerms → List Term → Prop where
  | done {xs} :
      CompletesTerms (PartialTerms.done xs) xs
  | cutoff {xs} :
      CompletesTerms PartialTerms.cutoff xs
  | elemsDone {pre suffix : List Term} :
      CompletesTerms (PartialTerms.elems pre none) (pre ++ suffix)
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
  | borrowTargets {mutable : Bool} {targets : PartialLVals}
      {targets' : List LVal} :
      CompletesLVals targets targets' →
      CompletesTy (PartialTy.borrowTargets mutable targets)
        (.borrow mutable targets')
  | boxElement {element : PartialTy} {element' : Ty} :
      CompletesTy element element' →
      CompletesTy (PartialTy.boxElement element) (.box element')

inductive CompletesLVal : PartialLVal → LVal → Prop where
  | done {x} :
      CompletesLVal (PartialLVal.done x) x
  | cutoff {x} :
      CompletesLVal PartialLVal.cutoff x
  | varName {x : PartialName} {x' : Name} :
      CompletesName x x' →
      CompletesLVal (PartialLVal.varName x) (.var x')
  | derefOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesLVal (PartialLVal.derefOperand operand) (.deref operand')

inductive CompletesValue : PartialValue → Value → Prop where
  | done {x} :
      CompletesValue (PartialValue.done x) x
  | cutoff {x} :
      CompletesValue PartialValue.cutoff x
  | intValue {n : Int} :
      CompletesValue (PartialValue.intValue n) (.int n)
  | boolValue {b : Bool} :
      CompletesValue (PartialValue.boolValue b) (.bool b)

inductive CompletesTerm : PartialTerm → Term → Prop where
  | done {x} :
      CompletesTerm (PartialTerm.done x) x
  | cutoff {x} :
      CompletesTerm PartialTerm.cutoff x
  | blockTerms {lifetime : Lifetime} {terms : PartialTerms}
      {terms' : List Term} :
      CompletesTerms terms terms' →
      CompletesTerm (PartialTerm.blockTerms lifetime terms)
        (.block lifetime terms')
  | letMutName {name : PartialName} {name' : Name}
      {initialiser : Term} :
      CompletesName name name' →
      CompletesTerm (PartialTerm.letMutName name)
        (.letMut name' initialiser)
  | letMutInitialiser {name : Name} {initialiser : PartialTerm}
      {initialiser' : Term} :
      CompletesTerm initialiser initialiser' →
      CompletesTerm (PartialTerm.letMutInitialiser name initialiser)
        (.letMut name initialiser')
  | assignLhs {lhs : PartialLVal} {lhs' : LVal} {rhs : Term} :
      CompletesLVal lhs lhs' →
      CompletesTerm (PartialTerm.assignLhs lhs) (.assign lhs' rhs)
  | assignRhs {lhs : LVal} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.assignRhs lhs rhs) (.assign lhs rhs')
  | boxOperand {operand : PartialTerm} {operand' : Term} :
      CompletesTerm operand operand' →
      CompletesTerm (PartialTerm.boxOperand operand) (.box operand')
  | borrowOperand {mutable : Bool} {operand : PartialLVal}
      {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.borrowOperand mutable operand)
        (.borrow mutable operand')
  | moveOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.moveOperand operand) (.move operand')
  | copyOperand {operand : PartialLVal} {operand' : LVal} :
      CompletesLVal operand operand' →
      CompletesTerm (PartialTerm.copyOperand operand) (.copy operand')
  | valValue {value : PartialValue} {value' : Value} :
      CompletesValue value value' →
      CompletesTerm (PartialTerm.valValue value) (.val value')
  | eqLhs {lhs : PartialTerm} {lhs' rhs : Term} :
      CompletesTerm lhs lhs' →
      CompletesTerm (PartialTerm.eqLhs lhs) (.eq lhs' rhs)
  | eqRhs {lhs : Term} {rhs : PartialTerm} {rhs' : Term} :
      CompletesTerm rhs rhs' →
      CompletesTerm (PartialTerm.eqRhs lhs rhs) (.eq lhs rhs')
  | iteCondition {condition : PartialTerm} {condition' trueBranch falseBranch : Term} :
      CompletesTerm condition condition' →
      CompletesTerm (PartialTerm.iteCondition condition)
        (.ite condition' trueBranch falseBranch)
  | iteTrueBranch {condition : Term} {trueBranch : PartialTerm}
      {trueBranch' falseBranch : Term} :
      CompletesTerm trueBranch trueBranch' →
      CompletesTerm (PartialTerm.iteTrueBranch condition trueBranch)
        (.ite condition trueBranch' falseBranch)
  | iteFalseBranch {condition trueBranch : Term} {falseBranch : PartialTerm}
      {falseBranch' : Term} :
      CompletesTerm falseBranch falseBranch' →
      CompletesTerm
        (PartialTerm.iteFalseBranch condition trueBranch falseBranch)
        (.ite condition trueBranch falseBranch')

end
"""


def main() -> None:
    if not SOURCE.exists():
        raise FileNotFoundError(SOURCE)
    template = TEMPLATE.read_text()
    if MARKER not in template:
        raise ValueError(f"missing marker {MARKER!r} in {TEMPLATE}")
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(template.replace(MARKER, GENERATED))


if __name__ == "__main__":
    main()
