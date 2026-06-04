import LwRust.Core.BorrowChecker
import LwRust.Core.OperationalSemantics

/-!
Formal proof layer for the core calculus.

The executable translation in `Core.BorrowChecker` and `Core.OperationalSemantics`
mirrors the Java implementation with stateful environments, partial moves,
borrows and heap locations.  The executable definitions are the authoritative
objects for the FR proof statements below.

TODO: Prove the general `Executable.Progress` and `Executable.Soundness`
predicates for all terms accepted by `BorrowChecker.checkProgram`.  The next
step is to introduce inductive checker/evaluator relations corresponding to
`BorrowChecker.checkTerm` and `OperationalSemantics.eval`, then prove adequacy
lemmas connecting those relations back to the executable functions.
-/

namespace LwRust
namespace Core
namespace Proofs

namespace Executable

mutual
  inductive ValueHasType : LwRust.Core.Value → Ty → Prop where
    | unit : ValueHasType .unit Ty.unit
    | int (n : Int) : ValueHasType (.int n) Ty.int
    | tuple {values : List LwRust.Core.Value} {tys : List Ty} :
        ValuesHaveTypes values tys →
        ValueHasType (.tuple values) (.tuple tys)

    -- TODO: References require the heap typing relation between
    -- `OperationalSemantics.State` and `BorrowChecker.Env`.
    | ref {r : Reference} :
        ValueHasType (.ref r) (.borrow false [])

    -- TODO: Moved values should only appear inside the store; connecting this to
    -- `Ty.undef` requires the executable store typing invariant.
    | moved {ty : Ty} :
        ValueHasType .moved (.undef ty)

  inductive ValuesHaveTypes : List LwRust.Core.Value → List Ty → Prop where
    | nil : ValuesHaveTypes [] []
    | cons {value : LwRust.Core.Value} {values : List LwRust.Core.Value} {ty : Ty} {tys : List Ty} :
        ValueHasType value ty →
        ValuesHaveTypes values tys →
        ValuesHaveTypes (value :: values) (ty :: tys)
end

def Progress : Prop :=
  ∀ term ty,
    BorrowChecker.checkProgram term = .ok ty →
    ∃ value, OperationalSemantics.execute term = .ok value

def Soundness : Prop :=
  ∀ term ty value,
    BorrowChecker.checkProgram term = .ok ty →
    OperationalSemantics.execute term = .ok value →
    ValueHasType value ty

theorem progress : Progress := by
  -- TODO: Prove via inductive checker/evaluator relations plus adequacy lemmas
  -- for `BorrowChecker.checkProgram` and `OperationalSemantics.execute`.
  sorry

theorem soundness : Soundness := by
  -- TODO: Prove preservation of the executable store typing invariant across
  -- `OperationalSemantics.eval`, then discharge result typing.
  sorry

end Executable

end Proofs
end Core
end LwRust
