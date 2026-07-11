import FWRust.Paper.Typing

/-!
The old environment-thinning counterexample used an empty borrow target list as
the strengthened side of a dereference.  Empty target lists are no longer
typable by `LValTargetsTyping`, so that historical construction is not a valid
typing derivation in the current calculus.
-/

namespace FWRust
namespace Paper

open Core

theorem no_empty_lval_targets_typing {env : Env} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    ¬ LValTargetsTyping env [] partialTy lifetime := by
  intro htyping
  cases htyping

end Paper
end FWRust
