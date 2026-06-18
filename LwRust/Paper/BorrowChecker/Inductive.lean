import LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance

/-!
Proof-facing closed-program borrow-checking predicates.
-/

namespace LwRust
namespace Paper

open Core

/--
Proof-facing closed-program borrow/type check.

This is the inductive property that a closed source term has some declarative
typing derivation from the empty environment and empty store typing.  The
executable boolean is `borrowCheck?`; `borrowCheck?_sound` bridges
from `borrowCheck? fuel term = true` to `borrowCheck term`.
-/
def borrowCheck (term : Term) : Prop :=
  ∃ ty env, TermTyping Env.empty StoreTyping.empty Lifetime.root term ty env

/--
Proof-facing closed-program rejection.

This is deliberately stronger than `borrowCheckFailed? fuel term = true`: an
executable rule failure is not yet a completeness theorem for non-typability.
Logical rejection is therefore exposed through proof-carrying rejection
certificates, with `CertifiedBorrowReject` packaging the closed-program case.
-/
def borrowReject (term : Term) : Prop :=
  ¬ borrowCheck term

theorem borrowCheck_of_typing {term : Term} {ty : Ty} {env : Env}
    (typing : TermTyping Env.empty StoreTyping.empty Lifetime.root term ty env) :
    borrowCheck term :=
  ⟨ty, env, typing⟩

theorem borrowReject_of_no_typing {term : Term}
    (notyping :
      ¬ ∃ ty env, TermTyping Env.empty StoreTyping.empty Lifetime.root term ty env) :
    borrowReject term := by
  intro hcheck
  exact notyping hcheck


end Paper
end LwRust
