import LwRust.Paper.Soundness

/-!
# Lemma 4.9 (Borrow Invariance)

Paper statement (Section 4.3):

> Let `S₁ ▷ t` be a valid state; let `σ` be a store typing where `S₁ ▷ t ⊢ σ`;
> let `Γ₁` be a well-formed typing environment with respect to a lifetime `l`
> where `S₁ ∼ Γ₁` and `Γ₂` be an arbitrary typing environment; let `t` be a
> term; and let `T` be a type.  If `Γ₁ ⊢ ⟨t : T⟩^l_σ ⊣ Γ₂`, then `Γ₂[γ ↦ T^l]`
> is well-formed with respect to `l` for arbitrary `γ ∈ fresh`.

Status: reduced to the Appendix 9.6 update/borrow-invariance facts, packaged as
`UpdateBorrowInvariantObligations` and discharged by
`updateBorrowInvariantObligations_appendix96`.

The borrow invariant is now mechanised **faithfully per target** (Definition
4.8(i): each individual target lval `w` of a contained borrow is typable with
`m ≼ n`), as opposed to the earlier — and unsound — joint target-list typing
`Γ ⊢ ū : ⟨T⟩^m` (Definition 3.21, which belongs to the well-formed *type*
judgement established at borrow creation by `T-LvBor`, not to the runtime
invariant).  This was the root cause that blocked the environment-join case: rule
W-Bor merges the target *lists* of two joined borrows without joining their
pointee types, so the merged list has no joint typing in general, yet each target
keeps its own per-target typing.  With the per-target statement:

* the previously **false** obligation `partialTyUnion_preserves_borrows` is now a
  theorem (`PartialTyBorrowsWellFormedInSlot.of_partialTyUnion`);
* the borrow-target join transport uses the single-lval
  `FullLValTypingJoinTransport` (no joint cons-union landmark);
* the single-lval determinism keystone `lvalTyping_eqv`/`lvalTyping_sameShape`
  (from the linearizability rank φ) is fully proven and unconditional.

Two deep landmark `sorry`s remain inside
`updateBorrowInvariantObligations_appendix96`, both genuine Appendix 9.6 content
on the now-sound per-target foundation:
1. `derefLValTypingJoinConstructorSplitLandmarks_appendix96.borrow_borrow` —
   transporting a deref-of-borrow (reborrow) typing across an environment join;
2. `EnvWrite.preserves_core_appendix96` — one-step `EnvWrite` preservation of the
   contained-borrow / borrow-target-transport invariants.
-/

namespace LwRust.Paper.Soundness

open LwRust.Paper LwRust.Core

/-- Lemma 4.9, unconditional form (modulo the Appendix 9.6 join sorries inside
`updateBorrowInvariantObligations_appendix96`). -/
theorem lemma_4_9_borrowInvariance
    {store : ProgramStore} {env₁ env₂ : Env} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty} {gamma : Name}
    (hrefs : ∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime)
    (hvalid : ValidState store term)
    (hstoreTyping : ValidStoreTyping store term typing)
    (hwellFormed : WellFormedEnv env₁ lifetime)
    (hsafe : store ∼ₛ env₁)
    (htyping : TermTyping env₁ typing lifetime term ty env₂)
    (hfresh : env₂.fresh gamma) :
    WellFormedEnv (env₂.update gamma { ty := .ty ty, lifetime := lifetime })
      lifetime :=
  borrowInvariance updateBorrowInvariantObligations_appendix96
    hrefs hvalid hstoreTyping hwellFormed hsafe htyping hfresh

end LwRust.Paper.Soundness
