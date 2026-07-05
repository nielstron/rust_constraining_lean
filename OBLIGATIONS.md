# Remaining Obligations

State (branch `fix/reduce`): the full `lake build` is green and there is no
`sorry`, `admit`, or `axiom` anywhere in `LwRust/`.  All remaining gaps are
**explicit hypotheses in theorem statements**, listed here.

## 1. Critical: prove and export `preservation` (Lemma 4.11)

No compiled whole-term `preservation` theorem exists.  The only complete
proof of it is in `LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean.reference`
(the pre-single-target development; not compiled, not imported).  Every final
safety theorem currently takes the Lemma 4.11 conclusion as an explicit
hypothesis — the `terminalSafety` parameter of shape

```
∀ …, SourceTerm term → ValidRuntimeState store term →
  ValidStoreTyping store term typing → WellFormedEnv env₁ lifetime →
  BorrowSafeEnv env₁ → store ≈ₛ env₁ →
  TermTyping env₁ typing lifetime term ty env₂ →
  MultiStep store lifetime term finalStore (.val finalValue) →
  FullTerminalStateSafe finalStore finalValue env₂ ty
```

Sites carrying it (all discharge every *other* premise at empty initial
states, so this parameter is the single remaining assumption):

- `Theorem_4_12_TypeAndBorrowSafety.lean`: `terminatesAsValue_bounded`,
  `terminatesAsValue`, `theorem_4_12_typeAndBorrowSafety`,
  `theorem_4_12_typeAndBorrowSafety_total`
- `InitialStates.lean`: `emptyInitial_preservation`,
  `lemma_4_11_preservation_emptyInitial`, `emptyInitial_typeAndBorrowSafety`
  (+ `_total`), `theorem_4_12_typeAndBorrowSafety_emptyInitial`
- `Appendix9/Lemma_9_9_ValuePreservation.lean` and
  `Appendix9/Lemma_9_10_StorePreservation.lean`: currently trivial
  projections of the assumed `FullTerminalStateSafe` premise (their other
  premises are ignored); they regain content once the premise is a theorem.

The assumption is not vacuous:
`Examples/TypeSafetyReject.lean` (`MutableBorrowAssignmentExample`) shows the
mutable-borrow-hop assignment `let mut x = 0; let mut p = &mut x; *p = 1` is
well-typed and reachable from the empty initial state — exactly the hard case
the missing induction must cover.

### Proof state and plan

Proved in `Lemma_4_11_Preservation.lean` (live, green):

- per-redex runtime preservation for moves (var / deref-box / deref-boxFull),
  direct-variable and dereference assignments, declare, and block exit;
- the borrow-hop write kernel: pointwise transport
  (`chainGuard_cycle_prohibited`, `EnvWrite.hop_nested_slot_preserved`), the
  hop-iteration keystone `EnvWrite.select_final` with the traversed-spine
  export (`HopsTo`), the reads telescope
  (`HopsTo.locReads_ne_of_links_clean`), and the per-link discharge
  (`clean_hop_link_of_guarded_leaf`).

Remaining, in order:

1. **Sibling on-chain frame**: the `ChainGuard` coverage walk and the frame
   assembly for slots on the write chain but distinct from the changed slot.
   (An 18-line pinning lemma `edge_into_final_base_eq` for this sits in
   `git stash` from the pre-pull session.)
2. **General assign theorem**: assemble the hop kernel + frames into
   preservation for assignment through arbitrary mutable-borrow chains.
3. **Whole-term induction**: port the `preservation_bounded` skeleton from
   the `.reference` file (threading `BorrowSafeEnv env₁`), export
   `preservation`, and replace the `terminalSafety` hypotheses at the sites
   above.

## 2. Optional: collapse the stale-aware interior

The final theorem statements already conclude the strict paper predicates
(`FullTerminalStateSafe`, strict abstraction `≈ₛ`).  The per-redex helper
lemmas still run over the stale-aware `WhenInitialized` family and upgrade at
the end (`TerminalStateSafe.full_of_wellFormed`).  With conditionals removed,
stale borrow annotations plausibly cannot arise at all; collapsing the
interior to the strict predicates would simplify the development but is not
needed for the headline theorems.

## 3. Paper-sync items to keep documented (or eliminate)

Tracked in `DIFFERENCES.md`; listed here as potential future work:

- `LValBaseOutlives`: Definition 4.8(i) and L-Borrow carry an extra
  "borrow target's base slot outlives the reference" conjunct not present in
  the printed definitions.  Either keep (documented) or attempt removal.
- `T-Block`'s `LifetimeChild` requires an *immediate* child lifetime; the
  paper only assumes nesting.
- `T-Assign` checks the lhs typing / shape / rhs well-formedness in the
  post-rhs environment (the follow-up's convention), not the core's pre-rhs
  `Γ₁`.
- `CopyTy` counts `unit` as copyable (printed Definition 3.6 lists only
  `int` and immutable borrows).
