# Phase D Hard Sites

## 2026-07-04 Runtime Preservation Port Attempt

What was completed in this pass:

- `LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean`
  - Added `PartialTyDefined`.
  - Added `Strike.not_defined`.
  - Added `LValTyping.defined_of_envMove`.
  - Added `TargetInitialized.of_envMove`.
  - Added `ValidPartialValueWhenInitialized.move_env`.
  - Added weak live-reach store-update framing:
    `validPartialValueWhenInitialized_update_of_not_live_reaches`.
  - Added the syntactic bridge from initialized runtime reads back to static
    write conflicts:
    `lval_loc_var_conflict_or_writeProhibited_whenInitialized`,
    `locReads_var_conflict_or_writeProhibited_whenInitialized`,
    `borrowDependencyWhenInitialized_var_writeProhibited`, and
    `reachesWhenInitialized_var_ne_of_stored_not_writeProhibited`.
  - Completed the first missing runtime helper:
    `preservation_move_var_multistep_runtime_whenInitialized_of_wellFormed`.
  - Verified with:

```bash
lake build LwRust.Paper.Soundness.Lemma_4_11_Preservation
```

- `LwRust/Paper/Soundness/Appendix9/Lemma_9_5_DropPreservation.lean`
  - Fixed the stale `RuntimeFrame.validValue_drops_of_avoids_reaches`
    reference by importing `Lemma_4_11_Preservation`, where the current
    runtime-frame export lives.
  - Verified with:

```bash
lake build LwRust.Paper.Soundness.Appendix9.Lemma_9_5_DropPreservation
```

- `LwRust/Paper/Soundness/InitialStates.lean`
  - Replaced stale full-safe source-initial bridge calls with direct
    `TerminalStateSafe` projections where no general preservation theorem is
    needed.
  - Replaced removed borrow-invariance wrapper calls with the completed static
    walk `typingPreservesWellFormedWhenInitialized_of_sourceTerm`.
  - The target still fails only at the exported `preservation` call sites while
    that theorem is absent:

```text
error: Unknown identifier `preservation`
```

Current hard proof site:

- `preservation_move_deref_box_multistep_runtime_whenInitialized_of_wellFormed`
  and `preservation_move_deref_boxFull_multistep_runtime_whenInitialized_of_wellFormed`
  are now the first unresolved runtime redex helpers.
- The direct-variable move case is solved by reducing the store write to
  `store.update (VariableProjection x) undef`, proving no initialized live
  reach from any surviving slot can inspect `x`, and transporting validity
  through `EnvMove`.
- The dereference move cases need a different structural lemma.  The runtime
  write updates the selected heap/interior location, while `EnvMove` changes
  the base environment slot by `Strike`.  The missing lemma must show that a
  base slot value valid at the source partial type remains valid at the struck
  partial type after the selected runtime location is updated to `undef`.
  Shape-wise this is a value/store counterpart of `Strike`:

```lean
ValidPartialValueWhenInitialized env store baseValue sourceTy →
LValTyping env movedLv (.ty ty) valueLifetime →
EnvMove env movedLv moved →
store.write movedLv .undef = some store' →
ValidPartialValueWhenInitialized moved store' baseValue struckTy
```

  More concretely, it should recurse over the `Strike` path and use
  `LValLocationAbstractionWhenInitialized` to align each static `.box`/
  `.ty (.box _)` spine step with the runtime owner reference.  At the struck
  leaf it should use `ValidPartialValueWhenInitialized.undef`; for unrelated
  subvalues it should use the new live-reach update frame.

## Current Compile Surface

`LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean` is now a fresh small
module and builds with:

```bash
lake build LwRust.Paper.Soundness.Lemma_4_11_Preservation
```

The old 11k-line proof has been moved to
`LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean.reference` for
consultation only.  It is out of the import graph.

The fresh module currently contains compatibility shims, local lifetime/frame
lemmas, owner-reach ownership helpers, the recursive `RuntimeFrame` drop-frame
export, the first lvalue-selected initialized well-formedness helpers, a
source-value well-formedness base helper, and a factored initialized
sequence-drop safe-abstraction lemma.  It deliberately does **not** export
unsound placeholders for the public preservation theorem.

## Remaining Missing Exports

Downstream soundness modules are red because these names have not been rebuilt:

- `preservation_bounded`
- `preservation`
- `typingPreservesWellFormedWhenInitialized_of_sourceTerm`

Current failing target:

```bash
lake build LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
```

Current errors from that target:

```text
error: LwRust/Paper/Soundness/Theorem_4_12_TypeAndBorrowSafety.lean:206:6: Unknown identifier `preservation_bounded`
error: LwRust/Paper/Soundness/Theorem_4_12_TypeAndBorrowSafety.lean:264:10: Unknown identifier `preservation_bounded`
error: LwRust/Paper/Soundness/Theorem_4_12_TypeAndBorrowSafety.lean:269:11: Unknown identifier `typingPreservesWellFormedWhenInitialized_of_sourceTerm`
error: LwRust/Paper/Soundness/Theorem_4_12_TypeAndBorrowSafety.lean:513:12: Unknown identifier `preservation`
```

This also blocks Appendix 9.9/9.10, which project value/store preservation from
`preservation`.

## Completed In Latest Session

- Added the first single-target `EnvWrite` static-invariant support in
  `Lemma_4_11_Preservation.lean`:
  - `UpdateAtPath.lifetimesSurvive`
  - `EnvWrite.lifetimesSurvive`
  - `LValBaseOutlives.write`
  - `LValBaseOutlives.of_write`
  - `UpdateAtPath.contains_borrow_result`
  - `EnvWrite.contains_borrow_source`
  - `EnvWrite.var_inv`
- Verified after each edit with:

```bash
lake build LwRust.Paper.Soundness.Lemma_4_11_Preservation
```

  The preservation module remains green.
- Rechecked downstream with:

```bash
lake build LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
```

  The downstream red surface is unchanged: the only unknown identifiers are
  still `preservation_bounded`,
  `typingPreservesWellFormedWhenInitialized_of_sourceTerm`, and
  `preservation`.
- Hole grep over the fresh preservation module and this note is clean.

## Completed In Previous Session

- Rebuilt the single-target move invariant layer in
  `Lemma_4_11_Preservation.lean`:
  - `Strike.contains_borrow`
  - `Strike.vars_subset`
  - `UpdateAtPath.contains_borrow`
  - `EnvMove.contains_borrow_source`
  - `WriteProhibited.of_contains_conflict`
  - `not_pathConflicts_of_not_writeProhibited_contains`
  - `EnvMove.preserves_linearizable`
  - `BorrowSafeEnv.move`
  - `LValTyping.contains_borrow`
  - `LValTyping.move_to_source_of_no_conflicts`
  - `LValTyping.deterministic`
  - `ContainedBorrowsWellFormedWhenInitialized.move`
  - `WellFormedEnvWhenInitialized.move`
- Verified after each edit with:

```bash
lake build LwRust.Paper.Soundness.Lemma_4_11_Preservation
```

  The preservation module remains green.  Hole grep over the fresh preservation
  module and this note is clean.

## Completed In Older Session

- Rebuilt the public initialized sequence value-drop frame export:
  - `safeAbstraction_seq_value_drop_whenInitialized`
- Added the single-target live-borrow frame layer used by that export:
  - `RuntimeFrame.ProtectedByBase`
  - `RuntimeFrame.lval_loc_protectedBySomeBase_whenInitialized`
  - `RuntimeFrame.locReads_protectedBySomeBase_whenInitialized`
  - `RuntimeFrame.BorrowDependencyWhenInitialized`
  - `RuntimeFrame.ReachesWhenInitialized`
  - `RuntimeFrame.validPartialValueWhenInitialized_erase_of_not_live_reaches`
  - `RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_live_reaches`
  - `RuntimeFrame.dropsAvoids_of_protectedByBase_unprotected_values`
  - `RuntimeFrame.dropsAvoids_of_borrowDependencyWhenInitialized_unprotected_values`
  - `RuntimeFrame.dropsAvoids_of_ownerReaches_stored`
  - `RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized`
- Rechecked downstream with:

```bash
lake build LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
```

  The sequence-drop unknown is gone.  Remaining unknown identifiers are
  exactly `preservation_bounded`, `typingPreservesWellFormedWhenInitialized_of_sourceTerm`,
  and `preservation`.

## Completed In Older Session

- Added owner-reach ownership facts needed by the sequence-drop and assignment
  frame rebuild:
  - `RuntimeFrame.store_owns_of_ownerReaches_stored`
  - `RuntimeFrame.store_owns_of_reaches_stored_validPartialValue`
  - `RuntimeFrame.store_owns_of_reaches_stored_validPartialValueWhenInitialized`
- Rechecked downstream with:

```bash
lake build LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
```

  At that point the unknown-identifier list still included the public
  sequence-drop wrapper; that wrapper has since been rebuilt in the current
  session.

## Completed In Older Session

- Added source-value well-formedness support for the `T-Const` preservation
  base case:
  - `ValueTyping.wellFormedTyWhenInitialized_of_sourceValue`
- Added a factored initialized `R-Seq` drop frame:
  - `safeAbstraction_seq_value_drop_whenInitialized_of_reaches`
  - The public wrapper is now rebuilt using the live-borrow
    `RuntimeFrame.ReachesWhenInitialized` frame, so stale borrow annotations do
    not require preserving dead runtime target reads.
- Checked that the `.reference` file is not close to a clean copy-forward:
  standalone elaboration fails immediately on stale multi-target borrow
  (`Ty.borrow mutable targets`), ranked `EnvWrite`/`UpdateAtPath`, and removed
  fan-out helpers such as `LValTargetsTyping`/`PartialTyUnion`.

- Added single-target `RuntimeFrame` erase/drop frame support in the fresh
  preservation module:
  - `RuntimeFrame.loc_erase_of_not_locReads`
  - `RuntimeFrame.validPartialValueSkeleton_erase_of_not_owner_reaches`
  - `RuntimeFrame.validPartialValue_erase_of_not_reaches`
  - `RuntimeFrame.validPartialValueWhenInitialized_erase_of_not_reaches`
  - `RuntimeFrame.ownerReaches_erase_to_store`
  - `RuntimeFrame.reaches_erase_to_store`
  - `RuntimeFrame.validPartialValue_drops_of_avoids_reaches`
  - `RuntimeFrame.validPartialValueWhenInitialized_drops_of_avoids_reachesWhenInitialized`
  - `RuntimeFrame.validValue_drops_of_avoids_reaches`
- Added lvalue-selected initialized well-formedness helpers:
  - `PartialTyBorrowsWellFormedInSlotWhenInitialized.box_inv`
  - `wellFormedTyWhenInitialized_of_partialTyBorrows`
  - `LValTyping.partialTyBorrowsWellFormedInSlotWhenInitialized`
  - `LValTyping.wellFormedTyWhenInitialized`
- Deleted obsolete out-of-graph example files:
  - `LwRust/Paper/Examples/ThinningFalse.lean`
  - `LwRust/Paper/Examples/BoxDerefPending.lean`
- Verified after each preservation-file edit with:

```bash
lake build LwRust.Paper.Soundness.Lemma_4_11_Preservation
```

## Proof Work Still Needed

- Prove strict/initialized well-formedness preservation for the current
  single-target rules.  Existing helper coverage now includes lifetime
  preservation for `EnvMove`, both lifetime directions for `EnvWrite`,
  `EnvSlotsOutlive.write`, `LValBaseOutlives.write`/`of_write`,
  result-borrow containment for `EnvWrite`, lvalue-selected initialized type
  well-formedness, and the full initialized `EnvMove` contained-borrow case.
  Remaining hard parts are: contained-borrow target-typing preservation across
  `EnvWrite` strong update (especially writes through mutable borrows, where
  the syntactic LHS base and effective updated root differ) and block
  `dropLifetime` contained-borrow preservation.
- Prove `EnvWrite.preserves_linearizable` for strong update over the current
  mutual `UpdateAtPath`/`EnvWrite`.
- Add `BorrowSafeEnv` preservation for general `EnvWrite` once the strong
  update conflict lemma is available.  `BorrowSafeEnv.move` is complete.
- Thread `WellFormedEnv`, `Linearizable`, and `BorrowSafeEnv` through
  `preservation_bounded`.
- Rebuild the move/assignment frame theorem in single-target form: if a
  surviving slot or RHS value reaches the written runtime leaf, that reach must
  contradict either owner uniqueness/protection or `¬ WriteProhibited`.
- Rebuild block lifetime-drop safe-abstraction frames using the retained
  `DropsAvoids` and `RuntimeFrame.Reaches` helpers.  The sequence value-drop
  case is now complete in initialized form.

Concrete next proof target for well-formedness: rebuild
`typingPreservesWellFormedWhenInitialized_of_sourceTerm` only after proving the
contained-borrow preservation pieces for `EnvWrite` and `dropLifetime`.  The
`EnvMove` case is now complete via `WellFormedEnvWhenInitialized.move`; the
current helper coverage for writes gives the lifetime/domain and borrow-origin
parts, but not yet the initialized-target typing transport needed to finish
`ContainedBorrowsWellFormedWhenInitialized.write`.
