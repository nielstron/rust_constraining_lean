# Phase D Hard Sites

Status: `LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean` remains green
after adding the new strike/path and owner-chain extraction support, the
owner-route collapse helpers, the dereference-move runtime preservation
helpers, the direct-variable assignment owner-drop frame, and the pure
partial-box dereference-assignment runtime preservation wrapper:

- `LValTyping.strike_suffix` factors a strike at a typed lvalue into the
  remaining suffix over that lvalue's type.
- `OwnerChainAt.extend`, `ownsChain_extend`, `OwnerChainPrefix.extend`, and
  `ProgramStore.loc_eq_var_of_path_nil` package the zero-or-owner-chain runtime
  facts needed by dereference moves.
- `lvalTyping_box_ownerChainPrefix_whenInitialized` and
  `lvalTyping_tyBox_ownerChainPrefix_whenInitialized_of_strike` derive the
  runtime chain prefix, root/leaf slots, and root/leaf validity directly from
  `SafeAbstraction`, `LValTyping`, and `Strike`.
- `ownsChain_unique`, `ownsChain_append`, `ownerReaches_ownsChain_stored`, and
  `ownerReaches_stored_ne_chain_leaf` discharge owner-reach sibling cases for
  chain-leaf writes.
- `preservation_move_deref_box_multistep_runtime_whenInitialized_of_wellFormed`
  and
  `preservation_move_deref_boxFull_multistep_runtime_whenInitialized_of_wellFormed`
  are now proved and compile.
- Direct-variable assignment support now includes the post-write orphaned-owner
  drop frame (`safeAbstractionWhenInitialized_drops_of_orphaned_values_early`,
  `droppedValueOwnersOrphaned_assign`) plus result-environment static transport
  facts (`envWrite_var_rhs_vars_writeProhibited`,
  `envSlot_partialTy_vars_writeProhibited`,
  `LValTyping.envWrite_var_to_source_of_no_conflicts`, and
  `validPartialValueWhenInitialized_envWrite_var_of_no_write`).
- Direct-variable assignment runtime preservation is now proved:
  `preservation_assign_var_step_runtime_whenInitialized_of_wellFormed`.
  The new result-environment variable reach frame is
  `lval_loc_var_conflict_or_writeProhibited_envWrite_var`,
  `locReads_var_conflict_or_writeProhibited_envWrite_var`,
  `borrowDependencyWhenInitialized_envWrite_var_writeProhibited`, and
  `reachesWhenInitialized_var_ne_of_envWrite_var_not_writeProhibited`.
- Pure partial-box dereference assignment now has a static/runtime descent
  kernel:
  `PathSelect`, `PathSelect.snoc_box`, `PathSelect.update_env_eq`,
  `LValTyping.box_pathSelect`, `EnvWrite.deref_box_update_eq`, and
  `validPartialValueWhenInitialized_updateAtPath_write`.  These replace the
  old rank-zero owner-spine fact for the part of `EnvWrite` that descends
  through actual owner boxes: the write result is a single root-slot update,
  and the owner-chain leaf write realizes the `UpdateAtPath` result when the
  RHS validity has already been framed in the result environment and updated
  store.
- Added and compiled two strict post-write environment transport helpers:
  `TargetInitialized.envWrite` and
  `validPartialValueWhenInitialized_envWrite_of_result_contains`.  These move
  initialized target typings and initialized value validity from the source
  environment to the post-`EnvWrite` environment using
  `EnvWrite.chain_guarded`, `LValTyping.exists_env3`, `BorrowSafeEnv`, and
  `TyBorrowSafeAgainstEnv`.  The stale-borrow branch is discharged from
  `EnvWrite.contains_borrow_source`: result annotations are either RHS-origin
  and strictly well-formed in the source environment, or source-slot-origin and
  covered by `ContainedBorrowsWellFormed`.
- Added and compiled `PathSelect.update_contains_rhs` and
  `EnvWrite.deref_box_result_contains`.  These record the pure owner-path
  static fact needed by dereference assignment: along a box-only selected path,
  RHS borrow annotations appear in the updated root slot of the post-write
  environment.
- Added and compiled the pure full-box static companions
  `PathSelect.snoc_boxFull`,
  `EnvWrite.deref_boxFull_update_eq_of_select`, and
  `EnvWrite.deref_boxFull_result_contains_of_select`.  These cover the
  `tyBox` version of the same `PathSelect` owner path: once a
  `PathSelect (LVal.path source) slot.ty (.ty (.box oldTy))` witness is
  available, writing `source.deref` is characterized as a single root-slot
  update and RHS borrows are contained in that updated result slot.
- Added and compiled the runtime/static bridge for pure selected owner paths:
  `OwnerChainPrefix.prepend_owner`,
  `PathSelect.ownerChainPrefix_whenInitialized`, and
  `PathSelect.exists_strike_undef`.  The full-box assignment proof uses the
  last bridge to reuse the already-proved `Strike`/`OwnerChainAt` runtime
  extractor rather than duplicating the lvalue descent.
- Added and compiled the initialized lifetime-drop safe-abstraction wrappers
  `safeAbstractionWhenInitialized_dropLifetime_of_preserved`,
  `dropPreservation_lifetime_whenInitialized`, and the
  `dropLifetime_*_whenInitialized` domain helpers.  These are prerequisites for
  the singleton `R-BlockB` lifetime-drop proof.
- Added and compiled
  `preservation_assign_deref_box_step_runtime_whenInitialized_of_frames`, a
  framed pure-box dereference-assignment helper.  It proves the entire runtime
  assignment/write/drop step once supplied with the two result-environment
  reach-exclusion frames: one for the RHS value and one for every unchanged
  sibling slot.  This isolates the remaining assignment work to the generalized
  post-`EnvWrite` reach frame.
- Added and compiled the pure root-update post-`EnvWrite` chain-leaf reach
  frame:
  `LValTyping.update_var_to_source_of_no_conflicts`,
  `lval_loc_chain_leaf_conflict_or_writeProhibited_update_var_whenInitialized`,
  `locReads_chain_leaf_conflict_or_writeProhibited_update_var_whenInitialized`,
  `borrowDependencyWhenInitialized_chain_leaf_update_var_writeProhibited`, and
  `reachesWhenInitialized_chain_leaf_ne_of_update_var_not_writeProhibited`.
  This covers the `PathSelect` owner path where the static write result is a
  single update at `LVal.base lhs`; it does not cover
  `UpdateAtPath.mutBorrow` re-rooting.
- Added and compiled `ownerReaches_ownsChain_value` and
  `ownerReaches_value_ne_chain_leaf_of_unowned_root`, which exclude RHS owner
  roots from the selected heap leaf using term-store disjointness,
  `ValueOwnerTargetsHeap`, and `ownsChain_unique`.
- Added and compiled
  `preservation_assign_deref_box_step_runtime_whenInitialized_of_wellFormed`.
  The pure partial-box dereference assignment case is now proved end-to-end.
- Added and compiled
  `preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_frames`
  and
  `preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_wellFormed_of_select`.
  This proves the full-box dereference assignment for the pure `PathSelect`
  owner path.  The unqualified full-box helper is still pending because it
  must split off the `UpdateAtPath.mutBorrow` route and dispatch that route to
  the borrow-hop/re-rooting proof.

The final `lake build` is not green yet because `preservation` is still not
exported.  Rechecked after the compiled helper additions above; current
full-build failures are:

- `Appendix9/Lemma_9_9_ValuePreservation.lean:37`: unknown identifier
  `preservation`.
- `Appendix9/Lemma_9_10_StorePreservation.lean:49`: unknown identifier
  `preservation`.
- `InitialStates.lean:278` and `InitialStates.lean:676`: unknown identifier
  `preservation`.

The remaining assignment blocker is the non-pure write-chain case.  The
post-`EnvWrite` reachability frame is now proved for the `PathSelect` owner
path where the changed static slot is `LVal.base lhs`; the still-missing step
is the `UpdateAtPath.mutBorrow` re-rooting case needed by full-box paths that
pass through a mutable borrow and by the direct borrow-hop assignment helper.
That case must restart the runtime owner-chain extraction at the borrowed
target's base variable and use `EnvWrite.chain_guarded` to relate the final
guarded static slot to the re-rooted runtime leaf.

## 1. Deref move: struck owner spine after runtime write

Former hard blocker:

`validPartialValueWhenInitialized_strike_write` is now present and green.

Current needed use site:

`preservation_move_deref_boxFull_multistep_runtime_whenInitialized_of_wellFormed`

The old proof used `StoreOwnerSpineWhenInitialized.valid_after_strike_nonempty`.
The fresh file now has the direct `Strike`/`OwnerChainAt` replacement and the
runtime lvalue-chain extractors listed above.

Completed: both dereference move helpers are proved.  The owner-chain witness is
extracted from the runtime lvalue computation, the struck static slot is aligned
with `EnvMove`, and all other slots are framed with the chain-leaf reach
exclusion.

## 2. Deref assign: runtime leaf and static graft alignment

Blocked helpers:

- `preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_wellFormed`
- `preservation_assign_deref_borrow_step_runtime_whenInitialized_of_wellFormed`

The old proof aligned the runtime write location with the static write result
through `StoreOwnerSpineWhenInitialized` plus ranked selected-target machinery.
The single-target file replaces the static side with
`EnvWrite.chain_guarded`, `LValTyping.exists_env3`,
`LValTyping.transport_of_outside_chain`, and the strict write kernel, but it
does not yet expose a runtime lemma connecting the selected heap leaf from
`ProgramStore.loc (.deref source)` to the guarded static chain.

Concrete subgoals:

- Generalize the initialized reachability/result-environment frame from the
  now-proved direct variable version to the selected heap leaf.  The pure
  root-update version is complete; the remaining borrow-reach cases are the
  `UpdateAtPath.mutBorrow` cases that re-root the runtime descent at the borrow
  target's base variable while still concluding `WriteProhibited env₃ lhs`.
- Extract the concrete selected leaf from `Step.assign` and the lhs
  `LValTyping` derivation via `lvalTyping_defined_location_whenInitialized`.
- For the partial-box owner-chain case, use the new `PathSelect`/`EnvWrite`
  kernel to show that static `EnvWrite` descends through boxes and changes the
  owner root slot.  Completed.  The pure full-box owner path is also completed
  via the `_of_select` wrapper.  The remaining work is the non-pure
  `UpdateAtPath.mutBorrow` route: full-box paths that pass through a mutable
  borrow must split to the same re-rooted proof as the direct borrow-hop
  assignment helper.
- Preserve the RHS value and unaffected environment slots after the runtime
  write using `validPartialValueWhenInitialized_update_of_not_live_reaches`.
  The existing variable frame is insufficient because the updated location is
  a heap leaf rather than `VariableProjection x`.
- Complete the post-write/post-drop runtime invariants using the existing
  drop-orphan machinery once the leaf-alignment frame is available.

## 3. Direct variable assign: old owner values

Completed helper:

`preservation_assign_var_step_runtime_whenInitialized_of_wellFormed`

The helper now covers old lhs values that own heap trees.  It writes the RHS
value, frames the RHS and sibling slots using the post-`EnvWrite` variable
reach exclusion, proves overwritten owners orphaned with
`droppedValueOwnersOrphaned_assign`, and drops the old value through
`safeAbstractionWhenInitialized_drops_of_orphaned_values_early` plus
`validRuntimeState_assign_step_of_postWriteDrop_invariants`.

## 4. Singleton block final value lifetime drop

Blocked helper:

`preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop`

Most of the old proof can be reused, but these WhenInitialized lifetime-drop
helpers are not present in the fresh file:

- `dropPreservation_lifetime_whenInitialized`
- `dropLifetime_domain_equiv_of_ownerTargetsHeap_whenInitialized`
- a value-level `dropsAvoids_of_reaches_validPartialValueWhenInitialized`
- `borrowDependencyWhenInitialized_dropsAvoids_lifetime`

The file already has stored-slot variants:

- `dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized`
- `dropsAvoids_of_borrowDependencyWhenInitialized_unprotected_values`

The missing bridge is still the value-level lifetime-drop-specific proof that
values being dropped at the block lifetime cannot be protected by a dependency
of the terminal value.  The stored-slot preservation path has the needed
variants, but the terminal value branch still needs a
`dropsAvoids_of_reaches_validPartialValueWhenInitialized`-style lemma for
`DropsLifetime`.  The proof should use `LifetimeChild`, `EnvSlotsOutlive`, heap
slots at root lifetime, `ValidRuntimeState.storeTermDisjoint`, and
`lifetimeDropOwnersDisjoint_of_heapRootLifetime`.

## 5. Final induction and downstream callers

The final `preservation_bounded` skeleton from the reference remains portable
after the helpers above exist.  It should add a `BorrowSafeEnv env₁` hypothesis:
`strict_assign_rule_result_counterexample` in the fresh file shows that
`WellFormedEnv env₁ lifetime` alone is insufficient for the strict assignment
walk.  Empty initial call sites can discharge the extra premise with
`borrowSafeEnv_empty`.
