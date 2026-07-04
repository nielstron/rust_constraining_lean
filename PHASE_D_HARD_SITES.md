# Phase D Hard Sites

Status: `LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean` remains green
after adding the new strike/path and owner-chain extraction support, the
owner-route collapse helpers, the dereference-move runtime preservation
helpers, the direct-variable assignment owner-drop frame, and the first
pure-owner dereference-assignment alignment kernel:

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

The final `lake build` is not green yet because `preservation` is still not
exported.  Current full-build failures are:

- `Appendix9/Lemma_9_9_ValuePreservation.lean:37`: unknown identifier
  `preservation`.
- `Appendix9/Lemma_9_10_StorePreservation.lean:49`: unknown identifier
  `preservation`.
- `InitialStates.lean:278` and `InitialStates.lean:676`: unknown identifier
  `preservation`.

The remaining blocker is the dereference-assignment result-environment frame:
the owner-chain leaf and pure-box `UpdateAtPath` alignment are now available,
but the RHS value and surviving slots still have to be transported into the
post-`EnvWrite` environment while excluding live borrow dependencies that reach
the selected heap leaf.  This is the generalized
`reachesWhenInitialized_*_ne_of_stored_not_writeProhibited` step under
`EnvWrite.chain_guarded`; the direct-variable version is not strong enough
because the runtime write location is a heap leaf while the static change is a
guarded root/graft slot.

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

- `preservation_assign_deref_box_step_runtime_whenInitialized_of_wellFormed`
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
  now-proved direct variable version to the selected heap leaf.  Borrow-reach
  cases must conclude `WriteProhibited env₃ lhs` from
  `EnvWrite.chain_guarded`, `LValTyping.exists_env3`, and the strict
  `BorrowSafeEnv`/`TyBorrowSafeAgainstEnv` facts; owner-reach cases are covered
  by the owner-route collapse helpers.
- Extract the concrete selected leaf from `Step.assign` and the lhs
  `LValTyping` derivation via `lvalTyping_defined_location_whenInitialized`.
- For the partial-box owner-chain case, use the new `PathSelect`/`EnvWrite`
  kernel to show that static `EnvWrite` descends through boxes and changes the
  owner root slot.  The full-box and borrow-hop assignment cases still need the
  corresponding rebasing step under `EnvWrite.chain_guarded`.
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

The missing bridge is a lifetime-drop-specific proof that values being dropped
at the block lifetime cannot be protected by a dependency of a surviving slot or
the terminal value.  The proof should use `LifetimeChild`, `EnvSlotsOutlive`,
heap slots at root lifetime, and `lifetimeDropOwnersDisjoint_of_heapRootLifetime`.

## 5. Final induction and downstream callers

The final `preservation_bounded` skeleton from the reference remains portable
after the helpers above exist.  It should add a `BorrowSafeEnv env₁` hypothesis:
`strict_assign_rule_result_counterexample` in the fresh file shows that
`WellFormedEnv env₁ lifetime` alone is insufficient for the strict assignment
walk.  Empty initial call sites can discharge the extra premise with
`borrowSafeEnv_empty`.
