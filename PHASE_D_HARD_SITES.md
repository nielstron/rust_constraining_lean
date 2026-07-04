# Phase D Hard Sites

Status: `LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean` remains green
after adding the new strike/path and owner-chain extraction support:

- `LValTyping.strike_suffix` factors a strike at a typed lvalue into the
  remaining suffix over that lvalue's type.
- `OwnerChainAt.extend`, `ownsChain_extend`, `OwnerChainPrefix.extend`, and
  `ProgramStore.loc_eq_var_of_path_nil` package the zero-or-owner-chain runtime
  facts needed by dereference moves.
- `lvalTyping_box_ownerChainPrefix_whenInitialized` and
  `lvalTyping_tyBox_ownerChainPrefix_whenInitialized_of_strike` derive the
  runtime chain prefix, root/leaf slots, and root/leaf validity directly from
  `SafeAbstraction`, `LValTyping`, and `Strike`.

The final `lake build` is not green yet because `preservation` is still not
exported.  The next blocker is no longer owner-chain acyclicity itself, but the
initialized reachability frame needed after writing the selected heap leaf.

## 1. Deref move: struck owner spine after runtime write

Former hard blocker:

`validPartialValueWhenInitialized_strike_write` is now present and green.

Current needed use site:

`preservation_move_deref_boxFull_multistep_runtime_whenInitialized_of_wellFormed`

The old proof used `StoreOwnerSpineWhenInitialized.valid_after_strike_nonempty`.
The fresh file now has the direct `Strike`/`OwnerChainAt` replacement and the
runtime lvalue-chain extractors listed above.

Remaining concrete subgoals:

- Use `lvalTyping_tyBox_ownerChainPrefix_whenInitialized_of_strike` on the
  source lvalue, extend the returned prefix by the final `.boxFull` edge, then
  feed the resulting `OwnerChainAt`/`OwnsChain` into
  `validPartialValueWhenInitialized_strike_write`.
- Generalize the solved variable reachability frame
  `reachesWhenInitialized_var_ne_of_stored_not_writeProhibited` from
  `VariableProjection x` to the selected heap leaf of an owner chain.  Owner
  reaches should be discharged by `ValidPartialValueWhenInitialized.
  no_storage_ownership_cycle`/`ValidStore`; live borrow reaches need the
  corresponding `¬ WriteProhibited env source.deref` conflict exclusion.
- Use that generalized frame for the moved value and for all other safe
  abstraction slots via `validPartialValueWhenInitialized_update_of_not_live_reaches`,
  then transport through `ValidPartialValueWhenInitialized.move_env`.

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

- Extract the concrete selected leaf from `Step.assign` and the lhs
  `LValTyping` derivation via `lvalTyping_defined_location_whenInitialized`.
- Prove that the static `EnvWrite` changed either no slot or the single
  chain-guarded graft slot, and that this slot is the root whose runtime value
  owns the selected leaf.
- Preserve the RHS value and unaffected environment slots after the runtime
  write using `validPartialValueWhenInitialized_update_of_not_live_reaches`.
  The existing variable frame is insufficient because the updated location is
  a heap leaf rather than `VariableProjection x`.
- Complete the post-write/post-drop runtime invariants using the existing
  drop-orphan machinery once the leaf-alignment frame is available.

## 3. Direct variable assign: old owner values

Blocked helper:

`preservation_assign_var_step_runtime_whenInitialized_of_wellFormed`

Existing helper:

`preservation_assign_var_old_nonOwner_step_runtime_whenInitialized_of_preserved`

The existing helper covers old lhs values that are known non-owning.  That is
enough for old shapes `.unit`, `.int`, and borrow types via
`safeAbstraction_var_read_nonOwner_of_envShape`.  It is not enough for direct
variable assignment where `ShapeCompatible env oldTy (.ty rhsTy)` permits
`oldTy = .ty (.box T)` and `rhsTy = .box U`.  In that case the old slot can own a
heap tree and the assignment step drops the overwritten value after the write.

Concrete subgoals:

- Build the full old-owner direct-variable assignment frame over
  `validRuntimeState_assign_step_of_postWriteDrop_invariants`.
- Show owners in the old value become orphaned after the write, then are safely
  removed by `Drops`.
- Preserve the RHS value and all other variables through write plus drop using
  the existing reach/drop-avoidance lemmas.

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
