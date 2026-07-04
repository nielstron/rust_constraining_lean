# Phase D Hard Sites

Status: the static preservation walks in
`LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean` remain green.  The
runtime induction is still blocked by proof obligations that are absent from the
single-target helper stack.

## 1. Deref move: struck owner spine after runtime write

Blocked helper:

`validPartialValueWhenInitialized_strike_write`

Needed use site:

`preservation_move_deref_boxFull_multistep_runtime_whenInitialized_of_wellFormed`

The old proof used `StoreOwnerSpineWhenInitialized.valid_after_strike_nonempty`.
That entire spine layer is gone in the single-target file.  The fresh proof must
replace it with a direct induction over `Strike`, aligned with the concrete
`ProgramStore.loc` chain from `Step.move`.

Concrete subgoals:

- At the strike leaf, the runtime write has updated the selected leaf slot to
  `.undef`, so the result must be rebuilt with
  `ValidPartialValueWhenInitialized.undef`.
- At each box or full-box step, the owner slot at the current owner location must
  be shown unchanged by the deeper leaf update.  This requires a distinctness
  proof between the current owner location and the selected leaf.  The available
  ingredients are `ValidPartialValueSkeleton.no_owned_path_to_storage`,
  `ValidStore` owner uniqueness, and the concrete ownership edge exposed by the
  valid box/full-box constructor.
- Borrow values inside sibling subtrees must be transported across the update:
  live targets need `store.loc` preservation, and stale targets remain stale.
  The variable case has this via
  `reachesWhenInitialized_var_ne_of_stored_not_writeProhibited`; the deref case
  needs the same frame generalized from a variable location to the selected
  heap leaf.
- After the store proof, the environment must be transported through `EnvMove`.
  The available current lemma
  `ValidPartialValueWhenInitialized.move_env` is sufficient only after the
  post-write validity in the source environment is established.

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

