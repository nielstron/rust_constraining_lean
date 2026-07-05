# Phase D Hard Sites

Status: `LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean` remains green
after adding the new strike/path and owner-chain extraction support, the
owner-route collapse helpers, the dereference-move runtime preservation
helpers, the direct-variable assignment owner-drop frame, and the pure
partial/full-box dereference-assignment runtime preservation wrappers, plus
the singleton block lifetime-drop runtime preservation helper:

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
- Added and compiled the singleton block lifetime-drop preservation path:
  `dropsAvoids_of_protectedByBase_lifetime_whenInitialized`,
  `lval_loc_dropsAvoids_lifetime_whenInitialized`,
  `locReads_dropsAvoids_lifetime_whenInitialized`,
  `borrowDependencyWhenInitialized_dropsAvoids_lifetime`,
  `RuntimeFrame.dropsAvoids_of_reaches_stored_validPartialValueWhenInitialized_of_frames`,
  `dropsAvoids_of_ownerReaches_value_lifetime_whenInitialized`, and
  `preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop`.
- Added and compiled small runtime re-rooting conveniences:
  `ProgramStore.loc_prependPath_eq_of_loc_eq`,
  `ProgramStore.read_eq_of_loc_eq`, and
  `ProgramStore.write_eq_of_loc_eq`.  These only package the runtime equality
  side of mutable-borrow hop re-rooting; the static/result-environment
  chain-collapse proof is still the remaining hard assignment step.
- Added and compiled the next runtime re-rooting wrappers:
  `assign_step_of_loc_eq`, `validRuntimeState_assign_lhs_of_value`,
  `lvalTyping_deref_borrow_loc_eq_whenInitialized`, and
  `assign_step_prependPath_deref_borrow_whenInitialized`.  These replay an
  assignment redex at an equal concrete location, show assignment runtime
  validity is independent of the syntactic lhs when the RHS is already a
  value, and package the live-borrow fact
  `store.loc source.deref = store.loc target` (plus any remaining deref
  suffix).  They are operational/runtimestore support only; they do not yet
  prove `EnvWrite.runtime_leaf_align` or rebuild the on-chain static slots.
- Added and compiled the first Round 14 hop-elimination conveniences:
  `Env.update_same_pointwise`, `EnvWrite.deref_borrow_var_inv`,
  `TargetInitialized.transport_of_pointwise`,
  `safeAbstractionWhenInitialized_transport_pointwise`, and
  `TerminalStateSafe.transport_env_pointwise`.  These provide the syntactic
  variable borrow-hop inversion and the pointwise environment transport needed
  after replaying an assignment at the re-rooted lvalue.  They do not yet lift
  the inversion through a box/boxFull prefix or rebuild restored on-chain
  holder slots after the nested write.
- Re-audited on 2026-07-05 after `chain_entry_env3`/`chain_entry_unique`:
  the keystone chain-entry facts are present and compile, but the runtime
  mut-borrow re-rooting bridge is still not present.  In particular,
  `EnvWrite.runtime_leaf_align`, the generalized post-`EnvWrite` chain-leaf
  reach frame for `UpdateAtPath.mutBorrow`, the unqualified
  `preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_wellFormed`,
  and `preservation_assign_deref_borrow_step_runtime_whenInitialized_of_wellFormed`
  are still absent.  The current pure full-box helper is only
  `preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_wellFormed_of_select`,
  requiring a `PathSelect` owner-only path witness; it cannot dispatch
  full-box paths whose source typing reaches `.ty (.box oldTy)` through
  `LValTyping.borrow`.
- Added and compiled the first Round 12 runtime-route increment:
  `LValTyping.transport_into_source_of_outside_chain`,
  `lval_loc_chain_protected_base_on_chain`,
  `ownerReaches_stored_ne_guarded_chain_leaf`,
  `locReads_chain_protected_base_on_chain`,
  `borrowDependencyWhenInitialized_chain_leaf_ne_of_outside_chain`,
  `reachesWhenInitialized_chain_leaf_ne_of_outside_chain`, and
  `reachesWhenInitialized_chain_leaf_ne_of_stored_outside_chain`.
  These prove that post-write typings rooted outside the guarded source chain
  transport back to the source environment, and that off-chain sibling slots
  cannot reach the guarded runtime leaf.  `Lemma_4_11_Preservation.lean`
  remains green after this increment.  This is not yet the full mut-borrow
  assignment proof: the structural hop-elimination proof still needs to lift
  `EnvWrite.deref_borrow_var_inv` through box/boxFull prefixes and directly
  rebuild on-chain borrow slots after the nested write.
- Added and compiled the Round 15 lvalue split:
  `LValTyping.tyBox_pathSelect_or_borrow`.  A full-box lvalue is now classified
  as either an owner-only `PathSelect` descent or an explicit first
  mutable-borrow hop
  `source = prependPath pref hopSource.deref` whose target re-types at the
  same full-box slot after the prefix.  Added
  `preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_wellFormed_of_no_borrow_hop`,
  which packages the already-proved full-box assignment helper for the
  owner-only branch and leaves exactly that explicit hop witness as the
  remaining re-rooting case.
- Added and compiled the corrected Round 16 pure write split:
  `UpdateAtPath.pathSelect_or_hop` and
  `EnvWrite.select_or_hop_update_same`, plus
  `EnvWrite.select_or_hop_of_nested_slot`.  The hop branch now records the
  fact that the local rebuilt type is unchanged and that the outer write result
  is `nested.update (LVal.base lhs) slot`; the pointwise form is available
  once supplied with the exact missing typed premise that the nested write
  preserves that outer holder slot.  This is intentionally weaker than the
  originally sketched pure pointwise branch: without typed no-write /
  borrow-safety data, the pointwise claim is false when the nested hop target
  writes back into the same outer holder base.  The remaining proof obligation
  is therefore the typed nested-slot preservation step under the actual
  assignment hypotheses, or equivalently the framed structural assignment
  theorem that avoids requiring `¬ WriteProhibited` for the reduced hop target.
- Added and compiled the typed Round 16 runtime split:
  `UpdateAtPath.pathSelect_or_hop_typed` and
  `EnvWrite.select_or_hop_typed`.  The hop branch now carries the reduced
  `EnvWrite`, the rebased reduced-lhs `LValTyping`, and the concrete runtime
  equality `store.loc lhs = store.loc reduced`.  The location/rebase part of
  the borrow-hop assignment bridge is therefore no longer missing.  The
  remaining blocker is the recursive environment frame: the reduced lhs can be
  `WriteProhibited` by the hop annotation itself, so the existing pure
  `_of_wellFormed` / `_of_frames` helpers cannot be invoked recursively with a
  per-level `¬ WriteProhibited`.  The next proof must either discharge the
  Round-17 `nested_slot_preserved_of_notWrite`/pointwise transport obligation
  using the top-level `¬ WriteProhibited`, or introduce the framed structural
  assignment theorem whose base cases consume the Round-12 guarded-leaf frames
  keyed to the original top-level write.
- Added and compiled the first Round 18 no-reentry packaging:
  `chainGuard_head_inv` and `chain_entry_source`.  The first decomposes a
  `ChainGuard` path into the root case or the root's first mutable-borrow edge;
  the second is the source-environment analogue of `chain_entry_env3`: any
  source annotation targeting into the guarded top-level write chain has an
  on-chain holder.  These are prerequisites for showing that a nested
  borrow-hop write cannot re-enter an already visited holder slot under the
  top-level `¬ WriteProhibited env₃ lhs` premise.  The remaining missing lemma
  is still the full no-reentry/nested-slot preservation step: when the reduced
  nested `EnvWrite`'s `chain_guarded` changed slot is an outer holder, the last
  edge back into the top chain must be classified in the final env and converted
  to `WriteProhibited env₃ lhs` using `BorrowSafeEnv` and the compiled
  chain-entry kernels.
- Added and compiled the first Round 19 no-reentry kernels:
  `chainGuard_self_edge_eq_root`,
  `borrowSafe_same_target_unique_edge`,
  `chainGuard_step_root_prohibited`, and
  `chainGuard_self_edge_eq_changed_slot`.  The first collapses a guarded
  mutable self-edge to the guard root by repeatedly comparing it with the
  preceding chain edge via `BorrowSafeEnv`.  The second packages the
  non-self-edge uniqueness step: when two annotations target the same guarded
  base, `BorrowSafeEnv` gives the same holder and unary slot containment pins
  the annotation to the chain edge.  The third packages the root-entry
  exclusion: a source mutable annotation targeting the top write root must be
  held at the single changed/graft slot, otherwise it survives through `hne`
  into `env₃` and contradicts `¬ WriteProhibited env₃ lhs`.  The fourth combines
  the root and self-edge facts for the degenerate re-entry/self-edge branch,
  forcing such an edge to be at the changed slot.  This does not yet finish
  `top_prefix_in_nested`/`nested_slot_preserved`; the remaining hard case is the
  induction that uses the unique-entry step to walk a non-self nested re-entry
  back toward the top root, then discharges the graft-slot/root case with the
  graft-target exclusion.
- Added and compiled the Round 20 mechanical frame extraction:
  `PathSelect.update_borrows`,
  `WriteProhibited.transport_of_pointwise`,
  `not_writeProhibited_of_pointwise`, and
  `WellFormedEnvWhenInitialized.transport_of_pointwise`.  Refactored
  `preservation_assign_deref_box_step_runtime_whenInitialized_of_frames` and
  `preservation_assign_deref_boxFull_step_runtime_whenInitialized_of_frames`
  so they consume already-transported RHS and sibling validities instead of a
  local `¬ WriteProhibited` premise; their well-formed callers now construct
  those validities from `validPartialValueWhenInitialized_envWrite_of_result_contains`.
  Added `preservation_assign_var_step_runtime_whenInitialized_of_frames` and
  rewrote `preservation_assign_var_step_runtime_whenInitialized_of_wellFormed`
  as the wrapper that derives its four frame/validity premises from the
  existing variable no-write facts.

The final `lake build` is not green yet because `preservation` is still not
exported.  Rechecked on 2026-07-05 after the compiled helper additions above;
current full-build failures are:

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
guarded static slot to the re-rooted runtime leaf.  A re-audit confirmed that
this is not final-theorem plumbing: `Theorem_4_12_TypeAndBorrowSafety` is
parameterized by preservation rather than proving it, and the old reference
borrow-hop proof depends on removed rank/selected-target machinery.

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
  root-update version is complete.  The off-chain sibling portion of the
  guarded-chain frame is now compiled via
  `reachesWhenInitialized_chain_leaf_ne_of_stored_outside_chain`.  Remaining:
  the borrow-hop branch exposed by
  `LValTyping.tyBox_pathSelect_or_borrow` must re-root the runtime step from
  `source.deref` to `prependPath pref target`, invert the corresponding
  `EnvWrite`/`UpdateAtPath.mutBorrow` subderivation through any owner prefix,
  and transport the terminal/safe-abstraction conclusion across the
  pointwise-equal outer updates.  Use the Round 14 hop-elimination route rather
  than `EnvWrite.runtime_leaf_align`:
  replay the runtime step at the re-rooted lvalue, recurse on the nested
  `EnvWrite`, transport pointwise-equal terminal states, and rebuild the
  guarded on-chain borrow slots directly.
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
  Off-chain sibling slots now have the needed reach exclusion.  RHS/graft
  values still need the corresponding graft-contained target exclusion at the
  re-rooted nested write leaf, and chain slots between the original base and
  the graft slot must be rebuilt rather than framed.
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

Completed helper:

`preservation_blockB_value_multistep_runtime_whenInitialized_of_runtimeDrop`

The value-level and stored-slot lifetime-drop frames are now present and the
singleton `R-BlockB` proof compiles.  The terminal value is framed with
`dropsAvoids_of_ownerReaches_value_lifetime_whenInitialized`; surviving
environment slots use the stored-slot frame plus
`borrowDependencyWhenInitialized_dropsAvoids_lifetime`, and the final safe
abstraction is rebuilt with `dropPreservation_lifetime_whenInitialized`.

## 5. Final induction and downstream callers

The final `preservation_bounded` skeleton from the reference remains portable
after the helpers above exist.  It should add a `BorrowSafeEnv env₁` hypothesis:
`strict_assign_rule_result_counterexample` in the fresh file shows that
`WellFormedEnv env₁ lifetime` alone is insufficient for the strict assignment
walk.  Empty initial call sites can discharge the extra premise with
`borrowSafeEnv_empty`.
