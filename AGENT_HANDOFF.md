# Agent Handoff

## Mission

Validate the transport layers by continuing the attempt to remove the extra
premises from `LwRust/Paper/Typing.lean`. The target is that preservation and
soundness should no longer depend on the old paper-extension premises:

- `EnvJoinSameShape`
- `Coherent`
- `ContainedBorrowsWellFormed`

Do not re-add those premises to typing rules. Derive whatever weak runtime
facts are actually needed from the remaining premises.

The current user hint is important: for the `undef`/non-`undef` merge, relax the
storage abstraction. This is already the right direction. The relaxation should
be at the runtime evidence boundary, not by weakening typing.

## Current Build State

Run from `/home/niels/rust_constraining_lean`.

Passing:

```bash
lake build LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance
```

Failing:

```bash
lake build LwRust.Paper.Soundness.Lemma_4_11_Preservation
```

The preservation failure is stable. Main errors:

- `T-Move` calls `preservation_move_var_multistep_runtimeSafe_of_wellFormed`
  and `preservation_move_deref_box_multistep_runtimeSafe_of_wellFormed`, but
  the current preservation motive supplies only `EnvSlotsOutlive`, not
  `WellFormedEnv`.
- The `T-Move` branch returns `TerminalStateRuntimeSafe`, while the new motive
  expects `TerminalStateRelaxedValueSafe`.
- `typingPreservesWellFormed_of_sourceTerm` is referenced in preservation, but
  that theorem is intentionally gone/commented out. Do not resurrect it.
- Assignment helpers still expect strict `RuntimeEnvAbstraction`; the IH now
  provides `RelaxedRuntimeEnvAbstraction`.
- While and block cases still contain stale premise-era plumbing and old binder
  assumptions.

## Dirty Files

Current dirty files:

```text
LwRust/Paper/Soundness/Helpers/BorrowSafety.lean
LwRust/Paper/Soundness/Helpers/Frame.lean
LwRust/Paper/Soundness/Helpers/GhostErasure.lean
LwRust/Paper/Soundness/Lemma_4_10_Progress.lean
LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean
LwRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean
LwRust/Paper/Typing.lean
```

Do not revert unrelated work. Treat these as in-progress proof-layer edits.

## Important Existing Infrastructure

The following infrastructure already builds in
`LwRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean`.

Storage abstraction:

- `RelaxedRuntimeEnvAbstraction`
- `RelaxedRuntimeEnvAbstractionWithSlotProtection`
- `RelaxedRuntimeEnvAbstraction.update_var`
- `RelaxedRuntimeEnvAbstraction.update_of_evidenceFrame`
- `RelaxedRuntimeEnvAbstractionWithSlotProtection.update_of_evidenceFrame`
- `RelaxedRuntimeEnvInvariant`
- `RelaxedRuntimeEnvInvariantWithSlotProtection`

Runtime evidence:

- `RuntimeFrame.RelaxedValidPartialValueEvidence`
- `RuntimeFrame.relaxedValidPartialValueEvidence_update_of_owner_and_evidence_dependency_frame`

Terminal wrappers:

- `TerminalValueProtected`
- `TerminalValueProtected.of_protected_read`
- `TerminalStateRelaxedRuntimeSafe`
- `TerminalStateRelaxedValueSafe`
- `TerminalStateSlotProtectedRuntimeSafe`
- `TerminalStateSlotProtectedValueSafe`

Useful redex helpers already exist for relaxed copy, borrow, box, declare, and
some drop cases. Move and assignment are the main stale areas.

## Key Design Constraint

The relaxed storage abstraction is sound because `undef` evidence is lossy:

```lean
RuntimeFrame.RelaxedValidPartialValueEvidence.undef
```

It intentionally forgets concrete owner/dependency evidence hidden behind an
abstract `undef` slot. That is appropriate for the slot being moved from or for
join abstraction.

Do not globally weaken non-`undef` evidence. Concrete evidence for live values
still needs dependency protection. For lifetime drops, use the slot-protected
variant (`ProtectedByBaseOutliving`) rather than plain protection.

## Recommended Next Step

Start with direct variable move. It is the cleanest failing family.

Add a relaxed variable-move helper near the existing move wrappers in
`Lemma_4_9_BorrowInvariance.lean`, around the current
`preservation_move_var_multistep_runtimeSafe_of_wellFormed` area.

Target shape:

```lean
theorem preservation_move_var_multistep_relaxedValue_of_transport
    {store finalStore : ProgramStore} {env1 env2 : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {x : Name} {finalValue : Value} {ty : Ty} :
    RelaxedRuntimeEnvAbstraction store env1 ->
    BorrowSafeEnv env1 ->
    ValidRuntimeState store (.move (.var x)) ->
    env1.slotAt x = some { ty := .ty ty, lifetime := valueLifetime } ->
    EnvMove env1 (.var x) env2 ->
    TermTyping env1 typing lifetime (.move (.var x)) ty env2 ->
    MultiStep store lifetime (.move (.var x)) finalStore (.val finalValue) ->
    TerminalStateRelaxedValueSafe finalStore finalValue env2 ty := by
  ...
```

The exact name/signature can change, but avoid requiring `WellFormedEnv`.

Proof ingredients:

1. Invert the one `Step.move`.
2. Use `lvalTyping_protected_location_full_of_relaxed` plus
   `TerminalValueProtected.of_protected_read` to protect the moved value in the
   pre-store.
3. Transport that terminal value evidence across:

```lean
store.update (VariableProjection x)
  { value := .undef, lifetime := valueLifetime }
```

4. Use `RelaxedRuntimeEnvAbstraction.update_var` for the post environment. The
   moved slot gets:

```lean
RuntimeFrame.RelaxedValidPartialValueEvidence.undef
```

5. Prove frame facts for other slots and for the moved value. This is the real
   missing bridge: derive that selected owner/dependency evidence for other
   non-`undef` slots cannot mention `VariableProjection x` from:

```lean
BorrowSafeEnv env1
not WriteProhibited env1 (.var x)
RelaxedRuntimeEnvAbstraction store env1
```

There are older well-formedness-based lemmas for this around:

- `borrowDependency_not_protectedByBase_of_varsProtectedIn`
- `movedValue_reaches_ne_protected_leaf`
- `RuntimeFrame.value_reaches_ne_var_of_varsProtected`

Those currently rely on `WellFormedEnv`. Either replace them with a weaker
runtime-evidence version or prove a narrow version just for variable move.

## Likely Helper To Add First

A general terminal value transport helper would reduce duplication:

```lean
theorem TerminalValueProtected.update_of_evidenceFrame
    {store : ProgramStore} {updated : Location} {newSlot : StoreSlot}
    {value : Value} {ty : Ty} :
    TerminalValueProtected store value ty ->
    (forall location,
      RuntimeFrame.RelaxedEvidenceOwnerReach store evidence location ->
      location != updated) ->
    (forall location,
      RuntimeFrame.RelaxedEvidenceBorrowDependency store evidence location ->
      location != updated) ->
    (forall location,
      RuntimeFrame.RelaxedEvidenceBorrowDependency store evidence location ->
      forall base,
        ProtectedByBase store base location ->
        ProtectedByBase (store.update updated newSlot) base location) ->
    TerminalValueProtected (store.update updated newSlot) value ty
```

This sketch needs existential elimination because `TerminalValueProtected`
hides `evidence`. The implementation should `rcases hprotected with
<evidence, hdepsProtected>` and then call:

```lean
RuntimeFrame.relaxedValidPartialValueEvidence_update_of_owner_and_evidence_dependency_frame
```

## Preservation Edits After The Helper

In `LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean`, update the `T-Move`
case around the current failing lines near 5384.

Replace the well-formedness-based calls with the new relaxed helper. The branch
must return `TerminalStateRelaxedValueSafe`, not `TerminalStateRuntimeSafe`.

The deref-box move case can be deferred if necessary, but the final proof needs
a matching relaxed helper for it too. Variable move is the smaller proof and
should validate the storage-abstraction approach first.

## Do Not Do This

- Do not re-add `EnvJoinSameShape`, `Coherent`, or
  `ContainedBorrowsWellFormed` to `Typing.lean`.
- Do not resurrect `typingPreservesWellFormed_of_sourceTerm` from the old block
  comment.
- Do not convert all relaxed abstraction back to strict abstraction just to make
  preservation compile.
- Do not weaken non-`undef` evidence so much that borrow dependencies become
  unprotected.

## Useful Commands

```bash
rg -n "preservation_move_var|RelaxedRuntimeEnvAbstraction.update_var|TerminalValueProtected" \
  LwRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean

rg -n "case move|typingPreservesWellFormed_of_sourceTerm|RuntimeEnvAbstraction" \
  LwRust/Paper/Soundness/Lemma_4_11_Preservation.lean

lake build LwRust.Paper.Soundness.Lemma_4_9_BorrowInvariance
lake build LwRust.Paper.Soundness.Lemma_4_11_Preservation
```

## One-Sentence Prompt For The Next Agent

Continue removing the extra typing premises by replacing preservation's stale
well-formedness-based move/assignment/while transport with relaxed runtime
storage abstraction; start by proving direct variable move preservation over
`RelaxedRuntimeEnvAbstraction`, using lossy `undef` evidence only for the moved
slot and protected concrete evidence everywhere else.
