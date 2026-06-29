# Handoff: Exposed Coherence From Concrete Writes

Date: 2026-06-29

## Verified Status

- `lake env lean LwRust/Paper/Soundness/Lemma_4_9_BorrowInvariance.lean` passes.
- The last full `lake build` completed successfully before the final unverified helper attempt was backed out.
- No proof placeholders or trusted declarations were introduced in the touched soundness files.

## Main Progress

- Added lvalue-exposed coherence predicates:
  - `PartialTyExposedCoherent`
  - `PartialTyExposedOutputCoherent`
  - `PartialTyExposedStepCoherent`
  - global/root-local lvalue-output variants.
- Added rank-based transport across root updates:
  - `LValTyping.update_of_rank_lt`
  - `LValTyping.update_of_rank_lt_result`
  - `PartialTyExposedCoherent.update_of_rank_lt_result`
- Added concrete assignment-leaf exposed-output coherence from `ShapeCompatible`:
  - `ShapeCompatible.right_exposedOutputCoherent`
  - `ShapeCompatible.join_partialTyExposedOutputCoherent`
  - `UpdateAtPath.leaf_partialTyExposedOutputCoherent`
  - positive/non-fan-out `EnvWrite` wrappers.
- Added direct mutable-borrow traversal exposed coherence:
  - `UpdateAtPath.pathThroughMutBorrow_partialTyExposedCoherent_below`
- Added block-scoped branch/drop facts and exposed-coherence reachability predicates in `InitialStates.lean` and `Helpers/Validity.lean`.

## Current Remaining Gap

The assignment preservation cases still use:

- `have hcoh3 := hcoherentTyping hwellFormed hassignTyping`

The intended replacement is to construct `LValTypingExposedOutputsCoherent env₃` directly from:

- source `Coherent env₂` from the RHS induction result,
- final `LinearizedBy φ env₃`,
- `EnvWrite 0 env₂ lhs rhsTy env₃`,
- `ShapeCompatible env₂ oldTy (.ty rhsTy)`,
- `EnvWriteRhsTargetsWellFormed env₃ rhsTy`,
- `¬ WriteProhibited env₃ lhs`.

Then use `LValTypingExposedOutputsCoherent.coherent` to obtain `Coherent env₃`, and pass the same exposed-output invariant into `containedBorrowsWellFormed_assign`.

## Hard Part

The direct mutable-borrow theorem currently proves exposed coherence of the crossed borrow node:

- target list is typable in the fan-out result.

It does not yet prove the stronger target-output/step coherence needed to replace the preservation oracle:

- after typing the fan-out target list, the produced output partial type must itself be exposed coherent.

A generic theorem from `LValTargetsTyping result targets resultTy` plus lower-root outputs is not sound: `LValTargetsTyping.cons` can join target outputs without proving the assignment-specific compatibility that justifies newly merged borrow lists. The proof has to follow the concrete `WriteBorrowTargets`/positive-rank `EnvWrite` branches and use the `ShapeCompatible` leaf evidence.

## Attempt Backed Out

I tried adding:

- `UpdateAtPath.positive_writeShapeCompat`
- `UpdateAtPath.pathThroughMutBorrow_writeShapeCompat`

The route is plausible, but the first version was placed before `PathThroughMutBorrow` was defined and had an incorrect wrapper from `EnvWrite` back to `UpdateAtPath`. I backed it out rather than committing an unverified helper. If retried, place the through-borrow helper after `PathThroughMutBorrow`, and unpack selected `EnvWrite` branches carefully.

## Suggested Next Step

Prove a generated fan-out theorem, not a generic join theorem:

```lean
WriteBorrowTargets ... ->
  ... ->
  LValTargetsTyping source targets (.ty targetTy) targetLifetime ->
  PartialTyExposedCoherent source (.ty targetTy) ->
  ...
  ∃ resultTy resultLifetime,
    LValTargetsTyping result targets (.ty resultTy) resultLifetime ∧
    PartialTyExposedCoherent result (.ty resultTy)
```

The `cons` case should use concrete selected branch writes / positive-rank weak leaf `ShapeCompatible` evidence, then transport selected branch evidence into the joined fan-out result. Avoid deriving this from `EnvJoinSameShape` alone.
