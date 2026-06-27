# Agent Handoff

## STATUS (session 2 end): GREEN BUILD RESTORED — premise removal to be redone incrementally

`lake build` is GREEN (3003 jobs) again. Root-cause diagnosis (verified):
commit `81a25bf` "Reduce the typing premises" removed `EnvJoinSameShape`+`Coherent`
from T-If/T-While (and `ContainedBorrowsWellFormed`+`Coherent` from T-While,
`Coherent` from T-Assign) AND switched preservation to a relaxed abstraction, but
left the migration UNFINISHED — 5 preservation cases + `Theorem_4_12`/`Appendix9`
broken. Its parent `9c8daae` builds green. So this session restored the green
baseline by `git checkout 9c8daae -- LwRust/` (the unfinished breaking migration
is reverted in the working tree; `81a25bf` is preserved in git history).

### Why a wholesale "remove all three at once" migration is the wrong shape
The removed facts are load-bearing for preservation (move/assign frames need
`ContainedBorrowsWellFormed`; the WellFormed-preservation rec needs same-shape +
`Coherent` at joins). Removing them all at once breaks the chain. BUT they are
NOT all equally hard to re-derive:
- `EnvJoinSameShape`: **derivable** from the kept `EnvJoin` + the runtime
  abstraction — `EnvJoin.sameShape_{left,right}_of_safeAbstraction`
  (RuntimeFacts ~1107) / `_of_runtimeEnvAbstraction` (Lemma_4_9 ~8740) already
  exist. Paper Def 3.10 confirms same-shape is a join INVARIANT ("will always be
  the case"), so removing it as a premise and deriving it is the paper-faithful
  move.
- `ContainedBorrowsWellFormed`: derivable from `Coherent`+same-shape via
  `containedBorrowsWellFormed_join` (Lemma_4_9 ~3169) — supply same-shape from the
  abstraction.
- `Coherent`: removal is the HARD one — `Coherent`-of-join needs
  `EnvJoinCoherenceObligations` (RuntimeFacts ~30), whose target-transport has a
  circularity (forward `LValTyping` transport itself needs `Coherent` of the join,
  via `lvalTyping_transport_of_sameShapeStrengthening` Lemma_4_9 ~3050). Paper
  Def 3.8 treats coherence as built into the join, so keeping `Coherent` as a
  rule obligation is defensibly paper-faithful; full removal needs a non-circular
  runtime-coherence argument (`RuntimeCoherent`, RuntimeFacts ~1489–1690).

### Recommended incremental plan (each step ends GREEN)
Work from the green baseline. For each premise, change the rule, then derive it at
every use (thread the runtime abstraction into `typingPreservesWellFormed` so the
join cases call the `*_of_runtimeEnvAbstraction` lemmas), and fix the constructor
arity at every match (preservation, progress, Theorem_4_12, extractor, examples).
Order: (1) drop `EnvJoinSameShape` (derive); (2) drop `ContainedBorrowsWellFormed`
from T-While (derive); (3) decide on `Coherent` (keep as paper-faithful invariant,
or remove via the runtime-coherence route). Verify `lake build` green after each.

### Session-2 relaxed-abstraction artifacts (now reverted in tree, in history)
The relaxed `WritableRootsUnborrowed` move-frame layer +
`preservation_move_var_multistep_relaxedValue_of_invariant` +
`containedBorrowsWellFormed_join_of_runtimeAbstraction` were built and compiled on
top of `81a25bf` this session (see git stash / the `81a25bf` tree). They are an
alternative (relaxed) route; the incremental-from-green route above is simpler.

---


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

## PAPER EVIDENCE (settles the strategy) — read with the breakthrough below

`paper/lw_rust.pdf` Definition 3.10 (Environment Join): environments are joined by
joining the types of all variables, and "We additionally require that variables are
declared in the same lifetime but, in fact, **this will always be the case**." So
the paper treats same-shape as an *invariant that always holds*, NOT a checked
premise on T-If; and Def 3.8 combines borrows "in a coherent fashion" as part of
the join. CONCLUSION: removing `EnvJoinSameShape`/`Coherent` as Lean rule premises
is the paper-faithful direction; re-adding them would DIVERGE from the paper. The
correct fix is to DERIVE them (from `EnvJoin` + the runtime abstraction), which is
guaranteed possible because the paper's own soundness depends on these invariants
holding. This is the work below.

## BREAKTHROUGH (session 2, late) — the join blocker is FALSE; read this first

Earlier in this session I (wrongly, following the previous agent's commented-out
note) believed `ContainedBorrowsWellFormed` cannot be preserved across `T-If`/
`T-While` joins without the removed `EnvJoinSameShape` premise. **That is false.**
`EnvJoinSameShape` is *derivable from the kept `EnvJoin` premise plus the runtime
abstraction* — the lemmas already exist:
`EnvJoin.sameShape_left_of_runtimeEnvAbstraction` /
`...right...` (Lemma_4_9 ~11795). I used them to build and COMPILE:

  `containedBorrowsWellFormed_join_of_runtimeAbstraction`  (Lemma_4_9, ~11835)
    RuntimeEnvAbstraction store {left,right,join} → EnvJoin → CBWF left → CBWF
    right → Coherent join → Linearizable join → CBWF join

So CBWF transports through joins with NO `EnvJoinSameShape` premise. This means
**`WellFormedEnv`/CBWF CAN be threaded as a preservation-internal invariant**
(established at the well-formed entry, preserved per rule), which is exactly the
"derive the weak version from existing premises + runtime semantics" goal — and it
does NOT re-add anything to Typing.lean's rules.

### Concrete path to green (now de-risked — each step is a known lemma)

1. Rebuild `typingPreservesWellFormed` as
   `typingPreservesWellFormed_of_runtimeAbstraction` (the commented-out
   `typingPreservesWellFormed_of_ruleCarriedObligations` at Lemma_4_9 ~3880 is the
   template; it already handles move/declare/assign/block/eq/cons via existing
   per-rule lemmas `move_preserves_wellFormed`, `block_preserves_wellFormed`,
   `containedBorrowsWellFormed_assign`, …). Changes vs the template:
   - Thread the (relaxed or strict) runtime abstraction so the `ite`/`while` join
     cases call `containedBorrowsWellFormed_join_of_runtimeAbstraction` instead of
     destructuring the removed `hsameLeft/hsameRight` premises.
   - `Coherent join` for `T-If`: the rule no longer carries it. Derive it (README:
     "coherence is derivable for core programs") or thread `Coherent` as part of
     the invariant (T-While keeps it via `hcoh`). If a `coherent_join_of_*` lemma
     is missing, build it (joint target typing of the union from branch coherence
     + same-shape-from-abstraction).
   - `Linearizable join`: `T-If` keeps `Linearizable env₅`; `T-While` keeps it.
2. Thread `WellFormedEnv store-env` (or just CBWF + EnvSlotsOutlive + Coherent +
   Linearizable) through the preservation motive with a strengthened conclusion
   carrying it for the result env (destructure `⟨hterminal, hwf'⟩` to preserve
   existing accessors). The move/assign/while/singleton cases then have
   `WellFormedEnv` and use the EXISTING strict helpers
   (`preservation_move_var_multistep_runtimeSafe_of_wellFormed`,
   `preservation_assign_*`, `preservation_whileRunEnds`) — OR the relaxed helper
   `preservation_move_var_multistep_relaxedValue_of_invariant` after deriving
   `WritableRootsUnborrowed` from CBWF via `WritableRootsUnborrowed.of_wellFormed`.
   Either way the frame faithfulness is now available.
3. Fix the downstream consumers (`Theorem_4_12`, `Appendix9`) that reference the
   commented-out `typingPreservesWellFormed_of_sourceTerm`: point them at the
   rebuilt lemma. The extractor (`NestedBlocks`) arity fixes are already done.

This is a large but now-MECHANICAL assembly (no open research problem remains).
The lossy `WritableRootsUnborrowed` family stays as the move-frame discharge layer.

## REFINED DIAGNOSIS (session 2) — read this first

The original "use `update_var` with plain `RelaxedRuntimeEnvAbstraction`" recipe
is **insufficient as stated**, for a precise reason. Confirmed by reading the
definitions and `README.md` lines 175–183.

What `update_var` actually needs (its `hotherFrame`) is: for every *other* slot
`y ≠ x`, its evidence's borrow dependencies must avoid `VariableProjection x`.
The borrow-dependency half is the only hard part (owner-reach trivially avoids
variable roots via `StoreOwnerTargetsHeap`).

`RelaxedRuntimeEnvAbstraction` only records, per dependency, `∃ base,
ProtectedByBase store base location` (see def at ~7993). For a dependency equal
to `VariableProjection x`, this forces `base = x` (variable roots are not
owned-transitively) — which gives **no contradiction** with
`¬ WriteProhibited env (.var x)` on its own. The protected-deps invariant
(`RuntimeRepresentedSlotsProtected`, ~7918) was explicitly designed for *drops*
("protected by some live base") and is genuinely too weak for *move*, which
needs the dual "the dependency is not the writable moved root".

Why no runtime evidence fixes this directly: both `ValidPartialValue` (strict,
SafeAbstraction.lean:33 V-Borrow) and `RelaxedValidPartialValueEvidence`
(Frame.lean:721 borrow) record only `target ∈ targets` + `store.loc target =
location` + (relaxed) `LocReads store target dep`. Neither carries an
`LValTyping env target …` for the borrow target. So a dependency
`LocReads store target (Var x)` cannot be turned into `WriteProhibited (.var x)`
without typing `target` — i.e. without `ContainedBorrowsWellFormed` (a removed
premise). README's `**x`/`*x` counterexample (`p ↦ &mut [*x]`, `q ↦ &mut [**x]`)
is exactly this gap.

**The intended faithfulness key is `BorrowSafeEnv` (already in the motive).** It
forbids the conflicting-targets configuration (`*x ⋈ **x` ⇒ same root), which is
what makes the move frame TRUE. But to USE it you still need the env-typing of
borrow targets to run the bridge — `borrowDependency_var_writeProhibited_or_mem_vars`
(~5757) and `borrowDependency_protected_writeProhibited_or_mem_vars` (~5806) do
exactly the right reasoning but currently take full `WellFormedEnv` (used only via
`lval_loc_or_reads_protected_writeProhibited_or_base` / `locReads_var_writeProhibited_or_base`
at ~4319, which need `LValTyping` of the target).

Also confirmed: full `WellFormedEnv` cannot be re-threaded — its preservation
(`typingPreservesWellFormed_of_sourceTerm`) is gone because CBWF preservation
across `join` itself needs the removed `EnvJoinSameShape`-era transport facts
(see `EnvJoin.preserves_containedBorrowsWellFormed_of_target_transport`,
RuntimeFacts.lean ~920). So CBWF-as-premise is also blocked at `join`.

### Two viable resolutions (pick one)

1. **Thread a join-transportable semantic invariant** (recommended). Define e.g.
   `WritableRootsUnborrowed store env :=` for every represented slot `y` and every
   *selected* borrow dependency `d`, if `d = VariableProjection z` then
   `WriteProhibited env (.var z)`. This is:
   - derivable initially from `ContainedBorrowsWellFormed` + `∼ₛ` via the existing
     `borrowDependency_protected_writeProhibited_or_mem_vars` (both disjuncts give
     `WriteProhibited`), so it holds at the empty/source-initial env;
   - **join-transportable without `EnvJoinSameShape`** the same way
     `RuntimeRepresentedSlotsProtected` is (it is store-side selected-dependency
     data + a monotone `WriteProhibited` fact), which is the whole point of the
     proof-carrying `RuntimeEnvAbstraction` (comment at ~7950).
   Then `move`/`assign` discharge their frame from this invariant + `BorrowSafeEnv`
   directly, no `WellFormedEnv`. Cost: add it to the preservation motive and
   re-establish it in every case (most cases trivial: no env change / fresh slot).

2. **Refactor the bridge lemmas to `RelaxedRuntimeEnvAbstraction + BorrowSafeEnv`**
   and have the relaxed abstraction additionally carry, per represented slot, the
   `LValTyping env target` of each contained borrow target (a runtime CBWF). This
   is heavier (touches the abstraction's data) but localizes the change.

### Infrastructure built this session (compiles in `Lemma_4_9`)

New, all building, placed just after `RuntimeRepresentedSlotsProtected.of_containedBorrowsWellFormed`:

- `def WritableRootsUnborrowed store env` — for every represented slot's borrow
  dependency `location` protected by base `z`, `WriteProhibited env (.var z)`.
  This is the join-transportable weak invariant replacing CBWF for move/assign.
- `WritableRootsUnborrowed.relaxedEvidence_borrowDependency_ne_var` — discharges
  `update_var`'s `hotherFrame` borrow obligation (`location ≠ VariableProjection x`).
- `WritableRootsUnborrowed.protectingBase_ne_writable` — discharges
  `update_var`'s `hprotectedTransport` (the protecting base `≠ x`, so
  `ProtectedByBase.update_of_not_protected` transports the protection across the
  `Var x → undef` update; note variable roots are not owned-transitively, so
  `¬ ProtectedByBase store base (Var x) ↔ base ≠ x`).
- `WritableRootsUnborrowed.of_wellFormed` — entry establishment from
  `WellFormedEnv + ∼ₛ + ValidStore + StoreOwnerTargetsHeap`, via the existing
  `borrowDependency_protected_writeProhibited_or_mem_vars` (both disjuncts give
  `WriteProhibited`).
- `RuntimeFrame.ownerReaches_stored_ne_var` — owner-reach from a stored
  (partial) value never hits a variable root (heap-only; needs just
  `StoreOwnerTargetsHeap`).
- `WritableRootsUnborrowed.move_value_frame` — packaged moved-value frame:
  `Reaches store (.value value) (.ty ty) loc → loc ≠ Var x`.

Also built & compiling (the rest of the toolkit):
- `RuntimeFrame.RelaxedEvidenceOwnerReach.ownerReaches` (concreteness-free).
- `WritableRootsUnborrowed.move_other_frame` (`update_var`'s `hotherFrame`).
- `TerminalValueProtected.update_of_frame` (moved-value protection transport).

### DONE: full variable-move helper (compiles)

`preservation_move_var_multistep_relaxedValue_of_invariant`
(hyps: `RelaxedRuntimeEnvAbstraction store env₁`, `WritableRootsUnborrowed store
env₁`, `ValidRuntimeState`, slot, `EnvMove`, `¬WriteProhibited`, `MultiStep`) →
`TerminalStateRelaxedValueSafe`, with NO `WellFormedEnv`. Placed right after
`preservation_move_var_multistep_relaxedRuntime_of_wellFormed` in `Lemma_4_9`.
This is the premise-free replacement for
`preservation_move_var_multistep_runtimeSafe_of_wellFormed`.

### Remaining to land the green build

1. **Deref-box move**: analogous `preservation_move_deref_box_..._of_invariant`
   (the moved leaf is a heap box owner, not the variable root; reuse the same
   discharge lemmas — the borrow frame still goes through `WritableRootsUnborrowed`
   for OTHER slots, and the moved leaf's frame is owner/heap).
2. **Thread `WritableRootsUnborrowed` through the preservation motive** (task #6).
   KEY REALIZATION (session 2): it is NOT enough to add it only as a motive
   *hypothesis*. Sequencing cases (`cons`, `ite`, `block` list, `while` body)
   call the sub-IH on the *post-sub-evaluation* state `(store', resultEnv)`, so
   they need the invariant THERE — which only the strengthened *conclusion*
   provides. Therefore:
   - Add `WritableRootsUnborrowed store env₁` as a **premise** of
     `preservation_bounded` (after `RelaxedRuntimeEnvAbstraction`), intro it,
     and pass it at the `TermTyping.rec` application.
   - Add it to motive_1 and motive_2 as a hypothesis (after
     `RelaxedRuntimeEnvAbstraction store env`).
   - **Strengthen the motive CONCLUSION** to
     `TerminalStateRelaxedValueSafe … env₂ ty ∧ WritableRootsUnborrowed finalStore env₂`
     (motive_2: result env `env₂.dropLifetime blockLifetime`). Extract `.1` for
     the final theorem goal.
   - Every case proves the extra conjunct for its result env+store:
     * const/copy/borrow: pass-through (store/env unchanged from premise).
     * move: `WritableRootsUnborrowed.move_var` transport (TO BUILD — see note).
     * box/declare: fresh-allocation transport (fresh location is no existing dep).
     * assign: write/drop transport.
     * block/drop: drop transport.
     * ite/while: **join** transport (same-shape, like
       `RuntimeRepresentedSlotsProtected`, no `EnvJoinSameShape`).
     * cons/singleton/ite/while sub-IHs: get the invariant for `(store', env')`
       from the sub-IH's strengthened conclusion (`.2`).
   - Establish at entry via `WritableRootsUnborrowed.of_wellFormed`
     (empty/source-initial env is `WellFormedEnv`).
   CRITICAL FINDING (session 2): the lossy `WritableRootsUnborrowed` (whose
   conclusion is just `WriteProhibited env (.var z)`) is **sufficient to discharge
   the move/assign frame** (the flagship helper proves this) but is **NOT
   self-transportable** through the move/assign env-strike. Reason: after striking
   `x`, `WriteProhibited env (.var z)` survives only if the borrow that prohibits
   `z` lives in a slot `≠ x`. That is in fact always the case (if `y≠x`'s value has
   a borrow dependency into `z`'s subtree, then `z` is prohibited via `y` or via
   some intermediate `q≠x` — `q=x` would make `y` target `x`-rooted, contradicting
   `¬WriteProhibited (.var x)`), but PROVING it requires tracing the dependency to
   the specific prohibiting slot — i.e. exactly the env↔runtime borrow-target
   faithfulness that `ContainedBorrowsWellFormed` provides and that the lossy
   invariant has discarded. The `WriteProhibited`/`mem_vars` disjunction in
   `borrowDependency_protected_writeProhibited_or_mem_vars` is genuine (nested
   `*q` borrows hit the `WriteProhibited` disjunct, not `mem_vars`), so you cannot
   strengthen the conclusion to the strike-robust `z ∈ vars(envSlot.ty)` either.

   CORRECTED SOLUTION (session 2, supersedes the above): the right threaded
   invariant is **`ContainedBorrowsWellFormed env` itself**, carried as a
   *preservation-internal* invariant (NOT re-added to any Typing.lean rule — so the
   handoff's "don't re-add to Typing.lean" is respected; cf. `BorrowSafeEnv`, which
   is already a preservation premise per README:302). Why this is the right one:
   - It is exactly the per-slot fact (`PartialTyBorrowsWellFormedInSlot` for every
     represented slot) that the move/assign frame bridges
     (`borrowDependency_var_writeProhibited_or_mem_vars` etc.) actually consume, so
     deriving `WritableRootsUnborrowed` from it is the existing
     `WritableRootsUnborrowed.of_wellFormed` route (its `.1` field).
   - The `BorrowTargetsWellFormedInSlot` obligation only requires each target
     typeable at *some* type (existential) + outlives — NOT joint typing at the
     merged pointee. So it **does** transport through `T-If`/`T-While` joins using
     same-shape derived from the *runtime abstraction* (not the removed
     `EnvJoinSameShape` premise): see
     `EnvJoin.left_sameShapeStrengthening_of_runtimeEnvAbstraction` (Lemma_4_11
     ~13289) and `EnvJoin.preserves_containedBorrowsWellFormed_of_target_transport`
     (RuntimeFacts ~920) — discharge its target-transport hypotheses from the
     runtime same-shape map rather than `EnvJoinSameShape`.
   - It transports through `move`/`assign` env-strikes via the `¬WriteProhibited`
     guard: other slots' borrow targets cannot mention the struck var `x` (else `x`
     is write-prohibited), so they stay typeable in the struck env.

   CONCRETE PLAN:
   a. Build `typingPreservesContainedBorrowsWellFormed_of_runtimeAbstraction`
      (the CBWF-only, runtime-abstraction-based replacement for the deleted
      `typingPreservesWellFormed_of_sourceTerm`): CBWF preserved per typing rule,
      joins discharged via runtime same-shape.
   b. Thread `ContainedBorrowsWellFormed store-env` through the preservation motive
      (premise + motive_1/motive_2 hypothesis + strengthened conclusion carrying
      CBWF for the result env, so sequencing sub-IHs get it — destructure
      `⟨hterminal, hcbwf'⟩` to keep existing accessors).
   c. Move/assign cases: derive `WritableRootsUnborrowed` locally via
      `.of_wellFormed`-style (needs CBWF + ∼ₛ from the relaxed abstraction's strict
      core + ValidStore + heap) and call the built helper
      `preservation_move_var_multistep_relaxedValue_of_invariant`.
   The `WritableRootsUnborrowed` family in Lemma_4_9 stays as the frame-discharge
   layer; only the threaded carrier changes from it to CBWF. This is the sorry-free
   path to green; it is a large multi-file change (all 17 preservation cases +
   `Theorem_4_12`/`Appendix9` consumers) but every step is now a known, provable
   lemma rather than an open problem.
3. **Wire** `preservation_move_var_multistep_relaxedValue_of_invariant` into the
   preservation `case move` (var branch), then assign/while/singleton.

### Broken cases are all the same root cause

The 32 errors (lines ~5384–5919 of `Lemma_4_11_Preservation.lean`) are in exactly
five cases: `move`, `assign`, `whileLoop`, `whileLoopDiverging`, `singleton`. All
fail because the motive was switched to `RelaxedRuntimeEnvAbstraction` but these
cases still call strict-`∼ₛ` / `WellFormedEnv` / `typingPreservesWellFormed_*`
machinery that has no relaxed equivalent yet. `whileLoop` keeps `hcbwf/hcoh/hlin`
in its *rule* (so it can rebuild WF of the loop invariant), but its IH calls and
`preservation_whileRunEnds` (strict, ~5136) must be ported to the relaxed
interface. `eq`, `ite`, `ite-diverging`, `block` (recursive), `cons` already work
on the relaxed motive — mirror them.

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
