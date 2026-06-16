# Status: removing `BorrowSafeEnv` from `T-If` (branch `drop-ite-borrowsafe`)

**Goal.** Remove the `BorrowSafeEnv env₅` premise from the `T-If` typing rule
(`TermTyping.ite`, `LwRust/Paper/Typing.lean`) and re-establish all runtime-safety
theorems (Progress, Preservation, Borrow Invariance / Lemma 4.9, Theorem 4.12,
`reachable_progress`, Examples) with **zero sorries**. The premise is already
removed (only `TyBorrowSafeAgainstEnv env₅ joinTy` remains). One `sorry` remains:
`Corollary_4_14_BorrowSafety.lean` (`BorrowSafeEnv env₅` for the merged join).

`main` is sorry-free; this is a feature branch. The merged-join `BorrowSafeEnv env₅`
is **genuinely false** — the §4.5.1 deviation the paper concedes — so it must be
**worked around**, never proved.

## Validated approach

Thread a runtime witness `BorrowSafeWitness store env` (`Lemma_4_9:309`) through
preservation in place of the false `BorrowSafeEnv` threading, then delete the false
"Corollary 4.14" (`typingPreservesBorrowSafeResult_global`). The witness is
`∃ env_w, BorrowSafeEnv env_w ∧ env_w ⊑ env ∧ keep-contract`, where `env_w` is the
"executed-path" environment (joins resolved to the taken branch — genuinely
borrow-safe). The lone runtime consumer of borrow-safety is
`WriteGuarded.collapse_kill_realized` (`Lemma_4_9:~7652`) in the deref-assignment
frame, which establishes mutable-borrow target uniqueness so the kill (drop) is sound.

## Committed green progress (each builds; sorry count stays 1)

- `7cc16cd` — simplified `BorrowSafeWitness` (dropped the dead `store ∼ₛ env_w`
  realization field); refactored `collapse_kill_realized` onto `SelectedTarget`
  (`Lemma_4_9:289`).
- `f7445f0` — reverse-descent infrastructure (`borrowContains_of_owned_borrowCell`,
  `borrowContains_of_valid_borrowRef`, `ownsAt_storage_inv`,
  `envBorrow_of_selectedTarget`); keystone `borrowSafeWitness_ite_hlive` proved
  modulo an `hbridge` premise.
- `da21862` — defined `LocMutExcl` (`Lemma_4_9:534`); re-based the keystone onto it
  (dropped `hbridge`); keystone conclusion is now **location-coverage**.

## The core obstruction (precisely characterized over 6 agent runs)

Syntactic `BorrowSafeEnv` (path-conflict `⋈`, i.e. same base variable) cannot bridge
to the **location-based** runtime reasoning that joins force:

1. A join merges cross-branch borrow-target lists (W-Bor union).
2. A runtime-**selected** target `s` that is *only* in the non-executed branch can
   co-resolve (`store.loc` is **non-injective**) with the executed-branch target
   `t₃` at the same location, yet is **not syntactically** in the borrow-safe witness.
3. `collapse_kill_realized.step` derives node identity `container = c` from a
   **same-base** conflict `t' ⋈ t` fed to `BorrowSafeEnv`. The two targets it
   compares (`t'` = first-spine-cell location, `t` = env-borrow-target location)
   share only a base variable and are provably **not co-located**, so a
   location-coverage / `LocMutExcl` premise cannot drive that step.

The predicate both consumers would need to share is genuine **location-based
node-uniqueness for `&mut`**:
`∀ x y mx my Tx Ty tx ty, env_w ⊢ x ↝ &mut Tx → env_w ⊢ y ↝ borrow my Ty →
 tx ∈ Tx → ty ∈ Ty → store.loc tx = store.loc ty → x = y`.
This is **strictly stronger** than syntactic `BorrowSafeEnv` and **not derivable**
from it (runtime `Value.ref` carries no mutability bit; co-location ⇏ `⋈`). It must
be a **threaded runtime invariant**.

Key (correct) insight that keeps it tractable: such a location invariant is
**store-level**, so the `ite` *join* preserves it essentially for free (the join is
type-level; the post-`ite` store is the executed branch's store; W-Bor preserves
`&mut`-ness). Its real preservation crux is straight-line **borrow creation**
(`x = &mut y`), discharged by the borrow rule's existing write-prohibition check.

## Remaining work to reach zero sorries (the "re-architecture" path)

1. **Re-index** `WriteGuarded` / `SlotDepKill` / `writeGuarded_of_resolution` /
   `loc_protected_guarded_base` by the resolved **leaf `Location`** end-to-end, so
   `collapse_kill`'s `container = c` is driven by location-uniqueness on genuinely
   co-located targets.
2. **Define + prove + thread** the location-based `&mut`-exclusivity invariant
   through preservation (`ite` trivial; creation from the rule), discharging the
   `LocMutExcl`/location-uniqueness premise.
3. **Phase 3** — thread `BorrowSafeWitness` through the `preservation` and
   `reachable_progress` motives (~17 cases each), reroute the ~6 + ~10
   `typingPreservesBorrowSafeResult_global` consumers, and **delete** Corollary 4.14
   → zero sorries.

This is a major (multi-week-class) formalization — essentially mechanizing the exact
runtime borrow-safety-across-joins property §4.5.1 concedes is not established.

## Alternative attack angles worth scoping (cheaper than the full re-architecture)

- **A. Executed-path realization (`store ∼ₛ env_w`).** Re-add `store ∼ₛ env_w` to
  the witness and thread it (parallel to the existing `store ∼ₛ env` threading; `ite`
  case = executed branch's). If `collapse_kill`'s resolution targets `t', t` are
  provably the *realized* ones (∈ `env_w`), the env₄-only case becomes **vacuous**
  and the syntactic keep-contract suffices — no re-index. Hinges on whether
  `writeGuarded_of_resolution` only produces realized targets.
- **C. Bypass `collapse_kill`'s uniqueness.** Check whether the deref-write's actual
  runtime-safety obligation (validity of what is dropped / written) can be shown
  directly from well-formedness + the executed branch, without node-identity
  uniqueness at all.
- **F. Existing store invariants.** Re-audit `ValidState` / `ValidStoreTyping` /
  `ValidPartialValue` for any borrow-provenance constraint strong enough to yield
  location-exclusivity without a new threaded invariant.
