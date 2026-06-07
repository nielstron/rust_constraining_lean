import LwRust.Paper.Soundness.Corollary_4_14_BorrowSafety

/-!
# Lemma 9.8 (Alias Preservation)

> Let `S₁ ▷ t` be a valid state and `S₂ ▷ v` a terminal state; let `σ` be a
> store typing … Then reduction preserves the validity (no duplicate owning
> references) invariant of states: `S₂ ▷ v` is valid.

Status: **mechanized** for the structural/redex fragments as the `validState`/
`validRuntimeState` preservation lemmas in `LwRust.Paper.Soundness`:

* `validState_blockB`, `validState_seq_step`, `validState_declare` — per-rule
  valid-state preservation fragments;
* `drops_validStore`, `dropsLifetime_validStore`, `validStore_write_*`,
  `validStore_update_*` — store-validity preservation under the primitive
  operations;
* `ValidRuntimeState` bundles Definition 4.3 validity with the explicit
  owner-allocation invariant the concrete store model needs.

The end-to-end multistep "`S₂ ▷ v` valid" statement is folded into the
`ValidRuntimeState finalStore (.val finalValue)` conjunct of `TerminalStateSafe`,
established alongside Preservation (Lemma 4.11) for the runtime cases.
-/
