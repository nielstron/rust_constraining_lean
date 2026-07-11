import FWRust.Paper.Soundness

/-!
Focused witnesses for the minimal loop rule `T-While`.

The first example checks and executes `while false { unit }`.  The second
checks the same harmless loop in an environment whose live loans form a
two-node cycle.  That environment cannot be `Linearizable`, so the second
derivation is an executable independence witness for dropping the historical
global-ranking premise from `T-While`.
-/

namespace FWRust
namespace Paper
namespace WhileSafety

open Core

def bodyLifetime : Lifetime := [0]

def falseLoop : Term :=
  .whileLoop bodyLifetime (.val (.bool false)) (.val .unit)

theorem bodyLifetime_child :
    LifetimeChild Lifetime.root bodyLifetime := by
  exact ⟨0, rfl⟩

theorem envJoin_self (env : Env) : EnvJoin env env env := by
  simp [EnvJoin]

theorem env_ext (left right : Env)
    (h : ∀ name, left.slotAt name = right.slotAt name) : left = right := by
  cases left with
  | mk leftSlotAt =>
      cases right with
      | mk rightSlotAt =>
          have : leftSlotAt = rightSlotAt := funext h
          subst this
          rfl

theorem loopInvariantNameFresh_self (env : Env) (condition body : Term) :
    LoopInvariantNameFresh env env condition body := by
  intro erased checked hfresh _hcondition _hbody
  exact hfresh

theorem empty_containedBorrowsWellFormedWhenInitialized :
    ContainedBorrowsWellFormedWhenInitialized Env.empty := by
  intro name slot mutable targets hslot _hcontains
  simp [Env.empty] at hslot

theorem falseLoop_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root falseLoop .unit
      Env.empty := by
  unfold falseLoop
  exact TermTyping.whileLoop
    bodyLifetime_child
    (envJoin_self Env.empty)
    empty_containedBorrowsWellFormedWhenInitialized
    (loopInvariantNameFresh_self Env.empty _ _)
    (TermTyping.const ValueTyping.bool)
    (TermTyping.const ValueTyping.unit)
    rfl

/-- The source loop enters its runtime condition phase and immediately exits. -/
theorem falseLoop_exits (store : ProgramStore) :
    MultiStep store Lifetime.root falseLoop store (.val .unit) := by
  unfold falseLoop
  exact MultiStep.trans Step.whileStart
    (MultiStep.trans Step.whileCondFalse MultiStep.refl)

/-- The general progress theorem applies directly to a source loop. -/
theorem falseLoop_progress :
    ProgressResult ProgramStore.empty Lifetime.root falseLoop :=
  emptyInitial_progress falseLoop_typing

/-- The two-step terminating run has the promised safe result store/value. -/
theorem falseLoop_terminalSafe :
    TerminalStateSafe ProgramStore.empty .unit Env.empty .unit :=
  emptyInitial_preservation falseLoop_typing
    (falseLoop_exits ProgramStore.empty)

/-- Runtime safety is not limited to the final value: every finite prefix of
the loop's execution is terminal or has a next step. -/
theorem falseLoop_allPrefixesProgress {currentStore : ProgramStore}
    {current : Term}
    (hreaches : MultiStep ProgramStore.empty Lifetime.root falseLoop
      currentStore current) :
    ProgressResult currentStore Lifetime.root current := by
  exact reachableProgressWhenInitialized
    (termTyping_empty_sourceTerm falseLoop_typing)
    (emptyInitialRuntimeState_valid_of_typing falseLoop_typing)
    (emptyInitialValidStoreTyping_of_typing falseLoop_typing)
    (wellFormedEnvWhenInitialized_empty Lifetime.root)
    safeAbstraction_empty
    ProgramStore.finiteSupport_empty
    falseLoop_typing hreaches

/-! ## Independence from the historical global ranking premise -/

def pSlot : EnvSlot :=
  { ty := .ty (.borrow false [.var "q"]), lifetime := Lifetime.root }

def qSlot : EnvSlot :=
  { ty := .ty (.borrow false [.var "p"]), lifetime := Lifetime.root }

/-- A live two-node loan cycle: `p : &[q]` and `q : &[p]`. -/
def cyclicEnv : Env :=
  (Env.empty.update "p" pSlot).update "q" qSlot

theorem cyclicEnv_p : cyclicEnv.slotAt "p" = some pSlot := by
  simp [cyclicEnv, Env.update]

theorem cyclicEnv_q : cyclicEnv.slotAt "q" = some qSlot := by
  simp [cyclicEnv, Env.update]

theorem cyclicEnv_none {name : Name} (hp : name ≠ "p") (hq : name ≠ "q") :
    cyclicEnv.slotAt name = none := by
  simp [cyclicEnv, Env.update, Env.empty, hp, hq]

theorem cyclicEnv_not_linearizable : ¬ Linearizable cyclicEnv := by
  rintro ⟨rank, hrank⟩
  have hqp : rank "q" < rank "p" :=
    hrank "p" pSlot cyclicEnv_p "q" (by
      simp [pSlot, PartialTy.vars, Ty.vars, LVal.base])
  have hpq : rank "p" < rank "q" :=
    hrank "q" qSlot cyclicEnv_q "p" (by
      simp [qSlot, PartialTy.vars, Ty.vars, LVal.base])
  omega

theorem cyclicEnv_p_base :
    LValBaseOutlives cyclicEnv (.var "p") Lifetime.root :=
  ⟨pSlot, by simpa [LVal.base] using cyclicEnv_p,
    LifetimeOutlives.refl Lifetime.root⟩

theorem cyclicEnv_q_base :
    LValBaseOutlives cyclicEnv (.var "q") Lifetime.root :=
  ⟨qSlot, by simpa [LVal.base] using cyclicEnv_q,
    LifetimeOutlives.refl Lifetime.root⟩

/-- The loop rule keeps only the local, runtime-relevant borrow obligation.
The cyclic loans meet it even though no global rank can orient the cycle. -/
theorem cyclicEnv_containedBorrowsWellFormedWhenInitialized :
    ContainedBorrowsWellFormedWhenInitialized cyclicEnv := by
  intro name slot mutable targets hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  by_cases hp : name = "p"
  · subst name
    have hslotEq : slot = pSlot :=
      Option.some.inj (hslot.symm.trans cyclicEnv_p)
    have hcontainedEq : containedSlot = pSlot :=
      Option.some.inj (hcontainedSlot.symm.trans cyclicEnv_p)
    subst slot
    subst containedSlot
    simp only [pSlot] at hcontainsTy
    cases hcontainsTy with
    | here =>
        intro target htarget
        simp only [List.mem_singleton] at htarget
        subst target
        exact ⟨cyclicEnv_q_base, fun _ =>
          ⟨.borrow false [.var "p"], Lifetime.root,
            LValTyping.var cyclicEnv_q,
            LifetimeOutlives.refl Lifetime.root,
            cyclicEnv_q_base⟩⟩
  · by_cases hq : name = "q"
    · subst name
      have hslotEq : slot = qSlot :=
        Option.some.inj (hslot.symm.trans cyclicEnv_q)
      have hcontainedEq : containedSlot = qSlot :=
        Option.some.inj (hcontainedSlot.symm.trans cyclicEnv_q)
      subst slot
      subst containedSlot
      simp only [qSlot] at hcontainsTy
      cases hcontainsTy with
      | here =>
          intro target htarget
          simp only [List.mem_singleton] at htarget
          subst target
          exact ⟨cyclicEnv_p_base, fun _ =>
            ⟨.borrow false [.var "q"], Lifetime.root,
              LValTyping.var cyclicEnv_p,
              LifetimeOutlives.refl Lifetime.root,
              cyclicEnv_p_base⟩⟩
    · have hnone := cyclicEnv_none hp hq
      rw [hslot] at hnone
      cases hnone

theorem cyclicEnv_drop_bodyLifetime :
    cyclicEnv.dropLifetime bodyLifetime = cyclicEnv := by
  apply env_ext
  intro name
  by_cases hp : name = "p"
  · subst name
    simp [Env.dropLifetime, cyclicEnv_p, pSlot, bodyLifetime, Lifetime.root]
  · by_cases hq : name = "q"
    · subst name
      simp [Env.dropLifetime, cyclicEnv_q, qSlot, bodyLifetime, Lifetime.root]
    · simp [Env.dropLifetime, cyclicEnv_none hp hq]

/-- `T-While` is applicable although its invariant is provably non-linearizable. -/
theorem cyclicFalseLoop_typing :
    TermTyping cyclicEnv StoreTyping.empty Lifetime.root falseLoop .unit
      cyclicEnv := by
  unfold falseLoop
  exact TermTyping.whileLoop
    bodyLifetime_child
    (envJoin_self cyclicEnv)
    cyclicEnv_containedBorrowsWellFormedWhenInitialized
    (loopInvariantNameFresh_self cyclicEnv _ _)
    (TermTyping.const ValueTyping.bool)
    (TermTyping.const ValueTyping.unit)
    cyclicEnv_drop_bodyLifetime

/-- Static loan cycles do not affect this program's concrete execution. -/
theorem cyclicFalseLoop_exits (store : ProgramStore) :
    MultiStep store Lifetime.root falseLoop store (.val .unit) :=
  falseLoop_exits store

end WhileSafety
end Paper
end FWRust
