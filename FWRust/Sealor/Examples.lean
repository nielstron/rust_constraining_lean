import FWRust.Sealor.Sealors.NestedBlocks

/-!
# Build-checked conditional sealor examples

These examples cover the two `ast_copier` conditional completions and the
recursive fallback used for an incomplete `else if` in statement position.
-/

namespace ConservativeSealor.Examples

open FWRust.Core
open FWRust.Paper
open ConservativeSealor

abbrev truth : Term := .val (.bool Bool.true)
abbrev unitTerm : Term := .val .unit

def branchLifetime : Lifetime :=
  { path := [0] }

theorem branchLifetime_child :
    LifetimeChild Lifetime.root branchLifetime :=
  ⟨0, rfl⟩

def completeUnitIf : Term :=
  .ite truth unitTerm unitTerm

theorem completeUnitIf_typing_at (lifetime : Lifetime) :
    TermTyping Env.empty StoreTyping.empty lifetime completeUnitIf
      .unit Env.empty := by
  exact TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    (TermTyping.const ValueTyping.unit)
    (TermTyping.const ValueTyping.unit)
    (PartialTyJoin.self (.ty .unit))
    (by simp [EnvJoin])

theorem completeUnitIf_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root completeUnitIf
      .unit Env.empty :=
  completeUnitIf_typing_at Lifetime.root

/-! ## Missing else -/

def missingElsePartial : PartialProgram :=
  .iteTrueBranch truth (.done unitTerm)

theorem missingElsePartial_completes :
    CompletesProgram missingElsePartial completeUnitIf :=
  Generated.CompletesTerm.ctermIte_iteTrueBranch Generated.CompletesTerm.done

theorem missingElse_seal_shape :
    sealProgram missingElsePartial = .ite truth unitTerm .missing :=
  by simp [sealProgram, missingElsePartial, sealTerm, sealTermStmts,
    branchRebuildable, missingTerm]

theorem missingElse_sealed_wellTyped :
    ProgramWellTyped (sealProgram missingElsePartial) :=
  sealProgram_wellTyped_of_completion missingElsePartial_completes
    ⟨.unit, Env.empty, completeUnitIf_typing⟩

/-! ## Missing then branch -/

/-- The parser has completed the condition but has not produced a then
branch.  This is the direct counterpart of `ast_copier`'s both-panic
fallback. -/
def missingThenPartial : PartialProgram :=
  .iteTrueBranch truth .cutoff

theorem missingThenPartial_completes :
    CompletesProgram missingThenPartial completeUnitIf :=
  Generated.CompletesTerm.ctermIte_iteTrueBranch
    Generated.CompletesTerm.cutoff

theorem missingThen_seal_shape :
    sealProgram missingThenPartial = .ite truth .missing .missing := by
  simp [sealProgram, missingThenPartial, sealTerm, sealTermStmts,
    branchRebuildable, missingTerm]

theorem missingThen_sealed_wellTyped :
    ProgramWellTyped (sealProgram missingThenPartial) :=
  sealProgram_wellTyped_of_completion missingThenPartial_completes
    ⟨.unit, Env.empty, completeUnitIf_typing⟩

/-! ## Incomplete then block -/

def incompleteThenPartial : PartialProgram :=
  .iteTrueBranch truth
    (.blockTerms branchLifetime (.elems [] none))

def completeThenBlockIf : Term :=
  .ite truth (.block branchLifetime [unitTerm]) unitTerm

theorem completeThenBlockIf_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root completeThenBlockIf
      .unit Env.empty := by
  unfold completeThenBlockIf
  have hblock : TermTyping Env.empty StoreTyping.empty Lifetime.root
      (.block branchLifetime [unitTerm]) .unit Env.empty :=
    TermTyping.block branchLifetime_child
      (.singleton (TermTyping.const ValueTyping.unit)) WellFormedTy.unit
        (by simp [Env.dropLifetime, Env.empty])
  exact TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    hblock
    (TermTyping.const ValueTyping.unit)
    (PartialTyJoin.self (.ty .unit))
    (by simp [EnvJoin])

theorem incompleteThenPartial_completes :
    CompletesProgram incompleteThenPartial completeThenBlockIf := by
  exact Generated.CompletesTerm.ctermIte_iteTrueBranch
    (Generated.CompletesTerm.ctermBlock_blockTerms
      (Generated.CompletesTerms.elemsDone (suffix := [unitTerm])))

theorem incompleteThen_seal_shape :
    sealProgram incompleteThenPartial =
      .ite truth (.block branchLifetime [.missing]) .missing :=
  by simp [sealProgram, incompleteThenPartial, sealTerm, sealTermStmts,
    sealTerms, branchRebuildable, missingTerm]

/-- The synthesized then block is panic-terminated. -/
theorem incompleteThen_trueBranch_diverges :
    Term.Diverges (.block branchLifetime [.missing]) :=
  Term.Diverges.block (by simp) Term.Diverges.missing

/-- The synthesized else branch is also a panic/missing completion. -/
theorem incompleteThen_falseBranch_diverges :
    Term.Diverges (.missing : Term) :=
  Term.Diverges.missing

theorem incompleteThen_sealed_wellTyped :
    ProgramWellTyped (sealProgram incompleteThenPartial) :=
  sealProgram_wellTyped_of_completion incompleteThenPartial_completes
    ⟨.unit, Env.empty, completeThenBlockIf_typing⟩

/-! ## Incomplete else block -/

def incompleteElsePartial : PartialProgram :=
  .iteFalseBranch truth unitTerm
    (.blockTerms branchLifetime (.elems [] none))

def completeElseBlockIf : Term :=
  .ite truth unitTerm (.block branchLifetime [unitTerm])

theorem completeElseBlockIf_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root completeElseBlockIf
      .unit Env.empty := by
  unfold completeElseBlockIf
  have hblock : TermTyping Env.empty StoreTyping.empty Lifetime.root
      (.block branchLifetime [unitTerm]) .unit Env.empty :=
    TermTyping.block branchLifetime_child
      (.singleton (TermTyping.const ValueTyping.unit)) WellFormedTy.unit
        (by simp [Env.dropLifetime, Env.empty])
  exact TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    (TermTyping.const ValueTyping.unit)
    hblock
    (PartialTyJoin.self (.ty .unit))
    (by simp [EnvJoin])

theorem incompleteElsePartial_completes :
    CompletesProgram incompleteElsePartial completeElseBlockIf := by
  exact Generated.CompletesTerm.ctermIte_iteFalseBranch
    (Generated.CompletesTerm.ctermBlock_blockTerms
      (Generated.CompletesTerms.elemsDone (suffix := [unitTerm])))

theorem incompleteElse_seal_shape :
    sealProgram incompleteElsePartial =
      .ite truth unitTerm (.block branchLifetime [.missing]) := by
  simp [sealProgram, incompleteElsePartial, sealTerm, sealTermStmts,
    sealTerms, branchRebuildable, missingTerm]

theorem incompleteElse_sealed_wellTyped :
    ProgramWellTyped (sealProgram incompleteElsePartial) :=
  sealProgram_wellTyped_of_completion incompleteElsePartial_completes
    ⟨.unit, Env.empty, completeElseBlockIf_typing⟩

/-! ## Incomplete `else if`

The full outer conditional is not rebuilt for the grammar's non-block branch
frontier.  At statement position its already-typed condition is retained,
then the nested `if` is sealed with a diverging else branch.  This is the
formal conservative fallback, not a claim of syntactic equivalence with the
copier's retained outer chain.

An exact rebuild would need new result-type and environment joins between the
completed outer true branch and the recursively sealed false branch.  The
completion derivation gives joins only for the false branch's unknown complete
term.  Wrapping the recursively sealed statements in a fresh diverging block
would avoid the joins, but would require a general theorem rebasing their
typing from this lifetime to the fresh child lifetime; fixed nested blocks and
declarations make that theorem false.  The transport theorem below proves the
weaker statement fallback is typable whenever the completion is typable,
without either extra premise.
-/

def elseIfFrontier : PartialTerm :=
  .iteFalseBranch truth unitTerm
    (.iteTrueBranch truth (.done unitTerm))

def completeElseIf : Term :=
  .ite truth unitTerm completeUnitIf

theorem completeElseIf_typing :
    TermTyping Env.empty StoreTyping.empty branchLifetime completeElseIf
      .unit Env.empty := by
  have hnested : TermTyping Env.empty StoreTyping.empty branchLifetime
      completeUnitIf .unit Env.empty :=
    completeUnitIf_typing_at branchLifetime
  exact TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    (TermTyping.const ValueTyping.unit)
    hnested
    (PartialTyJoin.self (.ty .unit))
    (by simp [EnvJoin])

def elseIfProgramPartial : PartialProgram :=
  .blockTerms branchLifetime (.elems [] (some elseIfFrontier))

def completeElseIfProgram : Program :=
  .block branchLifetime [completeElseIf]

theorem elseIfProgramPartial_completes :
    CompletesProgram elseIfProgramPartial completeElseIfProgram := by
  exact Generated.CompletesTerm.ctermBlock_blockTerms
    (Generated.CompletesTerms.elemsTail
      (Generated.CompletesTerm.ctermIte_iteFalseBranch
        (Generated.CompletesTerm.ctermIte_iteTrueBranch Generated.CompletesTerm.done)))

theorem completeElseIfProgram_wellTyped :
    ProgramWellTyped completeElseIfProgram := by
  refine ⟨.unit, Env.empty, TermTyping.block branchLifetime_child
    (.singleton completeElseIf_typing) WellFormedTy.unit ?_⟩
  simp [Env.dropLifetime, Env.empty]

theorem elseIf_statement_seal_shape :
    sealTermStmts branchLifetime elseIfFrontier =
      [truth, .ite truth unitTerm .missing] :=
  by simp [elseIfFrontier, sealTermStmts, sealTerm, branchRebuildable,
    missingTerm]

theorem elseIf_program_seal_shape :
    sealProgram elseIfProgramPartial =
      .block branchLifetime
        [truth, .ite truth unitTerm .missing, .missing] :=
  by simp [sealProgram, elseIfProgramPartial, elseIfFrontier, sealTerm,
    sealTermStmts, sealTerms, branchRebuildable, missingTerm]

theorem elseIf_sealed_wellTyped :
    ProgramWellTyped (sealProgram elseIfProgramPartial) :=
  sealProgram_wellTyped_of_completion elseIfProgramPartial_completes
    completeElseIfProgram_wellTyped

/-! ## Partial `while` frontiers -/

abbrev falsehood : Term :=
  .val (.bool Bool.false)

def completeFalseLoop : Term :=
  .whileLoop branchLifetime falsehood unitTerm

theorem empty_loopInvariantNameFresh (condition body : Term) :
    LoopInvariantNameFresh Env.empty Env.empty condition body := by
  intro erased checked hfresh _hcondition _hbody
  exact hfresh

theorem empty_containedBorrowsWellFormedWhenInitialized :
    ContainedBorrowsWellFormedWhenInitialized Env.empty := by
  intro name slot mutable targets hslot _hcontains
  simp [Env.empty] at hslot

theorem completeFalseLoop_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root completeFalseLoop
      .unit Env.empty := by
  unfold completeFalseLoop
  exact TermTyping.whileLoop (envBack := Env.empty) (envInv := Env.empty)
    branchLifetime_child
    (by simp [EnvJoin])
    empty_containedBorrowsWellFormedWhenInitialized
    (empty_loopInvariantNameFresh _ _)
    (TermTyping.const ValueTyping.bool)
    (TermTyping.const ValueTyping.unit)
    (by simp [Env.dropLifetime, Env.empty])

/-! An in-flight condition does not yet supply a reusable Boolean guard, so it
seals to the polymorphic missing term. -/

def incompleteWhileCondition : PartialProgram :=
  .whileCondition branchLifetime .cutoff

theorem incompleteWhileCondition_completes :
    CompletesProgram incompleteWhileCondition completeFalseLoop :=
  Generated.CompletesTerm.ctermWhile_whileCondition
    Generated.CompletesTerm.cutoff

theorem incompleteWhileCondition_seal_shape :
    sealProgram incompleteWhileCondition = missingTerm := by
  simp [sealProgram, incompleteWhileCondition, sealTerm, sealTermStmts]

theorem incompleteWhileCondition_sealed_wellTyped :
    ProgramWellTyped (sealProgram incompleteWhileCondition) :=
  sealProgram_wellTyped_of_completion incompleteWhileCondition_completes
    ⟨.unit, Env.empty, completeFalseLoop_typing⟩

/-! Once the guard is complete, it is retained.  A body not yet known to be a
Rust block is represented by the bottom-effect missing term. -/

def incompleteWhileBody : PartialProgram :=
  .whileBody branchLifetime falsehood .cutoff

theorem incompleteWhileBody_completes :
    CompletesProgram incompleteWhileBody completeFalseLoop :=
  Generated.CompletesTerm.ctermWhile_whileBody
    Generated.CompletesTerm.cutoff

theorem incompleteWhileBody_seal_shape :
    sealProgram incompleteWhileBody =
      (.whileLoop branchLifetime falsehood missingTerm) := by
  simp [sealProgram, incompleteWhileBody, sealTerm, sealTermStmts,
    loopBodyRebuildable]

theorem incompleteWhileBody_sealed_wellTyped :
    ProgramWellTyped (sealProgram incompleteWhileBody) :=
  sealProgram_wellTyped_of_completion incompleteWhileBody_completes
    ⟨.unit, Env.empty, completeFalseLoop_typing⟩

/-! A determined body does not need a fallback: the exact completed loop is
preserved and its original typing derivation is reused. -/

def determinedWhileBody : PartialProgram :=
  .whileBody branchLifetime falsehood (.done unitTerm)

theorem determinedWhileBody_completes :
    CompletesProgram determinedWhileBody completeFalseLoop :=
  Generated.CompletesTerm.ctermWhile_whileBody
    Generated.CompletesTerm.done

theorem determinedWhileBody_seal_shape :
    sealProgram determinedWhileBody = completeFalseLoop := by
  simp [sealProgram, determinedWhileBody, completeFalseLoop, sealTerm,
    sealTermStmts, loopBodyRebuildable]

theorem determinedWhileBody_sealed_wellTyped :
    ProgramWellTyped (sealProgram determinedWhileBody) :=
  sealProgram_wellTyped_of_completion determinedWhileBody_completes
    ⟨.unit, Env.empty, completeFalseLoop_typing⟩

/-! The same two paths for a realistic block-shaped Rust loop body. -/

def whileBlockLifetime : Lifetime :=
  { path := [0, 0] }

theorem whileBlockLifetime_child :
    LifetimeChild branchLifetime whileBlockLifetime :=
  ⟨0, rfl⟩

def completeFalseBlockLoop : Term :=
  .whileLoop branchLifetime falsehood
    (.block whileBlockLifetime [unitTerm])

theorem completeFalseBlockLoop_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root
      completeFalseBlockLoop .unit Env.empty := by
  unfold completeFalseBlockLoop
  have hbody : TermTyping Env.empty StoreTyping.empty branchLifetime
      (.block whileBlockLifetime [unitTerm]) .unit Env.empty := by
    exact TermTyping.block whileBlockLifetime_child
      (.singleton (TermTyping.const ValueTyping.unit)) WellFormedTy.unit
      (by simp [Env.dropLifetime, Env.empty])
  exact TermTyping.whileLoop (envBack := Env.empty) (envInv := Env.empty)
    branchLifetime_child
    (by simp [EnvJoin])
    empty_containedBorrowsWellFormedWhenInitialized
    (empty_loopInvariantNameFresh _ _)
    (TermTyping.const ValueTyping.bool)
    hbody
    (by simp [Env.dropLifetime, Env.empty])

def incompleteWhileBlockBody : PartialProgram :=
  .whileBody branchLifetime falsehood
    (.blockTerms whileBlockLifetime (.elems [] none))

theorem incompleteWhileBlockBody_completes :
    CompletesProgram incompleteWhileBlockBody completeFalseBlockLoop :=
  Generated.CompletesTerm.ctermWhile_whileBody
    (Generated.CompletesTerm.ctermBlock_blockTerms
      (Generated.CompletesTerms.elemsDone (suffix := [unitTerm])))

theorem incompleteWhileBlockBody_seal_shape :
    sealProgram incompleteWhileBlockBody =
      (.whileLoop branchLifetime falsehood
        (.block whileBlockLifetime [missingTerm])) := by
  simp [sealProgram, incompleteWhileBlockBody, sealTerm, sealTermStmts,
    sealTerms, loopBodyRebuildable]

/-- The exact shape needed for a source prefix such as
`while condition { prefix;`: neither the guard nor any completed body
statement is discarded. -/
theorem whileBody_statementPrefix_seal_shape
    (bodyLifetime blockLifetime : Lifetime) (condition : Term)
    (pre : List Term) :
    sealProgram
        (.whileBody bodyLifetime condition
          (.blockTerms blockLifetime (.elems pre none))) =
      (.whileLoop bodyLifetime condition
        (.block blockLifetime (pre ++ [missingTerm]))) := by
  simp [sealProgram, sealTerm, sealTermStmts, sealTerms,
    loopBodyRebuildable]

/-- A build-checked nonempty instance of `while condition { statement;`.
The extracted ordinary loop keeps both `condition` and `statement`. -/
def incompleteWhilePrefixedBlockBody : PartialProgram :=
  .whileBody branchLifetime falsehood
    (.blockTerms whileBlockLifetime (.elems [unitTerm] none))

theorem incompleteWhilePrefixedBlockBody_completes :
    CompletesProgram incompleteWhilePrefixedBlockBody completeFalseBlockLoop :=
  Generated.CompletesTerm.ctermWhile_whileBody
    (Generated.CompletesTerm.ctermBlock_blockTerms
      (Generated.CompletesTerms.elemsDone (suffix := [])))

theorem incompleteWhilePrefixedBlockBody_seal_shape :
    sealProgram incompleteWhilePrefixedBlockBody =
      (.whileLoop branchLifetime falsehood
        (.block whileBlockLifetime [unitTerm, missingTerm])) := by
  simpa [incompleteWhilePrefixedBlockBody] using
    whileBody_statementPrefix_seal_shape branchLifetime whileBlockLifetime
      falsehood [unitTerm]

theorem incompleteWhilePrefixedBlockBody_sealed_wellTyped :
    ProgramWellTyped (sealProgram incompleteWhilePrefixedBlockBody) :=
  sealProgram_wellTyped_of_completion
    incompleteWhilePrefixedBlockBody_completes
    ⟨.unit, Env.empty, completeFalseBlockLoop_typing⟩

theorem incompleteWhileBlockBody_sealed_wellTyped :
    ProgramWellTyped (sealProgram incompleteWhileBlockBody) :=
  sealProgram_wellTyped_of_completion incompleteWhileBlockBody_completes
    ⟨.unit, Env.empty, completeFalseBlockLoop_typing⟩

def determinedWhileBlockBody : PartialProgram :=
  .whileBody branchLifetime falsehood
    (.blockTerms whileBlockLifetime (.done [unitTerm]))

theorem determinedWhileBlockBody_completes :
    CompletesProgram determinedWhileBlockBody completeFalseBlockLoop :=
  Generated.CompletesTerm.ctermWhile_whileBody
    (Generated.CompletesTerm.ctermBlock_blockTerms
      Generated.CompletesTerms.done)

theorem determinedWhileBlockBody_seal_shape :
    sealProgram determinedWhileBlockBody = completeFalseBlockLoop := by
  simp [sealProgram, determinedWhileBlockBody, completeFalseBlockLoop,
    sealTerm, sealTermStmts, sealTerms, loopBodyRebuildable]

theorem determinedWhileBlockBody_sealed_wellTyped :
    ProgramWellTyped (sealProgram determinedWhileBlockBody) :=
  sealProgram_wellTyped_of_completion determinedWhileBlockBody_completes
    ⟨.unit, Env.empty, completeFalseBlockLoop_typing⟩

/-! Before the parser has exposed a body lifetime, the only premise-free
fallback is the polymorphic missing term. -/

def whileStartPartial : PartialProgram :=
  .whileStart

theorem whileStartPartial_completes :
    CompletesProgram whileStartPartial completeFalseLoop :=
  Generated.CompletesTerm.ctermWhile_whileStart

theorem whileStart_seal_shape :
    sealProgram whileStartPartial = missingTerm := by
  simp [sealProgram, whileStartPartial, sealTerm, sealTermStmts]

theorem whileStart_sealed_wellTyped :
    ProgramWellTyped (sealProgram whileStartPartial) :=
  sealProgram_wellTyped_of_completion whileStartPartial_completes
    ⟨.unit, Env.empty, completeFalseLoop_typing⟩

end ConservativeSealor.Examples
