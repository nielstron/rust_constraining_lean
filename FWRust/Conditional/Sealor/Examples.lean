import FWRust.Conditional.Sealor.NestedBlocks

/-!
# Build-checked conditional sealor examples

These examples cover the two `ast_copier` conditional completions and the
recursive fallback used for an incomplete `else if` in statement position.
-/

namespace FWRust.Conditional.Sealor.Examples

open FWRust.Conditional.Core
open FWRust.Conditional.Paper
open FWRust.Conditional.Sealor

abbrev truth : Term := .val (.bool true)
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
  CompletesTerm.iteTrueBranch CompletesTerm.done

theorem missingElse_seal_shape :
    sealProgram missingElsePartial = .ite truth unitTerm .missing :=
  by simp [sealProgram, missingElsePartial, sealTerm, sealTermStmts,
    missingTerm]

theorem missingElse_sealed_wellTyped :
    ProgramWellTyped (sealProgram missingElsePartial) :=
  sealProgram_wellTyped_of_completion missingElsePartial_completes
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
  exact CompletesTerm.iteTrueBranch
    (CompletesTerm.blockTerms
      (CompletesTerms.elemsDone (suffix := [unitTerm])))

theorem incompleteThen_seal_shape :
    sealProgram incompleteThenPartial =
      .ite truth (.block branchLifetime [.missing]) .missing :=
  by simp [sealProgram, incompleteThenPartial, sealTerm, sealTermStmts,
    sealTerms, missingTerm]

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
  exact CompletesTerm.iteFalseBranch
    (CompletesTerm.blockTerms
      (CompletesTerms.elemsDone (suffix := [unitTerm])))

theorem incompleteElse_seal_shape :
    sealProgram incompleteElsePartial =
      .ite truth unitTerm (.block branchLifetime [.missing]) := by
  simp [sealProgram, incompleteElsePartial, sealTerm, sealTermStmts,
    sealTerms, missingTerm]

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
  exact CompletesTerm.blockTerms
    (CompletesTerms.elemsFrontier
      (CompletesTerm.iteFalseBranch
        (CompletesTerm.iteTrueBranch CompletesTerm.done)))

theorem completeElseIfProgram_wellTyped :
    ProgramWellTyped completeElseIfProgram := by
  refine ⟨.unit, Env.empty, TermTyping.block branchLifetime_child
    (.singleton completeElseIf_typing) WellFormedTy.unit ?_⟩
  simp [Env.dropLifetime, Env.empty]

theorem elseIf_statement_seal_shape :
    sealTermStmts branchLifetime elseIfFrontier =
      [truth, .ite truth unitTerm .missing] :=
  by simp [elseIfFrontier, sealTermStmts, missingTerm]

theorem elseIf_program_seal_shape :
    sealProgram elseIfProgramPartial =
      .block branchLifetime
        [truth, .ite truth unitTerm .missing, .missing] :=
  by simp [sealProgram, elseIfProgramPartial, elseIfFrontier, sealTerm,
    sealTermStmts, sealTerms, missingTerm]

theorem elseIf_sealed_wellTyped :
    ProgramWellTyped (sealProgram elseIfProgramPartial) :=
  sealProgram_wellTyped_of_completion elseIfProgramPartial_completes
    completeElseIfProgram_wellTyped

end FWRust.Conditional.Sealor.Examples
